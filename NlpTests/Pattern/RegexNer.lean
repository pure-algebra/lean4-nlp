import Nlp.Pattern.RegexNer

/-!
# Typed RegexNER regression tests

These checks cover mixed compiler lanes, deterministic conflict precedence, sentence isolation,
existing-entity protection, the effectful range seam, and actionable boundary failures.
-/

namespace NlpTests.Pattern.RegexNer

open Nlp Nlp.Pattern

/-- Compile one test model while retaining an unexpected typed failure in the result. -/
private def compileModel (rules : Array RegexNerRule) :
    Except RegexNerCompileError RegexNerModel :=
  RegexNerModel.compile rules

#guard ({} : RegexNerCompileConfig).maxRules == 65_536
#guard ({} : RegexNerCompileConfig).maxPayloadEntries == 1_048_576
#guard ({} : RegexNerCompileConfig).maxSourceBytes == 67_108_864
#guard ({} : RegexNerCompileConfig).search.maxWork == 16_777_216
#guard ({} : RegexNerCompileConfig).search.maxMatches == 65_536

/-- A valid three-token document used by overlap-precedence tests. -/
private def newYorkCity : Doc [.tokens] :=
  { text := "New York City"
    spans := #[⟨0, 3⟩, ⟨4, 8⟩, ⟨9, 13⟩]
    forms := #["New", "York", "City"] }

/-- A two-token typed regular pattern for `New York`. -/
private def regularNewYork : Regular TokenAtom :=
  .seq (.atom (.form (.equal "New"))) (.atom (.form (.equal "York")))

/-- Extract a successful flat output, using a sentinel for an unexpected checked failure. -/
private def classesOf (compiled : Except RegexNerCompileError RegexNerModel)
    (doc : Doc [.tokens]) : Array String :=
  match compiled with
  | .error _ => #["unexpected-compile-error"]
  | .ok model =>
      match model.tagDocument doc with
      | .ok output => output.ner
      | .error _ => #["unexpected-document-error"]

/-- A later, higher-priority short match wins without changing the longer match's remainder. -/
private def highPriorityModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .phrase #["New", "York", "City"], entityClass := "LONG",
        priority := 1.0 },
      { pattern := .phrase #["New", "York"], entityClass := "SHORT", priority := 2.0 }]

example : classesOf highPriorityModel newYorkCity = #["SHORT", "SHORT", "O"] := by
  native_decide

/-- Equal priority prefers the longer overlapping span. -/
private def longerModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .phrase #["New", "York"], entityClass := "SHORT", priority := 1.0 },
      { pattern := .phrase #["New", "York", "City"], entityClass := "LONG",
        priority := 1.0 }]

example : classesOf longerModel newYorkCity = #["LONG", "LONG", "LONG"] := by
  native_decide

/-- Exact duplicate spans retain the lower source ordinal deterministically. -/
private def duplicateModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .phrase #["New", "York"], entityClass := "FIRST", priority := 1.0 },
      { pattern := .phrase #["New", "York"], entityClass := "SECOND", priority := 1.0 }]

example : classesOf duplicateModel newYorkCity = #["FIRST", "FIRST", "O"] := by
  native_decide

/-- Mixed-lane exact ties also use the original mixed source ordinal. -/
private def mixedTieModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .regular regularNewYork, entityClass := "REGULAR", priority := 4.0 },
      { pattern := .phrase #["New", "York"], entityClass := "PHRASE", priority := 4.0 }]

example : classesOf mixedTieModel newYorkCity = #["REGULAR", "REGULAR", "O"] := by
  native_decide

/-- Reversing mixed source order reverses an otherwise exact tie. -/
private def reversedMixedTieModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .phrase #["New", "York"], entityClass := "PHRASE", priority := 4.0 },
      { pattern := .regular regularNewYork, entityClass := "REGULAR", priority := 4.0 }]

example : classesOf reversedMixedTieModel newYorkCity = #["PHRASE", "PHRASE", "O"] := by
  native_decide

/-- Advertised sentence boundaries prevent exact and regular patterns from matching across them. -/
private def splitNewYork : Doc [.sents, .tokens] :=
  { text := "New York"
    spans := #[⟨0, 3⟩, ⟨4, 8⟩]
    forms := #["New", "York"]
    sentEnd := #[1, 2] }

/-- Both matching lanes contain the same otherwise crossing two-token pattern. -/
private def crossingModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .regular regularNewYork, entityClass := "REGULAR" },
      { pattern := .phrase #["New", "York"], entityClass := "PHRASE" }]

/-- Check that neither matching lane crosses an advertised sentence boundary. -/
private def crossingBlocked : Bool :=
  match crossingModel with
  | .error _ => false
  | .ok model =>
      match model.tagDocument splitNewYork with
      | .ok output => output.ner == #["O", "O"] && decide output.SemanticWF
      | .error _ => false

#guard crossingBlocked

/-- Existing entity runs used by complete-run and split-boundary protection tests. -/
private def entities : Doc [.ner, .tokens] :=
  { text := "a b c d"
    spans := #[⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩, ⟨6, 7⟩]
    forms := #["a", "b", "c", "d"]
    ner := #["O", "PERSON", "PERSON", "O"] }

/-- A complete existing run can be replaced when its class is explicitly overwriteable. -/
private def completeRunModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .phrase #["b", "c"], entityClass := "ORG",
        overwriteable := #["PERSON"] }]

/-- Check complete replacement together with preservation of every non-NER document field. -/
private def completeRunRewritten : Bool :=
  match completeRunModel with
  | .error _ => false
  | .ok model =>
      match model.tagDocument entities with
      | .ok output =>
          output.ner == #["O", "ORG", "ORG", "O"] && output.text == entities.text &&
            output.forms == entities.forms && output.spans == entities.spans &&
            decide output.SemanticWF
      | .error _ => false

#guard completeRunRewritten

/-- Permission alone cannot authorize a span beginning inside an existing entity run. -/
private def splitLeftModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .phrase #["c", "d"], entityClass := "ORG",
        overwriteable := #["PERSON"] }]

/-- Permission alone cannot authorize a span ending inside an existing entity run. -/
private def splitRightModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .phrase #["a", "b"], entityClass := "ORG",
        overwriteable := #["PERSON"] }]

/-- A complete non-background run is protected unless its label is explicitly overwriteable. -/
private def protectedRunModel : Except RegexNerCompileError RegexNerModel :=
  compileModel #[{ pattern := .phrase #["b", "c"], entityClass := "ORG" }]

/-- Check both boundary directions and the explicit overwrite-label requirement together. -/
private def existingRunProtection : Bool :=
  let expected := #["O", "PERSON", "PERSON", "O"]
  match splitLeftModel, splitRightModel, protectedRunModel with
  | .ok leftModel, .ok rightModel, .ok protectedModel =>
    match leftModel.tagDocument entities, rightModel.tagDocument entities,
        protectedModel.tagDocument entities with
    | .ok left, .ok right, .ok protectedOutput =>
        left.ner == expected && right.ner == expected && protectedOutput.ner == expected
    | _, _, _ => false
  | _, _, _ => false

#guard existingRunProtection

/-- Same-class runs on opposite sides of a sentence boundary remain sentence-local. -/
private def adjacentSentenceEntities : Doc [.ner, .sents, .tokens] :=
  { text := "a b"
    spans := #[⟨0, 1⟩, ⟨2, 3⟩]
    forms := #["a", "b"]
    sentEnd := #[1, 2]
    ner := #["PERSON", "PERSON"] }

/-- One complete-token rewrite for each adjacent sentence. -/
private def adjacentSentenceModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .phrase #["a"], entityClass := "LEFT",
        overwriteable := #["PERSON"] },
      { pattern := .phrase #["b"], entityClass := "RIGHT",
        overwriteable := #["PERSON"] }]

/-- Check that equal labels across a sentence fencepost do not merge protected runs. -/
private def adjacentSentenceRunsAreIndependent : Bool :=
  match adjacentSentenceModel with
  | .error _ => false
  | .ok model =>
      match model.tagDocument adjacentSentenceEntities with
      | .ok output => output.ner == #["LEFT", "RIGHT"] && decide output.SemanticWF
      | .error _ => false

#guard adjacentSentenceRunsAreIndependent

/-- The exposed seam threads by-value classes through separately cancellable sentence kernels. -/
private def repeatedNewYork : Doc [.sents, .tokens] :=
  { text := "New York New York"
    spans := #[⟨0, 3⟩, ⟨4, 8⟩, ⟨9, 12⟩, ⟨13, 17⟩]
    forms := #["New", "York", "New", "York"]
    sentEnd := #[2, 4] }

/-- Exact phrase model used to exercise the exposed range seam. -/
private def seamModel : Except RegexNerCompileError RegexNerModel :=
  compileModel #[{ pattern := .phrase #["New", "York"], entityClass := "PLACE" }]

/-- Validate, rewrite two ranges separately, then assemble one checked document. -/
private def rangeSeam : Bool :=
  match seamModel with
  | .error _ => false
  | .ok model =>
      match model.validateDocument repeatedNewYork with
      | .error _ => false
      | .ok checked =>
          let initial := RegexNerModel.initialClasses checked
          match RegexNerModel.rewriteRange checked initial 0 2 with
          | .error _ => false
          | .ok first =>
              if first != #["PLACE", "PLACE", "O", "O"] then
                false
              else
                match RegexNerModel.rewriteRange checked first 2 4 with
                | .error _ => false
                | .ok second =>
                    match RegexNerModel.assembleDocument checked second with
                    | .ok output =>
                        output.ner == #["PLACE", "PLACE", "PLACE", "PLACE"] &&
                          decide output.SemanticWF
                    | .error _ => false

#guard rangeSeam

/-- Advertised aligned classes are preserved; unadvertised stale storage becomes background. -/
private def staleClasses : Doc [.tokens] :=
  { newYorkCity with ner := #["STALE", "STALE", "STALE"] }

/-- Initial classes respect advertised layers only after session validation. -/
private def initialClassPolicy : Bool :=
  match seamModel with
  | .error _ => false
  | .ok model =>
      match model.validateDocument entities, model.validateDocument staleClasses with
      | .ok present, .ok stale =>
          RegexNerModel.initialClasses present == entities.ner &&
            RegexNerModel.initialClasses stale == #["O", "O", "O"]
      | _, _ => false

#guard initialClassPolicy

/-- Required optional columns are retained once and rejected before matching when absent. -/
private def fieldModel : Except RegexNerCompileError RegexNerModel :=
  compileModel
    #[{ pattern := .regular
          (.atom (.both (.pos (.prefix "NN")) (.lemma (.equal "city")))),
        entityClass := "PLACE" }]

/-- Check stable required-layer collection and original source-rule count. -/
private def fieldMetadata : Bool :=
  match fieldModel with
  | .ok model => model.requiredLayers == [.tokens, .pos, .lemma] && model.ruleCount == 1
  | .error _ => false

#guard fieldMetadata

/-- Check deterministic rejection of the first unavailable optional token column. -/
private def missingFieldRejected : Bool :=
  match fieldModel with
  | .error _ => false
  | .ok model =>
      match model.tagDocument newYorkCity with
      | .error (.missingLayer .pos) => true
      | _ => false

#guard missingFieldRejected

/-- Diagnostic identity replacement changes no compiled rule count or requirements. -/
private def diagnosticSourcePreserved : Bool :=
  match fieldModel with
  | .error _ => false
  | .ok model =>
      let renamed := model.withDiagnosticSource "models/regexner.rules"
      renamed.diagnosticSource == "models/regexner.rules" &&
        renamed.ruleCount == model.ruleCount &&
        decide (renamed.requiredLayers = model.requiredLayers)

#guard diagnosticSourcePreserved

/-- Source validation retains exact mixed ordinals and floating-point bits. -/
private def invalidSourcesRejected : Bool :=
  let nan := Float.ofBits 0x7ff8000000000001
  let regular : RegexNerRule := { pattern := .regular .epsilon, entityClass := "X" }
  let emptyEntity : RegexNerRule := { pattern := .regular .epsilon, entityClass := "" }
  let reservedEntity : RegexNerRule := { pattern := .regular .epsilon, entityClass := "O" }
  let badPriority : RegexNerRule :=
    { pattern := .regular .epsilon, entityClass := "X", priority := nan }
  match RegexNerModel.compile #[regular, emptyEntity],
      RegexNerModel.compile #[regular, reservedEntity],
      RegexNerModel.compile #[regular, badPriority],
      RegexNerModel.compile #[regular, { pattern := .phrase #[], entityClass := "X" }],
      RegexNerModel.compile
        #[regular, { pattern := .phrase #["ok", ""], entityClass := "X" }] with
  | .error (.emptyEntity 1), .error (.reservedEntity 1),
      .error (.invalidPriority 1 value bits),
      .error (.emptyPhrase 1), .error (.emptyPhraseToken 1 1) =>
      value.isNaN && bits == nan.toBits
  | _, _, _, _, _ => false

#guard invalidSourcesRejected

/-- Infinite priorities and both compiler-lane resource failures are typed. -/
private def boundedCompilationRejected : Bool :=
  let infinite : RegexNerRule :=
    { pattern := .regular .epsilon, entityClass := "X", priority := 1.0 / 0.0 }
  let regularRule : RegexNerRule :=
    { pattern := .regular (.atom (.form .any)), entityClass := "X" }
  let phraseRule : RegexNerRule := { pattern := .phrase #["x"], entityClass := "X" }
  match RegexNerModel.compile #[infinite],
      RegexNerModel.compileWith { regular := { maxStates := 1 } } #[regularRule],
      RegexNerModel.compileWith { phrase := { maxNodes := 1 } } #[phraseRule] with
  | .error (.invalidPriority 0 value _),
      .error (.regular (.stateBudget 2 1)),
      .error (.phrase (.nodeBudget 2 1)) =>
      !value.isFinite
  | _, _, _ => false

#guard boundedCompilationRejected

/-- Mixed metadata and source payloads are bounded before lane-specific allocation. -/
private def sourceBudgetsRejected : Bool :=
  let regularRule : RegexNerRule :=
    { pattern := .regular (.atom (.form .any)), entityClass := "X" }
  match RegexNerModel.compileWith { maxRules := 0 } #[regularRule],
      RegexNerModel.compileWith { maxPayloadEntries := 3 } #[regularRule],
      RegexNerModel.compileWith { maxSourceBytes := 0 } #[regularRule] with
  | .error (.ruleBudget 1 0), .error (.payloadBudget 4 3),
      .error (.sourceByteBudget 1 0) => true
  | _, _, _ => false

#guard sourceBudgetsRejected

/-- Retained range policies reject excessive NFA work and combined candidates exactly. -/
private def runtimeBudgetsRejected : Bool :=
  let regularRule : RegexNerRule :=
    { pattern := .regular (.atom (.form .any)), entityClass := "TOKEN" }
  let phraseRule : RegexNerRule :=
    { pattern := .phrase #["New"], entityClass := "WORD" }
  let regular := RegexNerModel.compileWith { search := { maxWork := 0 } } #[regularRule]
  let phrase := RegexNerModel.compileWith { search := { maxMatches := 0 } } #[phraseRule]
  match regular, phrase with
  | .ok regularModel, .ok phraseModel =>
      match regularModel.tagDocument newYorkCity, phraseModel.tagDocument newYorkCity with
      | .error (.searchWorkBudget required 0), .error (.candidateBudget 1 0) =>
          0 < required
      | _, _ => false
  | _, _ => false

#guard runtimeBudgetsRejected

/-- Nullable regular rules emit no zero-width rewrite and cannot stall document tagging. -/
private def nullableModel : Except RegexNerCompileError RegexNerModel :=
  compileModel #[{ pattern := .regular .epsilon, entityClass := "EMPTY" }]

example : classesOf nullableModel newYorkCity = #["O", "O", "O"] := by
  native_decide

/-- Malformed documents and misaligned seam arrays fail at their typed boundary. -/
private def malformed : Doc [.tokens] :=
  { newYorkCity with spans := #[⟨0, 3⟩] }

/-- Check semantic input failure and both range-seam class-alignment failures. -/
private def checkedBoundaryFailures : Bool :=
  match seamModel with
  | .error _ => false
  | .ok model =>
      match model.validateDocument newYorkCity with
      | .error _ => false
      | .ok checked =>
          match model.tagDocument malformed,
              RegexNerModel.rewriteRange checked #["O"] 0 3,
              RegexNerModel.assembleDocument checked #["O"] with
          | .error (.input (.structural _)), .error (.classAlignment 3 1),
              .error (.classAlignment 3 1) => true
          | _, _, _ => false

#guard checkedBoundaryFailures

end NlpTests.Pattern.RegexNer
