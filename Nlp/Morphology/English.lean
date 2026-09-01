import Std.Data.HashMap
import Nlp.Morphology.Rewrite

/-!
# English inflectional morphology

The productive rules are the public WordNet Morphy detachment table.  Exceptions and the lexical
index remain caller-supplied model data: analysis accepts a rewrite only when its candidate occurs
in that syntactic category.  This separation avoids importing WordNet data while retaining its
exception-first, lexicon-validated algorithm.

Lookup is deliberately case-sensitive.  Callers choose any case-normalization policy before model
construction and analysis; proper nouns have their own category and receive no productive rule.

Source: Princeton WordNet 3.0, `morphy(7WN)`, "Rules of Detachment".
-/

namespace Nlp.Morphology

/-- A lexical-index key, intentionally distinct across syntactic categories. -/
structure Key where
  pos : Pos
  form : String
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- One base form admitted by a caller-supplied lexical index. -/
structure Lexeme where
  pos : Pos
  lemma : String
  deriving Repr, DecidableEq, Inhabited

/-- One irregular surface-to-base mapping; multiple rows may share the same surface. -/
structure ExceptionEntry where
  pos : Pos
  surface : String
  lemma : String
  deriving Repr, DecidableEq, Inhabited

/-- Why a morphology model could not be constructed. -/
inductive CompileError where
  | emptyLexeme (index : Nat)
  | emptyExceptionSurface (index : Nat)
  | emptyExceptionLemma (index : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace English

/-- WordNet noun detachment rules, in the normative published order. -/
def nounRules : Array Rewrite :=
  #[⟨"s", ""⟩, ⟨"ses", "s"⟩, ⟨"xes", "x"⟩, ⟨"zes", "z"⟩,
    ⟨"ches", "ch"⟩, ⟨"shes", "sh"⟩, ⟨"men", "man"⟩, ⟨"ies", "y"⟩]

/-- WordNet verb detachment rules, including both candidates for ambiguous endings. -/
def verbRules : Array Rewrite :=
  #[⟨"s", ""⟩, ⟨"ies", "y"⟩, ⟨"es", "e"⟩, ⟨"es", ""⟩,
    ⟨"ed", "e"⟩, ⟨"ed", ""⟩, ⟨"ing", "e"⟩, ⟨"ing", ""⟩]

/-- WordNet adjective detachment rules. -/
def adjectiveRules : Array Rewrite :=
  #[⟨"er", ""⟩, ⟨"est", ""⟩, ⟨"er", "e"⟩, ⟨"est", "e"⟩]

/-- The productive rule table for one syntactic category. -/
@[inline] def rules : Pos → Array Rewrite
  | .noun => nounRules
  | .verb | .auxiliary => verbRules
  | .adjective => adjectiveRules
  | .properNoun | .adverb | .particle | .other => #[]

/-- Enumerate every relational analysis licensed by the productive rules. -/
def derivations (pos : Pos) (surface : String) : Array Derivation := Id.run do
  let mut output := Array.emptyWithCapacity (rules pos).size
  for rule in rules pos do
    match rule.analyze? surface with
    | some derivation =>
      unless derivation.lemma.isEmpty do
        output := output.push derivation
    | none => pure ()
  return output

/-- Enumerate the automatically derived generator forms from the inverse rule relation. -/
def generations (pos : Pos) (lemma : String) : Array Derivation := Id.run do
  if lemma.isEmpty then
    return #[]
  let mut output := Array.emptyWithCapacity (rules pos).size
  for rule in rules pos do
    match rule.generate? lemma with
    | some derivation =>
      unless derivation.surface.isEmpty do
        output := output.push derivation
    | none => pure ()
  return output

end English

/-- Provenance for one selected or generated morphological analysis. -/
inductive Origin where
  | identity
  | exception
  | rule (rewrite : Rewrite)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- One surface/lemma relation with its syntactic category and provenance. -/
structure Analysis where
  surface : String
  lemma : String
  pos : Pos
  origin : Origin
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A compiled English morphology model with forward and reverse exception indexes. -/
structure Model where
  private mk ::
  lexicon : Std.HashMap Key Unit
  exceptions : Std.HashMap Key (Array String)
  generators : Std.HashMap Key (Array String)

namespace Model

private def insertUnique (map : Std.HashMap Key (Array String)) (key : Key)
    (value : String) : Std.HashMap Key (Array String) :=
  let values := map.getD key #[]
  if values.contains value then map else map.insert key (values.push value)

/-- Validate and compile lexical and exception data into immutable lookup indexes. -/
def compile (lexemes : Array Lexeme) (exceptionEntries : Array ExceptionEntry) :
    Except CompileError Model := do
  let mut lexicon : Std.HashMap Key Unit := {}
  for index in [0:lexemes.size] do
    let lexeme := lexemes[index]!
    if lexeme.lemma.isEmpty then
      throw (.emptyLexeme index)
    lexicon := lexicon.insert ⟨lexeme.pos, lexeme.lemma⟩ ()
  let mut exceptions : Std.HashMap Key (Array String) := {}
  let mut generators : Std.HashMap Key (Array String) := {}
  for index in [0:exceptionEntries.size] do
    let entry := exceptionEntries[index]!
    if entry.surface.isEmpty then
      throw (.emptyExceptionSurface index)
    if entry.lemma.isEmpty then
      throw (.emptyExceptionLemma index)
    exceptions := insertUnique exceptions ⟨entry.pos, entry.surface⟩ entry.lemma
    generators := insertUnique generators ⟨entry.pos, entry.lemma⟩ entry.surface
  return ⟨lexicon, exceptions, generators⟩

/-- The empty validated model; useful for identity-preserving pipelines and incremental loading. -/
def empty : Model :=
  ⟨{}, {}, {}⟩

/-- Whether the lexical index admits a base form in one syntactic category. -/
@[inline] def contains (model : Model) (pos : Pos) (lemma : String) : Bool :=
  model.lexicon.contains ⟨pos, lemma⟩

private def licensedRuleAnalysis? (model : Model) (pos : Pos) (surface : String)
    (rule : Rewrite) : Option Analysis := do
  let derivation ← rule.analyze? surface
  let lemma := derivation.lemma
  if !lemma.isEmpty && model.contains pos lemma then
    some ⟨surface, lemma, pos, .rule rule⟩
  else
    none

private def firstRuleAnalysisAux (model : Model) (pos : Pos) (surface : String)
    (rules : Array Rewrite) : Nat → Nat → Option Analysis
  | 0, _ => none
  | fuel + 1, index =>
    match rules[index]? with
    | none => none
    | some rule =>
      match licensedRuleAnalysis? model pos surface rule with
      | some analysis => some analysis
      | none => firstRuleAnalysisAux model pos surface rules fuel (index + 1)

private def collectRuleAnalysesAux (model : Model) (pos : Pos) (surface : String)
    (rules : Array Rewrite) : Nat → Nat → Array Analysis
  | 0, _ => #[]
  | fuel + 1, index =>
    match rules[index]? with
    | none => #[]
    | some rule =>
      let remaining := collectRuleAnalysesAux model pos surface rules fuel (index + 1)
      match licensedRuleAnalysis? model pos surface rule with
      | some analysis => #[analysis] ++ remaining
      | none => remaining

private theorem firstRuleAnalysisAux_eq_head (model : Model) (pos : Pos) (surface : String)
    (rules : Array Rewrite) (fuel index : Nat) :
    firstRuleAnalysisAux model pos surface rules fuel index =
      (collectRuleAnalysesAux model pos surface rules fuel index)[0]? := by
  induction fuel generalizing index with
  | zero => simp [firstRuleAnalysisAux, collectRuleAnalysesAux]
  | succ fuel ih =>
    simp only [firstRuleAnalysisAux, collectRuleAnalysesAux]
    cases rules[index]? with
    | none => rfl
    | some rule =>
      cases found : licensedRuleAnalysis? model pos surface rule with
      | none => simpa [found] using ih (index + 1)
      | some analysis => simp [found, Array.getElem?_append]

private def firstRuleAnalysis? (model : Model) (pos : Pos)
    (surface : String) : Option Analysis :=
  let rules := English.rules pos
  firstRuleAnalysisAux model pos surface rules rules.size 0

private def ruleAnalyses (model : Model) (pos : Pos) (surface : String) : Array Analysis :=
  let rules := English.rules pos
  collectRuleAnalysesAux model pos surface rules rules.size 0

private theorem firstRuleAnalysis?_eq_head (model : Model) (pos : Pos) (surface : String) :
    firstRuleAnalysis? model pos surface = (ruleAnalyses model pos surface)[0]? :=
  firstRuleAnalysisAux_eq_head model pos surface (English.rules pos) (English.rules pos).size 0

private def diagnosticAnalyses (model : Model) (pos : Pos)
    (surface : String) : Array Analysis :=
  match model.exceptions.get? ⟨pos, surface⟩ with
  | some lemmas => lemmas.map fun lemma ↦ ⟨surface, lemma, pos, .exception⟩
  | none =>
    if model.contains pos surface then
      #[⟨surface, surface, pos, .identity⟩] ++ model.ruleAnalyses pos surface
    else
      model.ruleAnalyses pos surface

private def firstAnalysis? (model : Model) (pos : Pos) (surface : String) : Option Analysis :=
  match model.exceptions.get? ⟨pos, surface⟩ with
  | some lemmas => lemmas[0]?.map fun lemma ↦ ⟨surface, lemma, pos, .exception⟩
  | none =>
    if model.contains pos surface then some ⟨surface, surface, pos, .identity⟩
    else firstRuleAnalysis? model pos surface

private theorem firstAnalysis?_eq_diagnostic_head (model : Model) (pos : Pos)
    (surface : String) :
    firstAnalysis? model pos surface = (diagnosticAnalyses model pos surface)[0]? := by
  unfold firstAnalysis? diagnosticAnalyses
  cases model.exceptions.get? ⟨pos, surface⟩ with
  | some lemmas =>
    cases lemmas using Array.casesOn <;> simp
  | none =>
    by_cases identity : model.contains pos surface
    · simp [identity, Array.getElem?_append]
    · simpa [identity] using firstRuleAnalysis?_eq_head model pos surface

/--
Return every licensed analysis in stable priority order.

Irregular exceptions are authoritative.  Otherwise an exact lexical hit precedes productive
detachment candidates, each of which must also occur in the supplied lexical index.
-/
def analyses (model : Model) (pos : Pos) (surface : String) : Array Analysis :=
  diagnosticAnalyses model pos surface

/-- Return the highest-priority licensed lemma without materializing diagnostic alternatives. -/
@[inline] def lemma? (model : Model) (pos : Pos) (surface : String) : Option String :=
  (model.firstAnalysis? pos surface).map Analysis.lemma

/-- The allocation-light selected lemma is exactly the head of the diagnostic candidate array. -/
theorem lemma?_eq_analyses_head (model : Model) (pos : Pos) (surface : String) :
    model.lemma? pos surface = (model.analyses pos surface)[0]?.map Analysis.lemma := by
  rw [lemma?, analyses, firstAnalysis?_eq_diagnostic_head]

/-- Conservative total lemmatization: retain the source spelling when no analysis is licensed. -/
@[inline] def lemmaOrSelf (model : Model) (pos : Pos) (surface : String) : String :=
  (model.lemma? pos surface).getD surface

private def pushUniqueSurface (output : Array Analysis) (analysis : Analysis) : Array Analysis :=
  if output.any fun present ↦ present.surface == analysis.surface then output
  else output.push analysis

/--
Enumerate generator candidates from the exact inverse relation.

Generation is intentionally many-valued: reversed exception rows are followed by the unchanged
lemma and productive inverse-rule candidates.  This does not claim that the complete
lexicon-filtered analyzer is bijective; callers must rank or filter the generated surfaces.
-/
def generate (model : Model) (pos : Pos) (lemma : String) : Array Analysis := Id.run do
  if lemma.isEmpty then
    return #[]
  let mut output := #[]
  match model.generators.get? ⟨pos, lemma⟩ with
  | some surfaces =>
    for surface in surfaces do
      output := pushUniqueSurface output ⟨surface, lemma, pos, .exception⟩
  | none => pure ()
  output := pushUniqueSurface output ⟨lemma, lemma, pos, .identity⟩
  for derivation in English.generations pos lemma do
    output := pushUniqueSurface output
      ⟨derivation.surface, lemma, pos, .rule derivation.rule⟩
  return output

end Model

end Nlp.Morphology
