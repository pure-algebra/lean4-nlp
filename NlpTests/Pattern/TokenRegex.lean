import Nlp.Pattern.TokenRegex

/-! # Bounded textual token-regex tests -/

namespace NlpTests.Pattern.TokenRegex

open Nlp Nlp.Pattern Nlp.Pattern.TokenRegex

private def language? (source : String) : Option (Regular TokenAtom) :=
  (parse source).toOption.map Pattern.language

private def parseError? (config : ParseConfig) (source : String) : Option ParseError :=
  match parseWith config source with
  | .ok _ => none
  | .error error => some error

private def handBuilt : Regular TokenAtom :=
  .seq
    (.seq (.atom (.form (.equal "New"))) (.atom (.pos (.equal "NNP"))))
    (.atom (.ner (.equal "CITY")))

/-- Exact field aliases and implicit sequence concatenation lower faithfully. -/
example :
    language? "[word:\"New\"] [tag:NNP] [ner:CITY]" = some handBuilt := by
  native_decide

/-- Token-local Boolean precedence is negation, conjunction, then alternation. -/
example :
    language? "[{word:a} | !{lemma:b} & {pos:C}]" =
      some (.atom (.either (.form (.equal "a"))
        (.both (.negate (.lemma (.equal "b"))) (.pos (.equal "C"))))) := by
  native_decide

/-- Empty brackets are the typed any-token predicate. -/
example : language? "[]" = some (.atom (.form .any)) := by
  native_decide

/-- Noncapturing grouping and sequence alternation preserve precedence. -/
example :
    language? "(?:[word:a] [word:b]|[word:c]) [lemma:d]" =
      some (.seq
        (.alt (.seq (.atom (.form (.equal "a"))) (.atom (.form (.equal "b"))))
          (.atom (.form (.equal "c"))))
        (.atom (.lemma (.equal "d")))) := by
  native_decide

/-- Greedy regular quantifiers lower only to the existing six-constructor kernel. -/
example :
    language? "[word:a]? [word:b]* [word:c]+" =
      some (.seq
        (.seq (.alt (.atom (.form (.equal "a"))) .epsilon)
          (.star (.atom (.form (.equal "b")))))
        (.seq (.atom (.form (.equal "c")))
          (.star (.atom (.form (.equal "c")))))) := by
  native_decide

/-- Bounded and lower-unbounded repetition lower to balanced regular concatenations. -/
example :
    language? "[word:x]{2,4}" =
      some (.seq
        (.seq (.atom (.form (.equal "x"))) (.atom (.form (.equal "x"))))
        (.seq
          (.alt (.atom (.form (.equal "x"))) .epsilon)
          (.alt (.atom (.form (.equal "x"))) .epsilon))) := by
  native_decide

example :
    language? "[word:x]{2,}" =
      some (.seq
        (.seq (.atom (.form (.equal "x"))) (.atom (.form (.equal "x"))))
        (.star (.atom (.form (.equal "x"))))) := by
  native_decide

/-- Exact repetition includes the zero case without manufacturing a consuming atom. -/
example :
    language? "[word:x]{0}" = some .epsilon &&
      language? "[word:x]{3}" =
        some (.seq
          (.seq (.atom (.form (.equal "x"))) (.atom (.form (.equal "x"))))
          (.atom (.form (.equal "x")))) := by
  native_decide

/-- Parsed requirements are retained without recursive post-validation. -/
example : (parse "[lemma:x] [pos:Y] [lemma:z]").toOption.map Pattern.requiredLayers =
    some [.tokens, .lemma, .pos] := by
  native_decide

/-- The source-byte budget accepts its exact boundary and rejects one byte less. -/
example :
    (parseWith { maxSourceBytes := 8 } "[word:a]").isOk &&
      parseError? { maxSourceBytes := 7 } "[word:a]" ==
        some ⟨.sourceByteBudget 8 7, ⟨0, 8⟩⟩ := by
  native_decide

/-- The lexeme budget accepts its exact count and reports the first unretained item. -/
example :
    (parseWith { maxLexemes := 5 } "[word:a]").isOk &&
      parseError? { maxLexemes := 4 } "[word:a]" ==
        some ⟨.lexemeBudget 5 4, ⟨7, 8⟩⟩ := by
  native_decide

/-- The nesting budget accepts its exact depth and rejects one level less. -/
example :
    (parseWith { maxNesting := 2 } "(?:[word:a])").isOk &&
      parseError? { maxNesting := 1 } "(?:[word:a])" ==
        some ⟨.nestingBudget 2 1, ⟨3, 4⟩⟩ := by
  native_decide

/-- Expanded regular-node accounting has exact and one-short behavior. -/
example :
    (parseWith { maxExpandedNodes := 4 } "[word:a]+").isOk &&
      parseError? { maxExpandedNodes := 3 } "[word:a]+" ==
        some ⟨.expandedNodeBudget 4 3, ⟨8, 9⟩⟩ := by
  native_decide

/-- Repeat duplication and connectors are included in the exact expanded-node charge. -/
example :
    (parseWith { maxExpandedNodes := 11 } "[word:x]{2,4}").toOption.map
        Pattern.expandedNodeCount == some 11 &&
      parseError? { maxExpandedNodes := 10 } "[word:x]{2,4}" ==
        some ⟨.expandedNodeBudget 11 10, ⟨8, 13⟩⟩ := by
  native_decide

/-- UTF-8 diagnostics use bytes, not scalar or UTF-16 coordinates. -/
example :
    parseError? {} "[word:\"é\"] ^" ==
      some ⟨.unsupported .anchor, ⟨12, 13⟩⟩ := by
  native_decide

/-- Unsupported slash literals consume their complete escape-aware lexical item. -/
example :
    parseError? {} "/a\\/b/ [word:x]" ==
      some ⟨.unsupported .regexLiteral, ⟨0, 6⟩⟩ := by
  native_decide

/-- Unsupported reluctant, backreference, macro, capture, anchor, and action syntax is explicit. -/
example :
    parseError? {} "[word:a]*?" ==
        some ⟨.unsupported .reluctantQuantifier, ⟨8, 10⟩⟩ &&
      parseError? {} "\\123" ==
        some ⟨.unsupported .backreference, ⟨0, 4⟩⟩ &&
      parseError? {} "$THING" ==
        some ⟨.unsupported .macro, ⟨0, 6⟩⟩ &&
      parseError? {} "([word:a])" ==
        some ⟨.unsupported .capturingGroup, ⟨0, 1⟩⟩ &&
      parseError? {} "$" ==
        some ⟨.unsupported .anchor, ⟨0, 1⟩⟩ &&
      parseError? {} "[word:a] ==> x" ==
        some ⟨.unsupported .action, ⟨9, 12⟩⟩ := by
  native_decide

/-- Repeat-bound failures are checked before repeat-sized arrays are allocated. -/
example :
    parseError? { maxExpandedNodes := 32 } "[word:x]{999999999999999999999}" ==
      some ⟨.expandedNodeBudget 33 32, ⟨9, 30⟩⟩ := by
  native_decide

/-- Inverted bounded repetition is rejected at its complete quantifier span. -/
example :
    parseError? {} "[word:x]{4,2}" ==
      some ⟨.invertedRepeat 4 2, ⟨8, 13⟩⟩ := by
  native_decide

/-- A hostile delimiter depth is stopped at the documented hard implementation cap. -/
private def nestedPattern (depth : Nat) : String :=
  (List.replicate depth "(?:").foldl (· ++ ·) "" ++ "[word:x]" ++
    (List.replicate depth ")").foldl (· ++ ·) ""

example :
    (match parseWith { maxNesting := hardMaxNesting + 100 }
        (nestedPattern (hardMaxNesting + 1)) with
    | .error ⟨.nestingBudget required limit, _⟩ =>
        required == hardMaxNesting + 1 && limit == hardMaxNesting
    | _ => false) = true := by
  native_decide

/-- Long flat source chains lower to logarithmic-depth Boolean and sequence trees. -/
private def repeatedSource (separator item : String) (count : Nat) : String :=
  String.intercalate separator (List.replicate count item)

example :
    (parse (repeatedSource " " "[word:x]" 1024)).toOption.map
        Pattern.expandedNodeCount == some 2047 &&
      (parse ("[" ++ repeatedSource " & " "word:x" 1024 ++ "]")).isOk := by
  native_decide

/-- Flat alternation retains exact linear node growth through one owned active frame. -/
example :
    (parse (repeatedSource " | " "[word:x]" 4096)).toOption.map
      Pattern.expandedNodeCount == some 8191 := by
  native_decide

/-- Reference acceptance agrees with an independently written regular-language pattern. -/
private def forms : Doc [.tokens] :=
  { text := "New NNP CITY"
    forms := #["New", "unused", "unused"]
    spans := #[⟨0, 3⟩, ⟨4, 7⟩, ⟨8, 12⟩]
    pos := #["X", "NNP", "X"]
    ner := #["O", "O", "CITY"] }

example :
    (match parse "[word:New] [pos:NNP] [ner:CITY]" with
    | .error _ => false
    | .ok parsed =>
        parsed.language.matchesRange (TokenAtom.holdsAtUnchecked forms) forms.size 0 3 ==
          handBuilt.matchesRange (TokenAtom.holdsAtUnchecked forms) forms.size 0 3) = true := by
  native_decide

/-- Checked compilation retains source, requirements, and the existing one-rule automaton. -/
example :
    (match compileWith {} {} "[lemma:run]+" with
    | .error _ => false
    | .ok compiled =>
        compiled.source == "[lemma:run]+" &&
          compiled.requiredLayers == [.tokens, .lemma] &&
          compiled.automaton.ruleCount == 1) = true := by
  native_decide

/-- Existing Thompson budgets remain typed at the checked textual compilation seam. -/
example :
    (match compileWith {} { maxStates := 2 } "[word:x]" with
    | .error (.automaton (.stateBudget 3 2)) => true
    | _ => false) = true := by
  native_decide

private def checkedDoc : Doc [.tokens, .pos, .lemma, .ner] :=
  { text := "New runs CITY"
    forms := #["New", "runs", "CITY"]
    spans := #[⟨0, 3⟩, ⟨4, 8⟩, ⟨9, 13⟩]
    pos := #["NNP", "VBZ", "NNP"]
    lemma := #["new", "run", "city"]
    ner := #["O", "O", "CITY"] }

/-- The functional facade validates once and returns absolute proof-carrying matches. -/
example :
    (match compile "[lemma:run] [ner:CITY]" with
    | .error _ => false
    | .ok compiled =>
        match compiled.findOverlappingRange checkedDoc with
        | .ok #[matched] => matched.rule == 0 && matched.start == 1 && matched.stop == 3
        | _ => false) = true := by
  native_decide

/-- Missing advertised columns are distinguished from malformed document storage. -/
example :
    (match compile "[lemma:run]" with
    | .error _ => false
    | .ok compiled =>
        match compiled.findOverlappingRange forms with
        | .error (.missingLayer .lemma) => true
        | _ => false) = true := by
  native_decide

/-- Functional matching retains the existing exact work and output budgets. -/
example :
    (match compile "[word:New]" with
    | .error _ => false
    | .ok compiled =>
        match compiled.findOverlappingRangeWith { maxWork := 0 } checkedDoc with
        | .error (.search (.workBudget required 0)) => 0 < required
        | _ => false) = true := by
  native_decide

end NlpTests.Pattern.TokenRegex
