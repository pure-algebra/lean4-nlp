import Nlp.Pattern.Phrase

/-!
# Exact token-phrase automaton tests

These checks exercise shared prefixes, dictionary suffixes, duplicate rules, range isolation,
out-of-vocabulary resets, and bounded compilation. A small reference matcher differentially checks
the compiled candidate set without depending on automaton emission order.
-/

namespace NlpTests.Pattern.Phrase

open Nlp.Pattern

/-- Extract stable source ordinals and full-input coordinates from phrase matches. -/
private def triples (found : Array PhraseMatch) : Array (Nat × Nat × Nat) :=
  found.map fun matched ↦ (matched.rule, matched.start, matched.stop)

/-- Shared-prefix and suffix rules used by the deterministic regression checks. -/
private def source : Array (Array String) :=
  #[#["New", "York"], #["York"], #["New", "York", "City"],
    #["York", "City"], #["New", "York"]]

/-- Compile the fixed test model or fail loudly during test evaluation. -/
private def model : PhraseAutomaton :=
  match PhraseAutomaton.compile source with
  | .ok value => value
  | .error _ => panic! "fixed phrase model failed to compile"

#guard model.ruleCount == 5
#guard model.vocabularySize == 3
#guard model.nodeCount == 6
#guard ({} : PhraseCompileConfig).maxNodes == 1_048_576
#guard ({} : PhraseCompileConfig).maxRules == 65_536
#guard ({} : PhraseCompileConfig).maxSourceTokens == 1_048_576

/-- Shared prefixes remain distinct and dictionary suffixes emit at the same stop fencepost. -/
example : triples (model.findAll #["I", "love", "New", "York", "City"]) =
    #[(0, 2, 4), (4, 2, 4), (1, 3, 4), (2, 2, 5), (3, 3, 5)] := by
  native_decide

/-- Bounded search succeeds exactly at its output size and fails before one extra emission. -/
private def exactMatchBudget : Bool :=
  let forms := #["New", "York", "City"]
  match model.findAllRangeWithLimit 5 forms 0 forms.size,
      model.findAllRangeWithLimit 4 forms 0 forms.size with
  | .ok found, .error (.matchBudget 5 4) =>
      triples found == #[(0, 0, 2), (4, 0, 2), (1, 1, 2),
        (2, 0, 3), (3, 1, 3)]
  | _, _ => false

#guard exactMatchBudget

/-- A normalized offset range retains full coordinates and cannot cross its lower boundary. -/
example : triples
    (model.findAllRange #["New", "York", "x", "New", "York", "City"] 3 6) =
    #[(0, 3, 5), (4, 3, 5), (1, 4, 5), (2, 3, 6), (3, 4, 6)] := by
  native_decide

/-- Clipping an oversized upper fencepost is exact. -/
example : triples (model.findAllRange #["x", "York"] 1 99) = #[(1, 1, 2)] := by
  native_decide

/-- Reversed and explicitly empty ranges contain no matches. -/
example : model.findAllRange #["New", "York"] 2 1 = #[] := by native_decide
example : model.findAllRange #["New", "York"] 1 1 = #[] := by native_decide

/-- An unknown token resets the failure machine before matching resumes. -/
example : triples (model.findAll #["New", "unknown", "New", "York"]) =
    #[(0, 2, 4), (4, 2, 4), (1, 3, 4)] := by
  native_decide

/-- A three-level dictionary-suffix chain emits every exact suffix once. -/
private def suffixModel : PhraseAutomaton :=
  match PhraseAutomaton.compile #[#["a"], #["b", "a"], #["c", "b", "a"]] with
  | .ok value => value
  | .error _ => panic! "suffix phrase model failed to compile"

example : triples (suffixModel.findAll #["c", "b", "a"]) =
    #[(2, 0, 3), (1, 1, 3), (0, 2, 3)] := by
  native_decide

/-- Check one exact phrase against a caller-selected full-input start. -/
private def referenceAt (phrase forms : Array String) (start : Nat) : Bool := Id.run do
  if forms.size < start + phrase.size then
    return false
  for offset in [0:phrase.size] do
    if phrase[offset]! != forms[start + offset]! then
      return false
  return true

/-- Brute-force exact candidates in source-rule then start order. -/
private def reference (phrases : Array (Array String)) (forms : Array String)
    (start stop : Nat) : Array (Nat × Nat × Nat) := Id.run do
  let (lower, upper) := PhraseAutomaton.normalizeRange forms.size start stop
  let mut output := #[]
  for rule in [0:phrases.size] do
    let phrase := phrases[rule]!
    for position in [lower:upper] do
      let after := position + phrase.size
      if after ≤ upper && referenceAt phrase forms position then
        output := output.push (rule, position, after)
  return output

/-- Candidate arrays agree as finite source-rule/span sets, independently of emission order. -/
private def sameCandidateSet (left right : Array (Nat × Nat × Nat)) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

/-- The compiled machine agrees with a separately shaped brute-force matcher. -/
example : sameCandidateSet
    (triples (model.findAllRange #["York", "New", "York", "City", "York"] 0 5))
    (reference source #["York", "New", "York", "City", "York"] 0 5) = true := by
  native_decide

/-- Empty phrases and empty phrase tokens fail at exact source coordinates. -/
private def emptyPhraseRejected : Bool :=
  match PhraseAutomaton.compile #[#["ok"], #[]] with
  | .error (.emptyPhrase 1) => true
  | _ => false

#guard emptyPhraseRejected

private def emptyTokenRejected : Bool :=
  match PhraseAutomaton.compile #[#["ok", ""]] with
  | .error (.emptyToken 0 1) => true
  | _ => false

#guard emptyTokenRejected

/-- A hard node budget reports the first required node count. -/
private def nodeBudgetRejected : Bool :=
  match PhraseAutomaton.compile #[#["a"]] { maxNodes := 1 } with
  | .error (.nodeBudget 2 1) => true
  | _ => false

#guard nodeBudgetRejected

/-- Duplicate phrases can sit exactly on every configured allocation-driving boundary. -/
private def exactDuplicateBudgetsAccepted : Bool :=
  let phrases := #[#["same"], #["same"]]
  let config : PhraseCompileConfig :=
    { maxNodes := 2, maxRules := 2, maxSourceTokens := 2 }
  match PhraseAutomaton.compile phrases config with
  | .ok compiled =>
      compiled.ruleCount == 2 && compiled.nodeCount == 2 &&
        compiled.vocabularySize == 1 &&
        triples (compiled.findAll #["same"]) == #[(0, 0, 1), (1, 0, 1)]
  | .error _ => false

#guard exactDuplicateBudgetsAccepted

/-- The rule budget rejects duplicate-heavy sources before node or token allocation policies. -/
private def duplicateRuleBudgetRejected : Bool :=
  let phrases := #[#["same"], #["same"], #["same"]]
  let config : PhraseCompileConfig :=
    { maxNodes := 0, maxRules := 2, maxSourceTokens := 0 }
  match PhraseAutomaton.compile phrases config with
  | .error (.ruleBudget 3 2) => true
  | _ => false

#guard duplicateRuleBudgetRejected

/-- Cumulative source tokens count duplicates even when every phrase shares one trie edge. -/
private def duplicateSourceTokenBudgetRejected : Bool :=
  let phrases := #[#["same"], #["same"], #["same"]]
  let config : PhraseCompileConfig :=
    { maxNodes := 2, maxRules := 3, maxSourceTokens := 2 }
  match PhraseAutomaton.compile phrases config with
  | .error (.sourceTokenBudget 3 2) => true
  | _ => false

#guard duplicateSourceTokenBudgetRejected

/-- Full structural validation retains an empty-phrase ordinal before aggregate budget errors. -/
private def emptyPhrasePrecedesAggregateBudgets : Bool :=
  let phrases := #[#["ok"], #[]]
  let config : PhraseCompileConfig :=
    { maxNodes := 0, maxRules := 2, maxSourceTokens := 0 }
  match PhraseAutomaton.compile phrases config with
  | .error (.emptyPhrase 1) => true
  | _ => false

#guard emptyPhrasePrecedesAggregateBudgets

/-- Full structural validation retains an empty-token ordinal before aggregate budget errors. -/
private def emptyTokenPrecedesAggregateBudgets : Bool :=
  let phrases := #[#["ok"], #["also", ""]]
  let config : PhraseCompileConfig :=
    { maxNodes := 0, maxRules := 2, maxSourceTokens := 0 }
  match PhraseAutomaton.compile phrases config with
  | .error (.emptyToken 1 1) => true
  | _ => false

#guard emptyTokenPrecedesAggregateBudgets

/-- Every executable match exposes its proof-carrying positive-width invariant. -/
example (matched : PhraseMatch) : 0 < matched.width :=
  matched.width_pos

end NlpTests.Pattern.Phrase
