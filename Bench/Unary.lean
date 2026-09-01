import Nlp.Grammar.Unary

/-!
# Unary-elimination benchmark

This standalone native benchmark builds every source grammar through public treebank induction.
It measures a no-unary baseline, a long chain whose only base rule is at the sink, and a layered
diamond both within budget and at a deliberate path-cap failure. Fixture construction and one
warm-up elimination occur outside each timed region.

The fixed defaults are intended to finish quickly in CI and ordinary manual release builds. The
report consumes every path, arena step, emitted rule, and provenance entry in a deterministic
checksum; no machine-specific performance threshold is asserted.
-/

namespace UnaryBenchmark

open Nlp Nlp.Grammar

/-- Structural and output counters forced from one successful elimination. -/
private structure Metrics where
  sourceNT : Nat
  sourceUnary : Nat
  paths : Nat
  steps : Nat
  visits : Nat
  outputBinary : Nat
  outputLexical : Nat
  checksum : UInt64

/-- Construct an interner whose reverse table has exactly `count` valid identifiers. -/
private def interner (count : Nat) : Interner :=
  { names := Array.ofFn (n := count) fun index ↦ s!"symbol-{index.val}" }

/-- Construct one unary node around an already-built child. -/
@[inline] private def unaryNode (category : Nat) (child : Tree) : Tree :=
  .node (UInt32.ofNat category) child #[]

/-- Map exact induction counts to fixed-width native benchmark weights. -/
private def nativeWeights (grammar : TreebankGrammar Count) : TreebankGrammar UInt64 :=
  grammar.mapWeights fun count ↦ UInt64.ofNat count.toNat

/-- Induce a wide lexical grammar with one nonterminal and no unary productions. -/
private def baselineGrammar (lexicalRules : Nat) :
    Except InduceError (TreebankGrammar UInt64) :=
  let symbols := lexicalRules + 1
  let trees := Array.ofFn (n := lexicalRules) fun index ↦
    Tree.node 0 (.leaf (UInt32.ofNat (index.val + 1))) #[]
  (Grammar.induce (interner symbols) trees).map nativeWeights

/-- Build a chain of `nonterminals` nodes ending in one lexical base rule. -/
private def chainTree (nonterminals : Nat) : Tree := Id.run do
  let sink := nonterminals - 1
  let mut tree := unaryNode sink (.leaf (UInt32.ofNat nonterminals))
  for offset in [0:sink] do
    tree := unaryNode (sink - 1 - offset) tree
  return tree

/-- Induce the long-chain arena stress fixture through the public treebank API. -/
private def chainGrammar (nonterminals : Nat) :
    Except InduceError (TreebankGrammar UInt64) :=
  (Grammar.induce (interner (nonterminals + 1)) #[chainTree nonterminals]).map nativeWeights

/-- Select the node at one binary layer for a deterministic root-to-sink pattern. -/
@[inline] private def layerNode (layer pattern : Nat) : Nat :=
  1 + 2 * layer + (pattern / (2 ^ layer)) % 2

/-- Build one root-to-sink path through a width-two layered diamond. -/
private def diamondTree (layers pattern : Nat) : Tree := Id.run do
  let sink := 1 + 2 * layers
  let word := sink + 1
  let mut tree := unaryNode sink (.leaf (UInt32.ofNat word))
  for offset in [0:layers] do
    let layer := layers - 1 - offset
    tree := unaryNode (layerNode layer pattern) tree
  return unaryNode 0 tree

/--
Induce every binary choice through a bounded width-two layered diamond.

Enumerating all patterns makes both root edges, every complete bipartite inter-layer edge, and
both sink edges observable while induction aggregates repeated occurrences by source position.
-/
private def diamondGrammar (layers : Nat) :
    Except InduceError (TreebankGrammar UInt64) :=
  let patterns := 2 ^ layers
  let trees := Array.ofFn (n := patterns) fun pattern ↦ diamondTree layers pattern.val
  (Grammar.induce (interner (2 * layers + 3)) trees).map nativeWeights

/-- Mix one observable word into a deterministic fixed-width checksum. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let value := value + (0x9E3779B97F4A7C15 : UInt64) + (state <<< 6) + (state >>> 2)
  (state ^^^ value) * (0xD6E8FEB86659FD93 : UInt64)

/-- Encode an optional arena ordinal without colliding with `none`. -/
@[inline] private def optionOrdinal : Option Nat → UInt64
  | none => 0
  | some ordinal => UInt64.ofNat ordinal + 1

/-- Force the complete successful result graph into one observable checksum. -/
@[noinline] private def resultChecksum (result : UnaryFreeGrammar UInt64) : UInt64 := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat result.source.nNT)
  checksum := mix checksum (UInt64.ofNat result.source.unary.size)
  for path in result.paths do
    checksum := mix checksum (UInt64.ofNat path.source.toNat)
    checksum := mix checksum (UInt64.ofNat path.target.toNat)
    checksum := mix checksum (optionOrdinal path.lastStep)
    checksum := mix checksum (UInt64.ofNat path.length)
    checksum := mix checksum path.weight
  for step in result.pathSteps do
    checksum := mix checksum (UInt64.ofNat step.sourceRule)
    checksum := mix checksum (optionOrdinal step.previous)
  for rule in result.grammar.bin do
    checksum := mix checksum (UInt64.ofNat rule.lhs.toNat)
    checksum := mix checksum (UInt64.ofNat rule.r1.toNat)
    checksum := mix checksum (UInt64.ofNat rule.r2.toNat)
    checksum := mix checksum rule.w
  for provenance in result.binaryProvenance do
    checksum := mix checksum (UInt64.ofNat provenance.pathOrdinal)
    checksum := mix checksum (UInt64.ofNat provenance.sourceRule)
  for rule in result.grammar.lex do
    checksum := mix checksum (UInt64.ofNat rule.lhs.toNat)
    checksum := mix checksum (UInt64.ofNat rule.tok.toNat)
    checksum := mix checksum rule.w
  for provenance in result.lexicalProvenance do
    checksum := mix checksum (UInt64.ofNat provenance.pathOrdinal)
    checksum := mix checksum (UInt64.ofNat provenance.sourceRule)
  return checksum

/-- Run and fully force one successful elimination. -/
@[noinline] private def eliminateMetrics (config : UnaryElimConfig)
    (grammar : TreebankGrammar UInt64) : Except UnaryElimError Metrics := do
  let result ← grammar.eliminateAcyclicUnaryWith config
  let visits := result.paths.foldl (fun total path ↦ total + path.length) 0
  return {
    sourceNT := grammar.nNT
    sourceUnary := grammar.unary.size
    paths := result.paths.size
    steps := result.pathSteps.size
    visits
    outputBinary := result.grammar.bin.size
    outputLexical := result.grammar.lex.size
    checksum := resultChecksum result
  }

/-- Render all requested counters and two useful structural throughput rates. -/
private def reportSuccess (name : String) (metrics : Metrics) (nanos : Nat)
    (checksum : UInt64) : IO Unit := do
  let seconds := Float.ofNat (max nanos 1) / 1000000000.0
  let milliseconds := Float.ofNat nanos / 1000000.0
  let pathsPerSecond := Float.ofNat metrics.paths / seconds
  let visitsPerSecond := Float.ofNat metrics.visits / seconds
  IO.println <| s!"{name}: sourceNT={metrics.sourceNT} sourceUnary={metrics.sourceUnary} " ++
    s!"paths={metrics.paths} steps={metrics.steps} visits={metrics.visits} " ++
    s!"outBin={metrics.outputBinary} outLex={metrics.outputLexical} " ++
    s!"elapsed={milliseconds} ms paths/s={pathsPerSecond} " ++
    s!"visits/s={visitsPerSecond} chk={checksum}"

/-- Warm up, time repeated eliminations, and reject any checksum instability. -/
private def benchSuccess (name : String) (repetitions : Nat) (config : UnaryElimConfig)
    (grammar : TreebankGrammar UInt64) : IO Metrics := do
  let warm ← IO.lazyPure fun _ ↦ eliminateMetrics config grammar
  let expected ←
    match warm with
    | .ok metrics => pure metrics
    | .error error => throw <| IO.userError s!"{name} warm-up failed: {repr error}"
  let start ← IO.monoNanosNow
  let mut checksum := expected.checksum
  for _ in [0:repetitions] do
    let current ← IO.lazyPure fun _ ↦ eliminateMetrics config grammar
    match current with
    | .error error => throw <| IO.userError s!"{name} timed run failed: {repr error}"
    | .ok metrics =>
      if metrics.checksum != expected.checksum then
        throw <| IO.userError s!"{name} checksum changed"
      checksum := checksum + metrics.checksum
  let stop ← IO.monoNanosNow
  let nanos := (stop - start) / repetitions
  reportSuccess name expected nanos checksum
  return expected

/-- Reduce the expected budget failure to a deterministic checksum word. -/
@[inline] private def failureChecksum : UnaryElimError → UInt64
  | .pathBudget required limit =>
    mix (UInt64.ofNat required) (UInt64.ofNat limit)
  | _ => 0

/-- Warm up and time the deliberate layered-diamond path-cap rejection. -/
private def benchPathFailure (repetitions : Nat) (cap : Nat)
    (grammar : TreebankGrammar UInt64) : IO Unit := do
  let config := { UnaryElimConfig.default with maxPaths := cap }
  let warm ← IO.lazyPure fun _ ↦ eliminateMetrics config grammar
  let expected ←
    match warm with
    | .error error@(.pathBudget _ _) => pure error
    | .error error => throw <| IO.userError s!"unexpected cap failure: {repr error}"
    | .ok _ => throw <| IO.userError "layered diamond unexpectedly fit the path cap"
  let start ← IO.monoNanosNow
  let mut checksum := failureChecksum expected
  for _ in [0:repetitions] do
    let current ← IO.lazyPure fun _ ↦ eliminateMetrics config grammar
    match current with
    | .error error =>
      if error != expected then
        throw <| IO.userError "layered-diamond cap error changed"
      checksum := checksum + failureChecksum error
    | .ok _ => throw <| IO.userError "layered diamond unexpectedly succeeded"
  let stop ← IO.monoNanosNow
  let nanos := (stop - start) / repetitions
  let milliseconds := Float.ofNat nanos / 1000000.0
  let attemptsPerSecond := 1000000000.0 / Float.ofNat (max nanos 1)
  IO.println <| s!"layered diamond cap: sourceNT={grammar.nNT} " ++
    s!"sourceUnary={grammar.unary.size} cap={cap} error={repr expected} " ++
    s!"elapsed={milliseconds} ms attempts/s={attemptsPerSecond} chk={checksum}"

/-- Resolve a benchmark fixture or raise a readable induction failure. -/
private def requireGrammar (name : String)
    (grammar : Except InduceError (TreebankGrammar UInt64)) : IO (TreebankGrammar UInt64) :=
  match grammar with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{name} induction failed: {repr error}"

/-- Run the quick baseline, arena stress, layered success, and layered cap-failure lanes. -/
def main : IO Unit := do
  let baseline ← requireGrammar "no-unary baseline" (baselineGrammar 2048)
  discard <| benchSuccess "no-unary baseline" 5 .default baseline

  let chain ← requireGrammar "long chain" (chainGrammar 192)
  discard <| benchSuccess "long chain with sink base" 3 .default chain

  let diamond ← requireGrammar "layered diamond" (diamondGrammar 10)
  let diamondMetrics ← benchSuccess "layered diamond" 3 .default diamond
  let cap := max diamond.nNT (diamondMetrics.paths / 2)
  benchPathFailure 3 cap diamond

end UnaryBenchmark

def main : IO Unit := UnaryBenchmark.main
