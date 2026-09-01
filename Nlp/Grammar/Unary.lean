import Nlp.Grammar.Induce

/-!
# Bounded acyclic unary elimination

This module removes unary productions from a validated acyclic treebank grammar. Parallel unary
rules remain distinct positional edges, so every emitted CNF alternative has an exact unary path
and an exact binary or lexical source-rule ordinal.

Paths list unary source ordinals from the outermost rule to the innermost rule. Nonempty path
weights are left-associated in that same order, and the base-rule weight is multiplied last. Thus
two unary weights `u0`, `u1` and a base weight `b` produce `(u0 * u1) * b`. Identity paths emit
`b` itself, without evaluating `1 * b`. No associativity or identity law is required by the
executable transform; relating this bracketing to another derivation convention requires an
associativity law.

Validation and cycle detection cover the complete declared nonterminal graph, including nodes
unreachable from the start. Constructor-protected origin indexes are retained, not rebuilt or
independently revalidated here. For probabilistic grammars, use induction, then MLE, then unary
elimination so each emitted alternative receives the product of already-normalized source rules.

Only finite acyclic expansion is implemented here. Epsilon elimination, strongly connected
components, and star closure are deliberately outside this API.
-/

namespace Nlp

/-- Explicit limits for the data created by acyclic unary elimination. -/
structure UnaryElimConfig where
  /-- Maximum declared nonterminals accepted before adjacency allocation. -/
  maxNonterminals : Nat := 65_536
  /-- Maximum source unary rules accepted before adjacency allocation. -/
  maxUnaryRules : Nat := 262_144
  /-- Maximum number of identity and nonempty positional unary paths. -/
  maxPaths : Nat := 1_048_576
  /-- Maximum sum of path lengths visited while constructing all positional paths. -/
  maxPathRuleVisits : Nat := 8_388_608
  /-- Maximum number of unary edges in any one positional path. -/
  maxPathLength : Nat := 256
  /-- Maximum number of emitted binary alternatives, including duplicates. -/
  maxOutputBinaryRules : Nat := 1_048_576
  /-- Maximum number of emitted lexical alternatives, including duplicates. -/
  maxOutputLexicalRules : Nat := 1_048_576
  /-- Maximum combined number of emitted binary and lexical alternatives. -/
  maxOutputRules : Nat := 1_572_864
deriving Repr, DecidableEq, Inhabited

/-- Production limits suitable for ordinary in-memory parsing. -/
def UnaryElimConfig.default : UnaryElimConfig := {}

/-- One reverse-linked step in the shared-prefix arena for positional unary paths. -/
structure UnaryPathStep where
  /-- Exact ordinal of this edge in the source unary-rule array. -/
  sourceRule : Nat
  /-- Arena ordinal of the previous outer edge, or `none` at the source. -/
  previous : Option Nat
deriving Repr, DecidableEq, Inhabited

/-- One identity or nonempty positional path through the shared step arena. -/
structure UnaryPath (K : Type) where
  /-- Outermost nonterminal at which the expanded alternative is emitted. -/
  source : NT
  /-- Innermost nonterminal whose binary or lexical rule closes the path. -/
  target : NT
  /-- Arena ordinal of the innermost unary edge, or `none` for identity. -/
  lastStep : Option Nat
  /-- Exact number of unary edges in this path. -/
  length : Nat
  /-- `1` for identity paths; otherwise the left fold of unary weights in source order. -/
  weight : K
deriving Repr, DecidableEq

namespace UnaryPath

/-- Close a path with a base weight, preserving identity-path weights without multiplication. -/
@[inline] def closeWeight [Mul K] (path : UnaryPath K) (base : K) : K :=
  if path.length == 0 then base else path.weight * base

end UnaryPath

/-- Provenance for one emitted binary alternative. -/
structure UnaryBinaryProvenance where
  /-- Exact index into `UnaryFreeGrammar.paths`. -/
  pathOrdinal : Nat
  /-- Exact index into `UnaryFreeGrammar.source.binary`. -/
  sourceRule : Nat
deriving Repr, DecidableEq, Inhabited

/-- Provenance for one emitted lexical alternative. -/
structure UnaryLexicalProvenance where
  /-- Exact index into `UnaryFreeGrammar.paths`. -/
  pathOrdinal : Nat
  /-- Exact index into `UnaryFreeGrammar.source.lexical`. -/
  sourceRule : Nat
deriving Repr, DecidableEq, Inhabited

/-- A typed validation, cycle, representation, or expansion-budget failure. -/
inductive UnaryElimError where
  /-- The declared nonterminal space cannot be represented by `NT`. -/
  | nonterminalCapacity (count : Nat)
  /-- The declared nonterminal count exceeds the configured policy limit. -/
  | nonterminalBudget (required limit : Nat)
  /-- The source unary-rule count exceeds the configured policy limit. -/
  | unaryRuleBudget (required limit : Nat)
  /-- The source start identifier is outside the declared nonterminal space. -/
  | invalidStart (start : NT) (nNT : Nat)
  /-- A binary source rule contains an out-of-range nonterminal identifier. -/
  | invalidBinaryRule (source : Nat) (lhs left right : NT) (nNT : Nat)
  /-- A unary source rule contains an out-of-range nonterminal identifier. -/
  | invalidUnaryRule (source : Nat) (lhs rhs : NT) (nNT : Nat)
  /-- A lexical source rule contains an out-of-range left-hand side. -/
  | invalidLexicalRule (source : Nat) (lhs : NT) (nNT : Nat)
  /-- A deterministic closed nonterminal walk and its aligned unary source-rule ordinals. -/
  | cycle (nonterminals : Array NT) (sourceRules : Array Nat)
  /-- Adding positional paths would exceed the configured limit. -/
  | pathBudget (required limit : Nat)
  /-- Visiting the represented path lengths would exceed the configured aggregate limit. -/
  | pathRuleVisitBudget (required limit : Nat)
  /-- Extending a path would exceed the configured per-path length limit. -/
  | pathLengthBudget (required limit : Nat)
  /-- Emitting more binary alternatives would exceed the configured limit. -/
  | outputBinaryBudget (required limit : Nat)
  /-- Emitting more lexical alternatives would exceed the configured limit. -/
  | outputLexicalBudget (required limit : Nat)
  /-- Emitting the combined alternatives would exceed the configured limit. -/
  | outputRuleBudget (required limit : Nat)
  /-- The expanded binary-rule array cannot use the parser's `UInt32` rule ordinals. -/
  | outputBinaryCapacity (count : Nat)
  /-- The expanded lexical-rule array cannot use the parser's `UInt32` rule ordinals. -/
  | outputLexicalCapacity (count : Nat)
deriving Repr, DecidableEq, Inhabited

/--
A validated unary-free grammar with source-locked, position-preserving provenance.

The constructor is private. `binaryProvenance` and `lexicalProvenance` are built in the same loops
as their respective rule arrays and are aligned one-for-one with them.
-/
structure UnaryFreeGrammar (K : Type) where
  private mk ::
  /-- The exact source grammar whose rule ordinals occur in the provenance arrays. -/
  source : TreebankGrammar K
  /-- The expanded unary-free CNF grammar. -/
  grammar : CNF K
  /-- All identity and positional unary paths in deterministic ordinal order. -/
  paths : Array (UnaryPath K)
  /-- Reverse-linked arena with one final step per nonidentity path and shared prefixes. -/
  pathSteps : Array UnaryPathStep
  /-- Provenance aligned one-for-one with `grammar.bin`. -/
  binaryProvenance : Array UnaryBinaryProvenance
  /-- Provenance aligned one-for-one with `grammar.lex`. -/
  lexicalProvenance : Array UnaryLexicalProvenance

namespace UnaryFreeGrammar

/-- Materialize one path's checked outermost-to-innermost unary source ordinals. -/
def pathSourceRules? (result : UnaryFreeGrammar K) (pathOrdinal : Nat) :
    Option (Array Nat) := do
  let path ← result.paths[pathOrdinal]?
  let mut current := path.lastStep
  let mut reversedRules := Array.emptyWithCapacity path.length
  for _ in [0:path.length] do
    let stepOrdinal ← current
    let step ← result.pathSteps[stepOrdinal]?
    let _ ← result.source.unary[step.sourceRule]?
    reversedRules := reversedRules.push step.sourceRule
    current := step.previous
  if current.isNone then some reversedRules.reverse else none

end UnaryFreeGrammar

private structure UnaryEdge (K : Type) where
  sourceRule : Nat
  lhs : NT
  rhs : NT
  weight : K

private structure SourceBinary (K : Type) where
  sourceRule : Nat
  rule : BinRule K

private structure SourceLexical (K : Type) where
  sourceRule : Nat
  rule : LexRule K

private structure ValidatedSource (K : Type) where
  outgoing : Array (Array (UnaryEdge K))
  incoming : Array (Array (UnaryEdge K))
  indegree : Array Nat
  binaryByLhs : Array (Array (SourceBinary K))
  lexicalByLhs : Array (Array (SourceLexical K))

private structure Topology where
  processed : Nat
  residualIndegree : Array Nat

private structure BuiltPaths (K : Type) where
  paths : Array (UnaryPath K)
  steps : Array UnaryPathStep

private structure PathBuildState (K : Type) where
  pathCount : Nat
  ruleVisits : Nat
  steps : Array UnaryPathStep
  paths : Array (UnaryPath K)
  head : Nat

private structure OutputCounts where
  binary : Nat
  lexical : Nat

private structure ExpandedRules (K : Type) where
  binary : Array (BinRule K)
  lexical : Array (LexRule K)
  binaryProvenance : Array UnaryBinaryProvenance
  lexicalProvenance : Array UnaryLexicalProvenance

namespace TreebankGrammar

@[inline] private def fitsNT (nNT : Nat) (value : NT) : Bool :=
  value.toNat < nNT

private def validateSource (grammar : TreebankGrammar K) : Except UnaryElimError Unit := do
  if UInt32.size < grammar.nNT then
    throw (.nonterminalCapacity grammar.nNT)
  unless fitsNT grammar.nNT grammar.start do
    throw (.invalidStart grammar.start grammar.nNT)
  let mut binarySource := 0
  for rule in grammar.binary do
    unless fitsNT grammar.nNT rule.lhs && fitsNT grammar.nNT rule.r1 &&
        fitsNT grammar.nNT rule.r2 do
      throw (.invalidBinaryRule binarySource rule.lhs rule.r1 rule.r2 grammar.nNT)
    binarySource := binarySource + 1
  let mut unarySource := 0
  for rule in grammar.unary do
    unless fitsNT grammar.nNT rule.lhs && fitsNT grammar.nNT rule.rhs do
      throw (.invalidUnaryRule unarySource rule.lhs rule.rhs grammar.nNT)
    unarySource := unarySource + 1
  let mut lexicalSource := 0
  for rule in grammar.lexical do
    unless fitsNT grammar.nNT rule.lhs do
      throw (.invalidLexicalRule lexicalSource rule.lhs grammar.nNT)
    lexicalSource := lexicalSource + 1

private def preflightLowerBounds (config : UnaryElimConfig)
    (grammar : TreebankGrammar K) : Except UnaryElimError Unit := do
  if config.maxNonterminals < grammar.nNT then
    throw (.nonterminalBudget grammar.nNT config.maxNonterminals)
  if config.maxUnaryRules < grammar.unary.size then
    throw (.unaryRuleBudget grammar.unary.size config.maxUnaryRules)
  if config.maxPaths < grammar.nNT then
    throw (.pathBudget grammar.nNT config.maxPaths)
  if config.maxPathRuleVisits < grammar.unary.size then
    throw (.pathRuleVisitBudget grammar.unary.size config.maxPathRuleVisits)
  if config.maxOutputBinaryRules < grammar.binary.size then
    throw (.outputBinaryBudget grammar.binary.size config.maxOutputBinaryRules)
  if UInt32.size < grammar.binary.size then
    throw (.outputBinaryCapacity grammar.binary.size)
  if config.maxOutputLexicalRules < grammar.lexical.size then
    throw (.outputLexicalBudget grammar.lexical.size config.maxOutputLexicalRules)
  if UInt32.size < grammar.lexical.size then
    throw (.outputLexicalCapacity grammar.lexical.size)
  unless grammar.binary.size ≤ config.maxOutputRules &&
      grammar.lexical.size ≤ config.maxOutputRules - grammar.binary.size do
    throw (.outputRuleBudget (grammar.binary.size + grammar.lexical.size)
      config.maxOutputRules)

private def indexSource (grammar : TreebankGrammar K) : ValidatedSource K := Id.run do
  let mut outgoing := Array.replicate grammar.nNT #[]
  let mut incoming := Array.replicate grammar.nNT #[]
  let mut indegree := Array.replicate grammar.nNT 0
  let mut binaryByLhs := Array.replicate grammar.nNT #[]
  let mut lexicalByLhs := Array.replicate grammar.nNT #[]
  let mut binarySource := 0
  for rule in grammar.binary do
    let entry : SourceBinary K := ⟨binarySource, rule⟩
    binaryByLhs := binaryByLhs.modify rule.lhs.toNat fun bucket ↦ bucket.push entry
    binarySource := binarySource + 1
  let mut unarySource := 0
  for rule in grammar.unary do
    let edge : UnaryEdge K := ⟨unarySource, rule.lhs, rule.rhs, rule.w⟩
    outgoing := outgoing.modify rule.lhs.toNat fun bucket ↦ bucket.push edge
    incoming := incoming.modify rule.rhs.toNat fun bucket ↦ bucket.push edge
    indegree := indegree.modify rule.rhs.toNat fun degree ↦ degree + 1
    unarySource := unarySource + 1
  let mut lexicalSource := 0
  for rule in grammar.lexical do
    let entry : SourceLexical K := ⟨lexicalSource, rule⟩
    lexicalByLhs := lexicalByLhs.modify rule.lhs.toNat fun bucket ↦ bucket.push entry
    lexicalSource := lexicalSource + 1
  return ⟨outgoing, incoming, indegree, binaryByLhs, lexicalByLhs⟩

private def kahnOrder (validated : ValidatedSource K) : Topology := Id.run do
  let mut indegree := validated.indegree
  let mut queue : Array NT := #[]
  for identifier in [0:indegree.size] do
    if indegree[identifier]?.getD 0 == 0 then
      queue := queue.push (UInt32.ofNat identifier)
  let mut head := 0
  let mut processed := 0
  for _ in [0:indegree.size] do
    if head < queue.size then
      match queue[head]? with
      | none => pure ()
      | some node =>
        head := head + 1
        processed := processed + 1
        match validated.outgoing[node.toNat]? with
        | none => pure ()
        | some edges =>
          for edge in edges do
            let degree := indegree[edge.rhs.toNat]?.getD 0
            let next := degree - 1
            indegree := indegree.set! edge.rhs.toNat next
            if next == 0 then
              queue := queue.push edge.rhs
  return ⟨processed, indegree⟩

private def suffix (items : Array α) (first : Nat) : Array α := Id.run do
  let mut output := #[]
  let mut index := 0
  for item in items do
    if first ≤ index then
      output := output.push item
    index := index + 1
  return output

private def firstResidualIncoming? (validated : ValidatedSource K)
    (indegree : Array Nat) (node : NT) : Option (UnaryEdge K) := Id.run do
  let mut result := none
  match validated.incoming[node.toNat]? with
  | none => pure ()
  | some edges =>
    for edge in edges do
      if result.isNone && 0 < indegree[edge.lhs.toNat]?.getD 0 then
        result := some edge
  return result

private def deterministicCycle (validated : ValidatedSource K)
    (indegree : Array Nat) : Array NT × Array Nat := Id.run do
  let mut start := UInt32.ofNat 0
  let mut hasStart := false
  for identifier in [0:indegree.size] do
    if !hasStart && 0 < indegree[identifier]?.getD 0 then
      start := UInt32.ofNat identifier
      hasStart := true
  let mut current := start
  let mut backwardNodes : Array NT := #[]
  let mut backwardRules : Array Nat := #[]
  let unseen := indegree.size
  let mut seenAt := Array.replicate indegree.size unseen
  let mut result : Option (Array NT × Array Nat) := none
  for _ in [0:indegree.size + 1] do
    if result.isNone then
      let first := seenAt[current.toNat]?.getD unseen
      if first < unseen then
        let nodes := (suffix backwardNodes first).push current
        let rules := suffix backwardRules first
        result := some (nodes.reverse, rules.reverse)
      else
        seenAt := seenAt.set! current.toNat backwardNodes.size
        backwardNodes := backwardNodes.push current
        match firstResidualIncoming? validated indegree current with
        | some edge =>
          backwardRules := backwardRules.push edge.sourceRule
          current := edge.lhs
        | none =>
          result := some (#[current], #[])
  return result.getD (#[start], #[])

@[inline] private def checkedAdd (current additional limit : Nat) : Option Nat :=
  if current ≤ limit && additional ≤ limit - current then
    some (current + additional)
  else
    none

private def expandSource [One K] [Mul K] (config : UnaryElimConfig)
    (validated : ValidatedSource K) :
    Nat → PathBuildState K → Except UnaryElimError (PathBuildState K)
  | 0, state =>
    if state.head < state.paths.size then
      .error (.pathBudget (state.pathCount + 1) config.maxPaths)
    else
      .ok state
  | fuel + 1, state => do
    let path ←
      match state.paths[state.head]? with
      | some path => pure path
      | none => return state
    let mut next := { state with head := state.head + 1 }
    match validated.outgoing[path.target.toNat]? with
    | none => pure ()
    | some edges =>
      for edge in edges do
        let nextPathCount ←
          match checkedAdd next.pathCount 1 config.maxPaths with
          | some count => pure count
          | none => throw (.pathBudget (next.pathCount + 1) config.maxPaths)
        let pathLength ←
          match checkedAdd path.length 1 config.maxPathLength with
          | some length => pure length
          | none => throw (.pathLengthBudget (path.length + 1) config.maxPathLength)
        let nextRuleVisits ←
          match checkedAdd next.ruleVisits pathLength config.maxPathRuleVisits with
          | some count => pure count
          | none =>
            throw (.pathRuleVisitBudget (next.ruleVisits + pathLength)
              config.maxPathRuleVisits)
        let weight := if path.length == 0 then edge.weight else path.weight * edge.weight
        let extended : UnaryPath K :=
          ⟨path.source, edge.rhs, some next.steps.size, pathLength, weight⟩
        next :=
          { next with
            pathCount := nextPathCount
            ruleVisits := nextRuleVisits
            steps := next.steps.push ⟨edge.sourceRule, path.lastStep⟩
            paths := next.paths.push extended }
    expandSource config validated fuel next

private def buildPaths [One K] [Mul K] (config : UnaryElimConfig)
    (validated : ValidatedSource K) (topology : Topology) :
    Except UnaryElimError (BuiltPaths K) := do
  let mut state : PathBuildState K :=
    ⟨0, 0, #[], Array.emptyWithCapacity topology.processed, 0⟩
  for identifier in [0:topology.processed] do
    let nextPathCount ←
      match checkedAdd state.pathCount 1 config.maxPaths with
      | some count => pure count
      | none => throw (.pathBudget (state.pathCount + 1) config.maxPaths)
    let source := UInt32.ofNat identifier
    let identity : UnaryPath K := ⟨source, source, none, 0, 1⟩
    state :=
      { state with
        pathCount := nextPathCount
        paths := state.paths.push identity
        head := state.paths.size }
    state ← expandSource config validated config.maxPaths state
  return ⟨state.paths, state.steps⟩

private def countOutputs (config : UnaryElimConfig) (validated : ValidatedSource K)
    (paths : Array (UnaryPath K)) : Except UnaryElimError OutputCounts := do
  let mut binary := 0
  let mut lexical := 0
  for path in paths do
    let binaryAdditional := validated.binaryByLhs[path.target.toNat]?.map Array.size |>.getD 0
    let nextBinary ←
      match checkedAdd binary binaryAdditional config.maxOutputBinaryRules with
      | some count => pure count
      | none =>
        throw (.outputBinaryBudget (binary + binaryAdditional)
          config.maxOutputBinaryRules)
    let _ ←
      match checkedAdd binary binaryAdditional UInt32.size with
      | some count => pure count
      | none => throw (.outputBinaryCapacity (binary + binaryAdditional))
    binary := nextBinary
    let lexicalAdditional :=
      validated.lexicalByLhs[path.target.toNat]?.map Array.size |>.getD 0
    let nextLexical ←
      match checkedAdd lexical lexicalAdditional config.maxOutputLexicalRules with
      | some count => pure count
      | none =>
        throw (.outputLexicalBudget (lexical + lexicalAdditional)
          config.maxOutputLexicalRules)
    let _ ←
      match checkedAdd lexical lexicalAdditional UInt32.size with
      | some count => pure count
      | none => throw (.outputLexicalCapacity (lexical + lexicalAdditional))
    lexical := nextLexical
  unless binary ≤ config.maxOutputRules && lexical ≤ config.maxOutputRules - binary do
    throw (.outputRuleBudget (binary + lexical) config.maxOutputRules)
  return ⟨binary, lexical⟩

private def emitRules [Mul K] (validated : ValidatedSource K)
    (paths : Array (UnaryPath K)) (counts : OutputCounts) : ExpandedRules K := Id.run do
  let mut binary := Array.emptyWithCapacity counts.binary
  let mut lexical := Array.emptyWithCapacity counts.lexical
  let mut binaryProvenance := Array.emptyWithCapacity counts.binary
  let mut lexicalProvenance := Array.emptyWithCapacity counts.lexical
  let mut pathOrdinal := 0
  for path in paths do
    match validated.binaryByLhs[path.target.toNat]? with
    | none => pure ()
    | some sources =>
      for source in sources do
        let rule : BinRule K :=
          ⟨path.source, source.rule.r1, source.rule.r2,
            path.closeWeight source.rule.w⟩
        binary := binary.push rule
        binaryProvenance := binaryProvenance.push ⟨pathOrdinal, source.sourceRule⟩
    match validated.lexicalByLhs[path.target.toNat]? with
    | none => pure ()
    | some sources =>
      for source in sources do
        let rule : LexRule K :=
          ⟨path.source, source.rule.tok, path.closeWeight source.rule.w⟩
        lexical := lexical.push rule
        lexicalProvenance := lexicalProvenance.push ⟨pathOrdinal, source.sourceRule⟩
    pathOrdinal := pathOrdinal + 1
  return ⟨binary, lexical, binaryProvenance, lexicalProvenance⟩

private def assembleResult [Mul K] (source : TreebankGrammar K)
    (validated : ValidatedSource K) (built : BuiltPaths K)
    (counts : OutputCounts) : UnaryFreeGrammar K :=
  let expanded := emitRules validated built.paths counts
  let grammar : CNF K := ⟨expanded.binary, expanded.lexical, source.start, source.nNT⟩
  .mk source grammar built.paths built.steps expanded.binaryProvenance
    expanded.lexicalProvenance

/--
Validate and eliminate every positional unary path under explicit expansion limits.

Validation, lower-bound preflight, and deterministic cycle rejection finish before path expansion.
Paths are ordered by ascending source nonterminal. Each source has its identity first, followed by
breadth-first extensions in source unary-rule order. Emitted alternatives are path-major and
base-source-major, and duplicates are never aggregated.
-/
def eliminateAcyclicUnaryWith [One K] [Mul K] (config : UnaryElimConfig)
    (grammar : TreebankGrammar K) : Except UnaryElimError (UnaryFreeGrammar K) := do
  validateSource grammar
  preflightLowerBounds config grammar
  let validated := indexSource grammar
  let topology := kahnOrder validated
  unless topology.processed == grammar.nNT do
    let witness := deterministicCycle validated topology.residualIndegree
    throw (.cycle witness.1 witness.2)
  let built ← buildPaths config validated topology
  let counts ← countOutputs config validated built.paths
  return assembleResult grammar validated built counts

private theorem eliminateAcyclicUnaryWith_projections [One K] [Mul K]
    (config : UnaryElimConfig) (grammar : TreebankGrammar K)
    (result : UnaryFreeGrammar K)
    (success : eliminateAcyclicUnaryWith config grammar = .ok result) :
    result.source = grammar ∧ result.grammar.start = grammar.start ∧
      result.grammar.nNT = grammar.nNT := by
  unfold eliminateAcyclicUnaryWith at success
  cases validation : validateSource grammar with
  | error error =>
    simp [Bind.bind, Except.bind, validation] at success
  | ok value =>
    cases value
    cases preflight : preflightLowerBounds config grammar with
    | error error =>
      simp [Bind.bind, Except.bind, validation, preflight] at success
    | ok value =>
      cases value
      let validated := indexSource grammar
      let topology := kahnOrder validated
      by_cases acyclic : topology.processed = grammar.nNT
      · cases paths : buildPaths config validated topology with
        | error error =>
          simp [Bind.bind, Except.bind, validation, preflight,
            validated, topology, acyclic, paths] at success
        | ok built =>
          cases counts : countOutputs config validated built.paths with
          | error error =>
            simp [Bind.bind, Except.bind, validation, preflight,
              validated, topology, acyclic, paths, counts] at success
          | ok outputCounts =>
            have equality : assembleResult grammar validated built outputCounts = result := by
              simpa [Bind.bind, Pure.pure, Except.instMonad, Except.bind, Except.pure,
                validation, preflight, validated, topology, acyclic, paths, counts]
                using success
            rw [← equality]
            simp [assembleResult]
      · simp [Bind.bind, Except.bind, validation, preflight,
          validated, topology, acyclic] at success

/-- Successful elimination retains the exact source grammar used for provenance. -/
theorem eliminateAcyclicUnaryWith_source [One K] [Mul K]
    (config : UnaryElimConfig) (grammar : TreebankGrammar K)
    (result : UnaryFreeGrammar K)
    (success : eliminateAcyclicUnaryWith config grammar = .ok result) :
    result.source = grammar :=
  (eliminateAcyclicUnaryWith_projections config grammar result success).1

/-- Successful elimination preserves the source start nonterminal exactly. -/
theorem eliminateAcyclicUnaryWith_start [One K] [Mul K]
    (config : UnaryElimConfig) (grammar : TreebankGrammar K)
    (result : UnaryFreeGrammar K)
    (success : eliminateAcyclicUnaryWith config grammar = .ok result) :
    result.grammar.start = grammar.start :=
  (eliminateAcyclicUnaryWith_projections config grammar result success).2.1

/-- Successful elimination preserves the declared nonterminal count exactly. -/
theorem eliminateAcyclicUnaryWith_nNT [One K] [Mul K]
    (config : UnaryElimConfig) (grammar : TreebankGrammar K)
    (result : UnaryFreeGrammar K)
    (success : eliminateAcyclicUnaryWith config grammar = .ok result) :
    result.grammar.nNT = grammar.nNT :=
  (eliminateAcyclicUnaryWith_projections config grammar result success).2.2

/-- Eliminate acyclic unary rules using `UnaryElimConfig.default`. -/
@[inline] def eliminateAcyclicUnary [One K] [Mul K] (grammar : TreebankGrammar K) :
    Except UnaryElimError (UnaryFreeGrammar K) :=
  eliminateAcyclicUnaryWith UnaryElimConfig.default grammar

end TreebankGrammar
end Nlp
