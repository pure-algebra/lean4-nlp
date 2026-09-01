import Std.Data.HashMap
import Std.Data.HashSet
import Nlp.Core.Data.Interner
import Nlp.IO.Ptb

/-!
# EVALB-compatible constituency evaluation

This module implements the scoring semantics of the vendored 2006 EVALB release. Parameters
remain a small functional value; `CompiledParams` prepares hash tables once for corpus scoring.
Sentence extraction is linear in tree size and bracket matching is expected linear time for the
usual disjoint equivalence pairs. Crossing brackets retain EVALB's test-bracket-oriented
definition. The text adapter rejects label-less and zero-child nodes that `Tree` cannot represent,
rather than silently changing their scores.
-/

namespace Nlp.Eval.Evalb

/-- Human-readable EVALB parameters. -/
structure Params where
  labeled : Bool := true
  deleteLabel : Array String := #["TOP", "-NONE-", ",", ":", "``", "''", "."]
  deleteLabelForLength : Array String := #["-NONE-"]
  quoteLabel : Array String := #[]
  eqLabel : Array (String × String) := #[("ADVP", "PRT")]
  eqWord : Array (String × String) := #[]
  cutoffLen : Nat := 40
  /-- Abort threshold retained for effectful streaming drivers; pure array scoring reports all. -/
  maxErrors : Nat := 10
deriving Repr, DecidableEq, BEq, Inhabited

namespace Params

/-- Empty parameter state used when reading a complete `.prm` file. -/
def empty : Params where
  deleteLabel := #[]
  deleteLabelForLength := #[]
  eqLabel := #[]

/-- The canonical Michael Collins parameterization. -/
def collins : Params := {}

end Params

/-- A labelled, half-open nonterminal span after EVALB normalization. -/
structure Bracket where
  label : String
  start : Nat
  stop : Nat
deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- A surviving terminal and its preterminal tag. -/
structure Terminal where
  tag : String
  word : String
deriving Repr, DecidableEq, BEq, Inhabited

/-- Typed parameter, tree, alignment, and corpus errors. -/
inductive Error where
  | malformedParameter (line : Nat) (value : String)
  | invalidNumber (line : Nat) (name value : String)
  | unknownCategory (id : Cat)
  | unknownWord (id : Word)
  | bareLeaf (word : Word)
  | invalidTreeShape (category : Cat)
  | emptyTest
  | lengthMismatch (gold test : Nat)
  | wordMismatch (position : Nat) (gold test : String)
  | sentenceCountMismatch (gold test : Nat)
  | unsupportedTextShape (line token : Nat) (why : String)
  | ptb (error : Nlp.IO.PtbError)
deriving Repr, DecidableEq, Inhabited

/-- Counts reported for one valid aligned sentence pair. -/
structure SentenceScore where
  len : Nat
  matched : Nat
  goldBrackets : Nat
  testBrackets : Nat
  crossing : Nat
  words : Nat
  correctTags : Nat
deriving Repr, DecidableEq, BEq, Inhabited

/-- EVALB's three sentence statuses, retaining a typed cause for errors. -/
inductive SentenceResult where
  | valid (score : SentenceScore)
  | skipped (len words : Nat)
  | error (len words : Nat) (cause : Error)
deriving Repr, DecidableEq, Inhabited

/-- Micro-aggregateable EVALB summary counts. -/
structure Summary where
  sentences : Nat := 0
  errors : Nat := 0
  skipped : Nat := 0
  valid : Nat := 0
  matched : Nat := 0
  goldBrackets : Nat := 0
  testBrackets : Nat := 0
  complete : Nat := 0
  crossing : Nat := 0
  noCrossing : Nat := 0
  atMostTwoCrossing : Nat := 0
  words : Nat := 0
  correctTags : Nat := 0
deriving Repr, DecidableEq, BEq, Inhabited

/-- Per-sentence outcomes plus the all-sentence and cutoff summaries. -/
structure CorpusScore where
  results : Array SentenceResult
  all : Summary
  cutoff : Summary
deriving Repr, DecidableEq, Inhabited

@[inline] private def ratio (numerator denominator : Nat) : Float :=
  if denominator == 0 then 0.0 else Float.ofNat numerator / Float.ofNat denominator

/-- Micro bracketing recall. -/
@[inline] def Summary.recall (summary : Summary) : Float :=
  ratio summary.matched summary.goldBrackets

/-- Micro bracketing precision. -/
@[inline] def Summary.precision (summary : Summary) : Float :=
  ratio summary.matched summary.testBrackets

/-- Micro bracketing F1 from aggregate counts. -/
@[inline] def Summary.f1 (summary : Summary) : Float :=
  ratio (2 * summary.matched) (summary.goldBrackets + summary.testBrackets)

/-- Fraction of valid sentences with a complete bracket match. -/
@[inline] def Summary.completeRate (summary : Summary) : Float :=
  ratio summary.complete summary.valid

/-- Mean number of crossing test brackets over valid sentences. -/
@[inline] def Summary.averageCrossing (summary : Summary) : Float :=
  ratio summary.crossing summary.valid

/-- Fraction of valid sentences with no crossing brackets. -/
@[inline] def Summary.noCrossingRate (summary : Summary) : Float :=
  ratio summary.noCrossing summary.valid

/-- Fraction of valid sentences with at most two crossing brackets. -/
@[inline] def Summary.atMostTwoCrossingRate (summary : Summary) : Float :=
  ratio summary.atMostTwoCrossing summary.valid

/-- Positional preterminal-tag accuracy over surviving words. -/
@[inline] def Summary.taggingAccuracy (summary : Summary) : Float :=
  ratio summary.correctTags summary.words

private def fields (line : String) : Array String := Id.run do
  let mut output : Array String := #[]
  let mut reversed : List Char := []
  for character in line.toList do
    if character.isWhitespace then
      unless reversed.isEmpty do
        output := output.push (String.ofList reversed.reverse)
        reversed := []
    else
      reversed := character :: reversed
  unless reversed.isEmpty do
    output := output.push (String.ofList reversed.reverse)
  return output

private def parseNat (line : Nat) (name value : String) : Except Error Nat :=
  match value.toNat? with
  | some result => .ok result
  | none => .error (.invalidNumber line name value)

private def parseLine (lineNumber : Nat) (params : Params) (line : String) :
    Except Error Params := do
  let tokens := (fields line).takeWhile fun token => !token.startsWith "##"
  match tokens[0]? with
  | none => pure params
  | some name =>
    if name.startsWith "#" then
      pure params
    else
      match name, tokens[1]?, tokens[2]?, tokens.size with
      | "DEBUG", some _, none, 2 => pure params
      | "MAX_ERROR", some value, none, 2 =>
          pure { params with maxErrors := ← parseNat lineNumber name value }
      | "CUTOFF_LEN", some value, none, 2 =>
          pure { params with cutoffLen := ← parseNat lineNumber name value }
      | "LABELED", some value, none, 2 =>
          let parsed ← parseNat lineNumber name value
          if parsed ≤ 1 then
            pure { params with labeled := parsed == 1 }
          else
            throw (.invalidNumber lineNumber name value)
      | "DELETE_LABEL", some value, none, 2 =>
          pure { params with deleteLabel := params.deleteLabel.push value }
      | "DELETE_LABEL_FOR_LENGTH", some value, none, 2 =>
          pure { params with
            deleteLabelForLength := params.deleteLabelForLength.push value }
      | "QUOTE_LABEL", some value, none, 2 =>
          pure { params with quoteLabel := params.quoteLabel.push value }
      | "EQ_LABEL", some left, some right, 3 =>
          pure { params with eqLabel := params.eqLabel.push (left, right) }
      | "EQ_WORD", some left, some right, 3 =>
          pure { params with eqWord := params.eqWord.push (left, right) }
      | _, _, _, _ => throw (.malformedParameter lineNumber line)

/-- Parse an upstream EVALB parameter file without performing IO. -/
def parseParams (input : String) : Except Error Params := do
  let mut params := Params.empty
  let mut lineNumber := 0
  for line in input.splitOn "\n" do
    lineNumber := lineNumber + 1
    params ← parseLine lineNumber params line
  pure params

private def hashSetOf (values : Array String) : Std.HashSet String := Id.run do
  let mut result : Std.HashSet String := {}
  for value in values do
    result := result.insert value
  return result

private def aliasMap (pairs : Array (String × String)) :
    Option (Std.HashMap String String) := Id.run do
  let mut aliases : Std.HashMap String String := {}
  for (left, right) in pairs do
    if left == right then
      pure ()
    else
      match aliases.get? left, aliases.get? right with
      | none, none =>
          aliases := aliases.insert left left
          aliases := aliases.insert right left
      | some leftClass, some rightClass =>
          unless leftClass == rightClass do return none
      | some _, none => return none
      | none, some _ => return none
  return some aliases

/-- Hash-indexed parameters prepared once per evaluation run. -/
structure CompiledParams where
  source : Params
  deleteLabel : Std.HashSet String
  bracketDeleteLabel : Std.HashSet String
  deleteLabelForLength : Std.HashSet String
  quoteLabel : Std.HashSet String
  labelAliases : Option (Std.HashMap String String)
  wordAliases : Option (Std.HashMap String String)

/-- Validate equivalence classes and compile all repeated membership checks. -/
def Params.compile (params : Params) : Except Error CompiledParams := do
  let labelAliases := aliasMap params.eqLabel
  let mut bracketDeleteLabel : Std.HashSet String := {}
  for label in params.deleteLabel do
    let key := labelAliases.map (fun aliases => aliases.getD label label) |>.getD label
    bracketDeleteLabel := bracketDeleteLabel.insert key
  pure {
    source := params
    deleteLabel := hashSetOf params.deleteLabel
    bracketDeleteLabel
    deleteLabelForLength := hashSetOf params.deleteLabelForLength
    quoteLabel := hashSetOf params.quoteLabel
    labelAliases
    wordAliases := aliasMap params.eqWord
  }

@[inline] private def labelKey (params : CompiledParams) (label : String) : String :=
  params.labelAliases.map (fun aliases => aliases.getD label label) |>.getD label

@[inline] private def wordKey (params : CompiledParams) (word : String) : String :=
  params.wordAliases.map (fun aliases => aliases.getD word word) |>.getD word

@[inline] private def pairEqual (pairs : Array (String × String))
    (left right : String) : Bool :=
  pairs.any fun pair =>
    (left == pair.1 && right == pair.2) || (left == pair.2 && right == pair.1)

@[inline] private def labelsEqual (params : CompiledParams) (left right : String) : Bool :=
  left == right || match params.labelAliases with
    | some _ => labelKey params left == labelKey params right
    | none => pairEqual params.source.eqLabel left right

@[inline] private def wordsEqual (params : CompiledParams) (left right : String) : Bool :=
  left == right || match params.wordAliases with
    | some _ => wordKey params left == wordKey params right
    | none => pairEqual params.source.eqWord left right

private def stripFunctionChars : List Char → List Char
  | [] => []
  | '-' :: _ => []
  | '=' :: _ => []
  | character :: rest => character :: stripFunctionChars rest

@[inline] private def bracketLabel (params : CompiledParams) (label : String) : String :=
  labelKey params (String.ofList (stripFunctionChars label.toList))

private structure RawBracket where
  label : String
  start : Nat
  stop : Nat
deriving Inhabited

private structure RawSentence where
  brackets : Array RawBracket := #[]
  terminals : Array Terminal := #[]
  len : Nat := 0

private def categoryName (interner : Interner) (category : Cat) : Except Error String :=
  match interner.name? category with
  | some value => .ok value
  | none => .error (.unknownCategory category)

private def wordName (interner : Interner) (word : Word) : Except Error String :=
  match interner.name? word with
  | some value => .ok value
  | none => .error (.unknownWord word)

private def treeExtractor (params : CompiledParams) (interner : Interner) (tree : Tree) :
    RawSentence → Except Error RawSentence :=
  tree.para
    (fun word _ => .error (.bareLeaf word))
    (fun category first rest state => do
      let label ← categoryName interner category
      match first.1, rest.isEmpty with
      | .leaf word, true =>
          let terminalWord ← wordName interner word
          let len :=
            if params.deleteLabelForLength.contains label then state.len else state.len + 1
          pure { state with
            terminals := state.terminals.push { tag := label, word := terminalWord }
            len }
      | .leaf _, false => throw (.invalidTreeShape category)
      | .node _ _ _, _ =>
          let start := state.terminals.size
          let bracketIndex := state.brackets.size
          let placeholder : RawBracket := { label, start, stop := start }
          let withBracket := { state with brackets := state.brackets.push placeholder }
          let afterFirst ← first.2 withBracket
          let afterChildren ← rest.foldl
            (fun result child => result >>= child.2)
            (.ok afterFirst)
          let bracket : RawBracket := { label, start, stop := afterChildren.terminals.size }
          pure { afterChildren with
            brackets := afterChildren.brackets.set! bracketIndex bracket })

@[inline] private def extractTree (params : CompiledParams) (interner : Interner)
    (tree : Tree) (state : RawSentence) : Except Error RawSentence :=
  treeExtractor params interner tree state

private def extractForest (params : CompiledParams) (interner : Interner)
    (forest : Array Tree) : Except Error RawSentence :=
  forest.attach.foldl
    (fun result ⟨tree, _⟩ => result >>= extractTree params interner tree)
    (.ok {})

private def initialKeep (params : CompiledParams) (sentence : RawSentence) : Array Bool :=
  sentence.terminals.map fun terminal => !params.deleteLabel.contains terminal.tag

@[inline] private def isQuoteWord (word : String) : Bool :=
  word == "'" || word == "\"" || word == "/"

private structure QuoteCandidate where
  survivingIndex : Nat
  rawIndex : Nat
  tag : String
deriving Inhabited

private def quoteCandidates (params : CompiledParams) (sentence : RawSentence)
    (keep : Array Bool) : Array QuoteCandidate := Id.run do
  let mut output : Array QuoteCandidate := #[]
  let mut survivingIndex := 0
  for rawIndex in [0:sentence.terminals.size] do
    let terminal := sentence.terminals[rawIndex]!
    if params.quoteLabel.contains terminal.tag && isQuoteWord terminal.word then
      output := output.push { survivingIndex, rawIndex, tag := terminal.tag }
    if keep.getD rawIndex false then
      survivingIndex := survivingIndex + 1
  return output

/-- Reproduce the 2006 asymmetric quote-deletion repair before declaring a length mismatch. -/
private def repairQuotes (params : CompiledParams) (gold test : RawSentence)
    (goldKeep testKeep : Array Bool) : Array Bool × Array Bool := Id.run do
  let mut goldQuotes := quoteCandidates params gold goldKeep
  let mut testQuotes := quoteCandidates params test testKeep
  let mut repairedGold := goldKeep
  let mut repairedTest := testKeep
  for testIndex in [0:testQuotes.size] do
    let testQuote := testQuotes[testIndex]!
    for goldIndex in [0:goldQuotes.size] do
      let goldQuote := goldQuotes[goldIndex]!
      if goldQuote.survivingIndex == testQuote.survivingIndex &&
          goldQuote.tag != testQuote.tag then
        let goldAlive := repairedGold.getD goldQuote.rawIndex false
        let testAlive := repairedTest.getD testQuote.rawIndex false
        if !goldAlive && testAlive then
          repairedGold := repairedGold.set! goldQuote.rawIndex true
          for later in [goldIndex:goldQuotes.size] do
            let candidate := goldQuotes[later]!
            goldQuotes := goldQuotes.set! later {
              candidate with survivingIndex := candidate.survivingIndex + 1 }
        else if goldAlive && !testAlive then
          repairedTest := repairedTest.set! testQuote.rawIndex true
          for later in [testIndex:testQuotes.size] do
            let candidate := testQuotes[later]!
            testQuotes := testQuotes.set! later {
              candidate with survivingIndex := candidate.survivingIndex + 1 }
  return (repairedGold, repairedTest)

private structure PreparedSentence where
  brackets : Array Bracket
  terminals : Array Terminal
  len : Nat

private def prefixCounts (keep : Array Bool) : Array Nat := Id.run do
  let mut counts := Array.replicate (keep.size + 1) 0
  let mut total := 0
  for index in [0:keep.size] do
    if keep.getD index false then
      total := total + 1
    counts := counts.set! (index + 1) total
  return counts

private def prepareSentence (params : CompiledParams) (raw : RawSentence)
    (keep : Array Bool) : PreparedSentence := Id.run do
  let offsets := prefixCounts keep
  let mut terminals : Array Terminal := #[]
  for index in [0:raw.terminals.size] do
    if keep.getD index false then
      terminals := terminals.push raw.terminals[index]!
  let mut brackets : Array Bracket := #[]
  for rawBracket in raw.brackets do
    let start := offsets.getD rawBracket.start 0
    let stop := offsets.getD rawBracket.stop start
    let label := bracketLabel params rawBracket.label
    let deleted :=
      match params.labelAliases with
      | some _ => params.bracketDeleteLabel.contains label
      | none => params.source.deleteLabel.any fun deletedLabel =>
          labelsEqual params label deletedLabel
    if start < stop && !deleted then
      brackets := brackets.push {
        label := if params.source.labeled then label else ""
        start
        stop
      }
  return { brackets, terminals, len := raw.len }

private def hashBracketMatches (gold test : Array Bracket) : Nat := Id.run do
  let mut remaining : Std.HashMap Bracket Nat :=
    Std.HashMap.emptyWithCapacity gold.size
  for bracket in gold do
    remaining := remaining.insert bracket (remaining.getD bracket 0 + 1)
  let mut matched := 0
  for bracket in test do
    let count := remaining.getD bracket 0
    if 0 < count then
      remaining := remaining.insert bracket (count - 1)
      matched := matched + 1
  return matched

private def greedyBracketMatches (params : CompiledParams)
    (gold test : Array Bracket) : Nat := Id.run do
  let mut consumed := Array.replicate test.size false
  let mut matched := 0
  for goldBracket in gold do
    let mut found := false
    for testIndex in [0:test.size] do
      let testBracket := test[testIndex]!
      if !found && !consumed[testIndex]! && goldBracket.start == testBracket.start &&
          goldBracket.stop == testBracket.stop &&
          labelsEqual params goldBracket.label testBracket.label then
        consumed := consumed.set! testIndex true
        found := true
    if found then
      matched := matched + 1
  return matched

private def bracketMatches (params : CompiledParams)
    (gold test : Array Bracket) : Nat :=
  if !params.source.labeled || params.labelAliases.isSome then
    hashBracketMatches gold test
  else
    greedyBracketMatches params gold test

@[inline] private def crosses (gold test : Bracket) : Bool :=
  (gold.start < test.start && test.start < gold.stop && gold.stop < test.stop) ||
    (test.start < gold.start && gold.start < test.stop && test.stop < gold.stop)

private def crossingCount (gold test : Array Bracket) : Nat := Id.run do
  let mut total := 0
  for testBracket in test do
    if gold.any fun goldBracket => crosses goldBracket testBracket then
      total := total + 1
  return total

private def correctTagCount (params : CompiledParams) (gold test : Array Terminal) : Nat :=
  Id.run do
    let mut correct := 0
    for index in [0:gold.size] do
      let goldTerminal := gold[index]!
      let testTerminal := test[index]!
      if labelsEqual params goldTerminal.tag testTerminal.tag then
        correct := correct + 1
    return correct

private def compareWords (params : CompiledParams) (gold test : Array Terminal) :
    Except Error Unit := do
  for index in [0:gold.size] do
    let goldWord := gold[index]!.word
    let testWord := test[index]!.word
    unless wordsEqual params goldWord testWord do
      throw (.wordMismatch index goldWord testWord)

private def scoreRawDetailed (params : CompiledParams) (gold test : RawSentence) :
    Except (Nat × Error) SentenceScore := do
  let initialGoldKeep := initialKeep params gold
  let initialTestKeep := initialKeep params test
  let initialGoldWords := initialGoldKeep.count true
  let initialTestWords := initialTestKeep.count true
  let (goldKeep, testKeep) :=
    if initialGoldWords == initialTestWords then
      (initialGoldKeep, initialTestKeep)
    else
      repairQuotes params gold test initialGoldKeep initialTestKeep
  let preparedGold := prepareSentence params gold goldKeep
  let preparedTest := prepareSentence params test testKeep
  let goldWords := preparedGold.terminals.size
  if preparedTest.terminals.isEmpty then
    throw (goldWords, .emptyTest)
  unless preparedGold.terminals.size == preparedTest.terminals.size do
    throw (goldWords,
      .lengthMismatch preparedGold.terminals.size preparedTest.terminals.size)
  match compareWords params preparedGold.terminals preparedTest.terminals with
  | .error cause => throw (goldWords, cause)
  | .ok () => pure ()
  let matched := bracketMatches params preparedGold.brackets preparedTest.brackets
  pure {
    len := preparedGold.len
    matched
    goldBrackets := preparedGold.brackets.size
    testBrackets := preparedTest.brackets.size
    crossing := crossingCount preparedGold.brackets preparedTest.brackets
    words := preparedGold.terminals.size
    correctTags := correctTagCount params preparedGold.terminals preparedTest.terminals
  }

private def scoreRaw (params : CompiledParams) (gold test : RawSentence) :
    Except Error SentenceScore :=
  (scoreRawDetailed params gold test).mapError Prod.snd

/-- Score one pair of PTB forests with already compiled parameters. -/
def scoreSentenceWith (params : CompiledParams) (interner : Interner)
    (gold test : Array Tree) : Except Error SentenceScore := do
  let rawGold ← extractForest params interner gold
  let rawTest ← extractForest params interner test
  scoreRaw params rawGold rawTest

/-- Functional convenience API that compiles parameters and scores one pair. -/
def scoreSentence (params : Params) (interner : Interner) (gold test : Array Tree) :
    Except Error SentenceScore := do
  let compiled ← params.compile
  scoreSentenceWith compiled interner gold test

private def resultLength : SentenceResult → Nat
  | .valid score => score.len
  | .skipped len _ => len
  | .error len _ _ => len

private def Summary.add (summary : Summary) : SentenceResult → Summary
  | .skipped _ _ => { summary with
      sentences := summary.sentences + 1
      skipped := summary.skipped + 1 }
  | .error _ _ _ => { summary with
      sentences := summary.sentences + 1
      errors := summary.errors + 1 }
  | .valid score => { summary with
      sentences := summary.sentences + 1
      valid := summary.valid + 1
      matched := summary.matched + score.matched
      goldBrackets := summary.goldBrackets + score.goldBrackets
      testBrackets := summary.testBrackets + score.testBrackets
      complete := summary.complete +
        if score.goldBrackets == score.testBrackets &&
            score.testBrackets == score.matched then 1 else 0
      crossing := summary.crossing + score.crossing
      noCrossing := summary.noCrossing + if score.crossing == 0 then 1 else 0
      atMostTwoCrossing := summary.atMostTwoCrossing + if score.crossing ≤ 2 then 1 else 0
      words := summary.words + score.words
      correctTags := summary.correctTags + score.correctTags }

/-- Score one sentence while preserving EVALB's valid, skipped, and error statuses as data. -/
def scoreSentenceResultWith (params : CompiledParams) (interner : Interner)
    (gold test : Array Tree) : SentenceResult :=
  match extractForest params interner gold with
  | .error cause => .error 0 0 cause
  | .ok rawGold =>
      let initialGoldWords := (initialKeep params rawGold).count true
      match extractForest params interner test with
      | .error cause => .error rawGold.len initialGoldWords cause
      | .ok rawTest =>
          match scoreRawDetailed params rawGold rawTest with
          | .ok score => .valid score
          | .error (goldWords, .emptyTest) => .skipped rawGold.len goldWords
          | .error (goldWords, cause) => .error rawGold.len goldWords cause

/-- Functional status-preserving sentence scorer with parameter compilation. -/
def scoreSentenceResult (params : Params) (interner : Interner)
    (gold test : Array Tree) : Except Error SentenceResult := do
  let compiled ← params.compile
  pure <| scoreSentenceResultWith compiled interner gold test

/-- Score an aligned corpus and compute EVALB's micro summaries. -/
def scoreCorpusWith (params : CompiledParams) (interner : Interner)
    (gold test : Array (Array Tree)) : Except Error CorpusScore := do
  unless gold.size == test.size do
    throw (.sentenceCountMismatch gold.size test.size)
  let mut results : Array SentenceResult := #[]
  let mut all : Summary := {}
  let mut cutoff : Summary := {}
  for index in [0:gold.size] do
    let result := scoreSentenceResultWith params interner gold[index]! test[index]!
    results := results.push result
    all := all.add result
    if resultLength result ≤ params.source.cutoffLen then
      cutoff := cutoff.add result
  pure { results, all, cutoff }

/-- Functional convenience API that compiles parameters once for the whole corpus. -/
def scoreCorpus (params : Params) (interner : Interner)
    (gold test : Array (Array Tree)) : Except Error CorpusScore := do
  let compiled ← params.compile
  scoreCorpusWith compiled interner gold test

private def corpusLines (input : String) : List String :=
  if input.isEmpty then
    []
  else
    let lines := input.splitOn "\n"
    if input.endsWith "\n" then lines.dropLast else lines

private inductive ShapeToken where
  | openParen
  | closeParen
  | atom
deriving Inhabited

private def shapeTokens (input : String) : Array ShapeToken := Id.run do
  let mut tokens : Array ShapeToken := #[]
  let mut insideAtom := false
  for character in input.toList do
    if character.isWhitespace then
      if insideAtom then
        tokens := tokens.push .atom
        insideAtom := false
    else if character == '(' then
      if insideAtom then
        tokens := tokens.push .atom
        insideAtom := false
      tokens := tokens.push .openParen
    else if character == ')' then
      if insideAtom then
        tokens := tokens.push .atom
        insideAtom := false
      tokens := tokens.push .closeParen
    else
      insideAtom := true
  if insideAtom then
    tokens := tokens.push .atom
  return tokens

/-- Reject PTB shapes that the nonempty labelled `Tree` representation cannot preserve. -/
private def validateTextShape (lineNumber : Nat) (input : String) : Except Error Unit := do
  let tokens := shapeTokens input
  for index in [0:tokens.size] do
    match tokens[index]! with
    | .openParen =>
        match tokens[index + 1]? with
        | some .openParen =>
            throw (.unsupportedTextShape lineNumber (index + 1)
              "label-less nodes are not representable")
        | some .closeParen =>
            throw (.unsupportedTextShape lineNumber (index + 1)
              "empty label-less nodes are not representable")
        | some .atom =>
            if let some .closeParen := tokens[index + 2]? then
              throw (.unsupportedTextShape lineNumber (index + 1)
                "zero-child labelled nodes are not representable")
        | none => pure ()
    | _ => pure ()

/-- Parse one PTB forest per physical line while preserving blank sentences. -/
def parsePtbCorpus (interner : Interner) (input : String) :
    Except Error (Interner × Array (Array Tree)) := do
  let mut nextInterner := interner
  let mut sentences : Array (Array Tree) := #[]
  let mut lineNumber := 0
  for line in corpusLines input do
    lineNumber := lineNumber + 1
    validateTextShape lineNumber line
    match Nlp.IO.parseBracketed nextInterner line with
    | .ok (afterLine, forest) =>
        nextInterner := afterLine
        sentences := sentences.push forest
    | .error error => throw (.ptb error)
  pure (nextInterner, sentences)

/-- Pure canonical-PTB text-to-score path used by regression fixtures and effectful adapters. -/
def scorePtbText (params : Params) (gold test : String) : Except Error CorpusScore := do
  let (afterGold, goldCorpus) ← parsePtbCorpus Interner.empty gold
  let (interner, testCorpus) ← parsePtbCorpus afterGold test
  scoreCorpus params interner goldCorpus testCorpus

end Nlp.Eval.Evalb
