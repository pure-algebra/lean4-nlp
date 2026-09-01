import Nlp.Core.Data.Interner
import Nlp.Syntax.Tree

/-!
# Penn Treebank bracketed trees

This module reads whitespace-insensitive PTB trees into the existing interned `Tree` shape. A
preterminal is `Tree.node tag (.leaf word) #[]`; an internal node has node-valued children. The
source format's label-less singleton outer wrapper is accepted and erased because `Tree` has no
unlabelled-node constructor.
-/

namespace Nlp.IO

/-- Whether an atom names a category or a terminal word. -/
inductive PtbAtomRole where
  | category
  | word
  deriving Repr, DecidableEq, Inhabited

/-- Typed PTB syntax, interning, and printing failures. Token positions are one-based. -/
inductive PtbError where
  | strayClose (token : Nat)
  | missingClose (openedAt : Nat)
  | malformedAtom (token : Nat) (atom : String)
  | childAfterTerminal (token : Nat)
  | emptyNode (openedAt : Nat)
  | labelLessNonRoot (openedAt : Nat)
  | labelLessArity (openedAt found : Nat)
  | internerError (error : Interner.Error)
  | unknownCategory (id : Cat)
  | unknownWord (id : Word)
  | unprintableAtom (role : PtbAtomRole) (id : UInt32) (value : String)
  | bareLeafRoot (word : Word)
  | invalidTreeShape (category : Cat)
  deriving Repr, DecidableEq, Inhabited

private inductive PtbToken where
  | openParen
  | closeParen
  | atom (value : String)

private def tokenize (input : String) : Array PtbToken := Id.run do
  let mut tokens : Array PtbToken := #[]
  let mut reversedAtom : List Char := []
  for character in input.toList do
    if character.isWhitespace then
      unless reversedAtom.isEmpty do
        tokens := tokens.push (.atom (String.ofList reversedAtom.reverse))
        reversedAtom := []
    else if character = '(' then
      unless reversedAtom.isEmpty do
        tokens := tokens.push (.atom (String.ofList reversedAtom.reverse))
        reversedAtom := []
      tokens := tokens.push .openParen
    else if character = ')' then
      unless reversedAtom.isEmpty do
        tokens := tokens.push (.atom (String.ofList reversedAtom.reverse))
        reversedAtom := []
      tokens := tokens.push .closeParen
    else
      reversedAtom := character :: reversedAtom
  unless reversedAtom.isEmpty do
    tokens := tokens.push (.atom (String.ofList reversedAtom.reverse))
  return tokens

private structure PtbFrame where
  openedAt : Nat
  label : Option String := none
  terminal : Option String := none
  children : Array Tree := #[]

private def internAtom (interner : Interner) (atom : String) :
    Except PtbError (Interner × UInt32) :=
  match interner.intern atom with
  | .ok result => .ok result
  | .error error => .error (.internerError error)

private def finishFrame (interner : Interner) (frame : PtbFrame) (isRoot : Bool) :
    Except PtbError (Interner × Tree) := do
  match frame.label, frame.terminal, frame.children.toList with
  | none, none, [] => throw (.emptyNode frame.openedAt)
  | none, none, [tree] =>
    if isRoot then pure (interner, tree) else throw (.labelLessNonRoot frame.openedAt)
  | none, none, children => throw (.labelLessArity frame.openedAt children.length)
  | none, some _, _ => throw (.malformedAtom frame.openedAt "")
  | some _, none, [] => throw (.emptyNode frame.openedAt)
  | some label, none, child :: children =>
    let (next, category) ← internAtom interner label
    pure (next, .node category child children.toArray)
  | some label, some word, [] =>
    let (afterLabel, category) ← internAtom interner label
    let (afterWord, terminal) ← internAtom afterLabel word
    pure (afterWord, .node category (.leaf terminal) #[])
  | some _, some _, _ :: _ => throw (.childAfterTerminal frame.openedAt)

/-- Parse zero or more PTB trees while persistently extending the supplied interner.

Whitespace is arbitrary. Labelled roots and a label-less singleton outer wrapper are accepted;
the latter is erased to fit `Tree`. The explicit frame stack keeps the parser total.
-/
def parseBracketed (interner : Interner) (input : String) :
    Except PtbError (Interner × Array Tree) := do
  let mut nextInterner := interner
  let mut frames : List PtbFrame := []
  let mut trees : Array Tree := #[]
  let mut tokenNumber := 0
  for token in tokenize input do
    tokenNumber := tokenNumber + 1
    match token with
    | .openParen =>
      match frames with
      | frame :: _ =>
        if frame.terminal.isSome then throw (.childAfterTerminal tokenNumber) else pure ()
      | [] => pure ()
      frames := { openedAt := tokenNumber } :: frames
    | .closeParen =>
      match frames with
      | [] => throw (.strayClose tokenNumber)
      | frame :: rest =>
        let (afterFrame, tree) ← finishFrame nextInterner frame rest.isEmpty
        nextInterner := afterFrame
        frames := rest
        match frames with
        | [] => trees := trees.push tree
        | parent :: parents =>
          if parent.terminal.isSome then
            throw (.childAfterTerminal tokenNumber)
          else
            frames := { parent with children := parent.children.push tree } :: parents
    | .atom atom =>
      match frames with
      | [] => throw (.malformedAtom tokenNumber atom)
      | frame :: rest =>
        match frame.label, frame.terminal with
        | none, none =>
          if frame.children.isEmpty then
            frames := { frame with label := some atom } :: rest
          else
            throw (.malformedAtom tokenNumber atom)
        | some _, none =>
          if frame.children.isEmpty then
            frames := { frame with terminal := some atom } :: rest
          else
            throw (.malformedAtom tokenNumber atom)
        | _, some _ => throw (.childAfterTerminal tokenNumber)
  match frames with
  | [] => pure (nextInterner, trees)
  | frame :: _ => throw (.missingClose frame.openedAt)

private def printableAtom (value : String) : Bool :=
  !value.isEmpty && value.toList.all fun character ↦
    !character.isWhitespace && character != '(' && character != ')'

private def resolveAtom (interner : Interner) (role : PtbAtomRole) (id : UInt32) :
    Except PtbError String :=
  match interner.name? id with
  | none =>
    match role with
    | .category => .error (.unknownCategory id)
    | .word => .error (.unknownWord id)
  | some value =>
    if printableAtom value then .ok value else .error (.unprintableAtom role id value)

/-- Print one tree in a canonical single-line PTB form.

Every referenced ID must resolve to a nonempty atom without whitespace or literal parentheses.
Successful output parses back to the same labelled/preterminal structure and terminal yield when
read with the same interner.
-/
def renderBracketed (interner : Interner) (tree : Tree) : Except PtbError String :=
  match tree with
  | .leaf word => .error (.bareLeafRoot word)
  | .node _ _ _ =>
    tree.para
      (fun word ↦ resolveAtom interner .word word)
      (fun category first rest =>
        match first.1 with
        | .leaf _ =>
          if rest.isEmpty then do
            let label ← resolveAtom interner .category category
            let word ← first.2
            pure ("(" ++ label ++ " " ++ word ++ ")")
          else
            .error (.invalidTreeShape category)
        | .node _ _ _ => do
          let label ← resolveAtom interner .category category
          let firstChild ← first.2
          let mut renderedChildren := firstChild
          for (child, rendered) in rest do
            match child with
            | .leaf _ => throw (.invalidTreeShape category)
            | .node _ _ _ =>
              let childText ← rendered
              renderedChildren := renderedChildren ++ " " ++ childText
          pure ("(" ++ label ++ " " ++ renderedChildren ++ ")"))

end Nlp.IO
