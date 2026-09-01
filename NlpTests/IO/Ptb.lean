import Nlp.IO.PtbLemmas

namespace NlpTests.IO.Ptb

open Nlp Nlp.IO

private def shape (tree : Tree) : String :=
  tree.cata
    (fun word ↦ "L[" ++ toString word ++ "]")
    (fun category child children ↦
      children.foldl (fun output next ↦ output ++ next) ("N[" ++ toString category ++ child) ++
        "]")

private def yieldNames (interner : Interner) (tree : Tree) : Option (Array String) := do
  let mut names : Array String := #[]
  for word in tree.yieldWords do
    let name ← interner.name? word
    names := names.push name
  pure names

private def simple : String :=
  "(S (NP (DT The) (NN cat)) (VP (VBD slept)) (. .))"

private def simpleCanonical : Bool :=
  match parseBracketed Interner.empty simple with
  | .ok (interner, trees) =>
    match trees.toList with
    | [tree] =>
      tree.width == 4 && yieldNames interner tree == some #["The", "cat", "slept", "."] &&
        match renderBracketed interner tree with
        | .ok rendered => rendered == simple
        | .error _ => false
    | _ => false
  | .error _ => false

#guard simpleCanonical

private def multiple : String :=
  "\n(TOP\n  (S1 (NN one)))\n\t(ROOT (S (VB two)))   (S1 (JJ three))\n"

private def multilineAndMultiple : Bool :=
  match parseBracketed Interner.empty multiple with
  | .ok (interner, trees) =>
    trees.size == 3 && trees.foldl (fun width tree ↦ width + tree.width) 0 == 3 &&
      match trees.toList with
      | [top, root, s1] =>
        yieldNames interner top == some #["one"] &&
          yieldNames interner root == some #["two"] && yieldNames interner s1 == some #["three"]
      | _ => false
  | .error _ => false

#guard multilineAndMultiple

private def labelLess : String := "( (S (INTJ (RB No)) (, ,)))"

private def labelLessWrapper : Bool :=
  match parseBracketed Interner.empty labelLess with
  | .ok (interner, trees) =>
    match trees.toList with
    | [tree] =>
      tree.width == 2 && yieldNames interner tree == some #["No", ","] &&
        match renderBracketed interner tree with
        | .ok rendered => rendered == "(S (INTJ (RB No)) (, ,))"
        | .error _ => false
    | _ => false
  | .error _ => false

#guard labelLessWrapper

private def specialAtoms : String := "(S (-NONE- *T*-1) (-LRB- -LRB-))"

private def reservedHyphensRemainAtoms : Bool :=
  match parseBracketed Interner.empty specialAtoms with
  | .ok (interner, trees) =>
    match trees.toList with
    | [tree] =>
      yieldNames interner tree == some #["*T*-1", "-LRB-"] &&
        match renderBracketed interner tree with
        | .ok rendered => rendered == specialAtoms
        | .error _ => false
    | _ => false
  | .error _ => false

#guard reservedHyphensRemainAtoms

private def malformed (input : String) (accept : PtbError → Bool) : Bool :=
  match parseBracketed Interner.empty input with
  | .error error => accept error
  | .ok _ => false

#guard malformed ")" fun error ↦ match error with | .strayClose 1 => true | _ => false
#guard malformed "(S (NN dog)" fun error ↦ match error with | .missingClose 1 => true | _ => false
#guard malformed "(" fun error ↦ match error with | .missingClose 1 => true | _ => false
#guard malformed "()" fun error ↦ match error with | .emptyNode 1 => true | _ => false
#guard malformed "(S)" fun error ↦ match error with | .emptyNode 1 => true | _ => false
#guard malformed "bare" fun error ↦ match error with | .malformedAtom 1 "bare" => true | _ => false
#guard malformed "(S (NN one) extra)" fun error ↦
  match error with | .malformedAtom _ "extra" => true | _ => false
#guard malformed "( (NN one) (NN two))" fun error ↦
  match error with | .labelLessArity 1 2 => true | _ => false
#guard malformed "(S ((NN one)))" fun error ↦
  match error with | .labelLessNonRoot 3 => true | _ => false
#guard malformed "(S one two)" fun error ↦
  match error with | .childAfterTerminal 4 => true | _ => false
#guard malformed "(S one (NN two))" fun error ↦
  match error with | .childAfterTerminal 4 => true | _ => false

private def parseRenderParse : Bool :=
  match parseBracketed Interner.empty simple with
  | .error _ => false
  | .ok (interner, trees) =>
    match trees.toList with
    | [tree] =>
      match renderBracketed interner tree with
      | .error _ => false
      | .ok rendered =>
        match parseBracketed interner rendered with
        | .ok (_, reparsed) =>
          match reparsed.toList with
          | [other] => shape other == shape tree && other.yieldWords == tree.yieldWords
          | _ => false
        | .error _ => false
    | _ => false

#guard parseRenderParse

private def unknownCategory : Bool :=
  match renderBracketed Interner.empty (.node 99 (.leaf 0) #[]) with
  | .error (.unknownCategory 99) => true
  | _ => false

#guard unknownCategory

#guard match renderBracketed Interner.empty (.leaf 7) with
  | .error (.bareLeafRoot 7) => true
  | _ => false

private def unknownWord : Bool :=
  match Interner.empty.intern "NN" with
  | .error _ => false
  | .ok (interner, category) =>
    match renderBracketed interner (.node category (.leaf 99) #[]) with
    | .error (.unknownWord 99) => true
    | _ => false

#guard unknownWord

private def unprintableWord : Bool :=
  match Interner.empty.intern "NN" with
  | .error _ => false
  | .ok (withTag, category) =>
    match withTag.intern "two words" with
    | .error _ => false
    | .ok (interner, word) =>
      match renderBracketed interner (.node category (.leaf word) #[]) with
      | .error (.unprintableAtom .word _ "two words") => true
      | _ => false

#guard unprintableWord

private def unprintableParen : Bool :=
  match Interner.empty.intern "NN" with
  | .error _ => false
  | .ok (withTag, category) =>
    match withTag.intern "(" with
    | .error _ => false
    | .ok (interner, word) =>
      match renderBracketed interner (.node category (.leaf word) #[]) with
      | .error (.unprintableAtom .word _ "(") => true
      | _ => false

#guard unprintableParen

private def invalidShape : Bool :=
  match parseBracketed Interner.empty "(S (NN one) (NN two))" with
  | .error _ => false
  | .ok (interner, trees) =>
    match trees.toList with
    | [.node category (.node tag (.leaf one) #[]) #[.node _ (.leaf two) #[]]] =>
      match renderBracketed interner (.node category (.leaf one) #[.node tag (.leaf two) #[]]) with
      | .error (.invalidTreeShape _) => true
      | _ => false
    | _ => false

#guard invalidShape

example : parseBracketed Interner.empty "" = .ok (Interner.empty, #[]) :=
  parseBracketed_empty Interner.empty

example (word : Word) :
    renderBracketed Interner.empty (.leaf word) = .error (.bareLeafRoot word) :=
  renderBracketed_leaf Interner.empty word

example (category : Cat) (first second : Word) :
    renderBracketed Interner.empty (.node category (.leaf first) #[.leaf second]) =
      .error (.invalidTreeShape category) :=
  renderBracketed_preterminal_with_sibling Interner.empty category first second

end NlpTests.IO.Ptb
