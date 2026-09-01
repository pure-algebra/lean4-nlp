import Nlp.Pipeline.Ann
import Nlp.Pipeline.Parallel

/-!
# Functional annotators at an effectful boundary

Pure annotators remain ordinary `Ann Id` values. `Ann.lift` embeds them into any applicative
effect without changing their hot path. The `NLP` facade adds cancellation-aware, ordered,
bounded traversal for applications that want one effectful API from files through annotation.
-/

namespace Nlp

namespace Ann

/-- Package a polymorphic pure document transformation as an annotator. -/
@[inline] def fromPure (name : String)
    (run : {available : Layers} → Sub requires available →
      Doc available → Doc (produces ++ available)) : Ann Id requires produces where
  name := name
  run := run

/-- Lift a pure annotator into an effect without wrapping or changing its pure implementation. -/
@[inline] def lift [Pure M] (ann : Ann Id requires produces) : Ann M requires produces where
  name := ann.name
  run := fun requirements doc ↦ pure (ann.run requirements doc)

end Ann

namespace NLP

/-- Run one effectful annotator with requirements discharged at the call site. -/
@[inline] def annotate (ann : Ann NLP requires produces) (doc : Doc available)
    (requirementsProof : Sub requires available := by decide) :
    NLP (Doc (produces ++ available)) :=
  ann.run requirementsProof doc

/-- Run one pure annotator through the preferred effectful facade. -/
@[inline] def annotatePure (ann : Ann Id requires produces) (doc : Doc available)
    (requirementsProof : Sub requires available := by decide) :
    NLP (Doc (produces ++ available)) :=
  pure (ann.run requirementsProof doc)

/--
Apply an effectful function to an array with bounded outer parallelism and stable output order.

Cancellation is checked between items. Nested calls are forced onto the serial path by
`traverseChunks`, preventing multiplicative thread fan-out.
-/
private def traverseArrayCore (input : Array α) (worker : α → NLP β) : NLP (Array β) := do
  let chunks ← traverseChunks input fun source start stop ↦ do
    let mut output := Array.emptyWithCapacity (stop - start)
    for index in [start:stop] do
      checkCancelled
      match source[index]? with
      | some value => output := output.push (← worker value)
      | none =>
        throw <| .invalidConfig "parallel chunk escaped its source array"
    return output
  let mut output := Array.emptyWithCapacity input.size
  for chunk in chunks do
    for value in chunk do
      output := output.push value
  return output

/-- Apply the configured traversal grain to an ordered, bounded array traversal. -/
@[inline] def traverseArray (input : Array α) (worker : α → NLP β) : NLP (Array β) :=
  traverseArrayCore input worker

/--
Traverse with a cost-informed item grain while preserving every other runtime setting.

Use this when each item is known to be expensive, such as a complete CKY sentence. Zero is
normalized to one by the planner.
-/
@[inline] def traverseArrayWithGrain (minGrain : Nat) (input : Array α)
    (worker : α → NLP β) : NLP (Array β) :=
  withConfig (fun config ↦ { config with parallelMinGrain := minGrain }) <|
    traverseArrayCore input worker

/-- Annotate documents concurrently when the configured grain admits it, preserving order. -/
@[inline] def annotateMany (ann : Ann NLP requires produces)
    (documents : Array (Doc available))
    (requirementsProof : Sub requires available := by decide) :
    NLP (Array (Doc (produces ++ available))) :=
  traverseArray documents fun doc ↦ ann.run requirementsProof doc

/-- Annotate with an explicit number of documents per parallel scheduling unit. -/
@[inline] def annotateManyWithGrain (minGrain : Nat) (ann : Ann NLP requires produces)
    (documents : Array (Doc available))
    (requirementsProof : Sub requires available := by decide) :
    NLP (Array (Doc (produces ++ available))) :=
  traverseArrayWithGrain minGrain documents fun doc ↦ ann.run requirementsProof doc

/-- Lift and apply a pure annotator over a corpus through the effectful scheduler. -/
@[inline] def annotateManyPure (ann : Ann Id requires produces)
    (documents : Array (Doc available))
    (requirementsProof : Sub requires available := by decide) :
    NLP (Array (Doc (produces ++ available))) :=
  traverseArray documents fun doc ↦ pure (ann.run requirementsProof doc)

end NLP

end Nlp
