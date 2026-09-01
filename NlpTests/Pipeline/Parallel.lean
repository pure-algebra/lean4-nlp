import Nlp.Pipeline.Parallel

namespace NlpTests.Pipeline.Parallel

open Nlp Nlp.Parallel

def exhaustivePlans : Bool := Id.run do
  for size in [0:256] do
    for workers in [0:17] do
      for grain in [0:33] do
        let chunks := chunkPlan size workers grain
        if !validPlan size chunks || !balancedPlan chunks || !coarsePlan grain chunks then
          return false
        if !boundedPlan workers chunks then
          return false
  return true

private def weightPatterns (size : Nat) : Array (Array Nat) :=
  #[Array.replicate size 0,
    Array.replicate size 1,
    Array.ofFn (n := size) fun index ↦ index + 1,
    Array.ofFn (n := size) fun index ↦ if index = size / 2 then 1000 else 1]

def exhaustiveWeightedPlans : Bool := Id.run do
  for size in [0:65] do
    for weights in weightPatterns size do
      for workers in [0:9] do
        for grain in [0:17] do
          let chunks := weightedChunkPlan weights workers grain
          if !validPlan size chunks || !boundedPlan workers chunks ||
              !weightedCoarsePlan weights grain chunks then
            return false
  return true

private def smallWeightArrays : Nat → Array (Array Nat)
  | 0 => #[#[]]
  | size + 1 =>
      (smallWeightArrays size).flatMap fun weights ↦
        #[weights.push 0, weights.push 1, weights.push 4]

def exhaustiveCartesianWeightedPlans : Bool := Id.run do
  for size in [0:8] do
    for weights in smallWeightArrays size do
      for workers in [0:7] do
        for grain in [0:10] do
          let chunks := weightedChunkPlan weights workers grain
          if !validPlan size chunks || !boundedPlan workers chunks ||
              !weightedCoarsePlan weights grain chunks then
            return false
  return true

example : exhaustivePlans = true := by native_decide
example : exhaustiveWeightedPlans = true := by native_decide
example : exhaustiveCartesianWeightedPlans = true := by native_decide

example : boundedWorkers 0 0 0 = 1 := by decide
example : boundedWorkers 32 12 8 = 8 := by decide
example : chunkPlan 0 8 64 = #[] := by decide
example : validPlan 1 #[] = false := by decide
example : validPlan 1 #[⟨0, 0⟩] = false := by decide
example : validPlan 3 #[⟨0, 1⟩, ⟨2, 3⟩] = false := by decide
example : validPlan 3 #[⟨0, 2⟩, ⟨1, 3⟩] = false := by decide
example : validPlan 3 #[⟨0, 4⟩] = false := by decide
example : validPlan 3 #[⟨0, 2⟩] = false := by decide
example : weightedCoarsePlan #[1] 1 #[⟨0, 2⟩, ⟨2, 3⟩] = false := by decide
example : chunkPlan 10 4 1 = #[⟨0, 3⟩, ⟨3, 6⟩, ⟨6, 8⟩, ⟨8, 10⟩] := by
  native_decide

example : chunkPlan 10 8 64 = #[⟨0, 10⟩] := by
  native_decide

example : totalWeight #[0, 2, 0, 5] = 9 := by decide

example : weightedChunkPlan #[1, 1, 8, 1, 1] 2 1 = #[⟨0, 2⟩, ⟨2, 5⟩] := by
  native_decide

example : weightedChunkPlan #[1000, 1, 1, 1] 4 2 = #[⟨0, 1⟩, ⟨1, 4⟩] := by
  native_decide

example : weightedChunkPlan #[99, 99, 2] 2 1 = #[⟨0, 1⟩, ⟨1, 3⟩] := by
  native_decide

example : weightedChunkPlan #[5, 5, 5, 5] 4 6 = #[⟨0, 2⟩, ⟨2, 4⟩] := by
  native_decide

example : weightedChunkPlan #[2, 1, 1, 3] 3 2 =
    #[⟨0, 1⟩, ⟨1, 3⟩, ⟨3, 4⟩] := by
  native_decide

example : weightedChunkPlan #[3, 1, 2, 4] 3 3 =
    #[⟨0, 1⟩, ⟨1, 3⟩, ⟨3, 4⟩] := by
  native_decide

example (size count : Nat) (hcount : 0 < count) :
    chunkBoundary size count count = size :=
  chunkBoundary_end size count hcount

example (size count index : Nat) :
    (chunkAt size count index).stop = (chunkAt size count (index + 1)).start :=
  chunkAt_adjacent size count index

example (size workers grain : Nat) (index : Fin (chunkCount size workers grain)) :
    (chunkPlan size workers grain)[index] =
      chunkAt size (chunkCount size workers grain) index :=
  chunkPlan_get size workers grain index

example (size workers grain : Nat) :
    boundedPlan workers (chunkPlan size workers grain) = true :=
  boundedPlan_chunkPlan size workers grain

example (weights : Array Nat) (workers minWeight : Nat) :
    boundedPlan workers (weightedChunkPlan weights workers minWeight) = true :=
  boundedPlan_weightedChunkPlan weights workers minWeight

example (size workers grain : Nat) :
    coarsePlan grain (chunkPlan size workers grain) = true :=
  coarsePlan_chunkPlan size workers grain

example (size workers grain : Nat) :
    balancedPlan (chunkPlan size workers grain) = true :=
  balancedPlan_chunkPlan size workers grain

example (size workers grain : Nat) (hsize : 0 < size)
    (index : Fin (chunkCount size workers grain)) :
    (chunkPlan size workers grain)[index].start <
        (chunkPlan size workers grain)[index].stop ∧
      (chunkPlan size workers grain)[index].stop ≤ size :=
  chunkPlan_get_wf size workers grain hsize index

def orderedWorker (_input : Array Nat) (start stop : Nat) : NLP (Nat × Nat) := do
  NLP.checkCancelled
  return (start, stop)

def testOrderedTraversal : IO Unit := do
  let input := Array.range 100
  let config : Config := {
    numThreads := 4
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config (NLP.traverseChunks input orderedWorker) with
  | .ok result =>
      let workers := boundedWorkers 4 hardwareConcurrency 4
      let expected := (chunkPlan input.size workers 1).map fun chunk ↦
        (chunk.start, chunk.stop)
      if result != expected then
        throw <| IO.userError s!"unordered traversal: {result}"
  | .error _ => throw <| IO.userError "parallel traversal failed"

def testSingleChunk : IO Unit := do
  let input := Array.range 10
  let config : Config := { numThreads := 8, parallelMinGrain := 64 }
  match ← NLP.runIO config (NLP.traverseChunks input orderedWorker) with
  | .ok #[(0, 10)] => pure ()
  | _ => throw <| IO.userError "single-chunk path failed"

def testWeightedTraversal : IO Unit := do
  let input := #[1, 1, 8, 1, 1]
  let config : Config := {
    numThreads := 2
    parallelMinWeight := 1
    maxDedicatedThreads := 2
  }
  match ← NLP.runIO config (NLP.traverseWeightedChunks input id orderedWorker) with
  | .ok #[(0, 2), (2, 5)] => pure ()
  | _ => throw <| IO.userError "weighted traversal did not preserve its planned order"

def testEmptyWeightedTraversal : IO Unit := do
  let input : Array Nat := #[]
  match ← NLP.runIO {} (NLP.traverseWeightedChunks input id orderedWorker) with
  | .ok #[] => pure ()
  | _ => throw <| IO.userError "empty weighted traversal did not remain empty"

def failingWorker (_input : Array Nat) (start _stop : Nat) : NLP Nat := do
  NLP.checkCancelled
  if start == 0 then
    throw <| .invalidInput "chunk 0" "expected test failure"
  return start

def racingFailureWorker (_input : Array Nat) (start _stop : Nat) : NLP Nat := do
  if start = 0 then
    liftM <| IO.sleep 25
  throw <| .invalidInput s!"chunk {start}" "expected racing failure"

def testErrorPath : IO Unit := do
  let input := Array.range 100
  let config : Config := {
    numThreads := 4
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config (NLP.traverseChunks input failingWorker) with
  | .error (.invalidInput "chunk 0" "expected test failure") => pure ()
  | _ => throw <| IO.userError "parallel error was not preserved"

def testErrorDrainsChildren : IO Unit := do
  let cancellation ← liftM <| Std.CancellationContext.new
  let config : Config := {
    numThreads := 4
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  let env : Env := { config, cancellation }
  let result ← liftM <|
    (NLP.runIn env (NLP.traverseChunks (Array.range 100) failingWorker)).toBaseIO
  let alive ← liftM <| cancellation.countAliveTokens
  match result with
  | .error (.invalidInput "chunk 0" "expected test failure") =>
      if alive != 1 then
        throw <| IO.userError s!"parallel failure leaked {alive - 1} child contexts"
  | _ => throw <| IO.userError "parallel drain test did not preserve its error"

def testLowestChunkErrorWins : IO Unit := do
  let config : Config := {
    numThreads := 4
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config (NLP.traverseChunks (Array.range 100) racingFailureWorker) with
  | .error (.invalidInput "chunk 0" "expected racing failure") => pure ()
  | _ => throw <| IO.userError "parallel traversal did not preserve lowest-chunk error order"

def testSuccessReleasesChildren : IO Unit := do
  let cancellation ← liftM <| Std.CancellationContext.new
  let config : Config := {
    numThreads := 4
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  let env : Env := { config, cancellation }
  let result ← liftM <|
    (NLP.runIn env (NLP.traverseChunks (Array.range 100) orderedWorker)).toBaseIO
  let alive ← liftM <| cancellation.countAliveTokens
  match result with
  | .ok _ =>
      if alive != 1 then
        throw <| IO.userError s!"parallel success leaked {alive - 1} child contexts"
  | .error _ => throw <| IO.userError "parallel success-path traversal failed"

#eval testOrderedTraversal
#eval testSingleChunk
#eval testWeightedTraversal
#eval testEmptyWeightedTraversal
#eval testErrorPath
#eval testErrorDrainsChildren
#eval testLowestChunkErrorWins
#eval testSuccessReleasesChildren

end NlpTests.Pipeline.Parallel
