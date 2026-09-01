import Nlp

/-!
# Parallel scheduling benchmark

This standalone executable measures Lean's built-in `Task.spawn` on independent, CPU-bound corpus
work. The production scheduler lives in `Nlp.Pipeline.Parallel`; this benchmark keeps a small
checksum kernel and task-boundary floor for repeatable performance experiments.
-/

namespace ParallelBenchmark

/-- A half-open array range `[start, stop)`. Only `chunkPlan` constructs benchmark chunks. -/
structure Chunk where
  start : Nat
  stop : Nat
deriving Repr, DecidableEq, Inhabited

/-- Scheduling policy kept narrower than Lean's raw numeric priorities. -/
inductive Scheduler where
  | pooled
  | dedicated
deriving Repr, DecidableEq, Inhabited

@[inline] def Scheduler.priority : Scheduler → Task.Priority
  | .pooled => Task.Priority.default
  | .dedicated => Task.Priority.dedicated

/-- Scheduler knobs.  `minGrain` prevents task overhead from dominating small inputs. -/
structure Config where
  workers : Nat := 1
  minGrain : Nat := 65536
  scheduler : Scheduler := .dedicated
deriving Repr, Inhabited

/-- Split `size` items into at most `workers` contiguous, balanced, nonempty chunks. -/
def chunkPlan (size : Nat) (config : Config) : Array Chunk := Id.run do
  if size == 0 then
    return #[]
  let workers := max config.workers 1
  let grain := max config.minGrain 1
  let grainBound := (size - 1) / grain + 1
  let chunkCount := min workers grainBound
  let shortLength := size / chunkCount
  let longerCount := size % chunkCount
  let mut chunks := Array.emptyWithCapacity chunkCount
  let mut start := 0
  for index in [0:chunkCount] do
    let length := shortLength + if index < longerCount then 1 else 0
    let stop := start + length
    chunks := chunks.push ⟨start, stop⟩
    start := stop
  return chunks

/-- Check the partition contract without trusting the worker. -/
def validPlan (size : Nat) (chunks : Array Chunk) : Bool := Id.run do
  let mut cursor := 0
  let mut valid := size == 0 || !chunks.isEmpty
  for chunk in chunks do
    valid := valid && chunk.start == cursor && chunk.start < chunk.stop && chunk.stop ≤ size
    cursor := chunk.stop
  return valid && cursor == size

/--
Run one pure worker per chunk and collect results in chunk order.

The worker is invoked once per task, not once per element.  Its inner loop should therefore be a
monomorphic first-order kernel.  Spawning marks captured object graphs multi-threaded permanently;
callers must treat `input` as read-only after crossing this boundary.
-/
@[noinline] def mapChunks (config : Config) (input : Array α)
    (worker : Array α → Nat → Nat → β) : Array β :=
  let chunks := chunkPlan input.size config
  if chunks.size ≤ 1 then
    chunks.map fun chunk ↦ worker input chunk.start chunk.stop
  else
    let tasks := chunks.map fun chunk ↦
      Task.spawn (prio := config.scheduler.priority) fun _ ↦
        worker input chunk.start chunk.stop
    tasks.map fun task ↦ task.get

/-- Deterministically combine chunk results from left to right. -/
@[noinline] def foldChunks (config : Config) (input : Array α) (init : β)
    (combine : β → β → β) (worker : Array α → Nat → Nat → β) : β :=
  (mapChunks config input worker).foldl combine init

/--
Preferred effectful surface: eagerly start one `EIO` worker per chunk, preserve result order,
and propagate the first error after cooperatively cancelling the remaining tasks.

Long-running workers should poll `IO.checkCanceled` between bounded work units. This benchmark
does not pretend that cancellation can preempt an arbitrary pure inner loop.
-/
def traverseChunks (config : Config) (input : Array α)
    (worker : Array α → Nat → Nat → EIO ε β) : EIO ε (Array β) := do
  let chunks := chunkPlan input.size config
  if chunks.size ≤ 1 then
    let mut output := Array.emptyWithCapacity chunks.size
    for chunk in chunks do
      output := output.push (← worker input chunk.start chunk.stop)
    return output
  let mut tasks : Array (Task (Except ε β)) := Array.emptyWithCapacity chunks.size
  for chunk in chunks do
    let task ← liftM <|
      EIO.asTask (worker input chunk.start chunk.stop) config.scheduler.priority
    tasks := tasks.push task
  let mut output := Array.emptyWithCapacity tasks.size
  for task in tasks do
    match ← liftM <| IO.wait task with
    | .ok value => output := output.push value
    | .error error =>
        for pending in tasks do
          liftM <| IO.cancel pending
        for pending in tasks do
          discard <| liftM <| IO.wait pending
        throw error
  return output

@[inline] def mix (value : UInt64) : UInt64 :=
  let value := (value ^^^ (value >>> 27)) * 0x3C79AC492BA7B653
  (value ^^^ (value >>> 33)) * 0x1C69B3F74AC4AE35

def burn : Nat → UInt64 → UInt64
  | 0, value => value
  | rounds + 1, value => burn rounds (mix value + UInt64.ofNat rounds)

/-- Deliberately CPU-heavy, associative checksum over one array slice. -/
@[noinline] def checksumSlice (rounds : Nat) (input : Array UInt32)
    (start stop : Nat) : UInt64 :=
  let rec go : Nat → Nat → UInt64 → UInt64
    | 0, _, total => total
    | remaining + 1, index, total =>
        let value := UInt64.ofNat (input.getD index 0).toNat
        go remaining (index + 1) (total + burn rounds (value + UInt64.ofNat index))
  go (stop - start) start 0

@[noinline] def serialChecksum (rounds : Nat) (input : Array UInt32) : UInt64 :=
  checksumSlice rounds input 0 input.size

@[noinline] def parallelChecksum (config : Config) (rounds : Nat)
    (input : Array UInt32) : UInt64 :=
  foldChunks config input 0 (· + ·) (checksumSlice rounds)

@[noinline] def effectfulChecksum (config : Config) (rounds : Nat)
    (input : Array UInt32) : IO UInt64 := do
  let partials ← traverseChunks config input fun values start stop ↦
    pure <| checksumSlice rounds values start stop
  return partials.foldl (· + ·) 0

def bench (name : String) (repetitions : Nat) (input : IO.Ref (Array UInt32))
    (run : Array UInt32 → UInt64) : IO (UInt64 × Nat) := do
  let warmupRef ← IO.mkRef <| run (← input.get)
  let mut checksum ← warmupRef.get
  let start ← IO.monoNanosNow
  for _ in [0:repetitions] do
    checksum := checksum + run (← input.get)
  let stop ← IO.monoNanosNow
  let nanos := (stop - start) / repetitions
  IO.println s!"{name}\t{nanos / 1000} us/run\tchk={checksum}"
  return (checksum, nanos)

def benchIO (name : String) (repetitions : Nat) (input : IO.Ref (Array UInt32))
    (run : Array UInt32 → IO UInt64) : IO (UInt64 × Nat) := do
  let mut checksum ← run (← input.get)
  let start ← IO.monoNanosNow
  for _ in [0:repetitions] do
    checksum := checksum + (← run (← input.get))
  let stop ← IO.monoNanosNow
  let nanos := (stop - start) / repetitions
  IO.println s!"{name}\t{nanos / 1000} us/run\tchk={checksum}"
  return (checksum, nanos)

def main : IO Unit := do
  let itemCount := 2000000
  let rounds := 32
  let input := Array.ofFn (n := itemCount) fun index ↦
    UInt32.ofNat ((index.val * 2654435761 + 17) % UInt32.size)
  let inputRef ← IO.mkRef input
  let hardware := (System.Platform.Internal.getHardwareConcurrency ()).toNat
  let maxWorkers := min (max hardware 1) 8
  IO.println s!"hardware threads={hardware}; items={itemCount}; rounds={rounds}"

  let expected := serialChecksum rounds input
  let (_, serialNanos) ← bench "serial" 3 inputRef (serialChecksum rounds)

  for workers in #[1, 2, 4, 8] do
    if workers ≤ maxWorkers then
      let config : Config :=
        { workers, minGrain := 65536, scheduler := .pooled }
      let plan := chunkPlan itemCount config
      let actual := parallelChecksum config rounds input
      if !validPlan itemCount plan || actual != expected then
        throw <| IO.userError s!"invalid result for {workers} workers: {repr plan}"
      let (_, nanos) ← bench s!"Task.spawn default x{workers}" 3 inputRef
        (parallelChecksum config rounds)
      let speedup := Float.ofNat serialNanos / Float.ofNat nanos
      IO.println s!"  speedup={speedup}x chunks={plan.size}"

  for workers in #[2, 4, 8] do
    if workers ≤ maxWorkers then
      let config : Config :=
        { workers, minGrain := 65536, scheduler := .dedicated }
      let actual := parallelChecksum config rounds input
      if actual != expected then
        throw <| IO.userError s!"dedicated-worker x{workers} result disagreed with serial"
      let (_, nanos) ← bench s!"Task.spawn dedicated x{workers}" 3 inputRef
        (parallelChecksum config rounds)
      let speedup := Float.ofNat serialNanos / Float.ofNat nanos
      IO.println s!"  speedup={speedup}x"

  let effectConfig : Config :=
    { workers := maxWorkers, minGrain := 65536, scheduler := .dedicated }
  let effectActual ← effectfulChecksum effectConfig rounds input
  if effectActual != expected then
    throw <| IO.userError "effectful traversal result disagreed with serial"
  let (_, effectNanos) ← benchIO s!"EIO dedicated x{maxWorkers}" 3 inputRef
    (effectfulChecksum effectConfig rounds)
  let effectSpeedup := Float.ofNat serialNanos / Float.ofNat effectNanos
  IO.println s!"  speedup={effectSpeedup}x"

  let tiny := Array.replicate 8 (1 : UInt32)
  let tinyRef ← IO.mkRef tiny
  let tinyConfig : Config :=
    { workers := 8, minGrain := 1, scheduler := .dedicated }
  IO.println "--- task-boundary floor (eight trivial items) ---"
  discard <| bench "serial tiny" 1000 tinyRef (serialChecksum 0)
  discard <| bench "dedicated x8 tiny" 50 tinyRef (parallelChecksum tinyConfig 0)

end ParallelBenchmark

def main : IO Unit := ParallelBenchmark.main
