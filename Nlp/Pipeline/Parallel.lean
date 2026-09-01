import Init.System.Platform
import Nlp.Pipeline.Runtime

/-!
# Bounded, ordered corpus concurrency

Planning is pure and independently testable. Execution eagerly starts coarse chunks on dedicated
threads, then collects results in chunk order. The observed error is therefore the first error in
chunk order, not necessarily the first one in wall-clock time.

Workers must call `NLP.checkCancelled` between bounded work units. Cancellation is cooperative and
cannot preempt an arbitrary pure inner loop.
-/

namespace Nlp.Parallel

/-- A half-open range `[start, stop)`. -/
structure Chunk where
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq, Inhabited

namespace Chunk

/-- Number of work items in a chunk. -/
@[inline] def length (chunk : Chunk) : Nat :=
  chunk.stop - chunk.start

end Chunk

/--
Clamp a requested worker count against the machine and the configured dedicated-thread ceiling.
Zero values mean "at least one", never "unbounded".
-/
@[inline] def boundedWorkers (requested hardware hardCap : Nat) : Nat :=
  min (max requested 1) <| min (max hardware 1) (max hardCap 1)

/-- Number of chunks selected by the worker and minimum-grain limits. -/
@[inline] def chunkCount (size workers minGrain : Nat) : Nat :=
  if size = 0 then
    0
  else
    let workers := max workers 1
    let grain := max minGrain 1
    let grainBound := max (size / grain) 1
    min workers grainBound

/-- Boundary after `index` balanced chunks. -/
@[inline] def chunkBoundary (size count index : Nat) : Nat :=
  index * (size / count) + min index (size % count)

/-- Formula for one balanced chunk. -/
@[inline] def chunkAt (size count index : Nat) : Chunk :=
  ⟨chunkBoundary size count index, chunkBoundary size count (index + 1)⟩

/-- Split work into balanced, contiguous, nonempty chunks, subject to a minimum coarse grain. -/
def chunkPlan (size workers minGrain : Nat) : Array Chunk :=
  let count := chunkCount size workers minGrain
  Array.ofFn (n := count) fun index ↦ chunkAt size count index

@[simp] theorem chunkBoundary_zero (size count : Nat) :
    chunkBoundary size count 0 = 0 := by
  simp [chunkBoundary]

/-- Adjacent formula chunks share exactly one boundary. -/
theorem chunkAt_adjacent (size count index : Nat) :
    (chunkAt size count index).stop = (chunkAt size count (index + 1)).start := by
  rfl

/-- The final balanced boundary covers the complete input. -/
theorem chunkBoundary_end (size count : Nat) (hcount : 0 < count) :
    chunkBoundary size count count = size := by
  have hmod : size % count ≤ count := Nat.le_of_lt <| Nat.mod_lt size hcount
  simpa [chunkBoundary, Nat.min_eq_right hmod] using Nat.div_add_mod size count

@[simp] theorem chunkPlan_size (size workers minGrain : Nat) :
    (chunkPlan size workers minGrain).size = chunkCount size workers minGrain := by
  simp [chunkPlan]

/-- Every executable-plan entry is the corresponding formula chunk. -/
theorem chunkPlan_get (size workers minGrain : Nat)
    (index : Fin (chunkCount size workers minGrain)) :
    (chunkPlan size workers minGrain)[index] =
      chunkAt size (chunkCount size workers minGrain) index := by
  simp [chunkPlan]

theorem chunkCount_pos (size workers minGrain : Nat) (hsize : 0 < size) :
    0 < chunkCount size workers minGrain := by
  simp only [chunkCount, if_neg (Nat.ne_of_gt hsize)]
  omega

theorem chunkPlan_size_pos (size workers minGrain : Nat) (hsize : 0 < size) :
    0 < (chunkPlan size workers minGrain).size := by
  simpa using chunkCount_pos size workers minGrain hsize

theorem chunkCount_le_size (size workers minGrain : Nat) (hsize : 0 < size) :
    chunkCount size workers minGrain ≤ size := by
  simp only [chunkCount, if_neg (Nat.ne_of_gt hsize)]
  have hdiv : size / max minGrain 1 ≤ size := Nat.div_le_self ..
  omega

theorem chunkCount_le_workers (size workers minGrain : Nat) :
    chunkCount size workers minGrain ≤ max workers 1 := by
  simp only [chunkCount]
  split
  · omega
  · exact Nat.min_le_left ..

theorem chunkCount_le_grainBound (size workers minGrain : Nat) :
    chunkCount size workers minGrain ≤ max (size / max minGrain 1) 1 := by
  simp only [chunkCount]
  split
  · omega
  · exact Nat.min_le_right ..

theorem chunkCount_le_div (size workers minGrain : Nat)
    (hmulti : 1 < chunkCount size workers minGrain) :
    chunkCount size workers minGrain ≤ size / max minGrain 1 := by
  have hbound := chunkCount_le_grainBound size workers minGrain
  have hquotient : 1 < size / max minGrain 1 := by
    omega
  simpa [Nat.max_eq_left (Nat.le_of_lt hquotient)] using hbound

/-- Multi-chunk plans meet the normalized minimum grain at the quotient level. -/
theorem minGrain_le_chunkQuotient (size workers minGrain : Nat)
    (hmulti : 1 < chunkCount size workers minGrain) :
    max minGrain 1 ≤ size / chunkCount size workers minGrain := by
  have hcount : 0 < chunkCount size workers minGrain := by omega
  have hgrain : 0 < max minGrain 1 := by omega
  have hcountDiv := chunkCount_le_div size workers minGrain hmulti
  have hproduct : chunkCount size workers minGrain * max minGrain 1 ≤ size :=
    (Nat.le_div_iff_mul_le hgrain).1 hcountDiv
  apply (Nat.le_div_iff_mul_le hcount).2
  simpa [Nat.mul_comm] using hproduct

/-- Boundaries strictly advance whenever the requested count fits the nonempty input. -/
theorem chunkBoundary_lt_succ (size count index : Nat) (hcount : 0 < count)
    (hfit : count ≤ size) :
    chunkBoundary size count index < chunkBoundary size count (index + 1) := by
  have hquotient : 0 < size / count := Nat.div_pos hfit hcount
  have hminimum : min index (size % count) ≤ min (index + 1) (size % count) := by
    omega
  simp only [chunkBoundary, Nat.add_mul, Nat.one_mul]
  omega

/-- Every boundary through `count` remains inside the input. -/
theorem chunkBoundary_le_size (size count index : Nat) (hindex : index ≤ count) :
    chunkBoundary size count index ≤ size := by
  have hproduct : index * (size / count) ≤ count * (size / count) :=
    Nat.mul_le_mul_right (size / count) hindex
  have hminimum : min index (size % count) ≤ size % count := Nat.min_le_right ..
  calc
    chunkBoundary size count index ≤ count * (size / count) + size % count := by
      simpa [chunkBoundary] using Nat.add_le_add hproduct hminimum
    _ = size := Nat.div_add_mod size count

/-- A selected formula chunk is nonempty and ends within the input. -/
theorem chunkAt_wf (size count index : Nat) (hcount : 0 < count)
    (hfit : count ≤ size) (hindex : index < count) :
    (chunkAt size count index).start < (chunkAt size count index).stop ∧
      (chunkAt size count index).stop ≤ size := by
  constructor
  · exact chunkBoundary_lt_succ size count index hcount hfit
  · exact chunkBoundary_le_size size count (index + 1) (by omega)

/-- Closed form for a chunk length: the first remainder chunks receive one extra item. -/
theorem chunkAt_length (size count index : Nat) :
    (chunkAt size count index).length =
      size / count + if index < size % count then 1 else 0 := by
  by_cases hextra : index < size % count
  · have hstart : min index (size % count) = index :=
      Nat.min_eq_left (Nat.le_of_lt hextra)
    have hstop : min (index + 1) (size % count) = index + 1 :=
      Nat.min_eq_left (by omega)
    simp only [Chunk.length, chunkAt, chunkBoundary]
    rw [hstart, hstop, if_pos hextra]
    simp only [Nat.add_mul, Nat.one_mul]
    have heq :
        index * (size / count) + size / count + (index + 1) =
          (index * (size / count) + index) + (size / count + 1) := by
      omega
    rw [heq, Nat.add_sub_self_left]
  · have hstart : min index (size % count) = size % count :=
      Nat.min_eq_right (Nat.le_of_not_gt hextra)
    have hstop : min (index + 1) (size % count) = size % count :=
      Nat.min_eq_right (by omega)
    simp only [Chunk.length, chunkAt, chunkBoundary]
    rw [hstart, hstop, if_neg hextra]
    simp only [Nat.add_mul, Nat.one_mul]
    have heq :
        index * (size / count) + size / count + size % count =
          (index * (size / count) + size % count) + size / count := by
      omega
    rw [heq, Nat.add_sub_self_left]
    simp

/-- Any two formula chunks differ in length by at most one. -/
theorem chunkAt_length_le_succ (size count left right : Nat) :
    (chunkAt size count left).length ≤ (chunkAt size count right).length + 1 := by
  rw [chunkAt_length, chunkAt_length]
  split <;> split <;> omega

/-- Every executable chunk has the short length or one extra item. -/
theorem chunkPlan_length_bounds (size workers minGrain : Nat)
    (index : Fin (chunkCount size workers minGrain)) :
    size / chunkCount size workers minGrain ≤
        (chunkPlan size workers minGrain)[index].length ∧
      (chunkPlan size workers minGrain)[index].length ≤
        size / chunkCount size workers minGrain + 1 := by
  rw [chunkPlan_get, chunkAt_length]
  split <;> omega

private theorem foldLengthBounds (chunks : Array Chunk) (base initial : Nat)
    (hinitial : base ≤ initial ∧ initial ≤ base + 1)
    (hall : ∀ index : Fin chunks.size,
      base ≤ chunks[index].length ∧ chunks[index].length ≤ base + 1) :
    let bounds := chunks.foldl
      (fun (shortest, longest) chunk ↦
        (min shortest chunk.length, max longest chunk.length))
      (initial, initial)
    base ≤ bounds.1 ∧ bounds.1 ≤ base + 1 ∧
      base ≤ bounds.2 ∧ bounds.2 ≤ base + 1 := by
  dsimp only
  let step : Nat × Nat → Chunk → Nat × Nat := fun bounds chunk ↦
    (min bounds.1 chunk.length, max bounds.2 chunk.length)
  let motive : Nat → Nat × Nat → Prop := fun _ bounds ↦
      base ≤ bounds.1 ∧ bounds.1 ≤ base + 1 ∧
        base ≤ bounds.2 ∧ bounds.2 ≤ base + 1
  change motive chunks.size (chunks.foldl step (initial, initial))
  apply Array.foldl_induction motive
  · omega
  · intro index bounds hbounds
    rcases bounds with ⟨shortest, longest⟩
    simp only [motive, step] at hbounds ⊢
    have hchunk := hall index
    omega

/-- The executable plan inherits the pairwise formula balance bound. -/
theorem chunkPlan_length_le_succ (size workers minGrain : Nat)
    (left right : Fin (chunkCount size workers minGrain)) :
    (chunkPlan size workers minGrain)[left].length ≤
      (chunkPlan size workers minGrain)[right].length + 1 := by
  rw [chunkPlan_get, chunkPlan_get]
  exact chunkAt_length_le_succ ..

/-- Every executable-plan entry is nonempty and lies within a nonempty input. -/
theorem chunkPlan_get_wf (size workers minGrain : Nat) (hsize : 0 < size)
    (index : Fin (chunkCount size workers minGrain)) :
    (chunkPlan size workers minGrain)[index].start <
        (chunkPlan size workers minGrain)[index].stop ∧
      (chunkPlan size workers minGrain)[index].stop ≤ size := by
  rw [chunkPlan_get]
  exact chunkAt_wf size (chunkCount size workers minGrain) index
    (chunkCount_pos size workers minGrain hsize)
    (chunkCount_le_size size workers minGrain hsize) index.isLt

/-- Adjacent executable-plan entries meet with no gap or overlap. -/
theorem chunkPlan_adjacent (size workers minGrain : Nat)
    (left right : Fin (chunkCount size workers minGrain))
    (hnext : right.val = left.val + 1) :
    (chunkPlan size workers minGrain)[left].stop =
      (chunkPlan size workers minGrain)[right].start := by
  rw [chunkPlan_get, chunkPlan_get]
  simpa [hnext] using
    chunkAt_adjacent size (chunkCount size workers minGrain) left.val

/-- Any final executable-plan entry reaches the full input boundary. -/
theorem chunkPlan_final_stop (size workers minGrain : Nat) (hsize : 0 < size)
    (last : Fin (chunkCount size workers minGrain))
    (hlast : last.val + 1 = chunkCount size workers minGrain) :
    (chunkPlan size workers minGrain)[last].stop = size := by
  rw [chunkPlan_get]
  simp only [chunkAt]
  rw [hlast]
  exact chunkBoundary_end size (chunkCount size workers minGrain) <|
    chunkCount_pos size workers minGrain hsize

/-- Every chunk in a multi-chunk executable plan meets the normalized minimum grain. -/
theorem chunkPlan_minGrain (size workers minGrain : Nat)
    (hmulti : 1 < chunkCount size workers minGrain)
    (index : Fin (chunkCount size workers minGrain)) :
    max minGrain 1 ≤ (chunkPlan size workers minGrain)[index].length := by
  rw [chunkPlan_get, chunkAt_length]
  have hquotient := minGrain_le_chunkQuotient size workers minGrain hmulti
  split <;> omega

/-
The formula above intentionally computes the shared quotient and remainder through `chunkAt`.
Chunk counts are bounded by dedicated-thread caps (normally at most eight), so this keeps the proof
surface direct without making planning material to corpus runtime.
-/

/-- Executable checker for contiguity, coverage, nonemptiness, and bounds. -/
def validPlan (size : Nat) (chunks : Array Chunk) : Bool := Id.run do
  let mut cursor := 0
  let mut valid := size == 0 || !chunks.isEmpty
  for chunk in chunks do
    valid := valid && chunk.start == cursor
    valid := valid && chunk.start < chunk.stop
    valid := valid && chunk.stop ≤ size
    cursor := chunk.stop
  return valid && cursor == size

/-- Executable checker that chunk lengths differ by at most one. -/
def balancedPlan (chunks : Array Chunk) : Bool :=
  match chunks[0]? with
  | none => true
  | some first =>
      let bounds := chunks.foldl
        (fun (shortest, longest) chunk ↦
          (min shortest chunk.length, max longest chunk.length))
        (first.length, first.length)
      bounds.2 ≤ bounds.1 + 1

@[simp] theorem balancedPlan_chunkPlan (size workers minGrain : Nat) :
    balancedPlan (chunkPlan size workers minGrain) = true := by
  let chunks := chunkPlan size workers minGrain
  let count := chunkCount size workers minGrain
  by_cases hempty : count = 0
  · simp [balancedPlan, chunkPlan, count, hempty]
  · have hcount : 0 < count := Nat.zero_lt_of_ne_zero hempty
    have hsize : 0 < chunks.size := by
      simpa [chunks, count] using hcount
    have hhead : chunks[0]? = some chunks[0] := Array.getElem?_eq_getElem hsize
    unfold balancedPlan
    rw [hhead]
    let base := size / count
    let bounds := chunks.foldl
      (fun (shortest, longest) chunk ↦
        (min shortest chunk.length, max longest chunk.length))
      (chunks[0].length, chunks[0].length)
    have hinitial : base ≤ chunks[0].length ∧ chunks[0].length ≤ base + 1 := by
      simpa [base, chunks, count] using
        chunkPlan_length_bounds size workers minGrain ⟨0, by simpa [count] using hcount⟩
    have hall : ∀ index : Fin chunks.size,
        base ≤ chunks[index].length ∧ chunks[index].length ≤ base + 1 := by
      intro index
      let planIndex : Fin count := ⟨index, by simpa [chunks, count] using index.isLt⟩
      simpa [base, chunks, count, planIndex] using
        chunkPlan_length_bounds size workers minGrain planIndex
    have hbounds := foldLengthBounds chunks base chunks[0].length hinitial hall
    change decide (bounds.2 ≤ bounds.1 + 1) = true
    simp only [decide_eq_true_eq]
    dsimp only [bounds]
    dsimp only [bounds] at hbounds
    omega

/-- Executable checker for the configured minimum grain on every multi-chunk plan. -/
def coarsePlan (minGrain : Nat) (chunks : Array Chunk) : Bool :=
  chunks.size ≤ 1 || chunks.all fun chunk ↦ max minGrain 1 ≤ chunk.length

@[simp] theorem coarsePlan_chunkPlan (size workers minGrain : Nat) :
    coarsePlan minGrain (chunkPlan size workers minGrain) = true := by
  by_cases hsmall : chunkCount size workers minGrain ≤ 1
  · have hsizesmall : (chunkPlan size workers minGrain).size ≤ 1 := by
      simpa using hsmall
    simp only [coarsePlan, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hsizesmall
  · have hmulti : 1 < chunkCount size workers minGrain := by omega
    simp only [coarsePlan, Bool.or_eq_true, decide_eq_true_eq]
    apply Or.inr
    rw [Array.all_eq_true]
    intro index hindex
    have hindex' : index < chunkCount size workers minGrain := by
      simpa using hindex
    simpa using
      chunkPlan_minGrain size workers minGrain hmulti ⟨index, hindex'⟩

/-- Executable checker for the worker-count ceiling. -/
def boundedPlan (workers : Nat) (chunks : Array Chunk) : Bool :=
  chunks.size ≤ max workers 1

@[simp] theorem boundedPlan_chunkPlan (size workers minGrain : Nat) :
    boundedPlan workers (chunkPlan size workers minGrain) = true := by
  simp [boundedPlan, chunkCount_le_workers]

@[simp] theorem chunkPlan_zero (workers minGrain : Nat) :
    chunkPlan 0 workers minGrain = #[] := by
  simp [chunkPlan, chunkCount]

/-- Read the machine limit once at the outer scheduling boundary. -/
@[inline] def hardwareConcurrency : Nat :=
  max (System.Platform.Internal.getHardwareConcurrency ()).toNat 1

/-- Worker count used by a top-level environment; nested traversals are forced serial. -/
@[inline] def workersFor (env : Env) : Nat :=
  if env.parallelDepth == 0 then
    boundedWorkers env.config.numThreads hardwareConcurrency env.config.maxDedicatedThreads
  else
    1

private structure Running (T : Type) where
  task : Task (Except Fail T)
  cancellation : Std.CancellationContext

/-- Signal both cancellation mechanisms and wait until every task has stopped. -/
private def cancelAndDrain (tasks : Array (Running T)) : BaseIO Unit := do
  for running in tasks do
    running.cancellation.cancel .cancel
    IO.cancel running.task
  for running in tasks do
    discard <| IO.wait running.task

/-- Release successful child contexts without changing their already-collected results. -/
private def releaseContexts (tasks : Array (Running T)) : BaseIO Unit := do
  for running in tasks do
    running.cancellation.cancel .cancel

/--
Apply one effectful worker to each coarse chunk and preserve chunk order in the result.

The array is shared read-only after tasks start. A multi-chunk traversal suppresses nested
parallelism in child environments. Every typed error cancels and drains every sibling before it is
re-thrown.
-/
def traverseChunks (input : Array α)
    (worker : Array α → Nat → Nat → NLP β) : NLP (Array β) := do
  NLP.checkCancelled
  let env ← read
  let chunks := chunkPlan input.size (workersFor env) env.config.parallelMinGrain
  if chunks.size ≤ 1 then
    let mut output := Array.emptyWithCapacity chunks.size
    for chunk in chunks do
      NLP.checkCancelled
      output := output.push (← worker input chunk.start chunk.stop)
    return output

  let mut running : Array (Running β) := Array.emptyWithCapacity chunks.size
  for chunk in chunks do
    let cancellation ← liftM <| env.cancellation.fork
    let childEnv := { env with
      cancellation
      parallelDepth := env.parallelDepth + 1
    }
    let action : EIO Fail β := do
      NLP.checkCancelled childEnv
      let result ← worker input chunk.start chunk.stop childEnv
      NLP.checkCancelled childEnv
      return result
    let task ← liftM <| EIO.asTask action Task.Priority.dedicated
    running := running.push ⟨task, cancellation⟩

  try
    let mut output := Array.emptyWithCapacity running.size
    for current in running do
      NLP.checkCancelled
      match ← liftM <| IO.wait current.task with
      | .ok value => output := output.push value
      | .error error => throw error
    liftM <| releaseContexts running
    return output
  catch error =>
    liftM <| cancelAndDrain running
    throw error

end Nlp.Parallel

namespace Nlp.NLP

/-- Preferred effectful facade for bounded, ordered chunk traversal. -/
@[inline] def traverseChunks (input : Array α)
    (worker : Array α → Nat → Nat → NLP β) : NLP (Array β) :=
  Nlp.Parallel.traverseChunks input worker

end Nlp.NLP
