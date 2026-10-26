import JuliaLean.Tasks.TaskModel

namespace JuliaLean.Tasks

/-- Default worker count from `base/asyncmap.jl:116-129`. Naturals model the
accepted nonnegative integer `ntasks` values. -/
def normalizedNTasks (length ntasks : Nat) : Nat :=
  if ntasks = 0 then max 1 (min 100 length) else ntasks

/-- Initial worker count when `ntasks` is a function,
`base/asyncmap.jl:133-150`. Julia asserts an `Int`, changes zero to one, then
iterates `1:nt`; that range is empty for a negative result. -/
def dynamicWorkerCount (ntasks : Int) : Nat :=
  if ntasks = 0 then 1 else ntasks.toNat

/-- The documented zero-argument `ntasks` form should either reject its result
or start a worker, so a nonempty input does not block forever on the first
unbuffered-channel put. -/
def AsyncMapDynamicNTasksTerminates : Prop :=
  ∀ ntasks : Int, 0 < dynamicWorkerCount ntasks

theorem asyncMapDynamicNTasksTerminates_refuted : ¬ AsyncMapDynamicNTasksTerminates := by
  intro claimed
  have negative := claimed (-1)
  simp [dynamicWorkerCount] at negative

def validBatchSize : Option Nat → Bool
  | none => true
  | some n => 0 < n

abbrev ResultSlots := Nat → Option Nat

/-- Indexed assignment `results[i] = f(args...)`,
`base/asyncmap.jl:238-250`. Out-of-range jobs are ignored by this total model;
enumeration never generates them. -/
def asyncStore (f : Nat → Nat) (inputs : List Nat) (slots : ResultSlots)
    (index : Nat) : ResultSlots :=
  match inputs[index]? with
  | none => slots
  | some input => fun i => if i = index then some (f input) else slots i

/-- Apply indexed completions in an arbitrary order. Each order is one worker
interleaving, including interleavings made by batching. -/
def asyncRun (f : Nat → Nat) (inputs : List Nat) : List Nat → ResultSlots
  | [] => fun _ => none
  | index :: order => asyncStore f inputs (asyncRun f inputs order) index

/-- The full model keeps the public worker and batch parameters explicit.
They affect which completion orders are possible, while indexed writes make
the result at an input position independent of that order. -/
def asyncmapModel (f : Nat → Nat) (inputs : List Nat) (ntasks : Nat)
    (batchSize : Option Nat) (order : List Nat) : ResultSlots :=
  let _workers := normalizedNTasks inputs.length ntasks
  let _batch := batchSize
  asyncRun f inputs order

private theorem normalizedNTasks_pos (length ntasks : Nat) :
    0 < normalizedNTasks length ntasks := by
  unfold normalizedNTasks
  split <;> omega

private theorem asyncRun_correct (f : Nat → Nat) (inputs : List Nat)
    (order : List Nat) (index input : Nat) (atIndex : inputs[index]? = some input)
    (completed : index ∈ order) : asyncRun f inputs order index = some (f input) := by
  induction order with
  | nil => simp at completed
  | cons job order ih =>
      simp only [List.mem_cons] at completed
      by_cases same : job = index
      · subst job
        simp [asyncRun, asyncStore, atIndex]
      · have inRest : index ∈ order := completed.resolve_left (Ne.symm same)
        have correct := ih inRest
        simp only [asyncRun, asyncStore]
        cases hjob : inputs[job]? <;> simp [Ne.symm same, correct]

/-- For every accepted worker count, positive batch size, and completion
interleaving that contains an input index, the slot at that index contains
that input's mapped value. Reading slots from 1 through n therefore returns
results in input order (`base/asyncmap.jl:12,76-92,238-290`). -/
def AsyncMapOrdered : Prop :=
  ∀ (f : Nat → Nat) (inputs : List Nat) (ntasks : Nat) (batchSize : Option Nat)
      (order : List Nat),
    validBatchSize batchSize = true →
    (∀ index input, inputs[index]? = some input → index ∈ order) →
    ∀ index input, inputs[index]? = some input →
      0 < normalizedNTasks inputs.length ntasks ∧
      asyncmapModel f inputs ntasks batchSize order index = some (f input)

theorem asyncMapOrdered_proven : AsyncMapOrdered := by
  intro f inputs ntasks batchSize order _ complete index input atIndex
  exact ⟨normalizedNTasks_pos inputs.length ntasks,
    asyncRun_correct f inputs order index input atIndex (complete index input atIndex)⟩

end JuliaLean.Tasks
