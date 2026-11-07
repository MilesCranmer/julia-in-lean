import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.common.copy
import JuliaLean.Proofs.base.array.common.grow

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection

open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorWindows

/- Wrapped `Int` values are compared through the `ival_*` lemmas; unfolding `JInt.wrap` inside
arithmetic decision procedures is exponential. -/
attribute [local irreducible] JInt.wrap

theorem vwContents_last {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (xs : List (Option α))
    (v : Option α)
    (hxs : s.contents handle = xs ++ [v]) :
    n.val = xs.length + 1 ∧ (vwWindow slots off n)[(n.val - 1).toNat]? = some v := by
  have hl := vwWindow_length h
  rw [← h.contents, hxs] at hl
  simp only [List.length_append, List.length_singleton] at hl
  have hn0 := h.2.2.2.1
  refine ⟨by omega, ?_⟩
  rw [← h.contents, hxs, show (n.val - 1).toNat = xs.length by omega]
  simp

theorem vwContents_first {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (xs : List (Option α))
    (v : Option α)
    (hxs : s.contents handle = v :: xs) :
    n.val = xs.length + 1 ∧ (vwWindow slots off n)[((one : I).val - 1).toNat]? = some v := by
  have hl := vwWindow_length h
  rw [← h.contents, hxs] at hl
  simp only [List.length_cons] at hl
  have hn0 := h.2.2.2.1
  refine ⟨by omega, ?_⟩
  rw [← h.contents, hxs]
  simp [ival_one]

def PopSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (isempty : Nat → MutationM α Bool) (lastindex : Nat → MutationM α I),
    (∀ s h v, s.arrays[h]? = some v → (isempty h).run s = (.ok (v.size.val == 0), s)) →
    (∀ s h v, s.arrays[h]? = some v → (lastindex h).run s = (.ok v.size, s)) →
    ∀ (s : MutableMemory α) (handle : Nat), s.validVector handle →
      let back := (pop isempty lastindex mutableGet (deleteend (mutableStorage layout) pure) handle).run s
      let front := (popfirst isempty mutableGet (deletebeg (mutableStorage layout) pure) handle).run s
      (s.contents handle = [] →
        back = (.error (.argument "array must be non-empty"), s) ∧
        front = (.error (.argument "array must be non-empty"), s)) ∧
      (∀ xs : List (Option α), s.contents handle = xs ++ [none] →
        back = (.error .undefinedReference, s)) ∧
      (∀ (xs : List (Option α)) (x : α), s.contents handle = xs ++ [some x] →
        ∃ next, back = (.ok x, next) ∧ next.contents handle = xs ∧ next.validVector handle) ∧
      (∀ xs : List (Option α), s.contents handle = none :: xs →
        front = (.error .undefinedReference, s)) ∧
      (∀ (xs : List (Option α)) (x : α), s.contents handle = some x :: xs →
        ∃ next, front = (.ok x, next) ∧ next.contents handle = xs ∧ next.validVector handle)

def PushSpec : Prop :=
  ∀ (α β : Type) (l : DictLayout) (alreadyTyped : β → Bool) (asTyped : β → α)
    (conv : β → Except Error α) (s : MutableMemory α) (handle : Nat) (item : β),
    s.validVector handle →
    let boxed : DictLayout := boxedDictLayout
    let g := geometryOf s handle
    let run := (push alreadyTyped asTyped (fun x => stateExceptLift (conv x))
      (push1361 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableLength mutableSet) handle item).run s
    let runAny := fun x : α => (push1368 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime boxed)) pure
      (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime boxed)))) mutableLength mutableSet handle x).run s
    let value := if alreadyTyped item then .ok (asTyped item) else conv item
    let pushed := fun (x : α) (r : Nat) (next : MutableMemory α) =>
      r = handle ∧ next.validVector handle ∧ next.contents handle = s.contents handle ++ [some x]
    (∀ e, value = .error e → run = (.error e, s)) ∧
    (∀ x, value = .ok x → Follows s (growendPlan l g 1) run (pushed x)) ∧
    (∀ x, Follows s (growendPlan boxed g 1) (runAny x) (pushed x))

theorem list_set_first (l xs : List β) (v : β) (hl : l.length = xs.length + 1)
    (hd : l.drop 1 = xs) : l.set 0 v = v :: xs := by
  match l, hl with
  | y :: ys, _ => simp only [List.set_cons_zero, List.drop_succ_cons, List.drop_zero] at hd ⊢; rw [hd]

/-- `_pushfirst!` on a valid vector whose memory can grow by three slots. -/
def PushfirstSpec : Prop :=
  ∀ (α β : Type) (l : DictLayout) (alreadyTyped : β → Bool) (asTyped : β → α)
    (conv : β → Except Error α) (s : MutableMemory α) (handle : Nat) (item : β),
    s.validVector handle →
    let boxed : DictLayout := boxedDictLayout
    let g := geometryOf s handle
    let run := (pushfirst alreadyTyped asTyped (fun x => stateExceptLift (conv x))
      (pushfirst1777 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableSet) handle item).run s
    let runAny := fun x : α => (pushfirst1784 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime boxed)) pure
      (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime boxed)))) mutableSet handle x).run s
    let value := if alreadyTyped item then .ok (asTyped item) else conv item
    let pushed := fun (x : α) (r : Nat) (next : MutableMemory α) =>
      r = handle ∧ next.validVector handle ∧ next.contents handle = some x :: s.contents handle
    (∀ e, value = .error e → run = (.error e, s)) ∧
    (∀ x, value = .ok x → Follows s (growbegPlan l g 1) run (pushed x)) ∧
    (∀ x, Follows s (growbegPlan boxed g 1) (runAny x) (pushed x))

def DequeueSpec : Prop := PushSpec ∧ PushfirstSpec ∧ PopSpec
end VectorWindows
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `_growat!(a, i, delta)` (array.jl:1225), called by `insert!` and `splice!`: a negative
`delta` raises `ArgumentError` and an index outside `1:length(a)+1` raises `BoundsError`, both with
`a` untouched; otherwise `a` gets `delta` more slots opened before position `i`, `a[1:i-1]` staying
in place and `a[i:end]` following the new slots in order, in a valid vector, and no other array
header changes. The size precondition is that the memory length plus `2*delta + 1` is an `Int`, as
the checked growth arithmetic requires. -/

def InsertSpec : Prop :=
  ∀ (α β : Type) (l : DictLayout) (t : IntTy) (alreadyTyped : β → Bool) (asTyped : β → α)
    (conv : β → Except Error α) (s : MutableMemory α) (handle : Nat) (i : JInt t) (item : β),
    s.validVector handle →
    let w := s.contents handle
    let run := (insert alreadyTyped asTyped (fun x => stateExceptLift (conv x))
      (insertTyped (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) lengthToInt lengthToInt
          (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
          (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))))
        (fun a x j => do mutableSet a x (← lengthToInt j))) handle i item).run s
    let value := if alreadyTyped item then .ok (asTyped item) else conv item
    (∀ e, value = .error e → run = (.error e, s)) ∧
    (∀ x, value = .ok x →
      (¬ (IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max) → run = (.error .inexact, s)) ∧
      (IntTy.i64.min ≤ i.val → i.val ≤ IntTy.i64.max →
        Follows s (growatPlan l (geometryOf s handle) i.val 1) run (fun r next =>
          r = handle ∧ next.validVector handle ∧
          next.contents handle = w.take (i.val - 1).toNat ++ some x :: w.drop (i.val - 1).toNat)))

/-- `push!(a::Vector{Any}, x...)` and `pushfirst!(a::Vector{Any}, x...)` (array.jl:1373, 1789;
docstrings at array.jl:1325-1350 and 1753-1771): the values are appended after (respectively
inserted before) every old element, in argument order, and the vector stays valid. The size
precondition is that the memory length plus the number of values is an `Int` for `push!`, and
plus twice that number plus one for `pushfirst!`, as the checked growth arithmetic of
`_growbeg!` requires. -/

def PushManySpec : Prop :=
  ∀ (α : Type) (s : MutableMemory α) (handle : Nat) (xs : List α),
    s.validVector handle → xs.length ≤ typemaxNat →
    let boxed : DictLayout := boxedDictLayout
    let g := geometryOf s handle
    let back := (pushAnyMany mutableLength
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime boxed)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime boxed))))
      mutableSet handle xs).run s
    let front := (pushfirstAnyMany
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime boxed)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime boxed))))
      mutableSet handle xs).run s
    Follows s (growendPlan boxed g xs.length) back (fun r next => r = handle ∧
      next.validVector handle ∧ next.contents handle = s.contents handle ++ xs.map some) ∧
    Follows s (growbegPlan boxed g xs.length) front (fun r next => r = handle ∧
      next.validVector handle ∧ next.contents handle = xs.map some ++ s.contents handle)
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorSets

variable {α : Type} [DecidableEq α]

/-- `pop!(keep, x)`. -/
def setPop (_ : Unit) (x : α) : SetM α Unit :=
  modify fun st => { st with set := st.set.erase x }

/-- `push!(v, x)` on the tracked vector. -/
def vecPush (_ : Unit) (x : α) : SetM α Unit :=
  modify fun st => { st with vec := st.vec ++ [x] }
end VectorSets
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev vectorIsempty {α : Type} (h : Nat) : MutationM α Bool :=
  JuliaLean.base.abstractarray.isemptyArray mutableLength h

/-- `lastindex(a::AbstractArray) = last(eachindex(IndexLinear(), a))` (abstractarray.jl:429,
`lastindexArray`), with `eachindex(IndexLinear(), ::AbstractVector) = axes1(a)`
(abstractarray.jl:396, `eachindexLinearVector`), `axes1(a::Vector) = OneTo(length(a))` and
range.jl's `last(r::OrdinalRange)` (`last_OrdinalRange`, the `stop` field converted to the element
type). -/
def vectorLastindex {α : Type} (h : Nat) : MutationM α I := do
  let n ← mutableLength h
  let last := JuliaLean.base.abstractarray.lastindexArray
    (JuliaLean.base.abstractarray.eachindexLinearVector
      (fun n : I => (.ok ⟨n⟩ : JuliaLean.base.abstractarray.Result (JuliaLean.base.range.OneTo I))))
    (fun r => match JuliaLean.base.range.last_OrdinalRange (T := I) (A := I) r with
      | .ok v => .ok v
      | .error _ => .error (.julia .boundsError)) n
  match last with
  | .ok v => pure v
  | .error _ => throw .bounds

/-- `pop!(a::Vector)` and `popfirst!(a::Vector)` (array.jl:1695, 1831; docstrings at 1654-1694:
"Remove an item in `collection` and return it", and 1799-1830: "Remove the first `item` from
`collection`"), with `isempty`, `lastindex`, `a[end]`/`a[1]` and `_deleteend!`/`_deletebeg!` their
models: on an empty vector `ArgumentError("array must be non-empty")` with the store unchanged; an
unassigned end element raises `UndefRefError` with the store unchanged; otherwise the end element
is returned and removed, the others staying in order in a valid vector. -/
def PopSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (s : MutableMemory α) (handle : Nat), s.validVector handle →
    let back := (pop vectorIsempty vectorLastindex mutableGet (deleteend (mutableStorage layout) pure)
      handle).run s
    let front := (popfirst vectorIsempty mutableGet (deletebeg (mutableStorage layout) pure) handle).run s
    (s.contents handle = [] →
      back = (.error (.argument "array must be non-empty"), s) ∧
      front = (.error (.argument "array must be non-empty"), s)) ∧
    (∀ xs : List (Option α), s.contents handle = xs ++ [none] →
      back = (.error .undefinedReference, s)) ∧
    (∀ (xs : List (Option α)) (x : α), s.contents handle = xs ++ [some x] →
      ∃ next, back = (.ok x, next) ∧ next.contents handle = xs ∧ next.validVector handle) ∧
    (∀ xs : List (Option α), s.contents handle = none :: xs →
      front = (.error .undefinedReference, s)) ∧
    (∀ (xs : List (Option α)) (x : α), s.contents handle = some x :: xs →
      ∃ next, front = (.ok x, next) ∧ next.contents handle = xs ∧ next.validVector handle)

def DequeueSpec : Prop :=
  ∀ (α β : Type) (l : DictLayout) (alreadyTyped : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (s : MutableMemory α) (handle : Nat) (x : β),
    s.validVector handle →
    let g := geometryOf s handle
    let stored := if alreadyTyped x then .ok (asTyped x) else convert x
    let pushBack : MutationM α Nat := JuliaLean.base.array.push alreadyTyped asTyped
      (fun x => stateExceptLift (convert x))
      (push1361 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableLength mutableSet) handle x
    let pushFront : MutationM α Nat := pushfirst alreadyTyped asTyped
      (fun x => stateExceptLift (convert x))
      (pushfirst1777 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableSet) handle x
    let backRound : MutationM α α := do
      let _ ← pushBack
      pop vectorIsempty vectorLastindex mutableGet (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) handle
    let frontRound : MutationM α α := do
      let _ ← pushFront
      popfirst vectorIsempty mutableGet (deletebeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) handle
    let restored := fun (y r : α) (next : MutableMemory α) =>
      r = y ∧ next.validVector handle ∧ next.contents handle = s.contents handle
    (∀ e, stored = .error e → pushBack.run s = (.error e, s) ∧ pushFront.run s = (.error e, s)) ∧
    (∀ y, stored = .ok y →
      Follows s (growendPlan l g 1) (backRound.run s) (restored y) ∧
      Follows s (growbegPlan l g 1) (frontRound.run s) (restored y))

private theorem vectorLastindexRun {α : Type} (s : MutableMemory α) (handle mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s handle mem off n slots) :
    (vectorLastindex handle).run s = (.ok n, s) := by
  simp [vectorLastindex, JuliaLean.base.abstractarray.lastindexArray,
    JuliaLean.base.abstractarray.eachindexLinearVector, JuliaLean.base.range.last_OrdinalRange,
    JuliaLean.base.range.JFieldStop.stop, JuliaLean.Proofs.base.range.convert_self,
    stateExcept_bind, stateExcept_pure, stateExcept_throw,
    mutableLength_run s handle _ h.1, Except.bind, Except.pure]

theorem popSpec : PopSpec := by
  intro α layout s handle hvalid
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvalid
  have hc := hv.contents
  have hwl := vwWindow_length hv
  have hlen : (s.contents handle).length = n.val.toNat := by rw [hc]; exact hwl
  have hEmptyRun : (vectorIsempty handle).run s = (.ok (n.val == 0), s) := by
    simp only [vectorIsempty, JuliaLean.base.abstractarray.isemptyArray, stateExcept_bind,
      mutableLength_run s handle _ hv.1, stateExcept_pure]
  have hLastRun := vectorLastindexRun s handle mem off n slots hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnil
    have hnNat : n.val.toNat = 0 := by
      have h := hlen
      rw [hnil] at h
      simpa using h.symm
    have hnCast : (n.val.toNat : Int) = n.val :=
      Int.toNat_of_nonneg hv.2.2.2.1
    have hn : n.val = 0 := by
      have h := congrArg (fun z : Nat => (z : Int)) hnNat
      rw [hnCast] at h
      exact h
    simp [pop, popfirst, stateExcept_bind, stateExcept_pure, stateExcept_throw,
      hEmptyRun, hn]
  · intro xs hxs
    obtain ⟨hn, hslot⟩ := vwContents_last hv xs none hxs
    have hindex : (n.val - 1).toNat = n.val.toNat - 1 := by omega
    have hread : (mutableGet handle n).run s = (.error .undefinedReference, s) := by
      rw [vwGet_run s handle mem off n slots hv n ⟨by omega, Int.le_refl _⟩]
      rw [hindex] at hslot
      simp [hslot]
    have hnonzero : n.val ≠ 0 := by omega
    have hfalse : (n.val == 0) = false := by simp [hnonzero]
    simp [pop, stateExcept_bind, stateExcept_pure, stateExcept_throw,
      hEmptyRun, hfalse, hLastRun, hread]
  · intro xs x hxs
    obtain ⟨hn, hslot⟩ := vwContents_last hv xs (some x) hxs
    have hindex : (n.val - 1).toNat = n.val.toNat - 1 := by omega
    have hread : (mutableGet handle n).run s = (.ok x, s) := by
      rw [vwGet_run s handle mem off n slots hv n ⟨by omega, Int.le_refl _⟩]
      rw [hindex] at hslot
      simp [hslot]
    obtain ⟨next, slots', hdelete, hnext, _, _, hwindow⟩ :=
      vwDeleteend_run (layout := layout) s handle mem off n slots hv one
        (by simp) (by rw [ival_one]; omega)
        (by have hnb := ival_bounds n; rw [ival_one]; omega)
    have hdeleteMap :
        (Except.map (fun (_ : Unit) => x) <$> (deleteend (mutableStorage layout) pure handle one).run) s =
          (.ok x, next) := by
      change (Except.map (fun (_ : Unit) => x) ((deleteend (mutableStorage layout) pure handle one).run s).1,
        ((deleteend (mutableStorage layout) pure handle one).run s).2) = _
      rw [hdelete]
      rfl
    have hcontents : next.contents handle = xs := by
      have hnat : n.val.toNat = xs.length + 1 := by
        have h := hwl
        rw [← hc, hxs] at h
        simp at h
        omega
      rw [hnext.contents, hwindow, ← hc, hxs, ival_one]
      simp [List.take_append, hnat]
    have hnonzero : n.val ≠ 0 := by omega
    have hfalse : (n.val == 0) = false := by simp [hnonzero]
    refine ⟨next, ?_, hcontents, hnext.valid⟩
    simp [pop, stateExcept_bind, stateExcept_pure, stateExcept_throw, mutation_map_run,
      hEmptyRun, hfalse, hLastRun, hread, hdeleteMap]
  · intro xs hxs
    obtain ⟨hn, hslot⟩ := vwContents_first hv xs none hxs
    have hslot' : (vwWindow slots off n)[0]? = some none := by
      simpa [ival_one] using hslot
    have hread : (mutableGet handle one).run s = (.error .undefinedReference, s) := by
      rw [vwGet_run s handle mem off n slots hv one
        ⟨by rw [ival_one]; omega, by rw [ival_one]; omega⟩]
      simp [hslot']
    have hnonzero : n.val ≠ 0 := by omega
    have hfalse : (n.val == 0) = false := by simp [hnonzero]
    simp [popfirst, stateExcept_bind, stateExcept_pure, stateExcept_throw,
      hEmptyRun, hfalse, hread]
  · intro xs x hxs
    obtain ⟨hn, hslot⟩ := vwContents_first hv xs (some x) hxs
    have hslot' : (vwWindow slots off n)[0]? = some (some x) := by
      simpa [ival_one] using hslot
    have hread : (mutableGet handle one).run s = (.ok x, s) := by
      rw [vwGet_run s handle mem off n slots hv one
        ⟨by rw [ival_one]; omega, by rw [ival_one]; omega⟩]
      simp [hslot']
    obtain ⟨next, off', slots', hdelete, hnext, _, _, hwindow⟩ :=
      vwDeletebeg_run (layout := layout) s handle mem off n slots hv one
        (by rw [ival_one]; omega) (by rw [ival_one]; omega)
    have hdeleteMap :
        (Except.map (fun (_ : Unit) => x) <$> (deletebeg (mutableStorage layout) pure handle one).run) s =
          (.ok x, next) := by
      change (Except.map (fun (_ : Unit) => x) ((deletebeg (mutableStorage layout) pure handle one).run s).1,
        ((deletebeg (mutableStorage layout) pure handle one).run s).2) = _
      rw [hdelete]
      rfl
    have hcontents : next.contents handle = xs := by
      rw [hnext.contents, hwindow, ← hc, hxs, ival_one]
      simp
    have hnonzero : n.val ≠ 0 := by omega
    have hfalse : (n.val == 0) = false := by simp [hnonzero]
    refine ⟨next, ?_, hcontents, hnext.valid⟩
    simp [popfirst, stateExcept_bind, stateExcept_pure, stateExcept_throw,
      hEmptyRun, hfalse, hread, hdeleteMap]
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round7
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4

/-- The source allocation invariant shared by ordinary and externally wrapped live memories. -/
def LiveMemorySize (s : MutableMemory α) (a : Nat) : Prop :=
  ∀ vector slots, s.arrays[a]? = some vector → s.memories[vector.reference.1]? = some slots →
    slots.length < maxIntVal

/-- `default` is used only when the numeric range test fails. In-range Bool indexing still fails
before deletion, and an undefined slot raises before mutation. -/
def PopatSpec : Prop :=
  ∀ (α β : Type) (layout : MemoryLayoutMetadata) (ops : BigIntegerOps), ops.Lawful →
  ∀ (s : MutableMemory α) (a : Nat) (i : IntegerValue), s.validVector a → LiveMemorySize s a →
    let xs := s.contents a
    let remove := fun (a : Nat) (j : IntegerValue) (d : I) =>
      windowDelete α (layout := layout) ops a j (.ofInt d)
    let run := (popat (vectorGetInteger ops) remove a i).run s
    let withDefault := fun (fallback : β) =>
      (popatDefault mutableLength IntegerValue.val
        (fun a j => Sum.inl <$> vectorGetInteger ops a j) remove a i (Sum.inr fallback)).run s
    (i.isBool = true → ∃ message, run = (.error (.argument message), s)) ∧
    (¬i.validIndex xs.length → ∃ error, run = (.error error, s)) ∧
    (∀ fallback, ¬(1 ≤ i.val ∧ i.val ≤ (xs.length : Int)) →
      withDefault fallback = (.ok (Sum.inr fallback), s)) ∧
    (∀ fallback, i.isBool = true → 1 ≤ i.val → i.val ≤ (xs.length : Int) →
      ∃ message, withDefault fallback = (.error (.argument message), s)) ∧
    (i.validIndex xs.length → xs[(i.val - 1).toNat]? = some none →
      run = (.error .undefinedReference, s) ∧
      ∀ fallback, withDefault fallback = (.error .undefinedReference, s)) ∧
    (∀ value, i.validIndex xs.length → xs[(i.val - 1).toNat]? = some (some value) →
      (∃ after, run = (.ok value, after) ∧ after.validVector a ∧
        after.contents a = xs.eraseIdx (i.val - 1).toNat ∧
        ∀ other, other ≠ a → after.arrays[other]? = s.arrays[other]?) ∧
      ∀ fallback, ∃ after, withDefault fallback = (.ok (Sum.inl value), after) ∧
        after.validVector a ∧ after.contents a = xs.eraseIdx (i.val - 1).toNat ∧
        ∀ other, other ≠ a → after.arrays[other]? = s.arrays[other]?)
end round7
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
variable {α : Type}

/-- The push step as a `Follows` statement for the documented `push!` postcondition. -/
theorem push_follows (l : DictLayout) {s : MutableMemory α} {handle : Nat}
    (hvalid : s.validVector handle) (x : α) :
    Follows s (growendPlan l (geometryOf s handle) 1)
      ((push1361 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableLength mutableSet handle x).run s)
      (fun r next => r = handle ∧ next.validVector handle ∧
        next.contents handle = s.contents handle ++ [some x]) := by
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  rw [VecAt.geometry h]
  obtain ⟨herr, hok⟩ := push_plan l h x
  refine ⟨herr, fun g' hg' => ?_⟩
  obtain ⟨next, _, _, _, hrun, hv, _, _, hwin, _⟩ := hok g' hg'
  exact ⟨handle, next, hrun, rfl, hv.valid, by rw [hv.contents, hwin, h.contents]⟩

theorem pushSpec : PushSpec := by
  intro α β l alreadyTyped asTyped conv s handle item hvalid
  dsimp only
  refine ⟨fun e he => (push_value_error alreadyTyped asTyped conv _ s handle item e he).1,
    fun x hx => ?_, fun x => ?_⟩
  · rw [(push_value_ok alreadyTyped asTyped conv _ s handle item x hx).1]
    exact push_follows l hvalid x
  · exact push_follows boxedDictLayout hvalid x
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
variable {α : Type}

/-- `_pushfirst!(a, x)` (`_growbeg!(a, 1)`, then `a[1] = x`) on a valid vector follows
`growbegPlan l g 1`. -/
theorem pushfirst_plan (l : DictLayout) {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (x : α) :
    (∀ e, growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ 1 = .error e →
      (pushfirst1777 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableSet handle x).run s = (.error e, s)) ∧
    (∀ g', growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ 1 = .ok g' →
      ∃ next mem' off' slots',
        (pushfirst1777 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
          mutableSet handle x).run s = (.ok handle, next) ∧
        VecAt next handle mem' off' (n + one) slots' ∧
        vwWindow slots' off' (n + one) = some x :: vwWindow slots off n ∧
        geometryOf next handle = g') := by
  obtain ⟨herr, hok⟩ := growbeg_plan l h one (by rw [ival_one]; decide)
  rw [show one.val.toNat = 1 from rfl] at herr hok
  refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
  · simp only [pushfirst1777, stateExcept_bind, herr e he]
  · obtain ⟨next, mem', off', slots', hrun, hv, _, hnd, hwin, hgeo, _⟩ := hok g' hg'
    rw [ival_one] at hnd
    have hn0 := h.2.2.2.1
    have hset := vwSet_run next handle mem' off' (n + one) slots' hv one
      ⟨by rw [ival_one]; omega, by rw [ival_one]; omega⟩ x
    refine ⟨_, mem', off', _, ?_, hv.set (off'.val - 1 + one.val - 1).toNat (some x), ?_, ?_⟩
    · simp only [pushfirst1777, stateExcept_bind, hrun, hset, stateExcept_pure]
    · rw [vwWindow_set _ _ _ _ _ hv.2.2.1 (by rw [ival_one]; omega)]
      rw [ival_one]
      exact list_set_first _ _ _ (by rw [vwWindow_length hv, hnd, vwWindow_length h]; omega) hwin
    · rw [VecAt.geometry (hv.set _ _), List.length_set, ← VecAt.geometry hv, hgeo]

theorem round4_lift_eq {σ β : Type} :
    (round4.stateExceptLift : Except Error β → ExceptT Error (StateM σ) β) = stateExceptLift := rfl

theorem dequeueSpec : round4.DequeueSpec := by
  intro α β l alreadyTyped asTyped convert s handle x hvalid
  dsimp only
  simp only [round4_lift_eq]
  refine ⟨fun e he => ⟨(push_value_error alreadyTyped asTyped convert _ s handle x e he).1,
    (push_value_error alreadyTyped asTyped convert _ s handle x e he).2⟩, fun y hy => ⟨?_, ?_⟩⟩
  · obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
    rw [VecAt.geometry h]
    obtain ⟨herr, hok⟩ := push_plan l h y
    have hpush := (push_value_ok alreadyTyped asTyped convert
      (push1361 (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableLength mutableSet) s handle x y hy).1
    refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
    · simp only [stateExcept_bind, hpush, herr e he]
    · obtain ⟨next, _, _, _, hrun, hv, _, _, hwin, _⟩ := hok g' hg'
      have hcont : next.contents handle = s.contents handle ++ [some y] := by
        rw [hv.contents, hwin, h.contents]
      obtain ⟨next2, hpop, hc2, hv2⟩ := (round4.popSpec α (MemoryLayoutMetadata.ofRuntime l) next handle hv.valid).2.2.1 _ y hcont
      exact ⟨y, next2, by simp only [stateExcept_bind, hpush, hrun]; exact hpop, rfl, hv2, hc2⟩
  · obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
    rw [VecAt.geometry h]
    obtain ⟨herr, hok⟩ := pushfirst_plan l h y
    have hpush := (push_value_ok alreadyTyped asTyped convert
      (pushfirst1777 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableSet) s handle x y hy).2
    refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
    · simp only [stateExcept_bind, hpush, herr e he]
    · obtain ⟨next, _, _, _, hrun, hv, hwin, _⟩ := hok g' hg'
      have hcont : next.contents handle = some y :: s.contents handle := by
        rw [hv.contents, hwin, h.contents]
      obtain ⟨next2, hpop, hc2, hv2⟩ :=
        (round4.popSpec α (MemoryLayoutMetadata.ofRuntime l) next handle hv.valid).2.2.2.2 _ y hcont
      exact ⟨y, next2, by simp only [stateExcept_bind, hpush, hrun]; exact hpop, rfl, hv2, hc2⟩
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {α : Type}

/-- The `@_safeindex for i = 1:nx; a[base+i] = x[i]; end` loop of `push!(a::Vector{Any}, x...)`
and `pushfirst!(a::Vector{Any}, x...)`: the values land in order after the slots `pre`. -/
theorem setLoop_run {handle mem : Nat} {off N : I} (idx : I → I) (base : Int) (hb0 : 0 ≤ base)
    (hidx : ∀ j : I, 1 ≤ j.val → base + j.val ≤ N.val → (idx j).val = base + j.val) :
    ∀ (xs : List α) (st : MutableMemory α) (slots : List (Option α)) (i : I)
      (pre suf : List (Option α)),
      VecAt st handle mem off N slots → vwWindow slots off N = pre ++ suf →
      (pre.length : Int) = base + i.val - 1 → 1 ≤ i.val → xs.length ≤ suf.length →
      ∃ r slots', (forIn xs i (fun x (r : I) => (do
            mutableSet handle x (idx r)
            pure (ForInStep.yield (r + one)) : MutationM α (ForInStep I)))).run st =
          (.ok r, { st with memories := st.memories.set mem slots' }) ∧
        VecAt { st with memories := st.memories.set mem slots' } handle mem off N slots' ∧
        vwWindow slots' off N = pre ++ xs.map some ++ suf.drop xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro st slots i pre suf h hw _ _ _
    have hself : st.memories.set mem slots = st.memories := by
      obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp h.2.1
      rw [← hv]; exact List.set_getElem_self hlt
    refine ⟨i, slots, ?_, ?_, by simpa using hw⟩
    · simp only [List.forIn_nil, stateExcept_pure, hself]
    · rw [hself]; exact h
  | cons x xs ih =>
    intro st slots i pre suf h hw hpre hi hlen
    have hl := vwWindow_length h
    rw [hw] at hl
    obtain ⟨y, suf', rfl⟩ : ∃ y suf', suf = y :: suf' := by
      cases suf with
      | nil => simp at hlen
      | cons y s => exact ⟨y, s, rfl⟩
    simp only [List.length_append, List.length_cons] at hl hlen
    have hn0 := h.2.2.2.1
    have hib := ival_bounds i
    have hNb := ival_bounds N
    have hp : (idx i).val = base + i.val := hidx i hi (by omega)
    have hset := vwSet_run st handle mem off N slots h (idx i)
      ⟨by rw [hp]; omega, by rw [hp]; omega⟩ x
    have hw1 : vwWindow (slots.set (off.val - 1 + (idx i).val - 1).toNat (some x)) off N =
        (pre ++ [some x]) ++ suf' := by
      rw [vwWindow_set _ _ _ _ _ h.2.2.1 (by rw [hp]; omega), hw, hp,
        show (base + i.val - 1).toNat = pre.length by omega]
      simp
    have hv1 := h.set (off.val - 1 + (idx i).val - 1).toNat (some x)
    cases xs with
    | nil =>
      refine ⟨i + one, slots.set (off.val - 1 + (idx i).val - 1).toNat (some x), ?_, hv1, ?_⟩
      · simp only [List.forIn_cons, List.forIn_nil, stateExcept_bind, hset, stateExcept_pure]
      · rw [hw1]; simp
    | cons z zs =>
      have hi1 : (i + one).val = i.val + 1 := ival_add_one i (by
        simp only [List.length_cons] at hlen; omega)
      obtain ⟨r, slots2, hrun2, hv2, hw2⟩ := ih _ _ (i + one) (pre ++ [some x]) suf' hv1 hw1
        (by simp only [List.length_append, List.length_singleton]; push_cast; rw [hi1]; omega)
        (by rw [hi1]; omega) (by simp only [List.length_cons] at hlen ⊢; omega)
      simp only [List.set_set] at hrun2 hv2
      refine ⟨r, slots2, ?_, hv2, ?_⟩
      · rw [List.forIn_cons]
        simp only [stateExcept_bind, hset, stateExcept_pure]
        exact hrun2
      · rw [hw2]; simp
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem pushAnyMany_eq {m : Type → Type} [Monad m] {A β : Type} (length : A → m I)
    (growend : A → I → m Unit) (set : A → β → I → m Unit) (a : A) (xs : List β) :
    pushAnyMany length growend set a xs = (do
      let na ← length a
      growend a (JInt.wrap .i64 xs.length)
      let _ ← forIn xs one (fun x (r : I) => do
        set a x (na + r)
        pure (ForInStep.yield (r + one)))
      pure a) := rfl

theorem pushfirstAnyMany_eq {m : Type → Type} [Monad m] {A β : Type}
    (growbeg : A → I → m Unit) (set : A → β → I → m Unit) (a : A) (xs : List β) :
    pushfirstAnyMany growbeg set a xs = (do
      growbeg a (JInt.wrap .i64 xs.length)
      let _ ← forIn xs one (fun x (r : I) => do
        set a x r
        pure (ForInStep.yield (r + one)))
      pure a) := rfl

theorem pushAny_err {α : Type} (len : Nat → MutationM α I) (grow : Nat → I → MutationM α Unit)
    (set : Nat → α → I → MutationM α Unit) (s : MutableMemory α) (handle : Nat) (xs : List α)
    (na : I) (e : Error) (hl : (len handle).run s = (.ok na, s))
    (hg : (grow handle (JInt.wrap .i64 (xs.length : Int))).run s = (.error e, s)) :
    (pushAnyMany len grow set handle xs).run s = (.error e, s) := by
  rw [pushAnyMany_eq]
  simp only [stateExcept_bind, hl, hg]

theorem pushAny_ok {α : Type} (len : Nat → MutationM α I) (grow : Nat → I → MutationM α Unit)
    (set : Nat → α → I → MutationM α Unit) (s next : MutableMemory α) (final : MutableMemory α)
    (handle : Nat) (xs : List α) (na r : I) (hl : (len handle).run s = (.ok na, s))
    (hg : (grow handle (JInt.wrap .i64 (xs.length : Int))).run s = (.ok (), next))
    (hloop : (forIn xs one (fun x (r : I) => (do
        set handle x (na + r)
        pure (ForInStep.yield (r + one)) : MutationM α (ForInStep I)))).run next = (.ok r, final)) :
    (pushAnyMany len grow set handle xs).run s = (.ok handle, final) := by
  rw [pushAnyMany_eq]
  simp only [stateExcept_bind, hl, hg, hloop, stateExcept_pure]

theorem pushfirstAny_err {α : Type} (grow : Nat → I → MutationM α Unit)
    (set : Nat → α → I → MutationM α Unit) (s : MutableMemory α) (handle : Nat) (xs : List α)
    (e : Error) (hg : (grow handle (JInt.wrap .i64 (xs.length : Int))).run s = (.error e, s)) :
    (pushfirstAnyMany grow set handle xs).run s = (.error e, s) := by
  rw [pushfirstAnyMany_eq]
  simp only [stateExcept_bind, hg]

theorem pushfirstAny_ok {α : Type} (grow : Nat → I → MutationM α Unit)
    (set : Nat → α → I → MutationM α Unit) (s next final : MutableMemory α)
    (handle : Nat) (xs : List α) (r : I)
    (hg : (grow handle (JInt.wrap .i64 (xs.length : Int))).run s = (.ok (), next))
    (hloop : (forIn xs one (fun x (r : I) => (do
        set handle x r
        pure (ForInStep.yield (r + one)) : MutationM α (ForInStep I)))).run next = (.ok r, final)) :
    (pushfirstAnyMany grow set handle xs).run s = (.ok handle, final) := by
  rw [pushfirstAnyMany_eq]
  simp only [stateExcept_bind, hg, hloop, stateExcept_pure]

theorem pushMany_back {α : Type} (s : MutableMemory α) (handle : Nat) (xs : List α)
    (hvalid : s.validVector handle) (hlen : xs.length ≤ typemaxNat) :
    Follows s (growendPlan boxedDictLayout (geometryOf s handle) xs.length)
      ((pushAnyMany mutableLength
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime boxedDictLayout)) pure
          (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime boxedDictLayout))))
        mutableSet handle xs).run s) (fun r next => r = handle ∧
      next.validVector handle ∧ next.contents handle = s.contents handle ++ xs.map some) := by
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  rw [VecAt.geometry h]
  have hn0 := h.2.2.2.1
  have hnx : (JInt.wrap .i64 (xs.length : Int)).val = xs.length :=
    ival_wrap _ (by unfold typemaxNat at hlen; omega)
  have hnxN : (JInt.wrap .i64 (xs.length : Int)).val.toNat = xs.length := by rw [hnx]; omega
  have hold := vwWindow_length h
  obtain ⟨herr, hok⟩ := growend_plan boxedDictLayout h (JInt.wrap .i64 xs.length)
    (by rw [hnx]; omega)
  rw [hnxN] at herr hok
  refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
  · exact pushAny_err _ _ _ s handle xs _ e (mutableLength_run s handle _ h.1) (herr e he)
  · obtain ⟨next, mem', off', slots', hrun, hv, _, hnd, hwin, _⟩ := hok g' hg'
    have hl' := vwWindow_length hv
    obtain ⟨r, slots2, hloop, hv2, hw2⟩ := setLoop_run (handle := handle) (mem := mem')
      (off := off') (N := n + JInt.wrap .i64 xs.length) (fun r => n + r) n.val hn0
      (by
        intro j _ _
        have := ival_bounds (n + JInt.wrap .i64 xs.length)
        exact ival_add _ _ (by omega))
      xs next slots' one (vwWindow slots off n)
      ((vwWindow slots' off' (n + JInt.wrap .i64 xs.length)).drop n.val.toNat) hv
      (by rw [← hwin, List.take_append_drop])
      (by rw [hold, ival_one]; omega) (by rw [ival_one]; decide)
      (by rw [List.length_drop, hl', hnd, hnx]; omega)
    refine ⟨handle, _, ?_, rfl, hv2.valid, ?_⟩
    · exact pushAny_ok _ _ _ s next _ handle xs _ _ (mutableLength_run s handle _ h.1) hrun hloop
    · rw [hv2.contents, hw2, h.contents, List.drop_eq_nil_of_le (by
        rw [List.length_drop, hl', hnd, hnx]; omega)]
      simp

theorem pushMany_front {α : Type} (s : MutableMemory α) (handle : Nat) (xs : List α)
    (hvalid : s.validVector handle) (hlen : xs.length ≤ typemaxNat) :
    Follows s (growbegPlan boxedDictLayout (geometryOf s handle) xs.length)
      ((pushfirstAnyMany
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime boxedDictLayout)) pure
          (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime boxedDictLayout))))
        mutableSet handle xs).run s) (fun r next => r = handle ∧
      next.validVector handle ∧ next.contents handle = xs.map some ++ s.contents handle) := by
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  rw [VecAt.geometry h]
  have hn0 := h.2.2.2.1
  have hnx : (JInt.wrap .i64 (xs.length : Int)).val = xs.length :=
    ival_wrap _ (by unfold typemaxNat at hlen; omega)
  have hnxN : (JInt.wrap .i64 (xs.length : Int)).val.toNat = xs.length := by rw [hnx]; omega
  have hold := vwWindow_length h
  obtain ⟨herr, hok⟩ := growbeg_plan boxedDictLayout h (JInt.wrap .i64 xs.length)
    (by rw [hnx]; omega)
  rw [hnxN] at herr hok
  refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
  · exact pushfirstAny_err _ _ s handle xs e (herr e he)
  · obtain ⟨next, mem', off', slots', hrun, hv, _, hnd, hwin, _⟩ := hok g' hg'
    have hl' := vwWindow_length hv
    obtain ⟨r, slots2, hloop, hv2, hw2⟩ := setLoop_run (handle := handle) (mem := mem')
      (off := off') (N := n + JInt.wrap .i64 xs.length) (fun r => r) 0 (Int.le_refl 0)
      (by intro j _ _; simp)
      xs next slots' one [] (vwWindow slots' off' (n + JInt.wrap .i64 xs.length)) hv
      (by simp) (by simp [ival_one]) (by rw [ival_one]; decide)
      (by rw [hl', hnd, hnx]; omega)
    refine ⟨handle, _, ?_, rfl, hv2.valid, ?_⟩
    · exact pushfirstAny_ok _ _ s next _ handle xs _ hrun hloop
    · rw [hv2.contents, hw2, h.contents, hwin]
      simp


theorem pushManySpec : PushManySpec := by
  intro α s handle xs hvalid hlen
  exact ⟨pushMany_back s handle xs hvalid hlen, pushMany_front s handle xs hvalid hlen⟩
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4 JuliaLean.Proofs.base.array.round7
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 1000000


theorem arrayToIndex_valid (ops : BigIntegerOps) (hops : ops.Lawful) (i : IntegerValue)
    (n : Nat) (hn : (n : Int) < 9223372036854775807) (hi : i.validIndex n) :
    arrayToIndex ops i = .ok (JInt.wrap .i64 i.val) := by
  have hb : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := by
    have := hi.2
    change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807
    omega
  cases i with
  | bool b => simp [IntegerValue.validIndex, IntegerValue.isBool] at hi
  | big v =>
    simp only [IntegerValue.val] at hb
    simp [arrayToIndex, JuliaLean.base.indices.to_index_Integer, hops.1,
      IntegerValue.val, hb, indexError, Except.mapError]
  | bit t x =>
    simp only [IntegerValue.val] at hb
    cases t <;>
      simp [arrayToIndex, JuliaLean.base.indices.to_index_Array,
        JuliaLean.base.indices.to_index_A_i, JuliaLean.base.indices.to_index,
        JuliaLean.base.indices.to_index_Integer, JuliaLean.base.indices.convert_Int_BitInteger,
        JuliaLean.base.int.convert, JInt.convert, IntegerValue.val, hb, Except.mapError]
    all_goals apply Subtype.ext
    all_goals first
      | exact (ival_wrap _ hb).symm
      | exact JuliaLean.Proofs.base.int.bitcast_val .i64 x rfl

theorem arrayToIndex_value (ops : BigIntegerOps) (hops : ops.Lawful)
    (i : IntegerValue) (j : I) (hj : arrayToIndex ops i = .ok j) :
    i.isBool = false ∧ j.val = wrapInt .i64 i.val := by
  cases i with
  | bool b =>
    simp [arrayToIndex, JuliaLean.base.indices.to_index_Bool, Except.mapError] at hj
  | big v =>
    simp only [arrayToIndex, JuliaLean.base.indices.to_index_Integer, hops.1] at hj
    by_cases hb : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max
    · simp [hb, Except.mapError] at hj
      subst j
      exact ⟨rfl, rfl⟩
    · simp [hb, Except.mapError] at hj
  | bit t x =>
    have hx := x.property
    cases t <;>
      simp only [arrayToIndex, JuliaLean.base.indices.to_index_Array,
        JuliaLean.base.indices.to_index_A_i, JuliaLean.base.indices.to_index,
        JuliaLean.base.indices.to_index_Integer, JuliaLean.base.indices.convert_Int_BitInteger,
        JuliaLean.base.int.convert, JInt.convert] at hj
    all_goals first
      | (simp only [Except.mapError, Except.ok.injEq] at hj
         subst j
         exact ⟨rfl, JuliaLean.Proofs.base.int.bitcast_val .i64 x rfl⟩)
      | (split at hj
         next hb =>
           simp [Except.mapError] at hj
           subst j
           exact ⟨rfl, (wrapInt_of_inRange .i64 _ hb).symm⟩
         next hb => first | exact (hb hx).elim | simp [Except.mapError] at hj)

theorem arrayToIndex_sound (ops : BigIntegerOps) (hops : ops.Lawful)
    (i : IntegerValue) (j : I) (hj : arrayToIndex ops i = .ok j)
    (hj1 : 1 ≤ j.val) : i.isBool = false ∧ j.val = i.val := by
  obtain ⟨hbool, hv⟩ := arrayToIndex_value ops hops i j hj
  refine ⟨hbool, ?_⟩
  cases i with
  | bool b => contradiction
  | big v =>
    simp only [arrayToIndex, JuliaLean.base.indices.to_index_Integer, hops.1] at hj
    split at hj
    · rename_i hb
      simpa [IntegerValue.val, wrapInt_of_inRange .i64 _ hb] using hv
    · simp [Except.mapError] at hj
  | bit t x =>
    by_cases ht : t = .u64
    · subst t
      have hx := x.property
      have hm := JuliaLean.Proofs.base.int.wrapInt_emod_self .i64 x.val
      have jb := j.property
      simp only [IntegerValue.val] at hv
      rw [← hv] at hm
      change 0 ≤ x.val ∧ x.val ≤ 18446744073709551615 at hx
      change -9223372036854775808 ≤ j.val ∧ j.val ≤ 9223372036854775807 at jb
      change j.val % 18446744073709551616 = x.val % 18446744073709551616 at hm
      have hleft : j.val % 18446744073709551616 = j.val :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have hright : x.val % 18446744073709551616 = x.val :=
        Int.emod_eq_of_lt (by omega) (by omega)
      rw [hleft, hright] at hm
      exact hm
    · have hb : IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max := by
        by_cases hb : IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max
        · exact hb
        · cases t <;> first
          | exact (ht rfl).elim
          | exact (hb x.property).elim
          | simp [arrayToIndex, JuliaLean.base.indices.to_index_Array,
              JuliaLean.base.indices.to_index_A_i, JuliaLean.base.indices.to_index,
              JuliaLean.base.indices.to_index_Integer, JuliaLean.base.indices.convert_Int_BitInteger,
              JuliaLean.base.int.convert, JInt.convert, hb, Except.mapError] at hj
      simpa [IntegerValue.val, wrapInt_of_inRange .i64 _ hb] using hv

theorem integerToInt_ofInt (ops : BigIntegerOps) (hops : ops.Lawful) (x : I) :
    (integerToInt ops (.bit .i64 x) : MutationM α I) = pure x := by
  have hc : (IntegerValue.bit .i64 x).toInt ops = .ok x := by
    simp [IntegerValue.toInt, IntegerValue.convertTo, JuliaLean.base.int.convert,
      JInt.convert, x.property, Except.mapError]
  unfold integerToInt
  rw [hc]
  rfl

theorem add64_eq (x y : I) : JuliaLean.base.int.add x y = x + y := by
  apply Subtype.ext
  exact JuliaLean.Proofs.base.int.add_int_val x y

theorem sub64_eq (x y : I) : JuliaLean.base.int.sub x y = x - y := by
  apply Subtype.ext
  exact JuliaLean.Proofs.base.int.sub_int_val x y

theorem promote64_eq : IntTy.i64.promote .i64 = .i64 := rfl

theorem windowDelete_int (ops : BigIntegerOps) (hops : ops.Lawful)
    (a : Nat) (i : IntegerValue) (d : I) :
    (windowDelete α (layout := layout) ops a i (.ofInt d)) =
      (do let j ← integerToInt ops i; vecDeleteat α (layout := layout) a j d) := by
  unfold windowDelete vecDeleteat deleteatWindow
  simp only [IntegerValue.ofInt, IntegerValue.val, IntegerValue.addInt,
    IntegerValue.subFromInt, IntegerValue.subInt, IntegerValue.leInt,
    JuliaLean.base.int.binop, promote64_eq, JuliaLean.base.int.remT, JuliaLean.base.int.rem_same,
    dite_true, ite_true, integerToInt_ofInt ops hops, JuliaLean.Proofs.base.int.le_eq,
    add64_eq, sub64_eq]
  simp only [deletebeg, deleteend, integerToInt_ofInt ops hops]
  simp only [pure_bind, bind_assoc]
  rfl

theorem exceptState_map (f : β → γ) (action : ExceptT Error (StateM σ) β) (s : σ) :
    (f <$> action).run s = ((action.run s).1.map f, (action.run s).2) := by
  rw [map_eq_pure_bind, stateExcept_bind]
  rcases hr : action.run s with ⟨r, next⟩
  cases r <;> rfl

theorem integerLift_run (v : Except Error β) (s : σ) :
    (round4.stateExceptLift v).run s = (v, s) := rfl

theorem vectorGet_bool (ops : BigIntegerOps) (s : MutableMemory α) (a : Nat) (b : Bool) :
    (vectorGetInteger ops a (.bool b)).run s =
      (.error (.argument ("invalid index: " ++ toString b ++ " of type Bool")), s) := by
  rfl

theorem popatSpec : round7.PopatSpec := by
  intro α β layout ops hops s a i hvalid hsize
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  have hn0 := h.2.2.2.1
  have ho := h.2.2.1
  have he := h.2.2.2.2.1
  have hmax : slots.length < 9223372036854775807 := hsize _ _ h.1 h.2.1
  have hnmax : n.val < 9223372036854775807 := by omega
  have hlen : ((s.contents a).length : Int) = n.val := by
    rw [h.contents, vwWindow_length h]
    omega
  have hget (hi : i.validIndex (s.contents a).length) :
      (vectorGetInteger ops a i).run s =
        ((match (s.contents a)[(i.val - 1).toNat]? with
        | some (some value) => .ok value
        | _ => .error .undefinedReference), s) := by
    have hc := arrayToIndex_valid ops hops i (s.contents a).length (by omega) hi
    have hv : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ (by
      have := hi.2
      change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807
      omega)
    have hr := vwGet_run s a mem off n slots h (JInt.wrap .i64 i.val)
      (by rw [hv]; rw [← hlen]; exact hi.2)
    rw [hv, ← h.contents] at hr
    cases hs : (s.contents a)[(i.val - 1).toNat]? with
    | none => simpa only [vectorGetInteger, stateExcept_bind, integerLift_run, hc, hs] using hr
    | some value =>
      cases value <;> simpa only [vectorGetInteger, stateExcept_bind, integerLift_run, hc, hs] using hr
  have hremove (hi : i.validIndex (s.contents a).length) :
      ∃ after, (windowDelete α (layout := layout) ops a i (.ofInt one)).run s = (.ok (), after) ∧
        after.validVector a ∧ after.contents a = (s.contents a).eraseIdx (i.val - 1).toNat ∧
        ∀ other, other ≠ a → after.arrays[other]? = s.arrays[other]? := by
    have hb : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := by
      have := hi.2
      change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807
      omega
    have hv : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ hb
    obtain ⟨after, hrun, hval, hcontents, hframe⟩ := deleteOne_run s a mem off n slots h
      (JInt.wrap .i64 i.val) one (by rw [hv]; exact hi.2.1)
      (by rw [hv, ← hlen]; exact hi.2.2) ival_one
    refine ⟨after, ?_, hval, ?_, hframe⟩
    · rw [windowDelete_int ops hops]
      rw [stateExcept_bind, integerToInt_run, integerValue_toInt hops, if_pos hb]
      exact hrun
    · simp only [hv, ival_one] at hcontents
      rw [← h.contents] at hcontents
      rw [List.eraseIdx_eq_take_drop_succ, hcontents]
      rw [show (i.val - 1 + 1).toNat = (i.val - 1).toNat + 1 by have := hi.2.1; omega]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb
    cases i with
    | bit t x => simp [IntegerValue.isBool] at hb
    | big x => simp [IntegerValue.isBool] at hb
    | bool b =>
      refine ⟨"invalid index: " ++ toString b ++ " of type Bool", ?_⟩
      simp only [popat, stateExcept_bind, vectorGet_bool]
  · intro hi
    cases hc : arrayToIndex ops i with
    | error e =>
      refine ⟨e, ?_⟩
      simp only [popat, vectorGetInteger, stateExcept_bind, integerLift_run, hc]
    | ok j =>
      have hjout : j.val < 1 ∨ n.val < j.val := by
        by_cases hh : 1 ≤ j.val ∧ j.val ≤ n.val
        · obtain ⟨hb, hv⟩ := arrayToIndex_sound ops hops i j hc hh.1
          exact (hi ⟨hb, by omega, by omega⟩).elim
        · omega
      refine ⟨.bounds, ?_⟩
      simp only [popat, vectorGetInteger, stateExcept_bind, integerLift_run, hc,
        vwGet_outside s a _ h.1 j hjout]
  · intro fallback hout
    have hh : ¬ (1 ≤ i.val ∧ i.val ≤ n.val) := by rw [← hlen]; exact hout
    simp only [popatDefault, stateExcept_bind, mutableLength_run s a _ h.1, hh,
      ite_false, stateExcept_pure]
  · intro fallback hb hi1 hin
    have hh : 1 ≤ i.val ∧ i.val ≤ n.val := by rw [← hlen]; exact ⟨hi1, hin⟩
    cases i with
    | bit t x => simp [IntegerValue.isBool] at hb
    | big x => simp [IntegerValue.isBool] at hb
    | bool b =>
      refine ⟨"invalid index: " ++ toString b ++ " of type Bool", ?_⟩
      simp only [popatDefault, stateExcept_bind, mutableLength_run s a _ h.1, hh,
        and_self, ite_true, exceptState_map, vectorGet_bool, Except.map]
  · intro hi hnone
    have hr := hget hi
    rw [hnone] at hr
    have hh : 1 ≤ i.val ∧ i.val ≤ n.val := by rw [← hlen]; exact hi.2
    refine ⟨?_, fun fallback => ?_⟩
    · simp only [popat, stateExcept_bind, hr]
    · simp only [popatDefault, stateExcept_bind, mutableLength_run s a _ h.1, hh,
        and_self, ite_true, exceptState_map, hr, Except.map]
  · intro value hi hslot
    have hr := hget hi
    rw [hslot] at hr
    obtain ⟨after, hd, hv, hcs, hframe⟩ := hremove hi
    have hh : 1 ≤ i.val ∧ i.val ≤ n.val := by rw [← hlen]; exact hi.2
    refine ⟨⟨after, ?_, hv, hcs, hframe⟩, fun fallback => ⟨after, ?_, hv, hcs, hframe⟩⟩
    · simp only [popat, stateExcept_bind, hr, hd, stateExcept_pure]
    · simp only [popatDefault, stateExcept_bind, mutableLength_run s a _ h.1, hh,
        and_self, ite_true, exceptState_map, hr, Except.map, hd, stateExcept_pure]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 1000000
attribute [local irreducible] JInt.wrap

theorem pushfirst_native_follows (l : DictLayout) (s : MutableMemory α) (a mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots) (x : α) :
    Follows s (growbegPlan l (geometryOf s a) 1)
      ((pushfirst1777 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) mutableSet a x).run s)
      (fun r next => r = a ∧ next.validVector a ∧ next.contents a = some x :: s.contents a) := by
  rw [opusGrowth.VecAt.geometry h]
  obtain ⟨herr,hok⟩ := pushfirst_plan l h x
  refine ⟨herr,fun g hg => ?_⟩
  obtain ⟨after,mem',off',slots',hr,hv,hContents,_⟩ := hok g hg
  refine ⟨a,after,hr,rfl,hv.valid,?_⟩
  rw [hv.contents,hContents,← h.contents]

theorem pushfirstSpec : PushfirstSpec := by
  intro α β l alreadyTyped asTyped conv s a item hvalid
  dsimp only
  obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
  refine ⟨fun error he => ?_,fun x hx => ?_,fun x => ?_⟩
  · exact (push_value_error alreadyTyped asTyped conv
      (pushfirst1777 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) mutableSet) s a item error he).2
  · rw [(push_value_ok alreadyTyped asTyped conv
      (pushfirst1777 (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) mutableSet) s a item x hx).2]
    exact pushfirst_native_follows l s a mem off n slots h x
  · exact pushfirst_native_follows boxedDictLayout s a mem off n slots h x
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 3000000
attribute [local irreducible] JInt.wrap

theorem growat_convert_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadExceptOf Error m]
    (st : Storage m A Mem R) (toDelta : D → m I) (toIndex : Index → m I)
    (growb growe : A → I → m Unit) (a : A) (i : Index) (d : D) :
    growat st toDelta toIndex growb growe a i d =
      (do let delta ← toDelta d
          let index ← toIndex i
          growat st pure pure growb growe a index delta) := by
  simp only [growat,pure_bind,bind_assoc]

theorem lengthToInt_int (x : I) : (lengthToInt x : MutationM α I) = pure x := by
  have hc : (JuliaLean.base.int.convert .i64 x).mapError (fun _ => Error.inexact) = .ok x := by
    rw [bitinteger_array_conversion,if_pos x.property]
    apply congrArg Except.ok
    apply Subtype.ext
    exact ival_wrap _ x.property
  unfold lengthToInt
  rw [hc]
  rfl

theorem insertTyped_toInt_eq {t : IntTy} (l : DictLayout) (a : Nat) (i : JInt t) (x : α)
    (hi : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max) :
    insertTyped (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) lengthToInt lengthToInt
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))))
      (fun a x i => do mutableSet a x (← lengthToInt i)) a i x =
    insertTyped (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))))
      mutableSet a (JInt.wrap .i64 i.val) x := by
  have hiC : (lengthToInt i : MutationM α I) = pure (JInt.wrap .i64 i.val) := by
    unfold lengthToInt
    rw [bitinteger_array_conversion,if_pos hi]
    rfl
  unfold insertTyped
  rw [growat_convert_eq]
  simp only [lengthToInt_int,hiC,pure_bind,bind_assoc]

theorem insertTyped_toInt_error {t : IntTy} (l : DictLayout) (s : MutableMemory α)
    (a : Nat) (i : JInt t) (x : α) (hi : ¬ (IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max)) :
    (insertTyped (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) lengthToInt lengthToInt
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))))
      (fun a x i => do mutableSet a x (← lengthToInt i)) a i x).run s = (.error .inexact,s) := by
  have hiC : (lengthToInt i : MutationM α I) = throw .inexact := by
    unfold lengthToInt
    rw [bitinteger_array_conversion,if_neg hi]
    rfl
  unfold insertTyped
  rw [growat_convert_eq]
  simp only [lengthToInt_int,hiC,pure_bind,stateExcept_bind,stateExcept_throw]

theorem insert_native (l : DictLayout) (s : MutableMemory α) (a mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots) (i : I) (x : α) :
    Follows s (growatPlan l (geometryOf s a) i.val 1)
      ((insertTyped (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))))
        mutableSet a i x).run s)
      (fun r next => r = a ∧ next.validVector a ∧ next.contents a =
        (s.contents a).take (i.val-1).toNat ++ some x :: (s.contents a).drop (i.val-1).toNat) := by
  have H := growat_plan_native l s a mem off n slots h i one (by rw [ival_one]; decide)
  rw [show one.val.toNat = 1 from by rw [ival_one]; rfl] at H
  refine ⟨fun e he => ?_,fun g hg => ?_⟩
  · simp only [insertTyped,stateExcept_bind,H.1 e he]
  · have hi := growatPlan_ok_index l (geometryOf s a) i.val 1 g hg
    obtain ⟨result,grown,hGrow,hValid,hLen,hPre,hSuf,_⟩ := H.2 g hg
    cases result
    obtain ⟨mem',off',n',slots',hv⟩ := validVector_vecAt hValid
    have hLen' : n'.val = (s.contents a).length+1 := by
      rw [vecAt_length_int hv,ival_one] at hLen
      exact hLen
    have hi' : 1 ≤ i.val ∧ i.val ≤ n'.val := ⟨hi.1,by
      have hN : (geometryOf s a).length = (s.contents a).length := by
        rw [opusGrowth.VecAt.geometry h,h.contents,vwWindow_length h]
      rw [hN] at hi
      omega⟩
    have hp : (i.val-1).toNat < (grown.contents a).length := by
      have hN := vecAt_length_int hv
      have := hi'.1
      have := hi'.2
      omega
    have hpNext : (i.val-1).toNat+1 = i.val.toNat := by have := hi.1; omega
    have hSuf' : (grown.contents a).drop i.val.toNat = (s.contents a).drop (i.val-1).toNat := by
      simpa only [ival_one,Int.sub_add_cancel] using hSuf
    let after : MutableMemory α := {grown with memories := (grown.memories.set mem'
      (slots'.set (off'.val-1+i.val-1).toNat (some x)))}
    have ha : VecAt after a mem' off' n' (slots'.set (off'.val-1+i.val-1).toNat (some x)) := hv.set _ _
    refine ⟨a,after,?_,rfl,ha.valid,?_⟩
    · simp only [insertTyped,stateExcept_bind,hGrow,vwSet_run grown a mem' off' n' slots' hv i hi' x,
        stateExcept_pure]
      rfl
    · have hcontents : after.contents a = (grown.contents a).set (i.val-1).toNat (some x) := by
        rw [ha.contents,vwWindow_set slots' off' n' i (some x) hv.2.2.1 hi'.1,← hv.contents]
      rw [hcontents,list_set_splice _ _ _ hp,hpNext,hPre,hSuf',List.append_assoc,List.singleton_append]

theorem insert_value_error {α β Z : Type} (alreadyTyped : β → Bool) (asTyped : β → α)
    (conv : β → Except Error α) (put : Nat → Z → α → MutationM α Nat) (s : MutableMemory α)
    (a : Nat) (i : Z) (item : β) (error : Error)
    (h : (if alreadyTyped item then .ok (asTyped item) else conv item) = .error error) :
    (insert alreadyTyped asTyped (fun x => stateExceptLift (conv x)) put a i item).run s =
      (.error error,s) := by
  simpa only [JuliaLean.base.array.insert,JuliaLean.base.array.push] using
    (push_value_error alreadyTyped asTyped conv (fun a x => put a i x) s a item error h).1

theorem insert_value_ok {α β Z : Type} (alreadyTyped : β → Bool) (asTyped : β → α)
    (conv : β → Except Error α) (put : Nat → Z → α → MutationM α Nat) (s : MutableMemory α)
    (a : Nat) (i : Z) (item : β) (x : α)
    (h : (if alreadyTyped item then .ok (asTyped item) else conv item) = .ok x) :
    (insert alreadyTyped asTyped (fun x => stateExceptLift (conv x)) put a i item).run s =
      (put a i x).run s := by
  simpa only [JuliaLean.base.array.insert,JuliaLean.base.array.push] using
    (push_value_ok alreadyTyped asTyped conv (fun a x => put a i x) s a item x h).1

theorem insertSpec : InsertSpec := by
  intro α β l t alreadyTyped asTyped conv s a i item hvalid
  dsimp only
  let put : Nat → JInt t → α → MutationM α Nat :=
    insertTyped (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) lengthToInt lengthToInt
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))))
      (fun a x i => do mutableSet a x (← lengthToInt i))
  refine ⟨fun error he => ?_,fun x hx => ?_⟩
  · exact insert_value_error alreadyTyped asTyped conv put s a i item error he
  · have hValue := insert_value_ok alreadyTyped asTyped conv put s a i item x hx
    rw [hValue]
    change (¬ (IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max) →
      (put a i x).run s = (.error .inexact,s)) ∧ _
    refine ⟨fun hi => insertTyped_toInt_error l s a i x hi,fun hlo hhi => ?_⟩
    change Follows s (growatPlan l (geometryOf s a) i.val 1)
      ((insertTyped (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) lengthToInt lengthToInt
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))))
        (fun a x i => do mutableSet a x (← lengthToInt i)) a i x).run s) _
    rw [insertTyped_toInt_eq l a i x ⟨hlo,hhi⟩]
    obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
    have hi : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ ⟨hlo,hhi⟩
    simpa only [hi] using insert_native l s a mem off n slots h (JInt.wrap .i64 i.val) x
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion2
open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Completion2

/-- The variadic insertion method passes the original array and entire tuple to its selected append/prepend method once. -/
def PushManyArguments : Prop :=
  ∀ (A X : Type) (a : A) (values : List X) (initial : List Nat),
    (JuliaLean.base.array.Completion2.pushMany (fun a xs => call 0 (.ok (a, xs))) a values).run initial =
      (.ok (a, values), initial ++ [0])

/-- The variadic insertion method passes the original array and entire tuple to its selected append/prepend method once. -/
def PushfirstManyArguments : Prop :=
  ∀ (A X : Type) (a : A) (values : List X) (initial : List Nat),
    (JuliaLean.base.array.Completion2.pushfirstMany (fun a xs => call 0 (.ok (a, xs))) a values).run initial =
      (.ok (a, values), initial ++ [0])
end JuliaLean.Proofs.base.array.Completion2


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry

def PushContents : Prop := PushSpec ∧ PushfirstSpec ∧ PushManySpec

theorem pushContents : PushContents :=
  ⟨opusGrowth.pushSpec, solArrayGrow.pushfirstSpec, opusGrowth.pushManySpec⟩
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion2.PushManyArguments_proven : JuliaLean.Proofs.base.array.Completion2.PushManyArguments := by
  unfold JuliaLean.Proofs.base.array.Completion2.PushManyArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.pushMany, JuliaLean.base.array.pushMany, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.PushfirstManyArguments_proven : JuliaLean.Proofs.base.array.Completion2.PushfirstManyArguments := by
  unfold JuliaLean.Proofs.base.array.Completion2.PushfirstManyArguments
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.pushfirstMany, JuliaLean.base.array.pushfirstMany, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesPush1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-popat", juliaFile := "base/array.jl",
    juliaFns := ["popat!(::Vector, ::Integer)", "popat!(::Vector, ::Integer, default)"],
    statement := "popat! removes and returns the indexed item, shifts following items, and preserves other array headers. An out-of-range numeric index returns an independently typed default when supplied. An in-range Bool still raises ArgumentError; undefined slots raise UndefRefError before deletion. Existing backing Memory lengths obey their source allocation limits.",
    source := "base/array.jl:1704-1751", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round7.PopatSpec, thm := some ``JuliaLean.Proofs.base.array.solArrayGrow.popatSpec }
]
def entriesPush2 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-pop", juliaFile := "base/array.jl",
    juliaFns := ["pop!(::Vector)", "popfirst!(::Vector)"],
    statement := "`pop!(a::Vector)` and `popfirst!(a::Vector)` (array.jl:1695, 1831; docstrings at 1654-1694: \"Remove an item in `collection` and return it\", and 1799-1830: \"Remove the first `item` from `collection`\"), with `isempty`, `lastindex`, `a[end]`/`a[1]` and `_deleteend!`/`_deletebeg!` their models: on an empty vector `ArgumentError(\"array must be non-empty\")` with the store unchanged; an unassigned end element raises `UndefRefError` with the store unchanged; otherwise the end element is returned and removed, the others staying in order in a valid vector.",
    source := "base/array.jl:1695", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.PopSpec, thm := some ``JuliaLean.Proofs.base.array.round4.popSpec,
    notes := "" },
  { id := "array-push-append", juliaFile := "base/array.jl",
    juliaFns := ["push!(::Vector{T}, item)", "_push!(::Vector{T}, ::T)", "push!(::Vector{Any}, x)"],
    statement := "push!(a, item) appends convert(eltype(a), item) after every old element, which keep their order, in a valid vector, and a failing conversion propagates with a untouched; the memory length plus one must be an Int.",
    source := "base/array.jl:1325-1350 (docstring)",
    status := .proven, prop := ``PushSpec, thm := some ``opusGrowth.pushSpec}
]
def entriesPush3 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-pushfirst-convert", juliaFile := "base/array.jl",
    juliaFns := ["pushfirst!(a::Vector{T}, item) where T", "_pushfirst!(::Vector{T}, ::T)",
      "pushfirst!(::Vector{Any}, x)"],
    statement := "pushfirst!(a, item) inserts convert(eltype(a), item) before every old element, which keep their order, in a valid vector, and a failing conversion propagates with a untouched; the memory length plus three must be an Int.",
    source := "base/array.jl:1753-1771 (docstring),1772-1788",
    status := .proven, prop := ``PushfirstSpec, thm := some ``JuliaLean.Proofs.base.array.solArrayGrow.pushfirstSpec},
  { id := "arrayops-dequeue", juliaFile := "base/array.jl",
    juliaFns := ["push!(::Vector, x)", "pushfirst!(::Vector, x)", "pop!(::Vector)", "popfirst!(::Vector)"],
    statement := "The dequeue contract of array.jl's \"Dequeue functionality\" (push!, pop!, pushfirst!, popfirst!; docstrings at array.jl:1325-1350, 1654-1694, 1753-1771, 1799-1830) for an item of any type: the `Vector{T}` methods `push!(a, item)` and `pushfirst!(a, item)` (array.jl:1353, 1772) store `item` itself when it is already a `T` and otherwise `convert(T, item)` (user-extensible, a parameter with no law; \"convert first so we don't grow the array if the assignment won't work\"). When that conversion throws, both `push!` and `pushfirst!` raise its error with the store unchanged. Otherwise `push!(a, item)` followed by `pop!(a)` returns the stored value and leaves `a` with its old contents, and `pushfirst!(a, item)` followed by `popfirst!(a)` does the same at the front, in a valid vector. The precondition is that the memory can grow by one slot at either end.",
    source := "base/array.jl:1325-1350, array.jl:1353", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.DequeueSpec, thm := some ``opusGrowth.dequeueSpec,
    notes := "" }
]
def entriesPush4 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-insert", juliaFile := "base/array.jl",
    juliaFns := ["insert!(a::Array{T,1}, i::Integer, item) where T", "_insert!(a::Array{T,1}, i::Integer, item::T) where T"],
    statement := "insert!(a, i, item) for an index of any BitInteger type converts item first (errors propagate with a untouched), raises InexactError when i is not an Int value and BoundsError outside 1:length(a)+1 with a untouched, and otherwise puts the converted item at index i with the old elements before and after it in order.",
    source := "base/array.jl:1840-1872 (insert! docstring)", status := .proven, prop := ``InsertSpec, thm := some ``JuliaLean.Proofs.base.array.solArrayGrow.insertSpec },
  { id := "multidimcov-array-faithful-1794", juliaFile := "base/array.jl",
    juliaFns := ["push!(a::Vector{Any}, @nospecialize x...)", "pushfirst!(a::Vector{Any}, @nospecialize x...)"],
    statement := "push!(a::Vector{Any}, x...) appends the values after every old element and pushfirst!(a::Vector{Any}, x...) inserts them before, in argument order, in a valid vector.",
    source := "base/array.jl:1325-1350,1373-1386,1753-1771,1789-1797 (push!/pushfirst! docstrings)", status := .proven, prop := ``PushManySpec, thm := some ``opusGrowth.pushManySpec }
]
def entriesPush5 : List JuliaLean.Registry.Entry := [
{ id := "array-push-many-arguments", juliaFile := "base/array.jl",
  juliaFns := ["push!(a::AbstractVector, iter...)"],
  statement := "The variadic insertion method passes the original array and entire tuple to its selected append/prepend method once.",
  source := "base/array.jl:1431-1431", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.PushManyArguments, thm := some ``JuliaLean.Proofs.base.array.Completion2.PushManyArguments_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-pushfirst-many-arguments", juliaFile := "base/array.jl",
  juliaFns := ["pushfirst!(a::AbstractVector, iter...)"],
  statement := "The variadic insertion method passes the original array and entire tuple to its selected append/prepend method once.",
  source := "base/array.jl:1496-1496", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.PushfirstManyArguments, thm := some ``JuliaLean.Proofs.base.array.Completion2.PushfirstManyArguments_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry
def entriesPush6 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-push", juliaFile := "base/array.jl", juliaFns := ["push!(::Vector{T}, item)", "_push!(::Vector{T}, ::T)", "push!(::Vector{Any}, x)",
      "push!(::Vector{Any}, x...)", "_pushfirst!(::Vector{T}, ::T)", "pushfirst!(::Vector{Any}, x)",
      "pushfirst!(::Vector{Any}, x...)"],
    statement := "push! appends the converted items after every old element and pushfirst! puts them before, old elements keeping their order; a failing conversion propagates.", source := "docstrings base/array.jl:1330, 1757", status := .proven,
    prop := ``PushContents, thm := some ``pushContents }
]
end JuliaLean.Proofs.base.array.LegacyRetired

