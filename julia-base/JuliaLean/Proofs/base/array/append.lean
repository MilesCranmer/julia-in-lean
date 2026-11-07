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

def AppendManySnapshot : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (xs : List α) (sources : List (Option (List α))) (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs.map some →
    (∀ p ∈ sources.zipIdx, match p.1 with
      | none => True
      | some values => initial.validVector (p.2 + 1) ∧
          initial.contents (p.2 + 1) = values.map some) →
    xs.length < 2 ^ 62 →
    let handles := sources.zipIdx |>.map fun (source, i) => if source.isNone then 0 else i + 1
    let appendOne := fun (a source : Nat) => do
      let _ ← appendVector (m := MutationM α) (fun _ => false) pure mutableLength pure
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) mutableLength
        (fun _ => pure one) mutableCopyto a source
      pure ()
    let prependOne := fun (a source : Nat) => do
      let _ ← prependVector (m := MutationM α) (fun _ => false) pure
        (fun source a => source == a) (fun _ source => pure source)
        mutableLength (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        mutableLength mutableCopyto a source
      pure ()
    let afterAppend := (appendMany appendOne 0 handles).run initial
    let afterPrepend := (prependMany prependOne 0 handles).run initial
    (afterAppend.1 = .ok 0 ∧ afterAppend.2.contents =
      (xs ++ sources.flatMap (·.getD xs)).map some) ∧
    (afterPrepend.1 = .ok 0 ∧ afterPrepend.2.contents =
      (sources.flatMap (·.getD xs) ++ xs).map some)
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section GenericGrowth

/-- `push!(a, x)` (array.jl:1325-1350 docstring): the value is stored after every old element. -/
def PushesAtEnd (P : MutableMemory α → Prop) (handle : Nat)
    (push : Nat → α → MutationM α Unit) : Prop :=
  ∀ s x, P s → s.validVector handle → ∃ next, (push handle x).run s = (.ok (), next) ∧ P next ∧
    next.validVector handle ∧ next.contents handle = s.contents handle ++ [some x]

/-- `pushfirst!(a, x)` (array.jl:1753-1770 docstring): the value is stored before every old
element. -/
def PushesAtFront (P : MutableMemory α → Prop) (handle : Nat)
    (pushfirst : Nat → α → MutationM α Unit) : Prop :=
  ∀ s x, P s → s.validVector handle → ∃ next, (pushfirst handle x).run s = (.ok (), next) ∧
    P next ∧ next.validVector handle ∧ next.contents handle = some x :: s.contents handle

/-- `reverse!(a, 1, n)` (array.jl:2291-2316 docstring) reverses the first `n` elements. -/
def ReversesPrefix (P : MutableMemory α → Prop) (handle : Nat)
    (reverse : Nat → I → I → MutationM α Unit) : Prop :=
  ∀ s (n : I), P s → s.validVector handle → 0 ≤ n.val →
    n.val ≤ ((s.contents handle).length : Int) →
    ∃ next, (reverse handle one n).run s = (.ok (), next) ∧ P next ∧ next.validVector handle ∧
      next.contents handle = ((s.contents handle).take n.val.toNat).reverse ++
        (s.contents handle).drop n.val.toNat

/-- An action that only changes capacity, as `sizehint!` (array.jl:1576-1610 docstring) does. -/
def KeepsContents (P : MutableMemory α → Prop) (handle : Nat) (act : MutationM α Unit) : Prop :=
  ∀ s, P s → s.validVector handle → ∃ next, act.run s = (.ok (), next) ∧ P next ∧
    next.validVector handle ∧ next.contents handle = s.contents handle

theorem appendUnsized_run (P : MutableMemory α → Prop) (handle : Nat)
    (push : Nat → α → MutationM α Unit) (hpush : PushesAtEnd P handle push) :
    ∀ (xs : List α) (s : MutableMemory α), P s → s.validVector handle →
      ∃ next, (appendUnsized push handle xs).run s = (.ok handle, next) ∧ P next ∧
        next.validVector handle ∧ next.contents handle = s.contents handle ++ xs.map some
  | [], s, hP, hv => ⟨s, by simp [appendUnsized, stateExcept_bind, stateExcept_pure], hP, hv,
      by simp⟩
  | x :: xs, s, hP, hv => by
    obtain ⟨s1, h1, hP1, hv1, hc1⟩ := hpush s x hP hv
    obtain ⟨next, h2, hP2, hv2, hc2⟩ := appendUnsized_run P handle push hpush xs s1 hP1 hv1
    refine ⟨next, ?_, hP2, hv2, by rw [hc2, hc1]; simp⟩
    have hstep : (appendUnsized push handle (x :: xs)).run s =
        (appendUnsized push handle xs).run s1 := by
      simp only [appendUnsized, List.forIn_cons, stateExcept_bind, h1, stateExcept_pure]
    rw [hstep, h2]

/-- The counting `pushfirst!` loop of `_prepend!` after any number of items. -/
theorem prependLoop_run (P : MutableMemory α → Prop) (handle : Nat)
    (pushfirst : Nat → α → MutationM α Unit) (hpf : PushesAtFront P handle pushfirst) :
    ∀ (xs : List α) (r : I) (s : MutableMemory α), P s → s.validVector handle → 0 ≤ r.val →
      r.val + xs.length ≤ 2 ^ 62 →
      ∃ r' next, (forIn xs r (fun (item : α) (r : I) => (do
          pushfirst handle item
          pure (ForInStep.yield (r + one)) : MutationM α (ForInStep I)))).run s = (.ok r', next) ∧
        r'.val = r.val + xs.length ∧ P next ∧ next.validVector handle ∧
        next.contents handle = (xs.map some).reverse ++ s.contents handle
  | [], r, s, hP, hv, _, _ => ⟨r, s, rfl, by simp, hP, hv, by simp⟩
  | x :: xs, r, s, hP, hv, hr, hlen => by
    obtain ⟨s1, h1, hP1, hv1, hc1⟩ := hpf s x hP hv
    have hrb := ival_bounds r
    have hr1 : (r + one).val = r.val + 1 := ival_add_one _ (by simp at hlen; omega)
    obtain ⟨r', next, h2, hr', hP2, hv2, hc2⟩ :=
      prependLoop_run P handle pushfirst hpf xs (r + one) s1 hP1 hv1 (by omega)
        (by simp at hlen; omega)
    refine ⟨r', next, ?_, by rw [hr', hr1]; simp; omega, hP2, hv2, by
      rw [hc2, hc1]; simp⟩
    simp only [List.forIn_cons, stateExcept_bind, h1, stateExcept_pure]
    exact h2

/-- `_append!(a, ::IteratorSize, iter)` and `_append!(a, ::Union{HasLength,HasShape}, iter)`
(array.jl:1434-1447), reached through `append!(a::AbstractVector, iter)` (array.jl:1430) and
`push!(a::AbstractVector, iter...)` (array.jl:1431); docstrings of `append!` and `push!` at
array.jl:1325-1350 and 1384-1418: every value of `iter` is added at the end, in iteration order,
after every old element, and `a` is returned. A failing `Int(length(iter))` conversion propagates
before `a` is touched. -/
def AppendIterSpec : Prop :=
  ∀ (α : Type) (t : IntTy) (P : MutableMemory α → Prop) (handle : Nat)
    (push : Nat → α → MutationM α Unit) (sizehint : Nat → I → Bool → MutationM α Unit)
    (arrayLength : Nat → MutationM α I) (length : List α → JInt t)
    (toInt : JInt t → MutationM α I),
    PushesAtEnd P handle push → (∀ sz first, KeepsContents P handle (sizehint handle sz first)) →
    (∀ s, ∃ l, (arrayLength handle).run s = (.ok l, s)) →
    ∀ (xs : List α) (s : MutableMemory α), P s → s.validVector handle →
    let sized := appendSized length toInt arrayLength sizehint push
    let unsized := appendUnsized push
    let expected := s.contents handle ++ xs.map some
    (∃ next, (unsized handle xs).run s = (.ok handle, next) ∧ next.validVector handle ∧
      next.contents handle = expected) ∧
    (∀ e, (toInt (length xs)).run s = (.error e, s) → (sized handle xs).run s = (.error e, s)) ∧
    (∀ n, (toInt (length xs)).run s = (.ok n, s) →
      ∃ next, (sized handle xs).run s = (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle = expected) ∧
    (∀ (Size : Type) (iteratorSize : List α → Size) (hasLength : Size → Bool),
      (hasLength (iteratorSize xs) = true → ∃ n, (toInt (length xs)).run s = (.ok n, s)) →
      let append := appendIterator iteratorSize hasLength length toInt arrayLength sizehint push
      (∃ next, (append handle xs).run s = (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle = expected) ∧
      (∃ next, (pushMany (fun _ => false) pure (fun ys => JInt.wrap .i64 ys.length)
          (fun _ _ => pure ()) arrayLength (fun _ => pure one) (fun _ _ _ _ _ => pure ())
          sizehint push handle xs).run s = (.ok handle, next) ∧
        next.validVector handle ∧ next.contents handle = expected))

theorem appendSized_run {α : Type} {t : IntTy} (P : MutableMemory α → Prop) (handle : Nat)
    (push : Nat → α → MutationM α Unit) (sizehint : Nat → I → Bool → MutationM α Unit)
    (arrayLength : Nat → MutationM α I) (length : List α → JInt t)
    (toInt : JInt t → MutationM α I) (hpush : PushesAtEnd P handle push)
    (hsize : ∀ sz first, KeepsContents P handle (sizehint handle sz first))
    (hlen : ∀ s, ∃ l, (arrayLength handle).run s = (.ok l, s))
    (xs : List α) (s : MutableMemory α) (hP : P s) (hv : s.validVector handle) (n : I)
    (hn : (toInt (length xs)).run s = (.ok n, s)) :
    ∃ next, (appendSized length toInt arrayLength sizehint push handle xs).run s =
      (.ok handle, next) ∧ next.validVector handle ∧
      next.contents handle = s.contents handle ++ xs.map some := by
  obtain ⟨l, hl⟩ := hlen s
  obtain ⟨s1, h1, hP1, hv1, hc1⟩ := hsize (l + n) false s hP hv
  obtain ⟨next, h2, _, hv2, hc2⟩ := appendUnsized_run P handle push hpush xs s1 hP1 hv1
  refine ⟨next, ?_, hv2, by rw [hc2, hc1]⟩
  simp only [appendSized, stateExcept_bind, hn, hl, h1]
  simpa only [appendUnsized, stateExcept_bind] using h2

def PrependIterSpec : Prop :=
  ∀ (α : Type) (t : IntTy) (P : MutableMemory α → Prop) (handle : Nat)
    (pushfirst : Nat → α → MutationM α Unit) (reverse : Nat → I → I → MutationM α Unit)
    (sizehint : Nat → I → Bool → Bool → MutationM α Unit) (requireOneBased : Nat → MutationM α Unit)
    (arrayLength : Nat → MutationM α I) (length : List α → JInt t)
    (toInt : JInt t → MutationM α I),
    PushesAtFront P handle pushfirst → ReversesPrefix P handle reverse →
    (∀ sz first shrink, KeepsContents P handle (sizehint handle sz first shrink)) →
    (∀ s, (requireOneBased handle).run s = (.ok (), s)) →
    (∀ s, ∃ l, (arrayLength handle).run s = (.ok l, s)) →
    ∀ (xs : List α) (s : MutableMemory α), P s → s.validVector handle →
    (xs.length : Int) < 2 ^ 62 →
    let sized := prependSized requireOneBased length toInt arrayLength sizehint pushfirst reverse
    let unsized := prependUnsized pushfirst reverse
    let expected := xs.map some ++ s.contents handle
    (∃ next, (unsized handle xs).run s = (.ok handle, next) ∧ next.validVector handle ∧
      next.contents handle = expected) ∧
    (∀ e, (toInt (length xs)).run s = (.error e, s) → (sized handle xs).run s = (.error e, s)) ∧
    (∀ n, (toInt (length xs)).run s = (.ok n, s) →
      ∃ next, (sized handle xs).run s = (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle = expected) ∧
    (∀ (Size : Type) (iteratorSize : List α → Size) (hasLength : Size → Bool),
      (hasLength (iteratorSize xs) = true → ∃ n, (toInt (length xs)).run s = (.ok n, s)) →
      let prepend := prependIterator iteratorSize hasLength requireOneBased length toInt
        arrayLength sizehint pushfirst reverse
      (∃ next, (prepend handle xs).run s = (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle = expected) ∧
      (∃ next, (pushfirstMany (fun _ => false) pure (fun ys => JInt.wrap .i64 ys.length)
          (fun _ _ => pure ()) (fun _ => pure one) (fun _ _ _ _ _ => pure ())
          requireOneBased arrayLength sizehint pushfirst reverse handle xs).run s = (.ok handle, next) ∧
        next.validVector handle ∧ next.contents handle = expected))

theorem prependUnsized_run {α : Type} (P : MutableMemory α → Prop) (handle : Nat)
    (pushfirst : Nat → α → MutationM α Unit) (reverse : Nat → I → I → MutationM α Unit)
    (hpf : PushesAtFront P handle pushfirst) (hrev : ReversesPrefix P handle reverse)
    (xs : List α) (s : MutableMemory α) (hP : P s) (hv : s.validVector handle)
    (hsmall : (xs.length : Int) < 2 ^ 62) :
    ∃ next, (prependUnsized pushfirst reverse handle xs).run s = (.ok handle, next) ∧ P next ∧
      next.validVector handle ∧ next.contents handle = xs.map some ++ s.contents handle := by
  obtain ⟨r', s1, h1, hr', hP1, hv1, hc1⟩ :=
    prependLoop_run P handle pushfirst hpf xs zero s hP hv (by simp [ival_zero])
      (by simp [ival_zero]; omega)
  rw [ival_zero, Int.zero_add] at hr'
  obtain ⟨next, h2, hP2, hv2, hc2⟩ := hrev s1 r' hP1 hv1 (by omega)
    (by rw [hc1, hr']; simp; omega)
  refine ⟨next, ?_, hP2, hv2, ?_⟩
  · simp only [prependUnsized, stateExcept_bind, h1, h2, stateExcept_pure]
  · have hk : r'.val.toNat = (xs.map some).reverse.length := by simp; omega
    rw [hc2, hc1, hk, List.take_left, List.drop_left, List.reverse_reverse]

theorem prependSized_run {α : Type} {t : IntTy} (P : MutableMemory α → Prop) (handle : Nat)
    (pushfirst : Nat → α → MutationM α Unit) (reverse : Nat → I → I → MutationM α Unit)
    (sizehint : Nat → I → Bool → Bool → MutationM α Unit) (requireOneBased : Nat → MutationM α Unit)
    (arrayLength : Nat → MutationM α I) (length : List α → JInt t)
    (toInt : JInt t → MutationM α I) (hpf : PushesAtFront P handle pushfirst)
    (hrev : ReversesPrefix P handle reverse)
    (hsize : ∀ sz first shrink, KeepsContents P handle (sizehint handle sz first shrink))
    (hreq : ∀ s, (requireOneBased handle).run s = (.ok (), s))
    (hlen : ∀ s, ∃ l, (arrayLength handle).run s = (.ok l, s))
    (xs : List α) (s : MutableMemory α) (hP : P s) (hv : s.validVector handle)
    (hsmall : (xs.length : Int) < 2 ^ 62) (n : I)
    (hn : (toInt (length xs)).run s = (.ok n, s)) :
    ∃ next, (prependSized requireOneBased length toInt arrayLength sizehint pushfirst reverse
      handle xs).run s = (.ok handle, next) ∧ next.validVector handle ∧
      next.contents handle = xs.map some ++ s.contents handle := by
  obtain ⟨l, hl⟩ := hlen s
  obtain ⟨s1, h1, hP1, hv1, hc1⟩ := hsize (l + n) true false s hP hv
  obtain ⟨next, h2, _, hv2, hc2⟩ :=
    prependUnsized_run P handle pushfirst reverse hpf hrev xs s1 hP1 hv1 hsmall
  refine ⟨next, ?_, hv2, by rw [hc2, hc1]⟩
  simp only [prependSized, stateExcept_bind, hreq, hn, hl, h1]
  simpa only [prependUnsized, stateExcept_bind] using h2
end GenericGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `append!(a, items)` for a `Vector` `a` and a `Vector` `items` (array.jl:1422; docstring at
array.jl:1384-1418): `a` becomes its old elements followed by the elements `items` had before the
call, unassigned slots included, in a valid vector; `items` may be `a` itself, which doubles it.
`length(items)` and `firstindex(items) == 1` are the `Vector` methods of essentials.jl and
abstractarray.jl; a distinct `items` does not share `a`'s memory. The size precondition is that
`a`'s memory length plus `length(items)` is an `Int`. -/

def AppendVectorSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (s : MutableMemory α) (a b : Nat),
    s.validVector a → s.validVector b →
    (b = a ∨ ∀ va vb, s.arrays[a]? = some va → s.arrays[b]? = some vb →
      va.reference.1 ≠ vb.reference.1) →
    let run := (appendVector (m := MutationM α) (fun _ => false) pure mutableLength pure
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableLength (fun _ => pure one) mutableCopyto a b).run s
    Follows s (growendPlan l (geometryOf s a) (s.contents b).length) run (fun r next =>
      r = a ∧ next.validVector a ∧ next.contents a = s.contents a ++ s.contents b)

/-- `prepend!(a, items)` for a `Vector` `a` and a `Vector` `items` (array.jl:1480; docstring at
array.jl:1449-1476): `a` becomes the elements `items` had before the call followed by its old
elements, unassigned slots included, in a valid vector; `items` may be `a` itself, which doubles
it. `length(items)` and `lastindex(items)` are the `Vector` methods, and a distinct `items` does not
share `a`'s memory, so `unalias(a, items)` returns `items` itself. The size precondition is that
`a`'s memory length plus `2*length(items) + 1` is an `Int`, as the checked growth arithmetic
of `_growbeg!` requires. -/

def PrependVectorSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (s : MutableMemory α) (a b : Nat),
    s.validVector a → s.validVector b →
    (b = a ∨ ∀ va vb, s.arrays[a]? = some va → s.arrays[b]? = some vb →
      va.reference.1 ≠ vb.reference.1) →
    let run := (prependVector (m := MutationM α) (fun _ => false) pure (fun items a => items == a)
        (fun _ items => pure items) mutableLength
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        mutableLength mutableCopyto a b).run s
    Follows s (growbegPlan l (geometryOf s a) (s.contents b).length) run (fun r next =>
      r = a ∧ next.validVector a ∧ next.contents a = s.contents b ++ s.contents a)
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

def appendVectorStep {α : Type} {layout : MemoryLayoutMetadata} (a source : Nat) : MutationM α Unit := do
  let _ ← appendVector (m := MutationM α) (fun _ => false) pure mutableLength pure
    (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) mutableLength
    (fun _ => pure one) mutableCopyto a source
  pure ()

def prependVectorStep {α : Type} {layout : MemoryLayoutMetadata} (a source : Nat) : MutationM α Unit := do
  let _ ← prependVector (m := MutationM α) (fun _ => false) pure
    (fun source a => source == a) (fun _ source => pure source)
    mutableLength (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
    mutableLength mutableCopyto a source
  pure ()
/-- `append!(a, iter...)` and `prepend!(a, iter...)` (array.jl:1432, 1497; docstrings at
array.jl:1384-1418 and 1449-1476: "For an ordered container `collection`, add the elements of each
`collections` to the end of it"; "Insert the elements of each `collections` to the beginning of
`a`. When `collections` specifies multiple collections, order is maintained: elements of
`collections[1]` will appear leftmost in `a`, and so on.") for source vectors whose slots may be
unassigned, any of which may be `a` itself: the methods add one collection at a time
(`append!` from the first source on, `prepend!` from the last source back), each step adding the
collection's elements as they are at that step, so a source that is `a` adds `a`'s current
elements. `a` ends holding that result in a valid vector, and `a` is returned. Sources other than
`a` do not share `a`'s memory. -/
def AppendManyDisjointSpec : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (xs : List (Option α)) (vectors : List (List (Option α))) (sources : List Nat)
    (initial : MutableMemory α),
    initial.validVector 0 → initial.contents = xs →
    (∀ p ∈ vectors.zipIdx, initial.validVector (p.2 + 1) ∧ initial.contents (p.2 + 1) = p.1 ∧
      ∀ v w, initial.arrays[0]? = some v → initial.arrays[p.2 + 1]? = some w →
        v.reference.1 ≠ w.reference.1) →
    (∀ h ∈ sources, h ≤ vectors.length) →
    let contents := fun (current : List (Option α)) (h : Nat) =>
      if h = 0 then current else initial.contents h
    let appended := sources.foldl (fun acc h => acc ++ contents acc h) xs
    let prepended := sources.foldr (fun h acc => contents acc h ++ acc) xs
    (appended.length + prepended.length) < 2 ^ 61 →
    (∀ v slots, initial.arrays[0]? = some v → initial.memories[v.reference.1]? = some slots →
      slots.length + appended.length + prepended.length + 3 < 2 ^ 61) →
    let afterAppend := (appendMany (appendVectorStep (layout := layout)) 0 sources).run initial
    let afterPrepend := (prependMany (prependVectorStep (layout := layout)) 0 sources).run initial
    (afterAppend.1 = .ok 0 ∧ afterAppend.2.validVector 0 ∧ afterAppend.2.contents = appended) ∧
    (afterPrepend.1 = .ok 0 ∧ afterPrepend.2.validVector 0 ∧ afterPrepend.2.contents = prepended)

/-- `pushfirst!(a::Vector{T}, item::T)` (array.jl:1777) with `_growbeg!` on the store. -/
def vectorPushfirstTyped {α : Type} {layout : MemoryLayoutMetadata} (a : Nat) (x : α) : MutationM α Unit := do
  let _ ← pushfirst1777 (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout))) mutableSet
    a x
  pure ()

/-- `reverse!(a, 1, n)` (array.jl:2312) on a vector of the store, with array.jl's `midpoint`
over int.jl's wrapping arithmetic. -/
def vectorReverseBang {α : Type} (a : Nat) (start stop : I) : MutationM α Unit := do
  let _ ← reverseBang (m := MutationM α) pure pure pure (fun _ => pure one) mutableLength
    (fun lo hi => pure (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
      JuliaLean.base.int.lshr_BitInteger_BitUnsigned lo hi))
    mutableGet mutableSet a start stop
  pure ()

/-- `require_one_based_indexing(a)` (abstractarray.jl) for a `Vector`, whose axes are
`OneTo`s and so have no offset. -/
def vectorRequireOneBased {α : Type} (_a : Nat) : MutationM α Unit :=
  match JuliaLean.base.abstractarray.requireOneBased (m := JuliaLean.base.abstractarray.Result) (fun (_ : Unit) => .ok false) () with
  | .ok _ => pure ()
  | .error _ => throw (.argument "offset arrays are not supported but got an array with index other than 1")

/-- An iterator of any type whose iteration (`iterate`, user-extensible, no Lean model) yields
the values `vals`, in order: the documented iteration protocol of a finite iterator, as Julia's
`for` loop runs it. -/
def IteratesAs {α X : Type} [ForIn (MutationM α) X α] (itr : X) (vals : List α) : Prop :=
  ∀ (β : Type) (init : β) (f : α → β → MutationM α (ForInStep β)),
    forIn itr init f = forIn vals init f

/-- `_append!(a, ::Union{HasLength,HasShape}, iter)` and `_append!(a, ::IteratorSize, iter)`
(array.jl:1434-1447), reached through `append!(a::AbstractVector, iter)` (array.jl:1430) and
`push!(a::AbstractVector, iter...)` (array.jl:1431; docstrings of `append!` and `push!` at
array.jl:1384-1418 and 1325-1350: the elements of the collection are added to the end, in
order), on a vector of the store, for an iterator of any type with any finite iteration
(`IteratesAs`) and any `IteratorSize`, with `push!`, `sizehint!`, `length` and `Int(·)` the models
of array.jl and int.jl and `length(iter)` the iterator's own length (any value of any BitInteger
type): when the iterator declares a length and `Int(length(iter))` fails, `InexactError`
propagates with `a` untouched; when it declares its true length, or no length, `a` ends holding
its old elements followed by the iterator's, in a valid vector, and `a` is returned. -/
def AppendIterSpec : Prop :=
  ∀ (α X Size : Type) [ForIn (MutationM α) X α] (layout : MemoryLayoutMetadata) (t : IntTy) (handle : Nat)
    (length : X → JInt t) (iteratorSize : X → Size) (hasLength : Size → Bool)
    (itr : X) (xs : List α) (s : MutableMemory α),
    IteratesAs itr xs → s.validVector handle →
    (∀ v slots, s.arrays[handle]? = some v → s.memories[v.reference.1]? = some slots →
      slots.length + xs.length + 3 < 2 ^ 62) →
    let append := appendIterator (m := MutationM α) iteratorSize hasLength length lengthToInt
      mutableLength (fun a n first => vectorSizehint (layout := layout) a n first false) (vectorPushTyped (layout := layout))
    let expected := s.contents handle ++ xs.map some
    (hasLength (iteratorSize itr) = true → ¬ intFits (length itr) →
      (append handle itr).run s = (.error .inexact, s)) ∧
    ((hasLength (iteratorSize itr) = true → (length itr).val = xs.length) →
      ∃ next, (append handle itr).run s = (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle = expected) ∧
    (∀ (lengthList : List α → JInt .i64), (lengthList xs).val = xs.length →
      ∃ next, (pushMany (m := MutationM α) (fun _ => false) pure lengthList
        (fun _ _ => pure ()) mutableLength (fun _ => pure one) (fun _ _ _ _ _ => pure ())
        (fun a n first => vectorSizehint (layout := layout) a n first false) (vectorPushTyped (layout := layout))
        handle xs).run s = (.ok handle, next) ∧
        next.validVector handle ∧ next.contents handle = expected)

def PrependIterSpec : Prop :=
  ∀ (α X Size : Type) [ForIn (MutationM α) X α] (layout : MemoryLayoutMetadata) (t : IntTy) (handle : Nat)
    (length : X → JInt t) (iteratorSize : X → Size) (hasLength : Size → Bool)
    (itr : X) (xs : List α) (s : MutableMemory α),
    IteratesAs itr xs → s.validVector handle →
    (∀ v slots, s.arrays[handle]? = some v → s.memories[v.reference.1]? = some slots →
      slots.length + xs.length + 3 < 2 ^ 62) →
    let prepend := prependIterator (m := MutationM α) iteratorSize hasLength vectorRequireOneBased
      length lengthToInt mutableLength (vectorSizehint (layout := layout)) (vectorPushfirstTyped (layout := layout)) vectorReverseBang
    let expected := xs.map some ++ s.contents handle
    (hasLength (iteratorSize itr) = true → ¬ intFits (length itr) →
      (prepend handle itr).run s = (.error .inexact, s)) ∧
    ((hasLength (iteratorSize itr) = true → (length itr).val = xs.length) →
      ∃ next, (prepend handle itr).run s = (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle = expected) ∧
    (∀ (lengthList : List α → JInt .i64), (lengthList xs).val = xs.length →
      ∃ next, (pushfirstMany (m := MutationM α) (fun _ => false) pure lengthList
        (fun _ _ => pure ()) (fun _ => pure one) (fun _ _ _ _ _ => pure ())
        vectorRequireOneBased mutableLength (vectorSizehint (layout := layout))
        (vectorPushfirstTyped (layout := layout)) vectorReverseBang
        handle xs).run s = (.ok handle, next) ∧
        next.validVector handle ∧ next.contents handle = expected)
end round4
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

theorem VecAt.replace {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (sl : List (Option α))
    (hl : sl.length = slots.length) :
    VecAt { s with memories := s.memories.set mem sl } handle mem off n sl := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  exact ⟨ha, List.getElem?_set_self hlt, ho, hn0, by rw [hl]; exact he, by rw [hl]; exact hc⟩

theorem mutableCopyto_zero (st : MutableMemory α) (a b : Nat) (d o k : I) (hk : k.val = 0) :
    (mutableCopyto a d b o k).run st = (.ok (), st) := by
  simp only [mutableCopyto, copyto288, copytoImpl, stateExcept_bind, stateExcept_pure, hk,
    decide_true, ite_true]

/-- The window of the destination after `vwCopyto_run`. -/
theorem vwCopyto_window {offA nA offB nB : I} {slotsA slotsB : List (Option α)}
    (hao : 1 ≤ offA.val) (hae : offA.val - 1 + nA.val ≤ (slotsA.length : Int)) (hbo : 1 ≤ offB.val)
    (hbe : offB.val - 1 + nB.val ≤ (slotsB.length : Int)) (doffs soffs k : I) (hk : 1 ≤ k.val)
    (hd1 : 1 ≤ doffs.val) (hde : doffs.val - 1 + k.val ≤ nA.val)
    (hs1 : 1 ≤ soffs.val) (hse : soffs.val - 1 + k.val ≤ nB.val) :
    vwWindow (slotsA.take ((offA.val - 1).toNat + (doffs.val - 1).toNat) ++
        (slotsB.drop ((offB.val - 1).toNat + (soffs.val - 1).toNat)).take k.val.toNat ++
        slotsA.drop ((offA.val - 1).toNat + (doffs.val - 1).toNat + k.val.toNat)) offA nA =
      (vwWindow slotsA offA nA).take (doffs.val - 1).toNat ++
        ((vwWindow slotsB offB nB).drop (soffs.val - 1).toNat).take k.val.toNat ++
        (vwWindow slotsA offA nA).drop ((doffs.val - 1).toNat + k.val.toNat) := by
  have hX : ((vwWindow slotsB offB nB).drop (soffs.val - 1).toNat).take k.val.toNat =
      (slotsB.drop ((offB.val - 1).toNat + (soffs.val - 1).toNat)).take k.val.toNat := by
    simp only [vwWindow]
    rw [List.drop_take, List.drop_drop, List.take_take,
      Nat.min_eq_left (show k.val.toNat ≤ nB.val.toNat - (soffs.val - 1).toNat by omega)]
  rw [hX]
  simp only [vwWindow]
  exact splice_window slotsA _ _ _ _ _ (by omega) (by omega)
    (by simp only [List.length_take, List.length_drop]; omega)

theorem appendVectorSpec : AppendVectorSpec := by
  intro α l s a b hva hvb hdisj
  dsimp only
  obtain ⟨memA, offA, nA, slotsA, ha⟩ := validVector_vecAt hva
  obtain ⟨memB, offB, nB, slotsB, hb⟩ := validVector_vecAt hvb
  have hwa := ha.contents
  have hwb := hb.contents
  have hlb := vwWindow_length hb
  have hnb0 := hb.2.2.2.1
  have hna0 := ha.2.2.2.1
  have hnab := ival_bounds nA
  have hnbb := ival_bounds nB
  have h1 : one.val = 1 := ival_one
  have hlenB : (s.contents b).length = nB.val.toNat := by rw [hwb, hlb]
  rw [VecAt.geometry ha, hlenB]
  obtain ⟨herr, hok⟩ := growend_plan l ha nB hnb0
  refine ⟨fun e he => ?_, fun g' hg' => ?_⟩
  · simp only [appendVector, stateExcept_bind, mutableLength_run s b _ hb.1, stateExcept_pure,
      Bool.false_eq_true, ite_false, herr e he]
  · obtain ⟨next, memA', offA', slotsA', hrun, hv, harr, hnd, hwin, _, hlen, hframe, hmem'⟩ :=
      hok g' hg'
    have hla' := vwWindow_length hv
    have hvA := hv.2.2.2.2.1
    have hW0 : (vwWindow slotsA' offA' (nA + nB)).take nA.val.toNat = s.contents a := by
      rw [hwin, hwa]
    have hWd : (vwWindow slotsA' offA' (nA + nB)).drop (nA.val.toNat + nB.val.toNat) = [] :=
      List.drop_eq_nil_of_le (by rw [hla']; omega)
    by_cases hz : nB.val = 0
    · refine ⟨a, next, ?_, rfl, hv.valid, ?_⟩
      · simp only [appendVector, stateExcept_bind, mutableLength_run s b _ hb.1, stateExcept_pure,
          Bool.false_eq_true, ite_false, hrun, mutableLength_run next a _ hv.1,
          mutableCopyto_zero _ _ _ _ _ _ hz]
      · rw [hv.contents, ← hW0, List.take_of_length_le (l := vwWindow slotsA' offA' (nA + nB))
          (i := nA.val.toNat) (by rw [hla']; omega),
          List.eq_nil_of_length_eq_zero (by rw [hlenB]; omega : (s.contents b).length = 0),
          List.append_nil]
    · have hk : 1 ≤ nB.val := by omega
      have hsub : (nA + nB - nB).val = nA.val := by
        rw [ival_sub (nA + nB) nB (by omega), hnd]
        omega
      have hdo : (nA + nB - nB + one).val = nA.val + 1 := by
        have := ival_bounds (nA + nB)
        rw [ival_add_one (nA + nB - nB) (by omega), hsub]
      obtain ⟨memS, offS, nS, slotsS, hsrc, hnS, hwS⟩ : ∃ memS offS nS slotsS,
          VecAt next b memS offS nS slotsS ∧ nB.val ≤ nS.val ∧
          ((vwWindow slotsS offS nS).drop (one.val - 1).toNat).take nB.val.toNat = s.contents b := by
        by_cases hab : b = a
        · subst hab
          have hsame : nB = nA := by
            have := ha.1.symm.trans hb.1
            simp only [Option.some.injEq, MutableVector.mk.injEq, Prod.mk.injEq] at this
            exact this.2.symm
          refine ⟨memA', offA', nA + nB, slotsA', hv, by omega, ?_⟩
          rw [h1, show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero, ← hW0, hsame]
        · have hmb := hb.2.1
          have hmlt := (List.getElem?_eq_some_iff.mp hmb).choose
          have hne : memB ≠ memA := by
            intro hm
            exact hdisj.elim hab fun h => h _ _ ha.1 hb.1 hm.symm
          refine ⟨memB, offB, nB, slotsB,
            ⟨?_, ?_, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2⟩, Int.le_refl _, ?_⟩
          · rw [harr, List.getElem?_set_ne (fun h => hab h.symm)]
            exact hb.1
          · rw [hframe memB hmlt hne]
            exact hmb
          · rw [h1, show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero, hwb,
              List.take_of_length_le (Nat.le_of_eq hlb)]
      have hsO := hsrc.2.2.1
      have hsE := hsrc.2.2.2.2.1
      have hcopy := vwCopyto_run next hv hsrc (nA + nB - nB + one) one nB hk (by omega)
        (by omega) (by omega) (by omega)
      have hwin2 := vwCopyto_window hv.2.2.1 hvA hsO hsE
        (nA + nB - nB + one) one nB hk (by omega) (by omega) (by omega) (by omega)
      have hoA' := hv.2.2.1
      have hrep := VecAt.replace hv (slotsA'.take ((offA'.val - 1).toNat + ((nA + nB - nB + one).val - 1).toNat) ++
          (slotsS.drop ((offS.val - 1).toNat + (one.val - 1).toNat)).take nB.val.toNat ++
          slotsA'.drop ((offA'.val - 1).toNat + ((nA + nB - nB + one).val - 1).toNat + nB.val.toNat))
        (splice_length _ _ _ _ (by omega) (by simp only [List.length_take, List.length_drop]; omega))
      refine ⟨a, _, ?_, rfl, hrep.valid, ?_⟩
      · simp only [appendVector, stateExcept_bind, mutableLength_run s b _ hb.1, stateExcept_pure,
          Bool.false_eq_true, ite_false, hrun, mutableLength_run next a _ hv.1, hcopy]
      · rw [hrep.contents, hwin2, hwS, hdo, show (nA.val + 1 - 1).toNat = nA.val.toNat by omega,
          hW0, hWd, List.append_nil]
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
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 3000000
attribute [local irreducible] JInt.wrap

theorem tailSourceIndex_val (n k : I) (hk : 1 ≤ k.val) (hkn : k.val ≤ n.val) :
    (n-k+one).val = n.val-k.val+1 := by
  have hnB := ival_bounds n
  have hkB := ival_bounds k
  have hs : (n-k).val = n.val-k.val := ival_sub _ _ (by omega)
  rw [ival_add_one (n-k) (by rw [hs]; omega),hs]

theorem prependVectorSpec : PrependVectorSpec := by
  intro α l s a b hva hvb hdisj
  dsimp only
  obtain ⟨memA,offA,nA,slotsA,ha⟩ := validVector_vecAt hva
  obtain ⟨memB,offB,nB,slotsB,hb⟩ := validVector_vecAt hvb
  have hwa := ha.contents
  have hwb := hb.contents
  have hlb := vwWindow_length hb
  have hnb0 := hb.2.2.2.1
  have hna0 := ha.2.2.2.1
  have hnab := ival_bounds nA
  have hnbb := ival_bounds nB
  have h1 : one.val = 1 := ival_one
  have hlenB : (s.contents b).length = nB.val.toNat := by rw [hwb,hlb]
  rw [opusGrowth.VecAt.geometry ha,hlenB]
  obtain ⟨herr,hok⟩ := growbeg_plan l ha nB hnb0
  refine ⟨fun e he => ?_,fun g hg => ?_⟩
  · simp only [prependVector,Bool.false_eq_true,ite_false,ite_self,stateExcept_bind,stateExcept_pure,
      mutableLength_run s b _ hb.1,herr e he]
  · obtain ⟨grown,memA',offA',slotsA',hGrow,hv,harr,hnd,hwin,_,hmemlen,hframe,hmem'⟩ := hok g hg
    have hNewLen := vwWindow_length hv
    have hEndA := hv.2.2.2.2.1
    have hOffA := hv.2.2.1
    have hTail : (vwWindow slotsA' offA' (nA+nB)).drop nB.val.toNat = s.contents a := by
      rw [hwin,← hwa]
    by_cases hz : nB.val = 0
    · have hTake : (vwWindow slotsA' offA' (nA+nB)) = s.contents a := by
        simpa only [hz,Int.toNat_zero,List.drop_zero] using hTail
      have hEmpty : s.contents b = [] := List.eq_nil_of_length_eq_zero (by rw [hlenB]; omega)
      obtain ⟨vb,hvb'⟩ : ∃ vb, grown.arrays[b]? = some vb := by
        by_cases hab : b = a
        · subst b
          exact ⟨_,hv.1⟩
        · refine ⟨⟨(memB,offB),nB⟩,?_⟩
          rw [harr,List.getElem?_set_ne (fun h => hab h.symm)]
          exact hb.1
      refine ⟨a,grown,?_,rfl,hv.valid,?_⟩
      · simp only [prependVector,Bool.false_eq_true,ite_false,ite_self,stateExcept_bind,stateExcept_pure,
          mutableLength_run s b _ hb.1,hGrow,mutableLength_run grown b _ hvb',
          mutableCopyto_zero _ _ _ _ _ _ hz]
      · rw [hv.contents,hTake,hEmpty,List.nil_append]
    · have hk : 1 ≤ nB.val := by omega
      obtain ⟨memS,offS,nS,slotsS,hsrc,hnS,hSlice⟩ : ∃ memS offS nS slotsS,
          VecAt grown b memS offS nS slotsS ∧ nB.val ≤ nS.val ∧
          ((vwWindow slotsS offS nS).drop ((nS-nB+one).val-1).toNat).take nB.val.toNat = s.contents b := by
        by_cases hab : b = a
        · subst b
          have hsame : nB = nA := by
            have hh := ha.1.symm.trans hb.1
            simp only [Option.some.injEq,MutableVector.mk.injEq,Prod.mk.injEq] at hh
            exact hh.2.symm
          have hIdx := tailSourceIndex_val (nA+nB) nB hk (by omega)
          refine ⟨memA',offA',nA+nB,slotsA',hv,by omega,?_⟩
          rw [hIdx,hnd]
          have hp : (nA.val+nB.val-nB.val+1-1).toNat = nB.val.toNat := by rw [hsame]; omega
          rw [hp,hwin,← hwa]
          exact List.take_of_length_le (Nat.le_of_eq hlenB)
        · have hmb := hb.2.1
          have hmlt := (List.getElem?_eq_some_iff.mp hmb).choose
          have hne : memB ≠ memA := by
            intro hm
            exact hdisj.elim hab (fun h => h _ _ ha.1 hb.1 hm.symm)
          have hsrc : VecAt grown b memB offB nB slotsB := by
            refine ⟨?_,?_,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2⟩
            · rw [harr,List.getElem?_set_ne (fun h => hab h.symm)]
              exact hb.1
            · rw [hframe memB hmlt hne]
              exact hmb
          refine ⟨memB,offB,nB,slotsB,hsrc,Int.le_refl _,?_⟩
          rw [tailSourceIndex_val nB nB hk (Int.le_refl _)]
          simp only [Int.sub_self,Int.zero_add,Int.sub_self,Int.toNat_zero,List.drop_zero]
          rw [← hwb]
          exact List.take_of_length_le (Nat.le_of_eq hlenB)
      have hIdx := tailSourceIndex_val nS nB hk hnS
      have hsO := hsrc.2.2.1
      have hsE := hsrc.2.2.2.2.1
      have hcopy := vwCopyto_run grown hv hsrc one (nS-nB+one) nB hk
        (by rw [h1]; decide) (by rw [h1]; omega) (by rw [hIdx]; omega) (by rw [hIdx]; omega)
      have hwindow := vwCopyto_window hv.2.2.1 hEndA hsO hsE one (nS-nB+one) nB hk
        (by rw [h1]; decide) (by rw [h1]; omega) (by rw [hIdx]; omega) (by rw [hIdx]; omega)
      have hDestSpace : (offA'.val-1).toNat+(one.val-1).toNat+nB.val.toNat ≤ slotsA'.length := by
        rw [h1]
        omega
      have hSourceLength : ((slotsS.drop ((offS.val-1).toNat+((nS-nB+one).val-1).toNat)).take nB.val.toNat).length =
          nB.val.toNat := by
        simp only [List.length_take,List.length_drop]
        rw [hIdx]
        omega
      have hrep := VecAt.replace hv (slotsA'.take ((offA'.val-1).toNat+(one.val-1).toNat) ++
        (slotsS.drop ((offS.val-1).toNat+((nS-nB+one).val-1).toNat)).take nB.val.toNat ++
        slotsA'.drop ((offA'.val-1).toNat+(one.val-1).toNat+nB.val.toNat))
        (splice_length _ _ _ _ hDestSpace hSourceLength)
      refine ⟨a,_,?_,rfl,hrep.valid,?_⟩
      · simp only [prependVector,Bool.false_eq_true,ite_false,ite_self,stateExcept_bind,stateExcept_pure,
          mutableLength_run s b _ hb.1,hGrow,mutableLength_run grown b _ hsrc.1,hcopy]
      · rw [hrep.contents,hwindow,hSlice,h1]
        simp only [Int.sub_self,Int.toNat_zero,List.take_zero,List.nil_append,Nat.zero_add]
        rw [hTail]
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
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 1000000
attribute [local irreducible] JInt.wrap

theorem mutableAllocate_header_run (layout : Option MemoryLayout) (s : MutableMemory α)
    (a : Nat) (n : I) :
    (mutableAllocate layout a n).run s =
      match (memoryUndef (m := MutationM α) layout (mutableFreshMemory 0) mutableFreshMemory n).run s with
      | (.error e, after) => (.error e, after)
      | (.ok mem, after) => (.ok after.arrays.length,
          { after with arrays := after.arrays ++ [⟨(mem, one), n⟩] }) := by
  unfold mutableAllocate arrayUndef1
  rw [stateExcept_bind]
  cases h : (memoryUndef (m := MutationM α) layout (mutableFreshMemory 0) mutableFreshMemory n).run s with
  | mk result after => cases result <;> rfl

theorem mutableAllocate_good_run (l : DictLayout) (s : MutableMemory α) (a : Nat) (n : I)
    (hn : 0 ≤ n.val) (hfit : memoryFits l n.val.toNat) :
    (mutableAllocate (MemoryLayoutMetadata.ofRuntime l) a n).run s =
      (.ok s.arrays.length,
        { memories := s.memories ++ [List.replicate n.val.toNat none],
          arrays := s.arrays ++ [⟨(s.memories.length, one), n⟩] }) := by
  have h := (arrayNewMemorySpec α l s a n).2.2 hn hfit
  simp only [arrayNewMemory, mutableStorage] at h
  rw [mutableAllocate_header_run,h]

theorem mutableAllocate_bad_run (l : DictLayout) (s : MutableMemory α) (a : Nat) (n : I)
    (hn : 0 ≤ n.val) (hfit : ¬ memoryFits l n.val.toNat) :
    (mutableAllocate (MemoryLayoutMetadata.ofRuntime l) a n).run s = (.error (.argument genericMemorySizeMessage),s) := by
  have h := (arrayNewMemorySpec α l s a n).2.1 hn hfit
  simp only [arrayNewMemory, mutableStorage] at h
  rw [mutableAllocate_header_run,h]

theorem vecAt_append (s : MutableMemory α) (a mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (extraMemories : List (List (Option α))) (extraArrays : List MutableVector) :
    VecAt { memories := s.memories ++ extraMemories, arrays := s.arrays ++ extraArrays }
      a mem off n slots := by
  have ha := (List.getElem?_eq_some_iff.mp h.1).choose
  have hm := (List.getElem?_eq_some_iff.mp h.2.1).choose
  refine ⟨?_,?_,h.2.2⟩
  · exact (List.getElem?_append_left ha).trans h.1
  · exact (List.getElem?_append_left hm).trans h.2.1
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

theorem MultidimcovArrayV2AppendIter_proven :
    JuliaLean.Proofs.base.array.AppendIterSpec := by
  intro α t P handle push sizehint arrayLength length toInt hpush hsize hlen xs s hP hv
  dsimp only
  have unsized : ∃ next, (appendUnsized push handle xs).run s = (.ok handle, next) ∧
      next.validVector handle ∧ next.contents handle = s.contents handle ++ xs.map some := by
    obtain ⟨next, hr, _, hvn, hc⟩ := appendUnsized_run P handle push hpush xs s hP hv
    exact ⟨next, hr, hvn, hc⟩
  refine ⟨unsized, ?_, ?_, ?_⟩
  · intro e he
    simp only [appendSized, stateExcept_bind, he]
  · intro n hn
    exact appendSized_run P handle push sizehint arrayLength length toInt
      hpush hsize hlen xs s hP hv n hn
  · intro Size iteratorSize hasLength hknown
    constructor
    · by_cases hs : hasLength (iteratorSize xs) = true
      · obtain ⟨n, hn⟩ := hknown hs
        simpa only [appendIterator, appendDispatch, hs, ite_true] using
          appendSized_run P handle push sizehint arrayLength length toInt
            hpush hsize hlen xs s hP hv n hn
      · simpa only [appendIterator, appendDispatch, hs, Bool.false_eq_true, ite_false] using unsized
    · simpa only [pushMany, appendTupleDispatch, Bool.false_eq_true, ite_false,
        appendIterator, appendDispatch, id_eq, ite_true] using
        appendSized_run P handle push sizehint arrayLength
          (fun ys => JInt.wrap .i64 ys.length) pure hpush hsize hlen xs s hP hv
          (JInt.wrap .i64 xs.length) rfl

theorem MultidimcovArrayV2PrependIter_proven :
    JuliaLean.Proofs.base.array.PrependIterSpec := by
  intro α t P handle pushfirst reverse sizehint requireOneBased arrayLength length toInt
    hpush hreverse hsize hreq hlen xs s hP hv hsmall
  dsimp only
  have unsized : ∃ next, (prependUnsized pushfirst reverse handle xs).run s =
      (.ok handle, next) ∧ next.validVector handle ∧
      next.contents handle = xs.map some ++ s.contents handle := by
    obtain ⟨next, hr, _, hvn, hc⟩ :=
      prependUnsized_run P handle pushfirst reverse hpush hreverse xs s hP hv hsmall
    exact ⟨next, hr, hvn, hc⟩
  refine ⟨unsized, ?_, ?_, ?_⟩
  · intro e he
    simp only [prependSized, stateExcept_bind, hreq, he]
  · intro n hn
    exact prependSized_run P handle pushfirst reverse sizehint requireOneBased arrayLength
      length toInt hpush hreverse hsize hreq hlen xs s hP hv hsmall n hn
  · intro Size iteratorSize hasLength hknown
    constructor
    · by_cases hs : hasLength (iteratorSize xs) = true
      · obtain ⟨n, hn⟩ := hknown hs
        simpa only [prependIterator, prependDispatch, hs, ite_true] using
          prependSized_run P handle pushfirst reverse sizehint requireOneBased arrayLength
            length toInt hpush hreverse hsize hreq hlen xs s hP hv hsmall n hn
      · simpa only [prependIterator, prependDispatch, hs, Bool.false_eq_true, ite_false] using unsized
    · simpa only [pushfirstMany, prependTupleDispatch, Bool.false_eq_true, ite_false,
        prependIterator, prependDispatch, id_eq, ite_true] using
        prependSized_run P handle pushfirst reverse sizehint requireOneBased arrayLength
          (fun ys => JInt.wrap .i64 ys.length) pure hpush hreverse hsize hreq hlen xs s hP hv
          hsmall (JInt.wrap .i64 xs.length) rfl
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group14

open JuliaLean
open JuliaLean.base.array (I Error)
open JuliaLean.Registry

/-- The existing exception/state boundary, generalized over the whole runtime
state. Keeping ExceptT outside StateM retains effects preceding an exception. -/
abbrev BoundaryM (World : Type) := ExceptT Error (StateM World)

/-- `append!` returns the original array handle whenever it succeeds. An
iterator-size, declared-length, or length-conversion error is propagated at that
point, preserving exactly the state produced by that call and performing no
later capacity/element operations. All interface implementations and states are
quantified; there is no correctness law or success assumption on a callee.

The implications classify actual interface outcomes rather than restricting the
input domain. They are falsifiable, for example by moving sizehint/push before
length conversion or returning a different handle. No element-order promise is
claimed for an arbitrary user-defined push! implementation.

Julia source: base/array.jl:1430,1434-1447.
Documentation: base/array.jl:1384-1418; doc/src/manual/interfaces.md:8-49.
Pin: f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def AppendIteratorBoundaryInvariant : Prop :=
  ∀ (World A X E Size Z : Type) [ForIn (BoundaryM World) X E]
    (iteratorSize : X → BoundaryM World Size) (sized : Size → Option Bool)
    (length : X → BoundaryM World Z) (toInt : Z → BoundaryM World I)
    (arrayLength : A → BoundaryM World I)
    (sizehint : A → I → Bool → BoundaryM World Unit)
    (push : A → E → BoundaryM World Unit)
    (a : A) (itr : X) (initial : World),
    let run := (JuliaLean.base.array.Models1Group14.appendIterator
      iteratorSize sized length toInt arrayLength sizehint push a itr).run initial
    let traitRun := (iteratorSize itr).run initial
    (∀ (e : Error) (after : World), traitRun = (.error e, after) →
      run = (.error e, after)) ∧
    (∀ (trait : Size) (afterTrait : World),
      traitRun = (.ok trait, afterTrait) → sized trait = none →
      run = (.error (.method "_append!"), afterTrait)) ∧
    (∀ (trait : Size) (afterTrait : World), traitRun = (.ok trait, afterTrait) →
      sized trait = some true →
      (∀ (e : Error) (afterLength : World),
        (length itr).run afterTrait = (.error e, afterLength) →
        run = (.error e, afterLength)) ∧
      (∀ (rawLength : Z) (afterLength : World),
        (length itr).run afterTrait = (.ok rawLength, afterLength) →
        ∀ (e : Error) (afterConversion : World),
          (toInt rawLength).run afterLength = (.error e, afterConversion) →
          run = (.error e, afterConversion))) ∧
    (∀ (result : A) (final : World), run = (.ok result, final) → result = a)

/-- Generic prepend observes IteratorSize before resolving its installed helper.
Every trait error retains its state. A non-Vector receiver or malformed returned
trait raises MethodError without entering either helper. On the sized route,
the one-based check, declared length and Int conversion propagate errors in
that order; successful calls return the original array handle. Every typed
state, iterator, value and boundary operation is quantified, without supplying
a callee correctness law. The method table is the pinned Base table, so later
user-added `_prepend!` extensions are not silently represented as default calls.
Julia source: base/array.jl:1495,1499-1520; documentation:1450-1476. -/
def PrependIteratorBoundaryInvariant : Prop :=
  ∀ (World A X E Size Z : Type) [ForIn (BoundaryM World) X E]
    (isVector : A → Bool) (iteratorSize : X → BoundaryM World Size)
    (classifySize : Size → Option Bool)
    (requireOneBased : A → BoundaryM World Unit)
    (length : X → BoundaryM World Z) (toInt : Z → BoundaryM World I)
    (arrayLength : A → BoundaryM World I)
    (sizehint : A → I → Bool → Bool → BoundaryM World Unit)
    (pushfirst : A → E → BoundaryM World Unit)
    (reverse : A → I → I → BoundaryM World Unit)
    (a : A) (itr : X) (initial : World),
    let run := (JuliaLean.base.array.Models1Group14.prependIterator
      isVector iteratorSize classifySize requireOneBased length toInt
      arrayLength sizehint pushfirst reverse a itr).run initial
    (∀ error afterTrait,
      (iteratorSize itr).run initial = (.error error, afterTrait) →
      run = (.error error, afterTrait)) ∧
    (∀ trait afterTrait,
      (iteratorSize itr).run initial = (.ok trait, afterTrait) →
      (isVector a = false ∨ classifySize trait = none) →
      run = (.error (.method "_prepend!"), afterTrait)) ∧
    (∀ trait afterTrait,
      (iteratorSize itr).run initial = (.ok trait, afterTrait) →
      isVector a = true → classifySize trait = some true →
      (∀ error afterCheck,
        (requireOneBased a).run afterTrait = (.error error, afterCheck) →
        run = (.error error, afterCheck)) ∧
      (∀ afterCheck,
        (requireOneBased a).run afterTrait = (.ok (), afterCheck) →
        (∀ error afterLength,
          (length itr).run afterCheck = (.error error, afterLength) →
          run = (.error error, afterLength)) ∧
        (∀ rawLength afterLength error afterConversion,
          (length itr).run afterCheck = (.ok rawLength, afterLength) →
          (toInt rawLength).run afterLength = (.error error, afterConversion) →
          run = (.error error, afterConversion)))) ∧
    (∀ result final, run = (.ok result, final) → result = a)
end JuliaLean.Proofs.base.array.Models1Group14


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesAppend1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-append-iter", juliaFile := "base/array.jl",
    juliaFns := ["append!(a::AbstractVector, iter)", "push!(a::AbstractVector, iter...)",
      "_append!(a::AbstractVector, ::Union{HasLength,HasShape}, iter)",
      "_append!(a::AbstractVector, ::IteratorSize, iter)"],
    statement := "`_append!(a, ::Union{HasLength,HasShape}, iter)` and `_append!(a, ::IteratorSize, iter)` (array.jl:1434-1447), reached through `append!(a::AbstractVector, iter)` (array.jl:1430) and `push!(a::AbstractVector, iter...)` (array.jl:1431; docstrings of `append!` and `push!` at array.jl:1384-1418 and 1325-1350: the elements of the collection are added to the end, in order), on a vector of the store, for an iterator of any type with any finite iteration (`IteratesAs`) and any `IteratorSize`, with `push!`, `sizehint!`, `length` and `Int(·)` the models of array.jl and int.jl and `length(iter)` the iterator's own length (any value of any BitInteger type): when the iterator declares a length and `Int(length(iter))` fails, `InexactError` propagates with `a` untouched; when it declares its true length, or no length, `a` ends holding its old elements followed by the iterator's, in a valid vector, and `a` is returned.",
    source := "base/array.jl:1384-1418, array.jl:1430, array.jl:1431, array.jl:1434-1447", status := .proven,
    prop := ``AppendIterSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2AppendIter_proven,
    notes := "" },
  { id := "multidimcov-array-v2-prepend-iter", juliaFile := "base/array.jl",
    juliaFns := ["prepend!(a::AbstractVector, iter)", "pushfirst!(a::AbstractVector, iter...)",
      "_prepend!(a::Vector, ::Union{HasLength,HasShape}, iter)", "_prepend!(a::Vector, ::IteratorSize, iter)"],
    statement := "`_prepend!(a::Vector, ::Union{HasLength,HasShape}, iter)` and `_prepend!(a::Vector, ::IteratorSize, iter)` (array.jl:1499-1520), reached through `prepend!(a::AbstractVector, iter)` (array.jl:1495) and `pushfirst!(a::AbstractVector, iter...)` (array.jl:1496; docstrings of `prepend!` and `pushfirst!` at array.jl:1449-1476 and 1753-1771: the elements are inserted at the beginning, keeping their order), on a vector of the store, for an iterator of any type with any finite iteration and any `IteratorSize`, with `require_one_based_indexing`, `pushfirst!`, `reverse!`, `sizehint!`, `length` and `Int(·)` the models of abstractarray.jl, array.jl and int.jl and `length(iter)` the iterator's own length: when the iterator declares a length and `Int(length(iter))` fails, `InexactError` propagates with `a` untouched; when it declares its true length, or no length, `a` ends holding the iterator's elements in order followed by its old elements, in a valid vector, and `a` is returned.",
    source := "base/array.jl:1449-1476, array.jl:1495, array.jl:1496, array.jl:1499-1520", status := .proven,
    prop := ``PrependIterSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2PrependIter_proven,
    notes := "" }
]
def entriesAppend2 : List JuliaLean.Registry.Entry := [
  { id := "arrayops-append-many-self", juliaFile := "base/array.jl",
    juliaFns := ["append!(a::AbstractVector, iter...)", "prepend!(a::AbstractVector, iter...)"],
    statement := "`append!(a, iter...)` and `prepend!(a, iter...)` (array.jl:1432, 1497; docstrings at array.jl:1384-1418 and 1449-1476: \"For an ordered container `collection`, add the elements of each `collections` to the end of it\"; \"Insert the elements of each `collections` to the beginning of `a`. When `collections` specifies multiple collections, order is maintained: elements of `collections[1]` will appear leftmost in `a`, and so on.\") for source vectors whose slots may be unassigned, any of which may be `a` itself: the methods add one collection at a time (`append!` from the first source on, `prepend!` from the last source back), each step adding the collection's elements as they are at that step, so a source that is `a` adds `a`'s current elements. `a` ends holding that result in a valid vector, and `a` is returned. Sources other than `a` do not share `a`'s memory.",
    source := "base/array.jl:1384-1418, array.jl:1432", status := .todo,
    prop := ``AppendManySnapshot, thm := none,
    notes := "Statement/prose mismatch: AppendManySnapshot reads every self source from the initial vector, while the registered prose specifies sequential sources using the vector at each step. append!(a, a, a) with a = [1] therefore yields four ones as the prose requires; the returned proof only refutes the obsolete three-element snapshot demand." }
]
def entriesAppend3 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-append", juliaFile := "base/array.jl",
    juliaFns := ["append!(a::Vector{T}, items::Union{AbstractVector{<:T},Tuple}) where T"],
    statement := "append!(a, items) for a Vector items makes a its old elements followed by the elements items had before the call (unassigned slots included), items == a doubling a, in a valid vector.",
    source := "base/array.jl:1384-1428 (append! docstring)", status := .proven, prop := ``AppendVectorSpec, thm := some ``opusGrowth.appendVectorSpec },
  { id := "multidimcov-array-v2-prepend", juliaFile := "base/array.jl",
    juliaFns := ["prepend!(a::Vector{T}, items::Union{AbstractVector{<:T},Tuple}) where T"],
    statement := "prepend!(a, items) for a Vector items makes a the elements items had before the call followed by its old elements (unassigned slots included), items == a doubling a, in a valid vector.",
    source := "base/array.jl:1449-1493 (prepend! docstring)", status := .proven, prop := ``PrependVectorSpec, thm := some ``JuliaLean.Proofs.base.array.solArrayGrow.prependVectorSpec }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesAppend4 : List JuliaLean.Registry.Entry := [
{ id := "array-append-iterator-boundaries", juliaFile := "base/array.jl",
    juliaFns := ["append!(a::AbstractVector, iter)", "_append!(a::AbstractVector, ::Union{HasLength,HasShape}, iter)"],
    statement := "Iterator append returns its original array handle on success. Trait, length and Int-conversion errors propagate before later capacity/element operations, retaining the exact state left by the failing call; no callee correctness law is assumed.",
    source := "base/array.jl:1430,1434–1447; base/array.jl:1384–1418; exception-order and returned-handle invariants" , status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.AppendIteratorBoundaryInvariant, thm := none,
    notes := "Complete invariant over the existing typed stateful interface. User operations and iteration remain explicit boundaries; this is not a concrete implementation of every custom iterator or array." },
{ id := "array-prepend-iterator-boundaries", juliaFile := "base/array.jl",
    juliaFns := ["prepend!(a::AbstractVector, iter)", "_prepend!(a::Vector, ::Union{HasLength,HasShape}, iter)"],
    statement := "Generic prepend observes IteratorSize before helper dispatch. Trait errors retain their effects; a non-Vector receiver or malformed trait raises MethodError without calling a helper. Sized-route one-based, length and Int-conversion errors preserve their source order and state, and success returns the original array handle.",
    source := "base/array.jl:1495,1499–1520; base/array.jl:1450–1476; dispatch/error/identity invariants" , status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.PrependIteratorBoundaryInvariant, thm := none,
    notes := "The explicit method table is pinned Base: only Vector _prepend! methods are installed. Later user extensions are outside that table. Runtime type/trait projections are not unknown callee implementations, and no correctness law is assumed." }
]
end JuliaLean.Proofs.base.array

