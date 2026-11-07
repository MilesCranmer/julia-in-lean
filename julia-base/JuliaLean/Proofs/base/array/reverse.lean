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

/-- Out-of-place reversal and in-place reversal of a copy have equal results
or the same exception, including empty and one-element windows. -/
def ReverseCopyAgrees : Prop :=
  ∀ (α : Type) (s t : IntTy) (xs : List α) (start : JInt s) (stop : JInt t),
    xs.length < 2 ^ 62 →
    ((JuliaLean.base.array.reverse (m := VectorM α)
      (fun i => liftM (indexConvert i)) (fun i => liftM (indexConvert i))
      heapSimilar (fun _ => pure one) heapLength heapGet heapSet 0 start stop).run
        [xs.map some]).map (fun (handle, heap) => heap[handle]?) =
    ((reverseBang (m := VectorM α)
      (fun i => liftM (indexConvert i)) (fun i => liftM (indexConvert i))
      pure (fun _ => pure one) heapLength
      (fun lo hi => pure (midpoint (· + ·) (· - ·)
        (fun x n => JInt.wrap .i64 ((x.val % 2 ^ 64) / 2 ^ n.val.toNat)) lo hi))
      heapGet heapSet 0 start stop).run [xs.map some]).map
        (fun (handle, heap) => heap[handle]?)

/-- Reversing a valid index reflects it through the two linear endpoints, including wide indices. -/
def ReverseIndexReflectionSpec : Prop :=
  ∀ (A : Type) (firstLinear lastLinear : A → I) (a : A)
    (t : IntTy) (i : JInt t),
    (firstLinear a).val ≤ i.val → i.val ≤ (lastLinear a).val →
    (reverseind firstLinear lastLinear (JuliaLean.base.int.binop JuliaLean.base.int.sub)
      a i).val = (firstLinear a).val + (lastLinear a).val - i.val
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section HeapRanges

attribute [local irreducible] JInt.wrap wrapInt

/-! ### One-dimensional `dims` keywords of `reverse` and `reverse!` -/

/-- The `dims` keyword of `reverse(A::AbstractVector; dims)`: `:` or an Integer. -/
inductive VectorDims (t : IntTy) where
  | colon
  | integer (d : JInt t)

/-- `reverse(v, start, stop)` (array.jl:2248) on the shared heap. -/
def heapReverse3 {α : Type} (a : Nat) (start stop : I) : VectorM α Nat :=
  JuliaLean.base.array.reverse (m := VectorM α) (fun i => liftM (indexConvert i))
    (fun i => liftM (indexConvert i)) heapSimilar (fun _ => pure one) heapLength heapGet heapSet
    a start stop

/-- `reverse!(v, start, stop)` (array.jl:2312) on the shared heap. -/
def heapReverseBang3 {α : Type} (a : Nat) (start stop : I) : VectorM α Nat :=
  reverseBang (m := VectorM α) (fun i => liftM (indexConvert i)) (fun i => liftM (indexConvert i))
    pure (fun _ => pure one) heapLength
    (fun lo hi => pure (midpoint (· + ·) (· - ·)
      (fun x n => JInt.wrap .i64 ((x.val % 2 ^ 64) / 2 ^ n.val.toNat)) lo hi))
    heapGet heapSet a start stop

/-- `_reverse(A, :)` / `_reverse!(A, :)` (array.jl:2267) for the three-argument method `f`. -/
def heapReverseColon {α : Type} (f : Nat → I → I → VectorM α Nat) (a : Nat) : VectorM α Nat :=
  reverseColon (fun _ => pure one) heapLength f a

/-- The `_reverse`/`_reverse!` method selected by the `dims` value (array.jl:2267, 2269). -/
def heapReverseDim {α : Type} {t : IntTy} (f : Nat → I → I → VectorM α Nat) (a : Nat) :
    VectorDims t → VectorM α Nat
  | .colon => heapReverseColon f a
  | .integer d => reverseIntegerDim (fun d : JInt t => d.val == 1) (fun d => toString d.val)
      (heapReverseColon f) a d

/-- `reverse(A; dims)` / `reverse!(A; dims)` for a vector (array.jl:2266). -/
abbrev heapReverseDims {α : Type} {t : IntTy} (f : Nat → I → I → VectorM α Nat) (a : Nat)
    (dims : VectorDims t) : VectorM α Nat :=
  reverseDims (heapReverseDim f) a dims

/-- `reverse(v; dims)` and `reverse!(v; dims)` for a vector (array.jl:2264-2272): `dims = :` and
`dims = 1` both act on the whole vector, `f(v, firstindex(v), lastindex(v))` for the
three-argument `reverse` or `reverse!`, and every other integer `dims` raises
`ArgumentError("invalid dimension d ≠ 1")` before touching the vector. -/
def ReverseDimsSpec : Prop :=
  ∀ (α : Type) (t : IntTy) (heap : VectorHeap α) (a : Nat) (d : JInt t),
    ∀ f ∈ [heapReverse3 (α := α), heapReverseBang3 (α := α)],
    (heapReverseDims f a (.colon : VectorDims t)).run heap =
      (do f a one (← heapLength a)).run heap ∧
    (d.val = 1 → (heapReverseDims f a (.integer d)).run heap =
      (do f a one (← heapLength a)).run heap) ∧
    (d.val ≠ 1 → (heapReverseDims f a (.integer d)).run heap =
      .error (.argument ("invalid dimension " ++ toString d.val ++ " ≠ 1")))

theorem reverseDimsSpec : ReverseDimsSpec := by
  intro α t heap a d f _
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    have hb : (d.val == 1) = true := by simp [h]
    simp only [heapReverseDims, reverseDims, heapReverseDim, reverseIntegerDim, hb,
      Bool.not_true, Bool.false_eq_true, ite_false]
    rfl
  · intro h
    have hb : (d.val == 1) = false := by simp [h]
    simp only [heapReverseDims, reverseDims, heapReverseDim, reverseIntegerDim, hb,
      Bool.not_false, ite_true, vector_bind_run, vector_throw_run]
end HeapRanges
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
open JuliaLean.Proofs.base.int

private theorem midpoint_difference_pattern {t : IntTy} (lo hi : JInt t) (h : lo.val ≤ hi.val) :
    (pattern (JuliaLean.base.int.subWrap hi lo) : Int) = hi.val - lo.val := by
  have hlo := lo.property
  have hhi := hi.property
  have he := wrapInt_emod_self t (hi.val - lo.val)
  unfold pattern
  rw [JuliaLean.base.int.subWrap, sub_int_val]
  rw [he]
  have hmod : (hi.val - lo.val) % ((2 ^ t.bits : Nat) : Int) = hi.val - lo.val := by
    apply Int.emod_eq_of_lt (by omega)
    cases t <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hlo hhi ⊢ <;> omega
  rw [hmod]
  exact Int.toNat_of_nonneg (by omega)

private theorem midpoint_half_fits {t : IntTy} (lo hi : JInt t) (h : lo.val ≤ hi.val) :
    t.min ≤ (hi.val - lo.val) / 2 ∧ (hi.val - lo.val) / 2 ≤ t.max := by
  have hlo := lo.property
  have hhi := hi.property
  cases t <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hlo hhi ⊢ <;> omega

/-- Midpoints lie between ordered integer endpoints and round their average down,
    including when the subtraction overflows the signed representation. -/
def BitIntegerMidpointSpec : Prop :=
  ∀ (t : IntTy) (lo hi : JInt t), lo.val ≤ hi.val →
    let mid := midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
      JuliaLean.base.int.lshr_BitInteger_BitUnsigned lo hi
    mid.val = (lo.val + hi.val) / 2 ∧ lo.val ≤ mid.val ∧ mid.val ≤ hi.val

theorem bitIntegerMidpointSpec : BitIntegerMidpointSpec := by
  intro t lo hi h
  dsimp only
  unfold midpoint
  have hc : pattern (JInt.wrap .u8 1) = 1 := by
    simp [pattern, JInt.wrap, wrapInt, IntTy.bits, IntTy.signed]
  have hs : (JuliaLean.base.int.lshr_BitInteger_BitUnsigned
      (JuliaLean.base.int.subWrap hi lo) (JInt.wrap .u8 1)).val = (hi.val - lo.val) / 2 := by
    rw [JuliaLean.base.int.lshr_BitInteger_BitUnsigned, lshr_int_val,
      midpoint_difference_pattern lo hi h, hc]
    simp only [Int.pow_one]
    exact wrapInt_of_inRange t _ (midpoint_half_fits lo hi h)
  change (JuliaLean.base.int.addWrap lo _).val = _ ∧ _
  rw [JuliaLean.base.int.addWrap, add_int_val, hs]
  have hlo := lo.property
  have hhi := hi.property
  have hf : t.min ≤ lo.val + (hi.val - lo.val) / 2 ∧
      lo.val + (hi.val - lo.val) / 2 ≤ t.max := by omega
  rw [wrapInt_of_inRange t _ hf]
  omega
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000



def ReverseindSpec : Prop :=
  ∀ (A : Type) (a : A) (n : I) (t : IntTy) (i : JInt t), n.val < 2 ^ 62 → 1 ≤ i.val →
    i.val ≤ n.val →
    (reverseind (fun _ : A => one) (fun _ => n) (JuliaLean.base.int.binop JuliaLean.base.int.sub)
      a i).val = n.val + 1 - i.val ∧
    1 ≤ (reverseind (fun _ : A => one) (fun _ => n)
      (JuliaLean.base.int.binop JuliaLean.base.int.sub) a i).val ∧
    (reverseind (fun _ : A => one) (fun _ => n) (JuliaLean.base.int.binop JuliaLean.base.int.sub)
      a i).val ≤ n.val ∧
    (reverseind (fun _ : A => one) (fun _ => n) (JuliaLean.base.int.binop JuliaLean.base.int.sub) a
      (reverseind (fun _ : A => one) (fun _ => n)
        (JuliaLean.base.int.binop JuliaLean.base.int.sub) a i)).val = i.val ∧
    ∀ (β : Type) (xs : List β), (xs.length : Int) = n.val →
      xs.reverse[(i.val - 1).toNat]? =
        xs[((reverseind (fun _ : A => one) (fun _ => n)
          (JuliaLean.base.int.binop JuliaLean.base.int.sub) a i).val - 1).toNat]?

/-! ### Reversing a window -/

/-- The elements `xs` with the one-based window `start:stop` reversed. -/

def reverseWindow (xs : List α) (start stop : Int) : List α :=
  xs.take (start - 1).toNat ++ ((xs.drop (start - 1).toNat).take (stop - start + 1).toNat).reverse ++
    xs.drop stop.toNat
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
section HeapRanges

/-- The `dims` keyword of `reverse(A::AbstractVector; dims)`: `:` or an Integer. -/
inductive VectorDims (t : IntTy) where
  | colon
  | integer (d : JInt t)

/-- `reverse(v, start, stop)` (array.jl:2248) on the shared heap. -/
def heapReverse3 {α : Type} (a : Nat) (start stop : I) : VectorM α Nat :=
  JuliaLean.base.array.reverse (m := VectorM α) (fun i => liftM (indexConvert i))
    (fun i => liftM (indexConvert i)) heapSimilar (fun _ => pure one) heapLength heapGet heapSet
    a start stop

/-- `reverse!(v, start, stop)` (array.jl:2312) on the shared heap. -/
def heapReverseBang3 {α : Type} (a : Nat) (start stop : I) : VectorM α Nat :=
  reverseBang (m := VectorM α) (fun i => liftM (indexConvert i)) (fun i => liftM (indexConvert i))
    pure (fun _ => pure one) heapLength
    (fun lo hi => pure (midpoint (· + ·) (· - ·)
      (fun x n => JInt.wrap .i64 ((x.val % 2 ^ 64) / 2 ^ n.val.toNat)) lo hi))
    heapGet heapSet a start stop

/-- `_reverse(A, :)` / `_reverse!(A, :)` (array.jl:2267) for the three-argument method `f`. -/
def heapReverseColon {α : Type} (f : Nat → I → I → VectorM α Nat) (a : Nat) : VectorM α Nat :=
  reverseColon (fun _ => pure one) heapLength f a

/-- The `_reverse`/`_reverse!` method selected by the `dims` value (array.jl:2267, 2269). -/
def heapReverseDim {α : Type} {t : IntTy} (f : Nat → I → I → VectorM α Nat) (a : Nat) :
    VectorDims t → VectorM α Nat
  | .colon => heapReverseColon f a
  | .integer d => reverseIntegerDim (fun d : JInt t => d.val == 1) (fun d => toString d.val)
      (heapReverseColon f) a d

/-- `reverse(A; dims)` / `reverse!(A; dims)` for a vector (array.jl:2266). -/
abbrev heapReverseDims {α : Type} {t : IntTy} (f : Nat → I → I → VectorM α Nat) (a : Nat)
    (dims : VectorDims t) : VectorM α Nat :=
  reverseDims (heapReverseDim f) a dims
end HeapRanges
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
section NewStatements

/-- The elements `xs` with the one-based window `start:stop` reversed. -/
def reverseWindow (xs : List α) (start stop : Int) : List α :=
  xs.take (start - 1).toNat ++ ((xs.drop (start - 1).toNat).take (stop - start + 1).toNat).reverse ++
    xs.drop stop.toNat
end NewStatements
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

def heapGetInteger {α : Type} (ops : BigIntegerOps) (handle : Nat) (i : IntegerValue) :
    VectorM α α := do
  heapGet handle (← StateT.lift (arrayToIndex ops i))

/-- `firstindex(v)` and `lastindex(v)` of a vector of length `n` (abstractarray.jl:452, 429 with
`eachindex(IndexLinear(), ::AbstractVector) = axes1(v) = OneTo(n)` and range.jl's `first`/`last`). -/
def vectorFirstLinear (n : I) : I :=
  match JuliaLean.base.abstractarray.firstindexArray
    (JuliaLean.base.abstractarray.eachindexLinearVector
      (fun n : I => (.ok ⟨n⟩ : JuliaLean.base.abstractarray.Result (JuliaLean.base.range.OneTo I))))
    (fun r => .ok (JuliaLean.base.range.first_OneTo r)) n with
  | .ok v => v
  | .error _ => one

def vectorLastLinear (n : I) : I :=
  match JuliaLean.base.abstractarray.lastindexArray
    (JuliaLean.base.abstractarray.eachindexLinearVector
      (fun n : I => (.ok ⟨n⟩ : JuliaLean.base.abstractarray.Result (JuliaLean.base.range.OneTo I))))
    (fun r => match JuliaLean.base.range.last_OrdinalRange (T := I) (A := I) r with
      | .ok v => .ok v
      | .error _ => .error (.julia .boundsError)) n with
  | .ok v => v
  | .error _ => n

/-- `reverse(v, start, stop)` (array.jl:2248) on a vector of the shared heap (handle `0`), with
`Int(start)`, `Int(stop)`, `similar(v)` (`heapSimilar`), `firstindex`/`lastindex` and the Array
reads and stores. -/
abbrev heapReverse {α : Type} (ops : BigIntegerOps) (start stop : IntegerValue) : VectorM α Nat :=
  JuliaLean.base.array.reverse (m := VectorM α)
    (fun i : IntegerValue => StateT.lift (i.toInt ops)) (fun i : IntegerValue => StateT.lift (i.toInt ops))
    heapSimilar (fun _ => pure one) heapLength heapGet heapSet 0 start stop

/-- `reverseind(v::AbstractVector, i)` (array.jl:2276; docstring at array.jl:2258-2275: "Given an
index `i` in `reverse(v)`, return the corresponding index in `v` so that
`v[reverseind(v,i)] == reverse(v)[i]`") for a vector of the shared heap with unassigned slots
allowed and an index of any `Integer` type, with `LinearIndices(v)`'s `first` and `last`, the
promoted `first(li) + last(li) - i`, and `reverse(v)` (array.jl:2267, `reverse(v, firstindex(v),
lastindex(v))`): for every valid index `i` of `reverse(v)` (not a `Bool`, in `1:length(v)`), reading
`v` at `reverseind(v, i)` gives exactly what reading `reverse(v)` at `i` gives (the same element,
or the same error at an unassigned slot). -/
def ReverseIndexReflectionSpec : Prop :=
  ∀ (α : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (xs : List (Option α)) (i : IntegerValue),
    xs.length < 2 ^ 62 → i.validIndex xs.length →
    let n : I := JInt.wrap .i64 xs.length
    let viaIndex := heapGetInteger (α := α) ops 0
      (reverseind vectorFirstLinear vectorLastLinear (fun f i => i.subFromInt ops f) n i)
    let viaReverse : VectorM α α := do
      let r ← reverseColon (m := VectorM α) (fun _ => pure one) heapLength
        (fun a s e => JuliaLean.base.array.reverse (m := VectorM α)
          (fun i : I => pure i) (fun i : I => pure i)
          heapSimilar (fun _ => pure one) heapLength heapGet heapSet a s e) 0
      heapGetInteger ops r i
    (viaIndex.run [xs]).map Prod.fst = (viaReverse.run [xs]).map Prod.fst

def ReverseWindowSpec : Prop :=
  ∀ (α : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (xs : List (Option α)) (start stop : IntegerValue),
    xs.length < 2 ^ 62 →
    let run := (heapReverse (α := α) ops start stop).run [xs]
    (¬ start.fits → run = .error .inexact) ∧
    (start.fits → ¬ stop.fits → run = .error .inexact) ∧
    (1 ≤ start.val → start.val ≤ stop.val + 1 → stop.val ≤ xs.length →
      ((∀ x ∈ xs, x.isSome) → run = .ok (1, [xs, reverseWindow xs start.val stop.val])) ∧
      (none ∈ xs → run = .error .undefinedReference))

abbrev heapReverseBang {α : Type} (ops : BigIntegerOps) (start stop : IntegerValue) :
    VectorM α Nat :=
  reverseBang (m := VectorM α)
    (fun i : IntegerValue => StateT.lift (i.toInt ops)) (fun i : IntegerValue => StateT.lift (i.toInt ops))
    pure (fun _ => pure one) heapLength
    (fun lo hi => pure (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
      JuliaLean.base.int.lshr_BitInteger_BitUnsigned lo hi))
    heapGet heapSet 0 start stop

/-- `reverse!(v, start, stop)` (array.jl:2312; docstring at array.jl:2291-2311: "In-place version
of `reverse`") on a vector of the shared heap whose slots may be unassigned, with endpoints of any
`Integer` type: an endpoint with no equal `Int` raises `InexactError`; when `stop ≤ start` it
returns `v` unchanged; a window `start < stop` reaching outside `1:length(v)` raises `BoundsError`
with `v` unchanged; otherwise, when the window `v[start:stop]` is fully assigned it is reversed in
place and `v` returned, and when it holds an unassigned slot `UndefRefError` is raised. The
midpoint is `midpoint` of array.jl:2283 with the wrapping arithmetic of int.jl. -/
def ReverseBangWindowSpec : Prop :=
  ∀ (α : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (xs : List (Option α)) (start stop : IntegerValue),
    xs.length < 2 ^ 62 →
    let run := (heapReverseBang (α := α) ops start stop).run [xs]
    let window := (xs.drop (start.val - 1).toNat).take (stop.val - start.val + 1).toNat
    (¬ start.fits → run = .error .inexact) ∧
    (start.fits → ¬ stop.fits → run = .error .inexact) ∧
    (start.fits → stop.fits → stop.val ≤ start.val → run = .ok (0, [xs])) ∧
    (start.fits → stop.fits → start.val < stop.val → ¬(1 ≤ start.val ∧ stop.val ≤ xs.length) →
      run = .error .bounds) ∧
    (start.val < stop.val → 1 ≤ start.val → stop.val ≤ xs.length →
      ((∀ x ∈ window, x.isSome) → run = .ok (0, [reverseWindow xs start.val stop.val])) ∧
      (none ∈ window → run = .error .undefinedReference))

def ReverseCopyAgrees : Prop := ReverseWindowSpec ∧ ReverseBangWindowSpec
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section IndexGets

theorem reverseind_val (A : Type) (a : A) (n : I) (t : IntTy) (i : JInt t)
    (hn : n.val < 2 ^ 62) (hi1 : 1 ≤ i.val) (hin : i.val ≤ n.val) :
    (reverseind (fun _ : A => one) (fun _ => n) (JuliaLean.base.int.binop JuliaLean.base.int.sub)
      a i).val = n.val + 1 - i.val := by
  have hnb := ival_bounds n
  have hn' : n.val < 4611686018427387904 := hn
  have hadd : (one + n).val = 1 + n.val := by
    rw [ival_add _ _ (by rw [ival_one]; omega), ival_one]
  show (JuliaLean.base.int.binop JuliaLean.base.int.sub (one + n) i).val = _
  rw [JuliaLean.Proofs.base.range.binop_val_sub JuliaLean.base.int.sub
    (fun a b => JuliaLean.Proofs.base.int.sub_int_val a b), hadd]
  obtain ⟨hmin, hmax⟩ := promote_i64_range t
  rw [wrapInt_of_inRange _ _ ⟨by omega, by omega⟩]
  omega

theorem reverseindSpec : ReverseindSpec := by
  intro A a n t i hn hi1 hin
  have hr := reverseind_val A a n t i hn hi1 hin
  have hr2 := reverseind_val A a n _
    (reverseind (fun _ : A => one) (fun _ => n) (JuliaLean.base.int.binop JuliaLean.base.int.sub)
      a i) hn (by omega) (by omega)
  refine ⟨hr, by omega, by omega, by rw [hr2, hr]; omega, ?_⟩
  intro β xs hxs
  rw [hr, List.getElem?_reverse (by omega)]
  congr 1
  omega
end IndexGets
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 16384

theorem ArrayReverseindWideIndex_refuted :
    ¬ JuliaLean.Proofs.base.array.ReverseIndexReflectionSpec := by
  intro h
  have bad := h Unit
    (fun _ => JInt.wrap .i64 9223372036854775805)
    (fun _ => JInt.wrap .i64 9223372036854775806) ()
    .i128 (JInt.wrap .i128 9223372036854775805) (by decide) (by decide)
  change (-9223372036854775810 : Int) = 9223372036854775806 at bad
  exact (by decide : (-9223372036854775810 : Int) ≠ 9223372036854775806) bad
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Partial target 45: conversion of the first endpoint fails before allocation or reads. -/
theorem reverseStartInexact {α : Type} (ops : round4.BigIntegerOps) (hops : ops.Lawful)
    (xs : List (Option α)) (start stop : round4.IntegerValue) (hs : ¬start.fits) :
    (round4.heapReverse (α := α) ops start stop).run [xs] = .error .inexact := by
  have hc : start.toInt ops = .error .inexact := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_neg hs
  simp only [round4.heapReverse, JuliaLean.base.array.reverse, hc,
    vector_bind_run]
  rfl

/-- Partial target 45: the second endpoint is converted immediately after the first. -/
theorem reverseStopInexact {α : Type} (ops : round4.BigIntegerOps) (hops : ops.Lawful)
    (xs : List (Option α)) (start stop : round4.IntegerValue)
    (hs : start.fits) (ht : ¬stop.fits) :
    (round4.heapReverse (α := α) ops start stop).run [xs] = .error .inexact := by
  have hc : start.toInt ops = .ok (JInt.wrap .i64 start.val) := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos hs
  have hd : stop.toInt ops = .error .inexact := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_neg ht
  simp only [round4.heapReverse, JuliaLean.base.array.reverse, hc, hd,
    vector_bind_run]
  rfl
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Reading an original source slot, including both kinds of read error. -/
def copyPairRead {α : Type} (source : List (Option α)) (i : I) : Except Error α := do
  match ← vectorGet source i with
  | none => .error .undefinedReference
  | some x => .ok x

/-- The read sequence associated with a destination/source pair plan. -/
def copyPairValues {α : Type} (source : List (Option α)) (keys : List (I × I)) :
    Except Error (List α) := keys.mapM (fun key => copyPairRead source key.2)

/-- The actual source reads and destination stores performed by a reversal phase. -/
def copyPairs {α : Type} (keys : List (I × I)) : VectorM α Unit :=
  forIn keys () fun key _ => do
    heapSet 1 (← heapGet 0 key.2) key.1
    pure (.yield ())

/-- A plan writes consecutive destination slots after a prefix of length `n`. -/
def copyPairsOrder (n : Nat) : List (I × I) → Prop
  | [] => True
  | key :: keys => key.1.val = (n : Int) + 1 ∧ copyPairsOrder (n + 1) keys

theorem copyPairsOrder_get (n : Nat) (keys : List (I × I)) :
    copyPairsOrder n keys ↔
      ∀ (j : Nat) (hj : j < keys.length), (keys[j]).1.val = (n : Int) + j + 1 := by
  induction keys generalizing n with
  | nil =>
    constructor
    · intro _ j hj
      simp only [List.length_nil] at hj
      omega
    · intro _
      trivial
  | cons key keys ih =>
    constructor
    · rintro ⟨hfirst, htail⟩ j hj
      cases j with
      | zero =>
        simpa only [List.getElem_cons_zero, Int.natCast_zero, Int.add_zero] using hfirst
      | succ j =>
        have hj' : j < keys.length := by simp only [List.length_cons] at hj; omega
        have hv := (ih (n + 1)).mp htail j hj'
        simp only [List.getElem_cons_succ, Int.natCast_add, Int.natCast_one,
          Int.natCast_succ] at hv ⊢
        omega
    · intro h
      refine ⟨?_, (ih (n + 1)).mpr ?_⟩
      · have hv := h 0 (by simp only [List.length_cons]; omega)
        change key.1.val = (n : Int) + 0 + 1 at hv
        simpa only [Int.add_zero] using hv
      · intro j hj
        have hv := h (j + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ, Int.natCast_add, Int.natCast_one] at hv ⊢
        omega

/-- A destination list equal to the ordinary one-based positions satisfies the loop order. -/
theorem copyPairsOrder_of_destinations (keys : List (I × I))
    (hn : keys.length < 2 ^ 62)
    (hd : keys.map Prod.fst =
      (List.range keys.length).map (fun (k : Nat) => JInt.wrap .i64 ((k : Int) + 1))) :
    copyPairsOrder 0 keys := by
  apply (copyPairsOrder_get 0 keys).mpr
  intro j hj
  have hv := congrArg (fun (is : List I) => is[j]?) hd
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getElem?_range hj] at hv
  have hindex : (keys[j]).1 = JInt.wrap .i64 ((j : Int) + 1) := Option.some.inj hv
  rw [hindex, ival_wrap _ (by omega)]
  omega

/-- Each prefix of a consecutive plan is itself a consecutive plan. -/
theorem copyPairsOrder_prefix (n : Nat) (left right : List (I × I))
    (h : copyPairsOrder n (left ++ right)) : copyPairsOrder n left := by
  induction left generalizing n with
  | nil => trivial
  | cons key keys ih =>
    exact ⟨h.1, ih (n + 1) h.2⟩

/-- A successful sequence has exactly one value for each source read. -/
theorem copyPairValues_length {α : Type} (source : List (Option α))
    (keys : List (I × I)) (values : List α)
    (h : copyPairValues source keys = .ok values) : values.length = keys.length :=
  converted_length (fun (key : I × I) => copyPairRead source key.2) keys values h

theorem copyPairs_nil {α : Type} : copyPairs (α := α) [] = pure () := rfl

theorem copyPairs_cons {α : Type} (key : I × I) (keys : List (I × I)) :
    copyPairs (α := α) (key :: keys) = (do
      heapSet 1 (← heapGet 0 key.2) key.1
      copyPairs keys) := by
  simp only [copyPairs, List.forIn_cons, bind_assoc, pure_bind]

/-- Reversal's three phases can be concatenated without changing evaluation order. -/
theorem copyPairs_append {α : Type} (left right : List (I × I)) :
    copyPairs (α := α) (left ++ right) = (do
      copyPairs left
      copyPairs right) := by
  induction left with
  | nil => simp only [List.nil_append, copyPairs_nil, pure_bind]
  | cons key keys ih =>
    simp only [List.cons_append, copyPairs_cons, ih, bind_assoc]

/-- Mapping each loop index to its destination/source pair preserves the original loop. -/
theorem copyPairs_map {α : Type} (indices : List I) (source : I → I) :
    copyPairs (α := α) (indices.map (fun i => (i, source i))) =
      (forIn indices PUnit.unit (fun i _ => do
        heapSet 1 (← heapGet 0 (source i)) i
        pure (ForInStep.yield PUnit.unit)) : VectorM α PUnit) := by
  simp only [copyPairs, List.forIn_map]

/-- Stores into handle 1 leave reads from handle 0 equal to the original source list. -/
theorem copyPairRead_run {α : Type} (source out : List (Option α)) (i : I) :
    (heapGet (α := α) 0 i).run [source, out] =
      (copyPairRead source i).map (fun x => (x, [source, out])) := by
  simp only [heapGet, vector_bind_run, heapSlots_run, List.getElem?_cons_zero,
    vector_lift_run]
  cases hr : vectorGet source i with
  | error e =>
    simp only [hr, Except.map]
    simp only [copyPairRead, hr, Bind.bind, Except.bind, Except.map]
  | ok slot =>
    cases slot with
    | none =>
      simp only [hr, Except.map, vector_throw_run]
      simp only [copyPairRead, hr, Bind.bind, Except.bind, Except.map]
    | some x =>
      simp only [hr, Except.map, vector_pure_run]
      simp only [copyPairRead, hr, Bind.bind, Except.bind, Except.map]

/-- Sequential copies preserve the source, retain the unwritten tail, and propagate read errors. -/
theorem copyPairs_run {α : Type} (source : List (Option α)) (keys : List (I × I)) :
    ∀ (pre : List α) (tail : List (Option α)),
      copyPairsOrder pre.length keys → keys.length ≤ tail.length →
      pre.length + tail.length < 2 ^ 62 →
      (copyPairs (α := α) keys).run [source, pre.map some ++ tail] =
        (copyPairValues source keys).map (fun values =>
          ((), [source, (pre ++ values).map some ++ tail.drop values.length])) := by
  induction keys with
  | nil =>
    intro pre tail _ _ _
    rw [copyPairs_nil, vector_pure_run]
    simp only [copyPairValues, List.mapM_nil,
      Pure.pure, Except.pure, Except.map, List.append_nil, List.length_nil, List.drop_zero]
  | cons key keys ih =>
    intro pre tail horder hroom hsmall
    cases tail with
    | nil => simp only [List.length_cons, List.length_nil] at hroom; omega
    | cons old tail =>
      have hd : key.1 = JInt.wrap .i64 ((pre.length : Int) + 1) := by
        apply Subtype.ext
        rw [ival_wrap _ (by simp only [List.length_cons] at hsmall; omega)]
        exact horder.1
      cases hr : copyPairRead source key.2 with
      | error e =>
        simp only [copyPairs_cons, vector_bind_run, copyPairRead_run, hr, Except.map]
        simp only [copyPairValues, List.mapM_cons, hr, Bind.bind, Except.bind, Except.map]
      | ok x =>
        have hstore := ChatGPTBatch1.ArrayFilter.batch1_filterStore [source] pre old tail x hsmall
        change (heapSet 1 x (JInt.wrap .i64 ((pre.length : Int) + 1))).run
            [source, pre.map some ++ old :: tail] =
          .ok ((), [source, pre.map some ++ some x :: tail]) at hstore
        have hslots : pre.map some ++ some x :: tail = (pre ++ [x]).map some ++ tail := by
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append]
        have horder' : copyPairsOrder (pre ++ [x]).length keys := by
          simpa only [List.length_append, List.length_singleton] using horder.2
        have hroom' : keys.length ≤ tail.length := by
          simp only [List.length_cons] at hroom
          omega
        have hsmall' : (pre ++ [x]).length + tail.length < 2 ^ 62 := by
          simp only [List.length_append, List.length_singleton, List.length_cons,
            List.length_nil] at hsmall ⊢
          omega
        rw [copyPairs_cons]
        simp only [vector_bind_run, copyPairRead_run, hr, Except.map]
        rw [hd, hstore, hslots]
        dsimp only
        rw [ih (pre ++ [x]) tail horder' hroom' hsmall']
        simp only [copyPairValues, List.mapM_cons, hr, Bind.bind, Except.bind]
        cases ht : keys.mapM (fun (key : I × I) => copyPairRead source key.2) with
        | error e => simp only [ht, Except.map, Bind.bind, Except.bind]
        | ok values =>
          simp only [ht, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_assoc,
            List.singleton_append, List.length_cons, List.drop_succ_cons]

/-- A later length lookup still observes the untouched source after any copying prefix. -/
theorem copyPairs_then_length {α β : Type} (source : List (Option α))
    (keys : List (I × I)) (pre : List α) (tail : List (Option α))
    (horder : copyPairsOrder pre.length keys) (hroom : keys.length ≤ tail.length)
    (hsmall : pre.length + tail.length < 2 ^ 62) (next : I → VectorM α β) :
    (do
      copyPairs (α := α) keys
      let n ← heapLength 0
      next n).run [source, pre.map some ++ tail] =
    (do
      copyPairs (α := α) keys
      next (JInt.wrap .i64 source.length)).run [source, pre.map some ++ tail] := by
  simp only [vector_bind_run, copyPairs_run source keys pre tail horder hroom hsmall]
  cases h : copyPairValues source keys with
  | error e => simp only [h, Except.map]
  | ok values =>
    simp only [h, Except.map, heapLength_run, List.getElem?_cons_zero]
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The three source loops, with destination and source positions kept together. -/
def reverseWindowPairs (before middle after : Nat) : List (I × I) :=
  (List.range before).map (fun (k : Nat) =>
      (JInt.wrap .i64 ((k : Int) + 1), JInt.wrap .i64 ((k : Int) + 1))) ++
  (List.range middle).map (fun (k : Nat) =>
      (JInt.wrap .i64 ((before : Int) + k + 1),
       JInt.wrap .i64 ((before : Int) + middle - k))) ++
  (List.range after).map (fun (k : Nat) =>
      (JInt.wrap .i64 ((before : Int) + middle + k + 1),
       JInt.wrap .i64 ((before : Int) + middle + k + 1)))

/-- Reading consecutive valid positions recovers the corresponding slice, including holes. -/
theorem reverseSliceSlots (xs : List (Option α)) (offset count : Nat)
    (h : offset + count ≤ xs.length) :
    (List.range count).map (fun (k : Nat) => xs[offset + k]?.join) =
      (xs.drop offset).take count := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro k hk hk'
    have hkcount : k < count := by simpa only [List.length_map, List.length_range] using hk
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl

/-- Reading a valid slice backwards recovers its reversal, including holes. -/
theorem reverseSliceSlotsBackwards (xs : List (Option α)) (offset count : Nat)
    (h : offset + count ≤ xs.length) :
    (List.range count).map (fun (k : Nat) => xs[offset + (count - 1 - k)]?.join) =
      ((xs.drop offset).take count).reverse := by
  have hlen : ((xs.drop offset).take count).length = count := by
    simp only [List.length_take, List.length_drop]
    omega
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_reverse, hlen]
  · intro k hk hk'
    have hkcount : k < count := by simpa only [List.length_map, List.length_range] using hk
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, hlen,
      List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl

/-- Range enumeration agrees with ordinary consecutive natural positions in this size domain. -/
theorem reverseIntRange (offset count : Nat) (hn : offset + count < 2 ^ 62) :
    intRange (JInt.wrap .i64 ((offset : Int) + 1))
      (JInt.wrap .i64 ((offset : Int) + count)) =
      (List.range count).map (fun (k : Nat) => JInt.wrap .i64 ((offset : Int) + k + 1)) := by
  rw [intRange, ival_wrap _ (by omega), ival_wrap _ (by omega)]
  have hc : (((offset : Int) + count - (offset + 1) + 1).toNat) = count := by omega
  rw [hc]
  apply List.map_congr_left
  intro k _
  congr 1
  omega

/-- Every destination is written exactly once, in increasing order. -/
theorem reverseWindowPairs_destinations (before middle after : Nat) :
    (reverseWindowPairs before middle after).map Prod.fst =
      (List.range (before + middle + after)).map (fun (k : Nat) => JInt.wrap .i64 ((k : Int) + 1)) := by
  simp only [reverseWindowPairs, List.map_append, List.map_map, Function.comp_def,
    List.range_add]
  congr 1

/-- All source positions in the three-loop plan are inside the original vector. -/
theorem reverseWindowPairs_sources (before middle after : Nat)
    (hn : before + middle + after < 2 ^ 62) :
    ∀ pair ∈ reverseWindowPairs before middle after,
      1 ≤ pair.2.val ∧ pair.2.val ≤ (before + middle + after : Nat) := by
  intro pair hp
  simp only [reverseWindowPairs, List.mem_append, List.mem_map, List.mem_range] at hp
  rcases hp with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
  · rw [ival_wrap _ (by omega)]
    omega
  · rw [ival_wrap _ (by omega)]
    omega
  · rw [ival_wrap _ (by omega)]
    omega

/-- The copy plan reads exactly the specified prefix, reversed middle, and suffix. -/
theorem reverseWindowPairs_slots (xs : List (Option α)) (before middle after : Nat)
    (hlen : xs.length = before + middle + after) (hn : xs.length < 2 ^ 62) :
    (reverseWindowPairs before middle after).map
      (fun pair => xs[(pair.2.val - 1).toNat]?.join) =
      xs.take before ++ ((xs.drop before).take middle).reverse ++ xs.drop (before + middle) := by
  have hpre : (List.range before).map
      (fun (k : Nat) => xs[((JInt.wrap .i64 ((k : Int) + 1)).val - 1).toNat]?.join) =
      xs.take before := by
    have hm : (List.range before).map
        (fun (k : Nat) => xs[((JInt.wrap .i64 ((k : Int) + 1)).val - 1).toNat]?.join) =
        (List.range before).map (fun (k : Nat) => xs[0 + k]?.join) := by
      apply List.map_congr_left
      intro k hk
      have hk' := List.mem_range.mp hk
      rw [ival_wrap _ (by omega)]
      congr 2
      omega
    rw [hm, reverseSliceSlots xs 0 before (by omega), List.drop_zero]
  have hmid : (List.range middle).map
      (fun (k : Nat) => xs[((JInt.wrap .i64 ((before : Int) + middle - k)).val - 1).toNat]?.join) =
      ((xs.drop before).take middle).reverse := by
    have hm : (List.range middle).map
        (fun (k : Nat) => xs[((JInt.wrap .i64 ((before : Int) + middle - k)).val - 1).toNat]?.join) =
        (List.range middle).map (fun (k : Nat) => xs[before + (middle - 1 - k)]?.join) := by
      apply List.map_congr_left
      intro k hk
      have hk' := List.mem_range.mp hk
      rw [ival_wrap _ (by omega)]
      congr 2
      omega
    rw [hm, reverseSliceSlotsBackwards xs before middle (by omega)]
  have hpost : (List.range after).map
      (fun (k : Nat) => xs[((JInt.wrap .i64 ((before : Int) + middle + k + 1)).val - 1).toNat]?.join) =
      xs.drop (before + middle) := by
    have hm : (List.range after).map
        (fun (k : Nat) => xs[((JInt.wrap .i64 ((before : Int) + middle + k + 1)).val - 1).toNat]?.join) =
        (List.range after).map (fun (k : Nat) => xs[(before + middle) + k]?.join) := by
      apply List.map_congr_left
      intro k hk
      have hk' := List.mem_range.mp hk
      rw [ival_wrap _ (by omega)]
      congr 2
      omega
    rw [hm, reverseSliceSlots xs (before + middle) after (by omega)]
    apply List.take_of_length_le
    simp only [List.length_drop]
    omega
  simpa only [reverseWindowPairs, List.map_append, List.map_map, Function.comp_def,
    hpre, hmid, hpost]


/-- The natural three-part description is exactly the source's three integer ranges. -/
theorem reverseWindowPairs_model (s t : I) (n : Nat)
    (hn : n < 2 ^ 62) (hs : 1 ≤ s.val) (hst : s.val ≤ t.val + 1)
    (ht : t.val ≤ (n : Int)) :
    ((intRange one (s - one)).map (fun i => (i, i)) ++
      (intRange s t).map (fun i => (i, t + s - i)) ++
      (intRange (t + one) (JInt.wrap .i64 n)).map (fun i => (i, i))) =
      reverseWindowPairs (s.val - 1).toNat (t.val - s.val + 1).toNat
        ((n : Int) - t.val).toNat := by
  let before := (s.val - 1).toNat
  let middle := (t.val - s.val + 1).toNat
  let after := ((n : Int) - t.val).toNat
  have hb : (before : Int) = s.val - 1 := by dsimp only [before]; omega
  have hm : (middle : Int) = t.val - s.val + 1 := by dsimp only [middle]; omega
  have ha : (after : Int) = (n : Int) - t.val := by dsimp only [after]; omega
  have hlen : before + middle + after = n := by omega
  have hpre : intRange one (s - one) =
      (List.range before).map (fun (k : Nat) => JInt.wrap .i64 ((k : Int) + 1)) := by
    rw [intRange, ival_one, ival_sub_one s (by omega)]
    have hc : (s.val - 1 - 1 + 1).toNat = before := by dsimp only [before]; omega
    rw [hc]
    apply List.map_congr_left
    intro k _
    congr 1
    omega
  have hpost : intRange (t + one) (JInt.wrap .i64 n) =
      (List.range after).map
        (fun (k : Nat) => JInt.wrap .i64 ((before : Int) + middle + k + 1)) := by
    rw [intRange, ival_add_one t (by omega), ival_wrap _ (by omega)]
    have hc : ((n : Int) - (t.val + 1) + 1).toNat = after := by
      dsimp only [after]
      omega
    rw [hc]
    apply List.map_congr_left
    intro k _
    congr 1
    omega
  have hmiddle : (intRange s t).map (fun i => (i, t + s - i)) =
      (List.range middle).map (fun (k : Nat) =>
        (JInt.wrap .i64 ((before : Int) + k + 1),
         JInt.wrap .i64 ((before : Int) + middle - k))) := by
    simp only [intRange, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro k hk
    have hk' : k < middle := List.mem_range.mp hk
    have hkv : (JInt.wrap .i64 (s.val + k)).val = s.val + k :=
      ival_wrap _ (by omega)
    apply Prod.ext
    · apply Subtype.ext
      change (JInt.wrap .i64 (s.val + (k : Int))).val =
        (JInt.wrap .i64 ((before : Int) + k + 1)).val
      rw [hkv, ival_wrap _ (by omega)]
      omega
    · apply Subtype.ext
      change (t + s - JInt.wrap .i64 (s.val + (k : Int))).val =
        (JInt.wrap .i64 ((before : Int) + middle - k)).val
      rw [ival_add_sub _ _ _ (by rw [hkv]; omega), hkv, ival_wrap _ (by omega)]
      omega
  change _ = reverseWindowPairs before middle after
  rw [hpre, hmiddle, hpost]
  simp only [reverseWindowPairs, List.map_map, Function.comp_def]

/-- The three lengths cover the whole source and have exactly the documented window result. -/
theorem reverseWindow_decomposition (xs : List (Option α)) (s t : Int)
    (hs : 1 ≤ s) (hst : s ≤ t + 1) (ht : t ≤ (xs.length : Int)) :
    let before := (s - 1).toNat
    let middle := (t - s + 1).toNat
    let after := ((xs.length : Int) - t).toNat
    xs.length = before + middle + after ∧
    round4.reverseWindow xs s t =
      xs.take before ++ ((xs.drop before).take middle).reverse ++ xs.drop (before + middle) := by
  dsimp only
  have hsum : (s - 1).toNat + (t - s + 1).toNat = t.toNat := by omega
  constructor
  · omega
  · rw [round4.reverseWindow, hsum]
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The only possible error when a known in-bounds slot is read. -/
def reverseRequireSlot : Option α → Except Error α
  | none => .error .undefinedReference
  | some x => .ok x

theorem reverseReadSlot (xs : List (Option α)) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ (xs.length : Int)) :
    copyPairRead xs i = reverseRequireSlot (xs[(i.val - 1).toNat]?.join) := by
  have hk : (i.val - 1).toNat < xs.length := by omega
  simp only [copyPairRead, vectorGet, if_pos hi, List.getElem?_eq_getElem hk,
    Bind.bind, Except.bind, Option.join_some]
  cases xs[(i.val - 1).toNat] <;> rfl

/-- Reading an in-bounds plan is precisely a left-to-right read of its selected slots. -/
theorem reverseReadPlan (xs : List (Option α)) (keys : List (I × I))
    (hi : ∀ key ∈ keys, 1 ≤ key.2.val ∧ key.2.val ≤ (xs.length : Int)) :
    copyPairValues xs keys =
      (keys.map (fun key => xs[(key.2.val - 1).toNat]?.join)).mapM reverseRequireSlot := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    have hh := reverseReadSlot xs key.2 (hi key (List.mem_cons_self ..))
    have ht := ih (fun k hk => hi k (List.mem_cons_of_mem _ hk))
    simp only [copyPairValues, List.mapM_cons, List.map_cons] at ht ⊢
    rw [hh, ht]

/-- Every assigned sequence has a successful read with exactly the original slots. -/
theorem reverseReadAssigned (slots : List (Option α))
    (ha : ∀ slot ∈ slots, slot.isSome) :
    ∃ values, slots.mapM reverseRequireSlot = .ok values ∧ values.map some = slots := by
  induction slots with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons slot slots ih =>
    have hh := ha slot (List.mem_cons_self ..)
    have ht := ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    cases slot with
    | none => cases hh
    | some x =>
      obtain ⟨values, hv, hs⟩ := ht
      refine ⟨x :: values, ?_, ?_⟩
      · simp only [List.mapM_cons, reverseRequireSlot, hv, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · rw [List.map_cons, hs]

/-- Any hole is eventually read and produces the undefined-reference exception. -/
theorem reverseReadUnassigned (slots : List (Option α)) (h : none ∈ slots) :
    slots.mapM reverseRequireSlot = .error .undefinedReference := by
  induction slots with
  | nil => cases h
  | cons slot slots ih =>
    cases slot with
    | none => simp only [List.mapM_cons, reverseRequireSlot, Bind.bind, Except.bind]
    | some x =>
      have ht : none ∈ slots := by simpa only [List.mem_cons, reduceCtorEq, false_or] using h
      simp only [List.mapM_cons, reverseRequireSlot, ih ht, Bind.bind, Except.bind]

/-- Reversing the middle slice preserves membership, even for unassigned slots. -/
theorem reverseSlices_mem (xs : List α) (before middle : Nat) (x : α) :
    x ∈ xs.take before ++ ((xs.drop before).take middle).reverse ++ xs.drop (before + middle) ↔
      x ∈ xs := by
  have hsplit : xs.take before ++ (xs.drop before).take middle ++ xs.drop (before + middle) = xs := by
    rw [← List.take_add, List.take_append_drop]
  calc
    x ∈ xs.take before ++ ((xs.drop before).take middle).reverse ++ xs.drop (before + middle) ↔
        x ∈ xs.take before ++ (xs.drop before).take middle ++ xs.drop (before + middle) := by
          simp only [List.mem_append, List.mem_reverse]
    _ ↔ x ∈ xs := by rw [hsplit]

/-- The result has the original length when the selected window is valid. -/
theorem reverseWindow_length (xs : List α) (s t : Int)
    (hs : 1 ≤ s) (hst : s ≤ t + 1) (ht : t ≤ (xs.length : Int)) :
    (round4.reverseWindow xs s t).length = xs.length := by
  simp only [round4.reverseWindow, List.length_append, List.length_take,
    List.length_reverse, List.length_drop]
  omega


/-- The source's three loops fill a fresh vector according to their complete read plan. -/
theorem reverseFixedPlanRun (xs : List (Option α)) (s t : I)
    (hn : xs.length < 2 ^ 62) (hs : 1 ≤ s.val) (hst : s.val ≤ t.val + 1)
    (ht : t.val ≤ (xs.length : Int)) :
    (JuliaLean.base.array.reverse (m := VectorM α)
      (fun i : I => pure i) (fun i : I => pure i)
      heapSimilar (fun _ => pure one) heapLength heapGet heapSet 0 s t).run [xs] =
      (copyPairValues xs (reverseWindowPairs (s.val - 1).toNat
        (t.val - s.val + 1).toNat ((xs.length : Int) - t.val).toNat)).map
        (fun values => (1, [xs, values.map some])) := by
  let left := (intRange one (s - one)).map (fun i => (i, i))
  let middle := (intRange s t).map (fun i => (i, t + s - i))
  let right := (intRange (t + one) (JInt.wrap .i64 xs.length)).map (fun i => (i, i))
  let keys := left ++ middle ++ right
  have hmodel : keys = reverseWindowPairs (s.val - 1).toNat
      (t.val - s.val + 1).toNat ((xs.length : Int) - t.val).toNat :=
    reverseWindowPairs_model s t xs.length hn hs hst ht
  have hd := reverseWindow_decomposition xs s.val t.val hs hst ht
  have hlen : keys.length = xs.length := by
    rw [hmodel]
    simp only [reverseWindowPairs, List.length_append, List.length_map, List.length_range]
    exact hd.1.symm
  have horder : copyPairsOrder 0 keys := by
    apply copyPairsOrder_of_destinations keys (by rw [hlen]; exact hn)
    rw [hmodel]
    simpa only [reverseWindowPairs, List.length_append, List.length_map, List.length_range] using
      reverseWindowPairs_destinations (s.val - 1).toNat (t.val - s.val + 1).toNat
        ((xs.length : Int) - t.val).toNat
  have hprefix : copyPairsOrder 0 (left ++ middle) :=
    copyPairsOrder_prefix 0 (left ++ middle) right horder
  have hroom : (left ++ middle).length ≤ xs.length := by
    dsimp only [keys] at hlen
    simp only [List.length_append] at hlen ⊢
    omega
  have hsimilar : (heapSimilar (α := α) 0).run [xs] =
      .ok (1, [xs, List.replicate xs.length none]) := rfl
  unfold JuliaLean.base.array.reverse
  simp only [pure_bind]
  rw [vector_bind_run, hsimilar]
  simp only [pure_bind, ← copyPairs_map]
  rw [← bind_assoc, ← copyPairs_append]
  have hlengthRun := copyPairs_then_length xs (left ++ middle) [] (List.replicate xs.length none)
    hprefix (by simpa only [List.length_replicate] using hroom)
    (by simpa only [List.length_nil, List.length_replicate, Nat.zero_add] using hn)
    (fun n => do
      copyPairs ((intRange (t + one) n).map (fun i => (i, i)))
      pure (1 : Nat))
  simp only [List.map_nil, List.nil_append] at hlengthRun
  rw [hlengthRun]
  rw [← bind_assoc, ← copyPairs_append]
  change ((do copyPairs keys; pure 1) : VectorM α Nat).run
      [xs, List.replicate xs.length none] = _
  have hrun := copyPairs_run xs keys [] (List.replicate xs.length none) horder
    (by rw [List.length_replicate, hlen]; exact Nat.le_refl _)
    (by simpa only [List.length_nil, List.length_replicate, Nat.zero_add] using hn)
  simp only [List.map_nil, List.nil_append] at hrun
  rw [vector_bind_run, hrun, ← hmodel]
  cases hv : copyPairValues xs keys with
  | error e => rfl
  | ok values =>
    have hl : values.length = xs.length := (copyPairValues_length xs keys values hv).trans hlen
    have hdrop : (List.replicate xs.length (none : Option α)).drop values.length = [] := by
      apply List.drop_eq_nil_iff.mpr
      rw [List.length_replicate, hl]
      exact Nat.le_refl _
    simp only [Except.map, List.nil_append, hdrop, List.append_nil, vector_pure_run]

/-- Out-of-place reversal reads every source slot and writes the exact reversed window. -/
theorem MultidimcovArrayV2ReverseWindow_proven :
    JuliaLean.Proofs.base.array.round4.ReverseWindowSpec := by
  intro α ops hops xs start stop hn
  refine ⟨reverseStartInexact ops hops xs start stop, reverseStopInexact ops hops xs start stop, ?_⟩
  intro hs hst ht
  have hsfit : start.fits := by
    change -9223372036854775808 ≤ start.val ∧ start.val ≤ 9223372036854775807
    omega
  have htfit : stop.fits := by
    change -9223372036854775808 ≤ stop.val ∧ stop.val ≤ 9223372036854775807
    omega
  let s : I := JInt.wrap .i64 start.val
  let t : I := JInt.wrap .i64 stop.val
  have hsv : s.val = start.val := ival_wrap _ (by omega)
  have htv : t.val = stop.val := ival_wrap _ (by omega)
  have hc : start.toInt ops = .ok s := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos hsfit
  have he : stop.toInt ops = .ok t := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos htfit
  have hfixed : (round4.heapReverse (α := α) ops start stop).run [xs] =
      (JuliaLean.base.array.reverse (m := VectorM α)
        (fun i : I => pure i) (fun i : I => pure i)
        heapSimilar (fun _ => pure one) heapLength heapGet heapSet 0 s t).run [xs] := by
    simp only [round4.heapReverse, JuliaLean.base.array.reverse, vector_bind_run,
      vector_lift_run, hc, he, Except.map, vector_pure_run]
    rfl
  have hr := reverseFixedPlanRun xs s t hn (by rw [hsv]; exact hs)
    (by rw [hsv, htv]; exact hst) (by rw [htv]; exact ht)
  rw [hfixed, hr]
  rw [hsv, htv]
  let before := (start.val - 1).toNat
  let middle := (stop.val - start.val + 1).toNat
  let after := ((xs.length : Int) - stop.val).toNat
  have hdecomp := reverseWindow_decomposition xs start.val stop.val hs hst ht
  have hlength : xs.length = before + middle + after := hdecomp.1
  have hreads := reverseReadPlan xs (reverseWindowPairs before middle after)
    (by
      intro key hk
      have hb := reverseWindowPairs_sources before middle after (by rw [← hlength]; exact hn) key hk
      simpa only [← hlength] using hb)
  rw [hreads, reverseWindowPairs_slots xs before middle after hlength hn]
  constructor
  · intro hassign
    obtain ⟨values, hread, hslots⟩ := reverseReadAssigned
      (xs.take before ++ ((xs.drop before).take middle).reverse ++ xs.drop (before + middle))
      (fun slot hmem => hassign slot ((reverseSlices_mem xs before middle slot).mp hmem))
    rw [hread]
    simp only [Except.map, hslots]
    rw [hdecomp.2]
  · intro hnone
    have hread := reverseReadUnassigned
      (xs.take before ++ ((xs.drop before).take middle).reverse ++ xs.drop (before + middle))
      ((reverseSlices_mem xs before middle none).mpr hnone)
    rw [hread]
    rfl
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


/- Allocation and collection partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192




/- Complete sorted deletion and splice proof -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxHeartbeats 600000
set_option maxRecDepth 4096

/-- The first endpoint is converted before all heap access. -/
theorem reverseBangStartInexact {α : Type} (ops : round4.BigIntegerOps)
    (hops : ops.Lawful) (heap : VectorHeap α) (start stop : round4.IntegerValue)
    (hs : ¬ start.fits) :
    (round4.heapReverseBang (α := α) ops start stop).run heap = .error .inexact := by
  have hc : start.toInt ops = .error .inexact := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_neg hs
  simp only [round4.heapReverseBang, reverseBang, hc, vector_bind_run]
  rfl

/-- The second endpoint is converted before all heap access. -/
theorem reverseBangStopInexact {α : Type} (ops : round4.BigIntegerOps)
    (hops : ops.Lawful) (heap : VectorHeap α) (start stop : round4.IntegerValue)
    (hs : start.fits) (ht : ¬ stop.fits) :
    (round4.heapReverseBang (α := α) ops start stop).run heap = .error .inexact := by
  have hc : start.toInt ops = .ok (JInt.wrap .i64 start.val) := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos hs
  have hd : stop.toInt ops = .error .inexact := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_neg ht
  simp only [round4.heapReverseBang, reverseBang, hc, hd, vector_bind_run]
  rfl

/-- An empty or singleton reversal returns before bounds checks and heap reads. -/
theorem reverseBangNoop {α : Type} (ops : round4.BigIntegerOps)
    (hops : ops.Lawful) (heap : VectorHeap α) (start stop : round4.IntegerValue)
    (hs : start.fits) (ht : stop.fits) (hle : stop.val ≤ start.val) :
    (round4.heapReverseBang (α := α) ops start stop).run heap = .ok (0, heap) := by
  have hc : start.toInt ops = .ok (JInt.wrap .i64 start.val) := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos hs
  have hd : stop.toInt ops = .ok (JInt.wrap .i64 stop.val) := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos ht
  have hnot : ¬ JInt.wrap .i64 stop.val > JInt.wrap .i64 start.val := by
    change ¬ (JInt.wrap .i64 start.val).val < (JInt.wrap .i64 stop.val).val
    rw [ival_wrap _ hs, ival_wrap _ ht]
    omega
  simp only [round4.heapReverseBang, reverseBang, hc, hd, vector_bind_run]
  change ((if JInt.wrap .i64 stop.val > JInt.wrap .i64 start.val then _ else pure 0) : VectorM α Nat).run heap = _
  rw [if_neg hnot]
  rfl

/-- The complete bounds-error clause of the frozen contract, before swaps start. -/
theorem reverseBangBounds {α : Type} (ops : round4.BigIntegerOps)
    (hops : ops.Lawful) (xs : List (Option α)) (start stop : round4.IntegerValue)
    (hlen : xs.length < 2 ^ 62) (hs : start.fits) (ht : stop.fits)
    (hlt : start.val < stop.val) (hbad : ¬ (1 ≤ start.val ∧ stop.val ≤ xs.length)) :
    (round4.heapReverseBang (α := α) ops start stop).run [xs] = .error .bounds := by
  have hc : start.toInt ops = .ok (JInt.wrap .i64 start.val) := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos hs
  have hd : stop.toInt ops = .ok (JInt.wrap .i64 stop.val) := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos ht
  have hsv : (JInt.wrap .i64 start.val).val = start.val := ival_wrap _ hs
  have htv : (JInt.wrap .i64 stop.val).val = stop.val := ival_wrap _ ht
  have hnv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length :=
    ival_wrap _ (by omega)
  have hgt : JInt.wrap .i64 stop.val > JInt.wrap .i64 start.val := by
    change (JInt.wrap .i64 start.val).val < (JInt.wrap .i64 stop.val).val
    rw [hsv, htv]
    exact hlt
  simp only [round4.heapReverseBang, reverseBang, hc, hd, vector_bind_run]
  change ((if JInt.wrap .i64 stop.val > JInt.wrap .i64 start.val then _ else pure 0) :
    VectorM α Nat).run [xs] = _
  rw [if_pos hgt]
  by_cases hsl : 1 ≤ start.val
  · by_cases hsu : start.val ≤ xs.length
    · have htl : 1 ≤ stop.val := by omega
      have htu : ¬ stop.val ≤ xs.length := by omega
      simp only [vector_bind_run, vector_pure_run, jle_iff, ival_one, hsv, htv,
        hsl, not_true_eq_false, ite_false, heapLength_run, List.getElem?_cons_zero,
        hnv, hsu, decide_true, Bool.not_true, Bool.false_eq_true, htl, htu,
        decide_false, Bool.not_false, ite_true, vector_throw_run]
    · simp only [vector_bind_run, vector_pure_run, jle_iff, ival_one, hsv, hsl,
        not_true_eq_false, ite_false, heapLength_run, List.getElem?_cons_zero,
        hnv, hsu, decide_false, Bool.not_false, ite_true, vector_throw_run]
  · simp only [vector_bind_run, vector_pure_run, jle_iff, ival_one, hsv, hsl,
      not_false_eq_true, ite_true, Bool.not_false, vector_throw_run]

/-- One source loop iteration: read right, read left, then write both slots. -/
def reverseBangSwapStep {α : Type} (handle : Nat) (left right : I) :
    VectorM α (ForInStep I) := do
  let rightValue ← heapGet handle right
  let leftValue ← heapGet handle left
  heapSet handle rightValue left
  heapSet handle leftValue right
  pure (.yield (right - one))

/-- Exact successful behavior of a single swap, with no premise on other slots. -/
theorem reverseBangSwapAssigned {α : Type} (xs : List (Option α)) (left right : I)
    (hl : 1 ≤ left.val ∧ left.val ≤ xs.length)
    (hr : 1 ≤ right.val ∧ right.val ≤ xs.length) (x y : α)
    (hxl : xs[(left.val - 1).toNat]? = some (some x))
    (hyr : xs[(right.val - 1).toNat]? = some (some y)) :
    (reverseBangSwapStep 0 left right).run [xs] =
      .ok (.yield (right - one),
        [(xs.set (left.val - 1).toNat (some y)).set (right.val - 1).toNat (some x)]) := by
  have hreadR := heapGet_run [xs] 0 xs rfl right
  rw [if_pos hr, hyr] at hreadR
  have hreadL := heapGet_run [xs] 0 xs rfl left
  rw [if_pos hl, hxl] at hreadL
  have hwriteL := heapSet_run [xs] 0 xs rfl left hl.1 hl.2 y
  have hwriteR := heapSet_run [xs.set (left.val - 1).toNat (some y)] 0
    (xs.set (left.val - 1).toNat (some y)) rfl right hr.1
    (by simpa only [List.length_set] using hr.2) x
  simp only [List.set_cons_zero] at hwriteL hwriteR
  simp only [reverseBangSwapStep, vector_bind_run, hreadR, hreadL,
    hwriteL, hwriteR, vector_pure_run]

/-- A missing right slot fails before the left slot is read. -/
theorem reverseBangSwapRightUndefined {α : Type} (xs : List (Option α)) (left right : I)
    (hr : 1 ≤ right.val ∧ right.val ≤ xs.length)
    (hu : xs[(right.val - 1).toNat]? = some none) :
    (reverseBangSwapStep 0 left right).run [xs] = .error .undefinedReference := by
  have hread := heapGet_run [xs] 0 xs rfl right
  rw [if_pos hr, hu] at hread
  simp only [reverseBangSwapStep, vector_bind_run, hread]

/-- After a successful right read, a missing left slot fails before either write. -/
theorem reverseBangSwapLeftUndefined {α : Type} (xs : List (Option α)) (left right : I)
    (hl : 1 ≤ left.val ∧ left.val ≤ xs.length)
    (hr : 1 ≤ right.val ∧ right.val ≤ xs.length) (y : α)
    (hu : xs[(left.val - 1).toNat]? = some none)
    (hyr : xs[(right.val - 1).toNat]? = some (some y)) :
    (reverseBangSwapStep 0 left right).run [xs] = .error .undefinedReference := by
  have hreadR := heapGet_run [xs] 0 xs rfl right
  rw [if_pos hr, hyr] at hreadR
  have hreadL := heapGet_run [xs] 0 xs rfl left
  rw [if_pos hl, hu] at hreadL
  simp only [reverseBangSwapStep, vector_bind_run, hreadR, hreadL]

/-- With valid endpoints, the frozen implementation is precisely its swap loop. -/
theorem reverseBangValidLoop {α : Type} (ops : round4.BigIntegerOps)
    (hops : ops.Lawful) (xs : List (Option α)) (start stop : round4.IntegerValue)
    (hlen : xs.length < 2 ^ 62) (hs : start.fits) (ht : stop.fits)
    (hlt : start.val < stop.val) (hlo : 1 ≤ start.val) (hhi : stop.val ≤ xs.length) :
    (round4.heapReverseBang (α := α) ops start stop).run [xs] =
      ((do
        let _ ← forIn
          (intRange (JInt.wrap .i64 start.val)
            (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
              JuliaLean.base.int.lshr_BitInteger_BitUnsigned
              (JInt.wrap .i64 start.val) (JInt.wrap .i64 stop.val - one)))
          (JInt.wrap .i64 stop.val) (reverseBangSwapStep 0)
        pure 0) : VectorM α Nat).run [xs] := by
  have hc : start.toInt ops = .ok (JInt.wrap .i64 start.val) := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos hs
  have hd : stop.toInt ops = .ok (JInt.wrap .i64 stop.val) := by
    rw [opusGrowth.integerValue_toInt hops]
    exact if_pos ht
  have hsv : (JInt.wrap .i64 start.val).val = start.val := ival_wrap _ hs
  have htv : (JInt.wrap .i64 stop.val).val = stop.val := ival_wrap _ ht
  have hnv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length :=
    ival_wrap _ (by omega)
  have hgt : JInt.wrap .i64 stop.val > JInt.wrap .i64 start.val := by
    change (JInt.wrap .i64 start.val).val < (JInt.wrap .i64 stop.val).val
    rw [hsv, htv]
    exact hlt
  have hsl : start.val ≤ xs.length := by omega
  have htl : 1 ≤ stop.val := by omega
  simp only [round4.heapReverseBang, reverseBang, hc, hd, vector_bind_run]
  change ((if JInt.wrap .i64 stop.val > JInt.wrap .i64 start.val then _ else pure 0) :
    VectorM α Nat).run [xs] = _
  rw [if_pos hgt]
  simp only [vector_bind_run, vector_pure_run, jle_iff, ival_one, hsv, htv,
    hlo, htl, not_true_eq_false, ite_false, heapLength_run, List.getElem?_cons_zero,
    hnv, hsl, hhi, decide_true, Bool.not_true, Bool.false_eq_true]
  rfl

/-- The last left-hand position is the floor of `(start + stop - 1)/2`. -/
theorem reverseBangMidpointValue (start stop : I)
    (hlo : 1 ≤ start.val) (hlt : start.val < stop.val) :
    (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
      JuliaLean.base.int.lshr_BitInteger_BitUnsigned start (stop - one)).val =
        (start.val + stop.val - 1) / 2 := by
  have hs := ival_bounds start
  have ht := ival_bounds stop
  have hsub : (stop - one).val = stop.val - 1 :=
    ival_sub_one stop (by omega)
  have hmid := bitIntegerMidpointSpec .i64 start (stop - one) (by rw [hsub]; omega)
  rw [hsub] at hmid
  rw [hmid.1]
  congr 1
  omega

/-- There are exactly half as many swaps as window slots, rounded down. -/
theorem reverseBangSwapCount (start stop : I)
    (hlo : 1 ≤ start.val) (hlt : start.val < stop.val) :
    (intRange start (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
      JuliaLean.base.int.lshr_BitInteger_BitUnsigned start (stop - one))).length =
        ((stop.val - start.val + 1) / 2).toNat := by
  simp only [intRange, List.length_map, List.length_range,
    reverseBangMidpointValue start stop hlo hlt]
  congr 1
  omega

/-- Every left index lies strictly to the left of its reflected right index. -/
theorem reverseBangLeftHalf (start stop left : I)
    (hlo : 1 ≤ start.val) (hlt : start.val < stop.val)
    (hmem : left ∈ intRange start
      (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
        JuliaLean.base.int.lshr_BitInteger_BitUnsigned start (stop - one))) :
    start.val ≤ left.val ∧ 2 * left.val < start.val + stop.val := by
  have hb := intRange_mem _ _ _ hmem
  rw [reverseBangMidpointValue start stop hlo hlt] at hb
  omega

/-- Reflection of a scheduled left position stays inside the window. -/
theorem reverseBangMirror (start stop left : I)
    (hlo : 1 ≤ start.val) (hlt : start.val < stop.val)
    (hmem : left ∈ intRange start
      (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
        JuliaLean.base.int.lshr_BitInteger_BitUnsigned start (stop - one))) :
    (JInt.wrap .i64 (start.val + stop.val - left.val)).val =
      start.val + stop.val - left.val ∧
    left.val < (JInt.wrap .i64 (start.val + stop.val - left.val)).val ∧
    (JInt.wrap .i64 (start.val + stop.val - left.val)).val ≤ stop.val := by
  have hh := reverseBangLeftHalf start stop left hlo hlt hmem
  have ht := ival_bounds stop
  have hw : (JInt.wrap .i64 (start.val + stop.val - left.val)).val =
      start.val + stop.val - left.val := ival_wrap _ (by omega)
  rw [hw]
  omega

/-- The odd midpoint occurs in neither half of the mathematical swap schedule. -/
theorem reverseBangCenterNotScheduled (start stop left : I) (center : Int)
    (hlo : 1 ≤ start.val) (hlt : start.val < stop.val)
    (hc : 2 * center = start.val + stop.val)
    (hmem : left ∈ intRange start
      (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
        JuliaLean.base.int.lshr_BitInteger_BitUnsigned start (stop - one))) :
    left.val < center ∧
      center < (JInt.wrap .i64 (start.val + stop.val - left.val)).val := by
  have hh := reverseBangLeftHalf start stop left hlo hlt hmem
  have hm := reverseBangMirror start stop left hlo hlt hmem
  rw [hm.1]
  omega

/-- A successful swap preserves every raw slot it does not write. -/
theorem reverseBangSwapPreservesOther {α : Type} (xs : List (Option α))
    (left right : I) (x y : α) (position : Nat)
    (hl : (left.val - 1).toNat ≠ position)
    (hr : (right.val - 1).toNat ≠ position) :
    ((xs.set (left.val - 1).toNat (some y)).set
      (right.val - 1).toNat (some x))[position]? = xs[position]? := by
  rw [List.getElem?_set_ne hr, List.getElem?_set_ne hl]

/-- Consecutive left positions after a prefix, used to expose the loop induction. -/
def reverseBangIndices (before count : Nat) : List I :=
  (List.range count).map (fun (k : Nat) => JInt.wrap .i64 ((before : Int) + k + 1))

theorem reverseBangIndicesNil (before : Nat) : reverseBangIndices before 0 = [] := rfl

theorem reverseBangIndicesCons (before count : Nat) :
    reverseBangIndices before (count + 1) =
      JInt.wrap .i64 ((before : Int) + 1) :: reverseBangIndices (before + 1) count := by
  simp only [reverseBangIndices, List.range_succ_eq_map, List.map_cons, List.map_map,
    Int.natCast_zero, Int.add_zero, Function.comp_def]
  apply congrArg (List.cons (JInt.wrap .i64 ((before : Int) + 1)))
  apply List.map_congr_left
  intro k _
  apply congrArg (JInt.wrap .i64)
  simp only [Int.natCast_add, Int.natCast_one, Int.natCast_succ]
  omega

/-- Exchanging two exposed ends leaves the entire intervening raw segment intact. -/
theorem reverseBangSwapEnds {α : Type} (before middle after : List (Option α)) (x y : α) :
    ((before ++ (some x :: middle) ++ (some y :: after)).set before.length (some y)).set
      (before.length + middle.length + 1) (some x) =
      before ++ (some y :: middle) ++ (some x :: after) := by
  rw [List.append_assoc, List.set_append_right _ _ (by omega)]
  simp only [Nat.sub_self, List.cons_append, List.set_cons_zero]
  rw [List.set_append_right _ _ (by omega)]
  have hsub : before.length + middle.length + 1 - before.length = middle.length + 1 := by omega
  rw [hsub]
  simp only [List.set_cons_succ]
  rw [List.set_append_right _ _ (by omega)]
  simp only [Nat.sub_self, List.set_cons_zero]
  rw [List.append_assoc]
  rfl

/-- One swap at the two ends of an arbitrary raw middle segment. -/
theorem reverseBangSwapEndsRun {α : Type} (before middle after : List (Option α))
    (x y : α) (hsmall : before.length + middle.length + after.length + 2 < 2 ^ 62) :
    (reverseBangSwapStep 0 (JInt.wrap .i64 ((before.length : Int) + 1))
      (JInt.wrap .i64 ((before.length : Int) + middle.length + 2))).run
      [before ++ (some x :: middle) ++ (some y :: after)] =
        .ok (.yield (JInt.wrap .i64 ((before.length : Int) + middle.length + 2) - one),
          [before ++ (some y :: middle) ++ (some x :: after)]) := by
  let left := JInt.wrap .i64 ((before.length : Int) + 1)
  let right := JInt.wrap .i64 ((before.length : Int) + middle.length + 2)
  have hlv : left.val = (before.length : Int) + 1 := ival_wrap _ (by omega)
  have hrv : right.val = (before.length : Int) + middle.length + 2 := ival_wrap _ (by omega)
  have hli : (left.val - 1).toNat = before.length := by rw [hlv]; omega
  have hri : (right.val - 1).toNat = before.length + middle.length + 1 := by rw [hrv]; omega
  have hleft : (before ++ (some x :: middle) ++ (some y :: after))[(left.val - 1).toNat]? =
      some (some x) := by
    rw [hli, List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.cons_append, List.getElem?_cons_zero]
  have hright : (before ++ (some x :: middle) ++ (some y :: after))[(right.val - 1).toNat]? =
      some (some y) := by
    rw [hri, List.getElem?_append_right (by simp only [List.length_append, List.length_cons]; omega)]
    have hsub : before.length + middle.length + 1 - (before ++ some x :: middle).length = 0 := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [hsub]
    rfl
  have hrun := reverseBangSwapAssigned
    (before ++ (some x :: middle) ++ (some y :: after)) left right
    (by rw [hlv]; simp only [List.length_append, List.length_cons]; omega)
    (by rw [hrv]; simp only [List.length_append, List.length_cons]; omega) x y hleft hright
  rw [hli, hri, reverseBangSwapEnds] at hrun
  exact hrun

/-- Decrementing a small natural cursor has its ordinary mathematical value. -/
theorem reverseBangWrapPred (n : Nat) (hsmall : n < 2 ^ 62) :
    JInt.wrap .i64 (n : Int) - one = JInt.wrap .i64 ((n : Int) - 1) := by
  apply Subtype.ext
  have hv : (JInt.wrap .i64 (n : Int)).val = (n : Int) := ival_wrap _ (by omega)
  have hr : (JInt.wrap .i64 ((n : Int) - 1)).val = (n : Int) - 1 :=
    ival_wrap _ (by omega)
  calc
    (JInt.wrap .i64 (n : Int) - one).val = (JInt.wrap .i64 (n : Int)).val - 1 :=
      ival_sub_one (JInt.wrap .i64 (n : Int)) (by rw [hv]; omega)
    _ = (n : Int) - 1 := congrArg (fun z : Int => z - 1) hv
    _ = (JInt.wrap .i64 ((n : Int) - 1)).val := hr.symm

/-- An even window, or an odd window with one central slot, executes one swap per side item. -/
theorem reverseBangIntRangeIndices (before count middle : Nat)
    (hcount : 0 < count) (hcenter : middle ≤ 1)
    (hsmall : before + count + middle + count < 2 ^ 62) :
    intRange (JInt.wrap .i64 ((before : Int) + 1))
      (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
        JuliaLean.base.int.lshr_BitInteger_BitUnsigned
        (JInt.wrap .i64 ((before : Int) + 1))
        (JInt.wrap .i64 ((before + count + middle + count : Nat) : Int) - one)) =
          reverseBangIndices before count := by
  let start := JInt.wrap .i64 ((before : Int) + 1)
  let stop := JInt.wrap .i64 ((before + count + middle + count : Nat) : Int)
  have hsv : start.val = (before : Int) + 1 := ival_wrap _ (by omega)
  have htv : stop.val = ((before + count + middle + count : Nat) : Int) := ival_wrap _ (by omega)
  have hlo : 1 ≤ start.val := by rw [hsv]; omega
  have hlt : start.val < stop.val := by rw [hsv, htv]; omega
  change intRange start
    (midpoint JuliaLean.base.int.addWrap JuliaLean.base.int.subWrap
      JuliaLean.base.int.lshr_BitInteger_BitUnsigned start (stop - one)) = _
  simp only [intRange, reverseBangIndices, reverseBangMidpointValue start stop hlo hlt, hsv, htv]
  have hcountEq :
      ((((before : Int) + 1 + ((before + count + middle + count : Nat) : Int) - 1) / 2 -
        ((before : Int) + 1) + 1).toNat) = count := by omega
  rw [hcountEq]
  apply List.map_congr_left
  intro k _
  apply congrArg (JInt.wrap .i64)
  omega
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion
open JuliaLean JuliaLean.base.array
open JuliaLean.Registry

/-- A failed start conversion occurs before stop conversion, allocation,
index discovery and reads/writes, preserving the failed conversion's state. -/
def ReverseStartErrors : Prop :=
  ∀ (W A E Start Stop : Type)
    (toStart : Start → ExceptT Error (StateM W) I)
    (toStop : Stop → ExceptT Error (StateM W) I)
    (similar : A → ExceptT Error (StateM W) A)
    (first last : A → ExceptT Error (StateM W) I)
    (get : A → I → ExceptT Error (StateM W) E)
    (set : A → E → I → ExceptT Error (StateM W) Unit)
    (a : A) (start : Start) (stop : Stop) (before after : W) (error : Error),
    (toStart start).run before = (.error error, after) →
    (JuliaLean.base.array.reverse toStart toStop similar first last get set a start stop).run before =
      (.error error, after)
end JuliaLean.Proofs.base.array.Completion


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

/-- In-place reversal converts the start before the stop and before discovering axes or touching elements; a start conversion error retains exactly its state. -/
def ReverseBangStartFailures : Prop :=
  ∀ (W A Start Stop Linear Bound E : Type)
    (toStart : Start → ExceptT Error (StateM W) I) (toStop : Stop → ExceptT Error (StateM W) I)
    (linear : A → ExceptT Error (StateM W) Linear)
    (first last : Linear → ExceptT Error (StateM W) Bound)
    (lower : Bound → I → ExceptT Error (StateM W) (Option Bool))
    (upper : I → Bound → ExceptT Error (StateM W) (Option Bool))
    (get : A → I → ExceptT Error (StateM W) E)
    (set : A → E → I → ExceptT Error (StateM W) Unit)
    (a : A) (start : Start) (stop : Stop) (before after : W) (error : Error),
    (toStart start).run before = (.error error, after) →
    (JuliaLean.base.array.Completion3.reverseBang toStart toStop linear first last lower upper get set
      a start stop).run before = (.error error, after)
end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- Observable calls at the existing reverseind boundary, base/array.jl:2276-2279.
Payloads retain the original vector, constructed LinearIndices object, native
arithmetic operand, and original integer index without narrowing its type. -/
inductive ReverseindEvent (A Linear Z : Type) where
  | construct (a : A)
  | first (li : Linear)
  | last (li : Linear)
  | subtract (left : I) (originalIndex : Z)

/-- A concrete responder records its effect before returning or throwing. This
is instrumentation for the source-order invariant, not a supplied callee law. -/
def reverseindReply {Exception A Linear Z Result : Type}
    (event : ReverseindEvent A Linear Z) (answer : Except Exception Result) :
    ExceptT Exception (StateM (List (ReverseindEvent A Linear Z))) Result := do
  modify fun events => events ++ [event]
  match answer with
  | .ok x => pure x
  | .error e => throw e

/-- The wrapper calls LinearIndices, first, last, and promoted subtraction in that
order; the first exception stops later calls and retains every preceding effect.
This ranges over arbitrary original/result index types, exceptions and runtime
responses, and does not assume that any response implements a correct callee.
The subtraction call receives the unmodified original index and the native-width
sum of the two observed endpoints.

Julia source: base/array.jl:2276-2279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Obvious invariant: source expression evaluation and exception propagation. -/
def ReverseindBoundaryProtocol : Prop :=
  ∀ (Exception A Linear Z W : Type) (a : A) (i : Z)
    (initial : List (ReverseindEvent A Linear Z))
    (constructed : Except Exception Linear)
    (firstReply lastReply : Except Exception I) (subtractReply : Except Exception W),
    let run := (JuliaLean.base.array.Models1Group14.reverseindEffectful
      (fun a => reverseindReply (.construct a) constructed)
      (fun li => reverseindReply (.first li) firstReply)
      (fun li => reverseindReply (.last li) lastReply)
      (fun left original => reverseindReply (.subtract left original) subtractReply)
      a i).run initial
    match constructed, firstReply, lastReply with
    | .error e, _, _ =>
      run = (.error e, initial ++ [.construct a])
    | .ok li, .error e, _ =>
      run = (.error e, initial ++ [.construct a, .first li])
    | .ok li, .ok _, .error e =>
      run = (.error e, initial ++ [.construct a, .first li, .last li])
    | .ok li, .ok lower, .ok upper =>
      run = (subtractReply, initial ++ [.construct a, .first li, .last li,
        .subtract (JInt.wrap .i64 (lower.val + upper.val)) i])

/-- A constructible standard Vector extent. The bound is the actual native
GenericMemory element-count limit from src/genericmemory.c:55-73, not a smaller
arbitrary arithmetic range. A nonunion byte Vector can have this extent in the
installed allocator model; no unrestricted Lean list represents an array here. -/
structure ReverseindVectorExtent where
  length : Nat
  allocatable : length < maxIntVal - 1

/-- Concrete standard-vector LinearIndices observations and native Int subtraction
for the reverseind contract at base/array.jl:2276-2279. Only a length is needed:
reverseind never reads a vector element or mutates its storage. -/
def reverseindNative (v : ReverseindVectorExtent) (i : I) : I :=
  JuliaLean.base.array.Models1Group14.reverseindEffectful (m := Id)
    (fun v : ReverseindVectorExtent => pure v.length)
    (fun _ : Nat => pure one)
    (fun n : Nat => pure (JInt.wrap .i64 (n : Int)))
    (fun left original : I => pure (left - original)) v i

/-- On every constructible standard Vector extent and every valid native Int
index, reverseind reflects the index through the endpoints, stays in bounds,
and is an involution. The expected value is mathematical n+1-i; the actual
calculation uses Core's wrapping JInt addition/subtraction through the new model.

Julia documentation: base/strings/basic.jl:721-740.
Julia source: base/array.jl:2276-2279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
The valid-index premises are exactly the documented domain. -/
def ReverseindNativeReflection : Prop :=
  ∀ (v : ReverseindVectorExtent) (i : I),
    1 ≤ i.val → i.val ≤ (v.length : Int) →
    let reflected := reverseindNative v i
    reflected.val = (v.length : Int) + 1 - i.val ∧
    1 ≤ reflected.val ∧ reflected.val ≤ (v.length : Int) ∧
    reverseindNative v reflected = i
end JuliaLean.Proofs.base.array.Models1Group14


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion.ReverseStartErrors_proven : JuliaLean.Proofs.base.array.Completion.ReverseStartErrors := by
  unfold JuliaLean.Proofs.base.array.Completion.ReverseStartErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.reverse, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion3.ReverseBangStartFailures_proven : JuliaLean.Proofs.base.array.Completion3.ReverseBangStartFailures := by
  unfold JuliaLean.Proofs.base.array.Completion3.ReverseBangStartFailures
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion3.reverseBang, JuliaLean.base.array.reverseBang, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesReverse1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-reverse-dims", juliaFile := "base/array.jl",
    juliaFns := ["reverse(::AbstractVector; dims)", "reverse!(::AbstractVector; dims)",
      "_reverse(A, ::Colon)", "_reverse(A, ::Integer)", "_reverse!(A, ::Colon)",
      "_reverse!(A, ::Integer)"],
    statement := "reverse(v; dims) and reverse!(v; dims) with dims = : or 1 act as reverse(v, 1, length(v)) and reverse!(v, 1, length(v)); every other integer dims throws ArgumentError before touching v.",
    source := "base/array.jl:2263-2272",
    status := .proven, prop := ``ReverseDimsSpec, thm := some ``reverseDimsSpec}
]
def entriesReverse2 : List JuliaLean.Registry.Entry := [
  { id := "array-reverseind-wide-index", juliaFile := "base/array.jl",
    juliaFns := ["reverseind(v, i)"],
    statement := "`reverseind(v::AbstractVector, i)` (array.jl:2276; docstring at array.jl:2258-2275: \"Given an index `i` in `reverse(v)`, return the corresponding index in `v` so that `v[reverseind(v,i)] == reverse(v)[i]`\") for a vector of the shared heap with unassigned slots allowed and an index of any `Integer` type, with `LinearIndices(v)`'s `first` and `last`, the promoted `first(li) + last(li) - i`, and `reverse(v)` (array.jl:2267, `reverse(v, firstindex(v), lastindex(v))`): for every valid index `i` of `reverse(v)` (not a `Bool`, in `1:length(v)`), reading `v` at `reverseind(v, i)` gives exactly what reading `reverse(v)` at `i` gives (the same element, or the same error at an unassigned slot).",
    source := "base/array.jl:2258-2275, array.jl:2267, array.jl:2276", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #42366; see bugs/array-reverseind-wide-index.yaml",
    prop := ``ReverseIndexReflectionSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayReverseindWideIndex_refuted,
    notes := "" }
]
def entriesReverse3 : List JuliaLean.Registry.Entry := [
  { id := "arrayops-reverse-window-inconsistent", juliaFile := "base/array.jl",
    juliaFns := ["reverse(::AbstractVector, ::Integer, ::Integer)", "reverse!(::AbstractVector, ::Integer, ::Integer)"],
    statement := "The documented reversal of a window, for both `reverse(v, start, stop)` and `reverse!(v, start, stop)` (array.jl:2248, 2312): the exact contents on every window, as stated by `ReverseWindowSpec` and `ReverseBangWindowSpec`.",
    source := "base/array.jl:2248", status := .todo,
    prop := ``ReverseCopyAgrees, thm := none,
    notes := "Statement/prose mismatch: this ReverseCopyAgrees requires equal results or exceptions for all endpoints, whereas the registered prose refers to the separate window contracts. The returned [1], start = stop = 0 witness lies outside the copy contract's valid window and compares its BoundsError with reverse!'s specified unchanged return. It does not refute the documented target." }
]
def entriesReverse4 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-reverseind", juliaFile := "base/array.jl",
    juliaFns := ["reverseind(a::AbstractVector, i::Integer)"],
    statement := "For a vector with linear indices 1:n (n < 2^62) and i in 1:n of any BitInteger type, reverseind(v, i) = n + 1 - i lies in 1:n, applying it twice gives i, and v[reverseind(v, i)] == reverse(v)[i].",
    source := "base/array.jl:2276-2279; reverseind docstring (strings/basic.jl)", status := .proven, prop := ``ReverseindSpec, thm := some ``reverseindSpec }
]
def entriesReverse5 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-reverse-window", juliaFile := "base/array.jl",
    juliaFns := ["reverse(A::AbstractVector, start::Integer, stop::Integer=lastindex(A))"],
    statement := "`reverse(v, start, stop)` (array.jl:2248; docstring at array.jl:2222-2247: \"Return a copy of `v` reversed from start to stop\") on a vector of the shared heap whose slots may be unassigned, with endpoints of any `Integer` type: an endpoint with no equal `Int` raises `InexactError`; for a window `1 ≤ start ≤ stop + 1 ≤ length(v) + 1` of a fully assigned vector it returns a fresh vector equal to `v` with `v[start:stop]` reversed, leaving `v` unchanged; a vector with an unassigned slot raises `UndefRefError` (every slot is read).",
    source := "base/array.jl:2222-2247, array.jl:2248", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.ReverseWindowSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2ReverseWindow_proven,
    notes := "" },
  { id := "multidimcov-array-v2-reverse-bang", juliaFile := "base/array.jl",
    juliaFns := ["reverse!(v::AbstractVector, start::Integer, stop::Integer=lastindex(v))"],
    statement := "`reverse!(v, start, stop)` (array.jl:2312; docstring at array.jl:2291-2311: \"In-place version of `reverse`\") on a vector of the shared heap whose slots may be unassigned, with endpoints of any `Integer` type: an endpoint with no equal `Int` raises `InexactError`; when `stop ≤ start` it returns `v` unchanged; a window `start < stop` reaching outside `1:length(v)` raises `BoundsError` with `v` unchanged; otherwise, when the window `v[start:stop]` is fully assigned it is reversed in place and `v` returned, and when it holds an unassigned slot `UndefRefError` is raised. The midpoint is `midpoint` of array.jl:2283 with the wrapping arithmetic of int.jl.",
    source := "base/array.jl:2283, array.jl:2291-2311, array.jl:2312", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.round4.ReverseBangWindowSpec, thm := none,
    notes := "Statement defect: reverse! swaps endpoints without reading an untouched odd center, so an unassigned center does not force UndefRefError. Source base/array.jl:2312-2328 does not promise a read of every slot. The returned [some first, none, some last] witness for 1:3 refutes that unsupported error guarantee, already present in both Prop and registry prose, rather than a documented Julia promise." }
]
def entriesReverse6 : List JuliaLean.Registry.Entry := [
{ id := "array-reverse-start-errors", juliaFile := "base/array.jl",
  juliaFns := ["reverse(A::AbstractVector, start::Integer, stop::Integer=lastindex(A))"],
  statement := "A failed start conversion occurs before stop conversion, allocation, index discovery and reads/writes, preserving the failed conversion's state.",
  source := "base/array.jl:2248-2261", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.ReverseStartErrors, thm := some ``JuliaLean.Proofs.base.array.Completion.ReverseStartErrors_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." }
]
def entriesReverse7 : List JuliaLean.Registry.Entry := [
{ id := "array-reverse-bang-start-failures", juliaFile := "base/array.jl",
  juliaFns := ["reverse!(v::AbstractVector, start::Integer, stop::Integer=lastindex(v))"],
  statement := "In-place reversal converts the start before the stop and before discovering axes or touching elements; a start conversion error retains exactly its state.",
  source := "base/array.jl:2312-2328", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.ReverseBangStartFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.ReverseBangStartFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesReverse8 : List JuliaLean.Registry.Entry := [
{ id := "array-reverseind-boundary-protocol", juliaFile := "base/array.jl",
    juliaFns := ["reverseind(a::AbstractVector, i::Integer)"],
    statement := "For arbitrary original/result index types and runtime responses, reverseind constructs LinearIndices once, observes first then last, and calls subtraction with the native-width endpoint sum and the unchanged original index. The first exception propagates, later calls do not occur, and effects preceding that exception are retained.",
    source := "base/array.jl:2276-2279 (evaluation-order and exception-propagation invariant)",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.ReverseindBoundaryProtocol,
    thm := none,
    notes := "Concrete instrumented responders cover all success/error combinations without assuming callee correctness. This is a protocol statement at the existing LinearIndices/endpoint/subtraction boundary, not a complete model of custom methods." },
{ id := "array-reverseind-native-reflection", juliaFile := "base/array.jl",
    juliaFns := ["reverseind(a::AbstractVector, i::Integer)"],
    statement := "For every constructible standard Vector extent and every valid native Int index i, reverseind returns the mathematical index length+1-i, remains in bounds, and applying it twice returns i.",
    source := "base/array.jl:2276-2279; base/strings/basic.jl:721-740 (reverseind docstring); src/genericmemory.c:55-73 (constructible element count)",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.ReverseindNativeReflection,
    thm := none,
    notes := "Uses actual Core JInt arithmetic through reverseindEffectful. The extent bound is the installed GenericMemory allocation limit. The separate protocol property retains the full typed boundary, including nonstandard indexing and errors." }
]
end JuliaLean.Proofs.base.array

