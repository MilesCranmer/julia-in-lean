import JuliaLean.BroadcastViews.FastLinearProofs

/-!
`strides`/`stride` of a view of an `Array`, `base/subarray.jl:437-446` and
`base/reinterpretarray.jl:204-206`, master `bbfa0ce4150`.
-/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- `size_to_strides(s, sz...)`, `base/abstractarray.jl:609-611`: `(s, s*sz[1], s*sz[1]*sz[2], ...)`
with one entry per dimension. -/
def sizeToStrides (s : I64) : List I64 → List I64
  | [] => []
  | [_] => [s]
  | d :: ds => s :: sizeToStrides (s * d) ds

/-- `substrides(strds, I)`, `base/subarray.jl:439-444`: scalars drop their stride, a `Slice` keeps
it, a range multiplies it by its step. -/
def substrides : List I64 → List LIdx → List I64
  | _ :: st, .scalar _ :: is => substrides st is
  | s :: st, .slice :: is => s :: substrides st is
  | s :: st, .urange _ _ :: is => s * i64 1 :: substrides st is
  | s :: st, .srange _ step _ :: is => s * step :: substrides st is
  | _, _ => []

/-- `size(V)`: the lengths of the non-scalar indices (`length(Slice(OneTo(n))) == n`). -/
def viewSize : List I64 → List LIdx → List I64
  | _ :: ns, .scalar _ :: is => viewSize ns is
  | n :: ns, .slice :: is => n :: viewSize ns is
  | _ :: ns, .urange _ len :: is => len :: viewSize ns is
  | _ :: ns, .srange _ _ len :: is => len :: viewSize ns is
  | _, _ => []

/-- `stride(V::SubArray, d) = d <= ndims(V) ? strides(V)[d] : strides(V)[end] * size(V)[end]`
(`base/subarray.jl:446`), with `strides(V) = substrides(strides(V.parent), V.indices)` (437) and
`strides(::Array) = size_to_strides(1, size(a)...)` (`base/reinterpretarray.jl:204`). Indexing the
empty tuple `()[end]` throws `BoundsError`. -/
def strideSub (ns : List I64) (I : List LIdx) (d : Nat) : R I64 :=
  let st := substrides (sizeToStrides (i64 1) ns) I
  let sz := viewSize ns I
  if d ≤ st.length then .ok (st.getD (d - 1) (i64 0))
  else match st.getLast?, sz.getLast? with
    | some a, some b => .ok (a * b)
    | _, _ => .error .boundsError

/-- `stride(V, k)` returns a value for every view of an `Array` and every dimension `k ≥ 1`, as
`stride(A, k)` does for every `Array` (`base/reinterpretarray.jl:205-206`: `length(A)` past the
last dimension) and for every `AbstractArray` (`base/abstractarray.jl:597-607`: 1 for a
zero-dimensional array). -/
def StrideTotal : Prop :=
  ∀ (ns : List I64) (I : List LIdx) (k : Nat), IdxInBounds ns I → 1 ≤ k → ∃ v, strideSub ns I k = .ok v

/-- `stride(view(zeros(3, 4), 1, 2), 1)` throws `BoundsError`: `strides(V) == ()`. -/
theorem stride_zero_dim : strideSub [i64 3, i64 4] [.scalar (i64 1), .scalar (i64 2)] 1 = .error .boundsError := by
  decide

theorem strideTotal_refuted : ¬ StrideTotal := by
  intro h
  have hb : IdxInBounds [i64 3, i64 4] [.scalar (i64 1), .scalar (i64 2)] := by
    show 1 ≤ (i64 1).val ∧ (i64 1).val ≤ (i64 3).val ∧ (1 ≤ (i64 2).val ∧ (i64 2).val ≤ (i64 4).val ∧ True)
    decide
  obtain ⟨v, hv⟩ := h [i64 3, i64 4] [.scalar (i64 1), .scalar (i64 2)] 1 hb (by decide)
  rw [stride_zero_dim] at hv
  cases hv

end JuliaLean.BroadcastViews
