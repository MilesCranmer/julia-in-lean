import JuliaLean.Core
import JuliaLean.ReinterpretArrays.MultInv

/-!
Model of `reshape` (`base/reshapedarray.jl`) and of `Core.checked_dims` (`base/boot.jl`), master.
Dimensions are Julia `Int`s (`JInt64`).
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- `Intrinsics.ule_int(typemax_Int, x)`: `x` is negative or `typemax(Int)`. -/
def uleTypemax (x : JInt64) : Bool := decide (x.val < 0 ∨ x.val = IntTy.max .i64)

/-- `Intrinsics.checked_smul_int(a, b)`: the wrapped product and whether it overflowed. -/
def checkedSmul (a b : JInt64) : JInt64 × Bool :=
  (a * b, decide ¬ (IntTy.min .i64 ≤ a.val * b.val ∧ a.val * b.val ≤ IntTy.max .i64))

/-- The loop of `_checked_mul_dims(m, d...)`, `base/boot.jl:798-807`, over the remaining `d`
with accumulator `a` and flags `ovflw`, `neg`, `zero`. -/
def checkedMulDimsLoop : List JInt64 → JInt64 → Bool → Bool → Bool → JInt64 × Bool
  | [], a, ovflw, neg, zero => (a, neg || (ovflw && !zero))
  | di :: d, a, ovflw, neg, zero =>
    let b := checkedSmul a di
    checkedMulDimsLoop d b.1 (ovflw || b.2) (neg || uleTypemax di) (zero || decide (di.val = 0))

/-- `_checked_mul_dims`, `base/boot.jl:782-808` (methods for zero, one, two and more dimensions). -/
def checkedMulDims : List JInt64 → JInt64 × Bool
  | [] => (JInt.lit .i64 1, false)
  | [m] => (m, uleTypemax m)
  | [m, n] => let b := checkedSmul m n; (b.1, b.2 || uleTypemax m || uleTypemax n)
  | m :: d => checkedMulDimsLoop d m false (uleTypemax m) false

/-- `Core.checked_dims(d::Int...)`, `base/boot.jl:811-818`. -/
def checkedDims : List JInt64 → Jl JInt64
  | [] => .ok (JInt.lit .i64 1)
  | [m] => .ok m
  | d => let b := checkedMulDims d
    if b.2 then .error (.argumentError "invalid Array dimensions") else .ok b.1

/-- Julia's `DimensionMismatch`, recorded as a distinct exception. -/
def dimensionMismatch : JlError := .argumentError "DimensionMismatch"

/-- The size check of `_reshape(parent::AbstractArray, dims::Dims)`, `base/reshapedarray.jl:221-225`,
for a parent with `n = length(parent)` elements; on success `__reshape` wraps the parent. -/
def reshapeCheck (n : JInt64) (dims : List JInt64) : Jl Unit := do
  let p ← checkedDims dims
  if p = n then pure () else throw dimensionMismatch

/-- `_reshape_uncolon` and `_reshape_uncolon_computesize` for `Int` dimensions with one `Colon`,
`base/reshapedarray.jl:143-162,172-177`: `pre` and `post` are the dimensions before and after
the colon, `len = length(A)`. -/
def reshapeUncolon (len : JInt64) (pre post : List JInt64) : Jl (List JInt64) := do
  let sz ← if len.val = 0 then pure (JInt.lit .i64 0) else do
    let pr ← checkedDims (pre ++ post)
    if pr.val = 0 then throw dimensionMismatch
    let quo ← JInt.div len pr
    let rem ← JInt.remInt len pr
    if rem.val ≠ 0 then throw dimensionMismatch
    pure quo
  pure (pre ++ [sz] ++ post)

/-- `reshape(A, pre..., :, post...)` for a generic parent with `len` elements,
`base/reshapedarray.jl:136,128,221-225`. -/
def reshapeColon (len : JInt64) (pre post : List JInt64) : Jl (List JInt64) := do
  let dims ← reshapeUncolon len pre post
  reshapeCheck len dims
  pure dims

/-- `SignedMultiplicativeInverse.(max.(1, front(size(parent))))`, `base/reshapedarray.jl:235-241`.
`SmiNewAll szs mis` holds when the constructor returns `mis` for the sizes `szs`. -/
def SmiNewAll : List JInt64 → List (SignedMI .i64) → Prop
  | [], [] => True
  | s :: szs, m :: mis => SmiNew (if s.val < 1 then JInt.lit .i64 1 else s) m ∧ SmiNewAll szs mis
  | _, _ => False

/-- `_ind2sub_rs(ax, szs, ind)`, `base/reshapedarray.jl:272-276`, for a parent whose axes start at
`firsts`: `divrem(ind, mi)` is `div(ind, mi)` and `ind - d * mi.divisor`
(`base/multinverses.jl:151-154`). -/
def ind2subRsAux : List JInt64 → List (SignedMI .i64) → JInt64 → List JInt64
  | firsts, [], ind => [ind + firsts.getLastD (JInt.lit .i64 1)]
  | f :: firsts, mi :: mis, ind =>
    let d := smiDiv ind mi
    let r := ind - d * mi.divisor
    (r + f) :: ind2subRsAux firsts mis d
  | [], _ :: _, ind => [ind]

/-- `ind2sub_rs(ax, szs, i)`, `base/reshapedarray.jl:270-271`. -/
def ind2subRs (firsts : List JInt64) (mis : List (SignedMI .i64)) (i : JInt64) : List JInt64 :=
  match mis with
  | [] => [i]
  | _ => ind2subRsAux firsts mis (i - JInt.lit .i64 1)

/-- Column-major linear index (1-based) of 1-based subscripts `J` in an array of size `szs`. -/
def sub2indMath : List Int → List Int → Int
  | [], _ => 1
  | _, [] => 1
  | [_], [j] => j
  | s :: szs, j :: js => j + s * (sub2indMath szs js - 1)

end JuliaLean.ReinterpretArrays
