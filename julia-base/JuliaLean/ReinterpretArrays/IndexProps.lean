import JuliaLean.ReinterpretArrays.Reshape
import JuliaLean.ReinterpretArrays.Views

/-!
Properties of `reshape`, `ReshapedArray` index conversion, fast linear `SubArray` indexing and
`PermutedDimsArray` index permutation.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- Product of `Int` dimensions as an exact integer. -/
def dimProd (dims : List JInt64) : Int := (dims.map (·.val)).foldr (· * ·) 1

/-- `reshape(A, dims)` succeeds only when every dimension is nonnegative and their exact product is
`length(A)` (it never accepts a wrapped product). -/
def ReshapeCheckSound : Prop :=
  ∀ (n : JInt64) (dims : List JInt64), 0 ≤ n.val → reshapeCheck n dims = .ok () →
    (∀ d ∈ dims, 0 ≤ d.val) ∧ dimProd dims = n.val

/-- `reshape(A, dims)` succeeds whenever every dimension is nonnegative and their product is
`length(A)`. -/
def ReshapeCheckComplete : Prop :=
  ∀ (n : JInt64) (dims : List JInt64), 0 ≤ n.val → (∀ d ∈ dims, 0 ≤ d.val) →
    dimProd dims = n.val → reshapeCheck n dims = .ok ()

/-- `reshape(A, pre..., :, post...)` returns only dimensions `(pre..., c, post...)` that are nonnegative
and multiply exactly to `length(A)`. -/
def ReshapeColonSound : Prop :=
  ∀ (len : JInt64) (pre post dims : List JInt64), 0 ≤ len.val → reshapeColon len pre post = .ok dims →
    (∃ c, dims = pre ++ [c] ++ post) ∧ (∀ d ∈ dims, 0 ≤ d.val) ∧ dimProd dims = len.val

/-- The parent subscripts that `ReshapedArray` computes from a linear index with
`SignedMultiplicativeInverse` division are the column-major subscripts of that index, for every parent
size whose length is an `Int`. -/
def Ind2subCorrect : Prop :=
  ∀ (szs : List JInt64) (last : JInt64) (mis : List (SignedMI .i64)) (i : JInt64),
    SmiNewAll szs mis → (∀ s ∈ szs, 0 ≤ s.val) → 0 ≤ last.val →
    dimProd (szs ++ [last]) ≤ IntTy.max .i64 → 1 ≤ i.val → i.val ≤ dimProd (szs ++ [last]) →
    let J := ind2subRs (List.replicate (szs.length + 1) (JInt.lit .i64 1)) mis i
    J.length = szs.length + 1 ∧
    (∀ p ∈ J.zip (szs ++ [last]), 1 ≤ p.1.val ∧ p.1.val ≤ p.2.val) ∧
    sub2indMath ((szs ++ [last]).map (·.val)) (J.map (·.val)) = i.val

/-- `view(A, r, c2, ..., ck)[i]` with a range `r` and scalars `c` reads the parent at the linear index of
`(r[i], c2, ..., ck)`, for every in-bounds view of a parent whose length is an `Int`. -/
def ViewIndexCorrect : Prop :=
  ∀ (s1 : JInt64) (rest cs : List JInt64) (start step : JInt64) (len : Int),
    rest.length = cs.length → (∀ s ∈ s1 :: rest, 0 ≤ s.val) → dimProd (s1 :: rest) ≤ IntTy.max .i64 →
    (∀ p ∈ cs.zip rest, 1 ≤ p.1.val ∧ p.1.val ≤ p.2.val) →
    (∀ k : Int, 1 ≤ k → k ≤ len → 1 ≤ start.val + (k - 1) * step.val ∧ start.val + (k - 1) * step.val ≤ s1.val) →
    ∀ i : JInt64, 1 ≤ i.val → i.val ≤ len →
      (viewParentIndex (viewLayout (s1 :: rest) start step cs) i).val =
        sub2indMath ((s1 :: rest).map (·.val)) ((start.val + (i.val - 1) * step.val) :: cs.map (·.val))

/-- `PermutedDimsArray(A, perm)` is constructed exactly when `perm` is a permutation of `1:N`, and then
`B[I...]` reads `A[J...]` with `J[perm[d]] == I[d]`, in bounds whenever `I` is in bounds of
`size(B) = genperm(size(A), perm)`. -/
def PermutedCorrect : Prop :=
  ∀ (perm : List Int) (dims : List Int), perm.length = dims.length →
    (isperm perm = false → ∃ e, pdaNew perm dims.length = .error e) ∧
    (isperm perm = true → ∃ iperm, pdaNew perm dims.length = .ok iperm ∧
      ∀ I : List Int, I.length = dims.length →
        (∀ p ∈ I.zip (genperm dims perm), 1 ≤ p.1 ∧ p.1 ≤ p.2) →
        let J := genperm I iperm
        J.length = dims.length ∧ (∀ p ∈ J.zip dims, 1 ≤ p.1 ∧ p.1 ≤ p.2) ∧
        ∀ d < dims.length, J.getD ((perm.getD d 0) - 1).toNat 0 = I.getD d 0)

end JuliaLean.ReinterpretArrays
