import JuliaLean.Proofs.base.reduce.Contracts
import JuliaLean.base.accumulate

namespace JuliaLean.Reduce

/-! ### Accumulation -/

/-- `accumulate(op, v; dims = d, init)` with `d` beyond the dimensions of `v` (a slice of
length 1 along `d`) returns `op(init, v[i])` for every element: `init` instantiates the
accumulation (`base/accumulate.jl:306-310`). -/
def AccumulateDimsInit : Prop :=
  ∀ (v : List (JInt .i64)) (init : JInt .i64) (d : Int), 2 ≤ d →
    accumulateVecDims (fun a b => a + b) id id (some init) v d = .ok (v.map (init + ·))

/-- `accumulate(op, A; dims, init)` scans the columns (`dims = 1`) or rows (`dims = 2`) of a
matrix like `accumulate(op, slice; init)`, and `dims = 1` on a vector is the plain
`accumulate` (`base/accumulate.jl:235-293`). -/
def AccumulateDimsScan : Prop :=
  ∀ (α β : Type) [Inhabited α] [Inhabited β] (op : β → α → β) (first copy : α → β)
    (init : Option β) (A : Mat α) (v : List α),
    accumulateVecDims op first copy init v 1 = .ok (accumulateVec op first init v) ∧
    (A.WF → ∃ B, accumulateDims op first copy init A 1 = .ok B ∧
      ∀ j < A.n, B.col j = accumulateVec op first init (A.col j)) ∧
    (A.WF → 0 < A.n → ∃ B, accumulateDims op first copy init A 2 = .ok B ∧
      ∀ i < A.m, B.row i = accumulateVec op first init (A.row i))

/-- `cumsum(v; dims)` equals `accumulate(+, v; dims)` for every `dims`: both scan for
`dims = 1`, copy for `dims > 1` and throw `ArgumentError` for `dims ≤ 0`
(`base/accumulate.jl:70-119, 374-375`). -/
def CumsumAccumulate : Prop :=
  ∀ (v : List (JInt .i64)) (d : Int),
    cumsumVecDims id (fun a b => a + b) id v d = accumulateVecDims (fun a b => a + b) id id none v d

/-- `cumprod(v)` of a small-integer vector holds the prefix products in `Int`/`UInt`,
wrapping only there (`base/accumulate.jl:94-98, 196-198, 230`). -/
def CumprodWidened : Prop :=
  ∀ (t : IntTy) (v : List (JInt t)), smallTy t →
    accumulateVecDims Val.mulProd Val.firstMulProd id none (ints t v) 1 =
      .ok ((List.range v.length).map fun k =>
        .int (sumTy t) (JInt.wrap (sumTy t) ((v.take (k + 1)).map (·.val)).prod))

end JuliaLean.Reduce
