import JuliaLean.Proofs.base.reduce.Contracts
import JuliaLean.base.reducedim
import JuliaLean.base.anyall

namespace JuliaLean.Reduce

open JuliaLean.Float

/-- Slice `k` (0-based) of a matrix reduced along `d`: column `k` for `d = 1`, row `k`
for `d = 2`. -/
def Mat.slice (A : Mat Val) (d k : Nat) : List Val := if d = 1 then A.col k else A.row k

/-! ### Reductions along a dimension -/

/-- `sum(A; dims = d)` for a `BitInteger` matrix has the reduced shape and holds the exact
slice sums in the widened type, wrapping only there (`base/reducedim.jl:464-485`). -/
def SumDimsExact : Prop :=
  ∀ (t : IntTy) (A : Mat Val) (d : Nat), A.WF → (d = 1 ∨ d = 2) →
    (∀ x ∈ A.data, ∃ y, x = .int t y) →
    ∃ Rr, sumDims (fun x => .ok x) (.int t) A d = .ok Rr ∧
      (Rr.m, Rr.n) = reducedShape A.m A.n d ∧ Rr.data.length = Rr.m * Rr.n ∧
      ∀ k < Rr.data.length,
        Rr.get k = .int (sumTy t) (JInt.wrap (sumTy t) ((A.slice d k).map Val.intVal).sum)

/-- `maximum(A; dims = d)` and `minimum(A; dims = d)` of a nonempty `Matrix{Int}` hold
`maximum`/`minimum` of each slice, in the reduced shape (`base/reducedim.jl:613-743`). -/
def MaxDimsInt : Prop :=
  ∀ (A : Mat Val) (d : Nat) (isMax : Bool), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, ∃ y, x = .int .i64 y) →
    ∃ Rr, maxminDims (fun x => .ok x) isMax (.int .i64) A d = .ok Rr ∧
      (Rr.m, Rr.n) = reducedShape A.m A.n d ∧ Rr.data.length = Rr.m * Rr.n ∧
      ∀ k < Rr.data.length,
        (if isMax then Vec.maximum (A.slice d k) else Vec.minimum (A.slice d k)) = .ok (Rr.get k)

/-- Numeric equality `x == y` of two numbers. -/
def Val.numEq (x y : Val) : Prop := F64.eq x.toF64 y.toF64 = true

/-- `maximum(A; dims = d)` succeeds for a nonempty matrix with element type `Int`,
`Float64` or `Union{Int, Float64}` and holds values equal to `maximum` of each slice. -/
def MaxDimsUnion : Prop :=
  ∀ (A : Mat Val) (d : Nat) (ty : Ty), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (ty = .int .i64 ∨ ty = .f64 ∨ ty = .union (.int .i64) .f64) →
    (∀ x ∈ A.data, ty.isa x = true ∧ x.isnan = false) →
    ∃ Rr, maxminDims (fun x => .ok x) true ty A d = .ok Rr ∧
      ∀ k < Rr.data.length, ∃ y, Vec.maximum (A.slice d k) = .ok y ∧ Val.numEq (Rr.get k) y

/-- `maximum(A; dims = d)` of a nonempty matrix whose entries are all `missing` is a
matrix of `missing`, as `maximum` of each slice is (`base/missing.jl:129-137`). -/
def MaxDimsMissing : Prop :=
  ∀ (A : Mat Val) (d : Nat) (isMax : Bool), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, x = .missing) →
    ∃ Rr, maxminDims (fun x => .ok x) isMax .missing A d = .ok Rr ∧
      ∀ k < Rr.data.length, Rr.get k = .missing

/-- `maximum(abs, A; dims = d)` of a nonempty `Matrix{Int}` holds `maximum(abs, slice)`
for every slice. -/
def MaxAbsDims : Prop :=
  ∀ (A : Mat Val) (d : Nat), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, ∃ y, x = .int .i64 y) →
    ∃ Rr, maxAbsDims (.int .i64) A d = .ok Rr ∧
      ∀ k < Rr.data.length, Vec.maxAbs (.int .i64) (A.slice d k) = .ok (Rr.get k)

/-- `sum(A; dims = d, init = zero(S))` of a small-integer matrix holds `sum(slice;
init = zero(S))` for every slice, as the dimension-free `sum` with `init` does. -/
def SumDimsInit : Prop :=
  ∀ (t s : IntTy) (A : Mat Val) (d : Nat), smallTy t → smallTy s → A.WF → (d = 1 ∨ d = 2) →
    (∀ x ∈ A.data, ∃ y, x = .int t y) →
    ∃ Rr, mapreduceDimsInit (fun x => .ok x) (fun x y => .ok (Val.addSum x y)) 1024
        (.int s (JInt.lit s 0)) A d = .ok Rr ∧
      ∀ k < Rr.data.length,
        Val.intVal (Rr.get k) = Val.intVal (Vec.sumInit (.int s (JInt.lit s 0)) (A.slice d k))

/-- `any(A; dims = d)` of a nonempty matrix of `Bool`s and `missing`s holds `any(slice)`
for every slice, three-valued as `any` is (`base/anyall.jl:8-10`). -/
def AnyDimsSlices : Prop :=
  ∀ (A : Mat Val) (d : Nat), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, x = .missing ∨ x = .bool true ∨ x = .bool false) →
    ∃ Rr, anyDims id A d = .ok Rr ∧
      ∀ k < Rr.data.length, Vec.any id (A.slice d k) = .ok (Rr.get k)

/-- The 1-based `CartesianIndex` of element `i` (1-based) of slice `k` along `d`. -/
def sliceIndex (d k i : Nat) : Nat × Nat := if d = 1 then (i, k + 1) else (k + 1, i)

/-- `findmax(A; dims = d)` and `findmin(A; dims = d)` of a nonempty `Matrix{Float64}` hold,
for every slice, `findmax`/`findmin` of the slice with the index mapped to a
`CartesianIndex` (`base/reducedim.jl:1169-1212`). -/
def FindDimsSlices : Prop :=
  ∀ (A : Mat Val) (d : Nat) (isMax : Bool), A.WF → (d = 1 ∨ d = 2) → 0 < A.m → 0 < A.n →
    (∀ x ∈ A.data, ∃ y, x = .f64 y) →
    ∃ Rr, findDims id isMax .f64 A d = .ok Rr ∧
      (Rr.vals.m, Rr.vals.n) = reducedShape A.m A.n d ∧
      Rr.vals.data.length = Rr.vals.m * Rr.vals.n ∧ Rr.idx.length = Rr.vals.data.length ∧
      ∀ k < Rr.vals.data.length, ∃ i,
        (if isMax then Vec.findmax (A.slice d k) else Vec.findmin (A.slice d k)) =
          .ok (Rr.vals.get k, i) ∧ Rr.idx[k]? = some (sliceIndex d k i)

/-- `findmax(A; dims = d)` returns arrays of the reduced shape (size 1 along `d`), the shape
`sum(A; dims = d)` has, whenever it returns. -/
def FindDimsShape : Prop :=
  ∀ (A : Mat Val) (d : Nat) (ty : Ty) (Rr : FindRes), A.WF → (d = 1 ∨ d = 2) →
    findDims id true ty A d = .ok Rr → (Rr.vals.m, Rr.vals.n) = reducedShape A.m A.n d

end JuliaLean.Reduce
