import JuliaLean.ReinterpretArrays.Bytes

/-!
Properties of `ReinterpretArray` element access and sizes (`base/reinterpretarray.jl`).
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- Every element of the parent column has `aligned_sizeof(S)` bytes. -/
def WellFormed (sS : Nat) (col : List Bytes) : Prop := ∀ s ∈ col, s.length = sS

/-- The bytes of element `i1` of `reinterpret(T, A)`: bytes `(i1-1)*sT+1 : i1*sT` of the column. -/
def expectedBytes (sT : Nat) (col : List Bytes) (i1 : Int) : Bytes :=
  (col.flatten.drop ((i1.toNat - 1) * sT)).take sT

/-- `reinterpret(T, A)[i1, J...]` returns exactly the `aligned_sizeof(T)` parent bytes starting at byte
`(i1-1)*aligned_sizeof(T)` of column `J`, and throws `BoundsError` outside `1:size(R, 1)`, for every
pair of element sizes accepted by the constructor and every parent whose byte count fits in an `Int`. -/
def RaGetCorrect : Prop :=
  ∀ (sS sT : Nat) (scalar : Bool) (col : List Bytes) (i1 sz1 : JInt64),
    0 < sS → 0 < sT → sT ≤ IntTy.max .i64 → (scalar = true → sS = sT) → WellFormed sS col →
    col.length * sS ≤ IntTy.max .i64 →
    raNewCheck sS sT (JInt.lit .i64 col.length) = .ok () →
    raSize1 sS sT (JInt.lit .i64 col.length) = .ok sz1 →
    raGet sS sT scalar col sz1 i1 =
      if 1 ≤ i1.val ∧ i1.val ≤ sz1.val then .ok (expectedBytes sT col i1.val) else .error .boundsError

/-- `reinterpret(T, A)[i1, J...] = v` changes exactly the `aligned_sizeof(T)` parent bytes starting at
byte `(i1-1)*aligned_sizeof(T)` of column `J` to the bytes of `v`, leaves every other byte (in
particular the neighbouring bytes of partially overwritten parent elements) unchanged, and throws
`BoundsError` outside `1:size(R, 1)`. -/
def RaSetCorrect : Prop :=
  ∀ (sS sT : Nat) (scalar : Bool) (col : List Bytes) (i1 sz1 : JInt64) (v : Bytes),
    0 < sS → 0 < sT → sT ≤ IntTy.max .i64 → (scalar = true → sS = sT) → WellFormed sS col → v.length = sT →
    col.length * sS ≤ IntTy.max .i64 →
    raNewCheck sS sT (JInt.lit .i64 col.length) = .ok () →
    raSize1 sS sT (JInt.lit .i64 col.length) = .ok sz1 →
    if 1 ≤ i1.val ∧ i1.val ≤ sz1.val then
      ∃ col', raSet sS sT scalar col sz1 i1 v = .ok col' ∧ WellFormed sS col' ∧
        col'.length = col.length ∧
        col'.flatten = overwrite col.flatten ((i1.val.toNat - 1) * sT) v
    else raSet sS sT scalar col sz1 i1 v = .error .boundsError

/-- `reinterpret(T, A)` either throws or has `size(R, 1) * aligned_sizeof(T) == size(A, 1) * aligned_sizeof(S)`,
for every first-dimension length `size(A, 1)` (an `Int`, e.g. of a lazy range). -/
def RaSizeExact : Prop :=
  ∀ (sS sT : Nat) (len : JInt64), 0 < sS → 0 < sT → 0 ≤ len.val → sS ≤ 256 → sT ≤ 256 →
    raNewCheck sS sT len = .ok () → ∀ sz1, raSize1 sS sT len = .ok sz1 →
      sz1.val * sT = len.val * sS

/-- Nesting `reinterpret(reshape, ...)` gives the same size (or error) as applying it to an
array of the intermediate type: `reinterpret(reshape, T, reinterpret(reshape, S, a))` behaves like
`reinterpret(reshape, T, b)` with `b` of size `size(reinterpret(reshape, S, a))`. -/
def RrNestedSize : Prop :=
  ∀ (sU sS sT : Nat) (dims d1 : List Nat), 0 < sU → 0 < sS → 0 < sT → sU ≠ sS → sS ≠ sT → sU ≠ sT →
    rrSize sU sS dims = .ok d1 → rrNestedSize sU sS sT dims = rrSize sS sT d1

def RrNestedSizeRelease : Prop :=
  ∀ (sU sS sT : Nat) (dims d1 : List Nat), 0 < sU → 0 < sS → 0 < sT → sU ≠ sS → sS ≠ sT → sU ≠ sT →
    rrSize sU sS dims = .ok d1 → rrNestedSizeRelease sU sS sT dims = rrSize sS sT d1

end JuliaLean.ReinterpretArrays
