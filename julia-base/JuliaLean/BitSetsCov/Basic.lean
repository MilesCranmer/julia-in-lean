import JuliaLean.BitArrays.BitSetProof

/-!
# Shared definitions of the `BitSetsCov` area

* `Exc` lists the Julia exception types that the methods of `base/bitset.jl`,
  `base/set.jl`, `base/abstractset.jl`, `base/idset.jl` and
  `base/bitarray.jl` throw; `R α` is a result that may throw one of them.
* An `Integer` argument is its mathematical value (`Int`); `Int(n)` is
  `toInt n`, which throws `InexactError` outside `typemin(Int):typemax(Int)`.
* `Vector{UInt64}` primitives (`resize!`, `copyto!`, `_growend!`, ...) act on
  `List U64`; newly allocated memory holds an arbitrary `dirty` chunk.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays

/-- Julia exception types of this area. -/
inductive Exc where
  | keyError | argumentError | boundsError | inexactError | dimensionMismatch
  | methodError | domainError | divideError | typeError | assertionError
  deriving Repr, DecidableEq, Inhabited

abbrev R (α : Type) := Except Exc α

/-- `typemin(Int) <= n <= typemax(Int)` for an `Integer` `n`. -/
def inIntRange (n : Int) : Prop := -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807

instance (n : Int) : Decidable (inIntRange n) := by unfold inIntRange; infer_instance

theorem inIntRange_iff (n : Int) : inIntRange n ↔ IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max := by
  simp [inIntRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]

/-- `Int(n)` for an `Integer` value `n`. -/
def toInt (n : Int) : R JInt64 :=
  if h : inIntRange n then .ok ⟨n, (inIntRange_iff n).mp h⟩ else .error .inexactError

/-- `x << 6` on an `Int` (wraps). -/
def shl6 (x : Int) : JInt64 := JInt.wrap .i64 (x * 64)

/-! ## `Vector{UInt64}` primitives -/

/-- `resize!(v, n)` for `n ≥ 0` (`base/array.jl`): truncate, or append
uninitialised chunks. -/
def vresize (v : List U64) (n : Nat) (dirty : U64) : List U64 :=
  if n ≤ v.length then v.take n else v ++ List.replicate (n - v.length) dirty

/-- `copyto!(dest, src)` for two `Vector{UInt64}` (`base/array.jl`): throws
`BoundsError` when `src` is longer, otherwise overwrites `dest[1:length(src)]`. -/
def vcopyto (dest src : List U64) : R (List U64) :=
  if src.length > dest.length then .error .boundsError else .ok (src ++ dest.drop src.length)

/-- `_growbeg!(v, k)`: `k` uninitialised chunks in front. -/
def growbeg (v : List U64) (k : Nat) (dirty : U64) : List U64 := List.replicate k dirty ++ v

/-- `_deletebeg!(v, k)`. -/
def deletebeg (v : List U64) (k : Nat) : List U64 := v.drop k

/-- `v[i] = x` (1-based). -/
def vset (v : List U64) (i : Nat) (x : U64) : List U64 := v.set (i - 1) x

/-- `v[i]` (1-based, `@inbounds`). -/
def vget (v : List U64) (i : Nat) : U64 := v.getD (i - 1) 0

/-- `unsafe_copyto!(dest, doffs, src, soffs, n)` on `Vector{UInt64}`: element-wise
copy of `src[soffs:soffs+n-1]` into `dest[doffs:doffs+n-1]`. -/
def vunsafeCopyto (dest : List U64) (doffs : Nat) (src : List U64) (soffs n : Nat) : List U64 :=
  (List.range n).foldl (fun d k => vset d (doffs + k) (vget src (soffs + k))) dest

end JuliaLean.BitSetsCov
