import JuliaLean.base.bitset

namespace JuliaLean.BitArrays

open BV

/-! ## BitSet -/

/-- `n in s` after any sequence of `push!` and `delete!` agrees with `Set{Int}`
for all `Int` elements, including negative ones and `typemin`/`typemax`. -/
def BitSetPushDeleteAgrees : Prop :=
  ∀ (ops : List (Bool × JInt64)) (n : JInt64),
    (ops.foldl (fun s (o : Bool × JInt64) => if o.1 then s.push o.2 else s.delete o.2) BitSetS.empty).contains n =
      (ops.foldl (fun (S : JInt64 → Bool) (o : Bool × JInt64) =>
        fun y => if y = o.2 then o.1 else S y) (fun _ => false)) n

/-- `symdiff!(s::BitSet, itr)` agrees with `symdiff!(Set{Int}(s), itr)`, which
symmetric-differences with the set of elements of `itr`
(`base/abstractset.jl:297`, #46397): `x` is in the result exactly when it is in
exactly one of `s` and `itr`. -/
def BitSetSymdiffAgrees : Prop :=
  ∀ (xs ns : List JInt64) (y : JInt64),
    ((BitSetS.ofList xs).symdiff ns).contains y = (decide (y ∈ xs) ^^ decide (y ∈ ns))
end JuliaLean.BitArrays
