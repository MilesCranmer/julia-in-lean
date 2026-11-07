import JuliaLean.base.bitarray

namespace JuliaLean.BitArrays
/-- A difference in the first element takes precedence over all later chunks and lengths. -/
def BitVectorCmpFirstBit : Prop :=
  ∀ (as bs : List U64) (na nb : Nat),
    cmpChunks (0 :: as) (1 :: bs) na nb = -1 ∧
    cmpChunks (1 :: as) (0 :: bs) na nb = 1

theorem bitVectorCmpFirstBit : BitVectorCmpFirstBit := by
  intro as bs na nb
  constructor <;> rfl
end JuliaLean.BitArrays
