import JuliaLean.base.hashing

namespace JuliaLean.Proofs.base.hashing.LegacyCoverage

open JuliaLean JuliaLean.base.hashing

/-- The primitive hash operations retain the full UInt64 product, use its high
and low halves in order, wrap linear mixing, and apply the written finalizer
shifts. Source: base/hashing.jl:48-61.
-/
def HashPrimitiveBehavior : Prop :=
  (∀ a b : Word, mulParts a b =
    (JInt.lit .u64 (a.val * b.val / 2 ^ 64), JInt.lit .u64 (a.val * b.val))) ∧
  (∀ a b : Word, hashMix a b = xorWord (mulParts a b).1 (mulParts a b).2) ∧
  (∀ x h : Word, hashMixLinear x h (Or.inl rfl) =
    JInt.lit .u64 3 * h - JInt.lit .u64 x.val) ∧
  (∀ x : Word, hashFinalizer x =
    let x := xorWord x (shrWord x 32)
    let x := x * JInt.lit .u64 0x63652a4cd374b267
    xorWord x (shrWord x 33))

theorem hashPrimitiveBehavior : HashPrimitiveBehavior :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end JuliaLean.Proofs.base.hashing.LegacyCoverage
