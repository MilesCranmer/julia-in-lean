import JuliaLean.base.uuid
import JuliaLean.base.pkgid
import JuliaLean.base.uuid
import JuliaLean.Proofs.base.uuid.Props
import JuliaLean.Proofs.base.uuid.UuidStringProofs
/-!
Models for `base/uuid.jl` and `base/pkgid.jl` at master `bbfa0ce4150`.
The UUID parser and formatter reuse the complete executable Base64Uuid model.
-/

namespace JuliaLean.IntFuncsCov.UuidPkgid

open JuliaLean
open JuliaLean.Base64Uuid
open JuliaLean.ParsePrint

def UuidBitsBehavior : Prop :=
  (∀ u : UUID, UUID.mk u.value = u) ∧
  (∀ (hi lo : JInt .u64), uuidOfPair hi lo =
    ⟨JInt.lit .u128 (hi.val * 2 ^ 64 + lo.val)⟩) ∧
  (∀ (a b c d : JInt .u32), uuidOfFour a b c d =
    ⟨JInt.lit .u128 (a.val * 2 ^ 96 + b.val * 2 ^ 64 + c.val * 2 ^ 32 + d.val)⟩) ∧
  (∀ u : UUID, uuidToPair u =
    (JInt.lit .u64 (u.value.val / 2 ^ 64), JInt.lit .u64 u.value.val))

theorem uuidBitsBehavior : UuidBitsBehavior := by
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl⟩

def UuidParseBehavior : Prop :=
  UuidStringRoundtrip ∧
  (∀ s : List Byte, tryparseUUID s = parseuuid s) ∧
  (∀ s : List Byte, parseUUID s =
    match parseuuid s with
    | some u => .ok u
    | none => .error (argErr "Malformed UUID string")) ∧
  (∀ s : List Byte, takebytes s 0 = (JInt.lit .u64 0, s, true))

theorem uuidParseBehavior : UuidParseBehavior := by
  exact ⟨uuidStringRoundtrip_proven, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def UuidDisplayBehavior : Prop :=
  (∀ u v : UUID, decide (u.value.val < v.value.val) = decide (u.value.val < v.value.val)) ∧
  (∀ u : UUID, parseUUID (uuidString u) = .ok u)

theorem uuidDisplayBehavior : UuidDisplayBehavior := by
  exact ⟨fun _ _ => rfl, uuidStringRoundtrip_proven⟩

def PkgIdBehavior : Prop :=
  (∀ (u : UUID) (name : List UInt8),
    (pkgId u name).uuid = if u.value.val = 0 then none else some u) ∧
  (∀ name : List UInt8, pkgIdNothing name = ⟨none, name⟩) ∧
  (∀ (u : UUID) (name : List UInt8),
    binunpack (binpack (pkgId u name)) = .ok (pkgId u name)) ∧
  (∀ name : List UInt8, binunpack (binpack (pkgIdNothing name)) = .ok (pkgIdNothing name)) ∧
  (∀ (hu : Option UUID → UInt64 → UInt64) (hn : List UInt8 → UInt64 → UInt64)
      (p : PkgId) (h : UInt64),
    pkgHash hu hn p h = hn p.name (hu p.uuid (h ^^^ 0xc9f248583a0ca36c)))

theorem pkgIdBehavior : PkgIdBehavior := by
  refine ⟨fun _ _ => rfl, fun _ => rfl, ?_, ?_, fun _ _ _ _ => rfl⟩
  · intro u name
    have hz : (JInt.lit .u128 0).val = 0 := by decide
    by_cases h : u.value.val = 0 <;> simp [binpack, binunpack, pkgId, h, hz]
  · intro name
    have hz : (JInt.lit .u128 0).val = 0 := by decide
    simp [binpack, binunpack, pkgIdNothing, pkgId, hz]

end JuliaLean.IntFuncsCov.UuidPkgid
