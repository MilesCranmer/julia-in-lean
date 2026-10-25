import JuliaLean.Dicts.InvTable

/-!
# `age` arithmetic

`h.age::UInt` counts mutations modulo `2^64`. `ageAdd a n` is `a` after `n`
increments; fewer than `2^64` increments, at least one, change its value.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-- `age` advanced by `n` increments. -/
def ageAdd (a : JInt .u64) (n : Nat) : JInt .u64 := JInt.wrap .u64 (a.val + n)

theorem u64_val_range (a : JInt .u64) : 0 ≤ a.val ∧ a.val < 2 ^ 64 := by
  have h := a.property
  have h1 : IntTy.min .u64 = 0 := by decide
  have h2 : IntTy.max .u64 = 2 ^ 64 - 1 := by decide
  omega

theorem ageAdd_val (a : JInt .u64) (n : Nat) : (ageAdd a n).val = (a.val + n) % 2 ^ 64 := rfl

theorem ageAdd_zero (a : JInt .u64) : ageAdd a 0 = a := by
  apply Subtype.ext
  rw [ageAdd_val]
  have := u64_val_range a
  omega

theorem ageAdd_add (a : JInt .u64) (n k : Nat) : ageAdd (ageAdd a n) k = ageAdd a (n + k) := by
  apply Subtype.ext
  rw [ageAdd_val, ageAdd_val, ageAdd_val]
  omega

theorem bump_eq (a : JInt .u64) : bump a = ageAdd a 1 := by
  have h1 : (JInt.lit .u64 1).val = 1 := by decide
  show JInt.wrap .u64 (a.val + (JInt.lit .u64 1).val) = JInt.wrap .u64 (a.val + ((1 : Nat) : Int))
  rw [h1] <;> rfl

theorem bump_ageAdd (a : JInt .u64) (n : Nat) : bump (ageAdd a n) = ageAdd a (n + 1) := by
  rw [bump_eq, ageAdd_add]

theorem bump_bump (a : JInt .u64) : bump (bump a) = ageAdd a 2 := by
  rw [bump_eq, bump_eq, ageAdd_add]

theorem ageAdd_ne (a : JInt .u64) {n : Nat} (h1 : 0 < n) (h2 : n < 2 ^ 64) :
    (ageAdd a n).val ≠ a.val := by
  rw [ageAdd_val]
  have := u64_val_range a
  omega

/-- `t'` keeps the slots and keys of `t` and at least its `maxprobe`. -/
def Same (t t' : Table K V) : Prop :=
  t'.size = t.size ∧ t'.slots = t.slots ∧ t'.keys = t.keys ∧ t.maxprobe ≤ t'.maxprobe

theorem Same.refl (t : Table K V) : Same t t := ⟨rfl, rfl, rfl, Nat.le_refl _⟩

theorem Same.trans {t1 t2 t3 : Table K V} (h1 : Same t1 t2) (h2 : Same t2 t3) : Same t1 t3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, Nat.le_trans h1.2.2.2 h2.2.2.2⟩

/-- A table operation advanced the age by `n`, and left slots and keys alone when `n = 0`. -/
def AgeStep (t t' : Table K V) (n : Nat) : Prop := t'.age = ageAdd t.age n ∧ (n = 0 → Same t t')

theorem AgeStep.refl (t : Table K V) : AgeStep t t 0 := ⟨(ageAdd_zero _).symm, fun _ => Same.refl t⟩

theorem AgeStep.trans {t1 t2 t3 : Table K V} {n1 n2 : Nat} (h1 : AgeStep t1 t2 n1)
    (h2 : AgeStep t2 t3 n2) : AgeStep t1 t3 (n1 + n2) :=
  ⟨by rw [h2.1, h1.1, ageAdd_add], fun h => (h1.2 (by omega)).trans (h2.2 (by omega))⟩

theorem AgeStep.of_pos {t t' : Table K V} {n : Nat} (h : t'.age = ageAdd t.age n) (hn : 0 < n) :
    AgeStep t t' n := ⟨h, fun h0 => absurd h0 (by omega)⟩

end JuliaLean.Dicts
