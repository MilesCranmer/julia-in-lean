import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.effects

/-!
Properties of `Compiler/src/effects.jl` (`Effects`, `merge_effects`, the `is_*` queries, the
`ipo_purity_bits` encoding) and of the override application in `abstractinterpretation.jl` and
`typeinfer.jl`, and of the C readers of the encoding.

The order on one `UInt8` effect field is the documented one (Compiler/src/effects.jl:74-127):
`ALWAYS_TRUE` is the strongest state, `ALWAYS_FALSE` the weakest, and a conditional state is
weaker the more condition bits it has. `FieldLe x y` says `x` is at least as strong as `y`. On a
`Bool` field `true` is the stronger state. `EffLe a b` is the order taken field by field.

`Valid e` says every field fits the bits `encode_effects` gives it (3 bits for `consistent`, 2
for the other `UInt8` fields). Every constant of `effects.jl` is valid, and `merge_effects`,
`override_effects`, `adjust_effects` and `decode_effects` produce valid values from valid
inputs, so every `Effects` inference builds is valid.
-/

namespace JuliaLean.Proofs.Compiler.src.effects

open JuliaLean.Registry
open JuliaLean.Compiler

instance decForallBool {p : Bool → Prop} [DecidablePred p] : Decidable (∀ b, p b) :=
  decidable_of_iff (p false ∧ p true)
    ⟨fun ⟨h0, h1⟩ b => by cases b <;> assumption, fun h => ⟨h false, h true⟩⟩

/-! ## Orders and validity -/

/-- `x` is at least as strong as `y` in the documented order of an effect field: `y` is
`ALWAYS_FALSE`, or `x` is not `ALWAYS_FALSE` and every bit of `x` is a bit of `y`. -/
def FieldLe (x y : UInt8) : Prop := y = ALWAYS_FALSE ∨ (x ≠ ALWAYS_FALSE ∧ x ||| y = y)

instance (x y : UInt8) : Decidable (FieldLe x y) := by unfold FieldLe; infer_instance

/-- `x` is at least as strong as `y` on a `Bool` effect field. -/
def BoolLe (x y : Bool) : Prop := y = true → x = true

instance (x y : Bool) : Decidable (BoolLe x y) := by unfold BoolLe; infer_instance

/-- `a` is at least as strong as `b` in every field. -/
def EffLe (a b : Effects) : Prop :=
  FieldLe a.consistent b.consistent ∧ FieldLe a.effect_free b.effect_free ∧
  FieldLe a.reset_safe b.reset_safe ∧ BoolLe a.nothrow b.nothrow ∧
  BoolLe a.terminates b.terminates ∧ BoolLe a.notaskstate b.notaskstate ∧
  FieldLe a.inaccessiblememonly b.inaccessiblememonly ∧ FieldLe a.noub b.noub ∧
  FieldLe a.nonoverlayed b.nonoverlayed ∧ BoolLe a.nortcall b.nortcall

instance (a b : Effects) : Decidable (EffLe a b) := by unfold EffLe; infer_instance

/-- Every field fits the bits `encode_effects` stores it in. -/
def Valid (e : Effects) : Prop :=
  e.consistent.toNat < 8 ∧ e.effect_free.toNat < 4 ∧ e.reset_safe.toNat < 4 ∧
  e.inaccessiblememonly.toNat < 4 ∧ e.noub.toNat < 4 ∧ e.nonoverlayed.toNat < 4

instance (e : Effects) : Decidable (Valid e) := by unfold Valid; infer_instance

/-- The states a call's effects take: `consistent` is one of `ALWAYS_TRUE`, `ALWAYS_FALSE`,
`CONSISTENT_IF_NOTRETURNED`, `CONSISTENT_IF_INACCESSIBLEMEMONLY` or their union, and every other
`UInt8` field is `ALWAYS_TRUE`, `ALWAYS_FALSE` or its one conditional state.
`EFFECT_FREE_GLOBALLY` is left out: only single statements have it, and `merge_effects!`
(Compiler/src/inferencestate.jl:1408-1414) turns it into `ALWAYS_TRUE` before a caller sees it. -/
def CallLevel (e : Effects) : Prop :=
  (e.consistent = 0 ∨ e.consistent = 1 ∨ e.consistent = 2 ∨ e.consistent = 4 ∨ e.consistent = 6) ∧
  e.effect_free.toNat < 3 ∧ e.reset_safe.toNat < 3 ∧ e.inaccessiblememonly.toNat < 3 ∧
  e.noub.toNat < 3 ∧ e.nonoverlayed.toNat < 3

instance (e : Effects) : Decidable (CallLevel e) := by unfold CallLevel; infer_instance

/-! ## `UInt8` and `Nat` bit facts -/

theorem u8_eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) : a = b := UInt8.toNat_inj.mp h

theorem or_ne_one {a b : UInt8} (ha : a ≠ 1) (hb : b ≠ 1) : a ||| b ≠ 1 := by
  intro h
  have h' := congrArg UInt8.toNat h
  rw [UInt8.toNat_or] at h'
  have h1 : a.toNat ≤ a.toNat ||| b.toNat := Nat.left_le_or
  have h2 : b.toNat ≤ a.toNat ||| b.toNat := by rw [Nat.or_comm]; exact Nat.left_le_or
  have ha' : a.toNat ≠ 1 := fun e => ha (u8_eq_of_toNat (b := 1) e)
  have hb' : b.toNat ≠ 1 := fun e => hb (u8_eq_of_toNat (b := 1) e)
  have hone : (1 : UInt8).toNat = 1 := rfl
  rw [hone] at h'
  have hx : a.toNat = 0 := by omega
  have hy : b.toNat = 0 := by omega
  rw [hx, hy] at h'
  exact absurd h' (by decide)

theorem or_eq_zero {a b : UInt8} (h : a ||| b = 0) : a = 0 ∧ b = 0 := by
  have h' := congrArg UInt8.toNat h
  rw [UInt8.toNat_or] at h'
  have h1 : a.toNat ≤ a.toNat ||| b.toNat := Nat.left_le_or
  have h2 : b.toNat ≤ a.toNat ||| b.toNat := by rw [Nat.or_comm]; exact Nat.left_le_or
  have hzero : (0 : UInt8).toNat = 0 := rfl
  rw [hzero] at h'
  exact ⟨u8_eq_of_toNat (b := 0) (by omega), u8_eq_of_toNat (b := 0) (by omega)⟩

theorem or_le_two {a b : UInt8} (h : a ||| b = 2) : a.toNat ≤ 2 ∧ b.toNat ≤ 2 := by
  have h' := congrArg UInt8.toNat h
  rw [UInt8.toNat_or] at h'
  have h1 : a.toNat ≤ a.toNat ||| b.toNat := Nat.left_le_or
  have h2 : b.toNat ≤ a.toNat ||| b.toNat := by rw [Nat.or_comm]; exact Nat.left_le_or
  have htwo : (2 : UInt8).toNat = 2 := rfl
  rw [htwo] at h'
  omega

theorem u8_cases3 (y : UInt8) (h : y.toNat ≤ 2) : y = 0 ∨ y = 1 ∨ y = 2 := by
  have : y.toNat = 0 ∨ y.toNat = 1 ∨ y.toNat = 2 := by omega
  rcases this with h | h | h
  · exact Or.inl (u8_eq_of_toNat (b := 0) h)
  · exact Or.inr (Or.inl (u8_eq_of_toNat (b := 1) h))
  · exact Or.inr (Or.inr (u8_eq_of_toNat (b := 2) h))

theorem u8_cases4 (y : UInt8) (h : y.toNat < 4) : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by
  have : y.toNat = 0 ∨ y.toNat = 1 ∨ y.toNat = 2 ∨ y.toNat = 3 := by omega
  rcases this with h | h | h | h
  · exact Or.inl (u8_eq_of_toNat (b := 0) h)
  · exact Or.inr (Or.inl (u8_eq_of_toNat (b := 1) h))
  · exact Or.inr (Or.inr (Or.inl (u8_eq_of_toNat (b := 2) h)))
  · exact Or.inr (Or.inr (Or.inr (u8_eq_of_toNat (b := 3) h)))

theorem or_lt {a b : UInt8} {k : Nat} (ha : a.toNat < 2 ^ k) (hb : b.toNat < 2 ^ k) :
    (a ||| b).toNat < 2 ^ k := by
  rw [UInt8.toNat_or]; exact Nat.or_lt_two_pow ha hb

/-! ## `merge_effectbits` -/

theorem mb_one_left (b : UInt8) : mergeEffectbits 1 b = 1 := by
  simp [mergeEffectbits, ALWAYS_FALSE]

theorem mb_one_right (a : UInt8) : mergeEffectbits a 1 = 1 := by
  simp [mergeEffectbits, ALWAYS_FALSE]

theorem mb_or {a b : UInt8} (ha : a ≠ 1) (hb : b ≠ 1) : mergeEffectbits a b = a ||| b := by
  simp [mergeEffectbits, ALWAYS_FALSE, ha, hb]

theorem mb_comm (a b : UInt8) : mergeEffectbits a b = mergeEffectbits b a := by
  by_cases ha : a = 1
  · subst ha; rw [mb_one_left, mb_one_right]
  by_cases hb : b = 1
  · subst hb; rw [mb_one_left, mb_one_right]
  rw [mb_or ha hb, mb_or hb ha, UInt8.or_comm]

theorem mb_self (a : UInt8) : mergeEffectbits a a = a := by
  by_cases ha : a = 1
  · subst ha; rw [mb_one_left]
  rw [mb_or ha ha, UInt8.or_self]

theorem mb_assoc (a b c : UInt8) :
    mergeEffectbits (mergeEffectbits a b) c = mergeEffectbits a (mergeEffectbits b c) := by
  by_cases ha : a = 1
  · subst ha; simp only [mb_one_left]
  by_cases hb : b = 1
  · subst hb; simp only [mb_one_left, mb_one_right]
  by_cases hc : c = 1
  · subst hc; simp only [mb_one_right]
  rw [mb_or ha hb, mb_or (or_ne_one ha hb) hc, mb_or hb hc, mb_or ha (or_ne_one hb hc),
    UInt8.or_assoc]

theorem mb_ne_one {a b : UInt8} (ha : a ≠ 1) (hb : b ≠ 1) : mergeEffectbits a b ≠ 1 := by
  rw [mb_or ha hb]; exact or_ne_one ha hb

theorem fieldLe_refl (x : UInt8) : FieldLe x x := by
  by_cases h : x = 1
  · exact Or.inl h
  · exact Or.inr ⟨h, UInt8.or_self⟩

theorem fieldLe_zero (y : UInt8) : FieldLe 0 y := by
  by_cases h : y = 1
  · exact Or.inl h
  · exact Or.inr ⟨by decide, UInt8.zero_or⟩

theorem fieldLe_trans {x y z : UInt8} (hxy : FieldLe x y) (hyz : FieldLe y z) : FieldLe x z := by
  rcases hyz with hz | ⟨hy, hyz⟩
  · exact Or.inl hz
  rcases hxy with hy' | ⟨hx, hxy⟩
  · exact absurd hy' hy
  · refine Or.inr ⟨hx, ?_⟩
    rw [← hyz, ← UInt8.or_assoc, hxy]

theorem fieldLe_merge_left (a b : UInt8) : FieldLe a (mergeEffectbits a b) := by
  by_cases ha : a = 1
  · subst ha; rw [mb_one_left]; exact Or.inl rfl
  by_cases hb : b = 1
  · subst hb; rw [mb_one_right]; exact Or.inl rfl
  rw [mb_or ha hb]
  exact Or.inr ⟨ha, by rw [← UInt8.or_assoc, UInt8.or_self]⟩

theorem fieldLe_merge_right (a b : UInt8) : FieldLe b (mergeEffectbits a b) := by
  rw [mb_comm]; exact fieldLe_merge_left b a

theorem fieldLe_merge_lub {a b z : UInt8} (ha : FieldLe a z) (hb : FieldLe b z) :
    FieldLe (mergeEffectbits a b) z := by
  rcases ha with hz | ⟨ha, haz⟩
  · exact Or.inl hz
  rcases hb with hz | ⟨hb, hbz⟩
  · exact Or.inl hz
  rw [mb_or ha hb]
  exact Or.inr ⟨or_ne_one ha hb, by rw [UInt8.or_assoc, hbz, haz]⟩

theorem fieldLe_iff_merge (x y : UInt8) : FieldLe x y ↔ mergeEffectbits x y = y := by
  constructor
  · rintro (hy | ⟨hx, hxy⟩)
    · subst hy; exact mb_one_right x
    · by_cases hy : y = 1
      · subst hy; exact mb_one_right x
      · rw [mb_or hx hy, hxy]
  · intro h
    by_cases hx : x = 1
    · subst hx; rw [mb_one_left] at h; exact Or.inl h.symm
    by_cases hy : y = 1
    · exact Or.inl hy
    · rw [mb_or hx hy] at h; exact Or.inr ⟨hx, h⟩

theorem fieldLe_merge_mono {a a' b b' : UInt8} (ha : FieldLe a a') (hb : FieldLe b b') :
    FieldLe (mergeEffectbits a b) (mergeEffectbits a' b') :=
  fieldLe_merge_lub (fieldLe_trans ha (fieldLe_merge_left a' b'))
    (fieldLe_trans hb (fieldLe_merge_right a' b'))

theorem mb_eq_zero (x y : UInt8) : mergeEffectbits x y = 0 ↔ x = 0 ∧ y = 0 := by
  by_cases hx : x = 1
  · subst hx; rw [mb_one_left]; simp
  by_cases hy : y = 1
  · subst hy; rw [mb_one_right]; simp
  rw [mb_or hx hy]
  constructor
  · exact or_eq_zero
  · rintro ⟨rfl, rfl⟩; rfl

theorem mb_zero_or_two (x y : UInt8) :
    (mergeEffectbits x y = 0 ∨ mergeEffectbits x y = 2) ↔
      ((x = 0 ∨ x = 2) ∧ (y = 0 ∨ y = 2)) := by
  by_cases hx : x = 1
  · subst hx; rw [mb_one_left]; simp
  by_cases hy : y = 1
  · subst hy; rw [mb_one_right]; simp
  rw [mb_or hx hy]
  constructor
  · rintro (h | h)
    · obtain ⟨rfl, rfl⟩ := or_eq_zero h; simp
    · obtain ⟨h1, h2⟩ := or_le_two h
      rcases u8_cases3 x h1 with rfl | rfl | rfl <;> rcases u8_cases3 y h2 with rfl | rfl | rfl <;>
        simp_all
  · rintro ⟨hx' | hx', hy' | hy'⟩ <;> subst hx' <;> subst hy' <;> decide

/-! ## `merge_effects` -/

theorem merge_comm (a b : Effects) : mergeEffects a b = mergeEffects b a := by
  simp only [mergeEffects, mergeEffectbitsBool, mb_comm a.consistent, mb_comm a.effect_free,
    mb_comm a.reset_safe, mb_comm a.inaccessiblememonly, mb_comm a.noub, mb_comm a.nonoverlayed,
    Bool.and_comm a.nothrow, Bool.and_comm a.terminates, Bool.and_comm a.notaskstate,
    Bool.and_comm a.nortcall]

theorem merge_self (a : Effects) : mergeEffects a a = a := by
  cases a; simp only [mergeEffects, mergeEffectbitsBool, mb_self, Bool.and_self]

theorem merge_assoc (a b c : Effects) :
    mergeEffects (mergeEffects a b) c = mergeEffects a (mergeEffects b c) := by
  simp only [mergeEffects, mergeEffectbitsBool, mb_assoc, Bool.and_assoc]

theorem boolLe_refl (x : Bool) : BoolLe x x := id

theorem boolLe_true (y : Bool) : BoolLe true y := fun _ => rfl

theorem effLe_iff_merge (a b : Effects) : EffLe a b ↔ mergeEffects a b = b := by
  obtain ⟨c, ef, rs, nt, te, ns, im, nu, no, rc⟩ := a
  obtain ⟨c', ef', rs', nt', te', ns', im', nu', no', rc'⟩ := b
  simp only [EffLe, BoolLe, mergeEffects, mergeEffectbitsBool, Effects.mk.injEq, fieldLe_iff_merge]
  cases nt <;> cases nt' <;> cases te <;> cases te' <;> cases ns <;> cases ns' <;> cases rc <;>
    cases rc' <;> simp

theorem effLe_merge_left (a b : Effects) : EffLe a (mergeEffects a b) := by
  refine ⟨fieldLe_merge_left _ _, fieldLe_merge_left _ _, fieldLe_merge_left _ _, ?_, ?_, ?_,
    fieldLe_merge_left _ _, fieldLe_merge_left _ _, fieldLe_merge_left _ _, ?_⟩ <;>
    simp [BoolLe, mergeEffects, mergeEffectbitsBool] <;> intro h _ <;> exact h

theorem effLe_merge_right (a b : Effects) : EffLe b (mergeEffects a b) := by
  rw [merge_comm]; exact effLe_merge_left b a

theorem effLe_merge_lub {a b z : Effects} (ha : EffLe a z) (hb : EffLe b z) :
    EffLe (mergeEffects a b) z := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
  refine ⟨fieldLe_merge_lub a1 b1, fieldLe_merge_lub a2 b2, fieldLe_merge_lub a3 b3, ?_, ?_, ?_,
    fieldLe_merge_lub a7 b7, fieldLe_merge_lub a8 b8, fieldLe_merge_lub a9 b9, ?_⟩ <;>
    simp only [BoolLe, mergeEffects, mergeEffectbitsBool, Bool.and_eq_true] at * <;>
    intro h <;> simp_all

theorem effLe_trans {a b c : Effects} (hab : EffLe a b) (hbc : EffLe b c) : EffLe a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hab
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hbc
  exact ⟨fieldLe_trans a1 b1, fieldLe_trans a2 b2, fieldLe_trans a3 b3, fun h => a4 (b4 h),
    fun h => a5 (b5 h), fun h => a6 (b6 h), fieldLe_trans a7 b7, fieldLe_trans a8 b8,
    fieldLe_trans a9 b9, fun h => a10 (b10 h)⟩

theorem effLe_merge_mono {a a' b b' : Effects} (ha : EffLe a a') (hb : EffLe b b') :
    EffLe (mergeEffects a b) (mergeEffects a' b') :=
  effLe_merge_lub (effLe_trans ha (effLe_merge_left a' b')) (effLe_trans hb (effLe_merge_right a' b'))

theorem mb_valid {a b : UInt8} {k : Nat} (hk : 1 ≤ k) (ha : a.toNat < 2 ^ k) (hb : b.toNat < 2 ^ k) :
    (mergeEffectbits a b).toNat < 2 ^ k := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  by_cases ha1 : a = 1
  · subst ha1; rw [mb_one_left]; show 1 < 2 ^ k; omega
  by_cases hb1 : b = 1
  · subst hb1; rw [mb_one_right]; show 1 < 2 ^ k; omega
  rw [mb_or ha1 hb1]; exact or_lt ha hb

theorem merge_valid {a b : Effects} (ha : Valid a) (hb : Valid b) : Valid (mergeEffects a b) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  exact ⟨mb_valid (k := 3) (by decide) a1 b1, mb_valid (k := 2) (by decide) a2 b2,
    mb_valid (k := 2) (by decide) a3 b3, mb_valid (k := 2) (by decide) a4 b4,
    mb_valid (k := 2) (by decide) a5 b5, mb_valid (k := 2) (by decide) a6 b6⟩

/-- `merge_effectbits` is a commutative, associative and idempotent operation on every byte
(and on `Bool`), and its order (`merge_effectbits(x, y) == y`) is the documented order
`FieldLe`, in which it is the least upper bound and monotone in both arguments. On `Bool`
(where `true` means the property holds) the merge keeps a property exactly when both sides
have it, so it is the least upper bound in the order `true` before `false`: a side that
throws makes the merge throw. -/
def MergeEffectbitsLaws : Prop :=
  (∀ a b : UInt8, mergeEffectbits a b = mergeEffectbits b a) ∧
  (∀ a b c : UInt8, mergeEffectbits (mergeEffectbits a b) c = mergeEffectbits a (mergeEffectbits b c)) ∧
  (∀ a : UInt8, mergeEffectbits a a = a) ∧
  (∀ x y : UInt8, FieldLe x y ↔ mergeEffectbits x y = y) ∧
  (∀ a b : UInt8, FieldLe a (mergeEffectbits a b) ∧ FieldLe b (mergeEffectbits a b)) ∧
  (∀ a b z : UInt8, FieldLe a z → FieldLe b z → FieldLe (mergeEffectbits a b) z) ∧
  (∀ a a' b b' : UInt8, FieldLe a a' → FieldLe b b' →
    FieldLe (mergeEffectbits a b) (mergeEffectbits a' b')) ∧
  (∀ a b : Bool, mergeEffectbitsBool a b = mergeEffectbitsBool b a) ∧
  (∀ a b c : Bool, mergeEffectbitsBool (mergeEffectbitsBool a b) c =
    mergeEffectbitsBool a (mergeEffectbitsBool b c)) ∧
  (∀ a : Bool, mergeEffectbitsBool a a = a) ∧
  (∀ a b : Bool, mergeEffectbitsBool a b = true ↔ (a = true ∧ b = true))

theorem mergeEffectbitsLaws_proven : MergeEffectbitsLaws :=
  ⟨mb_comm, mb_assoc, mb_self, fieldLe_iff_merge,
    fun a b => ⟨fieldLe_merge_left a b, fieldLe_merge_right a b⟩,
    fun _ _ _ => fieldLe_merge_lub, fun _ _ _ _ => fieldLe_merge_mono,
    fun a b => Bool.and_comm a b, fun a b c => Bool.and_assoc a b c, fun a => Bool.and_self a,
    fun a b => by cases a <;> cases b <;> decide⟩

/-- `merge_effects` is commutative, associative and idempotent, so the merged effects of a
method do not depend on the order in which inference visits its statements. Its order is
`EffLe`, in which it is the least upper bound and monotone in both arguments, and it keeps
every field within its encoded width. -/
def MergeEffectsLaws : Prop :=
  (∀ a b : Effects, mergeEffects a b = mergeEffects b a) ∧
  (∀ a b c : Effects, mergeEffects (mergeEffects a b) c = mergeEffects a (mergeEffects b c)) ∧
  (∀ a : Effects, mergeEffects a a = a) ∧
  (∀ a b : Effects, EffLe a b ↔ mergeEffects a b = b) ∧
  (∀ a b : Effects, EffLe a (mergeEffects a b) ∧ EffLe b (mergeEffects a b)) ∧
  (∀ a b z : Effects, EffLe a z → EffLe b z → EffLe (mergeEffects a b) z) ∧
  (∀ a a' b b' : Effects, EffLe a a' → EffLe b b' → EffLe (mergeEffects a b) (mergeEffects a' b')) ∧
  (∀ a b : Effects, Valid a → Valid b → Valid (mergeEffects a b))

theorem mergeEffectsLaws_proven : MergeEffectsLaws :=
  ⟨merge_comm, merge_assoc, merge_self, effLe_iff_merge,
    fun a b => ⟨effLe_merge_left a b, effLe_merge_right a b⟩,
    fun _ _ _ => effLe_merge_lub, fun _ _ _ _ => effLe_merge_mono, fun _ _ => merge_valid⟩

/-! ## The queries and `merge_effects` -/

/-- Each query reads exactly the field test of its source line (Compiler/src/effects.jl:326-369). -/
def QueriesFields : Prop := ∀ (e : Effects) (cr : Bool),
  isConsistent e = (e.consistent == ALWAYS_TRUE) ∧ isEffectFree e = (e.effect_free == ALWAYS_TRUE) ∧
  isResetSafe e = (e.reset_safe == ALWAYS_TRUE) ∧ isNothrow e = e.nothrow ∧
  isTerminates e = e.terminates ∧ isNotaskstate e = e.notaskstate ∧
  isInaccessiblememonly e = (e.inaccessiblememonly == ALWAYS_TRUE) ∧ isNoub e = (e.noub == ALWAYS_TRUE) ∧
  isNoubIfNoinbounds e = (e.noub == NOUB_IF_NOINBOUNDS) ∧ isNonoverlayed e = (e.nonoverlayed == ALWAYS_TRUE) ∧
  isNortcall e = e.nortcall ∧
  isFoldable e cr = ((e.consistent == ALWAYS_TRUE) && (e.noub == ALWAYS_TRUE || e.noub == NOUB_IF_NOINBOUNDS) &&
    (e.effect_free == ALWAYS_TRUE) && e.terminates && (!cr || e.nortcall)) ∧
  isFoldableNothrow e cr = (isFoldable e cr && e.nothrow) ∧
  isRemovableIfUnused e = ((e.effect_free == ALWAYS_TRUE) && e.terminates && e.nothrow) ∧
  isFinalizerInlineable e = (e.nothrow && e.notaskstate) ∧
  isConsistentIfNotreturned e = (e.consistent &&& CONSISTENT_IF_NOTRETURNED != 0) ∧
  isConsistentIfInaccessiblememonly e = (e.consistent &&& CONSISTENT_IF_INACCESSIBLEMEMONLY != 0) ∧
  isEffectFreeIfInaccessiblememonly e = (e.effect_free &&& EFFECT_FREE_IF_INACCESSIBLEMEMONLY != 0) ∧
  isResetSafeIfInaccessiblememonly e = (e.reset_safe &&& RESET_SAFE_IF_INACCESSIBLEMEMONLY != 0) ∧
  isInaccessiblememOrArgmemonly e = (e.inaccessiblememonly == INACCESSIBLEMEM_OR_ARGMEMONLY) ∧
  isConsistentOverlay e = (e.nonoverlayed == CONSISTENT_OVERLAY)

theorem queriesFields_proven : QueriesFields := fun _ _ =>
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Each query that asks for a full-strength state (`ALWAYS_TRUE` or `true`), and each query
built from them (`is_foldable` with either `check_rtcall`, `is_foldable_nothrow`,
`is_removable_if_unused`, `is_finalizer_inlineable`), holds of `merge_effects(a, b)` exactly when
it holds of both `a` and `b`; and every query reads the field test of its source line. -/
def QueriesMerge : Prop := QueriesFields ∧ ∀ a b : Effects,
  (isConsistent (mergeEffects a b) = (isConsistent a && isConsistent b)) ∧
  (isEffectFree (mergeEffects a b) = (isEffectFree a && isEffectFree b)) ∧
  (isResetSafe (mergeEffects a b) = (isResetSafe a && isResetSafe b)) ∧
  (isNothrow (mergeEffects a b) = (isNothrow a && isNothrow b)) ∧
  (isTerminates (mergeEffects a b) = (isTerminates a && isTerminates b)) ∧
  (isNotaskstate (mergeEffects a b) = (isNotaskstate a && isNotaskstate b)) ∧
  (isInaccessiblememonly (mergeEffects a b) = (isInaccessiblememonly a && isInaccessiblememonly b)) ∧
  (isNoub (mergeEffects a b) = (isNoub a && isNoub b)) ∧
  (isNonoverlayed (mergeEffects a b) = (isNonoverlayed a && isNonoverlayed b)) ∧
  (isNortcall (mergeEffects a b) = (isNortcall a && isNortcall b)) ∧
  (∀ cr, isFoldable (mergeEffects a b) cr = (isFoldable a cr && isFoldable b cr)) ∧
  (∀ cr, isFoldableNothrow (mergeEffects a b) cr = (isFoldableNothrow a cr && isFoldableNothrow b cr)) ∧
  (isRemovableIfUnused (mergeEffects a b) = (isRemovableIfUnused a && isRemovableIfUnused b)) ∧
  (isFinalizerInlineable (mergeEffects a b) = (isFinalizerInlineable a && isFinalizerInlineable b))

theorem noub_two : NOUB_IF_NOINBOUNDS = 2 := by decide

theorem queriesMerge_proven : QueriesMerge := by
  refine ⟨queriesFields_proven, ?_⟩
  intro a b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try intro cr)
  all_goals (try cases cr)
  all_goals
    apply Bool.eq_iff_iff.mpr
    simp only [isConsistent, isEffectFree, isResetSafe, isNothrow, isTerminates, isNotaskstate,
      isInaccessiblememonly, isNoub, isNonoverlayed, isNortcall, isFoldable, isFoldableNothrow,
      isNoubIfNoinbounds, isRemovableIfUnused, isFinalizerInlineable, mergeEffects,
      mergeEffectbitsBool, ALWAYS_TRUE, noub_two, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    try simp only [mb_zero_or_two]
    try simp [mb_eq_zero, and_assoc, and_comm, and_left_comm]

/-! ## The queries on the named states -/

/-- `e` with one field replaced, starting from `EFFECTS_TOTAL`. -/
def withC (v : UInt8) : Effects := Effects.kw EFFECTS_TOTAL (consistent := v)
def withEF (v : UInt8) : Effects := Effects.kw EFFECTS_TOTAL (effect_free := v)
def withRS (v : UInt8) : Effects := Effects.kw EFFECTS_TOTAL (reset_safe := v)
def withIM (v : UInt8) : Effects := Effects.kw EFFECTS_TOTAL (inaccessiblememonly := v)
def withNU (v : UInt8) : Effects := Effects.kw EFFECTS_TOTAL (noub := v)
def withNO (v : UInt8) : Effects := Effects.kw EFFECTS_TOTAL (nonoverlayed := v)

/-- On the named states of each field (the constants of Compiler/src/effects.jl:168-195), each
query is true exactly at the state it names: the full-strength queries at `ALWAYS_TRUE` only,
`is_consistent_if_notreturned` at `CONSISTENT_IF_NOTRETURNED` and its union with
`CONSISTENT_IF_INACCESSIBLEMEMONLY`, `is_consistent_if_inaccessiblememonly` at
`CONSISTENT_IF_INACCESSIBLEMEMONLY` and that union, `is_reset_safe_if_inaccessiblememonly`,
`is_inaccessiblemem_or_argmemonly`, `is_noub_if_noinbounds` and `is_consistent_overlay` at their
one conditional state. Every query also reads the field test of its source line. -/
def QueriesNamedStates : Prop := QueriesFields ∧ (
  (∀ v ∈ [ALWAYS_TRUE, ALWAYS_FALSE, CONSISTENT_IF_NOTRETURNED, CONSISTENT_IF_INACCESSIBLEMEMONLY,
      CONSISTENT_IF_NOTRETURNED ||| CONSISTENT_IF_INACCESSIBLEMEMONLY],
    isConsistent (withC v) = (v == ALWAYS_TRUE) ∧
    isConsistentIfNotreturned (withC v) =
      (v == CONSISTENT_IF_NOTRETURNED || v == CONSISTENT_IF_NOTRETURNED ||| CONSISTENT_IF_INACCESSIBLEMEMONLY) ∧
    isConsistentIfInaccessiblememonly (withC v) =
      (v == CONSISTENT_IF_INACCESSIBLEMEMONLY ||
        v == CONSISTENT_IF_NOTRETURNED ||| CONSISTENT_IF_INACCESSIBLEMEMONLY)) ∧
  (∀ v ∈ [ALWAYS_TRUE, ALWAYS_FALSE, EFFECT_FREE_IF_INACCESSIBLEMEMONLY, EFFECT_FREE_GLOBALLY],
    isEffectFree (withEF v) = (v == ALWAYS_TRUE)) ∧
  (∀ v ∈ [ALWAYS_TRUE, ALWAYS_FALSE, RESET_SAFE_IF_INACCESSIBLEMEMONLY],
    isResetSafe (withRS v) = (v == ALWAYS_TRUE) ∧
    isResetSafeIfInaccessiblememonly (withRS v) = (v == RESET_SAFE_IF_INACCESSIBLEMEMONLY)) ∧
  (∀ v ∈ [ALWAYS_TRUE, ALWAYS_FALSE, INACCESSIBLEMEM_OR_ARGMEMONLY],
    isInaccessiblememonly (withIM v) = (v == ALWAYS_TRUE) ∧
    isInaccessiblememOrArgmemonly (withIM v) = (v == INACCESSIBLEMEM_OR_ARGMEMONLY)) ∧
  (∀ v ∈ [ALWAYS_TRUE, ALWAYS_FALSE, NOUB_IF_NOINBOUNDS],
    isNoub (withNU v) = (v == ALWAYS_TRUE) ∧ isNoubIfNoinbounds (withNU v) = (v == NOUB_IF_NOINBOUNDS)) ∧
  (∀ v ∈ [ALWAYS_TRUE, ALWAYS_FALSE, CONSISTENT_OVERLAY],
    isNonoverlayed (withNO v) = (v == ALWAYS_TRUE) ∧ isConsistentOverlay (withNO v) = (v == CONSISTENT_OVERLAY)))

theorem queriesNamedStates_proven : QueriesNamedStates := ⟨queriesFields_proven, by decide⟩

/-- `is_effect_free_if_inaccessiblememonly` is true exactly at `EFFECT_FREE_IF_INACCESSIBLEMEMONLY`
among the named `effect_free` states (its body is the bit test `effect_free &
EFFECT_FREE_IF_INACCESSIBLEMEMONLY != 0`, see `QueriesFields`). -/
def EffectFreeIfIamoNamedStates : Prop :=
  ∀ v ∈ [ALWAYS_TRUE, ALWAYS_FALSE, EFFECT_FREE_IF_INACCESSIBLEMEMONLY, EFFECT_FREE_GLOBALLY],
    isEffectFreeIfInaccessiblememonly (withEF v) = (v == EFFECT_FREE_IF_INACCESSIBLEMEMONLY)

/-- `EFFECT_FREE_GLOBALLY` is `0x03`, the bit union of `ALWAYS_FALSE` and
`EFFECT_FREE_IF_INACCESSIBLEMEMONLY`, so the conditional query reads it as conditional, and
`merge_effectbits(EFFECT_FREE_GLOBALLY, EFFECT_FREE_IF_INACCESSIBLEMEMONLY)` is
`EFFECT_FREE_GLOBALLY`, which drops the condition. -/
theorem effectFreeIfIamoNamedStates_refuted : ¬ EffectFreeIfIamoNamedStates := by
  intro h
  have := h EFFECT_FREE_GLOBALLY (by simp)
  revert this; decide

theorem globally_merge_drops_condition :
    mergeEffectbits EFFECT_FREE_GLOBALLY EFFECT_FREE_IF_INACCESSIBLEMEMONLY = EFFECT_FREE_GLOBALLY ∧
    EFFECT_FREE_GLOBALLY = ALWAYS_FALSE ||| EFFECT_FREE_IF_INACCESSIBLEMEMONLY := by decide

/-! ## `is_better_effects` -/

/-- On call-level states, `is_better_effects(new, old)` holds exactly when `new` differs from
`old` and is at least as strong in every field (`merge_effects(new, old) == old`). -/
def IsBetterEffectsOrder : Prop :=
  ∀ new old : Effects, CallLevel new → CallLevel old →
    (isBetterEffects new old = true ↔ (new ≠ old ∧ EffLe new old))

/-- `is_better_effects` calls `CONSISTENT_IF_NOTRETURNED` better than
`CONSISTENT_IF_INACCESSIBLEMEMONLY` and the reverse too; the two are incomparable. -/
theorem isBetterEffectsOrder_refuted : ¬ IsBetterEffectsOrder := by
  intro h
  have := (h (withC CONSISTENT_IF_NOTRETURNED) (withC CONSISTENT_IF_INACCESSIBLEMEMONLY)
    (by decide) (by decide)).mp (by decide)
  revert this; decide

/-- The other direction fails too: `CONSISTENT_IF_NOTRETURNED` is strictly stronger than the
union of both conditions, but `is_better_effects` does not say so; and the union is called
better than `CONSISTENT_IF_INACCESSIBLEMEMONLY` although it is weaker. -/
theorem isBetterEffects_more_counterexamples :
    isBetterEffects (withC CONSISTENT_IF_INACCESSIBLEMEMONLY) (withC CONSISTENT_IF_NOTRETURNED) = true ∧
    isBetterEffects (withC CONSISTENT_IF_NOTRETURNED)
      (withC (CONSISTENT_IF_NOTRETURNED ||| CONSISTENT_IF_INACCESSIBLEMEMONLY)) = false ∧
    EffLe (withC CONSISTENT_IF_NOTRETURNED)
      (withC (CONSISTENT_IF_NOTRETURNED ||| CONSISTENT_IF_INACCESSIBLEMEMONLY)) ∧
    isBetterEffects (withC (CONSISTENT_IF_NOTRETURNED ||| CONSISTENT_IF_INACCESSIBLEMEMONLY))
      (withC CONSISTENT_IF_INACCESSIBLEMEMONLY) = true ∧
    ¬ EffLe (withC (CONSISTENT_IF_NOTRETURNED ||| CONSISTENT_IF_INACCESSIBLEMEMONLY))
      (withC CONSISTENT_IF_INACCESSIBLEMEMONLY) := by decide

/-! ## Encoding -/

theorem or_add (x y k : Nat) (h : x < 2 ^ k) : x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm]

theorem or8 (x y : Nat) (h : x < 8) : x ||| y * 8 = x + y * 8 := or_add x y 3 h
theorem or32 (x y : Nat) (h : x < 32) : x ||| y * 32 = x + y * 32 := or_add x y 5 h
theorem or64 (x y : Nat) (h : x < 64) : x ||| y * 64 = x + y * 64 := or_add x y 6 h
theorem or128 (x y : Nat) (h : x < 128) : x ||| y * 128 = x + y * 128 := or_add x y 7 h
theorem or256 (x y : Nat) (h : x < 256) : x ||| y * 256 = x + y * 256 := or_add x y 8 h
theorem or1024 (x y : Nat) (h : x < 1024) : x ||| y * 1024 = x + y * 1024 := or_add x y 10 h
theorem or4096 (x y : Nat) (h : x < 4096) : x ||| y * 4096 = x + y * 4096 := or_add x y 12 h
theorem or16384 (x y : Nat) (h : x < 16384) : x ||| y * 16384 = x + y * 16384 := or_add x y 14 h
theorem or32768 (x y : Nat) (h : x < 32768) : x ||| y * 32768 = x + y * 32768 := or_add x y 15 h

theorem sh0 (x : UInt8) : (x.toUInt32 <<< (0 : UInt32)).toNat = x.toNat := by
  have h : x.toNat < 256 := x.toNat_lt
  simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; try omega
theorem sh3 (x : UInt8) : (x.toUInt32 <<< (3 : UInt32)).toNat = x.toNat * 8 := by
  have h : x.toNat < 256 := x.toNat_lt
  simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; try omega
theorem sh8 (x : UInt8) : (x.toUInt32 <<< (8 : UInt32)).toNat = x.toNat * 256 := by
  have h : x.toNat < 256 := x.toNat_lt
  simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; try omega
theorem sh10 (x : UInt8) : (x.toUInt32 <<< (10 : UInt32)).toNat = x.toNat * 1024 := by
  have h : x.toNat < 256 := x.toNat_lt
  simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; try omega
theorem sh12 (x : UInt8) : (x.toUInt32 <<< (12 : UInt32)).toNat = x.toNat * 4096 := by
  have h : x.toNat < 256 := x.toNat_lt
  simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; try omega
theorem sh15 (x : UInt8) : (x.toUInt32 <<< (15 : UInt32)).toNat = x.toNat * 32768 := by
  have h : x.toNat < 256 := x.toNat_lt
  simp; try omega
theorem shB5 (b : Bool) : (boolU32 b <<< (5 : UInt32)).toNat = b.toNat * 32 := by cases b <;> decide
theorem shB6 (b : Bool) : (boolU32 b <<< (6 : UInt32)).toNat = b.toNat * 64 := by cases b <;> decide
theorem shB7 (b : Bool) : (boolU32 b <<< (7 : UInt32)).toNat = b.toNat * 128 := by cases b <;> decide
theorem shB14 (b : Bool) : (boolU32 b <<< (14 : UInt32)).toNat = b.toNat * 16384 := by
  cases b <;> decide

/-- The word `encode_effects` stores, as a number, for a valid `Effects`. -/
def encN (e : Effects) : Nat :=
  e.consistent.toNat + e.effect_free.toNat * 8 + e.nothrow.toNat * 32 + e.terminates.toNat * 64 +
    e.notaskstate.toNat * 128 + e.inaccessiblememonly.toNat * 256 + e.noub.toNat * 1024 +
    e.nonoverlayed.toNat * 4096 + e.nortcall.toNat * 16384 + e.reset_safe.toNat * 32768

theorem encode_toNat (e : Effects) (hv : Valid e) : (encodeEffects e).toNat = encN e := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  have b1 := Bool.toNat_le e.nothrow
  have b2 := Bool.toNat_le e.terminates
  have b3 := Bool.toNat_le e.notaskstate
  have b4 := Bool.toNat_le e.nortcall
  simp only [encodeEffects, encN, UInt32.toNat_or, sh0, sh3, sh8, sh10, sh12, sh15, shB5, shB6,
    shB7, shB14]
  simp (disch := omega) only [or8, or32, or64, or128, or256, or1024, or4096, or16384, or32768]

theorem fld (w k m : UInt32) (j : Nat) (hk : k.toNat < 32) (hm : m.toNat = 2 ^ j - 1) :
    ((w >>> k) &&& m).toNat = w.toNat / 2 ^ k.toNat % 2 ^ j := by
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow, hm,
    Nat.and_two_pow_sub_one_eq_mod]

theorem u8fld (x : UInt32) (h : x.toNat < 256) : x.toUInt8.toNat = x.toNat := by
  rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt h

theorem bnefld (x : UInt32) (h : x.toNat < 2) : (x != 0) = (x.toNat == 1) := by
  have : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases this with h' | h'
  · have : x = 0 := (UInt32.toNat_inj (a := x) (b := 0)).mp h'
    subst this; rfl
  · have hx : x ≠ 0 := fun e => by rw [e] at h'; exact absurd h' (by decide)
    simp [hx, h']

theorem dC (w : UInt32) : ((w >>> 0) &&& 0x07).toUInt8.toNat = w.toNat % 8 := by
  rw [u8fld _ (by rw [fld w 0 7 3 (by decide) (by decide)]; omega), fld w 0 7 3 (by decide) (by decide)]
  simp
theorem dU (w : UInt32) (k : UInt32) (hk : k.toNat < 32) :
    ((w >>> k) &&& 0x03).toUInt8.toNat = w.toNat / 2 ^ k.toNat % 4 := by
  rw [u8fld _ (by rw [fld w k 3 2 hk (by decide)]; omega), fld w k 3 2 hk (by decide)]
theorem dB (w : UInt32) (k : UInt32) (hk : k.toNat < 32) :
    ((w >>> k) &&& 0x01 != 0) = (w.toNat / 2 ^ k.toNat % 2 == 1) := by
  rw [bnefld _ (by rw [fld w k 1 1 hk (by decide)]; omega), fld w k 1 1 hk (by decide)]

theorem bool_of_mod (b : Bool) (n : Nat) (h : n % 2 = b.toNat) : (n % 2 == 1) = b := by
  cases b <;> simp_all

theorem decode_encode_valid (e : Effects) (hv : Valid e) : decodeEffects (encodeEffects e) = e := by
  have hn := encode_toNat e hv
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  obtain ⟨c, ef, rs, nt, te, ns, im, nu, no, rc⟩ := e
  have b1 := Bool.toNat_le nt
  have b2 := Bool.toNat_le te
  have b3 := Bool.toNat_le ns
  have b4 := Bool.toNat_le rc
  simp only [encN] at hn h1 h2 h3 h4 h5 h6
  simp only [decodeEffects, Effects.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply u8_eq_of_toNat; rw [dC, hn]; omega
  · apply u8_eq_of_toNat; rw [dU _ 3 (by decide), hn]; show _ / 8 % 4 = _; omega
  · apply u8_eq_of_toNat; rw [dU _ 15 (by decide), hn]; show _ / 32768 % 4 = _; omega
  · rw [dB _ 5 (by decide), hn]; apply bool_of_mod; show _ / 32 % 2 = _; omega
  · rw [dB _ 6 (by decide), hn]; apply bool_of_mod; show _ / 64 % 2 = _; omega
  · rw [dB _ 7 (by decide), hn]; apply bool_of_mod; show _ / 128 % 2 = _; omega
  · apply u8_eq_of_toNat; rw [dU _ 8 (by decide), hn]; show _ / 256 % 4 = _; omega
  · apply u8_eq_of_toNat; rw [dU _ 10 (by decide), hn]; show _ / 1024 % 4 = _; omega
  · apply u8_eq_of_toNat; rw [dU _ 12 (by decide), hn]; show _ / 4096 % 4 = _; omega
  · rw [dB _ 14 (by decide), hn]; apply bool_of_mod; show _ / 16384 % 2 = _; omega

theorem decode_valid (w : UInt32) : Valid (decodeEffects w) := by
  simp only [Valid, decodeEffects]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dC]; omega
  all_goals (rw [dU _ _ (by decide)]; omega)

theorem bool_toNat_mod (n : Nat) : (n % 2 == 1).toNat = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem encode_decode (w : UInt32) : encodeEffects (decodeEffects w) = w &&& 0x1ffff := by
  apply UInt32.toNat_inj.mp
  rw [encode_toNat _ (decode_valid w)]
  simp only [encN, decodeEffects]
  rw [dC, dU _ 3 (by decide), dU _ 15 (by decide), dU _ 8 (by decide), dU _ 10 (by decide),
    dU _ 12 (by decide), dB _ 5 (by decide), dB _ 6 (by decide), dB _ 7 (by decide),
    dB _ 14 (by decide), bool_toNat_mod, bool_toNat_mod, bool_toNat_mod, bool_toNat_mod,
    UInt32.toNat_and]
  have hm : w.toNat &&& (0x1ffff : UInt32).toNat = w.toNat % 131072 :=
    Nat.and_two_pow_sub_one_eq_mod _ 17
  rw [hm]
  show w.toNat % 8 + w.toNat / 8 % 4 * 8 + w.toNat / 32 % 2 * 32 + w.toNat / 64 % 2 * 64 +
    w.toNat / 128 % 2 * 128 + w.toNat / 256 % 4 * 256 + w.toNat / 1024 % 4 * 1024 +
    w.toNat / 4096 % 4 * 4096 + w.toNat / 16384 % 2 * 16384 + w.toNat / 32768 % 4 * 32768 =
    w.toNat % 131072
  omega

/-- The `ipo_purity_bits` encoding loses nothing: `decode_effects(encode_effects(e)) == e` for
every valid `Effects` (every field within its 3- or 2-bit slot; inference only builds valid ones),
the encoding uses only the low 17 bits, `decode_effects` always returns a valid `Effects`, and
`encode_effects(decode_effects(w))` keeps exactly the low 17 bits of `w`. So no two fields share
a bit, and no field is cut when a `CodeInstance` is written to a package image and read back. -/
def EncodeDecodeEffects : Prop :=
  (∀ e : Effects, Valid e → decodeEffects (encodeEffects e) = e) ∧
  (∀ e : Effects, Valid e → (encodeEffects e).toNat < 2 ^ 17) ∧
  (∀ w : UInt32, Valid (decodeEffects w)) ∧
  (∀ w : UInt32, encodeEffects (decodeEffects w) = w &&& 0x1ffff)

theorem encodeDecodeEffects_proven : EncodeDecodeEffects := by
  refine ⟨decode_encode_valid, ?_, decode_valid, encode_decode⟩
  intro e hv
  rw [encode_toNat e hv]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  have b1 := Bool.toNat_le e.nothrow
  have b2 := Bool.toNat_le e.terminates
  have b3 := Bool.toNat_le e.notaskstate
  have b4 := Bool.toNat_le e.nortcall
  simp only [encN]
  show _ < 131072
  omega

/-- Every constant of Compiler/src/effects.jl:168-200 is a valid, call-level state. -/
def ConstantsValid : Prop :=
  Valid EFFECTS_TOTAL ∧ Valid EFFECTS_THROWS ∧ Valid EFFECTS_UNKNOWN ∧ Valid EFFECTS_MINIMAL ∧
  CallLevel EFFECTS_TOTAL ∧ CallLevel EFFECTS_THROWS ∧ CallLevel EFFECTS_UNKNOWN ∧ CallLevel EFFECTS_MINIMAL ∧
  (∀ v ∈ [ALWAYS_TRUE, ALWAYS_FALSE, CONSISTENT_IF_NOTRETURNED, CONSISTENT_IF_INACCESSIBLEMEMONLY,
      CONSISTENT_IF_NOTRETURNED ||| CONSISTENT_IF_INACCESSIBLEMEMONLY], v.toNat < 8) ∧
  (∀ v ∈ [EFFECT_FREE_IF_INACCESSIBLEMEMONLY, EFFECT_FREE_GLOBALLY, INACCESSIBLEMEM_OR_ARGMEMONLY,
      NOUB_IF_NOINBOUNDS, CONSISTENT_OVERLAY, RESET_SAFE_IF_INACCESSIBLEMEMONLY], v.toNat < 4)

theorem constantsValid_proven : ConstantsValid := by unfold ConstantsValid; decide

/-! ## Overrides and their storage -/

/-- The arguments of `Expr(:purity, ...)` that `form_purity_expr(eo)` builds
(base/expr.jl:1066-1072): the fields of `eo` in declaration order. -/
def overrideArgs (eo : EffectsOverride) : List Bool :=
  [eo.consistent, eo.effect_free, eo.nothrow, eo.terminates_globally, eo.terminates_locally,
    eo.notaskstate, eo.inaccessiblememonly, eo.noub, eo.noub_if_noinbounds, eo.consistent_overlay,
    eo.nortcall]

/-- An override survives every place it is stored: `decode_effects_override(encode_effects_override(eo))
== eo`; the `Method.purity` bits that `jl_method_set_source` (src/method.c) builds from
`form_purity_expr(eo)` decode to `eo`; and the statement flag it builds inside an `@assume_effects`
region decodes to `eo` with `decode_statement_effects_override`, whatever the three IR flag bits
below it (`@inbounds`, `@inline`, `@noinline`). -/
def OverrideStorage : Prop :=
  ∀ eo : EffectsOverride,
    decodeEffectsOverride (encodeEffectsOverride eo) = eo ∧
    decodeEffectsOverride (methodPurityBits [overrideArgs eo]) = eo ∧
    ∀ low : UInt32, low.toNat < 8 →
      decodeStatementEffectsOverride (statementPurityFlag [overrideArgs eo] ||| low) = eo

theorem overrideStorage_bools : ∀ a b c d e f g h i j k : Bool,
    decodeEffectsOverride (encodeEffectsOverride ⟨a, b, c, d, e, f, g, h, i, j, k⟩) =
      ⟨a, b, c, d, e, f, g, h, i, j, k⟩ ∧
    decodeEffectsOverride (methodPurityBits [overrideArgs ⟨a, b, c, d, e, f, g, h, i, j, k⟩]) =
      ⟨a, b, c, d, e, f, g, h, i, j, k⟩ ∧
    ∀ l0 l1 l2 : Bool,
      decodeStatementEffectsOverride (statementPurityFlag [overrideArgs ⟨a, b, c, d, e, f, g, h, i, j, k⟩] |||
        (boolU32 l0 ||| boolU32 l1 <<< 1 ||| boolU32 l2 <<< 2)) = ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := by
  decide +kernel

theorem low_bits (low : UInt32) (h : low.toNat < 8) :
    ∃ l0 l1 l2 : Bool, low = boolU32 l0 ||| boolU32 l1 <<< 1 ||| boolU32 l2 <<< 2 := by
  have : low.toNat = 0 ∨ low.toNat = 1 ∨ low.toNat = 2 ∨ low.toNat = 3 ∨ low.toNat = 4 ∨
      low.toNat = 5 ∨ low.toNat = 6 ∨ low.toNat = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h
  · exact ⟨false, false, false, UInt32.toNat_inj.mp (by rw [h]; decide)⟩
  · exact ⟨true, false, false, UInt32.toNat_inj.mp (by rw [h]; decide)⟩
  · exact ⟨false, true, false, UInt32.toNat_inj.mp (by rw [h]; decide)⟩
  · exact ⟨true, true, false, UInt32.toNat_inj.mp (by rw [h]; decide)⟩
  · exact ⟨false, false, true, UInt32.toNat_inj.mp (by rw [h]; decide)⟩
  · exact ⟨true, false, true, UInt32.toNat_inj.mp (by rw [h]; decide)⟩
  · exact ⟨false, true, true, UInt32.toNat_inj.mp (by rw [h]; decide)⟩
  · exact ⟨true, true, true, UInt32.toNat_inj.mp (by rw [h]; decide)⟩

theorem overrideStorage_proven : OverrideStorage := by
  rintro ⟨a, b, c, d, e, f, g, h, i, j, k⟩
  obtain ⟨h1, h2, h3⟩ := overrideStorage_bools a b c d e f g h i j k
  refine ⟨h1, h2, ?_⟩
  intro low hl
  obtain ⟨l0, l1, l2, rfl⟩ := low_bits low hl
  exact h3 l0 l1 l2

/-- `override_effects(effects, override)` (the call-site and `ccall` override) sets each field
the override names to its strongest state (`noub_if_noinbounds` gives `NOUB_IF_NOINBOUNDS`
unless `noub` is already `ALWAYS_TRUE`), leaves every other field unchanged, and so never
weakens a valid `Effects` and keeps it valid. -/
def OverrideEffectsStrengthens : Prop :=
  ∀ (e : Effects) (eo : EffectsOverride), Valid e →
    overrideEffects e eo =
      ⟨if eo.consistent then ALWAYS_TRUE else e.consistent,
       if eo.effect_free then ALWAYS_TRUE else e.effect_free,
       e.reset_safe,
       if eo.nothrow then true else e.nothrow,
       if eo.terminates_globally then true else e.terminates,
       if eo.notaskstate then true else e.notaskstate,
       if eo.inaccessiblememonly then ALWAYS_TRUE else e.inaccessiblememonly,
       if eo.noub then ALWAYS_TRUE
         else if (eo.noub_if_noinbounds && e.noub != ALWAYS_TRUE) = true then NOUB_IF_NOINBOUNDS
         else e.noub,
       e.nonoverlayed,
       if eo.nortcall then true else e.nortcall⟩ ∧
    EffLe (overrideEffects e eo) e ∧ Valid (overrideEffects e eo)

theorem ite_fieldLe (c : Bool) (y : UInt8) : FieldLe (if c then ALWAYS_TRUE else y) y := by
  cases c
  · exact fieldLe_refl y
  · exact fieldLe_zero y

theorem ite_boolLe (c y : Bool) : BoolLe (if c then true else y) y := by
  cases c
  · exact boolLe_refl y
  · exact boolLe_true y

theorem noub_fieldLe (c d : Bool) (y : UInt8) (hy : y.toNat < 4) :
    FieldLe (if c then ALWAYS_TRUE else if (d && y != ALWAYS_TRUE) = true then NOUB_IF_NOINBOUNDS else y) y := by
  cases c
  · cases d
    · exact fieldLe_refl y
    · rcases u8_cases4 y hy with rfl | rfl | rfl | rfl <;> decide
  · exact fieldLe_zero y

theorem noub_valid (c d : Bool) (y : UInt8) (hy : y.toNat < 4) :
    (if c then ALWAYS_TRUE else if (d && y != ALWAYS_TRUE) = true then NOUB_IF_NOINBOUNDS else y).toNat < 4 := by
  rcases u8_cases4 y hy with rfl | rfl | rfl | rfl <;> cases c <;> cases d <;> decide

theorem ite_valid (c : Bool) (y : UInt8) {k : Nat} (_hk : 1 ≤ k) (hy : y.toNat < 2 ^ k) :
    (if c then ALWAYS_TRUE else y).toNat < 2 ^ k := by
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  cases c
  · exact hy
  · show 0 < 2 ^ k; omega

theorem overrideEffectsStrengthens_proven : OverrideEffectsStrengthens := by
  intro e eo hv
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨ite_fieldLe _ _, ite_fieldLe _ _, fieldLe_refl _, ite_boolLe _ _, ite_boolLe _ _,
      ite_boolLe _ _, ite_fieldLe _ _, noub_fieldLe _ _ _ h5, fieldLe_refl _, ite_boolLe _ _⟩
  · refine ⟨ite_valid _ _ (k := 3) (by decide) h1, ite_valid _ _ (k := 2) (by decide) h2, h3,
      ite_valid _ _ (k := 2) (by decide) h4, ?_, h6⟩
    exact noub_valid _ _ _ h5

/-- `adjust_effects(ipo_effects, def::Method)` never weakens a valid `Effects`. -/
def AdjustEffectsStrengthens : Prop :=
  ∀ (e : Effects) (purity : UInt16), Valid e → EffLe (adjustEffectsMethod e purity) e

/-- A method whose purity has the `consistent_overlay` bit gets `nonoverlayed =
CONSISTENT_OVERLAY` even when inference found `ALWAYS_TRUE` (Compiler/src/typeinfer.jl:659-661). -/
theorem adjustEffectsStrengthens_refuted : ¬ AdjustEffectsStrengthens := by
  intro h
  have := h EFFECTS_TOTAL 0x0200 (by decide)
  revert this; decide

theorem adjust_consistent_overlay_weakens :
    (adjustEffectsMethod EFFECTS_TOTAL 0x0200).nonoverlayed = CONSISTENT_OVERLAY ∧
    (decodeEffectsOverride 0x0200).consistent_overlay = true := by decide

/-- `adjust_effects(ipo_effects, def::Method)` written as one record: each field the method's
override names is set to its strongest state, `consistent_overlay` sets `nonoverlayed` to
`CONSISTENT_OVERLAY`, and `noub_if_noinbounds` gives `NOUB_IF_NOINBOUNDS` unless `noub` is
already `ALWAYS_TRUE`. -/
def adjustClosed (e : Effects) (o : EffectsOverride) : Effects :=
  ⟨if o.consistent then ALWAYS_TRUE else e.consistent,
   if o.effect_free then ALWAYS_TRUE else e.effect_free,
   e.reset_safe,
   if o.nothrow then true else e.nothrow,
   if o.terminates_globally then true else e.terminates,
   if o.notaskstate then true else e.notaskstate,
   if o.inaccessiblememonly then ALWAYS_TRUE else e.inaccessiblememonly,
   if o.noub then ALWAYS_TRUE
     else if (o.noub_if_noinbounds && e.noub != ALWAYS_TRUE) = true then NOUB_IF_NOINBOUNDS
     else e.noub,
   if o.consistent_overlay then CONSISTENT_OVERLAY else e.nonoverlayed,
   if o.nortcall then true else e.nortcall⟩

theorem adjust_closed (e : Effects) (p : UInt16) :
    adjustEffectsMethod e p = adjustClosed e (decodeEffectsOverride p) := by
  unfold adjustEffectsMethod
  generalize decodeEffectsOverride p = o
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := o
  cases a8 <;> cases a9
  all_goals
    cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a6 <;> cases a7 <;> cases a10 <;> cases a11
  all_goals first
    | rfl
    | (by_cases h : (e.noub != ALWAYS_TRUE) = true <;> simp [h, adjustClosed, Effects.kw] <;> rfl)

theorem overlay_fieldLe (c : Bool) (y : UInt8) (hy : y.toNat < 4) (h0 : y ≠ ALWAYS_TRUE) :
    FieldLe (if c then CONSISTENT_OVERLAY else y) y := by
  rcases u8_cases4 y hy with rfl | rfl | rfl | rfl <;> cases c <;> first | decide | exact absurd rfl h0

theorem overlay_valid (c : Bool) (y : UInt8) (hy : y.toNat < 4) :
    (if c then CONSISTENT_OVERLAY else y).toNat < 4 := by
  cases c
  · exact hy
  · show CONSISTENT_OVERLAY.toNat < 4; decide

/-- `adjust_effects(ipo_effects, def::Method)` is the record `adjustClosed` (each named field set
to its strongest state), keeps a valid `Effects` valid, and never weakens it when inference has
not found `nonoverlayed` to be `ALWAYS_TRUE`. -/
def AdjustEffectsSpec : Prop :=
  ∀ (e : Effects) (purity : UInt16), Valid e →
    adjustEffectsMethod e purity = adjustClosed e (decodeEffectsOverride purity) ∧
    Valid (adjustEffectsMethod e purity) ∧
    (e.nonoverlayed ≠ ALWAYS_TRUE → EffLe (adjustEffectsMethod e purity) e)

theorem adjustEffectsSpec_proven : AdjustEffectsSpec := by
  intro e p hv
  rw [adjust_closed]
  generalize decodeEffectsOverride p = o
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨ite_valid _ _ (k := 3) (by decide) h1, ite_valid _ _ (k := 2) (by decide) h2, h3,
      ite_valid _ _ (k := 2) (by decide) h4, noub_valid _ _ _ h5, overlay_valid _ _ h6⟩
  · intro h0
    exact ⟨ite_fieldLe _ _, ite_fieldLe _ _, fieldLe_refl _, ite_boolLe _ _, ite_boolLe _ _,
      ite_boolLe _ _, ite_fieldLe _ _, noub_fieldLe _ _ _ h5, overlay_fieldLe _ _ h6 h0, ite_boolLe _ _⟩

/-! ## The C readers of `ipo_purity_bits` -/

theorem u8_beq0 (x : UInt32) (h : x.toNat < 256) : (x.toUInt8 == 0) = (x == 0) := by
  by_cases hx : x = 0
  · subst hx; rfl
  · have : x.toUInt8 ≠ 0 := fun e => hx ((UInt32.toNat_inj (a := x) (b := 0)).mp (by
      have := congrArg UInt8.toNat e
      rw [u8fld x h] at this
      exact this))
    rw [beq_false_of_ne hx, beq_false_of_ne this]

theorem and_lt (w _k : UInt32) (m : UInt32) (hm : m.toNat < 256) : ((w >>> _k) &&& m).toNat < 256 := by
  rw [UInt32.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right hm

/-- What the two C readers of `ipo_purity_bits` read, for every word: `effects_foldable`
(src/staticdata.c:645-652) is `is_consistent && is_noub && is_effect_free && is_terminates` of
`decode_effects(w)`, and `effects_ipo_reset_safe` (src/codegen.cpp:2516-2525) is `w != 0 &&
is_effect_free && is_reset_safe` of it. With the encoding's round trip, on a valid `Effects` `e`
with a nonzero word the reset-safe reader agrees with Julia's `is_effect_free(e) &&
is_reset_safe(e)`. -/
def CReadersDecode : Prop :=
  (∀ w : UInt32, effectsFoldableC w =
    (isConsistent (decodeEffects w) && isNoub (decodeEffects w) && isEffectFree (decodeEffects w) &&
      isTerminates (decodeEffects w))) ∧
  (∀ w : UInt32, effectsIpoResetSafeC w =
    (w != 0 && isEffectFree (decodeEffects w) && isResetSafe (decodeEffects w))) ∧
  (∀ e : Effects, Valid e → encodeEffects e ≠ 0 →
    effectsIpoResetSafeC (encodeEffects e) = (isEffectFree e && isResetSafe e))

theorem cReadersDecode_proven : CReadersDecode := by
  have hf : ∀ w : UInt32, effectsFoldableC w =
      (isConsistent (decodeEffects w) && isNoub (decodeEffects w) && isEffectFree (decodeEffects w) &&
        isTerminates (decodeEffects w)) := by
    intro w
    simp only [effectsFoldableC, isConsistent, isNoub, isEffectFree, isTerminates, decodeEffects,
      ALWAYS_TRUE]
    rw [u8_beq0 _ (and_lt _ _ _ (by decide)), u8_beq0 _ (and_lt _ _ _ (by decide)),
      u8_beq0 _ (and_lt _ _ _ (by decide)), UInt32.shiftRight_zero]
  have hr : ∀ w : UInt32, effectsIpoResetSafeC w =
      (w != 0 && isEffectFree (decodeEffects w) && isResetSafe (decodeEffects w)) := by
    intro w
    simp only [effectsIpoResetSafeC, isEffectFree, isResetSafe, decodeEffects, ALWAYS_TRUE]
    rw [u8_beq0 _ (and_lt _ _ _ (by decide)), u8_beq0 _ (and_lt _ _ _ (by decide))]
  refine ⟨hf, hr, ?_⟩
  intro e hv hz
  rw [hr, decode_encode_valid e hv]
  have h0 : (encodeEffects e != 0) = true := bne_iff_ne.mpr hz
  rw [h0, Bool.true_and]

/-- `effects_foldable` is "kept in sync with `Core.Compiler.is_foldable(effects, true)`"
(its comment, src/staticdata.c:647): for every valid `Effects` `e`,
`effects_foldable(encode_effects(e)) == is_foldable(e, true)`. -/
def CFoldableSync : Prop :=
  ∀ e : Effects, Valid e → effectsFoldableC (encodeEffects e) = isFoldable e true

/-- `NOUB_IF_NOINBOUNDS` is foldable for `is_foldable` but not for `effects_foldable`; and
`effects_foldable` does not read `nortcall`. -/
theorem cFoldableSync_refuted : ¬ CFoldableSync := by
  intro h
  have := h (withNU NOUB_IF_NOINBOUNDS) (by decide)
  revert this; decide

theorem cFoldable_nortcall_counterexample :
    effectsFoldableC (encodeEffects (Effects.kw EFFECTS_TOTAL (nortcall := false))) = true ∧
    isFoldable (Effects.kw EFFECTS_TOTAL (nortcall := false)) true = false := by decide

/-- `effects_ipo_reset_safe` treats the word `0` as "no recorded effects", but `0` is also
`encode_effects` of a real `Effects` (nothing proven but the `UInt8` fields), which is effect-free
and reset-safe. -/
theorem cResetSafe_zero_word :
    encodeEffects ⟨0, 0, 0, false, false, false, 0, 0, 0, false⟩ = 0 ∧
    effectsIpoResetSafeC 0 = false ∧
    isEffectFree ⟨0, 0, 0, false, false, false, 0, 0, 0, false⟩ = true ∧
    isResetSafe ⟨0, 0, 0, false, false, false, 0, 0, 0, false⟩ = true := by decide

/-! ## The keyword constructor -/

/-- `Effects(effects; kwargs...)` copies `effects` and replaces exactly the named fields. -/
def EffectsKwSpec : Prop :=
  (∀ e : Effects, Effects.kw e = e) ∧
  (∀ (e : Effects) c ef rs nt te ns im nu no rc,
    Effects.kw e c ef rs nt te ns im nu no rc = ⟨c, ef, rs, nt, te, ns, im, nu, no, rc⟩)

theorem effectsKwSpec_proven : EffectsKwSpec :=
  ⟨fun _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ => rfl⟩

/-- Registry entries of `Compiler/src/effects.jl`. -/
def entries : List Entry := [
  { id := "compiler-effects-encode-roundtrip", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["encode_effects(e::Effects)", "decode_effects(e::UInt32)"],
    statement := "decode_effects(encode_effects(e)) == e for every Effects whose fields fit their slots (3 bits for consistent, 2 for the other UInt8 fields), the encoding uses only the low 17 bits, decode_effects always returns such an Effects, and encode_effects(decode_effects(w)) == w & 0x1ffff. No two fields share a bit and none is cut when ipo_purity_bits is cached and reloaded.",
    source := "comment Compiler/src/effects.jl:371 (sync with codegen.cpp and staticdata.c); invariant: CodeInstance.ipo_purity_bits stores the effects (Compiler/src/typeinfer.jl:1187)",
    status := .proven, prop := ``EncodeDecodeEffects, thm := some ``encodeDecodeEffects_proven,
    notes := "Every Effects inference builds fits: see compiler-effects-constants-valid and the validity parts of the merge, override and adjust entries." },
  { id := "compiler-effects-constants-valid", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["EFFECTS_TOTAL", "EFFECTS_THROWS", "EFFECTS_UNKNOWN", "EFFECTS_MINIMAL", "ALWAYS_TRUE", "ALWAYS_FALSE", "CONSISTENT_IF_NOTRETURNED", "CONSISTENT_IF_INACCESSIBLEMEMONLY", "EFFECT_FREE_IF_INACCESSIBLEMEMONLY", "EFFECT_FREE_GLOBALLY", "INACCESSIBLEMEM_OR_ARGMEMONLY", "NOUB_IF_NOINBOUNDS", "CONSISTENT_OVERLAY", "RESET_SAFE_IF_INACCESSIBLEMEMONLY"],
    statement := "Every state constant fits the slot encode_effects gives its field, and the four EFFECTS_* constants are valid call-level Effects.",
    source := "invariant (Compiler/src/effects.jl:168-200 with the slot widths of encode_effects, effects.jl:371-383)",
    status := .proven, prop := ``ConstantsValid, thm := some ``constantsValid_proven },
  { id := "compiler-effects-merge-effectbits", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["merge_effectbits(old::UInt8, new::UInt8)", "merge_effectbits(old::Bool, new::Bool)"],
    statement := "On every byte merge_effectbits is commutative, associative and idempotent; merge_effectbits(x, y) == y exactly when x is at least as strong as y in the documented order (y is ALWAYS_FALSE, or x is not and x's bits are bits of y); in that order it is the least upper bound and monotone in both arguments. The Bool method is commutative, associative and idempotent, and merge_effectbits(a, b) is true exactly when both a and b are true (a property such as nothrow survives the merge only if both sides have it).",
    source := "docstring Compiler/src/effects.jl:121-127 (statement effects are merged into one global Effects, each property moving from ALWAYS_TRUE towards ALWAYS_FALSE)",
    status := .proven, prop := ``MergeEffectbitsLaws, thm := some ``mergeEffectbitsLaws_proven },
  { id := "compiler-effects-merge-effects", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["merge_effects(old::Effects, new::Effects)"],
    statement := "merge_effects is commutative, associative and idempotent (so a method's merged effects do not depend on the order statements are visited), is the least upper bound in the fieldwise order and monotone in both arguments, and keeps every field within its encoded width.",
    source := "docstring Compiler/src/effects.jl:121-127",
    status := .proven, prop := ``MergeEffectsLaws, thm := some ``mergeEffectsLaws_proven },
  { id := "compiler-effects-queries-merge", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["is_consistent(effects::Effects)", "is_effect_free(effects::Effects)", "is_reset_safe(effects::Effects)", "is_nothrow(effects::Effects)", "is_terminates(effects::Effects)", "is_notaskstate(effects::Effects)", "is_inaccessiblememonly(effects::Effects)", "is_noub(effects::Effects)", "is_nonoverlayed(effects::Effects)", "is_nortcall(effects::Effects)", "is_foldable(effects::Effects, check_rtcall::Bool=false)", "is_foldable_nothrow(effects::Effects, check_rtcall::Bool=false)", "is_removable_if_unused(effects::Effects)", "is_finalizer_inlineable(effects::Effects)"],
    statement := "Each full-strength query, and is_foldable (either check_rtcall), is_foldable_nothrow, is_removable_if_unused and is_finalizer_inlineable, holds of merge_effects(a, b) exactly when it holds of both a and b, for all Effects including out-of-range bytes; and each query reads exactly the field test of its source line.",
    source := "invariant: the queries summarise the fields that merge_effects combines (Compiler/src/effects.jl:326-358)",
    status := .proven, prop := ``QueriesMerge, thm := some ``queriesMerge_proven },
  { id := "compiler-effects-queries-named-states", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["is_consistent(effects::Effects)", "is_effect_free(effects::Effects)", "is_reset_safe(effects::Effects)", "is_inaccessiblememonly(effects::Effects)", "is_noub(effects::Effects)", "is_noub_if_noinbounds(effects::Effects)", "is_nonoverlayed(effects::Effects)", "is_consistent_if_notreturned(effects::Effects)", "is_consistent_if_inaccessiblememonly(effects::Effects)", "is_reset_safe_if_inaccessiblememonly(effects::Effects)", "is_inaccessiblemem_or_argmemonly(effects::Effects)", "is_consistent_overlay(effects::Effects)"],
    statement := "On the named states of each field, each query is true exactly at the state it names: full-strength queries at ALWAYS_TRUE only, each conditional query at its conditional state (for consistent, at that condition alone or with the other one); and each query reads exactly the field test of its source line.",
    source := "docstring Compiler/src/effects.jl:44-127 and the show key effects.jl:1-42",
    status := .proven, prop := ``QueriesNamedStates, thm := some ``queriesNamedStates_proven },
  { id := "compiler-effects-effect-free-globally-collision", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["is_effect_free_if_inaccessiblememonly(effects::Effects)", "merge_effectbits(old::UInt8, new::UInt8)"],
    statement := "is_effect_free_if_inaccessiblememonly is true exactly at EFFECT_FREE_IF_INACCESSIBLEMEMONLY among the named effect_free states.",
    source := "docstrings Compiler/src/effects.jl:62-63 and 178-182 (EFFECT_FREE_GLOBALLY is effect-free for callers, not a conditional state)",
    status := .refuted, prop := ``EffectFreeIfIamoNamedStates, thm := some ``effectFreeIfIamoNamedStates_refuted,
    issue := "none found (queries: EFFECT_FREE_GLOBALLY; EFFECT_FREE_GLOBALLY EFIIMO; gc_preserve_begin effect_free; EFFECT_FREE_GLOBALLY merge; issues and prs)",
    notes := "EFFECT_FREE_GLOBALLY is 0x03 = ALWAYS_FALSE | EFFECT_FREE_IF_INACCESSIBLEMEMONLY, so the query reads it as conditional and GC.@preserve begin/end statements get IR_FLAG_EFIIMO; also merge_effectbits(GLOBALLY, IF_INACCESSIBLEMEMONLY) == GLOBALLY drops the condition (globally_merge_drops_condition). No wrong code shown: the flag is only used together with IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM, which these statements lack. Same on nightly 290d5bb5f5." },
  { id := "compiler-effects-is-better-order", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["is_better_effects(new::Effects, old::Effects)"],
    statement := "On call-level states, is_better_effects(new, old) holds exactly when new differs from old and is at least as strong in every field (merge_effects(new, old) == old).",
    source := "invariant: the name, and its use at Compiler/src/abstractinterpretation.jl:233 to keep const-prop effects that are better than the regular ones",
    status := .refuted, prop := ``IsBetterEffectsOrder, thm := some ``isBetterEffectsOrder_refuted,
    issue := "none found (queries: is_better_effects; is_better_effects consistent; is_better_effects CONSISTENT_IF_NOTRETURNED; constprop effects better; issues and prs)",
    notes := "consistent = CONSISTENT_IF_NOTRETURNED and CONSISTENT_IF_INACCESSIBLEMEMONLY are each called better than the other; the union of both is called better than CONSISTENT_IF_INACCESSIBLEMEMONLY although it is weaker; CONSISTENT_IF_NOTRETURNED is not called better than the union although it is stronger (isBetterEffects_more_counterexamples). Every other field follows the order on these states (smoke test, 2M random pairs). Same on nightly 290d5bb5f5 and 1.13.3." },
  { id := "compiler-effects-override-storage", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["decode_statement_effects_override(ssaflag::UInt32)", "encode_effects_override(eo::EffectsOverride)", "decode_effects_override(e::UInt16)"],
    statement := "An EffectsOverride survives every place it is stored: decode_effects_override(encode_effects_override(eo)) == eo; the Method.purity bits that src/method.c builds from form_purity_expr(eo) decode to eo; and the statement flag it builds inside an @assume_effects region decodes to eo with decode_statement_effects_override, whatever the three IR flag bits below it.",
    source := "invariant: the override is written by base/expr.jl and src/method.c and read back by the compiler (Compiler/src/typeinfer.jl:635, effects.jl:399-400)",
    status := .proven, prop := ``OverrideStorage, thm := some ``overrideStorage_proven,
    notes := "The C side assumes bitfields are allocated from the least significant bit (GCC/Clang ABIs), as the model of _jl_purity_overrides_t does. Proven by kernel evaluation over all 2^11 overrides and 2^3 low flag values." },
  { id := "compiler-effects-override-effects", juliaFile := "Compiler/src/abstractinterpretation.jl",
    juliaFns := ["override_effects(effects::Effects, override::EffectsOverride)"],
    statement := "override_effects sets each field the override names to its strongest state (noub_if_noinbounds gives NOUB_IF_NOINBOUNDS unless noub is already ALWAYS_TRUE), leaves reset_safe, nonoverlayed and every unnamed field unchanged, and so never weakens a valid Effects and keeps it valid.",
    source := "docstring base/expr.jl (Base.@assume_effects: the settings assert properties, they do not remove them)",
    status := .proven, prop := ``OverrideEffectsStrengthens, thm := some ``overrideEffectsStrengthens_proven },
  { id := "compiler-effects-adjust-spec", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["adjust_effects(ipo_effects::Effects, def::Method)"],
    statement := "adjust_effects(ipo_effects, def) sets each field def.purity names to its strongest state (consistent_overlay sets nonoverlayed to CONSISTENT_OVERLAY), keeps a valid Effects valid, and never weakens it when nonoverlayed is not ALWAYS_TRUE.",
    source := "comment Compiler/src/typeinfer.jl:634 (override the analyzed effects using manually annotated effect settings)",
    status := .proven, prop := ``AdjustEffectsSpec, thm := some ``adjustEffectsSpec_proven },
  { id := "compiler-effects-adjust-consistent-overlay", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["adjust_effects(ipo_effects::Effects, def::Method)"],
    statement := "adjust_effects(ipo_effects, def) never weakens a valid Effects.",
    source := "comment Compiler/src/typeinfer.jl:634 and the @assume_effects docstring (annotations only assert properties)",
    status := .refuted, prop := ``AdjustEffectsStrengthens, thm := some ``adjustEffectsStrengthens_refuted,
    issue := "none found; related #64715 (overrides lost across inference cycles) (queries: consistent_overlay; consistent_overlay adjust_effects; consistent_overlay nonoverlayed weaken; issues and prs)",
    notes := "A method with the consistent_overlay purity bit gets nonoverlayed = CONSISTENT_OVERLAY even when inference found ALWAYS_TRUE. Reachable only through a hand-written Expr(:purity) on a method that is not an overlay: @consistent_overlay always defines an overlay, whose inference already starts at CONSISTENT_OVERLAY (inferencestate.jl:420-423), and @assume_effects has no consistent_overlay setting. Same on nightly 290d5bb5f5." },
  { id := "compiler-effects-c-readers", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["encode_effects(e::Effects)", "decode_effects(e::UInt32)"],
    statement := "For every word, effects_foldable (src/staticdata.c) reads is_consistent && is_noub && is_effect_free && is_terminates of decode_effects(w), and effects_ipo_reset_safe (src/codegen.cpp) reads w != 0 && is_effect_free && is_reset_safe of it; so on a valid Effects with a nonzero word the reset-safe reader agrees with Julia.",
    source := "comments Compiler/src/effects.jl:371, src/staticdata.c:647, src/codegen.cpp:2516-2520 (kept in sync with encode_effects)",
    status := .proven, prop := ``CReadersDecode, thm := some ``cReadersDecode_proven,
    notes := "The C functions are static, so this is checked against the model only. The word 0 is also the encoding of a real Effects that is effect-free and reset-safe (cResetSafe_zero_word); codegen treats it as unknown, which is conservative." },
  { id := "compiler-effects-c-foldable-sync", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["encode_effects(e::Effects)", "is_foldable(effects::Effects, check_rtcall::Bool=false)"],
    statement := "effects_foldable(encode_effects(e)) == is_foldable(e, true) for every valid Effects e.",
    source := "comment src/staticdata.c:647 (N.B.: This needs to be kept in sync with Core.Compiler.is_foldable(effects, true))",
    status := .refuted, prop := ``CFoldableSync, thm := some ``cFoldableSync_refuted,
    issue := "none found (queries: effects_foldable; effects_foldable staticdata noub; effects_foldable is_foldable sync; staticdata discard inferred foldable; noub irinterp discard; noub_if_noinbounds pkgimage inferred; issues and prs)",
    notes := "effects_foldable requires noub == ALWAYS_TRUE where is_foldable also accepts NOUB_IF_NOINBOUNDS, and it ignores nortcall (cFoldable_nortcall_counterexample). The repro shows a package image dropping the non-inlineable inferred code of a foldable NOUB_IF_NOINBOUNDS method. Same on nightly 290d5bb5f5; on 1.13.3 the repro does not reproduce because both methods lose their code there." },
  { id := "compiler-effects-kw-ctor", juliaFile := "Compiler/src/effects.jl",
    juliaFns := ["Effects(effects::Effects=EFFECTS_MINIMAL; kwargs...)"],
    statement := "Effects(effects; kwargs...) copies effects and replaces exactly the named fields; with no keywords it returns effects unchanged.",
    source := "invariant (keyword defaults are the fields of effects, Compiler/src/effects.jl:202-224)",
    status := .proven, prop := ``EffectsKwSpec, thm := some ``effectsKwSpec_proven }
]

end JuliaLean.Proofs.Compiler.src.effects
