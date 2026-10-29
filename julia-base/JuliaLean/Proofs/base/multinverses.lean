import JuliaLean.base.multinverses
import JuliaLean.Proofs.base.int
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.multinverses

open JuliaLean JuliaLean.base.multinverses JuliaLean.Registry
open JuliaLean.Proofs.base.int

/-- The ordinary fixed-width `rem` callee used inside the magic constructors. -/
def BaseRemLaw (remFn : SameTypeRem) : Prop :=
  ∀ {t : IntTy} (a b : JInt t), remFn a b = JInt.remInt a b

/-- The ordinary fixed-width `divrem` callee used inside the magic constructors. -/
def BaseDivremLaw (divremFn : SameTypeDivrem) : Prop :=
  ∀ {t : IntTy} (a b : JInt t), divremFn a b = do
    let q ← JInt.div a b
    let r ← JInt.remInt a b
    pure (q, r)

/-- `unsigned(::Type)` maps fixed-width signed types to same-width unsigned types. -/
def UnsignedTypeSpecification : Prop :=
  unsignedTypeBool = .u64 ∧
  unsignedTypeInt8 = IntTy.toUnsigned .i8 ∧
  unsignedTypeInt16 = IntTy.toUnsigned .i16 ∧
  unsignedTypeInt32 = IntTy.toUnsigned .i32 ∧
  unsignedTypeInt64 = IntTy.toUnsigned .i64 ∧
  unsignedTypeInt128 = IntTy.toUnsigned .i128 ∧
  (∀ t : IntTy, ∀ h : t.signed = false,
    unsignedTypeUnsigned t h = IntTy.toUnsigned t) ∧
  (∀ {types : List Type} (slurp : JuliaTuple types),
    unsignedTypeBottom slurp =
      .error ⟨"unsigned", .cons JuliaLean.base.int.UnionBottom.type slurp⟩)

/-- Zero divisors raise `ArgumentError` through each public constructor entry point. -/
def ZeroDivisorsRejected : Prop :=
  ∀ (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (t : IntTy),
    (∀ (h : t.signed = true),
      signedInverseConstructor h remFn divremFn (JInt.lit t 0) =
        .error (.argumentError "cannot compute magic for d == 0") ∧
      signedMultiplicativeInverse h remFn divremFn (JInt.lit t 0) =
        .error (.argumentError "cannot compute magic for d == 0") ∧
      multiplicativeinverseSigned h remFn divremFn (JInt.lit t 0) =
        .error (.argumentError "cannot compute magic for d == 0")) ∧
    (∀ (h : t.signed = false),
      unsignedInverseConstructor h remFn divremFn (JInt.lit t 0) =
        .error (.argumentError "cannot compute magic for d == 0") ∧
      unsignedMultiplicativeInverse h remFn divremFn (JInt.lit t 0) =
        .error (.argumentError "cannot compute magic for d == 0") ∧
      multiplicativeinverseUnsigned h remFn divremFn (JInt.lit t 0) =
        .error (.argumentError "cannot compute magic for d == 0"))

/-- Every signed width's precomputed inverse gives the direct quotient for every dividend. -/
def SignedInverseDivision : Prop :=
  ∀ (remFn : SameTypeRem) (divremFn : SameTypeDivrem),
    BaseRemLaw remFn → BaseDivremLaw divremFn →
    ∀ t : IntTy, ∀ (h : t.signed = true), ∀ (d : JInt t), d.val ≠ 0 →
      ∃ inverse : SignedMultiplicativeInverse t,
        signedInverseConstructor h remFn divremFn d = .ok inverse ∧
        inverse.divisor = d ∧
        ∀ a : JInt t,
          (.ok (divSignedInverse a inverse) : Jl (JInt t)) = JInt.div a d

/-- Every unsigned width's precomputed inverse gives the direct quotient for every dividend. -/
def UnsignedInverseDivision : Prop :=
  ∀ (remFn : SameTypeRem) (divremFn : SameTypeDivrem),
    BaseRemLaw remFn → BaseDivremLaw divremFn →
    ∀ t : IntTy, ∀ (h : t.signed = false), ∀ (d : JInt t), d.val ≠ 0 →
      ∃ inverse : UnsignedMultiplicativeInverse t,
        unsignedInverseConstructor h remFn divremFn d = .ok inverse ∧
        inverse.divisor = d ∧
        ∀ a : JInt t,
          (.ok (divUnsignedInverse a inverse) : Jl (JInt t)) = JInt.div a d

/-- The inverse remainder and modulus agree with fixed-width integer remainder and modulus. -/
def InverseRemainderAndModulus : Prop :=
  ∀ (remFn : SameTypeRem) (divremFn : SameTypeDivrem),
    BaseRemLaw remFn → BaseDivremLaw divremFn →
    (∀ t : IntTy, ∀ (h : t.signed = true), ∀ (d : JInt t), d.val ≠ 0 →
      ∃ inverse : SignedMultiplicativeInverse t,
        signedInverseConstructor h remFn divremFn d = .ok inverse ∧
        inverse.divisor = d ∧
        ∀ a : JInt t,
          (.ok (rem a (.signed inverse)) : Jl (JInt t)) = JInt.remInt a d ∧
          (.ok (modSignedInverse a inverse) : Jl (JInt t)) = JInt.mod a d) ∧
    (∀ t : IntTy, ∀ (h : t.signed = false), ∀ (d : JInt t), d.val ≠ 0 →
      ∃ inverse : UnsignedMultiplicativeInverse t,
        unsignedInverseConstructor h remFn divremFn d = .ok inverse ∧
        inverse.divisor = d ∧
        ∀ a : JInt t,
          (.ok (rem a (.unsigned inverse)) : Jl (JInt t)) = JInt.remInt a d ∧
          (.ok (modUnsignedInverse a inverse) : Jl (JInt t)) = JInt.mod a d)

/-- The inverse `divrem` method agrees with ordinary `divrem`, including `DivideError`. -/
def InverseDivremMatchesBase : Prop :=
  ∀ (remFn : SameTypeRem) (divremFn : SameTypeDivrem),
    BaseRemLaw remFn → BaseDivremLaw divremFn →
    (∀ t : IntTy, ∀ (h : t.signed = true), ∀ (d : JInt t), d.val ≠ 0 →
      ∃ inverse : SignedMultiplicativeInverse t,
        signedInverseConstructor h remFn divremFn d = .ok inverse ∧
        ∀ a : JInt t,
          (.ok (divremInverse a (.signed inverse)) : Jl (JInt t × JInt t)) = divremFn a d) ∧
    (∀ t : IntTy, ∀ (h : t.signed = false), ∀ (d : JInt t), d.val ≠ 0 →
      ∃ inverse : UnsignedMultiplicativeInverse t,
        unsignedInverseConstructor h remFn divremFn d = .ok inverse ∧
        ∀ a : JInt t,
          (.ok (divremInverse a (.unsigned inverse)) : Jl (JInt t × JInt t)) = divremFn a d)

/-- The convenience constructor preserves its divisor for both signednesses. -/
def MultiplicativeInverseDispatchPreservesDivisor : Prop :=
  ∀ (remFn : SameTypeRem) (divremFn : SameTypeDivrem),
    BaseRemLaw remFn → BaseDivremLaw divremFn →
    (∀ t : IntTy, ∀ (h : t.signed = true), ∀ (d : JInt t), d.val ≠ 0 →
      (multiplicativeinverseSigned h remFn divremFn d).map
        (fun inverse => inverse.divisor) = .ok d) ∧
    (∀ t : IntTy, ∀ (h : t.signed = false), ∀ (d : JInt t), d.val ≠ 0 →
      (multiplicativeinverseUnsigned h remFn divremFn d).map
        (fun inverse => inverse.divisor) = .ok d)

/-- Both signed convenience constructors preserve direct division and remainder behavior. -/
def SignedPublicAPIBehavior : Prop :=
  ∀ (remFn : SameTypeRem) (divremFn : SameTypeDivrem),
    BaseRemLaw remFn → BaseDivremLaw divremFn →
    ∀ t : IntTy, ∀ (h : t.signed = true), ∀ (d : JInt t), d.val ≠ 0 →
      (∃ inverse : SignedMultiplicativeInverse t,
        signedMultiplicativeInverse h remFn divremFn d = .ok inverse ∧
        inverse.divisor = d ∧
        ∀ a : JInt t,
          (.ok (divSignedInverse a inverse) : Jl (JInt t)) = JInt.div a d ∧
          (.ok (rem a (.signed inverse)) : Jl (JInt t)) = JInt.remInt a d) ∧
      (∃ inverse : SignedMultiplicativeInverse t,
        multiplicativeinverseSigned h remFn divremFn d = .ok inverse ∧
        inverse.divisor = d ∧
        ∀ a : JInt t,
          (.ok (divSignedInverse a inverse) : Jl (JInt t)) = JInt.div a d ∧
          (.ok (rem a (.signed inverse)) : Jl (JInt t)) = JInt.remInt a d)

/-- Both unsigned convenience constructors preserve direct division and remainder behavior. -/
def UnsignedPublicAPIBehavior : Prop :=
  ∀ (remFn : SameTypeRem) (divremFn : SameTypeDivrem),
    BaseRemLaw remFn → BaseDivremLaw divremFn →
    ∀ t : IntTy, ∀ (h : t.signed = false), ∀ (d : JInt t), d.val ≠ 0 →
      (∃ inverse : UnsignedMultiplicativeInverse t,
        unsignedMultiplicativeInverse h remFn divremFn d = .ok inverse ∧
        inverse.divisor = d ∧
        ∀ a : JInt t,
          (.ok (divUnsignedInverse a inverse) : Jl (JInt t)) = JInt.div a d ∧
          (.ok (rem a (.unsigned inverse)) : Jl (JInt t)) = JInt.remInt a d) ∧
      (∃ inverse : UnsignedMultiplicativeInverse t,
        multiplicativeinverseUnsigned h remFn divremFn d = .ok inverse ∧
        inverse.divisor = d ∧
        ∀ a : JInt t,
          (.ok (divUnsignedInverse a inverse) : Jl (JInt t)) = JInt.div a d ∧
          (.ok (rem a (.unsigned inverse)) : Jl (JInt t)) = JInt.remInt a d)

/-- The public inverse APIs preserve results and reject invalid input. -/
def MultiplicativeInversePublicAPI : Prop :=
  ZeroDivisorsRejected ∧
  SignedPublicAPIBehavior ∧
  UnsignedPublicAPIBehavior ∧
  UnsignedTypeSpecification

/-- The unsigned inverse specification includes division and remainder behavior. -/
def UnsignedMultiplicativeInverseCorrect : Prop :=
  UnsignedInverseDivision ∧ InverseRemainderAndModulus

/-- The signed inverse specification includes the matching `divrem` result. -/
def SignedInverseDivisionAndDivrem : Prop :=
  SignedInverseDivision ∧ InverseDivremMatchesBase

/--
All fixed-width constructors, conversion methods, and inverse arithmetic preserve their integer
contracts for every signedness, width, divisor, and dividend.
-/
def MultiplicativeInverseSourceBehavior : Prop :=
  MultiplicativeInversePublicAPI ∧
  SignedInverseDivision ∧
  UnsignedInverseDivision ∧
  InverseRemainderAndModulus ∧
  InverseDivremMatchesBase ∧
  MultiplicativeInverseDispatchPreservesDivisor

theorem mulHi_val {t : IntTy} (a b : JInt t) :
    (mulHi a b).val = (a.val * b.val) / 2 ^ t.bits := by
  cases t
  all_goals unfold mulHi
  case i128 => exact JuliaLean.Proofs.base.int.mulHiI128_val a b
  case u128 => exact JuliaLean.Proofs.base.int.mulHiU128_val a b
  all_goals
    apply JuliaLean.Proofs.base.int.mulHiExact_proven _ _ rfl
    intro x
    rw [JuliaLean.Proofs.base.int.widenTo_val]
    apply wrapInt_of_inRange
    have hx := x.property
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx ⊢
    omega

theorem remainder_of_wrapped_quotient {t : IntTy} (a d q : JInt t)
    (hq : q.val = wrapInt t (a.val.tdiv d.val)) :
    JuliaLean.base.int.subWrap a (JuliaLean.base.int.mulWrap q d) =
      JInt.wrap t (a.val.tmod d.val) := by
  apply JuliaLean.Proofs.base.int.jint_eq
  rw [JuliaLean.Proofs.base.int.subWrapWraps_proven,
    JuliaLean.Proofs.base.int.mulWrapWraps_proven, hq,
    JuliaLean.Proofs.base.int.wrapInt_mul_left,
    JuliaLean.Proofs.base.int.wrapInt_sub_right]
  have h := Int.tmod_add_mul_tdiv a.val d.val
  have heq : a.val - a.val.tdiv d.val * d.val = a.val.tmod d.val := by
    rw [Int.mul_comm] at h
    omega
  exact congrArg (wrapInt t) heq

theorem inverse_remainder_of_wrapped_quotient {t : IntTy} (a : JInt t)
    (b : MultiplicativeInverse t)
    (hq : (divInverse a b).val = wrapInt t (a.val.tdiv
      (match b with | .signed inverse => inverse.divisor | .unsigned inverse => inverse.divisor).val)) :
    rem a b = JInt.wrap t (a.val.tmod
      (match b with | .signed inverse => inverse.divisor | .unsigned inverse => inverse.divisor).val) := by
  exact remainder_of_wrapped_quotient a _ _ hq

theorem inverse_remainder_matches_base {t : IntTy} (a : JInt t)
    (b : MultiplicativeInverse t)
    (hd : (match b with | .signed inverse => inverse.divisor | .unsigned inverse => inverse.divisor).val ≠ 0)
    (hq : (divInverse a b).val = wrapInt t (a.val.tdiv
      (match b with | .signed inverse => inverse.divisor | .unsigned inverse => inverse.divisor).val)) :
    (.ok (rem a b) : Jl (JInt t)) = JInt.remInt a
      (match b with | .signed inverse => inverse.divisor | .unsigned inverse => inverse.divisor) := by
  rw [inverse_remainder_of_wrapped_quotient a b hq]
  cases b <;> simp_all [JInt.remInt]

theorem unsigned_remainder_modulus_of_wrapped_quotient {t : IntTy}
    (a : JInt t) (b : UnsignedMultiplicativeInverse t) (hd : b.divisor.val ≠ 0)
    (hq : (divUnsignedInverse a b).val = wrapInt t (a.val.tdiv b.divisor.val)) :
    (.ok (rem a (.unsigned b)) : Jl (JInt t)) = JInt.remInt a b.divisor ∧
      (.ok (modUnsignedInverse a b) : Jl (JInt t)) = JInt.mod a b.divisor := by
  have hr := inverse_remainder_matches_base a (.unsigned b) hd hq
  refine ⟨hr, ?_⟩
  simpa only [modUnsignedInverse, JInt.mod, b.typeWitness, Bool.false_eq_true, if_false] using hr

theorem signed_mod_expansion {t : IntTy} (ht : t.signed = true)
    (a d : JInt t) (hd : d.val ≠ 0) (hd1 : d.val ≠ -1) :
    JInt.mod a d = .ok (a -
      (JInt.wrap t (a.val.tdiv d.val) - JInt.lit t
        (if ((a.val < 0 ∧ 0 ≤ d.val) ∨ (0 ≤ a.val ∧ d.val < 0)) ∧
          (JInt.wrap t (a.val.tdiv d.val) * d).val ≠ a.val then 1 else 0)) * d) := by
  have hdiv : JInt.div a d = .ok (JInt.wrap t (a.val.tdiv d.val)) := by
    simp only [JInt.div, hd, if_false]
    rw [if_neg (by rintro ⟨_, _, h⟩; exact hd1 h)]
  simp only [JInt.mod, ht, if_true, hd1, if_false, JInt.fld, hdiv]
  rfl

theorem signed_signbit_val {t : IntTy} (ht : t.signed = true) (a : JInt t) :
    JuliaLean.base.int.signbit a = decide (a.val < 0) := by
  simp only [JuliaLean.base.int.signbit, ht, if_true]
  exact (JuliaLean.Proofs.base.int.signPredicates_proven t a).1

theorem signed_remainder_modulus_of_wrapped_quotient {t : IntTy}
    (a : JInt t) (b : SignedMultiplicativeInverse t) (hd : b.divisor.val ≠ 0)
    (hq : (divSignedInverse a b).val = wrapInt t (a.val.tdiv b.divisor.val)) :
    (.ok (rem a (.signed b)) : Jl (JInt t)) = JInt.remInt a b.divisor ∧
      (.ok (modSignedInverse a b) : Jl (JInt t)) = JInt.mod a b.divisor := by
  have hr := inverse_remainder_of_wrapped_quotient a (.signed b) hq
  have hrval : (rem a (.signed b)).val = a.val.tmod b.divisor.val := by
    rw [hr]
    exact wrapInt_of_inRange _ _ (tmod_fits a b.divisor)
  refine ⟨inverse_remainder_matches_base a (.signed b) hd hq, ?_⟩
  unfold modSignedInverse
  dsimp only
  rw [signed_signbit_val b.typeWitness, signed_signbit_val b.typeWitness, hrval]
  by_cases hd1 : b.divisor.val = -1
  · have hzero : a.val.tmod b.divisor.val = 0 := by simp [hd1]
    rw [hzero, if_pos (Or.inl rfl)]
    simp only [JInt.mod, b.typeWitness, if_true, hd1]
    apply congrArg Except.ok
    apply Subtype.ext
    rw [hrval, hzero]
    cases t <;> rfl
  · rw [signed_mod_expansion b.typeWitness a b.divisor hd hd1]
    have hqd : (JInt.wrap t (a.val.tdiv b.divisor.val) * b.divisor).val =
        a.val - a.val.tmod b.divisor.val := by
      change wrapInt t (wrapInt t (a.val.tdiv b.divisor.val) * b.divisor.val) = _
      rw [wrapInt_mul_left]
      have h := Int.tmod_add_mul_tdiv a.val b.divisor.val
      rw [Int.mul_comm] at h
      rw [show a.val.tdiv b.divisor.val * b.divisor.val =
        a.val - a.val.tmod b.divisor.val by omega]
      apply wrapInt_of_inRange
      have ha := a.property
      have hb := tmod_between a.val b.divisor.val
      cases t <;> simp_all [fits, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    have hform (c : Int) :
        (a - (JInt.wrap t (a.val.tdiv b.divisor.val) - JInt.lit t c) * b.divisor).val =
          wrapInt t (a.val.tmod b.divisor.val + c * b.divisor.val) := by
      change wrapInt t (a.val - wrapInt t
        (wrapInt t (wrapInt t (a.val.tdiv b.divisor.val) - wrapInt t c) *
          b.divisor.val)) = _
      calc
        _ = wrapInt t (a.val -
            (a.val.tdiv b.divisor.val - c) * b.divisor.val) := by
          apply wrapInt_congr
          rw [Int.sub_emod a.val _, wrapInt_emod_self,
            Int.mul_emod (wrapInt t (wrapInt t (a.val.tdiv b.divisor.val) - wrapInt t c)) _,
            wrapInt_emod_self,
            Int.sub_emod (wrapInt t (a.val.tdiv b.divisor.val)) (wrapInt t c),
            wrapInt_emod_self, wrapInt_emod_self,
            ← Int.sub_emod (a.val.tdiv b.divisor.val) c,
            ← Int.mul_emod (a.val.tdiv b.divisor.val - c) b.divisor.val,
            ← Int.sub_emod]
        _ = _ := by
          congr 1
          have h := Int.tmod_add_mul_tdiv a.val b.divisor.val
          grind
    have hsign : a.val.tmod b.divisor.val ≠ 0 →
        (a.val.tmod b.divisor.val < 0 ↔ a.val < 0) := by
      intro h0
      have h := tmod_between a.val b.divisor.val
      constructor
      · intro hn
        apply Classical.byContradiction
        intro ha
        have := h.1 (by omega)
        omega
      · intro ha
        have := h.2 ha
        omega
    by_cases hs : a.val.tmod b.divisor.val = 0 ∨
        decide (a.val.tmod b.divisor.val < 0) = decide (b.divisor.val < 0)
    · rw [if_pos hs, if_neg]
      · apply congrArg Except.ok
        apply Subtype.ext
        rw [hrval, hform, Int.zero_mul, Int.add_zero]
        exact (wrapInt_of_inRange _ _ (tmod_fits a b.divisor)).symm
      · rintro ⟨hsign', hne⟩
        rw [hqd] at hne
        by_cases h0 : a.val.tmod b.divisor.val = 0
        · exact hne (by omega)
        · have he := hs.resolve_left h0
          rw [decide_eq_decide] at he
          have hi := (hsign h0).symm.trans he
          rcases hsign' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have := hi.1 h1
            omega
          · have := hi.2 h2
            omega
    · have h0 : a.val.tmod b.divisor.val ≠ 0 := fun h => hs (Or.inl h)
      have hdiff : ¬ (a.val.tmod b.divisor.val < 0 ↔ b.divisor.val < 0) :=
        fun h => hs (Or.inr (decide_eq_decide.mpr h))
      rw [if_neg hs, if_pos]
      · apply congrArg Except.ok
        apply Subtype.ext
        rw [addWrapWraps_proven, hrval, hform, Int.one_mul]
      · refine ⟨?_, ?_⟩
        · by_cases ha : a.val < 0
          · left
            refine ⟨ha, ?_⟩
            apply Classical.byContradiction
            intro hdneg
            exact hdiff ⟨fun _ => by omega, fun _ => (hsign h0).2 ha⟩
          · right
            refine ⟨by omega, ?_⟩
            apply Classical.byContradiction
            intro hdneg
            exact hdiff ⟨fun h => absurd ((hsign h0).1 h) ha, fun h => by omega⟩
        · rw [hqd]
          omega

private theorem magic_divmod_of_eq {x c q r : Int} (hc : 0 < c)
    (h : x = c * q + r) (h0 : 0 ≤ r) (h1 : r < c) :
    x / c = q ∧ x % c = r := by
  have hq : x / c = q := by
    subst h
    rw [Int.add_comm, Int.mul_comm, Int.add_mul_ediv_right _ _ (by omega : c ≠ 0),
      Int.ediv_eq_zero_of_lt h0 h1, Int.zero_add]
  refine ⟨hq, ?_⟩
  rw [Int.emod_def, hq]
  omega

private theorem magic_ediv_eq_of_bounds {x c q : Int} (hc : 0 < c)
    (h1 : c * q ≤ x) (h2 : x < c * q + c) : x / c = q :=
  (magic_divmod_of_eq hc (show x = c * q + (x - c * q) by omega)
    (by omega) (by omega)).1

private theorem magic_le_of_mul_le {D b c : Int} (hD : 0 < D)
    (h : D * b ≤ D * c) : b ≤ c := by
  rcases (show b ≤ c ∨ c + 1 ≤ b by omega) with h' | h'
  · exact h'
  · have := Int.mul_le_mul_of_nonneg_left h' (Int.le_of_lt hD)
    rw [Int.mul_add, Int.mul_one] at this
    omega

private theorem magic_lt_of_mul_lt {D b c : Int} (hD : 0 < D)
    (h : D * b < D * c) : b < c := by
  rcases (show b < c ∨ c ≤ b by omega) with h' | h'
  · exact h'
  · have := Int.mul_le_mul_of_nonneg_left h' (Int.le_of_lt hD)
    omega

private theorem magic_mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a * b := by
  have := Int.mul_le_mul_of_nonneg_left hb ha
  rwa [Int.mul_zero] at this

theorem unsigned_magic_div {W D nc K ρ X m e A : Int}
    (hD : 0 < D) (hK : 1 ≤ K) (hnc : nc = K * D)
    (hρ1 : ρ < D) (hW : W - 1 = nc + ρ) (hX : 0 < X)
    (hWX : ∃ j, X = W * j) (hm : D * m = X + e)
    (he0 : 0 ≤ e) (he1 : e < D) (hen : e * nc < X)
    (hA0 : 0 ≤ A) (hA1 : A < W) : A * m / X = A / D := by
  have hq := Int.mul_ediv_add_emod A D
  have hr0 := Int.emod_nonneg A (by omega : D ≠ 0)
  have hr1 := Int.emod_lt_of_pos A hD
  obtain ⟨q, hqd⟩ : ∃ q, q = A / D := ⟨_, rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r, r = A % D := ⟨_, rfl⟩
  rw [← hqd, ← hrd] at hq
  rw [← hrd] at hr0 hr1
  rw [← hqd]
  have hDX : X ≤ (D - r) * X := by
    have := Int.mul_le_mul_of_nonneg_right (show 1 ≤ D - r by omega)
      (Int.le_of_lt hX)
    rwa [Int.one_mul] at this
  have hND : D ≤ nc := by
    have := Int.mul_le_mul_of_nonneg_right hK (Int.le_of_lt hD)
    rw [Int.one_mul] at this
    omega
  have hen' : nc * e < X := by rw [Int.mul_comm]; exact hen
  have hqK : q ≤ K := by
    have h1 : D * q < D * (K + 1) := by
      rw [Int.mul_add, Int.mul_one, Int.mul_comm D K]
      omega
    have := magic_lt_of_mul_lt hD h1
    omega
  have hkey : A * e < (D - r) * X := by
    rcases (show q < K ∨ q = K by omega) with hlt | heq
    · have h1 := Int.mul_le_mul_of_nonneg_left (show q ≤ K - 1 by omega)
        (Int.le_of_lt hD)
      rw [Int.mul_sub, Int.mul_one, Int.mul_comm D K] at h1
      have h2 := Int.mul_le_mul_of_nonneg_right (show A ≤ nc by omega) he0
      omega
    · rw [heq, Int.mul_comm] at hq
      rcases (show r = D - 1 ∨ r ≤ D - 2 by omega) with hr | hr
      · obtain ⟨j, hj⟩ := hWX
        have hWK : W = D * (K + 1) := by
          rw [Int.mul_add, Int.mul_one, Int.mul_comm D K]
          omega
        have h1 : D * (m - (K + 1) * j) = e := by
          rw [Int.mul_sub, ← Int.mul_assoc, ← hWK]
          omega
        have he : e = 0 := by
          rcases (show m - (K + 1) * j ≤ -1 ∨
              m - (K + 1) * j = 0 ∨ 1 ≤ m - (K + 1) * j by omega) with h | h | h
          · have := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hD)
            omega
          · rw [h, Int.mul_zero] at h1
            omega
          · have := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hD)
            omega
        rw [he, Int.mul_zero]
        omega
      · have h1 := Int.mul_le_mul_of_nonneg_right (show r ≤ nc by omega) he0
        have h2 : A * e = nc * e + r * e := by
          rw [← hq, ← hnc, Int.add_mul]
        have h3 := Int.mul_le_mul_of_nonneg_right (show 2 ≤ D - r by omega)
          (Int.le_of_lt hX)
        omega
  have h1 : D * (A * m) = A * X + A * e := by
    rw [Int.mul_left_comm, hm, Int.mul_add]
  have h2 : A * X = D * (X * q) + r * X := by
    rw [← hq, Int.add_mul, Int.mul_assoc, Int.mul_comm q X]
  have h3 : (D - r) * X = D * X - r * X := Int.sub_mul _ _ _
  have h4 : D * (X * q + X) = D * (X * q) + D * X := Int.mul_add _ _ _
  have h5 := magic_mul_nonneg hr0 (Int.le_of_lt hX)
  have h6 := magic_mul_nonneg hA0 he0
  apply magic_ediv_eq_of_bounds hX
  · apply magic_le_of_mul_le hD
    omega
  · apply magic_lt_of_mul_lt hD
    omega

theorem unsignedInverseLoop_total {t : IntTy} (d nc signedmin signedmax : JInt t)
    (fuel : Nat) (state : UnsignedLoopState t) :
    ∃ result, unsignedInverseLoop d nc signedmin signedmax fuel state = .ok result := by
  induction fuel generalizing state with
  | zero => exact ⟨state, rfl⟩
  | succ fuel ih =>
      have hconvert (x : JInt t) : JuliaLean.base.int.convert t x = .ok x := by
        simp only [JuliaLean.base.int.convert, JInt.convert, dif_pos x.property]
      simp only [unsignedInverseLoop, hconvert, Bind.bind, Except.bind]
      repeat' split
      all_goals first | exact ih _ | exact ⟨_, rfl⟩

theorem signedInverseLoop_p_bounds {t : IntTy} (anc ad : JInt t)
    (fuel : Nat) (state : SignedLoopState t) :
    state.p ≤ (signedInverseLoop anc ad fuel state).p ∧
      (signedInverseLoop anc ad fuel state).p ≤ state.p + fuel := by
  induction fuel generalizing state with
  | zero => simp [signedInverseLoop]
  | succ fuel ih =>
      dsimp only [signedInverseLoop]
      repeat' split
      all_goals dsimp only
      all_goals
        first
        | (constructor
           · apply Nat.le_trans ?_ (ih _).1
             dsimp only
             omega
           · apply Nat.le_trans (ih _).2
             dsimp only
             omega)
        | exact ⟨Nat.le_succ _, by omega⟩

theorem unsignedInverseLoop_p_bounds {t : IntTy} (d nc signedmin signedmax : JInt t)
    (fuel : Nat) (state result : UnsignedLoopState t)
    (hresult : unsignedInverseLoop d nc signedmin signedmax fuel state = .ok result) :
    state.p ≤ result.p ∧ result.p ≤ state.p + fuel := by
  induction fuel generalizing state result with
  | zero =>
      cases hresult
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ fuel ih =>
      have hconvert (x : JInt t) : JuliaLean.base.int.convert t x = .ok x := by
        simp only [JuliaLean.base.int.convert, JInt.convert, dif_pos x.property]
      simp only [unsignedInverseLoop, hconvert, Bind.bind, Except.bind] at hresult
      repeat' split at hresult
      all_goals
        first
        | (have h := ih _ _ hresult
           dsimp only at h
           exact ⟨by omega, by omega⟩)
        | (cases hresult
           dsimp only
           exact ⟨by omega, by omega⟩)

theorem signedInverseConstructor_divisor {t : IntTy} (hSigned : t.signed = true)
    (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (d : JInt t)
    (inverse : SignedMultiplicativeInverse t)
    (hresult : signedInverseConstructor hSigned remFn divremFn d = .ok inverse) :
    inverse.divisor = d := by
  simp only [signedInverseConstructor, Bind.bind, Except.bind] at hresult
  split at hresult
  · cases hresult
  · repeat' first | split at hresult | cases hresult
    all_goals rfl

theorem unsignedInverseConstructor_divisor {t : IntTy} (hUnsigned : t.signed = false)
    (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (d : JInt t)
    (inverse : UnsignedMultiplicativeInverse t)
    (hresult : unsignedInverseConstructor hUnsigned remFn divremFn d = .ok inverse) :
    inverse.divisor = d := by
  simp only [unsignedInverseConstructor, Bind.bind, Except.bind] at hresult
  split at hresult
  · cases hresult
  · repeat' first | split at hresult | cases hresult
    all_goals rfl

private def ordinaryDivrem : SameTypeDivrem := fun {t} a b => do
  let q ← JInt.div a b
  let r ← JInt.remInt a b
  pure (q, r)

theorem SignedInverseDivision_refuted : ¬ SignedInverseDivision := by
  intro h
  obtain ⟨inverse, _, _, ha⟩ :=
    h (@JInt.remInt) ordinaryDivrem (by intro t a b; rfl) (by intro t a b; rfl)
      .i8 rfl (JInt.lit .i8 (-1)) (by decide)
  have he := ha (JInt.typemin .i8)
  have hd : JInt.div (JInt.typemin .i8) (JInt.lit .i8 (-1)) =
      .error .divideError := by rfl
  rw [hd] at he
  cases he

theorem SignedInverseDivisionAndDivrem_refuted : ¬ SignedInverseDivisionAndDivrem :=
  fun h => SignedInverseDivision_refuted h.1

theorem SignedPublicAPIBehavior_refuted : ¬ SignedPublicAPIBehavior := by
  intro h
  obtain ⟨inverse, _, _, ha⟩ :=
    (h (@JInt.remInt) ordinaryDivrem (by intro t a b; rfl) (by intro t a b; rfl)
      .i8 rfl (JInt.lit .i8 (-1)) (by decide)).1
  have he := (ha (JInt.typemin .i8)).1
  have hd : JInt.div (JInt.typemin .i8) (JInt.lit .i8 (-1)) =
      .error .divideError := by rfl
  rw [hd] at he
  cases he

theorem MultiplicativeInversePublicAPI_refuted : ¬ MultiplicativeInversePublicAPI :=
  fun h => SignedPublicAPIBehavior_refuted h.2.1

theorem MultiplicativeInverseSourceBehavior_refuted : ¬ MultiplicativeInverseSourceBehavior :=
  fun h => SignedInverseDivision_refuted h.2.1

/-- Registry entries for `base/multinverses.jl`. -/
def entries : List Entry := [
  { id := "reinterpretarrays-umi-div", juliaFile := "base/multinverses.jl"
    juliaFns := ["UnsignedMultiplicativeInverse{T}(d)", "div(::T, ::UnsignedMultiplicativeInverse{T})",
      "rem(::T, ::MultiplicativeInverse{T})"]
    statement := "For every unsigned BitInteger width, every nonzero divisor produces an inverse whose divisor is unchanged, and its division and remainder equal direct fixed-width division and remainder for every dividend."
    source := "base/multinverses.jl:19-45 (constant-division algorithm)"
    status := .todo, prop := ``UnsignedMultiplicativeInverseCorrect, thm := none },
  { id := "reinterpretarrays-smi-div", juliaFile := "base/multinverses.jl"
    juliaFns := ["SignedMultiplicativeInverse{T}(d)", "div(::T, ::SignedMultiplicativeInverse{T})"]
    statement := "For every signed BitInteger width, every nonzero divisor produces an inverse whose division equals direct fixed-width division for every dividend, including the `typemin(T) ÷ -1` error case."
    source := "base/multinverses.jl:19-45 (constant-division algorithm)"
    status := .refuted, prop := ``SignedInverseDivision, thm := some ``SignedInverseDivision_refuted
    issue := "none found (queries: SignedMultiplicativeInverse; multiplicativeinverse; MultiplicativeInverses; multiplicative inverse typemin)" },
  { id := "reinterpretarrays-smi-rem-mod", juliaFile := "base/multinverses.jl"
    juliaFns := ["rem(::T, ::MultiplicativeInverse{T})", "mod(::T, ::SignedMultiplicativeInverse{T})",
      "mod(::T, ::UnsignedMultiplicativeInverse{T})"]
    statement := "For signed and unsigned BitInteger widths, inverse remainder and modulus equal direct fixed-width remainder and modulus for every nonzero divisor and dividend."
    source := "base/multinverses.jl:148-161"
    status := .todo, prop := ``InverseRemainderAndModulus, thm := none },
  { id := "reinterpretarrays-smi-div-typemin", juliaFile := "base/multinverses.jl"
    juliaFns := ["div(::T, ::SignedMultiplicativeInverse{T})", "divrem(::T, ::MultiplicativeInverse{T})"]
    statement := "For every signed BitInteger width, divisor and dividend with nonzero divisor, inverse division and divrem equal direct fixed-width division and divrem, including `typemin(T) ÷ -1` errors."
    source := "base/multinverses.jl:19-21 (constant-division algorithm); base/div.jl `divrem` contract"
    status := .refuted, prop := ``SignedInverseDivisionAndDivrem, thm := some ``SignedInverseDivisionAndDivrem_refuted
    issue := "none found (queries: SignedMultiplicativeInverse, multiplicativeinverse, MultiplicativeInverses, multiplicative inverse typemin)" },
  { id := "intfuncscov-multiplicative-inverse-source", juliaFile := "base/multinverses.jl"
    juliaFns := ["unsigned", "SignedMultiplicativeInverse", "UnsignedMultiplicativeInverse",
      "div", "rem", "divrem", "mod", "multiplicativeinverse"]
    statement := "Across all fixed-width signed and unsigned integer types, the constructors reject zero, preserve each nonzero divisor, and make inverse division, remainder, modulus, and divrem agree with direct integer operations; unsigned type conversion and signedness dispatch select the matching width."
    source := "base/multinverses.jl:8-164; constant-division invariant"
    status := .refuted, prop := ``MultiplicativeInverseSourceBehavior, thm := some ``MultiplicativeInverseSourceBehavior_refuted
    issue := "none found (queries: SignedMultiplicativeInverse; multiplicativeinverse; MultiplicativeInverses; multiplicative inverse typemin)" },
  { id := "multinverses-zero-argumenterror", juliaFile := "base/multinverses.jl"
    juliaFns := ["unsigned(::Type{Bool})", "unsigned(::Type{Int8})",
      "unsigned(::Type{Int16})", "unsigned(::Type{Int32})", "unsigned(::Type{Int64})",
      "unsigned(::Type{Int128})", "unsigned(::Type{T}) where {T<:Unsigned}",
      "unsigned(::Type{Union{}}, slurp...)", "SignedMultiplicativeInverse{T}(d)",
      "SignedMultiplicativeInverse(x::Signed)", "UnsignedMultiplicativeInverse{T}(d)",
      "UnsignedMultiplicativeInverse(x::Unsigned)", "div(::T, ::SignedMultiplicativeInverse{T})",
      "div(::T, ::UnsignedMultiplicativeInverse{T})", "rem(::T, ::MultiplicativeInverse{T})",
      "multiplicativeinverse(x::Signed)", "multiplicativeinverse(x::Unsigned)"]
    statement := "Across every signed and unsigned BitInteger width, the multiplicative-inverse constructors and multiplicativeinverse throw ArgumentError for zero. For nonzero divisors they preserve d and their div/rem agree with direct integer operations for every dividend; unsigned(::Type{T}) returns the corresponding unsigned width, and unsigned(::Type{Union{}}, slurp...) throws MethodError with (Union{}, slurp...) as its arguments."
    source := "base/multinverses.jl:8-15,53-54,90,98-99,135,137-149,163-164"
    status := .refuted, prop := ``MultiplicativeInversePublicAPI, thm := some ``MultiplicativeInversePublicAPI_refuted
    issue := "none found (queries: SignedMultiplicativeInverse; multiplicativeinverse; MultiplicativeInverses; multiplicative inverse typemin)" }
]

end JuliaLean.Proofs.base.multinverses
