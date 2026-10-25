import JuliaLean.VersionNumbers.Props

/-!
# Proven `VersionNumber` order properties
-/

namespace JuliaLean.VersionNumbers

open JuliaLean

/-! ## Comparators -/

/-- Lexicographic combination of two comparison results. -/
def lexI (x r : Int) : Int := if x ≠ 0 then x else r

theorem lexI_le {x r : Int} : lexI x r ≤ 0 ↔ x < 0 ∨ (x = 0 ∧ r ≤ 0) := by
  unfold lexI; split <;> omega

theorem lexI_zero {x r : Int} : lexI x r = 0 ↔ x = 0 ∧ r = 0 := by
  unfold lexI; split <;> omega

/-- A total preorder given as a three-way comparison. -/
structure IsPre {α : Type} (c : α → α → Int) : Prop where
  anti : ∀ a b, c b a = - c a b
  trans : ∀ a b d, c a b ≤ 0 → c b d ≤ 0 → c a d ≤ 0

/-- A total order given as a three-way comparison. -/
structure IsCmp {α : Type} (c : α → α → Int) : Prop extends IsPre c where
  eq0 : ∀ a b, c a b = 0 → a = b

section
variable {α : Type} {c : α → α → Int}

theorem IsPre.self (h : IsPre c) (a : α) : c a a = 0 := by
  have := h.anti a a; omega

theorem IsPre.lt_le (h : IsPre c) {a b d : α} (h1 : c a b < 0) (h2 : c b d ≤ 0) : c a d < 0 := by
  have := h.anti a d; have := h.anti a b
  have : ¬ c d a ≤ 0 := fun h3 => by have := h.trans b d a h2 h3; omega
  omega

theorem IsPre.le_lt (h : IsPre c) {a b d : α} (h1 : c a b ≤ 0) (h2 : c b d < 0) : c a d < 0 := by
  have := h.anti a d; have := h.anti b d
  have : ¬ c d a ≤ 0 := fun h3 => by have := h.trans d a b h3 h1; omega
  omega

theorem pull_pre {β : Type} {c : β → β → Int} (h : IsPre c) (f : α → β) :
    IsPre (fun a b => c (f a) (f b)) :=
  ⟨fun _ _ => h.anti _ _, fun _ _ _ => h.trans _ _ _⟩

theorem lex_pre {c1 c2 : α → α → Int} (h1 : IsPre c1) (h2 : IsPre c2) :
    IsPre (fun a b => lexI (c1 a b) (c2 a b)) := by
  constructor
  · intro a b
    show lexI (c1 b a) (c2 b a) = - lexI (c1 a b) (c2 a b)
    rw [h1.anti, h2.anti]; unfold lexI; split <;> split <;> omega
  · intro a b d hab hbd
    simp only [lexI_le] at hab hbd ⊢
    rcases hab with hab | ⟨e1, hab⟩ <;> rcases hbd with hbd | ⟨e2, hbd⟩
    · exact Or.inl (h1.lt_le hab (by omega))
    · exact Or.inl (h1.lt_le hab (by omega))
    · exact Or.inl (h1.le_lt (by omega) hbd)
    · refine Or.inr ⟨?_, h2.trans a b d hab hbd⟩
      have := h1.trans a b d (by omega) (by omega)
      have := h1.trans d b a (by rw [h1.anti]; omega) (by rw [h1.anti]; omega)
      have := h1.anti a d
      omega

/-- Lexicographic comparison of lists, a proper prefix first. -/
def lexList (c : α → α → Int) : List α → List α → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => lexI (c a b) (lexList c as bs)

theorem lexList_anti (h : IsCmp c) : ∀ as bs : List α, lexList c bs as = - lexList c as bs
  | [], [] => by simp [lexList]
  | [], _ :: _ => by simp [lexList]
  | _ :: _, [] => by simp [lexList]
  | a :: as, b :: bs => by
    simp only [lexList]
    rw [h.anti, lexList_anti h as bs]; unfold lexI; split <;> split <;> omega

theorem lexList_trans (h : IsCmp c) :
    ∀ as bs ds : List α, lexList c as bs ≤ 0 → lexList c bs ds ≤ 0 → lexList c as ds ≤ 0
  | [], _, [], _, _ => by simp [lexList]
  | [], _, _ :: _, _, _ => by simp [lexList]
  | _ :: _, [], _, h1, _ => by simp [lexList] at h1
  | _ :: _, _ :: _, [], _, h2 => by simp [lexList] at h2
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [lexList, lexI_le] at h1 h2 ⊢
    have hp := h.toIsPre
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact Or.inl (hp.lt_le h1 (by omega))
    · exact Or.inl (hp.lt_le h1 (by omega))
    · exact Or.inl (hp.le_lt (by omega) h2)
    · have := h.eq0 _ _ e1; have := h.eq0 _ _ e2; subst_vars
      exact Or.inr ⟨hp.self _, lexList_trans h _ _ _ h1 h2⟩

theorem lexList_eq0 (h : IsCmp c) : ∀ as bs : List α, lexList c as bs = 0 → as = bs
  | [], [], _ => rfl
  | [], _ :: _, e => by simp [lexList] at e
  | _ :: _, [], e => by simp [lexList] at e
  | a :: as, b :: bs, e => by
    simp only [lexList, lexI_zero] at e
    rw [h.eq0 _ _ e.1, lexList_eq0 h as bs e.2]

theorem lexList_cmp (h : IsCmp c) : IsCmp (lexList c) :=
  ⟨⟨lexList_anti h, lexList_trans h⟩, lexList_eq0 h⟩

end

theorem cmpInt_spec (x y : Int) :
    (x < y ∧ cmpInt x y = -1) ∨ (x = y ∧ cmpInt x y = 0) ∨ (y < x ∧ cmpInt x y = 1) := by
  unfold cmpInt
  split
  · exact Or.inl ⟨by assumption, rfl⟩
  · split
    · exact Or.inr (Or.inr ⟨by assumption, rfl⟩)
    · exact Or.inr (Or.inl ⟨by omega, rfl⟩)

theorem cmpInt_cmp : IsCmp cmpInt := by
  refine ⟨⟨fun a b => ?_, fun a b d h1 h2 => ?_⟩, fun a b h => ?_⟩
  · rcases cmpInt_spec a b with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases cmpInt_spec b a with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · rcases cmpInt_spec a b with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases cmpInt_spec b d with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
      rcases cmpInt_spec a d with ⟨h7, h8⟩ | ⟨h7, h8⟩ | ⟨h7, h8⟩ <;> omega
  · rcases cmpInt_spec a b with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

/-- Code-point comparison of characters. -/
def charCmp (a b : Char) : Int := cmpInt a.val.toNat b.val.toNat

theorem charCmp_cmp : IsCmp charCmp := by
  refine ⟨pull_pre cmpInt_cmp.toIsPre (fun a : Char => (a.val.toNat : Int)), fun a b h => ?_⟩
  have e := cmpInt_cmp.eq0 _ _ h
  exact Char.ext (UInt32.toNat_inj.mp (by omega))

theorem cmpStr_eq : ∀ as bs : List Char, cmpStr as bs = lexList charCmp as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    rw [cmpStr, lexList, cmpStr_eq as bs]
    simp only [UInt32.lt_iff_toNat_lt, charCmp, lexI]
    rcases cmpInt_spec (a.val.toNat : Int) b.val.toNat with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [h2]
    · have : a.val.toNat < b.val.toNat := by omega
      rw [if_pos this]; simp
    · have : a.val.toNat = b.val.toNat := by omega
      rw [this, if_neg (Nat.lt_irrefl _), if_neg (Nat.lt_irrefl _)]; simp
    · have h3 : b.val.toNat < a.val.toNat := by omega
      have h4 : ¬ a.val.toNat < b.val.toNat := by omega
      rw [if_neg h4, if_pos h3]; simp

theorem cmpStr_cmp : IsCmp cmpStr := by
  have e : cmpStr = lexList charCmp := funext fun a => funext fun b => cmpStr_eq a b
  rw [e]; exact lexList_cmp charCmp_cmp

theorem cmpStr_nil_nil : cmpStr [] [] = 0 := rfl
theorem cmpStr_nil_cons (c : Char) (cs : List Char) : cmpStr [] (c :: cs) = -1 := rfl
theorem cmpStr_cons_nil (c : Char) (cs : List Char) : cmpStr (c :: cs) [] = 1 := rfl

theorem identCmp_cmp : IsCmp identCmp := by
  refine ⟨⟨fun a b => ?_, fun a b d h1 h2 => ?_⟩, fun a b h => ?_⟩
  · rcases a with x | (_ | ⟨_, _⟩) <;> rcases b with y | (_ | ⟨_, _⟩) <;>
      simp [identCmp, cmpStr_nil_nil, cmpStr_nil_cons, cmpStr_cons_nil] <;>
      first | exact cmpInt_cmp.anti _ _ | exact cmpStr_cmp.anti _ _
  · rcases a with x | (_ | ⟨_, _⟩) <;> rcases b with y | (_ | ⟨_, _⟩) <;>
      rcases d with z | (_ | ⟨_, _⟩) <;>
      simp [identCmp, cmpStr_nil_nil, cmpStr_nil_cons, cmpStr_cons_nil] at h1 h2 ⊢ <;>
      first | exact cmpInt_cmp.trans _ _ _ h1 h2 | exact cmpStr_cmp.trans _ _ _ h1 h2 | omega
  · rcases a with x | (_ | ⟨_, _⟩) <;> rcases b with y | (_ | ⟨_, _⟩) <;>
      simp [identCmp, cmpStr_nil_nil, cmpStr_nil_cons, cmpStr_cons_nil] at h ⊢
    all_goals first
      | exact Subtype.ext (cmpInt_cmp.eq0 _ _ h)
      | exact cmpStr_cmp.eq0 _ _ h
      | exact List.cons.inj (cmpStr_cmp.eq0 _ _ h)

theorem tupleCmp_eq : ∀ as bs : List Ident, tupleCmp as bs = lexList identCmp as bs
  | [], [] => by simp [tupleCmp, zipCmp, lexList]
  | [], _ :: _ => by simp [tupleCmp, zipCmp, lexList]
  | _ :: _, [] => by simp [tupleCmp, zipCmp, lexList]
  | a :: as, b :: bs => by
    rw [lexList]
    by_cases h : identCmp a b = 0
    · have e : tupleCmp (a :: as) (b :: bs) = tupleCmp as bs := by simp [tupleCmp, zipCmp, h]
      rw [e, tupleCmp_eq as bs]; simp [lexI, h]
    · have e : tupleCmp (a :: as) (b :: bs) = identCmp a b := by simp [tupleCmp, zipCmp, h]
      rw [e]; simp [lexI, h]

theorem tupleCmp_cmp : IsCmp tupleCmp := by
  have e : tupleCmp = lexList identCmp := funext fun a => funext fun b => tupleCmp_eq a b
  rw [e]; exact lexList_cmp identCmp_cmp

/-! ## `isless` as a comparator -/

def flag (b : Bool) : Int := if b then 1 else 0

/-- The three-way comparison underlying `isless`. -/
def vcmp (a b : VersionNumber) : Int :=
  lexI (cmpInt a.major.val b.major.val) (lexI (cmpInt a.minor.val b.minor.val)
    (lexI (cmpInt a.patch.val b.patch.val) (lexI (cmpInt (flag a.pre.isEmpty) (flag b.pre.isEmpty))
    (lexI (tupleCmp a.pre b.pre) (lexI (cmpInt (flag (issupbuild a)) (flag (issupbuild b)))
    (tupleCmp a.build b.build))))))

theorem vcmp_pre : IsPre vcmp :=
  lex_pre (pull_pre cmpInt_cmp.toIsPre (fun v : VersionNumber => v.major.val))
    (lex_pre (pull_pre cmpInt_cmp.toIsPre (fun v : VersionNumber => v.minor.val))
    (lex_pre (pull_pre cmpInt_cmp.toIsPre (fun v : VersionNumber => v.patch.val))
    (lex_pre (pull_pre cmpInt_cmp.toIsPre (fun v : VersionNumber => flag v.pre.isEmpty))
    (lex_pre (pull_pre tupleCmp_cmp.toIsPre (fun v : VersionNumber => v.pre))
    (lex_pre (pull_pre cmpInt_cmp.toIsPre (fun v : VersionNumber => flag (issupbuild v)))
    (pull_pre tupleCmp_cmp.toIsPre (fun v : VersionNumber => v.build)))))))

theorem vcmp_eq0 (a b : VersionNumber) (h : vcmp a b = 0) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [vcmp, lexI_zero] at h
  obtain ⟨h1, h2, h3, -, h5, -, h7⟩ := h
  have := Subtype.ext (cmpInt_cmp.eq0 _ _ h1)
  have := Subtype.ext (cmpInt_cmp.eq0 _ _ h2)
  have := Subtype.ext (cmpInt_cmp.eq0 _ _ h3)
  have := tupleCmp_cmp.eq0 _ _ h5
  have := tupleCmp_cmp.eq0 _ _ h7
  subst_vars
  rfl

theorem step_int (x y r : Int) (t : Bool) (h : t = decide (r < 0)) :
    (if x < y then true else if x > y then false else t) = decide (lexI (cmpInt x y) r < 0) := by
  rcases cmpInt_spec x y with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2]
  · rw [if_pos h1]; simp [lexI]
  · subst h1; rw [if_neg (Int.lt_irrefl _), if_neg (Int.lt_irrefl _), h]; simp [lexI]
  · rw [if_neg (by omega), if_pos h1]; simp [lexI]

theorem step_flag (p q : Bool) (r : Int) (t : Bool) (h : t = decide (r < 0)) :
    (if !p && q then true else if p && !q then false else t) =
      decide (lexI (cmpInt (flag p) (flag q)) r < 0) := by
  cases p <;> cases q <;> simp [flag, cmpInt, lexI, h]

theorem step_cmp (c r : Int) (t : Bool) (h : t = decide (r < 0)) :
    (if c < 0 then true else if c > 0 then false else t) = decide (lexI c r < 0) := by
  unfold lexI
  rcases Int.lt_trichotomy c 0 with h1 | h1 | h1
  · rw [if_pos h1, if_pos (by omega)]; simp [h1]
  · subst h1; simp [h]
  · rw [if_neg (by omega), if_pos h1, if_pos (by omega)]
    exact (decide_eq_false (by omega)).symm

theorem vless_eq (a b : VersionNumber) : vless a b = decide (vcmp a b < 0) := by
  unfold vless vcmp
  exact step_int _ _ _ _ (step_int _ _ _ _ (step_int _ _ _ _
    (step_flag _ _ _ _ (step_cmp _ _ _ (step_flag _ _ _ _ rfl)))))

theorem vless_iff (a b : VersionNumber) : vless a b = true ↔ vcmp a b < 0 := by
  rw [vless_eq]; exact decide_eq_true_iff

/-! ## Equality, hashing, total order -/

theorem eqStructural_proven : EqStructural := by
  intro a b
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  constructor
  · intro h
    have e1 : a1 = b1 := Decidable.byContradiction fun e => by simp [veq, e] at h
    have e2 : a2 = b2 := Decidable.byContradiction fun e => by simp [veq, e1, e] at h
    have e3 : a3 = b3 := Decidable.byContradiction fun e => by simp [veq, e1, e2, e] at h
    have e4 : tupleCmp a4 b4 = 0 :=
      Decidable.byContradiction fun e => by simp [veq, e1, e2, e3, e] at h
    have e5 : tupleCmp a5 b5 = 0 :=
      Decidable.byContradiction fun e => by simp [veq, e1, e2, e3, e4, e] at h
    have := tupleCmp_cmp.eq0 _ _ e4
    have := tupleCmp_cmp.eq0 _ _ e5
    subst_vars
    rfl
  · intro h
    cases h
    simp [veq, tupleCmp_cmp.self]

theorem hashConsistent_proven : HashConsistent := by
  intro hu ht h a b e
  rw [eqStructural_proven] at e
  rw [e]

theorem islessTotalOrder_proven : IslessTotalOrder := by
  have hp := vcmp_pre
  refine ⟨fun a => ?_, fun a b d h1 h2 => ?_, fun a b => ?_, fun a b h => ?_⟩
  · rw [vless_eq, hp.self]; rfl
  · rw [vless_iff] at *
    exact hp.lt_le h1 (by omega)
  · rw [vless_iff, vless_iff, hp.anti a b]
    rcases Int.lt_trichotomy (vcmp a b) 0 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ((eqStructural_proven a b).mpr (vcmp_eq0 _ _ h)))
    · exact Or.inr (Or.inr (by omega))
  · rw [vless_iff] at h
    refine ⟨?_, ?_⟩
    · cases e : veq a b
      · rfl
      · rw [eqStructural_proven] at e
        subst e
        rw [hp.self] at h
        exact absurd h (Int.lt_irrefl 0)
    · rw [vless_eq, hp.anti]
      simp only [decide_eq_false_iff_not]
      omega

end JuliaLean.VersionNumbers
