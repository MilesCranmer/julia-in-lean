import JuliaLean.VersionNumbers.Order

/-!
# Proven `VersionNumber` precedence, bounds and neighbour properties
-/

namespace JuliaLean.VersionNumbers

open JuliaLean

/-! ## Arithmetic facts -/

theorem lexI_lt {x r : Int} : lexI x r < 0 ↔ x < 0 ∨ (x = 0 ∧ r < 0) := by
  unfold lexI; split <;> omega

theorem lexI_zero_left (r : Int) : lexI 0 r = r := by simp [lexI]

theorem cmpInt_self (x : Int) : cmpInt x x = 0 := cmpInt_cmp.toIsPre.self x

theorem tupleCmp_self (p : List Ident) : tupleCmp p p = 0 := tupleCmp_cmp.toIsPre.self p

theorem umin : IntTy.min .u32 = 0 := by decide

theorem umax : IntTy.max .u32 = 4294967295 := by decide

theorem vmax_val : vmax.val = 4294967295 := by decide

theorem u32_zero_val : (u32 0).val = 0 := by decide

theorem u32_nonneg (x : JInt .u32) : 0 ≤ x.val := by
  have := x.property.1; have := umin; omega

theorem u32_le (x : JInt .u32) : x.val ≤ 4294967295 := by
  have := x.property.2; have := umax; omega

/-! ## Construction -/

theorem occursRe_ident_nil : occursRe identRe [] = true := by decide +kernel

theorem newVersion_ok_of (ma mi pa : JInt .u32) (pre bld : List Ident)
    (h1 : checkPre pre bld pre = .ok ()) (h2 : checkBuild bld bld = .ok ()) :
    newVersion ma mi pa pre bld = .ok ⟨ma, mi, pa, pre, bld⟩ := by
  have n1 : ¬ ma.val < 0 := Int.not_lt.mpr (u32_nonneg ma)
  have n2 : ¬ mi.val < 0 := Int.not_lt.mpr (u32_nonneg mi)
  have n3 : ¬ pa.val < 0 := Int.not_lt.mpr (u32_nonneg pa)
  unfold newVersion
  simp [n1, n2, n3, h1, h2, bind, Except.bind, pure, Except.pure]

theorem newVersion_inv {ma mi pa : JInt .u32} {pre bld : List Ident} {w : VersionNumber}
    (h : newVersion ma mi pa pre bld = .ok w) : checkPre pre bld pre = .ok () := by
  have n1 : ¬ ma.val < 0 := Int.not_lt.mpr (u32_nonneg ma)
  have n2 : ¬ mi.val < 0 := Int.not_lt.mpr (u32_nonneg mi)
  have n3 : ¬ pa.val < 0 := Int.not_lt.mpr (u32_nonneg pa)
  unfold newVersion at h
  cases e1 : checkPre pre bld pre with
  | error err => simp [n1, n2, n3, e1, bind, Except.bind] at h
  | ok u => rfl

theorem constructible_pre {w : VersionNumber} (hc : Constructible w) (hp : w.pre = [.str []]) :
    w.build = [] := by
  have h := newVersion_inv hc
  rw [hp] at h
  cases hb : w.build with
  | nil => rfl
  | cons b bs =>
    rw [hb] at h
    simp [checkPre, occursRe_ident_nil, throw, throwThe, MonadExceptOf.throw] at h

theorem newVersion_plain (ma mi pa : JInt .u32) :
    newVersion ma mi pa [] [] = .ok ⟨ma, mi, pa, [], []⟩ :=
  newVersion_ok_of _ _ _ _ _ rfl rfl

/-! ## `isless` split at major.minor.patch -/

/-- The comparison of the pre-release and build annotations inside `vcmp`. -/
def tailCmp (a b : VersionNumber) : Int :=
  lexI (cmpInt (flag a.pre.isEmpty) (flag b.pre.isEmpty))
    (lexI (tupleCmp a.pre b.pre) (lexI (cmpInt (flag (issupbuild a)) (flag (issupbuild b)))
    (tupleCmp a.build b.build)))

theorem vless_split (a b : VersionNumber) :
    vless a b = true ↔ mmpLt a b ∨ (a.major.val = b.major.val ∧ a.minor.val = b.minor.val ∧
      a.patch.val = b.patch.val ∧ tailCmp a b < 0) := by
  have e : vcmp a b = lexI (cmpInt a.major.val b.major.val) (lexI (cmpInt a.minor.val b.minor.val)
      (lexI (cmpInt a.patch.val b.patch.val) (tailCmp a b))) := rfl
  rw [vless_iff, e]
  simp only [lexI_lt]
  unfold mmpLt
  rcases cmpInt_spec a.major.val b.major.val with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
  rcases cmpInt_spec a.minor.val b.minor.val with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
  rcases cmpInt_spec a.patch.val b.patch.val with ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ <;>
  constructor <;> intro h <;> omega

theorem vless_of_mmpLt {a b : VersionNumber} (h : mmpLt a b) : vless a b = true :=
  (vless_split a b).mpr (Or.inl h)

theorem vless_same (a b : VersionNumber) (h : sameMmp a b) : vless a b = true ↔ tailCmp a b < 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [vless_split]
  unfold mmpLt
  rw [h1, h2, h3]
  constructor
  · intro h; omega
  · intro h; omega

theorem tail_same {a b : VersionNumber} (hp : a.pre = b.pre) (hb : a.build = b.build) :
    tailCmp a b = 0 := by
  unfold tailCmp issupbuild
  rw [hp, hb]
  simp only [cmpInt_self, tupleCmp_self, lexI_zero_left]

theorem vless_same_ann {a b : VersionNumber} (hp : a.pre = b.pre) (hb : a.build = b.build) :
    vless a b = true ↔ mmpLt a b := by
  rw [vless_split, tail_same hp hb]
  constructor
  · intro h; rcases h with h | ⟨_, _, _, h⟩
    · exact h
    · omega
  · exact Or.inl

theorem tupleCmp_nonneg_nil (l : List Ident) : 0 ≤ tupleCmp l [] := by
  rw [tupleCmp_eq]; cases l <;> simp [lexList]

theorem tupleCmp_nil_cons (y : Ident) (ys : List Ident) : tupleCmp [] (y :: ys) = -1 := by
  rw [tupleCmp_eq]; rfl

theorem tupleCmp_ge_min (x : Ident) (xs : List Ident) : 0 ≤ tupleCmp (x :: xs) [.str []] := by
  rw [tupleCmp_eq]
  simp only [lexList]
  have h1 : 0 ≤ identCmp x (.str []) := by
    cases x with
    | num n => simp [identCmp]
    | str s => cases s <;> simp [identCmp, cmpStr_nil_nil, cmpStr_cons_nil]
  have h2 : 0 ≤ lexList identCmp xs [] := by cases xs <;> simp [lexList]
  unfold lexI; split <;> omega

theorem tail_lo {w lo : VersionNumber} (hc : Constructible w) (h1 : lo.pre = [.str []])
    (h2 : lo.build = []) : 0 ≤ tailCmp w lo := by
  unfold tailCmp issupbuild
  rw [h1, h2]
  cases hp : w.pre with
  | nil => simp [flag, cmpInt, lexI]
  | cons x xs =>
    have hT := tupleCmp_ge_min x xs
    have hZ : tupleCmp (x :: xs) [.str []] = 0 → w.build = [] :=
      fun h => constructible_pre hc (hp.trans (tupleCmp_cmp.eq0 _ _ h))
    have f1 : flag (x :: xs).isEmpty = 0 := rfl
    have f2 : flag [Ident.str []].isEmpty = 0 := rfl
    rw [f1, f2, cmpInt_self, lexI_zero_left]
    unfold lexI
    split
    · omega
    · rw [hZ (by omega)]
      simp [cmpInt_self, tupleCmp_self]

theorem tail_hi {hi w : VersionNumber} (h1 : hi.pre = []) (h2 : hi.build = [.str []]) :
    0 ≤ tailCmp hi w := by
  unfold tailCmp issupbuild
  rw [h1, h2]
  have e1 : ([Ident.str []] == [Ident.str []]) = true := rfl
  cases hp : w.pre with
  | cons x xs => simp [flag, cmpInt, lexI]
  | nil =>
    rw [e1, cmpInt_self, tupleCmp_self, lexI_zero_left, lexI_zero_left]
    cases hb : (w.build == [Ident.str []])
    · simp [flag, cmpInt, lexI]
    · rw [eq_of_beq hb]
      simp [cmpInt_self, tupleCmp_self, lexI]

theorem vless_lo (w lo : VersionNumber) (hc : Constructible w) (h1 : lo.pre = [.str []])
    (h2 : lo.build = []) : vless w lo = true ↔ mmpLt w lo := by
  rw [vless_split]
  have := tail_lo hc h1 h2
  constructor
  · intro h; rcases h with h | ⟨_, _, _, h⟩
    · exact h
    · omega
  · exact Or.inl

theorem vless_hi (hi w : VersionNumber) (h1 : hi.pre = []) (h2 : hi.build = [.str []]) :
    vless hi w = true ↔ mmpLt hi w := by
  rw [vless_split]
  have := tail_hi (w := w) h1 h2
  constructor
  · intro h; rcases h with h | ⟨_, _, _, h⟩
    · exact h
    · omega
  · exact Or.inl

theorem vless_false_of_plain {v t : VersionNumber} (hv : v.pre = []) (ht : Plain t)
    (h : ¬ mmpLt v t) : vless v t = false := by
  have h0 : 0 ≤ tailCmp v t := by
    unfold tailCmp issupbuild
    rw [hv, ht.1, ht.2]
    have e0 : (([] : List Ident) == [Ident.str []]) = false := rfl
    rw [e0, cmpInt_self, tupleCmp_self, lexI_zero_left, lexI_zero_left]
    cases hb : (v.build == [Ident.str []])
    · rw [cmpInt_self, lexI_zero_left]; exact tupleCmp_nonneg_nil _
    · simp [flag, cmpInt, lexI]
  cases e : vless v t
  · rfl
  · rcases (vless_split v t).mp e with h' | ⟨_, _, _, h'⟩
    · exact absurd h' h
    · omega

/-! ## semver precedence -/

theorem exists_cons {α : Type} {l : List α} (h : l ≠ []) : ∃ x xs, l = x :: xs := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => exact ⟨x, xs, rfl⟩

theorem isEmpty_append_cons {α : Type} (p : List α) (x : α) (q : List α) :
    (p ++ x :: q).isEmpty = false := by
  cases p <;> rfl

theorem lexList_append {α : Type} {c : α → α → Int} (h : IsPre c) (p as bs : List α) :
    lexList c (p ++ as) (p ++ bs) = lexList c as bs := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [List.cons_append, lexList, h.self, ih, lexI_zero_left]

theorem strLt_cmp : ∀ s t : List Char, strLt s t → cmpStr s t < 0
  | [], [], h => by simp [strLt] at h
  | [], _ :: _, _ => by rw [cmpStr_nil_cons]; decide
  | _ :: _, [], h => by simp [strLt] at h
  | a :: as, b :: bs, h => by
    rcases h with h | ⟨rfl, h⟩
    · simp only [cmpStr]; rw [if_pos h]; decide
    · simp only [cmpStr]
      have : ¬ a.val < a.val := by rw [UInt32.lt_iff_toNat_lt]; exact Nat.lt_irrefl _
      rw [if_neg this, if_neg this]
      exact strLt_cmp as bs h

theorem identPrecedes_lt : ∀ x y : Ident, identPrecedes x y → identCmp x y < 0
  | .num m, .num n, h => by
    have h' : m.val < n.val := h
    show cmpInt m.val n.val < 0
    rcases cmpInt_spec m.val n.val with ⟨_, e⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  | .num _, .str t, h => by
    cases t with
    | nil => exact absurd rfl h
    | cons c cs => simp [identCmp]
  | .str s, .str t, h => strLt_cmp s t h.2
  | .str _, .num _, h => h.elim

theorem semverPrecedence_proven : SemverPrecedence := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hs ha hb
    rw [vless_same a b hs]
    unfold tailCmp
    obtain ⟨x, xs, hx⟩ := exists_cons ha
    rw [hb, hx, lexI_lt]
    left
    exact (by decide : cmpInt 0 1 < 0)
  · intro a b hs hp ha hb
    rw [vless_same a b hs]
    unfold tailCmp issupbuild
    obtain ⟨y, ys, hy⟩ := exists_cons hb
    have e0 : (([] : List Ident) == [Ident.str []]) = false := rfl
    rw [hp, ha, hy, cmpInt_self, tupleCmp_self, lexI_zero_left, lexI_zero_left, e0,
      tupleCmp_nil_cons]
    cases (y :: ys == [Ident.str []]) <;> decide
  · intro a b p x y q r hs ha hb hxy
    rw [vless_same a b hs]
    unfold tailCmp
    rw [ha, hb, isEmpty_append_cons, isEmpty_append_cons, cmpInt_self, lexI_zero_left, lexI_lt]
    left
    rw [tupleCmp_eq, lexList_append identCmp_cmp.toIsPre]
    simp only [lexList, lexI_lt]
    exact Or.inl (identPrecedes_lt x y hxy)
  · intro a b p q hs ha hb hp hq
    obtain ⟨z, zs, rfl⟩ := exists_cons hp
    obtain ⟨y, ys, rfl⟩ := exists_cons hq
    rw [vless_same a b hs]
    unfold tailCmp
    rw [ha, hb, isEmpty_append_cons, show (z :: zs).isEmpty = false from rfl, cmpInt_self,
      lexI_zero_left, lexI_lt]
    left
    have := lexList_append identCmp_cmp.toIsPre (z :: zs) [] (y :: ys)
    rw [List.append_nil] at this
    rw [tupleCmp_eq, this]
    exact (by decide : (-1 : Int) < 0)

/-! ## typemin, typemax, bounds -/

theorem typemin_major : typeminV.major.val = 0 := by decide
theorem typemin_minor : typeminV.minor.val = 0 := by decide
theorem typemin_patch : typeminV.patch.val = 0 := by decide
theorem typemax_major : typemaxV.major.val = 4294967295 := by decide
theorem typemax_minor : typemaxV.minor.val = 4294967295 := by decide
theorem typemax_patch : typemaxV.patch.val = 4294967295 := by decide

theorem typeminTypemax_proven : TypeminTypemax := by
  refine ⟨by decide +kernel, by unfold Constructible; decide +kernel, fun v hc => ⟨?_, ?_⟩⟩
  · cases e : vless v typeminV
    · rfl
    · have h := (vless_lo v typeminV hc rfl rfl).mp e
      unfold mmpLt at h
      have := u32_nonneg v.major; have := u32_nonneg v.minor; have := u32_nonneg v.patch
      rw [typemin_major, typemin_minor, typemin_patch] at h
      omega
  · cases e : vless typemaxV v
    · rfl
    · have h := (vless_hi typemaxV v rfl rfl).mp e
      unfold mmpLt at h
      have := u32_le v.major; have := u32_le v.minor; have := u32_le v.patch
      rw [typemax_major, typemax_minor, typemax_patch] at h
      omega

theorem lowerbound_eq (v : VersionNumber) :
    lowerbound v = .ok ⟨v.major, v.minor, v.patch, [.str []], []⟩ := by
  unfold lowerbound versionOf
  exact newVersion_ok_of _ _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem upperbound_eq (v : VersionNumber) :
    upperbound v = .ok ⟨v.major, v.minor, v.patch, [], [.str []]⟩ := by
  unfold upperbound versionOf
  exact newVersion_ok_of _ _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem boundsBracket_proven : BoundsBracket := by
  intro v
  exact ⟨_, _, lowerbound_eq v, upperbound_eq v,
    fun w hc => ⟨vless_lo w _ hc rfl rfl, vless_hi _ w rfl rfl⟩⟩

/-! ## `thispatch`, `thisminor`, `thismajor` -/

theorem thispatch_eq (v : VersionNumber) :
    thispatch v = .ok ⟨v.major, v.minor, v.patch, [], []⟩ := by
  unfold thispatch versionOf; exact newVersion_plain _ _ _

theorem thisminor_eq (v : VersionNumber) :
    thisminor v = .ok ⟨v.major, v.minor, u32 0, [], []⟩ := by
  unfold thisminor versionOf; exact newVersion_plain _ _ _

theorem thismajor_eq (v : VersionNumber) :
    thismajor v = .ok ⟨v.major, u32 0, u32 0, [], []⟩ := by
  unfold thismajor versionOf; exact newVersion_plain _ _ _

theorem plain_le_of_mmp {a b : VersionNumber} (hp : Plain a) (hq : Plain b)
    (h : mmpLt a b → False) : vless a b = false := by
  cases e : vless a b
  · rfl
  · exact absurd ((vless_same_ann (hp.1.trans hq.1.symm) (hp.2.trans hq.2.symm)).mp e) h

theorem thisMonotone_proven : ThisMonotone := by
  refine ⟨fun v => ⟨thispatch_eq v, thisminor_eq v, thismajor_eq v⟩, fun v w hvw => ?_⟩
  have key : ¬ mmpLt w v := fun h => by rw [vless_of_mmpLt h] at hvw; cases hvw
  refine ⟨fun a b ha hb => ?_, fun a b ha hb => ?_, fun a b ha hb => ?_⟩
  · rw [thispatch_eq] at ha hb; cases ha; cases hb
    exact plain_le_of_mmp ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ fun h => key (by unfold mmpLt at h ⊢; exact h)
  · rw [thisminor_eq] at ha hb; cases ha; cases hb
    refine plain_le_of_mmp ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ fun h => key ?_
    unfold mmpLt at h ⊢
    dsimp only at h
    omega
  · rw [thismajor_eq] at ha hb; cases ha; cases hb
    refine plain_le_of_mmp ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ fun h => key ?_
    unfold mmpLt at h ⊢
    dsimp only at h
    rw [u32_zero_val] at h
    omega

/-! ## `nextpatch`, `nextminor`, `nextmajor` -/

theorem succ_ok (x : JInt .u32) (h : x.val < vmax.val) :
    ∃ s : JInt .u32, succU32 x = .ok s ∧ s.val = x.val + 1 := by
  rw [vmax_val] at h
  have h' : IntTy.min .u32 ≤ x.val + 1 ∧ x.val + 1 ≤ IntTy.max .u32 := by
    have := umin; have := umax; have := u32_nonneg x; omega
  unfold succU32 JInt.convert
  rw [dif_pos h']
  exact ⟨_, rfl, rfl⟩

theorem succ_vmax : succU32 vmax = .error (.inexactError "UInt32") := by decide +kernel

theorem nextpatch_true {v : VersionNumber} (h : vless v ⟨v.major, v.minor, v.patch, [], []⟩ = true) :
    nextpatch v = .ok ⟨v.major, v.minor, v.patch, [], []⟩ := by
  simp [nextpatch, thispatch_eq, h, bind, Except.bind, pure, Except.pure]

theorem nextpatch_false {v : VersionNumber} {r : Jl (JInt .u32)}
    (h : vless v ⟨v.major, v.minor, v.patch, [], []⟩ = false) (hs : succU32 v.patch = r) :
    nextpatch v = (do versionOf v.major v.minor (← r)) := by
  simp [nextpatch, thispatch_eq, h, hs, bind, Except.bind]

theorem nextminor_true {v : VersionNumber} (h : vless v ⟨v.major, v.minor, u32 0, [], []⟩ = true) :
    nextminor v = .ok ⟨v.major, v.minor, u32 0, [], []⟩ := by
  simp [nextminor, thisminor_eq, h, bind, Except.bind, pure, Except.pure]

theorem nextminor_false {v : VersionNumber} {r : Jl (JInt .u32)}
    (h : vless v ⟨v.major, v.minor, u32 0, [], []⟩ = false) (hs : succU32 v.minor = r) :
    nextminor v = (do versionOf v.major (← r) (u32 0)) := by
  simp [nextminor, thisminor_eq, h, hs, bind, Except.bind]

theorem nextmajor_true {v : VersionNumber} (h : vless v ⟨v.major, u32 0, u32 0, [], []⟩ = true) :
    nextmajor v = .ok ⟨v.major, u32 0, u32 0, [], []⟩ := by
  simp [nextmajor, thismajor_eq, h, bind, Except.bind, pure, Except.pure]

theorem nextmajor_false {v : VersionNumber} {r : Jl (JInt .u32)}
    (h : vless v ⟨v.major, u32 0, u32 0, [], []⟩ = false) (hs : succU32 v.major = r) :
    nextmajor v = (do versionOf (← r) (u32 0) (u32 0)) := by
  simp [nextmajor, thismajor_eq, h, hs, bind, Except.bind]

theorem nextOverflow_proven : NextOverflow := by
  intro v hv
  have n1 := u32_nonneg v.patch
  have n2 := u32_nonneg v.minor
  refine ⟨fun hp => ?_, fun hm => ?_, fun hM => ?_⟩
  · have hl := vless_false_of_plain (t := ⟨v.major, v.minor, v.patch, [], []⟩) hv ⟨rfl, rfl⟩
      (by unfold mmpLt; dsimp only; omega)
    refine ⟨"UInt32", ?_⟩
    have := nextpatch_false (v := v) (r := .error (.inexactError "UInt32")) hl (by rw [hp]; exact succ_vmax)
    rw [this]; rfl
  · have hl := vless_false_of_plain (t := ⟨v.major, v.minor, u32 0, [], []⟩) hv ⟨rfl, rfl⟩
      (by unfold mmpLt; dsimp only; rw [u32_zero_val]; omega)
    refine ⟨"UInt32", ?_⟩
    have := nextminor_false (v := v) (r := .error (.inexactError "UInt32")) hl (by rw [hm]; exact succ_vmax)
    rw [this]; rfl
  · have hl := vless_false_of_plain (t := ⟨v.major, u32 0, u32 0, [], []⟩) hv ⟨rfl, rfl⟩
      (by unfold mmpLt; dsimp only; rw [u32_zero_val]; omega)
    refine ⟨"UInt32", ?_⟩
    have := nextmajor_false (v := v) (r := .error (.inexactError "UInt32")) hl (by rw [hM]; exact succ_vmax)
    rw [this]; rfl

theorem least_helper (u v w : VersionNumber) (hu : Plain u) (hw : Plain w) (hvu : vless v u = true)
    (h : mmpLt u w → mmpLt u v ∨ u = w ∨ vless v u = false) : vless u w = false := by
  cases e : vless u w
  · rfl
  · have m := (vless_same_ann (hu.1.trans hw.1.symm) (hu.2.trans hw.2.symm)).mp e
    rcases h m with h | rfl | h
    · have := (islessTotalOrder_proven.2.2.2 v u hvu).2
      rw [vless_of_mmpLt h] at this; cases this
    · rw [islessTotalOrder_proven.1] at e; cases e
    · rw [hvu] at h; cases h

theorem plain_ext {u : VersionNumber} (hu : Plain u) {M m p : JInt .u32} (h1 : u.major.val = M.val)
    (h2 : u.minor.val = m.val) (h3 : u.patch.val = p.val) : u = ⟨M, m, p, [], []⟩ := by
  obtain ⟨u1, u2, u3, u4, u5⟩ := u
  obtain ⟨h4, h5⟩ := hu
  dsimp only at h1 h2 h3 h4 h5
  have := Subtype.ext h1; have := Subtype.ext h2; have := Subtype.ext h3
  subst_vars
  rfl

theorem nextLeast_proven : NextLeast := by
  intro v
  have np := u32_nonneg v.patch
  have nm := u32_nonneg v.minor
  have z := u32_zero_val
  refine ⟨fun hp => ?_, fun hm => ?_, fun hM => ?_⟩
  · cases hl : vless v ⟨v.major, v.minor, v.patch, [], []⟩
    · obtain ⟨s, hs, hsv⟩ := succ_ok v.patch hp
      refine ⟨⟨v.major, v.minor, s, [], []⟩, ?_, ⟨rfl, rfl⟩, ?_, ?_⟩
      · rw [nextpatch_false hl hs]; exact newVersion_plain _ _ _
      · exact vless_of_mmpLt (by unfold mmpLt; dsimp only; omega)
      · intro u hu hvu
        refine least_helper u v _ hu ⟨rfl, rfl⟩ hvu fun h => ?_
        unfold mmpLt at h ⊢
        dsimp only at h
        by_cases e : u.major.val = v.major.val ∧ u.minor.val = v.minor.val ∧ u.patch.val = v.patch.val
        · right; right; rw [plain_ext hu e.1 e.2.1 e.2.2]; exact hl
        · left; omega
    · exact ⟨_, nextpatch_true hl, ⟨rfl, rfl⟩, hl,
        fun u hu hvu => least_helper u v _ hu ⟨rfl, rfl⟩ hvu fun h => Or.inl h⟩
  · cases hl : vless v ⟨v.major, v.minor, u32 0, [], []⟩
    · obtain ⟨s, hs, hsv⟩ := succ_ok v.minor hm
      refine ⟨⟨v.major, s, u32 0, [], []⟩, ?_, ⟨rfl, rfl⟩, z, ?_, ?_⟩
      · rw [nextminor_false hl hs]; exact newVersion_plain _ _ _
      · exact vless_of_mmpLt (by unfold mmpLt; dsimp only; omega)
      · intro u hu hu0 hvu
        refine least_helper u v _ hu ⟨rfl, rfl⟩ hvu fun h => ?_
        unfold mmpLt at h ⊢
        dsimp only at h
        by_cases e : u.major.val = v.major.val ∧ u.minor.val = v.minor.val
        · right; right; rw [plain_ext hu e.1 e.2 (hu0.trans z.symm)]; exact hl
        · left; omega
    · refine ⟨_, nextminor_true hl, ⟨rfl, rfl⟩, z, hl, fun u hu hu0 hvu => ?_⟩
      refine least_helper u v _ hu ⟨rfl, rfl⟩ hvu fun h => Or.inl ?_
      unfold mmpLt at h ⊢
      dsimp only at h
      omega
  · cases hl : vless v ⟨v.major, u32 0, u32 0, [], []⟩
    · obtain ⟨s, hs, hsv⟩ := succ_ok v.major hM
      refine ⟨⟨s, u32 0, u32 0, [], []⟩, ?_, ⟨rfl, rfl⟩, z, z, ?_, ?_⟩
      · rw [nextmajor_false hl hs]; exact newVersion_plain _ _ _
      · exact vless_of_mmpLt (by unfold mmpLt; dsimp only; omega)
      · intro u hu hu1 hu0 hvu
        refine least_helper u v _ hu ⟨rfl, rfl⟩ hvu fun h => ?_
        unfold mmpLt at h ⊢
        dsimp only at h
        by_cases e : u.major.val = v.major.val
        · right; right; rw [plain_ext hu e (hu1.trans z.symm) (hu0.trans z.symm)]; exact hl
        · left; omega
    · refine ⟨_, nextmajor_true hl, ⟨rfl, rfl⟩, z, z, hl, fun u hu hu1 hu0 hvu => ?_⟩
      refine least_helper u v _ hu ⟨rfl, rfl⟩ hvu fun h => Or.inl ?_
      unfold mmpLt at h ⊢
      dsimp only at h
      omega

end JuliaLean.VersionNumbers
