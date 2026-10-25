import JuliaLean.Platforms.Lemmas
import JuliaLean.Platforms.DlProofVersion

/-!
# `parse_dl_name_version` inverts the library file-name scheme (`DlNameInverse`)

For each pattern the proof shows that the pattern matches the extension part of
the file name (with the version in group 2) and no longer suffix, unless the name
is one `AmbiguousName` excludes. The derivation relation `Mt` of
`DlProofRegex.lean` turns these into statements about strings.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (Re Caps matchRe capture VersionNumber vprint)
open JuliaLean.VersionNumbers.Re

/-! ## Characters -/

/-- `[\.\d]`. -/
def isDD (c : Char) : Bool := c == '.' || isAsciiDigit c

/-- A character of `vprint v` for a version without annotations. -/
def VCh (y : Char) : Prop := y = '.' ∨ IsDig y

theorem VCh.alpha {y : Char} (h : VCh y) : isAsciiAlpha y = false := by
  rcases h with rfl | h
  · decide
  · exact h.alpha

theorem VCh.ne {y : Char} (h : VCh y) : y ≠ '\n' ∧ y ≠ '-' ∧ y ≠ '/' := by
  rcases h with rfl | h
  · decide
  · exact ⟨h.ne.2.1, h.ne.2.2.1, h.ne.2.2.2.2.1⟩

theorem VCh.dd {y : Char} (h : VCh y) : isDD y = true := by
  rcases h with rfl | h
  · decide
  · simp [isDD, h.ascii]

theorem digit_ne_dot {x : Char} (h : isAsciiDigit x = true) : x ≠ '.' := by
  rintro rfl
  exact absurd h (by decide)

theorem dd_digit {x : Char} (h : isDD x = true) (hx : x ≠ '.') : isAsciiDigit x = true := by
  simp only [isDD, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd h hx
  · exact h

/-! ## Printed versions -/

/-- `M.m.p` with nonempty decimal components. -/
def VStr (V : List Char) : Prop :=
  ∃ A B C, V = A ++ '.' :: (B ++ '.' :: C) ∧ A ≠ [] ∧ B ≠ [] ∧ C ≠ [] ∧
    (∀ y ∈ A, IsDig y) ∧ (∀ y ∈ B, IsDig y) ∧ (∀ y ∈ C, IsDig y)

theorem vstr_vprint (w : VersionNumber) (hp : w.pre = []) (hb : w.build = []) : VStr (vprint w) :=
  ⟨_, _, _, vprint_plain w hp hb, showNat_ne_nil _, showNat_ne_nil _, showNat_ne_nil _,
    showNat_dig _, showNat_dig _, showNat_dig _⟩

theorem VStr.vch {V : List Char} (h : VStr V) : ∀ y ∈ V, VCh y := by
  obtain ⟨A, B, C, rfl, -, -, -, hA, hB, hC⟩ := h
  intro y hy
  simp only [List.mem_append, List.mem_cons] at hy
  rcases hy with hy | hy | hy | hy | hy
  · exact .inr (hA y hy)
  · exact .inl hy
  · exact .inr (hB y hy)
  · exact .inl hy
  · exact .inr (hC y hy)

theorem VStr.vch_cons {V : List Char} (h : VStr V) : ∀ y ∈ '.' :: V, VCh y := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with hy | hy
  · exact .inl hy
  · exact h.vch y hy

theorem VStr.ne_nil {V : List Char} (h : VStr V) : V ≠ [] := by
  obtain ⟨A, B, C, rfl, -⟩ := h
  simp

theorem VStr.noslash {V : List Char} (h : VStr V) : ∀ y ∈ V, y ≠ '/' :=
  fun y hy => (h.vch y hy).ne.2.2

theorem dropWhile_dot {a : Char} (ha : a ≠ '.') (t : List Char) :
    (a :: t).dropWhile (· == '.') = a :: t := by
  have h : (a == '.') = false := beq_eq_false_iff_ne.2 ha
  simp only [List.dropWhile, h]

theorem VStr.strip {V : List Char} (h : VStr V) : stripChar '.' V = V := by
  obtain ⟨A, B, C, hV, hA, -, hC, hAd, -, hCd⟩ := h
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  rcases List.eq_nil_or_concat C with rfl | ⟨C', c, rfl⟩
  · exact absurd rfl hC
  have ha : a ≠ '.' := (hAd a (by simp)).ne.1
  have hc : c ≠ '.' := (hCd c (by simp)).ne.1
  have h1 : V = a :: (A' ++ '.' :: (B ++ '.' :: C'.concat c)) := by rw [hV]; rfl
  have hr : V.reverse = c :: (a :: (A' ++ '.' :: (B ++ '.' :: C'))).reverse := by rw [hV]; simp
  unfold stripChar
  rw [h1, dropWhile_dot ha, ← h1, hr, dropWhile_dot hc, ← hr, List.reverse_reverse]

theorem stripChar_dot_cons (V : List Char) : stripChar '.' ('.' :: V) = stripChar '.' V := by
  unfold stripChar
  simp [List.dropWhile]

/-! ## Every `.` followed by a digit -/

def dotsOk : List Char → Bool
  | [] => true
  | [c] => c != '.'
  | c :: d :: t => (c != '.' || isAsciiDigit d) && dotsOk (d :: t)

theorem dotsOk_cons_ne {c : Char} (hc : c ≠ '.') (r : List Char) : dotsOk (c :: r) = dotsOk r := by
  cases r with
  | nil => simp [dotsOk, hc]
  | cons d t => simp [dotsOk, hc]

theorem dotsOk_append_nodot : ∀ (u r : List Char), (∀ x ∈ u, x ≠ '.') → dotsOk (u ++ r) = dotsOk r
  | [], _, _ => rfl
  | x :: u, r, h => by
    rw [List.cons_append, dotsOk_cons_ne (h x (by simp)),
      dotsOk_append_nodot u r (fun y hy => h y (by simp [hy]))]

theorem dotsOk_tail (c : Char) (r : List Char) (h : dotsOk (c :: r) = true) : dotsOk r = true := by
  cases r with
  | nil => rfl
  | cons d t =>
    simp only [dotsOk, Bool.and_eq_true] at h
    exact h.2

theorem dotsOk_split : ∀ (u v : List Char), dotsOk (u ++ '.' :: v) = true →
    ∃ d t, v = d :: t ∧ isAsciiDigit d = true
  | [], [], h => by simp [dotsOk] at h
  | [], d :: t, h => by
    simp only [List.nil_append, dotsOk, Bool.and_eq_true, Bool.or_eq_true] at h
    refine ⟨d, t, rfl, ?_⟩
    rcases h.1 with h1 | h1
    · exact absurd h1 (by decide)
    · exact h1
  | x :: u, v, h => dotsOk_split u v (dotsOk_tail x _ h)

theorem dotsOk_blk (ds r : List Char) (hne : ds ≠ []) (hd : ∀ x ∈ ds, isAsciiDigit x = true)
    (hr : dotsOk r = true) : dotsOk ('.' :: (ds ++ r)) = true := by
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h1 : dotsOk ((d :: ds) ++ r) = true := by
    rw [dotsOk_append_nodot _ _ (fun x hx => digit_ne_dot (hd x hx))]
    exact hr
  simp only [List.cons_append] at h1 ⊢
  simp only [dotsOk, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨.inr (hd d (by simp)), h1⟩

/-! ## `(\.\d+)*` and the tags -/

/-- Words of `(\.\d+)*`, through the properties the proofs use. -/
def BL (u : List Char) : Prop :=
  (u = [] ∨ ∃ t, u = '.' :: t) ∧ (∀ x ∈ u, isDD x = true) ∧
    ∀ r, dotsOk r = true → dotsOk (u ++ r) = true

/-- Words of `(\.\d+)+`. -/
def PL (y : List Char) : Prop := (∃ t, y = '.' :: t) ∧ BL y

theorem BL_nil : BL [] := ⟨.inl rfl, by simp, fun _ hr => hr⟩

theorem BL_blk {ds v : List Char} (hne : ds ≠ []) (hd : ∀ x ∈ ds, isAsciiDigit x = true) (hv : BL v) :
    BL ('.' :: (ds ++ v)) := by
  refine ⟨.inr ⟨_, rfl⟩, ?_, fun r hr => ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · decide
    · simp [isDD, hd x hx]
    · exact hv.2.1 x hx
  · rw [List.cons_append, List.append_assoc]
    exact dotsOk_blk ds (v ++ r) hne hd (hv.2.2 r hr)

/-- `\.\d+`. -/
def blk : Re := seq (chr '.') (plus (cls isAsciiDigit))

/-- `(?:\.\d+)+`. -/
def verP : Re := plus blk

/-- `[A-Za-z][\w\-]*`. -/
def tagD : Re := seq (cls isAsciiAlpha) (star (cls fun c => isWord c || c == '-'))

/-- `(?:((?:\.\d+)+)([A-Za-z][\w\-]*)?)?`. -/
def VO : Re := opt (seq (group verGroup verP) (opt (group 3 tagD)))

theorem soRest_eq : soRest = seq (litD (s% ".so")) (seq VO eol) := rfl

theorem dylibRest_eq : dylibRest = seq VO (seq (litD (s% ".dylib")) eol) := rfl

/-- `(?:[\.\d]+)+`. -/
def ddP : Re := plus (plus (cls fun c => c == '.' || isAsciiDigit c))

/-- `[A-Za-z][\w\.]*`. -/
def tagW : Re := seq (cls isAsciiAlpha) (star (cls fun c => isWord c || c == '.'))

/-- `(?:-(?:((?:[\.\d]+)+)([A-Za-z][\w\.]*)?)?)?`. -/
def WO : Re := opt (seq (chr '-') (opt (seq (group verGroup ddP) (opt (group 3 tagW)))))

theorem dllRest_eq : dllRest = seq WO (seq (litCI (s% ".dll")) eol) := rfl

section Inv
variable {s s' : List Char} {c c' : Caps}

theorem blk_inv (h : Mt blk s c s' c') :
    c' = c ∧ ∃ ds, s = '.' :: (ds ++ s') ∧ ds ≠ [] ∧ ∀ x ∈ ds, isAsciiDigit x = true := by
  obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
  obtain ⟨hs, hc⟩ := Mt_chr_inv h1
  obtain ⟨hc', ds, hs1, hne, hd⟩ := Mt_plus_cls h2
  subst hs hs1
  exact ⟨hc'.trans hc, ds, rfl, hne, hd⟩

theorem verP_inv (h : Mt verP s c s' c') : c' = c ∧ ∃ y, s = y ++ s' ∧ PL y := by
  obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
  obtain ⟨hc1, ds, hs, hne, hd⟩ := blk_inv h1
  obtain ⟨hc2, u, hu, hBL⟩ := Mt_star_lang (L := BL) BL_nil (fun s c s' c' h => by
    obtain ⟨hc, ds, hs, hne, hd⟩ := blk_inv h
    exact ⟨hc, '.' :: ds, by simp [hs], fun v hv => by simpa using BL_blk hne hd hv⟩) h2
  subst hs hu
  exact ⟨hc2.trans hc1, '.' :: (ds ++ u), by simp, ⟨_, rfl⟩, BL_blk hne hd hBL⟩

theorem tagD_inv (h : Mt tagD s c s' c') : c' = c ∧ ∃ z, s = z ++ s' ∧ IsTag true z := by
  obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
  obtain ⟨a, hs, ha, hc1⟩ := Mt_cls_inv h1
  obtain ⟨hc2, u, hu, hU⟩ := Mt_star_cls h2
  subst hs hu
  refine ⟨hc2.trans hc1, a :: u, rfl, a, u, rfl, ha, List.all_eq_true.2 fun x hx => ?_⟩
  simpa using hU x hx

theorem tagW_inv (h : Mt tagW s c s' c') : c' = c ∧ ∃ z, s = z ++ s' ∧ IsTag false z := by
  obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
  obtain ⟨a, hs, ha, hc1⟩ := Mt_cls_inv h1
  obtain ⟨hc2, u, hu, hU⟩ := Mt_star_cls h2
  subst hs hu
  refine ⟨hc2.trans hc1, a :: u, rfl, a, u, rfl, ha, List.all_eq_true.2 fun x hx => ?_⟩
  simpa using hU x hx

theorem ddP_inv (h : Mt ddP s c s' c') :
    c' = c ∧ ∃ y, s = y ++ s' ∧ y ≠ [] ∧ ∀ x ∈ y, isDD x = true := by
  obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
  obtain ⟨hc1, u, hu, hne, hU⟩ := Mt_plus_cls h1
  obtain ⟨hc2, v, hv, hV⟩ := Mt_star_lang (L := fun v => ∀ x ∈ v, isDD x = true) (by simp)
    (fun s c s' c' h => by
      obtain ⟨hc, u, hu, -, hU⟩ := Mt_plus_cls h
      refine ⟨hc, u, hu, fun v hv x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact hU x hx
      · exact hv x hx) h2
  subst hu hv
  refine ⟨hc2.trans hc1, u ++ v, by simp, by simp [hne], fun x hx => ?_⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact hU x hx
  · exact hV x hx

theorem VO_inv (h : Mt VO s c s' c') :
    (s' = s ∧ c' = c) ∨ ∃ y z, s = y ++ (z ++ s') ∧ PL y ∧ (z = [] ∨ IsTag true z) ∧
      capture c' verGroup = some y := by
  rcases Mt_opt_inv h with h | h
  · right
    obtain ⟨s1, c1, hg, ht⟩ := Mt_seq_inv h
    obtain ⟨c0, hP, hc1⟩ := Mt_group_inv hg
    obtain ⟨-, y, hs, hy⟩ := verP_inv hP
    subst hs hc1
    rcases Mt_opt_inv ht with ht | ⟨hs', hc'⟩
    · obtain ⟨c2, hT, hc'⟩ := Mt_group_inv ht
      obtain ⟨hc2, z, hs1, hz⟩ := tagD_inv hT
      subst hs1 hc' hc2
      refine ⟨y, z, rfl, hy, .inr hz, ?_⟩
      simp only [take_cap]
      simp [capture, verGroup]
    · subst hs' hc'
      refine ⟨y, [], rfl, hy, .inl rfl, ?_⟩
      simp only [take_cap]
      simp [capture, verGroup]
  · exact .inl h

theorem WO_inv (h : Mt WO s c s' c') :
    (s' = s ∧ c' = c) ∨ (s = '-' :: s' ∧ c' = c) ∨
      ∃ y z, s = '-' :: (y ++ (z ++ s')) ∧ y ≠ [] ∧ (∀ x ∈ y, isDD x = true) ∧
        (z = [] ∨ IsTag false z) ∧ capture c' verGroup = some y := by
  rcases Mt_opt_inv h with h | h
  · right
    obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
    obtain ⟨hs, hc1⟩ := Mt_chr_inv h1
    subst hs hc1
    rcases Mt_opt_inv h2 with h2 | ⟨hs', hc'⟩
    · right
      obtain ⟨s2, c2, hg, ht⟩ := Mt_seq_inv h2
      obtain ⟨c0, hP, hc2⟩ := Mt_group_inv hg
      obtain ⟨-, y, hs1, hne, hy⟩ := ddP_inv hP
      subst hs1 hc2
      rcases Mt_opt_inv ht with ht | ⟨hs', hc'⟩
      · obtain ⟨c3, hT, hc'⟩ := Mt_group_inv ht
        obtain ⟨hc3, z, hs2, hz⟩ := tagW_inv hT
        subst hs2 hc' hc3
        refine ⟨y, z, rfl, hne, hy, .inr hz, ?_⟩
        simp only [take_cap]
        simp [capture, verGroup]
      · subst hs' hc'
        refine ⟨y, [], rfl, hne, hy, .inl rfl, ?_⟩
        simp only [take_cap]
        simp [capture, verGroup]
    · left
      subst hs' hc'
      exact ⟨rfl, rfl⟩
  · exact .inl h

end Inv

theorem tagD_nodot {z : List Char} (hz : z = [] ∨ IsTag true z) : ∀ x ∈ z, x ≠ '.' := by
  rintro x hx rfl
  rcases hz with rfl | ⟨c, r, rfl, hc, hr⟩
  · simp at hx
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact absurd hc (by decide)
    · have := List.all_eq_true.1 hr _ hx
      revert this
      decide

theorem tagW_nodash {z : List Char} (hz : z = [] ∨ IsTag false z) : ∀ x ∈ z, x ≠ '-' := by
  rintro x hx rfl
  rcases hz with rfl | ⟨c, r, rfl, hc, hr⟩
  · simp at hx
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact absurd hc (by decide)
    · have := List.all_eq_true.1 hr _ hx
      revert this
      decide

/-! ## The three patterns -/

theorem so_inv {s s' : List Char} {x : Caps} (h : Mt soRest s [] s' x) :
    (s' = [] ∨ s' = ['\n']) ∧ ∃ R, s = '.' :: 's' :: 'o' :: (R ++ s') ∧
      ((R = [] ∧ x = []) ∨
        ∃ y z, R = y ++ z ∧ PL y ∧ (z = [] ∨ IsTag true z) ∧ capture x verGroup = some y) := by
  rw [soRest_eq] at h
  obtain ⟨s1, c1, h1, h⟩ := Mt_seq_inv h
  obtain ⟨hs, hc1⟩ := Mt_litD _ (by decide) h1
  obtain ⟨s2, c2, h2, h3⟩ := Mt_seq_inv h
  obtain ⟨he, hc, hs2⟩ := Mt_eol_inv h3
  subst hs hc1 he hc
  refine ⟨hs2, ?_⟩
  rcases VO_inv h2 with ⟨he, hc⟩ | ⟨y, z, hyz, hy, hz, hcap⟩
  · subst he hc
    exact ⟨[], rfl, .inl ⟨rfl, rfl⟩⟩
  · subst hyz
    exact ⟨y ++ z, by simp, .inr ⟨y, z, rfl, hy, hz, hcap⟩⟩

theorem dylib_inv {s s' : List Char} {x : Caps} (h : Mt dylibRest s [] s' x) :
    (s' = [] ∨ s' = ['\n']) ∧ ∃ R, s = R ++ (s% ".dylib" ++ s') ∧
      ((R = [] ∧ x = []) ∨
        ∃ y z, R = y ++ z ∧ PL y ∧ (z = [] ∨ IsTag true z) ∧ capture x verGroup = some y) := by
  rw [dylibRest_eq] at h
  obtain ⟨s1, c1, h1, h⟩ := Mt_seq_inv h
  obtain ⟨s2, c2, h2, h3⟩ := Mt_seq_inv h
  obtain ⟨hs1, hc2⟩ := Mt_litD _ (by decide) h2
  obtain ⟨he, hc, hs2⟩ := Mt_eol_inv h3
  subst hs1 hc2 he hc
  refine ⟨hs2, ?_⟩
  rcases VO_inv h1 with ⟨he, hc⟩ | ⟨y, z, hyz, hy, hz, hcap⟩
  · subst he hc
    exact ⟨[], rfl, .inl ⟨rfl, rfl⟩⟩
  · subst hyz
    exact ⟨y ++ z, by simp, .inr ⟨y, z, rfl, hy, hz, hcap⟩⟩

theorem dll_inv {s s' : List Char} {x : Caps} (h : Mt dllRest s [] s' x) :
    (s' = [] ∨ s' = ['\n']) ∧ ∃ R u, s = R ++ (u ++ s') ∧ u.length = 4 ∧
      ((R = [] ∧ x = []) ∨ (R = ['-'] ∧ x = []) ∨
        ∃ y z, R = '-' :: (y ++ z) ∧ y ≠ [] ∧ (∀ c ∈ y, isDD c = true) ∧ (z = [] ∨ IsTag false z) ∧
          capture x verGroup = some y) := by
  rw [dllRest_eq] at h
  obtain ⟨s1, c1, h1, h⟩ := Mt_seq_inv h
  obtain ⟨s2, c2, h2, h3⟩ := Mt_seq_inv h
  obtain ⟨hc2, u, hs1, hu⟩ := Mt_litCI _ (by decide) h2
  obtain ⟨he, hc, hs2⟩ := Mt_eol_inv h3
  subst hs1 hc2 he hc
  refine ⟨hs2, ?_⟩
  rcases WO_inv h1 with ⟨he, hc⟩ | ⟨he, hc⟩ | ⟨y, z, hyz, hne, hy, hz, hcap⟩
  · subst he hc
    exact ⟨[], u, rfl, hu, .inl ⟨rfl, rfl⟩⟩
  · subst he hc
    exact ⟨['-'], u, rfl, hu, .inr (.inl ⟨rfl, rfl⟩)⟩
  · subst hyz
    exact ⟨'-' :: (y ++ z), u, by simp, hu, .inr (.inr ⟨y, z, rfl, hne, hy, hz, hcap⟩)⟩

/-! ## No match at an earlier split -/

theorem strip_tail {Q R t s' : List Char} {a : Char} (ha : a ≠ '\n') (hs' : s' = [] ∨ s' = ['\n'])
    (h : Q ++ (t ++ [a]) = R ++ ((t ++ [a]) ++ s')) : s' = [] ∧ Q = R := by
  rcases hs' with rfl | rfl
  · rw [List.append_nil] at h
    exact ⟨rfl, (List.append_inj' h rfl).1⟩
  · exfalso
    exact no_nl (P := Q ++ t) (P' := R ++ (t ++ [a])) ha (by simpa using h)

theorem strip_tail4 {Q R u t s' : List Char} {a : Char} (ha : a ≠ '\n') (hs' : s' = [] ∨ s' = ['\n'])
    (hu : u.length = (t ++ [a]).length) (h : Q ++ (t ++ [a]) = R ++ (u ++ s')) : s' = [] ∧ Q = R := by
  rcases hs' with rfl | rfl
  · rw [List.append_nil] at h
    exact ⟨rfl, (List.append_inj' h hu.symm).1⟩
  · exfalso
    exact no_nl (P := Q ++ t) (P' := R ++ u) ha (by simpa using h)

/-- The last `.`-block of a prefix `w` of a word of `(\.\d+)*` followed by
nothing or by another block. -/
theorem lastblock {y w rest : List Char} (hy : BL y) (hyw : y = w ++ rest)
    (hrest : rest = [] ∨ ∃ t, rest = '.' :: t) (hw : '.' ∈ w) :
    ∃ p ds, w = p ++ '.' :: ds ∧ AllDigits ds := by
  obtain ⟨p, ds, rfl, hds⟩ := last_dot w hw
  refine ⟨p, ds, rfl, ?_, ?_⟩
  · intro hnil
    subst hnil
    have h := hy.2.2 [] rfl
    rw [hyw, List.append_nil, List.append_assoc] at h
    obtain ⟨d, t, hdt, hd⟩ := dotsOk_split p _ h
    rcases hrest with rfl | ⟨t', rfl⟩
    · simp at hdt
    · injection hdt with hd1 hd2
      rw [← hd1] at hd
      exact absurd hd (by decide)
  · rw [List.all_eq_true]
    intro x hx
    have hxy : x ∈ y := by rw [hyw]; simp [hx]
    exact dd_digit (hy.2.1 x hxy) (hds x hx)

theorem so_none (w vt : List Char) (hw : w ≠ []) :
    matchRe soRest (w ++ '.' :: 's' :: 'o' :: vt) = none := by
  cases hm : matchRe soRest (w ++ '.' :: 's' :: 'o' :: vt) with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨s', h⟩ := matchRe_sound hm
    obtain ⟨hs', R, hR, hRc⟩ := so_inv h
    have hok : dotsOk (R ++ s') = true := by
      have h0 : dotsOk s' = true := by rcases hs' with rfl | rfl <;> rfl
      rcases hRc with ⟨rfl, -⟩ | ⟨y, z, rfl, hy, hz, -⟩
      · simpa using h0
      · rw [List.append_assoc]
        exact hy.2.2.2 _ (by rw [dotsOk_append_nodot _ _ (tagD_nodot hz)]; exact h0)
    match w, hw, hR with
    | [], hw, _ => exact hw rfl
    | [a], _, hR =>
      injection hR with h1 h2
      injection h2 with h3 h4
      exact absurd h3 (by decide)
    | [a, b], _, hR =>
      injection hR with h1 h2
      injection h2 with h3 h4
      injection h4 with h5 h6
      exact absurd h5 (by decide)
    | a :: b :: d :: w', _, hR =>
      injection hR with h1 h2
      injection h2 with h3 h4
      injection h4 with h5 h6
      rw [← h6] at hok
      obtain ⟨e, t, he, hd⟩ := dotsOk_split w' _ hok
      injection he with he1 he2
      rw [← he1] at hd
      exact absurd hd (by decide)

theorem mac_none_unv (pre w : List Char) (hw : w ≠ [])
    (hamb : ¬ AmbiguousName (s% "macos") (pre ++ w) false) :
    matchRe dylibRest (w ++ s% ".dylib") = none := by
  cases hm : matchRe dylibRest (w ++ s% ".dylib") with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨s', h⟩ := matchRe_sound hm
    obtain ⟨hs', R, hR, hRc⟩ := dylib_inv h
    obtain ⟨-, hwR⟩ := strip_tail (Q := w) (t := ['.', 'd', 'y', 'l', 'i']) (a := 'b') (by decide) hs' hR
    rcases hRc with ⟨hR0, -⟩ | ⟨y, z, hyz, hy, hz, -⟩
    · exact hw (hwR.trans hR0)
    · apply hamb
      unfold AmbiguousName
      rw [if_pos (by decide)]
      obtain ⟨t, ht⟩ := hy.1
      obtain ⟨p, ds, hp, hds⟩ := lastblock hy.2 (List.append_nil y).symm (.inl rfl) (by rw [ht]; simp)
      refine ⟨pre ++ p, ds, z, by rw [hwR, hyz, hp]; simp, hds, ?_⟩
      rcases hz with hz | hz
      · exact .inl hz
      · exact .inr ⟨rfl, hz⟩

theorem mac_none_ver (pre w V : List Char) (hw : w ≠ []) (hV : VStr V)
    (hamb : ¬ AmbiguousName (s% "macos") (pre ++ w) true) :
    matchRe dylibRest (w ++ '.' :: (V ++ s% ".dylib")) = none := by
  cases hm : matchRe dylibRest (w ++ '.' :: (V ++ s% ".dylib")) with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨s', h⟩ := matchRe_sound hm
    obtain ⟨hs', R, hR, hRc⟩ := dylib_inv h
    obtain ⟨-, hwR⟩ := strip_tail (Q := w ++ '.' :: V) (R := R) (t := ['.', 'd', 'y', 'l', 'i'])
      (a := 'b') (by decide) hs' (by simpa using hR)
    rcases hRc with ⟨hR0, -⟩ | ⟨y, z, hyz, hy, hz, -⟩
    · rw [hR0] at hwR
      simp at hwR
    · apply hamb
      unfold AmbiguousName
      rw [if_pos (by decide)]
      obtain ⟨A, B, C, hVe, -, -, -, -, -, hCd⟩ := hV
      have hz0 : z = [] := by
        rcases hz with hz | ⟨c, r, rfl, hc, hr⟩
        · exact hz
        · exfalso
          have h1 : y ++ c :: r = (w ++ '.' :: (A ++ '.' :: B)) ++ '.' :: C := by
            rw [← hyz, ← hwR, hVe]
            simp
          obtain ⟨E, hE⟩ := suffix_nodot h1 (tagD_nodot (.inr ⟨c, r, rfl, hc, hr⟩))
          have hcC : c ∈ C := by rw [hE]; simp
          rw [(hCd c hcC).alpha] at hc
          exact absurd hc (by decide)
      subst hz0
      have hyw : y = w ++ '.' :: V := by rw [hwR, hyz, List.append_nil]
      obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hw
      have ha : a = '.' := by
        obtain ⟨t, ht⟩ := hy.1
        rw [hyw] at ht
        simp only [List.cons_append, List.cons.injEq] at ht
        exact ht.1
      subst ha
      obtain ⟨p, ds, hp, hds⟩ := lastblock hy.2 hyw (.inr ⟨V, rfl⟩) (by simp)
      exact ⟨pre ++ p, ds, [], by rw [hp]; simp, hds, .inl rfl⟩

theorem win_none_unv (pre w : List Char) (hw : w ≠ [])
    (hamb : ¬ AmbiguousName (s% "windows") (pre ++ w) false) :
    matchRe dllRest (w ++ s% ".dll") = none := by
  cases hm : matchRe dllRest (w ++ s% ".dll") with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨s', h⟩ := matchRe_sound hm
    obtain ⟨hs', R, u, hR, hu, hRc⟩ := dll_inv h
    obtain ⟨-, hwR⟩ := strip_tail4 (Q := w) (t := ['.', 'd', 'l']) (a := 'l') (by decide) hs' hu hR
    apply hamb
    unfold AmbiguousName
    rw [if_neg (by decide), if_pos (by decide)]
    refine ⟨rfl, ?_⟩
    rcases hRc with ⟨hR0, -⟩ | ⟨hR0, -⟩ | ⟨y, z, hyz, hne, hy, hz, -⟩
    · exact absurd (hwR.trans hR0) hw
    · exact ⟨pre, [], by rw [hwR, hR0], .inl rfl⟩
    · exact ⟨pre, y ++ z, by rw [hwR, hyz], .inr ⟨y, z, rfl, hne, List.all_eq_true.2 hy, hz⟩⟩

theorem win_none_ver (w V : List Char) (hw : w ≠ []) :
    matchRe dllRest (w ++ '-' :: (V ++ s% ".dll")) = none := by
  cases hm : matchRe dllRest (w ++ '-' :: (V ++ s% ".dll")) with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨s', h⟩ := matchRe_sound hm
    obtain ⟨hs', R, u, hR, hu, hRc⟩ := dll_inv h
    obtain ⟨-, hwR⟩ := strip_tail4 (Q := w ++ '-' :: V) (t := ['.', 'd', 'l']) (a := 'l') (by decide) hs' hu
      (by rw [← hR]; simp)
    obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hw
    rcases hRc with ⟨hR0, -⟩ | ⟨hR0, -⟩ | ⟨y, z, hyz, -, hy, hz, -⟩
    · rw [hR0] at hwR
      simp at hwR
    · rw [hR0] at hwR
      simp at hwR
    · rw [hyz] at hwR
      simp only [List.cons_append, List.cons.injEq] at hwR
      have hm : '-' ∈ y ++ z := by rw [← hwR.2]; simp
      rcases List.mem_append.1 hm with hm | hm
      · exact absurd (hy _ hm) (by decide)
      · exact tagW_nodash hz _ hm rfl

/-! ## The match at the extension -/

theorem so_cap_none {x : Caps} (hm : matchRe soRest (s% ".so") = some x) : capture x verGroup = none := by
  obtain ⟨s', h⟩ := matchRe_sound hm
  obtain ⟨-, R, hR, hRc⟩ := so_inv h
  injection hR with h1 hR1
  injection hR1 with h2 hR2
  injection hR2 with h3 hR3
  rcases hRc with ⟨-, rfl⟩ | ⟨y, z, hyz, hy, -, -⟩
  · rfl
  · exfalso
    obtain ⟨t, rfl⟩ := hy.1
    rw [hyz] at hR3
    simp at hR3

theorem so_cap_ver {V : List Char} (hV : VStr V) {x : Caps}
    (hm : matchRe soRest ('.' :: 's' :: 'o' :: '.' :: V) = some x) :
    capture x verGroup = some ('.' :: V) := by
  obtain ⟨s', h⟩ := matchRe_sound hm
  obtain ⟨hs', R, hR, hRc⟩ := so_inv h
  injection hR with h1 hR1
  injection hR1 with h2 hR2
  injection hR2 with h3 hR3
  have hs0 : s' = [] := by
    rcases hs' with h0 | h0
    · exact h0
    · exfalso
      have : '\n' ∈ '.' :: V := by rw [hR3, h0]; simp
      exact (hV.vch_cons _ this).ne.1 rfl
  subst hs0
  rw [List.append_nil] at hR3
  rcases hRc with ⟨hR0, -⟩ | ⟨y, z, hyz, -, hz, hcap⟩
  · rw [hR0] at hR3
    simp at hR3
  · have hz0 : z = [] := by
      rcases hz with hz | ⟨c, r, rfl, hc, -⟩
      · exact hz
      · exfalso
        have hc' : c ∈ '.' :: V := by rw [hR3, hyz]; simp
        rw [(hV.vch_cons c hc').alpha] at hc
        exact absurd hc (by decide)
    subst hz0
    rw [hcap, hR3, hyz, List.append_nil]

theorem mac_cap_unv {x : Caps} (hm : matchRe dylibRest (s% ".dylib") = some x) :
    capture x verGroup = none := by
  obtain ⟨s', h⟩ := matchRe_sound hm
  obtain ⟨hs', R, hR, hRc⟩ := dylib_inv h
  obtain ⟨-, hR0⟩ := strip_tail (Q := []) (t := ['.', 'd', 'y', 'l', 'i']) (a := 'b') (by decide) hs' hR
  rcases hRc with ⟨-, rfl⟩ | ⟨y, z, hyz, hy, -, -⟩
  · rfl
  · exfalso
    obtain ⟨t, rfl⟩ := hy.1
    rw [← hR0] at hyz
    simp at hyz

theorem mac_cap_ver {V : List Char} (hV : VStr V) {x : Caps}
    (hm : matchRe dylibRest ('.' :: (V ++ s% ".dylib")) = some x) :
    capture x verGroup = some ('.' :: V) := by
  obtain ⟨s', h⟩ := matchRe_sound hm
  obtain ⟨hs', R, hR, hRc⟩ := dylib_inv h
  obtain ⟨-, hR0⟩ := strip_tail (Q := '.' :: V) (t := ['.', 'd', 'y', 'l', 'i']) (a := 'b') (by decide) hs' hR
  rcases hRc with ⟨hR1, -⟩ | ⟨y, z, hyz, -, hz, hcap⟩
  · rw [hR1] at hR0
    simp at hR0
  · have hz0 : z = [] := by
      rcases hz with hz | ⟨c, r, rfl, hc, -⟩
      · exact hz
      · exfalso
        have hcV : c ∈ '.' :: V := by rw [hR0, hyz]; simp
        rw [(hV.vch_cons c hcV).alpha] at hc
        exact absurd hc (by decide)
    subst hz0
    rw [hcap, hR0, hyz, List.append_nil]

theorem win_cap_unv {x : Caps} (hm : matchRe dllRest (s% ".dll") = some x) : capture x verGroup = none := by
  obtain ⟨s', h⟩ := matchRe_sound hm
  obtain ⟨hs', R, u, hR, hu, hRc⟩ := dll_inv h
  obtain ⟨-, hR0⟩ := strip_tail4 (Q := []) (t := ['.', 'd', 'l']) (a := 'l') (by decide) hs' hu hR
  rcases hRc with ⟨-, rfl⟩ | ⟨hR1, -⟩ | ⟨y, z, hyz, -⟩
  · rfl
  · rw [← hR0] at hR1
    simp at hR1
  · rw [← hR0] at hyz
    simp at hyz

theorem win_cap_ver {V : List Char} (hV : VStr V) {x : Caps}
    (hm : matchRe dllRest ('-' :: (V ++ s% ".dll")) = some x) : capture x verGroup = some V := by
  obtain ⟨s', h⟩ := matchRe_sound hm
  obtain ⟨hs', R, u, hR, hu, hRc⟩ := dll_inv h
  obtain ⟨-, hR0⟩ := strip_tail4 (Q := '-' :: V) (t := ['.', 'd', 'l']) (a := 'l') (by decide) hs' hu hR
  rcases hRc with ⟨hR1, -⟩ | ⟨hR1, -⟩ | ⟨y, z, hyz, -, -, hz, hcap⟩
  · rw [hR1] at hR0
    simp at hR0
  · rw [hR1] at hR0
    simp only [List.cons.injEq, true_and] at hR0
    exact absurd hR0 hV.ne_nil
  · rw [hyz] at hR0
    simp only [List.cons.injEq, true_and] at hR0
    have hz0 : z = [] := by
      rcases hz with hz | ⟨c, r, rfl, hc, -⟩
      · exact hz
      · exfalso
        have hcV : c ∈ V := by rw [hR0]; simp
        rw [(hV.vch c hcV).alpha] at hc
        exact absurd hc (by decide)
    subst hz0
    rw [hcap, hR0, List.append_nil]

/-! ## Existence of the match at the extension -/

theorem blk_mk (ds r : List Char) (c : Caps) (hne : ds ≠ []) (hd : ∀ y ∈ ds, IsDig y) :
    Mt blk ('.' :: (ds ++ r)) c r c :=
  .seq (Mt_chr_mk '.' _ c) (Mt_plus_cls_mk ds r c hne (fun y hy => (hd y hy).ascii))

theorem verP_mk3 (A B C r : List Char) (c : Caps) (hA : A ≠ []) (hB : B ≠ []) (hC : C ≠ [])
    (hAd : ∀ y ∈ A, IsDig y) (hBd : ∀ y ∈ B, IsDig y) (hCd : ∀ y ∈ C, IsDig y) :
    Mt verP ('.' :: (A ++ '.' :: (B ++ '.' :: (C ++ r)))) c r c :=
  .seq (blk_mk A _ c hA hAd) (.starCons (blk_mk B _ c hB hBd) (by simp <;> omega)
    (.starCons (blk_mk C r c hC hCd) (by simp <;> omega) .starNil))

theorem so_mk_unv : ∃ x, Mt soRest (s% ".so") [] [] x := by
  rw [soRest_eq]
  exact ⟨_, .seq (Mt_litD_mk (s% ".so") [] [] (by decide)) (.seq (.altR .eps) (.eol (.inl rfl)))⟩

theorem so_mk_ver {V : List Char} (hV : VStr V) : ∃ x, Mt soRest ('.' :: 's' :: 'o' :: '.' :: V) [] [] x := by
  obtain ⟨A, B, C, rfl, hA, hB, hC, hAd, hBd, hCd⟩ := hV
  rw [soRest_eq]
  have hP := verP_mk3 A B C [] [] hA hB hC hAd hBd hCd
  simp only [List.append_nil] at hP
  exact ⟨_, .seq (Mt_litD_mk (s% ".so") _ [] (by decide))
    (.seq (.altL (.seq (.group hP) (.altR .eps))) (.eol (.inl rfl)))⟩

theorem mac_mk_unv : ∃ x, Mt dylibRest (s% ".dylib") [] [] x := by
  rw [dylibRest_eq]
  exact ⟨_, .seq (.altR .eps) (.seq (Mt_litD_mk (s% ".dylib") [] [] (by decide)) (.eol (.inl rfl)))⟩

theorem mac_mk_ver {V : List Char} (hV : VStr V) : ∃ x, Mt dylibRest ('.' :: (V ++ s% ".dylib")) [] [] x := by
  obtain ⟨A, B, C, rfl, hA, hB, hC, hAd, hBd, hCd⟩ := hV
  rw [dylibRest_eq]
  have hP := verP_mk3 A B C (s% ".dylib") [] hA hB hC hAd hBd hCd
  have e : '.' :: ((A ++ '.' :: (B ++ '.' :: C)) ++ s% ".dylib") =
      '.' :: (A ++ '.' :: (B ++ '.' :: (C ++ s% ".dylib"))) := by simp
  rw [e]
  exact ⟨_, .seq (.altL (.seq (.group hP) (.altR .eps)))
    (.seq (Mt_litD_mk (s% ".dylib") [] _ (by decide)) (.eol (.inl rfl)))⟩

theorem win_mk_unv : ∃ x, Mt dllRest (s% ".dll") [] [] x := by
  rw [dllRest_eq]
  exact ⟨_, .seq (.altR .eps) (.seq (Mt_litCI_mk (s% ".dll") [] [] (by decide)) (.eol (.inl rfl)))⟩

theorem win_mk_ver {V : List Char} (hV : VStr V) : ∃ x, Mt dllRest ('-' :: (V ++ s% ".dll")) [] [] x := by
  have hP : Mt ddP (V ++ s% ".dll") [] (s% ".dll") [] :=
    .seq (Mt_plus_cls_mk V _ [] hV.ne_nil (fun y hy => (hV.vch y hy).dd)) .starNil
  rw [dllRest_eq]
  exact ⟨_, .seq (.altL (.seq (Mt_chr_mk '-' _ _) (.altL (.seq (.group hP) (.altR .eps)))))
    (.seq (Mt_litCI_mk (s% ".dll") [] _ (by decide)) (.eol (.inl rfl)))⟩

/-! ## Assembly -/

theorem basename_noslash (l : List Char) (h : ∀ x ∈ l, x ≠ '/') : basename l = l := by
  unfold basename
  rw [takeWhile_all _ (fun x hx => by simpa using h x (List.mem_reverse.1 hx)), List.reverse_reverse]

theorem noslash_app {a b : List Char} (ha : ∀ x ∈ a, x ≠ '/') (hb : ∀ x ∈ b, x ≠ '/') :
    ∀ x ∈ a ++ b, x ≠ '/' := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem parse_none {o file name : Str} {m : Caps} (hb : basename file = file)
    (hl : lazyMatch (dlRest o) file = some (name, m)) (hc : capture m verGroup = none) :
    parseDlNameVersion file o = .ok (name, none) := by
  simp [parseDlNameVersion, hb, hl, hc, pure, Except.pure]

theorem parse_some {o file name cap : Str} {m : Caps} {w : VersionNumber} (hb : basename file = file)
    (hl : lazyMatch (dlRest o) file = some (name, m)) (hc : capture m verGroup = some cap)
    (hne : cap ≠ []) (hp : VersionNumbers.parse (stripChar '.' cap) = .ok w) :
    parseDlNameVersion file o = .ok (name, some w) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [parseDlNameVersion, hb, hl, hc, hp, bind, Except.bind, pure, Except.pure]

theorem platformDlext_eq (p : Platform) (o : Str) (hp : os p = some o) :
    platformDlext p = if o = s% "windows" then s% "dll" else if o = s% "macos" then s% "dylib" else s% "so" := by
  unfold platformDlext
  rw [hp]
  by_cases h1 : o = s% "windows"
  · subst h1
    decide
  · by_cases h2 : o = s% "macos"
    · subst h2
      decide
    · simp [h1, h2]

theorem so_ok (o name : Str) (v : Option VersionNumber) (hw : o ≠ s% "windows") (hm : o ≠ s% "macos")
    (hslash : '/' ∉ name) (hplain : ∀ w, v = some w → w.pre = [] ∧ w.build = []) :
    parseDlNameVersion (dlFileName o name v (s% "so")) o = .ok (name, v) := by
  have hR : dlRest o = soRest := by simp [dlRest, hw, hm]
  have hns : ∀ x ∈ name, x ≠ '/' := fun x hx h => hslash (h ▸ hx)
  cases v with
  | none =>
    have hf : dlFileName o name none (s% "so") = name ++ s% ".so" := by simp [dlFileName, hw, hm]
    rw [hf]
    obtain ⟨x0, hx0⟩ := so_mk_unv
    obtain ⟨m, hm'⟩ := matchRe_complete hx0
    refine parse_none (basename_noslash _ (noslash_app hns (by decide))) ?_ (so_cap_none hm')
    rw [hR]
    exact lazyMatch_split soRest _ (by decide) m hm' name (fun _ w _ hw' => so_none w [] hw')
  | some w =>
    obtain ⟨hpw, hbw⟩ := hplain w rfl
    have hV := vstr_vprint w hpw hbw
    have hf : dlFileName o name (some w) (s% "so") = name ++ ('.' :: 's' :: 'o' :: '.' :: vprint w) := by
      simp [dlFileName, hw, hm]
    rw [hf]
    obtain ⟨x0, hx0⟩ := so_mk_ver hV
    obtain ⟨m, hm'⟩ := matchRe_complete hx0
    refine parse_some (basename_noslash _ (noslash_app hns
      (noslash_app (a := ['.', 's', 'o', '.']) (by decide) hV.noslash))) ?_ (so_cap_ver hV hm')
      (List.cons_ne_nil _ _) ?_
    · rw [hR]
      exact lazyMatch_split soRest _ (by simp) m hm' name (fun _ w' _ hw' => so_none w' _ hw')
    · rw [stripChar_dot_cons, hV.strip]
      exact parse_vprint w hpw hbw

theorem mac_ok (name : Str) (v : Option VersionNumber) (hslash : '/' ∉ name)
    (hplain : ∀ w, v = some w → w.pre = [] ∧ w.build = [])
    (hamb : ¬ AmbiguousName (s% "macos") name v.isSome) :
    parseDlNameVersion (dlFileName (s% "macos") name v (s% "dylib")) (s% "macos") = .ok (name, v) := by
  have hmw : (s% "macos" == s% "windows") = false := by decide
  have hR : dlRest (s% "macos") = dylibRest := by simp [dlRest, hmw]
  have hns : ∀ x ∈ name, x ≠ '/' := fun x hx h => hslash (h ▸ hx)
  cases v with
  | none =>
    have hf : dlFileName (s% "macos") name none (s% "dylib") = name ++ s% ".dylib" := by
      simp [dlFileName, hmw]
    rw [hf]
    obtain ⟨x0, hx0⟩ := mac_mk_unv
    obtain ⟨m, hm⟩ := matchRe_complete hx0
    refine parse_none (basename_noslash _ (noslash_app hns (by decide))) ?_ (mac_cap_unv hm)
    rw [hR]
    exact lazyMatch_split dylibRest _ (by decide) m hm name
      (fun u w hu hw => mac_none_unv u w hw (by rw [← hu]; exact hamb))
  | some w =>
    obtain ⟨hpw, hbw⟩ := hplain w rfl
    have hV := vstr_vprint w hpw hbw
    have hf : dlFileName (s% "macos") name (some w) (s% "dylib") =
        name ++ '.' :: (vprint w ++ s% ".dylib") := by
      simp [dlFileName, hmw]
    rw [hf]
    obtain ⟨x0, hx0⟩ := mac_mk_ver hV
    obtain ⟨m, hm⟩ := matchRe_complete hx0
    refine parse_some (basename_noslash _ (noslash_app hns
      (noslash_app (a := ['.']) (by decide) (noslash_app hV.noslash (by decide))))) ?_
      (mac_cap_ver hV hm) (List.cons_ne_nil _ _) ?_
    · rw [hR]
      exact lazyMatch_split dylibRest _ (by simp) m hm name
        (fun u w' hu hw' => mac_none_ver u w' _ hw' hV (by rw [← hu]; exact hamb))
    · rw [stripChar_dot_cons, hV.strip]
      exact parse_vprint w hpw hbw

theorem win_ok (name : Str) (v : Option VersionNumber) (hslash : '/' ∉ name)
    (hplain : ∀ w, v = some w → w.pre = [] ∧ w.build = [])
    (hamb : ¬ AmbiguousName (s% "windows") name v.isSome) :
    parseDlNameVersion (dlFileName (s% "windows") name v (s% "dll")) (s% "windows") = .ok (name, v) := by
  have hR : dlRest (s% "windows") = dllRest := by simp [dlRest]
  have hns : ∀ x ∈ name, x ≠ '/' := fun x hx h => hslash (h ▸ hx)
  cases v with
  | none =>
    have hf : dlFileName (s% "windows") name none (s% "dll") = name ++ s% ".dll" := by
      simp [dlFileName]
    rw [hf]
    obtain ⟨x0, hx0⟩ := win_mk_unv
    obtain ⟨m, hm⟩ := matchRe_complete hx0
    refine parse_none (basename_noslash _ (noslash_app hns (by decide))) ?_ (win_cap_unv hm)
    rw [hR]
    exact lazyMatch_split dllRest _ (by decide) m hm name
      (fun u w hu hw => win_none_unv u w hw (by rw [← hu]; exact hamb))
  | some w =>
    obtain ⟨hpw, hbw⟩ := hplain w rfl
    have hV := vstr_vprint w hpw hbw
    have hf : dlFileName (s% "windows") name (some w) (s% "dll") =
        name ++ '-' :: (vprint w ++ s% ".dll") := by
      simp [dlFileName]
    rw [hf]
    obtain ⟨x0, hx0⟩ := win_mk_ver hV
    obtain ⟨m, hm⟩ := matchRe_complete hx0
    refine parse_some (basename_noslash _ (noslash_app hns
      (noslash_app (a := ['-']) (by decide) (noslash_app hV.noslash (by decide))))) ?_
      (win_cap_ver hV hm) hV.ne_nil ?_
    · rw [hR]
      exact lazyMatch_split dllRest _ (by simp) m hm name
        (fun _ w' _ hw' => win_none_ver w' _ hw')
    · rw [hV.strip]
      exact parse_vprint w hpw hbw

theorem dlNameInverse_proven : DlNameInverse := by
  intro p o name v hp hslash hplain hamb
  rw [platformDlext_eq p o hp]
  by_cases hw : o = s% "windows"
  · subst hw
    rw [if_pos rfl]
    exact win_ok name v hslash hplain hamb
  · by_cases hm : o = s% "macos"
    · subst hm
      rw [if_neg (by decide), if_pos rfl]
      exact mac_ok name v hslash hplain hamb
    · rw [if_neg hw, if_neg hm]
      exact so_ok o name v hw hm hslash hplain

end JuliaLean.Platforms
