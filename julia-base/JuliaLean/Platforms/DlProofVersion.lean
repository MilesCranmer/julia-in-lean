import JuliaLean.Platforms.DlProofRegex
import JuliaLean.VersionNumbers.Next
import JuliaLean.VersionNumbers.Order

/-!
# `parse(VersionNumber, string(v)) == v` for versions without annotations

`showNat` digits, `parseUnsigned` on them, and the match of `VERSION_REGEX` on
`M.m.p`.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (Re Caps matchRe capture VersionNumber vprint showNat tryparse
  versionRe parseUnsigned digitsValue veq typemaxV isUcpDigit isLetterCI isAlnumHyCI newVersion_plain
  eqStructural_proven umax u32_nonneg u32_le)
open JuliaLean.VersionNumbers.Re

/-! ## Digits -/

/-- A decimal digit as printed by `showNat`. -/
def IsDig (x : Char) : Prop := ∃ d : Fin 10, x = Nat.digitChar d.val

theorem IsDig.ascii {x : Char} (h : IsDig x) : isAsciiDigit x = true := by
  obtain ⟨d, rfl⟩ := h; revert d; decide +kernel

theorem IsDig.vascii {x : Char} (h : IsDig x) : VersionNumbers.isAsciiDigit x = true := by
  obtain ⟨d, rfl⟩ := h; revert d; decide +kernel

theorem IsDig.ucp {x : Char} (h : IsDig x) : isUcpDigit x = true := by
  obtain ⟨d, rfl⟩ := h; revert d; decide +kernel

theorem IsDig.alpha {x : Char} (h : IsDig x) : isAsciiAlpha x = false := by
  obtain ⟨d, rfl⟩ := h; revert d; decide +kernel

theorem IsDig.ne {x : Char} (h : IsDig x) :
    x ≠ '.' ∧ x ≠ '\n' ∧ x ≠ '-' ∧ x ≠ '+' ∧ x ≠ '/' ∧ x ≠ '∞' ∧ x ≠ 'v' ∧ x ≠ 'V' := by
  obtain ⟨d, rfl⟩ := h; revert d; decide +kernel

theorem IsDig.not_tail {x : Char} (h : IsDig x) : ¬ (x = '-' ∨ x = '+' ∨ isLetterCI x = true) := by
  obtain ⟨d, rfl⟩ := h; revert d; decide +kernel

theorem showNat_dig (n : Nat) : ∀ x ∈ showNat n, IsDig x := by
  intro x hx
  unfold showNat at hx
  rw [Nat.toDigits_eq_ite (by decide)] at hx
  split at hx
  · rename_i h
    simp only [List.mem_singleton] at hx
    exact ⟨⟨n, h⟩, hx⟩
  · rename_i h
    rcases List.mem_append.1 hx with hx | hx
    · exact showNat_dig (n / 10) x hx
    · simp only [List.mem_singleton] at hx
      exact ⟨⟨n % 10, Nat.mod_lt _ (by decide)⟩, hx⟩
termination_by n
decreasing_by omega

theorem showNat_ne_nil (n : Nat) : showNat n ≠ [] := Nat.toDigits_ne_nil

theorem digitsValue_snoc (l : List Char) {d : Nat} (h : d < 10) :
    digitsValue (l ++ [Nat.digitChar d]) = 10 * digitsValue l + d := by
  have h1 : (Nat.digitChar d).val.toNat = 48 + d := Nat.toNat_digitChar_of_lt_ten h
  have h2 : ('0' : Char).val.toNat = 48 := rfl
  simp only [digitsValue, List.foldl_append, List.foldl_cons, List.foldl_nil, h1, h2]
  omega

theorem digitsValue_showNat (n : Nat) : digitsValue (showNat n) = n := by
  unfold showNat
  rw [Nat.toDigits_eq_ite (by decide)]
  split
  · rename_i h
    rw [show [Nat.digitChar n] = [] ++ [Nat.digitChar n] from rfl, digitsValue_snoc [] h]
    simp [digitsValue]
  · rename_i h
    rw [digitsValue_snoc _ (Nat.mod_lt _ (by decide))]
    have := digitsValue_showNat (n / 10)
    unfold showNat at this
    rw [this]
    omega
termination_by n
decreasing_by omega

theorem takeWhile_all {p : Char → Bool} : ∀ (l : List Char), (∀ x ∈ l, p x = true) → l.takeWhile p = l
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.takeWhile, h x (by simp), takeWhile_all l (fun y hy => h y (by simp [hy]))]

theorem parseUnsigned_showNat (x : JInt .u32) : parseUnsigned .u32 (showNat x.val.toNat) = .ok x := by
  have hall : ∀ y ∈ showNat x.val.toNat, VersionNumbers.isAsciiDigit y = true :=
    fun y hy => (showNat_dig _ y hy).vascii
  have hne := showNat_ne_nil x.val.toNat
  have h0 := u32_nonneg x
  have h1 := u32_le x
  have hI : ((x.val.toNat : Nat) : Int) = x.val := Int.toNat_of_nonneg h0
  have hE : (showNat x.val.toNat).isEmpty = false := by
    cases h : showNat x.val.toNat with
    | nil => exact absurd h hne
    | cons _ _ => rfl
  simp only [parseUnsigned]
  rw [takeWhile_all _ hall, digitsValue_showNat, if_neg (by simp [hE]),
    if_neg (fun h => absurd h.2 (by rw [hI]; have := umax; omega)), if_neg (Nat.lt_irrefl _)]
  unfold JInt.convert
  rw [dif_pos (by rw [hI]; exact x.property)]
  exact congrArg Except.ok (Subtype.ext hI)

theorem vprint_plain (w : VersionNumber) (hp : w.pre = []) (hb : w.build = []) :
    vprint w = showNat w.major.val.toNat ++ '.' :: (showNat w.minor.val.toNat ++ '.' :: showNat w.patch.val.toNat) := by
  have hne : veq w typemaxV = false := by
    cases h : veq w typemaxV
    · rfl
    · have := (eqStructural_proven w typemaxV).1 h
      rw [this] at hb
      exact absurd hb (by simp [typemaxV])
  simp [vprint, hne, hp, hb]
  rfl

/-! ## `VERSION_REGEX` on `M.m.p` -/

/-- The part of `VERSION_REGEX` after the patch number. -/
def vTail : Re :=
  let an := cls isAlnumHyCI
  alt (group 4 (chr '-'))
    (seq
      (opt (group 5 (alt
        (seqs [cls isLetterCI, star an, star (seq (chr '.') (plus an))])
        (seqs [chr '-', star (seq (plus an) (chr '.')), plus an]))))
      (alt (group 6 (chr '+'))
        (opt (seq (chr '+') (group 7 (seq (star (seq (plus an) (chr '.'))) (plus an)))))))

theorem versionRe_eq : versionRe = seq (opt (cls (fun c => c == 'v' || c == 'V')))
    (seq (group 1 (plus (cls isUcpDigit)))
    (seq (opt (seq (chr '.') (group 2 (plus (cls isUcpDigit)))))
    (seq (opt (seq (chr '.') (group 3 (plus (cls isUcpDigit))))) (seq vTail eol)))) := rfl

theorem vTail_inv {s : List Char} {c : Caps} {s' : List Char} {c' : Caps} (h : Mt vTail s c s' c') :
    (s' = s ∧ c' = c) ∨ ∃ y t, s = y :: t ∧ (y = '-' ∨ y = '+' ∨ isLetterCI y = true) := by
  rcases Mt_alt_inv h with h | h
  · obtain ⟨c1, h, -⟩ := Mt_group_inv h
    obtain ⟨rfl, -⟩ := Mt_chr_inv h
    exact .inr ⟨_, _, rfl, .inl rfl⟩
  · obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h
    rcases Mt_opt_inv h1 with h1 | ⟨rfl, rfl⟩
    · obtain ⟨c2, h1, -⟩ := Mt_group_inv h1
      rcases Mt_alt_inv h1 with h1 | h1
      · obtain ⟨s3, c3, h3, -⟩ := Mt_seq_inv h1
        obtain ⟨y, rfl, hy, -⟩ := Mt_cls_inv h3
        exact .inr ⟨_, _, rfl, .inr (.inr hy)⟩
      · obtain ⟨s3, c3, h3, -⟩ := Mt_seq_inv h1
        obtain ⟨rfl, -⟩ := Mt_chr_inv h3
        exact .inr ⟨_, _, rfl, .inl rfl⟩
    · rcases Mt_alt_inv h2 with h2 | h2
      · obtain ⟨c2, h2, -⟩ := Mt_group_inv h2
        obtain ⟨rfl, -⟩ := Mt_chr_inv h2
        exact .inr ⟨_, _, rfl, .inr (.inl rfl)⟩
      · rcases Mt_opt_inv h2 with h2 | ⟨rfl, rfl⟩
        · obtain ⟨s3, c3, h3, -⟩ := Mt_seq_inv h2
          obtain ⟨rfl, -⟩ := Mt_chr_inv h3
          exact .inr ⟨_, _, rfl, .inr (.inl rfl)⟩
        · exact .inl ⟨rfl, rfl⟩

theorem vTail_mk (c : Caps) : Mt vTail [] c [] c := .altR (.seq (.altR .eps) (.altR (.altR .eps)))

theorem dotopt_inv {i : Nat} {s : List Char} {c : Caps} {s' : List Char} {c' : Caps}
    (h : Mt (opt (seq (chr '.') (group i (plus (cls isUcpDigit))))) s c s' c') :
    (s' = s ∧ c' = c) ∨
      ∃ U, s = '.' :: (U ++ s') ∧ U ≠ [] ∧ (∀ y ∈ U, isUcpDigit y = true) ∧ c' = (i, U) :: c := by
  rcases Mt_opt_inv h with h0 | h0
  · obtain ⟨s1, c1, h1, h2⟩ := Mt_seq_inv h0
    obtain ⟨hs, hc⟩ := Mt_chr_inv h1
    obtain ⟨c2, h3, hc'⟩ := Mt_group_inv h2
    obtain ⟨hc2, U, hs1, hne, hU⟩ := Mt_plus_cls h3
    subst hs hs1 hc'
    refine .inr ⟨U, rfl, hne, hU, ?_⟩
    rw [take_cap, hc2, hc]
  · exact .inl h0

theorem Mt_plus_cls_all {p : Char → Bool} (u : List Char) (c : Caps) (hne : u ≠ [])
    (hu : ∀ x ∈ u, p x = true) : Mt (plus (.cls p)) u c [] c := by
  simpa using Mt_plus_cls_mk u [] c hne hu

theorem ucp_nodot {U : List Char} (h : ∀ y ∈ U, isUcpDigit y = true) : ∀ y ∈ U, y ≠ '.' := by
  intro y hy hd
  have := h y hy
  rw [hd] at this
  exact absurd this (by decide +kernel)

theorem dig_nodot {U : List Char} (h : ∀ y ∈ U, IsDig y) : ∀ y ∈ U, y ≠ '.' :=
  fun y hy => (h y hy).ne.1

theorem vre_inv {A B C : List Char} (hA : ∀ y ∈ A, IsDig y) (hB : ∀ y ∈ B, IsDig y)
    (hC : ∀ y ∈ C, IsDig y) {s s' : List Char} {x : Caps} (hs : s = A ++ '.' :: (B ++ '.' :: C))
    (h : Mt versionRe s [] s' x) : x = [(3, C), (2, B), (1, A)] := by
  have hv : ∀ y ∈ s, y = '.' ∨ IsDig y := by
    intro y hy
    rw [hs] at hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | hy | hy | hy | hy
    · exact .inr (hA y hy)
    · exact .inl hy
    · exact .inr (hB y hy)
    · exact .inl hy
    · exact .inr (hC y hy)
  rw [versionRe_eq] at h
  obtain ⟨s1, c1, hO1, hR1⟩ := Mt_seq_inv h
  have hs1 : s1 = s ∧ c1 = [] := by
    rcases Mt_opt_inv hO1 with hO | hO
    · exfalso
      obtain ⟨y, hy1, hy, -⟩ := Mt_cls_inv hO
      simp only [Bool.or_eq_true, beq_iff_eq] at hy
      rcases hv y (by rw [hy1]; simp) with hy' | hd
      · rw [hy'] at hy
        rcases hy with hy | hy <;> exact absurd hy (by decide)
      · rcases hy with hy | hy
        · exact hd.ne.2.2.2.2.2.2.1 hy
        · exact hd.ne.2.2.2.2.2.2.2 hy
    · exact hO
  obtain ⟨hs1, hc1⟩ := hs1
  subst hs1 hc1
  obtain ⟨s2, c2, hG1, hR2⟩ := Mt_seq_inv hR1
  obtain ⟨c0, hP1, hc2⟩ := Mt_group_inv hG1
  obtain ⟨hc0, U1, hU1, -, hU1d⟩ := Mt_plus_cls hP1
  obtain ⟨s3, c3, hO2, hR3⟩ := Mt_seq_inv hR2
  obtain ⟨s4, c4, hO3, hR4⟩ := Mt_seq_inv hR3
  obtain ⟨s5, c5, hT, hE⟩ := Mt_seq_inv hR4
  obtain ⟨he5, hc5, hs5⟩ := Mt_eol_inv hE
  obtain ⟨u3, hu3⟩ := hO2.suffix
  obtain ⟨u4, hu4⟩ := hO3.suffix
  have hv4 : ∀ y ∈ s4, y = '.' ∨ IsDig y := fun y hy => hv y (by rw [hU1, hu3, hu4]; simp [hy])
  have hs4 : s4 = [] ∧ c5 = c4 := by
    rcases vTail_inv hT with ⟨he4, hc4⟩ | ⟨y, t, hyt, hy⟩
    · refine ⟨?_, hc4⟩
      rw [he4] at hs5
      rcases hs5 with h0 | h0
      · exact h0
      · exfalso
        rcases hv4 '\n' (by simp [h0]) with h0 | h0
        · exact absurd h0 (by decide)
        · exact h0.ne.2.1 rfl
    · exfalso
      rcases hv4 y (by simp [hyt]) with hy' | hd
      · rw [hy'] at hy
        revert hy
        decide
      · exact hd.not_tail hy
  obtain ⟨hs4, hc4⟩ := hs4
  rw [hc5, hc4]
  subst hs4 hc2 hc0
  have hAd := dig_nodot hA
  have hBd := dig_nodot hB
  have hU1n := ucp_nodot hU1d
  rw [hs] at hU1
  rcases dotopt_inv hO2 with ⟨he2, -⟩ | ⟨U2, hs2, -, hU2d, hc3⟩ <;>
    rcases dotopt_inv hO3 with ⟨he3, -⟩ | ⟨U3, hs3, -, hU3d, hc4'⟩
  · exfalso
    subst he3 he2
    have hd : '.' ∈ U1 := by rw [← List.append_nil U1, ← hU1]; simp
    exact hU1n _ hd rfl
  · exfalso
    subst hs3 he2
    obtain ⟨-, h2⟩ := dot_unique _ _ _ _ hU1 hAd hU1n
    have hd : '.' ∈ U3 := by simp only [List.append_nil] at h2; rw [← h2]; simp
    exact ucp_nodot hU3d _ hd rfl
  · exfalso
    subst he3 hs2
    obtain ⟨-, h2⟩ := dot_unique _ _ _ _ hU1 hAd hU1n
    have hd : '.' ∈ U2 := by simp only [List.append_nil] at h2; rw [← h2]; simp
    exact ucp_nodot hU2d _ hd rfl
  · subst hs3 hs2
    rw [hc4', hc3]
    obtain ⟨hAU, h2⟩ := dot_unique _ _ _ _ hU1 hAd hU1n
    simp only [List.append_nil] at h2
    obtain ⟨hBU, hCU⟩ := dot_unique _ _ _ _ h2 hBd (ucp_nodot hU2d)
    rw [hs, hBU, hCU]
    try simp only [List.append_nil]
    rw [take_cap]

theorem vre_mk {A B C : List Char} (hA : A ≠ []) (hB : B ≠ []) (hC : C ≠ [])
    (hAd : ∀ y ∈ A, IsDig y) (hBd : ∀ y ∈ B, IsDig y) (hCd : ∀ y ∈ C, IsDig y) :
    ∃ x, Mt versionRe (A ++ '.' :: (B ++ '.' :: C)) [] [] x := by
  rw [versionRe_eq]
  exact ⟨_, .seq (.altR .eps) (.seq (.group (Mt_plus_cls_mk A _ [] hA (fun y hy => (hAd y hy).ucp)))
    (.seq (.altL (.seq (Mt_chr_mk '.' _ _) (.group (Mt_plus_cls_mk B _ _ hB (fun y hy => (hBd y hy).ucp)))))
    (.seq (.altL (.seq (Mt_chr_mk '.' _ _) (.group (Mt_plus_cls_all C _ hC (fun y hy => (hCd y hy).ucp)))))
    (.seq (vTail_mk _) (.eol (.inl rfl))))))⟩

/-- `parse(VersionNumber, string(v)) == v` when `v` has no pre-release or build part. -/
theorem parse_vprint (w : VersionNumber) (hp : w.pre = []) (hb : w.build = []) :
    VersionNumbers.parse (vprint w) = .ok w := by
  rw [vprint_plain w hp hb]
  obtain ⟨M, m, P, pre, bld⟩ := w
  simp only at hp hb
  subst hp hb
  simp only
  have dA := showNat_dig M.val.toNat
  have dB := showNat_dig m.val.toNat
  have dC := showNat_dig P.val.toNat
  obtain ⟨x0, hx0⟩ := vre_mk (showNat_ne_nil _) (showNat_ne_nil _) (showNat_ne_nil _) dA dB dC
  obtain ⟨x, hx⟩ := matchRe_complete hx0
  obtain ⟨s', hs'⟩ := matchRe_sound hx
  have := vre_inv dA dB dC rfl hs'
  subst this
  have hinf : (showNat M.val.toNat ++ '.' :: (showNat m.val.toNat ++ '.' :: showNat P.val.toNat)
      == ['∞']) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg List.length h
    simp at this
    omega
  simp [VersionNumbers.parse, tryparse, hinf, hx, capture, parseUnsigned_showNat, newVersion_plain,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

end JuliaLean.Platforms
