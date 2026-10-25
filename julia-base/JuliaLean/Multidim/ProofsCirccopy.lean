import JuliaLean.Multidim.ProofsCirc

/-! Proof of `CirccopyNonempty`: on nonempty arrays of equal size, `circcopy!` succeeds
and puts at each destination index the source element congruent to it modulo the
size, in every dimension. -/

namespace JuliaLean.Multidim

theorem inAxes_cons' (p : Int × Int) (ax : List (Int × Int)) (j : Int) (J : List Int) :
    inAxes (p :: ax) (j :: J) = true ↔ (p.1 ≤ j ∧ j ≤ p.2) ∧ inAxes ax J = true := by
  obtain ⟨lo, hi⟩ := p; exact inAxes_cons lo hi ax j J

/-- One dimension of a `circcopy!` block: destination `pd` inside the destination axis
`ad`, source `ps` of the same length inside the source axis `as`, each destination index
mapped to the source index congruent to it modulo the length. -/
def DimOKc (ad as pd ps : Int × Int) : Prop :=
  pd.2 - pd.1 = ps.2 - ps.1 ∧ pd.1 - 1 ≤ pd.2 ∧ ad.1 ≤ pd.1 ∧ pd.2 ≤ ad.2 ∧ as.1 ≤ ps.1 ∧
    ps.2 ≤ as.2 ∧ -2 ^ 40 < ad.1 ∧ ad.2 < 2 ^ 40 ∧ -2 ^ 40 < as.1 ∧ as.2 < 2 ^ 40 ∧
    ∀ j, pd.1 ≤ j → j ≤ pd.2 → ps.1 + (j - pd.1) = as.1 + (j - as.1) % (as.2 - as.1 + 1)

def DimsOKc : List (Int × Int) → List (Int × Int) → List (Int × Int) → List (Int × Int) → Prop
  | ad :: ads, as :: ass, pd :: pds, ps :: pss => DimOKc ad as pd ps ∧ DimsOKc ads ass pds pss
  | [], [], [], [] => True
  | _, _, _, _ => False

/-- The documented value at `J`. -/
def ccF (axs : List (Int × Int)) (J : List Int) : List Int :=
  (J.zip axs).map fun (j, s) => s.1 + (j - s.1) % (s.2 - s.1 + 1)

theorem dimc_1 (fd ld fs ls s Q l : Int) (hl : ld - fd + 1 = l) (hl' : ls - fs + 1 = l)
    (hs0 : 0 ≤ s) (hs1 : s < l) (hQ : l * Q + s = fs - fd)
    (b1 : -2 ^ 40 < fd) (b2 : ld < 2 ^ 40) (b3 : -2 ^ 40 < fs) (b4 : ls < 2 ^ 40) :
    DimOKc (fd, ld) (fs, ls) (fd, fd + s - 1) (ls - s + 1, ls) := by
  refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
    by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
    by dsimp only; omega, by dsimp only; omega, ?_⟩
  dsimp only
  intro j h1 h2
  rw [hl', emod_of_eq (j - fs) (j - fd - s + l) l (-(Q + 1))
    (by rw [Int.mul_neg, Int.mul_add, Int.mul_one]; omega) (by omega) (by omega)]
  omega

theorem dimc_2 (fd ld fs ls s Q l : Int) (hl : ld - fd + 1 = l) (hl' : ls - fs + 1 = l)
    (hs0 : 0 ≤ s) (hs1 : s < l) (hQ : l * Q + s = fs - fd)
    (b1 : -2 ^ 40 < fd) (b2 : ld < 2 ^ 40) (b3 : -2 ^ 40 < fs) (b4 : ls < 2 ^ 40) :
    DimOKc (fd, ld) (fs, ls) (fd + s, ld) (fs, ls - s) := by
  refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
    by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
    by dsimp only; omega, by dsimp only; omega, ?_⟩
  dsimp only
  intro j h1 h2
  rw [hl', emod_of_eq (j - fs) (j - fd - s) l (-Q) (by rw [Int.mul_neg]; omega) (by omega) (by omega)]
  omega

/-- `circcopyBlocks` succeeds on nonempty axes of equal lengths; its blocks satisfy
`DimsOKc` and cover the destination axes. -/
theorem ccBlocks_spec : ∀ (axd axs : List (Int × Int)),
    (∀ p ∈ axd, p.1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    (∀ p ∈ axs, p.1 ≤ p.2 ∧ -2 ^ 40 < p.1 ∧ p.2 < 2 ^ 40) →
    axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
    ∃ blocks, circcopyBlocks axd axs = .ok blocks ∧ (∀ b ∈ blocks, DimsOKc axd axs b.1 b.2) ∧
      ∀ J, inAxes axd J = true → ∃ b ∈ blocks, InBlock b.1 J := by
  intro axd
  induction axd with
  | nil =>
    intro axs _ _ hlen
    cases axs with
    | cons _ _ => simp at hlen
    | nil =>
      refine ⟨[([], [])], rfl, fun b hb => ?_, fun J hJ => ?_⟩
      · simp at hb; subst hb; simp [DimsOKc]
      · cases J with
        | nil => exact ⟨([], []), by simp, by simp [InBlock]⟩
        | cons j J => simp [inAxes_nil_cons] at hJ
  | cons ad ads ih =>
    intro axs hd hs hlen
    cases axs with
    | nil => simp at hlen
    | cons as ass =>
      obtain ⟨fd, ld⟩ := ad
      obtain ⟨fs, ls⟩ := as
      simp only [List.map_cons, List.cons.injEq] at hlen
      obtain ⟨hl1, hlen'⟩ := hlen
      obtain ⟨hd1, hd2, hd3⟩ := hd (fd, ld) (by simp)
      obtain ⟨hs1', hs2, hs3⟩ := hs (fs, ls) (by simp)
      obtain ⟨rest, hrest, hok, hcov⟩ := ih ass (fun p hp => hd p (by simp [hp]))
        (fun p hp => hs p (by simp [hp])) hlen'
      have hl0 : ¬ (ld - fd + 1 = 0) := by omega
      have hpos : (0 : Int) < ld - fd + 1 := by omega
      have hs0 : 0 ≤ (fs - fd) % (ld - fd + 1) := Int.emod_nonneg _ (by omega)
      have hsl : (fs - fd) % (ld - fd + 1) < ld - fd + 1 := Int.emod_lt_of_pos _ hpos
      have hQ := Int.mul_ediv_add_emod (fs - fd) (ld - fd + 1)
      refine ⟨rest.map (fun b => ((fd, fd + (fs - fd) % (ld - fd + 1) - 1) :: b.1,
          (ls - (fs - fd) % (ld - fd + 1) + 1, ls) :: b.2)) ++
        rest.map (fun b => ((fd + (fs - fd) % (ld - fd + 1), ld) :: b.1,
          (fs, ls - (fs - fd) % (ld - fd + 1)) :: b.2)), ?_, ?_, ?_⟩
      · simp [circcopyBlocks, hl0, hrest]; rfl
      · intro b hb
        simp only [List.mem_append, List.mem_map] at hb
        rcases hb with ⟨b', hb', rfl⟩ | ⟨b', hb', rfl⟩
        · exact ⟨dimc_1 fd ld fs ls _ _ _ rfl (by omega) hs0 hsl hQ hd2 hd3 hs2 hs3, hok b' hb'⟩
        · exact ⟨dimc_2 fd ld fs ls _ _ _ rfl (by omega) hs0 hsl hQ hd2 hd3 hs2 hs3, hok b' hb'⟩
      · intro J hJ
        cases J with
        | nil => simp [inAxes_cons_nil] at hJ
        | cons j J =>
          rw [inAxes_cons] at hJ
          obtain ⟨⟨hj1, hj2⟩, hJ'⟩ := hJ
          obtain ⟨b', hb', hin⟩ := hcov J hJ'
          simp only [List.mem_append, List.mem_map]
          by_cases hj : j ≤ fd + (fs - fd) % (ld - fd + 1) - 1
          · exact ⟨_, Or.inl ⟨b', hb', rfl⟩, by simp only [InBlock]; exact ⟨by omega, by omega, hin⟩⟩
          · exact ⟨_, Or.inr ⟨b', hb', rfl⟩, by simp only [InBlock]; exact ⟨by omega, by omega, hin⟩⟩

theorem lens_eq_c : ∀ (axd axs pds pss : List (Int × Int)), DimsOKc axd axs pds pss →
    (pds.map fun p => unitRng p.1 p.2).map (·.len) = (pss.map fun p => unitRng p.1 p.2).map (·.len) := by
  intro axd
  induction axd with
  | nil =>
    intro axs pds pss hok
    rcases axs with _ | ⟨as, ass⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp [DimsOKc] at hok ⊢
  | cons ad ads ih =>
    intro axs pds pss hok
    rcases axs with _ | ⟨as, ass⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp only [DimsOKc] at hok
    obtain ⟨⟨hdiff, -⟩, hrest⟩ := hok
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih ass pds pss hrest⟩
    rw [unitRng_len, unitRng_len, hdiff]

theorem corners_c : ∀ (axd axs pds pss : List (Int × Int)), DimsOKc axd axs pds pss →
    (∀ p ∈ pds, p.1 ≤ p.2) →
    inAxes axd ((pds.map fun p => unitRng p.1 p.2).map (·.start.val)) = true ∧
    inAxes axd ((pds.map fun p => unitRng p.1 p.2).map (·.last.val)) = true ∧
    inAxes axs ((pss.map fun p => unitRng p.1 p.2).map (·.start.val)) = true ∧
    inAxes axs ((pss.map fun p => unitRng p.1 p.2).map (·.last.val)) = true := by
  intro axd
  induction axd with
  | nil =>
    intro axs pds pss hok _
    rcases axs with _ | ⟨as, ass⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp [DimsOKc] at hok ⊢
    simp [inAxes]
  | cons ad ads ih =>
    intro axs pds pss hok hne
    rcases axs with _ | ⟨as, ass⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp only [DimsOKc] at hok
    obtain ⟨⟨hdiff, hle, h1, h2, h3, h4, b1, b2, b3, b4, -⟩, hrest⟩ := hok
    have hpd : pd.1 ≤ pd.2 := hne pd (by simp)
    obtain ⟨c1, c2, c3, c4⟩ := ih ass pds pss hrest (fun p hp => hne p (by simp [hp]))
    simp only [List.map_cons, inAxes_cons']
    rw [unitRng_start pd.1 pd.2 (by omega) (by omega), unitRng_last pd.1 pd.2 (by omega) hpd (by omega),
      unitRng_start ps.1 ps.2 (by omega) (by omega), unitRng_last ps.1 ps.2 (by omega) (by omega) (by omega)]
    exact ⟨⟨by omega, c1⟩, ⟨by omega, c2⟩, ⟨by omega, c3⟩, ⟨by omega, c4⟩⟩

theorem cover_value_c : ∀ (axd axs pds pss : List (Int × Int)), DimsOKc axd axs pds pss →
    ∀ (J : List Int) (ks : List Nat),
    ((pds.map fun p => unitRng p.1 p.2).zip J).mapM (fun (r, j) => r.pos j) = some ks →
    ((pss.map fun p => unitRng p.1 p.2).zip ks).map (fun (r, k) => r.elem k) = ccF axs J := by
  intro axd
  induction axd with
  | nil =>
    intro axs pds pss hok J ks _
    rcases axs with _ | ⟨as, ass⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp [DimsOKc] at hok ⊢
    simp [ccF]
  | cons ad ads ih =>
    intro axs pds pss hok J ks hm
    rcases axs with _ | ⟨as, ass⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp only [DimsOKc] at hok
    obtain ⟨⟨hdiff, hle, h1, h2, h3, h4, b1, b2, b3, b4, hcov⟩, hrest⟩ := hok
    cases J with
    | nil =>
      simp at hm; subst hm; simp [ccF]
    | cons j J =>
      simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons] at hm
      rw [unitRng_pos pd.1 pd.2 j (by omega) (by omega)] at hm
      by_cases hj : pd.1 ≤ j ∧ j ≤ pd.2
      · rw [if_pos hj] at hm
        cases hm' : ((pds.map fun p => unitRng p.1 p.2).zip J).mapM (fun (r, j) => r.pos j) with
        | none => simp [hm'] at hm
        | some ks' =>
          simp [hm'] at hm
          subst hm
          have := ih ass pds pss hrest J ks' hm'
          simp only [ccF] at this ⊢
          simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
          refine ⟨?_, this⟩
          rw [unitRng_elem ps.1 ps.2 _ (by omega) (by omega)]
          have := hcov j hj.1 hj.2
          omega
      · rw [if_neg hj] at hm
        simp at hm

theorem cover_some_c : ∀ (axd axs pds pss : List (Int × Int)), DimsOKc axd axs pds pss →
    ∀ J : List Int, InBlock pds J →
    ∃ ks, ((pds.map fun p => unitRng p.1 p.2).zip J).mapM (fun (r, j) => r.pos j) = some ks := by
  intro axd
  induction axd with
  | nil =>
    intro axs pds pss hok J hin
    rcases axs with _ | ⟨as, ass⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp [DimsOKc] at hok ⊢
  | cons ad ads ih =>
    intro axs pds pss hok J hin
    rcases axs with _ | ⟨as, ass⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp only [DimsOKc] at hok
    obtain ⟨⟨hdiff, hle, h1, h2, h3, h4, b1, b2, b3, b4, -⟩, hrest⟩ := hok
    cases J with
    | nil => simp [InBlock] at hin
    | cons j J =>
      obtain ⟨hj1, hj2, hin'⟩ := hin
      obtain ⟨ks', hks'⟩ := ih ass pds pss hrest J hin'
      have hp := unitRng_pos pd.1 pd.2 j (by omega) (by omega)
      rw [if_pos ⟨hj1, hj2⟩] at hp
      exact ⟨(j - pd.1).toNat :: ks', by simp [List.mapM_cons, hp, hks']⟩

theorem block_step_c {α : Type} (axd axs pds pss : List (Int × Int)) (hok : DimsOKc axd axs pds pss)
    (dest : List Int → Option α) (src : List Int → α) :
    ∃ dest', copytoCI axd dest (pds.map fun p => unitRng p.1 p.2) axs src
        (pss.map fun p => unitRng p.1 p.2) = .ok dest' ∧
      ∀ J, (dest' J = dest J ∨ dest' J = some (src (ccF axs J))) ∧
        (InBlock pds J → dest' J = some (src (ccF axs J))) := by
  unfold copytoCI
  by_cases he : (pds.map fun p => unitRng p.1 p.2).any (·.len == 0) = true
  · rw [if_pos he]
    refine ⟨dest, rfl, fun J => ⟨Or.inl rfl, fun hJ => ?_⟩⟩
    exfalso
    obtain ⟨r, hr, h0⟩ := List.any_eq_true.mp he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have := inBlock_le pds J hJ p hp
    simp [unitRng] at h0
    omega
  · rw [if_neg he]
    have hne : ∀ p ∈ pds, p.1 ≤ p.2 := by
      intro p hp
      refine Classical.byContradiction fun hlt => he (List.any_eq_true.mpr ⟨_, List.mem_map_of_mem hp, ?_⟩)
      simp [unitRng]
      omega
    rw [if_neg (fun h => h (lens_eq_c axd axs pds pss hok))]
    obtain ⟨c1, c2, c3, c4⟩ := corners_c axd axs pds pss hok hne
    rw [c1, c2, c3, c4, if_neg (by decide)]
    refine ⟨_, rfl, fun J => ?_⟩
    dsimp only
    constructor
    · split
      · next ks hks =>
        split
        · exact Or.inr (congrArg (fun x => some (src x)) (cover_value_c axd axs pds pss hok J ks hks))
        · exact Or.inl rfl
      · exact Or.inl rfl
    · intro hJ
      obtain ⟨ks, hks⟩ := cover_some_c axd axs pds pss hok J hJ
      have hlen : J.length = (pds.map fun p => unitRng p.1 p.2).length := by
        rw [List.length_map]; exact inBlock_length pds J hJ
      split
      · next ks' hks' =>
        rw [if_pos hlen]
        exact congrArg (fun x => some (src x)) (cover_value_c axd axs pds pss hok J ks' hks')
      · next h => rw [hks] at h; cases h

/-- The all-zero-shift shortcut agrees with the formula. -/
theorem shortcut_eq : ∀ (axd axs : List (Int × Int)) (J : List Int),
    (∀ p ∈ axd, p.1 ≤ p.2) →
    (axs.zip axd).all (fun (s, d) => s.1 - d.1 = 0) = true →
    axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
    inAxes axd J = true →
    (J.zip (axs.zip axd)).map (fun (j, s, d) => j - d.1 + s.1) = ccF axs J := by
  intro axd
  induction axd with
  | nil =>
    intro axs J _ _ hlen _
    cases axs with
    | nil => simp [ccF]
    | cons _ _ => simp at hlen
  | cons ad ads ih =>
    intro axs J hd hall hlen hJ
    cases axs with
    | nil => simp at hlen
    | cons as ass =>
      cases J with
      | nil => simp [inAxes_cons_nil] at hJ
      | cons j J =>
        rw [inAxes_cons'] at hJ
        obtain ⟨⟨hj1, hj2⟩, hJ'⟩ := hJ
        simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
        simp only [List.map_cons, List.cons.injEq] at hlen
        have := ih ass J (fun p hp => hd p (by simp [hp])) hall.2 hlen.2 hJ'
        simp only [ccF] at this ⊢
        simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
        refine ⟨?_, this⟩
        have h0 := hall.1
        have h1 := hlen.1
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        omega

theorem circcopyNonempty : CirccopyNonempty := by
  intro axd axs dest src hd hs hlen
  unfold circcopy
  rw [if_neg (fun h => h hlen.symm)]
  by_cases hall : (axs.zip axd).all (fun (s, d) => s.1 - d.1 = 0) = true
  · rw [if_pos hall]
    refine ⟨_, rfl, fun J hJ => ?_⟩
    dsimp only
    rw [if_pos hJ]
    exact congrArg (fun x => some (src x))
      (shortcut_eq axd axs J (fun p hp => (hd p hp).1) hall hlen hJ)
  · rw [if_neg hall]
    obtain ⟨blocks, hbl, hok, hcov⟩ := ccBlocks_spec axd axs hd hs hlen
    rw [hbl]
    obtain ⟨d', hrun, hJ⟩ := runBlocks_spec axd axs src (fun J => some (src (ccF axs J)))
      (fun b J => InBlock b.1 J) blocks
      (fun b hb dest => block_step_c axd axs b.1 b.2 (hok b hb) dest src) dest
    exact ⟨d', hrun, fun J hJin => (hJ J).2 (hcov J hJin)⟩

end JuliaLean.Multidim
