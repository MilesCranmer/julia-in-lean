import JuliaLean.Multidim.Props

/-! Proof of `CircshiftFormula`: every `copyto!` call of `circshift` succeeds and the
result at each index is the source at the documented `mod` position. -/

namespace JuliaLean.Multidim

/-! ## Unit ranges with small endpoints -/

theorem i64_val (x : Int) (h1 : -2 ^ 62 ≤ x) (h2 : x ≤ 2 ^ 62) : (i64 x).val = x :=
  wrapInt_of_inRange .i64 x (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

theorem unitRng_start (lo hi : Int) (h1 : -2 ^ 62 ≤ lo) (h2 : lo ≤ 2 ^ 62) :
    (unitRng lo hi).start.val = lo := i64_val lo h1 h2

theorem unitRng_step (lo hi : Int) : (unitRng lo hi).step.val = 1 := i64_val 1 (by omega) (by omega)

theorem unitRng_len (lo hi : Int) : (unitRng lo hi).len = (hi - lo + 1).toNat := rfl

theorem unitRng_elem (lo hi k : Int) (h1 : -2 ^ 62 ≤ lo) (h2 : lo ≤ 2 ^ 62) :
    (unitRng lo hi).elem k = lo + k := by
  unfold Rng.elem; rw [unitRng_start lo hi h1 h2, unitRng_step, Int.mul_one]

theorem unitRng_last (lo hi : Int) (h1 : -2 ^ 62 ≤ lo) (h2 : lo ≤ hi) (h3 : hi ≤ 2 ^ 62) :
    (unitRng lo hi).last.val = hi := by
  unfold Rng.last
  rw [unitRng_elem lo hi _ h1 (by omega), unitRng_len]
  show wrapInt .i64 _ = hi
  rw [wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
  omega

theorem unitRng_pos (lo hi x : Int) (h1 : -2 ^ 62 ≤ lo) (h2 : lo ≤ 2 ^ 62) :
    (unitRng lo hi).pos x = if lo ≤ x ∧ x ≤ hi then some (x - lo).toNat else none := by
  unfold Rng.pos
  rw [unitRng_start lo hi h1 h2, unitRng_step, unitRng_len]
  by_cases h : lo ≤ x ∧ x ≤ hi
  · have hc : (1 : Int) ≠ 0 ∧ (x - lo) % 1 = 0 ∧ 0 ≤ (x - lo) / 1 ∧
        (x - lo) / 1 < ((hi - lo + 1).toNat : Int) := by
      simp only [Int.emod_one, Int.ediv_one, true_and]; omega
    rw [if_pos hc, if_pos h, Int.ediv_one]
  · have hc : ¬ ((1 : Int) ≠ 0 ∧ (x - lo) % 1 = 0 ∧ 0 ≤ (x - lo) / 1 ∧
        (x - lo) / 1 < ((hi - lo + 1).toNat : Int)) := by
      simp only [Int.emod_one, Int.ediv_one, true_and]; omega
    rw [if_neg hc, if_neg h]

/-! ## `inAxes` on lists -/

theorem inAxes_cons (lo hi : Int) (ax : List (Int × Int)) (j : Int) (J : List Int) :
    inAxes ((lo, hi) :: ax) (j :: J) = true ↔ (lo ≤ j ∧ j ≤ hi) ∧ inAxes ax J = true := by
  simp only [inAxes, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, Nat.add_right_cancel_iff]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩⟩

theorem inAxes_nil_cons (j : Int) (J : List Int) : inAxes [] (j :: J) = false := by
  simp [inAxes]

theorem inAxes_cons_nil (p : Int × Int) (ax : List (Int × Int)) : inAxes (p :: ax) [] = false := by
  simp [inAxes]

theorem oneAxes_cons (n : Nat) (ns : List Nat) : oneAxes (n :: ns) = ((1 : Int), (n : Int)) :: oneAxes ns :=
  rfl

/-! ## Blocks as products of per-dimension choices -/

/-- One dimension of a block: destination `pd` and source `ps` have equal lengths, lie
in `1:n`, and map each destination index to the `mod` formula. -/
def DimOK (n : Nat) (d : Int) (pd ps : Int × Int) : Prop :=
  pd.2 - pd.1 = ps.2 - ps.1 ∧ pd.1 - 1 ≤ pd.2 ∧ 1 ≤ pd.1 ∧ pd.2 ≤ n ∧ 1 ≤ ps.1 ∧ ps.2 ≤ n ∧
    ∀ j, pd.1 ≤ j → j ≤ pd.2 → ps.1 + (j - pd.1) = (j - 1 - d) % (n : Int) + 1

def DimsOK : List Nat → List Int → List (Int × Int) → List (Int × Int) → Prop
  | n :: ns, d :: ds, pd :: pds, ps :: pss => DimOK n d pd ps ∧ DimsOK ns ds pds pss
  | [], [], [], [] => True
  | _, _, _, _ => False

/-- `J` lies in the destination block `pds`. -/
def InBlock : List (Int × Int) → List Int → Prop
  | pd :: pds, j :: J => pd.1 ≤ j ∧ j ≤ pd.2 ∧ InBlock pds J
  | [], [] => True
  | _, _ => False

/-- The documented value at `J`. -/
def circF (sz : List Nat) (sh : List Int) (J : List Int) : List Int :=
  (J.zip (sz.zip sh)).map fun (j, n, s) => (j - 1 - s) % (n : Int) + 1

theorem emod_of_eq (a t n q : Int) (h : a = t + n * q) (h0 : 0 ≤ t) (h1 : t < n) : a % n = t := by
  subst h; rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt h0 h1

theorem dim_r1 (n : Nat) (d : Int) (hn : 0 < n) :
    DimOK n d (1, 1 + d % (n : Int) - 1) ((n : Int) - d % (n : Int) + 1, n) := by
  have hs0 : 0 ≤ d % (n : Int) := Int.emod_nonneg _ (by omega)
  have hs1 : d % (n : Int) < n := Int.emod_lt_of_pos _ (by omega)
  have hd := Int.mul_ediv_add_emod d (n : Int)
  generalize d % (n : Int) = s at *
  generalize d / (n : Int) = Q at *
  refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
    by dsimp only; omega, by dsimp only; omega, ?_⟩
  dsimp only
  intro j h1 h2
  rw [emod_of_eq (j - 1 - d) (j - 1 - s + n) n (-(Q + 1))
    (by rw [Int.mul_neg, Int.mul_add, Int.mul_one]; omega) (by omega) (by omega)]
  omega

theorem dim_r2 (n : Nat) (d : Int) (hn : 0 < n) :
    DimOK n d (1 + d % (n : Int), n) (1, (n : Int) - d % (n : Int)) := by
  have hs0 : 0 ≤ d % (n : Int) := Int.emod_nonneg _ (by omega)
  have hs1 : d % (n : Int) < n := Int.emod_lt_of_pos _ (by omega)
  have hd := Int.mul_ediv_add_emod d (n : Int)
  generalize d % (n : Int) = s at *
  generalize d / (n : Int) = Q at *
  refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
    by dsimp only; omega, by dsimp only; omega, ?_⟩
  dsimp only
  intro j h1 h2
  rw [emod_of_eq (j - 1 - d) (j - 1 - s) n (-Q)
    (by rw [Int.mul_neg]; omega) (by omega) (by omega)]
  omega

theorem blocks_ok : ∀ (sz : List Nat) (sh : List Int), sh.length = sz.length → (∀ n ∈ sz, 0 < n) →
    ∀ b ∈ circBlocks sz sh, DimsOK sz sh b.1 b.2 := by
  intro sz
  induction sz with
  | nil =>
    intro sh hl _ b hb
    cases sh with
    | nil => simp [circBlocks] at hb; subst hb; simp [DimsOK]
    | cons _ _ => simp at hl
  | cons n ns ih =>
    intro sh hl hpos b hb
    cases sh with
    | nil => simp at hl
    | cons d ds =>
      have hn : 0 < n := hpos n (by simp)
      have ih' := ih ds (by simpa using hl) (fun m hm => hpos m (by simp [hm]))
      simp only [circBlocks, List.mem_append, List.mem_map] at hb
      rcases hb with ⟨b', hb', rfl⟩ | ⟨b', hb', rfl⟩
      · exact ⟨dim_r1 n d hn, ih' b' hb'⟩
      · exact ⟨dim_r2 n d hn, ih' b' hb'⟩

theorem cover : ∀ (sz : List Nat) (sh : List Int) (J : List Int), sh.length = sz.length →
    (∀ n ∈ sz, 0 < n) → inAxes (oneAxes sz) J = true → ∃ b ∈ circBlocks sz sh, InBlock b.1 J := by
  intro sz
  induction sz with
  | nil =>
    intro sh J hl _ hJ
    cases sh with
    | nil =>
      cases J with
      | nil => exact ⟨([], []), by simp [circBlocks], by simp [InBlock]⟩
      | cons j J => simp [oneAxes, inAxes_nil_cons] at hJ
    | cons _ _ => simp at hl
  | cons n ns ih =>
    intro sh J hl hpos hJ
    cases sh with
    | nil => simp at hl
    | cons d ds =>
      cases J with
      | nil => simp [oneAxes_cons, inAxes_cons_nil] at hJ
      | cons j J =>
        rw [oneAxes_cons, inAxes_cons] at hJ
        obtain ⟨⟨hj1, hj2⟩, hJ'⟩ := hJ
        obtain ⟨b', hb', hin⟩ := ih ds J (by simpa using hl) (fun m hm => hpos m (by simp [hm])) hJ'
        simp only [circBlocks, List.mem_append, List.mem_map]
        by_cases hj : j ≤ d % (n : Int)
        · exact ⟨_, Or.inl ⟨b', hb', rfl⟩, by simp only [InBlock]; exact ⟨by omega, by omega, hin⟩⟩
        · exact ⟨_, Or.inr ⟨b', hb', rfl⟩, by simp only [InBlock]; exact ⟨by omega, by omega, hin⟩⟩

theorem empty_box : ∀ (sz : List Nat) (J : List Int), sz.any (· == 0) = true →
    inAxes (oneAxes sz) J = true → False := by
  intro sz
  induction sz with
  | nil => intro J h; simp at h
  | cons n ns ih =>
    intro J hz hJ
    cases J with
    | nil => simp [oneAxes_cons, inAxes_cons_nil] at hJ
    | cons j J =>
      rw [oneAxes_cons, inAxes_cons] at hJ
      simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at hz
      rcases hz with hz | hz
      · subst hz; simp at hJ; omega
      · exact ih J hz hJ.2

/-! ## One `copyto!` call per block -/

theorem inBlock_le : ∀ (pds : List (Int × Int)) (J : List Int), InBlock pds J → ∀ p ∈ pds, p.1 ≤ p.2 := by
  intro pds
  induction pds with
  | nil => intro J _ p hp; simp at hp
  | cons pd pds ih =>
    intro J h p hp
    cases J with
    | nil => simp [InBlock] at h
    | cons j J =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · omega
      · exact ih J h3 p hp

theorem inBlock_length : ∀ (pds : List (Int × Int)) (J : List Int), InBlock pds J → J.length = pds.length := by
  intro pds
  induction pds with
  | nil => intro J h; cases J with
    | nil => rfl
    | cons _ _ => simp [InBlock] at h
  | cons pd pds ih =>
    intro J h
    cases J with
    | nil => simp [InBlock] at h
    | cons j J => simp [ih J h.2.2]

theorem lens_eq : ∀ (sz : List Nat) (sh : List Int) (pds pss : List (Int × Int)), DimsOK sz sh pds pss →
    (pds.map fun p => unitRng p.1 p.2).map (·.len) = (pss.map fun p => unitRng p.1 p.2).map (·.len) := by
  intro sz
  induction sz with
  | nil =>
    intro sh pds pss hok
    rcases sh with _ | ⟨d, ds⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp [DimsOK] at hok ⊢
  | cons n ns ih =>
    intro sh pds pss hok
    rcases sh with _ | ⟨d, ds⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp only [DimsOK] at hok
    obtain ⟨⟨hdiff, -⟩, hrest⟩ := hok
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih ds pds pss hrest⟩
    rw [unitRng_len, unitRng_len, hdiff]

theorem corners : ∀ (sz : List Nat) (sh : List Int) (pds pss : List (Int × Int)), DimsOK sz sh pds pss →
    (∀ n ∈ sz, n < 2 ^ 62) → (∀ p ∈ pds, p.1 ≤ p.2) →
    inAxes (oneAxes sz) ((pds.map fun p => unitRng p.1 p.2).map (·.start.val)) = true ∧
    inAxes (oneAxes sz) ((pds.map fun p => unitRng p.1 p.2).map (·.last.val)) = true ∧
    inAxes (oneAxes sz) ((pss.map fun p => unitRng p.1 p.2).map (·.start.val)) = true ∧
    inAxes (oneAxes sz) ((pss.map fun p => unitRng p.1 p.2).map (·.last.val)) = true := by
  intro sz
  induction sz with
  | nil =>
    intro sh pds pss hok _ _
    rcases sh with _ | ⟨d, ds⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp [DimsOK] at hok ⊢
    simp [oneAxes, inAxes]
  | cons n ns ih =>
    intro sh pds pss hok hb hne
    rcases sh with _ | ⟨d, ds⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp only [DimsOK] at hok
    obtain ⟨⟨hdiff, hle, h1, h2, h3, h4, -⟩, hrest⟩ := hok
    have hn : n < 2 ^ 62 := hb n (by simp)
    have hpd : pd.1 ≤ pd.2 := hne pd (by simp)
    obtain ⟨c1, c2, c3, c4⟩ := ih ds pds pss hrest (fun m hm => hb m (by simp [hm]))
      (fun p hp => hne p (by simp [hp]))
    simp only [List.map_cons, oneAxes_cons, inAxes_cons]
    rw [unitRng_start pd.1 pd.2 (by omega) (by omega), unitRng_last pd.1 pd.2 (by omega) hpd (by omega),
      unitRng_start ps.1 ps.2 (by omega) (by omega), unitRng_last ps.1 ps.2 (by omega) (by omega) (by omega)]
    exact ⟨⟨by omega, c1⟩, ⟨by omega, c2⟩, ⟨by omega, c3⟩, ⟨by omega, c4⟩⟩

theorem cover_value : ∀ (sz : List Nat) (sh : List Int) (pds pss : List (Int × Int)), DimsOK sz sh pds pss →
    (∀ n ∈ sz, n < 2 ^ 62) → ∀ (J : List Int) (ks : List Nat),
    ((pds.map fun p => unitRng p.1 p.2).zip J).mapM (fun (r, j) => r.pos j) = some ks →
    ((pss.map fun p => unitRng p.1 p.2).zip ks).map (fun (r, k) => r.elem k) = circF sz sh J := by
  intro sz
  induction sz with
  | nil =>
    intro sh pds pss hok _ J ks _
    rcases sh with _ | ⟨d, ds⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp [DimsOK] at hok ⊢
    simp [circF]
  | cons n ns ih =>
    intro sh pds pss hok hb J ks hm
    rcases sh with _ | ⟨d, ds⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp only [DimsOK] at hok
    obtain ⟨⟨hdiff, hle, h1, h2, h3, h4, hcov⟩, hrest⟩ := hok
    have hn : n < 2 ^ 62 := hb n (by simp)
    cases J with
    | nil =>
      simp at hm; subst hm; simp [circF]
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
          have := ih ds pds pss hrest (fun m hm => hb m (by simp [hm])) J ks' hm'
          simp only [circF] at this ⊢
          simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
          refine ⟨?_, this⟩
          rw [unitRng_elem ps.1 ps.2 _ (by omega) (by omega)]
          have := hcov j hj.1 hj.2
          omega
      · rw [if_neg hj] at hm
        simp at hm

theorem cover_some : ∀ (sz : List Nat) (sh : List Int) (pds pss : List (Int × Int)), DimsOK sz sh pds pss →
    (∀ n ∈ sz, n < 2 ^ 62) → ∀ J : List Int, InBlock pds J →
    ∃ ks, ((pds.map fun p => unitRng p.1 p.2).zip J).mapM (fun (r, j) => r.pos j) = some ks := by
  intro sz
  induction sz with
  | nil =>
    intro sh pds pss hok _ J hin
    rcases sh with _ | ⟨d, ds⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp [DimsOK] at hok ⊢
  | cons n ns ih =>
    intro sh pds pss hok hb J hin
    rcases sh with _ | ⟨d, ds⟩ <;> rcases pds with _ | ⟨pd, pds⟩ <;> rcases pss with _ | ⟨ps, pss⟩ <;>
      simp only [DimsOK] at hok
    obtain ⟨⟨hdiff, hle, h1, h2, h3, h4, -⟩, hrest⟩ := hok
    have hn : n < 2 ^ 62 := hb n (by simp)
    cases J with
    | nil => simp [InBlock] at hin
    | cons j J =>
      obtain ⟨hj1, hj2, hin'⟩ := hin
      obtain ⟨ks', hks'⟩ := ih ds pds pss hrest (fun m hm => hb m (by simp [hm])) J hin'
      have hp := unitRng_pos pd.1 pd.2 j (by omega) (by omega)
      rw [if_pos ⟨hj1, hj2⟩] at hp
      exact ⟨(j - pd.1).toNat :: ks', by simp [List.mapM_cons, hp, hks']⟩

theorem block_step {α : Type} (sz : List Nat) (sh : List Int) (pds pss : List (Int × Int))
    (hok : DimsOK sz sh pds pss) (hb : ∀ n ∈ sz, n < 2 ^ 62)
    (dest : List Int → Option α) (src : List Int → α) :
    ∃ dest', copytoCI (oneAxes sz) dest (pds.map fun p => unitRng p.1 p.2) (oneAxes sz) src
        (pss.map fun p => unitRng p.1 p.2) = .ok dest' ∧
      ∀ J, (dest' J = dest J ∨ dest' J = some (src (circF sz sh J))) ∧
        (InBlock pds J → dest' J = some (src (circF sz sh J))) := by
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
    rw [if_neg (fun h => h (lens_eq sz sh pds pss hok))]
    obtain ⟨c1, c2, c3, c4⟩ := corners sz sh pds pss hok hb hne
    rw [c1, c2, c3, c4, if_neg (by decide)]
    refine ⟨_, rfl, fun J => ?_⟩
    dsimp only
    constructor
    · split
      · next ks hks =>
        split
        · exact Or.inr (congrArg (fun x => some (src x)) (cover_value sz sh pds pss hok hb J ks hks))
        · exact Or.inl rfl
      · exact Or.inl rfl
    · intro hJ
      obtain ⟨ks, hks⟩ := cover_some sz sh pds pss hok hb J hJ
      have hlen : J.length = (pds.map fun p => unitRng p.1 p.2).length := by
        rw [List.length_map]; exact inBlock_length pds J hJ
      split
      · next ks' hks' =>
        rw [if_pos hlen]
        exact congrArg (fun x => some (src x)) (cover_value sz sh pds pss hok hb J ks' hks')
      · next h => rw [hks] at h; cases h

/-! ## Running all blocks -/

theorem runBlocks_spec {α : Type} (axd axs : List (Int × Int)) (src : List Int → α)
    (g : List Int → Option α) (C : List (Int × Int) × List (Int × Int) → List Int → Prop) :
    ∀ L : List (List (Int × Int) × List (Int × Int)),
    (∀ b ∈ L, ∀ dest, ∃ dest', copytoCI axd dest (b.1.map fun p => unitRng p.1 p.2) axs src
        (b.2.map fun p => unitRng p.1 p.2) = .ok dest' ∧
      ∀ J, (dest' J = dest J ∨ dest' J = g J) ∧ (C b J → dest' J = g J)) →
    ∀ dest, ∃ d', runBlocks axd axs src L dest = .ok d' ∧
      ∀ J, (d' J = dest J ∨ d' J = g J) ∧ ((∃ b ∈ L, C b J) → d' J = g J) := by
  intro L
  induction L with
  | nil =>
    intro _ dest
    exact ⟨dest, rfl, fun J => ⟨Or.inl rfl, fun ⟨_, hb, _⟩ => by simp at hb⟩⟩
  | cons b rest ih =>
    intro hL dest
    obtain ⟨bd, bs⟩ := b
    obtain ⟨d1, h1, h1J⟩ := hL (bd, bs) (by simp) dest
    obtain ⟨d2, h2, h2J⟩ := ih (fun b' hb' => hL b' (by simp [hb'])) d1
    refine ⟨d2, ?_, fun J => ⟨?_, ?_⟩⟩
    · rw [runBlocks, h1]; exact h2
    · rcases (h2J J).1 with h | h
      · rw [h]; rcases (h1J J).1 with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · exact Or.inr h
    · rintro ⟨b', hb', hC⟩
      simp only [List.mem_cons] at hb'
      rcases hb' with rfl | hb'
      · rcases (h2J J).1 with h | h
        · rw [h]; exact (h1J J).2 hC
        · exact h
      · exact (h2J J).2 ⟨b', hb', hC⟩

theorem circshiftFormula : CircshiftFormula := by
  intro sz shifts src hsz hlen
  unfold circshift
  by_cases hz : sz.any (· == 0) = true
  · rw [if_pos hz]
    exact ⟨_, rfl, fun J hJ => (empty_box sz J hz hJ).elim⟩
  · rw [if_neg hz]
    have hpos : ∀ n ∈ sz, 0 < n := by
      intro n hn
      refine Nat.pos_of_ne_zero fun h0 => hz (List.any_eq_true.mpr ⟨n, hn, by simp [h0]⟩)
    have hfill : fillToLength shifts sz.length =
        .ok (shifts ++ List.replicate (sz.length - shifts.length) 0) := by
      unfold fillToLength; rw [if_neg (by omega)]
    rw [hfill]
    have hshlen : (shifts ++ List.replicate (sz.length - shifts.length) 0).length = sz.length := by
      simp; omega
    obtain ⟨d', hrun, hJ⟩ := runBlocks_spec (oneAxes sz) (oneAxes sz) src
      (fun J => some (src (circF sz (shifts ++ List.replicate (sz.length - shifts.length) 0) J)))
      (fun b J => InBlock b.1 J)
      (circBlocks sz (shifts ++ List.replicate (sz.length - shifts.length) 0))
      (fun b hb dest => block_step sz _ b.1 b.2
        (blocks_ok sz _ hshlen hpos b hb) hsz dest src)
      (fun _ => none)
    exact ⟨d', hrun, fun J hJin => (hJ J).2 (cover sz _ J hshlen hpos hJin)⟩

end JuliaLean.Multidim
