import JuliaLean.RandomSampling.NdlProofs

/-! Proofs for `randperm`, `randcycle`, `shuffle!`, `rand(Char)` and the empty-collection errors. -/

set_option maxRecDepth 10000

namespace JuliaLean.RandomSampling

open JuliaLean

theorem lit64_val (x : Nat) (hx : x < 2 ^ 62) : (JInt.lit .i64 x).val = x := by
  rw [val_lit']
  apply wrapInt_of_inRange
  have hmin : IntTy.i64.min = -(2 : Int) ^ 63 := rfl
  have hmax : IntTy.i64.max = (2 : Int) ^ 63 - 1 := rfl
  have h63 : (2 : Int) ^ 63 = ((2 ^ 62 : Nat) : Int) * 2 := by
    rw [show 63 = 62 + 1 from rfl, Int.pow_succ, two_pow_int]
  rw [hmin, hmax, h63]
  omega

/-- `rand(rng, lo:hi)` for `lo ≤ hi` returns some `j` in `lo:hi`. -/
theorem randRange_bounds {σ : Type} (g : Rng σ) (fuel : Nat) (lo hi : JInt64) (st : σ)
    (res : Jl (JInt64 × σ)) (hlo : lo.val ≤ hi.val) (hr : randRange g fuel lo hi st = some res) :
    ∃ j st', res = .ok (j, st') ∧ lo.val ≤ j.val ∧ j.val ≤ hi.val := by
  unfold randRange at hr
  cases hs : ndlSampler lo hi with
  | error e =>
    unfold ndlSampler at hs
    rw [if_neg (Int.not_lt.2 hlo)] at hs
    cases hs
  | ok sp =>
    rw [hs] at hr
    exact ndlInRange_proven .i64 (by decide) lo hi sp hs σ g fuel st res hr

/-- `rand(rng, 1:h)` for `1 ≤ h` returns some `j` in `1:h`. -/
theorem randRange_spec {σ : Type} (g : Rng σ) (fuel h : Nat) (st : σ) (res : Jl (JInt64 × σ))
    (h1 : 1 ≤ h) (h2 : h < 2 ^ 62) (hr : randIndex g fuel h st = some res) :
    ∃ j st', res = .ok (j, st') ∧ 1 ≤ j.val ∧ j.val ≤ h := by
  have e1 : (JInt.lit .i64 1).val = 1 := lit64_val 1 (by decide)
  have e2 := lit64_val h h2
  unfold randIndex at hr
  obtain ⟨j, st', hres, ha, hb⟩ := randRange_bounds g fuel _ _ st res (by rw [e1, e2]; omega) hr
  rw [e1] at ha
  rw [e2] at hb
  exact ⟨j, st', hres, ha, hb⟩

/-- `draw h` returns some `j` in `1:h` whenever `1 ≤ h`. -/
def DrawInRange {σ : Type} (draw : Nat → σ → Run σ JInt64) : Prop :=
  ∀ h st r, 1 ≤ h → h < 2 ^ 62 → draw h st = some r →
    ∃ j st', r = .ok (j, st') ∧ 1 ≤ j.val ∧ j.val ≤ h

/-- The loop shared by `randperm!`, `randcycle!` and `shuffle!` preserves any invariant its
body preserves for draws `j` in `1:hi(i)`. -/
theorem permLoop_inv {σ : Type} (draw : Nat → σ → Run σ JInt64) (hdraw : DrawInRange draw)
    (hi : Nat → Nat)
    (body : Nat → Nat → (Nat → Int) → (Nat → Int)) (P : Nat → (Nat → Int) → Prop)
    (hhi : ∀ i, 2 ≤ i → 1 ≤ hi i ∧ hi i ≤ i)
    (hstep : ∀ i j a, 2 ≤ i → 1 ≤ j → j ≤ hi i → P (i - 1) a → P i (body i j a)) :
    ∀ k i a st res, 2 ≤ i → i + k ≤ 2 ^ 62 → P (i - 1) a →
      permLoop draw hi body k i a st = some res →
      ∃ a' st', res = .ok (a', st') ∧ P (i + k - 1) a'
  | 0, i, a, st, res, _, _, hP, h => by
    simp only [permLoop, Option.some.injEq] at h
    subst h
    exact ⟨a, st, rfl, by simpa using hP⟩
  | k + 1, i, a, st, res, hi2, hk, hP, h => by
    have hb := hhi i hi2
    simp only [permLoop] at h
    cases hr : draw (hi i) st with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨j, st', rfl, hj1, hj2⟩ := hdraw (hi i) st r hb.1 (by omega) hr
      rw [hr] at h
      dsimp only at h
      have hP' := hstep i j.val.toNat a hi2 (by omega) (by omega) hP
      obtain ⟨a', st'', hres', hP''⟩ := permLoop_inv draw hdraw hi body P hhi hstep k (i + 1) _ st'
        res (by omega) (by omega) (by simpa using hP') h
      exact ⟨a', st'', hres', by rw [show i + (k + 1) - 1 = i + 1 + k - 1 by omega]; exact hP''⟩

/-- Inserting `i` after position `j` of a permutation of `1:i-1` gives a permutation of `1:i`. -/
theorem insert_perm (i j : Nat) (a b : Nat → Int) (hi : 2 ≤ i) (hj1 : 1 ≤ j) (hj2 : j ≤ i)
    (hP : IsPerm (i - 1) a)
    (hb : ∀ k, b k = if k = j then (i : Int) else if k = i then a j else a k) : IsPerm i b := by
  obtain ⟨hv, hinj⟩ := hP
  -- every position of `1:i` except `j` reads `a` at a position `k'` of `1:i-1`
  have hread : ∀ k, 1 ≤ k → k ≤ i → k ≠ j →
      ∃ k', 1 ≤ k' ∧ k' ≤ i - 1 ∧ b k = a k' ∧ (k = i → k' = j) ∧ (k ≠ i → k' = k) := by
    intro k hk1 hk2 hkj
    by_cases hki : k = i
    · subst hki
      refine ⟨j, hj1, by omega, by rw [hb]; simp [hkj], fun _ => rfl, fun h => absurd rfl h⟩
    · refine ⟨k, hk1, by omega, by rw [hb]; simp [hkj, hki], fun h => absurd h hki, fun _ => rfl⟩
  constructor
  · intro k hk1 hk2
    by_cases hkj : k = j
    · rw [hb]; simp [hkj]; omega
    · obtain ⟨k', h1, h2, h3, -, -⟩ := hread k hk1 hk2 hkj
      have := hv k' h1 h2
      rw [h3]; omega
  · intro k l hk1 hk2 hl1 hl2 hkl
    by_cases hkj : k = j <;> by_cases hlj : l = j
    · omega
    · obtain ⟨l', h1, h2, h3, -, -⟩ := hread l hl1 hl2 hlj
      have := hv l' h1 h2
      rw [hb k] at hkl; simp [hkj] at hkl; rw [h3] at hkl; omega
    · obtain ⟨k', h1, h2, h3, -, -⟩ := hread k hk1 hk2 hkj
      have := hv k' h1 h2
      rw [hb l] at hkl; simp [hlj] at hkl; rw [h3] at hkl; omega
    · obtain ⟨k', h1, h2, h3, h4, h5⟩ := hread k hk1 hk2 hkj
      obtain ⟨l', h1', h2', h3', h4', h5'⟩ := hread l hl1 hl2 hlj
      rw [h3, h3'] at hkl
      have hkl' := hinj k' l' h1 h2 h1' h2' hkl
      by_cases hki : k = i <;> by_cases hli : l = i
      · omega
      · have := h4 hki; have := h5' hli; omega
      · have := h5 hki; have := h4' hli; omega
      · have := h5 hki; have := h5' hli; omega

theorem randpermBody_eq (i j : Nat) (a : Nat → Int) (k : Nat) :
    randpermBody i j a k = if k = j then (i : Int) else if k = i then a j else a k := by
  unfold randpermBody update
  by_cases hij : i = j
  · subst hij; by_cases hk : k = i <;> simp [hk]
  · simp [hij]

theorem randcycleBody_eq (i j : Nat) (a : Nat → Int) (k : Nat) :
    randcycleBody i j a k = if k = j then (i : Int) else if k = i then a j else a k := by
  unfold randcycleBody update; rfl

theorem randpermIsPerm_proven : RandpermIsPerm := by
  intro σ g fuel n st res hn h
  unfold randperm at h
  split at h
  · rename_i hn0
    simp only [Option.some.injEq] at h
    subst h hn0
    exact ⟨_, _, rfl, fun k h1 h2 => absurd h2 (by omega), fun k _ _ h2 => absurd h2 (by omega)⟩
  · rename_i hn0
    obtain ⟨a', st', hres, hP⟩ := permLoop_inv (randIndex g fuel) (randRange_spec g fuel) id
      randpermBody (fun i a => IsPerm i a)
      (fun i hi => ⟨show 1 ≤ i by omega, Nat.le_refl i⟩)
      (fun i j a hi hj1 hj2 hP => insert_perm i j a _ hi hj1 hj2 hP (randpermBody_eq i j a))
      (n - 1) 2 _ st res (by omega) (by omega)
      (⟨fun k h1 h2 => by simp [update, show k = 1 by omega],
        fun k l h1 h2 h3 h4 _ => by omega⟩) h
    exact ⟨a', st', hres, by rw [show n = 2 + (n - 1) - 1 by omega]; exact hP⟩

/-- `iterPerm` stays inside `1:i` for a permutation of `1:i`. -/
theorem iterPerm_mem (i : Nat) (a : Nat → Int) (hP : IsPerm i a) (hi : 1 ≤ i) :
    ∀ m, 1 ≤ iterPerm a m 1 ∧ iterPerm a m 1 ≤ i
  | 0 => ⟨Nat.le_refl 1, hi⟩
  | m + 1 => by
    obtain ⟨h1, h2⟩ := iterPerm_mem i a hP hi m
    have := hP.1 _ h1 h2
    show 1 ≤ (a (iterPerm a m 1)).toNat ∧ (a (iterPerm a m 1)).toNat ≤ i
    omega

/-- Every element reachable from 1 before the insertion is reachable after it. -/
theorem iterPerm_lift (i j : Nat) (a b : Nat → Int) (hi : 2 ≤ i) (hj1 : 1 ≤ j) (hj2 : j ≤ i - 1)
    (hP : IsPerm (i - 1) a)
    (hb : ∀ k, b k = if k = j then (i : Int) else if k = i then a j else a k) :
    ∀ m, ∃ m', iterPerm b m' 1 = iterPerm a m 1
  | 0 => ⟨0, rfl⟩
  | m + 1 => by
    obtain ⟨m', hm'⟩ := iterPerm_lift i j a b hi hj1 hj2 hP hb m
    obtain ⟨h1, h2⟩ := iterPerm_mem (i - 1) a hP (by omega) m
    by_cases hx : iterPerm a m 1 = j
    · refine ⟨m' + 2, ?_⟩
      show (b (b (iterPerm b m' 1)).toNat).toNat = (a (iterPerm a m 1)).toNat
      rw [hm', hx, hb j]
      simp only [↓reduceIte, Int.toNat_natCast]
      rw [hb i]
      simp [show i ≠ j by omega]
    · refine ⟨m' + 1, ?_⟩
      show (b (iterPerm b m' 1)).toNat = (a (iterPerm a m 1)).toNat
      rw [hm', hb]
      simp [hx, show iterPerm a m 1 ≠ i by omega]

theorem randcycleSingleCycle_proven : RandcycleSingleCycle := by
  intro σ g fuel n st res hn h
  unfold randcycle at h
  split at h
  · rename_i hn0
    simp only [Option.some.injEq] at h
    subst h hn0
    exact ⟨_, _, rfl, ⟨fun k h1 h2 => absurd h2 (by omega), fun k _ _ h2 => absurd h2 (by omega)⟩,
      fun k h1 h2 => absurd h2 (by omega)⟩
  · rename_i hn0
    obtain ⟨a', st', hres, hP, hR⟩ := permLoop_inv (randIndex g fuel) (randRange_spec g fuel)
      (fun i => i - 1) randcycleBody
      (fun i a => IsPerm i a ∧ ∀ k, 1 ≤ k → k ≤ i → ∃ m, iterPerm a m 1 = k)
      (fun i hi => ⟨show 1 ≤ i - 1 by omega, show i - 1 ≤ i by omega⟩)
      (fun i j a hi hj1 hj2 ⟨hP, hR⟩ => by
        refine ⟨insert_perm i j a _ hi hj1 (by omega) hP (randcycleBody_eq i j a), ?_⟩
        intro k hk1 hk2
        by_cases hki : k = i
        · obtain ⟨m, hm⟩ := hR j hj1 hj2
          obtain ⟨m', hm'⟩ := iterPerm_lift i j a _ hi hj1 hj2 hP (randcycleBody_eq i j a) m
          refine ⟨m' + 1, ?_⟩
          show (randcycleBody i j a (iterPerm (randcycleBody i j a) m' 1)).toNat = k
          rw [hm', hm, randcycleBody_eq]
          simp [hki]
        · obtain ⟨m, hm⟩ := hR k hk1 (by omega)
          obtain ⟨m', hm'⟩ := iterPerm_lift i j a _ hi hj1 hj2 hP (randcycleBody_eq i j a) m
          exact ⟨m', hm'.trans hm⟩)
      (n - 1) 2 _ st res (by omega) (by omega)
      ⟨⟨fun k h1 h2 => by simp [update, show k = 1 by omega],
        fun k l h1 h2 h3 h4 _ => by omega⟩,
       fun k h1 h2 => ⟨0, by simp [iterPerm]; omega⟩⟩ h
    refine ⟨a', st', hres, ?_, ?_⟩
    · rw [show n = 2 + (n - 1) - 1 by omega]; exact hP
    · rw [show n = 2 + (n - 1) - 1 by omega]; exact hR

theorem shuffleBody_eq (i j : Nat) (b : Nat → Int) (k : Nat) :
    shuffleBody i j b k = if k = j then b i else if k = i then b j else b k := by
  unfold shuffleBody update; rfl

/-- `shuffle!` on `c` tracks `c` composed with `randperm!`, draw for draw. -/
theorem shuffle_loop {σ : Type} (draw : Nat → σ → Run σ JInt64) (hdraw : DrawInRange draw)
    (c : Nat → Int) :
    ∀ k i (p b : Nat → Int) (st : σ), 2 ≤ i → i + k ≤ 2 ^ 62 →
      (∀ x, b x = if 1 ≤ x ∧ x ≤ i - 1 then c (p x).toNat else c x) →
      permLoop draw id shuffleBody k i b st =
        (permLoop draw id randpermBody k i p st).map fun res => res.map fun q =>
          (fun x => if 1 ≤ x ∧ x ≤ i + k - 1 then c (q.1 x).toNat else c x, q.2)
  | 0, i, p, b, st, _, _, hrel => by
    have hb : b = fun x => if 1 ≤ x ∧ x ≤ i - 1 then c (p x).toNat else c x := funext hrel
    subst hb
    simp only [permLoop, Option.map_some, Except.map, Nat.add_zero]
  | k + 1, i, p, b, st, hi, hk, hrel => by
    simp only [permLoop, id_eq]
    cases hr : draw i st with
    | none => rfl
    | some r =>
      obtain ⟨j, st', rfl, hj1, hj2⟩ := hdraw i st r (by omega) (by omega) hr
      dsimp only
      rw [shuffle_loop draw hdraw c k (i + 1) (randpermBody i j.val.toNat p)
        (shuffleBody i j.val.toNat b) st' (by omega) (by omega)]
      · simp only [show i + 1 + k - 1 = i + (k + 1) - 1 by omega]
      · intro x
        rw [shuffleBody_eq, randpermBody_eq]
        by_cases hxj : x = j.val.toNat
        · rw [if_pos hxj, if_pos hxj, hrel i]
          simp only [Int.toNat_natCast]
          rw [if_neg (by omega), if_pos (by omega)]
        · rw [if_neg hxj, if_neg hxj]
          by_cases hxi : x = i
          · rw [if_pos hxi, if_pos hxi, hrel, if_pos (by omega), if_pos (by omega)]
          · rw [if_neg hxi, if_neg hxi, hrel]
            by_cases hx : 1 ≤ x ∧ x ≤ i - 1
            · rw [if_pos hx, if_pos (by omega)]
            · rw [if_neg hx, if_neg (by omega)]

theorem shuffleIsRandperm_proven : ShuffleIsRandperm := by
  intro σ g fuel n st c hn
  unfold shuffle randperm
  by_cases hn0 : n = 0
  · subst hn0
    simp only [permLoop, Nat.zero_sub, ↓reduceIte, Option.map_some, Except.map,
      Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, and_true]
    funext x
    split
    · omega
    · rfl
  · rw [if_neg hn0, shuffle_loop (randIndex g fuel) (randRange_spec g fuel) c (n - 1) 2
      (update undefArray 1 1) c st (by omega) (by omega)]
    · simp only [show 2 + (n - 1) - 1 = n by omega]
    · intro x
      by_cases hx : x = 1
      · subst hx; simp [update]
      · rw [if_neg (by omega)]

theorem randCharValid_proven : RandCharValid := by
  intro σ g fuel st res h
  unfold randCharCode at h
  split at h
  · rename_i e he
    unfold ndlSampler at he
    split at he
    · rename_i hc; exact absurd hc (by decide)
    · cases he
  · rename_i sp hsp
    cases hr : ndlRand g sp fuel st with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨v, st', hres, h1, h2⟩ := ndlInRange_proven .u32 (by decide) _ _ sp hsp σ g fuel st r hr
      subst hres
      simp only [hr, Option.map_some, Except.map, Option.some.injEq] at h
      subst h
      refine ⟨_, _, rfl, ?_⟩
      have e1 : (JInt.lit .u32 0x10f7ff).val = 0x10f7ff := by decide
      have e0 : (JInt.lit .u32 0).val = 0 := by decide
      rw [e1] at h2; rw [e0] at h1
      by_cases hv : v.val < 0xd800
      · simp only [hv, ↓reduceIte]; omega
      · simp only [hv, ↓reduceIte]
        have h2048 : wrapInt .u32 2048 = 2048 := by decide
        rw [val_add', val_lit', h2048,
          wrapInt_unsigned (u := .u32) (z := v.val + 2048) rfl (by omega) (by
            rw [show IntTy.u32.bits = 32 from rfl]; omega)]
        omega

theorem emptyArgumentError_proven : EmptyArgumentError := by
  refine ⟨fun t a b h => ?_, fun t a b h => ?_, fun s hs => ?_⟩
  · unfold ndlSampler; rw [if_pos h]
  · unfold fastSampler; rw [if_pos h]
  · unfold stringSampler ndlSampler
    rw [if_pos]
    simp only [Strings.ncodeunits, hs, List.length_nil]
    decide

end JuliaLean.RandomSampling
