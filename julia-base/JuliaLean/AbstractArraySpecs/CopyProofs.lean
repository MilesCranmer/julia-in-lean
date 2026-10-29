import JuliaLean.AbstractArraySpecs.IterProofs

/-! Proof of the `copyto!(dest, src)` contract. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

theorem wrap_add (x y : Int) : wrapInt .i64 (x + wrapInt .i64 y) = wrapInt .i64 (x + y) := by
  rw [wi, wi, wi]; omega

theorem wrap_add' (x y : Int) : wrapInt .i64 (wrapInt .i64 y + x) = wrapInt .i64 (y + x) := by
  rw [wi, wi, wi]; omega

theorem isemptyA_eq {α : Type} (A : Arr α) (hA : A.WF) :
    isemptyA A = decide (A.data.length = 0) := by
  unfold isemptyA
  rw [beq64, lengthA_val A hA, zero_val]
  simp

/-- Range-mode `eachindex` steps yield one index `lo + j`. -/
theorem each_step_range {α : Type} (A : Arr α) (hA : A.WF) (hr : eachRange A = true) (j : Nat)
    (st : IterState) (hg : GoodE A j st) (h : j < A.data.length) :
    ∃ i st', eachindexStep A st = some ([i], st') ∧ i.val = (linearAxis A).lo.val + j ∧
      refPos A [i] = some j ∧ GoodE A (j + 1) st' := by
  have hj : j ≤ A.data.length := Nat.le_of_lt h
  obtain ⟨s1, -⟩ := each_step A hA j st hg hj
  obtain ⟨I, st', hs, -, hp, hg'⟩ := s1 h
  unfold GoodE at hg
  simp only [hr, if_true] at hg
  have hhi := linAx_len A hA
  have hlo := bnd (linearAxis A).lo
  have hhb := bnd (linearAxis A).hi
  rcases hg with ⟨rfl, rfl⟩ | ⟨hj1, i, rfl, hi⟩
  · have : axIsEmpty (linearAxis A) = false := by
      simp only [axIsEmpty, decide_eq_false_iff_not]
      show ¬ (linearAxis A).hi.val < (linearAxis A).lo.val
      omega
    have hs' := hs
    simp only [eachindexStep, this, Bool.false_eq_true, if_false, Option.some.injEq,
      Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    exact ⟨_, _, hs, by simp, hp, hg'⟩
  · have hne : i ≠ (linearAxis A).hi := by
      intro e; have := congrArg Subtype.val e; omega
    have hs' := hs
    simp only [eachindexStep, hne, if_false, Option.some.injEq, Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    refine ⟨_, _, hs, ?_, hp, hg'⟩
    rw [vadd, one_val, hi, wrap_id _ (by omega) (by omega)]; omega

theorem set_prefix_id {α : Type} (xs ys : List α) (j : Nat) (hx : j < xs.length)
    (hy : j < ys.length) :
    (xs.take j ++ ys.drop j).set j (xs[j]'hx) = xs.take (j + 1) ++ ys.drop (j + 1) := by
  have := set_prefix id xs ys j hx hy
  simpa [List.map_id] using this

theorem prefix_done {α : Type} (xs ys : List α) (h : xs.length ≤ ys.length) :
    xs.take xs.length ++ ys.drop xs.length = xs ++ ys.drop xs.length := by
  rw [List.take_length]

/-- `A` read as an `IndexLinear` array (same axes and elements). -/
def linView {α : Type} (A : Arr α) : Arr α := { A with style := .linear }

theorem linView_eachRange {α : Type} (A : Arr α) : eachRange (linView A) = true := rfl

/-- `LinearIndices(A)` steps do not depend on `A`'s style. -/
theorem eachindexStep_linView {α : Type} (A : Arr α) (j : Nat) (st : IterState)
    (hg : GoodE (linView A) j st) : eachindexStep A st = eachindexStep (linView A) st := by
  unfold GoodE at hg
  rw [linView_eachRange, if_pos rfl] at hg
  rcases hg with ⟨_, rfl⟩ | ⟨_, i, rfl, _⟩ <;> rfl

theorem goodE_rngStart {α : Type} (A : Arr α) : GoodE (linView A) 0 .rngStart := by
  unfold GoodE; rw [linView_eachRange, if_pos rfl]; exact Or.inl ⟨rfl, rfl⟩

/-- The single-index loop over `LinearIndices(src)`. -/
theorem copyLL_from {α : Type} (dest src : Arr α) (hd : dest.WF) (hs : src.WF) (Δ : I64)
    (hΔ : Δ.val = wrapInt .i64 ((linearAxis dest).lo.val - (linearAxis src).lo.val))
    (hle : src.data.length ≤ dest.data.length) :
    ∀ (n j : Nat) (st : IterState), GoodE (linView src) j st → j ≤ src.data.length →
      src.data.length - j < n →
      copyLL src Δ n { dest with data := src.data.take j ++ dest.data.drop j } st =
        .ok { dest with data := src.data ++ dest.data.drop src.data.length } := by
  have hsL : (linView src).WF := hs
  intro n
  induction n with
  | zero => intro j st _ _ h; omega
  | succ n ih =>
    intro j st hg hj hn
    have hstep := eachindexStep_linView src j st hg
    by_cases h1 : j < src.data.length
    · have hj1 : j + 1 ≤ src.data.length := h1
      have hn1 : src.data.length - (j + 1) < n := by omega
      have hjd : j < dest.data.length := by omega
      have hlen : (src.data.take j ++ dest.data.drop j).length = dest.data.length := by
        simp only [List.length_append, List.length_take, List.length_drop]; omega
      have hD : ({ dest with data := src.data.take j ++ dest.data.drop j } : Arr α).WF :=
        ⟨hd.1, by rw [← hd.2.1]; exact congrArg _ hlen, hd.2.2⟩
      have hst := refLin_step dest hd j (by omega)
      rw [if_pos hjd] at hst
      have hlo := bnd (linearAxis src).lo
      have hdlo := bnd (linearAxis dest).lo
      have hdhi := linAx_len dest hd
      have hdb := bnd (linearAxis dest).hi
      obtain ⟨i, st', hs1, hiv, hp, hg'⟩ := each_step_range (linView src) hsL (linView_eachRange src) j st hg h1
      change i.val = (linearAxis src).lo.val + j at hiv
      rw [copyLL, hstep, hs1]
      simp only [List.map_cons, List.map_nil]
      have hk : (i + Δ).val = wrapInt .i64 ((linearAxis dest).lo.val + j) := by
        rw [vadd, hiv, hΔ, wrap_add]; congr 1; omega
      have hpD : refPos { dest with data := src.data.take j ++ dest.data.drop j } [i + Δ] = some j := by
        rw [refPos_data]; show refLinPos dest (i + Δ).val = some j; rw [hk, hst]
      rw [getindex_at src hs [i] j (Or.inr rfl) (by exact hp), bind_ok,
        setindex_at _ hD [i + Δ] j _ (Or.inr rfl) hpD, bind_ok]
      simp only []
      rw [set_prefix_id src.data dest.data j h1 hjd]
      exact ih (j + 1) st' hg' hj1 hn1
    · have e3 : j = src.data.length := by omega
      obtain ⟨-, s2⟩ := each_step (linView src) hsL j st hg hj
      rw [copyLL, hstep, s2 e3]
      simp only []
      rw [e3, List.take_length]

/-- The dual-index loop. -/
theorem copyLC_from {α : Type} (dest src : Arr α) (hd : dest.WF) (hs : src.WF)
    (hle : src.data.length ≤ dest.data.length) :
    ∀ (n j : Nat) (st : IterState) (i : I64), Good src j st → j ≤ src.data.length →
      src.data.length - j < n →
      i.val = wrapInt .i64 ((linearAxis dest).lo.val + j - 1) →
      copyLC src n { dest with data := src.data.take j ++ dest.data.drop j } i st =
        .ok { dest with data := src.data ++ dest.data.drop src.data.length } := by
  intro n
  induction n with
  | zero => intro j st _ _ _ h; omega
  | succ n ih =>
    intro j st i hg hj hn hi
    obtain ⟨s1, s2⟩ := iter_step src hs j st hg hj
    by_cases h1 : j < src.data.length
    · have hj1 : j + 1 ≤ src.data.length := h1
      have hn1 : src.data.length - (j + 1) < n := by omega
      have hjd : j < dest.data.length := by omega
      have hlen : (src.data.take j ++ dest.data.drop j).length = dest.data.length := by
        simp only [List.length_append, List.length_take, List.length_drop]; omega
      have hD : ({ dest with data := src.data.take j ++ dest.data.drop j } : Arr α).WF :=
        ⟨hd.1, by rw [← hd.2.1]; exact congrArg _ hlen, hd.2.2⟩
      have hst := refLin_step dest hd j (by omega)
      rw [if_pos hjd] at hst
      have hi' : (i + i64 1).val = wrapInt .i64 ((linearAxis dest).lo.val + j) := by
        rw [vadd, one_val, hi, wrap_add']; congr 1; omega
      have hpD : refPos { dest with data := src.data.take j ++ dest.data.drop j } [i + i64 1] = some j := by
        rw [refPos_data]; show refLinPos dest (i + i64 1).val = some j; rw [hi', hst]
      obtain ⟨st', hit, hg'⟩ := s1 h1
      rw [copyLC, hit, bind_ok]
      simp only []
      rw [setindex_at _ hD [i + i64 1] j _ (Or.inr rfl) hpD, bind_ok]
      simp only []
      rw [set_prefix_id src.data dest.data j h1 hjd]
      exact ih (j + 1) st' (i + i64 1) hg' hj1 hn1 (by rw [hi']; congr 1; omega)
    · have e3 : j = src.data.length := by omega
      rw [copyLC, s2 e3, bind_ok]
      simp only []
      rw [e3, List.take_length]

/-- The shared-iterator loop, given that `src` reads at `dest`'s indices select the same
positions. -/
theorem copyShared_from {α : Type} (dest src : Arr α) (hd : dest.WF) (hs : src.WF)
    (hL : src.data.length = dest.data.length)
    (hrel : ∀ (j : Nat) (I : List I64), j < dest.data.length → refPos dest I = some j →
      (dest.axes.length ≤ I.length ∨ I.length = 1) → (eachRange dest = true → ∃ k, I = [k]) →
      refPos src I = some j ∧ (src.axes.length ≤ I.length ∨ I.length = 1)) :
    ∀ (n j : Nat) (st : IterState), GoodE dest j st → j ≤ dest.data.length →
      dest.data.length - j < n →
      copyShared src n { dest with data := src.data.take j ++ dest.data.drop j } st =
        .ok { dest with data := src.data ++ dest.data.drop src.data.length } := by
  intro n
  induction n with
  | zero => intro j st _ _ h; omega
  | succ n ih =>
    intro j st hg hj hn
    by_cases h1 : j < dest.data.length
    · have hj1 : j + 1 ≤ dest.data.length := h1
      have hn1 : dest.data.length - (j + 1) < n := by omega
      have hjs : j < src.data.length := by omega
      have hlen : (src.data.take j ++ dest.data.drop j).length = dest.data.length := by
        simp only [List.length_append, List.length_take, List.length_drop]; omega
      have hD : ({ dest with data := src.data.take j ++ dest.data.drop j } : Arr α).WF :=
        ⟨hd.1, by rw [← hd.2.1]; exact congrArg _ hlen, hd.2.2⟩
      obtain ⟨d1, -⟩ := each_step dest hd j st hg hj
      obtain ⟨I, st', hs1, hIl, hIp, hg'⟩ := d1 h1
      have hsing : eachRange dest = true → ∃ k, I = [k] := by
        intro hr
        obtain ⟨i, st'', hs2, -⟩ := each_step_range dest hd hr j st hg h1
        rw [hs1] at hs2
        simp only [Option.some.injEq, Prod.mk.injEq] at hs2
        exact ⟨i, hs2.1⟩
      obtain ⟨hsp, hsl⟩ := hrel j I h1 hIp hIl hsing
      rw [copyShared, eachindexStep_data, hs1]
      simp only []
      rw [getindex_at src hs I j hsl hsp, bind_ok,
        setindex_at _ hD I j _ hIl (by rw [refPos_data]; exact hIp), bind_ok]
      simp only []
      rw [set_prefix_id src.data dest.data j hjs h1]
      exact ih (j + 1) st' hg' hj1 hn1
    · have e3 : j = dest.data.length := by omega
      obtain ⟨-, d2⟩ := each_step dest hd j st hg hj
      rw [copyShared, eachindexStep_data, d2 e3]
      simp only []
      rw [e3, ← hL, List.take_length]

/-! ## Equal iterators select equal positions -/

theorem refLinPos_some {α : Type} (A : Arr α) (hA : A.WF) (k : Int) (j : Nat)
    (h : refLinPos A k = some j) : k = (linearAxis A).lo.val + j := by
  unfold refLinPos at h
  unfold linearAxis
  rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩ <;> simp only [hax] at h ⊢ <;>
    simp only [axes1, hax, onetoLen, oneTo, one_val] <;>
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

/-- The endpoints of an axis. -/
def lohi (r : Ax) : Int × Int := (r.lo.val, r.hi.val)

theorem axEq_vals {r s : Ax} (hr : r.WF) (hs : s.WF) (h : axEq r s = true) (h1 : 1 ≤ r.len) :
    r.lo.val = s.lo.val ∧ r.hi.val = s.hi.val := by
  have := len_def r; have := len_def s
  have hr0 := hr.2.1; have hs0 := hs.2.1
  have lr := axLength_val hr; have ls := axLength_val hs
  unfold axEq axIsEmpty at h
  simp only [decide_lt64, beq64, one_val] at h
  split at h
  · rename_i he; simp only [decide_eq_true_eq] at he; omega
  · split at h
    · rename_i h1; simp only [decide_eq_true_eq] at h1; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega

theorem axesEq_lohi (axs : List Ax) : ∀ (bxs : List Ax), (∀ r ∈ axs, r.WF) → (∀ r ∈ bxs, r.WF) →
    (∀ r ∈ axs, 1 ≤ r.len) → axesEq axs bxs = true → axs.map lohi = bxs.map lohi := by
  induction axs with
  | nil => intro bxs _ _ _ h; cases bxs with
    | nil => rfl
    | cons _ _ => simp [axesEq] at h
  | cons r rs ih =>
    intro bxs ha hb h1 h
    cases bxs with
    | nil => simp [axesEq] at h
    | cons s ss =>
      simp only [axesEq, Bool.and_eq_true] at h
      obtain ⟨e1, e2⟩ := axEq_vals (ha r (by simp)) (hb s (by simp)) h.1 (h1 r (by simp))
      simp only [List.map_cons, lohi, e1, e2,
        ih ss (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx]))
          (fun x hx => h1 x (by simp [hx])) h.2]

theorem refCartPos_congr (axs : List Ax) : ∀ (bxs : List Ax), axs.map lohi = bxs.map lohi →
    ∀ is, refCartPos axs is = refCartPos bxs is := by
  induction axs with
  | nil => intro bxs h is; cases bxs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons r rs ih =>
    intro bxs h is
    cases bxs with
    | nil => simp at h
    | cons s ss =>
      simp only [List.map_cons, List.cons.injEq, lohi, Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, e3⟩ := h
      have el : r.len = s.len := by rw [len_def, len_def, e1, e2]
      cases is with
      | nil =>
        have hq : ∀ (xs : List Ax), xs.all (fun r => decide (r.len = 1)) =
            (xs.map lohi).all (fun p => decide (p.2 - p.1 + 1 = 1)) := by
          intro xs; rw [List.all_map]; rfl
        simp only [refCartPos]
        rw [hq (r :: rs), hq (s :: ss), List.map_cons, List.map_cons, e3,
          show lohi r = lohi s by simp only [lohi, e1, e2]]
      | cons i is =>
        simp only [refCartPos, e1, e2, el, ih ss e3 is]

theorem totalLen_congr (axs : List Ax) : ∀ (bxs : List Ax), axs.map lohi = bxs.map lohi →
    totalLen axs = totalLen bxs := by
  induction axs with
  | nil => intro bxs h; cases bxs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons r rs ih =>
    intro bxs h
    cases bxs with
    | nil => simp at h
    | cons s ss =>
      simp only [List.map_cons, List.cons.injEq, lohi, Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, e3⟩ := h
      rw [totalLen_cons, totalLen_cons, len_def, len_def, e1, e2, ih ss e3]

theorem refPos_congr {α : Type} (A B : Arr α) (h : A.axes.map lohi = B.axes.map lohi) (I : List I64) :
    refPos A I = refPos B I := by
  have hc := refCartPos_congr A.axes B.axes h
  have ht := totalLen_congr A.axes B.axes h
  match I with
  | [k] =>
    show refLinPos A k.val = refLinPos B k.val
    unfold refLinPos
    rcases ha : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩ <;> rcases hb : B.axes with _ | ⟨s, _ | ⟨s2, ss⟩⟩ <;>
      rw [ha, hb] at h <;> simp only [List.map_nil, List.map_cons, List.cons.injEq, lohi,
        Prod.mk.injEq, reduceCtorEq, and_false, false_and, List.nil_eq, List.cons_ne_nil] at h ⊢ <;>
      rw [ha, hb] at ht
    · obtain ⟨⟨e1, e2⟩, _⟩ := h; rw [e1, e2]
    · rw [ht]
  | [] => exact hc []
  | k1 :: k2 :: ks => exact hc _

/-! ## The contract -/

theorem copytoUnaliasedS_prefix {α : Type} (ds ss : Style) (dest src : Arr α) (hd : dest.WF)
    (hs : src.WF) :
    (src.data.length ≤ dest.data.length →
      copytoUnaliasedS ds ss dest src = .ok { dest with data := src.data ++ dest.data.drop src.data.length }) ∧
    (dest.data.length < src.data.length → ∃ e, copytoUnaliasedS ds ss dest src = .error e) := by
  have hdhi := linAx_len dest hd
  have hshi := linAx_len src hs
  have hdlo := bnd (linearAxis dest).lo
  have hslo := bnd (linearAxis src).lo
  have hdb := bnd (linearAxis dest).hi
  have hsb := bnd (linearAxis src).hi
  have hdwf := linearAxis_wf dest hd
  by_cases he : src.data.length = 0
  · have hE : isemptyA src = true := by rw [isemptyA_eq src hs]; simp [he]
    refine ⟨fun _ => ?_, fun h => by omega⟩
    simp only [copytoUnaliasedS, hE, if_true]
    rw [he, List.drop_zero, List.eq_nil_of_length_eq_zero he, List.nil_append]
  have hE : isemptyA src = false := by rw [isemptyA_eq src hs]; simp [he]
  -- the bounds check
  have hc1 : checkindex (linearAxis dest) ((linearAxis src).lo + ((linearAxis dest).lo - (linearAxis src).lo)) =
      decide (1 ≤ dest.data.length) := by
    rw [checkindex_eq hdwf, vadd, vsub, wrap_add]
    rw [show (linearAxis src).lo.val + ((linearAxis dest).lo.val - (linearAxis src).lo.val) =
      (linearAxis dest).lo.val by omega, wrap_id _ (by omega) (by omega)]
    simp only [decide_eq_decide]; omega
  have hc2 : checkindex (linearAxis dest) ((linearAxis src).hi + ((linearAxis dest).lo - (linearAxis src).lo)) =
      decide (src.data.length ≤ dest.data.length) := by
    rw [checkindex_eq hdwf, vadd, vsub, wrap_add]
    rw [show (linearAxis src).hi.val + ((linearAxis dest).lo.val - (linearAxis src).lo.val) =
      (linearAxis dest).lo.val + src.data.length - 1 by omega, wi]
    simp only [decide_eq_decide]
    have : (src.data.length : Int) ≤ 9223372036854775807 := by have := hs.2.1; have := hs.2.2; rw [tmax_eq] at this; omega
    omega
  refine ⟨fun hle => ?_, fun hlt => ?_⟩
  · have hc : (checkindex (linearAxis dest) ((linearAxis src).lo + ((linearAxis dest).lo - (linearAxis src).lo)) &&
        checkindex (linearAxis dest) ((linearAxis src).hi + ((linearAxis dest).lo - (linearAxis src).lo))) = true := by
      rw [hc1, hc2]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [copytoUnaliasedS, hE, Bool.false_eq_true, if_false, hc, Bool.not_true]
    have e0 : ({ dest with data := src.data.take 0 ++ dest.data.drop 0 } : Arr α) = dest := by
      cases dest; simp
    cases ds <;> cases ss <;> simp only []
    · -- IndexLinear dest, IndexLinear src
      have h := copyLL_from dest src hd hs _ (by rw [vsub]) hle (fuelOf src) 0 .rngStart
        (goodE_rngStart src) (Nat.zero_le _) (by simp [fuelOf])
      rw [e0] at h; exact h
    · -- IndexLinear dest, IndexCartesian src
      have h := copyLC_from dest src hd hs hle (fuelOf src) 0 (iterStart src) ((linearAxis dest).lo - i64 1)
        (good_start src) (Nat.zero_le _) (by simp [fuelOf])
        (by rw [vsub, one_val]; congr 1; omega)
      rw [e0] at h; exact h
    all_goals
      have hne : 1 ≤ src.data.length := by omega
      by_cases hit : iterEq dest src = true
      · rw [if_pos hit]
        -- equal iterators: same length, and `src` reads at `dest`'s indices hit the same positions
        unfold iterEq at hit
        rcases hrd : eachRange dest <;> rcases hrs : eachRange src <;> rw [hrd, hrs] at hit <;>
          simp only [Bool.false_eq_true] at hit
        · -- two CartesianIndices
          have hpos := (totalLen_pos_iff src.axes hs.1).mp (by have := hs.2.1; omega)
          have hpos' : ∀ r ∈ dest.axes, 1 ≤ r.len := by
            have hl := axesEq_lohi dest.axes src.axes hd.1 hs.1
            intro r hr
            have hlen := axesEq_total dest.axes src.axes hd.1 hs.1 hit
            have := (totalLen_pos_iff dest.axes hd.1).mp (by have := hd.2.1; have := hs.2.1; omega)
            exact this r hr
          have hlh := axesEq_lohi dest.axes src.axes hd.1 hs.1 hpos' hit
          have hL : src.data.length = dest.data.length := by
            have := totalLen_congr _ _ hlh; have := hd.2.1; have := hs.2.1; omega
          have hlen : dest.axes.length = src.axes.length := by
            have := congrArg List.length hlh; simpa using this
          have h := copyShared_from dest src hd hs hL (fun j I _ hp hl _ => by
              refine ⟨by rw [← refPos_congr dest src hlh]; exact hp, by rw [← hlen]; exact hl⟩)
            (fuelOf dest) 0 (eachStart dest) (goodE_start dest) (Nat.zero_le _) (by simp [fuelOf])
          rw [e0] at h; exact h
        · -- two unit ranges
          have hsn : 1 ≤ (linearAxis src).len := by rw [len_def]; omega
          have hdwf' := linearAxis_wf src hs
          obtain ⟨e1, e2⟩ := axEq_vals hdwf hdwf' hit (by
            have := axEq_len hdwf hdwf' hit; omega)
          have hL : src.data.length = dest.data.length := by omega
          have h := copyShared_from dest src hd hs hL (fun j I hj hp _ hsing => by
              obtain ⟨k, rfl⟩ := hsing hrd
              have hk := refLinPos_some dest hd k.val j hp
              have hst := refLin_step src hs j (by omega)
              rw [if_pos (by omega), ← e1, ← hk, wrap_id _ (bnd k).1 (bnd k).2] at hst
              exact ⟨hst, Or.inr rfl⟩)
            (fuelOf dest) 0 (eachStart dest) (goodE_start dest) (Nat.zero_le _) (by simp [fuelOf])
          rw [e0] at h; exact h
      · rw [if_neg hit]
        have h := mapLoop_from id dest src hd hs (fuelOf dest) 0 (eachStart dest) (eachStart src)
          (goodE_start dest) (goodE_start src) (Nat.zero_le _) (Nat.zero_le _) (by simp [fuelOf])
        have e1 : ({ dest with data := (src.data.take 0).map id ++ dest.data.drop 0 } : Arr α) = dest := by
          cases dest; simp
        rw [e1, List.take_of_length_le hle, List.map_id] at h
        exact h
  · have hc : (checkindex (linearAxis dest) ((linearAxis src).lo + ((linearAxis dest).lo - (linearAxis src).lo)) &&
        checkindex (linearAxis dest) ((linearAxis src).hi + ((linearAxis dest).lo - (linearAxis src).lo))) = false := by
      rw [hc2]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
    refine ⟨.boundsError, ?_⟩
    simp only [copytoUnaliasedS, hE, Bool.false_eq_true, if_false, hc, Bool.not_false, if_true]

/-- The element loop of `_copyto_bitarray!` into a destination whose linear indices start
at 1. -/
theorem bitLoop_from {α : Type} (dest src : Arr α) (hd : dest.WF) (hs : src.WF)
    (hlo : (linearAxis dest).lo.val = 1) (hle : src.data.length ≤ dest.data.length) :
    ∀ (n j : Nat) (st : IterState) (k : I64), GoodE src j st → j ≤ src.data.length →
      src.data.length - j < n → k.val = wrapInt .i64 (1 + j) →
      bitLoop src n { dest with data := src.data.take j ++ dest.data.drop j } k st =
        .ok { dest with data := src.data ++ dest.data.drop src.data.length } := by
  intro n
  induction n with
  | zero => intro j st _ _ _ h; omega
  | succ n ih =>
    intro j st k hg hj hn hk
    by_cases h1 : j < src.data.length
    · have hj1 : j + 1 ≤ src.data.length := h1
      have hn1 : src.data.length - (j + 1) < n := by omega
      have hjd : j < dest.data.length := by omega
      have hlen : (src.data.take j ++ dest.data.drop j).length = dest.data.length := by
        simp only [List.length_append, List.length_take, List.length_drop]; omega
      have hD : ({ dest with data := src.data.take j ++ dest.data.drop j } : Arr α).WF :=
        ⟨hd.1, by rw [← hd.2.1]; exact congrArg _ hlen, hd.2.2⟩
      have hst := refLin_step dest hd j (by omega)
      rw [if_pos hjd, hlo] at hst
      have hpD : refPos { dest with data := src.data.take j ++ dest.data.drop j } [k] = some j := by
        rw [refPos_data]; show refLinPos dest k.val = some j; rw [hk, hst]
      obtain ⟨s1, -⟩ := each_step src hs j st hg hj
      obtain ⟨I, st', hs1, hIl, hIp, hg'⟩ := s1 h1
      rw [bitLoop, hs1]
      simp only []
      rw [getindex_at src hs I j hIl hIp, bind_ok,
        setindex_at _ hD [k] j _ (Or.inr rfl) hpD, bind_ok]
      simp only []
      rw [set_prefix_id src.data dest.data j h1 hjd]
      exact ih (j + 1) st' (k + i64 1) hg' hj1 hn1 (by rw [vadd, one_val, hk, wrap_add']; congr 1 <;> omega)
    · have e3 : j = src.data.length := by omega
      obtain ⟨-, s2⟩ := each_step src hs j st hg hj
      rw [bitLoop, s2 e3]
      simp only []
      rw [e3, List.take_length]

theorem linearAxis_lo_oneTo {α : Type} (A : Arr α) (hA : A.WF) (h : ∀ r ∈ A.axes, r.kind = .oneTo) :
    (linearAxis A).lo.val = 1 := by
  unfold linearAxis
  rcases hax : A.axes with _ | ⟨r, _ | ⟨r2, rs⟩⟩
  · rfl
  · show (axes1 A).lo.val = 1
    unfold axes1; rw [hax]
    exact (hA.1 r (by simp [hax])).1 (h r (by simp [hax]))
  · rfl

theorem unaliasA_eq {α : Type} (aliased : Bool) (src : Arr α) : unaliasA aliased src = src := by
  cases aliased <;> rfl

theorem copytoPrefix_proven : CopytoPrefix := by
  intro α destBit aliased dest src hd hs hbit
  by_cases he : src.data.length = 0
  · have hE : isemptyA src = true := by rw [isemptyA_eq src hs]; simp [he]
    refine ⟨fun _ => ?_, fun h => by omega⟩
    simp only [copytoA, hE, if_true]
    rw [he, List.drop_zero, List.eq_nil_of_length_eq_zero he, List.nil_append]
  have hE : isemptyA src = false := by rw [isemptyA_eq src hs]; simp [he]
  cases destBit
  · simp only [copytoA, hE, Bool.false_eq_true, if_false, unaliasA_eq, copytoUnaliased]
    exact copytoUnaliasedS_prefix _ _ dest src hd hs
  · obtain ⟨-, hone⟩ := hbit rfl
    have hlo := linearAxis_lo_oneTo dest hd hone
    have hl0 : (lengthA src == i64 0) = false := by
      rw [beq64, lengthA_val src hs, zero_val]; simp [he]
    have hlt : decide (lengthA dest < lengthA src) = decide (dest.data.length < src.data.length) := by
      rw [decide_lt64, lengthA_val dest hd, lengthA_val src hs]; simp
    refine ⟨fun hle => ?_, fun hlt' => ⟨.boundsError, ?_⟩⟩
    · have hnl : ¬ lengthA dest < lengthA src := by
        intro h; have := of_decide_eq_true (hlt ▸ decide_eq_true h); omega
      simp only [copytoA, hE, Bool.false_eq_true, if_false, if_true, copytoBitarray, hl0, hnl]
      have h := bitLoop_from dest src hd hs hlo hle (fuelOf src) 0 (eachStart src) (i64 1)
        (goodE_start src) (Nat.zero_le _) (by simp [fuelOf]) (by rw [one_val]; decide)
      have e0 : ({ dest with data := src.data.take 0 ++ dest.data.drop 0 } : Arr α) = dest := by
        cases dest; simp
      rw [e0] at h; exact h
    · have hl : lengthA dest < lengthA src := of_decide_eq_true (by rw [hlt]; exact decide_eq_true hlt')
      simp only [copytoA, hE, Bool.false_eq_true, if_false, if_true, copytoBitarray, hl0, hl]

theorem copytoStylesPrefix_proven : CopytoStylesPrefix := by
  intro α ds ss aliased dest src hd hs
  by_cases he : src.data.length = 0
  · have hE : isemptyA src = true := by rw [isemptyA_eq src hs]; simp [he]
    refine ⟨fun _ => ?_, fun h => by omega⟩
    simp only [copytoStyles, hE, if_true]
    rw [he, List.drop_zero, List.eq_nil_of_length_eq_zero he, List.nil_append]
  have hE : isemptyA src = false := by rw [isemptyA_eq src hs]; simp [he]
  simp only [copytoStyles, hE, Bool.false_eq_true, if_false, unaliasA_eq]
  exact copytoUnaliasedS_prefix _ _ dest src hd hs

theorem copyEqual_proven : CopyEqual := by
  intro α A hA hk junk hj
  have hall : A.axes.all (fun r => decide (r.kind = .oneTo)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]; exact hk
  have hax : A.axes.map (fun r => oneTo r.hi) = A.axes := by
    conv => rhs; rw [← List.map_id A.axes]
    apply List.map_congr_left
    intro r hr
    obtain ⟨k, lo, hi⟩ := r
    have hk' : k = .oneTo := hk _ hr
    have hlo : lo.val = 1 := (hA.1 _ hr).1 hk'
    subst hk'
    simp only [oneTo, id, Ax.mk.injEq, true_and, and_true]
    exact ext64 (by rw [hlo, one_val])
  have hS : (⟨A.axes, .linear, junk⟩ : Arr α).WF := ⟨hA.1, by rw [← hA.2.1, hj], hA.2.2⟩
  have h := (copytoPrefix_proven false false ⟨A.axes, .linear, junk⟩ A hS hA (by simp)).1 (by simp [hj])
  simp only [copyA, similarArr, hall, if_true, Option.map_some, hax, h, List.drop_eq_nil_of_le (by simp [hj] : junk.length ≤ A.data.length), List.append_nil]

end JuliaLean.AbstractArraySpecs
