import JuliaLean.AbstractArraySpecs.MutRowsProofs

/-! Proofs of the `map_n!` and `map!(f, dest, As...)` row contracts. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

/-! ## The reference values, built one position at a time -/

/-- The reference values at positions `0, ..., k - 1`. -/
def refUpTo {β : Type} (g : Nat → Option β) (k : Nat) : List β := (List.range k).filterMap g

theorem refUpTo_succ {β : Type} (g : Nat → Option β) (k : Nat) :
    refUpTo g (k + 1) = refUpTo g k ++ (g k).toList := by
  unfold refUpTo
  rw [List.range_succ, List.filterMap_append]
  cases h : g k <;> simp [h]

theorem refUpTo_length {β : Type} (g : Nat → Option β) (m : Nat) (hg : ∀ k < m, (g k).isSome) :
    ∀ k, k ≤ m → (refUpTo g k).length = k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [refUpTo_succ, List.length_append, refUpTo_length g m hg k (by omega)]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hg k (by omega))
    rw [hx]; simp

theorem refUpTo_take {β : Type} (g : Nat → Option β) (m : Nat) (hg : ∀ k < m, (g k).isSome) (j : Nat) :
    ∀ k, j ≤ k → k ≤ m → (refUpTo g k).take j = refUpTo g j
  | 0, hj, _ => by rw [show j = 0 by omega]; rfl
  | k + 1, hj, hk => by
    by_cases h : j = k + 1
    · rw [h, List.take_of_length_le (by rw [refUpTo_length g m hg (k + 1) hk]; omega)]
    · rw [refUpTo_succ, List.take_append_of_le_length (by rw [refUpTo_length g m hg k (by omega)]; omega),
        refUpTo_take g m hg j k (by omega) (by omega)]

/-- The shortest length among the lists. -/
def minLen {β : Type} (ls : List (List β)) : Nat := (ls.map List.length).min?.getD 0

theorem minLen_spec {β : Type} (ls : List (List β)) (hne : ls ≠ []) :
    (∀ l ∈ ls, minLen ls ≤ l.length) ∧ ∃ l ∈ ls, l.length = minLen ls := by
  unfold minLen
  cases h : (ls.map List.length).min? with
  | none =>
    rw [List.min?_eq_none_iff, List.map_eq_nil_iff] at h
    exact absurd h hne
  | some a =>
    obtain ⟨h1, h2⟩ := List.min?_eq_some_iff.mp h
    simp only [Option.getD_some]
    refine ⟨fun l hl => h2 _ (List.mem_map_of_mem hl), ?_⟩
    obtain ⟨l, hl, e⟩ := List.mem_map.mp h1
    exact ⟨l, hl, e⟩

theorem mapM_getElem_some {β : Type} (k : Nat) :
    ∀ (ls : List (List β)), (∀ l ∈ ls, k < l.length) → ∃ xs, ls.mapM (·[k]?) = some xs
  | [], _ => ⟨[], rfl⟩
  | l :: ls, h => by
    obtain ⟨xs, e⟩ := mapM_getElem_some k ls (fun x hx => h x (by simp [hx]))
    refine ⟨l[k]'(h l (by simp)) :: xs, ?_⟩
    simp [List.mapM_cons, e, List.getElem?_eq_getElem (h l (by simp))]

/-- `f` of the `k`-th elements of the sources, if they all have one. -/
def mapNVal {α : Type} (f : List α → α) (As : List (Arr α)) (k : Nat) : Option α :=
  ((As.map (·.data)).mapM (·[k]?)).map f

theorem mapNRef_eq {α : Type} (f : List α → α) (As : List (Arr α)) :
    mapNRef f (As.map (·.data)) = refUpTo (mapNVal f As) (minLen (As.map (·.data))) := rfl

theorem mapNVal_some {α : Type} (f : List α → α) (As : List (Arr α)) (hne : As ≠ []) :
    ∀ k < minLen (As.map (·.data)), (mapNVal f As k).isSome := by
  intro k hk
  have hne' : As.map (·.data) ≠ [] := by simpa using hne
  obtain ⟨h1, -⟩ := minLen_spec _ hne'
  obtain ⟨xs, e⟩ := mapM_getElem_some k _ (fun l hl => Nat.lt_of_lt_of_le hk (h1 l hl))
  simp [mapNVal, e]

/-- Writing position `j` right after a prefix of length `j`. -/
theorem set_after {α : Type} (P d : List α) (j : Nat) (y : α) (hP : P.length = j) (hj : j < d.length) :
    (P ++ d.drop j).set j y = (P ++ [y]) ++ d.drop (j + 1) := by
  rw [List.set_append_right _ _ (by omega), hP, Nat.sub_self, List.drop_eq_getElem_cons hj,
    List.set_cons_zero, List.append_assoc, List.singleton_append]

/-! ## Reading all sources at one position -/

theorem ithAll_at {α : Type} (i : I64) (j : Nat) :
    ∀ (As : List (Arr α)), (∀ a ∈ As, a.WF ∧ refPos a [i] = some j) →
      ∃ xs, ithAll i As = .ok xs ∧ (As.map (·.data)).mapM (·[j]?) = some xs
  | [], _ => ⟨[], rfl, rfl⟩
  | a :: as, h => by
    obtain ⟨ha, hp⟩ := h a (by simp)
    obtain ⟨xs, e1, e2⟩ := ithAll_at i j as (fun x hx => h x (by simp [hx]))
    have hlt := refPos_lt a ha [i] j hp
    refine ⟨a.data[j]'hlt :: xs, ?_, ?_⟩
    · rw [ithAll, getindex_at a ha [i] j (Or.inr rfl) hp, bind_ok, e1, bind_ok]
    · simp [List.mapM_cons, e2, List.getElem?_eq_getElem hlt]

/-- Each source's index list selects position `j`. -/
def PosAll {α : Type} (j : Nat) : List (Arr α) → List (List I64) → Prop
  | [], [] => True
  | a :: as, I :: Is => a.WF ∧ (a.axes.length ≤ I.length ∨ I.length = 1) ∧ refPos a I = some j ∧ PosAll j as Is
  | _, _ => False

/-- Each source's `eachindex` iteration is before position `j`. -/
def GoodAll {α : Type} (j : Nat) : List (Arr α) → List IterState → Prop
  | [], [] => True
  | a :: as, s :: ss => GoodE a j s ∧ GoodAll j as ss
  | _, _ => False

theorem goodAll_start {α : Type} : ∀ (As : List (Arr α)), GoodAll 0 As (As.map eachStart)
  | [] => trivial
  | a :: as => ⟨goodE_start a, goodAll_start as⟩

theorem getAll_at {α : Type} (j : Nat) :
    ∀ (As : List (Arr α)) (Is : List (List I64)), PosAll j As Is →
      ∃ xs, getAll As Is = .ok xs ∧ (As.map (·.data)).mapM (·[j]?) = some xs
  | [], [], _ => ⟨[], rfl, rfl⟩
  | a :: as, I :: Is, ⟨ha, hle, hp, hrest⟩ => by
    obtain ⟨xs, e1, e2⟩ := getAll_at j as Is hrest
    have hlt := refPos_lt a ha I j hp
    refine ⟨a.data[j]'hlt :: xs, ?_, ?_⟩
    · rw [getAll, getindex_at a ha I j hle hp, bind_ok, e1, bind_ok]
    · simp [List.mapM_cons, e2, List.getElem?_eq_getElem hlt]

theorem stepAll_step {α : Type} (j : Nat) (As : List (Arr α)) :
    ∀ (ss : List IterState), (∀ a ∈ As, a.WF) → GoodAll j As ss →
      (∀ a ∈ As, j ≤ a.data.length) →
      ((∀ a ∈ As, j < a.data.length) →
        ∃ Is ss', stepAll As ss = some (Is, ss') ∧ PosAll j As Is ∧ GoodAll (j + 1) As ss') ∧
      ((∃ a ∈ As, j = a.data.length) → stepAll As ss = none) := by
  induction As with
  | nil =>
    intro ss _ hg _
    cases ss with
    | nil => exact ⟨fun _ => ⟨[], [], rfl, trivial, trivial⟩, fun ⟨_, h, _⟩ => by simp at h⟩
    | cons _ _ => simp only [GoodAll] at hg
  | cons a as ih =>
    intro ss hwf hg hle
    cases ss with
    | nil => simp only [GoodAll] at hg
    | cons s ss =>
      obtain ⟨ga, grest⟩ := hg
      have ha := hwf a (by simp)
      obtain ⟨r1, r2⟩ := ih ss (fun x hx => hwf x (by simp [hx])) grest (fun x hx => hle x (by simp [hx]))
      obtain ⟨s1, s2⟩ := each_step a ha j s ga (hle a (by simp))
      refine ⟨fun h => ?_, fun ⟨b, hb, e⟩ => ?_⟩
      · obtain ⟨I, s', hs, hIl, hIp, gs'⟩ := s1 (h a (by simp))
        obtain ⟨Is, ss', hss, hP, hG⟩ := r1 (fun x hx => h x (by simp [hx]))
        refine ⟨I :: Is, s' :: ss', ?_, ⟨ha, hIl, hIp, hP⟩, ⟨gs', hG⟩⟩
        simp only [stepAll, hs, hss, Option.map_some]
      · rcases List.mem_cons.mp hb with rfl | hb'
        · simp only [stepAll, s2 e]
        · rcases hs : eachindexStep a s with _ | ⟨I, s'⟩
          · simp only [stepAll, hs]
          · simp only [stepAll, hs, r2 ⟨b, hb', e⟩, Option.map_none]

/-! ## The two loops of `map_n!` -/

theorem mapNZip_from {α : Type} (f : List α → α) (dest : Arr α) (As : List (Arr α)) (hd : dest.WF)
    (hAs : ∀ a ∈ As, a.WF) (hne : As ≠ []) :
    ∀ (n j : Nat) (sd : IterState) (ss : List IterState), GoodE dest j sd → GoodAll j As ss →
      j ≤ dest.data.length → j ≤ minLen (As.map (·.data)) → dest.data.length - j < n →
      mapNZip f As n { dest with data := refUpTo (mapNVal f As) j ++ dest.data.drop j } sd ss =
        .ok { dest with data := refUpTo (mapNVal f As) (min dest.data.length (minLen (As.map (·.data)))) ++
          dest.data.drop (minLen (As.map (·.data))) } := by
  have hne' : As.map (·.data) ≠ [] := by simpa using hne
  obtain ⟨hmin, ⟨l0, hl0, el0⟩⟩ := minLen_spec _ hne'
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp hl0
  have hsome := mapNVal_some f As hne
  have hlen := refUpTo_length _ _ hsome
  have hmin' : ∀ a ∈ As, minLen (As.map (·.data)) ≤ a.data.length :=
    fun a ha => hmin _ (List.mem_map_of_mem ha)
  intro n
  induction n with
  | zero => intro j sd ss _ _ _ _ h; omega
  | succ n ih =>
    intro j sd ss gd gs hjd hjm hn
    have hjl : j + (dest.data.length - j) = dest.data.length := by omega
    obtain ⟨d1, d2⟩ := each_step dest hd j sd gd hjd
    obtain ⟨r1, r2⟩ := stepAll_step j As ss hAs gs (fun a ha => Nat.le_trans hjm (hmin' a ha))
    by_cases h1 : j < dest.data.length
    · have hn1 : dest.data.length - (j + 1) < n := by omega
      obtain ⟨I, sd', hsd, hIl, hIp, gd'⟩ := d1 h1
      by_cases h2 : j < minLen (As.map (·.data))
      · obtain ⟨Is, ss', hss, hP, hG⟩ := r1 (fun a ha => Nat.lt_of_lt_of_le h2 (hmin' a ha))
        obtain ⟨xs, e1, e2⟩ := getAll_at j As Is hP
        have hPl : (refUpTo (mapNVal f As) j).length = j := hlen j (by omega)
        have hD : ({ dest with data := refUpTo (mapNVal f As) j ++ dest.data.drop j } : Arr α).WF :=
          wf_data dest _ hd (by rw [List.length_append, hPl, List.length_drop]; exact hjl)
        rw [mapNZip, eachindexStep_data, hsd]
        simp only []
        rw [hss]
        simp only []
        rw [e1, bind_ok, setindex_at _ hD I j _ hIl (by rw [refPos_data]; exact hIp), bind_ok]
        simp only []
        have hv : mapNVal f As j = some (f xs) := by simp [mapNVal, e2]
        rw [set_after _ dest.data j (f xs) hPl h1,
          show refUpTo (mapNVal f As) j ++ [f xs] = refUpTo (mapNVal f As) (j + 1) by
            rw [refUpTo_succ, hv]; rfl]
        exact ih (j + 1) sd' ss' gd' hG h1 h2 hn1
      · have e3 : j = minLen (As.map (·.data)) := by omega
        rw [mapNZip, eachindexStep_data, hsd]
        simp only []
        rw [r2 ⟨a0, ha0, by rw [e3, el0]⟩]
        simp only []
        rw [Nat.min_eq_right (by omega), e3]
    · have e3 : j = dest.data.length := by omega
      rw [mapNZip, eachindexStep_data, d2 e3]
      simp only []
      rw [Nat.min_eq_left (by omega), e3, List.drop_length,
        List.drop_eq_nil_of_le (show dest.data.length ≤ minLen (As.map (·.data)) by omega)]

theorem totalLen_pos_axes (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) (h : 0 < totalLen axs) :
    ∀ r ∈ axs, 1 ≤ r.len := by
  induction axs with
  | nil => simp
  | cons r rs ih =>
    rw [totalLen_cons] at h
    have hr := (hwf r (by simp)).2.1
    have hrs := totalLen_nonneg rs (fun x hx => hwf x (by simp [hx]))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases Int.lt_or_eq_of_le hr with h' | h'
      · omega
      · rw [← h', Int.zero_mul] at h; omega
    · have hpos : 0 < totalLen rs := by
        rcases Int.lt_or_eq_of_le hrs with h' | h'
        · exact h'
        · rw [← h', Int.mul_zero] at h; omega
      exact ih (fun y hy => hwf y (by simp [hy])) hpos x hx'

theorem refPos_linView {α : Type} (A : Arr α) (I : List I64) : refPos (linView A) I = refPos A I := rfl

theorem mapNLin_from {α : Type} (f : List α → α) (D0 : Arr α) (As : List (Arr α)) (hd : D0.WF)
    (hAs : ∀ a ∈ As, a.WF) (hax : ∀ a ∈ As, axesEq a.axes D0.axes = true) :
    ∀ (n j : Nat) (st : IterState), GoodE (linView D0) j st → j ≤ D0.data.length →
      D0.data.length - j < n →
      mapNLin f D0 As n { D0 with data := refUpTo (mapNVal f As) j ++ D0.data.drop j } st =
        .ok { D0 with data := refUpTo (mapNVal f As) D0.data.length } := by
  have hdL : (linView D0).WF := hd
  have hlenA : ∀ a ∈ As, a.data.length = D0.data.length := by
    intro a ha
    have h1 := (hAs a ha).2.1; have h2 := hd.2.1
    have := axesEq_total a.axes D0.axes (hAs a ha).1 hd.1 (hax a ha)
    omega
  intro n
  induction n with
  | zero => intro j st _ _ h; omega
  | succ n ih =>
    intro j st hg hj hn
    have hstep := eachindexStep_linView D0 j st hg
    by_cases h1 : j < D0.data.length
    · obtain ⟨i, st', hs1, -, hp, hg'⟩ := each_step_range (linView D0) hdL (linView_eachRange D0) j st hg h1
      rw [refPos_linView] at hp
      have hpos : 0 < totalLen D0.axes := by have := hd.2.1; omega
      have hall : ∀ a ∈ As, a.WF ∧ refPos a [i] = some j := by
        intro a ha
        have haw := hAs a ha
        have hta : 0 < totalLen a.axes := by have := haw.2.1; have := hlenA a ha; omega
        have hl := axesEq_lohi a.axes D0.axes haw.1 hd.1 (totalLen_pos_axes a.axes haw.1 hta) (hax a ha)
        exact ⟨haw, by rw [refPos_congr a D0 hl]; exact hp⟩
      obtain ⟨xs, e1, e2⟩ := ithAll_at i j As hall
      have hsome : ∀ k < D0.data.length, (mapNVal f As k).isSome := by
        intro k hk
        obtain ⟨ys, e⟩ := mapM_getElem_some k (As.map (·.data)) (by
          intro l hl; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl; rw [hlenA a ha]; exact hk)
        simp [mapNVal, e]
      have hPl : (refUpTo (mapNVal f As) j).length = j := refUpTo_length _ _ hsome j (by omega)
      have hD : ({ D0 with data := refUpTo (mapNVal f As) j ++ D0.data.drop j } : Arr α).WF :=
        wf_data D0 _ hd (by rw [List.length_append, hPl, List.length_drop]; omega)
      rw [mapNLin, hstep, hs1]
      simp only [List.headD_cons]
      rw [e1, bind_ok, setindex_at _ hD [i] j _ (Or.inr rfl) (by rw [refPos_data]; exact hp), bind_ok]
      have hv : mapNVal f As j = some (f xs) := by simp [mapNVal, e2]
      rw [set_after _ D0.data j (f xs) hPl h1,
        show refUpTo (mapNVal f As) j ++ [f xs] = refUpTo (mapNVal f As) (j + 1) by
          rw [refUpTo_succ, hv]; rfl]
      exact ih (j + 1) st' hg' h1 (by omega)
    · have e3 : j = D0.data.length := by omega
      obtain ⟨-, s2⟩ := each_step (linView D0) hdL j st hg hj
      rw [mapNLin, hstep, s2 e3]
      simp only []
      rw [e3, List.drop_length, List.append_nil]

/-! ## The contracts -/

theorem mapNPrefix_proven : MapNPrefix := by
  intro α f dest As hd hAs hne
  simp only []
  rw [mapNRef_eq]
  have hne' : As.map (·.data) ≠ [] := by simpa using hne
  have hsome := mapNVal_some f As hne
  have hrl := refUpTo_length _ _ hsome (minLen (As.map (·.data))) (Nat.le_refl _)
  rw [hrl]
  unfold mapN
  have hinit : ({ dest with data := refUpTo (mapNVal f As) 0 ++ dest.data.drop 0 } : Arr α) = dest := by
    cases dest; rfl
  by_cases hlin : As.all (fun x => linIdxEq x dest) = true
  · rw [if_pos hlin]
    have hax : ∀ a ∈ As, axesEq a.axes dest.axes = true := fun a ha => List.all_eq_true.mp hlin a ha
    have hlenA : ∀ a ∈ As, a.data.length = dest.data.length := by
      intro a ha
      have h1 := (hAs a ha).2.1; have h2 := hd.2.1
      have := axesEq_total a.axes dest.axes (hAs a ha).1 hd.1 (hax a ha)
      omega
    have hm : minLen (As.map (·.data)) = dest.data.length := by
      obtain ⟨-, l, hl, el⟩ := minLen_spec _ hne'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
      rw [← el, hlenA a ha]
    have h := mapNLin_from f dest As hd hAs hax (fuelOf dest) 0 .rngStart (goodE_rngStart dest)
      (Nat.zero_le _) (by simp [fuelOf])
    rw [hinit] at h
    rw [h, hm, List.take_of_length_le (by rw [← hm]; exact Nat.le_of_eq hrl), List.drop_length,
      List.append_nil]
  · rw [if_neg hlin]
    have h := mapNZip_from f dest As hd hAs hne (fuelOf dest) 0 _ _ (goodE_start dest) (goodAll_start As)
      (Nat.zero_le _) (Nat.zero_le _) (by simp [fuelOf])
    rw [hinit] at h
    rw [h]
    rcases Nat.le_total dest.data.length (minLen (As.map (·.data))) with hle | hle
    · rw [Nat.min_eq_left hle, refUpTo_take _ _ hsome _ _ hle (Nat.le_refl _)]
    · rw [Nat.min_eq_right hle, List.take_of_length_le (by rw [hrl]; exact hle)]

theorem mapBangNPrefix_proven : MapBangNPrefix := by
  intro α f dest As hd hAs hne
  have h := mapNPrefix_proven f dest As hd hAs hne
  simp only [] at h ⊢
  unfold mapBangN
  rw [if_neg (by cases As with | nil => exact absurd rfl hne | cons _ _ => simp)]
  exact h

end JuliaLean.AbstractArraySpecs
