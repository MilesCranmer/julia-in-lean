import JuliaLean.Paths.Props

/-!
# `normpath` and `abspath`: idempotence, canonical form, lexical meaning
-/

namespace JuliaLean.Paths.Norm

open JuliaLean.Paths

/-- No separator in `x`. -/
def SepFree (x : Str) : Prop := ∀ c ∈ x, isSep c = false

/-- A normalized component: nonempty, separator-free and not `.`. -/
def Good (x : Str) : Prop := x ≠ [] ∧ SepFree x ∧ x ≠ ['.']

theorem isSep_slash : isSep '/' = true := by decide

theorem sepFree_nil : SepFree [] := by
  intro c hc
  simp at hc

theorem sepFree_head {t : Str} (ht : SepFree t) : ∀ c, t.head? = some c → isSep c = false := by
  intro c hc
  cases t with
  | nil => simp at hc
  | cons a t' =>
    simp at hc
    subst hc
    exact ht _ (by simp)

theorem sepFree_dotdot : SepFree dotdot := by
  intro c hc
  simp [dotdot] at hc
  subst hc
  decide

theorem good_dotdot : Good dotdot := ⟨by simp [dotdot], sepFree_dotdot, by simp [dotdot]⟩

/-! ## `splitRuns` -/

theorem splitRuns_cons_eq {c : Char} {cs w : Str} {ws : List Str} (h : splitRuns cs = w :: ws) :
    splitRuns (c :: cs) =
      if isSep c then (if cs.head?.map isSep == some true then w :: ws else [] :: w :: ws)
      else (c :: w) :: ws := by
  rw [splitRuns, h]

theorem splitRuns_ne_nil (p : Str) : splitRuns p ≠ [] := by
  cases p with
  | nil => simp [splitRuns]
  | cons c cs =>
    cases h : splitRuns cs with
    | nil => rw [splitRuns, h]; simp
    | cons w ws =>
      rw [splitRuns_cons_eq h]
      split
      · split <;> simp
      · simp

theorem splitRuns_cons_exists (p : Str) : ∃ w ws, splitRuns p = w :: ws := by
  cases h : splitRuns p with
  | nil => exact absurd h (splitRuns_ne_nil p)
  | cons w ws => exact ⟨w, ws, rfl⟩

theorem splitRuns_sepFree_append {w : Str} (hw : SepFree w) {s h : Str} {t : List Str}
    (hs : splitRuns s = h :: t) : splitRuns (w ++ s) = (w ++ h) :: t := by
  induction w with
  | nil => simpa using hs
  | cons c w ih =>
    have hc : isSep c = false := hw c (by simp)
    have ih' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    rw [List.cons_append, splitRuns_cons_eq ih', hc]
    simp

theorem splitRuns_slash {s : Str} (hs : ∀ c, s.head? = some c → isSep c = false) :
    splitRuns ('/' :: s) = [] :: splitRuns s := by
  obtain ⟨w, ws, h⟩ := splitRuns_cons_exists s
  have hb : (s.head?.map isSep == some true) = false := by
    cases hh : s.head? with
    | none => rfl
    | some c => simp [hs c hh]
  rw [splitRuns_cons_eq h, h, isSep_slash, hb]
  simp

theorem splitRuns_sepFree {t : Str} (ht : SepFree t) : splitRuns t = [t] := by
  have := splitRuns_sepFree_append ht (s := []) (h := []) (t := []) rfl
  simpa using this

theorem splitRuns_mem_sepFree : ∀ (p : Str), ∀ x ∈ splitRuns p, SepFree x
  | [], x, hx => by
    simp [splitRuns] at hx
    subst hx
    exact sepFree_nil
  | c :: cs, x, hx => by
    obtain ⟨w, ws, h⟩ := splitRuns_cons_exists cs
    have ih := splitRuns_mem_sepFree cs
    rw [h] at ih
    rw [splitRuns_cons_eq h] at hx
    by_cases hc : isSep c = true
    · rw [if_pos hc] at hx
      split at hx
      · exact ih x hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact sepFree_nil
        · exact ih x hx
    · rw [if_neg hc] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · intro d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · simpa using hc
        · exact ih w (by simp) d hd
      · exact ih x (List.mem_cons_of_mem _ hx)

/-- The pieces of `q ++ s` end like those of `s` once `s` has at least two pieces. -/
theorem splitRuns_append_last (s : Str) (u z : Str) (v : List Str)
    (hs : splitRuns s = (u :: v) ++ [z]) :
    ∀ q : Str, ∃ u' v', splitRuns (q ++ s) = (u' :: v') ++ [z]
  | [] => ⟨u, v, by simpa using hs⟩
  | c :: q => by
    obtain ⟨u', v', h⟩ := splitRuns_append_last s u z v hs q
    rw [List.cons_append, splitRuns_cons_eq h]
    split
    · split
      · exact ⟨u', v', rfl⟩
      · exact ⟨[], u' :: v', rfl⟩
    · exact ⟨c :: u', v', rfl⟩

/-! ## `joinSep` -/

theorem joinSep_single (a : Str) : joinSep [a] = a := rfl

theorem joinSep_cons_cons (a b : Str) (l : List Str) :
    joinSep (a :: b :: l) = a ++ '/' :: joinSep (b :: l) := rfl

theorem joinSep_cons_exists (a : Str) (l : List Str) : ∃ r, joinSep (a :: l) = a ++ r := by
  cases l with
  | nil => exact ⟨[], by simp [joinSep_single]⟩
  | cons b l => exact ⟨_, joinSep_cons_cons a b l⟩

theorem joinSep_head {b : Str} (bs : List Str) (s : Str) (hb : b ≠ [] ∧ SepFree b) :
    ∀ c, (joinSep (b :: bs) ++ s).head? = some c → isSep c = false := by
  intro c hc
  obtain ⟨r, hr⟩ := joinSep_cons_exists b bs
  rw [hr] at hc
  cases b with
  | nil => exact absurd rfl hb.1
  | cons b0 b' =>
    simp at hc
    subst hc
    exact hb.2 _ (by simp)

theorem splitRuns_joinSep_append (s : Str) (R : List Str) (hs : splitRuns s = [] :: R) :
    ∀ (a : Str) (as : List Str), SepFree a → (∀ x ∈ as, x ≠ [] ∧ SepFree x) →
      splitRuns (joinSep (a :: as) ++ s) = (a :: as) ++ R
  | a, [], ha, _ => by
    rw [joinSep_single, splitRuns_sepFree_append ha hs]
    simp
  | a, b :: bs, ha, has => by
    have hb := has b (by simp)
    have ih := splitRuns_joinSep_append s R hs b bs hb.2 (fun x hx => has x (List.mem_cons_of_mem _ hx))
    rw [joinSep_cons_cons, List.append_assoc, List.cons_append,
      splitRuns_sepFree_append ha (splitRuns_slash (joinSep_head bs s hb)), ih]
    simp

theorem splitRuns_joinSep_list (s : Str) (R : List Str) (hs : splitRuns s = [] :: R) (Q : List Str)
    (hQ : ∀ x ∈ Q, x ≠ [] ∧ SepFree x) (hne : Q ≠ []) :
    splitRuns (joinSep Q ++ s) = Q ++ R := by
  cases Q with
  | nil => exact absurd rfl hne
  | cons a as =>
    exact splitRuns_joinSep_append s R hs a as (hQ a (by simp)).2
      (fun x hx => hQ x (List.mem_cons_of_mem _ hx))

theorem splitRuns_slash_joinSep_list (s : Str) (R : List Str) (hs : splitRuns s = [] :: R) (Q : List Str)
    (hQ : ∀ x ∈ Q, x ≠ [] ∧ SepFree x) (hne : Q ≠ []) :
    splitRuns ('/' :: (joinSep Q ++ s)) = [] :: (Q ++ R) := by
  cases Q with
  | nil => exact absurd rfl hne
  | cons a as =>
    rw [splitRuns_slash (joinSep_head as s (hQ a (by simp))),
      splitRuns_joinSep_list s R hs (a :: as) hQ hne]

/-! ## `noDoubleSep` -/

theorem nds_cons_nonsep {c : Char} (hc : isSep c = false) (s : Str) :
    noDoubleSep (c :: s) = noDoubleSep s := by
  cases s with
  | nil => rfl
  | cons b r => simp [noDoubleSep, hc]

theorem nds_sepFree_append {w : Str} (hw : SepFree w) (s : Str) :
    noDoubleSep (w ++ s) = noDoubleSep s := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [List.cons_append, nds_cons_nonsep (hw c (by simp)),
      ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))]

theorem nds_slash {s : Str} (hs : ∀ c, s.head? = some c → isSep c = false) :
    noDoubleSep ('/' :: s) = noDoubleSep s := by
  cases s with
  | nil => rfl
  | cons b r => simp [noDoubleSep, hs b rfl]

theorem nds_joinSep_append (s : Str) :
    ∀ (a : Str) (as : List Str), SepFree a → (∀ x ∈ as, x ≠ [] ∧ SepFree x) →
      noDoubleSep (joinSep (a :: as) ++ s) = noDoubleSep s
  | a, [], ha, _ => by rw [joinSep_single, nds_sepFree_append ha]
  | a, b :: bs, ha, has => by
    have hb := has b (by simp)
    rw [joinSep_cons_cons, List.append_assoc, List.cons_append, nds_sepFree_append ha,
      nds_slash (joinSep_head bs s hb),
      nds_joinSep_append s b bs hb.2 (fun x hx => has x (List.mem_cons_of_mem _ hx))]

/-! ## The `..` cancellation loop -/

theorem rfp_cons_cons (a b : Str) (rest : List Str) : removeFirstPair (a :: b :: rest) =
    if (a != dotdot && b == dotdot) = true then some rest
    else (removeFirstPair (b :: rest)).map (a :: ·) := rfl

theorem rfp_nil : removeFirstPair [] = none := rfl

theorem rfp_single (a : Str) : removeFirstPair [a] = none := rfl

theorem rfp_some {L L' : List Str} (h : removeFirstPair L = some L') :
    (∃ a rest, L = a :: dotdot :: rest ∧ a ≠ dotdot ∧ L' = rest) ∨
    (∃ a L1 L1', L = a :: L1 ∧ removeFirstPair L1 = some L1' ∧ L' = a :: L1') := by
  rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [rfp_nil] at h
  · simp [rfp_single] at h
  · rw [rfp_cons_cons] at h
    by_cases hc : (a != dotdot && b == dotdot) = true
    · rw [if_pos hc] at h
      simp at hc
      left
      exact ⟨a, rest, by rw [hc.2], hc.1, (Option.some.inj h).symm⟩
    · rw [if_neg hc] at h
      right
      cases h2 : removeFirstPair (b :: rest) with
      | none => simp [h2] at h
      | some L1' =>
        simp [h2] at h
        exact ⟨a, b :: rest, L1', rfl, h2, h.symm⟩

theorem rfp_length {L L' : List Str} (h : removeFirstPair L = some L') :
    L'.length + 2 = L.length := by
  induction L generalizing L' with
  | nil => simp [rfp_nil] at h
  | cons a L1 ih =>
    rcases rfp_some h with ⟨a', rest, hL, -, rfl⟩ | ⟨a', L2, L2', hL, h2, rfl⟩
    · rw [hL]
      simp
    · simp at hL
      obtain ⟨rfl, rfl⟩ := hL
      have := ih h2
      simp
      omega

theorem rfp_mem {L L' : List Str} (h : removeFirstPair L = some L') {x : Str} (hx : x ∈ L') :
    x ∈ L := by
  induction L generalizing L' with
  | nil => simp [rfp_nil] at h
  | cons a L1 ih =>
    rcases rfp_some h with ⟨a', rest, hL, -, rfl⟩ | ⟨a', L2, L2', hL, h2, rfl⟩
    · rw [hL]
      simp [hx]
    · simp at hL
      obtain ⟨rfl, rfl⟩ := hL
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · exact List.mem_cons_of_mem _ (ih h2 hx)

theorem resolveStep_name {x : Str} (h1 : x ≠ []) (h2 : x ≠ ['.']) (h3 : x ≠ dotdot) (st : List Str) :
    resolveStep st x = st ++ [x] := by
  simp [resolveStep, h1, h2, h3]

theorem resolveStep_dotdot (st : List Str) : resolveStep st dotdot = st.dropLast := by
  simp [resolveStep, dotdot]

theorem resolveStep_nil (st : List Str) : resolveStep st [] = st := by
  simp [resolveStep]

theorem resolveStep_dot (st : List Str) : resolveStep st ['.'] = st := by
  simp [resolveStep]

theorem rfp_fold {L L' : List Str} (h : removeFirstPair L = some L')
    (hg : ∀ x ∈ L, x ≠ [] ∧ x ≠ ['.']) (st : List Str) :
    L'.foldl resolveStep st = L.foldl resolveStep st := by
  induction L generalizing L' st with
  | nil => simp [rfp_nil] at h
  | cons a L1 ih =>
    rcases rfp_some h with ⟨a', rest, hL, ha, rfl⟩ | ⟨a', L2, L2', hL, h2, rfl⟩
    · have hg' := hg a' (by rw [hL]; simp)
      rw [hL, List.foldl_cons, List.foldl_cons, resolveStep_name hg'.1 hg'.2 ha, resolveStep_dotdot]
      simp
    · simp at hL
      obtain ⟨rfl, rfl⟩ := hL
      rw [List.foldl_cons, List.foldl_cons]
      exact ih h2 (fun x hx => hg x (List.mem_cons_of_mem _ hx)) _

theorem rfp_last {x : Str} (hx : x ≠ dotdot) {l : List Str} {L' : List Str}
    (h : removeFirstPair (l ++ [x]) = some L') : ∃ l', L' = l' ++ [x] := by
  induction l generalizing L' with
  | nil => simp [rfp_single] at h
  | cons a l1 ih =>
    rcases rfp_some h with ⟨a', rest, hL, -, rfl⟩ | ⟨a', L2, L2', hL, h2, rfl⟩
    · simp at hL
      obtain ⟨rfl, hL⟩ := hL
      cases l1 with
      | nil =>
        simp at hL
        exact absurd hL.1 hx
      | cons b l2 =>
        simp at hL
        exact ⟨l2, hL.2.symm⟩
    · simp at hL
      obtain ⟨rfl, rfl⟩ := hL
      obtain ⟨l', hl'⟩ := ih h2
      exact ⟨a :: l', by simp [hl']⟩

theorem cleanLoop_induct (P : List Str → Prop)
    (hstep : ∀ L L', removeFirstPair L = some L' → P L → P L') :
    ∀ (n : Nat) (L : List Str), P L → P (cleanLoop n L)
  | 0, _, h => h
  | n + 1, L, h => by
    cases h2 : removeFirstPair L with
    | none => simpa [cleanLoop, h2] using h
    | some L' => simpa [cleanLoop, h2] using cleanLoop_induct P hstep n L' (hstep L L' h2 h)

theorem cleanLoop_none : ∀ (n : Nat) (L : List Str), L.length + 1 ≤ n →
    removeFirstPair (cleanLoop n L) = none
  | 0, _, h => by omega
  | n + 1, L, h => by
    cases h2 : removeFirstPair L with
    | none => simp [cleanLoop, h2]
    | some L' =>
      have := rfp_length h2
      simp only [cleanLoop, h2]
      exact cleanLoop_none n L' (by omega)

theorem cleanLoop_self {L : List Str} (h : removeFirstPair L = none) : ∀ n, cleanLoop n L = L
  | 0 => rfl
  | n + 1 => by simp [cleanLoop, h]

theorem rfp_none_no_dd : ∀ (a : Str) (L : List Str), removeFirstPair (a :: L) = none →
    a ≠ dotdot → ∀ x ∈ a :: L, x ≠ dotdot
  | a, [], _, ha => by simpa using ha
  | a, b :: L, h, ha => by
    rw [rfp_cons_cons] at h
    have hb : b ≠ dotdot := by
      intro hb
      rw [if_pos (by simp [ha, hb])] at h
      cases h
    rw [if_neg (by simp [hb])] at h
    have h2 : removeFirstPair (b :: L) = none := by
      cases h3 : removeFirstPair (b :: L) with
      | none => rfl
      | some _ => simp [h3] at h
    have ih := rfp_none_no_dd b L h2 hb
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact ih x hx

theorem rfp_none_dd_tail (L : List Str) (h : removeFirstPair (dotdot :: L) = none) :
    removeFirstPair L = none := by
  cases L with
  | nil => rfl
  | cons b L =>
    rw [rfp_cons_cons, if_neg (by simp)] at h
    cases h3 : removeFirstPair (b :: L) with
    | none => rfl
    | some _ => simp [h3] at h

theorem rfp_none_shape : ∀ L : List Str, removeFirstPair L = none →
    ∃ k rest, L = List.replicate k dotdot ++ rest ∧ ∀ x ∈ rest, x ≠ dotdot
  | [], _ => ⟨0, [], rfl, by simp⟩
  | a :: L, h => by
    by_cases ha : a = dotdot
    · subst ha
      obtain ⟨k, rest, h1, h2⟩ := rfp_none_shape L (rfp_none_dd_tail L h)
      exact ⟨k + 1, rest, by rw [h1, List.replicate_succ, List.cons_append], h2⟩
    · exact ⟨0, a :: L, rfl, rfp_none_no_dd a L h ha⟩

theorem rfp_none_of_no_dd : ∀ L : List Str, (∀ x ∈ L, x ≠ dotdot) → removeFirstPair L = none
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: L, h => by
    rw [rfp_cons_cons, if_neg (by simp [h b (by simp)]),
      rfp_none_of_no_dd (b :: L) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem dropWhile_dd (k : Nat) (rest : List Str) (h : ∀ x ∈ rest, x ≠ dotdot) :
    (List.replicate k dotdot ++ rest).dropWhile (· == dotdot) = rest := by
  induction k with
  | zero =>
    cases rest with
    | nil => rfl
    | cons a r => simp [List.dropWhile_cons, h a (by simp)]
  | succ k ih => simp [List.replicate_succ, List.dropWhile_cons, ih]

theorem dropWhile_last {x : Str} (hx : x ≠ dotdot) :
    ∀ l : List Str, ∃ l', (l ++ [x]).dropWhile (· == dotdot) = l' ++ [x]
  | [] => ⟨[], by simp [List.dropWhile_cons, hx]⟩
  | a :: l => by
    by_cases ha : a = dotdot
    · obtain ⟨l', hl'⟩ := dropWhile_last hx l
      exact ⟨l', by simp [List.dropWhile_cons, ha, hl']⟩
    · exact ⟨a :: l, by simp [List.dropWhile_cons, ha]⟩

theorem foldl_rep_root (k : Nat) : (List.replicate k dotdot).foldl resolveStep [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, resolveStep_dotdot]; exact ih

theorem foldl_names (Q : List Str) (hQ : ∀ y ∈ Q, Good y ∧ y ≠ dotdot) (st : List Str) :
    Q.foldl resolveStep st = st ++ Q := by
  induction Q generalizing st with
  | nil => simp
  | cons a Q ih =>
    have ha := hQ a (by simp)
    rw [List.foldl_cons, resolveStep_name ha.1.1 ha.1.2.2 ha.2,
      ih (fun y hy => hQ y (List.mem_cons_of_mem _ hy))]
    simp

/-! ## Filters -/

theorem foldl_filter_noop (f : List Str → Str → List Str) (q : Str → Bool) :
    ∀ (l : List Str) (st : List Str), (∀ x ∈ l, q x = false → ∀ s, f s x = s) →
      (l.filter q).foldl f st = l.foldl f st
  | [], _, _ => rfl
  | a :: l, st, h => by
    have ih := foldl_filter_noop f q l
    by_cases ha : q a = true
    · rw [List.filter_cons_of_pos ha, List.foldl_cons, List.foldl_cons,
        ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    · rw [List.filter_cons_of_neg ha, List.foldl_cons, h a (by simp) (by simpa using ha),
        ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem filter_last {q : Str → Bool} {x : Str} (hq : q x = true) (l : List Str) :
    (l ++ [x]).filter q = l.filter q ++ [x] := by
  rw [List.filter_append, List.filter_cons_of_pos hq, List.filter_nil]

theorem filter_ne_nil_self (Q : List Str) (hQ : ∀ y ∈ Q, y ≠ []) :
    Q.filter (· ≠ []) = Q :=
  List.filter_eq_self.2 (fun y hy => by simpa using hQ y hy)

theorem filter_ne_nil_app (Q R : List Str) (hQ : ∀ y ∈ Q, y ≠ []) (hR : R = [] ∨ R = [[]]) :
    (Q ++ R).filter (· ≠ []) = Q := by
  rw [List.filter_append, filter_ne_nil_self Q hQ]
  rcases hR with rfl | rfl <;> simp

theorem filter_dot_self (Q : List Str) (hQ : ∀ y ∈ Q, y ≠ ['.']) :
    Q.filter (· != ['.']) = Q :=
  List.filter_eq_self.2 (fun y hy => by simpa using hQ y hy)

/-! ## Decomposition of `normpath` -/

def P0 (p : Str) : List Str := (splitAtSeps p false).filter (· != ['.'])

def CL (p : Str) : List Str := cleanLoop ((P0 p).length + 1) (P0 p)

def QQ (p : Str) : List Str :=
  if isabspath p then (CL p).dropWhile (· == dotdot)
  else if (CL p).isEmpty then [['.']] else CL p

def BB (p : Str) : Str := if isabspath p then '/' :: joinSep (QQ p) else joinSep (QQ p)

def TT (p : Str) : Str := if (isdirpath p && !isdirpath (BB p)) = true then ['/'] else []

theorem splitAtSeps_false (p : Str) : splitAtSeps p false = (splitRuns p).filter (· ≠ []) := rfl

theorem normpath_ite (p : Str) :
    normpath p = if (isdirpath p && !isdirpath (BB p)) = true then BB p ++ ['/'] else BB p := rfl

theorem normpath_eq (p : Str) : normpath p = BB p ++ TT p := by
  rw [normpath_ite, TT]
  split <;> simp

theorem TT_cases (p : Str) : TT p = [] ∨ TT p = ['/'] := by
  unfold TT
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem splitRuns_TT (p : Str) : ∃ R, (R = [] ∨ R = [[]]) ∧ splitRuns (TT p) = [] :: R := by
  rcases TT_cases p with h | h <;> rw [h]
  · exact ⟨[], Or.inl rfl, rfl⟩
  · exact ⟨[[]], Or.inr rfl, by decide⟩

theorem nds_TT (p : Str) : noDoubleSep (TT p) = true := by
  rcases TT_cases p with h | h <;> rw [h] <;> rfl

theorem mem_P0 {p x : Str} (h : x ∈ P0 p) : x ∈ splitRuns p ∧ x ≠ [] ∧ x ≠ ['.'] := by
  unfold P0 at h
  rw [splitAtSeps_false, List.mem_filter, List.mem_filter] at h
  exact ⟨h.1.1, by simpa using h.1.2, by simpa using h.2⟩

theorem P0_good {p x : Str} (h : x ∈ P0 p) : Good x := by
  obtain ⟨h1, h2, h3⟩ := mem_P0 h
  exact ⟨h2, splitRuns_mem_sepFree p x h1, h3⟩

theorem CL_props (p : Str) :
    (∀ x ∈ CL p, x ∈ P0 p) ∧ ∀ st, (CL p).foldl resolveStep st = (P0 p).foldl resolveStep st := by
  refine cleanLoop_induct
    (fun L => (∀ x ∈ L, x ∈ P0 p) ∧ ∀ st, L.foldl resolveStep st = (P0 p).foldl resolveStep st)
    ?_ _ _ ⟨fun x hx => hx, fun st => rfl⟩
  intro L L' h ⟨hm, hf⟩
  refine ⟨fun x hx => hm x (rfp_mem h hx), fun st => ?_⟩
  rw [rfp_fold h (fun x hx => ⟨(P0_good (hm x hx)).1, (P0_good (hm x hx)).2.2⟩) st, hf]

theorem CL_good {p x : Str} (h : x ∈ CL p) : Good x := P0_good ((CL_props p).1 x h)

theorem CL_none (p : Str) : removeFirstPair (CL p) = none :=
  cleanLoop_none _ _ (Nat.le_refl _)

theorem CL_fold (p : Str) (st : List Str) :
    (CL p).foldl resolveStep st = (P0 p).foldl resolveStep st := (CL_props p).2 st

theorem QQ_abs {p : Str} (h : isabspath p = true) :
    ∃ k, CL p = List.replicate k dotdot ++ QQ p ∧ ∀ y ∈ QQ p, Good y ∧ y ≠ dotdot := by
  obtain ⟨k, rest, h1, h2⟩ := rfp_none_shape _ (CL_none p)
  have hq : QQ p = rest := by
    rw [QQ, if_pos h, h1, dropWhile_dd k rest h2]
  refine ⟨k, by rw [hq, h1], fun y hy => ?_⟩
  rw [hq] at hy
  exact ⟨CL_good (by rw [h1]; exact List.mem_append_right _ hy), h2 y hy⟩

theorem QQ_rel {p : Str} (h : isabspath p = false) :
    (CL p = [] ∧ QQ p = [['.']]) ∨ (CL p ≠ [] ∧ QQ p = CL p) := by
  cases hc : CL p with
  | nil => left; exact ⟨rfl, by rw [QQ, if_neg (by simp [h]), hc]; rfl⟩
  | cons a l => right; exact ⟨by simp, by rw [QQ, if_neg (by simp [h]), hc]; rfl⟩

theorem QQ_wf (p : Str) : ∀ y ∈ QQ p, y ≠ [] ∧ SepFree y := by
  intro y hy
  cases h : isabspath p
  · rcases QQ_rel h with ⟨_, hq⟩ | ⟨_, hq⟩
    · rw [hq] at hy
      simp at hy
      subst hy
      exact ⟨by simp, fun c hc => by simp at hc; subst hc; decide⟩
    · rw [hq] at hy
      exact ⟨(CL_good hy).1, (CL_good hy).2.1⟩
  · obtain ⟨_, _, hQ⟩ := QQ_abs h
    exact ⟨(hQ y hy).1.1, (hQ y hy).1.2.1⟩

theorem QQ_rel_ne {p : Str} (h : isabspath p = false) : QQ p ≠ [] := by
  rcases QQ_rel h with ⟨_, hq⟩ | ⟨hc, hq⟩
  · rw [hq]; simp
  · rw [hq]; exact hc

theorem BB_abs {p : Str} (h : isabspath p = true) : BB p = '/' :: joinSep (QQ p) := by
  rw [BB, if_pos h]

theorem BB_rel {p : Str} (h : isabspath p = false) : BB p = joinSep (QQ p) := by
  rw [BB, if_neg (by simp [h])]

theorem normpath_abs_nil {p : Str} (h : isabspath p = true) (hq : QQ p = []) : normpath p = ['/'] := by
  have hB : BB p = ['/'] := by rw [BB_abs h, hq]; rfl
  have hT : TT p = [] := by
    unfold TT
    have hd : isdirpath ['/'] = true := by decide
    rw [hB, if_neg (by simp [hd])]
  rw [normpath_eq, hB, hT]
  rfl

theorem normpath_rel_dot {p : Str} (h : isabspath p = false) (hc : CL p = []) : normpath p = ['.'] := by
  have hq : QQ p = [['.']] := by rw [QQ, if_neg (by simp [h]), hc]; rfl
  have hB : BB p = ['.'] := by rw [BB_rel h, hq]; rfl
  have hT : TT p = [] := by
    unfold TT
    have hd : isdirpath ['.'] = true := by decide
    rw [hB, if_neg (by simp [hd])]
  rw [normpath_eq, hB, hT]
  rfl

theorem normpath_abs_cons {p : Str} (h : isabspath p = true) :
    normpath p = '/' :: (joinSep (QQ p) ++ TT p) := by
  rw [normpath_eq, BB_abs h, List.cons_append]

theorem normpath_rel {p : Str} (h : isabspath p = false) : normpath p = joinSep (QQ p) ++ TT p := by
  rw [normpath_eq, BB_rel h]

theorem splitRuns_normpath_abs {p : Str} (h : isabspath p = true) (hne : QQ p ≠ []) :
    ∃ R, (R = [] ∨ R = [[]]) ∧ splitRuns (normpath p) = [] :: (QQ p ++ R) := by
  obtain ⟨R, hR, hs⟩ := splitRuns_TT p
  exact ⟨R, hR, by rw [normpath_abs_cons h, splitRuns_slash_joinSep_list _ R hs _ (QQ_wf p) hne]⟩

theorem splitRuns_normpath_rel {p : Str} (h : isabspath p = false) :
    ∃ R, (R = [] ∨ R = [[]]) ∧ splitRuns (normpath p) = QQ p ++ R := by
  obtain ⟨R, hR, hs⟩ := splitRuns_TT p
  exact ⟨R, hR, by rw [normpath_rel h, splitRuns_joinSep_list _ R hs _ (QQ_wf p) (QQ_rel_ne h)]⟩

theorem isabspath_normpath (p : Str) : isabspath (normpath p) = isabspath p := by
  cases h : isabspath p
  · rw [normpath_rel h]
    obtain ⟨a, as, ha⟩ : ∃ a as, QQ p = a :: as := by
      cases hq : QQ p with
      | nil => exact absurd hq (QQ_rel_ne h)
      | cons a as => exact ⟨a, as, rfl⟩
    have hw := QQ_wf p a (by rw [ha]; simp)
    obtain ⟨r, hr⟩ := joinSep_cons_exists a as
    rw [ha, hr]
    cases a with
    | nil => exact absurd rfl hw.1
    | cons a0 a' => exact hw.2 a0 (by simp)
  · rw [normpath_abs_cons h]
    rfl

theorem P0_eq_splitRuns (x : Str) :
    P0 x = ((splitRuns x).filter (· ≠ [])).filter (· != ['.']) := rfl

theorem P0_normpath (p : Str) : P0 (normpath p) = (QQ p).filter (· != ['.']) := by
  rw [P0_eq_splitRuns]
  have hQ : ∀ y ∈ QQ p, y ≠ [] := fun y hy => (QQ_wf p y hy).1
  cases h : isabspath p
  · obtain ⟨R, hR, hs⟩ := splitRuns_normpath_rel h
    rw [hs, filter_ne_nil_app _ _ hQ hR]
  · by_cases hne : QQ p = []
    · rw [normpath_abs_nil h hne, hne]
      rfl
    · obtain ⟨R, hR, hs⟩ := splitRuns_normpath_abs h hne
      rw [hs, List.filter_cons_of_neg (p := fun y : Str => decide (y ≠ [])) (by simp),
        filter_ne_nil_app _ _ hQ hR]

theorem QQ_normpath (p : Str) : QQ (normpath p) = QQ p := by
  have hCL : CL (normpath p) = cleanLoop ((P0 (normpath p)).length + 1) (P0 (normpath p)) := rfl
  cases h : isabspath p
  · have hN : isabspath (normpath p) = false := by rw [isabspath_normpath, h]
    rcases QQ_rel h with ⟨hc, hq⟩ | ⟨hc, hq⟩
    · rw [P0_normpath, hq] at hCL
      have hCL' : CL (normpath p) = [] := by rw [hCL]; rfl
      rw [hq, QQ, if_neg (by simp [hN]), hCL']
      rfl
    · rw [P0_normpath, hq, filter_dot_self _ (fun y hy => (CL_good hy).2.2),
        cleanLoop_self (CL_none p)] at hCL
      rw [hq, QQ, if_neg (by simp [hN]), hCL]
      cases hc' : CL p with
      | nil => exact absurd hc' hc
      | cons a l => rfl
  · have hN : isabspath (normpath p) = true := by rw [isabspath_normpath, h]
    obtain ⟨k, _, hQ⟩ := QQ_abs h
    rw [P0_normpath, filter_dot_self _ (fun y hy => (hQ y hy).1.2.2),
      cleanLoop_self (rfp_none_of_no_dd _ (fun y hy => (hQ y hy).2))] at hCL
    rw [QQ, if_pos hN, hCL]
    have := dropWhile_dd 0 (QQ p) (fun y hy => (hQ y hy).2)
    simpa using this

theorem BB_normpath (p : Str) : BB (normpath p) = BB p := by
  unfold BB
  rw [isabspath_normpath, QQ_normpath]

/-! ## `isdirpath` -/

def isDirName (a : Str) : Bool := a == [] || a == ['.'] || a == dotdot

theorem isdirpath_eq (p : Str) : isdirpath p = isDirName (splitdirNoDrive [] p).2 := rfl

theorem path_decomp : ∀ p : Str, SepFree p ∨ ∃ q t, p = q ++ '/' :: t ∧ SepFree t
  | [] => Or.inl sepFree_nil
  | c :: cs => by
    rcases path_decomp cs with h | ⟨q, t, hq, ht⟩
    · by_cases hc : isSep c = true
      · right
        have : c = '/' := by simpa [isSep] using hc
        subst this
        exact ⟨[], cs, rfl, h⟩
      · left
        intro d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · simpa using hc
        · exact h d hd
    · right
      exact ⟨c :: q, t, by rw [hq]; rfl, ht⟩

theorem span_loop_app {P : Char → Bool} : ∀ (l1 l2 acc : Str), (∀ x ∈ l1, P x = true) →
    List.span.loop P (l1 ++ l2) acc = List.span.loop P l2 (l1.reverse ++ acc)
  | [], _, _, _ => rfl
  | a :: l1, l2, acc, h => by
    have ha := h a (by simp)
    simp only [List.cons_append, List.span.loop, ha]
    rw [span_loop_app l1 l2 (a :: acc) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

theorem span_split {P : Char → Bool} {l1 l2 : Str} {c : Char} (h1 : ∀ x ∈ l1, P x = true)
    (hc : P c = false) : List.span P (l1 ++ c :: l2) = (l1, c :: l2) := by
  unfold List.span
  rw [span_loop_app l1 (c :: l2) [] h1]
  simp [List.span.loop, hc]

theorem span_all {P : Char → Bool} {l : Str} (h : ∀ x ∈ l, P x = true) :
    List.span P l = (l, []) := by
  unfold List.span
  have := span_loop_app l [] [] h
  rw [List.append_nil] at this
  rw [this]
  simp [List.span.loop]

theorem basename_sepFree {t : Str} (ht : SepFree t) : (splitdirNoDrive [] t).2 = t := by
  have hs : List.span (fun c => !isSep c) t.reverse = (t.reverse, []) :=
    span_all (fun c hc => by simp [ht c (List.mem_reverse.1 hc)])
  unfold splitdirNoDrive splitLast
  simp only [hs]

theorem basename_slash (q : Str) {t : Str} (ht : SepFree t) : (splitdirNoDrive [] (q ++ '/' :: t)).2 = t := by
  have hr : (q ++ '/' :: t).reverse = t.reverse ++ '/' :: q.reverse := by simp
  have hall : ∀ x ∈ t.reverse, (fun c => !isSep c) x = true :=
    fun x hx => by simp [ht x (List.mem_reverse.1 hx)]
  have hc : (fun c => !isSep c) '/' = false := by decide
  unfold splitdirNoDrive splitLast
  simp only [hr, span_split hall hc, List.reverse_reverse]

theorem splitRuns_last (p : Str) : ∃ pre, splitRuns p = pre ++ [(splitdirNoDrive [] p).2] := by
  rcases path_decomp p with h | ⟨q, t, rfl, ht⟩
  · exact ⟨[], by rw [splitRuns_sepFree h, basename_sepFree h]; rfl⟩
  · have hs : splitRuns ('/' :: t) = ([] :: []) ++ [t] := by
      rw [splitRuns_slash (sepFree_head ht), splitRuns_sepFree ht]
      rfl
    obtain ⟨u', v', h⟩ := splitRuns_append_last ('/' :: t) [] t [] hs q
    exact ⟨u' :: v', by rw [h, basename_slash q ht]⟩

theorem isdirpath_of_last {p x : Str} {pre : List Str} (h : splitRuns p = pre ++ [x]) :
    isdirpath p = isDirName x := by
  obtain ⟨pre', h'⟩ := splitRuns_last p
  rw [h] at h'
  have := congrArg List.getLast? h'
  simp at this
  rw [isdirpath_eq, ← this]

theorem isdirpath_append_slash (p : Str) : isdirpath (p ++ ['/']) = true := by
  have hs : splitRuns ['/'] = ([] :: []) ++ [[]] := by decide
  obtain ⟨u', v', h⟩ := splitRuns_append_last ['/'] [] [] [] hs p
  rw [isdirpath_of_last h]
  rfl

theorem isDirName_false {x : Str} (h : isDirName x = false) : x ≠ [] ∧ x ≠ ['.'] ∧ x ≠ dotdot := by
  simp [isDirName] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem isdirpath_BB_false {p : Str} (hp : isdirpath p = false) : isdirpath (BB p) = false := by
  obtain ⟨pre, hpre⟩ := splitRuns_last p
  have hx := isDirName_false ((isdirpath_eq p).symm.trans hp)
  generalize (splitdirNoDrive [] p).2 = x at hpre hx
  have hP : P0 p = ((pre.filter (· ≠ [])).filter (· != ['.'])) ++ [x] := by
    rw [P0_eq_splitRuns, hpre, filter_last (q := fun y : Str => decide (y ≠ [])) (by simpa using hx.1),
      filter_last (q := fun y : Str => y != ['.']) (by simpa using hx.2.1)]
  obtain ⟨l, hl⟩ : ∃ l, CL p = l ++ [x] :=
    cleanLoop_induct (fun L => ∃ l, L = l ++ [x])
      (fun L L' h ⟨l, hl⟩ => by subst hl; exact rfp_last hx.2.2 h) _ _ ⟨_, hP⟩
  cases h : isabspath p
  · rcases QQ_rel h with ⟨hc, _⟩ | ⟨_, hq⟩
    · rw [hc] at hl
      simp at hl
    · have hs : splitRuns (BB p) = l ++ [x] := by
        rw [BB_rel h, ← List.append_nil (joinSep (QQ p)),
          splitRuns_joinSep_list [] [] rfl _ (QQ_wf p) (QQ_rel_ne h), hq, hl, List.append_nil]
      rw [isdirpath_of_last hs]
      simp [isDirName, hx.1, hx.2.1, hx.2.2]
  · obtain ⟨l', hl'⟩ := dropWhile_last hx.2.2 l
    have hq : QQ p = l' ++ [x] := by rw [QQ, if_pos h, hl, hl']
    have hs : splitRuns (BB p) = ([] :: l') ++ [x] := by
      rw [BB_abs h, ← List.append_nil (joinSep (QQ p)),
        splitRuns_slash_joinSep_list [] [] rfl _ (QQ_wf p) (by rw [hq]; simp), hq]
      simp
    rw [isdirpath_of_last hs]
    simp [isDirName, hx.1, hx.2.1, hx.2.2]

end JuliaLean.Paths.Norm

namespace JuliaLean.Paths

open JuliaLean.Paths.Norm

theorem normpathIsdirpath_proven : NormpathIsdirpath := by
  intro p
  rw [normpath_eq]
  unfold TT
  cases hd : isdirpath p
  · rw [if_neg (by simp), List.append_nil, isdirpath_BB_false hd]
  · cases hb : isdirpath (BB p)
    · rw [if_pos (by simp), isdirpath_append_slash]
    · rw [if_neg (by simp), List.append_nil, hb]

theorem normpathIdempotent_proven : NormpathIdempotent := by
  intro p
  have hT : TT (normpath p) = TT p := by
    unfold TT
    rw [BB_normpath, normpathIsdirpath_proven p]
  rw [normpath_eq (normpath p), BB_normpath, hT, ← normpath_eq]

theorem normpathCanonical_proven : NormpathCanonical := by
  intro p
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · cases h : isabspath p
    · rw [normpath_rel h]
      obtain ⟨a, as, ha⟩ : ∃ a as, QQ p = a :: as := by
        cases hq : QQ p with
        | nil => exact absurd hq (QQ_rel_ne h)
        | cons a as => exact ⟨a, as, rfl⟩
      have hw := QQ_wf p
      rw [ha] at hw ⊢
      rw [nds_joinSep_append _ a as (hw a (by simp)).2 (fun x hx => hw x (List.mem_cons_of_mem _ hx)),
        nds_TT]
    · by_cases hne : QQ p = []
      · rw [normpath_abs_nil h hne]
        rfl
      · rw [normpath_abs_cons h]
        obtain ⟨a, as, ha⟩ : ∃ a as, QQ p = a :: as := by
          cases hq : QQ p with
          | nil => exact absurd hq hne
          | cons a as => exact ⟨a, as, rfl⟩
        have hw := QQ_wf p
        rw [ha] at hw ⊢
        rw [nds_slash (joinSep_head as _ (hw a (by simp))),
          nds_joinSep_append _ a as (hw a (by simp)).2 (fun x hx => hw x (List.mem_cons_of_mem _ hx)),
          nds_TT]
  · refine ⟨by rw [isabspath_normpath, h], fun c hc => ?_⟩
    by_cases hne : QQ p = []
    · rw [normpath_abs_nil h hne] at hc
      have : splitRuns ['/'] = [[], []] := by decide
      rw [this] at hc
      simp at hc
      subst hc
      decide
    · obtain ⟨R, hR, hs⟩ := splitRuns_normpath_abs h hne
      obtain ⟨_, _, hQ⟩ := QQ_abs h
      rw [hs] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · decide
      rcases List.mem_append.1 hc with hc | hc
      · exact ⟨(hQ c hc).1.2.2, (hQ c hc).2⟩
      · rcases hR with rfl | rfl
        · simp at hc
        · simp at hc
          subst hc
          decide
  · refine ⟨by rw [isabspath_normpath, h], ?_, ?_⟩
    · rcases QQ_rel h with ⟨hc, _⟩ | ⟨hc, hq⟩
      · exact Or.inl (normpath_rel_dot h hc)
      · right
        intro c hcm
        obtain ⟨R, hR, hs⟩ := splitRuns_normpath_rel h
        rw [hs, hq] at hcm
        rcases List.mem_append.1 hcm with hcm | hcm
        · exact (CL_good hcm).2.2
        · rcases hR with rfl | rfl
          · simp at hcm
          · simp at hcm
            subst hcm
            decide
    · rcases QQ_rel h with ⟨hc, _⟩ | ⟨hc, hq⟩
      · refine ⟨0, [['.']], ?_, ?_⟩
        · rw [normpath_rel_dot h hc]
          rfl
        · intro c hcm
          simp at hcm
          subst hcm
          decide
      · obtain ⟨R, hR, hs⟩ := splitRuns_normpath_rel h
        obtain ⟨k, rest, h1, h2⟩ := rfp_none_shape _ (CL_none p)
        refine ⟨k, rest ++ R, by rw [hs, hq, h1, List.append_assoc], fun c hcm => ?_⟩
        rcases List.mem_append.1 hcm with hcm | hcm
        · exact h2 c hcm
        · rcases hR with rfl | rfl
          · simp at hcm
          · simp at hcm
            subst hcm
            decide

theorem resolve_eq (base : List Str) (x : Str) :
    resolve base x = (P0 x).foldl resolveStep (if isabspath x then [] else base) := by
  unfold resolve
  rw [P0_eq_splitRuns, foldl_filter_noop, foldl_filter_noop]
  · intro y _ hq s
    simp at hq
    subst hq
    exact resolveStep_nil s
  · intro y _ hq s
    simp at hq
    subst hq
    exact resolveStep_dot s

theorem normpathLexical_proven : NormpathLexical := by
  intro base p
  rw [resolve_eq, resolve_eq, isabspath_normpath, P0_normpath, ← CL_fold]
  cases h : isabspath p
  · rcases QQ_rel h with ⟨hc, hq⟩ | ⟨_, hq⟩
    · rw [hq, hc]
      rfl
    · rw [hq, filter_dot_self _ (fun y hy => (CL_good hy).2.2)]
  · obtain ⟨k, hk, hQ⟩ := QQ_abs h
    rw [if_pos rfl, filter_dot_self _ (fun y hy => (hQ y hy).1.2.2), hk, List.foldl_append,
      foldl_rep_root]

theorem abspath_eq (cwd p : Str) :
    abspath cwd p = normpath (if !isabspath p then joinStep cwd p else p) := rfl

theorem abspath_arg_abs {cwd : Str} (p : Str) (hc : isabspath cwd = true) :
    isabspath (if !isabspath p then joinStep cwd p else p) = true := by
  cases hp : isabspath p
  · rw [if_pos (by simp)]
    unfold joinStep
    rw [if_neg (by simp [hp])]
    cases cwd with
    | nil => simp [isabspath] at hc
    | cons c cs => split <;> exact hc
  · rw [if_neg (by simp)]
    exact hp

theorem abspathLaws_proven : AbspathLaws := by
  intro cwd p hc
  have h1 : isabspath (abspath cwd p) = true := by
    rw [abspath_eq, isabspath_normpath]
    exact abspath_arg_abs p hc
  refine ⟨h1, ?_⟩
  rw [abspath_eq cwd (abspath cwd p), if_neg (by simp [h1]), abspath_eq, normpathIdempotent_proven]

end JuliaLean.Paths
