import JuliaLean.Paths.Normpath

/-!
# `relpath` leads from `startpath` to `path`
-/

namespace JuliaLean.Paths.Rel

open JuliaLean.Paths JuliaLean.Paths.Norm

/-- The part of `relpath` after the two component arrays are computed,
`base/path.jl:938-956`. -/
def relCore (pathArr startArr : List Str) : Str :=
  let i := commonLen pathArr startArr
  let pathpart := joinSep ((pathArr.drop i).take (lastNonempty pathArr - i))
  let prefixNum : Int := (lastNonempty startArr : Int) - i - 1
  let rel :=
    if prefixNum ≥ 0 then
      let pre := dotdot ++ ['/']
      if pathpart.isEmpty then repeatStr pre prefixNum.toNat ++ dotdot
      else repeatStr pre prefixNum.toNat ++ dotdot ++ '/' :: pathpart
    else pathpart
  if rel.isEmpty then ['.'] else rel

theorem relpath_cons (cwd : Str) (c d : Char) (cs ds : Str) :
    relpath cwd (c :: cs) (d :: ds) =
      if ((c :: cs) == (d :: ds)) = true then .ok ['.']
      else .ok (relCore (splitRuns (abspath cwd (c :: cs))) (splitRuns (abspath cwd (d :: ds)))) := rfl

theorem resolve_dot (base : List Str) : resolve base ['.'] = base := by
  have h1 : splitRuns ['.'] = [['.']] := by decide
  have h2 : isabspath ['.'] = false := by decide
  simp [resolve, h1, h2, resolveStep_dot]

/-! ## Absolute normalized paths -/

theorem abs_form (cwd p : Str) (hc : isabspath cwd = true) :
    ∃ Q R, splitRuns (abspath cwd p) = [] :: (Q ++ R) ∧ (R = [] ∨ R = [[]]) ∧
      (∀ y ∈ Q, Good y ∧ y ≠ dotdot) ∧ resolve [] (abspath cwd p) = Q := by
  have hX := abspath_arg_abs p hc
  rw [abspath_eq]
  generalize (if !isabspath p then joinStep cwd p else p) = X at hX
  have hres : ∀ N : Str, resolve [] N = (splitRuns N).foldl resolveStep [] := by
    intro N
    unfold resolve
    split <;> rfl
  by_cases hne : QQ X = []
  · rw [normpath_abs_nil hX hne]
    have hs : splitRuns ['/'] = [] :: ([] ++ [[]]) := by decide
    refine ⟨[], [[]], hs, Or.inr rfl, by simp, ?_⟩
    rw [hres, hs]
    rfl
  · obtain ⟨R, hR, hs⟩ := splitRuns_normpath_abs hX hne
    obtain ⟨_, _, hQ⟩ := QQ_abs hX
    refine ⟨QQ X, R, hs, hR, hQ, ?_⟩
    rw [hres, hs, List.foldl_cons, resolveStep_nil, List.foldl_append, foldl_names _ hQ]
    rcases hR with rfl | rfl
    · simp
    · simp [resolveStep_nil]

/-! ## Arithmetic of the component arrays -/

theorem common_split : ∀ (QA QS : List Str), ∃ C A' S', QA = C ++ A' ∧ QS = C ++ S' ∧
    ∀ a b A'' S'', A' = a :: A'' → S' = b :: S'' → a ≠ b
  | a :: QA, b :: QS => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨C, A', S', h1, h2, h3⟩ := common_split QA QS
      exact ⟨a :: C, A', S', by rw [h1]; rfl, by rw [h2]; rfl, h3⟩
    · refine ⟨[], a :: QA, b :: QS, rfl, rfl, ?_⟩
      intro a' b' _ _ ha hb
      simp at ha hb
      rw [← ha.1, ← hb.1]
      exact hab
  | [], QS => ⟨[], [], QS, rfl, rfl, by simp⟩
  | _ :: _, [] => ⟨[], _, [], rfl, rfl, by simp⟩

theorem commonLen_nil_nil (X Y : List Str) : commonLen ([] :: X) ([] :: Y) = commonLen X Y + 1 := by
  simp [commonLen]

theorem commonLen_append (C X Y : List Str) :
    commonLen (C ++ X) (C ++ Y) = C.length + commonLen X Y := by
  induction C with
  | nil => simp
  | cons c C ih =>
    simp [commonLen, ih] <;> omega

theorem commonLen_div (A' S' RA RS : List Str) (hA : ∀ y ∈ A', y ≠ []) (hS : ∀ y ∈ S', y ≠ [])
    (hRA : RA = [] ∨ RA = [[]]) (hRS : RS = [] ∨ RS = [[]])
    (hdiv : ∀ a b A'' S'', A' = a :: A'' → S' = b :: S'' → a ≠ b) (hne : A' ≠ [] ∨ S' ≠ []) :
    commonLen (A' ++ RA) (S' ++ RS) = 0 := by
  cases A' with
  | nil =>
    cases S' with
    | nil => simp at hne
    | cons b S'' =>
      have hb := hS b (by simp)
      rcases hRA with rfl | rfl
      · rfl
      · simp [commonLen, hb]
  | cons a A'' =>
    have ha := hA a (by simp)
    cases S' with
    | nil =>
      rcases hRS with rfl | rfl
      · rfl
      · simp [commonLen, ha]
    | cons b S'' =>
      simp [commonLen, hdiv a b A'' S'' rfl rfl]

theorem go_append (l1 l2 : List Str) (i acc : Nat) :
    lastNonempty.go (l1 ++ l2) i acc =
      lastNonempty.go l2 (i + l1.length) (lastNonempty.go l1 i acc) := by
  induction l1 generalizing i acc with
  | nil => simp [lastNonempty.go]
  | cons x l ih =>
    have e : i + 1 + l.length = i + (l.length + 1) := by omega
    simp only [List.cons_append, lastNonempty.go, ih, List.length_cons, e]

theorem go_nonempty : ∀ (Q : List Str) (i acc : Nat), (∀ y ∈ Q, y ≠ []) →
    lastNonempty.go Q i acc = if Q = [] then acc else i + Q.length - 1
  | [], i, acc, _ => by simp [lastNonempty.go]
  | y :: Q, i, acc, h => by
    have hy : y.isEmpty = false := by
      cases y with
      | nil => exact absurd rfl (h [] (by simp))
      | cons _ _ => rfl
    simp only [lastNonempty.go, hy, Bool.false_eq_true, if_false]
    rw [go_nonempty Q (i + 1) i (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    cases Q with
    | nil => simp
    | cons z Q => simp <;> omega

theorem go_empties {R : List Str} (hR : R = [] ∨ R = [[]]) (n acc : Nat) :
    lastNonempty.go R n acc = acc := by
  rcases hR with rfl | rfl <;> rfl

theorem lastNonempty_form (Q R : List Str) (hQ : ∀ y ∈ Q, y ≠ []) (hR : R = [] ∨ R = [[]]) :
    lastNonempty ([] :: (Q ++ R)) = if Q = [] then 0 else Q.length + 1 := by
  have h1 : lastNonempty ([] :: (Q ++ R)) = lastNonempty.go (Q ++ R) 2 0 := rfl
  rw [h1, go_append, go_empties hR, go_nonempty Q 2 0 hQ]
  by_cases hq : Q = [] <;> simp [hq] <;> omega

theorem pathpart_eq (C A' RA : List Str) (hC : ∀ y ∈ C, y ≠ []) (hA : ∀ y ∈ A', y ≠ [])
    (hRA : RA = [] ∨ RA = [[]]) (i : Nat) (hi1 : C.length + 1 ≤ i)
    (hi2 : A' ≠ [] → i = C.length + 1) :
    (([] :: ((C ++ A') ++ RA)).drop i).take (lastNonempty ([] :: ((C ++ A') ++ RA)) - i) = A' := by
  have hCA : ∀ y ∈ C ++ A', y ≠ [] := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hC y hy
    · exact hA y hy
  rw [lastNonempty_form _ _ hCA hRA]
  by_cases hA0 : A' = []
  · subst hA0
    have : (if C ++ [] = [] then 0 else (C ++ []).length + 1) - i = 0 := by
      split <;> simp <;> omega
    rw [this, List.take_zero]
  · have hi := hi2 hA0
    subst hi
    have hne : C ++ A' ≠ [] := by simp [hA0]
    rw [if_neg hne, List.drop_succ_cons, List.append_assoc, List.drop_left]
    have : (C ++ A').length + 1 - (C.length + 1) = A'.length := by simp
    rw [this, List.take_left]

/-! ## The relative path -/

theorem joinSep_ne_nil (a : Str) (as : List Str) (ha : a ≠ []) : joinSep (a :: as) ≠ [] := by
  obtain ⟨r, hr⟩ := joinSep_cons_exists a as
  rw [hr]
  simp [ha]

theorem rep_join (A' : List Str) : ∀ n : Nat,
    repeatStr (dotdot ++ ['/']) n ++ joinSep (dotdot :: A') =
      joinSep (List.replicate (n + 1) dotdot ++ A')
  | 0 => by simp [repeatStr, List.replicate_succ]
  | n + 1 => by
    have e1 : List.replicate (n + 1 + 1) dotdot ++ A' = dotdot :: (List.replicate (n + 1) dotdot ++ A') := by
      simp [List.replicate_succ]
    have e2 : List.replicate (n + 1) dotdot ++ A' = dotdot :: (List.replicate n dotdot ++ A') := by
      simp [List.replicate_succ]
    rw [e1, e2, joinSep_cons_cons, ← e2, ← rep_join A' n]
    simp [repeatStr]

theorem rel_dd (A' : List Str) (hA : ∀ y ∈ A', y ≠ []) (n : Nat) :
    (if (joinSep A').isEmpty = true then repeatStr (dotdot ++ ['/']) n ++ dotdot
      else repeatStr (dotdot ++ ['/']) n ++ dotdot ++ '/' :: joinSep A') =
      joinSep (List.replicate (n + 1) dotdot ++ A') := by
  rw [← rep_join]
  cases A' with
  | nil => rfl
  | cons a A'' =>
    have hj : (joinSep (a :: A'')).isEmpty = false := by
      cases h : joinSep (a :: A'') with
      | nil => exact absurd h (joinSep_ne_nil a A'' (hA a (by simp)))
      | cons _ _ => rfl
    rw [hj, if_neg (by simp), joinSep_cons_cons, List.append_assoc]

theorem relCore_eq (C A' S' RA RS : List Str) (hC : ∀ y ∈ C, y ≠ []) (hA : ∀ y ∈ A', y ≠ [])
    (hS : ∀ y ∈ S', y ≠ []) (hRA : RA = [] ∨ RA = [[]]) (hRS : RS = [] ∨ RS = [[]])
    (hdiv : ∀ a b A'' S'', A' = a :: A'' → S' = b :: S'' → a ≠ b) :
    relCore ([] :: ((C ++ A') ++ RA)) ([] :: ((C ++ S') ++ RS)) =
      if List.replicate S'.length dotdot ++ A' = [] then ['.']
      else joinSep (List.replicate S'.length dotdot ++ A') := by
  have hi : commonLen ([] :: ((C ++ A') ++ RA)) ([] :: ((C ++ S') ++ RS)) =
      C.length + commonLen (A' ++ RA) (S' ++ RS) + 1 := by
    rw [commonLen_nil_nil, List.append_assoc, List.append_assoc, commonLen_append]
  have he : A' ≠ [] ∨ S' ≠ [] → commonLen (A' ++ RA) (S' ++ RS) = 0 :=
    commonLen_div A' S' RA RS hA hS hRA hRS hdiv
  have hCS : ∀ y ∈ C ++ S', y ≠ [] := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hC y hy
    · exact hS y hy
  have hLS := lastNonempty_form _ _ hCS hRS
  have hpp := pathpart_eq C A' RA hC hA hRA
    (commonLen ([] :: ((C ++ A') ++ RA)) ([] :: ((C ++ S') ++ RS)))
    (by rw [hi]; omega) (fun h => by rw [hi, he (Or.inl h)])
  simp only [relCore]
  rw [hpp]
  by_cases hS0 : S' = []
  · subst hS0
    have hneg : ¬ ((lastNonempty ([] :: ((C ++ []) ++ RS)) : Int) -
        ((commonLen ([] :: ((C ++ A') ++ RA)) ([] :: ((C ++ []) ++ RS)) : Nat) : Int) - 1 ≥ 0) := by
      rw [hLS, hi]
      split <;> simp <;> omega
    rw [if_neg hneg]
    simp only [List.length_nil, List.replicate_zero, List.nil_append]
    cases A' with
    | nil => rfl
    | cons a A'' =>
      have hj : (joinSep (a :: A'')).isEmpty = false := by
        cases h : joinSep (a :: A'') with
        | nil => exact absurd h (joinSep_ne_nil a A'' (hA a (by simp)))
        | cons _ _ => rfl
      rw [hj, if_neg (by simp), if_neg (by simp)]
  · have he0 := he (Or.inr hS0)
    have hCS0 : C ++ S' ≠ [] := by simp [hS0]
    have hS1 : 1 ≤ S'.length := by
      cases S' with
      | nil => exact absurd rfl hS0
      | cons _ _ => simp
    have hval : ((lastNonempty ([] :: ((C ++ S') ++ RS)) : Int) -
        ((commonLen ([] :: ((C ++ A') ++ RA)) ([] :: ((C ++ S') ++ RS)) : Nat) : Int) - 1) =
        ((S'.length - 1 : Nat) : Int) := by
      rw [hLS, hi, he0, if_neg hCS0, List.length_append]
      omega
    have hcond : ((S'.length - 1 : Nat) : Int) ≥ 0 := by omega
    rw [hval, if_pos hcond, Int.toNat_natCast, rel_dd A' hA]
    have hn : S'.length - 1 + 1 = S'.length := by omega
    rw [hn]
    have hW : List.replicate S'.length dotdot ++ A' ≠ [] := by
      cases S' with
      | nil => exact absurd rfl hS0
      | cons _ _ => simp [List.replicate_succ]
    have hj : (joinSep (List.replicate S'.length dotdot ++ A')).isEmpty = false := by
      obtain ⟨n, hn'⟩ : ∃ n, S'.length = n + 1 := ⟨S'.length - 1, by omega⟩
      rw [hn', List.replicate_succ, List.cons_append]
      cases h : joinSep (dotdot :: (List.replicate n dotdot ++ A')) with
      | nil => exact absurd h (joinSep_ne_nil _ _ (by simp [dotdot]))
      | cons _ _ => rfl
    rw [hj, if_neg (by simp), if_neg hW]

theorem foldl_rep_drop : ∀ (S' C : List Str),
    (List.replicate S'.length dotdot).foldl resolveStep (C ++ S') = C
  | [], C => by simp
  | s :: S', C => by
    have e : C ++ s :: S' = (C ++ [s]) ++ S' := by simp
    rw [e, List.length_cons, List.replicate_succ', List.foldl_append, foldl_rep_drop S' (C ++ [s])]
    simp [resolveStep_dotdot]

theorem relCore_spec (QA RA QS RS : List Str)
    (hA : ∀ y ∈ QA, Good y ∧ y ≠ dotdot) (hS : ∀ y ∈ QS, Good y ∧ y ≠ dotdot)
    (hRA : RA = [] ∨ RA = [[]]) (hRS : RS = [] ∨ RS = [[]]) :
    isabspath (relCore ([] :: (QA ++ RA)) ([] :: (QS ++ RS))) = false ∧
      resolve QS (relCore ([] :: (QA ++ RA)) ([] :: (QS ++ RS))) = QA := by
  obtain ⟨C, A', S', rfl, rfl, hdiv⟩ := common_split QA QS
  have hC : ∀ y ∈ C, Good y ∧ y ≠ dotdot := fun y hy => hA y (List.mem_append_left _ hy)
  have hA' : ∀ y ∈ A', Good y ∧ y ≠ dotdot := fun y hy => hA y (List.mem_append_right _ hy)
  have hS' : ∀ y ∈ S', Good y ∧ y ≠ dotdot := fun y hy => hS y (List.mem_append_right _ hy)
  rw [relCore_eq C A' S' RA RS (fun y hy => (hC y hy).1.1) (fun y hy => (hA' y hy).1.1)
    (fun y hy => (hS' y hy).1.1) hRA hRS hdiv]
  by_cases hW : List.replicate S'.length dotdot ++ A' = []
  · rw [if_pos hW]
    have hS0 : S' = [] := by
      cases S' with
      | nil => rfl
      | cons _ _ => simp [List.replicate_succ] at hW
    have hA0 : A' = [] := by
      subst hS0
      simpa using hW
    subst hS0
    subst hA0
    exact ⟨rfl, by rw [resolve_dot]⟩
  · rw [if_neg hW]
    have hWg : ∀ y ∈ List.replicate S'.length dotdot ++ A', y ≠ [] ∧ SepFree y := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · rw [(List.mem_replicate.1 hy).2]
        exact ⟨good_dotdot.1, sepFree_dotdot⟩
      · exact ⟨(hA' y hy).1.1, (hA' y hy).1.2.1⟩
    have hsplit : splitRuns (joinSep (List.replicate S'.length dotdot ++ A')) =
        List.replicate S'.length dotdot ++ A' := by
      have := splitRuns_joinSep_list [] [] rfl _ hWg hW
      simpa using this
    have habs : isabspath (joinSep (List.replicate S'.length dotdot ++ A')) = false := by
      obtain ⟨w, ws, hw⟩ : ∃ w ws, List.replicate S'.length dotdot ++ A' = w :: ws := by
        cases h : List.replicate S'.length dotdot ++ A' with
        | nil => exact absurd h hW
        | cons w ws => exact ⟨w, ws, rfl⟩
      have hg := hWg w (by rw [hw]; simp)
      obtain ⟨r, hr⟩ := joinSep_cons_exists w ws
      rw [hw, hr]
      cases w with
      | nil => exact absurd rfl hg.1
      | cons w0 w' => exact hg.2 w0 (by simp)
    refine ⟨habs, ?_⟩
    unfold resolve
    rw [habs, hsplit, if_neg (by simp), List.foldl_append, foldl_rep_drop, foldl_names _ hA']

end JuliaLean.Paths.Rel

namespace JuliaLean.Paths

open JuliaLean.Paths.Norm JuliaLean.Paths.Rel

theorem relpathRoundtrip_proven : RelpathRoundtrip := by
  intro cwd p s r hc h
  cases p with
  | nil =>
    obtain ⟨e, he⟩ : ∃ e, relpath cwd [] s = .error e := ⟨_, rfl⟩
    rw [he] at h
    cases h
  | cons c cs =>
    cases s with
    | nil =>
      obtain ⟨e, he⟩ : ∃ e, relpath cwd (c :: cs) [] = .error e := ⟨_, rfl⟩
      rw [he] at h
      cases h
    | cons d ds =>
      rw [relpath_cons] at h
      obtain ⟨QA, RA, hsA, hRA, hQA, hresA⟩ := abs_form cwd (c :: cs) hc
      obtain ⟨QS, RS, hsS, hRS, hQS, hresS⟩ := abs_form cwd (d :: ds) hc
      by_cases heq : ((c :: cs) == (d :: ds)) = true
      · rw [if_pos heq] at h
        cases h
        have he : (c :: cs) = (d :: ds) := by simpa using heq
        rw [he, resolve_dot]
        exact ⟨rfl, rfl⟩
      · rw [if_neg heq] at h
        cases h
        rw [hsA, hsS, hresS, hresA]
        exact relCore_spec QA RA QS RS hQA hQS hRA hRS

end JuliaLean.Paths
