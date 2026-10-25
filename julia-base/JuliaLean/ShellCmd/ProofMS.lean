import JuliaLean.ShellCmd.Props

set_option linter.unusedSimpArgs false
namespace JuliaLean.ShellCmd
namespace ProofMS

private abbrev bs := A '\\'
private abbrev dq := A '"'

private theorem take_run (k : Nat) (c : JC) (cs : JS) (hc : c ≠ bs) :
    ((List.replicate k bs ++ c :: cs).takeWhile (· == bs)) = List.replicate k bs := by
  induction k with
  | zero => simp [hc]
  | succ k ih => simp [List.replicate_succ, ih]

private theorem run_step (k n : Nat) (c : JC) (cs : JS) (ws : List JS)
    (cur : Option JS) (inq : Bool) (hc : c ≠ bs) :
    msWords (n + 1) (List.replicate (k + 1) bs ++ c :: cs) ws cur inq =
      (if c == dq then
        let acc := cur.getD [] ++ List.replicate ((k + 1) / 2) bs
        if (k + 1) % 2 == 1 then msWords n cs ws (some (acc ++ [dq])) inq
        else let q := msQuote cs acc inq; msWords n q.1 ws (some q.2.1) q.2.2
       else msWords n (c :: cs) ws (some (cur.getD [] ++ List.replicate (k + 1) bs)) inq) := by
  have ht := take_run (k + 1) c cs hc
  have hd : (List.replicate (k + 1) bs ++ c :: cs).drop (k + 1) = c :: cs := by simp
  simp only [List.replicate_succ, List.cons_append] at ht hd ⊢
  rw [msWords]
  simp only [show (bs == A ' ') = false by decide,
    show (bs == A '\t') = false by decide, Bool.or_self, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, show (bs == A '\\') = true by decide,
    ht, List.length_replicate, List.length_cons, hd]
  rfl

private theorem literal_step (n : Nat) (c : JC) (cs : JS) (ws : List JS)
    (cur : Option JS) (inq : Bool) (hb : c ≠ bs) (hq : c ≠ dq)
    (hs : inq = true ∨ (c ≠ A ' ' ∧ c ≠ A '\t')) :
    msWords (n + 1) (c :: cs) ws cur inq =
      msWords n cs ws (some (cur.getD [] ++ [c])) inq := by
  rcases hs with rfl | ⟨hs, ht⟩
  · simp [msWords, hb, hq]
  · simp [msWords, hb, hq, hs, ht]

private theorem quote_end (rest cur : JS)
    (hr : rest = [] ∨ ∃ t, rest = A ' ' :: t) :
    msQuote rest cur true = (rest, cur, false) := by
  rcases hr with rfl | ⟨t, rfl⟩ <;> rfl

private theorem raw (w : JS) : ∀ (k n : Nat) (rest acc : JS) (ws result : List JS),
    (rest = [] ∨ ∃ t, rest = A ' ' :: t) →
    (List.replicate k bs ++ escapeRawString dq w k ++ dq :: rest).length < n →
    (∀ m, rest.length < m →
      msWords m rest ws (some (acc ++ List.replicate k bs ++ w)) false = result) →
    msWords n (List.replicate k bs ++ escapeRawString dq w k ++ dq :: rest)
      ws (some acc) true = result := by
  induction w with
  | nil =>
    intro k n rest acc ws result hr hn finish
    have he : List.replicate k bs ++ escapeRawString dq [] k ++ dq :: rest =
        List.replicate (2 * k) bs ++ dq :: rest := by
      simp [escapeRawString, Nat.two_mul]
    rw [he] at hn ⊢
    cases n with
    | zero => simp at hn
    | succ n =>
      cases k with
      | zero =>
        simp only [Nat.mul_zero, List.replicate_zero, List.nil_append] at hn ⊢
        simpa [msWords, show dq ≠ bs by decide, quote_end rest acc hr] using finish n (by simpa using hn)
      | succ k =>
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          run_step _ _ _ _ _ _ _ (by decide)]
        have hhalf : ((2 * k + 1) + 1) / 2 = k + 1 := by omega
        have hmod : ((2 * k + 1) + 1) % 2 = 0 := by omega
        simpa [hhalf, hmod, quote_end rest _ hr] using
          finish n (by simp only [List.length_append, List.length_replicate, List.length_cons] at hn; omega)
  | cons c cs ih =>
    intro k n rest acc ws result hr hn finish
    by_cases hb : c = bs
    · subst c
      have he : List.replicate k bs ++ escapeRawString dq (bs :: cs) k ++ dq :: rest =
          List.replicate (k + 1) bs ++ escapeRawString dq cs (k + 1) ++ dq :: rest := by
        simp [escapeRawString, List.replicate_succ', List.append_assoc]
      rw [he] at hn ⊢
      apply ih (k + 1) n rest acc ws result hr hn
      intro m hm
      simpa [List.replicate_succ', List.append_assoc] using finish m hm
    · by_cases hq : c = dq
      · subst c
        have he : List.replicate k bs ++ escapeRawString dq (dq :: cs) k ++ dq :: rest =
            List.replicate (2 * k + 1) bs ++ dq :: (escapeRawString dq cs 0 ++ dq :: rest) := by
          simp only [escapeRawString, show (dq == A '\\') = false by decide,
            Bool.false_eq_true, ↓reduceIte, BEq.rfl]
          simp only [← List.append_assoc]
          change (List.replicate k bs ++ List.replicate (k + 1) bs) ++
            dq :: escapeRawString dq cs 0 ++ dq :: rest = _
          simp [Nat.two_mul, Nat.add_assoc, List.append_assoc]
        rw [he] at hn ⊢
        cases n with
        | zero => simp at hn
        | succ n =>
          rw [run_step _ _ _ _ _ _ _ (by decide)]
          have hhalf : (2 * k + 1) / 2 = k := by omega
          have hmod : (2 * k + 1) % 2 = 1 := by omega
          simp only [BEq.rfl, ↓reduceIte, hhalf, hmod, Option.getD_some]
          apply ih 0 n rest (acc ++ List.replicate k bs ++ [dq]) ws result hr
          · simp only [List.length_append, List.length_replicate, List.length_cons] at hn ⊢
            omega
          · intro m hm
            simpa [List.append_assoc] using finish m hm
      · have he : List.replicate k bs ++ escapeRawString dq (c :: cs) k ++ dq :: rest =
            List.replicate k bs ++ c :: (escapeRawString dq cs 0 ++ dq :: rest) := by
          simp [escapeRawString, hb, hq]
        rw [he] at hn ⊢
        cases k with
        | zero =>
          cases n with
          | zero => simp at hn
          | succ n =>
            simp only [List.replicate_zero, List.nil_append] at hn ⊢
            rw [literal_step _ _ _ _ _ _ hb hq (Or.inl rfl)]
            apply ih 0 n rest (acc ++ [c]) ws result hr (by simpa using hn)
            intro m hm
            simpa [List.append_assoc] using finish m hm
        | succ k =>
          cases n with
          | zero => simp at hn
          | succ n =>
            rw [run_step _ _ _ _ _ _ _ hb]
            simp only [show (c == dq) = false from beq_eq_false_iff_ne.mpr hq,
              Bool.false_eq_true, ↓reduceIte, Option.getD_some]
            cases n with
            | zero => simp only [List.length_append, List.length_replicate, List.length_cons] at hn; omega
            | succ n =>
              rw [literal_step _ _ _ _ _ _ hb hq (Or.inl rfl)]
              apply ih 0 n rest (acc ++ List.replicate (k + 1) bs ++ [c]) ws result hr
              · simp only [List.length_append, List.length_replicate, List.length_cons] at hn ⊢
                omega
              · intro m hm
                simpa [List.append_assoc] using finish m hm

private theorem take_bs (k : Nat) :
    (List.replicate k bs).takeWhile (· == bs) = List.replicate k bs := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem run_last (k n : Nat) (ws : List JS) (acc : JS) :
    msWords (n + 1) (List.replicate (k + 1) bs) ws (some acc) false =
      msWords n [] ws (some (acc ++ List.replicate (k + 1) bs)) false := by
  have ht := take_bs (k + 1)
  have hd : (List.replicate (k + 1) bs).drop (k + 1) = [] := by simp
  simp only [List.replicate_succ] at ht hd ⊢
  rw [msWords]
  simp only [show (bs == A ' ') = false by decide,
    show (bs == A '\t') = false by decide, Bool.or_self, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, show (bs == A '\\') = true by decide,
    ht, List.length_replicate, List.length_cons, hd, Option.getD_some]
  rfl

private theorem plain (w : JS) : ∀ (k n : Nat) (rest acc : JS) (ws result : List JS),
    w.any (fun c => c == A ' ' || c == A '\t' || c == dq) = false →
    (rest = [] ∨ ∃ t, rest = A ' ' :: t) →
    (List.replicate k bs ++ w ++ rest).length < n →
    (∀ m, rest.length < m →
      msWords m rest ws (some (acc ++ List.replicate k bs ++ w)) false = result) →
    msWords n (List.replicate k bs ++ w ++ rest) ws (some acc) false = result := by
  induction w with
  | nil =>
    intro k n rest acc ws result hp hr hn finish
    cases k with
    | zero => simpa using finish n (by simpa using hn)
    | succ k =>
      cases n with
      | zero => simp at hn
      | succ n =>
        simp only [List.append_nil] at hn ⊢
        rcases hr with rfl | ⟨t, rfl⟩
        · simp only [List.append_nil] at hn ⊢
          rw [run_last]
          simpa using finish n (by simp only [List.length_replicate] at hn; simp; omega)
        · rw [run_step _ _ _ _ _ _ _ (by decide)]
          simpa [show A ' ' ≠ dq by decide] using
            finish n (by simp only [List.length_append, List.length_replicate] at hn; omega)
  | cons c cs ih =>
    intro k n rest acc ws result hp hr hn finish
    simp only [List.any_cons, Bool.or_eq_false_iff] at hp
    have hchar : (c ≠ A ' ' ∧ c ≠ A '\t') ∧ c ≠ dq := by
      simpa only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] using hp.1
    by_cases hb : c = bs
    · subst c
      have he : List.replicate k bs ++ bs :: cs ++ rest =
          List.replicate (k + 1) bs ++ cs ++ rest := by
        simp [List.replicate_succ', List.append_assoc]
      rw [he] at hn ⊢
      apply ih (k + 1) n rest acc ws result hp.2 hr hn
      intro m hm
      simpa [List.replicate_succ', List.append_assoc] using finish m hm
    · cases k with
      | zero =>
        cases n with
        | zero => simp at hn
        | succ n =>
          simp only [List.replicate_zero, List.nil_append, List.cons_append] at hn ⊢
          rw [literal_step _ _ _ _ _ _ hb hchar.2 (Or.inr hchar.1)]
          apply ih 0 n rest (acc ++ [c]) ws result hp.2 hr (by simpa using hn)
          intro m hm
          simpa [List.append_assoc] using finish m hm
      | succ k =>
        cases n with
        | zero => simp at hn
        | succ n =>
          rw [List.append_assoc, List.cons_append] at hn ⊢
          rw [run_step _ _ _ _ _ _ _ hb]
          simp only [show (c == dq) = false from beq_eq_false_iff_ne.mpr hchar.2,
            Bool.false_eq_true, ↓reduceIte, Option.getD_some]
          cases n with
          | zero => simp only [List.length_append, List.length_replicate, List.length_cons] at hn; omega
          | succ n =>
            rw [literal_step _ _ _ _ _ _ hb hchar.2 (Or.inr hchar.1)]
            apply ih 0 n rest (acc ++ List.replicate (k + 1) bs ++ [c]) ws result hp.2 hr
            · simp only [List.length_append, List.length_replicate, List.length_cons] at hn ⊢; omega
            · intro m hm
              simpa [List.append_assoc] using finish m hm

private theorem quote_open (rest acc : JS) :
    msQuote rest acc false = (rest, acc, true) := by
  cases rest <;> rfl

private theorem open_step (n : Nat) (rest : JS) (ws : List JS) :
    msWords (n + 1) (dq :: rest) ws none false =
      msWords n rest ws (some []) true := by
  simp [msWords, show dq ≠ bs by decide, show dq ≠ A ' ' by decide,
    show dq ≠ A '\t' by decide, quote_open]

private theorem start_some (n : Nat) (c : JC) (cs : JS) (ws : List JS)
    (hs : c ≠ A ' ') (ht : c ≠ A '\t') :
    msWords (n + 1) (c :: cs) ws none false =
      msWords (n + 1) (c :: cs) ws (some []) false := by
  simp [msWords, hs, ht]

private theorem argument (w : JS) (n : Nat) (rest : JS) (ws result : List JS)
    (hr : rest = [] ∨ ∃ t, rest = A ' ' :: t)
    (hn : (msArg w ++ rest).length < n)
    (finish : ∀ m, rest.length < m → msWords m rest ws (some w) false = result) :
    msWords n (msArg w ++ rest) ws none false = result := by
  unfold msArg at hn ⊢
  split at hn <;> rename_i hp
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    cases n with
    | zero => simp at hn
    | succ n =>
      simp only [List.cons_append, List.append_assoc] at hn ⊢
      rw [open_step]
      apply raw w 0 n rest [] ws result hr (by simpa using hn)
      intro m hm
      simpa using finish m hm
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    cases w with
    | nil => simp at hp
    | cons c cs =>
      have hp' : (c :: cs).any (fun c => c == A ' ' || c == A '\t' || c == dq) = false := by
        simpa using hp
      have hc : c ≠ A ' ' ∧ c ≠ A '\t' := by
        simp only [List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hp'
        exact hp'.1.1
      cases n with
      | zero => simp at hn
      | succ n =>
        rw [List.cons_append, start_some _ _ _ _ hc.1 hc.2]
        apply plain (c :: cs) 0 (n + 1) rest [] ws result hp' hr (by simpa using hn)
        intro m hm
        simpa using finish m hm

private theorem joined (xs : List JS) : ∀ (n : Nat) (ws : List JS),
    (msIO xs).length < n → msWords n (msIO xs) ws none false = ws ++ xs := by
  induction xs with
  | nil =>
    intro n ws hn
    cases n <;> simp [msIO, joinSp, msWords] at *
  | cons w xs ih =>
    intro n ws hn
    have he : msIO (w :: xs) =
        msArg w ++ (match xs with | [] => [] | _ :: _ => A ' ' :: msIO xs) := by
      cases xs <;> simp [msIO, joinSp, List.append_assoc]
    rw [he] at hn ⊢
    apply argument w n _ ws (ws ++ w :: xs)
    · cases xs with
      | nil => exact Or.inl rfl
      | cons x xs => exact Or.inr ⟨msIO (x :: xs), rfl⟩
    · exact hn
    · intro m hm
      cases xs with
      | nil =>
        cases m <;> simp [msWords] at *
      | cons x xs =>
        cases m with
        | zero => simp at hm
        | succ m =>
          simp only [msWords, Bool.not_false, BEq.rfl, Bool.true_or,
            Bool.true_and, ↓reduceIte, Option.toList_some]
          rw [ih m (ws ++ [w]) (by simpa using hm)]
          simp [List.append_assoc]

end ProofMS

theorem msArgsRoundTrip_proven : MsArgsRoundTrip := by
  intro xs hxs
  refine ⟨msIO xs, ?_, ?_⟩
  · cases xs with
    | nil => exact False.elim (hxs rfl)
    | cons w ws => rfl
  · simpa [msParse] using ProofMS.joined xs ((msIO xs).length + 1) [] (by omega)

end JuliaLean.ShellCmd
