import JuliaLean.ShellCmd.Props

namespace JuliaLean.ShellCmd
namespace ProofQuote

private theorem keep_pos (q : JC) (hq : isspace q = false) :
    ∀ (r : JS) (old : Option JC), q ∈ r → 0 < rstripKeep old r := by
  intro r
  induction r with
  | nil => simp
  | cons c r ih =>
    intro old hm
    simp only [rstripKeep]
    split
    · omega
    · split
      · omega
      · have hc : isspace c = true := by simpa using ‹¬(!isspace c) = true›
        have hqr : q ∈ r := by
          rcases List.mem_cons.mp hm with he | he
          · subst c; simp [hq] at hc
          · exact he
        exact ih (some c) hqr

private theorem rstrip_cons (q : JC) (t : JS) (hq : isspace q = false) :
    ∃ u : JS, rstripShell (q :: t) = q :: u ∧ ∀ c ∈ u, c ∈ t := by
  have hp : 0 < rstripKeep none (q :: t).reverse :=
    keep_pos q hq _ _ (by simp)
  unfold rstripShell
  cases hk : rstripKeep none (q :: t).reverse with
  | zero => omega
  | succ n =>
    refine ⟨t.take n, ?_, ?_⟩
    · rfl
    · intro c hc
      exact List.mem_of_mem_take hc

private theorem pairs_filter (t : JS) (p : Nat) (hp : 1 ≤ p) :
    (pairsFrom p t).filter (fun q => (q.1 : Int) < 1) = [] := by
  induction t generalizing p with
  | nil => rfl
  | cons c t ih =>
    have hn : ¬ (p : Int) < 1 := by omega
    simp [pairsFrom, hn, ih (p + ncuC c) (by omega)]

private theorem prevind_one (s : JS) : prevind s 1 = 0 := by
  simp [prevind, pairs_filter s 1 (by omega)]

private theorem pairs_free (q : JC) (t : JS) (h : q ∉ t) (p : Nat) :
    ∀ x ∈ pairsFrom p t, x.2 ≠ q := by
  induction t generalizing p with
  | nil => simp [pairsFrom]
  | cons c t ih =>
    have hc : c ≠ q := by intro he; subst c; simp at h
    have ht : q ∉ t := by intro hm; exact h (List.mem_cons_of_mem _ hm)
    intro x hx
    simp only [pairsFrom, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact ih ht _ x hx

private theorem loop_sq (str s sp : JS) (st : List (Nat × JC)) (σ : PState)
    (n : Nat) (hn : st.length ≤ n) (hsq : σ.inSQ = true)
    (hf : ∀ x ∈ st, x.2 ≠ A '\'') : parseLoop str s sp n st σ = .ok σ := by
  induction st generalizing n with
  | nil => simp [parseLoop]
  | cons x st ih =>
    rcases x with ⟨j, c⟩
    have hc := hf (j, c) (by simp)
    have ht : ∀ x ∈ st, x.2 ≠ A '\'' := by
      intro x hx; exact hf x (by simp [hx])
    cases n with
    | zero => simp at hn
    | succ n =>
      have hn' : st.length ≤ n := by simpa using hn
      simp [parseLoop, hsq, hc, ih n hn' ht]

private theorem loop_dq (str s sp : JS) (st : List (Nat × JC)) (σ : PState)
    (n : Nat) (hn : st.length ≤ n) (hdq : σ.inDQ = true)
    (hf : ∀ x ∈ st, x.2 ≠ A '"')
    (hb : ∀ x ∈ st, x.2 ≠ A '\\') : parseLoop str s sp n st σ = .ok σ := by
  induction st generalizing n with
  | nil => simp [parseLoop]
  | cons x st ih =>
    rcases x with ⟨j, c⟩
    have hc := hf (j, c) (by simp)
    have hbc := hb (j, c) (by simp)
    have ht : ∀ x ∈ st, x.2 ≠ A '"' := by
      intro x hx; exact hf x (by simp [hx])
    have hbt : ∀ x ∈ st, x.2 ≠ A '\\' := by
      intro x hx; exact hb x (by simp [hx])
    cases n with
    | zero => simp at hn
    | succ n =>
      have hn' : st.length ≤ n := by simpa using hn
      simp [parseLoop, hdq, hc, hbc, ih n hn' ht hbt]

private theorem parse_sq (str : JS) (h : A '\'' ∉ str) :
    shellParse (A '\'' :: str) [] = .error (.error "unterminated single quote") := by
  obtain ⟨u, hu, hmem⟩ := rstrip_cons (A '\'') str (by decide)
  have hf : A '\'' ∉ u := by
    intro hm
    exact h (hmem _ hm)
  have hl : (lstripOff (A '\'' :: str)).2 = A '\'' :: str := by
    simp [lstripOff, show isspace (A '\'') = false from by decide]
  simp only [shellParse, hl, hu, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    pairsFrom, List.length_cons]
  simp only [parseLoop]
  simp only [show isspace (A '\'') = false from by decide,
    show (A '\'' == A '\'') = true from by decide, Bool.not_false,
    Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  simp [consumeUpto, prevind_one, slice, pushNonempty]
  simp only [bind, Except.bind]
  rw [loop_sq _ _ _ _ _ _ (by simp) rfl (pairs_free _ u hf _)]
  rfl

private theorem parse_dq (str : JS) (h : A '"' ∉ str) (hb : A '\\' ∉ str) :
    shellParse (A '"' :: str) [] = .error (.error "unterminated double quote") := by
  obtain ⟨u, hu, hmem⟩ := rstrip_cons (A '"') str (by decide)
  have hf : A '"' ∉ u := by
    intro hm
    exact h (hmem _ hm)
  have hbf : A '\\' ∉ u := by
    intro hm
    exact hb (hmem _ hm)
  have hl : (lstripOff (A '"' :: str)).2 = A '"' :: str := by
    simp [lstripOff, show isspace (A '"') = false from by decide]
  simp only [shellParse, hl, hu, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    pairsFrom, List.length_cons]
  simp only [parseLoop]
  simp only [show isspace (A '"') = false from by decide,
    show (A '"' == A '\'') = false from by decide,
    show (A '"' == A '"') = true from by decide, Bool.not_false,
    Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  simp [consumeUpto, prevind_one, slice, pushNonempty]
  simp only [bind, Except.bind]
  rw [loop_dq _ _ _ _ _ _ (by simp) rfl (pairs_free _ u hf _) (pairs_free _ u hbf _)]
  rfl

end ProofQuote

theorem splitUnterminatedQuote_proven : SplitUnterminatedQuote := by
  constructor
  · intro t h
    unfold shellSplit
    rw [ProofQuote.parse_sq t h]
    rfl
  · intro t h hb
    unfold shellSplit
    rw [ProofQuote.parse_dq t h hb]
    rfl

end JuliaLean.ShellCmd
