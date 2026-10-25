import JuliaLean.ShellCmd.Props

namespace JuliaLean.ShellCmd
namespace PosixProof

private def enc (c : JC) : JS :=
  if c == A '\'' || c == A '"' then [A '\\', c] else [c]

private def allowed (first : Bool) (c : JC) : Bool :=
  isAlnum c || isCommon c || c == A '\'' || c == A '"' || (!first && c == A '=')

private theorem fuel_mono {n : Nat} {s : JS} {ws out : List JS} {cur : Option JS}
    (h : posixWords n s ws cur = some out) :
    ∀ m, n ≤ m → posixWords m s ws cur = some out := by
  induction n generalizing s ws cur with
  | zero => simp [posixWords] at h
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hnm : n ≤ m := by omega
      cases s with
      | nil => simpa only [posixWords] using h
      | cons c cs =>
        simp only [posixWords] at h ⊢
        split at h <;> rename_i hblank <;> simp only [hblank, ↓reduceIte]
        · exact ih h m hnm
        · split at h <;> rename_i hslash <;> simp only [hslash, ↓reduceIte]
          · cases cs with
            | nil => contradiction
            | cons d ds =>
              simp only at h ⊢
              split at h <;> rename_i hnl <;> simp only [hnl, ↓reduceIte] <;> exact ih h m hnm
          · split at h <;> rename_i hquote <;> simp only [hquote, ↓reduceIte]
            · split at h <;> rename_i hclose <;> simp only [hclose, ↓reduceIte]
              · exact ih h m hnm
              · contradiction
            · split at h <;> rename_i hdquote <;> simp only [hdquote, ↓reduceIte]
              · cases he : dqScan (cs.length + 1) cs with
                | none => simp [he] at h
                | some p =>
                  simp only [he] at h ⊢
                  exact ih h m hnm
              · split at h <;> rename_i hspecial <;> simp only [hspecial, ↓reduceIte]
                · contradiction
                · split at h <;> rename_i hstart <;> simp only [hstart, ↓reduceIte]
                  · contradiction
                  · split at h <;> rename_i heq <;> simp only [heq, ↓reduceIte]
                    · contradiction
                    · exact ih h m hnm

private theorem quote_prefix (q rest : JS) (hq : A '\'' ∉ q)
    (n : Nat) (ws : List JS) (cur : Option JS) :
    posixWords (n + 1) (A '\'' :: (q ++ A '\'' :: rest)) ws cur =
      posixWords n rest ws (some (cur.getD [] ++ q)) := by
  have ht : (q ++ A '\'' :: rest).takeWhile (· != A '\'') = q := by
    induction q with
    | nil => simp
    | cons c cs ih =>
      have hp : A '\'' ≠ c ∧ A '\'' ∉ cs := by simpa only [List.mem_cons, not_or] using hq
      have hc : c ≠ A '\'' := Ne.symm hp.1
      simp [hc, ih hp.2]
  have hd : (q ++ A '\'' :: rest).drop (q.length + 1) = rest := by
    simp [List.drop_append, List.drop_eq_nil_of_le (by omega : q.length ≤ q.length + 1)]
  simp only [posixWords]
  simp +decide [ht, hd]

private theorem scan_flags (first : Bool) (s : JS) (hs hd : Bool) :
    (hs = true → (posixScan first s hs hd).1 = true) ∧
    (hd = true → (posixScan first s hs hd).2.1 = true) := by
  fun_induction posixScan first s hs hd <;> simp_all

private theorem scan_spec (first : Bool) (s : JS) (hs hd : Bool)
    (h : (posixScan first s hs hd).2.2 = true) :
    (∀ c ∈ s, allowed first c = true) ∧
    ((posixScan first s hs hd).1 = false → A '\'' ∉ s) ∧
    ((posixScan first s hs hd).2.1 = false → A '"' ∉ s) := by
  have a1 : isAlnum (A '\'') = false := by decide
  have a2 : isAlnum (A '"') = false := by decide
  have b1 : isCommon (A '\'') = false := by decide
  have b2 : isCommon (A '"') = false := by decide
  induction s generalizing hs hd with
  | nil => simp
  | cons c cs ih =>
    simp only [posixScan] at h ⊢
    split at h <;> simp only [*]
    · obtain ⟨ha, hb, hd'⟩ := ih hs hd h
      have cq : c ≠ A '\'' := by intro he; subst c; simp_all
      have cd : c ≠ A '"' := by intro he; subst c; simp_all
      exact ⟨by simpa [allowed, *] using ha, by simpa [Ne.symm cq] using hb, by simpa [Ne.symm cd] using hd'⟩
    · split at h <;> simp only [*]
      · obtain ⟨ha, hb, hd'⟩ := ih hs hd h
        have cq : c ≠ A '\'' := by intro he; subst c; simp_all
        have cd : c ≠ A '"' := by intro he; subst c; simp_all
        exact ⟨by simpa [allowed, *] using ha, by simpa [Ne.symm cq] using hb, by simpa [Ne.symm cd] using hd'⟩
      · split at h <;> simp only [*]
        · rename_i hc
          have ce : c = A '\'' := by simpa using hc
          subst c
          obtain ⟨ha, hb, hd'⟩ := ih true hd h
          have hf := (scan_flags first cs true hd).1 rfl
          exact ⟨by simpa [allowed] using ha, by simp [hf], by simpa +decide using hd'⟩
        · split at h <;> simp only [*]
          · rename_i hc
            split at h <;> simp only [*]
            · contradiction
            · have ce : c = A '"' := by simpa using hc
              subst c
              obtain ⟨ha, hb, hd'⟩ := ih hs true h
              have hf := (scan_flags first cs hs true).2 rfl
              exact ⟨by simpa [allowed] using ha, by simpa +decide using hb, by simp [hf]⟩
          · split at h <;> simp only [*]
            · rename_i hc
              obtain ⟨ha, hb, hd'⟩ := ih hs hd h
              have he : first = false ∧ c = A '=' := by simpa using hc
              rcases he with ⟨hf, rfl⟩
              exact ⟨by simpa +decide [allowed, hf] using ha, by simpa +decide using hb, by simpa +decide using hd'⟩
            · contradiction

private theorem quoted_cost (s : JS) :
    ∃ k, k ≤ (A '\'' :: (replaceC s (A '\'') (S "'\\''") ++ [A '\''])).length ∧
      ∀ (q : JS), A '\'' ∉ q → ∀ (rest : JS) (n : Nat) (ws : List JS) (cur : Option JS),
        posixWords (n + k)
          (A '\'' :: (q ++ replaceC s (A '\'') (S "'\\''") ++ A '\'' :: rest)) ws cur =
        posixWords n rest ws (some (cur.getD [] ++ q ++ s)) := by
  induction s with
  | nil =>
    refine ⟨1, by simp [replaceC], ?_⟩
    intro q hq rest n ws cur
    simpa [replaceC] using quote_prefix q rest hq n ws cur
  | cons c cs ih =>
    obtain ⟨k, hk, ih⟩ := ih
    by_cases hc : c = A '\''
    · subst c
      refine ⟨k + 2, ?_, ?_⟩
      · have hr : replaceC (A '\'' :: cs) (A '\'') (S "'\\''") =
            S "'\\''" ++ replaceC cs (A '\'') (S "'\\''") := by simp [replaceC]
        rw [hr]
        have hl : (S "'\\''").length = 4 := rfl
        simp only [List.length_cons, List.length_append, hl] at hk ⊢
        omega
      · intro q hq rest n ws cur
        have h1 := quote_prefix q
          (A '\\' :: A '\'' :: A '\'' :: (replaceC cs (A '\'') (S "'\\''") ++ A '\'' :: rest))
          hq (n + k + 1) ws cur
        have h2 := ih [] (by simp) rest n ws (some (cur.getD [] ++ q ++ [A '\'']))
        simp only [List.nil_append, Option.getD_some] at h2
        calc
          _ = posixWords (n + k + 1)
              (A '\\' :: A '\'' :: A '\'' :: (replaceC cs (A '\'') (S "'\\''") ++ A '\'' :: rest))
              ws (some (cur.getD [] ++ q)) := by
                simpa [replaceC, S, List.append_assoc, Nat.add_assoc] using h1
          _ = posixWords (n + k)
              (A '\'' :: (replaceC cs (A '\'') (S "'\\''") ++ A '\'' :: rest))
              ws (some (cur.getD [] ++ q ++ [A '\''])) := by
                simp +decide [posixWords, List.append_assoc]
          _ = _ := by simpa [List.append_assoc] using h2
    · refine ⟨k, ?_, ?_⟩
      · simpa [replaceC, hc, Nat.add_assoc] using Nat.le_trans hk (Nat.le_succ _)
      · intro q hq rest n ws cur
        have hq' : A '\'' ∉ q ++ [c] := by simp [hq, Ne.symm hc]
        simpa [replaceC, hc, List.append_assoc] using ih (q ++ [c]) hq' rest n ws cur

private theorem common_safe (c : JC) (h : (isAlnum c || isCommon c) = true) :
    c ∉ S " \t\\'\"|&;<>()$`*?[\n#~=" := by
  have bad : ∀ d ∈ S " \t\\'\"|&;<>()$`*?[\n#~=", (isAlnum d || isCommon d) = false := by
    change ∀ d ∈ [A ' ', A '\t', A '\\', A '\'', A '"', A '|', A '&', A ';',
      A '<', A '>', A '(', A ')', A '$', A '`', A '*', A '?', A '[', A '\n',
      A '#', A '~', A '='], (isAlnum d || isCommon d) = false
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    decide
  intro hm
  have := bad c hm
  simp_all

private theorem char_prefix (first : Bool) (c : JC)
    (ha : allowed first c = true) (rest : JS) (n : Nat)
    (ws : List JS) (cur : Option JS) (hf : first = ws.isEmpty) :
    posixWords (n + 1) (enc c ++ rest) ws cur =
      posixWords n rest ws (some (cur.getD [] ++ [c])) := by
  by_cases hq : c = A '\''
  · subst c
    simp +decide [enc, posixWords]
  · by_cases hd : c = A '"'
    · subst c
      simp +decide [enc, posixWords]
    · by_cases he : c = A '='
      · subst c
        have hn : ws.isEmpty = false := by
          cases hw : ws.isEmpty <;> simp_all +decide [allowed, isAlnum, isCommon]
        simp +decide [enc, posixWords, hn]
      · have hs : (isAlnum c || isCommon c) = true := by
          simpa [allowed, hq, hd, he] using ha
        have hc := common_safe c hs
        change c ∉ [A ' ', A '\t', A '\\', A '\'', A '"', A '|', A '&', A ';',
          A '<', A '>', A '(', A ')', A '$', A '`', A '*', A '?', A '[', A '\n',
          A '#', A '~', A '='] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
        simp only [enc]
        simp_all [posixWords, cin, S]

private theorem bare_prefix (first : Bool) (s : JS)
    (ha : ∀ c ∈ s, allowed first c = true) (rest : JS) (n : Nat)
    (ws : List JS) (acc : JS) (hf : first = ws.isEmpty) :
    posixWords (n + s.length) (s.flatMap enc ++ rest) ws (some acc) =
      posixWords n rest ws (some (acc ++ s)) := by
  induction s generalizing acc with
  | nil => simp
  | cons c cs ih =>
    have hc : allowed first c = true := ha c (by simp)
    have ht : ∀ d ∈ cs, allowed first d = true := by
      intro d hd
      exact ha d (by simp [hd])
    have hp := char_prefix first c hc (cs.flatMap enc ++ rest) (n + cs.length) ws (some acc) hf
    simp only [Option.getD_some] at hp
    simpa [List.flatMap_cons, List.append_assoc, Nat.add_assoc] using hp.trans (ih ht (acc ++ [c]))

private theorem enc_length (s : JS) : s.length ≤ (s.flatMap enc).length := by
  induction s with
  | nil => simp
  | cons c cs ih =>
    have hc : 1 ≤ (enc c).length := by unfold enc; split <;> simp
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

private theorem bare_nonempty (first : Bool) (s : JS) (hne : s ≠ [])
    (ha : ∀ c ∈ s, allowed first c = true) :
    ∃ k, k ≤ (s.flatMap enc).length ∧
      ∀ (rest : JS) (n : Nat) (ws : List JS) (cur : Option JS),
        first = ws.isEmpty →
        posixWords (n + k) (s.flatMap enc ++ rest) ws cur =
          posixWords n rest ws (some (cur.getD [] ++ s)) := by
  refine ⟨s.length, ?_, ?_⟩
  · exact enc_length s
  · intro rest n ws cur hf
    cases s with
    | nil => contradiction
    | cons c cs =>
      have hc := ha c (by simp)
      have ht : ∀ d ∈ cs, allowed first d = true := by
        intro d hd
        exact ha d (by simp [hd])
      have hp := char_prefix first c hc (cs.flatMap enc ++ rest) (n + cs.length) ws cur hf
      simpa [List.flatMap_cons, List.append_assoc, Nat.add_assoc] using
        hp.trans (bare_prefix first cs ht rest n ws (cur.getD [] ++ [c]) hf)

private theorem bare_encoding (s : JS) (hs hd : Bool)
    (hq : hs = false → A '\'' ∉ s) (hdq : hd = false → A '"' ∉ s) :
    (if hd then replaceC (if hs then replaceC s (A '\'') (S "\\'") else s) (A '"') (S "\\\"")
      else (if hs then replaceC s (A '\'') (S "\\'") else s)) = s.flatMap enc := by
  induction s with
  | nil => cases hs <;> cases hd <;> simp [replaceC]
  | cons c cs ih =>
    have hqt : hs = false → A '\'' ∉ cs := by intro hh; exact fun hm => hq hh (by simp [hm])
    have hdt : hd = false → A '"' ∉ cs := by intro hh; exact fun hm => hdq hh (by simp [hm])
    specialize ih hqt hdt
    have hi := congrArg (fun a : JS => enc c ++ a) ih
    by_cases hc : c = A '\'' <;> by_cases hdc : c = A '"'
    all_goals cases hs <;> cases hd
    all_goals first
      | solve
        | have hh := hq rfl
          simp [hc] at hh
      | solve
        | have hh := hdq rfl
          simp [hdc] at hh
      | simpa +decide [replaceC, enc, S, hc, hdc, List.flatMap_append] using hi

private theorem word_prefix (first : Bool) (s : JS) :
    ∃ k, k ≤ (posixWord first s).length ∧
      ∀ (rest : JS) (n : Nat) (ws : List JS) (cur : Option JS),
        first = ws.isEmpty →
        posixWords (n + k) (posixWord first s ++ rest) ws cur =
          posixWords n rest ws (some (cur.getD [] ++ s)) := by
  have quoted : ∃ k, k ≤ (A '\'' :: (replaceC s (A '\'') (S "'\\''") ++ [A '\''])).length ∧
      ∀ (rest : JS) (n : Nat) (ws : List JS) (cur : Option JS),
        first = ws.isEmpty →
        posixWords (n + k) ((A '\'' :: (replaceC s (A '\'') (S "'\\''") ++ [A '\''])) ++ rest) ws cur =
          posixWords n rest ws (some (cur.getD [] ++ s)) := by
    obtain ⟨k, hk, hp⟩ := quoted_cost s
    exact ⟨k, hk, fun rest n ws cur _ => by simpa using hp [] (by simp) rest n ws cur⟩
  by_cases he : s = []
  · subst s
    simpa [posixWord, replaceC, S] using quoted
  · have hn : s.isEmpty = false := by cases s <;> simp_all
    by_cases hw : (posixScan first s false false).2.2 = true
    · obtain ⟨ha, hq, hd⟩ := scan_spec first s false false hw
      have hb := bare_encoding s (posixScan first s false false).1
        (posixScan first s false false).2.1 hq hd
      have hp := bare_nonempty first s he ha
      simpa only [posixWord, hn, Bool.false_eq_true, ↓reduceIte, hw, hb] using hp
    · simpa only [posixWord, hn, Bool.false_eq_true, ↓reduceIte, hw, List.cons_append] using quoted

private theorem tail_success (xs : List JS) (ws : List JS) (acc : JS) :
    ∃ k, k ≤ (xs.flatMap (fun a => A ' ' :: posixWord false a)).length ∧
      posixWords (k + 1) (xs.flatMap (fun a => A ' ' :: posixWord false a)) ws (some acc) =
        some (ws ++ acc :: xs) := by
  induction xs generalizing ws acc with
  | nil => exact ⟨0, by simp, by simp [posixWords]⟩
  | cons x xs ih =>
    obtain ⟨kw, hkw, hw⟩ := word_prefix false x
    obtain ⟨kt, hkt, ht⟩ := ih (ws ++ [acc]) x
    refine ⟨kt + kw + 1, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
    · have hf : false = (ws ++ [acc]).isEmpty := by simp
      have hp := hw (xs.flatMap (fun a => A ' ' :: posixWord false a))
        (kt + 1) (ws ++ [acc]) none hf
      simp only [Option.getD_none, List.nil_append] at hp
      have hstep :
          posixWords (kt + kw + 1 + 1)
            (A ' ' :: (posixWord false x ++ xs.flatMap (fun a => A ' ' :: posixWord false a))) ws (some acc) =
          posixWords (kt + 1 + kw)
            (posixWord false x ++ xs.flatMap (fun a => A ' ' :: posixWord false a)) (ws ++ [acc]) none := by
        simp +decide [posixWords, Nat.add_assoc, Nat.add_comm]
      simpa [List.flatMap_cons, List.append_assoc] using hstep.trans (hp.trans ht)

end PosixProof

theorem posixlyRoundTrip_proven : PosixlyRoundTrip := by
  intro xs
  cases xs with
  | nil => simp [shellEscapePosixly, posixSplit, posixWords]
  | cons x xs =>
    obtain ⟨kw, hkw, hw⟩ := PosixProof.word_prefix true x
    obtain ⟨kt, hkt, ht⟩ := PosixProof.tail_success xs [] x
    have hp := hw (xs.flatMap (fun a => A ' ' :: posixWord false a)) (kt + 1) [] none rfl
    simp only [Option.getD_none, List.nil_append] at hp
    have hr := hp.trans ht
    apply PosixProof.fuel_mono hr
    simp only [shellEscapePosixly, List.length_append] at *
    omega

end JuliaLean.ShellCmd
