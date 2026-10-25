import JuliaLean.ShellCmd.Props

namespace JuliaLean.ShellCmd

namespace WinProof

@[simp] private theorem quote_ne_caret : A '"' ≠ A '^' := by decide
@[simp] private theorem at_ne_quote : A '@' ≠ A '"' := by decide
@[simp] private theorem at_ne_caret : A '@' ≠ A '^' := by decide
@[simp] private theorem caret_ne_at : A '^' ≠ A '@' := by decide
@[simp] private theorem at_not_operator : cin (A '@') (S "()!<>&|") = false := by decide

private theorem split_quote (s : JS) (h : A '"' ∈ s) :
    ∃ pre post, s = pre ++ A '"' :: post ∧ A '"' ∉ pre := by
  induction s with
  | nil => simp at h
  | cons c cs ih =>
    by_cases hc : c = A '"'
    · subst c
      exact ⟨[], cs, rfl, by simp⟩
    · have ht : A '"' ∈ cs := by simpa [hc, eq_comm] using h
      obtain ⟨pre, post, hs, hp⟩ := ih ht
      exact ⟨c :: pre, post, by simp [hs], by simp [hc, eq_comm, hp]⟩

private theorem take_quote (pre post : JS) (h : A '"' ∉ pre) :
    (pre ++ A '"' :: post).takeWhile (· != A '"') = pre := by
  induction pre with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≠ A '"' := fun he => h (by simp [he])
    have ht : A '"' ∉ cs := fun hm => h (by simp [hm])
    simp [hc, ih ht]

private theorem drop_quote (pre post : JS) :
    (pre ++ A '"' :: post).drop (pre.length + 1) = post := by
  induction pre with
  | nil => simp
  | cons c cs ih => simp_all [Nat.add_assoc]

private theorem phase_quoted (pre tail : JS) (h : A '"' ∉ pre) :
    cmdPhase2 (pre ++ A '"' :: tail) true =
      (cmdPhase2 tail false).map (fun t => pre ++ A '"' :: t) := by
  induction pre with
  | nil => simp [cmdPhase2]
  | cons c cs ih =>
    have hc : c ≠ A '"' := fun he => h (by simp [he])
    have ht : A '"' ∉ cs := fun hm => h (by simp [hm])
    have hb : (c != A '"') = true := by simpa using hc
    simp [cmdPhase2, hb, ih ht, Option.map_map, Function.comp_def]

private theorem special_at : wincmdSpecial (A '@') = false := by decide

private theorem nonspecial (c : JC) (h : wincmdSpecial c = false) :
    c ≠ A '^' ∧ c ≠ A '"' ∧ cin c (S "()!<>&|") = false := by
  simp_all [wincmdSpecial, cin, S, Bool.or_eq_false_iff]

private theorem loop_inverse (n : Nat) (s : JS) (hn : s.length < n) :
    cmdPhase2 (wincmdLoop n s) false = some s := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    cases s with
    | nil => simp [wincmdLoop, cmdPhase2]
    | cons c cs =>
      have ht : cs.length < n := by simpa using hn
      by_cases hp : (c == A '"' && cs.contains (A '"')) = true
      · have hh : c = A '"' ∧ A '"' ∈ cs := by simpa using hp
        obtain ⟨hc, hm⟩ := hh
        obtain ⟨pre, post, hs, hpre⟩ := split_quote cs hm
        have hpost : post.length < n := by simp [hs] at ht; omega
        subst c
        simp only [wincmdLoop, hp, ↓reduceIte]
        rw [hs, take_quote pre post hpre, drop_quote]
        simp only [List.cons_append, List.append_assoc]
        rw [cmdPhase2.eq_def]
        simp [phase_quoted pre _ hpre, ih post hpost]
      · simp only [wincmdLoop, hp, Bool.false_eq_true, ↓reduceIte]
        by_cases hc : wincmdSpecial c = true
        · simp [hc, cmdPhase2, ih cs ht]
        · have hf : wincmdSpecial c = false := Bool.eq_false_iff.mpr hc
          obtain ⟨hcaret, hquote, hop⟩ := nonspecial c hf
          simp only [hf, Bool.false_eq_true, ↓reduceIte, List.singleton_append]
          rw [cmdPhase2.eq_def]
          simp [hcaret, hquote, hop, ih cs ht]

private theorem loop_head (n : Nat) (c : JC) (cs : JS) (hn : 0 < n)
    (hc : c ≠ A '@') : (wincmdLoop n (c :: cs)).head? ≠ some (A '@') := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [wincmdLoop]
    split
    · simpa using hc
    · split
      · simp only [List.cons_append, List.head?_cons]
        decide
      · simpa using hc

private theorem no_control (s : JS) (hr : A '\r' ∉ s) (hn : A '\n' ∉ s)
    (hz : A '\x00' ∉ s) :
    s.any (fun c => c == A '\r' || c == A '\n' || c == A '\x00') = false := by
  simp only [List.any_eq_false]
  intro c hc
  have hcr : c ≠ A '\r' := fun he => hr (he ▸ hc)
  have hcn : c ≠ A '\n' := fun he => hn (he ▸ hc)
  have hcz : c ≠ A '\x00' := fun he => hz (he ▸ hc)
  simp [hcr, hcn, hcz]

end WinProof

theorem wincmdRoundTrip_proven : WincmdRoundTrip := by
  intro s _ hr hn hz
  refine ⟨(if s.head? == some (A '@') then [A '^'] else []) ++
    wincmdLoop (s.length + 1) s, ?_, ?_⟩
  · simp [shellEscapeWincmd, WinProof.no_control s hr hn hz]
  · cases s with
    | nil => simp [cmdLine, wincmdLoop, cmdPhase2]
    | cons c cs =>
      by_cases hc : c = A '@'
      · subst c
        have he : wincmdLoop (cs.length + 2) (A '@' :: cs) =
            A '@' :: wincmdLoop (cs.length + 1) cs := by
          simp [wincmdLoop, WinProof.special_at]
        simp [he, cmdLine, cmdPhase2, WinProof.loop_inverse, Nat.lt_add_one]
      · have hh := WinProof.loop_head (cs.length + 2) c cs (by omega) hc
        simp [hc, cmdLine, hh, WinProof.loop_inverse, Nat.lt_add_one, Nat.add_assoc]

theorem wincmdControlThrows_proven : WincmdControlThrows := by
  intro s h
  refine ⟨"control character unsupported by CMD.EXE", ?_⟩
  have ha : s.any (fun c => c == A '\r' || c == A '\n' || c == A '\x00') = true := by
    rcases h with hr | hn | hz
    · exact List.any_eq_true.mpr ⟨A '\r', hr, by decide⟩
    · exact List.any_eq_true.mpr ⟨A '\n', hn, by decide⟩
    · exact List.any_eq_true.mpr ⟨A '\x00', hz, by decide⟩
  simp [shellEscapeWincmd, ha]

end JuliaLean.ShellCmd
