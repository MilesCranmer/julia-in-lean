import JuliaLean.RegexUnicode.SubstProps

/-!
# Settling the substitution and regex-builder properties

Refutations use the counterexamples replayed by `repro/regexunicode-<id>.jl`.
-/

namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

/-! ## Refutations -/

/-- `io = PipeBuffer(); write(io, "head"); read(io, UInt8); replace(io, "abc", r"(b)" =>
s"<\1>")`: the capture lands at the read position, which then moves. -/
theorem replaceCaptureAppend_refuted : ¬ ReplaceCaptureAppend := by
  intro h
  have := h (.pipe (.mem []) (2 ^ 63 - 1)) [.write [104, 101, 97, 100], .readByte]
    (.grp 1 (.lit 98)) [97, 98, 99] [60, 92, 49, 62] (by decide) (by decide)
  revert this
  decide +kernel

/-- `replace(devnull, "abc", r"(b)" => s"<\1>")` throws `MethodError` (no `ensureroom`),
while `replace("abc", r"(b)" => s"<\1>") == "a<b>c"`. -/
theorem replaceCaptureGenericIO_refuted : ¬ ReplaceCaptureGenericIO := by
  intro h
  have := h (.other []) (Or.inl ⟨[], rfl⟩) (.grp 1 (.lit 98)) [97, 98, 99] [60, 92, 49, 62]
    (by decide) (by decide) (by decide +kernel)
  revert this
  decide +kernel

/-- `s"\g<>"` with `r"(a)"` on `"ab"` throws `ArgumentError` from `parse(Int, "")`. -/
theorem substEmptyGroupName_refuted : ¬ SubstEmptyGroupName := by
  intro h
  have := h (.grp 1 (.lit 97)) [97, 98] 0 _ rfl (.other []) [92, 103, 60, 62] (by decide) (by decide)
  revert this
  decide

/-- `s"\18446744073709551617"` with `r"(a)"` on `"ab"` writes group 1: the digit loop wraps
to `1`. -/
theorem substGroupRef_refuted : ¬ SubstGroupRef := by
  intro h
  have := h (.grp 1 (.lit 97)) [97, 98] 0
    [49, 56, 52, 52, 54, 55, 52, 52, 48, 55, 51, 55, 48, 57, 53, 53, 49, 54, 49, 55]
    (by decide) (by decide)
  revert this
  decide +kernel

/-- `r"a"^-1 == r"(?:a){-1}"`, in which `{-1}` is literal text. -/
theorem regexPowQuant_refuted : ¬ RegexPowQuant := by
  intro h
  have := h ⟨['a'], noFlags, 0, 0⟩ (-1) (by decide)
  revert this
  decide

/-- `r"a  # the letter a"x * "b"`: the comment swallows the closing parenthesis. -/
theorem regexConcatCompiles_refuted : ¬ RegexConcatCompiles := by
  intro h
  have := h ⟨"a  # the letter a".toList, ⟨false, false, false, true⟩, 0, 0⟩ ['b'] (by decide)
  revert this
  decide

/-- `match(r"(?J)(?<x>a)|(?<x>b)", "b")`: `keys(m) == ["x", "x"]` but `haskey(m, "x")` is
false. -/
theorem dupnamesHaskey_refuted : ¬ DupnamesHaskey := by
  intro h
  have hk := h 2 [(1, [120]), (2, [120])] (by decide) (.name [120]) (by decide)
  have e : haskey 2 [(1, [120]), (2, [120])] (.name [120]) = .ok false := rfl
  rw [e] at hk
  cases hk

/-! ## `regexunicode-subst-literal` -/

theorem drop_cons_getD {l : List UInt8} {p : Nat} (h : p < l.length) :
    l.drop p = l.getD p 0 :: l.drop (p + 1) := by
  rw [List.drop_eq_getElem_cons h]
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ne_sub {l : List UInt8} {p : Nat} (h : p < l.length) (hs : SUB ∉ l) :
    l.getD p 0 ≠ SUB := by
  intro he
  apply hs
  rw [← he]
  simp [List.getD_eq_getElem?_getD, h]

theorem substLoop_literal (ctx : Ctx) (repl : List UInt8) (hs : SUB ∉ repl) :
    ∀ fuel p nb, repl.length < fuel + p →
      substLoop ctx repl fuel p nb = writeChars (repl.drop p) nb := by
  intro fuel
  induction fuel with
  | zero =>
    intro p nb hf
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ f ih =>
    intro p nb hf
    by_cases hp : repl.length ≤ p
    · rw [List.drop_eq_nil_of_le hp]
      simp [substLoop, hp, writeChars]
    · have hlt : p < repl.length := by omega
      rw [drop_cons_getD hlt]
      simp only [substLoop, hp, getD_ne_sub hlt hs, ↓reduceIte, writeChars]
      congr 1
      funext w
      exact ih (p + 1) (nb + w) (by omega)

theorem writeChars_other (cs : List UInt8) :
    ∀ (nb : I) (out : List UInt8), ∃ nb', writeChars cs nb (.other out) = .ok nb' (.other (out ++ cs)) := by
  induction cs with
  | nil => intro nb out; exact ⟨nb, by simp; rfl⟩
  | cons c t ih =>
    intro nb out
    obtain ⟨nb', h⟩ := ih (nb + i 1) (out ++ [c])
    have e : writeChars (c :: t) nb (.other out) = writeChars t (nb + i 1) (.other (out ++ [c])) := rfl
    exact ⟨nb', by rw [e, h]; simp⟩

theorem substLiteral_proven : SubstLiteral := by
  intro ctx repl hs
  have hstep : ∀ snk, substStep ctx repl snk = writeChars repl (i 0) snk := by
    intro snk
    unfold substStep
    rw [substLoop_literal ctx repl hs (repl.length + 1) 0 (i 0) (by omega)]
    rfl
  refine ⟨hstep, fun out => ?_⟩
  rw [hstep]
  exact writeChars_other repl (i 0) out

/-! ## `regexunicode-concat-quote` -/

/-- Lexer steps spent on `replaceE s ++ "\E"` inside a quote. -/
def qcost : List Char → Nat
  | [] => 1
  | [_] => 2
  | c :: d :: t => if c = '\\' ∧ d = 'E' then 4 + qcost t else 1 + qcost (d :: t)

theorem replaceE_head (d : Char) (t : List Char) : ∃ r, replaceE (d :: t) = d :: r := by
  cases t with
  | nil => exact ⟨[], rfl⟩
  | cons e t' =>
    by_cases h : d = '\\' ∧ e = 'E'
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨'\\' :: 'E' :: '\\' :: 'Q' :: 'E' :: replaceE t', by simp [replaceE]⟩
    · exact ⟨replaceE (e :: t'), by simp [replaceE, h]⟩

theorem lexAux_quote_lit (f : Nat) (c : Char) (t : List Char) (ext : Bool) (stk : List Bool)
    (acc : List Tok) (h : ¬ (c = '\\' ∧ t.head? = some 'E')) :
    lexAux (f + 1) (c :: t) true ext stk acc = lexAux f t true ext stk (.lit c :: acc) := by
  simp only [lexAux]
  split
  · exact absurd ‹_› h
  · rfl

theorem lexAux_quote_exit (f : Nat) (t : List Char) (ext : Bool) (stk : List Bool) (acc : List Tok) :
    lexAux (f + 1) ('\\' :: 'E' :: t) true ext stk acc = lexAux f t false ext stk acc := by
  simp [lexAux]

theorem lexAux_enter (f : Nat) (t : List Char) (ext : Bool) (stk : List Bool) (acc : List Tok) :
    lexAux (f + 1) ('\\' :: 'Q' :: t) false ext stk acc = lexAux f t true ext stk acc := by
  simp +decide [lexAux]

theorem quote_body (s : List Char) :
    ∀ (rest : List Char) (ext : Bool) (stk : List Bool) (acc : List Tok) (f : Nat),
      lexAux (f + qcost s) (replaceE s ++ '\\' :: 'E' :: rest) true ext stk acc =
        lexAux f rest false ext stk ((s.map Tok.lit).reverse ++ acc) := by
  induction s using replaceE.induct with
  | case1 =>
    intro rest ext stk acc f
    simp only [qcost, replaceE, List.nil_append, List.map_nil, List.reverse_nil]
    exact lexAux_quote_exit f rest ext stk acc
  | case2 c =>
    intro rest ext stk acc f
    simp only [qcost, replaceE, List.cons_append, List.nil_append]
    rw [show f + 2 = (f + 1) + 1 by omega,
      lexAux_quote_lit _ _ _ _ _ _ (by simp +decide), lexAux_quote_exit]
    simp
  | case3 c d t h ih =>
    obtain ⟨rfl, rfl⟩ := h
    intro rest ext stk acc f
    have hq : qcost ('\\' :: 'E' :: t) = 4 + qcost t := by simp [qcost]
    have hr : replaceE ('\\' :: 'E' :: t) = ['\\', '\\', 'E', '\\', 'Q', 'E'] ++ replaceE t := by
      simp [replaceE]
    rw [hq, hr, show f + (4 + qcost t) = (f + qcost t) + 1 + 1 + 1 + 1 by omega]
    simp only [List.cons_append, List.nil_append]
    rw [lexAux_quote_lit _ _ _ _ _ _ (by simp +decide), lexAux_quote_exit, lexAux_enter,
      lexAux_quote_lit _ _ _ _ _ _ (by simp +decide), ih]
    simp
  | case4 c d t h ih =>
    intro rest ext stk acc f
    obtain ⟨r, hr⟩ := replaceE_head d t
    have hq : qcost (c :: d :: t) = 1 + qcost (d :: t) := by simp [qcost, h]
    have he : replaceE (c :: d :: t) = c :: replaceE (d :: t) := by simp [replaceE, h]
    rw [hq, he, show f + (1 + qcost (d :: t)) = (f + qcost (d :: t)) + 1 by omega,
      List.cons_append, lexAux_quote_lit _ _ _ _ _ _ (by rw [hr]; simpa using h), ih]
    simp

theorem qcost_le (s : List Char) : qcost s ≤ (replaceE s).length + 1 := by
  induction s using replaceE.induct with
  | case1 => simp [qcost, replaceE]
  | case2 c => simp [qcost, replaceE]
  | case3 c d t h ih =>
    obtain ⟨rfl, rfl⟩ := h
    simp [qcost, replaceE]
    omega
  | case4 c d t h ih =>
    simp [qcost, replaceE, h]
    omega

theorem wrap_lex_prefix (s rest : List Char) (ext : Bool) (stk : List Bool) (acc : List Tok) (f : Nat) :
    lexAux (f + (1 + qcost s)) (wrapString s ++ rest) false ext stk acc =
      lexAux f rest false ext stk ((s.map Tok.lit).reverse ++ acc) := by
  rw [show f + (1 + qcost s) = (f + qcost s) + 1 by omega]
  simp only [wrapString, List.append_assoc, List.cons_append, List.nil_append]
  rw [lexAux_enter]
  exact quote_body s rest ext stk acc f

theorem concatQuote_proven : ConcatQuote := by
  intro s ext
  refine ⟨?_, ⟨1 + qcost s, fun rest stk acc f => wrap_lex_prefix s rest ext stk acc f⟩⟩
  have hq := qcost_le s
  have hl : (wrapString s).length = (replaceE s).length + 4 := by simp [wrapString]
  have hw := wrap_lex_prefix s [] ext [] [] ((replaceE s).length + 3 - qcost s + 1)
  rw [List.append_nil] at hw
  unfold lex
  rw [hl, show (replaceE s).length + 4 + 1 = ((replaceE s).length + 3 - qcost s + 1) + (1 + qcost s) by omega,
    hw]
  simp [lexAux]

end JuliaLean.RegexUnicode.Subst
