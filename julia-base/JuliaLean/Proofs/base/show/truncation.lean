import JuliaLean.base.show
import JuliaLean.base.strings.io
import JuliaLean.Proofs.base.coreio.showSupport
import JuliaLean.Proofs.base.strings.io.escapeRoundTrip


namespace JuliaLean.ShowCov

open Truncate StringsIO

/-- `_truncate_at_width_or_chars(false, str, width, rpad)` returns text that fits
in `width` columns, for character widths of at most 2 and the default one-column
truncation mark (`base/show.jl:104-135`, used by limited `Dict`/`Set` display). -/
def TruncateFitsWidth : Prop :=
  ∀ (tw : Char → Nat) (str : List Char) (width : Int) (rpad : Bool),
    (∀ c, tw c ≤ 2) → tw '…' = 1 → 1 ≤ width →
    (textwidth tw (truncateAt tw false str width rpad) : Int) ≤ width

/-- Julia's `textwidth` on the characters used below. -/
def cjkTw (c : Char) : Nat := if c = '中' then 2 else 1

theorem truncateFitsWidth_refuted : ¬ TruncateFitsWidth := by
  intro h
  have := h cjkTw ['a', 'b', '中'] 3 false (by intro c; unfold cjkTw; split <;> omega) (by decide) (by decide)
  revert this
  decide

/-- With ANSI escapes ignored, the result gains a `"\e[0m"` only when the last
escape sequence before the cut is not already `"\e[0m"`: a string whose only
escape sequence is a reset keeps a single escape (`base/show.jl:110,114,127`). -/
def TruncateResetOnlyWhenNeeded : Prop :=
  ∀ (tw : Char → Nat) (a b : List Char) (width : Int),
    (∀ c ∈ a ++ b, c.toNat ≠ 0x1b) →
    (truncateAt tw true (a ++ resetSeq ++ b) width).count '\x1b' ≤ 1

theorem truncateResetOnlyWhenNeeded_refuted : ¬ TruncateResetOnlyWhenNeeded := by
  intro h
  have := h (fun _ => 1) ['a', 'b'] ['c', 'd', 'e', 'f', 'g', 'h'] 4 (by decide)
  revert this
  decide

/-- Degenerate widths: a nonpositive width, or one narrower than the truncation
mark, gives `""`; an empty string gives `""`, or `width` spaces with `rpad`
(`base/show.jl:105-106,125`). -/
def TruncateDegenerate : Prop :=
  ∀ (tw : Char → Nat) (ign : Bool) (str : List Char) (width : Int) (rpad : Bool) (chars mark : List Char),
    (width ≤ 0 → truncateAt tw ign str width rpad chars mark = []) ∧
    (width < textwidth tw mark → truncateAt tw ign str width rpad chars mark = []) ∧
    (0 < width → (textwidth tw mark : Int) ≤ width →
      truncateAt tw ign [] width rpad chars mark = if rpad then List.replicate width.toNat ' ' else [])

theorem truncateDegenerate_proven : TruncateDegenerate := by
  intro tw ign str width rpad chars mark
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [truncateAt, h]
  · intro h; simp [truncateAt, h]
  · intro h1 h2
    have h3 : ¬ width ≤ 0 := by omega
    have h4 : ¬ width < (textwidth tw mark : Int) := by omega
    cases ign <;> simp [truncateAt, h3, h4, ansiTokens, ansiTokensF, charTokens, indexed, truncLoop]

/-! ## `ANSIIterator` -/

theorem ansiMatch_plain (c : Char) (cs : List Char) (h : c.toNat ≠ 0x1b) :
    ansiMatch (c :: cs) = some (.ch c, cs) := by
  simp [ansiMatch, h]

theorem ansiTokensF_plain (s : List Char) (n : Nat) (hn : s.length ≤ n) (h : ∀ c ∈ s, c.toNat ≠ 0x1b) :
    ansiTokensF n s = s.map Tok.ch := by
  induction s generalizing n with
  | nil => cases n <;> simp [ansiTokensF, ansiMatch]
  | cons c cs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      simp only [ansiTokensF, ansiMatch_plain c cs (h c (by simp)), List.map_cons]
      rw [ih n (by simp at hn; omega) (fun x hx => h x (by simp [hx]))]

/-- `ANSIIterator(s)` yields each character of an escape-free string as a `Char`
(so its `textwidth` is the string's), an `ANSIDelimiter` has `textwidth` 0 and
the `ncodeunits` of its text, and the reset sequence `"\e[0m"` is matched as one
delimiter; the iterator's `IteratorSize` is `SizeUnknown` and its `eltype` is
`Pair{Int, Union{Char,ANSIDelimiter}}` (`base/show.jl:79-102`). -/
def AnsiIteratorSpec : Prop :=
  ∀ (tw : Char → Nat) (s rest : List Char) (d : List Char),
    ((∀ c ∈ s, c.toNat ≠ 0x1b) → ansiTokens s = s.map Tok.ch ∧ ansiWidth tw s = textwidth tw s) ∧
    Tok.width tw (.ansi d) = 0 ∧ Tok.ncu (.ansi d) = (d.map Char.utf8Size).sum ∧
    ansiMatch (resetSeq ++ rest) = some (.ansi resetSeq, rest) ∧
    iteratorSizeANSI = "SizeUnknown" ∧ eltypeANSI = "Pair{Int, Union{Char,ANSIDelimiter}}"

theorem ansiIteratorSpec_proven : AnsiIteratorSpec := by
  intro tw s rest d
  refine ⟨?_, rfl, rfl, ?_, rfl, rfl⟩
  · intro h
    have ht : ansiTokens s = s.map Tok.ch := ansiTokensF_plain s s.length (Nat.le_refl _) h
    refine ⟨ht, ?_⟩
    simp only [ansiWidth, ht, textwidth, List.map_map]
    rfl
  · simp [ansiMatch, resetSeq, spanRange, inRange]

/-! ## `type_depth_limit` -/

/-- `repr(c)` for a printable ASCII character: `'c'`, with `'` and `\` escaped
by a backslash (`show(io, c::AbstractChar)`, `base/char.jl`). -/
def reprAsciiChar (c : Char) : List Char :=
  if c = '\'' then ['\'', '\\', '\'', '\''] else if c = '\\' then ['\'', '\\', '\\', '\''] else ['\'', c, '\'']

/-- The type string `A{c}B{C}` for a `Char` parameter `c`. -/
def charParamType (c : Char) : List Char := ['A', '{'] ++ reprAsciiChar c ++ ['}', 'B', '{', 'C', '}']

/-- `type_depth_limit` ignores braces inside character literals: for every
printable ASCII `Char` parameter `c`, limiting `A{c}B{C}` to depth 1 gives
`A{…}B{…}` (`base/show.jl:2725-2816`; printable ASCII has `textwidth` 1). -/
def TypeDepthLimitCharParam : Prop :=
  ∀ c : Char, 0x20 ≤ c.toNat → c.toNat ≤ 0x7e →
    typeDepthLimit (fun _ => 1) (charParamType c) 0 (some 1) = .ok ['A', '{', '…', '}', 'B', '{', '…', '}']

theorem typeDepthLimitCharParam_refuted : ¬ TypeDepthLimitCharParam := by
  intro h
  have := h '\\' (by decide) (by decide)
  revert this
  decide

/-- The same holds for every printable ASCII character other than the backslash. -/
def TypeDepthLimitCharParamNoBackslash : Prop :=
  ∀ c : Char, 0x20 ≤ c.toNat → c.toNat ≤ 0x7e → c ≠ '\\' →
    typeDepthLimit (fun _ => 1) (charParamType c) 0 (some 1) = .ok ['A', '{', '…', '}', 'B', '{', '…', '}']

theorem tdl_all_ascii : ∀ n, n < 95 → Char.ofNat (n + 0x20) ≠ '\\' →
    typeDepthLimit (fun _ => 1) (charParamType (Char.ofNat (n + 0x20))) 0 (some 1) =
      .ok ['A', '{', '…', '}', 'B', '{', '…', '}'] := by
  decide +kernel

theorem typeDepthLimitCharParamNoBackslash_proven : TypeDepthLimitCharParamNoBackslash := by
  intro c h1 h2 h3
  have hc : c = Char.ofNat (c.toNat - 0x20 + 0x20) := by
    rw [Nat.sub_add_cancel h1]; exact (Char.ofNat_toNat c).symm
  rw [hc] at h3 ⊢
  exact tdl_all_ascii (c.toNat - 0x20) (by omega) h3

/-- A depth limit at or above the maximal nesting keeps the string unchanged
when it has no quotes or escapes (`base/show.jl:2799-2815`). -/
def TypeDepthLimitWide : Prop :=
  ∀ (tw : Char → Nat) (s : List Char), (∀ c ∈ s, c ∉ ['{', '}', '\'', '"', '\\', '\x1b']) →
    typeDepthLimit tw s 0 (some 1) = .ok s

theorem pass1_flat (tw : Char → Nat) (s : List Char) (h : ∀ c ∈ s, c ∉ ['{', '}', '\'', '"', '\\', '\x1b'])
    (p : Pass1) (hp : p.depth = 0) (hq : p.q = ⟨false, false, false⟩) :
    ∃ p', (s.map Tok.ch).foldlM (pass1Step tw) p = .ok p' ∧ p'.depths = p.depths ++ s.map (fun _ => 0) := by
  induction s generalizing p with
  | nil => exact ⟨p, rfl, by simp⟩
  | cons c cs ih =>
    have hc := h c (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    obtain ⟨h1, h2, h3, h4, h5, _⟩ := hc
    let p1 : Pass1 := ⟨p.depth, if p.depth > 0 then bumpAt p.widthAt (p.depth.toNat - 1) (tw c) else p.widthAt,
      p.levelcount, p.strwid + tw c, p.q, p.depths ++ [p.depth]⟩
    have step : pass1Step tw p (.ch c) = .ok p1 := by
      simp [pass1Step, h1, h2, h3, h4, h5, hq, QState.quoted, p1]
    obtain ⟨p', hf, hd⟩ := ih (fun x hx => h x (by simp [hx])) p1 (by simp [p1, hp]) (by simp [p1, hq])
    refine ⟨p', ?_, ?_⟩
    · simp only [List.map_cons, List.foldlM_cons, step, R.ok_bind]; exact hf
    · rw [hd]; simp [p1, hp]

theorem pass2_flat (s : List Char) (prev : Int) (hprev : prev = 0) :
    pass2 1 prev ((s.map Tok.ch).zip (s.map (fun _ => (0 : Int)))) = s := by
  subst hprev
  induction s with
  | nil => rfl
  | cons c cs ih => simp [pass2, ih]

theorem typeDepthLimitWide_proven : TypeDepthLimitWide := by
  intro tw s h
  have hesc : ∀ c ∈ s, c.toNat ≠ 0x1b := by
    intro c hc heq
    apply h c hc
    have : c = '\x1b' := by rw [← Char.ofNat_toNat c, heq]
    simp [this]
  have ht : ansiTokens s = s.map Tok.ch := ansiTokensF_plain s s.length (Nat.le_refl _) hesc
  obtain ⟨p', hf, hd⟩ := pass1_flat tw s h ⟨0, [], [], 0, ⟨false, false, false⟩, []⟩ rfl rfl
  simp only [typeDepthLimit, ht, pass1, hf, R.ok_bind, hd, List.nil_append, R.pure_eq]
  rw [pass2_flat s 0 rfl]

end JuliaLean.ShowCov
