import JuliaLean.ShowCov.Truncate
import JuliaLean.ShowCov.StringsIO
import JuliaLean.Show.EscapeRoundTrip

/-!
Properties of the ANSI-aware truncation helpers in `base/show.jl` and of
`base/strings/io.jl`.
-/

namespace JuliaLean.ShowCov

open Truncate StringsIO

/-! ## `_truncate_at_width_or_chars` -/

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

/-! ## `print`, `println`, `sprint`, `string` -/

@[simp] theorem evText_append (a b : List Ev) : evText (a ++ b) = evText a ++ evText b := by
  induction a with
  | nil => simp [evText]
  | cons e es ih => cases e <;> simp [evText, ih, String.append_assoc]

@[simp] theorem lockDepth_append (a b : List Ev) : lockDepth (a ++ b) = lockDepth a + lockDepth b := by
  induction a with
  | nil => simp [lockDepth]
  | cons e es ih => cases e <;> simp [lockDepth, ih] <;> omega

theorem printMany_go (items : List Shown) (h : ∀ x ∈ items, x.err = none) :
    (printMany.go items).2 = none ∧
    evText (printMany.go items).1 = String.join (items.map (fun x => evText x.evs)) ∧
    ((∀ x ∈ items, lockDepth x.evs = 0) → lockDepth (printMany.go items).1 = 0) := by
  induction items with
  | nil => simp [printMany.go, evText, lockDepth]
  | cons x xs ih =>
    have hx := h x (by simp)
    obtain ⟨i1, i2, i3⟩ := ih (fun y hy => h y (by simp [hy]))
    simp only [printMany.go, printAny, hx]
    refine ⟨i1, ?_, ?_⟩
    · simp [i2, evText, String.join_cons]
    · intro hl
      simp [lockDepth, i3 (fun y hy => hl y (by simp [hy])), hl x (by simp)]

/-- `print(io, x)` writes exactly what `show(io, x)` writes under one
`lock`/`unlock` pair, released even when `show` throws; `print(io, xs...)` and
`println(io, xs...)` write the arguments' texts in order (plus `"\n"`), with
balanced locking (`base/strings/io.jl:32-77`). -/
def PrintLocking : Prop :=
  ∀ (shown : Shown) (items : List Shown),
    (printAny shown).evs = [.lock] ++ shown.evs ++ [.unlock] ∧ (printAny shown).err = shown.err ∧
    lockDepth (printAny shown).evs = lockDepth shown.evs ∧ evText (printAny shown).evs = evText shown.evs ∧
    ((∀ x ∈ items, x.err = none) →
      (printMany items).err = none ∧
      evText (printMany items).evs = String.join (items.map (fun x => evText x.evs)) ∧
      evText (printlnMany items).evs = String.join (items.map (fun x => evText x.evs)) ++ "\n" ∧
      ((∀ x ∈ items, lockDepth x.evs = 0) → lockDepth (printMany items).evs = 0))

theorem printLocking_proven : PrintLocking := by
  intro shown items
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simp [printAny, lockDepth]; omega
  · simp [printAny, evText]
  · intro h
    obtain ⟨g1, g2, g3⟩ := printMany_go items h
    have h' : ∀ x ∈ items ++ [strArg "\n"], x.err = none := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · simp at hx; subst hx; rfl
    obtain ⟨_, l2, _⟩ := printMany_go (items ++ [strArg "\n"]) h'
    refine ⟨g1, ?_, ?_, ?_⟩
    · simp [printMany, g2, evText]
    · have l2' := l2
      simp only [List.map_append, String.join_append] at l2'
      simp only [printlnMany, printMany, evText_append]
      rw [l2']; simp [strArg, evText]
    · intro hl
      simp [printMany, lockDepth, g3 hl]

/-- `sprint(f, args...; context)` returns the text `f` wrote (rethrowing its
exception), with the stream carrying the `context` properties: one pair, a
tuple of pairs (the last pair is the newest binding), or another stream's
properties; `repr` is `sprint(show, ...)` and `limitrepr` adds `:limit => true`
(`base/strings/io.jl:104-114, 284-286`). -/
def SprintCollects : Prop :=
  ∀ (f : Props → Shown) (ctx : Ctx) (sz : Nat) (kvs : List (String × String)) (kv : String × String) (p : Props),
    ((f (ctxProps ctx)).err = none → sprint f ctx sz = .ok (evText (f (ctxProps ctx)).evs)) ∧
    (∀ e, (f (ctxProps ctx)).err = some e → sprint f ctx sz = .error e) ∧
    ctxProps (.tuple (kvs ++ [kv])) = kv :: (ctxProps (.tuple kvs)) ∧
    ctxProps (.pair kv) = [kv] ∧ ctxProps .none = [] ∧ ctxProps (.io p) = p ∧
    repr f ctx = sprint f ctx ∧ limitrepr f = sprint f (.pair ("limit", "true"))

theorem sprintCollects_proven : SprintCollects := by
  intro f ctx sz kvs kv p
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro h; simp [sprint, h]
  · intro e h; simp [sprint, h]
  · simp [ctxProps]

/-- Julia's `string(n)` for an integer: optional `-` and the decimal digits. -/
def intDigits (n : Int) : List Char := (if n < 0 then ['-'] else []) ++ Nat.toDigits 10 n.natAbs

/-- `_str_sizehint(x)` is the exact byte length of `string(x)` for `String`s,
`Char`s and 32/64-bit integers, and the fixed guesses 20, 12, 8 otherwise;
`print_to_string`/`string(xs...)`/`string_with_env` return `""` for no
arguments and otherwise the concatenated `print` texts, whatever the size hint;
`string(::Symbol)` is the name (`base/strings/io.jl:116-188`). -/
def StringBuilding : Prop :=
  ∀ (n : Int) (u : Nat) (s : List Char) (c : Char) (xs : List (Arg × Shown))
    (env : Props) (ys : List (Arg × (Props → Shown))) (name : String),
    strSizehint (.i64 n) = (intDigits n).length ∧ strSizehint (.i32 n) = (intDigits n).length ∧
    strSizehint (.u64 u) = (intDigits u).length ∧ strSizehint (.u32 u) = (intDigits u).length ∧
    strSizehint (.str s) = (s.map Char.utf8Size).sum ∧ strSizehint (.char c) = c.utf8Size ∧
    strSizehint .float64 = 20 ∧ strSizehint .float32 = 12 ∧ strSizehint .other = 8 ∧
    printToString [] = .ok "" ∧ stringWithEnv env [] = .ok "" ∧
    ((∀ x ∈ xs, x.2.err = none) → xs ≠ [] →
      printToString xs = .ok (String.join (xs.map (fun x => evText x.2.evs))) ∧
      string xs = .ok (String.join (xs.map (fun x => evText x.2.evs)))) ∧
    ((∀ y ∈ ys, (y.2 env).err = none) → ys ≠ [] →
      stringWithEnv env ys = .ok (String.join (ys.map (fun y => evText (y.2 env).evs)))) ∧
    stringSym name = name

theorem stringBuilding_proven : StringBuilding := by
  intro n u s c xs env ys name
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · show ndigits10 n + (if n < 0 then 1 else 0) = (intDigits n).length
    unfold intDigits ndigits10; split <;> simp <;> omega
  · show ndigits10 n + (if n < 0 then 1 else 0) = (intDigits n).length
    unfold intDigits ndigits10; split <;> simp <;> omega
  · simp [strSizehint, intDigits, ndigits10]
  · simp [strSizehint, intDigits, ndigits10]
  · intro h hne
    have h' : ∀ x ∈ xs.map (·.2), x.err = none := by
      intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact h y hy
    obtain ⟨g1, g2, _⟩ := printMany_go (xs.map (·.2)) h'
    have hne' : xs.isEmpty = false := by cases xs <;> simp_all
    have : printToString xs = .ok (String.join (xs.map (fun x => evText x.2.evs))) := by
      simp [printToString, hne', printMany, g1, evText, g2, List.map_map, Function.comp_def]
    exact ⟨this, this⟩
  · intro h hne
    have h' : ∀ x ∈ ys.map (fun y => y.2 env), x.err = none := by
      intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact h y hy
    obtain ⟨g1, g2, _⟩ := printMany_go (ys.map (fun y => y.2 env)) h'
    have hne' : ys.isEmpty = false := by cases ys <;> simp_all
    simp [stringWithEnv, hne', printMany, g1, evText, g2, List.map_map, Function.comp_def]

/-- `print(io, s::AbstractString)` prints the characters one by one and
`write(io, s::AbstractString)` returns the number of bytes written; for `String`
and `SubString{String}`, `write` writes the whole string in one call and returns
`sizeof(s)`, and `print` writes the same text (`base/strings/io.jl:192-193, 242-246`). -/
def StringWrites : Prop :=
  ∀ (cs : List Char) (s : String),
    evText (printAbstractString cs) = String.join (cs.map String.singleton) ∧
    evText (writeAbstractString cs).1 = String.join (cs.map String.singleton) ∧
    (writeAbstractString cs).2 = (cs.map Char.utf8Size).sum ∧
    (writeString s).1 = [.write s] ∧ (writeString s).2 = s.utf8ByteSize ∧
    evText (printString s) = s ∧ showAbstractString s = s

theorem evText_singletons (cs : List Char) :
    evText (cs.map (fun c => Ev.write (String.singleton c))) = String.join (cs.map String.singleton) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [evText, ih, String.join_cons]

theorem stringWrites_proven : StringWrites := by
  intro cs s
  refine ⟨evText_singletons cs, evText_singletons cs, rfl, rfl, rfl, ?_, rfl⟩
  simp [printString, writeString, evText]

/-! ## `join` -/

theorem intersperse_cons (d x : String) (xs : List String) :
    List.intersperse d (x :: xs) = x :: xs.flatMap (fun y => [d, y]) := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => simp [List.intersperse, ih]

theorem join2_go_false (d : String) (xs : List String) :
    join2.go d false xs = xs.flatMap (fun y => [d, y]) := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [join2.go, ih]

theorem joinLast_go_false (d l p b : String) (ys : List String) :
    joinLast.go d l false (some p) (ys ++ [b]) = [d] ++ List.intersperse d (p :: ys) ++ [l, b] := by
  induction ys generalizing p with
  | nil => simp [joinLast.go]
  | cons y ys ih =>
    simp only [List.cons_append, joinLast.go, ih]
    simp [intersperse_cons]

theorem joinLast_go_true (d l p b : String) (ys : List String) :
    joinLast.go d l true (some p) (ys ++ [b]) = List.intersperse d (p :: ys) ++ [l, b] := by
  cases ys with
  | nil => simp [joinLast.go]
  | cons y ys =>
    simp only [List.cons_append, joinLast.go, joinLast_go_false]
    simp [intersperse_cons]

/-- `join(io, iterator, delim, last)` prints the items with `delim` between
adjacent items and `last` between the last two, and `join(io, iterator, delim)`
puts `delim` between all adjacent items (`base/strings/io.jl:311-354`);
`_join_preserve_annotations` returns a plain `String` for concrete
unannotated element types and for tuples without annotated parts
(`base/strings/io.jl:356-387`). -/
def JoinSpec : Prop :=
  ∀ (xs : List String) (a b d l : String) (j : JoinInfo),
    joinLast [] d l = [] ∧ joinLast [a] d l = [a] ∧
    joinLast (xs ++ [a, b]) d l = List.intersperse d (xs ++ [a]) ++ [l, b] ∧
    join2 xs d = List.intersperse d xs ∧
    joinText xs (some d) none = String.join (List.intersperse d xs) ∧
    joinText xs none none = String.join xs ∧
    (j.concrete = true → j.eltAnnotated = false → j.argsAnnotated = false → joinKindGeneric j = .plain) ∧
    (j.eltAnnotated = false → j.argsAnnotated = false → joinKindTuple j = .plain) ∧
    (j.eltAnnotated = true → joinKindTuple j = .annotated)

theorem join2_spec (xs : List String) (d : String) : join2 xs d = List.intersperse d xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [join2, join2.go, join2_go_false, intersperse_cons]

theorem joinSpec_proven : JoinSpec := by
  intro xs a b d l j
  refine ⟨rfl, rfl, ?_, join2_spec xs d, ?_, ?_, ?_, ?_, ?_⟩
  · cases xs with
    | nil => simp [joinLast, joinLast.go]
    | cons x xs =>
      simp only [joinLast, List.cons_append, joinLast.go]
      have := joinLast_go_true d l x b (xs ++ [a])
      simpa using this
  · simp [joinText, join2_spec]
  · simp [joinText, join2_spec]
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y ys => simp [List.intersperse, String.join_cons] at ih ⊢; rw [← ih]
  · intro h1 h2 h3; simp [joinKindGeneric, h1, h2, h3]
  · intro h1 h2; simp [joinKindTuple, h1, h2]
  · intro h1; simp [joinKindTuple, h1]

/-! ## `escape_raw_string` -/

theorem escRaw_count (delim : Char) (cs : List Char) (e t : Nat) :
    (escRaw delim cs e t).1.length + t = cs.length + (escRaw delim cs e t).2 ∧ t ≤ (escRaw delim cs e t).2 := by
  induction cs generalizing e t with
  | nil => simp [escRaw]; omega
  | cons c cs ih =>
    simp only [escRaw]
    split
    · have := ih (e + 1) t; simp; omega
    · split
      · have := ih 0 (t + (e + 1)); simp; omega
      · have := ih 0 t; simp; omega

theorem escRaw_backslashes (delim : Char) (hd : delim ≠ '\\') (n : Nat) (rest : List Char) (e t : Nat) :
    escRaw delim (List.replicate n '\\' ++ rest) e t =
      (List.replicate n '\\' ++ (escRaw delim rest (e + n) t).1, (escRaw delim rest (e + n) t).2) := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, escRaw, if_true]
    rw [ih (e + 1)]
    simp [Nat.add_assoc, Nat.add_comm 1 n]

/-- `escape_raw_string(s, delim)` raises the `n` backslashes before each
delimiter to `2n+1` and doubles trailing backslashes; the returned count is
the number of backslashes added, so the escaped text is that much longer, and a
string that needs no change is returned as is (`base/strings/io.jl:645-697`);
`@raw_str` returns its text unchanged (`base/strings/io.jl:643`). -/
def EscapeRawSpec : Prop :=
  ∀ (delim : Char) (s : List Char) (n : Nat) (c : Char),
    (escapeRawStringIO s delim).1.length = s.length + (escapeRawStringIO s delim).2 ∧
    ((escapeRawStringIO s delim).2 = 0 → escapeRawString s delim = s) ∧
    (delim ≠ '\\' → escapeRawString (List.replicate n '\\' ++ [delim]) delim =
      List.replicate (2 * n + 1) '\\' ++ [delim]) ∧
    (delim ≠ '\\' → c ≠ '\\' → c ≠ delim → escapeRawString (c :: List.replicate n '\\') delim =
      c :: List.replicate (2 * n) '\\') ∧
    rawStr s = s

theorem escRaw_trailing (delim : Char) (hd : delim ≠ '\\') (n : Nat) :
    escRaw delim (List.replicate n '\\') 0 0 = (List.replicate (2 * n) '\\', n) := by
  have h1 := escRaw_backslashes delim hd n [] 0 0
  rw [List.append_nil] at h1
  rw [h1]; simp only [escRaw, Nat.zero_add]
  rw [List.replicate_append_replicate, Nat.two_mul]

theorem escapeRawSpec_proven : EscapeRawSpec := by
  intro delim s n c
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · have := (escRaw_count delim s 0 0).1; simpa [escapeRawStringIO] using this
  · intro h; simp [escapeRawString, h]
  · intro hd
    have h1 := escRaw_backslashes delim hd n [delim] 0 0
    have h2 : escRaw delim [delim] (0 + n) 0 = (List.replicate (n + 1) '\\' ++ [delim], n + 1) := by
      have hd' : ¬ delim = '\\' := hd
      simp [escRaw, hd']
    simp only [escapeRawString, escapeRawStringIO, h1, h2]
    rw [if_neg (Nat.add_one_ne_zero n), ← List.append_assoc, List.replicate_append_replicate]
    congr 2; omega
  · intro hd hc hcd
    simp only [escapeRawString, escapeRawStringIO, escRaw, hc, hcd, if_false, escRaw_trailing delim hd n]
    by_cases hn : n = 0 <;> simp [hn]

/-! ## `indentation`, `unindent` -/

theorem indentation_spaces (tw k count : Nat) (c : Char) (rest : List Char) (h1 : c ≠ ' ') (h2 : c ≠ '\t') :
    indentation tw (List.replicate k ' ' ++ c :: rest) count = (count + k, false) := by
  induction k generalizing count with
  | zero => simp [indentation, h1, h2]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, indentation, if_true]
    rw [ih]; simp; omega

theorem indentation_blank (tw count : Nat) (s : List Char) (h : ∀ c ∈ s, c = ' ' ∨ c = '\t') :
    (indentation tw s count).2 = true := by
  induction s generalizing count with
  | nil => rfl
  | cons c cs ih =>
    rcases h c (by simp) with hc | hc
    · subst hc; simp only [indentation, if_true]; exact ih _ (fun x hx => h x (by simp [hx]))
    · subst hc; simp only [indentation]; simp; exact ih _ (fun x hx => h x (by simp [hx]))

theorem unindent_cut (i : Int) (tw : Nat) (k col : Nat) (c : Char) (rest : List Char)
    (h1 : c ≠ ' ') (h2 : c ≠ '\t') (h3 : c ≠ '\n') :
    unindentLoop i tw true col (List.replicate k ' ' ++ c :: rest) =
      spaces (col + k) i ++ c :: unindentLoop i tw false (col + k + 1) rest := by
  induction k generalizing col with
  | zero => simp [unindentLoop, h1, h2, h3]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, unindentLoop, if_true]
    rw [ih]; simp [Nat.add_assoc, Nat.add_comm 1 k]
    congr 1; omega

theorem unindent_plain (i : Int) (tw col : Nat) (rest : List Char) (h : ∀ x ∈ rest, x ≠ '\t' ∧ x ≠ '\n') :
    unindentLoop i tw false col rest = rest := by
  induction rest generalizing col with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    simp only [unindentLoop, hx.1, hx.2, if_false]
    rw [ih _ (fun y hy => h y (by simp [hy]))]

/-- `indentation(str)` returns the width of the leading blanks and whether the
string has nothing else; `unindent(str, 0)` is `str`, and on a line of `k`
leading spaces followed by text without tabs or newlines, `unindent(str, i)`
keeps `k - i` of the spaces and the rest (`base/strings/io.jl:699-803`). -/
def IndentSpec : Prop :=
  ∀ (tw : Nat) (s : List Char) (k i : Nat) (c : Char) (rest : List Char),
    unindent s 0 tw = s ∧
    (c ≠ ' ' → c ≠ '\t' → indentation tw (List.replicate k ' ' ++ c :: rest) 0 = (k, false)) ∧
    ((∀ x ∈ s, x = ' ' ∨ x = '\t') → (indentation tw s 0).2 = true) ∧
    (0 < i → c ≠ ' ' → c ≠ '\t' → c ≠ '\n' → (∀ x ∈ rest, x ≠ '\t' ∧ x ≠ '\n') →
      unindent (List.replicate k ' ' ++ c :: rest) i tw = List.replicate (k - i) ' ' ++ c :: rest)

theorem indentSpec_proven : IndentSpec := by
  intro tw s k i c rest
  refine ⟨by simp [unindent], ?_, indentation_blank tw 0 s, ?_⟩
  · intro h1 h2; rw [indentation_spaces tw k 0 c rest h1 h2]; simp
  · intro hi h1 h2 h3 hr
    have hne : (i : Int) ≠ 0 := by omega
    simp only [unindent, hne, if_false]
    rw [unindent_cut i tw k 0 c rest h1 h2 h3, unindent_plain i tw _ rest hr]
    simp only [spaces, Nat.zero_add]
    congr 2
    omega

/-! ## Strings from characters -/

theorem annotated_regions (cs : List AChar) (point : Nat) (hp : 1 ≤ point) :
    ∀ r ∈ annotatedStringOfChars.go point cs, r.1.1 = r.1.2 ∧ 1 ≤ r.1.1 := by
  induction cs generalizing point with
  | nil => simp [annotatedStringOfChars.go]
  | cons c cs ih =>
    intro r hr
    simp only [annotatedStringOfChars.go, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨a, _, rfl⟩ | hr
    · exact ⟨rfl, hp⟩
    · exact ih (point + c.char.utf8Size) (by omega) r hr

/-- `String(a::AbstractVector{Char})` is the characters in order with
`sum(ncodeunits)` bytes; `String(chars::AbstractVector{<:AbstractChar})` prints
each character; `AnnotatedString(chars)` has the characters as text and one
single-position region per annotation, at the annotated character's first
byte (`base/strings/io.jl:805-847`). -/
def CharsToString : Prop :=
  ∀ {C : Type} (a : List Char) (pr : C → List Char) (chars : List C) (cs : List AChar),
    (stringOfChars a).1 = a ∧ (stringOfChars a).2 = (a.map Char.utf8Size).sum ∧
    stringOfAbstractChars pr chars = chars.flatMap pr ∧
    (annotatedStringOfChars cs).1 = cs.map (·.char) ∧
    (∀ r ∈ (annotatedStringOfChars cs).2, r.1.1 = r.1.2 ∧ 1 ≤ r.1.1)

theorem charsToString_proven : CharsToString := by
  intro C a pr chars cs
  exact ⟨rfl, rfl, rfl, rfl, annotated_regions cs 1 (Nat.le_refl 1)⟩

/-! ## Limited string display -/

/-- `show(io, MIME"text/plain", str; limit)` prints `str` in full unless a
limit applies, and elides only when the replacement `" ⋯ n bytes ⋯ "` is no
longer than the `n` code units it replaces (`base/strings/io.jl:196-236`). -/
def ShowLimitedSpec : Prop :=
  ∀ (x : LimitIn) (limit : Option Int) (h : Nat) (r : String) (t : Nat),
    (x.ioLimit = false → showLimited x none = .full) ∧
    (showLimited x limit = .elided h r t →
      (r.utf8ByteSize : Int) ≤ elidedCount x h t ∧ r = skipText (limitedUnits x) (elidedCount x h t))

theorem limitedElide_elided (x : LimitIn) (hd tl h : Nat) (r : String) (t : Nat) :
    limitedElide x hd tl = .elided h r t →
      (r.utf8ByteSize : Int) ≤ elidedCount x h t ∧ r = skipText (limitedUnits x) (elidedCount x h t) := by
  unfold limitedElide
  split
  · rename_i hc
    intro he
    obtain ⟨rfl, rfl, rfl⟩ := LimitOut.elided.inj he
    exact ⟨by omega, rfl⟩
  · intro he; cases he

theorem limitedAt_elided (x : LimitIn) (l : Int) (h : Nat) (r : String) (t : Nat) :
    limitedAt x l = .elided h r t →
      (r.utf8ByteSize : Int) ≤ elidedCount x h t ∧ r = skipText (limitedUnits x) (elidedCount x h t) := by
  unfold limitedAt
  split
  · intro he; cases he
  · exact limitedElide_elided x _ _ h r t

theorem showLimitedSpec_proven : ShowLimitedSpec := by
  intro x limit h r t
  refine ⟨?_, ?_⟩
  · intro hl; simp [showLimited, effectiveLimit, hl]
  · intro he
    unfold showLimited at he
    cases hl : effectiveLimit x limit with
    | none => rw [hl] at he; cases he
    | some l => rw [hl] at he; exact limitedAt_elided x l h r t he

/-! ## Escaping helpers (models of `JuliaLean.Show`) -/

open JuliaLean.Show JuliaLean.Strings in
/-- `need_full_hex(c)` is `true` exactly for a following hex digit; `escape_nul(c)`
gives `"\\x00"` exactly before an octal digit (where `"\\0"` would be ambiguous)
and `"\\0"` otherwise; `print_quoted`/`show(io, ::AbstractString)` wrap
`escape_string(s, ('"', '$'))` in double quotes; `b"..."` of the escaped form of
any in-range string gives back its bytes (`base/strings/io.jl:194, 395-397,
491-495, 613-616`). -/
def EscapeHelpers : Prop :=
  ∀ (nxt : Option UInt32) (d : UData) (s : JStr),
    (needFullHex nxt = true ↔ ∃ c, nxt = some c ∧ isxdigit c = true) ∧
    (escapeNul nxt = asc ['\\', 'x', '0', '0'] ↔
      ∃ c, nxt = some c ∧ (decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x37)) = true) ∧
    printQuoted d s = [0x22] ++ escapeStringIO d s [ac 0x22, ac 0x24] [] false false ++ [0x22] ∧
    (s.bytes.length < 2 ^ 59 →
      (∀ c ∈ chars s, ¬ (ismalformed c = false ∧ isoverlong c = false ∧ ∃ u, codepoint c = .ok u ∧ u > 0x10ffff)) →
      ∃ r, escapeString d s = .ok r ∧ bStr r = .ok s.bytes)

open JuliaLean.Show JuliaLean.Strings in
theorem escapeHelpers_proven : EscapeHelpers := by
  intro nxt d s
  refine ⟨?_, ?_, rfl, ?_⟩
  · cases nxt <;> simp [needFullHex]
  · cases nxt with
    | none => simp [escapeNul, asc]
    | some c =>
      simp only [escapeNul]
      split
      · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; simp [h]
      · rename_i h
        simp only [Option.some.injEq, exists_eq_left']
        constructor
        · intro he; simp [asc] at he
        · intro he; exact absurd he h
  · intro hl hc
    obtain ⟨r, t, h1, h2, h3⟩ := escapeRoundTripInRange_proven d s hl hc
    exact ⟨r, h1, by simp only [bStr, h2]; exact congrArg Except.ok h3⟩

end JuliaLean.ShowCov
