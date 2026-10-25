import JuliaLean.Core
import JuliaLean.Strings.Ops

/-!
# Unicode character functions, `base/strings/unicode.jl`

Models of the `Char` predicates and case mappings of `base/strings/unicode.jl`
and of the keyword handling of `normalize` (master `bbfa0ce4150`). A `Char` is
its 32-bit bit pattern (`JuliaLean.Strings`): `'a'` is `0x61000000`.

utf8proc is a primitive (`Utf8proc`): each field is one C function or table
lookup, used only through the documented behaviour stated where a property
needs it.
-/

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-- Exceptions of the modelled Unicode functions: those of the shared String/Char
model (`InvalidCharError`, `CodePointError`, `BoundsError`, ...), the
`ErrorException` of `utf8proc_error` (`base/strings/unicode.jl:153`), the
`TypeError` of a failed `::T` assertion, and `fuel`, the value of a loop whose
iteration bound ran out (the proofs show the bounds are never reached). -/
inductive UErr where
  | str (e : SErr)
  | errorException
  | typeError
  | fuel
  deriving Repr, DecidableEq, Inhabited

abbrev UJl (α : Type) := Except UErr α

/-- Lift a String-model result. -/
def liftS {α : Type} : SJl α → UJl α
  | .ok a => .ok a
  | .error e => .error (.str e)

/-- `true` when a call returns. -/
def okB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- The utf8proc entry points Julia calls. -/
structure Utf8proc where
  /-- `utf8proc_toupper(c::UInt32)::UInt32` -/
  toupper : UInt32 → UInt32
  /-- `utf8proc_tolower(c::UInt32)::UInt32` -/
  tolower : UInt32 → UInt32
  /-- `utf8proc_totitle(c::UInt32)::UInt32` -/
  totitle : UInt32 → UInt32
  /-- `utf8proc_category(c::UInt32)::Cint`, a code in `0:29`. -/
  category : UInt32 → Nat
  /-- `utf8proc_grapheme_break_stateful(c1::UInt32, c2::UInt32, state::Ref{Int32})::Bool`:
  the result and the new value of `state[]`. -/
  gbStateful : Int32 → UInt32 → UInt32 → Bool × Int32
  /-- `utf8proc_decompose_char(uc, dst, bufsize, options, C_NULL)`: the code points of
  the decomposition of `uc` under `options` (`.ok`), or the negative error code it
  returns. It stores the first `min(length, bufsize)` of them at `dst` and returns the
  full length. -/
  decomposeChar : UInt32 → Nat → Except Int (List UInt32)
  /-- `utf8proc_get_property(uc).combining_class` (the `UInt16` that
  `combining_class` loads, `stdlib/Unicode/src/Unicode.jl:228`). -/
  combiningClass : UInt32 → UInt16

/-! ## Option bits, `base/strings/unicode.jl:136-149` -/

def STABLE : Nat := 1 <<< 1
def COMPAT : Nat := 1 <<< 2
def COMPOSE : Nat := 1 <<< 3
def DECOMPOSE : Nat := 1 <<< 4
def IGNORE : Nat := 1 <<< 5
def REJECTNA : Nat := 1 <<< 6
def NLF2LS : Nat := 1 <<< 7
def NLF2PS : Nat := 1 <<< 8
def NLF2LF : Nat := NLF2LS ||| NLF2PS
def STRIPCC : Nat := 1 <<< 9
def CASEFOLD : Nat := 1 <<< 10
def LUMP : Nat := 1 <<< 12
def STRIPMARK : Nat := 1 <<< 13

/-! ## Character functions -/

/-- `'a' <= c <= 'z'` on bit patterns (`isless(x::Char, y::Char)`, `base/char.jl:264`). -/
abbrev inRange (lo hi c : UInt32) : Bool := decide (lo ≤ c) && decide (c ≤ hi)

/-- The non-ASCII branch of the case mappings: `T(@ccall f(c::UInt32)::UInt32)`. The
argument conversion `UInt32(c)` throws `InvalidCharError` for a malformed `c`;
`Char(::UInt32)` throws `CodePointError` above `0x1fffff`. -/
def viaUtf8proc (f : UInt32 → UInt32) (c : UInt32) : UJl UInt32 := do
  let u ← liftS (codepoint c)
  liftS (charOfU32 (f u))

/-- `lowercase(c::T)`, `base/strings/unicode.jl:318-319`. For an ASCII `c`,
`c + 0x20` is `bitcast(Char, (z % UInt32) << 24)` with `z` the code point plus 32
(`+%`, `base/char.jl:285-294`), i.e. the bit pattern plus `0x20000000`. -/
def lowercaseChar (P : Utf8proc) (c : UInt32) : UJl UInt32 :=
  if isasciiChar c then .ok (if inRange 0x41000000 0x5a000000 c then c + 0x20000000 else c)
  else viaUtf8proc P.tolower c

/-- `uppercase(c::T)`, `base/strings/unicode.jl:339-340`. -/
def uppercaseChar (P : Utf8proc) (c : UInt32) : UJl UInt32 :=
  if isasciiChar c then .ok (if inRange 0x61000000 0x7a000000 c then c - 0x20000000 else c)
  else viaUtf8proc P.toupper c

/-- `titlecase(c::T)`, `base/strings/unicode.jl:364-365`. -/
def titlecaseChar (P : Utf8proc) (c : UInt32) : UJl UInt32 :=
  if isasciiChar c then .ok (if inRange 0x61000000 0x7a000000 c then c - 0x20000000 else c)
  else viaUtf8proc P.totitle c

/-- `unsafe_codepoint(c::Char)`, `base/char.jl:183-191`: `UInt32(c)` without the
malformation check. -/
def unsafeCodepoint (c : UInt32) : UInt32 :=
  let u := c
  if u < 0x80000000 then u >>> 24
  else
    let l1 := clo32 u
    let t0 := land56 (ctz32 u)
    let u := u &&& ushr32 0xffffffff l1
    let u := ushr32 u t0
    ((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
      ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6)

/-- `category_code(c::AbstractChar)` and `category_code(x::Integer)`,
`base/strings/unicode.jl:372-381`. -/
def categoryCode (P : Utf8proc) (c : UInt32) : Nat :=
  if !ismalformed c then
    let x := unsafeCodepoint c
    if x ≤ 0x10ffff then P.category x else 30
  else 31

/-- `isletter(c) = UTF8PROC_CATEGORY_LU <= category_code(c) <= UTF8PROC_CATEGORY_LO`
(`LU = 1`, `LO = 5`), `base/strings/unicode.jl:522`. -/
def isletterChar (P : Utf8proc) (c : UInt32) : Bool :=
  decide (1 ≤ categoryCode P c) && decide (categoryCode P c ≤ 5)

/-- `iscntrl(c::AbstractChar) = c <= '\x1f' || '\x7f' <= c <= '\u9f'`,
`base/strings/unicode.jl:568`, with the bit-pattern comparison of `Char`:
`'\x1f'` is `0x1f000000`, `'\x7f'` is `0x7f000000`, `'\u9f'` is `0xc29f0000`. -/
def iscntrlChar (c : UInt32) : Bool :=
  decide (c ≤ 0x1f000000) || (decide (0x7f000000 ≤ c) && decide (c ≤ 0xc29f0000))

/-- `isvalid(::Type{T}, c::Integer) = isvalid(T, Unsigned(c))` and
`isvalid(::Type{<:AbstractChar}, c::Unsigned)`, `base/strings/unicode.jl:59-60`, for
`c::Int`: `Unsigned(x::Int64) = UInt64(x)` (`base/int.jl:1213`) throws
`InexactError` for a negative `x`. -/
def isvalidCharInt (x : JInt64) : Jl Bool := do
  let c ← JInt.convert .u64 x.val
  pure (decide (c.val ≤ 0xd7ff) || (decide (0xe000 ≤ c.val) && decide (c.val ≤ 0x10ffff)))

/-! ## String case mappings -/

/-- The loop of `map(f, s::AbstractString)`, `base/strings/basic.jl:657-671`: `f` is
applied to each character in iteration order; its results are stored with
`__unsafe_string!` (the character's bytes). -/
def mapCharsM (f : UInt32 → UJl UInt32) : List UInt32 → UJl (List UInt32)
  | [] => .ok []
  | c :: cs => do
    let c' ← f c
    let rest ← mapCharsM f cs
    pure (c' :: rest)

/-- `map(f, s::AbstractString)`, `base/strings/basic.jl:657-671`. -/
def mapStr (f : UInt32 → UJl UInt32) (s : JStr) : UJl JStr := do
  let cs ← mapCharsM f (chars s)
  liftS (stringOfChars cs)

/-- `uppercase(s::AbstractString) = map(uppercase, s)`, `base/strings/unicode.jl:676`. -/
def uppercaseStr (P : Utf8proc) (s : JStr) : UJl JStr := mapStr (uppercaseChar P) s

/-- `lowercase(s::AbstractString) = map(lowercase, s)`, `base/strings/unicode.jl:693`. -/
def lowercaseStr (P : Utf8proc) (s : JStr) : UJl JStr := mapStr (lowercaseChar P) s

/-! ## `normalize` keywords -/

/-- The Boolean keywords of `normalize(s; ...)`, `base/strings/unicode.jl:202-217`. -/
structure NormKw where
  stable : Bool := false
  compat : Bool := false
  compose : Bool := true
  decompose : Bool := false
  stripignore : Bool := false
  rejectna : Bool := false
  newline2ls : Bool := false
  newline2ps : Bool := false
  newline2lf : Bool := false
  stripcc : Bool := false
  casefold : Bool := false
  lump : Bool := false
  stripmark : Bool := false
  deriving Repr, DecidableEq

/-- `x | y` on the `Int` flags; all values are in `0:2^14-1`, where `Int` bitwise or
is `Nat.lor`. -/
abbrev orIf (b : Bool) (flags bit : Nat) : Nat := if b then flags ||| bit else flags

/-- `Bool` to `Int` in `newline2ls + newline2ps + newline2lf`. -/
abbrev b2n (b : Bool) : Nat := if b then 1 else 0

/-- The flag computation of `normalize(s; kw...)`, `base/strings/unicode.jl:218-240`:
the `flags` passed to `utf8proc_map`, or the `ArgumentError` thrown before the call. -/
def normalizeFlags (k : NormKw) : Jl Nat :=
  let flags := 0
  let flags := orIf k.stable flags STABLE
  let flags := orIf k.compat flags COMPAT
  let r : Jl Nat :=
    if k.decompose then .ok (flags ||| DECOMPOSE)
    else if k.compose then .ok (flags ||| COMPOSE)
    else if k.compat || k.stripmark then
      .error (.argumentError "compat=true or stripmark=true require compose=true or decompose=true")
    else .ok flags
  match r with
  | .error e => .error e
  | .ok flags =>
    let flags := orIf k.stripignore flags IGNORE
    let flags := orIf k.rejectna flags REJECTNA
    if b2n k.newline2ls + b2n k.newline2ps + b2n k.newline2lf > 1 then
      .error (.argumentError "only one newline conversion may be specified")
    else
      let flags := orIf k.newline2ls flags NLF2LS
      let flags := orIf k.newline2ps flags NLF2PS
      let flags := orIf k.newline2lf flags NLF2LF
      let flags := orIf k.stripcc flags STRIPCC
      let flags := orIf k.casefold flags CASEFOLD
      let flags := orIf k.lump flags LUMP
      .ok (orIf k.stripmark flags STRIPMARK)

/-- The documented meaning of the keywords (`Unicode.normalize` docstring,
`stdlib/Unicode/src/Unicode.jl:60-118`): each option contributes its bit;
`decompose=true` selects decomposition and ignores `compose`. -/
def docFlags (k : NormKw) : Nat :=
  (if k.stable then STABLE else 0) ||| (if k.compat then COMPAT else 0) |||
  (if k.decompose then DECOMPOSE else if k.compose then COMPOSE else 0) |||
  (if k.stripignore then IGNORE else 0) ||| (if k.rejectna then REJECTNA else 0) |||
  (if k.newline2ls then NLF2LS else 0) ||| (if k.newline2ps then NLF2PS else 0) |||
  (if k.newline2lf then NLF2LF else 0) ||| (if k.stripcc then STRIPCC else 0) |||
  (if k.casefold then CASEFOLD else 0) ||| (if k.lump then LUMP else 0) |||
  (if k.stripmark then STRIPMARK else 0)

/-- The documented rejections: `compat` or `stripmark` without composition or
decomposition, and more than one newline conversion. -/
def normRejects (k : NormKw) : Bool :=
  ((k.compat || k.stripmark) && !k.compose && !k.decompose) ||
    decide (b2n k.newline2ls + b2n k.newline2ps + b2n k.newline2lf > 1)

/-- Property: `normalize` throws `ArgumentError` before calling utf8proc exactly in the
documented cases, and otherwise passes exactly the documented flags. -/
def NormalizeOptions : Prop :=
  ∀ k : NormKw,
    (normRejects k = false ∧ normalizeFlags k = .ok (docFlags k)) ∨
    (normRejects k = true ∧ ∃ msg, normalizeFlags k = .error (.argumentError msg))

/-- The decision procedure behind `normalizeOptions_proven`. -/
def normCheck (k : NormKw) : Bool :=
  match normalizeFlags k with
  | .ok f => !normRejects k && f == docFlags k
  | .error (.argumentError _) => normRejects k
  | .error _ => false

theorem normCheck_all : ∀ a b c d e f g h i j l m n : Bool,
    normCheck ⟨a, b, c, d, e, f, g, h, i, j, l, m, n⟩ = true := by
  decide +kernel

theorem normalizeOptions_proven : NormalizeOptions := by
  intro k
  have hc : normCheck k = true := by
    cases k; exact normCheck_all _ _ _ _ _ _ _ _ _ _ _ _ _
  unfold normCheck at hc
  split at hc
  · rename_i f hf
    left
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    exact ⟨hc.1, by rw [hf, hc.2]⟩
  · rename_i msg hf
    exact .inr ⟨hc, msg, hf⟩
  · exact absurd hc (by simp)

/-! ## Refuted properties of the character functions -/

/-- Property (`iscntrl` docstring, `base/strings/unicode.jl:553-567`: control characters
are the non-printing characters of the Latin-1 subset): `iscntrl(c)` implies that `c`
is a valid character. -/
def IscntrlValid : Prop := ∀ c : UInt32, iscntrlChar c = true → isvalidChar c = true

/-- `'\x80'` (the lone byte `0x80`, bit pattern `0x80000000`) is malformed but lies
between `'\x7f'` and `'\u9f'` in the bit-pattern order. -/
theorem iscntrlValid_refuted : ¬ IscntrlValid := fun h =>
  absurd (h 0x80000000 (by decide)) (by decide)

/-- Property (`isvalid(T, value)` docstring, `base/strings/unicode.jl:33-55`: return
`true` if the value is valid for the type): `isvalid(Char, x)` returns a `Bool` for
every `x::Int`. -/
def IsvalidCharIntTotal : Prop := ∀ x : JInt64, ∃ b, isvalidCharInt x = .ok b

/-- `isvalid(Char, -1)` throws `InexactError` from `Unsigned(-1)`. -/
theorem isvalidCharIntTotal_refuted : ¬ IsvalidCharIntTotal := by
  intro h
  obtain ⟨b, hb⟩ := h (ix (-1))
  have e : isvalidCharInt (ix (-1)) = .error (.inexactError "UInt64") := rfl
  rw [e] at hb
  cases hb

/-- Documented behaviour of the utf8proc case mappings: a code point maps to a code
point. -/
def Utf8proc.CaseAxioms (P : Utf8proc) : Prop :=
  ∀ u : UInt32, u < 0x110000 →
    P.toupper u < 0x110000 ∧ P.tolower u < 0x110000 ∧ P.totitle u < 0x110000

/-- Property (`uppercase(s)`/`lowercase(s)` docstrings, `base/strings/unicode.jl:663-692`:
return `s` with all characters converted): neither throws for any `String`. -/
def CaseMapNoThrow : Prop :=
  ∀ P : Utf8proc, P.CaseAxioms → ∀ s : JStr,
    okB (uppercaseStr P s) = true ∧ okB (lowercaseStr P s) = true

/-- The identity case tables. -/
def idCase : Utf8proc where
  toupper := id
  tolower := id
  totitle := id
  category := fun _ => 0
  gbStateful := fun _ _ _ => (true, 0)
  decomposeChar := fun u _ => .ok [u]
  combiningClass := fun _ => 0

theorem idCase_axioms : idCase.CaseAxioms := fun _ h => ⟨h, h, h⟩

/-- `"a\xffb"`. -/
def strAffB : JStr := ⟨[0x61, 0xff, 0x62], by decide⟩

/-- `uppercase("a\xffb")` converts `'\xff'` with `UInt32(c)` in the `ccall`, which
throws `InvalidCharError`; `lowercase` likewise. -/
theorem caseMapNoThrow_refuted : ¬ CaseMapNoThrow := fun h =>
  absurd (h idCase idCase_axioms strAffB).1 (by decide)

theorem lowercase_affb_throws :
    lowercaseStr idCase strAffB = .error (.str (.invalidChar 0xff000000)) := by rfl

end JuliaLean.RegexUnicode.Uni
