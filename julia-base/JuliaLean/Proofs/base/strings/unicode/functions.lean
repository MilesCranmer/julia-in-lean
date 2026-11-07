import JuliaLean.base.strings.unicode

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
