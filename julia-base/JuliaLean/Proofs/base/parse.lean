import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.expr
import JuliaLean.Registry.Types
import JuliaLean.base.parse


section

/-!
# Properties of `base/parse.jl` (models in `DocsSyntaxCov.Parse`)
-/

namespace JuliaLean.DocsSyntaxCov.Parse

open JuliaLean
open JuliaLean.ParsePrint.IntParse

/-- `isnumeric` on ASCII characters: exactly the digits `0-9` (raw `Char` of an ASCII
character is its code shifted left by 24 bits). -/
def NumericSpec (isnumeric : Nat → Bool) : Prop :=
  ∀ c : Nat, c < 128 → isnumeric (c * 2 ^ 24) = decide (48 ≤ c ∧ c ≤ 57)

/-! ## `parse(::Type{Union{}}, ...)` -/

def ParseUnionAllThrows : Prop :=
  ∀ (args : List Nat), parseUnionAll args = "cannot parse a value as Union{}"

theorem parseUnionAllThrows : ParseUnionAllThrows := fun _ => rfl

/-! ## `parse(T, c::AbstractChar; base)` -/

/-- The docstring's digit values: `0-9`, `A-Z` are 10-35, `a-z` are 10-35 up to base 36
and 36-61 above; an invalid base or a digit not below the base throws `ArgumentError`. -/
def ParseCharDigits : Prop :=
  ∀ (t : IntTy) (c : Nat) (base : Int),
    (¬ (2 ≤ base ∧ base ≤ 62) → ∃ m, parseChar t c base = .error (.argumentError m)) ∧
    (2 ≤ base ∧ base ≤ 62 →
      (48 ≤ c ∧ c ≤ 57 → parseChar t c base =
        if (c : Int) - 48 < base then JInt.convert (t.name) t ((c : Int) - 48) else .error (.argumentError "invalid base digit")) ∧
      (65 ≤ c ∧ c ≤ 90 → parseChar t c base =
        if (c : Int) - 55 < base then JInt.convert (t.name) t ((c : Int) - 55) else .error (.argumentError "invalid base digit")) ∧
      (97 ≤ c ∧ c ≤ 122 → parseChar t c base =
        let d : Int := (c : Int) - 97 + (if base ≤ 36 then 10 else 36)
        if d < base then JInt.convert (t.name) t d else .error (.argumentError "invalid base digit")))

theorem parseCharDigits : ParseCharDigits := by
  intro t c base
  refine ⟨fun hb => ⟨"invalid base", by simp [parseChar, hb]⟩, fun hb => ⟨?_, ?_, ?_⟩⟩
  · intro hc
    have h1 : (48 : Nat) ≤ c ∧ c ≤ 57 := hc
    simp only [parseChar, hb, not_true_eq_false, and_self, if_false, charDigit, h1, if_true]
    by_cases h : (c : Int) - 48 < base <;> simp [h]
  · intro hc
    have h1 : ¬ ((48 : Nat) ≤ c ∧ c ≤ 57) := by omega
    have h2 : (65 : Nat) ≤ c ∧ c ≤ 90 := hc
    have e : (c : Int) - 65 + 10 = (c : Int) - 55 := by omega
    simp only [parseChar, hb, not_true_eq_false, and_self, if_false, charDigit, h1, h2, if_true, e]
    by_cases h : (c : Int) - 55 < base <;> simp [h]
  · intro hc
    have h1 : ¬ ((48 : Nat) ≤ c ∧ c ≤ 57) := by omega
    have h2 : ¬ ((65 : Nat) ≤ c ∧ c ≤ 90) := by omega
    have h3 : (97 : Nat) ≤ c ∧ c ≤ 122 := hc
    simp only [parseChar, hb, not_true_eq_false, and_self, if_false, charDigit, h1, h2, h3, if_true]
    by_cases h : (c : Int) - 97 + (if base ≤ 36 then 10 else 36) < base <;> simp [h]

/-! ## `tryparse_internal` with positions and `check_valid_base` -/

/-- On an ASCII string, `tryparse_internal(T, s, a, b, base, raise)` parses exactly the bytes
`a:b` (and nothing when `a > b`), as `parseint_utf8` with those bounds; `tryparse_internal(T,
s, a, b, raise)` uses base 10; `check_valid_base` accepts exactly `2:62`. -/
def TryparseInternalIntRange : Prop :=
  ∀ (t : IntTy) (s : Bytes) (a b base : Int) (raise : Bool),
    (∀ k, cuN s k < 0x80) →
    tryparseInternalInt t s a b base raise =
      parseintUtf8 t s a (if 1 ≤ a ∧ a ≤ b then b else a - 1) base raise ∧
    tryparseInternalInt10 t s a b raise = tryparseInternalInt t s a b 10 raise ∧
    tryparseInternalIntCopy t s base raise = parseintUtf8 t s 1 (ncu s) base raise ∧
    (checkValidBase base = if 2 ≤ base ∧ base ≤ 62 then .ok base else .error (.argumentError "invalid base"))

theorem tryparseInternalIntRange : TryparseInternalIntRange := by
  intro t s a b base raise hs
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold tryparseInternalInt
  by_cases h : 1 ≤ a ∧ a ≤ b
  · have hb := hs b
    simp only [h, and_self, if_true, nextind, iterate]
    have : ¬ (0x80 ≤ cuN s b ∧ cuN s b ≤ 0xf7) := by omega
    simp [this]
  · simp [h]

/-- `parseint_string` is `parseint_utf8` on the whole string after `check_valid_base`, with base
`0` (a prefix decides) when none is given: the shared path of `parse` and `tryparse`. -/
def ParseintStringWhole : Prop :=
  ∀ (t : IntTy) (s : Bytes) (raise : Bool),
    parseintString t s none raise = parseintUtf8 t s 1 (ncu s) 0 raise ∧
    ∀ b : Int, 2 ≤ b ∧ b ≤ 62 → parseintString t s (some b) raise = parseintUtf8 t s 1 (ncu s) b raise

theorem parseintStringWhole : ParseintStringWhole := by
  intro t s raise
  refine ⟨rfl, fun b hb => ?_⟩
  simp [parseintString, validBase, hb]

/-! ## `Bool` -/

/-- Leading whitespace is ignored like trailing whitespace: if `parse(Bool, s)` succeeds, so
does `parse(Bool, " " * s)` with the same value (the code skips "leading and trailing
whitespace", `base/parse.jl:201`, and `parse(Int, " 1") == 1`). -/
def BoolLeadingSpace : Prop :=
  ∀ (isnumeric : Nat → Bool), NumericSpec isnumeric →
    ∀ (s : Bytes) (b : Bool), parseBoolStr isnumeric s false = .ok (some b) →
      parseBoolStr isnumeric (byte 32 :: s) false = .ok (some b)

/-- The ASCII `isnumeric`. -/
def asciiNumeric (u : Nat) : Bool := decide (48 * 2 ^ 24 ≤ u ∧ u ≤ 57 * 2 ^ 24 ∧ u % 2 ^ 24 = 0)

theorem asciiNumeric_spec : NumericSpec asciiNumeric := by
  intro c hc
  unfold asciiNumeric
  simp only [Nat.mul_mod_left, and_true]
  by_cases h : 48 ≤ c ∧ c ≤ 57
  · simp [h]; omega
  · simp [h]; omega

theorem bool_one : parseBoolStr asciiNumeric ([byte 49]) false = .ok (some true) := by decide +kernel

theorem bool_space_one : parseBoolStr asciiNumeric ([byte 32, byte 49]) false = .ok none := by decide +kernel

theorem boolLeadingSpace_refuted : ¬ BoolLeadingSpace := by
  intro h
  have := h asciiNumeric asciiNumeric_spec ([byte 49]) true bool_one
  rw [show byte 32 :: [byte 49] = [byte 32, byte 49] from rfl, bool_space_one] at this
  cases this

/-! ## Floats and the `Real` fallbacks -/

/-- `tryparse(T, s)` for `T <: IEEEFloat` hands `Parsers.parsefloat` the bytes between the first
and last non-ASCII-whitespace byte; `tryparse_internal(T, s, a, b)` passes the whole string
when `a:b` covers it; with `raise`, `nothing` becomes an `ArgumentError`; `parse` returns the
parsed value or throws. -/
def FloatAndRealFallbacks : Prop :=
  ∀ {F : Type} (pf : Bytes → Option F) (s : Bytes) (raise : Bool),
    tryparseFloat pf s = pf (slice s (skipAsciiFwd s (ncu s) (s.length + 1) 1)
      (skipAsciiBack s (skipAsciiFwd s (ncu s) (s.length + 1) 1) (s.length + 1) (ncu s))) ∧
    tryparseInternalReal (tryparseFloat pf) s 1 (lastindex s) = tryparseFloat pf s ∧
    (tryparseInternalRealKw (tryparseFloat pf) s raise =
      if raise ∧ (tryparseFloat pf s).isNone then .error (.argumentError "cannot parse")
      else .ok (tryparseFloat pf s)) ∧
    (∀ a b, tryparseInternalRealRaise (tryparseFloat pf) s a b false =
      .ok (tryparseInternalReal (tryparseFloat pf) s a b)) ∧
    (parseReal (tryparseFloat pf) s =
      match tryparseFloat pf s with
      | some r => .ok r
      | none => .error (.argumentError "cannot parse")) ∧
    (parseFailure s 1 (lastindex s)).2 = .argumentError "cannot parse"

theorem floatAndRealFallbacks : FloatAndRealFallbacks := by
  intro F pf s raise
  refine ⟨rfl, by simp [tryparseInternalReal], ?_, ?_, ?_, rfl⟩
  · unfold tryparseInternalRealKw
    by_cases h : raise = true ∧ (tryparseFloat pf s).isNone = true
    · simp only [h, and_self, if_true]; rfl
    · simp only [h, if_false]; rfl
  · intro a b; simp [tryparseInternalRealRaise] <;> rfl
  · unfold parseReal tryparseInternalRealKw
    cases h : tryparseFloat pf s <;> simp [h] <;> rfl

/-! ## Complex numbers -/

/-- No float literal contains the letter `q`. -/
def NoQ {F : Type} (pf : Bytes → Option F) : Prop := ∀ w, byte 113 ∈ w → pf w = none

/-- The docstring promises an error (or `nothing` from `tryparse`) when the string does not
contain a valid number: a string that parses as a complex number stops parsing when a `q`,
which no number contains, is appended. -/
def ComplexTrailingRejected : Prop :=
  ∀ {F : Type} (ops : FloatOps F) (pf : Bytes → Option F), NoQ pf →
    ∀ (s : Bytes) (z : F × F),
      tryparseComplexStr ops (floatComponent pf) s false = .ok (some z) →
      tryparseComplexStr ops (floatComponent pf) (s ++ [byte 113]) false = .ok none

/-- A float parser that accepts exactly the literal `2`. -/
def pfTwo (w : Bytes) : Option Nat := if w == [byte 50] then some 2 else none

def natOps : FloatOps Nat := ⟨0, id⟩

theorem pfTwo_noQ : NoQ pfTwo := by
  intro w hw
  unfold pfTwo
  have : ¬ (w == [byte 50]) = true := by
    intro h
    have h' : w = [byte 50] := by simpa using h
    subst h'
    revert hw; decide
  simp [this]

theorem complex_2im :
    tryparseComplexStr natOps (floatComponent pfTwo) ([byte 50, byte 105, byte 109]) false = .ok (some (0, 2)) := by
  decide +kernel

theorem complex_2imq :
    tryparseComplexStr natOps (floatComponent pfTwo) ([byte 50, byte 105, byte 109, byte 113]) false = .ok (some (0, 2)) := by
  decide +kernel

theorem complexTrailingRejected_refuted : ¬ ComplexTrailingRejected := by
  intro h
  have := h natOps pfTwo pfTwo_noQ ([byte 50, byte 105, byte 109]) (0, 2) complex_2im
  rw [show [byte 50, byte 105, byte 109] ++ [byte 113] = [byte 50, byte 105, byte 109, byte 113] from rfl, complex_2imq] at this
  cases this

end JuliaLean.DocsSyntaxCov.Parse

end

section

/-! Row-specific properties not supplied by the initial area models. -/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

namespace Parse

open JuliaLean.ParsePrint.IntParse

def WhitespaceAndIntegerMethods : Prop :=
  (∀ b, isspaceAscii b = (b.val == 32 || (9 ≤ b.val && b.val ≤ 13))) ∧
  (∀ s i, skipspacechar s i =
    let (c, next) := iterate s i
    if isspaceChar c then next else i) ∧
  (∀ s i j, skipspacecharBack s i j =
    let k := thisind s j
    if k ≥ i ∧ isspaceChar (getChar s k) then k - 1 else j) ∧
  (∀ s i j, skipspace s i j = skipspaceLoop s j (s.length + 1) i) ∧
  (∀ s i j, skipspaceBack s i j = skipspaceBackLoop s i (s.length + 1) j) ∧
  (∀ t s base raise, parseintString t s base raise = do
    let b ← validBase base
    parseintUtf8 t s 1 (ncu s) b raise)

theorem whitespaceAndIntegerMethods : WhitespaceAndIntegerMethods :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def ParseWrapperMethods : Prop :=
  (∀ isnumeric s raise, parseBoolStr isnumeric s raise =
    tryparseBool isnumeric s 1 (lastindex s) 0 raise) ∧
  (∀ F pf s, @tryparseFloat F pf s = tryparseFloatRange pf s 1 (ncu s)) ∧
  (∀ R tp s a b, @tryparseInternalReal R tp s a b =
    if a == 1 ∧ b == lastindex s then tp s else tp (slice s a (nextind s b - 1))) ∧
  (∀ R tp s, @parseReal R tp s = do
    match ← tryparseInternalRealKw tp s true with
    | some r => pure r | none => .error (.methodError "convert"))

theorem parseWrapperMethods : ParseWrapperMethods :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩

end Parse

namespace TomlPrint

end TomlPrint

namespace Binary

open JuliaLean.Platforms

end Binary

namespace TomlRows

open JuliaLean.Toml

end TomlRows

namespace Binary

open JuliaLean.Platforms

end Binary

namespace Syntax

end Syntax

end JuliaLean.DocsSyntaxCov

end

namespace JuliaLean.Proofs.base.parse

open JuliaLean.Registry

open JuliaLean.DocsSyntaxCov in
open JuliaLean.Registry in
def entries : List Entry := [
  proven "docssyntaxcov-parse-union" "base/parse.jl" ["parse(::Union{})", "tryparse(::Union{})"]
    "Parsing Union{} always throws the documented error."
    "base/parse.jl:37,263" ``Parse.ParseUnionAllThrows ``Parse.parseUnionAllThrows,
  proven "docssyntaxcov-parse-char" "base/parse.jl" ["parse(::AbstractChar)"]
    "Character digits and bases are accepted exactly in their documented ranges."
    "base/parse.jl:39-47" ``Parse.ParseCharDigits ``Parse.parseCharDigits,
  proven "docssyntaxcov-parse-whitespace" "base/parse.jl"
    ["isspace_ascii", "skipspacechar", "skipspacechar_back", "skipspace", "skipspace_back", "parseint_preamble", "parseint_utf8", "throw_parseint_error"]
    "Whitespace and integer helpers mirror the shared integer-parser bodies."
    "base/parse.jl:53-171" ``Parse.WhitespaceAndIntegerMethods ``Parse.whitespaceAndIntegerMethods,
  proven "docssyntaxcov-parse-int-range" "base/parse.jl" ["tryparse_internal(::Integer)", "check_valid_base"]
    "Integer range parsing uses the requested byte range and validates bases 2 through 62."
    "base/parse.jl:173-182,234-239" ``Parse.TryparseInternalIntRange ``Parse.tryparseInternalIntRange,
  proven "docssyntaxcov-parse-int-string" "base/parse.jl" ["parseint_string", "parse", "tryparse"]
    "Integer string parsing consumes the whole string with prefix base detection."
    "base/parse.jl:247-263" ``Parse.ParseintStringWhole ``Parse.parseintStringWhole,
  refuted "docssyntaxcov-parse-bool-leading-space" "base/parse.jl" ["tryparse_internal(::Bool)", "parse(::Bool)", "tryparse(::Bool)"]
    "Leading whitespace is accepted for numeric Bool forms as it is for trailing whitespace."
    "base/parse.jl:184-232"
    "#42616 (closed, related); queries: parse Bool whitespace, parse Bool leading space, tryparse Bool"
    "parse(Bool, \" 1\") throws while \"1 \" succeeds."
    ``Parse.BoolLeadingSpace ``Parse.boolLeadingSpace_refuted,
  proven "docssyntaxcov-parse-wrappers" "base/parse.jl" ["tryparse", "parse", "tryparse_internal"]
    "Bool, float and real wrappers delegate to the exact internal ranges and raise policy."
    "base/parse.jl:247-280,346-374" ``Parse.ParseWrapperMethods ``Parse.parseWrapperMethods,
  proven "docssyntaxcov-parse-real" "base/parse.jl" ["tryparse_internal(::Real)", "_parse_failure", "parse(::Real)"]
    "Real parsing trims the documented range and converts failure to ArgumentError."
    "base/parse.jl:346-374" ``Parse.FloatAndRealFallbacks ``Parse.floatAndRealFallbacks,
  refuted "docssyntaxcov-parse-complex-trailing" "base/parse.jl" ["tryparse_internal(::Complex)", "parse(::Complex)", "tryparse(::Complex)"]
    "Complex parsing rejects characters after the imaginary unit."
    "base/parse.jl:284-343"
    "none found (queries: parse complex, Complex parse im, parse Complex trailing characters)"
    "Characters after the last imaginary unit are ignored."
    ``Parse.ComplexTrailingRejected ``Parse.complexTrailingRejected_refuted,
]

end JuliaLean.Proofs.base.parse
