import JuliaLean.DocsSyntaxCov.Parse

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
        if (c : Int) - 48 < base then JInt.convert t ((c : Int) - 48) else .error (.argumentError "invalid base digit")) ∧
      (65 ≤ c ∧ c ≤ 90 → parseChar t c base =
        if (c : Int) - 55 < base then JInt.convert t ((c : Int) - 55) else .error (.argumentError "invalid base digit")) ∧
      (97 ≤ c ∧ c ≤ 122 → parseChar t c base =
        let d : Int := (c : Int) - 97 + (if base ≤ 36 then 10 else 36)
        if d < base then JInt.convert t d else .error (.argumentError "invalid base digit")))

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
  · intro a b; simp [tryparseInternalRealRaise]; rfl
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
