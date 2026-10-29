import JuliaLean.base.rounding
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.Proofs.base.float
import JuliaLean.Promotion.IEEE
import JuliaLean.Registry.Types

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

/-!
# Properties of `base/rounding.jl`

Specifications of the methods modelled in `JuliaLean.base.rounding`, with their proofs and
refutations. Callees from `base/int.jl` and `base/float.jl` are instantiated with the
source-mirrored definitions in `JuliaLean.base.int` and `JuliaLean.base.float`, and generic
methods are also verified across arbitrary custom mode, keyword, input, and target types.
-/

namespace JuliaLean.Proofs.base.rounding

open JuliaLean JuliaLean.Promotion JuliaLean.base.rounding

/-! ## Independent arithmetic specifications -/

def SupportedMode (mode : RoundingMode) : Prop :=
  match mode.tag with
  | .Other _ => False
  | _ => True

/-- Exact rational-to-integer rounding for the seven Base rounding modes. -/
def exactRound (n : Int) (d : Nat) (mode : RoundingMode) : Int :=
  let denominator : Int := d
  let floor := n / denominator
  let remainder := n % denominator
  let twice := 2 * remainder
  if remainder = 0 then floor
  else
    match mode.tag with
    | .Down => floor
    | .Up => floor + 1
    | .ToZero => if n < 0 then floor + 1 else floor
    | .FromZero => if n < 0 then floor else floor + 1
    | .Nearest =>
      if twice < denominator then floor
      else if twice > denominator then floor + 1
      else if floor % 2 = 0 then floor else floor + 1
    | .NearestTiesAway =>
      if twice < denominator then floor
      else if twice > denominator then floor + 1
      else if n < 0 then floor else floor + 1
    | .NearestTiesUp => if twice < denominator then floor else floor + 1
    | .Other _ => floor

/-- Keyword options (`digits`, `sigdigits`, `base`) for `round`, `trunc`, `floor`, and `ceil`. -/
structure RoundKeywords where
  digits : Int := 0
  sigdigits : Option Nat := none
  base : Nat := 10
  deriving Repr, DecidableEq

/-- Exact rational rounding to `kw.digits` places (or `kw.sigdigits` significant digits when
`sigdigits = some s`) in base `kw.base`:
for non-negative effective digits `k`, rounds `n / d` to a multiple of `1 / base^k`;
for negative effective digits `-k`, rounds `n / d` to a multiple of `base^k`. -/
def exactRoundDigits (n : Int) (d : Nat) (mode : RoundingMode) (kw : RoundKeywords) : Int × Nat :=
  let effDigits : Int :=
    match kw.sigdigits with
    | some s => (s : Int) - 1
    | none => kw.digits
  let scale := kw.base ^ effDigits.natAbs
  if 0 ≤ effDigits then
    (exactRound (n * (scale : Int)) d mode, scale)
  else
    (exactRound n (d * scale) mode * (scale : Int), 1)

/-- The independent bit-level decision promised by `correct_rounding_requires_increment`. -/
def expectedIncrement (bits : RoundingBit → Bool) (mode : RoundingMode) (signBit : Bool) : Jl Bool :=
  match mode.tag with
  | .Nearest => .ok (bits .RoundBit && (bits .StickyBit || bits .FinalBit))
  | .NearestTiesUp => .ok (bits .RoundBit && (bits .StickyBit || !signBit))
  | .NearestTiesAway => .ok (bits .RoundBit)
  | .Up => .ok (!signBit && (bits .RoundBit || bits .StickyBit))
  | .Down => .ok (signBit && (bits .RoundBit || bits .StickyBit))
  | .FromZero => .ok (bits .RoundBit || bits .StickyBit)
  | .ToZero => .ok false
  | .Other _ => .error (.methodError "rounds_away_from_zero")

/-! ## Property 1: Bit rounding and mode predicates (`rounding-correct-increment`) -/

/-- The mode predicates, generic tuple forwarders, and `correct_rounding_requires_increment`
follow the documented tie and directed rounding rules across both built-in `RoundingMode` values
and custom mode types `μ`, and agree with exact rational rounding `exactRound` for every bit
pattern, significand quotient, sign, and rounding mode. -/
def CorrectRoundingIncrement : Prop :=
  (∀ (bits : RoundingBit → Bool) (mode : RoundingMode) (signBit : Bool) (q : Nat),
    let m : Nat := 2 * q + (if bits .FinalBit then 1 else 0)
    let rem4 : Nat := (if bits .RoundBit then 2 else 0) + (if bits .StickyBit then 1 else 0)
    let n : Int := if signBit then -(4 * (m : Int) + (rem4 : Int)) else 4 * (m : Int) + (rem4 : Int)
    let rNearest : RoundingMode → Jl Bool := fun r => .ok (roundsToNearest r)
    roundsToNearest mode = roundsToNearestTuple roundsToNearest (mode, signBit) ∧
    roundsAwayFromZero mode signBit = roundsAwayFromZeroTuple roundsAwayFromZero (mode, signBit) ∧
    tieBreakerIsToEven mode = tieBreakerIsToEvenTuple tieBreakerIsToEven (mode, signBit) ∧
    tieBreakerRoundsAway mode signBit =
      tieBreakerRoundsAwayTuple tieBreakerRoundsAway (mode, signBit) ∧
    correctRoundingRequiresIncrement rNearest roundsAwayFromZero tieBreakerIsToEven
      tieBreakerRoundsAway bits (fun b => .ok b) mode signBit =
      expectedIncrement bits mode signBit ∧
    (SupportedMode mode →
      correctRoundingRequiresIncrement rNearest roundsAwayFromZero tieBreakerIsToEven
        tieBreakerRoundsAway bits (fun b => .ok b) mode signBit =
        .ok (decide ((exactRound n 4 mode).natAbs = m + 1)) ∧
      (∀ inc : Bool,
        correctRoundingRequiresIncrement rNearest roundsAwayFromZero tieBreakerIsToEven
          tieBreakerRoundsAway bits (fun b => .ok b) mode signBit = .ok inc →
        exactRound n 4 mode =
          if signBit then -(((m + if inc then 1 else 0 : Nat) : Int))
          else ((m + if inc then 1 else 0 : Nat) : Int)))) ∧
  (∀ {μ : Type} (rNearest : μ → Jl Bool) (rAway : μ → Bool → Jl Bool)
    (tEven : μ → Jl Bool) (tAway : μ → Bool → Jl Bool)
    (bits : RoundingBit → Bool) (mode : μ) (signBit isEven away : Bool),
    roundsToNearestTuple rNearest (mode, signBit) = rNearest mode ∧
    roundsAwayFromZeroTuple rAway (mode, signBit) = rAway mode signBit ∧
    tieBreakerIsToEvenTuple tEven (mode, signBit) = tEven mode ∧
    tieBreakerRoundsAwayTuple tAway (mode, signBit) = tAway mode signBit ∧
    (rNearest mode = .ok true → tEven mode = .ok isEven → tAway mode signBit = .ok away →
      correctRoundingRequiresIncrement rNearest rAway tEven tAway bits (fun b => .ok b) mode signBit =
        .ok (bits .RoundBit && (bits .StickyBit || if isEven then bits .FinalBit else away))) ∧
    (rNearest mode = .ok false → rAway mode signBit = .ok away →
      correctRoundingRequiresIncrement rNearest rAway tEven tAway bits (fun b => .ok b) mode signBit =
        .ok (away && (bits .RoundBit || bits .StickyBit))))

theorem exactRound_bits (bF bR bS signBit : Bool) (mode : RoundingMode) (q : Nat)
    (hm : SupportedMode mode) :
    let m : Nat := 2 * q + (if bF then 1 else 0)
    let rem4 : Nat := (if bR then 2 else 0) + (if bS then 1 else 0)
    let n : Int := if signBit then -(4 * (m : Int) + (rem4 : Int)) else 4 * (m : Int) + (rem4 : Int)
    let inc : Bool :=
      match mode.tag with
      | .Nearest => bR && (bS || bF)
      | .NearestTiesUp => bR && (bS || !signBit)
      | .NearestTiesAway => bR
      | .Up => !signBit && (bR || bS)
      | .Down => signBit && (bR || bS)
      | .FromZero => bR || bS
      | _ => false
    exactRound n 4 mode =
      if signBit then -(((m + if inc then 1 else 0 : Nat) : Int))
      else ((m + if inc then 1 else 0 : Nat) : Int) := by
  obtain ⟨tag⟩ := mode
  cases tag with
  | Other _ => exact False.elim hm
  | Nearest | ToZero | Up | Down | FromZero | NearestTiesAway | NearestTiesUp =>
    dsimp only
    cases bF <;> cases bR <;> cases bS <;> cases signBit <;>
      simp only [exactRound, Bool.false_eq_true, ↓reduceIte,
        Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false,
        Bool.not_true, Bool.not_false] <;>
      try (split <;> try (split <;> try split)) <;> omega

theorem correctRoundingRequiresIncrement_eq (bits : RoundingBit → Bool) (mode : RoundingMode)
    (signBit : Bool) :
    correctRoundingRequiresIncrement (fun r => .ok (roundsToNearest r)) roundsAwayFromZero
      tieBreakerIsToEven tieBreakerRoundsAway bits (fun b => .ok b) mode signBit =
      expectedIncrement bits mode signBit := by
  obtain ⟨tag⟩ := mode
  unfold correctRoundingRequiresIncrement expectedIncrement
    roundsToNearestTuple roundsToNearest
    roundsToNearestNearest roundsToNearestTiesUp roundsToNearestTiesAway roundsToNearestDefault
    tieBreakerIsToEvenTuple tieBreakerIsToEven
    tieBreakerIsToEvenNearest tieBreakerIsToEvenTiesUp tieBreakerIsToEvenTiesAway
    tieBreakerRoundsAwayTuple tieBreakerRoundsAway
    tieBreakerRoundsAwayTiesUp tieBreakerRoundsAwayTiesAway
    roundsAwayFromZeroTuple roundsAwayFromZero
    roundsAwayFromZeroUp roundsAwayFromZeroDown roundsAwayFromZeroFromZero roundsAwayFromZeroToZero
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases tag <;>
    cases bits .FinalBit <;>
    cases bits .RoundBit <;>
    cases bits .StickyBit <;>
    cases signBit <;>
    rfl

theorem correctRoundingIncrement_proven : CorrectRoundingIncrement := by
  refine ⟨?_, ?_⟩
  · intro bits mode signBit q
    dsimp only
    have hci := correctRoundingRequiresIncrement_eq bits mode signBit
    refine ⟨rfl, rfl, rfl, rfl, hci, ?_⟩
    intro hm
    have hex := exactRound_bits (bits .FinalBit) (bits .RoundBit) (bits .StickyBit) signBit mode q hm
    dsimp only at hex
    have hci' :
        expectedIncrement bits mode signBit =
          .ok (match mode.tag with
            | .Nearest => bits .RoundBit && (bits .StickyBit || bits .FinalBit)
            | .NearestTiesUp => bits .RoundBit && (bits .StickyBit || !signBit)
            | .NearestTiesAway => bits .RoundBit
            | .Up => !signBit && (bits .RoundBit || bits .StickyBit)
            | .Down => signBit && (bits .RoundBit || bits .StickyBit)
            | .FromZero => bits .RoundBit || bits .StickyBit
            | _ => false) := by
      obtain ⟨tag⟩ := mode
      cases tag with
      | Other _ => exact False.elim hm
      | _ => rfl
    rw [hci, hci', hex]
    generalize (match mode.tag with
      | .Nearest => bits .RoundBit && (bits .StickyBit || bits .FinalBit)
      | .NearestTiesUp => bits .RoundBit && (bits .StickyBit || !signBit)
      | .NearestTiesAway => bits .RoundBit
      | .Up => !signBit && (bits .RoundBit || bits .StickyBit)
      | .Down => signBit && (bits .RoundBit || bits .StickyBit)
      | .FromZero => bits .RoundBit || bits .StickyBit
      | _ => false) = inc
    refine ⟨?_, ?_⟩
    · congr 1
      cases signBit <;> cases inc <;> simp <;> omega
    · intro inc' hinc
      cases hinc
      rfl
  · intro μ rNearest rAway tEven tAway bits mode signBit isEven away
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro hN hE hA
      unfold correctRoundingRequiresIncrement
        roundsToNearestTuple tieBreakerIsToEvenTuple tieBreakerRoundsAwayTuple
      simp only [hN, hE, hA, Bind.bind, Except.bind, Pure.pure, Except.pure, ↓reduceIte]
      cases bits .RoundBit <;> cases bits .StickyBit <;>
        cases isEven <;> cases bits .FinalBit <;> cases away <;> rfl
    · intro hN hA
      unfold correctRoundingRequiresIncrement
        roundsToNearestTuple roundsAwayFromZeroTuple
      simp only [hN, hA, Bind.bind, Except.bind, Pure.pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
      cases away <;> cases bits .RoundBit <;> cases bits .StickyBit <;> rfl

/-! ## Property 2: Floating-point environment (`rounding-fenv-mode-mapping`) -/

/-- The four raw environment codes form a round-trip bijection with the four IEEE rounding modes
(`RoundNearest`, `RoundDown`, `RoundUp`, `RoundToZero`), unsupported modes raise `MethodError` in
`to_fenv`, and unknown codes raise the specified `ArgumentError` in `from_fenv` and `rounding`. -/
def FEnvModeMapping : Prop :=
  ∀ (codes : FEnvCodes) (showInt : Int → String) (raw : Int)
    (getNative : FEnv → Int) (T : FEnvFloatType) (env : FEnv) (slurp : List Int),
    toFenv codes RoundNearest = .ok codes.toNearest ∧
    toFenv codes RoundDown = .ok codes.downward ∧
    toFenv codes RoundUp = .ok codes.upward ∧
    toFenv codes RoundToZero = .ok codes.towardZero ∧
    toFenv codes RoundFromZero = .error (.methodError "to_fenv") ∧
    toFenv codes RoundNearestTiesAway = .error (.methodError "to_fenv") ∧
    toFenv codes RoundNearestTiesUp = .error (.methodError "to_fenv") ∧
    fromFenv codes (fun a b => decide (a = b)) showInt raw =
      (if raw = codes.toNearest then .ok RoundNearest
       else if raw = codes.downward then .ok RoundDown
       else if raw = codes.upward then .ok RoundUp
       else if raw = codes.towardZero then .ok RoundToZero
       else .error (.argumentError ("invalid rounding mode code: " ++ showInt raw))) ∧
    rounding codes (fun a b => decide (a = b)) showInt getNative T env =
      fromFenv codes (fun a b => decide (a = b)) showInt (roundingRaw getNative T env) ∧
    roundingBottom slurp = .error (.methodError "rounding") ∧
    ((codes.toNearest ≠ codes.downward ∧ codes.toNearest ≠ codes.upward ∧
      codes.toNearest ≠ codes.towardZero ∧ codes.downward ≠ codes.upward ∧
      codes.downward ≠ codes.towardZero ∧ codes.upward ≠ codes.towardZero) →
      ∀ (mode : RoundingMode) (c : Int),
        toFenv codes mode = .ok c ↔
          (mode = RoundNearest ∨ mode = RoundDown ∨ mode = RoundUp ∨ mode = RoundToZero) ∧
          fromFenv codes (fun a b => decide (a = b)) showInt c = .ok mode)

theorem fenvModeMapping_proven : FEnvModeMapping := by
  intro codes showInt raw getNative T env slurp
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · unfold fromFenv
    by_cases h1 : raw = codes.toNearest <;>
      by_cases h2 : raw = codes.downward <;>
      by_cases h3 : raw = codes.upward <;>
      by_cases h4 : raw = codes.towardZero <;>
      simp_all
  · rintro ⟨h12, h13, h14, h23, h24, h34⟩ mode c
    obtain ⟨tag⟩ := mode
    cases tag <;>
      simp only [toFenv, toFenvNearest, toFenvDown, toFenvUp, toFenvToZero,
        fromFenv, RoundNearest, RoundDown, RoundUp, RoundToZero,
        Except.ok.injEq, RoundingMode.mk.injEq, reduceCtorEq,
        false_or, true_or, or_true, true_and, false_and]
    · constructor
      · rintro ⟨⟩; simp
      · intro h
        by_cases hc1 : c = codes.toNearest
        · exact hc1.symm
        · exfalso
          by_cases hc2 : c = codes.downward <;>
            by_cases hc3 : c = codes.upward <;>
            by_cases hc4 : c = codes.towardZero <;>
            simp_all
    · constructor
      · rintro ⟨⟩; simp [Ne.symm h14, Ne.symm h24, Ne.symm h34]
      · intro h
        by_cases hc4 : c = codes.towardZero
        · exact hc4.symm
        · exfalso
          by_cases hc1 : c = codes.toNearest <;>
            by_cases hc2 : c = codes.downward <;>
            by_cases hc3 : c = codes.upward <;>
            simp_all
    · constructor
      · rintro ⟨⟩; simp [Ne.symm h13, Ne.symm h23]
      · intro h
        by_cases hc3 : c = codes.upward
        · exact hc3.symm
        · exfalso
          by_cases hc1 : c = codes.toNearest <;>
            by_cases hc2 : c = codes.downward <;>
            by_cases hc4 : c = codes.towardZero <;>
            simp_all
    · constructor
      · rintro ⟨⟩; simp [Ne.symm h12]
      · intro h
        by_cases hc2 : c = codes.downward
        · exact hc2.symm
        · exfalso
          by_cases hc1 : c = codes.toNearest <;>
            by_cases hc3 : c = codes.upward <;>
            by_cases hc4 : c = codes.towardZero <;>
            simp_all

/-! ## Property 3: Scoped rounding restoration (`rounding-scoped-mode-restoration`) -/

/-- Both scoped wrappers execute the callback in the updated floating-point environment, return its
result or error unchanged, and restore the entry rounding mode afterward. -/
def ScopedRoundingRestored : Prop :=
  ∀ {T α : Type} (getNative : T → FEnv → Int)
    (setNative : T → Int → FEnv → Int × FEnv)
    (setMode : T → RoundingMode → FEnv → Jl FEnv)
    (f : FEnv → Jl α × FEnv) (target : T) (floatTarget : FEnvFloatType)
    (mode : RoundingMode) (raw : Int) (env : FEnv) (slurp : List Int),
    let getF : FEnvFloatType → FEnv → Int :=
      fun t e => roundingRaw (fun s => s.rounding) t e
    let setF : FEnvFloatType → Int → FEnv → Int × FEnv :=
      fun t c e => setroundingRaw id (fun code s => (0, { s with rounding := code })) t c e
    (∀ err, setMode target mode env = .error err →
      setroundingScoped getNative setNative (setroundingDecl setMode) f target mode env =
        (.error err, env)) ∧
    (∀ changed, setMode target mode env = .ok changed →
      (∀ state : FEnv, (setNative target (getNative target env) state).2.rounding =
        getNative target env) →
      (setroundingScoped getNative setNative (setroundingDecl setMode) f target mode env).1 =
        (f changed).1 ∧
      (setroundingScoped getNative setNative (setroundingDecl setMode) f target mode env).2.rounding =
        getNative target env) ∧
    setroundingRawScoped id getF setF f floatTarget raw env =
      ((f { env with rounding := raw }).1,
       { (f { env with rounding := raw }).2 with rounding := env.rounding }) ∧
    (setroundingBottom f slurp : Jl α) = .error (.methodError "setrounding")

theorem scopedRoundingRestored_proven : ScopedRoundingRestored := by
  intro T α getNative setNative setMode f target floatTarget mode raw env slurp getF setF
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro err herr
    simp [setroundingScoped, setroundingDecl, herr]
  · intro changed hok hrestore
    simp [setroundingScoped, setroundingDecl, hok, hrestore]
  · simp [setroundingRawScoped, getF, setF, roundingRaw, setroundingRaw]

/-! ## Property 4: Directed conversion (`rounding-directed-float-conversion`) -/

/-- A converted value is the greatest representable value no greater than the input. -/
def GreatestBelow {α β : Type} (ops : ConvertRoundingOps α β)
    (targetLess : β → β → Bool) (x : α) (y : β) : Prop :=
  ops.greater y x = .ok false ∧
    ∀ z, ops.greater z x = .ok false → targetLess y z = false

/-- A converted value is the least representable value no less than the input. -/
def LeastAbove {α β : Type} (ops : ConvertRoundingOps α β)
    (targetLess : β → β → Bool) (x : α) (y : β) : Prop :=
  ops.less y x = .ok false ∧
    ∀ z, ops.less z x = .ok false → targetLess z y = false

/-- Nearest conversion chooses a closest target value bracketed by `prevfloat` and `nextfloat`, and
mixed comparisons and sign tests agree with the supplied order. -/
def DirectedInputLaw {α β : Type} (ops : ConvertRoundingOps α β)
    (targetLess : β → β → Bool) (inputLess : α → β → Bool)
    (outputLess : β → α → Bool) (isPositive isNegative : α → Bool)
    (distanceLe : β → α → β → Bool) (x : α) : Prop :=
  (∀ y, ops.greater y x = .ok (inputLess x y) ∧
    ops.less y x = .ok (outputLess y x)) ∧
  ops.positive x = .ok (isPositive x) ∧
  ops.negative x = .ok (isNegative x) ∧
  (isPositive x = true → isNegative x = false) ∧
  (isNegative x = true → isPositive x = false) ∧
  (∀ y, ops.convert x = .ok y →
    (∀ z, distanceLe y x z = true) ∧
    (inputLess x y = false → GreatestBelow ops targetLess x y) ∧
    (inputLess x y = true → GreatestBelow ops targetLess x (ops.prevfloat y)) ∧
    (outputLess y x = false → LeastAbove ops targetLess x y) ∧
    (outputLess y x = true → LeastAbove ops targetLess x (ops.nextfloat y)) ∧
    (isPositive x = false → isNegative x = false →
      inputLess x y = false ∧ outputLess y x = false))

/-- Concrete `ConvertRoundingOps` instantiated with `JuliaLean.base.float` operations for converting
a `Float64` value to an `IEEEFloat` type `T`. -/
def floatConvertRoundingOps (T : JuliaLean.base.float.FTy) :
    ConvertRoundingOps (JuliaLean.base.float.FV .f64) (JuliaLean.base.float.FV T) where
  convert x := .ok (JuliaLean.base.float.convertFloat T x)
  greater y x := .ok (JuliaLean.base.float.lt_IEEEFloat x (JuliaLean.base.float.convertFloat .f64 y))
  less y x := .ok (JuliaLean.base.float.lt_IEEEFloat (JuliaLean.base.float.convertFloat .f64 y) x)
  positive x := .ok (JuliaLean.base.float.lt_IEEEFloat (JuliaLean.base.float.zero_float .f64) x)
  negative x := .ok (JuliaLean.base.float.lt_IEEEFloat x (JuliaLean.base.float.zero_float .f64))
  prevfloat := JuliaLean.base.float.prevfloat
  nextfloat := JuliaLean.base.float.nextfloat

/-- Directed conversion selects the nearest representable value on the requested side, and on
concrete `IEEEFloat` conversions in `JuliaLean.base.float` acts as the identity on `Float64` across
all five modes and matches `Fl.convert` in `RoundNearest`. -/
def DirectedConversionSpec : Prop :=
  (∀ {α β : Type} (ops : ConvertRoundingOps α β) (targetLess : β → β → Bool)
    (inputLess : α → β → Bool) (outputLess : β → α → Bool)
    (isPositive isNegative : α → Bool) (distanceLe : β → α → β → Bool) (x : α),
    DirectedInputLaw ops targetLess inputLess outputLess isPositive isNegative distanceLe x →
    (∀ err, ops.convert x = .error err →
      convertRoundingType ops x RoundNearest = .error err) ∧
    (∀ y, convertRoundingType ops x RoundNearest = .ok y →
      ∀ z, distanceLe y x z = true) ∧
    (∀ err, ops.convert x = .error err →
      convertRoundingType ops x RoundDown = .error err ∧
      convertRoundingType ops x RoundUp = .error err ∧
      convertRoundingType ops x RoundToZero = .error err ∧
      convertRoundingType ops x RoundFromZero = .error err) ∧
    (∀ y, convertRoundingType ops x RoundDown = .ok y → GreatestBelow ops targetLess x y) ∧
    (∀ y, convertRoundingType ops x RoundUp = .ok y → LeastAbove ops targetLess x y) ∧
    (∀ y, convertRoundingType ops x RoundToZero = .ok y →
      if isPositive x then GreatestBelow ops targetLess x y
      else if isNegative x then LeastAbove ops targetLess x y
      else ops.greater y x = .ok false ∧ ops.less y x = .ok false) ∧
    (∀ y, convertRoundingType ops x RoundFromZero = .ok y →
      if isPositive x then LeastAbove ops targetLess x y
      else if isNegative x then GreatestBelow ops targetLess x y
      else ops.greater y x = .ok false ∧ ops.less y x = .ok false)) ∧
  (∀ (T : JuliaLean.base.float.FTy) (x : JuliaLean.base.float.FV .f64),
    convertRoundingType (floatConvertRoundingOps T) x RoundNearest = .ok (Fl.convert x) ∧
    convertRoundingType (floatConvertRoundingOps .f64) x RoundNearest = .ok x ∧
    convertRoundingType (floatConvertRoundingOps .f64) x RoundDown = .ok x ∧
    convertRoundingType (floatConvertRoundingOps .f64) x RoundUp = .ok x ∧
    convertRoundingType (floatConvertRoundingOps .f64) x RoundToZero = .ok x ∧
    convertRoundingType (floatConvertRoundingOps .f64) x RoundFromZero = .ok x)

theorem lt_IEEEFloat_irrefl {T : JuliaLean.base.float.FTy} (x : JuliaLean.base.float.FV T) :
    JuliaLean.base.float.lt_IEEEFloat x x = false := by
  unfold JuliaLean.base.float.lt_IEEEFloat JuliaLean.base.float.lt_float
    JuliaLean.C.jlLtFloat Fl.lt
  cases x.isnan <;> cases x.iszero <;> cases x.signbit <;> simp

theorem directedConversionSpec_proven : DirectedConversionSpec := by
  refine ⟨?_, ?_⟩
  · intro α β ops targetLess inputLess outputLess isPositive isNegative distanceLe x hLaw
    obtain ⟨hCmp, hPos, hNeg, hPosNeg, hNegPos, hConv⟩ := hLaw
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro err herr
      simp [convertRoundingType, convertRounding, RoundNearest, convertRoundingNearest, herr]
    · intro y hy z
      simp only [convertRoundingType, convertRounding, RoundNearest, convertRoundingNearest] at hy
      exact (hConv y hy).1 z
    · intro err herr
      simp [convertRoundingType, convertRounding, RoundDown, RoundUp, RoundToZero, RoundFromZero,
        convertRoundingDown, convertRoundingUp, convertRoundingToZero, convertRoundingFromZero,
        herr, Bind.bind, Except.bind]
    · intro y hy
      simp only [convertRoundingType, convertRounding, RoundDown, convertRoundingDown] at hy
      cases hc : ops.convert x with
      | error err => simp [hc, Bind.bind, Except.bind] at hy
      | ok y0 =>
        have hcy := hConv y0 hc
        have hgt := (hCmp y0).1
        simp only [hc, hgt, Bind.bind, Except.bind, Pure.pure, Except.pure] at hy
        cases hg : inputLess x y0
        · simp only [hg, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hy
          subst hy
          exact hcy.2.1 hg
        · simp only [hg, ↓reduceIte, Except.ok.injEq] at hy
          subst hy
          exact hcy.2.2.1 hg
    · intro y hy
      simp only [convertRoundingType, convertRounding, RoundUp, convertRoundingUp] at hy
      cases hc : ops.convert x with
      | error err => simp [hc, Bind.bind, Except.bind] at hy
      | ok y0 =>
        have hcy := hConv y0 hc
        have hlt := (hCmp y0).2
        simp only [hc, hlt, Bind.bind, Except.bind, Pure.pure, Except.pure] at hy
        cases hl : outputLess y0 x
        · simp only [hl, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hy
          subst hy
          exact hcy.2.2.2.1 hl
        · simp only [hl, ↓reduceIte, Except.ok.injEq] at hy
          subst hy
          exact hcy.2.2.2.2.1 hl
    · intro y hy
      simp only [convertRoundingType, convertRounding, RoundToZero, convertRoundingToZero] at hy
      cases hc : ops.convert x with
      | error err => simp [hc, Bind.bind, Except.bind] at hy
      | ok y0 =>
        have hcy := hConv y0 hc
        have hgt := (hCmp y0).1
        have hlt := (hCmp y0).2
        simp only [hc, hPos, hgt, hlt, Bind.bind, Except.bind, Pure.pure, Except.pure] at hy
        cases hp : isPositive x
        · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hy ⊢
          cases hn : isNegative x
          · have hzero := hcy.2.2.2.2.2 hp hn
            simp only [hzero.2, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hy ⊢
            subst hy
            rw [hgt, hlt, hzero.1, hzero.2]
            exact ⟨rfl, rfl⟩
          · simp only [↓reduceIte]
            cases hl : outputLess y0 x
            · simp only [hl, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hy
              subst hy
              exact hcy.2.2.2.1 hl
            · simp only [hl, ↓reduceIte, Except.ok.injEq] at hy
              subst hy
              exact hcy.2.2.2.2.1 hl
        · simp only [hp, ↓reduceIte] at hy ⊢
          cases hg : inputLess x y0
          · simp only [hg, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hy
            subst hy
            exact hcy.2.1 hg
          · simp only [hg, ↓reduceIte, Except.ok.injEq] at hy
            subst hy
            exact hcy.2.2.1 hg
    · intro y hy
      simp only [convertRoundingType, convertRounding, RoundFromZero, convertRoundingFromZero] at hy
      cases hc : ops.convert x with
      | error err => simp [hc, Bind.bind, Except.bind] at hy
      | ok y0 =>
        have hcy := hConv y0 hc
        have hgt := (hCmp y0).1
        have hlt := (hCmp y0).2
        simp only [hc, hNeg, hgt, hlt, Bind.bind, Except.bind, Pure.pure, Except.pure] at hy
        cases hn : isNegative x
        · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hy
          cases hp : isPositive x
          · have hzero := hcy.2.2.2.2.2 hp hn
            simp only [hzero.2, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hy ⊢
            subst hy
            rw [hgt, hlt, hzero.1, hzero.2]
            exact ⟨rfl, rfl⟩
          · simp only [↓reduceIte]
            cases hl : outputLess y0 x
            · simp only [hl, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hy
              subst hy
              exact hcy.2.2.2.1 hl
            · simp only [hl, ↓reduceIte, Except.ok.injEq] at hy
              subst hy
              exact hcy.2.2.2.2.1 hl
        · have hp : isPositive x = false := hNegPos hn
          simp only [hp, hn, Bool.false_eq_true, ↓reduceIte] at hy ⊢
          cases hg : inputLess x y0
          · simp only [hg, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hy
            subst hy
            exact hcy.2.1 hg
          · simp only [hg, ↓reduceIte, Except.ok.injEq] at hy
            subst hy
            exact hcy.2.2.1 hg
  · intro T x
    have hlt : JuliaLean.base.float.lt_IEEEFloat x x = false := lt_IEEEFloat_irrefl x
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
    · simp [convertRoundingType, convertRounding, RoundNearest, convertRoundingNearest,
        floatConvertRoundingOps, JuliaLean.Proofs.base.float.convertFloat_eq]
    · simp [convertRoundingType, convertRounding, RoundDown, convertRoundingDown,
        floatConvertRoundingOps, JuliaLean.base.float.convertFloat, hlt, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · simp [convertRoundingType, convertRounding, RoundUp, convertRoundingUp,
        floatConvertRoundingOps, JuliaLean.base.float.convertFloat, hlt, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · simp only [convertRoundingType, convertRounding, RoundToZero, convertRoundingToZero,
        floatConvertRoundingOps, JuliaLean.base.float.convertFloat, hlt, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
      split <;> rfl
    · simp only [convertRoundingType, convertRounding, RoundFromZero, convertRoundingFromZero,
        floatConvertRoundingOps, JuliaLean.base.float.convertFloat, hlt, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
      split <;> rfl

/-! ## Property 5: Integer and generic type/keyword rounding (`floatfuncs-round-int-exact`) -/

/-- The independent exact integer result promised by `round`, `trunc`, `floor`, and `ceil`. -/
def expectedIntegerRound (t : IntTy) {Tf : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV Tf) (mode : RoundingMode) : Jl (JInt t) :=
  let rational := Fl.toRat x
  let rounded := exactRound rational.1 rational.2 mode
  if Fl.isfinite x && decide (t.min ≤ rounded ∧ rounded ≤ t.max) then
    .ok (JInt.wrap t rounded)
  else
    .error (.inexactError t.name)

/-- The external `round(x, mode)` callee returns a float with the same finiteness as `x` whose
rational value is `exactRound(x, mode)` whenever `x` is finite. -/
def FloatRoundIntegerLaw {Tf : JuliaLean.base.float.FTy}
    (roundValue : JuliaLean.base.float.FV Tf → RoundingMode → Jl (JuliaLean.base.float.FV Tf)) : Prop :=
  ∀ (x : JuliaLean.base.float.FV Tf) (mode : RoundingMode), SupportedMode mode →
    ∃ y : JuliaLean.base.float.FV Tf,
      roundValue x mode = .ok y ∧
      Fl.isfinite y = Fl.isfinite x ∧
      (Fl.isfinite x = true →
        (Fl.toRat y).1 = exactRound (Fl.toRat x).1 (Fl.toRat x).2 mode * ((Fl.toRat y).2 : Int))

/-- Generic contract for `round(x, mode)` and `convert(T, x_integer)` over arbitrary input type `α`,
intermediate rounded type `β`, and target type family `τ` (`resultType : τ → Type`). -/
def GenericRoundConvertLaw {τ α β : Type} (resultType : τ → Type)
    (isFinite : α → Bool) (toRat : α → Int × Nat)
    (canRepresent : τ → Int → Bool) (ofInt : (T : τ) → Int → resultType T)
    (typeName : τ → String)
    (roundValue : α → RoundingMode → Jl β)
    (convert : (T : τ) → β → Jl (resultType T)) : Prop :=
  ∀ (T : τ) (x : α) (mode : RoundingMode), SupportedMode mode →
    ∃ xInt : β,
      roundValue x mode = .ok xInt ∧
      convert T xInt =
        let r := exactRound (toRat x).1 (toRat x).2 mode
        if isFinite x && canRepresent T r then .ok (ofInt T r)
        else .error (.inexactError (typeName T))

theorem toRat_den_pos {Tf : JuliaLean.base.float.FTy} (x : JuliaLean.base.float.FV Tf)
    (h : x.isfinite = true) : 0 < x.toRat.2 :=
  (JuliaLean.Promotion.Fl.toRat_key (JuliaLean.Proofs.base.float.good_fty Tf) x h).1

theorem mul_tdiv_cancel_pos (m : Int) (d : Nat) (hd : 0 < d) :
    (m * (d : Int)).tdiv (d : Int) = m := by
  rcases Int.lt_or_le m 0 with hneg | hpos
  · obtain ⟨k, hk⟩ : ∃ k : Nat, m = -(k : Int) := ⟨(-m).toNat, by omega⟩
    rw [hk, Int.neg_mul, ← Int.natCast_mul, Int.neg_tdiv, ← Int.ofNat_tdiv,
      Nat.mul_div_cancel _ hd]
  · obtain ⟨k, hk⟩ : ∃ k : Nat, m = (k : Int) := ⟨m.toNat, by omega⟩
    rw [hk, ← Int.natCast_mul, ← Int.ofNat_tdiv, Nat.mul_div_cancel _ hd]

/-- Type-converting and keyword-forwarding `round`, `trunc`, `floor`, `ceil`, and `_round_convert`:
(1) for every `IEEEFloat` input (`Tf : FTy`) and `BitInteger` target (`t : IntTy`) via
`JuliaLean.base.float.intOfFloat`, returns the exact rounded integer when in range and raises
`InexactError` otherwise;
(2) for arbitrary generic input types `α`, intermediate types `β`, and target type families
`resultType : τ → Type` satisfying `GenericRoundConvertLaw`, converts the rounded integer to
`resultType T` when representable and raises `InexactError` otherwise across `roundTypeWithMode`,
`truncType`, `floorType`, `ceilType`, `roundType`, and `roundConvert`;
(3) for keyword rounding with `digits`, `sigdigits`, and `base` (`RoundKeywords`) as well as
arbitrary keyword bundles `kws : κ`, `truncKeyword`, `floorKeyword`, `ceilKeyword`, and
`roundKeyword` forward the requested keyword options under `RoundToZero`, `RoundDown`, `RoundUp`,
and `RoundNearest`, matching `exactRoundDigits`. -/
def RoundIntExact : Prop :=
  (∀ (Tf : JuliaLean.base.float.FTy) (t : IntTy) (x : JuliaLean.base.float.FV Tf)
    (mode : RoundingMode)
    (roundValue : JuliaLean.base.float.FV Tf → RoundingMode → Jl (JuliaLean.base.float.FV Tf))
    (slurp : List Int),
    SupportedMode mode → FloatRoundIntegerLaw roundValue →
    roundTypeWithMode JInt roundValue (fun s y => JuliaLean.base.float.intOfFloat s y) t x mode =
      expectedIntegerRound t x mode ∧
    truncType JInt roundValue (fun s y => JuliaLean.base.float.intOfFloat s y) t x =
      expectedIntegerRound t x RoundToZero ∧
    floorType JInt roundValue (fun s y => JuliaLean.base.float.intOfFloat s y) t x =
      expectedIntegerRound t x RoundDown ∧
    ceilType JInt roundValue (fun s y => JuliaLean.base.float.intOfFloat s y) t x =
      expectedIntegerRound t x RoundUp ∧
    roundType JInt roundValue (fun s y => JuliaLean.base.float.intOfFloat s y) t x =
      expectedIntegerRound t x RoundNearest ∧
    (truncBottom slurp () : Jl (JInt t)) = .error (.methodError "trunc") ∧
    (floorBottom slurp () : Jl (JInt t)) = .error (.methodError "floor") ∧
    (ceilBottom slurp () : Jl (JInt t)) = .error (.methodError "ceil") ∧
    (roundBottom slurp () : Jl (JInt t)) = .error (.methodError "round")) ∧
  (∀ {τ α β : Type} (resultType : τ → Type)
    (isFinite : α → Bool) (toRat : α → Int × Nat)
    (canRepresent : τ → Int → Bool) (ofInt : (T : τ) → Int → resultType T)
    (typeName : τ → String)
    (roundValue : α → RoundingMode → Jl β)
    (convert : (T : τ) → β → Jl (resultType T))
    (T : τ) (x : α) (xInt : β) (mode : RoundingMode),
    SupportedMode mode →
    GenericRoundConvertLaw resultType isFinite toRat canRepresent ofInt typeName roundValue convert →
    roundConvert resultType convert T xInt x mode = convert T xInt ∧
    roundTypeWithMode resultType roundValue convert T x mode =
      (let r := exactRound (toRat x).1 (toRat x).2 mode
       if isFinite x && canRepresent T r then .ok (ofInt T r)
       else .error (.inexactError (typeName T))) ∧
    truncType resultType roundValue convert T x =
      (let r := exactRound (toRat x).1 (toRat x).2 RoundToZero
       if isFinite x && canRepresent T r then .ok (ofInt T r)
       else .error (.inexactError (typeName T))) ∧
    floorType resultType roundValue convert T x =
      (let r := exactRound (toRat x).1 (toRat x).2 RoundDown
       if isFinite x && canRepresent T r then .ok (ofInt T r)
       else .error (.inexactError (typeName T))) ∧
    ceilType resultType roundValue convert T x =
      (let r := exactRound (toRat x).1 (toRat x).2 RoundUp
       if isFinite x && canRepresent T r then .ok (ofInt T r)
       else .error (.inexactError (typeName T))) ∧
    roundType resultType roundValue convert T x =
      (let r := exactRound (toRat x).1 (toRat x).2 RoundNearest
       if isFinite x && canRepresent T r then .ok (ofInt T r)
       else .error (.inexactError (typeName T)))) ∧
  (∀ {α κ β : Type} (roundKw : α → RoundingMode → κ → β) (x : α) (kws : κ)
    (q : Int × Nat) (kw : RoundKeywords),
    let roundDigitsFn : (Int × Nat) → RoundingMode → RoundKeywords → Jl (Int × Nat) :=
      fun r m k => .ok (exactRoundDigits r.1 r.2 m k)
    truncKeyword roundKw x kws = roundKw x RoundToZero kws ∧
    floorKeyword roundKw x kws = roundKw x RoundDown kws ∧
    ceilKeyword roundKw x kws = roundKw x RoundUp kws ∧
    roundKeyword roundKw x kws = roundKw x RoundNearest kws ∧
    truncKeyword roundDigitsFn q kw = .ok (exactRoundDigits q.1 q.2 RoundToZero kw) ∧
    floorKeyword roundDigitsFn q kw = .ok (exactRoundDigits q.1 q.2 RoundDown kw) ∧
    ceilKeyword roundDigitsFn q kw = .ok (exactRoundDigits q.1 q.2 RoundUp kw) ∧
    roundKeyword roundDigitsFn q kw = .ok (exactRoundDigits q.1 q.2 RoundNearest kw) ∧
    truncKeyword roundDigitsFn q { digits := 0, sigdigits := none, base := kw.base } =
      .ok (exactRound q.1 q.2 RoundToZero, 1) ∧
    floorKeyword roundDigitsFn q { digits := 0, sigdigits := none, base := kw.base } =
      .ok (exactRound q.1 q.2 RoundDown, 1) ∧
    ceilKeyword roundDigitsFn q { digits := 0, sigdigits := none, base := kw.base } =
      .ok (exactRound q.1 q.2 RoundUp, 1) ∧
    roundKeyword roundDigitsFn q { digits := 0, sigdigits := none, base := kw.base } =
      .ok (exactRound q.1 q.2 RoundNearest, 1))

theorem roundTypeWithMode_intOfFloat_eq (Tf : JuliaLean.base.float.FTy) (t : IntTy)
    (x : JuliaLean.base.float.FV Tf) (mode : RoundingMode)
    (roundValue : JuliaLean.base.float.FV Tf → RoundingMode → Jl (JuliaLean.base.float.FV Tf))
    (hm : SupportedMode mode) (hLaw : FloatRoundIntegerLaw roundValue) :
    roundTypeWithMode JInt roundValue (fun s y => JuliaLean.base.float.intOfFloat s y) t x mode =
      expectedIntegerRound t x mode := by
  obtain ⟨y, hy, hfin, hrat⟩ := hLaw x mode hm
  unfold roundTypeWithMode roundConvert expectedIntegerRound
  simp only [hy, Bind.bind, Except.bind]
  rw [JuliaLean.Proofs.base.float.TruncProofs.intOfFloat_eq Tf t y]
  cases hx : Fl.isfinite x
  · have hyf : y.isfinite = false := by rw [hfin, hx]
    have hyi : y.isinteger = false := by unfold Fl.isinteger; simp [hyf]
    simp [hyi]
  · have hyf : y.isfinite = true := by rw [hfin, hx]
    have hval := hrat hx
    have hd : 0 < y.toRat.2 := toRat_den_pos y hyf
    have hmod : y.toRat.1 % (y.toRat.2 : Int) = 0 := by
      rw [hval, Int.mul_emod_left]
    have hyi : y.isinteger = true := by
      unfold Fl.isinteger
      simp [hyf, hmod]
    have htrunc : y.truncVal = exactRound (Fl.toRat x).1 (Fl.toRat x).2 mode := by
      unfold Fl.truncVal
      rw [hval, mul_tdiv_cancel_pos _ _ hd]
    simp [hyi, htrunc]

theorem roundTypeWithMode_generic_eq {τ α β : Type} (resultType : τ → Type)
    (isFinite : α → Bool) (toRat : α → Int × Nat)
    (canRepresent : τ → Int → Bool) (ofInt : (T : τ) → Int → resultType T)
    (typeName : τ → String)
    (roundValue : α → RoundingMode → Jl β)
    (convert : (T : τ) → β → Jl (resultType T))
    (T : τ) (x : α) (mode : RoundingMode)
    (hm : SupportedMode mode)
    (hLaw : GenericRoundConvertLaw resultType isFinite toRat canRepresent ofInt typeName roundValue convert) :
    roundTypeWithMode resultType roundValue convert T x mode =
      (let r := exactRound (toRat x).1 (toRat x).2 mode
       if isFinite x && canRepresent T r then .ok (ofInt T r)
       else .error (.inexactError (typeName T))) := by
  obtain ⟨xInt, hxInt, hConv⟩ := hLaw T x mode hm
  unfold roundTypeWithMode roundConvert
  simp [hxInt, hConv, Bind.bind, Except.bind]

theorem roundIntExact_proven : RoundIntExact := by
  refine ⟨?_, ?_, ?_⟩
  · intro Tf t x mode roundValue slurp hm hLaw
    exact ⟨roundTypeWithMode_intOfFloat_eq Tf t x mode roundValue hm hLaw,
      roundTypeWithMode_intOfFloat_eq Tf t x RoundToZero roundValue trivial hLaw,
      roundTypeWithMode_intOfFloat_eq Tf t x RoundDown roundValue trivial hLaw,
      roundTypeWithMode_intOfFloat_eq Tf t x RoundUp roundValue trivial hLaw,
      roundTypeWithMode_intOfFloat_eq Tf t x RoundNearest roundValue trivial hLaw,
      rfl, rfl, rfl, rfl⟩
  · intro τ α β resultType isFinite toRat canRepresent ofInt typeName roundValue convert T x xInt mode hm hLaw
    exact ⟨rfl,
      roundTypeWithMode_generic_eq resultType isFinite toRat canRepresent ofInt typeName roundValue convert T x mode hm hLaw,
      roundTypeWithMode_generic_eq resultType isFinite toRat canRepresent ofInt typeName roundValue convert T x RoundToZero trivial hLaw,
      roundTypeWithMode_generic_eq resultType isFinite toRat canRepresent ofInt typeName roundValue convert T x RoundDown trivial hLaw,
      roundTypeWithMode_generic_eq resultType isFinite toRat canRepresent ofInt typeName roundValue convert T x RoundUp trivial hLaw,
      roundTypeWithMode_generic_eq resultType isFinite toRat canRepresent ofInt typeName roundValue convert T x RoundNearest trivial hLaw⟩
  · intro α κ β roundKw x kws q kw roundDigitsFn
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp [truncKeyword, floorKeyword, ceilKeyword, roundKeyword, roundDigitsFn, exactRoundDigits]

/-! ## Property 6: Double rounding to `Float32` (`floatfuncs-round-float-type-double`) -/

/-- `|p-r| ≤ |q-r|` for exact rationals with positive denominators. -/
def ratDistLe (p q r : Int × Nat) : Bool :=
  decide ((p.1 * (r.2 : Int) - r.1 * (p.2 : Int)).natAbs * (q.2 * r.2) ≤
    (q.1 * (r.2 : Int) - r.1 * (q.2 : Int)).natAbs * (p.2 * r.2))

/-- The documented contract for `round(Float32, x)` and `round(Float32, x, RoundNearest)`
(`base/rounding.jl:352-354`): for every non-NaN `IEEEFloat` input `x` (across `Float16`, `Float32`,
and `Float64`, finite or infinite) and every `BitInteger` or `Int` (`BigInt`) real input, rounding
to `Float32` preserves `±Inf` and rounds finite inputs to the nearest `Float32`-representable
integer (or `±Inf` when beyond one ulp above `floatmax(Float32)`). -/
def RoundToF32Nearest : Prop :=
  (∀ (S : JuliaLean.base.float.FTy) (x : JuliaLean.base.float.FV S)
    (c : JuliaLean.base.float.FV .f32),
    Fl.isnan x = false → Fl.isfinite c = true →
    (Fl.toRat c).1 % ((Fl.toRat c).2 : Int) = 0 →
    ∃ y : JuliaLean.base.float.FV .f32,
      roundTypeWithMode JuliaLean.base.float.FV
        (fun z _ => .ok (JuliaLean.base.float.round_Nearest_llvm z))
        (fun T z => .ok (JuliaLean.base.float.convertFloat T z))
        .f32 x RoundNearest = .ok y ∧
      roundType JuliaLean.base.float.FV
        (fun z _ => .ok (JuliaLean.base.float.round_Nearest_llvm z))
        (fun T z => .ok (JuliaLean.base.float.convertFloat T z))
        .f32 x = .ok y ∧
      (Fl.isinf x = true → y = Fl.inf x.signbit) ∧
      (Fl.isfinite x = true → Fl.isfinite y = true →
        ratDistLe (Fl.toRat y) (Fl.toRat c) (Fl.toRat x) = true)) ∧
  (∀ (Ti : IntTy) (n : JInt Ti) (c : JuliaLean.base.float.FV .f32),
    Fl.isfinite c = true → (Fl.toRat c).1 % ((Fl.toRat c).2 : Int) = 0 →
    ∃ y : JuliaLean.base.float.FV .f32,
      roundTypeWithMode JuliaLean.base.float.FV
        (fun z m => .ok (roundInteger z m))
        (fun T z => .ok (JuliaLean.base.float.floatOfInt T z))
        .f32 n RoundNearest = .ok y ∧
      roundType JuliaLean.base.float.FV
        (fun z m => .ok (roundInteger z m))
        (fun T z => .ok (JuliaLean.base.float.floatOfInt T z))
        .f32 n = .ok y ∧
      (Fl.isfinite y = true → ratDistLe (Fl.toRat y) (Fl.toRat c) (n.val, 1) = true))

/-- `x = 16777217.3` (`0x4170000014cccccd`) and `c = 16777218f0` (`0x4b800001`):
`round(Float64(x), RoundNearest) = 16777217.0`, which `convert(Float32, ...)` rounds to even
(`16777216f0`), even though `16777218f0` is closer to `16777217.3`. -/
theorem roundToF32Nearest_refuted : ¬ RoundToF32Nearest := by
  intro h
  have bad := h.1 .f64 (Fl.ofBits 0x4170000014cccccd) (Fl.ofBits 0x4b800001)
    (by decide) (by decide) (by decide)
  rcases bad with ⟨y, hy, _, _, hdist⟩
  change Except.ok (JuliaLean.base.float.convertFloat .f32
    (JuliaLean.base.float.round_Nearest_llvm (Fl.ofBits 0x4170000014cccccd))) = Except.ok y at hy
  injection hy with hy_eq
  subst hy_eq
  revert hdist
  decide +kernel

/-! ## Property 7: Integer rounding identity (`rounding-integer-input-identity`) -/

/-- Rounding an integer `x` in any mode agrees with `exactRound x 1 mode = x` across arbitrary
`Integer` types `α`, unbounded `BigInt` (`Int`), `Bool`, and all ten fixed-width `BitInteger`
types (`JInt source`); keyword and type-converting wrappers preserve every in-range integer and
raise `InexactError` when out of range. -/
def IntegerRoundIdentity : Prop :=
  ∀ {α κ : Type} (intVal : α → Int) (u : α) (kws : κ)
    (z : Int) (b : Bool) (target source : IntTy) (x : JInt source) (mode : RoundingMode),
    let boolVal : Bool → Int := fun v => if v then 1 else 0
    -- Generic `Integer` subtype `α`:
    exactRound (intVal u) 1 mode = intVal u ∧
    intVal (roundInteger u mode) = exactRound (intVal u) 1 mode ∧
    roundInteger u mode = u ∧
    truncKeyword (fun v m (_ : κ) => roundInteger v m) u kws = u ∧
    floorKeyword (fun v m (_ : κ) => roundInteger v m) u kws = u ∧
    ceilKeyword (fun v m (_ : κ) => roundInteger v m) u kws = u ∧
    roundKeyword (fun v m (_ : κ) => roundInteger v m) u kws = u ∧
    -- `BigInt` (`Int`):
    exactRound z 1 mode = z ∧
    roundInteger z mode = exactRound z 1 mode ∧
    roundTypeWithMode (fun _ : Unit => Int) (fun v m => .ok (roundInteger v m))
      (fun _ v => .ok v) () z mode = .ok (exactRound z 1 mode) ∧
    roundTypeWithMode JInt (fun v m => .ok (roundInteger v m))
      JInt.convert target z mode =
      (if decide (target.min ≤ exactRound z 1 mode ∧ exactRound z 1 mode ≤ target.max) then
        .ok (JInt.wrap target (exactRound z 1 mode))
       else .error (.inexactError target.name)) ∧
    -- `Bool`:
    roundInteger b mode = b ∧
    boolVal (roundInteger b mode) = exactRound (boolVal b) 1 mode ∧
    roundTypeWithMode (fun _ : Unit => Bool) (fun v m => .ok (roundInteger v m))
      (fun _ v => .ok v) () b mode = .ok b ∧
    roundTypeWithMode JInt (fun v m => .ok (roundInteger v m))
      (fun t v => JInt.convert t (boolVal v)) target b mode =
      .ok (JInt.wrap target (exactRound (boolVal b) 1 mode)) ∧
    -- Fixed-width `BitInteger` (`JInt source`):
    exactRound x.val 1 mode = x.val ∧
    (roundInteger x mode).val = exactRound x.val 1 mode ∧
    roundInteger x mode = x ∧
    roundTypeWithMode JInt (fun v m => .ok (roundInteger v m))
      (fun t y => JuliaLean.base.int.convert t y) target x mode =
      (if decide (target.min ≤ exactRound x.val 1 mode ∧ exactRound x.val 1 mode ≤ target.max) then
        .ok (JInt.wrap target (exactRound x.val 1 mode))
       else .error (.inexactError target.name)) ∧
    truncType JInt (fun v m => .ok (roundInteger v m))
      (fun t y => JuliaLean.base.int.convert t y) target x =
      (if decide (target.min ≤ exactRound x.val 1 RoundToZero ∧
          exactRound x.val 1 RoundToZero ≤ target.max) then
        .ok (JInt.wrap target (exactRound x.val 1 RoundToZero))
       else .error (.inexactError target.name)) ∧
    floorType JInt (fun v m => .ok (roundInteger v m))
      (fun t y => JuliaLean.base.int.convert t y) target x =
      (if decide (target.min ≤ exactRound x.val 1 RoundDown ∧
          exactRound x.val 1 RoundDown ≤ target.max) then
        .ok (JInt.wrap target (exactRound x.val 1 RoundDown))
       else .error (.inexactError target.name)) ∧
    ceilType JInt (fun v m => .ok (roundInteger v m))
      (fun t y => JuliaLean.base.int.convert t y) target x =
      (if decide (target.min ≤ exactRound x.val 1 RoundUp ∧
          exactRound x.val 1 RoundUp ≤ target.max) then
        .ok (JInt.wrap target (exactRound x.val 1 RoundUp))
       else .error (.inexactError target.name)) ∧
    roundType JInt (fun v m => .ok (roundInteger v m))
      (fun t y => JuliaLean.base.int.convert t y) target x =
      (if decide (target.min ≤ exactRound x.val 1 RoundNearest ∧
          exactRound x.val 1 RoundNearest ≤ target.max) then
        .ok (JInt.wrap target (exactRound x.val 1 RoundNearest))
       else .error (.inexactError target.name)) ∧
    roundTypeWithMode JInt (fun v m => .ok (roundInteger v m))
      (fun t y => JuliaLean.base.int.convert t y) source x mode = .ok x

theorem exactRound_one (z : Int) (mode : RoundingMode) : exactRound z 1 mode = z := by
  simp [exactRound]

theorem jintConvert_eq_ite (target : IntTy) (z : Int) :
    JInt.convert target z =
      if decide (target.min ≤ z ∧ z ≤ target.max) then .ok (JInt.wrap target z)
      else .error (.inexactError target.name) := by
  unfold JInt.convert
  by_cases h : target.min ≤ z ∧ z ≤ target.max
  · rw [decide_eq_true h]
    simp only [h, and_self, ↓reduceDIte, ↓reduceIte, Except.ok.injEq]
    apply Subtype.ext
    exact (wrapInt_of_inRange target z h).symm
  · rw [decide_eq_false h]
    simp only [h, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]

theorem boolVal_inRange (target : IntTy) (b : Bool) :
    target.min ≤ (if b then (1 : Int) else 0) ∧ (if b then (1 : Int) else 0) ≤ target.max := by
  cases target <;> cases b <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]

theorem integerRoundIdentity_proven : IntegerRoundIdentity := by
  intro α κ intVal u kws z b target source x mode boolVal
  have hexU : exactRound (intVal u) 1 mode = intVal u := exactRound_one (intVal u) mode
  have hexZ : exactRound z 1 mode = z := exactRound_one z mode
  have hexB : exactRound (boolVal b) 1 mode = boolVal b := exactRound_one (boolVal b) mode
  have hexX : ∀ m, exactRound x.val 1 m = x.val := fun m => exactRound_one x.val m
  refine ⟨hexU, by rw [hexU]; rfl, rfl, rfl, rfl, rfl, rfl,
    hexZ, by rw [hexZ]; rfl, ?_, ?_,
    rfl, by rw [hexB]; rfl, rfl, ?_,
    hexX mode, by rw [hexX mode]; rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hexZ]; rfl
  · rw [hexZ]
    unfold roundTypeWithMode roundConvert roundInteger
    simp only [Bind.bind, Except.bind]
    exact jintConvert_eq_ite target z
  · rw [hexB]
    unfold roundTypeWithMode roundConvert roundInteger
    simp only [Bind.bind, Except.bind]
    rw [jintConvert_eq_ite target (boolVal b), decide_eq_true (boolVal_inRange target b)]
    rfl
  · rw [hexX mode]
    unfold roundTypeWithMode roundConvert roundInteger JuliaLean.base.int.convert
    simp only [Bind.bind, Except.bind]
    exact jintConvert_eq_ite target x.val
  · rw [hexX RoundToZero]
    unfold truncType roundTypeWithMode roundConvert roundInteger JuliaLean.base.int.convert
    simp only [Bind.bind, Except.bind]
    exact jintConvert_eq_ite target x.val
  · rw [hexX RoundDown]
    unfold floorType roundTypeWithMode roundConvert roundInteger JuliaLean.base.int.convert
    simp only [Bind.bind, Except.bind]
    exact jintConvert_eq_ite target x.val
  · rw [hexX RoundUp]
    unfold ceilType roundTypeWithMode roundConvert roundInteger JuliaLean.base.int.convert
    simp only [Bind.bind, Except.bind]
    exact jintConvert_eq_ite target x.val
  · rw [hexX RoundNearest]
    unfold roundType roundTypeWithMode roundConvert roundInteger JuliaLean.base.int.convert
    simp only [Bind.bind, Except.bind]
    exact jintConvert_eq_ite target x.val
  · unfold roundTypeWithMode roundConvert roundInteger JuliaLean.base.int.convert JInt.convert
    simp only [Bind.bind, Except.bind, x.property, and_self, ↓reduceDIte]

/-! ## Property 8: Zero-subnormal control (`rounding-zero-subnormal-setting`) -/

/-- Setting zero-subnormal behavior succeeds whenever `yes = false` or the hardware supports
zeroing subnormals, updates the environment flag iff it succeeds, and `get_zero_subnormals` reads
back the environment flag from any C status word. -/
def ZeroSubnormalBehavior : Prop :=
  ∀ (supportsZeroing yes : Bool) (env : FEnv) (nonzeroCode : Int),
    nonzeroCode ≠ 0 →
    let step : Bool → FEnv → Int × FEnv :=
      fun req state =>
        if req && !supportsZeroing then (nonzeroCode, state)
        else (0, { state with zeroSubnormals := req })
    let setNative : Bool → Int := fun req => (step req env).1
    let afterEnv : FEnv := (step yes env).2
    let getFromEnv : FEnv → Unit → Int :=
      fun state () => if state.zeroSubnormals then nonzeroCode else 0
    setZeroSubnormals setNative false = true ∧
    setZeroSubnormals setNative yes = (!yes || supportsZeroing) ∧
    getZeroSubnormals (getFromEnv env) = env.zeroSubnormals ∧
    (setZeroSubnormals setNative yes = true →
      getZeroSubnormals (getFromEnv afterEnv) = yes) ∧
    (setZeroSubnormals setNative yes = false →
      yes = true ∧ supportsZeroing = false ∧
      getZeroSubnormals (getFromEnv afterEnv) = env.zeroSubnormals)

theorem zeroSubnormalBehavior_proven : ZeroSubnormalBehavior := by
  intro supportsZeroing yes env nonzeroCode hne step setNative afterEnv getFromEnv
  have hbeq : (nonzeroCode == 0) = false := beq_eq_false_iff_ne.mpr hne
  have hbne : (nonzeroCode != 0) = true := bne_iff_ne.mpr hne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [setZeroSubnormals, setNative, step]
  · cases yes <;> cases supportsZeroing <;>
      simp [setZeroSubnormals, setNative, step, hbeq]
  · cases hzs : env.zeroSubnormals <;>
      simp [getZeroSubnormals, getFromEnv, hzs, hbne]
  · cases yes <;> cases supportsZeroing <;>
      simp [setZeroSubnormals, getZeroSubnormals, setNative, afterEnv, getFromEnv, step, hbeq, hbne]
  · cases yes <;> cases supportsZeroing <;>
      cases hzs : env.zeroSubnormals <;>
      simp [setZeroSubnormals, getZeroSubnormals, setNative, afterEnv, getFromEnv, step, hzs, hbeq, hbne]

/-! ## Nothing-to-promise entries -/

/-! Nothing to promise: setrounding(T::Type, mode)@206: docstring signature declaration with no method body; covered as `setroundingDecl` in `ScopedRoundingRestored`. -/
/-! Nothing to promise: rounding(::Type{Union{}}, slurp...)@223: bottom-type ambiguity trap that unconditionally throws `MethodError`; covered in `FEnvModeMapping`. -/
/-! Nothing to promise: setrounding(f, ::Type{Union{}}, slurp...)@247: bottom-type ambiguity trap that unconditionally throws `MethodError`; covered in `ScopedRoundingRestored`. -/
/-! Nothing to promise: trunc(::Type{Union{}}, slurp...; kwargs...)@492: bottom-type ambiguity trap that unconditionally throws `MethodError`; covered in `RoundIntExact`. -/
/-! Nothing to promise: floor(::Type{Union{}}, slurp...; kwargs...)@493: bottom-type ambiguity trap that unconditionally throws `MethodError`; covered in `RoundIntExact`. -/
/-! Nothing to promise: ceil(::Type{Union{}}, slurp...; kwargs...)@494: bottom-type ambiguity trap that unconditionally throws `MethodError`; covered in `RoundIntExact`. -/
/-! Nothing to promise: round(::Type{Union{}}, slurp...; kwargs...)@495: bottom-type ambiguity trap that unconditionally throws `MethodError`; covered in `RoundIntExact`. -/

/-! ## Method-to-property table -/

def methodProperties : List (String × String) := [
  ("rounds_to_nearest(::RoundingMode)@115", "CorrectRoundingIncrement"),
  ("rounds_to_nearest(::RoundingMode{:Nearest})@116", "CorrectRoundingIncrement"),
  ("rounds_to_nearest(::RoundingMode{:NearestTiesUp})@117", "CorrectRoundingIncrement"),
  ("rounds_to_nearest(::RoundingMode{:NearestTiesAway})@118", "CorrectRoundingIncrement"),
  ("rounds_away_from_zero(::RoundingMode{:Up}, Bool)@119", "CorrectRoundingIncrement"),
  ("rounds_away_from_zero(::RoundingMode{:Down}, Bool)@120", "CorrectRoundingIncrement"),
  ("rounds_away_from_zero(::RoundingMode{:FromZero}, Bool)@121", "CorrectRoundingIncrement"),
  ("rounds_away_from_zero(::RoundingMode{:ToZero}, Bool)@122", "CorrectRoundingIncrement"),
  ("tie_breaker_is_to_even(::RoundingMode{:Nearest})@123", "CorrectRoundingIncrement"),
  ("tie_breaker_is_to_even(::RoundingMode{:NearestTiesUp})@124", "CorrectRoundingIncrement"),
  ("tie_breaker_is_to_even(::RoundingMode{:NearestTiesAway})@125", "CorrectRoundingIncrement"),
  ("tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesUp}, Bool)@126", "CorrectRoundingIncrement"),
  ("tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesAway}, Bool)@127", "CorrectRoundingIncrement"),
  ("rounds_to_nearest(::Tuple{Any,Bool})@129", "CorrectRoundingIncrement"),
  ("rounds_away_from_zero(::Tuple{Any,Bool})@130", "CorrectRoundingIncrement"),
  ("tie_breaker_is_to_even(::Tuple{Any,Bool})@131", "CorrectRoundingIncrement"),
  ("tie_breaker_rounds_away_from_zero(::Tuple{Any,Bool})@132", "CorrectRoundingIncrement"),
  ("correct_rounding_requires_increment@138", "CorrectRoundingIncrement"),
  ("to_fenv(::RoundingMode{:Nearest})@170", "FEnvModeMapping"),
  ("to_fenv(::RoundingMode{:ToZero})@171", "FEnvModeMapping"),
  ("to_fenv(::RoundingMode{:Up})@172", "FEnvModeMapping"),
  ("to_fenv(::RoundingMode{:Down})@173", "FEnvModeMapping"),
  ("from_fenv(::Integer)@175", "FEnvModeMapping"),
  ("setrounding(T::Type, mode)@206", "ScopedRoundingRestored"),
  ("setrounding_raw(::Type{<:Union{Float32,Float64}}, Integer)@219", "ScopedRoundingRestored"),
  ("rounding_raw(::Type{<:Union{Float32,Float64}})@220", "FEnvModeMapping; ScopedRoundingRestored"),
  ("rounding(::Type{T})@222", "FEnvModeMapping"),
  ("rounding(::Type{Union{}}, slurp...)@223", "FEnvModeMapping"),
  ("setrounding(f, ::Type{T}, RoundingMode)@238", "ScopedRoundingRestored"),
  ("setrounding(f, ::Type{Union{}}, slurp...)@247", "ScopedRoundingRestored"),
  ("setrounding_raw(f, ::Type{T}, rounding)@248", "ScopedRoundingRestored"),
  ("(::Type{T})(x::Real, RoundingMode)@267", "DirectedConversionSpec"),
  ("_convert_rounding(::Type{T}, x::Real, RoundingMode{:Nearest})@269", "DirectedConversionSpec"),
  ("_convert_rounding(::Type{T}, x::Real, RoundingMode{:Down})@270", "DirectedConversionSpec"),
  ("_convert_rounding(::Type{T}, x::Real, RoundingMode{:Up})@274", "DirectedConversionSpec"),
  ("_convert_rounding(::Type{T}, x::Real, RoundingMode{:ToZero})@278", "DirectedConversionSpec"),
  ("_convert_rounding(::Type{T}, x::Real, RoundingMode{:FromZero})@286", "DirectedConversionSpec"),
  ("set_zero_subnormals(Bool)@313", "ZeroSubnormalBehavior"),
  ("get_zero_subnormals()@325", "ZeroSubnormalBehavior"),
  ("trunc(x; kws...)@480", "RoundIntExact; IntegerRoundIdentity"),
  ("floor(x; kws...)@481", "RoundIntExact; IntegerRoundIdentity"),
  ("ceil(x; kws...)@482", "RoundIntExact; IntegerRoundIdentity"),
  ("round(x; kws...)@483", "RoundIntExact; IntegerRoundIdentity"),
  ("trunc(::Type{T}, x)@485", "RoundIntExact; IntegerRoundIdentity"),
  ("floor(::Type{T}, x)@486", "RoundIntExact; IntegerRoundIdentity"),
  ("ceil(::Type{T}, x)@487", "RoundIntExact; IntegerRoundIdentity"),
  ("round(::Type{T}, x)@488", "RoundIntExact; RoundToF32Nearest; IntegerRoundIdentity"),
  ("round(::Type{T}, x, RoundingMode)@490", "RoundIntExact; RoundToF32Nearest; IntegerRoundIdentity"),
  ("_round_convert(::Type{T}, x_integer, x, r)@491", "RoundIntExact; RoundToF32Nearest; IntegerRoundIdentity"),
  ("trunc(::Type{Union{}}, slurp...; kwargs...)@492", "RoundIntExact"),
  ("floor(::Type{Union{}}, slurp...; kwargs...)@493", "RoundIntExact"),
  ("ceil(::Type{Union{}}, slurp...; kwargs...)@494", "RoundIntExact"),
  ("round(::Type{Union{}}, slurp...; kwargs...)@495", "RoundIntExact"),
  ("round(::Integer, RoundingMode)@497", "IntegerRoundIdentity")
]

/-! ## Registry -/

def entries : List JuliaLean.Registry.Entry := [
  { id := "floatfuncs-round-int-exact", juliaFile := "base/rounding.jl",
    juliaFns := ["round(::Type{T}, x, ::RoundingMode)", "_round_convert(::Type{T}, x_integer, x, r)",
      "trunc(::Type{T}, x)", "floor(::Type{T}, x)", "ceil(::Type{T}, x)", "round(::Type{T}, x)",
      "trunc(x; kws...)", "floor(x; kws...)", "ceil(x; kws...)", "round(x; kws...)",
      "trunc(::Type{Union{}}, slurp...; kwargs...)", "floor(::Type{Union{}}, slurp...; kwargs...)",
      "ceil(::Type{Union{}}, slurp...; kwargs...)", "round(::Type{Union{}}, slurp...; kwargs...)"],
    statement := "For every IEEEFloat input and BitInteger target (via intOfFloat), and generically for any input and target type under GenericRoundConvertLaw, rounding in any supported mode returns the exact rounded integer when representable and throws InexactError otherwise; trunc, floor, ceil, and default round forward their mode and digits/sigdigits/base keyword arguments.",
    source := "base/rounding.jl:337-345,420-427,451-458,468-475,480-495", status := .proven,
    prop := ``RoundIntExact, thm := some ``roundIntExact_proven },
  { id := "floatfuncs-round-float-type-double", juliaFile := "base/rounding.jl",
    juliaFns := ["round(::Type{Float32}, x, ::RoundingMode)", "round(::Type{Float32}, x)",
      "Base._round_convert"],
    statement := "For every non-NaN IEEEFloat input (including infinities) and every integer/real input, round(Float32, x) preserves ±Inf and rounds finite inputs to the Float32-representable integer nearest to x.",
    source := "base/rounding.jl:352-354 (round docstring), 488-491", status := .refuted,
    prop := ``RoundToF32Nearest, thm := some ``roundToF32Nearest_refuted,
    issue := "none found (queries: round Float32; round Float16; round Float32 double rounding; round to float type nearest; round Float16 RoundNearestTiesAway; _round_convert; PRs: round Float16)",
    notes := "round(Float32, 16777217.3) == 16777216f0 although 16777218f0 is closer: round(x, RoundNearest) gives 16777217.0, which _round_convert converts to Float32 via round-to-even." },
  { id := "rounding-correct-increment", juliaFile := "base/rounding.jl",
    juliaFns := ["rounds_to_nearest(::RoundingMode)", "rounds_to_nearest(::RoundingMode{:Nearest})",
      "rounds_to_nearest(::RoundingMode{:NearestTiesUp})", "rounds_to_nearest(::RoundingMode{:NearestTiesAway})",
      "rounds_away_from_zero(::RoundingMode{:Up}, ::Bool)", "rounds_away_from_zero(::RoundingMode{:Down}, ::Bool)",
      "rounds_away_from_zero(::RoundingMode{:FromZero}, ::Bool)", "rounds_away_from_zero(::RoundingMode{:ToZero}, ::Bool)",
      "tie_breaker_is_to_even(::RoundingMode{:Nearest})", "tie_breaker_is_to_even(::RoundingMode{:NearestTiesUp})",
      "tie_breaker_is_to_even(::RoundingMode{:NearestTiesAway})",
      "tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesUp}, ::Bool)",
      "tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesAway}, ::Bool)",
      "rounds_to_nearest(::Tuple{Any,Bool})", "rounds_away_from_zero(::Tuple{Any,Bool})",
      "tie_breaker_is_to_even(::Tuple{Any,Bool})", "tie_breaker_rounds_away_from_zero(::Tuple{Any,Bool})",
      "correct_rounding_requires_increment"],
    statement := "The mode predicates, tuple forwarders, and increment decision follow nearest-even, nearest-ties-up, nearest-ties-away, and directed rounding across built-in and custom modes and match exact rational rounding for every bit pattern, significand quotient, and sign.",
    source := "base/rounding.jl:115-168", status := .proven,
    prop := ``CorrectRoundingIncrement, thm := some ``correctRoundingIncrement_proven },
  { id := "rounding-fenv-mode-mapping", juliaFile := "base/rounding.jl",
    juliaFns := ["to_fenv(::RoundingMode{:Nearest})", "to_fenv(::RoundingMode{:ToZero})",
      "to_fenv(::RoundingMode{:Up})", "to_fenv(::RoundingMode{:Down})",
      "from_fenv(::Integer)", "rounding_raw(::Type{<:Union{Float32,Float64}})",
      "rounding(::Type{T})", "rounding(::Type{Union{}}, slurp...)"],
    statement := "The four IEEE fenv codes form a round-trip bijection with RoundNearest, RoundDown, RoundUp, and RoundToZero; unsupported modes raise MethodError in to_fenv and unknown codes raise ArgumentError in from_fenv and rounding.",
    source := "base/rounding.jl:170-187,219-223", status := .proven,
    prop := ``FEnvModeMapping, thm := some ``fenvModeMapping_proven },
  { id := "rounding-scoped-mode-restoration", juliaFile := "base/rounding.jl",
    juliaFns := ["setrounding(T::Type, mode)",
      "setrounding_raw(::Type{<:Union{Float32,Float64}}, ::Integer)",
      "rounding_raw(::Type{<:Union{Float32,Float64}})",
      "setrounding(f::Function, ::Type{T}, ::RoundingMode)",
      "setrounding(f, ::Type{Union{}}, slurp...)",
      "setrounding_raw(f::Function, ::Type{T}, rounding)"],
    statement := "Both scoped setters execute the callback under the requested rounding mode, return its result or error, and restore the original floating-point rounding mode afterward.",
    source := "base/rounding.jl:206,219-220,238-256", status := .proven,
    prop := ``ScopedRoundingRestored, thm := some ``scopedRoundingRestored_proven },
  { id := "rounding-directed-float-conversion", juliaFile := "base/rounding.jl",
    juliaFns := ["(::Type{T})(x::Real, r::RoundingMode)",
      "_convert_rounding(::Type{T}, x::Real, ::RoundingMode{:Nearest})",
      "_convert_rounding(::Type{T}, x::Real, ::RoundingMode{:Down})",
      "_convert_rounding(::Type{T}, x::Real, ::RoundingMode{:Up})",
      "_convert_rounding(::Type{T}, x::Real, ::RoundingMode{:ToZero})",
      "_convert_rounding(::Type{T}, x::Real, ::RoundingMode{:FromZero})"],
    statement := "Floating-point type conversion uses nearest conversion in RoundNearest, chooses the closest representable value on the required side in directed modes, and on concrete IEEEFloat conversions preserves Float64 inputs across all five modes.",
    source := "base/rounding.jl:259-293", status := .proven,
    prop := ``DirectedConversionSpec, thm := some ``directedConversionSpec_proven },
  { id := "rounding-zero-subnormal-setting", juliaFile := "base/rounding.jl",
    juliaFns := ["set_zero_subnormals(yes::Bool)", "get_zero_subnormals()"],
    statement := "Setting zero-subnormal behavior succeeds whenever disabling or when hardware supports zeroing subnormals, updates the environment flag iff it succeeds, and get_zero_subnormals reads back the current flag.",
    source := "base/rounding.jl:298-325", status := .proven,
    prop := ``ZeroSubnormalBehavior, thm := some ``zeroSubnormalBehavior_proven },
  { id := "rounding-integer-input-identity", juliaFile := "base/rounding.jl",
    juliaFns := ["round(x::Integer, r::RoundingMode)", "round(::Type{T}, x, ::RoundingMode)",
      "_round_convert(::Type{T}, x_integer, x, r)", "trunc(::Type{T}, x)", "floor(::Type{T}, x)",
      "ceil(::Type{T}, x)", "round(::Type{T}, x)", "trunc(x; kws...)", "floor(x; kws...)",
      "ceil(x; kws...)", "round(x; kws...)"],
    statement := "Rounding an integer input in any mode equals exactRound(x, 1, mode) = x across generic Integer types, BigInt, Bool, and all fixed-width BitInteger types; keyword and type-converting integer rounding preserve in-range integers and throw InexactError out of range.",
    source := "base/rounding.jl:480-491,497", status := .proven,
    prop := ``IntegerRoundIdentity, thm := some ``integerRoundIdentity_proven }
]

end JuliaLean.Proofs.base.rounding
