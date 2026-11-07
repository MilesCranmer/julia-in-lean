import JuliaLean.base.parsers.floats

namespace JuliaLean.NumMisc

/-- NaN payload acceptance agrees with the documented unsigned-integer grammar. -/
def FloatGrammarExact : Prop :=
  ∀ s : List Byte, (sourceNanPayload s).isSome = documentedNanPayload s

/-- Every nonnegative integer through `2^53` takes the exact fast path and is unchanged. -/
def FloatExactIntegerRounding : Prop :=
  ∀ w : Nat, w ≤ 2^53 → fromDecimalInteger w = some w

def fooPayload : List Byte := [102, 111, 111]

theorem sourceNanPayload_foo : sourceNanPayload fooPayload = some 0 := by decide +kernel

theorem documentedNanPayload_foo : documentedNanPayload fooPayload = false := by decide +kernel

theorem floatGrammarExact_refuted : ¬ FloatGrammarExact := by
  intro h
  have hs := h fooPayload
  rw [sourceNanPayload_foo, documentedNanPayload_foo] at hs
  simp at hs

theorem floatExactIntegerRounding_proven : FloatExactIntegerRounding := by
  intro w hw
  simp [fromDecimalInteger, hw]

end JuliaLean.NumMisc

namespace JuliaLean.NumMisc.Coverage

def ParserInitBehavior : Prop :=
  (∀ xs m carry, mulSmall xs m carry =
    match xs with
    | [] => ([], carry)
    | x :: rest =>
        let product := x * m + carry
        let tail := mulSmall rest m (product / limbBase)
        (product % limbBase :: tail.1, tail.2)) ∧
  (∀ kind, pow10Range kind = match kind with
    | .f64 => (-342, 308) | .f32 => (-64, 38) | .f16 => (-26, 4)) ∧
  (∀ kind, halfwayRange kind = match kind with
    | .f64 => (-4, 23) | .f32 => (-17, 10) | .f16 => (-26, 5)) ∧
  (∀ a b, mul64Parts a b = (a * b / limbBase % limbBase, a * b % limbBase)) ∧
  (∀ kind w q, eiselPath kind w q =
    let range := pow10Range kind
    if w == 0 then .zero else if q < range.1 || q > range.2 then .outOfRange
    else if q == 0 then .exact else .general) ∧
  (∀ w q powers bits, decimalPath w q powers bits =
    if w == 0 then .zero
    else if q.natAbs < powers && w ≤ 2^(bits + 1) then .exactPower else .eisel) ∧
  (∀ xs, div5Limbs xs =
    let result := div5BigEndian xs.reverse 0; (result.1.reverse, result.2)) ∧
  (∀ xs k s, top128At xs k s =
    let ki : Int := k
    let hi := if s == 0 then limbAt xs ki
      else (limbAt xs ki * 2^s + limbAt xs (ki - 1) / 2^(64 - s)) % limbBase
    let lo := if s == 0 then limbAt xs (ki - 1)
      else (limbAt xs (ki - 1) * 2^s + limbAt xs (ki - 2) / 2^(64 - s)) % limbBase
    (hi, lo)) ∧
  (∀ bits raw m e, packBitsShape bits raw m e =
    if e ≤ 0 then .finite m 0 else
      let carry := m ≥ 2^(bits + 1)
      let m' := if carry then m / 2 else m
      let e' := if carry then e + 1 else e
      if e' ≥ raw then .infinity else .finite m' e'.toNat) ∧
  (∀ bits infinity, fromBitsShape bits infinity =
    if bits == 0 then .underflow else if bits == infinity then .overflow else .finite bits) ∧
  (∀ kind, exactPow10Count kind = match kind with | .f64 => 23 | .f32 => 11 | .f16 => 5) ∧
  (∀ base n, powerChunks base n =
    let step := if base == 2 then 63 else 27
    (List.range ((n + step - 1) / step)).map fun k => min (n - k * step) step)

theorem parserInitBehavior : ParserInitBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro xs; cases xs <;> intros <;> rfl
  · intro kind; cases kind <;> rfl
  · intro kind; cases kind <;> rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro kind; cases kind <;> rfl
  · intros; rfl
def ParserScanBehavior : Prop :=
  (∀ bytes word, matchWord bytes word =
    (bytes.length ≥ word.length &&
      ((bytes.take word.length).zip word).all (fun p => asciiLower p.1 == p.2))) ∧
  (∀ bytes, parseValueRoute bytes = floatParseRoute bytes) ∧
  (∀ payload, sourceNanPayload payload =
    if payload.all isNanChar then some (if documentedNanPayload payload then 1 else 0) else none)

theorem parserScanBehavior : ParserScanBehavior := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

end JuliaLean.NumMisc.Coverage
