import JuliaLean.base.parsers.ints

/-!
# `base/parsers/Parsers.jl` and `base/parsers/ints.jl`

The byte helpers use natural numbers reduced modulo `2^64`, matching `UInt64`.
The integer parser records the observable value/failure result. Its `Bool` case
keeps the generic method's `T(base)` conversion, which is the source of the
documented counterexample.
-/

namespace JuliaLean.MiscCov.Parsers

open JuliaLean.MiscCov

def HelperContract : Prop :=
  (∀ buf i, i + 8 ≤ buf.length →
    load8Stable buf i = load8CodeUnits buf i ∧ load8Stable buf i = load8Word buf i) ∧
  (∀ buf i, load8Generic buf i =
    (List.range 8).reverse.foldl (fun w k => u64 (w * 256 ||| byte buf (i + k))) 0) ∧
  (∀ w, isdigits8 w =
    (((w &&& 0xf0f0f0f0f0f0f0f0) |||
      ((add64 w 0x0606060606060606 &&& 0xf0f0f0f0f0f0f0f0) >>> 4)) == 0x3333333333333333)) ∧
  (∀ w, digits8 w =
    let x := sub64 w 0x3030303030303030
    let x := add64 (mul64 x 10) (x >>> 8)
    (((mul64 (x &&& 0x000000ff000000ff) 0x000f424000000064) +
      mul64 ((x >>> 16) &&& 0x000000ff000000ff) 0x0000271000000001) % 2^64) >>> 32) ∧
  (∀ w lo hi, bytesin w lo hi =
    (mul64 (0x80 - lo) 0x0101010101010101 |> add64 w) &&&
    Nat.xor (mul64 (0x7f - hi) 0x0101010101010101 |> add64 w) (2^64 - 1) &&&
    0x8080808080808080) ∧
  (∀ w, ishexdigits8 w =
    ((w &&& 0x8080808080808080 == 0) &&
      ((bytesin w 0x30 0x39 ||| bytesin (w ||| 0x2020202020202020) 0x61 0x66) ==
        0x8080808080808080))) ∧
  (∀ w, hexdigits8 w =
    let x := add64 (w &&& 0x0f0f0f0f0f0f0f0f) (mul64 ((w >>> 6) &&& 0x0101010101010101) 9)
    let x := ((x <<< 4) ||| (x >>> 8)) &&& 0x00ff00ff00ff00ff
    let x := ((x <<< 8) ||| (x >>> 16)) &&& 0x0000ffff0000ffff
    ((x <<< 16) ||| (x >>> 32)) &&& 0x00000000ffffffff) ∧
  (∀ buf i j base, overflowfailure buf i j base =
    if ((buf.drop i).take (j + 1 - i)).all (fun b => digitvalue b base < base)
    then .overflow else .invalid) ∧
  showFailure .invalid = "Base.Parsers.INVALID" ∧
  showFailure .overflow = "Base.Parsers.OVERFLOW" ∧
  showFailure .underflow = "Base.Parsers.UNDERFLOW" ∧
  digitvalue 0x30 10 = 0 ∧ digitvalue 0x39 10 = 9 ∧
  digitvalue 0x41 16 = 10 ∧ digitvalue 0x61 16 = 10 ∧ digitvalue 0x61 62 = 36

theorem helperContract_proven : HelperContract := by
  unfold HelperContract
  refine ⟨fun buf i _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl,
    rfl, rfl, rfl, ?_⟩
  decide

/-- The docstring promises a value or `ParseFailure`, without throwing, for
every integer type and valid base. -/
def ParsevalueNoThrow : Prop := ∀ bytes base, 2 ≤ base → base ≤ 62 →
  ∃ r, parsevalue .bool false bytes base = .ok r

theorem parsevalueNoThrow_refuted : ¬ ParsevalueNoThrow := by
  intro h
  rcases h [0x31] 10 (by decide) (by decide) with ⟨r, hr⟩
  simp [parsevalue, parseintInteger, convertKind, bind, Except.bind] at hr

def ParseContract : Prop :=
  (∀ bits signed neg buf i j base,
    parseintBit bits signed neg buf i j base =
      if j < i then .failure .invalid else
        let ds := (buf.drop i).take (j + 1 - i)
        let p := if base = 10 then parseMagnitude ds 10
          else if bits < 32 then parseMagnitude ds base
          else if base = 16 then parseMagnitude ds 16 else parseMagnitude ds base
        match p with
        | none => .failure .invalid
        | some n =>
          let lim := if signed then (if neg then 2^(bits - 1) else 2^(bits - 1) - 1) else 2^bits - 1
          if n ≤ lim then .value (if neg then -(n : Int) else n) else .failure .overflow) ∧
  (∀ bytes base, parsevalue .arbitrary true bytes base =
    if !(2 ≤ base && base ≤ 62) then .error (.argumentError "invalid base")
    else
      let (neg, i) := match bytes with
        | b :: _ => if b == 0x2d || b == 0x2b then (b == 0x2d, 1) else (false, 0)
        | [] => (false, 0)
      parseintInteger .arbitrary bytes i (bytes.length - 1) base neg)

theorem parseContract_proven : ParseContract := by
  constructor
  · intro bits signed neg buf i j base
    rfl
  · intro bytes base
    simp only [parsevalue]
    split <;> rfl

end JuliaLean.MiscCov.Parsers
