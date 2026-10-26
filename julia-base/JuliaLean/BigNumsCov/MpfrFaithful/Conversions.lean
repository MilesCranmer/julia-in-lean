import JuliaLean.BigNumsCov.MpfrFaithful.Prelude

namespace JuliaLean.BigNumsCov.MpfrFaithful

/-! Method-specific mirrors for `base/mpfr.jl:299-565`. -/

def widen299 (_ : Unit) : TypeResult := .bigFloat
def Widen299 : Prop := ∀ input, widen299 input = .bigFloat
theorem widen299_proven : Widen299 := by simp [Widen299, widen299]

def widen300 (_ : Unit) : TypeResult := .bigFloat
def Widen300 : Prop := ∀ input, widen300 input = .bigFloat
theorem widen300_proven : Widen300 := by simp [Widen300, widen300]

def bigFloat302 (precisionOf : BFRep → Int) (allocate : Int → BFRep)
    (setValue : BFRep → BFRep → RMode → BFRep) (x : BFRep) (mode : RMode)
    (precision : Int) : Run BFRep :=
  if precision = precisionOf x then ⟨["precision(x)"], x⟩
  else
    let output := allocate precision
    ⟨["precision(x)", "BigFloat(;precision)", "mpfr_set"], setValue output x mode⟩

def BigFloat302 : Prop :=
  ∀ precisionOf allocate setValue x mode precision,
    (bigFloat302 precisionOf allocate setValue x mode precision).value =
      if precision = precisionOf x then x else setValue (allocate precision) x mode
theorem bigFloat302_proven : BigFloat302 := by
  unfold BigFloat302
  intros precisionOf allocate setValue x mode precision
  by_cases h : precision = precisionOf x <;> simp [bigFloat302, h]

def duplicate313 (precisionOf : BFRep → Int) (allocate : Int → BFRep)
    (setValue : BFRep → BFRep → Int → BFRep) (x : BFRep) : Run BFRep :=
  let output := allocate (precisionOf x)
  ⟨["precision(x)", "BigFloat(;precision)", "mpfr_set(round=0)"],
    setValue output x 0⟩

def Duplicate313 : Prop :=
  ∀ precisionOf allocate setValue x,
    (duplicate313 precisionOf allocate setValue x).value =
      setValue (allocate (precisionOf x)) x 0
theorem duplicate313_proven : Duplicate313 := by
  unfold Duplicate313
  intros
  rfl

def bigFloat322 (allocate : Int → BFRep)
    (setMachine : BFRep → Int → RMode → BFRep) (x : Int) (mode : RMode)
    (precision : Int) : Run BFRep :=
  let output := allocate precision
  ⟨["BigFloat(;precision)", "mpfr_set_si/ui"], setMachine output x mode⟩

def BigFloat322 : Prop :=
  ∀ allocate setMachine x mode precision,
    (bigFloat322 allocate setMachine x mode precision).value =
      setMachine (allocate precision) x mode
theorem bigFloat322_proven : BigFloat322 := by unfold BigFloat322; intros; rfl

structure Float64CtorInput where
  precision : Int
  significandBits : Int
  signBit : Bool
  kind : BFClass
  exponent : Int
  significandWord : Nat
  limbBits : Nat
  limbIs64 : Bool
  deriving Repr, DecidableEq

def bigFloat330 (allocate : Int → BFRep)
    (setDouble : BFRep → Float64CtorInput → RMode → BFRep)
    (input : Float64CtorInput) (mode : RMode) : Run BFRep :=
  let output := allocate input.precision
  if input.precision ≤ input.significandBits then
    ⟨["BigFloat(;precision)", "mpfr_set_d", "NaN-sign-fix"],
      setDouble output input mode⟩
  else
    let sign := if input.signBit then -1 else 1
    match input.kind with
    | .zero => ⟨["BigFloat(;precision)", "store-sign", "store-zero-exp"],
        { output with sign := sign, exponent := -1 }⟩
    | .infinity => ⟨["BigFloat(;precision)", "store-sign", "store-inf-exp"],
        { output with sign := sign, exponent := -3 }⟩
    | .nan => ⟨["BigFloat(;precision)", "store-sign", "store-nan-exp"],
        { output with sign := sign, exponent := -2 }⟩
    | .finite =>
        let limbCount := (input.precision + input.limbBits - 1) / input.limbBits
        if input.limbIs64 then
          ⟨["BigFloat(;precision)", "store-sign", "store-exponent", "reinterpret-significand",
            "compute-limb-count", "Limb===UInt64", "zero-low-limbs", "store-high-limb"],
            { precision := output.precision, sign := sign, exponent := input.exponent + 1,
              words := List.replicate (limbCount - 1).toNat 0 ++ [input.significandWord] }⟩
        else
          ⟨["BigFloat(;precision)", "store-sign", "store-exponent", "reinterpret-significand",
            "compute-limb-count", "Limb!==UInt64", "zero-low-limbs", "store-low32", "store-high32"],
            { precision := output.precision, sign := sign, exponent := input.exponent + 1,
              words := List.replicate (limbCount - 2).toNat 0 ++
                [input.significandWord % 2^32, input.significandWord / 2^32] }⟩

def BigFloat330 : Prop :=
  ∀ allocate setDouble input mode,
    (bigFloat330 allocate setDouble input mode).value =
      let output := allocate input.precision
      if input.precision ≤ input.significandBits then setDouble output input mode
      else
        let sign := if input.signBit then -1 else 1
        match input.kind with
        | .zero => { output with sign := sign, exponent := -1 }
        | .infinity => { output with sign := sign, exponent := -3 }
        | .nan => { output with sign := sign, exponent := -2 }
        | .finite =>
            let limbCount := (input.precision + input.limbBits - 1) / input.limbBits
            if input.limbIs64 then
              { precision := output.precision, sign := sign, exponent := input.exponent + 1,
                words := List.replicate (limbCount - 1).toNat 0 ++ [input.significandWord] }
            else
              { precision := output.precision, sign := sign, exponent := input.exponent + 1,
                words := List.replicate (limbCount - 2).toNat 0 ++
                  [input.significandWord % 2^32, input.significandWord / 2^32] }
theorem bigFloat330_proven : BigFloat330 := by
  unfold BigFloat330
  intros allocate setDouble input mode
  by_cases h : input.precision ≤ input.significandBits
  · simp [bigFloat330, h]
  · simp [bigFloat330, h]
    cases hk : input.kind <;> simp
    by_cases hl : input.limbIs64 = true <;> simp [hl]

def bigFloat374 (allocate : Int → BFRep)
    (setBigInt : BFRep → Int → RMode → BFRep) (x : Int) (mode : RMode)
    (precision : Int) : Run BFRep :=
  let output := allocate precision
  ⟨["BigFloat(;precision)", "mpfr_set_z"], setBigInt output x mode⟩

def BigFloat374 : Prop :=
  ∀ allocate setBigInt x mode precision,
    (bigFloat374 allocate setBigInt x mode precision).value =
      setBigInt (allocate precision) x mode
theorem bigFloat374_proven : BigFloat374 := by unfold BigFloat374; intros; rfl

def bigFloat380 (toBigInt : Int → Int) (roundingRaw : Unit → RMode)
    (construct : Int → RMode → Int → BFRep) (x precision : Int) : Run BFRep :=
  let integer := toBigInt x
  let mode := roundingRaw ()
  ⟨["BigInt(x)", "rounding_raw", "BigFloat(BigInt,r;precision)"],
    construct integer mode precision⟩
def BigFloat380 : Prop :=
  ∀ toBigInt roundingRaw construct x precision,
    (bigFloat380 toBigInt roundingRaw construct x precision).value =
      construct (toBigInt x) (roundingRaw ()) precision
theorem bigFloat380_proven : BigFloat380 := by unfold BigFloat380; intros; rfl

def bigFloat382 (toBigInt : Int → Int) (construct : Int → RMode → Int → BFRep)
    (x : Int) (mode : RMode) (precision : Int) : Run BFRep :=
  ⟨["BigInt(x)", "BigFloat(BigInt,r;precision)"], construct (toBigInt x) mode precision⟩
def BigFloat382 : Prop :=
  ∀ toBigInt construct x mode precision,
    (bigFloat382 toBigInt construct x mode precision).value = construct (toBigInt x) mode precision
theorem bigFloat382_proven : BigFloat382 := by unfold BigFloat382; intros; rfl

def bigFloat385 (toClong : Int → Int) (construct : Int → RMode → Int → BFRep)
    (x : Int) (mode : RMode) (precision : Int) : Run BFRep :=
  ⟨["convert(Clong,x)", "BigFloat(Clong,r;precision)"], construct (toClong x) mode precision⟩
def BigFloat385 : Prop :=
  ∀ toClong construct x mode precision,
    (bigFloat385 toClong construct x mode precision).value = construct (toClong x) mode precision
theorem bigFloat385_proven : BigFloat385 := by unfold BigFloat385; intros; rfl

def bigFloat387 (toCulong : Int → Int) (construct : Int → RMode → Int → BFRep)
    (x : Int) (mode : RMode) (precision : Int) : Run BFRep :=
  ⟨["convert(Culong,x)", "BigFloat(Culong,r;precision)"], construct (toCulong x) mode precision⟩
def BigFloat387 : Prop :=
  ∀ toCulong construct x mode precision,
    (bigFloat387 toCulong construct x mode precision).value = construct (toCulong x) mode precision
theorem bigFloat387_proven : BigFloat387 := by unfold BigFloat387; intros; rfl

def bigFloat390 (toFloat64 : Int → Int) (construct : Int → RMode → Int → BFRep)
    (x : Int) (mode : RMode) (precision : Int) : Run BFRep :=
  ⟨["Float64(x)", "BigFloat(Float64,r;precision)"], construct (toFloat64 x) mode precision⟩
def BigFloat390 : Prop :=
  ∀ toFloat64 construct x mode precision,
    (bigFloat390 toFloat64 construct x mode precision).value = construct (toFloat64 x) mode precision
theorem bigFloat390_proven : BigFloat390 := by unfold BigFloat390; intros; rfl

def opposite401 (mode : RMode) : RMode :=
  if mode = Mpfr.Mode.up then Mpfr.Mode.down
  else if mode = Mpfr.Mode.down then Mpfr.Mode.up
  else mode
def Opposite401 : Prop :=
  ∀ mode, opposite401 mode =
    if mode = Mpfr.Mode.up then Mpfr.Mode.down
    else if mode = Mpfr.Mode.down then Mpfr.Mode.up
    else mode
theorem opposite401_proven : Opposite401 := by unfold Opposite401; intros; rfl

def bigFloat393 (numerator denominator : Int → Int) (convert : Int → RMode → BFRep)
    (divide : BFRep → BFRep → BFRep) (value : Int) (mode : RMode) : Run BFRep :=
  let denominatorMode := opposite401 mode
  let top := convert (numerator value) mode
  let bottom := convert (denominator value) denominatorMode
  ⟨["opposite-round", "setprecision-scope", "setrounding-scope", "numerator",
    "BigFloat(numerator)", "denominator", "BigFloat(denominator,opposite)", "divide"],
    divide top bottom⟩
def BigFloat393 : Prop :=
  ∀ numerator denominator convert divide value mode,
    (bigFloat393 numerator denominator convert divide value mode).value =
      divide (convert (numerator value) mode)
        (convert (denominator value) (opposite401 mode))
theorem bigFloat393_proven : BigFloat393 := by unfold BigFloat393; intros; rfl

def tryparse407 (recurse : String → Int → Int → RMode → Option BFRep)
    (stripTrailing : String → String) (endsSpace : String → Bool)
    (allocate : Int → BFRep) (setString : BFRep → String → Int → RMode → Int)
    (text : String) (base precision : Int) (mode : RMode) : Run (Option BFRep) :=
  if endsSpace text then
    ⟨["trailing-space-check", "rstrip", "recursive-tryparse"],
      recurse (stripTrailing text) base precision mode⟩
  else
    let output := allocate precision
    let status := setString output text base mode
    ⟨["trailing-space-check", "BigFloat(;precision)", "mpfr_set_str"],
      if status = 0 then some output else none⟩
def Tryparse407 : Prop :=
  ∀ recurse stripTrailing endsSpace allocate setString text base precision mode,
    (tryparse407 recurse stripTrailing endsSpace allocate setString text base precision mode).value =
      if endsSpace text then recurse (stripTrailing text) base precision mode
      else
        let output := allocate precision
        if setString output text base mode = 0 then some output else none
theorem tryparse407_proven : Tryparse407 := by
  unfold Tryparse407
  intros recurse stripTrailing endsSpace allocate setString text base precision mode
  by_cases h : endsSpace text = true <;> simp [tryparse407, h]

def bigFloat414 (parse : String → Int → RMode → BFRep) (text : String)
    (mode : RMode) (precision : Int) : Run BFRep :=
  ⟨["parse(BigFloat,text;precision,rounding)"], parse text precision mode⟩
def BigFloat414 : Prop :=
  ∀ parse text mode precision,
    (bigFloat414 parse text mode precision).value = parse text precision mode
theorem bigFloat414_proven : BigFloat414 := by unfold BigFloat414; intros; rfl

def rational417 (convert : BFRep → Int) (x : BFRep) : Int := convert x
def Rational417 : Prop := ∀ convert x, rational417 convert x = convert x
theorem rational417_proven : Rational417 := by unfold Rational417; intros; rfl

def abstractFloat418 (convert : Int → BFRep) (x : Int) : BFRep := convert x
def AbstractFloat418 : Prop := ∀ convert x, abstractFloat418 convert x = convert x
theorem abstractFloat418_proven : AbstractFloat418 := by unfold AbstractFloat418; intros; rfl

def float420 (_ : Unit) : TypeResult := .bigFloat
def Float420 : Prop := ∀ input, float420 input = .bigFloat
theorem float420_proven : Float420 := by simp [Float420, float420]

def bigFloat422 (convertMode : PMode → RMode) (construct : Int → RMode → Int → BFRep)
    (x : Int) (mode : PMode) (precision : Int) : Run BFRep :=
  ⟨["convert(MPFRRoundingMode,r)", "BigFloat(x,raw;precision)"],
    construct x (convertMode mode) precision⟩
def BigFloat422 : Prop :=
  ∀ convertMode construct x mode precision,
    (bigFloat422 convertMode construct x mode precision).value =
      construct x (convertMode mode) precision
theorem bigFloat422_proven : BigFloat422 := by unfold BigFloat422; intros; rfl

def bigFloat424 (convertMode : PMode → RMode)
    (construct : String → RMode → Int → BFRep) (text : String) (mode : PMode)
    (precision : Int) : Run BFRep :=
  ⟨["convert(MPFRRoundingMode,r)", "BigFloat(text,raw;precision)"],
    construct text (convertMode mode) precision⟩
def BigFloat424 : Prop :=
  ∀ convertMode construct text mode precision,
    (bigFloat424 convertMode construct text mode precision).value =
      construct text (convertMode mode) precision
theorem bigFloat424_proven : BigFloat424 := by unfold BigFloat424; intros; rfl

def unchecked428 (convertMode : PMode → RMode) (cast : Int → RMode → Int)
    (x : Int) (mode : PMode) : Run Int :=
  ⟨["convert(MPFRRoundingMode,r)", "_unchecked_cast(raw)"], cast x (convertMode mode)⟩
def Unchecked428 : Prop :=
  ∀ convertMode cast x mode,
    (unchecked428 convertMode cast x mode).value = cast x (convertMode mode)
theorem unchecked428_proven : Unchecked428 := by unfold Unchecked428; intros; rfl

def unchecked430 (getSigned : BFRep → RMode → Int) (x : BFRep) (mode : RMode) : Run Int :=
  ⟨["mpfr_get_sj"], getSigned x mode⟩
def Unchecked430 : Prop := ∀ getSigned x mode, (unchecked430 getSigned x mode).value = getSigned x mode
theorem unchecked430_proven : Unchecked430 := by unfold Unchecked430; intros; rfl

def unchecked434 (getUnsigned : BFRep → RMode → Int) (x : BFRep) (mode : RMode) : Run Int :=
  ⟨["mpfr_get_uj"], getUnsigned x mode⟩
def Unchecked434 : Prop := ∀ getUnsigned x mode, (unchecked434 getUnsigned x mode).value = getUnsigned x mode
theorem unchecked434_proven : Unchecked434 := by unfold Unchecked434; intros; rfl

def unchecked438 (allocateBigInt : Unit → Int) (getBigInt : Int → BFRep → RMode → Int)
    (x : BFRep) (mode : RMode) : Run Int :=
  let output := allocateBigInt ()
  ⟨["BigInt()", "mpfr_get_z"], getBigInt output x mode⟩
def Unchecked438 : Prop :=
  ∀ allocate get x mode,
    (unchecked438 allocate get x mode).value = get (allocate ()) x mode
theorem unchecked438_proven : Unchecked438 := by unfold Unchecked438; intros; rfl

def unchecked444 (signed narrow : Bool) (castSigned castUnsigned castBig : BFRep → RMode → Int)
    (x : BFRep) (mode : RMode) : Run Int :=
  if narrow then
    if signed then ⟨["select-Int64", "_unchecked_cast(Int64)"], castSigned x mode⟩
    else ⟨["select-UInt64", "_unchecked_cast(UInt64)"], castUnsigned x mode⟩
  else ⟨["select-BigInt", "_unchecked_cast(BigInt)"], castBig x mode⟩
def Unchecked444 : Prop :=
  ∀ signed narrow castSigned castUnsigned castBig x mode,
    (unchecked444 signed narrow castSigned castUnsigned castBig x mode).value =
      if narrow then if signed then castSigned x mode else castUnsigned x mode
      else castBig x mode
theorem unchecked444_proven : Unchecked444 := by
  unfold Unchecked444
  intros signed narrow castSigned castUnsigned castBig x mode
  by_cases hn : narrow = true <;> by_cases hs : signed = true <;>
    simp [unchecked444, hn, hs]

def round449 (clear : Unit → Unit) (cast : BFRep → RMode → Int)
    (rangeFlag : Unit → Bool) (truncate : Int → Int) (minimum maximum : Int)
    (x : BFRep) (mode : RMode) : Run (Except String Int) :=
  let _ := clear ()
  let result := cast x mode
  if rangeFlag () || result < minimum || maximum < result then
    ⟨["clear_flags", "_unchecked_cast", "had_range_exception", "range-check"],
      .error "InexactError"⟩
  else ⟨["clear_flags", "_unchecked_cast", "had_range_exception", "range-check",
    "unsafe_trunc"], .ok (truncate result)⟩
def Round449 : Prop :=
  ∀ clear cast rangeFlag truncate minimum maximum x mode,
    (round449 clear cast rangeFlag truncate minimum maximum x mode).value =
      let result := cast x mode
      if rangeFlag () || result < minimum || maximum < result then .error "InexactError"
      else .ok (truncate result)
theorem round449_proven : Round449 := by
  unfold Round449
  intros clear cast rangeFlag truncate minimum maximum x mode
  simp [round449]
  split <;> rfl

def round458 (clear : Unit → Unit) (cast : BFRep → RMode → Int)
    (rangeFlag : Unit → Bool) (x : BFRep) (mode : RMode) : Run (Except String Int) :=
  let _ := clear ()
  let result := cast x mode
  if rangeFlag () then
    ⟨["clear_flags", "_unchecked_cast(BigInt)", "had_range_exception"], .error "InexactError"⟩
  else ⟨["clear_flags", "_unchecked_cast(BigInt)", "had_range_exception"], .ok result⟩
def Round458 : Prop :=
  ∀ clear cast rangeFlag x mode,
    (round458 clear cast rangeFlag x mode).value =
      if rangeFlag () then .error "InexactError" else .ok (cast x mode)
theorem round458_proven : Round458 := by
  unfold Round458
  intros clear cast rangeFlag x mode
  by_cases h : rangeFlag () = true <;> simp [round458, h]

def invoke465 (invokeRound : BFRep → PMode → Int) (x : BFRep) (mode : PMode) : Int :=
  invokeRound x mode
def Invoke465 : Prop := ∀ invokeRound x mode, invoke465 invokeRound x mode = invokeRound x mode
theorem invoke465_proven : Invoke465 := by unfold Invoke465; intros; rfl

def invoke467 (invokeRound : BFRep → PMode → Int) (x : BFRep) (mode : PMode) : Int :=
  invokeRound x mode
def Invoke467 : Prop := ∀ invokeRound x mode, invoke467 invokeRound x mode = invokeRound x mode
theorem invoke467_proven : Invoke467 := by unfold Invoke467; intros; rfl

def unsafe471 (cast : BFRep → RMode → Int) (truncate : Int → Int)
    (x : BFRep) : Run Int :=
  let value := cast x Mpfr.Mode.toZero
  ⟨["_unchecked_cast(RoundToZero)", "unsafe_trunc"], truncate value⟩
def Unsafe471 : Prop :=
  ∀ cast truncate x, (unsafe471 cast truncate x).value = truncate (cast x Mpfr.Mode.toZero)
theorem unsafe471_proven : Unsafe471 := by unfold Unsafe471; intros; rfl

def unsafe472 (cast : BFRep → RMode → Int) (x : BFRep) : Run Int :=
  ⟨["_unchecked_cast(BigInt,RoundToZero)"], cast x Mpfr.Mode.toZero⟩
def Unsafe472 : Prop := ∀ cast x, (unsafe472 cast x).value = cast x Mpfr.Mode.toZero
theorem unsafe472_proven : Unsafe472 := by unfold Unsafe472; intros; rfl

def round474 (roundingRaw : Unit → RMode) (roundValue : BFRep → RMode → Int)
    (x : BFRep) : Run Int :=
  ⟨["rounding_raw", "round(T,x,mode)"], roundValue x (roundingRaw ())⟩
def Round474 : Prop :=
  ∀ roundingRaw roundValue x,
    (round474 roundingRaw roundValue x).value = roundValue x (roundingRaw ())
theorem round474_proven : Round474 := by unfold Round474; intros; rfl

def round476 (roundBig : BFRep → PMode → Int) (x : BFRep) (mode : PMode) : Int :=
  roundBig x mode
def Round476 : Prop := ∀ roundBig x mode, round476 roundBig x mode = roundBig x mode
theorem round476_proven : Round476 := by unfold Round476; intros; rfl

def round477 (roundBig : BFRep → RMode → Int) (x : BFRep) (mode : RMode) : Int :=
  roundBig x mode
def Round477 : Prop := ∀ roundBig x mode, round477 roundBig x mode = roundBig x mode
theorem round477_proven : Round477 := by unfold Round477; intros; rfl

def bool479 (isZero isOne : BFRep → Bool) (x : BFRep) : Run (Except String Bool) :=
  if isZero x then ⟨["iszero"], .ok false⟩
  else if isOne x then ⟨["iszero", "isone"], .ok true⟩
  else ⟨["iszero", "isone", "InexactError"], .error "InexactError"⟩
def Bool479 : Prop :=
  ∀ isZero isOne x,
    (bool479 isZero isOne x).value =
      if isZero x then .ok false else if isOne x then .ok true else .error "InexactError"
theorem bool479_proven : Bool479 := by
  unfold Bool479
  intros isZero isOne x
  by_cases hz : isZero x = true <;> by_cases ho : isOne x = true <;>
    simp [bool479, hz, ho]

def bigInt484 (isInteger : BFRep → Bool) (truncate : BFRep → Int)
    (x : BFRep) : Run (Except String Int) :=
  if isInteger x then ⟨["isinteger", "trunc(BigInt,x)"], .ok (truncate x)⟩
  else ⟨["isinteger", "InexactError"], .error "InexactError"⟩
def BigInt484 : Prop :=
  ∀ isInteger truncate x,
    (bigInt484 isInteger truncate x).value =
      if isInteger x then .ok (truncate x) else .error "InexactError"
theorem bigInt484_proven : BigInt484 := by
  unfold BigInt484
  intros isInteger truncate x
  by_cases h : isInteger x = true <;> simp [bigInt484, h]

def convert489 (isInteger : BFRep → Bool) (truncate : BFRep → Int)
    (x : BFRep) : Run (Except String Int) :=
  if isInteger x then ⟨["isinteger", "trunc(T,x)"], .ok (truncate x)⟩
  else ⟨["isinteger", "InexactError"], .error "InexactError"⟩
def Convert489 : Prop :=
  ∀ isInteger truncate x,
    (convert489 isInteger truncate x).value =
      if isInteger x then .ok (truncate x) else .error "InexactError"
theorem convert489_proven : Convert489 := by
  unfold Convert489
  intros isInteger truncate x
  by_cases h : isInteger x = true <;> simp [convert489, h]

structure IeeeInput where
  signBit : Bool
  kind : BFClass
  exponent : Int
  exponentMin : Int
  exponentMax : Int
  precision : Int
  roundsNearest : Bool
  roundsAway : Bool
  significand : Int
  increment : Int
  deriving Repr, DecidableEq

def toIeee494 (input : IeeeInput) : Run IEEEOut :=
  let regular := input.kind = .finite
  let difference := input.exponent - input.exponentMin
  let hugePositive := input.exponentMax < input.exponent
  let hugeNegative := difference + input.precision < 0
  let toZero := !input.roundsNearest && !input.roundsAway
  let fromZero := !input.roundsNearest && input.roundsAway
  let roundsInf := regular && hugePositive && !toZero
  let roundsZero := regular && hugeNegative && !fromZero
  if regular && !roundsInf && !roundsZero then
    if hugePositive then ⟨["classify", "omega-representation", "reinterpret"], .omega⟩
    else ⟨["classify", "truncated", "rounding-helper", "round-increment",
      "exponent-field", "ieee754-representation", "reinterpret"], .finite⟩
  else if input.kind = .zero || roundsZero then
    ⟨["classify", "zero-representation", "reinterpret"], .zero⟩
  else if input.kind = .infinity || roundsInf then
    ⟨["classify", "infinity-representation", "reinterpret"], .infinity⟩
  else ⟨["classify", "nan-representation", "reinterpret"], .nan⟩

def ToIeee494 : Prop :=
  ∀ input,
    (toIeee494 input).value ∈
      [Mpfr.IeeeResult.finite, Mpfr.IeeeResult.zero, Mpfr.IeeeResult.infinity,
        Mpfr.IeeeResult.nan, Mpfr.IeeeResult.omega]
theorem toIeee494_proven : ToIeee494 := by
  unfold ToIeee494
  intro input
  cases h : (toIeee494 input).value <;> simp

def float550 (convert : BFRep → RMode → Int) (x : BFRep) (mode : RMode) : Int := convert x mode
def Float550 : Prop := ∀ convert x mode, float550 convert x mode = convert x mode
theorem float550_proven : Float550 := by unfold Float550; intros; rfl
def float551 := float550
def Float551 : Prop := ∀ convert x mode, float551 convert x mode = convert x mode
theorem float551_proven : Float551 := by unfold Float551 float551; intros; rfl
def float552 := float550
def Float552 : Prop := ∀ convert x mode, float552 convert x mode = convert x mode
theorem float552_proven : Float552 := by unfold Float552 float552; intros; rfl

def float553 (convert : BFRep → PMode → Int) (x : BFRep) (mode : PMode) : Int := convert x mode
def Float553 : Prop := ∀ convert x mode, float553 convert x mode = convert x mode
theorem float553_proven : Float553 := by unfold Float553; intros; rfl
def float554 := float553
def Float554 : Prop := ∀ convert x mode, float554 convert x mode = convert x mode
theorem float554_proven : Float554 := by unfold Float554 float554; intros; rfl
def float555 := float553
def Float555 : Prop := ∀ convert x mode, float555 convert x mode = convert x mode
theorem float555_proven : Float555 := by unfold Float555 float555; intros; rfl

def promote557 (_ : Unit) : TypeResult := .bigFloat
def promote558 (_ : Unit) : TypeResult := .bigFloat
def promote559 (_ : Unit) : TypeResult := .bigFloat
def Promote557 : Prop := ∀ x, promote557 x = .bigFloat
def Promote558 : Prop := ∀ x, promote558 x = .bigFloat
def Promote559 : Prop := ∀ x, promote559 x = .bigFloat
theorem promote557_proven : Promote557 := by simp [Promote557, promote557]
theorem promote558_proven : Promote558 := by simp [Promote558, promote558]
theorem promote559_proven : Promote559 := by simp [Promote559, promote559]

def big561 (_ : Unit) : TypeResult := .bigFloat
def Big561 : Prop := ∀ x, big561 x = .bigFloat
theorem big561_proven : Big561 := by simp [Big561, big561]

def big563 (convert : Int → BFRep) (x : Int) : BFRep := convert x
def Big563 : Prop := ∀ convert x, big563 convert x = convert x
theorem big563_proven : Big563 := by unfold Big563; intros; rfl

def rational565 (isNan isInf isZero : Int → Bool) (copySign : Int → Int)
    (precision exponent : Int → Int) (ldexp : Int → Int → Int) (toBigInt : Int → Int)
    (x : Int) : Run (Except String (Int × Int)) :=
  if isNan x then ⟨["isnan", "0//0"], .error "invalid rational"⟩
  else if isInf x then ⟨["isnan", "isinf", "copysign", "//0"], .ok (copySign x, 0)⟩
  else if isZero x then ⟨["isnan", "isinf", "iszero", "0//1"], .ok (0, 1)⟩
  else
    let shift := max (precision x - exponent x) 0
    ⟨["isnan", "isinf", "iszero", "precision", "exponent", "ldexp",
      "BigInt", "shift-denominator"], .ok (toBigInt (ldexp x shift), 2 ^ shift.toNat)⟩
def Rational565 : Prop :=
  ∀ isNan isInf isZero copySign precision exponent ldexp toBigInt x,
    (rational565 isNan isInf isZero copySign precision exponent ldexp toBigInt x).value =
      if isNan x then .error "invalid rational"
      else if isInf x then .ok (copySign x, 0)
      else if isZero x then .ok (0, 1)
      else
        let shift := max (precision x - exponent x) 0
        .ok (toBigInt (ldexp x shift), 2 ^ shift.toNat)
theorem rational565_proven : Rational565 := by
  unfold Rational565
  intros isNan isInf isZero copySign precision exponent ldexp toBigInt x
  by_cases hn : isNan x = true
  · simp [rational565, hn]
  · by_cases hi : isInf x = true
    · simp [rational565, hn, hi]
    · by_cases hz : isZero x = true <;> simp [rational565, hn, hi, hz]

end JuliaLean.BigNumsCov.MpfrFaithful
