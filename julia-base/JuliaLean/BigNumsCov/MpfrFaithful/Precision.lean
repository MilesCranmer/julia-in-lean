import JuliaLean.BigNumsCov.MpfrFaithful.Prelude

namespace JuliaLean.BigNumsCov.MpfrFaithful

/-! `base/mpfr.jl:1041-1219`. -/

def precision1041 (getPrecision : BFRep → Int) (x : BFRep) : Run Int :=
  ⟨["mpfr_get_prec"], getPrecision x⟩
def Precision1041 : Prop := ∀ getPrecision x,
  (precision1041 getPrecision x).value = getPrecision x
theorem precision1041_proven : Precision1041 := by unfold Precision1041; intros; rfl

def precision1044 (precisionBase : BFRep → Int → Int) (x : BFRep) (base : Int) : Int :=
  precisionBase x base
def Precision1044 : Prop := ∀ precisionBase x base,
  precision1044 precisionBase x base = precisionBase x base
theorem precision1044_proven : Precision1044 := by unfold Precision1044; intros; rfl

def convertPrecision1047 (log2 : Int → Int) (ceilInt : Int → Int)
    (precision base : Int) : Run Int :=
  if base = 2 then ⟨["base==2"], precision⟩
  else ⟨["base==2", "log2(base)", "precision*log2", "ceil(Int)"],
    ceilInt (precision * log2 base)⟩
def ConvertPrecision1047 : Prop := ∀ log2 ceilInt precision base,
  (convertPrecision1047 log2 ceilInt precision base).value =
    if base = 2 then precision else ceilInt (precision * log2 base)
theorem convertPrecision1047_proven : ConvertPrecision1047 := by
  unfold ConvertPrecision1047
  intros log2 ceilInt precision base
  by_cases h : base = 2 <;> simp [convertPrecision1047, h]

def typePrecision1050 (scopedValue : Option Int) (defaultValue : Int) : Run Int :=
  ⟨["ScopedValues.get(CURRENT_PRECISION)", "something(DEFAULT_PRECISION)", "Int"],
    scopedValue.getD defaultValue⟩
def TypePrecision1050 : Prop := ∀ scopedValue defaultValue,
  (typePrecision1050 scopedValue defaultValue).value = scopedValue.getD defaultValue
theorem typePrecision1050_proven : TypePrecision1050 := by unfold TypePrecision1050; intros; rfl

def setprecision1069 (convert : Int → Int → Int) (_oldValue precision base : Int) :
    Run (Except String (Int × Int)) :=
  if base ≤ 1 then ⟨["base-check", "DomainError(base)"], .error "base"⟩
  else if precision ≤ 0 then
    ⟨["base-check", "precision-check", "DomainError(precision)"], .error "precision"⟩
  else ⟨["base-check", "precision-check", "convert-precision", "assign-default"],
    .ok (precision, convert precision base)⟩
def Setprecision1069 : Prop := ∀ convert oldValue precision base,
  (setprecision1069 convert oldValue precision base).value =
    if base ≤ 1 then .error "base"
    else if precision ≤ 0 then .error "precision"
    else .ok (precision, convert precision base)
theorem setprecision1069_proven : Setprecision1069 := by
  unfold Setprecision1069
  intros convert oldValue precision base
  by_cases hb : base ≤ 1
  · simp [setprecision1069, hb]
  · by_cases hp : precision ≤ 0 <;> simp [setprecision1069, hb, hp]

def setprecision1076 (setter : Int → Int → Except String (Int × Int))
    (precision base : Int) : Except String (Int × Int) := setter precision base
def Setprecision1076 : Prop := ∀ setter precision base,
  setprecision1076 setter precision base = setter precision base
theorem setprecision1076_proven : Setprecision1076 := by unfold Setprecision1076; intros; rfl

def maxint1078 (toBigFloat : Int → BFRep) (precision : BFRep → Int)
    (power : BFRep → Int → BFRep) (x : BFRep) : Run BFRep :=
  ⟨["BigFloat(2)", "precision(x)", "power"], power (toBigFloat 2) (precision x)⟩
def Maxint1078 : Prop := ∀ toBigFloat precision power x,
  (maxint1078 toBigFloat precision power x).value = power (toBigFloat 2) (precision x)
theorem maxint1078_proven : Maxint1078 := by unfold Maxint1078; intros; rfl

def maxint1079 (toBigFloat : Int → BFRep) (precision : Unit → Int)
    (power : BFRep → Int → BFRep) : Run BFRep :=
  ⟨["BigFloat(2)", "precision(BigFloat)", "power"], power (toBigFloat 2) (precision ())⟩
def Maxint1079 : Prop := ∀ toBigFloat precision power,
  (maxint1079 toBigFloat precision power).value = power (toBigFloat 2) (precision ())
theorem maxint1079_proven : Maxint1079 := by unfold Maxint1079; intros; rfl

def copysign1081 (allocate : Unit → BFRep)
    (copySign : BFRep → BFRep → BFRep → BFRep) (x y : BFRep) : Run BFRep :=
  ⟨["BigFloat()", "mpfr_copysign(rounding_raw)"], copySign (allocate ()) x y⟩
def Copysign1081 : Prop := ∀ allocate copySign x y,
  (copysign1081 allocate copySign x y).value = copySign (allocate ()) x y
theorem copysign1081_proven : Copysign1081 := by unfold Copysign1081; intros; rfl

def exponent1087 (isZero isFinite : BFRep → Bool) (getExponent : BFRep → Int)
    (x : BFRep) : Run (Except String Int) :=
  if isZero x || !isFinite x then
    ⟨["iszero", "isfinite", "DomainError"], .error "DomainError"⟩
  else ⟨["iszero", "isfinite", "mpfr_get_exp", "subtract-one"], .ok (getExponent x - 1)⟩
def Exponent1087 : Prop := ∀ isZero isFinite getExponent x,
  (exponent1087 isZero isFinite getExponent x).value =
    if isZero x || !isFinite x then .error "DomainError" else .ok (getExponent x - 1)
theorem exponent1087_proven : Exponent1087 := by
  unfold Exponent1087
  intros
  simp [exponent1087]
  split <;> rfl

def frexp1095 (allocate : Unit → BFRep)
    (frexp : BFRep → BFRep → BFRep × Int) (x : BFRep) : Run (BFRep × Int) :=
  let output := allocate ()
  ⟨["BigFloat()", "Ref{Clong}()", "mpfr_frexp", "read-exponent-ref"], frexp output x⟩
def Frexp1095 : Prop := ∀ allocate frexp x,
  (frexp1095 allocate frexp x).value = frexp (allocate ()) x
theorem frexp1095_proven : Frexp1095 := by unfold Frexp1095; intros; rfl

def significand1102 (allocate : Unit → BFRep)
    (frexp : BFRep → BFRep → BFRep × Int) (multiply : BFRep → Int → BFRep)
    (x : BFRep) : Run BFRep :=
  let output := (frexp (allocate ()) x).1
  ⟨["BigFloat()", "Ref{Clong}()", "mpfr_frexp", "mpfr_mul_si(2)"], multiply output 2⟩
def Significand1102 : Prop := ∀ allocate frexp multiply x,
  (significand1102 allocate frexp multiply x).value = multiply (frexp (allocate ()) x).1 2
theorem significand1102_proven : Significand1102 := by unfold Significand1102; intros; rfl

def round1121 (allocate : Unit → BFRep) (operation : BFRep → BFRep → BFRep)
    (x : BFRep) : Run BFRep :=
  ⟨["BigFloat()", "selected-mpfr-rounding-function"], operation (allocate ()) x⟩
def Round1121 : Prop := ∀ allocate operation x,
  (round1121 allocate operation x).value = operation (allocate ()) x
theorem round1121_proven : Round1121 := by unfold Round1121; intros; rfl

def isinf1129 (x : BFRep) (infExponent : Int) : Bool := x.exponent = infExponent
def Isinf1129 : Prop := ∀ x infExponent, isinf1129 x infExponent = true ↔ x.exponent = infExponent
theorem isinf1129_proven : Isinf1129 := by simp [Isinf1129, isinf1129]

def isnan1133 (x : BFRep) (nanExponent : Int) : Bool := x.exponent = nanExponent
def Isnan1133 : Prop := ∀ x nanExponent, isnan1133 x nanExponent = true ↔ x.exponent = nanExponent
theorem isnan1133_proven : Isnan1133 := by simp [Isnan1133, isnan1133]

def iszero1141 (x : BFRep) (zeroExponent : Int) : Bool := x.exponent = zeroExponent
def Iszero1141 : Prop := ∀ x zeroExponent, iszero1141 x zeroExponent = true ↔ x.exponent = zeroExponent
theorem iszero1141_proven : Iszero1141 := by simp [Iszero1141, iszero1141]

def isone1142 (equal : BFRep → Int → Bool) (x : BFRep) : Bool := equal x 1
def Isone1142 : Prop := ∀ equal x, isone1142 equal x = equal x 1
theorem isone1142_proven : Isone1142 := by unfold Isone1142; intros; rfl

def typemax1148 (positiveInfinity : BFRep) (_ : Unit) : BFRep := positiveInfinity
def Typemax1148 : Prop := ∀ value input, typemax1148 value input = value
theorem typemax1148_proven : Typemax1148 := by unfold Typemax1148; intros; rfl

def typemin1149 (negativeInfinity : BFRep) (_ : Unit) : BFRep := negativeInfinity
def Typemin1149 : Prop := ∀ value input, typemin1149 value input = value
theorem typemin1149_proven : Typemin1149 := by unfold Typemin1149; intros; rfl

def nextfloat1151 (signBit : Int → Bool) (absolute : Int → Int)
    (previous : BFRep → Int → BFRep) (nextAbove : BFRep → BFRep)
    (x : BFRep) (count : Int) : Run BFRep :=
  if signBit count then ⟨["signbit(n)", "abs(n)", "prevfloat!(x,abs(n))"],
    previous x (absolute count)⟩
  else ⟨["signbit(n)", "for 1:n mpfr_nextabove"],
    (List.range count.toNat).foldl (fun value _ => nextAbove value) x⟩
def Nextfloat1151 : Prop := ∀ signBit absolute previous nextAbove x count,
  (nextfloat1151 signBit absolute previous nextAbove x count).value =
    if signBit count then previous x (absolute count)
    else (List.range count.toNat).foldl (fun value _ => nextAbove value) x
theorem nextfloat1151_proven : Nextfloat1151 := by
  unfold Nextfloat1151
  intros signBit absolute previous nextAbove x count
  by_cases h : signBit count = true <;> simp [nextfloat1151, h]

def prevfloat1159 (signBit : Int → Bool) (absolute : Int → Int)
    (next : BFRep → Int → BFRep) (nextBelow : BFRep → BFRep)
    (x : BFRep) (count : Int) : Run BFRep :=
  if signBit count then ⟨["signbit(n)", "abs(n)", "nextfloat!(x,abs(n))"],
    next x (absolute count)⟩
  else ⟨["signbit(n)", "for 1:n mpfr_nextbelow"],
    (List.range count.toNat).foldl (fun value _ => nextBelow value) x⟩
def Prevfloat1159 : Prop := ∀ signBit absolute next nextBelow x count,
  (prevfloat1159 signBit absolute next nextBelow x count).value =
    if signBit count then next x (absolute count)
    else (List.range count.toNat).foldl (fun value _ => nextBelow value) x
theorem prevfloat1159_proven : Prevfloat1159 := by
  unfold Prevfloat1159
  intros signBit absolute next nextBelow x count
  by_cases h : signBit count = true <;> simp [prevfloat1159, h]

def nextfloat1167 (duplicate : BFRep → BFRep) (nextMut : BFRep → Int → BFRep)
    (x : BFRep) (count : Int) : Run BFRep :=
  if count = 0 then ⟨["n==0"], x⟩
  else ⟨["n==0", "_duplicate", "nextfloat!"], nextMut (duplicate x) count⟩
def Nextfloat1167 : Prop := ∀ duplicate nextMut x count,
  (nextfloat1167 duplicate nextMut x count).value =
    if count = 0 then x else nextMut (duplicate x) count
theorem nextfloat1167_proven : Nextfloat1167 := by
  unfold Nextfloat1167
  intros duplicate nextMut x count
  by_cases h : count = 0 <;> simp [nextfloat1167, h]

def prevfloat1168 (duplicate : BFRep → BFRep) (prevMut : BFRep → Int → BFRep)
    (x : BFRep) (count : Int) : Run BFRep :=
  if count = 0 then ⟨["n==0"], x⟩
  else ⟨["n==0", "_duplicate", "prevfloat!"], prevMut (duplicate x) count⟩
def Prevfloat1168 : Prop := ∀ duplicate prevMut x count,
  (prevfloat1168 duplicate prevMut x count).value =
    if count = 0 then x else prevMut (duplicate x) count
theorem prevfloat1168_proven : Prevfloat1168 := by
  unfold Prevfloat1168
  intros duplicate prevMut x count
  by_cases h : count = 0 <;> simp [prevfloat1168, h]

def eps1170 (toBigFloat : Int → BFRep) (next : BFRep → BFRep)
    (subtract : BFRep → BFRep → BFRep) : BFRep :=
  let one := toBigFloat 1
  subtract (next one) one
def Eps1170 : Prop := ∀ toBigFloat next subtract,
  eps1170 toBigFloat next subtract = subtract (next (toBigFloat 1)) (toBigFloat 1)
theorem eps1170_proven : Eps1170 := by unfold Eps1170; intros; rfl

def floatmin1172 (zero : Unit → BFRep) (next : BFRep → BFRep) : BFRep := next (zero ())
def Floatmin1172 : Prop := ∀ zero next, floatmin1172 zero next = next (zero ())
theorem floatmin1172_proven : Floatmin1172 := by unfold Floatmin1172; intros; rfl

def floatmax1173 (infinity : Unit → BFRep) (previous : BFRep → BFRep) : BFRep := previous (infinity ())
def Floatmax1173 : Prop := ∀ infinity previous, floatmax1173 infinity previous = previous (infinity ())
theorem floatmax1173_proven : Floatmax1173 := by unfold Floatmax1173; intros; rfl

def setprecision1214 (convert : Int → Int → Int) (withScoped : Int → (Unit → Int) → Int)
    (callback : Unit → Int) (precision base : Int) : Run Int :=
  let converted := convert precision base
  ⟨["convert-precision", "ScopedValue-install", "callback", "ScopedValue-restore"],
    withScoped converted callback⟩
def Setprecision1214 : Prop := ∀ convert withScoped callback precision base,
  (setprecision1214 convert withScoped callback precision base).value =
    withScoped (convert precision base) callback
theorem setprecision1214_proven : Setprecision1214 := by unfold Setprecision1214; intros; rfl

structure MethodError1217 where
  functionName : String
  arguments : List Int
  deriving Repr, DecidableEq

def setprecision1217 (callback : Int) (slurp : List Int) : Except MethodError1217 Int :=
  .error { functionName := "setprecision", arguments := callback :: slurp }
def Setprecision1217 : Prop := ∀ callback slurp,
  setprecision1217 callback slurp =
    .error { functionName := "setprecision", arguments := callback :: slurp }
theorem setprecision1217_proven : Setprecision1217 := by unfold Setprecision1217; intros; rfl

def setprecision1219 (withScoped : (Unit → Int) → Int → Int → Int)
    (callback : Unit → Int) (precision base : Int) : Int := withScoped callback precision base
def Setprecision1219 : Prop := ∀ withScoped callback precision base,
  setprecision1219 withScoped callback precision base = withScoped callback precision base
theorem setprecision1219_proven : Setprecision1219 := by unfold Setprecision1219; intros; rfl

end JuliaLean.BigNumsCov.MpfrFaithful
