import JuliaLean.BigNumsCov.MpfrFaithful.Prelude

namespace JuliaLean.BigNumsCov.MpfrFaithful

/-! Hollow mathematical methods in `base/mpfr.jl:781-985`. -/

def sqrt781 (isNan : BFRep → Bool) (allocate : Unit → BFRep)
    (sqrtPrimitive : BFRep → BFRep → BFRep) (x : BFRep) : Run (Except String BFRep) :=
  if isNan x then ⟨["isnan(input)"], .ok x⟩
  else
    let output := sqrtPrimitive (allocate ()) x
    if isNan output then
      ⟨["isnan(input)", "BigFloat()", "mpfr_sqrt", "isnan(output)", "DomainError"],
        .error "DomainError"⟩
    else ⟨["isnan(input)", "BigFloat()", "mpfr_sqrt", "isnan(output)"], .ok output⟩
def Sqrt781 : Prop :=
  ∀ isNan allocate sqrtPrimitive x,
    (sqrt781 isNan allocate sqrtPrimitive x).value =
      if isNan x then .ok x
      else
        let output := sqrtPrimitive (allocate ()) x
        if isNan output then .error "DomainError" else .ok output
theorem sqrt781_proven : Sqrt781 := by
  unfold Sqrt781
  intros isNan allocate sqrtPrimitive x
  by_cases hi : isNan x = true
  · simp [sqrt781, hi]
  · by_cases ho : isNan (sqrtPrimitive (allocate ()) x) = true <;>
      simp [sqrt781, hi, ho]

def sqrt789 (toBigFloat : Int → BFRep) (sqrtValue : BFRep → Except String BFRep)
    (x : Int) : Run (Except String BFRep) :=
  ⟨["BigFloat(x)", "sqrt(BigFloat)"], sqrtValue (toBigFloat x)⟩
def Sqrt789 : Prop :=
  ∀ toBigFloat sqrtValue x,
    (sqrt789 toBigFloat sqrtValue x).value = sqrtValue (toBigFloat x)
theorem sqrt789_proven : Sqrt789 := by unfold Sqrt789; intros; rfl

def power815 (fitsClong : Int → Bool) (toClong toBigInt : Int → Int)
    (powClong powBigInt : BFRep → Int → BFRep) (x : BFRep) (exponent : Int) : Run BFRep :=
  if fitsClong exponent then
    ⟨["Clong-range-check", "Clong(y)", "pow-Clong"], powClong x (toClong exponent)⟩
  else ⟨["Clong-range-check", "BigInt(y)", "pow-BigInt"], powBigInt x (toBigInt exponent)⟩
def Power815 : Prop :=
  ∀ fits toClong toBigInt powClong powBigInt x exponent,
    (power815 fits toClong toBigInt powClong powBigInt x exponent).value =
      if fits exponent then powClong x (toClong exponent) else powBigInt x (toBigInt exponent)
theorem power815_proven : Power815 := by
  unfold Power815
  intros fits toClong toBigInt powClong powBigInt x exponent
  by_cases h : fits exponent = true <;> simp [power815, h]

def power816 (fitsCulong : Int → Bool) (toCulong toBigInt : Int → Int)
    (powCulong powBigInt : BFRep → Int → BFRep) (x : BFRep) (exponent : Int) : Run BFRep :=
  if fitsCulong exponent then
    ⟨["Culong-range-check", "Culong(y)", "pow-Culong"], powCulong x (toCulong exponent)⟩
  else ⟨["Culong-range-check", "BigInt(y)", "pow-BigInt"], powBigInt x (toBigInt exponent)⟩
def Power816 : Prop :=
  ∀ fits toCulong toBigInt powCulong powBigInt x exponent,
    (power816 fits toCulong toBigInt powCulong powBigInt x exponent).value =
      if fits exponent then powCulong x (toCulong exponent) else powBigInt x (toBigInt exponent)
theorem power816_proven : Power816 := by
  unfold Power816
  intros fits toCulong toBigInt powCulong powBigInt x exponent
  by_cases h : fits exponent = true <;> simp [power816, h]

def sincosFast826 (allocate : Unit → BFRep)
    (sinCos : BFRep → BFRep → BFRep → BFRep × BFRep) (value : BFRep) : Run (BFRep × BFRep) :=
  let sine := allocate ()
  let cosine := allocate ()
  ⟨["BigFloat(s)", "BigFloat(c)", "mpfr_sin_cos"], sinCos sine cosine value⟩
def SincosFast826 : Prop :=
  ∀ allocate sinCos value,
    (sincosFast826 allocate sinCos value).value = sinCos (allocate ()) (allocate ()) value
theorem sincosFast826_proven : SincosFast826 := by unfold SincosFast826; intros; rfl

def sincos832 (fast : BFRep → BFRep × BFRep) (value : BFRep) : BFRep × BFRep := fast value
def Sincos832 : Prop := ∀ fast value, sincos832 fast value = fast value
theorem sincos832_proven : Sincos832 := by unfold Sincos832; intros; rfl

def bigLn2835 (allocate : Unit → BFRep) (constant : BFRep → BFRep) : Run BFRep :=
  ⟨["BigFloat()", "mpfr_const_log2(rounding_raw)"], constant (allocate ())⟩
def BigLn2835 : Prop := ∀ allocate constant, (bigLn2835 allocate constant).value = constant (allocate ())
theorem bigLn2835_proven : BigLn2835 := by unfold BigLn2835; intros; rfl

def ldexp841 (allocate : Unit → BFRep) (multiply : BFRep → BFRep → Int → BFRep)
    (x : BFRep) (exponent : Int) : Run BFRep :=
  ⟨["BigFloat()", "mpfr_mul_2si(rounding_raw)"], multiply (allocate ()) x exponent⟩
def Ldexp841 : Prop := ∀ allocate multiply x exponent,
  (ldexp841 allocate multiply x exponent).value = multiply (allocate ()) x exponent
theorem ldexp841_proven : Ldexp841 := by unfold Ldexp841; intros; rfl

def ldexp846 (allocate : Unit → BFRep) (multiply : BFRep → BFRep → Int → BFRep)
    (x : BFRep) (exponent : Int) : Run BFRep :=
  ⟨["BigFloat()", "mpfr_mul_2ui(rounding_raw)"], multiply (allocate ()) x exponent⟩
def Ldexp846 : Prop := ∀ allocate multiply x exponent,
  (ldexp846 allocate multiply x exponent).value = multiply (allocate ()) x exponent
theorem ldexp846_proven : Ldexp846 := by unfold Ldexp846; intros; rfl

def ldexp851 (convert : Int → Int) (ldexp : BFRep → Int → BFRep)
    (x : BFRep) (exponent : Int) : BFRep := ldexp x (convert exponent)
def Ldexp851 : Prop := ∀ convert ldexp x exponent, ldexp851 convert ldexp x exponent = ldexp x (convert exponent)
theorem ldexp851_proven : Ldexp851 := by unfold Ldexp851; intros; rfl

def ldexp852 (convert : Int → Int) (ldexp : BFRep → Int → BFRep)
    (x : BFRep) (exponent : Int) : BFRep := ldexp x (convert exponent)
def Ldexp852 : Prop := ∀ convert ldexp x exponent, ldexp852 convert ldexp x exponent = ldexp x (convert exponent)
theorem ldexp852_proven : Ldexp852 := by unfold Ldexp852; intros; rfl

def ldexp853 (toBigFloat : Int → BFRep) (exp2 : BFRep → BFRep)
    (multiply : BFRep → BFRep → BFRep) (x : BFRep) (exponent : Int) : BFRep :=
  multiply x (exp2 (toBigFloat exponent))
def Ldexp853 : Prop := ∀ toBigFloat exp2 multiply x exponent,
  ldexp853 toBigFloat exp2 multiply x exponent = multiply x (exp2 (toBigFloat exponent))
theorem ldexp853_proven : Ldexp853 := by unfold Ldexp853; intros; rfl

def factorial855 (lessZero isInteger : BFRep → Bool) (toCulong : BFRep → Int)
    (allocate : Unit → BFRep) (factorial : BFRep → Int → BFRep) (x : BFRep) :
    Run (Except String BFRep) :=
  if lessZero x || !isInteger x then
    ⟨["x<0", "isinteger", "DomainError"], .error "DomainError"⟩
  else
    let scalar := toCulong x
    ⟨["x<0", "isinteger", "convert(Culong,x)", "BigFloat()", "mpfr_fac_ui"],
      .ok (factorial (allocate ()) scalar)⟩
def Factorial855 : Prop := ∀ lessZero isInteger toCulong allocate factorial x,
  (factorial855 lessZero isInteger toCulong allocate factorial x).value =
    if lessZero x || !isInteger x then .error "DomainError"
    else .ok (factorial (allocate ()) (toCulong x))
theorem factorial855_proven : Factorial855 := by
  unfold Factorial855
  intros
  simp [factorial855]
  split <;> rfl

def logarithm872 (negative : BFRep → Bool) (allocate : Unit → BFRep)
    (logarithm : BFRep → BFRep → BFRep) (x : BFRep) : Run (Except String BFRep) :=
  if negative x then ⟨["x<0", "DomainError"], .error "DomainError"⟩
  else ⟨["x<0", "BigFloat()", "mpfr_log(rounding_raw)"],
    .ok (logarithm (allocate ()) x)⟩
def Logarithm872 : Prop := ∀ negative allocate logarithm x,
  (logarithm872 negative allocate logarithm x).value =
    if negative x then .error "DomainError" else .ok (logarithm (allocate ()) x)
theorem logarithm872_proven : Logarithm872 := by
  unfold Logarithm872
  intros negative allocate logarithm x
  by_cases h : negative x = true <;> simp [logarithm872, h]

def log1p884 (belowMinusOne : BFRep → Bool) (allocate : Unit → BFRep)
    (log1p : BFRep → BFRep → BFRep) (x : BFRep) : Run (Except String BFRep) :=
  if belowMinusOne x then ⟨["x<-1", "DomainError"], .error "DomainError"⟩
  else ⟨["x<-1", "BigFloat()", "mpfr_log1p(rounding_raw)"], .ok (log1p (allocate ()) x)⟩
def Log1p884 : Prop := ∀ below allocate log1p x,
  (log1p884 below allocate log1p x).value =
    if below x then .error "DomainError" else .ok (log1p (allocate ()) x)
theorem log1p884_proven : Log1p884 := by
  unfold Log1p884
  intros below allocate log1p x
  by_cases h : below x = true <;> simp [log1p884, h]

def minmax897 (isNan : BFRep → Bool) (isLess : BFRep → BFRep → Bool)
    (x y : BFRep) : Run (BFRep × BFRep) :=
  if isNan x then ⟨["isnan(x)"], (x, x)⟩
  else if isNan y then ⟨["isnan(x)", "isnan(y)"], (y, y)⟩
  else if isLess x y then ⟨["isnan(x)", "isnan(y)", "_isless(x,y)"], (x, y)⟩
  else ⟨["isnan(x)", "isnan(y)", "_isless(x,y)"], (y, x)⟩
def Minmax897 : Prop := ∀ isNan isLess x y,
  (minmax897 isNan isLess x y).value =
    if isNan x then (x, x) else if isNan y then (y, y)
    else if isLess x y then (x, y) else (y, x)
theorem minmax897_proven : Minmax897 := by
  unfold Minmax897
  intros isNan isLess x y
  by_cases hx : isNan x = true
  · simp [minmax897, hx]
  · by_cases hy : isNan y = true
    · simp [minmax897, hx, hy]
    · by_cases hl : isLess x y = true <;> simp [minmax897, hx, hy, hl]

def extrema903 (isNan : BFRep → Bool) (isLess : BFRep → BFRep → Bool)
    (x y : BFRep × BFRep) : Run (BFRep × BFRep) :=
  if isNan x.1 then ⟨["destructure", "isnan(x1)"], x⟩
  else if isNan y.1 then ⟨["destructure", "isnan(x1)", "isnan(y1)"], y⟩
  else
    let low := if isLess x.1 y.1 then x.1 else y.1
    let high := if isLess x.2 y.2 then y.2 else x.2
    ⟨["destructure", "isnan(x1)", "isnan(y1)", "_isless(x1,y1)", "_isless(x2,y2)"],
      (low, high)⟩
def Extrema903 : Prop := ∀ isNan isLess x y,
  (extrema903 isNan isLess x y).value =
    if isNan x.1 then x else if isNan y.1 then y
    else (if isLess x.1 y.1 then x.1 else y.1,
      if isLess x.2 y.2 then y.2 else x.2)
theorem extrema903_proven : Extrema903 := by
  unfold Extrema903
  intros isNan isLess x y
  by_cases hx : isNan x.1 = true
  · simp [extrema903, hx]
  · by_cases hy : isNan y.1 = true
    · simp [extrema903, hx, hy]
    · simp [extrema903, hx, hy]

def modf912 (allocate : Unit → BFRep)
    (modf : BFRep → BFRep → BFRep → BFRep × BFRep) (x : BFRep) : Run (BFRep × BFRep) :=
  let integer := allocate ()
  let fraction := allocate ()
  let result := modf integer fraction x
  ⟨["BigFloat(integer)", "BigFloat(fraction)", "mpfr_modf", "reverse-output-tuple"],
    (result.2, result.1)⟩
def Modf912 : Prop := ∀ allocate modf x,
  (modf912 allocate modf x).value =
    let result := modf (allocate ()) (allocate ()) x
    (result.2, result.1)
theorem modf912_proven : Modf912 := by unfold Modf912; intros; rfl

def rem2pi932 (pi : Unit → BFRep) (toBigFloat : BFRep → BFRep)
    (multiply : Int → BFRep → BFRep) (rem : BFRep → BFRep → PMode → BFRep)
    (x : BFRep) (mode : PMode) : Run BFRep :=
  let modulus := multiply 2 (toBigFloat (pi ()))
  ⟨["pi", "BigFloat(pi)", "2*pi", "rem(x,modulus,r)"], rem x modulus mode⟩
def Rem2pi932 : Prop := ∀ pi toBigFloat multiply rem x mode,
  (rem2pi932 pi toBigFloat multiply rem x mode).value =
    rem x (multiply 2 (toBigFloat (pi ()))) mode
theorem rem2pi932_proven : Rem2pi932 := by unfold Rem2pi932; intros; rfl

def checkedUnary946 (isNan : BFRep → Bool) (allocate : Unit → BFRep)
    (operation : BFRep → BFRep → BFRep) (x : BFRep) : Run (Except String BFRep) :=
  if isNan x then ⟨["isnan(input)"], .ok x⟩
  else
    let output := operation (allocate ()) x
    if isNan output then
      ⟨["isnan(input)", "BigFloat()", "mpfr_op", "isnan(output)", "DomainError"],
        .error "DomainError"⟩
    else ⟨["isnan(input)", "BigFloat()", "mpfr_op", "isnan(output)"], .ok output⟩
def CheckedUnary946 : Prop := ∀ isNan allocate operation x,
  (checkedUnary946 isNan allocate operation x).value =
    if isNan x then .ok x
    else
      let output := operation (allocate ()) x
      if isNan output then .error "DomainError" else .ok output
theorem checkedUnary946_proven : CheckedUnary946 := by
  unfold CheckedUnary946
  intros isNan allocate operation x
  by_cases hi : isNan x = true
  · simp [checkedUnary946, hi]
  · by_cases ho : isNan (operation (allocate ()) x) = true <;>
      simp [checkedUnary946, hi, ho]

def degree966 (isNan : BFRep → Bool) (allocate : Unit → BFRep)
    (operation : BFRep → BFRep → Int → BFRep) (x : BFRep) : Run (Except String BFRep) :=
  if isNan x then ⟨["isnan(input)"], .ok x⟩
  else
    let output := operation (allocate ()) x 360
    if isNan output then
      ⟨["isnan(input)", "BigFloat()", "mpfr_op_u(360)", "isnan(output)", "DomainError"],
        .error "DomainError"⟩
    else ⟨["isnan(input)", "BigFloat()", "mpfr_op_u(360)", "isnan(output)"], .ok output⟩
def Degree966 : Prop := ∀ isNan allocate operation x,
  (degree966 isNan allocate operation x).value =
    if isNan x then .ok x
    else
      let output := operation (allocate ()) x 360
      if isNan output then .error "DomainError" else .ok output
theorem degree966_proven : Degree966 := by
  unfold Degree966
  intros isNan allocate operation x
  by_cases hi : isNan x = true
  · simp [degree966, hi]
  · by_cases ho : isNan (operation (allocate ()) x 360) = true <;>
      simp [degree966, hi, ho]

def degree973 := degree966
def Degree973 : Prop := ∀ isNan allocate operation x,
  (degree973 isNan allocate operation x).value =
    if isNan x then .ok x
    else
      let output := operation (allocate ()) x 360
      if isNan output then .error "DomainError" else .ok output
theorem degree973_proven : Degree973 := by
  unfold Degree973 degree973
  intros isNan allocate operation x
  by_cases hi : isNan x = true
  · simp [degree966, hi]
  · by_cases ho : isNan (operation (allocate ()) x 360) = true <;>
      simp [degree966, hi, ho]

def atand982 (allocate : Unit → BFRep)
    (atan2u : BFRep → BFRep → BFRep → Int → BFRep) (y x : BFRep) : Run BFRep :=
  ⟨["BigFloat()", "mpfr_atan2u(360,rounding_raw)"], atan2u (allocate ()) y x 360⟩
def Atand982 : Prop := ∀ allocate atan2u y x,
  (atand982 allocate atan2u y x).value = atan2u (allocate ()) y x 360
theorem atand982_proven : Atand982 := by unfold Atand982; intros; rfl

end JuliaLean.BigNumsCov.MpfrFaithful
