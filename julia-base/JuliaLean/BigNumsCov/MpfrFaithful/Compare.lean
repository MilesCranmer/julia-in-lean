import JuliaLean.BigNumsCov.MpfrFaithful.Prelude

namespace JuliaLean.BigNumsCov.MpfrFaithful

/-! `base/mpfr.jl:990-1039`. -/

def equal990 (primitive : BFRep → BFRep → Int) (x y : BFRep) : Run Bool :=
  ⟨["mpfr_equal_p"], primitive x y != 0⟩
def Equal990 : Prop := ∀ primitive x y, (equal990 primitive x y).value = (primitive x y != 0)
theorem equal990_proven : Equal990 := by unfold Equal990; intros; rfl

def lessEqual991 (primitive : BFRep → BFRep → Int) (x y : BFRep) : Run Bool :=
  ⟨["mpfr_lessequal_p"], primitive x y != 0⟩
def LessEqual991 : Prop := ∀ primitive x y, (lessEqual991 primitive x y).value = (primitive x y != 0)
theorem lessEqual991_proven : LessEqual991 := by unfold LessEqual991; intros; rfl

def less992 (primitive : BFRep → BFRep → Int) (x y : BFRep) : Run Bool :=
  ⟨["mpfr_less_p"], primitive x y != 0⟩
def Less992 : Prop := ∀ primitive x y, (less992 primitive x y).value = (primitive x y != 0)
theorem less992_proven : Less992 := by unfold Less992; intros; rfl

def cmp994 (isNan : BFRep → Bool) (primitive : BFRep → Int → Int)
    (x : BFRep) (y : Int) : Run Int :=
  if isNan x then ⟨["isnan(x)"], 1⟩
  else ⟨["isnan(x)", "mpfr_cmp_z"], primitive x y⟩
def Cmp994 : Prop := ∀ isNan primitive x y,
  (cmp994 isNan primitive x y).value = if isNan x then 1 else primitive x y
theorem cmp994_proven : Cmp994 := by
  unfold Cmp994
  intros isNan primitive x y
  by_cases h : isNan x = true <;> simp [cmp994, h]

def cmp998 (isNan : BFRep → Bool) (primitive : BFRep → Int → Int)
    (x : BFRep) (y : Int) : Run Int :=
  if isNan x then ⟨["isnan(x)"], 1⟩
  else ⟨["isnan(x)", "mpfr_cmp_si"], primitive x y⟩
def Cmp998 : Prop := ∀ isNan primitive x y,
  (cmp998 isNan primitive x y).value = if isNan x then 1 else primitive x y
theorem cmp998_proven : Cmp998 := by
  unfold Cmp998
  intros isNan primitive x y
  by_cases h : isNan x = true <;> simp [cmp998, h]

def cmp1002 (isNan : BFRep → Bool) (primitive : BFRep → Int → Int)
    (x : BFRep) (y : Int) : Run Int :=
  if isNan x then ⟨["isnan(x)"], 1⟩
  else ⟨["isnan(x)", "mpfr_cmp_ui"], primitive x y⟩
def Cmp1002 : Prop := ∀ isNan primitive x y,
  (cmp1002 isNan primitive x y).value = if isNan x then 1 else primitive x y
theorem cmp1002_proven : Cmp1002 := by
  unfold Cmp1002
  intros isNan primitive x y
  by_cases h : isNan x = true <;> simp [cmp1002, h]

def cmp1006 (toBigInt : Int → Int) (cmp : BFRep → Int → Int) (x : BFRep) (y : Int) : Int :=
  cmp x (toBigInt y)
def Cmp1006 : Prop := ∀ toBigInt cmp x y, cmp1006 toBigInt cmp x y = cmp x (toBigInt y)
theorem cmp1006_proven : Cmp1006 := by unfold Cmp1006; intros; rfl

def cmp1007 (cmp : BFRep → Int → Int) (x : Int) (y : BFRep) : Int := -cmp y x
def Cmp1007 : Prop := ∀ cmp x y, cmp1007 cmp x y = -cmp y x
theorem cmp1007_proven : Cmp1007 := by unfold Cmp1007; intros; rfl

def cmp1009 (isNanBF : BFRep → Bool) (isNanDouble : Int → Bool)
    (primitive : BFRep → Int → Int) (x : BFRep) (y : Int) : Run Int :=
  if isNanBF x then
    if isNanDouble y then ⟨["isnan(x)", "isnan(y)"], 0⟩
    else ⟨["isnan(x)", "isnan(y)"], 1⟩
  else if isNanDouble y then ⟨["isnan(x)", "isnan(y)"], -1⟩
  else ⟨["isnan(x)", "isnan(y)", "mpfr_cmp_d"], primitive x y⟩
def Cmp1009 : Prop := ∀ isNanBF isNanDouble primitive x y,
  (cmp1009 isNanBF isNanDouble primitive x y).value =
    if isNanBF x then if isNanDouble y then 0 else 1
    else if isNanDouble y then -1 else primitive x y
theorem cmp1009_proven : Cmp1009 := by
  unfold Cmp1009
  intros isNanBF isNanDouble primitive x y
  by_cases hx : isNanBF x = true <;> by_cases hy : isNanDouble y = true <;>
    simp [cmp1009, hx, hy]

def cmp1014 (cmp : BFRep → Int → Int) (x : Int) (y : BFRep) : Int := -cmp y x
def Cmp1014 : Prop := ∀ cmp x y, cmp1014 cmp x y = -cmp y x
theorem cmp1014_proven : Cmp1014 := by unfold Cmp1014; intros; rfl

def eq1016 (isNan : BFRep → Bool) (cmp : BFRep → Int → Int) (x : BFRep) (y : Int) : Run Bool :=
  if isNan x then ⟨["isnan(x)"], false⟩ else ⟨["isnan(x)", "cmp(x,y)"], cmp x y = 0⟩
def Eq1016 : Prop := ∀ isNan cmp x y,
  (eq1016 isNan cmp x y).value = (!isNan x && cmp x y = 0)
theorem eq1016_proven : Eq1016 := by unfold Eq1016; intros; simp [eq1016]; split <;> simp_all

def eq1017 (eq : BFRep → Int → Bool) (x : Int) (y : BFRep) : Bool := eq y x
def Eq1017 : Prop := ∀ eq x y, eq1017 eq x y = eq y x
theorem eq1017_proven : Eq1017 := by unfold Eq1017; intros; rfl

def eq1018 (isNanBF : BFRep → Bool) (isNanDouble : Int → Bool)
    (cmp : BFRep → Int → Int) (x : BFRep) (y : Int) : Run Bool :=
  if isNanBF x then ⟨["isnan(x)"], false⟩
  else if isNanDouble y then ⟨["isnan(x)", "isnan(y)"], false⟩
  else ⟨["isnan(x)", "isnan(y)", "cmp(x,y)"], cmp x y = 0⟩
def Eq1018 : Prop := ∀ isNanBF isNanDouble cmp x y,
  (eq1018 isNanBF isNanDouble cmp x y).value =
    (!isNanBF x && !isNanDouble y && cmp x y = 0)
theorem eq1018_proven : Eq1018 := by
  unfold Eq1018
  intros isNanBF isNanDouble cmp x y
  by_cases hx : isNanBF x = true <;> by_cases hy : isNanDouble y = true <;>
    simp [eq1018, hx, hy]

def eq1019 (eq : BFRep → Int → Bool) (x : Int) (y : BFRep) : Bool := eq y x
def Eq1019 : Prop := ∀ eq x y, eq1019 eq x y = eq y x
theorem eq1019_proven : Eq1019 := by unfold Eq1019; intros; rfl

def lt1021 (isNan : BFRep → Bool) (cmp : BFRep → Int → Int) (x : BFRep) (y : Int) : Run Bool :=
  if isNan x then ⟨["isnan(x)"], false⟩ else ⟨["isnan(x)", "cmp(x,y)"], cmp x y < 0⟩
def Lt1021 : Prop := ∀ isNan cmp x y,
  (lt1021 isNan cmp x y).value = (!isNan x && cmp x y < 0)
theorem lt1021_proven : Lt1021 := by unfold Lt1021; intros; simp [lt1021]; split <;> simp_all

def lt1022 (isNan : BFRep → Bool) (cmp : BFRep → Int → Int) (x : Int) (y : BFRep) : Run Bool :=
  if isNan y then ⟨["isnan(y)"], false⟩ else ⟨["isnan(y)", "cmp(y,x)"], cmp y x > 0⟩
def Lt1022 : Prop := ∀ isNan cmp x y,
  (lt1022 isNan cmp x y).value = (!isNan y && cmp y x > 0)
theorem lt1022_proven : Lt1022 := by unfold Lt1022; intros; simp [lt1022]; split <;> simp_all

def lt1023 (isNanBF : BFRep → Bool) (isNanDouble : Int → Bool)
    (cmp : BFRep → Int → Int) (x : BFRep) (y : Int) : Run Bool :=
  if isNanBF x then ⟨["isnan(x)"], false⟩
  else if isNanDouble y then ⟨["isnan(x)", "isnan(y)"], false⟩
  else ⟨["isnan(x)", "isnan(y)", "cmp(x,y)"], cmp x y < 0⟩
def Lt1023 : Prop := ∀ isNanBF isNanDouble cmp x y,
  (lt1023 isNanBF isNanDouble cmp x y).value =
    (!isNanBF x && !isNanDouble y && cmp x y < 0)
theorem lt1023_proven : Lt1023 := by
  unfold Lt1023
  intros isNanBF isNanDouble cmp x y
  by_cases hx : isNanBF x = true <;> by_cases hy : isNanDouble y = true <;>
    simp [lt1023, hx, hy]

def lt1024 (isNanBF : BFRep → Bool) (isNanDouble : Int → Bool)
    (cmp : BFRep → Int → Int) (x : Int) (y : BFRep) : Run Bool :=
  if isNanDouble x then ⟨["isnan(x)"], false⟩
  else if isNanBF y then ⟨["isnan(x)", "isnan(y)"], false⟩
  else ⟨["isnan(x)", "isnan(y)", "cmp(y,x)"], cmp y x > 0⟩
def Lt1024 : Prop := ∀ isNanBF isNanDouble cmp x y,
  (lt1024 isNanBF isNanDouble cmp x y).value =
    (!isNanDouble x && !isNanBF y && cmp y x > 0)
theorem lt1024_proven : Lt1024 := by
  unfold Lt1024
  intros isNanBF isNanDouble cmp x y
  by_cases hx : isNanDouble x = true <;> by_cases hy : isNanBF y = true <;>
    simp [lt1024, hx, hy]

def le1026 (isNan : BFRep → Bool) (cmp : BFRep → Int → Int) (x : BFRep) (y : Int) : Run Bool :=
  if isNan x then ⟨["isnan(x)"], false⟩ else ⟨["isnan(x)", "cmp(x,y)"], cmp x y ≤ 0⟩
def Le1026 : Prop := ∀ isNan cmp x y,
  (le1026 isNan cmp x y).value = (!isNan x && cmp x y ≤ 0)
theorem le1026_proven : Le1026 := by unfold Le1026; intros; simp [le1026]; split <;> simp_all

def le1027 (isNan : BFRep → Bool) (cmp : BFRep → Int → Int) (x : Int) (y : BFRep) : Run Bool :=
  if isNan y then ⟨["isnan(y)"], false⟩ else ⟨["isnan(y)", "cmp(y,x)"], cmp y x ≥ 0⟩
def Le1027 : Prop := ∀ isNan cmp x y,
  (le1027 isNan cmp x y).value = (!isNan y && cmp y x ≥ 0)
theorem le1027_proven : Le1027 := by unfold Le1027; intros; simp [le1027]; split <;> simp_all

def le1028 (isNanBF : BFRep → Bool) (isNanDouble : Int → Bool)
    (cmp : BFRep → Int → Int) (x : BFRep) (y : Int) : Run Bool :=
  if isNanBF x then ⟨["isnan(x)"], false⟩
  else if isNanDouble y then ⟨["isnan(x)", "isnan(y)"], false⟩
  else ⟨["isnan(x)", "isnan(y)", "cmp(x,y)"], cmp x y ≤ 0⟩
def Le1028 : Prop := ∀ isNanBF isNanDouble cmp x y,
  (le1028 isNanBF isNanDouble cmp x y).value =
    (!isNanBF x && !isNanDouble y && cmp x y ≤ 0)
theorem le1028_proven : Le1028 := by
  unfold Le1028
  intros isNanBF isNanDouble cmp x y
  by_cases hx : isNanBF x = true <;> by_cases hy : isNanDouble y = true <;>
    simp [le1028, hx, hy]

def le1029 (isNanBF : BFRep → Bool) (isNanDouble : Int → Bool)
    (cmp : BFRep → Int → Int) (x : Int) (y : BFRep) : Run Bool :=
  if isNanDouble x then ⟨["isnan(x)"], false⟩
  else if isNanBF y then ⟨["isnan(x)", "isnan(y)"], false⟩
  else ⟨["isnan(x)", "isnan(y)", "cmp(y,x)"], cmp y x ≥ 0⟩
def Le1029 : Prop := ∀ isNanBF isNanDouble cmp x y,
  (le1029 isNanBF isNanDouble cmp x y).value =
    (!isNanDouble x && !isNanBF y && cmp y x ≥ 0)
theorem le1029_proven : Le1029 := by
  unfold Le1029
  intros isNanBF isNanDouble cmp x y
  by_cases hx : isNanDouble x = true <;> by_cases hy : isNanBF y = true <;>
    simp [le1029, hx, hy]

def signbit1033 (signBit : Int → Bool) (x : BFRep) : Run Bool :=
  ⟨["getproperty(sign)", "signbit(sign)"], signBit x.sign⟩
def Signbit1033 : Prop := ∀ signBit x, (signbit1033 signBit x).value = signBit x.sign
theorem signbit1033_proven : Signbit1033 := by unfold Signbit1033; intros; rfl

def sign1035 (cmpZero : BFRep → Int) (isNan : BFRep → Bool)
    (negOne posOne : BFRep → BFRep) (x : BFRep) : Run BFRep :=
  let comparison := cmpZero x
  if comparison = 0 || isNan x then ⟨["cmp(x,0)", "isnan(x)"], x⟩
  else if comparison < 0 then ⟨["cmp(x,0)", "isnan(x)", "-one(x)"], negOne x⟩
  else ⟨["cmp(x,0)", "isnan(x)", "one(x)"], posOne x⟩
def Sign1035 : Prop := ∀ cmpZero isNan negOne posOne x,
  (sign1035 cmpZero isNan negOne posOne x).value =
    if cmpZero x = 0 || isNan x then x
    else if cmpZero x < 0 then negOne x else posOne x
theorem sign1035_proven : Sign1035 := by
  unfold Sign1035
  intros cmpZero isNan negOne posOne x
  by_cases hz : cmpZero x = 0 ∨ isNan x = true
  · simp [sign1035, hz]
  · by_cases hn : cmpZero x < 0 <;> simp [sign1035, hz, hn]

end JuliaLean.BigNumsCov.MpfrFaithful
