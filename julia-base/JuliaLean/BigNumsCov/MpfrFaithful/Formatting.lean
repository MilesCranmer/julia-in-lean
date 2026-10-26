import JuliaLean.BigNumsCov.MpfrFaithful.Prelude

namespace JuliaLean.BigNumsCov.MpfrFaithful

/-! `base/mpfr.jl:1221-1332`. -/

def replaceComma1221 : List Char → List Char
  | [] => []
  | ',' :: rest => '.' :: rest
  | char :: rest => char :: replaceComma1221 rest

def stringMpfr1221 (asprintf : BFRep → String → List Char) (toString : List Char → String)
    (x : BFRep) (format : String) : Run String :=
  let bytes := asprintf x format
  let normalized := replaceComma1221 bytes
  ⟨["Ref{Ptr{UInt8}}", "mpfr_asprintf", "read-pointer", "scan-first-comma",
    "unsafe_string", "mpfr_free_str"], toString normalized⟩
def StringMpfr1221 : Prop := ∀ asprintf toString x format,
  (stringMpfr1221 asprintf toString x format).value =
    toString (replaceComma1221 (asprintf x format))
theorem stringMpfr1221_proven : StringMpfr1221 := by unfold StringMpfr1221; intros; rfl

structure ScientificText where
  mantissa : String
  exponent : Int
  hasPoint : Bool
  strippedMantissa : String
  integerPart : String
  fractionalPart : String
  negative : Bool
  deriving Repr, DecidableEq

def prettify1239 (appendPoint ensureZero moveRight moveLeft scientific : ScientificText → String)
    (text : ScientificText) : Run String :=
  let withPoint := if text.hasPoint then text else
    { text with mantissa := appendPoint text, hasPoint := true }
  let normalized := { withPoint with mantissa := withPoint.strippedMantissa }
  if -5 < normalized.exponent ∧ normalized.exponent < 6 then
    if normalized.exponent = 0 then
      ⟨["split-e", "ensure-point", "rstrip-zero", "ensure-trailing-zero", "parse-exponent"],
        ensureZero normalized⟩
    else if 0 < normalized.exponent then
      ⟨["split-e", "ensure-point", "rstrip-zero", "ensure-trailing-zero", "parse-exponent",
        "split-mantissa", "move-point-right"], moveRight normalized⟩
    else ⟨["split-e", "ensure-point", "rstrip-zero", "ensure-trailing-zero", "parse-exponent",
      "split-mantissa", "strip-sign", "assert-single-integer-digit", "move-point-left"],
      moveLeft normalized⟩
  else ⟨["split-e", "ensure-point", "rstrip-zero", "ensure-trailing-zero", "parse-exponent",
    "scientific-format"], scientific normalized⟩

def Prettify1239 : Prop :=
  ∀ appendPoint ensureZero moveRight moveLeft scientific text,
    (prettify1239 appendPoint ensureZero moveRight moveLeft scientific text).value =
      let withPoint := if text.hasPoint then text else
        { text with mantissa := appendPoint text, hasPoint := true }
      let normalized := { withPoint with mantissa := withPoint.strippedMantissa }
      if -5 < normalized.exponent ∧ normalized.exponent < 6 then
        if normalized.exponent = 0 then ensureZero normalized
        else if 0 < normalized.exponent then moveRight normalized else moveLeft normalized
      else scientific normalized
theorem prettify1239_proven : Prettify1239 := by
  unfold Prettify1239
  intros appendPoint ensureZero moveRight moveLeft scientific text
  by_cases hp : text.hasPoint = true
  · simp [prettify1239, hp]
    by_cases hr : -5 < text.exponent ∧ text.exponent < 6
    · by_cases hz : text.exponent = 0
      · simp [hz]
      · by_cases hs : 0 < text.exponent <;> simp [hr, hz, hs]
    · simp [hr]
  · simp [prettify1239, hp]
    by_cases hr : -5 < text.exponent ∧ text.exponent < 6
    · by_cases hz : text.exponent = 0
      · simp [hz]
      · by_cases hs : 0 < text.exponent <;> simp [hr, hz, hs]
    · simp [hr]

def string1267 (isFinite : BFRep → Bool) (toFloat64 : BFRep → Int)
    (floatString : Int → String) (stringMpfr : BFRep → String → String)
    (prettify : String → String) (x : BFRep) (format : String) : Run String :=
  if isFinite x then
    ⟨["isfinite", "string_mpfr", "prettify"], prettify (stringMpfr x format)⟩
  else ⟨["isfinite", "Float64(x)", "string"], floatString (toFloat64 x)⟩
def String1267 : Prop := ∀ isFinite toFloat64 floatString stringMpfr prettify x format,
  (string1267 isFinite toFloat64 floatString stringMpfr prettify x format).value =
    if isFinite x then prettify (stringMpfr x format) else floatString (toFloat64 x)
theorem string1267_proven : String1267 := by
  unfold String1267
  intros isFinite toFloat64 floatString stringMpfr prettify x format
  by_cases h : isFinite x = true <;> simp [string1267, h]

def string1271 (format : BFRep → String → String) (x : BFRep) : String := format x "%Re"
def String1271 : Prop := ∀ format x, string1271 format x = format x "%Re"
theorem string1271_proven : String1271 := by unfold String1271; intros; rfl

def string1272 (formatString : Int → String) (format : BFRep → String → String)
    (x : BFRep) (digits : Int) : String := format x (formatString digits)
def String1272 : Prop := ∀ formatString format x digits,
  string1272 formatString format x digits = format x (formatString digits)
theorem string1272_proven : String1272 := by unfold String1272; intros; rfl

def string1274 (format : BFRep → String) (x : BFRep) : String := format x
def String1274 : Prop := ∀ format x, string1274 format x = format x
theorem string1274_proven : String1274 := by unfold String1274; intros; rfl

def print1276 (format : BFRep → String) (printTo : Int → String → Int)
    (io : Int) (x : BFRep) : Run Int :=
  ⟨["string(BigFloat)", "print(io,text)"], printTo io (format x)⟩
def Print1276 : Prop := ∀ format printTo io x,
  (print1276 format printTo io x).value = printTo io (format x)
theorem print1276_proven : Print1276 := by unfold Print1276; intros; rfl

def show1277 (getCompact : Int → Bool) (short full : BFRep → String)
    (printTo : Int → String → Int) (io : Int) (x : BFRep) : Run Int :=
  if getCompact io then
    ⟨["get(io,:compact,false)", "_string(x,5)", "print"], printTo io (short x)⟩
  else ⟨["get(io,:compact,false)", "_string(x)", "print"], printTo io (full x)⟩
def Show1277 : Prop := ∀ getCompact short full printTo io x,
  (show1277 getCompact short full printTo io x).value =
    if getCompact io then printTo io (short x) else printTo io (full x)
theorem show1277_proven : Show1277 := by
  unfold Show1277
  intros getCompact short full printTo io x
  by_cases h : getCompact io = true <;> simp [show1277, h]

def setEmax1295 (primitive : Int → Int) (check : Int → Except String Unit)
    (value : Int) : Run (Except String Unit) :=
  ⟨["mpfr_set_emax", "check_exponent_err"], check (primitive value)⟩
def SetEmax1295 : Prop := ∀ primitive check value,
  (setEmax1295 primitive check value).value = check (primitive value)
theorem setEmax1295_proven : SetEmax1295 := by unfold SetEmax1295; intros; rfl

def setEmin1296 (primitive : Int → Int) (check : Int → Except String Unit)
    (value : Int) : Run (Except String Unit) :=
  ⟨["mpfr_set_emin", "check_exponent_err"], check (primitive value)⟩
def SetEmin1296 : Prop := ∀ primitive check value,
  (setEmin1296 primitive check value).value = check (primitive value)
theorem setEmin1296_proven : SetEmin1296 := by unfold SetEmin1296; intros; rfl

def deepcopy1298 (lookupOrInsert : BFRep → (Unit → BFRep) → BFRep)
    (copyWords : List Nat → List Nat) (construct : List Nat → BFRep) (x : BFRep) : Run BFRep :=
  let make := fun _ => construct (copyWords x.words)
  ⟨["get!(stackdict,x)", "copy(getfield(d))", "_BigFloat(copy)"], lookupOrInsert x make⟩
def Deepcopy1298 : Prop := ∀ lookupOrInsert copyWords construct x,
  (deepcopy1298 lookupOrInsert copyWords construct x).value =
    lookupOrInsert x (fun _ => construct (copyWords x.words))
theorem deepcopy1298_proven : Deepcopy1298 := by unfold Deepcopy1298; intros; rfl

def decompose1307 (isNan isInf isZero : BFRep → Bool) (allocateBigInt : Nat → Int)
    (copyLimbs : Int → List Nat → Nat → Int) (x : BFRep) : Run (Int × Int × Int) :=
  if isNan x then ⟨["isnan"], (0, 0, 0)⟩
  else if isInf x then ⟨["isnan", "isinf"], (x.sign, 0, 0)⟩
  else if isZero x then ⟨["isnan", "isinf", "x==0"], (0, 0, x.sign)⟩
  else
    let limbs := (x.precision.toNat + 63) / 64
    let bytes := limbs * 8
    let significand := copyLimbs (allocateBigInt limbs) x.words bytes
    ⟨["isnan", "isinf", "x==0", "BigInt()", "compute-limbs", "realloc2",
      "memcpy", "exponent-minus-bits"], (significand, x.exponent - 8 * bytes, x.sign)⟩
def Decompose1307 : Prop := ∀ isNan isInf isZero allocateBigInt copyLimbs x,
  (decompose1307 isNan isInf isZero allocateBigInt copyLimbs x).value =
    if isNan x then (0, 0, 0)
    else if isInf x then (x.sign, 0, 0)
    else if isZero x then (0, 0, x.sign)
    else
      let limbs := (x.precision.toNat + 63) / 64
      let bytes := limbs * 8
      (copyLimbs (allocateBigInt limbs) x.words bytes, x.exponent - 8 * bytes, x.sign)
theorem decompose1307_proven : Decompose1307 := by
  unfold Decompose1307
  intros isNan isInf isZero allocateBigInt copyLimbs x
  by_cases hn : isNan x = true
  · simp [decompose1307, hn]
  · by_cases hi : isInf x = true
    · simp [decompose1307, hn, hi]
    · by_cases hz : isZero x = true <;> simp [decompose1307, hn, hi, hz]

def clearFlags1326 (primitive : Unit → Unit) : Run Unit :=
  let value := primitive ()
  ⟨["mpfr_clear_flags"], value⟩
def ClearFlags1326 : Prop := ∀ primitive, (clearFlags1326 primitive).value = primitive ()
theorem clearFlags1326_proven : ClearFlags1326 := by unfold ClearFlags1326; intros; rfl

def hadUnderflow1327 (primitive : Unit → Int) : Run Bool := ⟨["mpfr_underflow_p"], primitive () != 0⟩
def HadUnderflow1327 : Prop := ∀ primitive, (hadUnderflow1327 primitive).value = (primitive () != 0)
theorem hadUnderflow1327_proven : HadUnderflow1327 := by unfold HadUnderflow1327; intros; rfl

def hadOverflow1328 (primitive : Unit → Int) : Run Bool := ⟨["mpfr_overflow_p"], primitive () != 0⟩
def HadOverflow1328 : Prop := ∀ primitive, (hadOverflow1328 primitive).value = (primitive () != 0)
theorem hadOverflow1328_proven : HadOverflow1328 := by unfold HadOverflow1328; intros; rfl

def hadDivzero1329 (primitive : Unit → Int) : Run Bool := ⟨["mpfr_divby0_p"], primitive () != 0⟩
def HadDivzero1329 : Prop := ∀ primitive, (hadDivzero1329 primitive).value = (primitive () != 0)
theorem hadDivzero1329_proven : HadDivzero1329 := by unfold HadDivzero1329; intros; rfl

def hadNan1330 (primitive : Unit → Int) : Run Bool := ⟨["mpfr_nanflag_p"], primitive () != 0⟩
def HadNan1330 : Prop := ∀ primitive, (hadNan1330 primitive).value = (primitive () != 0)
theorem hadNan1330_proven : HadNan1330 := by unfold HadNan1330; intros; rfl

def hadInexact1331 (primitive : Unit → Int) : Run Bool := ⟨["mpfr_inexflag_p"], primitive () != 0⟩
def HadInexact1331 : Prop := ∀ primitive, (hadInexact1331 primitive).value = (primitive () != 0)
theorem hadInexact1331_proven : HadInexact1331 := by unfold HadInexact1331; intros; rfl

def hadRange1332 (primitive : Unit → Int) : Run Bool := ⟨["mpfr_erangeflag_p"], primitive () != 0⟩
def HadRange1332 : Prop := ∀ primitive, (hadRange1332 primitive).value = (primitive () != 0)
theorem hadRange1332_proven : HadRange1332 := by unfold HadRange1332; intros; rfl

end JuliaLean.BigNumsCov.MpfrFaithful
