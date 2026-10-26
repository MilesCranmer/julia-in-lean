import JuliaLean.BigNumsCov.MpfrFaithful.Prelude

namespace JuliaLean.BigNumsCov.MpfrFaithful

/-! `base/mpfr.jl:149-254`. -/

def bigFloat149 (initializePointer : List Nat → Unit) (words : List Nat) : Run BFRep :=
  let _ := initializePointer words
  ⟨["unsafe_convert(Ref{BigFloat},BigFloatData)"],
    { precision := 0, sign := 1, exponent := 0, words := words }⟩

def BigFloat149 : Prop :=
  ∀ initializePointer words,
    (bigFloat149 initializePointer words).calls =
      ["unsafe_convert(Ref{BigFloat},BigFloatData)"] ∧
    (bigFloat149 initializePointer words).value.words = words

theorem bigFloat149_proven : BigFloat149 := by
  unfold BigFloat149
  intros
  exact ⟨rfl, rfl⟩

def bigFloat154 (customSize : Int → Nat) (allocate : Nat → List Nat)
    (precision : Int) (offsetBytes limbBytes nanExponent : Nat) : Run (Except String BFRep) :=
  if precision < 1 then
    ⟨["precision-check"], .error "precision cannot be less than 1"⟩
  else
    let bytes := customSize precision
    let limbs := (bytes + offsetBytes + limbBytes - 1) / limbBytes
    let words := allocate limbs
    ⟨["precision-check", "mpfr_custom_get_size", "Memory", "unsafe_convert",
      "store-precision", "store-sign", "store-nan-exponent", "store-data-pointer"],
      .ok { precision := precision, sign := 1, exponent := nanExponent, words := words }⟩

def BigFloat154 : Prop :=
  ∀ customSize allocate precision offsetBytes limbBytes nanExponent,
    (bigFloat154 customSize allocate precision offsetBytes limbBytes nanExponent).value =
      if precision < 1 then .error "precision cannot be less than 1"
      else
        let bytes := customSize precision
        let limbs := (bytes + offsetBytes + limbBytes - 1) / limbBytes
        .ok { precision := precision, sign := 1, exponent := nanExponent, words := allocate limbs }

theorem bigFloat154_proven : BigFloat154 := by
  unfold BigFloat154
  intros customSize allocate precision offsetBytes limbBytes nanExponent
  by_cases h : precision < 1 <;> simp [bigFloat154, h]

def getproperty183 (x : BFRep) (field : BFField) : Run (Except String BFFieldValue) :=
  match field with
  | .precision => ⟨["getfield(d)", "unsafe_convert", "unsafe_load(prec)"],
      .ok (.scalar x.precision)⟩
  | .sign => ⟨["getfield(d)", "unsafe_convert", "unsafe_load(sign)"],
      .ok (.scalar x.sign)⟩
  | .exponent => ⟨["getfield(d)", "unsafe_convert", "unsafe_load(exp)"],
      .ok (.scalar x.exponent)⟩
  | .data => ⟨["getfield(d)", "unsafe_convert", "BigFloatData"], .ok (.data x.words)⟩
  | .other => ⟨["getfield(d)", "unsafe_convert", "FieldError"], .error "FieldError"⟩

def Getproperty183 : Prop :=
  ∀ x field, (getproperty183 x field).value =
    match field with
    | .precision => .ok (.scalar x.precision)
    | .sign => .ok (.scalar x.sign)
    | .exponent => .ok (.scalar x.exponent)
    | .data => .ok (.data x.words)
    | .other => .error "FieldError"

theorem getproperty183_proven : Getproperty183 := by
  unfold Getproperty183
  intros x field
  cases field <;> rfl

def setproperty201 (x : BFRep) (field : BFField) (value : Int) :
    Run (Except String BFRep) :=
  match field with
  | .sign => ⟨["getfield(d)", "unsafe_convert", "unsafe_store(sign)"],
      .ok { x with sign := value }⟩
  | .exponent => ⟨["getfield(d)", "unsafe_convert", "unsafe_store(exp)"],
      .ok { x with exponent := value }⟩
  | _ => ⟨["getfield(d)", "unsafe_convert", "FieldError"], .error "FieldError"⟩

def Setproperty201 : Prop :=
  ∀ x field value, (setproperty201 x field value).value =
    match field with
    | .sign => .ok { x with sign := value }
    | .exponent => .ok { x with exponent := value }
    | _ => .error "FieldError"

theorem setproperty201_proven : Setproperty201 := by
  unfold Setproperty201
  intros x field value
  cases field <;> rfl

def unsafeConvert214 (_ : PtrInput) : Except RefConversionError Int :=
  .error (.errorException "not compatible with mpfr")
def unsafeConvert215 (_ : PtrInput) : Except RefConversionError Int :=
  .error (.errorException "not compatible with mpfr")

def UnsafeConvert214 : Prop := ∀ input,
  unsafeConvert214 input = .error (.errorException "not compatible with mpfr")
def UnsafeConvert215 : Prop := ∀ input,
  unsafeConvert215 input = .error (.errorException "not compatible with mpfr")
theorem unsafeConvert214_proven : UnsafeConvert214 := by
  unfold UnsafeConvert214
  intros
  rfl
theorem unsafeConvert215_proven : UnsafeConvert215 := by
  unfold UnsafeConvert215
  intros
  rfl

def cconvert216 (x : BFRep) : List Nat := x.words
def Cconvert216 : Prop := ∀ x, cconvert216 x = x.words
theorem cconvert216_proven : Cconvert216 := by
  unfold Cconvert216
  intros
  rfl

def cconvert217 (convert : Int → BFRep) (x : Int) : Run (List Nat) :=
  let converted := convert x
  ⟨["convert(BigFloat,x)", "getfield(d)"], converted.words⟩

def Cconvert217 : Prop :=
  ∀ convert x, (cconvert217 convert x).value = (convert x).words
theorem cconvert217_proven : Cconvert217 := by
  unfold Cconvert217
  intros
  rfl

def cconvert218 (dereference : Int → BFRep) (reference : Int) : Run (List Nat) :=
  let x := dereference reference
  ⟨["getindex(Ref)", "getfield(d)"], x.words⟩

def Cconvert218 : Prop :=
  ∀ dereference reference, (cconvert218 dereference reference).value =
    (dereference reference).words
theorem cconvert218_proven : Cconvert218 := by
  unfold Cconvert218
  intros
  rfl

def unsafeConvert219 (storedPointer computedPointer basePointer : Int) : Run (Int × Int) :=
  if storedPointer != computedPointer then
    ⟨["getfield(d)", "unsafe_convert", "compute-dptrptr", "compute-dptr",
      "unsafe_load(monotonic)", "unsafe_store(monotonic)"], (computedPointer, basePointer)⟩
  else
    ⟨["getfield(d)", "unsafe_convert", "compute-dptrptr", "compute-dptr",
      "unsafe_load(monotonic)"], (storedPointer, basePointer)⟩

def UnsafeConvert219 : Prop :=
  ∀ stored computed base,
    (unsafeConvert219 stored computed base).value =
      (if stored != computed then computed else stored, base)

theorem unsafeConvert219_proven : UnsafeConvert219 := by
  unfold UnsafeConvert219
  intros stored computed base
  by_cases h : stored = computed <;> simp [unsafeConvert219, h]

def unsafeConvert229 (basePointer offset : Int) : Int := basePointer + offset
def UnsafeConvert229 : Prop := ∀ base offset, unsafeConvert229 base offset = base + offset
theorem unsafeConvert229_proven : UnsafeConvert229 := by
  unfold UnsafeConvert229
  intros
  rfl

def setindex230 (words : List Int) (offset : Nat) (value index : Int) :
    Except String (List Int) :=
  if 1 ≤ index ∧ index ≤ words.length - offset then
    .ok (words.set (index.toNat + offset - 1) value)
  else .error "BoundsError"

def Setindex230 : Prop :=
  ∀ words (offset : Nat) value index,
    setindex230 words offset value index =
      if 1 ≤ index ∧ index ≤ words.length - offset then
        .ok (words.set (index.toNat + offset - 1) value)
      else .error "BoundsError"

theorem setindex230_proven : Setindex230 := by
  unfold Setindex230
  intros
  rfl

def getindex236 (words : List Int) (offset : Nat) (index : Int) : Except String Int :=
  if 1 ≤ index ∧ index ≤ words.length - offset then
    match words[index.toNat + offset - 1]? with
    | some value => .ok value
    | none => .error "BoundsError"
  else .error "BoundsError"

def Getindex236 : Prop :=
  ∀ words (offset : Nat) index,
    getindex236 words offset index =
      if 1 ≤ index ∧ index ≤ words.length - offset then
        match words[index.toNat + offset - 1]? with
        | some value => .ok value
        | none => .error "BoundsError"
      else .error "BoundsError"

theorem getindex236_proven : Getindex236 := by
  unfold Getindex236
  intros
  rfl

def length241 (wordsLength offset : Nat) : Nat := wordsLength - offset
def Length241 : Prop := ∀ (length offset : Nat), length241 length offset = length - offset
theorem length241_proven : Length241 := by
  unfold Length241
  intros
  rfl

def copyto242 (copy : List Int → Nat → List Int → List Int) (words limbs : List Int)
    (offset : Nat) : Run (List Int) :=
  ⟨["getfield(d)", "copyto!(offset+1)"], copy words (offset + 1) limbs⟩

def Copyto242 : Prop :=
  ∀ copy words limbs offset,
    (copyto242 copy words limbs offset).value = copy words (offset + 1) limbs
theorem copyto242_proven : Copyto242 := by
  unfold Copyto242
  intros
  rfl

def setroundingRaw247 (_old newMode : RMode) : RMode × RMode := (newMode, newMode)
def SetroundingRaw247 : Prop := ∀ old newMode, setroundingRaw247 old newMode = (newMode, newMode)
theorem setroundingRaw247_proven : SetroundingRaw247 := by
  unfold SetroundingRaw247
  intros
  rfl

def setroundingRaw248 (callback : RMode → Int) (old newMode : RMode) : Run (Int × RMode) :=
  let value := callback newMode
  ⟨["ScopedValue-install", "callback", "ScopedValue-restore"], (value, old)⟩

def SetroundingRaw248 : Prop :=
  ∀ callback old newMode,
    (setroundingRaw248 callback old newMode).value = (callback newMode, old)
theorem setroundingRaw248_proven : SetroundingRaw248 := by
  unfold SetroundingRaw248
  intros
  rfl

def rounding252 (raw : Unit → RMode) (convert : RMode → PMode) : Run PMode :=
  let mode := raw ()
  ⟨["rounding_raw(BigFloat)", "convert(RoundingMode,mode)"], convert mode⟩

def Rounding252 : Prop :=
  ∀ raw convert, (rounding252 raw convert).value = convert (raw ())
theorem rounding252_proven : Rounding252 := by
  unfold Rounding252
  intros
  rfl

def setrounding253 (convert : PMode → RMode) (assign : RMode → RMode)
    (mode : PMode) : Run RMode :=
  let raw := convert mode
  ⟨["convert(MPFRRoundingMode,r)", "setrounding_raw(BigFloat,raw)"], assign raw⟩

def Setrounding253 : Prop :=
  ∀ convert assign mode, (setrounding253 convert assign mode).value = assign (convert mode)
theorem setrounding253_proven : Setrounding253 := by
  unfold Setrounding253
  intros
  rfl

def setrounding254 (convert : PMode → RMode) (withScoped : (RMode → Int) → RMode → Int)
    (callback : RMode → Int) (mode : PMode) : Run Int :=
  let raw := convert mode
  ⟨["convert(MPFRRoundingMode,r)", "setrounding_raw(f,BigFloat,raw)"],
    withScoped callback raw⟩

def Setrounding254 : Prop :=
  ∀ convert withScoped callback mode,
    (setrounding254 convert withScoped callback mode).value = withScoped callback (convert mode)
theorem setrounding254_proven : Setrounding254 := by
  unfold Setrounding254
  intros
  rfl

end JuliaLean.BigNumsCov.MpfrFaithful
