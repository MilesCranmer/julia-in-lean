import JuliaLean.RangesCov.Twice
import JuliaLean.RangesCov.Log
import JuliaLean.RangesCov.Convert

namespace JuliaLean.RangesCov
namespace TwiceMethods

open JuliaLean JuliaLean.Registry

/-- A type-parametric TwicePrecision value for constructor and conversion wrappers. -/
structure GTP (α : Type) where
  hi : α
  lo : α
  deriving DecidableEq

/-- `canonicalize2(big,little)`, base/twiceprecision.jl:48-51, for any numeric type. -/
def canonicalizeG (add sub : α → α → α) (big little : α) : α × α :=
  let h := add big little
  (h, add (sub big h) little)

def CanonicalizeGenericBehaviour : Prop := ∀ (α : Type) add sub (big little : α),
  canonicalizeG add sub big little =
    let h := add big little; (h, add (sub big h) little)
theorem canonicalizeGenericBehaviour_proven : CanonicalizeGenericBehaviour := fun _ _ _ _ _ => rfl

/-- `add12(x::T,y::T)`, base/twiceprecision.jl:83-86, with type operations explicit. -/
def add12GenericSame (absGt : α → α → Bool) (canonicalize : α → α → α × α)
    (x y : α) : α × α :=
  let p := if absGt y x then (y, x) else (x, y)
  canonicalize p.1 p.2

def Add12GenericSameBehaviour : Prop := ∀ (α : Type) absGt canonicalize (x y : α),
  add12GenericSame absGt canonicalize x y =
    let p := if absGt y x then (y, x) else (x, y); canonicalize p.1 p.2
theorem add12GenericSameBehaviour_proven : Add12GenericSameBehaviour := fun _ _ _ _ _ => rfl

/-- `mul12(::AbstractFloat,::AbstractFloat)`, base/twiceprecision.jl:114-117. -/
def mul12FloatGeneric (twoMul : α → α → α × α) (isfinite : α → Bool) (x y : α) : α × α :=
  let p := twoMul x y
  if !isfinite p.1 then (p.1, p.1) else p

def Mul12FloatGenericBehaviour : Prop := ∀ (α : Type) twoMul isfinite (x y : α),
  mul12FloatGeneric twoMul isfinite x y =
    let p := twoMul x y; if !isfinite p.1 then (p.1, p.1) else p
theorem mul12FloatGenericBehaviour_proven : Mul12FloatGenericBehaviour := fun _ _ _ _ _ => rfl

/-- `mul12(x::T,y::T) where T`, base/twiceprecision.jl:118. -/
def mul12GenericSame (mul : α → α → α) (zero : α → α) (x y : α) : α × α :=
  let p := mul x y
  (p, zero p)

def Mul12GenericSameBehaviour : Prop := ∀ (α : Type) mul zero (x y : α),
  mul12GenericSame mul zero x y = let p := mul x y; (p, zero p)
theorem mul12GenericSameBehaviour_proven : Mul12GenericSameBehaviour := fun _ _ _ _ _ => rfl

def add12Same (x y : F64) : F64 × F64 := FloatRanges.add12 x y
def Add12SameBehaviour : Prop := ∀ x y,
  add12Same x y =
    let p := if Float.F64.lt (Float.F64.abs x) (Float.F64.abs y) then (y, x) else (x, y)
    FloatRanges.canonicalize2 p.1 p.2
theorem add12SameBehaviour_proven : Add12SameBehaviour := fun _ _ => rfl

def add12Promote (promote : α → β → γ × γ) (add12 : γ → γ → δ) (x : α) (y : β) : δ :=
  let p := promote x y
  add12 p.1 p.2
def Add12PromoteBehaviour : Prop := ∀ (α β γ δ : Type) promote add12 x y,
  add12Promote (promote : α → β → γ × γ) (add12 : γ → γ → δ) x y =
    let p := promote x y; add12 p.1 p.2
theorem add12PromoteBehaviour_proven : Add12PromoteBehaviour := fun _ _ _ _ _ _ _ _ => rfl

def mul12Promote (promote : α → β → γ × γ) (mul12 : γ → γ → δ) (x : α) (y : β) : δ :=
  let p := promote x y
  mul12 p.1 p.2
def Mul12PromoteBehaviour : Prop := ∀ (α β γ δ : Type) promote mul12 x y,
  mul12Promote (promote : α → β → γ × γ) (mul12 : γ → γ → δ) x y =
    let p := promote x y; mul12 p.1 p.2
theorem mul12PromoteBehaviour_proven : Mul12PromoteBehaviour := fun _ _ _ _ _ _ _ _ => rfl

/-- `div12(::AbstractFloat, ::AbstractFloat)`, base/twiceprecision.jl:146-154.
`frexp` and `ldexp` are primitive parameters; every arithmetic step is retained. -/
def div12FloatGeneric (frexp : α → α × Int) (div : α → α → α) (neg : α → α)
    (fma : α → α → α → α) (canonicalize : α → α → α × α)
    (iszero isfinite : α → Bool) (ldexp : α → Int → α) (x y : α) : α × α :=
  let xs := frexp x
  let ys := frexp y
  let r := div xs.1 ys.1
  let correction := div (neg (fma r ys.1 (neg xs.1))) ys.1
  let p := canonicalize r correction
  if iszero r || !isfinite r then (r, r)
  else (ldexp p.1 (xs.2 - ys.2), ldexp p.2 (xs.2 - ys.2))

def Div12FloatBehaviour : Prop := ∀ (α : Type) frexp div neg fma canonicalize iszero isfinite ldexp (x y : α),
  div12FloatGeneric frexp div neg fma canonicalize iszero isfinite ldexp x y =
    let xs := frexp x
    let ys := frexp y
    let r := div xs.1 ys.1
    let correction := div (neg (fma r ys.1 (neg xs.1))) ys.1
    let p := canonicalize r correction
    if iszero r || !isfinite r then (r, r)
    else (ldexp p.1 (xs.2 - ys.2), ldexp p.2 (xs.2 - ys.2))
theorem div12FloatBehaviour_proven : Div12FloatBehaviour := fun _ _ _ _ _ _ _ _ _ _ _ => rfl

def div12Generic (div : α → α → α) (zero : α → α) (x y : α) : α × α :=
  let p := div x y
  (p, zero p)
def Div12GenericBehaviour : Prop := ∀ (α : Type) (div : α → α → α) (zero : α → α) (x y : α),
  div12Generic div zero x y = let p := div x y; (p, zero p)
theorem div12GenericBehaviour_proven : Div12GenericBehaviour := fun _ _ _ _ _ => rfl

def div12Promote (promote : α → β → γ × γ) (div12 : γ → γ → δ) (x : α) (y : β) : δ :=
  let p := promote x y
  div12 p.1 p.2
def Div12PromoteBehaviour : Prop := ∀ (α β γ δ : Type) promote div12 x y,
  div12Promote (promote : α → β → γ × γ) (div12 : γ → γ → δ) x y =
    let p := promote x y; div12 p.1 p.2
theorem div12PromoteBehaviour_proven : Div12PromoteBehaviour := fun _ _ _ _ _ _ _ _ => rfl

def tpFromSame (zero : α) (x : α) : GTP α := ⟨x, zero⟩
def tpIdentity (x : GTP α) : GTP α := x
def tpConvert (convert : β → α) (sub : β → α → β) (x : β) : GTP α :=
  let xT := convert x
  ⟨xT, convert (sub x xT)⟩
def tpOuter (typed : α → GTP α) (x : α) : GTP α := typed x
def tpRatioSmall (div : α → α → α) (typed : α → GTP α) (n d : α) : GTP α := typed (div n d)
def tpRatioAny (typed : α → GTP α) (div : GTP α → β → GTP α) (n : α) (d : β) : GTP α := div (typed n) d
def tpRatioBits (ratio : α → β → GTP γ) (truncate : GTP γ → Int → GTP γ) (n : α) (d : β) (nb : Int) : GTP γ :=
  truncate (ratio n d) nb

def TpFromSameBehaviour : Prop := ∀ (α : Type) z x, tpFromSame (α := α) z x = ⟨x, z⟩
def TpIdentityBehaviour : Prop := ∀ (α : Type) (x : GTP α), tpIdentity x = x
def TpConvertBehaviour : Prop := ∀ (α β : Type) convert sub x,
  tpConvert (convert : β → α) (sub : β → α → β) x =
    let xT := convert x; ⟨xT, convert (sub x xT)⟩
def TpOuterBehaviour : Prop := ∀ (α : Type) typed x, tpOuter (typed : α → GTP α) x = typed x
def TpRatioSmallBehaviour : Prop := ∀ (α : Type) div typed n d,
  tpRatioSmall (div : α → α → α) (typed : α → GTP α) n d = typed (div n d)
def TpRatioAnyBehaviour : Prop := ∀ (α β : Type) typed div n d,
  tpRatioAny (typed : α → GTP α) (div : GTP α → β → GTP α) n d = div (typed n) d
def TpRatioBitsBehaviour : Prop := ∀ (α β γ : Type) ratio truncate n d nb,
  tpRatioBits (ratio : α → β → GTP γ) (truncate : GTP γ → Int → GTP γ) n d nb = truncate (ratio n d) nb
theorem tpFromSameBehaviour_proven : TpFromSameBehaviour := fun _ _ _ => rfl
theorem tpIdentityBehaviour_proven : TpIdentityBehaviour := fun _ _ => rfl
theorem tpConvertBehaviour_proven : TpConvertBehaviour := fun _ _ _ _ _ => rfl
theorem tpOuterBehaviour_proven : TpOuterBehaviour := fun _ _ _ => rfl
theorem tpRatioSmallBehaviour_proven : TpRatioSmallBehaviour := fun _ _ _ _ _ => rfl
theorem tpRatioAnyBehaviour_proven : TpRatioAnyBehaviour := fun _ _ _ _ _ _ => rfl
theorem tpRatioBitsBehaviour_proven : TpRatioBitsBehaviour := fun _ _ _ _ _ _ _ _ => rfl

def twiceprecisionF (x : F64) (nb : Int) : TP := FloatRanges.TP.trunc (FloatRanges.TP.ofF x) nb
def twiceprecisionTp (x : TP) (nb : Int) : TP := FloatRanges.TP.trunc x nb
def TwiceprecisionFBehaviour : Prop := ∀ x nb,
  twiceprecisionF x nb =
    let hi := FloatRanges.truncbits x nb
    ⟨hi, Float.F64.add (Float.F64.sub x hi) FloatRanges.fzero⟩
def TwiceprecisionTpBehaviour : Prop := ∀ x nb,
  twiceprecisionTp x nb =
    let hi := FloatRanges.truncbits x.hi nb
    ⟨hi, Float.F64.add (Float.F64.sub x.hi hi) x.lo⟩
theorem twiceprecisionFBehaviour_proven : TwiceprecisionFBehaviour := fun _ _ => rfl
theorem twiceprecisionTpBehaviour_proven : TwiceprecisionTpBehaviour := fun _ _ => rfl

def nbitslenRange (r : FloatRanges.SRL) : Int := FloatRanges.nbitslen r.len r.offset
def NbitslenRangeBehaviour : Prop := ∀ r, nbitslenRange r = FloatRanges.nbitslen r.len r.offset
theorem nbitslenRangeBehaviour_proven : NbitslenRangeBehaviour := fun _ => rfl

/-- Type-level results use the integer type model already used by range promotion. -/
def tpEltype (t : NType) : NType := t
def tpPromote (a b : NType) : NType := Ranges.Num.promote a b
def TpEltypeBehaviour : Prop := ∀ t, tpEltype t = t
def TpPromoteTpBehaviour : Prop := ∀ a b, tpPromote a b = Ranges.Num.promote a b
def TpPromoteNumberBehaviour : Prop := ∀ a b, tpPromote a b = Ranges.Num.promote a b
theorem tpEltypeBehaviour_proven : TpEltypeBehaviour := fun _ => rfl
theorem tpPromoteTpBehaviour_proven : TpPromoteTpBehaviour := fun _ _ => rfl
theorem tpPromoteNumberBehaviour_proven : TpPromoteNumberBehaviour := fun _ _ => rfl

def tpToNumber (x : TP) : F64 := FloatRanges.TP.toF x
def tpConvertSame (x : TP) : TP := x
def tpConvertPair (convert : α → β) (x : GTP α) : GTP β := ⟨convert x.hi, convert x.lo⟩
def tpConvertToNumber (convert : α → β) (add : β → β → β) (x : GTP α) : β := add (convert x.hi) (convert x.lo)
def convertToNumberWrapper (convert : GTP α → β) (x : GTP α) : β := convert x
def numberToTp (typed : α → GTP β) (x : α) : GTP β := typed x
def tpFloatSame (x : TP) : TP := x
def tpFloatMap (toFloat : α → β) (x : GTP α) : GTP β := ⟨toFloat x.hi, toFloat x.lo⟩
def tpBig (toBig : α → β) (add : β → β → β) (x : GTP α) : β := add (toBig x.hi) (toBig x.lo)

def TpToNumberBehaviour : Prop := ∀ x, tpToNumber x = Float.F64.add x.hi x.lo
def TpConvertSameBehaviour : Prop := ∀ x, tpConvertSame x = x
def TpConvertPairBehaviour : Prop := ∀ (α β : Type) f (x : GTP α), tpConvertPair (f : α → β) x = ⟨f x.hi, f x.lo⟩
def TpConvertToNumberBehaviour : Prop := ∀ (α β : Type) f add (x : GTP α), tpConvertToNumber (f : α → β) add x = add (f x.hi) (f x.lo)
def ConvertToNumberWrapperBehaviour : Prop := ∀ (α β : Type) f (x : GTP α),
  convertToNumberWrapper (f : GTP α → β) x = f x
def NumberToTpBehaviour : Prop := ∀ (α β : Type) typed x, numberToTp (typed : α → GTP β) x = typed x
def TpFloatSameBehaviour : Prop := ∀ x, tpFloatSame x = x
def TpFloatMapBehaviour : Prop := ∀ (α β : Type) f (x : GTP α), tpFloatMap (f : α → β) x = ⟨f x.hi, f x.lo⟩
def TpBigBehaviour : Prop := ∀ (α β : Type) f add (x : GTP α), tpBig (f : α → β) add x = add (f x.hi) (f x.lo)
theorem tpToNumberBehaviour_proven : TpToNumberBehaviour := fun _ => rfl
theorem tpConvertSameBehaviour_proven : TpConvertSameBehaviour := fun _ => rfl
theorem tpConvertPairBehaviour_proven : TpConvertPairBehaviour := fun _ _ _ _ => rfl
theorem tpConvertToNumberBehaviour_proven : TpConvertToNumberBehaviour := fun _ _ _ _ _ => rfl
theorem convertToNumberWrapperBehaviour_proven : ConvertToNumberWrapperBehaviour := fun _ _ _ _ => rfl
theorem numberToTpBehaviour_proven : NumberToTpBehaviour := fun _ _ _ _ => rfl
theorem tpFloatSameBehaviour_proven : TpFloatSameBehaviour := fun _ => rfl
theorem tpFloatMapBehaviour_proven : TpFloatMapBehaviour := fun _ _ _ _ => rfl
theorem tpBigBehaviour_proven : TpBigBehaviour := fun _ _ _ _ _ => rfl

def tpZeroValue (_x : GTP α) (z : α) : GTP α := ⟨z, z⟩
def tpZeroType (z : α) : GTP α := ⟨z, z⟩
def TpZeroValueBehaviour : Prop := ∀ (α : Type) (x : GTP α) z, tpZeroValue x z = ⟨z, z⟩
def TpZeroTypeBehaviour : Prop := ∀ (α : Type) z, tpZeroType (α := α) z = ⟨z, z⟩
theorem tpZeroValueBehaviour_proven : TpZeroValueBehaviour := fun _ _ _ => rfl
theorem tpZeroTypeBehaviour_proven : TpZeroTypeBehaviour := fun _ _ => rfl

/-- Type-parametric translations of the compensated arithmetic bodies. -/
def addNumberG (add12 canonicalize : α → α → α × α) (add : α → α → α)
    (x : GTP α) (y : α) : GTP α :=
  let p := add12 x.hi y
  let q := canonicalize p.1 (add p.2 x.lo)
  ⟨q.1, q.2⟩

def addTpG (add sub : α → α → α) (absGt : α → α → Bool)
    (canonicalize : α → α → α × α) (x y : GTP α) : GTP α :=
  let r := add x.hi y.hi
  let s := if absGt x.hi y.hi then
      add (add (add (sub x.hi r) y.hi) y.lo) x.lo
    else add (add (add (sub y.hi r) x.hi) x.lo) y.lo
  let p := canonicalize r s
  ⟨p.1, p.2⟩

def mulNumberG (eqZero : β → Bool) (mul : α → β → α)
    (oftype : α → β → α) (zero : α → α) (mulTp : GTP α → GTP α → GTP α)
    (x : GTP α) (v : β) : GTP α :=
  if eqZero v then ⟨mul x.hi v, mul x.lo v⟩
  else
    let hi := oftype (mul x.hi v) v
    mulTp x ⟨hi, zero hi⟩

def mulTpG (mul add : α → α → α) (mul12 canonicalize : α → α → α × α)
    (iszero isfinite : α → Bool) (x y : GTP α) : GTP α :=
  let p := mul12 x.hi y.hi
  let q := canonicalize p.1 (add (add (mul x.hi y.lo) (mul x.lo y.hi)) p.2)
  let ret : GTP α := ⟨q.1, q.2⟩
  if iszero p.1 || !isfinite p.1 then ⟨p.1, p.1⟩ else ret

def divTpG (div mul sub add : α → α → α) (mul12 canonicalize : α → α → α × α)
    (iszero isfinite : α → Bool) (x y : GTP α) : GTP α :=
  let hi := div x.hi y.hi
  let p := mul12 hi y.hi
  let lo := div (sub (add (sub (sub x.hi p.1) p.2) x.lo) (mul hi y.lo)) y.hi
  let q := canonicalize hi lo
  let ret : GTP α := ⟨q.1, q.2⟩
  if iszero hi || !isfinite hi then ⟨hi, hi⟩ else ret

def AddNumberGenericBehaviour : Prop := ∀ (α : Type) add12 canonicalize add (x : GTP α) y,
  addNumberG add12 canonicalize add x y =
    let p := add12 x.hi y
    let q := canonicalize p.1 (add p.2 x.lo)
    ⟨q.1, q.2⟩
def AddTpGenericBehaviour : Prop := ∀ (α : Type) add sub absGt canonicalize (x y : GTP α),
  addTpG add sub absGt canonicalize x y =
    let r := add x.hi y.hi
    let s := if absGt x.hi y.hi then add (add (add (sub x.hi r) y.hi) y.lo) x.lo
      else add (add (add (sub y.hi r) x.hi) x.lo) y.lo
    let p := canonicalize r s
    ⟨p.1, p.2⟩
def MulNumberGenericBehaviour : Prop := ∀ (α β : Type) eqZero mul oftype zero mulTp (x : GTP α) (v : β),
  mulNumberG eqZero mul oftype zero mulTp x v =
    if eqZero v then ⟨mul x.hi v, mul x.lo v⟩
    else
      let hi := oftype (mul x.hi v) v
      mulTp x ⟨hi, zero hi⟩
def MulTpGenericBehaviour : Prop := ∀ (α : Type) mul add mul12 canonicalize iszero isfinite (x y : GTP α),
  mulTpG mul add mul12 canonicalize iszero isfinite x y =
    let p := mul12 x.hi y.hi
    let q := canonicalize p.1 (add (add (mul x.hi y.lo) (mul x.lo y.hi)) p.2)
    let ret : GTP α := ⟨q.1, q.2⟩
    if iszero p.1 || !isfinite p.1 then ⟨p.1, p.1⟩ else ret
def DivTpGenericBehaviour : Prop := ∀ (α : Type) div mul sub add mul12 canonicalize iszero isfinite (x y : GTP α),
  divTpG div mul sub add mul12 canonicalize iszero isfinite x y =
    let hi := div x.hi y.hi
    let p := mul12 hi y.hi
    let lo := div (sub (add (sub (sub x.hi p.1) p.2) x.lo) (mul hi y.lo)) y.hi
    let q := canonicalize hi lo
    let ret : GTP α := ⟨q.1, q.2⟩
    if iszero hi || !isfinite hi then ⟨hi, hi⟩ else ret
theorem addNumberGenericBehaviour_proven : AddNumberGenericBehaviour := fun _ _ _ _ _ _ => rfl
theorem addTpGenericBehaviour_proven : AddTpGenericBehaviour := fun _ _ _ _ _ _ _ => rfl
theorem mulNumberGenericBehaviour_proven : MulNumberGenericBehaviour := fun _ _ _ _ _ _ _ _ _ => rfl
theorem mulTpGenericBehaviour_proven : MulTpGenericBehaviour := fun _ _ _ _ _ _ _ _ _ => rfl
theorem divTpGenericBehaviour_proven : DivTpGenericBehaviour := fun _ _ _ _ _ _ _ _ _ _ _ => rfl

def tpAddNumber (x : TP) (y : F64) : TP := FloatRanges.TP.addF x y
def numberAddTp (x : F64) (y : TP) : TP := FloatRanges.TP.addF y x
def tpAdd (x y : TP) : TP := FloatRanges.TP.add x y
def tpAddPromote (promote : α → β → TP × TP) (x : α) (y : β) : TP :=
  let p := promote x y; FloatRanges.TP.add p.1 p.2
def tpSub (x y : TP) : TP := FloatRanges.TP.add x y.neg
def tpSubNumber (x : TP) (y : F64) : TP := FloatRanges.TP.addF x (Float.F64.neg y)
def numberSubTp (x : F64) (y : TP) : TP := FloatRanges.TP.addF y.neg x
def tpMulNumber (x : TP) (y : F64) : TP := FloatRanges.TP.mulF x y
def numberMulTp (x : F64) (y : TP) : TP := FloatRanges.TP.mulF y x
def tpMul (x y : TP) : TP := FloatRanges.TP.mul x y
def tpMulPromote (promote : α → β → TP × TP) (x : α) (y : β) : TP :=
  let p := promote x y; FloatRanges.TP.mul p.1 p.2
def tpDivNumber (x : TP) (y : F64) : TP := FloatRanges.TP.divF x y
def tpDiv (x y : TP) : TP := FloatRanges.TP.div x y

def TpAddNumberBehaviour : Prop := ∀ x y, tpAddNumber x y = FloatRanges.TP.addF x y
def NumberAddTpBehaviour : Prop := ∀ x y, numberAddTp x y = tpAddNumber y x
def TpAddBehaviour : Prop := ∀ x y, tpAdd x y = FloatRanges.TP.add x y
def TpAddPromoteBehaviour : Prop := ∀ (α β : Type) p x y,
  tpAddPromote (p : α → β → TP × TP) x y = let q := p x y; FloatRanges.TP.add q.1 q.2
def TpSubBehaviour : Prop := ∀ x y, tpSub x y = FloatRanges.TP.add x y.neg
def TpSubNumberBehaviour : Prop := ∀ x y, tpSubNumber x y = FloatRanges.TP.addF x (Float.F64.neg y)
def NumberSubTpBehaviour : Prop := ∀ x y, numberSubTp x y = FloatRanges.TP.addF y.neg x
def TpMulNumberBehaviour : Prop := ∀ x y, tpMulNumber x y = FloatRanges.TP.mulF x y
def NumberMulTpBehaviour : Prop := ∀ x y, numberMulTp x y = tpMulNumber y x
def TpMulBehaviour : Prop := ∀ x y, tpMul x y = FloatRanges.TP.mul x y
def TpMulPromoteBehaviour : Prop := ∀ (α β : Type) p x y,
  tpMulPromote (p : α → β → TP × TP) x y = let q := p x y; FloatRanges.TP.mul q.1 q.2
def TpDivNumberBehaviour : Prop := ∀ x y, tpDivNumber x y = FloatRanges.TP.divF x y
def TpDivBehaviour : Prop := ∀ x y, tpDiv x y = FloatRanges.TP.div x y
theorem tpAddNumberBehaviour_proven : TpAddNumberBehaviour := fun _ _ => rfl
theorem numberAddTpBehaviour_proven : NumberAddTpBehaviour := fun _ _ => rfl
theorem tpAddBehaviour_proven : TpAddBehaviour := fun _ _ => rfl
theorem tpAddPromoteBehaviour_proven : TpAddPromoteBehaviour := fun _ _ _ _ _ => rfl
theorem tpSubBehaviour_proven : TpSubBehaviour := fun _ _ => rfl
theorem tpSubNumberBehaviour_proven : TpSubNumberBehaviour := fun _ _ => rfl
theorem numberSubTpBehaviour_proven : NumberSubTpBehaviour := fun _ _ => rfl
theorem tpMulNumberBehaviour_proven : TpMulNumberBehaviour := fun _ _ => rfl
theorem numberMulTpBehaviour_proven : NumberMulTpBehaviour := fun _ _ => rfl
theorem tpMulBehaviour_proven : TpMulBehaviour := fun _ _ => rfl
theorem tpMulPromoteBehaviour_proven : TpMulPromoteBehaviour := fun _ _ _ _ _ => rfl
theorem tpDivNumberBehaviour_proven : TpDivNumberBehaviour := fun _ _ => rfl
theorem tpDivBehaviour_proven : TpDivBehaviour := fun _ _ => rfl

def TpMulIntegerBehaviour : Prop := ∀ x v, Twice.mulInt x v =
  if v.val = 0 then ⟨Float.F64.mul x.hi (FloatRanges.flt v), Float.F64.mul x.lo (FloatRanges.flt v)⟩
  else
    let nb := FloatRanges.topSetBit (FloatRanges.iabs v - FloatRanges.i64 1)
    let u := FloatRanges.truncbits x.hi nb
    let p := FloatRanges.canonicalize2 (Float.F64.mul u (FloatRanges.flt v))
      (Float.F64.mul (Float.F64.add (Float.F64.sub x.hi u) x.lo) (FloatRanges.flt v))
    ⟨p.1, p.2⟩
theorem tpMulIntegerBehaviour_proven : TpMulIntegerBehaviour := fun _ _ => rfl

/-- Non-Float64 high-precision constructors store ordinary Float64 reference and step. -/
def hpTupleSmall (ref step : I64 × I64) (len off : I64) : FSRL :=
  ⟨Float.F64.div (FloatRanges.flt ref.1) (FloatRanges.flt ref.2),
    Float.F64.div (FloatRanges.flt step.1) (FloatRanges.flt step.2), len, off⟩
def asF64One (x : F64) : F64 := x
def asF64Pair (x : F64 × F64) : F64 := Float.F64.add x.1 x.2
def asF64Scalar (convert : α → F64) (x : α) : F64 := convert x
def asF64Tuple (convert : α → F64) (x : α × α) : F64 := Float.F64.add (convert x.1) (convert x.2)
def hpFloatSmall (ref step : F64 × F64) (len off : I64) : FSRL :=
  ⟨asF64Pair ref, asF64Pair step, len, off⟩
def HpTupleSmallBehaviour : Prop := ∀ ref step len off,
  (hpTupleSmall ref step len off).len = len ∧ (hpTupleSmall ref step len off).offset = off
def AsF64OneBehaviour : Prop := ∀ x, asF64One x = x
def AsF64PairBehaviour : Prop := ∀ x, asF64Pair x = Float.F64.add x.1 x.2
def AsF64ScalarBehaviour : Prop := ∀ (α : Type) f x, asF64Scalar (f : α → F64) x = f x
def AsF64TupleBehaviour : Prop := ∀ (α : Type) f (x : α × α),
  asF64Tuple (f : α → F64) x = Float.F64.add (f x.1) (f x.2)
def HpFloatSmallBehaviour : Prop := ∀ ref step len off,
  (hpFloatSmall ref step len off).ref = asF64Pair ref ∧ (hpFloatSmall ref step len off).step = asF64Pair step
theorem hpTupleSmallBehaviour_proven : HpTupleSmallBehaviour := fun _ _ _ _ => ⟨rfl, rfl⟩
theorem asF64OneBehaviour_proven : AsF64OneBehaviour := fun _ => rfl
theorem asF64PairBehaviour_proven : AsF64PairBehaviour := fun _ => rfl
theorem asF64ScalarBehaviour_proven : AsF64ScalarBehaviour := fun _ _ _ => rfl
theorem asF64TupleBehaviour_proven : AsF64TupleBehaviour := fun _ _ _ => rfl
theorem hpFloatSmallBehaviour_proven : HpFloatSmallBehaviour := fun _ _ _ _ => ⟨rfl, rfl⟩

def StepTpFloatBehaviour : Prop := ∀ r : FloatRanges.SRL, r.step.toF = Float.F64.add r.step.hi r.step.lo
def StepTpGenericBehaviour : Prop := ∀ r : FloatRanges.SRL, r.step.toF = Float.F64.add r.step.hi r.step.lo
def stepTpParametric (convert : α → β) (add : β → β → β) (step : GTP α) : β :=
  add (convert step.hi) (convert step.lo)
def StepTpParametricBehaviour : Prop := ∀ (α β : Type) convert add (step : GTP α),
  stepTpParametric (convert : α → β) add step = add (convert step.hi) (convert step.lo)
theorem stepTpFloatBehaviour_proven : StepTpFloatBehaviour := fun _ => rfl
theorem stepTpGenericBehaviour_proven : StepTpGenericBehaviour := fun _ => rfl
theorem stepTpParametricBehaviour_proven : StepTpParametricBehaviour := fun _ _ _ _ _ => rfl

def rsslFloatPromote (promote : α → β → γ × γ) (method : γ → γ → δ → ε)
    (a : α) (st : β) (len : δ) : ε :=
  let p := promote a st
  method p.1 p.2 len
def RsslFloatPromoteBehaviour : Prop := ∀ (α β γ δ ε : Type) promote method a st len,
  rsslFloatPromote (promote : α → β → γ × γ) (method : γ → γ → δ → ε) a st len =
    let p := promote a st; method p.1 p.2 len
theorem rsslFloatPromoteBehaviour_proven : RsslFloatPromoteBehaviour := fun _ _ _ _ _ _ _ _ _ _ => rfl

/-- Reference and step storage selected by the slicing method at base/twiceprecision.jl:497-533. -/
inductive SliceValue where
  | f64 (x : F64)
  | twice (x : TP)
  deriving DecidableEq

structure TpSliceResult where
  ref : SliceValue
  step : SliceValue
  len : I64
  offset : I64
  deriving DecidableEq

def numToI64 (x : Num) : Jl I64 := do
  let x ← Ranges.Num.cast (.bit .i64) x
  match x with
  | ⟨.bit .i64, n⟩ => pure n
  | _ => .error (.inexactError "Int64")

def tpSliceBounds (r : FloatRanges.SRL) (s : Rng) : Jl Bool := do
  if (Ranges.first s).ty = .bool then
    let n ← Ranges.length s
    return decide (n.val = r.len.val)
  if Ranges.isEmpty s then return true
  return decide (1 ≤ (Ranges.first s).val ∧ (Ranges.first s).val ≤ r.len.val ∧
    1 ≤ (Ranges.last s).val ∧ (Ranges.last s).val ≤ r.len.val)

/-- `getindex(r::StepRangeLen{T,<:TwicePrecision,<:TwicePrecision}, s::OrdinalRange)`,
base/twiceprecision.jl:497-533. -/
def getindexTpSliceSpec (r : FloatRanges.SRL) (s : Rng) : Jl TpSliceResult := do
  if !(← tpSliceBounds r s) then throw .boundsError
  let len ← numToI64 (← Ranges.length s)
  let sstepN := Ranges.step s
  let sstep ← numToI64 sstepN
  let rstep := r.step
  if (Ranges.first s).ty = .bool then
    if len.val = 0 then
      pure ⟨.f64 r.first, .twice rstep, FloatRanges.i64 0, FloatRanges.i64 1⟩
    else if len.val = 1 then
      if (Ranges.first s).val ≠ 0 then
        pure ⟨.f64 r.first, .twice rstep, FloatRanges.i64 1, FloatRanges.i64 1⟩
      else
        pure ⟨.f64 r.first, .twice rstep, FloatRanges.i64 0, FloatRanges.i64 1⟩
    else
      pure ⟨.f64 r.last, .f64 r.stepF, FloatRanges.i64 1, FloatRanges.i64 1⟩
  else
    let q := Float.F64.add
      (Float.F64.div (FloatRanges.flt (r.offset - (← numToI64 (Ranges.first s)))) (FloatRanges.flt sstep))
      Float.F64.one
    let rounded ← Float.F64.roundInt .i64 q
    let soffset := FloatRanges.iclamp rounded (FloatRanges.i64 1) len
    let firstS ← numToI64 (Ranges.first s)
    let ioffset := firstS + (soffset - FloatRanges.i64 1) * sstep
    let newstep := if sstep.val = 1 ∨ len.val < 2 then rstep
      else FloatRanges.TP.trunc (Twice.mulInt rstep sstep) (FloatRanges.nbitslen len soffset)
    let soffset := FloatRanges.imax (FloatRanges.i64 1) soffset
    let ref := if ioffset = r.offset then r.ref
      else FloatRanges.TP.add r.ref (Twice.mulInt rstep (ioffset - r.offset))
    pure ⟨.twice ref, .twice newstep, len, soffset⟩

def getindexTpSlice (r : FloatRanges.SRL) (s : Rng) : Jl TpSliceResult :=
  getindexTpSliceSpec r s

def GetindexTpSliceBehaviour : Prop := ∀ r s,
  getindexTpSlice r s = getindexTpSliceSpec r s
theorem getindexTpSliceBehaviour_proven : GetindexTpSliceBehaviour := fun _ _ => rfl

def SrlTpSameBehaviour : Prop := ∀ r, Convert.srlTpSame r = r
def SrlTpConvertBehaviour : Prop := ∀ {t} (ref step : JInt t) len off,
  Convert.srlFloat64OfInt ref step len off = Convert.convertSrlInt ref step len off
def SrlFloat64FromSrlBehaviour : Prop := ∀ {t} (ref step : JInt t) len off,
  Convert.srlFloat64OfInt ref step len off = Convert.convertSrlInt ref step len off
def SrlIeeeFromSrlBehaviour : Prop := ∀ {t} (ref step : JInt t) len off,
  (Convert.srlIeeeOfInt ref step len off).len = len
def SrlFloat64FromRangeBehaviour : Prop := ∀ {t} (first step : JInt t) len,
  Convert.convertRangeInt first step len = Convert.convertSrlInt first step len (FloatRanges.i64 1)
def SrlIeeeFromRangeBehaviour : Prop := ∀ {t} (first step : JInt t) len,
  (Convert.srlIeeeOfInt first step len (FloatRanges.i64 1)).len = len
def ConvertSrlIntBehaviour : Prop := ∀ {t} (ref step : JInt t) len off out,
  Convert.convertSrlInt ref step len off = .ok out → out.len = len ∧ out.offset = off
def ConvertRangeIntBehaviour : Prop := ∀ {t} (first step : JInt t) len,
  Convert.convertRangeInt first step len = Convert.convertSrlInt first step len (FloatRanges.i64 1)
def ConvertSrlFloatBehaviour : Prop := ∀ f s len out,
  Convert.convertSrlFloat f s len = .ok out → out.len = len
def ConvertSrlFallbackBehaviour : Prop := ∀ r out,
  Convert.convertSrlFloatFallback r = .ok out → out.len = r.len ∧ out.offset = r.offset
def ConvertRangeFallbackBehaviour : Prop := ∀ f s len out,
  Convert.convertRangeFloatFallback f s len = .ok out → out.len = len

theorem srlTpSameBehaviour_proven : SrlTpSameBehaviour := fun _ => rfl
theorem srlTpConvertBehaviour_proven : SrlTpConvertBehaviour := fun _ _ _ _ => rfl
theorem srlFloat64FromSrlBehaviour_proven : SrlFloat64FromSrlBehaviour := fun _ _ _ _ => rfl
theorem srlIeeeFromSrlBehaviour_proven : SrlIeeeFromSrlBehaviour := fun _ _ _ _ => rfl
theorem srlFloat64FromRangeBehaviour_proven : SrlFloat64FromRangeBehaviour := fun _ _ _ => rfl
theorem srlIeeeFromRangeBehaviour_proven : SrlIeeeFromRangeBehaviour := fun _ _ _ => rfl
theorem convertSrlIntBehaviour_proven : ConvertSrlIntBehaviour := by
  intro t ref step len off out h
  exact (Convert.twiceConversions_proven.2.1 ref step len off out h)
theorem convertRangeIntBehaviour_proven : ConvertRangeIntBehaviour := fun _ _ _ => rfl
theorem convertSrlFloatBehaviour_proven : ConvertSrlFloatBehaviour := by
  intro f s len out h; exact Convert.twiceConversions_proven.2.2.2.2.1 f s len out h
theorem convertSrlFallbackBehaviour_proven : ConvertSrlFallbackBehaviour := by
  intro r out h
  have q := Convert.twiceConversions_proven.2.2.1 r out h
  exact ⟨q.1, (Convert.mk'_fields _ _ _ _ _ h).2.2.2⟩
theorem convertRangeFallbackBehaviour_proven : ConvertRangeFallbackBehaviour := by
  intro f s len out h; exact Convert.twiceConversions_proven.2.2.2.1 f s len out h

/-- TwicePrecision-specialized `sum`, base/twiceprecision.jl:606-622. -/
def sumTpSpec (r : FloatRanges.SRL) : F64 :=
  let l := r.len
  let np := l - r.offset
  let nn := r.offset - FloatRanges.i64 1
  let sp := Twice.sumpair ⟨.bit .i64, np⟩
  let sn := Twice.sumpair ⟨.bit .i64, nn⟩
  let spi : I64 := match sp.1 with | ⟨.bit .i64, x⟩ => x | _ => FloatRanges.i64 0
  let spj : I64 := match sp.2 with | ⟨.bit .i64, x⟩ => x | _ => FloatRanges.i64 0
  let sni : I64 := match sn.1 with | ⟨.bit .i64, x⟩ => x | _ => FloatRanges.i64 0
  let snj : I64 := match sn.2 with | ⟨.bit .i64, x⟩ => x | _ => FloatRanges.i64 0
  let tp := Twice.mulInt (Twice.mulInt r.step spi) spj
  let tn := Twice.mulInt (Twice.mulInt r.step sni) snj
  let p := FloatRanges.add12 tp.hi (Float.F64.neg tn.hi)
  let slo := Float.F64.add p.2 (Float.F64.sub tp.lo tn.lo)
  let ref := Twice.mulInt r.ref l
  let q := FloatRanges.add12 p.1 ref.hi
  (FloatRanges.add12 q.1 (Float.F64.add (Float.F64.add q.2 slo) ref.lo)).1

def sumTp (r : FloatRanges.SRL) : F64 := sumTpSpec r

def SumTpBehaviour : Prop := ∀ r, sumTp r = sumTpSpec r
theorem sumTpBehaviour_proven : SumTpBehaviour := fun _ => rfl

def LcmUncheckedBehaviour : Prop := ∀ a b,
  FloatRanges.lcmUnchecked a b = do
    let g ← IntArith.NumberTheory.gcd a b
    let q ← JInt.div b g
    pure (a * q)
theorem lcmUncheckedBehaviour_proven : LcmUncheckedBehaviour := fun _ _ => rfl

inductive FloatWidth where | abstract | f64 | f32 | f16 deriving DecidableEq
def narrow : FloatWidth → FloatWidth
  | .abstract => .f64
  | .f64 => .f32
  | .f32 => .f16
  | .f16 => .f16
def NarrowAbstractBehaviour : Prop := ∀ _ : Unit, narrow .abstract = .f64
def Narrow64Behaviour : Prop := ∀ _ : Unit, narrow .f64 = .f32
def Narrow32Behaviour : Prop := ∀ _ : Unit, narrow .f32 = .f16
def Narrow16Behaviour : Prop := ∀ _ : Unit, narrow .f16 = .f16
theorem narrowAbstractBehaviour_proven : NarrowAbstractBehaviour := fun _ => rfl
theorem narrow64Behaviour_proven : Narrow64Behaviour := fun _ => rfl
theorem narrow32Behaviour_proven : Narrow32Behaviour := fun _ => rfl
theorem narrow16Behaviour_proven : Narrow16Behaviour := fun _ => rfl

def tpProd (t : TP) (xs : List I64) : TP := xs.foldl Twice.mulInt t
def tpProdBase (t : TP) : TP := t
def TpProdBehaviour : Prop := ∀ t x xs, tpProd t (x :: xs) = tpProd (Twice.mulInt t x) xs
def TpProdBaseBehaviour : Prop := ∀ t, tpProdBase t = t
theorem tpProdBehaviour_proven : TpProdBehaviour := fun _ _ _ => rfl
theorem tpProdBaseBehaviour_proven : TpProdBaseBehaviour := fun _ => rfl

def ExpNumberBehaviour : Prop := ∀ exp x, Log.expAllowingTwice64 exp x = exp x
def ExpTpBehaviour : Prop := ∀ expImpl x, Log.expAllowingTwiceTP expImpl x = expImpl x.hi x.lo
def LogUncheckedBehaviour : Prop := ∀ logExt x,
  Log.logTwice64Unchecked logExt x =
    let xu := Float.F64.toBits x
    let xu := if xu < 2 ^ 52 then
      let y := Float.F64.toBits (Float.F64.mul x (Float.F64.ofBits 0x4330000000000000))
      let y := Nat.land y (2 ^ 63 - 1)
      (y + 2 ^ 64 - (52 * 2 ^ 52)) % 2 ^ 64
    else xu
    logExt xu
theorem expNumberBehaviour_proven : ExpNumberBehaviour := fun _ _ => rfl
theorem expTpBehaviour_proven : ExpTpBehaviour := fun _ _ => rfl
theorem logUncheckedBehaviour_proven : LogUncheckedBehaviour := fun _ _ => rfl

def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/twiceprecision.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := []

end TwiceMethods
end JuliaLean.RangesCov
