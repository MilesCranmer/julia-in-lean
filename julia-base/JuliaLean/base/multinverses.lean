import JuliaLean.base.int
import JuliaLean.base.operators
import JuliaLean.base.bool
import JuliaLean.base.number

namespace JuliaLean.base.multinverses

open JuliaLean JuliaLean.base.int

abbrev SameTypeRem := ∀ {t : IntTy}, JInt t → JInt t → Jl (JInt t)
abbrev SameTypeDivrem := ∀ {t : IntTy}, JInt t → JInt t → Jl (JInt t × JInt t)
inductive JuliaTuple : List Type → Type 2 where
  | nil : JuliaTuple []
  | cons {head : Type} {tail : List Type} (value : head) (rest : JuliaTuple tail) :
      JuliaTuple (head :: tail)

structure MethodError (Args : Type 2) where
  function : String
  arguments : Args

structure IntegerDomains (Ty : Type) where
  signed : Ty → Prop
  unsigned : Ty → Prop

/--
Julia source: base/multinverses.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Bool}) = UInt
-/
def unsignedTypeBool : IntTy := .u64

/--
Julia source: base/multinverses.jl:9-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Int8}) = UInt8
```
-/
def unsignedTypeInt8 : IntTy := .u8

/--
Julia source: base/multinverses.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Int16}) = UInt16
```
-/
def unsignedTypeInt16 : IntTy := .u16

/--
Julia source: base/multinverses.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Int32}) = UInt32
```
-/
def unsignedTypeInt32 : IntTy := .u32

/--
Julia source: base/multinverses.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Int64}) = UInt64
```
-/
def unsignedTypeInt64 : IntTy := .u64

/--
Julia source: base/multinverses.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Int128}) = UInt128
```
-/
def unsignedTypeInt128 : IntTy := .u128

/--
Julia source: base/multinverses.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{T}) where {T<:Unsigned} = T
```
-/
def unsignedTypeUnsigned {Ty : Type} (domain : IntegerDomains Ty)
    (T : Ty) (_h : domain.unsigned T) : Ty := T

/--
Julia source: base/multinverses.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Union{}}, slurp...) = throw(MethodError(unsigned, (Union{}, slurp...)))
```
-/
def unsignedTypeBottom {types : List Type} (slurp : JuliaTuple types) :
    Except (MethodError (JuliaTuple (UnionBottom :: types))) IntTy :=
  .error ⟨"unsigned", .cons UnionBottom.type slurp⟩

namespace I
export JuliaLean.base.int
  (lit add sub mul ofBool ifelse ltSame BinOpJl DivremJl remSame remT
   rem_BitSigned_Unsigned rem_Unsigned_BitSigned divrem_BitSigned_Unsigned
   divrem_Unsigned_BitSigned binop typemin zero unsigned abs signbit eq lt le
   mulSame addWrap subWrap mulWrap op_Integer rem_Bool_Type shl_Int shrU
   lshr_Int lshr_BitInteger_BitUnsigned convert flipsign)
end I

def bitDomains : IntegerDomains IntTy where
  signed := fun t => t.signed = true
  unsigned := fun t => t.signed = false

def unsignedTypeBits : IntTy → IntTy
  | .i8 => unsignedTypeInt8
  | .i16 => unsignedTypeInt16
  | .i32 => unsignedTypeInt32
  | .i64 => unsignedTypeInt64
  | .i128 => unsignedTypeInt128
  | .u8 => unsignedTypeUnsigned bitDomains .u8 rfl
  | .u16 => unsignedTypeUnsigned bitDomains .u16 rfl
  | .u32 => unsignedTypeUnsigned bitDomains .u32 rfl
  | .u64 => unsignedTypeUnsigned bitDomains .u64 rfl
  | .u128 => unsignedTypeUnsigned bitDomains .u128 rfl

/-- The `mul_hi` method from `base/int.jl`, instantiated for every BitInteger width. -/
def mulHi {t : IntTy} (a b : JInt t) : JInt t :=
  match t with
  | .i8 => mul_hi_Integer (fun x => widenTo .i16 x) a b
  | .i16 => mul_hi_Integer (fun x => widenTo .i32 x) a b
  | .i32 => mul_hi_Integer (fun x => widenTo .i64 x) a b
  | .i64 => mul_hi_Integer (fun x => widenTo .i128 x) a b
  | .i128 => mul_hi_Int128 a b
  | .u8 => mul_hi_Integer (fun x => widenTo .u16 x) a b
  | .u16 => mul_hi_Integer (fun x => widenTo .u32 x) a b
  | .u32 => mul_hi_Integer (fun x => widenTo .u64 x) a b
  | .u64 => mul_hi_Integer (fun x => widenTo .u128 x) a b
  | .u128 => mul_hi_UInt128 a b

abbrev Run (E A : Type) := Option (Except E A)

def whileLoop {E S A : Type} (step : S → Except E (Sum A S))
    (state : S) : Run E A :=
  match step state with
  | .error e => some (.error e)
  | .ok (.inl value) => some (.ok value)
  | .ok (.inr next) => whileLoop step next
partial_fixpoint

def after {E A B : Type} (r : Except E A)
    (k : A → Run E B) : Run E B :=
  match r with
  | .error e => some (.error e)
  | .ok a => k a

def continueRun {E A B : Type} (r : Run E A)
    (k : A → Run E B) : Run E B :=
  match r with
  | none => none
  | some r => after r k

structure Callees (Ty : Type) (V : Ty → Type) (D E : Type) where
  Sign : Type
  Condition : Type
  boolValue : Bool → Condition
  pack : (T : Ty) → V T → D
  int : JInt64 → D
  int8 : JInt .i8 → D
  uint8 : JInt .u8 → D
  argumentError : String → E
  render : D → Except E String
  unsignedType : Ty → Except E Ty
  typemin : Ty → Except E D
  oneType : Ty → Except E D
  oneValue : D → Except E D
  zeroValue : D → Except E D
  unsigned : D → Except E D
  abs : D → Except E D
  signbit : D → Except E Sign
  eq : D → D → Except E Bool
  lt : D → D → Except E Bool
  gt : D → D → Except E Bool
  ge : D → D → Except E Bool
  iszero : D → Except E Bool
  eqSign : Sign → Sign → Except E Bool
  eqValue : D → D → Except E Condition
  geValue : D → D → Except E Condition
  bitOr : Condition → Condition → Except E Condition
  ifelse : Condition → D → D → Except E D
  subCondition : JInt64 → Condition → Except E D
  fieldBool : Condition → Except E Bool
  fieldUInt8 : D → Except E (JInt .u8)
  add : D → D → Except E D
  sub : D → D → Except E D
  mul : D → D → Except E D
  addWrap : D → D → Except E D
  subWrap : D → D → Except E D
  mulWrap : D → D → Except E D
  addRightSign : D → Sign → Except E D
  addLeftSign : Sign → D → Except E D
  shl : D → JInt64 → Except E D
  shr : D → JInt .u8 → Except E D
  lshrOne : D → Except E D
  lshr : D → JInt .u8 → Except E D
  bitsizeof : D → Except E JInt64
  rem : D → D → Except E D
  divrem : D → D → Except E (D × D)
  remType : D → Ty → Except E D
  convert : Ty → D → Except E D
  field : (T : Ty) → D → Except E (V T)
  flipsign : D → D → Except E D
  mulHi : (T : Ty) → V T → V T → Except E D
  toUInt8 : JInt64 → Except E (JInt .u8)
  remUInt8 : D → Except E D

/--
Julia source: base/multinverses.jl:47-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct SignedMultiplicativeInverse{T<:Signed} <: MultiplicativeInverse{T}
    divisor::T
    multiplier::T
    addmul::Int8
    shift::UInt8
```
-/
structure SignedMultiplicativeInverse {Ty : Type} (V : Ty → Type)
    (domain : IntegerDomains Ty) (T : Ty) where
  typeWitness : domain.signed T
  divisor : V T
  multiplier : V T
  addmul : JInt .i8
  shift : JInt .u8

/--
Julia source: base/multinverses.jl:92-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct UnsignedMultiplicativeInverse{T<:Unsigned} <: MultiplicativeInverse{T}
    divisor::T
    multiplier::T
    add::Bool
    shift::UInt8
```
-/
structure UnsignedMultiplicativeInverse {Ty : Type} (V : Ty → Type)
    (domain : IntegerDomains Ty) (T : Ty) where
  typeWitness : domain.unsigned T
  divisor : V T
  multiplier : V T
  add : Bool
  shift : JInt .u8

structure SignedLoopState (D : Type) where
  p : JInt64
  q1 : D
  r1 : D
  q2 : D
  r2 : D

structure UnsignedLoopState (D C : Type) extends SignedLoopState D where
  add : C

def needsAnother {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) (q1 delta r1 : D) : Except E Bool := do
  if ← o.lt q1 delta then return true
  if ← o.eq q1 delta then return ← o.eq r1 (o.int (I.lit .i64 0))
  return false

def signedInverseStep {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) (UT : Ty) (anc ad : D)
    (state : SignedLoopState D) : Except E (Sum (SignedLoopState D) (SignedLoopState D)) := do
  let p := I.add state.p (I.lit .i64 1)
  let q1 ← o.shl state.q1 (I.lit .i64 1)
  let r1 ← o.shl state.r1 (I.lit .i64 1)
  let (q1, r1) ← if ← o.ge r1 anc then do
      let one ← o.oneType UT
      let q1 ← o.addWrap q1 one
      let r1 ← o.sub r1 anc
      pure (q1, r1)
    else pure (q1, r1)
  let q2 ← o.shl state.q2 (I.lit .i64 1)
  let r2 ← o.shl state.r2 (I.lit .i64 1)
  let (q2, r2) ← if ← o.ge r2 ad then do
      let one ← o.oneType UT
      let q2 ← o.addWrap q2 one
      let r2 ← o.sub r2 ad
      pure (q2, r2)
    else pure (q2, r2)
  let delta ← o.sub ad r2
  let next : SignedLoopState D := ⟨p, q1, r1, q2, r2⟩
  if ← needsAnother o q1 delta r1 then return .inr next
  return .inl next

/--
Julia source: base/multinverses.jl:65-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        while true
            p += 1                       # loop until we find a satisfactory p
            # update q1, r1 = divrem(2^p, abs(nc))
            q1 = q1<<1
            r1 = r1<<1
            if r1 >= anc                 # must be unsigned comparison
                q1 = q1 +% one(UT)
                r1 -= anc
            end
            # update q2, r2 = divrem(2^p, abs(d))
            q2 = q2<<1
            r2 = r2<<1
            if r2 >= ad
                q2 = q2 +% one(UT)
                r2 -= ad
            end
            delta = ad - r2
            (q1 < delta || (q1 == delta && r1 == 0)) || break
        end
```
-/
def signedInverseLoop {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) (UT : Ty) (anc ad : D)
    (state : SignedLoopState D) : Run E (SignedLoopState D) :=
  whileLoop (signedInverseStep o UT anc ad) state

/--
Julia source: base/multinverses.jl:53-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function SignedMultiplicativeInverse{T}(d::T) where T<:Signed
        d == 0 && throw(ArgumentError("cannot compute magic for d == $d"))
        signedmin = unsigned(typemin(T))
        UT = unsigned(T)

        # Algorithm from Hacker's Delight, section 10-4
        ad = unsigned(abs(d))
        t = signedmin + signbit(d)
        anc = t - one(UT) - rem(t, ad)   # absolute value of nc
        p = Core.bitsizeof(d) - 1
        q1, r1 = divrem(signedmin, anc)
        q2, r2 = divrem(signedmin, ad)
        while true
            p += 1                       # loop until we find a satisfactory p
            # update q1, r1 = divrem(2^p, abs(nc))
            q1 = q1<<1
            r1 = r1<<1
            if r1 >= anc                 # must be unsigned comparison
                q1 = q1 +% one(UT)
                r1 -= anc
            end
            # update q2, r2 = divrem(2^p, abs(d))
            q2 = q2<<1
            r2 = r2<<1
            if r2 >= ad
                q2 = q2 +% one(UT)
                r2 -= ad
            end
            delta = ad - r2
            (q1 < delta || (q1 == delta && r1 == 0)) || break
        end

        m = flipsign((q2 +% one(UT)) % T, d)  # resulting magic number
        s = p - Core.bitsizeof(d)            # resulting shift
        new(d, m, d > 0 && m < 0 ? Int8(1) : d < 0 && m > 0 ? Int8(-1) : Int8(0), UInt8(s))
    end
```
-/
def signedInverseConstructor {Ty D E : Type} {V : Ty → Type}
    (domain : IntegerDomains Ty) (o : Callees Ty V D E)
    {T : Ty} (h : domain.signed T) (d : V T) :
    Run E (SignedMultiplicativeInverse V domain T) :=
  after initialState fun (UT, anc, ad, state) =>
    continueRun (signedInverseLoop o UT anc ad state) fun state => some (do
      let one ← o.oneType UT
      let q2 ← o.addWrap state.q2 one
      let q2 ← o.remType q2 T
      let m ← o.flipsign q2 (o.pack T d)
      let width ← o.bitsizeof (o.pack T d)
      let s := I.sub state.p width
      let addmul ← if ← o.gt (o.pack T d) (o.int (I.lit .i64 0)) then do
          if ← o.lt m (o.int (I.lit .i64 0)) then pure (I.lit .i8 1)
          else negativeCase m
        else negativeCase m
      let shift ← o.toUInt8 s
      let multiplier ← o.field T m
      pure ⟨h, d, multiplier, addmul, shift⟩)
where
  initialState : Except E (Ty × D × D × SignedLoopState D) := do
    let dval := o.pack T d
    if ← o.eq dval (o.int (I.lit .i64 0)) then
      let text ← o.render dval
      throw (o.argumentError ("cannot compute magic for d == " ++ text))
    let minimum ← o.typemin T
    let signedmin ← o.unsigned minimum
    let UT ← o.unsignedType T
    let absd ← o.abs dval
    let ad ← o.unsigned absd
    let sign ← o.signbit dval
    let t ← o.addRightSign signedmin sign
    let one ← o.oneType UT
    let first ← o.sub t one
    let remainder ← o.rem t ad
    let anc ← o.sub first remainder
    let width ← o.bitsizeof dval
    let p := I.sub width (I.lit .i64 1)
    let (q1, r1) ← o.divrem signedmin anc
    let (q2, r2) ← o.divrem signedmin ad
    pure (UT, anc, ad, ⟨p, q1, r1, q2, r2⟩)
  negativeCase (m : D) : Except E (JInt .i8) := do
    if ← o.lt (o.pack T d) (o.int (I.lit .i64 0)) then
      if ← o.gt m (o.int (I.lit .i64 0)) then return I.lit .i8 (-1)
    return I.lit .i8 0

def unsignedInverseStep {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) (T : Ty) (d nc signedmin signedmax : D)
    (state : UnsignedLoopState D o.Condition) :
    Except E (Sum (UnsignedLoopState D o.Condition) (UnsignedLoopState D o.Condition)) := do
  let p := I.add state.p (I.lit .i64 1)
  let difference ← o.sub nc state.r1
  let threshold ← o.convert T difference
  let (q1, r1) ← if ← o.ge state.r1 threshold then do
      let q1 ← o.addWrap state.q1 state.q1
      let one ← o.oneType T
      let q1 ← o.addWrap q1 one
      let r1 ← o.addWrap state.r1 state.r1
      let r1 ← o.subWrap r1 nc
      pure (q1, r1)
    else do
      let q1 ← o.addWrap state.q1 state.q1
      let r1 ← o.addWrap state.r1 state.r1
      pure (q1, r1)
  let one ← o.oneType T
  let left ← o.addWrap state.r2 one
  let left ← o.convert T left
  let right ← o.subWrap d state.r2
  let right ← o.convert T right
  let (q2, r2, add) ← if ← o.ge left right then do
      let comparison ← o.geValue state.q2 signedmax
      let add ← o.bitOr state.add comparison
      let q2 ← o.addWrap state.q2 state.q2
      let one ← o.oneType T
      let q2 ← o.addWrap q2 one
      let r2 ← o.addWrap state.r2 state.r2
      let one ← o.oneType T
      let r2 ← o.addWrap r2 one
      let r2 ← o.subWrap r2 d
      pure (q2, r2, add)
    else do
      let comparison ← o.geValue state.q2 signedmin
      let add ← o.bitOr state.add comparison
      let q2 ← o.addWrap state.q2 state.q2
      let r2 ← o.addWrap state.r2 state.r2
      let one ← o.oneType T
      let r2 ← o.addWrap r2 one
      pure (q2, r2, add)
  let one ← o.oneType T
  let delta ← o.subWrap d one
  let delta ← o.subWrap delta r2
  let width ← o.bitsizeof d
  let limit := I.mul (I.lit .i64 2) width
  let next : UnsignedLoopState D o.Condition := ⟨⟨p, q1, r1, q2, r2⟩, add⟩
  if I.ltSame p limit then
    if ← needsAnother o q1 delta r1 then return .inr next
  return .inl next

/--
Julia source: base/multinverses.jl:109-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        while true
            p += 1
            if r1 >= convert(T, nc - r1)
                q1 = q1 +% q1 +% one(T)
                r1 = r1 +% r1 -% nc
            else
                q1 = q1 +% q1
                r1 = r1 +% r1
            end
            if convert(T, r2 +% one(T)) >= convert(T, d -% r2)
                add |= q2 >= signedmax
                q2 = q2 +% q2 +% one(T)
                r2 = r2 +% r2 +% one(T) -% d
            else
                add |= q2 >= signedmin
                q2 = q2 +% q2
                r2 = r2 +% r2 +% one(T)
            end
            delta = d -% one(T) -% r2
            (p < 2*Core.bitsizeof(d) && (q1 < delta || (q1 == delta && r1 == 0))) || break
        end
```
-/
def unsignedInverseLoop {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) (T : Ty) (d nc signedmin signedmax : D)
    (state : UnsignedLoopState D o.Condition) : Run E (UnsignedLoopState D o.Condition) :=
  whileLoop (unsignedInverseStep o T d nc signedmin signedmax) state

/--
Julia source: base/multinverses.jl:98-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function UnsignedMultiplicativeInverse{T}(d::T) where T<:Unsigned
        d == 0 && throw(ArgumentError("cannot compute magic for d == $d"))
        add = false
        signedmin = one(d) << (Core.bitsizeof(d)-1)
        signedmax = signedmin - one(T)
        allones = (zero(d) -% one(T)) % T

        nc = allones - rem(convert(T, allones - d), d)
        p = Core.bitsizeof(d) - 1
        q1, r1 = divrem(signedmin, nc)
        q2, r2 = divrem(signedmax, d)
        while true
            p += 1
            if r1 >= convert(T, nc - r1)
                q1 = q1 +% q1 +% one(T)
                r1 = r1 +% r1 -% nc
            else
                q1 = q1 +% q1
                r1 = r1 +% r1
            end
            if convert(T, r2 +% one(T)) >= convert(T, d -% r2)
                add |= q2 >= signedmax
                q2 = q2 +% q2 +% one(T)
                r2 = r2 +% r2 +% one(T) -% d
            else
                add |= q2 >= signedmin
                q2 = q2 +% q2
                r2 = r2 +% r2 +% one(T)
            end
            delta = d -% one(T) -% r2
            (p < 2*Core.bitsizeof(d) && (q1 < delta || (q1 == delta && r1 == 0))) || break
        end
        m = q2 +% one(T)             # resulting magic number
        s = p - Core.bitsizeof(d) - add    # resulting shift
        new(d, m, add, s % UInt8)
    end
```
-/
def unsignedInverseConstructor {Ty D E : Type} {V : Ty → Type}
    (domain : IntegerDomains Ty) (o : Callees Ty V D E)
    {T : Ty} (h : domain.unsigned T) (d : V T) :
    Run E (UnsignedMultiplicativeInverse V domain T) :=
  after initialState fun (nc, signedmin, signedmax, state) =>
    continueRun (unsignedInverseLoop o T (o.pack T d) nc signedmin signedmax state)
      fun state => some (do
        let one ← o.oneType T
        let m ← o.addWrap state.q2 one
        let width ← o.bitsizeof (o.pack T d)
        let s ← o.subCondition (I.sub state.p width) state.add
        let shiftValue ← o.remUInt8 s
        let multiplier ← o.field T m
        let add ← o.fieldBool state.add
        let shift ← o.fieldUInt8 shiftValue
        pure ⟨h, d, multiplier, add, shift⟩)
where
  initialState : Except E (D × D × D × UnsignedLoopState D o.Condition) := do
    let dval := o.pack T d
    if ← o.eq dval (o.int (I.lit .i64 0)) then
      let text ← o.render dval
      throw (o.argumentError ("cannot compute magic for d == " ++ text))
    let add := o.boolValue false
    let one ← o.oneValue dval
    let width ← o.bitsizeof dval
    let signedmin ← o.shl one (I.sub width (I.lit .i64 1))
    let one ← o.oneType T
    let signedmax ← o.sub signedmin one
    let zero ← o.zeroValue dval
    let one ← o.oneType T
    let allones ← o.subWrap zero one
    let allones ← o.remType allones T
    let difference ← o.sub allones dval
    let converted ← o.convert T difference
    let remainder ← o.rem converted dval
    let nc ← o.sub allones remainder
    let width ← o.bitsizeof dval
    let p := I.sub width (I.lit .i64 1)
    let (q1, r1) ← o.divrem signedmin nc
    let (q2, r2) ← o.divrem signedmax dval
    pure (nc, signedmin, signedmax, ⟨⟨p, q1, r1, q2, r2⟩, add⟩)

/--
Julia source: base/multinverses.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SignedMultiplicativeInverse(x::Signed) = SignedMultiplicativeInverse{typeof(x)}(x)
```
-/
def signedMultiplicativeInverse {Ty D E : Type} {V : Ty → Type}
    (domain : IntegerDomains Ty) (o : Callees Ty V D E)
    {T : Ty} (h : domain.signed T) (x : V T) :=
  signedInverseConstructor domain o h x

/--
Julia source: base/multinverses.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UnsignedMultiplicativeInverse(x::Unsigned) = UnsignedMultiplicativeInverse{typeof(x)}(x)
```
-/
def unsignedMultiplicativeInverse {Ty D E : Type} {V : Ty → Type}
    (domain : IntegerDomains Ty) (o : Callees Ty V D E)
    {T : Ty} (h : domain.unsigned T) (x : V T) :=
  unsignedInverseConstructor domain o h x

/--
Julia source: base/multinverses.jl:137-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(a::T, b::SignedMultiplicativeInverse{T}) where T
    x = mul_hi(a, b.multiplier)
    x = x +% ((a *% b.addmul) % T)
    ifelse(abs(b.divisor) == 1, a*b.divisor, (signbit(x) + (x >> b.shift)) % T)
end
```
-/
def divSignedInverse {Ty D E : Type} {V : Ty → Type}
    {domain : IntegerDomains Ty} (o : Callees Ty V D E)
    {T : Ty} (a : V T) (b : SignedMultiplicativeInverse V domain T) : Except E D := do
  let x ← o.mulHi T a b.multiplier
  let product ← o.mulWrap (o.pack T a) (o.int8 b.addmul)
  let product ← o.remType product T
  let x ← o.addWrap x product
  let absd ← o.abs (o.pack T b.divisor)
  let condition ← o.eqValue absd (o.int (I.lit .i64 1))
  let yes ← o.mul (o.pack T a) (o.pack T b.divisor)
  let sign ← o.signbit x
  let shifted ← o.shr x b.shift
  let sum ← o.addLeftSign sign shifted
  let no ← o.remType sum T
  o.ifelse condition yes no

/--
Julia source: base/multinverses.jl:142-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(a::T, b::UnsignedMultiplicativeInverse{T}) where T
    x = mul_hi(a, b.multiplier)
    x = ifelse(b.add, convert(T, convert(T, (convert(T, a -% x) >>> 1)) +% x), x)
    ifelse(b.divisor == 1, a, x >>> b.shift)
end
```
-/
def divUnsignedInverse {Ty D E : Type} {V : Ty → Type}
    {domain : IntegerDomains Ty} (o : Callees Ty V D E)
    {T : Ty} (a : V T) (b : UnsignedMultiplicativeInverse V domain T) : Except E D := do
  let x ← o.mulHi T a b.multiplier
  let difference ← o.subWrap (o.pack T a) x
  let difference ← o.convert T difference
  let half ← o.lshrOne difference
  let half ← o.convert T half
  let sum ← o.addWrap half x
  let yes ← o.convert T sum
  let x ← o.ifelse (o.boolValue b.add) yes x
  let condition ← o.eqValue (o.pack T b.divisor) (o.int (I.lit .i64 1))
  let no ← o.lshr x b.shift
  o.ifelse condition (o.pack T a) no

/--
Julia source: base/multinverses.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type  MultiplicativeInverse{T} <: Number end
```
-/
structure MultiplicativeInverse {Ty : Type} (V : Ty → Type) (D E : Type) (T : Ty) where
  Payload : Type
  value : Payload
  getDivisor : Payload → Except E D
  divide : V T → Payload → Except E D

def signedView {Ty D E : Type} {V : Ty → Type}
    {domain : IntegerDomains Ty} (o : Callees Ty V D E)
    {T : Ty} (b : SignedMultiplicativeInverse V domain T) :
    MultiplicativeInverse V D E T where
  Payload := SignedMultiplicativeInverse V domain T
  value := b
  getDivisor := fun b => pure (o.pack T b.divisor)
  divide := divSignedInverse o

def unsignedView {Ty D E : Type} {V : Ty → Type}
    {domain : IntegerDomains Ty} (o : Callees Ty V D E)
    {T : Ty} (b : UnsignedMultiplicativeInverse V domain T) :
    MultiplicativeInverse V D E T where
  Payload := UnsignedMultiplicativeInverse V domain T
  value := b
  getDivisor := fun b => pure (o.pack T b.divisor)
  divide := divUnsignedInverse o

def divInverse {Ty D E : Type} {V : Ty → Type} {T : Ty}
    (a : V T) (b : MultiplicativeInverse V D E T) : Except E D :=
  b.divide a b.value

/--
Julia source: base/multinverses.jl:148-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(a::T, b::MultiplicativeInverse{T}) where {T} =
    a - div(a, b)*b.divisor
```
-/
def rem {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) {T : Ty} (a : V T)
    (b : MultiplicativeInverse V D E T) : Except E D := do
  let q ← divInverse a b
  let divisor ← b.getDivisor b.value
  let product ← o.mul q divisor
  o.sub (o.pack T a) product

/--
Julia source: base/multinverses.jl:151-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(a::T, b::MultiplicativeInverse{T}) where T
    d = div(a, b)
    (d, a - d*b.divisor)
end
```
-/
def divremInverse {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) {T : Ty} (a : V T)
    (b : MultiplicativeInverse V D E T) : Except E (D × D) := do
  let q ← divInverse a b
  let divisor ← b.getDivisor b.value
  let product ← o.mul q divisor
  let r ← o.sub (o.pack T a) product
  pure (q, r)

/--
Julia source: base/multinverses.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(a::T, b::UnsignedMultiplicativeInverse{T}) where {T} = rem(a, b)
```
-/
def modUnsignedInverse {Ty D E : Type} {V : Ty → Type}
    {domain : IntegerDomains Ty} (o : Callees Ty V D E) {T : Ty}
    (a : V T) (b : UnsignedMultiplicativeInverse V domain T) : Except E D :=
  rem o a (unsignedView o b)

/--
Julia source: base/multinverses.jl:158-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mod(a::T, b::SignedMultiplicativeInverse{T}) where {T}
    r = rem(a, b)
    return (iszero(r) || signbit(r) == signbit(b.divisor)) ? r : r + b.divisor
end
```
-/
def modSignedInverse {Ty D E : Type} {V : Ty → Type}
    {domain : IntegerDomains Ty} (o : Callees Ty V D E) {T : Ty}
    (a : V T) (b : SignedMultiplicativeInverse V domain T) : Except E D := do
  let r ← rem o a (signedView o b)
  if ← o.iszero r then return r
  let rsign ← o.signbit r
  let dsign ← o.signbit (o.pack T b.divisor)
  if ← o.eqSign rsign dsign then return r
  o.add r (o.pack T b.divisor)

/--
Julia source: base/multinverses.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
multiplicativeinverse(x::Signed) = SignedMultiplicativeInverse(x)
```
-/
def multiplicativeinverseSigned {Ty D E : Type} {V : Ty → Type}
    (domain : IntegerDomains Ty) (o : Callees Ty V D E)
    {T : Ty} (h : domain.signed T) (x : V T) :=
  signedMultiplicativeInverse domain o h x

/--
Julia source: base/multinverses.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
multiplicativeinverse(x::Unsigned) = UnsignedMultiplicativeInverse(x)
```
-/
def multiplicativeinverseUnsigned {Ty D E : Type} {V : Ty → Type}
    (domain : IntegerDomains Ty) (o : Callees Ty V D E)
    {T : Ty} (h : domain.unsigned T) (x : V T) :=
  unsignedMultiplicativeInverse domain o h x

abbrev Bits := Sigma JInt

inductive BitsMultiplicativeInverse (t : IntTy) where
  | signed (inverse : SignedMultiplicativeInverse JInt bitDomains t)
  | unsigned (inverse : UnsignedMultiplicativeInverse JInt bitDomains t)

def bitsBin (op : {t : IntTy} → JInt t → JInt t → JInt t)
    (x y : Bits) : Bits :=
  ⟨x.1.promote y.1, I.binop op x.2 y.2⟩

def promotedRem : I.BinOpJl := fun {s t} a b =>
  I.remSame (I.remT (s.promote t) a) (I.remT (s.promote t) b)

def promotedDivrem (f : SameTypeDivrem) : I.DivremJl := fun {s t} a b =>
  f (I.remT (s.promote t) a) (I.remT (s.promote t) b)

def bitsRem (x y : Bits) : Jl Bits := do
  if x.1.signed = y.1.signed then
    return ⟨x.1.promote y.1, ← promotedRem x.2 y.2⟩
  else if x.1.signed then
    return ⟨(x.1.toUnsigned.promote y.1).toSigned,
      ← I.rem_BitSigned_Unsigned promotedRem x.2 y.2⟩
  else
    return ⟨x.1.promote y.1.toUnsigned,
      ← I.rem_Unsigned_BitSigned promotedRem x.2 y.2⟩

def bitsDivrem (f : SameTypeDivrem) (x y : Bits) : Jl (Bits × Bits) := do
  if x.1.signed = y.1.signed then
    let (q, r) ← promotedDivrem f x.2 y.2
    return (⟨x.1.promote y.1, q⟩, ⟨x.1.promote y.1, r⟩)
  else if x.1.signed then
    let (q, r) ← I.divrem_BitSigned_Unsigned (promotedDivrem f) x.2 y.2
    return (⟨(x.1.toUnsigned.promote y.1).toSigned, q⟩,
      ⟨(x.1.toUnsigned.promote y.1).toSigned, r⟩)
  else
    let (q, r) ← I.divrem_Unsigned_BitSigned (promotedDivrem f) x.2 y.2
    return (⟨(x.1.promote y.1.toUnsigned).toSigned.toUnsigned, q⟩,
      ⟨x.1.promote y.1.toUnsigned, r⟩)

def bitsIszeroCall {t : IntTy} (x : JInt t) : Jl Bool :=
  JuliaLean.base.number.iszero
    (fun x => .ok (I.zero x))
    (fun x y => .ok (I.eq x y)) x

def bitsCallees (f : SameTypeDivrem)
    (render : Bits → Jl String := fun x => pure (toString x.2.val)) :
    Callees IntTy JInt Bits JlError where
  Sign := Bool
  Condition := Bool
  boolValue := id
  pack := fun t x => ⟨t, x⟩
  int := fun x => ⟨.i64, x⟩
  int8 := fun x => ⟨.i8, x⟩
  uint8 := fun x => ⟨.u8, x⟩
  argumentError := JlError.argumentError
  render := render
  unsignedType := fun t => pure (unsignedTypeBits t)
  typemin := fun t => pure ⟨t, I.typemin t⟩
  oneType := fun t => pure ⟨t, I.lit t 1⟩
  oneValue := fun x => pure ⟨x.1, I.lit x.1 1⟩
  zeroValue := fun x => pure ⟨x.1, I.zero x.2⟩
  unsigned := fun x => pure ⟨x.1.toUnsigned, I.unsigned x.2⟩
  abs := fun x => pure ⟨x.1, I.abs x.2⟩
  signbit := fun x => pure (I.signbit x.2)
  eq := fun x y => pure (I.eq x.2 y.2)
  lt := fun x y => pure (I.lt x.2 y.2)
  gt := fun x y => pure (JuliaLean.base.operators.greaterThan I.lt x.2 y.2)
  ge := fun x y => pure (JuliaLean.base.operators.greaterEqual I.le x.2 y.2)
  iszero := fun x => bitsIszeroCall x.2
  eqSign := fun x y => pure (x == y)
  eqValue := fun x y => pure (I.eq x.2 y.2)
  geValue := fun x y => pure (JuliaLean.base.operators.greaterEqual I.le x.2 y.2)
  bitOr := fun x y => pure (JuliaLean.base.bool.orBool x y)
  ifelse := fun condition yes no => pure (I.ifelse condition yes no)
  subCondition := fun x b => pure ⟨.i64,
    I.op_Integer .i64 I.sub (I.remT .i64) (I.rem_Bool_Type .i64) x b⟩
  fieldBool := fun b => pure b
  fieldUInt8 := fun x => I.convert .u8 x.2
  add := fun x y => pure (bitsBin I.add x y)
  sub := fun x y => pure (bitsBin I.sub x y)
  mul := fun x y => pure (bitsBin I.mulSame x y)
  addWrap := fun x y => pure (bitsBin I.addWrap x y)
  subWrap := fun x y => pure (bitsBin I.subWrap x y)
  mulWrap := fun x y => pure (bitsBin I.mulWrap x y)
  addRightSign := fun x b => pure ⟨x.1,
    I.op_Integer x.1 I.add (I.remT x.1) (I.rem_Bool_Type x.1) x.2 b⟩
  addLeftSign := fun b x => pure ⟨x.1,
    I.op_Integer x.1 I.add (I.rem_Bool_Type x.1) (I.remT x.1) b x.2⟩
  shl := fun x n => pure ⟨x.1, I.shl_Int x.2 n⟩
  shr := fun x n => pure ⟨x.1, I.shrU x.2 n⟩
  lshrOne := fun x => pure ⟨x.1, I.lshr_Int x.2 (I.lit .i64 1)⟩
  lshr := fun x n => pure ⟨x.1, I.lshr_BitInteger_BitUnsigned x.2 n⟩
  bitsizeof := fun x => pure (I.lit .i64 x.1.bits)
  rem := bitsRem
  divrem := bitsDivrem f
  remType := fun x t => pure ⟨t, I.remT t x.2⟩
  convert := fun t x => do return ⟨t, ← I.convert t x.2⟩
  field := fun t x => I.convert t x.2
  flipsign := fun x y => pure ⟨x.1, I.flipsign x.2 y.2⟩
  mulHi := fun t a b => pure ⟨t, JuliaLean.base.multinverses.mulHi a b⟩
  toUInt8 := I.convert .u8
  remUInt8 := fun x => pure ⟨.u8, I.remT .u8 x.2⟩

abbrev bitsCalleesSource := bitsCallees

end JuliaLean.base.multinverses

namespace JuliaLean.IntArith.NumberTheory

/-- Unsigned multiplicative inverse fields, `base/multinverses.jl:92-96`. -/
structure UnsignedMI (t : IntTy) where
  divisor : JInt t
  multiplier : JInt t
  add : Bool
  shift : Nat

/-- Unsigned magic-number constructor loop, `base/multinverses.jl:109-132`.
The source explicitly stops at `p == 2*bits`; that test proves termination.
Every recurrence is evaluated in its original wrapping unsigned type. -/
def magicLoop (t : IntTy) (d nc : JInt t) (p : Nat)
    (q1 r1 q2 r2 : JInt t) (addFlag : Bool) : UnsignedMI t :=
  let one := JInt.lit t 1
  let signedmin := JInt.wrap t (2 ^ (t.bits - 1))
  let signedmax := signedmin - one
  let (q1, r1) := if r1 ≥ nc - r1 then
    (q1 + q1 + one, r1 + r1 - nc) else (q1 + q1, r1 + r1)
  let (q2, r2, addFlag) := if r2 + one ≥ d - r2 then
    (q2 + q2 + one, r2 + r2 + one - d, addFlag || decide (q2 ≥ signedmax))
    else (q2 + q2, r2 + r2 + one, addFlag || decide (q2 ≥ signedmin))
  let delta := d - one - r2
  if p + 1 < 2 * t.bits ∧ (q1 < delta ∨ (q1 = delta ∧ r1.val = 0)) then
    magicLoop t d nc (p + 1) q1 r1 q2 r2 addFlag
  else
    ⟨d, q2 + one, addFlag,
      (JInt.wrap .u8 (((p + 1 : Nat) : Int) - (t.bits : Int) - (if addFlag then 1 else 0))).val.toNat⟩
termination_by 2 * t.bits - p
decreasing_by omega

/-- Unsigned magic-number constructor, `base/multinverses.jl:98-108`. -/
def unsignedMI {t : IntTy} (d : JInt t) : Jl (UnsignedMI t) := do
  if d.val = 0 then .error (.argumentError "")
  else
    let one := JInt.lit t 1
    let signedmin := JInt.wrap t (2 ^ (t.bits - 1))
    let signedmax := signedmin - one
    let allones := JInt.lit t 0 - one
    let nc := allones - (← JInt.remInt (allones - d) d)
    let q1 ← JInt.div signedmin nc
    let r1 ← JInt.remInt signedmin nc
    let q2 ← JInt.div signedmax d
    let r2 ← JInt.remInt signedmax d
    pure (magicLoop t d nc (t.bits - 1) q1 r1 q2 r2 false)

/-- Unsigned inverse division and remainder,
`base/multinverses.jl:142-149,156`. `mul_hi` is the high half of the
explicitly widened wrapping product, `base/int.jl:123-124`. -/
def magicMod {t : IntTy} (a : JInt t) (mi : UnsignedMI t) : JInt t :=
  let x := JInt.wrap t (mul (widen t) a.val mi.multiplier.val / (2 ^ t.bits : Int))
  let x := if mi.add then shiftRight (a - x) 1 + x else x
  let q := if mi.divisor.val = 1 then a else shiftRight x mi.shift
  a - q * mi.divisor

end JuliaLean.IntArith.NumberTheory

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- Fields of `SignedMultiplicativeInverse{T}`, `base/multinverses.jl:47-51`. -/
structure SignedMI (t : IntTy) where
  divisor : JInt t
  multiplier : JInt t
  addmul : JInt .i8
  shift : JInt .u8
  deriving DecidableEq, Repr

/-- Loop state of the signed constructor, `base/multinverses.jl:62-64`. -/
structure SmiState (t : IntTy) where
  p : JInt .i64
  q1 : JInt t.toUnsigned
  r1 : JInt t.toUnsigned
  q2 : JInt t.toUnsigned
  r2 : JInt t.toUnsigned
  deriving DecidableEq, Repr

/-- Inputs computed before the loop, `base/multinverses.jl:54-64`: `anc`, `ad` and the
initial state. -/
def smiPre {t : IntTy} (d : JInt t) : Jl (JInt t.toUnsigned × JInt t.toUnsigned × SmiState t) := do
  if d.val = 0 then throw (.argumentError "cannot compute magic for d == 0")
  let signedmin : JInt t.toUnsigned := JInt.rem t.toUnsigned (JInt.typemin t)
  let ad : JInt t.toUnsigned := JInt.rem t.toUnsigned (jabs d)
  let tt : JInt t.toUnsigned := signedmin + JInt.lit t.toUnsigned (if d.val < 0 then 1 else 0)
  let anc := tt - JInt.lit t.toUnsigned 1 - (← JInt.remInt tt ad)
  let p : JInt .i64 := JInt.lit .i64 ((t.bits : Int) - 1)
  let q1 ← JInt.div signedmin anc
  let r1 ← JInt.remInt signedmin anc
  let q2 ← JInt.div signedmin ad
  let r2 ← JInt.remInt signedmin ad
  pure (anc, ad, ⟨p, q1, r1, q2, r2⟩)

/-- One pass of the loop body, `base/multinverses.jl:66-80`. -/
def smiStep {t : IntTy} (anc ad : JInt t.toUnsigned) (s : SmiState t) : SmiState t :=
  let one := JInt.lit t.toUnsigned 1
  let q1 := shl1 s.q1
  let r1 := shl1 s.r1
  let (q1, r1) := if r1 ≥ anc then (q1 + one, r1 - anc) else (q1, r1)
  let q2 := shl1 s.q2
  let r2 := shl1 s.r2
  let (q2, r2) := if r2 ≥ ad then (q2 + one, r2 - ad) else (q2, r2)
  ⟨s.p + JInt.lit .i64 1, q1, r1, q2, r2⟩

/-- Loop condition, `base/multinverses.jl:81-82`. -/
def smiContinue {t : IntTy} (ad : JInt t.toUnsigned) (s : SmiState t) : Prop :=
  let delta := ad - s.r2
  s.q1 < delta ∨ (s.q1 = delta ∧ s.r1.val = 0)

instance {t : IntTy} (ad : JInt t.toUnsigned) (s : SmiState t) : Decidable (smiContinue ad s) := by
  unfold smiContinue; infer_instance

/-- The `while true` loop, `base/multinverses.jl:65-83`, as a big-step relation: `SmiLoop anc ad s r`
holds when the loop started in state `s` terminates in state `r`. -/
inductive SmiLoop {t : IntTy} (anc ad : JInt t.toUnsigned) : SmiState t → SmiState t → Prop
  | stop (s : SmiState t) : ¬ smiContinue ad (smiStep anc ad s) → SmiLoop anc ad s (smiStep anc ad s)
  | next (s r : SmiState t) : smiContinue ad (smiStep anc ad s) →
      SmiLoop anc ad (smiStep anc ad s) r → SmiLoop anc ad s r

/-- Result fields, `base/multinverses.jl:85-87`. -/
def smiFinish {t : IntTy} (d : JInt t) (s : SmiState t) : Jl (SignedMI t) := do
  let m := flipsign (JInt.rem t (s.q2 + JInt.lit t.toUnsigned 1)) d
  let sh := s.p - JInt.lit .i64 (t.bits : Int)
  let addmul : JInt .i8 :=
    if d.val > 0 ∧ m.val < 0 then JInt.lit .i8 1
    else if d.val < 0 ∧ m.val > 0 then JInt.lit .i8 (-1) else JInt.lit .i8 0
  let shift ← JInt.convert (IntTy.u8.name) .u8 sh.val
  pure ⟨d, m, addmul, shift⟩

/-- `SignedMultiplicativeInverse{T}(d)`, `base/multinverses.jl:53-88`: `SmiNew d mi` holds when the
constructor returns `mi`. -/
def SmiNew {t : IntTy} (d : JInt t) (mi : SignedMI t) : Prop :=
  ∃ anc ad s0 s, smiPre d = .ok (anc, ad, s0) ∧ SmiLoop anc ad s0 s ∧ smiFinish d s = .ok mi
/-- `div(a, b::SignedMultiplicativeInverse)`, `base/multinverses.jl:137-141`. `a *% b.addmul`
promotes the `Int8` to `T`; `signbit(x) + (x >> shift)` promotes the `Bool` to `T`. -/
def smiDiv {t : IntTy} (a : JInt t) (b : SignedMI t) : JInt t :=
  let x := mulHi a b.multiplier
  let x := x + JInt.rem t (a * JInt.rem t b.addmul)
  if (jabs b.divisor).val = 1 then a * b.divisor
  else JInt.rem t (JInt.lit t (if x.val < 0 then 1 else 0) + shr x b.shift.val.toNat)

/-- `rem(a, b::MultiplicativeInverse)`, `base/multinverses.jl:148-149`. -/
def smiRem {t : IntTy} (a : JInt t) (b : SignedMI t) : JInt t := a - smiDiv a b * b.divisor

/-- `mod(a, b::SignedMultiplicativeInverse)`, `base/multinverses.jl:158-161`. -/
def smiMod {t : IntTy} (a : JInt t) (b : SignedMI t) : JInt t :=
  let r := smiRem a b
  if r.val = 0 ∨ (decide (r.val < 0) = decide (b.divisor.val < 0)) then r else r + b.divisor

/-- `div(a, b::UnsignedMultiplicativeInverse)`, `base/multinverses.jl:142-146`, on the constructor
model `IntArith.NumberTheory.unsignedMI` (`base/multinverses.jl:98-133`). -/
def umiDiv {t : IntTy} (a : JInt t) (b : IntArith.NumberTheory.UnsignedMI t) : JInt t :=
  let x := mulHi a b.multiplier
  let x := if b.add then shr (a - x) 1 + x else x
  if b.divisor.val = 1 then a else shr x b.shift

/-- `rem(a, b)` and `mod(a, b)` for an unsigned inverse, `base/multinverses.jl:148-149,156`. -/
def umiRem {t : IntTy} (a : JInt t) (b : IntArith.NumberTheory.UnsignedMI t) : JInt t :=
  a - umiDiv a b * b.divisor

end JuliaLean.ReinterpretArrays
