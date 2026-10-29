import JuliaLean.base.int

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

/--
Julia source: base/multinverses.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Bool}) = UInt
```
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
def unsignedTypeUnsigned (t : IntTy) (_h : t.signed = false) : IntTy := t

/--
Julia source: base/multinverses.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(::Type{Union{}}, slurp...) = throw(MethodError(unsigned, (Union{}, slurp...)))
```
-/
def unsignedTypeBottom {types : List Type} (slurp : JuliaTuple types) :
    Except (MethodError (JuliaTuple (UnionBottom :: types))) IntTy :=
  .error ⟨"unsigned", .cons UnionBottom.type slurp⟩


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
structure SignedMultiplicativeInverse (t : IntTy) where
  typeWitness : t.signed = true
  divisor : JInt t
  multiplier : JInt t
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
structure UnsignedMultiplicativeInverse (t : IntTy) where
  typeWitness : t.signed = false
  divisor : JInt t
  multiplier : JInt t
  add : Bool
  shift : JInt .u8
/--
Julia source: base/multinverses.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type  MultiplicativeInverse{T} <: Number end
```
-/
inductive MultiplicativeInverse (t : IntTy) where
  | signed (inverse : SignedMultiplicativeInverse t)
  | unsigned (inverse : UnsignedMultiplicativeInverse t)

/-- The loop variables updated by the unsigned constructor. -/
structure UnsignedLoopState (t : IntTy) where
  p : Nat
  q1 : JInt t
  r1 : JInt t
  q2 : JInt t
  r2 : JInt t
  add : Bool

/-- The loop variables updated by the signed constructor. -/
structure SignedLoopState (t : IntTy) where
  p : Nat
  q1 : JInt t
  r1 : JInt t
  q2 : JInt t
  r2 : JInt t

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
def signedInverseLoop {t : IntTy} (anc ad : JInt t) :
    Nat → SignedLoopState t → SignedLoopState t
  | 0, state => state
  | fuel + 1, state =>
      let p := state.p + 1
      let one := JInt.lit t 1
      let q1 := shl_int state.q1 (JInt.lit .i64 1)
      let r1 := shl_int state.r1 (JInt.lit .i64 1)
      let (q1, r1) :=
        if r1.val ≥ anc.val then (addWrap q1 one, subWrap r1 anc) else (q1, r1)
      let q2 := shl_int state.q2 (JInt.lit .i64 1)
      let r2 := shl_int state.r2 (JInt.lit .i64 1)
      let (q2, r2) :=
        if r2.val ≥ ad.val then (addWrap q2 one, subWrap r2 ad) else (q2, r2)
      let delta := subWrap ad r2
      let next : SignedLoopState t := ⟨p, q1, r1, q2, r2⟩
      if q1.val < delta.val ∨ (q1.val = delta.val ∧ r1.val = 0) then
        signedInverseLoop anc ad fuel next
      else next

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
def signedInverseConstructor {t : IntTy} (hSigned : t.signed = true)
    (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (d : JInt t) :
    Jl (SignedMultiplicativeInverse t) := do
  if d.val = 0 then
    .error (.argumentError "cannot compute magic for d == 0")
  else
    let signedmin := JuliaLean.base.int.unsigned (JInt.typemin t)
    let ad := JuliaLean.base.int.unsigned (JuliaLean.base.int.abs d)
    let tval := addWrap signedmin (JInt.lit t.toUnsigned (if JuliaLean.base.int.signbit d then 1 else 0))
    let anc := subWrap (subWrap tval (JInt.lit t.toUnsigned 1)) (← remFn tval ad)
    let p := t.bits - 1
    let (q1, r1) ← divremFn signedmin anc
    let (q2, r2) ← divremFn signedmin ad
    let state := signedInverseLoop anc ad (t.bits + 1) ⟨p, q1, r1, q2, r2⟩
    let one := JInt.lit t.toUnsigned 1
    let m := JuliaLean.base.int.flipsign (remT t (addWrap state.q2 one)) d
    let shift ← convert .u8 (JInt.lit .i64 ((state.p : Int) - (t.bits : Int)))
    let addmul :=
      if d.val > 0 ∧ m.val < 0 then JInt.lit .i8 1
      else if d.val < 0 ∧ m.val > 0 then JInt.lit .i8 (-1)
      else JInt.lit .i8 0
    pure ⟨hSigned, d, m, addmul, shift⟩

/--
Julia source: base/multinverses.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SignedMultiplicativeInverse(x::Signed) = SignedMultiplicativeInverse{typeof(x)}(x)
```
-/
def signedMultiplicativeInverse {t : IntTy} (hSigned : t.signed = true)
    (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (d : JInt t) :
    Jl (SignedMultiplicativeInverse t) :=
  signedInverseConstructor hSigned remFn divremFn d

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
def unsignedInverseLoop {t : IntTy} (d nc signedmin signedmax : JInt t) :
    Nat → UnsignedLoopState t → Jl (UnsignedLoopState t)
  | 0, state => pure state
  | fuel + 1, state => do
      let one := JInt.lit t 1
      let p := state.p + 1
      let r1Threshold ← convert t (subWrap nc state.r1)
      let (q1, r1) :=
        if state.r1.val ≥ r1Threshold.val then
          (addWrap (addWrap state.q1 state.q1) one, subWrap (addWrap state.r1 state.r1) nc)
        else (addWrap state.q1 state.q1, addWrap state.r1 state.r1)
      let r2Left ← convert t (addWrap state.r2 one)
      let r2Right ← convert t (subWrap d state.r2)
      let (q2, r2, add) :=
        if r2Left.val ≥ r2Right.val then
          (addWrap (addWrap state.q2 state.q2) one,
            subWrap (addWrap (addWrap state.r2 state.r2) one) d,
            state.add || state.q2.val ≥ signedmax.val)
        else
          (addWrap state.q2 state.q2, addWrap (addWrap state.r2 state.r2) one,
            state.add || state.q2.val ≥ signedmin.val)
      let delta := subWrap (subWrap d one) r2
      let next : UnsignedLoopState t := ⟨p, q1, r1, q2, r2, add⟩
      if p < 2 * t.bits ∧ (q1.val < delta.val ∨ (q1.val = delta.val ∧ r1.val = 0)) then
        unsignedInverseLoop d nc signedmin signedmax fuel next
      else pure next

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
def unsignedInverseConstructor {t : IntTy} (hUnsigned : t.signed = false)
    (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (d : JInt t) :
    Jl (UnsignedMultiplicativeInverse t) := do
  if d.val = 0 then
    .error (.argumentError "cannot compute magic for d == 0")
  else
    let one := JInt.lit t 1
    let signedmin := shl_int one (JInt.lit .i64 (Int.ofNat (t.bits - 1)))
    let signedmax := subWrap signedmin one
    let allones := remT t (subWrap (JInt.lit t 0) one)
    let delta ← convert t (subWrap allones d)
    let nc := subWrap allones (← remFn delta d)
    let p := t.bits - 1
    let (q1, r1) ← divremFn signedmin nc
    let (q2, r2) ← divremFn signedmax d
    let state ← unsignedInverseLoop d nc signedmin signedmax (t.bits + 1)
      ⟨p, q1, r1, q2, r2, false⟩
    let multiplier := addWrap state.q2 one
    let shift := remT .u8
      (JInt.lit .i64 ((state.p : Int) - (t.bits : Int) - (if state.add then 1 else 0)))
    pure ⟨hUnsigned, d, multiplier, state.add, shift⟩

/--
Julia source: base/multinverses.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UnsignedMultiplicativeInverse(x::Unsigned) = UnsignedMultiplicativeInverse{typeof(x)}(x)
```
-/
def unsignedMultiplicativeInverse {t : IntTy} (hUnsigned : t.signed = false)
    (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (d : JInt t) :
    Jl (UnsignedMultiplicativeInverse t) :=
  unsignedInverseConstructor hUnsigned remFn divremFn d

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
def divSignedInverse {t : IntTy} (a : JInt t) (b : SignedMultiplicativeInverse t) : JInt t :=
  let x := mulHi a b.multiplier
  let x := addWrap x (mulWrap a (remT t b.addmul))
  if (JuliaLean.base.int.abs b.divisor).val = 1 then mulWrap a b.divisor
  else
    remT t (addWrap (JInt.lit t (if JuliaLean.base.int.signbit x then 1 else 0))
      (ashr_int x b.shift))

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
def divUnsignedInverse {t : IntTy} (a : JInt t) (b : UnsignedMultiplicativeInverse t) : JInt t :=
  let x := mulHi a b.multiplier
  let x :=
    if b.add then
      let difference := JInt.wrap t (subWrap a x).val
      let half := lshr_int difference (JInt.lit .u8 1)
      let sum := addWrap half x
      JInt.wrap t sum.val
    else x
  if b.divisor.val = 1 then a else lshr_int x b.shift

/-- Dispatches inverse division to its two source methods. -/
def divInverse {t : IntTy} (a : JInt t) : MultiplicativeInverse t → JInt t
  | .signed b => divSignedInverse a b
  | .unsigned b => divUnsignedInverse a b

/--
Julia source: base/multinverses.jl:148-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(a::T, b::MultiplicativeInverse{T}) where {T} =
    a - div(a, b)*b.divisor
```
-/
def rem {t : IntTy} (a : JInt t) (b : MultiplicativeInverse t) : JInt t :=
  subWrap a (mulWrap (divInverse a b) (match b with
    | .signed inverse => inverse.divisor
    | .unsigned inverse => inverse.divisor))

/--
Julia source: base/multinverses.jl:151-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(a::T, b::MultiplicativeInverse{T}) where T
    d = div(a, b)
    (d, a - d*b.divisor)
end
```
-/
def divremInverse {t : IntTy} (a : JInt t) (b : MultiplicativeInverse t) : JInt t × JInt t :=
  let d := divInverse a b
  (d, subWrap a (mulWrap d (match b with
    | .signed inverse => inverse.divisor
    | .unsigned inverse => inverse.divisor)))

/--
Julia source: base/multinverses.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(a::T, b::UnsignedMultiplicativeInverse{T}) where {T} = rem(a, b)
```
-/
def modUnsignedInverse {t : IntTy} (a : JInt t) (b : UnsignedMultiplicativeInverse t) : JInt t :=
  rem a (.unsigned b)

/--
Julia source: base/multinverses.jl:158-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mod(a::T, b::SignedMultiplicativeInverse{T}) where {T}
    r = rem(a, b)
    return (iszero(r) || signbit(r) == signbit(b.divisor)) ? r : r + b.divisor
end
```
-/
def modSignedInverse {t : IntTy} (a : JInt t) (b : SignedMultiplicativeInverse t) : JInt t :=
  let r := rem a (.signed b)
  if r.val = 0 ∨ JuliaLean.base.int.signbit r = JuliaLean.base.int.signbit b.divisor then r
  else addWrap r b.divisor

/--
Julia source: base/multinverses.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
multiplicativeinverse(x::Signed) = SignedMultiplicativeInverse(x)
```
-/
def multiplicativeinverseSigned {t : IntTy} (hSigned : t.signed = true)
    (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (d : JInt t) :
    Jl (SignedMultiplicativeInverse t) :=
  signedMultiplicativeInverse hSigned remFn divremFn d

/--
Julia source: base/multinverses.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
multiplicativeinverse(x::Unsigned) = UnsignedMultiplicativeInverse(x)
```
-/
def multiplicativeinverseUnsigned {t : IntTy} (hUnsigned : t.signed = false)
    (remFn : SameTypeRem) (divremFn : SameTypeDivrem) (d : JInt t) :
    Jl (UnsignedMultiplicativeInverse t) :=
  unsignedMultiplicativeInverse hUnsigned remFn divremFn d

end JuliaLean.base.multinverses
