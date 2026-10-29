import JuliaLean.Core
import JuliaLean.base.int

/-!
# Model of `base/char.jl`

`JChar` is the 32-bit storage pattern of a Julia `Char`; integer arguments use their Julia integer types. Julia dispatch is represented by typed operation parameters where a method calls an extensible or later-loaded function.
-/

namespace JuliaLean.base.char

open JuliaLean JuliaLean.base.int

abbrev JChar := UInt32
abbrev JInt64 := JInt .i64

inductive CharError where
  | invalidChar {C : Type} (c : C)
  | codePointError {N : Type} (u : N)
  | boundsError
  | foreign (error : JlError)

abbrev CharResult (α : Type) := Except CharError α

structure CharBitOps where
  leadingOnes : JChar → JInt64
  trailingZeros : JChar → JInt64

def jUInt32 (x : JChar) : JInt .u32 := JInt.lit .u32 x.toNat

def leadingOnesUInt32 (x : JChar) : JInt64 :=
  leading_ones_Integer leading_zeros bnot (jUInt32 x)

def trailingZerosUInt32 (x : JChar) : JInt64 := trailing_zeros (jUInt32 x)

def charBitOps : CharBitOps := ⟨leadingOnesUInt32, trailingZerosUInt32⟩

def ushr32 (x : JChar) (k : Nat) : JChar :=
  if k < 32 then x >>> UInt32.ofNat k else 0

def shl32 (x : JChar) (k : Nat) : JChar :=
  if k < 32 then x <<< UInt32.ofNat k else 0

def exactUInt32 (x : Int) : CharResult JChar :=
  match JInt.convert .u32 x with
  | .ok u => .ok (UInt32.ofNat u.val.toNat)
  | .error e => .error (.foreign e)

def liftJl {α : Type} : Jl α → CharResult α
  | .ok value => .ok value
  | .error error => .error (.foreign error)


/--
Julia source: base/char.jl:308-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const hex_chars = UInt8['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
                        'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i',
                        'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r',
                        's', 't', 'u', 'v', 'w', 'x', 'y', 'z']
```
-/

def hex_chars : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
   0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,
   0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73,
   0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a]


def hexCharAt (index : Nat) : CharResult UInt8 :=
  if index = 0 then .error .boundsError else
    match hex_chars[index - 1]? with
    | some byte => .ok byte
    | none => .error .boundsError


/--
Julia source: base/char.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw_invalid_char(c::AbstractChar) = throw(InvalidCharError(c))
```
-/

def throw_invalid_char {C α : Type} (c : C) : CharResult α :=
  .error (.invalidChar c)


/--
Julia source: base/char.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline throw_code_point_err(u::Integer) = throw(CodePointError(u))
```
-/

def throw_code_point_err {N α : Type} (u : N) : CharResult α :=
  .error (.codePointError u)


/--
Julia source: base/char.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive (::Type{T})(x::Number) where {T<:AbstractChar} = T(UInt32(x)::UInt32)
```
-/

def constructor_Number_AbstractChar {N C : Type}
    (toUInt32 : N → CharResult JChar) (construct : JChar → CharResult C) (x : N) : CharResult C := do
  construct (← toUInt32 x)


/--
Julia source: base/char.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive AbstractChar(x::Number) = Char(x)
```
-/

def constructor_AbstractChar_Number {N : Type}
    (constructChar : N → CharResult JChar) (x : N) : CharResult JChar :=
  constructChar x


/--
Julia source: base/char.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive (::Type{T})(x::AbstractChar) where {T<:Union{Number,AbstractChar}} = T(codepoint(x))
```
-/

def constructor_AbstractChar_AbstractChar {C N D : Type}
    (codepoint : C → CharResult N) (construct : N → CharResult D) (x : C) : CharResult D := do
  construct (← codepoint x)

/--
Julia source: base/char.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive (::Type{T})(x::AbstractChar) where {T<:Union{Int32,Int64}} = codepoint(x) % T
```
-/

def constructor_Integer_AbstractChar {C N : Type} (target : IntTy)
    (codepoint : C → CharResult N)
    (rem : (t : IntTy) → N → CharResult (JInt t)) (x : C) : CharResult (JInt target) := do
  rem target (← codepoint x)


/--
Julia source: base/char.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(x::T) where {T<:AbstractChar} = x
```
-/

def constructor_Same_AbstractChar {C : Type} (x : C) : C := x


/--
Julia source: base/char.jl:71-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ncodeunits(c::Char)
    u = reinterpret(UInt32, c)
    # We care about how many trailing bytes are all zero
    # subtract that from the total number of bytes
    n_nonzero_bytes = sizeof(UInt32) - div(trailing_zeros(u), 0x8)
    # Take care of '\0', which has an all-zero bitpattern
    n_nonzero_bytes + iszero(u)
end
```
-/

def ncodeunits_Char {E : Type _} (sizeofUInt32 : JInt64)
    (div : JInt64 → JInt64 → Except E JInt64) (ops : CharBitOps)
    (iszero : JChar → Bool) (c : JChar) : Except E JInt64 := do
  let u := c
  let n_nonzero_bytes := sizeofUInt32 - (← div (ops.trailingZeros u) (JInt.lit .i64 8))
  pure (n_nonzero_bytes + (if iszero u then JInt.lit .i64 1 else JInt.lit .i64 0))


/--
Julia source: base/char.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline is_overlong_enc(u::UInt32) = (u >> 25 == 0x60) | (u >> 21 == 0x0704) | (u >> 20 == 0x0f08)
```
-/

def is_overlong_enc (u : JChar) : Bool :=
  (ushr32 u 25 == 0x60) || (ushr32 u 21 == 0x0704) || (ushr32 u 20 == 0x0f08)


/--
Julia source: base/char.jl:121-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isoverlong(c::Char)
    u = bitcast(UInt32, c)
    is_overlong_enc(u)
end
```
-/

def isoverlong_Char (c : JChar) : Bool :=
  let u := c
  is_overlong_enc u


/--
Julia source: base/char.jl:111-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ismalformed(c::Char)
    u = bitcast(UInt32, c)
    l1 = leading_ones(u) << 3
    t0 = trailing_zeros(u) & 56
    (l1 == 8) | (l1 + t0 > 32) |
    (((u & 0x00c0c0c0) ⊻ 0x00808080) >> t0 != 0)
end
```
-/

def ismalformed_Char (ops : CharBitOps) (c : JChar) : Bool :=
  let u := c
  let l1 := JInt.lit .i64 (8 * (ops.leadingOnes u).val)
  let t0 := band (ops.trailingZeros u) (JInt.lit .i64 56)
  (l1.val == 8) || ((l1 + t0).val > 32) ||
    (ushr32 ((u &&& 0x00c0c0c0) ^^^ 0x00808080) t0.val.toNat != 0)


/--
Julia source: base/char.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ismalformed(c::AbstractChar) = false
```
-/

def ismalformed_AbstractChar {C : Type} (_c : C) : Bool := false


/--
Julia source: base/char.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isoverlong(c::AbstractChar) = false
```
-/

def isoverlong_AbstractChar {C : Type} (_c : C) : Bool := false


/--
Julia source: base/char.jl:158-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function UInt32(c::Char)
    # TODO: use optimized inline LLVM
    u = bitcast(UInt32, c)
    u < 0x80000000 && return u >> 24
    l1 = leading_ones(u)
    t0 = trailing_zeros(u) & 56
    (l1 == 1) | (8l1 + t0 > 32) |
    (((u & 0x00c0c0c0) ⊻ 0x00808080) >> t0 != 0) &&
        throw_invalid_char(c)
    u &= 0xffffffff >> l1
    u >>= t0
    ((u & 0x0000007f) >> 0) | ((u & 0x00007f00) >> 2) |
    ((u & 0x007f0000) >> 4) | ((u & 0x7f000000) >> 6)
end
```
-/

def uint32_Char (ops : CharBitOps) (c : JChar) : CharResult JChar := do
  let u := c
  if u < 0x80000000 then return ushr32 u 24
  let l1 := ops.leadingOnes u
  let t0 := band (ops.trailingZeros u) (JInt.lit .i64 56)
  if l1.val == 1 ||
      (JInt.lit .i64 (8 * l1.val) + t0).val > 32 ||
      ushr32 ((u &&& 0x00c0c0c0) ^^^ 0x00808080) t0.val.toNat != 0 then
    throw_invalid_char c
  let u := u &&& ushr32 0xffffffff l1.val.toNat
  let u := ushr32 u t0.val.toNat
  pure (((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
    ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6))


/--
Julia source: base/char.jl:100-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive codepoint(c::Char) = UInt32(c)
```
-/

def codepoint_Char (ops : CharBitOps) (c : JChar) : CharResult JChar :=
  uint32_Char ops c


/--
Julia source: base/char.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_codepoint(c::AbstractChar) = UInt32(c)::UInt32
```
-/

def unsafe_codepoint_AbstractChar {C : Type}
    (toUInt32 : C → CharResult JChar) (c : C) : CharResult JChar := do
  pure (← toUInt32 c)


/--
Julia source: base/char.jl:184-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive @assume_effects :nothrow :foldable function unsafe_codepoint(c::Char)
    u = bitcast(UInt32, c)
    u < 0x80000000 && return u >> 24
    l1 = leading_ones(u)
    t0 = trailing_zeros(u) & 56
    u &= 0xffffffff >> l1
    u >>= t0
    return ((u & 0x0000007f) >> 0) | ((u & 0x00007f00) >> 2) | ((u & 0x007f0000) >> 4) | ((u & 0x7f000000) >> 6)
end
```
-/

def unsafe_codepoint_Char (ops : CharBitOps) (c : JChar) : JChar :=
  let u := c
  if u < 0x80000000 then ushr32 u 24 else
    let l1 := ops.leadingOnes u
    let t0 := band (ops.trailingZeros u) (JInt.lit .i64 56)
    let u := u &&& ushr32 0xffffffff l1.val.toNat
    let u := ushr32 u t0.val.toNat
    ((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
      ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6)


/--
Julia source: base/char.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive decode_overlong(c::AbstractChar) = codepoint(c)
```
-/

def decode_overlong_AbstractChar {C N : Type}
    (codepoint : C → CharResult N) (c : C) : CharResult N :=
  codepoint c


/--
Julia source: base/char.jl:211-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function Char(u::UInt32)
    u < 0x80 && return bitcast(Char, u << 24)
    u < 0x00200000 || throw_code_point_err(u)
    c = ((u << 0) & 0x0000003f) | ((u << 2) & 0x00003f00) |
        ((u << 4) & 0x003f0000) | ((u << 6) & 0x3f000000)
    c = u < 0x00000800 ? (c << 16) | 0xc0800000 :
        u < 0x00010000 ? (c << 08) | 0xe0808000 :
                         (c << 00) | 0xf0808080
    bitcast(Char, c)
end
```
-/

def char_UInt32 (u : JChar) : CharResult JChar := do
  if u < 0x80 then return shl32 u 24
  if u < 0x00200000 then pure () else throw_code_point_err u
  let c := ((shl32 u 0) &&& 0x0000003f) ||| ((shl32 u 2) &&& 0x00003f00) |||
    ((shl32 u 4) &&& 0x003f0000) ||| ((shl32 u 6) &&& 0x3f000000)
  let c := if u < 0x00000800 then (shl32 c 16) ||| 0xc0800000 else
    if u < 0x00010000 then (shl32 c 8) ||| 0xe0808000 else (shl32 c 0) ||| 0xf0808080
  pure c


/--
Julia source: base/char.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive @noinline UInt32_cold(c::Char) = UInt32(c)
```
-/

def uint32_cold (c : JChar) (ops : CharBitOps) : CharResult JChar :=
  uint32_Char ops c


/--
Julia source: base/char.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive @noinline Char_cold(b::UInt32) = Char(b)
```
-/

def char_cold (b : JChar) : CharResult JChar :=
  char_UInt32 b


/--
Julia source: base/char.jl:223-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function (T::Union{Type{Int8},Type{UInt8}})(c::Char)
    i = bitcast(Int32, c)
    i ≥ 0 ? ((i >>> 24) % T) : T(UInt32_cold(c))
end
```
-/

def smallIntegerFromChar {T : Type} (bitcastInt32 : JChar → Int32)
    (nonnegative : Int32 → Bool) (logicalShift : Int32 → Int32)
    (narrow : Int32 → CharResult T) (construct : JChar → CharResult T)
    (ops : CharBitOps) (c : JChar) : CharResult T := do
  let i := bitcastInt32 c
  if nonnegative i then narrow (logicalShift i) else construct (← uint32_cold c ops)


/--
Julia source: base/char.jl:229-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :aggressive function Char(b::Union{Int8,UInt8})
    0 ≤ b ≤ 0x7f ? bitcast(Char, (b % UInt32) << 24) : Char_cold(UInt32(b))
end
```
-/

def char_SmallInteger {B : Type} (isAscii : B → Bool) (smallBits : B → JChar)
    (toUInt32 : B → CharResult JChar) (b : B) : CharResult JChar :=
  if isAscii b then .ok (shl32 (smallBits b) 24) else do
    char_cold (← toUInt32 b)


/--
Julia source: base/char.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AbstractChar}, x::Number) = Char(x) # default to Char
```
-/

def convert_AbstractChar_Number {N : Type}
    (charFromNumber : N → CharResult JChar) (x : N) : CharResult JChar :=
  charFromNumber x


/--
Julia source: base/char.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::Number) where {T<:AbstractChar} = T(x)::T
```
-/

def convert_TypeAbstractChar_Number {N C : Type}
    (construct : N → CharResult C) (x : N) : CharResult C :=
  construct x


/--
Julia source: base/char.jl:235-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::AbstractChar) where {T<:Number} = T(x)::T
```
-/

def convert_TypeNumber_AbstractChar {C N : Type}
    (construct : C → CharResult N) (x : C) : CharResult N :=
  construct x


/--
Julia source: base/char.jl:236-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, c::AbstractChar) where {T<:AbstractChar} = T(c)::T
```
-/

def convert_TypeAbstractChar_AbstractChar {C : Type}
    (construct : C → CharResult C) (c : C) : CharResult C :=
  construct c


/--
Julia source: base/char.jl:237-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, c::T) where {T<:AbstractChar} = c
```
-/

def convert_SameAbstractChar {C : Type} (c : C) : C := c


/--
Julia source: base/char.jl:239-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::AbstractChar, ::Type{T}) where {T<:Number} = rem(codepoint(x), T)
```
-/

def rem_AbstractChar_Number {C N R : Type}
    (codepoint : C → CharResult N) (rem : N → R → CharResult R)
    (x : C) (target : R) : CharResult R := do
  rem (← codepoint x) target


/--
Julia source: base/char.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{Char}) = bitcast(Char, typemax(UInt32))
```
-/

def typemax_Char (typemaxUInt32 : JChar) : JChar :=
  typemaxUInt32


/--
Julia source: base/char.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{Char}) = bitcast(Char, typemin(UInt32))
```
-/

def typemin_Char (typeminUInt32 : JChar) : JChar :=
  typeminUInt32


/--
Julia source: base/char.jl:244-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(c::AbstractChar) = ()
```
-/

def size_AbstractChar {C : Type} (_c : C) : Unit := ()


/--
Julia source: base/char.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(c::AbstractChar, d::Integer) = d < 1 ? throw(BoundsError()) : 1
```
-/

def size_AbstractChar_Dimension {C I : Type} (less : I → I → Bool) (one : I)
    (_c : C) (d : I) : CharResult JInt64 :=
  if less d one then .error .boundsError else .ok (JInt.lit .i64 1)


/--
Julia source: base/char.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(c::AbstractChar) = 0
```
-/

def ndims_AbstractChar {C : Type} (_c : C) : JInt64 := JInt.lit .i64 0


/--
Julia source: base/char.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(::Type{<:AbstractChar}) = 0
```
-/

def ndims_TypeAbstractChar {C : Type} : JInt64 := JInt.lit .i64 0


/--
Julia source: base/char.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(c::AbstractChar) = 1
```
-/

def length_AbstractChar {C : Type} (_c : C) : JInt64 := JInt.lit .i64 1


/--
Julia source: base/char.jl:249-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:AbstractChar}) = HasShape{0}()
```
-/

inductive IteratorSize where
  | hasShape (rank : Nat)
  deriving Repr, DecidableEq

def iteratorSize_AbstractChar {C : Type} : IteratorSize := .hasShape 0


/--
Julia source: base/char.jl:250-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(c::AbstractChar) = 1
```
-/

def firstindex_AbstractChar {C : Type} (_c : C) : JInt64 := JInt.lit .i64 1


/--
Julia source: base/char.jl:251-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(c::AbstractChar) = 1
```
-/

def lastindex_AbstractChar {C : Type} (_c : C) : JInt64 := JInt.lit .i64 1


/--
Julia source: base/char.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(c::AbstractChar) = c
```
-/

def getindex_AbstractChar {C : Type} (c : C) : C := c


/--
Julia source: base/char.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(c::AbstractChar, i::Integer) = i == 1 ? c : throw(BoundsError())
```
-/

def getindex_AbstractChar_Integer {C I : Type}
    (equal : I → I → Bool) (one : I) (c : C) (i : I) : CharResult C :=
  if equal i one then .ok c else .error .boundsError


/--
Julia source: base/char.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(c::AbstractChar, I::Integer...) = all(x -> x == 1, I) ? c : throw(BoundsError())
```
-/

def getindex_AbstractChar_Vararg {C I : Type}
    (equal : I → I → Bool) (one : I) (c : C) (indices : List I) : CharResult C :=
  if indices.all (fun x => equal x one) then .ok c else .error .boundsError


/--
Julia source: base/char.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(c::AbstractChar) = c
```
-/

def first_AbstractChar {C : Type} (c : C) : C := c


/--
Julia source: base/char.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(c::AbstractChar) = c
```
-/

def last_AbstractChar {C : Type} (c : C) : C := c


/--
Julia source: base/char.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{T}) where {T<:AbstractChar} = T
```
-/

def eltype_AbstractChar {C : Type} : Type := C


/--
Julia source: base/char.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(c::AbstractChar, done=false) = done ? nothing : (c, true)
```
-/

def iterate_AbstractChar {C : Type} (c : C) (done : Bool := false) : Option (C × Bool) :=
  if done then none else some (c, true)


/--
Julia source: base/char.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(c::AbstractChar) = false
```
-/

def isempty_AbstractChar {C : Type} (_c : C) : Bool := false


/--
Julia source: base/char.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x::AbstractChar, y::AbstractChar) = x == y
```
-/

def in_AbstractChar {C : Type} (equal : C → C → Bool) (x y : C) : Bool :=
  equal x y


/--
Julia source: base/char.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Char, y::Char) = bitcast(UInt32, x) == bitcast(UInt32, y)
```
-/

def eq_Char (x y : JChar) : Bool := x == y


/--
Julia source: base/char.jl:264-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(x::Char, y::Char) = bitcast(UInt32, x) < bitcast(UInt32, y)
```
-/

def isless_Char (x y : JChar) : Bool := x < y


/--
Julia source: base/char.jl:265-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::Char, h::UInt) =
    hash_finalizer(((bitcast(UInt32, x) +% UInt64(0xd4d64234)) << 32) ⊻ UInt64(h)) % UInt
```
-/

def hash_Char (hashFinalizer : UInt64 → UInt64) (x : JChar) (h : UInt64) : UInt64 :=
  hashFinalizer (((UInt64.ofNat x.toNat + 0xd4d64234) <<< UInt64.ofNat 32) ^^^ h)


/--
Julia source: base/char.jl:269-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(x::AbstractChar, y::AbstractChar) = isless(Char(x)::Char, Char(y)::Char)
```
-/

def isless_AbstractChar {C : Type}
    (toChar : C → CharResult JChar) (islessChar : JChar → JChar → Bool)
    (x y : C) : CharResult Bool := do
  pure (islessChar (← toChar x) (← toChar y))


/--
Julia source: base/char.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::AbstractChar, y::AbstractChar) = Char(x)::Char == Char(y)::Char
```
-/

def eq_AbstractChar {C : Type}
    (toChar : C → CharResult JChar) (equalChar : JChar → JChar → Bool)
    (x y : C) : CharResult Bool := do
  pure (equalChar (← toChar x) (← toChar y))


/--
Julia source: base/char.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::AbstractChar, h::UInt) = hash(Char(x)::Char, h)
```
-/

def hash_AbstractChar {C : Type}
    (toChar : C → CharResult JChar) (hashChar : JChar → UInt64 → UInt64)
    (x : C) (h : UInt64) : CharResult UInt64 := do
  pure (hashChar (← toChar x) h)


/--
Julia source: base/char.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{T}) where {T<:AbstractChar} = T
```
-/

def widen_AbstractChar {C : Type} : Type := C


/--
Julia source: base/char.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline -%(x::AbstractChar, y::AbstractChar) = Int(x) -% Int(y)
```
-/

def subWrap_AbstractChar_AbstractChar {C : Type}
    (toInt : C → CharResult JInt64) (subWrap : JInt64 → JInt64 → JInt64)
    (x y : C) : CharResult JInt64 := do
  pure (subWrap (← toInt x) (← toInt y))


/--
Julia source: base/char.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline -(x::AbstractChar, y::AbstractChar) = Int(x) - Int(y)
```
-/

def sub_AbstractChar_AbstractChar {C : Type}
    (toInt : C → CharResult JInt64) (subInt : JInt64 → JInt64 → JInt64)
    (x y : C) : CharResult JInt64 := do
  pure (subInt (← toInt x) (← toInt y))


structure CharIntegerOps (C I P : Type) where
  isChar : Bool
  charBits : C → JChar
  int32OfChar : C → CharResult Int32
  int32OfInteger : I → CharResult Int32
  promoteInt32 : Int32 → P
  promoteInteger : I → P
  addPromoted : P → P → P
  subPromoted : P → P → P
  nonnegative : P → Bool
  belowAscii : P → Bool
  toUInt32 : P → CharResult JChar
  rawChar : JChar → C
  charFromUInt32 : JChar → CharResult C
  fromInt32 : Int32 → CharResult C


/--
Julia source: base/char.jl:276-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function -%(x::T, y::Integer) where {T<:AbstractChar}
    if x isa Char
        u = Int32((bitcast(UInt32, x) >> 24) % Int8)
        if u >= 0 # inline the runtime fast path
            z = u - y
            return 0 <= z < 0x80 ? bitcast(Char, (z % UInt32) << 24) : Char(UInt32(z))
        end
    end
    return T(Int32(x) - Int32(y))
end
```
-/

def subWrap_AbstractChar_Integer {C I P : Type} (ops : CharIntegerOps C I P)
    (x : C) (y : I) : CharResult C := do
  if ops.isChar then
    let highByte := ushr32 (ops.charBits x) 24
    let byte := UInt8.ofNat highByte.toNat
    let signedByte := Int8.ofBitVec byte.toBitVec
    let u := Int32.ofInt signedByte.toInt
    if u.toInt >= 0 then
      let z := ops.subPromoted (ops.promoteInt32 u) (ops.promoteInteger y)
      if ops.nonnegative z && ops.belowAscii z then
        return ops.rawChar (shl32 (← ops.toUInt32 z) 24)
      let code := ← ops.toUInt32 z
      return (← ops.charFromUInt32 code)
  let x32 ← ops.int32OfChar x
  let y32 ← ops.int32OfInteger y
  ops.fromInt32 (x32 - y32)


/--
Julia source: base/char.jl:286-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function +%(x::T, y::Integer) where {T<:AbstractChar}
    if x isa Char
        u = Int32((bitcast(UInt32, x) >> 24) % Int8)
        if u >= 0 # inline the runtime fast path
            z = u + y
            return 0 <= z < 0x80 ? bitcast(Char, (z % UInt32) << 24) : Char(UInt32(z))
        end
    end
    return T(Int32(x) + Int32(y))
end
```
-/

def addWrap_AbstractChar_Integer {C I P : Type} (ops : CharIntegerOps C I P)
    (x : C) (y : I) : CharResult C := do
  if ops.isChar then
    let highByte := ushr32 (ops.charBits x) 24
    let byte := UInt8.ofNat highByte.toNat
    let signedByte := Int8.ofBitVec byte.toBitVec
    let u := Int32.ofInt signedByte.toInt
    if u.toInt >= 0 then
      let z := ops.addPromoted (ops.promoteInt32 u) (ops.promoteInteger y)
      if ops.nonnegative z && ops.belowAscii z then
        return ops.rawChar (shl32 (← ops.toUInt32 z) 24)
      let code := ← ops.toUInt32 z
      return (← ops.charFromUInt32 code)
  let x32 ← ops.int32OfChar x
  let y32 ← ops.int32OfInteger y
  ops.fromInt32 (x32 + y32)


/--
Julia source: base/char.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::AbstractChar, y::Integer) = x +% y
```
-/

def add_AbstractChar_Integer {C I P : Type} (ops : CharIntegerOps C I P)
    (x : C) (y : I) : CharResult C :=
  addWrap_AbstractChar_Integer ops x y


/--
Julia source: base/char.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline +%(x::Integer, y::AbstractChar) = y + x
```
-/

def addWrap_Integer_AbstractChar {C I P : Type} (ops : CharIntegerOps C I P)
    (x : I) (y : C) : CharResult C :=
  add_AbstractChar_Integer ops y x


/--
Julia source: base/char.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::AbstractChar, y::Integer) = x -% y
```
-/

def sub_AbstractChar_Integer {C I P : Type} (ops : CharIntegerOps C I P)
    (x : C) (y : I) : CharResult C :=
  subWrap_AbstractChar_Integer ops x y


/--
Julia source: base/char.jl:300-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Integer, y::AbstractChar) = x +% y
```
-/

def add_Integer_AbstractChar {C I P : Type} (ops : CharIntegerOps C I P)
    (x : I) (y : C) : CharResult C :=
  addWrap_Integer_AbstractChar ops x y


def remUInt32ToIntTy (target : IntTy) (x : JChar) : CharResult (JInt target) :=
  .ok (remT target (jUInt32 x))

def charToInt32 (c : JChar) : CharResult Int32 := do
  let value ← constructor_Integer_AbstractChar .i32 (codepoint_Char charBitOps)
    remUInt32ToIntTy c
  pure (Int32.ofInt value.val)

def int64ToInt32 (x : JInt64) : CharResult Int32 := do
  let value ← liftJl (JInt.convert .i32 x.val)
  pure (Int32.ofInt value.val)

def int64PromoteInt32 (x : Int32) : JInt64 := JInt.lit .i64 x.toInt
def int64Identity (x : JInt64) : JInt64 := x
def addPromotedInt64 (x y : JInt64) : JInt64 := x + y
def subPromotedInt64 (x y : JInt64) : JInt64 := x - y
def nonnegativeInt64 (x : JInt64) : Bool := 0 ≤ x.val
def belowAsciiInt64 (x : JInt64) : Bool := x.val < 0x80
def int64ToUInt32 (x : JInt64) : CharResult JChar := exactUInt32 x.val
def rawCharIdentity (x : JChar) : JChar := x
def charFromInt32 (x : Int32) : CharResult JChar := do
  char_UInt32 (← exactUInt32 x.toInt)

def charIntegerOps : CharIntegerOps JChar JInt64 JInt64 :=
  { isChar := true
    charBits := rawCharIdentity
    int32OfChar := charToInt32
    int32OfInteger := int64ToInt32
    promoteInt32 := int64PromoteInt32
    promoteInteger := int64Identity
    addPromoted := addPromotedInt64
    subPromoted := subPromotedInt64
    nonnegative := nonnegativeInt64
    belowAscii := belowAsciiInt64
    toUInt32 := int64ToUInt32
    rawChar := rawCharIdentity
    charFromUInt32 := char_UInt32
    fromInt32 := charFromInt32 }


/--
Julia source: base/char.jl:305-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, c::Char) = (write(io, c); nothing)
```
-/

def print_Char {IO : Type} (writeChar : IO → JChar → CharResult (IO × JInt64))
    (io : IO) (c : JChar) : CharResult (IO × Unit) := do
  let (io, _) ← writeChar io c
  pure (io, ())


/--
Julia source: base/char.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, c::AbstractChar) = print(io, Char(c)::Char) # fallback: convert to output UTF-8
```
-/

def print_AbstractChar {C IO : Type}
    (toChar : C → CharResult JChar) (printChar : IO → JChar → CharResult (IO × Unit))
    (io : IO) (c : C) : CharResult (IO × Unit) := do
  printChar io (← toChar c)


inductive CharOutput where
  | bytes (value : List UInt8)
  | character (value : JChar)
  | text (parts : List String)
  deriving Repr, DecidableEq

def writeBytesTrace (io : List CharOutput) (bytes : List UInt8) : CharResult (List CharOutput × JInt64) :=
  .ok (io ++ [.bytes bytes], JInt.lit .i64 bytes.length)

def writeCharTrace (io : List CharOutput) (c : JChar) : CharResult (List CharOutput × JInt64) :=
  .ok (io ++ [.character c], JInt.lit .i64 1)

def printStringsTrace (io : List CharOutput) (parts : List String) : CharResult (List CharOutput × Unit) :=
  .ok (io ++ [.text parts], ())

def showInvalidLoop {IO : Type}
    (writeBytes : IO → List UInt8 → CharResult (IO × JInt64)) : Nat → IO → JChar → CharResult IO
  | 0, io, _ => .ok io
  | fuel + 1, io, u => do
    let a ← hexCharAt ((((ushr32 u 28) &&& 0xf).toNat) + 1)
    let b ← hexCharAt ((((ushr32 u 24) &&& 0xf).toNat) + 1)
    let (io, _) ← writeBytes io [0x5c, 0x78, a, b]
    let next := shl32 u 8
    if next == 0 then pure io else showInvalidLoop writeBytes fuel io next


/--
Julia source: base/char.jl:313-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_invalid(io::IO, c::Char)
    write(io, 0x27)
    u = bitcast(UInt32, c)
    while true
        a = hex_chars[((u >> 28) & 0xf) + 1]
        b = hex_chars[((u >> 24) & 0xf) + 1]
        write(io, 0x5c, UInt8('x'), a, b)
        (u <<= 8) == 0 && break
    end
    write(io, 0x27)
end
```
-/

def show_invalid_Char {IO : Type}
    (writeBytes : IO → List UInt8 → CharResult (IO × JInt64))
    (io : IO) (c : JChar) : CharResult (IO × JInt64) := do
  let (io, _) ← writeBytes io [0x27]
  let u := c
  let io ← showInvalidLoop writeBytes 4 io u
  writeBytes io [0x27]


structure CharShowOps (C IO N : Type) where
  lessEqualBackslash : C → Bool
  equalChar : C → JChar → Bool
  isOverlong : C → Bool
  isMalformed : C → Bool
  showInvalid : IO → C → CharResult (IO × JInt64)
  isPrint : C → Bool
  writeBytes : IO → List UInt8 → CharResult (IO × JInt64)
  printChar : IO → C → CharResult (IO × Unit)
  codepoint : C → CharResult N
  numLe : N → N → Bool
  numLiteral : Int → N
  leadingZeros : N → JInt64
  numRightShift : N → JInt64 → N
  numAnd : N → N → N
  numAdd : N → N → N
  toNat : N → Nat

def showHexDigits {C IO N : Type} (ops : CharShowOps C IO N) : Nat → IO → N → CharResult IO
  | 0, io, _ => .ok io
  | digits + 1, io, u => do
    let shift := JInt.lit .i64 (Int.ofNat (digits * 4))
    let value := ops.numAnd (ops.numRightShift u shift) (ops.numLiteral 0xf)
    let index := ops.toNat (ops.numAdd value (ops.numLiteral 1))
    let byte ← hexCharAt index
    let (io, _) ← ops.writeBytes io [byte]
    showHexDigits ops digits io u


/--
Julia source: base/char.jl:336-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, c::AbstractChar)
    if c <= '\\'
        b = c == '\0' ? 0x30 :
            c == '\a' ? 0x61 :
            c == '\b' ? 0x62 :
            c == '\t' ? 0x74 :
            c == '\n' ? 0x6e :
            c == '\v' ? 0x76 :
            c == '\f' ? 0x66 :
            c == '\r' ? 0x72 :
            c == '\e' ? 0x65 :
            c == '\'' ? 0x27 :
            c == '\\' ? 0x5c : 0xff
        if b != 0xff
            write(io, 0x27, 0x5c, b, 0x27)
            return
        end
    end
    if isoverlong(c) || ismalformed(c)
        show_invalid(io, c)
    elseif isprint(c)
        write(io, 0x27)
        print(io, c) # use print, not write, to use UTF-8 for any AbstractChar
        write(io, 0x27)
    else # unprintable, well-formed, non-overlong Unicode
        u = codepoint(c)
        write(io, 0x27, 0x5c, u <= 0x7f ? 0x78 : u <= 0xffff ? 0x75 : 0x55)
        d = max(2, 8 - (leading_zeros(u) >> 2))
        while 0 < d
            write(io, hex_chars[((u >> ((d -= 1) << 2)) & 0xf) + 1])
        end
        write(io, 0x27)
    end
    return
end
```
-/

def show_AbstractChar {C IO N : Type} (ops : CharShowOps C IO N)
    (io : IO) (c : C) : CharResult (IO × Unit) := do
  if ops.lessEqualBackslash c then
    let b : UInt8 :=
      if ops.equalChar c 0x00000000 then 0x30 else
      if ops.equalChar c 0x07000000 then 0x61 else
      if ops.equalChar c 0x08000000 then 0x62 else
      if ops.equalChar c 0x09000000 then 0x74 else
      if ops.equalChar c 0x0a000000 then 0x6e else
      if ops.equalChar c 0x0b000000 then 0x76 else
      if ops.equalChar c 0x0c000000 then 0x66 else
      if ops.equalChar c 0x0d000000 then 0x72 else
      if ops.equalChar c 0x1b000000 then 0x65 else
      if ops.equalChar c 0x27000000 then 0x27 else
      if ops.equalChar c 0x5c000000 then 0x5c else 0xff
    if b != 0xff then
      let (io, _) ← ops.writeBytes io [0x27, 0x5c, b, 0x27]
      return (io, ())
  if ops.isOverlong c || ops.isMalformed c then
    let (io, _) ← ops.showInvalid io c
    return (io, ())
  else if ops.isPrint c then
    let (io, _) ← ops.writeBytes io [0x27]
    let (io, _) ← ops.printChar io c
    let (io, _) ← ops.writeBytes io [0x27]
    return (io, ())
  else
    let u ← ops.codepoint c
    let tag : UInt8 := if ops.numLe u (ops.numLiteral 0x7f) then 0x78 else
      if ops.numLe u (ops.numLiteral 0xffff) then 0x75 else 0x55
    let leading := ops.leadingZeros u
    let digitCount := JInt.lit .i64 8 - ashr_int leading (JInt.lit .i64 2)
    let digits := Nat.max 2 digitCount.val.toNat
    let (io, _) ← ops.writeBytes io [0x27, 0x5c, tag]
    let io ← showHexDigits ops digits io u
    let (io, _) ← ops.writeBytes io [0x27]
    return (io, ())


structure CharPlainShowOps (C IO N : Type) where
  showValue : IO → C → CharResult (IO × Unit)
  compact : IO → CharResult Bool
  isMalformed : C → Bool
  isOverlong : C → Bool
  printStrings : IO → List String → CharResult (IO × Unit)
  decodeOverlong : C → CharResult N
  codepoint : C → CharResult N
  constructFromNumber : N → CharResult C
  stringBase16Pad4 : N → CharResult String
  uppercase : String → String
  isAscii : C → Bool
  categoryAbbrev : C → CharResult String
  categoryString : C → CharResult String


/--
Julia source: base/char.jl:372-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", c::T) where {T<:AbstractChar}
    show(io, c)
    get(io, :compact, false)::Bool && return
    if !ismalformed(c)
        print(io, ": ")
        if isoverlong(c)
            print(io, "[overlong] ")
            u = decode_overlong(c) # backwards compat Julia < 1.12
            c = T(u)
        else
            u = codepoint(c)
        end
        h = uppercase(string(u, base = 16, pad = 4))
        print(io, (isascii(c) ? "ASCII/" : ""), "Unicode U+", h)
    else
        print(io, ": Malformed UTF-8")
    end
    abr = Unicode.category_abbrev(c)
    str = Unicode.category_string(c)
    print(io, " (category ", abr, ": ", str, ")")
end
```
-/

def show_MIMETextPlain {C IO N : Type} (ops : CharPlainShowOps C IO N)
    (io : IO) (c : C) : CharResult (IO × Unit) := do
  let (io, _) ← ops.showValue io c
  if ← ops.compact io then return (io, ())
  let (io, c) ← if !ops.isMalformed c then do
    let (io, _) ← ops.printStrings io [": "]
    let (c, u) ← if ops.isOverlong c then do
      let (io, _) ← ops.printStrings io ["[overlong] "]
      let u ← ops.decodeOverlong c
      let c ← ops.constructFromNumber u
      pure (c, u)
    else
      pure (c, ← ops.codepoint c)
    let h ← ops.stringBase16Pad4 u
    let h := ops.uppercase h
    let (io, _) ← ops.printStrings io
      [(if ops.isAscii c then "ASCII/" else ""), "Unicode U+", h]
    pure (io, c)
  else do
    let (io, _) ← ops.printStrings io [": Malformed UTF-8"]
    pure (io, c)
  let abr ← ops.categoryAbbrev c
  let str ← ops.categoryString c
  ops.printStrings io [" (category ", abr, ": ", str, ")"]
def codepointInt64 (c : JChar) : CharResult JInt64 := do
  let u ← codepoint_Char charBitOps c
  pure (JInt.lit .i64 u.toNat)

def divInt64 (x y : JInt64) : CharResult JInt64 := liftJl (JInt.div x y)
def iszeroUInt32 (x : JChar) : Bool := x == 0

def lessEqualBackslashChar (c : JChar) : Bool := c ≤ 0x5c000000
def lessEqualUInt32 (x y : JChar) : Bool := x ≤ y
def numLiteralUInt32 (x : Int) : JChar := UInt32.ofNat x.toNat
def numRightShiftUInt32 (x : JChar) (k : JInt64) : JChar := ushr32 x k.val.toNat
def numAndUInt32 (x y : JChar) : JChar := x &&& y
def numAddUInt32 (x y : JChar) : JChar := x + y
def leadingZerosUInt32 (x : JChar) : JInt64 := leading_zeros (jUInt32 x)
def ismalformedChar (c : JChar) : Bool := ismalformed_Char charBitOps c
def codepointChar (c : JChar) : CharResult JChar := codepoint_Char charBitOps c
def showInvalidTrace (io : List CharOutput) (c : JChar) : CharResult (List CharOutput × JInt64) :=
  show_invalid_Char writeBytesTrace io c
def printCharTrace (io : List CharOutput) (c : JChar) : CharResult (List CharOutput × Unit) :=
  print_Char writeCharTrace io c

def charShowOpsFor {IO : Type} (isPrint : JChar → Bool)
    (writeBytes : IO → List UInt8 → CharResult (IO × JInt64))
    (showInvalid : IO → JChar → CharResult (IO × JInt64))
    (printChar : IO → JChar → CharResult (IO × Unit)) : CharShowOps JChar IO JChar :=
  { lessEqualBackslash := lessEqualBackslashChar
    equalChar := eq_Char
    isOverlong := isoverlong_Char
    isMalformed := ismalformedChar
    showInvalid := showInvalid
    isPrint := isPrint
    writeBytes := writeBytes
    printChar := printChar
    codepoint := codepointChar
    numLe := lessEqualUInt32
    numLiteral := numLiteralUInt32
    leadingZeros := leadingZerosUInt32
    numRightShift := numRightShiftUInt32
    numAnd := numAndUInt32
    numAdd := numAddUInt32
    toNat := UInt32.toNat }

def charShowOps (isPrint : JChar → Bool) : CharShowOps JChar (List CharOutput) JChar :=
  charShowOpsFor isPrint writeBytesTrace showInvalidTrace printCharTrace

def decodeOverlongChar (c : JChar) : CharResult JChar :=
  decode_overlong_AbstractChar codepointChar c

def charPlainShowOps {IO : Type}
    (isPrint : JChar → Bool)
    (writeBytes : IO → List UInt8 → CharResult (IO × JInt64))
    (showInvalid : IO → JChar → CharResult (IO × JInt64))
    (printChar : IO → JChar → CharResult (IO × Unit))
    (compact : IO → CharResult Bool)
    (printStrings : IO → List String → CharResult (IO × Unit))
    (stringBase16Pad4 : JChar → CharResult String) (uppercase : String → String)
    (isAscii : JChar → Bool) (categoryAbbrev categoryString : JChar → CharResult String) :
    CharPlainShowOps JChar IO JChar :=
  { showValue := show_AbstractChar (charShowOpsFor isPrint writeBytes showInvalid printChar)
    compact := compact
    isMalformed := ismalformedChar
    isOverlong := isoverlong_Char
    printStrings := printStrings
    decodeOverlong := decodeOverlongChar
    codepoint := codepointChar
    constructFromNumber := char_UInt32
    stringBase16Pad4 := stringBase16Pad4
    uppercase := uppercase
    isAscii := isAscii
    categoryAbbrev := categoryAbbrev
    categoryString := categoryString }


end JuliaLean.base.char
