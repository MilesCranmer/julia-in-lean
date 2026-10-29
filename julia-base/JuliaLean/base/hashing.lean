import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.Promotion.Compare

/-!
# Typed model of `base/hashing.jl` at Julia f755f49a9e41380d7da126b3c1db9fe7f83dd027.
The machine-width model targets Julia's 64-bit `UInt`; generic inputs remain type parameters,
and calls into dispatch, abstract iterators, and runtime services are typed interfaces.
-/

namespace JuliaLean.base.hashing

open JuliaLean JuliaLean.Promotion JuliaLean.base.int JuliaLean.base.float

abbrev Word := JInt .u64
abbrev Word32 := JInt .u32
abbrev HashSecret := Word × Word × Word × Word

def hashSeed : Word := JInt.lit .u64 0xbdd89aa982704029
def hashSecret : Word × Word × Word × Word :=
  (JInt.lit .u64 0x2d358dccaa6c78a5, JInt.lit .u64 0x8bb84b93962eacc9,
   JInt.lit .u64 0x4b33a62ed433d4a3, JInt.lit .u64 0xaaaaaaaaaaaaaaaa)

def xorWord (a b : Word) : Word := JInt.lit .u64 (Int.ofNat (Nat.xor a.val.toNat b.val.toNat))
def xorWord32 (a b : Word32) : Word32 := JInt.lit .u32 (Int.ofNat (Nat.xor a.val.toNat b.val.toNat))
def shlWord (x : Word) (n : Nat) : Word := JInt.lit .u64 (x.val * Int.ofNat (2 ^ n))
def shrWord (x : Word) (n : Nat) : Word := JInt.lit .u64 (x.val / Int.ofNat (2 ^ n))
def shlWord32 (x : Word32) (n : Nat) : Word32 := JInt.lit .u32 (x.val * Int.ofNat (2 ^ n))
def shrWord32 (x : Word32) (n : Nat) : Word32 := JInt.lit .u32 (x.val / Int.ofNat (2 ^ n))
def lowWord32 (x : Word) : Word32 := JInt.lit .u32 x.val

def hashMixLinear32 (x : Word32) (h : Word32) : Word32 := JInt.lit .u32 3 * h - x

def hashU64ToU32 (x : Word) : Word32 := JInt.lit .u32 x.val

def hashTypeSeed : Word := JInt.lit .u64 0x2c97bf8b3de87020
def hashExprSeed : Word := JInt.lit .u64 0x83c7900696d26dc6
def hashGlobalRefSeed : Word := JInt.lit .u64 0xe19bede84d316c06
def hashPartialStructSeed : Word := JInt.lit .u64 0xee5c84c1439961a8

structure WeakRef (α : Type) where
  value : α

structure IntegerCodeUnits (α : Type) where
  uvalue : α
  numBytes : Int

structure UTF8Units (S : Type) where
  string : S

inductive UTF8UnitsResult (A S : Type) where
  | codeunits (bytes : A)
  | iterated (units : UTF8Units S)

structure UTF8Iterator (S State Char : Type) where
  string : S
  defaultState : State
  first : S → Option (Char × State)
  next : S → State → Option (Char × State)
  reinterpretUInt32 : Char → Word32
  bswapUInt32 : Word32 → Word32

abbrev UTF8State (State : Type) := State × Word32

structure HashByteArray where
  firstIndex : Int
  length : Nat
  get : Int → UInt8

structure HashPointerOps (Ptr : Type) where
  Ptr32 : Type
  Ptr64 : Type
  convert32 : Ptr → Ptr32
  convert64 : Ptr → Ptr64
  add32 : Ptr32 → Int → Ptr32
  add64 : Ptr64 → Int → Ptr64
  load8 : Ptr → Nat → UInt8
  pointerref32 : Ptr32 → Nat → Nat → Word32
  pointerref64 : Ptr64 → Nat → Nat → Word

structure HashByteIterator (State : Type) where
  first : Option (UInt8 × State)
  next : State → Option (UInt8 × State)
  remaining : State → Nat
  defaultState : State

structure IteratorHashState (State : Type) where
  state : State
  seed : Word
  see1 : Word
  see2 : Word
  buflen : Word
  l0 : Word
  l1 : Word
  l2 : Word
  l3 : Word
  l4 : Word
  l5 : Word
  b0 : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  b4 : Nat
  b5 : Nat
  t0 : Word
  t1 : Word

structure FloatHashOps (α : Type) where
  leIntFloat : JInt .i64 → α → Bool
  ltFloatInt : α → JInt .i64 → Bool
  leUIntFloat : JInt .u64 → α → Bool
  ltFloatUInt : α → JInt .u64 → Bool
  fptosi : α → JInt .i64
  fptoui : α → JInt .u64
  isequalI64 : JInt .i64 → α → Bool
  isequalU64 : JInt .u64 → α → Bool
  isnan : α → Bool
  isfinite : α → Bool
  bitcastU64 : α → Word

structure Float16HashOps (α : Type) where
  isfinite : α → Bool
  isnan : α → Bool
  fptosi : α → JInt .i64
  isequalI64 : JInt .i64 → α → Bool
  toFloat64 : α → Fl double
  bitcastFloat64U64 : Fl double → Word

def standardHashFloat64Ops : FloatHashOps (Fl double) where
  leIntFloat := fun n x => cmpIF .le (T := .f64) (t := .i64) n x
  ltFloatInt := fun x n => cmpFI .lt (T := .f64) (t := .i64) x n
  leUIntFloat := fun n x => cmpIF .le (T := .f64) (t := .u64) n x
  ltFloatUInt := fun x n => cmpFI .lt (T := .f64) (t := .u64) x n
  fptosi := fun x => fptosi .i64 (T := .f64) x
  fptoui := fun x => fptoui .u64 (T := .f64) x
  isequalI64 := fun n x => cmpIF .eq (T := .f64) (t := .i64) n x
  isequalU64 := fun n x => cmpIF .eq (T := .f64) (t := .u64) n x
  isnan := fun x => x.isnan
  isfinite := fun x => x.isfinite
  bitcastU64 := fun x => bitcast_from_float .u64 (T := .f64) x

def standardHashFloat16Ops : Float16HashOps (Fl half) where
  isfinite := fun x => x.isfinite
  isnan := fun x => x.isnan
  fptosi := fun x => fptosi .i64 (T := .f16) x
  isequalI64 := fun n x => cmpIF .eq (T := .f16) (t := .i64) n x
  toFloat64 := fun x => fpext .f64 (S := .f16) x
  bitcastFloat64U64 := fun x => bitcast_from_float .u64 (T := .f64) x

structure RealHashOps (α : Type) where
  decompose : α → Int × Int × Int
  hashNaN : Word → Word
  hashSignedZero : Bool → Word → Word
  hashInfinity : Bool → Word → Word
  trailingZeros : Int → Nat
  topSetBit : Nat → Int
  shiftRight : Int → Nat → Int
  shiftLeft : Int → Nat → Int
  toInt64 : Int → JInt .i64
  toUInt64 : Int → JInt .u64
  signbit : Int → Bool
  toFloat64 : Int → Fl double
  ldexp : Fl double → Int → Fl double

structure HashFieldOps (X Y : Type) where
  fields : X → Nat
  isdefined : X → Nat → Bool
  getfield : X → Nat → Y
  missing : Y

@[simp] def readWord (bytes : List UInt8) (count : Nat) : Word :=
  JInt.lit .u64 (Int.ofNat ((List.range count).foldl
    (fun acc k => acc + (bytes.getD k 0).toNat * 2 ^ (8 * k)) 0))

def hashArrayLoad64 (a : HashByteArray) (idx : Int) : Word :=
  JInt.lit .u64 (Int.ofNat ((List.range 8).foldl
    (fun result i => result + (a.get (idx + Int.ofNat i)).toNat * 2 ^ (8 * i)) 0))

def hashArrayLoad32 (a : HashByteArray) (idx : Int) : Word32 :=
  JInt.lit .u32 (Int.ofNat ((List.range 4).foldl
    (fun result i => result + (a.get (idx + Int.ofNat i)).toNat * 2 ^ (8 * i)) 0))

/--
Julia source: base/hashing.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(data::Any) = hash(data, HASH_SEED)
```
-/
def hashAny {α : Type} (dispatch : α → Word → Word) (data : α) : Word :=
  dispatch data hashSeed

/--
Julia source: base/hashing.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(w::WeakRef, h::UInt) = hash(w.value, h)
```
-/
def hashWeakRef {α : Type} (dispatch : α → Word → Word) (w : WeakRef α) (h : Word) : Word :=
  dispatch w.value h

/--
Julia source: base/hashing.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _jl_type_hash(T::Type) = @assume_effects :total ccall(:jl_type_hash, UInt, (Any,), T)
```
-/
def jlTypeHash {α : Type} (runtimeTypeHash : α → Word) (T : α) : Word := runtimeTypeHash T

/--
Julia source: base/hashing.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(T::Type, h::UInt) = hash(_jl_type_hash(T), h)
```
-/
def hashType {α : Type} (runtimeTypeHash : α → Word)
    (hashUInt64 : Word → Word → Word) (T : α) (h : Word) : Word :=
  hashUInt64 (jlTypeHash runtimeTypeHash T) h

/--
Julia source: base/hashing.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(@nospecialize(data), h::UInt) = hash(objectid(data), h)
```
-/
def hashFallback {α : Type} (objectid : α → Word)
    (hashUInt64 : Word → Word → Word) (data : α) (h : Word) : Word :=
  hashUInt64 (objectid data) h

/--
Julia source: base/hashing.jl:48-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mul_parts(a::UInt64, b::UInt64)
    p = widemul(a, b)
    return (p >> 64) % UInt64, p % UInt64
end
```
-/
def mulParts (a b : Word) : Word × Word :=
  let p := a.val * b.val
  (JInt.lit .u64 (p / 2 ^ 64), JInt.lit .u64 p)

/--
Julia source: base/hashing.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash_mix(a::UInt64, b::UInt64) = ⊻(mul_parts(a, b)...)
```
-/
def hashMix (a b : Word) : Word :=
  let p := mulParts a b
  xorWord p.1 p.2

/--
Julia source: base/hashing.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash_mix_linear(x::Union{UInt64, UInt32}, h::UInt) = 3 *% h -% x
```
-/
def hashMixLinear {t : IntTy} (x : JInt t) (h : Word) (_hx : t = .u64 ∨ t = .u32) : Word :=
  JInt.lit .u64 3 * h - JInt.lit .u64 x.val

/--
Julia source: base/hashing.jl:56-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash_finalizer(x::UInt64)
    x ⊻= (x >> 32)
    x *%= 0x63652a4cd374b267
    x ⊻= (x >> 33)
    return x
end
```
-/
def hashFinalizer (x : Word) : Word :=
  let x := xorWord x (shrWord x 32)
  let x := x * JInt.lit .u64 0x63652a4cd374b267
  xorWord x (shrWord x 33)

/--
Julia source: base/hashing.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash_64_64(data::UInt64) = hash_finalizer(data)
```
-/
def hash64_64 (data : Word) : Word := hashFinalizer data

/--
Julia source: base/hashing.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash_64_32(data::UInt64) = hash_64_64(data) % UInt32
```
-/
def hash64_32 (data : Word) : Word32 := hashU64ToU32 (hash64_64 data)

/--
Julia source: base/hashing.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash_32_32(data::UInt32) = hash_64_32(UInt64(data))
```
-/
def hash32_32 (data : Word32) : Word32 := hash64_32 (JInt.lit .u64 data.val)

/--
Julia source: base/hashing.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::UInt64, h::UInt) = hash_uint64(hash_mix_linear(x, h))
```
-/
def hashUInt64 (x : Word) (h : Word) : Word := hash64_64 (hashMixLinear x h (Or.inl rfl))

def hashNaNSeed : Word := hashUInt64 (JInt.lit .u64 0x7ff8000000000000) hashSeed

/--
Julia source: base/hashing.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::Int64, h::UInt) = hash(bitcast(UInt64, x), h)
```
-/
def hashInt64 (x : JInt .i64) (h : Word) : Word :=
  hashUInt64 (JInt.lit .u64 x.val) h

inductive SmallInteger where
  | boolean (value : Bool)
  | fixed {t : IntTy} (value : JInt t) (width : t.bits ≤ 32)

def SmallInteger.value : SmallInteger → Int
  | .boolean false => 0
  | .boolean true => 1
  | .fixed x _ => x.val

/--
Julia source: base/hashing.jl:77-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::Union{Bool, Int8, UInt8, Int16, UInt16, Int32, UInt32}, h::UInt) = hash(Int64(x), h)
```
-/
def hashSmallInteger (x : SmallInteger) (h : Word) : Word :=
  hashInt64 (JInt.lit .i64 x.value) h

/--
Julia source: base/hashing.jl:84-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function IntegerCodeUnits(x::T) where {T<:Integer}
        # Calculate number of bytes needed (always pad to full byte)
        u = abs(x)
        num_bytes = max(cld(top_set_bit(u), 8), 1)
        return new{T}(u, num_bytes)
    end
```
-/
def integerCodeUnitsCtor {α : Type} (abs : α → α) (topSetBit : α → Int)
    (cld max : Int → Int → Int) (x : α) : IntegerCodeUnits α :=
  let u := abs x
  let numBytes := max (cld (topSetBit u) 8) 1
  ⟨u, numBytes⟩

/--
Julia source: base/hashing.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(units::IntegerCodeUnits) = (units.num_bytes,)
```
-/
def sizeIntegerCodeUnits {α : Type} (units : IntegerCodeUnits α) : Int × Unit :=
  (units.numBytes, ())

/--
Julia source: base/hashing.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(units::IntegerCodeUnits) = units.num_bytes
```
-/
def lengthIntegerCodeUnits {α : Type} (units : IntegerCodeUnits α) : Int := units.numBytes

/--
Julia source: base/hashing.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline getindex(units::IntegerCodeUnits, i::Int) = (units.uvalue >>> (8 * (i - 1))) % UInt8
```
-/
def getindexIntegerCodeUnits {α : Type} (shiftRight : α → Int → α)
    (modUInt8 : α → UInt8) (units : IntegerCodeUnits α) (i : Int) : UInt8 :=
  modUInt8 (shiftRight units.uvalue (8 * (i - 1)))

/--
Julia source: base/hashing.jl:94-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline load_le_array(::Type{UInt64}, units::IntegerCodeUnits, idx) = (units.uvalue >>> (8 * (idx - 1))) % UInt64
```
-/
def loadLEArrayU64Units {α : Type} (shiftRight : α → Int → α)
    (modUInt64 : α → Word) (units : IntegerCodeUnits α) (idx : Int) : Word :=
  modUInt64 (shiftRight units.uvalue (8 * (idx - 1)))

/--
Julia source: base/hashing.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline load_le_array(::Type{UInt32}, units::IntegerCodeUnits, idx) = (units.uvalue >>> (8 * (idx - 1))) % UInt32
```
-/
def loadLEArrayU32Units {α : Type} (shiftRight : α → Int → α)
    (modUInt32 : α → Word32) (units : IntegerCodeUnits α) (idx : Int) : Word32 :=
  modUInt32 (shiftRight units.uvalue (8 * (idx - 1)))

/--
Julia source: base/hashing.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunits(x::Integer) = IntegerCodeUnits(x)
```
-/
def codeunitsInteger {α : Type} (abs : α → α) (topSetBit : α → Int)
    (cld max : Int → Int → Int) (x : α) : IntegerCodeUnits α :=
  integerCodeUnitsCtor abs topSetBit cld max x

/--
Julia source: base/hashing.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
utf8units(s::AbstractString) = codeunit(s) <: UInt8 ? codeunits(s) : UTF8Units(s)
```
-/
def utf8units {A S : Type} (codeunitIsUInt8 : S → Bool) (codeunits : S → A)
    (s : S) : UTF8UnitsResult A S :=
  if codeunitIsUInt8 s then .codeunits (codeunits s) else .iterated ⟨s⟩

/--
Julia source: base/hashing.jl:109-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(units::UTF8Units)
    char_result = iterate(units.string)
    char_result === nothing && return nothing
    char, char_state = char_result

    # Decode char to UTF-8 bytes (similar to the write function)
    u = bswap(reinterpret(UInt32, char))

    # Return first byte and set up state for remaining bytes
    first_byte = u % UInt8
    remaining_bytes = u >> 8
    return first_byte, (char_state, remaining_bytes)
end
```
-/
def iterateUTF8First {S State Char : Type} (iterate : S → Option (Char × State))
    (reinterpret : Char → Word32) (bswap : Word32 → Word32) (units : UTF8Units S) :
    Option (UInt8 × UTF8State State) := do
  let (char, charState) ← iterate units.string
  let u := bswap (reinterpret char)
  let firstByte := UInt8.ofNat (u.val.toNat % 256)
  let remainingBytes := shrWord32 u 8
  pure (firstByte, (charState, remainingBytes))

/--
Julia source: base/hashing.jl:123-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(units::UTF8Units, state)
    char_state, remaining_bytes = state
    # If we have more bytes from current char, return next byte
    if remaining_bytes != 0
        byte = remaining_bytes % UInt8
        new_remaining = remaining_bytes >> 8
        return byte, (char_state, new_remaining)
    end

    # Move to next char
    char_result = iterate(units.string, char_state)
    char_result === nothing && return nothing
    char, new_char_state = char_result

    # Decode new char to UTF-8 bytes
    u = bswap(reinterpret(UInt32, char))

    # Return first byte and set up state for remaining bytes
    first_byte = u % UInt8
    remaining_bytes = u >> 8

    return first_byte, (new_char_state, remaining_bytes)
end
```
-/
def iterateUTF8State {S State Char : Type} (iterate : S → State → Option (Char × State))
    (reinterpret : Char → Word32) (bswap : Word32 → Word32) (units : UTF8Units S)
    (state : UTF8State State) : Option (UInt8 × UTF8State State) :=
  let (charState, remainingBytes) := state
  if remainingBytes.val != 0 then
    let byte := UInt8.ofNat (remainingBytes.val.toNat % 256)
    let newRemaining := shrWord32 remainingBytes 8
    some (byte, (charState, newRemaining))
  else
    match iterate units.string charState with
    | none => none
    | some (char, newCharState) =>
        let u := bswap (reinterpret char)
        let firstByte := UInt8.ofNat (u.val.toNat % 256)
        let remainingBytes := shrWord32 u 8
        some (firstByte, (newCharState, remainingBytes))

/--
Julia source: base/hashing.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash_integer(x::Integer, h::UInt) = _hash_integer(x, UInt64(h)) % UInt
```
-/
def hashInteger {α : Type} (abs : α → α) (isnegative : α → Bool)
    (topSetBit : α → Int) (cld max : Int → Int → Int)
    (core : (α → α) → (α → Bool) → (α → Int) → (Int → Int → Int) → (Int → Int → Int) →
      (IntegerCodeUnits α → Word → HashSecret → Word) → α → Word → Word)
    (hashBytes : IntegerCodeUnits α → Word → HashSecret → Word)
    (x : α) (h : Word) : Word :=
  core abs isnegative topSetBit cld max hashBytes x h

/--
Julia source: base/hashing.jl:148-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hash_integer(
        x::Integer,
        seed::UInt64,
        secret::NTuple{4, UInt64} = HASH_SECRET
    )
    # Handle sign by XOR-ing with seed
    seed ⊻= (x < 0)
    # Get little-endian byte representation of absolute value
    # and hash using the new safe hash_bytes function
    u = abs(x) # n.b.: this hashes typemin(IntN) correctly even if abs fails
    return hash_bytes(codeunits(u), seed, secret)
end
```
-/
def _hashInteger {α : Type} (abs : α → α) (isnegative : α → Bool)
    (topSetBit : α → Int) (cld max : Int → Int → Int)
    (hashBytes : IntegerCodeUnits α → Word → HashSecret → Word)
    (x : α) (seed : Word) (secret : HashSecret := hashSecret) : Word :=
  let seed := if isnegative x then xorWord seed (JInt.lit .u64 1) else seed
  let u := abs x
  hashBytes (codeunitsInteger abs topSetBit cld max u) seed secret

/--
Julia source: base/hashing.jl:165-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(x::Float64, h::UInt)
    # see comments on trunc and hash(Real, UInt)
    if typemin(Int64) <= x < typemax(Int64)
        xi = fptosi(Int64, x)
        if isequal(xi, x)
            return hash(xi, h)
        end
    elseif typemin(UInt64) <= x < typemax(UInt64)
        xu = fptoui(UInt64, x)
        if isequal(xu, x)
            return hash(xu, h)
        end
    elseif isnan(x)
        return hx_NaN ⊻ h # NaN does not have a stable bit pattern
    end
    return hash(bitcast(UInt64, x), h)
end
```
-/
def hashFloat64 {α : Type} (ops : FloatHashOps α) (x : α) (h : Word) : Word :=
  if ops.leIntFloat (JInt.typemin .i64) x && ops.ltFloatInt x (JInt.typemax .i64) then
    let xi := ops.fptosi x
    if ops.isequalI64 xi x then hashInt64 xi h
    else hashUInt64 (ops.bitcastU64 x) h
  else if ops.leUIntFloat (JInt.lit .u64 0) x && ops.ltFloatUInt x (JInt.typemax .u64) then
    let xu := ops.fptoui x
    if ops.isequalU64 xu x then hashUInt64 xu h
    else hashUInt64 (ops.bitcastU64 x) h
  else if ops.isnan x then xorWord hashNaNSeed h
  else hashUInt64 (ops.bitcastU64 x) h

/--
Julia source: base/hashing.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::Float32, h::UInt) = hash(Float64(x), h)
```
-/
def hashFloat32 {α : Type} (toFloat64 : α → Fl double) (ops : FloatHashOps (Fl double))
    (x : α) (h : Word) : Word :=
  hashFloat64 ops (toFloat64 x) h

/--
Julia source: base/hashing.jl:185-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(x::Float16, h::UInt)
    # see comments on trunc and hash(Real, UInt)
    if isfinite(x) # all finite Float16 fit in Int64
        xi = fptosi(Int64, x)
        if isequal(xi, x)
            return hash(xi, h)
        end
    elseif isnan(x)
        return hx_NaN ⊻ h # NaN does not have a stable bit pattern
    end
    return hash(bitcast(UInt64, Float64(x)), h)
end
```
-/
def hashFloat16 {α : Type} (ops : Float16HashOps α) (x : α) (h : Word) : Word :=
  if ops.isfinite x then
    let xi := ops.fptosi x
    if ops.isequalI64 xi x then hashInt64 xi h
    else hashUInt64 (ops.bitcastFloat64U64 (ops.toFloat64 x)) h
  else if ops.isnan x then xorWord hashNaNSeed h
  else hashUInt64 (ops.bitcastFloat64U64 (ops.toFloat64 x)) h

def hashFloat64Canonical (x : Fl double) (h : Word) : Word :=
  hashFloat64 standardHashFloat64Ops x h

def hashNaNCanonical (h : Word) : Word := hashFloat64Canonical Fl.nan h

def hashSignedZeroCanonical (positive : Bool) (h : Word) : Word :=
  hashFloat64Canonical (Fl.zero (!positive)) h

def hashInfinityCanonical (positive : Bool) (h : Word) : Word :=
  hashFloat64Canonical (Fl.inf (!positive)) h

/--
Julia source: base/hashing.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hash_shl!(x, n) = (x << n)
```
-/
def hashShl {α : Type} (shl : α → Nat → α) (x : α) (n : Nat) : α := shl x n

/--
Julia source: base/hashing.jl:200-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(x::Real, h::UInt)
    # decompose x as num*2^pow/den
    num, pow, den = decompose(x)

    # handle special values
    num == 0 && den == 0 && return hash(NaN, h)
    num == 0 && return hash(ifelse(den > 0, 0.0, -0.0), h)
    den == 0 && return hash(ifelse(num > 0, Inf, -Inf), h)

    # normalize decomposition
    if den < 0
        num = -num
        den = -den
    end
    num_z = trailing_zeros(num)

    num >>= num_z
    den_z = trailing_zeros(den)
    den >>= den_z
    pow += num_z - den_z
    # If the real can be represented as an Int64, UInt64, or Float64, hash as those types.
    # To be an Integer the denominator must be 1 and the power must be non-negative.
    if den == 1
        # left = ceil(log2(num*2^pow))
        left = top_set_bit(abs(num)) + pow
        # 2^-1074 is the minimum Float64 so if the power is smaller, not a Float64
        if -1074 <= pow
            if 0 <= pow # if pow is non-negative, it is an integer
                left <= 63 && return hash(Int64(num) << Int(pow), h)
                left <= 64 && !signbit(num) && return hash(UInt64(num) << Int(pow), h)
            end # typemin(Int64) handled by Float64 case
            # 2^1024 is the maximum Float64 so if the power is greater, not a Float64
            # Float64s have 53 mantissa bits (including implicit bit)
            left <= 1024 && left - pow <= 53 && return hash(ldexp(Float64(num), pow), h)
        end
    else
        h = hash_integer(den, h)
    end
    # handle generic rational values
    h = hash_integer(pow, h)

    # trimming only whole bytes of trailing zeros simplifies greatly
    # some specializations for memory-backed bitintegers
    h = hash_integer((pow > 0) ? _hash_shl!(num, pow % 8) : num, h)
    return h
end
```
-/
def hashReal {α : Type} (ops : RealHashOps α)
    (hashFloat64 : Fl double → Word → Word) (hashInteger : Int → Word → Word)
    (hashInt64 : JInt .i64 → Word → Word) (hashUInt64 : Word → Word → Word)
    (x : α) (h : Word) : Word := Id.run do
  let (num0, pow0, den0) := ops.decompose x
  if num0 = 0 && den0 = 0 then return ops.hashNaN h
  if num0 = 0 then return ops.hashSignedZero (den0 > 0) h
  if den0 = 0 then return ops.hashInfinity (num0 > 0) h
  let mut num := num0
  let mut den := den0
  let mut pow := pow0
  if den < 0 then
    num := -num
    den := -den
  let numZ := ops.trailingZeros num
  num := ops.shiftRight num numZ
  let denZ := ops.trailingZeros den
  den := ops.shiftRight den denZ
  pow := pow + Int.ofNat numZ - Int.ofNat denZ
  let mut seed := h
  if den = 1 then
    let left := ops.topSetBit (num.natAbs) + pow
    if -1074 ≤ pow then
      if 0 ≤ pow then
        if left ≤ 63 then return hashInt64 (ops.toInt64 (ops.shiftLeft num pow.toNat)) seed
        if left ≤ 64 && !ops.signbit num then
          return hashUInt64 (ops.toUInt64 (ops.shiftLeft num pow.toNat)) seed
      if left ≤ 1024 && left - pow ≤ 53 then
        return hashFloat64 (ops.ldexp (ops.toFloat64 num) pow) seed
  else
    seed := hashInteger den seed
  seed := hashInteger pow seed
  let n := if pow > 0 then (pow % 8).toNat else 0
  let finalNum := if pow > 0 then ops.shiftLeft num n else num
  return hashInteger finalNum seed

/--
Julia source: base/hashing.jl:251-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    hash(x::QuoteNode, h::UInt) = hash(x.value, h ⊻ 0x2c97bf8b3de87020)
```
-/
def hashQuoteNode64 {α : Type} (hash : α → Word → Word) (value : α) (h : Word) : Word :=
  hash value (xorWord h hashTypeSeed)

/--
Julia source: base/hashing.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    hash(x::PhiNode, h::UInt) = hash(x.edges, hash(x.values, h ⊻ 0x2c97bf8b3de87020))
```
-/
def hashPhiNode64 {A B : Type} (hashEdges : A → Word → Word) (hashValues : B → Word → Word)
    (edges : A) (values : B) (h : Word) : Word :=
  hashEdges edges (hashValues values (xorWord h hashTypeSeed))

/--
Julia source: base/hashing.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    hash(x::PhiCNode, h::UInt) = hash(x.values, h ⊻ 0x2c97bf8b3de87020)
```
-/
def hashPhiCNode64 {α : Type} (hash : α → Word → Word) (values : α) (h : Word) : Word :=
  hash values (xorWord h hashTypeSeed)

/--
Julia source: base/hashing.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    hash(x::QuoteNode, h::UInt) = hash(x.value, h ⊻ 0x469d72af)
```
-/
def hashQuoteNode32 {α : Type} (hash : α → Word32 → Word32) (value : α) (h : Word32) : Word32 :=
  hash value (xorWord32 h (JInt.lit .u32 0x469d72af))

/--
Julia source: base/hashing.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    hash(x::PhiNode, h::UInt) = hash(x.edges, hash(x.values, h ⊻ 0x469d72af))
```
-/
def hashPhiNode32 {A B : Type} (hashEdges : A → Word32 → Word32) (hashValues : B → Word32 → Word32)
    (edges : A) (values : B) (h : Word32) : Word32 :=
  hashEdges edges (hashValues values (xorWord32 h (JInt.lit .u32 0x469d72af)))

/--
Julia source: base/hashing.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    hash(x::PhiCNode, h::UInt) = hash(x.values, h ⊻ 0x469d72af)
```
-/
def hashPhiCNode32 {α : Type} (hash : α → Word32 → Word32) (values : α) (h : Word32) : Word32 :=
  hash values (xorWord32 h (JInt.lit .u32 0x469d72af))

/--
Julia source: base/hashing.jl:260-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(x::Expr, h::UInt)
    h = hash(x.head, h ⊻ (UInt === UInt64 ? 0x83c7900696d26dc6 : 0x469d72af))
    # Hint that `x.args::Vector{Any}` is mostly Expr, Symbol, and LineNumberNode.
    hash_shaped(x.args, h ⊻ hash_abstractarray_seed, (Val{Expr}(), Val{Symbol}(), Val{LineNumberNode}()))
end
```
-/
def hashExpr {H A Tags : Type} (head : H) (args : A) (hashHead : H → Word → Word)
    (hashShaped : A → Word → Tags → Word) (tags : Tags) (arraySeed : Word) (h : Word) : Word :=
  let h := hashHead head (xorWord h hashExprSeed)
  hashShaped args (xorWord h arraySeed) tags

/--
Julia source: base/hashing.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(x::CodeInfo, h::UInt)
    h ⊻= UInt === UInt64 ? 0x2c97bf8b3de87020 : 0x469d72af
    for i in 1:nfields(x)
        h = hash(isdefined(x, i) ? getfield(x, i) : missing, h)
    end
    return h
end
```
-/
def hashCodeInfo {X Y : Type} (ops : HashFieldOps X Y) (hash : Y → Word → Word)
    (x : X) (h : Word) : Word :=
  ((List.range (ops.fields x)).foldl (fun h i =>
    hash (if ops.isdefined x (i + 1) then ops.getfield x (i + 1) else ops.missing) h)
    (xorWord h hashTypeSeed))

/--
Julia source: base/hashing.jl:274-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(x::DebugInfo, h::UInt)
    h ⊻= UInt === UInt64 ? 0x2c97bf8b3de87020 : 0x469d72af
    for i in 1:nfields(x)
        h = hash(getfield(x, i), h)
    end
    return h
end
```
-/
def hashDebugInfo {X Y : Type} (ops : HashFieldOps X Y) (hash : Y → Word → Word)
    (x : X) (h : Word) : Word :=
  ((List.range (ops.fields x)).foldl (fun h i => hash (ops.getfield x (i + 1)) h)
    (xorWord h hashTypeSeed))

/--
Julia source: base/hashing.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::Symbol) = objectid(x)
```
-/
def hashSymbol {α : Type} (objectid : α → Word) (symbol : α) : Word := objectid symbol

structure GlobalRef (M N : Type) where
  mod : M
  name : N

/--
Julia source: base/hashing.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::GlobalRef, h::UInt) = hash(x.name, hash(x.mod, h ⊻ hashgr_seed))
```
-/
def hashGlobalRef {M N : Type} (hashMod : M → Word → Word) (hashName : N → Word → Word)
    (x : GlobalRef M N) (h : Word) : Word :=
  hashName x.name (hashMod x.mod (xorWord h hashGlobalRefSeed))

structure PartialStruct (T U F : Type) where
  typ : T
  undefs : U
  fields : F

/--
Julia source: base/hashing.jl:287-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(x::PartialStruct, h::UInt)
    h ⊻= hashps_seed
    h = hash(x.typ, h)
    h = hash(x.undefs, h)
    h = hash(x.fields, h)
    return h
end
```
-/
def hashPartialStruct {T U F : Type} (hashType : T → Word → Word)
    (hashUndefs : U → Word → Word) (hashFields : F → Word → Word)
    (x : PartialStruct T U F) (h : Word) : Word :=
  let h := xorWord h hashPartialStructSeed
  let h := hashType x.typ h
  let h := hashUndefs x.undefs h
  hashFields x.fields h

/--
Julia source: base/hashing.jl:296-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
load_le(::Type{T}, ptr::Ptr{UInt8}, i, align::Int=1) where {T <: Union{UInt32, UInt64}} =
    pointerref(convert(Ptr{T}, ptr + i - 1), 1, align)
```
-/
def loadLE {P Q α : Type} (convert : P → Q) (pointerAdd : Q → Int → Q)
    (pointerref : Q → Nat → Nat → α) (ptr : P) (i : Int) (align : Nat) : α :=
  pointerref (pointerAdd (convert ptr) (i - 1)) 1 align

def hashPointer48Loop {Ptr : Type} (ops : HashPointerOps Ptr) (ptr : Ptr)
    (secret : HashSecret) (align : Nat) :
    Nat → Nat → Word → Word → Word → Word × Word × Word × Nat × Nat
  | i, pos, seed, see1, see2 =>
      if i > 48 then
        let load64 (offset : Nat) (alignment : Nat) :=
          loadLE ops.convert64 ops.add64 ops.pointerref64 ptr (Int.ofNat offset) alignment
        let seed := hashMix
          (xorWord (load64 pos align) secret.1)
          (xorWord (load64 (pos + 8) align) seed)
        let see1 := hashMix
          (xorWord (load64 (pos + 16) align) secret.2.1)
          (xorWord (load64 (pos + 24) align) see1)
        let see2 := hashMix
          (xorWord (load64 (pos + 32) align) secret.2.2.1)
          (xorWord (load64 (pos + 40) align) see2)
        hashPointer48Loop ops ptr secret align (i - 48) (pos + 48) seed see1 see2
      else (seed, see1, see2, pos, i)
termination_by i _pos _seed _see1 _see2 => i
decreasing_by omega

/--
Julia source: base/hashing.jl:301-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :terminates_globally function hash_bytes(
        ptr::Ptr{UInt8},
        n::Int,
        seed::UInt64,
        secret::NTuple{4, UInt64},
        ::Val{A}=Val(1)
    ) where {A}
    # Adapted with gratitude from [rapidhash](https://github.com/Nicoshev/rapidhash)
    align = min(A, 8)
    buflen = UInt64(n)
    seed = seed ⊻ hash_mix(seed ⊻ secret[3], secret[2])

    a = zero(UInt64)
    b = zero(UInt64)
    i = buflen

    if buflen ≤ 16
        if buflen ≥ 4
            seed ⊻= buflen
            if buflen ≥ 8
                a = load_le(UInt64, ptr, 1, align)
                b = load_le(UInt64, ptr, n - 7)
            else
                a = UInt64(load_le(UInt32, ptr, 1, align))
                b = UInt64(load_le(UInt32, ptr, n - 3))
            end
        elseif buflen > 0
            a = (UInt64(unsafe_load(ptr)) << 45) | UInt64(unsafe_load(ptr, n))
            b = UInt64(unsafe_load(ptr, div(n, 2) + 1))
        end
    else
        pos = 1
        if i > 48
            see1 = seed
            see2 = seed
            while i > 48
                seed = hash_mix(
                    load_le(UInt64, ptr, pos, align) ⊻ secret[1],
                    load_le(UInt64, ptr, pos + 8, align) ⊻ seed
                )
                see1 = hash_mix(
                    load_le(UInt64, ptr, pos + 16, align) ⊻ secret[2],
                    load_le(UInt64, ptr, pos + 24, align) ⊻ see1
                )
                see2 = hash_mix(
                    load_le(UInt64, ptr, pos + 32, align) ⊻ secret[3],
                    load_le(UInt64, ptr, pos + 40, align) ⊻ see2
                )
                pos += 48
                i -= 48
            end
            seed ⊻= see1
            seed ⊻= see2
        end
        if i > 16
            seed = hash_mix(
                load_le(UInt64, ptr, pos, align) ⊻ secret[3],
                load_le(UInt64, ptr, pos + 8, align) ⊻ seed
            )
            if i > 32
                seed = hash_mix(
                    load_le(UInt64, ptr, pos + 16, align) ⊻ secret[3],
                    load_le(UInt64, ptr, pos + 24, align) ⊻ seed
                )
            end
        end

        a = load_le(UInt64, ptr, n - 15) ⊻ i
        b = load_le(UInt64, ptr, n - 7)
    end

    a = a ⊻ secret[2]
    b = b ⊻ seed
    b, a = mul_parts(a, b)
    return hash_mix(a ⊻ secret[4], b ⊻ secret[2] ⊻ i)
end
```
-/
def hashBytesPointer {Ptr : Type} (ops : HashPointerOps Ptr) (ptr : Ptr) (n : Nat)
    (seed0 : Word) (secret : HashSecret) (alignment : Nat := 1) : Word := Id.run do
  let align := min alignment 8
  let buflen := JInt.lit .u64 n
  let mut seed := xorWord seed0 (hashMix (xorWord seed0 secret.2.2.1) secret.2.1)
  let mut a : Word := JInt.lit .u64 0
  let mut b : Word := JInt.lit .u64 0
  let mut i := n
  let load64 (offset : Nat) (loadAlign : Nat := 1) :=
    loadLE ops.convert64 ops.add64 ops.pointerref64 ptr (Int.ofNat offset) loadAlign
  let load32 (offset : Nat) (loadAlign : Nat := 1) :=
    loadLE ops.convert32 ops.add32 ops.pointerref32 ptr (Int.ofNat offset) loadAlign
  if buflen.val ≤ 16 then
    if buflen.val ≥ 4 then
      seed := xorWord seed buflen
      if buflen.val ≥ 8 then
        a := load64 1 align
        b := load64 (n - 7)
      else
        a := JInt.lit .u64 (load32 1 align).val
        b := JInt.lit .u64 (load32 (n - 3)).val
    else if buflen.val > 0 then
      a := shlWord (JInt.lit .u64 (ops.load8 ptr 1).toNat) 45 +
        JInt.lit .u64 (ops.load8 ptr n).toNat
      b := JInt.lit .u64 (ops.load8 ptr (n / 2 + 1)).toNat
  else
    let mut pos := 1
    if i > 48 then
      let (newSeed, see1, see2, newPos, newI) :=
        hashPointer48Loop ops ptr secret align i pos seed seed seed
      seed := xorWord (xorWord newSeed see1) see2
      pos := newPos
      i := newI
    if i > 16 then
      seed := hashMix
        (xorWord (load64 pos align) secret.2.2.1)
        (xorWord (load64 (pos + 8) align) seed)
      if i > 32 then
        seed := hashMix
          (xorWord (load64 (pos + 16) align) secret.2.2.1)
          (xorWord (load64 (pos + 24) align) seed)
    a := xorWord (load64 (n - 15)) (JInt.lit .u64 i)
    b := load64 (n - 7)
  a := xorWord a secret.2.1
  b := xorWord b seed
  let (high, low) := mulParts a b
  return hashMix (xorWord low secret.2.2.2) (xorWord (xorWord high secret.2.1) (JInt.lit .u64 i))

/--
Julia source: base/hashing.jl:378-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function load_le_array(::Type{UInt64}, arr::AbstractArray{UInt8}, idx)
    # n.b. for whatever reason, writing this as a loop ensures LLVM
    # optimizations (particular SROA) don't make a disaster of this code
    # early on so it can actually emit the optimal result
    result = zero(UInt64)
    for i in 0:7
        byte = @inbounds arr[idx + i]
        result |= UInt64(byte) << (8 * i)
    end
    return result
end
```
-/
def loadLEArrayU64 (arr : HashByteArray) (idx : Int) : Word :=
  (List.range 8).foldl (fun result i =>
    let byte := arr.get (idx + Int.ofNat i)
    result + JInt.lit .u64 (Int.ofNat (byte.toNat * 2 ^ (8 * i))))
    (JInt.lit .u64 0)

/--
Julia source: base/hashing.jl:390-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function load_le_array(::Type{UInt32}, arr::AbstractArray{UInt8}, idx)
    result = zero(UInt32)
    for i in 0:3
        byte = @inbounds arr[idx + i]
        result |= UInt32(byte) << (8 * i)
    end
    return result
end
```
-/
def loadLEArrayU32 (arr : HashByteArray) (idx : Int) : Word32 :=
  (List.range 4).foldl (fun result i =>
    let byte := arr.get (idx + Int.ofNat i)
    result + JInt.lit .u32 (Int.ofNat (byte.toNat * 2 ^ (8 * i))))
    (JInt.lit .u32 0)

def hashArray48Loop (arr : HashByteArray) (secret : HashSecret) :
    Nat → Int → Word → Word → Word → Word × Word × Word × Int × Nat
  | i, pos, seed, see1, see2 =>
      if i > 48 then
        let seed := hashMix
          (xorWord (loadLEArrayU64 arr (arr.firstIndex + pos)) secret.1)
          (xorWord (loadLEArrayU64 arr (arr.firstIndex + pos + 8)) seed)
        let see1 := hashMix
          (xorWord (loadLEArrayU64 arr (arr.firstIndex + pos + 16)) secret.2.1)
          (xorWord (loadLEArrayU64 arr (arr.firstIndex + pos + 24)) see1)
        let see2 := hashMix
          (xorWord (loadLEArrayU64 arr (arr.firstIndex + pos + 32)) secret.2.2.1)
          (xorWord (loadLEArrayU64 arr (arr.firstIndex + pos + 40)) see2)
        hashArray48Loop arr secret (i - 48) (pos + 48) seed see1 see2
      else (seed, see1, see2, pos, i)
termination_by i _pos _seed _see1 _see2 => i
decreasing_by omega

/--
Julia source: base/hashing.jl:399-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :terminates_globally function hash_bytes(
        arr::AbstractArray{UInt8},
        seed::UInt64,
        secret::NTuple{4, UInt64}
    )
    # Adapted with gratitude from [rapidhash](https://github.com/Nicoshev/rapidhash)
    n = length(arr)
    buflen = UInt64(n)
    seed = seed ⊻ hash_mix(seed ⊻ secret[3], secret[2])
    firstidx = firstindex(arr)

    a = zero(UInt64)
    b = zero(UInt64)
    i = buflen

    if buflen ≤ 16
        if buflen ≥ 4
            seed ⊻= buflen
            if buflen ≥ 8
                a = load_le_array(UInt64, arr, firstidx)
                b = load_le_array(UInt64, arr, firstidx + n - 8)
            else
                a = UInt64(load_le_array(UInt32, arr, firstidx))
                b = UInt64(load_le_array(UInt32, arr, firstidx + n - 4))
            end
        elseif buflen > 0
            a = (UInt64(@inbounds arr[firstidx]) << 45) | UInt64(@inbounds arr[firstidx + n - 1])
            b = UInt64(@inbounds arr[firstidx + div(n, 2)])
        end
    else
        pos = 0
        if i > 48
            see1 = seed
            see2 = seed
            while i > 48
                seed = hash_mix(
                    load_le_array(UInt64, arr, firstidx + pos) ⊻ secret[1],
                    load_le_array(UInt64, arr, firstidx + pos + 8) ⊻ seed
                )
                see1 = hash_mix(
                    load_le_array(UInt64, arr, firstidx + pos + 16) ⊻ secret[2],
                    load_le_array(UInt64, arr, firstidx + pos + 24) ⊻ see1
                )
                see2 = hash_mix(
                    load_le_array(UInt64, arr, firstidx + pos + 32) ⊻ secret[3],
                    load_le_array(UInt64, arr, firstidx + pos + 40) ⊻ see2
                )
                pos += 48
                i -= 48
            end
            seed ⊻= see1
            seed ⊻= see2
        end
        if i > 16
            seed = hash_mix(
                load_le_array(UInt64, arr, firstidx + pos) ⊻ secret[3],
                load_le_array(UInt64, arr, firstidx + pos + 8) ⊻ seed
            )
            if i > 32
                seed = hash_mix(
                    load_le_array(UInt64, arr, firstidx + pos + 16) ⊻ secret[3],
                    load_le_array(UInt64, arr, firstidx + pos + 24) ⊻ seed
                )
            end
        end

        a = load_le_array(UInt64, arr, firstidx + n - 16) ⊻ i
        b = load_le_array(UInt64, arr, firstidx + n - 8)
    end

    a = a ⊻ secret[2]
    b = b ⊻ seed
    b, a = mul_parts(a, b)
    return hash_mix(a ⊻ secret[4], b ⊻ secret[2] ⊻ i)
end
```
-/
def hashBytesArray (arr : HashByteArray) (seed0 : Word) (secret : HashSecret) : Word := Id.run do
  let n := arr.length
  let buflen := JInt.lit .u64 n
  let mut seed := xorWord seed0 (hashMix (xorWord seed0 secret.2.2.1) secret.2.1)
  let firstidx := arr.firstIndex
  let mut a : Word := JInt.lit .u64 0
  let mut b : Word := JInt.lit .u64 0
  let mut i := n
  if buflen.val ≤ 16 then
    if buflen.val ≥ 4 then
      seed := xorWord seed buflen
      if buflen.val ≥ 8 then
        a := loadLEArrayU64 arr firstidx
        b := loadLEArrayU64 arr (firstidx + Int.ofNat n - 8)
      else
        a := JInt.lit .u64 (loadLEArrayU32 arr firstidx).val
        b := JInt.lit .u64 (loadLEArrayU32 arr (firstidx + Int.ofNat n - 4)).val
    else if buflen.val > 0 then
      a := shlWord (JInt.lit .u64 (arr.get firstidx).toNat) 45 +
        JInt.lit .u64 (arr.get (firstidx + Int.ofNat n - 1)).toNat
      b := JInt.lit .u64 (arr.get (firstidx + Int.ofNat (n / 2))).toNat
  else
    let mut pos : Int := 0
    if i > 48 then
      let (newSeed, see1, see2, newPos, newI) :=
        hashArray48Loop arr secret i pos seed seed seed
      seed := xorWord (xorWord newSeed see1) see2
      pos := newPos
      i := newI
    if i > 16 then
      seed := hashMix
        (xorWord (loadLEArrayU64 arr (firstidx + pos)) secret.2.2.1)
        (xorWord (loadLEArrayU64 arr (firstidx + pos + 8)) seed)
      if i > 32 then
        seed := hashMix
          (xorWord (loadLEArrayU64 arr (firstidx + pos + 16)) secret.2.2.1)
          (xorWord (loadLEArrayU64 arr (firstidx + pos + 24)) seed)
    a := xorWord (loadLEArrayU64 arr (firstidx + Int.ofNat n - 16)) (JInt.lit .u64 i)
    b := loadLEArrayU64 arr (firstidx + Int.ofNat n - 8)
  a := xorWord a secret.2.1
  b := xorWord b seed
  let (high, low) := mulParts a b
  return hashMix (xorWord low secret.2.2.2) (xorWord (xorWord high secret.2.1) (JInt.lit .u64 i))

def intMagnitudeModel (x : Int) : Int := Int.ofNat x.natAbs

def intTopSetBitModel (x : Int) : Int :=
  if x = 0 then 0 else Int.ofNat (x.natAbs.log2 + 1)

def intCeilDivModel (x y : Int) : Int := x / y + if x % y = 0 then 0 else 1

def integerUnitsArray (units : IntegerCodeUnits Int) : HashByteArray :=
  { firstIndex := 1
    length := units.numBytes.toNat
    get := fun i => getindexIntegerCodeUnits
      (fun x shift => x / Int.ofNat (2 ^ shift.toNat))
      (fun x => UInt8.ofNat (x.toNat % 256)) units i }

def hashIntegerInt (x : Int) (h : Word) : Word :=
  hashInteger intMagnitudeModel (fun x => decide (x < 0)) intTopSetBitModel intCeilDivModel (fun a b => max a b)
    _hashInteger (fun units seed secret => hashBytesArray (integerUnitsArray units) seed secret) x h

/--
Julia source: base/hashing.jl:479-482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function concat_shift(low::UInt64, high::UInt64, shift_bytes::UInt8)
    shift_bits = (shift_bytes * 0x8) & 0x3f
    return (low >> shift_bits) | (high << (0x40 - shift_bits))
end
```
-/
def concatShift (low high : Word) (shiftBytes : UInt8) : Word :=
  let shiftBits := shiftBytes.toNat * 8 % 64
  (shrWord low shiftBits) + (shlWord high (64 - shiftBits))

/--
Julia source: base/hashing.jl:484-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function read_uint64_from_uint8_iter(iter, state)
    value = zero(UInt64)
    @nexprs 8 i -> begin
        next_result = iterate(iter, state)
        next_result === nothing && return value, state, UInt8(i - 1)
        byte, state = next_result
        value |= UInt64(byte) << ((i - 1) * 8)
    end
    return value, state, 0x8
end
```
-/
def readUInt64State {State : Type} (iter : HashByteIterator State) (state : State) : Word × State × UInt8 :=
  let (_active, value, finalState, count) := (List.range 8).foldl
    (fun (active, value, state, count) i =>
      if !active then (false, value, state, count)
      else match iter.next state with
        | none => (false, value, state, count)
        | some (byte, newState) =>
            let wordByte := JInt.lit .u64 byte.toNat
            (true, value + shlWord wordByte (8 * i), newState, count + 1))
    (true, JInt.lit .u64 0, state, 0)
  (value, finalState, UInt8.ofNat count)

/--
Julia source: base/hashing.jl:495-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function read_uint64_from_uint8_iter(iter)
    next_result = iterate(iter)
    next_result === nothing && return nothing
    byte, state = next_result
    value = UInt64(byte)
    @nexprs 7 i -> begin
        next_result = iterate(iter, state)
        next_result === nothing && return value, state, UInt8(i)
        byte, state = next_result
        value |= UInt64(byte::UInt8) << (i * 8)
    end
    return value, state, 0x8
end
```
-/
def readUInt64First {State : Type} (iter : HashByteIterator State) : Option (Word × State × UInt8) :=
  match iter.first with
  | none => none
  | some (byte, state) =>
      let initial := JInt.lit .u64 byte.toNat
      let (active, value, finalState, count) := (List.range 7).foldl
        (fun (active, value, state, count) j =>
          if !active then (false, value, state, count)
          else
            let i := j + 1
            match iter.next state with
            | none => (false, value, state, i)
            | some (nextByte, newState) =>
                let wordByte := JInt.lit .u64 nextByte.toNat
                (true, value + shlWord wordByte (8 * i), newState, i + 1))
        (true, initial, state, 1)
      let count := if active then 8 else count
      some (value, finalState, UInt8.ofNat count)

partial def hashIteratorChunks {State : Type} (iter : HashByteIterator State)
    (secret : HashSecret) (s : IteratorHashState State) : IteratorHashState State := Id.run do
  let (l1, state, b1Byte) := readUInt64State iter s.state
  let b1 := b1Byte.toNat
  let s := { s with l1 := l1, state := state, b1 := b1 }
  if b1 < 8 then
    return { s with
      t0 := concatShift s.l5 s.l0 (UInt8.ofNat b1)
      t1 := concatShift s.l0 s.l1 (UInt8.ofNat b1) }
  let (l2, state, b2Byte) := readUInt64State iter s.state
  let b2 := b2Byte.toNat
  let s := { s with l2 := l2, state := state, b2 := b2 }
  if b2 < 8 then
    return { s with
      t0 := concatShift s.l0 s.l1 (UInt8.ofNat b2)
      t1 := concatShift s.l1 s.l2 (UInt8.ofNat b2) }
  let (l3, state, b3Byte) := readUInt64State iter s.state
  let b3 := b3Byte.toNat
  let s := { s with l3 := l3, state := state, b3 := b3 }
  if b3 < 8 then
    return { s with
      t0 := concatShift s.l1 s.l2 (UInt8.ofNat b3)
      t1 := concatShift s.l2 s.l3 (UInt8.ofNat b3) }
  let (l4, state, b4Byte) := readUInt64State iter s.state
  let b4 := b4Byte.toNat
  let s := { s with l4 := l4, state := state, b4 := b4 }
  if b4 < 8 then
    return { s with
      t0 := concatShift s.l2 s.l3 (UInt8.ofNat b4)
      t1 := concatShift s.l3 s.l4 (UInt8.ofNat b4) }
  let (l5, state, b5Byte) := readUInt64State iter s.state
  let b5 := b5Byte.toNat
  let s := { s with l5 := l5, state := state, b5 := b5 }
  if b5 < 8 then
    return { s with
      t0 := concatShift s.l3 s.l4 (UInt8.ofNat b5)
      t1 := concatShift s.l4 s.l5 (UInt8.ofNat b5) }
  let (l0, state, b0Byte) := readUInt64State iter s.state
  let b0 := b0Byte.toNat
  if b0 = 0 then
    return { s with t0 := s.l4, t1 := s.l5 }
  let seed := hashMix (xorWord s.l0 secret.1) (xorWord s.l1 s.seed)
  let see1 := hashMix (xorWord s.l2 secret.2.1) (xorWord s.l3 s.see1)
  let see2 := hashMix (xorWord s.l4 secret.2.2.1) (xorWord s.l5 s.see2)
  let s := { s with seed := seed, see1 := see1, see2 := see2, buflen := s.buflen + JInt.lit .u64 48, l0 := l0, state := state, b0 := b0, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0 }
  if b0 < 8 then
    return { s with
      t0 := concatShift s.l4 s.l5 (UInt8.ofNat b0)
      t1 := concatShift s.l5 s.l0 (UInt8.ofNat b0) }
  return hashIteratorChunks iter secret s

/--
Julia source: base/hashing.jl:509-647 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :terminates_globally function hash_bytes(
        iter,
        seed::UInt64,
        secret::NTuple{4, UInt64}
    )
    seed = seed ⊻ hash_mix(seed ⊻ secret[3], secret[2])

    a = zero(UInt64)
    b = zero(UInt64)
    buflen = zero(UInt64)

    see1 = seed
    see2 = seed
    l0 = zero(UInt64)
    l1 = zero(UInt64)
    l2 = zero(UInt64)
    l3 = zero(UInt64)
    l4 = zero(UInt64)
    l5 = zero(UInt64)
    b0 = 0x0
    b1 = 0x0
    b2 = 0x0
    b3 = 0x0
    b4 = 0x0
    b5 = 0x0
    t0 = zero(UInt64)
    t1 = zero(UInt64)

    # Handle first iteration separately
    read = read_uint64_from_uint8_iter(iter)
    if read !== nothing
        l0, state, b0 = read
        # Repeat hashing chunks until a short read
        while true
            l1, state, b1 = read_uint64_from_uint8_iter(iter, state)
            if b1 == 0x8
                l2, state, b2 = read_uint64_from_uint8_iter(iter, state)
                if b2 == 0x8
                    l3, state, b3 = read_uint64_from_uint8_iter(iter, state)
                    if b3 == 0x8
                        l4, state, b4 = read_uint64_from_uint8_iter(iter, state)
                        if b4 == 0x8
                            l5, state, b5 = read_uint64_from_uint8_iter(iter, state)
                            if b5 == 0x8
                                # Read start of next chunk
                                read = read_uint64_from_uint8_iter(iter, state)
                                if read[3] == 0x0
                                    # Read exactly 48 bytes
                                    t0 = l4
                                    t1 = l5
                                    break
                                else
                                    # Read more than 48 bytes - process and continue to next chunk
                                    seed = hash_mix(l0 ⊻ secret[1], l1 ⊻ seed)
                                    see1 = hash_mix(l2 ⊻ secret[2], l3 ⊻ see1)
                                    see2 = hash_mix(l4 ⊻ secret[3], l5 ⊻ see2)
                                    buflen += 48
                                    l0, state, b0 = read
                                    b1 = 0
                                    b2 = 0
                                    b3 = 0
                                    b4 = 0
                                    b5 = 0
                                    if b0 < 8
                                        t0 = concat_shift(l4, l5, b0)
                                        t1 = concat_shift(l5, l0, b0)
                                        break
                                    end
                                end
                            else
                                # Extract final 16 bytes at the first short read
                                t0 = concat_shift(l3, l4, b5)
                                t1 = concat_shift(l4, l5, b5)
                                break
                            end
                        else
                            t0 = concat_shift(l2, l3, b4)
                            t1 = concat_shift(l3, l4, b4)
                            break
                        end
                    else
                        t0 = concat_shift(l1, l2, b3)
                        t1 = concat_shift(l2, l3, b3)
                        break
                    end
                else
                    t0 = concat_shift(l0, l1, b2)
                    t1 = concat_shift(l1, l2, b2)
                    break
                end
            else
                t0 = concat_shift(l5, l0, b1)
                t1 = concat_shift(l0, l1, b1)
                break
            end
        end
    end

    # Partial chunk, handle based on size
    bytes_chunk = b0 + b1 + b2 + b3 + b4 + b5
    if buflen > 0
        # Finalize last full chunk
        seed ⊻= see1
        seed ⊻= see2
    end
    buflen += bytes_chunk
    if buflen ≤ 16
        if bytes_chunk ≥ 0x4
            seed ⊻= bytes_chunk
            if bytes_chunk ≥ 0x8
                a = l0
                b = t1
            else
                a = UInt64(l0 % UInt32)
                b = UInt64((l0 >>> ((0x8 * (bytes_chunk - 0x4)) % 0x3f)) % UInt32)
            end
        elseif bytes_chunk > 0x0
            b0 = l0 % UInt8
            b1 = (l0 >>> ((0x8 * div(bytes_chunk, 0x2)) % 0x3f)) % UInt8
            b2 = (l0 >>> ((0x8 * (bytes_chunk - 0x1)) % 0x3f)) % UInt8
            a = (UInt64(b0) << 45) | UInt64(b2)
            b = UInt64(b1)
        end
    else
        if bytes_chunk > 0x10
            seed = hash_mix(l0 ⊻ secret[3], l1 ⊻ seed)
            if bytes_chunk > 0x20
                seed = hash_mix(l2 ⊻ secret[3], l3 ⊻ seed)
            end
        end
        a = t0 ⊻ bytes_chunk
        b = t1
    end

    a = a ⊻ secret[2]
    b = b ⊻ seed
    b, a = mul_parts(a, b)
    return hash_mix(a ⊻ secret[4], b ⊻ secret[2] ⊻ bytes_chunk)
end
```
-/
def hashBytesIterator {State : Type} (iter : HashByteIterator State)
    (seed0 : Word) (secret : HashSecret) : Word := Id.run do
  let seed := xorWord seed0 (hashMix (xorWord seed0 secret.2.2.1) secret.2.1)
  let empty : IteratorHashState State := {
    state := iter.defaultState, seed := seed, see1 := seed, see2 := seed,
    buflen := JInt.lit .u64 0,
    l0 := JInt.lit .u64 0, l1 := JInt.lit .u64 0, l2 := JInt.lit .u64 0,
    l3 := JInt.lit .u64 0, l4 := JInt.lit .u64 0, l5 := JInt.lit .u64 0,
    b0 := 0, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0,
    t0 := JInt.lit .u64 0, t1 := JInt.lit .u64 0 }
  let s := match readUInt64First iter with
    | none => empty
    | some (l0, state, b0) =>
        let s := { empty with l0 := l0, state := state, b0 := b0.toNat }
        hashIteratorChunks iter secret s
  let bytesChunk : Nat := s.b0 + s.b1 + s.b2 + s.b3 + s.b4 + s.b5
  let mut seed := s.seed
  if decide (0 < (s.buflen.val : Int)) then
    seed := xorWord (xorWord seed s.see1) s.see2
  let buflen := s.buflen + JInt.lit .u64 bytesChunk
  let mut a : Word := JInt.lit .u64 0
  let mut b : Word := JInt.lit .u64 0
  if buflen.val ≤ 16 then
    if bytesChunk ≥ 4 then
      seed := xorWord seed (JInt.lit .u64 bytesChunk)
      if bytesChunk ≥ 8 then
        a := s.l0
        b := s.t1
      else
        a := JInt.lit .u64 (lowWord32 s.l0).val
        let shift : Nat := (8 : Nat) * (bytesChunk - 4) % (63 : Nat)
        b := JInt.lit .u64 (lowWord32 (shrWord s.l0 shift)).val
    else if bytesChunk > 0 then
      let b0 := UInt8.ofNat (s.l0.val.toNat % 256)
      let shift1 : Nat := (8 : Nat) * (bytesChunk / 2) % (63 : Nat)
      let b1 := UInt8.ofNat ((shrWord s.l0 shift1).val.toNat % 256)
      let shift2 : Nat := (8 : Nat) * (bytesChunk - 1) % (63 : Nat)
      let b2 := UInt8.ofNat ((shrWord s.l0 shift2).val.toNat % 256)
      a := shlWord (JInt.lit .u64 b0.toNat) 45 + JInt.lit .u64 b2.toNat
      b := JInt.lit .u64 b1.toNat
  else
    if bytesChunk > 16 then
      seed := hashMix (xorWord s.l0 secret.2.2.1) (xorWord s.l1 seed)
      if bytesChunk > 32 then
        seed := hashMix (xorWord s.l2 secret.2.2.1) (xorWord s.l3 seed)
    a := xorWord s.t0 (JInt.lit .u64 bytesChunk)
    b := s.t1
  a := xorWord a secret.2.1
  b := xorWord b seed
  let (high, low) := mulParts a b
  return hashMix (xorWord low secret.2.2.2)
    (xorWord (xorWord high secret.2.1) (JInt.lit .u64 bytesChunk))

def utf8ByteIterator {S State Char : Type} (ops : UTF8Iterator S State Char)
    (units : UTF8Units S) : HashByteIterator (UTF8State State) :=
  { first := iterateUTF8First ops.first ops.reinterpretUInt32 ops.bswapUInt32 units
    next := fun state => iterateUTF8State ops.next ops.reinterpretUInt32 ops.bswapUInt32 units state
    remaining := fun _ => 0
    defaultState := (ops.defaultState, JInt.lit .u32 0) }

def hashUTF8Units {S State Char : Type} (ops : UTF8Iterator S State Char)
    (units : UTF8Units S) (seed : Word) (secret : HashSecret) : Word :=
  hashBytesIterator (utf8ByteIterator ops units) seed secret

def hashBytesDispatch {S State Char : Type} (ops : UTF8Iterator S State Char)
    (units : UTF8UnitsResult HashByteArray S) (seed : Word) (secret : HashSecret) : Word :=
  match units with
  | .codeunits bytes => hashBytesArray bytes seed secret
  | .iterated chars => hashUTF8Units ops chars seed secret


/--
Julia source: base/hashing.jl:649-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(data::AbstractString, h::UInt) =
    hash_bytes(utf8units(data), UInt64(h), HASH_SECRET) % UInt
```
-/
def hashAbstractString {S State Char : Type} (ops : UTF8Iterator S State Char)
    (codeunitIsUInt8 : S → Bool) (codeunits : S → HashByteArray)
    (data : S) (h : Word) : Word :=
  hashBytesDispatch ops (utf8units codeunitIsUInt8 codeunits data) h hashSecret

/--
Julia source: base/hashing.jl:652-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :total hash(data::String, h::UInt) =
    GC.@preserve data hash_bytes(
        pointer(data), sizeof(data), UInt64(h), HASH_SECRET, Val(sizeof(Int))) % UInt
```
-/
def hashString {S Ptr : Type} (ops : HashPointerOps Ptr)
    (preserve : S → Word → Word) (pointer : S → Ptr) (sizeof : S → Nat)
    (sizeofInt : Nat) (data : S) (h : Word) : Word :=
  preserve data (hashBytesPointer ops (pointer data) (sizeof data) h hashSecret sizeofInt)

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:1-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- const HASH_SEED = UInt == UInt64 ? 0xbdd89aa982704029 : 0xeabe9406
-- const HASH_SECRET = (
--     0x2d358dccaa6c78a5,
--     0x8bb84b93962eacc9,
--     0x4b33a62ed433d4a3,
--     0xaaaaaaaaaaaaaaaa,
-- )
-- 
-- """
--     hash(x[, h::UInt])::UInt
-- 
-- Compute an integer hash code such that `isequal(x,y)` implies `isequal(hash(x), hash(y))`. The
-- optional second argument `h` is another hash code to be mixed with the result.
-- 
-- New types should implement the 2-argument form, typically by calling the 2-argument `hash`
-- method recursively in order to mix hashes of the contents with each other (and with `h`).
-- Typically, any type that implements `hash` should also implement its own [`==`](@ref) (hence
-- [`isequal`](@ref)) to guarantee the property mentioned above.
-- 
-- The hash value may change when a new Julia process is started.
-- 
-- !!! warning
--     When implementing the 2-argument form, the second argument `h` should _not_ be given a
--     default value such `h = UInt(0)` as this will implicitly create a 1-argument method that
--     is more specific than the fallback (see [Note on Optional and keyword Arguments](@ref)),
--     but potentially with the wrong seed, causing hash inconsistencies.
-- 
-- ```jldoctest; filter = r"0x[0-9a-f]{16}"
-- julia> a = hash(10)
-- 0x759d18cc5346a65f
-- 
-- julia> hash(10, a) # only use the output of another hash function as the second argument
-- 0x03158cd61b1b0bd1
-- ```
-- 
-- See also [`objectid`](@ref), [`Dict`](@ref), [`Set`](@ref).
-- """
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:42-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Types can't be deleted, so marking as total allows the compiler to look up the hash
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:53-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # faster-but-weaker than hash_mix intended for small keys
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:66-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if UInt === UInt64
--     const hash_uint64 = hash_64_64
--     const hash_uint = hash_64_64
-- else
--     const hash_uint64 = hash_64_32
--     const hash_uint = hash_32_32
-- end
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:78-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # IntegerCodeUnits provides a little-endian byte representation of integers
-- struct IntegerCodeUnits{T<:Integer} <: AbstractVector{UInt8}
--     uvalue::T
--     num_bytes::Int
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:96-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # Main interface function to get little-endian byte representation of integers
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:100-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # UTF8Units provides UTF-8 byte iteration for any AbstractString
-- struct UTF8Units{T<:AbstractString}
--     string::T
-- end
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:107-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Iterator state: (char_iter_state, remaining_utf8_bytes)
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:160-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- ## efficient value-based hashing of floats ##
-- 
-- const hx_NaN = hash(reinterpret(UInt64, NaN))
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:184-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:197-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## generic hashing for rational values ##
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:246-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- ## symbol & expression hashing ##
-- if UInt === UInt64
--     # conservatively hash using == equality of all of the data, even though == often uses === internally
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- else
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:258-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:283-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const hashgr_seed = 0xe19bede84d316c06 % UInt
-- const hashps_seed = 0xee5c84c1439961a8 % UInt
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:298-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # `A` is a known power-of-two alignment of `ptr`. Only the loads at multiples of 8 bytes from
-- # `ptr` can use it; the overlapping reads of the tail may be misaligned.
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:377-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:389-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:398-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:474-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # Helper function to concatenate two UInt64 values with a byte shift
-- # Returns the result of shifting 'low' right by 'shift_bytes' bytes and
-- # filling the high bits with the low bits of 'high'
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:483-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:494-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:648-648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: file-level constants, comments, and metadata are represented above or are not callable methods.
-- UNTRANSLATED
-- Source: base/hashing.jl:651-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # String data follows the length field of a 4-byte-aligned object
-- /Source


end JuliaLean.base.hashing
