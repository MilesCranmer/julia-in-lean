import JuliaLean.stdlib.Base64.src.Base64
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.char
import JuliaLean.base.operators
import JuliaLean.base.parse
import JuliaLean.base.hashing
import JuliaLean.base.broadcast

/-!
# Model of `base/uuid.jl`

Typed source-mirrored methods for UUID construction, conversion, parsing, hashing, display, and
broadcasting at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. UUID payloads are `JInt .u128`.
The UTF-8 and byte iterators, hash dispatch, CRC32C implementation, string allocation and pointer
operations, and IO printing remain typed interfaces where Julia dispatches to other files or runtime
services. Parser control flow, byte packing, hexadecimal checks, and integer conversions are modeled
here.
-/

namespace JuliaLean.base.uuid

open JuliaLean

abbrev U32 := JInt .u32
abbrev U64 := JInt .u64
abbrev U128 := JInt .u128

-- UNTRANSLATED
-- Source: base/uuid.jl:1-1 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- /Source
-- Reason: the license header does not define a callable method.


/-- The selected `iterate` methods for the units consumed by `takebytes`. -/
structure UUIDByteIterator (Units State : Type) where
  first : Units → Jl (Option (UInt8 × State))
  next : Units → State → Jl (Option (UInt8 × State))

/-- Runtime operations used by `string(::UUID)` for its allocated string and byte pointer. -/
structure UUIDStringOps (S Ptr : Type) where
  newString : JInt .i64 → Jl S
  pointer : S → Jl Ptr
  unsafeStore : Ptr → UInt8 → JInt .i64 → Jl Unit
  preserve : {α : Type} → S → (Unit → Jl α) → Jl α

/--
Julia source: base/uuid.jl:3-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
Represents a Universally Unique Identifier (UUID).
Can be built from one `UInt128` (all byte values), two `UInt64`, or four `UInt32`.
Conversion from a string will check the UUID validity.
"""
struct UUID
    value::UInt128
end
```
-/
structure UUID where
  value : U128
  deriving Repr, DecidableEq
/-- `Parsers.INVALID` or a parsed UUID. -/
inductive UUIDParseResult where
  | value (uuid : UUID)
  | invalid
  deriving Repr, DecidableEq

/--
Julia source: base/uuid.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UUID(u::UUID) = u
```
-/
def uuidIdentity (u : UUID) : UUID := u

/--
Julia source: base/uuid.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UUID(u::NTuple{2, UInt64}) = UUID((UInt128(u[1]) << 64) | UInt128(u[2]))
```
-/
def uuidFromTuple2 (u : U64 × U64) : UUID :=
  ⟨JuliaLean.base.int.bor
    (JuliaLean.base.int.shl_Int (JInt.rem .u128 u.1) (JInt.lit .i64 64))
    (JInt.rem .u128 u.2)⟩

/--
Julia source: base/uuid.jl:13-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UUID(u::NTuple{4, UInt32}) = UUID((UInt128(u[1]) << 96) | (UInt128(u[2]) << 64) |
                                  (UInt128(u[3]) << 32) | UInt128(u[4]))
```
-/
def uuidFromTuple4 (u : U32 × U32 × U32 × U32) : UUID :=
  let (hh, hl, lh, ll) := u
  ⟨JuliaLean.base.int.bor
    (JuliaLean.base.int.bor
      (JuliaLean.base.int.bor
        (JuliaLean.base.int.shl_Int (JInt.rem .u128 hh) (JInt.lit .i64 96))
        (JuliaLean.base.int.shl_Int (JInt.rem .u128 hl) (JInt.lit .i64 64)))
      (JuliaLean.base.int.shl_Int (JInt.rem .u128 lh) (JInt.lit .i64 32)))
    (JInt.rem .u128 ll)⟩

/--
Julia source: base/uuid.jl:16-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{NTuple{2, UInt64}}, uuid::UUID)
    bytes = uuid.value
    hi = UInt64((bytes >> 64) & 0xffffffffffffffff)
    lo = UInt64(bytes & 0xffffffffffffffff)
    return (hi, lo)
end
```
-/
def convertUUIDToTuple2 (uuid : UUID) : U64 × U64 :=
  let bytes := uuid.value
  let mask := JInt.lit .u128 0xffffffffffffffff
  let hi := JInt.rem .u64
    (JuliaLean.base.int.band
      (JuliaLean.base.int.shr_Int bytes (JInt.lit .i64 64)) mask)
  let lo := JInt.rem .u64 (JuliaLean.base.int.band bytes mask)
  (hi, lo)

/--
Julia source: base/uuid.jl:23-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{NTuple{4, UInt32}}, uuid::UUID)
    bytes = uuid.value
    hh = UInt32((bytes >> 96) & 0xffffffff)
    hl = UInt32((bytes >> 64) & 0xffffffff)
    lh = UInt32((bytes >> 32) & 0xffffffff)
    ll = UInt32(bytes & 0xffffffff)
    return (hh, hl, lh, ll)
end
```
-/
def convertUUIDToTuple4 (uuid : UUID) : U32 × U32 × U32 × U32 :=
  let bytes := uuid.value
  let mask := JInt.lit .u128 0xffffffff
  let hh := JInt.rem .u32
    (JuliaLean.base.int.band
      (JuliaLean.base.int.shr_Int bytes (JInt.lit .i64 96)) mask)
  let hl := JInt.rem .u32
    (JuliaLean.base.int.band
      (JuliaLean.base.int.shr_Int bytes (JInt.lit .i64 64)) mask)
  let lh := JInt.rem .u32
    (JuliaLean.base.int.band
      (JuliaLean.base.int.shr_Int bytes (JInt.lit .i64 32)) mask)
  let ll := JInt.rem .u32 (JuliaLean.base.int.band bytes mask)
  (hh, hl, lh, ll)

/--
Julia source: base/uuid.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UInt128(u::UUID) = u.value
```
-/
def toUInt128 (u : UUID) : U128 := u.value

/--
Julia source: base/uuid.jl:34-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let
    uuid_hash_seed = UInt === UInt64 ? 0xd06fa04f86f11b53 : 0x96a1f36d
    Base.hash(uuid::UUID, h::UInt) = hash(uuid_hash_seed, hash(convert(NTuple{2, UInt64}, uuid), h))
end
```
-/
def hashUUID (hash : {T : Type} → T → U64 → U64) (uuid : UUID) (h : U64) : U64 :=
  let uuidHashSeed : U64 := JInt.lit .u64 0xd06fa04f86f11b53
  hash uuidHashSeed (hash (convertUUIDToTuple2 uuid) h)

/--
Julia source: base/uuid.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(uuid::UUID, crc::UInt32=0x00000000) = _crc32c(uuid.value, crc)
```
-/
def crc32cUUID (crc32c : U128 → U32 → U32) (uuid : UUID)
    (crc : U32 := JInt.lit .u32 0) : U32 :=
  crc32c uuid.value crc

/--
Julia source: base/uuid.jl:41-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The next `n` bytes of the iteration `y` of `units` in a word, the first in the lowest byte,
# the iteration after them, and whether there were `n`. `y` is `nothing` or the iteration in
# each of the two returns, so each result has a concrete type that callers can split on.
@inline function takebytes(units, y, n::Int)
    w = zero(UInt64)
    exact = @label exact begin
        for k in 0:n-1
            y === nothing && break exact false
            b, state = y
            w |= UInt64(b) << 8k
            y = iterate(units, state)
        end
        true
    end
    y === nothing && return (; w, y, exact)
    return (; w, y, exact)
end
```
-/
-- Source: base/uuid.jl:44-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def takebytes {Units State : Type} (ops : UUIDByteIterator Units State)
    (units : Units) (y : Option (UInt8 × State)) (n : JInt .i64) :
    Jl (U64 × Option (UInt8 × State) × Bool) :=
  let rec loop : Nat → JInt .i64 → U64 → Option (UInt8 × State) → Jl (U64 × Option (UInt8 × State) × Bool)
    | 0, _, w, y => pure (w, y, true)
    | _ + 1, _, w, none => pure (w, none, false)
    | remaining + 1, k, w, some (b, state) => do
        let byte := JInt.lit .u64 (Int.ofNat b.toNat)
        let shift := JuliaLean.base.int.mul (JInt.lit .i64 8) k
        let w := JuliaLean.base.int.bor w (JuliaLean.base.int.shl_Int byte shift)
        let y ← ops.next units state
        match remaining with
        | 0 => pure (w, y, true)
        | _ + 1 => loop remaining (JuliaLean.base.int.add_int k (JInt.lit .i64 1)) w y
  let stop := JuliaLean.base.int.sub n (JInt.lit .i64 1)
  let count := if stop.val < 0 then 0 else stop.val.toNat + 1
  do
    let (w, y, exact) ← loop count (JInt.lit .i64 0) (JInt.lit .u64 0) y
    match y with
    | none => pure (w, y, exact)
    | some _ => pure (w, y, exact)

/--
Julia source: base/uuid.jl:59-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The UUID spelled by the 36 bytes that `units` iterates. They are read as eight hex digits,
# four groups of a dash and four digits, and eight more digits, and the digits are checked
# and converted eight at a time.
function parseuuid(units)
    a, y, ok1 = takebytes(units, iterate(units), 8)
    b, y, ok2 = takebytes(units, y, 5)
    c, y, ok3 = takebytes(units, y, 5)
    d, y, ok4 = takebytes(units, y, 5)
    e, y, ok5 = takebytes(units, y, 5)
    f, y, ok6 = takebytes(units, y, 8)
    # returning before using the words lets the compiler merge the end checks of their bytes
    ok1 & ok2 & ok3 & ok4 & ok5 & ok6 & (y === nothing) || return Parsers.INVALID
    dashes = (b & 0xff) | (c & 0xff) << 8 | (d & 0xff) << 16 | (e & 0xff) << 24
    dashes == UInt8('-') * 0x01010101 || return Parsers.INVALID
    w2 = b >> 8 | c >> 8 << 32
    w3 = d >> 8 | e >> 8 << 32
    Parsers.ishexdigits8(a) & Parsers.ishexdigits8(w2) & Parsers.ishexdigits8(w3) &
        Parsers.ishexdigits8(f) || return Parsers.INVALID
    return UUID((Parsers.hexdigits8(a) << 32 | Parsers.hexdigits8(w2),
                 Parsers.hexdigits8(w3) << 32 | Parsers.hexdigits8(f)))
end
```
-/
def parseuuid {Units State : Type} (ops : UUIDByteIterator Units State) (units : Units) :
    Jl UUIDParseResult := do
  let first ← ops.first units
  let (a, y, ok1) ← takebytes ops units first (JInt.lit .i64 8)
  let (b, y, ok2) ← takebytes ops units y (JInt.lit .i64 5)
  let (c, y, ok3) ← takebytes ops units y (JInt.lit .i64 5)
  let (d, y, ok4) ← takebytes ops units y (JInt.lit .i64 5)
  let (e, y, ok5) ← takebytes ops units y (JInt.lit .i64 5)
  let (f, y, ok6) ← takebytes ops units y (JInt.lit .i64 8)
  let atEnd := match y with
    | none => true
    | some _ => false
  if !(ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && atEnd) then return .invalid
  let mask := JInt.lit .u64 0xff
  let dashes := JuliaLean.base.int.bor
    (JuliaLean.base.int.bor
      (JuliaLean.base.int.bor
        (JuliaLean.base.int.band b mask)
        (JuliaLean.base.int.shl_Int (JuliaLean.base.int.band c mask) (JInt.lit .i64 8)))
      (JuliaLean.base.int.shl_Int (JuliaLean.base.int.band d mask) (JInt.lit .i64 16)))
    (JuliaLean.base.int.shl_Int (JuliaLean.base.int.band e mask) (JInt.lit .i64 24))
  if dashes != JInt.lit .u64 0x2d2d2d2d then return .invalid
  let w2 := JuliaLean.base.int.bor
    (JuliaLean.base.int.shr_Int b (JInt.lit .i64 8))
    (JuliaLean.base.int.shl_Int
      (JuliaLean.base.int.shr_Int c (JInt.lit .i64 8)) (JInt.lit .i64 32))
  let w3 := JuliaLean.base.int.bor
    (JuliaLean.base.int.shr_Int d (JInt.lit .i64 8))
    (JuliaLean.base.int.shl_Int
      (JuliaLean.base.int.shr_Int e (JInt.lit .i64 8)) (JInt.lit .i64 32))
  if !(JuliaLean.ParsePrint.IntParse.ishexdigits8 a &&
      JuliaLean.ParsePrint.IntParse.ishexdigits8 w2 &&
      JuliaLean.ParsePrint.IntParse.ishexdigits8 w3 &&
      JuliaLean.ParsePrint.IntParse.ishexdigits8 f) then return .invalid
  let hi := JuliaLean.base.int.bor
    (JuliaLean.base.int.shl_Int (JuliaLean.ParsePrint.IntParse.hexdigits8 a) (JInt.lit .i64 32))
    (JuliaLean.ParsePrint.IntParse.hexdigits8 w2)
  let lo := JuliaLean.base.int.bor
    (JuliaLean.base.int.shl_Int (JuliaLean.ParsePrint.IntParse.hexdigits8 w3) (JInt.lit .i64 32))
    (JuliaLean.ParsePrint.IntParse.hexdigits8 f)
  pure (.value (uuidFromTuple2 (hi, lo)))

/--
Julia source: base/uuid.jl:81-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Parsers.parsevalue(::Type{UUID}, bytes::AbstractVector{UInt8}) = parseuuid(bytes)
```
-/
def parsevalueUUID {Bytes State : Type} (ops : UUIDByteIterator Bytes State) (bytes : Bytes) :
    Jl UUIDParseResult :=
  parseuuid ops bytes

/--
Julia source: base/uuid.jl:83-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tryparse(::Type{UUID}, s::AbstractString)
    u = parseuuid(utf8units(s))
    return u isa UUID ? u : nothing
end
```
-/
def tryparseUUID {S A State : Type} (codeunitIsUInt8 : S → Bool) (codeunits : S → A)
    (ops : UUIDByteIterator (JuliaLean.base.hashing.UTF8UnitsResult A S) State) (s : S) :
    Jl (Option UUID) := do
  let units := JuliaLean.base.hashing.utf8units codeunitIsUInt8 codeunits s
  match ← parseuuid ops units with
  | .value uuid => pure (some uuid)
  | .invalid => pure none

/--
Julia source: base/uuid.jl:88-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let
    @noinline throw_malformed_uuid(s) = throw(ArgumentError("Malformed UUID string: $(repr(s))"))
```
-/
def throwMalformedUUID {S α : Type} (repr : S → String) (s : S) : Jl α :=
  .error (.argumentError ("Malformed UUID string: " ++ repr s))

/--
Julia source: base/uuid.jl:90-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Base.parse(::Type{UUID}, s::AbstractString)
        uuid = tryparse(UUID, s)
        return uuid === nothing ? throw_malformed_uuid(s) : uuid
    end
```
-/
def parseUUID {S A State : Type} (codeunitIsUInt8 : S → Bool) (codeunits : S → A)
    (ops : UUIDByteIterator (JuliaLean.base.hashing.UTF8UnitsResult A S) State)
    (repr : S → String) (s : S) : Jl UUID := do
  let uuid ← tryparseUUID codeunitIsUInt8 codeunits ops s
  match uuid with
  | some uuid => pure uuid
  | none => throwMalformedUUID repr s

/--
Julia source: base/uuid.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UUID(s::AbstractString) = parse(UUID, s)
```
-/
def uuidFromString {S A State : Type} (codeunitIsUInt8 : S → Bool) (codeunits : S → A)
    (ops : UUIDByteIterator (JuliaLean.base.hashing.UTF8UnitsResult A S) State)
    (repr : S → String) (s : S) : Jl UUID :=
  parseUUID codeunitIsUInt8 codeunits ops repr s

/--
Julia source: base/uuid.jl:98-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let groupings = [36:-1:25; 23:-1:20; 18:-1:15; 13:-1:10; 8:-1:1]
    global string
    function string(u::UUID)
        u = u.value
        str = Base._string_n(36)
        GC.@preserve str begin
            p = pointer(str)
            for i in groupings
                unsafe_store!(p, @inbounds(hex_chars[1 + u & 0xf]), i)
                u >>= 4
            end
            unsafe_store!(p, UInt8('-'), 9)
            unsafe_store!(p, UInt8('-'), 14)
            unsafe_store!(p, UInt8('-'), 19)
            unsafe_store!(p, UInt8('-'), 24)
        end
        return str
    end
end
```
-/
def stringUUID {S Ptr : Type} (ops : UUIDStringOps S Ptr) (u : UUID) : Jl S := do
  let str ← ops.newString (JInt.lit .i64 36)
  let groupings :=
    (List.range 12).map (fun k => 36 - k) ++
    (List.range 4).map (fun k => 23 - k) ++
    (List.range 4).map (fun k => 18 - k) ++
    (List.range 4).map (fun k => 13 - k) ++
    (List.range 8).map (fun k => 8 - k)
  let write : Unit → Jl Unit := fun _ => do
    let p ← ops.pointer str
    let rec storeDigits : List Nat → U128 → Jl Unit
      | [], _ => pure ()
      | i :: rest, value => do
          let digit := JuliaLean.base.int.band value (JInt.lit .u128 0xf)
          let byte := JuliaLean.base.char.hex_chars.getD digit.val.toNat (UInt8.ofNat 0)
          ops.unsafeStore p byte (JInt.lit .i64 (Int.ofNat i))
          storeDigits rest (JuliaLean.base.int.shr_Int value (JInt.lit .i64 4))
    storeDigits groupings u.value
    ops.unsafeStore p (UInt8.ofNat 45) (JInt.lit .i64 9)
    ops.unsafeStore p (UInt8.ofNat 45) (JInt.lit .i64 14)
    ops.unsafeStore p (UInt8.ofNat 45) (JInt.lit .i64 19)
    ops.unsafeStore p (UInt8.ofNat 45) (JInt.lit .i64 24)
  let _ ← ops.preserve str write
  pure str

/--
Julia source: base/uuid.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, u::UUID) = print(io, string(u))
```
-/
def printUUID {IO S : Type} (string : UUID → Jl S) (print : IO → S → Jl Unit)
    (io : IO) (u : UUID) : Jl Unit := do
  print io (← string u)

/--
Julia source: base/uuid.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, u::UUID) = print(io, UUID, "(\"", u, "\")")
```
-/
def showUUID {IO TypeToken : Type}
    (print : IO → TypeToken → String → UUID → String → Jl Unit)
    (uuidType : TypeToken) (io : IO) (u : UUID) : Jl Unit :=
  print io uuidType "(\"" u "\")"

/--
Julia source: base/uuid.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(a::UUID, b::UUID) = isless(a.value, b.value)
```
-/
def islessUUID (a b : UUID) : Bool :=
  JuliaLean.base.operators.islessReal JuliaLean.base.int.lt_BitUnsigned a.value b.value

/--
Julia source: base/uuid.jl:123-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# give UUID scalar behavior in broadcasting
Base.broadcastable(x::UUID) = Ref(x)
```
-/
def broadcastableUUID (x : UUID) : JuliaLean.base.broadcast.Material.RefValue UUID :=
  ⟨x⟩

end JuliaLean.base.uuid

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

abbrev U128 := JInt .u128
abbrev U64 := JInt .u64

/-- `struct UUID; value::UInt128; end`, `base/uuid.jl:8-10`. -/
structure UUID where
  value : U128
  deriving Repr, DecidableEq

/-- `UUID(u::NTuple{2, UInt64})`, `base/uuid.jl:12`. -/
def UUID.ofPair (hi lo : U64) : UUID :=
  ⟨bor (shl (JInt.rem .u128 hi) 64) (JInt.rem .u128 lo)⟩


/-- `groupings = [36:-1:25; 23:-1:20; 18:-1:15; 13:-1:10; 8:-1:1]`, `base/uuid.jl:98`. -/
def groupings : List Nat :=
  (List.range 12).map (36 - ·) ++ (List.range 4).map (23 - ·) ++ (List.range 4).map (18 - ·) ++
    (List.range 4).map (13 - ·) ++ (List.range 8).map (8 - ·)

/-- `string(u::UUID)`, `base/uuid.jl:100-115`: a 36-byte string, filled from the last
hex digit backwards, then the four dashes. The initial contents of the fresh string
are never read (every position is stored), and are modelled as zeros. -/
def uuidString (u : UUID) : List Byte :=
  let (a, _) := groupings.foldl
    (fun (acc : List Byte × U128) (i : Nat) =>
      let (a, v) := acc
      (a.set (i - 1) (hex_chars.getD (bn (JInt.rem .u8 (band v (JInt.lit .u128 0xf)))) (b8 0)), shr v 4))
    (List.replicate 36 (b8 0), u.value)
  ((((a.set 8 (b8 45)).set 13 (b8 45)).set 18 (b8 45)).set 23 (b8 45))

/-- `takebytes(units, y, n)`, `base/uuid.jl:44-57`: the next `n` bytes as a
little-endian `UInt64` (first byte lowest), the remaining iteration, and whether there
were `n`. `units` is the not-yet-iterated rest of the code units. -/
def takebytes (units : List Byte) (n : Nat) : U64 × List Byte × Bool :=
  let rec go : Nat → Nat → U64 → List Byte → U64 × List Byte × Bool
    | 0, _, w, y => (w, y, true)
    | _ + 1, _, w, [] => (w, [], false)
    | m + 1, k, w, b :: y => go m (k + 1) (bor w (shl (JInt.rem .u64 b) (8 * k))) y
  go n 0 (JInt.lit .u64 0) units

/-- `parseuuid(units)`, `base/uuid.jl:62-79`; `none` is `Parsers.INVALID`. -/
def parseuuid (units : List Byte) : Option UUID :=
  let (a, y, ok1) := takebytes units 8
  let (b, y, ok2) := takebytes y 5
  let (c, y, ok3) := takebytes y 5
  let (d, y, ok4) := takebytes y 5
  let (e, y, ok5) := takebytes y 5
  let (f, y, ok6) := takebytes y 8
  if !(ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && y.isEmpty) then none else
  let m := JInt.lit .u64 0xff
  let dashes := bor (bor (bor (band b m) (shl (band c m) 8)) (shl (band d m) 16)) (shl (band e m) 24)
  if dashes != JInt.lit .u64 (45 * 0x01010101) then none else
  let w2 := bor (shr b 8) (shl (shr c 8) 32)
  let w3 := bor (shr d 8) (shl (shr e 8) 32)
  if !(IntParse.ishexdigits8 a && IntParse.ishexdigits8 w2 && IntParse.ishexdigits8 w3 &&
      IntParse.ishexdigits8 f) then none else
  some (UUID.ofPair (bor (shl (IntParse.hexdigits8 a) 32) (IntParse.hexdigits8 w2))
    (bor (shl (IntParse.hexdigits8 w3) 32) (IntParse.hexdigits8 f)))

/-- `tryparse(UUID, s)`, `base/uuid.jl:83-86`; `s` is given by its UTF-8 code units. -/
def tryparseUUID (s : List Byte) : Option UUID := parseuuid s

/-- `UUID(s)` = `parse(UUID, s)`, `base/uuid.jl:88-96`. -/
def parseUUID (s : List Byte) : Jle UUID :=
  match tryparseUUID s with
  | some u => .ok u
  | none => .error (argErr "Malformed UUID string")

end JuliaLean.Base64Uuid

namespace JuliaLean.IntFuncsCov.UuidPkgid

open JuliaLean
open JuliaLean.Base64Uuid
open JuliaLean.ParsePrint


def uuidOfPair (hi lo : JInt .u64) : UUID :=
  ⟨JInt.lit .u128 (hi.val * 2 ^ 64 + lo.val)⟩

def uuidOfFour (a b c d : JInt .u32) : UUID :=
  ⟨JInt.lit .u128 (a.val * 2 ^ 96 + b.val * 2 ^ 64 + c.val * 2 ^ 32 + d.val)⟩

def uuidToPair (u : UUID) : JInt .u64 × JInt .u64 :=
  (JInt.lit .u64 (u.value.val / 2 ^ 64), JInt.lit .u64 u.value.val)

def uuidToFour (u : UUID) : JInt .u32 × JInt .u32 × JInt .u32 × JInt .u32 :=
  (JInt.lit .u32 (u.value.val / 2 ^ 96), JInt.lit .u32 (u.value.val / 2 ^ 64),
    JInt.lit .u32 (u.value.val / 2 ^ 32), JInt.lit .u32 u.value.val)

end JuliaLean.IntFuncsCov.UuidPkgid
