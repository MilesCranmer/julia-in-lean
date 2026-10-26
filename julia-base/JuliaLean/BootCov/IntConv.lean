import JuliaLean.BootCov.Basic

/-!
Integer conversions defined in `Core` (`base/boot.jl:1032-1221`, master
`bbfa0ce4150`): the intrinsics `trunc_int`, `sext_int`, `zext_int`, `bitcast`,
`eq_int` and `slt_int` act on the fixed-width bit pattern of a `JInt`, and the
`toT` tables are transcribed one source line per case.
-/

namespace JuliaLean.BootCov.IntConv

open JuliaLean
open JuliaLean.BootCov

/-- A value of `BuiltinInts` (`base/boot.jl:1182`): a fixed-width integer or a `Bool`. -/
inductive BuiltinInt where
  | int (t : IntTy) (x : JInt t)
  | bool (b : Bool)

/-- The mathematical integer a `BuiltinInts` value denotes. -/
def BuiltinInt.value : BuiltinInt → Int
  | .int _ x => x.val
  | .bool b => if b then 1 else 0

/-- `bitsizeof(typeof(x))`; `Bool` occupies 8 bits. -/
def BuiltinInt.bits : BuiltinInt → Nat
  | .int t _ => t.bits
  | .bool _ => 8

/-- `trunc_int(To, x)`: keep the low `To.bits` bits. -/
def truncInt (To : IntTy) {t : IntTy} (x : JInt t) : JInt To := JInt.wrap To x.val

/-- `sext_int(To, x)`: read the pattern of `x` as signed, then widen. -/
def sextInt (To : IntTy) {t : IntTy} (x : JInt t) : JInt To :=
  JInt.wrap To (wrapInt t.toSigned x.val)

/-- `zext_int(To, x)`: read the pattern of `x` as unsigned, then widen. -/
def zextInt (To : IntTy) {t : IntTy} (x : JInt t) : JInt To :=
  JInt.wrap To (wrapInt t.toUnsigned x.val)

/-- `bitcast(To, x)` between integer types of the same width. -/
def bitcastInt (To : IntTy) {t : IntTy} (x : JInt t) : JInt To := JInt.wrap To x.val

/-- `bitcast(To, b)` / `zext_int(To, b)` of a `Bool`, whose bit pattern is `0x00` or `0x01`. -/
def boolTo (To : IntTy) (b : Bool) : JInt To := JInt.wrap To (if b then 1 else 0)

/-- `is_top_bit_set(x) = slt_int(x, xor_int(x, x))`, `base/boot.jl:1037-1042`. -/
def isTopBitSet {t : IntTy} (x : JInt t) : Bool := decide (wrapInt t.toSigned x.val < 0)

/-- `throw_inexacterror(func, To, val)`, `base/boot.jl:1045`. -/
def throwInexact {α : Type} (func : String) (To : IntTy) : R α := .error (.inexact func To.name)

/-- `check_sign_bit(To, x)`, `base/boot.jl:1047-1053`. -/
def checkSignBit (To : IntTy) {t : IntTy} (x : JInt t) : R (JInt t) :=
  -- `is_top_bit_set(x) && throw_inexacterror(...)`
  if wrapInt t.toSigned x.val < 0 then
    throwInexact (if t.bits = To.bits then "convert" else "trunc") To
  else .ok x

/-- `checked_trunc_sint(To, x)`, `base/boot.jl:1055-1061`. -/
def checkedTruncSint (To : IntTy) {t : IntTy} (x : JInt t) : R (JInt To) :=
  let y := truncInt To x
  let back := sextInt t y
  -- `eq_int(x, back) || throw_inexacterror(:trunc, To, x)`
  if x.val = back.val then .ok y else throwInexact "trunc" To

/-- `checked_trunc_uint(To, x)`, `base/boot.jl:1063-1069`. -/
def checkedTruncUint (To : IntTy) {t : IntTy} (x : JInt t) : R (JInt To) :=
  let y := truncInt To x
  let back := zextInt t y
  if x.val = back.val then .ok y else throwInexact "trunc" To

/-- `toInt8`, `base/boot.jl:1071-1081`, one case per source type. -/
def toInt8 : BuiltinInt → R (JInt .i8)
  | .int .i8 x => .ok x
  | .int .i16 x => checkedTruncSint .i8 x
  | .int .i32 x => checkedTruncSint .i8 x
  | .int .i64 x => checkedTruncSint .i8 x
  | .int .i128 x => checkedTruncSint .i8 x
  | .int .u8 x => do let x ← checkSignBit .i8 x; pure (bitcastInt .i8 x)
  | .int .u16 x => do let x ← checkSignBit .i8 x; checkedTruncSint .i8 x
  | .int .u32 x => do let x ← checkSignBit .i8 x; checkedTruncSint .i8 x
  | .int .u64 x => do let x ← checkSignBit .i8 x; checkedTruncSint .i8 x
  | .int .u128 x => do let x ← checkSignBit .i8 x; checkedTruncSint .i8 x
  | .bool b => .ok (boolTo .i8 b)  -- bitcast(Int8, x)

/-- `toInt16`, `base/boot.jl:1082-1092`, one case per source type. -/
def toInt16 : BuiltinInt → R (JInt .i16)
  | .int .i8 x => .ok (sextInt .i16 x)
  | .int .i16 x => .ok x
  | .int .i32 x => checkedTruncSint .i16 x
  | .int .i64 x => checkedTruncSint .i16 x
  | .int .i128 x => checkedTruncSint .i16 x
  | .int .u8 x => .ok (zextInt .i16 x)
  | .int .u16 x => do let x ← checkSignBit .i16 x; pure (bitcastInt .i16 x)
  | .int .u32 x => do let x ← checkSignBit .i16 x; checkedTruncSint .i16 x
  | .int .u64 x => do let x ← checkSignBit .i16 x; checkedTruncSint .i16 x
  | .int .u128 x => do let x ← checkSignBit .i16 x; checkedTruncSint .i16 x
  | .bool b => .ok (boolTo .i16 b)  -- zext_int(Int16, x)

/-- `toInt32`, `base/boot.jl:1093-1103`, one case per source type. -/
def toInt32 : BuiltinInt → R (JInt .i32)
  | .int .i8 x => .ok (sextInt .i32 x)
  | .int .i16 x => .ok (sextInt .i32 x)
  | .int .i32 x => .ok x
  | .int .i64 x => checkedTruncSint .i32 x
  | .int .i128 x => checkedTruncSint .i32 x
  | .int .u8 x => .ok (zextInt .i32 x)
  | .int .u16 x => .ok (zextInt .i32 x)
  | .int .u32 x => do let x ← checkSignBit .i32 x; pure (bitcastInt .i32 x)
  | .int .u64 x => do let x ← checkSignBit .i32 x; checkedTruncSint .i32 x
  | .int .u128 x => do let x ← checkSignBit .i32 x; checkedTruncSint .i32 x
  | .bool b => .ok (boolTo .i32 b)  -- zext_int(Int32, x)

/-- `toInt64`, `base/boot.jl:1104-1114`, one case per source type. -/
def toInt64 : BuiltinInt → R (JInt .i64)
  | .int .i8 x => .ok (sextInt .i64 x)
  | .int .i16 x => .ok (sextInt .i64 x)
  | .int .i32 x => .ok (sextInt .i64 x)
  | .int .i64 x => .ok x
  | .int .i128 x => checkedTruncSint .i64 x
  | .int .u8 x => .ok (zextInt .i64 x)
  | .int .u16 x => .ok (zextInt .i64 x)
  | .int .u32 x => .ok (zextInt .i64 x)
  | .int .u64 x => do let x ← checkSignBit .i64 x; pure (bitcastInt .i64 x)
  | .int .u128 x => do let x ← checkSignBit .i64 x; checkedTruncSint .i64 x
  | .bool b => .ok (boolTo .i64 b)  -- zext_int(Int64, x)

/-- `toInt128`, `base/boot.jl:1115-1125`, one case per source type. -/
def toInt128 : BuiltinInt → R (JInt .i128)
  | .int .i8 x => .ok (sextInt .i128 x)
  | .int .i16 x => .ok (sextInt .i128 x)
  | .int .i32 x => .ok (sextInt .i128 x)
  | .int .i64 x => .ok (sextInt .i128 x)
  | .int .i128 x => .ok x
  | .int .u8 x => .ok (zextInt .i128 x)
  | .int .u16 x => .ok (zextInt .i128 x)
  | .int .u32 x => .ok (zextInt .i128 x)
  | .int .u64 x => .ok (zextInt .i128 x)
  | .int .u128 x => do let x ← checkSignBit .i128 x; pure (bitcastInt .i128 x)
  | .bool b => .ok (boolTo .i128 b)  -- zext_int(Int128, x)

/-- `toUInt8`, `base/boot.jl:1126-1136`, one case per source type. -/
def toUInt8 : BuiltinInt → R (JInt .u8)
  | .int .i8 x => do let x ← checkSignBit .u8 x; pure (bitcastInt .u8 x)
  | .int .i16 x => checkedTruncUint .u8 x
  | .int .i32 x => checkedTruncUint .u8 x
  | .int .i64 x => checkedTruncUint .u8 x
  | .int .i128 x => checkedTruncUint .u8 x
  | .int .u8 x => .ok x
  | .int .u16 x => checkedTruncUint .u8 x
  | .int .u32 x => checkedTruncUint .u8 x
  | .int .u64 x => checkedTruncUint .u8 x
  | .int .u128 x => checkedTruncUint .u8 x
  | .bool b => .ok (boolTo .u8 b)  -- bitcast(UInt8, x)

/-- `toUInt16`, `base/boot.jl:1137-1147`, one case per source type. -/
def toUInt16 : BuiltinInt → R (JInt .u16)
  | .int .i8 x => do let x ← checkSignBit .u16 x; pure (sextInt .u16 x)
  | .int .i16 x => do let x ← checkSignBit .u16 x; pure (bitcastInt .u16 x)
  | .int .i32 x => checkedTruncUint .u16 x
  | .int .i64 x => checkedTruncUint .u16 x
  | .int .i128 x => checkedTruncUint .u16 x
  | .int .u8 x => .ok (zextInt .u16 x)
  | .int .u16 x => .ok x
  | .int .u32 x => checkedTruncUint .u16 x
  | .int .u64 x => checkedTruncUint .u16 x
  | .int .u128 x => checkedTruncUint .u16 x
  | .bool b => .ok (boolTo .u16 b)  -- zext_int(UInt16, x)

/-- `toUInt32`, `base/boot.jl:1148-1158`, one case per source type. -/
def toUInt32 : BuiltinInt → R (JInt .u32)
  | .int .i8 x => do let x ← checkSignBit .u32 x; pure (sextInt .u32 x)
  | .int .i16 x => do let x ← checkSignBit .u32 x; pure (sextInt .u32 x)
  | .int .i32 x => do let x ← checkSignBit .u32 x; pure (bitcastInt .u32 x)
  | .int .i64 x => checkedTruncUint .u32 x
  | .int .i128 x => checkedTruncUint .u32 x
  | .int .u8 x => .ok (zextInt .u32 x)
  | .int .u16 x => .ok (zextInt .u32 x)
  | .int .u32 x => .ok x
  | .int .u64 x => checkedTruncUint .u32 x
  | .int .u128 x => checkedTruncUint .u32 x
  | .bool b => .ok (boolTo .u32 b)  -- zext_int(UInt32, x)

/-- `toUInt64`, `base/boot.jl:1159-1169`, one case per source type. -/
def toUInt64 : BuiltinInt → R (JInt .u64)
  | .int .i8 x => do let x ← checkSignBit .u64 x; pure (sextInt .u64 x)
  | .int .i16 x => do let x ← checkSignBit .u64 x; pure (sextInt .u64 x)
  | .int .i32 x => do let x ← checkSignBit .u64 x; pure (sextInt .u64 x)
  | .int .i64 x => do let x ← checkSignBit .u64 x; pure (bitcastInt .u64 x)
  | .int .i128 x => checkedTruncUint .u64 x
  | .int .u8 x => .ok (zextInt .u64 x)
  | .int .u16 x => .ok (zextInt .u64 x)
  | .int .u32 x => .ok (zextInt .u64 x)
  | .int .u64 x => .ok x
  | .int .u128 x => checkedTruncUint .u64 x
  | .bool b => .ok (boolTo .u64 b)  -- zext_int(UInt64, x)

/-- `toUInt128`, `base/boot.jl:1170-1180`, one case per source type. -/
def toUInt128 : BuiltinInt → R (JInt .u128)
  | .int .i8 x => do let x ← checkSignBit .u128 x; pure (sextInt .u128 x)
  | .int .i16 x => do let x ← checkSignBit .u128 x; pure (sextInt .u128 x)
  | .int .i32 x => do let x ← checkSignBit .u128 x; pure (sextInt .u128 x)
  | .int .i64 x => do let x ← checkSignBit .u128 x; pure (sextInt .u128 x)
  | .int .i128 x => do let x ← checkSignBit .u128 x; pure (bitcastInt .u128 x)
  | .int .u8 x => .ok (zextInt .u128 x)
  | .int .u16 x => .ok (zextInt .u128 x)
  | .int .u32 x => .ok (zextInt .u128 x)
  | .int .u64 x => .ok (zextInt .u128 x)
  | .int .u128 x => .ok x
  | .bool b => .ok (boolTo .u128 b)  -- zext_int(UInt128, x)


/-- `Int8(x::BuiltinInts) = toInt8(x)::Int8` and the other nine constructors,
`base/boot.jl:1184-1193`; the typeassert always holds. -/
def ctor : (To : IntTy) → BuiltinInt → R (JInt To)
  | .i8 => toInt8 | .i16 => toInt16 | .i32 => toInt32 | .i64 => toInt64
  | .i128 => toInt128 | .u8 => toUInt8 | .u16 => toUInt16 | .u32 => toUInt32
  | .u64 => toUInt64 | .u128 => toUInt128

/-- `Signed(x::UIntN) = IntN(x)` and `Unsigned(x::IntN) = UIntN(x)`, `base/boot.jl:1206-1215`. -/
def signedOf {t : IntTy} (x : JInt t) : R (JInt t.toSigned) := ctor t.toSigned (.int t x)
def unsignedOf {t : IntTy} (x : JInt t) : R (JInt t.toUnsigned) := ctor t.toUnsigned (.int t x)

/-- `Signed(x::Union{Float16,Float32,Float64,Bool}) = Int(x)` and the `Unsigned`
analogue (`base/boot.jl:1217-1218`); `intOf`/`uintOf` is the `Int(x)`/`UInt(x)`
constructor for the source type. -/
def signedOther {α : Type} (intOf : α → R JInt64) (x : α) : R JInt64 := intOf x
def unsignedOther {α : Type} (uintOf : α → R (JInt .u64)) (x : α) : R (JInt .u64) := uintOf x

/-- `Integer(x::Integer) = x` and `Integer(x::Union{Float16,Float32,Float64}) = Int(x)`,
`base/boot.jl:1220-1221`. -/
def integerOfInteger {α : Type} (x : α) : α := x
def integerOfFloat {α : Type} (intOf : α → R JInt64) (x : α) : R JInt64 := intOf x

/-- `(::Type{T})(x::T) where {T<:Number} = x`, `base/boot.jl:1195`. -/
def sameTypeCtor {α : Type} (x : α) : α := x

/-- A pointer value: its address as a 64-bit pattern. -/
structure Ptr where
  addr : JInt .u64

/-- `Int(x::Ptr) = bitcast(Int, x)` and `UInt(x::Ptr) = bitcast(UInt, x)`, `base/boot.jl:1197-1198`. -/
def intOfPtr (p : Ptr) : JInt64 := bitcastInt .i64 p.addr
def uintOfPtr (p : Ptr) : JInt .u64 := p.addr

/-- `(PT::Type{Ptr{T}})(x::Union{Int,UInt,Ptr}=0) = bitcast(PT, x)`, `base/boot.jl:1203`. -/
def ptrOfInt (x : JInt64) : Ptr := ⟨bitcastInt .u64 x⟩
def ptrOfUInt (x : JInt .u64) : Ptr := ⟨x⟩
def ptrOfPtr (p : Ptr) : Ptr := p
def ptrDefault : Ptr := ptrOfInt (JInt.lit .i64 0)

/-- `(AS::Type{AddrSpace{Backend}})(x::UInt8) = bitcast(AS, x)`, `base/boot.jl:1204`:
an address space is its 8-bit tag. -/
def addrSpaceOf (x : JInt .u8) : JInt .u8 := bitcastInt .u8 x

end JuliaLean.BootCov.IntConv
