import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.expr

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- `Intrinsics.ule_int(typemax_Int, x)`: `x` is negative or `typemax(Int)`. -/
def uleTypemax (x : JInt64) : Bool := decide (x.val < 0 ∨ x.val = IntTy.max .i64)

/-- `Intrinsics.checked_smul_int(a, b)`: the wrapped product and whether it overflowed. -/
def checkedSmul (a b : JInt64) : JInt64 × Bool :=
  (a * b, decide ¬ (IntTy.min .i64 ≤ a.val * b.val ∧ a.val * b.val ≤ IntTy.max .i64))

/-- The loop of `_checked_mul_dims(m, d...)`, `base/boot.jl:798-807`, over the remaining `d`
with accumulator `a` and flags `ovflw`, `neg`, `zero`. -/
def checkedMulDimsLoop : List JInt64 → JInt64 → Bool → Bool → Bool → JInt64 × Bool
  | [], a, ovflw, neg, zero => (a, neg || (ovflw && !zero))
  | di :: d, a, ovflw, neg, zero =>
    let b := checkedSmul a di
    checkedMulDimsLoop d b.1 (ovflw || b.2) (neg || uleTypemax di) (zero || decide (di.val = 0))

/-- `_checked_mul_dims`, `base/boot.jl:782-808` (methods for zero, one, two and more dimensions). -/
def checkedMulDims : List JInt64 → JInt64 × Bool
  | [] => (JInt.lit .i64 1, false)
  | [m] => (m, uleTypemax m)
  | [m, n] => let b := checkedSmul m n; (b.1, b.2 || uleTypemax m || uleTypemax n)
  | m :: d => checkedMulDimsLoop d m false (uleTypemax m) false

/-- `Core.checked_dims(d::Int...)`, `base/boot.jl:811-818`. -/
def checkedDims : List JInt64 → Jl JInt64
  | [] => .ok (JInt.lit .i64 1)
  | [m] => .ok m
  | d => let b := checkedMulDims d
    if b.2 then .error (.argumentError "invalid Array dimensions") else .ok b.1

end JuliaLean.ReinterpretArrays


section

/-!
Shared model for `base/boot.jl` and `base/essentials.jl` at Julia master
`bbfa0ce4150`.

* `Exc` is the exception a modelled method throws; `R α = Except Exc α`.
* `JType` is a Julia type object: a `DataType` with its type name and
  parameters, a `Union`, `Union{}`, a `TypeVar` (identified by `id`), a
  `UnionAll`, a `Vararg`, a `TypeApp`, or a non-type type parameter.
* `JVal` is a Julia value: the scalar and syntax values these files build
  (symbols, strings, `Expr`, `QuoteNode`, `LineNumberNode`, `GlobalRef`),
  tuples, type objects, and struct instances `obj ty fields` whose undefined
  fields (`#undef`) are `none`.
-/

namespace JuliaLean.BootCov

open JuliaLean

/-- Exceptions thrown by the modelled methods. -/
inductive Exc where
  /-- `InexactError(func, To, val)`; `to` is the target type name. -/
  | inexact (func : String) (to : String)
  | argument (msg : String)
  | bounds
  /-- `TypeError(func, ...)` from a typeassert or a `new` field check. -/
  | typeError (func : String)
  | typeName
  | method (fn : String)
  | undefRef
  /-- `ErrorException(msg)`, i.e. `error(msg)`. -/
  | error (msg : String)
  deriving Repr, DecidableEq

abbrev R (α : Type) := Except Exc α

/-- Julia type objects. -/
inductive JType where
  /-- A `DataType`: type name, whether it is abstract, parameters. -/
  | dt (name : String) (abstract : Bool) (params : List JType)
  | union (a b : JType)
  | bottom
  /-- `TypeVar(name, lb, ub)`; `id` is the object identity. -/
  | tvar (id : Nat) (name : String) (lb ub : JType)
  /-- `UnionAll(var, body)`; `var` is a `tvar`. -/
  | unionAll (var : JType) (body : JType)
  /-- `Vararg{T, N}` with either parameter possibly absent. -/
  | vararg (T : Option JType) (N : Option JType)
  /-- `Core.TypeApp(head, param)`. -/
  | typeApp (head param : JType)
  /-- An `Int` used as a type parameter (e.g. a `Vararg` length). -/
  | intParam (n : Int)
  /-- A tuple of symbols used as a type parameter, e.g. `NamedTuple` names. -/
  | names (syms : List String)
  /-- Any other non-type parameter. -/
  | other (tag : String)
  deriving Repr, Inhabited

/-- Julia values. -/
inductive JVal where
  | nothing
  | bool (b : Bool)
  | int (n : Int)
  | uint8 (n : Nat)
  | sym (s : String)
  | str (s : String)
  | char (c : Char)
  | tuple (xs : List JVal)
  | expr (head : String) (args : List JVal)
  | quoteNode (v : JVal)
  | lineNode (line : Int) (file : JVal)
  | globalRef (mod name : String)
  | module_ (name : String)
  | ty (t : JType)
  /-- A struct instance; `none` is an undefined field. -/
  | obj (ty : String) (fields : List (Option JVal))
  /-- Any other object, compared by identity. -/
  | opaque (id : Nat)
  deriving Repr, Inhabited

/-- `getfield(x, i)` of a struct instance: `UndefRefError` for `#undef`. -/
def getfieldObj : JVal → Nat → R JVal
  | .obj _ fs, i =>
    match fs[i - 1]? with
    | some (some v) => .ok v
    | some none => .error .undefRef
    | none => .error .bounds
  | _, _ => .error .bounds

/-- `isdefined(x, i)` of a struct instance. -/
def isdefinedObj : JVal → Nat → Bool
  | .obj _ fs, i => match fs[i - 1]? with | some (some _) => true | _ => false
  | _, _ => false

/-- `Expr(head, args...)` value. -/
def mkExpr (head : String) (args : List JVal) : JVal := .expr head args

/-- `esc(e) = Expr(:escape, e)` (`base/essentials.jl:893`). -/
def esc (e : JVal) : JVal := .expr "escape" [e]

end JuliaLean.BootCov

end

section

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

end

section

/-!
Struct constructors defined in `Core` (`base/boot.jl`, master `bbfa0ce4150`):
exception types, inference lattice elements, IR nodes and small wrappers.
A constructor builds `obj ty fields`; `none` is a field `new` left undefined.
`new(...)` in an inner constructor converts each argument to its declared field
type (`convert` throws `MethodError` when no conversion exists), while
`Expr(:new, ...)` checks the field type without converting (`TypeError`).
-/

namespace JuliaLean.BootCov.Objects

open JuliaLean
open JuliaLean.BootCov

/-- `convert(AbstractString, x)` for a field declared `AbstractString`. -/
def toAbstractString : JVal → R JVal
  | .str s => .ok (.str s)
  | _ => .error (.method "convert")

/-- `convert(Symbol, x)` for a field declared `Symbol`. -/
def toSymbol : JVal → R JVal
  | .sym s => .ok (.sym s)
  | _ => .error (.method "convert")

/-- `convert(Union{AbstractString,GlobalRef,Symbol}, x)`. -/
def toContext : JVal → R JVal
  | .str s => .ok (.str s)
  | .globalRef m n => .ok (.globalRef m n)
  | .sym s => .ok (.sym s)
  | _ => .error (.method "convert")

/-- `Symbol(x)` for any value, through `string(x)` (`base/strings/basic.jl`);
`str` renders other values. -/
def symbolOf (str : JVal → String) : JVal → JVal
  | .sym s => .sym s
  | .str s => .sym s
  | v => .sym (str v)

/-! ## Exceptions, `base/boot.jl:470-606` -/

/-- `ErrorException(msg::AbstractString) = new(msg)`, line 472. -/
def errorException (msg : String) : JVal := .obj "ErrorException" [some (.str msg)]
/-- `BoundsError()`, `BoundsError(a)`, `BoundsError(a, i)`, lines 478-480. -/
def boundsError0 : JVal := .obj "BoundsError" [none, none]
def boundsError1 (a : JVal) : JVal := .obj "BoundsError" [some a, none]
def boundsError2 (a i : JVal) : JVal := .obj "BoundsError" [some a, some i]
/-- The field-less exceptions and singletons: `T() = new()`, lines 483-498, 516,
603, 606, 696, 757, 974, 977. -/
def fieldless (name : String) : JVal := .obj name []
/-- `UndefVarError(var)` and `UndefVarError(var, scope)`, lines 504-505; `world` is
`jl_get_tls_world_age()`. -/
def undefVarError1 (world : Nat) (var : String) : JVal :=
  .obj "UndefVarError" [some (.sym var), some (.int world), none]
def undefVarError2 (world : Nat) (var : String) (scope : JVal) : JVal :=
  .obj "UndefVarError" [some (.sym var), some (.int world), some scope]
/-- `ConcurrencyViolationError(msg) = new(msg)`, line 509. -/
def concurrencyViolationError (msg : String) : JVal := .obj "ConcurrencyViolationError" [some (.str msg)]
/-- `MissingCodeError(mi) = new(mi)`, line 513. -/
def missingCodeError (mi : JVal) : JVal := .obj "MissingCodeError" [some mi]
/-- `DomainError(val) = new(val, "")` and `DomainError(val, msg) = new(val, msg)`, lines 521-522. -/
def domainError1 (val : JVal) : JVal := .obj "DomainError" [some val, some (.str "")]
def domainError2 (val msg : JVal) : R JVal := do
  let m ← toAbstractString msg
  pure (.obj "DomainError" [some val, some m])
/-- `TypeError(func, context, expected, got) = new(func, context, expected, got)`, lines 534-535. -/
def typeError4 (func context expected got : JVal) : R JVal := do
  let f ← toSymbol func
  let c ← toContext context
  pure (.obj "TypeError" [some f, some c, some expected, some got])
/-- `TypeError(where, expected, got) = TypeError(Symbol(where), "", expected, got)`, lines 537-538. -/
def typeError3 (str : JVal → String) (where_ expected got : JVal) : R JVal :=
  typeError4 (symbolOf str where_) (.str "") expected got
/-- `InexactError(f::Symbol, args...) = new(f, args)`, line 542. -/
def inexactError (f : String) (args : List JVal) : JVal :=
  .obj "InexactError" [some (.sym f), some (.tuple args)]
/-- `OverflowError`, `ArgumentError` (`new(msg)`), lines 546, 551. -/
def overflowError (msg : String) : JVal := .obj "OverflowError" [some (.str msg)]
def argumentError (msg : String) : JVal := .obj "ArgumentError" [some (.str msg)]
/-- `UndefKeywordError(var::Symbol) = new(var)`, line 555. -/
def undefKeywordError (var : String) : JVal := .obj "UndefKeywordError" [some (.sym var)]
/-- `typemax_UInt`, line 557. -/
def typemaxUInt : Nat := 2 ^ 64 - 1
/-- `MethodError(f, args, world) = new(f, args, world)` and
`MethodError(f, args) = MethodError(f, args, typemax_UInt)`, lines 565-567. -/
def methodError3 (f args : JVal) (world : Nat) : JVal :=
  .obj "MethodError" [some f, some args, some (.int world)]
def methodError2 (f args : JVal) : JVal := methodError3 f args typemaxUInt
/-- `AssertionError(msg) = new(msg)` and `AssertionError() = AssertionError("")`, lines 571-573. -/
def assertionError1 (msg : String) : JVal := .obj "AssertionError" [some (.str msg)]
def assertionError0 : JVal := assertionError1 ""
/-- `FieldError(type, field) = new(type, field)`, line 578. -/
def fieldError (type : JVal) (field : String) : JVal := .obj "FieldError" [some type, some (.sym field)]
/-- `LoadError(file, line, error)` and `InitError(mod, error)`, lines 587, 593. -/
def loadError (file : String) (line : Int) (err : JVal) : JVal :=
  .obj "LoadError" [some (.str file), some (.int line), some err]
def initError (mod : String) (err : JVal) : JVal := .obj "InitError" [some (.sym mod), some err]
/-- `ABIOverride(abi, def) = new(abi, def)`, line 599. -/
def abiOverride (abi def_ : JVal) : JVal := .obj "ABIOverride" [some abi, some def_]
/-- `TypeNameError(a) = new(a)`, line 1307. -/
def typeNameError (a : JVal) : JVal := .obj "TypeNameError" [some a]

/-! ## Small wrappers, `base/boot.jl:611-696`, 1012, 1269-1273, 1335 -/

/-- `String(s::String) = s` and `Nothing() = nothing`, lines 611, 614. -/
def stringOfString (s : String) : String := s
def nothingCtor : JVal := .nothing
/-- `EvalInto(m) = new(m)`, line 624. -/
def evalInto (m : String) : JVal := .obj "EvalInto" [some (.module_ m)]
/-- `Box(x) = new(x)` and `Box() = new()`, lines 630-631. -/
def box1 (x : JVal) : JVal := .obj "Box" [some x]
def box0 : JVal := .obj "Box" [none]
/-- `WeakRef(v)` (`jl_gc_new_weakref_th`) and `WeakRef() = WeakRef(nothing)`, lines 638-640:
a fresh weak reference whose value is `v` until `v` is collected. -/
def weakRef1 (v : JVal) : JVal := .obj "WeakRef" [some v]
def weakRef0 : JVal := weakRef1 .nothing
/-- `Tuple{}() = ()`, line 643. -/
def emptyTuple : JVal := .tuple []
/-- `VecElement{T}(value::T) = new(value)` and `VecElement(arg::T) = VecElement{T}(arg)`,
lines 647-649. -/
def vecElementT (value : JVal) : JVal := .obj "VecElement" [some value]
def vecElement (arg : JVal) : JVal := vecElementT arg
/-- Inference lattice elements, lines 654-696: `new` of the arguments. -/
def const_ (v : JVal) : JVal := .obj "Const" [some v]
def partialStruct (typ undefs fields : JVal) : JVal := .obj "PartialStruct" [some typ, some undefs, some fields]
def interConditional (slot : Int) (thentype elsetype : JVal) : JVal :=
  .obj "InterConditional" [some (.int slot), some thentype, some elsetype]
def interMustAlias (slot : Int) (vartyp : JVal) (fldidx : Int) (fldtyp : JVal) : JVal :=
  .obj "InterMustAlias" [some (.int slot), some vartyp, some (.int fldidx), some fldtyp]
def partialOpaque (typ env parent source : JVal) : JVal :=
  .obj "PartialOpaque" [some typ, some env, some parent, some source]
def partialTask (fetchType : JVal) : JVal := .obj "PartialTask" [some fetchType]
/-- `GeneratedFunctionStub(gen, argnames, spnames) = new(...)`, line 1012. -/
def generatedFunctionStub (gen argnames spnames : JVal) : JVal :=
  .obj "GeneratedFunctionStub" [some gen, some argnames, some spnames]
/-- `MacroSource(lno, syntax_ver) = new(lno, syntax_ver)`, line 1335. -/
def macroSource (lno ver : JVal) : JVal := .obj "MacroSource" [some lno, some ver]

/-! ## IR nodes, `base/boot.jl:699-736` and 1292-1293 -/

def gotoNode (label : Int) : JVal := .obj "GotoNode" [some (.int label)]
def newvarNode (slot : JVal) : JVal := .obj "NewvarNode" [some slot]
def quoteNode (v : JVal) : JVal := .quoteNode v
def ssaValue (id : Int) : JVal := .obj "SSAValue" [some (.int id)]
def argument (n : Int) : JVal := .obj "Argument" [some (.int n)]
def returnNode1 (val : JVal) : JVal := .obj "ReturnNode" [some val]
def returnNode0 : JVal := .obj "ReturnNode" [none]
def gotoIfNot (cond : JVal) (dest : Int) : JVal := .obj "GotoIfNot" [some cond, some (.int dest)]
def enterNode1 (dest : Int) : JVal := .obj "EnterNode" [some (.int dest), none]
def enterNode2 (dest : Int) (scope : JVal) : JVal := .obj "EnterNode" [some (.int dest), some scope]
/-- `LineNumberNode(l) = new(l, nothing)`, line 710. -/
def lineNumberNode1 (l : Int) : JVal := .lineNode l .nothing
/-- `LineNumberNode(l, f)`, lines 711-714: a `String` file becomes a `Symbol`; `Expr(:new)`
then checks the field type `Union{Nothing,Symbol}`. -/
def lineNumberNode2 (l : Int) (f : JVal) : R JVal :=
  let f := match f with | .str s => JVal.sym s | v => v
  match f with
  | .nothing => .ok (.lineNode l .nothing)
  | .sym s => .ok (.lineNode l (.sym s))
  | _ => .error (.typeError "new")
def debugInfo4 (def_ linetable edges codelocs : JVal) : JVal :=
  .obj "DebugInfo" [some def_, some linetable, some edges, some codelocs]
/-- `DebugInfo(def) = new(def, nothing, svec(), "")`, lines 717-718. -/
def debugInfo1 (def_ : JVal) : JVal := debugInfo4 def_ .nothing (.tuple []) (.str "")
def slotNumber (n : Int) : JVal := .obj "SlotNumber" [some (.int n)]
def phiNode (edges values : JVal) : JVal := .obj "PhiNode" [some edges, some values]
def piNode (val typ : JVal) : JVal := .obj "PiNode" [some val, some typ]
def phiCNode (values : JVal) : JVal := .obj "PhiCNode" [some values]
def upsilonNode1 (val : JVal) : JVal := .obj "UpsilonNode" [some val]
def upsilonNode0 : JVal := .obj "UpsilonNode" [none]
def methodMatch (specTypes sparams method : JVal) (fullyCovers : Bool) : JVal :=
  .obj "MethodMatch" [some specTypes, some sparams, some method, some (.bool fullyCovers)]
def lineInfoNode (mod method file : JVal) (line inlinedAt : Int) : JVal :=
  .obj "LineInfoNode" [some mod, some method, some file, some (.int line), some (.int inlinedAt)]
/-- `EnterNode(old, new_dest)`, lines 1292-1293: keep the old scope if it is defined. -/
def enterNodeRetarget (old : JVal) (newDest : Int) : R JVal :=
  if isdefinedObj old 2 then do
    let s ← getfieldObj old 2
    pure (enterNode2 newDest s)
  else pure (enterNode1 newDest)

/-! ## Pairs, `base/boot.jl:1268-1274` -/

/-- `Pair(a, b) = new{typeof(a), typeof(b)}(a, b)`. -/
def pair (a b : JVal) : JVal := .obj "Pair" [some a, some b]
/-- The `Pair{A, B}(a, b)` method Julia actually runs: `base/Base.jl:9-13` deletes the
`Core` method of `base/boot.jl:1270-1273` and installs one that converts each argument that
is not already of its field type (`convA`, `convB` are `convert(A, _)`, `convert(B, _)`). -/
def pairAB (convA convB : JVal → R JVal) (a b : JVal) : R JVal := do
  let a ← convA a
  let b ← convB b
  pure (.obj "Pair" [some a, some b])

/-! ## Named tuples, `base/boot.jl:1022-1030` -/

/-- `NamedTuple{names}(args::Tuple)`: `Expr(:splatnew, NamedTuple{names,typeof(args)}, args)`;
building the type fails unless there is one name per element. -/
def namedTupleNames (names : List String) (args : List JVal) : R (List (String × JVal)) :=
  if names.length = args.length then .ok (names.zip args)
  else .error (.error "NamedTuple names and field types must have matching lengths")
/-- `(NT::Type{NamedTuple{names,T}})(args::T)`: the type already matches the arguments. -/
def namedTupleNT (names : List String) (args : List JVal) (_ : names.length = args.length) :
    List (String × JVal) := names.zip args
/-- `NamedTuple() = NamedTuple{(),Tuple{}}(())`. -/
def namedTupleEmpty : List (String × JVal) := namedTupleNT [] [] rfl

/-! ## Handles built by C calls, `base/boot.jl:617-626`, 740-751 -/

/-- `GlobalRef(m, s)` (`jl_module_globalref`), line 750. -/
def globalRef (m s : String) : JVal := .globalRef m s
/-- `Module(name=:anonymous, std_imports=true, default_names=true)` (`jl_f_new_module`),
line 751: a fresh module `id` with that name. -/
structure NewModule where
  name : String
  stdImports : Bool
  defaultNames : Bool
  deriving Repr, DecidableEq
def moduleCtor (name : String := "anonymous") (stdImports : Bool := true)
    (defaultNames : Bool := true) : NewModule := ⟨name, stdImports, defaultNames⟩
/-- `CodeInstance(mi, owner, ...)` (`jl_new_codeinst`), lines 740-749: the runtime builds the
instance from the thirteen arguments, in order. -/
def codeInstance (newCodeinst : List JVal → JVal) (args : List JVal) : JVal := newCodeinst args
/-- `getptls() = ccall(:jl_get_ptls_states, ...)`, line 617: the current thread's state pointer. -/
def getptls (ptls : Nat) : Nat := ptls
/-- `include(m, fname)` (`jl_load_`) and `eval(m, e)` (`jl_toplevel_eval_in`), lines 619-620,
and `(this::EvalInto)(e) = eval(this.m, e)`, line 626. -/
def include_ (load : String → String → R JVal) (m fname : String) : R JVal := load m fname
def eval_ (toplevel : String → JVal → R JVal) (m : String) (e : JVal) : R JVal := toplevel m e
def evalIntoCall (toplevel : String → JVal → R JVal) (this : JVal) (e : JVal) : R JVal :=
  match this with
  | .obj "EvalInto" [some (.module_ m)] => eval_ toplevel m e
  | _ => .error (.method "EvalInto")

end JuliaLean.BootCov.Objects

end

section

/-!
Type-object functions of `base/boot.jl` and `base/essentials.jl` (master
`bbfa0ce4150`): `Typeof`, `TypeVar`, `UnionAll`, `typename`, the
`unwrap_unionall` family, `Vararg` helpers, `datatype_min_ninitialized`,
`has_typevar` and the `TypeApp` machinery.
-/

namespace JuliaLean.BootCov.Types

open JuliaLean
open JuliaLean.BootCov

mutual
/-- Typevar ids free in a type (`jl_has_free_typevars` / `jl_has_typevar`). -/
def freeVars : JType → List Nat
  | .dt _ _ ps => freeVarsList ps
  | .union a b => freeVars a ++ freeVars b
  | .bottom => []
  | .tvar id _ _ _ => [id]
  | .unionAll v body => freeVarsBound v ++ (freeVars body).filter (· ≠ varId v)
  | .vararg T N => freeVarsOpt T ++ freeVarsOpt N
  | .typeApp h p => freeVars h ++ freeVars p
  | .intParam _ => []
  | .names _ => []
  | .other _ => []
def freeVarsList : List JType → List Nat
  | [] => []
  | t :: ts => freeVars t ++ freeVarsList ts
def freeVarsOpt : Option JType → List Nat
  | none => []
  | some t => freeVars t
/-- Free variables of the bounds of a `UnionAll` variable. -/
def freeVarsBound : JType → List Nat
  | .tvar _ _ lb ub => freeVars lb ++ freeVars ub
  | _ => []
/-- The id of a `UnionAll` variable. -/
def varId : JType → Nat
  | .tvar id _ _ _ => id
  | _ => 0
end
-- Source: base/essentials.jl:1288
-- placed here to break an import cycle with essentials

/-- `jl_has_typevar(t, v)`, `base/essentials.jl:1288`. -/
def hasTypevar (t v : JType) : Bool := (freeVars t).contains (varId v)

/-- `jl_has_free_typevars(t)`. -/
def hasFreeTypevars (t : JType) : Bool := !(freeVars t).isEmpty

/-- `isa(x, Type)`: a type object (not a `Vararg`, not a plain parameter). -/
def isType : JType → Bool
  | .vararg _ _ => false
  | .intParam _ => false
  | .names _ => false
  | .other _ => false
  | .typeApp _ _ => false
  | .tvar _ _ _ _ => false
  | _ => true

/-- `Type{x}` and `Core.TypeEgal{x}`. -/
def typeKind (x : JType) : JType := .dt "Type" true [x]
def typeEgalKind (x : JType) : JType := .dt "TypeEgal" true [x]

/-- `(f::typeof(Typeof))(x)`, `base/boot.jl:300-307`; `typeof` is the runtime `typeof`. -/
def typeof_ (typeof : JVal → JType) (x : JVal) : JType :=
  match x with
  | .ty t => if isType t then (if hasFreeTypevars t then typeKind t else typeEgalKind t)
             else typeof x
  | _ => typeof x

/-- `(f::typeof(TypeEqOf))(x)`, `base/boot.jl:316-319`. -/
def typeEqOf (typeof : JVal → JType) (x : JVal) : JType :=
  match x with
  | .ty t => if isType t then typeKind t else typeof x
  | _ => typeof x

/-- `_typeof_captured_variable(t)`, `base/boot.jl:387`. -/
def typeofCapturedVariable (typeof : JVal → JType) (t : JVal) : JType :=
  match t with
  | .ty T => if isType T && hasFreeTypevars T then typeof t else typeof_ typeof t
  | _ => typeof_ typeof t

/-- A bound accepted by `jl_new_typevar`: a type or a typevar. -/
def isBound : JType → Bool
  | .vararg _ _ => false
  | .intParam _ => false
  | .names _ => false
  | .other _ => false
  | _ => true

/-- `_typevar(n::Symbol, lb, ub)` (`jl_new_typevar`) with object identity `fresh`;
`TypeVar(n)`, `TypeVar(n, ub)`, `TypeVar(n, lb, ub)`, `base/boot.jl:370-372`. -/
def typevar3 (fresh : Nat) (n : JVal) (lb ub : JType) : R JType :=
  match n with
  | .sym s =>
    if !isBound lb then .error (.typeError "TypeVar")
    else if !isBound ub then .error (.typeError "TypeVar")
    else .ok (.tvar fresh s lb ub)
  | _ => .error (.typeError "typeassert")
def typevar1 (fresh : Nat) (n : JVal) : R JType := typevar3 fresh n .bottom (.dt "Any" true [])
def typevar2 (fresh : Nat) (n : JVal) (ub : JType) : R JType := typevar3 fresh n .bottom ub

/-- `jl_type_unionall(v, body)` (`src/jltypes.c:1054-1099`). -/
def typeUnionall (v body : JType) : R JType :=
  match body with
  | .vararg T N =>
    let tHas := match T with | some t => hasTypevar t v | none => false
    let nHas := match N with | some n => hasTypevar n v | none => false
    if !tHas && !nHas then .ok body
    else if tHas && nHas then .error (.error "Wrapping `Vararg` directly in UnionAll is disallowed")
    else if tHas then
      match T with
      | some t => .ok (.vararg (some (if hasTypevar t v then .unionAll v t else t)) N)
      | none => .ok body
    else .ok (.vararg T none)
  | .intParam _ | .names _ | .other _ => .error (.typeError "UnionAll")
  | _ =>
    match body, v with
    | .tvar i _ _ _, .tvar j _ _ ub => if i = j then .ok ub
        else if hasTypevar body v then .ok (.unionAll v body) else .ok body
    | _, _ => if hasTypevar body v then .ok (.unionAll v body) else .ok body

/-- `UnionAll(v, t) = ccall(:jl_type_unionall, Any, (Any, Any), v::TypeVar, t)`,
`base/boot.jl:373`. -/
def unionAllCtor (v t : JType) : R JType :=
  match v with
  | .tvar _ _ _ _ => typeUnionall v t
  | _ => .error (.typeError "typeassert")

/-- `typename(a)`, `base/boot.jl:1310-1318`: the type name of a `DataType`, of a `Union`
whose members share it, and of a `UnionAll` body; `TypeNameError` otherwise. -/
def typename : JType → R String
  | .dt name _ _ => .ok name
  | .union a b => do
    let ta ← typename a
    let tb ← typename b
    if ta = tb then pure tb else .error .typeName
  | .unionAll _ body => typename body
  | _ => .error .typeName

/-- `(>:)(a, b) = (b <: a)` and `(!==)(a, b) = !(a === b)`, `base/boot.jl:1322-1323`. -/
def supertypeOf {α : Type} (sub : α → α → Bool) (a b : α) : Bool := sub b a
def notEgal {α : Type} (egal : α → α → Bool) (a b : α) : Bool := !egal a b

/-- `TypeApp(head, param) = new(head, param)`, `base/boot.jl:420-422`. -/
def typeAppCtor (head param : JType) : JType := .typeApp head param

/-- `_contains_typeapp(x)`, `base/boot.jl:426-434`. -/
def containsTypeapp : JType → Bool
  | .typeApp _ _ => true
  | .unionAll _ body => containsTypeapp body
  | _ => false

/-- The nested chain `TypeApp(TypeApp(tc, p1), p2), ...` built by the loops of
`apply_type_or_typeapp`. -/
def typeAppChain (tc : JType) (params : List JType) : JType :=
  params.foldl typeAppCtor tc

/-- `apply_type_or_typeapp(tc, params...)`, `base/boot.jl:436-467`; `applyType` is the
`apply_type` builtin. -/
def applyTypeOrTypeapp (applyType : JType → List JType → R JType) (tc : JType)
    (params : List JType) : R JType :=
  match tc with
  | .tvar _ _ _ _ | .typeApp _ _ => .ok (typeAppChain tc params)
  | _ => if params.any containsTypeapp then .ok (typeAppChain tc params)
         else applyType tc params

/-- `resolve_typegroup(mod, typevars, struct_infos, old_types)`, `base/boot.jl:403-409`:
an empty typegroup returns `()`, otherwise the runtime resolves it. -/
def resolveTypegroup (resolve : List JVal → List JVal → List JVal → JVal)
    (typevars structInfos oldTypes : List JVal) : JVal :=
  if typevars.length = 0 then .tuple [] else resolve typevars structInfos oldTypes

end JuliaLean.BootCov.Types

end

section

/-!
Memory, `MemoryRef`, `Array`, `SimpleVector` and `Symbol` primitives of
`base/boot.jl` and `base/essentials.jl` (master `bbfa0ce4150`).

A memory is its list of slots (`none` is an undefined slot); a reference is a
memory and a 0-based element offset; an array is a reference and its
dimensions. `maxLen` is the largest element count the runtime can allocate for
the element type (`jl_alloc_genericmemory` rejects counts with
`nel >= MAXINTVAL-1` or a byte size that overflows).
-/

namespace JuliaLean.BootCov.Arrays

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv

abbrev Mem := List (Option JVal)

structure MRef where
  mem : Mem
  /-- 0-based offset of the referenced element. -/
  off : Nat

structure Arr where
  ref : MRef
  dims : List JInt64

/-- `memorynew(self, m)` (`jl_alloc_genericmemory`): `m` is read as `size_t`. -/
def memorynew (maxLen : Nat) (m : JInt64) : R Mem :=
  let nel := wrapInt .u64 m.val
  if nel > maxLen then .error (.argument "invalid GenericMemory size")
  else .ok (List.replicate nel.toNat none)

/-- `GenericMemory{kind,T,addrspace}(undef, m)`, `(undef, (m,))` and `()`,
`base/boot.jl:762-765`. -/
def memoryUndef (maxLen : Nat) (m : JInt64) : R Mem := memorynew maxLen m
def memoryUndefTuple (maxLen : Nat) (d : JInt64) : R Mem := memoryUndef maxLen d
def memoryEmpty (maxLen : Nat) : R Mem := memoryUndef maxLen (JInt.lit .i64 0)

/-- `memoryrefnew(mem)`: a reference to the first slot. -/
def memoryrefnew1 (mem : Mem) : MRef := ⟨mem, 0⟩

/-- `memoryrefnew(mem, i, true)`, `src/builtins.c`: `i - 1` read as `size_t` must be
below the length. -/
def memoryrefnewMem (mem : Mem) (i : JInt64) : R MRef :=
  let k := wrapInt .u64 (i.val - 1)
  if k ≥ mem.length then .error .bounds else .ok ⟨mem, k.toNat⟩

/-- `memoryrefnew(ref, i, true)`: the shifted offset, computed modulo `2^64`, must be
below the length. -/
def memoryrefnewRef (r : MRef) (i : JInt64) : R MRef :=
  let k := wrapInt .u64 (r.off + wrapInt .u64 (i.val - 1))
  if k ≥ r.mem.length then .error .bounds else .ok ⟨r.mem, k.toNat⟩

/-- `memoryref(mem)`, `memoryref(mem, i::Integer)`, `memoryref(ref, i::Integer)` and the
`GenericMemoryRef` aliases, `base/boot.jl:768-773`: `Int(i)` converts first. -/
def memoryref1 (mem : Mem) : MRef := memoryrefnew1 mem
def memoryref2 (mem : Mem) (i : BuiltinInt) : R MRef := do
  let i ← ctor .i64 i
  memoryrefnewMem mem i
def memoryrefRef (r : MRef) (i : BuiltinInt) : R MRef := do
  let i ← ctor .i64 i
  memoryrefnewRef r i
def genericMemoryRef1 (mem : Mem) : MRef := memoryref1 mem
def genericMemoryRef2 (mem : Mem) (i : BuiltinInt) : R MRef := memoryref2 mem i
def genericMemoryRefRef (r : MRef) (i : BuiltinInt) : R MRef := memoryrefRef r i

/-- `new_as_memoryref(self, m) = memoryref(Memory(undef, m))`, `base/boot.jl:779`. -/
def newAsMemoryref (maxLen : Nat) (m : JInt64) : R MRef := do
  let mem ← memoryUndef maxLen m
  pure (memoryref1 mem)

/-! `Core.checked_dims` and `_checked_mul_dims` (`base/boot.jl:782-818`) are
`JuliaLean.ReinterpretArrays.checkedDims` and `checkedMulDims`. -/
open JuliaLean.ReinterpretArrays (checkedDims checkedMulDims)

/-- Read a shared-model result as a result of this area (`ArgumentError` stays one). -/
def ofJl {α : Type} : Jl α → R α
  | .ok a => .ok a
  | .error (.argumentError m) => .error (.argument m)
  | .error _ => .error (.error "unexpected exception")

/-- `Array{T,1}(undef, m)`, `base/boot.jl:821-824`. -/
def array1 (maxLen : Nat) (m : JInt64) : R Arr := do
  let mem ← memoryUndef maxLen m
  pure ⟨memoryref1 mem, [m]⟩
/-- `Array{T,2}(undef, m, n)`, `base/boot.jl:825-827`. -/
def array2 (maxLen : Nat) (m n : JInt64) : R Arr := do
  let p ← ofJl (checkedDims [m, n])
  let r ← newAsMemoryref maxLen p
  pure ⟨r, [m, n]⟩
/-- `Array{T,3}(undef, m, n, o)`, `base/boot.jl:828-830`. -/
def array3 (maxLen : Nat) (m n o : JInt64) : R Arr := do
  let p ← ofJl (checkedDims [m, n, o])
  let r ← newAsMemoryref maxLen p
  pure ⟨r, [m, n, o]⟩
/-- `Array{T,N}(undef, d::Vararg{Int,N})`, `base/boot.jl:831-833`. -/
def arrayN (maxLen : Nat) (d : List JInt64) : R Arr := do
  let p ← ofJl (checkedDims d)
  let r ← newAsMemoryref maxLen p
  pure ⟨r, d⟩

/-- Method selection among the four `Array{T,N}(undef, dims...)` methods. -/
def arrayUndef (maxLen : Nat) : List JInt64 → R Arr
  | [m] => array1 maxLen m
  | [m, n] => array2 maxLen m n
  | [m, n, o] => array3 maxLen m n o
  | d => arrayN maxLen d

/-- `Array{T,N}(undef, d::NTuple{N,Int})`, `base/boot.jl:835-838`: splat the tuple. -/
def arrayUndefTuple (maxLen : Nat) (d : List JInt64) : R Arr := arrayUndef maxLen d
/-- `Array{T}(undef, dims...)` and `Array{T}(undef, d::Tuple)`, `base/boot.jl:840-845`:
`N` is the number of dimensions. -/
def arrayTUndef (maxLen : Nat) (d : List JInt64) : R Arr := arrayUndef maxLen d
def arrayTUndefTuple (maxLen : Nat) (d : List JInt64) : R Arr := arrayUndefTuple maxLen d
/-- `Vector{T}() = Vector{T}(undef, 0)`, `base/boot.jl:847`. -/
def vectorEmpty (maxLen : Nat) : R Arr := array1 maxLen (JInt.lit .i64 0)

/-- The converting constructors `Array{T,N} where T`, `Array(A)`, `Array{T}(A)` and
`AbstractArray{T}(A)`, `base/boot.jl:849-854`: each calls the constructor with element
type `elt` and the source dimensionality `N`. `conv elt N` is that constructor. -/
def arrayFromAbstract {A B : Type} (conv : String → Nat → A → B) (eltS : String) (N : Nat)
    (x : A) : B := conv eltS N x
def arrayOf {A B : Type} (conv : String → Nat → A → B) (eltT : String) (N : Nat) (x : A) : B :=
  conv eltT N x
def arrayTOf {A B : Type} (conv : String → Nat → A → B) (T : String) (N : Nat) (x : A) : B :=
  conv T N x
def abstractArrayTOf {A B : Type} (conv : String → Nat → A → B) (T : String) (N : Nat)
    (x : A) : B := conv T N x

/-! ## `Symbol` constructors, `base/boot.jl:858-873` -/

/-- `_Symbol(ptr, sz, root)` (`jl_symbol_n`): a symbol is its byte string; a NUL byte
throws `ArgumentError`. -/
def symbolN (bytes : List Nat) : R (List Nat) :=
  if bytes.contains 0 then .error (.argument "Symbol name may not contain \\0") else .ok bytes

/-- `Symbol(s::String)`: the bytes of `s` (`sizeof(s)` of them). -/
def symbolOfString (s : List Nat) : R (List Nat) := symbolN (s.take s.length)
/-- `Symbol(a::Array{UInt8,1})`: `size(a)[1]` bytes starting at the array's reference. -/
def symbolOfVector (a : List Nat) (off len : Nat) : R (List Nat) := symbolN ((a.drop off).take len)
/-- `Symbol(s::Symbol) = s`. -/
def symbolOfSymbol (s : List Nat) : List Nat := s

end JuliaLean.BootCov.Arrays

end

section

/-!
Macros of `base/boot.jl` and `base/essentials.jl` (master `bbfa0ce4150`) as
functions from their arguments (and `__module__`, `__source__`) to the `Expr`
they return, plus the small doc-system helpers of `Core`.
-/

namespace JuliaLean.BootCov.Macros

open JuliaLean
open JuliaLean.BootCov

def EffectFlags.toList (f : EffectFlags) : List JVal :=
  [f.consistent, f.effectFree, f.nothrow, f.terminatesGlobally, f.terminatesLocally,
    f.notaskstate, f.inaccessiblememonly, f.noub, f.noubIfNoinbounds, f.consistentOverlay,
    f.nortcall].map JVal.bool

/-- `@_total_meta()`, `base/boot.jl:333-346`. -/
def coreTotalMeta : EffectFlags := ⟨true, true, true, true, false, true, true, true, false, false, true⟩
/-- `@_foldable_meta()`, `base/boot.jl:348-361`. -/
def coreFoldableMeta : EffectFlags := ⟨true, true, false, true, false, true, true, true, false, false, true⟩

/-- The expansion of an effect macro: `_is_internal(__module__) && Expr(:meta, Expr(:purity, ...))`. -/
def effectMeta (internal : Bool) (f : EffectFlags) : JVal :=
  if internal then .expr "meta" [.expr "purity" f.toList] else .bool false

/-- `Core._is_internal(m) = m === Core`, `base/boot.jl:331`. -/
def coreIsInternal (m : String) : Bool := m == "Core"

/-- `@nospecialize(x)` in `Core`, `base/boot.jl:324-326`. -/
def coreNospecialize (x : JVal) : JVal := .expr "escape" [.expr "meta" [.sym "nospecialize", x]]
/-- `@latestworld`, `@inline`, `@noinline`, `@nospecializeinfer`, `@_boundscheck`,
`base/boot.jl:329`, 363-367. -/
def latestworld : JVal := .expr "latestworld" []
def inlineMacro : JVal := .expr "meta" [.sym "inline"]
def noinlineMacro : JVal := .expr "meta" [.sym "noinline"]
def nospecializeinferMacro : JVal := .expr "meta" [.sym "nospecializeinfer"]
def boundscheckMarker : JVal := .expr "boundscheck" []

/-- `Expr(args...) = _expr(args...)`, `base/boot.jl:327`: the head must be a `Symbol`. -/
def exprCtor : List JVal → R JVal
  | [] => .error (.argument "too few arguments")
  | .sym h :: args => .ok (.expr h args)
  | _ :: _ => .error (.typeError "Expr")

/-! ## Doc-system basics in `Core`, `base/boot.jl:940-960` -/

/-- `@doc(x...)`, lines 941-945; `atdoc` is the current `Core.atdoc` hook. -/
def docMacro (atdoc : JVal → String → List JVal → JVal) (source : JVal) (module_ : String)
    (x : List JVal) : JVal :=
  let docex := atdoc source module_ x
  match docex with
  | .expr "escape" _ => docex
  | _ => .expr "escape" [.expr "hygienic-scope" [docex, .module_ "Core", source]]

/-- `@__doc__(x)`, lines 946-948. -/
def docMarker (x : JVal) : JVal := .expr "escape" [.expr "block" [.expr "meta" [.sym "doc"], x]]

/-- `isbasicdoc(x)`, line 950. -/
def isbasicdoc : JVal → Bool
  | .expr "." _ => true
  | .quoteNode _ => true
  | .sym _ => true
  | _ => false

/-- `firstarg(arg1, args...) = arg1`, line 951. -/
def firstarg (arg1 : JVal) (_ : List JVal) : JVal := arg1

/-- `iscallexpr(ex::Expr)` and `iscallexpr(ex) = false`, lines 952-953. -/
def iscallexpr : JVal → R Bool
  | .expr "where" (a :: _) => iscallexpr a  -- `firstarg(ex.args...)` is `a`
  | .expr "where" [] => .error (.method "firstarg")
  | .expr "call" _ => .ok true
  | _ => .ok false

/-- `ignoredoc(source, mod, str, expr)`, lines 954-957. -/
def ignoredoc (expr : JVal) : R JVal := do
  let c ← iscallexpr expr
  if isbasicdoc expr || c then pure (.expr "escape" [.nothing]) else pure (.expr "escape" [expr])

/-- `atdoc!(λ) = global atdoc = λ`, line 960: returns `λ` and installs it. -/
def atdocBang {α : Type} (_old : α) (lam : α) : α × α := (lam, lam)

end JuliaLean.BootCov.Macros

end

section

/-!
Remaining methods of `base/boot.jl` and `base/essentials.jl` (master
`bbfa0ce4150`): the stand-alone `Core` printing functions, identity
conversions, tuple helpers, `Pairs`, small predicates and the `Core` hooks.
-/

namespace JuliaLean.BootCov.Misc

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv

/-! ## `Core` printing, `base/boot.jl:970-1006`

The two `Core` streams write to the runtime's `jl_uv_stdout`/`jl_uv_stderr`; the
state is the byte list written so far to each. `staticShow x` is the output of
`jl_static_show` for `x`, and `utf8 c` the bytes `jl_uv_putc` writes for `c`. -/

inductive CoreIO where
  | stdout
  | stderr
  deriving DecidableEq, Repr

/-- `CoreSTDOUT()` and `CoreSTDERR()`, lines 974-977. -/
def coreSTDOUT : CoreIO := .stdout
def coreSTDERR : CoreIO := .stderr

structure Out where
  out : List Nat
  err : List Nat

/-- `io_pointer(::CoreSTDOUT)` and `io_pointer(::CoreSTDERR)`, lines 981-982: the stream's
runtime handle, given as `(stdoutHandle, stderrHandle)`. -/
def ioPointer (handles : Nat × Nat) : CoreIO → Nat
  | .stdout => handles.1
  | .stderr => handles.2

def emit (io : CoreIO) (bs : List Nat) (s : Out) : Out :=
  match io with
  | .stdout => { s with out := s.out ++ bs }
  | .stderr => { s with err := s.err ++ bs }

/-- `unsafe_write(io, x::Ptr{UInt8}, nb::UInt)` and the `nb::Int` method, lines 984-987:
write the `nb` bytes at `x` (`bytes`) and return `nb`. -/
def unsafeWrite (io : CoreIO) (bytes : List Nat) (nb : Nat) (s : Out) : Nat × Out :=
  (nb, emit io (bytes.take nb) s)

/-- `write(io, x::UInt8)`, lines 988-989. -/
def writeByte (io : CoreIO) (x : Nat) (s : Out) : Nat × Out := (1, emit io [x] s)

/-- `write(io, x::String)`, lines 990-994: `sizeof(x)` bytes. -/
def writeString (io : CoreIO) (x : List Nat) (s : Out) : Nat × Out :=
  let nb := x.length
  let r := unsafeWrite io x nb s
  (nb, r.2)

/-- Printable arguments of the `Core` printing functions. -/
inductive PrintArg where
  | char (bytes : List Nat)
  | string (bytes : List Nat)
  | other (shown : List Nat)

/-- `show(io, x)`, line 996 (`jl_static_show`). -/
def coreShow (io : CoreIO) (staticShow : PrintArg → List Nat) (x : PrintArg) (s : Out) : Out :=
  emit io (staticShow x) s

/-- `print(io, x::AbstractChar)`, `print(io, x::String)`, `print(io, x)`, lines 997-999. -/
def print1 (io : CoreIO) (staticShow : PrintArg → List Nat) (x : PrintArg) (s : Out) : Out :=
  match x with
  | .char b => emit io b s
  | .string b => (writeString io b s).2
  | v => coreShow io staticShow v s

/-- `print(io, x, a...) = (print(io, x); print(io, a...))`, line 1000. -/
def printN (io : CoreIO) (staticShow : PrintArg → List Nat) : List PrintArg → Out → Out
  | [], s => s
  | x :: a, s => printN io staticShow a (print1 io staticShow x s)

/-- `println(io) = (write(io, 0x0a); nothing)` and `println(io, x...)`, lines 1001-1002. -/
def println0 (io : CoreIO) (s : Out) : Out := (writeByte io 10 s).2
def printlnN (io : CoreIO) (staticShow : PrintArg → List Nat) (xs : List PrintArg) (s : Out) : Out :=
  println0 io (printN io staticShow xs s)

/-- `show(a)`, `print(a...)`, `println(a...)` on `Core.stdout`, lines 1004-1006. -/
def show0 (staticShow : PrintArg → List Nat) (a : PrintArg) (s : Out) : Out :=
  coreShow .stdout staticShow a s
def print0 (staticShow : PrintArg → List Nat) (a : List PrintArg) (s : Out) : Out :=
  printN .stdout staticShow a s
def printlnStdout (staticShow : PrintArg → List Nat) (a : List PrintArg) (s : Out) : Out :=
  printlnN .stdout staticShow a s

/-- The bytes `print` produces for one argument. -/
def printBytes (staticShow : PrintArg → List Nat) : PrintArg → List Nat
  | .char b => b
  | .string b => b
  | v => staticShow v

/-! ## Identity conversions and `Union{}` -/

/-- `convert(::Type{Any}, x) = x`, `convert(::Type{T}, x::T) = x` (`base/boot.jl:381-382`),
`convert(::Type{Type}, x::Type) = x` and `convert(::Type{String}, x::String) = x`
(`base/essentials.jl:476-480`), `convert(::Type{T}, x::T) where T<:Tuple` (line 652). -/
def convertSame {α : Type} (x : α) : α := x
/-- `cconvert(::Type{T}, x) = convert(T, x)` in `Core`, `base/boot.jl:383`. -/
def coreCconvert {α β : Type} (convert : α → β) (x : α) : β := convert x
/-- `unsafe_convert(::Type{T}, x::T) = x`, `base/boot.jl:384` and `base/essentials.jl:742-743`. -/
def unsafeConvertSame {α : Type} (x : α) : α := x

/-- `Union{}(a...)` and `kwcall(kwargs, ::Type{Union{}}, a...)` (`base/boot.jl:398-399`),
`convert(::Type{Union{}}, _...)` (`base/essentials.jl:474`) and
`cconvert(::Type{Union{}}, x...) = convert(Union{}, x...)` (line 740). -/
def unionBottomCtor {α : Type} (_ : List α) : R α :=
  .error (.argument "cannot construct a value of type Union{} for return result")
def kwcallUnionBottom {α : Type} (_kwargs : α) (a : List α) : R α := unionBottomCtor a

/-! ## `Core` hooks and shims, `base/boot.jl:1227-1281` -/

/-- `struct_name_shim(x, name, mod, t) = x === mod ? t : getfield(x, name)`. -/
def structNameShim {α : Type} (getfield : α → String → R α) (eqMod : Bool) (x : α) (name : String)
    (t : α) : R α :=
  if eqMod then .ok t else getfield x name

/-- `Core._parse`, `Core._lower` and `Core._toplevel_eval` hooks. -/
structure Hooks (α : Type) where
  parse : α
  lower : α
  toplevelEval : α

/-- `_setparser!(p)`, `_setlowerer!(l)` and `_set_toplevel_eval!(f)`, lines 1252-1254:
`setglobal!` installs the hook and returns it. -/
def setparser {α : Type} (h : Hooks α) (p : α) : α × Hooks α := (p, { h with parse := p })
def setlowerer {α : Type} (h : Hooks α) (l : α) : α × Hooks α := (l, { h with lower := l })
def setToplevelEval {α : Type} (h : Hooks α) (f : α) : α × Hooks α := (f, { h with toplevelEval := f })

/-- `_hasmethod(tt)`, lines 1276-1281: whether `jl_gf_invoke_lookup(tt, nothing, world)` finds
a method in the current world. -/
def hasmethod {τ μ : Type} (lookup : τ → Nat → Option μ) (world : Nat) (tt : τ) : Bool :=
  !(lookup tt world).isNone

end JuliaLean.BootCov.Misc

end


/-!
# Model of `base/boot.jl`

The `Core` module of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`: the constructors of the
core types, the AST and IR node constructors, the `Array`/`GenericMemory` constructors, the error
types and their constructors, the `NamedTuple`/`Tuple` helpers, the `Core` integer conversions, the
bootstrapping `import`/`using`, the documentation hooks, the debugging `print` functions and the
frontend hooks, on a 64-bit platform (`Int === Int64`, `UInt === UInt64`).

A Julia value is a value of the installed `base/expr.jl` model (`JuliaLean.base.expr.Value`): the
AST and IR nodes of that type are built directly, and every other value is a leaf `L`. Instances of
the structs that this file defines (the exceptions, `TypeApp`, `Pair`, the inference lattice
elements and the rest) are `Obj` values, a leaf through `CoreOps.obj`; a field that `new` left
undefined is `none`. Fixed-width integers are the `JInt` values of `JuliaLean.Core`, and the
intrinsics `trunc_int`, `sext_int`, `zext_int`, `bitcast`, `eq_int`, `slt_int`, `xor_int`,
`sle_int`, `ule_int` and `ult_int` are the installed `base/int.jl` ones (`JuliaLean.base.int`),
with `checked_smul_int` and `udiv_int` from `JuliaLean.C`. A `Bool` operand of an intrinsic is its
byte `0x00` or `0x01`.

The builtins (`isa`, `typeof`, `===`, `getfield`, `fieldtype`, `nfields`, `apply_type`, `<:`,
`_typevar`, `new`, `splatnew`, `memorynew`, `memoryrefnew`, `getglobal`, `setglobal!`,
`_apply_iterate`, `_import`, `_using`, ...) and the runtime `ccall`s are typed operations in
`CoreOps` with their documented behaviour and no assumed laws. `CoreOps.call` is a call of a
generic function that later files extend (`convert`, `Int`, `Base.getindex`, the `Array`
conversions, ...), resolved by Julia's dispatch at the time of the call. An argument constrained
by a method signature is passed already dispatched: a typed `Value` for Julia types the model
represents by `Value`, a `JInt` for a fixed-width integer, a `Sym` for a `Symbol`. The fields of a
struct that `new` fills are converted with `convert(fieldtype, x)` when the field is typed, as
lowering does, and checked against the field type; raw `Expr(:new, ...)` only checks.

`CoreM` is a computation over the runtime world `W`: `.error (v, w)` is `throw(v)` with the world
`w` at the throw, and `none` is divergence (the recursion of `_contains_typeapp` and `typename` is a
`partial_fixpoint`). Exceptions raised by the runtime itself (failed type assertions, missing
methods, builtin errors) are built as `Obj` values directly, as the C runtime does; a Julia-level
`throw(T(...))` calls the modelled constructor.
-/

namespace JuliaLean.base.boot

open JuliaLean
open JuliaLean.base.expr (Value LeafOps Sym)
open JuliaLean.base.int (trunc_int sext_int zext_int bitcast eq_int slt_int xor_int sle_int
  ule_int ult_int sub_int)

abbrev I32 := JInt .i32
abbrev I64 := JInt .i64
abbrev U8 := JInt .u8
abbrev U64 := JInt .u64

/-- Instances of the structs defined in this file whose values are not AST nodes of
`base/expr.jl`; `none` is a field that `new` left undefined. -/
inductive Obj (L : Type) where
  | typeApp (head param : Value L)
  | errorException (msg : Value L)
  | boundsError (a i : Option (Value L))
  | divideError
  | outOfMemoryError
  | readOnlyMemoryError
  | segmentationFault
  | stackOverflowError
  | undefRefError
  | undefVarError (var world : Value L) (scope : Option (Value L))
  | concurrencyViolationError (msg : Value L)
  | missingCodeError (mi : Value L)
  | interruptException
  | domainError (val msg : Value L)
  | typeError (func context expected got : Value L)
  | inexactError (func args : Value L)
  | overflowError (msg : Value L)
  | argumentError (msg : Value L)
  | undefKeywordError (var : Value L)
  | methodError (f args world : Value L)
  | assertionError (msg : Value L)
  | fieldError (typ field : Value L)
  | loadError (file line error : Value L)
  | initError (mod error : Value L)
  | abiOverride (abi defn : Value L)
  | precompilableError
  | trimFailure
  | evalInto (m : Value L)
  /-- `VecElement{T}(value)`. -/
  | vecElement (T value : Value L)
  | const (val : Value L)
  | partialStruct (typ undefs fields : Value L)
  | interConditional (slot thentype elsetype : Value L)
  | interMustAlias (slot vartyp fldidx fldtyp : Value L)
  | partialOpaque (typ env parent source : Value L)
  | partialTask (fetch_type : Value L)
  | possiblyAmbiguous
  | debugInfo (defn linetable edges codelocs : Value L)
  | methodMatch (spec_types sparams method fully_covers : Value L)
  | lineInfoNode (mod method file line inlined_at : Value L)
  | undefInitializer
  | coreSTDOUT
  | coreSTDERR
  | generatedFunctionStub (gen argnames spnames : Value L)
  /-- `Pair{A, B}(first, second)`. -/
  | pair (A B first second : Value L)
  | typeNameError (a : Value L)
  | macroSource (lno syntax_ver : Value L)

/-- A computation in the runtime world `W` that may throw a Julia value or diverge (`none`). -/
abbrev CoreM (W L A : Type) := W → Option (Except (Value L × W) (A × W))

instance {W L : Type} : Monad (CoreM W L) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world => do
    match ← action world with
    | .error error => pure (.error error)
    | .ok (value, world) => next value world

instance {W L : Type} : MonadExceptOf (Value L) (CoreM W L) where
  throw value := fun world => some (.error (value, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (value, world)) => handler value world

instance monoBindCoreM {W L : Type} : Lean.Order.MonoBind (CoreM W L) where
  bind_mono_left h := by
    intro w
    exact Lean.Order.MonoBind.bind_mono_left (m := Option) (h w)
  bind_mono_right h := by
    intro w
    apply Lean.Order.MonoBind.bind_mono_right (m := Option)
    intro r
    rcases r with e | ⟨v, w'⟩
    · exact Lean.Order.PartialOrder.rel_refl
    · exact h v w'

/-- The builtins, intrinsics and runtime calls used by `boot.jl`, over the world `W` and the leaf
values `L`. Each operation is the documented behaviour of the named builtin or C entry point;
no laws are assumed. -/
structure CoreOps (W L : Type) extends LeafOps L where
  /-- A `String` with this text. -/
  str : String → L
  /-- An instance of a struct defined in this file. -/
  obj : Obj L → L
  /-- A fixed-width integer value. -/
  int : {t : IntTy} → JInt t → L
  /-- The tuple `(xs...)`. -/
  tuple : List (Value L) → L
  /-- `Core.svec(xs...)`. -/
  svec : List (Value L) → L
  /-- The value of the constant `Core.name` (a type, a function or a module); `"Union{}"` is the
  empty union. -/
  core : String → L
  /-- The builtin `===`. -/
  same : Value L → Value L → Bool
  /-- The builtin `isa(x, T)`. -/
  isa : Value L → Value L → Bool
  /-- The builtin `typeof`. -/
  typeOf : Value L → L
  /-- `has_free_typevars(t)`. -/
  hasFreeTypevars : Value L → Bool
  /-- The builtin `apply_type(tc, params...)`: `TypeError` for an invalid parameter. -/
  applyType : Value L → List (Value L) → CoreM W L (Value L)
  /-- The builtin `<:`: `TypeError` for an argument that is not a type. -/
  subtype : Value L → Value L → CoreM W L Bool
  /-- The builtin `getfield(x, f)` for a field name or index `f`: `FieldError`, `BoundsError`,
  `UndefRefError` or `TypeError` when the field does not exist or is undefined. -/
  getfield : Value L → Value L → CoreM W L (Value L)
  /-- The builtin `nfields`. -/
  nfields : Value L → I64
  /-- The builtin `fieldtype(T, f)`. -/
  fieldtype : Value L → Sym → CoreM W L (Value L)
  /-- The builtin `getglobal(m, s)`: `UndefVarError` for an undefined binding. -/
  getglobal : Value L → Value L → CoreM W L (Value L)
  /-- The builtin `setglobal!(m, s, x)`, returning `x`. -/
  setglobal : Value L → Sym → Value L → CoreM W L (Value L)
  /-- A call `f(args...)` of a generic function, dispatched over the methods that exist when it
  runs. -/
  call : Value L → List (Value L) → CoreM W L (Value L)
  /-- The builtin `_typevar(n, lb, ub)`: `TypeError` for a bound that is not a type. -/
  typevar : Sym → Value L → Value L → CoreM W L (Value L)
  /-- `jl_type_unionall(v, t)`. -/
  typeUnionall : Value L → Value L → CoreM W L (Value L)
  /-- The builtin `_svec_len`. -/
  svecLen : Value L → I64
  /-- `jl_resolve_typegroup(mod, typevars, struct_infos, old_types)`. -/
  resolveTypegroup : Value L → Value L → Value L → Value L → CoreM W L (Value L)
  /-- `jl_get_tls_world_age()`. -/
  worldAge : CoreM W L U64
  /-- The builtin `new` of a mutable struct `Core.Box`, with `contents` given or undefined. -/
  newBox : Option (Value L) → CoreM W L (Value L)
  /-- `jl_get_ptls_states()`. -/
  getptls : CoreM W L (Value L)
  /-- `jl_gc_new_weakref_th(ptls, v)`: a new `WeakRef` to `v`. -/
  newWeakref : Value L → Value L → CoreM W L (Value L)
  /-- `jl_load_(m, fname)`: evaluate the file in module `m`. -/
  load : Value L → Value L → CoreM W L (Value L)
  /-- `jl_toplevel_eval_in(m, e)`. -/
  toplevelEval : Value L → Value L → CoreM W L (Value L)
  /-- `jl_new_codeinst(...)` with the thirteen arguments of `CodeInstance`. -/
  newCodeinst : List (Value L) → CoreM W L (Value L)
  /-- `jl_module_globalref(m, s)`: the `GlobalRef` of the binding, created if needed. -/
  moduleGlobalref : Value L → Sym → CoreM W L (Value L)
  /-- `jl_f_new_module(name, std_imports, default_names)`. -/
  newModule : Sym → Bool → Bool → CoreM W L (Value L)
  /-- The builtin `memorynew(T, m)`: `ArgumentError("invalid GenericMemory size: ...")` for a
  negative or too large `m`. -/
  memorynew : Value L → I64 → CoreM W L (Value L)
  /-- The builtin `memoryrefnew(mem)`: a reference to the first element. -/
  memoryrefnew : Value L → CoreM W L (Value L)
  /-- The builtin `memoryrefnew(ref, i, boundscheck)`: `BoundsError` out of range when
  `boundscheck` is true. -/
  memoryrefnewIndex : Value L → Value L → Bool → CoreM W L (Value L)
  /-- The builtin `new(T, fields...)`: `TypeError(:new, ...)` for a field of the wrong type. -/
  new : Value L → List (Value L) → CoreM W L (Value L)
  /-- The builtin `splatnew(T, t)`. -/
  splatnew : Value L → Value L → CoreM W L (Value L)
  /-- The bytes of a `String` (`jl_string_ptr` and `sizeof`). -/
  stringBytes : Value L → List U8
  /-- The bytes of a `Vector{UInt8}`. -/
  vectorBytes : Value L → CoreM W L (List U8)
  /-- The name of the `Symbol` with these bytes (`jl_symbol_n`, given no zero byte). -/
  symbolName : List U8 → Sym
  /-- The builtin `_import(to, from, asname, name, explicit)`. -/
  importBinding : Value L → Value L → Value L → Value L → Bool → CoreM W L Unit
  /-- The builtin `_using(to, from)`. -/
  usingModule : Value L → Value L → CoreM W L Unit
  /-- `Intrinsics.pointerref(cglobal(:jl_uv_stdout or :jl_uv_stderr, Ptr{Cvoid}), 1, 1)`. -/
  uvStdio : Bool → CoreM W L (Value L)
  /-- `jl_uv_puts(stream, ptr, nb)`. -/
  uvPuts : Value L → Value L → Value L → CoreM W L Unit
  /-- `jl_uv_putb(stream, byte)`. -/
  uvPutb : Value L → U8 → CoreM W L Unit
  /-- `jl_uv_putc(stream, char)`. -/
  uvPutc : Value L → Value L → CoreM W L Unit
  /-- `jl_string_ptr(s)`. -/
  stringPtr : Value L → CoreM W L (Value L)
  /-- `jl_static_show(stream, x)`. -/
  staticShow : Value L → Value L → CoreM W L Unit
  /-- The builtin `_apply_iterate(iterate, f, args...)`. -/
  applyIterate : Value L → List (Value L) → CoreM W L (Value L)
  /-- `jl_gf_invoke_lookup(tt, nothing, world)`: the matching method or `nothing`. -/
  invokeLookup : Value L → U64 → CoreM W L (Value L)
  /-- The intrinsic `bitcast(T, x)`. -/
  bitcastValue : Value L → Value L → CoreM W L (Value L)
  /-- `jl_ver_major()` and `jl_ver_minor()`. -/
  verMajor : CoreM W L I32
  verMinor : CoreM W L I32

section
variable {W L : Type} (ops : CoreOps W L)

/-- The constant `Core.name` as a value. -/
def coreV (name : String) : Value L := .leaf (ops.core name)

/-- A `String` value. -/
def strV (s : String) : Value L := .leaf (ops.str s)

/-- An `Int` value. -/
def intV {t : IntTy} (x : JInt t) : Value L := .leaf (ops.int x)

/-- A `Bool` value. -/
def boolV (b : Bool) : Value L := .leaf (ops.ofBool b)

/-- `nothing`. -/
def nothingV : Value L := .leaf ops.nothing

/-- `x === nothing`. -/
def isNothingV (x : Value L) : Bool := ops.same x (nothingV ops)

/-- An instance of a struct of this file as a value. -/
def objV (o : Obj L) : Value L := .leaf (ops.obj o)

/-- The tuple `(xs...)` as a value. -/
def tupleV (xs : List (Value L)) : Value L := .leaf (ops.tuple xs)

/-- `throw(x)` of an instance built by the runtime. -/
def throwObj {α : Type} (o : Obj L) : CoreM W L α := throw (objV ops o)

/-- The `TypeError(func, context, expected, got)` that the runtime throws. -/
def throwTypeError {α : Type} (func context : String) (expected got : Value L) : CoreM W L α :=
  throwObj ops (.typeError (.symbol func) (strV ops context) expected got)

/-- `x::T`: `TypeError(:typeassert, "", T, x)` unless `isa(x, T)`. -/
def typeassert (x T : Value L) : CoreM W L (Value L) :=
  if ops.isa x T then pure x else throwTypeError ops "typeassert" "" T x

/-- The `MethodError` that dispatch throws when no method of the `Core` function `f` matches
`args`, in the current world. -/
def noMethod {α : Type} (f : String) (args : List (Value L)) : CoreM W L α := do
  let world ← ops.worldAge
  throwObj ops (.methodError (coreV ops f) (tupleV ops args) (intV ops world))

/-- The value that lowering of `new` stores in the typed field `field` of the struct type `S`:
`convert(fieldtype(S, field), x)`, which must then have the field type. -/
def convertField (S : Value L) (field : Sym) (x : Value L) : CoreM W L (Value L) := do
  let T ← ops.fieldtype S field
  let y ← ops.call (coreV ops "convert") [T, x]
  if ops.isa y T then pure y else throwTypeError ops "new" "" T y

/-- `convertField` for a struct type `Core.name`. -/
def cf (name : String) (field : Sym) (x : Value L) : CoreM W L (Value L) :=
  convertField ops (coreV ops name) field x

/-- The bit pattern `0x00` or `0x01` of a `Bool`, read as an integer of type `T` (`bitcast` and
`zext_int` of a `Bool`). -/
def boolBits (T : IntTy) (b : Bool) : JInt T := JInt.lit T (if b then 1 else 0)

/-- The type `T` of a fixed-width integer as a value. -/
def intType (T : IntTy) : Value L := coreV ops T.name

/-- `Expr(:meta, Expr(:purity, flags...))`. -/
def purityMeta (flags : List Bool) : Value L :=
  .expr "meta" [.expr "purity" (flags.map (boolV ops))]

/-- `n::Symbol`: the runtime's `TypeError(:typeassert, "", Symbol, n)` otherwise. -/
def assertSymbol (n : Value L) : CoreM W L Sym :=
  match n with
  | .symbol s => pure s
  | _ => throwTypeError ops "typeassert" "" (coreV ops "Symbol") n

/-- The function `Main.Base.name`: `getfield` of the module `Base` read from `Main`. -/
def baseFunction (name : Sym) : CoreM W L (Value L) := do
  ops.getfield (← ops.getfield (coreV ops "Main") (.symbol "Base")) (.symbol name)

-- Reason: Commented-out descriptions of the builtin types that the runtime defines in C; they define no method.
-- UNTRANSLATED
-- Source: base/boot.jl:1-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # commented-out definitions are implemented in C
-- 
-- #abstract type Any <: Any end
-- #abstract type AnyType end
-- #struct TypeEq <: AnyType
-- #    T
-- #end
-- #const Type = TypeEq(T) where T
-- # TypeEgal{T} is the egality-based dual of TypeEq{T}: its only instance is `T`
-- # itself (matched by `===`), used internally for dispatch-cache specialization.
-- # Free typevars are disallowed inside TypeEgal.
-- #struct TypeEgal <: AnyType
-- #    T
-- #end
-- 
-- #abstract type Vararg{T} end
-- 
-- #mutable struct Symbol
-- ## opaque
-- #end
-- 
-- #mutable struct TypeName
-- #    name::Symbol
-- #end
-- 
-- #mutable struct DataType <: AnyType
-- #    name::TypeName
-- #    super::Type
-- #    parameters::Tuple
-- #    names::Tuple
-- #    types::Tuple
-- #    ctor
-- #    instance
-- #    size::Int32
-- #    abstract::Bool
-- #    mutable::Bool
-- #    pointerfree::Bool
-- #end
-- 
-- #struct Union <: AnyType
-- #    a
-- #    b
-- #end
-- 
-- #mutable struct TypeVar
-- #    name::Symbol
-- #    lb::Type
-- #    ub::Type
-- #end
-- 
-- #struct UnionAll <: AnyType
-- #    var::TypeVar
-- #    body
-- #end
-- 
-- #struct Nothing
-- #end
-- #const nothing = Nothing()
-- 
-- #abstract type AbstractArray{T,N} end
-- #abstract type DenseArray{T,N} <: AbstractArray{T,N} end
-- 
-- #primitive type AddrSpace{Backend::Module} 8 end
-- #const CPU = bitcast(AddrSpace{Core}, 0x00)
-- 
-- #struct GenericMemory{kind::Symbol, T, AS::AddrSpace}
-- #   length::Int
-- #   const data::Ptr{Cvoid} # make this GenericPtr{addrspace, Cvoid}
-- #   Union{ # hidden data
-- #       elements :: NTuple{length, T}
-- #       owner :: Any
-- #   }
-- #end
-- 
-- #struct GenericMemoryRef{kind::Symbol, T, AS::AddrSpace}
-- #    mem::GenericMemory{kind, T, AS}
-- #    data::Ptr{Cvoid} # make this GenericPtr{addrspace, Cvoid}
-- #end
-- 
-- #mutable struct Array{T,N} <: DenseArray{T,N}
-- #  ref::MemoryRef{T}
-- #  size::NTuple{N,Int}
-- #end
-- 
-- #mutable struct Module
-- ## opaque
-- #end
-- 
-- #mutable struct SimpleVector
-- ## opaque
-- #end
-- 
-- #mutable struct String
-- ## opaque
-- #end
-- 
-- #mutable struct Method
-- #...
-- #end
-- 
-- #mutable struct MethodInstance
-- #...
-- #end
-- 
-- #mutable struct CodeInstance
-- #...
-- #end
-- 
-- #mutable struct CodeInfo
-- #...
-- #end
-- 
-- #mutable struct TypeMapLevel
-- #...
-- #end
-- 
-- #mutable struct TypeMapEntry
-- #...
-- #end
-- 
-- #abstract type Ref{T} end
-- #primitive type Ptr{T} <: Ref{T} {32|64} end
-- 
-- # types for the front end
-- 
-- #mutable struct Expr
-- #    head::Symbol
-- #    args::Array{Any,1}
-- #end
-- 
-- #struct LineNumberNode
-- #    line::Int
-- #    file::Union{Symbol,Nothing}
-- #end
-- 
-- #struct LegacyLineInfoNode end # only used internally during lowering
-- 
-- #struct DebugInfo
-- #    def::Any # (Union{Symbol, Method, MethodInstance})
-- #    linetable::Any # (Union{Nothing,DebugInfo})
-- #    edges::SimpleVector # Vector{DebugInfo}
-- #    codelocs::String # compressed Vector{UInt8}
-- #end
-- 
-- #struct GotoNode
-- #    label::Int
-- #end
-- 
-- #struct GotoIfNot
-- #    cond::Any
-- #    dest::Int
-- #end
-- 
-- #struct ReturnNode
-- #    val::Any
-- #end
-- 
-- #struct PiNode
-- #    val
-- #    typ
-- #end
-- 
-- #struct PhiNode
-- #    edges::Vector{Int32}
-- #    values::Vector{Any}
-- #end
-- 
-- #struct PhiCNode
-- #    values::Vector{Any}
-- #end
-- 
-- #struct UpsilonNode
-- #    val
-- #end
-- 
-- #struct QuoteNode
-- #    value
-- #end
-- 
-- #struct GlobalRef
-- #    mod::Module
-- #    name::Symbol
-- #end
-- 
-- #mutable struct Task
-- #    next::Any
-- #    queue::Any
-- #    storage::Any
-- #    donenotify::Any
-- #    result::Any
-- #    scope::Any
-- #    code::Any
-- #    @atomic _state::UInt8
-- #    sticky::UInt8
-- #    priority::UInt16
-- #    @atomic _isexception::UInt8
-- #    @atomic preempt_request::UInt8
-- #    bound_cancel_default::UInt8
-- #    pad02::UInt8
-- #    rngState0::UInt64
-- #    rngState1::UInt64
-- #    rngState2::UInt64
-- #    rngState3::UInt64
-- #    rngState4::UInt64
-- #    const metrics_enabled::Bool
-- #    pad10::UInt8
-- #    pad11::UInt8
-- #    pad12::UInt8
-- #    @atomic first_enqueued_at::UInt64
-- #    @atomic last_started_running_at::UInt64
-- #    @atomic running_time_ns::UInt64
-- #    @atomic finished_at::UInt64
-- #    @atomic waiting_on::Any
-- #    cached_wait_entry::Any
-- #    cached_cancel_entry::Any
-- #    invoked::Any
-- #    @atomic bound_cancel_token::Union{Nothing, CancellationTokenSource}
-- #end
-- 
-- /Source

-- Reason: The export list, the aliases `getproperty`/`setproperty!` of the builtins `getfield`/`setfield!`, the abstract and primitive type declarations and the `UInt` alias are load-time definitions with no method.
-- UNTRANSLATED
-- Source: base/boot.jl:222-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- export
--     # key types
--     Any, TypeEq, Type, DataType, Vararg, NTuple,
--     Tuple, UnionAll, TypeVar, Union, Nothing, Cvoid,
--     AbstractArray, DenseArray, NamedTuple, Pair,
--     # special objects
--     Function, Method, Module, Symbol, Task, UndefInitializer, undef, WeakRef, VecElement,
--     Array, Memory, MemoryRef, AtomicMemory, AtomicMemoryRef, GenericMemory, GenericMemoryRef,
--     # numeric types
--     Number, Real, Integer, Bool, Ref, Ptr,
--     AbstractFloat, Float16, Float32, Float64,
--     Signed, Int, Int8, Int16, Int32, Int64, Int128,
--     Unsigned, UInt, UInt8, UInt16, UInt32, UInt64, UInt128,
--     # string types
--     AbstractChar, Char, AbstractString, String, IO,
--     # errors
--     ErrorException, BoundsError, DivideError, DomainError, Exception,
--     InterruptException, InexactError, OutOfMemoryError, ReadOnlyMemoryError,
--     OverflowError, StackOverflowError, SegmentationFault, UndefRefError, UndefVarError,
--     TypeError, ArgumentError, MethodError, AssertionError, LoadError, InitError,
--     UndefKeywordError, ConcurrencyViolationError, FieldError,
--     # AST representation
--     Expr, QuoteNode, LineNumberNode, GlobalRef,
--     # object model functions
--     fieldtype, getfield, setfield!, swapfield!, modifyfield!, replacefield!, setfieldonce!,
--     nfields, throw, tuple, ===, isdefined, bitsizeof,
--     # access to globals
--     getglobal, setglobal!, swapglobal!, modifyglobal!, replaceglobal!, setglobalonce!, isdefinedglobal,
--     # ifelse, sizeof    # not exported, to avoid conflicting with Base
--     # type reflection
--     <:, typeof, isa, typeassert,
--     # method reflection
--     applicable, invoke,
--     # constants
--     nothing, Main,
--     # backwards compatibility
--     arrayref, arrayset, arraysize, const_arrayref
-- 
-- const getproperty = getfield # TODO: use `getglobal` for modules instead
-- const setproperty! = setfield!
-- 
-- abstract type Number end
-- abstract type Real     <: Number end
-- abstract type AbstractFloat <: Real end
-- abstract type Integer  <: Real end
-- abstract type Signed   <: Integer end
-- abstract type Unsigned <: Integer end
-- 
-- primitive type Float16 <: AbstractFloat 16 end
-- primitive type Float32 <: AbstractFloat 32 end
-- primitive type Float64 <: AbstractFloat 64 end
-- 
-- primitive type BFloat16 <: AbstractFloat 16 end
-- 
-- #primitive type Bool <: Integer 8 end
-- abstract type AbstractChar end
-- primitive type Char <: AbstractChar 32 end
-- 
-- primitive type Int8    <: Signed   8 end
-- #primitive type UInt8   <: Unsigned 8 end
-- primitive type Int16   <: Signed   16 end
-- #primitive type UInt16  <: Unsigned 16 end
-- #primitive type Int32   <: Signed   32 end
-- #primitive type UInt32  <: Unsigned 32 end
-- #primitive type Int64   <: Signed   64 end
-- #primitive type UInt64  <: Unsigned 64 end
-- primitive type Int128  <: Signed   128 end
-- primitive type UInt128 <: Unsigned 128 end
-- 
-- if Int === Int64
--     const UInt = UInt64
-- else
--     const UInt = UInt32
-- end
-- 
-- /Source

/--
Julia source: base/boot.jl:297-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Typeof end
ccall(:jl_toplevel_eval_in, Any, (Any, Any),
      Core, quote
      (f::typeof(Typeof))(x) = begin
          $(_expr(:meta,:nospecialize,:x))
          if isa(x,Type)
              has_free_typevars(x) ? Type{x} : TypeEgal{x}
          else
              typeof(x)
          end
      end
      end)

```
-/
def Typeof (x : Value L) : CoreM W L (Value L) :=
  if ops.isa x (coreV ops "Type") then
    if ops.hasFreeTypevars x then ops.applyType (coreV ops "Type") [x]
    else ops.applyType (coreV ops "TypeEgal") [x]
  else pure (.leaf (ops.typeOf x))

/--
Julia source: base/boot.jl:310-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# like `Typeof`, but yields the equality kind `Type{x}` for type values; used
# by lowering to spell the callee self-type of method definitions, so equal
# UnionAll spellings share the constructor method they define
function TypeEqOf end
ccall(:jl_toplevel_eval_in, Any, (Any, Any),
      Core, quote
      (f::typeof(TypeEqOf))(x) = begin
          $(_expr(:meta,:nospecialize,:x))
          isa(x,Type) ? Type{x} : typeof(x)
      end
      end)

```
-/
def TypeEqOf (x : Value L) : CoreM W L (Value L) :=
  if ops.isa x (coreV ops "Type") then ops.applyType (coreV ops "Type") [x]
  else pure (.leaf (ops.typeOf x))

-- Reason: This declares the generic function `iterate` with no method.
-- UNTRANSLATED
-- Source: base/boot.jl:322-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate end
-- 
-- /Source

/--
Julia source: base/boot.jl:324-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro nospecialize(x)
    _expr(:escape, _expr(:meta, :nospecialize, x))
end
Expr(@nospecialize args...) = _expr(args...)

```
-/
def macro_nospecialize (x : Value L) : Value L :=
  .expr "escape" [.expr "meta" [.symbol "nospecialize", x]]

/-- The builtin `_expr(head, args...)`: `ArgumentError` without arguments and `TypeError` for a
head that is not a `Symbol`. -/
def _expr : List (Value L) → CoreM W L (Value L)
  | [] => throwObj ops (.argumentError (strV ops "Expr: too few arguments (expected 1)"))
  | .symbol head :: args => pure (.expr head args)
  | x :: _ => throwTypeError ops "Expr" "" (coreV ops "Symbol") x

def Expr_ (args : List (Value L)) : CoreM W L (Value L) := _expr ops args

/--
Julia source: base/boot.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro latestworld() Expr(:latestworld) end

```
-/
def macro_latestworld : Value L := .expr "latestworld" []

/--
Julia source: base/boot.jl:331-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_is_internal(__module__) = __module__ === Core
# can be used in place of `@assume_effects :total` (supposed to be used for bootstrapping)
macro _total_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#true,
        #=:effect_free=#true,
        #=:nothrow=#true,
        #=:terminates_globally=#true,
        #=:terminates_locally=#false,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#true,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#true))
end
```
-/
def _is_internal (mod : Value L) : Bool := ops.same mod (coreV ops "Core")

/-- `__module__` is the module of the macro call; a `false` result is the value `false`. -/
def macro__total_meta (mod : Value L) : Value L :=
  if _is_internal ops mod then
    purityMeta ops [true, true, true, true, false, true, true, true, false, false, true]
  else boolV ops false

/--
Julia source: base/boot.jl:347-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# can be used in place of `@assume_effects :foldable` (supposed to be used for bootstrapping)
macro _foldable_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#true,
        #=:effect_free=#true,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#false,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#true,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#true))
end

```
-/
def macro__foldable_meta (mod : Value L) : Value L :=
  if _is_internal ops mod then
    purityMeta ops [true, true, false, true, false, true, true, true, false, false, true]
  else boolV ops false

/--
Julia source: base/boot.jl:363-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro inline()      Expr(:meta, :inline)      end
macro noinline()    Expr(:meta, :noinline)    end
macro nospecializeinfer() Expr(:meta, :nospecializeinfer) end

macro _boundscheck() Expr(:boundscheck) end

```
-/
def macro_inline : Value L := .expr "meta" [.symbol "inline"]
def macro_noinline : Value L := .expr "meta" [.symbol "noinline"]
def macro_nospecializeinfer : Value L := .expr "meta" [.symbol "nospecializeinfer"]
def macro__boundscheck : Value L := .expr "boundscheck" []

/--
Julia source: base/boot.jl:369-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# n.b. the effects and model of these is refined in inference abstractinterpretation.jl
TypeVar(@nospecialize(n)) = _typevar(n::Symbol, Union{}, Any)
TypeVar(@nospecialize(n), @nospecialize(ub)) = _typevar(n::Symbol, Union{}, ub)
TypeVar(@nospecialize(n), @nospecialize(lb), @nospecialize(ub)) = _typevar(n::Symbol, lb, ub)
UnionAll(@nospecialize(v), @nospecialize(t)) = ccall(:jl_type_unionall, Any, (Any, Any), v::TypeVar, t)

```
-/
def TypeVar1 (n : Value L) : CoreM W L (Value L) := do
  ops.typevar (← assertSymbol ops n) (coreV ops "Union{}") (coreV ops "Any")
def TypeVar2 (n ub : Value L) : CoreM W L (Value L) := do
  ops.typevar (← assertSymbol ops n) (coreV ops "Union{}") ub
def TypeVar3 (n lb ub : Value L) : CoreM W L (Value L) := do
  ops.typevar (← assertSymbol ops n) lb ub
def UnionAll (v t : Value L) : CoreM W L (Value L) := do
  ops.typeUnionall (← typeassert ops v (coreV ops "TypeVar")) t

-- Reason: The type aliases `Memory` and `MemoryRef` are load-time definitions with no method.
-- UNTRANSLATED
-- Source: base/boot.jl:375-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const Memory{T} = GenericMemory{:not_atomic, T, CPU}
-- const MemoryRef{T} = GenericMemoryRef{:not_atomic, T, CPU}
-- 
-- /Source

/--
Julia source: base/boot.jl:378-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# simple convert for use by constructors of types in Core
# note that there is no actual conversion defined here,
# so the methods and ccall's in Core aren't permitted to use convert
convert(::Type{Any}, @nospecialize(x)) = x
convert(::Type{T}, x::T) where {T} = x
cconvert(::Type{T}, x) where {T} = convert(T, x)
unsafe_convert(::Type{T}, x::T) where {T} = x

```
-/
def convert_Any (x : Value L) : Value L := x
def convert_T (x : Value L) : Value L := x
def cconvert (T x : Value L) : CoreM W L (Value L) := ops.call (coreV ops "convert") [T, x]
def unsafe_convert (x : Value L) : Value L := x

/--
Julia source: base/boot.jl:386-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# will be inserted by the frontend for closures
_typeof_captured_variable(@nospecialize t) = (@_total_meta; t isa Type && has_free_typevars(t) ? typeof(t) : Typeof(t))

```
-/
def _typeof_captured_variable (t : Value L) : CoreM W L (Value L) :=
  if ops.isa t (coreV ops "Type") && ops.hasFreeTypevars t then pure (.leaf (ops.typeOf t))
  else Typeof ops t

/--
Julia source: base/boot.jl:389-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# dispatch token indicating a kwarg (keyword sorter) call
function kwcall end
# deprecated internal functions:
kwfunc(@nospecialize(f)) = kwcall
kwftype(@nospecialize(t)) = typeof(kwcall)

```
-/
def kwfunc (_f : Value L) : Value L := coreV ops "kwcall"
def kwftype (_t : Value L) : Value L := .leaf (ops.typeOf (coreV ops "kwcall"))

/--
Julia source: base/boot.jl:401-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# resolve_typegroup must be defined before any struct definition, since all structs
# are now lowered using the typegroup mechanism (for #60919 safety).
function resolve_typegroup(mod::Module, typevars::SimpleVector, struct_infos::SimpleVector, old_types::SimpleVector)
    n = _svec_len(typevars)
    if n === 0
        return ()
    end
    return ccall(:jl_resolve_typegroup, Any, (Any, Any, Any, Any), mod, typevars, struct_infos, old_types)
end

```
-/
def resolve_typegroup (mod typevars struct_infos old_types : Value L) : CoreM W L (Value L) :=
  let n := ops.svecLen typevars
  if n.val = 0 then pure (tupleV ops [])
  else ops.resolveTypegroup mod typevars struct_infos old_types

/--
Julia source: base/boot.jl:411-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# n.b. TypeApp and apply_type_or_typeapp must be defined before the first
# struct definition, whose lowered field-type thunks may call them.
# TypeApp: lazy type application for typegroup blocks.
# Represents a single type application step, like UnionAll represents a single where binding.
# T{P1, P2} is TypeApp(TypeApp(T, P1), P2) -- nested left-to-right.
# Allowed inside UnionAll; rejected by subtyping/intersection (like free typevars).
struct TypeApp
    head::Any            # Type constructor (TypeVar, Type, or outer TypeApp)
    param::Any           # Single type parameter
    function TypeApp(@nospecialize(head), @nospecialize(param))
        return new(head, param)
    end
end

```
-/
def TypeApp (head param : Value L) : Value L := objV ops (.typeApp head param)

/--
Julia source: base/boot.jl:425-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Check if a value contains a TypeApp anywhere in its structure
function _contains_typeapp(@nospecialize(x))
    if x isa TypeApp
        return true
    end
    if x isa UnionAll
        return _contains_typeapp(x.body)
    end
    return false
end

```
-/
def _contains_typeapp (x : Value L) : CoreM W L Bool := do
  if ops.isa x (coreV ops "TypeApp") then
    return true
  if ops.isa x (coreV ops "UnionAll") then
    return ← _contains_typeapp (← ops.getfield x (.symbol "body"))
  return false
partial_fixpoint

/--
Julia source: base/boot.jl:436-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function apply_type_or_typeapp(@nospecialize(tc), @nospecialize params...)
    # Head is TypeVar/TypeApp => must defer (apply_type requires UnionAll/DataType head)
    if tc isa TypeVar || tc isa TypeApp
        # Build nested TypeApp chain: TypeApp(TypeApp(tc, p1), p2), ...
        n = nfields(params)
        result = tc
        i = 1
        while Intrinsics.sle_int(i, n)
            result = TypeApp(result, getfield(params, i))
            i = Intrinsics.add_int(i, 1)
        end
        return result
    end
    # Any param contains TypeApp => must defer
    n = nfields(params)
    i = 1
    while Intrinsics.sle_int(i, n)
        if _contains_typeapp(getfield(params, i))
            # Build nested TypeApp chain for all params
            result = tc
            j = 1
            while Intrinsics.sle_int(j, n)
                result = TypeApp(result, getfield(params, j))
                j = Intrinsics.add_int(j, 1)
            end
            return result
        end
        i = Intrinsics.add_int(i, 1)
    end
    # All concrete -- real apply_type
    return apply_type(tc, params...)
end

```
-/
-- The `TypeApp(TypeApp(tc, p1), p2), ...` chain that both loops build.
def typeAppChain (tc : Value L) (params : List (Value L)) : Value L :=
  params.foldl (fun result p => TypeApp ops result p) tc

def apply_type_or_typeapp (tc : Value L) (params : List (Value L)) : CoreM W L (Value L) := do
  if ops.isa tc (coreV ops "TypeVar") || ops.isa tc (coreV ops "TypeApp") then
    return typeAppChain ops tc params
  for p in params do
    if ← _contains_typeapp ops p then
      return typeAppChain ops tc params
  ops.applyType tc params

-- Reason: The abstract type `Exception` defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:469-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abstract type Exception end
-- /Source

/--
Julia source: base/boot.jl:470-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct ErrorException <: Exception
    msg::AbstractString
    ErrorException(msg::AbstractString) = new(msg)
end

```
-/
def ErrorException (msg : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.errorException (← cf ops "ErrorException" "msg" msg)))

/--
Julia source: base/boot.jl:475-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct BoundsError <: Exception
    a::Any
    i::Any
    BoundsError() = new()
    BoundsError(@nospecialize(a)) = (@noinline; new(a))
    BoundsError(@nospecialize(a), i) = (@noinline; new(a,i))
end
```
-/
def BoundsError0 : Value L := objV ops (.boundsError none none)
def BoundsError1 (a : Value L) : Value L := objV ops (.boundsError (some a) none)
def BoundsError2 (a i : Value L) : Value L := objV ops (.boundsError (some a) (some i))

/--
Julia source: base/boot.jl:482-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DivideError         <: Exception
    DivideError() = new()
end
struct OutOfMemoryError    <: Exception
    OutOfMemoryError() = new()
end
struct ReadOnlyMemoryError <: Exception
    ReadOnlyMemoryError() = new()
end
struct SegmentationFault   <: Exception
    SegmentationFault() = new()
end
struct StackOverflowError  <: Exception
    StackOverflowError() = new()
end
struct UndefRefError       <: Exception
    UndefRefError() = new()
end
```
-/
def DivideError : Value L := objV ops .divideError
def OutOfMemoryError : Value L := objV ops .outOfMemoryError
def ReadOnlyMemoryError : Value L := objV ops .readOnlyMemoryError
def SegmentationFault : Value L := objV ops .segmentationFault
def StackOverflowError : Value L := objV ops .stackOverflowError
def UndefRefError : Value L := objV ops .undefRefError

/--
Julia source: base/boot.jl:500-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct UndefVarError <: Exception
    var::Symbol
    world::UInt
    scope # a Module or Symbol or other object describing the context where this variable was looked for (e.g. Main or :local or :static_parameter)
    UndefVarError(var::Symbol) = new(var, ccall(:jl_get_tls_world_age, UInt, ()))
    UndefVarError(var::Symbol, @nospecialize scope) = new(var, ccall(:jl_get_tls_world_age, UInt, ()), scope)
end
```
-/
def UndefVarError1 (var : Sym) : CoreM W L (Value L) := do
  let var ← cf ops "UndefVarError" "var" (.symbol var)
  let world ← cf ops "UndefVarError" "world" (intV ops (← ops.worldAge))
  pure (objV ops (.undefVarError var world none))
def UndefVarError2 (var : Sym) (scope : Value L) : CoreM W L (Value L) := do
  let var ← cf ops "UndefVarError" "var" (.symbol var)
  let world ← cf ops "UndefVarError" "world" (intV ops (← ops.worldAge))
  pure (objV ops (.undefVarError var world (some scope)))

/--
Julia source: base/boot.jl:507-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct ConcurrencyViolationError <: Exception
    msg::AbstractString
    ConcurrencyViolationError(msg::AbstractString) = new(msg)
end
```
-/
def ConcurrencyViolationError (msg : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.concurrencyViolationError (← cf ops "ConcurrencyViolationError" "msg" msg)))

/--
Julia source: base/boot.jl:511-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct MissingCodeError <: Exception
    mi::MethodInstance
    MissingCodeError(mi::MethodInstance) = new(mi)
end
```
-/
def MissingCodeError (mi : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.missingCodeError (← cf ops "MissingCodeError" "mi" mi)))

/--
Julia source: base/boot.jl:515-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct InterruptException <: Exception
    InterruptException() = new()
end
```
-/
def InterruptException : Value L := objV ops .interruptException

/--
Julia source: base/boot.jl:518-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DomainError <: Exception
    val
    msg::AbstractString
    DomainError(@nospecialize(val)) = (@noinline; new(val, ""))
    DomainError(@nospecialize(val), @nospecialize(msg)) = (@noinline; new(val, msg))
end
```
-/
def DomainError1 (val : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.domainError val (← cf ops "DomainError" "msg" (strV ops ""))))
def DomainError2 (val msg : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.domainError val (← cf ops "DomainError" "msg" msg)))

/--
Julia source: base/boot.jl:524-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct TypeError <: Exception
    # `func` is the name of the builtin function that encountered a type error,
    # the name of the type that hit an error in its definition or application, or
    # some other brief description of where the error happened.
    # `context` optionally adds extra detail, e.g. the name of the type parameter
    # that got a bad value.
    func::Symbol
    context::Union{AbstractString,GlobalRef,Symbol}
    expected::Type
    got
    TypeError(func, context, @nospecialize(expected::Type), @nospecialize(got)) =
        new(func, context, expected, got)
end
TypeError(where, @nospecialize(expected::Type), @nospecialize(got)) =
    TypeError(Symbol(where), "", expected, got)
```
-/
def TypeError4 (func context expected got : Value L) : CoreM W L (Value L) := do
  let func ← cf ops "TypeError" "func" func
  let context ← cf ops "TypeError" "context" context
  let expected ← cf ops "TypeError" "expected" expected
  pure (objV ops (.typeError func context expected got))
/-- `Symbol(where)` is a call of the generic function `Symbol`. -/
def TypeError3 (where_ expected got : Value L) : CoreM W L (Value L) := do
  TypeError4 ops (← ops.call (coreV ops "Symbol") [where_]) (strV ops "") expected got

/--
Julia source: base/boot.jl:539-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct InexactError <: Exception
    func::Symbol
    args
    InexactError(f::Symbol, @nospecialize(args...)) = (@noinline; new(f, args))
end
```
-/
def InexactError (f : Sym) (args : List (Value L)) : CoreM W L (Value L) := do
  pure (objV ops (.inexactError (← cf ops "InexactError" "func" (.symbol f)) (tupleV ops args)))

/--
Julia source: base/boot.jl:544-548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct OverflowError <: Exception
    msg::AbstractString
    OverflowError(msg::AbstractString) = new(msg)
end

```
-/
def OverflowError (msg : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.overflowError (← cf ops "OverflowError" "msg" msg)))

/--
Julia source: base/boot.jl:549-552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct ArgumentError <: Exception
    msg::AbstractString
    ArgumentError(msg::AbstractString) = new(msg)
end
```
-/
def ArgumentError (msg : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.argumentError (← cf ops "ArgumentError" "msg" msg)))

/-- `throw(ArgumentError(msg))` for a string literal `msg`. -/
def throwArgumentError {α : Type} (msg : String) : CoreM W L α := do
  throw (← ArgumentError ops (strV ops msg))

/--
Julia source: base/boot.jl:395-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Let the compiler assume that calling Union{} as a constructor does not need
# to be considered ever (which comes up often as Type{<:T} inference, and
# occasionally in user code from eltype).
Union{}(a...) = throw(ArgumentError("cannot construct a value of type Union{} for return result"))
kwcall(kwargs, ::Type{Union{}}, a...) = Union{}(a...)

```
-/
def Union_bottom {α : Type} (_a : List (Value L)) : CoreM W L α :=
  throwArgumentError ops "cannot construct a value of type Union{} for return result"
def kwcall_bottom {α : Type} (_kwargs : Value L) (a : List (Value L)) : CoreM W L α :=
  Union_bottom ops a

/--
Julia source: base/boot.jl:553-557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct UndefKeywordError <: Exception
    var::Symbol
    UndefKeywordError(var::Symbol) = new(var)
end

```
-/
def UndefKeywordError (var : Sym) : CoreM W L (Value L) := do
  pure (objV ops (.undefKeywordError (← cf ops "UndefKeywordError" "var" (.symbol var))))

/--
Julia source: base/boot.jl:558-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const typemax_UInt = Intrinsics.sext_int(UInt, 0xFF)
const typemax_Int = Core.Intrinsics.udiv_int(Core.Intrinsics.sext_int(Int, 0xFF), 2)

```
-/
def typemax_UInt : U64 := sext_int .u64 (JInt.lit .u8 0xFF) (by decide)
def typemax_Int : I64 :=
  C.toJInt .i64 (JuliaLean.base.int.okOf (C.jlUdivInt (C.fromJInt (sext_int .i64 (JInt.lit .u8 0xFF) (by decide)))
    (C.fromJInt (JInt.lit .i64 2))) (by
      intro e h
      have h2 : (C.fromJInt (JInt.lit IntTy.i64 2)).toNat = 2 := by decide
      simp [C.jlUdivInt, C.integerDivide, h2, pure, Except.pure] at h))

/--
Julia source: base/boot.jl:561-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct MethodError <: Exception
    f
    args
    world::UInt
    MethodError(@nospecialize(f), @nospecialize(args), world::UInt) = new(f, args, world)
end
MethodError(@nospecialize(f), @nospecialize(args)) = MethodError(f, args, typemax_UInt)

```
-/
def MethodError3 (f args : Value L) (world : U64) : CoreM W L (Value L) := do
  pure (objV ops (.methodError f args (← cf ops "MethodError" "world" (intV ops world))))
def MethodError2 (f args : Value L) : CoreM W L (Value L) := MethodError3 ops f args typemax_UInt

/--
Julia source: base/boot.jl:569-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct AssertionError <: Exception
    msg::AbstractString
    AssertionError(msg::AbstractString) = (@noinline; new(msg))
end
AssertionError() = (@noinline; AssertionError(""))

```
-/
def AssertionError1 (msg : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.assertionError (← cf ops "AssertionError" "msg" msg)))
def AssertionError0 : CoreM W L (Value L) := AssertionError1 ops (strV ops "")

/--
Julia source: base/boot.jl:575-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct FieldError <: Exception
    type::DataType
    field::Symbol
    FieldError(type::DataType, field::Symbol) = new(type, field)
end

```
-/
def FieldError (type : Value L) (field : Sym) : CoreM W L (Value L) := do
  let type ← cf ops "FieldError" "type" type
  pure (objV ops (.fieldError type (← cf ops "FieldError" "field" (.symbol field))))

-- Reason: The abstract type `WrappedException` defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:581-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abstract type WrappedException <: Exception end
-- 
-- /Source

/--
Julia source: base/boot.jl:583-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct LoadError <: WrappedException
    file::AbstractString
    line::Int
    error
    LoadError(file::AbstractString, line::Int, @nospecialize(error)) = new(file, line, error)
end

```
-/
def LoadError (file : Value L) (line : I64) (error : Value L) : CoreM W L (Value L) := do
  let file ← cf ops "LoadError" "file" file
  pure (objV ops (.loadError file (← cf ops "LoadError" "line" (intV ops line)) error))

/--
Julia source: base/boot.jl:590-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct InitError <: WrappedException
    mod::Symbol
    error
    InitError(mod::Symbol, @nospecialize(error)) = new(mod, error)
end

```
-/
def InitError (mod : Sym) (error : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.initError (← cf ops "InitError" "mod" (.symbol mod)) error))

/--
Julia source: base/boot.jl:596-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct ABIOverride
    abi::Type
    def::MethodInstance
    ABIOverride(@nospecialize(abi::Type), def::MethodInstance) = new(abi, def)
end

```
-/
def ABIOverride (abi def_ : Value L) : CoreM W L (Value L) := do
  let abi ← cf ops "ABIOverride" "abi" abi
  pure (objV ops (.abiOverride abi (← cf ops "ABIOverride" "def" def_)))

/--
Julia source: base/boot.jl:602-604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PrecompilableError <: Exception
    PrecompilableError() = new()
end
```
-/
def PrecompilableError : Value L := objV ops .precompilableError

/--
Julia source: base/boot.jl:605-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct TrimFailure <: Exception
    TrimFailure() = new()
end
```
-/
def TrimFailure : Value L := objV ops .trimFailure

-- Reason: The abstract type `LazyLibraryCallback` defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:608-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # `Libdl.LazyLibraryCallback`, defined here to be visible to the compiler
-- abstract type LazyLibraryCallback end
-- 
-- /Source

/--
Julia source: base/boot.jl:611-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
String(s::String) = s  # no constructor yet

```
-/
def String_String (s : Value L) : Value L := s

-- Reason: The alias `Cvoid` of `Nothing` defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:613-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const Cvoid = Nothing
-- /Source

/--
Julia source: base/boot.jl:614-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Nothing() = nothing

```
-/
def Nothing_ : Value L := nothingV ops

/--
Julia source: base/boot.jl:616-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This should always be inlined
getptls() = ccall(:jl_get_ptls_states, Ptr{Cvoid}, ())

```
-/
def getptls : CoreM W L (Value L) := ops.getptls

/--
Julia source: base/boot.jl:619-621 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
include(m::Module, fname::String) = (@noinline; ccall(:jl_load_, Any, (Any, Any), m, fname))
eval(m::Module, @nospecialize(e)) = (@noinline; ccall(:jl_toplevel_eval_in, Any, (Any, Any), m, e))

```
-/
def include_ (m fname : Value L) : CoreM W L (Value L) := ops.load m fname
def eval (m e : Value L) : CoreM W L (Value L) := ops.toplevelEval m e

/--
Julia source: base/boot.jl:622-627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct EvalInto <: Function
    m::Module
    EvalInto(m::Module) = new(m)
end
(this::EvalInto)(@nospecialize(e)) = eval(this.m, e)

```
-/
def EvalInto (m : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.evalInto (← cf ops "EvalInto" "m" m)))
/-- `(this::EvalInto)(e)`; `this.m` is `getfield(this, :m)`. -/
def EvalInto_call (this e : Value L) : CoreM W L (Value L) := do
  eval ops (← ops.getfield this (.symbol "m")) e

/--
Julia source: base/boot.jl:628-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct Box
    contents::Any
    Box(@nospecialize(x)) = new(x)
    Box() = new()
end

```
-/
def Box1 (x : Value L) : CoreM W L (Value L) := ops.newBox (some x)
def Box0 : CoreM W L (Value L) := ops.newBox none

/--
Julia source: base/boot.jl:634-642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# constructors for built-in types

mutable struct WeakRef
    value
    WeakRef() = WeakRef(nothing)
    WeakRef(@nospecialize(v)) = ccall(:jl_gc_new_weakref_th, Ref{WeakRef},
                                      (Ptr{Cvoid}, Any), getptls(), v)
end

```
-/
def WeakRef1 (v : Value L) : CoreM W L (Value L) := do ops.newWeakref (← getptls ops) v
def WeakRef0 : CoreM W L (Value L) := WeakRef1 ops (nothingV ops)

/--
Julia source: base/boot.jl:643-644 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Tuple{}() = ()

```
-/
def Tuple_empty : Value L := tupleV ops []

/--
Julia source: base/boot.jl:645-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct VecElement{T}
    value::T
    VecElement{T}(value::T) where {T} = new(value) # disable converting constructor in Core
end
VecElement(arg::T) where {T} = VecElement{T}(arg)

```
-/
-- `VecElement{T}(value)`; `self` is the type `VecElement{T}`.
def VecElement_T (T value : Value L) : CoreM W L (Value L) := do
  let self ← ops.applyType (coreV ops "VecElement") [T]
  pure (objV ops (.vecElement T (← convertField ops self "value" value)))
def VecElement (arg : Value L) : CoreM W L (Value L) := VecElement_T ops (.leaf (ops.typeOf arg)) arg

/--
Julia source: base/boot.jl:651-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# inference lattice element types (moved from jltypes.c)
struct Const
    val
    Const(@nospecialize(v)) = new(v)
end

```
-/
def Const (v : Value L) : Value L := objV ops (.const v)

/--
Julia source: base/boot.jl:657-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PartialStruct
    typ
    undefs::Array{Union{Nothing,Bool}, 1}
    fields::Array{Any, 1}
    # N.B. The constructor for this struct is intentionally not defined here.
    # It is defined in coreir.jl along with some validation logic.
    global _PartialStruct
    _PartialStruct(@nospecialize(typ), undef::Array{Union{Nothing,Bool}, 1}, fields::Array{Any, 1}) = new(typ, undef, fields)
end

```
-/
def _PartialStruct (typ undef fields : Value L) : CoreM W L (Value L) := do
  let undef ← cf ops "PartialStruct" "undefs" undef
  pure (objV ops (.partialStruct typ undef (← cf ops "PartialStruct" "fields" fields)))

/--
Julia source: base/boot.jl:667-673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct InterConditional
    slot::Int
    thentype
    elsetype
    InterConditional(slot::Int, @nospecialize(thentype), @nospecialize(elsetype)) = new(slot, thentype, elsetype)
end

```
-/
def InterConditional (slot : I64) (thentype elsetype : Value L) : CoreM W L (Value L) := do
  pure (objV ops (.interConditional (← cf ops "InterConditional" "slot" (intV ops slot)) thentype elsetype))

/--
Julia source: base/boot.jl:674-681 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct InterMustAlias
    slot::Int
    vartyp::Any
    fldidx::Int
    fldtyp::Any
    InterMustAlias(slot::Int, @nospecialize(vartyp), fldidx::Int, @nospecialize(fldtyp)) = new(slot, vartyp, fldidx, fldtyp)
end

```
-/
def InterMustAlias (slot : I64) (vartyp : Value L) (fldidx : I64) (fldtyp : Value L) :
    CoreM W L (Value L) := do
  let slot ← cf ops "InterMustAlias" "slot" (intV ops slot)
  let fldidx ← cf ops "InterMustAlias" "fldidx" (intV ops fldidx)
  pure (objV ops (.interMustAlias slot vartyp fldidx fldtyp))

/--
Julia source: base/boot.jl:682-689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PartialOpaque
    typ::Type
    env
    parent::MethodInstance
    source
    PartialOpaque(@nospecialize(typ::Type), @nospecialize(env), parent::MethodInstance, source) = new(typ, env, parent, source)
end

```
-/
def PartialOpaque (typ env parent source : Value L) : CoreM W L (Value L) := do
  let typ ← cf ops "PartialOpaque" "typ" typ
  let parent ← cf ops "PartialOpaque" "parent" parent
  pure (objV ops (.partialOpaque typ env parent source))

/--
Julia source: base/boot.jl:690-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PartialTask
    fetch_type
    PartialTask(@nospecialize(fetch_type)) = new(fetch_type)
end

```
-/
def PartialTask (fetch_type : Value L) : Value L := objV ops (.partialTask fetch_type)

/--
Julia source: base/boot.jl:695-698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PossiblyAmbiguous
    PossiblyAmbiguous() = new()
end

```
-/
def PossiblyAmbiguous : Value L := objV ops .possiblyAmbiguous

/--
Julia source: base/boot.jl:730-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct LineInfoNode # legacy support for aiding Serializer.deserialize of old IR
    mod::Module
    method
    file::Symbol
    line::Int32
    inlined_at::Int32
    LineInfoNode(mod::Module, @nospecialize(method), file::Symbol, line::Int32, inlined_at::Int32) = new(mod, method, file, line, inlined_at)
end


```
-/
def LineInfoNode (mod method : Value L) (file : Sym) (line inlined_at : I32) :
    CoreM W L (Value L) := do
  let mod ← cf ops "LineInfoNode" "mod" mod
  let file ← cf ops "LineInfoNode" "file" (.symbol file)
  let line ← cf ops "LineInfoNode" "line" (intV ops line)
  let inlined_at ← cf ops "LineInfoNode" "inlined_at" (intV ops inlined_at)
  pure (objV ops (.lineInfoNode mod method file line inlined_at))

/--
Julia source: base/boot.jl:740-749 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function CodeInstance(
    mi::Union{MethodInstance, ABIOverride}, owner, @nospecialize(rettype), @nospecialize(exctype), @nospecialize(inferred_const),
    @nospecialize(inferred), const_flags::Int32, min_world::UInt, max_world::UInt,
    effects::UInt32, @nospecialize(analysis_results),
    di::Union{DebugInfo,Nothing}, edges::SimpleVector)
    return ccall(:jl_new_codeinst, Ref{CodeInstance},
        (Any, Any, Any, Any, Any, Any, Int32, UInt, UInt, UInt32, Any, Any, Any),
        mi, owner, rettype, exctype, inferred_const, inferred, const_flags, min_world, max_world,
        effects, analysis_results, di, edges)
end
```
-/
def CodeInstance (mi owner rettype exctype inferred_const inferred : Value L) (const_flags : I32)
    (min_world max_world : U64) (effects : JInt .u32) (analysis_results di edges : Value L) :
    CoreM W L (Value L) :=
  ops.newCodeinst [mi, owner, rettype, exctype, inferred_const, inferred, intV ops const_flags,
    intV ops min_world, intV ops max_world, intV ops effects, analysis_results, di, edges]

/--
Julia source: base/boot.jl:750-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
GlobalRef(m::Module, s::Symbol) = ccall(:jl_module_globalref, Ref{GlobalRef}, (Any, Any), m, s)
```
-/
def GlobalRef (m : Value L) (s : Sym) : CoreM W L (Value L) := ops.moduleGlobalref m s

/--
Julia source: base/boot.jl:751-752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Module(name::Symbol=:anonymous, std_imports::Bool=true, default_names::Bool=true) = ccall(:jl_f_new_module, Ref{Module}, (Any, Bool, Bool), name, std_imports, default_names)

```
-/
def Module3 (name : Sym) (std_imports default_names : Bool) : CoreM W L (Value L) :=
  ops.newModule name std_imports default_names
def Module2 (name : Sym) (std_imports : Bool) : CoreM W L (Value L) := Module3 ops name std_imports true
def Module1 (name : Sym) : CoreM W L (Value L) := Module3 ops name true true
def Module0 : CoreM W L (Value L) := Module3 ops "anonymous" true true

-- Reason: The type alias `NTuple` defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:753-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const NTuple{N,T} = Tuple{Vararg{T,N}}
-- 
-- /Source

/--
Julia source: base/boot.jl:755-760 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## primitive Array constructors
struct UndefInitializer
    UndefInitializer() = new()
end
const undef = UndefInitializer()

```
-/
def UndefInitializer : Value L := objV ops .undefInitializer
def undef : Value L := UndefInitializer ops

/--
Julia source: base/boot.jl:761-766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# type and dimensionality specified
(self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind} = memorynew(self, m)
(self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, d::NTuple{1,Int}) where {T,kind,addrspace} = self(undef, getfield(d,1))
# empty vector constructor
(self::Type{GenericMemory{kind,T,addrspace}})() where {T,kind,addrspace} = self(undef, 0)

```
-/
-- `self` is the type `GenericMemory{kind,T,addrspace}`.
def GenericMemory_undef (self : Value L) (m : I64) : CoreM W L (Value L) := ops.memorynew self m
def GenericMemory_undef_tuple (self : Value L) (d : I64) : CoreM W L (Value L) :=
  GenericMemory_undef ops self d
def GenericMemory_empty (self : Value L) : CoreM W L (Value L) :=
  GenericMemory_undef ops self (JInt.lit .i64 0)

/--
Julia source: base/boot.jl:767-774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# memoryref is simply convenience wrapper function around memoryrefnew
memoryref(mem::GenericMemory) = memoryrefnew(mem)
memoryref(mem::GenericMemory, i::Integer) = memoryrefnew(mem, Int(i), @_boundscheck)
memoryref(ref::GenericMemoryRef, i::Integer) = memoryrefnew(ref, Int(i), @_boundscheck)
GenericMemoryRef(mem::GenericMemory) = memoryref(mem)
GenericMemoryRef(mem::GenericMemory, i::Integer) = memoryref(mem, i)
GenericMemoryRef(mem::GenericMemoryRef, i::Integer) = memoryref(mem, i)

```
-/
def memoryref1 (mem : Value L) : CoreM W L (Value L) := ops.memoryrefnew mem
/-- `boundscheck` is the value of `@_boundscheck` at the call: `true` outside `@inbounds`.
`Int(i)` is a call of the generic function `Int`. -/
def memoryref2 (mem i : Value L) (boundscheck : Bool) : CoreM W L (Value L) := do
  ops.memoryrefnewIndex mem (← ops.call (coreV ops "Int64") [i]) boundscheck
def memoryref_ref (ref i : Value L) (boundscheck : Bool) : CoreM W L (Value L) := do
  ops.memoryrefnewIndex ref (← ops.call (coreV ops "Int64") [i]) boundscheck
def GenericMemoryRef1 (mem : Value L) : CoreM W L (Value L) := memoryref1 ops mem
def GenericMemoryRef2 (mem i : Value L) (boundscheck : Bool) : CoreM W L (Value L) :=
  memoryref2 ops mem i boundscheck
def GenericMemoryRef_ref (ref i : Value L) (boundscheck : Bool) : CoreM W L (Value L) :=
  memoryref_ref ops ref i boundscheck

-- Reason: The type aliases `AtomicMemory` and `AtomicMemoryRef` define no method.
-- UNTRANSLATED
-- Source: base/boot.jl:775-777 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const AtomicMemory{T} = GenericMemory{:atomic, T, CPU}
-- const AtomicMemoryRef{T} = GenericMemoryRef{:atomic, T, CPU}
-- 
-- /Source

/--
Julia source: base/boot.jl:778-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# construction helpers for Array
new_as_memoryref(self::Type{GenericMemoryRef{kind,T,addrspace}}, m::Int) where {T,kind,addrspace} = memoryref(fieldtype(self, :mem)(undef, m))

```
-/
def new_as_memoryref (self : Value L) (m : I64) : CoreM W L (Value L) := do
  memoryref1 ops (← GenericMemory_undef ops (← ops.fieldtype self "mem") m)

/--
Julia source: base/boot.jl:781-810 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# checked-multiply intrinsic function for dimensions
_checked_mul_dims() = 1, false
_checked_mul_dims(m::Int) = m, Intrinsics.ule_int(typemax_Int, m) # equivalently: (m + 1) < 1
function _checked_mul_dims(m::Int, n::Int)
    b = Intrinsics.checked_smul_int(m, n)
    a = getfield(b, 1)
    ovflw = getfield(b, 2)
    ovflw = Intrinsics.or_int(ovflw, Intrinsics.ule_int(typemax_Int, m))
    ovflw = Intrinsics.or_int(ovflw, Intrinsics.ule_int(typemax_Int, n))
    return a, ovflw
end
function _checked_mul_dims(m::Int, d::Int...)
    @_foldable_meta # the compiler needs to know this loop terminates
    a = m
    i = 1
    ovflw = false
    neg = Intrinsics.ule_int(typemax_Int, m)
    zero = false # if m==0 we won't have overflow since we go left to right
    while Intrinsics.sle_int(i, nfields(d))
        di = getfield(d, i)
        b = Intrinsics.checked_smul_int(a, di)
        zero = Intrinsics.or_int(zero, di === 0)
        ovflw = Intrinsics.or_int(ovflw, getfield(b, 2))
        neg = Intrinsics.or_int(neg, Intrinsics.ule_int(typemax_Int, di))
        a = getfield(b, 1)
        i = Intrinsics.add_int(i, 1)
   end
   return a, Intrinsics.or_int(neg, Intrinsics.and_int(ovflw, Intrinsics.not_int(zero)))
end

```
-/
def _checked_mul_dims0 : I64 × Bool := (JInt.lit .i64 1, false)
def _checked_mul_dims1 (m : I64) : I64 × Bool := (m, ule_int typemax_Int m)

/-- The intrinsic `checked_smul_int(a, b)`: the wrapped product and whether it overflowed. -/
def checked_smul_int (a b : I64) : I64 × Bool :=
  let r := C.jlCheckedSmulInt (C.fromJInt a) (C.fromJInt b)
  (C.toJInt .i64 r.1, r.2)

def _checked_mul_dims2 (m n : I64) : I64 × Bool :=
  let b := checked_smul_int m n
  let a := b.1
  let ovflw := b.2
  let ovflw := ovflw || ule_int typemax_Int m
  let ovflw := ovflw || ule_int typemax_Int n
  (a, ovflw)

/-- The `while` loop of `_checked_mul_dims(m, d...)` over the remaining `d`, from the state
`(a, ovflw, neg, zero)`. -/
def _checked_mul_dims_loop : I64 → Bool → Bool → Bool → List I64 → I64 × Bool × Bool × Bool
  | a, ovflw, neg, zero, [] => (a, ovflw, neg, zero)
  | a, ovflw, neg, zero, di :: d =>
    let b := checked_smul_int a di
    let zero := zero || di.val == 0
    let ovflw := ovflw || b.2
    let neg := neg || ule_int typemax_Int di
    _checked_mul_dims_loop b.1 ovflw neg zero d

def _checked_mul_dimsN (m : I64) (d : List I64) : I64 × Bool :=
  let (a, ovflw, neg, zero) := _checked_mul_dims_loop m false (ule_int typemax_Int m) false d
  (a, neg || (ovflw && !zero))

/-- The method of `_checked_mul_dims(d...)` that dispatch selects for `length(d)` arguments. -/
def checkedMulDims : List I64 → I64 × Bool
  | [] => _checked_mul_dims0
  | [m] => _checked_mul_dims1 m
  | [m, n] => _checked_mul_dims2 m n
  | m :: d => _checked_mul_dimsN m d

/--
Julia source: base/boot.jl:811-819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# convert a set of dims to a length, with overflow checking
checked_dims() = 1
checked_dims(m::Int) = m # defer this check to Memory constructor instead
function checked_dims(d::Int...)
    b = _checked_mul_dims(d...)
    getfield(b, 2) && throw(ArgumentError("invalid Array dimensions"))
    return getfield(b, 1)
end

```
-/
def checked_dims0 : I64 := JInt.lit .i64 1
def checked_dims1 (m : I64) : I64 := m
def checked_dimsN (d : List I64) : CoreM W L I64 := do
  let b := checkedMulDims d
  if b.2 then throwArgumentError ops "invalid Array dimensions"
  pure b.1

/-- The method of `checked_dims(d...)` that dispatch selects for `length(d)` arguments. -/
def checkedDims : List I64 → CoreM W L I64
  | [] => pure checked_dims0
  | [m] => pure (checked_dims1 m)
  | d => checked_dimsN ops d

/--
Julia source: base/boot.jl:820-848 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# type and dimensionality specified, accepting dims as series of Ints
eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
    mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
    return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
end))
eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
    return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
end))
eval(Core, :(function (self::Type{Array{T,3}})(::UndefInitializer, m::Int, n::Int, o::Int) where {T}
    return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n, o))), :((m, n, o))))
end))
eval(Core, :(function (self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}
    return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(d...))), :d))
end))
# type and dimensionality specified, accepting dims as tuples of Ints
(self::Type{Array{T,1}})(::UndefInitializer, d::NTuple{1, Int}) where {T} = self(undef, getfield(d, 1))
(self::Type{Array{T,2}})(::UndefInitializer, d::NTuple{2, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2))
(self::Type{Array{T,3}})(::UndefInitializer, d::NTuple{3, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2), getfield(d, 3))
(self::Type{Array{T,N}})(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = self(undef, d...)
# type but not dimensionality specified
Array{T}(::UndefInitializer, m::Int) where {T} = Array{T, 1}(undef, m)
Array{T}(::UndefInitializer, m::Int, n::Int) where {T} = Array{T, 2}(undef, m, n)
Array{T}(::UndefInitializer, m::Int, n::Int, o::Int) where {T} = Array{T, 3}(undef, m, n, o)
# Guard against invalidations due to spurious `Tuple{}` intersections
Array{T}(::UndefInitializer, ::Tuple{}) where {T} = Array{T, 0}(undef)
Array{T}(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = Array{T, N}(undef, d)
# empty vector constructor
(self::Type{Array{T, 1}})() where {T} = self(undef, 0)

```
-/
-- `self` is the type `Array{T,N}`; `Expr(:new, :self, ref, dims)` is the builtin `new`.
def Array_1 (self : Value L) (m : I64) : CoreM W L (Value L) := do
  let mem ← GenericMemory_undef ops (← ops.fieldtype (← ops.fieldtype self "ref") "mem") m
  ops.new self [← memoryref1 ops mem, tupleV ops [intV ops m]]
def Array_2 (self : Value L) (m n : I64) : CoreM W L (Value L) := do
  let ref ← new_as_memoryref ops (← ops.fieldtype self "ref") (← checked_dimsN ops [m, n])
  ops.new self [ref, tupleV ops [intV ops m, intV ops n]]
def Array_3 (self : Value L) (m n o : I64) : CoreM W L (Value L) := do
  let ref ← new_as_memoryref ops (← ops.fieldtype self "ref") (← checked_dimsN ops [m, n, o])
  ops.new self [ref, tupleV ops [intV ops m, intV ops n, intV ops o]]
def Array_N (self : Value L) (d : List I64) : CoreM W L (Value L) := do
  let ref ← new_as_memoryref ops (← ops.fieldtype self "ref") (← checkedDims ops d)
  ops.new self [ref, tupleV ops (d.map (intV ops))]

/-- `self(undef, d...)` for `self = Array{T,N}`: the method dispatch selects for `N = length(d)`. -/
def arrayUndef (self : Value L) : List I64 → CoreM W L (Value L)
  | [m] => Array_1 ops self m
  | [m, n] => Array_2 ops self m n
  | [m, n, o] => Array_3 ops self m n o
  | d => Array_N ops self d

def Array_1_tuple (self : Value L) (d : I64) : CoreM W L (Value L) := Array_1 ops self d
def Array_2_tuple (self : Value L) (d1 d2 : I64) : CoreM W L (Value L) := Array_2 ops self d1 d2
def Array_3_tuple (self : Value L) (d1 d2 d3 : I64) : CoreM W L (Value L) :=
  Array_3 ops self d1 d2 d3
def Array_N_tuple (self : Value L) (d : List I64) : CoreM W L (Value L) := arrayUndef ops self d

/-- `Array{T, N}` as a type value. -/
def arrayType (T : Value L) (N : Nat) : CoreM W L (Value L) :=
  ops.applyType (coreV ops "Array") [T, intV ops (JInt.lit .i64 N)]

def Array_T_1 (T : Value L) (m : I64) : CoreM W L (Value L) := do
  Array_1 ops (← arrayType ops T 1) m
def Array_T_2 (T : Value L) (m n : I64) : CoreM W L (Value L) := do
  Array_2 ops (← arrayType ops T 2) m n
def Array_T_3 (T : Value L) (m n o : I64) : CoreM W L (Value L) := do
  Array_3 ops (← arrayType ops T 3) m n o
def Array_T_empty_tuple (T : Value L) : CoreM W L (Value L) := do
  arrayUndef ops (← arrayType ops T 0) []
def Array_T_tuple (T : Value L) (d : List I64) : CoreM W L (Value L) := do
  Array_N_tuple ops (← arrayType ops T d.length) d
def Array_1_empty (self : Value L) : CoreM W L (Value L) := Array_1 ops self (JInt.lit .i64 0)

/--
Julia source: base/boot.jl:849-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(Array{T, N} where T)(x::AbstractArray{S, N}) where {S, N} = Array{S, N}(x)

Array(A::AbstractArray{T, N})    where {T, N}   = Array{T, N}(A)
Array{T}(A::AbstractArray{S, N}) where {T, N, S} = Array{T, N}(A)

AbstractArray{T}(A::AbstractArray{S, N}) where {T, S, N} = AbstractArray{T, N}(A)

```
-/
-- `S`, `T` and `N` are the static parameters of the method; the conversion constructors that are
-- called are defined outside this file.
def Array_where_T (S N x : Value L) : CoreM W L (Value L) := do
  ops.call (← ops.applyType (coreV ops "Array") [S, N]) [x]
def Array_A (T N A : Value L) : CoreM W L (Value L) := do
  ops.call (← ops.applyType (coreV ops "Array") [T, N]) [A]
def Array_T_A (T N A : Value L) : CoreM W L (Value L) := do
  ops.call (← ops.applyType (coreV ops "Array") [T, N]) [A]
def AbstractArray_T_A (T N A : Value L) : CoreM W L (Value L) := do
  ops.call (← ops.applyType (coreV ops "AbstractArray") [T, N]) [A]

/--
Julia source: base/boot.jl:856-874 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# primitive Symbol constructors

## Helper for proper GC rooting without unsafe_convert
eval(Core, quote
    _Symbol(ptr::Ptr{UInt8}, sz::Int, root::Any) = $(Expr(:foreigncall, QuoteNode(:jl_symbol_n),
        Ref{Symbol}, svec(Ptr{UInt8}, Int), 0, QuoteNode(:ccall), :ptr, :sz, :root))
end)

function Symbol(s::String)
    @_foldable_meta
    @noinline
    return _Symbol(ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s), sizeof(s), s)
end
function Symbol(a::Array{UInt8, 1})
    @noinline
    return _Symbol(bitcast(Ptr{UInt8}, a.ref.ptr_or_offset), getfield(a.size, 1), a.ref.mem)
end
Symbol(s::Symbol) = s

```
-/
-- `_Symbol(ptr, sz, root)` is given the `sz` bytes at `ptr`; `jl_symbol_n` rejects a zero byte.
def _Symbol (bytes : List U8) : CoreM W L Sym :=
  if bytes.any (fun b => b.val == 0) then
    throwObj ops (.argumentError (strV ops "Symbol name may not contain \\0"))
  else pure (ops.symbolName bytes)
def Symbol_String (s : Value L) : CoreM W L Sym := _Symbol ops (ops.stringBytes s)
def Symbol_Array (a : Value L) : CoreM W L Sym := do _Symbol ops (← ops.vectorBytes a)
def Symbol_Symbol (s : Sym) : Sym := s

/--
Julia source: base/boot.jl:699-727 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eval(Core, quote
    GotoNode(label::Int) = $(Expr(:new, :GotoNode, :label))
    NewvarNode(slot::SlotNumber) = $(Expr(:new, :NewvarNode, :slot))
    QuoteNode(@nospecialize value) = $(Expr(:new, :QuoteNode, :value))
    SSAValue(id::Int) = $(Expr(:new, :SSAValue, :id))
    Argument(n::Int) = $(Expr(:new, :Argument, :n))
    ReturnNode(@nospecialize val) = $(Expr(:new, :ReturnNode, :val))
    ReturnNode() = $(Expr(:new, :ReturnNode)) # unassigned val indicates unreachable
    GotoIfNot(@nospecialize(cond), dest::Int) = $(Expr(:new, :GotoIfNot, :cond, :dest))
    EnterNode(dest::Int) = $(Expr(:new, :EnterNode, :dest))
    EnterNode(dest::Int, @nospecialize(scope)) = $(Expr(:new, :EnterNode, :dest, :scope))
    LineNumberNode(l::Int) = $(Expr(:new, :LineNumberNode, :l, nothing))
    function LineNumberNode(l::Int, @nospecialize(f))
        isa(f, String) && (f = Symbol(f))
        return $(Expr(:new, :LineNumberNode, :l, :f))
    end
    DebugInfo(def::Union{Method,MethodInstance,Symbol}, linetable::Union{Nothing,DebugInfo,String}, edges::SimpleVector, codelocs::String) =
        $(Expr(:new, :DebugInfo, :def, :linetable, :edges, :codelocs))
    DebugInfo(def::Union{Method,MethodInstance,Symbol}) =
        $(Expr(:new, :DebugInfo, :def, nothing, Core.svec(), ""))
    SlotNumber(n::Int) = $(Expr(:new, :SlotNumber, :n))
    PhiNode(edges::Array{Int32, 1}, values::Array{Any, 1}) = $(Expr(:new, :PhiNode, :edges, :values))
    PiNode(@nospecialize(val), @nospecialize(typ)) = $(Expr(:new, :PiNode, :val, :typ))
    PhiCNode(values::Array{Any, 1}) = $(Expr(:new, :PhiCNode, :values))
    UpsilonNode(@nospecialize(val)) = $(Expr(:new, :UpsilonNode, :val))
    UpsilonNode() = $(Expr(:new, :UpsilonNode))
    MethodMatch(@nospecialize(spec_types), sparams::SimpleVector, method::Method, fully_covers::Bool) = $(Expr(:new, :MethodMatch, :spec_types, :sparams, :method, :fully_covers))
end)

```
-/
def GotoNode (label : I64) : Value L := .gotoNode label
def NewvarNode (slot : Value L) : Value L := .newvarNode slot
def QuoteNode (value : Value L) : Value L := .quoteNode value
def SSAValue (id : I64) : Value L := .ssaValue id
def Argument (n : I64) : Value L := .argument n
def ReturnNode1 (val : Value L) : Value L := .returnNode (some val)
def ReturnNode0 : Value L := .returnNode none
def GotoIfNot (cond : Value L) (dest : I64) : Value L := .gotoIfNot cond dest
def EnterNode1 (dest : I64) : Value L := .enterNode dest none
def EnterNode2 (dest : I64) (scope : Value L) : Value L := .enterNode dest (some scope)
def LineNumberNode1 (l : I64) : Value L := .lineNumberNode l (nothingV ops)
/-- The raw `new` checks that `file` has the field type `Union{Nothing, Symbol}`. -/
def LineNumberNode2 (l : I64) (f : Value L) : CoreM W L (Value L) := do
  let f ← if ops.isa f (coreV ops "String") then do pure (.symbol (← Symbol_String ops f))
    else pure f
  match f with
  | .symbol _ => pure (.lineNumberNode l f)
  | _ =>
    if isNothingV ops f then pure (.lineNumberNode l f)
    else throwTypeError ops "new" "" (← ops.fieldtype (coreV ops "LineNumberNode") "file") f
def DebugInfo4 (def_ linetable edges codelocs : Value L) : Value L :=
  objV ops (.debugInfo def_ linetable edges codelocs)
def DebugInfo1 (def_ : Value L) : Value L :=
  objV ops (.debugInfo def_ (nothingV ops) (.leaf (ops.svec [])) (strV ops ""))
def SlotNumber (n : I64) : Value L := .slotNumber n
/-- The arrays of a `PhiNode` are given by their contents, as in `base/expr.jl`. -/
def PhiNode (edges : List I32) (values : List (Option (Value L))) : Value L := .phiNode edges values
/-- The `typ` of a `PiNode` is a non-AST value, as in `base/expr.jl`. -/
def PiNode (val : Value L) (typ : L) : Value L := .piNode val typ
def PhiCNode (values : List (Option (Value L))) : Value L := .phiCNode values
def UpsilonNode1 (val : Value L) : Value L := .upsilonNode (some val)
def UpsilonNode0 : Value L := .upsilonNode none
def MethodMatch (spec_types sparams method : Value L) (fully_covers : Bool) : Value L :=
  objV ops (.methodMatch spec_types sparams method (boolV ops fully_covers))

/--
Julia source: base/boot.jl:728-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const NullDebugInfo = DebugInfo(:none)

```
-/
def NullDebugInfo : Value L := DebugInfo1 ops (.symbol "none")

/--
Julia source: base/boot.jl:875-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Minimal implementations of using/import for bootstrapping (supports only
# `import .M: a, b, c, ...`, little error checking)
let
    fail() = throw(ArgumentError("unsupported import/using while bootstrapping"))
    length(a::Array{T, 1}) where {T} = getfield(getfield(a, :size), 1)
    function getindex(A::Array, i::Int)
        Intrinsics.ult_int(Intrinsics.bitcast(UInt, Intrinsics.sub_int(i, 1)), Intrinsics.bitcast(UInt, length(A))) || fail()
        memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
    end
    x == y = Intrinsics.eq_int(x, y)
    x + y = Intrinsics.add_int(x, y)
    x <= y = Intrinsics.sle_int(x, y)

    global function _eval_import(explicit::Bool, to::Module, from::Union{Expr, Nothing}, paths::Expr...)
        from isa Expr || fail()
        if length(from.args) == 2 && getindex(from.args, 1) === :.
            from = getglobal(to, getindex(from.args, 2))
        elseif length(from.args) == 1 && getindex(from.args, 1) === :Core
            from = Core
        elseif length(from.args) == 1 && getindex(from.args, 1) === :Base
            from = Main.Base
        else
            fail()
        end
        from isa Module || fail()
        i = 1
        while i <= nfields(paths)
            a = getfield(paths, i).args
            length(a) == 1 || fail()
            s = getindex(a, 1)
            Core._import(to, from, s, s, explicit)
            i += 1
        end
    end

    global function _eval_using(to::Module, path::Expr)
        getindex(path.args, 1) === :. || fail()
        from = getglobal(to, getindex(path.args, 2))
        i = 3
        while i <= length(path.args)
            from = getfield(from, getindex(path.args, i))
            i += 1
        end
        from isa Module || fail()
        Core._using(to, from)
    end
end

```
-/
def fail {α : Type} : CoreM W L α :=
  throwArgumentError ops "unsupported import/using while bootstrapping"
/-- The local `length` of a `Vector`, here the arguments of an `Expr`. -/
def length (a : List (Value L)) : I64 := JInt.lit .i64 a.length
/-- The local `getindex`: `fail()` unless `1 ≤ i ≤ length(A)`. -/
def getindex (A : List (Value L)) (i : I64) : CoreM W L (Value L) :=
  if ult_int (bitcast .u64 (sub_int i (JInt.lit .i64 1)) (by decide))
      (bitcast .u64 (length A) (by decide)) then
    match A[(i.val - 1).toNat]? with
    | some x => pure x
    | none => fail ops
  else fail ops
def eq (x y : I64) : Bool := eq_int x y
def add (x y : I64) : I64 := JuliaLean.base.int.add_int x y
def le (x y : I64) : Bool := sle_int x y

/-- The module that `from` names: `.M` relative to `to`, `Core` or `Base`; `fail()` otherwise. -/
def evalImportFrom (to : Value L) (args : List (Value L)) : CoreM W L (Value L) := do
  if eq (length args) (JInt.lit .i64 2) then
    if ops.same (← getindex ops args (JInt.lit .i64 1)) (.symbol ".") then
      return ← ops.getglobal to (← getindex ops args (JInt.lit .i64 2))
  if eq (length args) (JInt.lit .i64 1) then
    if ops.same (← getindex ops args (JInt.lit .i64 1)) (.symbol "Core") then
      return coreV ops "Core"
  if eq (length args) (JInt.lit .i64 1) then
    if ops.same (← getindex ops args (JInt.lit .i64 1)) (.symbol "Base") then
      return ← ops.getfield (coreV ops "Main") (.symbol "Base")
  fail ops

/-- `from` is `nothing` or an `Expr`; each path is an `Expr`, given by its arguments. -/
def _eval_import (explicit : Bool) (to from_ : Value L) (paths : List (List (Value L))) :
    CoreM W L Unit := do
  let args ← match from_ with
    | .expr _ args => pure args
    | _ => fail ops
  let from_ ← evalImportFrom ops to args
  if !ops.isa from_ (coreV ops "Module") then fail ops
  for a in paths do
    if !eq (length a) (JInt.lit .i64 1) then fail ops
    let s ← getindex ops a (JInt.lit .i64 1)
    ops.importBinding to from_ s s explicit

/-- `path` is an `Expr`, given by its arguments. -/
def _eval_using (to : Value L) (args : List (Value L)) : CoreM W L Unit := do
  if !ops.same (← getindex ops args (JInt.lit .i64 1)) (.symbol ".") then fail ops
  let mut from_ ← ops.getglobal to (← getindex ops args (JInt.lit .i64 2))
  for x in args.drop 2 do
    from_ ← ops.getfield from_ x
  if !ops.isa from_ (coreV ops "Module") then fail ops
  ops.usingModule to from_

-- Reason: The module `IR` only re-exports types defined in C; it defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:923-939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # module providing the IR object model
-- # excluding types already exported by Core (GlobalRef, QuoteNode, Expr, LineNumberNode)
-- # any type beyond these is self-quoting (see also Base.isa_ast_node)
-- module IR
-- 
-- export CodeInfo, MethodInstance, CodeInstance, GotoNode, GotoIfNot, ReturnNode,
--     NewvarNode, SSAValue, SlotNumber, Argument,
--     PiNode, PhiNode, PhiCNode, UpsilonNode, DebugInfo,
--     Const, PartialStruct, InterConditional, EnterNode
-- 
-- using Core: CodeInfo, MethodInstance, CodeInstance, GotoNode, GotoIfNot, ReturnNode,
--     NewvarNode, SSAValue, SlotNumber, Argument,
--     PiNode, PhiNode, PhiCNode, UpsilonNode, DebugInfo,
--     Const, PartialStruct, InterConditional, EnterNode
-- 
-- end # module IR
-- 
-- /Source

/--
Julia source: base/boot.jl:940-949 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# docsystem basics
macro doc(x...)
    docex = atdoc(__source__, __module__, x...)
    isa(docex, Expr) && docex.head === :escape && return docex
    return Expr(:escape, Expr(:var"hygienic-scope", docex, typeof(atdoc).name.module, __source__))
end
macro __doc__(x)
    return Expr(:escape, Expr(:block, Expr(:meta, :doc), x))
end

```
-/
def macro_doc (source mod : Value L) (x : List (Value L)) : CoreM W L (Value L) := do
  let docex ← ops.call (← ops.getglobal (coreV ops "Core") (.symbol "atdoc")) (source :: mod :: x)
  match docex with
  | .expr "escape" _ => return docex
  | _ =>
    let atdoc ← ops.getglobal (coreV ops "Core") (.symbol "atdoc")
    let name ← ops.getfield (.leaf (ops.typeOf atdoc)) (.symbol "name")
    let m ← ops.getfield name (.symbol "module")
    pure (.expr "escape" [.expr "hygienic-scope" [docex, m, source]])
def macro___doc__ (x : Value L) : Value L :=
  .expr "escape" [.expr "block" [.expr "meta" [.symbol "doc"], x]]

/--
Julia source: base/boot.jl:950-958 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isbasicdoc(@nospecialize x) = (isa(x, Expr) && x.head === :.) || isa(x, Union{QuoteNode, Symbol})
firstarg(arg1, args...) = arg1
iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
iscallexpr(ex) = false
function ignoredoc(source, mod, str, expr)
    (isbasicdoc(expr) || iscallexpr(expr)) && return Expr(:escape, nothing)
    Expr(:escape, expr)
end

```
-/
def isbasicdoc (x : Value L) : Bool :=
  (match x with
   | .expr "." _ => true
   | _ => false) ||
  (match x with
   | .quoteNode _ => true
   | .symbol _ => true
   | _ => false)
def firstarg (arg1 : Value L) (_args : List (Value L)) : Value L := arg1
/-- Both methods: the `Expr` method recurses on `firstarg(ex.args...)` (a `MethodError` for an
empty `where`); any other value is not a call. -/
def iscallexpr : Value L → CoreM W L Bool
  | .expr "where" [] => noMethod ops "firstarg" []
  | .expr "where" (a :: _) => iscallexpr a
  | .expr head _ => pure (head == "call")
  | _ => pure false
def ignoredoc (_source _mod _str expr : Value L) : CoreM W L (Value L) := do
  let basic ← if isbasicdoc expr then pure true else iscallexpr ops expr
  if basic then return .expr "escape" [nothingV ops]
  pure (.expr "escape" [expr])

/--
Julia source: base/boot.jl:959-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
global atdoc = ignoredoc
atdoc!(λ)    = global atdoc = λ

```
-/
def atdoc_initial : Value L := coreV ops "ignoredoc"
def atdoc! (f : Value L) : CoreM W L (Value L) := ops.setglobal (coreV ops "Core") "atdoc" f

-- Reason: The macros `@int128_str`, `@uint128_str`, `@big_str` and `@cmd` are declared with no method.
-- UNTRANSLATED
-- Source: base/boot.jl:962-970 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # macros for big integer syntax
-- macro int128_str end
-- macro uint128_str end
-- macro big_str end
-- 
-- # macro for command syntax
-- macro cmd end
-- 
-- 
-- /Source

-- Reason: The abstract type `IO` defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:971-972 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # simple stand-alone print definitions for debugging
-- abstract type IO end
-- /Source

/--
Julia source: base/boot.jl:973-978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct CoreSTDOUT <: IO
    CoreSTDOUT() = new()
end
struct CoreSTDERR <: IO
    CoreSTDERR() = new()
end
```
-/
def CoreSTDOUT : Value L := objV ops .coreSTDOUT
def CoreSTDERR : Value L := objV ops .coreSTDERR

/--
Julia source: base/boot.jl:979-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const stdout = CoreSTDOUT()
const stderr = CoreSTDERR()
```
-/
def stdout : Value L := CoreSTDOUT ops
def stderr : Value L := CoreSTDERR ops

/--
Julia source: base/boot.jl:981-983 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
io_pointer(::CoreSTDOUT) = Intrinsics.pointerref(cglobal(:jl_uv_stdout, Ptr{Cvoid}), 1, 1)
io_pointer(::CoreSTDERR) = Intrinsics.pointerref(cglobal(:jl_uv_stderr, Ptr{Cvoid}), 1, 1)

```
-/
def io_pointer_STDOUT : CoreM W L (Value L) := ops.uvStdio false
def io_pointer_STDERR : CoreM W L (Value L) := ops.uvStdio true
/-- `io_pointer(io)`: the method dispatch selects for `io`. -/
def io_pointer (io : Value L) : CoreM W L (Value L) :=
  if ops.isa io (coreV ops "CoreSTDOUT") then io_pointer_STDOUT ops
  else if ops.isa io (coreV ops "CoreSTDERR") then io_pointer_STDERR ops
  else noMethod ops "io_pointer" [io]

/--
Julia source: base/boot.jl:984-995 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_write(io::IO, x::Ptr{UInt8}, nb::UInt) =
    (ccall(:jl_uv_puts, Cvoid, (Ptr{Cvoid}, Ptr{UInt8}, UInt), io_pointer(io), x, nb); nb)
unsafe_write(io::IO, x::Ptr{UInt8}, nb::Int) =
    (ccall(:jl_uv_puts, Cvoid, (Ptr{Cvoid}, Ptr{UInt8}, Int), io_pointer(io), x, nb); nb)
write(io::IO, x::UInt8) =
    (ccall(:jl_uv_putb, Cvoid, (Ptr{Cvoid}, UInt8), io_pointer(io), x); 1)
function write(io::IO, x::String)
    nb = sizeof(x)
    unsafe_write(io, ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), x), nb)
    return nb
end

```
-/
def unsafe_write_UInt (io x nb : Value L) : CoreM W L (Value L) := do
  ops.uvPuts (← io_pointer ops io) x nb
  pure nb
def unsafe_write_Int (io x nb : Value L) : CoreM W L (Value L) := do
  ops.uvPuts (← io_pointer ops io) x nb
  pure nb
def write_UInt8 (io : Value L) (x : U8) : CoreM W L (Value L) := do
  ops.uvPutb (← io_pointer ops io) x
  pure (intV ops (JInt.lit .i64 1))
def write_String (io x : Value L) : CoreM W L (Value L) := do
  let nb := intV ops (JInt.lit .i64 (ops.stringBytes x).length)
  let _ ← unsafe_write_Int ops io (← ops.stringPtr x) nb
  pure nb

/--
Julia source: base/boot.jl:996-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, @nospecialize x) = ccall(:jl_static_show, Cvoid, (Ptr{Cvoid}, Any), io_pointer(io), x)
print(io::IO, x::AbstractChar) = ccall(:jl_uv_putc, Cvoid, (Ptr{Cvoid}, Char), io_pointer(io), x)
print(io::IO, x::String) = (write(io, x); nothing)
print(io::IO, @nospecialize x) = show(io, x)
print(io::IO, @nospecialize(x), @nospecialize a...) = (print(io, x); print(io, a...))
println(io::IO) = (write(io, 0x0a); nothing) # 0x0a = '\n'
println(io::IO, @nospecialize x...) = (print(io, x...); println(io))

```
-/
def show_ (io x : Value L) : CoreM W L (Value L) := do
  ops.staticShow (← io_pointer ops io) x
  pure (nothingV ops)
/-- The `Char` argument of the `ccall` is `unsafe_convert(Char, cconvert(Char, x))`. -/
def print_Char (io x : Value L) : CoreM W L (Value L) := do
  let c ← ops.call (coreV ops "cconvert") [coreV ops "Char", x]
  ops.uvPutc (← io_pointer ops io) (← ops.call (coreV ops "unsafe_convert") [coreV ops "Char", c])
  pure (nothingV ops)
def print_String (io x : Value L) : CoreM W L (Value L) := do
  let _ ← write_String ops io x
  pure (nothingV ops)
def print_Any (io x : Value L) : CoreM W L (Value L) := show_ ops io x
/-- `print(io, x)`: the method dispatch selects for `x`. -/
def print1 (io x : Value L) : CoreM W L (Value L) :=
  if ops.isa x (coreV ops "AbstractChar") then print_Char ops io x
  else if ops.isa x (coreV ops "String") then print_String ops io x
  else print_Any ops io x
/-- `print(io, x, a...)` with the remaining arguments `a`; with none it is `print(io, x)`. -/
def printSeq (io x : Value L) : List (Value L) → CoreM W L (Value L)
  | [] => print1 ops io x
  | y :: ys => do
    let _ ← print1 ops io x
    printSeq io y ys
def print_varargs (io x a0 : Value L) (a : List (Value L)) : CoreM W L (Value L) :=
  printSeq ops io x (a0 :: a)
def println0 (io : Value L) : CoreM W L (Value L) := do
  let _ ← write_UInt8 ops io (JInt.lit .u8 0x0a)
  pure (nothingV ops)
def println_io (io x : Value L) (xs : List (Value L)) : CoreM W L (Value L) := do
  let _ ← printSeq ops io x xs
  println0 ops io

/--
Julia source: base/boot.jl:1004-1007 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(@nospecialize a) = show(stdout, a)
print(@nospecialize a...) = print(stdout, a...)
println(@nospecialize a...) = println(stdout, a...)

```
-/
def show_stdout (a : Value L) : CoreM W L (Value L) := show_ ops (stdout ops) a
/-- With no argument, `print(stdout)` has no method in `Core`. -/
def print_stdout : List (Value L) → CoreM W L (Value L)
  | [] => noMethod ops "print" [stdout ops]
  | x :: xs => printSeq ops (stdout ops) x xs
def println_stdout : List (Value L) → CoreM W L (Value L)
  | [] => println0 ops (stdout ops)
  | x :: xs => println_io ops (stdout ops) x xs

/--
Julia source: base/boot.jl:1008-1013 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct GeneratedFunctionStub
    gen
    argnames::SimpleVector
    spnames::SimpleVector
    GeneratedFunctionStub(@nospecialize(gen), argnames::SimpleVector, spnames::SimpleVector) = new(gen, argnames, spnames)
end
```
-/
def GeneratedFunctionStub (gen argnames spnames : Value L) : CoreM W L (Value L) := do
  let argnames ← cf ops "GeneratedFunctionStub" "argnames" argnames
  let spnames ← cf ops "GeneratedFunctionStub" "spnames" spnames
  pure (objV ops (.generatedFunctionStub gen argnames spnames))

-- Reason: The abstract type `CachedGenerator` defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:1014-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # If the generator is a subtype of this trait, inference caches the generated unoptimized
-- # code, sacrificing memory space to improve the performance of subsequent inferences.
-- # This tradeoff is not appropriate in general cases (e.g., for `GeneratedFunctionStub`s
-- # generated from the front end), but it can be justified for generators involving complex
-- # code transformations, such as a Cassette-like system.
-- abstract type CachedGenerator end
-- 
-- /Source

/--
Julia source: base/boot.jl:1029-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eval(Core, :((NT::Type{NamedTuple{names,T}})(args::T) where {names, T <: Tuple} =
             $(Expr(:splatnew, :NT, :args))))

```
-/
-- `NT` is the type `NamedTuple{names,T}`.
def NamedTuple_NT (NT args : Value L) : CoreM W L (Value L) := ops.splatnew NT args

/--
Julia source: base/boot.jl:1022-1023 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
NamedTuple() = NamedTuple{(),Tuple{}}(())

```
-/
def NamedTuple0 : CoreM W L (Value L) := do
  let NT ← ops.applyType (coreV ops "NamedTuple")
    [tupleV ops [], ← ops.applyType (coreV ops "Tuple") []]
  NamedTuple_NT ops NT (tupleV ops [])

/--
Julia source: base/boot.jl:1024-1026 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eval(Core, :(NamedTuple{names}(args::Tuple) where {names} =
             $(Expr(:splatnew, :(NamedTuple{names,typeof(args)}), :args))))

```
-/
def NamedTuple_names (names args : Value L) : CoreM W L (Value L) := do
  ops.splatnew (← ops.applyType (coreV ops "NamedTuple") [names, .leaf (ops.typeOf args)]) args

-- Reason: This `using` of intrinsics is load-time structure.
-- UNTRANSLATED
-- Source: base/boot.jl:1027-1028 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- using .Intrinsics: sle_int, add_int
-- 
-- /Source

-- Reason: This `import` of intrinsics is load-time structure.
-- UNTRANSLATED
-- Source: base/boot.jl:1032-1036 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # constructors for built-in types
-- 
-- import .Intrinsics: eq_int, trunc_int, lshr_int, sub_int, shl_int, bitcast, sext_int, zext_int, and_int,
--     slt_int, xor_int
-- 
-- /Source

/--
Julia source: base/boot.jl:1037-1043 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_top_bit_set(x)
    @inline
    # the top bit is set iff x is negative as a signed number; Core has no
    # `zero`, and `xor_int(x, x)` is a zero of any width
    slt_int(x, xor_int(x, x))
end

```
-/
def is_top_bit_set {t : IntTy} (x : JInt t) : Bool := slt_int x (xor_int x x)

/--
Julia source: base/boot.jl:1044-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# n.b. This function exists for CUDA to overload to configure error behavior (see #48097)
throw_inexacterror(func::Symbol, to, val) = throw(InexactError(func, to, val))

```
-/
def throw_inexacterror {α : Type} (func : Sym) (to val : Value L) : CoreM W L α := do
  throw (← InexactError ops func [to, val])

/--
Julia source: base/boot.jl:1047-1054 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_sign_bit(::Type{To}, x) where {To}
    @inline
    # the top bit is the sign bit of x but "sign bit" sounds better in stacktraces
    # n.b. if x is signed, then bitsizeof(x) === bitsizeof(To), otherwise bitsizeof(x) >= bitsizeof(To)
    is_top_bit_set(x) && throw_inexacterror(bitsizeof(x) === bitsizeof(To) ? :convert : :trunc, To, x)
    x
end

```
-/
def check_sign_bit (To : IntTy) {t : IntTy} (x : JInt t) : CoreM W L (JInt t) := do
  if is_top_bit_set x then
    throw_inexacterror ops (if t.bits == To.bits then "convert" else "trunc") (intType ops To)
      (intV ops x)
  pure x

/--
Julia source: base/boot.jl:1055-1062 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checked_trunc_sint(::Type{To}, x::From) where {To,From}
    @inline
    y = trunc_int(To, x)
    back = sext_int(From, y)
    eq_int(x, back) || throw_inexacterror(:trunc, To, x)
    y
end

```
-/
def checked_trunc_sint (To : IntTy) {t : IntTy} (x : JInt t) (h : To.bits < t.bits) :
    CoreM W L (JInt To) := do
  let y := trunc_int To x h
  let back := sext_int t y h
  if !eq_int x back then throw_inexacterror ops "trunc" (intType ops To) (intV ops x)
  pure y

/--
Julia source: base/boot.jl:1063-1070 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checked_trunc_uint(::Type{To}, x::From) where {To,From}
    @inline
    y = trunc_int(To, x)
    back = zext_int(From, y)
    eq_int(x, back) || throw_inexacterror(:trunc, To, x)
    y
end

```
-/
def checked_trunc_uint (To : IntTy) {t : IntTy} (x : JInt t) (h : To.bits < t.bits) :
    CoreM W L (JInt To) := do
  let y := trunc_int To x h
  let back := zext_int t y h
  if !eq_int x back then throw_inexacterror ops "trunc" (intType ops To) (intV ops x)
  pure y

/--
Julia source: base/boot.jl:1071-1081 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toInt8(x::Int8)       = x
toInt8(x::Int16)      = checked_trunc_sint(Int8, x)
toInt8(x::Int32)      = checked_trunc_sint(Int8, x)
toInt8(x::Int64)      = checked_trunc_sint(Int8, x)
toInt8(x::Int128)     = checked_trunc_sint(Int8, x)
toInt8(x::UInt8)      = bitcast(Int8, check_sign_bit(Int8, x))
toInt8(x::UInt16)     = checked_trunc_sint(Int8, check_sign_bit(Int8, x))
toInt8(x::UInt32)     = checked_trunc_sint(Int8, check_sign_bit(Int8, x))
toInt8(x::UInt64)     = checked_trunc_sint(Int8, check_sign_bit(Int8, x))
toInt8(x::UInt128)    = checked_trunc_sint(Int8, check_sign_bit(Int8, x))
toInt8(x::Bool)       = bitcast(Int8, x)
```
-/
def toInt8_Int8 (x : JInt .i8) : CoreM W L (JInt .i8) := pure x
def toInt8_Int16 (x : JInt .i16) : CoreM W L (JInt .i8) := checked_trunc_sint ops .i8 x (by decide)
def toInt8_Int32 (x : JInt .i32) : CoreM W L (JInt .i8) := checked_trunc_sint ops .i8 x (by decide)
def toInt8_Int64 (x : JInt .i64) : CoreM W L (JInt .i8) := checked_trunc_sint ops .i8 x (by decide)
def toInt8_Int128 (x : JInt .i128) : CoreM W L (JInt .i8) := checked_trunc_sint ops .i8 x (by decide)
def toInt8_UInt8 (x : JInt .u8) : CoreM W L (JInt .i8) := do
  let y ← check_sign_bit ops .i8 x
  pure (bitcast .i8 y (by decide))
def toInt8_UInt16 (x : JInt .u16) : CoreM W L (JInt .i8) := do
  let y ← check_sign_bit ops .i8 x
  checked_trunc_sint ops .i8 y (by decide)
def toInt8_UInt32 (x : JInt .u32) : CoreM W L (JInt .i8) := do
  let y ← check_sign_bit ops .i8 x
  checked_trunc_sint ops .i8 y (by decide)
def toInt8_UInt64 (x : JInt .u64) : CoreM W L (JInt .i8) := do
  let y ← check_sign_bit ops .i8 x
  checked_trunc_sint ops .i8 y (by decide)
def toInt8_UInt128 (x : JInt .u128) : CoreM W L (JInt .i8) := do
  let y ← check_sign_bit ops .i8 x
  checked_trunc_sint ops .i8 y (by decide)
def toInt8_Bool (x : Bool) : CoreM W L (JInt .i8) := pure (boolBits .i8 x)

/--
Julia source: base/boot.jl:1082-1092 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toInt16(x::Int8)      = sext_int(Int16, x)
toInt16(x::Int16)     = x
toInt16(x::Int32)     = checked_trunc_sint(Int16, x)
toInt16(x::Int64)     = checked_trunc_sint(Int16, x)
toInt16(x::Int128)    = checked_trunc_sint(Int16, x)
toInt16(x::UInt8)     = zext_int(Int16, x)
toInt16(x::UInt16)    = bitcast(Int16, check_sign_bit(Int16, x))
toInt16(x::UInt32)    = checked_trunc_sint(Int16, check_sign_bit(Int16, x))
toInt16(x::UInt64)    = checked_trunc_sint(Int16, check_sign_bit(Int16, x))
toInt16(x::UInt128)   = checked_trunc_sint(Int16, check_sign_bit(Int16, x))
toInt16(x::Bool)      = zext_int(Int16, x)
```
-/
def toInt16_Int8 (x : JInt .i8) : CoreM W L (JInt .i16) := pure (sext_int .i16 x (by decide))
def toInt16_Int16 (x : JInt .i16) : CoreM W L (JInt .i16) := pure x
def toInt16_Int32 (x : JInt .i32) : CoreM W L (JInt .i16) := checked_trunc_sint ops .i16 x (by decide)
def toInt16_Int64 (x : JInt .i64) : CoreM W L (JInt .i16) := checked_trunc_sint ops .i16 x (by decide)
def toInt16_Int128 (x : JInt .i128) : CoreM W L (JInt .i16) := checked_trunc_sint ops .i16 x (by decide)
def toInt16_UInt8 (x : JInt .u8) : CoreM W L (JInt .i16) := pure (zext_int .i16 x (by decide))
def toInt16_UInt16 (x : JInt .u16) : CoreM W L (JInt .i16) := do
  let y ← check_sign_bit ops .i16 x
  pure (bitcast .i16 y (by decide))
def toInt16_UInt32 (x : JInt .u32) : CoreM W L (JInt .i16) := do
  let y ← check_sign_bit ops .i16 x
  checked_trunc_sint ops .i16 y (by decide)
def toInt16_UInt64 (x : JInt .u64) : CoreM W L (JInt .i16) := do
  let y ← check_sign_bit ops .i16 x
  checked_trunc_sint ops .i16 y (by decide)
def toInt16_UInt128 (x : JInt .u128) : CoreM W L (JInt .i16) := do
  let y ← check_sign_bit ops .i16 x
  checked_trunc_sint ops .i16 y (by decide)
def toInt16_Bool (x : Bool) : CoreM W L (JInt .i16) := pure (boolBits .i16 x)

/--
Julia source: base/boot.jl:1093-1103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toInt32(x::Int8)      = sext_int(Int32, x)
toInt32(x::Int16)     = sext_int(Int32, x)
toInt32(x::Int32)     = x
toInt32(x::Int64)     = checked_trunc_sint(Int32, x)
toInt32(x::Int128)    = checked_trunc_sint(Int32, x)
toInt32(x::UInt8)     = zext_int(Int32, x)
toInt32(x::UInt16)    = zext_int(Int32, x)
toInt32(x::UInt32)    = bitcast(Int32, check_sign_bit(Int32, x))
toInt32(x::UInt64)    = checked_trunc_sint(Int32, check_sign_bit(Int32, x))
toInt32(x::UInt128)   = checked_trunc_sint(Int32, check_sign_bit(Int32, x))
toInt32(x::Bool)      = zext_int(Int32, x)
```
-/
def toInt32_Int8 (x : JInt .i8) : CoreM W L (JInt .i32) := pure (sext_int .i32 x (by decide))
def toInt32_Int16 (x : JInt .i16) : CoreM W L (JInt .i32) := pure (sext_int .i32 x (by decide))
def toInt32_Int32 (x : JInt .i32) : CoreM W L (JInt .i32) := pure x
def toInt32_Int64 (x : JInt .i64) : CoreM W L (JInt .i32) := checked_trunc_sint ops .i32 x (by decide)
def toInt32_Int128 (x : JInt .i128) : CoreM W L (JInt .i32) := checked_trunc_sint ops .i32 x (by decide)
def toInt32_UInt8 (x : JInt .u8) : CoreM W L (JInt .i32) := pure (zext_int .i32 x (by decide))
def toInt32_UInt16 (x : JInt .u16) : CoreM W L (JInt .i32) := pure (zext_int .i32 x (by decide))
def toInt32_UInt32 (x : JInt .u32) : CoreM W L (JInt .i32) := do
  let y ← check_sign_bit ops .i32 x
  pure (bitcast .i32 y (by decide))
def toInt32_UInt64 (x : JInt .u64) : CoreM W L (JInt .i32) := do
  let y ← check_sign_bit ops .i32 x
  checked_trunc_sint ops .i32 y (by decide)
def toInt32_UInt128 (x : JInt .u128) : CoreM W L (JInt .i32) := do
  let y ← check_sign_bit ops .i32 x
  checked_trunc_sint ops .i32 y (by decide)
def toInt32_Bool (x : Bool) : CoreM W L (JInt .i32) := pure (boolBits .i32 x)

/--
Julia source: base/boot.jl:1104-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toInt64(x::Int8)      = sext_int(Int64, x)
toInt64(x::Int16)     = sext_int(Int64, x)
toInt64(x::Int32)     = sext_int(Int64, x)
toInt64(x::Int64)     = x
toInt64(x::Int128)    = checked_trunc_sint(Int64, x)
toInt64(x::UInt8)     = zext_int(Int64, x)
toInt64(x::UInt16)    = zext_int(Int64, x)
toInt64(x::UInt32)    = zext_int(Int64, x)
toInt64(x::UInt64)    = bitcast(Int64, check_sign_bit(Int64, x))
toInt64(x::UInt128)   = checked_trunc_sint(Int64, check_sign_bit(Int64, x))
toInt64(x::Bool)      = zext_int(Int64, x)
```
-/
def toInt64_Int8 (x : JInt .i8) : CoreM W L (JInt .i64) := pure (sext_int .i64 x (by decide))
def toInt64_Int16 (x : JInt .i16) : CoreM W L (JInt .i64) := pure (sext_int .i64 x (by decide))
def toInt64_Int32 (x : JInt .i32) : CoreM W L (JInt .i64) := pure (sext_int .i64 x (by decide))
def toInt64_Int64 (x : JInt .i64) : CoreM W L (JInt .i64) := pure x
def toInt64_Int128 (x : JInt .i128) : CoreM W L (JInt .i64) := checked_trunc_sint ops .i64 x (by decide)
def toInt64_UInt8 (x : JInt .u8) : CoreM W L (JInt .i64) := pure (zext_int .i64 x (by decide))
def toInt64_UInt16 (x : JInt .u16) : CoreM W L (JInt .i64) := pure (zext_int .i64 x (by decide))
def toInt64_UInt32 (x : JInt .u32) : CoreM W L (JInt .i64) := pure (zext_int .i64 x (by decide))
def toInt64_UInt64 (x : JInt .u64) : CoreM W L (JInt .i64) := do
  let y ← check_sign_bit ops .i64 x
  pure (bitcast .i64 y (by decide))
def toInt64_UInt128 (x : JInt .u128) : CoreM W L (JInt .i64) := do
  let y ← check_sign_bit ops .i64 x
  checked_trunc_sint ops .i64 y (by decide)
def toInt64_Bool (x : Bool) : CoreM W L (JInt .i64) := pure (boolBits .i64 x)

/--
Julia source: base/boot.jl:1115-1125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toInt128(x::Int8)     = sext_int(Int128, x)
toInt128(x::Int16)    = sext_int(Int128, x)
toInt128(x::Int32)    = sext_int(Int128, x)
toInt128(x::Int64)    = sext_int(Int128, x)
toInt128(x::Int128)   = x
toInt128(x::UInt8)    = zext_int(Int128, x)
toInt128(x::UInt16)   = zext_int(Int128, x)
toInt128(x::UInt32)   = zext_int(Int128, x)
toInt128(x::UInt64)   = zext_int(Int128, x)
toInt128(x::UInt128)  = bitcast(Int128, check_sign_bit(Int128, x))
toInt128(x::Bool)     = zext_int(Int128, x)
```
-/
def toInt128_Int8 (x : JInt .i8) : CoreM W L (JInt .i128) := pure (sext_int .i128 x (by decide))
def toInt128_Int16 (x : JInt .i16) : CoreM W L (JInt .i128) := pure (sext_int .i128 x (by decide))
def toInt128_Int32 (x : JInt .i32) : CoreM W L (JInt .i128) := pure (sext_int .i128 x (by decide))
def toInt128_Int64 (x : JInt .i64) : CoreM W L (JInt .i128) := pure (sext_int .i128 x (by decide))
def toInt128_Int128 (x : JInt .i128) : CoreM W L (JInt .i128) := pure x
def toInt128_UInt8 (x : JInt .u8) : CoreM W L (JInt .i128) := pure (zext_int .i128 x (by decide))
def toInt128_UInt16 (x : JInt .u16) : CoreM W L (JInt .i128) := pure (zext_int .i128 x (by decide))
def toInt128_UInt32 (x : JInt .u32) : CoreM W L (JInt .i128) := pure (zext_int .i128 x (by decide))
def toInt128_UInt64 (x : JInt .u64) : CoreM W L (JInt .i128) := pure (zext_int .i128 x (by decide))
def toInt128_UInt128 (x : JInt .u128) : CoreM W L (JInt .i128) := do
  let y ← check_sign_bit ops .i128 x
  pure (bitcast .i128 y (by decide))
def toInt128_Bool (x : Bool) : CoreM W L (JInt .i128) := pure (boolBits .i128 x)

/--
Julia source: base/boot.jl:1126-1136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toUInt8(x::Int8)      = bitcast(UInt8, check_sign_bit(UInt8, x))
toUInt8(x::Int16)     = checked_trunc_uint(UInt8, x)
toUInt8(x::Int32)     = checked_trunc_uint(UInt8, x)
toUInt8(x::Int64)     = checked_trunc_uint(UInt8, x)
toUInt8(x::Int128)    = checked_trunc_uint(UInt8, x)
toUInt8(x::UInt8)     = x
toUInt8(x::UInt16)    = checked_trunc_uint(UInt8, x)
toUInt8(x::UInt32)    = checked_trunc_uint(UInt8, x)
toUInt8(x::UInt64)    = checked_trunc_uint(UInt8, x)
toUInt8(x::UInt128)   = checked_trunc_uint(UInt8, x)
toUInt8(x::Bool)      = bitcast(UInt8, x)
```
-/
def toUInt8_Int8 (x : JInt .i8) : CoreM W L (JInt .u8) := do
  let y ← check_sign_bit ops .u8 x
  pure (bitcast .u8 y (by decide))
def toUInt8_Int16 (x : JInt .i16) : CoreM W L (JInt .u8) := checked_trunc_uint ops .u8 x (by decide)
def toUInt8_Int32 (x : JInt .i32) : CoreM W L (JInt .u8) := checked_trunc_uint ops .u8 x (by decide)
def toUInt8_Int64 (x : JInt .i64) : CoreM W L (JInt .u8) := checked_trunc_uint ops .u8 x (by decide)
def toUInt8_Int128 (x : JInt .i128) : CoreM W L (JInt .u8) := checked_trunc_uint ops .u8 x (by decide)
def toUInt8_UInt8 (x : JInt .u8) : CoreM W L (JInt .u8) := pure x
def toUInt8_UInt16 (x : JInt .u16) : CoreM W L (JInt .u8) := checked_trunc_uint ops .u8 x (by decide)
def toUInt8_UInt32 (x : JInt .u32) : CoreM W L (JInt .u8) := checked_trunc_uint ops .u8 x (by decide)
def toUInt8_UInt64 (x : JInt .u64) : CoreM W L (JInt .u8) := checked_trunc_uint ops .u8 x (by decide)
def toUInt8_UInt128 (x : JInt .u128) : CoreM W L (JInt .u8) := checked_trunc_uint ops .u8 x (by decide)
def toUInt8_Bool (x : Bool) : CoreM W L (JInt .u8) := pure (boolBits .u8 x)

/--
Julia source: base/boot.jl:1137-1147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toUInt16(x::Int8)     = sext_int(UInt16, check_sign_bit(UInt16, x))
toUInt16(x::Int16)    = bitcast(UInt16, check_sign_bit(UInt16, x))
toUInt16(x::Int32)    = checked_trunc_uint(UInt16, x)
toUInt16(x::Int64)    = checked_trunc_uint(UInt16, x)
toUInt16(x::Int128)   = checked_trunc_uint(UInt16, x)
toUInt16(x::UInt8)    = zext_int(UInt16, x)
toUInt16(x::UInt16)   = x
toUInt16(x::UInt32)   = checked_trunc_uint(UInt16, x)
toUInt16(x::UInt64)   = checked_trunc_uint(UInt16, x)
toUInt16(x::UInt128)  = checked_trunc_uint(UInt16, x)
toUInt16(x::Bool)     = zext_int(UInt16, x)
```
-/
def toUInt16_Int8 (x : JInt .i8) : CoreM W L (JInt .u16) := do
  let y ← check_sign_bit ops .u16 x
  pure (sext_int .u16 y (by decide))
def toUInt16_Int16 (x : JInt .i16) : CoreM W L (JInt .u16) := do
  let y ← check_sign_bit ops .u16 x
  pure (bitcast .u16 y (by decide))
def toUInt16_Int32 (x : JInt .i32) : CoreM W L (JInt .u16) := checked_trunc_uint ops .u16 x (by decide)
def toUInt16_Int64 (x : JInt .i64) : CoreM W L (JInt .u16) := checked_trunc_uint ops .u16 x (by decide)
def toUInt16_Int128 (x : JInt .i128) : CoreM W L (JInt .u16) := checked_trunc_uint ops .u16 x (by decide)
def toUInt16_UInt8 (x : JInt .u8) : CoreM W L (JInt .u16) := pure (zext_int .u16 x (by decide))
def toUInt16_UInt16 (x : JInt .u16) : CoreM W L (JInt .u16) := pure x
def toUInt16_UInt32 (x : JInt .u32) : CoreM W L (JInt .u16) := checked_trunc_uint ops .u16 x (by decide)
def toUInt16_UInt64 (x : JInt .u64) : CoreM W L (JInt .u16) := checked_trunc_uint ops .u16 x (by decide)
def toUInt16_UInt128 (x : JInt .u128) : CoreM W L (JInt .u16) := checked_trunc_uint ops .u16 x (by decide)
def toUInt16_Bool (x : Bool) : CoreM W L (JInt .u16) := pure (boolBits .u16 x)

/--
Julia source: base/boot.jl:1148-1158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toUInt32(x::Int8)     = sext_int(UInt32, check_sign_bit(UInt32, x))
toUInt32(x::Int16)    = sext_int(UInt32, check_sign_bit(UInt32, x))
toUInt32(x::Int32)    = bitcast(UInt32, check_sign_bit(UInt32, x))
toUInt32(x::Int64)    = checked_trunc_uint(UInt32, x)
toUInt32(x::Int128)   = checked_trunc_uint(UInt32, x)
toUInt32(x::UInt8)    = zext_int(UInt32, x)
toUInt32(x::UInt16)   = zext_int(UInt32, x)
toUInt32(x::UInt32)   = x
toUInt32(x::UInt64)   = checked_trunc_uint(UInt32, x)
toUInt32(x::UInt128)  = checked_trunc_uint(UInt32, x)
toUInt32(x::Bool)     = zext_int(UInt32, x)
```
-/
def toUInt32_Int8 (x : JInt .i8) : CoreM W L (JInt .u32) := do
  let y ← check_sign_bit ops .u32 x
  pure (sext_int .u32 y (by decide))
def toUInt32_Int16 (x : JInt .i16) : CoreM W L (JInt .u32) := do
  let y ← check_sign_bit ops .u32 x
  pure (sext_int .u32 y (by decide))
def toUInt32_Int32 (x : JInt .i32) : CoreM W L (JInt .u32) := do
  let y ← check_sign_bit ops .u32 x
  pure (bitcast .u32 y (by decide))
def toUInt32_Int64 (x : JInt .i64) : CoreM W L (JInt .u32) := checked_trunc_uint ops .u32 x (by decide)
def toUInt32_Int128 (x : JInt .i128) : CoreM W L (JInt .u32) := checked_trunc_uint ops .u32 x (by decide)
def toUInt32_UInt8 (x : JInt .u8) : CoreM W L (JInt .u32) := pure (zext_int .u32 x (by decide))
def toUInt32_UInt16 (x : JInt .u16) : CoreM W L (JInt .u32) := pure (zext_int .u32 x (by decide))
def toUInt32_UInt32 (x : JInt .u32) : CoreM W L (JInt .u32) := pure x
def toUInt32_UInt64 (x : JInt .u64) : CoreM W L (JInt .u32) := checked_trunc_uint ops .u32 x (by decide)
def toUInt32_UInt128 (x : JInt .u128) : CoreM W L (JInt .u32) := checked_trunc_uint ops .u32 x (by decide)
def toUInt32_Bool (x : Bool) : CoreM W L (JInt .u32) := pure (boolBits .u32 x)

/--
Julia source: base/boot.jl:1159-1169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toUInt64(x::Int8)     = sext_int(UInt64, check_sign_bit(UInt64, x))
toUInt64(x::Int16)    = sext_int(UInt64, check_sign_bit(UInt64, x))
toUInt64(x::Int32)    = sext_int(UInt64, check_sign_bit(UInt64, x))
toUInt64(x::Int64)    = bitcast(UInt64, check_sign_bit(UInt64, x))
toUInt64(x::Int128)   = checked_trunc_uint(UInt64, x)
toUInt64(x::UInt8)    = zext_int(UInt64, x)
toUInt64(x::UInt16)   = zext_int(UInt64, x)
toUInt64(x::UInt32)   = zext_int(UInt64, x)
toUInt64(x::UInt64)   = x
toUInt64(x::UInt128)  = checked_trunc_uint(UInt64, x)
toUInt64(x::Bool)     = zext_int(UInt64, x)
```
-/
def toUInt64_Int8 (x : JInt .i8) : CoreM W L (JInt .u64) := do
  let y ← check_sign_bit ops .u64 x
  pure (sext_int .u64 y (by decide))
def toUInt64_Int16 (x : JInt .i16) : CoreM W L (JInt .u64) := do
  let y ← check_sign_bit ops .u64 x
  pure (sext_int .u64 y (by decide))
def toUInt64_Int32 (x : JInt .i32) : CoreM W L (JInt .u64) := do
  let y ← check_sign_bit ops .u64 x
  pure (sext_int .u64 y (by decide))
def toUInt64_Int64 (x : JInt .i64) : CoreM W L (JInt .u64) := do
  let y ← check_sign_bit ops .u64 x
  pure (bitcast .u64 y (by decide))
def toUInt64_Int128 (x : JInt .i128) : CoreM W L (JInt .u64) := checked_trunc_uint ops .u64 x (by decide)
def toUInt64_UInt8 (x : JInt .u8) : CoreM W L (JInt .u64) := pure (zext_int .u64 x (by decide))
def toUInt64_UInt16 (x : JInt .u16) : CoreM W L (JInt .u64) := pure (zext_int .u64 x (by decide))
def toUInt64_UInt32 (x : JInt .u32) : CoreM W L (JInt .u64) := pure (zext_int .u64 x (by decide))
def toUInt64_UInt64 (x : JInt .u64) : CoreM W L (JInt .u64) := pure x
def toUInt64_UInt128 (x : JInt .u128) : CoreM W L (JInt .u64) := checked_trunc_uint ops .u64 x (by decide)
def toUInt64_Bool (x : Bool) : CoreM W L (JInt .u64) := pure (boolBits .u64 x)

/--
Julia source: base/boot.jl:1170-1181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
toUInt128(x::Int8)    = sext_int(UInt128, check_sign_bit(UInt128, x))
toUInt128(x::Int16)   = sext_int(UInt128, check_sign_bit(UInt128, x))
toUInt128(x::Int32)   = sext_int(UInt128, check_sign_bit(UInt128, x))
toUInt128(x::Int64)   = sext_int(UInt128, check_sign_bit(UInt128, x))
toUInt128(x::Int128)  = bitcast(UInt128, check_sign_bit(UInt128, x))
toUInt128(x::UInt8)   = zext_int(UInt128, x)
toUInt128(x::UInt16)  = zext_int(UInt128, x)
toUInt128(x::UInt32)  = zext_int(UInt128, x)
toUInt128(x::UInt64)  = zext_int(UInt128, x)
toUInt128(x::UInt128) = x
toUInt128(x::Bool)    = zext_int(UInt128, x)

```
-/
def toUInt128_Int8 (x : JInt .i8) : CoreM W L (JInt .u128) := do
  let y ← check_sign_bit ops .u128 x
  pure (sext_int .u128 y (by decide))
def toUInt128_Int16 (x : JInt .i16) : CoreM W L (JInt .u128) := do
  let y ← check_sign_bit ops .u128 x
  pure (sext_int .u128 y (by decide))
def toUInt128_Int32 (x : JInt .i32) : CoreM W L (JInt .u128) := do
  let y ← check_sign_bit ops .u128 x
  pure (sext_int .u128 y (by decide))
def toUInt128_Int64 (x : JInt .i64) : CoreM W L (JInt .u128) := do
  let y ← check_sign_bit ops .u128 x
  pure (sext_int .u128 y (by decide))
def toUInt128_Int128 (x : JInt .i128) : CoreM W L (JInt .u128) := do
  let y ← check_sign_bit ops .u128 x
  pure (bitcast .u128 y (by decide))
def toUInt128_UInt8 (x : JInt .u8) : CoreM W L (JInt .u128) := pure (zext_int .u128 x (by decide))
def toUInt128_UInt16 (x : JInt .u16) : CoreM W L (JInt .u128) := pure (zext_int .u128 x (by decide))
def toUInt128_UInt32 (x : JInt .u32) : CoreM W L (JInt .u128) := pure (zext_int .u128 x (by decide))
def toUInt128_UInt64 (x : JInt .u64) : CoreM W L (JInt .u128) := pure (zext_int .u128 x (by decide))
def toUInt128_UInt128 (x : JInt .u128) : CoreM W L (JInt .u128) := pure x
def toUInt128_Bool (x : Bool) : CoreM W L (JInt .u128) := pure (boolBits .u128 x)
/--
Julia source: base/boot.jl:1182-1194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# TODO: this is here to work around the 4 method limit in inference (#23210).
const BuiltinInts = Union{Int128, Int16, Int32, Int64, Int8, UInt128, UInt16, UInt32, UInt64, UInt8, Bool}
Int8(x::BuiltinInts)    = toInt8(x)::Int8
Int16(x::BuiltinInts)   = toInt16(x)::Int16
Int32(x::BuiltinInts)   = toInt32(x)::Int32
Int64(x::BuiltinInts)   = toInt64(x)::Int64
Int128(x::BuiltinInts)  = toInt128(x)::Int128
UInt8(x::BuiltinInts)   = toUInt8(x)::UInt8
UInt16(x::BuiltinInts)  = toUInt16(x)::UInt16
UInt32(x::BuiltinInts)  = toUInt32(x)::UInt32
UInt64(x::BuiltinInts)  = toUInt64(x)::UInt64
UInt128(x::BuiltinInts) = toUInt128(x)::UInt128

```
-/
inductive BuiltinInts where
  | int (t : IntTy) (x : JInt t)
  | bool (x : Bool)

/-- `toInt8(x)`: the method dispatch selects for `x`. -/
def toInt8 : BuiltinInts → CoreM W L (JInt .i8)
  | .int .i8 x => toInt8_Int8 x
  | .int .i16 x => toInt8_Int16 ops x
  | .int .i32 x => toInt8_Int32 ops x
  | .int .i64 x => toInt8_Int64 ops x
  | .int .i128 x => toInt8_Int128 ops x
  | .int .u8 x => toInt8_UInt8 ops x
  | .int .u16 x => toInt8_UInt16 ops x
  | .int .u32 x => toInt8_UInt32 ops x
  | .int .u64 x => toInt8_UInt64 ops x
  | .int .u128 x => toInt8_UInt128 ops x
  | .bool x => toInt8_Bool x
/-- `toInt16(x)`: the method dispatch selects for `x`. -/
def toInt16 : BuiltinInts → CoreM W L (JInt .i16)
  | .int .i8 x => toInt16_Int8 x
  | .int .i16 x => toInt16_Int16 x
  | .int .i32 x => toInt16_Int32 ops x
  | .int .i64 x => toInt16_Int64 ops x
  | .int .i128 x => toInt16_Int128 ops x
  | .int .u8 x => toInt16_UInt8 x
  | .int .u16 x => toInt16_UInt16 ops x
  | .int .u32 x => toInt16_UInt32 ops x
  | .int .u64 x => toInt16_UInt64 ops x
  | .int .u128 x => toInt16_UInt128 ops x
  | .bool x => toInt16_Bool x
/-- `toInt32(x)`: the method dispatch selects for `x`. -/
def toInt32 : BuiltinInts → CoreM W L (JInt .i32)
  | .int .i8 x => toInt32_Int8 x
  | .int .i16 x => toInt32_Int16 x
  | .int .i32 x => toInt32_Int32 x
  | .int .i64 x => toInt32_Int64 ops x
  | .int .i128 x => toInt32_Int128 ops x
  | .int .u8 x => toInt32_UInt8 x
  | .int .u16 x => toInt32_UInt16 x
  | .int .u32 x => toInt32_UInt32 ops x
  | .int .u64 x => toInt32_UInt64 ops x
  | .int .u128 x => toInt32_UInt128 ops x
  | .bool x => toInt32_Bool x
/-- `toInt64(x)`: the method dispatch selects for `x`. -/
def toInt64 : BuiltinInts → CoreM W L (JInt .i64)
  | .int .i8 x => toInt64_Int8 x
  | .int .i16 x => toInt64_Int16 x
  | .int .i32 x => toInt64_Int32 x
  | .int .i64 x => toInt64_Int64 x
  | .int .i128 x => toInt64_Int128 ops x
  | .int .u8 x => toInt64_UInt8 x
  | .int .u16 x => toInt64_UInt16 x
  | .int .u32 x => toInt64_UInt32 x
  | .int .u64 x => toInt64_UInt64 ops x
  | .int .u128 x => toInt64_UInt128 ops x
  | .bool x => toInt64_Bool x
/-- `toInt128(x)`: the method dispatch selects for `x`. -/
def toInt128 : BuiltinInts → CoreM W L (JInt .i128)
  | .int .i8 x => toInt128_Int8 x
  | .int .i16 x => toInt128_Int16 x
  | .int .i32 x => toInt128_Int32 x
  | .int .i64 x => toInt128_Int64 x
  | .int .i128 x => toInt128_Int128 x
  | .int .u8 x => toInt128_UInt8 x
  | .int .u16 x => toInt128_UInt16 x
  | .int .u32 x => toInt128_UInt32 x
  | .int .u64 x => toInt128_UInt64 x
  | .int .u128 x => toInt128_UInt128 ops x
  | .bool x => toInt128_Bool x
/-- `toUInt8(x)`: the method dispatch selects for `x`. -/
def toUInt8 : BuiltinInts → CoreM W L (JInt .u8)
  | .int .i8 x => toUInt8_Int8 ops x
  | .int .i16 x => toUInt8_Int16 ops x
  | .int .i32 x => toUInt8_Int32 ops x
  | .int .i64 x => toUInt8_Int64 ops x
  | .int .i128 x => toUInt8_Int128 ops x
  | .int .u8 x => toUInt8_UInt8 x
  | .int .u16 x => toUInt8_UInt16 ops x
  | .int .u32 x => toUInt8_UInt32 ops x
  | .int .u64 x => toUInt8_UInt64 ops x
  | .int .u128 x => toUInt8_UInt128 ops x
  | .bool x => toUInt8_Bool x
/-- `toUInt16(x)`: the method dispatch selects for `x`. -/
def toUInt16 : BuiltinInts → CoreM W L (JInt .u16)
  | .int .i8 x => toUInt16_Int8 ops x
  | .int .i16 x => toUInt16_Int16 ops x
  | .int .i32 x => toUInt16_Int32 ops x
  | .int .i64 x => toUInt16_Int64 ops x
  | .int .i128 x => toUInt16_Int128 ops x
  | .int .u8 x => toUInt16_UInt8 x
  | .int .u16 x => toUInt16_UInt16 x
  | .int .u32 x => toUInt16_UInt32 ops x
  | .int .u64 x => toUInt16_UInt64 ops x
  | .int .u128 x => toUInt16_UInt128 ops x
  | .bool x => toUInt16_Bool x
/-- `toUInt32(x)`: the method dispatch selects for `x`. -/
def toUInt32 : BuiltinInts → CoreM W L (JInt .u32)
  | .int .i8 x => toUInt32_Int8 ops x
  | .int .i16 x => toUInt32_Int16 ops x
  | .int .i32 x => toUInt32_Int32 ops x
  | .int .i64 x => toUInt32_Int64 ops x
  | .int .i128 x => toUInt32_Int128 ops x
  | .int .u8 x => toUInt32_UInt8 x
  | .int .u16 x => toUInt32_UInt16 x
  | .int .u32 x => toUInt32_UInt32 x
  | .int .u64 x => toUInt32_UInt64 ops x
  | .int .u128 x => toUInt32_UInt128 ops x
  | .bool x => toUInt32_Bool x
/-- `toUInt64(x)`: the method dispatch selects for `x`. -/
def toUInt64 : BuiltinInts → CoreM W L (JInt .u64)
  | .int .i8 x => toUInt64_Int8 ops x
  | .int .i16 x => toUInt64_Int16 ops x
  | .int .i32 x => toUInt64_Int32 ops x
  | .int .i64 x => toUInt64_Int64 ops x
  | .int .i128 x => toUInt64_Int128 ops x
  | .int .u8 x => toUInt64_UInt8 x
  | .int .u16 x => toUInt64_UInt16 x
  | .int .u32 x => toUInt64_UInt32 x
  | .int .u64 x => toUInt64_UInt64 x
  | .int .u128 x => toUInt64_UInt128 ops x
  | .bool x => toUInt64_Bool x
/-- `toUInt128(x)`: the method dispatch selects for `x`. -/
def toUInt128 : BuiltinInts → CoreM W L (JInt .u128)
  | .int .i8 x => toUInt128_Int8 ops x
  | .int .i16 x => toUInt128_Int16 ops x
  | .int .i32 x => toUInt128_Int32 ops x
  | .int .i64 x => toUInt128_Int64 ops x
  | .int .i128 x => toUInt128_Int128 ops x
  | .int .u8 x => toUInt128_UInt8 x
  | .int .u16 x => toUInt128_UInt16 x
  | .int .u32 x => toUInt128_UInt32 x
  | .int .u64 x => toUInt128_UInt64 x
  | .int .u128 x => toUInt128_UInt128 x
  | .bool x => toUInt128_Bool x
def Int8_ (x : BuiltinInts) : CoreM W L (JInt .i8) := toInt8 ops x
def Int16_ (x : BuiltinInts) : CoreM W L (JInt .i16) := toInt16 ops x
def Int32_ (x : BuiltinInts) : CoreM W L (JInt .i32) := toInt32 ops x
def Int64_ (x : BuiltinInts) : CoreM W L (JInt .i64) := toInt64 ops x
def Int128_ (x : BuiltinInts) : CoreM W L (JInt .i128) := toInt128 ops x
def UInt8_ (x : BuiltinInts) : CoreM W L (JInt .u8) := toUInt8 ops x
def UInt16_ (x : BuiltinInts) : CoreM W L (JInt .u16) := toUInt16 ops x
def UInt32_ (x : BuiltinInts) : CoreM W L (JInt .u32) := toUInt32 ops x
def UInt64_ (x : BuiltinInts) : CoreM W L (JInt .u64) := toUInt64 ops x
def UInt128_ (x : BuiltinInts) : CoreM W L (JInt .u128) := toUInt128 ops x

/--
Julia source: base/boot.jl:1195-1196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(x::T) where {T<:Number} = x

```
-/
def Number_identity (x : Value L) : Value L := x

/--
Julia source: base/boot.jl:1197-1198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Int(x::Ptr)  = bitcast(Int, x)
UInt(x::Ptr) = bitcast(UInt, x)
```
-/
def Int_Ptr (x : Value L) : CoreM W L (Value L) := ops.bitcastValue (coreV ops "Int64") x
def UInt_Ptr (x : Value L) : CoreM W L (Value L) := ops.bitcastValue (coreV ops "UInt64") x

/--
Julia source: base/boot.jl:1199-1202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Int === Int32
Int64(x::Ptr) = Int64(UInt32(x))
UInt64(x::Ptr) = UInt64(UInt32(x))
end
```
-/
-- These methods exist only where `Int === Int32`. There `UInt32(x::Ptr)` is the method
-- `UInt(x::Ptr) = bitcast(UInt32, x)`, so the pointer is given by its 32-bit address.
def Int64_Ptr32 (x : JInt .u32) : CoreM W L I64 := Int64_ ops (.int .u32 x)
def UInt64_Ptr32 (x : JInt .u32) : CoreM W L U64 := UInt64_ ops (.int .u32 x)

/--
Julia source: base/boot.jl:1203-1205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(PT::Type{Ptr{T}} where T)(x::Union{Int,UInt,Ptr}=0) = bitcast(PT, x)
(AS::Type{AddrSpace{Backend}} where Backend)(x::UInt8) = bitcast(AS, x)

```
-/
-- `PT` is the type `Ptr{T}` and `AS` the type `AddrSpace{Backend}`.
def Ptr_ (PT x : Value L) : CoreM W L (Value L) := ops.bitcastValue PT x
def Ptr_0 (PT : Value L) : CoreM W L (Value L) := Ptr_ ops PT (intV ops (JInt.lit .i64 0))
def AddrSpace (AS : Value L) (x : U8) : CoreM W L (Value L) := ops.bitcastValue AS (intV ops x)

/--
Julia source: base/boot.jl:1206-1216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Signed(x::UInt8)    = Int8(x)
Unsigned(x::Int8)   = UInt8(x)
Signed(x::UInt16)   = Int16(x)
Unsigned(x::Int16)  = UInt16(x)
Signed(x::UInt32)   = Int32(x)
Unsigned(x::Int32)  = UInt32(x)
Signed(x::UInt64)   = Int64(x)
Unsigned(x::Int64)  = UInt64(x)
Signed(x::UInt128)  = Int128(x)
Unsigned(x::Int128) = UInt128(x)

```
-/
def Signed_UInt8 (x : JInt .u8) : CoreM W L (JInt .i8) := Int8_ ops (.int .u8 x)
def Unsigned_Int8 (x : JInt .i8) : CoreM W L (JInt .u8) := UInt8_ ops (.int .i8 x)
def Signed_UInt16 (x : JInt .u16) : CoreM W L (JInt .i16) := Int16_ ops (.int .u16 x)
def Unsigned_Int16 (x : JInt .i16) : CoreM W L (JInt .u16) := UInt16_ ops (.int .i16 x)
def Signed_UInt32 (x : JInt .u32) : CoreM W L (JInt .i32) := Int32_ ops (.int .u32 x)
def Unsigned_Int32 (x : JInt .i32) : CoreM W L (JInt .u32) := UInt32_ ops (.int .i32 x)
def Signed_UInt64 (x : JInt .u64) : CoreM W L (JInt .i64) := Int64_ ops (.int .u64 x)
def Unsigned_Int64 (x : JInt .i64) : CoreM W L (JInt .u64) := UInt64_ ops (.int .i64 x)
def Signed_UInt128 (x : JInt .u128) : CoreM W L (JInt .i128) := Int128_ ops (.int .u128 x)
def Unsigned_Int128 (x : JInt .i128) : CoreM W L (JInt .u128) := UInt128_ ops (.int .i128 x)

/--
Julia source: base/boot.jl:1217-1219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Signed(x::Union{Float16, Float32, Float64, Bool})   = Int(x)
Unsigned(x::Union{Float16, Float32, Float64, Bool}) = UInt(x)

```
-/
-- `Int(x)` and `UInt(x)` are calls of the generic functions `Int64` and `UInt64`.
def Signed_Float (x : Value L) : CoreM W L (Value L) := ops.call (coreV ops "Int64") [x]
def Unsigned_Float (x : Value L) : CoreM W L (Value L) := ops.call (coreV ops "UInt64") [x]

/--
Julia source: base/boot.jl:1220-1222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Integer(x::Integer) = x
Integer(x::Union{Float16, Float32, Float64}) = Int(x)

```
-/
def Integer_Integer (x : Value L) : Value L := x
def Integer_Float (x : Value L) : CoreM W L (Value L) := ops.call (coreV ops "Int64") [x]

/--
Julia source: base/boot.jl:1223-1230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# During definition of struct type `B`, if an `A.B` expression refers to
# the eventual global name of the struct, then return the partially-initialized
# type object.
# TODO: remove. This is a shim for backwards compatibility.
function struct_name_shim(@nospecialize(x), name::Symbol, mod::Module, @nospecialize(t))
    return x === mod ? t : getfield(x, name)
end

```
-/
def struct_name_shim (x : Value L) (name : Sym) (mod t : Value L) : CoreM W L (Value L) :=
  if ops.same x mod then pure t else ops.getfield x (.symbol name)

/--
Julia source: base/boot.jl:1231-1251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Bindings for the julia frontend.  The internal jl_parse and jl_lower will call
# Core._parse and Core._lower respectively (if they are not `nothing`.)

#    Core._parse(text, filename, lineno, offset, options, edition)
#
# Parse Julia code from the buffer `text`, starting at `offset` and attributing
# it to `filename`. `options` should be one of `:atom`, `:statement` or `:all`,
# indicating how much the parser will consume.
#
# Return (ast, offset) containing an `Expr` (or `Syntax` on newer versions) and
# the new offset as an `Int`.
_parse = nothing

#    Core._lower(code, module, filename="none", linenum=0, world=0xfff..., warn=false)
#
# Lower `code` (usually Expr), returning `svec(e::Any xs::Any...)` where `e` is
# the lowered code, and `xs` is possible additional information from
# JuliaLowering (TBD).
_lower = nothing
_toplevel_eval = nothing

```
-/
-- The initial values of the globals `Core._parse`, `Core._lower` and `Core._toplevel_eval`.
def _parse : Value L := nothingV ops
def _lower : Value L := nothingV ops
def _toplevel_eval : Value L := nothingV ops

/--
Julia source: base/boot.jl:1252-1255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_setparser!(parser) = setglobal!(Core, :_parse, parser)
_setlowerer!(lowerer) = setglobal!(Core, :_lower, lowerer)
_set_toplevel_eval!(f) = setglobal!(Core, :_toplevel_eval, f)

```
-/
def _setparser! (parser : Value L) : CoreM W L (Value L) :=
  ops.setglobal (coreV ops "Core") "_parse" parser
def _setlowerer! (lowerer : Value L) : CoreM W L (Value L) :=
  ops.setglobal (coreV ops "Core") "_lower" lowerer
def _set_toplevel_eval! (f : Value L) : CoreM W L (Value L) :=
  ops.setglobal (coreV ops "Core") "_toplevel_eval" f

/--
Julia source: base/boot.jl:1256-1257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# support for deprecated uses of builtin functions
_apply(x...) = _apply_iterate(Main.Base.iterate, x...)
```
-/
def _apply (x : List (Value L)) : CoreM W L (Value L) := do
  ops.applyIterate (← baseFunction ops "iterate") x

-- Reason: These bind `_apply_pure` to `_apply` and `_call_latest` and `_call_in_world` to the builtins `invokelatest` and `invoke_in_world`; they define no method.
-- UNTRANSLATED
-- Source: base/boot.jl:1258-1261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const _apply_pure = _apply
-- const _call_latest = invokelatest
-- const _call_in_world = invoke_in_world
-- 
-- /Source

/--
Julia source: base/boot.jl:1262-1275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Pair{A, B}
    first::A
    second::B
    # if we didn't inline this, it's probably because the callsite was actually dynamic
    # to avoid potentially compiling many copies of this, we mark the arguments with `@nospecialize`
    # but also mark the whole function with `@inline` to ensure we will inline it whenever possible
    # (even if `convert(::Type{A}, a::A)` for some reason was expensive)
    Pair(a, b) = new{typeof(a), typeof(b)}(a, b)
    function Pair{A, B}(@nospecialize(a), @nospecialize(b)) where {A, B}
        @inline
        return new(a::A, b::B)
    end
end

```
-/
def Pair (a b : Value L) : CoreM W L (Value L) := do
  let A : Value L := .leaf (ops.typeOf a)
  let B : Value L := .leaf (ops.typeOf b)
  let self ← ops.applyType (coreV ops "Pair") [A, B]
  let first ← convertField ops self "first" a
  let second ← convertField ops self "second" b
  pure (objV ops (.pair A B first second))
def Pair_AB (A B a b : Value L) : CoreM W L (Value L) := do
  let a ← typeassert ops a A
  let b ← typeassert ops b B
  let self ← ops.applyType (coreV ops "Pair") [A, B]
  let first ← convertField ops self "first" a
  let second ← convertField ops self "second" b
  pure (objV ops (.pair A B first second))

/--
Julia source: base/boot.jl:1276-1282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hasmethod(@nospecialize(tt)) # this function has a special tfunc
    @nospecializeinfer
    @noinline
    world = ccall(:jl_get_tls_world_age, UInt, ()) # tls_world_age()
    return Intrinsics.not_int(ccall(:jl_gf_invoke_lookup, Any, (Any, Any, UInt), tt, nothing, world) === nothing)
end

```
-/
def _hasmethod (tt : Value L) : CoreM W L Bool := do
  let world ← ops.worldAge
  pure !(isNothingV ops (← ops.invokeLookup tt world))

/--
Julia source: base/boot.jl:1283-1288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# for backward compat
arrayref(inbounds::Bool, A::Array, i::Int...) = Main.Base.getindex(A, i...)
const_arrayref(inbounds::Bool, A::Array, i::Int...) = Main.Base.getindex(A, i...)
arrayset(inbounds::Bool, A::Array{T}, x::Any, i::Int...) where {T} = Main.Base.setindex!(A, x::T, i...)
arraysize(a::Array) = a.size
arraysize(a::Array, i::Int) = sle_int(i, nfields(a.size)) ? getfield(a.size, i) : 1
```
-/
def arrayref (_inbounds : Bool) (A : Value L) (i : List I64) : CoreM W L (Value L) := do
  ops.call (← baseFunction ops "getindex") (A :: i.map (intV ops))
def const_arrayref (_inbounds : Bool) (A : Value L) (i : List I64) : CoreM W L (Value L) := do
  ops.call (← baseFunction ops "getindex") (A :: i.map (intV ops))
/-- `T` is the element type of `A`. -/
def arrayset (_inbounds : Bool) (T A x : Value L) (i : List I64) : CoreM W L (Value L) := do
  let x ← typeassert ops x T
  ops.call (← baseFunction ops "setindex!") (A :: x :: i.map (intV ops))
def arraysize1 (a : Value L) : CoreM W L (Value L) := ops.getfield a (.symbol "size")
def arraysize2 (a : Value L) (i : I64) : CoreM W L (Value L) := do
  if sle_int i (ops.nfields (← ops.getfield a (.symbol "size"))) then
    ops.getfield (← ops.getfield a (.symbol "size")) (intV ops i)
  else pure (intV ops (JInt.lit .i64 1))

-- Reason: This binds `check_top_bit` to `check_sign_bit`; it defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:1289-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const check_top_bit = check_sign_bit
-- 
-- /Source

/--
Julia source: base/boot.jl:1291-1294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# For convenience
EnterNode(old::EnterNode, new_dest::Int) = isdefined(old, :scope) ?
    EnterNode(new_dest, old.scope) : EnterNode(new_dest)

```
-/
-- `old` is the `EnterNode` with destination `dest` and `scope` (`none` when undefined).
def EnterNode_old (_dest : I64) (scope : Option (Value L)) (new_dest : I64) : Value L :=
  match scope with
  | some s => EnterNode2 new_dest s
  | none => EnterNode1 new_dest

/--
Julia source: base/boot.jl:1295-1301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# typename(_).constprop_heuristic
const FORCE_CONST_PROP           = 0x01
const ARRAY_INDEX_HEURISTIC      = 0x02
const ITERATE_HEURISTIC          = 0x04
const SAMETYPE_HEURISTIC         = 0x08
const DISABLE_SEMI_CONCRETE_EVAL = 0x10

```
-/
def FORCE_CONST_PROP : U8 := JInt.lit .u8 0x01
def ARRAY_INDEX_HEURISTIC : U8 := JInt.lit .u8 0x02
def ITERATE_HEURISTIC : U8 := JInt.lit .u8 0x04
def SAMETYPE_HEURISTIC : U8 := JInt.lit .u8 0x08
def DISABLE_SEMI_CONCRETE_EVAL : U8 := JInt.lit .u8 0x10

/--
Julia source: base/boot.jl:1302-1319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `typename` has special tfunc support in inference to improve
# the result for `Type{Union{...}}`. It is defined here, so that the Compiler
# can look it up by value.
struct TypeNameError <: Exception
    a
    TypeNameError(@nospecialize(a)) = new(a)
end

typename(a) = throw(TypeNameError(a))
typename(a::DataType) = a.name
function typename(a::Union)
    ta = typename(a.a)
    tb = typename(a.b)
    ta === tb || throw(TypeNameError(a))
    return tb
end
typename(union::UnionAll) = typename(union.body)

```
-/
def TypeNameError (a : Value L) : Value L := objV ops (.typeNameError a)
/-- All four methods; `a.name`, `a.a`, `a.b` and `a.body` are `getfield` reads. -/
def typename (a : Value L) : CoreM W L (Value L) := do
  if ops.isa a (coreV ops "DataType") then
    return ← ops.getfield a (.symbol "name")
  if ops.isa a (coreV ops "Union") then
    let ta ← typename (← ops.getfield a (.symbol "a"))
    let tb ← typename (← ops.getfield a (.symbol "b"))
    if !ops.same ta tb then throw (TypeNameError ops a)
    return tb
  if ops.isa a (coreV ops "UnionAll") then
    return ← typename (← ops.getfield a (.symbol "body"))
  throw (TypeNameError ops a)
partial_fixpoint

/--
Julia source: base/boot.jl:1320-1324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Special inference support to avoid excess specialization of these methods.
# TODO: Replace this by a generic heuristic.
(>:)(@nospecialize(a), @nospecialize(b)) = (b <: a)
(!==)(@nospecialize(a), @nospecialize(b)) = Intrinsics.not_int(a === b)

```
-/
def supertype_op (a b : Value L) : CoreM W L Bool := ops.subtype b a
def not_egal (a b : Value L) : Bool := !ops.same a b

-- Reason: This `include` of `optimized_generics.jl` is load-time structure.
-- UNTRANSLATED
-- Source: base/boot.jl:1325-1326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- include(Core, "optimized_generics.jl")
-- 
-- /Source

/--
Julia source: base/boot.jl:1327-1330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const OLDEST_EDITION = (1, 13)
const VERSION_EDITION =
    (Int(ccall(:jl_ver_major, Int32, ())), Int(ccall(:jl_ver_minor, Int32, ())))

```
-/
def OLDEST_EDITION : I64 × I64 := (JInt.lit .i64 1, JInt.lit .i64 13)
def VERSION_EDITION : CoreM W L (I64 × I64) := do
  let major ← Int64_ ops (.int .i32 (← ops.verMajor))
  let minor ← Int64_ ops (.int .i32 (← ops.verMinor))
  pure (major, minor)

/--
Julia source: base/boot.jl:1331-1337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Used only by the magic @VERSION macro
struct MacroSource
    lno::Any # ::LineNumberNode, but needs to be a pointer
    syntax_ver::Any # ::VersionNumber =#
    MacroSource(@nospecialize(lno), @nospecialize(syntax_ver)) = new(lno, syntax_ver)
end

```
-/
def MacroSource (lno syntax_ver : Value L) : Value L := objV ops (.macroSource lno syntax_ver)

-- Reason: This call marks `Core` as the top module at load time; it defines no method.
-- UNTRANSLATED
-- Source: base/boot.jl:1338-1338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ccall(:jl_set_istopmod, Cvoid, (Any, Bool), Core, true)
-- /Source
end

end JuliaLean.base.boot


namespace JuliaLean.base.boot.Models2Group4

/-- Additive runtime boundary for the two-argument Core.isdefined builtin,
whose omission from CoreOps prevents full untyped callers from using it.
Arguments are universal values: Modules and ordinary objects, field symbols,
integer indices (including absent/out-of-range fields), and invalid selector
types. The builtin returns Bool, reports actual runtime failures as thrown
values, and uses its default memory ordering. CoreM preserves the world on a
failure and admits divergence. This boundary denotes the native builtin, not
a generic Julia helper or a replacement for the caller's algorithm. It adds
no fields to existing CoreOps and imposes no assumed correctness laws.
Julia source: base/boot.jl:247 (the Core builtin export);
base/docs/basedocs.jl:3014-3056 (the builtin's full field-selector contract).
Required only by base/loading.jl:2855-2865 in this proposal. -/
-- Source: base/docs/basedocs.jl:3014-3056 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     isdefined(m::Module, s::Symbol, [order::Symbol])
--     isdefined(object, s::Symbol, [order::Symbol])
--     isdefined(object, index::Int, [order::Symbol])
-- 
-- Tests whether a global variable or object field is defined. The arguments can
-- be a module and a symbol or a composite object and field name (as a symbol) or
-- index. Optionally, an ordering can be defined for the operation. If the field
-- was declared `@atomic`, the specification is strongly recommended to be
-- compatible with the stores to that location. Otherwise, if not declared as
-- `@atomic`, this parameter must be `:not_atomic` if specified.
-- 
-- To test whether an array element is defined, use [`isassigned`](@ref) instead.
-- 
-- The global variable variant is supported for compatibility with older julia
-- releases. For new code, prefer [`isdefinedglobal`](@ref).
-- 
-- See also [`@isdefined`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> isdefined(Base, :sum)
-- true
-- 
-- julia> isdefined(Base, :NonExistentMethod)
-- false
-- 
-- julia> a = 1//2;
-- 
-- julia> isdefined(a, 2)
-- true
-- 
-- julia> isdefined(a, 3)
-- false
-- 
-- julia> isdefined(a, :num)
-- true
-- 
-- julia> isdefined(a, :numerator)
-- false
-- ```
-- """
-- isdefined
-- /Source
structure IsDefinedOps (W L : Type) where
  isdefined : JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L →
    JuliaLean.base.boot.CoreM W L Bool

end JuliaLean.base.boot.Models2Group4



namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Identity-preserving construction model for the small Core macros at
`base/boot.jl:324-367`. Expr objects and their `Vector{Any}` argument containers
have separate, tagged logical identities. Natural-number identities are heap
names, not Julia integers or physical addresses. They can be consistently renamed
without changing an observation. Existing heaps can contain shared references,
cycles, and undefined fields or slots; the macros never dereference their input.

The `other` constructor ranges over all remaining Julia values, retaining their
identity and representation through `L`. It is disjoint from Core, Bool, Symbol,
and the tracked Expr/vector references; those values have their unique tagged
representations below. No operation dispatches on an `other` value here.

Each allocation creates a fresh Expr and a fresh argument vector as a semantic
pair. This records language-visible identity and sharing, not an order for the
runtime's physical allocations. The model abstracts GC, physical addresses, and
resource exhaustion. Each vector still obeys Julia's native-Int size invariant.
The needed calls all have Symbol heads and at most eleven arguments, so none has
an argument-count, type, or size error. This dependency is not a model of the
unrestricted `Expr(args...)` row at line 327 and makes no claim about that row's
invalid-head or missing-head error paths.
-/

/-- A Julia Symbol's raw name bytes, including non-UTF-8 names.
Representation support for `base/boot.jl:324-367`; Symbol interning is described
at `base/docs/basedocs.jl:2563-2564`. A validity predicate can exclude NUL bytes;
the fixed symbols constructed below are all valid ASCII names. -/
-- Source: base/boot.jl:324-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro nospecialize(x)
--     _expr(:escape, _expr(:meta, :nospecialize, x))
-- end
-- Expr(@nospecialize args...) = _expr(args...)
-- /Source
abbrev SymbolName := List UInt8

/-- Encode an ASCII source symbol spelling. This helper is used only for fixed
source literals in `base/boot.jl:324-367`; runtime symbols use `SymbolName`
directly, so they are not restricted to Lean's valid-UTF-8 Strings. -/
-- Source: base/boot.jl:324-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro nospecialize(x)
--     _expr(:escape, _expr(:meta, :nospecialize, x))
-- end
-- Expr(@nospecialize args...) = _expr(args...)
-- /Source
def symbolName (name : String) : SymbolName := name.toByteArray.toList

/-- Julia values relevant to `base/boot.jl:324-367`. Distinct `exprRef` and
`argsRef` tags give Expr objects and `Vector{Any}` containers separate identity
spaces. `other` preserves every other value without inspection or conversion. -/
inductive Value (L : Type) where
  | other (value : L)
  | coreModule
  | bool (value : Bool)
  | symbol (name : SymbolName)
  | exprRef (ref : Nat)
  | argsRef (ref : Nat)

/-- A native-sized `Vector{Any}`, the concrete field type of Expr.args documented
at `base/docs/basedocs.jl:715-719`, used by `base/boot.jl:324-367`.
`none` is an undefined slot in an already-existing vector; fresh vectors contain
only initialized slots. This representation bound is not a runtime branch. -/
structure VectorAny (L : Type) where
  data : List (Option (Value L))
  size_ok : data.length ≤ IntTy.i64.max.toNat

/-- An Expr's two mutable fields, for `base/boot.jl:324-367` and
`base/docs/basedocs.jl:715-719`. Optional fields represent existing uninitialized
objects; the constructor below always initializes both fields. -/
structure ExprCell where
  head : Option SymbolName
  args : Option Nat

/-- Heap graph for the concrete Expr construction needed at
`base/boot.jl:324-367`. It admits shared argument containers and cycles.
Appending new cells leaves every previous object and identity intact. -/
structure Heap (L : Type) where
  expressions : List ExprCell
  argsVectors : List (VectorAny L)

/-- Allocation state for the fixed, valid Expr calls at `base/boot.jl:324-367`.
There are no source-visible failing checks in these valid-head calls. -/
-- Source: base/boot.jl:324-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro nospecialize(x)
--     _expr(:escape, _expr(:meta, :nospecialize, x))
-- end
-- Expr(@nospecialize args...) = _expr(args...)
-- /Source
abbrev MacroM (L α : Type) := StateM (Heap L) α

/-- Observation of an Expr heap cell; this is a specification observer, not a
replacement for a Julia getfield method. Used for the construction behavior at
`base/boot.jl:324-367`. -/
-- Source: base/boot.jl:952-953 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- iscallexpr(ex) = false
-- /Source
def readExpr {L : Type} (heap : Heap L) (ref : Nat) : Option ExprCell :=
  heap.expressions[ref]?

/-- Observation of an Expr argument container; this is a specification observer
for `base/boot.jl:324-367`, not a Julia indexing method or Julia index arithmetic. -/
-- Source: base/boot.jl:952-953 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- iscallexpr(ex) = false
-- /Source
def readArgs {L : Type} (heap : Heap L) (ref : Nat) : Option (VectorAny L) :=
  heap.argsVectors[ref]?

/-- Concrete `_expr` allocation for a known Symbol head and initialized,
native-sized argument tuple, as needed by `base/boot.jl:324-367`. The Expr
constructor's valid-head behavior is documented at
`base/docs/basedocs.jl:712-719`. Every argument value is stored without copying
its referent; the newly allocated Expr and vector have fresh logical identities.
This is a necessary runtime dependency, not coverage of general Expr row 327.
Its pair of appended cells is a semantic allocation, not a physical-order claim. -/
-- Source: base/boot.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Expr(@nospecialize args...) = _expr(args...)
-- /Source
def allocExpr {L : Type} (head : SymbolName) (args : List (Value L))
    (size_ok : args.length ≤ IntTy.i64.max.toNat) : MacroM L (Value L) :=
  fun heap =>
    let vector : VectorAny L :=
      { data := args.map some
        size_ok := by simpa only [List.length_map] using size_ok }
    let cell : ExprCell :=
      { head := some head, args := some heap.argsVectors.length }
    (.exprRef heap.expressions.length,
      { expressions := heap.expressions ++ [cell]
        argsVectors := heap.argsVectors ++ [vector] })

/-- `@nospecialize(x)` builds its inner metadata before its outer escape node,
retaining the exact argument value, including any existing object identity.
Source reference: `base/boot.jl:324-326`. -/
-- Source: base/boot.jl:324-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro nospecialize(x)
--     _expr(:escape, _expr(:meta, :nospecialize, x))
-- end
-- /Source
def nospecializeMacro {L : Type} (x : Value L) : MacroM L (Value L) := do
  let inner ← allocExpr (symbolName "meta") [.symbol (symbolName "nospecialize"), x]
    (by simp only [List.length_cons, List.length_nil]; decide)
  allocExpr (symbolName "escape") [inner] (by simp only [List.length_cons, List.length_nil]; decide)

/-- `@latestworld` constructs a fresh marker expression with no arguments.
Source reference: `base/boot.jl:329`. -/
-- Source: base/boot.jl:329-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro latestworld() Expr(:latestworld) end
-- /Source
def latestworldMacro {L : Type} : MacroM L (Value L) :=
  allocExpr (symbolName "latestworld") [] (by simp only [List.length_nil]; decide)

/-- `_is_internal` uses Core's actual identity, without an unconstrained
equality callback. Julia source: `base/boot.jl:331`. -/
-- Source: base/boot.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _is_internal(__module__) = __module__ === Core
-- /Source
def isInternal {L : Type} : Value L → Bool
  | .coreModule => true
  | _ => false

/-- `@_total_meta` short-circuits outside Core. In Core it constructs the purity
node before the enclosing metadata node, preserving the eleven source flags.
Source reference: `base/boot.jl:333-346`. -/
-- Source: base/boot.jl:333-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _total_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#true,
--         #=:effect_free=#true,
--         #=:nothrow=#true,
--         #=:terminates_globally=#true,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#true,
--         #=:inaccessiblememonly=#true,
--         #=:noub=#true,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#true))
-- end
-- /Source
def totalMetaMacro {L : Type} (mod : Value L) : MacroM L (Value L) := do
  if isInternal mod then
    let purity ← allocExpr (symbolName "purity")
      [.bool true, .bool true, .bool true, .bool true, .bool false,
       .bool true, .bool true, .bool true, .bool false, .bool false, .bool true]
      (by simp only [List.length_cons, List.length_nil]; decide)
    allocExpr (symbolName "meta") [purity] (by simp only [List.length_cons, List.length_nil]; decide)
  else
    pure (.bool false)

/-- `@_foldable_meta` short-circuits outside Core. In Core it builds the purity
node before the enclosing metadata node; its nothrow flag is false.
Source reference: `base/boot.jl:348-361`. -/
-- Source: base/boot.jl:348-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _foldable_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#true,
--         #=:effect_free=#true,
--         #=:nothrow=#false,
--         #=:terminates_globally=#true,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#true,
--         #=:inaccessiblememonly=#true,
--         #=:noub=#true,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#true))
-- end
-- /Source
def foldableMetaMacro {L : Type} (mod : Value L) : MacroM L (Value L) := do
  if isInternal mod then
    let purity ← allocExpr (symbolName "purity")
      [.bool true, .bool true, .bool false, .bool true, .bool false,
       .bool true, .bool true, .bool true, .bool false, .bool false, .bool true]
      (by simp only [List.length_cons, List.length_nil]; decide)
    allocExpr (symbolName "meta") [purity] (by simp only [List.length_cons, List.length_nil]; decide)
  else
    pure (.bool false)

/-- Zero-argument `@inline` constructs its metadata marker.
Source reference: `base/boot.jl:363`. -/
-- Source: base/boot.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro inline()      Expr(:meta, :inline)      end
-- /Source
def inlineMacro {L : Type} : MacroM L (Value L) :=
  allocExpr (symbolName "meta") [.symbol (symbolName "inline")] (by simp only [List.length_cons, List.length_nil]; decide)

/-- Zero-argument `@noinline` constructs its metadata marker.
Source reference: `base/boot.jl:364`. -/
-- Source: base/boot.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro noinline()    Expr(:meta, :noinline)    end
-- /Source
def noinlineMacro {L : Type} : MacroM L (Value L) :=
  allocExpr (symbolName "meta") [.symbol (symbolName "noinline")] (by simp only [List.length_cons, List.length_nil]; decide)

/-- `@nospecializeinfer` constructs its metadata marker.
Source reference: `base/boot.jl:365`. -/
-- Source: base/boot.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro nospecializeinfer() Expr(:meta, :nospecializeinfer) end
-- /Source
def nospecializeinferMacro {L : Type} : MacroM L (Value L) :=
  allocExpr (symbolName "meta") [.symbol (symbolName "nospecializeinfer")] (by simp only [List.length_cons, List.length_nil]; decide)

/-- `@_boundscheck` constructs its zero-argument marker.
Source reference: `base/boot.jl:367`. -/
-- Source: base/boot.jl:367-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _boundscheck() Expr(:boundscheck) end
-- /Source
def boundscheckMacro {L : Type} : MacroM L (Value L) :=
  allocExpr (symbolName "boundscheck") [] (by simp only [List.length_nil]; decide)

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Typed immutable constructors at `base/boot.jl:472-599`, preserving the existing
`Obj L` representation. Each function models the body after its Julia method has
been selected: its source-typed parameters already satisfy the indicated
`AbstractString`, `Symbol`, `MethodInstance`, `DataType`, or `Type` signature.
The complete domains, including custom AbstractString subtypes and non-UTF-8
symbols, are preserved as uninterpreted `expr.Value L` payloads. In particular,
mutable input objects may be opaque `.leaf` identity handles; none is inspected,
reconstructed, or converted. The model bodies are also defined on the wider Lean
payload type, without asserting that Julia dispatch accepts those extra values.

For each typed field, the selected method's input already has the field type;
the `isa` fast path of lowered `new` stores it directly. See the explicit
convert-for-type-declaration pattern at `base/essentials.jl:1468-1488`.
All Any fields likewise retain the supplied value directly. These additions do
not invoke the baseline's unconditional `cf` conversion or any runtime callback.

`CoreOps.str`, `.int`, and `.tuple` below are pure representation embeddings
already present in the baseline, not arbitrary implementations of Julia calls.
Every property quantifies over all embeddings, with no correctness laws.
The empty String literal, machine integers, and already-formed varargs tuple are
encoded through those fields. `Obj` is returned transparently so its fields can
be observed without depending on the arbitrary `CoreOps.obj` embedding.

As in the existing `Obj` model, physical storage and allocation exhaustion are
abstracted. The source has no user-visible allocation identity for these
immutable wrappers; stored references retain their original identity.
-/

/-- An already-evaluated Julia varargs tuple for `base/boot.jl:542`.
Its native-Int arity bound is a representation invariant, not an extra source
check or a numeric replacement for Julia arithmetic. Tuple elements may be
arbitrary Julia values, and their order and identities are retained. -/
structure ConstructorTuple (L : Type) where
  values : List (JuliaLean.base.expr.Value L)
  size_ok : values.length ≤ IntTy.i64.max.toNat

/-- Store the accepted AbstractString object itself in ErrorException.msg.
Source reference: `base/boot.jl:472`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ErrorException(msg::AbstractString) = new(msg)
-- /Source
def errorExceptionCtor {L : Type} (msg : JuliaLean.base.expr.Value L) : Obj L :=
  .errorException msg

/-- Store the accepted AbstractString object itself in ConcurrencyViolationError.msg.
Source reference: `base/boot.jl:509`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ConcurrencyViolationError(msg::AbstractString) = new(msg)
-- /Source
def concurrencyViolationCtor {L : Type} (msg : JuliaLean.base.expr.Value L) : Obj L :=
  .concurrencyViolationError msg

/-- Store the accepted MethodInstance unchanged in MissingCodeError.mi.
Source reference: `base/boot.jl:513`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:513-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     MissingCodeError(mi::MethodInstance) = new(mi)
-- /Source
def missingCodeCtor {L : Type} (mi : JuliaLean.base.expr.Value L) : Obj L :=
  .missingCodeError mi

/-- Preserve the offending value and initialize DomainError.msg to the empty String.
Source reference: `base/boot.jl:521`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:521-521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     DomainError(@nospecialize(val)) = (@noinline; new(val, ""))
-- /Source
def domainErrorDefaultCtor {W L : Type} (ops : CoreOps W L) (val : JuliaLean.base.expr.Value L) : Obj L :=
  .domainError val (strV ops "")

/-- Preserve the function Symbol and the complete, ordered, native-sized varargs tuple in InexactError.
Source reference: `base/boot.jl:542`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     InexactError(f::Symbol, @nospecialize(args...)) = (@noinline; new(f, args))
-- /Source
def inexactErrorCtor {W L : Type} (ops : CoreOps W L) (f : JuliaLean.base.expr.Value L) (args : ConstructorTuple L) : Obj L :=
  .inexactError f (tupleV ops args.values)

/-- Store the accepted AbstractString object itself in OverflowError.msg.
Source reference: `base/boot.jl:546`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:546-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     OverflowError(msg::AbstractString) = new(msg)
-- /Source
def overflowErrorCtor {L : Type} (msg : JuliaLean.base.expr.Value L) : Obj L :=
  .overflowError msg

/-- Store the accepted AbstractString object itself in ArgumentError.msg.
Source reference: `base/boot.jl:551`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:551-551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ArgumentError(msg::AbstractString) = new(msg)
-- /Source
def argumentErrorCtor {L : Type} (msg : JuliaLean.base.expr.Value L) : Obj L :=
  .argumentError msg

/-- Store the accepted Symbol itself in UndefKeywordError.var.
Source reference: `base/boot.jl:555`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     UndefKeywordError(var::Symbol) = new(var)
-- /Source
def undefKeywordCtor {L : Type} (var : JuliaLean.base.expr.Value L) : Obj L :=
  .undefKeywordError var

/-- Preserve the function, argument value, and every native UInt world in MethodError.
Source reference: `base/boot.jl:565`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:565-565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     MethodError(@nospecialize(f), @nospecialize(args), world::UInt) = new(f, args, world)
-- /Source
def methodErrorCtor {W L : Type} (ops : CoreOps W L) (f args : JuliaLean.base.expr.Value L) (world : JInt .u64) : Obj L :=
  .methodError f args (intV ops world)

/-- Store the accepted AbstractString object itself in AssertionError.msg.
Source reference: `base/boot.jl:571`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:571-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     AssertionError(msg::AbstractString) = (@noinline; new(msg))
-- /Source
def assertionErrorCtor {L : Type} (msg : JuliaLean.base.expr.Value L) : Obj L :=
  .assertionError msg

/-- The zero-argument AssertionError initializes its message to the empty String.
Source reference: `base/boot.jl:573`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- AssertionError() = (@noinline; AssertionError(""))
-- /Source
def assertionErrorDefaultCtor {W L : Type} (ops : CoreOps W L) : Obj L :=
  assertionErrorCtor (strV ops "")

/-- Preserve the accepted DataType and field Symbol as FieldError.type and FieldError.field.
Source reference: `base/boot.jl:578`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:578-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     FieldError(type::DataType, field::Symbol) = new(type, field)
-- /Source
def fieldErrorCtor {L : Type} (typ field : JuliaLean.base.expr.Value L) : Obj L :=
  .fieldError typ field

/-- Preserve the accepted AbstractString filename, every native Int line, and the wrapped error in LoadError.
Source reference: `base/boot.jl:587`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:587-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     LoadError(file::AbstractString, line::Int, @nospecialize(error)) = new(file, line, error)
-- /Source
def loadErrorCtor {W L : Type} (ops : CoreOps W L) (file : JuliaLean.base.expr.Value L) (line : JInt .i64) (error : JuliaLean.base.expr.Value L) : Obj L :=
  .loadError file (intV ops line) error

/-- Preserve the accepted module-name Symbol and the wrapped error in InitError.
Source reference: `base/boot.jl:593`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:593-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     InitError(mod::Symbol, @nospecialize(error)) = new(mod, error)
-- /Source
def initErrorCtor {L : Type} (mod error : JuliaLean.base.expr.Value L) : Obj L :=
  .initError mod error

/-- Preserve the accepted Type and MethodInstance in ABIOverride.abi and ABIOverride.def.
Source reference: `base/boot.jl:599`. Source-typed parameters are already
accepted by dispatch, so lowered `new` performs no conversion on these fields. -/
-- Source: base/boot.jl:599-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ABIOverride(@nospecialize(abi::Type), def::MethodInstance) = new(abi, def)
-- /Source
def abiOverrideCtor {L : Type} (abi defn : JuliaLean.base.expr.Value L) : Obj L :=
  .abiOverride abi defn

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Additional source-typed constructors. The source dispatch constraints already
ensure the field types. The concrete isa fast path of lowered new, documented
at base/essentials.jl:1468-1488, stores these values directly. The arbitrary
expr.Value payloads retain opaque Julia identities; they are not inspected or
copied. The functions are defined on a wider Lean carrier, but no claim is made
that Julia dispatch accepts values outside the source signature.
-/

/-- Store the actual Module identity in the callable EvalInto wrapper.
Source reference: base/boot.jl:624. This models its constructor, not evaluation. -/
-- Source: base/boot.jl:624-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     EvalInto(m::Module) = new(m)
-- /Source
def evalIntoCtor {L : Type} (mod : JuliaLean.base.expr.Value L) : Obj L :=
  .evalInto mod

/-- The already-dispatched type parameter T is retained with its value.
There is no type-application call or converting constructor in this body.
Source reference: base/boot.jl:647. -/
-- Source: base/boot.jl:647-647 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     VecElement{T}(value::T) where {T} = new(value) # disable converting constructor in Core
-- /Source
def vecElementTypedCtor {L : Type} (T value : JuliaLean.base.expr.Value L) : Obj L :=
  .vecElement T value

/-- Store the complete native-Int slot and both arbitrary type values.
Source reference: base/boot.jl:671. -/
-- Source: base/boot.jl:671-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     InterConditional(slot::Int, @nospecialize(thentype), @nospecialize(elsetype)) = new(slot, thentype, elsetype)
-- /Source
def interConditionalCtor {W L : Type} (ops : CoreOps W L) (slot : JInt .i64)
    (thentype elsetype : JuliaLean.base.expr.Value L) : Obj L :=
  .interConditional (intV ops slot) thentype elsetype

/-- Preserve both native-Int fields and the arbitrary type/variable payloads.
Source reference: base/boot.jl:679. -/
-- Source: base/boot.jl:679-679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     InterMustAlias(slot::Int, @nospecialize(vartyp), fldidx::Int, @nospecialize(fldtyp)) = new(slot, vartyp, fldidx, fldtyp)
-- /Source
def interMustAliasCtor {W L : Type} (ops : CoreOps W L) (slot : JInt .i64)
    (vartyp : JuliaLean.base.expr.Value L) (fldidx : JInt .i64)
    (fldtyp : JuliaLean.base.expr.Value L) : Obj L :=
  .interMustAlias (intV ops slot) vartyp (intV ops fldidx) fldtyp

/-- Preserve the Module and Symbol identities and the full Int32 ranges.
Source reference: base/boot.jl:736. -/
-- Source: base/boot.jl:736-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     LineInfoNode(mod::Module, @nospecialize(method), file::Symbol, line::Int32, inlined_at::Int32) = new(mod, method, file, line, inlined_at)
-- /Source
def lineInfoCtor {W L : Type} (ops : CoreOps W L)
    (mod method file : JuliaLean.base.expr.Value L) (line inlinedAt : JInt .i32) : Obj L :=
  .lineInfoNode mod method file (intV ops line) (intV ops inlinedAt)

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

/-!
Concrete mutable-Box allocation for the two constructors in base/boot.jl.
The logical store is not a Julia array; its Nat addresses are object names,
not Julia machine integers or physical addresses. The unrestricted carrier V
represents actual Julia values, including references to pre-existing mutable
objects. A stored V is preserved without conversion or copying its referent.
Physical allocation, GC and resource exhaustion are abstracted, as in the
macro-construction model. There is no user dispatch or callback in either body.

PhiNode, PiNode and PhiCNode are immutable in the pinned source. Their faithful
BootCov.Objects models are reused rather than given mutable node identities.
Their array-valued fields retain opaque input identities, not copied contents.
-/

/-- A logical identity of a mutable Core.Box object. Nat is a heap name, not
a Julia integer. Representation support for base/boot.jl:628-632.
-/
structure BoxHandle where
  ref : Nat
  deriving Repr, DecidableEq

/-- A finite store of Box contents. An existing cell may be undefined (`none`)
or contain any Julia value (`some v`), including aliased object references.
This is a ghost store of objects, not a machine-sized Julia array.
Representation support for base/boot.jl:628-632.
-/
-- Source: base/boot.jl:628-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct Box
--     contents::Any
--     Box(@nospecialize(x)) = new(x)
--     Box() = new()
-- end
-- /Source
abbrev BoxHeap (V : Type) := List (Option V)

/-- Box(x) allocates a fresh mutable object and initializes its Any field with
the original x, preserving every previously allocated Box. The argument's
referent is not inspected or copied. Julia source: base/boot.jl:630.
-/
-- Source: base/boot.jl:628-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct Box
--     contents::Any
--     Box(@nospecialize(x)) = new(x)
--     Box() = new()
-- end
-- /Source
def boxWithValue {V : Type} (x : V) : StateM (BoxHeap V) BoxHandle :=
  fun heap => (⟨heap.length⟩, heap ++ [some x])

/-- Box() allocates a fresh mutable object with its reference field undefined.
It does not replace the absent value by nothing or another default.
Source reference: base/boot.jl:631.
-/
-- Source: base/boot.jl:628-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct Box
--     contents::Any
--     Box(@nospecialize(x)) = new(x)
--     Box() = new()
-- end
-- /Source
def boxWithoutValue {V : Type} : StateM (BoxHeap V) BoxHandle :=
  fun heap => (⟨heap.length⟩, heap ++ [none])

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-- The current task's relevant runtime metadata. The native UInt world age and
the native-width TLS pointer are concrete state fields, not callbacks. `rest`
retains all unrelated runtime state. The primitive reads below do not schedule
another task or mutate any field. Source context: base/boot.jl:500-505,617;
the pinned jl_get_ptls_states body is preserved in JuliaLean/src/threading_c.lean
and returns jl_current_task->ptls directly. -/
structure ThreadState (W : Type) where
  worldAge : JInt .u64
  ptls : JuliaLean.BootCov.IntConv.Ptr
  rest : W

/-- Concrete current-task world-age read required by both UndefVarError
constructors. It returns the task's native UInt metadata and retains all state.
This is a local runtime dependency, not a supplied implementation of a call.
Source reference: base/boot.jl:504-505 (jl_get_tls_world_age ccall). -/
-- Source: base/boot.jl:504-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     UndefVarError(var::Symbol) = new(var, ccall(:jl_get_tls_world_age, UInt, ()))
--     UndefVarError(var::Symbol, @nospecialize scope) = new(var, ccall(:jl_get_tls_world_age, UInt, ()), scope)
-- /Source
def readWorldAge {W : Type} : StateM (ThreadState W) (JInt .u64) :=
  fun state => (state.worldAge, state)

/-- Preserve the Symbol, read the current native UInt world age, and leave
scope undefined. The Symbol already satisfies its field type at dispatch.
Source reference: base/boot.jl:504. -/
-- Source: base/boot.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     UndefVarError(var::Symbol) = new(var, ccall(:jl_get_tls_world_age, UInt, ()))
-- /Source
def undefVarErrorCtor {W L : Type} (ops : CoreOps W L)
    (var : JuliaLean.base.expr.Value L) : StateM (ThreadState W) (Obj L) := do
  let world ← readWorldAge
  pure (.undefVarError var (intV ops world) none)

/-- The scope-taking UndefVarError preserves every scope value and records
the current task's native UInt world, without conversion or mutation.
Source reference: base/boot.jl:505. -/
-- Source: base/boot.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     UndefVarError(var::Symbol, @nospecialize scope) = new(var, ccall(:jl_get_tls_world_age, UInt, ()), scope)
-- /Source
def undefVarErrorScopeCtor {W L : Type} (ops : CoreOps W L)
    (var scope : JuliaLean.base.expr.Value L) : StateM (ThreadState W) (Obj L) := do
  let world ← readWorldAge
  pure (.undefVarError var (intV ops world) (some scope))

/-- The native TLS pointer is read from the current task without allocation or
mutation. Concrete dependency: src/threading.c's jl_get_ptls_states returns
jl_current_task->ptls, as preserved in JuliaLean/src/threading_c.lean:63-67.
Source reference: base/boot.jl:617. -/
-- Source: base/boot.jl:617-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getptls() = ccall(:jl_get_ptls_states, Ptr{Cvoid}, ())
-- /Source
def getPtls {W : Type} : StateM (ThreadState W) JuliaLean.BootCov.IntConv.Ptr :=
  fun state => (state.ptls, state)

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Complete TypeVar constructor bodies for `base/boot.jl:370-372` and their
necessary concrete `_typevar` runtime dependency. The latter follows the pinned
`src/builtins.c:2210-2224` source retained verbatim in
`JuliaLean/src/jltypes_c.lean`. Type predicates are represented by disjoint
runtime-kind tags, not by arbitrary callbacks. Types with free variables remain
types; no lower/upper subtype relation or closedness condition is imposed.

TypeVar has object identity even though its name/lb/ub fields are const
(src/jltypes.c:3713-3719). Every successful construction receives a fresh logical
identity and stores its original name and bound references. The representation
conservatively permits shared/cyclic references and undefined old fields; the
constructor does not inspect or change any old cell. No field-mutation method
or claim that those extra states are reachable is introduced. Natural-number references are abstract object
names, not Julia integers, pointer values, or machine arithmetic. Physical
allocation, GC, and resource exhaustion are abstracted as for the other local
construction models. All source-visible validation failures are explicit.

The opaque carrier `L` covers every payload not inspected here. Tags are
disjoint representations of actual runtime kinds: `typeValue` contains the
remaining Julia types, `typeApp` contains Core.TypeApp objects (which are not
types), and `other` contains all remaining non-types. A bound that is an existing
TypeVar uses `typevarRef`, so its mutable identity is retained independently of
the contents of its current fields.
-/

/-- An interned Symbol name accepted by `TypeVar` at `base/boot.jl:370-372`.
Raw bytes include non-UTF-8 Symbol names. The absence of NUL and native-sized
length are representation invariants, not new constructor checks. Symbol's
byte-name rule is documented by `base/boot.jl:858-873` and the installed
`JuliaLean.base.boot._Symbol` model. -/
structure TypeVarName where
  bytes : List UInt8
  noNul : (0 : UInt8) ∉ bytes
  nativeSize : bytes.length ≤ IntTy.i64.max.toNat

/-- Runtime-kind and identity observations used by `base/boot.jl:370-372` and
`src/builtins.c:2210-2224`. `typeValue` includes types with arbitrary free type
variables. `typeApp` is deliberately separate from every accepted bound kind. -/
inductive TypeVarValue (L : Type) where
  | symbol (name : TypeVarName)
  | bottom
  | anyType
  | typeValue (value : L)
  | typevarRef (ref : Nat)
  | typeApp (value : L)
  | other (value : L)

/-- The three const fields initialized by `jl_new_typevar`
(`src/builtins.c:2210-2224`). Existing cells may have undefined fields; every new
cell is fully initialized. Bound fields retain exact value/reference payloads. -/
structure TypeVarCell (L : Type) where
  name : Option TypeVarName
  lower : Option (TypeVarValue L)
  upper : Option (TypeVarValue L)

/-- The TypeVar objects of a runtime state. Append-only construction preserves
all pre-existing object identities and stored fields. Other runtime objects are
opaque payloads whose state this constructor does not access.
Source reference: `base/boot.jl:370-372`; `src/builtins.c:2210-2224`. -/
structure TypeVarHeap (L : Type) where
  cells : List (TypeVarCell L)

/-- The concrete expected types in the TypeErrors raised by these methods.
The runtime says `Type` even though it separately accepts TypeVar bounds.
Source reference: `base/boot.jl:370-372`; `src/builtins.c:2210-2224`. -/
inductive TypeVarExpected where
  | symbol
  | type
  deriving DecidableEq

/-- A refined payload for the existing `BootCov.Exc.typeError` exception class.
`context`, `expected`, and `got` retain the distinctions required to observe
name-before-bounds and lower-before-upper error order. This introduces no new
Julia exception class. -/
structure TypeVarError (L : Type) where
  exception : JuliaLean.BootCov.Exc
  context : String
  expected : TypeVarExpected
  got : TypeVarValue L

/-- State and exceptions through the existing `MonadExceptOf`/`MonadStateOf`
interfaces. The state remains observable on failure, so validation's absence of
allocation is part of the model. -/
-- Source: base/boot.jl:370-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- TypeVar(@nospecialize(n)) = _typevar(n::Symbol, Union{}, Any)
-- TypeVar(@nospecialize(n), @nospecialize(ub)) = _typevar(n::Symbol, Union{}, ub)
-- TypeVar(@nospecialize(n), @nospecialize(lb), @nospecialize(ub)) = _typevar(n::Symbol, lb, ub)
-- /Source
abbrev TypeVarM (L A : Type) := ExceptT (TypeVarError L) (StateM (TypeVarHeap L)) A

/-- Concrete identity test against `jl_bottom_type`, used in
`src/builtins.c:2210-2224`. -/
-- Source: src/builtins.c:2210-2224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_tvar_t *jl_new_typevar(jl_sym_t *name, jl_value_t *lb, jl_value_t *ub)
-- {
--     if (lb != jl_bottom_type && !jl_is_type(lb) && !jl_is_typevar(lb))
--         jl_type_error_rt("TypeVar", "lower bound", (jl_value_t *)jl_type_type, lb);
--     if (ub != (jl_value_t *)jl_any_type && !jl_is_type(ub) && !jl_is_typevar(ub))
--         jl_type_error_rt("TypeVar", "upper bound", (jl_value_t *)jl_type_type, ub);
--     jl_task_t *ct = jl_current_task;
--     jl_tvar_t *tv = (jl_tvar_t *)jl_gc_alloc(ct->ptls, sizeof(jl_tvar_t), jl_tvar_type);
--     jl_set_typetagof(tv, jl_tvar_tag, 0);
--     tv->name = name;
--     tv->lb = lb;
--     tv->ub = ub;
--     return tv;
-- }
-- 
-- /Source
def typeVarIsBottom {L : Type} : TypeVarValue L → Bool
  | .bottom => true
  | _ => false

/-- Concrete identity test against `jl_any_type`, used in
`src/builtins.c:2210-2224`. -/
-- Source: src/builtins.c:2210-2224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_tvar_t *jl_new_typevar(jl_sym_t *name, jl_value_t *lb, jl_value_t *ub)
-- {
--     if (lb != jl_bottom_type && !jl_is_type(lb) && !jl_is_typevar(lb))
--         jl_type_error_rt("TypeVar", "lower bound", (jl_value_t *)jl_type_type, lb);
--     if (ub != (jl_value_t *)jl_any_type && !jl_is_type(ub) && !jl_is_typevar(ub))
--         jl_type_error_rt("TypeVar", "upper bound", (jl_value_t *)jl_type_type, ub);
--     jl_task_t *ct = jl_current_task;
--     jl_tvar_t *tv = (jl_tvar_t *)jl_gc_alloc(ct->ptls, sizeof(jl_tvar_t), jl_tvar_type);
--     jl_set_typetagof(tv, jl_tvar_tag, 0);
--     tv->name = name;
--     tv->lb = lb;
--     tv->ub = ub;
--     return tv;
-- }
-- 
-- /Source
def typeVarIsAny {L : Type} : TypeVarValue L → Bool
  | .anyType => true
  | _ => false

/-- The concrete `jl_is_type` kind check needed by
`src/builtins.c:2210-2224`. In particular TypeApp, TypeVar, and ordinary values
are not types; TypeVar is accepted by a separate source test. -/
-- Source: src/builtins.c:2210-2224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_tvar_t *jl_new_typevar(jl_sym_t *name, jl_value_t *lb, jl_value_t *ub)
-- {
--     if (lb != jl_bottom_type && !jl_is_type(lb) && !jl_is_typevar(lb))
--         jl_type_error_rt("TypeVar", "lower bound", (jl_value_t *)jl_type_type, lb);
--     if (ub != (jl_value_t *)jl_any_type && !jl_is_type(ub) && !jl_is_typevar(ub))
--         jl_type_error_rt("TypeVar", "upper bound", (jl_value_t *)jl_type_type, ub);
--     jl_task_t *ct = jl_current_task;
--     jl_tvar_t *tv = (jl_tvar_t *)jl_gc_alloc(ct->ptls, sizeof(jl_tvar_t), jl_tvar_type);
--     jl_set_typetagof(tv, jl_tvar_tag, 0);
--     tv->name = name;
--     tv->lb = lb;
--     tv->ub = ub;
--     return tv;
-- }
-- 
-- /Source
def typeVarIsType {L : Type} : TypeVarValue L → Bool
  | .bottom | .anyType | .typeValue _ => true
  | _ => false

/-- The concrete `jl_is_typevar` kind check needed by
`src/builtins.c:2210-2224`. It does not inspect the object's mutable bounds. -/
-- Source: src/builtins.c:2210-2224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_tvar_t *jl_new_typevar(jl_sym_t *name, jl_value_t *lb, jl_value_t *ub)
-- {
--     if (lb != jl_bottom_type && !jl_is_type(lb) && !jl_is_typevar(lb))
--         jl_type_error_rt("TypeVar", "lower bound", (jl_value_t *)jl_type_type, lb);
--     if (ub != (jl_value_t *)jl_any_type && !jl_is_type(ub) && !jl_is_typevar(ub))
--         jl_type_error_rt("TypeVar", "upper bound", (jl_value_t *)jl_type_type, ub);
--     jl_task_t *ct = jl_current_task;
--     jl_tvar_t *tv = (jl_tvar_t *)jl_gc_alloc(ct->ptls, sizeof(jl_tvar_t), jl_tvar_type);
--     jl_set_typetagof(tv, jl_tvar_tag, 0);
--     tv->name = name;
--     tv->lb = lb;
--     tv->ub = ub;
--     return tv;
-- }
-- 
-- /Source
def typeVarIsVariable {L : Type} : TypeVarValue L → Bool
  | .typevarRef _ => true
  | _ => false

/-- Concrete `_typevar` dependency: check lower and then upper bound, allocate
only after both checks succeed, and initialize every field. There is no subtype
or free-variable check. Julia source: `src/builtins.c:2210-2224`, retained in the
pinned source comments of `JuliaLean/src/jltypes_c.lean`; called by
`base/boot.jl:370-372`. The task/PTLS plumbing supplies allocation context only;
its allocation effect is represented by the fresh heap cell below. -/
-- Source: src/builtins.c:2210-2224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_tvar_t *jl_new_typevar(jl_sym_t *name, jl_value_t *lb, jl_value_t *ub)
-- {
--     if (lb != jl_bottom_type && !jl_is_type(lb) && !jl_is_typevar(lb))
--         jl_type_error_rt("TypeVar", "lower bound", (jl_value_t *)jl_type_type, lb);
--     if (ub != (jl_value_t *)jl_any_type && !jl_is_type(ub) && !jl_is_typevar(ub))
--         jl_type_error_rt("TypeVar", "upper bound", (jl_value_t *)jl_type_type, ub);
--     jl_task_t *ct = jl_current_task;
--     jl_tvar_t *tv = (jl_tvar_t *)jl_gc_alloc(ct->ptls, sizeof(jl_tvar_t), jl_tvar_type);
--     jl_set_typetagof(tv, jl_tvar_tag, 0);
--     tv->name = name;
--     tv->lb = lb;
--     tv->ub = ub;
--     return tv;
-- }
-- 
-- /Source
def newTypeVar {L : Type} (name : TypeVarName) (lb ub : TypeVarValue L) :
    TypeVarM L (TypeVarValue L) := do
  if !typeVarIsBottom lb && !typeVarIsType lb && !typeVarIsVariable lb then
    throw { exception := .typeError "TypeVar", context := "lower bound", expected := .type, got := lb }
  if !typeVarIsAny ub && !typeVarIsType ub && !typeVarIsVariable ub then
    throw { exception := .typeError "TypeVar", context := "upper bound", expected := .type, got := ub }
  let heap : TypeVarHeap L ← get
  let ref := heap.cells.length
  set ({ cells := heap.cells ++ [{ name := some name, lower := some lb, upper := some ub }] } : TypeVarHeap L)
  pure (.typevarRef ref)

/-- Concrete `n::Symbol` check at `base/boot.jl:370-372`. Its failure precedes
every bound validation and allocates no TypeVar cell. -/
-- Source: base/boot.jl:370-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- TypeVar(@nospecialize(n)) = _typevar(n::Symbol, Union{}, Any)
-- TypeVar(@nospecialize(n), @nospecialize(ub)) = _typevar(n::Symbol, Union{}, ub)
-- TypeVar(@nospecialize(n), @nospecialize(lb), @nospecialize(ub)) = _typevar(n::Symbol, lb, ub)
-- /Source
def typeVarAssertName {L : Type} (n : TypeVarValue L) : TypeVarM L TypeVarName :=
  match n with
  | .symbol name => pure name
  | _ => throw { exception := .typeError "typeassert", context := "", expected := .symbol, got := n }

/-- `TypeVar(n)` preserves the Symbol name and defaults to bottom/Any bounds.
Source reference: `base/boot.jl:370`. -/
-- Source: base/boot.jl:370-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- TypeVar(@nospecialize(n)) = _typevar(n::Symbol, Union{}, Any)
-- /Source
def typeVar1 {L : Type} (n : TypeVarValue L) : TypeVarM L (TypeVarValue L) := do
  newTypeVar (← typeVarAssertName n) .bottom .anyType

/-- `TypeVar(n, ub)` checks its name before the supplied bound and defaults its
lower bound to bottom. Julia source: `base/boot.jl:371`. -/
-- Source: base/boot.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- TypeVar(@nospecialize(n), @nospecialize(ub)) = _typevar(n::Symbol, Union{}, ub)
-- /Source
def typeVar2 {L : Type} (n ub : TypeVarValue L) : TypeVarM L (TypeVarValue L) := do
  newTypeVar (← typeVarAssertName n) .bottom ub

/-- `TypeVar(n, lb, ub)` checks its name first, then validates bounds in source
order and allocates fresh mutable identity. Julia source: `base/boot.jl:372`. -/
-- Source: base/boot.jl:372-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- TypeVar(@nospecialize(n), @nospecialize(lb), @nospecialize(ub)) = _typevar(n::Symbol, lb, ub)
-- /Source
def typeVar3 {L : Type} (n lb ub : TypeVarValue L) : TypeVarM L (TypeVarValue L) := do
  newTypeVar (← typeVarAssertName n) lb ub

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Generic-field constructors at `base/boot.jl:522,534-538`. The classification tags
below are a concrete, disjoint partition of their input domain, not a supplied
`isa` implementation. The AbstractString class includes every user subtype;
Symbol and GlobalRef are their full concrete classes. All other Julia values
belong to `other`. Payloads retain arbitrary objects and opaque identities.
The expected argument of TypeError is already Type by the source signature.

Only `convert(target, value)` and `Symbol(where)` remain open dispatch calls:
the source does not fix the types on which those calls dispatch. They are
parameterized with unrestricted effects, exceptions, and possible divergence.
No return-type or correctness law is imposed. A conversion may return a value
of the wrong class, whose raw-new check occurs only after every field expression
has finished. See `base/essentials.jl:1468-1488` for the pinned lowered-new pattern.

The encoding record supplies existing pure CoreOps representation functions and
one representation constant for Union{AbstractString,GlobalRef,Symbol}; the
latter is a type expression, not a named Core global. It is not a callback for
computing field metadata or deciding type membership. Error construction uses
an actual represented TypeError object, with the offending returned value.
-/

/-- Concrete type classes needed by the fields in `base/boot.jl:518-535`.
Each actual value has exactly one class. Custom AbstractString values are included. -/
inductive ConstructorClass where
  | symbol
  | abstractString
  | globalRef
  | other
  deriving DecidableEq, BEq, Repr

/-- A full Julia payload together with its fixed class in the disjoint partition
needed at `base/boot.jl:522,534-538`. Tags are representation information, not
assumptions on callback correctness. Callback results carry their actual class. -/
structure ClassifiedConstructorValue (L : Type) where
  kind : ConstructorClass
  value : JuliaLean.base.expr.Value L

/-- The three fixed target field types in `base/boot.jl:518-535`. -/
inductive ConstructorFieldTarget where
  | abstractString
  | symbol
  | context
  deriving DecidableEq, BEq, Repr

/-- Exact membership for the fixed field types in `base/boot.jl:518-535`.
The context field accepts AbstractString, GlobalRef, or Symbol. -/
-- Source: base/essentials.jl:1468-1488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             # Use an isa check to avoid depending on convert inlining.
--             # This matches the old convert-for-type-decl pattern:
--             #   isa(arg, fieldtype(self, i)) ? arg : convert(fieldtype(self, i), arg)
--             # The isa check is important because user code may define ambiguous
--             # convert methods (e.g. convert(::Any, v::T) = v) that prevent the
--             # optimizer from inlining convert(fieldtype(self, i), arg) when the
--             # field type is Any after specialization.
--             ft_expr = Expr(:call, GlobalRef(Core, :fieldtype), Core.Argument(1), i)
--             ft_ssa = Expr(:ssavalue, bidx)
--             cnvt_ssa = Expr(:ssavalue, bidx + 1)
--             isa_check = Expr(:call, GlobalRef(Core, :isa), Core.Argument(i + 1), ft_ssa)
--             convert_expr = Expr(:call, GlobalRef(Base, :convert), ft_ssa, Core.Argument(i + 1))
--             @inbounds body_args[bidx] = Expr(:(=), ft_ssa, ft_expr)
--             @inbounds body_args[bidx + 1] = Expr(:(=), cnvt_ssa, Expr(:if, isa_check,
--                                                Core.Argument(i + 1), convert_expr))
--             @inbounds new_args[i] = cnvt_ssa
--             bidx = bidx + 2
--         end
--         i = i + 1
--     end
--     body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
-- /Source
def constructorFieldAccepts : ConstructorFieldTarget → ConstructorClass → Bool
  | .abstractString, .abstractString => true
  | .symbol, .symbol => true
  | .context, .abstractString => true
  | .context, .globalRef => true
  | .context, .symbol => true
  | _, _ => false

/-- Pure value encodings for `base/boot.jl:522,534-538`. Only runtime.str,
runtime.core, and runtime.obj are used; no runtime operation is called.
contextType denotes the fixed Union{AbstractString,GlobalRef,Symbol} object. -/
structure GenericConstructorEncoding (W L : Type) where
  runtime : CoreOps W L
  contextType : JuliaLean.base.expr.Value L

/-- Open dispatch selected on source arguments of unspecified type in
`base/boot.jl:522,534-538`. `convert` receives the exact fixed target type and
unchanged argument; Symbol is the generic constructor call in the three-argument
TypeError method. Both may throw, mutate state, diverge, or return another class. -/
structure GenericConstructorDispatch (m : Type → Type) (L : Type) where
  convert : ConstructorFieldTarget → ClassifiedConstructorValue L →
    m (ClassifiedConstructorValue L)
  symbol : ClassifiedConstructorValue L → m (ClassifiedConstructorValue L)

/-- Encode one of the concrete field types at `base/boot.jl:518-535`.
This is a pure selection of fixed type objects, not open fieldtype behavior. -/
-- Source: base/boot.jl:524-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct TypeError <: Exception
--     # `func` is the name of the builtin function that encountered a type error,
--     # the name of the type that hit an error in its definition or application, or
--     # some other brief description of where the error happened.
--     # `context` optionally adds extra detail, e.g. the name of the type parameter
--     # that got a bad value.
--     func::Symbol
--     context::Union{AbstractString,GlobalRef,Symbol}
--     expected::Type
--     got
--     TypeError(func, context, @nospecialize(expected::Type), @nospecialize(got)) =
--         new(func, context, expected, got)
-- /Source
def constructorFieldType {W L : Type} (encoding : GenericConstructorEncoding W L) :
    ConstructorFieldTarget → JuliaLean.base.expr.Value L
  | .abstractString => coreV encoding.runtime "AbstractString"
  | .symbol => coreV encoding.runtime "Symbol"
  | .context => encoding.contextType

/-- Evaluate a lowered-new field expression: an already compatible value is
retained; only an incompatible source value invokes dispatched convert.
Source reference: `base/essentials.jl:1468-1488`, used by `base/boot.jl:522,535`. -/
-- Source: base/essentials.jl:1468-1488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             # Use an isa check to avoid depending on convert inlining.
--             # This matches the old convert-for-type-decl pattern:
--             #   isa(arg, fieldtype(self, i)) ? arg : convert(fieldtype(self, i), arg)
--             # The isa check is important because user code may define ambiguous
--             # convert methods (e.g. convert(::Any, v::T) = v) that prevent the
--             # optimizer from inlining convert(fieldtype(self, i), arg) when the
--             # field type is Any after specialization.
--             ft_expr = Expr(:call, GlobalRef(Core, :fieldtype), Core.Argument(1), i)
--             ft_ssa = Expr(:ssavalue, bidx)
--             cnvt_ssa = Expr(:ssavalue, bidx + 1)
--             isa_check = Expr(:call, GlobalRef(Core, :isa), Core.Argument(i + 1), ft_ssa)
--             convert_expr = Expr(:call, GlobalRef(Base, :convert), ft_ssa, Core.Argument(i + 1))
--             @inbounds body_args[bidx] = Expr(:(=), ft_ssa, ft_expr)
--             @inbounds body_args[bidx + 1] = Expr(:(=), cnvt_ssa, Expr(:if, isa_check,
--                                                Core.Argument(i + 1), convert_expr))
--             @inbounds new_args[i] = cnvt_ssa
--             bidx = bidx + 2
--         end
--         i = i + 1
--     end
--     body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
-- /Source
def prepareConstructorField {m : Type → Type} [Monad m] {L : Type}
    (dispatch : GenericConstructorDispatch m L) (target : ConstructorFieldTarget)
    (input : ClassifiedConstructorValue L) : m (ClassifiedConstructorValue L) :=
  if constructorFieldAccepts target input.kind then pure input
  else dispatch.convert target input

/-- Perform the raw-new field check, after all field expressions have evaluated.
A failed check throws TypeError(:new, "", fieldtype, returnedValue), rather than
reconverting the value or discarding a custom conversion's effects.
Source reference: `base/boot.jl:522,535`; lowered raw-new is emitted at
`base/essentials.jl:1488`. -/
-- Source: base/essentials.jl:1488-1488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
-- /Source
def finishConstructorField {m : Type → Type} [Monad m] {W L : Type}
    [MonadExceptOf (JuliaLean.base.expr.Value L) m]
    (encoding : GenericConstructorEncoding W L) (target : ConstructorFieldTarget)
    (prepared : ClassifiedConstructorValue L) : m (JuliaLean.base.expr.Value L) :=
  if constructorFieldAccepts target prepared.kind then pure prepared.value
  else
    throw (objV encoding.runtime
      (.typeError (.symbol "new") (strV encoding.runtime "")
        (constructorFieldType encoding target) prepared.value))

/-- Full-domain two-argument DomainError. The value field is Any; the message
field is conditionally converted and then checked by raw new.
Source reference: `base/boot.jl:522`. -/
-- Source: base/boot.jl:522-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     DomainError(@nospecialize(val), @nospecialize(msg)) = (@noinline; new(val, msg))
-- /Source
def domainErrorCtor {m : Type → Type} [Monad m] {W L : Type}
    [MonadExceptOf (JuliaLean.base.expr.Value L) m]
    (encoding : GenericConstructorEncoding W L)
    (dispatch : GenericConstructorDispatch m L) (val : JuliaLean.base.expr.Value L)
    (msg : ClassifiedConstructorValue L) : m (Obj L) := do
  let prepared ← prepareConstructorField dispatch .abstractString msg
  let stored ← finishConstructorField encoding .abstractString prepared
  pure (.domainError val stored)

/-- Full-domain four-argument TypeError. Both potentially converting expressions
are evaluated left-to-right before either raw-new check. The source-typed expected
field and Any got field are stored directly.
Source reference: `base/boot.jl:534-535`. -/
-- Source: base/boot.jl:534-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     TypeError(func, context, @nospecialize(expected::Type), @nospecialize(got)) =
--         new(func, context, expected, got)
-- /Source
def typeErrorCtor {m : Type → Type} [Monad m] {W L : Type}
    [MonadExceptOf (JuliaLean.base.expr.Value L) m]
    (encoding : GenericConstructorEncoding W L)
    (dispatch : GenericConstructorDispatch m L)
    (func context : ClassifiedConstructorValue L)
    (expected got : JuliaLean.base.expr.Value L) : m (Obj L) := do
  let preparedFunc ← prepareConstructorField dispatch .symbol func
  let preparedContext ← prepareConstructorField dispatch .context context
  let storedFunc ← finishConstructorField encoding .symbol preparedFunc
  let storedContext ← finishConstructorField encoding .context preparedContext
  pure (.typeError storedFunc storedContext expected got)

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Complete two-argument LineNumberNode at `base/boot.jl:711-714`. The file's
runtime class is represented by disjoint tags: concrete String, Symbol,
Nothing, or any other Julia value. Only concrete Strings are converted. Their
native-sized bytes include embedded NUL and invalid UTF-8; no Lean String
conversion loses those cases. Symbol construction calls the installed concrete
`BootCov.Arrays.symbolOfString`, including its NUL rejection.

The Symbol byte encoding and fixed Union{Symbol,Nothing} value below are pure
representations, not supplied implementations of Symbol, isa, or fieldtype.
Opaque payloads retain every uninspected Julia value and mutable identity.
LineNumberNode is immutable, Symbols are interned by their bytes, and nothing
is a singleton. Consequently construction has no mutable object identity to
allocate in this model. GC, intern-table storage and allocation exhaustion are
abstracted; all source-visible validation failures are retained.
-/

/-- The native-sized raw bytes of a concrete String, read by
`Symbol(s::String)` at `base/boot.jl:864-868`. Non-UTF-8 and NUL are permitted. -/
structure LineNumberString where
  bytes : List UInt8
  nativeSize : bytes.length ≤ IntTy.i64.max.toNat

/-- The complete file argument domain at `base/boot.jl:711`. Symbol payloads
are already dispatch-refined symbols and are stored unchanged. `other` includes
all remaining values, including arbitrary custom AbstractString subtypes. -/
inductive LineNumberFile (L : Type) where
  | string (value : LineNumberString)
  | symbol (value : JuliaLean.base.expr.Value L)
  | nothing
  | other (value : JuliaLean.base.expr.Value L)

/-- Pure encodings used by `base/boot.jl:711-714`: raw interned Symbol names,
the actual Union{Symbol,Nothing} field type, and existing constant encodings.
No runtime behavior in CoreOps is invoked. `symbolBytes` is only applied to
native-sized lists of byte values produced by the installed Symbol model. -/
structure LineNumberEncoding (W L : Type) where
  runtime : CoreOps W L
  symbolBytes : List Nat → JuliaLean.base.expr.Value L
  fileType : JuliaLean.base.expr.Value L

/-- Refined payload of the existing Julia exception classes. Symbol errors
retain the installed `BootCov.Exc` unchanged; a raw-new TypeError additionally
retains its existing transparent Obj payload, including the offending value.
This introduces no new Julia exception class. Source: `base/boot.jl:711-714`. -/
structure LineNumberError (L : Type) where
  exception : JuliaLean.BootCov.Exc
  typeErrorPayload : Option (Obj L)

/-- The concrete String-to-Symbol dependency at `base/boot.jl:864-868`.
The installed model reads every source byte and rejects NUL before returning
the interned byte name. Raw bytes are converted losslessly to its Nat encoding;
no arbitrary Symbol callback or Unicode normalization is introduced. -/
-- Source: base/boot.jl:864-868 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Symbol(s::String)
--     @_foldable_meta
--     @noinline
--     return _Symbol(ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s), sizeof(s), s)
-- end
-- /Source
def lineNumberSymbol {W L : Type} (encoding : LineNumberEncoding W L)
    (s : LineNumberString) : Except (LineNumberError L) (JuliaLean.base.expr.Value L) :=
  match JuliaLean.BootCov.Arrays.symbolOfString (s.bytes.map UInt8.toNat) with
  | .ok bytes => .ok (encoding.symbolBytes bytes)
  | .error exception => .error { exception, typeErrorPayload := none }

/-- `LineNumberNode(l, f)` retains its native Int line, converts precisely the
concrete String case to Symbol, and otherwise checks the raw-new file field.
Symbol and nothing are accepted unchanged; every other Julia value, including
custom AbstractString objects, receives TypeError(:new, "", Union{Symbol,Nothing}, f).
Source: `base/boot.jl:711-714`, generated in the complete context below.
Field layout: `base/boot.jl:133-136`. -/
-- Source: base/boot.jl:699-726 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, quote
--     GotoNode(label::Int) = $(Expr(:new, :GotoNode, :label))
--     NewvarNode(slot::SlotNumber) = $(Expr(:new, :NewvarNode, :slot))
--     QuoteNode(@nospecialize value) = $(Expr(:new, :QuoteNode, :value))
--     SSAValue(id::Int) = $(Expr(:new, :SSAValue, :id))
--     Argument(n::Int) = $(Expr(:new, :Argument, :n))
--     ReturnNode(@nospecialize val) = $(Expr(:new, :ReturnNode, :val))
--     ReturnNode() = $(Expr(:new, :ReturnNode)) # unassigned val indicates unreachable
--     GotoIfNot(@nospecialize(cond), dest::Int) = $(Expr(:new, :GotoIfNot, :cond, :dest))
--     EnterNode(dest::Int) = $(Expr(:new, :EnterNode, :dest))
--     EnterNode(dest::Int, @nospecialize(scope)) = $(Expr(:new, :EnterNode, :dest, :scope))
--     LineNumberNode(l::Int) = $(Expr(:new, :LineNumberNode, :l, nothing))
--     function LineNumberNode(l::Int, @nospecialize(f))
--         isa(f, String) && (f = Symbol(f))
--         return $(Expr(:new, :LineNumberNode, :l, :f))
--     end
--     DebugInfo(def::Union{Method,MethodInstance,Symbol}, linetable::Union{Nothing,DebugInfo,String}, edges::SimpleVector, codelocs::String) =
--         $(Expr(:new, :DebugInfo, :def, :linetable, :edges, :codelocs))
--     DebugInfo(def::Union{Method,MethodInstance,Symbol}) =
--         $(Expr(:new, :DebugInfo, :def, nothing, Core.svec(), ""))
--     SlotNumber(n::Int) = $(Expr(:new, :SlotNumber, :n))
--     PhiNode(edges::Array{Int32, 1}, values::Array{Any, 1}) = $(Expr(:new, :PhiNode, :edges, :values))
--     PiNode(@nospecialize(val), @nospecialize(typ)) = $(Expr(:new, :PiNode, :val, :typ))
--     PhiCNode(values::Array{Any, 1}) = $(Expr(:new, :PhiCNode, :values))
--     UpsilonNode(@nospecialize(val)) = $(Expr(:new, :UpsilonNode, :val))
--     UpsilonNode() = $(Expr(:new, :UpsilonNode))
--     MethodMatch(@nospecialize(spec_types), sparams::SimpleVector, method::Method, fully_covers::Bool) = $(Expr(:new, :MethodMatch, :spec_types, :sparams, :method, :fully_covers))
-- end)
-- /Source
def lineNumberNode2Ctor {W L : Type} (encoding : LineNumberEncoding W L)
    (line : JInt .i64) (file : LineNumberFile L) :
    Except (LineNumberError L) (JuliaLean.base.expr.Value L) := do
  let prepared : Sum (JuliaLean.base.expr.Value L) (JuliaLean.base.expr.Value L) ←
    match file with
    | .string s => pure (.inl (← lineNumberSymbol encoding s))
    | .symbol value => pure (.inl value)
    | .nothing => pure (.inl (nothingV encoding.runtime))
    | .other value => pure (.inr value)
  match prepared with
  | .inl accepted => pure (.lineNumberNode line accepted)
  | .inr got =>
    throw {
      exception := .typeError "new"
      typeErrorPayload := some (.typeError (.symbol "new") (strV encoding.runtime "")
        encoding.fileType got) }

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-- Calls whose target depends on the unspecified concrete subtype of IO.
Both fields are genuine Julia generic dispatch, not replacements for a fixed
primitive implementation. The source does not fix IO to CoreSTDOUT/CoreSTDERR.
Arbitrary state, errors and divergence can be retained by m.
Source reference: base/boot.jl:998-1001. -/
structure PrintingDispatch (m : Type → Type) (L : Type) where
  write : JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L →
    m (JuliaLean.base.expr.Value L)
  showValue : JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L →
    m (JuliaLean.base.expr.Value L)

/-- Call dispatched write on the actual IO and source-typed String, discard
only a successful return value, then return nothing. Errors, divergence and
effects of custom IO methods are retained. Julia source: base/boot.jl:998. -/
-- Source: base/boot.jl:998-998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- print(io::IO, x::String) = (write(io, x); nothing)
-- /Source
def printString {m : Type → Type} [Monad m] {W L : Type}
    (encoding : CoreOps W L) (dispatch : PrintingDispatch m L)
    (io x : JuliaLean.base.expr.Value L) : m (JuliaLean.base.expr.Value L) := do
  let _ ← dispatch.write io x
  pure (nothingV encoding)

/-- The generic print fallback forwards to show selected on the actual IO and
value types, with no restrictions on its outcome. Julia source: base/boot.jl:999. -/
-- Source: base/boot.jl:999-999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- print(io::IO, @nospecialize x) = show(io, x)
-- /Source
def printAny {m : Type → Type} {L : Type}
    (dispatch : PrintingDispatch m L) (io x : JuliaLean.base.expr.Value L) :
    m (JuliaLean.base.expr.Value L) := dispatch.showValue io x

/-- The no-value println method writes exactly the source UInt8 newline
through open IO dispatch and returns nothing only if that call returns.
The native byte uses JInt UInt8, not a mathematical unbounded integer.
Source reference: base/boot.jl:1001. -/
-- Source: base/boot.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- println(io::IO) = (write(io, 0x0a); nothing) # 0x0a = '\n'
-- /Source
def printlnIO {m : Type → Type} [Monad m] {W L : Type}
    (encoding : CoreOps W L) (dispatch : PrintingDispatch m L)
    (io : JuliaLean.base.expr.Value L) : m (JuliaLean.base.expr.Value L) := do
  let _ ← dispatch.write io (intV encoding (JInt.lit .u8 10))
  pure (nothingV encoding)

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Closed raw-vararg `checked_dims` body, reusing the installed source-mirrored
native arithmetic at `base/boot.jl:782-809`. The zero- and one-argument
`checked_dims` methods are already complete and remain unchanged.

The list below represents an actual tuple of Int64 values. Its arity bound is
the UInt32 `DataTypeLayout.nfields` bound from
`base/runtime_internals.jl:624-630,716-723`, not an assumed array-size bound.
In particular the installed structural translation of the dimension loop
cannot hide signed-Int loop-counter overflow on any represented tuple: its
last increment is at most 2^32, well below typemax(Int64).

All native arithmetic remains in the installed JInt/C intrinsic definitions.
No mathematical Int/Nat arithmetic substitutes for a Julia multiplication.
Only the fixed literal's String representation and immutable exception
embedding use CoreOps. They are data embeddings; no dispatch, reflection,
conversion, exception-construction or runtime-behavior callback is called.
The actual ArgumentError constructor is the installed concrete group model.
As elsewhere in these immutable-constructor models, GC, physical allocation
and resource exhaustion are abstracted.
-/

/-- An actual Julia tuple of Int dimensions, including every native Int value
and every representable arity. The bound is representation metadata, not an
extra runtime check in `base/boot.jl:814-818`.
-/
structure DimensionTuple where
  values : List I64
  arityBound : values.length ≤ (IntTy.max .u32).toNat

/-- Complete body of the raw vararg method `base/boot.jl:814-818`, including
explicit invocation with zero or one argument. The scalar method at line813
deliberately skips validation, but this body always calls `_checked_mul_dims`.
The already installed closed helper dispatcher selects the actual zero,
one, two, or variadic multiplication method. On rejection the concrete
ArgumentError constructor is invoked and that object is thrown.
-/
-- Source: base/boot.jl:814-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checked_dims(d::Int...)
--     b = _checked_mul_dims(d...)
--     getfield(b, 2) && throw(ArgumentError("invalid Array dimensions"))
--     return getfield(b, 1)
-- end
-- /Source
def checkedDimsVarargs {W L : Type} (ops : CoreOps W L) (d : DimensionTuple) :
    CoreM W L I64 := do
  let b := checkedMulDims d.values
  if b.2 then
    throw (objV ops (argumentErrorCtor (strV ops "invalid Array dimensions")))
  pure b.1

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-- The local bootstrap failure at `base/boot.jl:878`: construct its concrete
ArgumentError from the fixed String message and throw it. The typed constructor
is the group's complete concrete argumentErrorCtor, so no convert/fieldtype
callback is introduced for this already compatible String argument. The
surrounding local-definition context is retained below. -/
-- Source: base/boot.jl:877-886 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- let
--     fail() = throw(ArgumentError("unsupported import/using while bootstrapping"))
--     length(a::Array{T, 1}) where {T} = getfield(getfield(a, :size), 1)
--     function getindex(A::Array, i::Int)
--         Intrinsics.ult_int(Intrinsics.bitcast(UInt, Intrinsics.sub_int(i, 1)), Intrinsics.bitcast(UInt, length(A))) || fail()
--         memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
--     end
--     x == y = Intrinsics.eq_int(x, y)
--     x + y = Intrinsics.add_int(x, y)
--     x <= y = Intrinsics.sle_int(x, y)
-- /Source
def bootstrapFail {W L A : Type} (ops : CoreOps W L) : CoreM W L A :=
  throwObj ops (argumentErrorCtor (strV ops "unsupported import/using while bootstrapping"))

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
The generated typed NamedTuple constructor at `base/boot.jl:1029-1030`
uses raw splatnew. Its existing NT target is not assumed allocatable: the
stored DataType/concreteness/layout flags are checked first, as in the pinned
`src/datatype.c:1744-1791`. Nonconcrete or incomplete targets produce the
original TypeError(:new, DataType, NT), before field count or field reads.

For an allocatable valid NamedTuple{names,T}, its fields are exactly the finite
parameters of T: pinned `src/jltypes.c:2726-2773` validates this during type
formation. The source args::T signature therefore supplies compatible field
values, including values with types more specific than abstract declared field
types. The raw count check remains explicit; per-field isa tests cannot fail
on this dispatch domain. No convert, type application, arbitrary isa callback,
or additional success precondition is introduced.

An NT with free parameters has isconcretetype=false by
`src/jltypes.c:2090-2104` and is handled by the target guard. Symbol names and
full declared field types remain represented in the unchanged runtime NT token.
Immutable named-tuple value identity is determined by this type and its stored
fields, including any shared mutable payload references. Physical allocation,
GC and exhaustion are abstracted as for the other immutable constructors.
-/

/-- Actual stored target metadata read by raw splatnew. These flags represent
runtime fields, not supplied validation behavior. Source: `base/boot.jl:1029-1030`;
`src/datatype.c:1744-1754`. The count comes from UInt32 DataTypeLayout.nfields. -/
structure TypedNamedTupleTarget (L : Type) where
  value : JuliaLean.base.expr.Value L
  isDataType : Bool
  isConcrete : Bool
  hasLayout : Bool
  layoutOpaque : Bool
  fieldCount : JInt .u32

/-- A constructible Julia tuple passed as args::T. Its DataType layout stores
arity as UInt32; mathematical List indexes do not replace source arithmetic.
Source: `base/boot.jl:1029-1030`; `base/runtime_internals.jl:626,716-723`. -/
structure TypedNamedTupleArguments (L : Type) where
  values : List (JuliaLean.base.expr.Value L)
  arity : values.length ≤ (2^32 - 1 : Nat)

/-- Immutable result retaining the exact declared type and every input field.
Source: `base/boot.jl:1029-1030`. -/
structure TypedNamedTupleValue (L : Type) where
  runtimeType : JuliaLean.base.expr.Value L
  fields : TypedNamedTupleArguments L

/-- Refined existing TypeError/ArgumentError payload from jl_new_structt. No
new Julia exception class is introduced. Source: `src/datatype.c:1744-1754`. -/
structure TypedNamedTupleError (L : Type) where
  exception : JuliaLean.BootCov.Exc
  expected : Option String := none
  got : Option (JuliaLean.base.expr.Value L) := none

/-! Necessary concrete splatnew target/count validation from the pinned source. -/
-- Source: src/datatype.c:1744-1754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_value_t *jl_new_structt(jl_datatype_t *type, jl_value_t *tup)
-- {
--     jl_task_t *ct = jl_current_task;
--     if (!jl_is_tuple(tup))
--         jl_type_error("new", (jl_value_t*)jl_tuple_type, tup);
--     if (!jl_is_datatype(type) || !type->isconcretetype || type->layout == NULL || jl_is_layout_opaque(type->layout))
--         jl_type_error("new", (jl_value_t *)jl_datatype_type, (jl_value_t *)type);
--     size_t nargs = jl_nfields(tup);
--     size_t nf = jl_datatype_nfields(type);
--     JL_NARGS(new, nf, nf);
--     if (type->instance != NULL) {
-- /Source

/-- Complete typed NamedTuple body: check actual target allocatability, then
exact count, then store the source-compatible tuple fields under the original
NT type. JL_NARGS errors use the C int conversion of nfields explicitly via
i32 wrapping, rather than silently replacing native arithmetic with Nat.
Source reference: `base/boot.jl:1029-1030`; runtime closure above and
`src/julia.h:2426-2428`, `src/rtutils.c:102-110`. -/
-- Source: base/boot.jl:1029-1030 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :((NT::Type{NamedTuple{names,T}})(args::T) where {names, T <: Tuple} =
--              $(Expr(:splatnew, :NT, :args))))
-- /Source
def typedNamedTupleCtor {L : Type} (NT : TypedNamedTupleTarget L)
    (args : TypedNamedTupleArguments L) : Except (TypedNamedTupleError L) (TypedNamedTupleValue L) := do
  if !NT.isDataType || !NT.isConcrete || !NT.hasLayout || NT.layoutOpaque then
    throw { exception := .typeError "new", expected := some "DataType", got := some NT.value }
  if args.values.length < NT.fieldCount.val.toNat then
    throw { exception := .argument s!"new: too few arguments (expected {(JInt.wrap .i32 NT.fieldCount.val).val})" }
  if args.values.length > NT.fieldCount.val.toNat then
    throw { exception := .argument s!"new: too many arguments (expected {(JInt.wrap .i32 NT.fieldCount.val).val})" }
  pure { runtimeType := NT.value, fields := args }

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Complete native integer conversions for `base/boot.jl:1071-1215`. The installed
`BootCov.IntConv` tables already mirror every concrete source branch, in order,
using native JInt bit patterns. Their only information loss is the original
argument of an InexactError. The additive result refinement below retains the
existing exception and attaches the actual target and complete typed input.
Thus it preserves sign-check versus truncation order and the source's error
function Symbol, including `:trunc` for negative narrower signed inputs to a
wider unsigned target. It does not replace these branches with a range test.

The target IntTy denotes its unique concrete Core integer DataType. BuiltinInt
records every native integer type/value and both Bool values, so the error's
`args` tuple `(target, original_input)` is recoverable without any value loss.
All data are immutable. GC, physical allocation, and resource exhaustion are
abstracted as for the installed pure native models. No open runtime operation
or assumed callee-correctness law is introduced. The generic source helpers
1037/1047/1055/1063 remain unclaimed: custom primitive types and invalid intrinsic
arguments need a larger runtime model. Here their installed native branches
are used only on the exact concrete, valid-width source calls.
-/

/-- A refinement of the installed exception carrier for the concrete native
conversions at `base/boot.jl:1045,1071-1215`. It retains the exception class and
function name plus both actual InexactError argument values. -/
structure NativeConversionError where
  exception : JuliaLean.BootCov.Exc
  target : IntTy
  input : JuliaLean.BootCov.IntConv.BuiltinInt

/-- Retain the complete payload of `InexactError(func, to, val)` at
`base/boot.jl:1045` when reusing an installed concrete native table. This is a
representation refinement, not another dispatch or a new arithmetic check.
Every old error is preserved; no unexpected case is replaced by a default. -/
-- Source: base/boot.jl:1045-1045 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- throw_inexacterror(func::Symbol, to, val) = throw(InexactError(func, to, val))
-- /Source
def refineNativeResult (target : IntTy) (input : JuliaLean.BootCov.IntConv.BuiltinInt)
    (result : JuliaLean.BootCov.R (JInt target)) :
    Except NativeConversionError (JInt target) :=
  match result with
  | .ok value => .ok value
  | .error exception => .error { exception, target, input }

/-- Full concrete `toInt8(x::Int16)` at `base/boot.jl:1072`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int16 bit pattern is included. -/
-- Source: base/boot.jl:1072-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::Int16)      = checked_trunc_sint(Int8, x)
-- /Source
def nativeToInt8FromInt16 (x : JInt .i16) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .i16 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .i16 x))

/-- Full concrete `toInt8(x::Int32)` at `base/boot.jl:1073`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int32 bit pattern is included. -/
-- Source: base/boot.jl:1073-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::Int32)      = checked_trunc_sint(Int8, x)
-- /Source
def nativeToInt8FromInt32 (x : JInt .i32) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .i32 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .i32 x))

/-- Full concrete `toInt8(x::Int64)` at `base/boot.jl:1074`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int64 bit pattern is included. -/
-- Source: base/boot.jl:1074-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::Int64)      = checked_trunc_sint(Int8, x)
-- /Source
def nativeToInt8FromInt64 (x : JInt .i64) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .i64 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .i64 x))

/-- Full concrete `toInt8(x::Int128)` at `base/boot.jl:1075`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1075-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::Int128)     = checked_trunc_sint(Int8, x)
-- /Source
def nativeToInt8FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .i128 x))

/-- Full concrete `toInt8(x::UInt8)` at `base/boot.jl:1076`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt8 bit pattern is included. -/
-- Source: base/boot.jl:1076-1076 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::UInt8)      = bitcast(Int8, check_sign_bit(Int8, x))
-- /Source
def nativeToInt8FromUInt8 (x : JInt .u8) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .u8 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .u8 x))

/-- Full concrete `toInt8(x::UInt16)` at `base/boot.jl:1077`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt16 bit pattern is included. -/
-- Source: base/boot.jl:1077-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::UInt16)     = checked_trunc_sint(Int8, check_sign_bit(Int8, x))
-- /Source
def nativeToInt8FromUInt16 (x : JInt .u16) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .u16 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .u16 x))

/-- Full concrete `toInt8(x::UInt32)` at `base/boot.jl:1078`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt32 bit pattern is included. -/
-- Source: base/boot.jl:1078-1078 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::UInt32)     = checked_trunc_sint(Int8, check_sign_bit(Int8, x))
-- /Source
def nativeToInt8FromUInt32 (x : JInt .u32) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .u32 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .u32 x))

/-- Full concrete `toInt8(x::UInt64)` at `base/boot.jl:1079`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt64 bit pattern is included. -/
-- Source: base/boot.jl:1079-1079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::UInt64)     = checked_trunc_sint(Int8, check_sign_bit(Int8, x))
-- /Source
def nativeToInt8FromUInt64 (x : JInt .u64) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .u64 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .u64 x))

/-- Full concrete `toInt8(x::UInt128)` at `base/boot.jl:1080`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1080-1080 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt8(x::UInt128)    = checked_trunc_sint(Int8, check_sign_bit(Int8, x))
-- /Source
def nativeToInt8FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toInt8 (.int .u128 x))

/-- Full concrete `toInt16(x::Int32)` at `base/boot.jl:1084`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int32 bit pattern is included. -/
-- Source: base/boot.jl:1084-1084 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt16(x::Int32)     = checked_trunc_sint(Int16, x)
-- /Source
def nativeToInt16FromInt32 (x : JInt .i32) : Except NativeConversionError (JInt .i16) :=
  refineNativeResult .i16 (.int .i32 x)
    (JuliaLean.BootCov.IntConv.toInt16 (.int .i32 x))

/-- Full concrete `toInt16(x::Int64)` at `base/boot.jl:1085`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int64 bit pattern is included. -/
-- Source: base/boot.jl:1085-1085 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt16(x::Int64)     = checked_trunc_sint(Int16, x)
-- /Source
def nativeToInt16FromInt64 (x : JInt .i64) : Except NativeConversionError (JInt .i16) :=
  refineNativeResult .i16 (.int .i64 x)
    (JuliaLean.BootCov.IntConv.toInt16 (.int .i64 x))

/-- Full concrete `toInt16(x::Int128)` at `base/boot.jl:1086`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1086-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt16(x::Int128)    = checked_trunc_sint(Int16, x)
-- /Source
def nativeToInt16FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .i16) :=
  refineNativeResult .i16 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toInt16 (.int .i128 x))

/-- Full concrete `toInt16(x::UInt16)` at `base/boot.jl:1088`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt16 bit pattern is included. -/
-- Source: base/boot.jl:1088-1088 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt16(x::UInt16)    = bitcast(Int16, check_sign_bit(Int16, x))
-- /Source
def nativeToInt16FromUInt16 (x : JInt .u16) : Except NativeConversionError (JInt .i16) :=
  refineNativeResult .i16 (.int .u16 x)
    (JuliaLean.BootCov.IntConv.toInt16 (.int .u16 x))

/-- Full concrete `toInt16(x::UInt32)` at `base/boot.jl:1089`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt32 bit pattern is included. -/
-- Source: base/boot.jl:1089-1089 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt16(x::UInt32)    = checked_trunc_sint(Int16, check_sign_bit(Int16, x))
-- /Source
def nativeToInt16FromUInt32 (x : JInt .u32) : Except NativeConversionError (JInt .i16) :=
  refineNativeResult .i16 (.int .u32 x)
    (JuliaLean.BootCov.IntConv.toInt16 (.int .u32 x))

/-- Full concrete `toInt16(x::UInt64)` at `base/boot.jl:1090`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt64 bit pattern is included. -/
-- Source: base/boot.jl:1090-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt16(x::UInt64)    = checked_trunc_sint(Int16, check_sign_bit(Int16, x))
-- /Source
def nativeToInt16FromUInt64 (x : JInt .u64) : Except NativeConversionError (JInt .i16) :=
  refineNativeResult .i16 (.int .u64 x)
    (JuliaLean.BootCov.IntConv.toInt16 (.int .u64 x))

/-- Full concrete `toInt16(x::UInt128)` at `base/boot.jl:1091`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1091-1091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt16(x::UInt128)   = checked_trunc_sint(Int16, check_sign_bit(Int16, x))
-- /Source
def nativeToInt16FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .i16) :=
  refineNativeResult .i16 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toInt16 (.int .u128 x))

/-- Full concrete `toInt32(x::Int64)` at `base/boot.jl:1096`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int64 bit pattern is included. -/
-- Source: base/boot.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt32(x::Int64)     = checked_trunc_sint(Int32, x)
-- /Source
def nativeToInt32FromInt64 (x : JInt .i64) : Except NativeConversionError (JInt .i32) :=
  refineNativeResult .i32 (.int .i64 x)
    (JuliaLean.BootCov.IntConv.toInt32 (.int .i64 x))

/-- Full concrete `toInt32(x::Int128)` at `base/boot.jl:1097`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1097-1097 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt32(x::Int128)    = checked_trunc_sint(Int32, x)
-- /Source
def nativeToInt32FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .i32) :=
  refineNativeResult .i32 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toInt32 (.int .i128 x))

/-- Full concrete `toInt32(x::UInt32)` at `base/boot.jl:1100`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt32 bit pattern is included. -/
-- Source: base/boot.jl:1100-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt32(x::UInt32)    = bitcast(Int32, check_sign_bit(Int32, x))
-- /Source
def nativeToInt32FromUInt32 (x : JInt .u32) : Except NativeConversionError (JInt .i32) :=
  refineNativeResult .i32 (.int .u32 x)
    (JuliaLean.BootCov.IntConv.toInt32 (.int .u32 x))

/-- Full concrete `toInt32(x::UInt64)` at `base/boot.jl:1101`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt64 bit pattern is included. -/
-- Source: base/boot.jl:1101-1101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt32(x::UInt64)    = checked_trunc_sint(Int32, check_sign_bit(Int32, x))
-- /Source
def nativeToInt32FromUInt64 (x : JInt .u64) : Except NativeConversionError (JInt .i32) :=
  refineNativeResult .i32 (.int .u64 x)
    (JuliaLean.BootCov.IntConv.toInt32 (.int .u64 x))

/-- Full concrete `toInt32(x::UInt128)` at `base/boot.jl:1102`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt32(x::UInt128)   = checked_trunc_sint(Int32, check_sign_bit(Int32, x))
-- /Source
def nativeToInt32FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .i32) :=
  refineNativeResult .i32 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toInt32 (.int .u128 x))

/-- Full concrete `toInt64(x::Int128)` at `base/boot.jl:1108`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1108-1108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt64(x::Int128)    = checked_trunc_sint(Int64, x)
-- /Source
def nativeToInt64FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .i64) :=
  refineNativeResult .i64 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toInt64 (.int .i128 x))

/-- Full concrete `toInt64(x::UInt64)` at `base/boot.jl:1112`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt64 bit pattern is included. -/
-- Source: base/boot.jl:1112-1112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt64(x::UInt64)    = bitcast(Int64, check_sign_bit(Int64, x))
-- /Source
def nativeToInt64FromUInt64 (x : JInt .u64) : Except NativeConversionError (JInt .i64) :=
  refineNativeResult .i64 (.int .u64 x)
    (JuliaLean.BootCov.IntConv.toInt64 (.int .u64 x))

/-- Full concrete `toInt64(x::UInt128)` at `base/boot.jl:1113`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1113-1113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt64(x::UInt128)   = checked_trunc_sint(Int64, check_sign_bit(Int64, x))
-- /Source
def nativeToInt64FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .i64) :=
  refineNativeResult .i64 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toInt64 (.int .u128 x))

/-- Full concrete `toInt128(x::UInt128)` at `base/boot.jl:1124`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1124-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt128(x::UInt128)  = bitcast(Int128, check_sign_bit(Int128, x))
-- /Source
def nativeToInt128FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .i128) :=
  refineNativeResult .i128 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toInt128 (.int .u128 x))

/-- Full concrete `toUInt8(x::Int8)` at `base/boot.jl:1126`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int8 bit pattern is included. -/
-- Source: base/boot.jl:1126-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::Int8)      = bitcast(UInt8, check_sign_bit(UInt8, x))
-- /Source
def nativeToUInt8FromInt8 (x : JInt .i8) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .i8 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .i8 x))

/-- Full concrete `toUInt8(x::Int16)` at `base/boot.jl:1127`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int16 bit pattern is included. -/
-- Source: base/boot.jl:1127-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::Int16)     = checked_trunc_uint(UInt8, x)
-- /Source
def nativeToUInt8FromInt16 (x : JInt .i16) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .i16 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .i16 x))

/-- Full concrete `toUInt8(x::Int32)` at `base/boot.jl:1128`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int32 bit pattern is included. -/
-- Source: base/boot.jl:1128-1128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::Int32)     = checked_trunc_uint(UInt8, x)
-- /Source
def nativeToUInt8FromInt32 (x : JInt .i32) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .i32 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .i32 x))

/-- Full concrete `toUInt8(x::Int64)` at `base/boot.jl:1129`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int64 bit pattern is included. -/
-- Source: base/boot.jl:1129-1129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::Int64)     = checked_trunc_uint(UInt8, x)
-- /Source
def nativeToUInt8FromInt64 (x : JInt .i64) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .i64 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .i64 x))

/-- Full concrete `toUInt8(x::Int128)` at `base/boot.jl:1130`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1130-1130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::Int128)    = checked_trunc_uint(UInt8, x)
-- /Source
def nativeToUInt8FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .i128 x))

/-- Full concrete `toUInt8(x::UInt16)` at `base/boot.jl:1132`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt16 bit pattern is included. -/
-- Source: base/boot.jl:1132-1132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::UInt16)    = checked_trunc_uint(UInt8, x)
-- /Source
def nativeToUInt8FromUInt16 (x : JInt .u16) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .u16 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .u16 x))

/-- Full concrete `toUInt8(x::UInt32)` at `base/boot.jl:1133`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt32 bit pattern is included. -/
-- Source: base/boot.jl:1133-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::UInt32)    = checked_trunc_uint(UInt8, x)
-- /Source
def nativeToUInt8FromUInt32 (x : JInt .u32) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .u32 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .u32 x))

/-- Full concrete `toUInt8(x::UInt64)` at `base/boot.jl:1134`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt64 bit pattern is included. -/
-- Source: base/boot.jl:1134-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::UInt64)    = checked_trunc_uint(UInt8, x)
-- /Source
def nativeToUInt8FromUInt64 (x : JInt .u64) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .u64 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .u64 x))

/-- Full concrete `toUInt8(x::UInt128)` at `base/boot.jl:1135`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1135-1135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt8(x::UInt128)   = checked_trunc_uint(UInt8, x)
-- /Source
def nativeToUInt8FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toUInt8 (.int .u128 x))

/-- Full concrete `toUInt16(x::Int8)` at `base/boot.jl:1137`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int8 bit pattern is included. -/
-- Source: base/boot.jl:1137-1137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt16(x::Int8)     = sext_int(UInt16, check_sign_bit(UInt16, x))
-- /Source
def nativeToUInt16FromInt8 (x : JInt .i8) : Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 (.int .i8 x)
    (JuliaLean.BootCov.IntConv.toUInt16 (.int .i8 x))

/-- Full concrete `toUInt16(x::Int16)` at `base/boot.jl:1138`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int16 bit pattern is included. -/
-- Source: base/boot.jl:1138-1138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt16(x::Int16)    = bitcast(UInt16, check_sign_bit(UInt16, x))
-- /Source
def nativeToUInt16FromInt16 (x : JInt .i16) : Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 (.int .i16 x)
    (JuliaLean.BootCov.IntConv.toUInt16 (.int .i16 x))

/-- Full concrete `toUInt16(x::Int32)` at `base/boot.jl:1139`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int32 bit pattern is included. -/
-- Source: base/boot.jl:1139-1139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt16(x::Int32)    = checked_trunc_uint(UInt16, x)
-- /Source
def nativeToUInt16FromInt32 (x : JInt .i32) : Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 (.int .i32 x)
    (JuliaLean.BootCov.IntConv.toUInt16 (.int .i32 x))

/-- Full concrete `toUInt16(x::Int64)` at `base/boot.jl:1140`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int64 bit pattern is included. -/
-- Source: base/boot.jl:1140-1140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt16(x::Int64)    = checked_trunc_uint(UInt16, x)
-- /Source
def nativeToUInt16FromInt64 (x : JInt .i64) : Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 (.int .i64 x)
    (JuliaLean.BootCov.IntConv.toUInt16 (.int .i64 x))

/-- Full concrete `toUInt16(x::Int128)` at `base/boot.jl:1141`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1141-1141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt16(x::Int128)   = checked_trunc_uint(UInt16, x)
-- /Source
def nativeToUInt16FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toUInt16 (.int .i128 x))

/-- Full concrete `toUInt16(x::UInt32)` at `base/boot.jl:1144`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt32 bit pattern is included. -/
-- Source: base/boot.jl:1144-1144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt16(x::UInt32)   = checked_trunc_uint(UInt16, x)
-- /Source
def nativeToUInt16FromUInt32 (x : JInt .u32) : Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 (.int .u32 x)
    (JuliaLean.BootCov.IntConv.toUInt16 (.int .u32 x))

/-- Full concrete `toUInt16(x::UInt64)` at `base/boot.jl:1145`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt64 bit pattern is included. -/
-- Source: base/boot.jl:1145-1145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt16(x::UInt64)   = checked_trunc_uint(UInt16, x)
-- /Source
def nativeToUInt16FromUInt64 (x : JInt .u64) : Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 (.int .u64 x)
    (JuliaLean.BootCov.IntConv.toUInt16 (.int .u64 x))

/-- Full concrete `toUInt16(x::UInt128)` at `base/boot.jl:1146`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1146-1146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt16(x::UInt128)  = checked_trunc_uint(UInt16, x)
-- /Source
def nativeToUInt16FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toUInt16 (.int .u128 x))

/-- Full concrete `toUInt32(x::Int8)` at `base/boot.jl:1148`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int8 bit pattern is included. -/
-- Source: base/boot.jl:1148-1148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt32(x::Int8)     = sext_int(UInt32, check_sign_bit(UInt32, x))
-- /Source
def nativeToUInt32FromInt8 (x : JInt .i8) : Except NativeConversionError (JInt .u32) :=
  refineNativeResult .u32 (.int .i8 x)
    (JuliaLean.BootCov.IntConv.toUInt32 (.int .i8 x))

/-- Full concrete `toUInt32(x::Int16)` at `base/boot.jl:1149`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int16 bit pattern is included. -/
-- Source: base/boot.jl:1149-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt32(x::Int16)    = sext_int(UInt32, check_sign_bit(UInt32, x))
-- /Source
def nativeToUInt32FromInt16 (x : JInt .i16) : Except NativeConversionError (JInt .u32) :=
  refineNativeResult .u32 (.int .i16 x)
    (JuliaLean.BootCov.IntConv.toUInt32 (.int .i16 x))

/-- Full concrete `toUInt32(x::Int32)` at `base/boot.jl:1150`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int32 bit pattern is included. -/
-- Source: base/boot.jl:1150-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt32(x::Int32)    = bitcast(UInt32, check_sign_bit(UInt32, x))
-- /Source
def nativeToUInt32FromInt32 (x : JInt .i32) : Except NativeConversionError (JInt .u32) :=
  refineNativeResult .u32 (.int .i32 x)
    (JuliaLean.BootCov.IntConv.toUInt32 (.int .i32 x))

/-- Full concrete `toUInt32(x::Int64)` at `base/boot.jl:1151`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int64 bit pattern is included. -/
-- Source: base/boot.jl:1151-1151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt32(x::Int64)    = checked_trunc_uint(UInt32, x)
-- /Source
def nativeToUInt32FromInt64 (x : JInt .i64) : Except NativeConversionError (JInt .u32) :=
  refineNativeResult .u32 (.int .i64 x)
    (JuliaLean.BootCov.IntConv.toUInt32 (.int .i64 x))

/-- Full concrete `toUInt32(x::Int128)` at `base/boot.jl:1152`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1152-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt32(x::Int128)   = checked_trunc_uint(UInt32, x)
-- /Source
def nativeToUInt32FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .u32) :=
  refineNativeResult .u32 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toUInt32 (.int .i128 x))

/-- Full concrete `toUInt32(x::UInt64)` at `base/boot.jl:1156`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt64 bit pattern is included. -/
-- Source: base/boot.jl:1156-1156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt32(x::UInt64)   = checked_trunc_uint(UInt32, x)
-- /Source
def nativeToUInt32FromUInt64 (x : JInt .u64) : Except NativeConversionError (JInt .u32) :=
  refineNativeResult .u32 (.int .u64 x)
    (JuliaLean.BootCov.IntConv.toUInt32 (.int .u64 x))

/-- Full concrete `toUInt32(x::UInt128)` at `base/boot.jl:1157`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1157-1157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt32(x::UInt128)  = checked_trunc_uint(UInt32, x)
-- /Source
def nativeToUInt32FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .u32) :=
  refineNativeResult .u32 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toUInt32 (.int .u128 x))

/-- Full concrete `toUInt64(x::Int8)` at `base/boot.jl:1159`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int8 bit pattern is included. -/
-- Source: base/boot.jl:1159-1159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt64(x::Int8)     = sext_int(UInt64, check_sign_bit(UInt64, x))
-- /Source
def nativeToUInt64FromInt8 (x : JInt .i8) : Except NativeConversionError (JInt .u64) :=
  refineNativeResult .u64 (.int .i8 x)
    (JuliaLean.BootCov.IntConv.toUInt64 (.int .i8 x))

/-- Full concrete `toUInt64(x::Int16)` at `base/boot.jl:1160`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int16 bit pattern is included. -/
-- Source: base/boot.jl:1160-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt64(x::Int16)    = sext_int(UInt64, check_sign_bit(UInt64, x))
-- /Source
def nativeToUInt64FromInt16 (x : JInt .i16) : Except NativeConversionError (JInt .u64) :=
  refineNativeResult .u64 (.int .i16 x)
    (JuliaLean.BootCov.IntConv.toUInt64 (.int .i16 x))

/-- Full concrete `toUInt64(x::Int32)` at `base/boot.jl:1161`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int32 bit pattern is included. -/
-- Source: base/boot.jl:1161-1161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt64(x::Int32)    = sext_int(UInt64, check_sign_bit(UInt64, x))
-- /Source
def nativeToUInt64FromInt32 (x : JInt .i32) : Except NativeConversionError (JInt .u64) :=
  refineNativeResult .u64 (.int .i32 x)
    (JuliaLean.BootCov.IntConv.toUInt64 (.int .i32 x))

/-- Full concrete `toUInt64(x::Int64)` at `base/boot.jl:1162`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int64 bit pattern is included. -/
-- Source: base/boot.jl:1162-1162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt64(x::Int64)    = bitcast(UInt64, check_sign_bit(UInt64, x))
-- /Source
def nativeToUInt64FromInt64 (x : JInt .i64) : Except NativeConversionError (JInt .u64) :=
  refineNativeResult .u64 (.int .i64 x)
    (JuliaLean.BootCov.IntConv.toUInt64 (.int .i64 x))

/-- Full concrete `toUInt64(x::Int128)` at `base/boot.jl:1163`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1163-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt64(x::Int128)   = checked_trunc_uint(UInt64, x)
-- /Source
def nativeToUInt64FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .u64) :=
  refineNativeResult .u64 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toUInt64 (.int .i128 x))

/-- Full concrete `toUInt64(x::UInt128)` at `base/boot.jl:1168`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every UInt128 bit pattern is included. -/
-- Source: base/boot.jl:1168-1168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt64(x::UInt128)  = checked_trunc_uint(UInt64, x)
-- /Source
def nativeToUInt64FromUInt128 (x : JInt .u128) : Except NativeConversionError (JInt .u64) :=
  refineNativeResult .u64 (.int .u128 x)
    (JuliaLean.BootCov.IntConv.toUInt64 (.int .u128 x))

/-- Full concrete `toUInt128(x::Int8)` at `base/boot.jl:1170`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int8 bit pattern is included. -/
-- Source: base/boot.jl:1170-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt128(x::Int8)    = sext_int(UInt128, check_sign_bit(UInt128, x))
-- /Source
def nativeToUInt128FromInt8 (x : JInt .i8) : Except NativeConversionError (JInt .u128) :=
  refineNativeResult .u128 (.int .i8 x)
    (JuliaLean.BootCov.IntConv.toUInt128 (.int .i8 x))

/-- Full concrete `toUInt128(x::Int16)` at `base/boot.jl:1171`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int16 bit pattern is included. -/
-- Source: base/boot.jl:1171-1171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt128(x::Int16)   = sext_int(UInt128, check_sign_bit(UInt128, x))
-- /Source
def nativeToUInt128FromInt16 (x : JInt .i16) : Except NativeConversionError (JInt .u128) :=
  refineNativeResult .u128 (.int .i16 x)
    (JuliaLean.BootCov.IntConv.toUInt128 (.int .i16 x))

/-- Full concrete `toUInt128(x::Int32)` at `base/boot.jl:1172`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int32 bit pattern is included. -/
-- Source: base/boot.jl:1172-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt128(x::Int32)   = sext_int(UInt128, check_sign_bit(UInt128, x))
-- /Source
def nativeToUInt128FromInt32 (x : JInt .i32) : Except NativeConversionError (JInt .u128) :=
  refineNativeResult .u128 (.int .i32 x)
    (JuliaLean.BootCov.IntConv.toUInt128 (.int .i32 x))

/-- Full concrete `toUInt128(x::Int64)` at `base/boot.jl:1173`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int64 bit pattern is included. -/
-- Source: base/boot.jl:1173-1173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt128(x::Int64)   = sext_int(UInt128, check_sign_bit(UInt128, x))
-- /Source
def nativeToUInt128FromInt64 (x : JInt .i64) : Except NativeConversionError (JInt .u128) :=
  refineNativeResult .u128 (.int .i64 x)
    (JuliaLean.BootCov.IntConv.toUInt128 (.int .i64 x))

/-- Full concrete `toUInt128(x::Int128)` at `base/boot.jl:1174`.
Reuse exactly its installed source-mirrored native branch, retaining the original
target/input on any exception. Every Int128 bit pattern is included. -/
-- Source: base/boot.jl:1174-1174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt128(x::Int128)  = bitcast(UInt128, check_sign_bit(UInt128, x))
-- /Source
def nativeToUInt128FromInt128 (x : JInt .i128) : Except NativeConversionError (JInt .u128) :=
  refineNativeResult .u128 (.int .i128 x)
    (JuliaLean.BootCov.IntConv.toUInt128 (.int .i128 x))

/-- The complete `Int8(x::BuiltinInts)` constructor at `base/boot.jl:1184`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1184-1184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Int8(x::BuiltinInts)    = toInt8(x)::Int8
-- /Source
def nativeInt8Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .i8) :=
  refineNativeResult .i8 x (JuliaLean.BootCov.IntConv.toInt8 x)

/-- The complete `Int16(x::BuiltinInts)` constructor at `base/boot.jl:1185`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1185-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Int16(x::BuiltinInts)   = toInt16(x)::Int16
-- /Source
def nativeInt16Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .i16) :=
  refineNativeResult .i16 x (JuliaLean.BootCov.IntConv.toInt16 x)

/-- The complete `Int32(x::BuiltinInts)` constructor at `base/boot.jl:1186`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1186-1186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Int32(x::BuiltinInts)   = toInt32(x)::Int32
-- /Source
def nativeInt32Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .i32) :=
  refineNativeResult .i32 x (JuliaLean.BootCov.IntConv.toInt32 x)

/-- The complete `Int64(x::BuiltinInts)` constructor at `base/boot.jl:1187`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1187-1187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Int64(x::BuiltinInts)   = toInt64(x)::Int64
-- /Source
def nativeInt64Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .i64) :=
  refineNativeResult .i64 x (JuliaLean.BootCov.IntConv.toInt64 x)

/-- The complete `Int128(x::BuiltinInts)` constructor at `base/boot.jl:1188`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1188-1188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Int128(x::BuiltinInts)  = toInt128(x)::Int128
-- /Source
def nativeInt128Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .i128) :=
  refineNativeResult .i128 x (JuliaLean.BootCov.IntConv.toInt128 x)

/-- The complete `UInt8(x::BuiltinInts)` constructor at `base/boot.jl:1189`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1189-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- UInt8(x::BuiltinInts)   = toUInt8(x)::UInt8
-- /Source
def nativeUInt8Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .u8) :=
  refineNativeResult .u8 x (JuliaLean.BootCov.IntConv.toUInt8 x)

/-- The complete `UInt16(x::BuiltinInts)` constructor at `base/boot.jl:1190`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1190-1190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- UInt16(x::BuiltinInts)  = toUInt16(x)::UInt16
-- /Source
def nativeUInt16Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .u16) :=
  refineNativeResult .u16 x (JuliaLean.BootCov.IntConv.toUInt16 x)

/-- The complete `UInt32(x::BuiltinInts)` constructor at `base/boot.jl:1191`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1191-1191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- UInt32(x::BuiltinInts)  = toUInt32(x)::UInt32
-- /Source
def nativeUInt32Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .u32) :=
  refineNativeResult .u32 x (JuliaLean.BootCov.IntConv.toUInt32 x)

/-- The complete `UInt64(x::BuiltinInts)` constructor at `base/boot.jl:1192`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1192-1192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- UInt64(x::BuiltinInts)  = toUInt64(x)::UInt64
-- /Source
def nativeUInt64Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .u64) :=
  refineNativeResult .u64 x (JuliaLean.BootCov.IntConv.toUInt64 x)

/-- The complete `UInt128(x::BuiltinInts)` constructor at `base/boot.jl:1193`,
including every ten native integer types and Bool. The installed complete
table performs its concrete dispatch and source branch checks; JInt's result
type makes the source return assertion exact without an extra runtime call. -/
-- Source: base/boot.jl:1193-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- UInt128(x::BuiltinInts) = toUInt128(x)::UInt128
-- /Source
def nativeUInt128Ctor (x : JuliaLean.BootCov.IntConv.BuiltinInt) :
    Except NativeConversionError (JInt .u128) :=
  refineNativeResult .u128 x (JuliaLean.BootCov.IntConv.toUInt128 x)

/-- Complete `Signed(x::UInt8)` at `base/boot.jl:1206`. Call the complete
concrete Int8 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1206-1206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Signed(x::UInt8)    = Int8(x)
-- /Source
def nativeSignedFromUInt8 (x : JInt .u8) :
    Except NativeConversionError (JInt .i8) :=
  nativeInt8Ctor (.int .u8 x)

/-- Complete `Unsigned(x::Int8)` at `base/boot.jl:1207`. Call the complete
concrete UInt8 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1207-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Unsigned(x::Int8)   = UInt8(x)
-- /Source
def nativeUnsignedFromInt8 (x : JInt .i8) :
    Except NativeConversionError (JInt .u8) :=
  nativeUInt8Ctor (.int .i8 x)

/-- Complete `Signed(x::UInt16)` at `base/boot.jl:1208`. Call the complete
concrete Int16 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1208-1208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Signed(x::UInt16)   = Int16(x)
-- /Source
def nativeSignedFromUInt16 (x : JInt .u16) :
    Except NativeConversionError (JInt .i16) :=
  nativeInt16Ctor (.int .u16 x)

/-- Complete `Unsigned(x::Int16)` at `base/boot.jl:1209`. Call the complete
concrete UInt16 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1209-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Unsigned(x::Int16)  = UInt16(x)
-- /Source
def nativeUnsignedFromInt16 (x : JInt .i16) :
    Except NativeConversionError (JInt .u16) :=
  nativeUInt16Ctor (.int .i16 x)

/-- Complete `Signed(x::UInt32)` at `base/boot.jl:1210`. Call the complete
concrete Int32 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1210-1210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Signed(x::UInt32)   = Int32(x)
-- /Source
def nativeSignedFromUInt32 (x : JInt .u32) :
    Except NativeConversionError (JInt .i32) :=
  nativeInt32Ctor (.int .u32 x)

/-- Complete `Unsigned(x::Int32)` at `base/boot.jl:1211`. Call the complete
concrete UInt32 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1211-1211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Unsigned(x::Int32)  = UInt32(x)
-- /Source
def nativeUnsignedFromInt32 (x : JInt .i32) :
    Except NativeConversionError (JInt .u32) :=
  nativeUInt32Ctor (.int .i32 x)

/-- Complete `Signed(x::UInt64)` at `base/boot.jl:1212`. Call the complete
concrete Int64 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1212-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Signed(x::UInt64)   = Int64(x)
-- /Source
def nativeSignedFromUInt64 (x : JInt .u64) :
    Except NativeConversionError (JInt .i64) :=
  nativeInt64Ctor (.int .u64 x)

/-- Complete `Unsigned(x::Int64)` at `base/boot.jl:1213`. Call the complete
concrete UInt64 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1213-1213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Unsigned(x::Int64)  = UInt64(x)
-- /Source
def nativeUnsignedFromInt64 (x : JInt .i64) :
    Except NativeConversionError (JInt .u64) :=
  nativeUInt64Ctor (.int .i64 x)

/-- Complete `Signed(x::UInt128)` at `base/boot.jl:1214`. Call the complete
concrete Int128 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1214-1214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Signed(x::UInt128)  = Int128(x)
-- /Source
def nativeSignedFromUInt128 (x : JInt .u128) :
    Except NativeConversionError (JInt .i128) :=
  nativeInt128Ctor (.int .u128 x)

/-- Complete `Unsigned(x::Int128)` at `base/boot.jl:1215`. Call the complete
concrete UInt128 constructor at the exact source point; all original bits and
the conversion's complete error payload are retained. -/
-- Source: base/boot.jl:1215-1215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Unsigned(x::Int128) = UInt128(x)
-- /Source
def nativeUnsignedFromInt128 (x : JInt .i128) :
    Except NativeConversionError (JInt .u128) :=
  nativeUInt128Ctor (.int .i128 x)

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1.FloatConversion

open JuliaLean
open JuliaLean.base.boot
open JuliaLean.Promotion

/-!
Closed concrete dependencies for the three Float/Bool conversion wrappers in
`base/boot.jl:1217-1221`, on this packet's 64-bit Julia target.

`base/float.lean` is source-available but its import is not prebuilt. This small
local closure implements only the required Int64/UInt64 constructor instances
and their concrete floating callees, using the already imported C intrinsic
models. It does not compile that file or any missing baseline import.

FV is the installed raw-bit IEEE representation. Every Float16/32/64 bit
pattern is admitted, including subnormals, both zeros, infinities, quiet and
signaling NaNs, and every payload/sign. There is no host Float approximation.
The generated lower/upper-bound constants are computed with the same concrete
sitofp/uitofp/add intrinsics as the source generator, so Float16's infinities
and Float32/64's rounded integer endpoints are retained.

CoreOps.str/core/obj/tuple and `encode` below are pure value representations,
not behavior callbacks. Error construction calls the existing concrete
Models2Group1.inexactErrorCtor and keeps the function Symbol, target type,
and original input bit pattern. No dynamic dispatch callback is reachable.
The only resource abstraction is the existing immutable-constructor boundary:
GC, physical allocation, and resource exhaustion.
-/

/-- The exact three source floating types in `base/boot.jl:1217-1221`.
Their layouts are specified at `base/float.jl:105-123`.
-/
inductive FT where
  | f16 | f32 | f64
  deriving DecidableEq, Repr

/-- The installed IEEE format for each concrete source type.
Representation support for `base/boot.jl:1217-1221`; layouts at
`base/float.jl:105-123`.
-/
-- Source: base/boot.jl:1217-1221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Signed(x::Union{Float16, Float32, Float64, Bool})   = Int(x)
-- Unsigned(x::Union{Float16, Float32, Float64, Bool}) = UInt(x)
-- 
-- Integer(x::Integer) = x
-- Integer(x::Union{Float16, Float32, Float64}) = Int(x)
-- /Source
def FT.fmt : FT → Fmt
  | .f16 => half
  | .f32 => single
  | .f64 => double

/-- The entire raw-bit domain of a concrete source float, with no finiteness,
integrality, or range restriction. -/
-- Source: base/boot.jl:1217-1221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Signed(x::Union{Float16, Float32, Float64, Bool})   = Int(x)
-- Unsigned(x::Union{Float16, Float32, Float64, Bool}) = UInt(x)
-- 
-- Integer(x::Integer) = x
-- Integer(x::Union{Float16, Float32, Float64}) = Int(x)
-- /Source
abbrev FV (kind : FT) := Fl kind.fmt

/-- A source float retaining its concrete type and exact raw bits.
Representation of the Float16/Float32/Float64 union at `base/boot.jl:1221`.
-/
structure IEEEInput where
  kind : FT
  value : FV kind

/-- The entire source union at `base/boot.jl:1217-1218`; Bool remains a
separate type instead of being encoded as a floating point value.
-/
inductive FloatOrBool where
  | float (value : IEEEInput)
  | bool (value : Bool)

/-- Concrete generated `Tf(::Int64)` callee at `base/float.jl:243-249`.
Used to evaluate generated bounds and the fixed zero/one literals; integer
conversion and IEEE rounding are delegated only to the installed C primitive.
-/
-- Source: base/float.jl:243-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for t1 in (Float16, Float32, Float64)
--     for st in (Int8, Int16, Int32, Int64)
--         @eval begin
--             (::Type{$t1})(x::($st)) = sitofp($t1, x)
--             promote_rule(::Type{$t1}, ::Type{$st}) = $t1
--         end
--     end
--     for ut in (Bool, UInt8, UInt16, UInt32, UInt64)
--         @eval begin
--             (::Type{$t1})(x::($ut)) = uitofp($t1, x)
--             promote_rule(::Type{$t1}, ::Type{$ut}) = $t1
--         end
--     end
-- end
-- /Source
def fromInt64 (kind : FT) (value : JInt .i64) : FV kind :=
  C.jlSitofp kind.fmt (C.fromJInt value)

/-- Concrete generated `Tf(::UInt64)` callee at `base/float.jl:250-256`,
used for the UInt64 constructor's generated lower/upper constants.
-/
-- Source: base/float.jl:243-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for t1 in (Float16, Float32, Float64)
--     for st in (Int8, Int16, Int32, Int64)
--         @eval begin
--             (::Type{$t1})(x::($st)) = sitofp($t1, x)
--             promote_rule(::Type{$t1}, ::Type{$st}) = $t1
--         end
--     end
--     for ut in (Bool, UInt8, UInt16, UInt32, UInt64)
--         @eval begin
--             (::Type{$t1})(x::($ut)) = uitofp($t1, x)
--             promote_rule(::Type{$t1}, ::Type{$ut}) = $t1
--         end
--     end
-- end
-- /Source
def fromUInt64 (kind : FT) (value : JInt .u64) : FV kind :=
  C.jlUitofp kind.fmt (C.fromJInt value)

/-- The concrete IEEEFloat truncation selected by `trunc(x)` at
`base/rounding.jl:480`, through `round(x,RoundToZero)` at
`base/float.jl:458`. No keyword arguments are present in this call.
-/
-- Source: base/rounding.jl:480-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- trunc(x; kws...) = round(x, RoundToZero; kws...)
-- /Source
-- Source: base/float.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- round(x::IEEEFloat, ::RoundingMode{:ToZero})  = trunc_llvm(x)
-- /Source
def truncFloat {kind : FT} (value : FV kind) : FV kind :=
  C.jlTruncLlvm value

/-- Concrete `isinteger` closure for the three IEEE formats at
`base/floatfuncs.jl:51`. It executes truncation, subtraction, and equality with
the converted zero in source order, rather than substituting a mathematical
integrality test for the source body. The operator callees are the concrete
intrinsics at `base/float.jl:488,615`; zero/oftype/convert select the installed
Int64-to-float primitive at `base/number.jl:363` and `base/float.jl:243-249`.
-/
-- Source: base/floatfuncs.jl:51-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(x::AbstractFloat) = iszero(x - trunc(x)) # note: x == trunc(x) would be incorrect for x=Inf
-- /Source
def isIntegerFloat {kind : FT} (value : FV kind) : Bool :=
  let truncated := truncFloat value
  let remainder := C.jlSubFloat value truncated
  C.jlEqFloat remainder (fromInt64 kind (JInt.lit .i64 0))

/-- Concrete `unsafe_trunc(Int64,x)` callee at `base/float.jl:408-412`.
The checked constructor below calls it only after all source checks succeed.
As documented at `base/float.jl:390-397`, out-of-range unsafe truncation has no
particular numeric guarantee; the installed C primitive supplies its total
representation without being used to bypass the checks.
-/
-- Source: base/float.jl:408-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for Ti in (Int8, Int16, Int32, Int64)
--     @eval begin
--         unsafe_trunc(::Type{$Ti}, x::IEEEFloat) = fptosi($Ti, x)
--     end
-- end
-- /Source
def unsafeTruncInt64 {kind : FT} (value : FV kind) : JInt .i64 :=
  C.toJInt .i64 (C.jlFptosi (IntTy.bits .i64) value)

/-- Concrete `unsafe_trunc(UInt64,x)` callee at `base/float.jl:413-417`.
The checked constructor below reaches it only for finite, nonnegative,
integral values in the UInt64 range.
-/
-- Source: base/float.jl:413-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for Ti in (UInt8, UInt16, UInt32, UInt64)
--     @eval begin
--         unsafe_trunc(::Type{$Ti}, x::IEEEFloat) = fptoui($Ti, x)
--     end
-- end
-- /Source
def unsafeTruncUInt64 {kind : FT} (value : FV kind) : JInt .u64 :=
  C.toJInt .u64 (C.jlFptoui (IntTy.bits .u64) value)

/-- Complete Int64 constructor instances generated at
`base/float.jl:881-931` for Float16, Float32, and Float64. Since Int64 is signed
and is at least as wide as each source format, all three use the generator's
second branch: inclusive lower bound, strict upper bound, then isinteger.
The exact input representation is retained in the InexactError tuple.
-/
-- Source: base/float.jl:881-931 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for Ti in (Int8, Int16, Int32, Int64, Int128, UInt8, UInt16, UInt32, UInt64, UInt128)
--     for Tf in (Float16, Float32, Float64)
--         if Ti <: Unsigned || sizeof(Ti) < sizeof(Tf)
--             # Here `Tf(typemin(Ti))-1` is exact, so we can compare the lower-bound
--             # directly. `Tf(typemax(Ti))+1` is either always exactly representable, or
--             # rounded to `Inf` (e.g. when `Ti==UInt128 && Tf==Float32`).
--             @eval begin
--                 function round(::Type{$Ti},x::$Tf,::RoundingMode{:ToZero})
--                     if $(Tf(typemin(Ti))-one(Tf)) < x < $(Tf(typemax(Ti))+one(Tf))
--                         return unsafe_trunc($Ti,x)
--                     else
--                         throw(InexactError(:round, $Ti, x, RoundToZero))
--                     end
--                 end
--                 function (::Type{$Ti})(x::$Tf)
--                     # When typemax(Ti) is not representable by Tf but typemax(Ti) + 1 is,
--                     # then < Tf(typemax(Ti) + 1) is stricter than <= Tf(typemax(Ti)). Using
--                     # the former causes us to throw on UInt64(Float64(typemax(UInt64))+1)
--                     if ($(Tf(typemin(Ti))) <= x < $(Tf(typemax(Ti))+one(Tf))) && isinteger(x)
--                         return unsafe_trunc($Ti,x)
--                     else
--                         throw(InexactError($(Expr(:quote,nameof(Ti))), $Ti, x))
--                     end
--                 end
--             end
--         else
--             # Here `eps(Tf(typemin(Ti))) > 1`, so the only value which can be truncated to
--             # `Tf(typemin(Ti)` is itself. Similarly, `Tf(typemax(Ti))` is inexact and will
--             # be rounded up. For `Float16` and larger integer types, `Tf(typemin(Ti))` is
--             # `-Inf`, so the lower bound is made strict to exclude it.
--             lo = Tf(typemin(Ti))
--             lo_cmp = lo === Tf(-Inf) ? :(<) : :(<=)
--             @eval begin
--                 function round(::Type{$Ti},x::$Tf,::RoundingMode{:ToZero})
--                     if $lo_cmp($lo, x) && x < $(Tf(typemax(Ti)))
--                         return unsafe_trunc($Ti,x)
--                     else
--                         throw(InexactError(:round, $Ti, x, RoundToZero))
--                     end
--                 end
--                 function (::Type{$Ti})(x::$Tf)
--                     if ($(Tf(typemin(Ti))) <= x < $(Tf(typemax(Ti)))) && isinteger(x)
--                         return unsafe_trunc($Ti,x)
--                     else
--                         throw(InexactError($(Expr(:quote,nameof(Ti))), $Ti, x))
--                     end
--                 end
--             end
--         end
--     end
-- end
-- /Source
def int64FromIEEE {W L : Type} (ops : CoreOps W L)
    (encode : IEEEInput → L) (input : IEEEInput) : CoreM W L (JInt .i64) := do
  let value := input.value
  let lo := fromInt64 input.kind (JInt.typemin .i64)
  let hi := fromInt64 input.kind (JInt.typemax .i64)
  if (C.jlLeFloat lo value && C.jlLtFloat value hi) && isIntegerFloat value then
    pure (unsafeTruncInt64 value)
  else
    let args : JuliaLean.base.boot.Models2Group1.ConstructorTuple L :=
      { values := [coreV ops "Int64", .leaf (encode input)]
        size_ok := by change 2 ≤ IntTy.i64.max.toNat; decide }
    throw (objV ops (JuliaLean.base.boot.Models2Group1.inexactErrorCtor ops
      (.symbol "Int64") args))

/-- Complete UInt64 constructor instances generated at
`base/float.jl:881-931`. The unsigned generator branch applies to every source
format: inclusive converted zero, strict converted typemax-plus-one bound,
then isinteger. Addition of one is IEEE addition in the source format.
The exception preserves the original input, including NaN payload/sign bits.
-/
-- Source: base/float.jl:881-931 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for Ti in (Int8, Int16, Int32, Int64, Int128, UInt8, UInt16, UInt32, UInt64, UInt128)
--     for Tf in (Float16, Float32, Float64)
--         if Ti <: Unsigned || sizeof(Ti) < sizeof(Tf)
--             # Here `Tf(typemin(Ti))-1` is exact, so we can compare the lower-bound
--             # directly. `Tf(typemax(Ti))+1` is either always exactly representable, or
--             # rounded to `Inf` (e.g. when `Ti==UInt128 && Tf==Float32`).
--             @eval begin
--                 function round(::Type{$Ti},x::$Tf,::RoundingMode{:ToZero})
--                     if $(Tf(typemin(Ti))-one(Tf)) < x < $(Tf(typemax(Ti))+one(Tf))
--                         return unsafe_trunc($Ti,x)
--                     else
--                         throw(InexactError(:round, $Ti, x, RoundToZero))
--                     end
--                 end
--                 function (::Type{$Ti})(x::$Tf)
--                     # When typemax(Ti) is not representable by Tf but typemax(Ti) + 1 is,
--                     # then < Tf(typemax(Ti) + 1) is stricter than <= Tf(typemax(Ti)). Using
--                     # the former causes us to throw on UInt64(Float64(typemax(UInt64))+1)
--                     if ($(Tf(typemin(Ti))) <= x < $(Tf(typemax(Ti))+one(Tf))) && isinteger(x)
--                         return unsafe_trunc($Ti,x)
--                     else
--                         throw(InexactError($(Expr(:quote,nameof(Ti))), $Ti, x))
--                     end
--                 end
--             end
--         else
--             # Here `eps(Tf(typemin(Ti))) > 1`, so the only value which can be truncated to
--             # `Tf(typemin(Ti)` is itself. Similarly, `Tf(typemax(Ti))` is inexact and will
--             # be rounded up. For `Float16` and larger integer types, `Tf(typemin(Ti))` is
--             # `-Inf`, so the lower bound is made strict to exclude it.
--             lo = Tf(typemin(Ti))
--             lo_cmp = lo === Tf(-Inf) ? :(<) : :(<=)
--             @eval begin
--                 function round(::Type{$Ti},x::$Tf,::RoundingMode{:ToZero})
--                     if $lo_cmp($lo, x) && x < $(Tf(typemax(Ti)))
--                         return unsafe_trunc($Ti,x)
--                     else
--                         throw(InexactError(:round, $Ti, x, RoundToZero))
--                     end
--                 end
--                 function (::Type{$Ti})(x::$Tf)
--                     if ($(Tf(typemin(Ti))) <= x < $(Tf(typemax(Ti)))) && isinteger(x)
--                         return unsafe_trunc($Ti,x)
--                     else
--                         throw(InexactError($(Expr(:quote,nameof(Ti))), $Ti, x))
--                     end
--                 end
--             end
--         end
--     end
-- end
-- /Source
def uint64FromIEEE {W L : Type} (ops : CoreOps W L)
    (encode : IEEEInput → L) (input : IEEEInput) : CoreM W L (JInt .u64) := do
  let value := input.value
  let lo := fromUInt64 input.kind (JInt.typemin .u64)
  let hi := C.jlAddFloat (fromUInt64 input.kind (JInt.typemax .u64))
    (fromInt64 input.kind (JInt.lit .i64 1))
  if (C.jlLeFloat lo value && C.jlLtFloat value hi) && isIntegerFloat value then
    pure (unsafeTruncUInt64 value)
  else
    let args : JuliaLean.base.boot.Models2Group1.ConstructorTuple L :=
      { values := [coreV ops "UInt64", .leaf (encode input)]
        size_ok := by change 2 ≤ IntTy.i64.max.toNat; decide }
    throw (objV ops (JuliaLean.base.boot.Models2Group1.inexactErrorCtor ops
      (.symbol "UInt64") args))

/-- `Signed` on its entire Float16/32/64/Bool union at `base/boot.jl:1217`.
All dispatch is closed: each float selects the generated Int64 constructor
above, and Bool selects the installed concrete Int64/BuiltinInts constructor.
-/
-- Source: base/boot.jl:1217-1217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Signed(x::Union{Float16, Float32, Float64, Bool})   = Int(x)
-- /Source
def signed {W L : Type} (ops : CoreOps W L) (encode : IEEEInput → L) :
    FloatOrBool → CoreM W L (JInt .i64)
  | .float input => int64FromIEEE ops encode input
  | .bool value => Int64_ ops (.bool value)

/-- `Unsigned` on its entire Float16/32/64/Bool union at
`base/boot.jl:1218`. Its Bool branch uses the installed UInt64 constructor;
the float branches use the complete concrete constructors above.
-/
-- Source: base/boot.jl:1218-1218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Unsigned(x::Union{Float16, Float32, Float64, Bool}) = UInt(x)
-- /Source
def unsigned {W L : Type} (ops : CoreOps W L) (encode : IEEEInput → L) :
    FloatOrBool → CoreM W L (JInt .u64)
  | .float input => uint64FromIEEE ops encode input
  | .bool value => UInt64_ ops (.bool value)

/-- `Integer` on the entire Float16/32/64 union at `base/boot.jl:1221`.
It selects the exact same concrete Int64 constructor as Julia's source.
-/
-- Source: base/boot.jl:1221-1221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Integer(x::Union{Float16, Float32, Float64}) = Int(x)
-- /Source
def integer {W L : Type} (ops : CoreOps W L) (encode : IEEEInput → L)
    (input : IEEEInput) : CoreM W L (JInt .i64) :=
  int64FromIEEE ops encode input

end JuliaLean.base.boot.Models2Group1.FloatConversion


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Concrete stored metadata for the pointer, AddrSpace and Array-size methods.
Type-parameter tokens and opaque payloads preserve complete source values and
identities. Reading a stored tag or field is a projection, not an arbitrary
typeof/getfield/bitcast callback. The packet targets native Int64/UInt64.
-/

/-- A pointer with its actual Ptr parameter retained, including arbitrary
pointee types. The address is the native UInt bit pattern. Source: base/boot.jl:1203. -/
structure ParameterizedPointer (P : Type) where
  parameter : P
  address : JInt .u64

/-- The entire source union accepted by the Ptr constructor. A source pointer
can have a different parameter from the target. Source: base/boot.jl:1203. -/
inductive PointerInput (P : Type) where
  | signed (value : JInt .i64)
  | unsigned (value : JInt .u64)
  | pointer (value : ParameterizedPointer P)

/-- The source-selected Ptr DataType and its actual stored concreteness flag.
The family fixes primitive status and native width; free parameters can still
make a target nonconcrete. This metadata is read by jl_bitcast, not supplied as
an assumed correctness law. Source: base/boot.jl:1203; src/runtime_intrinsics.c:439-453. -/
structure PointerTarget (P : Type) where
  parameter : P
  isConcrete : Bool

/-- Bitcast retains every address bit and installs the selected Ptr parameter.
Every case calls the existing concrete integer/pointer bitcast behavior; the
actual target-concreteness check precedes that bitcast. There is no dereference
or conversion dispatch; allocation/GC of immutable primitive boxes is abstracted. Source: base/boot.jl:1203. -/
-- Source: base/boot.jl:1203-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (PT::Type{Ptr{T}} where T)(x::Union{Int,UInt,Ptr}=0) = bitcast(PT, x)
-- /Source
def pointerCtor {P : Type} (target : PointerTarget P) (input : PointerInput P) :
    JuliaLean.BootCov.R (ParameterizedPointer P) := do
  if !target.isConcrete then
    throw (.error "bitcast: target type not a leaf primitive type")
  let address := match input with
    | .signed value => (JuliaLean.BootCov.IntConv.ptrOfInt value).addr
    | .unsigned value => (JuliaLean.BootCov.IntConv.ptrOfUInt value).addr
    | .pointer value =>
        (JuliaLean.BootCov.IntConv.ptrOfPtr ⟨value.address⟩).addr
  pure { parameter := target.parameter, address := address }

/-- The optional-argument entry point uses source native Int zero before the
same concrete pointer bitcast. Source: base/boot.jl:1203. -/
-- Source: base/boot.jl:1203-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (PT::Type{Ptr{T}} where T)(x::Union{Int,UInt,Ptr}=0) = bitcast(PT, x)
-- /Source
def pointerDefault {P : Type} (target : PointerTarget P) :
    JuliaLean.BootCov.R (ParameterizedPointer P) :=
  pointerCtor target (.signed (JInt.lit .i64 0))

/-- AddrSpace carries its Backend parameter and its complete native byte.
Source: base/boot.jl:1204. -/
structure ParameterizedAddressSpace (P : Type) where
  backend : P
  bits : JInt .u8

/-- Actual AddrSpace DataType metadata. The source family fixes its primitive
byte layout; the concreteness bit remains a checked runtime field.
Source: base/boot.jl:1204; src/runtime_intrinsics.c:439-453. -/
structure AddressSpaceTarget (P : Type) where
  backend : P
  isConcrete : Bool

/-- The concrete byte bitcast first checks the actual target concreteness, then
preserves the chosen Backend parameter and every bit without a user conversion. Source: base/boot.jl:1204. -/
-- Source: base/boot.jl:1204-1204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (AS::Type{AddrSpace{Backend}} where Backend)(x::UInt8) = bitcast(AS, x)
-- /Source
def addressSpaceCtor {P : Type} (target : AddressSpaceTarget P) (x : JInt .u8) :
    JuliaLean.BootCov.R (ParameterizedAddressSpace P) := do
  if !target.isConcrete then
    throw (.error "bitcast: target type not a leaf primitive type")
  pure { backend := target.backend, bits := JuliaLean.BootCov.IntConv.addrSpaceOf x }

/-- The actual immutable native-Int size tuple stored in an Array header.
The UInt32 nfields bound follows DataTypeLayout.nfields in
base/runtime_internals.jl:626,716-723. No positivity requirement is needed by either field-read method.
This permits empty tuples and every native-Int field bit pattern.
Source: base/boot.jl:82-85,1287-1288. -/
structure ArraySizeTuple where
  values : List (JInt .i64)
  fieldCount : values.length ≤ (2^32-1 : Nat)

/-- Only fields observed by arraysize are exposed. The remaining native array
reference, element type and identity are retained opaquely rather than copied
or restricted. Source: base/boot.jl:82-85,1287-1288. -/
structure ConcreteArrayHeader (V : Type) where
  size : ArraySizeTuple
  otherFields : V

/-- Refine the existing BoundsError class with its original size tuple and
native Int index, so failed getfield preserves its Julia exception payload.
Source: base/boot.jl:1288 (getfield of the size tuple). -/
structure ArraySizeBoundsError where
  exception : JuliaLean.BootCov.Exc
  tuple : ArraySizeTuple
  index : JInt .i64

/-- Read the stored size tuple unchanged, without allocating, copying a mutable
array, invoking arbitrary getfield behavior or recomputing dimensions.
Source: base/boot.jl:1287. -/
-- Source: base/boot.jl:1287-1287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- arraysize(a::Array) = a.size
-- /Source
def arraySizeTuple {V : Type} (array : ConcreteArrayHeader V) : ArraySizeTuple :=
  array.size

/-- Follow the signed native comparison, including negative and zero indices.
The selected getfield performs its concrete bounds check; a trailing positive
dimension instead returns native Int one. The second source a.size read is kept
explicit and observes the same header because no intervening operation mutates
state. Source: base/boot.jl:1288. -/
-- Source: base/boot.jl:1288-1288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- arraysize(a::Array, i::Int) = sle_int(i, nfields(a.size)) ? getfield(a.size, i) : 1
-- /Source
def arraySizeAt {V : Type} (array : ConcreteArrayHeader V) (i : JInt .i64) :
    Except ArraySizeBoundsError (JInt .i64) := do
  let dimensions := array.size
  let count := JInt.wrap .i64 dimensions.values.length
  if JuliaLean.base.int.sle_int i count then
    let dimensions := array.size
    if i.val < 1 then
      throw { exception := .bounds, tuple := dimensions, index := i }
    match dimensions.values[(i.val - 1).toNat]? with
    | some dimension => pure dimension
    | none => throw { exception := .bounds, tuple := dimensions, index := i }
  else
    pure (JInt.lit .i64 1)

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Complete selected DataType method of Core.typename at base/boot.jl:1311.
The actual initialized DataType.name field is a TypeName object identity, not
its printed spelling. Remaining metadata is opaque. DataType.name is a const
field initialized by type formation (src/jltypes.c:3600-3633), so this field read
has no missing-field or mutation branch. Physical GC addresses are abstracted.
-/

/-- Actual DataType metadata relevant to typename. `identity` names the type
object, `name` names its TypeName object, and `rest` retains unobserved fields.
Source: base/boot.jl:1311. -/
structure DataTypeNameMetadata (V : Type) where
  identity : Nat
  name : Nat
  rest : V

/-- The DataType method returns the stored TypeName object identity without
allocating or comparing strings. Source: base/boot.jl:1311. -/
-- Source: base/boot.jl:1311-1311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typename(a::DataType) = a.name
-- /Source
def typeNameDataType {V : Type} (value : DataTypeNameMetadata V) : Nat :=
  value.name

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Full Expr(args...) closure, base/boot.jl:327. The source-available original
src/builtins.c at the exact pin supplies jl_f__expr:2192-2207. Its checks are
not inferred from a tree-only convenience model. JL_NARGSV first requires at
least one argument; JL_TYPECHK next requires the actual first value to be a
Symbol; only then does allocation/copying occur. The macros are defined in
src/julia.h:2430-2436, and the exact too-few message is formed by
src/rtutils.c:102-105. No conversion or user dispatch is performed.

The original C source was recovered from an existing source-download cache,
not from another group's Lean models. Nine independent C blocks match the
packet's pinned excerpts at identical line numbers; its SHA256 and provenance
are recorded in NOTES.md. The successful allocation calls the already completed
identity-preserving allocExpr dependency. Its semantic allocation pair abstracts
only physical allocation order, GC and resource exhaustion; source-visible
reference sharing and all argument validation remain explicit.
-/

/-- A constructible Julia argument tuple. The actual runtime DataType layout
stores nfields as UInt32 (base/runtime_internals.jl:626,716-723); each argument
retains its full tagged value and any shared or cyclic object identity.
Source: base/boot.jl:327. -/
structure ExprArgumentTuple (L : Type) where
  values : List (Value L)
  arity : values.length ≤ (2^32-1 : Nat)

/-- Refined payload for the existing ArgumentError/TypeError classes raised by
jl_f__expr. A bad head retains func=Expr, empty context, expected Symbol and
the unchanged offending value. The arity error has the exact runtime message.
Source: src/builtins.c:2192-2207; src/julia.h:2430-2436;
src/rtutils.c:102-105,136-141. -/
structure ExprConstructorError (L : Type) where
  exception : JuliaLean.BootCov.Exc
  context : String
  expected : Option TypeVarExpected
  got : Option (Value L)

/-! Necessary concrete runtime closure, quoted from the pinned original C source. -/
-- Source: src/builtins.c:2192-2207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f__expr)
-- {
--     jl_task_t *ct = jl_current_task;
--     JL_NARGSV(Expr, 1);
--     JL_TYPECHK(Expr, symbol, args[0]);
--     jl_array_t *ar = jl_alloc_vec_any(nargs-1);
--     JL_GC_PUSH1(&ar);
--     for(size_t i=0; i < nargs-1; i++)
--         jl_array_ptr_set(ar, i, args[i+1]);
--     jl_expr_t *ex = (jl_expr_t*)jl_gc_alloc(ct->ptls, sizeof(jl_expr_t),
--                                             jl_expr_type);
--     ex->head = (jl_sym_t*)args[0];
--     ex->args = ar;
--     JL_GC_POP();
--     return (jl_value_t*)ex;
-- }
-- /Source

/-- The source-visible Expr constructor, including zero arguments and every
non-Symbol head. On success the first value becomes the head and every remaining
value is stored unchanged in the fresh Vector{Any}; on failure no Expr or argument
vector is allocated. Julia source: base/boot.jl:327. Runtime closure:
src/builtins.c:2192-2207 and the argument/type-check macros cited above. -/
-- Source: base/boot.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Expr(@nospecialize args...) = _expr(args...)
-- /Source
def exprConstructor {L : Type} (arguments : ExprArgumentTuple L) :
    ExceptT (ExprConstructorError L) (StateM (Heap L)) (Value L) := do
  match shape : arguments.values with
  | [] =>
      throw { exception := .argument "Expr: too few arguments (expected 1)",
              context := "", expected := none, got := none }
  | .symbol head :: tail =>
      have bound : tail.length ≤ IntTy.i64.max.toNat := by
        have arity := arguments.arity
        rw [shape] at arity
        simp only [List.length_cons] at arity
        exact Nat.le_trans (Nat.le_of_succ_le arity) (by decide)
      let heap ← get
      let allocated := allocExpr head tail bound heap
      set allocated.2
      pure allocated.1
  | head :: _ =>
      throw { exception := .typeError "Expr", context := "",
              expected := some .symbol, got := some head }

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Documentation marker, predicates and ignoredoc at `base/boot.jl:946-957`, on the
existing identity heap. Undefined Expr fields, undefined argument slots,
shared arrays, cyclic Expr graphs, and arbitrary opaque values are retained.
The selected Expr method recurses concretely, using partial_fixpoint rather
than a finite fuel cutoff. An endless where chain denotes divergence in the
existing CoreM semantics; physical stack exhaustion is abstracted.

Dispatch selection is explicit for the predicate and Expr branches. Each
custom flag means that Julia selected a method other than the fixed source
method on argument types the call site does not fix. The corresponding call is unrestricted: it may return any Julia
value, mutate both heap and external world, throw any value, or diverge. Flags
inspect the current world, so effects can change subsequent method selection.
No callback-correctness law is assumed. The fixed Expr method is always the
concrete recursion; the full-Any fallback body remains separately available.

firstarg dispatch occurs only after every slot of ex.args has been splatted.
The size_t count includes the function argument; jl_apply narrows it to UInt32
and subtracts one at UInt32 width. Thus generic firstarg dispatch is invoked on the prefix whose
length is array_length modulo 2^32, while undefined slots anywhere in the full
array still fail before that call. The array domain is not restricted to UInt32.
The firstarg call itself is an open generic call on unfixed element types and
arity, including zero arguments. Its interface retains every lookup failure,
method error, custom result, mutation and divergence; it does not assume that
the source fallback was entered. The selected firstarg body at951 is modeled
separately and is not used as a surrogate for generic dispatch here. In ignoredoc, only the actual || and && conditions assert
Bool. In particular a custom recursive iscallexpr result is not preemptively
restricted to Bool. Source/default Expr allocation uses the established concrete
allocExpr helper after preceding effects and retains argument references.
Generic Expr calls with arbitrary argument types retain their actual selected
custom constructors, including arbitrary return values and heap effects.

The temporary argument SimpleVector in src/builtins.c:914-936 is private: its
identity never escapes and no Julia callback runs between its allocation and
these concrete slot reads. Its physical allocation, GC and resource exhaustion
are within the existing allocator abstraction. The installed pinned source at
src/genericmemory.c:55-73 bounds an actual boxed Array's storage below 2^63-2
bytes, so adding the function slot and SimpleVector header fits UInt64 byte
arithmetic. The cached original builtins.c and julia.h establish all modeled
splat reads and the UInt32 call boundary. The body of jl_alloc_svec itself was
not present in the supplied mirrors or cached original-source files; no hidden
count cap is claimed or implemented. No smaller semantic cap is evidenced by
the available source. The model does not impose a UInt32 array-length limit.
-/

/-- Uninspected non-Expr kinds needed by `base/boot.jl:950,954-957`.
A QuoteNode's payload is opaque because these methods never read its value.
Every remaining Julia value is carried by other, with its identity unchanged. -/
inductive DocumentationAtom (L : Type) where
  | quoteNode (value : L)
  | nothing
  | other (value : L)

-- Source: base/boot.jl:950-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isbasicdoc(@nospecialize x) = (isa(x, Expr) && x.head === :.) || isa(x, Union{QuoteNode, Symbol})
-- firstarg(arg1, args...) = arg1
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- iscallexpr(ex) = false
-- function ignoredoc(source, mod, str, expr)
--     (isbasicdoc(expr) || iscallexpr(expr)) && return Expr(:escape, nothing)
--     Expr(:escape, expr)
-- end
-- /Source
abbrev DocumentationValue (L : Type) := Value (DocumentationAtom L)

/-- Actual heap plus arbitrary external runtime state. Custom dispatched
methods may mutate either component; concrete source reads do not. -/
structure DocumentationWorld (W L : Type) where
  heap : Heap (DocumentationAtom L)
  external : W

/-- Refined payload of the existing exception classes used by source reads
and conditional Bool checks. The Bool TypeError retains its
actual offending value. No new Julia exception class is introduced. -/
structure DocumentationRuntimeError (L : Type) where
  exception : JuliaLean.BootCov.Exc
  context : String := ""
  expected : Option String := none
  got : Option (DocumentationValue L) := none
  arguments : Option (List (DocumentationValue L)) := none

/-- Any Julia value may be thrown by an open custom dispatch target. -/
inductive DocumentationException (L : Type) where
  | runtime (error : DocumentationRuntimeError L)
  | custom (value : DocumentationValue L)

-- Source: base/boot.jl:950-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isbasicdoc(@nospecialize x) = (isa(x, Expr) && x.head === :.) || isa(x, Union{QuoteNode, Symbol})
-- firstarg(arg1, args...) = arg1
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- iscallexpr(ex) = false
-- function ignoredoc(source, mod, str, expr)
--     (isbasicdoc(expr) || iscallexpr(expr)) && return Expr(:escape, nothing)
--     Expr(:escape, expr)
-- end
-- /Source
abbrev DocumentationM (W L A : Type) :=
  CoreM (DocumentationWorld W L) (DocumentationException L) A

/-- Explicit source/default versus custom dispatch at the open predicate and
constructor call sites in `base/boot.jl:946-957`. The firstArgument field is the
actual generic firstarg call on unfixed element types/arity, including lookup
errors before any method body is entered. A custom iscallexpr selection applies
only to non-Expr inputs; the fixed concrete Expr method is never a callback. -/
structure DocumentationDispatch (W L : Type) where
  customBasicSelected : DocumentationWorld W L → DocumentationValue L → Bool
  customBasic : DocumentationValue L → DocumentationM W L (DocumentationValue L)
  firstArgument : List (DocumentationValue L) → DocumentationM W L (DocumentationValue L)
  customCallSelected : DocumentationWorld W L → DocumentationValue L → Bool
  customCall : DocumentationValue L → DocumentationM W L (DocumentationValue L)
  customExprSelected : DocumentationWorld W L → List (DocumentationValue L) → Bool
  customExpr : List (DocumentationValue L) → DocumentationM W L (DocumentationValue L)

/-- Raise an existing Julia exception class through the installed CoreM
interface, retaining its payload and current state. Source uses: `base/boot.jl:950,952,955`. -/
-- Source: base/boot.jl:952-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- /Source
def documentationThrow {W L A : Type} (error : DocumentationRuntimeError L) :
    DocumentationM W L A := throw (.leaf (.runtime error))

/-- Concrete Expr.head read. Undefined fields raise UndefRefError. Missing
references are outside the valid heap representation and use the same total
extension; every actual Expr reference denotes an existing cell.
Source: `base/boot.jl:950,952`. -/
-- Source: base/boot.jl:950-950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isbasicdoc(@nospecialize x) = (isa(x, Expr) && x.head === :.) || isa(x, Union{QuoteNode, Symbol})
-- /Source
def documentationHead {W L : Type} (ref : Nat) : DocumentationM W L SymbolName :=
  fun world =>
    match (readExpr world.heap ref).bind ExprCell.head with
    | some head => some (.ok (head, world))
    | none => documentationThrow { exception := .undefRef } world

/-- Concrete Expr.args read, including an undefined args field. A defined
field retains its existing mutable vector's identity and current slot state.
Source: `base/boot.jl:952`. -/
-- Source: base/boot.jl:952-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- /Source
def documentationArguments {W L : Type} (ref : Nat) :
    DocumentationM W L (VectorAny (DocumentationAtom L)) :=
  fun world =>
    match ((readExpr world.heap ref).bind ExprCell.args).bind (readArgs world.heap) with
    | some vector => some (.ok (vector, world))
    | none => documentationThrow { exception := .undefRef } world

/-- Full concrete Array{Any,1} splat: read all slots in source order before
dispatching firstarg; an undefined slot raises UndefRefError even after a
defined first slot. This is the local carrier version of the installed
essentials.splat/readAllAny behavior (essentials cannot be imported by boot).
Input comes from native-sized VectorAny; recursion does not perform Julia
integer arithmetic. Source call: `base/boot.jl:952`; splatting is documented in
`doc/src/manual/functions.md`, Varargs Functions. -/
-- Source: base/boot.jl:952-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- /Source
def documentationSplat {W L : Type} : List (Option (DocumentationValue L)) →
    DocumentationM W L (List (DocumentationValue L))
  | [] => pure []
  | none :: _ => documentationThrow { exception := .undefRef }
  | some value :: rest => do
    let values ← documentationSplat rest
    pure (value :: values)

/-- The concrete native call boundary after the full Array{Any,1} splat.
_apply_iterate counts the function plus all elements in size_t, then jl_apply
narrows that count to uint32 and subtracts one at uint32 width. The callee
therefore invokes generic dispatch on the original array prefix of length
modulo 2^32, not a restricted-size source array. This is the argument list at
jl_apply_generic entry; subsequent lookup outcomes remain in firstArgument. Source: `base/boot.jl:952`;
`src/builtins.c:1047-1049`, `src/julia.h:2596-2599`. -/
-- Source: src/julia.h:2596-2599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- STATIC_INLINE jl_value_t *jl_apply(jl_value_t **args, uint32_t nargs) JL_CANSAFEPOINT
-- {
--     return jl_apply_generic(args[0], &args[1], nargs - 1);
-- }
-- /Source
def documentationApplyArguments {L : Type} (values : List (DocumentationValue L)) :
    List (DocumentationValue L) :=
  let elements : JInt .u64 := JInt.wrap .u64 (values.length : Int)
  let withFunction := elements + JInt.lit .u64 1
  let calledArity := JInt.rem .u32 withFunction - JInt.lit .u32 1
  values.take calledArity.val.toNat

/-- The actual full-Any fallback body, also valid under invoke with an Expr
argument. It does not inspect that argument or redirect to another method.
Source: `base/boot.jl:953`. -/
-- Source: base/boot.jl:953-953 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex) = false
-- /Source
def documentationIsCallFallback {L : Type} (_value : DocumentationValue L) :
    DocumentationValue L := .bool false

/-- Dispatch on a non-Expr recursive result retains custom behavior; otherwise
the actual source fallback returns false. Source: `base/boot.jl:952-953`. -/
-- Source: base/boot.jl:952-953 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- iscallexpr(ex) = false
-- /Source
def documentationCallNonExpr {W L : Type} (dispatch : DocumentationDispatch W L)
    (value : DocumentationValue L) : DocumentationM W L (DocumentationValue L) :=
  fun world =>
    if dispatch.customCallSelected world value then dispatch.customCall value world
    else some (.ok (documentationIsCallFallback value, world))

/-- Complete selected iscallexpr(::Expr) body. Both head reads occur in their
source positions; a where node splats its full args vector before firstarg
dispatch, then concretely recurses on an Expr result. Other results retain
their selected generic dispatch. Shared/cyclic graphs are not unfolded into
trees, and no arbitrary recursion callback or finite fuel is introduced.
Source: `base/boot.jl:952`. -/
-- Source: base/boot.jl:952-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- /Source
def documentationIsCallExpr {W L : Type} (dispatch : DocumentationDispatch W L)
    (ref : Nat) : DocumentationM W L (DocumentationValue L) := do
  let head ← documentationHead ref
  if head == symbolName "where" then
    let vector ← documentationArguments ref
    let allArguments ← documentationSplat vector.data
    let arguments := documentationApplyArguments allArguments
    let first ← dispatch.firstArgument arguments
    match first with
    | .exprRef next => documentationIsCallExpr dispatch next
    | value => documentationCallNonExpr dispatch value
  else
    let head ← documentationHead ref
    pure (.bool (head == symbolName "call"))
partial_fixpoint

/-- Complete selected isbasicdoc body over all Julia values. An Expr's
undefined head is observable, while every other type test is concrete.
Source: `base/boot.jl:950`. -/
-- Source: base/boot.jl:950-950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isbasicdoc(@nospecialize x) = (isa(x, Expr) && x.head === :.) || isa(x, Union{QuoteNode, Symbol})
-- /Source
def documentationIsBasic {W L : Type} (value : DocumentationValue L) :
    DocumentationM W L (DocumentationValue L) := do
  match value with
  | .exprRef ref => pure (.bool ((← documentationHead ref) == symbolName "."))
  | .symbol _ => pure (.bool true)
  | .other (.quoteNode _) => pure (.bool true)
  | _ => pure (.bool false)

/-- Explicit generic isbasicdoc dispatch in ignoredoc, where the argument
type is unspecified. The source default always uses its concrete body above.
Source: `base/boot.jl:955`. -/
-- Source: base/boot.jl:954-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ignoredoc(source, mod, str, expr)
--     (isbasicdoc(expr) || iscallexpr(expr)) && return Expr(:escape, nothing)
--     Expr(:escape, expr)
-- end
-- /Source
def documentationBasicDispatch {W L : Type} (dispatch : DocumentationDispatch W L)
    (value : DocumentationValue L) : DocumentationM W L (DocumentationValue L) :=
  fun world =>
    if dispatch.customBasicSelected world value then dispatch.customBasic value world
    else documentationIsBasic value world

/-- The actual iscallexpr method is fixed for Expr, and selected explicitly
between source fallback and custom calls otherwise. Source: `base/boot.jl:952-955`. -/
-- Source: base/boot.jl:952-955 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iscallexpr(ex::Expr) = (isa(ex, Expr) && ex.head === :where) ? iscallexpr(firstarg(ex.args...)) : (isa(ex, Expr) && ex.head === :call)
-- iscallexpr(ex) = false
-- function ignoredoc(source, mod, str, expr)
--     (isbasicdoc(expr) || iscallexpr(expr)) && return Expr(:escape, nothing)
-- /Source
def documentationCallDispatch {W L : Type} (dispatch : DocumentationDispatch W L) :
    DocumentationValue L → DocumentationM W L (DocumentationValue L)
  | .exprRef ref => documentationIsCallExpr dispatch ref
  | value => documentationCallNonExpr dispatch value

/-- Actual conditional Bool assertion, without restricting custom return
values before they reach the ||/&& test. Non-Bool produces
TypeError(:if, "", Bool, value) with its original offending payload.
Source: `base/boot.jl:955`; `doc/src/manual/control-flow.md`, Short-Circuit Evaluation. -/
-- Source: base/boot.jl:955-955 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     (isbasicdoc(expr) || iscallexpr(expr)) && return Expr(:escape, nothing)
-- /Source
def documentationCondition {W L : Type} (value : DocumentationValue L) : DocumentationM W L Bool :=
  match value with
  | .bool b => pure b
  | _ => documentationThrow {
      exception := .typeError "if"
      expected := some "Bool"
      got := some value }

/-- The complete default Expr source body on a known Symbol head and an
actual UInt32-bounded argument tuple. All source validation is settled by
these representation fields; reuse the concrete fresh allocator. The proof
is a storage bound, not an assumed callee law. Source: `base/boot.jl:327,946-948,955-956`.
-/
-- Source: base/boot.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Expr(@nospecialize args...) = _expr(args...)
-- /Source
def documentationFixedExpression {W L : Type} (head : SymbolName)
    (arguments : List (DocumentationValue L))
    (arity : arguments.length + 1 ≤ (2^32 - 1 : Nat)) :
    DocumentationM W L (DocumentationValue L) :=
  fun world =>
    have bound : arguments.length ≤ IntTy.i64.max.toNat :=
      Nat.le_trans (Nat.le_of_succ_le arity) (by decide)
    let (value, heap) := allocExpr head arguments bound world.heap
    some (.ok (value, { world with heap }))

/-- Generic Expr calls with values of unspecified types retain selected
custom constructor methods. Dispatch receives the exact complete argument
list, including the fixed Symbol head, after preceding heap/world effects.
The source body remains concrete; custom methods may return any value, throw,
mutate or diverge. Source: `base/boot.jl:947,956`.
-/
-- Source: base/boot.jl:946-948 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro __doc__(x)
--     return Expr(:escape, Expr(:block, Expr(:meta, :doc), x))
-- end
-- /Source
def documentationExpressionDispatch {W L : Type} (dispatch : DocumentationDispatch W L)
    (head : SymbolName) (arguments : List (DocumentationValue L))
    (arity : arguments.length + 1 ≤ (2^32 - 1 : Nat)) :
    DocumentationM W L (DocumentationValue L) :=
  fun world =>
    let actualArguments := .symbol head :: arguments
    if dispatch.customExprSelected world actualArguments then
      dispatch.customExpr actualArguments world
    else
      documentationFixedExpression head arguments arity world

/-- Concrete fixed-Symbol metadata allocation precedes two generic Expr
calls. The block call sees the original arbitrary x; the outer escape call
sees the actual block result, including a non-Expr custom result. Both calls
select methods in their current world, and every custom effect/error/divergence
is retained. Source: `base/boot.jl:946-948`.
-/
-- Source: base/boot.jl:946-948 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro __doc__(x)
--     return Expr(:escape, Expr(:block, Expr(:meta, :doc), x))
-- end
-- /Source
def documentationMarkerMacro {W L : Type} (dispatch : DocumentationDispatch W L)
    (x : DocumentationValue L) : DocumentationM W L (DocumentationValue L) := do
  let metadata ← documentationFixedExpression (symbolName "meta") [.symbol (symbolName "doc")]
    (by simp only [List.length_cons, List.length_nil]; decide)
  let block ← documentationExpressionDispatch dispatch (symbolName "block") [metadata, x]
    (by simp only [List.length_cons, List.length_nil]; decide)
  documentationExpressionDispatch dispatch (symbolName "escape") [block]
    (by simp only [List.length_cons, List.length_nil]; decide)

/-- Lift the established fresh escape allocation through the current world.
Its caller in the true ignoredoc branches supplies fixed nothing; the false
branch uses the generic dispatch helper instead. Source: `base/boot.jl:955`.
-/
-- Source: base/boot.jl:955-955 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     (isbasicdoc(expr) || iscallexpr(expr)) && return Expr(:escape, nothing)
-- /Source
def documentationEscape {W L : Type} (argument : DocumentationValue L) :
    DocumentationM W L (DocumentationValue L) :=
  documentationFixedExpression (symbolName "escape") [argument]
    (by simp only [List.length_cons, List.length_nil]; decide)

/-- Complete ignoredoc: retain short-circuit order, type-check each actually
used conditional result, then call Expr after all preceding effects. Ignored
forms allocate an escape containing nothing. Other forms pass the exact original
expr to default/custom Expr dispatch; a source result is fresh, while custom
results remain unrestricted even after mutation of that original object.
Source: `base/boot.jl:954-957`. -/
-- Source: base/boot.jl:954-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ignoredoc(source, mod, str, expr)
--     (isbasicdoc(expr) || iscallexpr(expr)) && return Expr(:escape, nothing)
--     Expr(:escape, expr)
-- end
-- /Source
def documentationIgnore {W L : Type} (dispatch : DocumentationDispatch W L)
    (_source _mod _str expr : DocumentationValue L) : DocumentationM W L (DocumentationValue L) := do
  let basic ← documentationBasicDispatch dispatch expr
  if ← documentationCondition basic then
    return ← documentationEscape (.other .nothing)
  let call ← documentationCallDispatch dispatch expr
  if ← documentationCondition call then
    return ← documentationEscape (.other .nothing)
  documentationExpressionDispatch dispatch (symbolName "escape") [expr]
    (by simp only [List.length_cons, List.length_nil]; decide)

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-- The vararg tail of println(io, x...), after a real source call supplied its
fixed IO argument. Julia's callable nargs is UInt32, so the tail plus that fixed
argument fits UInt32. This is an actual call-arity invariant, not a restriction
to ordinary small argument lists. Source: base/boot.jl:1002; src/julia.h:2591-2598. -/
structure PrintingArguments (L : Type) where
  values : List (JuliaLean.base.expr.Value L)
  arity : values.length < (2^32-1 : Nat)

/-- These two calls dispatch on the source-unspecified concrete subtype of IO
and on arbitrary value types. Neither callback replaces a recursive invocation
of the selected vararg println body: the second call has the distinct zero-value
arity, with its own source method and possible more-specific IO methods.
Source: base/boot.jl:1001-1002. -/
structure LinePrintingDispatch (m : Type → Type) (L : Type) where
  printValues : JuliaLean.base.expr.Value L → PrintingArguments L →
    m (JuliaLean.base.expr.Value L)
  printNewline : JuliaLean.base.expr.Value L → m (JuliaLean.base.expr.Value L)

/-- The full vararg println body, including an empty tail selected explicitly
by invoke. Complete the first dispatched print before the newline call; preserve
the final call's arbitrary result, all effects, errors and divergence.
Source reference: base/boot.jl:1002. -/
-- Source: base/boot.jl:1002-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- println(io::IO, @nospecialize x...) = (print(io, x...); println(io))
-- /Source
def printlnValues {m : Type → Type} [Monad m] {L : Type}
    (dispatch : LinePrintingDispatch m L) (io : JuliaLean.base.expr.Value L)
    (values : PrintingArguments L) : m (JuliaLean.base.expr.Value L) := do
  let _ ← dispatch.printValues io values
  dispatch.printNewline io

/-- The one-argument show wrapper supplies the installed concrete stdout
singleton and forwards its unchanged arbitrary operand to generic show.
The operand's type is not fixed by this source method, so custom show dispatch
remains open. No jl_static_show behavior is supplied as a callback.
Source reference: base/boot.jl:1004. -/
-- Source: base/boot.jl:1004-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(@nospecialize a) = show(stdout, a)
-- /Source
def showStdout {m : Type → Type} {W L : Type} (encoding : CoreOps W L)
    (dispatch : PrintingDispatch m L) (value : JuliaLean.base.expr.Value L) :
    m (JuliaLean.base.expr.Value L) :=
  dispatch.showValue (JuliaLean.base.boot.stdout encoding) value

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1.Reflection

open JuliaLean

/-!
Concrete runtime metadata for Typeof, captured-variable typing, and kwftype.
The input is the actual immutable type-parameter/bound graph, with shared
object identities retained when the finite graph is expanded. DataType field
types, supertypes, TypeName caches and arbitrary object payloads are retained
opaquely because these methods do not traverse them. The source graph relevant
here is finite: type parameters and Union/UnionAll fields are fixed, and even
TypeVar's identity-bearing bounds are const (src/jltypes.c:3713-3719).

Stored DataType.hasfreetypevars is the actual runtime cache field read by the
pinned C algorithm, not a supplied Boolean answer for an arbitrary value.
For nested binders the body recursively scans parameters with TypeVar identity
scope, just as C does. The source's full kind set is explicit, including
TypeEq, TypeEgal and TypeofBottom. TypeVar, TypeApp, Intersect and Vararg are
not silently classified as values satisfying isa(_,Type).

Runtime type tags are data, represented by the actual jl_small_typeof table
and a stored header for other values. There is no typeof/isa/free-variable/
canonicalization callback. Nat identities are object names, not Julia integer
computations. Physical addresses, GC and resource exhaustion are abstracted.

General TypeEqOf remains outside this closure: jl_wrap_Type can canonicalize
a closed parameter using jl_types_equal. In Typeof, only a parameter already
found to have free type variables reaches that constructor, making its
canonicalization branch unreachable. The specialized helper below carries
that directly computed branch fact, rather than assuming a callee law.
-/

/-- An existing object's identity and actual runtime DataType header. Used for
the stored TypeName.wrapper reference and for ordinary Julia values.
Source: src/julia.h:197-207,1175-1193; src/jltypes.c:2192-2205.
-/
structure StoredReference where
  identity : Nat
  runtimeType : Nat

/-- The actual fixed runtime type objects reached by decoding the compact
kind tags. These are global data values, not type-reflection operations.
Source: src/julia.h:1109-1121,1175-1193; src/jltypes.c:3713-3792.
-/
structure RuntimeTypes where
  dataType : Nat
  unionAll : Nat
  unionType : Nat
  typeEq : Nat
  typeEgal : Nat
  typeofBottom : Nat
  typeVar : Nat
  typeApp : Nat
  intersect : Nat
  vararg : Nat
  bottomValue : Nat
  anyValue : Nat

/-- Actual source values relevant to the C free-variable traversal. TypeVar
binding is by object identity, not by the spelling in its opaque metadata.
DataType parameters are the logical sequence of an actual native-sized
SimpleVector. All source-reachable sequences obey the machine bound; this
model extends the non-arithmetic traversal to arbitrary finite sequences.
The separately defined NativeGraph predicate records the exact source domain.
A wrapper handle
may be absent while type metadata is being initialized; extract_wrapper
returns NULL in that case. The `other` case retains all remaining values and
their real runtime type headers, including mutable-object identities.
Source: src/jltypes.c:126-191,2192-2205; src/julia.h:1826-1842,1914-1917.
-/
inductive Value (V : Type) where
  | dataType (identity : Nat) (cachedHasFree : Bool) (parameters : List (Value V))
      (wrapper : Option StoredReference) (rest : V)
  | unionAll (identity boundVariable : Nat) (lower upper body : Value V) (rest : V)
  | unionType (identity : Nat) (left right : Value V)
  | typeEq (identity : Nat) (parameter : Value V)
  | typeEgal (identity : Nat) (parameter : Value V)
  | bottom
  | typeVar (identity : Nat) (lower upper : Value V) (rest : V)
  | typeApp (identity : Nat) (rest : V)
  | intersect (identity : Nat) (left right : Value V)
  | vararg (identity : Nat) (element count : Option (Value V)) (rest : V)
  | other (header : StoredReference) (payload : V)

mutual
/-- Representation invariant for actual native-sized SimpleVectors throughout
all fields traversed by the runtime. This bounds representation storage, not a
new runtime guard. Opaque payloads may retain arbitrary untraversed cycles.
Source: src/julia.h:1826-1842; src/jltypes.c:126-191.
-/
-- Source: src/julia.h:238-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- // Data is stored at the end of this variable-length struct.
-- typedef struct JL_GC_TRACKED_TYPE {
--     JL_DATA_TYPE
--     size_t length;
--     // pointer size aligned
--     // jl_value_t *data[];
-- } jl_svec_t;
-- /Source
def NativeGraph {V : Type} : Value V → Prop
  | .dataType _ _ parameters _ _ =>
      parameters.length ≤ IntTy.i64.max.toNat ∧ NativeParameters parameters
  | .unionAll _ _ lower upper body _ =>
      NativeGraph lower ∧ NativeGraph upper ∧ NativeGraph body
  | .unionType _ left right | .intersect _ left right =>
      NativeGraph left ∧ NativeGraph right
  | .typeEq _ parameter | .typeEgal _ parameter => NativeGraph parameter
  | .typeVar _ lower upper _ => NativeGraph lower ∧ NativeGraph upper
  | .vararg _ element count _ =>
      (∀ v, element = some v → NativeGraph v) ∧
      (∀ v, count = some v → NativeGraph v)
  | _ => True

/-- Logical conjunction of the native-storage invariants of every parameter.
Source: the SimpleVector parameter sequence in src/jltypes.c:158-164.
-/
-- Source: src/julia.h:1391-1394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #define jl_nparams(t)  jl_svec_len(((jl_datatype_t*)(t))->parameters)
-- #define jl_tparam0(t)  jl_svecref(((jl_datatype_t*)(t))->parameters, 0)
-- #define jl_tparam1(t)  jl_svecref(((jl_datatype_t*)(t))->parameters, 1)
-- #define jl_tparam2(t)  jl_svecref(((jl_datatype_t*)(t))->parameters, 2)
-- /Source
def NativeParameters {V : Type} : List (Value V) → Prop
  | [] => True
  | value :: rest => NativeGraph value ∧ NativeParameters rest
end

/-- An actual Julia value with native-bounded metadata storage. This field is
representation evidence, not a precondition checked by any source method.
Source: src/julia.h:1826-1842; src/jltypes.c:126-191.
-/
structure JuliaValue (V : Type) where
  object : Value V
  nativeGraph : NativeGraph object

/-- Observe the existing object's identity; no source arithmetic is performed.
Source: pointer-identity comparisons in src/jltypes.c:126-191,3268-3311.
-/
-- Source: src/jltypes.c:137-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             jl_unionall_t *ua = (jl_unionall_t*)v;
--             if (ua->var->lb != jl_bottom_type && has_free_typevars(ua->var->lb, env))
--                 return 1;
--             if (ua->var->ub != (jl_value_t*)jl_any_type && has_free_typevars(ua->var->ub, env))
--                 return 1;
--             jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
--             newenv->var = ua->var;
-- /Source
def objectIdentity {V : Type} (types : RuntimeTypes) : Value V → Nat
  | .dataType identity .. | .unionAll identity .. | .unionType identity ..
  | .typeEq identity .. | .typeEgal identity .. | .typeVar identity ..
  | .typeApp identity .. | .intersect identity .. | .vararg identity .. => identity
  | .bottom => types.bottomValue
  | .other header _ => header.identity

/-- Concrete typeof header decoding, using the actual compact-tag table for
the named cases and the object's stored DataType header otherwise.
Source: base/boot.jl:300-307,387,393; src/builtins.c:612-616 and
src/julia.h:197-207,1175-1193.
-/
-- Source: src/builtins.c:612-616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_typeof)
-- {
--     JL_NARGS(typeof, 1, 1);
--     return jl_typeof(args[0]);
-- }
-- /Source
def runtimeType {V : Type} (types : RuntimeTypes) : Value V → Nat
  | .dataType .. => types.dataType
  | .unionAll .. => types.unionAll
  | .unionType .. => types.unionType
  | .typeEq .. => types.typeEq
  | .typeEgal .. => types.typeEgal
  | .bottom => types.typeofBottom
  | .typeVar .. => types.typeVar
  | .typeApp .. => types.typeApp
  | .intersect .. => types.intersect
  | .vararg .. => types.vararg
  | .other header _ => header.runtimeType

/-- Concrete isa(value,Type): exactly the compact kind-tag interval identified
by jl_is_type. The specialized jl_isa case returns true for exactly these
kinds when its second argument is the fixed Type global.
Source: base/boot.jl:302,387; src/subtype.c:4253-4314,780-783,3210-3219,3796-3805;
src/julia.h:1109-1121,1900-1917. The non-kind jl_isa path falls
through to subtype, whose DataType-against-TypeEq case rejects every runtime
header outside the six kind globals and abstract AnyType. An ordinary value
cannot have abstract AnyType itself as its concrete runtime header.
-/
-- Source: src/julia.h:1907-1917 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- STATIC_INLINE int jl_is_kindtag(uintptr_t t) JL_NOTSAFEPOINT
-- {
--     t >>= 4;
--     return t - jl_typeofbottom_tag <= jl_datatype_tag - jl_typeofbottom_tag;
-- }
-- 
-- STATIC_INLINE int jl_is_type(jl_value_t *v) JL_NOTSAFEPOINT
-- {
--     return jl_is_kindtag(jl_typetagof(v));
-- }
-- /Source
def isType {V : Type} : Value V → Bool
  | .dataType .. | .unionAll .. | .unionType ..
  | .typeEq .. | .typeEgal .. | .bottom => true
  | _ => false

mutual
/-- Closed has_free_typevars traversal with its actual DataType cache fast
path, TypeVar identity environment, UnionAll bound checks before binding,
and precise TypeApp/Vararg/TypeEq/TypeEgal handling. Source:
src/jltypes.c:126-191, needed by base/boot.jl:303,387.
-/
-- Source: src/jltypes.c:126-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int has_free_typevars(jl_value_t *v, jl_typeenv_t *env) JL_NOTSAFEPOINT
-- {
--     while (1) {
--         if (jl_is_datatype(v) && (env == NULL || !((jl_datatype_t*)v)->hasfreetypevars))
--             return ((jl_datatype_t*)v)->hasfreetypevars;
--         if (jl_is_typevar(v)) {
--             return !typeenv_has(env, (jl_tvar_t*)v);
--         }
--         if (jl_is_typeapp(v))
--             return 1;
--         while (jl_is_unionall(v)) {
--             jl_unionall_t *ua = (jl_unionall_t*)v;
--             if (ua->var->lb != jl_bottom_type && has_free_typevars(ua->var->lb, env))
--                 return 1;
--             if (ua->var->ub != (jl_value_t*)jl_any_type && has_free_typevars(ua->var->ub, env))
--                 return 1;
--             jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
--             newenv->var = ua->var;
--             newenv->val = NULL;
--             newenv->prev = env;
--             env = newenv;
--             v = ua->body;
--         }
--         // After unwrapping UnionAll, body might be TypeApp or TypeVar;
--         // restart the loop so those checks at the top fire.
--         if (jl_is_typeapp(v) || jl_is_typevar(v))
--             continue;
--         if (jl_is_datatype(v)) {
--             int expect = ((jl_datatype_t*)v)->hasfreetypevars;
--             if (expect == 0 || env == NULL)
--                 return expect;
--             size_t i;
--             for (i = 0; i < jl_nparams(v); i++) {
--                 if (has_free_typevars(jl_tparam(v, i), env))
--                     return 1;
--             }
--             return 0;
--         }
--         else if (jl_is_uniontype(v) || jl_is_intersecttype(v)) {
--             if (has_free_typevars(((jl_uniontype_t*)v)->a, env))
--                 return 1;
--            v = ((jl_uniontype_t*)v)->b;
--         }
--         else if (jl_is_some_Type(v)) {
--             v = jl_some_Type_T(v);
--         }
--         else if (jl_is_vararg(v)) {
--             jl_vararg_t *vm = (jl_vararg_t*)v;
--             if (!vm->T)
--                 return 0;
--             if (vm->N) {
--                 if (has_free_typevars(vm->N, env))
--                     return 1;
--             }
--             v = vm->T;
--         }
--         else {
--             return 0;
--         }
--     }
-- }
-- 
-- JL_DLLEXPORT int jl_has_free_typevars(jl_value_t *v) JL_NOTSAFEPOINT
-- {
--     return has_free_typevars(v, NULL);
-- }
-- /Source
def hasFree {V : Type} (types : RuntimeTypes) (value : Value V)
    (bound : List Nat) : Bool :=
  match value with
  | .dataType _ cached parameters _ _ =>
      if bound.isEmpty || !cached then cached else hasFreeParameters types parameters bound
  | .typeVar identity .. => !(bound.contains identity)
  | .typeApp .. => true
  | .unionAll _ boundVariable lower upper body _ =>
      if objectIdentity types lower != types.bottomValue && hasFree types lower bound then true
      else if objectIdentity types upper != types.anyValue && hasFree types upper bound then true
      else hasFree types body (boundVariable :: bound)
  | .unionType _ left right | .intersect _ left right =>
      hasFree types left bound || hasFree types right bound
  | .typeEq _ parameter | .typeEgal _ parameter => hasFree types parameter bound
  | .vararg _ none _ _ => false
  | .vararg _ (some element) count _ =>
      (match count with | none => false | some count => hasFree types count bound) ||
        hasFree types element bound
  | _ => false

/-- Source-ordered scan of the actual DataType parameters, stopping at its
first free-variable occurrence. This is the for-loop in src/jltypes.c:163-169;
the native-sized SimpleVector bound is recorded by NativeGraph. The logical
list traversal performs no Julia integer arithmetic.
-/
-- Source: src/jltypes.c:158-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             for (i = 0; i < jl_nparams(v); i++) {
--                 if (has_free_typevars(jl_tparam(v, i), env))
--                     return 1;
--             }
--             return 0;
--         }
--         else if (jl_is_uniontype(v) || jl_is_intersecttype(v)) {
--             if (has_free_typevars(((jl_uniontype_t*)v)->a, env))
--                 return 1;
--            v = ((jl_uniontype_t*)v)->b;
--         }
--         else if (jl_is_some_Type(v)) {
--             v = jl_some_Type_T(v);
-- /Source
def hasFreeParameters {V : Type} (types : RuntimeTypes) (parameters : List (Value V))
    (bound : List Nat) : Bool :=
  match parameters with
  | [] => false
  | parameter :: rest => hasFree types parameter bound || hasFreeParameters types rest bound
end

/-- Concrete extract_wrapper traversal: follow UnionAll bodies, then read the
stored DataType name.wrapper; Union checks its left arm before its right, and
TypeVar forwards its upper bound. Other kinds produce NULL.
Source: src/jltypes.c:2192-2205,3268-3292.
-/
-- Source: src/jltypes.c:2192-2205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static jl_value_t *extract_wrapper(jl_value_t *t JL_PROPAGATES_ROOT) JL_NOTSAFEPOINT JL_GLOBALLY_ROOTED
-- {
--     t = jl_unwrap_unionall(t);
--     if (jl_is_datatype(t))
--         return ((jl_datatype_t*)t)->name->wrapper;
--     if (jl_is_uniontype(t)) {
--         jl_value_t *n1 = extract_wrapper(((jl_uniontype_t*)t)->a);
--         if (n1 != NULL) return n1;
--         return extract_wrapper(((jl_uniontype_t*)t)->b);
--     }
--     if (jl_is_typevar(t))
--         return extract_wrapper(((jl_tvar_t*)t)->ub);
--     return NULL;
-- }
-- /Source
def extractWrapper {V : Type} : Value V → Option StoredReference
  | .unionAll _ _ _ _ body _ => extractWrapper body
  | .dataType _ _ _ wrapper _ => wrapper
  | .unionType _ left right =>
      match extractWrapper left with
      | some wrapper => some wrapper
      | none => extractWrapper right
  | .typeVar _ _ upper _ => extractWrapper upper
  | _ => none

/-- The result retains either an existing type-object identity or the exact
parameter of a new immutable TypeEq/TypeEgal object. These two wrapper classes
are distinct and carry the original argument value, not a type-name string.
Source: src/jltypes.c:3268-3311 and base/boot.jl:5-16.
-/
inductive Result (V : Type) where
  | existing (identity : Nat)
  | equality (parameter : Value V)
  | egality (parameter : Value V)

/-- The only jl_wrap_Type calls needed here have already passed the actual
has_free_typevars test. The proof parameter is the source branch's computed
Bool result, not an assumption about a callee's correctness. In this domain
the apply_type validation succeeds because jl_valid_type_param accepts every
kind value (src/builtins.c:2041-2050,2076-2081). The initial Type{Union{}}
rewrite and bottom cache case cannot occur, and the
canonicalization conjunction stops at its false !has_free_typevars operand.
The concrete extract_wrapper traversal and pointer/type comparisons remain
explicit; the unreachable jl_types_equal branch is removed by that branch
invariant. Source: src/jltypes.c:3268-3292; base/boot.jl:303.
-/
-- Source: src/jltypes.c:3268-3292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_typeeq_t *jl_wrap_Type(jl_value_t *t)
-- {
--     if (jl_is_typeeq(t) && jl_typeeq_T(t) == jl_bottom_type)
--         t = (jl_value_t*)jl_typeofbottom_type;
--     jl_value_t *tw = extract_wrapper(t);
--     if (tw && tw != t && jl_typeof(t) == jl_typeof(tw) &&
--             !jl_has_free_typevars(t) && jl_types_equal(t, tw)) {
--         t = tw;
--     }
--     if (t == jl_bottom_type && jl_typeofbottom_type && jl_typeofbottom_type->name) {
--         jl_value_t *cached = jl_atomic_load_relaxed(&jl_typeofbottom_type->name->Typeofwrapper);
--         if (cached)
--             return (jl_typeeq_t*)cached;
--     }
--     jl_task_t *ct = jl_current_task;
--     JL_GC_PUSH1(&t);
--     jl_typeeq_t *te = (jl_typeeq_t*)jl_gc_alloc(ct->ptls, sizeof(jl_typeeq_t), jl_typeeq_type);
--     jl_set_typetagof(te, jl_typeeq_tag, 0);
--     te->T = t;
--     if (t == jl_bottom_type && jl_typeofbottom_type && jl_typeofbottom_type->name) {
--         jl_gc_write_atomic(jl_typeofbottom_type->name, jl_typeofbottom_type->name->Typeofwrapper, jl_value_t, (jl_value_t*)te, relaxed);
--     }
--     JL_GC_POP();
--     return te;
-- }
-- /Source
def wrapFreeType {V : Type} (types : RuntimeTypes) (value : Value V)
    (_isKind : isType value = true)
    (isFree : hasFree types value [] = true) : Result V :=
  let wrapper := extractWrapper value
  let eligible := match wrapper with
    | none => false
    | some wrapper =>
        wrapper.identity != objectIdentity types value &&
        runtimeType types value == wrapper.runtimeType
  if impossible : eligible && !(hasFree types value []) then
    False.elim (by simp [isFree] at impossible)
  else
    .equality value

/-- The jl_wrap_TypeEgal specialization reached only after the enclosing
method establishes isa(value,Type) and no free type variables. Its validation
cannot fail; the bottom singleton is normalized to its actual existing
TypeofBottom DataType, and every other parameter is retained exactly.
Source: src/jltypes.c:3294-3311; base/boot.jl:303.
-/
-- Source: src/jltypes.c:3294-3311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_value_t *jl_wrap_TypeEgal(jl_value_t *t)
-- {
--     // `TypeEgal` pins a type value by egality; non-type parameters and free
--     // typevars are not valid.
--     if (!jl_is_type(t) || jl_has_free_typevars(t))
--         jl_type_error_rt("TypeEgal", "parameter", (jl_value_t*)jl_type_type, t);
--     // `typeof(Union{})` already denotes exactly the single-instance set `{Union{}}`
--     // (the bottom object is unique), so normalize to it
--     if (t == jl_bottom_type)
--         return (jl_value_t*)jl_typeofbottom_type;
--     jl_task_t *ct = jl_current_task;
--     JL_GC_PUSH1(&t);
--     jl_value_t *te = jl_gc_alloc(ct->ptls, sizeof(jl_typeeq_t), jl_typeegal_type);
--     jl_set_typetagof(te, jl_typeegal_tag, 0);
--     ((jl_typeeq_t*)te)->T = t;
--     JL_GC_POP();
--     return te;
-- }
-- /Source
def wrapClosedType {V : Type} (types : RuntimeTypes) (value : Value V)
    (_isKind : isType value = true) (_isClosed : hasFree types value [] = false) : Result V :=
  match value with
  | .bottom => .existing types.typeofBottom
  | _ => .egality value

/-- Complete Typeof body for every Julia value, including all type-object
kinds and non-type values. It uses concrete stored tags, the real scoped
free-variable algorithm, and only the reachable concrete wrapper branches.
Source: base/boot.jl:300-307, with its toplevel generator context preserved.
-/
-- Source: base/boot.jl:297-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Typeof end
-- ccall(:jl_toplevel_eval_in, Any, (Any, Any),
--       Core, quote
--       (f::typeof(Typeof))(x) = begin
--           $(_expr(:meta,:nospecialize,:x))
--           if isa(x,Type)
--               has_free_typevars(x) ? Type{x} : TypeEgal{x}
--           else
--               typeof(x)
--           end
--       end
--       end)
-- 
-- # like `Typeof`, but yields the equality kind `Type{x}` for type values; used
-- /Source
def typeOf {V : Type} (types : RuntimeTypes) (input : JuliaValue V) : Result V :=
  let value := input.object
  if isKind : isType value = true then
    match isFree : hasFree types value [] with
    | true => wrapFreeType types value isKind isFree
    | false => wrapClosedType types value isKind isFree
  else
    .existing (runtimeType types value)

/-- Pure embeddings into the existing universal Core value carrier. These
fields identify original values and freshly formed immutable type wrappers;
they execute no Julia behavior and assume no callee-correctness law.
Source: base/boot.jl:387; representation boundary for the generic Typeof call.
-/
structure CapturedRepresentation (V L : Type) where
  input : JuliaValue V → JuliaLean.base.expr.Value L
  result : Result V → JuliaLean.base.expr.Value L

/-- Complete captured-variable typing helper. The source short-circuit skips
free-variable traversal for non-types; a free type value returns its actual
runtime DataType. Otherwise the generic Typeof call uses its selected method:
the source method is concrete typeOf above, while more-specific custom methods
run through the existing CoreOps.call interface with unrestricted return,
exception, state effects and divergence. Selection is actual dispatch metadata
at the call point, not a law about the selected operation. Even type-object
arguments may select a more-specific Type{user_type} method.
Source: base/boot.jl:387.
-/
-- Source: base/boot.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _typeof_captured_variable(@nospecialize t) = (@_total_meta; t isa Type && has_free_typevars(t) ? typeof(t) : Typeof(t))
-- /Source
def capturedVariableType {W V L : Type} (types : RuntimeTypes)
    (ops : JuliaLean.base.boot.CoreOps W L)
    (customSelected : W → JuliaValue V → Bool)
    (representation : CapturedRepresentation V L) (input : JuliaValue V) :
    JuliaLean.base.boot.CoreM W L (JuliaLean.base.expr.Value L) :=
  let value := input.object
  if isType value && hasFree types value [] then
    pure (representation.result (.existing (runtimeType types value)))
  else
    fun world =>
      if customSelected world input then
        ops.call (JuliaLean.base.boot.coreV ops "Typeof") [representation.input input] world
      else
        some (.ok (representation.result (typeOf types input), world))

/-- Stored Core.kwcall global object and its actual header. The payload is
the existing function object; the header is data, not a typeof callback.
Source: base/boot.jl:389-393; src/builtins.c:612-616.
-/
structure KeywordGlobal (V : Type) where
  object : V
  header : StoredReference

/-- The deprecated kwftype method ignores its input and reads the actual
runtime type header of the fixed Core.kwcall global.
Source: base/boot.jl:393.
-/
-- Source: base/boot.jl:393-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- kwftype(@nospecialize(t)) = typeof(kwcall)
-- /Source
def keywordFunctionType {V A : Type} (kwcall : KeywordGlobal V) (_input : A) : Nat :=
  kwcall.header.runtimeType

end JuliaLean.base.boot.Models2Group1.Reflection


namespace JuliaLean.base.boot.Models2Group1.AliasDispatch

open JuliaLean

/-!
Three complete source bodies whose inner calls retain genuine open dispatch.
Runtime type tags and immutable UnionAll body fields reuse the concrete
Reflection.Value metadata representation. No whole recursive body is supplied
as a callback: a source-selected _contains_typeapp call executes the recursion
below; only a more-specific selected method uses CoreOps.call.

CoreOps.call has unrestricted return values, exceptions, world effects and
divergence. The methods do not assert Bool or constructor result types that the
source does not assert. Value encodings are pure representation operations.
Physical allocation/GC/resource exhaustion use the existing abstraction.
-/

/-- Complete selected `_contains_typeapp` body. The actual TypeApp and UnionAll
tags are fixed runtime metadata. A UnionAll's actual immutable body is read
before dispatch selection; default selection recurses concretely, while a
custom method can return any Julia value and keeps all effects/errors/divergence.
The source never Bool-asserts a recursive result. Native parameter-storage bounds
are carried by Reflection.JuliaValue for actual inputs; uninspected metadata is
not a Julia operation, and this traversal performs no machine arithmetic.
Source: base/boot.jl:426-434; UnionAll fields are const/initialized in
src/jltypes.c:3728-3741. The encode field preserves the original body's identity.
-/
-- Source: base/boot.jl:426-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _contains_typeapp(@nospecialize(x))
--     if x isa TypeApp
--         return true
--     end
--     if x isa UnionAll
--         return _contains_typeapp(x.body)
--     end
--     return false
-- end
-- /Source
def containsTypeApp {W V L : Type} (ops : CoreOps W L)
    (customSelected : W → Reflection.Value V → Bool)
    (encode : Reflection.Value V → JuliaLean.base.expr.Value L) :
    Reflection.Value V → CoreM W L (JuliaLean.base.expr.Value L)
  | .typeApp .. => pure (boolV ops true)
  | .unionAll _ _ _ _ body _ =>
      fun world =>
        if customSelected world body then
          ops.call (coreV ops "_contains_typeapp") [encode body] world
        else
          containsTypeApp ops customSelected encode body world
  | _ => pure (boolV ops false)

/-- Complete selected three-argument TypeError body. Both calls are generic
on types this method does not fix: Symbol receives the original where value,
then the four-argument TypeError call receives that exact result, the literal
empty String, and the untouched source-typed expected and arbitrary got values.
Neither call is forced to return an instance of the constructor it names.
The declared expected::Type constraint is represented by selection of this
method, and no body operation further inspects or converts that argument.
Source: base/boot.jl:537-538.
-/
-- Source: base/boot.jl:537-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- TypeError(where, @nospecialize(expected::Type), @nospecialize(got)) =
--     TypeError(Symbol(where), "", expected, got)
-- /Source
def typeErrorFromWhere {W L : Type} (ops : CoreOps W L)
    (where_ expected got : JuliaLean.base.expr.Value L) :
    CoreM W L (JuliaLean.base.expr.Value L) := do
  let func ← ops.call (coreV ops "Symbol") [where_]
  ops.call (coreV ops "TypeError") [func, strV ops "", expected, got]

/-- Complete selected EnterNode convenience body. The old immutable node is
represented by its native destination and optional actual scope field; None
is an undefined field, distinct from every defined Julia value. The destination
is not read by the source. An undefined scope calls the installed concrete
one-argument constructor. A defined scope uses the selected two-argument
constructor: its source method is installed EnterNode2, while more-specific
methods on the unfixed scope type use unrestricted CoreOps.call. No type check
is added to custom constructor results.
Source: base/boot.jl:1292-1293, concrete constructors at 708-709.
-/
-- Source: base/boot.jl:1292-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- EnterNode(old::EnterNode, new_dest::Int) = isdefined(old, :scope) ?
--     EnterNode(new_dest, old.scope) : EnterNode(new_dest)
-- /Source
def enterNodeRetarget {W L : Type} (ops : CoreOps W L)
    (customSelected : W → I64 → JuliaLean.base.expr.Value L → Bool)
    (_oldDestination : I64) (scope : Option (JuliaLean.base.expr.Value L))
    (newDestination : I64) : CoreM W L (JuliaLean.base.expr.Value L) :=
  match scope with
  | none => pure (JuliaLean.base.boot.EnterNode1 newDestination)
  | some scope =>
      fun world =>
        if customSelected world newDestination scope then
          ops.call (coreV ops "EnterNode") [intV ops newDestination, scope] world
        else
          some (.ok (JuliaLean.base.boot.EnterNode2 newDestination scope, world))

end JuliaLean.base.boot.Models2Group1.AliasDispatch


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Complete GenericMemory constructor and reference wrappers, boot.jl:762-779.
Concrete helpers reproduce the pinned allocation and memoryrefnew C bodies.
Type descriptors expose actual stored runtime metadata, including the original
element parameter, kind bytes, address-space identity/tag, concrete-subtype bit,
layout, zero-initialization bit, and the cached zero-length memory identity.
The cache invariant is the C runtime's own type-layout invariant: a supported,
laid-out GenericMemory type already has its empty instance. It excludes the
unreachable abort after validation in jl_alloc_genericmemory; it is not a law
about a supplied operation. No type/layout/allocation callback is used.

Memory objects have fresh logical heap identities. Existing objects and the
type's cached empty object retain their identities, and references share their
original memory object. Natural-number identities are alpha-renamable heap
names, not Julia integer arithmetic. Physical base addresses, GC, and resource
exhaustion are abstracted; every source size/type/width check remains explicit.
A reference's UInt64 data records the exact pointer difference from its backing
base, or the actual element offset for union/zero-size storage. All pointer
increments and offset checks use native-width arithmetic, including wrapping.

Raw allocated bytes distinguish known zero from unspecified storage. `none`
means an unspecified raw byte, not a language-level undefined reference slot:
isbits storage is not falsely described as unassigned. Existing byte state can
contain arbitrary initialized or unspecified bytes. These constructors and
reference wrappers never dereference an element. A source-valid memory handle
denotes its live heap identity, immutable type metadata, and current length.

Int(i) is an open dispatch target because i has unspecified Integer
subtype. Constructor aliases also preserve methods selected on unspecified
GenericMemory parameters; custom results are unrestricted Julia values. It may mutate the heap/world, throw, diverge, or even return a non-Int.
The concrete builtin's Int assertion follows that call, before current memory
length/layout access. The builtin checks bounds even when its Bool is false,
as the pinned C source shows. No callback correctness/termination law is used.
-/

/-- Actual GenericMemory element layout fields read at
`src/genericmemory.c:75-102` and `src/builtins.c:2243-2298`. The byte size field
has its runtime UInt32 width; pointer storage has an eight-byte native word. -/
structure MemoryNativeLayout where
  size : JInt .u32
  boxed : Bool
  union : Bool

/-- The AddrSpace backend parameter. `other` excludes Core and preserves every
other admitted type-parameter value without inspecting it. Source: `base/boot.jl:65-66`. -/
inductive MemoryBackend (L : Type) where
  | core
  | other (value : JuliaLean.base.expr.Value L)

/-- GenericMemory kind parameter metadata. Type formation rejects concrete
non-Symbol kinds but admits a TypeVar (src/jltypes.c:2778-2790). The wider other
carrier includes those free parameters and total-extension cases; it never
excludes an actual existing GenericMemory type descriptor. -/
inductive MemoryKindParameter (L : Type) where
  | symbol (name : TypeVarName)
  | other (value : JuliaLean.base.expr.Value L)

/-- Actual eight-bit AddrSpace value, retaining its backend identity.
Source: `base/boot.jl:65-66`; `src/genericmemory.c:83-85`. -/
structure MemoryAddressSpace (L : Type) where
  backend : MemoryBackend L
  tag : JInt .u8

/-- GenericMemory address-space parameter metadata. Type formation checks
AddrSpace instances but admits free TypeVars (src/jltypes.c:2778-2790). The wider
other carrier retains these and total-extension cases. Allocation still checks
actual Core.CPU identity (genericmemory.c83-85), including non-CPU AddrSpace. -/
inductive MemoryAddressParameter (L : Type) where
  | address (value : MemoryAddressSpace L)
  | other (value : JuliaLean.base.expr.Value L)

/-- Concrete kind validation by raw Symbol name. Native-sized, NUL-free byte
names are inherited from the complete Symbol carrier, with no UTF-8 premise.
Source: `src/genericmemory.c:81-82`. -/
-- Source: src/genericmemory.c:75-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_genericmemory_t *jl_alloc_genericmemory(jl_value_t *mtype, size_t nel)
-- {
--     assert(jl_is_datatype(mtype));
--     jl_genericmemory_t *m = (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
--     if (m == NULL) {
--         jl_value_t *kind = jl_tparam0((jl_datatype_t*)mtype);
--         if (kind != (jl_value_t*)jl_not_atomic_sym && kind != (jl_value_t*)jl_atomic_sym)
--             jl_error("GenericMemory kind must be :not_atomic or :atomic");
--         jl_value_t *addrspace = jl_tparam2((jl_datatype_t*)mtype);
--         if (!jl_is_addrspacecore(addrspace) || jl_unbox_uint8(addrspace) != 0)
--             jl_error("GenericMemory addrspace must be Core.CPU");
--         if (!((jl_datatype_t*)mtype)->has_concrete_subtype || layout == NULL)
--             jl_type_error_rt("GenericMemory", "element type", (jl_value_t*)jl_type_type, jl_tparam1(mtype));
--         abort(); // this is checked already by jl_get_genericmemory_layout
--     }
--     assert(((jl_datatype_t*)mtype)->has_concrete_subtype && layout != NULL);
--     if (nel == 0) // zero-sized allocation optimization fast path
--         return m;
-- 
--     size_t elsz = layout->size;
--     int isboxed = layout->flags.arrayelem_isboxed;
--     int isunion = layout->flags.arrayelem_isunion;
--     int zi = ((jl_datatype_t*)mtype)->zeroinit;
--     if (isboxed)
--         elsz = sizeof(void*);
--     return _new_genericmemory_(mtype, nel, isunion, zi, elsz);
-- }
-- /Source
def memoryKindValid {L : Type} : MemoryKindParameter L → Bool
  | .symbol name =>
      name.bytes == symbolName "not_atomic" || name.bytes == symbolName "atomic"
  | .other _ => false

/-- Concrete Core.CPU identity check, including the AddrSpace{Core} backend
and zero UInt8 payload. Source: `src/genericmemory.c:83-85`. -/
-- Source: src/genericmemory.c:75-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_genericmemory_t *jl_alloc_genericmemory(jl_value_t *mtype, size_t nel)
-- {
--     assert(jl_is_datatype(mtype));
--     jl_genericmemory_t *m = (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
--     if (m == NULL) {
--         jl_value_t *kind = jl_tparam0((jl_datatype_t*)mtype);
--         if (kind != (jl_value_t*)jl_not_atomic_sym && kind != (jl_value_t*)jl_atomic_sym)
--             jl_error("GenericMemory kind must be :not_atomic or :atomic");
--         jl_value_t *addrspace = jl_tparam2((jl_datatype_t*)mtype);
--         if (!jl_is_addrspacecore(addrspace) || jl_unbox_uint8(addrspace) != 0)
--             jl_error("GenericMemory addrspace must be Core.CPU");
--         if (!((jl_datatype_t*)mtype)->has_concrete_subtype || layout == NULL)
--             jl_type_error_rt("GenericMemory", "element type", (jl_value_t*)jl_type_type, jl_tparam1(mtype));
--         abort(); // this is checked already by jl_get_genericmemory_layout
--     }
--     assert(((jl_datatype_t*)mtype)->has_concrete_subtype && layout != NULL);
--     if (nel == 0) // zero-sized allocation optimization fast path
--         return m;
-- 
--     size_t elsz = layout->size;
--     int isboxed = layout->flags.arrayelem_isboxed;
--     int isunion = layout->flags.arrayelem_isunion;
--     int zi = ((jl_datatype_t*)mtype)->zeroinit;
--     if (isboxed)
--         elsz = sizeof(void*);
--     return _new_genericmemory_(mtype, nel, isunion, zi, elsz);
-- }
-- /Source
def memoryAddressIsCPU {L : Type} : MemoryAddressParameter L → Bool
  | .address address =>
      match address.backend with
      | .core => address.tag.val == 0
      | .other _ => false
  | .other _ => false

/-- An existing GenericMemory DataType and its actual runtime metadata.
The original element parameter may be any admitted type parameter, including
invalid element arguments for which construction throws TypeError.
`cacheInvariant` is precisely the validity invariant asserted by the C source
after its null-instance validation; it rules out the source's impossible abort.
Source: `src/genericmemory.c:75-102`, especially lines 79-90. -/
structure MemoryNativeType (L : Type) where
  identity : Nat
  kind : MemoryKindParameter L
  element : JuliaLean.base.expr.Value L
  address : MemoryAddressParameter L
  hasConcreteSubtype : Bool
  layout : Option MemoryNativeLayout
  zeroInit : Bool
  cachedInstance : Option Nat
  cacheInvariant : (cachedInstance.isSome = true) ↔
    (memoryKindValid kind = true ∧ memoryAddressIsCPU address = true ∧
      hasConcreteSubtype = true ∧ layout.isSome = true)

/-- An actual GenericMemory object. Its immutable type metadata and layout
are fixed by its source type; mutable raw contents/length live in the heap.
Source-valid handles are live logical identities below heap.nextIdentity.
Source: `base/boot.jl:68-75`; `src/genericmemory.c:75-102`. -/
structure MemoryNativeObject (L : Type) where
  identity : Nat
  type : MemoryNativeType L
  layout : MemoryNativeLayout
  layout_eq : type.layout = some layout
  ready : type.cachedInstance.isSome = true

/-- Immutable GenericMemoryRef fields. `data` contains relative native pointer
bits, or element-offset bits for union/zero-size layouts; its interpretation is
fixed by the stored memory's actual layout. The original memory identity is
retained even when later dispatch changes that memory's current length.
Source: `base/boot.jl:77-80`; `src/builtins.c:2243-2298`. -/
structure MemoryNativeRef (L : Type) where
  memory : MemoryNativeObject L
  data : JInt .u64

/-- Current raw memory state. Count and byte count are native size_t values.
Only indices strictly below byteCount denote storage bytes; `none` there means
an unspecified raw byte. Unrelated mutable Julia state is retained separately.
Source: `src/genericmemory.c:55-73`. -/
structure MemoryNativeContents where
  length : JInt .u64
  byteCount : JInt .u64
  bytes : Nat → Option UInt8

/-- Heap identities and mutable memory contents. The total map is observed
only at live handles; entries beyond nextIdentity are unused placeholders.
Construction changes exactly one fresh entry and advances the fresh identity.
Source: `src/genericmemory.c:30-52,55-73`. -/
structure MemoryNativeHeap where
  nextIdentity : Nat
  contents : Nat → MemoryNativeContents

structure MemoryNativeWorld (W : Type) where
  heap : MemoryNativeHeap
  external : W

/-- BoundsError's actual first argument distinguishes memory from reference.
Source: `src/builtins.c:2267,2281,2286,2291`. -/
inductive MemoryBoundsValue (L : Type) where
  | memory (value : MemoryNativeObject L)
  | reference (value : MemoryNativeRef L)

/-- Refinement of existing exception classes with their source payloads.
TypeError retains context/expected/original got; BoundsError retains the exact
memory/reference and the converted Int index passed to the builtin.
Source: `src/genericmemory.c:81-87`; `src/builtins.c:2258-2292`. -/
structure MemoryNativeError (L : Type) where
  exception : JuliaLean.BootCov.Exc
  context : String := ""
  expected : Option String := none
  got : Option (JuliaLean.base.expr.Value L) := none
  boundsObject : Option (MemoryBoundsValue L) := none
  boundsIndex : Option (JInt .i64) := none

inductive MemoryNativeException (L : Type) where
  | runtime (error : MemoryNativeError L)
  | custom (value : JuliaLean.base.expr.Value L)

-- Source: base/boot.jl:762-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind} = memorynew(self, m)
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, d::NTuple{1,Int}) where {T,kind,addrspace} = self(undef, getfield(d,1))
-- # empty vector constructor
-- (self::Type{GenericMemory{kind,T,addrspace}})() where {T,kind,addrspace} = self(undef, 0)
-- 
-- # memoryref is simply convenience wrapper function around memoryrefnew
-- memoryref(mem::GenericMemory) = memoryrefnew(mem)
-- memoryref(mem::GenericMemory, i::Integer) = memoryrefnew(mem, Int(i), @_boundscheck)
-- memoryref(ref::GenericMemoryRef, i::Integer) = memoryrefnew(ref, Int(i), @_boundscheck)
-- GenericMemoryRef(mem::GenericMemory) = memoryref(mem)
-- GenericMemoryRef(mem::GenericMemory, i::Integer) = memoryref(mem, i)
-- GenericMemoryRef(mem::GenericMemoryRef, i::Integer) = memoryref(mem, i)
-- 
-- const AtomicMemory{T} = GenericMemory{:atomic, T, CPU}
-- const AtomicMemoryRef{T} = GenericMemoryRef{:atomic, T, CPU}
-- 
-- # construction helpers for Array
-- new_as_memoryref(self::Type{GenericMemoryRef{kind,T,addrspace}}, m::Int) where {T,kind,addrspace} = memoryref(fieldtype(self, :mem)(undef, m))
-- /Source
abbrev MemoryNativeM (W L A : Type) :=
  CoreM (MemoryNativeWorld W) (MemoryNativeException L) A

/-- All results of the open Int(i) dispatch: a native Int, or any other actual
value. A wrong result type is checked by the concrete memoryrefnew builtin at
its own source position. Source: `base/boot.jl:769-770`. -/
inductive MemoryIndexResult (L : Type) where
  | native (value : JInt .i64)
  | other (value : JuliaLean.base.expr.Value L)

/-- The sole open source dispatch target. It has no success, type-correctness,
state-preservation, or termination assumptions. Source: `base/boot.jl:769-770`. -/
structure MemoryNativeDispatch (W L : Type) where
  toInt : JuliaLean.base.expr.Value L → MemoryNativeM W L (MemoryIndexResult L)

/-- Any return value of a user-selected memoryref specialization. The aliases
at boot.jl:772-773 impose no result type assertion. -/
inductive MemoryAliasResult (L : Type) where
  | reference (value : MemoryNativeRef L)
  | other (value : JuliaLean.base.expr.Value L)

/-- The indexed constructor aliases call memoryref on an unspecified Integer
subtype. A more-specific custom method may be selected instead of the concrete
source wrapper. Selection reads the current world, and its unrestricted result,
effects, errors and divergence are preserved. The default branch still runs
the complete concrete memoryref body, including Int dispatch and validation.
Source: base/boot.jl:772-773. -/
structure MemoryNativeAliasDispatch (W L : Type) where
  native : MemoryNativeDispatch W L
  customSelected : MemoryNativeWorld W → MemoryBoundsValue L →
    JuliaLean.base.expr.Value L → Bool
  custom : MemoryBoundsValue L → JuliaLean.base.expr.Value L →
    MemoryNativeM W L (MemoryAliasResult L)

/-- Results of the constructor dispatch boundary. The first case records the
known installed constructor's tracked allocation. The second retains the full
value returned by selected user code, without a source-level type assertion.
This tag records the dispatch path, not a promised Julia return type: a custom
result can itself be any Base or user value. Source: base/boot.jl:763,765,779. -/
inductive MemoryConstructorResult (L : Type) where
  | memory (value : MemoryNativeObject L)
  | customResult (value : JuliaLean.base.expr.Value L)

/-- Genuine constructor and one-argument memoryref dispatch. A user's type
parameters can select a more-specific method despite the fixed undef/Int
arguments. Known default branches remain concrete. After an arbitrary custom
constructor returns, its result type is unfixed; the subsequent memoryref call
is therefore an open dispatch on that original value. Every operation retains
state, errors and divergence, and imposes no result-type or correctness law.
Source: base/boot.jl:763,765,771,779. -/
structure MemoryCreationDispatch (W L : Type) where
  constructorSelected : MemoryNativeWorld W → MemoryNativeType L → JInt .i64 → Bool
  constructor : MemoryNativeType L → JInt .i64 →
    MemoryNativeM W L (JuliaLean.base.expr.Value L)
  firstSelected : MemoryNativeWorld W → MemoryNativeObject L → Bool
  first : MemoryNativeObject L → MemoryNativeM W L (MemoryAliasResult L)
  afterCustomConstructor : JuliaLean.base.expr.Value L →
    MemoryNativeM W L (MemoryAliasResult L)

/-- A GenericMemoryRef DataType's fixed mem field type, with exactly the same
kind, element, and address-space parameters. This is stored type structure,
not an arbitrary fieldtype or type-application callback.
Source: `base/boot.jl:77-80,779`. -/
structure MemoryNativeRefType (L : Type) where
  memoryType : MemoryNativeType L

/-- Throw a refined existing exception without altering its state or payload.
Source: `src/genericmemory.c:81-87`; `src/builtins.c:2267-2292`. -/
-- Source: src/genericmemory.c:75-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_genericmemory_t *jl_alloc_genericmemory(jl_value_t *mtype, size_t nel)
-- {
--     assert(jl_is_datatype(mtype));
--     jl_genericmemory_t *m = (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
--     if (m == NULL) {
--         jl_value_t *kind = jl_tparam0((jl_datatype_t*)mtype);
--         if (kind != (jl_value_t*)jl_not_atomic_sym && kind != (jl_value_t*)jl_atomic_sym)
--             jl_error("GenericMemory kind must be :not_atomic or :atomic");
--         jl_value_t *addrspace = jl_tparam2((jl_datatype_t*)mtype);
--         if (!jl_is_addrspacecore(addrspace) || jl_unbox_uint8(addrspace) != 0)
--             jl_error("GenericMemory addrspace must be Core.CPU");
--         if (!((jl_datatype_t*)mtype)->has_concrete_subtype || layout == NULL)
--             jl_type_error_rt("GenericMemory", "element type", (jl_value_t*)jl_type_type, jl_tparam1(mtype));
--         abort(); // this is checked already by jl_get_genericmemory_layout
--     }
--     assert(((jl_datatype_t*)mtype)->has_concrete_subtype && layout != NULL);
--     if (nel == 0) // zero-sized allocation optimization fast path
--         return m;
-- 
--     size_t elsz = layout->size;
--     int isboxed = layout->flags.arrayelem_isboxed;
--     int isunion = layout->flags.arrayelem_isunion;
--     int zi = ((jl_datatype_t*)mtype)->zeroinit;
--     if (isboxed)
--         elsz = sizeof(void*);
--     return _new_genericmemory_(mtype, nel, isunion, zi, elsz);
-- }
-- /Source
def memoryNativeThrow {W L A : Type} (error : MemoryNativeError L) :
    MemoryNativeM W L A := throw (.leaf (.runtime error))

/-- Full fixed size-error message of the C allocator.
Source: `src/genericmemory.c:65-66`. -/
-- Source: src/genericmemory.c:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static jl_genericmemory_t *_new_genericmemory_(jl_value_t *mtype, size_t nel, int8_t isunion, int8_t zeroinit, size_t elsz) JL_CANSAFEPOINT
-- {
--     if (nel == 0) // zero-sized allocation optimization
--         return (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     size_t nbytes = 0; // initialized to workaround clang sa bug on v20: https://github.com/llvm/llvm-project/issues/136292
--     int overflow = __builtin_mul_overflow(nel, elsz, &nbytes);
--     if (isunion) {
--         // an extra byte for each isbits union memory element, stored at m->ptr + m->length
--         overflow |= __builtin_add_overflow(nel, nbytes, &nbytes);
--     }
--     if ((nel >= MAXINTVAL-1) || (nbytes >= MAXINTVAL-1) || overflow)
--         jl_exceptionf(jl_argumenterror_type, "invalid GenericMemory size: the number of elements is either negative or too large for system address width");
--     jl_task_t *ct = jl_current_task;
--     jl_genericmemory_t *m = jl_alloc_genericmemory_unchecked((jl_ptls_t) ct->ptls, nbytes, (jl_datatype_t*)mtype);
--     m->length = nel;
--     if (zeroinit)
--         memset((char*)m->ptr, 0, nbytes);
--     return m;
-- }
-- /Source
def memoryNativeSizeMessage : String :=
  "invalid GenericMemory size: the number of elements is either negative or too large for system address width"

/-- Native size_t checked product: preserve its UInt64 wrapped value and
overflow flag. Source: `src/genericmemory.c:60`. -/
-- Source: src/genericmemory.c:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static jl_genericmemory_t *_new_genericmemory_(jl_value_t *mtype, size_t nel, int8_t isunion, int8_t zeroinit, size_t elsz) JL_CANSAFEPOINT
-- {
--     if (nel == 0) // zero-sized allocation optimization
--         return (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     size_t nbytes = 0; // initialized to workaround clang sa bug on v20: https://github.com/llvm/llvm-project/issues/136292
--     int overflow = __builtin_mul_overflow(nel, elsz, &nbytes);
--     if (isunion) {
--         // an extra byte for each isbits union memory element, stored at m->ptr + m->length
--         overflow |= __builtin_add_overflow(nel, nbytes, &nbytes);
--     }
--     if ((nel >= MAXINTVAL-1) || (nbytes >= MAXINTVAL-1) || overflow)
--         jl_exceptionf(jl_argumenterror_type, "invalid GenericMemory size: the number of elements is either negative or too large for system address width");
--     jl_task_t *ct = jl_current_task;
--     jl_genericmemory_t *m = jl_alloc_genericmemory_unchecked((jl_ptls_t) ct->ptls, nbytes, (jl_datatype_t*)mtype);
--     m->length = nel;
--     if (zeroinit)
--         memset((char*)m->ptr, 0, nbytes);
--     return m;
-- }
-- /Source
def memoryNativeMul (a b : JInt .u64) : JInt .u64 × Bool :=
  (a * b, decide (IntTy.u64.max < a.val * b.val))

/-- Native size_t checked sum, for the union's selector bytes.
Source: `src/genericmemory.c:63`. -/
-- Source: src/genericmemory.c:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static jl_genericmemory_t *_new_genericmemory_(jl_value_t *mtype, size_t nel, int8_t isunion, int8_t zeroinit, size_t elsz) JL_CANSAFEPOINT
-- {
--     if (nel == 0) // zero-sized allocation optimization
--         return (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     size_t nbytes = 0; // initialized to workaround clang sa bug on v20: https://github.com/llvm/llvm-project/issues/136292
--     int overflow = __builtin_mul_overflow(nel, elsz, &nbytes);
--     if (isunion) {
--         // an extra byte for each isbits union memory element, stored at m->ptr + m->length
--         overflow |= __builtin_add_overflow(nel, nbytes, &nbytes);
--     }
--     if ((nel >= MAXINTVAL-1) || (nbytes >= MAXINTVAL-1) || overflow)
--         jl_exceptionf(jl_argumenterror_type, "invalid GenericMemory size: the number of elements is either negative or too large for system address width");
--     jl_task_t *ct = jl_current_task;
--     jl_genericmemory_t *m = jl_alloc_genericmemory_unchecked((jl_ptls_t) ct->ptls, nbytes, (jl_datatype_t*)mtype);
--     m->length = nel;
--     if (zeroinit)
--         memset((char*)m->ptr, 0, nbytes);
--     return m;
-- }
-- /Source
def memoryNativeAdd (a b : JInt .u64) : JInt .u64 × Bool :=
  (a + b, decide (IntTy.u64.max < a.val + b.val))

/-- The native unsigned count bound MAXINTVAL-1 used by the actual allocator.
Source: `src/genericmemory.c:27,65`. -/
-- Source: src/genericmemory.c:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static jl_genericmemory_t *_new_genericmemory_(jl_value_t *mtype, size_t nel, int8_t isunion, int8_t zeroinit, size_t elsz) JL_CANSAFEPOINT
-- {
--     if (nel == 0) // zero-sized allocation optimization
--         return (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     size_t nbytes = 0; // initialized to workaround clang sa bug on v20: https://github.com/llvm/llvm-project/issues/136292
--     int overflow = __builtin_mul_overflow(nel, elsz, &nbytes);
--     if (isunion) {
--         // an extra byte for each isbits union memory element, stored at m->ptr + m->length
--         overflow |= __builtin_add_overflow(nel, nbytes, &nbytes);
--     }
--     if ((nel >= MAXINTVAL-1) || (nbytes >= MAXINTVAL-1) || overflow)
--         jl_exceptionf(jl_argumenterror_type, "invalid GenericMemory size: the number of elements is either negative or too large for system address width");
--     jl_task_t *ct = jl_current_task;
--     jl_genericmemory_t *m = jl_alloc_genericmemory_unchecked((jl_ptls_t) ct->ptls, nbytes, (jl_datatype_t*)mtype);
--     m->length = nel;
--     if (zeroinit)
--         memset((char*)m->ptr, 0, nbytes);
--     return m;
-- }
-- /Source
def memoryNativeLimit : JInt .u64 := JInt.wrap .u64 ((2 : Int) ^ 63 - 2)

/-- Concrete unchecked allocation after validation: create a fresh memory
identity, set length, and clear exactly the data bytes when zeroinit is set.
Physical GC placement/exhaustion are abstracted; raw unspecified bytes remain
unspecified rather than becoming false language-level undef slots.
Source: `src/genericmemory.c:30-52,67-72`. -/
-- Source: src/genericmemory.c:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static jl_genericmemory_t *_new_genericmemory_(jl_value_t *mtype, size_t nel, int8_t isunion, int8_t zeroinit, size_t elsz) JL_CANSAFEPOINT
-- {
--     if (nel == 0) // zero-sized allocation optimization
--         return (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     size_t nbytes = 0; // initialized to workaround clang sa bug on v20: https://github.com/llvm/llvm-project/issues/136292
--     int overflow = __builtin_mul_overflow(nel, elsz, &nbytes);
--     if (isunion) {
--         // an extra byte for each isbits union memory element, stored at m->ptr + m->length
--         overflow |= __builtin_add_overflow(nel, nbytes, &nbytes);
--     }
--     if ((nel >= MAXINTVAL-1) || (nbytes >= MAXINTVAL-1) || overflow)
--         jl_exceptionf(jl_argumenterror_type, "invalid GenericMemory size: the number of elements is either negative or too large for system address width");
--     jl_task_t *ct = jl_current_task;
--     jl_genericmemory_t *m = jl_alloc_genericmemory_unchecked((jl_ptls_t) ct->ptls, nbytes, (jl_datatype_t*)mtype);
--     m->length = nel;
--     if (zeroinit)
--         memset((char*)m->ptr, 0, nbytes);
--     return m;
-- }
-- /Source
def memoryNativeAllocate {W L : Type} (type : MemoryNativeType L)
    (layout : MemoryNativeLayout) (layout_eq : type.layout = some layout)
    (ready : type.cachedInstance.isSome = true) (nel nbytes : JInt .u64) :
    MemoryNativeM W L (MemoryNativeObject L) :=
  fun world =>
    let identity := world.heap.nextIdentity
    let cell : MemoryNativeContents :=
      { length := nel, byteCount := nbytes,
        bytes := fun _ => if type.zeroInit then some 0 else none }
    let heap : MemoryNativeHeap :=
      { nextIdentity := identity + 1
        contents := fun key => if key = identity then cell else world.heap.contents key }
    some (.ok (⟨identity, type, layout, layout_eq, ready⟩, { world with heap }))

/-- Complete _new_genericmemory_ for a supported laid-out type. Every size_t
multiply/add and both MAXINTVAL-1 comparisons retain the source order; zero
returns the existing cached object before any size arithmetic.
Source: `src/genericmemory.c:55-73`. -/
-- Source: src/genericmemory.c:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static jl_genericmemory_t *_new_genericmemory_(jl_value_t *mtype, size_t nel, int8_t isunion, int8_t zeroinit, size_t elsz) JL_CANSAFEPOINT
-- {
--     if (nel == 0) // zero-sized allocation optimization
--         return (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     size_t nbytes = 0; // initialized to workaround clang sa bug on v20: https://github.com/llvm/llvm-project/issues/136292
--     int overflow = __builtin_mul_overflow(nel, elsz, &nbytes);
--     if (isunion) {
--         // an extra byte for each isbits union memory element, stored at m->ptr + m->length
--         overflow |= __builtin_add_overflow(nel, nbytes, &nbytes);
--     }
--     if ((nel >= MAXINTVAL-1) || (nbytes >= MAXINTVAL-1) || overflow)
--         jl_exceptionf(jl_argumenterror_type, "invalid GenericMemory size: the number of elements is either negative or too large for system address width");
--     jl_task_t *ct = jl_current_task;
--     jl_genericmemory_t *m = jl_alloc_genericmemory_unchecked((jl_ptls_t) ct->ptls, nbytes, (jl_datatype_t*)mtype);
--     m->length = nel;
--     if (zeroinit)
--         memset((char*)m->ptr, 0, nbytes);
--     return m;
-- }
-- /Source
def memoryNativeNew {W L : Type} (type : MemoryNativeType L)
    (layout : MemoryNativeLayout) (layout_eq : type.layout = some layout)
    (ready : type.cachedInstance.isSome = true) (emptyIdentity : Nat)
    (nel elsz : JInt .u64) : MemoryNativeM W L (MemoryNativeObject L) := do
  if nel.val = 0 then
    return ⟨emptyIdentity, type, layout, layout_eq, ready⟩
  let (nbytes, overflow) := memoryNativeMul nel elsz
  let (nbytes, overflow) :=
    if layout.union then
      let result := memoryNativeAdd nel nbytes
      (result.1, overflow || result.2)
    else (nbytes, overflow)
  if nel.val ≥ memoryNativeLimit.val || nbytes.val ≥ memoryNativeLimit.val || overflow then
    memoryNativeThrow { exception := .argument memoryNativeSizeMessage }
  else
    memoryNativeAllocate type layout layout_eq ready nel nbytes

/-- Complete concrete allocation type validation, cache fast path, boxed-size
selection, and call to the actual size-checked allocator. The final C abort
has no valid runtime input: the cacheInvariant supplies its contradiction.
Source: `src/genericmemory.c:75-102`. -/
-- Source: src/genericmemory.c:75-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_genericmemory_t *jl_alloc_genericmemory(jl_value_t *mtype, size_t nel)
-- {
--     assert(jl_is_datatype(mtype));
--     jl_genericmemory_t *m = (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
--     if (m == NULL) {
--         jl_value_t *kind = jl_tparam0((jl_datatype_t*)mtype);
--         if (kind != (jl_value_t*)jl_not_atomic_sym && kind != (jl_value_t*)jl_atomic_sym)
--             jl_error("GenericMemory kind must be :not_atomic or :atomic");
--         jl_value_t *addrspace = jl_tparam2((jl_datatype_t*)mtype);
--         if (!jl_is_addrspacecore(addrspace) || jl_unbox_uint8(addrspace) != 0)
--             jl_error("GenericMemory addrspace must be Core.CPU");
--         if (!((jl_datatype_t*)mtype)->has_concrete_subtype || layout == NULL)
--             jl_type_error_rt("GenericMemory", "element type", (jl_value_t*)jl_type_type, jl_tparam1(mtype));
--         abort(); // this is checked already by jl_get_genericmemory_layout
--     }
--     assert(((jl_datatype_t*)mtype)->has_concrete_subtype && layout != NULL);
--     if (nel == 0) // zero-sized allocation optimization fast path
--         return m;
-- 
--     size_t elsz = layout->size;
--     int isboxed = layout->flags.arrayelem_isboxed;
--     int isunion = layout->flags.arrayelem_isunion;
--     int zi = ((jl_datatype_t*)mtype)->zeroinit;
--     if (isboxed)
--         elsz = sizeof(void*);
--     return _new_genericmemory_(mtype, nel, isunion, zi, elsz);
-- }
-- /Source
def memoryNativeAlloc {W L : Type} (type : MemoryNativeType L) (nel : JInt .u64) :
    MemoryNativeM W L (MemoryNativeObject L) := do
  match hi : type.cachedInstance with
  | none =>
    if hk : memoryKindValid type.kind = true then
      if ha : memoryAddressIsCPU type.address = true then
        if hc : type.hasConcreteSubtype = true then
          match hl : type.layout with
          | none => memoryNativeThrow {
              exception := .typeError "GenericMemory", context := "element type",
              expected := some "Type", got := some type.element }
          | some _ =>
            have impossible : False := by
              have valid := type.cacheInvariant.mpr ⟨hk, ha, hc, by simp [hl]⟩
              simp [hi] at valid
            return (False.elim impossible)
        else memoryNativeThrow {
          exception := .typeError "GenericMemory", context := "element type",
          expected := some "Type", got := some type.element }
      else memoryNativeThrow {
        exception := .error "GenericMemory addrspace must be Core.CPU" }
    else memoryNativeThrow {
      exception := .error "GenericMemory kind must be :not_atomic or :atomic" }
  | some emptyIdentity =>
    have ready : type.cachedInstance.isSome = true := by simp [hi]
    match hl : type.layout with
    | none =>
      have impossible : False := by
        have valid := (type.cacheInvariant.mp ready).2.2.2
        simp [hl] at valid
      return (False.elim impossible)
    | some layout =>
      if nel.val = 0 then
        return ⟨emptyIdentity, type, layout, hl, ready⟩
      let elsz : JInt .u64 :=
        if layout.boxed then JInt.wrap .u64 8 else JInt.wrap .u64 layout.size.val
      memoryNativeNew type layout hl ready emptyIdentity nel elsz

/-- The concrete two-argument memorynew builtin after its source signature's
GenericMemory DataType and native-Int type checks. Negative native Int values
are reinterpreted as size_t exactly before allocation validation.
Source: `src/builtins.c:2233-2241`; called by `base/boot.jl:762`. -/
-- Source: src/builtins.c:2233-2241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_memorynew)
-- {
--     JL_NARGS(memorynew, 2, 2);
--     jl_datatype_t *jl_genericmemory_type_type = jl_datatype_type;
--     JL_TYPECHK(memorynew, genericmemory_type, args[0]);
--     JL_TYPECHK(memorynew, long, args[1]);
--     size_t nel = jl_unbox_long(args[1]);
--     return (jl_value_t*)jl_alloc_genericmemory(args[0], nel);
-- }
-- /Source
def memoryNativeBuiltinNew {W L : Type} (type : MemoryNativeType L) (n : JInt .i64) :
    MemoryNativeM W L (MemoryNativeObject L) :=
  memoryNativeAlloc type (JInt.wrap .u64 n.val)

/-- Full typed GenericMemory undef constructor. Source: `base/boot.jl:762`. -/
-- Source: base/boot.jl:762-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind} = memorynew(self, m)
-- /Source
def memoryUndefCtor {W L : Type} (type : MemoryNativeType L) (n : JInt .i64) :
    MemoryNativeM W L (MemoryNativeObject L) := memoryNativeBuiltinNew type n

/-- Select the actual GenericMemory undef constructor on its original type
parameters. Only the installed default invokes the concrete allocator.
Source: `base/boot.jl:763,765,779`. -/
-- Source: base/boot.jl:763-763 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, d::NTuple{1,Int}) where {T,kind,addrspace} = self(undef, getfield(d,1))
-- /Source
def memoryNativeConstruct {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (type : MemoryNativeType L) (n : JInt .i64) :
    MemoryNativeM W L (MemoryConstructorResult L) := fun world =>
  if dispatch.constructorSelected world type n then
    (do let result ← dispatch.constructor type n
        pure (MemoryConstructorResult.customResult result)) world
  else
    (do let memory ← memoryUndefCtor type n
        pure (MemoryConstructorResult.memory memory)) world

/-- Singleton tuple constructor: project its actual native Int field and
perform the selected constructor call, including arbitrary custom results.
Source: `base/boot.jl:763`. -/
-- Source: base/boot.jl:763-763 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, d::NTuple{1,Int}) where {T,kind,addrspace} = self(undef, getfield(d,1))
-- /Source
def memoryTupleCtor {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (type : MemoryNativeType L) (dimension : JInt .i64) :
    MemoryNativeM W L (MemoryConstructorResult L) :=
  memoryNativeConstruct dispatch type dimension

/-- The empty alias forwards native zero to the actual selected constructor.
The installed branch validates the type before returning its cached singleton;
a selected custom method can have any result/effect. Source: `base/boot.jl:765`. -/
-- Source: base/boot.jl:765-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})() where {T,kind,addrspace} = self(undef, 0)
-- /Source
def memoryEmptyCtor {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (type : MemoryNativeType L) : MemoryNativeM W L (MemoryConstructorResult L) :=
  memoryNativeConstruct dispatch type (JInt.wrap .i64 0)

/-- The one-argument memoryrefnew builtin: its concrete reference type retains
the original kind/element/address-space parameters and memory identity.
The data is index zero for union/zero-size storage and the backing base pointer
otherwise; both have relative native bit value zero in this representation.
No element or length is read, so empty memories are accepted.
Source: `src/builtins.c:2243-2255`; `src/genericmemory.c:299-308`. -/
-- Source: src/builtins.c:2243-2298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_memoryrefnew)
-- {
--     JL_NARGS(memoryrefnew, 1, 3);
--     if (nargs == 1) {
--         JL_TYPECHK(memoryrefnew, genericmemory, args[0]);
--         jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--         jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--         JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--         if (layout->flags.arrayelem_isunion || layout->size == 0)
--             return (jl_value_t*)jl_new_memoryref(typ, m, 0);
--         return (jl_value_t*)jl_new_memoryref(typ, m, m->ptr);
--     }
--     else {
--         JL_TYPECHK(memoryrefnew, long, args[1]);
--         if (nargs == 3)
--             JL_TYPECHK(memoryrefnew, bool, args[2]);
--         size_t i = (size_t) jl_unbox_long(args[1]) - 1;
--         char *data;
--         if (jl_is_genericmemory(args[0])) {
--             jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--             jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--             JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--             if (i >= m->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--             if (layout->flags.arrayelem_isunion || layout->size == 0)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)i);
--             else if (layout->flags.arrayelem_isboxed)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + sizeof(jl_value_t*)*i);
--             return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + layout->size*i);
--         }
--         JL_TYPECHK(memoryrefnew, genericmemoryref, args[0]);
--         jl_genericmemoryref_t *m = (jl_genericmemoryref_t*)args[0];
--         jl_genericmemory_t *mem = m->mem;
--         data = (char*)m->ptr_or_offset;
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(mem))->layout;
--         if (layout->flags.arrayelem_isboxed) {
--             if (((data - (char*)mem->ptr) / sizeof(jl_value_t*)) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += sizeof(jl_value_t*) * i;
--         }
--         else if (layout->flags.arrayelem_isunion || layout->size == 0) {
--             if ((size_t)data + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += i;
--         }
--         else {
--             if (((data - (char*)mem->ptr) / layout->size) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += layout->size * i;
--         }
--         return (jl_value_t*)jl_new_memoryref((jl_value_t*)jl_typetagof(m), mem, data);
--     }
-- }
-- 
-- /Source
def memoryNativeFirst {W L : Type} (memory : MemoryNativeObject L) :
    MemoryNativeM W L (MemoryNativeRef L) := do
  if memory.layout.union || memory.layout.size.val = 0 then
    pure ⟨memory, JInt.wrap .u64 0⟩
  else
    pure ⟨memory, JInt.wrap .u64 0⟩

/-- Native size_t division used by pointer-index decoding. For boxed storage,
C's sizeof denominator is size_t; ptrdiff is therefore read as unsigned.
Source: `src/builtins.c:2279-2282`. -/
-- Source: src/builtins.c:2243-2298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_memoryrefnew)
-- {
--     JL_NARGS(memoryrefnew, 1, 3);
--     if (nargs == 1) {
--         JL_TYPECHK(memoryrefnew, genericmemory, args[0]);
--         jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--         jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--         JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--         if (layout->flags.arrayelem_isunion || layout->size == 0)
--             return (jl_value_t*)jl_new_memoryref(typ, m, 0);
--         return (jl_value_t*)jl_new_memoryref(typ, m, m->ptr);
--     }
--     else {
--         JL_TYPECHK(memoryrefnew, long, args[1]);
--         if (nargs == 3)
--             JL_TYPECHK(memoryrefnew, bool, args[2]);
--         size_t i = (size_t) jl_unbox_long(args[1]) - 1;
--         char *data;
--         if (jl_is_genericmemory(args[0])) {
--             jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--             jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--             JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--             if (i >= m->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--             if (layout->flags.arrayelem_isunion || layout->size == 0)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)i);
--             else if (layout->flags.arrayelem_isboxed)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + sizeof(jl_value_t*)*i);
--             return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + layout->size*i);
--         }
--         JL_TYPECHK(memoryrefnew, genericmemoryref, args[0]);
--         jl_genericmemoryref_t *m = (jl_genericmemoryref_t*)args[0];
--         jl_genericmemory_t *mem = m->mem;
--         data = (char*)m->ptr_or_offset;
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(mem))->layout;
--         if (layout->flags.arrayelem_isboxed) {
--             if (((data - (char*)mem->ptr) / sizeof(jl_value_t*)) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += sizeof(jl_value_t*) * i;
--         }
--         else if (layout->flags.arrayelem_isunion || layout->size == 0) {
--             if ((size_t)data + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += i;
--         }
--         else {
--             if (((data - (char*)mem->ptr) / layout->size) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += layout->size * i;
--         }
--         return (jl_value_t*)jl_new_memoryref((jl_value_t*)jl_typetagof(m), mem, data);
--     }
-- }
-- 
-- /Source
def memoryNativeUnsignedQuotient (data : JInt .u64) (size : Int) : JInt .u64 :=
  JInt.wrap .u64 (data.val / size)

/-- Nonboxed pointer difference divided by layout->size. The UInt32 size
promotes to signed ptrdiff_t, so signed division truncates toward zero before
the later size_t addition. Every actual nonnegative offset has its usual
element index. Source: `src/builtins.c:2290-2293`. -/
-- Source: src/builtins.c:2243-2298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_memoryrefnew)
-- {
--     JL_NARGS(memoryrefnew, 1, 3);
--     if (nargs == 1) {
--         JL_TYPECHK(memoryrefnew, genericmemory, args[0]);
--         jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--         jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--         JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--         if (layout->flags.arrayelem_isunion || layout->size == 0)
--             return (jl_value_t*)jl_new_memoryref(typ, m, 0);
--         return (jl_value_t*)jl_new_memoryref(typ, m, m->ptr);
--     }
--     else {
--         JL_TYPECHK(memoryrefnew, long, args[1]);
--         if (nargs == 3)
--             JL_TYPECHK(memoryrefnew, bool, args[2]);
--         size_t i = (size_t) jl_unbox_long(args[1]) - 1;
--         char *data;
--         if (jl_is_genericmemory(args[0])) {
--             jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--             jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--             JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--             if (i >= m->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--             if (layout->flags.arrayelem_isunion || layout->size == 0)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)i);
--             else if (layout->flags.arrayelem_isboxed)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + sizeof(jl_value_t*)*i);
--             return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + layout->size*i);
--         }
--         JL_TYPECHK(memoryrefnew, genericmemoryref, args[0]);
--         jl_genericmemoryref_t *m = (jl_genericmemoryref_t*)args[0];
--         jl_genericmemory_t *mem = m->mem;
--         data = (char*)m->ptr_or_offset;
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(mem))->layout;
--         if (layout->flags.arrayelem_isboxed) {
--             if (((data - (char*)mem->ptr) / sizeof(jl_value_t*)) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += sizeof(jl_value_t*) * i;
--         }
--         else if (layout->flags.arrayelem_isunion || layout->size == 0) {
--             if ((size_t)data + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += i;
--         }
--         else {
--             if (((data - (char*)mem->ptr) / layout->size) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += layout->size * i;
--         }
--         return (jl_value_t*)jl_new_memoryref((jl_value_t*)jl_typetagof(m), mem, data);
--     }
-- }
-- 
-- /Source
def memoryNativeSignedQuotient (data : JInt .u64) (size : JInt .u32) : JInt .u64 :=
  JInt.wrap .u64 ((JInt.wrap .i64 data.val).val.tdiv size.val)

/-- Indexed memory-input branch of memoryrefnew: source UInt64 i-1, current
length read, unconditional bounds check, then union/zero/boxed/raw address
selection. The Bool is typed but not consulted by the runtime C body.
Source: `src/builtins.c:2257-2275`. -/
-- Source: src/builtins.c:2243-2298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_memoryrefnew)
-- {
--     JL_NARGS(memoryrefnew, 1, 3);
--     if (nargs == 1) {
--         JL_TYPECHK(memoryrefnew, genericmemory, args[0]);
--         jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--         jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--         JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--         if (layout->flags.arrayelem_isunion || layout->size == 0)
--             return (jl_value_t*)jl_new_memoryref(typ, m, 0);
--         return (jl_value_t*)jl_new_memoryref(typ, m, m->ptr);
--     }
--     else {
--         JL_TYPECHK(memoryrefnew, long, args[1]);
--         if (nargs == 3)
--             JL_TYPECHK(memoryrefnew, bool, args[2]);
--         size_t i = (size_t) jl_unbox_long(args[1]) - 1;
--         char *data;
--         if (jl_is_genericmemory(args[0])) {
--             jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--             jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--             JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--             if (i >= m->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--             if (layout->flags.arrayelem_isunion || layout->size == 0)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)i);
--             else if (layout->flags.arrayelem_isboxed)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + sizeof(jl_value_t*)*i);
--             return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + layout->size*i);
--         }
--         JL_TYPECHK(memoryrefnew, genericmemoryref, args[0]);
--         jl_genericmemoryref_t *m = (jl_genericmemoryref_t*)args[0];
--         jl_genericmemory_t *mem = m->mem;
--         data = (char*)m->ptr_or_offset;
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(mem))->layout;
--         if (layout->flags.arrayelem_isboxed) {
--             if (((data - (char*)mem->ptr) / sizeof(jl_value_t*)) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += sizeof(jl_value_t*) * i;
--         }
--         else if (layout->flags.arrayelem_isunion || layout->size == 0) {
--             if ((size_t)data + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += i;
--         }
--         else {
--             if (((data - (char*)mem->ptr) / layout->size) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += layout->size * i;
--         }
--         return (jl_value_t*)jl_new_memoryref((jl_value_t*)jl_typetagof(m), mem, data);
--     }
-- }
-- 
-- /Source
def memoryNativeIndexMemory {W L : Type} (memory : MemoryNativeObject L)
    (index : JInt .i64) (_boundscheck : Bool) : MemoryNativeM W L (MemoryNativeRef L) :=
  fun world =>
    let i : JInt .u64 := JInt.wrap .u64 index.val - JInt.wrap .u64 1
    let length := (world.heap.contents memory.identity).length
    if i.val ≥ length.val then
      memoryNativeThrow {
        exception := .bounds, boundsObject := some (.memory memory), boundsIndex := some index } world
    else
      let data :=
        if memory.layout.union || memory.layout.size.val = 0 then i
        else if memory.layout.boxed then JInt.wrap .u64 8 * i
        else JInt.wrap .u64 memory.layout.size.val * i
      some (.ok (⟨memory, data⟩, world))

/-- Indexed reference-input branch of memoryrefnew. The actual current memory
length is read after the caller's Int conversion. Source order distinguishes
boxed pointer words, union/zero-size offsets, and inline element bytes; each
native candidate index is checked before changing pointer-or-offset bits.
Source: `src/builtins.c:2276-2297`. -/
-- Source: src/builtins.c:2243-2298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_memoryrefnew)
-- {
--     JL_NARGS(memoryrefnew, 1, 3);
--     if (nargs == 1) {
--         JL_TYPECHK(memoryrefnew, genericmemory, args[0]);
--         jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--         jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--         JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--         if (layout->flags.arrayelem_isunion || layout->size == 0)
--             return (jl_value_t*)jl_new_memoryref(typ, m, 0);
--         return (jl_value_t*)jl_new_memoryref(typ, m, m->ptr);
--     }
--     else {
--         JL_TYPECHK(memoryrefnew, long, args[1]);
--         if (nargs == 3)
--             JL_TYPECHK(memoryrefnew, bool, args[2]);
--         size_t i = (size_t) jl_unbox_long(args[1]) - 1;
--         char *data;
--         if (jl_is_genericmemory(args[0])) {
--             jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--             jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--             JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--             if (i >= m->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--             if (layout->flags.arrayelem_isunion || layout->size == 0)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)i);
--             else if (layout->flags.arrayelem_isboxed)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + sizeof(jl_value_t*)*i);
--             return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + layout->size*i);
--         }
--         JL_TYPECHK(memoryrefnew, genericmemoryref, args[0]);
--         jl_genericmemoryref_t *m = (jl_genericmemoryref_t*)args[0];
--         jl_genericmemory_t *mem = m->mem;
--         data = (char*)m->ptr_or_offset;
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(mem))->layout;
--         if (layout->flags.arrayelem_isboxed) {
--             if (((data - (char*)mem->ptr) / sizeof(jl_value_t*)) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += sizeof(jl_value_t*) * i;
--         }
--         else if (layout->flags.arrayelem_isunion || layout->size == 0) {
--             if ((size_t)data + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += i;
--         }
--         else {
--             if (((data - (char*)mem->ptr) / layout->size) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += layout->size * i;
--         }
--         return (jl_value_t*)jl_new_memoryref((jl_value_t*)jl_typetagof(m), mem, data);
--     }
-- }
-- 
-- /Source
def memoryNativeIndexReference {W L : Type} (reference : MemoryNativeRef L)
    (index : JInt .i64) (_boundscheck : Bool) : MemoryNativeM W L (MemoryNativeRef L) :=
  fun world =>
    let i : JInt .u64 := JInt.wrap .u64 index.val - JInt.wrap .u64 1
    let length := (world.heap.contents reference.memory.identity).length
    let layout := reference.memory.layout
    let fail : MemoryNativeM W L (MemoryNativeRef L) := memoryNativeThrow {
      exception := .bounds, boundsObject := some (.reference reference), boundsIndex := some index }
    if layout.boxed then
      let candidate := memoryNativeUnsignedQuotient reference.data 8 + i
      if candidate.val ≥ length.val then fail world
      else some (.ok (⟨reference.memory, reference.data + JInt.wrap .u64 8 * i⟩, world))
    else if layout.union || layout.size.val = 0 then
      let candidate := reference.data + i
      if candidate.val ≥ length.val then fail world
      else some (.ok (⟨reference.memory, reference.data + i⟩, world))
    else
      let candidate := memoryNativeSignedQuotient reference.data layout.size + i
      if candidate.val ≥ length.val then fail world
      else some (.ok (⟨reference.memory,
        reference.data + JInt.wrap .u64 layout.size.val * i⟩, world))

/-- Concrete native Int assertion performed by memoryrefnew after open Int(i)
dispatch. Wrong returned values retain their original offending payload.
Source: `src/builtins.c:2257-2259`; `base/boot.jl:769-770`. -/
-- Source: src/builtins.c:2243-2298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_CALLABLE(jl_f_memoryrefnew)
-- {
--     JL_NARGS(memoryrefnew, 1, 3);
--     if (nargs == 1) {
--         JL_TYPECHK(memoryrefnew, genericmemory, args[0]);
--         jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--         jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--         JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--         if (layout->flags.arrayelem_isunion || layout->size == 0)
--             return (jl_value_t*)jl_new_memoryref(typ, m, 0);
--         return (jl_value_t*)jl_new_memoryref(typ, m, m->ptr);
--     }
--     else {
--         JL_TYPECHK(memoryrefnew, long, args[1]);
--         if (nargs == 3)
--             JL_TYPECHK(memoryrefnew, bool, args[2]);
--         size_t i = (size_t) jl_unbox_long(args[1]) - 1;
--         char *data;
--         if (jl_is_genericmemory(args[0])) {
--             jl_genericmemory_t *m = (jl_genericmemory_t*)args[0];
--             jl_value_t *typ = jl_apply_type((jl_value_t*)jl_genericmemoryref_type, jl_svec_data(((jl_datatype_t*)jl_typetagof(m))->parameters), 3);
--             JL_GC_PROMISE_ROOTED(typ); // it is a concrete type
--             if (i >= m->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--             if (layout->flags.arrayelem_isunion || layout->size == 0)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)i);
--             else if (layout->flags.arrayelem_isboxed)
--                 return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + sizeof(jl_value_t*)*i);
--             return (jl_value_t*)jl_new_memoryref(typ, m, (char*)m->ptr + layout->size*i);
--         }
--         JL_TYPECHK(memoryrefnew, genericmemoryref, args[0]);
--         jl_genericmemoryref_t *m = (jl_genericmemoryref_t*)args[0];
--         jl_genericmemory_t *mem = m->mem;
--         data = (char*)m->ptr_or_offset;
--         const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(mem))->layout;
--         if (layout->flags.arrayelem_isboxed) {
--             if (((data - (char*)mem->ptr) / sizeof(jl_value_t*)) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += sizeof(jl_value_t*) * i;
--         }
--         else if (layout->flags.arrayelem_isunion || layout->size == 0) {
--             if ((size_t)data + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += i;
--         }
--         else {
--             if (((data - (char*)mem->ptr) / layout->size) + i >= mem->length)
--                 jl_bounds_error((jl_value_t*)m, args[1]);
--             data += layout->size * i;
--         }
--         return (jl_value_t*)jl_new_memoryref((jl_value_t*)jl_typetagof(m), mem, data);
--     }
-- }
-- 
-- /Source
def memoryNativeAssertIndex {W L : Type} (result : MemoryIndexResult L) :
    MemoryNativeM W L (JInt .i64) :=
  match result with
  | .native value => pure value
  | .other value => memoryNativeThrow {
      exception := .typeError "memoryrefnew", expected := some "Int64", got := some value }

/-- Complete one-argument wrapper, retaining the existing memory's identity
and accepting empty memories. Source: `base/boot.jl:768`. -/
-- Source: base/boot.jl:768-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- memoryref(mem::GenericMemory) = memoryrefnew(mem)
-- /Source
def memoryRef {W L : Type} (memory : MemoryNativeObject L) :
    MemoryNativeM W L (MemoryNativeRef L) := memoryNativeFirst memory

/-- Complete memory-input indexed wrapper. Preserve every custom Integer
conversion outcome/effect, then run the fixed builtin at the source point.
Source: `base/boot.jl:769`. -/
-- Source: base/boot.jl:769-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- memoryref(mem::GenericMemory, i::Integer) = memoryrefnew(mem, Int(i), @_boundscheck)
-- /Source
def memoryRefAt {W L : Type} (dispatch : MemoryNativeDispatch W L)
    (memory : MemoryNativeObject L) (index : JuliaLean.base.expr.Value L)
    (boundscheck : Bool) : MemoryNativeM W L (MemoryNativeRef L) := do
  let converted ← dispatch.toInt index
  let native ← memoryNativeAssertIndex converted
  memoryNativeIndexMemory memory native boundscheck

/-- Complete reference-input indexed wrapper, preserving custom Int(i)
effects/errors/divergence before native assertion and current-length bounds.
Source: `base/boot.jl:770`. -/
-- Source: base/boot.jl:770-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- memoryref(ref::GenericMemoryRef, i::Integer) = memoryrefnew(ref, Int(i), @_boundscheck)
-- /Source
def memoryRefShift {W L : Type} (dispatch : MemoryNativeDispatch W L)
    (reference : MemoryNativeRef L) (index : JuliaLean.base.expr.Value L)
    (boundscheck : Bool) : MemoryNativeM W L (MemoryNativeRef L) := do
  let converted ← dispatch.toInt index
  let native ← memoryNativeAssertIndex converted
  memoryNativeIndexReference reference native boundscheck

/-- Select one-argument memoryref on the actual current memory type. The
known default calls the concrete builtin wrapper; a selected custom method
retains its unrestricted result. Source: `base/boot.jl:771,779`. -/
-- Source: base/boot.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- GenericMemoryRef(mem::GenericMemory) = memoryref(mem)
-- /Source
def memoryNativeSelectFirst {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (memory : MemoryNativeObject L) : MemoryNativeM W L (MemoryAliasResult L) :=
  fun world =>
    if dispatch.firstSelected world memory then dispatch.first memory world
    else (do let reference ← memoryRef memory
             pure (MemoryAliasResult.reference reference)) world

/-- Complete GenericMemoryRef(memory) alias, including more-specific methods
selected on unspecified element/kind/address-space parameters. No returned
reference assertion is added. Source: `base/boot.jl:771`. -/
-- Source: base/boot.jl:771-771 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- GenericMemoryRef(mem::GenericMemory) = memoryref(mem)
-- /Source
def genericMemoryRefCtor {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (memory : MemoryNativeObject L) : MemoryNativeM W L (MemoryAliasResult L) :=
  memoryNativeSelectFirst dispatch memory

/-- Complete indexed memory alias. Its call to memoryref may dispatch to a
more-specific custom Integer method; that method's arbitrary return value is
returned unchanged, without a native-reference assertion. Otherwise execute
the complete selected source memoryref body. Source: `base/boot.jl:772`. -/
-- Source: base/boot.jl:772-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- GenericMemoryRef(mem::GenericMemory, i::Integer) = memoryref(mem, i)
-- /Source
def genericMemoryRefAtCtor {W L : Type} (dispatch : MemoryNativeAliasDispatch W L)
    (memory : MemoryNativeObject L) (index : JuliaLean.base.expr.Value L)
    (boundscheck : Bool) : MemoryNativeM W L (MemoryAliasResult L) :=
  fun world =>
    if dispatch.customSelected world (.memory memory) index then
      dispatch.custom (.memory memory) index world
    else
      (do let reference ← memoryRefAt dispatch.native memory index boundscheck
          pure (MemoryAliasResult.reference reference)) world

/-- Complete indexed reference alias, with actual default/custom memoryref
selection on the unspecified Integer subtype. No result-type promise is imposed
on a selected custom method. Source: `base/boot.jl:773`. -/
-- Source: base/boot.jl:773-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- GenericMemoryRef(mem::GenericMemoryRef, i::Integer) = memoryref(mem, i)
-- /Source
def genericMemoryRefShiftCtor {W L : Type} (dispatch : MemoryNativeAliasDispatch W L)
    (reference : MemoryNativeRef L) (index : JuliaLean.base.expr.Value L)
    (boundscheck : Bool) : MemoryNativeM W L (MemoryAliasResult L) :=
  fun world =>
    if dispatch.customSelected world (.reference reference) index then
      dispatch.custom (.reference reference) index world
    else
      (do let result ← memoryRefShift dispatch.native reference index boundscheck
          pure (MemoryAliasResult.reference result)) world

/-- Complete new_as_memoryref: project the actual fixed mem type, call its
selected constructor, then invoke memoryref on that actual returned value.
The installed allocation branch retains every native type/size check and the
subsequent installed/custom memoryref choice. A custom constructor result has
no prescribed Julia type, so memoryref dispatch on it is genuinely open and
is called only after that custom method succeeds. Source: `base/boot.jl:779`. -/
-- Source: base/boot.jl:779-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- new_as_memoryref(self::Type{GenericMemoryRef{kind,T,addrspace}}, m::Int) where {T,kind,addrspace} = memoryref(fieldtype(self, :mem)(undef, m))
-- /Source
def newAsMemoryRefCtor {W L : Type} (dispatch : MemoryCreationDispatch W L)
    (type : MemoryNativeRefType L) (n : JInt .i64) :
    MemoryNativeM W L (MemoryAliasResult L) := do
  let result ← memoryNativeConstruct dispatch type.memoryType n
  match result with
  | .memory memory => memoryNativeSelectFirst dispatch memory
  | .customResult value => dispatch.afterCustomConstructor value

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1.GenericForwarding

open JuliaLean

/-!
Complete generic forwarding bodies at boot.jl:399,567,1045,1310.
Each generic callee dispatches on an argument type the source method does not
fix. Its actual call uses the installed CoreOps.call interface, retaining
arbitrary Julia results, errors, effects and divergence. A constructor may
return a value that is not an instance of the type it names: these source
bodies add no result-type assertions. The two throwing wrappers throw exactly
the returned value only after successful constructor return.

The source-selected inner constructor bodies remain separately modeled.
Nothing here supplies a callback for a fixed primitive, concrete native scalar
conversion, the method's own recursion, or a runtime type-validation operation.
Physical allocation/GC/resource exhaustion use the established abstraction.
-/

/-- The source kwcall argument tuple has two non-vararg operands: kwargs and
Union{}. The runtime call arity is UInt32, so len(a)+2 must fit that word.
The outgoing positional splat contains only a and fits without truncation.
Every argument retains its arbitrary Julia value and object identity.
Source: base/boot.jl:399; src/julia.h:2591,2596-2599.
-/
structure KeywordBottomArguments (L : Type) where
  values : List (JuliaLean.base.expr.Value L)
  arity : values.length + 2 ≤ (2^32 - 1 : Nat)

/-- The selected keyword wrapper ignores kwargs and forwards exactly the
original positional values to the Union{} constructor's actual dispatch.
A custom method on an unfixed argument may return any value; the keyword
wrapper does not impose the source fallback's ArgumentError behavior.
Source: base/boot.jl:399.
-/
-- Source: base/boot.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- kwcall(kwargs, ::Type{Union{}}, a...) = Union{}(a...)
-- /Source
def keywordBottom {W L : Type} (ops : CoreOps W L)
    (_kwargs : JuliaLean.base.expr.Value L) (arguments : KeywordBottomArguments L) :
    CoreM W L (JuliaLean.base.expr.Value L) :=
  ops.call (coreV ops "Union{}") arguments.values

/-- The selected two-argument MethodError body calls the generic three-argument
constructor with the original f/args and native typemax(UInt), preserving all
callee outcomes and mutations without asserting the returned value's type.
Source: base/boot.jl:567; typemax_UInt is the installed native constant at558.
-/
-- Source: base/boot.jl:567-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- MethodError(@nospecialize(f), @nospecialize(args)) = MethodError(f, args, typemax_UInt)
-- /Source
def methodErrorDefault {W L : Type} (ops : CoreOps W L)
    (f args : JuliaLean.base.expr.Value L) : CoreM W L (JuliaLean.base.expr.Value L) :=
  ops.call (coreV ops "MethodError") [f, args, intV ops JuliaLean.base.boot.typemax_UInt]

/-- Call the generic InexactError constructor with the source-typed Symbol
and original arbitrary target/value, then throw exactly its successful result.
A constructor exception or divergence propagates before that outer throw.
There is no TypeError, instance assertion, or fabricated standard exception.
Source: base/boot.jl:1045.
-/
-- Source: base/boot.jl:1045-1045 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- throw_inexacterror(func::Symbol, to, val) = throw(InexactError(func, to, val))
-- /Source
def throwInexact {W L A : Type} (ops : CoreOps W L)
    (func target value : JuliaLean.base.expr.Value L) : CoreM W L A := do
  let exception ← ops.call (coreV ops "InexactError") [func, target, value]
  throw exception

/-- The selected typename fallback first dispatches TypeNameError on the
original arbitrary value, then throws exactly the returned value. More-specific
exception constructors may mutate, throw, diverge, or return any Julia value.
The separate selected DataType typename body remains a direct metadata read.
Source: base/boot.jl:1310.
-/
-- Source: base/boot.jl:1310-1310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typename(a) = throw(TypeNameError(a))
-- /Source
def typeNameFallback {W L A : Type} (ops : CoreOps W L)
    (value : JuliaLean.base.expr.Value L) : CoreM W L A := do
  let exception ← ops.call (coreV ops "TypeNameError") [value]
  throw exception

end JuliaLean.base.boot.Models2Group1.GenericForwarding


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-- Actual immutable UnionAll fields relevant to the selected method at
base/boot.jl:1318. Its Any-typed body is guaranteed initialized (ninitialized=2)
and retains the full existing runtime metadata/identity, with native storage
bounds. The binder and original UnionAll identity are uninspected actual data.
This is a field view, not a field-access or type-reflection callback.
Source: base/boot.jl:1318; src/jltypes.c:3728-3735.
-/
structure UnionAllTypeNameInput (V : Type) where
  identity : Nat
  binder : V
  body : Reflection.JuliaValue V

/-- The generic call following one actual UnionAll body read. When that body
is itself a UnionAll and dispatch selects this same source method, its own
body executes by concrete structural recursion. All other selected methods
receive the original body through CoreOps.call with arbitrary return, thrown
value, effects and divergence. The source adds no TypeName result assertion.
The source selector is actual current-world dispatch metadata; encode is a
pure identity-preserving representation map, not a runtime operation.
Source: base/boot.jl:1318. Relevant body fields are immutable and initialized;
the finite graph expansion preserves all original object identities.
-/
-- Source: base/boot.jl:1318-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typename(union::UnionAll) = typename(union.body)
-- /Source
def typeNameUnionAllDispatchBody {W V L : Type} (ops : CoreOps W L)
    (sourceSelected : W → Reflection.Value V → Bool)
    (encode : Reflection.Value V → JuliaLean.base.expr.Value L)
    (value : Reflection.Value V) : CoreM W L (JuliaLean.base.expr.Value L) :=
  match value with
  | .unionAll _ _ _ _ body _ =>
      fun world =>
        if sourceSelected world value then
          typeNameUnionAllDispatchBody ops sourceSelected encode body world
        else
          ops.call (coreV ops "typename") [encode value] world
  | _ => ops.call (coreV ops "typename") [encode value]
termination_by value

/-- Complete selected UnionAll typename method: read its actual immutable
body, then perform generic dispatch with explicit recursion for selection of
this same source method. Non-own selected targets remain unrestricted because
this method does not fix the body's type. This does not replace the separate
Union method's equality algorithm or claim the whole typename generic function.
Source: base/boot.jl:1318.
-/
-- Source: base/boot.jl:1318-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typename(union::UnionAll) = typename(union.body)
-- /Source
def typeNameUnionAllDispatch {W V L : Type} (ops : CoreOps W L)
    (sourceSelected : W → Reflection.Value V → Bool)
    (encode : Reflection.Value V → JuliaLean.base.expr.Value L)
    (value : UnionAllTypeNameInput V) : CoreM W L (JuliaLean.base.expr.Value L) :=
  let body := value.body.object
  typeNameUnionAllDispatchBody ops sourceSelected encode body

end JuliaLean.base.boot.Models2Group1


namespace JuliaLean.base.boot.Models2Group1.PrintMany

open JuliaLean

/-!
Complete selected print(io::IO,x,a...) body at boot.jl:1000, including explicit
invoke of that source body with an empty tail. IO's concrete subtype and every
payload type remain unfixed, so first-call generic dispatch is unrestricted.
The installed fixed-arity print(io::IO,x) method at999 dominates source1000
whenever there is only one payload. Thus neither the first two-argument call
nor a singleton tail call can select source1000 itself. An empty tail invokes
the actual generic print(io), with no fabricated MethodError or return value.

For at least two remaining payloads, the tail call's current method selection
can be source1000 or another method. A source selection executes the same body
by structural recursion on the strictly smaller tail. Other selections use
the existing CoreOps.call with exact arguments. Selection is observed after
the first call's effects. Custom callees may return any value, throw, mutate,
or diverge; no correctness/termination law or output-type assertion is imposed.
This models the installed method family; replacing/removing fixed-arity999 is
not assumed as an additional source configuration.
-/

/-- Actual variadic call operands after io and x. The runtime generic arity
is UInt32, including those two fixed arguments. Every outgoing call fits the
same bound; original values and aliases are retained without copying objects.
Source: base/boot.jl:1000; src/julia.h:2591,2596-2599.
-/
structure Arguments (L : Type) where
  first : JuliaLean.base.expr.Value L
  tail : List (JuliaLean.base.expr.Value L)
  arity : tail.length + 2 ≤ (2^32 - 1 : Nat)

/-- Actual method selection for a tail with at least two payloads. True means
the source1000 method is selected; false means an independently selected other
method. It sees the current world and the exact original io/tail operands.
This is dispatch metadata, not a correctness law about a supplied operation.
Source: base/boot.jl:998-1000.
-/
-- Source: base/boot.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- print(io::IO, @nospecialize(x), @nospecialize a...) = (print(io, x); print(io, a...))
-- /Source
abbrev SourceSelected (W L : Type) :=
  W → JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) → Bool

/-- Execute the source method's own body, retaining actual generic calls and
its concrete recursive source-selection branch. The list traversal uses no
Julia integer arithmetic; native constructibility is carried by public Arguments.
The recursion's first operand is the next original payload, with the identical
io handle. Source: base/boot.jl:1000; fixed-arity dispatch context998-999.
-/
-- Source: base/boot.jl:998-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- print(io::IO, x::String) = (write(io, x); nothing)
-- print(io::IO, @nospecialize x) = show(io, x)
-- print(io::IO, @nospecialize(x), @nospecialize a...) = (print(io, x); print(io, a...))
-- /Source
def sourceBody {W L : Type} (ops : CoreOps W L) (sourceSelected : SourceSelected W L)
    (io first : JuliaLean.base.expr.Value L) (tail : List (JuliaLean.base.expr.Value L)) :
    CoreM W L (JuliaLean.base.expr.Value L) := do
  let _ ← ops.call (coreV ops "print") [io, first]
  match tail with
  | [] => ops.call (coreV ops "print") [io]
  | [last] => ops.call (coreV ops "print") [io, last]
  | next :: second :: rest =>
      fun world =>
        if sourceSelected world io (next :: second :: rest) then
          sourceBody ops sourceSelected io next (second :: rest) world
        else
          ops.call (coreV ops "print") (io :: next :: second :: rest) world
termination_by tail

/-- Full source method for every constructible variadic call, including an
empty tail when its body is explicitly selected. Initial and recursive calls
preserve errors/effects/divergence and return the actual final generic result.
Source: base/boot.jl:1000.
-/
-- Source: base/boot.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- print(io::IO, @nospecialize(x), @nospecialize a...) = (print(io, x); print(io, a...))
-- /Source
def printMany {W L : Type} (ops : CoreOps W L) (sourceSelected : SourceSelected W L)
    (io : JuliaLean.base.expr.Value L) (arguments : Arguments L) :
    CoreM W L (JuliaLean.base.expr.Value L) :=
  sourceBody ops sourceSelected io arguments.first arguments.tail

end JuliaLean.base.boot.Models2Group1.PrintMany


namespace JuliaLean.base.boot.Models2Group1

open JuliaLean

/-!
Concrete Array undef kernels, base/boot.jl:821-833. The stored field types are
actual Array structure: ref is GenericMemoryRef{:not_atomic,T,Core.CPU}, and
size is the native Int tuple. Allocation reuses the complete GenericMemory
C closure. Genuine methods selected on unspecified T remain explicit, with
arbitrary values/effects/errors/divergence; no concrete builtin is a callback.

Each Array has a fresh logical mutable identity. Its reference field preserves
the exact original reference value, including shared backing memory or an
opaque existing reference whose internal fields are not read. Existing Array
fields may be undefined. Logical identities abstract physical GC placement and
resource exhaustion; all explicit native size and type checks are retained.

The tuple carrier has the necessary actual tuple layout bound 8*N<=2^32-1.
Every native Int field takes eight bytes; datatype.c:645-648,825-830 rejects
field offsets/sizes that exceed UInt32. A ready concrete Array additionally
has the stricter containing-field bound, but free-T/layout-null existing
targets can skip that layout check and remain in this complete domain. The
tuple bound is representation metadata, not a new dimension check.
Consequently source tuple splats fit the UInt32 jl_apply argument boundary.
The actual native argument-count arithmetic is still performed below.
-/

/-- Full opaque payload carrier, refined only by the concrete reference type
needed by raw-new's field assertion. `other` excludes GenericMemoryRef values;
`reference` retains an arbitrary existing reference's original payload and
interned type identity, including references whose fields are not inspected.
The identity is the one-to-one GenericMemory parameter/type identity, not a
machine integer or arbitrary isa callback. Source: boot.jl:77-80,821-833. -/
inductive ArrayNativeLeaf (L : Type) where
  | other (value : L)
  | reference (memoryTypeIdentity : Nat) (value : L)

/-- Actual fixed Array element/type metadata. Kind and address-space are
forced by the installed Array field declaration; invalid or free element
parameters remain in the complete memory descriptor. Concrete/layout bits
are actual target metadata used by raw new, not laws about user operations.
Source: src/jltypes.c:4026-4034; src/datatype.c:1707-1717. -/
structure ArrayNativeElement (L : Type) where
  memoryType : MemoryNativeType (ArrayNativeLeaf L)
  kindFixed : ∃ name, memoryType.kind = .symbol name ∧ name.bytes = symbolName "not_atomic"
  addressFixed : memoryAddressIsCPU memoryType.address = true
  concrete : Bool
  hasLayout : Bool

/-- An actual Int64 dimension tuple. Its necessary UInt32 field-offset bound
comes from the tuple runtime layout checker, not an allocation budget. Existing
free-T/layout-null Array targets need not satisfy the stricter containing-field
bound, so that stronger condition is deliberately absent.
Source: src/datatype.c:645-648,825-830; src/jltypes.c:3801-3804. -/
structure ArrayNativeDimensions where
  values : List (JInt .i64)
  fieldSizeBound : values.length * 8 ≤ (IntTy.max .u32).toNat

structure ArrayNativeType (L : Type) where
  element : ArrayNativeElement L
  rank : JInt .i64

structure ArrayNativeObject (L : Type) where
  identity : Nat
  type : ArrayNativeType L

/-- Mutable Array fields preserve definedness, exact reference value, type,
and size tuple. Newly created arrays initialize both fields.
Source: boot.jl:821-833; src/jltypes.c:4026-4034. -/
structure ArrayNativeCell (L : Type) where
  type : ArrayNativeType L
  reference : Option (MemoryAliasResult (ArrayNativeLeaf L))
  dimensions : Option ArrayNativeDimensions

structure ArrayNativeHeap (L : Type) where
  cells : List (ArrayNativeCell L)

abbrev ArrayNativeWorld (W L : Type) := MemoryNativeWorld (ArrayNativeHeap L × W)

/-- Refinements of existing Julia exceptions. Memory errors retain their full
original value; dimension errors retain the installed JlError; raw new's
TypeError(:new,"",DataType,self) or reference-field TypeError retains the
actual expected type and complete original offending value. -/
inductive ArrayNativeException (L : Type) where
  | memory (value : JuliaLean.base.expr.Value (MemoryNativeException (ArrayNativeLeaf L)))
  | dimensions (error : JlError)
  | newSelf (target : ArrayNativeType L)
  | newReference (expected : MemoryNativeType (ArrayNativeLeaf L))
      (got : MemoryAliasResult (ArrayNativeLeaf L))

abbrev ArrayNativeM (W L A : Type) := CoreM (ArrayNativeWorld W L) (ArrayNativeException L) A

/-- Actual new_as_memoryref selection on the unfixed element parameter, plus
the complete constructor/memoryref operations used by its default body.
All selected user results have full reference-or-other value classification;
opaque references use ArrayNativeLeaf.reference with their original payload.
Source: boot.jl:821-833,779. -/
structure ArrayNativeDispatch (W L : Type) where
  memory : MemoryCreationDispatch (ArrayNativeHeap L × W) (ArrayNativeLeaf L)
  newAsSelected : ArrayNativeWorld W L → MemoryNativeRefType (ArrayNativeLeaf L) → JInt .i64 → Bool
  newAs : MemoryNativeRefType (ArrayNativeLeaf L) → JInt .i64 →
    ArrayNativeM W L (MemoryAliasResult (ArrayNativeLeaf L))

/-- Lift the installed memory computation without altering any success,
error payload, heap/world effect or divergence. Source: boot.jl:821-833. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def arrayNativeLiftMemory {W L A : Type}
    (action : MemoryNativeM (ArrayNativeHeap L × W) (ArrayNativeLeaf L) A) :
    ArrayNativeM W L A := fun world =>
  match action world with
  | none => none
  | some (.error (error, after)) => some (.error (.leaf (.memory error), after))
  | some (.ok result) => some (.ok result)

/-- Closed checked_dims dispatcher for native dimensions. The installed
ReinterpretArrays model has the exact scalar bypass and checked native
multiplication/overflow/negative handling. No error is dropped or defaulted.
Source: boot.jl:812-818; called by boot.jl:825-833. -/
-- Source: base/boot.jl:812-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checked_dims() = 1
-- checked_dims(m::Int) = m # defer this check to Memory constructor instead
-- function checked_dims(d::Int...)
--     b = _checked_mul_dims(d...)
--     getfield(b, 2) && throw(ArgumentError("invalid Array dimensions"))
--     return getfield(b, 1)
-- end
-- /Source
def arrayNativeCheckedDims {W L : Type} (values : List (JInt .i64)) :
    ArrayNativeM W L (JInt .i64) :=
  match JuliaLean.ReinterpretArrays.checkedDims values with
  | .error error => throw (.leaf (.dimensions error))
  | .ok value => pure value

/-- The source UInt32 apply boundary for a tuple-only native-dimension splat.
All input fields are already present native Int values. The tuple-layout bound
ensures no truncation, but the source size_t increment, UInt32 cast and native
subtraction remain explicit. Source: builtins.c:1047; julia.h:2596-2599;
boot.jl:831-833. -/
-- Source: src/julia.h:2596-2599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- STATIC_INLINE jl_value_t *jl_apply(jl_value_t **args, uint32_t nargs) JL_CANSAFEPOINT
-- {
--     return jl_apply_generic(args[0], &args[1], nargs - 1);
-- }
-- /Source
def arrayNativeSplatDimensions (dims : ArrayNativeDimensions) : List (JInt .i64) :=
  let total : JInt .u64 := JInt.wrap .u64 (dims.values.length : Int) + JInt.wrap .u64 1
  let count : JInt .u32 := JInt.wrap .u32 total.val - JInt.wrap .u32 1
  dims.values.take count.val.toNat

/-- Concrete target/reference type observation used by raw new. Known tracked
references expose their actual memory type; opaque references expose actual
stored type identity while preserving every unread internal field/payload.
Source: datatype.c:1716-1720. -/
-- Source: src/datatype.c:1707-1742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_value_t *jl_new_structv(jl_datatype_t *type, jl_value_t **args, uint32_t na)
-- {
--     jl_task_t *ct = jl_current_task;
--     if (!jl_is_datatype(type) || !type->isconcretetype || type->layout == NULL || jl_is_layout_opaque(type->layout)) {
--         jl_type_error("new", (jl_value_t*)jl_datatype_type, (jl_value_t*)type);
--     }
--     size_t nf = jl_datatype_nfields(type);
--     if (nf - type->name->n_uninitialized > na || na > nf)
--         jl_error("invalid struct allocation");
--     for (size_t i = 0; i < na; i++) {
--         jl_value_t *ft = jl_field_type_concrete(type, i);
--         if (!jl_isa(args[i], ft))
--             jl_type_error("new", ft, args[i]);
--     }
--     if (type->instance != NULL)
--         return type->instance;
--     jl_value_t *jv = jl_gc_alloc(ct->ptls, jl_datatype_size(type), type);
--     if (type->smalltag) // TODO: do we need this?
--         jl_set_typetagof(jv, type->smalltag, 0);
--     if (jl_datatype_nfields(type) > 0) {
--         if (jl_field_offset(type, 0) != 0) {
--             memset(jl_data_ptr(jv), 0, jl_field_offset(type, 0));
--         }
--         JL_GC_PUSH1(&jv);
--         for (size_t i = 0; i < na; i++) {
--             set_nth_field(type, jv, i, args[i], 0);
--         }
--         if (na < jl_datatype_nfields(type)) {
--             char *data = (char*)jl_data_ptr(jv);
--             size_t offs = jl_field_offset(type, na);
--             memset(data + offs, 0, jl_datatype_size(type) - offs);
--         }
--         JL_GC_POP();
--     }
--     return jv;
-- }
-- /Source
def arrayNativeReferenceType {L : Type} : MemoryAliasResult (ArrayNativeLeaf L) → Option Nat
  | .reference reference => some reference.memory.type.identity
  | .other (.leaf (.reference identity _)) => some identity
  | .other _ => none

/-- Raw Expr(:new) field checks occur after the field expressions have run.
The target concrete/layout check precedes the reference-field assertion. The
already-native size tuple has precisely the target rank and needs no dynamic
conversion. Success appends one fresh mutable Array, preserving memory and
all earlier callback effects. Source: boot.jl:821-833; datatype.c:1707-1742. -/
-- Source: src/datatype.c:1707-1742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT jl_value_t *jl_new_structv(jl_datatype_t *type, jl_value_t **args, uint32_t na)
-- {
--     jl_task_t *ct = jl_current_task;
--     if (!jl_is_datatype(type) || !type->isconcretetype || type->layout == NULL || jl_is_layout_opaque(type->layout)) {
--         jl_type_error("new", (jl_value_t*)jl_datatype_type, (jl_value_t*)type);
--     }
--     size_t nf = jl_datatype_nfields(type);
--     if (nf - type->name->n_uninitialized > na || na > nf)
--         jl_error("invalid struct allocation");
--     for (size_t i = 0; i < na; i++) {
--         jl_value_t *ft = jl_field_type_concrete(type, i);
--         if (!jl_isa(args[i], ft))
--             jl_type_error("new", ft, args[i]);
--     }
--     if (type->instance != NULL)
--         return type->instance;
--     jl_value_t *jv = jl_gc_alloc(ct->ptls, jl_datatype_size(type), type);
--     if (type->smalltag) // TODO: do we need this?
--         jl_set_typetagof(jv, type->smalltag, 0);
--     if (jl_datatype_nfields(type) > 0) {
--         if (jl_field_offset(type, 0) != 0) {
--             memset(jl_data_ptr(jv), 0, jl_field_offset(type, 0));
--         }
--         JL_GC_PUSH1(&jv);
--         for (size_t i = 0; i < na; i++) {
--             set_nth_field(type, jv, i, args[i], 0);
--         }
--         if (na < jl_datatype_nfields(type)) {
--             char *data = (char*)jl_data_ptr(jv);
--             size_t offs = jl_field_offset(type, na);
--             memset(data + offs, 0, jl_datatype_size(type) - offs);
--         }
--         JL_GC_POP();
--     }
--     return jv;
-- }
-- /Source
def arrayNativeNew {W L : Type} (element : ArrayNativeElement L)
    (dims : ArrayNativeDimensions) (reference : MemoryAliasResult (ArrayNativeLeaf L)) :
    ArrayNativeM W L (ArrayNativeObject L) := fun world =>
  let target : ArrayNativeType L := ⟨element, JInt.wrap .i64 (dims.values.length : Int)⟩
  if !element.concrete || !element.hasLayout then
    some (.error (.leaf (.newSelf target), world))
  else if arrayNativeReferenceType reference ≠ some element.memoryType.identity then
    some (.error (.leaf (.newReference element.memoryType reference), world))
  else
    let identity := world.external.1.cells.length
    let cell : ArrayNativeCell L := ⟨target, some reference, some dims⟩
    let heap : ArrayNativeHeap L := ⟨world.external.1.cells ++ [cell]⟩
    some (.ok (⟨identity, target⟩, { world with external := (heap, world.external.2) }))

/-- The actual new_as_memoryref call: only a genuinely selected user method is
open; its default executes the complete installed body and concrete memory
allocation/reference helpers. Source: boot.jl:825-833,779. -/
-- Source: base/boot.jl:825-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- /Source
def arrayNativeNewAs {W L : Type} (dispatch : ArrayNativeDispatch W L)
    (type : MemoryNativeRefType (ArrayNativeLeaf L)) (n : JInt .i64) :
    ArrayNativeM W L (MemoryAliasResult (ArrayNativeLeaf L)) := fun world =>
  if dispatch.newAsSelected world type n then dispatch.newAs type n world
  else arrayNativeLiftMemory (newAsMemoryRefCtor dispatch.memory type n) world

/-- Complete one-dimensional selected undef body, including constructor and
memoryref dispatch on unfixed T, arbitrary returned values, and raw-new checks
only after both calls succeed. Source: base/boot.jl:821-824. -/
-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
def arrayNative1Ctor {W L : Type} (dispatch : ArrayNativeDispatch W L)
    (element : ArrayNativeElement L) (m : JInt .i64) : ArrayNativeM W L (ArrayNativeObject L) := do
  let memory ← arrayNativeLiftMemory (memoryNativeConstruct dispatch.memory element.memoryType m)
  let reference ← arrayNativeLiftMemory (match memory with
    | .memory value => memoryNativeSelectFirst dispatch.memory value
    | .customResult value => dispatch.memory.afterCustomConstructor value)
  arrayNativeNew element ⟨[m], by simp only [List.length_cons, List.length_nil]; decide⟩ reference

/-- Complete rank-two selected body. Dimension errors precede allocation or
selected new_as_memoryref effects; raw-new assertions follow the actual result.
Source: base/boot.jl:825-827. -/
-- Source: base/boot.jl:825-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- /Source
def arrayNative2Ctor {W L : Type} (dispatch : ArrayNativeDispatch W L)
    (element : ArrayNativeElement L) (m n : JInt .i64) : ArrayNativeM W L (ArrayNativeObject L) := do
  let count ← arrayNativeCheckedDims [m, n]
  let reference ← arrayNativeNewAs dispatch ⟨element.memoryType⟩ count
  arrayNativeNew element ⟨[m, n], by simp only [List.length_cons, List.length_nil]; decide⟩ reference

/-- Complete rank-three selected body, preserving original dimension order
and exact native count/error behavior. Source: base/boot.jl:828-830. -/
-- Source: base/boot.jl:828-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,3}})(::UndefInitializer, m::Int, n::Int, o::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n, o))), :((m, n, o))))
-- end))
-- /Source
def arrayNative3Ctor {W L : Type} (dispatch : ArrayNativeDispatch W L)
    (element : ArrayNativeElement L) (m n o : JInt .i64) : ArrayNativeM W L (ArrayNativeObject L) := do
  let count ← arrayNativeCheckedDims [m, n, o]
  let reference ← arrayNativeNewAs dispatch ⟨element.memoryType⟩ count
  arrayNativeNew element ⟨[m, n, o], by simp only [List.length_cons, List.length_nil]; decide⟩ reference

/-- Complete explicitly selected vararg body for every existing Array rank.
The source checked_dims dispatcher retains the zero/scalar specializations;
the original tuple is stored, with native apply-arity handling at its splat.
Source: base/boot.jl:831-833. -/
-- Source: base/boot.jl:831-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(d...))), :d))
-- end))
-- /Source
def arrayNativeVarargCtor {W L : Type} (dispatch : ArrayNativeDispatch W L)
    (element : ArrayNativeElement L) (dims : ArrayNativeDimensions) :
    ArrayNativeM W L (ArrayNativeObject L) := do
  let count ← arrayNativeCheckedDims (arrayNativeSplatDimensions dims)
  let reference ← arrayNativeNewAs dispatch ⟨element.memoryType⟩ count
  arrayNativeNew element dims reference


/-- Source constructor aliases return the installed Array or any value chosen
by a user specialization. The origin tag imposes no Julia return-type check.
Source: boot.jl:835-847. -/
inductive ArrayNativeAliasResult (L : Type) where
  | array (value : ArrayNativeObject L)
  | customResult (value : JuliaLean.base.expr.Value (ArrayNativeLeaf L))

/-- Genuine Array constructor specialization on unspecified T. Fixed native
undef/dimension operands do not prohibit a user-specific callable Array type.
The default branch remains the complete known constructor dispatcher.
Source: boot.jl:835-847. -/
structure ArrayWrapperDispatch (W L : Type) where
  kernel : ArrayNativeDispatch W L
  selected : ArrayNativeWorld W L → ArrayNativeType L → ArrayNativeDimensions → Bool
  custom : ArrayNativeType L → ArrayNativeDimensions →
    ArrayNativeM W L (JuliaLean.base.expr.Value (ArrayNativeLeaf L))

/-- Installed Array constructor dispatch chooses rank1/2/3 specializations
before the generic vararg method. The original native tuple is retained in
the generic case. Source: boot.jl:821-833,835-838. -/
-- Source: base/boot.jl:831-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(d...))), :d))
-- end))
-- /Source
def arrayNativeDefaultConstructor {W L : Type} (dispatch : ArrayNativeDispatch W L)
    (element : ArrayNativeElement L) (dims : ArrayNativeDimensions) :
    ArrayNativeM W L (ArrayNativeObject L) :=
  match dims.values with
  | [m] => arrayNative1Ctor dispatch element m
  | [m,n] => arrayNative2Ctor dispatch element m n
  | [m,n,o] => arrayNative3Ctor dispatch element m n o
  | _ => arrayNativeVarargCtor dispatch element dims

/-- Invoke the original Array{T,N} target with undef followed by the exact
native dimension operands. The installed branch remains concrete; a selected
custom result is returned unchanged and may have any Julia type.
Source: boot.jl:835-847. -/
-- Source: base/boot.jl:838-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{Array{T,N}})(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = self(undef, d...)
-- /Source
def arrayNativeInvoke {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (dims : ArrayNativeDimensions) :
    ArrayNativeM W L (ArrayNativeAliasResult L) := fun world =>
  let target : ArrayNativeType L := ⟨element, JInt.wrap .i64 (dims.values.length : Int)⟩
  if dispatch.selected world target dims then
    (do let value ← dispatch.custom target dims
        pure (ArrayNativeAliasResult.customResult value)) world
  else
    (do let value ← arrayNativeDefaultConstructor dispatch.kernel element dims
        pure (ArrayNativeAliasResult.array value)) world

/-- Native apply boundary for self(undef,d...): the function and fixed undef
precede the tuple fields. UInt32 subtraction removes both, and the actual dimension-tuple
layout bound guarantees that the prefix still contains all original fields.
Source: boot.jl:838; builtins.c:1047; julia.h:2596-2599. -/
-- Source: src/julia.h:2596-2599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- STATIC_INLINE jl_value_t *jl_apply(jl_value_t **args, uint32_t nargs) JL_CANSAFEPOINT
-- {
--     return jl_apply_generic(args[0], &args[1], nargs - 1);
-- }
-- /Source
def arrayNativeSelfSplatDimensions (dims : ArrayNativeDimensions) : ArrayNativeDimensions :=
  let total : JInt .u64 := JInt.wrap .u64 (dims.values.length : Int) + JInt.wrap .u64 2
  let argc : JInt .u32 := JInt.wrap .u32 total.val - JInt.wrap .u32 1
  let count : JInt .u32 := argc - JInt.wrap .u32 1
  ⟨dims.values.take count.val.toNat, by
    exact Nat.le_trans (Nat.mul_le_mul_right 8 (List.length_take_le' _ _)) dims.fieldSizeBound⟩

/-- Project the sole actual tuple field before the selected constructor call.
Source: base/boot.jl:835. -/
-- Source: base/boot.jl:835-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{Array{T,1}})(::UndefInitializer, d::NTuple{1, Int}) where {T} = self(undef, getfield(d, 1))
-- /Source
def arrayNativeTuple1Ctor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (dimension : JInt .i64) :
    ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element ⟨[dimension], by simp only [List.length_cons,List.length_nil]; decide⟩

/-- Project tuple fields in source order and preserve constructor dispatch.
Source: base/boot.jl:836. -/
-- Source: base/boot.jl:836-836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{Array{T,2}})(::UndefInitializer, d::NTuple{2, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2))
-- /Source
def arrayNativeTuple2Ctor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (dims : JInt .i64 × JInt .i64) :
    ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element ⟨[dims.1,dims.2], by simp only [List.length_cons,List.length_nil]; decide⟩

/-- Retain all three native tuple fields and the selected constructor result.
Source: base/boot.jl:837. -/
-- Source: base/boot.jl:837-837 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{Array{T,3}})(::UndefInitializer, d::NTuple{3, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2), getfield(d, 3))
-- /Source
def arrayNativeTuple3Ctor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (dims : JInt .i64 × JInt .i64 × JInt .i64) :
    ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element ⟨[dims.1,dims.2.1,dims.2.2], by simp only [List.length_cons,List.length_nil]; decide⟩

/-- Complete generic tuple alias for an existing Array{T,N}; native apply
arithmetic preserves the original target/rank and tuple by its layout bound.
Source: base/boot.jl:838. -/
-- Source: base/boot.jl:838-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{Array{T,N}})(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = self(undef, d...)
-- /Source
def arrayNativeTupleCtor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (dims : ArrayNativeDimensions) :
    ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element (arrayNativeSelfSplatDimensions dims)

/-- The fixed native rank1 application names valid Array family structure;
T and its actual field-type metadata are preserved. Generic constructor
dispatch on that target remains explicit. Source: base/boot.jl:840. -/
-- Source: base/boot.jl:840-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Array{T}(::UndefInitializer, m::Int) where {T} = Array{T, 1}(undef, m)
-- /Source
def arrayNativeInferred1Ctor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (m : JInt .i64) :
    ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element ⟨[m], by simp only [List.length_cons,List.length_nil]; decide⟩

/-- Fixed native rank2 type structure and original dimension ordering.
Source: base/boot.jl:841. -/
-- Source: base/boot.jl:841-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Array{T}(::UndefInitializer, m::Int, n::Int) where {T} = Array{T, 2}(undef, m, n)
-- /Source
def arrayNativeInferred2Ctor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (m n : JInt .i64) :
    ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element ⟨[m,n], by simp only [List.length_cons,List.length_nil]; decide⟩

/-- Fixed native rank3 type structure and original dimension ordering.
Source: base/boot.jl:842. -/
-- Source: base/boot.jl:842-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Array{T}(::UndefInitializer, m::Int, n::Int, o::Int) where {T} = Array{T, 3}(undef, m, n, o)
-- /Source
def arrayNativeInferred3Ctor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) (m n o : JInt .i64) :
    ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element ⟨[m,n,o], by simp only [List.length_cons,List.length_nil]; decide⟩

/-- The empty-tuple guard constructs the fixed rank0 target and calls it with
undef alone. Its installed constructor requests one backing element, while
selected custom methods retain arbitrary outcomes. Source: base/boot.jl:844. -/
-- Source: base/boot.jl:844-844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Array{T}(::UndefInitializer, ::Tuple{}) where {T} = Array{T, 0}(undef)
-- /Source
def arrayNativeInferred0Ctor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) : ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element ⟨[], by simp only [List.length_nil]; decide⟩

/-- The empty-vector alias forwards native zero to the original rank1 target.
Even when the default memory is a cached singleton, a successful installed
Array constructor allocates a distinct mutable Array. Source: base/boot.jl:847. -/
-- Source: base/boot.jl:847-847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{Array{T, 1}})() where {T} = self(undef, 0)
-- /Source
def arrayNativeEmptyVectorCtor {W L : Type} (dispatch : ArrayWrapperDispatch W L)
    (element : ArrayNativeElement L) : ArrayNativeM W L (ArrayNativeAliasResult L) :=
  arrayNativeInvoke dispatch element ⟨[JInt.wrap .i64 0], by simp only [List.length_cons,List.length_nil]; decide⟩

end JuliaLean.base.boot.Models2Group1

namespace JuliaLean.ArrayOps

open JuliaLean

/-- `memoryref(ref, k)` with its bounds check (`base/boot.jl:770`): `Int(k)`, then
`1 ≤ k ≤ length` of the backing memory. The memory is modelled as exactly as long
as the vector; the only calls that differ are those with `k ≥ 2^62`, which fail
in Julia as well. -/
def memoryrefCheck {t : IntTy} (len : Nat) (k : JInt t) : Jl Unit := do
  let k ← toInt k
  if 1 ≤ k.val ∧ k.val ≤ len then pure () else throw .boundsError

end JuliaLean.ArrayOps
