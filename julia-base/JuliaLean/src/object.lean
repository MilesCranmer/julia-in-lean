import Std
import JuliaLean.src.julia_h

/-!
Object model for Julia values (`src/julia.h`, `jl_value_t`).

Every runtime value in the pilot is an `Obj`:
* `Obj.type t`: a type object (`DataType`, `Union`, `UnionAll`, `Union{}`, ...).
* `Obj.bits ty v`: a primitive (`isbits` primitive-type) value such as `Int64`, `UInt64`, `Bool`,
  `Char`, or `Float64` (stored as its raw integer/bit representation `v`).
* `Obj.fn name`: a singleton function object identified by its qualified name (e.g. `"Base.size"`).
* `Obj.imm ty fields`: an immutable struct or tuple (`Core.Tuple`) with its concrete type and
  field values.
* `Obj.ref addr`: a reference to a mutable object (`Array`, `GenericMemory`, mutable struct)
  stored in a `Heap`.
-/

namespace JuliaLean

open JuliaLean.C

inductive Obj where
  /-- Type object (`DataType`, `Union`, `UnionAll`, `Union{}`, ...). -/
  | type (t : Val)
  /-- Primitive value (`Int64`, `UInt8`, `Bool`, `Char`, `Float64` raw bits, ...). -/
  | bits (ty : Val) (v : Int)
  /-- Singleton function object, identified by its qualified name. -/
  | fn (name : String)
  /-- Immutable struct or tuple (`Core.Tuple`) with its concrete type and field values. -/
  | imm (ty : Val) (fields : List Obj)
  /-- Reference to a mutable object on the `Heap` (`Array`, `GenericMemory`, mutable struct). -/
  | ref (addr : Nat)
  deriving Repr, Inhabited

mutual
def Obj.beq : Obj → Obj → Bool
  | .type a, .type b => a == b
  | .bits ta va, .bits tb vb => ta == tb && va == vb
  | .fn a, .fn b => a == b
  | .imm ta fa, .imm tb fb => ta == tb && Obj.beqList fa fb
  | .ref a, .ref b => a == b
  | _, _ => false

def Obj.beqList : List Obj → List Obj → Bool
  | [], [] => true
  | a :: as, b :: bs => Obj.beq a b && Obj.beqList as bs
  | _, _ => false
end

instance : BEq Obj := ⟨Obj.beq⟩

/-- A mutable cell on the `Heap`.
* `mut ty fields`: a mutable struct (including `Array{T, N}`, whose fields are `[ref, size]`).
* `mem ty elems`: a `GenericMemory{kind, T, AS}` object backing an `Array`, storing its elements. -/
inductive HeapCell where
  | mut (ty : Val) (fields : Array Obj)
  | mem (ty : Val) (elems : Array Obj)
  deriving Repr, Inhabited

/-- Heap of mutable objects plus the recorded `Core.Typeof(fn)` map for function singletons. -/
structure Heap where
  cells : Array HeapCell := #[]
  fnTypes : Std.HashMap String Val := {}
  deriving Inhabited

/-- Well-known `Val` types used by `Base` and `Core` primitives. -/
def boolType : Val := .datatype "Core.Bool" []
def int8Type : Val := .datatype "Core.Int8" []
def uint8Type : Val := .datatype "Core.UInt8" []
def int16Type : Val := .datatype "Core.Int16" []
def uint16Type : Val := .datatype "Core.UInt16" []
def int32Type : Val := .datatype "Core.Int32" []
def uint32Type : Val := .datatype "Core.UInt32" []
def int64Type : Val := longType
def uint64Type : Val := .datatype "Core.UInt64" []
def int128Type : Val := .datatype "Core.Int128" []
def uint128Type : Val := .datatype "Core.UInt128" []
def float16Type : Val := .datatype "Core.Float16" []
def float32Type : Val := .datatype "Core.Float32" []
def float64Type : Val := .datatype "Core.Float64" []
def charType : Val := .datatype "Core.Char" []
def stringType : Val := .datatype "Core.String" []
def nothingType : Val := .datatype "Core.Nothing" []
def colonType : Val := .datatype "Base.Colon" []
def indexLinearType : Val := .datatype "Base.IndexLinear" []
def indexCartesianType : Val := .datatype "Base.IndexCartesian" []
def oneToType (T : Val) : Val := .datatype "Base.OneTo" [T]
def valType (v : Val) : Val := .datatype "Base.Val" [v]

/-- Exception `DataType`s reported in `(exc <ser(typeof(e))>)`. -/
def methodErrorType : Val := .datatype "Core.MethodError" []
def boundsErrorType : Val := .datatype "Core.BoundsError" []
def argumentErrorType : Val := .datatype "Core.ArgumentError" []
def inexactErrorType : Val := .datatype "Core.InexactError" []
def typeErrorType : Val := .datatype "Core.TypeError" []
def canonicalIndexErrorType : Val := .datatype "Base.CanonicalIndexError" []
def dimensionMismatchType : Val := .datatype "Base.DimensionMismatch" []
def errorExceptionType : Val := .datatype "Core.ErrorException" []
def stackOverflowErrorType : Val := .datatype "Core.StackOverflowError" []
def divideErrorType : Val := .datatype "Core.DivideError" []

/-- `Core.CPU` address space parameter (`AddrSpace{Core}(0x00)`). -/
def cpuAddrSpace : Val := .bits (.datatype "Core.AddrSpace" [.module "Core"]) 0

/-- `GenericMemory{:not_atomic, T, Core.CPU}`. -/
def memoryType (elemTy : Val) : Val :=
  .datatype "Core.GenericMemory" [.symbol "not_atomic", elemTy, cpuAddrSpace]

/-- `GenericMemoryRef{:not_atomic, T, Core.CPU}`. -/
def memoryRefType (elemTy : Val) : Val :=
  .datatype "Core.GenericMemoryRef" [.symbol "not_atomic", elemTy, cpuAddrSpace]

/-- `Array{T, N}`. -/
def arrayType (elemTy : Val) (ndims : Nat) : Val :=
  .datatype "Core.Array" [elemTy, .long (Int.ofNat ndims)]

/-- `jl_typeof` on runtime objects (`Obj`). -/
def typeOf (H : Heap) : Obj → Val
  | .type t => JuliaLean.C.typeOf t
  | .bits ty _ => ty
  | .fn name =>
    match H.fnTypes.get? name with
    | some (.typeegal t) | some (.typeeq t) => JuliaLean.C.typeOf t
    | some ty => ty
    | none => .datatype ("#fn:" ++ name) []
  | .imm ty _ => ty
  | .ref addr =>
    match H.cells[addr]? with
    | some (.mut ty _) | some (.mem ty _) => ty
    | none => .bottom

/-- Construct primitive and singleton objects. -/
def mkInt (n : Int) : Obj := .bits int64Type n
def mkUInt64 (n : UInt64) : Obj := .bits uint64Type (Int.ofNat n.toNat)
def mkBool (b : Bool) : Obj := .bits boolType (if b then 1 else 0)
def nothingObj : Obj := .imm nothingType []
def colonObj : Obj := .imm colonType []
def indexLinearObj : Obj := .imm indexLinearType []
def indexCartesianObj : Obj := .imm indexCartesianType []

/-- Construct a `Tuple` object with its concrete `Core.Tuple` type. -/
def mkTuple (H : Heap) (xs : List Obj) : Obj :=
  .imm (.datatype tupleName (xs.map (typeOf H))) xs

/-- Allocate a mutable struct cell on `H`. -/
def Heap.allocMut (H : Heap) (ty : Val) (fields : Array Obj) : Heap × Obj :=
  let addr := H.cells.size
  ({ H with cells := H.cells.push (.mut ty fields) }, .ref addr)

/-- Allocate a `GenericMemory` cell on `H`. -/
def Heap.allocMem (H : Heap) (ty : Val) (elems : Array Obj) : Heap × Obj :=
  let addr := H.cells.size
  ({ H with cells := H.cells.push (.mem ty elems) }, .ref addr)

/-- Allocate an `Array{elemTy, dims.length}` backed by a `GenericMemory` cell on `H`, matching
`base/boot.jl:68-85` (`mutable struct Array{T,N}; ref::MemoryRef{T}; size::NTuple{N,Int}; end`). -/
def Heap.allocArray (H : Heap) (elemTy : Val) (dims : List Int) (elems : List Obj) : Heap × Obj :=
  let (H, memRef) := H.allocMem (memoryType elemTy) elems.toArray
  let refObj : Obj := .imm (memoryRefType elemTy) [memRef, mkInt 1]
  let sizeTy : Val := .datatype tupleName (dims.map (fun _ => int64Type))
  let sizeObj : Obj := .imm sizeTy (dims.map mkInt)
  H.allocMut (arrayType elemTy dims.length) #[refObj, sizeObj]

/-- Inspect an `Array` reference on `H`, returning `(elemTy, dims, elems)` when `o` is an `Array`. -/
def Heap.arrayInfo? (H : Heap) (o : Obj) : Option (Val × List Int × List Obj) := do
  let .ref addr := o | none
  let .mut (.datatype "Core.Array" [elemTy, _]) #[refObj, sizeObj] ← H.cells[addr]? | none
  let .imm _ [.ref memAddr, .bits _ offset] := refObj | none
  let .mem _ elems ← H.cells[memAddr]? | none
  let .imm _ sizeFields := sizeObj | none
  let dims ← sizeFields.mapM fun
    | .bits _ d => some d
    | _ => none
  let count := (dims.foldl (· * ·) 1).toNat
  let start := (offset - 1).toNat
  let slice := (elems.extract start (start + count)).toList
  some (elemTy, dims, slice)

end JuliaLean
