import Std
import JuliaLean.src.julia_h
import JuliaLean.src.jltypes_c
import JuliaLean.src.subtype_c
import JuliaLean.src.typemap_c
import JuliaLean.src.gf_c
import JuliaLean.src.object

/-!
Call and dispatch machinery for the Base generic-function pilot.

Bodies take the open-recursion dispatcher `Call := String → List Obj → R Obj` as their first
argument (`Body := Call → List Obj → R Obj`), so Lean files modelling `base/*.jl` never import
one another. Each generic function call builds the runtime dispatch tuple type
`Tuple{Core.Typeof(f), Core.Typeof.(args)...}`, looks up the method in the function's
`gf_c.MethodTable` via `gfLookup`, and invokes the corresponding body from `World.bodies` at
fuel `n - 1`.
-/

namespace JuliaLean

open JuliaLean.C

/-- Default step budget for subtyping and method-table lookup inside `gf_c.lean`. -/
def dispatchFuel : Nat := 100000

/-- Default call-depth fuel for `call` (exhaustion raises `StackOverflowError`). -/
def defaultCallFuel : Nat := 512

/-- Outcome error of a pilot execution step. -/
inductive Err where
  /-- A Julia exception thrown during execution (`throw(e)`), identified by `typeof(e)`. -/
  | exc (ty : Val) (msg : String := "")
  /-- A method selected by dispatch (or feature) that has no Lean body yet. -/
  | unmodelled (msg : String)
  /-- Internal model or harness error. -/
  | internal (msg : String)
  deriving Repr, Inhabited

/-- Mutable state threaded through a pilot execution (`R`). -/
structure ExecState where
  heap : Heap
  types : Types
  ops : GfOps
  fieldNames : Std.HashMap String (List String)
  typeFlags : List (Val × Nat) := []
  builtTables : Std.HashMap String MethodTable := {}
  lookupCache : Std.HashMap String LookupResult := {}
  selectedBodies : Std.HashSet (String × String) := {}
  usedBodyKeys : Std.HashSet String := {}
  selfObj : Obj := nothingObj
  nextId : Nat := 2000000000

/-- Errors preserve prior heap mutations and dispatch caches, as Julia exceptions do. -/
abbrev R := ExceptT Err (StateM ExecState)

/-- Open-recursion dispatcher passed to every method body. -/
abbrev Call := String → List Obj → R Obj

/-- A ported Julia method body (`Call → List Obj → R Obj`). -/
abbrev Body := Call → List Obj → R Obj

/-- Method tables (from `G` lines), function types (from `F` lines), `(fn, k) -> file:line`
locations, and registered Lean method bodies (`file:line -> Body`). -/
structure World where
  types : Types
  ops : GfOps
  fnTypes : Std.HashMap String Val
  tables : Std.HashMap String MethodTable
  rawMethods : Std.HashMap String (List Method) := {}
  locs : Std.HashMap (String × Int) String
  bodies : Std.HashMap String Body
  fieldNames : Std.HashMap String (List String)
  typeFlags : List (Val × Nat) := []
/-- Default struct field name tables for `getfield(x, :sym)`. -/
def defaultFieldNames : Std.HashMap String (List String) :=
  Std.HashMap.ofList
    [ ("Core.Array", ["ref", "size"])
    , ("Core.GenericMemory", ["length", "data"])
    , ("Core.GenericMemoryRef", ["mem", "data"])
    , ("Base.OneTo", ["stop"])
    , ("Base.UnitRange", ["start", "stop"])
    , ("Base.StepRange", ["start", "step", "stop"])
    , ("Base.Slice", ["indices"])
    , ("Base.IdentityUnitRange", ["indices"])
    , ("Base.LinearIndices", ["indices"])
    , ("Base.CartesianIndex", ["I"])
    , ("Base.CartesianIndices", ["indices"])
    , ("Base.LogicalIndex", ["mask", "sum"])
    , ("Main.P.LinV", ["n"])
    , ("Main.P.CartM", ["m", "n"])
    , ("Main.P.NoSize", [])
    , ("P.LinV", ["n"])
    , ("P.CartM", ["m", "n"])
    , ("P.NoSize", [])
    ]

/-- Run a `CM` type-system computation inside `R`. -/
def runCM (m : CM α) : R α := do
  let st ← get
  match m.run st.nextId with
  | .ok (a, nextId') =>
    set { st with nextId := nextId' }
    return a
  | .error e =>
    if e == "recursion budget exhausted" then
      throw (.exc stackOverflowErrorType e)
    else if e.startsWith "unmodelled:" then
      throw (.unmodelled e)
    else
      throw (.internal e)

/-- `jl_typeof(o)` in the current `Heap`. -/
def typeOfObj (o : Obj) : R Val := do
  return typeOf (← get).heap o

/-- The `#self#` callable object of the currently executing method. -/
def getSelf : R Obj := do
  return (← get).selfObj

/-- Construct a `Tuple` object in `R`. -/
def mkTupleR (xs : List Obj) : R Obj := do
  return mkTuple (← get).heap xs

/-- Throw a Julia exception of type `ty`. -/
def throwExc (ty : Val) (msg : String := "") : R α :=
  throw (.exc ty msg)

def throwMethodError (msg : String := "MethodError") : R α :=
  throw (.exc methodErrorType msg)

def throwBoundsError (msg : String := "BoundsError") : R α :=
  throw (.exc boundsErrorType msg)

def throwArgumentError (msg : String := "ArgumentError") : R α :=
  throw (.exc argumentErrorType msg)

def throwInexactError (msg : String := "InexactError") : R α :=
  throw (.exc inexactErrorType msg)

def throwTypeError (msg : String := "TypeError") : R α :=
  throw (.exc typeErrorType msg)

def throwCanonicalIndexError (msg : String := "CanonicalIndexError") : R α :=
  throw (.exc canonicalIndexErrorType msg)

def throwDimensionMismatch (msg : String := "DimensionMismatch") : R α :=
  throw (.exc dimensionMismatchType msg)

def throwErrorException (msg : String := "ErrorException") : R α :=
  throw (.exc errorExceptionType msg)

def throwDivideError (msg : String := "DivideError") : R α :=
  throw (.exc divideErrorType msg)

/-- Dispatch-tuple element type for a runtime argument `o` (`jl_inst_arg_tuple_type`,
`src/jltypes.c:2914-2933`): type objects use `TypeEgal{t}` (or `TypeEq{t}` if `t` has free
typevars), function singletons use their recorded `Core.Typeof(fn)`, and all other objects use
`typeOf H o`. -/
def argTypeElem (o : Obj) : R Val := do
  let st ← get
  match o with
  | .type t =>
    if t.hasFreeTypevars then
      runCM (wrapType dispatchFuel st.types st.ops.toOps t)
    else
      runCM (wrapTypeEgal t)
  | .fn name =>
    match st.heap.fnTypes.get? name with
    | some ft => return ft
    | none => return typeOf st.heap o
  | _ => return typeOf st.heap o

/-- Obtain the `MethodTable` for `tableName`, building and memoizing it on first use when stored in
`W.rawMethods`. -/
def getMethodTable (W : World) (tableName : String) : R MethodTable := do
  if let some mt := W.tables.get? tableName then
    return mt
  let st ← get
  if let some mt := st.builtTables.get? tableName then
    return mt
  let some ms := W.rawMethods.get? tableName
    | throw (.unmodelled s!"unmodelled: function {tableName}")
  let mt ← runCM (buildMethodTable dispatchFuel W.types W.ops ms)
  modify fun s => { s with builtTables := s.builtTables.insert tableName mt }
  return mt

/-- Look up the method selected by `gfLookup` for `f(args...)`. -/
def lookupMethod (n : Nat) (W : World) (f : String) (args : List Obj) :
    R (LookupResult × String × Obj × List Obj) := do
  if n == 0 then
    throw (.exc stackOverflowErrorType "StackOverflowError")
  let (tableName, selfObj, ft, callArgs) ←
    if f.startsWith "@type:" || f.startsWith "@obj:" then do
      let tname := (f.drop (if f.startsWith "@type:" then 6 else 5)).toString
      let self :: rest := args
        | throw (.internal s!"call {f} missing callable object")
      let ft ← argTypeElem self
      pure (tname, self, ft, rest)
    else
      match W.fnTypes.get? f with
      | some ft =>
        let self := match ft with
          | .typeegal t | .typeeq t => Obj.type t
          | _ => Obj.fn f
        pure (f, self, ft, args)
      | none =>
        throw (.unmodelled s!"unmodelled: function {f}")
  let mt ← getMethodTable W tableName
  let argTypes ← callArgs.mapM argTypeElem
  let argt : Val := .datatype tupleName (ft :: argTypes)
  let cacheKey := s!"{tableName}:{repr argt}"
  let st ← get
  if let some cached := st.lookupCache.get? cacheKey then
    return (cached, tableName, selfObj, callArgs)
  let res ← runCM (gfLookup dispatchFuel W.types W.ops mt argt)
  modify fun s => { s with lookupCache := s.lookupCache.insert cacheKey res }
  return (res, tableName, selfObj, callArgs)

/-- Look up a registered body for `(tableName, loc)`. -/
def findBody? (W : World) (tableName loc : String) : Option Body :=
  match W.bodies.get? (tableName ++ "@" ++ loc) with
  | some b => some b
  | none => W.bodies.get? loc

def recordBody (W : World) (fn loc : String) : R Unit := do
  let qualifiedKey := fn ++ "@" ++ loc
  let bodyKey := if W.bodies.contains qualifiedKey then qualifiedKey else loc
  modify fun s => { s with
    selectedBodies := s.selectedBodies.insert (fn, loc)
    usedBodyKeys := s.usedBodyKeys.insert bodyKey }

/-- Execute `f(args...)` at call fuel `n`:
1. If `f` is in `W.tables` or `W.rawMethods`, build `Tuple{typeof(f), typeof.(args)...}`, run
   `gfLookup`, and invoke the selected method's body at `n - 1` (or throw `MethodError` on
   `nomethod`/`ambiguous`, or `unmodelled: method <file>:<line>` when the selected method has no
   registered body).
2. If `f` is a type constructor not tabulated in `W.tables`/`W.rawMethods` (e.g. `Base.OneTo`,
   `Base.LinearIndices`, `Core.Int64`, `Core.Float64`) that has a constructor entry in `W.bodies`,
   invoke that constructor entry at `n - 1`. -/
def call : Nat → World → String → List Obj → R Obj
  | 0, _, _, _ => throw (.exc stackOverflowErrorType "StackOverflowError")
  | n + 1, W, f, args => do
    if ["Base.OneTo", "Base.LinearIndices", "Core.Int64", "Core.Float64"].contains f then
      let some ctorBody := W.bodies.get? f
        | throw (.unmodelled s!"unmodelled: constructor {f}")
      modify fun s => { s with usedBodyKeys := s.usedBodyKeys.insert f }
      return ← ctorBody (call n W) args
    let (res, tableName, selfObj, callArgs) ← lookupMethod (n + 1) W f args
    match res with
    | .nomethod => throwMethodError s!"MethodError: no method matching {tableName}"
    | .ambiguous => throwMethodError s!"MethodError: ambiguous call to {tableName}"
    | .method k =>
      let some loc := W.locs.get? (tableName, k)
        | throw (.internal s!"missing method location for ({tableName}, {k})")
      recordBody W tableName loc
      let some body := findBody? W tableName loc
        | throw (.unmodelled s!"unmodelled: method {loc}")
      let st ← get
      let prevSelf := st.selfObj
      set { st with selfObj := selfObj }
      try
        let out ← body (call n W) callArgs
        modify fun s => { s with selfObj := prevSelf }
        return out
      catch e =>
        modify fun s => { s with selfObj := prevSelf }
        throw e

/-- Top-level call entry point for `PilotHarness`: returns the top-level dispatch result
(`<file>:<line>`, `"nomethod"`, or `"ambiguous"`) together with the execution outcome. -/
def callTop (n : Nat) (W : World) (f : String) (args : List Obj) :
    R (String × Except Err Obj) := do
  let (res, tableName, selfObj, callArgs) ← lookupMethod n W f args
  match res with
  | .nomethod => return ("nomethod", .error (.exc methodErrorType "MethodError"))
  | .ambiguous => return ("ambiguous", .error (.exc methodErrorType "MethodError (ambiguous)"))
  | .method k =>
    let some loc := W.locs.get? (tableName, k)
      | return ("?", .error (.internal s!"missing method location for ({tableName}, {k})"))
    recordBody W tableName loc
    let some body := findBody? W tableName loc
      | return (loc, .error (.unmodelled s!"unmodelled: method {loc}"))
    let st ← get
    let prevSelf := st.selfObj
    set { st with selfObj := selfObj }
    match n with
    | 0 =>
      set { st with selfObj := prevSelf }
      return (loc, .error (.exc stackOverflowErrorType "StackOverflowError"))
    | n' + 1 =>
      try
        let out ← body (call n' W) callArgs
        modify fun s => { s with selfObj := prevSelf }
        return (loc, .ok out)
      catch e =>
        modify fun s => { s with selfObj := prevSelf }
        return (loc, .error e)

/-- Invoke a callable `Obj` (`Obj.fn` or `Obj.type`) through `call`. -/
def callObj (c : Call) (fObj : Obj) (args : List Obj) : R Obj :=
  match fObj with
  | .fn name => c name args
  | .type (.datatype name []) => c name args
  | .type (.datatype name (_ :: _)) => c ("@type:" ++ name) (fObj :: args)
  | .imm (.datatype name _) _ => c ("@obj:call:" ++ name) (fObj :: args)
  | .type t => throw (.unmodelled s!"unmodelled: call on type {repr t}")
  | _ => throw (.unmodelled s!"unmodelled: call on non-function object {repr fObj}")

/-! ## Core builtins and intrinsics used by Base method bodies -/

/-- Extract the integer value of a primitive `Obj.bits`. -/
def asInt (o : Obj) : R Int :=
  match o with
  | .bits _ v => return v
  | _ => throwTypeError s!"expected integer bits, got {repr o}"

/-- Extract a `Bool` from `Obj.bits boolType v` (throwing `TypeError` on non-`Bool`, matching
Julia's `if cond` / `&&` / `||` type check). -/
def asBool (o : Obj) : R Bool :=
  match o with
  | .bits ty v =>
    if ty == boolType then return (v != 0)
    else throwTypeError s!"TypeError: non-boolean ({repr ty}) used in boolean context"
  | _ => throwTypeError s!"TypeError: non-boolean ({repr o}) used in boolean context"

/-- Extract the fields of a `Core.Tuple` object. -/
def unpackTuple (o : Obj) : R (List Obj) :=
  match o with
  | .imm (.datatype "Core.Tuple" _) fields => return fields
  | _ => throwTypeError s!"expected Tuple, got {repr o}"

/-- `Core.nfields(x)` (`src/builtins.c`). -/
def nfieldsObj (o : Obj) : R Int := do
  match o with
  | .imm _ fields => return Int.ofNat fields.length
  | .ref addr =>
    let st ← get
    match st.heap.cells[addr]? with
    | some (.mut _ fields) => return Int.ofNat fields.size
    | some (.mem _ _) => return 2
    | none => throw (.internal s!"dangling heap ref {addr}")
  | .bits _ _ | .fn _ | .type _ => return 0

/-- `Core.getfield(x, i::Int, boundscheck::Bool = true)` (1-based index). -/
def getfieldIdx (o : Obj) (i : Int) (_boundscheck : Bool := true) : R Obj := do
  match o with
  | .imm _ fields =>
    if i < 1 || i > Int.ofNat fields.length then
      throwBoundsError "BoundsError: attempt to access Tuple/struct field out of bounds"
    return fields[(i - 1).toNat]!
  | .ref addr =>
    let st ← get
    match st.heap.cells[addr]? with
    | some (.mut _ fields) =>
      if i < 1 || i > Int.ofNat fields.size then
        throwBoundsError "BoundsError: attempt to access mutable struct field out of bounds"
      return fields[(i - 1).toNat]!
    | some (.mem _ elems) =>
      if i == 1 then return mkInt (Int.ofNat elems.size)
      else throwBoundsError "BoundsError: GenericMemory field access"
    | none => throw (.internal s!"dangling heap ref {addr}")
  | _ => throwBoundsError "BoundsError: getfield on object with no fields"

/-- `Core.getfield(x, sym::Symbol)` (`src/builtins.c`). -/
def getfieldSym (o : Obj) (field : String) : R Obj := do
  let st ← get
  let ty := typeOf st.heap o
  let .datatype dtName _ := ty
    | throwTypeError s!"getfield: expected struct DataType, got {repr ty}"
  let some names := st.fieldNames.get? dtName
    | throw (.unmodelled s!"unmodelled: field names for {dtName}")
  match names.idxOf? field with
  | some idx =>
    if idx < names.length then
      getfieldIdx o (Int.ofNat (idx + 1))
    else
      throwTypeError s!"type {dtName} has no field {field}"
  | none => throwTypeError s!"type {dtName} has no field {field}"

/-- `Core.argtail(x, rest...)` (`base/essentials.jl:541`). -/
def argtail (xs : List Obj) : R Obj := do
  match xs with
  | [] => throwArgumentError "Cannot call tail on an empty tuple."
  | _ :: rest => mkTupleR rest

/-- `Core.memoryrefnew(ref, i::Int, boundscheck::Bool)` (`src/genericmemory.c`).
Accepts either a `GenericMemory` (`Obj.ref`) or an existing `GenericMemoryRef` (`Obj.imm`). -/
def memoryrefnew (refOrMem : Obj) (i : Int) (boundscheck : Bool := false) : R Obj := do
  let st ← get
  match refOrMem with
  | .ref addr =>
    let some (.mem (.datatype "Core.GenericMemory" [_, elemTy, _]) elems) := st.heap.cells[addr]?
      | throwTypeError "memoryrefnew: expected GenericMemory"
    if boundscheck && (i < 1 || i > Int.ofNat elems.size) then
      throwBoundsError "BoundsError: memoryrefnew"
    return .imm (memoryRefType elemTy) [.ref addr, mkInt i]
  | .imm (ty@(.datatype "Core.GenericMemoryRef" _)) [.ref addr, .bits _ offset] =>
    let some (.mem _ elems) := st.heap.cells[addr]?
      | throw (.internal s!"dangling GenericMemory ref {addr}")
    let newIdx := offset + i - 1
    if boundscheck && (newIdx < 1 || newIdx > Int.ofNat elems.size) then
      throwBoundsError "BoundsError: memoryrefnew"
    return .imm ty [.ref addr, mkInt newIdx]
  | _ => throwTypeError s!"memoryrefnew: unexpected argument {repr refOrMem}"

/-- `Core.memoryrefget(ref::GenericMemoryRef, order::Symbol, boundscheck::Bool)` (`src/genericmemory.c`). -/
def memoryrefget (refObj : Obj) (_order : String := "not_atomic") (boundscheck : Bool := false) : R Obj := do
  let st ← get
  let .imm (.datatype "Core.GenericMemoryRef" _) [.ref addr, .bits _ idx] := refObj
    | throwTypeError s!"memoryrefget: expected GenericMemoryRef, got {repr refObj}"
  let some (.mem _ elems) := st.heap.cells[addr]?
    | throw (.internal s!"dangling GenericMemory ref {addr}")
  if idx < 1 || idx > Int.ofNat elems.size then
    if boundscheck then
      throwBoundsError "BoundsError: memoryrefget"
    else
      throwBoundsError "BoundsError: out-of-bounds memoryrefget"
  return elems[(idx - 1).toNat]!

/-- `Core.isa(o, T)` (`src/subtype.c:jl_isa`). -/
def isaObj (o : Obj) (targetTy : Val) : R Bool := do
  let st ← get
  match o with
  | .type t => runCM (jlSubtype dispatchFuel st.types (.typeegal t) targetTy)
  | _ =>
    let ty := typeOf st.heap o
    runCM (jlSubtype dispatchFuel st.types ty targetTy)

/-- Walk the supertype chain of `ty` using `datatypeComputeSuper` (`typemap_c.lean`) until reaching
`Core.AbstractArray{T, N}`, returning `(T, N)`. -/
def abstractArrayParamsOfType (fuel : Nat) (ty : Val) : R (Val × Int) := do
  match fuel with
  | 0 => throw (.exc stackOverflowErrorType "abstractArrayParamsOfType: fuel exhausted")
  | fuel' + 1 =>
    let unw := ty.unwrapUnionall
    match unw with
    | .datatype "Core.AbstractArray" [elemTy, .long ndims] =>
      return (elemTy, ndims)
    | .datatype _ _ =>
      let st ← get
      let some sup ← runCM (datatypeComputeSuper dispatchFuel st.types st.ops.toOps unw)
        | throwTypeError s!"{repr unw} is not a subtype of AbstractArray"
      if sup == unw then
        throwTypeError s!"{repr unw} is not a subtype of AbstractArray"
      abstractArrayParamsOfType fuel' sup
    | _ => throwTypeError s!"expected AbstractArray DataType, got {repr ty}"

/-- Extract `(T, N)` from an `AbstractArray{T, N}` instance `A`. -/
def abstractArrayParams (A : Obj) : R (Val × Int) := do
  let ty ← typeOfObj A
  abstractArrayParamsOfType 32 ty

/-- Core 64-bit unsigned comparison `Core.Intrinsics.ult_int(a, b)`: compares two 64-bit integer
bit patterns as `UInt64`. -/
def ultInt64 (a b : Int) : Bool :=
  let ua : UInt64 := UInt64.ofNat ((a % (1 <<< 64) + (1 <<< 64)).toNat % (1 <<< 64))
  let ub : UInt64 := UInt64.ofNat ((b % (1 <<< 64) + (1 <<< 64)).toNat % (1 <<< 64))
  ua < ub

/-- Wrap a signed mathematical integer to 64-bit two's-complement `Int64`. -/
def wrapInt64 (x : Int) : Int :=
  let m : Int := 1 <<< 64
  let h : Int := 1 <<< 63
  let u := ((x % m) + m) % m
  if u ≥ h then u - m else u

/-- Wrap an integer bit pattern to unsigned 64-bit `[0, 2^64)`. -/
def wrapUInt64 (x : Int) : Int :=
  let m : Int := 1 <<< 64
  ((x % m) + m) % m

end JuliaLean
