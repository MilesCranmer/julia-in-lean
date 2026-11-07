import JuliaLean.base.io

/-!
# Model of `base/runtime_internals.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Module, type, method and native-pointer identities are separate typed parameters.
Runtime/type-system operations, including Core `typeof`, `isdefined`, `applicable`
and `sizeof`, are typed primitives, not a reconstruction of Julia dispatch.
Julia-side branches, bounds checks, exception classes and bitfield arithmetic are
implemented here. Integer results retain their native widths. Mutable-world and
exception effects use `base.io.M`; recursive type queries have no fuel cutoff.
Generator eligibility reads lowered-code slots through typed runtime operations; frontend macro
expansion remains untranslated.
file containing their Julia source.
-/

namespace JuliaLean.base.runtime_internals
open JuliaLean
open JuliaLean.base.io (M Error whileLoop)
abbrev I := JInt64
abbrev U := JInt .u64
abbrev U32 := JInt .u32
abbrev U16 := JInt .u16
abbrev U8 := JInt .u8
abbrev Cint := JInt .i32
def i (z : Int) : I := JInt.wrap .i64 z

def has8 (value : U8) (mask : Nat) : Bool :=
  (BitVec.ofInt 8 value.val &&& BitVec.ofNat 8 mask).toNat != 0

def has16 (value : U16) (mask : Nat) : Bool :=
  (BitVec.ofInt 16 value.val &&& BitVec.ofNat 16 mask).toNat != 0

def alignInt (x size : I) : I :=
  JInt.wrap .i64 ((BitVec.ofInt 64 (x + size - i 1).val &&& BitVec.ofInt 64 (-size).val).toNat)

structure ModuleOps (World Module Sym : Type) where
  parent : Module → M World Module
  egal : Module → Module → Bool
  main : Module
  base : Module
  core : Module
  compiler : Module
  definedMainBase : M World Bool
  getMainBase : M World Module
  nameof : Module → M World Sym

/--
Julia source: base/runtime_internals.jl:624-640 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DataTypeLayout
    size::UInt32
    nfields::UInt32
    npointers::UInt32
    firstptr::Int32
    alignment::UInt16
    flags::UInt16
    # haspadding : 1;
    # fielddesc_type : 2;
    # arrayelem_isboxed : 1;
    # arrayelem_isunion : 1;
    # arrayelem_isatomic : 1;
    # arrayelem_islocked : 1;
    # isbitsegal : 1;
    # unused_bits : 7;
    # padding : 1;
end
```
-/
structure DataTypeLayout where
  size : U32
  nfields : U32
  npointers : U32
  firstptr : Cint
  alignment : U16
  flags : U16

structure TypeOps (World Value DataType Name Module Pointer Sym : Type) where
  unwrap : Value → Value
  asDatatype : Value → Option DataType
  datatypeValue : DataType → Value
  asUnion : Value → Option (Value × Value)
  isTypeEq : Value → Bool
  isTypeEgal : Value → Bool
  isAType : Value → Bool
  isTypeVar : Value → Bool
  typeParameter : Value → M World Value
  typeof : Value → DataType
  coreTypeof : Value → M World Value
  egal : Value → Value → Bool
  egalName : Name → Name → Bool
  bottom : Value
  any : Value
  typeOfBottomType : Value
  coreTypeofBottom : Value
  kindTypes : List Value
  tupleName : Name
  namedTupleName : Name
  nameOf : DataType → Name
  name : Name → Sym
  module : Name → Module
  nameFlags : Name → U8
  dataFlags : DataType → U16
  names : Name → List Sym
  wrapper : Name → Value
  parameter : DataType → I → M World Value
  parameters : DataType → M World (List Value)
  symbolTuple : Value → Option (List Sym)
  fieldtypes : DataType → M World (List Value)
  isTuple : Value → Bool
  isVaTuple : DataType → Bool
  isVararg : Value → Bool
  unwrapVararg : Value → Value
  tupleType : List Value → M World Value
  asTypeCollection : Value → Option (List Value)
  rewrapUnionall : Value → Value → M World Value
  hasInstance : DataType → M World Bool
  layout : DataType → Pointer
  isNull : Pointer → Bool
  loadLayout : Pointer → M World DataTypeLayout
  constFields : Name → Pointer
  atomicFields : Name → Pointer
  loadUInt32 : Pointer → I → M World U32
  nativeFieldIndex : DataType → Sym → Bool → M World Cint
  nfields : Value → M World I
  coreSizeof : Value → M World I
  applicable : Value → List Value → M World Bool
  isdefined : Value → Sym → M World Bool
  assertType : Value → M World Value
  typeintersect : Value → Value → M World Value
  morespecific : Value → Value → M World Cint


/--
Julia source: base/runtime_internals.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentmodule(m::Module) = (@_total_meta; ccall(:jl_module_parent, Ref{Module}, (Any,), m))
```
-/
def parentmoduleModule {World Module Sym : Type} (ops : ModuleOps World Module Sym)
    (m : Module) : M World Module := ops.parent m

/--
Julia source: base/runtime_internals.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_root_module(m::Module) = parentmodule(m) === m || m === Compiler || (isdefined(Main, :Base) && m === Main.Base)
```
-/
def isRootModule {World Module Sym : Type} (ops : ModuleOps World Module Sym)
    (m : Module) : M World Bool := do
  if ops.egal (← parentmoduleModule ops m) m then return true
  if ops.egal m ops.compiler then return true
  if !(← ops.definedMainBase) then return false
  pure (ops.egal m (← ops.getMainBase))

/--
Julia source: base/runtime_internals.jl:32-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function moduleroot(m::Module)
    @_total_meta
    while true
        is_root_module(m) && return m
        p = parentmodule(m)
        p === m && return m
        m = p
    end
end

```
-/
def moduleroot {World Module Sym : Type} (ops : ModuleOps World Module Sym) (m : Module) : M World Module :=
  whileLoop (fun m => do
    if ← isRootModule ops m then return .inl m
    let p ← parentmoduleModule ops m
    if ops.egal p m then return .inl m
    pure (.inr p)) m

/--
Julia source: base/runtime_internals.jl:48-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro __MODULE__()
    return __module__
end
```
-/
def moduleMacro {Module : Type} (expansionModule : Module) : Module := expansionModule

/--
Julia source: base/runtime_internals.jl:66-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fullname(m::Module)
    @_total_meta
    mn = nameof(m)
    if m === Main || m === Base || m === Core
        return (mn,)
    end
    mp = parentmodule(m)
    if mp === m
        return (mn,)
    end
    return (fullname(mp)..., mn)
end

```
-/
def fullname {World Module Sym : Type} (ops : ModuleOps World Module Sym) (m : Module) : M World (List Sym) :=
  whileLoop (fun (m, suffix) => do
    let name ← ops.nameof m
    if ops.egal m ops.main || ops.egal m ops.base || ops.egal m ops.core then return .inl (name :: suffix)
    let parent ← ops.parent m
    if ops.egal parent m then return .inl (name :: suffix)
    pure (.inr (parent, name :: suffix))) (m, [])

/--
Julia source: base/runtime_internals.jl:84-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function moduleloc(m::Module)
    line = Ref{Int32}(0)
    file = ccall(:jl_module_getloc, Ref{Symbol}, (Any, Ref{Int32}), m, line)
    return LineNumberNode(Int(line[]), file)
end
```
-/
def moduleloc {World Module Sym Ref32 Location : Type} (newRef : Cint → M World Ref32)
    (getloc : Module → Ref32 → M World Sym) (readRef : Ref32 → M World Cint)
    (lineNumberNode : I → Sym → M World Location) (m : Module) : M World Location := do
  let line ← newRef (JInt.wrap .i32 0)
  let file ← getloc m line
  lineNumberNode (i (← readRef line).val) file

/--
Julia source: base/runtime_internals.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
names(m::Module; kwargs...) = sort!(unsorted_names(m; kwargs...))
```
-/
def names {World Module Sym Keywords : Type} (unsorted : Module → Keywords → M World (List Sym))
    (sort : List Sym → M World (List Sym)) (m : Module) (kwargs : Keywords) : M World (List Sym) := do
  sort (← unsorted m kwargs)

/--
Julia source: base/runtime_internals.jl:123-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsorted_names(m::Module; all::Bool=false, imported::Bool=false, usings::Bool=false,
               world::UInt=tls_world_age()) =
    ccall(:jl_module_names, Array{Symbol,1}, (Any, Cint, Cint, Cint, UInt), m, all, imported, usings, world)
```
-/
def unsortedNames {World Module Sym : Type}
    (jlModuleNames : Module → Cint → Cint → Cint → U → M World (List Sym))
    (tlsWorldAge : M World U) (m : Module) (all imported usings : Bool := false)
    (world : Option U := none) : M World (List Sym) := do
  let world ← match world with | some world => pure world | none => tlsWorldAge
  jlModuleNames m (JInt.wrap .i32 (if all then 1 else 0))
    (JInt.wrap .i32 (if imported then 1 else 0)) (JInt.wrap .i32 (if usings then 1 else 0)) world

/--
Julia source: base/runtime_internals.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isexported(m::Module, s::Symbol) = ccall(:jl_module_exports_p, Cint, (Any, Any), m, s) != 0
```
-/
def isexported {World Module Sym : Type} (native : Module → Sym → M World Cint)
    (m : Module) (s : Sym) : M World Bool := do pure ((← native m s).val != 0)

/--
Julia source: base/runtime_internals.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispublic(m::Module, s::Symbol) = ccall(:jl_module_public_p, Cint, (Any, Any), m, s) != 0
```
-/
def ispublic {World Module Sym : Type} (native : Module → Sym → M World Cint)
    (m : Module) (s : Sym) : M World Bool := do pure ((← native m s).val != 0)

/--
Julia source: base/runtime_internals.jl:227-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdeprecated(m::Module, s::Symbol) = ccall(:jl_is_binding_deprecated, Cint, (Any, Any), m, s) != 0
```
-/
def isdeprecated {World Module Sym : Type} (native : Module → Sym → M World Cint)
    (m : Module) (s : Sym) : M World Bool := do pure ((← native m s).val != 0)

/--
Julia source: base/runtime_internals.jl:229-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function binding_module(m::Module, s::Symbol)
    p = ccall(:jl_get_module_of_binding, Ptr{Cvoid}, (Any, Any), m, s)
    p == C_NULL && return m
    return unsafe_pointer_to_objref(p)::Module
end
```
-/
def bindingModule {World Module Sym Pointer : Type} (native : Module → Sym → M World Pointer)
    (isNull : Pointer → Bool) (unsafeObjrefModule : Pointer → M World Module)
    (m : Module) (s : Sym) : M World Module := do
  let p ← native m s
  if isNull p then return m
  unsafeObjrefModule p

/--
Julia source: base/runtime_internals.jl:334-336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function delete_binding(mod::Module, sym::Symbol)
    ccall(:jl_disable_binding, Cvoid, (Any,), GlobalRef(mod, sym))
end
```
-/
def deleteBinding {World Module Sym GlobalRef : Type} (globalRef : Module → Sym → GlobalRef)
    (disableBinding : GlobalRef → M World Unit) (mod : Module) (sym : Sym) : M World Unit :=
  disableBinding (globalRef mod sym)

/--
Julia source: base/runtime_internals.jl:363-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function set_binding_visibility!(mod::Module, sym::Symbol, vis::Symbol)
    state = vis === :none   ? Cint(0) :
            vis === :public ? Cint(1) :
            vis === :export ? Cint(2) :
            throw(ArgumentError(LazyString("visibility must be :none, :public, or :export, got ", repr(vis))))
    ccall(:jl_module_set_visibility, Cvoid, (Any, Any, Cint), mod, sym, state)
    return nothing
end
```
-/
def setBindingVisibility {World Module Sym : Type} (literal : String → Sym)
    (egal : Sym → Sym → Bool) (native : Module → Sym → Cint → M World Unit)
    (mod : Module) (sym vis : Sym) : M World Unit := do
  let state ← if egal vis (literal "none") then pure (JInt.wrap .i32 0)
    else if egal vis (literal "public") then pure (JInt.wrap .i32 1)
    else if egal vis (literal "export") then pure (JInt.wrap .i32 2)
    else throw (.jl (.argumentError "visibility must be :none, :public, or :export"))
  native mod sym state
  pure ()

/--
Julia source: base/runtime_internals.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isTypeEq(@nospecialize t) = isa(t, TypeEq)
```
-/
def isTypeEq {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool := ops.isTypeEq t

/--
Julia source: base/runtime_internals.jl:1109-1109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isTypeEgal(@nospecialize t) = isa(t, Core.TypeEgal)
```
-/
def isTypeEgal {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool := ops.isTypeEgal t

/--
Julia source: base/runtime_internals.jl:1095-1095 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isType(@nospecialize t) = isTypeEq(t) || isTypeEgal(t)
```
-/
def isType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  isTypeEq ops t || isTypeEgal ops t

/--
Julia source: base/runtime_internals.jl:1111-1111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
type_parameter(t::TypeEq) = getfield(t, :T)
```
-/
def typeParameterEq {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : M World V :=
  ops.typeParameter t

/--
Julia source: base/runtime_internals.jl:1112-1112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
type_parameter(t::Core.TypeEgal) = getfield(t, :T)
```
-/
def typeParameterEgal {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : M World V :=
  ops.typeParameter t

/--
Julia source: base/runtime_internals.jl:861-861 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ismutabletypename(tn::Core.TypeName) = tn.flags & 0x2 == 0x2
```
-/
def ismutabletypename {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (tn : N) : Bool :=
  has8 (ops.nameFlags tn) 2

/--
Julia source: base/runtime_internals.jl:840-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ismutable(@nospecialize(x)) = (@_total_meta; (typeof(x).name::Core.TypeName).flags & 0x2 == 0x2)
```
-/
def ismutable {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (x : V) : Bool :=
  has8 (ops.nameFlags (ops.nameOf (ops.typeof x))) 2

/--
Julia source: base/runtime_internals.jl:854-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ismutabletype(@nospecialize t)
    @_total_meta
    t = unwrap_unionall(t)
    # TODO: what to do for `Union`?
    return isa(t, DataType) && ismutabletypename(t.name)
end
```
-/
def ismutabletype {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  match ops.asDatatype (ops.unwrap t) with | none => false | some dt => ismutabletypename ops (ops.nameOf dt)

/--
Julia source: base/runtime_internals.jl:885-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isprimitivetype(@nospecialize t)
    @_total_meta
    t = unwrap_unionall(t)
    # TODO: what to do for `Union`?
    isa(t, DataType) || return false
    return (t.flags & 0x0080) == 0x0080
end
```
-/
def isprimitivetype {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  match ops.asDatatype (ops.unwrap t) with | none => false | some dt => has16 (ops.dataFlags dt) 128

/--
Julia source: base/runtime_internals.jl:1186-1192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isabstracttype(@nospecialize(t))
    @_total_meta
    t = unwrap_unionall(t)
    isType(t) && return true
    # TODO: what to do for `Union`?
    return isa(t, DataType) && (t.name.flags & 0x1) == 0x1
end
```
-/
def isabstracttype {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  let t := ops.unwrap t
  if isType ops t then true
  else match ops.asDatatype t with | none => false | some dt => has8 (ops.nameFlags (ops.nameOf dt)) 1

/--
Julia source: base/runtime_internals.jl:870-876 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isstructtype(@nospecialize t)
    @_total_meta
    t = unwrap_unionall(t)
    # TODO: what to do for `Union`?
    isa(t, DataType) || return false
    return !isprimitivetype(t) && !isabstracttype(t)
end
```
-/
def isstructtype {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  let t := ops.unwrap t
  match ops.asDatatype t with
  | none => false
  | some _ => !isprimitivetype ops t && !isabstracttype ops t

/--
Julia source: base/runtime_internals.jl:917-917 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isbitstype(@nospecialize t) = (@_total_meta; isa(t, DataType) && (t.flags & 0x0008) == 0x0008)
```
-/
def isbitstype {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  match ops.asDatatype t with | none => false | some dt => has16 (ops.dataFlags dt) 8

/--
Julia source: base/runtime_internals.jl:990-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdispatchtuple(@nospecialize(t)) = (@_total_meta; isa(t, DataType) && (t.flags & 0x0004) == 0x0004)
```
-/
def isdispatchtuple {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  match ops.asDatatype t with | none => false | some dt => has16 (ops.dataFlags dt) 4

/--
Julia source: base/runtime_internals.jl:1161-1161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isconcretetype(@nospecialize(t)) = (@_total_meta; isa(t, DataType) && (t.flags & 0x0002) == 0x0002)
```
-/
def isconcretetype {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  match ops.asDatatype t with | none => false | some dt => has16 (ops.dataFlags dt) 2

/--
Julia source: base/runtime_internals.jl:924-924 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isbits(@nospecialize x) = isbitstype(typeof(x))
```
-/
def isbits {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (x : V) : Bool :=
  isbitstype ops (ops.datatypeValue (ops.typeof x))

/--
Julia source: base/runtime_internals.jl:936-939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function objectid(@nospecialize(x))
    @_total_meta
    return ccall(:jl_object_id, UInt, (Any,), x)
end
```
-/
def objectid {World V : Type} (jlObjectId : V → M World U) (x : V) : M World U := jlObjectId x

/--
Julia source: base/runtime_internals.jl:992-992 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_ismutationfree(dt::DataType) = (@_total_meta; (dt.flags & 0x0100) == 0x0100)
```
-/
def datatypeIsmutationfree {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : Bool :=
  has16 (ops.dataFlags dt) 256

/--
Julia source: base/runtime_internals.jl:1017-1017 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_isidentityfree(dt::DataType) = (@_total_meta; (dt.flags & 0x0200) == 0x0200)
```
-/
def datatypeIsidentityfree {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : Bool :=
  has16 (ops.dataFlags dt) 512

/--
Julia source: base/runtime_internals.jl:1003-1015 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ismutationfree(@nospecialize(t))
    t = unwrap_unionall(t)
    if isa(t, DataType)
        return datatype_ismutationfree(t)
    elseif isType(t)
        T = type_parameter(t)
        return isa(T, Type) && ismutationfree(typeof(T))
    elseif isa(t, Union)
        return ismutationfree(t.a) && ismutationfree(t.b)
    end
    # TypeVar, etc.
    return false
end
```
-/
def ismutationfree {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : M World Bool := fun world => do
  let t := ops.unwrap t
  if let some dt := ops.asDatatype t then return .ok (datatypeIsmutationfree ops dt, world)
  if isType ops t then
    match ← ops.typeParameter t world with
    | .error error => pure (.error error)
    | .ok (target, world) =>
      if !ops.isAType target then return .ok (false, world)
      ismutationfree ops (ops.datatypeValue (ops.typeof target)) world
  else if let some (a, b) := ops.asUnion t then
    match ← ismutationfree ops a world with
    | .error error => pure (.error error)
    | .ok (false, world) => pure (.ok (false, world))
    | .ok (true, world) => ismutationfree ops b world
  else pure (.ok (false, world))
partial_fixpoint

/--
Julia source: base/runtime_internals.jl:1026-1038 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isidentityfree(@nospecialize(t))
    t = unwrap_unionall(t)
    if isa(t, DataType)
        return datatype_isidentityfree(t)
    elseif isType(t)
        T = type_parameter(t)
        return isa(T, Type) && isidentityfree(typeof(T))
    elseif isa(t, Union)
        return isidentityfree(t.a) && isidentityfree(t.b)
    end
    # TypeVar, etc.
    return false
end
```
-/
def isidentityfree {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : M World Bool := fun world => do
  let t := ops.unwrap t
  if let some dt := ops.asDatatype t then return .ok (datatypeIsidentityfree ops dt, world)
  if isType ops t then
    match ← ops.typeParameter t world with
    | .error error => pure (.error error)
    | .ok (target, world) =>
      if !ops.isAType target then return .ok (false, world)
      isidentityfree ops (ops.datatypeValue (ops.typeof target)) world
  else if let some (a, b) := ops.asUnion t then
    match ← isidentityfree ops a world with
    | .error error => pure (.error error)
    | .ok (false, world) => pure (.ok (false, world))
    | .ok (true, world) => isidentityfree ops b world
  else pure (.ok (false, world))
partial_fixpoint

/--
Julia source: base/runtime_internals.jl:1049-1049 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iskindtype(@nospecialize t) = (t === Core.AnyType || t === DataType || t === UnionAll || t === Union || t === TypeEq || t === Core.TypeEgal || t === typeof(Bottom))
```
-/
def iskindtype {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  ops.kindTypes.any (fun kind => ops.egal t kind)

/--
Julia source: base/runtime_internals.jl:1074-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isconcretedispatch(@nospecialize t) = isconcretetype(t) && !iskindtype(t)
```
-/
def isconcretedispatch {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : Bool :=
  isconcretetype ops t && !iskindtype ops t

/--
Julia source: base/runtime_internals.jl:1080-1083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isdispatchelem(@nospecialize v)
    return (v === Bottom) || (v === typeof(Bottom)) || isconcretedispatch(v) ||
        isTypeEgal(v) || (isTypeEq(v) && type_parameter(v) === Union{})
end
```
-/
def isdispatchelem {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (v : V) : M World Bool := do
  if ops.egal v ops.bottom || ops.egal v ops.coreTypeofBottom || isconcretedispatch ops v || isTypeEgal ops v then return true
  if !isTypeEq ops v then return false
  pure (ops.egal (← ops.typeParameter v) ops.bottom)

/--
Julia source: base/runtime_internals.jl:642-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function DataTypeLayout(dt::DataType)
    layout = dt.layout::Ptr{Cvoid}
    layout == C_NULL && throw(UndefRefError())
    return unsafe_load(convert(Ptr{DataTypeLayout}, layout))
end
```
-/
def dataTypeLayout {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World DataTypeLayout := do
  let layout := ops.layout dt
  if ops.isNull layout then throw (.foreignError "UndefRefError" "null datatype layout")
  ops.loadLayout layout

/--
Julia source: base/runtime_internals.jl:656-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_alignment(dtl::DataTypeLayout) = Int(dtl.alignment)
```
-/
def datatypeAlignmentLayout (dtl : DataTypeLayout) : I := i dtl.alignment.val

/--
Julia source: base/runtime_internals.jl:702-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_haspadding(dtl::DataTypeLayout) = dtl.flags & 1 == 1
```
-/
def datatypeHaspaddingLayout (dtl : DataTypeLayout) : Bool := has16 dtl.flags 1

/--
Julia source: base/runtime_internals.jl:713-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_isbitsegal(dtl::DataTypeLayout) = (dtl.flags & (1<<7)) != 0
```
-/
def datatypeIsbitsegalLayout (dtl : DataTypeLayout) : Bool := has16 dtl.flags 128

/--
Julia source: base/runtime_internals.jl:723-723 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_nfields(dtl::DataTypeLayout) = dtl.nfields
```
-/
def datatypeNfieldsLayout (dtl : DataTypeLayout) : U32 := dtl.nfields

/--
Julia source: base/runtime_internals.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_npointers(dtl::DataTypeLayout) = dtl.npointers
```
-/
def datatypeNpointersLayout (dtl : DataTypeLayout) : U32 := dtl.npointers

/--
Julia source: base/runtime_internals.jl:754-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_fielddesc_type(dtl::DataTypeLayout) = (dtl.flags >> 1) & 3
```
-/
def datatypeFielddescTypeLayout (dtl : DataTypeLayout) : U16 := JInt.wrap .u16 ((dtl.flags.val / 2) % 4)

/--
Julia source: base/runtime_internals.jl:767-767 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_arrayelem(dtl::DataTypeLayout) = (dtl.flags >> 3) & 3
```
-/
def datatypeArrayelemLayout (dtl : DataTypeLayout) : U16 := JInt.wrap .u16 ((dtl.flags.val / 8) % 4)

/--
Julia source: base/runtime_internals.jl:770-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_layoutsize(dtl::DataTypeLayout) = dtl.size % Int
```
-/
def datatypeLayoutsizeLayout (dtl : DataTypeLayout) : I := i dtl.size.val

/--
Julia source: base/runtime_internals.jl:655-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_alignment(dt::DataType) = (@_foldable_meta; datatype_alignment(DataTypeLayout(dt)))
```
-/
def datatypeAlignment {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World I := do
  pure (datatypeAlignmentLayout (← dataTypeLayout ops dt))

/--
Julia source: base/runtime_internals.jl:701-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_haspadding(dt::DataType) = (@_foldable_meta; datatype_haspadding(DataTypeLayout(dt)))
```
-/
def datatypeHaspadding {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World Bool := do
  pure (datatypeHaspaddingLayout (← dataTypeLayout ops dt))

/--
Julia source: base/runtime_internals.jl:712-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_isbitsegal(dt::DataType) = (@_foldable_meta; datatype_isbitsegal(DataTypeLayout(dt)))
```
-/
def datatypeIsbitsegal {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World Bool := do
  pure (datatypeIsbitsegalLayout (← dataTypeLayout ops dt))

/--
Julia source: base/runtime_internals.jl:722-722 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_nfields(dt::DataType) = (@_foldable_meta; datatype_nfields(DataTypeLayout(dt)))
```
-/
def datatypeNfields {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World U32 := do
  pure (datatypeNfieldsLayout (← dataTypeLayout ops dt))

/--
Julia source: base/runtime_internals.jl:730-730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_npointers(dt::DataType) = (@_foldable_meta; datatype_npointers(DataTypeLayout(dt)))
```
-/
def datatypeNpointers {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World U32 := do
  pure (datatypeNpointersLayout (← dataTypeLayout ops dt))

/--
Julia source: base/runtime_internals.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_fielddesc_type(dt::DataType) = (@_foldable_meta; datatype_fielddesc_type(DataTypeLayout(dt)))
```
-/
def datatypeFielddescType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World U16 := do
  pure (datatypeFielddescTypeLayout (← dataTypeLayout ops dt))

/--
Julia source: base/runtime_internals.jl:766-766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_arrayelem(dt::DataType) = (@_foldable_meta; datatype_arrayelem(DataTypeLayout(dt)))
```
-/
def datatypeArrayelem {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World U16 := do
  pure (datatypeArrayelemLayout (← dataTypeLayout ops dt))

/--
Julia source: base/runtime_internals.jl:769-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_layoutsize(dt::DataType) = (@_foldable_meta; datatype_layoutsize(DataTypeLayout(dt)))
```
-/
def datatypeLayoutsize {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World I := do
  pure (datatypeLayoutsizeLayout (← dataTypeLayout ops dt))

/--
Julia source: base/runtime_internals.jl:739-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function datatype_pointerfree(dt::DataType)
    @_foldable_meta
    return datatype_npointers(dt) == 0
end
```
-/
def datatypePointerfree {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World Bool := do
  pure ((← datatypeNpointers ops dt).val == 0)

/--
Julia source: base/runtime_internals.jl:1194-1196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_datatype_layoutopaque(dt::DataType)
    datatype_nfields(dt) == 0 && !datatype_pointerfree(dt)
end
```
-/
def isDatatypeLayoutopaque {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (dt : D) : M World Bool := do
  if (← datatypeNfields ops dt).val != 0 then return false
  pure (!(← datatypePointerfree ops dt))

/--
Julia source: base/runtime_internals.jl:1212-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issingletontype(@nospecialize(t)) = (@_total_meta; isa(t, DataType) && isdefined(t, :instance) && datatype_layoutsize(t) == 0 && datatype_pointerfree(t))
```
-/
def issingletontype {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : M World Bool := do
  let some dt := ops.asDatatype t | return false
  if !(← ops.hasInstance dt) then return false
  if (← datatypeLayoutsize ops dt).val != 0 then return false
  datatypePointerfree ops dt

/--
Julia source: base/runtime_internals.jl:658-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uniontype_layout(@nospecialize T::Type)
    sz = RefValue{Csize_t}(0)
    algn = RefValue{Csize_t}(0)
    isinline = ccall(:jl_islayout_inline, Cint, (Any, Ptr{Csize_t}, Ptr{Csize_t}), T, sz, algn) != 0
    (isinline, Int(sz[]), Int(algn[]))
end
```
-/
def uniontypeLayout {World V Ref : Type} (newRef : U → M World Ref) (get : Ref → M World U)
    (jlIslayoutInline : V → Ref → Ref → M World Cint) (t : V) : M World (Bool × I × I) := do
  let size ← newRef (JInt.wrap .u64 0)
  let alignment ← newRef (JInt.wrap .u64 0)
  let inlineValue := (← jlIslayoutInline t size alignment).val != 0
  let size ← JuliaLean.base.io.liftJl (JInt.convert "convert" .i64 (← get size).val)
  let alignment ← JuliaLean.base.io.liftJl (JInt.convert "convert" .i64 (← get alignment).val)
  pure (inlineValue, size, alignment)

/--
Julia source: base/runtime_internals.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LLT_ALIGN(x, sz) = (x + sz - 1) & -sz
```
-/
def lltAlign {A B R : Type} (add : A → B → R) (subOne : R → R) (neg : B → B)
    (bitand : R → B → R) (x : A) (size : B) : R := bitand (subOne (add x size)) (neg size)

/--
Julia source: base/runtime_internals.jl:668-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function aligned_sizeof(@nospecialize T::Type)
    @_foldable_meta
    if isa(T, Union)
        if allocatedinline(T)
            # NOTE this check is equivalent to `isbitsunion(T)`, we can improve type
            # inference in the second branch with the outer `isa(T, Union)` check
            _, sz, al = uniontype_layout(T)
            return LLT_ALIGN(sz, al)
        end
    elseif allocatedinline(T)
        if T === Type{Union{}}
            # allocated with the layout of the `typeof(Union{})` singleton
            # (cf. `normalize_typeofbottom_layout_alias`), which is what the
            # `DataType`-only layout queries below expect
            T = Core.TypeofBottom
        end
        al = datatype_alignment(T)
        return LLT_ALIGN(Core.sizeof(T), al)
    end
    return Core.sizeof(Ptr{Cvoid})
end
```
-/
def alignedSizeof {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (allocatedinline : V → M World Bool) (unionLayout : V → M World (Bool × I × I))
    (pointerSize : I) (t : V) : M World I := do
  let mut t := t
  if (ops.asUnion t).isSome then
    if ← allocatedinline t then
      let (_, size, alignment) ← unionLayout t
      return alignInt size alignment
  else if ← allocatedinline t then
    if ops.egal t ops.typeOfBottomType then t := ops.coreTypeofBottom
    let some dt := ops.asDatatype t | throw (.foreignError "MethodError" "datatype_alignment")
    let alignment ← datatypeAlignment ops dt
    return alignInt (← ops.coreSizeof t) alignment
  pure pointerSize

/--
Julia source: base/runtime_internals.jl:690-690 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gc_alignment(sz::Integer) = Int(ccall(:jl_alignment, Cint, (Csize_t,), sz))
```
-/
def gcAlignmentSize {World Integer : Type} (jlAlignment : Integer → M World Cint) (size : Integer) : M World I := do
  pure (i (← jlAlignment size).val)

/--
Julia source: base/runtime_internals.jl:691-691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gc_alignment(T::Type) = gc_alignment(Core.sizeof(T))
```
-/
def gcAlignmentType {World V : Type} (sizeof : V → M World I)
    (gcAlignment : I → M World I) (t : V) : M World I := do gcAlignment (← sizeof t)

/--
Julia source: base/runtime_internals.jl:774-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct FieldDesc
    isforeign::Bool
    isptr::Bool
    size::UInt32
    offset::UInt32
end
```
-/
structure FieldDesc where
  isforeign : Bool
  isptr : Bool
  size : U32
  offset : U32

/--
Julia source: base/runtime_internals.jl:781-784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct FieldDescStorage{T}
    ptrsize::T
    offset::T
end
```
-/
structure FieldDescStorage (T : Type) where
  ptrsize : T
  offset : T

/--
Julia source: base/runtime_internals.jl:785-787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
FieldDesc(fd::FieldDescStorage{T}) where {T} =
    FieldDesc(false, fd.ptrsize & 1 != 0,
              fd.ptrsize >> 1, fd.offset)
```
-/
def fieldDescFromStorage {World T : Type} (andOneNonzero : T → M World Bool)
    (shiftRightOne : T → M World T) (convertUInt32 : T → M World U32)
    (fd : FieldDescStorage T) : M World FieldDesc := do
  let isptr ← andOneNonzero fd.ptrsize
  let size ← shiftRightOne fd.ptrsize
  let size ← convertUInt32 size
  let offset ← convertUInt32 fd.offset
  pure ⟨false, isptr, size, offset⟩

def decodeBitsStorage {World : Type} {t : IntTy} (fd : FieldDescStorage (JInt t)) : M World FieldDesc :=
  fieldDescFromStorage (fun value => pure (value.val % 2 != 0))
    (fun value => pure (JInt.wrap t (value.val / 2)))
    (fun value => JuliaLean.base.io.liftJl (JInt.convert "convert" .u32 value.val)) fd

/--
Julia source: base/runtime_internals.jl:789-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DataTypeFieldDesc
    dt::DataType
    function DataTypeFieldDesc(dt::DataType)
        dt.layout == C_NULL && throw(UndefRefError())
        new(dt)
    end
end
```
-/
structure DataTypeFieldDesc (D : Type) where
  dt : D

/--
Julia source: base/runtime_internals.jl:791-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function DataTypeFieldDesc(dt::DataType)
        dt.layout == C_NULL && throw(UndefRefError())
        new(dt)
    end
```
-/
def dataTypeFieldDesc {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (dt : D) : M World (DataTypeFieldDesc D) := do
  if ops.isNull (ops.layout dt) then throw (.foreignError "UndefRefError" "null datatype layout")
  pure ⟨dt⟩

/--
Julia source: base/runtime_internals.jl:797-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(dtfd::DataTypeFieldDesc, i::Int)
    layout_ptr = convert(Ptr{DataTypeLayout}, dtfd.dt.layout)
    fd_ptr = layout_ptr + Core.sizeof(DataTypeLayout)
    layout = unsafe_load(layout_ptr)
    fielddesc_type = (layout.flags >> 1) & 3
    nfields = layout.nfields
    @boundscheck ((1 <= i <= nfields) || throw(BoundsError(dtfd, i)))
    if fielddesc_type == 0  # JL_FIELDDESC_8
        return FieldDesc(unsafe_load(Ptr{FieldDescStorage{UInt8}}(fd_ptr), i))
    elseif fielddesc_type == 1  # JL_FIELDDESC_16
        return FieldDesc(unsafe_load(Ptr{FieldDescStorage{UInt16}}(fd_ptr), i))
    elseif fielddesc_type == 2  # JL_FIELDDESC_32
        return FieldDesc(unsafe_load(Ptr{FieldDescStorage{UInt32}}(fd_ptr), i))
    else # fielddesc_type == 3  # JL_FIELDDESC_FOREIGN
        return FieldDesc(true, true, 0, 0)
    end
end
```
-/
def getindexFieldDesc {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (addPointer : P → I → M World P) (layoutSizeof : M World I)
    (load8 : P → I → M World (FieldDescStorage U8))
    (load16 : P → I → M World (FieldDescStorage U16))
    (load32 : P → I → M World (FieldDescStorage U32))
    (dtfd : DataTypeFieldDesc D) (index : I) : M World FieldDesc := do
  let layoutPointer := ops.layout dtfd.dt
  let fieldsPointer ← addPointer layoutPointer (← layoutSizeof)
  let layout ← ops.loadLayout layoutPointer
  let fielddescType := datatypeFielddescTypeLayout layout
  if !(i 1 ≤ index && index.val ≤ layout.nfields.val) then throw (.jl .boundsError)
  if fielddescType.val == 0 then decodeBitsStorage (← load8 fieldsPointer index)
  else if fielddescType.val == 1 then decodeBitsStorage (← load16 fieldsPointer index)
  else if fielddescType.val == 2 then decodeBitsStorage (← load32 fieldsPointer index)
  else pure ⟨true, true, JInt.wrap .u32 0, JInt.wrap .u32 0⟩

/--
Julia source: base/runtime_internals.jl:237-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldnames(@nospecialize t)
    if t.name === _NAMEDTUPLE_NAME
        if t.parameters[1] isa Tuple
            return t.parameters[1]
        else
            throw(ArgumentError("type does not have definite field names"))
        end
    end
    return t.name.names
end
```
-/
def internalFieldnames {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : D)
    : M World (List Sym) := do
  if ops.egalName (ops.nameOf t) ops.namedTupleName then
    let names ← ops.parameter t (i 1)
    match ops.symbolTuple names with
    | some names => pure names
    | none => throw (.jl (.argumentError "type does not have definite field names"))
  else pure (ops.names (ops.nameOf t))

/--
Julia source: base/runtime_internals.jl:1376-1396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function datatype_fieldcount(t::DataType)
    if t.name === _NAMEDTUPLE_NAME
        names, types = t.parameters[1], t.parameters[2]
        if names isa Tuple
            return length(names)
        end
        if types isa DataType && types <: Tuple
            return datatype_fieldcount(types)
        end
        return nothing
    elseif isabstracttype(t)
        return nothing
    end
    if t.name === Tuple.name
        isvatuple(t) && return nothing
        return length(t.types)
    end
    # Equivalent to length(t.types), but `t.types` is lazy and we do not want
    # to be forced to compute it.
    return length(t.name.names)
end
```
-/
def datatypeFieldcount {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : D)
    : M World (Option I) := fun world => do
  if ops.egalName (ops.nameOf t) ops.namedTupleName then
    match ← ops.parameter t (i 1) world with
    | .error error => pure (.error error)
    | .ok (names, world) =>
      match ← ops.parameter t (i 2) world with
      | .error error => pure (.error error)
      | .ok (types, world) =>
        if let some names := ops.symbolTuple names then return .ok (some (i names.length), world)
        if let some typesData := ops.asDatatype types then
          if ops.isTuple types then return ← datatypeFieldcount ops typesData world
        pure (.ok (none, world))
  else if isabstracttype ops (ops.datatypeValue t) then pure (.ok (none, world))
  else if ops.egalName (ops.nameOf t) ops.tupleName then
    if ops.isVaTuple t then return .ok (none, world)
    match ← ops.fieldtypes t world with
    | .error error => pure (.error error)
    | .ok (types, world) => pure (.ok (some (i types.length), world))
  else pure (.ok (some (i (ops.names (ops.nameOf t)).length), world))
partial_fixpoint

/--
Julia source: base/runtime_internals.jl:1398-1409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typename_noerror(@nospecialize(t))
    t = unwrap_unionall(t)
    if t isa DataType
        return t.name
    elseif t isa Union
        aname = _typename_noerror(t.a)
        aname === nothing && return nothing
        bname = _typename_noerror(t.b)
        return aname === bname ? aname : nothing
    end
    return nothing
end
```
-/
def typenameNoerror {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V)
    : M World (Option N) := fun world => do
  let t := ops.unwrap t
  if let some dt := ops.asDatatype t then return .ok (some (ops.nameOf dt), world)
  if let some (a, b) := ops.asUnion t then
    match ← typenameNoerror ops a world with
    | .error error => pure (.error error)
    | .ok (none, world) => pure (.ok (none, world))
    | .ok (some aname, world) =>
      match ← typenameNoerror ops b world with
      | .error error => pure (.error error)
      | .ok (some bname, world) => pure (.ok (if ops.egalName aname bname then some aname else none, world))
      | .ok (none, world) => pure (.ok (none, world))
  else pure (.ok (none, world))
partial_fixpoint

/--
Julia source: base/runtime_internals.jl:1440-1455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldcount_noerror(@nospecialize(t))
    t === Union{} && return 0
    t = unwrap_unionall(t)
    if t isa Union
        _typename_noerror(t) === nothing && return nothing
        acount = _fieldcount_noerror(t.a)
        acount === nothing && return nothing
        bcount = _fieldcount_noerror(t.b)
        return acount === bcount ? acount : nothing
    elseif t === Union{}
        return 0
    end
    t isa DataType || return nothing
    return datatype_fieldcount(t)
end

```
-/
def internalFieldcountNoerror {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V)
    : M World (Option I) := fun world => do
  if ops.egal t ops.bottom then return .ok (some (i 0), world)
  let t := ops.unwrap t
  if let some (a, b) := ops.asUnion t then
    match ← typenameNoerror ops t world with
    | .error error => pure (.error error)
    | .ok (none, world) => pure (.ok (none, world))
    | .ok (some _, world) =>
      match ← internalFieldcountNoerror ops a world with
      | .error error => pure (.error error)
      | .ok (none, world) => pure (.ok (none, world))
      | .ok (some acount, world) =>
        match ← internalFieldcountNoerror ops b world with
        | .error error => pure (.error error)
        | .ok (bcount, world) => pure (.ok (if bcount == some acount then some acount else none, world))
  else if ops.egal t ops.bottom then pure (.ok (some (i 0), world))
  else if let some dt := ops.asDatatype t then datatypeFieldcount ops dt world
  else pure (.ok (none, world))
partial_fixpoint

/--
Julia source: base/runtime_internals.jl:1489-1491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fieldcount_noerror(@nospecialize t)
    return _fieldcount_noerror(t)
end
```
-/
def fieldcountNoerror {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V)
    : M World (Option I) := internalFieldcountNoerror ops t

/--
Julia source: base/runtime_internals.jl:1462-1487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fieldcount(@nospecialize t)
    @_foldable_meta
    if t === Union{}
        throw(ArgumentError("The empty type does not have a well-defined number of fields since it does not have instances."))
    end
    if t isa Core.TypeEgal
        return nfields(type_parameter(t))
    end
    t = unwrap_unionall(t)
    if t isa Union
        fcount = _fieldcount_noerror(t)
        fcount === nothing && throw(ArgumentError("type does not have a definite number of fields"))
        return fcount
    end
    if t isa TypeEq
        throw(ArgumentError("type does not have a definite number of fields"))
    end
    if !(t isa DataType)
        throw(TypeError(:fieldcount, DataType, t))
    end
    fcount = datatype_fieldcount(t)
    if fcount === nothing
        throw(ArgumentError("type does not have a definite number of fields"))
    end
    return fcount
end
```
-/
def fieldcount {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : M World I := do
  if ops.egal t ops.bottom then
    throw (.jl (.argumentError "The empty type does not have a well-defined number of fields since it does not have instances."))
  if ops.isTypeEgal t then return ← ops.nfields (← ops.typeParameter t)
  let t := ops.unwrap t
  if (ops.asUnion t).isSome then
    let some count ← internalFieldcountNoerror ops t |
      throw (.jl (.argumentError "type does not have a definite number of fields"))
    return count
  if ops.isTypeEq t then throw (.jl (.argumentError "type does not have a definite number of fields"))
  let some dt := ops.asDatatype t | throw (.foreignError "TypeError" "fieldcount expected DataType")
  let some count ← datatypeFieldcount ops dt |
    throw (.jl (.argumentError "type does not have a definite number of fields"))
  pure count

/--
Julia source: base/runtime_internals.jl:1330-1334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldindex_maythrow(T::DataType, name::Symbol)
    @_foldable_meta
    @noinline
    return Int(ccall(:jl_field_index, Cint, (Any, Any, Cint), T, name, true)+1)
end
```
-/
def fieldindexMaythrow {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : D) (name : Sym) : M World I := do pure (i (← ops.nativeFieldIndex t name true).val + i 1)

/--
Julia source: base/runtime_internals.jl:1336-1340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldindex_nothrow(T::DataType, name::Symbol)
    @_total_meta
    @noinline
    return Int(ccall(:jl_field_index, Cint, (Any, Any, Cint), T, name, false)+1)
end
```
-/
def fieldindexNothrow {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : D) (name : Sym) : M World I := do pure (i (← ops.nativeFieldIndex t name false).val + i 1)

/--
Julia source: base/runtime_internals.jl:1326-1328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fieldindex(T::DataType, name::Symbol, err::Bool=true)
    return err ? _fieldindex_maythrow(T, name) : _fieldindex_nothrow(T, name)
end
```
-/
def fieldindexDataType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : D) (name : Sym) (error : Bool := true) : M World I :=
  if error then fieldindexMaythrow ops t name else fieldindexNothrow ops t name

/--
Julia source: base/runtime_internals.jl:1411-1424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldindex_error_type(@nospecialize(t))
    t = unwrap_unionall(t)
    if t isa DataType
        fieldcount_noerror(t) === nothing && return nothing
        return t
    elseif t isa Union
        tn = _typename_noerror(t)
        tn === nothing && return nothing
        t = unwrap_unionall(tn.wrapper)
        t isa DataType || return nothing
        return t
    end
    return nothing
end
```
-/
def fieldindexErrorType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V)
    : M World (Option D) := do
  let t := ops.unwrap t
  if let some dt := ops.asDatatype t then
    if (← fieldcountNoerror ops t).isNone then return none
    pure (some dt)
  else if (ops.asUnion t).isSome then
    let some tn ← typenameNoerror ops t | return none
    pure (ops.asDatatype (ops.unwrap (ops.wrapper tn)))
  else pure none

/--
Julia source: base/runtime_internals.jl:1426-1438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldindex_noerror(@nospecialize(t), name::Symbol)
    t = unwrap_unionall(t)
    if t isa Union
        _typename_noerror(t) === nothing && return nothing
        aidx = _fieldindex_noerror(t.a, name)
        aidx === nothing && return nothing
        bidx = _fieldindex_noerror(t.b, name)
        return aidx === bidx ? aidx : nothing
    elseif t isa DataType
        return fieldindex(t, name, false)
    end
    return nothing
end
```
-/
def fieldindexNoerror {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) (name : Sym)
    : M World (Option I) := fun world => do
  let t := ops.unwrap t
  if let some (a, b) := ops.asUnion t then
    match ← typenameNoerror ops t world with
    | .error error => pure (.error error)
    | .ok (none, world) => pure (.ok (none, world))
    | .ok (some _, world) =>
      match ← fieldindexNoerror ops a name world with
      | .error error => pure (.error error)
      | .ok (none, world) => pure (.ok (none, world))
      | .ok (some aidx, world) =>
        match ← fieldindexNoerror ops b name world with
        | .error error => pure (.error error)
        | .ok (bidx, world) => pure (.ok (if bidx == some aidx then some aidx else none, world))
  else if let some dt := ops.asDatatype t then
    match ← fieldindexDataType ops dt name false world with
    | .error error => pure (.error error)
    | .ok (index, world) => pure (.ok (some index, world))
  else pure (.ok (none, world))
partial_fixpoint

/--
Julia source: base/runtime_internals.jl:1350-1362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldindex(@nospecialize(t), name::Symbol, err::Bool)
    idx = _fieldindex_noerror(t, name)
    if idx === nothing
        err && throw(ArgumentError("type does not have definite fields"))
        return 0
    end
    if idx == 0 && err
        t = _fieldindex_error_type(t)
        t === nothing && throw(ArgumentError("type does not have definite fields"))
        return fieldindex(t, name, true)
    end
    return idx
end
```
-/
def internalFieldindex {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : V) (name : Sym) (error : Bool) : M World I := do
  let idx ← fieldindexNoerror ops t name
  match idx with
  | none =>
    if error then throw (.jl (.argumentError "type does not have definite fields"))
    pure (i 0)
  | some idx =>
    if idx.val == 0 && error then
      let some dt ← fieldindexErrorType ops t | throw (.jl (.argumentError "type does not have definite fields"))
      return ← fieldindexDataType ops dt name true
    pure idx

/--
Julia source: base/runtime_internals.jl:1342-1344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fieldindex(t::UnionAll, name::Symbol, err::Bool=true)
    return _fieldindex(t, name, err)
end
```
-/
def fieldindexUnionall {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : V) (name : Sym) (error : Bool := true) : M World I := internalFieldindex ops t name error

/--
Julia source: base/runtime_internals.jl:1346-1348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fieldindex(t::Union, name::Symbol, err::Bool=true)
    return _fieldindex(t, name, err)
end
```
-/
def fieldindexUnion {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : V) (name : Sym) (error : Bool := true) : M World I := internalFieldindex ops t name error

/-- Dispatch for the `fieldindex` overloads at runtime_internals.jl:1326-1348.
`asDatatype` and `asUnion` are the installed runtime type descriptors.
A UnionAll differs from its fully unwrapped body; other runtime kinds, including
TypeofBottom, have no matching method. -/
-- Source: base/runtime_internals.jl:1326-1348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fieldindex(T::DataType, name::Symbol, err::Bool=true)
-- fieldindex(t::UnionAll, name::Symbol, err::Bool=true)
-- fieldindex(t::Union, name::Symbol, err::Bool=true)
def fieldindexDispatch {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : V) (name : Sym) (error : Bool := true) : M World I :=
  if let some dt := ops.asDatatype t then fieldindexDataType ops dt name error
  else if (ops.asUnion t).isSome then fieldindexUnion ops t name error
  else if !ops.egal (ops.unwrap t) t then fieldindexUnionall ops t name error
  else throw (.jl (.methodError "fieldindex"))

/--
Julia source: base/runtime_internals.jl:435-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldnames(t::DataType) = (fieldcount(t); # error check to make sure type is specific enough
                           (_fieldnames(t)...,))::Tuple{Vararg{Symbol}}
```
-/
def fieldnamesDataType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : D)
    : M World (List Sym) := do
  let _ ← fieldcount ops (ops.datatypeValue t)
  internalFieldnames ops t

/--
Julia source: base/runtime_internals.jl:437-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldnames(t::UnionAll) = fieldnames(unwrap_unionall(t))
```
-/
def fieldnamesUnionall {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (fieldnames : V → M World (List Sym)) (t : V) : M World (List Sym) := fieldnames (ops.unwrap t)

/--
Julia source: base/runtime_internals.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldnames(t::Core.TypeEgal) = fieldnames(typeof(type_parameter(t)))
```
-/
def fieldnamesEgal {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : V) : M World (List Sym) := do fieldnamesDataType ops (ops.typeof (← ops.typeParameter t))

/--
Julia source: base/runtime_internals.jl:439-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldnames(::TypeEq) = throw(ArgumentError("type does not have a definite number of fields"))
```
-/
def fieldnamesTypeEq {World Result : Type} : M World Result := throw (.jl (.argumentError "type does not have a definite number of fields"))

/--
Julia source: base/runtime_internals.jl:440-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldnames(::Core.TypeofBottom) =
    throw(ArgumentError("The empty type does not have field names since it does not have instances."))
```
-/
def fieldnamesBottom {World Result : Type} : M World Result := throw (.jl (.argumentError "The empty type does not have field names since it does not have instances."))

/--
Julia source: base/runtime_internals.jl:442-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldnames(t::Type{<:Tuple}) = ntuple(identity, fieldcount(t))
```
-/
def fieldnamesTuple {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V)
    : M World (List I) := do pure ((List.range (← fieldcount ops t).val.toNat).map (fun (n : Nat) => i (Int.ofNat n) + i 1))

/--
Julia source: base/runtime_internals.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    throw_not_def_field() = throw(ArgumentError("type does not have definite field names"))
```
-/
def throwNotDefiniteField {World Result : Type} : M World Result :=
  throw (.jl (.argumentError "type does not have definite field names"))

/--
Julia source: base/runtime_internals.jl:393-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function throw_field_access(t, i, n_fields)
        field_label = n_fields == 1 ? "field" : "fields"
        throw(ArgumentError("Cannot access field $i since type $t only has $n_fields $field_label."))
    end
```
-/
def throwFieldAccess {World T Index Result : Type} (_t : T) (_index : Index) (_nfields : I) : M World Result :=
  throw (.jl (.argumentError "Cannot access field since type has too few fields."))

/--
Julia source: base/runtime_internals.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    throw_need_pos_int(i) = throw(ArgumentError("Field numbers must be positive integers. $i is invalid."))
```
-/
def throwNeedPositiveInteger {World Index Result : Type} (_index : Index) : M World Result :=
  throw (.jl (.argumentError "Field numbers must be positive integers."))

/--
Julia source: base/runtime_internals.jl:391-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fieldname(t::DataType, i::Integer)
    throw_not_def_field() = throw(ArgumentError("type does not have definite field names"))
    function throw_field_access(t, i, n_fields)
        field_label = n_fields == 1 ? "field" : "fields"
        throw(ArgumentError("Cannot access field $i since type $t only has $n_fields $field_label."))
    end
    throw_need_pos_int(i) = throw(ArgumentError("Field numbers must be positive integers. $i is invalid."))

    isabstracttype(t) && throw_not_def_field()
    names = _fieldnames(t)
    n_fields = length(names)::Int
    i > n_fields && throw_field_access(t, i, n_fields)
    i < 1 && throw_need_pos_int(i)
    return @inbounds names[i]::Symbol
end
```
-/
def fieldnameDataType {World V D N Mod P Sym Index : Type} (ops : TypeOps World V D N Mod P Sym)
    (greaterThanCount : Index → I → M World Bool) (lessThanOne : Index → M World Bool)
    (indexNames : List Sym → Index → M World Sym) (t : D) (index : Index) : M World Sym := do
  if isabstracttype ops (ops.datatypeValue t) then return ← throwNotDefiniteField
  let names ← internalFieldnames ops t
  let nfields := i names.length
  if ← greaterThanCount index nfields then return ← throwFieldAccess t index nfields
  if ← lessThanOne index then return ← throwNeedPositiveInteger index
  indexNames names index

/--
Julia source: base/runtime_internals.jl:407-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldname(t::UnionAll, i::Integer) = fieldname(unwrap_unionall(t), i)
```
-/
def fieldnameUnionall {World V Index Sym : Type} (unwrap : V → V)
    (fieldname : V → Index → M World Sym) (t : V) (index : Index) : M World Sym := fieldname (unwrap t) index

/--
Julia source: base/runtime_internals.jl:408-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldname(t::Core.TypeEgal, i::Integer) = fieldname(typeof(type_parameter(t)), i)
```
-/
def fieldnameEgal {World V D N Mod P Sym Index : Type} (ops : TypeOps World V D N Mod P Sym)
    (fieldname : D → Index → M World Sym) (t : V) (index : Index) : M World Sym := do
  fieldname (ops.typeof (← ops.typeParameter t)) index

/--
Julia source: base/runtime_internals.jl:409-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldname(::TypeEq, ::Integer) = throw(ArgumentError("type does not have definite field names"))
```
-/
def fieldnameTypeEq {World Index Result : Type} (_index : Index) : M World Result := throwNotDefiniteField

/--
Julia source: base/runtime_internals.jl:410-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldname(t::Type{<:Tuple}, i::Integer) =
    i < 1 || i > fieldcount(t) ? throw(BoundsError(t, i)) : Int(i)
```
-/
def fieldnameTuple {World V Index : Type} (lessOne : Index → M World Bool)
    (fieldcount : V → M World I) (greater : Index → I → M World Bool) (toInt : Index → M World I)
    (t : V) (index : Index) : M World I := do
  if ← lessOne index then throw (.jl .boundsError)
  if ← greater index (← fieldcount t) then throw (.jl .boundsError)
  toInt index

/--
Julia source: base/runtime_internals.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasfield(T::Type, name::Symbol) = fieldindex(T, name, false) > 0
```
-/
def hasfield {World V Sym : Type} (fieldindex : V → Sym → Bool → M World I) (t : V) (name : Sym) : M World Bool := do
  pure ((← fieldindex t name false).val > 0)

/--
Julia source: base/runtime_internals.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nameof(t::DataType) = t.name.name
```
-/
def nameofDataType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : D) : Sym :=
  ops.name (ops.nameOf t)

/--
Julia source: base/runtime_internals.jl:488-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nameof(t::UnionAll) = nameof(unwrap_unionall(t))::Symbol
```
-/
def nameofUnionall {World V Sym : Type} (unwrap : V → V)
    (nameof : V → M World Sym) (t : V) : M World Sym := nameof (unwrap t)

/--
Julia source: base/runtime_internals.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentmodule(t::DataType) = t.name.module
```
-/
def parentmoduleDataType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : D) : Mod :=
  ops.module (ops.nameOf t)

/--
Julia source: base/runtime_internals.jl:510-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentmodule(t::UnionAll) = parentmodule(unwrap_unionall(t))
```
-/
def parentmoduleUnionall {World V Mod : Type} (unwrap : V → V)
    (parentmodule : V → M World Mod) (t : V) : M World Mod := parentmodule (unwrap t)

/--
Julia source: base/runtime_internals.jl:522-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isconst(m::Module, s::Symbol) =
    ccall(:jl_is_const, Cint, (Any, Any), m, s) != 0
```
-/
def isconstGlobal {World Module Sym : Type} (jlIsConst : Module → Sym → M World Cint)
    (m : Module) (s : Sym) : M World Bool := do pure ((← jlIsConst m s).val != 0)

/--
Julia source: base/runtime_internals.jl:525-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isconst(g::GlobalRef)
    return ccall(:jl_globalref_is_const, Cint, (Any,), g) != 0
end
```
-/
def isconstGlobalRef {World GlobalRef : Type} (jlIsConst : GlobalRef → M World Cint)
    (g : GlobalRef) : M World Bool := do pure ((← jlIsConst g).val != 0)

/--
Julia source: base/runtime_internals.jl:544-557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isconst(@nospecialize(t::Type), s::Int)
    @_foldable_meta
    t = unwrap_unionall(t)
    # TODO: what to do for `Union`?
    isa(t, DataType) || return false # uncertain
    ismutabletype(t) || return true # immutable structs are always const
    1 <= s <= length(t.name.names) || return true # OOB reads are "const" since they always throw
    constfields = t.name.constfields
    constfields === C_NULL && return false
    s -= 1
    return unsafe_load(Ptr{UInt32}(constfields), 1 + s÷32) & (1 << (s%32)) != 0
end

"""
```
-/
def isconstIndex {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) (index : I) : M World Bool := do
  let t := ops.unwrap t
  let some dt := ops.asDatatype t | return false
  if !ismutabletype ops t then return true
  if !(i 1 ≤ index && index.val ≤ (ops.names (ops.nameOf dt)).length) then return true
  let fields := ops.constFields (ops.nameOf dt)
  if ops.isNull fields then return false
  let index := index - i 1
  let word ← ops.loadUInt32 fields (i 1 + i (index.val / 32))
  pure ((BitVec.ofInt 32 word.val &&& (BitVec.ofNat 32 1 <<< (index.val % 32).toNat)).toNat != 0)

/--
Julia source: base/runtime_internals.jl:568-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isfieldatomic(@nospecialize(t::Type), s::Int)
    @_foldable_meta
    t = unwrap_unionall(t)
    # TODO: what to do for `Union`?
    isa(t, DataType) || return false # uncertain
    ismutabletype(t) || return false # immutable structs are never atomic
    1 <= s <= length(t.name.names) || return false # OOB reads are not atomic (they always throw)
    atomicfields = t.name.atomicfields
    atomicfields === C_NULL && return false
    s -= 1
    return unsafe_load(Ptr{UInt32}(atomicfields), 1 + s÷32) & (1 << (s%32)) != 0
end

"""
```
-/
def isfieldatomicIndex {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) (index : I) : M World Bool := do
  let t := ops.unwrap t
  let some dt := ops.asDatatype t | return false
  if !ismutabletype ops t then return false
  if !(i 1 ≤ index && index.val ≤ (ops.names (ops.nameOf dt)).length) then return false
  let fields := ops.atomicFields (ops.nameOf dt)
  if ops.isNull fields then return false
  let index := index - i 1
  let word ← ops.loadUInt32 fields (i 1 + i (index.val / 32))
  pure ((BitVec.ofInt 32 word.val &&& (BitVec.ofNat 32 1 <<< (index.val % 32).toNat)).toNat != 0)

/--
Julia source: base/runtime_internals.jl:538-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isconst(@nospecialize(t::Type), s::Symbol)
    @_foldable_meta
    t = unwrap_unionall(t)
    isa(t, DataType) || return false
    return isconst(t, fieldindex(t, s, false))
end
```
-/
def isconstSymbol {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : V) (symbol : Sym) : M World Bool := do
  let t := ops.unwrap t
  let some dt := ops.asDatatype t | return false
  isconstIndex ops t (← fieldindexDataType ops dt symbol false)

/--
Julia source: base/runtime_internals.jl:562-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isfieldatomic(@nospecialize(t::Type), s::Symbol)
    @_foldable_meta
    t = unwrap_unionall(t)
    isa(t, DataType) || return false
    return isfieldatomic(t, fieldindex(t, s, false))
end
```
-/
def isfieldatomicSymbol {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (t : V) (symbol : Sym) : M World Bool := do
  let t := ops.unwrap t
  let some dt := ops.asDatatype t | return false
  isfieldatomicIndex ops t (← fieldindexDataType ops dt symbol false)

/--
Julia source: base/runtime_internals.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
datatype_fieldtypes(x::DataType) = ccall(:jl_get_fieldtypes, Core.SimpleVector, (Any,), x)
```
-/
def datatypeFieldtypes {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (x : D)
    : M World (List V) := ops.fieldtypes x

/--
Julia source: base/runtime_internals.jl:1223-1223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typeintersect(@nospecialize(a), @nospecialize(b)) = (@_total_meta; ccall(:jl_type_intersection, Any, (Any, Any), a::Type, b::Type))
```
-/
def typeintersect {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (a b : V) : M World V := do
  let a ← ops.assertType a
  let b ← ops.assertType b
  ops.typeintersect a b

/--
Julia source: base/runtime_internals.jl:1225-1225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
morespecific(@nospecialize(a), @nospecialize(b)) = (@_total_meta; ccall(:jl_type_morespecific, Cint, (Any, Any), a::Type, b::Type) != 0)
```
-/
def morespecificTypes {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (a b : V) : M World Bool := do
  let a ← ops.assertType a
  let b ← ops.assertType b
  pure ((← ops.morespecific a b).val != 0)

/--
Julia source: base/runtime_internals.jl:1226-1226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
morespecific(a::Method, b::Method) = ccall(:jl_method_morespecific, Cint, (Any, Any), a, b) != 0
```
-/
def morespecificMethods {World Method : Type} (native : Method → Method → M World Cint) (a b : Method)
    : M World Bool := do pure ((← native a b).val != 0)

/--
Julia source: base/runtime_internals.jl:1273-1273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldoffset(x::DataType, idx::Integer) = (@_foldable_meta; ccall(:jl_get_field_offset, Csize_t, (Any, Cint), x, idx))
```
-/
def fieldoffsetIndex {World D Index : Type} (native : D → Index → M World U) (x : D) (index : Index) : M World U :=
  native x index

/--
Julia source: base/runtime_internals.jl:1274-1274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldoffset(x::DataType, name::Symbol) = fieldoffset(x, fieldindex(x, name))
```
-/
def fieldoffsetName {World D Sym : Type} (fieldindex : D → Sym → M World I)
    (fieldoffset : D → I → M World U) (x : D) (name : Sym) : M World U := do fieldoffset x (← fieldindex x name)

/--
Julia source: base/runtime_internals.jl:1275-1275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldoffset(x::Core.TypeEgal, idx::Union{Integer,Symbol}) = fieldoffset(typeof(type_parameter(x)), idx)
```
-/
def fieldoffsetEgal {World V D N Mod P Sym Index : Type} (ops : TypeOps World V D N Mod P Sym)
    (fieldoffset : D → Index → M World U) (x : V) (index : Index) : M World U := do
  fieldoffset (ops.typeof (← ops.typeParameter x)) index

/--
Julia source: base/runtime_internals.jl:1513-1513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldtypes(@nospecialize T::Type) = (@_foldable_meta; ntupleany(i -> fieldtype(T, i), fieldcount(T)))
```
-/
def fieldtypes {World V : Type} (fieldcount : V → M World I) (fieldtype : V → I → M World V)
    (t : V) : M World (List V) := do
  let count ← fieldcount t
  (List.range count.val.toNat).mapM (fun (n : Nat) => fieldtype t (i (Int.ofNat n) + i 1))

/--
Julia source: base/runtime_internals.jl:1514-1514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fieldtypes(T::Core.TypeEgal) = fieldtypes(typeof(type_parameter(T)))
```
-/
def fieldtypesEgal {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (fieldtypes : D → M World (List V)) (t : V) : M World (List V) := do
  fieldtypes (ops.typeof (← ops.typeParameter t))

/--
Julia source: base/runtime_internals.jl:1534-1552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function to_tuple_type(@nospecialize(t))
    @_terminates_locally_meta
    if isa(t, Tuple) || isa(t, AbstractArray) || isa(t, SimpleVector)
        t = Tuple{t...}
    end
    if isa(t, Type) && t <: Tuple
        for p in (unwrap_unionall(t)::DataType).parameters
            if isa(p, Core.TypeofVararg)
                p = unwrapva(p)
            end
            if !(isa(p, Core.AnyType) || isa(p, TypeVar))
                error("argument tuple type must contain only types")
            end
        end
    else
        error("expected tuple type")
    end
    t
end
```
-/
def toTupleType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (t : V) : M World V := do
  let t ← match ops.asTypeCollection t with | none => pure t | some types => ops.tupleType types
  if ops.isAType t && ops.isTuple t then
    let some dt := ops.asDatatype (ops.unwrap t) | throw (.foreignError "TypeError" "expected DataType")
    for parameter in ← ops.parameters dt do
      let parameter := if ops.isVararg parameter then ops.unwrapVararg parameter else parameter
      if !(ops.isAType parameter || ops.isTypeVar parameter) then
        throw (.errorException "argument tuple type must contain only types")
  else throw (.errorException "expected tuple type")
  pure t

/--
Julia source: base/runtime_internals.jl:1554-1561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function signature_type(@nospecialize(f), @nospecialize(argtypes))
    argtypes = to_tuple_type(argtypes)
    # `Core.Typeof` matches the per-argument key of the dispatch tuple
    # constructed by `jl_inst_arg_tuple_type`.
    ft = Core.Typeof(f)
    u = unwrap_unionall(argtypes)::DataType
    return rewrap_unionall(Tuple{ft, u.parameters...}, argtypes)
end
```
-/
def signatureType {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (f argtypes : V) : M World V := do
  let argtypes ← toTupleType ops argtypes
  let ft ← ops.coreTypeof f
  let some unwrapped := ops.asDatatype (ops.unwrap argtypes) | throw (.foreignError "TypeError" "expected DataType")
  let constructed ← ops.tupleType (ft :: (← ops.parameters unwrapped))
  ops.rewrapUnionall constructed argtypes

/--
Julia source: base/runtime_internals.jl:1653-1653 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_world_counter() = ccall(:jl_get_world_counter, UInt, ())
```
-/
def getWorldCounter {World : Type} (jlGetWorldCounter : M World U) : M World U := jlGetWorldCounter

/--
Julia source: base/runtime_internals.jl:1660-1660 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tls_world_age() = ccall(:jl_get_tls_world_age, UInt, ())
```
-/
def tlsWorldAge {World : Type} (jlGetTlsWorldAge : M World U) : M World U := jlGetTlsWorldAge

/--
Julia source: base/runtime_internals.jl:1679-1679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
propertynames(x) = fieldnames(typeof(x))
```
-/
def propertynames {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (fieldnames : D → M World (List Sym)) (x : V) : M World (List Sym) := fieldnames (ops.typeof x)

/--
Julia source: base/runtime_internals.jl:1680-1680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
propertynames(m::Module) = names(m)
```
-/
def propertynamesModule {World Mod Sym : Type} (names : Mod → M World (List Sym)) (m : Mod)
    : M World (List Sym) := names m

/--
Julia source: base/runtime_internals.jl:1681-1681 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
propertynames(x, private::Bool) = propertynames(x) # ignore private flag by default
```
-/
def propertynamesPrivate {World V Result : Type} (propertynames : V → M World Result)
    (x : V) (_private : Bool) : M World Result := propertynames x

/--
Julia source: base/runtime_internals.jl:1682-1682 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
propertynames(x::Array) = () # hide the fields from tab completion to discourage calling `x.size` instead of `size(x)`, even though they are equivalent
```
-/
def propertynamesArray {Array Sym : Type} (_x : Array) : List Sym := []

/--
Julia source: base/runtime_internals.jl:1694-1694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasproperty(x, s::Symbol) = s in propertynames(x)
```
-/
def hasproperty {World V Sym Properties : Type} (propertynames : V → M World Properties)
    (contains : Sym → Properties → M World Bool) (x : V) (s : Sym) : M World Bool := do
  contains s (← propertynames x)

/--
Julia source: base/runtime_internals.jl:1701-1703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function delete_method(m::Method)
    ccall(:jl_method_table_disable, Cvoid, (Any,), m)
end
```
-/
def deleteMethod {World Method : Type} (jlDisable : Method → M World Unit) (m : Method) : M World Unit := jlDisable m

/--
Julia source: base/runtime_internals.jl:1707-1710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct MethodList <: AbstractArray{Method,1}
    ms::Array{Method,1}
    tn::Core.TypeName # contains module.singletonname globalref for altering some aspects of printing
end
```
-/
structure MethodList (Method Name : Type) where
  ms : List Method
  tn : Name

/--
Julia source: base/runtime_internals.jl:1712-1712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(m::MethodList) = size(m.ms)
```
-/
def methodListSize {Method Name : Type} (m : MethodList Method Name) : List I := [i m.ms.length]

/--
Julia source: base/runtime_internals.jl:1713-1713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(m::MethodList, i::Integer) = m.ms[i]
```
-/
def methodListGetindex {World Method Name Index : Type} (getindex : List Method → Index → M World Method)
    (m : MethodList Method Name) (index : Index) : M World Method := getindex m.ms index

/--
Julia source: base/runtime_internals.jl:1715-1721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function MethodList(mt::Core.MethodTable)
    ms = Method[]
    visit(mt) do m
        push!(ms, m)
    end
    return MethodList(ms, Any.name)
end
```
-/
def methodListFromTable {World Method Name Table Ref : Type} (newVector : M World Ref)
    (push : Ref → Method → M World Unit) (read : Ref → M World (List Method))
    (visit : Table → (Method → M World Unit) → M World Unit) (anyName : Name) (mt : Table)
    : M World (MethodList Method Name) := do
  let ms ← newVector
  visit mt (fun m => push ms m)
  pure ⟨← read ms, anyName⟩

/--
Julia source: base/runtime_internals.jl:1723-1731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function matches_to_methods(ms::Array{Any,1}, tn::Core.TypeName, mod)
    # Lack of specialization => a comprehension triggers too many invalidations via _collect, so collect the methods manually
    ms = Method[(ms[i]::Core.MethodMatch).method for i in 1:length(ms)]
    # Remove methods not part of module
    mod === nothing || filter!(ms) do m
        return parentmodule(m) ∈ mod
    end
    return MethodList(ms, tn)
end
```
-/
def matchesToMethods {World Match Method Name Mod ModuleSet : Type}
    (matchMethod : Match → M World Method) (parentmodule : Method → M World Mod)
    (contains : Mod → ModuleSet → M World Bool) (ms : List Match) (tn : Name) (mod : Option ModuleSet)
    : M World (MethodList Method Name) := do
  let methods ← ms.mapM matchMethod
  let methods ← match mod with
    | none => pure methods
    | some modules => methods.filterM (fun method => do contains (← parentmodule method) modules)
  pure ⟨methods, tn⟩

/--
Julia source: base/runtime_internals.jl:1751-1757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function methods(@nospecialize(f), @nospecialize(t),
                 mod::Union{Tuple{Module},AbstractArray{Module},AbstractSet{Module},Nothing}=nothing)
    world = get_world_counter()
    world == typemax(UInt) && error("code reflection cannot be used from generated functions")
    ms = _methods(f, t, -1, world)::Vector{Any}
    return matches_to_methods(ms, typeof(f).name, mod)
end
```
-/
def methodsTyped {World V D N Mod P Sym Match Method ModuleSet : Type}
    (ops : TypeOps World V D N Mod P Sym) (getWorldCounter : M World U)
    (methods : V → V → I → U → M World (List Match))
    (matchMethod : Match → M World Method) (parentmodule : Method → M World Mod)
    (contains : Mod → ModuleSet → M World Bool) (f t : V) (mod : Option ModuleSet := none)
    : M World (MethodList Method N) := do
  let world ← getWorldCounter
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  let ms ← methods f t (i (-1)) world
  matchesToMethods matchMethod parentmodule contains ms (ops.nameOf (ops.typeof f)) mod

/--
Julia source: base/runtime_internals.jl:1758-1758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
methods(@nospecialize(f), @nospecialize(t), mod::Module) = methods(f, t, (mod,))
```
-/
def methodsModule {World V Mod ModuleSet Result : Type} (singleton : Mod → ModuleSet)
    (methods : V → V → Option ModuleSet → M World Result) (f t : V) (mod : Mod) : M World Result :=
  methods f t (some (singleton mod))

/--
Julia source: base/runtime_internals.jl:1760-1768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function methods_including_ambiguous(@nospecialize(f), @nospecialize(t))
    tt = signature_type(f, t)
    world = get_world_counter()
    world == typemax(UInt) && error("code reflection cannot be used from generated functions")
    min = RefValue{UInt}(typemin(UInt))
    max = RefValue{UInt}(typemax(UInt))
    ms = _methods_by_ftype(tt, nothing, -1, world, true, min, max, Ptr{Int32}(C_NULL))::Vector{Any}
    return matches_to_methods(ms, typeof(f).name, nothing)
end
```
-/
def methodsIncludingAmbiguous {World V D N Mod P Sym Match Method ModuleSet Ref Pointer : Type}
    (ops : TypeOps World V D N Mod P Sym) (getWorldCounter : M World U)
    (newRef : U → M World Ref) (nullPointer : Pointer)
    (methodsByType : V → I → U → Bool → Ref → Ref → Pointer → M World (List Match))
    (matchMethod : Match → M World Method) (parentmodule : Method → M World Mod)
    (contains : Mod → ModuleSet → M World Bool) (f t : V) : M World (MethodList Method N) := do
  let tt ← signatureType ops f t
  let world ← getWorldCounter
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  let minWorld ← newRef (JInt.typemin .u64)
  let maxWorld ← newRef (JInt.typemax .u64)
  let ms ← methodsByType tt (i (-1)) world true minWorld maxWorld nullPointer
  matchesToMethods matchMethod parentmodule contains ms (ops.nameOf (ops.typeof f)) none

/--
Julia source: base/runtime_internals.jl:1770-1774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function methods(@nospecialize(f),
                 mod::Union{Module,AbstractArray{Module},AbstractSet{Module},Nothing}=nothing)
    # return all matches
    return methods(f, Tuple{Vararg{Any}}, mod)
end
```
-/
def methodsAll {World V ModuleSet Result : Type} (tupleVarargAny : V)
    (methods : V → V → Option ModuleSet → M World Result) (f : V) (mod : Option ModuleSet := none) : M World Result :=
  methods f tupleVarargAny mod

/--
Julia source: base/runtime_internals.jl:1841-1847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function generating_output(incremental::Union{Bool,Nothing}=nothing)
    ccall(:jl_generating_output, Cint, ()) == 0 && return false
    if incremental !== nothing
        JLOptions().incremental == incremental || return false
    end
    return true
end
```
-/
def generatingOutput {World : Type} (jlGeneratingOutput : M World Cint)
    (optionsIncremental : M World Bool) (incremental : Option Bool := none) : M World Bool := do
  if (← jlGeneratingOutput).val == 0 then return false
  if let some incremental := incremental then
    if (← optionsIncremental) != incremental then return false
  pure true

/--
Julia source: base/runtime_internals.jl:1999-1999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasintersect(@nospecialize(a), @nospecialize(b)) = typeintersect(a, b) !== Bottom
```
-/
def hasintersect {World V : Type} (typeintersect : V → V → M World V) (isBottom : V → Bool)
    (a b : V) : M World Bool := do pure (!isBottom (← typeintersect a b))

/--
Julia source: base/runtime_internals.jl:2080-2086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(mt::Core.MethodTable)
    n = Ref(0)
    visit(mt) do m
        n[] += 1
    end
    return n[]
end
```
-/
def methodTableLength {World Table Method Ref : Type} (newCounter : I → M World Ref)
    (get : Ref → M World I) (set : Ref → I → M World Unit)
    (visit : Table → (Method → M World Unit) → M World Unit) (mt : Table) : M World I := do
  let n ← newCounter (i 0)
  visit mt (fun _ => do set n ((← get n) + i 1))
  get n

/--
Julia source: base/runtime_internals.jl:2087-2087 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(mt::Core.MethodTable) = (mt.defs === nothing)
```
-/
def methodTableIsempty {Table Defs : Type} (defs : Table → Option Defs) (mt : Table) : Bool := (defs mt).isNone


/-! ## Runtime-query and type-structure helpers -/

structure BindingOps (World Module Sym GlobalRef Binding Partition Value : Type) where
  globalRef : Module → Sym → M World GlobalRef
  hasBinding : GlobalRef → M World Bool
  cachedBinding : GlobalRef → M World Binding
  module : GlobalRef → Module
  name : GlobalRef → Sym
  getBinding : Module → Sym → Cint → M World Binding
  partition : Binding → U → M World Partition
  partitionHint : Binding → Partition → U → M World Partition
  restriction : Partition → M World Value
  next : Partition → M World (Sum Partition Binding)
  kind : Partition → U
  tlsWorldAge : M World U

structure LookupOps (World V Table Ref Pointer Match : Type) where
  newWorldRef : U → M World Ref
  nullAmbiguousPointer : Pointer
  matching : V → Option Table → Cint → Cint → U → Ref → Ref → Pointer → M World (Option (List Match))

def bottomParameterWorker {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (isUnionall : V → Bool) (upperBound : V → M World V) (query : Sum V (List V)) : M World Bool := fun world => do
  match query with
  | .inr [] => pure (.ok (false, world))
  | .inr (first :: rest) =>
    match ← bottomParameterWorker ops isUnionall upperBound (.inl first) world with
    | .error error => pure (.error error)
    | .ok (true, world) => pure (.ok (true, world))
    | .ok (false, world) => bottomParameterWorker ops isUnionall upperBound (.inr rest) world
  | .inl t =>
    if ops.egal t ops.bottom then return .ok (true, world)
    if let some dt := ops.asDatatype t then
      match ← ops.parameters dt world with
      | .error error => pure (.error error)
      | .ok (parameters, world) => bottomParameterWorker ops isUnionall upperBound (.inr parameters) world
    else if isType ops t then
      match ← ops.typeParameter t world with
      | .error error => pure (.error error)
      | .ok (parameter, world) => bottomParameterWorker ops isUnionall upperBound (.inl parameter) world
    else if isUnionall t then bottomParameterWorker ops isUnionall upperBound (.inl (ops.unwrap t)) world
    else if let some (a, b) := ops.asUnion t then
      match ← bottomParameterWorker ops isUnionall upperBound (.inl a) world with
      | .error error => pure (.error error)
      | .ok (left, world) =>
        match ← bottomParameterWorker ops isUnionall upperBound (.inl b) world with
        | .error error => pure (.error error)
        | .ok (right, world) => pure (.ok (left && right, world))
    else if ops.isTypeVar t then
      match ← upperBound t world with
      | .error error => pure (.error error)
      | .ok (upper, world) => bottomParameterWorker ops isUnionall upperBound (.inl upper) world
    else pure (.ok (false, world))
partial_fixpoint

/--
Julia source: base/runtime_internals.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_defined_const_binding(kind::UInt8) = (kind == PARTITION_KIND_CONST || kind == PARTITION_KIND_CONST_IMPORT || kind == PARTITION_KIND_IMPLICIT_CONST || kind == PARTITION_KIND_BACKDATED_CONST)
```
-/
def isDefinedConstBinding (kind : U8) : Bool := kind.val == 0 || kind.val == 1 || kind.val == 4 || kind.val == 11

/--
Julia source: base/runtime_internals.jl:276-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_some_const_binding(kind::UInt8) = (is_defined_const_binding(kind) || kind == PARTITION_KIND_UNDEF_CONST)
```
-/
def isSomeConstBinding (kind : U8) : Bool := isDefinedConstBinding kind || kind.val == 10

/--
Julia source: base/runtime_internals.jl:277-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_some_imported(kind::UInt8) = (kind == PARTITION_KIND_IMPLICIT_GLOBAL || kind == PARTITION_KIND_IMPLICIT_CONST || kind == PARTITION_KIND_EXPLICIT || kind == PARTITION_KIND_IMPORTED)
```
-/
def isSomeImported (kind : U8) : Bool := kind.val == 3 || kind.val == 4 || kind.val == 5 || kind.val == 6

/--
Julia source: base/runtime_internals.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_some_implicit(kind::UInt8) = (kind == PARTITION_KIND_IMPLICIT_GLOBAL || kind == PARTITION_KIND_IMPLICIT_CONST || kind == PARTITION_KIND_GUARD || kind == PARTITION_KIND_FAILED)
```
-/
def isSomeImplicit (kind : U8) : Bool := kind.val == 3 || kind.val == 4 || kind.val == 9 || kind.val == 7

/--
Julia source: base/runtime_internals.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_some_explicit_imported(kind::UInt8) = (kind == PARTITION_KIND_EXPLICIT || kind == PARTITION_KIND_IMPORTED)
```
-/
def isSomeExplicitImported (kind : U8) : Bool := kind.val == 5 || kind.val == 6

/--
Julia source: base/runtime_internals.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_some_binding_imported(kind::UInt8) = is_some_explicit_imported(kind) || kind == PARTITION_KIND_IMPLICIT_GLOBAL
```
-/
def isSomeBindingImported (kind : U8) : Bool := isSomeExplicitImported kind || kind.val == 3

/--
Julia source: base/runtime_internals.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_some_guard(kind::UInt8) = (kind == PARTITION_KIND_GUARD || kind == PARTITION_KIND_FAILED || kind == PARTITION_KIND_UNDEF_CONST)
```
-/
def isSomeGuard (kind : U8) : Bool := kind.val == 9 || kind.val == 7 || kind.val == 10

/--
Julia source: base/runtime_internals.jl:283-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_some_global(kind::UInt8) = (kind == PARTITION_KIND_GLOBAL || kind == PARTITION_KIND_DECLARED)
```
-/
def isSomeGlobal (kind : U8) : Bool := kind.val == 2 || kind.val == 8

/--
Julia source: base/runtime_internals.jl:285-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lookup_binding_partition(world::UInt, b::Core.Binding)
    ccall(:jl_get_binding_partition, Ref{Core.BindingPartition}, (Any, UInt), b, world)
end
```
-/
def lookupBindingPartition {World Mod Sym GR B Part V : Type} (ops : BindingOps World Mod Sym GR B Part V)
    (world : U) (binding : B) : M World Part := ops.partition binding world

/--
Julia source: base/runtime_internals.jl:289-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lookup_binding_partition(world::UInt, b::Core.Binding, previous_partition::Core.BindingPartition)
    ccall(:jl_get_binding_partition_with_hint, Ref{Core.BindingPartition}, (Any, Any, UInt), b, previous_partition, world)
end
```
-/
def lookupBindingPartitionHint {World Mod Sym GR B Part V : Type} (ops : BindingOps World Mod Sym GR B Part V)
    (world : U) (binding : B) (previous : Part) : M World Part := ops.partitionHint binding previous world

/--
Julia source: base/runtime_internals.jl:293-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{Core.Binding}, gr::Core.GlobalRef)
    if isdefined(gr, :binding)
        return gr.binding
    else
        return ccall(:jl_get_module_binding, Ref{Core.Binding}, (Any, Any, Cint), gr.mod, gr.name, true)
    end
end
```
-/
def convertBinding {World Mod Sym GR B Part V : Type} (ops : BindingOps World Mod Sym GR B Part V)
    (gr : GR) : M World B := do
  if ← ops.hasBinding gr then ops.cachedBinding gr
  else ops.getBinding (ops.module gr) (ops.name gr) (JInt.wrap .i32 1)

/--
Julia source: base/runtime_internals.jl:301-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lookup_binding_partition(world::UInt, gr::Core.GlobalRef)
    b = convert(Core.Binding, gr)
    return lookup_binding_partition(world, b)
end
```
-/
def lookupBindingPartitionGlobalRef {World Mod Sym GR B Part V : Type} (ops : BindingOps World Mod Sym GR B Part V)
    (world : U) (gr : GR) : M World Part := do lookupBindingPartition ops world (← convertBinding ops gr)

/--
Julia source: base/runtime_internals.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
partition_restriction(bpart::Core.BindingPartition) = ccall(:jl_bpart_get_restriction_value, Any, (Any,), bpart)
```
-/
def partitionRestriction {World Mod Sym GR B Part V : Type} (ops : BindingOps World Mod Sym GR B Part V)
    (part : Part) : M World V := ops.restriction part

/--
Julia source: base/runtime_internals.jl:311-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function partition_owner(bpart::Core.BindingPartition)
    next = bpart.next
    while next isa Core.BindingPartition
        next = next.next
    end
    return next::Core.Binding
end
```
-/
def partitionOwner {World Mod Sym GR B Part V : Type} (ops : BindingOps World Mod Sym GR B Part V)
    (part : Part) : M World B := do
  let next ← ops.next part
  whileLoop (fun next => do
    match next with
    | .inl part => pure (.inr (← ops.next part))
    | .inr binding => pure (.inl binding)) next

/--
Julia source: base/runtime_internals.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
binding_kind(bpart::Core.BindingPartition) = UInt8(bpart.kind & PARTITION_MASK_KIND)
```
-/
def bindingKindPartition {World Mod Sym GR B Part V : Type} (ops : BindingOps World Mod Sym GR B Part V)
    (part : Part) : U8 := JInt.wrap .u8 ((ops.kind part).val % 16)

/--
Julia source: base/runtime_internals.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
binding_kind(m::Module, s::Symbol) = binding_kind(lookup_binding_partition(tls_world_age(), GlobalRef(m, s)))
```
-/
def bindingKindModule {World Mod Sym GR B Part V : Type} (ops : BindingOps World Mod Sym GR B Part V)
    (mod : Mod) (sym : Sym) : M World U8 := do
  let world ← ops.tlsWorldAge
  let gr ← ops.globalRef mod sym
  pure (bindingKindPartition ops (← lookupBindingPartitionGlobalRef ops world gr))

/--
Julia source: base/runtime_internals.jl:1198-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_valid_intrinsic_elptr(@nospecialize(ety))
    ety === Any && return true
    isconcretetype(ety) || return false
    ety <: Array && return false
    return !is_datatype_layoutopaque(ety)
end
```
-/
def isValidIntrinsicElptr {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (subtypeArray : V → M World Bool) (ety : V) : M World Bool := do
  if ops.egal ety ops.any then return true
  if !isconcretetype ops ety then return false
  if ← subtypeArray ety then return false
  let some dt := ops.asDatatype ety | throw (.foreignError "MethodError" "is_datatype_layoutopaque")
  pure (!(← isDatatypeLayoutopaque ops dt))

/--
Julia source: base/runtime_internals.jl:1364-1368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function argument_datatype(@nospecialize t)
    @_total_meta
    @noinline
    return ccall(:jl_argument_datatype, Any, (Any,), t)::Union{Nothing,DataType}
end
```
-/
def argumentDatatype {World V D : Type} (jlArgumentDatatype : V → M World (Option D)) (t : V)
    : M World (Option D) := jlArgumentDatatype t

/--
Julia source: base/runtime_internals.jl:1370-1374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function argument_datatypename(@nospecialize t)
    @_total_meta
    @noinline
    return ccall(:jl_argument_datatypename, Any, (Any,), t)::Union{Nothing,Core.TypeName}
end
```
-/
def argumentDatatypename {World V N : Type} (jlArgumentDatatypename : V → M World (Option N)) (t : V)
    : M World (Option N) := jlArgumentDatatypename t

/--
Julia source: base/runtime_internals.jl:1563-1569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_methodtable(m::Method)
    mt = ccall(:jl_method_get_table, Any, (Any,), m)
    if mt === nothing
        return nothing
    end
    return mt::Core.MethodTable
end
```
-/
def getMethodtable {World Method Table : Type} (jlMethodGetTable : Method → M World (Option Table)) (m : Method)
    : M World (Option Table) := do
  let mt ← jlMethodGetTable m
  match mt with | none => pure none | some table => pure (some table)

/--
Julia source: base/runtime_internals.jl:1576-1591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function has_bottom_parameter(@nospecialize(t::Core.AnyType))
    t === Bottom && return true
    ty = typeof(t)
    if ty === DataType
        for p in getfield(t, :parameters)
            has_bottom_parameter(p) && return true
        end
    elseif ty === TypeEq || ty === Core.TypeEgal
        return has_bottom_parameter(type_parameter(t))
    elseif ty === UnionAll
        return has_bottom_parameter(unwrap_unionall(t))
    elseif ty === Union
        return has_bottom_parameter(getfield(t, :a)) & has_bottom_parameter(getfield(t, :b))
    end
    return false
end
```
-/
def hasBottomParameter {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)
    (isUnionall : V → Bool) (upperBound : V → M World V) (t : V) : M World Bool :=
  bottomParameterWorker ops isUnionall upperBound (.inl t)

/--
Julia source: base/runtime_internals.jl:1592-1592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_bottom_parameter(t::TypeVar) = has_bottom_parameter(t.ub)
```
-/
def hasBottomParameterTypevar {World V Var : Type} (getUpper : Var → M World V)
    (hasBottom : V → M World Bool) (t : Var) : M World Bool := do hasBottom (← getUpper t)

/--
Julia source: base/runtime_internals.jl:1593-1593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_bottom_parameter(::Any) = false
```
-/
def hasBottomParameterOther {Value : Type} (_t : Value) : Bool := false

/--
Julia source: base/runtime_internals.jl:1595-1597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function find_free_typevars(@nospecialize(t))
    return ccall(:jl_find_free_typevars, Array{Any, 1}, (Any,), t)
end
```
-/
def findFreeTypevars {World V : Type} (native : V → M World (List V)) (t : V) : M World (List V) := native t

/--
Julia source: base/runtime_internals.jl:1612-1629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rewrap_free_typevars(@nospecialize(t), pre=Core.svec())
    has_free_typevars(t) || return t
    # UnionAll cannot directly wrap a Vararg; the caller must wrap it in Tuple first
    isvarargtype(t) && return t
    fv = find_free_typevars(t)
    for i in length(fv):-1:1
        v = fv[i]::TypeVar
        wrap = true
        for p in pre
            if p === v
                wrap = false
                break
            end
        end
        wrap && (t = UnionAll(v, t))
    end
    return t
end
```
-/
def rewrapFreeTypevars {World V Var : Type} (hasFreeTypevars isvararg : V → Bool)
    (findFreeTypevars : V → M World (List V)) (assertTypevar : V → M World Var)
    (variableValue : Var → V) (egal : V → V → Bool) (unionAll : Var → V → M World V)
    (t : V) (pre : List V := []) : M World V := do
  if !hasFreeTypevars t then return t
  if isvararg t then return t
  let fv ← findFreeTypevars t
  let mut t := t
  for value in fv.reverse do
    let typevar ← assertTypevar value
    let mut wrap := true
    for p in pre do
      if egal p (variableValue typevar) then
        wrap := false
        break
    if wrap then t := ← unionAll typevar t
  pure t

/--
Julia source: base/runtime_internals.jl:1631-1634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typeintersect_env(@nospecialize(a), @nospecialize(b))
    (ti, env) = ccall(:jl_type_intersection_with_env, Any, (Any, Any), a, b)::SimpleVector
    Pair{Any, SimpleVector}(ti, env)
end
```
-/
def typeintersectEnv {World V Env : Type} (native : V → V → M World (V × Env)) (a b : V) : M World (V × Env) := do
  let (intersection, env) ← native a b
  pure (intersection, env)

/--
Julia source: base/runtime_internals.jl:1636-1636 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min_world(m::Core.CodeInstance) = m.min_world
```
-/
def minWorldCodeInstance {Code : Type} (getWorld : Code → U) (code : Code) : U := getWorld code

/--
Julia source: base/runtime_internals.jl:1637-1637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max_world(m::Core.CodeInstance) = m.max_world
```
-/
def maxWorldCodeInstance {Code : Type} (getWorld : Code → U) (code : Code) : U := getWorld code

/--
Julia source: base/runtime_internals.jl:1638-1638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min_world(m::Core.CodeInfo) = m.min_world
```
-/
def minWorldCodeInfo {Code : Type} (getWorld : Code → U) (code : Code) : U := getWorld code

/--
Julia source: base/runtime_internals.jl:1639-1639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max_world(m::Core.CodeInfo) = m.max_world
```
-/
def maxWorldCodeInfo {Code : Type} (getWorld : Code → U) (code : Code) : U := getWorld code

/--
Julia source: base/runtime_internals.jl:1662-1662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_require_world() = unsafe_load(cglobal(:jl_require_world, UInt))
```
-/
def getRequireWorld {World Pointer : Type} (cglobal : M World Pointer) (unsafeLoad : Pointer → M World U) : M World U := do
  unsafeLoad (← cglobal)

/--
Julia source: base/runtime_internals.jl:1778-1778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unionlen(@nospecialize(x)) = x isa Union ? unionlen(x.a) + unionlen(x.b) : 1
```
-/
def unionlen {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym) (x : V) : M World I :=
  whileLoop (fun (pending, count) => do
    match pending with
    | [] => pure (.inl count)
    | value :: rest =>
      match ops.asUnion value with
      | some (a, b) => pure (.inr (a :: b :: rest, count))
      | none => pure (.inr (rest, count + i 1))) ([x], i 0)

/--
Julia source: base/runtime_internals.jl:1780-1788 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uniontypes(@nospecialize(x), ts::Array{Any,1})
    if x isa Union
        _uniontypes(x.a, ts)
        _uniontypes(x.b, ts)
    else
        push!(ts, x)
    end
    return ts
end
```
-/
def internalUniontypes {World V D N Mod P Sym Ref : Type} (ops : TypeOps World V D N Mod P Sym)
    (push : Ref → V → M World Unit) (x : V) (types : Ref) : M World Ref := do
  whileLoop (fun pending => do
    match pending with
    | [] => pure (.inl ())
    | value :: rest =>
      match ops.asUnion value with
      | some (a, b) => pure (.inr (a :: b :: rest))
      | none =>
        push types value
        pure (.inr rest)) [x]
  pure types

/--
Julia source: base/runtime_internals.jl:1789-1789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uniontypes(@nospecialize(x)) = _uniontypes(x, Any[])
```
-/
def uniontypes {World V D N Mod P Sym Ref : Type} (ops : TypeOps World V D N Mod P Sym)
    (newVector : M World Ref) (push : Ref → V → M World Unit) (x : V) : M World Ref := do
  internalUniontypes ops push x (← newVector)

/--
Julia source: base/runtime_internals.jl:1802-1804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _methods_by_ftype(@nospecialize(t), mt::Union{Core.MethodTable, Nothing}, lim::Int, world::UInt, ambig::Bool, min::Ref{UInt}, max::Ref{UInt}, has_ambig::Ref{Int32})
    return ccall(:jl_matching_methods, Any, (Any, Any, Cint, Cint, UInt, Ptr{UInt}, Ptr{UInt}, Ptr{Int32}), t, mt, lim, ambig, world, min, max, has_ambig)::Union{Vector{Any},Nothing}
end
```
-/
def methodsByTypeNative {World V Table Ref Pointer Match : Type} (lookup : LookupOps World V Table Ref Pointer Match)
    (t : V) (table : Option Table) (limit : I) (world : U) (ambiguous : Bool)
    (minWorld maxWorld : Ref) (hasAmbiguous : Pointer) : M World (Option (List Match)) := do
  let limit ← JuliaLean.base.io.liftJl (JInt.convert "convert" .i32 limit.val)
  lookup.matching t table limit (JInt.wrap .i32 (if ambiguous then 1 else 0)) world minWorld maxWorld hasAmbiguous

/--
Julia source: base/runtime_internals.jl:1799-1801 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _methods_by_ftype(@nospecialize(t), mt::Union{Core.MethodTable, Nothing}, lim::Int, world::UInt)
    return _methods_by_ftype(t, mt, lim, world, false, RefValue{UInt}(typemin(UInt)), RefValue{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
end
```
-/
def methodsByTypeTable {World V Table Ref Pointer Match : Type} (lookup : LookupOps World V Table Ref Pointer Match)
    (t : V) (table : Option Table) (limit : I) (world : U) : M World (Option (List Match)) := do
  let minWorld ← lookup.newWorldRef (JInt.typemin .u64)
  let maxWorld ← lookup.newWorldRef (JInt.typemax .u64)
  methodsByTypeNative lookup t table limit world false minWorld maxWorld lookup.nullAmbiguousPointer

/--
Julia source: base/runtime_internals.jl:1796-1798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _methods_by_ftype(@nospecialize(t), lim::Int, world::UInt)
    return _methods_by_ftype(t, nothing, lim, world)
end
```
-/
def methodsByType {World V Table Ref Pointer Match : Type} (lookup : LookupOps World V Table Ref Pointer Match)
    (t : V) (limit : I) (world : U) : M World (Option (List Match)) := methodsByTypeTable lookup t none limit world

/--
Julia source: base/runtime_internals.jl:1791-1794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _methods(@nospecialize(f), @nospecialize(t), lim::Int, world::UInt)
    tt = signature_type(f, t)
    return _methods_by_ftype(tt, lim, world)
end
```
-/
def internalMethods {World V D N Mod P Sym Table Ref Pointer Match : Type}
    (ops : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref Pointer Match)
    (f t : V) (limit : I) (world : U) : M World (Option (List Match)) := do
  methodsByType lookup (← signatureType ops f t) limit world

/--
Julia source: base/runtime_internals.jl:1806-1806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasgenerator(m::Method) = isdefined(m, :generator)
```
-/
def hasgenerator {World Method : Type} (isdefinedGenerator : Method → M World Bool) (m : Method) : M World Bool :=
  isdefinedGenerator m

/--
Julia source: base/runtime_internals.jl:1807-1807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasgenerator(m::Core.MethodInstance) = hasgenerator(m.def::Method)
```
-/
def hasgeneratorMethodInstance {World MethodInstance Method : Type} (getDef : MethodInstance → M World Method)
    (isdefinedGenerator : Method → M World Bool) (m : MethodInstance) : M World Bool := do hasgenerator isdefinedGenerator (← getDef m)

/--
Julia source: base/runtime_internals.jl:1850-1850 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ast_slotflag(@nospecialize(code), i) = ccall(:jl_ir_slotflag, UInt8, (Any, Csize_t), code, i - 1)
```
-/
def astSlotflag {World Code Index MinusOne : Type} (subOne : Index → M World MinusOne)
    (jlIrSlotflag : Code → MinusOne → M World U8) (code : Code) (index : Index) : M World U8 := do
  jlIrSlotflag code (← subOne index)

/--
Julia source: base/runtime_internals.jl:1930-1947 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function subst_trivial_bounds(@nospecialize(atype))
    if !isa(atype, UnionAll)
        return atype
    end
    v = atype.var
    if isconcretetype(v.ub) || v.lb === v.ub
        subst = try
            atype{v.ub}
        catch
            # Note in rare cases a var bound might not be valid to substitute.
            nothing
        end
        if subst !== nothing
            return subst_trivial_bounds(subst)
        end
    end
    return UnionAll(v, subst_trivial_bounds(atype.body))
end
```
-/
def substTrivialBounds {World V D N Mod P Sym Var : Type} (ops : TypeOps World V D N Mod P Sym)
    (viewUnionall : V → Option (Var × V)) (upper lower : Var → V)
    (isNothing : V → Bool) (instantiate : V → V → M World V) (unionAll : Var → V → M World V) (atype : V) : M World V := fun world => do
  match viewUnionall atype with
  | none => pure (.ok (atype, world))
  | some (typevar, body) =>
    if isconcretetype ops (upper typevar) || ops.egal (lower typevar) (upper typevar) then
      match ← instantiate atype (upper typevar) world with
      | .ok (subst, world) =>
        if !isNothing subst then return ← substTrivialBounds ops viewUnionall upper lower isNothing instantiate unionAll subst world
        match ← substTrivialBounds ops viewUnionall upper lower isNothing instantiate unionAll body world with
        | .error error => pure (.error error)
        | .ok (body, world) => unionAll typevar body world
      | .error (_, world) =>
        match ← substTrivialBounds ops viewUnionall upper lower isNothing instantiate unionAll body world with
        | .error error => pure (.error error)
        | .ok (body, world) => unionAll typevar body world
    else
      match ← substTrivialBounds ops viewUnionall upper lower isNothing instantiate unionAll body world with
      | .error error => pure (.error error)
      | .ok (body, world) => unionAll typevar body world
partial_fixpoint

/--
Julia source: base/runtime_internals.jl:1953-1960 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function normalize_typevars(method::Method, @nospecialize(atype), sparams::SimpleVector)
    at2 = subst_trivial_bounds(atype)
    if at2 !== atype && at2 == atype
        atype = at2
        (_, sparams) = typeintersect_env(at2, method.sig)
    end
    return Pair{Any,SimpleVector}(atype, sparams)
end
```
-/
def normalizeTypevars {World Method V Params : Type} (substTrivialBounds : V → M World V)
    (egal : V → V → Bool) (equalType : V → V → M World Bool) (signature : Method → V)
    (intersectEnv : V → V → M World (V × Params)) (method : Method) (atype : V) (sparams : Params)
    : M World (V × Params) := do
  let at2 ← substTrivialBounds atype
  if !egal at2 atype then
    if ← equalType at2 atype then
      let (_, sparams) ← intersectEnv at2 (signature method)
      return (at2, sparams)
  pure (atype, sparams)

/--
Julia source: base/runtime_internals.jl:1962-1966 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_nospecializeinfer_sig(method::Method, @nospecialize(atype), sparams::SimpleVector)
    isa(atype, DataType) || return method.sig
    return ccall(:jl_normalize_to_compilable_sig, Any, (Any, Any, Any, Cint),
        atype, sparams, method, #=int return_if_compileable=#0)
end
```
-/
def getNospecializeinferSig {World V D N Mod P Sym Method Params : Type} (ops : TypeOps World V D N Mod P Sym)
    (signature : Method → V) (native : V → Params → Method → Cint → M World V)
    (method : Method) (atype : V) (sparams : Params) : M World V := do
  if (ops.asDatatype atype).isNone then return signature method
  native atype sparams method (JInt.wrap .i32 0)

/--
Julia source: base/runtime_internals.jl:1968-1968 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_nospecialized(method::Method) = method.nospecialize ≠ 0
```
-/
def isNospecialized {Method : Type} (nospecialize : Method → U32) (method : Method) : Bool := (nospecialize method).val != 0

/--
Julia source: base/runtime_internals.jl:1969-1969 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_nospecializeinfer(method::Method) = method.nospecializeinfer && is_nospecialized(method)
```
-/
def isNospecializeinfer {Method : Type} (nospecializeinfer : Method → Bool) (nospecialize : Method → U32)
    (method : Method) : Bool := nospecializeinfer method && isNospecialized nospecialize method

/--
Julia source: base/runtime_internals.jl:1809-1815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uncompressed_ir(m::Method)
    s = m.source
    if s isa String
        s = ccall(:jl_uncompress_ir, Ref{CodeInfo}, (Any, Ptr{Cvoid}, Any), m, C_NULL, s)
    end
    return s::CodeInfo
end
```
-/
def uncompressedIrMethod {World Method Raw Str Code Pointer : Type}
    (source : Method → M World Raw) (asString : Raw → Option Str) (codeValue : Code → Raw)
    (assertCode : Raw → M World Code) (jlUncompressIr : Method → Pointer → Str → M World Code)
    (nullPointer : Pointer) (method : Method) : M World Code := do
  let mut s ← source method
  if let some compressed := asString s then
    s := codeValue (← jlUncompressIr method nullPointer compressed)
  assertCode s

/--
Julia source: base/runtime_internals.jl:1817-1818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uncompressed_ir(codeinst::CodeInstance, s::String) =
    ccall(:jl_uncompress_ir, Ref{CodeInfo}, (Any, Any, Any), codeinst.def.def::Method, codeinst, s)
```
-/
def uncompressedIrCodeInstance {World CodeInstance Def Method Str Code : Type}
    (getDef : CodeInstance → M World Def) (getDefMethod : Def → M World Method)
    (jlUncompressIr : Method → CodeInstance → Str → M World Code)
    (codeinst : CodeInstance) (s : Str) : M World Code := do
  let method ← getDefMethod (← getDef codeinst)
  jlUncompressIr method codeinst s

/--
Julia source: base/runtime_internals.jl:1820-1827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_ci_mi(codeinst::CodeInstance)
    def = codeinst.def
    if def isa Core.ABIOverride
        return def.def
    else
        return def::MethodInstance
    end
end
```
-/
def getCiMi {World CodeInstance Def ABIOverride MethodInstance : Type}
    (getDef : CodeInstance → M World Def) (asAbiOverride : Def → Option ABIOverride)
    (abiDef : ABIOverride → M World MethodInstance) (assertMethodInstance : Def → M World MethodInstance)
    (codeinst : CodeInstance) : M World MethodInstance := do
  let value ← getDef codeinst
  match asAbiOverride value with
  | some overrideValue => abiDef overrideValue
  | none => assertMethodInstance value

/--
Julia source: base/runtime_internals.jl:1867-1869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function may_invoke_generator(mi::MethodInstance)
    return may_invoke_generator(mi.def::Method, mi.specTypes, mi.sparam_vals)
end
```
-/
def mayInvokeGeneratorInstance {World Instance Method V Params : Type}
    (getDef : Instance → M World Method) (specTypes : Instance → M World V)
    (sparamValues : Instance → M World Params) (analyzeGenerator : Method → V → Params → M World Bool)
    (mi : Instance) : M World Bool := do
  let method ← getDef mi
  let types ← specTypes mi
  let params ← sparamValues mi
  analyzeGenerator method types params

structure GeneratorAnalysisOps (World V Method Generator Code Match : Type) where
  methodGenerator : Method → M World Generator
  isGeneratedFunctionStub : Generator → Bool
  generatorFunction : Generator → V
  /-- The `Vararg{Any}` type value used to build the generator's lookup signature. -/
  varargAny : M World V
  methodPrimaryWorld : Method → U
  /-- `Method.nargs`, read as `UInt32` and converted to Julia `Int` in the method. -/
  methodNargs : Method → U32
  methodIsVararg : Method → Bool
  matchMethod : Match → M World Method
  isSimpleVector : V → Bool
  hasSource : Method → M World Bool
  source : Method → M World Code
  /-- `ccall(:jl_ir_nslots, Int, (Any,), code)`, the slot count of CodeInfo or compressed IR (`src/ircode.c:1303-1313`). -/
  irNslots : Code → M World I
  /-- `ccall(:jl_ir_slotflag, UInt8, (Any,Csize_t), code, i-1)` reads one slot flag (`src/ircode.c:1316-1324`). -/
  irSlotflag : Code → U → M World U8

/--
Julia source: base/runtime_internals.jl:1870-1925 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function may_invoke_generator(method::Method, @nospecialize(atype), sparams::SimpleVector)
    # If we have complete information, we may always call the generator
    isdispatchtuple(atype) && return true

    # We don't have complete information, but it is possible that the generator
    # syntactically doesn't make use of the information we don't have. Check
    # for that.

    # For now, only handle the (common, generated by the frontend case) that the
    # generator only has one method
    generator = method.generator
    isa(generator, Core.GeneratedFunctionStub) || return false
    tt = Tuple{typeof(generator.gen), Vararg{Any}}
    gen_mthds = _methods_by_ftype(tt, #=lim=#1, method.primary_world)
    gen_mthds isa Vector || return false
    length(gen_mthds) == 1 || return false

    generator_method = (first(gen_mthds)::Core.MethodMatch).method
    nsparams = length(sparams)
    isdefined(generator_method, :source) || return false
    code = generator_method.source
    nslots = ccall(:jl_ir_nslots, Int, (Any,), code)
    at = unwrap_unionall(atype)
    at isa DataType || return false
    (nslots >= 1 + length(sparams) + length(at.parameters)) || return false

    firstarg = 1
    for i = 1:nsparams
        if isa(sparams[i], SimpleVector)
            if (ast_slotflag(code, firstarg + i) & SLOT_USED) != 0
                return false
            end
        end
    end
    nargs = Int(method.nargs)
    non_va_args = method.isva ? nargs - 1 : nargs
    for i = 1:non_va_args
        if !isdispatchelem(at.parameters[i])
            if (ast_slotflag(code, firstarg + i + nsparams) & SLOT_USED) != 0
                return false
            end
        end
    end
    if method.isva
        # If the va argument is used, we need to ensure that all arguments that
        # contribute to the va tuple are dispatch elements
        if (ast_slotflag(code, firstarg + nargs + nsparams) & SLOT_USED) != 0
            for i = (non_va_args+1):length(at.parameters)
                if !isdispatchelem(at.parameters[i])
                    return false
                end
            end
        end
    end
    return true
end
```
-/
def mayInvokeGenerator {World V D N Mod P Sym Table Ref Pointer Match Method Generator Code : Type}
    (types : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref Pointer Match)
    (ops : GeneratorAnalysisOps World V Method Generator Code Match) (method : Method)
    (atype : V) (sparams : List V) : M World Bool := do
  if isdispatchtuple types atype then return true
  let generator ← ops.methodGenerator method
  if !ops.isGeneratedFunctionStub generator then return false
  let generatorType ← types.coreTypeof (ops.generatorFunction generator)
  let varargAny ← ops.varargAny
  let tupleType ← types.tupleType [generatorType, varargAny]
  let foundMethods ← methodsByType lookup tupleType (i 1) (ops.methodPrimaryWorld method)
  let some [matchValue] := foundMethods | return false
  let generatorMethod ← ops.matchMethod matchValue
  if !(← ops.hasSource generatorMethod) then return false
  let code ← ops.source generatorMethod
  let nslots ← ops.irNslots code
  let unwrappedType := types.unwrap atype
  let some datatype := types.asDatatype unwrappedType | return false
  let parameters ← types.parameters datatype
  let nsparams : I := i (Int.ofNat sparams.length)
  let requiredSlots := i 1 + nsparams + i (Int.ofNat parameters.length)
  if nslots.val < requiredSlots.val then return false
  let slotFlagAt : I → M World U8 := fun index =>
    astSlotflag
      (fun slot => JuliaLean.base.io.liftJl
        (JInt.convert "convert" .u64 (slot - i 1).val))
      ops.irSlotflag code index
  let firstarg := i 1
  let noSpecialVectorSlotUse ← whileLoop (fun index => do
    if index.val > nsparams.val then
      pure (.inl true)
    else
      let some sparam := sparams[index.val.toNat - 1]? | throw (.jl .boundsError)
      if ops.isSimpleVector sparam then
        if has8 (← slotFlagAt (firstarg + index)) 8 then pure (.inl false)
        else pure (.inr (index + i 1))
      else pure (.inr (index + i 1))) (i 1)
  if !noSpecialVectorSlotUse then return false
  let nargs ← JuliaLean.base.io.liftJl
    (JInt.convert "convert" .i64 (ops.methodNargs method).val)
  let nonVaArgs := if ops.methodIsVararg method then nargs - i 1 else nargs
  let noNonDispatchSlotUse ← whileLoop (fun index => do
    if index.val > nonVaArgs.val then
      pure (.inl true)
    else
      let some parameter := parameters[index.val.toNat - 1]? | throw (.jl .boundsError)
      if ← isdispatchelem types parameter then
        pure (.inr (index + i 1))
      else if has8 (← slotFlagAt (firstarg + index + nsparams)) 8 then
        pure (.inl false)
      else
        pure (.inr (index + i 1))) (i 1)
  if !noNonDispatchSlotUse then return false
  if ops.methodIsVararg method then
    if has8 (← slotFlagAt (firstarg + nargs + nsparams)) 8 then
      let noNonDispatchVarargUse ← whileLoop (fun index => do
        if index.val > (i (Int.ofNat parameters.length)).val then
          pure (.inl true)
        else
          let some parameter := parameters[index.val.toNat - 1]? | throw (.jl .boundsError)
          if ← isdispatchelem types parameter then
            pure (.inr (index + i 1))
          else
            pure (.inl false)) (nonVaArgs + i 1)
      if !noNonDispatchVarargUse then return false
  return true

structure SpecializationOps (World V Var Method Params Instance : Type) where
  viewUnionall : V → Option (Var × V)
  upper : Var → V
  lower : Var → V
  isNothing : V → Bool
  instantiate : V → V → M World V
  unionAll : Var → V → M World V
  equalType : V → V → M World Bool
  signature : Method → V
  intersectEnv : V → V → M World (V × Params)
  nospecializeinfer : Method → Bool
  nospecialize : Method → U32
  normalizeToCompilableSig : V → Params → Method → Cint → M World V
  lookup : Method → V → M World (Option Instance)
  getLinfo : Method → V → Params → M World Instance

/--
Julia source: base/runtime_internals.jl:1979-1993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function specialize_method(method::Method, @nospecialize(atype), sparams::SimpleVector; preexisting::Bool=false)
    @inline
    if isa(atype, UnionAll)
        atype, sparams = normalize_typevars(method, atype, sparams)
    end
    if is_nospecializeinfer(method) # TODO: this shouldn't be here
        atype = get_nospecializeinfer_sig(method, atype, sparams)
    end
    if preexisting
        # check cached specializations
        # for an existing result stored there
        return ccall(:jl_specializations_lookup, Any, (Any, Any), method, atype)::Union{Nothing,MethodInstance}
    end
    return ccall(:jl_specializations_get_linfo, Ref{MethodInstance}, (Any, Any, Any), method, atype, sparams)
end
```
-/
def specializeMethod {World V D N Mod P Sym Var Method Params Instance : Type}
    (types : TypeOps World V D N Mod P Sym) (ops : SpecializationOps World V Var Method Params Instance)
    (method : Method) (atype : V) (sparams : Params) (preexisting : Bool := false)
    : M World (Option Instance) := do
  let mut atype := atype
  let mut sparams := sparams
  if (ops.viewUnionall atype).isSome then
    let (normalized, parameters) ← normalizeTypevars
      (substTrivialBounds types ops.viewUnionall ops.upper ops.lower ops.isNothing ops.instantiate ops.unionAll)
      types.egal ops.equalType ops.signature ops.intersectEnv method atype sparams
    atype := normalized
    sparams := parameters
  if isNospecializeinfer ops.nospecializeinfer ops.nospecialize method then
    atype := ← getNospecializeinferSig types ops.signature ops.normalizeToCompilableSig method atype sparams
  if preexisting then return ← ops.lookup method atype
  pure (some (← ops.getLinfo method atype sparams))

/--
Julia source: base/runtime_internals.jl:1995-1997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function specialize_method(match::Core.MethodMatch; kwargs...)
    return specialize_method(match.method, match.spec_types, match.sparams; kwargs...)
end
```
-/
def specializeMethodMatch {World V D N Mod P Sym Var Method Params Instance Match : Type}
    (types : TypeOps World V D N Mod P Sym) (ops : SpecializationOps World V Var Method Params Instance)
    (method : Match → M World Method) (specTypes : Match → M World V) (sparams : Match → M World Params)
    (matchValue : Match) (preexisting : Bool := false) : M World (Option Instance) := do
  let methodValue ← method matchValue
  let typeValue ← specTypes matchValue
  let parameterValues ← sparams matchValue
  specializeMethod types ops methodValue typeValue parameterValues preexisting

-- UNTRANSLATED
-- Source: base/runtime_internals.jl:220-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro __FUNCTION__()
--     Expr(:thisfunction)
-- end
-- /Source
-- Reason: Frontend macro expansion constructs Expr(:thisfunction); the typed runtime model does not implement the Julia syntax/lowering AST.

-- Source: base/runtime_internals.jl:248-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # N.B.: Needs to be synced with julia.h
-- const PARTITION_KIND_CONST              = 0x0
-- const PARTITION_KIND_CONST_IMPORT       = 0x1
-- const PARTITION_KIND_GLOBAL             = 0x2
-- const PARTITION_KIND_IMPLICIT_GLOBAL    = 0x3
-- const PARTITION_KIND_IMPLICIT_CONST     = 0x4
-- const PARTITION_KIND_EXPLICIT           = 0x5
-- const PARTITION_KIND_IMPORTED           = 0x6
-- const PARTITION_KIND_FAILED             = 0x7
-- const PARTITION_KIND_DECLARED           = 0x8
-- const PARTITION_KIND_GUARD              = 0x9
-- const PARTITION_KIND_UNDEF_CONST        = 0xa
-- const PARTITION_KIND_BACKDATED_CONST    = 0xb
-- 
-- const PARTITION_FLAG_EXPORTED     = 0x10
-- const PARTITION_FLAG_DEPRECATED   = 0x20
-- const PARTITION_FLAG_DEPWARN      = 0x40
-- const PARTITION_FLAG_IMPLICITLY_EXPORTED = 0x80
-- const PARTITION_FLAG_IMPLICITLY_DEPRECATED = 0x100
-- 
-- const PARTITION_MASK_KIND         = 0x0f
-- const PARTITION_MASK_FLAG         = 0x1f0
-- 
-- const BINDING_FLAG_ANY_IMPLICIT_EDGES = 0x8
-- 
-- const JL_MODULE_USING_REEXPORT = 0x1
-- 
-- is_defined_const_binding(kind::UInt8) = (kind == PARTITION_KIND_CONST || kind == PARTITION_KIND_CONST_IMPORT || kind == PARTITION_KIND_IMPLICIT_CONST || kind == PARTITION_KIND_BACKDATED_CONST)
-- is_some_const_binding(kind::UInt8) = (is_defined_const_binding(kind) || kind == PARTITION_KIND_UNDEF_CONST)
-- is_some_imported(kind::UInt8) = (kind == PARTITION_KIND_IMPLICIT_GLOBAL || kind == PARTITION_KIND_IMPLICIT_CONST || kind == PARTITION_KIND_EXPLICIT || kind == PARTITION_KIND_IMPORTED)
-- is_some_implicit(kind::UInt8) = (kind == PARTITION_KIND_IMPLICIT_GLOBAL || kind == PARTITION_KIND_IMPLICIT_CONST || kind == PARTITION_KIND_GUARD || kind == PARTITION_KIND_FAILED)
-- is_some_explicit_imported(kind::UInt8) = (kind == PARTITION_KIND_EXPLICIT || kind == PARTITION_KIND_IMPORTED)
-- is_some_binding_imported(kind::UInt8) = is_some_explicit_imported(kind) || kind == PARTITION_KIND_IMPLICIT_GLOBAL
-- is_some_guard(kind::UInt8) = (kind == PARTITION_KIND_GUARD || kind == PARTITION_KIND_FAILED || kind == PARTITION_KIND_UNDEF_CONST)
-- # A global variable: accessed through the binding's own value slot (typed, or `Any` if weakly declared).
-- is_some_global(kind::UInt8) = (kind == PARTITION_KIND_GLOBAL || kind == PARTITION_KIND_DECLARED)
-- 
-- function lookup_binding_partition(world::UInt, b::Core.Binding)
--     ccall(:jl_get_binding_partition, Ref{Core.BindingPartition}, (Any, UInt), b, world)
-- end
-- 
-- function lookup_binding_partition(world::UInt, b::Core.Binding, previous_partition::Core.BindingPartition)
--     ccall(:jl_get_binding_partition_with_hint, Ref{Core.BindingPartition}, (Any, Any, UInt), b, previous_partition, world)
-- end
-- 
-- function convert(::Type{Core.Binding}, gr::Core.GlobalRef)
--     if isdefined(gr, :binding)
--         return gr.binding
--     else
--         return ccall(:jl_get_module_binding, Ref{Core.Binding}, (Any, Any, Cint), gr.mod, gr.name, true)
--     end
-- end
-- 
-- function lookup_binding_partition(world::UInt, gr::Core.GlobalRef)
--     b = convert(Core.Binding, gr)
--     return lookup_binding_partition(world, b)
-- end
-- 
-- partition_restriction(bpart::Core.BindingPartition) = ccall(:jl_bpart_get_restriction_value, Any, (Any,), bpart)
-- 
-- # Recover the `Core.Binding` that owns `bpart` by walking the chain to its end: the
-- # last (oldest) partition's `next` is a backreference to the owning binding, so the
-- # list can be traversed circularly.
-- function partition_owner(bpart::Core.BindingPartition)
--     next = bpart.next
--     while next isa Core.BindingPartition
--         next = next.next
--     end
--     return next::Core.Binding
-- end
-- 
-- binding_kind(bpart::Core.BindingPartition) = UInt8(bpart.kind & PARTITION_MASK_KIND)
-- binding_kind(m::Module, s::Symbol) = binding_kind(lookup_binding_partition(tls_world_age(), GlobalRef(m, s)))
-- 
-- /Source

-- UNTRANSLATED
-- Source: base/runtime_internals.jl:616-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro locals()
--     return Expr(:locals)
-- end
-- /Source
-- Reason: The @locals macro emits a compiler-interpreted syntax node; local-variable capture is frontend/lowering behaviour, outside the typed runtime model.

-- Source: base/runtime_internals.jl:1198-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function is_valid_intrinsic_elptr(@nospecialize(ety))
--     ety === Any && return true
--     isconcretetype(ety) || return false
--     ety <: Array && return false
--     return !is_datatype_layoutopaque(ety)
-- end
-- /Source

-- Source: base/runtime_internals.jl:1364-1374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function argument_datatype(@nospecialize t)
--     @_total_meta
--     @noinline
--     return ccall(:jl_argument_datatype, Any, (Any,), t)::Union{Nothing,DataType}
-- end
-- 
-- function argument_datatypename(@nospecialize t)
--     @_total_meta
--     @noinline
--     return ccall(:jl_argument_datatypename, Any, (Any,), t)::Union{Nothing,Core.TypeName}
-- end
-- /Source

-- Source: base/runtime_internals.jl:1563-1639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function get_methodtable(m::Method)
--     mt = ccall(:jl_method_get_table, Any, (Any,), m)
--     if mt === nothing
--         return nothing
--     end
--     return mt::Core.MethodTable
-- end
-- 
-- """
--     has_bottom_parameter(t)::Bool
-- 
-- Determine whether `t` is a Type for which one or more of its parameters is `Union{}`.
-- """
-- function has_bottom_parameter(@nospecialize(t::Core.AnyType))
--     t === Bottom && return true
--     ty = typeof(t)
--     if ty === DataType
--         for p in getfield(t, :parameters)
--             has_bottom_parameter(p) && return true
--         end
--     elseif ty === TypeEq || ty === Core.TypeEgal
--         return has_bottom_parameter(type_parameter(t))
--     elseif ty === UnionAll
--         return has_bottom_parameter(unwrap_unionall(t))
--     elseif ty === Union
--         return has_bottom_parameter(getfield(t, :a)) & has_bottom_parameter(getfield(t, :b))
--     end
--     return false
-- end
-- has_bottom_parameter(t::TypeVar) = has_bottom_parameter(t.ub)
-- has_bottom_parameter(::Any) = false
-- 
-- function find_free_typevars(@nospecialize(t))
--     return ccall(:jl_find_free_typevars, Array{Any, 1}, (Any,), t)
-- end
-- 
-- """
--     rewrap_free_typevars(@nospecialize(t), pre=Core.svec())
-- 
-- Wrap `t` in `UnionAll` for each `TypeVar` that is free in `t` but not referenced
-- in `pre` (the typevars that were free in the consumer's input before an env was
-- applied).
-- 
-- This is the consumer-side complement to `jl_type_intersection_env` /
-- `jl_subtype_env`: the env svec may contain entries whose typevar identity is
-- shared across slots. Rather than wrapping each slot independently (which breaks
-- that identity), callers that build a new type from the env should apply this
-- helper once to the final reconstructed type.
-- """
-- function rewrap_free_typevars(@nospecialize(t), pre=Core.svec())
--     has_free_typevars(t) || return t
--     # UnionAll cannot directly wrap a Vararg; the caller must wrap it in Tuple first
--     isvarargtype(t) && return t
--     fv = find_free_typevars(t)
--     for i in length(fv):-1:1
--         v = fv[i]::TypeVar
--         wrap = true
--         for p in pre
--             if p === v
--                 wrap = false
--                 break
--             end
--         end
--         wrap && (t = UnionAll(v, t))
--     end
--     return t
-- end
-- 
-- function typeintersect_env(@nospecialize(a), @nospecialize(b))
--     (ti, env) = ccall(:jl_type_intersection_with_env, Any, (Any, Any), a, b)::SimpleVector
--     Pair{Any, SimpleVector}(ti, env)
-- end
-- 
-- min_world(m::Core.CodeInstance) = m.min_world
-- max_world(m::Core.CodeInstance) = m.max_world
-- min_world(m::Core.CodeInfo) = m.min_world
-- max_world(m::Core.CodeInfo) = m.max_world
-- /Source

-- Source: base/runtime_internals.jl:1662-1662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- get_require_world() = unsafe_load(cglobal(:jl_require_world, UInt))
-- /Source

-- Source: base/runtime_internals.jl:1778-1831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unionlen(@nospecialize(x)) = x isa Union ? unionlen(x.a) + unionlen(x.b) : 1
-- 
-- function _uniontypes(@nospecialize(x), ts::Array{Any,1})
--     if x isa Union
--         _uniontypes(x.a, ts)
--         _uniontypes(x.b, ts)
--     else
--         push!(ts, x)
--     end
--     return ts
-- end
-- uniontypes(@nospecialize(x)) = _uniontypes(x, Any[])
-- 
-- function _methods(@nospecialize(f), @nospecialize(t), lim::Int, world::UInt)
--     tt = signature_type(f, t)
--     return _methods_by_ftype(tt, lim, world)
-- end
-- 
-- function _methods_by_ftype(@nospecialize(t), lim::Int, world::UInt)
--     return _methods_by_ftype(t, nothing, lim, world)
-- end
-- function _methods_by_ftype(@nospecialize(t), mt::Union{Core.MethodTable, Nothing}, lim::Int, world::UInt)
--     return _methods_by_ftype(t, mt, lim, world, false, RefValue{UInt}(typemin(UInt)), RefValue{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
-- end
-- function _methods_by_ftype(@nospecialize(t), mt::Union{Core.MethodTable, Nothing}, lim::Int, world::UInt, ambig::Bool, min::Ref{UInt}, max::Ref{UInt}, has_ambig::Ref{Int32})
--     return ccall(:jl_matching_methods, Any, (Any, Any, Cint, Cint, UInt, Ptr{UInt}, Ptr{UInt}, Ptr{Int32}), t, mt, lim, ambig, world, min, max, has_ambig)::Union{Vector{Any},Nothing}
-- end
-- 
-- hasgenerator(m::Method) = isdefined(m, :generator)
-- hasgenerator(m::Core.MethodInstance) = hasgenerator(m.def::Method)
-- 
-- function _uncompressed_ir(m::Method)
--     s = m.source
--     if s isa String
--         s = ccall(:jl_uncompress_ir, Ref{CodeInfo}, (Any, Ptr{Cvoid}, Any), m, C_NULL, s)
--     end
--     return s::CodeInfo
-- end
-- 
-- _uncompressed_ir(codeinst::CodeInstance, s::String) =
--     ccall(:jl_uncompress_ir, Ref{CodeInfo}, (Any, Any, Any), codeinst.def.def::Method, codeinst, s)
-- 
-- function get_ci_mi(codeinst::CodeInstance)
--     def = codeinst.def
--     if def isa Core.ABIOverride
--         return def.def
--     else
--         return def::MethodInstance
--     end
-- end
-- 
-- """
--     Base.generating_output([incremental::Bool])::Bool
-- 
-- /Source

-- Source: base/runtime_internals.jl:1849-1997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const SLOT_USED = 0x8
-- ast_slotflag(@nospecialize(code), i) = ccall(:jl_ir_slotflag, UInt8, (Any, Csize_t), code, i - 1)
-- 
-- """
--     may_invoke_generator(method, atype, sparams)::Bool
-- 
-- Compute whether or not we may invoke the generator for the given `method` on
-- the given `atype` and `sparams`. For correctness, all generated function are
-- required to return monotonic answers. However, since we don't expect users to
-- be able to successfully implement this criterion, we only call generated
-- functions on concrete types. The one exception to this is that we allow calling
-- generators with abstract types if the generator does not use said abstract type
-- (and thus cannot incorrectly use it to break monotonicity). This function
-- computes whether we are in either of these cases.
-- 
-- Unlike normal functions, the compilation heuristics still can't generate good dispatch
-- in some cases, but this may still allow inference not to fall over in some limited cases.
-- """
-- function may_invoke_generator(mi::MethodInstance)
--     return may_invoke_generator(mi.def::Method, mi.specTypes, mi.sparam_vals)
-- end
-- function may_invoke_generator(method::Method, @nospecialize(atype), sparams::SimpleVector)
--     # If we have complete information, we may always call the generator
--     isdispatchtuple(atype) && return true
-- 
--     # We don't have complete information, but it is possible that the generator
--     # syntactically doesn't make use of the information we don't have. Check
--     # for that.
-- 
--     # For now, only handle the (common, generated by the frontend case) that the
--     # generator only has one method
--     generator = method.generator
--     isa(generator, Core.GeneratedFunctionStub) || return false
--     tt = Tuple{typeof(generator.gen), Vararg{Any}}
--     gen_mthds = _methods_by_ftype(tt, #=lim=#1, method.primary_world)
--     gen_mthds isa Vector || return false
--     length(gen_mthds) == 1 || return false
-- 
--     generator_method = (first(gen_mthds)::Core.MethodMatch).method
--     nsparams = length(sparams)
--     isdefined(generator_method, :source) || return false
--     code = generator_method.source
--     nslots = ccall(:jl_ir_nslots, Int, (Any,), code)
--     at = unwrap_unionall(atype)
--     at isa DataType || return false
--     (nslots >= 1 + length(sparams) + length(at.parameters)) || return false
-- 
--     firstarg = 1
--     for i = 1:nsparams
--         if isa(sparams[i], SimpleVector)
--             if (ast_slotflag(code, firstarg + i) & SLOT_USED) != 0
--                 return false
--             end
--         end
--     end
--     nargs = Int(method.nargs)
--     non_va_args = method.isva ? nargs - 1 : nargs
--     for i = 1:non_va_args
--         if !isdispatchelem(at.parameters[i])
--             if (ast_slotflag(code, firstarg + i + nsparams) & SLOT_USED) != 0
--                 return false
--             end
--         end
--     end
--     if method.isva
--         # If the va argument is used, we need to ensure that all arguments that
--         # contribute to the va tuple are dispatch elements
--         if (ast_slotflag(code, firstarg + nargs + nsparams) & SLOT_USED) != 0
--             for i = (non_va_args+1):length(at.parameters)
--                 if !isdispatchelem(at.parameters[i])
--                     return false
--                 end
--             end
--         end
--     end
--     return true
-- end
-- 
-- # get a handle to the unique specialization object representing a particular instantiation of a call
-- # eliminate UnionAll vars that might be degenerate due to having identical bounds,
-- # or a concrete upper bound and appearing covariantly.
-- function subst_trivial_bounds(@nospecialize(atype))
--     if !isa(atype, UnionAll)
--         return atype
--     end
--     v = atype.var
--     if isconcretetype(v.ub) || v.lb === v.ub
--         subst = try
--             atype{v.ub}
--         catch
--             # Note in rare cases a var bound might not be valid to substitute.
--             nothing
--         end
--         if subst !== nothing
--             return subst_trivial_bounds(subst)
--         end
--     end
--     return UnionAll(v, subst_trivial_bounds(atype.body))
-- end
-- 
-- # If removing trivial vars from atype results in an equivalent type, use that
-- # instead. Otherwise we can get a case like issue #38888, where a signature like
-- #   f(x::S) where S<:Int
-- # gets cached and matches a concrete dispatch case.
-- function normalize_typevars(method::Method, @nospecialize(atype), sparams::SimpleVector)
--     at2 = subst_trivial_bounds(atype)
--     if at2 !== atype && at2 == atype
--         atype = at2
--         (_, sparams) = typeintersect_env(at2, method.sig)
--     end
--     return Pair{Any,SimpleVector}(atype, sparams)
-- end
-- 
-- function get_nospecializeinfer_sig(method::Method, @nospecialize(atype), sparams::SimpleVector)
--     isa(atype, DataType) || return method.sig
--     return ccall(:jl_normalize_to_compilable_sig, Any, (Any, Any, Any, Cint),
--         atype, sparams, method, #=int return_if_compileable=#0)
-- end
-- 
-- is_nospecialized(method::Method) = method.nospecialize ≠ 0
-- is_nospecializeinfer(method::Method) = method.nospecializeinfer && is_nospecialized(method)
-- 
-- """
-- Return MethodInstance corresponding to `atype` and `sparams`.
-- 
-- No widening / narrowing / compileable-normalization of `atype` is performed.
-- A slot for an argument known by egality must already carry the egality kind
-- (`TypeEgal{X}`, as `Compiler.widenconst` produces); a closed `Type{X}` slot
-- means the argument is only known up to type equality (#61323).
-- """
-- function specialize_method(method::Method, @nospecialize(atype), sparams::SimpleVector; preexisting::Bool=false)
--     @inline
--     if isa(atype, UnionAll)
--         atype, sparams = normalize_typevars(method, atype, sparams)
--     end
--     if is_nospecializeinfer(method) # TODO: this shouldn't be here
--         atype = get_nospecializeinfer_sig(method, atype, sparams)
--     end
--     if preexisting
--         # check cached specializations
--         # for an existing result stored there
--         return ccall(:jl_specializations_lookup, Any, (Any, Any), method, atype)::Union{Nothing,MethodInstance}
--     end
--     return ccall(:jl_specializations_get_linfo, Ref{MethodInstance}, (Any, Any, Any), method, atype, sparams)
-- end
-- 
-- function specialize_method(match::Core.MethodMatch; kwargs...)
--     return specialize_method(match.method, match.spec_types, match.sparams; kwargs...)
-- end
-- /Source

structure TypeMapLevelOps (World Level Memory Value : Type) where
  targ : Level → M World (Option Memory)
  arg1 : Level → M World (Option Memory)
  tname : Level → M World (Option Memory)
  name1 : Level → M World (Option Memory)
  list : Level → M World (Option Value)
  any : Level → M World (Option Value)

/--
Julia source: base/runtime_internals.jl:2012-2027 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function avisit(f, e::Memory{Any})
        # slot 1 holds the smallintset index; key/value pairs follow, so values
        # live on the odd slots starting at 3 (see mtcache layout in src/typemap.c)
        for i in 3:2:length(e)
            isassigned(e, i) || continue
            ei = e[i]
            if ei isa Memory{Any}
                for j in 3:2:length(ei)
                    isassigned(ei, j) || continue
                    visit(f, ei[j])
                end
            else
                visit(f, ei)
            end
        end
    end
```
-/
def avisit {World Function Memory Value : Type}
    (length : Memory → M World I) (isassigned : Memory → I → M World Bool)
    (getindex : Memory → I → M World Value) (asMemory : Value → Option Memory)
    (visit : Function → Value → M World Unit) (f : Function) (e : Memory) : M World Unit := do
  let n ← length e
  whileLoop (fun index => do
    if index ≤ n.val then
      let i := JuliaLean.base.runtime_internals.i index
      if ← isassigned e i then
        let ei ← getindex e i
        match asMemory ei with
        | some inner =>
          let count ← length inner
          whileLoop (fun index => do
            if index ≤ count.val then
              let j := JuliaLean.base.runtime_internals.i index
              if ← isassigned inner j then visit f (← getindex inner j)
              pure (.inr (index + 2))
            else pure (.inl ())) (3 : Int)
        | none => visit f ei
      pure (.inr (index + 2))
    else pure (.inl ())) (3 : Int)

/--
Julia source: base/runtime_internals.jl:2007-2010 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function visit(f, mt::Core.MethodTable)
    mt.defs !== nothing && visit(f, mt.defs)
    nothing
end
```
-/
def visitMethodTable {World Function Table Value : Type}
    (getDefs : Table → M World (Option Value)) (visit : Function → Value → M World Unit)
    (f : Function) (mt : Table) : M World Unit := do
  if (← getDefs mt).isSome then
    let some defs ← getDefs mt | throw (.jl (.methodError "visit"))
    visit f defs

/--
Julia source: base/runtime_internals.jl:2011-2043 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function visit(f, mc::Core.TypeMapLevel)
    function avisit(f, e::Memory{Any})
        # slot 1 holds the smallintset index; key/value pairs follow, so values
        # live on the odd slots starting at 3 (see mtcache layout in src/typemap.c)
        for i in 3:2:length(e)
            isassigned(e, i) || continue
            ei = e[i]
            if ei isa Memory{Any}
                for j in 3:2:length(ei)
                    isassigned(ei, j) || continue
                    visit(f, ei[j])
                end
            else
                visit(f, ei)
            end
        end
    end
    if mc.targ !== nothing
        avisit(f, mc.targ::Memory{Any})
    end
    if mc.arg1 !== nothing
        avisit(f, mc.arg1::Memory{Any})
    end
    if mc.tname !== nothing
        avisit(f, mc.tname::Memory{Any})
    end
    if mc.name1 !== nothing
        avisit(f, mc.name1::Memory{Any})
    end
    mc.list !== nothing && visit(f, mc.list)
    mc.any !== nothing && visit(f, mc.any)
    nothing
end
```
-/
def visitTypeMapLevel {World Function Level Memory Value : Type}
    (ops : TypeMapLevelOps World Level Memory Value) (length : Memory → M World I)
    (isassigned : Memory → I → M World Bool) (getindex : Memory → I → M World Value)
    (asMemory : Value → Option Memory) (visit : Function → Value → M World Unit)
    (f : Function) (mc : Level) : M World Unit := do
  if (← ops.targ mc).isSome then
    let some memory ← ops.targ mc | throw (.foreignError "TypeError" "expected Memory{Any}")
    avisit length isassigned getindex asMemory visit f memory
  if (← ops.arg1 mc).isSome then
    let some memory ← ops.arg1 mc | throw (.foreignError "TypeError" "expected Memory{Any}")
    avisit length isassigned getindex asMemory visit f memory
  if (← ops.tname mc).isSome then
    let some memory ← ops.tname mc | throw (.foreignError "TypeError" "expected Memory{Any}")
    avisit length isassigned getindex asMemory visit f memory
  if (← ops.name1 mc).isSome then
    let some memory ← ops.name1 mc | throw (.foreignError "TypeError" "expected Memory{Any}")
    avisit length isassigned getindex asMemory visit f memory
  if (← ops.list mc).isSome then
    let some value ← ops.list mc | throw (.jl (.methodError "visit"))
    visit f value
  if (← ops.any mc).isSome then
    let some value ← ops.any mc | throw (.jl (.methodError "visit"))
    visit f value

/--
Julia source: base/runtime_internals.jl:2044-2050 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function visit(f, d::Core.TypeMapEntry)
    while d !== nothing
        f(d.func)
        d = d.next
    end
    nothing
end
```
-/
def visitTypeMapEntry {World Function Entry Value Result : Type}
    (getFunc : Entry → M World Value) (getNext : Entry → M World (Option Entry))
    (call : Function → Value → M World Result) (f : Function) (d : Entry) : M World Unit := do
  whileLoop (fun cursor => do
    match cursor with
    | none => pure (.inl ())
    | some entry =>
      let _ ← call f (← getFunc entry)
      pure (.inr (← getNext entry))) (some d)

/--
Julia source: base/runtime_internals.jl:2051-2053 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct MethodSpecializations
    specializations::Union{Nothing, Core.MethodInstance, Core.SimpleVector}
end
```
-/
structure MethodSpecializations (Instance Vector : Type) where
  specializations : Option (Sum Instance Vector)

/--
Julia source: base/runtime_internals.jl:2059-2059 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
specializations(m::Method) = MethodSpecializations(isdefined(m, :specializations) ? m.specializations : nothing)
```
-/
def specializations {World Method Instance Vector : Type}
    (hasSpecializations : Method → M World Bool)
    (getSpecializations : Method → M World (Option (Sum Instance Vector)))
    (m : Method) : M World (MethodSpecializations Instance Vector) := do
  let value ← if ← hasSpecializations m then getSpecializations m else pure none
  pure ⟨value⟩

/--
Julia source: base/runtime_internals.jl:2067-2077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(specs::MethodSpecializations, i::Int)
    s = specs.specializations::Core.SimpleVector
    n = length(s)
    i >= n && return nothing
    item = nothing
    while i < n && item === nothing
        item = s[i+=1]
    end
    item === nothing && return nothing
    return (item, i)
end
```
-/
def iterateSpecializationsIndex {World Instance Vector Item : Type}
    (length : Vector → M World I) (getindex : Vector → I → M World (Option Item))
    (specs : MethodSpecializations Instance Vector) (index : I) : M World (Option (Item × I)) := do
  let some (.inr vector) := specs.specializations | throw (.foreignError "TypeError" "expected Core.SimpleVector")
  let n ← length vector
  if index.val ≥ n.val then return none
  let (index, item) ← whileLoop (fun state => do
    if state.1.val < n.val && state.2.isNone then
      let next := state.1 + i 1
      let item ← getindex vector next
      pure (.inr (next, item))
    else pure (.inl state)) (index, (none : Option Item))
  match item with
  | none => pure none
  | some value => pure (some (value, index))

/--
Julia source: base/runtime_internals.jl:2060-2065 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(specs::MethodSpecializations)
    s = specs.specializations
    s === nothing && return nothing
    isa(s, Core.MethodInstance) && return (s, nothing)
    return iterate(specs, 0)
end
```
-/
def iterateSpecializations {World Instance Vector Item : Type}
    (length : Vector → M World I) (getindex : Vector → I → M World (Option Item))
    (specs : MethodSpecializations Instance Vector) : M World (Option (Sum Instance Item × Option I)) := do
  match specs.specializations with
  | none => pure none
  | some (.inl mi) => pure (some (.inl mi, none))
  | some (.inr _) =>
    pure ((← iterateSpecializationsIndex length getindex specs (i 0)).map
      (fun (item, index) => (.inr item, some index)))

/--
Julia source: base/runtime_internals.jl:2066-2066 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(specs::MethodSpecializations, ::Nothing) = nothing
```
-/
def iterateSpecializationsNothing {Instance Vector Item : Type}
    (_specs : MethodSpecializations Instance Vector) (_state : Unit := ())
    : Option (Sum Instance Item × Option I) := none

/--
Julia source: base/runtime_internals.jl:2078-2078 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(specs::MethodSpecializations) = count(Returns(true), specs)
```
-/
def lengthSpecializations {World Instance Vector Item : Type}
    (count : (Item → Bool) → MethodSpecializations Instance Vector → M World I)
    (specs : MethodSpecializations Instance Vector) : M World I := count (fun _ => true) specs

-- Source context (iterator documentation)
-- Source: base/runtime_internals.jl:2054-2058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     specializations(m::Method) → itr
-- 
-- Return an iterator `itr` of all compiler-generated specializations of `m`.
-- """
-- /Source

/--
Julia source: base/runtime_internals.jl:2089-2091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uncompressed_ir(m::Method) = isdefined(m, :source) ? _uncompressed_ir(m) :
                             isdefined(m, :generator) ? error("Method is @generated; try `code_lowered` instead.") :
                             error("Code for this Method is not available.")
```
-/
def uncompressedIr {World Method Code : Type} (hasSource : Method → M World Bool)
    (hasGenerator : Method → M World Bool) (uncompress : Method → M World Code)
    (method : Method) : M World Code := do
  if ← hasSource method then return ← uncompress method
  if ← hasGenerator method then throw (.errorException "Method is @generated; try `code_lowered` instead.")
  throw (.errorException "Code for this Method is not available.")

/--
Julia source: base/runtime_internals.jl:2093-2093 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_image_globalref(m::Method) = ccall(:jl_ir_flag_has_image_globalref, Bool, (Any,), m.source)
```
-/
def hasImageGlobalref {World Method Source : Type} (source : Method → M World Source)
    (jlIrFlagHasImageGlobalref : Source → M World Bool) (method : Method) : M World Bool := do
  jlIrFlagHasImageGlobalref (← source method)

/-! ## Source context (documentation and declarations) -/
-- Source: base/runtime_internals.jl:1-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # name and module reflection
-- 
-- """
--     parentmodule(m::Module)::Module
-- 
-- Get a module's enclosing `Module`. `Main` is its own parent.
-- 
-- See also [`names`](@ref), [`nameof`](@ref), [`fullname`](@ref), [`@__MODULE__`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> parentmodule(Main)
-- Main
-- 
-- julia> parentmodule(Base.Broadcast)
-- Base
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:24-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     moduleroot(m::Module)::Module
-- 
-- Find the root module of a given module. This is the first module in the chain of
-- parent modules of `m` which is either a registered root module or which is its
-- own parent module.
-- """
-- /Source

-- Source: base/runtime_internals.jl:42-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     @__MODULE__ -> Module
-- 
-- Get the `Module` of the toplevel eval,
-- which is the `Module` code is currently being read from.
-- """
-- /Source

-- Source: base/runtime_internals.jl:51-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fullname(m::Module)
-- 
-- Get the fully-qualified name of a module as a tuple of symbols. For example,
-- 
-- # Examples
-- ```jldoctest
-- julia> fullname(Base.Iterators)
-- (:Base, :Iterators)
-- 
-- julia> fullname(Main)
-- (:Main,)
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:79-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     moduleloc(m::Module)::LineNumberNode
-- 
-- Get the location of the `module` definition.
-- """
-- /Source

-- Source: base/runtime_internals.jl:89-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     names(x::Module; all::Bool=false, imported::Bool=false, usings::Bool=false, world::UInt=Base.tls_world_age())::Vector{Symbol}
-- 
-- Get a vector of the public names of a `Module`, excluding deprecated names.
-- If `all` is true, then the list also includes non-public names defined in the module,
-- deprecated names, and compiler-generated names.
-- If `imported` is true, then names explicitly imported from other modules
-- are also included.
-- If `usings` is true, then names explicitly or implicitly imported via `using` are also included.
-- Names are returned in sorted order.
-- 
-- As a special case, all names defined in `Main` are considered \"public\",
-- since it is not idiomatic to explicitly mark names from `Main` as public.
-- 
-- The `world` argument controls the world age used to look up binding partitions, defaulting
-- to the current task's world age. Pass `world=Base.get_world_counter()` to include names
-- from the latest world.
-- 
-- !!! note
--     `sym ∈ names(SomeModule)` does *not* imply `isdefined(SomeModule, sym)`.
--     `names` may return symbols marked with `public` or `export`, even if
--     they are not defined in the module.
-- 
-- !!! warning
--     `names` may return duplicate names. The duplication happens, e.g. if an `import`ed name
--     conflicts with an already existing identifier.
-- 
-- !!! compat "Julia 1.12"
--     The `usings` argument requires Julia 1.12 or later.
-- 
-- See also [`Base.isexported`](@ref), [`Base.ispublic`](@ref), [`Base.@locals`](@ref), [`@__MODULE__`](@ref).
-- """
-- /Source

-- Source: base/runtime_internals.jl:126-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isexported(m::Module, s::Symbol)::Bool
-- 
-- Return whether a symbol is exported from a module.
-- 
-- See also [`ispublic`](@ref), [`names`](@ref).
-- 
-- ```jldoctest
-- julia> module Mod
--            export foo
--            public bar
--        end
-- Mod
-- 
-- julia> Base.isexported(Mod, :foo)
-- true
-- 
-- julia> Base.isexported(Mod, :bar)
-- false
-- 
-- julia> Base.isexported(Mod, :baz)
-- false
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:152-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     ispublic(m::Module, s::Symbol)::Bool
-- 
-- Return whether a symbol is marked as public in a module.
-- 
-- Exported symbols are considered public.
-- 
-- !!! compat "Julia 1.11"
--     This function and the notion of publicity were added in Julia 1.11.
-- 
-- See also [`isexported`](@ref), [`names`](@ref).
-- 
-- ```jldoctest
-- julia> module Mod
--            export foo
--            public bar
--        end
-- Mod
-- 
-- julia> Base.ispublic(Mod, :foo)
-- true
-- 
-- julia> Base.ispublic(Mod, :bar)
-- true
-- 
-- julia> Base.ispublic(Mod, :baz)
-- false
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:183-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @__FUNCTION__
-- 
-- Get the innermost enclosing function object.
-- 
-- !!! note
--     `@__FUNCTION__` has the same scoping behavior as `return`: when used
--     inside a closure, it refers to the closure and not the outer function.
--     Some macros, including [`@spawn`](@ref Threads.@spawn), [`@async`](@ref), etc.,
--     wrap their input in closures. When `@__FUNCTION__` is used within such code,
--     it will refer to the closure created by the macro rather than the enclosing function.
-- 
-- # Examples
-- 
-- `@__FUNCTION__` enables recursive anonymous functions:
-- 
-- ```jldoctest
-- julia> factorial = (n -> n <= 1 ? 1 : n * (@__FUNCTION__)(n - 1));
-- 
-- julia> factorial(5)
-- 120
-- ```
-- 
-- `@__FUNCTION__` can be combined with `nameof` to identify a function's
-- name from within its body:
-- 
-- ```jldoctest
-- julia> bar() = nameof(@__FUNCTION__);
-- 
-- julia> bar()
-- :bar
-- ```
-- 
-- !!! compat "Julia 1.13"
--     This macro requires at least Julia 1.13.
-- """
-- /Source

-- Source: base/runtime_internals.jl:223-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Reflects binding-partition deprecation (as set by `Base.deprecate` / `Base.@deprecate_binding`),
-- # including a binding reached through an implicit `using`, transparently through reexports.
-- # `@deprecate` deprecates a method rather than the binding, so it is intentionally not reported here.
-- /Source

-- Source: base/runtime_internals.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:234-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const _NAMEDTUPLE_NAME = NamedTuple.body.body.name
-- 
-- /Source

-- Source: base/runtime_internals.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:322-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     delete_binding(mod::Module, sym::Symbol)
-- 
-- Force the binding `mod.sym` to be undefined again, allowing it be redefined.
-- Note that this operation is very expensive, requiring a full scan of all code in the system,
-- as well as potential recompilation of any methods that (may) have used binding
-- information.
-- 
-- !!! warning
--     The implementation of this functionality is currently incomplete. Do not use
--     this method on versions that contain this disclaimer except for testing.
-- """
-- /Source

-- Source: base/runtime_internals.jl:337-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     set_binding_visibility!(mod::Module, sym::Symbol, vis::Symbol)
-- 
-- Select the declared visibility of `mod.sym`, one of `:export`, `:public`, or
-- `:none`. This is the programmatic counterpart to the `export` and `public`
-- keywords; unlike them it can also *retract* a declaration, since `:none`
-- removes a name's `export` or `public` status.
-- 
-- Retracting an `export` causes modules that did `using \$mod` to stop resolving
-- `sym` implicitly, once their world age advances past this call (see
-- [`invokelatest`](@ref) and [`get_world_counter`](@ref)). Because that
-- invalidates dependent compiled code, it can be expensive.
-- 
-- Unlike the exported flag, the public flag is not world-versioned: setting or
-- clearing it takes effect in every world age at once. Retracting to `:none`
-- therefore drops public status in all world ages, including ones in which the name
-- is declared public. Combined with the world-versioned export flag, this means an
-- older world age can still report a name as [`isexported`](@ref) while no longer
-- reporting it as [`ispublic`](@ref).
-- 
-- See also [`isexported`](@ref), [`ispublic`](@ref), [`delete_binding`](@ref).
-- 
-- !!! compat "Julia 1.14"
--     This function was added in Julia 1.14.
-- """
-- /Source

-- Source: base/runtime_internals.jl:371-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fieldname(x::DataType, i::Integer)
-- 
-- Get the name of field `i` of a `DataType`.
-- 
-- The return type is `Symbol`, except when `x <: Tuple`, in which case the index of the field is returned, of type `Int`.
-- 
-- # Examples
-- ```jldoctest
-- julia> fieldname(Rational, 1)
-- :num
-- 
-- julia> fieldname(Rational, 2)
-- :den
-- 
-- julia> fieldname(Tuple{String,Int}, 2)
-- 2
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:412-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fieldnames(x::DataType)
-- 
-- Get a tuple with the names of the fields of a `DataType`.
-- 
-- Each name is a `Symbol`, except when `x <: Tuple`, in which case each name (actually the
-- index of the field) is an `Int`.
-- 
-- See also [`propertynames`](@ref), [`hasfield`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> fieldnames(Rational)
-- (:num, :den)
-- 
-- julia> fieldnames(typeof(1+im))
-- (:re, :im)
-- 
-- julia> fieldnames(Tuple{String,Int})
-- (1, 2)
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:443-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     hasfield(T::Type, name::Symbol)
-- 
-- Return a boolean indicating whether `T` has `name` as one of its own fields.
-- 
-- See also [`fieldnames`](@ref), [`fieldcount`](@ref), [`hasproperty`](@ref).
-- 
-- !!! compat "Julia 1.2"
--      This function requires at least Julia 1.2.
-- 
-- # Examples
-- ```jldoctest
-- julia> struct Foo
--             bar::Int
--        end
-- 
-- julia> hasfield(Foo, :bar)
-- true
-- 
-- julia> hasfield(Foo, :x)
-- false
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:468-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     nameof(t::DataType)::Symbol
-- 
-- Get the name of a (potentially `UnionAll`-wrapped) `DataType` (without its parent module)
-- as a symbol.
-- 
-- # Examples
-- ```jldoctest
-- julia> module Foo
--            struct S{T}
--            end
--        end
-- Foo
-- 
-- julia> nameof(Foo.S{T} where T)
-- :S
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:489-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     parentmodule(t::DataType)::Module
-- 
-- Determine the module containing the definition of a (potentially `UnionAll`-wrapped) `DataType`.
-- 
-- # Examples
-- ```jldoctest
-- julia> module Foo
--            struct Int end
--        end
-- Foo
-- 
-- julia> parentmodule(Int)
-- Core
-- 
-- julia> parentmodule(Foo.Int)
-- Foo
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:511-521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isconst(m::Module, s::Symbol)::Bool
--     isconst(g::GlobalRef)::Bool
-- 
-- Determine whether a global is `const` in a given module `m`, either
-- because it was declared constant or because it was imported from a
-- constant binding. Note that constant-ness is specific to a particular
-- world age, so the result of this function may not be assumed to hold
-- after a world age update.
-- """
-- /Source

-- Source: base/runtime_internals.jl:524-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:528-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isconst(t::DataType, s::Union{Int,Symbol})::Bool
-- 
-- Determine whether a field `s` is const in a given type `t`
-- in the sense that a read from said field is consistent
-- for egal objects. Note in particular that out-of-bounds
-- fields are considered const under this definition (because
-- they always throw).
-- """
-- /Source

-- Source: base/runtime_internals.jl:558-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     isfieldatomic(t::DataType, s::Union{Int,Symbol})::Bool
-- 
-- Determine whether a field `s` is declared `@atomic` in a given type `t`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:582-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @locals()
-- 
-- Construct a dictionary of the names (as symbols) and values of all local
-- variables defined as of the call site.
-- 
-- !!! compat "Julia 1.1"
--     This macro requires at least Julia 1.1.
-- 
-- # Examples
-- ```jldoctest
-- julia> let x = 1, y = 2
--            Base.@locals
--        end
-- Dict{Symbol, Any} with 2 entries:
--   :y => 2
--   :x => 1
-- 
-- julia> function f(x)
--            local y
--            show(Base.@locals); println()
--            for i = 1:1
--                show(Base.@locals); println()
--            end
--            y = 2
--            show(Base.@locals); println()
--            nothing
--        end;
-- 
-- julia> f(42)
-- Dict{Symbol, Any}(:x => 42)
-- Dict{Symbol, Any}(:i => 1, :x => 42)
-- Dict{Symbol, Any}(:y => 2, :x => 42)
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:619-621 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # concrete datatype predicates
-- 
-- /Source

-- Source: base/runtime_internals.jl:623-623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:641-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:647-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.datatype_alignment(dt::DataType)::Int
-- 
-- Memory allocation minimum alignment for instances of this type.
-- Can be called on any `isconcretetype`, although for Memory it will give the
-- alignment of the elements, not the whole object.
-- """
-- /Source

-- Source: base/runtime_internals.jl:657-657 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:664-664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:666-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # amount of total space taken by T when stored in a container
-- /Source

-- Source: base/runtime_internals.jl:689-689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:692-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.datatype_haspadding(dt::DataType)::Bool
-- 
-- Return whether the fields of instances of this type are packed in memory,
-- with no intervening padding bits (defined as bits whose value does not impact
-- the semantic value of the instance itself).
-- Can be called on any `isconcretetype`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:703-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.datatype_isbitsegal(dt::DataType)::Bool
-- 
-- Return whether egality of the (non-padding bits of the) in-memory representation
-- of an instance of this type is equivalent to semantic egality of the instance itself.
-- This may not be the case if the type contains pointers to other values whose egality is
-- independent of their identity (e.g. immutable structs, some types, etc.).
-- """
-- /Source

-- Source: base/runtime_internals.jl:714-721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.datatype_nfields(dt::DataType)::UInt32
-- 
-- Return the number of fields known to this datatype's layout. This may be
-- different from the number of actual fields of the type for opaque types.
-- Can be called on any `isconcretetype`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:724-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.datatype_npointers(dt::DataType)::Int
-- 
-- Return the number of pointers in the layout of a datatype.
-- """
-- /Source

-- Source: base/runtime_internals.jl:732-738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.datatype_pointerfree(dt::DataType)::Bool
-- 
-- Return whether instances of this type can contain references to gc-managed memory.
-- Can be called on any `isconcretetype`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:743-752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.datatype_fielddesc_type(dt::DataType)::Int
-- 
-- Return the size in bytes of each field-description entry in the layout array,
-- located at `(dt.layout + sizeof(DataTypeLayout))`.
-- Can be called on any `isconcretetype`.
-- 
-- See also [`fieldoffset`](@ref).
-- """
-- /Source

-- Source: base/runtime_internals.jl:755-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.datatype_arrayelem(dt::DataType)::Int
-- 
-- Return the behavior of the trailing array types allocations.
-- Can be called on any `isconcretetype`, but only meaningful on `Memory`.
-- 
-- 0 = inlinealloc
-- 1 = isboxed
-- 2 = isbitsunion
-- """
-- /Source

-- Source: base/runtime_internals.jl:768-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:771-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # For type stability, we only expose a single struct that describes everything
-- /Source

-- Source: base/runtime_internals.jl:780-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:788-788 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:796-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:814-839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     ismutable(v)::Bool
-- 
-- Return `true` if and only if value `v` is mutable.  See [Mutable Composite Types](@ref)
-- for a discussion of immutability. Note that this function works on values, so if you
-- give it a `DataType`, it will tell you that a value of the type is mutable.
-- 
-- !!! note
--     For technical reasons, `ismutable` returns `true` for values of certain special types
--     (for example `String` and `Symbol`) even though they cannot be mutated in a permissible way.
-- 
-- See also [`isbits`](@ref), [`isstructtype`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> ismutable(1)
-- false
-- 
-- julia> ismutable([1,2])
-- true
-- ```
-- 
-- !!! compat "Julia 1.5"
--     This function requires at least Julia 1.5.
-- """
-- /Source

-- Source: base/runtime_internals.jl:841-853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # The type assertion above is required to fix some invalidations.
-- # See also https://github.com/JuliaLang/julia/issues/52134
-- 
-- """
--     ismutabletype(T)::Bool
-- 
-- Determine whether type `T` was declared as a mutable type
-- (i.e. using `mutable struct` keyword).
-- If `T` is not a type, then return `false`.
-- 
-- !!! compat "Julia 1.7"
--     This function requires at least Julia 1.7.
-- """
-- /Source

-- Source: base/runtime_internals.jl:860-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:862-869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isstructtype(T)::Bool
-- 
-- Determine whether type `T` was declared as a struct type
-- (i.e. using the `struct` or `mutable struct` keyword).
-- If `T` is not a type, then return `false`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:877-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isprimitivetype(T)::Bool
-- 
-- Determine whether type `T` was declared as a primitive type
-- (i.e. using the `primitive type` syntax).
-- If `T` is not a type, then return `false`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:892-916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isbitstype(T)
-- 
-- Return `true` if type `T` is a "plain data" type,
-- meaning it is immutable and contains no references to other values,
-- only `primitive` types and other `isbitstype` types.
-- Typical examples are numeric types such as [`UInt8`](@ref),
-- [`Float64`](@ref), and [`Complex{Float64}`](@ref).
-- This category of types is significant since they are valid as type parameters,
-- may not track [`isdefined`](@ref) / [`isassigned`](@ref) status,
-- and have a defined layout that is compatible with C.
-- If `T` is not a type, then return `false`.
-- 
-- See also [`isbits`](@ref), [`isprimitivetype`](@ref), [`ismutable`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> isbitstype(Complex{Float64})
-- true
-- 
-- julia> isbitstype(Complex)
-- false
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:918-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isbits(x)
-- 
-- Return `true` if `x` is an instance of an [`isbitstype`](@ref) type.
-- """
-- /Source

-- Source: base/runtime_internals.jl:925-935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     objectid(x)::UInt
-- 
-- Get a hash value for `x` based on object identity. This value is not unique nor
-- stable between Julia processes or versions.
-- 
-- If `x === y` then `objectid(x) == objectid(y)`, and usually when `x !== y`, `objectid(x) != objectid(y)`.
-- 
-- See also [`hash`](@ref), [`IdDict`](@ref).
-- """
-- /Source

-- Source: base/runtime_internals.jl:940-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isdispatchtuple(T)
-- 
-- Determine whether type `T` is a [`Tuple`](@ref) that could appear as a type
-- signature in dispatch.  For this to be true, every element of the tuple type
-- must be either:
-- - [concrete](@ref isconcretetype) but not a [kind type](@ref Base.iskindtype)
-- - the egality kind `Core.TypeEgal{U}` with no free type variables in `U` (a
--   `Type{U}` slot is not enough, since it also admits `==`-equal but non-`===`
--   argument values; `Type{Union{}}` is the exception, the bottom object being
--   unique)
-- 
-- !!! note
--     A dispatch tuple is relevant for method dispatch because it has no inhabited
--     subtypes.
-- 
--     For example, `Tuple{Int, DataType}` is concrete, but is not a dispatch tuple
--     because `Tuple{Int, Type{Bool}}` is an inhabited subtype.
-- 
--     `Tuple{Tuple{DataType}}` *is* a dispatch tuple because `Tuple{DataType}` is
--     concrete and not a kind; the subtype `Tuple{Tuple{Type{Int}}}` is not
--     inhabited.
-- 
-- If `T` is not a type, then return `false`.
-- 
-- # Examples
-- ```jldoctest
-- julia> isdispatchtuple(Int)
-- false
-- 
-- julia> isdispatchtuple(Tuple{Int})
-- true
-- 
-- julia> isdispatchtuple(Tuple{Number})
-- false
-- 
-- julia> isdispatchtuple(Tuple{DataType})
-- false
-- 
-- julia> isdispatchtuple(Tuple{Type{Int}})
-- false
-- 
-- julia> isdispatchtuple(Tuple{Core.TypeEgal{Int}})
-- true
-- 
-- julia> isdispatchtuple(Tuple{Type})
-- false
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:991-991 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:993-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.ismutationfree(T)
-- 
-- Determine whether type `T` is mutation free in the sense that no mutable memory
-- is reachable from this type (either in the type itself) or through any fields.
-- Note that the type itself need not be immutable. For example, an empty mutable
-- type is `ismutabletype`, but also `ismutationfree`.
-- If `T` is not a type, then return `false`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1016-1016 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1018-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.isidentityfree(T)
-- 
-- Determine whether type `T` is identity free in the sense that this type or any
-- reachable through its fields has non-content-based identity.
-- If `T` is not a type, then return `false`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1039-1048 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.iskindtype(T)
-- 
-- Determine whether `T` is a kind, that is, the type of a Julia type:
-- a [`DataType`](@ref), [`Union`](@ref), [`UnionAll`](@ref),
-- or [`Core.TypeofBottom`](@ref).
-- 
-- All kinds are [concrete](@ref isconcretetype) because types are Julia values.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1050-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.isconcretedispatch(T)
-- 
-- Return true if `T` is a [concrete type](@ref isconcretetype) that could appear
-- as an element of a [dispatch tuple](@ref isdispatchtuple).
-- 
-- See also [`isdispatchtuple`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> Base.isconcretedispatch(Int)
-- true
-- 
-- julia> Base.isconcretedispatch(Number)
-- false
-- 
-- julia> Base.isconcretedispatch(DataType)
-- false
-- 
-- julia> Base.isconcretedispatch(Type{Int})
-- false
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:1075-1079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- using Core: has_free_typevars
-- 
-- # equivalent to isa(v, Type) && isdispatchtuple(Tuple{v}) || v === Union{}
-- # and is thus perhaps most similar to the old (pre-1.0) `isconcretetype` query
-- /Source

-- Source: base/runtime_internals.jl:1084-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.isType(t)
-- 
-- Determine whether `t` is a kind whose values are Julia type objects. This is
-- true for both equality-keyed `Type{T}`/`TypeEq{T}` kinds and egality-keyed
-- `Core.TypeEgal{T}` kinds.
-- 
-- Use [`Base.isTypeEq`](@ref) or [`Base.isTypeEgal`](@ref) when the distinction
-- between equality and egality matters.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1096-1101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.isTypeEq(t)
-- 
-- Determine whether `t` is an equality-keyed `Type{T}`/`TypeEq{T}` kind.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1103-1108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.isTypeEgal(t)
-- 
-- Determine whether `t` is an egality-keyed `Core.TypeEgal{T}` kind.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1110-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1113-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isconcretetype(T)
-- 
-- Determine whether type `T` is a concrete type, meaning it could have direct instances
-- (values `x` such that `typeof(x) === T`).
-- Note that this is not the negation of `isabstracttype(T)`.
-- If `T` is not a type, then return `false`.
-- 
-- !!! note
--     While concrete types are not [abstract](@ref isabstracttype) and
--     vice versa, types can be neither concrete nor abstract (for example,
--     `Vector` (a [`UnionAll`](@ref))).
-- 
-- !!! note
--     `T` must be the exact type that would be returned from `typeof`.  It is
--     possible for a type `U` to exist such that `T == U`, `isconcretetype(T)`,
--     but `!isconcretetype(U)`.
-- 
-- See also [`isbits`](@ref), [`isabstracttype`](@ref), [`issingletontype`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> isconcretetype(Complex)
-- false
-- 
-- julia> isconcretetype(Complex{Float32})
-- true
-- 
-- julia> isconcretetype(Vector)
-- false
-- 
-- julia> isconcretetype(Vector{Complex})
-- true
-- 
-- julia> isconcretetype(Vector{Complex{Float32}})
-- true
-- 
-- julia> isconcretetype(Union{})
-- false
-- 
-- julia> isconcretetype(Union{Int,String})
-- false
-- 
-- julia> isconcretetype(Tuple{T} where T<:Int)
-- false
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:1162-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     isabstracttype(T)
-- 
-- Determine whether type `T` was declared as an abstract type
-- (i.e. using the `abstract type` syntax).
-- If `T` is not a type, then return `false`.
-- 
-- !!! note
--     While abstract types are not [concrete](@ref isconcretetype) and
--     vice versa, types can be neither concrete nor abstract (for example,
--     `Vector` (a [`UnionAll`](@ref))).
-- 
-- See also [`isconcretetype`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> isabstracttype(AbstractArray)
-- true
-- 
-- julia> isabstracttype(Vector)
-- false
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:1193-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1197-1197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1204-1211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.issingletontype(T)
-- 
-- Determine whether type `T` has exactly one possible instance; for example, a
-- struct type with no fields except other singleton values.
-- If `T` is not a concrete type, then return `false`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1213-1222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     typeintersect(T::Type, S::Type)
-- 
-- Compute a type that contains the intersection of `T` and `S`. Usually this will be the
-- smallest such type or one close to it.
-- 
-- A special case where exact behavior is guaranteed: when `T <: S`,
-- `typeintersect(S, T) == T == typeintersect(T, S)`.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1224-1224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1227-1272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fieldoffset(type, name::Symbol | i::Integer)
-- 
-- The byte offset of a field (specified by name or index) of a type relative to its start.
-- 
-- # Examples
-- ```jldoctest
-- julia> struct Foo
--            x::Int64
--            y::String
--        end
-- 
-- julia> fieldoffset(Foo, 2)
-- 0x0000000000000008
-- 
-- julia> fieldoffset(Foo, :x)
-- 0x0000000000000000
-- ```
-- 
-- We can use it to summarize information about a struct:
-- 
-- ```jldoctest
-- julia> structinfo(T) = [(fieldoffset(T,i), fieldname(T,i), fieldtype(T,i)) for i = 1:fieldcount(T)];
-- 
-- julia> structinfo(Base.Filesystem.StatStruct)
-- 14-element Vector{Tuple{UInt64, Symbol, Core.AnyType}}:
--  (0x0000000000000000, :desc, Union{RawFD, String})
--  (0x0000000000000008, :device, UInt64)
--  (0x0000000000000010, :inode, UInt64)
--  (0x0000000000000018, :mode, UInt64)
--  (0x0000000000000020, :nlink, Int64)
--  (0x0000000000000028, :uid, UInt64)
--  (0x0000000000000030, :gid, UInt64)
--  (0x0000000000000038, :rdev, UInt64)
--  (0x0000000000000040, :size, Int64)
--  (0x0000000000000048, :blksize, Int64)
--  (0x0000000000000050, :blocks, Int64)
--  (0x0000000000000058, :mtime, Float64)
--  (0x0000000000000060, :ctime, Float64)
--  (0x0000000000000068, :ioerrno, Int32)
-- ```
-- 
-- !!! compat "Julia 1.13"
--     Specifying the field by name rather than index requires Julia 1.13 or later.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1276-1325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fieldtype(T, name::Symbol | index::Int)
-- 
-- Determine the declared type of a field (specified by name or index) in a composite DataType `T`.
-- 
-- # Examples
-- ```jldoctest
-- julia> struct Foo
--            x::Int64
--            y::String
--        end
-- 
-- julia> fieldtype(Foo, :x)
-- Int64
-- 
-- julia> fieldtype(Foo, 2)
-- String
-- ```
-- """
-- fieldtype
-- 
-- """
--     fieldindex(T, name::Symbol, err:Bool=true)
-- 
-- Get the index of a named field, throwing an error if the field does not exist (when err==true)
-- or returning 0 (when err==false).
-- 
-- # Examples
-- ```jldoctest
-- julia> struct Foo
--            x::Int64
--            y::String
--        end
-- 
-- julia> fieldindex(Foo, :y)
-- 2
-- 
-- julia> fieldindex(Foo, :z)
-- ERROR: FieldError: type Foo has no field `z`, available fields: `x`, `y`
-- Stacktrace:
-- [...]
-- 
-- julia> fieldindex(Foo, :z, false)
-- 0
-- ```
-- 
-- !!! compat "Julia 1.13"
--     This function is exported as of Julia 1.13.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1329-1329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1335-1335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1341-1341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1345-1345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1349-1349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1363-1363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1375-1375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1397-1397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1410-1410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1425-1425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1439-1439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1456-1461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     fieldcount(t::Type)
-- 
-- Get the number of fields that an instance of the given type would have.
-- An error is thrown if the type is too abstract to determine this.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1488-1488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1492-1512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     fieldtypes(T::Type)
-- 
-- The declared types of all fields in a composite DataType `T` as a tuple.
-- 
-- !!! compat "Julia 1.1"
--     This function requires at least Julia 1.1.
-- 
-- # Examples
-- ```jldoctest
-- julia> struct Foo
--            x::Int64
--            y::String
--        end
-- 
-- julia> fieldtypes(Foo)
-- (Int64, String)
-- ```
-- """
-- /Source

-- Source: base/runtime_internals.jl:1515-1533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # return all instances, for types that can be enumerated
-- 
-- """
--     instances(T::Type)
-- 
-- Return a collection of all instances of the given type, if applicable. Mostly used for
-- enumerated types (see `@enum`).
-- 
-- # Examples
-- ```jldoctest
-- julia> @enum Color red blue green
-- 
-- julia> instances(Color)
-- (red, blue, green)
-- ```
-- """
-- function instances end
-- 
-- /Source

-- Source: base/runtime_internals.jl:1553-1553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1562-1562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1640-1652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     get_world_counter()
-- 
-- Return the current maximum world-age counter. This counter is monotonically
-- increasing.
-- 
-- !!! warning
--     This counter is global and may change at any time between invocations.
--     In general, most reflection functions operate on the current task's world
--     age, rather than the global maximum world age. See [`tls_world_age`](@ref)
--     as well as the [manual chapter of world age](@ref man-world-age).
-- """
-- /Source

-- Source: base/runtime_internals.jl:1654-1659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     tls_world_age()
-- 
-- Return the world the [`current_task`](@ref) is executing within.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1661-1661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1663-1678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     propertynames(x, private=false)
-- 
-- Get a tuple or a vector of the properties (`x.property`) of an object `x`.
-- This is typically the same as [`fieldnames(typeof(x))`](@ref), but types
-- that overload [`getproperty`](@ref) should generally overload `propertynames`
-- as well to get the properties of an instance of the type.
-- 
-- `propertynames(x)` may return only "public" property names that are part
-- of the documented interface of `x`.   If you want it to also return "private"
-- property names intended for internal use, pass `true` for the optional second argument.
-- REPL tab completion on `x.` shows only the `private=false` properties.
-- 
-- See also [`hasproperty`](@ref), [`hasfield`](@ref).
-- """
-- /Source

-- Source: base/runtime_internals.jl:1683-1693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     hasproperty(x, s::Symbol)
-- 
-- Return a boolean indicating whether the object `x` has `s` as one of its own properties.
-- 
-- !!! compat "Julia 1.2"
--      This function requires at least Julia 1.2.
-- 
-- See also [`propertynames`](@ref), [`hasfield`](@ref).
-- """
-- /Source

-- Source: base/runtime_internals.jl:1695-1700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     delete_method(m::Method)
-- 
-- Make method `m` uncallable and force recompilation of any methods that use(d) it.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1704-1706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # type for reflecting and pretty-printing a subset of methods
-- /Source

-- Source: base/runtime_internals.jl:1711-1711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1714-1714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1722-1722 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1732-1750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     methods(f, [types], [module])
-- 
-- Return the method table for `f`.
-- 
-- If `types` is specified, return an array of methods whose types match.
-- If `module` is specified, return an array of methods defined in that module.
-- A list of modules can also be specified as an array or set.
-- 
-- The methods are ordered from most to least specific. The relative order of
-- methods without a specificity relationship (i.e. ambiguous or incomparable)
-- is unspecified.
-- 
-- !!! compat "Julia 1.4"
--     At least Julia 1.4 is required for specifying a module.
-- 
-- See also [`which`](@ref), [`@which`](@ref Main.InteractiveUtils.@which), [`methodswith`](@ref Main.InteractiveUtils.methodswith).
-- """
-- /Source

-- Source: base/runtime_internals.jl:1759-1759 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1769-1769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1775-1777 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # low-level method lookup functions used by the compiler
-- 
-- /Source

-- Source: base/runtime_internals.jl:1832-1840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Return `true` if the current process is being used to pre-generate a
-- code cache via any of the `--output-*` command line arguments. The optional
-- `incremental` argument further specifies the precompilation mode: when set
-- to `true`, the function will return `true` only for package precompilation;
-- when set to `false`, it will return `true` only for system image generation.
-- 
-- !!! compat "Julia 1.11"
--     This function requires at least Julia 1.11.
-- """
-- /Source

-- Source: base/runtime_internals.jl:1848-1848 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:1998-1998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:2000-2006 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ###########
-- # scoping #
-- ###########
-- 
-- # high-level, more convenient method lookup functions
-- 
-- /Source

-- Source: base/runtime_internals.jl:2079-2079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/runtime_internals.jl:2086-2086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- /Source

-- Source: base/runtime_internals.jl:2088-2088 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


end JuliaLean.base.runtime_internals

section
namespace JuliaLean.RuntimeCov

/-- A Julia `Symbol`, modelled by its name. -/
abbrev Sym := String

/-- Exceptions thrown by the modelled methods, by Julia exception type. -/
inductive RtErr where
  | ioError (code : Int)
  | argumentError (msg : String)
  | boundsError
  | keyError
  | typeError
  | methodError
  | undefRefError
  | fieldError
  | inexactError
  | errorException (msg : String)
  deriving DecidableEq, Repr

/-- Result of a Julia call: a value or a thrown exception. -/
abbrev Rt (α : Type) := Except RtErr α

/-- `Base.uv_error(prefix, err)`: throws an `IOError` exactly when `err < 0`. -/
def uvError (err : Int) : Rt Unit :=
  if err < 0 then .error (.ioError err) else .ok ()

/-- `Base.UV_ENOENT` and `Base.UV_EACCES` (negated POSIX codes, libuv convention). -/
def UV_ENOENT : Int := -2
def UV_EACCES : Int := -13

/-- `lpad(s, n)` on ASCII text: left-pad with spaces to at least `n` characters. -/
def lpad (s : String) (n : Nat) : String :=
  String.ofList (List.replicate (n - s.length) ' ') ++ s
end JuliaLean.RuntimeCov
end

section
namespace JuliaLean.RuntimeCov.Layout

open JuliaLean.RuntimeCov

/-- `struct DataTypeLayout`, base/runtime_internals.jl:624-640. -/
structure DataTypeLayout where
  size : Nat
  nfields : Nat
  npointers : Nat
  firstptr : Int
  alignment : Nat
  flags : Nat
  deriving DecidableEq, Repr

/-- A `DataType` as far as the layout queries see it: `none` is a null
`layout` pointer. -/
structure DT where
  layout : Option DataTypeLayout
  fieldtypes : List String
  hasInstance : Bool
  isConcrete : Bool
  isArray : Bool
  deriving DecidableEq, Repr

/-- The Julia type of a returned integer (the docstrings declare result types). -/
inductive JNum where
  | int (n : Int)
  | uint32 (n : Nat)
  | uint16 (n : Nat)
  deriving DecidableEq, Repr

/-- `datatype_fieldtypes(x)`, line 622: the runtime's field-type vector. -/
def datatypeFieldtypes (dt : DT) : List String := dt.fieldtypes

/-- `DataTypeLayout(dt)`, lines 642-646. -/
def layoutOf (dt : DT) : Rt DataTypeLayout :=
  match dt.layout with
  | none => .error .undefRefError
  | some l => .ok l

/-- `datatype_alignment(dtl)`, line 656 (`Int(dtl.alignment)`), and the
`DataType` method, line 655. -/
def alignment (l : DataTypeLayout) : JNum := .int l.alignment
def alignmentDT (dt : DT) : Rt JNum := do let l ← layoutOf dt; pure (alignment l)

/-- `datatype_haspadding(dtl)`, line 702, and the `DataType` method, line 701. -/
def haspadding (l : DataTypeLayout) : Bool := l.flags % 2 == 1
def haspaddingDT (dt : DT) : Rt Bool := do let l ← layoutOf dt; pure (haspadding l)

/-- `datatype_isbitsegal(dtl)`, line 713, and line 712. -/
def isbitsegal (l : DataTypeLayout) : Bool := (l.flags / 128) % 2 != 0
def isbitsegalDT (dt : DT) : Rt Bool := do let l ← layoutOf dt; pure (isbitsegal l)

/-- `datatype_nfields(dtl)`, line 723 (the `UInt32` field), and line 722. -/
def nfields (l : DataTypeLayout) : JNum := .uint32 l.nfields
def nfieldsDT (dt : DT) : Rt JNum := do let l ← layoutOf dt; pure (nfields l)

/-- `datatype_npointers(dtl)`, line 731 (the `UInt32` field), and line 730. -/
def npointers (l : DataTypeLayout) : JNum := .uint32 l.npointers
def npointersDT (dt : DT) : Rt JNum := do let l ← layoutOf dt; pure (npointers l)

/-- `datatype_pointerfree(dt)`, lines 739-742. -/
def pointerfreeDT (dt : DT) : Rt Bool := do let l ← layoutOf dt; pure (l.npointers == 0)

/-- `datatype_fielddesc_type(dtl)`, line 754 (`(flags >> 1) & 3`), and line 753. -/
def fielddescType (l : DataTypeLayout) : Nat := (l.flags / 2) % 4
def fielddescTypeDT (dt : DT) : Rt Nat := do let l ← layoutOf dt; pure (fielddescType l)

/-- `datatype_arrayelem(dtl)`, line 767 (`(flags >> 3) & 3`), and line 766. -/
def arrayelem (l : DataTypeLayout) : Nat := (l.flags / 8) % 4
def arrayelemDT (dt : DT) : Rt Nat := do let l ← layoutOf dt; pure (arrayelem l)

/-- `datatype_layoutsize(dtl)`, line 770, and line 769. -/
def layoutsize (l : DataTypeLayout) : Nat := l.size
def layoutsizeDT (dt : DT) : Rt Nat := do let l ← layoutOf dt; pure (layoutsize l)

/-- `uniontype_layout(T)`, lines 658-663: the runtime's inline flag, size and alignment. -/
def uniontypeLayout (isinline : Bool) (sz al : Nat) : Bool × Nat × Nat := (isinline, sz, al)

/-- `LLT_ALIGN(x, sz)`, line 665: `(x + sz - 1) & -sz`, which for a power of
two `sz` clears the low bits of `x + sz - 1`. -/
def lltAlign (x sz : Nat) : Nat := (x + sz - 1) - (x + sz - 1) % sz

/-- What `aligned_sizeof` knows about `T`, lines 668-688. -/
inductive SizeQuery where
  | inlineUnion (sz al : Nat)
  | boxedUnion
  | inlineType (size al : Nat)
  | boxed
  deriving DecidableEq, Repr

/-- `aligned_sizeof(T)`, lines 668-688 (`Type{Union{}}` is handled as
`Core.TypeofBottom` by the caller of `inlineType`). -/
def alignedSizeof (ptrSize : Nat) : SizeQuery → Nat
  | .inlineUnion sz al => lltAlign sz al
  | .inlineType size al => lltAlign size al
  | .boxedUnion | .boxed => ptrSize

/-- `gc_alignment(sz)` and `gc_alignment(T)`, lines 690-691: the runtime's answer. -/
def gcAlignment (rt : Nat → Nat) (sz : Nat) : Nat := rt sz

/-- `struct FieldDesc` and `FieldDesc(fd::FieldDescStorage)`, lines 774-787. -/
structure FieldDesc where
  isforeign : Bool
  isptr : Bool
  size : Nat
  offset : Nat
  deriving DecidableEq, Repr

def fieldDescOf (ptrsize offset : Nat) : FieldDesc := ⟨false, ptrsize % 2 != 0, ptrsize / 2, offset⟩

/-- `DataTypeFieldDesc(dt)`, lines 791-794. -/
def mkDataTypeFieldDesc (dt : DT) : Rt DT :=
  match dt.layout with
  | none => .error .undefRefError
  | some _ => .ok dt

/-- `getindex(dtfd, i)`, lines 797-813: `entries` are the `(ptrsize, offset)`
pairs stored after the layout header. -/
def fieldDescAt (l : DataTypeLayout) (entries : List (Nat × Nat)) (i : Int) : Rt FieldDesc :=
  if ¬ (1 ≤ i ∧ i ≤ l.nfields) then .error .boundsError
  else if fielddescType l = 3 then .ok ⟨true, true, 0, 0⟩
  else match entries[(i - 1).toNat]? with
    | some (p, o) => .ok (fieldDescOf p o)
    | none => .error .boundsError

/-- `is_datatype_layoutopaque(dt)`, lines 1194-1196. -/
def isLayoutOpaque (l : DataTypeLayout) : Bool := l.nfields == 0 && l.npointers != 0

/-- `is_valid_intrinsic_elptr(ety)`, lines 1198-1203 (`isAny` for `ety === Any`). -/
def isValidIntrinsicElptr (isAny : Bool) (dt : DT) : Bool :=
  if isAny then true
  else if !dt.isConcrete then false
  else if dt.isArray then false
  else match dt.layout with
    | some l => !isLayoutOpaque l
    | none => false

/-- `issingletontype(t)`, line 1212. -/
def issingletontype (dt : DT) : Bool :=
  dt.hasInstance && match dt.layout with
    | some l => l.size == 0 && l.npointers == 0
    | none => false

/-- Bytes of one field-description entry: `FieldDescStorage{UInt8/16/32}` hold
two integers of 1, 2 or 4 bytes (codes 0, 1, 2). -/
def entryBytes : Nat → Nat
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | _ => 0
end JuliaLean.RuntimeCov.Layout
end

section
namespace JuliaLean.RuntimeCov.Fields

open JuliaLean.RuntimeCov

/-- A `Core.TypeName`: the fields the reflection code reads. -/
structure TName where
  name : Sym
  module : String
  names : List Sym
  isNamedTuple : Bool
  isTuple : Bool
  mutable : Bool
  abstract : Bool
  /-- `constfields`/`atomicfields` bitmaps as 0-based field indices; `none` is `C_NULL`. -/
  constfields : Option (List Nat)
  atomicfields : Option (List Nat)
  deriving DecidableEq, Repr

/-- A `DataType`. For `NamedTuple` types, `ntNames` is `parameters[1]` when it
is a tuple and `ntTypesCount` is `datatype_fieldcount(parameters[2])` when that
is a `Tuple` `DataType`. -/
structure DTy where
  tn : TName
  ntNames : Option (List Sym)
  ntTypesCount : Option Nat
  isvatuple : Bool
  ntypes : Nat
  deriving DecidableEq, Repr

inductive Ty where
  | dt (d : DTy)
  | union (a b : Ty)
  | unionAll (body : Ty)
  | bottom
  | typeEq
  | typeEgal (kind : DTy)
  | other
  deriving DecidableEq, Repr

/-- `unwrap_unionall(t)`. -/
def unwrap : Ty → Ty
  | .unionAll b => unwrap b
  | t => t

/-- `t isa Type{<:Tuple}` (`t <: Tuple`): the dispatch test for the tuple methods. -/
def isTupleType : Ty → Bool
  | .dt d => d.tn.isTuple
  | .union a b => isTupleType a && isTupleType b
  | .unionAll b => isTupleType b
  | .bottom => true
  | _ => false

/-! ## Names -/

/-- `_fieldnames(t)`, base/runtime_internals.jl:237-246. -/
def fieldnamesRaw (d : DTy) : Rt (List Sym) :=
  if d.tn.isNamedTuple then
    match d.ntNames with
    | some ns => .ok ns
    | none => .error (.argumentError "type does not have definite field names")
  else .ok d.tn.names

/-- `datatype_fieldcount(t)`, lines 1376-1396. -/
def datatypeFieldcount (d : DTy) : Option Nat :=
  if d.tn.isNamedTuple then
    match d.ntNames with
    | some ns => some ns.length
    | none => d.ntTypesCount
  else if d.tn.abstract then none
  else if d.tn.isTuple then (if d.isvatuple then none else some d.ntypes)
  else some d.tn.names.length

/-- `_typename_noerror(t)`, lines 1398-1409. -/
def typenameNoerror : Ty → Option TName
  | .unionAll b => typenameNoerror b
  | .dt d => some d.tn
  | .union a b =>
    match typenameNoerror a with
    | none => none
    | some an => if typenameNoerror b = some an then some an else none
  | _ => none

/-- `_fieldcount_noerror(t)`, lines 1440-1454. -/
def fieldcountNoerror : Ty → Option Nat
  | .bottom => some 0
  | .unionAll b => fieldcountNoerror b
  | .union a b =>
    if typenameNoerror (.union a b) = none then none
    else match fieldcountNoerror a with
      | none => none
      | some ac => if fieldcountNoerror b = some ac then some ac else none
  | .dt d => datatypeFieldcount d
  | _ => none

/-- `fieldcount_noerror(t)`, lines 1489-1491. -/
def fieldcountNoerrorPub (t : Ty) : Option Nat := fieldcountNoerror t

/-- `fieldcount(t)`, lines 1462-1487. -/
def fieldcount (t : Ty) : Rt Nat :=
  match t with
  | .bottom => .error (.argumentError "The empty type does not have a well-defined number of fields since it does not have instances.")
  | .typeEgal k => match datatypeFieldcount k with
    | some n => .ok n
    | none => .error (.argumentError "type does not have a definite number of fields")
  | _ =>
    match unwrap t with
    | .union a b => match fieldcountNoerror (.union a b) with
      | some n => .ok n
      | none => .error (.argumentError "type does not have a definite number of fields")
    | .typeEq => .error (.argumentError "type does not have a definite number of fields")
    | .dt d => match datatypeFieldcount d with
      | some n => .ok n
      | none => .error (.argumentError "type does not have a definite number of fields")
    | _ => .error .typeError

/-- `fieldname(t::DataType, i)`, lines 391-405, with its local helpers
`throw_not_def_field`, `throw_field_access`, `throw_need_pos_int` (392-397). -/
def fieldnameDT (d : DTy) (i : Int) : Rt Sym :=
  if d.tn.abstract then .error (.argumentError "type does not have definite field names")
  else do
    let names ← fieldnamesRaw d
    let n := names.length
    if i > n then .error (.argumentError ("Cannot access field " ++ toString i ++ " since type only has " ++ toString n ++ (if n == 1 then " field." else " fields.")))
    else if i < 1 then .error (.argumentError ("Field numbers must be positive integers. " ++ toString i ++ " is invalid."))
    else .ok (names.getD (i - 1).toNat "")

/-- The field "name" returned by `fieldname`: a `Symbol` or, for tuples, the index. -/
inductive FieldName where
  | sym (s : Sym)
  | idx (i : Int)
  deriving DecidableEq, Repr

/-- `fieldname(t, i)` over all methods, lines 391-411: the tuple method
(`Type{<:Tuple}`) is the most specific, then `DataType`, `UnionAll` (unwrap),
`Core.TypeEgal` (the kind of the parameter) and `TypeEq` (error). -/
def fieldname (t : Ty) (i : Int) : Rt FieldName :=
  if isTupleType t then do
    let n ← fieldcount t
    if i < 1 ∨ i > n then .error .boundsError else .ok (.idx i)
  else match t with
    | .dt d => FieldName.sym <$> fieldnameDT d i
    | .unionAll _ => match unwrap t with
      | .dt d => FieldName.sym <$> fieldnameDT d i
      | _ => .error .methodError
    | .typeEgal k => FieldName.sym <$> fieldnameDT k i
    | .typeEq => .error (.argumentError "type does not have definite field names")
    | _ => .error .methodError

/-- `fieldnames(t)` over all methods, lines 435-442. -/
def fieldnames (t : Ty) : Rt (List FieldName) :=
  match t with
  | .bottom => .error (.argumentError "The empty type does not have field names since it does not have instances.")
  | _ =>
    if isTupleType t then do
      let n ← fieldcount t
      pure ((List.range n).map fun (k : Nat) => .idx ((k : Int) + 1))
    else match t with
      | .typeEq => .error (.argumentError "type does not have a definite number of fields")
      | .typeEgal k => do let _ ← fieldcount (.dt k); let ns ← fieldnamesRaw k; pure (ns.map .sym)
      | _ => match unwrap t with
        | .dt d => do let _ ← fieldcount (.dt d); let ns ← fieldnamesRaw d; pure (ns.map .sym)
        | _ => .error .methodError

/-! ## Indices -/

/-- `jl_field_index(T, name, err)` for a `DataType`: the 0-based position in
its field names, `-1` if absent (an error when `err`). -/
def jlFieldIndex (d : DTy) (name : Sym) (err : Bool) : Rt Int :=
  match fieldnamesRaw d with
  | .error e => .error e
  | .ok ns =>
    match ns.idxOf? name with
    | some k => .ok k
    | none => if err then .error .fieldError else .ok (-1)

/-- `_fieldindex_maythrow` and `_fieldindex_nothrow`, lines 1330-1340, and
`fieldindex(T::DataType, name, err)`, lines 1326-1328. -/
def fieldindexDT (d : DTy) (name : Sym) (err : Bool) : Rt Int := do
  let k ← jlFieldIndex d name err
  pure (k + 1)

/-- `_fieldindex_noerror(t, name)`, lines 1426-1438. -/
def fieldindexNoerror (name : Sym) : Ty → Option Int
  | .unionAll b => fieldindexNoerror name b
  | .union a b =>
    if typenameNoerror (.union a b) = none then none
    else match fieldindexNoerror name a with
      | none => none
      | some ai => if fieldindexNoerror name b = some ai then some ai else none
  | .dt d => match fieldindexDT d name false with
    | .ok k => some k
    | .error _ => none
  | _ => none

/-- `_fieldindex_error_type(t)`, lines 1411-1424; `wrapper` is the type-name's
unwrapped `wrapper` when it is a `DataType`. -/
def fieldindexErrorType (wrapper : TName → Option DTy) (t : Ty) : Option DTy :=
  match unwrap t with
  | .dt d => if fieldcountNoerror (.dt d) = none then none else some d
  | .union a b => match typenameNoerror (.union a b) with
    | none => none
    | some tn => wrapper tn
  | _ => none

/-- `_fieldindex(t, name, err)`, lines 1350-1362. -/
def fieldindexGeneric (wrapper : TName → Option DTy) (t : Ty) (name : Sym) (err : Bool) : Rt Int :=
  match fieldindexNoerror name t with
  | none => if err then .error (.argumentError "type does not have definite fields") else .ok 0
  | some idx =>
    if idx = 0 ∧ err then
      match fieldindexErrorType wrapper t with
      | none => .error (.argumentError "type does not have definite fields")
      | some d => fieldindexDT d name true
    else .ok idx

/-- `fieldindex(t, name, err)` over all methods (lines 1326, 1342, 1346): only
`DataType`, `UnionAll` and `Union` have methods. -/
def fieldindex (wrapper : TName → Option DTy) (t : Ty) (name : Sym) (err : Bool) : Rt Int :=
  match t with
  | .dt d => fieldindexDT d name err
  | .unionAll _ | .union _ _ => fieldindexGeneric wrapper t name err
  | _ => .error .methodError

/-- `hasfield(T, name)`, line 467. -/
def hasfield (wrapper : TName → Option DTy) (t : Ty) (name : Sym) : Rt Bool := do
  let k ← fieldindex wrapper t name false
  pure (k > 0)

/-- `argument_datatype(t)` and `argument_datatypename(t)`, lines 1364-1374: the
runtime's answer. -/
def argumentDatatype {α : Type} (rt : Ty → Option α) (t : Ty) : Option α := rt t

/-! ## Names and modules of types -/

/-- `nameof(t::DataType)`, `nameof(t::UnionAll)`, lines 487-488. -/
def nameof (t : Ty) : Rt Sym :=
  match unwrap t with
  | .dt d => .ok d.tn.name
  | _ => .error .methodError

/-- `parentmodule(t::DataType)`, `parentmodule(t::UnionAll)`, lines 509-510. -/
def parentmoduleT (t : Ty) : Rt String :=
  match unwrap t with
  | .dt d => .ok d.tn.module
  | _ => .error .methodError

/-! ## Field constness and atomicity -/

/-- `isconst(t::Type, s::Int)`, lines 544-555. -/
def isconstIdx (t : Ty) (s : Int) : Bool :=
  match unwrap t with
  | .dt d =>
    if !d.tn.mutable then true
    else if ¬ (1 ≤ s ∧ s ≤ d.tn.names.length) then true
    else match d.tn.constfields with
      | none => false
      | some cs => (s - 1).toNat ∈ cs
  | _ => false

/-- `isconst(t::Type, s::Symbol)`, lines 538-543. -/
def isconstSym (t : Ty) (s : Sym) : Rt Bool :=
  match unwrap t with
  | .dt d => do let k ← fieldindexDT d s false; pure (isconstIdx (.dt d) k)
  | _ => .ok false

/-- `isfieldatomic(t::Type, s::Int)`, lines 568-579. -/
def isfieldatomicIdx (t : Ty) (s : Int) : Bool :=
  match unwrap t with
  | .dt d =>
    if !d.tn.mutable then false
    else if ¬ (1 ≤ s ∧ s ≤ d.tn.names.length) then false
    else match d.tn.atomicfields with
      | none => false
      | some cs => (s - 1).toNat ∈ cs
  | _ => false

/-- `isfieldatomic(t::Type, s::Symbol)`, lines 562-567. -/
def isfieldatomicSym (t : Ty) (s : Sym) : Rt Bool :=
  match unwrap t with
  | .dt d => do let k ← fieldindexDT d s false; pure (isfieldatomicIdx (.dt d) k)
  | _ => .ok false

/-! ## Offsets and field types -/

/-- `fieldoffset(x::DataType, idx)`, line 1273: the runtime's offset. -/
def fieldoffsetIdx (offset : DTy → Int → Nat) (d : DTy) (i : Int) : Nat := offset d i
/-- `fieldoffset(x::DataType, name)`, line 1274. -/
def fieldoffsetName (offset : DTy → Int → Nat) (d : DTy) (name : Sym) : Rt Nat := do
  let k ← fieldindexDT d name true
  pure (offset d k)
/-- `fieldoffset(x::Core.TypeEgal, idx)`, line 1275: the offset in `typeof(T)`. -/
def fieldoffsetEgal (offset : DTy → Int → Nat) (kind : DTy) (i : Int) : Nat := offset kind i

/-- `fieldtypes(T)`, lines 1513-1514: `fieldtype(T, i)` for `i in 1:fieldcount(T)`. -/
def fieldtypes {τ : Type} (fieldtype : Ty → Nat → τ) (t : Ty) : Rt (List τ) := do
  let n ← fieldcount t
  pure ((List.range n).map fun k => fieldtype t (k + 1))

/-! ## Properties of values -/

/-- What `propertynames` dispatches on, lines 1679-1682. -/
inductive Val where
  | module (names : List Sym)
  | array
  | other (t : Ty)

/-- `propertynames(x)`, `propertynames(m::Module)`, `propertynames(x::Array)`,
and `propertynames(x, private)` (which ignores the flag). -/
def propertynames (x : Val) : Rt (List FieldName) :=
  match x with
  | .module ns => .ok (ns.map .sym)
  | .array => .ok []
  | .other t => fieldnames t
def propertynamesPrivate (x : Val) (_private : Bool) : Rt (List FieldName) := propertynames x

/-- `hasproperty(x, s)`, line 1694. -/
def hasproperty (x : Val) (s : Sym) : Rt Bool := do
  let ps ← propertynames x
  pure (ps.contains (.sym s))

/-! ## Proven properties -/

def sampleTN (names : List Sym) (mutable : Bool) (cf af : Option (List Nat)) : TName :=
  ⟨"T", "Main", names, false, false, mutable, false, cf, af⟩
end JuliaLean.RuntimeCov.Fields
end

section
namespace JuliaLean.RuntimeCov.Modules

open JuliaLean.RuntimeCov

/-- A `Module`: a root (its own parent) or a submodule of `parent`. -/
inductive Mod where
  | root (name : Sym)
  | child (name : Sym) (parent : Mod)
  deriving DecidableEq, Repr

/-- `parentmodule(m::Module)`, line 21 (`jl_module_parent`). -/
def parentmodule : Mod → Mod
  | .root n => .root n
  | .child _ p => p

/-- `nameof(m::Module)`. -/
def nameofM : Mod → Sym
  | .root n => n
  | .child n _ => n

/-- `is_root_module(m)`, line 23: `isCompiler m` is `m === Compiler`,
`isMainBase m` is `isdefined(Main, :Base) && m === Main.Base`. -/
def isRootModule (isCompiler isMainBase : Mod → Bool) (m : Mod) : Bool :=
  decide (parentmodule m = m) || isCompiler m || isMainBase m

/-- `moduleroot(m)`, lines 32-40. -/
def moduleroot (isRoot : Mod → Bool) : Mod → Mod
  | m@(.root _) => if isRoot m then m else m
  | m@(.child _ p) => if isRoot m then m else moduleroot isRoot p

/-- `fullname(m)`, lines 66-77: `special m` is `m === Main || m === Base || m === Core`. -/
def fullname (special : Mod → Bool) : Mod → List Sym
  | m@(.root n) => if special m then [n] else [n]
  | m@(.child n p) => if special m then [n] else fullname special p ++ [n]

/-- The chain `m, parentmodule(m), ...` up to a root. -/
def chain : Mod → List Mod
  | m@(.root _) => [m]
  | m@(.child _ p) => m :: chain p

/-- `moduleloc(m)`, lines 84-88: `jl_module_getloc` returns the file and fills `line`. -/
structure LineNumberNode where
  line : Int
  file : Sym
  deriving DecidableEq, Repr

def moduleloc (getloc : Mod → Sym × Int) (m : Mod) : LineNumberNode :=
  let r := getloc m
  ⟨r.2, r.1⟩

/-- `unsorted_names(m; all, imported, usings, world)`, lines 123-125, and
`names(m; kwargs...)`, line 122 (`sort!` with the `Symbol` order `le`). -/
structure NamesOpts where
  all : Bool := false
  imported : Bool := false
  usings : Bool := false
  world : Nat
  deriving DecidableEq, Repr

def unsortedNames (jlNames : Mod → NamesOpts → List Sym) (m : Mod) (o : NamesOpts) : List Sym :=
  jlNames m o

def names (le : Sym → Sym → Bool) (jlNames : Mod → NamesOpts → List Sym) (m : Mod) (o : NamesOpts) :
    List Sym :=
  (unsortedNames jlNames m o).mergeSort le

/-- `isexported`, `ispublic`, `isdeprecated`, lines 151, 182, 227: the `Cint` answer `!= 0`. -/
def cintBool (r : Int) : Bool := r != 0
def isexported (q : Mod → Sym → Int) (m : Mod) (s : Sym) : Bool := cintBool (q m s)
def ispublic (q : Mod → Sym → Int) (m : Mod) (s : Sym) : Bool := cintBool (q m s)
def isdeprecated (q : Mod → Sym → Int) (m : Mod) (s : Sym) : Bool := cintBool (q m s)

/-- `binding_module(m, s)`, lines 229-233: a null owner pointer means `m` itself. -/
def bindingModule (owner : Mod → Sym → Option Mod) (m : Mod) (s : Sym) : Mod :=
  match owner m s with
  | none => m
  | some p => p

/-- `@__MODULE__`, lines 48-50, and `@__FUNCTION__`, `@locals` (lines 220-222, 616-618):
the expansion. -/
inductive MacroOut where
  | module (m : Mod)
  | expr (head : Sym)
  deriving DecidableEq, Repr

def atModule (callerModule : Mod) : MacroOut := .module callerModule
def atFunction : MacroOut := .expr "thisfunction"
def atLocals : MacroOut := .expr "locals"

/-! ## Binding partitions -/

def PARTITION_KIND_CONST : Nat := 0x0
def PARTITION_KIND_CONST_IMPORT : Nat := 0x1
def PARTITION_KIND_GLOBAL : Nat := 0x2
def PARTITION_KIND_IMPLICIT_GLOBAL : Nat := 0x3
def PARTITION_KIND_IMPLICIT_CONST : Nat := 0x4
def PARTITION_KIND_EXPLICIT : Nat := 0x5
def PARTITION_KIND_IMPORTED : Nat := 0x6
def PARTITION_KIND_FAILED : Nat := 0x7
def PARTITION_KIND_DECLARED : Nat := 0x8
def PARTITION_KIND_GUARD : Nat := 0x9
def PARTITION_KIND_UNDEF_CONST : Nat := 0xa
def PARTITION_KIND_BACKDATED_CONST : Nat := 0xb
def PARTITION_MASK_KIND : Nat := 0x0f

/-- Lines 275-283. -/
def isDefinedConstBinding (k : Nat) : Bool :=
  k == PARTITION_KIND_CONST || k == PARTITION_KIND_CONST_IMPORT ||
    k == PARTITION_KIND_IMPLICIT_CONST || k == PARTITION_KIND_BACKDATED_CONST
def isSomeConstBinding (k : Nat) : Bool := isDefinedConstBinding k || k == PARTITION_KIND_UNDEF_CONST
def isSomeImported (k : Nat) : Bool :=
  k == PARTITION_KIND_IMPLICIT_GLOBAL || k == PARTITION_KIND_IMPLICIT_CONST ||
    k == PARTITION_KIND_EXPLICIT || k == PARTITION_KIND_IMPORTED
def isSomeImplicit (k : Nat) : Bool :=
  k == PARTITION_KIND_IMPLICIT_GLOBAL || k == PARTITION_KIND_IMPLICIT_CONST ||
    k == PARTITION_KIND_GUARD || k == PARTITION_KIND_FAILED
def isSomeExplicitImported (k : Nat) : Bool := k == PARTITION_KIND_EXPLICIT || k == PARTITION_KIND_IMPORTED
def isSomeBindingImported (k : Nat) : Bool := isSomeExplicitImported k || k == PARTITION_KIND_IMPLICIT_GLOBAL
def isSomeGuard (k : Nat) : Bool :=
  k == PARTITION_KIND_GUARD || k == PARTITION_KIND_FAILED || k == PARTITION_KIND_UNDEF_CONST
def isSomeGlobal (k : Nat) : Bool := k == PARTITION_KIND_GLOBAL || k == PARTITION_KIND_DECLARED

/-- A `Core.BindingPartition` (its `kind` word) and the chain behind it: the
oldest partition's `next` is the owning `Core.Binding`. -/
structure Binding where
  id : Nat
  deriving DecidableEq, Repr

inductive PartNext where
  | binding (b : Binding)
  | part (kind : Nat) (next : PartNext)
  deriving DecidableEq, Repr

structure BPart where
  kind : Nat
  next : PartNext
  deriving DecidableEq, Repr

/-- The `while next isa Core.BindingPartition` walk of `partition_owner`. -/
def ownerWalk : PartNext → Binding
  | .binding b => b
  | .part _ n => ownerWalk n

/-- `partition_owner(bpart)`, lines 311-317. -/
def partitionOwner (p : BPart) : Binding := ownerWalk p.next

/-- `binding_kind(bpart)`, line 319. -/
def bindingKind (p : BPart) : Nat := p.kind &&& PARTITION_MASK_KIND

/-- A `GlobalRef`: module, name and the cached binding when `isdefined(gr, :binding)`. -/
structure GlobalRef where
  mod : Mod
  name : Sym
  binding : Option Binding
  deriving DecidableEq, Repr

/-- `lookup_binding_partition(world, b)` and the hinted form, lines 285-291:
runtime lookups. -/
def lookupBindingPartition (get : Nat → Binding → BPart) (world : Nat) (b : Binding) : BPart := get world b
def lookupBindingPartitionHint (get : Nat → Binding → BPart → BPart) (world : Nat) (b : Binding)
    (prev : BPart) : BPart := get world b prev

/-- `convert(::Type{Core.Binding}, gr)`, lines 293-299. -/
def convertBinding (moduleBinding : Mod → Sym → Binding) (gr : GlobalRef) : Binding :=
  match gr.binding with
  | some b => b
  | none => moduleBinding gr.mod gr.name

/-- `lookup_binding_partition(world, gr)`, lines 301-304. -/
def lookupBindingPartitionGR (moduleBinding : Mod → Sym → Binding) (get : Nat → Binding → BPart)
    (world : Nat) (gr : GlobalRef) : BPart :=
  let b := convertBinding moduleBinding gr
  lookupBindingPartition get world b

/-- `partition_restriction(bpart)`, line 306: the runtime's restriction value. -/
def partitionRestriction {α : Type} (restriction : BPart → α) (p : BPart) : α := restriction p

/-- `binding_kind(m, s)`, line 320: `GlobalRef(m, s)` carries no cached binding. -/
def bindingKindMS (moduleBinding : Mod → Sym → Binding) (get : Nat → Binding → BPart)
    (tlsWorld : Nat) (m : Mod) (s : Sym) : Nat :=
  bindingKind (lookupBindingPartitionGR moduleBinding get tlsWorld ⟨m, s, none⟩)

/-- Runtime calls issued by the binding mutators. -/
inductive Call where
  | disableBinding (gr : GlobalRef)
  | setVisibility (m : Mod) (s : Sym) (state : Int)
  deriving DecidableEq, Repr

/-- `delete_binding(mod, sym)`, lines 334-336. -/
def deleteBinding (m : Mod) (s : Sym) : Call := .disableBinding ⟨m, s, none⟩

/-- `set_binding_visibility!(mod, sym, vis)`, lines 363-370. -/
def setBindingVisibility (m : Mod) (s : Sym) (vis : Sym) : Rt Call :=
  if vis = "none" then .ok (.setVisibility m s 0)
  else if vis = "public" then .ok (.setVisibility m s 1)
  else if vis = "export" then .ok (.setVisibility m s 2)
  else .error (.argumentError ("visibility must be :none, :public, or :export, got :" ++ vis))

/-! ## World ages -/

/-- `get_world_counter()`, `tls_world_age()`, `get_require_world()`, lines 1653-1662. -/
def getWorldCounter (rt : Nat) : Nat := rt
def tlsWorldAge (rt : Nat) : Nat := rt
def getRequireWorld (global : Nat) : Nat := global

/-- `min_world`/`max_world` of a `CodeInstance` or `CodeInfo`, lines 1636-1639. -/
structure WorldRange where
  min_world : Nat
  max_world : Nat
  deriving DecidableEq, Repr

def minWorldCI (c : WorldRange) : Nat := c.min_world
def maxWorldCI (c : WorldRange) : Nat := c.max_world
def minWorldInfo (c : WorldRange) : Nat := c.min_world
def maxWorldInfo (c : WorldRange) : Nat := c.max_world
end JuliaLean.RuntimeCov.Modules
end

section
namespace JuliaLean.RuntimeCov.TypePreds

open JuliaLean.RuntimeCov

/-- The seven kind objects that `iskindtype` names (line 1049). -/
inductive Kind where
  | anyType | dataType | unionAll | union | typeEq | typeEgal | typeofBottom
  deriving DecidableEq, Repr

/-- A `DataType`: `flags` is `dt.flags`, `nameFlags` is `dt.name.flags`, and
`kind` says whether this object is one of the kind types. -/
structure DT where
  flags : Nat
  nameFlags : Nat
  kind : Option Kind
  hasInstance : Bool
  deriving DecidableEq, Repr

inductive Ty where
  | dt (d : DT) (params : List Ty)
  | union (a b : Ty)
  | unionAll (v : Sym) (lb ub : Ty) (body : Ty)
  | tvar (v : Sym) (lb ub : Ty)
  | bottom
  | typeEq (T : Ty)
  | typeEgal (T : Ty)
  | vararg (T : Ty)
  | value (id : Nat)
  deriving Repr

/-- `unwrap_unionall(t)`. -/
def unwrap : Ty → Ty
  | .unionAll _ _ _ b => unwrap b
  | t => t

/-- `isa(t, Type)` (equivalently `isa(t, Core.AnyType)`). -/
def isTypeVal : Ty → Bool
  | .dt _ _ | .union _ _ | .unionAll _ _ _ _ | .bottom | .typeEq _ | .typeEgal _ => true
  | _ => false

def bit (w m : Nat) : Bool := w &&& m == m

/-! ## Flag predicates -/

/-- `ismutabletypename(tn)`, line 861. -/
def ismutabletypename (nameFlags : Nat) : Bool := bit nameFlags 0x2

/-- `ismutable(x)`, line 840: `typeofV x` is `typeof(x)`. -/
def ismutable (typeofV : Ty → DT) (x : Ty) : Bool := bit (typeofV x).nameFlags 0x2

/-- `ismutabletype(t)`, lines 854-859. -/
def ismutabletype (t : Ty) : Bool :=
  match unwrap t with
  | .dt d _ => ismutabletypename d.nameFlags
  | _ => false

/-- `isTypeEq`, `isTypeEgal`, `isType`, lines 1095-1109. -/
def isTypeEq : Ty → Bool | .typeEq _ => true | _ => false
def isTypeEgal : Ty → Bool | .typeEgal _ => true | _ => false
def isType (t : Ty) : Bool := isTypeEq t || isTypeEgal t

/-- `type_parameter(t::TypeEq)`, `type_parameter(t::Core.TypeEgal)`, lines 1111-1112. -/
def typeParameter : Ty → Rt Ty
  | .typeEq T => .ok T
  | .typeEgal T => .ok T
  | _ => .error .methodError

/-- `isprimitivetype(t)`, lines 885-891. -/
def isprimitivetype (t : Ty) : Bool :=
  match unwrap t with
  | .dt d _ => bit d.flags 0x0080
  | _ => false

/-- `isabstracttype(t)`, lines 1186-1192. -/
def isabstracttype (t : Ty) : Bool :=
  let t := unwrap t
  if isType t then true
  else match t with
    | .dt d _ => bit d.nameFlags 0x1
    | _ => false

/-- `isstructtype(t)`, lines 870-876. -/
def isstructtype (t : Ty) : Bool :=
  match unwrap t with
  | .dt d ps => !isprimitivetype (.dt d ps) && !isabstracttype (.dt d ps)
  | _ => false

/-- `isbitstype(t)`, line 917, and `isbits(x)`, line 924. -/
def isbitstype : Ty → Bool
  | .dt d _ => bit d.flags 0x0008
  | _ => false
def isbits (typeofV : Ty → DT) (x : Ty) : Bool := isbitstype (.dt (typeofV x) [])

/-- `objectid(x)`, lines 936-939: `jl_object_id`. -/
def objectid (oid : Ty → Nat) (x : Ty) : Nat := oid x

/-- `isdispatchtuple(t)`, line 990, and `isconcretetype(t)`, line 1161. -/
def isdispatchtuple : Ty → Bool
  | .dt d _ => bit d.flags 0x0004
  | _ => false
def isconcretetype : Ty → Bool
  | .dt d _ => bit d.flags 0x0002
  | _ => false

/-- `datatype_ismutationfree`, `datatype_isidentityfree`, lines 992, 1017. -/
def datatypeIsmutationfree (d : DT) : Bool := bit d.flags 0x0100
def datatypeIsidentityfree (d : DT) : Bool := bit d.flags 0x0200

/-- `ismutationfree(t)`, lines 1003-1015: the `t = unwrap_unionall(t)` step is the
`UnionAll` clause; `kindOf T` is `typeof(T)`, a `DataType`, on which the
function reads `datatype_ismutationfree`. -/
def ismutationfree (kindOf : Ty → DT) : Ty → Bool
  | .unionAll _ _ _ b => ismutationfree kindOf b
  | .dt d _ => datatypeIsmutationfree d
  | .typeEq T | .typeEgal T => isTypeVal T && datatypeIsmutationfree (kindOf T)
  | .union a b => ismutationfree kindOf a && ismutationfree kindOf b
  | _ => false

/-- `isidentityfree(t)`, lines 1026-1038. -/
def isidentityfree (kindOf : Ty → DT) : Ty → Bool
  | .unionAll _ _ _ b => isidentityfree kindOf b
  | .dt d _ => datatypeIsidentityfree d
  | .typeEq T | .typeEgal T => isTypeVal T && datatypeIsidentityfree (kindOf T)
  | .union a b => isidentityfree kindOf a && isidentityfree kindOf b
  | _ => false

/-- `iskindtype(t)`, line 1049: `t` is one of the seven kind objects. -/
def iskindtype : Ty → Bool
  | .dt d _ => d.kind.isSome
  | _ => false

/-- `isconcretedispatch(t)`, line 1074. -/
def isconcretedispatch (t : Ty) : Bool := isconcretetype t && !iskindtype t

/-- `v === Union{}`. -/
def isBottom : Ty → Bool | .bottom => true | _ => false

def isTypeofBottom : Ty → Bool
  | .dt d _ => d.kind == some .typeofBottom
  | _ => false

/-- `isdispatchelem(v)`, lines 1080-1083. -/
def isdispatchelem (v : Ty) : Bool :=
  isBottom v || isTypeofBottom v || isconcretedispatch v || isTypeEgal v ||
    (isTypeEq v && (match typeParameter v with | .ok T => isBottom T | .error _ => false))

/-! ## The kind objects -/

/-- The kind `DataType`s as the runtime creates them (src/jltypes.c):
`Core.AnyType` comes from `jl_new_abstracttype`; the other six are concrete
struct types (`DataType` is mutable). -/
def kindDT : Kind → DT
  | .anyType => ⟨0x0, 0x1, some .anyType, false⟩
  | .dataType => ⟨0x2, 0x2, some .dataType, false⟩
  | k => ⟨0x2, 0x0, some k, false⟩

def kindType (k : Kind) : Ty := .dt (kindDT k) []
end JuliaLean.RuntimeCov.TypePreds
end

section
namespace JuliaLean.RuntimeCov.TypePreds

open JuliaLean.RuntimeCov
mutual
/-- `has_bottom_parameter(t::Core.AnyType)`, `(t::TypeVar)`, `(::Any)`,
lines 1576-1593.  The `UnionAll` clause recurses through `unwrap_unionall`. -/
def hasBottomParameter : Ty → Bool
  | .bottom => true
  | .dt _ ps => hasBottomParams ps
  | .typeEq T => hasBottomParameter T
  | .typeEgal T => hasBottomParameter T
  | .unionAll _ _ _ b => hasBottomParameter b
  | .union a b => hasBottomParameter a && hasBottomParameter b
  | .tvar _ _ ub => hasBottomParameter ub
  | _ => false
/-- The `for p in getfield(t, :parameters)` loop. -/
def hasBottomParams : List Ty → Bool
  | [] => false
  | p :: ps => hasBottomParameter p || hasBottomParams ps
end
end JuliaLean.RuntimeCov.TypePreds
end

section
namespace JuliaLean.RuntimeCov.TypePreds

open JuliaLean.RuntimeCov

/-- `unionlen(x)`, line 1778. -/
def unionlen : Ty → Nat
  | .union a b => unionlen a + unionlen b
  | _ => 1

/-- `_uniontypes(x, ts)`, lines 1780-1788, and `uniontypes(x)`, line 1789. -/
def uniontypesAcc : Ty → List Ty → List Ty
  | .union a b, ts => uniontypesAcc b (uniontypesAcc a ts)
  | x, ts => ts ++ [x]
def uniontypes (x : Ty) : List Ty := uniontypesAcc x []

/-- `find_free_typevars(t)`, lines 1595-1597: the runtime's list. -/
def findFreeTypevars (rt : Ty → List (Sym × Ty × Ty)) (t : Ty) : List (Sym × Ty × Ty) := rt t

def isvarargtype : Ty → Bool | .vararg _ => true | _ => false

/-- `rewrap_free_typevars(t, pre)`, lines 1612-1629: the loop runs from the last
free variable to the first, wrapping each one not in `pre`. -/
def rewrapFreeTypevars (hasFree : Ty → Bool) (ffv : Ty → List (Sym × Ty × Ty)) (t : Ty)
    (pre : List Sym) : Ty :=
  if !hasFree t then t
  else if isvarargtype t then t
  else
    (findFreeTypevars ffv t).reverse.foldl
      (fun acc (v : Sym × Ty × Ty) => if pre.contains v.1 then acc else .unionAll v.1 v.2.1 v.2.2 acc) t

/-- `typeintersect(a, b)`, line 1223: both arguments must be types. -/
def typeintersect (rt : Ty → Ty → Ty) (a b : Ty) : Rt Ty :=
  if isTypeVal a && isTypeVal b then .ok (rt a b) else .error .typeError

/-- `morespecific(a, b)` on types and on methods, lines 1225-1226. -/
def morespecific (rt : Ty → Ty → Int) (a b : Ty) : Rt Bool :=
  if isTypeVal a && isTypeVal b then .ok (rt a b != 0) else .error .typeError
def morespecificMethod (rt : Nat → Nat → Int) (a b : Nat) : Bool := rt a b != 0

/-- `hasintersect(a, b)`, line 1999. -/
def hasintersect (rt : Ty → Ty → Ty) (a b : Ty) : Rt Bool := do
  let ti ← typeintersect rt a b
  pure (!isBottom ti)

/-- `typeintersect_env(a, b)`, lines 1631-1634: the runtime's `(ti, env)` pair. -/
def typeintersectEnv {ε : Type} (rt : Ty → Ty → Ty × ε) (a b : Ty) : Ty × ε := rt a b

/-- `datatype_fieldtypes(x)`, line 622, and `get_methodtable(m)`, lines 1563-1569:
runtime answers. -/
def datatypeFieldtypes (rt : DT → List Ty) (d : DT) : List Ty := rt d
def getMethodtable {μ : Type} (rt : Nat → Option μ) (m : Nat) : Option μ := rt m

/-! ## Argument tuples -/

/-- What `to_tuple_type` receives: a `Tuple`, `AbstractArray` or `SimpleVector`
of elements (spliced into `Tuple{t...}`), or any other value. -/
inductive TTArg where
  | coll (elems : List Ty)
  | val (t : Ty)

def unwrapva : Ty → Ty | .vararg T => T | t => t
def isTVar : Ty → Bool | .tvar _ _ _ => true | _ => false

/-- `to_tuple_type(t)`, lines 1534-1552: `tupleDT` is the `Tuple` type
constructor's `DataType`; `subTuple t` is `t <: Tuple`. -/
def toTupleType (tupleDT : DT) (subTuple : Ty → Bool) (a : TTArg) : Rt Ty :=
  let t := match a with | .coll es => Ty.dt tupleDT es | .val t => t
  if isTypeVal t && subTuple t then
    match unwrap t with
    | .dt _ ps =>
      if ps.all (fun p => let p := unwrapva p; isTypeVal p || isTVar p) then .ok t
      else .error (.errorException "argument tuple type must contain only types")
    | _ => .error .typeError
  else .error (.errorException "expected tuple type")

/-- `rewrap_unionall(body, t)`: re-wrap `body` in `t`'s `UnionAll` binders. -/
def rewrapUnionall (body : Ty) : Ty → Ty
  | .unionAll v lb ub b => .unionAll v lb ub (rewrapUnionall body b)
  | _ => body

/-- `signature_type(f, argtypes)`, lines 1554-1561: `ft` is `Core.Typeof(f)`. -/
def signatureType (tupleDT : DT) (subTuple : Ty → Bool) (ft : Ty) (a : TTArg) : Rt Ty := do
  let argtypes ← toTupleType tupleDT subTuple a
  match unwrap argtypes with
  | .dt _ ps => pure (rewrapUnionall (.dt tupleDT (ft :: ps)) argtypes)
  | _ => .error .typeError
end JuliaLean.RuntimeCov.TypePreds
end

section
namespace JuliaLean.RuntimeCov.Methods

open JuliaLean.RuntimeCov
open JuliaLean.RuntimeCov.TypePreds

def typemaxUInt : Nat := 2 ^ 64 - 1

/-! ## MethodList and `methods` -/

/-- `MethodList(ms, tn)`, lines 1715-1716. -/
structure MethodList where
  ms : List Nat
  tn : Sym
  deriving DecidableEq, Repr

/-- `size(m::MethodList)`, line 1712, and `getindex(m, i)`, line 1713. -/
def mlSize (m : MethodList) : List Nat := [m.ms.length]
def mlGetindex (m : MethodList) (i : Int) : Rt Nat :=
  if 1 ≤ i ∧ i ≤ m.ms.length then .ok (m.ms.getD (i - 1).toNat 0) else .error .boundsError

/-- `matches_to_methods(ms, tn, mod)`, lines 1723-1731: `modOf m` is
`parentmodule(m)`; `mods = none` is `mod === nothing`. -/
def matchesToMethods (modOf : Nat → Sym) (ms : List Nat) (tn : Sym) (mods : Option (List Sym)) :
    MethodList :=
  match mods with
  | none => ⟨ms, tn⟩
  | some mods => ⟨ms.filter (fun m => mods.contains (modOf m)), tn⟩

/-- The arguments of one `jl_matching_methods` call. -/
structure MatchQuery where
  t : Ty
  mt : Option Nat
  lim : Int
  ambig : Bool
  world : Nat
  minWorld : Nat
  maxWorld : Nat
  deriving Repr

/-- `_methods_by_ftype` with eight arguments (line 1802), four (line 1799), and
three (line 1796). `jl` answers a query with a vector of matches or `nothing`. -/
def methodsByFtype8 (jl : MatchQuery → Option (List Nat)) (t : Ty) (mt : Option Nat) (lim : Int)
    (world : Nat) (ambig : Bool) (mn mx : Nat) : Option (List Nat) :=
  jl ⟨t, mt, lim, ambig, world, mn, mx⟩
def methodsByFtype4 (jl : MatchQuery → Option (List Nat)) (t : Ty) (mt : Option Nat) (lim : Int)
    (world : Nat) : Option (List Nat) :=
  methodsByFtype8 jl t mt lim world false 0 typemaxUInt
def methodsByFtype3 (jl : MatchQuery → Option (List Nat)) (t : Ty) (lim : Int) (world : Nat) :
    Option (List Nat) :=
  methodsByFtype4 jl t none lim world

/-- `_methods(f, t, lim, world)`, lines 1791-1794: `sig` is `signature_type(f, t)`. -/
def methods_ (jl : MatchQuery → Option (List Nat)) (sig : Rt Ty) (lim : Int) (world : Nat) :
    Rt (Option (List Nat)) := do
  let tt ← sig
  pure (methodsByFtype3 jl tt lim world)

def reflectionError : RtErr := .errorException "code reflection cannot be used from generated functions"

/-- `methods(f, t, mod)`, lines 1751-1757: `tn` is `typeof(f).name`. -/
def methods (jl : MatchQuery → Option (List Nat)) (modOf : Nat → Sym) (sig : Rt Ty) (tn : Sym)
    (world : Nat) (mods : Option (List Sym)) : Rt MethodList :=
  if world = typemaxUInt then .error reflectionError
  else do
    let ms ← methods_ jl sig (-1) world
    match ms with
    | none => .error .typeError
    | some ms => pure (matchesToMethods modOf ms tn mods)

/-- `methods(f, t, mod::Module)`, line 1758. -/
def methodsMod (jl : MatchQuery → Option (List Nat)) (modOf : Nat → Sym) (sig : Rt Ty) (tn : Sym)
    (world : Nat) (mod : Sym) : Rt MethodList :=
  methods jl modOf sig tn world (some [mod])

/-- `methods(f, mod)`, lines 1770-1774: `sigAll` is `signature_type(f, Tuple{Vararg{Any}})`. -/
def methodsAll (jl : MatchQuery → Option (List Nat)) (modOf : Nat → Sym) (sigAll : Rt Ty) (tn : Sym)
    (world : Nat) (mods : Option (List Sym)) : Rt MethodList :=
  methods jl modOf sigAll tn world mods

/-- `methods_including_ambiguous(f, t)`, lines 1760-1768. -/
def methodsIncludingAmbiguous (jl : MatchQuery → Option (List Nat)) (modOf : Nat → Sym) (sig : Rt Ty)
    (tn : Sym) (world : Nat) : Rt MethodList := do
  let tt ← sig
  if world = typemaxUInt then .error reflectionError
  else
    match methodsByFtype8 jl tt none (-1) world true 0 typemaxUInt with
    | none => .error .typeError
    | some ms => pure (matchesToMethods modOf ms tn none)

/-- Runtime calls issued by method mutators and specializers. -/
inductive Call where
  | disable (m : Nat)
  | lookup (m : Nat) (atype : Ty)
  | getLinfo (m : Nat) (atype : Ty) (sparams : List Ty)
  deriving Repr

/-- `delete_method(m)`, lines 1701-1703. -/
def deleteMethod (m : Nat) : Call := .disable m

/-! ## Method fields, IR and generators -/

inductive Source where
  | str (s : String)
  | codeInfo (c : Nat)
  | other
  deriving DecidableEq, Repr

structure Method where
  id : Nat
  source : Option Source
  hasGenerator : Bool
  nospecialize : Nat
  nospecializeinfer : Bool
  nargs : Nat
  isva : Bool
  sig : Ty
  deriving Repr

/-- `hasgenerator(m::Method)`, `hasgenerator(mi)`, lines 1806-1807. -/
def hasgenerator (m : Method) : Bool := m.hasGenerator
def hasgeneratorMI (miDef : Method) : Bool := hasgenerator miDef

/-- `_uncompressed_ir(m::Method)`, lines 1809-1815: `uncompress` is `jl_uncompress_ir`. -/
def uncompressedIr_ (uncompress : Method → String → Nat) (m : Method) (s : Source) : Rt Nat :=
  match s with
  | .str str => .ok (uncompress m str)
  | .codeInfo c => .ok c
  | .other => .error .typeError

/-- `_uncompressed_ir(codeinst, s)`, lines 1817-1818. -/
def uncompressedIrCI (uncompress : Method → Nat → String → Nat) (defMethod : Method) (ci : Nat)
    (s : String) : Nat := uncompress defMethod ci s

/-- `uncompressed_ir(m)`, lines 2089-2091. -/
def uncompressedIr (uncompress : Method → String → Nat) (m : Method) : Rt Nat :=
  match m.source with
  | some s => uncompressedIr_ uncompress m s
  | none =>
    if m.hasGenerator then .error (.errorException "Method is @generated; try `code_lowered` instead.")
    else .error (.errorException "Code for this Method is not available.")

/-- `codeinst.def`: a `MethodInstance` or an `ABIOverride` wrapping one. -/
inductive CIDef where
  | mi (m : Nat)
  | abiOverride (m : Nat)
  | other
  deriving DecidableEq, Repr

/-- `get_ci_mi(codeinst)`, lines 1820-1827. -/
def getCiMi (d : CIDef) : Rt Nat :=
  match d with
  | .abiOverride m => .ok m
  | .mi m => .ok m
  | .other => .error .typeError

/-- `generating_output(incremental)`, lines 1841-1847: `jlGen` is
`jl_generating_output()`, `optIncr` is `JLOptions().incremental != 0`. -/
def generatingOutput (jlGen : Int) (optIncr : Bool) (incremental : Option Bool) : Bool :=
  if jlGen = 0 then false
  else match incremental with
    | some inc => if optIncr == inc then true else false
    | none => true

/-- `ast_slotflag(code, i)`, line 1850: `jl_ir_slotflag(code, i - 1)`. -/
def astSlotflag {κ : Type} (rt : κ → Nat → Nat) (code : κ) (i : Nat) : Nat := rt code (i - 1)

/-- `has_image_globalref(m)`, line 2093. -/
def hasImageGlobalref (rt : Option Source → Bool) (m : Method) : Bool := rt m.source

def SLOT_USED : Nat := 0x8
def slotUsed (flag : Nat) : Bool := flag &&& SLOT_USED != 0

/-- The generator facts `may_invoke_generator` reads. -/
structure GenInfo where
  isStub : Bool
  genMethods : Option (List Nat)
  hasSource : Bool
  nslots : Nat
  slotflag : Nat → Nat

/-- The `for i = 1:non_va_args` loop of lines 1898-1904. -/
def checkArgs (slotflag : Nat → Nat) (nsp : Nat) (ps : List Ty) : List Nat → Rt Bool
  | [] => .ok true
  | i :: is =>
    match ps[i - 1]? with
    | none => .error .boundsError
    | some p =>
      if !isdispatchelem p && slotUsed (slotflag (1 + i + nsp)) then .ok false
      else checkArgs slotflag nsp ps is

/-- `may_invoke_generator(method, atype, sparams)`, lines 1870-1925: `isDT` is
`isdispatchtuple(atype)`, `atParams` the parameters of `unwrap_unionall(atype)`
when it is a `DataType`, `sparamIsSvec` the `isa(sparams[i], SimpleVector)`
tests. -/
def mayInvokeGenerator (isDT : Bool) (g : GenInfo) (m : Method) (atParams : Option (List Ty))
    (sparamIsSvec : List Bool) : Rt Bool :=
  if isDT then .ok true
  else if !g.isStub then .ok false
  else match g.genMethods with
    | none => .ok false
    | some gm =>
      if gm.length ≠ 1 then .ok false
      else if !g.hasSource then .ok false
      else match atParams with
        | none => .ok false
        | some ps =>
          let nsp := sparamIsSvec.length
          if !(decide (g.nslots ≥ 1 + nsp + ps.length)) then .ok false
          else if (List.range' 1 nsp).any (fun i => sparamIsSvec.getD (i - 1) false && slotUsed (g.slotflag (1 + i)))
          then .ok false
          else
            let nonva := if m.isva then m.nargs - 1 else m.nargs
            match checkArgs g.slotflag nsp ps (List.range' 1 nonva) with
            | .error e => .error e
            | .ok false => .ok false
            | .ok true =>
              if m.isva && slotUsed (g.slotflag (1 + m.nargs + nsp)) then
                .ok ((ps.drop nonva).all isdispatchelem)
              else .ok true

/-- `may_invoke_generator(mi)`, lines 1867-1869. -/
def mayInvokeGeneratorMI (isDT : Bool) (g : GenInfo) (miDef : Method) (atParams : Option (List Ty))
    (sparamIsSvec : List Bool) : Rt Bool :=
  mayInvokeGenerator isDT g miDef atParams sparamIsSvec

/-! ## Specialization -/

/-- `subst_trivial_bounds(atype)`, lines 1930-1947: `egal` is `===` on types,
`inst t ub` is `atype{v.ub}` (`none` when instantiation throws); recursion
depth is bounded by `fuel`. -/
def substTrivialBounds (egal : Ty → Ty → Bool) (inst : Ty → Ty → Option Ty) : Nat → Ty → Ty
  | 0, t => t
  | f + 1, t =>
    match t with
    | .unionAll v lb ub body =>
      if isconcretetype ub || egal lb ub then
        match inst t ub with
        | some s => substTrivialBounds egal inst f s
        | none => .unionAll v lb ub (substTrivialBounds egal inst f body)
      else .unionAll v lb ub (substTrivialBounds egal inst f body)
    | _ => t

/-- The number of leading `UnionAll` binders. -/
def uaDepth : Ty → Nat
  | .unionAll _ _ _ b => uaDepth b + 1
  | _ => 0

/-- `normalize_typevars(method, atype, sparams)`, lines 1953-1960: `eqT` is `==`
on types, `env a b` the environment of `typeintersect_env(a, b)`. -/
def normalizeTypevars (egal : Ty → Ty → Bool) (inst : Ty → Ty → Option Ty) (eqT : Ty → Ty → Bool)
    (env : Ty → Ty → List Ty) (m : Method) (atype : Ty) (sparams : List Ty) : Ty × List Ty :=
  let at2 := substTrivialBounds egal inst (uaDepth atype) atype
  if !egal at2 atype && eqT at2 atype then (at2, env at2 m.sig) else (atype, sparams)

/-- `get_nospecializeinfer_sig`, lines 1962-1966. -/
def getNospecializeinferSig (norm : Ty → List Ty → Method → Ty) (m : Method) (atype : Ty)
    (sparams : List Ty) : Ty :=
  match atype with
  | .dt _ _ => norm atype sparams m
  | _ => m.sig

/-- `is_nospecialized`, `is_nospecializeinfer`, lines 1968-1969. -/
def isNospecialized (m : Method) : Bool := m.nospecialize ≠ 0
def isNospecializeinfer (m : Method) : Bool := m.nospecializeinfer && isNospecialized m

/-- `specialize_method(method, atype, sparams; preexisting)`, lines 1979-1993. -/
def specializeMethod (egal : Ty → Ty → Bool) (inst : Ty → Ty → Option Ty) (eqT : Ty → Ty → Bool)
    (env : Ty → Ty → List Ty) (norm : Ty → List Ty → Method → Ty) (m : Method) (atype : Ty)
    (sparams : List Ty) (preexisting : Bool := false) : Call :=
  let r := match atype with
    | .unionAll _ _ _ _ => normalizeTypevars egal inst eqT env m atype sparams
    | _ => (atype, sparams)
  let atype := if isNospecializeinfer m then getNospecializeinferSig norm m r.1 r.2 else r.1
  if preexisting then .lookup m.id atype else .getLinfo m.id atype r.2

/-- `specialize_method(match; kwargs...)`, lines 1995-1997. -/
structure MethodMatch where
  method : Method
  specTypes : Ty
  sparams : List Ty

def specializeMethodMatch (egal : Ty → Ty → Bool) (inst : Ty → Ty → Option Ty) (eqT : Ty → Ty → Bool)
    (env : Ty → Ty → List Ty) (norm : Ty → List Ty → Method → Ty) (mm : MethodMatch)
    (preexisting : Bool := false) : Call :=
  specializeMethod egal inst eqT env norm mm.method mm.specTypes mm.sparams preexisting

/-! ## The method-table walk -/

/-- A `TypeMapEntry` chain (its `func` fields in `next` order) or a
`TypeMapLevel`, whose four `Memory{Any}` caches hold, in each value slot, a
nested `Memory{Any}` of maps or a map. -/
inductive TMap where
  | entry (funcs : List Nat)
  | level (targ arg1 tname name1 : Option (List (Option (Sum (List (Option TMap)) TMap))))
      (list any : Option TMap)

/-- The indices `3:2:n`. -/
def juliaSlots (n : Nat) : List Nat := List.range' 3 ((n - 1) / 2) 2

/-- `avisit(f, e)`, lines 2012-2027, given the visitor `v` for nested maps. -/
def avisit (v : TMap → List Nat) (e : List (Option (Sum (List (Option TMap)) TMap))) : List Nat :=
  (juliaSlots e.length).flatMap fun i =>
    match e[i - 1]? with
    | some (some (Sum.inl inner)) =>
      (juliaSlots inner.length).flatMap fun j =>
        match inner[j - 1]? with
        | some (some t) => v t
        | _ => []
    | some (some (Sum.inr t)) => v t
    | _ => []

/-- `visit(f, mc::TypeMapLevel)` (lines 2011-2043) and `visit(f, d::TypeMapEntry)`
(lines 2044-2050): the sequence of methods passed to `f`; `fuel` bounds the depth. -/
def visitTM : Nat → TMap → List Nat
  | 0, _ => []
  | _ + 1, .entry funcs => funcs
  | f + 1, .level targ arg1 tname name1 list any =>
    let a := fun (c : Option (List (Option (Sum (List (Option TMap)) TMap)))) =>
      match c with | some e => avisit (visitTM f) e | none => []
    a targ ++ a arg1 ++ a tname ++ a name1 ++
      (match list with | some l => visitTM f l | none => []) ++
      (match any with | some l => visitTM f l | none => [])

/-- A `Core.MethodTable` and its `defs`. -/
structure MethodTable where
  defs : Option TMap

/-- `visit(f, mt::Core.MethodTable)`, lines 2007-2010. -/
def visitMT (fuel : Nat) (mt : MethodTable) : List Nat :=
  match mt.defs with
  | some d => visitTM fuel d
  | none => []

/-- `MethodList(mt)`, lines 1715-1721; `length(mt)`, lines 2080-2086;
`isempty(mt)`, line 2087. -/
def methodListMT (fuel : Nat) (mt : MethodTable) : MethodList := ⟨visitMT fuel mt, "Any"⟩
def lengthMT (fuel : Nat) (mt : MethodTable) : Nat := (visitMT fuel mt).length
def isemptyMT (mt : MethodTable) : Bool := mt.defs.isNone

/-! ## Specializations -/

/-- `m.specializations`: unset/`nothing`, one `MethodInstance`, or a `SimpleVector`
with empty (`nothing`) slots. -/
inductive Specs where
  | none
  | one (mi : Nat)
  | svec (s : List (Option Nat))
  deriving DecidableEq, Repr

/-- `specializations(m)`, line 2059. -/
def specializations (defined : Bool) (s : Specs) : Specs := if defined then s else .none

inductive State where
  | nothing
  | idx (i : Nat)
  deriving DecidableEq, Repr

/-- The `while i < n && item === nothing` loop of lines 2071-2075, from index `i`. -/
def scan (s : List (Option Nat)) (i : Nat) : Option (Nat × Nat) :=
  if h : i < s.length then
    match s[i] with
    | some x => some (x, i + 1)
    | none => scan s (i + 1)
  else none
termination_by s.length - i

/-- `iterate(specs, i::Int)`, lines 2067-2077, on the `SimpleVector` `s`. -/
def iterateIdx (s : List (Option Nat)) (i : Nat) : Option (Nat × Nat) :=
  if i ≥ s.length then none else scan s i

/-- `iterate(specs)`, lines 2060-2065. -/
def iterateSpecs (sp : Specs) : Option (Nat × State) :=
  match sp with
  | .none => none
  | .one mi => some (mi, .nothing)
  | .svec s => (iterateIdx s 0).map fun r => (r.1, .idx r.2)

/-- `iterate(specs, ::Nothing)` (line 2066) and `iterate(specs, i::Int)`. -/
def iterateSpecsFrom (sp : Specs) (st : State) : Rt (Option (Nat × State)) :=
  match st, sp with
  | .nothing, _ => .ok none
  | .idx i, .svec s => .ok ((iterateIdx s i).map fun r => (r.1, .idx r.2))
  | .idx _, _ => .error .typeError

theorem scan_spec (s : List (Option Nat)) (i : Nat) :
    (scan s i = none ∧ (s.drop i).filterMap id = []) ∨
    (∃ x j, scan s i = some (x, j) ∧ i < j ∧ j ≤ s.length ∧
      (s.drop i).filterMap id = x :: (s.drop j).filterMap id) := by
  unfold scan
  split
  · rename_i h
    have hd : s.drop i = s[i] :: s.drop (i + 1) := List.drop_eq_getElem_cons h
    split
    · rename_i x hx
      right; refine ⟨x, i + 1, rfl, by omega, by omega, ?_⟩
      rw [hd, hx]; simp
    · rename_i hx
      rcases scan_spec s (i + 1) with ⟨h1, h2⟩ | ⟨x, j, h1, h2, h3, h4⟩
      · left; refine ⟨h1, ?_⟩; rw [hd, hx]; simpa using h2
      · right; refine ⟨x, j, h1, by omega, h3, ?_⟩; rw [hd, hx]; simpa using h4
  · rename_i h
    left; refine ⟨rfl, ?_⟩
    simp [List.drop_eq_nil_of_le (by omega : s.length ≤ i)]
termination_by s.length - i

theorem iterateIdx_spec (s : List (Option Nat)) (i : Nat) :
    (iterateIdx s i = none ∧ (s.drop i).filterMap id = []) ∨
    (∃ x j, iterateIdx s i = some (x, j) ∧ i < j ∧ j ≤ s.length ∧
      (s.drop i).filterMap id = x :: (s.drop j).filterMap id) := by
  unfold iterateIdx
  split
  · rename_i h; left; refine ⟨rfl, ?_⟩; simp [List.drop_eq_nil_of_le (by omega : s.length ≤ i)]
  · exact scan_spec s i
/-- The elements the iteration protocol produces from state `i`
(`count(Returns(true), specs)` counts them). -/
def enumFrom (s : List (Option Nat)) (i : Nat) : List Nat :=
  match h : iterateIdx s i with
  | none => []
  | some (x, j) => x :: enumFrom s j
termination_by s.length - i
decreasing_by
  rcases iterateIdx_spec s i with ⟨h1, _⟩ | ⟨x', j', h1, h2, h3, _⟩
  · rw [h1] at h; cases h
  · rw [h1] at h; cases h; omega

/-- `length(specs::MethodSpecializations)`, line 2078. -/
def lengthSpecs (sp : Specs) : Nat :=
  match sp with
  | .none => 0
  | .one _ => 1
  | .svec s => (enumFrom s 0).length
end JuliaLean.RuntimeCov.Methods
end

section
namespace JuliaLean.ExprReflect

open JuliaLean

/-! ### Reflection -/

/-- Definite layout metadata used by `fieldnames`, `fieldcount`, and `fieldoffset`. -/
structure TypeLayout where
  names : List String
  offsets : List Nat
  definite : Bool
  deriving Repr, DecidableEq, Inhabited

/-- `fieldcount`; `base/runtime_internals.jl:1456-1487`. -/
def fieldCount (layout : TypeLayout) : Jl Nat :=
  if layout.definite then .ok layout.names.length
  else .error (.argumentError "type does not have a definite number of fields")

/-- `fieldnames`; `base/runtime_internals.jl:413-442`. -/
def fieldNames (layout : TypeLayout) : Jl (List String) := do
  if layout.definite then .ok layout.names
  else .error (.argumentError "type does not have a definite number of fields")

/-- One-based `fieldoffset(type, i)`. The public `Integer` index is converted to
`Cint` before `jl_get_field_offset`; `base/runtime_internals.jl:1228-1275`. -/
def fieldOffset (layout : TypeLayout) (index : Int) : Jl Nat := do
  if index < -2147483648 || 2147483647 < index then
    .error (.inexactError "Cint")
  else if !layout.definite then
    .error (.argumentError "type does not have a definite number of fields")
  else if index < 1 || layout.names.length < index.toNat then
    .error .boundsError
  else match layout.offsets[index.toNat - 1]? with
    | some offset => .ok offset
    | none => .error .boundsError

/-- Abstract method record. Input order is Julia's most-to-least-specific order. -/
structure MethodInfo where
  name : String
  moduleName : String
  signatureMatches : Bool
  deriving Repr, DecidableEq, Inhabited

/-- `matches_to_methods`; `base/runtime_internals.jl:1723-1731`. -/
def methods (table : List MethodInfo) (modules : Option (List String)) : List MethodInfo :=
  table.filter fun method =>
    method.signatureMatches && modules.all (·.contains method.moduleName)
end JuliaLean.ExprReflect
end
