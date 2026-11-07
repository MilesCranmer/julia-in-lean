import JuliaLean.base.runtime_internals
import JuliaLean.base.io
import JuliaLean.base.options
import JuliaLean.base.expr

/-!
# Model of `base/reflection.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Module/type/field queries live in the preceding runtime_internals source model.
This file models public function/method reflection, keyword checks, ambiguity
resolution and ordinary runtime/compiler-entry wrappers. Compiler lookup and
subtyping themselves remain typed type-system primitives; no Julia dispatch or
inference engine is reimplemented. Source world-age checks, short-circuit order,
method selection and exceptions remain explicit. Compiler inference and IR analysis
are typed inputs. The invoke macros construct Expr trees, including quoted source
positions. Runtime methods use `base.io.M`, preserving changes on errors.
-/

namespace JuliaLean.base.reflection
open JuliaLean
open JuliaLean.base.io (M Error whileLoop)
open JuliaLean.base.expr
open JuliaLean.base.runtime_internals (I U U32 Cint TypeOps LookupOps MethodList i)

structure CompilerOps (World Module Sym Function Args Result Vector : Type) where
  compiler : Module
  reflectionCompiler : M World (Option Module)
  getglobal : Module → Sym → M World Function
  newArgVector : Function → Args → M World Vector
  vectorLength : Vector → M World I
  callInTypeinfWorld : Vector → Cint → M World Result
  callCurrentWorld : Function → Args → M World Result
  symbol : String → Sym
  egalSymbol : Sym → Sym → Bool

structure KeywordLookupOps (World V Table Method Sym SlotSyms : Type) where
  lookup : V → Option Table → U → M World (Option Method)
  coreHasmethod : V → M World Bool
  keywordCallType : V
  namedTupleType : V
  slotSyms : Method → M World SlotSyms
  uncompressArgnames : SlotSyms → M World (List Sym)
  nargs : Method → Cint
  symbolBytes : Sym → M World (List UInt8)
  egalSymbol : Sym → Sym → Bool

structure AmbiguityOps (World V Method Match Pointer : Type) where
  egalMethod : Method → Method → Bool
  signature : Method → V
  newAmbiguityRef : Cint → M World Pointer
  readAmbiguityRef : Pointer → M World Cint
  matchMethod : Match → M World Method
  specTypes : Match → M World V
  sortMethodMatches : List Match → Cint → M World (Cint × List Match)
  subtype : V → V → M World Bool
  notEqualType : V → V → M World Bool
  isUnionall : V → Bool
  upperBound : V → M World V

/--
Julia source: base/reflection.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_debug_info_kind() = unsafe_load(cglobal(:jl_default_debug_info_kind, Cint))
```
-/
def defaultDebugInfoKind {World Pointer : Type} (cglobal : M World Pointer)
    (unsafeLoad : Pointer → M World Cint) : M World Cint := do unsafeLoad (← cglobal)

/--
Julia source: base/reflection.jl:75-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function method_instance(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}});
                         world=Base.get_world_counter(), method_table=nothing)
    tt = to_tuple_type(argtypes)
    mi = ccall(:jl_method_lookup_by_tt, Any,
                (Any, Csize_t, Any),
                tt, world, method_table)
    return mi::Union{Nothing, MethodInstance}
end
```
-/
def methodInstanceTypes {World V D N Mod P Sym Table Instance : Type} (ops : TypeOps World V D N Mod P Sym)
    (jlGetWorldCounter : M World U) (lookup : V → U → Option Table → M World (Option Instance))
    (argtypes : V) (world : Option U := none) (methodTable : Option Table := none) : M World (Option Instance) := do
  let world ← match world with | some world => pure world | none => JuliaLean.base.runtime_internals.getWorldCounter jlGetWorldCounter
  let tt ← JuliaLean.base.runtime_internals.toTupleType ops argtypes
  lookup tt world methodTable

/--
Julia source: base/reflection.jl:84-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function method_instance(@nospecialize(f), @nospecialize(t);
                         world=Base.get_world_counter(), method_table=nothing)
    tt = signature_type(f, t)
    return method_instance(tt; world, method_table)
end
```
-/
def methodInstanceFunction {World V D N Mod P Sym Table Instance : Type} (ops : TypeOps World V D N Mod P Sym)
    (jlGetWorldCounter : M World U) (lookup : V → U → Option Table → M World (Option Instance))
    (f t : V) (world : Option U := none) (methodTable : Option Table := none) : M World (Option Instance) := do
  let world ← match world with | some world => pure world | none => JuliaLean.base.runtime_internals.getWorldCounter jlGetWorldCounter
  let tt ← JuliaLean.base.runtime_internals.signatureType ops f t
  methodInstanceTypes ops jlGetWorldCounter lookup tt (some world) methodTable

/--
Julia source: base/reflection.jl:307-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function default_tt(@nospecialize(f))
    ms = methods(f)
    if length(ms) == 1
        return tuple_type_tail(only(ms).sig)
    else
        return Tuple
    end
end
```
-/
def defaultTupleType {World V Method Name : Type} (methods : V → M World (MethodList Method Name))
    (signature : Method → V) (tupleTypeTail : V → M World V) (tupleType : V) (f : V) : M World V := do
  let ms ← methods f
  if ms.ms.length == 1 then
    match ms.ms with
    | [method] => tupleTypeTail (signature method)
    | _ => throw (.jl .boundsError)
  else pure tupleType

/--
Julia source: base/reflection.jl:316-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function raise_match_failure(name::Symbol, @nospecialize(tt))
    @noinline
    sig_str = sprint(Base.show_tuple_as_call, Symbol(""), tt)
    error("$name: unanalyzable call given $sig_str")
end
```
-/
def raiseMatchFailure {World Sym V Result : Type} (sprintTupleCall : Sym → V → M World String)
    (emptySymbol : Sym) (symbolText : Sym → String) (name : Sym) (tt : V) : M World Result := do
  let signature ← sprintTupleCall emptySymbol tt
  throw (.errorException (symbolText name ++ ": unanalyzable call given " ++ signature))

/--
Julia source: base/reflection.jl:324-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invoke_in_typeinf_world(args...)
    vargs = Any[args...]
    return ccall(:jl_call_in_typeinf_world, Any, (Ptr{Any}, Cint), vargs, length(vargs))
end
```
-/
def invokeInTypeinfWorldArguments {World Args Result Vector : Type}
    (newArgVector : Args → M World Vector) (vectorLength : Vector → M World I)
    (callInTypeinfWorld : Vector → Cint → M World Result) (args : Args) : M World Result := do
  let vargs ← newArgVector args
  let length ← vectorLength vargs
  let count ← JuliaLean.base.io.liftJl (JInt.convert "convert" .i32 length.val)
  callInTypeinfWorld vargs count

def invokeInTypeinfWorld {World Mod Sym Function Args Result Vector : Type}
    (compiler : CompilerOps World Mod Sym Function Args Result Vector) (function : Function)
    (args : Args) : M World Result :=
  invokeInTypeinfWorldArguments (compiler.newArgVector function) compiler.vectorLength
    compiler.callInTypeinfWorld args

/--
Julia source: base/reflection.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invoke_default_compiler(fname::Symbol, args...)
    if REFLECTION_COMPILER[] === nothing
        return invoke_in_typeinf_world(getglobal(Compiler, fname), args...)
    else
        return getglobal(REFLECTION_COMPILER[], fname)(args...)
    end
end
```
-/
def invokeDefaultCompiler {World Mod Sym Function Args Result Vector : Type}
    (compiler : CompilerOps World Mod Sym Function Args Result Vector) (fname : Sym) (args : Args) : M World Result := do
  if (← compiler.reflectionCompiler).isNone then
    let function ← compiler.getglobal compiler.compiler fname
    invokeInTypeinfWorld compiler function args
  else
    let some module ← compiler.reflectionCompiler | throw (.jl (.methodError "getglobal"))
    let function ← compiler.getglobal module fname
    compiler.callCurrentWorld function args

def invokeTypedCompiler {World V D N Mod P Sym Function Args Result Vector Obj : Type}
    (ops : TypeOps World V D N Mod P Sym) (compiler : CompilerOps World Mod Sym Function Args Result Vector)
    (typeofObject : Obj → D) (supertype : D → M World D) (expectedName : String) (error : String)
    (object : Obj) (fname : Sym) (args : Args) : M World Result := do
  let target ← whileLoop (fun t => do
    let name := ops.name (ops.nameOf t)
    if compiler.egalSymbol name (compiler.symbol "Any") then throw (.errorException error)
    if compiler.egalSymbol name (compiler.symbol expectedName) then return .inl t
    pure (.inr (← supertype t))) (typeofObject object)
  let function ← compiler.getglobal (ops.module (ops.nameOf target)) fname
  compiler.callCurrentWorld function args

/--
Julia source: base/reflection.jl:337-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invoke_interp_compiler(interp, fname::Symbol, args...)
    if interp === nothing
        return invoke_default_compiler(fname, args...)
    else
        T = typeof(interp)
        while true
            Tname = typename(T).name
            Tname === :Any && error("Expected AbstractInterpreter")
            Tname === :AbstractInterpreter && break
            T = supertype(T)
        end
        return getglobal(typename(T).module, fname)(args...)
    end
end
```
-/
def invokeInterpCompiler {World V D N Mod P Sym Function Args Result Vector Interp : Type}
    (ops : TypeOps World V D N Mod P Sym) (compiler : CompilerOps World Mod Sym Function Args Result Vector)
    (typeofInterp : Interp → D) (supertype : D → M World D) (interp : Option Interp)
    (fname : Sym) (args : Args) : M World Result := do
  match interp with
  | none => invokeDefaultCompiler compiler fname args
  | some interp => invokeTypedCompiler ops compiler typeofInterp supertype "AbstractInterpreter" "Expected AbstractInterpreter" interp fname args

/--
Julia source: base/reflection.jl:352-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invoke_mt_compiler(mt, fname::Symbol, args...)
    if mt === nothing
        return invoke_default_compiler(fname, args...)
    else
        T = typeof(mt)
        while true
            Tname = typename(T).name
            Tname === :Any && error("Expected MethodTableView")
            Tname === :MethodTableView && break
            T = supertype(T)
        end
        return getglobal(typename(T).module, fname)(args...)
    end
end
```
-/
def invokeMtCompiler {World V D N Mod P Sym Function Args Result Vector Table : Type}
    (ops : TypeOps World V D N Mod P Sym) (compiler : CompilerOps World Mod Sym Function Args Result Vector)
    (typeofTable : Table → D) (supertype : D → M World D) (table : Option Table)
    (fname : Sym) (args : Args) : M World Result := do
  match table with
  | none => invokeDefaultCompiler compiler fname args
  | some table => invokeTypedCompiler ops compiler typeofTable supertype "MethodTableView" "Expected MethodTableView" table fname args

/--
Julia source: base/reflection.jl:559-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
check_generated_context(world::UInt) =
    (ccall(:jl_is_in_pure_context, Bool, ()) || world == typemax(UInt)) &&
        error("code reflection cannot be used from generated functions")

```
-/
def checkGeneratedContext {World : Type} (jlIsInPureContext : M World Bool) (world : U) : M World Bool := do
  if ← jlIsInPureContext then throw (.errorException "code reflection cannot be used from generated functions")
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  pure false

/--
Julia source: base/reflection.jl:968-979 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _which(@nospecialize(tt::Type);
    method_table #=::Union{Nothing,Core.MethodTable,Compiler.MethodTableView}=# =nothing,
    world::UInt=get_world_counter(),
    raise::Bool=true)
    world == typemax(UInt) && error("code reflection cannot be used from generated functions")
    match, = invoke_mt_compiler(method_table, :findsup_mt, tt, world, method_table)
    if match === nothing
        raise && error("no unique matching method found for the specified argument types")
        return nothing
    end
    return match::Core.MethodMatch
end
```
-/
def whichSignature {World V D N Mod P Sym Function Vector Table Match Metadata : Type}
    (ops : TypeOps World V D N Mod P Sym)
    (compiler : CompilerOps World Mod Sym Function (V × U × Option Table) (Option Match × Metadata) Vector)
    (typeofTable : Table → D) (supertype : D → M World D) (jlGetWorldCounter : M World U)
    (tt : V) (methodTable : Option Table := none) (world : Option U := none) (raise : Bool := true)
    : M World (Option Match) := do
  let world ← match world with | some world => pure world | none => JuliaLean.base.runtime_internals.getWorldCounter jlGetWorldCounter
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  let (matchValue, _) ← invokeMtCompiler ops compiler typeofTable supertype methodTable
    (compiler.symbol "findsup_mt") (tt, world, methodTable)
  match matchValue with
  | none =>
    if raise then throw (.errorException "no unique matching method found for the specified argument types")
    pure none
  | some value => pure (some value)

/--
Julia source: base/reflection.jl:990-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function which(@nospecialize(f), @nospecialize(t))
    tt = signature_type(f, t)
    world = get_world_counter()
    match, _ = invoke_default_compiler(:_findsup, tt, nothing, world)
    if match === nothing
        me = MethodError(f, t, world)
        ee = ErrorException(sprint(io -> begin
            println(io, "Calling invoke(f, t, args...) would throw:");
            Base.showerror(io, me);
        end))
        throw(ee)
    end
    return match.method
end
```
-/
def whichFunction {World V D N Mod P Sym Function Vector Table Match Metadata Method MethodError Io : Type}
    (ops : TypeOps World V D N Mod P Sym)
    (compiler : CompilerOps World Mod Sym Function (V × Option Table × U) (Option Match × Metadata) Vector)
    (jlGetWorldCounter : M World U) (method : Match → M World Method)
    (newMethodError : V → V → U → M World MethodError)
    (sprint : (Io → M World Unit) → M World String) (println : Io → String → M World Unit)
    (showerror : Io → MethodError → M World Unit) (f t : V) : M World Method := do
  let tt ← JuliaLean.base.runtime_internals.signatureType ops f t
  let world ← JuliaLean.base.runtime_internals.getWorldCounter jlGetWorldCounter
  let (matchValue, _) ← invokeDefaultCompiler compiler (compiler.symbol "_findsup") (tt, none, world)
  match matchValue with
  | none =>
    let me ← newMethodError f t world
    let message ← sprint (fun io => do
      println io "Calling invoke(f, t, args...) would throw:"
      showerror io me)
    throw (.errorException message)
  | some matchValue => method matchValue

/--
Julia source: base/reflection.jl:1010-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function which(@nospecialize(tt#=::Type=#))
    return _which(tt).method
end
```
-/
def whichTypes {World V D N Mod P Sym Function Vector Table Match Metadata Method : Type}
    (ops : TypeOps World V D N Mod P Sym)
    (compiler : CompilerOps World Mod Sym Function (V × U × Option Table) (Option Match × Metadata) Vector)
    (typeofTable : Table → D) (supertype : D → M World D) (jlGetWorldCounter : M World U)
    (method : Match → M World Method) (tt : V) : M World Method := do
  if !ops.isAType tt then throw (.jl (.methodError "_which"))
  let some matchValue ← whichSignature ops compiler typeofTable supertype jlGetWorldCounter tt |
    throw (.foreignError "FieldError" "nothing has no method field")
  method matchValue

/--
Julia source: base/reflection.jl:1013-1013 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
which(@nospecialize(argtypes::Tuple)) = which(to_tuple_type(argtypes))
```
-/
def whichTuple {World V D N Mod P Sym Method : Type} (ops : TypeOps World V D N Mod P Sym)
    (which : V → M World Method) (argtypes : V) : M World Method := do
  which (← JuliaLean.base.runtime_internals.toTupleType ops argtypes)

def whichModuleWithError {World Module Sym : Type} (isdefinedglobal : Module → Sym → M World Bool)
    (bindingModule : Module → Sym → M World Module) (message : Module → Sym → M World String)
    (mdl : Module) (symbol : Sym) : M World Module := do
  if !(← isdefinedglobal mdl symbol) then throw (.errorException (← message mdl symbol))
  bindingModule mdl symbol

/--
Julia source: base/reflection.jl:1020-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function which(mdl::Module, symbol::Symbol)
    if !isdefinedglobal(mdl, symbol)
        error("\"$symbol\" is not defined in module $mdl")
    end
    return binding_module(mdl, symbol)
end
```
-/
def whichModulePrinted {World Module Sym : Type} (isdefinedglobal : Module → Sym → M World Bool)
    (bindingModule : Module → Sym → M World Module)
    (symbolText : Sym → M World String) (moduleText : Module → M World String)
    (mdl : Module) (symbol : Sym) : M World Module :=
  whichModuleWithError isdefinedglobal bindingModule (fun mdl symbol => do
    let symbol ← symbolText symbol
    let module ← moduleText mdl
    pure ("\"" ++ symbol ++ "\" is not defined in module " ++ module)) mdl symbol

def whichModule {World Module Sym : Type} (isdefinedglobal : Module → Sym → M World Bool)
    (bindingModule : Module → Sym → M World Module) (mdl : Module) (symbol : Sym) : M World Module :=
  whichModuleWithError isdefinedglobal bindingModule
    (fun _ _ => pure "binding is not defined in module") mdl symbol

/--
Julia source: base/reflection.jl:1036-1038 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nameof(f::Function)
    return typeof(f).name.singletonname
end
```
-/
def nameofFunction {World V D N Mod P Sym Function : Type} (ops : TypeOps World V D N Mod P Sym)
    (typeof : Function → D) (singletonName : N → Sym) (f : Function) : Sym := singletonName (ops.nameOf (typeof f))

/--
Julia source: base/reflection.jl:1040-1043 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nameof(f::Core.IntrinsicFunction)
    name = ccall(:jl_intrinsic_name, Ptr{UInt8}, (Core.IntrinsicFunction,), f)
    return ccall(:jl_symbol, Ref{Symbol}, (Ptr{UInt8},), name)
end
```
-/
def nameofIntrinsic {World Intrinsic Pointer Sym : Type} (jlIntrinsicName : Intrinsic → M World Pointer)
    (jlSymbol : Pointer → M World Sym) (f : Intrinsic) : M World Sym := do jlSymbol (← jlIntrinsicName f)

/--
Julia source: base/reflection.jl:1051-1051 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentmodule(f::Function) = parentmodule(typeof(f))
```
-/
def parentmoduleFunction {World V D N Mod P Sym Function : Type} (ops : TypeOps World V D N Mod P Sym)
    (typeof : Function → D) (f : Function) : Mod := JuliaLean.base.runtime_internals.parentmoduleDataType ops (typeof f)

/--
Julia source: base/reflection.jl:1075-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentmodule(m::Method) = m.module
```
-/
def parentmoduleMethod {Method Module : Type} (module : Method → Module) (m : Method) : Module := module m

/--
Julia source: base/reflection.jl:1059-1065 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parentmodule(@nospecialize(f), @nospecialize(types))
    m = methods(f, types)
    if isempty(m)
        error("no matching methods")
    end
    return parentmodule(first(m))
end
```
-/
def parentmoduleFunctionTypes {World V Method N Module : Type}
    (methods : V → V → M World (MethodList Method N)) (module : Method → Module) (f types : V) : M World Module := do
  let m ← methods f types
  match m.ms with
  | [] => throw (.errorException "no matching methods")
  | first :: _ => pure (parentmoduleMethod module first)

/--
Julia source: base/reflection.jl:1113-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hasmethod(@nospecialize(f), @nospecialize(t))
    return Core._hasmethod(signature_type(f, t))
end
```
-/
def hasmethod {World V D N Mod P Sym Table Method Slot : Type} (ops : TypeOps World V D N Mod P Sym)
    (lookup : KeywordLookupOps World V Table Method Sym Slot) (f t : V) : M World Bool := do
  lookup.coreHasmethod (← JuliaLean.base.runtime_internals.signatureType ops f t)

/--
Julia source: base/reflection.jl:1117-1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Core.kwcall(kwargs::NamedTuple, ::typeof(hasmethod), @nospecialize(f), @nospecialize(t))
    world = kwargs.world::UInt # make sure this is the only local, to avoid confusing kwarg_decl()
    return ccall(:jl_gf_invoke_lookup, Any, (Any, Any, UInt), signature_type(f, t), nothing, world) !== nothing
end
```
-/
def hasmethodKwcall {World V D N Mod P Sym Table Method Slot Keywords : Type} (ops : TypeOps World V D N Mod P Sym)
    (lookup : KeywordLookupOps World V Table Method Sym Slot) (getWorld : Keywords → M World U)
    (kwargs : Keywords) (f t : V) : M World Bool := do
  let world ← getWorld kwargs
  let tt ← JuliaLean.base.runtime_internals.signatureType ops f t
  pure (← lookup.lookup tt none world).isSome

/--
Julia source: base/reflection.jl:1122-1139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hasmethod(f, t, kwnames::Tuple{Vararg{Symbol}}; world::UInt=get_world_counter())
    @nospecialize
    world == typemax(UInt) && error("code reflection cannot be used from generated functions")
    isempty(kwnames) && return hasmethod(f, t; world)
    t = to_tuple_type(t)
    ft = Core.Typeof(f)
    u = unwrap_unionall(t)::DataType
    tt = rewrap_unionall(Tuple{typeof(Core.kwcall), NamedTuple, ft, u.parameters...}, t)
    match = ccall(:jl_gf_invoke_lookup, Any, (Any, Any, UInt), tt, nothing, world)
    match === nothing && return false
    kws = ccall(:jl_uncompress_argnames, Array{Symbol,1}, (Any,), (match::Method).slot_syms)
    kws = kws[((match::Method).nargs + 1):end] # remove positional arguments
    isempty(kws) && return true # some kwfuncs simply forward everything directly
    for kw in kws
        endswith(String(kw), "...") && return true
    end
    return issubset(kwnames, kws)
end
```
-/
def hasmethodKeywords {World V D N Mod P Sym Table Method Slot : Type} (ops : TypeOps World V D N Mod P Sym)
    (lookup : KeywordLookupOps World V Table Method Sym Slot) (jlGetWorldCounter : M World U)
    (f t : V) (kwnames : List Sym) (world : Option U := none) : M World Bool := do
  let world ← match world with | some world => pure world | none => JuliaLean.base.runtime_internals.getWorldCounter jlGetWorldCounter
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  if kwnames.isEmpty then return ← hasmethodKwcall ops lookup (fun world => pure world) world f t
  let t ← JuliaLean.base.runtime_internals.toTupleType ops t
  let ft ← ops.coreTypeof f
  let some u := ops.asDatatype (ops.unwrap t) | throw (.foreignError "TypeError" "expected DataType")
  let tt ← ops.rewrapUnionall (← ops.tupleType
    ([lookup.keywordCallType, lookup.namedTupleType, ft] ++ (← ops.parameters u))) t
  let some matched ← lookup.lookup tt none world | return false
  let kws ← lookup.uncompressArgnames (← lookup.slotSyms matched)
  let nargs := i (lookup.nargs matched).val
  if nargs.val < 0 || nargs.val > kws.length then throw (.jl .boundsError)
  let kws := kws.drop nargs.val.toNat
  if kws.isEmpty then return true
  for kw in kws do
    let bytes ← lookup.symbolBytes kw
    if bytes.reverse.take 3 == [46, 46, 46] then return true
  pure (kwnames.all (fun name => kws.any (fun kw => lookup.egalSymbol name kw)))

/--
Julia source: base/reflection.jl:1249-1257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        function involves_both(ms)
            have_m1 = have_m2 = false
            for match in ms
                m = (match::Core.MethodMatch).method
                m === m1 && (have_m1 = true)
                m === m2 && (have_m2 = true)
            end
            return have_m1 && have_m2
        end
```
-/
def involvesBoth {World V Method Match Pointer : Type} (ambiguity : AmbiguityOps World V Method Match Pointer)
    (m1 m2 : Method) (ms : List Match) : M World Bool := do
  let mut haveM1 := false
  let mut haveM2 := false
  for matchValue in ms do
    let method ← ambiguity.matchMethod matchValue
    if ambiguity.egalMethod method m1 then haveM1 := true
    if ambiguity.egalMethod method m2 then haveM2 := true
  pure (haveM1 && haveM2)

/--
Julia source: base/reflection.jl:1233-1277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function inner(ti)
        ti === Bottom && return false
        if !ambiguous_bottom
            has_bottom_parameter(ti) && return false
        end
        world = get_world_counter()
        world == typemax(UInt) && return true # intersecting methods are always ambiguous in the generator world, which is true, albeit maybe confusing for some
        min = Ref{UInt}(typemin(UInt))
        max = Ref{UInt}(typemax(UInt))
        has_ambig = Ref{Int32}(0)
        ms = _methods_by_ftype(ti, nothing, -1, world, true, min, max, has_ambig)::Vector{Any}
        has_ambig[] == 0 && return false
        # if ml-matches reported the existence of an ambiguity over their
        # intersection, see if both m1 and m2 seem to be involved in it
        # (if one was fully dominated by a different method, we want to
        # report the other ambiguous pair)
        function involves_both(ms)
            have_m1 = have_m2 = false
            for match in ms
                m = (match::Core.MethodMatch).method
                m === m1 && (have_m1 = true)
                m === m2 && (have_m2 = true)
            end
            return have_m1 && have_m2
        end
        nms = length(ms)
        if !ambiguous_bottom
            filter!(ms) do m
                return !has_bottom_parameter((m::Core.MethodMatch).spec_types)
            end
        end
        # ml-matches did not need both methods to expose the reported ambiguity
        involves_both(ms) || return false
        if length(ms) != nms
            # If we intentionally removed certain ambiguities (via the
            # filter call above), re-run the runtime's match sort on the
            # remaining matches and see if the solution is still holding an ambiguity
            # and m1 and m2 are both still reported in the solution.
            if ccall(:jl_sort_method_matches, Cint, (Any, Cint), ms, true) == 0
                return false
            end
            involves_both(ms) || return false
        end
        return true
    end
```
-/
def ambiguityInner {World V D N Mod P Sym Method Match Pointer Ref Table : Type}
    (ops : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref Pointer Match)
    (ambiguity : AmbiguityOps World V Method Match Pointer) (jlGetWorldCounter : M World U)
    (m1 m2 : Method) (ambiguousBottom : Bool) (ti : V) : M World Bool := do
  if ops.egal ti ops.bottom then return false
  if !ambiguousBottom then
    if ← JuliaLean.base.runtime_internals.hasBottomParameter ops ambiguity.isUnionall ambiguity.upperBound ti then return false
  let world ← JuliaLean.base.runtime_internals.getWorldCounter jlGetWorldCounter
  if world == JInt.typemax .u64 then return true
  let minWorld ← lookup.newWorldRef (JInt.typemin .u64)
  let maxWorld ← lookup.newWorldRef (JInt.typemax .u64)
  let hasAmbiguous ← ambiguity.newAmbiguityRef (JInt.wrap .i32 0)
  let some foundMethods ← JuliaLean.base.runtime_internals.methodsByTypeNative lookup ti none (i (-1))
      world true minWorld maxWorld hasAmbiguous | throw (.foreignError "TypeError" "expected Vector")
  if (← ambiguity.readAmbiguityRef hasAmbiguous).val == 0 then return false
  let originalLength := foundMethods.length
  let mut methodMatches := foundMethods
  if !ambiguousBottom then
    methodMatches := ← methodMatches.filterM (fun matchValue => do
      let specTypes ← ambiguity.specTypes matchValue
      pure (!(← JuliaLean.base.runtime_internals.hasBottomParameter ops ambiguity.isUnionall ambiguity.upperBound specTypes)))
  if !(← involvesBoth ambiguity m1 m2 methodMatches) then return false
  if methodMatches.length != originalLength then
    let (status, sorted) ← ambiguity.sortMethodMatches methodMatches (JInt.wrap .i32 1)
    methodMatches := sorted
    if status.val == 0 then return false
    if !(← involvesBoth ambiguity m1 m2 methodMatches) then return false
  pure true

/--
Julia source: base/reflection.jl:1229-1297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isambiguous(m1::Method, m2::Method; ambiguous_bottom::Bool=false)
    m1 === m2 && return false
    ti = typeintersect(m1.sig, m2.sig)
    ti === Bottom && return false
    function inner(ti)
        ti === Bottom && return false
        if !ambiguous_bottom
            has_bottom_parameter(ti) && return false
        end
        world = get_world_counter()
        world == typemax(UInt) && return true # intersecting methods are always ambiguous in the generator world, which is true, albeit maybe confusing for some
        min = Ref{UInt}(typemin(UInt))
        max = Ref{UInt}(typemax(UInt))
        has_ambig = Ref{Int32}(0)
        ms = _methods_by_ftype(ti, nothing, -1, world, true, min, max, has_ambig)::Vector{Any}
        has_ambig[] == 0 && return false
        # if ml-matches reported the existence of an ambiguity over their
        # intersection, see if both m1 and m2 seem to be involved in it
        # (if one was fully dominated by a different method, we want to
        # report the other ambiguous pair)
        function involves_both(ms)
            have_m1 = have_m2 = false
            for match in ms
                m = (match::Core.MethodMatch).method
                m === m1 && (have_m1 = true)
                m === m2 && (have_m2 = true)
            end
            return have_m1 && have_m2
        end
        nms = length(ms)
        if !ambiguous_bottom
            filter!(ms) do m
                return !has_bottom_parameter((m::Core.MethodMatch).spec_types)
            end
        end
        # ml-matches did not need both methods to expose the reported ambiguity
        involves_both(ms) || return false
        if length(ms) != nms
            # If we intentionally removed certain ambiguities (via the
            # filter call above), re-run the runtime's match sort on the
            # remaining matches and see if the solution is still holding an ambiguity
            # and m1 and m2 are both still reported in the solution.
            if ccall(:jl_sort_method_matches, Cint, (Any, Cint), ms, true) == 0
                return false
            end
            involves_both(ms) || return false
        end
        return true
    end
    if !(ti <: m1.sig && ti <: m2.sig)
        # When type-intersection fails, it's often also not commutative. Thus
        # checking the reverse may allow detecting ambiguity solutions
        # correctly in more cases (and faster).
        ti2 = typeintersect(m2.sig, m1.sig)
        if ti2 <: m1.sig && ti2 <: m2.sig
            ti = ti2
        elseif ti != ti2
            # TODO: this would be the more correct way to handle this case, but
            #       people complained so we don't do it
            #inner(ti2) || return false # report that the type system failed to decide if it was ambiguous by saying they definitely are
            return false # report that the type system failed to decide if it was ambiguous by saying they definitely are not
        else
            return false # report that the type system failed to decide if it was ambiguous by saying they definitely are not
        end
    end
    inner(ti) || return false
    # otherwise type-intersection reported an ambiguity we couldn't solve
    return true
end
```
-/
def isambiguous {World V D N Mod P Sym Method Match Pointer Ref Table : Type}
    (ops : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref Pointer Match)
    (ambiguity : AmbiguityOps World V Method Match Pointer) (jlGetWorldCounter : M World U)
    (m1 m2 : Method) (ambiguousBottom : Bool := false) : M World Bool := do
  if ambiguity.egalMethod m1 m2 then return false
  let mut ti ← JuliaLean.base.runtime_internals.typeintersect ops (ambiguity.signature m1) (ambiguity.signature m2)
  if ops.egal ti ops.bottom then return false
  let fits ← if ← ambiguity.subtype ti (ambiguity.signature m1) then ambiguity.subtype ti (ambiguity.signature m2) else pure false
  if !fits then
    let ti2 ← JuliaLean.base.runtime_internals.typeintersect ops (ambiguity.signature m2) (ambiguity.signature m1)
    let fits2 ← if ← ambiguity.subtype ti2 (ambiguity.signature m1) then ambiguity.subtype ti2 (ambiguity.signature m2) else pure false
    if fits2 then ti := ti2
    else if ← ambiguity.notEqualType ti ti2 then return false
    else return false
  if !(← ambiguityInner ops lookup ambiguity jlGetWorldCounter m1 m2 ambiguousBottom ti) then return false
  pure true

/--
Julia source: base/reflection.jl:1365-1365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getglobalref(gr::GlobalRef, world::UInt) = ccall(:jl_eval_globalref, Any, (Any, UInt), gr, world)
```
-/
def getGlobalRef {World GlobalRef Value : Type} (jlEvalGlobalref : GlobalRef → U → M World Value)
    (gr : GlobalRef) (world : U) : M World Value := jlEvalGlobalref gr world

/--
Julia source: base/reflection.jl:1367-1376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invokelatest_gr(gr::GlobalRef, args...; kwargs...)
    @inline
    kwargs = merge(NamedTuple(), kwargs)
    world = get_world_counter()
    f = getglobalref(gr, world)
    if isempty(kwargs)
        return invoke_in_world(world, f, args...)
    end
    return invoke_in_world(world, Core.kwcall, kwargs, f, args...)
end
```
-/
def invokelatestGlobalRef {World GlobalRef Function Args Keywords KeywordTuple Result : Type}
    (mergeEmptyNamedTuple : Keywords → M World KeywordTuple) (isEmpty : KeywordTuple → Bool)
    (jlGetWorldCounter : M World U) (jlEvalGlobalref : GlobalRef → U → M World Function)
    (invokePlain : U → Function → Args → M World Result)
    (invokeKeywordCall : U → KeywordTuple → Function → Args → M World Result)
    (gr : GlobalRef) (args : Args) (kwargs : Keywords) : M World Result := do
  let kwargs ← mergeEmptyNamedTuple kwargs
  let world ← JuliaLean.base.runtime_internals.getWorldCounter jlGetWorldCounter
  let f ← getGlobalRef jlEvalGlobalref gr world
  if isEmpty kwargs then invokePlain world f args
  else invokeKeywordCall world kwargs f args

open JuliaLean.base.runtime_internals (SpecializationOps)

/-- The values and callees of the inference reflection methods (`code_typed_by_type`,
`return_types`, `infer_*`, `print_statement_costs`, `bodyfunction`). Julia values, including
types, methods, found, interpreters and `CodeInfo` objects, are `V`. The compiler's functions
are reached through the installed `invoke_interp_compiler` and `invoke_default_compiler`, with
the arguments and result as Julia values; their behaviour is the compiler's. -/
structure InferOps (World V D N Mod P Sym Function Vector Io : Type) where
  types : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym
  compiler : CompilerOps World Mod Sym Function (List V) V Vector
  typeofInterp : V → D
  supertype : D → M World D
  /-- `ccall(:jl_is_in_pure_context, Bool, ())`. -/
  jlIsInPureContext : M World Bool
  nothing : V
  isNothing : V → Bool
  ofBool : Bool → V
  ofWorld : U → V
  /-- `Any[xs...]`: a fresh `Vector{Any}` value. -/
  anyVector : List V → M World V
  /-- `isa(x, Core.OpaqueClosure)`, `isa(x, Core.Builtin)`, `isa(x, Method)`,
  `isa(x, Core.CodeInfo)`, `isa(x, Expr)` (its head and arguments), `isa(x, Symbol)`,
  `isa(x, GlobalRef)` (its module and name) and `isa(x, Core.SSAValue)` (its `id`). -/
  isOpaqueClosure : V → Bool
  isBuiltin : V → Bool
  isMethod : V → Bool
  isCodeInfo : V → Bool
  asExpr : V → Option (Sym × List V)
  asSymbol : V → Option Sym
  asGlobalRef : V → Option (V × Sym)
  asSSAValue : V → Option I
  /-- `x.f` of a field of a runtime object. -/
  getfield : V → Sym → M World V
  /-- The elements of a `Vector`, in iteration order. -/
  elements : V → M World (List V)
  /-- `x::T` for the named type `T`. -/
  typeassert : V → String → M World V
  /-- `a => b`, `Pair{CodeInfo,Any}(a, b)`, and the destructuring `(a, b) = x` of a pair or
  2-tuple. -/
  pair : V → V → M World V
  codeInfoPair : V → V → M World V
  destructure2 : V → M World (V × V)
  /-- `something(x, y)` (`base/some.jl`). -/
  something : V → V → M World V
  /-- `x ? a : b` of a value `x`: `TypeError` unless it is a `Bool`. -/
  asCondition : V → M World Bool
  /-- `remove_linenums!(code)` (`base/expr.jl`), mutating the `CodeInfo`. -/
  removeLinenums : V → M World Unit
  /-- `raise_match_failure`'s `sprint(Base.show_tuple_as_call, Symbol(""), tt)`. -/
  sprintTupleCall : Sym → V → M World String
  emptySymbol : Sym
  symbolText : Sym → String
  /-- `specialize_method(m, tt, Core.svec())` and `_uncompressed_ir(m)` (`runtime_internals.jl`),
  `uncompressed_ast(m)`. -/
  specializeMethod : V → V → M World V
  uncompressedIr : V → M World V
  uncompressedAst : V → M World V
  /-- `parentmodule(m::Method)`. -/
  parentmodule : V → V
  /-- `Core`. -/
  isCore : V → Bool
  /-- `invoke_in_world(world, getglobal, mod, sym)`. -/
  getglobalInWorld : U → V → Sym → M World V
  /-- `@isdefined(IRShow)` and `IRShow.debuginfo(debuginfo)`. -/
  irshowDefined : Bool
  irshowDebuginfo : Sym → M World Sym
  /-- `IRShow.show_ir(io, code, IRShow.IRShowConfig(linefn))`. -/
  showIr : Io → V → (Io → I → I → M World String) → M World Unit
  /-- `println(io, x)`, `println(io, s)`, `print(io, s)` and `println(io)`. -/
  printlnValue : Io → V → M World Unit
  printString : Io → String → M World Unit
  /-- `Int[]` with `empty!`, `resize!`, `length` and `getindex`. -/
  newIntVector : M World V
  emptyBang : V → M World Unit
  resizeBang : V → I → M World Unit
  length : V → M World I
  getindexInt : V → I → M World V
  /-- `ndigits(x)` and `lpad(x, n)` of an `Int` value. -/
  ndigits : V → M World I
  lpad : V → I → M World String

namespace InferOps
variable {World V D N Mod P Sym Function Vector Io : Type}

/-- `invoke_interp_compiler(passed_interp, fname, args...)`. -/
def call (o : InferOps World V D N Mod P Sym Function Vector Io) (passedInterp : Option V)
    (fname : String) (args : List V) : M World V :=
  invokeInterpCompiler o.types o.compiler o.typeofInterp o.supertype passedInterp
    (o.compiler.symbol fname) args

/-- `interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp`. -/
def defaultInterp (o : InferOps World V D N Mod P Sym Function Vector Io) (passedInterp : Option V)
    (world : U) : M World V :=
  match passedInterp with
  | none => invokeDefaultCompiler o.compiler (o.compiler.symbol "_default_interp") [o.ofWorld world]
  | some interp => pure interp

/-- `raise_match_failure(name, tt)`. -/
def raise {α : Type} (o : InferOps World V D N Mod P Sym Function Vector Io) (name : String) (tt : V) :
    M World α :=
  raiseMatchFailure o.sprintTupleCall o.emptySymbol o.symbolText (o.compiler.symbol name) tt

/-- `matches.matches` of the `_findall_matches` result. -/
def matchList (o : InferOps World V D N Mod P Sym Function Vector Io) (found : V) : M World (List V) := do
  o.elements (← o.getfield found (o.compiler.symbol "matches"))

/-- `xs[k]` of a list of values: `BoundsError` outside `1:length(xs)`. -/
def atIdx (xs : List V) (k : I) : M World V :=
  if 1 ≤ k.val ∧ k.val ≤ xs.length then
    match xs[(k.val - 1).toNat]? with
    | some x => pure x
    | none => throw (.jl .boundsError)
  else throw (.jl .boundsError)

/-- `to_tuple_type(types).parameters`. -/
def tupleParameters (o : InferOps World V D N Mod P Sym Function Vector Io) (types : V) :
    M World (List V) := do
  let tt ← JuliaLean.base.runtime_internals.toTupleType o.types types
  match o.types.asDatatype tt with
  | some dt => o.types.parameters dt
  | none => throw (.foreignError "FieldError" "type UnionAll has no field parameters")

end InferOps
structure LoweredOps (World V Method Instance Match Params Raw Str Code Pointer Sym : Type) where
  matchMethod : Match → M World Method
  matchSpecTypes : Match → M World V
  matchSparams : Match → M World Params
  instanceMethod : Instance → M World Method
  instanceSpecTypes : Instance → M World V
  instanceSparams : Instance → M World Params
  hasGenerator : Method → M World Bool
  analyzeGenerator : Method → V → Params → M World Bool
  irShowDefined : M World Bool
  irShowDebuginfo : Sym → M World Sym
  symbol : String → Sym
  egalSymbol : Sym → Sym → Bool
  codeForStaged : Instance → U → Pointer → M World Code
  nullPointer : Pointer
  hasSource : Method → M World Bool
  source : Method → M World Raw
  asString : Raw → Option Str
  codeValue : Code → Raw
  assertCode : Raw → M World Code
  uncompressNative : Method → Pointer → Str → M World Code
  removeLineNums : Code → M World Code
  instanceString : Instance → M World String
  typeString : V → M World String

/--
Julia source: base/reflection.jl:58-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function method_instances(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}), world::UInt)
    tt = to_tuple_type(argtypes)
    results = Core.MethodInstance[]
    # this make a better error message than the typeassert that follows
    world == typemax(UInt) && error("code reflection cannot be used from generated functions")
    for match in _methods_by_ftype(tt, -1, world)::Vector
        instance = specialize_method(match::Core.MethodMatch)
        push!(results, instance)
    end
    return results
end
```
-/
def methodInstances {World V D N Mod P Sym Var Method Params Instance Table Ref Match Raw Str Code : Type}
    (types : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref P Match)
    (specialization : SpecializationOps World V Var Method Params Instance)
    (ops : LoweredOps World V Method Instance Match Params Raw Str Code P Sym)
    (argtypes : V) (world : U) : M World (Array Instance) := do
  let tt ← JuliaLean.base.runtime_internals.toTupleType types argtypes
  let mut results : Array Instance := #[]
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  let some foundMethods ← JuliaLean.base.runtime_internals.methodsByType lookup tt (i (-1)) world
    | throw (.foreignError "TypeError" "expected Vector")
  for matchValue in foundMethods do
    let some methodInstance ← JuliaLean.base.runtime_internals.specializeMethodMatch types specialization
        ops.matchMethod ops.matchSpecTypes ops.matchSparams matchValue
      | throw (.foreignError "TypeError" "expected MethodInstance")
    results := results.push methodInstance
  pure results

/--
Julia source: base/reflection.jl:70-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function method_instances(@nospecialize(f), @nospecialize(t), world::UInt)
    tt = signature_type(f, t)
    return method_instances(tt, world)
end
```
-/
def methodInstancesFunction {World V D N Mod P Sym Var Method Params Instance Table Ref Match Raw Str Code : Type}
    (types : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref P Match)
    (specialization : SpecializationOps World V Var Method Params Instance)
    (ops : LoweredOps World V Method Instance Match Params Raw Str Code P Sym)
    (f t : V) (world : U) : M World (Array Instance) := do
  let tt ← JuliaLean.base.runtime_internals.signatureType types f t
  methodInstances types lookup specialization ops tt world

/--
Julia source: base/reflection.jl:19-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function code_lowered(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); generated::Bool=true, debuginfo::Symbol=:default)
    if @isdefined(IRShow)
        debuginfo = IRShow.debuginfo(debuginfo)
    elseif debuginfo === :default
        debuginfo = :source
    end
    if debuginfo !== :source && debuginfo !== :none
        throw(ArgumentError("'debuginfo' must be either :source or :none"))
    end
    world = get_world_counter()
    world == typemax(UInt) && error("code reflection cannot be used from generated functions")
    ret = CodeInfo[]
    for m in method_instances(argtypes, world)
        if generated && hasgenerator(m)
            if may_invoke_generator(m)
                code = ccall(:jl_code_for_staged, Ref{CodeInfo}, (Any, UInt, Ptr{Cvoid}), m, world, C_NULL)
            else
                error("Could not expand generator for `@generated` method ", m, ". ",
                      "This can happen if the provided argument types (", argtypes, ") are ",
                      "not concrete types, but the `generated` argument is `true`.")
            end
        else
            code = uncompressed_ir(m.def::Method)
            debuginfo === :none && remove_linenums!(code)
        end
        push!(ret, code)
    end
    return ret
end
```
-/
def codeLowered {World V D N Mod P Sym Var Method Params Instance Table Ref Match Raw Str Code : Type}
    (types : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref P Match)
    (specialization : SpecializationOps World V Var Method Params Instance)
    (ops : LoweredOps World V Method Instance Match Params Raw Str Code P Sym)
    (jlGetWorldCounter : M World U) (argtypes : V) (generated : Bool := true)
    (debuginfo : Sym := ops.symbol "default") : M World (Array Code) := do
  let mut debuginfo := debuginfo
  if ← ops.irShowDefined then
    debuginfo := ← ops.irShowDebuginfo debuginfo
  else if ops.egalSymbol debuginfo (ops.symbol "default") then
    debuginfo := ops.symbol "source"
  if !ops.egalSymbol debuginfo (ops.symbol "source") && !ops.egalSymbol debuginfo (ops.symbol "none") then
    throw (.jl (.argumentError "'debuginfo' must be either :source or :none"))
  let world ← JuliaLean.base.runtime_internals.getWorldCounter jlGetWorldCounter
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  let mut ret : Array Code := #[]
  for methodInstance in ← methodInstances types lookup specialization ops argtypes world do
    let hasGenerator ← if generated then
        JuliaLean.base.runtime_internals.hasgeneratorMethodInstance ops.instanceMethod ops.hasGenerator methodInstance
      else pure false
    let code ← if hasGenerator then do
        if ← JuliaLean.base.runtime_internals.mayInvokeGeneratorInstance
            ops.instanceMethod ops.instanceSpecTypes ops.instanceSparams ops.analyzeGenerator methodInstance then
          ops.codeForStaged methodInstance world ops.nullPointer
        else
          let methodText ← ops.instanceString methodInstance
          let typeText ← ops.typeString argtypes
          throw (.errorException ("Could not expand generator for `@generated` method " ++ methodText ++ ". " ++
            "This can happen if the provided argument types (" ++ typeText ++ ") are " ++
            "not concrete types, but the `generated` argument is `true`."))
      else do
        let method ← ops.instanceMethod methodInstance
        let code ← JuliaLean.base.runtime_internals.uncompressedIr ops.hasSource ops.hasGenerator
          (JuliaLean.base.runtime_internals.uncompressedIrMethod ops.source ops.asString ops.codeValue
            ops.assertCode ops.uncompressNative ops.nullPointer) method
        if ops.egalSymbol debuginfo (ops.symbol "none") then
          let _ ← ops.removeLineNums code
        pure code
    ret := ret.push code
  pure ret

/--
Julia source: base/reflection.jl:49-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function code_lowered(@nospecialize(f), @nospecialize(t=Tuple); generated::Bool=true, debuginfo::Symbol=:default)
    tt = signature_type(f, t)
    return code_lowered(tt; generated, debuginfo)
end
```
-/
def codeLoweredFunction {World V D N Mod P Sym Var Method Params Instance Table Ref Match Raw Str Code : Type}
    (types : TypeOps World V D N Mod P Sym) (lookup : LookupOps World V Table Ref P Match)
    (specialization : SpecializationOps World V Var Method Params Instance)
    (ops : LoweredOps World V Method Instance Match Params Raw Str Code P Sym)
    (jlGetWorldCounter : M World U) (f t : V) (generated : Bool := true)
    (debuginfo : Sym := ops.symbol "default") : M World (Array Code) := do
  let tt ← JuliaLean.base.runtime_internals.signatureType types f t
  codeLowered types lookup specialization ops jlGetWorldCounter tt generated debuginfo

-- Source context (declarations and comments)
-- Source: base/reflection.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source context (declarations and comments)
-- Source: base/reflection.jl:53-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # for backwards compat
-- const uncompressed_ast = uncompressed_ir
-- const _uncompressed_ast = _uncompressed_ir
-- 
-- /Source

-- Source context (declarations and comments)
-- Source: base/reflection.jl:69-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/reflection.jl:93-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct CodegenParams
    """
    If enabled, generate the necessary code to support the --track-allocations
    command line flag to julia itself. Note that the option itself does not enable
    allocation tracking. Rather, it merely generates the support code necessary
    to perform allocation tracking if requested by the command line option.
    """
    track_allocations::Cint

    """
    If enabled, generate the necessary code to support the --code-coverage
    command line flag to julia itself. Note that the option itself does not enable
    code coverage. Rather, it merely generates the support code necessary
    to perform code coverage if requested by the command line option.
    """
    code_coverage::Cint

    """
    If enabled, force the compiler to use the specialized signature
    for all generated functions, whenever legal. If disabled, the choice is made
    heuristically and specsig is only used when deemed profitable.
    """
    prefer_specsig::Cint

    """
    If enabled, enable emission of `.debug_names` sections.
    """
    gnu_pubnames::Cint

    """
    Controls what level of debug info to emit. Currently supported values are:
    - 0: no debug info
    - 1: full debug info
    - 2: Line tables only
    - 3: Debug directives only

    The integer values currently match the llvm::DICompilerUnit::DebugEmissionKind enum,
    although this is not guaranteed.
    """
    debug_info_kind::Cint

    """
    Controls the debug_info_level parameter, equivalent to the -g command line option.
    """
    debug_info_level::Cint

    """
    If enabled, generate a GC safepoint at the entry to every function. Emitting
    these extra safepoints can reduce the amount of time that other threads are
    waiting for the currently running thread to reach a safepoint. The cost for
    a safepoint is small, but non-zero. The option is enabled by default.
    """
    safepoint_on_entry::Cint

    """
    If enabled, add an implicit argument to each function call that is used to
    pass down the current task local state pointer. This argument is passed
    using the `swiftself` convention, which in the ordinary case means that the
    pointer is kept in a register and accesses are thus very fast. If this option
    is disabled, the task local state pointer must be loaded from thread local
    storage, which incurs a small amount of additional overhead. The option is enabled by
    default.
    """
    gcstack_arg::Cint

    """
    If enabled, use the Julia PLT mechanism to support lazy-resolution of `ccall`
    targets. The option may be disabled for use in environments where the julia
    runtime is unavailable, but is otherwise recommended to be enabled, even if
    lazy resolution is not required, as the Julia PLT mechanism may have superior
    performance compared to the native platform mechanism. The option is enabled by default.
    """
    use_jlplt::Cint

    """
        If enabled emit LLVM IR for all functions even if they wouldn't be compiled
        for some reason (i.e. functions that return a constant value).
    """
    force_emit_all::Cint

    """
    When enabled, run the MemorySanitizer pass.
    """
    sanitize_memory::Cint
    """
    When enabled, run the ThreadSanitizer pass.
    """
    sanitize_thread::Cint
    """
    When enabled, run the AddressSanitizer pass.
    """
    sanitize_address::Cint

    """
    When enabled, generate names that are globally unique in this Julia session,
    across all code generated with this flag set.  Intended for llvmpasses
    tests.
    """
    unique_names::Cint

    """
    If enabled, retain inlined function scopes in LLVM debug information. Enabled
    by default so consumers of the emitted IR can reconstruct inlined frames.
    Julia's internal codegen parameters disable this for image generation in release
    builds, since its own backtraces reconstruct these frames from CodeInstance debuginfo.
    """
    debug_info_inline_scopes::Cint

    function CodegenParams(; track_allocations::Bool=true, code_coverage::Bool=true,
                   prefer_specsig::Bool=false,
                   gnu_pubnames::Bool=true, debug_info_kind::Cint = default_debug_info_kind(),
                   debug_info_level::Cint = Cint(JLOptions().debug_level), safepoint_on_entry::Bool=true,
                   gcstack_arg::Bool=true, use_jlplt::Bool=true, force_emit_all::Bool=false,
                   sanitize_memory::Bool=false, sanitize_thread::Bool=false, sanitize_address::Bool=false,
                   unique_names::Bool=false,
                   debug_info_inline_scopes::Bool=true)
        return new(
            Cint(track_allocations), Cint(code_coverage),
            Cint(prefer_specsig),
            Cint(gnu_pubnames), debug_info_kind,
            debug_info_level, Cint(safepoint_on_entry),
            Cint(gcstack_arg), Cint(use_jlplt), Cint(force_emit_all),
            Cint(sanitize_memory), Cint(sanitize_thread), Cint(sanitize_address),
            Cint(unique_names), Cint(debug_info_inline_scopes))
    end
end
```
-/
structure CodegenParams where
  track_allocations : Cint
  code_coverage : Cint
  prefer_specsig : Cint
  gnu_pubnames : Cint
  debug_info_kind : Cint
  debug_info_level : Cint
  safepoint_on_entry : Cint
  gcstack_arg : Cint
  use_jlplt : Cint
  force_emit_all : Cint
  sanitize_memory : Cint
  sanitize_thread : Cint
  sanitize_address : Cint
  unique_names : Cint
  debug_info_inline_scopes : Cint


/--
Julia source: base/reflection.jl:201-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function CodegenParams(; track_allocations::Bool=true, code_coverage::Bool=true,
                   prefer_specsig::Bool=false,
                   gnu_pubnames::Bool=true, debug_info_kind::Cint = default_debug_info_kind(),
                   debug_info_level::Cint = Cint(JLOptions().debug_level), safepoint_on_entry::Bool=true,
                   gcstack_arg::Bool=true, use_jlplt::Bool=true, force_emit_all::Bool=false,
                   sanitize_memory::Bool=false, sanitize_thread::Bool=false, sanitize_address::Bool=false,
                   unique_names::Bool=false,
                   debug_info_inline_scopes::Bool=true)
        return new(
            Cint(track_allocations), Cint(code_coverage),
            Cint(prefer_specsig),
            Cint(gnu_pubnames), debug_info_kind,
            debug_info_level, Cint(safepoint_on_entry),
            Cint(gcstack_arg), Cint(use_jlplt), Cint(force_emit_all),
            Cint(sanitize_memory), Cint(sanitize_thread), Cint(sanitize_address),
            Cint(unique_names), Cint(debug_info_inline_scopes))
    end
```
-/
def newCodegenParams {World Pointer OptP OptPP : Type} (cglobalDebugKind : M World Pointer)
    (loadDebugKind : Pointer → M World Cint)
    (loadOptions : M World (JuliaLean.base.options.JLOptions OptP OptPP))
    (trackAllocations : Bool := true) (codeCoverage : Bool := true) (preferSpecsig : Bool := false)
    (gnuPubnames : Bool := true) (debugInfoKind : Option Cint := none) (debugInfoLevel : Option Cint := none)
    (safepointOnEntry : Bool := true) (gcstackArg : Bool := true) (useJlplt : Bool := true)
    (forceEmitAll : Bool := false) (sanitizeMemory : Bool := false) (sanitizeThread : Bool := false)
    (sanitizeAddress : Bool := false) (uniqueNames : Bool := false) (debugInfoInlineScopes : Bool := true)
    : M World CodegenParams := do
  let debugKind ← match debugInfoKind with
    | some value => pure value
    | none => defaultDebugInfoKind cglobalDebugKind loadDebugKind
  let debugLevel ← match debugInfoLevel with
    | some value => pure value
    | none => do
      let options ← JuliaLean.base.options.JLOptions_new loadOptions
      JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i32 options.debug_level)
  pure { track_allocations := JuliaLean.base.int.ofBool .i32 trackAllocations
         code_coverage := JuliaLean.base.int.ofBool .i32 codeCoverage
         prefer_specsig := JuliaLean.base.int.ofBool .i32 preferSpecsig
         gnu_pubnames := JuliaLean.base.int.ofBool .i32 gnuPubnames
         debug_info_kind := debugKind
         debug_info_level := debugLevel
         safepoint_on_entry := JuliaLean.base.int.ofBool .i32 safepointOnEntry
         gcstack_arg := JuliaLean.base.int.ofBool .i32 gcstackArg
         use_jlplt := JuliaLean.base.int.ofBool .i32 useJlplt
         force_emit_all := JuliaLean.base.int.ofBool .i32 forceEmitAll
         sanitize_memory := JuliaLean.base.int.ofBool .i32 sanitizeMemory
         sanitize_thread := JuliaLean.base.int.ofBool .i32 sanitizeThread
         sanitize_address := JuliaLean.base.int.ofBool .i32 sanitizeAddress
         unique_names := JuliaLean.base.int.ofBool .i32 uniqueNames
         debug_info_inline_scopes := JuliaLean.base.int.ofBool .i32 debugInfoInlineScopes }

/--
Julia source: base/reflection.jl:221-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct EmissionParams
    emit_metadata::Cint

    function EmissionParams(; emit_metadata::Bool=true)
        return new(Cint(emit_metadata))
    end
end
```
-/
structure EmissionParams where
  emit_metadata : Cint

/--
Julia source: base/reflection.jl:224-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function EmissionParams(; emit_metadata::Bool=true)
        return new(Cint(emit_metadata))
    end
```
-/
def newEmissionParams (emitMetadata : Bool := true) : EmissionParams :=
  ⟨JuliaLean.base.int.ofBool .i32 emitMetadata⟩

-- Source context (declarations and comments)
-- Source: base/reflection.jl:219-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # this type mirrors jl_emission_params_t (documented in julia.h)
-- /Source

-- Source context (declarations and comments)
-- Source: base/reflection.jl:228-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     code_typed(f, types; kw...)
-- 
-- Return an array of type-inferred lowered form (IR) for the methods matching the given
-- generic function and type signature.
-- 
-- # Keyword Arguments
-- 
-- - `optimize::Bool = true`: optional, controls whether additional optimizations,
--   such as inlining, are also applied.
-- - `debuginfo::Symbol = :default`: optional, controls the amount of code metadata present
--   in the output, possible options are `:source` or `:none`.
-- 
-- # Internal Keyword Arguments
-- 
-- This section should be considered internal, and is only for who understands Julia compiler
-- internals.
-- 
-- - `world::UInt = Base.get_world_counter()`: optional, controls the world age to use
--   when looking up methods, use current world age if not specified.
-- - `interp::Core.Compiler.AbstractInterpreter = Core.Compiler.NativeInterpreter(world)`:
--   optional, controls the abstract interpreter to use, use the native interpreter if not specified.
-- 
-- # Examples
-- 
-- One can put the argument types in a tuple to get the corresponding `code_typed`.
-- 
-- ```julia
-- julia> code_typed(+, (Float64, Float64))
-- 1-element Vector{Any}:
--  CodeInfo(
-- 1 ─ %1 = Base.add_float(x, y)::Float64
-- └──      return %1
-- ) => Float64
-- 
-- julia> code_typed((typeof(-), Float64, Float64))
-- 1-element Vector{Any}:
--  CodeInfo(
-- 1 ─ %1 = Base.sub_float(x, y)::Float64
-- └──      return %1
-- ) => Float64
-- 
-- julia> code_typed((Type{Int}, UInt8))
-- 1-element Vector{Any}:
--  CodeInfo(
-- 1 ─ %1 = Core.zext_int(Core.Int64, x)::Int64
-- └──      return %1
-- ) => Int64
-- 
-- julia> code_typed((Returns{Int64},))
-- 1-element Vector{Any}:
--  CodeInfo(
-- 1 ─ %1 =   builtin Base.getfield(obj, :value)::Int64
-- └──      return %1
-- ) => Int64
-- ```
-- /Source

/--
Julia source: base/reflection.jl:288-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function code_typed(@nospecialize(f), @nospecialize(types=default_tt(f)); kwargs...)
    if isa(f, Core.OpaqueClosure)
        return code_typed_opaque_closure(f, types; kwargs...)
    end
    tt = signature_type(f, types)
    return code_typed_by_type(tt; kwargs...)
end
```
-/
def codeTypedFunction {World V D N Mod P Sym Opaque Keywords Result : Type}
    (ops : TypeOps World V D N Mod P Sym) (asOpaque : V → Option Opaque)
    (codeTypedOpaque : Opaque → V → Keywords → M World Result)
    (codeTypedByType : V → Keywords → M World Result) (f types : V) (kwargs : Keywords) : M World Result := do
  if let some closure := asOpaque f then return ← codeTypedOpaque closure types kwargs
  let tt ← JuliaLean.base.runtime_internals.signatureType ops f types
  codeTypedByType tt kwargs

/--
Julia source: base/reflection.jl:299-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function code_typed(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); kwargs...)
    tt = to_tuple_type(argtypes)
    return code_typed_by_type(tt; kwargs...)
end
```
-/
def codeTypedTypes {World V D N Mod P Sym Keywords Result : Type}
    (ops : TypeOps World V D N Mod P Sym) (codeTypedByType : V → Keywords → M World Result)
    (argtypes : V) (kwargs : Keywords) : M World Result := do
  let tt ← JuliaLean.base.runtime_internals.toTupleType ops argtypes
  codeTypedByType tt kwargs

-- Source context (declarations and comments)
-- Source: base/reflection.jl:286-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function code_typed end
-- 
-- /Source

-- Source context (declarations and comments)
-- Source: base/reflection.jl:295-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # support queries with signatures rather than objects to better support
-- # non-singleton function objects such as `(::Foo)(::Int, ::Int)`
-- # via `code_typed((Foo, Int, Int))` or `code_typed(Tuple{Foo, Int, Int})`.
-- /Source

-- Source context (declarations and comments)
-- Source: base/reflection.jl:303-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # returns argument tuple type which is supposed to be used for `code_typed` and its family;
-- # if there is a single method this functions returns the method argument signature,
-- /Source

/--
Julia source: base/reflection.jl:492-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function code_ircode(@nospecialize(f), @nospecialize(types = default_tt(f)); kwargs...)
    if isa(f, Core.OpaqueClosure)
        error("OpaqueClosure not supported")
    end
    tt = signature_type(f, types)
    return code_ircode_by_type(tt; kwargs...)
end
```
-/
def codeIrcodeFunction {World V D N Mod P Sym Keywords Result : Type}
    (ops : TypeOps World V D N Mod P Sym) (isOpaque : V → Bool)
    (codeIrcodeByType : V → Keywords → M World Result) (f types : V) (kwargs : Keywords) : M World Result := do
  if isOpaque f then throw (.errorException "OpaqueClosure not supported")
  let tt ← JuliaLean.base.runtime_internals.signatureType ops f types
  codeIrcodeByType tt kwargs

/--
Julia source: base/reflection.jl:500-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function code_ircode(@nospecialize(argtypes::Union{Tuple,Type{<:Tuple}}); kwargs...)
    tt = to_tuple_type(argtypes)
    return code_ircode_by_type(tt; kwargs...)
end
```
-/
def codeIrcodeTypes {World V D N Mod P Sym Keywords Result : Type}
    (ops : TypeOps World V D N Mod P Sym) (codeIrcodeByType : V → Keywords → M World Result)
    (argtypes : V) (kwargs : Keywords) : M World Result := do
  let tt ← JuliaLean.base.runtime_internals.toTupleType ops argtypes
  codeIrcodeByType tt kwargs

/--
Julia source: base/reflection.jl:373-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function code_typed_by_type(@nospecialize(tt::Type);
                            optimize::Bool=true,
                            debuginfo::Symbol=:default,
                            world::UInt=get_world_counter(),
                            interp=nothing)
    passed_interp = interp
    interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp
    (ccall(:jl_is_in_pure_context, Bool, ()) || world == typemax(UInt)) &&
        error("code reflection cannot be used from generated functions")
    if @isdefined(IRShow)
        debuginfo = IRShow.debuginfo(debuginfo)
    elseif debuginfo === :default
        debuginfo = :source
    end
    if debuginfo !== :source && debuginfo !== :none
        throw(ArgumentError("'debuginfo' must be either :source or :none"))
    end
    tt = to_tuple_type(tt)
    matches = invoke_interp_compiler(passed_interp, :_findall_matches, interp, tt)
    matches === nothing && raise_match_failure(:code_typed, tt)
    asts = []
    for match in matches.matches
        match = match::Core.MethodMatch
        code = invoke_interp_compiler(passed_interp, :typeinf_code, interp, match, optimize)
        if code === nothing
            push!(asts, match.method => Any)
        else
            debuginfo === :none && remove_linenums!(code)
            push!(asts, code => code.rettype)
        end
    end
    return asts
end
```
-/
def codeTypedByType {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (tt : V) (optimize : Bool := true)
    (debuginfo : Sym) (world : U) (interp : Option V := none) : M World (List V) := do
  let passedInterp := interp
  let interp ← o.defaultInterp passedInterp world
  if ← o.jlIsInPureContext then throw (.errorException "code reflection cannot be used from generated functions")
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  let sym := o.compiler.symbol
  let debuginfo ← if o.irshowDefined then o.irshowDebuginfo debuginfo
    else if o.compiler.egalSymbol debuginfo (sym "default") then pure (sym "source")
    else pure debuginfo
  if !o.compiler.egalSymbol debuginfo (sym "source") && !o.compiler.egalSymbol debuginfo (sym "none") then
    throw (.jl (.argumentError "'debuginfo' must be either :source or :none"))
  let tt ← JuliaLean.base.runtime_internals.toTupleType o.types tt
  let found ← o.call passedInterp "_findall_matches" [interp, tt]
  if o.isNothing found then o.raise "code_typed" tt
  let mut asts : List V := []
  for each in ← o.matchList found do
    let each ← o.typeassert each "Core.MethodMatch"
    let code ← o.call passedInterp "typeinf_code" [interp, each, o.ofBool optimize]
    if o.isNothing code then
      asts := asts ++ [← o.pair (← o.getfield each (sym "method")) o.types.any]
    else
      if o.compiler.egalSymbol debuginfo (sym "none") then o.removeLinenums code
      asts := asts ++ [← o.pair code (← o.getfield code (sym "rettype"))]
  pure asts


/--
Julia source: base/reflection.jl:406-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function get_oc_code_rt(passed_interp, oc::Core.OpaqueClosure, types, optimize::Bool)
    @nospecialize oc types
    ccall(:jl_is_in_pure_context, Bool, ()) &&
        error("code reflection cannot be used from generated functions")
    m = oc.source
    if isa(m, Method)
        if isdefined(m, :source)
            if optimize
                tt = Tuple{typeof(oc.captures), to_tuple_type(types).parameters...}
                mi = specialize_method(m, tt, Core.svec())
                interp = invoke_interp_compiler(passed_interp, :_default_interp, m.primary_world)
                code = invoke_interp_compiler(passed_interp, :typeinf_code, interp, mi, optimize)
                if code isa CodeInfo
                    return Pair{CodeInfo, Any}(code, code.rettype)
                end
                error("inference not successful")
            else
                code = _uncompressed_ir(m)
                return Pair{CodeInfo, Any}(code, typeof(oc).parameters[2])
            end
        else
            # OC constructed from optimized IR
            codeinst = m.specializations.cache
            # XXX: the inferred field is not normally a CodeInfo, but this assumes it is guaranteed to be always
            return Pair{CodeInfo, Any}(codeinst.inferred, codeinst.rettype)
        end
    else
        error("encountered invalid Core.OpaqueClosure object")
    end
end
```
-/
def getOcCodeRt {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (passedInterp : Option V)
    (oc types : V) (optimize : Bool) : M World V := do
  if ← o.jlIsInPureContext then throw (.errorException "code reflection cannot be used from generated functions")
  let sym := o.compiler.symbol
  let m ← o.getfield oc (sym "source")
  if o.isMethod m then
    if ← o.types.isdefined m (sym "source") then
      if optimize then
        let captures ← o.getfield oc (sym "captures")
        let tt ← o.types.tupleType ((← o.types.coreTypeof captures) :: (← o.tupleParameters types))
        let mi ← o.specializeMethod m tt
        let interp ← o.call passedInterp "_default_interp" [← o.getfield m (sym "primary_world")]
        let code ← o.call passedInterp "typeinf_code" [interp, mi, o.ofBool optimize]
        if o.isCodeInfo code then
          return ← o.codeInfoPair code (← o.getfield code (sym "rettype"))
        throw (.errorException "inference not successful")
      else
        let code ← o.uncompressedIr m
        let some ocType := o.types.asDatatype (← o.types.coreTypeof oc)
          | throw (.foreignError "FieldError" "type UnionAll has no field parameters")
        o.codeInfoPair code (← o.types.parameter ocType (JInt.wrap .i64 2))
    else
      let codeinst ← o.getfield (← o.getfield m (sym "specializations")) (sym "cache")
      o.codeInfoPair (← o.getfield codeinst (sym "inferred")) (← o.getfield codeinst (sym "rettype"))
  else
    throw (.errorException "encountered invalid Core.OpaqueClosure object")


/--
Julia source: base/reflection.jl:437-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function code_typed_opaque_closure(oc::Core.OpaqueClosure, types;
                                   debuginfo::Symbol=:default,
                                   optimize::Bool=true,
                                   interp=nothing,
                                   _...)
    @nospecialize oc types
    (code, rt) = get_oc_code_rt(interp, oc, types, optimize)
    debuginfo === :none && remove_linenums!(code)
    return Any[Pair{CodeInfo,Any}(code, rt)]
end
```
-/
def codeTypedOpaqueClosure {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (oc types : V) (debuginfo : Sym)
    (optimize : Bool := true) (interp : Option V := none) : M World (List V) := do
  let (code, rt) ← o.destructure2 (← getOcCodeRt o interp oc types optimize)
  if o.compiler.egalSymbol debuginfo (o.compiler.symbol "none") then o.removeLinenums code
  pure [← o.codeInfoPair code rt]


-- Reason: The docstring of `code_ircode`, attached to its modelled method: no method body.
-- UNTRANSLATED
-- Source: base/reflection.jl:448-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     code_ircode(f, [types])
-- 
-- Return an array of pairs of `IRCode` and inferred return type if type inference succeeds.
-- The `Method` is included instead of `IRCode` otherwise.
-- 
-- See also: [`code_typed`](@ref)
-- 
-- # Internal Keyword Arguments
-- 
-- This section should be considered internal, and is only for who understands Julia compiler
-- internals.
-- 
-- - `world::UInt = Base.get_world_counter()`: optional, controls the world age to use
--   when looking up methods, use current world age if not specified.
-- - `interp::Core.Compiler.AbstractInterpreter = Core.Compiler.NativeInterpreter(world)`:
--   optional, controls the abstract interpreter to use, use the native interpreter if not specified.
-- - `optimize_until::Union{Int,String,Nothing} = nothing`: optional,
--   controls the optimization passes to run.
--   If it is a string, it specifies the name of the pass up to which the optimizer is run.
--   If it is an integer, it specifies the number of passes to run.
--   If it is `nothing` (default), all passes are run.
-- 
-- # Examples
-- 
-- One can put the argument types in a tuple to get the corresponding `code_ircode`.
-- 
-- ```julia
-- julia> Base.code_ircode(+, (Float64, Int64))
-- 1-element Vector{Any}:
--  388 1 ─ %1 = Base.sitofp(Float64, _3)::Float64
--     │   %2 = Base.add_float(_2, %1)::Float64
--     └──      return %2
--      => Float64
-- 
-- julia> Base.code_ircode(+, (Float64, Int64); optimize_until = "compact 1")
-- 1-element Vector{Any}:
--  388 1 ─ %1 = Base.promote(_2, _3)::Tuple{Float64, Float64}
--     │   %2 = Core._apply_iterate(Base.iterate, Base.:+, %1)::Float64
--     └──      return %2
--      => Float64
-- ```
-- """
-- /Source

-- Reason: The docstring of `code_ircode_by_type`: no method body.
-- UNTRANSLATED
-- Source: base/reflection.jl:504-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     code_ircode_by_type(types::Type{<:Tuple}; ...)
-- 
-- Similar to [`code_ircode`](@ref), except the argument is a tuple type describing
-- a full signature to query.
-- """
-- /Source


/--
Julia source: base/reflection.jl:511-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function code_ircode_by_type(
    @nospecialize(tt::Type);
    world::UInt=get_world_counter(),
    interp=nothing,
    optimize_until::Union{Int,String,Nothing}=nothing,
)
    passed_interp = interp
    interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp
    (ccall(:jl_is_in_pure_context, Bool, ()) || world == typemax(UInt)) &&
        error("code reflection cannot be used from generated functions")
    tt = to_tuple_type(tt)
    matches = invoke_interp_compiler(passed_interp, :_findall_matches, interp, tt)
    matches === nothing && raise_match_failure(:code_ircode, tt)
    asts = []
    for match in matches.matches
        match = match::Core.MethodMatch
        (code, ty) = invoke_interp_compiler(passed_interp, :typeinf_ircode, interp, match, optimize_until)
        if code === nothing
            push!(asts, match.method => Any)
        else
            push!(asts, code => ty)
        end
    end
    return asts
end
```
-/
def codeIrcodeByType {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (tt : V) (world : U)
    (interp : Option V := none) (optimizeUntil : V) : M World (List V) := do
  let passedInterp := interp
  let interp ← o.defaultInterp passedInterp world
  if ← o.jlIsInPureContext then throw (.errorException "code reflection cannot be used from generated functions")
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  let tt ← JuliaLean.base.runtime_internals.toTupleType o.types tt
  let found ← o.call passedInterp "_findall_matches" [interp, tt]
  if o.isNothing found then o.raise "code_ircode" tt
  let mut asts : List V := []
  for each in ← o.matchList found do
    let each ← o.typeassert each "Core.MethodMatch"
    let (code, ty) ← o.destructure2 (← o.call passedInterp "typeinf_ircode" [interp, each, optimizeUntil])
    if o.isNothing code then
      asts := asts ++ [← o.pair (← o.getfield each (o.compiler.symbol "method")) o.types.any]
    else
      asts := asts ++ [← o.pair code ty]
  pure asts


/--
Julia source: base/reflection.jl:536-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function _builtin_return_type(passed_interp, interp,
                              @nospecialize(f::Core.Builtin), @nospecialize(types))
    argtypes = Any[to_tuple_type(types).parameters...]
    rt = invoke_interp_compiler(passed_interp, :builtin_tfunction, interp, f, argtypes, nothing)
    return invoke_interp_compiler(passed_interp, :widenconst, rt)
end
```
-/
def builtinReturnType {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (passedInterp : Option V)
    (interp f types : V) : M World V := do
  let argtypes ← o.anyVector (← o.tupleParameters types)
  let rt ← o.call passedInterp "builtin_tfunction" [interp, f, argtypes, o.nothing]
  o.call passedInterp "widenconst" [rt]


/--
Julia source: base/reflection.jl:543-551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function _builtin_effects(passed_interp, interp,
                          @nospecialize(f::Core.Builtin), @nospecialize(types))
    argtypes = Any[to_tuple_type(types).parameters...]
    rt = invoke_interp_compiler(passed_interp, :builtin_tfunction, interp, f, argtypes, nothing)
    return invoke_interp_compiler(passed_interp, :builtin_effects,
        invoke_interp_compiler(passed_interp, :typeinf_lattice, interp),
        f, argtypes, rt)
end
```
-/
def builtinEffects {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (passedInterp : Option V)
    (interp f types : V) : M World V := do
  let argtypes ← o.anyVector (← o.tupleParameters types)
  let rt ← o.call passedInterp "builtin_tfunction" [interp, f, argtypes, o.nothing]
  let lattice ← o.call passedInterp "typeinf_lattice" [interp]
  o.call passedInterp "builtin_effects" [lattice, f, argtypes, rt]


/--
Julia source: base/reflection.jl:552-557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function _builtin_exception_type(passed_interp, interp,
                                 @nospecialize(f::Core.Builtin), @nospecialize(types))
    effects = _builtin_effects(passed_interp, interp, f, types)
    return invoke_interp_compiler(passed_interp, :is_nothrow, effects) ? Union{} : Any
end
```
-/
def builtinExceptionType {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (passedInterp : Option V)
    (interp f types : V) : M World V := do
  let effects ← builtinEffects o passedInterp interp f types
  if ← o.asCondition (← o.call passedInterp "is_nothrow" [effects]) then pure o.types.bottom
  else pure o.types.any

-- Source context (declarations and comments)
-- Source: base/reflection.jl:499-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/reflection.jl:610-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function return_types(@nospecialize(f), @nospecialize(types=default_tt(f));
                      world::UInt=get_world_counter(),
                      interp=nothing)
    passed_interp = interp
    interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp
    check_generated_context(world)
    if isa(f, Core.OpaqueClosure)
        _, rt = only(code_typed_opaque_closure(f, types; interp=passed_interp))
        return Any[rt]
    elseif isa(f, Core.Builtin)
        return Any[_builtin_return_type(passed_interp, interp, f, types)]
    end
    tt = signature_type(f, types)
    matches = invoke_interp_compiler(passed_interp, :_findall_matches, interp, tt)
    matches === nothing && raise_match_failure(:return_types, tt)
    rts = Any[]
    for match in matches.matches
        ty = invoke_interp_compiler(passed_interp, :typeinf_type, interp, match::Core.MethodMatch)
        push!(rts, something(ty, Any))
    end
    return rts
end
```
-/
def returnTypes {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (f types : V) (world : U)
    (interp : Option V := none) : M World (List V) := do
  let passedInterp := interp
  let interp ← o.defaultInterp passedInterp world
  let _ ← checkGeneratedContext o.jlIsInPureContext world
  if o.isOpaqueClosure f then
    let (_, rt) ← o.destructure2 (← onlyPair
      (← codeTypedOpaqueClosure o f types (o.compiler.symbol "default") (interp := passedInterp)))
    return [rt]
  else if o.isBuiltin f then
    return [← builtinReturnType o passedInterp interp f types]
  let tt ← JuliaLean.base.runtime_internals.signatureType o.types f types
  let found ← o.call passedInterp "_findall_matches" [interp, tt]
  if o.isNothing found then o.raise "return_types" tt
  let mut rts : List V := []
  for each in ← o.matchList found do
    let ty ← o.call passedInterp "typeinf_type" [interp, ← o.typeassert each "Core.MethodMatch"]
    rts := rts ++ [← o.something ty o.types.any]
  pure rts
where
  /-- `only(xs)`: `ArgumentError` unless `xs` has one element. -/
  onlyPair (xs : List V) : M World V :=
    match xs with
    | [x] => pure x
    | [] => throw (.jl (.argumentError "Collection is empty, must contain exactly 1 element"))
    | _ => throw (.jl (.argumentError "Collection has multiple elements, must contain exactly 1 element"))


-- Reason: The docstring of `infer_return_type`: no method body.
-- UNTRANSLATED
-- Source: base/reflection.jl:632-679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.infer_return_type(
--         f, types=default_tt(f);
--         world::UInt=get_world_counter(),
--         interp::Core.Compiler.AbstractInterpreter=Core.Compiler.NativeInterpreter(world)) -> rt::Type
-- 
-- Return an inferred return type of the function call specified by `f` and `types`.
-- 
-- # Arguments
-- - `f`: The function to analyze.
-- - `types` (optional): The argument types of the function. Defaults to the default tuple type of `f`.
-- - `world` (optional): The world counter to use for the analysis. Defaults to the current world counter.
-- - `interp` (optional): The abstract interpreter to use for the analysis. Defaults to a new `Core.Compiler.NativeInterpreter` with the specified `world`.
-- 
-- # Returns
-- - `rt::Type`: An inferred return type of the function call specified by the given call signature.
-- 
-- !!! note
--     Note that, different from [`Base.return_types`](@ref), this doesn't give you the list
--     return types of every possible method matching with the given `f` and `types`.
--     It returns a single return type, taking into account all potential outcomes of
--     any function call entailed by the given signature type.
-- 
-- # Examples
-- 
-- ```julia
-- julia> checksym(::Symbol) = :symbol;
-- 
-- julia> checksym(x::Any) = x;
-- 
-- julia> Base.infer_return_type(checksym, (Union{Symbol,String},))
-- Union{String, Symbol}
-- 
-- julia> Base.return_types(checksym, (Union{Symbol,String},))
-- 2-element Vector{Any}:
--  Symbol
--  Union{String, Symbol}
-- ```
-- 
-- It's important to note the difference here: `Base.return_types` gives back inferred results
-- for each method that matches the given signature `checksym(::Union{Symbol,String})`.
-- On the other hand `Base.infer_return_type` returns one collective result that sums up all those possibilities.
-- 
-- !!! warning
--     The `Base.infer_return_type` function should not be used from generated functions;
--     doing so will result in an error.
-- """
-- /Source


/--
Julia source: base/reflection.jl:680-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function infer_return_type(@nospecialize(f), @nospecialize(types=default_tt(f));
                           world::UInt=get_world_counter(),
                           interp=nothing)
    passed_interp = interp
    interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp
    check_generated_context(world)
    if isa(f, Core.OpaqueClosure)
        return last(only(code_typed_opaque_closure(f, types; interp=passed_interp)))
    elseif isa(f, Core.Builtin)
        return _builtin_return_type(passed_interp, interp, f, types)
    end
    tt = signature_type(f, types)
    matches = invoke_interp_compiler(passed_interp, :_findall_matches, interp, tt)
    matches === nothing && raise_match_failure(:infer_return_type, tt)
    rt = Union{}
    for match in matches.matches
        ty = invoke_interp_compiler(passed_interp, :typeinf_type, interp, match::Core.MethodMatch)
        rt = invoke_interp_compiler(passed_interp, :tmerge, rt, something(ty, Any))
    end
    return rt
end
```
-/
def inferReturnType {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (f types : V) (world : U)
    (interp : Option V := none) : M World V := do
  let passedInterp := interp
  let interp ← o.defaultInterp passedInterp world
  let _ ← checkGeneratedContext o.jlIsInPureContext world
  if o.isOpaqueClosure f then
    let (_, rt) ← o.destructure2 (← returnTypes.onlyPair
      (← codeTypedOpaqueClosure o f types (o.compiler.symbol "default") (interp := passedInterp)))
    return rt
  else if o.isBuiltin f then
    return ← builtinReturnType o passedInterp interp f types
  let tt ← JuliaLean.base.runtime_internals.signatureType o.types f types
  let found ← o.call passedInterp "_findall_matches" [interp, tt]
  if o.isNothing found then o.raise "infer_return_type" tt
  let mut rt := o.types.bottom
  for each in ← o.matchList found do
    let ty ← o.call passedInterp "typeinf_type" [interp, ← o.typeassert each "Core.MethodMatch"]
    rt ← o.call passedInterp "tmerge" [rt, ← o.something ty o.types.any]
  pure rt


-- Reason: The docstring of `infer_exception_types`: no method body.
-- UNTRANSLATED
-- Source: base/reflection.jl:701-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.infer_exception_types(
--         f, types=default_tt(f);
--         world::UInt=get_world_counter(),
--         interp::NativeInterpreter=Core.Compiler.NativeInterpreter(world)) -> excts::Vector{Any}
-- 
-- Return a list of possible exception types for a given function `f` and argument types `types`.
-- The list corresponds to the results of type inference on all the possible method match
-- candidates for `f` and `types` (see also [`methods(f, types)`](@ref methods).
-- It works like [`Base.return_types`](@ref), but it infers the exception types instead of the return types.
-- 
-- # Arguments
-- - `f`: The function to analyze.
-- - `types` (optional): The argument types of the function. Defaults to the default tuple type of `f`.
-- - `world` (optional): The world counter to use for the analysis. Defaults to the current world counter.
-- - `interp` (optional): The abstract interpreter to use for the analysis. Defaults to a new `Core.Compiler.NativeInterpreter` with the specified `world`.
-- 
-- # Returns
-- - `excts::Vector{Any}`: The list of exception types that are figured out by inference on
--   methods matching with the given `f` and `types`. The list's order matches the order
--   returned by `methods(f, types)`.
-- 
-- # Examples
-- 
-- ```julia
-- julia> throw_if_number(::Number) = error("number is given");
-- 
-- julia> throw_if_number(::Any) = nothing;
-- 
-- julia> Base.infer_exception_types(throw_if_number, (Int,))
-- 1-element Vector{Any}:
--  ErrorException
-- 
-- julia> methods(throw_if_number, (Any,))
-- # 2 methods for generic function "throw_if_number" from Main:
--  [1] throw_if_number(x::Number)
--      @ REPL[1]:1
--  [2] throw_if_number(::Any)
--      @ REPL[2]:1
-- 
-- julia> Base.infer_exception_types(throw_if_number, (Any,))
-- 2-element Vector{Any}:
--  ErrorException # the result of inference on `throw_if_number(::Number)`
--  Union{}        # the result of inference on `throw_if_number(::Any)`
-- ```
-- 
-- !!! warning
--     The `Base.infer_exception_types` function should not be used from generated functions;
--     doing so will result in an error.
-- """
-- /Source


/--
Julia source: base/reflection.jl:752-777 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function infer_exception_types(@nospecialize(f), @nospecialize(types=default_tt(f));
                               world::UInt=get_world_counter(),
                               interp=nothing)
    passed_interp = interp
    interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp
    check_generated_context(world)
    if isa(f, Core.OpaqueClosure)
        return Any[Any] # TODO
    elseif isa(f, Core.Builtin)
        return Any[_builtin_exception_type(passed_interp, interp, f, types)]
    end
    tt = signature_type(f, types)
    matches = invoke_interp_compiler(passed_interp, :_findall_matches, interp, tt)
    matches === nothing && raise_match_failure(:infer_exception_types, tt)
    excts = Any[]
    for match in matches.matches
        frame = invoke_interp_compiler(passed_interp, :typeinf_frame, interp, match::Core.MethodMatch, #=run_optimizer=#false)
        if frame === nothing
            exct = Any
        else
            exct = invoke_interp_compiler(passed_interp, :widenconst, frame.result.exc_result)
        end
        push!(excts, exct)
    end
    return excts
end
```
-/
def inferExceptionTypes {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (f types : V) (world : U)
    (interp : Option V := none) : M World (List V) := do
  let passedInterp := interp
  let interp ← o.defaultInterp passedInterp world
  let _ ← checkGeneratedContext o.jlIsInPureContext world
  if o.isOpaqueClosure f then
    return [o.types.any]
  else if o.isBuiltin f then
    return [← builtinExceptionType o passedInterp interp f types]
  let tt ← JuliaLean.base.runtime_internals.signatureType o.types f types
  let found ← o.call passedInterp "_findall_matches" [interp, tt]
  if o.isNothing found then o.raise "infer_exception_types" tt
  let mut excts : List V := []
  for each in ← o.matchList found do
    let frame ← o.call passedInterp "typeinf_frame"
      [interp, ← o.typeassert each "Core.MethodMatch", o.ofBool false]
    let exct ← if o.isNothing frame then pure o.types.any
      else do
        let result ← o.getfield frame (o.compiler.symbol "result")
        o.call passedInterp "widenconst" [← o.getfield result (o.compiler.symbol "exc_result")]
    excts := excts ++ [exct]
  pure excts


-- Reason: The docstring of `infer_exception_type`: no method body.
-- UNTRANSLATED
-- Source: base/reflection.jl:778-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.infer_exception_type(
--         f, types=default_tt(f);
--         world::UInt=get_world_counter(),
--         interp::Core.Compiler.AbstractInterpreter=Core.Compiler.NativeInterpreter(world)) -> exct::Type
-- 
-- Return the type of exception potentially thrown by the function call specified by `f` and `types`.
-- 
-- # Arguments
-- - `f`: The function to analyze.
-- - `types` (optional): The argument types of the function. Defaults to the default tuple type of `f`.
-- - `world` (optional): The world counter to use for the analysis. Defaults to the current world counter.
-- - `interp` (optional): The abstract interpreter to use for the analysis. Defaults to a new `Core.Compiler.NativeInterpreter` with the specified `world`.
-- 
-- # Returns
-- - `exct::Type`: The inferred type of exception that can be thrown by the function call
--   specified by the given call signature.
-- 
-- !!! note
--     Note that, different from [`Base.infer_exception_types`](@ref), this doesn't give you the list
--     exception types for every possible matching method with the given `f` and `types`.
--     It returns a single exception type, taking into account all potential outcomes of
--     any function call entailed by the given signature type.
-- 
-- # Examples
-- 
-- ```julia
-- julia> f1(x) = x * 2;
-- 
-- julia> Base.infer_exception_type(f1, (Int,))
-- Union{}
-- ```
-- 
-- The exception inferred as `Union{}` indicates that `f1(::Int)` will not throw any exception.
-- 
-- ```julia
-- julia> f2(x::Int) = x * 2;
-- 
-- julia> Base.infer_exception_type(f2, (Integer,))
-- MethodError
-- ```
-- 
-- This case is pretty much the same as with `f1`, but there's a key difference to note. For
-- `f2`, the argument type is limited to `Int`, while the argument type is given as `Tuple{Integer}`.
-- Because of this, taking into account the chance of the method error entailed by the call
-- signature, the exception type is widened to `MethodError`.
-- 
-- !!! warning
--     The `Base.infer_exception_type` function should not be used from generated functions;
--     doing so will result in an error.
-- """
-- /Source


/--
Julia source: base/reflection.jl:830-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function infer_exception_type(@nospecialize(f), @nospecialize(types=default_tt(f));
                              world::UInt=get_world_counter(),
                              interp=nothing)
    passed_interp = interp
    interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp
    check_generated_context(world)
    if isa(f, Core.OpaqueClosure)
        return Any # TODO
    elseif isa(f, Core.Builtin)
        return _builtin_exception_type(passed_interp, interp, f, types)
    end
    tt = signature_type(f, types)
    exct = invoke_interp_compiler(passed_interp, :_infer_exception_type, interp, tt, false)
    exct === nothing && raise_match_failure(:infer_exception_type, tt)
    return exct
end
```
-/
def inferExceptionType {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (f types : V) (world : U)
    (interp : Option V := none) : M World V := do
  let passedInterp := interp
  let interp ← o.defaultInterp passedInterp world
  let _ ← checkGeneratedContext o.jlIsInPureContext world
  if o.isOpaqueClosure f then
    return o.types.any
  else if o.isBuiltin f then
    return ← builtinExceptionType o passedInterp interp f types
  let tt ← JuliaLean.base.runtime_internals.signatureType o.types f types
  let exct ← o.call passedInterp "_infer_exception_type" [interp, tt, o.ofBool false]
  if o.isNothing exct then o.raise "infer_exception_type" tt
  pure exct


-- Reason: The docstring of `infer_effects`: no method body.
-- UNTRANSLATED
-- Source: base/reflection.jl:846-907 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.infer_effects(
--         f, types=default_tt(f);
--         optimize::Bool=true,
--         world::UInt=get_world_counter(),
--         interp::Core.Compiler.AbstractInterpreter=Core.Compiler.NativeInterpreter(world)) -> effects::Effects
-- 
-- Return the possible computation effects of the function call specified by `f` and `types`.
-- 
-- # Arguments
-- - `f`: The function to analyze.
-- - `types` (optional): The argument types of the function. Defaults to the default tuple type of `f`.
-- - `optimize` (optional): Whether to run additional effects refinements based on post-optimization analysis.
-- - `world` (optional): The world counter to use for the analysis. Defaults to the current world counter.
-- - `interp` (optional): The abstract interpreter to use for the analysis. Defaults to a new `Core.Compiler.NativeInterpreter` with the specified `world`.
-- 
-- # Returns
-- - `effects::Effects`: The computed effects of the function call specified by the given call signature.
--   See the documentation of [`Effects`](@ref Core.Compiler.Effects) or [`Base.@assume_effects`](@ref)
--   for more information on the various effect properties.
-- 
-- !!! note
--     Note that, different from [`Base.return_types`](@ref), this doesn't give you the list
--     effect analysis results for every possible matching method with the given `f` and `types`.
--     It returns a single effect, taking into account all potential outcomes of any function
--     call entailed by the given signature type.
-- 
-- # Examples
-- 
-- ```julia
-- julia> f1(x) = x * 2;
-- 
-- julia> Base.infer_effects(f1, (Int,))
-- (+c,+e,+re,+n,+t,+s,+m,+u,+o,+r)
-- ```
-- 
-- This function will return an `Effects` object with information about the computational
-- effects of the function `f1` when called with an `Int` argument.
-- 
-- ```julia
-- julia> f2(x::Int) = x * 2;
-- 
-- julia> Base.infer_effects(f2, (Integer,))
-- (+c,+e,+re,!n,+t,+s,+m,+u,+o,+r)
-- ```
-- 
-- This case is pretty much the same as with `f1`, but there's a key difference to note. For
-- `f2`, the argument type is limited to `Int`, while the argument type is given as `Tuple{Integer}`.
-- Because of this, taking into account the chance of the method error entailed by the call
-- signature, the `:nothrow` bit gets tainted.
-- 
-- !!! warning
--     The `Base.infer_effects` function should not be used from generated functions;
--     doing so will result in an error.
-- 
-- $(Compiler.effects_key_string)
-- 
-- # See Also
-- - [`Compiler.Effects`](@ref): A type representing the computational effects of a method call.
-- - [`Base.@assume_effects`](@ref): A macro for making assumptions about the effects of a method.
-- """
-- /Source


/--
Julia source: base/reflection.jl:908-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function infer_effects(@nospecialize(f), @nospecialize(types=default_tt(f));
                       optimize::Bool=true,
                       world::UInt=get_world_counter(),
                       interp=nothing)
    passed_interp = interp
    interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp
    check_generated_context(world)
    if isa(f, Core.Builtin)
        return _builtin_effects(passed_interp, interp, f, types)
    end
    tt = signature_type(f, types)
    effects = invoke_interp_compiler(passed_interp, :_infer_effects, interp, tt, optimize)
    effects === nothing && raise_match_failure(:infer_effects, tt)
    return effects
end
```
-/
def inferEffects {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (f types : V) (optimize : Bool := true)
    (world : U) (interp : Option V := none) : M World V := do
  let passedInterp := interp
  let interp ← o.defaultInterp passedInterp world
  let _ ← checkGeneratedContext o.jlIsInPureContext world
  if o.isBuiltin f then
    return ← builtinEffects o passedInterp interp f types
  let tt ← JuliaLean.base.runtime_internals.signatureType o.types f types
  let effects ← o.call passedInterp "_infer_effects" [interp, tt, o.ofBool optimize]
  if o.isNothing effects then o.raise "infer_effects" tt
  pure effects


-- Reason: The docstring of `print_statement_costs`: no method body.
-- UNTRANSLATED
-- Source: base/reflection.jl:923-929 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     print_statement_costs(io::IO, f, types)
-- 
-- Print type-inferred and optimized code for `f` given argument types `types`,
-- prepending each line with its cost as estimated by the compiler's inlining engine.
-- """
-- /Source

/--
Julia source: base/reflection.jl:930-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_statement_costs(io::IO, @nospecialize(f), @nospecialize(t); kwargs...)
    tt = signature_type(f, t)
    print_statement_costs(io, tt; kwargs...)
end
```
-/
def printStatementCostsFunction {World V D N Mod P Sym Io Keywords : Type}
    (ops : TypeOps World V D N Mod P Sym) (printCosts : Io → V → Keywords → M World Unit)
    (io : Io) (f t : V) (kwargs : Keywords) : M World Unit := do
  let tt ← JuliaLean.base.runtime_internals.signatureType ops f t
  printCosts io tt kwargs

/--
Julia source: base/reflection.jl:966-966 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print_statement_costs(args...; kwargs...) = print_statement_costs(stdout, args...; kwargs...)
```
-/
def printStatementCostsStdout {World Io Args Keywords Result : Type} (stdout : M World Io)
    (printCosts : Io → Args → Keywords → M World Result) (args : Args) (kwargs : Keywords) : M World Result := do
  printCosts (← stdout) args kwargs

/--
Julia source: base/reflection.jl:935-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_statement_costs(io::IO, @nospecialize(tt::Type);
                               world::UInt=get_world_counter(),
                               interp=nothing)
    passed_interp = interp
    interp = passed_interp === nothing ? invoke_default_compiler(:_default_interp, world) : interp
    tt = to_tuple_type(tt)
    world == typemax(UInt) && error("code reflection cannot be used from generated functions")
    matches = invoke_interp_compiler(passed_interp, :_findall_matches, interp, tt)
    matches === nothing && raise_match_failure(:print_statement_costs, tt)
    cst = Int[]
    for match in matches.matches
        match = match::Core.MethodMatch
        println(io, match.method)
        code = invoke_interp_compiler(passed_interp, :typeinf_code, interp, match, true)
        if code === nothing
            println(io, "  inference not successful")
        else
            empty!(cst)
            resize!(cst, length(code.code))
            maxcost = invoke_interp_compiler(passed_interp, :statement_costs!, interp, cst, code.code, code, match)
            nd = ndigits(maxcost)
            irshow_config = IRShow.IRShowConfig() do io, linestart, idx
                print(io, idx > 0 ? lpad(cst[idx], nd+1) : " "^(nd+1), " ")
                return ""
            end
            IRShow.show_ir(io, code, irshow_config)
        end
        println(io)
    end
end
```
-/
def printStatementCosts {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (io : Io) (tt : V) (world : U)
    (interp : Option V := none) : M World Unit := do
  let passedInterp := interp
  let interp ← o.defaultInterp passedInterp world
  let tt ← JuliaLean.base.runtime_internals.toTupleType o.types tt
  if world == JInt.typemax .u64 then throw (.errorException "code reflection cannot be used from generated functions")
  let found ← o.call passedInterp "_findall_matches" [interp, tt]
  if o.isNothing found then o.raise "print_statement_costs" tt
  let sym := o.compiler.symbol
  let cst ← o.newIntVector
  for each in ← o.matchList found do
    let each ← o.typeassert each "Core.MethodMatch"
    o.printlnValue io (← o.getfield each (sym "method"))
    let code ← o.call passedInterp "typeinf_code" [interp, each, o.ofBool true]
    if o.isNothing code then
      o.printString io "  inference not successful\n"
    else
      o.emptyBang cst
      let statements ← o.getfield code (sym "code")
      o.resizeBang cst (← o.length statements)
      let maxcost ← o.call passedInterp "statement_costs!" [interp, cst, statements, code, each]
      let nd ← o.ndigits maxcost
      -- the `IRShowConfig` line function `(io, linestart, idx) -> ...`
      let linefn (io : Io) (_linestart idx : I) : M World String := do
        let text ← if idx.val > 0 then o.lpad (← o.getindexInt cst idx) (nd + JInt.wrap .i64 1)
          else repeatSpace (nd + JInt.wrap .i64 1)
        o.printString io text
        o.printString io " "
        pure ""
      o.showIr io code linefn
    o.printString io "\n"
where
  /-- `" "^n`: `ArgumentError` for a negative `n`. -/
  repeatSpace (n : I) : M World String :=
    if n.val < 0 then throw (.jl (.argumentError s!"can't repeat a string {n.val} times"))
    else pure (String.ofList (List.replicate n.val.toNat ' '))

-- Source context (declarations and comments)
-- Source: base/reflection.jl:934-934 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source context (declarations and comments)
-- Source: base/reflection.jl:965-965 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/reflection.jl:1155-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bodyfunction(basemethod::Method; world::UInt=get_world_counter())
    fmod = parentmodule(basemethod)
    # The lowered code for `basemethod` should look like
    #   %1 = mkw(kwvalues..., #self#, args...)
    #        return %1
    # where `mkw` is the name of the "active" keyword body-function.
    ast = uncompressed_ast(basemethod)
    if isa(ast, Core.CodeInfo) && length(ast.code) >= 2
        callexpr = ast.code[end-1]
        if isa(callexpr, Expr) && callexpr.head === :call
            fsym = callexpr.args[1]
            while true
                if isa(fsym, Symbol)
                    return invoke_in_world(world, getglobal, fmod, fsym)
                elseif isa(fsym, GlobalRef)
                    if fsym.mod === Core && fsym.name === :_apply
                        fsym = callexpr.args[2]
                    elseif fsym.mod === Core && fsym.name === :_apply_iterate
                        fsym = callexpr.args[3]
                    end
                    if isa(fsym, Symbol)
                        return invoke_in_world(world, getglobal, fmod, fsym)::Function
                    elseif isa(fsym, GlobalRef)
                        return invoke_in_world(world, getglobal, fsym.mod, fsym.name)::Function
                    elseif isa(fsym, Core.SSAValue)
                        fsym = ast.code[fsym.id]
                    else
                        return nothing
                    end
                elseif isa(fsym, Core.SSAValue)
                    fsym = ast.code[fsym.id]
                else
                    return nothing
                end
            end
        end
    end
    return nothing
end
```
-/
def bodyfunction {World V D N Mod P Sym Function Vector Io : Type}
    (o : InferOps World V D N Mod P Sym Function Vector Io) (basemethod : V) (world : U) :
    M World V := do
  let fmod := o.parentmodule basemethod
  let sym := o.compiler.symbol
  let ast ← o.uncompressedAst basemethod
  if !o.isCodeInfo ast then return o.nothing
  let code ← o.elements (← o.getfield ast (sym "code"))
  if code.length < 2 then return o.nothing
  let callexpr ← InferOps.atIdx code (JInt.wrap .i64 (code.length - 1))
  let some (head, args) := o.asExpr callexpr | return o.nothing
  if !o.compiler.egalSymbol head (sym "call") then return o.nothing
  let fsym ← InferOps.atIdx args (JInt.wrap .i64 1)
  whileLoop (fun fsym : V => do
    if let some name := o.asSymbol fsym then
      return .inl (← o.getglobalInWorld world fmod name)
    if let some (mod, name) := o.asGlobalRef fsym then
      let fsym ← if o.isCore mod && o.compiler.egalSymbol name (sym "_apply") then
          InferOps.atIdx args (JInt.wrap .i64 2)
        else if o.isCore mod && o.compiler.egalSymbol name (sym "_apply_iterate") then
          InferOps.atIdx args (JInt.wrap .i64 3)
        else pure fsym
      if let some name := o.asSymbol fsym then
        return .inl (← o.typeassert (← o.getglobalInWorld world fmod name) "Function")
      if let some (mod, name) := o.asGlobalRef fsym then
        return .inl (← o.typeassert (← o.getglobalInWorld world mod name) "Function")
      if let some id := o.asSSAValue fsym then
        return .inr (← InferOps.atIdx code id)
      return .inl o.nothing
    if let some id := o.asSSAValue fsym then
      return .inr (← InferOps.atIdx code id)
    return .inl o.nothing) fsym

-- Reason: this blank line only separates the macro and helper function.
-- UNTRANSLATED
-- Source: base/reflection.jl:1449-1449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/reflection.jl:1451-1461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function flatten(xs)
        out = Any[]
        for x in xs
            if isexpr(x, :tuple)
                append!(out, x.args)
            else
                push!(out, x)
            end
        end
        return out
    end
```
-/
private def flattenCallArgs {L : Type} (xs : List (JuliaLean.base.expr.Value L)) :
    List (JuliaLean.base.expr.Value L) :=
  xs.foldl (fun out x =>
    match x with
    | .expr "tuple" args => out ++ args
    | _ => out ++ [x]) []

/--
Julia source: base/reflection.jl:1450-1497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function destructure_callex(topmod::Module, @nospecialize(ex))
    function flatten(xs)
        out = Any[]
        for x in xs
            if isexpr(x, :tuple)
                append!(out, x.args)
            else
                push!(out, x)
            end
        end
        return out
    end

    kwargs = Any[]
    if isexpr(ex, :call) # `f(args...)`
        f = first(ex.args)
        args = Any[]
        for x in ex.args[2:end]
            if isexpr(x, :parameters)
                append!(kwargs, x.args)
            elseif isexpr(x, :kw)
                push!(kwargs, x)
            else
                push!(args, x)
            end
        end
    elseif isexpr(ex, :.)   # `x.f`
        f = GlobalRef(topmod, :getproperty)
        args = flatten(ex.args)
    elseif isexpr(ex, :ref) # `x[i]`
        f = GlobalRef(topmod, :getindex)
        args = flatten(ex.args)
    elseif isexpr(ex, :(=)) # `x.f = v` or `x[i] = v`
        lhs, rhs = ex.args
        if isexpr(lhs, :.)
            f = GlobalRef(topmod, :setproperty!)
            args = flatten(Any[lhs.args..., rhs])
        elseif isexpr(lhs, :ref)
            f = GlobalRef(topmod, :setindex!)
            args = flatten(Any[lhs.args[1], rhs, lhs.args[2]])
        else
            throw(ArgumentError("expected a `setproperty!` expression `x.f = v` or `setindex!` expression `x[i] = v`"))
        end
    else
        throw(ArgumentError("expected a `:call` expression `f(args...; kwargs...)`"))
    end
    return f, args, kwargs
end
```
-/
def destructureCallex {World Module L : Type} (moduleValue : Module → L) (topmod : Module)
    (ex : JuliaLean.base.expr.Value L) :
    M World (JuliaLean.base.expr.Value L × List (JuliaLean.base.expr.Value L) × List (JuliaLean.base.expr.Value L)) := do
  let mut kwargs : List (JuliaLean.base.expr.Value L) := []
  let (fn, args) ←
    match ex with
    | .expr "call" callArgs => do
      let fn ← match callArgs with
        | fn :: _ => pure fn
        | [] => throw (.jl (.argumentError "collection must be non-empty"))
      let mut args : List (JuliaLean.base.expr.Value L) := []
      for x in callArgs.drop 1 do
        match x with
        | .expr "parameters" values => kwargs := kwargs ++ values
        | .expr "kw" _ => kwargs := kwargs ++ [x]
        | _ => args := args ++ [x]
      pure (fn, args)
    | .expr "." exprArgs =>
      pure (.globalRef (moduleValue topmod) "getproperty", flattenCallArgs exprArgs)
    | .expr "ref" exprArgs =>
      pure (.globalRef (moduleValue topmod) "getindex", flattenCallArgs exprArgs)
    | .expr "=" assignmentArgs => do
      let lhs ← match assignmentArgs with
        | lhs :: _ => pure lhs
        | [] => throw (.jl .boundsError)
      let rhs ← match assignmentArgs.drop 1 with
        | rhs :: _ => pure rhs
        | [] => throw (.jl .boundsError)
      match lhs with
      | .expr "." lhsArgs =>
        pure (.globalRef (moduleValue topmod) "setproperty!", flattenCallArgs (lhsArgs ++ [rhs]))
      | .expr "ref" lhsArgs =>
        let base ← match lhsArgs with
          | base :: _ => pure base
          | [] => throw (.jl .boundsError)
        let index ← match lhsArgs.drop 1 with
          | index :: _ => pure index
          | [] => throw (.jl .boundsError)
        pure (.globalRef (moduleValue topmod) "setindex!",
          flattenCallArgs [base, rhs, index])
      | _ =>
        throw (.jl (.argumentError "expected a `setproperty!` expression `x.f = v` or `setindex!` expression `x[i] = v`"))
    | _ => throw (.jl (.argumentError "expected a `:call` expression `f(args...; kwargs...)`"))
  pure (fn, args, kwargs)

/--
Julia source: base/reflection.jl:1345-1363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro invoke(ex)
    topmod = _topmod(__module__)
    f, args, kwargs = destructure_callex(topmod, ex)
    types = Expr(:curly, :Tuple)
    out = Expr(:call, GlobalRef(Core, :invoke))
    isempty(kwargs) || push!(out.args, Expr(:parameters, Any[esc(kw) for kw in kwargs]...))
    push!(out.args, esc(f))
    push!(out.args, types)
    for arg in args
        if isexpr(arg, :(::))
            push!(out.args, esc(arg.args[1]))
            push!(types.args, esc(arg.args[2]))
        else
            push!(out.args, esc(arg))
            push!(types.args, Expr(:call, GlobalRef(Core, :Typeof), esc(arg)))
        end
    end
    return out
end
```
-/
def invokeMacro {World L : Type} (getTopmod : L → M World L) (caller core : L)
    (ex : Value L) : M World (Value L) := do
  let topmod ← getTopmod caller
  let (f, args, kwargs) ← destructureCallex id topmod ex
  let mut types : List (Value L) := [.symbol "Tuple"]
  let mut values : List (Value L) := []
  for arg in args do
    if isexpr arg "::" then
      let parts := match arg with | .expr _ parts => parts | _ => []
      let value ← atArg parts 1
      let type ← atArg parts 2
      values := values ++ [esc value]
      types := types ++ [esc type]
    else
      values := values ++ [esc arg]
      types := types ++ [.expr "call" [.globalRef core "Typeof", esc arg]]
  let kw := if kwargs.isEmpty then [] else [.expr "parameters" (kwargs.map esc)]
  pure (.expr "call" ([.globalRef core "invoke"] ++ kw ++ [esc f, .expr "curly" types] ++ values))
where
  atArg (parts : List (Value L)) (n : Nat) : M World (Value L) :=
    match parts[n - 1]? with
    | some value => pure value
    | none => throw (.jl .boundsError)


/--
Julia source: base/reflection.jl:1406-1448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro invokelatest(ex)
    topmod = _topmod(__module__)
    f, args, kwargs = destructure_callex(topmod, ex)

    if !isa(f, GlobalRef)
        out_f = Expr(:call, GlobalRef(Base, :invokelatest))
        isempty(kwargs) || push!(out_f.args, Expr(:parameters, Any[esc(kw) for kw in kwargs]...))

        if isexpr(f, :(.))
            s = :s
            check = quote
                $s = $(esc(f.args[1]))
                isa($s, Module)
            end
            push!(out_f.args, Expr(:(.), s, esc(f.args[2])))
        else
            push!(out_f.args, esc(f))
        end
        append!(out_f.args, Any[esc(arg) for arg in args])

        if @isdefined(s)
            f = :(GlobalRef($s, $(esc(f.args[2]))))
        elseif isa(f, Symbol)
            check = esc(:($(Expr(:isglobal, f))))
        else
            return out_f
        end
    end

    out_gr = Expr(:call, GlobalRef(Base, :invokelatest_gr))
    isempty(kwargs) || push!(out_gr.args, Expr(:parameters, Any[esc(kw) for kw in kwargs]...))
    push!(out_gr.args, isa(f, GlobalRef) ? QuoteNode(f) :
                       isa(f, Symbol) ? QuoteNode(GlobalRef(__module__, f)) :
                       f)
    append!(out_gr.args, Any[esc(arg) for arg in args])

    if isa(f, GlobalRef)
        return out_gr
    end

    # f::Symbol
    return :($check ? $out_gr : $out_f)
end
```
-/
def invokelatestMacro {World L : Type} (getTopmod : L → M World L) (caller baseModule : L)
    (sourceFile : Value L) (ex : Value L) : M World (Value L) := do
  let topmod ← getTopmod caller
  let (original, args, kwargs) ← destructureCallex id topmod ex
  let kw := if kwargs.isEmpty then [] else [.expr "parameters" (kwargs.map esc)]
  let mut f := original
  let mut check : Value L := .symbol "nothing"
  let mut outF : Value L := .symbol "nothing"
  let mut global : Bool := false
  if let .globalRef _ _ := f then global := true
  if !global then
    let target ← if isexpr f "." then do
        let parts := match f with | .expr _ parts => parts | _ => []
        let receiver ← atArg parts 1
        let field ← atArg parts 2
        check := .expr "block" [.lineNumberNode (JuliaLean.base.expr.i64 1417) sourceFile,
          .expr "=" [.symbol "s", esc receiver],
          .lineNumberNode (JuliaLean.base.expr.i64 1418) sourceFile,
          .expr "call" [.symbol "isa", .symbol "s", .symbol "Module"]]
        f := .expr "call" [.symbol "GlobalRef", .symbol "s", esc field]
        pure (.expr "." [.symbol "s", esc field])
      else pure (esc f)
    outF := .expr "call" ([.globalRef baseModule "invokelatest"] ++ kw ++ [target] ++ args.map esc)
    if !(isexpr original ".") then
      if let .symbol _ := original then check := esc (.expr "isglobal" [original])
      else return outF
  let globalTarget := match f with
    | .globalRef _ _ => .quoteNode f
    | .symbol name => .quoteNode (.globalRef caller name)
    | _ => f
  let outGr : Value L := .expr "call"
    ([.globalRef baseModule "invokelatest_gr"] ++ kw ++ [globalTarget] ++ args.map esc)
  if global then return outGr
  pure (.expr "if" [check, outGr, outF])
where
  atArg (parts : List (Value L)) (n : Nat) : M World (Value L) :=
    match parts[n - 1]? with
    | some value => pure value
    | none => throw (.jl .boundsError)


/--
Julia source: base/reflection.jl:1506-1514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function drop_all_caches()
    ccall(:jl_drop_all_caches, Cvoid, ())

    # Reset loading.jl world age so that loading code is regenerated
    _require_world_age[] = typemax(UInt)

    # Call Base.Compiler.activate!() after dropping caching to activate coverage of the Compiler code itself
    Base.Compiler.activate!()
end
```
-/
def dropAllCaches {World Result : Type} (jlDropAllCaches : M World Unit)
    (setRequireWorldAge : U → M World Unit) (activateCompiler : M World Result) : M World Result := do
  jlDropAllCaches
  setRequireWorldAge (JInt.typemax .u64)
  activateCompiler

/-! ## Source context (documentation and declarations) -/
-- Source: base/reflection.jl:1-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     code_lowered(f, types; generated=true, debuginfo=:default)
-- 
-- Return an array of the lowered forms (IR) for the methods matching the given generic function
-- and type signature.
-- 
-- If `generated` is `false`, the returned `CodeInfo` instances will correspond to fallback
-- implementations. An error is thrown if no fallback implementation exists.
-- If `generated` is `true`, these `CodeInfo` instances will correspond to the method bodies
-- yielded by expanding the generators.
-- 
-- The keyword `debuginfo` controls the amount of code metadata present in the output.
-- 
-- Note that an error will be thrown if `types` are not concrete types when `generated` is
-- `true` and any of the corresponding methods are an `@generated` method.
-- """
-- /Source

-- Source: base/reflection.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:91-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # this type mirrors jl_cgparams_t (documented in julia.h)
-- /Source

-- Source: base/reflection.jl:285-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
-- /Source

-- Source: base/reflection.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # otherwise returns `Tuple` that doesn't match with any signature
-- /Source

-- Source: base/reflection.jl:315-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:321-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const REFLECTION_COMPILER = RefValue{Union{Nothing, Module}}(nothing)
-- 
-- /Source

-- Source: base/reflection.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:336-336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:351-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:366-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     code_typed_by_type(types::Type{<:Tuple}; ...)
-- 
-- Similar to [`code_typed`](@ref), except the argument is a tuple type describing
-- a full signature to query.
-- """
-- /Source

-- Source: base/reflection.jl:558-558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:563-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # TODO rename `Base.return_types` to `Base.infer_return_types`
-- 
-- """
--     Base.return_types(
--         f, types=default_tt(f);
--         world::UInt=get_world_counter(),
--         interp::NativeInterpreter=Core.Compiler.NativeInterpreter(world)) -> rts::Vector{Any}
-- 
-- Return a list of possible return types for a given function `f` and argument types `types`.
-- The list corresponds to the results of type inference on all the possible method match
-- candidates for `f` and `types` (see also [`methods(f, types)`](@ref methods).
-- 
-- # Arguments
-- - `f`: The function to analyze.
-- - `types` (optional): The argument types of the function. Defaults to the default tuple type of `f`.
-- - `world` (optional): The world counter to use for the analysis. Defaults to the current world counter.
-- - `interp` (optional): The abstract interpreter to use for the analysis. Defaults to a new `Core.Compiler.NativeInterpreter` with the specified `world`.
-- 
-- # Returns
-- - `rts::Vector{Any}`: The list of return types that are figured out by inference on
--   methods matching with the given `f` and `types`. The list's order matches the order
--   returned by `methods(f, types)`.
-- 
-- # Examples
-- 
-- ```julia
-- julia> Base.return_types(sum, Tuple{Vector{Int}})
-- 1-element Vector{Any}:
--  Int64
-- 
-- julia> methods(sum, (Union{Vector{Int},UnitRange{Int}},))
-- # 2 methods for generic function "sum" from Base:
--  [1] sum(r::AbstractRange{<:Real})
--      @ range.jl:1399
--  [2] sum(a::AbstractArray; dims, kw...)
--      @ reducedim.jl:1010
-- 
-- julia> Base.return_types(sum, (Union{Vector{Int},UnitRange{Int}},))
-- 2-element Vector{Any}:
--  Int64 # the result of inference on sum(r::AbstractRange{<:Real})
--  Int64 # the result of inference on sum(a::AbstractArray; dims, kw...)
-- ```
-- 
-- !!! warning
--     The `Base.return_types` function should not be used from generated functions;
--     doing so will result in an error.
-- """
-- /Source

-- Source: base/reflection.jl:967-967 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:980-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     which(f, types)
-- 
-- Return the method of `f` (a `Method` object) that would be called for arguments of the given `types`.
-- 
-- If `types` is an abstract type, then the method that would be called by `invoke` is returned.
-- 
-- See also [`parentmodule`](@ref), [`@which`](@ref Main.InteractiveUtils.@which), [`@edit`](@ref Main.InteractiveUtils.@edit).
-- """
-- /Source

-- Source: base/reflection.jl:1004-1009 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     which(types::Type{<:Tuple})
-- 
-- Return the method that would be called by the given type signature (as a tuple type).
-- """
-- /Source

-- Source: base/reflection.jl:1014-1019 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     which(module::Module, symbo::Symbol)
-- 
-- Return the module in which the binding for the variable referenced by `symbol` in `module` was created.
-- """
-- /Source

-- Source: base/reflection.jl:1026-1035 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # function reflection
-- 
-- """
--     nameof(f::Function)::Symbol
-- 
-- Get the name of a generic `Function` as a symbol. For anonymous functions,
-- this is a compiler-generated name. For explicitly-declared subtypes of
-- `Function`, it is the name of the function's type.
-- """
-- /Source

-- Source: base/reflection.jl:1039-1039 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:1044-1050 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     parentmodule(f::Function)::Module
-- 
-- Determine the module containing the (first) definition of a generic
-- function.
-- """
-- /Source

-- Source: base/reflection.jl:1052-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     parentmodule(f::Function, types)::Module
-- 
-- Determine the module containing the first method of a generic function `f` matching
-- the specified `types`.
-- """
-- /Source

-- Source: base/reflection.jl:1066-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     parentmodule(m::Method)::Module
-- 
-- Return the module in which the given method `m` is defined.
-- 
-- !!! compat "Julia 1.10"
--     Passing a `Method` as an argument requires Julia 1.10 or later.
-- """
-- /Source

-- Source: base/reflection.jl:1076-1112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     hasmethod(f, t::Type{<:Tuple}[, kwnames]; world=get_world_counter())::Bool
-- 
-- Determine whether the given generic function has a method matching the given
-- `Tuple` of argument types with the upper bound of world age given by `world`.
-- 
-- If a tuple of keyword argument names `kwnames` is provided, this also checks
-- whether the method of `f` matching `t` has the given keyword argument names.
-- If the matching method accepts a variable number of keyword arguments, e.g.
-- with `kwargs...`, any names given in `kwnames` are considered valid. Otherwise
-- the provided names must be a subset of the method's keyword arguments.
-- 
-- See also [`applicable`](@ref).
-- 
-- !!! compat "Julia 1.2"
--     Providing keyword argument names requires Julia 1.2 or later.
-- 
-- # Examples
-- ```jldoctest
-- julia> hasmethod(length, Tuple{Array})
-- true
-- 
-- julia> f(; oranges=0) = oranges;
-- 
-- julia> hasmethod(f, Tuple{}, (:oranges,))
-- true
-- 
-- julia> hasmethod(f, Tuple{}, (:apples, :bananas))
-- false
-- 
-- julia> g(; xs...) = 4;
-- 
-- julia> hasmethod(g, Tuple{}, (:a, :b, :c, :d))  # g accepts arbitrary kwargs
-- true
-- ```
-- """
-- /Source

-- Source: base/reflection.jl:1116-1116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:1140-1154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     fbody = bodyfunction(basemethod::Method; world::UInt=Base.get_world_counter())
-- 
-- Find the keyword "body function" (the function that contains the body of the method
-- as written, called after all missing keyword-arguments have been assigned default values).
-- `basemethod` is the method you obtain via [`which`](@ref) or [`methods`](@ref).
-- 
-- The binding of the body function is looked up in the world age given by `world`, which
-- defaults to the current world counter.
-- 
-- !!! compat "Julia 1.14"
--     The `world` keyword argument requires Julia 1.14 or later. Before Julia 1.14,
--     the binding was looked up in the world age of the calling task.
-- """
-- /Source

-- Source: base/reflection.jl:1194-1228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.isambiguous(m1, m2; ambiguous_bottom=false)::Bool
-- 
-- Determine whether two methods `m1` and `m2` may be ambiguous for some call
-- signature. This test is performed in the context of other methods of the same
-- function; in isolation, `m1` and `m2` might be ambiguous, but if a third method
-- resolving the ambiguity has been defined, this returns `false`.
-- Alternatively, in isolation `m1` and `m2` might be ordered, but if a third
-- method cannot be sorted with them, they may cause an ambiguity together.
-- 
-- For parametric types, the `ambiguous_bottom` keyword argument controls whether
-- `Union{}` counts as an ambiguous intersection of type parameters – when `true`,
-- it is considered ambiguous, when `false` it is not.
-- 
-- # Examples
-- ```jldoctest
-- julia> foo(x::Complex{<:Integer}) = 1
-- foo (generic function with 1 method)
-- 
-- julia> foo(x::Complex{<:Rational}) = 2
-- foo (generic function with 2 methods)
-- 
-- julia> m1, m2 = collect(methods(foo));
-- 
-- julia> typeintersect(m1.sig, m2.sig)
-- Tuple{typeof(foo), Complex{Union{}}}
-- 
-- julia> Base.isambiguous(m1, m2, ambiguous_bottom=true)
-- true
-- 
-- julia> Base.isambiguous(m1, m2, ambiguous_bottom=false)
-- false
-- ```
-- """
-- /Source

-- Source: base/reflection.jl:1298-1344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @invoke f(arg::T, ...; kwargs...)
-- 
-- Provides a convenient way to call [`invoke`](@ref) by expanding
-- `@invoke f(arg1::T1, arg2::T2; kwargs...)` to `invoke(f, Tuple{T1,T2}, arg1, arg2; kwargs...)`.
-- When an argument's type annotation is omitted, it's replaced with `Core.Typeof` that argument.
-- To invoke a method where an argument is untyped or explicitly typed as `Any`, annotate the
-- argument with `::Any`.
-- 
-- It also supports the following syntax:
-- - `@invoke (x::X).f` expands to `invoke(getproperty, Tuple{X,Symbol}, x, :f)`
-- - `@invoke (x::X).f = v::V` expands to `invoke(setproperty!, Tuple{X,Symbol,V}, x, :f, v)`
-- - `@invoke (xs::Xs)[i::I]` expands to `invoke(getindex, Tuple{Xs,I}, xs, i)`
-- - `@invoke (xs::Xs)[i::I] = v::V` expands to `invoke(setindex!, Tuple{Xs,V,I}, xs, v, i)`
-- 
-- # Examples
-- 
-- ```jldoctest
-- julia> @macroexpand @invoke f(x::T, y)
-- :(Core.invoke(f, Base.Tuple{T, Core.Typeof(y)}, x, y))
-- 
-- julia> @invoke 420::Integer % Unsigned
-- 0x00000000000001a4
-- 
-- julia> @macroexpand @invoke (x::X).f
-- :(Core.invoke(Base.getproperty, Base.Tuple{X, Core.Typeof(:f)}, x, :f))
-- 
-- julia> @macroexpand @invoke (x::X).f = v::V
-- :(Core.invoke(Base.setproperty!, Base.Tuple{X, Core.Typeof(:f), V}, x, :f, v))
-- 
-- julia> @macroexpand @invoke (xs::Xs)[i::I]
-- :(Core.invoke(Base.getindex, Base.Tuple{Xs, I}, xs, i))
-- 
-- julia> @macroexpand @invoke (xs::Xs)[i::I] = v::V
-- :(Core.invoke(Base.setindex!, Base.Tuple{Xs, V, I}, xs, v, i))
-- ```
-- 
-- !!! compat "Julia 1.7"
--     This macro requires Julia 1.7 or later.
-- 
-- !!! compat "Julia 1.9"
--     This macro is exported as of Julia 1.9.
-- 
-- !!! compat "Julia 1.10"
--     The additional syntax is supported as of Julia 1.10.
-- """
-- /Source

-- Source: base/reflection.jl:1364-1364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:1366-1366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/reflection.jl:1377-1405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @invokelatest f(args...; kwargs...)
-- 
-- Provides a convenient way to call [`invokelatest`](@ref).
-- `@invokelatest f(args...; kwargs...)` will simply be expanded into
-- `Base.invokelatest(f, args...; kwargs...)`.
-- 
-- It also supports the following syntax:
-- - `@invokelatest x.f` expands to `Base.invokelatest(getproperty, x, :f)`
-- - `@invokelatest x.f = v` expands to `Base.invokelatest(setproperty!, x, :f, v)`
-- - `@invokelatest xs[i]` expands to `Base.invokelatest(getindex, xs, i)`
-- - `@invokelatest xs[i] = v` expands to `Base.invokelatest(setindex!, xs, v, i)`
-- 
-- !!! note
--     If `f` is a global, it will be resolved consistently
--     in the (latest) world as the call target. However, all other arguments
--     (as well as `f` itself if it is not a literal global) will be evaluated
--     in the current world age.
-- 
-- !!! compat "Julia 1.7"
--     This macro requires Julia 1.7 or later.
-- 
-- !!! compat "Julia 1.9"
--     Prior to Julia 1.9, this macro was not exported, and was called as `Base.@invokelatest`.
-- 
-- !!! compat "Julia 1.10"
--     The additional `x.f` and `xs[i]` syntax requires Julia 1.10.
-- """
-- /Source

-- Source: base/reflection.jl:1498-1505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.drop_all_caches()
-- 
-- Internal function to drop all native code caches and increment world age.
-- This invalidates all compiled code as if a method was added that intersects
-- with all existing methods.
-- """
-- /Source


end JuliaLean.base.reflection

namespace JuliaLean.ExprReflect

open JuliaLean

/-- `which`, abstracting the runtime's unique most-specific match; `base/reflection.jl:968-1013`. -/
def whichMethod (table : List MethodInfo) (modules : Option (List String)) : Option MethodInfo :=
  (methods table modules).head?

/-- `hasmethod`; `base/reflection.jl:1077-1139`. -/
def hasMethod (table : List MethodInfo) (modules : Option (List String)) : Bool :=
  !(methods table modules).isEmpty

/-- `nameof(f::Function)`; `base/reflection.jl:1029-1043`. -/
def nameOf (functionName : String) : String := functionName

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

structure LoweredCandidate where
  generated : Bool
  mayInvokeGenerator : Bool
  fallback : String
  staged : String
  deriving Repr, DecidableEq, Inhabited

def loweredCandidate (useGenerated : Bool) (candidate : LoweredCandidate) : Jl String :=
  if useGenerated && candidate.generated then
    if candidate.mayInvokeGenerator then .ok candidate.staged
    else .error (.argumentError "could not expand generator")
  else .ok candidate.fallback

def codeLoweredModel (useGenerated : Bool) (candidates : List LoweredCandidate) : Jl (List String) :=
  candidates.mapM (loweredCandidate useGenerated)

def normalizeDebugInfo (irShowDefined : Bool) (debugInfo : String) : Jl String :=
  let normalized := if !irShowDefined && debugInfo == "default" then "source" else debugInfo
  if normalized == "source" || normalized == "none" then .ok normalized
  else .error (.argumentError "debuginfo must be source or none")

def reflectionWorldAllowed (pureContext : Bool) (worldIsMax : Bool) : Bool :=
  !pureContext && !worldIsMax

def methodInstancesModel (candidates : List String) : List String :=
  candidates.map ("specialize:" ++ ·)

def boolCint (value : Bool) : Int := if value then 1 else 0

structure CodegenFlags where
  trackAllocations : Bool
  codeCoverage : Bool
  preferSpecsig : Bool
  emitMetadata : Bool
  deriving Repr, Inhabited

def codegenParamsModel (flags : CodegenFlags) : List Int := [
  boolCint flags.trackAllocations, boolCint flags.codeCoverage,
  boolCint flags.preferSpecsig, boolCint flags.emitMetadata]

def emissionParamsModel (emitMetadata : Bool) : Int := boolCint emitMetadata

inductive CompilerRoute where | typeinfWorld | reflectionModule | interpreterModule | methodTableModule
  deriving Repr, DecidableEq, Inhabited

def compilerRoute (reflectionCompiler interp methodTable : Bool) : CompilerRoute :=
  if interp then .interpreterModule
  else if methodTable then .methodTableModule
  else if reflectionCompiler then .reflectionModule
  else .typeinfWorld

inductive FunctionClass where | ordinary | opaque | builtin
  deriving Repr, DecidableEq, Inhabited

def codeQueryRows (inferred : List (Option String)) : List String :=
  inferred.map fun result => result.getD "Method=>Any"

def irCodeQueryRows (inferred : List (Option (String × String))) : List String :=
  inferred.map fun result => match result with
    | none => "Method=>Any"
    | some (code, ty) => code ++ "=>" ++ ty

def returnTypeRows (functionClass : FunctionClass) (inferred : List (Option String)) : List String :=
  match functionClass with
  | .opaque => [inferred.head?.join.getD "Any"]
  | .builtin => [inferred.head?.join.getD "Any"]
  | .ordinary => inferred.map (·.getD "Any")

def exceptionTypeRows (functionClass : FunctionClass) (inferred : List (Option String)) : List String :=
  match functionClass with
  | .opaque => ["Any"]
  | .builtin => [inferred.head?.join.getD "Any"]
  | .ordinary => inferred.map (·.getD "Any")

def inferCollectiveType (functionClass : FunctionClass) (types : List String) : String :=
  match functionClass with
  | .opaque | .builtin => types.head?.getD "Any"
  | .ordinary => String.intercalate " ∪ " types

def checkGeneratedContext (pureContext worldIsMax : Bool) : Jl Unit :=
  if pureContext || worldIsMax then .error (.argumentError "reflection from generated function")
  else .ok ()

structure KeywordMethod where
  positionalMatch : Bool
  acceptedKeywords : List String
  forwardsKeywords : Bool
  deriving Repr, DecidableEq, Inhabited

def hasKeywordMethod (method : KeywordMethod) (requested : List String) : Bool :=
  method.positionalMatch &&
    (requested.isEmpty || method.forwardsKeywords || requested.all method.acceptedKeywords.contains)

def parentModuleModel (methods : List String) : Jl String :=
  match methods with
  | [] => .error (.argumentError "no matching methods")
  | moduleName :: _ => .ok moduleName

inductive BodyFunctionHead where
  | symbol (moduleName name : String)
  | globalRef (moduleName name : String)
  | apply (next : BodyFunctionHead)
  | applyIterate (next : BodyFunctionHead)
  | ssa (resolved : Option BodyFunctionHead)
  | other
  deriving Repr, Inhabited

def bodyFunctionModel : BodyFunctionHead → Option (String × String)
  | .symbol moduleName name | .globalRef moduleName name => some (moduleName, name)
  | .apply next | .applyIterate next => bodyFunctionModel next
  | .ssa (some next) => bodyFunctionModel next
  | .ssa none | .other => none

structure AmbiguityFacts where
  sameMethod : Bool
  bottomIntersection : Bool
  hasBottomParameter : Bool
  generatorWorld : Bool
  runtimeAmbiguity : Bool
  involvesBoth : Bool
  reverseIntersectionWorks : Bool
  deriving Repr, DecidableEq, Inhabited

def isAmbiguousModel (facts : AmbiguityFacts) (ambiguousBottom : Bool) : Bool :=
  if facts.sameMethod || facts.bottomIntersection then false
  else if !ambiguousBottom && facts.hasBottomParameter then false
  else if facts.generatorWorld then true
  else facts.runtimeAmbiguity && facts.involvesBoth && facts.reverseIntersectionWorks

inductive CallForm where | call | getproperty | getindex | setproperty | setindex | invalid
  deriving Repr, DecidableEq, Inhabited

def callTarget : CallForm → Jl String
  | .call => .ok "call-target"
  | .getproperty => .ok "getproperty"
  | .getindex => .ok "getindex"
  | .setproperty => .ok "setproperty!"
  | .setindex => .ok "setindex!"
  | .invalid => .error (.argumentError "expected call expression")

def invokeTypeSource (annotated : Bool) : String :=
  if annotated then "annotation" else "Core.Typeof"

def invokeLatestRoute (literalGlobal hasKeywords : Bool) : String :=
  if literalGlobal then
    if hasKeywords then "invokelatest_gr:kwcall" else "invokelatest_gr:invoke_in_world"
  else "invokelatest"

def flattenTupleArgs (arguments : List (List String)) : List String := arguments.flatten

structure CacheState where
  requireWorldIsMax : Bool
  compilerActive : Bool
  deriving Repr, DecidableEq, Inhabited

def dropCachesModel (_ : CacheState) : CacheState := ⟨true, true⟩

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

structure ReflectionMethod where
  name : String
  generated : Bool
  mayInvokeGenerator : Bool
  fallbackCode : String
  generatedCode : String
  moduleName : String
  deriving Repr, DecidableEq, Inhabited

def normalizeReflectionDebug (irShowDefined : Bool) (requested : String) : Jl String :=
  let normalized := if !irShowDefined && requested == "default" then "source" else requested
  if normalized == "source" || normalized == "none" then .ok normalized
  else .error (.argumentError "debuginfo must be source or none")

def lowerOne (generated : Bool) (method : ReflectionMethod) : Jl String :=
  if generated && method.generated then
    if method.mayInvokeGenerator then .ok method.generatedCode
    else .error (.argumentError "could not expand generator")
  else .ok method.fallbackCode

/-- `code_lowered(argtypes; generated, debuginfo)`; `base/reflection.jl:19-47`. -/

def reflectionRow19 (methods : List ReflectionMethod) (generated irShowDefined worldIsMax : Bool)
    (debugInfo : String) : Jl (List String) :=
  match normalizeReflectionDebug irShowDefined debugInfo with
  | .error error => .error error
  | .ok normalized =>
    if worldIsMax then .error (.argumentError "reflection from generated function")
    else methods.mapM fun method => do
      let code ← lowerOne generated method
      return if normalized == "none" && !(generated && method.generated) then "remove_linenums:" ++ code else code

def reflectionRow49 (signatureType : String → String → String) (function types : String)
    (query : String → Jl (List String)) : Jl (List String) :=
  query (signatureType function types)

def reflectionRow58 (worldIsMax : Bool) (candidates : List ReflectionMethod) : Jl (List String) :=
  if worldIsMax then .error (.argumentError "reflection from generated function")
  else .ok (candidates.map ("specialize:" ++ ·.name))

def reflectionRow70 (signatureType : String → String → String) (function types : String)
    (lookup : String → Jl (List String)) := lookup (signatureType function types)

def reflectionRow75 (tupleType : String) (_world : Nat) (methodTable : List (String × String)) : Option String :=
  (methodTable.find? (·.1 == tupleType)).map (·.2)

def reflectionRow84 (signatureType : String → String → String) (function types : String)
    (lookup : String → Option String) : Option String := lookup (signatureType function types)

def reflectionRow90 (runtimeGlobal : Int) : Int := runtimeGlobal

structure FullCodegenFlags where
  trackAllocations : Bool
  codeCoverage : Bool
  preferSpecsig : Bool
  gnuPubnames : Bool
  debugInfoKind : Int
  debugInfoLevel : Int
  safepointOnEntry : Bool
  gcstackArg : Bool
  useJlplt : Bool
  forceEmitAll : Bool
  sanitizeMemory : Bool
  sanitizeThread : Bool
  sanitizeAddress : Bool
  uniqueNames : Bool
  debugInfoInlineScopes : Bool
  deriving Repr, DecidableEq, Inhabited

def boolToCint (value : Bool) : Int := if value then 1 else 0

/-- `CodegenParams` keyword constructor; `base/reflection.jl:201-217`. -/

def reflectionRow201 (flags : FullCodegenFlags) : List Int := [
  boolToCint flags.trackAllocations, boolToCint flags.codeCoverage,
  boolToCint flags.preferSpecsig, boolToCint flags.gnuPubnames,
  flags.debugInfoKind, flags.debugInfoLevel, boolToCint flags.safepointOnEntry,
  boolToCint flags.gcstackArg, boolToCint flags.useJlplt, boolToCint flags.forceEmitAll,
  boolToCint flags.sanitizeMemory, boolToCint flags.sanitizeThread,
  boolToCint flags.sanitizeAddress, boolToCint flags.uniqueNames,
  boolToCint flags.debugInfoInlineScopes]

def reflectionRow224 (emitMetadata : Bool) : Int := boolToCint emitMetadata

inductive ReflectedFunction where | ordinary (name : String) | opaque (name : String) | builtin (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- Object-form `code_typed`; `base/reflection.jl:288-294`. -/

def reflectionRow288 (function : ReflectedFunction) (types : String)
    (opaqueQuery regularQuery : String → String → List String) : List String :=
  match function with
  | .opaque name => opaqueQuery name types
  | .ordinary name | .builtin name => regularQuery name types

def reflectionRow299 (toTupleType query : String → String) (arguments : String) : String :=
  query (toTupleType arguments)

def reflectionRow307 (methodSignatures : List String) : String :=
  match methodSignatures with | [only] => "tail:" ++ only | _ => "Tuple"

def reflectionRow316 (name signature : String) : Jl Unit :=
  .error (.argumentError (name ++ ": unanalyzable call given " ++ signature))

def reflectionRow324 (typeinfCall : List String → String) (arguments : List String) : String := typeinfCall arguments

def reflectionRow329 (customCompiler : Option (String → List String → String))
    (typeinfCompiler : String → List String → String) (name : String) (arguments : List String) : String :=
  match customCompiler with | none => typeinfCompiler name arguments | some compiler => compiler name arguments

structure CompilerType where
  ancestry : List (String × String)
  deriving Repr, DecidableEq, Inhabited

def findCompilerModule (target : String) (type : CompilerType) : Jl String :=
  match type.ancestry.find? (fun pair => pair.1 == target || pair.1 == "Any") with
  | some (name,moduleName) => if name == target then .ok moduleName else .error (.argumentError ("Expected " ++ target))
  | none => .error (.argumentError ("Expected " ++ target))

/-- `invoke_interp_compiler`; `base/reflection.jl:337-350`. -/

def reflectionRow337 (interpreter : Option CompilerType) (defaultCall : String)
    (moduleCall : String → String) : Jl String :=
  match interpreter with
  | none => .ok defaultCall
  | some type => return moduleCall (← findCompilerModule "AbstractInterpreter" type)

def reflectionRow352 (methodTable : Option CompilerType) (defaultCall : String)
    (moduleCall : String → String) : Jl String :=
  match methodTable with
  | none => .ok defaultCall
  | some type => return moduleCall (← findCompilerModule "MethodTableView" type)

structure InferenceMatch where
  methodName : String
  inferred : Option String
  returnType : String
  deriving Repr, DecidableEq, Inhabited

def shapeInferenceRows (candidates : List InferenceMatch) : List String :=
  candidates.map fun candidate => candidate.inferred.getD (candidate.methodName ++ "=>Any")

/-- `code_typed_by_type`; `base/reflection.jl:373-405`. -/

def reflectionRow373 (pure worldMax : Bool) (debugInfo : Jl String)
    (candidates : Option (List InferenceMatch)) : Jl (List String) :=
  if pure || worldMax then .error (.argumentError "reflection from generated function")
  else match debugInfo with
    | .error error => .error error
    | .ok _ => match candidates with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (shapeInferenceRows values)

inductive OpaqueSource where | methodSource (hasSource : Bool) (optimized : Bool) | optimizedIR | invalid
  deriving Repr, DecidableEq, Inhabited

/-- `get_oc_code_rt`; `base/reflection.jl:407-436`. -/

def reflectionRow407 (pure optimize : Bool) (source : OpaqueSource) : Jl String :=
  if pure then .error (.argumentError "reflection from generated function")
  else match source with
    | .methodSource true true => if optimize then .ok "typeinf_code=>rettype" else .ok "uncompressed_ir=>declaredtype"
    | .methodSource true false => .ok "uncompressed_ir=>declaredtype"
    | .methodSource false _ | .optimizedIR => .ok "cached_inferred=>rettype"
    | .invalid => .error (.argumentError "invalid OpaqueClosure")

def reflectionRow438 (result : Jl String) (debugNone : Bool) : Jl (List String) :=
  match result with | .error error => .error error | .ok code => .ok [if debugNone then "remove_linenums:" ++ code else code]

def reflectionRow492 (function : ReflectedFunction) (regularQuery : String → String) : Jl String :=
  match function with | .opaque _ => .error (.argumentError "OpaqueClosure not supported") | .ordinary name | .builtin name => .ok (regularQuery name)

def reflectionRow500 (toTuple query : String → String) (arguments : String) : String := query (toTuple arguments)

def reflectionRow511 (pure worldMax : Bool) (candidates : Option (List InferenceMatch)) : Jl (List String) :=
  if pure || worldMax then .error (.argumentError "reflection from generated function")
  else match candidates with | none => .error (.argumentError "unanalyzable call") | some values => .ok (shapeInferenceRows values)

def reflectionRow537 (builtinType widen : String → String) (arguments : String) : String := widen (builtinType arguments)

def reflectionRow544 (typeFunction lattice effects : String → String) (arguments : String) : String :=
  effects (lattice (typeFunction arguments))

def reflectionRow553 (isNothrow : Bool) : String := if isNothrow then "Union{}" else "Any"

def reflectionRow559 (pure worldMax : Bool) : Jl Unit :=
  if pure || worldMax then .error (.argumentError "reflection from generated function") else .ok ()

def reflectionRow610 (generatedContext : Bool) (functionClass : ReflectedFunction)
    (candidates : Option (List (Option String))) : Jl (List String) :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .opaque _ => .ok [((candidates.bind fun values => values.head?).join).getD "Any"]
    | .builtin _ => .ok [((candidates.bind fun values => values.head?).join).getD "Any"]
    | .ordinary _ => match candidates with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (values.map (·.getD "Any"))

def reflectionRow680 (generatedContext : Bool) (functionClass : ReflectedFunction)
    (types : Option (List String)) : Jl String :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .opaque _ | .builtin _ => .ok ((types.bind fun values => values.head?).getD "Any")
    | .ordinary _ => match types with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (String.intercalate "∪" values)

def reflectionRow752 (generatedContext : Bool) (functionClass : ReflectedFunction)
    (frames : Option (List (Option String))) : Jl (List String) :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .opaque _ => .ok ["Any"]
    | .builtin _ => .ok [((frames.bind fun values => values.head?).join).getD "Any"]
    | .ordinary _ => match frames with
      | none => .error (.argumentError "unanalyzable call")
      | some values => .ok (values.map (·.getD "Any"))

def reflectionRow830 (generatedContext : Bool) (functionClass : ReflectedFunction) (inferred : Option String) : Jl String :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .opaque _ => .ok "Any"
    | .builtin _ => .ok (inferred.getD "Any")
    | .ordinary _ => match inferred with
      | some value => .ok value
      | none => .error (.argumentError "unanalyzable call")

def reflectionRow908 (generatedContext : Bool) (functionClass : ReflectedFunction) (inferred : Option String) : Jl String :=
  if generatedContext then .error (.argumentError "reflection from generated function")
  else match functionClass with
    | .builtin _ => .ok (inferred.getD "unknown-effects")
    | _ => match inferred with
      | some value => .ok value
      | none => .error (.argumentError "unanalyzable call")

def reflectionRow930 (signatureType : String → String → String) (function types : String)
    (printer : String → String) : String := printer (signatureType function types)

def reflectionRow935 (candidates : List (String × Option (List Nat))) : List String :=
  candidates.map fun candidate => candidate.1 ++ match candidate.2 with
    | none => ": inference not successful" | some costs => ":" ++ toString costs

def reflectionRow966 (printer : String → String) (argument : String) : String := printer argument

structure ReflectedMethod where
  name : String
  moduleName : String
  keywordNames : List String
  forwardsKeywords : Bool
  deriving Repr, DecidableEq, Inhabited

inductive LookupCandidate where
  | missing
  | methodMatch (method : ReflectedMethod)
  | other

inductive LookupResult where
  | generatedFunctionError
  | noMatchError
  | typeError
  | none
  | matchFound (method : ReflectedMethod)
  deriving DecidableEq

/-- `_which`; the compiler result may be `nothing`, a MethodMatch, or an
incorrectly typed value rejected by the assertion at `base/reflection.jl:978`. -/

def reflectionRow968 (worldMax raiseError : Bool) (candidate : LookupCandidate) : LookupResult :=
  if worldMax then .generatedFunctionError
  else match candidate with
    | .missing => if raiseError then .noMatchError else .none
    | .methodMatch method => .matchFound method
    | .other => .typeError

def reflectionRow990 (candidate : Option ReflectedMethod) : Jl ReflectedMethod :=
  match candidate with | some method => .ok method | none => .error (.argumentError "invoke would throw")

def reflectionRow1010 (lookup : Jl (Option ReflectedMethod)) : Jl ReflectedMethod :=
  match lookup with
  | .error error => .error error
  | .ok (some method) => .ok method
  | .ok none => .error (.argumentError "no unique match")

def reflectionRow1013 (toTuple query : String → String) (arguments : String) : String := query (toTuple arguments)

def reflectionRow1020 (globalDefined : Bool) (moduleText symbolText bindingModule : String) :
    Except String String :=
  if globalDefined then .ok bindingModule
  else .error ("\"" ++ symbolText ++ "\" is not defined in module " ++ moduleText)

def reflectionRow1036 (singletonName : String) : String := singletonName

def reflectionRow1040 (intrinsicNames : List String) (index : Nat) : Option String := intrinsicNames[index]?

def reflectionRow1051 (typeModule : String) : String := typeModule

def reflectionRow1059 (methods : List ReflectedMethod) : Jl String :=
  match methods with | [] => .error (.argumentError "no matching methods") | method :: _ => .ok method.moduleName

def reflectionRow1075 (method : ReflectedMethod) : String := method.moduleName

def reflectionRow1113 (hasMatch : Bool) : Bool := hasMatch

def reflectionRow1117 (worldLookup : Nat → Bool) (world : Nat) : Bool := worldLookup world

def reflectionRow1122 (worldMax positionalMatch : Bool) (requested : List String)
    (method : Option ReflectedMethod) : Jl Bool :=
  if worldMax then .error (.argumentError "reflection from generated function")
  else if requested.isEmpty then .ok positionalMatch
  else match method with
    | none => .ok false
    | some method =>
      .ok (method.keywordNames.isEmpty || method.forwardsKeywords || requested.all method.keywordNames.contains)

inductive BodyFunctionRef where
  | symbol (moduleName name : String) | global (moduleName name : String)
  | apply (next : BodyFunctionRef) | applyIterate (next : BodyFunctionRef)
  | ssa (next : Option BodyFunctionRef) | invalid
  deriving Repr, Inhabited

/-- `bodyfunction`; `base/reflection.jl:1155-1193`. -/

def reflectionRow1155 : Nat → BodyFunctionRef → Option (String × String)
  | 0, _ => none
  | _, .symbol moduleName name | _, .global moduleName name => some (moduleName,name)
  | fuel+1, .apply next | fuel+1, .applyIterate next => reflectionRow1155 fuel next
  | fuel+1, .ssa (some next) => reflectionRow1155 fuel next
  | _, _ => none

structure AmbiguityInput where
  sameMethod : Bool
  bottomIntersection : Bool
  bottomParameter : Bool
  generatorWorld : Bool
  runtimeAmbiguity : Bool
  involvesFirst : Bool
  involvesSecond : Bool
  filteredMatches : Bool
  resortAmbiguous : Bool
  reverseIntersectionWorks : Bool
  deriving Repr, DecidableEq, Inhabited

def ambiguityInvolvesBoth (input : AmbiguityInput) : Bool := input.involvesFirst && input.involvesSecond

def ambiguityInner (input : AmbiguityInput) (ambiguousBottom : Bool) : Bool :=
  if input.bottomIntersection then false
  else if !ambiguousBottom && input.bottomParameter then false
  else if input.generatorWorld then true
  else if !input.runtimeAmbiguity then false
  else if !ambiguityInvolvesBoth input then false
  else if input.filteredMatches then input.resortAmbiguous && ambiguityInvolvesBoth input
  else true

/-- `isambiguous`; `base/reflection.jl:1229-1297`. -/

def reflectionRow1229 (input : AmbiguityInput) (ambiguousBottom : Bool) : Bool :=
  if input.sameMethod then false else if input.reverseIntersectionWorks then ambiguityInner input ambiguousBottom else false

def reflectionRow1233 (input : AmbiguityInput) (flag : Bool) : Bool := ambiguityInner input flag

def reflectionRow1249 (input : AmbiguityInput) : Bool := ambiguityInvolvesBoth input

inductive InvokeArgument where | annotated (value typeName : String) | plain (value : String)
  deriving Repr, DecidableEq, Inhabited

def invokeValue : InvokeArgument → String | .annotated value _ | .plain value => value

def invokeType : InvokeArgument → String | .annotated _ typeName => typeName | .plain value => "Core.Typeof(" ++ value ++ ")"

/-- `@invoke`; `base/reflection.jl:1345-1363`. -/

def reflectionRow1345 (function : String) (arguments : List InvokeArgument) (keywords : List String) : List String :=
  keywords ++ ["Core.invoke", function, "Tuple{" ++ String.intercalate "," (arguments.map invokeType) ++ "}"] ++ arguments.map invokeValue

def reflectionRow1365 (globals : List ((String × String) × String)) (moduleName name : String) : Option String :=
  (globals.find? (·.1 == (moduleName,name))).map (·.2)

def reflectionRow1367 (keywords : List String) : String := if keywords.isEmpty then "invoke_in_world" else "invoke_in_world:kwcall"

inductive LatestTarget where | literalGlobal | symbolGlobal | dottedGlobal | expression
  deriving Repr, DecidableEq, Inhabited

/-- `@invokelatest`; `base/reflection.jl:1406-1448`. -/

def reflectionRow1406 (target : LatestTarget) (isGlobal : Bool) : String :=
  match target with | .literalGlobal => "invokelatest_gr" | .dottedGlobal | .symbolGlobal => if isGlobal then "invokelatest_gr" else "invokelatest" | .expression => "invokelatest"

inductive CallExpression where
  | call (function : String) (arguments keywords : List String)
  | property (object field : String)
  | index (object : String) (indices : List String)
  | setProperty (object field value : String)
  | setIndex (object value : String) (indices : List String)
  | invalid
  deriving Repr, DecidableEq, Inhabited

def flattenArguments (values : List (List String)) : List String := values.flatten

/-- `destructure_callex`; `base/reflection.jl:1450-1497`. -/

def reflectionRow1450 : CallExpression → Jl (String × List String × List String)
  | .call function arguments keywords => .ok (function,arguments,keywords)
  | .property object field => .ok ("getproperty",[object,field],[])
  | .index object indices => .ok ("getindex",object::indices,[])
  | .setProperty object field value => .ok ("setproperty!",[object,field,value],[])
  | .setIndex object value indices => .ok ("setindex!",object::value::indices,[])
  | .invalid => .error (.argumentError "expected call expression")

def reflectionRow1451 (values : List (List String)) : List String := flattenArguments values

structure ReflectionCacheState where
  runtimeDropped : Bool
  requireWorldIsMax : Bool
  compilerActive : Bool
  deriving Repr, DecidableEq, Inhabited

/-- `drop_all_caches`; `base/reflection.jl:1506-1514`. -/

def reflectionRow1506 (_ : ReflectionCacheState) : ReflectionCacheState := ⟨true,true,true⟩

end JuliaLean.ExprReflect
