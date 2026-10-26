import JuliaLean.BootCov.Basic

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
