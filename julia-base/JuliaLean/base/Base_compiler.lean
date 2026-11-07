import JuliaLean.base.runtime_internals
import JuliaLean.Core

namespace JuliaLean.base.Base_compiler
open JuliaLean

inductive Error where
  | jl (error : JlError)
  | errorException (message : String)
  | other (typeName message : String)

abbrev Result := Except Error

section
variable {m : Type → Type} [Monad m]
variable {Object Module Symbol Value Ty Operator Result : Type}

/-- Runtime field and global operations. Conversion dispatch is selected by the declared type. -/
structure PropertyOps (m : Type → Type) (Object Module Symbol Value Ty : Type) where
  typeof : Object → Ty
  fieldtype : Ty → Symbol → m Ty
  bindingType : Module → Symbol → m Ty
  isa : Value → Ty → Bool
  convert : (ty : Ty) → Value → m { value : Value // isa value ty = true }
  setfield : Object → Symbol → Value → Symbol → m Value
  setglobal : Module → Symbol → Value → Symbol → m Value
  swapfield : Object → Symbol → Value → Symbol → m Value
  swapglobal : Module → Symbol → Value → Symbol → m Value

-- Source: base/Base_compiler.jl:71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getproperty(x::Module, f::Symbol, order::Symbol) = (@inline; getglobal(x, f, order))
def getpropertyModuleOrder (getglobal : Module → Symbol → Symbol → m Value)
    (x : Module) (f order : Symbol) : m Value := getglobal x f order

-- Source: base/Base_compiler.jl:78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getproperty(x::Type, f::Symbol, order::Symbol) = (@inline; getfield(x, f, order))
def getpropertyTypeOrder (getfield : Object → Symbol → Symbol → m Value)
    (x : Object) (f order : Symbol) : m Value := getfield x f order

-- Source: base/Base_compiler.jl:80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getproperty(x::Tuple, f::Int, order::Symbol) = (@inline; getfield(x, f, order))
def getpropertyTupleOrder (getfield : Object → JInt .i64 → Symbol → m Value)
    (x : Object) (f : JInt .i64) (order : Symbol) : m Value := getfield x f order

-- Source: base/Base_compiler.jl:83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getproperty(x, f::Symbol, order::Symbol) = (@inline; getfield(x, f, order))
def getpropertyOrder (getfield : Object → Symbol → Symbol → m Value)
    (x : Object) (f order : Symbol) : m Value := getfield x f order

-- Source: base/Base_compiler.jl:72-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setproperty!(x::Module, f::Symbol, v, order::Symbol=:monotonic)
--     @inline
--     ty = Core.get_binding_type(x, f)
--     val = v isa ty ? v : convert(ty, v)
--     return setglobal!(x, f, val, order)
-- end
def setpropertyModuleOrder (r : PropertyOps m Object Module Symbol Value Ty)
    (x : Module) (f : Symbol) (v : Value) (order : Symbol) : m Value := do
  let ty ← r.bindingType x f
  let val ← if r.isa v ty then pure v else do pure (← r.convert ty v).val
  r.setglobal x f val order

-- Source: base/Base_compiler.jl:72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- order::Symbol=:monotonic
def setpropertyModule (r : PropertyOps m Object Module String Value Ty)
    (x : Module) (f : String) (v : Value) : m Value :=
  setpropertyModuleOrder r x f v "monotonic"

-- Source: base/Base_compiler.jl:79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- setproperty!(x::Type, f::Symbol, v, order::Symbol) = error("setfield! fields of Types should not be changed")
def setpropertyTypeOrder [MonadExceptOf Error m]
    (_x : Object) (_f : Symbol) (_v : Value) (_order : Symbol) : m Value :=
  throwThe Error (.errorException "setfield! fields of Types should not be changed")

-- Source: base/Base_compiler.jl:81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- setproperty!(x::Tuple, f::Int, v, order::Symbol) = setfield!(x, f, v, order)
def setpropertyTupleOrder (setfield : Object → JInt .i64 → Value → Symbol → m Value)
    (x : Object) (f : JInt .i64) (v : Value) (order : Symbol) : m Value :=
  setfield x f v order

-- Source: base/Base_compiler.jl:84-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setproperty!(x, f::Symbol, v, order::Symbol)
--     @inline
--     ty = fieldtype(typeof(x), f)
--     val = v isa ty ? v : convert(ty, v)
--     return setfield!(x, f, val, order)
-- end
def setpropertyOrder (r : PropertyOps m Object Module Symbol Value Ty)
    (x : Object) (f : Symbol) (v : Value) (order : Symbol) : m Value := do
  let ty ← r.fieldtype (r.typeof x) f
  let val ← if r.isa v ty then pure v else do pure (← r.convert ty v).val
  r.setfield x f val order

-- Source: base/Base_compiler.jl:91-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function swapproperty!(x, f::Symbol, v, order::Symbol=:not_atomic)
--     @inline
--     ty = fieldtype(typeof(x), f)
--     val = v isa ty ? v : convert(ty, v)
--     return Core.swapfield!(x, f, val, order)
-- end
def swappropertyOrder (r : PropertyOps m Object Module Symbol Value Ty)
    (x : Object) (f : Symbol) (v : Value) (order : Symbol) : m Value := do
  let ty ← r.fieldtype (r.typeof x) f
  let val ← if r.isa v ty then pure v else do pure (← r.convert ty v).val
  r.swapfield x f val order

-- Source: base/Base_compiler.jl:91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- order::Symbol=:not_atomic
def swapproperty (r : PropertyOps m Object Module String Value Ty)
    (x : Object) (f : String) (v : Value) : m Value :=
  swappropertyOrder r x f v "not_atomic"

-- Source: base/Base_compiler.jl:114-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function swapproperty!(x::Module, f::Symbol, v, order::Symbol=:not_atomic)
--     @inline
--     ty = Core.get_binding_type(x, f)
--     val = v isa ty ? v : convert(ty, v)
--     return Core.swapglobal!(x, f, val, order)
-- end
def swappropertyModuleOrder (r : PropertyOps m Object Module Symbol Value Ty)
    (x : Module) (f : Symbol) (v : Value) (order : Symbol) : m Value := do
  let ty ← r.bindingType x f
  let val ← if r.isa v ty then pure v else do pure (← r.convert ty v).val
  r.swapglobal x f val order

-- Source: base/Base_compiler.jl:114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- order::Symbol=:not_atomic
def swappropertyModule (r : PropertyOps m Object Module String Value Ty)
    (x : Module) (f : String) (v : Value) : m Value :=
  swappropertyModuleOrder r x f v "not_atomic"

-- Source: base/Base_compiler.jl:97-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function modifyproperty!(x, f::Symbol, op, v, order::Symbol=:not_atomic)
--     @inline
--     return Core.modifyfield!(x, f, op, v, order)
-- end
def modifypropertyOrder (modifyfield : Object → Symbol → Operator → Value → Symbol → m Result)
    (x : Object) (f : Symbol) (op : Operator) (v : Value) (order : Symbol) : m Result :=
  modifyfield x f op v order

-- Source: base/Base_compiler.jl:97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- order::Symbol=:not_atomic
def modifyproperty (modifyfield : Object → String → Operator → Value → String → m Result)
    (x : Object) (f : String) (op : Operator) (v : Value) : m Result :=
  modifypropertyOrder modifyfield x f op v "not_atomic"

-- Source: base/Base_compiler.jl:120-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function modifyproperty!(x::Module, f::Symbol, op, v, order::Symbol=:not_atomic)
--     @inline
--     return Core.modifyglobal!(x, f, op, v, order)
-- end
def modifypropertyModuleOrder (modifyglobal : Module → Symbol → Operator → Value → Symbol → m Result)
    (x : Module) (f : Symbol) (op : Operator) (v : Value) (order : Symbol) : m Result :=
  modifyglobal x f op v order

-- Source: base/Base_compiler.jl:120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- order::Symbol=:not_atomic
def modifypropertyModule (modifyglobal : Module → String → Operator → Value → String → m Result)
    (x : Module) (f : String) (op : Operator) (v : Value) : m Result :=
  modifypropertyModuleOrder modifyglobal x f op v "not_atomic"

end
end JuliaLean.base.Base_compiler

section
namespace JuliaLean.RuntimeCov.BaseCompiler

open JuliaLean.RuntimeCov

/-- `include(path::String)`, base/Base_compiler.jl:30, and
`(this::IncludeInto)(fname)`, line 36: both forward to `include(mod, path)`. -/
def includeBase {μ β : Type} (inc : μ → String → β) (base : μ) (path : String) : β := inc base path
structure IncludeInto (μ : Type) where
  m : μ
/-- `IncludeInto(m)`, base/Base_compiler.jl:34. -/
def mkIncludeInto {μ : Type} (m : μ) : IncludeInto μ := ⟨m⟩
def callIncludeInto {μ β : Type} (inc : μ → String → β) (self : IncludeInto μ) (fname : String) : β :=
  inc self.m fname

/-- The expressions produced by `@inline()`, `@noinline()`, `@_boundscheck()`,
base/Base_compiler.jl:44-47. -/
inductive MetaExpr where
  | metaHead (head : Sym)
  | boundscheck
  deriving DecidableEq, Repr
def atInline : MetaExpr := .metaHead "inline"
def atNoinline : MetaExpr := .metaHead "noinline"
def atBoundscheck : MetaExpr := .boundscheck

/-- A value as the property protocol sees it. -/
inductive Obj where
  | module (name : String)
  | type (name : String)
  | array
  | tuple
  | other (tyName : String)
  deriving DecidableEq, Repr

/-- The runtime operations used by the property fallbacks: field access, the
declared field type, `isa`, `convert`, the binding type of a global. -/
structure Rt' (V : Type) where
  getfield : Obj → Sym → Rt V
  getglobal : String → Sym → Rt V
  fieldtype : Obj → Sym → Rt String
  bindingType : String → Sym → String
  isa : V → String → Bool
  convert : String → V → Rt V
  setfield : Obj → Sym → V → Rt V
  setglobal : String → Sym → V → Rt V

/-- `getproperty(x, f)` for modules, types, tuples and the fallback,
base/Base_compiler.jl:52-59, 71-83 (the ordered forms pass `order` through). -/
def getproperty {V : Type} (r : Rt' V) (x : Obj) (f : Sym) : Rt V :=
  match x with
  | .module m => r.getglobal m f
  | _ => r.getfield x f

/-- Ordered module property access delegates to `getglobal` with its original
module, symbol, and memory order (`base/Base_compiler.jl:71`). -/
def orderedModuleGet {M V : Type} (getglobal : M → Sym → Sym → Rt V)
    (m : M) (field order : Sym) : Rt V := getglobal m field order

/-- Ordered type and fallback property access delegate to `getfield`
(`base/Base_compiler.jl:78,83`). -/
def orderedFieldGet {O V : Type} (getfield : O → Sym → Sym → Rt V)
    (x : O) (field order : Sym) : Rt V := getfield x field order

/-- Tuple property access uses an integer field index
(`base/Base_compiler.jl:80`). -/
def orderedTupleGet {T V : Type} (getfield : T → Int → Sym → Rt V)
    (tuple : T) (index : Int) (order : Sym) : Rt V := getfield tuple index order

/-- Ordered writes obtain the declared type, convert only if necessary, and
pass the converted value and order to the relevant runtime operation. -/
structure OrderedSetRuntime (V : Type) where
  fieldType : Obj → Sym → Rt String
  bindingType : String → Sym → Rt String
  isa : V → String → Bool
  convert : String → V → Rt V
  setfield : Obj → Sym → V → Sym → Rt V
  setglobal : String → Sym → V → Sym → Rt V

def orderedSetField {V : Type} (r : OrderedSetRuntime V) (x : Obj)
    (field : Sym) (value : V) (order : Sym) : Rt V := do
  let ty ← r.fieldType x field
  let converted ← if r.isa value ty then .ok value else r.convert ty value
  r.setfield x field converted order

def orderedSetModule {V : Type} (r : OrderedSetRuntime V) (m : String)
    (field : Sym) (value : V) (order : Sym) : Rt V := do
  let ty ← r.bindingType m field
  let converted ← if r.isa value ty then .ok value else r.convert ty value
  r.setglobal m field converted order

def orderedSetModuleDefault {V : Type} (r : OrderedSetRuntime V) (m : String)
    (field : Sym) (value : V) : Rt V :=
  orderedSetModule r m field value "monotonic"

/-- `swapproperty!` uses the same type lookup and conversion as a write,
then invokes the swap primitive and returns its old value
(`base/Base_compiler.jl:91-96,114-119`). -/
def swapFieldProperty {V : Type} (r : OrderedSetRuntime V)
    (swapfield : Obj → Sym → V → Sym → Rt V) (x : Obj)
    (field : Sym) (value : V) (order : Sym) : Rt V :=
  orderedSetField { r with setfield := swapfield } x field value order

def swapGlobalProperty {V : Type} (r : OrderedSetRuntime V)
    (swapglobal : String → Sym → V → Sym → Rt V) (m : String)
    (field : Sym) (value : V) (order : Sym) : Rt V :=
  orderedSetModule { r with setglobal := swapglobal } m field value order

def swapFieldPropertyDefault {V : Type} (r : OrderedSetRuntime V)
    (swapfield : Obj → Sym → V → Sym → Rt V) (x : Obj)
    (field : Sym) (value : V) : Rt V :=
  swapFieldProperty r swapfield x field value "not_atomic"

def swapGlobalPropertyDefault {V : Type} (r : OrderedSetRuntime V)
    (swapglobal : String → Sym → V → Sym → Rt V) (m : String)
    (field : Sym) (value : V) : Rt V :=
  swapGlobalProperty r swapglobal m field value "not_atomic"

def orderedSetType {V : Type} : Rt V :=
  .error (.errorException "setfield! fields of Types should not be changed")

def orderedSetTuple {T V : Type} (setfield : T → Int → V → Sym → Rt V)
    (tuple : T) (index : Int) (value : V) (order : Sym) : Rt V :=
  setfield tuple index value order

/-- `modifyproperty!` forwards the object, field, operator, value, and order
without conversion to the matching Core operation
(`base/Base_compiler.jl:97-100,120-123`). -/
def modifyFieldProperty {O V F R : Type}
    (modify : O → Sym → F → V → Sym → R) (object : O) (field : Sym)
    (op : F) (value : V) (order : Sym) : R :=
  modify object field op value order

def modifyGlobalProperty {O V F R : Type}
    (modify : O → Sym → F → V → Sym → R) (moduleObj : O) (field : Sym)
    (op : F) (value : V) (order : Sym) : R :=
  modify moduleObj field op value order

def modifyFieldPropertyDefault {O V F R : Type}
    (modify : O → Sym → F → V → Sym → R) (object : O) (field : Sym)
    (op : F) (value : V) : R :=
  modifyFieldProperty modify object field op value "not_atomic"

def modifyGlobalPropertyDefault {O V F R : Type}
    (modify : O → Sym → F → V → Sym → R) (object : O) (field : Sym)
    (op : F) (value : V) : R :=
  modifyGlobalProperty modify object field op value "not_atomic"

/-- Convert `v` to `ty` unless it already is one (`v isa ty ? v : convert(ty, v)`). -/
def convertTo {V : Type} (r : Rt' V) (ty : String) (v : V) : Rt V :=
  if r.isa v ty then .ok v else r.convert ty v

/-- `setproperty!(x, f, v[, order])`, base/Base_compiler.jl:54-64, 72-89. -/
def setproperty {V : Type} (r : Rt' V) (x : Obj) (f : Sym) (v : V) : Rt V :=
  match x with
  | .type _ => .error (.errorException "setfield! fields of Types should not be changed")
  | .array => .error (.errorException "setfield! fields of Array should not be changed")
  | .tuple => r.setfield x f v
  | .module m => do let val ← convertTo r (r.bindingType m f) v; r.setglobal m f val
  | .other _ => do let ty ← r.fieldtype x f; let val ← convertTo r ty v; r.setfield x f val

/-- `dotgetproperty(x, f)`, base/Base_compiler.jl:69. -/
def dotgetproperty {V : Type} (r : Rt' V) (x : Obj) (f : Sym) : Rt V := getproperty r x f

/-- The value stored by `swapproperty!`, `replaceproperty!` and
`setpropertyonce!`, base/Base_compiler.jl:91-135 (fields and module globals):
the new value converted to the field or binding type. `modifyproperty!`
(lines 97-100, 120-123) passes `op` and `v` through unconverted. -/
def storedValue {V : Type} (r : Rt' V) (x : Obj) (f : Sym) (v : V) : Rt V :=
  match x with
  | .module m => convertTo r (r.bindingType m f) v
  | _ => do let ty ← r.fieldtype x f; convertTo r ty v
def modifyArgs {V W : Type} (op : W) (v : V) : W × V := (op, v)

/-- `convert(::Type{Any}, x)` and `convert(::Type{T}, x::T)`, lines 137-138. -/
def convertIdentity {α : Type} (x : α) : α := x

/-- `_topmod(m)`, base/Base_compiler.jl:147: the runtime's base module for `m`. -/
def topmod {μ : Type} (rt : μ → μ) (m : μ) : μ := rt m

/-- The effects of `_setup_module!(mod, edition)`, base/Base_compiler.jl:148-163:
the constants declared and the syntax version set (none during bootstrap or
with the flisp parser). -/
def setupModule (edition : Option (Nat × Nat)) (bootstrapParser : Bool) (oldest : Nat × Nat) :
    List Sym × Option (Nat × Nat) :=
  let consts := ["include", "eval"]
  match edition with
  | some e => (consts, some e)
  | none => if bootstrapParser then (consts, none) else (consts, some oldest)

/-- `eval(x)` and `eval(m, x)`, base/Base_compiler.jl:169-170. -/
def evalIn {μ α β : Type} (coreEval : μ → α → β) (m : μ) (x : α) : β := coreEval m x

/-- `strcat(x, y)`, base/Base_compiler.jl:194-206, on the byte contents: a
fresh string of `sizeof(x) + sizeof(y)` bytes, `x`'s bytes then `y`'s. -/
def strcat (x y : List UInt8) : List UInt8 :=
  let out := List.replicate (x.length + y.length) (0 : UInt8)
  let out := x ++ out.drop x.length
  out.take x.length ++ y ++ (out.drop (x.length + y.length))

/-- `time_ns()`, base/Base_compiler.jl:219: the runtime clock. -/
def timeNs (hrtime : Nat) : Nat := hrtime % 2 ^ 64

/-- `Core.kwcall(kwargs, invoke, f, T, args...)`, base/Base_compiler.jl:235-240:
the signature passed on is `Tuple{typeof(kwargs), typeof(f), T.parameters...}`. -/
def kwcallInvokeSig (kwT fT : String) (params : List String) : List String := kwT :: fT :: params

/-- `Core.kwcall(kwargs, applicable, args...)`, lines 246-249: the argument
list given to `applicable`. -/
def kwcallApplicableArgs {α : Type} (kwcall kwargs : α) (args : List α) : List α := kwcall :: kwargs :: args

/-- `Core._hasmethod(f, t)`, lines 250-255: `Tuple{Typeof(f), t.parameters...}`. -/
def hasmethodSig (fT : String) (params : List String) : List String := fT :: params

/-- `Core.kwcall(kwargs, invokelatest, f, args...)`, lines 274-277, and the
`invoke_in_world` form, lines 308-311: the arguments forwarded. -/
def kwcallLatestArgs {α : Type} (kwcall kwargs f : α) (args : List α) : List α := kwcall :: kwargs :: f :: args
def kwcallWorldArgs {α : Type} (world : Nat) (kwcall kwargs f : α) (args : List α) : Nat × List α :=
  (world, kwcall :: kwargs :: f :: args)

/-- `(vp::VersionedParse)(code, filename, lineno, offset, options)`, lines
318-326: whether the edition is passed to the parser. -/
def versionedParsePassesEdition (hasV114Hooks hasV110Hooks : Bool) : Bool :=
  !(!hasV114Hooks && hasV110Hooks)

/-- `==(x, y) = x === y`, base/Base_compiler.jl:338. -/
def eqFallback {α : Type} [DecidableEq α] (x y : α) : Bool := decide (x = y)

/-- `process_sysimg_args!()`, base/Base_compiler.jl:395-410: options from
`Core.ARGS[2:end]` in pairs; `none` value means `ARGS[i+1]` is out of range. -/
inductive SysimgArg where
  | buildsettings (file : String)
  | buildroot (dir : String)
  | dataroot (dir : String)
  deriving DecidableEq, Repr

/-- The value of one flag, base/Base_compiler.jl:399-406. -/
def sysimgFlag (flag v : String) : Rt SysimgArg :=
  if flag = "--buildsettings" then .ok (.buildsettings v)
  else if flag = "--buildroot" then .ok (.buildroot v)
  else if flag = "--dataroot" then .ok (.dataroot v)
  else .error (.errorException ("invalid sysimage argument: " ++ flag))

def processSysimgArgs : List String → Rt (List SysimgArg)
  | [] => .ok []
  | flag :: rest =>
    match rest with
    | [] =>
      if flag = "--buildsettings" || flag = "--buildroot" || flag = "--dataroot" then .error .boundsError
      else .error (.errorException ("invalid sysimage argument: " ++ flag))
    | v :: rest' => do
      let a ← sysimgFlag flag v
      let as ← processSysimgArgs rest'
      pure (a :: as)
end JuliaLean.RuntimeCov.BaseCompiler
end
