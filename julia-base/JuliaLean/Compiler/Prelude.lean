import JuliaLean.src.subtype_c

/-!
Shared definitions for the models of `Compiler/src/*.jl`.

* `CEnv`: the type-name universe of the C type model (`JuliaLean.C.Types`) plus the few
  per-type facts that the lattice code reads and `Types` does not record.
* The Julia builtins that the lattice code calls on type objects (`<:`, `==`, `===`, `isa`,
  `typeintersect`, `issingletontype`, ...), as thin wrappers over `subtype_c.lean`.
* `LElt`, the lattice elements of the default inference lattice, and `Lattice`, the lattice
  layers of `Compiler/src/abstractlattice.jl`.

Julia exceptions are thrown as strings `"julia:<ExceptionType>: <message>"` in `CM`; every other
thrown string (an unknown type name, an exhausted recursion budget, `unmodelled:`) is a failure of
the model, never a Julia outcome.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-- The universe a lattice computation runs in. -/
structure CEnv where
  types : Types
  /-- `fieldcount(T)` for the concrete struct types whose values appear as `Const` payloads
  (immutable values whose trailing undefined fields are left out of `Val.imm`). -/
  nfields : List (Val × Nat) := []
  /-- Names of the type names with `tn.constfields != C_NULL`. -/
  constfields : List String := []
  /-- Names of the type names declared with `primitive type`. -/
  primitives : List String := []
  /-- `T.instance` of the singleton types (`issingletontype(T)`). -/
  instances : List (Val × Val) := []
  /-- For concrete struct types (not tuples): the field types and
  `datatype_min_ninitialized(T)`, which `typelimits.jl` reads. -/
  structs : List (Val × List Val × Nat) := []
  deriving Inhabited

/-- Throw the Julia exception `exc` (e.g. `MethodError`, `ErrorException`, `AssertionError`). -/
def jlThrow {α : Type} (exc : String) (msg : String := "") : CM α :=
  throw s!"julia:{exc}: {msg}"

/-- A branch that calls code outside the modelled files (e.g. `tfuncs.jl`). -/
def unmodelled {α : Type} (what : String) : CM α :=
  throw s!"unmodelled: {what}"

/-- `a <: b` (`jl_subtype`). -/
def issub (n : Nat) (E : CEnv) (a b : Val) : CM Bool := jlSubtype n E.types a b

/-- `a == b` on types (`jl_types_equal`). -/
def tyEq (n : Nat) (E : CEnv) (a b : Val) : CM Bool := jlTypesEqual n E.types a b

/-- `a === b` (`jl_egal`). -/
def egal (n : Nat) (E : CEnv) (a b : Val) : CM Bool := JuliaLean.C.egal n E.types a b

/-- `isa(x, t)` (`jl_isa`). -/
def isa (n : Nat) (E : CEnv) (x t : Val) : CM Bool := jlIsa n E.types x t

/-- `typeintersect(a, b)` (`base/runtime_internals.jl:1223`, `jl_type_intersection`). -/
def typeintersect (n : Nat) (E : CEnv) (a b : Val) : CM Val := do
  if !a.isType || !b.isType then jlThrow "TypeError" "typeintersect"
  jlTypeIntersection n E.types a b

/-- `has_free_typevars(t)` (`jl_has_free_typevars`). -/
def hasFreeTypevars (t : Val) : Bool := t.hasFreeTypevars

/-- `isa(x, Type)`, equivalently `isa(x, Core.AnyType)`: the object's tag is a kind
(`jl_is_type`). -/
def isTypeObj (t : Val) : Bool := t.isType

/-- `isvarargtype(t)` (`base/essentials.jl:589-591`). -/
def isvarargtype (t : Val) : Bool := t.isVararg

/-- `unwrapva(t)` (`base/essentials.jl:603-606`). -/
def unwrapva (t : Val) : Val :=
  match t with
  | .vararg (some T) _ => T
  | .vararg none _ => anyType
  | t => t

/-- `isTypeEq(t)`, `isTypeEgal(t)`, `isType(t)` (`base/runtime_internals.jl:1095-1109`). -/
def isTypeEq (t : Val) : Bool := t.isTypeeq
def isTypeEgal (t : Val) : Bool := t.isTypeegal
def isType (t : Val) : Bool := isTypeEq t || isTypeEgal t

/-- `type_parameter(t)` (`base/runtime_internals.jl:1111-1112`). -/
def typeParameter (t : Val) : CM Val :=
  match t with
  | .typeeq T | .typeegal T => pure T
  | _ => jlThrow "MethodError" "type_parameter"

/-- `Type{t}` (`jl_wrap_Type` via `apply_type`). -/
def mkTypeEq (n : Nat) (E : CEnv) (t : Val) : CM Val := wrapType n E.types (subOps n E.types) t

/-- `Core.TypeEgal{t}` (`jl_wrap_TypeEgal`). -/
def mkTypeEgal (t : Val) : CM Val := do
  if !t.isType || t.hasFreeTypevars then jlThrow "TypeError" "TypeEgal parameter"
  wrapTypeEgal t

/-- `issingletontype(t)` (`base/runtime_internals.jl:1212`): a `DataType` with an instance and an
empty pointer-free layout, which only concrete types have (`jl_is_datatype_singleton`). -/
def issingletontype (n : Nat) (E : CEnv) (t : Val) : CM Bool := do
  if !t.isDatatype then return false
  isDatatypeSingleton n E.types t

/-- `t.instance` of a singleton type: `Union{}` for `typeof(Union{})`, otherwise the recorded
instance (a singleton struct can have fields of singleton types, e.g. `Some(nothing)`). -/
def singletonInstance (E : CEnv) (t : Val) : Val :=
  if t == typeofbottomType then .bottom
  else match E.instances.find? (·.1 == t) with
    | some (_, v) => v
    | none => .imm t []

/-- `ismutable(x)` (`base/runtime_internals.jl:840`): the type name of `typeof(x)` is mutable. -/
def ismutable (E : CEnv) (x : Val) : CM Bool := do
  match typeOf x with
  | .datatype name _ => return (← E.types.typename name).mutable
  | _ => jlThrow "TypeError" "ismutable"

/-- `typeof(val).name.constfields != C_NULL`. -/
def hasConstfields (E : CEnv) (x : Val) : Bool :=
  match typeOf x with
  | .datatype name _ => E.constfields.contains name
  | _ => false

/-- `nfields(x)` for a `Const` payload. -/
def nfieldsOf (E : CEnv) (x : Val) : CM Nat :=
  match x with
  | .imm ty fs =>
    if ty.isTupleType then pure fs.length
    else match E.nfields.find? (·.1 == ty) with
      | some (_, k) => pure k
      | none => unmodelled s!"nfields of {repr ty}"
  | .long _ | .bits .. | .symbol _ | .module _ => pure 0
  | _ => unmodelled s!"nfields of {repr x}"

/-- `isdefined(x, i)` for a `Const` payload (1-based `i`). -/
def isdefinedField (x : Val) (i : Nat) : Bool :=
  match x with
  | .imm _ fs => 1 ≤ i && i ≤ fs.length
  | _ => false

/-- `getfield(x, i)` for a `Const` payload (1-based `i`), after `isdefined(x, i)`. -/
def getfieldVal (x : Val) (i : Nat) : CM Val :=
  match x with
  | .imm _ fs => match fs[i - 1]? with
    | some v => pure v
    | none => jlThrow "UndefRefError"
  | _ => unmodelled "getfield"

/-- `Tuple.name`, `Task`, `TypeVar`, `Bool`. -/
def taskType : Val := .datatype "Core.Task" []
def boolTy : Val := .datatype "Core.Bool" []
def boolVal (b : Bool) : Val := .bits boolTy (if b then 1 else 0)

/-- `x === true` / `x === false` for a Julia object `x`. -/
def asBool? (x : Val) : Option Bool :=
  match x with
  | .bits ty 1 => if ty == boolTy then some true else none
  | .bits ty 0 => if ty == boolTy then some false else none
  | _ => none

/-- An object identity (`IdSet`, `Vector`, `MethodInstance`, ...), compared by `===`. -/
abbrev ObjId := Nat

/-- Lattice elements: the native types (`ty`) and the wrapper structs.

Julia source: base/boot.jl:651-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Const
    val
    Const(@nospecialize(v)) = new(v)
end

struct PartialStruct
    typ
    undefs::Array{Union{Nothing,Bool}, 1}
    fields::Array{Any, 1}
    ...
end

struct InterConditional
    slot::Int
    thentype
    elsetype
    ...
end

struct InterMustAlias
    slot::Int
    vartyp::Any
    fldidx::Int
    fldtyp::Any
    ...
end

struct PartialOpaque
    typ::Type
    env
    parent::MethodInstance
    source
    ...
end

struct PartialTask
    fetch_type
    PartialTask(@nospecialize(fetch_type)) = new(fetch_type)
end
```

Julia source: Compiler/src/typelattice.jl:40-57,90-105,126-133,192-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Conditional
    slot::Int
    ssadef::Int
    thentype
    elsetype
    isdefined::Bool
    ...
end

struct MustAlias
    slot::Int
    ssadef::Int
    vartyp::Any
    fldidx::Int
    fldtyp::Any
    ...
end

struct PartialTypeVar
    tv::TypeVar
    lb_certain::Bool
    ub_certain::Bool
    ...
end

struct LimitedAccuracy
    typ
    causes::IdSet{InferenceState}
    ...
end
```

The constructors are raw `new`; the validating constructors of `typelattice.jl` are modelled
separately. The `Vector`s of a `PartialStruct` and the `IdSet` of a `LimitedAccuracy` are mutable,
so `===` compares them by the identities `undefsId`, `fieldsId` and `causesId`. A cause is an
`InferenceState`, identified by its `ObjId`; `PartialOpaque`'s `parent` and `source` likewise. -/
inductive LElt where
  /-- A native type, or another Julia object used as a lattice element (`TypeVar`, `Vararg`). -/
  | ty (t : Val)
  | const (val : Val)
  | partialStruct (typ : Val) (undefs : List (Option Bool)) (fields : List LElt)
      (undefsId fieldsId : ObjId)
  | conditional (slot ssadef : Int) (thentype elsetype : LElt) (isdefined : Bool)
  | interConditional (slot : Int) (thentype elsetype : LElt)
  | mustAlias (slot ssadef : Int) (vartyp : LElt) (fldidx : Int) (fldtyp : LElt)
  | interMustAlias (slot : Int) (vartyp : LElt) (fldidx : Int) (fldtyp : LElt)
  | partialTypeVar (tv : Val) (lbCertain ubCertain : Bool)
  | limitedAccuracy (typ : LElt) (causes : List ObjId) (causesId : ObjId)
  | partialOpaque (typ : Val) (env : LElt) (parent source : ObjId)
  | partialTask (fetchType : LElt)
  deriving Repr, Inhabited

namespace LElt
def isConst : LElt → Bool | .const _ => true | _ => false
def isPartialStruct : LElt → Bool | .partialStruct .. => true | _ => false
def isConditional : LElt → Bool | .conditional .. => true | _ => false
def isInterConditional : LElt → Bool | .interConditional .. => true | _ => false
def isMustAlias : LElt → Bool | .mustAlias .. => true | _ => false
def isInterMustAlias : LElt → Bool | .interMustAlias .. => true | _ => false
def isPartialTypeVar : LElt → Bool | .partialTypeVar .. => true | _ => false
def isLimited : LElt → Bool | .limitedAccuracy .. => true | _ => false
def isPartialOpaque : LElt → Bool | .partialOpaque .. => true | _ => false
def isPartialTask : LElt → Bool | .partialTask .. => true | _ => false
/-- `isa(x, AnyConditional)` -/
def isAnyConditional (x : LElt) : Bool := x.isConditional || x.isInterConditional
/-- `isa(x, AnyMustAlias)` -/
def isAnyMustAlias (x : LElt) : Bool := x.isMustAlias || x.isInterMustAlias
/-- `isa(x, Type)` (equivalently `isa(x, AnyType)`) -/
def isTypeElt : LElt → Bool | .ty t => t.isType | _ => false
/-- `isa(x, Core.TypeofVararg)` -/
def isVarargElt : LElt → Bool | .ty t => t.isVararg | _ => false
end LElt

/-- `x === y` on lattice elements: structs field by field, mutable fields by identity. -/
def eltEgal (n : Nat) (E : CEnv) (a b : LElt) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match a, b with
    | .ty x, .ty y => egal n E x y
    | .const x, .const y => egal n E x y
    | .partialStruct t1 _ _ u1 f1, .partialStruct t2 _ _ u2 f2 => do
      if !(u1 == u2 && f1 == f2) then return false
      egal n E t1 t2
    | .conditional s1 d1 a1 b1 i1, .conditional s2 d2 a2 b2 i2 => do
      if !(s1 == s2 && d1 == d2 && i1 == i2) then return false
      if !(← eltEgal n E a1 a2) then return false
      eltEgal n E b1 b2
    | .interConditional s1 a1 b1, .interConditional s2 a2 b2 => do
      if s1 != s2 then return false
      if !(← eltEgal n E a1 a2) then return false
      eltEgal n E b1 b2
    | .mustAlias s1 d1 v1 i1 f1, .mustAlias s2 d2 v2 i2 f2 => do
      if !(s1 == s2 && d1 == d2 && i1 == i2) then return false
      if !(← eltEgal n E v1 v2) then return false
      eltEgal n E f1 f2
    | .interMustAlias s1 v1 i1 f1, .interMustAlias s2 v2 i2 f2 => do
      if !(s1 == s2 && i1 == i2) then return false
      if !(← eltEgal n E v1 v2) then return false
      eltEgal n E f1 f2
    | .partialTypeVar t1 l1 u1, .partialTypeVar t2 l2 u2 =>
      pure (t1.tvId == t2.tvId && l1 == l2 && u1 == u2)
    | .limitedAccuracy t1 _ c1, .limitedAccuracy t2 _ c2 => do
      if c1 != c2 then return false
      eltEgal n E t1 t2
    | .partialOpaque t1 e1 p1 s1, .partialOpaque t2 e2 p2 s2 => do
      if !(p1 == p2 && s1 == s2) then return false
      if !(← egal n E t1 t2) then return false
      eltEgal n E e1 e2
    | .partialTask f1, .partialTask f2 => eltEgal n E f1 f2
    | _, _ => pure false

/-- Lattice layers (`Compiler/src/abstractlattice.jl:10-96`).

Julia source: Compiler/src/abstractlattice.jl:10-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
...
struct JLTypeLattice <: AbstractLattice; end
struct ConstsLattice <: AbstractLattice; end
struct PartialsLattice{𝕃<:AbstractLattice} <: AbstractLattice
    parent::𝕃
end
struct ConditionalsLattice{𝕃<:AbstractLattice} <: AbstractLattice
    parent::𝕃
end
struct InterConditionalsLattice{𝕃<:AbstractLattice} <: AbstractLattice
    parent::𝕃
end
struct MustAliasesLattice{𝕃<:AbstractLattice} <: AbstractLattice
    parent::𝕃
end
struct InterMustAliasesLattice{𝕃<:AbstractLattice} <: AbstractLattice
    parent::𝕃
end
struct InferenceLattice{𝕃<:AbstractLattice} <: AbstractLattice
    parent::𝕃
end
```
-/
inductive Lattice where
  | jlType
  | consts
  | partials (parent : Lattice)
  | conditionals (parent : Lattice)
  | interConditionals (parent : Lattice)
  | mustAliases (parent : Lattice)
  | interMustAliases (parent : Lattice)
  | inference (parent : Lattice)
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `SimpleInferenceLattice`, `BaseInferenceLattice`, `IPOResultLattice`
(`Compiler/src/abstractlattice.jl:81-83`). -/
def simpleInferenceLattice : Lattice := .partials .consts
def baseInferenceLattice : Lattice := .mustAliases (.conditionals simpleInferenceLattice)
def ipoResultLattice : Lattice := .interMustAliases (.interConditionals simpleInferenceLattice)

/-- `fallback_lattice`, `fallback_ipo_lattice` (`Compiler/src/abstractlattice.jl:305-306`). -/
def fallbackLattice : Lattice := .inference baseInferenceLattice
def fallbackIpoLattice : Lattice := .inference ipoResultLattice

/-- `typeinf_lattice`, `ipo_lattice` and `optimizer_lattice` of a `NativeInterpreter`
(`Compiler/src/types.jl:649-651`). -/
def typeinfLattice : Lattice := .inference baseInferenceLattice
def ipoLattice : Lattice := .inference ipoResultLattice
def optimizerLattice : Lattice := simpleInferenceLattice

end JuliaLean.Compiler
