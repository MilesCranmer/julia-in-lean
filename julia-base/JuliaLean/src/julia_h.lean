/-!
The Julia objects that the type system manipulates (`src/julia.h`).

A `Val` is a Julia object reachable from a type: the type objects themselves (`DataType`,
`Union`, `UnionAll`, `TypeVar`, `Vararg`, `Union{}`, and the `TypeEq`/`TypeEgal` wrappers and
internal `Intersect` node of this Julia version) and the plain values allowed as type parameters
(`Int` and `Symbol`).

Object identity. C compares `jl_value_t*` pointers. Type variables are mutable objects with
identity in Julia (subtyping rewrites the bounds of inner variables in place,
`src/subtype.c:2038-2059`), so a `typevar` carries a unique `id`; equal ids are the same object,
and `==` compares type variables, and the variable of a `unionall`, by id alone. `DataType`s are
hash-consed by `jl_apply_type`, so pointer equality on them is structural equality. Unions and
UnionAlls are not cached in Julia; the model compares them structurally, which can only make a
pointer-equality fast path succeed where Julia would fall through to the full algorithm on equal
inputs.
-/

namespace JuliaLean.C

inductive Val where
  /-- A `DataType`: a type name applied to parameters. `Tuple` and `Vararg`-ended tuples use the
  name `Core.Tuple`. -/
  | datatype (name : String) (params : List Val)
  | union (a b : Val)
  /-- Internal meet node `Intersect{a, b}` (`jl_intersect_type`). -/
  | intersect (a b : Val)
  /-- `Type{T}`: the types `==` to `T` (`jl_typeeq_type`). -/
  | typeeq (T : Val)
  /-- `TypeEgal{T}`: the type object `T` itself (`jl_typeegal_type`). -/
  | typeegal (T : Val)
  /-- `body where lb <: name <: ub`; the bound variable is `typevar id name lb ub`. -/
  | unionall (id : Nat) (name : String) (lb ub body : Val)
  | typevar (id : Nat) (name : String) (lb ub : Val)
  /-- `Vararg{T, N}`; either part may be absent. -/
  | vararg (T : Option Val) (N : Option Val)
  /-- `Union{}` (`jl_bottom_type`). -/
  | bottom
  /-- `TypeApp{head, param}`: one lazy type application step (recursive type groups). -/
  | typeapp (head param : Val)
  | long (n : Int)
  | symbol (s : String)
  /-- A value of a primitive type other than `Int64` (which is `long`), e.g. `true` is
  `bits Bool 1` and `0x00` is `bits UInt8 0`. -/
  | bits (ty : Val) (v : Int)
  /-- An immutable struct or tuple value with its field values, e.g. `(:a, :b)`. -/
  | imm (ty : Val) (fields : List Val)
  /-- A module object, e.g. `Core` in `AddrSpace{Core}`; modules are compared by name. -/
  | module (name : String)
  deriving Repr, Inhabited

mutual
/-- Object equality: structural, except that a type variable is its `id`. -/
def Val.beq : Val → Val → Bool
  | .datatype n ps, .datatype m qs => n == m && Val.beqList ps qs
  | .union a b, .union c d | .intersect a b, .intersect c d | .typeapp a b, .typeapp c d =>
    Val.beq a c && Val.beq b d
  | .typeeq a, .typeeq b | .typeegal a, .typeegal b => Val.beq a b
  | .unionall i _ _ _ a, .unionall j _ _ _ b => i == j && Val.beq a b
  | .typevar i .., .typevar j .. => i == j
  | .vararg t n, .vararg u m => Val.beqOpt t u && Val.beqOpt n m
  | .bottom, .bottom => true
  | .long a, .long b => a == b
  | .symbol a, .symbol b => a == b
  | .bits t a, .bits u b => Val.beq t u && a == b
  | .imm t xs, .imm u ys => Val.beq t u && Val.beqList xs ys
  | .module a, .module b => a == b
  | _, _ => false
def Val.beqList : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => Val.beq a b && Val.beqList as bs
  | _, _ => false
def Val.beqOpt : Option Val → Option Val → Bool
  | none, none => true
  | some a, some b => Val.beq a b
  | _, _ => false
end

instance : BEq Val := ⟨Val.beq⟩

/-- What Julia stores in a `jl_typename_t` and the `DataType` it wraps. -/
structure TypeName where
  name : String
  abstract : Bool
  mutable : Bool
  /-- `tn.wrapper`: the `UnionAll`s over the type's parameters, around the generic `DataType`. -/
  wrapper : Val
  /-- The declared supertype of the generic `DataType`, over the wrapper's variables; `none` for
  `Any`, whose supertype is itself. -/
  super : Option Val
  deriving Repr, Inhabited

/-- The type names a computation can reach, as `jl_typename_t` objects referenced by name. -/
abbrev Universe := List TypeName

def Universe.find? (U : Universe) (name : String) : Option TypeName :=
  List.find? (fun t => t.name == name) U

/-- Properties a concrete `DataType` gets from its layout (`src/datatype.c`), which is not
modelled: `isbitstype`, `jl_is_datatype_singleton` and `has_concrete_subtype` (cleared from field
types in `jl_compute_field_offsets`, `src/datatype.c:699-708`). -/
structure Layout where
  dt : Val
  isbits : Bool
  singleton : Bool
  concreteSubtype : Bool
  deriving Repr, Inhabited

/-- The type names and layouts a computation can reach. -/
structure Types where
  names : Universe
  layouts : List Layout
  deriving Inhabited

/-- Computations on type objects. The state is the next fresh `TypeVar` id (`jl_new_typevar`);
an error is a Julia error, or exhaustion of the explicit recursion budget (Julia's stack
overflow). -/
abbrev CM := StateT Nat (Except String)

def freshId : CM Nat := modifyGet fun n => (n, n + 1)

def outOfBudget {α : Type} : CM α := throw "recursion budget exhausted"

def Types.typename (T : Types) (name : String) : CM TypeName :=
  match T.names.find? name with
  | some tn => pure tn
  | none => throw s!"unknown type name {name}"

/-- Well-known objects (`jl_any_type`, `jl_tuple_typename`, the kinds, ...). -/
def anyType : Val := .datatype "Core.Any" []
def tupleName : String := "Core.Tuple"
def datatypeType : Val := .datatype "Core.DataType" []
def uniontypeType : Val := .datatype "Core.Union" []
def unionallType : Val := .datatype "Core.UnionAll" []
def typeeqType : Val := .datatype "Core.TypeEq" []
def typeegalType : Val := .datatype "Core.TypeEgal" []
def typeofbottomType : Val := .datatype "Core.TypeofBottom" []
def tvarType : Val := .datatype "Core.TypeVar" []
def varargType : Val := .datatype "Core.TypeofVararg" []
def typeappType : Val := .datatype "Core.TypeApp" []
def intersectType : Val := .datatype "Core.Intersect" []
def longType : Val := .datatype "Core.Int64" []
def symbolType : Val := .datatype "Core.Symbol" []
/-- `jl_anytype_type`, the abstract kind `AnyType` (`== Type`, though not `===`). -/
def anytypeType : Val := .datatype "Core.AnyType" []

/-- `jl_typeof` -/
def typeOf : Val → Val
  | .datatype .. => datatypeType
  | .union .. => uniontypeType
  | .intersect .. => intersectType
  | .typeeq .. => typeeqType
  | .typeegal .. => typeegalType
  | .unionall .. => unionallType
  | .typevar .. => tvarType
  | .vararg .. => varargType
  | .bottom => typeofbottomType
  | .typeapp .. => typeappType
  | .long _ => longType
  | .symbol _ => symbolType
  | .bits ty _ => ty
  | .imm ty _ => ty
  | .module _ => .datatype "Core.Module" []

def Val.isDatatype : Val → Bool | .datatype .. => true | _ => false
def Val.isUnion : Val → Bool | .union .. => true | _ => false
def Val.isIntersect : Val → Bool | .intersect .. => true | _ => false
def Val.isTypeeq : Val → Bool | .typeeq .. => true | _ => false
def Val.isTypeegal : Val → Bool | .typeegal .. => true | _ => false
/-- `jl_is_some_Type` -/
def Val.isSomeType (v : Val) : Bool := v.isTypeeq || v.isTypeegal
def Val.isUnionall : Val → Bool | .unionall .. => true | _ => false
def Val.isTypevar : Val → Bool | .typevar .. => true | _ => false
def Val.isVararg : Val → Bool | .vararg .. => true | _ => false
def Val.isTypeapp : Val → Bool | .typeapp .. => true | _ => false
def Val.isLong : Val → Bool | .long _ => true | _ => false
def Val.isSymbol : Val → Bool | .symbol _ => true | _ => false
def Val.isModule : Val → Bool | .module _ => true | _ => false

/-- The parameter of a `TypeEq`/`TypeEgal` (`jl_some_Type_T`). -/
def Val.someTypeT : Val → Val | .typeeq T | .typeegal T => T | v => v

/-- `jl_is_kind`: the concrete kinds, whose instances are type objects. -/
def isKind (v : Val) : Bool :=
  v == uniontypeType || v == datatypeType || v == unionallType || v == typeeqType ||
  v == typeegalType || v == typeofbottomType

/-- `jl_is_type`: the object's tag is a kind. -/
def Val.isType (v : Val) : Bool := isKind (typeOf v)

def Val.name? : Val → Option String | .datatype n _ => some n | _ => none
def Val.params : Val → List Val | .datatype _ ps => ps | _ => []
/-- `jl_nparams` -/
def Val.nparams (v : Val) : Nat := v.params.length

/-- The variable of a `UnionAll`, as the `TypeVar` object. -/
def Val.uaVar : Val → Val | .unionall id n lb ub _ => .typevar id n lb ub | v => v
def Val.uaBody : Val → Val | .unionall _ _ _ _ b => b | v => v
def Val.tvId : Val → Option Nat | .typevar id _ _ _ => some id | _ => none
def Val.tvLb : Val → Val | .typevar _ _ lb _ => lb | _ => .bottom
def Val.tvUb : Val → Val | .typevar _ _ _ ub => ub | _ => anyType

/-- `jl_unwrap_unionall` -/
def Val.unwrapUnionall : Val → Val
  | .unionall _ _ _ _ b => b.unwrapUnionall
  | v => v

end JuliaLean.C
