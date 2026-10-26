import JuliaLean.Core

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
