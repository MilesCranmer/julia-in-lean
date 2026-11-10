import JuliaLean.Compiler.Prelude
import JuliaLean.Compiler.src.typeutils
import JuliaLean.Compiler.src.abstractlattice
import JuliaLean.Compiler.src.typelattice

/-!
`Compiler/src/typelimits.jl`: `tmerge` for every lattice layer, its fast path and slow path,
`tuplemerge`, the union-size limits, and the type-size limits (`limit_type_size`,
`type_more_complex`, `is_derived_type`).

Every function takes an explicit fuel `n` (Julia has none: running out is a model failure, not a
Julia outcome). Recursion through the layers keeps the layer explicit, as Julia's dispatch on the
lattice argument does.

The helpers these functions call from `base/` and from other `Compiler/src` files come first,
each citing its source. Two calls leave the modelled files:

* `getfield_tfunc(𝕃, x, Const(i))` (`Compiler/src/tfuncs.jl:1183-1400`), which
  `tmerge_partial_struct` and `issimplertype` call on a `Const` or `PartialStruct`. The model
  covers the branches those calls reach on a `PartialStruct` with `1 ≤ i ≤ length(fields)` and on
  a `Const` of an immutable non-type value; any other input reports `unmodelled`.
* `fieldtype(T, i)` and `datatype_min_ninitialized(T)` of a struct type read field types and
  `n_uninitialized`, which `Types` does not record; they come from the `CEnv.structs` side table,
  and a type missing from it reports `unmodelled`.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-! ## Julia builtins and `base/` helpers on type objects -/

/-- The C model throws Julia errors raised in `src/jltypes.c` as plain strings; turn the ones the
calls below can raise into Julia exceptions. -/
def liftC {α : Type} (m : CM α) : CM α := do
  try m catch e =>
    if e.startsWith "TypeError" then throw s!"julia:TypeError: {e}"
    else if e.startsWith "Wrapping `Vararg`" || e.startsWith "too many parameters" then
      throw s!"julia:ErrorException: {e}"
    else if e.startsWith "Vararg length is negative" then throw s!"julia:ErrorException: {e}"
    else if e.startsWith "Tuple field type cannot be Union{}" then
      throw s!"julia:ErrorException: {e}"
    else throw e

def tops (n : Nat) (E : CEnv) : Ops := subOps n E.types

/-- `Union{ts...}` (`jl_type_union`). -/
def jlUnion (n : Nat) (E : CEnv) (ts : List Val) : CM Val :=
  liftC (typeUnion n E.types (tops n E) ts)

/-- `UnionAll(v, body)` (`jl_type_unionall`). -/
def jlUnionAll (n : Nat) (E : CEnv) (v body : Val) : CM Val :=
  liftC (typeUnionall n E.types (tops n E) v body)

/-- `Vararg{T}` and `Vararg{T, N}` (`jl_wrap_vararg` with `check = 1`). -/
def jlVararg (n : Nat) (E : CEnv) (T : Val) (N : Option Val := none) : CM Val := do
  let some r ← liftC (wrapVararg n E.types (tops n E) (some T) N true 0)
    | jlThrow "TypeError" "Vararg"
  return r

/-- `Tuple{ps...}` (`jl_f_apply_type` on `Tuple`, then `jl_apply_tuple_type_v`).

Julia source: src/builtins.c (jl_f_apply_type) @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    if (args[0] == (jl_value_t*)jl_anytuple_type) {
        for(i=1; i < nargs; i++) {
            jl_value_t *pi = args[i];
            if (jl_is_vararg(pi)) {
                if (i != nargs-1)
                    jl_type_error_rt("Tuple", "non-final parameter", (jl_value_t*)jl_type_type, pi);
            }
            else if (!jl_is_valid_type_param(pi)) {
                jl_type_error_rt("Tuple", "parameter", (jl_value_t*)jl_type_type, pi);
            }
        }
        return jl_apply_tuple_type_v(&args[1], nargs-1);
    }
```
-/
def jlTuple (n : Nat) (E : CEnv) (ps : List Val) : CM Val := do
  let k := ps.length
  for (p, i) in ps.zip (List.range k) do
    if p.isVararg then
      if i + 1 != k then jlThrow "TypeError" "Tuple: non-final parameter"
    else if !(← validTypeParam n E.types p) then
      jlThrow "TypeError" "Tuple: parameter"
  let some r ← liftC (instDatatypeInner n E.types (tops n E) tupleName ps true 0)
    | jlThrow "TypeError" "Tuple"
  return r

/-- `tc{ps...}` for a `UnionAll` `tc` (`jl_apply_type`, `src/jltypes.c`): instantiate the
outer variables one at a time, checking each parameter against its bounds when they are
closed. -/
def jlApplyType (n : Nat) (E : CEnv) (tc : Val) (ps : List Val) : CM Val := do
  let ops := tops n E
  let mut tc := tc
  let mut tc0 := tc
  for p in ps do
    let .unionall _ _ _ _ body := tc0 | jlThrow "ErrorException" "too many parameters for type"
    tc0 := body
    if let .unionall _ _ lb ub _ := tc then
      if !lb.hasFreeTypevars && !ub.hasFreeTypevars then
        if !(← withinTypevar ops p lb ub) then jlThrow "TypeError" "apply_type: parameter bound"
      tc ← liftC (instantiateUnionall n E.types ops tc p)
  return tc

/-- `TypeVar(name, ub)` with `lb = Union{}`: a fresh variable. -/
def jlNewTypeVar (name : String) (ub : Val) : CM Val := do
  if !(ub.isType || ub.isTypevar) then jlThrow "TypeError" "TypeVar: upper bound"
  return .typevar (← freshId) name .bottom ub

/-- `Type` (`TypeEq{T} where T`); the model numbers its variable 0. -/
def typeTypeVal : Val := .unionall 0 "T" .bottom anyType (.typeeq (.typevar 0 "T" .bottom anyType))

/-- The type names `Any.name`, `Tuple.name` and `TypeEq.name`. -/
def anyName : String := "Core.Any"
def typeEqName : String := "Core.TypeEq"

/-- `unwrap_unionall(a)` and `rewrap_unionall(t, u)`.

Julia source: base/essentials.jl:544-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unwrap_unionall(@nospecialize(a))
    @_foldable_meta
    while isa(a,UnionAll)
        a = a.body
    end
    return a
end

function rewrap_unionall(@nospecialize(t), @nospecialize(u))
    @_foldable_meta
    if !isa(u, UnionAll)
        return t
    end
    return UnionAll(u.var, rewrap_unionall(t, u.body))
end

function rewrap_unionall(t::Core.TypeofVararg, @nospecialize(u))
    @_foldable_meta
    isdefined(t, :T) || return t
    if !isa(u, UnionAll)
        return t
    end
    T = rewrap_unionall(t.T, u)
    if !isdefined(t, :N) || t.N === u.var
        return Vararg{T}
    end
    return Vararg{T, t.N}
end
```
-/
def unwrapUnionall (a : Val) : Val := a.unwrapUnionall

def rewrapUnionallJ (n : Nat) (E : CEnv) (t u : Val) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let .vararg tT tN := t then
      let some tT := tT | return t
      if !u.isUnionall then return t
      let T ← rewrapUnionallJ n E tT u
      match tN with
      | none => return ← jlVararg n E T
      | some N => if N == u.uaVar then return ← jlVararg n E T else return ← jlVararg n E T (some N)
    let .unionall .. := u | return t
    jlUnionAll n E u.uaVar (← rewrapUnionallJ n E t u.uaBody)

/-- `supertype(T::DataType)` (`base/operators.jl:86-94`) and `datatype_super`
(`Compiler/src/utilities.jl:6`); `Tuple`s and `Any` have supertype `Any`. -/
def supertypeDT (n : Nat) (E : CEnv) (t : Val) : CM Val := do
  if !t.isDatatype then jlThrow "MethodError" "supertype"
  superOf n E.types (tops n E) t

/-- `isconcretetype(t)` (`base/runtime_internals.jl:1161`). -/
def isconcretetype (E : CEnv) (t : Val) : CM Bool := isConcreteType E.types t

/-- `iskindtype`, `isconcretedispatch`, `isdispatchelem`.

Julia source: base/runtime_internals.jl:1049,1074,1080-1083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iskindtype(@nospecialize t) = (t === Core.AnyType || t === DataType || t === UnionAll || t === Union || t === TypeEq || t === Core.TypeEgal || t === typeof(Bottom))
isconcretedispatch(@nospecialize t) = isconcretetype(t) && !iskindtype(t)
function isdispatchelem(@nospecialize v)
    return (v === Bottom) || (v === typeof(Bottom)) || isconcretedispatch(v) ||
        isTypeEgal(v) || (isTypeEq(v) && type_parameter(v) === Union{})
end
```
-/
def iskindtype (t : Val) : Bool :=
  t == anytypeType || t == datatypeType || t == unionallType || t == uniontypeType ||
    t == typeeqType || t == typeegalType || t == typeofbottomType

def isconcretedispatch (E : CEnv) (t : Val) : CM Bool := do
  return (← isconcretetype E t) && !iskindtype t

def isdispatchelem (E : CEnv) (v : Val) : CM Bool := do
  if v == .bottom || v == typeofbottomType then return true
  if ← isconcretedispatch E v then return true
  return isTypeEgal v || (isTypeEq v && v.someTypeT == .bottom)

/-- `isabstracttype(t)` (`base/runtime_internals.jl:1186-1192`). -/
def isabstracttype (E : CEnv) (t : Val) : CM Bool := do
  let t := unwrapUnionall t
  if isType t then return true
  match t with
  | .datatype name _ => return (← E.types.typename name).abstract
  | _ => return false

/-- `unionlen(x)` and `_uniontypes(x, ts)`.

Julia source: base/runtime_internals.jl:1778-1789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unionlen(@nospecialize(x)) = x isa Union ? unionlen(x.a) + unionlen(x.b) : 1

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
def unionlen : Val → Nat
  | .union a b => unionlen a + unionlen b
  | _ => 1

def uniontypes : Val → List Val
  | .union a b => uniontypes a ++ uniontypes b
  | x => [x]

/-- `unioncomplexity(x)`

Julia source: Compiler/src/typeutils.jl:394-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# unioncomplexity estimates the number of calls to `tmerge` to obtain the given type by
# counting the Union instances, taking also into account those hidden in a Tuple or UnionAll
unioncomplexity(@nospecialize x) = _unioncomplexity(x)::Int
function _unioncomplexity(@nospecialize x)
    if isa(x, DataType)
        x.name === Tuple.name || return 0
        c = 0
        for ti in x.parameters
            c = max(c, unioncomplexity(ti))
        end
        return c
    elseif isa(x, Union)
        return unioncomplexity(x.a) + unioncomplexity(x.b) + 1
    elseif isa(x, UnionAll)
        return max(unioncomplexity(x.body), unioncomplexity(x.var.ub))
    elseif isa(x, TypeofVararg)
        return isdefined(x, :T) ? unioncomplexity(x.T) + 1 : 1
    else
        return 0
    end
end
```
-/
def unioncomplexity (n : Nat) (x : Val) : CM Nat :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match x with
    | .datatype name ps =>
      if name != tupleName then return 0
      let mut c := 0
      for ti in ps do
        c := max c (← unioncomplexity n ti)
      return c
    | .union a b => return (← unioncomplexity n a) + (← unioncomplexity n b) + 1
    | .unionall _ _ _ ub body => return max (← unioncomplexity n body) (← unioncomplexity n ub)
    | .vararg (some T) _ => return (← unioncomplexity n T) + 1
    | .vararg none _ => return 1
    | _ => return 0

/-- `unwraptv_ub(t)` (`Compiler/src/typeutils.jl:425-430`): strip `TypeVar`s to their upper
bound. -/
def unwraptv (n : Nat) (t : Val) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => if let .typevar _ _ _ ub := t then unwraptv n ub else pure t

/-- `fieldtype(T, i)` for a `DataType` `T` (the `fieldtype` builtin): a tuple's `i`-th
parameter (its `Vararg` element type at and after the last position), or a struct's declared
field type from `CEnv.structs`. -/
def fieldtypeIdx (E : CEnv) (T : Val) (i : Nat) : CM Val := do
  match T with
  | .datatype name ps =>
    if name == tupleName then
      let np := ps.length
      if np > 0 && ps.getLast!.isVararg && i ≥ np then return unwrapva ps.getLast!
      if i < 1 || i > np then jlThrow "BoundsError" "fieldtype"
      return ps[i - 1]!
    match E.structs.find? (·.1 == T) with
    | some (_, fts, _) =>
      if i < 1 || i > fts.length then jlThrow "BoundsError" "fieldtype"
      return fts[i - 1]!
    | none => unmodelled s!"fieldtype of {repr T}"
  | _ => unmodelled s!"fieldtype of {repr T}"

/-- `datatype_fieldcount(t)` (`base/runtime_internals.jl:1376-1395`). -/
def datatypeFieldcount (E : CEnv) (t : Val) : CM (Option Nat) := do
  let .datatype name ps := t | jlThrow "TypeError" "datatype_fieldcount"
  if name == "Core.NamedTuple" then unmodelled "datatype_fieldcount(NamedTuple)"
  if ← isabstracttype E t then return none
  if name == tupleName then
    if t.isVaTuple then return none
    return some ps.length
  match E.structs.find? (·.1 == t) with
  | some (_, fts, _) => return some fts.length
  | none => match E.nfields.find? (·.1 == t) with
    | some (_, k) => return some k
    | none => unmodelled s!"fieldcount of {repr t}"

/-- `_fieldcount_noerror(t)` (`base/runtime_internals.jl:1440-1454`); the `Union` case is not
modelled. -/
def fieldcountNoerror (E : CEnv) (t : Val) : CM (Option Nat) := do
  if t == .bottom then return some 0
  let t := unwrapUnionall t
  if t.isUnion then unmodelled "_fieldcount_noerror(::Union)"
  if !t.isDatatype then return none
  datatypeFieldcount E t

/-- `fieldcount(t)`

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
def fieldcount (E : CEnv) (t : Val) : CM Nat := do
  if t == .bottom then jlThrow "ArgumentError" "fieldcount(Union{})"
  if isTypeEgal t then unmodelled "fieldcount(TypeEgal)"
  let t := unwrapUnionall t
  if t.isUnion then unmodelled "fieldcount(::Union)"
  if isTypeEq t then jlThrow "ArgumentError" "fieldcount(Type{T})"
  if !t.isDatatype then jlThrow "TypeError" "fieldcount"
  let some k ← datatypeFieldcount E t | jlThrow "ArgumentError" "fieldcount"
  return k

/-- `datatype_min_ninitialized(t0)`

Julia source: base/essentials.jl:615-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Compute the minimum number of initialized fields for a particular datatype
# (therefore also a lower bound on the number of fields)
function datatype_min_ninitialized(@nospecialize t0)
    t = unwrap_unionall(t0)
    t isa DataType || return 0
    isabstracttype(t) && return 0
    if t.name === _NAMEDTUPLE_NAME
        ...
    end
    if t.name === Tuple.name
        n = length(t.parameters)
        n == 0 && return 0
        va = t.parameters[n]
        if isvarargtype(va)
            n -= 1
            if isdefined(va, :N)
                va = va.N
                if va isa Int
                    n += va
                end
            end
        end
        return n
    end
    return length(t.name.names) - t.name.n_uninitialized
end
```
The `NamedTuple` branch is not modelled. -/
def datatypeMinNinitialized (E : CEnv) (t0 : Val) : CM Nat := do
  let t := unwrapUnionall t0
  let .datatype name ps := t | return 0
  if ← isabstracttype E t then return 0
  if name == "Core.NamedTuple" then unmodelled "datatype_min_ninitialized(NamedTuple)"
  if name == tupleName then
    let n := ps.length
    if n == 0 then return 0
    match ps.getLast! with
    | .vararg _ N =>
      let n := n - 1
      match N with
      | some (.long k) => return ((n : Int) + k).toNat
      | _ => return n
    | _ => return n
  match E.structs.find? (·.1 == t) with
  | some (_, _, k) => return k
  | none => unmodelled s!"datatype_min_ninitialized of {repr t}"

/-- `_typename(a)`: `Union{}` (the call throws), `Core.TypeName` (unknown), or `Const(tn)`.

Julia source: Compiler/src/typeutils.jl:164-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typename(@nospecialize a) = Union{}
_typename(::TypeVar) = Core.TypeName
function _typename(a::Union)
    ta = _typename(a.a)
    tb = _typename(a.b)
    ta === tb && return ta # same type-name
    (ta === Union{} || tb === Union{}) && return Union{} # threw an error
    (ta isa Const && tb isa Const) && return Union{} # will throw an error (different type-names)
    return Core.TypeName # uncertain result
end
_typename(union::UnionAll) = _typename(union.body)
_typename(a::DataType) = Const(a.name)
_typename(a::TypeEq) = Core.TypeName
```
-/
inductive TypenameT where
  | bottom
  | typeName
  | const (name : String)
  deriving BEq, Repr

def typenameT : Val → TypenameT
  | .typevar .. => .typeName
  | .union a b =>
    let ta := typenameT a
    let tb := typenameT b
    if ta == tb then ta
    else if ta == .bottom || tb == .bottom then .bottom
    else match ta, tb with
      | .const _, .const _ => .bottom
      | _, _ => .typeName
  | .unionall _ _ _ _ body => typenameT body
  | .datatype name _ => .const name
  | .typeeq _ => .typeName
  | _ => .bottom

/-- `tuple_tail_elem(𝕃, init, ct)`; `tmerge` is `tmerge(𝕃, ...)`.

Julia source: Compiler/src/typeutils.jl:178-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tuple_tail_elem(𝕃::AbstractLattice, @nospecialize(init), ct::Vector{Any})
    t = init
    for x in ct
        # FIXME: this is broken: it violates subtyping relations and creates invalid types with free typevars
        t = tmerge(𝕃, t, unwraptv(unwrapva(x)))
    end
    return Vararg{widenconst(t)}
end
```
-/
def tupleTailElem (n : Nat) (E : CEnv) (tmerge : LElt → LElt → CM LElt) (init : LElt)
    (ct : List Val) : CM Val := do
  let mut t := init
  for x in ct do
    t ← tmerge t (.ty (← unwraptv n (unwrapva x)))
  jlVararg n E (← widenconst n E t)

/-! ## Limitation parameters and union-size limits -/

/-- Julia source: Compiler/src/typelimits.jl:7-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const MAX_TYPEUNION_COMPLEXITY = 3
const MAX_TYPEUNION_LENGTH = 3
```
-/
def MAX_TYPEUNION_COMPLEXITY : Nat := 3
def MAX_TYPEUNION_LENGTH : Nat := 3

/-- `union_count_abstract(x)`

Julia source: Compiler/src/typelimits.jl:315-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
union_count_abstract(x::Union) = union_count_abstract(x.a) + union_count_abstract(x.b)
union_count_abstract(@nospecialize(x)) = !isdispatchelem(x)
```
-/
def unionCountAbstract (E : CEnv) : Val → CM Nat
  | .union a b => do return (← unionCountAbstract E a) + (← unionCountAbstract E b)
  | x => do return if ← isdispatchelem E x then 0 else 1

/-- `issimpleenoughtype(t)`; `issimpleenoughtupleelem` is the same function.

Julia source: Compiler/src/typelimits.jl:318-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issimpleenoughtype(@nospecialize t)
    ut = unwrap_unionall(t)
    ut isa DataType && ut.name.wrapper == t::Type && return true
    return max(unionlen(t), union_count_abstract(t) + 1) <= MAX_TYPEUNION_LENGTH &&
           unioncomplexity(t) <= MAX_TYPEUNION_COMPLEXITY
end

# We may want to apply a stricter limit than issimpleenoughtype to
# tupleelements individually, to try to keep the whole tuple under the limit,
# even after complicated recursion and other operations on it elsewhere
const issimpleenoughtupleelem = issimpleenoughtype
```
-/
def issimpleenoughtype (n : Nat) (E : CEnv) (t : Val) : CM Bool := do
  let ut := unwrapUnionall t
  if let .datatype name _ := ut then
    let tn ← E.types.typename name
    if ← tyEq n E tn.wrapper t then return true
  if !(max (unionlen t) ((← unionCountAbstract E t) + 1) ≤ MAX_TYPEUNION_LENGTH) then
    return false
  return (← unioncomplexity n t) ≤ MAX_TYPEUNION_COMPLEXITY

def issimpleenoughtupleelem := issimpleenoughtype

/-! ## Type-size limits -/

/-- `t ∈ supertypes(super)` up to `Any` (the `while` loop of `is_derived_type`). -/
def superChainHas (n : Nat) (E : CEnv) (t super : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if super == anyType then return false
    if ← egal n E t super then return true
    superChainHas n E t (← supertypeDT n E super)

/-- `is_derived_type(t, c, mindepth)`

Julia source: Compiler/src/typelimits.jl:35-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# try to find `type` somewhere in `comparison` type
# at a minimum nesting depth of `mindepth`
function is_derived_type(@nospecialize(t), @nospecialize(c), mindepth::Int)
    if has_free_typevars(t) || has_free_typevars(c)
        # Don't allow finding types with free typevars. These strongly depend
        # on identity and we do not make any effort to make sure this returns
        # sensible results in that case.
        return false
    end
    if t === c
        return mindepth <= 1
    end
    isvarargtype(t) && (t = unwrapva(t))
    isvarargtype(c) && (c = unwrapva(c))
    if isa(c, Union)
        # see if it is one of the elements of the union
        return is_derived_type(t, c.a, mindepth) || is_derived_type(t, c.b, mindepth)
    elseif isa(c, UnionAll)
        # see if it is derived from the body
        # also handle the var here, since this construct bounds the mindepth to the smallest possible value
        return is_derived_type(t, c.var.ub, mindepth) || is_derived_type(t, c.body, mindepth)
    elseif isType(c)
        return is_derived_type(t, type_parameter(c), mindepth)
    elseif isa(c, DataType)
        if mindepth > 0
            mindepth -= 1
        end
        if isa(t, DataType)
            # see if it is one of the supertypes of a parameter
            super = supertype(c)
            while super !== Any
                t === super && return true
                super = supertype(super)
            end
        end
        # see if it was extracted from a type parameter
        cP = c.parameters
        for p in cP
            is_derived_type(t, p, mindepth) && return true
        end
    end
    return false
end
```
-/
def isDerivedType (n : Nat) (E : CEnv) (t c : Val) (mindepth : Int) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if hasFreeTypevars t || hasFreeTypevars c then
      return false
    if ← egal n E t c then
      return decide (mindepth ≤ 1)
    let t := if isvarargtype t then unwrapva t else t
    let c := if isvarargtype c then unwrapva c else c
    match c with
    | .union ca cb =>
      if ← isDerivedType n E t ca mindepth then return true
      isDerivedType n E t cb mindepth
    | .unionall _ _ _ ub body =>
      if ← isDerivedType n E t ub mindepth then return true
      isDerivedType n E t body mindepth
    | _ =>
      if isType c then
        return ← isDerivedType n E t (← typeParameter c) mindepth
      else if c.isDatatype then
        let mindepth := if mindepth > 0 then mindepth - 1 else mindepth
        if t.isDatatype then
          if ← superChainHas n E t (← supertypeDT n E c) then return true
        for p in c.params do
          if ← isDerivedType n E t p mindepth then return true
      return false

/-- `is_derived_type_from_any(t, sources, mindepth)`

Julia source: Compiler/src/typelimits.jl:79-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_derived_type_from_any(@nospecialize(t), sources::SimpleVector, mindepth::Int)
    for s in sources
        is_derived_type(t, s, mindepth) && return true
    end
    return false
end
```
-/
def isDerivedTypeFromAny (n : Nat) (E : CEnv) (t : Val) (sources : List Val) (mindepth : Int) :
    CM Bool := do
  for s in sources do
    if ← isDerivedType n E t s mindepth then return true
  return false

/-- The names of the `TypeVar`s that the lowered `Type{<:Type}` (line 128) and `Type{<:Qt}`
(line 145) of `_limit_type_size` create; lowering fixes them when the pinned `Compiler` is built
(observed on the pinned binary). -/
def limitTypeVarNameType : String := "#s949"
def limitTypeVarName : String := "#s948"

/-- `Type{<:Q}`: a fresh `TypeVar` with upper bound `Q`, wrapped in `Type{}` and `where`. -/
def typeLowerWrap (n : Nat) (E : CEnv) (Q : Val) (name : String := limitTypeVarName) : CM Val := do
  let tv ← jlNewTypeVar name Q
  jlUnionAll n E tv (← mkTypeEq n E tv)

mutual
/-- `_limit_type_size(t, c, sources, depth, allowed_tuplelen)`; `tmerge` is
`tmerge(fallback_lattice, ...)`, which `tuple_tail_elem` calls.

Julia source: Compiler/src/typelimits.jl:86-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The goal of this function is to return a type of greater "size" and less "complexity" than
# both `t` or `c` over the lattice defined by `sources`, `depth`, and `allowed_tuplelen`.
function _limit_type_size(@nospecialize(t), @nospecialize(c), sources::SimpleVector, depth::Int, allowed_tuplelen::Int)
    @assert isa(t, AnyType) && isa(c, AnyType) "unhandled TypeVar / Vararg"
    if t === c
        return t # quick egal test
    elseif t === Union{}
        return t # easy case
    elseif isa(t, DataType) && isempty(t.parameters)
        return t # fast path: unparameterized are always simple
    else
        ut = unwrap_unionall(t)
        if is_derived_type_from_any(ut, sources, depth)
            return t # t isn't something new
        end
    end
    # peel off (and ignore) wrappers - they contribute no useful information, so we don't need to consider their size
    # first attempt to turn `c` into a type that contributes meaningful information
    # by peeling off meaningless non-matching wrappers of comparison one at a time
    # then unwrap `t`
    # NOTE that `TypeVar` / `Vararg` are handled separately to catch the logic errors
    if isa(c, UnionAll)
        return __limit_type_size(t, c.body, sources, depth, allowed_tuplelen)::AnyType
    end
    if isa(t, UnionAll)
        tbody = __limit_type_size(t.body, c, sources, depth, allowed_tuplelen)
        tbody === t.body && return t
        return UnionAll(t.var, tbody)::AnyType
    elseif isa(t, Union)
        if isa(c, Union)
            a = __limit_type_size(t.a, c.a, sources, depth, allowed_tuplelen)
            b = __limit_type_size(t.b, c.b, sources, depth, allowed_tuplelen)
            return Union{a, b}
        end
    elseif isType(t)
        # Type is fairly important, so do not widen it as fast as other types if avoidable
        # (this branch also covers `TypeEgal`, whose `Type{...}` widenings are supertypes)
        tt = type_parameter(t)
        ttu = unwrap_unionall(tt) # TODO: use a helper that preserves nested Type structure after #50692 is fixed
        # must forbid nesting through this if we detect that potentially occurring
        # we already know !is_derived_type_from_any so refuse to recurse here
        if isType(ttu)
            return Type{<:Type}
        elseif !isa(ttu, DataType)
            return Type
        end
        # try to peek into c to get a comparison object, but if we can't perhaps t is already simple enough on its own
        if isType(c)
            ct = type_parameter(c)
        else
            ct = Union{}
        end
        Qt = __limit_type_size(tt, ct, sources, depth + 1, 0)
        Qt === tt && return t
        Qt === Any && return Type
        # Can't form Type{<:Qt} just yet, without first make sure we limited the depth
        # enough, since this moves Qt outside of Type for is_derived_type_from_any
        Qt = __limit_type_size(tt, ct, sources, depth + 2, 0)
        Qt === Any && return Type
        return Type{<:Qt}
    elseif isa(t, DataType)
        if isa(c, DataType)
            tP = t.parameters
            cP = c.parameters
            if t.name === c.name && !isempty(cP)
                if t.name === Tuple.name
                    # for covariant datatypes (Tuple),
                    # apply type-size limit element-wise
                    ltP = length(tP)
                    lcP = length(cP)
                    np = min(ltP, max(lcP, allowed_tuplelen))
                    Q = Any[ tP[i] for i in 1:np ]
                    if ltP > np
                        # combine tp[np:end] into tP[np] using Vararg
                        Q[np] = tuple_tail_elem(fallback_lattice, Bottom, Any[ tP[i] for i in np:ltP ])
                    end
                    for i = 1:np
                        # now apply limit element-wise to Q
                        # padding out the comparison as needed to allowed_tuplelen elements
                        if i <= lcP
                            cPi = cP[i]
                        elseif isvarargtype(cP[lcP])
                            cPi = cP[lcP]
                        else
                            cPi = Any
                        end
                        Q[i] = __limit_type_size(Q[i], cPi, sources, depth + 1, 0)
                    end
                    return Tuple{Q...}
                end
            end
        end
        if allowed_tuplelen < 1 && t.name === Tuple.name
            # forbid nesting Tuple{Tuple{Tuple...}} through this
            return Any
        end
        widert = t.name.wrapper
        if !(t <: widert) # XXX: we should call has_free_typevars(t) here, but usually t does not have those wrappers by the time it got here
            # This can happen when a typevar has bounds too wide for its context, e.g.
            # `Complex{T} where T` is not a subtype of `Complex`. In that case widen even
            # faster to something safe to ensure the result is a supertype of the input.
            return Any
        end
        return widert
    end
    return Any
end
```
-/
def limitTypeSize_ (n : Nat) (E : CEnv) (tmerge : LElt → LElt → CM LElt) (t c : Val)
    (sources : List Val) (depth allowedTuplelen : Int) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if !(t.isType && c.isType) then
      jlThrow "AssertionError" "unhandled TypeVar / Vararg"
    if ← egal n E t c then
      return t
    else if t == .bottom then
      return t
    else if t.isDatatype && t.params.isEmpty then
      return t
    else
      let ut := unwrapUnionall t
      if ← isDerivedTypeFromAny n E ut sources depth then
        return t
    if let .unionall _ _ _ _ cbody := c then
      let r ← limitTypeSize__ n E tmerge t cbody sources depth allowedTuplelen
      if !r.isType then jlThrow "TypeError" "typeassert AnyType"
      return r
    match t with
    | .unionall _ _ _ _ tbody =>
      let tbody' ← limitTypeSize__ n E tmerge tbody c sources depth allowedTuplelen
      if ← egal n E tbody' tbody then return t
      let r ← jlUnionAll n E t.uaVar tbody'
      if !r.isType then jlThrow "TypeError" "typeassert AnyType"
      return r
    | .union ta tb =>
      if let .union ca cb := c then
        let a ← limitTypeSize__ n E tmerge ta ca sources depth allowedTuplelen
        let b ← limitTypeSize__ n E tmerge tb cb sources depth allowedTuplelen
        return ← jlUnion n E [a, b]
      return anyType
    | _ =>
    if isType t then
      -- Type is fairly important, so do not widen it as fast as other types if avoidable
      let tt ← typeParameter t
      let ttu := unwrapUnionall tt
      if isType ttu then
        return ← typeLowerWrap n E typeTypeVal limitTypeVarNameType
      else if !ttu.isDatatype then
        return typeTypeVal
      let ct ← if isType c then typeParameter c else pure .bottom
      let Qt ← limitTypeSize__ n E tmerge tt ct sources (depth + 1) 0
      if ← egal n E Qt tt then return t
      if Qt == anyType then return typeTypeVal
      let Qt ← limitTypeSize__ n E tmerge tt ct sources (depth + 2) 0
      if Qt == anyType then return typeTypeVal
      return ← typeLowerWrap n E Qt
    else if let .datatype tname tP := t then
      if let .datatype cname cP := c then
        if tname == cname && !cP.isEmpty then
          if tname == tupleName then
            -- for covariant datatypes (Tuple), apply type-size limit element-wise
            let ltP := tP.length
            let lcP := cP.length
            let np := min (ltP : Int) (max (lcP : Int) allowedTuplelen) |>.toNat
            let mut Q : Array Val := (tP.take np).toArray
            if ltP > np then
              -- combine tp[np:end] into tP[np] using Vararg
              Q := Q.set! (np - 1) (← tupleTailElem n E tmerge (.ty .bottom) (tP.drop (np - 1)))
            for i in [1:np+1] do
              let cPi :=
                if i ≤ lcP then cP[i - 1]!
                else if isvarargtype cP[lcP - 1]! then cP[lcP - 1]!
                else anyType
              Q := Q.set! (i - 1) (← limitTypeSize__ n E tmerge Q[i - 1]! cPi sources (depth + 1) 0)
            return ← jlTuple n E Q.toList
      if allowedTuplelen < 1 && tname == tupleName then
        -- forbid nesting Tuple{Tuple{Tuple...}} through this
        return anyType
      let widert := (← E.types.typename tname).wrapper
      if !(← issub n E t widert) then
        return anyType
      return widert
    return anyType

/-- `__limit_type_size(t, c, sources, depth, allowed_tuplelen)`

Julia source: Compiler/src/typelimits.jl:194-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# helper function of `_limit_type_size`, which has the right to take and return `TypeVar` / `Vararg`
function __limit_type_size(@nospecialize(t), @nospecialize(c), sources::SimpleVector, depth::Int, allowed_tuplelen::Int)
    isa(t, SimpleVector) && (t = t[1])
    isa(c, SimpleVector) && (c = c[1])
    cN = 0
    if isvarargtype(c) # Tuple{Vararg{T}} --> Tuple{T} is OK
        isdefined(c, :N) && (cN = c.N)
        c = unwrapva(c)
    end
    if isa(c, TypeVar)
        if isa(t, TypeVar) && t.ub === c.ub && (t.lb === Union{} || t.lb === c.lb)
            return t # it's ok to change the name, or widen `lb` to Union{}, so we can handle this immediately here
        end
        return __limit_type_size(t, c.ub, sources, depth, allowed_tuplelen)
    elseif isa(t, TypeVar)
        # don't have a matching TypeVar in comparison, so we keep just the upper bound
        return __limit_type_size(t.ub, c, sources, depth, allowed_tuplelen)
    elseif isvarargtype(t)
        # Tuple{Vararg{T,N}} --> Tuple{Vararg{S,M}} is OK
        # Tuple{T} --> Tuple{Vararg{T}} is OK
        # but S must be more limited than T, and must not introduce a new number for M
        VaT = __limit_type_size(unwrapva(t), c, sources, depth + 1, 0)
        if isdefined(t, :N)
            tN = t.N
            if isa(tN, TypeVar) || tN === cN
                return Vararg{VaT, tN}
            end
        end
        return Vararg{VaT}
    else
        return _limit_type_size(t, c, sources, depth, allowed_tuplelen)
    end
end
```
No `SimpleVector` reaches these functions from the modelled callers. -/
def limitTypeSize__ (n : Nat) (E : CEnv) (tmerge : LElt → LElt → CM LElt) (t c : Val)
    (sources : List Val) (depth allowedTuplelen : Int) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut cN : Val := .long 0
    let mut c := c
    if isvarargtype c then
      if let some N := c.varargN? then cN := N
      c := unwrapva c
    if let .typevar _ _ clb cub := c then
      if let .typevar _ _ tlb tub := t then
        if (← egal n E tub cub) && (tlb == .bottom || (← egal n E tlb clb)) then
          return t
      return ← limitTypeSize__ n E tmerge t cub sources depth allowedTuplelen
    else if let .typevar _ _ _ tub := t then
      return ← limitTypeSize__ n E tmerge tub c sources depth allowedTuplelen
    else if let .vararg _ tN := t then
      let VaT ← limitTypeSize__ n E tmerge (unwrapva t) c sources (depth + 1) 0
      if let some tN := tN then
        if tN.isTypevar || (← egal n E tN cN) then
          return ← jlVararg n E VaT (some tN)
      return ← jlVararg n E VaT
    else
      return ← limitTypeSize_ n E tmerge t c sources depth allowedTuplelen
end

/-- `type_more_complex(t, c, sources, depth, tupledepth, allowed_tuplelen)`

Julia source: Compiler/src/typelimits.jl:228-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function type_more_complex(@nospecialize(t), @nospecialize(c), sources::SimpleVector, depth::Int, tupledepth::Int, allowed_tuplelen::Int)
    # detect cases where the comparison is trivial
    if t === c
        return false
    elseif t === Union{}
        return false # Bottom is as simple as they come
    elseif isa(t, DataType) && isempty(t.parameters)
        return false # fastpath: unparameterized types are always finite
    elseif is_derived_type_from_any(unwrap_unionall(t), sources, depth)
        return false # t isn't something new
    end
    # peel off wrappers
    isvarargtype(t) && (t = unwrapva(t))
    isvarargtype(c) && (c = unwrapva(c))
    if isa(c, UnionAll)
        # allow wrapping type with fewer UnionAlls than comparison only if in a covariant context
        if !isa(t, UnionAll) && tupledepth == 0
            return true
        end
        c = unwrap_unionall(c)
    end
    if isa(t, UnionAll)
        t = unwrap_unionall(t)
    end
    # rules for various comparison types
    if isa(c, TypeVar)
        tupledepth = 1
        if isa(t, TypeVar)
            return !(t.lb === Union{} || t.lb === c.lb) || # simplify lb towards Union{}
                   type_more_complex(t.ub, c.ub, sources, depth + 1, tupledepth, 0)
        end
        c.lb === Union{} || return true
        return type_more_complex(t, c.ub, sources, depth, tupledepth, 0)
    elseif isa(c, Union)
        if isa(t, Union)
            return type_more_complex(t.a, c.a, sources, depth, tupledepth, allowed_tuplelen) ||
                   type_more_complex(t.b, c.b, sources, depth, tupledepth, allowed_tuplelen)
        end
        return type_more_complex(t, c.a, sources, depth, tupledepth, allowed_tuplelen) &&
               type_more_complex(t, c.b, sources, depth, tupledepth, allowed_tuplelen)
    elseif isa(t, Int) && isa(c, Int)
        return t !== 1 && !(0 <= t < c) # alternatively, could use !(abs(t) <= abs(c) || abs(t) < n) for some n
    end
    if isType(t)
        # Type is fairly important, so do not widen it as fast as other types if avoidable
        tt = type_parameter(t)
        # ttu = unwrap_unionall(tt) # TODO: use a helper that preserves nested Type structure after #50692 is fixed
        if isType(c)
            ct = type_parameter(c)
        else
            ct = Union{}
            tupledepth == 0 && return true # cannot allow nesting
        end
        # allow creating variation within a nested Type, but not very deep
        if tupledepth > 1
            tupledepth = 1
        else
            tupledepth = 0
        end
        return type_more_complex(tt, ct, sources, depth + 1, tupledepth, 0)
    end
    # base case for data types
    if isa(t, DataType)
        tP = t.parameters
        if isa(c, DataType) && t.name === c.name
            cP = c.parameters
            length(cP) < length(tP) && return true
            isempty(tP) && return false
            length(cP) > length(tP) && !isvarargtype(tP[end]) && depth == 1 && return false # is this line necessary?
            ntail = length(cP) - length(tP) # assume parameters were dropped from the tuple head
            # allow creating variation within a nested tuple, but only so deep
            if t.name === Tuple.name && tupledepth > 0
                tupledepth -= 1
            else
                tupledepth = 0
            end
            for i = 1:length(tP)
                tPi = tP[i]
                cPi = cP[i + ntail]
                type_more_complex(tPi, cPi, sources, depth + 1, tupledepth, 0) && return true
            end
            return false
        end
    end
    return true
end
```
-/
def typeMoreComplex (n : Nat) (E : CEnv) (t c : Val) (sources : List Val)
    (depth tupledepth allowedTuplelen : Int) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    -- detect cases where the comparison is trivial
    if ← egal n E t c then
      return false
    else if t == .bottom then
      return false
    else if t.isDatatype && t.params.isEmpty then
      return false
    else if ← isDerivedTypeFromAny n E (unwrapUnionall t) sources depth then
      return false
    -- peel off wrappers
    let mut t := if isvarargtype t then unwrapva t else t
    let mut c := if isvarargtype c then unwrapva c else c
    let mut tupledepth := tupledepth
    if c.isUnionall then
      if !t.isUnionall && tupledepth == 0 then
        return true
      c := unwrapUnionall c
    if t.isUnionall then
      t := unwrapUnionall t
    -- rules for various comparison types
    if let .typevar _ _ clb cub := c then
      tupledepth := 1
      if let .typevar _ _ tlb tub := t then
        if !(tlb == .bottom || (← egal n E tlb clb)) then return true
        return ← typeMoreComplex n E tub cub sources (depth + 1) tupledepth 0
      if clb != .bottom then return true
      return ← typeMoreComplex n E t cub sources depth tupledepth 0
    else if let .union ca cb := c then
      if let .union ta tb := t then
        if ← typeMoreComplex n E ta ca sources depth tupledepth allowedTuplelen then return true
        return ← typeMoreComplex n E tb cb sources depth tupledepth allowedTuplelen
      if !(← typeMoreComplex n E t ca sources depth tupledepth allowedTuplelen) then return false
      return ← typeMoreComplex n E t cb sources depth tupledepth allowedTuplelen
    else if let (.long ti, .long ci) := (t, c) then
      return ti != 1 && !(0 ≤ ti && ti < ci)
    if isType t then
      let tt ← typeParameter t
      let mut ct := Val.bottom
      if isType c then
        ct ← typeParameter c
      else
        if tupledepth == 0 then return true -- cannot allow nesting
      -- allow creating variation within a nested Type, but not very deep
      tupledepth := if tupledepth > 1 then 1 else 0
      return ← typeMoreComplex n E tt ct sources (depth + 1) tupledepth 0
    -- base case for data types
    if let .datatype tname tP := t then
      if let .datatype cname cP := c then
        if tname == cname then
          if cP.length < tP.length then return true
          if tP.isEmpty then return false
          if cP.length > tP.length && !isvarargtype tP.getLast! && depth == 1 then return false
          let ntail := cP.length - tP.length
          -- allow creating variation within a nested tuple, but only so deep
          tupledepth := if tname == tupleName && tupledepth > 0 then tupledepth - 1 else 0
          for i in [1:tP.length+1] do
            let tPi := tP[i - 1]!
            let cPi := cP[i + ntail - 1]!
            if ← typeMoreComplex n E tPi cPi sources (depth + 1) tupledepth 0 then return true
          return false
    return true

/-- `limit_type_size(t, compare, source, allowed_tupledepth, allowed_tuplelen)`

Julia source: Compiler/src/typelimits.jl:14-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# limit the complexity of type `t` to be simpler than the comparison type `compare`
# no new values may be introduced, so the parameter `source` encodes the set of all values already present
# the outermost tuple type is permitted to have up to `allowed_tuplelen` parameters
function limit_type_size(@nospecialize(t), @nospecialize(compare), @nospecialize(source), allowed_tupledepth::Int, allowed_tuplelen::Int)
    source = svec(unwrap_unionall(compare), unwrap_unionall(source))
    source[1] === source[2] && (source = svec(source[1]))
    type_more_complex(t, compare, source, 1, allowed_tupledepth, allowed_tuplelen) || return t
    r = _limit_type_size(t, compare, source, 1, allowed_tuplelen)
    #@assert t <: r # this may fail if t contains a typevar in invariant and multiple times
        # in covariant position and r looses the occurrence in invariant position (see #36407)
    if !(t <: r) # ideally, this should never happen
        # widen to minimum complexity to obtain a valid result
        r = _limit_type_size(t, Any, source, 1, allowed_tuplelen)
        t <: r || (r = Any) # final escape hatch
    end
    #@assert r === _limit_type_size(r, t, source) # this monotonicity constraint is slightly stronger than actually required,
      # since we only actually need to demonstrate that repeated application would reach a fixed point,
      #not that it is already at the fixed point
    return r
end
```
-/
def limitTypeSize (n : Nat) (E : CEnv) (tmerge : LElt → LElt → CM LElt) (t compare source : Val)
    (allowedTupledepth allowedTuplelen : Int) : CM Val := do
  let mut sources := [unwrapUnionall compare, unwrapUnionall source]
  if ← egal n E sources[0]! sources[1]! then sources := [sources[0]!]
  if !(← typeMoreComplex n E t compare sources 1 allowedTupledepth allowedTuplelen) then
    return t
  let mut r ← limitTypeSize_ n E tmerge t compare sources 1 allowedTuplelen
  if !(← issub n E t r) then -- ideally, this should never happen
    -- widen to minimum complexity to obtain a valid result
    r ← limitTypeSize_ n E tmerge t anyType sources 1 allowedTuplelen
    if !(← issub n E t r) then r := anyType -- final escape hatch
  return r

/-! ## `getfield_tfunc` on a known field index -/

def unwrapvaElt : LElt → LElt
  | .ty t => .ty (unwrapva t)
  | x => x

/-- `getfield_tfunc(𝕃, s00, Const(i))` on the inputs `tmerge_partial_struct` and
`issimplertype` give it. Other inputs report `unmodelled`.

Julia source: Compiler/src/tfuncs.jl:1183-1287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function getfield_tfunc(𝕃::AbstractLattice, s00, name)
    _getfield_tfunc(𝕃, s00, name, false)
end
...
function _getfield_tfunc_const(@nospecialize(sv), name::Const)
    nv = _getfield_fieldindex(typeof(sv), name)
    nv === nothing && return Bottom
    # relocated pointers change between processes, so their value can't be folded
    is_relocatable_ptr_field(Const(sv), name) && return nothing
    ...
    if !isa(sv, Module) && isconst(typeof(sv), nv)
        if isdefined(sv, nv)
            return Const(getfield(sv, nv))
        end
        return Bottom
    end
    return nothing
end

@nospecs function _getfield_tfunc(𝕃::InferenceLattice, s00, name, setfield::Bool)
    if isa(s00, LimitedAccuracy)
        # This will error, but it's better than duplicating the error here
        s00 = widenconst(s00)
    end
    return _getfield_tfunc(widenlattice(𝕃), s00, name, setfield)
end

@nospecs function _getfield_tfunc(𝕃::AnyConditionalsLattice, s00, name, setfield::Bool)
    if isa(s00, AnyConditional)
        return Bottom # Bool has no fields
    end
    return _getfield_tfunc(widenlattice(𝕃), s00, name, setfield)
end

@nospecs function _getfield_tfunc(𝕃::AnyMustAliasesLattice, s00, name, setfield::Bool)
    return _getfield_tfunc(widenlattice(𝕃), widenmustalias(s00), widenmustalias(name), setfield)
end

@nospecs function _getfield_tfunc(𝕃::PartialsLattice, s00, name, setfield::Bool)
    if isa(s00, PartialStruct)
        s = widenconst(s00)
        sty = unwrap_unionall(s)::DataType
        if isa(name, Const)
            nv = _getfield_fieldindex(sty, name)
            if isa(nv, Int)
                if nv < 1
                    return Bottom
                elseif nv ≤ length(s00.fields)
                    setfield && isconst(sty, nv) && return Bottom
                    return unwrapva(s00.fields[nv])
                end
            end
        end
        s00 = s
    elseif isa(s00, PartialTask)
        ...
        s00 = Task
    end
    return _getfield_tfunc(widenlattice(𝕃), s00, name, setfield)
end

@nospecs function _getfield_tfunc(𝕃::ConstsLattice, s00, name, setfield::Bool)
    if isa(s00, Const)
        sv = s00.val
        if isa(name, Const)
            nv = name.val
            if isa(sv, Module)
                setfield && return Bottom
                if isa(nv, Symbol)
                    # In ordinary inference, this case is intercepted early and
                    # re-routed to `getglobal`.
                    return Any
                end
                return Bottom
            end
            r = _getfield_tfunc_const(sv, name)
            r !== nothing && return r
        end
        s00 = widenconst(s00)
    end
    return _getfield_tfunc(widenlattice(𝕃), s00, name, setfield)
end
```
`is_relocatable_ptr_field` (`tfuncs.jl:2905`) is false for values that are not `TypeName`s or
`DataType`s; type-valued and mutable `Const`s and the `JLTypeLattice` method report
`unmodelled`. -/
def getfieldTfuncIdx (n : Nat) (E : CEnv) (L : Lattice) (s00 : LElt) (i : Nat) : CM LElt :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match L with
    | .inference p =>
      let mut s00 := s00
      if s00.isLimited then
        -- This will error, but it's better than duplicating the error here
        s00 := .ty (← widenconst n E s00)
      getfieldTfuncIdx n E p s00 i
    | .conditionals p | .interConditionals p =>
      if s00.isAnyConditional then return .ty .bottom
      getfieldTfuncIdx n E p s00 i
    | .mustAliases p | .interMustAliases p =>
      getfieldTfuncIdx n E p (← widenmustalias s00) i
    | .partials p =>
      let mut s00 := s00
      if let .partialStruct typ _ fields _ _ := s00 then
        if !(unwrapUnionall typ).isDatatype then jlThrow "TypeError" "typeassert DataType"
        if i < 1 then return .ty .bottom
        else if i ≤ fields.length then return unwrapvaElt fields[i - 1]!
        s00 := .ty typ
      else if s00.isPartialTask then
        s00 := .ty taskType
      getfieldTfuncIdx n E p s00 i
    | .consts =>
      if let .const sv := s00 then
        if sv.isModule then return .ty .bottom
        if sv.isType || sv.isTypevar then unmodelled "getfield_tfunc on a type-valued Const"
        if ← ismutable E sv then unmodelled "getfield_tfunc on a mutable Const"
        if isdefinedField sv i then return .const (← getfieldVal sv i)
        return .ty .bottom
      getfieldTfuncIdx n E .jlType s00 i
    | .jlType => unmodelled "getfield_tfunc(::JLTypeLattice, ...)"

/-! ## Lattice element constructors -/

/-- `n_initialized(t::Const)` and `n_initialized(pstruct::PartialStruct)`
(`Compiler/src/typelimits.jl:330-338`), as defined in `typelattice.lean`. -/
def nInitialized (E : CEnv) : LElt → CM Nat
  | .const v => nInitializedConst E v
  | .partialStruct _ us _ _ _ => pure (nInitializedPartialStruct us)
  | _ => jlThrow "MethodError" "n_initialized"

/-- `Core.PartialStruct(𝕃, typ, undefs, fields)` and the validating `Core.PartialStruct(typ,
undefs, fields)` it calls.

Julia source: Compiler/src/typelattice.jl:830-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Core.PartialStruct(::AbstractLattice, @nospecialize(typ::Type), undefs::Vector{Union{Nothing,Bool}}, fields::Vector{Any})
    for i = 1:length(fields)
        assert_nested_slotwrapper(fields[i])
    end
    return PartialStruct(typ, undefs, fields)
end
```

Julia source: base/coreir.jl:50-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Core.PartialStruct(typ::Type, undefs::Vector{Union{Nothing,Bool}}, fields::Vector{Any})
    fldcnt = fieldcount_noerror(typ)
    if fldcnt !== nothing
        @assert fldcnt == length(fields)
    else
        @assert typ <: Tuple && isvarargtype(fields[end])
        @assert datatype_min_ninitialized(typ) == length(fields) - 1
        @assert undefs[end] === nothing
    end
    @assert length(fields) == length(undefs)
    for i = 1:length(fields)
        if fields[i] === Union{}
            @assert undefs[i] === true "`Union{}` typed field should be strictly undefined"
        end
    end
    return Core._PartialStruct(typ, undefs, fields)
end
```
-/
def mkPartialStruct (n : Nat) (E : CEnv) (typ : Val) (undefs : List (Option Bool))
    (fields : List LElt) : CM LElt := do
  for f in fields do
    let _ ← assertNestedSlotwrapper f
  if !typ.isType then jlThrow "MethodError" "PartialStruct(typ::Type, ...)"
  match ← fieldcountNoerror E typ with
  | some fldcnt =>
    if fldcnt != fields.length then jlThrow "AssertionError" "fldcnt == length(fields)"
  | none =>
    if !(← issub n E typ anytupleType) || !(fields.getLast?.map LElt.isVarargElt).getD false then
      if fields.isEmpty && (← issub n E typ anytupleType) then jlThrow "BoundsError" "fields[end]"
      jlThrow "AssertionError" "typ <: Tuple && isvarargtype(fields[end])"
    if (← datatypeMinNinitialized E typ) != fields.length - 1 then
      jlThrow "AssertionError" "datatype_min_ninitialized(typ) == length(fields) - 1"
    if undefs.getLast? != some none then
      if undefs.isEmpty then jlThrow "BoundsError" "undefs[end]"
      jlThrow "AssertionError" "undefs[end] === nothing"
  if fields.length != undefs.length then jlThrow "AssertionError" "length(fields) == length(undefs)"
  for (f, u) in fields.zip undefs do
    if f.isBottom && u != some true then
      jlThrow "AssertionError" "`Union{}` typed field should be strictly undefined"
  return .partialStruct typ undefs fields (← freshId) (← freshId)

/-! ## `issimplertype` and the fast path -/

/-- `issimplertype(𝕃, typea, typeb)`

Julia source: Compiler/src/typelimits.jl:340-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A simplified type_more_complex query over the extended lattice
# (assumes typeb ⊑ typea)
@nospecializeinfer function issimplertype(𝕃::AbstractLattice, @nospecialize(typea), @nospecialize(typeb))
    @assert !isa(typea, LimitedAccuracy) && !isa(typeb, LimitedAccuracy) "LimitedAccuracy not supported by simplertype lattice" # n.b. the caller was supposed to handle these
    typea === typeb && return true
    if typea isa PartialStruct
        aty = widenconst(typea)
        issimplertype(𝕃, aty, widenconst(typeb)) || return false
        if typeb isa Const || typeb isa PartialStruct
            @assert n_initialized(typea) ≤ n_initialized(typeb) "typeb ⊑ typea is assumed"
        elseif typeb isa PartialStruct
            @assert n_initialized(typea) ≤ n_initialized(typeb) &&
                all(b === nothing || a === b for (a, b) in zip(_getundefs(typea), _getundefs(typeb))) "typeb ⊑ typea is assumed"
        else
            return false
        end
        for i = 1:length(typea.fields)
            ai = unwrapva(typea.fields[i])
            bi = fieldtype(aty, i)
            is_lattice_equal(𝕃, ai, bi) && continue
            tni = _typename(widenconst(ai))
            if tni isa Const
                bi = (tni.val::Core.TypeName).wrapper
                is_lattice_equal(𝕃, ai, bi) && continue
            end
            bi = getfield_tfunc(𝕃, typeb, Const(i))
            is_lattice_equal(𝕃, ai, bi) && continue
            # It is not enough for ai to be simpler than bi: it must exactly equal
            # (for this, an invariant struct field, by contrast to
            # type_more_complex above which handles covariant tuples).
            return false
        end
    elseif typea isa Type
        return issimpleenoughtype(typea)
    # elseif typea isa Const # fall-through to true is good
    elseif typea isa Conditional # follow issubconditional query
        typeb isa Const && return true
        typeb isa Conditional || return false
        is_same_conditionals(typea, typeb) || return false
        issimplertype(𝕃, typea.thentype, typeb.thentype) || return false
        issimplertype(𝕃, typea.elsetype, typeb.elsetype) || return false
    elseif typea isa InterConditional # ibid
        typeb isa Const && return true
        typeb isa InterConditional || return false
        is_same_conditionals(typea, typeb) || return false
        issimplertype(𝕃, typea.thentype, typeb.thentype) || return false
        issimplertype(𝕃, typea.elsetype, typeb.elsetype) || return false
    elseif typea isa MustAlias
        typeb isa MustAlias || return false
        issubalias(typeb, typea) || return false
        issimplertype(𝕃, typea.vartyp, typeb.vartyp) || return false
        issimplertype(𝕃, typea.fldtyp, typeb.fldtyp) || return false
    elseif typea isa InterMustAlias
        typeb isa InterMustAlias || return false
        issubalias(typeb, typea) || return false
        issimplertype(𝕃, typea.vartyp, typeb.vartyp) || return false
        issimplertype(𝕃, typea.fldtyp, typeb.fldtyp) || return false
    elseif typea isa PartialOpaque
        # TODO
        typeb isa PartialOpaque || return false
        aty = widenconst(typea)
        bty = widenconst(typeb)
        if typea.source === typeb.source && typea.parent === typeb.parent && aty == bty && typea.env == typeb.env
            return false
        end
        return false
    elseif typea isa PartialTask
        typeb isa PartialTask || return false
        return issimplertype(𝕃, typea.fetch_type, typeb.fetch_type)
    end
    return true
end
```
The `elseif typeb isa PartialStruct` branch is unreachable (the branch before it already takes
every `PartialStruct`). The `PartialOpaque` branch returns `false` whatever its comparisons give,
and they cannot throw, so the model returns `false` directly. -/
def issimplertype (n : Nat) (E : CEnv) (L : Lattice) (typea typeb : LElt) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if typea.isLimited || typeb.isLimited then
      jlThrow "AssertionError" "LimitedAccuracy not supported by simplertype lattice"
    if ← eltEgal n E typea typeb then return true
    match typea with
    | .partialStruct atyp _ afields _ _ =>
      let aty := atyp
      if !(← issimplertype n E L (.ty aty) (.ty (← widenconst n E typeb))) then return false
      if typeb.isConst || typeb.isPartialStruct then
        if !(decide ((← nInitialized E typea) ≤ (← nInitialized E typeb))) then
          jlThrow "AssertionError" "typeb ⊑ typea is assumed"
      else
        return false
      for i in [1:afields.length+1] do
        let ai := unwrapvaElt afields[i - 1]!
        let bi ← fieldtypeIdx E aty i
        if ← isLatticeEqual n E L ai (.ty bi) then continue
        let tni := typenameT (← widenconst n E ai)
        if let .const tname := tni then
          let bi := (← E.types.typename tname).wrapper
          if ← isLatticeEqual n E L ai (.ty bi) then continue
        let bi ← getfieldTfuncIdx n E L typeb i
        if ← isLatticeEqual n E L ai bi then continue
        -- It is not enough for ai to be simpler than bi: it must exactly equal
        return false
      return true
    | .ty t =>
      if t.isType then return ← issimpleenoughtype n E t
      return true
    | .conditional _ _ atp ae _ =>
      if typeb.isConst then return true
      let .conditional _ _ bt be _ := typeb | return false
      if !(← isSameConditionals typea typeb) then return false
      if !(← issimplertype n E L atp bt) then return false
      if !(← issimplertype n E L ae be) then return false
      return true
    | .interConditional _ atp ae =>
      if typeb.isConst then return true
      let .interConditional _ bt be := typeb | return false
      if !(← isSameConditionals typea typeb) then return false
      if !(← issimplertype n E L atp bt) then return false
      if !(← issimplertype n E L ae be) then return false
      return true
    | .mustAlias _ _ av _ af =>
      let .mustAlias _ _ bv _ bf := typeb | return false
      if !(← issubalias (sqsub n E) typeb typea) then return false
      if !(← issimplertype n E L av bv) then return false
      if !(← issimplertype n E L af bf) then return false
      return true
    | .interMustAlias _ av _ af =>
      let .interMustAlias _ bv _ bf := typeb | return false
      if !(← issubalias (sqsub n E) typeb typea) then return false
      if !(← issimplertype n E L av bv) then return false
      if !(← issimplertype n E L af bf) then return false
      return true
    | .partialOpaque .. =>
      return false
    | .partialTask af =>
      let .partialTask bf := typeb | return false
      issimplertype n E L af bf
    | _ => return true

/-- `tmerge_fast_path(lattice, typea, typeb)`; `none` is `nothing`.

Julia source: Compiler/src/typelimits.jl:413-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function tmerge_fast_path(lattice::AbstractLattice, @nospecialize(typea), @nospecialize(typeb))
    # Fast paths
    typea === Union{} && return typeb
    typeb === Union{} && return typea
    typea === typeb && return typea

    suba = ⊑(lattice, typea, typeb)
    suba && issimplertype(lattice, typeb, typea) && return typeb
    subb = ⊑(lattice, typeb, typea)
    suba && subb && return typea
    subb && issimplertype(lattice, typea, typeb) && return typea
    return nothing
end
```
-/
def tmergeFastPath (n : Nat) (E : CEnv) (L : Lattice) (typea typeb : LElt) : CM (Option LElt) := do
  if typea.isBottom then return some typeb
  if typeb.isBottom then return some typea
  if ← eltEgal n E typea typeb then return some typea
  let suba ← sqsub n E L typea typeb
  if suba then
    if ← issimplertype n E L typeb typea then return some typeb
  let subb ← sqsub n E L typeb typea
  if suba && subb then return some typea
  if subb then
    if ← issimplertype n E L typea typeb then return some typea
  return none

/-! ## `LimitedAccuracy` causes -/

/-- `union_causes(causesa, causesb)` and `merge_causes(causesa, causesb)`; a causes set is its
elements and its identity.

Julia source: Compiler/src/typelimits.jl:427-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function union_causes(causesa::IdSet{InferenceState}, causesb::IdSet{InferenceState})
    if causesa ⊆ causesb
        return causesb
    elseif causesb ⊆ causesa
        return causesa
    else
        return union!(copy(causesa), causesb)
    end
end

function merge_causes(causesa::IdSet{InferenceState}, causesb::IdSet{InferenceState})
    # TODO: When lattice elements are equal, we're allowed to discard one or the
    # other set, but we'll need to come up with a consistent rule. For now, we
    # just check the length, but other heuristics may be applicable.
    if length(causesa) < length(causesb)
        return causesa
    elseif length(causesb) < length(causesa)
        return causesb
    else
        return union!(copy(causesa), causesb)
    end
end
```
-/
def unionCauses (a b : List ObjId × ObjId) : CM (List ObjId × ObjId) := do
  if a.1.all b.1.contains then return b
  if b.1.all a.1.contains then return a
  let (c, cid) ← copyIdSet a.1
  return (idsetUnion c b.1, cid)

def mergeCauses (a b : List ObjId × ObjId) : CM (List ObjId × ObjId) := do
  if a.1.length < b.1.length then return a
  if b.1.length < a.1.length then return b
  let (c, cid) ← copyIdSet a.1
  return (idsetUnion c b.1, cid)

/-! ## Types-only slow path -/

/-- `datatype_super` up the chain until the type name is `name`. -/
def superUntilName (n : Nat) (E : CEnv) (u : Val) (name : String) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if u.name? == some name then return u
    if u == anyType then jlThrow "TypeError" "datatype_super"
    superUntilName n E (← supertypeDT n E u) name

/-- The number of `datatype_super` steps from `a` to `Any`; `aname` is reported if met. -/
def superHeight (n : Nat) (E : CEnv) (a : Val) (stopAt : Option String) : CM (Nat ⊕ Unit) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if a == anyType then return .inl 0
    if let some nm := stopAt then
      if a.name? == some nm then return .inr ()
    match ← superHeight n E (← supertypeDT n E a) stopAt with
    | .inl h => return .inl (h + 1)
    | .inr () => return .inr ()

def superN (n : Nat) (E : CEnv) (a : Val) : Nat → CM Val
  | 0 => pure a
  | k + 1 => do superN n E (← supertypeDT n E a) k

/-- `tname_intersect(aname, bname)`; a type name is its name string, `none` is `nothing`.

Julia source: Compiler/src/typelimits.jl:791-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer @noinline function tname_intersect(aname::Core.TypeName, bname::Core.TypeName)
    aname === bname && return aname
    if !isabstracttype(aname.wrapper) && !isabstracttype(bname.wrapper)
        return nothing # fast path
    end
    Any.name === aname && return aname
    a = unwrap_unionall(aname.wrapper)
    heighta = 0
    while a !== Any
        heighta += 1
        a = datatype_super(a)
    end
    b = unwrap_unionall(bname.wrapper)
    heightb = 0
    while b !== Any
        b.name === aname && return aname
        heightb += 1
        b = datatype_super(b)
    end
    a = unwrap_unionall(aname.wrapper)
    while heighta > heightb
        a = datatype_super(a)
        heighta -= 1
    end
    return a.name === bname ? bname : nothing
end
```
-/
def tnameIntersect (n : Nat) (E : CEnv) (aname bname : String) : CM (Option String) := do
  if aname == bname then return some aname
  let awr := (← E.types.typename aname).wrapper
  let bwr := (← E.types.typename bname).wrapper
  if !(← isabstracttype E awr) && !(← isabstracttype E bwr) then
    return none -- fast path
  if aname == anyName then return some aname
  let .inl heighta ← superHeight n E (unwrapUnionall awr) none | return none
  let .inl heightb ← superHeight n E (unwrapUnionall bwr) (some aname) | return some aname
  let mut a := unwrapUnionall awr
  if heighta > heightb then
    a ← superN n E a (heighta - heightb)
  return if a.name? == some bname then some bname else none

/-- `tuplemerge(a, b)`

Julia source: Compiler/src/typelimits.jl:942-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# the inverse of switchtupleunion, with limits on max element union size
function tuplemerge(a::DataType, b::DataType)
    @assert a.name === b.name === Tuple.name "assertion failure"
    ap, bp = a.parameters, b.parameters
    lar = length(ap)::Int
    lbr = length(bp)::Int
    va = lar > 0 && isvarargtype(ap[lar])
    vb = lbr > 0 && isvarargtype(bp[lbr])
    if lar == lbr && !va && !vb
        lt = lar
        vt = false
    else
        lt = 0 # or min(lar - va, lbr - vb)
        vt = true
    end
    # combine the common elements
    p = Vector{Any}(undef, lt + vt)
    for i = 1:lt
        ui = Union{ap[i], bp[i]}
        p[i] = issimpleenoughtupleelem(ui) ? ui : Any
    end
    # merge the remaining tail into a single, simple Tuple{Vararg{T}} (#22120)
    if vt
        tail = Union{}
        for loop_b = (false, true)
            for i = (lt + 1):(loop_b ? lbr : lar)
                ti = unwrapva(loop_b ? bp[i] : ap[i])
                while ti isa TypeVar
                    ti = ti.ub
                end
                # compare (ti <-> tail), (wrapper ti <-> tail), (ti <-> wrapper tail), then (wrapper ti <-> wrapper tail)
                # until we find the first element that contains the other in the pair
                # TODO: this result would be more stable (and more associative and more commutative)
                #   if we either joined all of the element wrappers first into a wide-tail, then picked between that or an exact tail,
                #   or (equivalently?) iteratively took super-types until reaching a common wrapper
                #   e.g. consider the results of `tuplemerge(Tuple{Complex}, Tuple{Number, Int})` and of
                #   `tuplemerge(Tuple{Int}, Tuple{String}, Tuple{Int, String})`
                #   c.f. tname_intersect in the algorithm above
                hasfree = has_free_typevars(ti)
                if hasfree || !(ti <: tail)
                    if !hasfree && tail <: ti
                        tail = ti # widen to ti
                    else
                        uw = unwrap_unionall(tail)
                        if uw isa DataType && tail <: uw.name.wrapper
                            # widen tail to wrapper(tail)
                            tail = uw.name.wrapper
                            if !(ti <: tail)
                                #assert !(tail <: ti)
                                uw = unwrap_unionall(ti)
                                if uw isa DataType && ti <: uw.name.wrapper
                                    # widen ti to wrapper(ti)
                                    ti = uw.name.wrapper
                                    #assert !(ti <: tail)
                                    if tail <: ti
                                        tail = ti
                                    else
                                        tail = Any # couldn't find common super-type
                                    end
                                else
                                    tail = Any # couldn't analyze type
                                end
                            end
                        else
                            tail = Any # couldn't analyze type
                        end
                    end
                end
                tail === Any && return Tuple # short-circuit loops
            end
        end
        @assert !(tail === Union{})
        if !issimpleenoughtupleelem(tail) || tail === Any
            p[lt + 1] = Vararg
            lt == 0 && return Tuple
        else
            p[lt + 1] = Vararg{tail}
        end
    end
    return Tuple{p...}
end
```
-/
def tuplemerge (n : Nat) (E : CEnv) (a b : Val) : CM Val := do
  let (.datatype an ap, .datatype bn bp) := (a, b) | jlThrow "MethodError" "tuplemerge"
  if !(an == bn && bn == tupleName) then jlThrow "AssertionError" "assertion failure"
  let lar := ap.length
  let lbr := bp.length
  let va := lar > 0 && isvarargtype ap[lar - 1]!
  let vb := lbr > 0 && isvarargtype bp[lbr - 1]!
  let (lt, vt) := if lar == lbr && !va && !vb then (lar, false) else (0, true)
  -- combine the common elements
  let mut p : Array Val := #[]
  for i in [1:lt+1] do
    let ui ← jlUnion n E [ap[i - 1]!, bp[i - 1]!]
    p := p.push (if ← issimpleenoughtupleelem n E ui then ui else anyType)
  -- merge the remaining tail into a single, simple Tuple{Vararg{T}} (#22120)
  if vt then
    let mut tail : Val := .bottom
    for loopB in [false, true] do
      for i in [lt + 1:(if loopB then lbr else lar) + 1] do
        let mut ti ← unwraptv n (unwrapva (if loopB then bp[i - 1]! else ap[i - 1]!))
        let hasfree := hasFreeTypevars ti
        let tiSub ← if hasfree then pure true else issub n E ti tail
        if hasfree || !tiSub then
          let tailSub ← if hasfree then pure false else issub n E tail ti
          if !hasfree && tailSub then
            tail := ti -- widen to ti
          else
            let uw := unwrapUnionall tail
            let tailOk ← match uw with
              | .datatype nm _ => do issub n E tail (← E.types.typename nm).wrapper
              | _ => pure false
            if tailOk then
              -- widen tail to wrapper(tail)
              tail := (← E.types.typename uw.name?.get!).wrapper
              if !(← issub n E ti tail) then
                let uw := unwrapUnionall ti
                let tiOk ← match uw with
                  | .datatype nm _ => do issub n E ti (← E.types.typename nm).wrapper
                  | _ => pure false
                if tiOk then
                  -- widen ti to wrapper(ti)
                  ti := (← E.types.typename uw.name?.get!).wrapper
                  if ← issub n E tail ti then
                    tail := ti
                  else
                    tail := anyType -- couldn't find common super-type
                else
                  tail := anyType -- couldn't analyze type
            else
              tail := anyType -- couldn't analyze type
        if tail == anyType then return anytupleType -- short-circuit loops
    if tail == .bottom then jlThrow "AssertionError" "!(tail === Union{})"
    if !(← issimpleenoughtupleelem n E tail) || tail == anyType then
      p := p.push (.vararg none none)
      if lt == 0 then return anytupleType
    else
      p := p.push (← jlVararg n E tail)
  jlTuple n E p.toList

/-- `tmerge_types_slow(typea, typeb)`

Julia source: Compiler/src/typelimits.jl:818-940 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer @noinline function tmerge_types_slow(@nospecialize(typea::AnyType), @nospecialize(typeb::AnyType))
    # collect the list of types from past tmerge calls returning Union
    # and then reduce over that list
    types = Any[]
    _uniontypes(typea, types)
    _uniontypes(typeb, types)
    typenames = Vector{Core.TypeName}(undef, length(types))
    all_datatypes = true
    for i in 1:length(types)
        # check that we will be able to analyze (and simplify) everything
        # bail if everything isn't a well-formed nominal kind
        ti = types[i]
        uw = unwrap_unionall(ti)
        if uw isa DataType
            ti <: uw.name.wrapper || return Any
            typenames[i] = uw.name
        elseif isType(uw)
            typenames[i] = TypeEq.name
            all_datatypes = false
        else
            return Any
        end
    end
    u = Union{types...}
    if issimpleenoughtype(u)
        return u
    end
    all_datatypes || return Any
    # see if any of the union elements have the same TypeName
    # in which case, simplify this tmerge by replacing it with
    # the widest possible version of itself (the wrapper)
    simplify = falses(length(types))
    for i in 1:length(types)
        typenames[i] === Any.name && continue
        ti = types[i]
        for j in (i + 1):length(types)
            typenames[j] === Any.name && continue
            ijname = tname_intersect(typenames[i], typenames[j])
            if !(ijname === nothing)
                tj = types[j]
                if ti <: tj
                    types[i] = Union{}
                    typenames[i] = Any.name
                    simplify[i] = false
                    simplify[j] = true
                    break
                elseif tj <: ti
                    types[j] = Union{}
                    typenames[j] = Any.name
                    simplify[j] = false
                    simplify[i] = true
                else
                    if ijname === Tuple.name
                        # try to widen Tuple slower: make a single non-concrete Tuple containing both
                        # converge the Tuple element-wise if they are the same length
                        # see 4ee2b41552a6bc95465c12ca66146d69b354317b, be59686f7613a2ccfd63491c7b354d0b16a95c05,
                        widen = tuplemerge(unwrap_unionall(ti)::DataType, unwrap_unionall(tj)::DataType)
                        widen = rewrap_unionall(rewrap_unionall(widen, ti), tj)
                        simplify[j] = false
                    else
                        wr = ijname.wrapper
                        uw = unwrap_unionall(wr)::DataType
                        ui = unwrap_unionall(ti)::DataType
                        while ui.name !== ijname
                            ui = datatype_super(ui)
                        end
                        uj = unwrap_unionall(tj)::DataType
                        while uj.name !== ijname
                            uj = datatype_super(uj)
                        end
                        p = Vector{Any}(undef, length(uw.parameters))
                        usep = true
                        widen = wr
                        for k = 1:length(uw.parameters)
                            ui_k = ui.parameters[k]
                            if ui_k === uj.parameters[k] && !has_free_typevars(ui_k)
                                p[k] = ui_k
                                usep = true
                            else
                                p[k] = uw.parameters[k]
                            end
                        end
                        if usep
                            widen = rewrap_unionall(wr{p...}, wr)
                            widen <: wr || (widen = wr) # sometimes there are cross-constraints on wr that we may lose in this process, but that would cause future calls to this to need to return Any, which is undesirable
                        end
                        simplify[j] = !usep
                    end
                    types[i] = Union{}
                    typenames[i] = Any.name
                    simplify[i] = false
                    types[j] = widen
                    typenames[j] = ijname
                    break
                end
            end
        end
    end
    # don't let elements of the union get too big, if the above didn't reduce something enough
    # Specifically widen Tuple{..., Union{lots of stuff}...} to Tuple{..., Any, ...}
    # Don't let Val{<:Val{<:Val}} keep nesting abstract levels either
    for i in 1:length(types)
        simplify[i] || continue
        ti = types[i]
        issimpleenoughtype(ti) && continue
        if typenames[i] === Tuple.name
            # otherwise we need to do a simple version of tuplemerge for one element now
            tip = (unwrap_unionall(ti)::DataType).parameters
            lt = length(tip)
            p = Vector{Any}(undef, lt)
            for j = 1:lt
                ui = tip[j]
                p[j] = issimpleenoughtupleelem(unwrapva(ui)) ? ui : isvarargtype(ui) ? Vararg : Any
            end
            types[i] = rewrap_unionall(Tuple{p...}, ti)
        else
            # this element is not simple enough yet, make it so now
            types[i] = typenames[i].wrapper
        end
    end
    u = Union{types...}
    return u
end
```
`usep` is never set to `false`, so `simplify[j] = !usep` is always `false` and the `if usep`
branch always runs; the model mirrors the code as written. -/
def tmergeTypesSlow (n : Nat) (E : CEnv) (typea typeb : Val) : CM Val := do
  if !typea.isType || !typeb.isType then jlThrow "MethodError" "tmerge_types_slow"
  let mut types : Array Val := (uniontypes typea ++ uniontypes typeb).toArray
  let k := types.size
  let mut typenames : Array String := Array.replicate k ""
  let mut allDatatypes := true
  for i in [0:k] do
    -- check that we will be able to analyze (and simplify) everything
    -- bail if everything isn't a well-formed nominal kind
    let ti := types[i]!
    let uw := unwrapUnionall ti
    if let .datatype nm _ := uw then
      if !(← issub n E ti (← E.types.typename nm).wrapper) then return anyType
      typenames := typenames.set! i nm
    else if isType uw then
      typenames := typenames.set! i typeEqName
      allDatatypes := false
    else
      return anyType
  let u ← jlUnion n E types.toList
  if ← issimpleenoughtype n E u then
    return u
  if !allDatatypes then return anyType
  -- see if any of the union elements have the same TypeName
  -- in which case, simplify this tmerge by replacing it with
  -- the widest possible version of itself (the wrapper)
  let mut simplify : Array Bool := Array.replicate k false
  for i in [0:k] do
    if typenames[i]! == anyName then continue
    let ti := types[i]!
    for j in [i + 1:k] do
      if typenames[j]! == anyName then continue
      let some ijname ← tnameIntersect n E typenames[i]! typenames[j]! | continue
      let tj := types[j]!
      if ← issub n E ti tj then
        types := types.set! i .bottom
        typenames := typenames.set! i anyName
        simplify := simplify.set! i false
        simplify := simplify.set! j true
        break
      else if ← issub n E tj ti then
        types := types.set! j .bottom
        typenames := typenames.set! j anyName
        simplify := simplify.set! j false
        simplify := simplify.set! i true
      else
        let mut widen : Val := anyType
        if ijname == tupleName then
          -- try to widen Tuple slower: make a single non-concrete Tuple containing both
          let ui := unwrapUnionall ti
          let uj := unwrapUnionall tj
          if !ui.isDatatype || !uj.isDatatype then jlThrow "TypeError" "typeassert DataType"
          widen ← tuplemerge n E ui uj
          widen ← rewrapUnionallJ n E (← rewrapUnionallJ n E widen ti) tj
          simplify := simplify.set! j false
        else
          let wr := (← E.types.typename ijname).wrapper
          let uw := unwrapUnionall wr
          let ui := unwrapUnionall ti
          let uj := unwrapUnionall tj
          if !uw.isDatatype || !ui.isDatatype || !uj.isDatatype then
            jlThrow "TypeError" "typeassert DataType"
          let ui ← superUntilName n E ui ijname
          let uj ← superUntilName n E uj ijname
          let mut p : Array Val := #[]
          let mut usep := true
          widen := wr
          for kk in [0:uw.params.length] do
            let uik := ui.params[kk]!
            if (← egal n E uik uj.params[kk]!) && !hasFreeTypevars uik then
              p := p.push uik
              usep := true
            else
              p := p.push uw.params[kk]!
          if usep then
            widen ← rewrapUnionallJ n E (← jlApplyType n E wr p.toList) wr
            if !(← issub n E widen wr) then widen := wr
          simplify := simplify.set! j (!usep)
        types := types.set! i .bottom
        typenames := typenames.set! i anyName
        simplify := simplify.set! i false
        types := types.set! j widen
        typenames := typenames.set! j ijname
        break
  -- don't let elements of the union get too big, if the above didn't reduce something enough
  for i in [0:k] do
    if !simplify[i]! then continue
    let ti := types[i]!
    if ← issimpleenoughtype n E ti then continue
    if typenames[i]! == tupleName then
      -- otherwise we need to do a simple version of tuplemerge for one element now
      let uti := unwrapUnionall ti
      if !uti.isDatatype then jlThrow "TypeError" "typeassert DataType"
      let mut p : Array Val := #[]
      for ui in uti.params do
        p := p.push (if ← issimpleenoughtupleelem n E (unwrapva ui) then ui
          else if isvarargtype ui then .vararg none none else anyType)
      types := types.set! i (← rewrapUnionallJ n E (← jlTuple n E p.toList) ti)
    else
      -- this element is not simple enough yet, make it so now
      types := types.set! i (← E.types.typename typenames[i]!).wrapper
  jlUnion n E types.toList

/-! ## `tmerge` of each layer -/

/-- `tmerge_partial_struct(𝕃, typea, typeb)`; `none` is `nothing`.

Julia source: Compiler/src/typelimits.jl:609-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# N.B. This can also be called with both typea::Const and typeb::Const to
# to recover PartialStruct from `Const`s with overlapping fields.
@nospecializeinfer function tmerge_partial_struct(𝕃::PartialsLattice, @nospecialize(typea), @nospecialize(typeb))
    aty = widenconst(typea)
    bty = widenconst(typeb)
    if aty === bty && !isType(aty)
        if typea isa PartialStruct
            if typeb isa PartialStruct
                nflds = length(typea.fields)
                @assert nflds == length(typeb.fields)
            else
                nflds = length(typea.fields)
            end
        elseif typeb isa PartialStruct
            nflds = length(typeb.fields)
        else
            nflds = fieldcount(aty)
        end
        nflds == 0 && return nothing
        undefs = Union{Nothing,Bool}[nothing for _ in 1:nflds]
        fields = Vector{Any}(undef, nflds)
        fldmin = datatype_min_ninitialized(aty)
        n_initialized_merged = min(n_initialized(typea), n_initialized(typeb))
        anyrefine = n_initialized_merged > fldmin
        for i = 1:nflds
            if i == nflds && isvatuple(aty)
                # the trailing `Vararg` element carries no information beyond `aty` itself,
                # so keep it as is
                fields[i] = (unwrap_unionall(aty)::DataType).parameters[end]
                continue # `undefs[i]` stays `nothing`
            end
            ai = getfield_tfunc(𝕃, typea, Const(i))
            bi = getfield_tfunc(𝕃, typeb, Const(i))
            ft = fieldtype(aty, i)
            if is_lattice_equal(𝕃, ai, bi) || is_lattice_equal(𝕃, ai, ft)
                # Since ai===bi, the given type has no restrictions on complexity.
                # and can be used to refine ft
                tyi = ai
            elseif is_lattice_equal(𝕃, bi, ft)
                tyi = bi
            elseif (tyi′ = tmerge_field(𝕃, ai, bi); tyi′ !== nothing)
                # allow external lattice implementation to provide a custom field-merge strategy
                tyi = tyi′
            else
                # Otherwise use the default aggressive field-merge implementation, and
                # choose between using the fieldtype or some other simple merged type.
                # The wrapper type never has restrictions on complexity,
                # so try to use that to refine the estimated type too.
                tni = _typename(widenconst(ai))
                if tni isa Const && tni === _typename(widenconst(bi))
                    # A tmeet call may cause tyi to become complex, but since the inputs were
                    # strictly limited to being egal, this has no restrictions on complexity.
                    # (Otherwise, we would need to use <: and take the narrower one without
                    # intersection. See the similar comment in abstract_call_method.)
                    tyi = typeintersect(ft, (tni.val::Core.TypeName).wrapper)
                else
                    # Since aty===bty, the fieldtype has no restrictions on complexity.
                    tyi = ft
                end
            end
            fields[i] = tyi
            if typea isa PartialStruct
                aundefᵢ = _getundefs(typea)[i]
                if typeb isa PartialStruct
                    if aundefᵢ === _getundefs(typeb)[i]
                        undefs[i] = aundefᵢ
                    end
                else
                    if aundefᵢ === !isdefined(typeb.val, i)
                        undefs[i] = aundefᵢ
                    end
                end
            elseif typeb isa PartialStruct
                bundefᵢ = _getundefs(typeb)[i]
                if !isdefined(typea.val, i) === bundefᵢ
                    undefs[i] = bundefᵢ
                end
            else
                aundefᵢ = isdefined(typea.val, i)
                if aundefᵢ === isdefined(typeb.val, i)
                    undefs[i] = !aundefᵢ
                end
            end
            if !anyrefine
                anyrefine = has_nontrivial_extended_info(𝕃, tyi) || # extended information
                            ⋤(𝕃, tyi, ft) # just a type-level information, but more precise than the declared type
            end
        end
        anyrefine && return PartialStruct(𝕃, aty, undefs, fields)
    end
    return nothing
end
```
-/
def tmergePartialStruct (n : Nat) (E : CEnv) (L : Lattice) (typea typeb : LElt) :
    CM (Option LElt) := do
  let aty ← widenconst n E typea
  let bty ← widenconst n E typeb
  if (← egal n E aty bty) && !isType aty then
    let nflds ← match typea, typeb with
      | .partialStruct _ _ af _ _, .partialStruct _ _ bf _ _ => do
        if af.length != bf.length then jlThrow "AssertionError" "nflds == length(typeb.fields)"
        pure af.length
      | .partialStruct _ _ af _ _, _ => pure af.length
      | _, .partialStruct _ _ bf _ _ => pure bf.length
      | _, _ => fieldcount E aty
    if nflds == 0 then return none
    let mut undefs : Array (Option Bool) := Array.replicate nflds none
    let mut fields : Array LElt := Array.replicate nflds (.ty .bottom)
    let fldmin ← datatypeMinNinitialized E aty
    let nInitializedMerged := min (← nInitialized E typea) (← nInitialized E typeb)
    let mut anyrefine := decide (nInitializedMerged > fldmin)
    for i in [1:nflds+1] do
      if i == nflds && aty.unwrapUnionall.isVaTuple then
        -- the trailing `Vararg` element carries no information beyond `aty` itself
        let uaty := unwrapUnionall aty
        if !uaty.isDatatype then jlThrow "TypeError" "typeassert DataType"
        fields := fields.set! (i - 1) (.ty uaty.params.getLast!)
        continue
      let ai ← getfieldTfuncIdx n E L typea i
      let bi ← getfieldTfuncIdx n E L typeb i
      let ft ← fieldtypeIdx E aty i
      let mut tyi : LElt := ai
      let eqab ← isLatticeEqual n E L ai bi
      if eqab || (← isLatticeEqual n E L ai (.ty ft)) then
        tyi := ai
      else if ← isLatticeEqual n E L bi (.ty ft) then
        tyi := bi
      else if let some tyi' ← tmergeField L ai bi then
        tyi := tyi'
      else
        let tni := typenameT (← widenconst n E ai)
        match tni with
        | .const tname =>
          if tni == typenameT (← widenconst n E bi) then
            tyi := .ty (← typeintersect n E ft (← E.types.typename tname).wrapper)
          else
            tyi := .ty ft
        | _ => tyi := .ty ft
      fields := fields.set! (i - 1) tyi
      match typea, typeb with
      | .partialStruct _ au _ _ _, .partialStruct _ bu _ _ _ =>
        let aundef ← jlIndex au i
        if aundef == (← jlIndex bu i) then undefs := undefs.set! (i - 1) aundef
      | .partialStruct _ au _ _ _, .const bval =>
        let aundef ← jlIndex au i
        if aundef == some (!isdefinedField bval i) then undefs := undefs.set! (i - 1) aundef
      | .const aval, .partialStruct _ bu _ _ _ =>
        let bundef ← jlIndex bu i
        if some (!isdefinedField aval i) == bundef then undefs := undefs.set! (i - 1) bundef
      | .const aval, .const bval =>
        let adef := isdefinedField aval i
        if adef == isdefinedField bval i then undefs := undefs.set! (i - 1) (some !adef)
      | _, _ => jlThrow "ErrorException" "type has no field val"
      if !anyrefine then
        -- extended information, or just a type-level information more precise than `ft`
        anyrefine := (← hasNontrivialExtendedInfo n E L tyi)
        if !anyrefine then
          anyrefine := (← sqsubStrictNe n E L tyi (.ty ft))
    if anyrefine then
      return some (← mkPartialStruct n E aty undefs.toList fields.toList)
  return none

/-- `tmerge(lattice, typea, typeb)` for every layer.

Julia source: Compiler/src/typelimits.jl:450-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer @noinline function tmerge_limited(lattice::InferenceLattice, @nospecialize(typea), @nospecialize(typeb))
    typea === Union{} && return typeb
    typeb === Union{} && return typea

    # Like tmerge_fast_path, but tracking which causes need to be preserved at
    # the same time.
    if isa(typea, LimitedAccuracy) && isa(typeb, LimitedAccuracy)
        causesa = typea.causes
        causesb = typeb.causes
        typea = typea.typ
        typeb = typeb.typ
        suba = ⊑(lattice, typea, typeb)
        subb = ⊑(lattice, typeb, typea)

        # Approximated types are lattice equal. Merge causes.
        if suba && subb
            return LimitedAccuracy(typeb, merge_causes(causesa, causesb))
        elseif suba
            issimplertype(lattice, typeb, typea) && return LimitedAccuracy(typeb, causesb)
            causes = causesb
            # `a`'s causes may be discarded
        elseif subb
            causes = causesa
        else
            causes = union_causes(causesa, causesb)
        end
    else
        if isa(typeb, LimitedAccuracy)
            (typea, typeb) = (typeb, typea)
        end
        typea = typea::LimitedAccuracy

        causes = typea.causes
        typea = typea.typ

        suba = ⊑(lattice, typea, typeb)
        if suba
            issimplertype(lattice, typeb, typea) && return typeb
            # `typea` was narrower than `typeb`. Whatever tmerge produces,
            # we know it must be wider than `typeb`, so we may drop the
            # causes.
            causes = nothing
        end
        subb = ⊑(lattice, typeb, typea)
    end

    suba && subb && return LimitedAccuracy(typea, causes)
    subb && issimplertype(lattice, typea, typeb) && return LimitedAccuracy(typea, causes)
    return LimitedAccuracy(tmerge(widenlattice(lattice), typea, typeb), causes)
end

@nospecializeinfer function tmerge(lattice::InferenceLattice, @nospecialize(typea), @nospecialize(typeb))
    if isa(typea, LimitedAccuracy) || isa(typeb, LimitedAccuracy)
        return tmerge_limited(lattice, typea, typeb)
    end

    return tmerge(widenlattice(lattice), typea, typeb)
end
```

Julia source: Compiler/src/typelimits.jl:509-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function tmerge(lattice::ConditionalsLattice, @nospecialize(typea), @nospecialize(typeb))
    # type-lattice for Conditional wrapper (NOTE never be merged with InterConditional)
    if isa(typea, Conditional) && isa(typeb, Const)
        if typeb.val === true
            typeb = Conditional(typea.slot, typea.ssadef, Any, Union{})
        elseif typeb.val === false
            typeb = Conditional(typea.slot, typea.ssadef, Union{}, Any)
        end
    end
    if isa(typeb, Conditional) && isa(typea, Const)
        if typea.val === true
            typea = Conditional(typeb.slot, typeb.ssadef, Any, Union{})
        elseif typea.val === false
            typea = Conditional(typeb.slot, typeb.ssadef, Union{}, Any)
        end
    end
    if isa(typea, Conditional) && isa(typeb, Conditional)
        if is_same_conditionals(typea, typeb)
            thentype = tmerge(widenlattice(lattice), typea.thentype, typeb.thentype)
            elsetype = tmerge(widenlattice(lattice), typea.elsetype, typeb.elsetype)
            if thentype !== elsetype
                return Conditional(typea.slot, typea.ssadef, thentype, elsetype)
            end
        end
        val = maybe_extract_const_bool(typea)
        if val isa Bool && val === maybe_extract_const_bool(typeb)
            return Const(val)
        end
        return Bool
    end
    if isa(typea, Conditional)
        typeb === Union{} && return typea
        typea = widenconditional(typea)
    elseif isa(typeb, Conditional)
        typea === Union{} && return typeb
        typeb = widenconditional(typeb)
    end
    return tmerge(widenlattice(lattice), typea, typeb)
end

@nospecializeinfer function tmerge(lattice::InterConditionalsLattice, @nospecialize(typea), @nospecialize(typeb))
    # type-lattice for InterConditional wrapper (NOTE never be merged with Conditional)
    ... (the same, with `InterConditional(slot, thentype, elsetype)`)
end

@nospecializeinfer function tmerge(𝕃::AnyMustAliasesLattice, @nospecialize(typea), @nospecialize(typeb))
    if is_valid_lattice_norec(𝕃, typea)
        typeb === Union{} && return typea
        if is_valid_lattice_norec(𝕃, typeb) && is_same_alias(typea, typeb) &&
                widenconst(typea.vartyp) === widenconst(typeb.vartyp)
            # alias information is identical so simply preserve it
            𝕃′ = widenlattice(𝕃)
            vartyp = tmerge(𝕃′, typea.vartyp, typeb.vartyp)
            fldtyp = tmerge(𝕃′, typea.fldtyp, typeb.fldtyp)
            return update_mustalias(typea; vartyp, fldtyp)
        end
        typea = widenmustalias(typea)
    end
    if is_valid_lattice_norec(𝕃, typeb)
        typea === Union{} && return typeb
        typeb = widenmustalias(typeb)
    end
    return tmerge(widenlattice(𝕃), typea, typeb)
end
```

Julia source: Compiler/src/typelimits.jl:702-789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function tmerge(lattice::PartialsLattice, @nospecialize(typea), @nospecialize(typeb))
    r = tmerge_fast_path(lattice, typea, typeb)
    r !== nothing && return r

    # type-lattice for Const and PartialStruct wrappers
    aps = isa(typea, PartialStruct)
    bps = isa(typeb, PartialStruct)
    acp = aps || isa(typea, Const)
    bcp = bps || isa(typeb, Const)
    if acp && bcp
        typea === typeb && return typea
        psrt = tmerge_partial_struct(lattice, typea, typeb)
        psrt !== nothing && return psrt
    end

    # Don't widen const here - external AbstractInterpreter might insert lattice
    # layers between us and `ConstsLattice`.
    wl = widenlattice(lattice)
    aps && (typea = widenlattice(wl, typea))
    bps && (typeb = widenlattice(wl, typeb))

    # type-lattice for PartialOpaque wrapper
    apo = isa(typea, PartialOpaque)
    bpo = isa(typeb, PartialOpaque)
    if apo && bpo
        aty = widenconst(typea)
        bty = widenconst(typeb)
        if aty == bty
            if !(typea.source === typeb.source &&
                typea.parent === typeb.parent)
                return widenconst(typea)
            end
            return PartialOpaque(typea.typ, tmerge(lattice, typea.env, typeb.env),
                typea.parent, typea.source)
        end
        typea = aty
        typeb = bty
    elseif apo
        typea = widenlattice(wl, typea)
    elseif bpo
        typeb = widenlattice(wl, typeb)
    end

    # type-lattice for PartialTask wrapper
    apt = isa(typea, PartialTask)
    bpt = isa(typeb, PartialTask)
    if apt && bpt
        # Both are PartialTask - merge their fetch types
        merged_fetch_type = tmerge(lattice, typea.fetch_type, typeb.fetch_type)
        # Any carries no additional type information - return Task
        merged_fetch_type === Any && return Task
        return PartialTask(merged_fetch_type)
    elseif apt
        typea = Task
    elseif bpt
        typeb = Task
    end

    return tmerge(wl, typea, typeb)
end

@nospecializeinfer function tmerge(lattice::ConstsLattice, @nospecialize(typea), @nospecialize(typeb))
    acp = isa(typea, Const) || isa(typea, PartialTypeVar)
    bcp = isa(typeb, Const) || isa(typeb, PartialTypeVar)
    if acp && bcp
        typea === typeb && return typea
    end
    wl = widenlattice(lattice)
    acp && (typea = widenlattice(wl, typea))
    bcp && (typeb = widenlattice(wl, typeb))
    return tmerge(wl, typea, typeb)
end

@nospecializeinfer function tmerge(lattice::JLTypeLattice, @nospecialize(typea::AnyType), @nospecialize(typeb::AnyType))
    # it's always ok to form a Union of two concrete types
    act = isconcretetype(typea)
    bct = isconcretetype(typeb)
    if act && bct
        # Extra fast path for pointer-egal concrete types
        (pointer_from_objref(typea) === pointer_from_objref(typeb)) && return typea
    end
    if (act || isType(typea)) && (bct || isType(typeb))
        return Union{typea, typeb}
    end
    u = tmerge_fast_path(lattice, typea, typeb)
    u === nothing || return u
    return tmerge_types_slow(typea, typeb)
end
```
Concrete `DataType`s are hash-consed, so `pointer_from_objref` equality is `Val` equality. -/
def tmerge (n : Nat) (E : CEnv) (L : Lattice) (typea typeb : LElt) : CM LElt :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match L with
    | .inference p =>
      if !(typea.isLimited || typeb.isLimited) then
        return ← tmerge n E p typea typeb
      -- tmerge_limited
      if typea.isBottom then return typeb
      if typeb.isBottom then return typea
      let mut causes : Option (List ObjId × ObjId) := none
      let mut ta := typea
      let mut tb := typeb
      let mut suba := false
      let mut subb := false
      if let (.limitedAccuracy atyp acs acid, .limitedAccuracy bt bcs bcid) := (typea, typeb) then
        ta := atyp
        tb := bt
        suba ← sqsub n E L ta tb
        subb ← sqsub n E L tb ta
        -- Approximated types are lattice equal. Merge causes.
        if suba && subb then
          return ← mkLimitedAccuracy tb (some (← mergeCauses (acs, acid) (bcs, bcid)))
        else if suba then
          if ← issimplertype n E L tb ta then
            return ← mkLimitedAccuracy tb (some (bcs, bcid))
          causes := some (bcs, bcid)
        else if subb then
          causes := some (acs, acid)
        else
          causes := some (← unionCauses (acs, acid) (bcs, bcid))
      else
        if typeb.isLimited then
          ta := typeb
          tb := typea
        let .limitedAccuracy atyp acs acid := ta | jlThrow "TypeError" "typeassert LimitedAccuracy"
        causes := some (acs, acid)
        ta := atyp
        suba ← sqsub n E L ta tb
        if suba then
          if ← issimplertype n E L tb ta then return tb
          -- `typea` was narrower than `typeb`: the causes may be dropped
          causes := none
        subb ← sqsub n E L tb ta
      if suba && subb then return ← mkLimitedAccuracy ta causes
      if subb then
        if ← issimplertype n E L ta tb then return ← mkLimitedAccuracy ta causes
      mkLimitedAccuracy (← tmerge n E p ta tb) causes
    | .conditionals p | .interConditionals p =>
      let inter := L matches .interConditionals _
      let mkC (like : LElt) (t e : LElt) : CM LElt :=
        match like with
        | .conditional slot ssadef .. => mkConditional slot ssadef t e
        | .interConditional slot .. => pure (.interConditional slot t e)
        | _ => jlThrow "ErrorException" "unreachable"
      let mut typea := typea
      let mut typeb := typeb
      if isConditionalT inter typea then
        if let .const bv := typeb then
          match asBool? bv with
          | some true => typeb ← mkC typea (.ty anyType) (.ty .bottom)
          | some false => typeb ← mkC typea (.ty .bottom) (.ty anyType)
          | none => pure ()
      if isConditionalT inter typeb then
        if let .const av := typea then
          match asBool? av with
          | some true => typea ← mkC typeb (.ty anyType) (.ty .bottom)
          | some false => typea ← mkC typeb (.ty .bottom) (.ty anyType)
          | none => pure ()
      if isConditionalT inter typea && isConditionalT inter typeb then
        if ← isSameConditionals typea typeb then
          let (atp, ae) := match typea with
            | .conditional _ _ t e _ | .interConditional _ t e => (t, e) | x => (x, x)
          let (bt, be) := match typeb with
            | .conditional _ _ t e _ | .interConditional _ t e => (t, e) | x => (x, x)
          let thentype ← tmerge n E p atp bt
          let elsetype ← tmerge n E p ae be
          if !(← eltEgal n E thentype elsetype) then
            return ← mkC typea thentype elsetype
        let val := maybeExtractConstBool typea
        if let some v := val then
          if some v == maybeExtractConstBool typeb then
            return .const (boolVal v)
        return .ty boolTy
      if isConditionalT inter typea then
        if typeb.isBottom then return typea
        typea ← widenconditional typea
      else if isConditionalT inter typeb then
        if typea.isBottom then return typeb
        typeb ← widenconditional typeb
      tmerge n E p typea typeb
    | .mustAliases p | .interMustAliases p =>
      let mut typea := typea
      let mut typeb := typeb
      if isValidLatticeNorec L typea then
        if typeb.isBottom then return typea
        if isValidLatticeNorec L typeb && isSameAlias typea typeb then
          let (av, af) := match typea with
            | .mustAlias _ _ v _ f | .interMustAlias _ v _ f => (v, f) | x => (x, x)
          let (bv, bf) := match typeb with
            | .mustAlias _ _ v _ f | .interMustAlias _ v _ f => (v, f) | x => (x, x)
          if ← egal n E (← widenconst n E av) (← widenconst n E bv) then
            -- alias information is identical so simply preserve it
            let vartyp ← tmerge n E p av bv
            let fldtyp ← tmerge n E p af bf
            return ← updateMustalias typea (some vartyp) (some fldtyp)
        typea ← widenmustalias typea
      if isValidLatticeNorec L typeb then
        if typea.isBottom then return typeb
        typeb ← widenmustalias typeb
      tmerge n E p typea typeb
    | .partials wl =>
      if let some r ← tmergeFastPath n E L typea typeb then return r
      -- type-lattice for Const and PartialStruct wrappers
      let aps := typea.isPartialStruct
      let bps := typeb.isPartialStruct
      let acp := aps || typea.isConst
      let bcp := bps || typeb.isConst
      if acp && bcp then
        if ← eltEgal n E typea typeb then return typea
        if let some psrt ← tmergePartialStruct n E L typea typeb then return psrt
      let mut typea := typea
      let mut typeb := typeb
      if aps then typea ← widenlatticeElt n E wl typea
      if bps then typeb ← widenlatticeElt n E wl typeb
      -- type-lattice for PartialOpaque wrapper
      match typea, typeb with
      | .partialOpaque atyp aenv apar asrc, .partialOpaque btyp benv bpar bsrc =>
        if ← tyEq n E atyp btyp then
          if !(asrc == bsrc && apar == bpar) then
            return .ty atyp
          return .partialOpaque atyp (← tmerge n E L aenv benv) apar asrc
        typea := .ty atyp
        typeb := .ty btyp
      | .partialOpaque .., _ => typea ← widenlatticeElt n E wl typea
      | _, .partialOpaque .. => typeb ← widenlatticeElt n E wl typeb
      | _, _ => pure ()
      -- type-lattice for PartialTask wrapper
      match typea, typeb with
      | .partialTask af, .partialTask bf =>
        let merged ← tmerge n E L af bf
        if merged.isAny then return .ty taskType
        return .partialTask merged
      | .partialTask _, _ => typea := .ty taskType
      | _, .partialTask _ => typeb := .ty taskType
      | _, _ => pure ()
      tmerge n E wl typea typeb
    | .consts =>
      let acp := typea.isConst || typea.isPartialTypeVar
      let bcp := typeb.isConst || typeb.isPartialTypeVar
      if acp && bcp then
        if ← eltEgal n E typea typeb then return typea
      let mut typea := typea
      let mut typeb := typeb
      if acp then typea ← widenlatticeElt n E .jlType typea
      if bcp then typeb ← widenlatticeElt n E .jlType typeb
      tmerge n E .jlType typea typeb
    | .jlType =>
      let (.ty ta, .ty tb) := (typea, typeb) | jlThrow "MethodError" "tmerge(::JLTypeLattice, ...)"
      if !ta.isType || !tb.isType then jlThrow "MethodError" "tmerge(::JLTypeLattice, ...)"
      -- it's always ok to form a Union of two concrete types
      let act ← isconcretetype E ta
      let bct ← isconcretetype E tb
      if act && bct then
        -- Extra fast path for pointer-egal concrete types
        if ta == tb then return typea
      if (act || isType ta) && (bct || isType tb) then
        return .ty (← jlUnion n E [ta, tb])
      if let some u ← tmergeFastPath n E L typea typeb then return u
      return .ty (← tmergeTypesSlow n E ta tb)

/-- `tmerge(a, b)` on `fallback_lattice` (`Compiler/src/abstractlattice.jl:317`). -/
def tmergeFallback (n : Nat) (E : CEnv) (a b : LElt) : CM LElt := tmerge n E fallbackLattice a b

end JuliaLean.Compiler
