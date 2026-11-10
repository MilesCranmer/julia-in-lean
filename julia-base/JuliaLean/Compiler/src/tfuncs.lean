import JuliaLean.Compiler.Prelude
import JuliaLean.Compiler.src.typeutils
import JuliaLean.Compiler.src.abstractlattice
import JuliaLean.Compiler.src.typelattice
import JuliaLean.Compiler.src.typelimits

/-!
`Compiler/src/tfuncs.jl`: the return-type functions (tfuncs) and `nothrow` predicates of the core
builtins, and the dispatch `builtin_tfunction` / `builtin_nothrow` for them.

Modelled builtins: `throw`, `Core.ifelse`, `===`, `isdefined`, `nfields`, `svec`, `typeof`,
`has_free_typevars`, `typeassert`, `isa`, `<:`, `getfield` and `tuple`. `builtin_tfunction` also
dispatches `current_scope`, `apply_type` and the builtins without a tfunc (`Any`), but does not
model the first two tfuncs. The other builtins and all intrinsics are not modelled:
`builtin_tfunction` reports `unmodelled` for them.

Every function takes an explicit fuel `n` (Julia has none: running out is a model failure, not a
Julia outcome). Recursion through the lattice layers keeps the layer explicit, as Julia's
dispatch on the lattice argument does.

Facts about struct types that `Types` does not record (field names, `const` and `@atomic`
fields, `n_uninitialized`) come from the `TEnv.tns` side table, keyed by type name; field types
and `datatype_min_ninitialized` come from `CEnv.structs`. A type missing from them reports
`unmodelled`. Other inputs the model cannot represent (a `Const` whose value is a type object or a
mutable object, whose fields `Val` does not record; a `TypeName` result; `NamedTuple` types) also
report `unmodelled`, at the point the Julia code would read them.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-! ## Side tables and runtime helpers -/

/-- Per-type-name facts: `tn.names`, the `tn.constfields` and `tn.atomicfields` bitmaps (empty
for `C_NULL`), and `tn.n_uninitialized`. -/
structure TnInfo where
  names : List String
  const : List Bool
  atomic : List Bool
  nUninit : Nat
  deriving Inhabited, Repr

/-- The universe of a tfunc computation. -/
structure TEnv where
  E : CEnv
  tns : List (String × TnInfo) := []
  deriving Inhabited

def TEnv.tn (T : TEnv) (name : String) : CM TnInfo :=
  match T.tns.lookup name with
  | some i => pure i
  | none => unmodelled s!"type name facts of {name}"

def moduleType : Val := .datatype "Core.Module" []
def namedTupleName : String := "Core.NamedTuple"
def svecType : Val := .datatype "Core.SimpleVector" []
def unionallType' : Val := unionallType

/-- `hasintersect(a, b)` (`base/runtime_internals.jl:1999`): `typeintersect(a, b) !== Bottom`. -/
def hasintersect (n : Nat) (E : CEnv) (a b : Val) : CM Bool := do
  return (← typeintersect n E a b) != .bottom

/-- Julia's short-circuit `a || b` and `a && b` on monadic conditions. -/
def orM (a b : CM Bool) : CM Bool := do if ← a then return true else b
def andM (a b : CM Bool) : CM Bool := do if ← a then b else return false

/-- `Const(true)` / `Const(false)`. -/
def constBool (b : Bool) : LElt := .const (boolVal b)

/-- `x === Const(true)` for a tfunc result. -/
def isConstTrue : LElt → Bool
  | .const v => asBool? v == some true
  | _ => false

/-- `isvatuple(t)` (`base/essentials.jl:593-601`). -/
def isvatuple (t : Val) : Bool :=
  match t.unwrapUnionall with
  | .datatype _ ps => match ps.getLast? with
    | some p => p.isVararg
    | none => false
  | _ => false

/-- `ismutabletype(t)` for a `DataType` `t`. -/
def ismutabletypeDT (E : CEnv) (t : Val) : CM Bool := do
  match t.unwrapUnionall with
  | .datatype name _ => return (← E.types.typename name).mutable
  | _ => return false

/-- `fieldindex(T::DataType, name, false)`: `jl_field_index(T, name, 0) + 1`, a 1-based index
into `T.name.names`, or `0`. Tuples have no field names. -/
def fieldindexDT (T : TEnv) (t : Val) (sym : String) : CM Nat := do
  let .datatype name _ := t | jlThrow "MethodError" "fieldindex"
  if name == namedTupleName then unmodelled "fieldindex(::NamedTuple)"
  if name == tupleName then return 0
  let info ← T.tn name
  match info.names.idxOf? sym with
  | some i => return i + 1
  | none => return 0

/-- `isconst(t::Type, s::Int)`

Julia source: base/runtime_internals.jl:544-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
```
-/
def isconstIdx (T : TEnv) (t : Val) (s : Int) : CM Bool := do
  let t := t.unwrapUnionall
  let .datatype name _ := t | return false
  if !(← T.E.types.typename name).mutable then return true
  let info ← T.tn name
  if !(1 ≤ s && s ≤ info.names.length) then return true
  if info.const.isEmpty then return false
  return info.const.getD (s - 1).toNat false

/-- `isfieldatomic(t::Type, s::Int)`

Julia source: base/runtime_internals.jl:568-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
```
-/
def isfieldatomicIdx (T : TEnv) (t : Val) (s : Int) : CM Bool := do
  let t := t.unwrapUnionall
  let .datatype name _ := t | return false
  if !(← T.E.types.typename name).mutable then return false
  let info ← T.tn name
  if !(1 ≤ s && s ≤ info.names.length) then return false
  if info.atomic.isEmpty then return false
  return info.atomic.getD (s - 1).toNat false

/-- `datatype_fieldtypes(s)` of a `DataType`: a tuple's parameters, or a struct's field types
from `CEnv.structs`. -/
def datatypeFieldtypes (E : CEnv) (s : Val) : CM (List Val) := do
  let .datatype name ps := s | jlThrow "TypeError" "datatype_fieldtypes"
  if name == tupleName then return ps
  if name == namedTupleName then unmodelled "datatype_fieldtypes(::NamedTuple)"
  match E.structs.find? (·.1 == s) with
  | some (_, fts, _) => return fts
  | none => unmodelled s!"datatype_fieldtypes of {repr s}"

/-- `isbitstype(t)`: a `DataType` whose layout is pointer-free and immutable. -/
def isbitstype (n : Nat) (E : CEnv) (t : Val) : CM Bool := do
  if !t.isDatatype then return false
  isBits n E.types t

/-- `nfields(x)` (`jl_f_nfields`, `src/builtins.c:1457-1462`): the field count of `typeof(x)`.
Values of kinds and other non-struct objects read the `CEnv.nfields` table. -/
def nfieldsRT (E : CEnv) (x : Val) : CM Nat := do
  match x with
  | .imm .. | .long _ | .bits .. | .symbol _ | .module _ => nfieldsOf E x
  | _ => match E.nfields.find? (·.1 == typeOf x) with
    | some (_, k) => pure k
    | none => unmodelled s!"nfields of {repr (typeOf x)}"

/-- `isdefined(x, i::Int)` on a `Const` payload. Values whose fields `Val` does not record
report `unmodelled`. -/
def isdefinedRT (E : CEnv) (x : Val) (i : Int) : CM Bool := do
  match x with
  | .imm _ fs => return 1 ≤ i && i ≤ fs.length
  | .long _ | .bits .. | .symbol _ => return false
  | _ =>
    let _ ← nfieldsRT E x
    unmodelled s!"isdefined on {repr (typeOf x)}"

/-- `getfield(x, i::Int)` on a `Const` payload after `isdefined(x, i)`. -/
def getfieldRT (x : Val) (i : Int) : CM Val :=
  match x with
  | .imm _ fs => match fs[(i - 1).toNat]? with
    | some v => if i ≥ 1 then pure v else jlThrow "BoundsError"
    | none => jlThrow "BoundsError"
  | _ => unmodelled "getfield on a Const payload"

/-! ## `instanceof_tfunc` -/

/-- `isa(x, Tuple)` for a type parameter `x`: a tuple value. -/
def isImmVal : Val → Bool
  | .imm ty _ => ty.isTupleType
  | _ => false

/-- `instanceof_tfunc(t, astag, troot)`, on a type (`instanceofTfuncT`) and on a lattice element.
The result is `(type, isexact, isconcrete, istype)`.

Julia source: Compiler/src/tfuncs.jl:97-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# returns (type, isexact, isconcrete, istype)
# if isexact is false, the actual runtime type may (will) be a subtype of t
# if isconcrete is true, the actual runtime type is definitely concrete (unreachable if not valid as a typeof)
# if istype is true, the actual runtime value will definitely be a type (e.g. this is false for Union{Type{Int}, Int})
function instanceof_tfunc(@nospecialize(t), astag::Bool=false, @nospecialize(troot = t))
    if isa(t, Const)
        if isa(t.val, Type) && valid_as_lattice(t.val, astag)
            return t.val, true, isconcretetype(t.val), true
        end
        return Bottom, true, false, false # runtime throws on non-Type
    end
    t = widenconst(t)
    troot = widenconst(troot)
    if t === Bottom
        return Bottom, true, true, false # runtime unreachable
    elseif t === typeof(Bottom) || !hasintersect(t, Type)
        return Bottom, true, false, false # literal Bottom or non-Type
    elseif isTypeEgal(t)
        # the value is exactly (`===`) the closed type `tp`
        tp = type_parameter(t)
        valid_as_lattice(tp, astag) || return Bottom, true, false, false # runtime unreachable / throws on non-Type
        return tp, true, isconcretetype(tp), true
    elseif isTypeEq(t)
        tp = type_parameter(t)
        valid_as_lattice(tp, astag) || return Bottom, true, false, false # runtime unreachable / throws on non-Type
        if troot isa UnionAll
            # Free `TypeVar`s inside `Type` has violated the "diagonal" rule.
            # Widen them before `UnionAll` rewraping to relax concrete constraint.
            tp = widen_diagonal(tp, troot)
        end
        return tp, !has_free_typevars(tp), isconcretetype(tp), true
    elseif isa(t, UnionAll)
        t′ = unwrap_unionall(t)
        t′′, isexact, isconcrete, istype = instanceof_tfunc(t′, astag, rewrap_unionall(t, troot))
        tr = rewrap_unionall(t′′, t)
        if t′′ isa DataType && t′′.name !== Tuple.name && !has_free_typevars(tr)
            # a real instance must be within the declared bounds of the type,
            # so we can intersect with the original wrapper.
            tr = typeintersect(tr, t′′.name.wrapper)
            isconcrete = !isabstracttype(t′′)
            if tr === Union{}
                # runtime unreachable (our inference Type{T} where S is
                # uninhabited with any runtime T that exists)
                isexact = true
            end
        end
        # If this is a NamedTuple type with known names but an unknown tuple type
        # parameter, use the length of the names to constrain the tuple type.
        if t′′ isa DataType && t′′.name === _NAMEDTUPLE_NAME && t′′.parameters[1] isa Tuple && has_free_typevars(t′′)
            names = t′′.parameters[1]::Tuple
            n = length(names)
            nt_bound = NamedTuple{names, T} where T<:NTuple{n, Any}
            tr = typeintersect(tr, nt_bound)
        end
        return tr, isexact, isconcrete, istype
    elseif isa(t, Union)
        ta, isexact_a, isconcrete_a, istype_a = instanceof_tfunc(unwraptv(t.a), astag, troot)
        tb, isexact_b, isconcrete_b, istype_b = instanceof_tfunc(unwraptv(t.b), astag, troot)
        isconcrete = isconcrete_a && isconcrete_b
        istype = istype_a && istype_b
        # most users already handle the Union case, so here we assume that
        # `isexact` only cares about the answers where there's actually a Type
        # (and assuming other cases causing runtime errors)
        ta === Union{} && return tb, isexact_b, isconcrete, istype
        tb === Union{} && return ta, isexact_a, isconcrete, istype
        return Union{ta, tb}, false, isconcrete, istype # at runtime, will be exactly one of these
    end
    return Any, false, false, false
end
```
The `Const` case is handled by `instanceofTfunc`; the recursive calls pass types, for which
`widenconst` is the identity. -/
def instanceofTfuncT (n : Nat) (E : CEnv) (t : Val) (astag : Bool) (troot : Val) :
    CM (Val × Bool × Bool × Bool) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let t ← widenconst n E (.ty t)
    let troot ← widenconst n E (.ty troot)
    if t == .bottom then
      return (.bottom, true, true, false)
    else if t == typeofbottomType || !(← hasintersect n E t typeTypeVal) then
      return (.bottom, true, false, false)
    else if isTypeEgal t then
      let tp ← typeParameter t
      if !(← validAsLattice n E tp astag) then return (.bottom, true, false, false)
      return (tp, true, ← isconcretetype E tp, true)
    else if isTypeEq t then
      let mut tp ← typeParameter t
      if !(← validAsLattice n E tp astag) then return (.bottom, true, false, false)
      if troot.isUnionall then
        tp ← jlWidenDiagonal n E.types tp troot
      return (tp, !hasFreeTypevars tp, ← isconcretetype E tp, true)
    else if t.isUnionall then
      let t' := unwrapUnionall t
      let (t'', isexact, isconcrete, istype) ←
        instanceofTfuncT n E t' astag (← rewrapUnionallJ n E t troot)
      let mut isexact := isexact
      let mut isconcrete := isconcrete
      let mut tr ← rewrapUnionallJ n E t'' t
      if let .datatype name ps := t'' then
        if name != tupleName && !hasFreeTypevars tr then
          tr ← typeintersect n E tr (← E.types.typename name).wrapper
          isconcrete := !(← isabstracttype E t'')
          if tr == .bottom then
            isexact := true
        if name == namedTupleName && (ps.head?.map isImmVal).getD false && hasFreeTypevars t'' then
          unmodelled "instanceof_tfunc: NamedTuple names bound"
      return (tr, isexact, isconcrete, istype)
    else if let .union a b := t then
      let (ta, isexactA, isconcreteA, istypeA) ← instanceofTfuncT n E (← unwraptv n a) astag troot
      let (tb, isexactB, isconcreteB, istypeB) ← instanceofTfuncT n E (← unwraptv n b) astag troot
      let isconcrete := isconcreteA && isconcreteB
      let istype := istypeA && istypeB
      if ta == .bottom then return (tb, isexactB, isconcrete, istype)
      if tb == .bottom then return (ta, isexactA, isconcrete, istype)
      return (← jlUnion n E [ta, tb], false, isconcrete, istype)
    return (anyType, false, false, false)

def instanceofTfunc (n : Nat) (E : CEnv) (t : LElt) (astag : Bool := false) :
    CM (Val × Bool × Bool × Bool) := do
  if let .const v := t then
    if ← andM (pure v.isType) (validAsLattice n E v astag) then
      return (v, true, ← isconcretetype E v, true)
    return (.bottom, true, false, false)
  let tw ← widenconst n E t
  instanceofTfuncT n E tw astag tw

/-! ## `ifelse`, `===`, `isdefined` -/

/-- `ifelse_tfunc(𝕃, cnd, x, y)`

Julia source: Compiler/src/tfuncs.jl:344-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function ifelse_tfunc(𝕃::AbstractLattice, cnd, x, y)
    cnd = widenslotwrapper(cnd)
    if isa(cnd, Const)
        if cnd.val === true
            return x
        elseif cnd.val === false
            return y
        else
            return Bottom
        end
    elseif !hasintersect(widenconst(cnd), Bool)
        return Bottom
    end
    return tmerge(𝕃, x, y)
end
```
-/
def ifelseTfunc (n : Nat) (E : CEnv) (L : Lattice) (cnd x y : LElt) : CM LElt := do
  let cnd ← widenslotwrapper cnd
  match cnd with
  | .const v =>
    match asBool? v with
    | some true => return x
    | some false => return y
    | none => return .ty .bottom
  | _ =>
    if !(← hasintersect n E (← widenconst n E cnd) boolTy) then
      return .ty .bottom
    tmerge n E L x y

/-- `ifelse_nothrow(𝕃, cond, x, y)`

Julia source: Compiler/src/tfuncs.jl:361-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function ifelse_nothrow(𝕃::AbstractLattice, cond, x, y)
    ⊑ = partialorder(𝕃)
    return cond ⊑ Bool
end
```
-/
def ifelseNothrow (n : Nat) (E : CEnv) (L : Lattice) (cond : LElt) : CM Bool :=
  sqsub n E L cond (.ty boolTy)

/-- `egal_tfunc(𝕃, x, y)` for every layer; layers without a method defer to their parent.

Julia source: Compiler/src/tfuncs.jl:366-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs egal_tfunc(𝕃::AbstractLattice, x, y) = egal_tfunc(widenlattice(𝕃), x, y)
@nospecs function egal_tfunc(𝕃::MustAliasesLattice, x, y)
    return egal_tfunc(widenlattice(𝕃), widenmustalias(x), widenmustalias(y))
end
@nospecs function egal_tfunc(𝕃::ConditionalsLattice, x, y)
    if isa(x, Conditional)
        y = widenconditional(y)
        if isa(y, Const)
            y.val === false && return Conditional(x.slot, x.ssadef, x.elsetype, x.thentype)
            y.val === true && return x
            return Const(false)
        end
    elseif isa(y, Conditional)
        x = widenconditional(x)
        if isa(x, Const)
            x.val === false && return Conditional(y.slot, y.ssadef, y.elsetype, y.thentype)
            x.val === true && return y
            return Const(false)
        end
    end
    return egal_tfunc(widenlattice(𝕃), x, y)
end
@nospecs function egal_tfunc(𝕃::ConstsLattice, x, y)
    if isa(x, Const) && isa(y, Const)
        return Const(x.val === y.val)
    elseif (isa(x, Const) && y === typeof(x.val) && issingletontype(y)) ||
           (isa(y, Const) && x === typeof(y.val) && issingletontype(x))
        return Const(true)
    end
    return egal_tfunc(widenlattice(𝕃), x, y)
end
@nospecs function egal_tfunc(::JLTypeLattice, x, y)
    hasintersect(widenconst(x), widenconst(y)) || return Const(false)
    return Bool
end
```
-/
def egalTfunc (n : Nat) (E : CEnv) (L : Lattice) (x y : LElt) : CM LElt :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match L with
    | .mustAliases p => egalTfunc n E p (← widenmustalias x) (← widenmustalias y)
    | .conditionals p =>
      let mut x := x
      let mut y := y
      if let .conditional xs xd xt xe _ := x then
        y ← widenconditional y
        if let .const v := y then
          if asBool? v == some false then return ← mkConditional xs xd xe xt
          if asBool? v == some true then return x
          return constBool false
      else if let .conditional ys yd yt ye _ := y then
        x ← widenconditional x
        if let .const v := x then
          if asBool? v == some false then return ← mkConditional ys yd ye yt
          if asBool? v == some true then return y
          return constBool false
      egalTfunc n E p x y
    | .consts =>
      match x, y with
      | .const a, .const b => return constBool (← egal n E a b)
      | _, _ =>
        let cx : CM Bool := do
          let .const a := x | return false
          let .ty yt := y | return false
          if !(← egal n E yt (typeOf a)) then return false
          issingletontype n E yt
        let cy : CM Bool := do
          let .const b := y | return false
          let .ty xt := x | return false
          if !(← egal n E xt (typeOf b)) then return false
          issingletontype n E xt
        if ← orM cx cy then return constBool true
        egalTfunc n E .jlType x y
    | .jlType =>
      if !(← hasintersect n E (← widenconst n E x) (← widenconst n E y)) then
        return constBool false
      return .ty boolTy
    | .inference p | .partials p | .interConditionals p | .interMustAliases p => egalTfunc n E p x y

/-- `isdefined_nothrow(𝕃, argtypes)` and `isdefined_nothrow(𝕃, x, name)`

Julia source: Compiler/src/tfuncs.jl:403-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isdefined_nothrow(𝕃::AbstractLattice, argtypes::Vector{Any})
    if length(argtypes) ≠ 2
        # TODO prove nothrow when ordering is specified
        return false
    end
    return isdefined_nothrow(𝕃, argtypes[1], argtypes[2])
end
@nospecs function isdefined_nothrow(𝕃::AbstractLattice, x, name)
    ⊑ = partialorder(𝕃)
    isvarargtype(x) && return false
    isvarargtype(name) && return false
    if hasintersect(widenconst(x), Module)
        return name ⊑ Symbol
    else
        return name ⊑ Symbol || name ⊑ Int
    end
end
```
-/
def isdefinedNothrow (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt) : CM Bool := do
  let [x, name] := argtypes | return false
  if x.isVarargElt then return false
  if name.isVarargElt then return false
  if ← hasintersect n E (← widenconst n E x) moduleType then
    sqsub n E L name (.ty symbolType)
  else
    orM (sqsub n E L name (.ty symbolType)) (sqsub n E L name (.ty longType))

/-- `isdefined_tfunc(𝕃, arg1, sym[, order])`

Julia source: Compiler/src/tfuncs.jl:421-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function isdefined_tfunc(𝕃::AbstractLattice, arg1, sym, order)
    return isdefined_tfunc(𝕃, arg1, sym)
end
@nospecs function isdefined_tfunc(𝕃::AbstractLattice, arg1, sym)
    if arg1 isa MustAlias
        arg1 = widenmustalias(arg1)
    end
    arg1t = arg1 isa Const ? typeof(arg1.val) : isconstType(arg1) ? typeof(type_parameter(arg1)) : widenconst(arg1)
    a1 = unwrap_unionall(arg1t)
    if isa(a1, DataType) && !isabstracttype(a1)
        if a1 === Module
            hasintersect(widenconst(sym), Symbol) || return Bottom
            # isa(sym, Const) case intercepted in abstract interpretation
        elseif isa(sym, Const)
            val = sym.val
            if isa(val, Symbol)
                idx = fieldindex(a1, val, false)::Int
            elseif isa(val, Int)
                idx = val
            else
                return Bottom
            end
            if 1 ≤ idx ≤ datatype_min_ninitialized(a1)
                return Const(true)
            elseif a1.name === _NAMEDTUPLE_NAME
                if isconcretetype(a1)
                    return Const(false)
                else
                    ns = a1.parameters[1]
                    if isa(ns, Tuple)
                        return Const(1 ≤ idx ≤ length(ns))
                    end
                end
            elseif idx ≤ 0 || (!isvatuple(a1) && idx > fieldcount(a1))
                return Const(false)
            elseif isa(arg1, Const)
                if !ismutabletype(a1) || isconst(a1, idx)
                    return Const(isdefined(arg1.val, idx))
                end
            elseif isa(arg1, PartialStruct)
                if !isvarargtype(arg1.fields[end])
                    aundefᵢ = _getundefs(arg1)[idx]
                    if aundefᵢ isa Bool
                        return Const(!aundefᵢ)
                    end
                end
            elseif !isvatuple(a1)
                fieldT = fieldtype(a1, idx)
                if isa(fieldT, DataType) && isbitstype(fieldT)
                    return Const(true)
                end
            end
        # datatype_fieldcount is what `fieldcount` uses internally
        # and returns nothing (!==0) for non-definite field counts.
        elseif datatype_fieldcount(a1) === 0
            return Const(false)
        end
    elseif isa(a1, Union)
        # Results can only be `Const` or `Bool`
        return tmerge(𝕃,
                      isdefined_tfunc(𝕃, rewrap_unionall(a1.a, arg1t), sym),
                      isdefined_tfunc(𝕃, rewrap_unionall(a1.b, arg1t), sym))
    end
    return Bool
end
```
-/
def isdefinedTfunc (n : Nat) (T : TEnv) (L : Lattice) (arg1 sym : LElt) : CM LElt :=
  let E := T.E
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let arg1 ← if arg1.isMustAlias then widenmustalias arg1 else pure arg1
    let arg1t ← match arg1 with
      | .const v => pure (typeOf v)
      | .ty t => if isconstType t then pure (typeOf (← typeParameter t)) else widenconst n E arg1
      | _ => widenconst n E arg1
    let a1 := unwrapUnionall arg1t
    if a1.isDatatype && !(← isabstracttype E a1) then
      if a1 == moduleType then
        if !(← hasintersect n E (← widenconst n E sym) symbolType) then return .ty .bottom
      else if let .const val := sym then
        let idx? : Option Int ← match val with
          | .symbol s => do pure (some (Int.ofNat (← fieldindexDT T a1 s)))
          | .long k => pure (some k)
          | _ => pure none
        let some idx := idx? | return .ty .bottom
        if 1 ≤ idx then
          if idx ≤ (← datatypeMinNinitialized E a1) then
            return constBool true
        if a1.name? == some namedTupleName then
          unmodelled "isdefined_tfunc(::NamedTuple)"
        let outOfRange ← if idx ≤ 0 then pure true
          else if isvatuple a1 then pure false
          else do pure (idx > (← fieldcount E a1))
        if outOfRange then
          return constBool false
        else if let .const v := arg1 then
          if ← orM (do return !(← ismutabletypeDT E a1)) (isconstIdx T a1 idx) then
            return constBool (← isdefinedRT E v idx)
        else if let .partialStruct _ undefs fields _ _ := arg1 then
          if !(← jlIndex fields fields.length).isVarargElt then
            if let some u ← jlIndex undefs idx.toNat then
              return constBool !u
        else if !isvatuple a1 then
          let fieldT ← fieldtypeIdx E a1 idx.toNat
          if ← andM (pure fieldT.isDatatype) (isbitstype n E fieldT) then
            return constBool true
      else if (← datatypeFieldcount E a1) == some 0 then
        return constBool false
    else if let .union a b := a1 then
      return ← tmerge n E L (← isdefinedTfunc n T L (.ty (← rewrapUnionallJ n E a arg1t)) sym)
        (← isdefinedTfunc n T L (.ty (← rewrapUnionallJ n E b arg1t)) sym)
    return .ty boolTy

/-! ## `nfields`, `typeof`, `has_free_typevars` -/

/-- `nfields_tfunc(𝕃, x)`

Julia source: Compiler/src/tfuncs.jl:620-645 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function nfields_tfunc(𝕃::AbstractLattice, x)
    isa(x, Const) && return Const(nfields(x.val))
    isa(x, Conditional) && return Const(0)
    xt = widenconst(x)
    x = unwrap_unionall(xt)
    isconstType(x) && return Const(nfields(type_parameter(x)))
    if isa(x, DataType) && !isabstracttype(x)
        if x.name === Tuple.name
            isvatuple(x) && return Int
            return Const(length(x.types))
        elseif x.name === _NAMEDTUPLE_NAME
            length(x.parameters) == 2 || return Int
            names = x.parameters[1]
            isa(names, Tuple{Vararg{Symbol}}) || return nfields_tfunc(𝕃, rewrap_unionall(x.parameters[2], xt))
            return Const(length(names))
        else
            return Const(isdefined(x, :types) ? length(x.types) : length(x.name.names))
        end
    end
    if isa(x, Union)
        na = nfields_tfunc(𝕃, unwraptv(x.a))
        na === Int && return Int
        return tmerge(𝕃, na, nfields_tfunc(𝕃, unwraptv(x.b)))
    end
    return Int
end
```
-/
def nfieldsTfunc (n : Nat) (T : TEnv) (L : Lattice) (x : LElt) : CM LElt :=
  let E := T.E
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let .const v := x then return .const (.long (← nfieldsRT E v))
    if x.isConditional then return .const (.long 0)
    let xt ← widenconst n E x
    let x := unwrapUnionall xt
    if isconstType x then return .const (.long (← nfieldsRT E (← typeParameter x)))
    if let .datatype name ps := x then
      if !(← isabstracttype E x) then
        if name == tupleName then
          if isvatuple x then return .ty longType
          return .const (.long ps.length)
        else if name == namedTupleName then
          unmodelled "nfields_tfunc(::NamedTuple)"
        else
          return .const (.long (← T.tn name).names.length)
    if let .union a b := x then
      let na ← nfieldsTfunc n T L (.ty (← unwraptv n a))
      if let .ty t := na then
        if t == longType then return .ty longType
      return ← tmerge n E L na (← nfieldsTfunc n T L (.ty (← unwraptv n b)))
    return .ty longType

/-- The variable name `<:` in `Type{<:t}` gets from lowering in the pinned system image. -/
def typeofTypevarName : String := "#s949"

/-- `typeof_concrete_vararg(t)`

Julia source: Compiler/src/tfuncs.jl:862-880 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# more accurate typeof_tfunc for vararg tuples abstract only in length
function typeof_concrete_vararg(t::DataType)
    np = length(t.parameters)
    for i = 1:np
        p = t.parameters[i]
        if i == np && isvarargtype(p)
            if isdefined(p, :T) && isconcretetype(p.T)
                t = Type{Tuple{t.parameters[1:np-1]..., Vararg{p.T, N}}} where N
                if isdefined(p, :N)
                    return t{p.N}
                end
                return t
            end
        elseif !isconcretetype(p)
            break
        end
    end
    return nothing
end
```
-/
def typeofConcreteVararg (n : Nat) (E : CEnv) (t : Val) : CM (Option Val) := do
  let ps := t.params
  let np := ps.length
  for (p, i) in ps.zip (List.range' 1 np) do
    if i == np && p.isVararg then
      if let .vararg (some pT) pN := p then
        if ← isconcretetype E pT then
          let N ← jlNewTypeVar "N" anyType
          let va ← jlVararg n E pT (some N)
          let tt ← jlUnionAll n E N (← mkTypeEq n E (← jlTuple n E (ps.take (np - 1) ++ [va])))
          if let some pN := pN then
            return some (← jlApplyType n E tt [pN])
          return some tt
    else if !(← isconcretetype E p) then
      break
  return none

mutual
/-- `typeof_tfunc(𝕃, t)`

Julia source: Compiler/src/tfuncs.jl:882-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function typeof_tfunc(𝕃::AbstractLattice, t)
    isa(t, Const) && return Const(typeof(t.val))
    t = widenconst(t)
    if isconstType(t)
        return Const(typeof(type_parameter(t)))
    elseif isTypeEq(t)
        # the value is only `== tp`, so its `typeof` is not pinned down (#61323)
    elseif isa(t, DataType)
        if isconcretetype(t)
            return Const(t)
        elseif t === Any
            return DataType
        else
            if t.name === Tuple.name
                tt = typeof_concrete_vararg(t)
                tt === nothing || return tt
            end
            return Type{<:t}
        end
    elseif isa(t, Union)
        a = widenconst(_typeof_tfunc(𝕃, t.a))
        b = widenconst(_typeof_tfunc(𝕃, t.b))
        return Union{a, b}
    elseif isa(t, UnionAll)
        u = unwrap_unionall(t)
        if isa(u, DataType) && !isabstracttype(u)
            if u.name === Tuple.name
                uu = typeof_concrete_vararg(u)
                if uu !== nothing
                    return rewrap_unionall(uu, t)
                end
            else
                return rewrap_unionall(Type{u}, t)
            end
        end
        return rewrap_unionall(widenconst(typeof_tfunc(𝕃, u)), t)
    end
    return DataType # typeof(anything)::DataType
end
```
-/
def typeofTfunc (n : Nat) (E : CEnv) (t : LElt) : CM LElt :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let .const v := t then return .const (typeOf v)
    let t ← widenconst n E t
    if isconstType t then
      return .const (typeOf (← typeParameter t))
    else if isTypeEq t then
      pure ()
    else if t.isDatatype then
      if ← isconcretetype E t then
        return .const t
      else if t == anyType then
        return .ty datatypeType
      else
        if t.name? == some tupleName then
          if let some tt ← typeofConcreteVararg n E t then return .ty tt
        let tv ← jlNewTypeVar typeofTypevarName t
        return .ty (← jlUnionAll n E tv (← mkTypeEq n E tv))
    else if let .union a b := t then
      let a ← widenconst n E (← typeofTfunc_ n E a)
      let b ← widenconst n E (← typeofTfunc_ n E b)
      return .ty (← jlUnion n E [a, b])
    else if t.isUnionall then
      let u := unwrapUnionall t
      if u.isDatatype && !(← isabstracttype E u) then
        if u.name? == some tupleName then
          if let some uu ← typeofConcreteVararg n E u then
            return .ty (← rewrapUnionallJ n E uu t)
        else
          return .ty (← rewrapUnionallJ n E (← mkTypeEq n E u) t)
      return .ty (← rewrapUnionallJ n E (← widenconst n E (← typeofTfunc n E (.ty u))) t)
    return .ty datatypeType

/-- `_typeof_tfunc(𝕃, t)`

Julia source: Compiler/src/tfuncs.jl:921-927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# helper function of `typeof_tfunc`, which accepts `TypeVar`
@nospecs function _typeof_tfunc(𝕃::AbstractLattice, t)
    if isa(t, TypeVar)
        return t.ub !== Any ? _typeof_tfunc(𝕃, t.ub) : DataType
    end
    return typeof_tfunc(𝕃, t)
end
```
-/
def typeofTfunc_ (n : Nat) (E : CEnv) (t : Val) : CM LElt :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let .typevar _ _ _ ub := t then
      return ← if ub != anyType then typeofTfunc_ n E ub else pure (.ty datatypeType)
    typeofTfunc n E (.ty t)
end

/-- `has_free_typevars_tfunc(𝕃, t)`

Julia source: Compiler/src/tfuncs.jl:930-944 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function has_free_typevars_tfunc(𝕃::AbstractLattice, t)
    isa(t, Const) && return Const(has_free_typevars(t.val))
    t = widenconst(t)
    if isType(t)
        p = type_parameter(t)
        # a free typevar in the lattice element stands for closed runtime values
        has_free_typevars(p) && return Bool
        return Const(has_free_typevars(p))
    elseif t === TypeVar
        return Const(true)
    elseif !hasintersect(t, Type) && !hasintersect(t, TypeVar) && !hasintersect(t, TypeofVararg)
        return Const(false)
    end
    return Bool
end
```
-/
def hasFreeTypevarsTfunc (n : Nat) (E : CEnv) (t : LElt) : CM LElt := do
  if let .const v := t then return constBool (hasFreeTypevars v)
  let t ← widenconst n E t
  if isType t then
    let p ← typeParameter t
    if hasFreeTypevars p then return .ty boolTy
    return constBool (hasFreeTypevars p)
  else if t == tvarType then
    return constBool true
  else if !(← hasintersect n E t typeTypeVal) && !(← hasintersect n E t tvarType) &&
      !(← hasintersect n E t varargType) then
    return constBool false
  return .ty boolTy

/-! ## `isa`, `<:` -/

/-- `isa_tfunc(𝕃, v, tt)`

Julia source: Compiler/src/tfuncs.jl:965-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function isa_tfunc(𝕃::AbstractLattice, v, tt)
    t, isexact = instanceof_tfunc(tt, true)
    if t === Bottom
        # check if t could be equivalent to typeof(Bottom), since that's valid in `isa`, but the set of `v` is empty
        # if `t` cannot have instances, it's also invalid on the RHS of isa
        hasintersect(widenconst(tt), Type) || return Union{}
        return Const(false)
    end
    if !has_free_typevars(t)
        if ⊑(𝕃, v, t)
            if isexact && isnotbrokensubtype(v, t)
                return Const(true)
            end
        else
            if isa(v, Const) || isa(v, Conditional)
                # this and the `isdispatchelem` below test for knowledge of a
                # leaftype appearing on the LHS (ensuring the isa is precise)
                return Const(false)
            end
            v = widenconst(v)
            isdispatchelem(v) && return Const(false)
            if !hasintersect(v, t)
                # similar to `isnotbrokensubtype` check above, `typeintersect(v, t)`
                # can't be trusted for kind types so we do an extra check here
                if !iskindtype(v)
                    return Const(false)
                end
            end
        end
    end
    # TODO: handle non-leaftype(t) by testing against lower and upper bounds
    return Bool
end
```
`isnotbrokensubtype` is `Compiler/src/typeutils.jl:38`. -/
def isaTfunc (n : Nat) (E : CEnv) (L : Lattice) (v tt : LElt) : CM LElt := do
  let (t, isexact, _, _) ← instanceofTfunc n E tt true
  if t == .bottom then
    if !(← hasintersect n E (← widenconst n E tt) typeTypeVal) then return .ty .bottom
    return constBool false
  if !hasFreeTypevars t then
    if ← sqsub n E L v (.ty t) then
      let isnotbrokensubtype : CM Bool := do
        if !iskindtype t then return true
        let .ty a := v | return true
        if !isType a then return true
        issub n E t a
      if ← andM (pure isexact) isnotbrokensubtype then
        return constBool true
    else
      if v.isConst || v.isConditional then
        return constBool false
      let v ← widenconst n E v
      if ← isdispatchelem E v then return constBool false
      if !(← hasintersect n E v t) then
        if !iskindtype v then
          return constBool false
  return .ty boolTy

/-- `isa_nothrow(𝕃, obj, typ)`

Julia source: Compiler/src/tfuncs.jl:1000-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function isa_nothrow(𝕃::AbstractLattice, obj, typ)
    ⊑ = partialorder(𝕃)
    return typ ⊑ Type
end
```
-/
def isaNothrow (n : Nat) (E : CEnv) (L : Lattice) (typ : LElt) : CM Bool :=
  sqsub n E L typ (.ty typeTypeVal)

/-- `subtype_tfunc(𝕃, a, b)`

Julia source: Compiler/src/tfuncs.jl:1005-1020 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function subtype_tfunc(𝕃::AbstractLattice, a, b)
    a, isexact_a = instanceof_tfunc(a, false)
    b, isexact_b = instanceof_tfunc(b, false)
    if !has_free_typevars(a) && !has_free_typevars(b)
        if a <: b
            if isexact_b || a === Bottom
                return Const(true)
            end
        else
            if isexact_a || (b !== Bottom && !hasintersect(a, b))
                return Const(false)
            end
        end
    end
    return Bool
end
```
-/
def subtypeTfunc (n : Nat) (E : CEnv) (a b : LElt) : CM LElt := do
  let (a, isexactA, _, _) ← instanceofTfunc n E a false
  let (b, isexactB, _, _) ← instanceofTfunc n E b false
  if !hasFreeTypevars a && !hasFreeTypevars b then
    if !a.isType || !b.isType then jlThrow "TypeError" "<:"
    if ← issub n E a b then
      if isexactB || a == .bottom then return constBool true
    else
      if isexactA || (b != .bottom && !(← hasintersect n E a b)) then return constBool false
  return .ty boolTy

/-- `subtype_nothrow(𝕃, lty, rty)`

Julia source: Compiler/src/tfuncs.jl:1023-1026 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function subtype_nothrow(𝕃::AbstractLattice, lty, rty)
    ⊑ = partialorder(𝕃)
    return lty ⊑ Type && rty ⊑ Type
end
```
-/
def subtypeNothrow (n : Nat) (E : CEnv) (L : Lattice) (lty rty : LElt) : CM Bool := do
  andM (sqsub n E L lty (.ty typeTypeVal)) (sqsub n E L rty (.ty typeTypeVal))

/-! ## `getfield` -/

/-- `_getfield_fieldindex(s::DataType, name::Const)`; `nv` is `name.val`.

Julia source: Compiler/src/tfuncs.jl:1187-1196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getfield_fieldindex(s::DataType, name::Const)
    nv = name.val
    if isa(nv, Symbol)
        nv = fieldindex(s, nv, false)
    end
    if isa(nv, Int)
        return nv
    end
    return nothing
end
```
-/
def getfieldFieldindex (T : TEnv) (s : Val) (nv : Val) : CM (Option Int) := do
  match nv with
  | .symbol sym => return some (Int.ofNat (← fieldindexDT T s sym))
  | .long k => return some k
  | _ => return none

/-- `isTypeDataType(t)`

Julia source: Compiler/src/typeutils.jl:14-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    isTypeDataType(@nospecialize t)::Bool

For a type `t` test whether ∀S s.t. `isa(S, rewrap_unionall(Core.TypeEgal{t}, ...))`,
we have `isa(S, DataType)`. In particular, if a statement is typed as `Core.TypeEgal{t}`
(potentially wrapped in some `UnionAll`), then we are guaranteed that this statement
will be a `DataType` at runtime. Note that this does not hold for a statement typed as
`Type{t}`, which may also be a `Union` or `UnionAll` rep that is `==` to `t` (#61323).
"""
function isTypeDataType(@nospecialize t)
    isType(t) && return false
    isa(t, DataType) || return false
    # Could be Union{} at runtime
    t === Core.TypeofBottom && return false
    # Return true if `t` is not covariant
    return t.name !== Tuple.name
end

```
-/
def isTypeDataTypeTf (t : Val) : Bool :=
  if isType t then false
  else match t with
    | .datatype name _ => t != typeofbottomType && name != tupleName
    | _ => false

/-- `_getfield_tfunc_const(sv, name::Const)`; `none` is `nothing`.

Julia source: Compiler/src/tfuncs.jl:1198-1215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getfield_tfunc_const(@nospecialize(sv), name::Const)
    nv = _getfield_fieldindex(typeof(sv), name)
    nv === nothing && return Bottom
    # relocated pointers change between processes, so their value can't be folded
    is_relocatable_ptr_field(Const(sv), name) && return nothing
    # `types` and `super` are write-once: non-const (filled lazily), but once
    # a defined value is observed it can never change, so folding it is sound
    if isa(sv, DataType) && (nv == DATATYPE_TYPES_FIELDINDEX || nv == DATATYPE_SUPER_FIELDINDEX) && isdefined(sv, nv)
        return Const(getfield(sv, nv))
    end
    if !isa(sv, Module) && isconst(typeof(sv), nv)
        if isdefined(sv, nv)
            return Const(getfield(sv, nv))
        end
        return Bottom
    end
    return nothing
end
```
`is_relocatable_ptr_field` (`Compiler/src/tfuncs.jl:2905-2924`) is `false` for a value that is
not a type object, a `TypeName` or a memory object; the model reports `unmodelled` for type objects
and memory objects (`Val` has no `TypeName`s). -/
def getfieldTfuncConst (n : Nat) (T : TEnv) (sv nv : Val) : CM (Option LElt) := do
  let E := T.E
  let some nv ← getfieldFieldindex T (typeOf sv) nv | return some (.ty .bottom)
  if sv.isType || sv.isTypevar then unmodelled "_getfield_tfunc_const on a type object"
  if let .mutableRef (.datatype name _) _ := sv then
    if name == "Core.GenericMemory" || name == "Core.GenericMemoryRef" then
      unmodelled "is_relocatable_ptr_field on a memory object"
  if !sv.isModule then
    if ← isconstIdx T (typeOf sv) nv then
      if ← isdefinedRT E sv nv then
        return some (.const (← getfieldRT sv nv))
      return some (.ty .bottom)
  let _ := n
  return none

/-- `_getfield_tfunc(::JLTypeLattice, s00, name, setfield)`

Julia source: Compiler/src/tfuncs.jl:1286-1405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function _getfield_tfunc(𝕃::JLTypeLattice, s00, name, setfield::Bool)
    s = unwrap_unionall(s00)
    if isa(s, Union)
        return tmerge(_getfield_tfunc(𝕃, rewrap_unionall(s.a, s00), name, setfield),
                      _getfield_tfunc(𝕃, rewrap_unionall(s.b, s00), name, setfield))
    end
    if isType(s)
        if isconstType(s)
            sv = type_parameter(s)
            if isa(name, Const)
                r = _getfield_tfunc_const(sv, name)
                r !== nothing && return r
            end
            s = typeof(sv)
        else
            sv = type_parameter(s)
            if isa(sv, DataType) && isa(name, Const) && name.val === :super &&
               # read without forcing: on a deferred instantiation whose slot
               # is still unset the modeled `getfield` throws, so no precision
               # is lost by falling through (see issue #61347)
               isdefined(sv, :super) &&
               (svsuper = getfield(sv, :super); !has_free_typevars(svsuper))
                # only `DataType` reps reach `.super` without throwing, and the
                # `.super`s of `==`-equal `DataType`s are `==`-equal (if not egal)
                return Type{svsuper}
            end
            if isTypeDataType(sv) && isa(name, Const)
                nv = _getfield_fieldindex(DataType, name)
                # neither a `Symbol` nor an `Int`, so the access throws for any rep
                nv === nothing && return Bottom
                if nv == DATATYPE_NAME_FIELDINDEX
                    # N.B. This only works for fields that do not depend on type
                    # parameters (which we do not know here).
                    rt = Const(sv.name)
                else
                    rt = _getfield_tfunc(𝕃, DataType, name, setfield)
                end
                # the value may also be a `UnionAll` or `Union` rep that is `==` to `sv`
                # (#61323), which reaches the fields of its own type instead
                rt = tmerge(rt, _getfield_tfunc(𝕃, UnionAll, name, setfield))
                return tmerge(rt, _getfield_tfunc(𝕃, Union, name, setfield))
            end
        end
    end
    isa(s, DataType) || return Any
    isabstracttype(s) && return Any
    if s <: Tuple && !hasintersect(widenconst(name), Int)
        return Bottom
    end
    if s <: Module
        setfield && return Bottom
        hasintersect(widenconst(name), Symbol) || return Bottom
        return Any
    end
    if s.name === _NAMEDTUPLE_NAME && !isconcretetype(s)
        if isa(name, Const) && isa(name.val, Symbol)
            if isa(s.parameters[1], Tuple)
                name = Const(Int(ccall(:jl_field_index, Cint, (Any, Any, Cint), s, name.val, false)+1))
            else
                name = Int
            end
        elseif Symbol ⊑ name
            name = Int
        end
        _ts = unwraptv(s.parameters[2])
        _ts = rewrap_unionall(_ts, s00)
        if !(_ts <: Tuple)
            return Any
        end
        return _getfield_tfunc(𝕃, _ts, name, setfield)
    end
    ftypes = datatype_fieldtypes(s)
    nf = length(ftypes)
    # If no value has this type, then this statement should be unreachable.
    # Bail quickly now.
    if !has_concrete_subtype(s) || nf == 0
        return Bottom
    end
    if isa(name, Conditional)
        return Bottom # can't index fields with Bool
    end
    if !isa(name, Const)
        name = widenconst(name)
        if !(Int <: name || Symbol <: name)
            return Bottom
        end
        if nf == 1
            fld = 1
        else
            # union together types of all fields
            t = Bottom
            for i in 1:nf
                _ft = unwrapva(ftypes[i])
                valid_as_lattice(_ft, true) || continue
                setfield && isconst(s, i) && continue
                t = tmerge(t, rewrap_unionall(_ft, s00))
                t === Any && break
            end
            return t
        end
    else
        fld = _getfield_fieldindex(s, name)
        fld === nothing && return Bottom
    end
    if s <: Tuple && fld >= nf && isvarargtype(ftypes[nf])
        R = unwrapva(ftypes[nf])
    else
        if fld < 1 || fld > nf
            return Bottom
        elseif setfield && isconst(s, fld)
            return Bottom
        end
        R = ftypes[fld]
        valid_as_lattice(R, true) || return Bottom
        if isempty(s.parameters)
            return R
        end
    end
    return rewrap_unionall(R, s00)
end
```
`isdefined(sv, :super)` is true for every `DataType` the model represents. -/
def getfieldTfuncJL (n : Nat) (T : TEnv) (s00 name : LElt) (setfield : Bool) : CM LElt :=
  let E := T.E
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let .ty s00t := s00 | return .ty anyType
    let mut s := unwrapUnionall s00t
    if let .union a b := s then
      return ← tmergeFallback n E
        (← getfieldTfuncJL n T (.ty (← rewrapUnionallJ n E a s00t)) name setfield)
        (← getfieldTfuncJL n T (.ty (← rewrapUnionallJ n E b s00t)) name setfield)
    if isType s then
      if isconstType s then
        let sv ← typeParameter s
        if let .const nv := name then
          if let some r ← getfieldTfuncConst n T sv nv then return r
        s := typeOf sv
      else
        let sv ← typeParameter s
        if sv.isDatatype then
          if let .const (.symbol "super") := name then
            let svsuper ← supertypeDT n E sv
            if !hasFreeTypevars svsuper then
              return .ty (← mkTypeEq n E svsuper)
        if isTypeDataTypeTf sv then
          if let .const nv := name then
            let some nv ← getfieldFieldindex T datatypeType nv | return .ty .bottom
            let rt ← if nv == Int.ofNat (← fieldindexDT T datatypeType "name") then
                unmodelled "Const(sv.name): a TypeName"
              else getfieldTfuncJL n T (.ty datatypeType) name setfield
            let rt ← tmergeFallback n E rt (← getfieldTfuncJL n T (.ty unionallType) name setfield)
            return ← tmergeFallback n E rt (← getfieldTfuncJL n T (.ty uniontypeType) name setfield)
    let .datatype sname sparams := s | return .ty anyType
    if ← isabstracttype E s then return .ty anyType
    if ← issub n E s anytupleType then
      if !(← hasintersect n E (← widenconst n E name) longType) then
        return .ty .bottom
    if ← issub n E s moduleType then
      if setfield then return .ty .bottom
      if !(← hasintersect n E (← widenconst n E name) symbolType) then return .ty .bottom
      return .ty anyType
    if sname == namedTupleName && !(← isconcretetype E s) then
      unmodelled "_getfield_tfunc on an abstract NamedTuple"
    let ftypes ← datatypeFieldtypes E s
    let nf := ftypes.length
    if !(← hasConcreteSubtype n E.types s) || nf == 0 then
      return .ty .bottom
    if name.isConditional then
      return .ty .bottom
    let mut fld : Int := 0
    if let .const nv := name then
      match ← getfieldFieldindex T s nv with
      | some k => fld := k
      | none => return .ty .bottom
    else
      let nameW ← widenconst n E name
      if !(← orM (issub n E longType nameW) (issub n E symbolType nameW)) then
        return .ty .bottom
      if nf == 1 then
        fld := 1
      else
        let mut t : LElt := .ty .bottom
        for (ft, i) in ftypes.zip (List.range' 1 nf) do
          let ft := unwrapva ft
          if !(← validAsLattice n E ft true) then continue
          if setfield then
            if ← isconstIdx T s i then continue
          t ← tmergeFallback n E t (.ty (← rewrapUnionallJ n E ft s00t))
          if let .ty tt := t then
            if tt == anyType then break
        return t
    let mut R : Val := .bottom
    if (← issub n E s anytupleType) && fld ≥ nf && ftypes.getLast!.isVararg then
      R := unwrapva ftypes.getLast!
    else
      if fld < 1 || fld > nf then
        return .ty .bottom
      if setfield then
        if ← isconstIdx T s fld then return .ty .bottom
      R := ftypes[(fld - 1).toNat]!
      if !(← validAsLattice n E R true) then return .ty .bottom
      if sparams.isEmpty then
        return .ty R
    return .ty (← rewrapUnionallJ n E R s00t)

/-- `_getfield_tfunc(𝕃, s00, name, setfield)` for the layers above `JLTypeLattice`.

Julia source: Compiler/src/tfuncs.jl:1217-1284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
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
        # N.B.: Do not use `PartialTask.fetch_type` to refine any field load here (e.g.
        # `:result`). Task fields are mutable, so `fetch_type` is not an invariant of the
        # current field contents; it is only sound as the *checked* side of the `typeassert`
        # in `fetch` (via `task_result_type_tfunc`). Refining the load itself would let the
        # optimizer prove that typeassert and delete it, turning a field mutation into
        # silent type confusion instead of a runtime `TypeError`.
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
-/
def getfieldTfuncL (n : Nat) (T : TEnv) (L : Lattice) (s00 name : LElt) (setfield : Bool) :
    CM LElt :=
  let E := T.E
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match L with
    | .inference p =>
      let s00 ← if s00.isLimited then pure (.ty (← widenconst n E s00)) else pure s00
      getfieldTfuncL n T p s00 name setfield
    | .conditionals p | .interConditionals p =>
      if s00.isAnyConditional then return .ty .bottom
      getfieldTfuncL n T p s00 name setfield
    | .mustAliases p | .interMustAliases p =>
      getfieldTfuncL n T p (← widenmustalias s00) (← widenmustalias name) setfield
    | .partials p =>
      let mut s00 := s00
      if let .partialStruct typ _ fields _ _ := s00 then
        let s := typ
        let sty := unwrapUnionall s
        if !sty.isDatatype then jlThrow "TypeError" "typeassert DataType"
        if let .const nv := name then
          if let some nv ← getfieldFieldindex T sty nv then
            if nv < 1 then
              return .ty .bottom
            else if nv ≤ fields.length then
              if setfield then
                if ← isconstIdx T sty nv then return .ty .bottom
              return unwrapvaElt fields[(nv - 1).toNat]!
        s00 := .ty s
      else if s00.isPartialTask then
        s00 := .ty taskType
      getfieldTfuncL n T p s00 name setfield
    | .consts =>
      let mut s00 := s00
      if let .const sv := s00 then
        if let .const nv := name then
          if sv.isModule then
            if setfield then return .ty .bottom
            if nv.isSymbol then return .ty anyType
            return .ty .bottom
          if let some r ← getfieldTfuncConst n T sv nv then return r
        s00 := .ty (← widenconst n E s00)
      getfieldTfuncL n T .jlType s00 name setfield
    | .jlType => getfieldTfuncJL n T s00 name setfield

/-- `getfield_tfunc(𝕃, s00, name[, boundscheck_or_order[, boundscheck]])`

Julia source: Compiler/src/tfuncs.jl:1169-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function getfield_tfunc(𝕃::AbstractLattice, s00, name, boundscheck_or_order)
    if !isvarargtype(boundscheck_or_order)
        t = widenconst(boundscheck_or_order)
        hasintersect(t, Symbol) || hasintersect(t, Bool) || return Bottom
    end
    return getfield_tfunc(𝕃, s00, name)
end
@nospecs function getfield_tfunc(𝕃::AbstractLattice, s00, name, order, boundscheck)
    hasintersect(widenconst(order), Symbol) || return Bottom
    if !isvarargtype(boundscheck)
        hasintersect(widenconst(boundscheck), Bool) || return Bottom
    end
    return getfield_tfunc(𝕃, s00, name)
end
@nospecs function getfield_tfunc(𝕃::AbstractLattice, s00, name)
    _getfield_tfunc(𝕃, s00, name, false)
end
```
-/
def getfieldTfunc (n : Nat) (T : TEnv) (L : Lattice) (args : List LElt) : CM LElt := do
  let E := T.E
  match args with
  | [s00, name] => getfieldTfuncL n T L s00 name false
  | [s00, name, bo] =>
    if !bo.isVarargElt then
      let t ← widenconst n E bo
      if !(← orM (hasintersect n E t symbolType) (hasintersect n E t boolTy)) then
        return .ty .bottom
    getfieldTfuncL n T L s00 name false
  | [s00, name, order, bc] =>
    if !(← hasintersect n E (← widenconst n E order) symbolType) then return .ty .bottom
    if !bc.isVarargElt then
      if !(← hasintersect n E (← widenconst n E bc) boolTy) then return .ty .bottom
    getfieldTfuncL n T L s00 name false
  | _ => jlThrow "MethodError" "getfield_tfunc"

/-- `getfield_boundscheck(argtypes)`: `:on`, `:off`, `:unknown` or `:unsafe`.

Julia source: Compiler/src/tfuncs.jl:1045-1069 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getfield_boundscheck(argtypes::Vector{Any})
    if length(argtypes) == 2
        isvarargtype(argtypes[2]) && return :unsafe
        return :on
    elseif length(argtypes) == 3
        boundscheck = argtypes[3]
        isvarargtype(boundscheck) && return :unsafe
        if widenconst(boundscheck) === Symbol
            return :on
        end
    elseif length(argtypes) == 4
        boundscheck = argtypes[4]
        isvarargtype(boundscheck) && return :unsafe
    else
        return :unsafe
    end
    boundscheck = widenconditional(boundscheck)
    if widenconst(boundscheck) === Bool
        if isa(boundscheck, Const)
            return boundscheck.val::Bool ? :on : :off
        end
        return :unknown # including a case when specified as `:boundscheck`
    end
    return :unsafe
end
```
-/
def getfieldBoundscheckTail (n : Nat) (E : CEnv) (bc : LElt) : CM String := do
  let bc ← widenconditional bc
  if (← widenconst n E bc) == boolTy then
    if let .const v := bc then
      match asBool? v with
      | some b => return if b then "on" else "off"
      | none => jlThrow "TypeError" "typeassert Bool"
    return "unknown"
  return "unsafe"

def getfieldBoundscheck (n : Nat) (E : CEnv) (argtypes : List LElt) : CM String := do
  match argtypes with
  | [_, a2] => return if a2.isVarargElt then "unsafe" else "on"
  | [_, _, bc] =>
    if bc.isVarargElt then return "unsafe"
    if (← widenconst n E bc) == symbolType then return "on"
    getfieldBoundscheckTail n E bc
  | [_, _, _, bc] =>
    if bc.isVarargElt then return "unsafe"
    getfieldBoundscheckTail n E bc
  | _ => return "unsafe"

/-- `try_compute_fieldidx(typ, field)` on a `DataType`.

Julia source: Compiler/src/tfuncs.jl:1028-1043 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function try_compute_fieldidx(@nospecialize(typ), @nospecialize(field))
    typ = unwraptv(typ)
    typ isa Union || typ isa UnionAll || typ isa DataType || return nothing
    if isa(field, Symbol)
        field = fieldindex(typ, field, false)
        field == 0 && return nothing
    elseif isa(field, Int)
        # Numerical field name can only be of type `Int`
        max_fields = fieldcount_noerror(typ)
        max_fields === nothing && return nothing
        (1 <= field <= max_fields) || return nothing
    else
        return nothing
    end
    return field
end
```
-/
def tryComputeFieldidx (n : Nat) (T : TEnv) (typ field : Val) : CM (Option Int) := do
  let typ ← unwraptv n typ
  if !(typ.isUnion || typ.isUnionall || typ.isDatatype) then return none
  match field with
  | .symbol sym =>
    if !typ.isDatatype then unmodelled "fieldindex on a Union or UnionAll"
    let k ← fieldindexDT T typ sym
    if k == 0 then return none
    return some k
  | .long k =>
    let some maxFields ← fieldcountNoerror T.E typ | return none
    if !(1 ≤ k && k ≤ maxFields) then return none
    return some k
  | _ => return none

/-- `getfield_nothrow(𝕃, s00, name, boundscheck::Bool)`

Julia source: Compiler/src/tfuncs.jl:1092-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function getfield_nothrow(𝕃::AbstractLattice, s00, name, boundscheck::Bool)
    # If we don't have boundscheck off and don't know the field, don't even bother
    if boundscheck
        isa(name, Const) || return false
    end

    ⊑ = partialorder(𝕃)

    # If we have s00 being a const, we can potentially refine our type-based analysis above
    if isa(s00, Const) || isconstType(s00) || isa(s00, PartialStruct)
        if isa(s00, Const)
            sv = s00.val
            sty = typeof(sv)
            nflds = nfields(sv)
            ismod = sv isa Module
        elseif isa(s00, PartialStruct)
            sty = unwrap_unionall(s00.typ)
            nflds = fieldcount_noerror(sty)
            ismod = false
        else
            sv = type_parameter(s00)
            sty = typeof(sv)
            nflds = nfields(sv)
            ismod = sv isa Module
        end
        if isa(name, Const)
            nval = name.val
            if !isa(nval, Symbol)
                ismod && return false
                isa(nval, Int) || return false
            end
            return isdefined_tfunc(𝕃, s00, name) === Const(true)
        end

        # If bounds checking is disabled and all fields are assigned,
        # we may assume that we don't throw
        @assert !boundscheck
        ismod && return false
        name ⊑ Int || name ⊑ Symbol || return false
        sty.name.n_uninitialized == 0 && return true
        nflds === nothing && return false
        for i = (datatype_min_ninitialized(sty)+1):nflds
            isdefined_tfunc(𝕃, s00, Const(i)) === Const(true) || return false
        end
        return true
    end

    s0 = widenconst_split(s00)
    s = unwrap_unionall(s0)
    if isa(s, Union)
        return getfield_nothrow(𝕃, rewrap_unionall(s.a, s00), name, boundscheck) &&
               getfield_nothrow(𝕃, rewrap_unionall(s.b, s00), name, boundscheck)
    elseif isa(s, Core.TypeEgal) && isTypeDataType(type_parameter(s))
        s = s0 = DataType
    end
    if isa(s, DataType)
        # Can't say anything about abstract types
        isabstracttype(s) && return false
        # If all fields are always initialized, and bounds check is disabled,
        # we can assume we don't throw
        if !boundscheck && s.name.n_uninitialized == 0
            name ⊑ Int || name ⊑ Symbol || return false
            return true
        end
        # Else we need to know what the field is
        isa(name, Const) || return false
        field = try_compute_fieldidx(s, name.val)
        field === nothing && return false
        isfieldatomic(s, field) && return false # TODO: currently we're only testing for ordering === :not_atomic
        field <= datatype_min_ninitialized(s) && return true
        # `try_compute_fieldidx` already check for field index bound.
        !isvatuple(s) && isbitstype(fieldtype(s0, field)) && return true
    end

    return false
end
```
-/
def getfieldNothrow4 (n : Nat) (T : TEnv) (L : Lattice) (s00 name : LElt) (boundscheck : Bool) :
    CM Bool :=
  let E := T.E
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if boundscheck then
      if !name.isConst then return false
    let constType := match s00 with | .ty t => isconstType t | _ => false
    if s00.isConst || constType || s00.isPartialStruct then
      let (sty, nflds, ismod) ← match s00 with
        | .const sv => pure (typeOf sv, some (← nfieldsRT E sv), sv.isModule)
        | .partialStruct typ .. =>
          let sty := unwrapUnionall typ
          pure (sty, ← fieldcountNoerror E sty, false)
        | .ty t => do
          let sv ← typeParameter t
          pure (typeOf sv, some (← nfieldsRT E sv), sv.isModule)
        | _ => jlThrow "UndefVarError" "sv"
      if let .const nval := name then
        if !nval.isSymbol then
          if ismod then return false
          if !nval.isLong then return false
        return isConstTrue (← isdefinedTfunc n T L s00 name)
      if boundscheck then jlThrow "AssertionError" "!boundscheck"
      if ismod then return false
      if !(← orM (sqsub n E L name (.ty longType)) (sqsub n E L name (.ty symbolType))) then
        return false
      let .datatype stn _ := sty | jlThrow "ErrorException" "sty.name"
      if (← T.tn stn).nUninit == 0 then return true
      let some nflds := nflds | return false
      for i in List.range' ((← datatypeMinNinitialized E sty) + 1)
          (nflds - (← datatypeMinNinitialized E sty)) do
        if !isConstTrue (← isdefinedTfunc n T L s00 (.const (.long i))) then return false
      return true
    let s0 ← widenconstSplit n E s00
    let mut s0 := s0
    let mut s := unwrapUnionall s0
    let s00t : Val := match s00 with | .ty t => t | _ => .bottom
    if let .union a b := s then
      let ra ← rewrapUnionallJ n E a s00t
      let rb ← rewrapUnionallJ n E b s00t
      if !(← getfieldNothrow4 n T L (.ty ra) name boundscheck) then return false
      return ← getfieldNothrow4 n T L (.ty rb) name boundscheck
    else if isTypeEgal s && isTypeDataTypeTf s.someTypeT then
      s := datatypeType
      s0 := datatypeType
    if let .datatype sname _ := s then
      if ← isabstracttype E s then return false
      if !boundscheck then
        if (← T.tn sname).nUninit == 0 then
          if !(← orM (sqsub n E L name (.ty longType)) (sqsub n E L name (.ty symbolType))) then
            return false
          return true
      let .const nv := name | return false
      let some field ← tryComputeFieldidx n T s nv | return false
      if ← isfieldatomicIdx T s field then return false
      if field ≤ (← datatypeMinNinitialized E s) then return true
      if !isvatuple s then
        if !s0.isDatatype then unmodelled "fieldtype on a UnionAll"
        if ← isbitstype n E (← fieldtypeIdx E s0 field.toNat) then return true
    return false

/-- `getfield_nothrow(𝕃, argtypes, boundscheck)`

Julia source: Compiler/src/tfuncs.jl:1071-1091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getfield_nothrow(𝕃::AbstractLattice, argtypes::Vector{Any}, boundscheck::Symbol=getfield_boundscheck(argtypes))
    boundscheck === :unsafe && return false
    ordering = Const(:not_atomic)
    if length(argtypes) == 3
        isvarargtype(argtypes[3]) && return false
        if widenconst(argtypes[3]) !== Bool
            ordering = argtypes[3]
        end
    elseif length(argtypes) == 4
        ordering = argtypes[3]
    elseif length(argtypes) ≠ 2
        return false
    end
    isa(ordering, Const) || return false
    ordering = ordering.val
    isa(ordering, Symbol) || return false
    if ordering !== :not_atomic # TODO: this is assuming not atomic
        return false
    end
    return getfield_nothrow(𝕃, argtypes[1], argtypes[2], !(boundscheck === :off))
end
```
-/
def getfieldNothrow (n : Nat) (T : TEnv) (L : Lattice) (argtypes : List LElt) : CM Bool := do
  let E := T.E
  let boundscheck ← getfieldBoundscheck n E argtypes
  if boundscheck == "unsafe" then return false
  let mut ordering : LElt := .const (.symbol "not_atomic")
  match argtypes with
  | [_, _, a3] =>
    if a3.isVarargElt then return false
    if (← widenconst n E a3) != boolTy then ordering := a3
  | [_, _, a3, _] => ordering := a3
  | [_, _] => pure ()
  | _ => return false
  let .const ov := ordering | return false
  let .symbol o := ov | return false
  if o != "not_atomic" then return false
  getfieldNothrow4 n T L argtypes[0]! argtypes[1]! (boundscheck != "off")

/-! ## `tuple` -/

/-- `partialstruct_init_undefs(typ, fields)`

Julia source: base/coreir.jl:75-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function partialstruct_init_undefs(@nospecialize(typ), fields::Vector{Any})
    nf = length(fields)
    minf = datatype_min_ninitialized(typ)
    for i = 1:minf
        if fields[i] === Union{}
            return nothing # disallow runtime-invalid `PartialStruct`
        end
    end
    undefs = Union{Nothing,Bool}[nothing for _ in 1:nf]
    for i in 1:minf
        undefs[i] = false
    end
    for i = minf+1:nf
        if fields[i] === Union{}
            undefs[i] = true
        end
    end
    return undefs
end
```
-/
def partialstructInitUndefs (E : CEnv) (typ : Val) (fields : List LElt) :
    CM (Option (List (Option Bool))) := do
  let nf := fields.length
  let minf ← datatypeMinNinitialized E typ
  for i in List.range' 1 minf do
    if (← jlIndex fields i).isBottom then return none
  return some ((List.range' 1 nf).map fun i =>
    if i ≤ minf then some false
    else if (fields[i - 1]!).isBottom then some true else none)

/-- `is_all_const_arg(argtypes, 1)` and `collect_const_args(argtypes, 1)`.

Julia source: Compiler/src/abstractinterpretation.jl:1107-1128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_all_const_arg(argtypes::Vector{Any}, start::Int)
    for i = start:length(argtypes)
        argtype = widenslotwrapper(argtypes[i])
        is_const_argtype(argtype) || return false
    end
    return true
end

is_const_argtype(@nospecialize argtype) = isa(argtype, Const) || isconstType(argtype) || issingletontype(argtype)

any_conditional(argtypes::Vector{Any}) = any(@nospecialize(x)->isa(x, Conditional), argtypes)
any_conditional(arginfo::ArgInfo) = any_conditional(arginfo.argtypes)

collect_const_args(arginfo::ArgInfo, start::Int) = collect_const_args(arginfo.argtypes, start)
function collect_const_args(argtypes::Vector{Any}, start::Int)
    return Any[ let a = widenslotwrapper(argtypes[i])
                    isa(a, Const) ? a.val :
                    isconstType(a) ? type_parameter(a) :
                    (a::DataType).instance
                end for i = start:length(argtypes) ]
end

```
-/
def isConstArgtype (n : Nat) (E : CEnv) (a : LElt) : CM Bool := do
  match a with
  | .const _ => return true
  | .ty t => orM (pure (isconstType t)) (issingletontype n E t)
  | _ => return false

def isAllConstArg (n : Nat) (E : CEnv) (argtypes : List LElt) : CM Bool := do
  for a in argtypes do
    if !(← isConstArgtype n E (← widenslotwrapper a)) then return false
  return true

def collectConstArgs (E : CEnv) (argtypes : List LElt) : CM (List Val) :=
  argtypes.mapM fun a => do
    match ← widenslotwrapper a with
    | .const v => pure v
    | .ty t => if isconstType t then typeParameter t else pure (singletonInstance E t)
    | _ => jlThrow "TypeError" "typeassert DataType"

/-- `tuple(xs...)` (`jl_f_tuple`, `src/builtins.c:1125-1130`): a tuple value of type
`Tuple{typeof.(xs)...}`. -/
def tupleRT (n : Nat) (E : CEnv) (xs : List Val) : CM Val := do
  if xs.isEmpty then return .imm emptytupleType []
  return .imm (← jlTuple n E (xs.map typeOf)) xs

/-- The parameter loop of `tuple_tfunc` (`Compiler/src/tfuncs.jl:2318-2361`), on the argument
types left after the `Vararg{Union{}}` drop and the all-constant check: the tuple parameters,
`anyinfo` and the updated argument types, or `none` for the `return Bottom` branch. -/
def tupleTfuncParams (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt) :
    CM (Option (List Val × Bool × List LElt)) := do
  let mut params : List Val := []
  let mut anyinfo := false
  let mut newArgtypes : List LElt := []
  for x in argtypes do
    let mut x := x
    if ← hasNontrivialExtendedInfo n E L x then
      anyinfo := true
    else
      if !x.isVarargElt then
        x := .ty (← widenconstSplit n E x)
    newArgtypes := newArgtypes ++ [x]
    if let .const v := x then
      params := params ++ [typeOf v]
    else
      let xv ← if x.isVarargElt then (match x with | .ty v => pure v | _ => pure anyType)
        else widenconstSplit n E x
      if isTypeEgal xv then
        anyinfo := true
        params := params ++ [typeOf (← typeParameter xv)]
      else if isTypeEq xv then
        anyinfo := true
        let xparam ← typeParameter xv
        params := params ++ [if xparam == .bottom then typeOf xparam else typeTypeVal]
      else if iskindtype xv then
        params := params ++ [xv]
      else
        let hasType ← if xv.isVararg then pure false else hasintersect n E xv typeTypeVal
        if hasType then
          params := params ++ [← jlUnion n E [xv, typeTypeVal]]
        else if xv == .bottom then
          return none
        else
          params := params ++ [xv]
  return some (params, anyinfo, newArgtypes)

/-- The `pop!` of a trailing `Vararg{Union{}}` in `tuple_tfunc` (`Compiler/src/tfuncs.jl:2308-2314`). -/
def tupleDropBottomVararg (argtypes : List LElt) : List LElt :=
  match argtypes.getLast? with
  | some (.ty (.vararg va _)) => if va.getD anyType == .bottom then argtypes.dropLast else argtypes
  | _ => argtypes

/-- `tuple_tfunc(𝕃, argtypes)`

Julia source: Compiler/src/tfuncs.jl:2303-2366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# convert the dispatch tuple type argtype to the real (concrete) type of
# the tuple of those values
function tuple_tfunc(𝕃::AbstractLattice, argtypes::Vector{Any})
    isempty(argtypes) && return Const(())
    argtypes = anymap(widenslotwrapper, argtypes)
    if isvarargtype(argtypes[end]) && unwrapva(argtypes[end]) === Union{}
        # Drop the Vararg in Tuple{...,Vararg{Union{}}} since it must be length 0.
        # If there is a Vararg num also, it must be a TypeVar, and it must be
        # zero, but that generally shouldn't show up here, since it implies a
        # UnionAll context is missing around this.
        pop!(argtypes)
    end
    if is_all_const_arg(argtypes, 1) # repeated from builtin_tfunction for the benefit of callers that use this tfunc directly
        return Const(tuple(collect_const_args(argtypes, 1)...))
    end
    params = Vector{Any}(undef, length(argtypes))
    anyinfo = false
    for i in 1:length(argtypes)
        x = argtypes[i]
        if has_nontrivial_extended_info(𝕃, x)
            anyinfo = true
        else
            if !isvarargtype(x)
                x = widenconst_split(x)
            end
            argtypes[i] = x
        end
        if isa(x, Const)
            params[i] = typeof(x.val)
        else
            x = isvarargtype(x) ? x : widenconst_split(x)
            # since there don't exist any values whose runtime type are `Tuple{Type{...}}`,
            # here we should turn such `Type{...}`-parameters to valid parameters, e.g.
            # (::Type{Int},) -> Tuple{DataType} (or PartialStruct for more accuracy)
            # (::Union{Type{Int32},Type{Int64}}) -> Tuple{Type}
            if isTypeEgal(x)
                anyinfo = true
                params[i] = typeof(type_parameter(x))
            elseif isTypeEq(x)
                anyinfo = true
                xparam = type_parameter(x)
                # an `==`-only type value has no pinned `typeof` (#61323), except
                # `Type{Union{}}` whose only value is `Union{}`
                if xparam === Bottom
                    params[i] = typeof(xparam)
                else
                    params[i] = Type
                end
            elseif iskindtype(x)
                params[i] = x
            elseif !isvarargtype(x) && hasintersect(x, Type)
                params[i] = Union{x, Type}
            elseif x === Union{}
                return Bottom # argtypes is malformed, but try not to crash
            else
                params[i] = x
            end
        end
    end
    typ = Tuple{params...}
    # replace a singleton type with its equivalent Const object
    issingletontype(typ) && return Const(typ.instance)
    return anyinfo ? PartialStruct(𝕃, typ, partialstruct_init_undefs(typ, argtypes)::Vector, argtypes) : typ
end
```
-/
def tupleTfunc (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt) : CM LElt := do
  if argtypes.isEmpty then return .const (.imm emptytupleType [])
  let argtypes := tupleDropBottomVararg (← argtypes.mapM widenslotwrapper)
  if ← isAllConstArg n E argtypes then
    return .const (← tupleRT n E (← collectConstArgs E argtypes))
  let some (params, anyinfo, newArgtypes) ← tupleTfuncParams n E L argtypes
    | return .ty .bottom
  let typ ← jlTuple n E params
  if ← issingletontype n E typ then return .const (singletonInstance E typ)
  if anyinfo then
    let some undefs ← partialstructInitUndefs E typ newArgtypes
      | jlThrow "TypeError" "typeassert Vector"
    return ← mkPartialStruct n E typ undefs newArgtypes
  return .ty typ

/-! ## `typeassert` -/

/-- The `getfield_tfunc` and `tuple_tfunc` calls of `tmeet(::PartialsLattice, ...)`. -/
def tfuncTmeetOps (n : Nat) (T : TEnv) : TmeetOps where
  getfieldTfuncWiden L t i := do
    widenconst n T.E (← getfieldTfunc n T L [.ty t, .const (.long i)])
  tupleTfunc L fields := tupleTfunc n T.E L fields

/-- `typeassert_tfunc(𝕃, v, t)`

Julia source: Compiler/src/tfuncs.jl:947-951 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function typeassert_tfunc(𝕃::AbstractLattice, v, t)
    t = instanceof_tfunc(t, true)[1]
    t === Any && return v
    return tmeet(𝕃, v, t)
end
```
-/
def typeassertTfunc (n : Nat) (T : TEnv) (L : Lattice) (v t : LElt) : CM LElt := do
  let (t, _, _, _) ← instanceofTfunc n T.E t true
  if t == anyType then return v
  tmeet (tfuncTmeetOps n T) n T.E L v t

/-- `typeassert_nothrow(𝕃, v, t)`

Julia source: Compiler/src/tfuncs.jl:954-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecs function typeassert_nothrow(𝕃::AbstractLattice, v, t)
    ⊑ = partialorder(𝕃)
    # ty, exact = instanceof_tfunc(t, true)
    # return exact && v ⊑ ty
    if (isType(t) && !has_free_typevars(t) && v ⊑ type_parameter(t)) ||
        (isa(t, Const) && isa(t.val, Type) && v ⊑ t.val)
        return true
    end
    return false
end
```
-/
def typeassertNothrow (n : Nat) (E : CEnv) (L : Lattice) (v t : LElt) : CM Bool := do
  if let .ty tt := t then
    if isType tt && !hasFreeTypevars tt then
      if ← sqsub n E L v (.ty (← typeParameter tt)) then return true
  if let .const tv := t then
    if tv.isType then
      if ← sqsub n E L v (.ty tv) then return true
  return false

/-! ## Dispatch -/

/-- The builtins this model covers, by name. -/
def modelledBuiltins : List String :=
  ["throw", "ifelse", "===", "isdefined", "nfields", "svec", "typeof", "has_free_typevars",
   "typeassert", "isa", "<:", "getfield", "tuple"]

/-- `_PURE_BUILTINS`, and the builtins in both `_CONSISTENT_BUILTINS` and
`_EFFECT_FREE_BUILTINS`, restricted to the modelled builtins.

Julia source: Compiler/src/tfuncs.jl:2714-2779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _PURE_BUILTINS = Any[
    tuple,
    svec,
    ===,
    typeof,
    has_free_typevars,
    nfields,
]

const _CONSISTENT_BUILTINS = Any[
    tuple, # Tuple is immutable, thus tuples of egal arguments are egal
    svec,  # SimpleVector is immutable, thus svecs of egal arguments are egal
    ===,
    typeof,
    has_free_typevars,
    nfields,
    fieldtype,
    apply_type,
    isa,
    UnionAll,
    Core.bitsizeof,
    Core.sizeof,
    Core.ifelse,
    (<:),
    typeassert,
    throw,
    Core.throw_methoderror,
    setfield!,
    donotdelete,
    memoryrefnew,
    memoryrefoffset,
    Core._svec_len,
    Core._svec_ref,
]

# known to be effect-free (but not necessarily nothrow)
const _EFFECT_FREE_BUILTINS = [
    fieldtype,
    apply_type,
    isa,
    UnionAll,
    getfield,
    Core.memorynew,
    memoryrefnew,
    memoryrefoffset,
    memoryrefget,
    const_memoryrefget,
    memoryref_isassigned,
    isdefined,
    Core.bitsizeof,
    Core.sizeof,
    Core.ifelse,
    Core._typevar,
    (<:),
    typeassert,
    throw,
    Core.throw_methoderror,
    getglobal,
    Core.getglobal_partition,
    Core.isdefinedglobal_partition,
    compilerbarrier,
    Core._svec_len,
    Core._svec_ref,
    Core.task_result_type,
]

```
-/
def pureBuiltins : List String := ["tuple", "svec", "===", "typeof", "has_free_typevars", "nfields"]
def foldableBuiltins : List String :=
  pureBuiltins ++ ["isa", "ifelse", "<:", "typeassert", "throw", "apply_type"]

/-- The builtins of `Core` that have no `add_tfunc` entry (`find_tfunc(f) === nothing`) and are
not special-cased by `builtin_tfunction`, listed on the pinned Julia. None is foldable. -/
def noTfuncBuiltins : List String :=
  ["_abstracttype", "_apply_iterate", "_call_in_world", "_call_in_world_total", "_call_latest",
   "_compute_sparams", "_equiv_typedef", "_import", "_new_cancel_source", "_primitivetype",
   "_setsuper!", "_structtype", "_task", "_typebody!", "_using", "cancellation_point!",
   "declare_const", "declare_global", "define_method", "invoke", "invoke_in_world",
   "invokelatest", "isdefinedglobal"]

/-- The builtins whose `builtin_tfunction` dispatch is modelled but whose tfunc is not:
`current_scope` (its argument check is modelled), `apply_type`, and the builtins without a
tfunc (`Any`). -/
def dispatchOnlyBuiltins : List String := ["current_scope", "apply_type"] ++ noTfuncBuiltins

/-- The `add_tfunc` arity bounds `(minarg, maxarg)` of the modelled builtins (`none` is
`INT_INF`).

Julia source: Compiler/src/tfuncs.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(throw, 1, 1, @nospecs((𝕃::AbstractLattice, x)->Bottom), 0)
```
Julia source: Compiler/src/tfuncs.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(Core.ifelse, 3, 3, ifelse_tfunc, 1)
```
Julia source: Compiler/src/tfuncs.jl:401-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(===, 2, 2, egal_tfunc, 1)
```
Julia source: Compiler/src/tfuncs.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(isdefined, 2, 3, isdefined_tfunc, 1)
```
Julia source: Compiler/src/tfuncs.jl:646-648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(nfields, 1, 1, nfields_tfunc, 1)
add_tfunc(Core._expr, 1, INT_INF, @nospecs((𝕃::AbstractLattice, args...)->Expr), 100)
add_tfunc(svec, 0, INT_INF, @nospecs((𝕃::AbstractLattice, args...)->SimpleVector), 20)
```
Julia source: Compiler/src/tfuncs.jl:928-928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(typeof, 1, 1, typeof_tfunc, 1)
```
Julia source: Compiler/src/tfuncs.jl:945-945 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(has_free_typevars, 1, 1, has_free_typevars_tfunc, 1)
```
Julia source: Compiler/src/tfuncs.jl:952-952 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(typeassert, 2, 2, typeassert_tfunc, 4)
```
Julia source: Compiler/src/tfuncs.jl:998-998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(isa, 2, 2, isa_tfunc, 1)
```
Julia source: Compiler/src/tfuncs.jl:1021-1021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(<:, 2, 2, subtype_tfunc, 10)
```
Julia source: Compiler/src/tfuncs.jl:1597-1597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
add_tfunc(getfield, 2, 4, getfield_tfunc, 1)
```
-/
def tfuncArity : String → Option (Nat × Option Nat)
  | "throw" => some (1, some 1)
  | "ifelse" => some (3, some 3)
  | "===" => some (2, some 2)
  | "isdefined" => some (2, some 3)
  | "nfields" => some (1, some 1)
  | "svec" => some (0, none)
  | "typeof" => some (1, some 1)
  | "has_free_typevars" => some (1, some 1)
  | "typeassert" => some (2, some 2)
  | "isa" => some (2, some 2)
  | "<:" => some (2, some 2)
  | "getfield" => some (2, some 4)
  | _ => none

/-- The field access of `jl_f_getfield` (`src/builtins.c:1217-1233`) on a tuple value: an `Int`
index is bounds checked, a `Symbol` names no tuple field, anything else is a `TypeError`
(`get_checked_fieldindex`, `src/builtins.c:1173-1200`). Other objects are not modelled. -/
def getfieldTupleRT (x i : Val) : CM Val :=
  match x with
  | .imm ty fs =>
    if !ty.isTupleType then unmodelled "getfield on a struct value"
    else match i with
      | .long k => match fs[(k - 1).toNat]? with
        | some v => if k ≥ 1 then pure v else jlThrow "BoundsError"
        | none => jlThrow "BoundsError"
      | .symbol _ => jlThrow "FieldError"
      | _ => jlThrow "TypeError" "getfield"
  | _ => unmodelled "getfield on a non-tuple value"

/-- Calling a modelled builtin on values (`src/builtins.c`): `jl_f_is` (606-610), `jl_f_typeof`
(612-616), `jl_f_has_free_typevars` (618-622), `jl_f_issubtype` (694-701), `jl_f_isa`
(703-708), `jl_f_typeassert` (710-717), `jl_f_throw` (719-724), `jl_f_ifelse` (734-739),
`jl_f_tuple` (1125-1130), `jl_f_getfield` (1202-1234, tuple values only) and `jl_f_nfields`
(1457-1462). `JL_TYPECHK(f, type, x)` is `jl_is_type(x)`; a wrong argument count is an error.
`isdefined` with a valid argument count is not modelled. -/
def builtinRT (n : Nat) (E : CEnv) (f : String) (args : List Val) : CM Val := do
  match f, args with
  | "===", [a, b] => return boolVal (← egal n E a b)
  | "typeof", [a] => return typeOf a
  | "has_free_typevars", [a] => return boolVal (hasFreeTypevars a)
  | "nfields", [a] => return .long (← nfieldsRT E a)
  | "<:", [a, b] =>
    if !a.isType || !b.isType then jlThrow "TypeError" "<:"
    return boolVal (← issub n E a b)
  | "isa", [x, t] =>
    if !t.isType then jlThrow "TypeError" "isa"
    return boolVal (← isa n E x t)
  | "typeassert", [x, t] =>
    if !t.isType then jlThrow "TypeError" "typeassert"
    if !(← isa n E x t) then jlThrow "TypeError" "typeassert"
    return x
  | "throw", [_] => jlThrow "Exception" "throw"
  | "ifelse", [c, x, y] =>
    match asBool? c with
    | some true => return x
    | some false => return y
    | none => jlThrow "TypeError" "ifelse"
  | "tuple", xs => tupleRT n E xs
  | "getfield", x :: i :: rest =>
    if rest.length > 2 then jlThrow "ArgumentError" "getfield: wrong number of arguments"
    match rest with
    | [o, b] =>
      if !o.isSymbol then jlThrow "TypeError" "getfield"
      if (asBool? b).isNone then jlThrow "TypeError" "getfield"
      unmodelled "getfield with a memory order"
    | [b] =>
      if (asBool? b).isNone then
        if !b.isSymbol then jlThrow "TypeError" "getfield"
        unmodelled "getfield with a memory order"
    | _ => pure ()
    getfieldTupleRT x i
  | "svec", _ => unmodelled "Const(svec(...))"
  | "isdefined", [_, _] | "isdefined", [_, _, _] => unmodelled "isdefined on a value"
  | f, _ =>
    if modelledBuiltins.contains f then jlThrow "ArgumentError" s!"{f}: wrong number of arguments"
    unmodelled s!"builtin {f}"

/-- Call the tfunc of `f` with the argument count fixed by `builtin_tfunction`. -/
def callTfunc (n : Nat) (T : TEnv) (L : Lattice) (f : String) (args : List LElt) : CM LElt := do
  let E := T.E
  match f, args with
  | "throw", [_] => return .ty .bottom
  | "ifelse", [c, x, y] => ifelseTfunc n E L c x y
  | "===", [x, y] => egalTfunc n E L x y
  | "isdefined", [a, s] | "isdefined", [a, s, _] => isdefinedTfunc n T L a s
  | "nfields", [x] => nfieldsTfunc n T L x
  | "svec", _ => return .ty svecType
  | "typeof", [x] => typeofTfunc n E x
  | "has_free_typevars", [x] => hasFreeTypevarsTfunc n E x
  | "typeassert", [v, t] => typeassertTfunc n T L v t
  | "isa", [v, t] => isaTfunc n E L v t
  | "<:", [a, b] => subtypeTfunc n E a b
  | "getfield", args => getfieldTfunc n T L args
  | f, _ => jlThrow "MethodError" s!"{f} tfunc"

/-- Is `e` a Julia exception (rather than a model failure)? -/
def isJuliaError (e : String) : Bool := e.startsWith "julia:"

/-- The constant-folding prologue of `builtin_tfunction` (`Compiler/src/tfuncs.jl:3259-3277`):
`some r` when it folds the call, `none` when it falls through. -/
def builtinFold (n : Nat) (E : CEnv) (f : String) (argtypes : List LElt) : CM (Option LElt) := do
  if !foldableBuiltins.contains f then return none
  if !(← isAllConstArg n E argtypes) then return none
  let argvals ← collectConstArgs E argtypes
  tryCatch (do return some (.const (← builtinRT n E f argvals))) fun e =>
    if isJuliaError e then return some (.ty .bottom) else throw e

/-- The argument check and `Vararg` padding of `builtin_tfunction`
(`Compiler/src/tfuncs.jl:3306-3325`): the arguments the tfunc is called with, or `none` for a
wrong argument count (`Bottom`). `unconstrain_vararg_length(va)` is `Vararg{unwrapva(va)}`
(`base/essentials.jl:608-613`); the `T` of an existing `Vararg` was already checked and normalized
by `jl_wrap_vararg`, so wrapping it again changes nothing. -/
def builtinArgs (minarg : Nat) (maxarg : Option Nat) (argtypes : List LElt) :
    Option (List LElt) :=
  match argtypes.getLast? with
  | some (.ty (.vararg vaT _)) =>
    let k := argtypes.length - 1
    if (maxarg.map (fun m => decide (k > m))).getD false then none
    else if maxarg == some k then some argtypes.dropLast
    else
      let padded := argtypes.dropLast ++ List.replicate (minarg - k) (.ty (vaT.getD anyType))
      if (maxarg.map (fun m => decide (padded.length < m))).getD true then
        some (padded ++ [.ty (.vararg (some (vaT.getD anyType)) none)])
      else some padded
  | _ =>
    if minarg ≤ argtypes.length && (maxarg.map (fun m => decide (argtypes.length ≤ m))).getD true
    then some argtypes else none

/-- `builtin_tfunction(interp, f, argtypes, sv)` for the builtins (not intrinsics), with `𝕃ᵢ = L`.
The tfuncs of `current_scope` and `apply_type` are not modelled, nor are the tfuncs of builtins
outside `modelledBuiltins`.

Julia source: Compiler/src/tfuncs.jl:3255-3334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function builtin_tfunction(interp::AbstractInterpreter, @nospecialize(f), argtypes::Vector{Any},
                           sv::Union{AbsIntState, Nothing})
    𝕃ᵢ = typeinf_lattice(interp)
    # Early constant evaluation for foldable builtins with all const args
    if isa(f, IntrinsicFunction) ? is_pure_intrinsic_infer(f) : (contains_is(_PURE_BUILTINS, f) || (contains_is(_CONSISTENT_BUILTINS, f) && contains_is(_EFFECT_FREE_BUILTINS, f)))
        if is_all_const_arg(argtypes, 1)
            argvals = collect_const_args(argtypes, 1)
            try
                # unroll a few common cases for better codegen
                if length(argvals) == 1
                    return Const(f(argvals[1]))
                elseif length(argvals) == 2
                    return Const(f(argvals[1], argvals[2]))
                elseif length(argvals) == 3
                    return Const(f(argvals[1], argvals[2], argvals[3]))
                end
                return Const(f(argvals...))
            catch ex # expected ErrorException, TypeError, ConcurrencyViolationError, DivideError etc.
                ex isa InterruptException && rethrow()
                return Bottom
            end
        end
    end
    if isa(f, IntrinsicFunction)
        iidx = Int(reinterpret(Int32, f)) + 1
        if iidx < 0 || iidx > length(T_IFUNC)
            # unknown intrinsic
            return Any
        end
        tf = T_IFUNC[iidx]
    else
        if f === tuple
            return tuple_tfunc(𝕃ᵢ, argtypes)
        elseif f === Core.current_scope
            if length(argtypes) != 0
                if length(argtypes) != 1 || !isvarargtype(argtypes[1])
                    return Bottom
                end
            end
            return current_scope_tfunc(interp, sv)
        elseif f === Core.apply_type
            return apply_type_tfunc(𝕃ᵢ, argtypes; max_union_splitting=InferenceParams(interp).max_union_splitting)
        end
        fidx = find_tfunc(f)
        if fidx === nothing
            # unknown/unhandled builtin function
            return Any
        end
        tf = T_FFUNC_VAL[fidx]
    end

    if hasvarargtype(argtypes)
        if length(argtypes) - 1 > tf[2]
            # definitely too many arguments
            return Bottom
        end
        if length(argtypes) - 1 == tf[2]
            argtypes = argtypes[1:end-1]
        else
            vatype = argtypes[end]::TypeofVararg
            argtypes = argtypes[1:end-1]
            while length(argtypes) < tf[1]
                push!(argtypes, unwrapva(vatype))
            end
            if length(argtypes) < tf[2]
                push!(argtypes, unconstrain_vararg_length(vatype))
            end
        end
    elseif !(tf[1] <= length(argtypes) <= tf[2])
        # wrong # of args
        return Bottom
    end
    tfunc = tf[3]
    na = length(argtypes)
    na == 1 && return tfunc(𝕃ᵢ, argtypes[1])
    na == 2 && return tfunc(𝕃ᵢ, argtypes[1], argtypes[2])
    na == 3 && return tfunc(𝕃ᵢ, argtypes[1], argtypes[2], argtypes[3])
    na == 4 && return tfunc(𝕃ᵢ, argtypes[1], argtypes[2], argtypes[3], argtypes[4])
    return tfunc(𝕃ᵢ, argtypes...)
end
```
-/
def builtinTfunction (n : Nat) (T : TEnv) (L : Lattice) (f : String) (argtypes : List LElt) :
    CM LElt := do
  let E := T.E
  if !(modelledBuiltins.contains f || dispatchOnlyBuiltins.contains f) then
    unmodelled s!"builtin_tfunction of {f}"
  if let some r ← builtinFold n E f argtypes then return r
  if f == "tuple" then
    return ← tupleTfunc n E L argtypes
  else if f == "current_scope" then
    if argtypes.length != 0 then
      if argtypes.length != 1 || !argtypes[0]!.isVarargElt then return .ty .bottom
    unmodelled "current_scope_tfunc"
  else if f == "apply_type" then
    unmodelled "apply_type_tfunc"
  -- `find_tfunc(f) === nothing`: an unknown or unhandled builtin
  let some (minarg, maxarg) := tfuncArity f | return .ty anyType
  match builtinArgs minarg maxarg argtypes with
  | none => return .ty .bottom
  | some args => callTfunc n T L f args

/-- `builtin_nothrow(𝕃, f, argtypes, rt)` and `_builtin_nothrow` for the modelled builtins.

Julia source: Compiler/src/tfuncs.jl:3236-3253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasvarargtype(argtypes::Vector{Any}) = !isempty(argtypes) && isvarargtype(argtypes[end])

"""
    builtin_nothrow(𝕃::AbstractLattice, f::Builtin, argtypes::Vector{Any}, rt)::Bool

Compute throw-ness of a builtin function call. `argtypes` should not include `f` itself.
"""
function builtin_nothrow(𝕃::AbstractLattice, @nospecialize(f), argtypes::Vector{Any}, @nospecialize(rt))
    rt === Bottom && return false
    if f === tuple || f === svec
        return true
    elseif hasvarargtype(argtypes)
        return false
    elseif contains_is(_PURE_BUILTINS, f)
        return true
    end
    return _builtin_nothrow(𝕃, f, argtypes, rt)
end
```
Julia source: Compiler/src/tfuncs.jl:2626-2711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _builtin_nothrow(𝕃::AbstractLattice, @nospecialize(f::Builtin), argtypes::Vector{Any},
                          @nospecialize(rt))
    ⊑ = partialorder(𝕃)
    na = length(argtypes)
    if f === Core.memorynew
        return memorynew_nothrow(argtypes)
    elseif f === memoryrefnew
        return memoryref_builtin_common_nothrow(argtypes)
    elseif f === memoryrefoffset
        length(argtypes) == 1 || return false
        memtype = widenconst(argtypes[1])
        return memtype ⊑ GenericMemoryRef
    elseif f === memoryrefset!
        return memoryrefop_builtin_common_nothrow(𝕃, argtypes, f)
    elseif f === memoryrefunset!
        return memoryrefop_builtin_common_nothrow(𝕃, argtypes, f)
    elseif f === memoryrefget || f === const_memoryrefget
        return memoryrefop_builtin_common_nothrow(𝕃, argtypes, f)
    elseif f === memoryref_isassigned
        return memoryrefop_builtin_common_nothrow(𝕃, argtypes, f)
    elseif f === Core._expr
        length(argtypes) >= 1 || return false
        return argtypes[1] ⊑ Symbol
    elseif f === Core._typevar
        na == 3 || return false
        return typevar_nothrow(𝕃, argtypes[1], argtypes[2], argtypes[3])
    elseif f === invoke
        return false
    elseif f === getfield
        return getfield_nothrow(𝕃, argtypes)
    elseif f === setfield!
        if na == 3
            return setfield!_nothrow(𝕃, argtypes[1], argtypes[2], argtypes[3])
        elseif na == 4
            return setfield!_nothrow(𝕃, argtypes[1], argtypes[2], argtypes[3], argtypes[4])
        end
        return false
    elseif f === fieldtype
        na == 2 || return false
        return fieldtype_nothrow(𝕃, argtypes[1], argtypes[2])
    elseif f === apply_type
        return apply_type_nothrow(𝕃, argtypes, rt)
    elseif f === isa
        na == 2 || return false
        return isa_nothrow(𝕃, nothing, argtypes[2])
    elseif f === (<:)
        na == 2 || return false
        return subtype_nothrow(𝕃, argtypes[1], argtypes[2])
    elseif f === isdefined
        return isdefined_nothrow(𝕃, argtypes)
    elseif f === Core.sizeof
        na == 1 || return false
        return sizeof_nothrow(argtypes[1])
    elseif f === Core.bitsizeof
        na == 1 || return false
        return bitsizeof_nothrow(argtypes[1])
    elseif f === Core.ifelse
        na == 3 || return false
        return ifelse_nothrow(𝕃, argtypes[1], nothing, nothing)
    elseif f === typeassert
        na == 2 || return false
        return typeassert_nothrow(𝕃, argtypes[1], argtypes[2])
    elseif f === Core.get_binding_type
        na == 2 || return false
        return get_binding_type_nothrow(𝕃, argtypes[1], argtypes[2])
    elseif f === donotdelete
        return true
    elseif f === Core.finalizer
        2 <= na <= 4 || return false
        # Core.finalizer does no error checking - that's done in Base.finalizer
        return true
    elseif f === Core.compilerbarrier
        na == 2 || return false
        return compilerbarrier_nothrow(argtypes[1], nothing)
    elseif f === Core._svec_len
        na == 1 || return false
        return _svec_len_nothrow(𝕃, argtypes[1])
    elseif f === Core._svec_ref
        na == 2 || return false
        return _svec_ref_tfunc(𝕃, argtypes[1], argtypes[2]) isa Const
    elseif f === Core.task_result_type
        na == 1 || return false
        return argtypes[1] ⊑ Task
    end
    return false
end
```
-/
def builtinNothrow (n : Nat) (T : TEnv) (L : Lattice) (f : String) (argtypes : List LElt)
    (rt : LElt) : CM Bool := do
  let E := T.E
  if !modelledBuiltins.contains f then unmodelled s!"builtin_nothrow of {f}"
  if rt.isBottom then return false
  if f == "tuple" || f == "svec" then return true
  if (argtypes.getLast?.map LElt.isVarargElt).getD false then return false
  if pureBuiltins.contains f then return true
  let na := argtypes.length
  match f with
  | "getfield" => getfieldNothrow n T L argtypes
  | "isa" => if na != 2 then return false else isaNothrow n E L argtypes[1]!
  | "<:" => if na != 2 then return false else subtypeNothrow n E L argtypes[0]! argtypes[1]!
  | "isdefined" => isdefinedNothrow n E L argtypes
  | "ifelse" => if na != 3 then return false else ifelseNothrow n E L argtypes[0]!
  | "typeassert" => if na != 2 then return false else typeassertNothrow n E L argtypes[0]! argtypes[1]!
  | _ => return false

end JuliaLean.Compiler
