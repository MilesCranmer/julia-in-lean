import JuliaLean.Compiler.Prelude
import JuliaLean.Compiler.src.typeutils
import JuliaLean.Compiler.src.abstractlattice

/-!
`Compiler/src/typelattice.jl`: lattice element constructors, the slot wrappers, and each layer's
`⊑`, `is_lattice_equal`, `tmeet` and `widenconst`.

Every function takes an explicit fuel `n` (Julia has none: running out is a model failure, not a
Julia outcome). Recursion through the layers keeps the layer explicit, as Julia's dispatch on the
lattice argument does.

Extension points for code outside this file:
* `TmeetOps` carries `getfield_tfunc` and `tuple_tfunc` (`Compiler/src/tfuncs.jl`), which the
  `Tuple` branch of `tmeet(::PartialsLattice, ...)` calls. `tmeetOpsUnmodelled` makes that branch
  report `unmodelled`.
* `smerge` and `stupdate!` take `tmerge` (`Compiler/src/typelimits.jl`) as an argument.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-! ## Constructors and `LimitedAccuracy` -/

/-- `LimitedAccuracy(typ, causes)`

Julia source: Compiler/src/typelattice.jl:195-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function LimitedAccuracy(@nospecialize(typ), causes::IdSet{InferenceState})
        @assert !isa(typ, LimitedAccuracy) "found nested LimitedAccuracy"
        return new(typ, causes)
    end
end
LimitedAccuracy(@nospecialize(T), ::Nothing) = T
```
`causes = none` is the `::Nothing` method. -/
def mkLimitedAccuracy (typ : LElt) (causes : Option (List ObjId × ObjId)) : CM LElt :=
  match causes with
  | none => pure typ
  | some (cs, cid) => do
    if typ.isLimited then jlThrow "AssertionError" "found nested LimitedAccuracy"
    return .limitedAccuracy typ cs cid

/-- `copy(s::IdSet)`: a new set object with the same elements. -/
def copyIdSet (cs : List ObjId) : CM (List ObjId × ObjId) := do
  return (cs, ← freshId)

/-- `union!(s, t)` on `IdSet`s: the elements of `t` not in `s` are appended. -/
def idsetUnion (s t : List ObjId) : List ObjId :=
  t.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) s

/-- `narrow_limited_typ(x, y)`

Julia source: Compiler/src/typelattice.jl:12-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Narrow `x` by the `LimitedAccuracy` of `y`. If `y` is limited, return `x` limited by the
# causes of `y` (and of `x`, if any). Otherwise return `x` unchanged.
@nospecializeinfer function narrow_limited_typ(@nospecialize(x), @nospecialize(y))
    y isa LimitedAccuracy || return x
    x isa LimitedAccuracy && return LimitedAccuracy(x.typ, union!(copy(x.causes), y.causes))
    return LimitedAccuracy(x, copy(y.causes))
end
```
-/
def narrowLimitedTyp (x y : LElt) : CM LElt := do
  let .limitedAccuracy _ ycauses _ := y | return x
  if let .limitedAccuracy xtyp xcauses _ := x then
    let (c, cid) ← copyIdSet xcauses
    return ← mkLimitedAccuracy xtyp (some (idsetUnion c ycauses, cid))
  mkLimitedAccuracy x (some (← copyIdSet ycauses))

/-- `assert_nested_slotwrapper(t)`

Julia source: Compiler/src/typelattice.jl:222-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function assert_nested_slotwrapper(@nospecialize t)
    @assert !(t isa Conditional)      "found nested Conditional"
    @assert !(t isa InterConditional) "found nested InterConditional"
    @assert !(t isa MustAlias)        "found nested MustAlias"
    @assert !(t isa InterMustAlias)   "found nested InterMustAlias"
    return t
end
```
-/
def assertNestedSlotwrapper (t : LElt) : CM LElt := do
  if t.isConditional then jlThrow "AssertionError" "found nested Conditional"
  if t.isInterConditional then jlThrow "AssertionError" "found nested InterConditional"
  if t.isMustAlias then jlThrow "AssertionError" "found nested MustAlias"
  if t.isInterMustAlias then jlThrow "AssertionError" "found nested InterMustAlias"
  return t

/-- `Conditional(slot, ssadef, thentype, elsetype; isdefined)`

Julia source: Compiler/src/typelattice.jl:49-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Conditional(slot::Int, ssadef::Int, @nospecialize(thentype), @nospecialize(elsetype);
                         isdefined::Bool=false)
        assert_nested_slotwrapper(thentype)
        assert_nested_slotwrapper(elsetype)
        limited = narrow_limited_typ(narrow_limited_typ(Bool, elsetype), thentype)
        limited isa LimitedAccuracy && return limited
        return new(slot, ssadef, thentype, elsetype, isdefined)
    end
```
-/
def mkConditional (slot ssadef : Int) (thentype elsetype : LElt) (isdefined : Bool := false) :
    CM LElt := do
  let _ ← assertNestedSlotwrapper thentype
  let _ ← assertNestedSlotwrapper elsetype
  let limited ← narrowLimitedTyp (← narrowLimitedTyp (.ty boolTy) elsetype) thentype
  if limited.isLimited then return limited
  return .conditional slot ssadef thentype elsetype isdefined

/-- `InterConditional(cnd::Conditional)`

Julia source: Compiler/src/typelattice.jl:62-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function InterConditional(cnd::Conditional)
    @assert cnd.ssadef == 0
    InterConditional(cnd.slot, cnd.thentype, cnd.elsetype)
end
```
-/
def interConditionalOf (cnd : LElt) : CM LElt := do
  let .conditional slot ssadef thentype elsetype _ := cnd
    | jlThrow "MethodError" "InterConditional"
  if ssadef != 0 then jlThrow "AssertionError" "cnd.ssadef == 0"
  return .interConditional slot thentype elsetype

/-- `MustAlias(slot, ssadef, vartyp, fldidx, fldtyp)`

Julia source: Compiler/src/typelattice.jl:96-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function MustAlias(slot::Int, ssadef::Int, @nospecialize(vartyp), fldidx::Int, @nospecialize(fldtyp))
        assert_nested_slotwrapper(vartyp)
        assert_nested_slotwrapper(fldtyp)
        # @assert !isalreadyconst(vartyp) "vartyp is already const"
        # @assert !isalreadyconst(fldtyp) "fldtyp is already const"
        limited = narrow_limited_typ(fldtyp, vartyp)
        limited isa LimitedAccuracy && return limited
        return new(slot, ssadef, vartyp, fldidx, fldtyp)
    end
```
-/
def mkMustAlias (slot ssadef : Int) (vartyp : LElt) (fldidx : Int) (fldtyp : LElt) : CM LElt := do
  let _ ← assertNestedSlotwrapper vartyp
  let _ ← assertNestedSlotwrapper fldtyp
  let limited ← narrowLimitedTyp fldtyp vartyp
  if limited.isLimited then return limited
  return .mustAlias slot ssadef vartyp fldidx fldtyp

/-- `InterMustAlias(alias::MustAlias)`

Julia source: Compiler/src/typelattice.jl:110-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function InterMustAlias(alias::MustAlias)
    @assert alias.ssadef == 0
    limited = narrow_limited_typ(alias.fldtyp, alias.vartyp)
    limited isa LimitedAccuracy && return limited
    InterMustAlias(alias.slot, alias.vartyp, alias.fldidx, alias.fldtyp)
end
```
-/
def interMustAliasOf (alias : LElt) : CM LElt := do
  let .mustAlias slot ssadef vartyp fldidx fldtyp := alias
    | jlThrow "MethodError" "InterMustAlias"
  if ssadef != 0 then jlThrow "AssertionError" "alias.ssadef == 0"
  let limited ← narrowLimitedTyp fldtyp vartyp
  if limited.isLimited then return limited
  return .interMustAlias slot vartyp fldidx fldtyp

/-- `update_mustalias(alias; vartyp, fldtyp)`

Julia source: Compiler/src/typelattice.jl:117-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return an alias of the same field as `alias`, with `vartyp` and `fldtyp` replaced.
# Not a constructor method: `InterMustAlias` is a `Core` type shared by all `Compiler`s.
update_mustalias(alias::MustAlias;
    @nospecialize(vartyp = alias.vartyp), @nospecialize(fldtyp = alias.fldtyp)) =
    MustAlias(alias.slot, alias.ssadef, vartyp, alias.fldidx, fldtyp)
update_mustalias(alias::InterMustAlias;
    @nospecialize(vartyp = alias.vartyp), @nospecialize(fldtyp = alias.fldtyp)) =
    InterMustAlias(alias.slot, vartyp, alias.fldidx, fldtyp)
```
The `InterMustAlias` method calls the raw `Core` constructor, with no validation. -/
def updateMustalias (alias : LElt) (vartyp fldtyp : Option LElt := none) : CM LElt :=
  match alias with
  | .mustAlias slot ssadef v i f => mkMustAlias slot ssadef (vartyp.getD v) i (fldtyp.getD f)
  | .interMustAlias slot v i f => pure (.interMustAlias slot (vartyp.getD v) i (fldtyp.getD f))
  | _ => jlThrow "MethodError" "update_mustalias"

/-! ## Slot wrappers -/

/-- `widenconditional(typ)`

Julia source: Compiler/src/typelattice.jl:242-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function widenconditional(@nospecialize typ)
    if isa(typ, AnyConditional)
        if typ.thentype === Union{}
            return Const(false)
        elseif typ.elsetype === Union{}
            return Const(true)
        else
            return Bool
        end
    elseif isa(typ, LimitedAccuracy)
        error("unhandled LimitedAccuracy")
    end
    return typ
end
```
-/
def widenconditional (typ : LElt) : CM LElt :=
  match typ with
  | .conditional _ _ thentype elsetype _ | .interConditional _ thentype elsetype =>
    match thentype, elsetype with
    | .ty .bottom, _ => pure (.const (boolVal false))
    | _, .ty .bottom => pure (.const (boolVal true))
    | _, _ => pure (.ty boolTy)
  | .limitedAccuracy .. => jlThrow "ErrorException" "unhandled LimitedAccuracy"
  | _ => pure typ

/-- `widenwrappedconditional(typ)`

Julia source: Compiler/src/typelattice.jl:256-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function widenwrappedconditional(@nospecialize typ)
    if isa(typ, LimitedAccuracy)
        return LimitedAccuracy(widenconditional(typ.typ), typ.causes)
    end
    return widenconditional(typ)
end
```
-/
def widenwrappedconditional (typ : LElt) : CM LElt := do
  if let .limitedAccuracy t cs cid := typ then
    return ← mkLimitedAccuracy (← widenconditional t) (some (cs, cid))
  widenconditional typ

/-- `widenmustalias(typ)`

Julia source: Compiler/src/typelattice.jl:298-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function widenmustalias(@nospecialize typ)
    if isa(typ, AnyMustAlias)
        return typ.fldtyp
    elseif isa(typ, LimitedAccuracy)
        error("unhandled LimitedAccuracy")
    end
    return typ
end
```
-/
def widenmustalias (typ : LElt) : CM LElt :=
  match typ with
  | .mustAlias _ _ _ _ f | .interMustAlias _ _ _ f => pure f
  | .limitedAccuracy .. => jlThrow "ErrorException" "unhandled LimitedAccuracy"
  | _ => pure typ

/-- `widenwrappedmustalias(typ)`

Julia source: Compiler/src/typelattice.jl:306-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function widenwrappedmustalias(@nospecialize typ)
    if isa(typ, LimitedAccuracy)
        return LimitedAccuracy(widenmustalias(typ.typ), typ.causes)
    end
    return widenmustalias(typ)
end
```
-/
def widenwrappedmustalias (typ : LElt) : CM LElt := do
  if let .limitedAccuracy t cs cid := typ then
    return ← mkLimitedAccuracy (← widenmustalias t) (some (cs, cid))
  widenmustalias typ

/-- `widenslotwrapper(typ)`

Julia source: Compiler/src/typelattice.jl:230-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function widenslotwrapper(@nospecialize typ)
    if isa(typ, AnyConditional)
        return widenconditional(typ)
    elseif isa(typ, AnyMustAlias)
        return widenmustalias(typ)
    end
    return typ
end
```
-/
def widenslotwrapper (typ : LElt) : CM LElt := do
  if typ.isAnyConditional then return ← widenconditional typ
  if typ.isAnyMustAlias then return ← widenmustalias typ
  return typ

/-- `is_same_conditionals(a, b)`

Julia source: Compiler/src/typelattice.jl:282-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_same_conditionals(a::Conditional, b::Conditional) = a.slot == b.slot && a.ssadef == b.ssadef
is_same_conditionals(a::C, b::C) where C<:AnyConditional = a.slot == b.slot
```
-/
def isSameConditionals (a b : LElt) : CM Bool :=
  match a, b with
  | .conditional s1 d1 .., .conditional s2 d2 .. => pure (s1 == s2 && d1 == d2)
  | .interConditional s1 .., .interConditional s2 .. => pure (s1 == s2)
  | _, _ => jlThrow "MethodError" "is_same_conditionals"

/-- `maybe_extract_const_bool(c)`: `none` is `nothing`.

Julia source: Compiler/src/typelattice.jl:287-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_extract_const_bool(c::Const) = (val = c.val; isa(val, Bool)) ? val : nothing
function maybe_extract_const_bool(c::AnyConditional)
    (c.thentype === Bottom && !(c.elsetype === Bottom)) && return false
    (c.elsetype === Bottom && !(c.thentype === Bottom)) && return true
    nothing
end
@nospecializeinfer maybe_extract_const_bool(@nospecialize c) = nothing
```
-/
def maybeExtractConstBool (c : LElt) : Option Bool :=
  let isBot : LElt → Bool := fun | .ty .bottom => true | _ => false
  match c with
  | .const val => asBool? val
  | .conditional _ _ t e _ | .interConditional _ t e =>
    if isBot t && !isBot e then some false
    else if isBot e && !isBot t then some true
    else none
  | _ => none

/-- `is_same_alias(a, b)`

Julia source: Compiler/src/typelattice.jl:372-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_same_alias(a::MustAlias, b::MustAlias) =
    a.slot == b.slot && a.ssadef == b.ssadef && a.fldidx == b.fldidx
is_same_alias(a::InterMustAlias, b::InterMustAlias) = a.slot == b.slot && a.fldidx == b.fldidx
is_same_alias(@nospecialize(a), @nospecialize(b)) = false
```
-/
def isSameAlias (a b : LElt) : Bool :=
  match a, b with
  | .mustAlias s1 d1 _ i1 _, .mustAlias s2 d2 _ i2 _ => s1 == s2 && d1 == d2 && i1 == i2
  | .interMustAlias s1 _ i1 _, .interMustAlias s2 _ i2 _ => s1 == s2 && i1 == i2
  | _, _ => false

/-- `ignorelimited(typ)`

Julia source: Compiler/src/typelattice.jl:395-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ignorelimited(@nospecialize typ) = typ
ignorelimited(typ::LimitedAccuracy) = typ.typ
```
-/
def ignorelimited : LElt → LElt
  | .limitedAccuracy t _ _ => t
  | t => t

/-! ## `widenconst` -/

/-- `widenconst(x)`

Julia source: Compiler/src/typelattice.jl:730-749 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    widenconst(x) -> t::Type

Widens extended lattice element `x` to native `Type` representation.
"""
widenconst(::AnyConditional) = Bool
widenconst(a::AnyMustAlias) = widenconst(widenmustalias(a))
# a closed type value widens to the egality kind, mirroring how `jl_inst_arg_tuple_type`
# keys runtime dispatch (`Const(v) ⊑ TypeEgal{v} ⊑ Type{v}`); an open one only to its
# `==`-class `Type{v}`
widenconst(c::Const) = (v = c.val; isa(v, Type) ?
    (has_free_typevars(v) ? Type{v} : Core.TypeEgal{v}) : typeof(v))
widenconst(::PartialTypeVar) = TypeVar
widenconst(t::Core.PartialStruct) = t.typ
widenconst(t::PartialOpaque) = t.typ
widenconst(t::PartialTask) = Task
@nospecializeinfer widenconst(@nospecialize t::AnyType) = t
widenconst(::TypeVar) = error("unhandled TypeVar")
widenconst(::TypeofVararg) = error("unhandled Vararg")
widenconst(::LimitedAccuracy) = error("unhandled LimitedAccuracy")
```
-/
def widenconst (n : Nat) (E : CEnv) (x : LElt) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
  match x with
  | .conditional .. | .interConditional .. => pure boolTy
  | .mustAlias _ _ _ _ f | .interMustAlias _ _ _ f => widenconst n E f
  | .const v =>
    if v.isType then
      if hasFreeTypevars v then mkTypeEq n E v else mkTypeEgal v
    else pure (typeOf v)
  | .partialTypeVar .. => pure tvarType
  | .partialStruct typ .. => pure typ
  | .partialOpaque typ .. => pure typ
  | .partialTask _ => pure taskType
  | .ty t =>
    if t.isType then pure t
    else if t.isTypevar then jlThrow "ErrorException" "unhandled TypeVar"
    else if t.isVararg then jlThrow "ErrorException" "unhandled Vararg"
    else jlThrow "MethodError" "widenconst"
  | .limitedAccuracy .. => jlThrow "ErrorException" "unhandled LimitedAccuracy"

/-- `widenconst_split(x)`

Julia source: Compiler/src/typelattice.jl:758-764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function widenconst_split(@nospecialize x)
    isa(x, AnyType) && return x
    isa(x, Const) && return widenconst(x)
    isa(x, PartialStruct) && return widenconst(x)
    isa(x, AnyConditional) && return Bool
    return widenconst(x)
end
```
-/
def widenconstSplit (n : Nat) (E : CEnv) (x : LElt) : CM Val := do
  if let .ty t := x then if t.isType then return t
  if x.isConst then return ← widenconst n E x
  if x.isPartialStruct then return ← widenconst n E x
  if x.isAnyConditional then return boolTy
  widenconst n E x

/-- `isalreadyconst(t)`

Julia source: Compiler/src/typelattice.jl:313-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function isalreadyconst(@nospecialize t)
    isa(t, Const) && return true
    issingletontype(t) && return true
    return isconstType(t)
end
```
-/
def isalreadyconst (n : Nat) (E : CEnv) (t : LElt) : CM Bool := do
  if t.isConst then return true
  let .ty t := t | return false
  if ← issingletontype n E t then return true
  return isconstType t

/-- `n_initialized(t::Const)` and `n_initialized(pstruct::PartialStruct)`, which the `⊑` of
`PartialsLattice` calls.

Julia source: Compiler/src/typelimits.jl:330-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function n_initialized(t::Const)
    nf = nfields(t.val)
    return something(findfirst(i::Int->!isdefined(t.val,i), 1:nf), nf+1)-1
end
function n_initialized(pstruct::PartialStruct)
    undefs = _getundefs(pstruct)
    nf = length(undefs)
    return something(findfirst(i::Int->undefs[i]!==false, 1:nf), nf+1)-1
end
```
-/
def nInitializedConst (E : CEnv) (val : Val) : CM Nat := do
  let nf ← nfieldsOf E val
  let first := (List.range nf).find? (fun i => !isdefinedField val (i + 1))
  return (first.map (· + 1)).getD (nf + 1) - 1

def nInitializedPartialStruct (undefs : List (Option Bool)) : Nat :=
  let nf := undefs.length
  let first := (List.range nf).find? (fun i => undefs[i]! != some false)
  (first.map (· + 1)).getD (nf + 1) - 1

/-- `v[i]` (1-based) with Julia's `BoundsError`. -/
def jlIndex {α : Type} [Inhabited α] (v : List α) (i : Nat) : CM α :=
  match v[i - 1]? with
  | some x => if i ≥ 1 then pure x else jlThrow "BoundsError"
  | none => jlThrow "BoundsError"

/-! ## Lattice order -/

/-- `issubconditional(𝕃, a, b)` and `_issubconditional`; `le` is `⊑` one fuel step down.

Julia source: Compiler/src/typelattice.jl:263-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `Conditional` and `InterConditional` are valid in opposite contexts
# (i.e. local inference and inter-procedural call), as such they will never be compared
@nospecializeinfer issubconditional(𝕃::AbstractLattice, a::Conditional, b::Conditional) =
    _issubconditional(𝕃, a, b, #=check_isdefined=#true)
@nospecializeinfer issubconditional(𝕃::AbstractLattice, a::InterConditional, b::InterConditional) =
    _issubconditional(𝕃, a, b, #=check_isdefined=#false)
@nospecializeinfer function _issubconditional(𝕃::AbstractLattice, a::C, b::C, check_isdefined::Bool) where C<:AnyConditional
    if is_same_conditionals(a, b)
        if ⊑(𝕃, a.thentype, b.thentype)
            if ⊑(𝕃, a.elsetype, b.elsetype)
                if !check_isdefined || a.isdefined ≥ b.isdefined
                    return true
                end
            end
        end
    end
    return false
end
```
-/
def issubconditional (le : Lattice → LElt → LElt → CM Bool) (L : Lattice) (a b : LElt) :
    CM Bool := do
  let (aT, aE, bT, bE, checkIsdefined, aDef, bDef) ← match a, b with
    | .conditional _ _ aT aE ad, .conditional _ _ bT bE bd => pure (aT, aE, bT, bE, true, ad, bd)
    | .interConditional _ aT aE, .interConditional _ bT bE => pure (aT, aE, bT, bE, false, false, false)
    | _, _ => jlThrow "MethodError" "issubconditional"
  if ← isSameConditionals a b then
    if ← le L aT bT then
      if ← le L aE bE then
        -- `a.isdefined ≥ b.isdefined` on `Bool`
        if !checkIsdefined || (aDef || !bDef) then
          return true
  return false

/-- `issubalias(a, b)`; `le` is `⊑` one fuel step down. The comparison uses the global `⊑`,
whose lattice is `fallback_lattice`, whatever the layer of the caller.

Julia source: Compiler/src/typelattice.jl:367-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issubalias(a::AnyMustAlias, b::AnyMustAlias)
    return is_same_alias(a, b) &&
        a.vartyp ⊑ b.vartyp && a.fldtyp ⊑ b.fldtyp
end
```
-/
def issubalias (le : Lattice → LElt → LElt → CM Bool) (a b : LElt) : CM Bool := do
  let (av, af, bv, bf) ← match a, b with
    | .mustAlias _ _ av _ af, .mustAlias _ _ bv _ bf
    | .mustAlias _ _ av _ af, .interMustAlias _ bv _ bf
    | .interMustAlias _ av _ af, .mustAlias _ _ bv _ bf
    | .interMustAlias _ av _ af, .interMustAlias _ bv _ bf => pure (av, af, bv, bf)
    | _, _ => jlThrow "MethodError" "issubalias"
  if !isSameAlias a b then return false
  if !(← le fallbackLattice av bv) then return false
  le fallbackLattice af bf

/-- `isa(x, ConditionalT)` for `ConditionalT = isa(lattice, ConditionalsLattice) ? Conditional :
InterConditional`. -/
def isConditionalT (inter : Bool) (x : LElt) : Bool :=
  if inter then x.isInterConditional else x.isConditional

/-- `isa(x, MustAliasT)` for `MustAliasT = isa(𝕃, MustAliasesLattice) ? MustAlias :
InterMustAlias`. -/
def isMustAliasT (inter : Bool) (x : LElt) : Bool :=
  if inter then x.isInterMustAlias else x.isMustAlias

def LElt.isBottom : LElt → Bool | .ty .bottom => true | _ => false
def LElt.isAny : LElt → Bool | .ty t => t == anyType | _ => false

/-- `⊑(𝕃, a, b)` for every layer.

Julia source: Compiler/src/typelattice.jl:401-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function ⊑(lattice::InferenceLattice, @nospecialize(a), @nospecialize(b))
    ⊑(widenlattice(lattice), ignorelimited(a), ignorelimited(b)) || return false

    isa(b, LimitedAccuracy) || return true

    # We've found that ignorelimited(a) ⊑ ignorelimited(b).
    # Now perform the reverse query to check for equality.
    ab_eq = ⊑(widenlattice(lattice), b.typ, ignorelimited(a))

    if !ab_eq
        # a's unlimited type is strictly smaller than b's
        return true
    end

    # a and b's unlimited types are equal.
    isa(a, LimitedAccuracy) || return false # b is limited, so ε smaller
    return b.causes ⊆ a.causes
end
```

Julia source: Compiler/src/typelattice.jl:420-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function ⊑(lattice::AnyConditionalsLattice, @nospecialize(a), @nospecialize(b))
    # Fast paths for common cases
    b === Any && return true
    a === Any && return false
    a === Union{} && return true
    b === Union{} && return false
    ConditionalT = isa(lattice, ConditionalsLattice) ? Conditional : InterConditional
    if isa(a, ConditionalT)
        if isa(b, ConditionalT)
            return issubconditional(lattice, a, b)
        elseif isa(b, Const) && isa(b.val, Bool)
            return maybe_extract_const_bool(a) === b.val
        end
        a = Bool
    elseif isa(b, ConditionalT)
        if isa(a, Const) && isa(a.val, Bool)
           if (a.val === true && b.thentype === Any && b.elsetype === Bottom) ||
              (a.val === false && b.elsetype === Any && b.thentype === Bottom)
               # this Conditional contains distinctly no lattice information, and is simply an alternative representation of the Const Bool used for internal tracking purposes
               return true
           end
        end
        return false
    end
    return ⊑(widenlattice(lattice), a, b)
end
```

Julia source: Compiler/src/typelattice.jl:447-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function ⊑(𝕃::AnyMustAliasesLattice, @nospecialize(a), @nospecialize(b))
    MustAliasT = isa(𝕃, MustAliasesLattice) ? MustAlias : InterMustAlias
    if isa(a, MustAliasT)
        if isa(b, MustAliasT)
            return issubalias(a, b)
        end
        a = widenmustalias(a)
    elseif isa(b, MustAliasT)
        return a === Union{}
    end
    return ⊑(widenlattice(𝕃), a, b)
end
```

Julia source: Compiler/src/typelattice.jl:460-545 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function ⊑(lattice::PartialsLattice, @nospecialize(a), @nospecialize(b))
    if isa(a, PartialStruct)
        if isa(b, PartialStruct)
            a.typ <: b.typ || return false
            nflds = length(a.fields)
            nflds == length(b.fields) || return false
            for i in 1:nflds
                if !(_getundefs(b)[i] === nothing || _getundefs(a)[i] === _getundefs(b)[i])
                    return false
                end
                af = a.fields[i]
                bf = b.fields[i]
                if i == nflds
                    if isvarargtype(af)
                        # If `af` is vararg, so must bf by the <: above
                        @assert isvarargtype(bf)
                        continue
                    elseif isvarargtype(bf)
                        # If `bf` is vararg, it must match the information
                        # in the type, so there's nothing to check here.
                        continue
                    end
                end
                ⊑(lattice, af, bf) || return false
            end
            return true
        end
        return isa(b, Type) && a.typ <: b
    elseif isa(b, PartialStruct)
        if isa(a, Const)
            widea = widenconst(a)
            isa(widea, DataType) || return false
            wideb = widenconst(b)
            wideb′ = unwrap_unionall(wideb)::DataType
            widea.name === wideb′.name || return false
            if wideb′.name === Tuple.name
                # We can skip the subtype check if b is a Tuple, since in that
                # case, the ⊑ of the elements is sufficient.
                # But for tuple comparisons, we need their lengths to be the same for now.
                # TODO improve accuracy for cases when `b` contains vararg element
                nfields(a.val) == length(b.fields) || return false
            else
                widea <: wideb || return false
                # for structs we need to check that `a` does not have less information than `b` that may be partially initialized
                n_initialized(a) ≥ n_initialized(b) || return false
            end
            nf = nfields(a.val)
            for i in 1:nf
                if !isdefined(a.val, i)
                    _getundefs(b)[i] === false && return false # conflicting defined-ness information
                    continue # since ∀ T Union{} ⊑ T
                end
                i > length(b.fields) && break # `a` has more information than `b` that is partially initialized struct
                if _getundefs(b)[i] === true
                    return false # conflicting defined-ness information
                end
                bfᵢ = b.fields[i]
                if i == nf
                    bfᵢ = unwrapva(bfᵢ)
                end
                ⊑(lattice, Const(getfield(a.val, i)), bfᵢ) || return false
            end
            return true
        end
        return false
    end
    if isa(a, PartialOpaque)
        if isa(b, PartialOpaque)
            (a.parent === b.parent && a.source === b.source) || return false
            return (widenconst(a) <: widenconst(b)) &&
                ⊑(lattice, a.env, b.env)
        end
        return ⊑(widenlattice(lattice), widenconst(a), b)
    elseif isa(b, PartialOpaque)
        return false
    end
    if isa(a, PartialTask)
        if isa(b, PartialTask)
            return ⊑(lattice, a.fetch_type, b.fetch_type)
        end
        return ⊑(widenlattice(lattice), Task, b)
    elseif isa(b, PartialTask)
        return false
    end
    return ⊑(widenlattice(lattice), a, b)
end
```

Julia source: Compiler/src/typelattice.jl:547-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function ⊑(lattice::ConstsLattice, @nospecialize(a), @nospecialize(b))
    if isa(a, Const)
        if isa(b, Const)
            return a.val === b.val
        end
        # TODO: `b` could potentially be a `PartialTypeVar` here, in which case we might be
        # able to return `true` in more cases; in the meantime, just returning this is the
        # most conservative option.
        return isa(b, Type) && isa(a.val, b)
    elseif isa(b, Const)
        if issingletontype(a)
            return a.instance === b.val
        end
        return false
    elseif isa(a, PartialTypeVar)
        return b === TypeVar || a === b
    elseif isa(b, PartialTypeVar)
        return false
    end
    return ⊑(widenlattice(lattice), a, b)
end
```

`⊑(::JLTypeLattice, ...)` is `sqsubJLType` (`Compiler/src/abstractlattice.jl:153`). -/
def sqsub (n : Nat) (E : CEnv) (L : Lattice) (a b : LElt) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    let le := sqsub n E
    match L with
    | .jlType => sqsubJLType n E a b
    | .inference p => do
      if !(← le p (ignorelimited a) (ignorelimited b)) then return false
      let .limitedAccuracy btyp bcauses _ := b | return true
      let abEq ← le p btyp (ignorelimited a)
      if !abEq then
        return true
      let .limitedAccuracy _ acauses _ := a | return false
      return bcauses.all acauses.contains
    | .conditionals p | .interConditionals p => do
      let inter := L matches .interConditionals _
      if b.isAny then return true
      if a.isAny then return false
      if a.isBottom then return true
      if b.isBottom then return false
      let mut a := a
      if isConditionalT inter a then
        if isConditionalT inter b then
          return ← issubconditional le L a b
        else if let .const bval := b then
          if let some bb := asBool? bval then
            return maybeExtractConstBool a == some bb
        a := .ty boolTy
      else if isConditionalT inter b then
        if let .const aval := a then
          if let some ab := asBool? aval then
            let (bt, be) := match b with
              | .conditional _ _ t e _ | .interConditional _ t e => (t, e)
              | _ => (b, b)
            if (ab && bt.isAny && be.isBottom) || (!ab && be.isAny && bt.isBottom) then
              -- this Conditional contains distinctly no lattice information
              return true
        return false
      le p a b
    | .mustAliases p | .interMustAliases p => do
      let inter := L matches .interMustAliases _
      let mut a := a
      if isMustAliasT inter a then
        if isMustAliasT inter b then
          return ← issubalias le a b
        a ← widenmustalias a
      else if isMustAliasT inter b then
        return a.isBottom
      le p a b
    | .partials p => do
      if let .partialStruct atyp aundefs afields _ _ := a then
        if let .partialStruct btyp bundefs bfields _ _ := b then
          if !(← issub n E atyp btyp) then return false
          let nflds := afields.length
          if nflds != bfields.length then return false
          for i in [1:nflds+1] do
            let bu ← jlIndex bundefs i
            if bu != none then
              if (← jlIndex aundefs i) != bu then
                return false
            let af ← jlIndex afields i
            let bf ← jlIndex bfields i
            if i == nflds then
              if af.isVarargElt then
                if !bf.isVarargElt then jlThrow "AssertionError" "isvarargtype(bf)"
                continue
              else if bf.isVarargElt then
                continue
            if !(← le L af bf) then return false
          return true
        let .ty bt := b | return false
        if !bt.isType then return false
        return ← issub n E atyp bt
      else if let .partialStruct btyp bundefs bfields _ _ := b then
        if let .const aval := a then
          let widea ← widenconst n E a
          if !widea.isDatatype then return false
          let wideb := btyp
          let wideb' := wideb.unwrapUnionall
          if !wideb'.isDatatype then jlThrow "TypeError" "typeassert DataType"
          if widea.name? != wideb'.name? then return false
          if wideb'.name? == some tupleName then
            if (← nfieldsOf E aval) != bfields.length then return false
          else
            if !(← issub n E widea wideb) then return false
            if !(decide ((← nInitializedConst E aval) ≥ nInitializedPartialStruct bundefs)) then
              return false
          let nf ← nfieldsOf E aval
          for i in [1:nf+1] do
            if !isdefinedField aval i then
              if (← jlIndex bundefs i) == some false then return false
              continue
            if i > bfields.length then break
            if (← jlIndex bundefs i) == some true then
              return false
            let mut bfi ← jlIndex bfields i
            if i == nf then
              bfi := match bfi with | .ty t => .ty (unwrapva t) | x => x
            if !(← le L (.const (← getfieldVal aval i)) bfi) then return false
          return true
        return false
      if let .partialOpaque atyp aenv apar asrc := a then
        if let .partialOpaque btyp benv bpar bsrc := b then
          if !(apar == bpar && asrc == bsrc) then return false
          if !(← issub n E atyp btyp) then return false
          return ← le L aenv benv
        return ← le p (.ty atyp) b
      else if b.isPartialOpaque then
        return false
      if let .partialTask afetch := a then
        if let .partialTask bfetch := b then
          return ← le L afetch bfetch
        return ← le p (.ty taskType) b
      else if b.isPartialTask then
        return false
      le p a b
    | .consts => do
      if let .const aval := a then
        if let .const bval := b then
          return ← egal n E aval bval
        let .ty bt := b | return false
        if !bt.isType then return false
        return ← isa n E aval bt
      else if let .const bval := b then
        if let .ty aT := a then
          if ← issingletontype n E aT then
            return ← egal n E (singletonInstance E aT) bval
        return false
      else if a.isPartialTypeVar then
        if let .ty bt := b then
          if bt == tvarType then return true
        return ← eltEgal n E a b
      else if b.isPartialTypeVar then
        return false
      le .jlType a b

/-- `is_lattice_bool(lattice, typ)`

Julia source: Compiler/src/typelattice.jl:285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer is_lattice_bool(lattice::AbstractLattice, @nospecialize(typ)) = typ !== Bottom && ⊑(lattice, typ, Bool)
```
-/
def isLatticeBool (n : Nat) (E : CEnv) (L : Lattice) (typ : LElt) : CM Bool := do
  if typ.isBottom then return false
  sqsub n E L typ (.ty boolTy)

/-- `⊏(𝕃, a, b)`

Julia source: Compiler/src/abstractlattice.jl:155-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    ⊏(𝕃::AbstractLattice, a, b)::Bool

The strict partial order over the type inference lattice.
This is defined as the irreflexive kernel of `⊑`.
"""
@nospecializeinfer ⊏(𝕃::AbstractLattice, @nospecialize(a), @nospecialize(b)) = ⊑(𝕃, a, b) && !⊑(𝕃, b, a)
```
-/
def sqsubStrict (n : Nat) (E : CEnv) (L : Lattice) (a b : LElt) : CM Bool := do
  if !(← sqsub n E L a b) then return false
  return !(← sqsub n E L b a)

/-- `⋤(𝕃, a, b)`

Julia source: Compiler/src/abstractlattice.jl:163-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    ⋤(𝕃::AbstractLattice, a, b)::Bool

This order could be used as a slightly more efficient version of the strict order `⊏`,
where we can safely assume `a ⊑ b` holds.
"""
@nospecializeinfer ⋤(𝕃::AbstractLattice, @nospecialize(a), @nospecialize(b)) = !⊑(𝕃, b, a)
```
-/
def sqsubStrictNe (n : Nat) (E : CEnv) (L : Lattice) (a b : LElt) : CM Bool := do
  return !(← sqsub n E L b a)

/-! ## Lattice equality -/

/-- `is_lattice_equal(𝕃, a, b)` for every layer. `JLTypeLattice` and the two must-alias layers
use the generic method.

Julia source: Compiler/src/abstractlattice.jl:171-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    is_lattice_equal(𝕃::AbstractLattice, a, b)::Bool

Check if two lattice elements are partial order equivalent.
This is basically `a ⊑ b && b ⊑ a` in the lattice of `𝕃`
but (optionally) with extra performance optimizations.
"""
@nospecializeinfer function is_lattice_equal(𝕃::AbstractLattice, @nospecialize(a), @nospecialize(b))
    a === b && return true
    return ⊑(𝕃, a, b) && ⊑(𝕃, b, a)
end
```

Julia source: Compiler/src/typelattice.jl:569-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function is_lattice_equal(lattice::InferenceLattice, @nospecialize(a), @nospecialize(b))
    if isa(a, LimitedAccuracy)
        isa(b, LimitedAccuracy) || return false
        a.causes == b.causes || return false
        a = a.typ
        b = b.typ
    elseif isa(b, LimitedAccuracy)
        return false
    end
    return is_lattice_equal(widenlattice(lattice), a, b)
end

@nospecializeinfer function is_lattice_equal(lattice::AnyConditionalsLattice, @nospecialize(a), @nospecialize(b))
    ConditionalT = isa(lattice, ConditionalsLattice) ? Conditional : InterConditional
    if isa(a, ConditionalT) || isa(b, ConditionalT)
        # TODO: Unwrap these and recurse to is_lattice_equal
        return ⊑(lattice, a, b) && ⊑(lattice, b, a)
    end
    return is_lattice_equal(widenlattice(lattice), a, b)
end

@nospecializeinfer function is_lattice_equal(lattice::PartialsLattice, @nospecialize(a), @nospecialize(b))
    if isa(a, PartialStruct)
        isa(b, PartialStruct) || return false
        length(a.fields) == length(b.fields) || return false
        _getundefs(a) == _getundefs(b) || return false
        widenconst(a) == widenconst(b) || return false
        a.fields === b.fields && return true # fast path
        for i in 1:length(a.fields)
            is_lattice_equal(lattice, a.fields[i], b.fields[i]) || return false
        end
        return true
    end
    isa(b, PartialStruct) && return false
    if isa(a, PartialOpaque)
        isa(b, PartialOpaque) || return false
        widenconst(a) == widenconst(b) || return false
        a.source === b.source || return false
        a.parent === b.parent || return false
        return is_lattice_equal(lattice, a.env, b.env)
    end
    isa(b, PartialOpaque) && return false
    if isa(a, PartialTask)
        isa(b, PartialTask) || return false
        return is_lattice_equal(lattice, a.fetch_type, b.fetch_type)
    end
    isa(b, PartialTask) && return false
    return is_lattice_equal(widenlattice(lattice), a, b)
end

@nospecializeinfer function is_lattice_equal(lattice::ConstsLattice, @nospecialize(a), @nospecialize(b))
    a === b && return true
    if a isa Const
        if issingletontype(b)
            return a.val === b.instance
        end
        # N.B. Assumes a === b checked above
        return false
    end
    if b isa Const
        if issingletontype(a)
            return a.instance === b.val
        end
        # N.B. Assumes a === b checked above
        return false
    end
    if isa(a, PartialTypeVar) || isa(b, PartialTypeVar)
        return false
    end
    return is_lattice_equal(widenlattice(lattice), a, b)
end
```
-/
def isLatticeEqual (n : Nat) (E : CEnv) (L : Lattice) (a b : LElt) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    let generic : CM Bool := do
      if ← eltEgal n E a b then return true
      if !(← sqsub n E L a b) then return false
      sqsub n E L b a
    match L with
    | .jlType | .mustAliases _ | .interMustAliases _ => generic
    | .inference p => do
      let mut a := a
      let mut b := b
      if let .limitedAccuracy atyp acauses _ := a then
        let .limitedAccuracy btyp bcauses _ := b | return false
        if !(acauses.all bcauses.contains && bcauses.all acauses.contains) then return false
        a := atyp
        b := btyp
      else if b.isLimited then
        return false
      isLatticeEqual n E p a b
    | .conditionals p | .interConditionals p => do
      let inter := L matches .interConditionals _
      if isConditionalT inter a || isConditionalT inter b then
        if !(← sqsub n E L a b) then return false
        return ← sqsub n E L b a
      isLatticeEqual n E p a b
    | .partials p => do
      if let .partialStruct atyp aundefs afields _ afid := a then
        let .partialStruct btyp bundefs bfields _ bfid := b | return false
        if afields.length != bfields.length then return false
        if aundefs != bundefs then return false
        if !(← tyEq n E atyp btyp) then return false
        if afid == bfid then return true
        for i in [1:afields.length+1] do
          if !(← isLatticeEqual n E L (← jlIndex afields i) (← jlIndex bfields i)) then
            return false
        return true
      if b.isPartialStruct then return false
      if let .partialOpaque atyp aenv apar asrc := a then
        let .partialOpaque btyp benv bpar bsrc := b | return false
        if !(← tyEq n E atyp btyp) then return false
        if asrc != bsrc then return false
        if apar != bpar then return false
        return ← isLatticeEqual n E L aenv benv
      if b.isPartialOpaque then return false
      if let .partialTask afetch := a then
        let .partialTask bfetch := b | return false
        return ← isLatticeEqual n E L afetch bfetch
      if b.isPartialTask then return false
      isLatticeEqual n E p a b
    | .consts => do
      if ← eltEgal n E a b then return true
      if let .const aval := a then
        if let .ty bt := b then
          if ← issingletontype n E bt then
            return ← egal n E aval (singletonInstance E bt)
        return false
      if let .const bval := b then
        if let .ty aT := a then
          if ← issingletontype n E aT then
            return ← egal n E (singletonInstance E aT) bval
        return false
      if a.isPartialTypeVar || b.isPartialTypeVar then
        return false
      isLatticeEqual n E .jlType a b

/-! ## Lattice meet -/

/-- `getfield_tfunc` and `tuple_tfunc` (`Compiler/src/tfuncs.jl`), which the `Tuple` branch of
`tmeet(::PartialsLattice, ...)` calls. -/
structure TmeetOps where
  /-- `widenconst(getfield_tfunc(lattice, t, Const(i)))` -/
  getfieldTfuncWiden : Lattice → Val → Nat → CM Val
  /-- `tuple_tfunc(lattice, fields)` -/
  tupleTfunc : Lattice → List LElt → CM LElt

def tmeetOpsUnmodelled : TmeetOps where
  getfieldTfuncWiden _ _ _ := unmodelled "getfield_tfunc"
  tupleTfunc _ _ := unmodelled "tuple_tfunc"

/-- `tmeet(𝕃, v, t::AnyType)` for every layer.

Julia source: Compiler/src/typelattice.jl:644-727 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function tmeet(lattice::PartialsLattice, @nospecialize(v), @nospecialize(t::AnyType))
    if isa(v, PartialStruct)
        has_free_typevars(t) && return v
        widev = widenconst(v)
        ti = typeintersect(widev, t)
        if ti === widev
            return v
        end
        valid_as_lattice(ti, true) || return Bottom
        if widev <: Tuple
            new_fields = Vector{Any}(undef, length(v.fields))
            for i = 1:length(new_fields)
                vfi = v.fields[i]
                if isvarargtype(vfi)
                    new_fields[i] = vfi
                else
                    nfi = new_fields[i] = tmeet(lattice, vfi, widenconst(getfield_tfunc(lattice, t, Const(i))))
                    if nfi === Bottom
                        return Bottom
                    end
                end
            end
            return tuple_tfunc(lattice, new_fields)
        end
        v = widev
    elseif isa(v, PartialOpaque)
        has_free_typevars(t) && return v
        widev = widenconst(v)
        if widev <: t
            return v
        end
        ti = typeintersect(widev, t)
        valid_as_lattice(ti, true) || return Bottom
        return PartialOpaque(ti, v.env, v.parent, v.source)
    elseif isa(v, PartialTask)
        has_free_typevars(t) && return v
        return Task <: t ? v : Bottom
    end
    return tmeet(widenlattice(lattice), v, t)
end

@nospecializeinfer function tmeet(lattice::ConstsLattice, @nospecialize(v), @nospecialize(t::AnyType))
    if isa(v, Const)
        if !has_free_typevars(t) && !isa(v.val, t)
            return Bottom
        end
        return v
    end
    tmeet(widenlattice(lattice), widenconst_split(v), t)
end

@nospecializeinfer function tmeet(lattice::ConditionalsLattice, @nospecialize(v), @nospecialize(t::AnyType))
    if isa(v, Conditional)
        if !(Bool <: t)
            return Bottom
        end
        return v
    end
    tmeet(widenlattice(lattice), v, t)
end

@nospecializeinfer function tmeet(𝕃::AnyMustAliasesLattice, @nospecialize(v), @nospecialize(t::AnyType))
    if is_valid_lattice_norec(𝕃, v)
        # The value still is the aliased field, so meet the field type and keep the alias,
        # unless the field value is now known
        fldtyp = tmeet(widenlattice(𝕃), v.fldtyp, t)
        fldtyp === Bottom && return Bottom
        isalreadyconst(fldtyp) && return fldtyp
        return update_mustalias(v; fldtyp)
    end
    return tmeet(widenlattice(𝕃), v, t)
end

@nospecializeinfer function tmeet(lattice::InferenceLattice, @nospecialize(v), @nospecialize(t::AnyType))
    # TODO: This can probably happen and should be handled
    @assert !isa(v, LimitedAccuracy)
    tmeet(widenlattice(lattice), v, t)
end

@nospecializeinfer function tmeet(lattice::InterConditionalsLattice, @nospecialize(v), @nospecialize(t::AnyType))
    # TODO: This can probably happen and should be handled
    @assert !isa(v, AnyConditional)
    tmeet(widenlattice(lattice), v, t)
end
```
`tmeet(::JLTypeLattice, ...)` is `tmeetJLType` (`Compiler/src/abstractlattice.jl:110-114`).
Each method declares `t::AnyType`, so a `t` that is not a type is a `MethodError`. -/
def tmeet (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice) (v : LElt) (t : Val) : CM LElt :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if !t.isType then jlThrow "MethodError" "tmeet(..., t::AnyType)"
    match L with
    | .jlType => tmeetJLType n E v t
    | .partials p => do
      let mut v := v
      if let .partialStruct vtyp _ vfields _ _ := v then
        if hasFreeTypevars t then return v
        let widev := vtyp
        let ti ← typeintersect n E widev t
        if ← egal n E ti widev then
          return v
        if !(← validAsLattice n E ti true) then return .ty .bottom
        if ← issub n E widev anytupleType then
          let mut newFields : List LElt := []
          for i in [1:vfields.length+1] do
            let vfi ← jlIndex vfields i
            if vfi.isVarargElt then
              newFields := newFields ++ [vfi]
            else
              let nfi ← tmeet ops n E L vfi (← ops.getfieldTfuncWiden L t i)
              newFields := newFields ++ [nfi]
              if nfi.isBottom then
                return .ty .bottom
          return ← ops.tupleTfunc L newFields
        v := .ty widev
      else if let .partialOpaque vtyp venv vpar vsrc := v then
        if hasFreeTypevars t then return v
        let widev := vtyp
        if ← issub n E widev t then
          return v
        let ti ← typeintersect n E widev t
        if !(← validAsLattice n E ti true) then return .ty .bottom
        return .partialOpaque ti venv vpar vsrc
      else if v.isPartialTask then
        if hasFreeTypevars t then return v
        return if ← issub n E taskType t then v else .ty .bottom
      tmeet ops n E p v t
    | .consts => do
      if let .const val := v then
        if !hasFreeTypevars t then
          if !(← isa n E val t) then
            return .ty .bottom
        return v
      tmeet ops n E .jlType (.ty (← widenconstSplit n E v)) t
    | .conditionals p => do
      if v.isConditional then
        if !(← issub n E boolTy t) then
          return .ty .bottom
        return v
      tmeet ops n E p v t
    | .mustAliases p | .interMustAliases p => do
      if isValidLatticeNorec L v then
        let vfld ← match v with
          | .mustAlias _ _ _ _ f | .interMustAlias _ _ _ f => pure f
          | _ => jlThrow "ErrorException" "fldtyp"
        let fldtyp ← tmeet ops n E p vfld t
        if fldtyp.isBottom then return .ty .bottom
        if ← isalreadyconst n E fldtyp then return fldtyp
        return ← updateMustalias v (fldtyp := some fldtyp)
      tmeet ops n E p v t
    | .inference p => do
      if v.isLimited then jlThrow "AssertionError" "!isa(v, LimitedAccuracy)"
      tmeet ops n E p v t
    | .interConditionals p => do
      if v.isAnyConditional then jlThrow "AssertionError" "!isa(v, AnyConditional)"
      tmeet ops n E p v t

/-! ## Other uses of the order -/

/-- `widenlattice(𝕃, t)`

Julia source: Compiler/src/abstractlattice.jl:320-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Widenlattice with argument
widenlattice(::JLTypeLattice, @nospecialize(t)) = widenconst(t)
function widenlattice(𝕃::AbstractLattice, @nospecialize(t))
    is_valid_lattice_norec(𝕃, t) && return t
    widenlattice(widenlattice(𝕃), t)
end
```
-/
def widenlatticeElt (n : Nat) (E : CEnv) : Lattice → LElt → CM LElt
  | .jlType, t => return .ty (← widenconst n E t)
  | .consts, t => do
    if isValidLatticeNorec .consts t then return t
    return .ty (← widenconst n E t)
  | L@(.partials p), t | L@(.conditionals p), t | L@(.interConditionals p), t
  | L@(.mustAliases p), t | L@(.interMustAliases p), t | L@(.inference p), t =>
    if isValidLatticeNorec L t then pure t else widenlatticeElt n E p t

/-- `narrow_mustalias(𝕃, x, y)`

Julia source: Compiler/src/typelattice.jl:377-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Narrow `x` by the must-alias information of `y`, if possible.
# Otherwise return x unchanged.
@nospecializeinfer function narrow_mustalias(𝕃::AbstractLattice, @nospecialize(x), @nospecialize(y))
    alias = ignorelimited(y)
    !isa(alias, AnyMustAlias) && return x
    typ = ignorelimited(x)
    typ === Bottom && return x # Union{} is maximally narrow
    isa(typ, AnyMustAlias) && return x # do not attempt to intersect alias information
    isa(typ, AnyConditional) && return x # ... or other wrappers
    # keep a known value as is, like the `getfield` case of `abstract_call_builtin`
    isalreadyconst(typ) && return x
    # this is an intersection with `y`, so keep the limitations of both
    return narrow_limited_typ(narrow_limited_typ(update_mustalias(alias; fldtyp = typ), x), y)
end
```
-/
def narrowMustalias (n : Nat) (E : CEnv) (_L : Lattice) (x y : LElt) : CM LElt := do
  let alias := ignorelimited y
  if !alias.isAnyMustAlias then return x
  let typ := ignorelimited x
  if typ.isBottom then return x
  if typ.isAnyMustAlias then return x
  if typ.isAnyConditional then return x
  if ← isalreadyconst n E typ then return x
  narrowLimitedTyp (← narrowLimitedTyp (← updateMustalias alias (fldtyp := some typ)) x) y

/-! ## State management -/

/-- `VarState` (`Compiler/src/types.jl:85-90`); `none` is `NOT_FOUND`. -/
structure VarState where
  typ : LElt
  ssadef : Int
  undef : Bool
  deriving Repr, Inhabited

/-- `smerge(lattice, sa, sb, join_pc)`; `tmerge` is the `tmerge` of `typelimits.jl`.

Julia source: Compiler/src/typelattice.jl:770-775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function smerge(lattice::AbstractLattice, sa::Union{NotFound,VarState}, sb::Union{NotFound,VarState}, join_pc::Int)
    sa === sb && return sa
    sa === NOT_FOUND && return sb
    sb === NOT_FOUND && return sa
    return VarState(tmerge(lattice, sa.typ, sb.typ), sa.ssadef == sb.ssadef ? sa.ssadef : join_pc, sa.undef | sb.undef)
end
```
-/
def smerge (n : Nat) (E : CEnv) (tmerge : Lattice → LElt → LElt → CM LElt) (L : Lattice)
    (sa sb : Option VarState) (joinPc : Int) : CM (Option VarState) := do
  match sa, sb with
  | none, none => return sa
  | some a, some b =>
    if (← eltEgal n E a.typ b.typ) && a.ssadef == b.ssadef && a.undef == b.undef then
      return sa
    return some ⟨← tmerge L a.typ b.typ, if a.ssadef == b.ssadef then a.ssadef else joinPc,
      a.undef || b.undef⟩
  | none, _ => return sb
  | _, none => return sa

/-- `schanged(lattice, n, o, join_pc)`

Julia source: Compiler/src/typelattice.jl:777-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer @inline schanged(lattice::AbstractLattice, @nospecialize(n), @nospecialize(o), join_pc::Int) =
    (n !== o) && (o === NOT_FOUND || (n !== NOT_FOUND && !(n.undef <= o.undef && (n.ssadef === o.ssadef || o.ssadef === join_pc) && ⊑(lattice, n.typ, o.typ))))
```
-/
def schanged (fuel : Nat) (E : CEnv) (L : Lattice) (n o : Option VarState) (joinPc : Int) :
    CM Bool := do
  let same ← match n, o with
    | none, none => pure true
    | some a, some b => do
      if a.ssadef == b.ssadef && a.undef == b.undef then eltEgal fuel E a.typ b.typ else pure false
    | _, _ => pure false
  if same then return false
  match n, o with
  | _, none => return true
  | none, _ => return false
  | some nv, some ov =>
    -- `n.undef <= o.undef` on `Bool`
    if !((!nv.undef || ov.undef) && (nv.ssadef == ov.ssadef || ov.ssadef == joinPc)) then
      return true
    return !(← sqsub fuel E L nv.typ ov.typ)

/-- `stupdate!(lattice, state, changes, join_pc)`, returning the new state and `changed`.

Julia source: Compiler/src/typelattice.jl:780-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function stupdate!(lattice::AbstractLattice, state::VarTable, changes::VarTable, join_pc::Int)
    changed = false
    for i = 1:length(state)
        newtype = changes[i]
        oldtype = state[i]
        # In addition to computing the type, the merge here computes the "reaching definition"
        # for a slot. The provided `join_pc` is a "virtual" PC, which corresponds to the ϕ-block
        # that would exist at the beginning of the BasicBlock.
        #
        # This effectively applies the "path-convergence criterion" for SSA construction.
        if schanged(lattice, newtype, oldtype, join_pc)
            state[i] = smerge(lattice, oldtype, newtype, join_pc)
            changed = true
        end
    end
    return changed
end
```
-/
def stupdate (n : Nat) (E : CEnv) (tmerge : Lattice → LElt → LElt → CM LElt) (L : Lattice)
    (state changes : List (Option VarState)) (joinPc : Int) :
    CM (List (Option VarState) × Bool) := do
  let mut state := state
  let mut changed := false
  for i in [0:state.length] do
    let newtype ← jlIndex changes (i + 1)
    let oldtype := state[i]!
    if ← schanged n E L newtype oldtype joinPc then
      state := state.set i (← smerge n E tmerge L oldtype newtype joinPc)
      changed := true
  return (state, changed)

/-! ## `fallback_lattice` methods -/

/-- `a ⊑ b`, `a ⊏ b`, `a ⋤ b`, `is_lattice_equal(a, b)` and `tmeet(a, b)` without a lattice.

Julia source: Compiler/src/abstractlattice.jl:313-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer @nospecialize(a) ⊑ @nospecialize(b) = ⊑(fallback_lattice, a, b)
@nospecializeinfer @nospecialize(a) ⊏ @nospecialize(b) = ⊏(fallback_lattice, a, b)
@nospecializeinfer @nospecialize(a) ⋤ @nospecialize(b) = ⋤(fallback_lattice, a, b)
@nospecializeinfer tmeet(@nospecialize(a), @nospecialize(b)) = tmeet(fallback_lattice, a, b)
@nospecializeinfer tmerge(@nospecialize(a), @nospecialize(b)) = tmerge(fallback_lattice, a, b)
@nospecializeinfer is_lattice_equal(@nospecialize(a), @nospecialize(b)) = is_lattice_equal(fallback_lattice, a, b)
```
-/
def sqsubFallback (n : Nat) (E : CEnv) (a b : LElt) : CM Bool := sqsub n E fallbackLattice a b
def sqsubStrictFallback (n : Nat) (E : CEnv) (a b : LElt) : CM Bool :=
  sqsubStrict n E fallbackLattice a b
def sqsubStrictNeFallback (n : Nat) (E : CEnv) (a b : LElt) : CM Bool :=
  sqsubStrictNe n E fallbackLattice a b
def isLatticeEqualFallback (n : Nat) (E : CEnv) (a b : LElt) : CM Bool :=
  isLatticeEqual n E fallbackLattice a b

end JuliaLean.Compiler
