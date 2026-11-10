import JuliaLean.Compiler.Prelude

/-!
The helpers of `Compiler/src/typeutils.jl` that the lattice files call, and the ones that need
nothing beyond `Prelude`. The functions of `typeutils.jl` that call `widenconst`, `tmerge` or the
union and tuple constructors of `typelimits.lean` are in `typeutils/lattice.lean`, because
`typelattice.lean` and `typelimits.lean` import this file.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-- `isconstType(t)`

Julia source: Compiler/src/typeutils.jl:12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isconstType(@nospecialize t) = isTypeEgal(t) || (isTypeEq(t) && type_parameter(t) === Union{})
```
-/
def isconstType (t : Val) : Bool :=
  isTypeEgal t || (isTypeEq t && t.someTypeT == .bottom)

/-- `isstructtype(t)` (`base/runtime_internals.jl:870-876`): a `DataType` that is neither
primitive nor abstract. -/
def isstructtype (E : CEnv) (t : Val) : CM Bool := do
  match t.unwrapUnionall with
  | .datatype name _ =>
    let tn ← E.types.typename name
    return !E.primitives.contains name && !tn.abstract
  | _ => return false

/-- `valid_as_lattice(x, astag)`

Julia source: Compiler/src/typeutils.jl:55-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# determine whether x is a valid lattice element
# For example, Type{v} is not valid if v is a value
# Accepts TypeVars and has_free_typevar also, since it assumes the user will rewrap it correctly
# If astag is true, then also requires that it be a possible type tag for a valid object
function valid_as_lattice(@nospecialize(x), astag::Bool=false)
    x === Bottom && false
    x isa TypeVar && return valid_as_lattice(x.ub, astag)
    x isa UnionAll && (x = unwrap_unionall(x))
    if x isa Union
        # the Union constructor ensures this (and we'll recheck after
        # operations that might remove the Union itself)
        return true
    end
    if isType(x)
        p = type_parameter(x)
        p isa Type || p isa TypeVar || return false
        return true
    end
    if x isa DataType
        if astag && isstructtype(x)
            datatype_fieldtypes(x) # force computation of has_concrete_subtype to be updated now
            return has_concrete_subtype(x)
        end
        return true
    end
    return false
end
```
The first line has no effect (its value is discarded), so `Bottom` reaches the final
`return false`. -/
def validAsLattice (n : Nat) (E : CEnv) (x : Val) (astag : Bool := false) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let _ := x == .bottom
    if x.isTypevar then return ← validAsLattice n E x.tvUb astag
    let x := if x.isUnionall then x.unwrapUnionall else x
    if x.isUnion then
      return true
    if isType x then
      let p := x.someTypeT
      if !(p.isType || p.isTypevar) then return false
      return true
    if x.isDatatype then
      if astag then
        if ← isstructtype E x then
          return ← hasConcreteSubtype n E.types x
      return true
    return false

/-- `isTypeDataType(t)`

Julia source: Compiler/src/typeutils.jl:23-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
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
def isTypeDataType (t : Val) : Bool :=
  if isType t then false
  else match t with
    | .datatype name _ => if t == typeofbottomType then false else name != tupleName
    | _ => false

/-- `has_extended_info(x)`

Julia source: Compiler/src/typeutils.jl:32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_extended_info(@nospecialize x) = (!isa(x, Type) && !isvarargtype(x)) || isType(x)
```
-/
def hasExtendedInfo (x : LElt) : Bool :=
  match x with
  | .ty t => (!t.isType && !isvarargtype t) || isType t
  | _ => true

/-- `isknownlength(t::DataType)`; another argument is a `MethodError`.

Julia source: Compiler/src/typeutils.jl:47-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isknownlength(t::DataType)
    isvatuple(t) || return true
    va = t.parameters[end]
    return isdefined(va, :N) && va.N isa Int
end
```
`isvatuple` (`base/essentials.jl:593-601`) is true for a `DataType` whose last parameter is a
`Vararg`; `t` is already unwrapped. -/
def isknownlength (t : Val) : CM Bool := do
  let .datatype _ ps := t | jlThrow "MethodError" "isknownlength"
  let some va := ps.getLast? | return true
  if !va.isVararg then return true
  match va with
  | .vararg _ (some (.long _)) => return true
  | _ => return false

/-- `has_concrete_subtype(d::DataType)`: the `0x0020` flag, which the C model computes.

Julia source: Compiler/src/typeutils.jl:53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_concrete_subtype(d::DataType) = d.flags & 0x0020 == 0x0020 # n.b. often computed only after setting the type and layout fields
```
-/
def hasConcreteSubtypeDT (n : Nat) (E : CEnv) (d : Val) : CM Bool := do
  if !d.isDatatype then jlThrow "MethodError" "has_concrete_subtype"
  hasConcreteSubtype n E.types d

/-- `valid_typeof_tparam(t)`

Julia source: Compiler/src/typeutils.jl:83-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function valid_typeof_tparam(@nospecialize(t))
    if t === Symbol || t === Module || isbitstype(t)
        return true
    end
    isconcretetype(t) || return false
    if t <: NamedTuple
        t = t.parameters[2]::DataType
    end
    if t <: Tuple
        for p in t.parameters
            valid_typeof_tparam(p) || return false
        end
        return true
    end
    return false
end
```
`t <: NamedTuple` and `t <: Tuple` are asked of a concrete `DataType`, where they hold exactly
when its name is `NamedTuple` or `Tuple`. -/
def validTypeofTparam (n : Nat) (E : CEnv) (t : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if t == symbolType || t == .datatype "Core.Module" [] || (← isBits n E.types t) then
      return true
    if !(← isConcreteType E.types t) then return false
    let mut t := t
    if t.name? == some "Core.NamedTuple" then
      match t.params[1]? with
      | some p => if p.isDatatype then t := p else
          jlThrow "TypeError" "valid_typeof_tparam: NamedTuple parameter"
      | none => jlThrow "BoundsError" "valid_typeof_tparam"
    if t.isTupleType then
      for p in t.params do
        if !(← validTypeofTparam n E p) then return false
      return true
    return false

/-- `valid_tparam(x)` for a non-type, non-`TypeVar` `x`.

Julia source: Compiler/src/typeutils.jl:100-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# test if non-Type, non-TypeVar `x` can be used to parameterize a type
valid_tparam(@nospecialize(x)) = valid_typeof_tparam(typeof(x))
```
-/
def validTparam (n : Nat) (E : CEnv) (x : Val) : CM Bool := validTypeofTparam n E (typeOf x)

/-- `compatible_vatuple(a::DataType, b::DataType)`

Julia source: Compiler/src/typeutils.jl:103-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compatible_vatuple(a::DataType, b::DataType)
    vaa = a.parameters[end]
    vab = b.parameters[end]
    if !(isvarargtype(vaa) && isvarargtype(vab))
        return isvarargtype(vaa) == isvarargtype(vab)
    end
    isdefined(vaa, :N) || return !isdefined(vab, :N)
    isdefined(vab, :N) || return false
    return vaa.N === vab.N
end
```
-/
def compatibleVatuple (n : Nat) (E : CEnv) (a b : Val) : CM Bool := do
  if !a.isDatatype || !b.isDatatype then jlThrow "MethodError" "compatible_vatuple"
  let some vaa := a.params.getLast? | jlThrow "BoundsError" "compatible_vatuple"
  let some vab := b.params.getLast? | jlThrow "BoundsError" "compatible_vatuple"
  if !(isvarargtype vaa && isvarargtype vab) then
    return isvarargtype vaa == isvarargtype vab
  match vaa, vab with
  | .vararg _ none, .vararg _ nb => return nb.isNone
  | .vararg _ (some _), .vararg _ none => return false
  | .vararg _ (some na), .vararg _ (some nb) => egal n E na nb
  | _, _ => return false

/-- `unionall_depth(ua)`

Julia source: Compiler/src/typeutils.jl:416-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unionall_depth(@nospecialize ua) # aka subtype_env_size
    depth = 0
    while ua isa UnionAll
        depth += 1
        ua = ua.body
    end
    return depth
end
```
-/
def unionallDepth : Val → Nat
  | .unionall _ _ _ _ body => unionallDepth body + 1
  | _ => 0

/-- `unwraptv_lb(t)`; `unwraptv_ub` (`unwraptv`) is in `typelimits.lean`.

Julia source: Compiler/src/typeutils.jl:431-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unwraptv_lb(@nospecialize t)
    while isa(t, TypeVar)
        t = t.lb
    end
    return t
end
```
-/
def unwraptvLb : Val → Val
  | .typevar _ _ lb _ => unwraptvLb lb
  | t => t

/-! ## Alias groups of call arguments -/

/-- An entry of `fargs` (the call's IR arguments). Only `SlotNumber`s and `SSAValue`s take part in
the alias checks, and two of them are `===` exactly when they are the same kind with the same
number; every other IR argument is `other`. -/
inductive FArg where
  | slot (id : Int)
  | ssa (id : Int)
  | other
  deriving BEq, Repr, Inhabited

def FArg.isSlotOrSSA : FArg → Bool
  | .other => false
  | _ => true

/-- `fargs[i]` (1-based) with Julia's bounds check. -/
def fargAt (fargs : List FArg) (i : Nat) : CM FArg :=
  match fargs[i - 1]? with
  | some a => pure a
  | none => jlThrow "BoundsError" "fargs"

/-- `argtypes[i]` (1-based) with Julia's bounds check. -/
def eltAt (argtypes : List LElt) (i : Nat) : CM LElt :=
  match argtypes[i - 1]? with
  | some a => pure a
  | none => jlThrow "BoundsError" "argtypes"

/-- `any_alias_candidate(na, fargs, argtypes)`

Julia source: Compiler/src/typeutils.jl:213-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Cheap, non-allocating necessary condition for a non-identity grouping: a shared
# `SlotNumber`/`SSAValue` in `fargs`, or at least two `MustAlias` in `argtypes`.
# Over-approximating only costs a needless allocation, never correctness.
function any_alias_candidate(
        na::Int,
        fargs::Union{Nothing,Vector{Any}},
        argtypes::Union{Nothing,Vector{Any}}
    )
    if fargs !== nothing
        for i = 1:na
            arg_i = fargs[i]
            if arg_i isa SlotNumber || arg_i isa SSAValue
                for j in 1:i-1
                    fargs[j] === arg_i && return true
                end
            end
        end
    end
    if argtypes !== nothing
        nmustalias = 0
        for i = 1:na
            if argtypes[i] isa MustAlias
                nmustalias += 1
                nmustalias == 2 && return true
            end
        end
    end
    return false
end
```
-/
def anyAliasCandidate (na : Nat) (fargs : Option (List FArg)) (argtypes : Option (List LElt)) :
    CM Bool := do
  if let some fa := fargs then
    for i in List.range' 1 na do
      let argI ← fargAt fa i
      if argI.isSlotOrSSA then
        for j in List.range' 1 (i - 1) do
          if (← fargAt fa j) == argI then return true
  if let some ats := argtypes then
    let mut nmustalias := 0
    for i in List.range' 1 na do
      if (← eltAt ats i).isMustAlias then
        nmustalias := nmustalias + 1
        if nmustalias == 2 then return true
  return false

/-- `merge_fargs_alias_groups!(groups, fargs)`; `groups` holds the 1-based leader of each
position.

Julia source: Compiler/src/typeutils.jl:243-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Detect aliasing from IR identity: same `SlotNumber`/`SSAValue` in `fargs`.
function merge_fargs_alias_groups!(groups::Vector{Int}, fargs::Vector{Any})
    for i = 1:length(groups)
        arg_i = fargs[i]
        if arg_i isa SlotNumber || arg_i isa SSAValue
            for j in 1:i-1
                if fargs[j] === arg_i
                    groups[i] = groups[j]
                    break
                end
            end
        end
    end
    return groups
end
```
-/
def mergeFargsAliasGroups (groups : Array Nat) (fargs : List FArg) : CM (Array Nat) := do
  let mut groups := groups
  for i in List.range' 1 groups.size do
    let argI ← fargAt fargs i
    if argI.isSlotOrSSA then
      for j in List.range' 1 (i - 1) do
        if (← fargAt fargs j) == argI then
          groups := groups.set! (i - 1) groups[j - 1]!
          break
  return groups

/-- `merge_mustalias_groups!(groups, argtypes)`

Julia source: Compiler/src/typeutils.jl:259-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Detect additional aliasing from `MustAlias` lattice elements in `argtypes`:
# two positions with the same `(slot, ssadef, fldidx)` must refer to the same value.
function merge_mustalias_groups!(groups::Vector{Int}, argtypes::Vector{Any})
    for i = 1:length(groups)
        groups[i] == i || continue # already a follower
        ti = argtypes[i]
        ti isa MustAlias || continue
        for j in 1:i-1
            groups[j] == j || continue # only match against leaders
            tj = argtypes[j]
            tj isa MustAlias || continue
            if ti.slot == tj.slot && ti.ssadef == tj.ssadef && ti.fldidx == tj.fldidx
                # Merge: make j the leader for i, and re-point any
                # existing followers of i to j as well
                for k in i:length(groups)
                    if groups[k] == i
                        groups[k] = j
                    end
                end
                break
            end
        end
    end
    return groups
end
```
-/
def mergeMustaliasGroups (groups : Array Nat) (argtypes : List LElt) : CM (Array Nat) := do
  let mut groups := groups
  for i in List.range' 1 groups.size do
    if groups[i - 1]! != i then continue
    let ti ← eltAt argtypes i
    let .mustAlias si di _ fi _ := ti | continue
    for j in List.range' 1 (i - 1) do
      if groups[j - 1]! != j then continue
      let tj ← eltAt argtypes j
      let .mustAlias sj dj _ fj _ := tj | continue
      if si == sj && di == dj && fi == fj then
        for k in List.range' i (groups.size + 1 - i) do
          if groups[k - 1]! == i then
            groups := groups.set! (k - 1) j
        break
  return groups

/-- `compute_alias_groups(na, fargs, argtypes)`: `none` for `nothing`.

Julia source: Compiler/src/typeutils.jl:187-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Given `fargs` from `ArgInfo` and optionally `argtypes`, compute alias groups
# for argument positions. Returns `nothing` when no aliasing is possible (both
# callers treat this as the identity grouping), otherwise a `Vector{Int}` where
# `groups[i]` is the index of the leader for position `i`. `groups[i] == i` means
# leader (or non-aliased); `groups[i] < i` means follower.
# ...
function compute_alias_groups(
        na::Int,
        fargs::Union{Nothing,Vector{Any}},
        argtypes::Union{Nothing,Vector{Any}}
    )
    # Fast path: skip the allocation when no aliasing is possible (the common
    # case on the inference hot path).
    any_alias_candidate(na, fargs, argtypes) || return nothing
    groups = Vector{Int}(undef, na)
    for i = 1:na
        groups[i] = i
    end
    fargs !== nothing && merge_fargs_alias_groups!(groups, fargs)
    argtypes !== nothing && merge_mustalias_groups!(groups, argtypes)
    return groups
end
```
-/
def computeAliasGroups (na : Nat) (fargs : Option (List FArg)) (argtypes : Option (List LElt)) :
    CM (Option (Array Nat)) := do
  if !(← anyAliasCandidate na fargs argtypes) then return none
  let mut groups : Array Nat := (List.range' 1 na).toArray
  if let some fa := fargs then groups ← mergeFargsAliasGroups groups fa
  if let some ats := argtypes then groups ← mergeMustaliasGroups groups ats
  return some groups

end JuliaLean.Compiler
