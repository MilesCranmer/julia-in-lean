import JuliaLean.Compiler.src.typeutils
import JuliaLean.Compiler.src.typelimits

/-!
The functions of `Compiler/src/typeutils.jl` that call `widenconst`, the union and tuple
constructors or `<:`, and the union-splitting limit check of `abstractinterpretation.jl` that uses
them. They cannot sit in `typeutils.lean`, which `typelattice.lean` and `typelimits.lean` import.

The pilot already modelled `unioncomplexity` (`unioncomplexity`), `unwraptv_ub` (`unwraptv`),
`_typename` (`typenameT`) and `tuple_tail_elem` (`tupleTailElem`) in `typelimits.lean`, and
`valid_as_lattice`, `isconstType` and `isstructtype` in `typeutils.lean`; they are reused here.

Not modelled: `is_identity_free_argtype` and `is_mutation_free_argtype`
(`Compiler/src/typeutils.jl:449-450,481-483`), which read the `isidentityfree` and
`ismutationfree` flags that C computes for each `DataType` and the type model does not record.

`fargs` entries are `FArg`s. An `argtypes::Vector{Any}` is a `List LElt`; a `SimpleVector` of
types (`a.parameters` in `typesubtract`) is a `List LElt` of `.ty` with `isVector = false`.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-- `a <: b` (`jl_f_issubtype`): both arguments must be types (`JL_TYPECHK(<:, type, ...)`), so a
`TypeVar` or `Vararg` is a `TypeError`. -/
def subtypeChecked (n : Nat) (E : CEnv) (a b : Val) : CM Bool := do
  if !a.isType then jlThrow "TypeError" "<:"
  if !b.isType then jlThrow "TypeError" "<:"
  issub n E a b

/-- `isnotbrokensubtype(a, b)`

Julia source: Compiler/src/typeutils.jl:34-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Subtyping currently intentionally answers certain queries incorrectly for kind types. For
# some of these queries, this check can be used to somewhat protect against making incorrect
# decisions based on incorrect subtyping. Note that this check, itself, is broken for
# certain combinations of `a` and `b` where one/both isa/are `Union`/`UnionAll` type(s)s.
isnotbrokensubtype(@nospecialize(a), @nospecialize(b)) = (!iskindtype(b) || !isType(a) || b <: a)
```
-/
def isnotbrokensubtype (n : Nat) (E : CEnv) (a b : Val) : CM Bool := do
  if !iskindtype b then return true
  if !isType a then return true
  subtypeChecked n E b a

/-- `argtypes_to_type(argtypes)`

Julia source: Compiler/src/typeutils.jl:40-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function argtypes_to_type(argtypes::Vector{Any})
    argtypes = anymap(@nospecialize(a) -> isvarargtype(a) ? a : widenconst_split(a), argtypes)
    filter!(@nospecialize(x) -> !isvarargtype(x) || valid_as_lattice(unwrapva(x), true), argtypes)
    all(@nospecialize(x) -> isvarargtype(x) || valid_as_lattice(x, true), argtypes) || return Bottom
    return Tuple{argtypes...}
end
```
-/
def argtypesToType (n : Nat) (E : CEnv) (argtypes : List LElt) : CM Val := do
  let argtypes ← argtypes.mapM fun a => match a with
    | .ty t => if isvarargtype t then pure t else widenconstSplit n E a
    | a => widenconstSplit n E a
  let argtypes ← argtypes.filterM fun x => do
    if !isvarargtype x then return true
    validAsLattice n E (unwrapva x) true
  for x in argtypes do
    if !(isvarargtype x || (← validAsLattice n E x true)) then return .bottom
  jlTuple n E argtypes

/-- `typemax(Int)` -/
def typemaxInt : Int := 9223372036854775807

/-- `unionsplitcost(𝕃, argtypes; fargs)`; `isVector` says whether `argtypes` is a `Vector{Any}`
(alias groups from `MustAlias`) or a `SimpleVector`.

Julia source: Compiler/src/typeutils.jl:285-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Gives a cost function over the effort to switch a tuple-union representation
# as a cartesian product, relative to the size of the original representation.
# Thus, we count the longest element as being roughly invariant to being inside
# or outside of the Tuple/Union nesting, though somewhat more expensive to be
# outside than inside because the representation is larger (because it
# informs the callee whether any splitting is possible).
function unionsplitcost(𝕃::AbstractLattice, argtypes::Union{SimpleVector,Vector{Any}};
                        fargs::Union{Nothing,Vector{Any}}=nothing)
    na = length(argtypes)
    groups = compute_alias_groups(na, fargs, argtypes isa Vector{Any} ? argtypes : nothing)
    nu = 1
    max = 2
    for i in 1:na
        # skip followers: their type is constrained by their leader
        if groups !== nothing && groups[i] != i
            continue
        end
        ti = argtypes[i]
        if has_extended_unionsplit(𝕃) && !isvarargtype(ti)
            ti = widenconst_split(ti)
        end
        if isa(ti, Union)
            nti = unionlen(ti)
            if nti > max
                max, nti = nti, max
            end
            nu, ovf = Core.Intrinsics.checked_smul_int(nu, nti)
            ovf && return typemax(Int)
        end
    end
    return nu
end
```
-/
def unionsplitcost (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt) (isVector : Bool)
    (fargs : Option (List FArg) := none) : CM Int := do
  let na := argtypes.length
  let groups ← computeAliasGroups na fargs (if isVector then some argtypes else none)
  let mut nu : Int := 1
  let mut max : Nat := 2
  for i in List.range' 1 na do
    if let some g := groups then
      if g[i - 1]! != i then continue
    let mut ti ← eltAt argtypes i
    if hasExtendedUnionsplit L && !ti.isVarargElt then
      ti := .ty (← widenconstSplit n E ti)
    if let .ty u@(.union ..) := ti then
      let mut nti := unionlen u
      if nti > max then
        (max, nti) := (nti, max)
      nu := nu * nti
      if nu > typemaxInt then return typemaxInt
  return nu

/-- `is_union_split_eligible(𝕃, argtypes, max_union_splitting; fargs)`

Julia source: Compiler/src/abstractinterpretation.jl:395-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_union_split_eligible(𝕃::AbstractLattice, argtypes::Vector{Any}, max_union_splitting::Int;
                        fargs::Union{Nothing,Vector{Any}}=nothing) =
    1 < unionsplitcost(𝕃, argtypes; fargs) <= max_union_splitting
```
-/
def isUnionSplitEligible (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt)
    (maxUnionSplitting : Int) (fargs : Option (List FArg) := none) : CM Bool := do
  let c ← unionsplitcost n E L argtypes true fargs
  return 1 < c && c ≤ maxUnionSplitting

/-- `_switchtupleunion(𝕃, t, i, tunion, origt, groups)`. `emit` is what the `i == 0` case pushes:
`copy(t)` when `origt === nothing`, `rewrap_unionall(Tuple{t...}, origt)` otherwise. `t` is passed
by value, so the restores after each loop leave nothing to undo; they are kept to mirror the
source.

Julia source: Compiler/src/typeutils.jl:333-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _switchtupleunion(𝕃::AbstractLattice, t::Vector{Any}, i::Int, tunion::Vector{Any},
                           @nospecialize(origt), groups::Union{Nothing,Vector{Int}}=nothing)
    if i == 0
        if origt === nothing
            push!(tunion, copy(t))
        else
            tpl = rewrap_unionall(Tuple{t...}, origt)
            push!(tunion, tpl)
        end
        return tunion
    end

    if groups !== nothing && groups[i] != i
        # If this position is a follower (aliased to an earlier position),
        # its type is already set by the leader — just recurse without iterating.
        _switchtupleunion(𝕃, t, i - 1, tunion, origt, groups)
    else
        origti = ti = t[i]
        followers = Int[]
        if groups !== nothing
            for j in 1:length(t)
                if groups[j] == i # Collect follower indices for this leader
                    push!(followers, j)
                end
            end
        end
        # TODO Generalize this to allow callsite union-splitting of MustAlias
        if isa(ti, Union)
            origtypes = Any[t[j] for j in followers]
            for ty in uniontypes(ti)
                t[i] = ty
                for j in followers
                    t[j] = ty
                end
                _switchtupleunion(𝕃, t, i - 1, tunion, origt, groups)
            end
            t[i] = origti
            for (k, j) in enumerate(followers)
                t[j] = origtypes[k]
            end
        elseif (has_extended_unionsplit(𝕃) && !isa(ti, Const) && !isvarargtype(ti) &&
            (wty = widenconst(ti); isa(wty, Union)))
            origtypes = Any[t[j] for j in followers]
            for ty in uniontypes(wty)
                t[i] = ty
                for j in followers
                    t[j] = ty
                end
                _switchtupleunion(𝕃, t, i - 1, tunion, origt, groups)
            end
            t[i] = origti
            for (k, j) in enumerate(followers)
                t[j] = origtypes[k]
            end
        else
            _switchtupleunion(𝕃, t, i - 1, tunion, origt, groups)
        end
    end
    return tunion
end
```
-/
def switchtupleunion_ {α : Type} (n : Nat) (E : CEnv) (L : Lattice) (emit : Array LElt → CM α)
    (t : Array LElt) (i : Nat) (tunion : Array α) (groups : Option (Array Nat)) :
    CM (Array α) :=
  match i with
  | 0 => do return tunion.push (← emit t)
  | i' + 1 => do
    let i := i' + 1
    if let some g := groups then
      if g[i - 1]! != i then
        return ← switchtupleunion_ n E L emit t i' tunion groups
    let some origti := t[i - 1]? | jlThrow "BoundsError" "_switchtupleunion"
    let ti := origti
    let mut followers : Array Nat := #[]
    if let some g := groups then
      for j in List.range' 1 t.size do
        if g[j - 1]! == i then followers := followers.push j
    -- The types to split over: `uniontypes(ti)` or `uniontypes(widenconst(ti))`, if any.
    let parts? : Option (List Val) ← do
      if let .ty u@(.union ..) := ti then pure (some (uniontypes u))
      else if hasExtendedUnionsplit L && !ti.isConst && !ti.isVarargElt then
        let wty ← widenconst n E ti
        if wty.isUnion then pure (some (uniontypes wty)) else pure none
      else pure none
    match parts? with
    | some parts =>
      let origtypes := followers.map fun j => t[j - 1]!
      let mut t := t
      let mut tunion := tunion
      for ty in parts do
        t := t.set! (i - 1) (.ty ty)
        for j in followers do
          t := t.set! (j - 1) (.ty ty)
        tunion ← switchtupleunion_ n E L emit t i' tunion groups
      t := t.set! (i - 1) origti
      for (j, k) in followers.toList.zip (List.range followers.size) do
        t := t.set! (j - 1) origtypes[k]!
      return tunion
    | none => switchtupleunion_ n E L emit t i' tunion groups

/-- `switchtupleunion(ty)`

Julia source: Compiler/src/typeutils.jl:318-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# take a Tuple where one or more parameters are Unions
# and return an array such that those Unions are removed
# and `Union{return...} == ty`
function switchtupleunion(@nospecialize(ty))
    tparams = (unwrap_unionall(ty)::DataType).parameters
    return _switchtupleunion(JLTypeLattice(), Any[tparams...], length(tparams), [], ty)
end
```
-/
def switchtupleunion (n : Nat) (E : CEnv) (ty : Val) : CM (List Val) := do
  let .datatype _ tparams := ty.unwrapUnionall
    | jlThrow "TypeError" "switchtupleunion: expected DataType"
  let emit (t : Array LElt) : CM Val := do
    let ps ← t.toList.mapM fun
      | .ty p => pure p
      | _ => throw "switchtupleunion: non-type parameter"
    rewrapUnionallJ n E (← jlTuple n E ps) ty
  let r ← switchtupleunion_ n E .jlType emit (tparams.map LElt.ty).toArray tparams.length #[] none
  return r.toList

/-- `switchtupleunion(𝕃, argtypes; fargs)`

Julia source: Compiler/src/typeutils.jl:326-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function switchtupleunion(𝕃::AbstractLattice, argtypes::Vector{Any};
                          fargs::Union{Nothing,Vector{Any}}=nothing)
    na = length(argtypes)
    groups = compute_alias_groups(na, fargs, argtypes)
    return _switchtupleunion(𝕃, argtypes, na, [], nothing, groups)
end
```
-/
def switchtupleunionL (n : Nat) (E : CEnv) (L : Lattice) (argtypes : List LElt)
    (fargs : Option (List FArg) := none) : CM (List (List LElt)) := do
  let na := argtypes.length
  let groups ← computeAliasGroups na fargs (some argtypes)
  let r ← switchtupleunion_ n E L (fun t => pure t.toList) argtypes.toArray na #[] groups
  return r.toList

/-- `typesubtract(a, b, max_union_splitting)`

Julia source: Compiler/src/typeutils.jl:114-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# return an upper-bound on type `a` with type `b` removed
# and also any contents that are not valid type tags on any objects
# such that `return <: a` && `Union{return, b} == Union{a, b}`
function typesubtract(@nospecialize(a), @nospecialize(b), max_union_splitting::Int)
    if a <: b && isnotbrokensubtype(a, b)
        return Bottom
    end
    ua = unwrap_unionall(a)
    if isa(ua, Union)
        uua = typesubtract(rewrap_unionall(ua.a, a), b, max_union_splitting)
        uub = typesubtract(rewrap_unionall(ua.b, a), b, max_union_splitting)
        return Union{valid_as_lattice(uua, true) ? uua : Union{},
                     valid_as_lattice(uub, true) ? uub : Union{}}
    elseif a isa DataType
        ub = unwrap_unionall(b)
        if ub isa DataType
            if a.name === ub.name === Tuple.name && length(a.parameters) == length(ub.parameters)
                if 1 < unionsplitcost(JLTypeLattice(), a.parameters) <= max_union_splitting
                    ta = switchtupleunion(a)
                    return typesubtract(Union{ta...}, b, 0)
                elseif b isa DataType
                    if !compatible_vatuple(a, b)
                        return a
                    end
                    # if exactly one element is not bottom after calling typesubtract
                    # then the result is all of the elements as normal except that one
                    notbottom = fill(false, length(a.parameters))
                    for i = 1:length(notbottom)
                        ap = unwrapva(a.parameters[i])
                        bp = unwrapva(b.parameters[i])
                        notbottom[i] = !(ap <: bp && isnotbrokensubtype(ap, bp))
                    end
                    let i = findfirst(notbottom)
                        if i !== nothing && findnext(notbottom, i + 1) === nothing
                            ta = collect(a.parameters)
                            ap = a.parameters[i]
                            bp = b.parameters[i]
                            (isvarargtype(ap) || isvarargtype(bp)) && return a
                            ta[i] = typesubtract(ap, bp, min(2, max_union_splitting))
                            ta[i] === Union{} && return Union{}
                            return Tuple{ta...}
                        end
                    end
                end
            end
        end
    end
    return a # TODO: improve this bound?
end
```
`a.name === ub.name === Tuple.name` is `a.name === ub.name && ub.name === Tuple.name`. -/
def typesubtract (n : Nat) (E : CEnv) (a b : Val) (maxUnionSplitting : Int) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if (← subtypeChecked n E a b) && (← isnotbrokensubtype n E a b) then
      return .bottom
    let ua := a.unwrapUnionall
    if let .union x y := ua then
      let uua ← typesubtract n E (← rewrapUnionallJ n E x a) b maxUnionSplitting
      let uub ← typesubtract n E (← rewrapUnionallJ n E y a) b maxUnionSplitting
      let p1 := if ← validAsLattice n E uua true then uua else .bottom
      let p2 := if ← validAsLattice n E uub true then uub else .bottom
      return ← jlUnion n E [p1, p2]
    if let .datatype aname aps := a then
      let ub := b.unwrapUnionall
      if let .datatype ubname ubps := ub then
        if aname == ubname && ubname == tupleName && aps.length == ubps.length then
          let c ← unionsplitcost n E .jlType (aps.map LElt.ty) false
          if 1 < c && c ≤ maxUnionSplitting then
            let ta ← switchtupleunion n E a
            return ← typesubtract n E (← jlUnion n E ta) b 0
          else if let .datatype _ bps := b then
            if !(← compatibleVatuple n E a b) then
              return a
            let mut notbottom : Array Bool := #[]
            for (ap, bp) in aps.zip bps do
              let ap := unwrapva ap
              let bp := unwrapva bp
              let s ← if ← subtypeChecked n E ap bp then isnotbrokensubtype n E ap bp
                else pure false
              notbottom := notbottom.push !s
            match notbottom.findIdx? id with
            | some i =>
              if (notbottom.toList.drop (i + 1)).all (! ·) then
                let ap := aps[i]!
                let bp := bps[i]!
                if isvarargtype ap || isvarargtype bp then return a
                let r ← typesubtract n E ap bp (min 2 maxUnionSplitting)
                if r == .bottom then return .bottom
                return ← jlTuple n E (aps.set i r)
            | none => pure ()
    return a

/-- `is_immutable_type(ty)` and `_is_immutable_type(ty)`.

Julia source: Compiler/src/typeutils.jl:462-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_immutable_type(@nospecialize ty) = _is_immutable_type(unwrap_unionall(ty))
function _is_immutable_type(@nospecialize ty)
    if isa(ty, Union)
        return _is_immutable_type(ty.a) && _is_immutable_type(ty.b)
    end
    isType(ty) && return false
    return !isabstracttype(ty) && !ismutabletype(ty)
end
```
`ismutabletype(t)` (`base/runtime_internals.jl:854-859`) is
`(t = unwrap_unionall(t); isa(t, DataType) && ismutabletypename(t.name))`. -/
def isImmutableType_ (E : CEnv) : Val → CM Bool
  | .union a b => do
    if !(← isImmutableType_ E a) then return false
    isImmutableType_ E b
  | ty => do
    if isType ty then return false
    if ← isabstracttype E ty then return false
    match ty.unwrapUnionall with
    | .datatype name _ => return !(← E.types.typename name).mutable
    | _ => return true

def isImmutableType (E : CEnv) (ty : Val) : CM Bool := isImmutableType_ E ty.unwrapUnionall

/-- `is_immutable_argtype(argtype)`

Julia source: Compiler/src/typeutils.jl:452-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    is_immutable_argtype(argtype)::Bool

Return `true` if the `argtype` object is known to be immutable.
...
"""
is_immutable_argtype(@nospecialize argtype) = is_immutable_type(widenconst_split(ignorelimited(argtype)))
```
-/
def isImmutableArgtype (n : Nat) (E : CEnv) (argtype : LElt) : CM Bool := do
  isImmutableType E (← widenconstSplit n E (ignorelimited argtype))

end JuliaLean.Compiler
