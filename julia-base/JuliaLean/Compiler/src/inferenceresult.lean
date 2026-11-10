import JuliaLean.Compiler.src.tfuncs

/-!
`Compiler/src/inferenceresult.jl`: the argument types an `InferenceResult` is cached under, and the
lookup of constant-propagation results in the local `InferenceCache`.

* `most_general_argtypes` turns a `MethodInstance`'s `specTypes` into the cache argument types of
  its non-constant inference (singletons and constant types become `Const`, the `Vararg` tail is
  canonicalised against `method.nargs`).
* `pick_const_args!`, `pick_const_arg` and `is_argtype_match` choose, position by position, between
  the argument types of a call and those cache argument types, which gives the key of a
  const-prop result.
* `va_process_argtypes` folds the trailing arguments of a varargs method into one tuple type.
* `constprop_cache_lookup` scans the cache entries of one `MethodInstance` for a result whose key
  matches the call's argument types under `is_lattice_equal`.

A `MethodInstance` or `Method` enters only through the fields these functions read (`nargs`,
`nospecialize`, `nospecializeinfer`, whether `specTypes` ends in a `Vararg`); cache entries are
records of the fields `constprop_cache_lookup` reads.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-- `unwrapva` on a lattice element: a `Vararg` element gives its element type. -/
def unwrapvaLElt : LElt → LElt
  | .ty t => .ty (unwrapva t)
  | e => e

/-- `Vararg{x}` for a lattice element `x` (`apply_type(Vararg, x)`): only types and `TypeVar`s
are valid parameters. -/
def varargOfElt (n : Nat) (E : CEnv) (x : LElt) : CM LElt := do
  match x with
  | .ty t => return .ty (← jlVararg n E t)
  | _ => jlThrow "TypeError" "Vararg"

/-- `argtypes[i]` for a 1-based `i`. -/
def atIdx (xs : List LElt) (i : Int) : CM LElt :=
  if i < 1 then jlThrow "BoundsError" "argtypes"
  else match xs[(i - 1).toNat]? with
    | some x => pure x
    | none => jlThrow "BoundsError" "argtypes"

/-- `argtype_by_index(argtypes, i)`, which the functions of this file call. It is defined in
`Compiler/src/abstractinterpretation.jl:2166-2174` (f755f49a9e41380d7da126b3c1db9fe7f83dd027):
```julia
function argtype_by_index(argtypes::Vector{Any}, i::Int)
    n = length(argtypes)
    na = argtypes[n]
    if isvarargtype(na)
        return i >= n ? unwrapva(na) : argtypes[i]
    else
        return i > n ? Bottom : argtypes[i]
    end
end
```
-/
def argtypeByIndex (argtypes : List LElt) (i : Int) : CM LElt := do
  let n : Int := argtypes.length
  let na ← atIdx argtypes n
  if na.isVarargElt then
    if i ≥ n then return unwrapvaLElt na else atIdx argtypes i
  else
    if i > n then return .ty .bottom else atIdx argtypes i

/-- `elim_free_typevars(t)`

Julia source: Compiler/src/inferenceresult.jl:204-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# eliminate free `TypeVar`s in order to make the life much easier down the road:
# at runtime only `Type{...}::DataType` can contain invalid type parameters, and other
# malformed types here are user-constructed type arguments given at an inference entry
# so this function will replace only the malformed `Type{...}::DataType` with `Type`
# and simply replace other possibilities with `Any`
function elim_free_typevars(@nospecialize t)
    if has_free_typevars(t)
        return isType(t) ? Type : Any
    else
        return t
    end
end
```
-/
def elimFreeTypevars (t : Val) : Val :=
  if hasFreeTypevars t then
    if isType t then typeTypeVal else anyType
  else t

/-- `most_general_argtypes(method, specTypes)`, with `nargs` the method's `nargs` (`none` for
`method === nothing`).

Julia source: Compiler/src/inferenceresult.jl:162-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function most_general_argtypes(method::Union{Method,Nothing}, @nospecialize(specTypes))
    params = (unwrap_unionall(specTypes)::DataType).parameters
    mi_argtypes = Any[params[i] for i = 1:length(params)]
    nargtypes = length(mi_argtypes)
    nargs = isa(method, Method) ? Int(method.nargs) : 0
    if length(mi_argtypes) < nargs && isvarargtype(mi_argtypes[end])
        resize!(mi_argtypes, nargs)
    end
    # Now, we propagate type info from `mi_argtypes` into `cache_argtypes`, improving some
    # type info as we go (where possible). Note that if we're dealing with a varargs method,
    # we already handled the last element of `cache_argtypes` (and decremented `nargs` so that
    # we don't overwrite the result of that work here).
    tail_index = min(nargtypes, nargs)
    local lastatype
    for i = 1:nargtypes
        atyp = mi_argtypes[i]
        wasva = false
        if i == nargtypes && isvarargtype(atyp)
            wasva = true
            atyp = unwrapva(atyp)
        end
        atyp = unwraptv(atyp)
        if issingletontype(atyp)
            # replace singleton types with their equivalent Const object
            atyp = Const(atyp.instance)
        elseif isconstType(atyp)
            atyp = Const(type_parameter(atyp))
        else
            atyp = elim_free_typevars(rewrap_unionall(atyp, specTypes))
        end
        mi_argtypes[i] = atyp
        if wasva
            lastatype = atyp
            mi_argtypes[end] = Vararg{widenconst(atyp)}
        end
    end
    for i = (tail_index+1):(nargs-1)
        mi_argtypes[i] = lastatype
    end
    return mi_argtypes
end
```
`mi_argtypes[i]` is read at step `i` before anything writes it: earlier steps write only smaller
indices, and `mi_argtypes[end]` is written only at the last step. -/
def mostGeneralArgtypes (n : Nat) (E : CEnv) (nargs? : Option Nat) (specTypes : Val) :
    CM (List LElt) := do
  let .datatype _ params := specTypes.unwrapUnionall
    | jlThrow "TypeError" "typeassert DataType"
  let nargtypes := params.length
  let nargs := nargs?.getD 0
  let mut mi : Array (Option LElt) := (params.map fun p => some (LElt.ty p)).toArray
  if mi.size < nargs then
    let some lastp := params.getLast? | jlThrow "BoundsError" "mi_argtypes[end]"
    if lastp.isVararg then
      mi := mi ++ Array.replicate (nargs - mi.size) none
  let tailIndex := min nargtypes nargs
  let mut lastatype : Option LElt := none
  for i in [1:nargtypes + 1] do
    let mut atyp := params[i - 1]!
    let mut wasva := false
    if i == nargtypes && atyp.isVararg then
      wasva := true
      atyp := unwrapva atyp
    atyp ← unwraptv n atyp
    let e : LElt ←
      if ← issingletontype n E atyp then pure (.const (singletonInstance E atyp))
      else if isconstType atyp then pure (.const (← typeParameter atyp))
      else pure (.ty (elimFreeTypevars (← rewrapUnionallJ n E atyp specTypes)))
    mi := mi.set! (i - 1) (some e)
    if wasva then
      lastatype := some e
      mi := mi.set! (mi.size - 1) (some (.ty (← jlVararg n E (← widenconst n E e))))
  for i in [tailIndex + 1:nargs] do
    let some la := lastatype | jlThrow "UndefVarError" "lastatype"
    if i > mi.size then jlThrow "BoundsError" "mi_argtypes"
    mi := mi.set! (i - 1) (some la)
  mi.toList.mapM fun
    | some e => pure e
    | none => jlThrow "UndefRefError" "mi_argtypes"

/-- `matching_cache_argtypes(𝕃, mi)`

Julia source: Compiler/src/inferenceresult.jl:3-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function matching_cache_argtypes(::AbstractLattice, mi::MethodInstance)
    (; def, specTypes) = mi
    return most_general_argtypes(isa(def, Method) ? def : nothing, specTypes)
end
```
-/
def matchingCacheArgtypesMI (n : Nat) (E : CEnv) (nargs? : Option Nat) (specTypes : Val) :
    CM (List LElt) :=
  mostGeneralArgtypes n E nargs? specTypes

/-- `get_nospecializeinfer_argtypes(argtypes, cache_argtypes, method)`, with the method's
`nospecializeinfer` flag, `nospecialize` bitmask and `nargs`. `is_nospecializeinfer(method)` is
`method.nospecializeinfer && method.nospecialize ≠ 0` (`base/runtime_internals.jl:1968-1969`).

Julia source: Compiler/src/inferenceresult.jl:8-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# For `@nospecializeinfer` methods, widen the `@nospecialize`'d argument positions back to
# `cache_argtypes` values to respect the `@nospecializeinfer` semantics.
# This also ensures that the constprop `argtypes` have the same length as `cache_argtypes`.
function get_nospecializeinfer_argtypes(argtypes::Vector{Any}, cache_argtypes::Vector{Any},
                                        method::Method)
    is_nospecializeinfer(method) || return argtypes
    nargs = Int(method.nargs)
    new_argtypes = Vector{Any}(undef, length(cache_argtypes))
    for i = 1:length(cache_argtypes)
        i_arg = min(i - 1, nargs - 1) # 0-indexed, 0 is the function slot
        if i_arg > 0 && !iszero(method.nospecialize & (1 << (i_arg - 1)))
            new_argtypes[i] = cache_argtypes[i]
        else
            new_argtypes[i] = argtypes[i]
        end
    end
    return new_argtypes
end
```
The mask is a nonnegative `Int32` and `i_arg ≤ nargs - 1`, so the shifted bit is the mask's bit
`i_arg - 1`. -/
def getNospecializeinferArgtypes (nospecializeinfer : Bool) (nospecialize : Nat) (nargs : Nat)
    (argtypes cacheArgtypes : List LElt) : CM (List LElt) := do
  if !(nospecializeinfer && nospecialize != 0) then return argtypes
  let mut out : List LElt := []
  for i in [1:cacheArgtypes.length + 1] do
    let iArg : Int := min ((i : Int) - 1) ((nargs : Int) - 1)
    if iArg > 0 && nospecialize.testBit (iArg - 1).toNat then
      out := out ++ [← atIdx cacheArgtypes i]
    else
      out := out ++ [← atIdx argtypes i]
  return out

/-- `is_argtype_match(𝕃, given_argtype, cache_argtype, overridden_by_const)`

Julia source: Compiler/src/inferenceresult.jl:100-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_argtype_match(𝕃::AbstractLattice,
                          @nospecialize(given_argtype),
                          @nospecialize(cache_argtype),
                          overridden_by_const::Bool)
    if is_forwardable_argtype(𝕃, given_argtype)
        return is_lattice_equal(𝕃, given_argtype, cache_argtype)
    else
        return !overridden_by_const
    end
end
```
-/
def isArgtypeMatch (n : Nat) (E : CEnv) (L : Lattice) (given cache : LElt)
    (overriddenByConst : Bool) : CM Bool := do
  if isForwardableArgtype L given then
    isLatticeEqual n E L given cache
  else
    return !overriddenByConst

/-- `pick_const_arg(𝕃, given_argtype, cache_argtype)`; `ops` supplies the `getfield_tfunc` and
`tuple_tfunc` calls of `tmeet`.

Julia source: Compiler/src/inferenceresult.jl:49-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pick_const_arg(𝕃::AbstractLattice, @nospecialize(given_argtype), @nospecialize(cache_argtype))
    if !is_argtype_match(𝕃, given_argtype, cache_argtype, false)
        # prefer the argtype we were given over the one computed from `mi`
        if (isa(given_argtype, PartialStruct) && isa(cache_argtype, Type) &&
            !⊏(𝕃, given_argtype, cache_argtype))
            # if the type information of this `PartialStruct` is less strict than
            # declared method signature, narrow it down using `tmeet`
            given_argtype = tmeet(𝕃, given_argtype, cache_argtype)
        end
        return given_argtype
    else
        return cache_argtype
    end
end
```
-/
def pickConstArg (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice) (given cache : LElt) :
    CM LElt := do
  if !(← isArgtypeMatch n E L given cache false) then
    let mut given := given
    if given.isPartialStruct && cache.isTypeElt then
      if !(← sqsubStrict n E L given cache) then
        let .ty ct := cache | jlThrow "ErrorException" "unreachable"
        given ← tmeet ops n E L given ct
    return given
  else
    return cache

/-- `resize!(a, k)`: truncate, or grow with undefined slots. -/
def resizeOpt (a : Array (Option LElt)) (k : Nat) : Array (Option LElt) :=
  if k ≤ a.size then a.extract 0 k else a ++ Array.replicate (k - a.size) none

def getOpt (a : Array (Option LElt)) (i : Nat) : CM LElt :=
  match a[i - 1]? with
  | some (some x) => pure x
  | some none => jlThrow "UndefRefError" "given_argtypes"
  | none => jlThrow "BoundsError" "given_argtypes"

def setOpt (a : Array (Option LElt)) (i : Nat) (x : LElt) : CM (Array (Option LElt)) :=
  if 1 ≤ i && i ≤ a.size then pure (a.set! (i - 1) (some x))
  else jlThrow "BoundsError" "given_argtypes"

/-- `pick_const_args!(𝕃, given_argtypes, cache_argtypes)`

Julia source: Compiler/src/inferenceresult.jl:64-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pick_const_args!(𝕃::AbstractLattice, given_argtypes::Vector{Any}, cache_argtypes::Vector{Any})
    ngiven = length(given_argtypes)
    ncache = length(cache_argtypes)
    if ngiven == 0 || ncache == 0
        return Any[]
    end
    given_va = given_argtypes[end]
    cache_va = cache_argtypes[end]
    if isvarargtype(given_va)
        va = unwrapva(given_va)
        if isvarargtype(cache_va)
            # Process the common prefix, then join
            nprocessargs = max(ngiven-1, ncache-1)
            resize!(given_argtypes, nprocessargs+1)
            given_argtypes[end] = Vararg{pick_const_arg(𝕃, va, unwrapva(cache_va))}
        else
            nprocessargs = ncache
            resize!(given_argtypes, nprocessargs)
        end
        for i = ngiven:nprocessargs
            given_argtypes[i] = va
        end
    elseif isvarargtype(cache_va)
        nprocessargs = ngiven
    else
        @assert ngiven == ncache
        nprocessargs = ngiven
    end
    for i = 1:nprocessargs
        given_argtype = given_argtypes[i]
        cache_argtype = argtype_by_index(cache_argtypes, i)
        given_argtypes[i] = pick_const_arg(𝕃, given_argtype, cache_argtype)
    end
    return given_argtypes
end
```
-/
def pickConstArgs (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice)
    (givenArgtypes cacheArgtypes : List LElt) : CM (List LElt) := do
  let ngiven := givenArgtypes.length
  let ncache := cacheArgtypes.length
  if ngiven == 0 || ncache == 0 then return []
  let givenVa := givenArgtypes.getLast!
  let cacheVa := cacheArgtypes.getLast!
  let mut g : Array (Option LElt) := (givenArgtypes.map some).toArray
  let mut nprocessargs := 0
  if givenVa.isVarargElt then
    let va := unwrapvaLElt givenVa
    if cacheVa.isVarargElt then
      nprocessargs := max (ngiven - 1) (ncache - 1)
      g := resizeOpt g (nprocessargs + 1)
      let picked ← pickConstArg ops n E L va (unwrapvaLElt cacheVa)
      g ← setOpt g g.size (← varargOfElt n E picked)
    else
      nprocessargs := ncache
      g := resizeOpt g nprocessargs
    for i in [ngiven:nprocessargs + 1] do
      g ← setOpt g i va
  else if cacheVa.isVarargElt then
    nprocessargs := ngiven
  else
    if ngiven != ncache then jlThrow "AssertionError" "ngiven == ncache"
    nprocessargs := ngiven
  for i in [1:nprocessargs + 1] do
    let givenArgtype ← getOpt g i
    let cacheArgtype ← argtypeByIndex cacheArgtypes i
    g ← setOpt g i (← pickConstArg ops n E L givenArgtype cacheArgtype)
  g.toList.mapM fun
    | some e => pure e
    | none => jlThrow "UndefRefError" "given_argtypes"

/-- `matching_cache_argtypes(𝕃, mi, simple_argtypes::Union{SimpleArgtypes, WidenedArgtypes},
cache_argtypes)`

Julia source: Compiler/src/inferenceresult.jl:38-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function matching_cache_argtypes(𝕃::AbstractLattice, ::MethodInstance,
                                 simple_argtypes::Union{SimpleArgtypes, WidenedArgtypes},
                                 cache_argtypes::Vector{Any})
    (; argtypes) = simple_argtypes
    given_argtypes = Vector{Any}(undef, length(argtypes))
    for i = 1:length(argtypes)
        given_argtypes[i] = widenslotwrapper(argtypes[i])
    end
    return pick_const_args!(𝕃, given_argtypes, cache_argtypes)
end
```
-/
def matchingCacheArgtypesSimple (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice)
    (argtypes cacheArgtypes : List LElt) : CM (List LElt) := do
  let given ← argtypes.mapM widenslotwrapper
  pickConstArgs ops n E L given cacheArgtypes

/-- `given_argtypes[a:b]`: empty when `a > b`, otherwise every index must be in bounds. -/
def sliceIdx (xs : List LElt) (a b : Int) : CM (List LElt) := do
  if a > b then return []
  if a < 1 || b > xs.length then jlThrow "BoundsError" "given_argtypes"
  return (xs.drop (a - 1).toNat).take (b - a + 1).toNat

/-- `va_process_argtypes(𝕃, given_argtypes, nargs, isva, mi)`

Julia source: Compiler/src/inferenceresult.jl:111-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function va_process_argtypes(𝕃::AbstractLattice, given_argtypes::Vector{Any}, nargs::UInt, isva::Bool, mi::MethodInstance)
    nargs = Int(nargs)
    if isva || (!isempty(given_argtypes) && isvarargtype(given_argtypes[end]))
        isva_given_argtypes = Vector{Any}(undef, nargs)
        for i = 1:(nargs-isva)
            newarg = argtype_by_index(given_argtypes, i)
            if isva && has_conditional(𝕃) && isa(newarg, Conditional)
                if newarg.slot > (nargs-isva)
                    newarg = widenconditional(newarg)
                end
            end
            if isva && has_mustalias(𝕃) && isa(newarg, MustAlias)
                if newarg.slot > (nargs-isva)
                    newarg = widenmustalias(newarg)
                end
            end
            isva_given_argtypes[i] = newarg
        end
        if isva
            if length(given_argtypes) < nargs && isvarargtype(given_argtypes[end])
                last = length(given_argtypes)
            else
                last = nargs
                if has_conditional(𝕃)
                    for i = last:length(given_argtypes)
                        newarg = given_argtypes[i]
                        if isa(newarg, Conditional) && newarg.slot > (nargs-isva)
                            given_argtypes[i] = widenconditional(newarg)
                        end
                    end
                end
                if has_mustalias(𝕃)
                    for i = last:length(given_argtypes)
                        newarg = given_argtypes[i]
                        if isa(newarg, MustAlias) && newarg.slot > (nargs-isva)
                            given_argtypes[i] = widenmustalias(newarg)
                        end
                    end
                end
            end
            isva_given_argtypes[nargs] = tuple_tfunc(𝕃, given_argtypes[last:end])
        end
        return isva_given_argtypes
    end
    if length(given_argtypes) != nargs
        println(given_argtypes, " != ", nargs, " for ", mi)
        throw(AssertionError("invalid `given_argtypes` for `mi`"))
    end
    return given_argtypes
end
```
-/
def vaProcessArgtypes (n : Nat) (E : CEnv) (L : Lattice) (givenArgtypes : List LElt) (nargs : Nat)
    (isva : Bool) : CM (List LElt) := do
  let nargsI : Int := nargs
  let nfixed : Int := nargsI - (if isva then 1 else 0)
  let lastIsVa := match givenArgtypes.getLast? with | some x => x.isVarargElt | none => false
  if isva || lastIsVa then
    let mut out : Array (Option LElt) := Array.replicate nargs none
    for i in [1:nfixed.toNat + 1] do
      let mut newarg ← argtypeByIndex givenArgtypes i
      if isva && hasConditional L then
        if let .conditional slot .. := newarg then
          if slot > nfixed then newarg ← widenconditional newarg
      if isva && hasMustalias L then
        if let .mustAlias slot .. := newarg then
          if slot > nfixed then newarg ← widenmustalias newarg
      out := out.set! (i - 1) (some newarg)
    if isva then
      let mut g := givenArgtypes.toArray
      let len : Int := g.size
      let mut last : Int := 0
      let mut tailIsVa := false
      if len < nargsI then
        tailIsVa := (← atIdx givenArgtypes len).isVarargElt
      if tailIsVa then
        last := len
      else
        last := nargsI
        if hasConditional L then
          for k in [0:(len - last + 1).toNat] do
            let i := last + k
            let newarg ← atIdx g.toList i
            if let .conditional slot .. := newarg then
              if slot > nfixed then g := g.set! (i - 1).toNat (← widenconditional newarg)
        if hasMustalias L then
          for k in [0:(len - last + 1).toNat] do
            let i := last + k
            let newarg ← atIdx g.toList i
            if let .mustAlias slot .. := newarg then
              if slot > nfixed then g := g.set! (i - 1).toNat (← widenmustalias newarg)
      let tt ← tupleTfunc n E L (← sliceIdx g.toList last len)
      if nargs == 0 then jlThrow "BoundsError" "isva_given_argtypes"
      out := out.set! (nargs - 1) (some tt)
    return ← out.toList.mapM fun
      | some e => pure e
      | none => jlThrow "UndefRefError" "isva_given_argtypes"
  if givenArgtypes.length != nargs then
    jlThrow "AssertionError" "invalid `given_argtypes` for `mi`"
  return givenArgtypes

/-! ## The local cache lookup -/

/-- A `WorldRange` (`first`, `last`). -/
abbrev Worlds := Nat × Nat

def Worlds.contains (w : Worlds) (x : Nat) : Bool := w.1 ≤ x && x ≤ w.2

/-- The fields of one `InferenceCache` entry that `constprop_cache_lookup` reads: the
`MethodInstance` it is indexed under, whether it is a `LocalInferenceResult` (then `proofWorlds`
is `proof_worlds(cached.proof)`), and the wrapped `InferenceResult`'s `cache_world`,
`valid_worlds`, `argtypes`, `overridden_by_const` (`none` for `nothing`) and `tombstone`. -/
structure ConstpropEntry where
  mi : ObjId
  isLocal : Bool
  proofWorlds : Worlds
  cacheWorld : Nat
  validWorlds : Worlds
  argtypes : List LElt
  overriddenByConst : Option (List Bool)
  tombstone : Bool
  deriving Inhabited

/-- What `constprop_cache_lookup` returns: the 1-based position in `cache.results` of the entry,
`nothing`, or `missing` (a tombstone matched). -/
inductive ConstpropLookup where
  | found (idx : Nat)
  | nothing_
  | missing_
  deriving Repr, BEq, Inhabited

/-- The inner loop `for i in 1:nargtypes` of `constprop_cache_lookup` on one entry, over the
query's argument types, the entry's `argtypes` and its `overridden_by_const` flags: `true` when every
position passes `is_argtype_match`, `false` at the first that fails (`@goto next_cache`). A flag
vector shorter than the query throws the `BoundsError` of `cache_overridden_by_const[i]`. (The
entry's `argtypes` have the query's length here; the loop runs only after that check.) -/
def argtypesMatch (n : Nat) (E : CEnv) (L : Lattice) : List LElt → List LElt → List Bool → CM Bool
  | [], _, _ => pure true
  | g :: gs, c :: cs, o :: os => do
    if !(← isArgtypeMatch n E L g c o) then return false
    argtypesMatch n E L gs cs os
  | _ :: _, _, _ => jlThrow "BoundsError" "overridden_by_const"

/-- The outer loop `for idx in indices` of `constprop_cache_lookup`, from the entry after position
`idx` of `cache.results`, with `found_tombstone` so far. Each `continue` and `@goto next_cache` goes
on to the next entry. -/
def constpropLookupLoop (n : Nat) (E : CEnv) (L : Lattice) (mi : ObjId) (miVa : Bool)
    (givenArgtypes : List LElt) (world : Nat) :
    Nat → Bool → List ConstpropEntry → CM ConstpropLookup
  | _, foundTombstone, [] => pure (if foundTombstone then .missing_ else .nothing_)
  | idx, foundTombstone, c :: rest => do
    if c.mi != mi || c.cacheWorld != world then
      return ← constpropLookupLoop n E L mi miVa givenArgtypes world (idx + 1) foundTombstone rest
    let validWorlds := if c.isLocal then c.proofWorlds else c.validWorlds
    if !validWorlds.contains world then
      return ← constpropLookupLoop n E L mi miVa givenArgtypes world (idx + 1) foundTombstone rest
    if c.argtypes.length != givenArgtypes.length then
      if !miVa then jlThrow "AssertionError" "invalid `cache_argtypes` for `mi`"
      return ← constpropLookupLoop n E L mi miVa givenArgtypes world (idx + 1) foundTombstone rest
    let some ov := c.overriddenByConst
      | constpropLookupLoop n E L mi miVa givenArgtypes world (idx + 1) foundTombstone rest
    if !(← argtypesMatch n E L givenArgtypes c.argtypes ov) then
      return ← constpropLookupLoop n E L mi miVa givenArgtypes world (idx + 1) foundTombstone rest
    if c.tombstone then
      return ← constpropLookupLoop n E L mi miVa givenArgtypes world (idx + 1) true rest
    return .found (idx + 1)

/-- `constprop_cache_lookup(𝕃, mi, given_argtypes, cache, world)`; `miVa` says whether
`mi.specTypes`'s last parameter is a `Vararg`. `get_indices(cache, mi)` is the positions of the
entries indexed under `mi`, in insertion order (`Compiler/src/types.jl:252-279`).

Julia source: Compiler/src/inferenceresult.jl:217-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function constprop_cache_lookup(𝕃::AbstractLattice, mi::MethodInstance,
                                given_argtypes::Vector{Any}, cache::InferenceCache,
                                world::UInt)
    nargtypes = length(given_argtypes)
    indices = get_indices(cache, mi)
    found_tombstone = false
    for idx in indices
        cached = cache.results[idx]
        cached_result = cached isa LocalInferenceResult ? cached.result : cached
        cached_result.cache_world == world || continue
        valid_worlds = cached isa LocalInferenceResult ?
            proof_worlds(cached.proof) : cached_result.valid_worlds
        world in valid_worlds || continue
        cache_argtypes = cached_result.argtypes
        if length(cache_argtypes) != nargtypes
            # A `MethodInstance` whose `specTypes` ends in an unbounded `Vararg` (i.e. its
            # trailing varargs are not specialized to a fixed arity) can be
            # const-propagated at multiple arities, producing cached results whose
            # `argtypes` differ in length (e.g. one ending in a `Vararg` element, another
            # expanded to concrete arguments). Such entries describe distinct argument
            # refinements, and a query of a different arity cannot reuse them, so skip.
            # Any other length mismatch would indicate a genuine bug.
            @assert isvarargtype((unwrap_unionall(mi.specTypes)::DataType).parameters[end]) "invalid `cache_argtypes` for `mi`"
            @goto next_cache
        end
        cache_overridden_by_const = cached_result.overridden_by_const
        cache_overridden_by_const === nothing && continue
        cache_overridden_by_const = cache_overridden_by_const::BitVector
        for i in 1:nargtypes
            if !is_argtype_match(𝕃, given_argtypes[i], cache_argtypes[i], cache_overridden_by_const[i])
                @goto next_cache
            end
        end
        # Don't return tombstoned entries as cache items: they represent rejected work
        # (due to LimitedAccuracy). Instead, record that a tombstone was found so the
        # caller can avoid re-attempting the same const-prop that would hit the same limit.
        if cached_result.tombstone
            found_tombstone = true
            @goto next_cache
        end
        return cached
        @label next_cache
    end
    return found_tombstone ? missing : nothing
end
```
-/
def constpropCacheLookup (n : Nat) (E : CEnv) (L : Lattice) (mi : ObjId) (miVa : Bool)
    (givenArgtypes : List LElt) (cache : List ConstpropEntry) (world : Nat) : CM ConstpropLookup :=
  constpropLookupLoop n E L mi miVa givenArgtypes world 0 false cache

/-- The `overridden_by_const` flags `const_prop_call` stores with a fresh const-prop result: position
`i` is overridden when the key's argument type is not `===` to the matching cache argument type.
The key is `argtypes`, the result of `matching_cache_argtypes` and `get_nospecializeinfer_argtypes`.
Defined in `Compiler/src/abstractinterpretation.jl:1517-1522`
(f755f49a9e41380d7da126b3c1db9fe7f83dd027):
```julia
    overridden_by_const = falses(length(argtypes))
    for i = 1:length(argtypes)
        if argtypes[i] !== argtype_by_index(cache_argtypes, i)
            overridden_by_const[i] = true
        end
    end
```
-/
def overriddenByConstFlags (n : Nat) (E : CEnv) (argtypes cacheArgtypes : List LElt) :
    CM (List Bool) := do
  let mut ov : List Bool := []
  for i in [1:argtypes.length + 1] do
    let a ← atIdx argtypes i
    let c ← argtypeByIndex cacheArgtypes i
    ov := ov ++ [!(← eltEgal n E a c)]
  return ov

end JuliaLean.Compiler
