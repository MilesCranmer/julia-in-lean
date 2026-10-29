import JuliaLean.Core

/-!
# Source-mirrored model of `base/abstractdict.jl`

Julia dispatch is represented by typed operation interfaces. `DictOps` supplies the concrete
AbstractDict operations called by these generic methods.
-/

namespace JuliaLean.base.abstractdict

inductive DictError where
  | keyError
  | methodError (name : String)
  | argumentError (message : String)
  | errorException (message : String)
  | dictionaryError (message : String)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except DictError α

structure DictType (T : Type) where
  name : String
  K : T
  V : T

structure DictOps (T D K V : Type) where
  pairs : D → List (K × V)
  get : D → K → Option V
  setindex : D → V → K → Result D
  delete : D → K → Result D
  emptyT : D → T → T → Result D
  emptyBang : D → Result D
  length : D → Nat
  sizehint : D → Nat → D
  hasLength : D → Bool
  typeOf : D → DictType T

structure Other (T K V : Type) where
  pairs : List (K × V)
  typeOf : DictType T
  hasLength : Bool

namespace DictOps

def other (ops : DictOps T D K V) (d : D) : Other T K V :=
  ⟨ops.pairs d, ops.typeOf d, ops.hasLength d⟩

end DictOps

inductive Part where
  | keys
  | vals
  deriving DecidableEq

def Part.Elem (K V : Type) : Part → Type
  | .keys => K
  | .vals => V

structure KeySet (K D : Type) where
  dict : D

structure ValueIterator (D : Type) where
  dict : D

structure PairType (T : Type) where
  key : Option T
  value : Option T

def pairEltype (K V : Option T) : PairType T := ⟨K, V⟩


/-! ## Membership -/

/--
Julia source: base/abstractdict.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(a::AbstractDict) = KeySet(a)
```
-/
def keysAD {K D : Type} (a : D) : KeySet K D := ⟨a⟩
/--
Julia source: base/abstractdict.jl:73-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(k, v::KeySet) = get(v.dict, k, secret_table_token) !== secret_table_token
```
-/
def inKeySet {T D K V : Type} (ops : DictOps T D K V) (v : KeySet K D) (k : K) : Bool :=
  (ops.get v.dict k).isSome

/--
Julia source: base/abstractdict.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(d::AbstractDict, k) = in(k, keys(d))
```
-/
def haskeyAD {T D K V : Type} (ops : DictOps T D K V) (d : D) (k : K) : Bool :=
  inKeySet ops (keysAD d) k
inductive Truth where
  | yes
  | no
  | missing
  deriving Repr, DecidableEq


/--
Julia source: base/abstractdict.jl:21-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function in(p::Pair, a::AbstractDict, valcmp=(==))
    v = get(a, p.first, secret_table_token)
    if v !== secret_table_token
        return valcmp(v, p.second)
    end
    return false
end
```
-/
def inPairAD {T D K V W : Type} (ops : DictOps T D K V)
    (valcmp : V → W → Truth) (a : D) (p : K × W) : Truth :=
  match ops.get a p.1 with
  | some v => valcmp v p.2
  | none => .no

/--
Julia source: base/abstractdict.jl:29-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function in(p, a::AbstractDict)
    error("""AbstractDict collections only contain Pairs;
             Either look for e.g. A=>B instead, or use the `keys` or `values`
             function if you are looking for a key or value respectively.""")
end
```
-/
def inNotPairAD {T D K V : Type} (_ops : DictOps T D K V) (_a : D) : Result Bool :=
  .error (.errorException "AbstractDict collections only contain Pairs;\n             Either look for e.g. A=>B instead, or use the `keys` or `values`\n             function if you are looking for a key or value respectively.")

/-! ## Dictionary summaries and key/value iterators -/

/--
Julia source: base/abstractdict.jl:35-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function summary(io::IO, t::AbstractDict)
    showarg(io, t, true)
    if Base.IteratorSize(t) isa HasLength
        n = length(t)
        print(io, " with ", n, (n==1 ? " entry" : " entries"))
    else
        print(io, "(...)")
    end
end
```
-/
def summaryAD {T D K V : Type} (ops : DictOps T D K V)
    (showarg : D → String) (d : D) : String :=
  showarg d ++ if ops.hasLength d then
    let n := ops.length d
    " with " ++ toString n ++ if n == 1 then " entry" else " entries"
  else "(...)"

/--
Julia source: base/abstractdict.jl:53-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function summary(io::IO, iter::T) where {T<:Union{KeySet,ValueIterator}}
    print(io, nameof(T), " for a ")
    summary(io, iter.dict)
end
```
-/
def summaryIter {T D K V : Type} (ops : DictOps T D K V)
    (showarg : D → String) (name : String) (d : D) : String :=
  name ++ " for a " ++ summaryAD ops showarg d

def Part.project {K V : Type} : (part : Part) → K × V → part.Elem K V
  | .keys, kv => kv.1
  | .vals, kv => kv.2
/--
Julia source: base/abstractdict.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, iter::Union{KeySet,ValueIterator}) = show_vector(io, iter)
```
-/
def showIter {T D K V : Type} (ops : DictOps T D K V)
    (showVector : {α : Type} → List α → String) (part : Part) (d : D) : String :=
  showVector ((ops.pairs d).map (Part.project part))

/--
Julia source: base/abstractdict.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(v::Union{KeySet,ValueIterator}) = length(v.dict)
```
-/
def lengthIter {T D K V : Type} (ops : DictOps T D K V) (_part : Part) (d : D) : Nat :=
  ops.length d

/--
Julia source: base/abstractdict.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(v::Union{KeySet,ValueIterator}) = isempty(v.dict)
```
-/
def isemptyIter {D : Type} (isempty : D → Bool) (_part : Part) (d : D) : Bool := isempty d

/--
Julia source: base/abstractdict.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_tt2(::Type{Pair{A,B}}) where {A,B} = B
```
-/
def tt2 (p : PairType T) : Result T :=
  match p.key, p.value with
  | some _, some v => .ok v
  | _, _ => .error (.methodError "_tt2")

/--
Julia source: base/abstractdict.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{ValueIterator{D}}) where {D} = _tt2(eltype(D))
```
-/
def eltypeValueIterator (p : PairType T) : Result T := tt2 p

/-- The source method's `nothing` or projected pair and unchanged iterator state. -/
def iterPartStep {K V S : Type} (part : Part) (y : Option ((K × V) × S)) :
    Option (part.Elem K V × S) :=
  match y with
  | none => none
  | some (kv, state) => some (match part with | .keys => kv.1 | .vals => kv.2, state)

/--
Julia source: base/abstractdict.jl:65-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(v::Union{KeySet,ValueIterator}, state...)
    y = iterate(v.dict, state...)
    y === nothing && return nothing
    return (y[1][isa(v, KeySet) ? 1 : 2], y[2])
end
```
-/
def iterateAD {D K V S : Type}
    (iterate : D → Option S → Option ((K × V) × S))
    (part : Part) (d : D) (state : Option S) :
    Option (part.Elem K V × S) :=
  match iterate d state with
  | none => none
  | some (kv, nextState) => some (Part.project part kv, nextState)

def iterPartAll {T D K V : Type} (ops : DictOps T D K V) (part : Part) (d : D) :
    List (part.Elem K V) :=
  (ops.pairs d).map (Part.project part)
/-- The list of projected keys or values used by the iterator display method. -/
def iterPartDisplay {T D K V : Type} (ops : DictOps T D K V)
    (showVector : {α : Type} → List α → String) (part : Part) (d : D) : String :=
  showVector (iterPartAll ops part d)

/--
Julia source: base/abstractdict.jl:71-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(v::KeySet) = copymutable(v)
```
-/
def copyKeySet {K D S : Type} (copymutable : KeySet K D → S) (v : KeySet K D) : S :=
  copymutable v


/--
Julia source: base/abstractdict.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
values(a::AbstractDict) = ValueIterator(a)
```
-/
def valuesAD {D : Type} (a : D) : ValueIterator D := ⟨a⟩

/--
Julia source: base/abstractdict.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(collection) = Generator(=>, keys(collection), values(collection))
```
-/
def pairsGeneric {C KI VI G : Type} (keys : C → KI) (values : C → VI)
    (generator : KI → VI → G) (collection : C) : G :=
  generator (keys collection) (values collection)

/--
Julia source: base/abstractdict.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(a::AbstractDict) = a
```
-/
def pairsAD {D : Type} (a : D) : D := a
/-! ## Type queries, empty, copy and merge! -/

/--
Julia source: base/abstractdict.jl:310-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(::Type{<:AbstractDict{K}}) where {K} = K
```
-/
def keytypeType (t : DictType T) : T := t.K

/--
Julia source: base/abstractdict.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keytype(a::AbstractDict) = keytype(typeof(a))
```
-/
def keytypeAD {T D K V : Type} (ops : DictOps T D K V) (d : D) : T :=
  keytypeType (ops.typeOf d)

/--
Julia source: base/abstractdict.jl:324-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(::Type{<:AbstractDict{<:Any,V}}) where {V} = V
```
-/
def valtypeType (t : DictType T) : T := t.V

/--
Julia source: base/abstractdict.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
valtype(a::AbstractDict) = valtype(typeof(a))
```
-/
def valtypeAD {T D K V : Type} (ops : DictOps T D K V) (d : D) : T :=
  valtypeType (ops.typeOf d)

/--
Julia source: base/abstractdict.jl:194-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(a::AbstractDict) = empty(a, keytype(a), valtype(a))
```
-/
def emptyAD {T D K V : Type} (ops : DictOps T D K V) (d : D) : Result D :=
  ops.emptyT d (keytypeAD ops d) (valtypeAD ops d)

/--
Julia source: base/abstractdict.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(a::AbstractDict, ::Type{V}) where {V} = empty(a, keytype(a), V) # Note: this is the form which makes sense for `Vector`.
```
-/
def emptyADV {T D K V : Type} (ops : DictOps T D K V) (d : D) (valueType : T) :
    Result D :=
  ops.emptyT d (keytypeAD ops d) valueType

/--
Julia source: base/abstractdict.jl:536-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizehint!(d::AbstractDict, n) = d
```
-/
def sizehintAD {D : Type} (d : D) (_n : Nat) : D := d

/-- Merge one source dictionary, optionally reserving its reported length first. -/
def mergeStep {T D K V : Type} (ops : DictOps T D K V) (d : D) (other : Other T K V) :
    Result D := do
  let d := if ops.hasLength d && other.hasLength then
    ops.sizehint d (ops.length d + other.pairs.length)
    else d
  other.pairs.foldlM (fun d kv => ops.setindex d kv.2 kv.1) d

/--
Julia source: base/abstractdict.jl:224-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function merge!(d::AbstractDict, others::AbstractDict...)
    for other in others
        if haslength(d) && haslength(other)
            sizehint!(d, length(d) + length(other); shrink = false)
        end
        for (k,v) in other
            d[k] = v
        end
    end
    return d
end
```
-/
def mergeBang {T D K V : Type} (ops : DictOps T D K V) (d : D)
    (others : List (Other T K V)) : Result D :=
  others.foldlM (mergeStep ops) d

/--
Julia source: base/abstractdict.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(a::AbstractDict) = merge!(empty(a), a)
```
-/
def copyAD {T D K V : Type} (ops : DictOps T D K V) (a : D) : Result D := do
  let empty ← emptyAD ops a
  mergeBang ops empty [ops.other a]

/--
Julia source: base/abstractdict.jl:198-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy!(dst::AbstractDict, src::AbstractDict)
    dst === src && return dst
    merge!(empty!(dst), src)
end
```
-/
def copyBangAD {T D K V : Type} (ops : DictOps T D K V) (same : Bool)
    (dst src : D) : Result D := do
  if same then pure dst
  else do
    let d ← ops.emptyBang dst
    mergeBang ops d [ops.other src]
/--
Julia source: base/abstractdict.jl:547-553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(t::AbstractDict{<:Any,V}, key) where V
    v = get(t, key, secret_table_token)
    if v === secret_table_token
        throw(KeyError(key))
    end
    return v::V
end
```
-/
def getindexAD {T D K V : Type} (ops : DictOps T D K V) (d : D) (key : K) : Result V :=
  match ops.get d key with
  | none => .error .keyError
  | some v => .ok v

/--
Julia source: base/abstractdict.jl:288-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mergewith!(combine, d1::AbstractDict, d2::AbstractDict)
    for (k, v) in d2
        d1[k] = haskey(d1, k) ? combine(d1[k], v) : v
    end
    return d1
end
```
-/
def mergewithBang2 {T D K V : Type} (ops : DictOps T D K V)
    (combine : V → V → V) (d1 : D) (d2 : Other T K V) : Result D :=
  d2.pairs.foldlM (fun d1 kv => do
    let value ← if haskeyAD ops d1 kv.1 then do
      let old ← getindexAD ops d1 kv.1
      pure (combine old kv.2)
      else pure kv.2
    ops.setindex d1 value kv.1) d1


/--
Julia source: base/abstractdict.jl:283-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mergewith!(combine, d::AbstractDict, others::AbstractDict...)
    foldl(mergewith!(combine), others; init = d)
end
```
-/
def mergewithBang {T D K V : Type} (ops : DictOps T D K V)
    (combine : V → V → V) (d : D) (others : List (Other T K V)) : Result D :=
  others.foldlM (fun d other => mergewithBang2 ops combine d other) d

/--
Julia source: base/abstractdict.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mergewith!(combine) = (args...) -> mergewith!(combine, args...)
```
-/
def mergewithCurried {T D K V : Type} (ops : DictOps T D K V)
    (combine : V → V → V) : D → List (Other T K V) → Result D :=
  fun d others => mergewithBang ops combine d others

/--
Julia source: base/abstractdict.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge!(combine::Callable, args...) = mergewith!(combine, args...)
```
-/
def mergeBangCombine {T D K V : Type} (ops : DictOps T D K V)
    (combine : V → V → V) (d : D) (others : List (Other T K V)) : Result D :=
  mergewithBang ops combine d others


/--
Julia source: base/abstractdict.jl:409-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promoteK(K) = K
```
-/
def promoteKBase (K : T) : T := K

/--
Julia source: base/abstractdict.jl:410-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promoteV(V) = V
```
-/
def promoteVBase (V : T) : T := V

/--
Julia source: base/abstractdict.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promoteK(K, d, ds...) = promoteK(promote_type(K, keytype(d)), ds...)
```
-/
def promoteKStep (promote : T → T → T) (K : T) (d : DictType T)
    (ds : List (DictType T)) : T :=
  match ds with
  | [] => promoteKBase (promote K (keytypeType d))
  | next :: rest => promoteKStep promote (promote K (keytypeType d)) next rest

/--
Julia source: base/abstractdict.jl:412-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promoteV(V, d, ds...) = promoteV(promote_type(V, valtype(d)), ds...)
```
-/
def promoteVStep (promote : T → T → T) (V : T) (d : DictType T)
    (ds : List (DictType T)) : T :=
  match ds with
  | [] => promoteVBase (promote V (valtypeType d))
  | next :: rest => promoteVStep promote (promote V (valtypeType d)) next rest
def promoteKAll (promote : T → T → T) (K : T) : List (DictType T) → T
  | [] => promoteKBase K
  | d :: ds => promoteKStep promote K d ds
def promoteVAll (promote : T → T → T) (V : T) : List (DictType T) → T
  | [] => promoteVBase V
  | d :: ds => promoteVStep promote V d ds

/--
Julia source: base/abstractdict.jl:413-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _typeddict(d::AbstractDict, others::AbstractDict...)
    K = promoteK(keytype(d), others...)
    V = promoteV(valtype(d), others...)
    Dict{K,V}(d)
end
```
-/
def typedDictModel {T D E K V : Type} (ops : DictOps T D K V)
    (promote : T → T → T) (dictOf : T → T → D → Result E) (d : D)
    (others : List (DictType T)) : Result E := do
  let K := promoteKAll promote (keytypeAD ops d) others
  let V := promoteVAll promote (valtypeAD ops d) others
  dictOf K V d

/--
Julia source: base/abstractdict.jl:361-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(d::AbstractDict, others::AbstractDict...) =
    merge!(_typeddict(d, others...), others...)
```
-/
def mergeAD {T D E K V : Type} (ops : DictOps T D K V)
    (dops : DictOps T E K V) (promote : T → T → T)
    (dictOf : T → T → D → Result E) (d : D)
    (others : List (DictType T × Other T K V)) : Result E := do
  let typed ← typedDictModel ops promote dictOf d (others.map Prod.fst)
  mergeBang dops typed (others.map Prod.snd)

/--
Julia source: base/abstractdict.jl:404-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mergewith(combine, d::AbstractDict, others::AbstractDict...) =
    mergewith!(combine, _typeddict(d, others...), others...)
```
-/
def mergewithAD {T D E K V : Type} (ops : DictOps T D K V)
    (dops : DictOps T E K V) (promote : T → T → T)
    (dictOf : T → T → D → Result E) (combine : V → V → V) (d : D)
    (others : List (DictType T × Other T K V)) : Result E := do
  let typed ← typedDictModel ops promote dictOf d (others.map Prod.fst)
  mergewithBang dops combine typed (others.map Prod.snd)

/--
Julia source: base/abstractdict.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mergewith(combine) = (args...) -> mergewith(combine, args...)
```
-/
def mergewithCurriedAD {T D E K V : Type} (ops : DictOps T D K V)
    (dops : DictOps T E K V) (promote : T → T → T)
    (dictOf : T → T → D → Result E) (combine : V → V → V) :
    D → List (DictType T × Other T K V) → Result E :=
  fun d others => mergewithAD ops dops promote dictOf combine d others

/--
Julia source: base/abstractdict.jl:439-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter!(f, d::AbstractDict)
    badkeys = Vector{keytype(d)}()
    for pair in d
        # don't delete!(d, k) here, since dictionary types
        # may not support mutation during iteration
        f(pair) || push!(badkeys, pair.first)
    end
    for k in badkeys
        delete!(d, k)
    end
    return d
end
```
-/
def filterBangAD {T D K V : Type} (ops : DictOps T D K V)
    (f : K × V → Bool) (d : D) : Result D :=
  let badkeys := (ops.pairs d).foldl
    (fun keys pair => if f pair then keys else keys ++ [pair.1]) []
  badkeys.foldlM (fun d k => ops.delete d k) d

/--
Julia source: base/abstractdict.jl:452-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter_in_one_pass!(f, d::AbstractDict)
    for pair in d
        if !f(pair)
            delete!(d, pair.first)
        end
    end
    return d
end
```
-/
def filterInOnePassAD {T D K V : Type} (ops : DictOps T D K V)
    (f : K × V → Bool) (d : D) : Result D :=
  (ops.pairs d).foldlM
    (fun d pair => if !f pair then ops.delete d pair.1 else .ok d) d

/--
Julia source: base/abstractdict.jl:479-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter(f, d::AbstractDict)
    # don't just do filter!(f, copy(d)): avoid making a whole copy of d
    df = empty(d)
    for pair in d
        if f(pair)
            df[pair.first] = pair.second
        end
    end
    return df
end
```
-/
def filterAD {T D K V : Type} (ops : DictOps T D K V)
    (f : K × V → Bool) (d : D) : Result D := do
  let df ← emptyAD ops d
  (ops.pairs d).foldlM
    (fun df pair => if f pair then ops.setindex df pair.2 pair.1 else .ok df) df

/--
Julia source: base/abstractdict.jl:490-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eltype(::Type{<:AbstractDict{K,V}}) where {K,V}
    if @isdefined(K)
        if @isdefined(V)
            return Pair{K,V}
        else
            return Pair{K}
        end
    elseif @isdefined(V)
        return Pair{k,V} where k
    else
        return Pair
    end
end
```
-/
def eltypeAD (K V : Option T) : PairType T :=
  match K with
  | some k => match V with
    | some v => ⟨some k, some v⟩
    | none => ⟨some k, none⟩
  | none => match V with
    | some v => ⟨none, some v⟩
    | none => ⟨none, none⟩

/-- The three possible results of value equality in `==` on dictionaries. -/
def boolTruth (b : Bool) : Truth := if b then .yes else .no

/--
Julia source: base/abstractdict.jl:504-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isequal(l::AbstractDict, r::AbstractDict)
    l === r && return true
    if isa(l,IdDict) != isa(r,IdDict)
        return false
    end
    if length(l) != length(r) return false end
    for pair in l
        if !in(pair, r, isequal)
            return false
        end
    end
    true
end
```
-/
def isequalAD {T D E K V : Type} (lops : DictOps T D K V) (rops : DictOps T E K V)
    (same : D → E → Bool) (lIsId rIsId : Bool) (valueEq : V → V → Bool)
    (l : D) (r : E) : Bool :=
  if same l r then true
  else if lIsId != rIsId then false
  else if lops.length l != rops.length r then false
  else
    (lops.pairs l).foldl (fun ok pair =>
      ok && inPairAD rops (fun a b => boolTruth (valueEq a b)) r pair == .yes) true

/--
Julia source: base/abstractdict.jl:518-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(l::AbstractDict, r::AbstractDict)
    if isa(l,IdDict) != isa(r,IdDict)
        return false
    end
    length(l) != length(r) && return false
    anymissing = false
    for pair in l
        isin = in(pair, r)
        if ismissing(isin)
            anymissing = true
        elseif !isin
            return false
        end
    end
    return anymissing ? missing : true
end
```
-/
def equalAD {T D E K V : Type} (lops : DictOps T D K V) (rops : DictOps T E K V)
    (lIsId rIsId : Bool) (valueEq : V → V → Truth) (l : D) (r : E) : Truth :=
  if lIsId != rIsId then .no
  else if lops.length l != rops.length r then .no
  else
    let (anyMissing, anyFalse) := (lops.pairs l).foldl (fun state pair =>
      if state.2 then state else
      match inPairAD rops valueEq r pair with
      | .yes => state
      | .no => (state.1, true)
      | .missing => (true, false)) (false, false)
    if anyFalse then .no else if anyMissing then .missing else .yes

def hashaSeed : Nat := 0x6d35bb51952d5539

/--
Julia source: base/abstractdict.jl:539-545 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(a::AbstractDict, h::UInt)
    hv = hasha_seed
    for (k,v) in a
        hv ⊻= hash(k, hash(v))
    end
    hash(hv, h)
end
```
-/
def hashAD {T D K V U : Type} (ops : DictOps T D K V)
    (seedOf : Nat → U) (xor : U → U → U)
    (hashKey : K → U → U) (hashValue : V → U)
    (hashUInt : U → U → U) (a : D) (h : U) : U :=
  hashUInt
    ((ops.pairs a).foldl (fun hv kv => xor hv (hashKey kv.1 (hashValue kv.2)))
      (seedOf hashaSeed)) h
/-- The `KeyError` payload retained by the Julia exception type. -/
structure KeyErrorData (K : Type) where
  key : K

structure TypeErrorData (T A : Type) where
  functionName : String
  expected : T
  got : A

def secretTableToken : String :=
  "__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__"

/--
Julia source: base/abstractdict.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
KeyTypeError(K, key) = TypeError(:var"dict key", K, key)
```
-/
def keyTypeError {T A : Type} (K : T) (key : A) : TypeErrorData T A :=
  ⟨"dict key", K, key⟩

/--
Julia source: base/abstractdict.jl:557-557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(t::AbstractDict, k1, k2, ks...) = getindex(t, tuple(k1,k2,ks...))
```
-/
def getindexTup {T D K V A : Type} (ops : DictOps T D K V)
    (tuple : A → A → List A → K) (d : D) (k1 k2 : A) (ks : List A) : Result V :=
  getindexAD ops d (tuple k1 k2 ks)

/--
Julia source: base/abstractdict.jl:558-558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(t::AbstractDict, v, k1, k2, ks...) = setindex!(t, v, tuple(k1,k2,ks...))
```
-/
def setindexTup {T D K V A : Type} (ops : DictOps T D K V)
    (tuple : A → A → List A → K) (d : D) (v : V) (k1 k2 : A) (ks : List A) : Result D :=
  ops.setindex d v (tuple k1 k2 ks)

structure KeyConversion (Q K : Type) where
  convert : Q → Result K

structure ValueConversion (W V : Type) where
  convert : W → Result V

/--
Julia source: base/abstractdict.jl:561-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(default::Callable, t::AbstractDict{K,V}, key) where K where V
    key = convert(K, key)
    if haskey(t, key)
        return t[key]
    else
        return t[key] = convert(V, default())
    end
end
```
-/
def getBangCallable {T D K V Q W : Type} (ops : DictOps T D K V)
    (convertKey : KeyConversion Q K) (convertValue : ValueConversion W V)
    (default : Unit → Result W) (d : D) (key0 : Q) : Result (V × D) := do
  let key ← convertKey.convert key0
  if haskeyAD ops d key then do
    let value ← getindexAD ops d key
    pure (value, d)
  else do
    let raw ← default ()
    let value ← convertValue.convert raw
    let d ← ops.setindex d value key
    pure (value, d)

/--
Julia source: base/abstractdict.jl:560-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get!(t::AbstractDict, key, default) = get!(() -> default, t, key)
```
-/
def getBangValue {T D K V Q W : Type} (ops : DictOps T D K V)
    (convertKey : KeyConversion Q K) (convertValue : ValueConversion W V)
    (d : D) (key : Q) (default : W) : Result (V × D) :=
  getBangCallable ops convertKey convertValue (fun _ => .ok default) d key

/--
Julia source: base/abstractdict.jl:570-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(t::AbstractDict, p::Pair) = setindex!(t, p.second, p.first)
```
-/
def pushAD {T D K V : Type} (ops : DictOps T D K V) (d : D) (p : K × V) : Result D :=
  ops.setindex d p.2 p.1

/--
Julia source: base/abstractdict.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::T) where {T<:AbstractDict} = x
```
-/
def convertSame {D : Type} (d : D) : D := d

/--
Julia source: base/abstractdict.jl:575-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{T}, x::AbstractDict) where T<:AbstractDict
    h = T(x)::T
    if length(h) != length(x)
        error("key collision during dictionary conversion")
    end
    return h
end
```
-/
def convertAD {T D E K V : Type} (ops : DictOps T D K V)
    (resultLength : E → Nat) (construct : D → Result E) (d : D) : Result E := do
  let result ← construct d
  if resultLength result != ops.length d then
    .error (.errorException "key collision during dictionary conversion")
  else
    .ok result

/--
Julia source: base/abstractdict.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_tablesz(x::T) where T <: Integer = x < 16 ? T(16) : one(T)<<(top_set_bit(x-one(T)))
```
-/
def tableSize {I : Type} (lt : I → I → Bool) (ofNat : Nat → I) (one : I)
    (sub shl : I → I → I) (topSetBit : I → I) (x : I) : I :=
  if lt x (ofNat 16) then ofNat 16 else shl one (topSetBit (sub x one))

/--
Julia source: base/abstractdict.jl:589-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_dict_kv_error() = throw(ArgumentError("AbstractDict(kv): kv needs to be an iterator of 2-tuples or pairs"))
```
-/
def throwDictKV {A : Type} : Result A :=
  .error (.argumentError "AbstractDict(kv): kv needs to be an iterator of 2-tuples or pairs")
structure TyOps (T X : Type) where
  typeOf : X → T
  isa : X → T → Bool
  join : T → T → T
  isaDict : DictType T → T → T → Bool

def kvPair {X : Type} : Option (List X) → Result (X × X)
  | some [k, v] => .ok (k, v)
  | _ => throwDictKV

/--
Julia source: base/abstractdict.jl:611-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function grow_to!(dest::AbstractDict{K,V}, itr, st) where {K, V}
    y = iterate(itr, st)
    while y !== nothing
        kv, st = y
        applicable(iterate, kv) || _throw_dict_kv_error()
        kst = iterate(kv)
        kst === nothing && _throw_dict_kv_error()
        k, kvst = kst
        vst = iterate(kv, kvst)
        vst === nothing && _throw_dict_kv_error()
        v, kvst = vst
        iterate(kv, kvst) === nothing || _throw_dict_kv_error()
        if isa(k, K) && isa(v, V)
            dest[k] = v
        else
            new = empty(dest, promote_typejoin(K, typeof(k)), promote_typejoin(V, typeof(v)))
            merge!(new, dest)
            new[k] = v
            return grow_to!(new, itr, st)
        end
        y = iterate(itr, st)
    end
    return dest
end
```
-/
def growToLoop {T D X : Type} (ty : TyOps T X) (ops : DictOps T D X X) :
    List (Option (List X)) → D → Result D
  | [], dest => .ok dest
  | kv :: rest, dest => do
      let (k, v) ← kvPair kv
      let K := keytypeAD ops dest
      let V := valtypeAD ops dest
      if ty.isa k K && ty.isa v V then do
        let dest ← ops.setindex dest v k
        growToLoop ty ops rest dest
      else do
        let new ← ops.emptyT dest (ty.join K (ty.typeOf k)) (ty.join V (ty.typeOf v))
        let new ← mergeBang ops new [ops.other dest]
        let new ← ops.setindex new v k
        growToLoop ty ops rest new

/--
Julia source: base/abstractdict.jl:591-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function grow_to!(dest::AbstractDict, itr)
    applicable(iterate, itr) || _throw_dict_kv_error()
    y = iterate(itr)
    y === nothing && return dest
    kv, st = y
    applicable(iterate, kv) || _throw_dict_kv_error()
    k = iterate(kv)
    k === nothing && _throw_dict_kv_error()
    k, kvst = k
    v = iterate(kv, kvst)
    v === nothing && _throw_dict_kv_error()
    v, kvst = v
    iterate(kv, kvst) === nothing || _throw_dict_kv_error()
    if !(dest isa AbstractDict{typeof(k), typeof(v)})
        dest = empty(dest, typeof(k), typeof(v))
    end
    dest[k] = v
    return grow_to!(dest, itr, st)
end
```
-/
def growTo {T D X : Type} (ty : TyOps T X) (ops : DictOps T D X X)
    (dest : D) (itr : Option (List (Option (List X)))) : Result D :=
  match itr with
  | none => throwDictKV
  | some [] => .ok dest
  | some (kv :: rest) => do
      let (k, v) ← kvPair kv
      let dest ← if ty.isaDict (ops.typeOf dest) (ty.typeOf k) (ty.typeOf v) then
        .ok dest
        else ops.emptyT dest (ty.typeOf k) (ty.typeOf v)
      let dest ← ops.setindex dest v k
      growToLoop ty ops rest dest

/--
Julia source: base/abstractdict.jl:637-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dict_with_eltype(DT_apply, kv, ::TP{K,V}) where {K,V} = DT_apply(K, V)(kv)
```
-/
def dictWithEltypeTP {T D X : Type}
    (DT : T → T → Option (List (Option (List X))) → Result D)
    (kv : Option (List (Option (List X)))) (K V : T) : Result D :=
  DT K V kv

/--
Julia source: base/abstractdict.jl:638-638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dict_with_eltype(DT_apply, kv::Generator, ::TP{K,V}) where {K,V} = DT_apply(K, V)(kv)
```
-/
def dictWithEltypeGeneratorTP {T D X : Type}
    (DT : T → T → Option (List (Option (List X))) → Result D)
    (kv : Option (List (Option (List X)))) (K V : T) : Result D :=
  DT K V kv

/--
Julia source: base/abstractdict.jl:639-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dict_with_eltype(DT_apply, ::Type{Pair{K,V}}) where {K,V} = DT_apply(K, V)()
```
-/
def dictWithEltypePair {T D : Type} (DT0 : T → T → Result D) (K V : T) : Result D :=
  DT0 K V

/--
Julia source: base/abstractdict.jl:640-640 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dict_with_eltype(DT_apply, ::Type) = DT_apply(Any, Any)()
```
-/
def dictWithEltypeUnknown {T D : Type} (DT0 : T → T → Result D) (anyType : T) :
    Result D :=
  DT0 anyType anyType

def emptyByEltype {T D : Type} (DT0 : T → T → Result D) (anyType : T)
    (pairType : T → Option (T × T)) (elementType : T) : Result D :=
  match pairType elementType with
  | some (K, V) => dictWithEltypePair DT0 K V
  | none => dictWithEltypeUnknown DT0 anyType

/--
Julia source: base/abstractdict.jl:641-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dict_with_eltype(DT_apply::F, kv, t) where {F} = grow_to!(dict_with_eltype(DT_apply, @default_eltype(typeof(kv))), kv)
```
-/
def dictWithEltypeGeneric {T D X : Type} (ty : TyOps T X) (ops : DictOps T D X X)
    (DT0 : T → T → Result D) (anyType : T) (pairType : T → Option (T × T))
    (defaultType : Option (List (Option (List X))) → T)
    (kv : Option (List (Option (List X)))) : Result D := do
  let dest ← emptyByEltype DT0 anyType pairType (defaultType kv)
  growTo ty ops dest kv

/--
Julia source: base/abstractdict.jl:642-648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dict_with_eltype(DT_apply::F, kv::Generator, t) where F
    T = @default_eltype(kv)
    if T <: Union{Pair, Tuple{Any, Any}} && isconcretetype(T)
        return dict_with_eltype(DT_apply, kv, T)
    end
    return grow_to!(dict_with_eltype(DT_apply, T), kv)
end
```
-/
def dictWithEltypeGenerator {T D X : Type} (ty : TyOps T X) (ops : DictOps T D X X)
    (DT : T → T → Option (List (Option (List X))) → Result D)
    (DT0 : T → T → Result D) (anyType : T)
    (pairType : T → Option (T × T))
    (defaultType : Option (List (Option (List X))) → T)
    (kv : Option (List (Option (List X)))) : Result D :=
  match pairType (defaultType kv) with
  | some (K, V) => dictWithEltypeGeneratorTP DT kv K V
  | none => dictWithEltypeGeneric ty ops DT0 anyType pairType defaultType kv

/--
Julia source: base/abstractdict.jl:673-681 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map!(f, iter::ValueIterator)
    # This is the naive fallback which requires hash evaluations
    # Contrary to the example Dict has an implementation which does not require hash evaluations
    dict = iter.dict
    for (key, val) in pairs(dict)
        dict[key] = f(val)
    end
    return iter
end
```
-/
def mapValuesAD {T D K V : Type} (ops : DictOps T D K V)
    (f : V → V) (iter : ValueIterator D) : Result (D × ValueIterator D) := do
  let d ← (ops.pairs iter.dict).foldlM
    (fun d pair => ops.setindex d (f pair.2) pair.1) iter.dict
  pure (d, iter)

end JuliaLean.base.abstractdict
