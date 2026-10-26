import JuliaLean.DictsCov.DictModel

/-!
# The generic `AbstractDict` methods of `base/abstractdict.jl` (master `bbfa0ce4150`)

The generic methods are written against the interface of a concrete
dictionary type: its iteration, `get(d, k, secret_table_token)`,
`setindex!`, `delete!`, `empty(d, K, V)`, `empty!`, `length`, `sizehint!`,
`haslength` and its type `typeof(d)`. `DictOps T D K V` collects these for a
Lean type `D` of dictionaries with keys `K` and values `V`; `T` stands for
Julia types. Each generic method below mirrors its Julia body over a
`DictOps`.

Modelling decisions:

* `get(d, k, secret_table_token)` is `ops.get d k : Option V`, `none` when the
  token comes back. A dictionary that stores the token itself as a value is
  the subject of the `iddicts-token-*` entries and is excluded here.
* `for x in d` is the list `ops.pairs d`. The loops of `filter_in_one_pass!`
  and of `map!` mutate `d` while iterating; they are modelled for types whose
  iteration visits the pairs present when the loop started, which is what the
  comment at `base/abstractdict.jl:442-443` asks of such types
  (`dictscov-iddict-map-rehash` refutes it for `IdDict`).
* Errors are `GErr`: the generic `KeyError`, `MethodError`, `error(...)` and
  `ArgumentError` of these methods, and the errors of the concrete type.
-/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

/-- Exceptions thrown by the generic methods. -/
inductive GErr where
  /-- `KeyError(key)` -/
  | keyError
  /-- `MethodError` for the function `fn` -/
  | methodError (fn : String)
  /-- `error(msg)` -/
  | errorException (msg : String)
  /-- `ArgumentError(msg)` -/
  | argumentError (msg : String)
  /-- An exception of a concrete dictionary type or of `convert` -/
  | dict (e : DErr)
  deriving Repr, DecidableEq

abbrev GR (α : Type) := Except GErr α

/-- Lift an error of the `Dict` model. -/
def liftD {α : Type} : DR α → GR α
  | .ok a => .ok a
  | .error e => .error (.dict e)

/-- A Julia type `AbstractDict{K,V}` subtype: its name and parameters. -/
structure DictTy (T : Type) where
  name : String
  K : T
  V : T
  deriving Repr, DecidableEq

/-- The interface of a concrete `AbstractDict` type used by the generic methods. -/
structure DictOps (T D K V : Type) where
  /-- `for (k, v) in d` -/
  pairs : D → List (K × V)
  /-- `get(d, k, secret_table_token)`, `none` for the token -/
  get : D → K → Option V
  /-- `setindex!(d, v, k)` -/
  setindex : D → V → K → GR D
  /-- `delete!(d, k)` -/
  delete : D → K → GR D
  /-- `empty(d, K, V)` -/
  emptyT : D → T → T → D
  /-- `empty!(d)` -/
  emptyBang : D → GR D
  /-- `length(d)` -/
  length : D → Nat
  /-- `sizehint!(d, n; shrink = false)` -/
  sizehint : D → Nat → D
  /-- `haslength(d)` (`IteratorSize(d) isa HasLength`) -/
  hasLength : D → Bool
  /-- `typeof(d)` -/
  typeOf : D → DictTy T

variable {T D E K V X : Type}

/-- `secret_table_token`, `base/abstractdict.jl:17`. -/
def secretTableToken : String := "__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__"

/-- The fields of `TypeError(func, expected, got)`. -/
structure TypeErrorV (T α : Type) where
  func : String
  expected : T
  got : α

/-- `KeyTypeError(K, key) = TypeError(:var"dict key", K, key)`, `base/abstractdict.jl:15`. -/
def keyTypeErrorV {α : Type} (K : T) (key : α) : TypeErrorV T α := ⟨"dict key", K, key⟩

/-! ## Membership, `base/abstractdict.jl:19-33,73` -/

/-- `in(k, v::KeySet) = get(v.dict, k, secret_table_token) !== secret_table_token`. -/
def inKeySet (ops : DictOps T D K V) (d : D) (k : K) : Bool := (ops.get d k).isSome

/-- `haskey(d::AbstractDict, k) = in(k, keys(d))`. -/
def haskeyAD (ops : DictOps T D K V) (d : D) (k : K) : Bool := inKeySet ops d k

/-- `in(p::Pair, a::AbstractDict, valcmp=(==))`. -/
def inPairAD (ops : DictOps T D K V) (valcmp : V → V → Bool) (a : D) (p : K × V) : Bool :=
  match ops.get a p.1 with
  | some v => valcmp v p.2
  | none => false

/-- The message of `in(p, a::AbstractDict)`, `base/abstractdict.jl:30-32`. -/
def notPairMsg : String :=
  "AbstractDict collections only contain Pairs;\nEither look for e.g. A=>B instead, or use the `keys` or `values`\nfunction if you are looking for a key or value respectively."

/-- `in(p, a::AbstractDict)` for a `p` that is not a `Pair`. -/
def inNotPairAD (_ops : DictOps T D K V) (_a : D) : GR Bool := throw (.errorException notPairMsg)

/-! ## `summary` and `show`, `base/abstractdict.jl:35-58` -/

/-- `summary(io, t::AbstractDict)`: `showarg(io, t, true)` is `showarg`. -/
def summaryAD (ops : DictOps T D K V) (showarg : D → String) (t : D) : String :=
  showarg t ++
    (if ops.hasLength t then
      let n := ops.length t
      " with " ++ toString n ++ (if n == 1 then " entry" else " entries")
    else "(...)")

/-- `summary(io, iter::T) where {T<:Union{KeySet,ValueIterator}}`: `nameof(T)` is `name`. -/
def summaryIter (ops : DictOps T D K V) (showarg : D → String) (name : String) (d : D) : String :=
  name ++ " for a " ++ summaryAD ops showarg d

/-- Which of `keys(d)`/`values(d)` an iterator is. -/
def Part.pick : (p : Part) → K × V → p.Elem K V
  | .keys => Prod.fst
  | .vals => Prod.snd

/-- `iterate(v::Union{KeySet,ValueIterator}, state...)`, `base/abstractdict.jl:65-69`,
from the result `y` of `iterate(v.dict, state...)`. -/
def iterPartStep {S : Type} (p : Part) (y : Option ((K × V) × S)) : Option (p.Elem K V × S) :=
  match y with
  | none => none
  | some (kv, s) => some (p.pick kv, s)

/-- The elements of `keys(d)`/`values(d)` (`keys(a) = KeySet(a)`,
`values(a) = ValueIterator(a)`, `base/abstractdict.jl:107,133`), each step
through `iterPartStep`. -/
def iterPartAll (ops : DictOps T D K V) (p : Part) (d : D) : List (p.Elem K V) :=
  (ops.pairs d).filterMap fun kv =>
    (iterPartStep (S := Unit) p (some (kv, ()))).map Prod.fst

/-- `show(io, iter::Union{KeySet,ValueIterator}) = show_vector(io, iter)`. -/
def showIter (ops : DictOps T D K V) (showVector : {α : Type} → List α → String)
    (p : Part) (d : D) : String :=
  showVector (iterPartAll ops p d)

/-- `length(v::Union{KeySet,ValueIterator}) = length(v.dict)`. -/
def lengthIter (ops : DictOps T D K V) (_p : Part) (d : D) : Nat := ops.length d

/-- `isempty(v::Union{KeySet,ValueIterator}) = isempty(v.dict)`, with the
dictionary's `isempty`. -/
def isemptyIter (isempty : D → Bool) (_p : Part) (d : D) : Bool := isempty d

/-- `copy(v::KeySet) = copymutable(v)`: a `Set` of the iterated keys, built by
`push!` (`isequal` keys collapse). -/
def copyKeySet (o : KeyOps K) (ops : DictOps T D K V) (d : D) : List K :=
  (iterPartAll ops .keys d).foldl (fun s k => if s.any (o.eq k) then s else s ++ [k]) []

/-- `pairs(collection) = Generator(=>, keys(collection), values(collection))`,
`base/abstractdict.jl:178`. -/
def pairsGen {A B : Type} (ks : List A) (vs : List B) : List (A × B) := List.zip ks vs

/-- `pairs(a::AbstractDict) = a`. -/
def pairsAD (ops : DictOps T D K V) (a : D) : List (K × V) := ops.pairs a

/-! ## Types, `base/abstractdict.jl:62-63,310-325,490-502` -/

/-- A `Pair` type with possibly unbound parameters. -/
inductive PairTy (T : Type) where
  | kv (k v : T)
  /-- `Pair{K}` -/
  | k (k : T)
  /-- `Pair{k,V} where k` -/
  | v (v : T)
  /-- `Pair` -/
  | any
  deriving Repr, DecidableEq

/-- `eltype(::Type{<:AbstractDict{K,V}})`: `none` is a parameter that is not
defined (`@isdefined`). -/
def eltypeAD (K V : Option T) : PairTy T :=
  match K, V with
  | some k, some v => .kv k v
  | some k, none => .k k
  | none, some v => .v v
  | none, none => .any

/-- `_tt2(::Type{Pair{A,B}}) = B`; other arguments have no method. -/
def tt2 : PairTy T → GR T
  | .kv _ b => pure b
  | _ => throw (.methodError "_tt2")

/-- `eltype(::Type{ValueIterator{D}}) = _tt2(eltype(D))`. -/
def eltypeValueIter (K V : Option T) : GR T := tt2 (eltypeAD K V)

/-- `keytype(::Type{<:AbstractDict{K}}) = K`. -/
def keytypeTy (t : DictTy T) : T := t.K

/-- `keytype(a::AbstractDict) = keytype(typeof(a))`. -/
def keytypeAD (ops : DictOps T D K V) (a : D) : T := keytypeTy (ops.typeOf a)

/-- `valtype(::Type{<:AbstractDict{<:Any,V}}) = V`. -/
def valtypeTy (t : DictTy T) : T := t.V

/-- `valtype(a::AbstractDict) = valtype(typeof(a))`. -/
def valtypeAD (ops : DictOps T D K V) (a : D) : T := valtypeTy (ops.typeOf a)

/-! ## `empty`, `copy`, `merge!`, `mergewith!`, `base/abstractdict.jl:194-297` -/

/-- `empty(a::AbstractDict) = empty(a, keytype(a), valtype(a))`. -/
def emptyAD (ops : DictOps T D K V) (a : D) : D := ops.emptyT a (keytypeAD ops a) (valtypeAD ops a)

/-- `empty(a::AbstractDict, ::Type{V}) = empty(a, keytype(a), V)`. -/
def emptyADV (ops : DictOps T D K V) (a : D) (V' : T) : D := ops.emptyT a (keytypeAD ops a) V'

/-- Another `AbstractDict` argument: its pairs and `haslength`. -/
structure Other (K V : Type) where
  pairs : List (K × V)
  hasLength : Bool

/-- A dictionary as an argument of `merge!`. -/
def DictOps.other (ops : DictOps T D K V) (d : D) : Other K V := ⟨ops.pairs d, ops.hasLength d⟩

/-- One `other` of `merge!`: `sizehint!` when both have a length, then `d[k] = v`
for each pair. -/
def mergeStep (ops : DictOps T D K V) (d : D) (other : Other K V) : GR D :=
  let d := if ops.hasLength d && other.hasLength then
    ops.sizehint d (ops.length d + other.pairs.length) else d
  other.pairs.foldlM (fun d kv => ops.setindex d kv.2 kv.1) d

/-- `merge!(d::AbstractDict, others::AbstractDict...)`, `base/abstractdict.jl:224-234`
(`length(other)` is the number of its pairs). -/
def mergeBang (ops : DictOps T D K V) (d : D) (others : List (Other K V)) : GR D :=
  others.foldlM (mergeStep ops) d

/-- `copy(a::AbstractDict) = merge!(empty(a), a)`. -/
def copyAD (ops : DictOps T D K V) (a : D) : GR D := mergeBang ops (emptyAD ops a) [ops.other a]

/-- `copy!(dst, src)`, `base/abstractdict.jl:198-201`; `same` is `dst === src`. -/
def copyBangAD (ops : DictOps T D K V) (same : Bool) (dst src : D) : GR D :=
  if same then pure dst else do
    let d ← ops.emptyBang dst
    mergeBang ops d [ops.other src]

/-- `getindex(t::AbstractDict{<:Any,V}, key)`, `base/abstractdict.jl:547-553`. -/
def getindexAD (ops : DictOps T D K V) (t : D) (key : K) : GR V :=
  match ops.get t key with
  | none => throw .keyError
  | some v => pure v

/-- The loop body of `mergewith!(combine, d1, d2)`:
`d1[k] = haskey(d1, k) ? combine(d1[k], v) : v`. -/
def mergewithStep (ops : DictOps T D K V) (combine : V → V → V) (d1 : D) (kv : K × V) : GR D := do
  let nv ← if haskeyAD ops d1 kv.1 then do
      let w ← getindexAD ops d1 kv.1
      pure (combine w kv.2)
    else pure kv.2
  ops.setindex d1 nv kv.1

/-- `mergewith!(combine, d1::AbstractDict, d2::AbstractDict)`, `base/abstractdict.jl:288-293`. -/
def mergewithBang2 (ops : DictOps T D K V) (combine : V → V → V) (d1 : D) (d2 : Other K V) : GR D :=
  d2.pairs.foldlM (mergewithStep ops combine) d1

/-- `mergewith!(combine, d::AbstractDict, others::AbstractDict...) =
foldl(mergewith!(combine), others; init = d)`, `base/abstractdict.jl:283-285`. -/
def mergewithBang (ops : DictOps T D K V) (combine : V → V → V) (d : D) (others : List (Other K V)) :
    GR D :=
  others.foldlM (mergewithBang2 ops combine) d

/-- `mergewith!(combine) = (args...) -> mergewith!(combine, args...)`. -/
def mergewithCurried (ops : DictOps T D K V) (combine : V → V → V) :
    D → List (Other K V) → GR D :=
  fun d others => mergewithBang ops combine d others

/-- `merge!(combine::Callable, args...) = mergewith!(combine, args...)`. -/
def mergeBangCombine (ops : DictOps T D K V) (combine : V → V → V) (d : D) (others : List (Other K V)) :
    GR D :=
  mergewithBang ops combine d others

/-! ## `merge`/`mergewith`, `base/abstractdict.jl:361-417` -/

/-- `promoteK(K) = K`, `promoteK(K, d, ds...) = promoteK(promote_type(K, keytype(d)), ds...)`. -/
def promoteK (promote : T → T → T) (K : T) : List (DictTy T) → T
  | [] => K
  | d :: ds => promoteK promote (promote K (keytypeTy d)) ds

/-- `promoteV`, as `promoteK` with `valtype`. -/
def promoteV (promote : T → T → T) (V : T) : List (DictTy T) → T
  | [] => V
  | d :: ds => promoteV promote (promote V (valtypeTy d)) ds

/-- `_typeddict(d, others...)`: `Dict{K,V}(d)` with the promoted parameters;
`dictOf K V ps` is `Dict{K,V}` of the pairs `ps`. -/
def typeddict (ops : DictOps T D K V) (promote : T → T → T) (dictOf : T → T → List (K × V) → GR E)
    (d : D) (others : List (DictTy T)) : GR E :=
  let K := promoteK promote (keytypeAD ops d) others
  let V := promoteV promote (valtypeAD ops d) others
  dictOf K V (ops.pairs d)

/-- `merge(d::AbstractDict, others::AbstractDict...) = merge!(_typeddict(d, others...), others...)`;
`dops` is the interface of `Dict`. -/
def mergeAD (ops : DictOps T D K V) (dops : DictOps T E K V) (promote : T → T → T)
    (dictOf : T → T → List (K × V) → GR E) (d : D) (others : List (DictTy T × Other K V)) : GR E := do
  let t ← typeddict ops promote dictOf d (others.map Prod.fst)
  mergeBang dops t (others.map Prod.snd)

/-- `mergewith(combine, d, others...) = mergewith!(combine, _typeddict(d, others...), others...)`. -/
def mergewithAD (ops : DictOps T D K V) (dops : DictOps T E K V) (promote : T → T → T)
    (dictOf : T → T → List (K × V) → GR E) (combine : V → V → V) (d : D)
    (others : List (DictTy T × Other K V)) : GR E := do
  let t ← typeddict ops promote dictOf d (others.map Prod.fst)
  mergewithBang dops combine t (others.map Prod.snd)

/-- `mergewith(combine) = (args...) -> mergewith(combine, args...)`. -/
def mergewithCurriedAD (ops : DictOps T D K V) (dops : DictOps T E K V) (promote : T → T → T)
    (dictOf : T → T → List (K × V) → GR E) (combine : V → V → V) :
    D → List (DictTy T × Other K V) → GR E :=
  fun d others => mergewithAD ops dops promote dictOf combine d others

/-! ## `filter!`/`filter`, `base/abstractdict.jl:439-488` -/

/-- `filter!(f, d::AbstractDict)`: collect the keys of the rejected pairs, then
`delete!` each. -/
def filterBangAD (ops : DictOps T D K V) (f : K × V → Bool) (d : D) : GR D :=
  let badkeys := (ops.pairs d).foldl (fun bk pair => if f pair then bk else bk ++ [pair.1]) []
  badkeys.foldlM (fun d k => ops.delete d k) d

/-- `filter_in_one_pass!(f, d)`: `delete!` each rejected pair while iterating
the pairs present when the loop started. -/
def filterInOnePass (ops : DictOps T D K V) (f : K × V → Bool) (d : D) : GR D :=
  (ops.pairs d).foldlM (fun d' pair => if !f pair then ops.delete d' pair.1 else pure d') d

/-- `filter(f, d::AbstractDict)`: `df = empty(d)`, then `df[k] = v` for each kept pair. -/
def filterAD (ops : DictOps T D K V) (f : K × V → Bool) (d : D) : GR D :=
  (ops.pairs d).foldlM (fun df pair => if f pair then ops.setindex df pair.2 pair.1 else pure df)
    (emptyAD ops d)

/-! ## Fallbacks, `base/abstractdict.jl:536-589` -/

/-- `sizehint!(d::AbstractDict, n) = d`. -/
def sizehintAD (d : D) (_n : Nat) : D := d

/-- `getindex(t::AbstractDict, k1, k2, ks...) = getindex(t, tuple(k1,k2,ks...))`;
`tuple` builds the key. -/
def getindexTup {A : Type} (ops : DictOps T D K V) (tuple : A → A → List A → K) (t : D)
    (k1 k2 : A) (ks : List A) : GR V :=
  getindexAD ops t (tuple k1 k2 ks)

/-- `setindex!(t::AbstractDict, v, k1, k2, ks...) = setindex!(t, v, tuple(k1,k2,ks...))`. -/
def setindexTup {A : Type} (ops : DictOps T D K V) (tuple : A → A → List A → K) (t : D) (v : V)
    (k1 k2 : A) (ks : List A) : GR D :=
  ops.setindex t v (tuple k1 k2 ks)

/-- `get!(default::Callable, t::AbstractDict{K,V}, key)`, `base/abstractdict.jl:561-568`:
`convert(K, key)` (`c.convert`), then the stored value or `t[key] = convert(V, default())`. -/
def getBangFAD {Q W : Type} (ops : DictOps T D K V) (c : Conv Q K) (cv : VConv W V)
    (default : Unit → GR W) (t : D) (key0 : Q) : GR (V × D) := do
  let key ← liftD (c.convert key0)
  if haskeyAD ops t key then do
    let v ← getindexAD ops t key
    pure (v, t)
  else do
    let w ← default ()
    let v ← liftD (cv.convert w)
    let t ← ops.setindex t v key
    pure (v, t)

/-- `get!(t::AbstractDict, key, default) = get!(() -> default, t, key)`. -/
def getBangAD {Q W : Type} (ops : DictOps T D K V) (c : Conv Q K) (cv : VConv W V)
    (t : D) (key0 : Q) (default : W) : GR (V × D) :=
  getBangFAD ops c cv (fun _ => pure default) t key0

/-- `push!(t::AbstractDict, p::Pair) = setindex!(t, p.second, p.first)`. -/
def pushAD (ops : DictOps T D K V) (t : D) (p : K × V) : GR D := ops.setindex t p.2 p.1

/-- `convert(::Type{T}, x::T) where {T<:AbstractDict} = x`. -/
def convertSame (x : D) : D := x

/-- `convert(::Type{T}, x::AbstractDict)`, `base/abstractdict.jl:575-581`:
`h = T(x)` is `mk x`. -/
def convertAD (ops : DictOps T D K V) (dops : DictOps T E K V) (mk : D → GR E) (x : D) : GR E := do
  let h ← mk x
  if dops.length h != ops.length x then throw (.errorException "key collision during dictionary conversion")
  pure h

/-- `_throw_dict_kv_error()`, `base/abstractdict.jl:589`. -/
def dictKVMsg : String := "AbstractDict(kv): kv needs to be an iterator of 2-tuples or pairs"

def throwDictKV {α : Type} : GR α := throw (.argumentError dictKVMsg)

/-! ## `grow_to!` and `dict_with_eltype`, `base/abstractdict.jl:591-648`

The iterator `itr` is `none` when `applicable(iterate, itr)` is false, else
the list of its elements; an element `kv` is `none` when it is not iterable,
else the list of its own elements. Keys and values are Julia values `X` with
`typeof` and `isa`. -/

/-- How Julia values meet types. -/
structure TyOps (T X : Type) where
  /-- `typeof(x)` -/
  typeOf : X → T
  /-- `x isa S` -/
  isa : X → T → Bool
  /-- `promote_typejoin(S, U)` -/
  join : T → T → T
  /-- `d isa AbstractDict{S, U}` for a dictionary of type `t` -/
  isaDict : DictTy T → T → T → Bool

/-- The checks `applicable(iterate, kv)`, two elements, and exhaustion. -/
def kvPair : Option (List X) → GR (X × X)
  | some [k, v] => pure (k, v)
  | _ => throwDictKV

/-- The loop of `grow_to!(dest::AbstractDict{K,V}, itr, st)`, `base/abstractdict.jl:611-634`,
over the remaining elements `rest`. -/
def growToLoop (ty : TyOps T X) (ops : DictOps T D X X) : List (Option (List X)) → D → GR D
  | [], dest => pure dest
  | kv :: rest, dest => do
    let (k, v) ← kvPair kv
    let K := keytypeAD ops dest
    let V := valtypeAD ops dest
    if ty.isa k K && ty.isa v V then do
      let dest ← ops.setindex dest v k
      growToLoop ty ops rest dest
    else do
      let new := ops.emptyT dest (ty.join K (ty.typeOf k)) (ty.join V (ty.typeOf v))
      let new ← mergeBang ops new [ops.other dest]
      let new ← ops.setindex new v k
      growToLoop ty ops rest new

/-- `grow_to!(dest::AbstractDict, itr)`, `base/abstractdict.jl:591-609`. -/
def growTo (ty : TyOps T X) (ops : DictOps T D X X) (dest : D) (itr : Option (List (Option (List X)))) :
    GR D :=
  match itr with
  | none => throwDictKV
  | some [] => pure dest
  | some (kv :: rest) => do
    let (k, v) ← kvPair kv
    let dest := if ty.isaDict (ops.typeOf dest) (ty.typeOf k) (ty.typeOf v) then dest
      else ops.emptyT dest (ty.typeOf k) (ty.typeOf v)
    let dest ← ops.setindex dest v k
    growToLoop ty ops rest dest

/-- The element type argument of `dict_with_eltype`. -/
inductive EltypeArg (T : Type) where
  /-- `Type{Tuple{K,V}}` or `Type{Pair{K,V}}` (`TP{K,V}`) -/
  | tp (k v : T)
  /-- any other type -/
  | other (t : T)

/-- `dict_with_eltype(DT_apply, kv, ::TP{K,V}) = DT_apply(K, V)(kv)` and the
`Generator` method of the same body, `base/abstractdict.jl:637-638`;
`DT K V itr` is `DT_apply(K, V)(itr)`. -/
def dictWithEltypeTP (DT : T → T → Option (List (Option (List X))) → GR D) (kv : Option (List (Option (List X))))
    (K V : T) : GR D :=
  DT K V kv

/-- `dict_with_eltype(DT_apply, ::Type{Pair{K,V}}) = DT_apply(K, V)()` and
`dict_with_eltype(DT_apply, ::Type) = DT_apply(Any, Any)()`, `base/abstractdict.jl:639-640`;
`DT0 K V` is `DT_apply(K, V)()`. -/
def dictWithEltypeEmpty (DT0 : T → T → D) (anyT : T) (isPair : T → Option (T × T)) (t : T) : D :=
  match isPair t with
  | some (k, v) => DT0 k v
  | none => DT0 anyT anyT

/-- `dict_with_eltype(DT_apply::F, kv, t) = grow_to!(dict_with_eltype(DT_apply,
@default_eltype(typeof(kv))), kv)`, `base/abstractdict.jl:641`; `et` is the
default element type. -/
def dictWithEltypeGrow (ty : TyOps T X) (ops : DictOps T D X X) (DT0 : T → T → D) (anyT : T)
    (isPair : T → Option (T × T)) (et : T) (kv : Option (List (Option (List X)))) : GR D :=
  growTo ty ops (dictWithEltypeEmpty DT0 anyT isPair et) kv

/-- `dict_with_eltype(DT_apply::F, kv::Generator, t)`, `base/abstractdict.jl:642-648`:
`T = @default_eltype(kv)` is `et`; `pairLike et` is
`T <: Union{Pair, Tuple{Any, Any}} && isconcretetype(T)` with its parameters. -/
def dictWithEltypeGen (ty : TyOps T X) (ops : DictOps T D X X)
    (DT : T → T → Option (List (Option (List X))) → GR D) (DT0 : T → T → D) (anyT : T)
    (isPair : T → Option (T × T)) (pairLike : T → Option (T × T)) (et : T)
    (kv : Option (List (Option (List X)))) : GR D :=
  match pairLike et with
  | some (k, v) => dictWithEltypeTP DT kv k v
  | none => growTo ty ops (dictWithEltypeEmpty DT0 anyT isPair et) kv

/-! ## `map!`, `base/abstractdict.jl:673-681` -/

/-- `map!(f, iter::ValueIterator)`: `dict[key] = f(val)` for each pair. -/
def mapValuesAD (ops : DictOps T D K V) (f : V → V) (dict : D) : GR D :=
  (pairsAD ops dict).foldlM (fun d kv => ops.setindex d (f kv.2) kv.1) dict

/-! ## Reference semantics -/

/-- `d[k] = v` on a lookup function. -/
def gset (o : KeyOps K) (g : K → Option V) (k : K) (v : V) : K → Option V :=
  fun q => if o.eq q k then some v else g q

/-- `delete!(d, k)` on a lookup function. -/
def gdel (o : KeyOps K) (g : K → Option V) (k : K) : K → Option V :=
  fun q => if o.eq q k then none else g q

/-- The lookup function of a list of distinct pairs. -/
def gOf (o : KeyOps K) (ps : List (K × V)) : K → Option V :=
  fun q => (ps.find? (fun e => o.eq q e.1)).map Prod.snd

/-- A concrete type whose methods behave like a finite map under the key
comparison `o`: lookups agree with the iterated pairs, which are distinct;
`setindex!`/`delete!`/`empty`/`empty!`/`sizehint!` update the lookups and
keep the type. -/
structure DictOps.Lawful (o : KeyOps K) (ops : DictOps T D K V) : Prop where
  get_pairs : ∀ d, ops.get d = gOf o (ops.pairs d)
  distinct : ∀ d, (ops.pairs d).Pairwise (fun a b => o.eq a.1 b.1 = false)
  length : ∀ d, ops.length d = (ops.pairs d).length
  set : ∀ d v k, ∃ d', ops.setindex d v k = .ok d' ∧ ops.get d' = gset o (ops.get d) k v ∧
    ops.typeOf d' = ops.typeOf d
  del : ∀ d k, ∃ d', ops.delete d k = .ok d' ∧ ops.get d' = gdel o (ops.get d) k
  emptyT : ∀ d K V, ops.get (ops.emptyT d K V) = (fun _ => none) ∧
    (ops.typeOf (ops.emptyT d K V)).K = K ∧ (ops.typeOf (ops.emptyT d K V)).V = V
  emptyBang : ∀ d, ∃ d', ops.emptyBang d = .ok d' ∧ ops.get d' = (fun _ => none)
  sizehint : ∀ d n, ops.get (ops.sizehint d n) = ops.get d ∧ ops.typeOf (ops.sizehint d n) = ops.typeOf d

end JuliaLean.DictsCov
