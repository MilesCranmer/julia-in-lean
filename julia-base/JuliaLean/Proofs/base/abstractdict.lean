import JuliaLean.base.abstractdict
import JuliaLean.Registry.Types

/-!
# Properties of `base/abstractdict.jl`

Every entry below is open for a proof or a Julia reproducer. Properties use the source-mirrored
methods in `JuliaLean.base.abstractdict`; operation records supply calls dispatched to concrete
AbstractDict implementations.
-/

namespace JuliaLean.Proofs.base.abstractdict

open JuliaLean.base.abstractdict JuliaLean.Registry

/-- `KeyTypeError` identifies the `dict key` operation, expected type, and received key. -/
def KeyTypeErrorFields : Prop :=
  ∀ (T A : Type) (expected : T) (key : A),
    let err := keyTypeError expected key
    err.functionName = "dict key" ∧ err.expected = expected ∧ err.got = key

/-- Membership follows lookup presence; pair membership compares a found value only. -/
def MembershipSpec : Prop :=
  ∀ (T D K V W : Type) (ops : DictOps T D K V) (d : D) (k : K)
    (valcmp : V → W → Truth) (w : W),
    haskeyAD ops d k = (ops.get d k).isSome ∧
    inKeySet ops (keysAD d) k = (ops.get d k).isSome ∧
    inPairAD ops valcmp d (k, w) =
      (match ops.get d k with | some v => valcmp v w | none => .no) ∧
    inNotPairAD ops d = .error (.errorException
      "AbstractDict collections only contain Pairs;\n             Either look for e.g. A=>B instead, or use the `keys` or `values`\n             function if you are looking for a key or value respectively.")

/-- Key and value views preserve pair order and iterator state. -/
def IteratorSemanticsSpec : Prop :=
  (∀ (D K V S : Type) (part : Part) (iter : D → Option S → Option ((K × V) × S))
      (d : D) (state : Option S),
    iterateAD iter part d state =
      match iter d state with
      | none => none
      | some (kv, next) => some (Part.project part kv, next)) ∧
  ∀ (T D K V : Type) (ops : DictOps T D K V) (d : D),
    iterPartAll ops .keys d = (ops.pairs d).map Prod.fst ∧
    iterPartAll ops .vals d = (ops.pairs d).map Prod.snd ∧
    (keysAD (K := K) d).dict = d ∧ (valuesAD d).dict = d ∧
    ops.pairs (pairsAD d) = ops.pairs d ∧
    (∀ (C KI VI G : Type) (keys : C → KI) (values : C → VI)
        (generator : KI → VI → G) (c : C),
      pairsGeneric keys values generator c = generator (keys c) (values c)) ∧
    (∀ part, lengthIter ops part d = ops.length d) ∧
    (∀ (isempty : D → Bool) part, isemptyIter isempty part d = isempty d) ∧
    (∀ (showarg : D → String) (name : String),
      summaryIter ops showarg name d = name ++ " for a " ++ summaryAD ops showarg d) ∧
    (∀ (showarg : D → String),
      summaryAD ops showarg d = showarg d ++
        (if ops.hasLength d then
          " with " ++ toString (ops.length d) ++
            if ops.length d == 1 then " entry" else " entries"
         else "(...)"))
def EmptyCopySpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (d empty copied : D),
    (emptyAD ops d = .ok empty →
      ops.pairs empty = [] ∧
      (ops.typeOf empty).K = (ops.typeOf d).K ∧
      (ops.typeOf empty).V = (ops.typeOf d).V) ∧
    (copyAD ops d = .ok copied →
      ∀ k, ops.get copied k = ops.get d k) ∧
    ∀ (same : Bool) (src result : D),
      copyBangAD ops same d src = .ok result →
        if same then result = d else ∀ k, ops.get result k = ops.get src k

/-- Dictionary type queries report the declared type parameters. -/
def DictTypeQueriesSpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (d : D) (t : DictType T)
    (k v : T),
    keytypeType t = t.K ∧ valtypeType t = t.V ∧
    keytypeAD ops d = (ops.typeOf d).K ∧ valtypeAD ops d = (ops.typeOf d).V ∧
    tt2 (⟨some k, some v⟩ : PairType T) = .ok v ∧
    eltypeValueIterator (⟨some k, some v⟩ : PairType T) = .ok v ∧
    (eltypeAD (some k) (some v)).key = some k ∧
    (eltypeAD (some k) (some v)).value = some v ∧
    (eltypeAD (some k) (none : Option T)).key = some k ∧
    (eltypeAD (some k) (none : Option T)).value = none ∧
    (eltypeAD (none : Option T) (some v)).key = none ∧
    (eltypeAD (none : Option T) (some v)).value = some v ∧
    (eltypeAD (none : Option T) (none : Option T)).key = none ∧
    (eltypeAD (none : Option T) (none : Option T)).value = none


/-- Generic indexing returns the stored value and reports `KeyError` on absence. -/
def GetIndexSpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (d : D) (k : K),
    getindexAD ops d k =
      match ops.get d k with | some v => .ok v | none => .error .keyError
def IndexingSpec : Prop :=
  ∀ (T D K V A : Type) (ops : DictOps T D K V) (d : D)
    (tuple : A → A → List A → K) (k1 k2 : A) (ks : List A) (v : V),
    getindexTup ops tuple d k1 k2 ks = getindexAD ops d (tuple k1 k2 ks) ∧
    setindexTup ops tuple d v k1 k2 ks = ops.setindex d v (tuple k1 k2 ks) ∧
    ∀ (pair : K × V), pushAD ops d pair = ops.setindex d pair.2 pair.1

/-- `get!` returns an existing value or converts, stores, and returns its default. -/
def GetBangValueSpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (d : D) (k : K) (v : V)
    (convertKey : KeyConversion K K) (convertValue : ValueConversion V V),
    (∀ key, convertKey.convert key = .ok key) →
    (∀ value, convertValue.convert value = .ok value) →
    match ops.get d k with
    | some old => getBangValue ops convertKey convertValue d k v = .ok (old, d)
    | none => ∃ updated, getBangValue ops convertKey convertValue d k v = .ok (v, updated) ∧
        ops.get updated k = some v

/-- `merge!` overwrites old values; `mergewith!` combines each value already present. -/
def MergeApplySpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (d : D) (others : List (Other T K V)) (merged : D),
    mergeBang ops d others = .ok merged →
      ∀ k, ops.get merged k =
        (others.flatMap fun other => other.pairs).foldl
          (fun old pair => if keyEq k pair.1 then some pair.2 else old) (ops.get d k)

def MergeWithApplySpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (combine : V → V → V) (d : D) (others : List (Other T K V)) (merged : D),
    mergewithBang ops combine d others = .ok merged →
      ∀ k, ops.get merged k =
        (others.flatMap fun other => other.pairs).foldl
          (fun old pair =>
            if keyEq k pair.1 then
              some (match old with | some value => combine value pair.2 | none => pair.2)
            else old) (ops.get d k)

/-- The three filter methods keep exactly the pairs accepted by `f`. -/
def FilterSemanticsSpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (f : K × V → Bool)
    (d filtered : D),
    (filterAD ops f d = .ok filtered →
      ∀ k v, ops.get d k = some v →
        ops.get filtered k = if f (k, v) then some v else none) ∧
    (filterBangAD ops f d = .ok filtered →
      ∀ k v, ops.get d k = some v →
        ops.get filtered k = if f (k, v) then some v else none) ∧
    (filterInOnePassAD ops f d = .ok filtered →
      ∀ k v, ops.get d k = some v →
        ops.get filtered k = if f (k, v) then some v else none)

/-- The documented filter and copy operations return a dictionary for every AbstractDict. -/
def FilterCopyNothrowSpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (d : D) (f : K × V → Bool),
    (∃ filtered, filterAD ops f d = .ok filtered) ∧
    (∃ copied, copyAD ops d = .ok copied)

/-- Type promotion folds each dictionary's key or value type from left to right. -/
def PromoteTypesSpec : Prop :=
  ∀ (T : Type) (promote : T → T → T) (K V : T) (types : List (DictType T)),
    promoteKAll promote K types = types.foldl (fun k d => promote k d.K) K ∧
    promoteVAll promote V types = types.foldl (fun v d => promote v d.V) V

/-- A merged IdDict retains every pair whose key is distinct by identity. -/
def MergeKeepsIdKeysSpec : Prop :=
  ∀ (T D E K V : Type) (ops : DictOps T D K V) (dops : DictOps T E K V)
    (promote : T → T → T) (dictOf : T → T → D → Result E)
    (isIdDict : D → Bool) (identity : K → K → Bool) (d : D),
    isIdDict d = true →
    (ops.pairs d).Pairwise (fun a b => identity a.1 b.1 = false) →
    ∃ merged, mergeAD ops dops promote dictOf d [] = .ok merged ∧
      (dops.pairs merged).length = (ops.pairs d).length

def DictEqualitySymmetricSpec : Prop :=
  ∀ (T D E K V : Type) (lops : DictOps T D K V) (rops : DictOps T E K V)
    (lIsId rIsId : Bool) (valueEq : V → V → Truth) (l : D) (r : E),
    (∀ a b, valueEq a b = valueEq b a) →
    equalAD lops rops lIsId rIsId valueEq l r =
      equalAD rops lops rIsId lIsId (fun a b => valueEq b a) r l

def DictBothEqualitySymmetricSpec : Prop :=
  ∀ (T D E K V : Type) (lops : DictOps T D K V) (rops : DictOps T E K V)
    (same : D → E → Bool) (sameReverse : E → D → Bool)
    (lIsId rIsId : Bool) (valueEq : V → V → Bool) (l : D) (r : E),
    (∀ a b, valueEq a b = valueEq b a) →
    equalAD lops rops lIsId rIsId (fun a b => boolTruth (valueEq a b)) l r =
      equalAD rops lops rIsId lIsId (fun a b => boolTruth (valueEq b a)) r l ∧
    isequalAD lops rops same lIsId rIsId valueEq l r =
      isequalAD rops lops sameReverse rIsId lIsId (fun a b => valueEq b a) r l

/-- Dictionary hashing is unchanged when pair order changes. -/
def HashPermutationSpec : Prop :=
  ∀ (T D K V U : Type) (ops : DictOps T D K V)
    (seedOf : Nat → U) (xor : U → U → U)
    (hashKey : K → U → U) (hashValue : V → U) (hashUInt : U → U → U)
    (a b : D) (h : U),
    (∀ x y, xor x y = xor y x) →
    (∀ x y z, xor (xor x y) z = xor x (xor y z)) →
    (ops.pairs a).Perm (ops.pairs b) →
    hashAD ops seedOf xor hashKey hashValue hashUInt a h =
      hashAD ops seedOf xor hashKey hashValue hashUInt b h

/-- The `sizehint!` fallback leaves the dictionary unchanged. -/
def SizeHintFallbackSpec : Prop :=
  ∀ (D : Type) (d : D) (n : Nat), sizehintAD d n = d

/-- `convert` preserves identity or rejects a key collision that changes length. -/
def ConversionSpec : Prop :=
  (∀ (D : Type) (d : D), convertSame d = d) ∧
  ∀ (T D E K V : Type) (ops : DictOps T D K V)
    (resultLength : E → Nat) (construct : D → Result E) (d : D),
    (∀ e, construct d = .error e → convertAD ops resultLength construct d = .error e) ∧
    ∀ result,
      convertAD ops resultLength construct d = .ok result ↔
        construct d = .ok result ∧ resultLength result = ops.length d

/-- `_tablesz` follows the integer table-size rule. -/
def TableSizeSpec : Prop :=
  ∀ (I : Type) (lt : I → I → Bool) (ofNat : Nat → I) (one : I)
    (sub shl : I → I → I) (topSetBit : I → I) (x : I),
    tableSize lt ofNat one sub shl topSetBit x =
      if lt x (ofNat 16) then ofNat 16 else shl one (topSetBit (sub x one))



/-- `map!` and `mergewith!` update every visited value according to their functions. -/
def MapValuesAndMergeOnceSpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (d d' merged : D)
    (f : V → V) (combine : V → V → V),
    (mapValuesAD ops f ⟨d⟩ = .ok (d', ⟨d⟩) →
      ∀ k v, ops.get d k = some v → ops.get d' k = some (f v)) ∧
    (mergewithBang2 ops combine d (ops.other d) = .ok merged →
      ∀ k v, ops.get d k = some v → ops.get merged k = some (combine v v))
def DictsMergeSpec : Prop := MergeApplySpec ∧ MergeWithApplySpec

/-- Curried and callable merge forms preserve their explicit combiner. -/
def MergeOverloadsSpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (combine : V → V → V)
    (d : D) (others : List (Other T K V)),
    mergewithCurried ops combine d others = mergewithBang ops combine d others ∧
    mergeBangCombine ops combine d others = mergewithBang ops combine d others


/-- The growth loop returns an empty destination unchanged and rejects noniterables. -/
def GrowToBoundarySpec : Prop :=
  (∀ (A : Type), throwDictKV (A := A) =
    .error (.argumentError "AbstractDict(kv): kv needs to be an iterator of 2-tuples or pairs")) ∧
  ∀ (T D X : Type) (ty : TyOps T X) (ops : DictOps T D X X) (d : D),
    growTo ty ops d none = throwDictKV ∧
    growTo ty ops d (some []) = .ok d


/-!
## Method-to-property table

| Julia method | Property |
|---|---|
| `KeyTypeError(K, key)@15` | `dictscov-abstractdict-l15` |
| `haskey@19`, `in(::Pair)@21`, `in(non-Pair)@29`, `in(::KeySet)@73` | `abstractdict-membership` |
| `summary@35`, iterator `summary@53`, `length@60`, `isempty@61`, `iterate@65`, `keys@107`, `values@133`, `pairs@178`, `pairs(::AbstractDict)@180` | `abstractdict-iterator-semantics` |
| `show(::Union{KeySet,ValueIterator})@58` | nothing to promise: delegates to `show_vector` |
| `copy(::KeySet)@71` | nothing to promise: delegates to `copymutable` |
| `_tt2@62`, `eltype(::ValueIterator)@63`, `keytype@310,311`, `valtype@324,325`, `eltype(::AbstractDict)@490` | `abstractdict-type-queries` |
| `empty@194,195`, `copy(::AbstractDict)@197`, `copy!@198` | `abstractdict-empty-copy` |
| `merge!@224`, `mergewith!@283,288`, `mergewith!@295`, `merge! callable@297` | `dicts-merge`, `abstractdict-merge-overloads` |
| `merge@361`, `mergewith@404,406`, `_typeddict@413`, `promoteK/V@409-412` | `dictscov-merge-iddict`, `abstractdict-promotion` |
| `filter!@439`, `filter_in_one_pass!@452`, `filter@479` | `abstractdict-filter-semantics`, `dictscov-immutable-filter-copy` |
| `isequal@504`, `==@518` | `dicts-persistentdict-eq-asymmetric`, `dicts-immutabledict-isequal` |
| `sizehint!@536`, `hash@539` | `abstractdict-sizehint`, `hashops-unordered-hash` |
| `getindex@547,557`, `setindex!@558`, `get!@560,561`, `push!@570` | `abstractdict-indexing`, `dicts-getbang-value` |
| `convert@573,575` | `abstractdict-conversion` |
| `_tablesz@584` | `abstractdict-table-size` |
| `_throw_dict_kv_error@589`, `grow_to!@591,611` | `abstractdict-grow-to` |
| `dict_with_eltype@637-642` | nothing to promise: internal helpers for public `Dict` constructors |
| `map!@673` | `dictscov-iddict-map-rehash` |

The `keys` generic-function declaration at line 81 has no method body.
-/
/-! Nothing to promise:
show(io::IO, iter::Union{KeySet,ValueIterator})@58: forwards to `show_vector`.
copy(v::KeySet)@71: forwards to `copymutable`; the generic set copy owns its behavior.
dict_with_eltype(DT_apply, kv, ::TP{K,V})@637: internal constructor type dispatch; the public Dict constructor owns the user-visible promise.
dict_with_eltype(DT_apply, kv::Generator, ::TP{K,V})@638: internal constructor type dispatch; the public Dict constructor owns the user-visible promise.
dict_with_eltype(DT_apply, ::Type{Pair{K,V}})@639: internal empty constructor selection; the public Dict constructor owns the user-visible promise.
dict_with_eltype(DT_apply, ::Type)@640: internal Any constructor selection; the public Dict constructor owns the user-visible promise.
dict_with_eltype(DT_apply::F, kv, t)@641: internal constructor growth; the public Dict constructor owns the user-visible promise.
dict_with_eltype(DT_apply::F, kv::Generator, t)@642: internal generator dispatch; the public Dict constructor owns the user-visible promise.
-/
def IndexingAllSpec : Prop := GetIndexSpec ∧ IndexingSpec

private def entry (id : String) (juliaFns : List String) (statement source : String)
    (prop : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/abstractdict.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := .todo, prop := prop }

def entries : List Entry := [
  entry "dictscov-abstractdict-l15" ["KeyTypeError(K, key)"]
    "KeyTypeError records the dict-key operation, expected type, and received key."
    "invariant; base/abstractdict.jl:15" ``KeyTypeErrorFields,
  entry "abstractdict-membership"
    ["haskey(d::AbstractDict, k)", "in(p::Pair, a::AbstractDict, valcmp=(==))",
      "in(p, a::AbstractDict)", "in(k, v::KeySet)"]
    "Dictionary membership tests key presence and compares a pair's value only when its key exists."
    "membership invariant; base/abstractdict.jl:19-33,73" ``MembershipSpec,
  entry "abstractdict-iterator-semantics"
    ["iterate(v::Union{KeySet,ValueIterator}, state...)", "keys(a::AbstractDict)",
      "values(a::AbstractDict)", "pairs(collection)", "pairs(a::AbstractDict)",
      "summary(io::IO, t::AbstractDict)", "summary(io::IO, iter::T)",
      "length(v::Union{KeySet,ValueIterator})", "isempty(v::Union{KeySet,ValueIterator})"]
    "Key and value views preserve pair order and state, and dictionary summaries report the correct count."
    "keys, values, pairs and summary docstrings; base/abstractdict.jl:35-43,53-69,84-92,109-118,135-180"
    ``IteratorSemanticsSpec,
  entry "abstractdict-type-queries"
    ["_tt2(::Type{Pair{A,B}})", "eltype(::Type{ValueIterator{D}})",
      "keytype(::Type{<:AbstractDict{K}})", "keytype(a::AbstractDict)",
      "valtype(::Type{<:AbstractDict{<:Any,V}})", "valtype(a::AbstractDict)",
      "eltype(::Type{<:AbstractDict{K,V}})"]
    "Dictionary key, value, and pair element types match the declared type parameters."
    "keytype, valtype and values docstrings; base/abstractdict.jl:62-63,299-325,490-502"
    ``DictTypeQueriesSpec,
  entry "abstractdict-empty-copy" ["empty(a::AbstractDict)",
      "empty(a::AbstractDict, ::Type{V})", "copy(a::AbstractDict)",
      "copy!(dst::AbstractDict, src::AbstractDict)"]
    "Empty dictionaries preserve requested types, copies preserve lookups, and copy! replaces destination contents."
    "empty docstring; copy invariants; base/abstractdict.jl:183-201" ``EmptyCopySpec,
  entry "abstractdict-indexing"
    ["getindex(t::AbstractDict{<:Any,V}, key)", "getindex(t::AbstractDict, k1, k2, ks...)",
      "setindex!(t::AbstractDict, v, k1, k2, ks...)", "push!(t::AbstractDict, p::Pair)"]
    "Indexing returns stored values or raises KeyError, and tuple indexing and push! use the corresponding key-value pair."
    "KeyError docstring and indexing behavior; base/abstractdict.jl:5-9,547-558,570"
    ``IndexingAllSpec,
  entry "dicts-getbang-value"
    ["get!(t::AbstractDict, key, default)",
      "get!(default::Callable, t::AbstractDict{K,V}, key)"]
    "get! returns the stored value, or converts, stores, and returns the default."
    "get! behavior; base/abstractdict.jl:560-568" ``GetBangValueSpec,
  entry "dicts-merge"
    ["merge!(d::AbstractDict, others::AbstractDict...)",
      "mergewith!(combine, d::AbstractDict, others::AbstractDict...)",
      "mergewith!(combine, d1::AbstractDict, d2::AbstractDict)"]
    "merge! overwrites with source pairs; mergewith! combines values for keys already present."
    "merge! and mergewith! docstrings; base/abstractdict.jl:203-293" ``DictsMergeSpec,
  entry "abstractdict-merge-overloads"
    ["mergewith!(combine)", "merge!(combine::Callable, args...)",
      "mergewith(combine)"]
    "Curried mergewith! and mergewith preserve the combiner, and callable merge! delegates to mergewith!."
    "mergewith! compatibility and curry docstrings; base/abstractdict.jl:237-249,295-297,365-376,406"
    ``MergeOverloadsSpec,
  entry "abstractdict-promotion" ["promoteK(K)", "promoteV(V)",
      "promoteK(K, d, ds...)", "promoteV(V, d, ds...)"]
    "Key and value type promotion folds dictionary type parameters from left to right."
    "type invariant; base/abstractdict.jl:409-412" ``PromoteTypesSpec,
  entry "abstractdict-filter-semantics"
    ["filter!(f, d::AbstractDict)", "filter_in_one_pass!(f, d::AbstractDict)",
      "filter(f, d::AbstractDict)"]
    "Each filter method keeps exactly the key-value pairs accepted by its predicate."
    "filter! and filter docstrings; base/abstractdict.jl:419-488" ``FilterSemanticsSpec,
  entry "dictscov-immutable-filter-copy"
    ["filter(f, d::AbstractDict)", "copy(a::AbstractDict)"]
    "filter and copy return a dictionary for every AbstractDict, including ImmutableDict."
    "filter docstring and copy behavior; base/abstractdict.jl:197,461-478"
    ``FilterCopyNothrowSpec,
  entry "dicts-persistentdict-eq-asymmetric"
    ["==(::AbstractDict, ::AbstractDict)"]
    "== between AbstractDicts is symmetric."
    "== docstring base/operators.jl:116; base/abstractdict.jl:518-533"
    ``DictEqualitySymmetricSpec,
  entry "dicts-immutabledict-isequal"
    ["isequal(::AbstractDict, ::AbstractDict)", "==(::AbstractDict, ::AbstractDict)"]
    "isequal and == between AbstractDicts are symmetric."
    "isequal docstring base/operators.jl:152; base/abstractdict.jl:504-533"
    ``DictBothEqualitySymmetricSpec,
  entry "hashops-unordered-hash"
    ["hash(a::AbstractDict, h::UInt)"]
    "Permuting an AbstractDict's pairs does not change its hash for any seed."
    "hash docstring base/hashing.jl:12-20; base/abstractdict.jl:538-545"
    ``HashPermutationSpec,
  entry "abstractdict-sizehint" ["sizehint!(d::AbstractDict, n)"]
    "The generic sizehint! fallback returns the same dictionary."
    "fallback invariant; base/abstractdict.jl:535-536" ``SizeHintFallbackSpec,
  entry "abstractdict-conversion"
    ["convert(::Type{T}, x::T)", "convert(::Type{T}, x::AbstractDict)"]
    "Conversion preserves an existing dictionary or rejects a key collision that reduces its length."
    "conversion behavior; base/abstractdict.jl:572-581" ``ConversionSpec,
  entry "abstractdict-table-size" ["_tablesz(x::T) where T <: Integer"]
    "The table size is 16 below 16 and otherwise follows the top-set-bit shift."
    "table-size invariant; base/abstractdict.jl:584" ``TableSizeSpec,
  entry "abstractdict-grow-to" ["_throw_dict_kv_error()", "grow_to!(dest::AbstractDict, itr)",
      "grow_to!(dest::AbstractDict{K,V}, itr, st)"]
    "Invalid dictionary-constructor iterators raise the documented ArgumentError; empty input leaves the destination unchanged."
    "constructor invariant; base/abstractdict.jl:588-634" ``GrowToBoundarySpec,
  entry "dictscov-merge-iddict"
    ["merge(d::AbstractDict, others::AbstractDict...)", "mergewith(combine, d::AbstractDict, others::AbstractDict...)",
      "_typeddict(d::AbstractDict, others::AbstractDict...)"]
    "Merging an IdDict retains every key distinct by identity."
    "merge docstring; base/abstractdict.jl:327-417" ``MergeKeepsIdKeysSpec,
  entry "dictscov-iddict-map-rehash"
    ["map!(f, iter::ValueIterator)", "mergewith!(combine, d1::AbstractDict, d2::AbstractDict)"]
    "map! transforms every value once, and merging a dictionary with itself combines each value once."
    "map! and mergewith! docstrings; base/abstractdict.jl:243-244,650-681"
    ``MapValuesAndMergeOnceSpec
]

end JuliaLean.Proofs.base.abstractdict
