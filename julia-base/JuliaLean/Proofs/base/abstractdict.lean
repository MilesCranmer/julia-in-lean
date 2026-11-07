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

end JuliaLean.Proofs.base.abstractdict

namespace JuliaLean.ChatGPT.Batch4.Group15
open JuliaLean.Proofs.base.abstractdict JuliaLean.base.abstractdict

theorem DictscovAbstractdictL15_proven : JuliaLean.Proofs.base.abstractdict.KeyTypeErrorFields := by
  intro T A expected key
  exact ⟨rfl, rfl, rfl⟩

theorem AbstractdictMembership_proven : JuliaLean.Proofs.base.abstractdict.MembershipSpec := by
  intro T D K V W ops d k valcmp w
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem AbstractdictIteratorSemantics_proven : JuliaLean.Proofs.base.abstractdict.IteratorSemanticsSpec := by
  constructor
  · intro D K V S part iter d state
    rfl
  · intro T D K V ops d
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro C KI VI G keys values generator c
      rfl
    · intro part
      rfl
    · intro isempty part
      rfl
    · intro showarg name
      rfl
    · intro showarg
      rfl

theorem AbstractdictTypeQueries_proven : JuliaLean.Proofs.base.abstractdict.DictTypeQueriesSpec := by
  intro T D K V ops d t k v
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem foundation_empty_dispatch (ops : DictOps T D K V) (d : D) :
    emptyAD ops d = ops.emptyT d (ops.typeOf d).K (ops.typeOf d).V := rfl

theorem foundation_copy_same (ops : DictOps T D K V) (d src : D) :
    copyBangAD ops true d src = .ok d := rfl

theorem foundation_get_existing (ops : DictOps T D K V) (d : D) (k : K) (v old : V)
    (convertKey : KeyConversion K K) (convertValue : ValueConversion V V)
    (hkey : convertKey.convert k = .ok k) (hget : ops.get d k = some old) :
    getBangValue ops convertKey convertValue d k v = .ok (old, d) := by
  simp only [getBangValue, getBangCallable, hkey, Bind.bind, Except.bind,
    haskeyAD, inKeySet, keysAD, hget, Option.isSome_some,
    ite_true, getindexAD, Pure.pure, Except.pure]

theorem foundation_get_inserted (ops : DictOps T D K V) (d updated : D)
    (k : K) (v : V) (convertKey : KeyConversion K K)
    (convertValue : ValueConversion V V)
    (hkey : convertKey.convert k = .ok k)
    (hvalue : convertValue.convert v = .ok v)
    (hget : ops.get d k = none) (hset : ops.setindex d v k = .ok updated) :
    getBangValue ops convertKey convertValue d k v = .ok (v, updated) := by
  simp only [getBangValue, getBangCallable, hkey, Bind.bind, Except.bind,
    haskeyAD, inKeySet, keysAD, hget, Option.isSome_none, Bool.false_eq_true,
    ite_false, hvalue, hset, Pure.pure, Except.pure]

theorem foundation_get_absent_with_contract (ops : DictOps T D K V) (d : D)
    (k : K) (v : V) (convertKey : KeyConversion K K)
    (convertValue : ValueConversion V V)
    (hkey : convertKey.convert k = .ok k)
    (hvalue : convertValue.convert v = .ok v)
    (hget : ops.get d k = none)
    (hinsert : ∃ updated, ops.setindex d v k = .ok updated ∧
      ops.get updated k = some v) :
    ∃ updated, getBangValue ops convertKey convertValue d k v = .ok (v, updated) ∧
      ops.get updated k = some v := by
  obtain ⟨updated, hset, hlookup⟩ := hinsert
  exact ⟨updated, foundation_get_inserted ops d updated k v convertKey convertValue
    hkey hvalue hget hset, hlookup⟩

theorem foundation_no_badkeys (pairs : List (K × V)) (keys : List K) :
    pairs.foldl (fun acc pair => if true then acc else acc ++ [pair.1]) keys = keys := by
  induction pairs generalizing keys with
  | nil => rfl
  | cons pair rest ih =>
    change rest.foldl (fun acc pair => if true then acc else acc ++ [pair.1]) keys = keys
    exact ih keys

theorem foundation_identity_fold (pairs : List (K × V)) (d : D) :
    pairs.foldlM (fun acc _ => (Except.ok acc : Result D)) d = .ok d := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    change rest.foldlM (fun acc _ => (Except.ok acc : Result D)) d = .ok d
    exact ih

theorem foundation_filter_true (ops : DictOps T D K V) (d : D) :
    filterBangAD ops (fun _ => true) d = .ok d := by
  unfold filterBangAD
  rw [foundation_no_badkeys]
  rfl

theorem foundation_filter_one_pass_true (ops : DictOps T D K V) (d : D) :
    filterInOnePassAD ops (fun _ => true) d = .ok d := by
  change (ops.pairs d).foldlM (fun acc _ => (Except.ok acc : Result D)) d = .ok d
  exact foundation_identity_fold (ops.pairs d) d

def foundationImmutableOps : DictOps Unit Bool Nat Nat where
  pairs d := if d then [(1, 2)] else []
  get d k := if d && k == 1 then some 2 else none
  setindex _ _ _ := .error (.methodError "setindex!")
  delete _ _ := .error (.methodError "delete!")
  emptyT _ _ _ := .ok false
  emptyBang _ := .error (.methodError "empty!")
  length d := if d then 1 else 0
  sizehint d _ := d
  hasLength _ := true
  typeOf _ := ⟨"ImmutableDict{Int,Int}", (), ()⟩

theorem foundation_get_immutable_failure :
    getBangValue foundationImmutableOps
      ⟨fun (k : Nat) => .ok k⟩ ⟨fun (v : Nat) => .ok v⟩ true 2 3 =
      .error (.methodError "setindex!") := rfl

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15

open JuliaLean.base.abstractdict JuliaLean.Proofs.base.abstractdict

def ceLookup {K V : Type} (keyEq : K → K → Bool) : List (K × V) → K → Option V
  | [], _ => none
  | pair :: rest, key => if keyEq key pair.1 then some pair.2 else ceLookup keyEq rest key

def ceInsert {K V : Type} (keyEq : K → K → Bool) (key : K) (value : V) :
    List (K × V) → List (K × V)
  | [] => [(key, value)]
  | pair :: rest => if keyEq key pair.1 then (key, value) :: rest
      else pair :: ceInsert keyEq key value rest

def ceDictOps {K V : Type} (keyEq : K → K → Bool) (mutableDict : Bool)
    (name : String) : DictOps Unit (List (K × V)) K V where
  pairs := id
  get := ceLookup keyEq
  setindex := fun d v k => if mutableDict then .ok (ceInsert keyEq k v d)
    else .error (.methodError "setindex!")
  delete := fun d k => if mutableDict then .ok (d.filter (fun pair => !(keyEq k pair.1)))
    else .error (.methodError "delete!")
  emptyT := fun _ _ _ => .ok []
  emptyBang := fun _ => if mutableDict then .ok [] else .error (.methodError "empty!")
  length := List.length
  sizehint := fun d _ => d
  hasLength := fun _ => true
  typeOf := fun _ => ⟨name, (), ()⟩

def ceImmutableOneOps : DictOps Unit (List (Unit × Unit)) Unit Unit :=
  ceDictOps (fun _ _ => true) false "ImmutableDict{Symbol,Int}"

theorem ceImmutableFilterFails :
    filterAD ceImmutableOneOps (fun _ => true) [((), ())] =
      .error (.methodError "setindex!") := by
  rfl

theorem DictscovImmutableFilterCopy_refuted :
    ¬ JuliaLean.Proofs.base.abstractdict.FilterCopyNothrowSpec := by
  intro h
  obtain ⟨filtered, hf⟩ := (h Unit (List (Unit × Unit)) Unit Unit
    ceImmutableOneOps [((), ())] (fun _ => true)).1
  rw [ceImmutableFilterFails] at hf
  cases hf

theorem cePromoteKStepFold {T : Type} (promote : T → T → T)
    (K : T) (d : DictType T) (ds : List (DictType T)) :
    promoteKStep promote K d ds = (d :: ds).foldl (fun k t => promote k t.K) K := by
  induction ds generalizing K d with
  | nil => rfl
  | cons next rest ih =>
      exact ih (promote K d.K) next

theorem cePromoteVStepFold {T : Type} (promote : T → T → T)
    (V : T) (d : DictType T) (ds : List (DictType T)) :
    promoteVStep promote V d ds = (d :: ds).foldl (fun v t => promote v t.V) V := by
  induction ds generalizing V d with
  | nil => rfl
  | cons next rest ih =>
      exact ih (promote V d.V) next

theorem AbstractdictPromotion_proven : JuliaLean.Proofs.base.abstractdict.PromoteTypesSpec := by
  intro T promote K V types
  cases types with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds => exact ⟨cePromoteKStepFold promote K d ds,
      cePromoteVStepFold promote V d ds⟩

inductive CeOneKey where
  | booleanTrue
  | integerOne
  deriving DecidableEq

def ceOneIdentity : CeOneKey → CeOneKey → Bool
  | .booleanTrue, .booleanTrue => true
  | .integerOne, .integerOne => true
  | _, _ => false

def ceOneValueEquality (_ _ : CeOneKey) : Bool := true

def ceIdOneOps : DictOps Unit (List (CeOneKey × Unit)) CeOneKey Unit :=
  ceDictOps ceOneIdentity true "IdDict{Any,Int}"

def ceValueOneOps : DictOps Unit (List (CeOneKey × Unit)) CeOneKey Unit :=
  ceDictOps ceOneValueEquality true "Dict{Any,Int}"

def ceTwoIdentityKeys : List (CeOneKey × Unit) :=
  [(.integerOne, ()), (.booleanTrue, ())]

def ceDictFromId (_ _ : Unit) (d : List (CeOneKey × Unit)) :
    Result (List (CeOneKey × Unit)) :=
  .ok (d.foldl (fun out pair => ceInsert ceOneValueEquality pair.1 pair.2 out) [])

theorem ceMergeIdCollapses :
    mergeAD ceIdOneOps ceValueOneOps (fun _ _ => ()) ceDictFromId ceTwoIdentityKeys [] =
      .ok [(.booleanTrue, ())] := by
  rfl

theorem DictscovMergeIddict_refuted :
    ¬ JuliaLean.Proofs.base.abstractdict.MergeKeepsIdKeysSpec := by
  intro h
  have distinct : (ceIdOneOps.pairs ceTwoIdentityKeys).Pairwise
      (fun a b => ceOneIdentity a.1 b.1 = false) := by decide
  obtain ⟨merged, hm, hn⟩ := h Unit (List (CeOneKey × Unit)) (List (CeOneKey × Unit))
    CeOneKey Unit ceIdOneOps ceValueOneOps (fun _ _ => ()) ceDictFromId
    (fun _ => true) ceOneIdentity ceTwoIdentityKeys rfl distinct
  rw [ceMergeIdCollapses] at hm
  cases hm
  have bad : (1 : Nat) = 2 := hn
  cases bad

inductive CeArrayKey where
  | firstArray
  | secondArray
  deriving DecidableEq

def ceArrayIdentity : CeArrayKey → CeArrayKey → Bool
  | .firstArray, .firstArray => true
  | .secondArray, .secondArray => true
  | _, _ => false

def ceArrayValueEquality (_ _ : CeArrayKey) : Bool := true

def cePersistentOps : DictOps Unit (List (CeArrayKey × Unit)) CeArrayKey Unit :=
  ceDictOps ceArrayIdentity false "PersistentDict{Vector{Int},Int}"

def ceArrayDictOps : DictOps Unit (List (CeArrayKey × Unit)) CeArrayKey Unit :=
  ceDictOps ceArrayValueEquality true "Dict{Vector{Int},Int}"

def cePersistentOne : List (CeArrayKey × Unit) := [(.firstArray, ())]
def ceArrayDictOne : List (CeArrayKey × Unit) := [(.secondArray, ())]

theorem DictsPersistentdictEqAsymmetric_refuted :
    ¬ JuliaLean.Proofs.base.abstractdict.DictEqualitySymmetricSpec := by
  intro h
  have bad := h Unit (List (CeArrayKey × Unit)) (List (CeArrayKey × Unit))
    CeArrayKey Unit cePersistentOps ceArrayDictOps false false (fun _ _ => .yes)
    cePersistentOne ceArrayDictOne (fun _ _ => rfl)
  have impossible : Truth.yes = Truth.no := bad
  cases impossible

def ceSymbolEquality (a b : Bool) : Bool := a == b

def ceRepeatedImmutableOps : DictOps Unit (List (Bool × Unit)) Bool Unit :=
  ceDictOps ceSymbolEquality false "ImmutableDict{Symbol,Int}"

def ceTwoSymbolDictOps : DictOps Unit (List (Bool × Unit)) Bool Unit :=
  ceDictOps ceSymbolEquality true "Dict{Symbol,Int}"

def ceRepeatedImmutable : List (Bool × Unit) := [(false, ()), (false, ())]
def ceTwoSymbolDict : List (Bool × Unit) := [(false, ()), (true, ())]

theorem DictsImmutabledictIsequal_refuted :
    ¬ JuliaLean.Proofs.base.abstractdict.DictBothEqualitySymmetricSpec := by
  intro h
  have bad := (h Unit (List (Bool × Unit)) (List (Bool × Unit)) Bool Unit
    ceRepeatedImmutableOps ceTwoSymbolDictOps (fun _ _ => false) (fun _ _ => false)
    false false (fun _ _ => true) ceRepeatedImmutable ceTwoSymbolDict
    (fun _ _ => rfl)).2
  have impossible : true = false := bad
  cases impossible

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15
open JuliaLean.base.abstractdict JuliaLean.Proofs.base.abstractdict

theorem ad_fold_perm {A U : Type} (combine : U → U → U) (value : A → U)
    (comm : ∀ x y, combine x y = combine y x)
    (assoc : ∀ x y z, combine (combine x y) z = combine x (combine y z))
    {xs ys : List A} (permutation : xs.Perm ys) :
    ∀ initial, xs.foldl (fun state a => combine state (value a)) initial =
      ys.foldl (fun state a => combine state (value a)) initial := by
  induction permutation with
  | nil => intro initial; rfl
  | cons a _ ih => intro initial; exact ih (combine initial (value a))
  | swap a b rest =>
    intro initial
    simp only [List.foldl_cons]
    rw [assoc, comm (value b) (value a), ← assoc]
  | trans _ _ ih₁ ih₂ =>
    intro initial
    exact (ih₁ initial).trans (ih₂ initial)

theorem HashopsUnorderedHash_proven : JuliaLean.Proofs.base.abstractdict.HashPermutationSpec := by
  intro T D K V U ops seedOf xor hashKey hashValue hashUInt a b h comm assoc permutation
  unfold hashAD
  rw [ad_fold_perm xor (fun kv : K × V => hashKey kv.1 (hashValue kv.2))
    comm assoc permutation]

theorem AbstractdictSizehint_proven : JuliaLean.Proofs.base.abstractdict.SizeHintFallbackSpec := by
  intro D d n
  rfl

theorem AbstractdictConversion_proven : JuliaLean.Proofs.base.abstractdict.ConversionSpec := by
  constructor
  · intro D d
    rfl
  · intro T D E K V ops resultLength construct d
    constructor
    · intro e failure
      unfold convertAD
      rw [failure]
      rfl
    · intro result
      unfold convertAD
      cases hc : construct d with
      | error e =>
        dsimp only [Bind.bind, Except.bind]
        constructor
        · intro impossible
          cases impossible
        · intro impossible
          cases impossible.1
      | ok constructed =>
        dsimp only [Bind.bind, Except.bind]
        by_cases hl : resultLength constructed = ops.length d
        · simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            Except.ok.injEq]
          constructor
          · intro eq
            subst result
            exact ⟨rfl, hl⟩
          · intro h
            exact h.1
        · have hb : (resultLength constructed != ops.length d) = true := by
            exact bne_iff_ne.mpr hl
          rw [ite_eq_left hb]
          constructor
          · intro impossible
            cases impossible
          · intro h
            have eq : constructed = result := Except.ok.inj h.1
            exact False.elim (hl (eq ▸ h.2))

theorem AbstractdictTableSize_proven : JuliaLean.Proofs.base.abstractdict.TableSizeSpec := by
  intro I lt ofNat one sub shl topSetBit x
  rfl

theorem AbstractdictMergeOverloads_proven : JuliaLean.Proofs.base.abstractdict.MergeOverloadsSpec := by
  intro T D K V ops combine d others
  exact ⟨rfl, rfl⟩

theorem AbstractdictGrowTo_proven : JuliaLean.Proofs.base.abstractdict.GrowToBoundarySpec := by
  constructor
  · intro A
    rfl
  · intro T D X ty ops d
    exact ⟨rfl, rfl⟩

theorem AbstractdictIndexing_proven : JuliaLean.Proofs.base.abstractdict.IndexingAllSpec := by
  constructor
  · intro T D K V ops d k
    unfold getindexAD
    cases ops.get d k <;> rfl
  · intro T D K V A ops d tuple k1 k2 ks v
    exact ⟨rfl, rfl, fun _ => rfl⟩

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15
open JuliaLean.base.abstractdict

theorem ad_foldlM_observe {A D E S : Type} (step : D → A → Except E D)
    (observe : D → S) (update : S → A → S)
    (step_law : ∀ d a out, step d a = .ok out → observe out = update (observe d) a)
    (xs : List A) (d out : D) (success : xs.foldlM step d = .ok out) :
    observe out = xs.foldl update (observe d) := by
  induction xs generalizing d with
  | nil =>
    have h : d = out := Except.ok.inj success
    subst out
    rfl
  | cons a rest ih =>
    cases hs : step d a with
    | error error =>
      simp only [List.foldlM_cons, hs, Bind.bind, Except.bind] at success
      cases success
    | ok next =>
      have remaining : rest.foldlM step next = .ok out := by
        simpa only [List.foldlM_cons, hs, Bind.bind, Except.bind] using success
      rw [List.foldl_cons, ← step_law d a next hs]
      exact ih next remaining

structure AdMergeLookupLaws (ops : DictOps T D K V) (keyEq : K → K → Bool) : Prop where
  inserted : ∀ d v k out, ops.setindex d v k = .ok out →
    ∀ q, ops.get out q = if keyEq q k then some v else ops.get d q
  sizehint_preserves : ∀ d n q, ops.get (ops.sizehint d n) q = ops.get d q
  equivalent_lookup : ∀ d q k, keyEq q k = true → ops.get d q = ops.get d k

theorem ad_merge_step_lookup (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (laws : AdMergeLookupLaws ops keyEq) (d out : D) (other : Other T K V)
    (success : mergeStep ops d other = .ok out) (q : K) :
    ops.get out q = other.pairs.foldl
      (fun old pair => if keyEq q pair.1 then some pair.2 else old) (ops.get d q) := by
  let prepared := if ops.hasLength d && other.hasLength then
      ops.sizehint d (ops.length d + other.pairs.length) else d
  have hp : ops.get prepared q = ops.get d q := by
    dsimp only [prepared]
    split
    · exact laws.sizehint_preserves d _ q
    · rfl
  have result := ad_foldlM_observe (fun state (pair : K × V) => ops.setindex state pair.2 pair.1)
    (fun state => ops.get state q)
    (fun old pair => if keyEq q pair.1 then some pair.2 else old)
    (fun state pair result h => laws.inserted state pair.2 pair.1 result h q)
    other.pairs prepared out success
  rw [hp] at result
  exact result

theorem ad_merge_overwrite_with_laws (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (laws : AdMergeLookupLaws ops keyEq) (d out : D) (others : List (Other T K V))
    (success : mergeBang ops d others = .ok out) (q : K) :
    ops.get out q = (others.flatMap fun other => other.pairs).foldl
      (fun old pair => if keyEq q pair.1 then some pair.2 else old) (ops.get d q) := by
  have result := ad_foldlM_observe (mergeStep ops) (fun state => ops.get state q)
    (fun old other => other.pairs.foldl
      (fun previous pair => if keyEq q pair.1 then some pair.2 else previous) old)
    (fun state other result h => ad_merge_step_lookup ops keyEq laws state result other h q)
    others d out success
  simpa only [List.foldl_flatMap] using result

theorem ad_mergewith_step_eq (ops : DictOps T D K V) (combine : V → V → V)
    (d : D) (other : Other T K V) :
    mergewithBang2 ops combine d other = other.pairs.foldlM
      (fun state pair => ops.setindex state
        (match ops.get state pair.1 with
        | some old => combine old pair.2
        | none => pair.2) pair.1) d := by
  unfold mergewithBang2
  apply congrArg (fun step : D → K × V → Result D => other.pairs.foldlM step d)
  funext state pair
  cases hget : ops.get state pair.1 <;>
    simp only [haskeyAD, inKeySet, keysAD, hget, Option.isSome_none,
      Option.isSome_some, Bool.false_eq_true, ite_false, ite_true, getindexAD,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem ad_mergewith_step_lookup (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (laws : AdMergeLookupLaws ops keyEq) (combine : V → V → V)
    (d out : D) (other : Other T K V)
    (success : mergewithBang2 ops combine d other = .ok out) (q : K) :
    ops.get out q = other.pairs.foldl (fun old pair =>
      if keyEq q pair.1 then
        some (match old with | some value => combine value pair.2 | none => pair.2)
      else old) (ops.get d q) := by
  rw [ad_mergewith_step_eq] at success
  apply ad_foldlM_observe _ (fun state => ops.get state q) _ ?_ other.pairs d out success
  intro state pair result h
  rw [laws.inserted state _ pair.1 result h q]
  by_cases heq : keyEq q pair.1 = true
  · simp only [heq, ite_true]
    rw [laws.equivalent_lookup state q pair.1 heq]
  · simp only [heq, Bool.false_eq_true, ite_false]

theorem ad_merge_combine_with_laws (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (laws : AdMergeLookupLaws ops keyEq) (combine : V → V → V)
    (d out : D) (others : List (Other T K V))
    (success : mergewithBang ops combine d others = .ok out) (q : K) :
    ops.get out q = (others.flatMap fun other => other.pairs).foldl
      (fun old pair => if keyEq q pair.1 then
        some (match old with | some value => combine value pair.2 | none => pair.2)
      else old) (ops.get d q) := by
  have result := ad_foldlM_observe (fun state other => mergewithBang2 ops combine state other)
    (fun state => ops.get state q)
    (fun old other => other.pairs.foldl
      (fun previous pair => if keyEq q pair.1 then
        some (match previous with | some value => combine value pair.2 | none => pair.2)
        else previous) old)
    (fun state other result h => ad_mergewith_step_lookup ops keyEq laws combine state result other h q)
    others d out success
  simpa only [List.foldl_flatMap] using result

theorem ad_map_values_with_laws (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (laws : AdMergeLookupLaws ops keyEq) (f : V → V) (d out : D)
    (success : mapValuesAD ops f ⟨d⟩ = .ok (out, ⟨d⟩)) (q : K) :
    ops.get out q = (ops.pairs d).foldl
      (fun old pair => if keyEq q pair.1 then some (f pair.2) else old) (ops.get d q) := by
  unfold mapValuesAD at success
  cases hfold : (ops.pairs d).foldlM
      (fun state pair => ops.setindex state (f pair.2) pair.1) d with
  | error error =>
    simp only [hfold, Bind.bind, Except.bind] at success
    cases success
  | ok result =>
    have heq : result = out := by
      have hp : (result, (⟨d⟩ : ValueIterator D)) = (out, ⟨d⟩) := by
        exact Except.ok.inj (by simpa only [hfold, Bind.bind, Except.bind, Pure.pure, Except.pure] using success)
      exact congrArg Prod.fst hp
    subst result
    exact ad_foldlM_observe _ (fun state => ops.get state q) _
      (fun state pair result h => laws.inserted state (f pair.2) pair.1 result h q)
      (ops.pairs d) d out hfold

theorem ad_foldl_identity {S A : Type} (step : S → A → S) (xs : List A) :
    (∀ state a, a ∈ xs → step state a = state) →
    ∀ initial, xs.foldl step initial = initial := by
  induction xs with
  | nil => intro _ initial; rfl
  | cons a rest ih =>
    intro h initial
    rw [List.foldl_cons, h initial a (List.mem_cons_self)]
    exact ih (fun state b hb => h state b (List.mem_cons_of_mem a hb)) initial

theorem ad_foldl_single_visit {S A : Type} (step : S → A → S)
    (before after : List A) (item : A) (initial : S)
    (before_identity : ∀ state a, a ∈ before → step state a = state)
    (after_identity : ∀ state a, a ∈ after → step state a = state) :
    (before ++ item :: after).foldl step initial = step initial item := by
  rw [List.foldl_append, ad_foldl_identity step before before_identity,
    List.foldl_cons, ad_foldl_identity step after after_identity]

theorem ad_map_lookup_single_visit (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (laws : AdMergeLookupLaws ops keyEq) (f : V → V) (d out : D)
    (q k : K) (v : V) (before after : List (K × V))
    (success : mapValuesAD ops f ⟨d⟩ = .ok (out, ⟨d⟩))
    (pairs : ops.pairs d = before ++ (k, v) :: after)
    (same_key : keyEq q k = true)
    (before_distinct : ∀ pair, pair ∈ before → keyEq q pair.1 = false)
    (after_distinct : ∀ pair, pair ∈ after → keyEq q pair.1 = false) :
    ops.get out q = some (f v) := by
  rw [ad_map_values_with_laws ops keyEq laws f d out success q, pairs]
  rw [ad_foldl_single_visit _ before after (k, v) (ops.get d q)
    (fun state pair hp => by rw [before_distinct pair hp] <;> rfl)
    (fun state pair hp => by rw [after_distinct pair hp] <;> rfl)]
  rw [same_key] <;> rfl

theorem ad_merge_self_single_visit (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (laws : AdMergeLookupLaws ops keyEq) (combine : V → V → V) (d out : D)
    (q k : K) (v : V) (before after : List (K × V))
    (success : mergewithBang2 ops combine d (ops.other d) = .ok out)
    (lookup : ops.get d q = some v)
    (pairs : ops.pairs d = before ++ (k, v) :: after)
    (same_key : keyEq q k = true)
    (before_distinct : ∀ pair, pair ∈ before → keyEq q pair.1 = false)
    (after_distinct : ∀ pair, pair ∈ after → keyEq q pair.1 = false) :
    ops.get out q = some (combine v v) := by
  have result := ad_mergewith_step_lookup ops keyEq laws combine d out (ops.other d) success q
  change ops.get out q = (ops.pairs d).foldl _ (ops.get d q) at result
  rw [pairs] at result
  rw [ad_foldl_single_visit _ before after (k, v) (ops.get d q)
    (fun state pair hp => by rw [before_distinct pair hp] <;> rfl)
    (fun state pair hp => by rw [after_distinct pair hp] <;> rfl)] at result
  simpa only [same_key, lookup, ite_true] using result

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.ChatGPT.Batch4.Group15
open JuliaLean.base.abstractdict

theorem ad_filter_lookup_fold (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (empty_lookup : ∀ d empty, emptyAD ops d = .ok empty →
      ∀ q, ops.get empty q = none)
    (insert_lookup : ∀ d v k out, ops.setindex d v k = .ok out →
      ∀ q, ops.get out q = if keyEq q k then some v else ops.get d q)
    (f : K × V → Bool) (d out : D)
    (success : filterAD ops f d = .ok out) (q : K) :
    ops.get out q = (ops.pairs d).foldl
      (fun old pair => if f pair then
        if keyEq q pair.1 then some pair.2 else old
        else old) none := by
  unfold filterAD at success
  cases he : emptyAD ops d with
  | error error =>
    simp only [he, Bind.bind, Except.bind] at success
    cases success
  | ok empty =>
    have hfold : (ops.pairs d).foldlM
        (fun state pair => if f pair then ops.setindex state pair.2 pair.1 else .ok state)
        empty = .ok out := by
      simpa only [he, Bind.bind, Except.bind] using success
    have result : ops.get out q = (ops.pairs d).foldl
        (fun old pair => if f pair then
          if keyEq q pair.1 then some pair.2 else old
          else old) (ops.get empty q) := by
      apply ad_foldlM_observe _ (fun state => ops.get state q) _ ?_
        (ops.pairs d) empty out hfold
      intro state pair next h
      cases hf : f pair with
      | false =>
        have hn : state = next := Except.ok.inj (by
          simpa only [hf, Bool.false_eq_true, ite_false] using h)
        subst next
        simp only [hf, Bool.false_eq_true, ite_false]
      | true =>
        have hs : ops.setindex state pair.2 pair.1 = .ok next := by
          simpa only [hf, ite_true] using h
        simpa only [hf, ite_true] using insert_lookup state pair.2 pair.1 next hs q
    rw [empty_lookup d empty he q] at result
    exact result

theorem ad_filter_rejected_keys_fold {K V S : Type}
    (f : K × V → Bool) (step : S → K → S)
    (pairs : List (K × V)) (keys : List K) (initial : S) :
    (pairs.foldl (fun keys pair => if f pair then keys else keys ++ [pair.1]) keys).foldl
      step initial =
    pairs.foldl (fun state pair => if f pair then state else step state pair.1)
      (keys.foldl step initial) := by
  induction pairs generalizing keys with
  | nil => rfl
  | cons pair rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases hf : f pair <;>
      simp only [hf, Bool.false_eq_true, ite_false, ite_true,
        List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ad_filter_bang_lookup_fold (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (delete_lookup : ∀ d k out, ops.delete d k = .ok out →
      ∀ q, ops.get out q = if keyEq q k then none else ops.get d q)
    (f : K × V → Bool) (d out : D)
    (success : filterBangAD ops f d = .ok out) (q : K) :
    ops.get out q = (ops.pairs d).foldl
      (fun old pair => if f pair then old else
        if keyEq q pair.1 then none else old) (ops.get d q) := by
  have result := ad_foldlM_observe (fun state key => ops.delete state key)
    (fun state => ops.get state q)
    (fun old key => if keyEq q key then none else old)
    (fun state key next h => delete_lookup state key next h q)
    ((ops.pairs d).foldl
      (fun keys pair => if f pair then keys else keys ++ [pair.1]) [])
    d out success
  simpa only [ad_filter_rejected_keys_fold, List.foldl_nil] using result

theorem ad_filter_one_pass_lookup_fold (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (delete_lookup : ∀ d k out, ops.delete d k = .ok out →
      ∀ q, ops.get out q = if keyEq q k then none else ops.get d q)
    (f : K × V → Bool) (d out : D)
    (success : filterInOnePassAD ops f d = .ok out) (q : K) :
    ops.get out q = (ops.pairs d).foldl
      (fun old pair => if f pair then old else
        if keyEq q pair.1 then none else old) (ops.get d q) := by
  apply ad_foldlM_observe _ (fun state => ops.get state q) _ ?_
    (ops.pairs d) d out success
  intro state pair next h
  cases hf : f pair with
  | false =>
    have hd : ops.delete state pair.1 = .ok next := by
      simpa only [hf, Bool.not_false, ite_true] using h
    simpa only [hf, Bool.false_eq_true, ite_false] using delete_lookup state pair.1 next hd q
  | true =>
    have hn : state = next := Except.ok.inj (by
      simpa only [hf, Bool.not_true, Bool.false_eq_true, ite_false] using h)
    subst next
    simp only [hf, ite_true]

theorem ad_filter_mutating_lookups_agree (ops : DictOps T D K V) (keyEq : K → K → Bool)
    (delete_lookup : ∀ d k out, ops.delete d k = .ok out →
      ∀ q, ops.get out q = if keyEq q k then none else ops.get d q)
    (f : K × V → Bool) (d twoPass onePass : D)
    (htwo : filterBangAD ops f d = .ok twoPass)
    (hone : filterInOnePassAD ops f d = .ok onePass) (q : K) :
    ops.get twoPass q = ops.get onePass q := by
  rw [ad_filter_bang_lookup_fold ops keyEq delete_lookup f d twoPass htwo q,
    ad_filter_one_pass_lookup_fold ops keyEq delete_lookup f d onePass hone q]

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.Proofs.base.abstractdict

open JuliaLean.base.abstractdict JuliaLean.Registry

def entries : List Entry := [
  { (entry "dictscov-abstractdict-l15" ["KeyTypeError(K, key)"]
    "KeyTypeError records the dict-key operation, expected type, and received key."
    "invariant; base/abstractdict.jl:15" ``KeyTypeErrorFields) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.DictscovAbstractdictL15_proven },
  { (entry "abstractdict-membership"
    ["haskey(d::AbstractDict, k)", "in(p::Pair, a::AbstractDict, valcmp=(==))",
      "in(p, a::AbstractDict)", "in(k, v::KeySet)"]
    "Dictionary membership tests key presence and compares a pair's value only when its key exists."
    "membership invariant; base/abstractdict.jl:19-33,73" ``MembershipSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictMembership_proven },
  { (entry "abstractdict-iterator-semantics"
    ["iterate(v::Union{KeySet,ValueIterator}, state...)", "keys(a::AbstractDict)",
      "values(a::AbstractDict)", "pairs(collection)", "pairs(a::AbstractDict)",
      "summary(io::IO, t::AbstractDict)", "summary(io::IO, iter::T)",
      "length(v::Union{KeySet,ValueIterator})", "isempty(v::Union{KeySet,ValueIterator})"]
    "Key and value views preserve pair order and state, and dictionary summaries report the correct count."
    "keys, values, pairs and summary docstrings; base/abstractdict.jl:35-43,53-69,84-92,109-118,135-180"
    ``IteratorSemanticsSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictIteratorSemantics_proven },
  { (entry "abstractdict-type-queries"
    ["_tt2(::Type{Pair{A,B}})", "eltype(::Type{ValueIterator{D}})",
      "keytype(::Type{<:AbstractDict{K}})", "keytype(a::AbstractDict)",
      "valtype(::Type{<:AbstractDict{<:Any,V}})", "valtype(a::AbstractDict)",
      "eltype(::Type{<:AbstractDict{K,V}})"]
    "Dictionary key, value, and pair element types match the declared type parameters."
    "keytype, valtype and values docstrings; base/abstractdict.jl:62-63,299-325,490-502"
    ``DictTypeQueriesSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictTypeQueries_proven },
  { (entry "abstractdict-empty-copy" ["empty(a::AbstractDict)",
      "empty(a::AbstractDict, ::Type{V})", "copy(a::AbstractDict)",
      "copy!(dst::AbstractDict, src::AbstractDict)"]
    "Empty dictionaries preserve requested types, copies preserve lookups, and copy! replaces destination contents."
    "empty docstring; copy invariants; base/abstractdict.jl:183-201" ``EmptyCopySpec) with status := .todo, thm := none, notes := "Statement gap: copying stored pairs between Dict and IdDict need not preserve alias lookups because key equivalence differs; require compatible key equivalence or state preservation of stored pairs. No Julia defect claimed." },
  { (entry "abstractdict-indexing"
    ["getindex(t::AbstractDict{<:Any,V}, key)", "getindex(t::AbstractDict, k1, k2, ks...)",
      "setindex!(t::AbstractDict, v, k1, k2, ks...)", "push!(t::AbstractDict, p::Pair)"]
    "Indexing returns stored values or raises KeyError, and tuple indexing and push! use the corresponding key-value pair."
    "KeyError docstring and indexing behavior; base/abstractdict.jl:5-9,547-558,570"
    ``IndexingAllSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictIndexing_proven },
  { (entry "dicts-getbang-value"
    ["get!(t::AbstractDict, key, default)",
      "get!(default::Callable, t::AbstractDict{K,V}, key)"]
    "get! returns the stored value, or converts, stores, and returns the default."
    "get! behavior; base/abstractdict.jl:560-568" ``GetBangValueSpec) with status := .todo, thm := none, notes := "Statement gap: the universal includes immutable dictionaries whose missing-key insertion fails; require successful insertion with its lookup law or specify propagation of insertion errors. No Julia defect claimed." },
  { (entry "dicts-merge"
    ["merge!(d::AbstractDict, others::AbstractDict...)",
      "mergewith!(combine, d::AbstractDict, others::AbstractDict...)",
      "mergewith!(combine, d1::AbstractDict, d2::AbstractDict)"]
    "merge! overwrites with source pairs; mergewith! combines values for keys already present."
    "merge! and mergewith! docstrings; base/abstractdict.jl:203-293" ``DictsMergeSpec) with status := .todo, thm := none, notes := "Statement gap: keyEq is arbitrary and is not passed to mergeBang or mergewithBang; connect the comparator to insertion, reservation and lookup laws before proving the claim." },
  { (entry "abstractdict-merge-overloads"
    ["mergewith!(combine)", "merge!(combine::Callable, args...)",
      "mergewith(combine)"]
    "Curried mergewith! and mergewith preserve the combiner, and callable merge! delegates to mergewith!."
    "mergewith! compatibility and curry docstrings; base/abstractdict.jl:237-249,295-297,365-376,406"
    ``MergeOverloadsSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictMergeOverloads_proven },
  { (entry "abstractdict-promotion" ["promoteK(K)", "promoteV(V)",
      "promoteK(K, d, ds...)", "promoteV(V, d, ds...)"]
    "Key and value type promotion folds dictionary type parameters from left to right."
    "type invariant; base/abstractdict.jl:409-412" ``PromoteTypesSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictPromotion_proven },
  { (entry "abstractdict-filter-semantics"
    ["filter!(f, d::AbstractDict)", "filter_in_one_pass!(f, d::AbstractDict)",
      "filter(f, d::AbstractDict)"]
    "Each filter method keeps exactly the key-value pairs accepted by its predicate."
    "filter! and filter docstrings; base/abstractdict.jl:419-488" ``FilterSemanticsSpec) with status := .todo, thm := none, notes := "Statement gap: the predicate tests queried lookup aliases rather than stored keys; true and Int(1) alias in Dict but can be distinguished by the predicate. Require predicate invariance or specify stored pairs." },
  { (entry "dictscov-immutable-filter-copy"
    ["filter(f, d::AbstractDict)", "copy(a::AbstractDict)"]
    "filter and copy return a dictionary for every AbstractDict, including ImmutableDict."
    "filter docstring and copy behavior; base/abstractdict.jl:197,461-478"
    ``FilterCopyNothrowSpec) with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.DictscovImmutableFilterCopy_refuted, issue := "Related JuliaLang/julia#22738 (open) discusses merge returning Dict for identity dictionaries. PR #40893 (merged) changes mutating mergewith! performance. No exact key-loss duplicate established." },
  { (entry "dicts-persistentdict-eq-asymmetric"
    ["==(::AbstractDict, ::AbstractDict)"]
    "== between AbstractDicts is symmetric."
    "== docstring base/operators.jl:116; base/abstractdict.jl:518-533"
    ``DictEqualitySymmetricSpec) with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.DictsPersistentdictEqAsymmetric_refuted, issue := "No exact duplicate established by completed narrow and broad queries. PR #52193 (merged) establishes identity-key semantics; #54740 and #53982 are related." },
  { (entry "dicts-immutabledict-isequal"
    ["isequal(::AbstractDict, ::AbstractDict)", "==(::AbstractDict, ::AbstractDict)"]
    "isequal and == between AbstractDicts are symmetric."
    "isequal docstring base/operators.jl:152; base/abstractdict.jl:504-533"
    ``DictBothEqualitySymmetricSpec) with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.DictsImmutabledictIsequal_refuted, issue := "Duplicate of JuliaLang/julia#64137 (open). Same repeated-key equality asymmetry; existing issue also covers hash disagreement." },
  { (entry "hashops-unordered-hash"
    ["hash(a::AbstractDict, h::UInt)"]
    "Permuting an AbstractDict's pairs does not change its hash for any seed."
    "hash docstring base/hashing.jl:12-20; base/abstractdict.jl:538-545"
    ``HashPermutationSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.HashopsUnorderedHash_proven },
  { (entry "abstractdict-sizehint" ["sizehint!(d::AbstractDict, n)"]
    "The generic sizehint! fallback returns the same dictionary."
    "fallback invariant; base/abstractdict.jl:535-536" ``SizeHintFallbackSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictSizehint_proven },
  { (entry "abstractdict-conversion"
    ["convert(::Type{T}, x::T)", "convert(::Type{T}, x::AbstractDict)"]
    "Conversion preserves an existing dictionary or rejects a key collision that reduces its length."
    "conversion behavior; base/abstractdict.jl:572-581" ``ConversionSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictConversion_proven },
  { (entry "abstractdict-table-size" ["_tablesz(x::T) where T <: Integer"]
    "The table size is 16 below 16 and otherwise follows the top-set-bit shift."
    "table-size invariant; base/abstractdict.jl:584" ``TableSizeSpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictTableSize_proven },
  { (entry "abstractdict-grow-to" ["_throw_dict_kv_error()", "grow_to!(dest::AbstractDict, itr)",
      "grow_to!(dest::AbstractDict{K,V}, itr, st)"]
    "Invalid dictionary-constructor iterators raise the documented ArgumentError; empty input leaves the destination unchanged."
    "constructor invariant; base/abstractdict.jl:588-634" ``GrowToBoundarySpec) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.AbstractdictGrowTo_proven },
  { (entry "dictscov-merge-iddict"
    ["merge(d::AbstractDict, others::AbstractDict...)", "mergewith(combine, d::AbstractDict, others::AbstractDict...)",
      "_typeddict(d::AbstractDict, others::AbstractDict...)"]
    "Merging an IdDict retains every key distinct by identity."
    "merge docstring; base/abstractdict.jl:327-417" ``MergeKeepsIdKeysSpec) with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.DictscovMergeIddict_refuted, issue := "Related JuliaLang/julia#22738 (open) discusses merge returning Dict for identity dictionaries. PR #40893 (merged) changes mutating mergewith! performance. No exact key-loss duplicate established." },
  { (entry "dictscov-iddict-map-rehash"
    ["map!(f, iter::ValueIterator)", "mergewith!(combine, d1::AbstractDict, d2::AbstractDict)"]
    "map! transforms every value once, and merging a dictionary with itself combines each value once."
    "map! and mergewith! docstrings; base/abstractdict.jl:243-244,650-681"
    ``MapValuesAndMergeOnceSpec) with status := .todo, thm := none, notes := "Statement gap: unrestricted DictOps lacks insertion/lookup and unique traversal laws. Existing bugs/dictscov-iddict-map-rehash.yaml and repro/dictscov-iddict-map-rehash.jl concern real rehash behavior under the older JuliaLean.DictsCov.IdDictMapOnce model; they do not settle this proposition." }
]

end JuliaLean.Proofs.base.abstractdict

namespace JuliaLean.ChatGPT.Batch8.Group3
open JuliaLean.Proofs.base.abstractdict JuliaLean.base.abstractdict

/-- The value-type empty overload delegates its explicit requested type unchanged. -/
theorem adBase_empty_value_dispatch (ops : DictOps T D K V) (d : D) (valueType : T) :
    emptyADV ops d valueType = ops.emptyT d (ops.typeOf d).K valueType := rfl

/-- Key conversion failures propagate before lookup, default evaluation, or mutation. -/
theorem adBase_get_key_failure (ops : DictOps T D K V) (d : D)
    (convertKey : KeyConversion Q K) (convertValue : ValueConversion W V)
    (key : Q) (value : W) (error : DictError)
    (failure : convertKey.convert key = .error error) :
    getBangValue ops convertKey convertValue d key value = .error error := by
  simp only [getBangValue, getBangCallable, failure, Bind.bind, Except.bind]

/-- An existing converted key bypasses value conversion and returns the original storage. -/
theorem adBase_get_converted_existing (ops : DictOps T D K V) (d : D)
    (convertKey : KeyConversion Q K) (convertValue : ValueConversion W V)
    (key : Q) (convertedKey : K) (default : W) (old : V)
    (hkey : convertKey.convert key = .ok convertedKey)
    (hget : ops.get d convertedKey = some old) :
    getBangValue ops convertKey convertValue d key default = .ok (old, d) := by
  simp only [getBangValue, getBangCallable, hkey, Bind.bind, Except.bind,
    haskeyAD, inKeySet, keysAD, hget, Option.isSome_some,
    ite_true, getindexAD, Pure.pure, Except.pure]

/-- The absent-key branch evaluates conversion and insertion in source order. -/
theorem adBase_get_converted_absent (ops : DictOps T D K V) (d : D)
    (convertKey : KeyConversion Q K) (convertValue : ValueConversion W V)
    (key : Q) (convertedKey : K) (default : W)
    (hkey : convertKey.convert key = .ok convertedKey)
    (hget : ops.get d convertedKey = none) :
    getBangValue ops convertKey convertValue d key default = (do
      let value ← convertValue.convert default
      let updated ← ops.setindex d value convertedKey
      pure (value, updated)) := by
  simp only [getBangValue, getBangCallable, hkey, Bind.bind, Except.bind,
    haskeyAD, inKeySet, keysAD, hget, Option.isSome_none,
    Bool.false_eq_true, ite_false, Pure.pure, Except.pure]

/-- Failure of an insertion is preserved exactly, including immutable-storage errors. -/
theorem adBase_get_insertion_failure (ops : DictOps T D K V) (d : D)
    (convertKey : KeyConversion K K) (convertValue : ValueConversion V V)
    (key : K) (value : V) (error : DictError)
    (hkey : convertKey.convert key = .ok key)
    (hvalue : convertValue.convert value = .ok value)
    (hget : ops.get d key = none)
    (hset : ops.setindex d value key = .error error) :
    getBangValue ops convertKey convertValue d key value = .error error := by
  rw [adBase_get_converted_absent ops d convertKey convertValue key key value hkey hget]
  simp only [hvalue, hset, Bind.bind, Except.bind]

/-- Copy forwards an unsuccessful empty construction without attempting merge. -/
theorem adBase_copy_empty_failure (ops : DictOps T D K V) (d : D) (error : DictError)
    (failure : emptyAD ops d = .error error) : copyAD ops d = .error error := by
  simp only [copyAD, failure, Bind.bind, Except.bind]

/-- The distinct-source copy! branch forwards an unsuccessful empty! operation. -/
theorem adBase_copy_bang_empty_failure (ops : DictOps T D K V) (d src : D)
    (error : DictError) (failure : ops.emptyBang d = .error error) :
    copyBangAD ops false d src = .error error := by
  simp only [copyBangAD, Bool.false_eq_true, ite_false, failure, Bind.bind, Except.bind]

end JuliaLean.ChatGPT.Batch8.Group3
