import JuliaLean.DictsCov.AbsModel

/-!
# Properties of the generic `AbstractDict` methods

Every property holds for every concrete dictionary type whose interface
behaves like a finite map (`DictOps.Lawful`) under a lawful key comparison.
-/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

/-- `merge!(d, others...)` on lookups: each pair of each other dictionary, in
order, is stored. -/
def gmerge {K V : Type} (o : KeyOps K) (g : K → Option V) (others : List (Other K V)) : K → Option V :=
  others.foldl (fun g oth => oth.pairs.foldl (fun g kv => gset o g kv.1 kv.2) g) g

/-- `mergewith!(combine, d, others...)` on lookups: a present key gets
`combine(old, new)`. -/
def gmergewith {K V : Type} (o : KeyOps K) (combine : V → V → V) (g : K → Option V)
    (others : List (Other K V)) : K → Option V :=
  others.foldl (fun g oth => oth.pairs.foldl (fun g kv =>
    gset o g kv.1 (match g kv.1 with | some w => combine w kv.2 | none => kv.2)) g) g

/-- Membership and lookup: `haskey(d, k)` and `k in keys(d)` test for a stored
key `isequal` to `k` (`haskey` docstring `base/dict.jl:534-551`), `(k => v) in d`
compares the stored value with `valcmp`, `in` of a non-`Pair` throws the
documented error, `d[k]` returns the stored value or throws `KeyError`
(`KeyError` docstring `base/abstractdict.jl:5-9`), and `KeyTypeError` builds
`TypeError(:var"dict key", K, key)`. -/
def AbsLookupSpec : Prop :=
  ∀ (T D K V : Type) (o : KeyOps K) (ops : DictOps T D K V), ops.Lawful o →
  ∀ (d : D) (k : K),
    haskeyAD ops d k = (gOf o (ops.pairs d) k).isSome ∧
    inKeySet ops d k = (gOf o (ops.pairs d) k).isSome ∧
    (∀ (valcmp : V → V → Bool) (v : V), inPairAD ops valcmp d (k, v) =
      match gOf o (ops.pairs d) k with | some w => valcmp w v | none => false) ∧
    inNotPairAD ops d = .error (.errorException notPairMsg) ∧
    getindexAD ops d k = (match gOf o (ops.pairs d) k with
      | some v => .ok v | none => .error .keyError) ∧
    (∀ (A : Type) (tuple : A → A → List A → K) (k1 k2 : A) (ks : List A),
      getindexTup ops tuple d k1 k2 ks = getindexAD ops d (tuple k1 k2 ks) ∧
      ∀ v, setindexTup ops tuple d v k1 k2 ks = ops.setindex d v (tuple k1 k2 ks)) ∧
    (∀ (t : T) (A : Type) (key : A), keyTypeErrorV t key = ⟨"dict key", t, key⟩)

/-- `keys(d)`/`values(d)`/`pairs(d)` iterate the keys, values and pairs of `d`
in the same order (`keys` docstring `base/abstractdict.jl:86-91`, `values`
docstring `base/abstractdict.jl:112-131`), have the length and emptiness of
`d`, `copy(keys(d))` is the set of keys, `show` prints the iterated elements,
and `summary` prints the entry count (`base/abstractdict.jl:35-58`). -/
def AbsIterSpec : Prop :=
  ∀ (T D K V : Type) (o : KeyOps K) (ops : DictOps T D K V), o.Lawful → ops.Lawful o →
  ∀ d : D,
    iterPartAll ops .keys d = (ops.pairs d).map Prod.fst ∧
    iterPartAll ops .vals d = (ops.pairs d).map Prod.snd ∧
    (∀ (S : Type) (p : Part) (kv : K × V) (s : S),
      iterPartStep p (some (kv, s)) = some (p.pick kv, s) ∧ iterPartStep (K := K) (V := V) (S := S) p none = none) ∧
    (∀ p, lengthIter ops p d = (ops.pairs d).length) ∧
    (∀ (isempty : D → Bool) p, isemptyIter isempty p d = isempty d) ∧
    pairsGen (iterPartAll ops .keys d) (iterPartAll ops .vals d) = ops.pairs d ∧
    pairsAD ops d = ops.pairs d ∧
    copyKeySet o ops d = (ops.pairs d).map Prod.fst ∧
    (∀ (showVector : {α : Type} → List α → String) p,
      showIter ops showVector p d = showVector (iterPartAll ops p d)) ∧
    (∀ showarg : D → String, summaryAD ops showarg d =
      showarg d ++ (if ops.hasLength d then
        " with " ++ toString (ops.pairs d).length ++
          (if (ops.pairs d).length == 1 then " entry" else " entries")
        else "(...)")) ∧
    (∀ (showarg : D → String) (name : String),
      summaryIter ops showarg name d = name ++ " for a " ++ summaryAD ops showarg d)

/-- The type functions: `eltype` of `AbstractDict{K,V}` is `Pair{K,V}` (with
unbound parameters left unbound), of `ValueIterator` is `V`, and `keytype`/
`valtype` are the parameters (docstrings `base/abstractdict.jl:299-323`). -/
def AbsTypeSpec : Prop :=
  ∀ (T D K V : Type) (ops : DictOps T D K V) (k v : T) (d : D),
    eltypeAD (some k) (some v) = .kv k v ∧ eltypeAD (some k) none = .k k ∧
    eltypeAD none (some v) = .v v ∧ eltypeAD (T := T) none none = .any ∧
    eltypeValueIter (some k) (some v) = .ok v ∧
    (∀ K' V' : Option T, (K' = none ∨ V' = none) → eltypeValueIter K' V' = .error (.methodError "_tt2")) ∧
    keytypeAD ops d = (ops.typeOf d).K ∧ valtypeAD ops d = (ops.typeOf d).V

/-- `empty(d)` has no pairs and the type parameters of `d` (`empty` docstring
`base/abstractdict.jl:183-193`), `copy(d)` has the pairs of `d`, `copy!(dst, src)`
makes `dst` hold the pairs of `src`, `merge!` stores the pairs of the other
dictionaries in order, `mergewith!` combines the values of present keys
(docstrings `base/abstractdict.jl:203-282`), `push!` is `setindex!`, and the
`sizehint!`/`convert` fallbacks return their argument. -/
def AbsCopyMergeSpec : Prop :=
  ∀ (T D K V : Type) (o : KeyOps K) (ops : DictOps T D K V), o.Lawful → ops.Lawful o →
  ∀ d : D,
    (ops.get (emptyAD ops d) = (fun _ => none) ∧
      (ops.typeOf (emptyAD ops d)).K = (ops.typeOf d).K ∧ (ops.typeOf (emptyAD ops d)).V = (ops.typeOf d).V) ∧
    (∀ V' : T, ops.get (emptyADV ops d V') = (fun _ => none) ∧
      (ops.typeOf (emptyADV ops d V')).K = (ops.typeOf d).K ∧ (ops.typeOf (emptyADV ops d V')).V = V') ∧
    (∃ d', copyAD ops d = .ok d' ∧ ops.get d' = ops.get d) ∧
    (∀ src, copyBangAD ops true d src = .ok d ∧
      ∃ d', copyBangAD ops false d src = .ok d' ∧ ops.get d' = ops.get src) ∧
    (∀ others, ∃ d', mergeBang ops d others = .ok d' ∧ ops.get d' = gmerge o (ops.get d) others ∧
      ops.typeOf d' = ops.typeOf d) ∧
    (∀ (combine : V → V → V) others,
      ∃ d', mergewithBang ops combine d others = .ok d' ∧
        ops.get d' = gmergewith o combine (ops.get d) others ∧
      mergewithCurried ops combine d others = mergewithBang ops combine d others ∧
      mergeBangCombine ops combine d others = mergewithBang ops combine d others) ∧
    (∀ p : K × V, pushAD ops d p = ops.setindex d p.2 p.1) ∧
    (∀ n, sizehintAD d n = d) ∧ convertSame d = d ∧
    (∀ (E : Type) (dops : DictOps T E K V) (mk : D → GR E) (h : E), mk d = .ok h →
      convertAD ops dops mk d = (if dops.length h = ops.length d then .ok h
        else .error (.errorException "key collision during dictionary conversion")))

/-- `merge`/`mergewith` copy `d` into a `Dict` with the promoted parameters
and merge the others into it (docstrings `base/abstractdict.jl:327-403`), for a
`d` compared like the `Dict` (`dictOf K V ps` builds the `Dict` of `ps`). -/
def AbsMergeSpec : Prop :=
  ∀ (T D E K V : Type) (o : KeyOps K) (ops : DictOps T D K V) (dops : DictOps T E K V),
    o.Lawful → ops.Lawful o → dops.Lawful o →
  ∀ (promote : T → T → T) (dictOf : T → T → List (K × V) → GR E),
    (∀ K' V' ps, ps.Pairwise (fun a b => o.eq a.1 b.1 = false) →
      ∃ t, dictOf K' V' ps = .ok t ∧ dops.get t = gOf o ps) →
  ∀ (d : D) (others : List (DictTy T × Other K V)) (combine : V → V → V),
    (∃ t, mergeAD ops dops promote dictOf d others = .ok t ∧
      dops.get t = gmerge o (ops.get d) (others.map Prod.snd)) ∧
    (∃ t, mergewithAD ops dops promote dictOf combine d others = .ok t ∧
      dops.get t = gmergewith o combine (ops.get d) (others.map Prod.snd)) ∧
    mergewithCurriedAD ops dops promote dictOf combine d others =
      mergewithAD ops dops promote dictOf combine d others ∧
    (∀ (K0 : T) (ds : List (DictTy T)),
      promoteK promote K0 ds = ds.foldl (fun K t => promote K t.K) K0 ∧
      promoteV promote K0 ds = ds.foldl (fun V t => promote V t.V) K0)

/-- `filter!(f, d)`, `filter_in_one_pass!(f, d)` and `filter(f, d)` keep exactly
the pairs for which `f` is true (`filter!` docstring `base/abstractdict.jl:419-438`,
`filter` docstring `base/abstractdict.jl:461-478`), and `map!(f, values(d))`
replaces each value `v` by `f(v)` (docstring `base/abstractdict.jl:650-672`). -/
def AbsFilterMapSpec : Prop :=
  ∀ (T D K V : Type) (o : KeyOps K) (ops : DictOps T D K V), o.Lawful → ops.Lawful o →
  ∀ (d : D) (f : K × V → Bool),
    (∃ d', filterBangAD ops f d = .ok d' ∧ ops.get d' = gOf o ((ops.pairs d).filter f)) ∧
    (∃ d', filterInOnePass ops f d = .ok d' ∧ ops.get d' = gOf o ((ops.pairs d).filter f)) ∧
    (∃ d', filterAD ops f d = .ok d' ∧ ops.get d' = gOf o ((ops.pairs d).filter f) ∧
      (ops.typeOf d').K = (ops.typeOf d).K ∧ (ops.typeOf d').V = (ops.typeOf d).V) ∧
    (∀ g : V → V, ∃ d', mapValuesAD ops g d = .ok d' ∧
      ops.get d' = fun q => (ops.get d q).map g)

/-- `get!(f, d, key)` converts the key, returns a stored value without calling
`f`, or stores and returns `convert(V, f())` (`get!` docstrings
`base/dict.jl:416-442`); `get!(d, key, default)` is `get!(() -> default, d, key)`. -/
def AbsGetBangSpec : Prop :=
  ∀ (T D K V Q W : Type) (o : KeyOps K) (ops : DictOps T D K V) (c : Conv Q K) (cv : VConv W V),
    o.Lawful → ops.Lawful o →
  ∀ (d : D) (key0 : Q) (default : Unit → GR W),
    (match c.convert key0 with
     | .error e => getBangFAD ops c cv default d key0 = .error (.dict e)
     | .ok key => match ops.get d key with
       | some v => getBangFAD ops c cv default d key0 = .ok (v, d)
       | none => match default () with
         | .error e => getBangFAD ops c cv default d key0 = .error e
         | .ok w => match cv.convert w with
           | .error e => getBangFAD ops c cv default d key0 = .error (.dict e)
           | .ok v => ∃ d', getBangFAD ops c cv default d key0 = .ok (v, d') ∧
               ops.get d' = gset o (ops.get d) key v) ∧
    (∀ w : W, getBangAD ops c cv d key0 w = getBangFAD ops c cv (fun _ => .ok w) d key0)

/-- `grow_to!` (behind `Dict(kv)` for iterators of unknown element type)
stores every pair of the iterator in order into an empty `dest`, widening the
type when needed, and throws the documented `ArgumentError` for a non-iterable
argument or an element that is not a 2-element iterable (`Dict` docstring
`base/dict.jl:31-64`); `dict_with_eltype` dispatches on the element type. -/
def AbsGrowSpec : Prop :=
  ∀ (T D X : Type) (o : KeyOps X) (ty : TyOps T X) (ops : DictOps T D X X), o.Lawful → ops.Lawful o →
  ∀ dest : D, ops.get dest = (fun _ => none) →
    (∀ kvs : List (X × X), ∃ d', growTo ty ops dest (some (kvs.map fun p => some [p.1, p.2])) = .ok d' ∧
      ops.get d' = kvs.foldl (fun g p => gset o g p.1 p.2) (fun _ => none)) ∧
    growTo ty ops dest none = .error (.argumentError dictKVMsg) ∧
    (∀ (pre : List (X × X)) (bad : Option (List X)) (post : List (Option (List X))),
      (∀ k v, bad ≠ some [k, v]) →
      growTo ty ops dest (some (pre.map (fun p => some [p.1, p.2]) ++ bad :: post)) =
        .error (.argumentError dictKVMsg)) ∧
    (∀ (DT : T → T → Option (List (Option (List X))) → GR D) (DT0 : T → T → D) (anyT : T)
        (isPair pairLike : T → Option (T × T)) (et K V : T) (kv : Option (List (Option (List X)))),
      dictWithEltypeTP DT kv K V = DT K V kv ∧
      dictWithEltypeEmpty DT0 anyT isPair et =
        (match isPair et with | some (k, v) => DT0 k v | none => DT0 anyT anyT) ∧
      dictWithEltypeGrow ty ops DT0 anyT isPair et kv = growTo ty ops (dictWithEltypeEmpty DT0 anyT isPair et) kv ∧
      dictWithEltypeGen ty ops DT DT0 anyT isPair pairLike et kv =
        (match pairLike et with
         | some (k, v) => DT k v kv
         | none => growTo ty ops (dictWithEltypeEmpty DT0 anyT isPair et) kv))

end JuliaLean.DictsCov
