import JuliaLean.DictsCov.DictModel

/-!
# Properties of the `Dict` methods of `base/dict.jl`

Every property holds for every hash and `isequal` satisfying the `Dict`
contract (`KeyOps.Lawful`), over every table reachable from `Dict()` by a
small call sequence (`Reach`), with keys of any type consistent with `hash`
and `isequal` (`QLawful`).
-/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

/-- The constructors build the reference map of their pairs (`Dict` docstring,
`base/dict.jl:31-64`); `copy` keeps the contents; the inner constructor stores
its arguments. -/
def DictConstructSpec : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
    Agrees o (dictAnyNew : Table K V) [] ∧ Agrees o (dictEmptyTuple () : Table K V) [] ∧
    (∀ (t : Table K V) m, Reach o t m → Agrees o (dictCopyOf t) m) ∧
    (∀ (size : Nat) (slots : Nat → Nat) (keys : Nat → Option K) (vals : Nat → Option V)
        (ndel count : Nat) (age : JInt .u64) (idxfloor maxprobe popcursor : Nat),
      dictRaw size slots keys vals ndel count age idxfloor maxprobe popcursor =
        { size := size, slots := slots, keys := keys, vals := vals, ndel := ndel, count := count,
          age := age, idxfloor := idxfloor, maxprobe := maxprobe, popcursor := popcursor }) ∧
    (∀ (kv : List (K × V)) (hasLen : Bool), kv.length ≤ 2 ^ 30 →
      ∃ t, dictKV o hasLen kv = .ok t ∧ Agrees o t (rbuild o kv)) ∧
    (∀ p : K × V, ∃ t, dictPair o p = .ok t ∧ Agrees o t [p]) ∧
    (∀ ps : List (K × V), ps.length ≤ 2 ^ 30 →
      ∃ t, dictPairs o ps = .ok t ∧ Agrees o t (rbuild o ps)) ∧
    (∀ ps : List (K × V), ps.length ≤ 2 ^ 30 →
      ∃ t, dictOfTypedPairs o ps = .ok t ∧ Agrees o t (rbuild o ps))

/-- Slot bytes and the home slot: `_shorthash7` is a filled byte holding the top
seven hash bits, `hashindex` is the hash modulo the table size plus one, and
the three slot tests classify the bytes `0x00`, `0x7f`, `0x80-0xff`
(`base/dict.jl:66,123-137`). -/
def DictSlotSpec : Prop :=
  (∀ h : JInt .u64, isFilledB (shorthash7 h) = true ∧ shorthash7 h = 128 + h.val.toNat / 2 ^ 57) ∧
  (∀ (h : JInt .u64) (p : Nat), 4 ≤ p → p ≤ 62 →
    (hashindex h (2 ^ p)).1 = h.val.toNat % 2 ^ p + 1 ∧ (hashindex h (2 ^ p)).2 = shorthash7 h ∧
    1 ≤ (hashindex h (2 ^ p)).1 ∧ (hashindex h (2 ^ p)).1 ≤ 2 ^ p) ∧
  (∀ b, b < 256 → (isEmptyB b = true ↔ b = 0) ∧ (isMissingB b = true ↔ b = 127) ∧
    (isFilledB b = true ↔ 128 ≤ b))

/-- `ht_keyindex` finds the slot of the stored key matching a key of any type,
or returns `-1`; `ht_keyindex2_shorthash!`/`ht_keyindex2!` return the slot of
a present key or a free slot on its probe sequence, and `_setindex!` there
stores a new key (`base/dict.jl:241-345`). -/
def DictKeyindexSpec : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m →
    (∀ (Q : Type) (c : Conv Q K), QLawful o c → ∀ q : Q,
      match rfindQ c m q with
      | some e => ∃ i : Nat, htKeyindex t (c.hash q) (c.iseq q) = .ok (i : Int) ∧ 1 ≤ i ∧
          i ≤ t.size ∧ ent t i = some e
      | none => htKeyindex t (c.hash q) (c.iseq q) = .ok (-1)) ∧
    (∀ q : K, ∃ idx t' n, keyindex2 o t (o.hash q) (o.eq q) = .ok (idx, shorthash7 (o.hash q), t') ∧
      keyindex2Bang o t q = .ok (idx, t') ∧ K2Out o t q idx t' n) ∧
    (∀ (q : K) (v : V), rfind o m q = none →
      ∃ idx t1 t', keyindex2Bang o t q = .ok (idx, t1) ∧ idx < 0 ∧
        setindexAtDefault o t1 v q (-idx).toNat = .ok t' ∧ Agrees o t' (rset o m q v))

/-- `setindex!` converts the value to `V` (`base/dict.jl:359-372`), the
`Dict{K,Any}` method stores it as is (`base/dict.jl:374-387`), and a key of
another type is converted and must stay `isequal` (`base/dict.jl:347-357`). -/
def DictSetindexSpec : Prop :=
  ∀ (K V Q W : Type) (o : KeyOps K) (c : Conv Q K) (cv : VConv W V), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m →
    (∀ (v0 : W) (key : K), match convV cv v0 with
      | .ok v => ∃ t', setindexV o cv t v0 key = .ok t' ∧ Agrees o t' (rset o m key v)
      | .error e => setindexV o cv t v0 key = .error e) ∧
    (∀ (v : V) (key : K), ∃ t', setindexAny o t v key = .ok t' ∧ Agrees o t' (rset o m key v)) ∧
    (∀ (v0 : W) (key0 : Q), match convKey c key0 with
      | .ok key => setindexConvV o c cv t v0 key0 = setindexV o cv t v0 key ∧
          (c.isa key0 = none → c.convert key0 = .ok key ∧ c.iseq key0 key = true)
      | .error e => setindexConvV o c cv t v0 key0 = .error e ∧ c.isa key0 = none ∧
          (c.convert key0 = .error e ∨
            (e = .keyTypeError ∧ ∃ k, c.convert key0 = .ok k ∧ c.iseq key0 k = false)))

/-- `get!(default, h, key)` returns the stored value without calling `default`,
or stores and returns `convert(V, default())`; a key of another type goes
through the key conversion of `setindex!` (`get!` docstring
`base/dict.jl:416-442`, `base/dict.jl:445-478`). -/
def DictGetBangSpec : Prop :=
  ∀ (K V Q W : Type) (o : KeyOps K) (c : Conv Q K) (cv : VConv W V), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m →
    (∀ (key : K) (w : W), match rfind o m key with
      | some e => ∃ t', getBangV o cv t key (fun t => pure (w, t)) = .ok (e.2, t') ∧ Agrees o t' m
      | none => match convV cv w with
        | .ok v => ∃ t', getBangV o cv t key (fun t => pure (w, t)) = .ok (v, t') ∧
            Agrees o t' (rset o m key v)
        | .error e => getBangV o cv t key (fun t => pure (w, t)) = .error e) ∧
    (∀ (key0 : Q) (default : Table K V → DR (W × Table K V)), match convKey c key0 with
      | .ok key => getBangConv o c cv t key0 default = getBangV o cv t key default
      | .error e => getBangConv o c cv t key0 default = .error e)

/-- Lookups with a key of any type: `getindex`, `get`, `get(f, ...)`, `haskey`,
`in(key, keys(d))` and `getkey` agree with the reference map (docstrings
`base/dict.jl:485-575`; `KeyError` docstring `base/abstractdict.jl:5-9`). -/
def DictLookupSpec : Prop :=
  ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → MaxValuesOK o → QLawful o c →
  ∀ (t : Table K V) m, Reach o t m → ∀ (q : Q) (dflt : V) (f : Unit → DR V) (kd : K),
    getindexQ c t q = (match rfindQ c m q with | some e => .ok e.2 | none => .error .keyError) ∧
    getQ c t q dflt = .ok (match rfindQ c m q with | some e => e.2 | none => dflt) ∧
    getFQ c t q f = (match rfindQ c m q with | some e => .ok e.2 | none => f ()) ∧
    haskeyQ c t q = .ok (rfindQ c m q).isSome ∧
    inKeySetQ c t q = .ok (rfindQ c m q).isSome ∧
    getkeyQ c t q kd = .ok (match rfindQ c m q with | some e => e.1 | none => kd)

/-- `pop!(h, key)` returns the stored value and deletes the stored key, or throws
`KeyError`; `pop!(h, key, default)` returns `default` instead; `_delete!` and
`_pop!` remove exactly the pair of their slot (`pop!` docstring
`base/dict.jl:591-612`, `base/dict.jl:580-656`). -/
def DictPopSpec : Prop :=
  ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → MaxValuesOK o → QLawful o c →
  ∀ (t : Table K V) m, Reach o t m →
    (∀ (q : Q) (dflt : V),
      (match rfindQ c m q with
       | some e => ∃ t', popQ c t q = .ok (e.2, t') ∧ Agrees o t' (rdel o m e.1)
       | none => popQ c t q = .error .keyError) ∧
      (match rfindQ c m q with
       | some e => ∃ t', popDefaultQ c t q dflt = .ok (e.2, t') ∧ Agrees o t' (rdel o m e.1)
       | none => popDefaultQ c t q dflt = .ok (dflt, t)) ∧
      (match rfindQ c m q with
       | some e => ∃ t', deleteQ c t q = .ok t' ∧ Agrees o t' (rdel o m e.1)
       | none => deleteQ c t q = .ok t)) ∧
    (∀ (i : Nat) (e : K × V), 1 ≤ i → i ≤ t.size → ent t i = some e →
      Agrees o (deleteAt t i) (rdel o m e.1) ∧ popAt t i = .ok (e.2, deleteAt t i))

/-- Iteration: `skip_deleted` returns the first filled slot at or after `i`
(or 0), `skip_deleted_floor!` caches it in `idxfloor`, the iteration protocol
(`_iterate_dict`, `iterate`) yields each stored pair once, `keys`/`values`
iterate in the same order (`keys` docstring `base/abstractdict.jl:86-91`),
`isempty` tests for no pairs and `Iterators.only` returns the single pair
(`base/dict.jl:689-723`). -/
def DictIterSpec : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m →
    (∀ i, 1 ≤ i →
      (skipDeleted t i = 0 ∧ ∀ p, i ≤ p → p ≤ t.size → isFilledB (t.slots p) = false) ∨
      (i ≤ skipDeleted t i ∧ skipDeleted t i ≤ t.size ∧ isFilledB (t.slots (skipDeleted t i)) = true ∧
        ∀ p, i ≤ p → p < skipDeleted t i → isFilledB (t.slots p) = false)) ∧
    ((skipDeletedFloor t).1 = skipDeleted t t.idxfloor ∧
      Agrees o (skipDeletedFloor t).2 m) ∧
    (∃ xs, collectDict t = .ok xs ∧ iterList t = .ok xs ∧ List.Perm xs m) ∧
    (∃ xs, collectDict t = .ok xs ∧ collectPart t .keys = .ok (xs.map Prod.fst) ∧
      collectPart t .vals = .ok (xs.map Prod.snd)) ∧
    (isemptyDict t = true ↔ m = []) ∧
    (match m with
     | [e] => onlyDict t = .ok e
     | _ => onlyDict t = .error .argumentError)

/-- `map!(f, values(d))` replaces every value `v` by `f(v)` (docstring
`base/abstractdict.jl:650-660`), and `reduce(merge, items)` is the left fold of
`merge` (`base/dict.jl:735-739`). -/
def DictMapReduceSpec : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
    (∀ (t : Table K V) m, Reach o t m → ∀ f : V → V,
      Agrees o (mapValues t f) (m.map fun e => (e.1, f e.2))) ∧
    (∀ items : List (Table K V × RMap K V), (∀ x ∈ items, Reach o x.1 x.2) →
      (items.map fun x => x.2.length).sum ≤ 2 ^ 30 →
      match items with
      | [] => reduceMerge o (items.map Prod.fst) = .error .argumentError
      | _ => ∃ t, reduceMerge o (items.map Prod.fst) = .ok t ∧
          Agrees o t (items.foldl (fun M x => x.2.foldl (fun M kv => rset o M kv.1 kv.2) M) []))

end JuliaLean.DictsCov
