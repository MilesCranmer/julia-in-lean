import JuliaLean.DictsCov.DictIterProofs
import JuliaLean.Registry.Types

/-!
# Per-method entries for the original DictsCov families

The first DictsCov pass grouped related source methods into conjunctions. This
file projects those proofs into one closed proposition per source method so a
coverage reviewer can inspect the exact mirrored function used by each row.
-/

namespace JuliaLean.DictsCov.DictSplitRows

open JuliaLean.Registry
open JuliaLean.Dicts
open JuliaLean.DictsCov

def Property77 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  Agrees o (dictAnyNew : Table K V) []
theorem property77 : Property77 := by
  intro K V o hl hm; exact (dictConstructSpec_proven K V o hl hm).1

def Property83 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → Agrees o (dictCopyOf t) m
theorem property83 : Property83 := by
  intro K V o hl hm; exact (dictConstructSpec_proven K V o hl hm).2.2.1

def Property87 : Prop := ∀ (K V : Type) (size : Nat) (slots : Nat → Nat)
    (keys : Nat → Option K) (vals : Nat → Option V) (ndel count : Nat)
    (age : JuliaLean.JInt .u64) (idxfloor maxprobe popcursor : Nat),
  dictRaw size slots keys vals ndel count age idxfloor maxprobe popcursor =
    { size := size, slots := slots, keys := keys, vals := vals, ndel := ndel,
      count := count, age := age, idxfloor := idxfloor,
      maxprobe := maxprobe, popcursor := popcursor }
theorem property87 : Property87 := by
  intro K V; exact fun size slots keys vals ndel count age idxfloor maxprobe popcursor => rfl

def Property91 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (pairs : List (K × V)) hasLength, pairs.length ≤ 2 ^ 30 →
    ∃ t, dictKV o hasLength pairs = .ok t ∧ Agrees o t (rbuild o pairs)
theorem property91 : Property91 := by
  intro K V o hl hm; exact (dictConstructSpec_proven K V o hl hm).2.2.2.2.1

def Property99 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ pair : K × V, ∃ t, dictPair o pair = .ok t ∧ Agrees o t [pair]
theorem property99 : Property99 := by
  intro K V o hl hm; exact (dictConstructSpec_proven K V o hl hm).2.2.2.2.2.1

def Property100 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ pairs : List (K × V), pairs.length ≤ 2 ^ 30 →
    ∃ t, dictPairs o pairs = .ok t ∧ Agrees o t (rbuild o pairs)
theorem property100 : Property100 := by
  intro K V o hl hm; exact (dictConstructSpec_proven K V o hl hm).2.2.2.2.2.2.1

def Property109 : Prop := Property77
theorem property109 : Property109 := property77

def Property110 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  Agrees o (dictEmptyTuple () : Table K V) []
theorem property110 : Property110 := by
  intro K V o hl hm; exact (dictConstructSpec_proven K V o hl hm).2.1

def Property111 : Prop := Property83
theorem property111 : Property111 := property83

def Property115 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ pairs : List (K × V), pairs.length ≤ 2 ^ 30 →
    ∃ t, dictOfTypedPairs o pairs = .ok t ∧ Agrees o t (rbuild o pairs)
theorem property115 : Property115 := by
  intro K V o hl hm; exact (dictConstructSpec_proven K V o hl hm).2.2.2.2.2.2.2

def Property123 : Prop := ∀ h : JuliaLean.JInt .u64,
  isFilledB (shorthash7 h) = true ∧ shorthash7 h = 128 + h.val.toNat / 2 ^ 57
theorem property123 : Property123 := dictSlotSpec_proven.1

def Property128 : Prop := ∀ (h : JuliaLean.JInt .u64) p, 4 ≤ p → p ≤ 62 →
  (hashindex h (2 ^ p)).1 = h.val.toNat % 2 ^ p + 1 ∧
  (hashindex h (2 ^ p)).2 = shorthash7 h ∧
  1 ≤ (hashindex h (2 ^ p)).1 ∧ (hashindex h (2 ^ p)).1 ≤ 2 ^ p
theorem property128 : Property128 := dictSlotSpec_proven.2.1

def Property135 : Prop := ∀ b, b < 256 → (isEmptyB b = true ↔ b = 0)
theorem property135 : Property135 := by
  intro b hb; exact (dictSlotSpec_proven.2.2 b hb).1

def Property136 : Prop := ∀ b, b < 256 → (isFilledB b = true ↔ 128 ≤ b)
theorem property136 : Property136 := by
  intro b hb; exact (dictSlotSpec_proven.2.2 b hb).2.2

def Property137 : Prop := ∀ b, b < 256 → (isMissingB b = true ↔ b = 127)
theorem property137 : Property137 := by
  intro b hb; exact (dictSlotSpec_proven.2.2 b hb).2.1

def Property241 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ (Q : Type) (c : Conv Q K),
    QLawful o c → ∀ q : Q,
      match rfindQ c m q with
      | some e => ∃ i : Nat, htKeyindex t (c.hash q) (c.iseq q) = .ok (i : Int) ∧
          1 ≤ i ∧ i ≤ t.size ∧ ent t i = some e
      | none => htKeyindex t (c.hash q) (c.iseq q) = .ok (-1)
theorem property241 : Property241 := by
  intro K V o hl hm t m hr; exact (dictKeyindexSpec_proven K V o hl hm t m hr).1

def Property270 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ q : K,
    ∃ idx t' n, keyindex2 o t (o.hash q) (o.eq q) = .ok (idx, shorthash7 (o.hash q), t') ∧
      K2Out o t q idx t' n
theorem property270 : Property270 := by
  intro K V o hl hm t m hr q
  obtain ⟨idx, t', n, h1, -, h3⟩ := (dictKeyindexSpec_proven K V o hl hm t m hr).2.1 q
  exact ⟨idx, t', n, h1, h3⟩

def Property325 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ q : K,
    ∃ idx t' n, keyindex2Bang o t q = .ok (idx, t') ∧ K2Out o t q idx t' n
theorem property325 : Property325 := by
  intro K V o hl hm t m hr q
  obtain ⟨idx, t', n, -, h2, h3⟩ := (dictKeyindexSpec_proven K V o hl hm t m hr).2.1 q
  exact ⟨idx, t', n, h2, h3⟩

def Property327 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ q v, rfind o m q = none →
    ∃ idx t1 t', keyindex2Bang o t q = .ok (idx, t1) ∧ idx < 0 ∧
      setindexAtDefault o t1 v q (-idx).toNat = .ok t' ∧ Agrees o t' (rset o m q v)
theorem property327 : Property327 := by
  intro K V o hl hm t m hr; exact (dictKeyindexSpec_proven K V o hl hm t m hr).2.2

def Property347 : Prop := ∀ (K V Q W : Type) (o : KeyOps K) (c : Conv Q K)
    (cv : VConv W V), o.Lawful → MaxValuesOK o → ∀ (t : Table K V) m,
    Reach o t m → ∀ v key,
      match convKey c key with
      | .ok converted => setindexConvV o c cv t v key = setindexV o cv t v converted ∧
          (c.isa key = none → c.convert key = .ok converted ∧ c.iseq key converted = true)
      | .error e => setindexConvV o c cv t v key = .error e ∧ c.isa key = none ∧
          (c.convert key = .error e ∨
            (e = .keyTypeError ∧ ∃ k, c.convert key = .ok k ∧ c.iseq key k = false))
theorem property347 : Property347 := by
  intro K V Q W o c cv hl hm t m hr
  exact (dictSetindexSpec_proven K V Q W o c cv hl hm t m hr).2.2

def Property359 : Prop := ∀ (K V W : Type) (o : KeyOps K) (cv : VConv W V),
  o.Lawful → MaxValuesOK o → ∀ (t : Table K V) m, Reach o t m → ∀ v key,
    match convV cv v with
    | .ok value => ∃ t', setindexV o cv t v key = .ok t' ∧ Agrees o t' (rset o m key value)
    | .error e => setindexV o cv t v key = .error e
theorem property359 : Property359 := by
  intro K V W o cv hl hm t m hr
  let c := Conv.self o
  exact (dictSetindexSpec_proven K V K W o c cv hl hm t m hr).1

def Property374 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ v key,
    ∃ t', setindexAny o t v key = .ok t' ∧ Agrees o t' (rset o m key v)
theorem property374 : Property374 := by
  intro K V o hl hm t m hr
  let cv : VConv V V := ⟨some, fun v => .ok v⟩
  exact (dictSetindexSpec_proven K V K V o (Conv.self o) cv hl hm t m hr).2.1

def Property445 : Prop := ∀ (K V Q W : Type) (o : KeyOps K) (c : Conv Q K)
    (cv : VConv W V), o.Lawful → MaxValuesOK o → ∀ (t : Table K V) m,
    Reach o t m → ∀ key default,
      match convKey c key with
      | .ok converted => getBangConv o c cv t key default = getBangV o cv t converted default
      | .error e => getBangConv o c cv t key default = .error e
theorem property445 : Property445 := by
  intro K V Q W o c cv hl hm t m hr
  exact (dictGetBangSpec_proven K V Q W o c cv hl hm t m hr).2

def Property457 : Prop := ∀ (K V W : Type) (o : KeyOps K) (cv : VConv W V),
  o.Lawful → MaxValuesOK o → ∀ (t : Table K V) m, Reach o t m → ∀ key w,
    match rfind o m key with
    | some e => ∃ t', getBangV o cv t key (fun t => .ok (w, t)) = .ok (e.2, t') ∧ Agrees o t' m
    | none => match convV cv w with
      | .ok v => ∃ t', getBangV o cv t key (fun t => .ok (w, t)) = .ok (v, t') ∧
          Agrees o t' (rset o m key v)
      | .error e => getBangV o cv t key (fun t => .ok (w, t)) = .error e
theorem property457 : Property457 := by
  intro K V W o cv hl hm t m hr
  exact (dictGetBangSpec_proven K V K W o (Conv.self o) cv hl hm t m hr).1

-- The six lookup properties need the reference map, so state them directly.
def Property480 : Prop := ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K),
  o.Lawful → MaxValuesOK o → QLawful o c → ∀ (t : Table K V) m, Reach o t m →
  ∀ q (d : V) (f : Unit → DR V) (kd : K),
  getindexQ c t q = match rfindQ c m q with | some e => .ok e.2 | none => .error .keyError
theorem property480 : Property480 := by
  intro K V Q o c hl hm hq t m hr q d f kd
  exact (dictLookupSpec_proven K V Q o c hl hm hq t m hr q d f kd).1

def Property507 : Prop := ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K),
  o.Lawful → MaxValuesOK o → QLawful o c → ∀ (t : Table K V) m, Reach o t m →
  ∀ q d (f : Unit → DR V) (kd : K),
  getQ c t q d = .ok (match rfindQ c m q with | some e => e.2 | none => d)
theorem property507 : Property507 := by
  intro K V Q o c hl hm hq t m hr q d f kd
  exact (dictLookupSpec_proven K V Q o c hl hm hq t m hr q d f kd).2.1

def Property529 : Prop := ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K),
  o.Lawful → MaxValuesOK o → QLawful o c → ∀ (t : Table K V) m, Reach o t m →
  ∀ q (d : V) f (kd : K),
  getFQ c t q f = match rfindQ c m q with | some e => .ok e.2 | none => f ()
theorem property529 : Property529 := by
  intro K V Q o c hl hm hq t m hr q d f kd
  exact (dictLookupSpec_proven K V Q o c hl hm hq t m hr q d f kd).2.2.1

def Property553 : Prop := ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K),
  o.Lawful → MaxValuesOK o → QLawful o c → ∀ (t : Table K V) m, Reach o t m →
  ∀ q (d : V) (f : Unit → DR V) (kd : K),
  haskeyQ c t q = .ok (rfindQ c m q).isSome
theorem property553 : Property553 := by
  intro K V Q o c hl hm hq t m hr q d f kd
  exact (dictLookupSpec_proven K V Q o c hl hm hq t m hr q d f kd).2.2.2.1

def Property554 : Prop := ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K),
  o.Lawful → MaxValuesOK o → QLawful o c → ∀ (t : Table K V) m, Reach o t m →
  ∀ q (d : V) (f : Unit → DR V) (kd : K),
  inKeySetQ c t q = .ok (rfindQ c m q).isSome
theorem property554 : Property554 := by
  intro K V Q o c hl hm hq t m hr q d f kd
  exact (dictLookupSpec_proven K V Q o c hl hm hq t m hr q d f kd).2.2.2.2.1

def Property575 : Prop := ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K),
  o.Lawful → MaxValuesOK o → QLawful o c → ∀ (t : Table K V) m, Reach o t m →
  ∀ q (dflt : V) (f : Unit → DR V) d,
  getkeyQ c t q d = .ok (match rfindQ c m q with | some e => e.1 | none => d)
theorem property575 : Property575 := by
  intro K V Q o c hl hm hq t m hr q dflt f d
  exact (dictLookupSpec_proven K V Q o c hl hm hq t m hr q dflt f d).2.2.2.2.2

def Property586 : Prop := ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K),
  o.Lawful → MaxValuesOK o → QLawful o c → ∀ (t : Table K V) m, Reach o t m → ∀ q,
    ∀ _default : V,
    match rfindQ c m q with
    | some e => ∃ t', popQ c t q = .ok (e.2, t') ∧ Agrees o t' (rdel o m e.1)
    | none => popQ c t q = .error .keyError
theorem property586 : Property586 := by
  intro K V Q o c hl hm hq t m hr q default
  exact ((dictPopSpec_proven K V Q o c hl hm hq t m hr).1 q default).1

def Property615 : Prop := ∀ (K V Q : Type) (o : KeyOps K) (c : Conv Q K),
  o.Lawful → MaxValuesOK o → QLawful o c → ∀ (t : Table K V) m, Reach o t m → ∀ q d,
    match rfindQ c m q with
    | some e => ∃ t', popDefaultQ c t q d = .ok (e.2, t') ∧ Agrees o t' (rdel o m e.1)
    | none => popDefaultQ c t q d = .ok (d, t)
theorem property615 : Property615 := by
  intro K V Q o c hl hm hq t m hr q d
  exact ((dictPopSpec_proven K V Q o c hl hm hq t m hr).1 q d).2.1

def Property580 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ i e, 1 ≤ i → i ≤ t.size → ent t i = some e →
    popAt t i = .ok (e.2, deleteAt t i)
theorem property580 : Property580 := by
  intro K V o hl hm t m hr i e h1 h2 he
  exact ((dictPopSpec_proven K V K o (Conv.self o) hl hm (qlawful_self hl) t m hr).2 i e h1 h2 he).2

def Property631 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ i e, 1 ≤ i → i ≤ t.size → ent t i = some e →
    Agrees o (deleteAt t i) (rdel o m e.1)
theorem property631 : Property631 := by
  intro K V o hl hm t m hr i e h1 h2 he
  exact ((dictPopSpec_proven K V K o (Conv.self o) hl hm (qlawful_self hl) t m hr).2 i e h1 h2 he).1

def Property689 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ i, 1 ≤ i →
    (skipDeleted t i = 0 ∧ ∀ p, i ≤ p → p ≤ t.size → isFilledB (t.slots p) = false) ∨
    (i ≤ skipDeleted t i ∧ skipDeleted t i ≤ t.size ∧
      isFilledB (t.slots (skipDeleted t i)) = true ∧
      ∀ p, i ≤ p → p < skipDeleted t i → isFilledB (t.slots p) = false)
theorem property689 : Property689 := by
  intro K V o hl hm t m hr; exact (dictIterSpec_proven K V o hl hm t m hr).1

def Property698 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m →
    (skipDeletedFloor t).1 = skipDeleted t t.idxfloor ∧ Agrees o (skipDeletedFloor t).2 m
theorem property698 : Property698 := by
  intro K V o hl hm t m hr; exact (dictIterSpec_proven K V o hl hm t m hr).2.1

def Property706 : Prop := ∀ (K V : Type) (t : Table K V) i,
  iterateDict t i = if i == 0 then .ok none else do
    let e ← entryAt t i
    return some (e, i + 1)
theorem property706 : Property706 := by unfold Property706; intros; rfl

def Property707 : Prop := ∀ (K V : Type) (t : Table K V),
  iterateFirst t = iterateDict t (skipDeleted t t.idxfloor)
theorem property707 : Property707 := by unfold Property707; intros; rfl

def Property710 : Prop := ∀ (K V : Type) (t : Table K V) i,
  iterateNext t i = iterateDict t (skipDeleted t i)
theorem property710 : Property710 := by unfold Property710; intros; rfl

def Property712 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → (isemptyDict t = true ↔ m = [])
theorem property712 : Property712 := by
  intro K V o hl hm t m hr; exact (dictIterSpec_proven K V o hl hm t m hr).2.2.2.2.1

def Property715 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m →
    match m with | [e] => onlyDict t = .ok e | _ => onlyDict t = .error .argumentError
theorem property715 : Property715 := by
  intro K V o hl hm t m hr; exact (dictIterSpec_proven K V o hl hm t m hr).2.2.2.2.2

def Property717 : Prop := ∀ (K V : Type) (t : Table K V) part i,
  iteratePart t part i = if i == 0 then .ok none else
    let i := skipDeleted t i
    if i == 0 then .ok none else do
      let x ← partAt t part i
      return some (x, i + 1)
theorem property717 : Property717 := by unfold Property717; intros; rfl

def Property735 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ items : List (Table K V × RMap K V), (∀ x ∈ items, Reach o x.1 x.2) →
    (items.map fun x => x.2.length).sum ≤ 2 ^ 30 →
    match items with
    | [] => reduceMerge o (items.map Prod.fst) = .error .argumentError
    | _ => ∃ t, reduceMerge o (items.map Prod.fst) = .ok t ∧
        Agrees o t (items.foldl (fun M x => x.2.foldl (fun M kv => rset o M kv.1 kv.2) M) [])
theorem property735 : Property735 := by
  intro K V o hl hm; exact (dictMapReduceSpec_proven K V o hl hm).2

def Property741 : Prop := ∀ (K V : Type) (o : KeyOps K), o.Lawful → MaxValuesOK o →
  ∀ (t : Table K V) m, Reach o t m → ∀ f,
    Agrees o (mapValues t f) (m.map fun e => (e.1, f e.2))
theorem property741 : Property741 := by
  intro K V o hl hm; exact (dictMapReduceSpec_proven K V o hl hm).1

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/dict.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry "dictscov-dict-l77" "Dict{K,V}() where V where K" "The typed empty constructor agrees with the empty reference map." "Dict docstring; base/dict.jl:77-82" ``Property77 ``property77,
  entry "dictscov-dict-l83" "Dict{K,V}(d::Dict{K,V}) where V where K" "The same-type copy constructor preserves all mappings." "copy invariant; base/dict.jl:83-86" ``Property83 ``property83,
  entry "dictscov-dict-l87" "Dict{K, V}(slots::Memory{UInt8}, keys::Memory{K}, vals::Memory{V}, ndel::Int, count::Int, age::UInt, idxfloor::Int, maxprobe::Int, popcursor::Int) where {K, V}" "The inner constructor stores every field." "invariant; base/dict.jl:87-89" ``Property87 ``property87,
  entry "dictscov-dict-l91" "Dict{K,V}(kv) where V where K" "The iterator constructor represents its pairs with later pairs winning." "Dict docstring; base/dict.jl:91-98" ``Property91 ``property91,
  entry "dictscov-dict-l99" "Dict{K,V}(p::Pair) where {K,V}" "The single-pair constructor represents that pair." "Dict docstring; base/dict.jl:99" ``Property99 ``property99,
  entry "dictscov-dict-l100" "Dict{K,V}(ps::Pair...) where V where K" "The pair constructor represents all pairs with later pairs winning." "Dict docstring; base/dict.jl:100-107" ``Property100 ``property100,
  entry "dictscov-dict-l109" "Dict()" "The untyped empty constructor is empty." "Dict docstring; base/dict.jl:109" ``Property109 ``property109,
  entry "dictscov-dict-l110" "Dict(kv::Tuple{})" "The empty-tuple constructor is empty." "Dict docstring; base/dict.jl:110" ``Property110 ``property110,
  entry "dictscov-dict-l111" "copy(d::Dict)" "copy preserves all mappings." "copy invariant; base/dict.jl:111" ``Property111 ``property111,
  entry "dictscov-dict-l115" "Dict(ps::Pair{K,V}...) where {K,V}" "Homogeneous pairs produce their later-wins reference map." "Dict docstring; base/dict.jl:115" ``Property115 ``property115,
  entry "dictscov-dict-l123" "_shorthash7(hsh::UInt)" "_shorthash7 stores the top seven hash bits with the filled bit set." "slot invariant; base/dict.jl:123" ``Property123 ``property123,
  entry "dictscov-dict-l128" "hashindex(key, sz::Integer)" "For power-of-two sizes, hashindex is hash modulo size plus one with the short hash." "hash-table invariant; base/dict.jl:128-133" ``Property128 ``property128,
  entry "dictscov-dict-l135" "isslotempty(h::Dict, i::Int)" "isslotempty recognizes only byte zero." "slot invariant; base/dict.jl:135" ``Property135 ``property135,
  entry "dictscov-dict-l136" "isslotfilled(h::Dict, i::Int)" "isslotfilled recognizes bytes with the high bit set." "slot invariant; base/dict.jl:136" ``Property136 ``property136,
  entry "dictscov-dict-l137" "isslotmissing(h::Dict, i::Int)" "isslotmissing recognizes the tombstone byte 0x7f." "slot invariant; base/dict.jl:137" ``Property137 ``property137,
  entry "dictscov-dict-l241" "ht_keyindex(h::Dict{K,V}, key) where V where K" "ht_keyindex returns the matching stored slot or -1." "lookup invariant; base/dict.jl:241-269" ``Property241 ``property241,
  entry "dictscov-dict-l270" "ht_keyindex2_shorthash!(h::Dict{K,V}, key) where V where K" "The short-hash insertion probe returns a valid present or free slot." "probe invariant; base/dict.jl:270-324" ``Property270 ``property270,
  entry "dictscov-dict-l325" "ht_keyindex2!(h::Dict, key)" "The insertion probe wrapper returns a valid present or free slot." "probe invariant; base/dict.jl:325" ``Property325 ``property325,
  entry "dictscov-dict-l327" "_setindex!(h::Dict, v, key, index, sh = _shorthash7(hash(key)))" "_setindex! at a returned free slot adds exactly the new mapping." "insertion invariant; base/dict.jl:327-345" ``Property327 ``property327,
  entry "dictscov-dict-l347" "setindex!(h::Dict{K,V}, v0, key0) where V where K" "Foreign-key insertion converts the key and rejects a conversion that is not isequal." "Dict key invariant; base/dict.jl:347-357" ``Property347 ``property347,
  entry "dictscov-dict-l359" "setindex!(h::Dict{K,V}, v0, key::K) where V where K" "Typed-key insertion converts the value and stores it." "Dict invariant; base/dict.jl:359-372" ``Property359 ``property359,
  entry "dictscov-dict-l374" "setindex!(h::Dict{K,Any}, v, key::K) where K" "Dict{K,Any} insertion stores the value without conversion." "Dict invariant; base/dict.jl:374-387" ``Property374 ``property374,
  entry "dictscov-dict-l445" "get!(default::Callable, h::Dict{K,V}, key0) where V where K" "Foreign-key get! follows the same key conversion as insertion." "get! docstring; base/dict.jl:445-455" ``Property445 ``property445,
  entry "dictscov-dict-l457" "get!(default::Callable, h::Dict{K,V}, key::K) where V where K" "Typed get! returns a present value or converts, stores, and returns the default." "get! docstring; base/dict.jl:457-478" ``Property457 ``property457,
  entry "dictscov-dict-l480" "getindex(h::Dict{K,V}, key) where V where K" "Indexing returns the stored value or KeyError." "KeyError docstring; base/dict.jl:480-505" ``Property480 ``property480,
  entry "dictscov-dict-l507" "get(h::Dict{K,V}, key, default) where V where K" "get returns the stored value or supplied default." "get invariant; base/dict.jl:507-527" ``Property507 ``property507,
  entry "dictscov-dict-l529" "get(default::Callable, h::Dict{K,V}, key) where V where K" "Callable get evaluates its default only when absent." "get invariant; base/dict.jl:529-551" ``Property529 ``property529,
  entry "dictscov-dict-l553" "haskey(h::Dict, key)" "haskey is true exactly for a matching stored key." "haskey invariant; base/dict.jl:553" ``Property553 ``property553,
  entry "dictscov-dict-l554" "in(key, v::KeySet{<:Any, <:Dict})" "KeySet membership is true exactly for a matching stored key." "keys invariant; base/dict.jl:554" ``Property554 ``property554,
  entry "dictscov-dict-l575" "getkey(h::Dict{K,V}, key, default) where V where K" "getkey returns the stored representative key or the supplied default." "getkey invariant; base/dict.jl:575-578" ``Property575 ``property575,
  entry "dictscov-dict-l580" "_pop!(h::Dict, index)" "_pop! returns the indexed value and deletes exactly that mapping." "pop! invariant; base/dict.jl:580-584" ``Property580 ``property580,
  entry "dictscov-dict-l586" "pop!(h::Dict, key)" "pop! returns and removes a present mapping or throws KeyError." "pop! docstring; base/dict.jl:586-589" ``Property586 ``property586,
  entry "dictscov-dict-l615" "pop!(h::Dict, key, default)" "Defaulted pop returns and removes a present value or returns default unchanged." "pop! docstring; base/dict.jl:615-618" ``Property615 ``property615,
  entry "dictscov-dict-l631" "_delete!(h::Dict{K,V}, index) where {K,V}" "_delete! removes exactly the mapping at its filled slot." "delete invariant; base/dict.jl:631-679" ``Property631 ``property631,
  entry "dictscov-dict-l689" "skip_deleted(h::Dict, i)" "skip_deleted finds the first filled slot at or after i or zero." "iteration invariant; base/dict.jl:689-696" ``Property689 ``property689,
  entry "dictscov-dict-l698" "skip_deleted_floor!(h::Dict)" "skip_deleted_floor! performs the scan and preserves mappings while caching a found floor." "iteration invariant; base/dict.jl:698-704" ``Property698 ``property698,
  entry "dictscov-dict-l706" "_iterate_dict(t::Dict{K,V}, i) where {K,V}" "_iterate_dict returns nothing at zero or the indexed pair and next state." "iteration invariant; base/dict.jl:706" ``Property706 ``property706,
  entry "dictscov-dict-l707" "iterate(t::Dict)" "Initial iteration scans from idxfloor and delegates to _iterate_dict." "iteration invariant; base/dict.jl:707-709" ``Property707 ``property707,
  entry "dictscov-dict-l710" "iterate(t::Dict, i)" "Stateful iteration scans from its state and delegates to _iterate_dict." "iteration invariant; base/dict.jl:710" ``Property710 ``property710,
  entry "dictscov-dict-l712" "isempty(t::Dict)" "isempty is true exactly when the reference map is empty." "iterator invariant; base/dict.jl:712" ``Property712 ``property712,
  entry "dictscov-dict-l715" "Iterators.only(t::Dict)" "only returns the sole pair and otherwise throws ArgumentError." "Iterators.only invariant; base/dict.jl:715" ``Property715 ``property715,
  entry "dictscov-dict-l717" "Base.iterate(v::T, i::Int = v.dict.idxfloor) where T <: Union{KeySet{<:Any, <:Dict}, ValueIterator{<:Dict}}" "Key and value iteration scans filled slots, projects the chosen component, and advances state." "keys docstring; base/dict.jl:717-723" ``Property717 ``property717,
  entry "dictscov-dict-l735" "reduce(::typeof(merge), items::Vector{<:Dict})" "reduce merge is the left fold of dictionary merge and errors for no items." "reduce invariant; base/dict.jl:735-739" ``Property735 ``property735,
  entry "dictscov-dict-l741" "map!(f, iter::ValueIterator{<:Dict})" "map! replaces every stored value with f(value)." "map! docstring; base/dict.jl:741-751" ``Property741 ``property741
]

end JuliaLean.DictsCov.DictSplitRows
