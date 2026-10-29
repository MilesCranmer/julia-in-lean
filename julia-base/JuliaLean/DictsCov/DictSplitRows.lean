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

def entries : List Entry := []

end JuliaLean.DictsCov.DictSplitRows
