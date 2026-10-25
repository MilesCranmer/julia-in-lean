import JuliaLean.Core

/-!
# The `Dict` hash table, `base/dict.jl` (master `bbfa0ce4150`)

`Dict{K,V}` is an open-addressing table with linear probing. This file mirrors
its fields and every function that reads or writes them, branch by branch.

Modelling decisions:

* The `Memory` fields `slots`, `keys`, `vals` are functions on the 1-based
  index, with `size` their common length. A `#undef` (or `unsetindex!`) entry
  of `keys`/`vals` is `none`. Julia's `unsetindex!` is a no-op for isbits
  element types; the model clears the entry anyway, which is unobservable
  because the source only reads `keys[i]`/`vals[i]` of filled slots.
* A slot byte is a `Nat` below 256: `0x00` empty, `0x7f` deleted, `0x80 | tag`
  filled (`base/dict.jl:66`).
* The `Int` fields `ndel`, `count`, `idxfloor`, `maxprobe`, `popcursor` and all
  index arithmetic are `Nat`: they stay in `[0, 4·size]`, and a table of `size`
  slots occupies at least `size` bytes, so on any table that fits in memory the
  Int64 arithmetic of the source cannot wrap. The one place where user input
  enters this arithmetic, `sizehint!`, is modelled with wrapping `JInt .i64`.
  `age::UInt` is a wrapping `JInt .u64`.
* Allocation (`Memory{T}(undef, n)`) always succeeds; Julia throws
  `OutOfMemoryError` where the machine cannot provide the memory.
* The hash function and the key comparison `key === k || isequal(key, k)`
  are parameters (`KeyOps`), so every property is stated for every hash,
  including adversarial ones.
* A Julia loop that provably never exits is the outcome `.diverges`.
-/

namespace JuliaLean.Dicts

/-- Exceptions (and non-termination) of the modelled calls. -/
inductive DErr where
  /-- `KeyError(key)` -/
  | keyError
  /-- `TypeError(:var"dict key", K, key)` from `KeyTypeError`, `base/abstractdict.jl:15` -/
  | keyTypeError
  /-- `ArgumentError`, e.g. `pop!` of an empty `Dict` -/
  | argumentError
  /-- `UndefRefError` from reading a `#undef` key or value (never happens on a well-formed table) -/
  | undefRef
  /-- `throw(h)` in `ht_keyindex`, `base/dict.jl:246` (never happens on a well-formed table) -/
  | thrownDict
  /-- An error of a shared Julia primitive, e.g. `InexactError` from `convert` -/
  | jl (e : JlError)
  /-- The call never returns: a Julia loop runs forever -/
  | diverges
  deriving Repr, DecidableEq, Inhabited

abbrev DR (α : Type) := Except DErr α

/-- Hashing and comparison of keys of type `K`. -/
structure KeyOps (K : Type) where
  /-- `hash(key)::UInt` -/
  hash : K → JInt .u64
  /-- `key === k || isequal(key, k)` -/
  eq : K → K → Bool
  /-- `max_values(K)`, `base/abstractset.jl:92-103` (`typemax(Int)` for most types) -/
  maxValues : JInt .i64 := JInt.typemax .i64

/-- The `isequal`/`hash` contract of the `Dict` docstring (`base/dict.jl:35`,
`hash` docstring `base/hashing.jl:12-16`): `isequal` is an equivalence relation
and `isequal(x, y)` implies `hash(x) == hash(y)`. -/
structure KeyOps.Lawful {K : Type} (o : KeyOps K) : Prop where
  refl : ∀ a, o.eq a a = true
  symm : ∀ a b, o.eq a b = true → o.eq b a = true
  trans : ∀ a b c, o.eq a b = true → o.eq b c = true → o.eq a c = true
  hash_eq : ∀ a b, o.eq a b = true → o.hash a = o.hash b

/-- Pointwise update of a `Memory` modelled as a function: `m[i] = x`. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (x : α) : Nat → α :=
  fun j => if j = i then x else f j

/-- The fields of `mutable struct Dict{K,V}`, `base/dict.jl:65-90`. -/
structure Table (K V : Type) where
  size : Nat
  slots : Nat → Nat
  keys : Nat → Option K
  vals : Nat → Option V
  ndel : Nat
  count : Nat
  age : JInt .u64
  idxfloor : Nat
  maxprobe : Nat
  popcursor : Nat

variable {K V : Type}

/-- `Dict{K,V}()`, `base/dict.jl:77-82`: `n = 0`, `idxfloor = max(1, n)`. -/
def Table.empty : Table K V :=
  ⟨0, fun _ => 0, fun _ => none, fun _ => none, 0, 0, JInt.lit .u64 0, 1, 0, 1⟩

/-- `h.age += 1` on `age::UInt`. -/
def bump (a : JInt .u64) : JInt .u64 := a + JInt.lit .u64 1

/-- `isslotempty`, `base/dict.jl:135`. -/
def isEmptyB (b : Nat) : Bool := b == 0
/-- `isslotfilled`, `base/dict.jl:136`: `(h.slots[i] & 0x80) != 0`. -/
def isFilledB (b : Nat) : Bool := Nat.land b 0x80 != 0
/-- `isslotmissing`, `base/dict.jl:137`. -/
def isMissingB (b : Nat) : Bool := b == 0x7f

/-- `_shorthash7`, `base/dict.jl:123`: `(hsh >> 57) % UInt8 | 0x80`. -/
def shorthash7 (hsh : JInt .u64) : Nat := Nat.lor ((hsh.val.toNat >>> 57) % 256) 0x80

/-- `hashindex(key, sz)`, `base/dict.jl:128-133`, given `hsh = hash(key)`:
`((hsh % Int) & (sz-1)) + 1`. The two's-complement `&` of the reinterpreted
hash with the nonnegative mask is the `&` of the unsigned bit pattern. -/
def hashindex (hsh : JInt .u64) (sz : Nat) : Nat × Nat :=
  (Nat.land hsh.val.toNat (sz - 1) + 1, shorthash7 hsh)

/-- `(index & (sz-1)) + 1`, the probe step of `base/dict.jl:174,259,301,315,640`. -/
def nextIdx (sz index : Nat) : Nat := Nat.land index (sz - 1) + 1

/-- Bit pattern of an Int64 value `x` (`x % UInt64`), for `&` on negative Ints. -/
def bits64 (x : Int) : Nat := (x % (2 ^ 64 : Int)).toNat

/-- `((index - 2) & (sz-1)) + 1`, the backward step of `_delete!`, `base/dict.jl:645`. -/
def prevIdx (sz index : Nat) : Nat := Nat.land (bits64 ((index : Int) - 2)) (sz - 1) + 1

/-- `(index - index0) & (newsz-1)`, the probe length in `rehash!`, `base/dict.jl:176`. -/
def probeDist (newsz index index0 : Nat) : Nat :=
  Nat.land (bits64 ((index : Int) - index0)) (newsz - 1)

/-- `_tablesz(x)`, `base/abstractdict.jl:584`, for an `Int` that never wraps
(all internal callers): `x < 16 ? 16 : 1 << top_set_bit(x-1)`. -/
def tableszNat (x : Nat) : Nat := if x < 16 then 16 else 2 ^ (Nat.log2 (x - 1) + 1)

/-- `_tablesz(x::Int)`, `base/abstractdict.jl:584`, with Int64 wrapping of the shift
(`1 << 63 == typemin(Int)`). `top_set_bit(y) = log2(y) + 1` for `y > 0`. -/
def tableszI64 (x : JInt .i64) : JInt .i64 :=
  if x.val < 16 then JInt.lit .i64 16
  else JInt.wrap .i64 (2 ^ (Nat.log2 (x.val.toNat - 1) + 1))

/-! ## Lookup -/

/-- The loop of `ht_keyindex`, `base/dict.jl:250-261`, with `left` slots still
to examine (`maxprobe + 1 - iter`). `m k` is `key === k || isequal(key, k)`. -/
def keyindexLoop (t : Table K V) (sh : Nat) (m : K → Bool) : Nat → Nat → Int
  | 0, _ => -1
  | left + 1, index =>
    if isEmptyB (t.slots index) then -1
    else if sh == t.slots index && (match t.keys index with | some k => m k | none => false)
    then (index : Int)
    else keyindexLoop t sh m left (nextIdx t.size index)

/-- `ht_keyindex(h, key)`, `base/dict.jl:241-263`, given `hq = hash(key)`:
the index of the key, or `-1`. -/
def htKeyindex (t : Table K V) (hq : JInt .u64) (m : K → Bool) : DR Int :=
  if t.count == 0 then pure (-1) else
  let sz := t.size
  if ¬ t.maxprobe < sz then throw .thrownDict else
  let (index, sh) := hashindex hq sz
  pure (keyindexLoop t sh m (t.maxprobe + 1) index)

/-- Value at a filled index (`h.vals[index]`). -/
def valAt (t : Table K V) (index : Nat) : DR V :=
  match t.vals index with
  | some v => pure v
  | none => throw .undefRef

/-- `get(h, key, nothing)`-style lookup shared by `get`, `getindex`, `haskey`,
`base/dict.jl:480-510,553`: `some v` if the key is present. -/
def lookup (t : Table K V) (hq : JInt .u64) (m : K → Bool) : DR (Option V) := do
  let index ← htKeyindex t hq m
  if index < 0 then pure none else some <$> valAt t index.toNat

/-- `get(h, key, nothing)` for a key of type `K`. -/
def dictGet (o : KeyOps K) (t : Table K V) (key : K) : DR (Option V) := lookup t (o.hash key) (o.eq key)

/-- `haskey(h, key)`, `base/dict.jl:553`. -/
def haskey (o : KeyOps K) (t : Table K V) (key : K) : DR Bool := do
  let index ← htKeyindex t (o.hash key) (o.eq key)
  pure (index ≥ 0)

/-- `getindex(h, key)`, `base/dict.jl:480-483`. -/
def getindex (o : KeyOps K) (t : Table K V) (key : K) : DR V := do
  match ← dictGet o t key with
  | some v => pure v
  | none => throw .keyError

/-! ## Rehash -/

/-- `while slots[index] != 0; index = (index & (newsz-1)) + 1; end`,
`base/dict.jl:173-175`, with `left` steps allowed. After `newsz` steps the
probe has visited every slot of the power-of-two table and returns to its
start without finding an empty slot; the slots do not change inside the
loop, so the Julia loop never exits (`none`). -/
def rehashProbe (slots : Nat → Nat) (newsz : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | left + 1, index =>
    if slots index != 0 then rehashProbe slots newsz left (nextIdx newsz index) else some index

/-- Locals of the copy loop of `rehash!`, `base/dict.jl:159-165`. -/
structure RehashAcc (K V : Type) where
  slots : Nat → Nat
  keys : Nat → Option K
  vals : Nat → Option V
  count : Nat
  maxprobe : Nat

/-- One iteration `i` of the copy loop, `base/dict.jl:167-183`. -/
def rehashStep (o : KeyOps K) (newsz : Nat) (olds : Nat → Nat) (oldk : Nat → Option K)
    (oldv : Nat → Option V) (acc : RehashAcc K V) (i : Nat) : DR (RehashAcc K V) :=
  if isFilledB (olds i) then
    match oldk i, oldv i with
    | some k, some v =>
      let (index0, _) := hashindex (o.hash k) newsz
      match rehashProbe acc.slots newsz newsz index0 with
      | none => throw .diverges
      | some index =>
        let probe := probeDist newsz index index0
        pure { slots := upd acc.slots index (olds i), keys := upd acc.keys index (some k),
               vals := upd acc.vals index (some v), count := acc.count + 1,
               maxprobe := if probe > acc.maxprobe then probe else acc.maxprobe }
    | _, _ => throw .undefRef
  else pure acc

/-- `rehash!(h, newsz)`, `base/dict.jl:139-194`. The `@assert h.age == age0`
(`base/dict.jl:185`) holds: there are no concurrent writers. -/
def rehash (o : KeyOps K) (t : Table K V) (newsz0 : Nat) : DR (Table K V) := do
  let sz := t.size
  let newsz := tableszNat newsz0
  let t := { t with age := bump t.age, idxfloor := 1, popcursor := 1 }
  if t.count == 0 then
    pure { t with size := newsz, slots := fun _ => 0, keys := fun _ => none,
                  vals := fun _ => none, ndel := 0, maxprobe := 0 }
  else
    let acc ← (List.range sz).foldlM
      (fun acc i => rehashStep o newsz t.slots t.keys t.vals acc (i + 1))
      ({ slots := fun _ => 0, keys := fun _ => none, vals := fun _ => none,
         count := 0, maxprobe := 0 } : RehashAcc K V)
    pure { t with age := bump t.age, size := newsz, slots := acc.slots, keys := acc.keys,
                  vals := acc.vals, count := acc.count, ndel := 0, maxprobe := acc.maxprobe }

/-! ## Insertion -/

/-- Outcome of the first loop of `ht_keyindex2_shorthash!`. -/
inductive Probe1 where
  | found (idx : Int)
  | broke (iter index : Nat) (avail : Int)

/-- First loop of `ht_keyindex2_shorthash!`, `base/dict.jl:283-304`, with
`left = maxprobe + 1 - iter` iterations remaining. -/
def keyindex2Loop1 (t : Table K V) (sh : Nat) (m : K → Bool) (sz : Nat) :
    Nat → Nat → Nat → Int → Probe1
  | 0, iter, index, avail => .broke iter index avail
  | left + 1, iter, index, avail =>
    let b := t.slots index
    if isEmptyB b then .found (if avail < 0 then avail else -(index : Int))
    else
      let hit : Bool :=
        if isMissingB b then false
        else if b == sh then (match t.keys index with | some k => m k | none => false)
        else false
      let avail : Int := if isMissingB b ∧ avail == 0 then -(index : Int) else avail
      if hit then .found (index : Int)
      else
        let index := nextIdx sz index
        let iter := iter + 1
        if iter > t.maxprobe then .broke iter index avail
        else keyindex2Loop1 t sh m sz left iter index avail

/-- Second loop of `ht_keyindex2_shorthash!`, `base/dict.jl:310-317`: the first
non-filled slot at probe length `iter < maxallowed`, as `(iter, index)`. -/
def keyindex2Loop2 (t : Table K V) (sz maxallowed : Nat) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | left + 1, iter, index =>
    if iter < maxallowed then
      if ¬ isFilledB (t.slots index) then some (iter, index)
      else keyindex2Loop2 t sz maxallowed left (iter + 1) (nextIdx sz index)
    else none

/-- `ht_keyindex2_shorthash!(h, key)`, `base/dict.jl:270-322`, given `hq = hash(key)`.
Returns `(index, sh, h')`: `index > 0` where the key is stored, `-pos` where it
would be inserted. The tail call after `rehash!` (`base/dict.jl:319-321`) is
bounded by `fuel`: every rehash at least doubles `sz` and `maxallowed ≥ sz/64`,
so after `count + 4` rehashes the second loop always finds a slot and the
`.diverges` branch is unreachable for the `fuel = count + 8` used by callers. -/
def htKeyindex2 (o : KeyOps K) : Nat → Table K V → JInt .u64 → (K → Bool) →
    DR (Int × Nat × Table K V)
  | fuel, t, hq, m =>
    let sz := t.size
    if sz == 0 then do
      let t ← rehash o t 4
      let (index, sh) := hashindex hq t.size
      pure (-(index : Int), sh, t)
    else
      let (index, sh) := hashindex hq sz
      match keyindex2Loop1 t sh m sz (t.maxprobe + 1) 0 index 0 with
      | .found i => pure (i, sh, t)
      | .broke iter index avail =>
        if avail < 0 then pure (avail, sh, t) else
        let maxallowed := max 16 (sz >>> 6)
        match keyindex2Loop2 t sz maxallowed maxallowed iter index with
        | some (iter, index) => pure (-(index : Int), sh, { t with maxprobe := iter })
        | none =>
          match fuel with
          | 0 => throw .diverges
          | fuel + 1 => do
            let t ← rehash o t (if t.count > 64000 then sz * 2 else sz * 4)
            htKeyindex2 o fuel t hq m

/-- `ht_keyindex2_shorthash!` with the fuel used throughout. -/
def keyindex2 (o : KeyOps K) (t : Table K V) (hq : JInt .u64) (m : K → Bool) :
    DR (Int × Nat × Table K V) :=
  htKeyindex2 o (t.count + 8) t hq m

/-- `_setindex!(h, v, key, index, sh)`, `base/dict.jl:327-345`. -/
def setindexAt (o : KeyOps K) (t : Table K V) (v : V) (key : K) (index sh : Nat) :
    DR (Table K V) :=
  let t := { t with ndel := t.ndel - (if isMissingB (t.slots index) then 1 else 0) }
  let t := { t with slots := upd t.slots index sh, keys := upd t.keys index (some key),
                    vals := upd t.vals index (some v), count := t.count + 1, age := bump t.age }
  let t := if index < t.idxfloor then { t with idxfloor := index } else t
  let sz := t.size
  if (t.count + t.ndel) * 3 > sz * 2 then
    rehash o t (if t.count > 64000 then t.count * 2 else max (t.count * 4) 4)
  else pure t

/-- Overwrite of an existing key, `base/dict.jl:363-366`. -/
def overwriteAt (t : Table K V) (v : V) (key : K) (index : Nat) : Table K V :=
  { t with age := bump t.age, keys := upd t.keys index (some key), vals := upd t.vals index (some v) }

/-- `setindex!(h, v, key::K)`, `base/dict.jl:359-372`. -/
def setindex (o : KeyOps K) (t : Table K V) (v : V) (key : K) : DR (Table K V) := do
  let (index, sh, t) ← keyindex2 o t (o.hash key) (o.eq key)
  if index > 0 then pure (overwriteAt t v key index.toNat)
  else setindexAt o t v key (-index).toNat sh

/-- `get!(default, h, key::K)`, `base/dict.jl:457-478`. `default` is the call
`default()`, which may read and mutate `h`; it returns its value and the
updated table. -/
def getBang (o : KeyOps K) (t : Table K V) (key : K)
    (default : Table K V → DR (V × Table K V)) : DR (V × Table K V) := do
  let (index, sh, t) ← keyindex2 o t (o.hash key) (o.eq key)
  if index > 0 then
    let v ← valAt t index.toNat
    pure (v, t)
  else
    let age0 := t.age
    let (v, t) ← default t
    let (index, sh, t) ←
      if t.age.val != age0.val then keyindex2 o t (o.hash key) (o.eq key)
      else pure (index, sh, t)
    if index > 0 then pure (v, overwriteAt t v key index.toNat)
    else
      let t ← setindexAt o t v key (-index).toNat sh
      pure (v, t)

/-- `get!(h, key, default)`, `base/abstractdict.jl:560`: `get!(() -> default, h, key)`. -/
def getBangVal (o : KeyOps K) (t : Table K V) (key : K) (v : V) : DR (V × Table K V) :=
  getBang o t key (fun t => pure (v, t))

/-! ## Deletion -/

/-- The tombstone-clearing loop of `_delete!`, `base/dict.jl:642-647`, with
`left` iterations allowed. The loop stops at the latest a full turn later, at
the slot it emptied first, so `size + 1` iterations always suffice. -/
def deleteBack (sz : Nat) : Nat → (Nat → Nat) → Nat → Int → (Nat → Nat) × Int
  | 0, slots, _, ndel => (slots, ndel)
  | left + 1, slots, index, ndel =>
    let ndel := ndel - 1
    let slots := upd slots index 0
    let index := prevIdx sz index
    if isMissingB (slots index) then deleteBack sz left slots index ndel else (slots, ndel)

/-- `_delete!(h, index)`, `base/dict.jl:631-656`. -/
def deleteAt (t : Table K V) (index : Nat) : Table K V :=
  let sz := t.size
  let keys := upd t.keys index none
  let vals := upd t.vals index none
  let nextind := nextIdx sz index
  let (slots, ndel) : (Nat → Nat) × Int :=
    if isEmptyB (t.slots nextind) then deleteBack sz (sz + 1) t.slots index 1
    else (upd t.slots index 0x7f, 1)
  { t with keys := keys, vals := vals, slots := slots, ndel := ((t.ndel : Int) + ndel).toNat,
           count := t.count - 1, age := bump t.age }

/-- `delete!(h, key)`, `base/dict.jl:681-687`. -/
def dictDelete (o : KeyOps K) (t : Table K V) (key : K) : DR (Table K V) := do
  let index ← htKeyindex t (o.hash key) (o.eq key)
  if index > 0 then pure (deleteAt t index.toNat) else pure t

/-- `pop!(h, key)`, `base/dict.jl:580-589`. -/
def popKey (o : KeyOps K) (t : Table K V) (key : K) : DR (V × Table K V) := do
  let index ← htKeyindex t (o.hash key) (o.eq key)
  if index > 0 then
    let v ← valAt t index.toNat
    pure (v, deleteAt t index.toNat)
  else throw .keyError

/-- `pop!(h, key, default)`, `base/dict.jl:615-618`. -/
def popKeyDefault (o : KeyOps K) (t : Table K V) (key : K) (d : V) : DR (V × Table K V) := do
  let index ← htKeyindex t (o.hash key) (o.eq key)
  if index > 0 then
    let v ← valAt t index.toNat
    pure (v, deleteAt t index.toNat)
  else pure (d, t)

/-! ## Iteration -/

/-- The loop of `skip_deleted`, `base/dict.jl:689-697`, over `left` indices. -/
def skipDeletedLoop (t : Table K V) : Nat → Nat → Nat
  | 0, _ => 0
  | left + 1, i => if isFilledB (t.slots i) then i else skipDeletedLoop t left (i + 1)

/-- `skip_deleted(h, i)`: the first filled index in `i:length(h.slots)`, or 0. -/
def skipDeleted (t : Table K V) (i : Nat) : Nat := skipDeletedLoop t (t.size + 1 - i) i

/-- Key and value at a filled index. -/
def entryAt (t : Table K V) (i : Nat) : DR (K × V) :=
  match t.keys i, t.vals i with
  | some k, some v => pure (k, v)
  | _, _ => throw .undefRef

/-- The iteration protocol from state `i`, `base/dict.jl:706-710`: `left`
bounds the number of steps (each yield strictly increases the state). -/
def iterFrom (t : Table K V) : Nat → Nat → DR (List (K × V))
  | 0, _ => pure []
  | left + 1, i =>
    let j := skipDeleted t i
    if j == 0 then pure [] else do
      let e ← entryAt t j
      let rest ← iterFrom t left (j + 1)
      pure (e :: rest)

/-- `collect(d)`: `iterate(t)` starts at `skip_deleted(t, t.idxfloor)`, `base/dict.jl:707-709`. -/
def iterList (t : Table K V) : DR (List (K × V)) := iterFrom t (t.size + 1) t.idxfloor

/-- `length(t::Dict) = t.count`, `base/dict.jl:713`. -/
def dictLength (t : Table K V) : Nat := t.count

/-- `pop!(h::Dict)`, `base/dict.jl:620-629` (master; 1.13.2 has no `popcursor`
and always starts at `skip_deleted_floor!(h)`). -/
def popAny (t : Table K V) : DR ((K × V) × Table K V) := do
  if t.count == 0 then throw .argumentError
  let idx := skipDeleted t t.popcursor
  let (idx, t) :=
    if idx == 0 then
      -- skip_deleted_floor!, base/dict.jl:698-704
      let i := skipDeleted t t.idxfloor
      (i, if i != 0 then { t with idxfloor := i } else t)
    else (idx, t)
  let t := { t with popcursor := idx + 1 }
  let e ← entryAt t idx
  pure (e, deleteAt t idx)

/-! ## Bulk operations -/

/-- `filter!(pred, h::Dict)`, `base/dict.jl:725-733`. -/
def filterBang (t : Table K V) (pred : K → V → Bool) : DR (Table K V) :=
  if t.count == 0 then pure t else
  (List.range t.size).foldlM (fun t i =>
    let i := i + 1
    if isFilledB (t.slots i) then do
      let (k, v) ← entryAt t i
      pure (if pred k v then t else deleteAt t i)
    else pure t) t

/-- `sizehint!(d::Dict{T}, newsz; shrink)`, `base/dict.jl:196-204`, with the
Int64 arithmetic of the source (`3 * newsz` wraps). The result of `_tablesz`
is positive and at most `2^62` here, so its `toNat` is exact. -/
def sizehint (o : KeyOps K) (t : Table K V) (n : JInt .i64) (shrink : Bool) :
    DR (Table K V) := do
  let oldsz := t.size
  let len : JInt .i64 := JInt.lit .i64 t.count
  let m1 := if len.val < n.val then n else len          -- max(newsz, length(d))
  let m2 := if o.maxValues.val < m1.val then o.maxValues else m1  -- min(_, max_values(T))
  let c ← match JInt.cld (JInt.lit .i64 3 * m2) (JInt.lit .i64 2) with
    | .ok c => pure c
    | .error e => throw (.jl e)
  let newsz := tableszI64 c
  if (if shrink then newsz.val = oldsz else newsz.val ≤ oldsz) then pure t
  else rehash o t newsz.val.toNat

/-- `empty!(h::Dict)`, `base/dict.jl:224-238`. -/
def emptyBang (t : Table K V) : Table K V :=
  { t with slots := fun _ => 0, keys := fun _ => none, vals := fun _ => none, ndel := 0,
           count := 0, maxprobe := 0, age := bump t.age, idxfloor := max 1 t.size,
           popcursor := 1 }

/-- `copy(d::Dict) = Dict(d)`, `base/dict.jl:83-86,111`: every field copied. -/
def dictCopy (t : Table K V) : Table K V := t

/-- `mergewith!(combine, d1::Dict, d2)`, `base/dict.jl:753-774`, for `d2` a `Dict`
with the same key type (no conversion). `combine` does not mutate `d1`. -/
def mergewith (o : KeyOps K) (combine : V → V → V) (d1 d2 : Table K V) : DR (Table K V) := do
  let d1 ← sizehint o d1 (JInt.lit .i64 (d1.count + d2.count)) false
  let items ← iterList d2
  items.foldlM (fun d1 kv => do
    let (k, v) := kv
    let (i, sh, d1) ← keyindex2 o d1 (o.hash k) (o.eq k)
    if i > 0 then
      let w ← valAt d1 i.toNat
      pure { d1 with vals := upd d1.vals i.toNat (some (combine w v)) }
    else setindexAt o d1 v k (-i).toNat sh) d1

/-- `merge!(d::AbstractDict, other)`, `base/abstractdict.jl:224-234`, for Dicts. -/
def dictMerge (o : KeyOps K) (d other : Table K V) : DR (Table K V) := do
  let d ← sizehint o d (JInt.lit .i64 (d.count + other.count)) false
  let items ← iterList other
  items.foldlM (fun d kv => setindex o d kv.2 kv.1) d

end JuliaLean.Dicts
