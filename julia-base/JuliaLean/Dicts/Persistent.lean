import JuliaLean.Core

/-!
# `PersistentDict` insertion, `base/dict.jl` and `base/hamt.jl` (master `bbfa0ce4150`)

`PersistentDict{K,V}` (`base/dict.jl:902-1069`) wraps a hash array mapped trie
(`base/hamt.jl`). Keys are compared with `===` and hashed with `objectid`
(`HashState(key) = HashState(key, objectid(key), 0, 0)`, `base/hamt.jl:93`).
Each trie level consumes 5 bits of the hash; after `MAX_SHIFT = 55` the hash is
replaced by `hash(objectid(key), UInt(depth ÷ 5))` (`next`, `base/hamt.jl:103-117`).

The persistent `path` (`copy = true`) followed by `insert!` is modelled as one
recursive function returning the new trie; `objectid`, `===` and
`hash(::UInt64, ::UInt)` are parameters.
-/

namespace JuliaLean.Dicts.Persistent

variable {K V : Type}

/-- Exceptions (and non-termination) of the modelled calls. -/
inductive PErr where
  /-- `error("Perfect hash collision")`, `base/hamt.jl:207` -/
  | perfectCollision
  /-- A trie entry that cannot occur (out-of-bounds read of `trie.data`) -/
  | undefRef
  /-- The call never returns -/
  | diverges
  deriving Repr, DecidableEq

abbrev PR (α : Type) := Except PErr α

/-- What the trie needs from keys of type `K`. -/
structure PDOps (K : Type) where
  /-- `objectid(key)` -/
  oid : K → JInt .u64
  /-- `k1 === k2` -/
  ideq : K → K → Bool
  /-- `hash(x::UInt64, h::UInt)` -/
  hu : JInt .u64 → JInt .u64 → JInt .u64

/-- `===` is an equivalence that `objectid` respects (`objectid` docstring:
"`objectid(x) == objectid(y)` if `x === y`"), and `hash(x, seed)` is injective
in `x` (as `hash(::UInt64, ::UInt)` is). -/
structure PDOps.Lawful {K : Type} (o : PDOps K) : Prop where
  refl : ∀ a, o.ideq a a = true
  symm : ∀ a b, o.ideq a b = true → o.ideq b a = true
  trans : ∀ a b c, o.ideq a b = true → o.ideq b c = true → o.ideq a c = true
  oid_eq : ∀ a b, o.ideq a b = true → o.oid a = o.oid b
  hu_inj : ∀ a b s, o.hu a s = o.hu b s → a = b

/-- `struct HAMT{K,V}; data::Vector{Union{Leaf{K,V}, HAMT{K,V}}}; bitmap::UInt32; end`
(`base/hamt.jl:62-67`); a `leaf` is `Leaf{K,V}(key, val)`. -/
inductive Trie (K V : Type) where
  | leaf (k : K) (v : V)
  | node (data : List (Trie K V)) (bitmap : Nat)

/-- `HashState` without its `key` field (`base/hamt.jl:87-92`). -/
structure HS where
  hash : JInt .u64
  depth : Nat
  shift : Nat

/-- `BITS_PER_LEVEL = 5` and `MAX_SHIFT = (64 ÷ 5 - 1) * 5 = 55`, `base/hamt.jl:46-50`. -/
def bitsPerLevel : Nat := 5
def maxShift : Nat := 55

/-- `HashState(key)`, `base/hamt.jl:93`. -/
def hs0 (o : PDOps K) (k : K) : HS := ⟨o.oid k, 0, 0⟩

/-- `next(h)`, `base/hamt.jl:103-117`. -/
def next (o : PDOps K) (k : K) (h : HS) : HS :=
  let depth := h.depth + 1
  let shift := h.shift + bitsPerLevel
  if shift > maxShift then ⟨o.hu (o.oid k) (JInt.wrap .u64 (depth / bitsPerLevel)), depth, 0⟩
  else ⟨h.hash, depth, shift⟩

/-- `HashState{K}(other, key)`, `base/hamt.jl:94-100`: `next` from `HashState(key)`
until the depth of `other`. -/
def hsAt (o : PDOps K) (k : K) (depth : Nat) : HS := Nat.repeat (next o k) depth (hs0 o k)

/-- `BitmapIndex(h) = (h.hash >> h.shift) & LEVEL_MASK`, `base/hamt.jl:124`. -/
def bitIdx (h : HS) : Nat := (h.hash.val.toNat >>> h.shift) % 32

/-- `isset(trie, bi)`, `base/hamt.jl:127`. -/
def isset (bitmap bi : Nat) : Bool := bitmap.testBit bi

/-- `entry_index(trie, bi) - 1`, `base/hamt.jl:138-141`: set bits below `bi`. -/
def entryIdx (bitmap bi : Nat) : Nat := ((List.range bi).filter bitmap.testBit).length

/-- The `while true` loop of `insert!` after a collision with the leaf `k' => v'`
(`base/hamt.jl:209-235`): one single-child level per equal 5-bit chunk, then a
level holding both leaves in bitmap order. -/
def grow (o : PDOps K) (k : K) (v : V) (k' : K) (v' : V) : Nat → HS → HS → PR (Trie K V)
  | 0, _, _ => throw .diverges
  | fuel + 1, h, hl =>
    let h := next o k h
    let hl := next o k' hl
    let bn := bitIdx h
    let bo := bitIdx hl
    if bn == bo then do
      let sub ← grow o k v k' v' fuel h hl
      pure (.node [sub] (2 ^ bn))
    else
      pure (.node (if bn < bo then [.leaf k v, .leaf k' v'] else [.leaf k' v', .leaf k v])
        (2 ^ bn ||| 2 ^ bo))

/-- `path(trie, h, true)` then `insert!(found, present, trie, i, bi, h, val)`
(`base/hamt.jl:158-190`, `192-237`). -/
def ins (o : PDOps K) (k : K) (v : V) : Nat → Trie K V → HS → PR (Trie K V)
  | 0, _, _ => throw .diverges
  | _ + 1, .leaf _ _, _ => throw .undefRef
  | fuel + 1, .node data bm, h =>
    let bi := bitIdx h
    let i := entryIdx bm bi
    if isset bm bi then
      match data[i]? with
      | none => throw .undefRef
      | some (.leaf k' v') =>
        -- `found = next.key === h.key`
        if o.ideq k' k then pure (.node (data.set i (.leaf k v)) bm)
        else do
          -- collision -> grow; `leaf_h = HashState{K}(h, leaf.key)`
          let hl := hsAt o k' h.depth
          if hl.hash == h.hash then throw .perfectCollision
          let sub ← grow o k v k' v' fuel h hl
          pure (.node (data.set i sub) bm)
      | some sub => do
        let sub ← ins o k v fuel sub (next o k h)
        pure (.node (data.set i sub) bm)
    else pure (.node (data.insertIdx i (.leaf k v)) (bm ||| 2 ^ bi))

/-- `HAMT{K,V}()`, the trie of `PersistentDict{K,V}()`. -/
def empty : Trie K V := .node [] 0

/-- Deeper than any trie whose keys have distinct hashes. -/
def fuelBound : Nat := 2 ^ 16

/-- `KeyValue.set(dict, key, val)` / `_keyvalueset`, `base/dict.jl:909-919`;
`PersistentDict(dict, key => val)` (`base/dict.jl:982-990`). -/
def pdSet (o : PDOps K) (t : Trie K V) (k : K) (v : V) : PR (Trie K V) :=
  ins o k v fuelBound t (hs0 o k)

/-- `PersistentDict(k1 => v1, ...)` from the empty trie (`base/dict.jl:970-1005`). -/
def pdBuild (o : PDOps K) (ps : List (K × V)) : PR (Trie K V) :=
  ps.foldlM (fun t kv => pdSet o t kv.1 kv.2) empty

/-- `KeyValue.get(dict, key)` with `path(trie, h)`, `base/dict.jl:1033-1045`. -/
def get (o : PDOps K) (k : K) : Nat → Trie K V → HS → Option V
  | 0, _, _ => none
  | _ + 1, .leaf _ _, _ => none
  | fuel + 1, .node data bm, h =>
    let bi := bitIdx h
    if isset bm bi then
      match data[entryIdx bm bi]? with
      | none => none
      | some (.leaf k' v') => if o.ideq k' k then some v' else none
      | some sub => get o k fuel sub (next o k h)
    else none

def pdGet (o : PDOps K) (t : Trie K V) (k : K) : Option V := get o k fuelBound t (hs0 o k)

/-- `PersistentDict` "behaves like an IdDict" (docstring `base/dict.jl:945-946`):
setting a key on any `PersistentDict` succeeds, and the key then maps to the value. -/
def PersistentSetGet : Prop :=
  ∀ (K V : Type) (o : PDOps K), o.Lawful → ∀ (ps : List (K × V)) t, pdBuild o ps = .ok t →
    ∀ k v, ∃ t', pdSet o t k v = .ok t' ∧ pdGet o t' k = some v

/-- `KeyValue.set(dict::PersistentDict{K,V}, key::K, val::V)` is declared
`Base.@assume_effects :nothrow` (`base/dict.jl:911-912`): it never throws. -/
def PersistentSetNothrow : Prop :=
  ∀ (K V : Type) (o : PDOps K), o.Lawful → ∀ (ps : List (K × V)) t, pdBuild o ps = .ok t →
    ∀ k v, (pdSet o t k v).toBool = true

/-- Keys `0` and `2` are distinct but share their `objectid` (the reproducer
builds such a pair of `Int64`/`UInt64` keys from `int64hash`). -/
def collideOps : PDOps Nat where
  oid := fun n => JInt.wrap .u64 (n % 2)
  ideq := fun a b => a == b
  hu := fun a _ => a

theorem collideOps_lawful : collideOps.Lawful where
  refl := by intro a; simp [collideOps]
  symm := by intro a b h; simp [collideOps] at h ⊢; exact h.symm
  trans := by intro a b c h1 h2; simp [collideOps] at h1 h2 ⊢; exact h1.trans h2
  oid_eq := by intro a b h; simp [collideOps] at h; rw [h]
  hu_inj := by intro a b s h; simpa [collideOps] using h

theorem collide_build : pdBuild collideOps [((0 : Nat), (1 : Nat))] =
    .ok (.node [.leaf 0 1] 1) := rfl

theorem collide_set : pdSet collideOps (.node [.leaf 0 1] 1 : Trie Nat Nat) 2 2 =
    .error .perfectCollision := rfl

theorem persistentSetGet_refuted : ¬ PersistentSetGet := by
  intro h
  obtain ⟨t', ht', -⟩ := h Nat Nat collideOps collideOps_lawful _ _ collide_build 2 2
  rw [collide_set] at ht'
  cases ht'

theorem persistentSetNothrow_refuted : ¬ PersistentSetNothrow := by
  intro h
  have hn := h Nat Nat collideOps collideOps_lawful _ _ collide_build 2 2
  rw [collide_set] at hn
  simp [Except.toBool] at hn

end JuliaLean.Dicts.Persistent
