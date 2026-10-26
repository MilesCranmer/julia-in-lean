import JuliaLean.Core

/-!
# The `IdDict` hash table slot by slot, `src/iddict.c` and `base/iddict.jl`

`JuliaLean.IdDicts` models `d.ht` as the list of live pairs. Iterating while
assigning (the generic `map!(f, values(d))` and `mergewith!(f, d, d)`,
`base/abstractdict.jl:288-293,673-681`) depends on where the pairs sit, so this
file mirrors the C table functions on the array itself: `ht` is the
`Memory{Any}` of length `2 * slots` holding key/value pairs; `none` is `NULL`.
A deleted pair leaves the key `nothing` with a `NULL` value
(`jl_eqtable_pop`, src/iddict.c:164-176).

Keys and values are `Int`s here (an `IdDict{Int,Int}`); `===` on `Int` is
equality, and `keyhash` (`jl_object_id_`) is a parameter.
-/

namespace JuliaLean.DictsCov.EqTable

/-- A key slot: `NULL`, the deletion marker `nothing`, or an `Int` key. -/
inductive KSlot where
  | null
  | nothing
  | key (k : Int)
  deriving Repr, DecidableEq

/-- `d.ht`: pairs `(key slot, value or NULL)`, slot `i` at `ht[2i], ht[2i+1]`. -/
abbrev Mem := List (KSlot × Option Int)

/-- `jl_alloc_memory_any(n)`: `n` entries, all `NULL` (`n/2` pairs). -/
def alloc (n : Nat) : Mem := List.replicate (n / 2) (.null, none)

def getSlot (a : Mem) (i : Nat) : KSlot × Option Int := a.getD i (.null, none)

/-- `max_probe(size)`, src/iddict.c:6. -/
def maxProbe (size : Nat) : Nat := if size ≤ 1024 then 16 else size / 64

/-- The probe loop of `jl_table_assign_bp`, src/iddict.c:50-79, over pair
indices (`index/2`). Returns `inr ()` when the value of a present key was
replaced, `inl (some j)` for the first free slot (`NULL` or deleted), `inl none`
when the table is full. -/
def probe (a : Mem) (key : Int) (sz : Nat) (orig : Nat) :
    Nat → Nat → Nat → Option Nat → Sum (Option Nat) Nat
  | 0, _, _, es => .inl es
  | fuel + 1, index, iter, es =>
    let (k2, v2) := getSlot a index
    if k2 == .null then .inl (if es.isNone then some index else es)
    else
      -- `jl_egal(key, k2)` with a present value: replace
      if k2 == .key key ∧ v2.isSome then .inr index
      else
        let es := if es.isNone ∧ v2.isNone then some index else es
        let index := (index + 1) % sz
        let iter := iter + 1
        if iter ≤ maxProbe sz ∧ index ≠ orig then probe a key sz orig fuel index iter es
        else .inl es

/-- Write pair slot `j`. -/
def setSlot (a : Mem) (j : Nat) (p : KSlot × Option Int) : Mem := a.set j p

/-- `jl_idtable_rehash(a, newsz)`, src/iddict.c:13-30: re-insert every pair
with a non-`NULL` value, in index order, into a fresh array of `newsz`
entries, with the insertion `ins`. -/
def rehashWith (ins : Mem → Int → Int → Mem) (a : Mem) (newsz : Nat) : Mem :=
  a.foldl (fun b p => match p with
    | (.key k, some v) => ins b k v
    | _ => b) (alloc newsz)

/-- `jl_table_assign_bp(&a, key, val)`, src/iddict.c:32-104: the new array and
`inserted`. `fuel` bounds the number of growths. -/
def assign (keyhash : Int → Nat) : Nat → Mem → Int → Int → Mem × Nat
  | 0, a, _, _ => (a, 0)
  | fuel + 1, a, key, val =>
    let a := if a.length = 0 then alloc 32 else a
    let sz := a.length
    let index := keyhash key % sz
    match probe a key sz index (sz + 1) index 0 none with
    | .inr j => (setSlot a j (.key key, some val), 0)
    | .inl (some j) => (setSlot a j (.key key, some val), 1)
    | .inl none =>
      let len := 2 * sz
      let newsz := if len < 32 then 32 else if len ≥ 2 ^ 19 ∨ len ≤ 2 ^ 8 then len * 2 else len * 4
      assign keyhash fuel (rehashWith (fun b k v => (assign keyhash fuel b k v).1) a newsz) key val

/-- `jl_idtable_rehash` with the insertion of `jl_table_assign_bp`. -/
def rehash (keyhash : Int → Nat) (fuel : Nat) (a : Mem) (newsz : Nat) : Mem :=
  rehashWith (fun b k v => (assign keyhash fuel b k v).1) a newsz

/-- The probe loop of `jl_table_peek_bp` for an `Int` key, src/iddict.c:118-133. -/
def peekGo (a : Mem) (key : Int) (sz orig : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, index, iter =>
    let (k2, v2) := getSlot a index
    if k2 == .null then none
    else if k2 == .key key then (if v2.isSome then some index else none)
    else
      let index := (index + 1) % sz
      let iter := iter + 1
      if iter ≤ maxProbe sz ∧ index ≠ orig then peekGo a key sz orig fuel index iter else none

/-- `jl_table_peek_bp(a, key)`, src/iddict.c:108-134: the pair index holding
`key` with a non-`NULL` value. -/
def peekH (keyhash : Int → Nat) (a : Mem) (key : Int) : Option Nat :=
  let sz := a.length
  if sz = 0 then none else
  let orig := keyhash key % sz
  peekGo a key sz orig (sz + 1) orig 0

/-- `mutable struct IdDict{Int,Int}`, base/iddict.jl:25-31. -/
structure IdD where
  ht : Mem
  count : Nat
  ndel : Nat
  deriving Repr, DecidableEq

/-- `IdDict{K,V}()`: `Memory{Any}(undef, 32)`, base/iddict.jl:31. -/
def IdD.new : IdD := ⟨alloc 32, 0, 0⟩

/-- `length(d.ht)` -/
def IdD.len (d : IdD) : Nat := 2 * d.ht.length

/-- Enough growths for any table in this file. -/
def fuel : Nat := 64

/-- `setindex!(d, val, key)`, base/iddict.jl:79-92, for `Int` keys and values. -/
def IdD.setindex (keyhash : Int → Nat) (d : IdD) (val key : Int) : IdD :=
  let d := if d.ndel ≥ (3 * d.len) / 4 then
      { d with ht := rehash keyhash fuel d.ht (max (d.len / 2) 32), ndel := 0 }
    else d
  let r := assign keyhash fuel d.ht key val
  { d with ht := r.1, count := d.count + r.2 }

/-- `delete!(d, key)` = `pop!(d, key, secret_table_token)`, base/iddict.jl:105-126. -/
def IdD.delete (keyhash : Int → Nat) (d : IdD) (key : Int) : IdD :=
  match peekH keyhash d.ht key with
  | some j => { d with ht := setSlot d.ht j (.nothing, none), count := d.count - 1, ndel := d.ndel + 1 }
  | none => d

/-- `get(d, key, default)`, base/iddict.jl:94-97. -/
def IdD.get (keyhash : Int → Nat) (d : IdD) (key : Int) : Option Int :=
  match peekH keyhash d.ht key with
  | some j => (getSlot d.ht j).2
  | none => none

/-- `jl_eqtable_nextind(t, i)` on pair indices, src/iddict.c:178-188. -/
def nextind (a : Mem) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, j => if j ≥ a.length then none
    else if (getSlot a j).2.isSome then some j else nextind a fuel (j + 1)

/-- `iterate(d, idx)`, base/iddict.jl:141-145: the pair at the next live slot
at or after pair index `j`, and the next state (the following slot). -/
def IdD.iterate (d : IdD) (j : Nat) : Option ((Int × Int) × Nat) :=
  match nextind d.ht (d.ht.length + 1) j with
  | none => none
  | some i => match getSlot d.ht i with
    | (.key k, some v) => some ((k, v), i + 1)
    | _ => none

/-- The generic `map!(f, values(d))`, base/abstractdict.jl:673-681:
`for (key, val) in pairs(dict); dict[key] = f(val); end`. -/
def mapValues (keyhash : Int → Nat) (f : Int → Int) : Nat → IdD → Nat → IdD
  | 0, d, _ => d
  | fuel + 1, d, j => match d.iterate j with
    | none => d
    | some ((k, v), j') => mapValues keyhash f fuel (d.setindex keyhash (f v) k) j'

/-- The generic `mergewith!(combine, d1, d2)` with `d1 === d2`,
base/abstractdict.jl:288-293: `d1[k] = haskey(d1, k) ? combine(d1[k], v) : v`
while iterating `d2`. -/
def mergewithSelf (keyhash : Int → Nat) (combine : Int → Int → Int) : Nat → IdD → Nat → IdD
  | 0, d, _ => d
  | fuel + 1, d, j => match d.iterate j with
    | none => d
    | some ((k, v), j') =>
      let nv := match d.get keyhash k with | some w => combine w v | none => v
      mergewithSelf keyhash combine fuel (d.setindex keyhash nv k) j'

/-- One call of a program building the dictionary. -/
inductive Op where
  | set (k v : Int)
  | del (k : Int)

def run (keyhash : Int → Nat) (ops : List Op) : IdD :=
  ops.foldl (fun d op => match op with
    | .set k v => d.setindex keyhash v k
    | .del k => d.delete keyhash k) IdD.new

/-- The pairs of a dictionary by iteration. -/
def pairsOf (d : IdD) : List (Int × Int) :=
  d.ht.filterMap fun p => match p with
    | (.key k, some v) => some (k, v)
    | _ => none

end JuliaLean.DictsCov.EqTable
