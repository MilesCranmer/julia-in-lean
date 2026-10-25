import JuliaLean.IdDicts.Value
import JuliaLean.Dicts.Table

/-!
# `IdDict`, base/iddict.jl (master `bbfa0ce4150`)

The table `d.ht::Memory{Any}` is manipulated only through the C functions
`jl_eqtable_put/get/pop/nextind` and `jl_idtable_rehash` (src/iddict.c). They
are modelled as a primitive map with `===` keys: `Tab` is the list of live
`(key, value)` pairs in slot order. src/iddict.c implements exactly this: a
deleted slot holds the tombstone `(nothing, NULL)`, skipped by
`jl_eqtable_nextind`, and the probe loops continue past tombstones (also for
the key `nothing`, src/iddict.c:67-71, 128-130).

The Julia wrapper code is mirrored line by line: the `count`/`ndel`
bookkeeping, the `ndel` rehash trigger, the `secret_table_token` sentinel, the
type checks and conversions, and the `::K`/`::V` casts.

Modelling decisions:
* `sz` is `length(d.ht)`. `jl_eqtable_put` may replace the array by a larger
  one (src/iddict.c:87-103); that growth is not tracked: it preserves the live
  pairs, and `sz` only decides when `setindex!` rehashes, which also
  preserves them.
* `count`, `ndel`, `sz` are `Nat`: on a table that fits in memory the Int
  arithmetic of base/iddict.jl:84-85,90,111-112 cannot wrap. `sizehint!`, the
  one place where a user integer enters, uses wrapping `JInt .i64`.
* Iteration order is the slot order of `Tab`; in Julia it is the hash order.
  No property depends on the order.
-/

namespace JuliaLean.IdDicts

/-- The live `(key, value)` pairs of an eqtable, in slot order. -/
abbrev Tab := List (JVal × JVal)

/-- `jl_eqtable_get(h, key, deflt)`, src/iddict.c:151-156. -/
def eqtableGet : Tab → JVal → JVal → JVal
  | [], _, deflt => deflt
  | (k', v') :: t, k, deflt => if egal k k' then v' else eqtableGet t k deflt

/-- `jl_eqtable_put(h, key, val, &inserted)`, src/iddict.c:140-147: replaces
the value of a `===` key in place (`inserted = 0`) or fills a free slot
(`inserted = 1`). -/
def eqtablePut : Tab → JVal → JVal → Tab × Nat
  | [], k, v => ([(k, v)], 1)
  | (k', v') :: t, k, v =>
      if egal k k' then ((k', v) :: t, 0)
      else let r := eqtablePut t k v; ((k', v') :: r.1, r.2)

/-- `jl_eqtable_pop(h, key, deflt, &found)`, src/iddict.c:164-176: the value
(or `deflt`), `found`, and the table with the pair cleared. -/
def eqtablePop : Tab → JVal → JVal → JVal × Bool × Tab
  | [], _, deflt => (deflt, false, [])
  | (k', v') :: t, k, deflt =>
      if egal k k' then (v', true, t)
      else let r := eqtablePop t k deflt; (r.1, r.2.1, (k', v') :: r.2.2)

/-- `IdDict{K,V}` fields, base/iddict.jl:27-31. -/
structure IdDict where
  K : JTy
  V : JTy
  ht : Tab
  /-- `length(d.ht)` -/
  sz : Nat
  count : Nat
  ndel : Nat

/-- `IdDict{K,V}()`, base/iddict.jl:31: `Memory{Any}(undef, 32)`. -/
def IdDict.new (K V : JTy) : IdDict := ⟨K, V, [], 32, 0, 0⟩

/-- `rehash!(d, newsz)`, base/iddict.jl:64-67: `jl_idtable_rehash` copies the
live pairs into a fresh array of `newsz` slots. -/
def IdDict.rehash (d : IdDict) (newsz : Nat) : IdDict := { d with sz := newsz }

/-- `sizehint!(d, newsz)`, base/iddict.jl:69-77 (`newsz*2` wraps). -/
def IdDict.sizehint (d : IdDict) (newsz : JInt .i64) : IdDict :=
  let newsz := JuliaLean.Dicts.tableszI64 (newsz * JInt.lit .i64 2)
  let oldsz := d.sz
  if newsz.val < ((oldsz * 5 / 4 : Nat) : Int) then d
  else d.rehash newsz.val.toNat

/-- `x::T` -/
def cast (x : JVal) (T : JTy) : Except IErr JVal :=
  if isa x T then .ok x else .error .typeError

/-- `setindex!(d, val, key)`, base/iddict.jl:79-92. -/
def IdDict.setindex (d : IdDict) (val key : JVal) : Out IdDict Unit :=
  if !isa key d.K then (d, .error .typeError) else
  let val? : Except IErr JVal :=
    if isa val d.V then .ok val else (convert d.V val).bind (cast · d.V)
  match val? with
  | .error e => (d, .error e)
  | .ok val =>
    let d := if d.ndel ≥ (3 * d.sz) / 4 then { d.rehash (max (d.sz / 2) 32) with ndel := 0 } else d
    let r := eqtablePut d.ht key val
    ({ d with ht := r.1, count := d.count + r.2 }, .ok ())

/-- `get(d, key, default)`, base/iddict.jl:94-97. -/
def IdDict.get (d : IdDict) (key default : JVal) : Except IErr JVal :=
  let val := eqtableGet d.ht key default
  if egal val default then .ok default else cast val d.V

/-- `getindex(d, key)`, base/iddict.jl:99-103. -/
def IdDict.getindex (d : IdDict) (key : JVal) : Except IErr JVal :=
  let val := eqtableGet d.ht key token
  if egal val token then .error .keyError else cast val d.V

/-- `pop!(d, key, default)`, base/iddict.jl:105-115. -/
def IdDict.pop3 (d : IdDict) (key default : JVal) : Out IdDict JVal :=
  let r := eqtablePop d.ht key default
  let d := { d with ht := r.2.2 }
  if !r.2.1 then (d, .ok default)
  else ({ d with count := d.count - 1, ndel := d.ndel + 1 }, cast r.1 d.V)

/-- `pop!(d, key)`, base/iddict.jl:117-121. -/
def IdDict.pop (d : IdDict) (key : JVal) : Out IdDict JVal :=
  let r := d.pop3 key token
  match r.2 with
  | .error e => (r.1, .error e)
  | .ok val => if egal val token then (r.1, .error .keyError) else (r.1, cast val d.V)

/-- `delete!(d, key)`, base/iddict.jl:123-126. -/
def IdDict.delete (d : IdDict) (key : JVal) : Out IdDict Unit :=
  let r := d.pop3 key token
  (r.1, r.2.map fun _ => ())

/-- `empty!(d)`, base/iddict.jl:128-137. -/
def IdDict.empty (d : IdDict) : IdDict := { d with ht := [], sz := 32, ndel := 0, count := 0 }

/-- `iterate(d)` to exhaustion, base/iddict.jl:139-145: `_oidd_nextind`
visits every live pair once; each yields `Pair{K,V}(ht[i]::K, ht[i+1]::V)`. -/
def IdDict.iterate (d : IdDict) : Except IErr Tab :=
  d.ht.mapM fun p => do
    let k ← cast p.1 d.K
    let v ← cast p.2 d.V
    pure (k, v)

/-- `length(d) = d.count`, base/iddict.jl:147. -/
def IdDict.length (d : IdDict) : Nat := d.count

/-- `haskey(d, k) = in(k, keys(d))`, base/abstractdict.jl:19 and
`in(k, ::KeySet{<:Any,<:IdDict})`, base/iddict.jl:185. -/
def IdDict.haskey (d : IdDict) (k : JVal) : Except IErr Bool :=
  (d.get k token).map fun v => !egal v token

/-- `get!(d, key, default)`, base/iddict.jl:151-160. -/
def IdDict.getBang (d : IdDict) (key default : JVal) : Out IdDict JVal :=
  let val := eqtableGet d.ht key token
  if egal val token then
    let val? : Except IErr JVal :=
      if isa default d.V then .ok default else (convert d.V default).bind (cast · d.V)
    match val? with
    | .error e => (d, .error e)
    | .ok val =>
      let r := d.setindex val key
      (r.1, r.2.map fun _ => val)
  else (d, cast val d.V)

/-- `get!(default::Callable, d, key)`, base/iddict.jl:171-183, for a `default`
that returns `fv` without touching `d`. -/
def IdDict.getBangF (d : IdDict) (fv key : JVal) : Out IdDict JVal :=
  let val := eqtableGet d.ht key token
  if egal val token then
    let val? : Except IErr JVal :=
      if !isa fv d.V then (convert d.V fv).bind (cast · d.V) else .ok fv
    match val? with
    | .error e => (d, .error e)
    | .ok val =>
      let r := d.setindex val key
      (r.1, r.2.map fun _ => val)
  else (d, cast val d.V)

/-! ## Call sequences -/

/-- Calls that change an `IdDict`. -/
inductive DOp where
  | set (k v : JVal)
  | delete (k : JVal)
  | pop3 (k default : JVal)
  | pop (k : JVal)
  | empty
  | sizehint (n : JInt .i64)
  | getBang (k default : JVal)
  | getBangF (fv k : JVal)

/-- One call; a throwing call leaves whatever state it reached (as under
`try ... catch end`). -/
def DOp.run (d : IdDict) : DOp → IdDict
  | .set k v => (d.setindex v k).1
  | .delete k => (d.delete k).1
  | .pop3 k dflt => (d.pop3 k dflt).1
  | .pop k => (d.pop k).1
  | .empty => d.empty
  | .sizehint n => d.sizehint n
  | .getBang k dflt => (d.getBang k dflt).1
  | .getBangF fv k => (d.getBangF fv k).1

/-- Run a call sequence from `IdDict{K,V}()`. -/
def runD (K V : JTy) (ops : List DOp) : IdDict := ops.foldl DOp.run (IdDict.new K V)

/-- The calls whose effect on the dictionary does not go through the
sentinel (`get!` reads through it and is treated separately). -/
def DOp.mutator : DOp → Bool
  | .getBang _ _ | .getBangF _ _ => false
  | _ => true

/-! ## Reference `===` map -/

/-- Reference lookup in a `===`-keyed association list. -/
def rLookup : Tab → JVal → Option JVal
  | [], _ => none
  | (k', v') :: t, k => if egal k k' then some v' else rLookup t k

/-- Reference insertion/overwrite. -/
def rSet (m : Tab) (k v : JVal) : Tab := (k, v) :: m.filter fun p => !egal p.1 k

/-- Reference deletion. -/
def rDel (m : Tab) (k : JVal) : Tab := m.filter fun p => !egal p.1 k

/-- The documented effect of a call on the reference map of an
`IdDict{K,V}`: `setindex!` throws for keys not of type `K`
(`KeyTypeError`) and for values that do not convert to `V`; `get!` stores
`convert(V, default)` exactly when the key is absent. -/
def DOp.ref (K V : JTy) (m : Tab) : DOp → Tab
  | .set k v => if isa k K then (match convert V v with | .ok w => rSet m k w | .error _ => m) else m
  | .delete k | .pop3 k _ | .pop k => rDel m k
  | .empty => []
  | .sizehint _ => m
  | .getBang k dflt | .getBangF dflt k =>
      match rLookup m k with
      | some _ => m
      | none => if isa k K then (match convert V dflt with | .ok w => rSet m k w | .error _ => m) else m

/-- The reference map after a call sequence. -/
def refD (K V : JTy) (ops : List DOp) : Tab := ops.foldl (DOp.ref K V) []

/-- Keys pairwise not `===`. -/
def keysDistinct (t : Tab) : Prop := (t.map Prod.fst).Nodup

end JuliaLean.IdDicts
