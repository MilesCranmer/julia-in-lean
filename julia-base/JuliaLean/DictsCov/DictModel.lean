import JuliaLean.DictsCov.LookupQ

/-!
# `Dict` methods of `base/dict.jl` (master `bbfa0ce4150`)

The table, probing, insertion, deletion and rehashing are the mirrored
definitions of `JuliaLean.Dicts` (`Dicts/Table.lean`). This file mirrors the
remaining `Dict` methods on top of them: constructors, key and value
conversion, lookups with keys of any type, `getkey`, `pop!`, iteration of the
dictionary and of its `keys`/`values`, `Iterators.only`, `map!` and
`reduce(merge, ...)`.

A key of a type other than `K` is a `Conv Q K` (`x isa K`, `convert(K, x)`,
`hash(x)`, `x === k || isequal(x, k)`); a value of a type other than `V` is a
`VConv W V` (`x isa V`, `convert(V, x)`).
-/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

variable {K V Q W : Type}

/-- How a value of type `W` is stored in a `Memory{V}`. -/
structure VConv (W V : Type) where
  /-- `x isa V` (with the value as a `V`) -/
  isa : W → Option V
  /-- `convert(V, x)::V` -/
  convert : W → DR V

/-- `v = v0 isa V ? v0 : convert(V, v0)::V`, `base/dict.jl:360`. -/
def convV (cv : VConv W V) (w : W) : DR V :=
  match cv.isa w with
  | some v => pure v
  | none => cv.convert w

/-! ## Constructors, `base/dict.jl:77-120` -/

/-- The inner constructor `Dict{K,V}(slots, keys, vals, ndel, count, age,
idxfloor, maxprobe, popcursor)`, `base/dict.jl:87-89`: `new(...)` of the
arguments (`size` is the common length of the three memories). -/
def dictRaw (size : Nat) (slots : Nat → Nat) (keys : Nat → Option K) (vals : Nat → Option V)
    (ndel count : Nat) (age : JInt .u64) (idxfloor maxprobe popcursor : Nat) : Table K V :=
  ⟨size, slots, keys, vals, ndel, count, age, idxfloor, maxprobe, popcursor⟩

/-- `Dict{K,V}(kv)`, `base/dict.jl:91-98`, for an iterator of pairs already of
types `K` and `V`; `hasLen` is `haslength(kv)`. -/
def dictKV (o : KeyOps K) (hasLen : Bool) (kv : List (K × V)) : DR (Table K V) := do
  let h : Table K V := Table.empty
  let h ← if hasLen then sizehint o h (JInt.lit .i64 kv.length) true else pure h
  kv.foldlM (fun h p => setindex o h p.2 p.1) h

/-- `Dict{K,V}(p::Pair) = setindex!(Dict{K,V}(), p.second, p.first)`, `base/dict.jl:99`. -/
def dictPair (o : KeyOps K) (p : K × V) : DR (Table K V) :=
  setindex o Table.empty p.2 p.1

/-- `Dict{K,V}(ps::Pair...)`, `base/dict.jl:100-107`. -/
def dictPairs (o : KeyOps K) (ps : List (K × V)) : DR (Table K V) := do
  let h ← sizehint o (Table.empty : Table K V) (JInt.lit .i64 ps.length) true
  ps.foldlM (fun h p => setindex o h p.2 p.1) h

/-- `Dict() = Dict{Any,Any}()`, `base/dict.jl:109` (here with `K = V = Any`
being the parameters of the table). -/
def dictAnyNew : Table K V := Table.empty

/-- `Dict(kv::Tuple{}) = Dict()`, `base/dict.jl:110`. -/
def dictEmptyTuple (_ : Unit) : Table K V := dictAnyNew

/-- `copy(d::Dict) = Dict(d)`, `base/dict.jl:111`, which is the copying inner
constructor `Dict{K,V}(d::Dict{K,V})`, `base/dict.jl:83-86`. -/
def dictCopyOf (t : Table K V) : Table K V := dictCopy t

/-- `Dict(ps::Pair{K,V}...) = Dict{K,V}(ps)`, `base/dict.jl:115`: a tuple has a length. -/
def dictOfTypedPairs (o : KeyOps K) (ps : List (K × V)) : DR (Table K V) := dictKV o true ps

/-! ## Insertion with conversion, `base/dict.jl:327-387` -/

/-- `ht_keyindex2!(h, key) = ht_keyindex2_shorthash!(h, key)[1]`, `base/dict.jl:325`. -/
def keyindex2Bang (o : KeyOps K) (t : Table K V) (key : K) : DR (Int × Table K V) := do
  let (index, _, t) ← keyindex2 o t (o.hash key) (o.eq key)
  pure (index, t)

/-- `_setindex!(h, v, key, index)` with the default `sh = _shorthash7(hash(key))`,
`base/dict.jl:327`. -/
def setindexAtDefault (o : KeyOps K) (t : Table K V) (v : V) (key : K) (index : Nat) :
    DR (Table K V) :=
  setindexAt o t v key index (shorthash7 (o.hash key))

/-- `setindex!(h::Dict{K,V}, v0, key::K)`, `base/dict.jl:359-372`. -/
def setindexV (o : KeyOps K) (cv : VConv W V) (t : Table K V) (v0 : W) (key : K) :
    DR (Table K V) := do
  let v ← convV cv v0
  let (index, sh, t) ← keyindex2 o t (o.hash key) (o.eq key)
  if index > 0 then pure (overwriteAt t v key index.toNat)
  else setindexAt o t v key (-index).toNat sh

/-- `setindex!(h::Dict{K,Any}, v, key::K)`, `base/dict.jl:374-387`: no value conversion. -/
def setindexAny (o : KeyOps K) (t : Table K V) (v : V) (key : K) : DR (Table K V) := do
  let (index, sh, t) ← keyindex2 o t (o.hash key) (o.eq key)
  if index > 0 then pure (overwriteAt t v key index.toNat)
  else setindexAt o t v key (-index).toNat sh

/-- `key = convert(K, key0)::K; isequal(key, key0) || throw(KeyTypeError(K, key0))`,
the key conversion of `base/dict.jl:347-357` and `445-455`. -/
def convKey (c : Conv Q K) (key0 : Q) : DR K :=
  match c.isa key0 with
  | some k => pure k
  | none => do
    let k ← c.convert key0
    if c.iseq key0 k then pure k else throw .keyTypeError

/-- `setindex!(h::Dict{K,V}, v0, key0)`, `base/dict.jl:347-357`. -/
def setindexConvV (o : KeyOps K) (c : Conv Q K) (cv : VConv W V) (t : Table K V) (v0 : W)
    (key0 : Q) : DR (Table K V) := do
  let key ← convKey c key0
  setindexV o cv t v0 key

/-! ## `get!`, `base/dict.jl:445-478` -/

/-- `get!(default, h::Dict{K,V}, key::K)`, `base/dict.jl:457-478`: `default()`
returns a `W` (and may read and mutate `h`), converted to `V` before the age
check. -/
def getBangV (o : KeyOps K) (cv : VConv W V) (t : Table K V) (key : K)
    (default : Table K V → DR (W × Table K V)) : DR (V × Table K V) :=
  getBang o t key (fun t => do
    let p ← default t
    let v ← convV cv p.1
    pure (v, p.2))

/-- `get!(default, h::Dict{K,V}, key0)`, `base/dict.jl:445-455`. -/
def getBangConv (o : KeyOps K) (c : Conv Q K) (cv : VConv W V) (t : Table K V) (key0 : Q)
    (default : Table K V → DR (W × Table K V)) : DR (V × Table K V) := do
  let key ← convKey c key0
  getBangV o cv t key default

/-! ## Lookups with a key of any type, `base/dict.jl:480-578` -/

/-- `getindex(h::Dict{K,V}, key)`, `base/dict.jl:480-483`. -/
def getindexQ (c : Conv Q K) (t : Table K V) (key : Q) : DR V := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  if index < 0 then throw .keyError else valAt t index.toNat

/-- `get(h::Dict{K,V}, key, default)`, `base/dict.jl:507-510`. -/
def getQ (c : Conv Q K) (t : Table K V) (key : Q) (default : V) : DR V := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  if index < 0 then pure default else valAt t index.toNat

/-- `get(default::Callable, h::Dict{K,V}, key)`, `base/dict.jl:529-532`:
`default()` is called only when the key is absent. -/
def getFQ (c : Conv Q K) (t : Table K V) (key : Q) (default : Unit → DR V) : DR V := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  if index < 0 then default () else valAt t index.toNat

/-- `haskey(h::Dict, key) = (ht_keyindex(h, key) >= 0)`, `base/dict.jl:553`. -/
def haskeyQ (c : Conv Q K) (t : Table K V) (key : Q) : DR Bool := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  pure (index ≥ 0)

/-- `in(key, v::KeySet{<:Any, <:Dict}) = (ht_keyindex(v.dict, key) >= 0)`, `base/dict.jl:554`. -/
def inKeySetQ (c : Conv Q K) (t : Table K V) (key : Q) : DR Bool := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  pure (index ≥ 0)

/-- Key at a filled index (`h.keys[index]::K`). -/
def keyAt (t : Table K V) (index : Nat) : DR K :=
  match t.keys index with
  | some k => pure k
  | none => throw .undefRef

/-- `getkey(h::Dict{K,V}, key, default)`, `base/dict.jl:575-578`. -/
def getkeyQ (c : Conv Q K) (t : Table K V) (key : Q) (default : K) : DR K := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  if index < 0 then pure default else keyAt t index.toNat

/-- `_pop!(h, index)`, `base/dict.jl:580-584`. -/
def popAt (t : Table K V) (index : Nat) : DR (V × Table K V) := do
  let val ← valAt t index
  pure (val, deleteAt t index)

/-- `pop!(h::Dict, key)`, `base/dict.jl:586-589`. -/
def popQ (c : Conv Q K) (t : Table K V) (key : Q) : DR (V × Table K V) := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  if index > 0 then popAt t index.toNat else throw .keyError

/-- `pop!(h::Dict, key, default)`, `base/dict.jl:615-618`. -/
def popDefaultQ (c : Conv Q K) (t : Table K V) (key : Q) (default : V) : DR (V × Table K V) := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  if index > 0 then popAt t index.toNat else pure (default, t)

/-- `delete!(h::Dict, key)`, `base/dict.jl:681-687`. -/
def deleteQ (c : Conv Q K) (t : Table K V) (key : Q) : DR (Table K V) := do
  let index ← htKeyindex t (c.hash key) (c.iseq key)
  if index > 0 then pure (deleteAt t index.toNat) else pure t

/-! ## Iteration, `base/dict.jl:689-723` -/

/-- `skip_deleted_floor!(h)`, `base/dict.jl:698-704`. -/
def skipDeletedFloor (t : Table K V) : Nat × Table K V :=
  let idx := skipDeleted t t.idxfloor
  (idx, if idx != 0 then { t with idxfloor := idx } else t)

/-- `_iterate_dict(t, i)`, `base/dict.jl:706`: `i == 0 ? nothing :
(Pair{K,V}(t.keys[i], t.vals[i]), i == typemax(Int) ? 0 : i+1)`. Indices are
below `2^62`, so `i == typemax(Int)` is false. -/
def iterateDict (t : Table K V) (i : Nat) : DR (Option ((K × V) × Nat)) :=
  if i == 0 then pure none else do
    let e ← entryAt t i
    pure (some (e, i + 1))

/-- `iterate(t::Dict) = _iterate_dict(t, skip_deleted(t, t.idxfloor))`, `base/dict.jl:707-709`. -/
def iterateFirst (t : Table K V) : DR (Option ((K × V) × Nat)) :=
  iterateDict t (skipDeleted t t.idxfloor)

/-- `iterate(t::Dict, i) = _iterate_dict(t, skip_deleted(t, i))`, `base/dict.jl:710`. -/
def iterateNext (t : Table K V) (i : Nat) : DR (Option ((K × V) × Nat)) :=
  iterateDict t (skipDeleted t i)

/-- `for x in t` from the state `i` of `iterate(t, i)`, with `left` steps of
fuel (each yield strictly increases the state). -/
def iterLoop (t : Table K V) : Nat → Nat → DR (List (K × V))
  | 0, _ => pure []
  | left + 1, i => do
    match ← iterateNext t i with
    | none => pure []
    | some (e, st) => do
      let rest ← iterLoop t left st
      pure (e :: rest)

/-- `collect(t)` through the iteration protocol: `iterate(t)` is
`iterate(t, t.idxfloor)` (`iterateFirst t = iterateNext t t.idxfloor`). -/
def collectDict (t : Table K V) : DR (List (K × V)) := iterLoop t (t.size + 1) t.idxfloor

/-- `isempty(t::Dict) = (t.count == 0)`, `base/dict.jl:712`. -/
def isemptyDict (t : Table K V) : Bool := t.count == 0

/-- `Iterators.only(t::Dict) = Iterators._only(t, first)`, `base/dict.jl:715`,
with `_only(x, first)` (`base/iterators.jl:1673-1678`): `length(x) != 1` throws
`ArgumentError`, else `first(x)`. -/
def onlyDict (t : Table K V) : DR (K × V) :=
  if dictLength t != 1 then throw .argumentError else do
    match ← iterateFirst t with
    | some (e, _) => pure e
    | none => throw .argumentError

/-- Whether an iterator over a `Dict` yields keys (`KeySet`) or values (`ValueIterator`). -/
inductive Part where
  | keys
  | vals
  deriving DecidableEq

/-- An element of `keys(d)` or `values(d)`. -/
def Part.Elem (K V : Type) : Part → Type
  | .keys => K
  | .vals => V

/-- `vals[i]` with `vals = T <: KeySet ? v.dict.keys : v.dict.vals`, `base/dict.jl:721-722`. -/
def partAt (t : Table K V) : (p : Part) → Nat → DR (p.Elem K V)
  | .keys, i => match t.keys i with
    | some k => pure k
    | none => throw .undefRef
  | .vals, i => match t.vals i with
    | some v => pure v
    | none => throw .undefRef

/-- `Base.iterate(v::Union{KeySet{<:Any,<:Dict}, ValueIterator{<:Dict}}, i = v.dict.idxfloor)`,
`base/dict.jl:717-723`. -/
def iteratePart (t : Table K V) (p : Part) (i : Nat) : DR (Option (p.Elem K V × Nat)) :=
  if i == 0 then pure none else
  let i := skipDeleted t i
  if i == 0 then pure none else do
    let x ← partAt t p i
    pure (some (x, i + 1))

/-- `collect(keys(d))` / `collect(values(d))` through `iteratePart` from `idxfloor`. -/
def partRun (t : Table K V) (p : Part) : Nat → Nat → DR (List (p.Elem K V))
  | 0, _ => throw .diverges
  | n + 1, i => do
    match ← iteratePart t p i with
    | none => pure []
    | some (x, j) => do
      let rest ← partRun t p n j
      pure (x :: rest)

def collectPart (t : Table K V) (p : Part) : DR (List (p.Elem K V)) :=
  partRun t p (t.size + 2) t.idxfloor

/-- `map!(f, iter::ValueIterator{<:Dict})`, `base/dict.jl:741-751`: for every
filled slot from `idxfloor` on, `vals[i] = f(vals[i])` (the store converts to
`V`; `f` here returns a `V` and does not touch the dictionary). -/
def mapValues (t : Table K V) (f : V → V) : Table K V :=
  (List.range' t.idxfloor (t.size + 1 - t.idxfloor)).foldl (fun t i =>
    if isFilledB (t.slots i) then
      { t with vals := upd t.vals i ((t.vals i).map f) }
    else t) t

/-- `reduce(::typeof(merge), items::Vector{<:Dict})`, `base/dict.jl:735-739`,
for dicts of one key and value type (so `K = mapreduce(keytype, promote_type,
items)` and `V` are that type; an empty `items` throws from `mapreduce`):
`reduce(merge!, items; init=Dict{K,V}())`. -/
def reduceMerge (o : KeyOps K) (items : List (Table K V)) : DR (Table K V) :=
  match items with
  | [] => throw .argumentError
  | _ => items.foldlM (fun acc d => dictMerge o acc d) Table.empty

end JuliaLean.DictsCov
