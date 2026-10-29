import JuliaLean.Core
import JuliaLean.Registry.Types

/-!
# Model of `base/dict.jl`

Typed models of the methods in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
-/

namespace JuliaLean.base.dict

open JuliaLean

/--
Julia source: base/dict.jl:65-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct Dict{K,V} <: AbstractDict{K,V}
    # Metadata: empty => 0x00, removed => 0x7f, full => 0b1[7 most significant hash bits]
    slots::Memory{UInt8}
    keys::Memory{K}
    vals::Memory{V}
    ndel::Int
    count::Int
    age::UInt
    idxfloor::Int  # an index <= the indices of all used slots
    maxprobe::Int
    popcursor::Int

    function Dict{K,V}() where V where K
        n = 0
        slots = Memory{UInt8}(undef,n)
        fill!(slots, 0x0)
        new(slots, Memory{K}(undef, n), Memory{V}(undef, n), 0, 0, 0, max(1, n), 0, 1)
    end
    function Dict{K,V}(d::Dict{K,V}) where V where K
        new(copy(d.slots), copy(d.keys), copy(d.vals), d.ndel, d.count, d.age,
            d.idxfloor, d.maxprobe, d.popcursor)
    end
    function Dict{K, V}(slots::Memory{UInt8}, keys::Memory{K}, vals::Memory{V}, ndel::Int, count::Int, age::UInt, idxfloor::Int, maxprobe::Int, popcursor::Int) where {K, V}
        new(slots, keys, vals, ndel, count, age, idxfloor, maxprobe, popcursor)
    end
end
```
-/
structure DictState (K V : Type) where
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

/--
Julia source: base/dict.jl:77-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Dict{K,V}() where V where K
        n = 0
        slots = Memory{UInt8}(undef,n)
        fill!(slots, 0x0)
        new(slots, Memory{K}(undef, n), Memory{V}(undef, n), 0, 0, 0, max(1, n), 0, 1)
    end
```
-/
def dictEmpty (K V : Type) : DictState K V :=
  ⟨0, fun _ => 0, fun _ => none, fun _ => none, 0, 0, JInt.wrap .u64 0, 1, 0, 1⟩

/--
Julia source: base/dict.jl:83-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Dict{K,V}(d::Dict{K,V}) where V where K
        new(copy(d.slots), copy(d.keys), copy(d.vals), d.ndel, d.count, d.age,
            d.idxfloor, d.maxprobe, d.popcursor)
    end
```
-/
def dictCopy {K V : Type} (copySlots : Nat → (Nat → Nat) → Nat → Nat)
    (copyKeys : Nat → (Nat → Option K) → Nat → Option K)
    (copyVals : Nat → (Nat → Option V) → Nat → Option V) (d : DictState K V) : DictState K V :=
  { d with slots := copySlots d.size d.slots,
           keys := copyKeys d.size d.keys,
           vals := copyVals d.size d.vals }

/--
Julia source: base/dict.jl:87-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Dict{K, V}(slots::Memory{UInt8}, keys::Memory{K}, vals::Memory{V}, ndel::Int, count::Int, age::UInt, idxfloor::Int, maxprobe::Int, popcursor::Int) where {K, V}
        new(slots, keys, vals, ndel, count, age, idxfloor, maxprobe, popcursor)
    end
```
-/
def dictRaw {K V : Type} (size : Nat) (slots : Nat → Nat) (keys : Nat → Option K)
    (vals : Nat → Option V) (ndel count : Nat) (age : JInt .u64)
    (idxfloor maxprobe popcursor : Nat) : DictState K V :=
  ⟨size, slots, keys, vals, ndel, count, age, idxfloor, maxprobe, popcursor⟩

/--
Julia source: base/dict.jl:27-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# These can be changed, to trade off better performance for space
const global maxallowedprobe = 16
const global maxprobeshift   = 6

```
-/
def maxallowedprobe : Nat := 16
def maxprobeshift : Nat := 6

/--
Julia source: base/dict.jl:123-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_shorthash7(hsh::UInt) = (hsh >> (8sizeof(UInt)-7))%UInt8 | 0x80
```
-/
def shorthash7 (hsh : JInt .u64) : Nat := Nat.lor ((hsh.val.toNat >>> 57) % 256) 0x80

/--
Julia source: base/dict.jl:128-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hashindex(key, sz::Integer)
    sz = Int(sz)::Int
    hsh = hash(key)::UInt
    idx = ((hsh % Int) & (sz-1)) + 1
    return idx, _shorthash7(hsh)
end
```
-/
def hashindex {K : Type} (hash : K → JInt .u64) (key : K) (sz : Nat) : Nat × Nat := Id.run do
  let hsh := hash key
  let idx := Nat.land hsh.val.toNat (sz - 1) + 1
  return (idx, shorthash7 hsh)

/--
Julia source: base/dict.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds isslotempty(h::Dict, i::Int) = h.slots[i] == 0x00
```
-/
def isslotempty {K V : Type} (h : DictState K V) (i : Nat) : Bool := h.slots i == 0

/--
Julia source: base/dict.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds isslotfilled(h::Dict, i::Int) = (h.slots[i] & 0x80) != 0
```
-/
def isslotfilled {K V : Type} (h : DictState K V) (i : Nat) : Bool := Nat.land (h.slots i) 0x80 != 0

/--
Julia source: base/dict.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds isslotmissing(h::Dict, i::Int) = h.slots[i] == 0x7f
```
-/
def isslotmissing {K V : Type} (h : DictState K V) (i : Nat) : Bool := h.slots i == 0x7f

inductive DictError where
  | keyError
  | keyTypeError
  | argumentError
  | undefRef
  | thrownDict
  | diverges
  | typeError
  deriving Repr, DecidableEq

universe u
abbrev DictResult (α : Type u) := Except DictError α

def nextIndex (size index : Nat) : Nat := Nat.land index (size - 1) + 1

def bumpAge (age : JInt .u64) : JInt .u64 := age + JInt.lit .u64 1

def updateAt {α : Type} (f : Nat → α) (i : Nat) (value : α) : Nat → α :=
  fun j => if j == i then value else f j

def intBits64 (x : Int) : Nat := (x % ((2 ^ 64 : Nat) : Int)).toNat

structure RehashAcc (K V : Type) where
  slots : Nat → Nat
  keys : Nat → Option K
  vals : Nat → Option V
  count : Nat
  maxprobe : Nat

def rehashProbe (slots : Nat → Nat) (newsize : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | remaining + 1, index =>
    if slots index == 0 then some index
    else rehashProbe slots newsize remaining (nextIndex newsize index)

def rehashCopyLoop {K V : Type} (hash : K → JInt .u64) (newsize : Nat)
    (oldslots : Nat → Nat) (oldkeys : Nat → Option K) (oldvals : Nat → Option V) :
    Nat → Nat → RehashAcc K V → DictResult (RehashAcc K V)
  | 0, _, acc => .ok acc
  | remaining + 1, i, acc => do
    if Nat.land (oldslots i) 0x80 != 0 then
      match oldkeys i, oldvals i with
      | some key, some value =>
        let (index0, _) := hashindex hash key newsize
        match rehashProbe acc.slots newsize newsize index0 with
        | none => .error .diverges
        | some index =>
          let probe := Nat.land (intBits64 ((index : Int) - (index0 : Int))) (newsize - 1)
          let acc : RehashAcc K V := RehashAcc.mk
            (updateAt acc.slots index (oldslots i))
            (updateAt acc.keys index (some key))
            (updateAt acc.vals index (some value))
            (acc.count + 1)
            (max acc.maxprobe probe)
          rehashCopyLoop hash newsize oldslots oldkeys oldvals remaining (i + 1) acc
      | _, _ => .error .undefRef
    else
      rehashCopyLoop hash newsize oldslots oldkeys oldvals remaining (i + 1) acc

/--
Julia source: base/dict.jl:139-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :none function rehash!(h::Dict{K,V}, newsz = length(h.keys)) where V where K
    olds = h.slots
    oldk = h.keys
    oldv = h.vals
    sz = length(olds)
    newsz = _tablesz(newsz)
    h.age += 1
    h.idxfloor = 1
    h.popcursor = 1
    if h.count == 0
        # TODO: tryresize
        h.slots = Memory{UInt8}(undef, newsz)
        fill!(h.slots, 0x0)
        h.keys = Memory{K}(undef, newsz)
        h.vals = Memory{V}(undef, newsz)
        h.ndel = 0
        h.maxprobe = 0
        return h
    end

    slots = Memory{UInt8}(undef, newsz)
    fill!(slots, 0x0)
    keys = Memory{K}(undef, newsz)
    vals = Memory{V}(undef, newsz)
    age0 = h.age
    count = 0
    maxprobe = 0

    for i = 1:sz
        @inbounds if (olds[i] & 0x80) != 0
            k = oldk[i]
            v = oldv[i]
            index, _ = hashindex(k, newsz)
            index0 = index
            while slots[index] != 0
                index = (index & (newsz-1)) + 1
            end
            probe = (index - index0) & (newsz-1)
            probe > maxprobe && (maxprobe = probe)
            slots[index] = olds[i]
            keys[index] = k
            vals[index] = v
            count += 1
        end
    end

    @assert h.age == age0 "Multiple concurrent writes to Dict detected!"
    h.age += 1
    h.slots = slots
    h.keys = keys
    h.vals = vals
    h.count = count
    h.ndel = 0
    h.maxprobe = maxprobe
    return h
end
```
-/
def rehash {K V : Type} (hash : K → JInt .u64) (tablesz : Nat → Nat)
    (h : DictState K V) (newsize0 : Nat) : DictResult (DictState K V) := do
  let oldslots := h.slots
  let oldkeys := h.keys
  let oldvals := h.vals
  let oldsize := h.size
  let newsize := tablesz newsize0
  let h := { h with age := bumpAge h.age, idxfloor := 1, popcursor := 1 }
  if h.count == 0 then
    let cleared : DictState K V := DictState.mk newsize (fun _ => 0) (fun _ => none)
      (fun _ => none) 0 h.count h.age h.idxfloor 0 h.popcursor
    .ok cleared
  else
    let initial : RehashAcc K V := RehashAcc.mk (fun _ => 0) (fun _ => none)
      (fun _ => none) 0 0
    let acc ← rehashCopyLoop hash newsize oldslots oldkeys oldvals oldsize 1 initial
    let result : DictState K V := DictState.mk newsize acc.slots acc.keys acc.vals
      0 acc.count (bumpAge h.age) 1 acc.maxprobe 1
    .ok result

/-- `min(max(newsz, length(d)), max_values(T)::Int)` of `sizehint!` on Julia `Int`. -/
def clampSizeHint (len maxValues : Nat) (requested : JInt .i64) : JInt .i64 :=
  JInt.wrap .i64 (min (max requested.val (len : Int)) (maxValues : Int))

/--
Julia source: base/dict.jl:196-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sizehint!(d::Dict{T}, newsz::Integer; shrink::Bool=true) where T
    newsz = Int(newsz)::Int
    oldsz = length(d.slots)
    # limit new element count to max_values of the key type
    newsz = min(max(newsz, length(d)), max_values(T)::Int)
    # need at least 1.5n space to hold n elements
    newsz = _tablesz(cld(3 * newsz, 2))
    return (shrink ? newsz == oldsz : newsz <= oldsz) ? d : rehash!(d, newsz)
end
```
-/
def sizehint {K V : Type} (hash : K → JInt .u64) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (d : DictState K V)
    (newsize : JInt .i64) (shrink : Bool) : DictResult (DictState K V) := do
  let oldsize := d.size
  let newsize := clampSizeHint d.count maxValues newsize
  let newsize := tablesz (cld (JInt.lit .i64 (3 * newsize.val))).val.toNat
  if (shrink && newsize == oldsize) || (!shrink && newsize ≤ oldsize) then
    .ok d
  else
    rehash hash tablesz d newsize

/--
Julia source: base/dict.jl:224-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(h::Dict{K,V}) where V where K
    fill!(h.slots, 0x0)
    sz = length(h.slots)
    for i in 1:sz
        unsetindex!(h.keys, i)
        unsetindex!(h.vals, i)
    end
    h.ndel = 0
    h.count = 0
    h.maxprobe = 0
    h.age += 1
    h.idxfloor = max(1, sz)
    h.popcursor = 1
    return h
end
```
-/
def emptyBang {K V : Type} (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) : DictState K V := Id.run do
  let mut keys := h.keys
  let mut vals := h.vals
  for i in [1:h.size + 1] do
    keys := unsetKey h.size keys i
    vals := unsetVal h.size vals i
  return DictState.mk h.size (fillSlots h.size 0 h.slots) keys vals 0 0
    (bumpAge h.age) (max 1 h.size) 0 1

/--
Julia source: base/dict.jl:712-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(t::Dict) = (t.count == 0)
```
-/
def isempty {K V : Type} (h : DictState K V) : Bool := h.count == 0

/--
Julia source: base/dict.jl:713-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::Dict) = t.count
```
-/
def length {K V : Type} (h : DictState K V) : Nat := h.count

/--
Julia source: base/dict.jl:241-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ht_keyindex(h::Dict{K,V}, key) where V where K
    isempty(h) && return -1
    sz = length(h.keys)
    iter = 0
    maxprobe = h.maxprobe
    maxprobe < sz || throw(h) # This error will never trigger, but is needed for terminates_locally to be valid
    index, sh = hashindex(key, sz)
    keys = h.keys

    @assume_effects :terminates_locally :noub @inbounds while true
        isslotempty(h,index) && return -1
        if sh == h.slots[index]
            k = keys[index]
            if (key ===  k || isequal(key, k))
                return index
            end
        end

        index = (index & (sz-1)) + 1
        (iter += 1) > maxprobe && return -1
    end
    # This line is unreachable
end
```
-/
def keyindexLoop {K V Q : Type} (matchesKey : Q → K → Bool) (query : Q)
    (h : DictState K V) (sh : Nat) : Nat → Nat → DictResult Int
  | 0, _ => .ok (-1)
  | remaining + 1, index => do
    if isslotempty h index then
      .ok (-1)
    else if sh == h.slots index then
      match h.keys index with
      | none => .error .undefRef
      | some stored =>
        if matchesKey query stored then .ok (index : Int)
        else keyindexLoop matchesKey query h sh remaining (nextIndex h.size index)
    else
      keyindexLoop matchesKey query h sh remaining (nextIndex h.size index)

def htKeyindex {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) : DictResult Int := do
  if isempty h then
    .ok (-1)
  else
    let size := h.size
    if !(h.maxprobe < size) then
      .error .thrownDict
    else
      let (index, sh) := hashindex hash key size
      keyindexLoop matchesKey key h sh (h.maxprobe + 1) index

inductive Probe1 where
  | found (index : Int)
  | broken (iter index : Nat) (avail : Int)

def keyindex2Loop1 {K V Q : Type} (matchesKey : Q → K → Bool) (query : Q)
    (h : DictState K V) (shortHash size : Nat) :
    Nat → Nat → Nat → Int → DictResult Probe1
  | 0, iter, index, avail => .ok (.broken iter index avail)
  | remaining + 1, iter, index, avail => do
    let slot := h.slots index
    if slot == 0 then
      .ok (.found (if avail < 0 then avail else -(index : Int)))
    else
      let avail := if slot == 0x7f && avail == 0 then -(index : Int) else avail
      let found ←
        if slot != 0x7f && slot == shortHash then
          match h.keys index with
          | none => .error .undefRef
          | some stored => .ok (matchesKey query stored)
        else
          .ok false
      if found then
        .ok (.found (index : Int))
      else
        let index := nextIndex size index
        let iter := iter + 1
        if iter > h.maxprobe then
          .ok (.broken iter index avail)
        else
          keyindex2Loop1 matchesKey query h shortHash size remaining iter index avail

def keyindex2Loop2 {K V : Type} (h : DictState K V) (size maxallowed : Nat) :
    Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | remaining + 1, iter, index =>
    if iter < maxallowed then
      if !isslotfilled h index then some (iter, index)
      else keyindex2Loop2 h size maxallowed remaining (iter + 1) (nextIndex size index)
    else
      none

/--
Julia source: base/dict.jl:270-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ht_keyindex2_shorthash!(h::Dict{K,V}, key) where V where K
    sz = length(h.keys)
    if sz == 0 # if Dict was empty resize and then return location to insert
        rehash!(h, 4)
        index, sh = hashindex(key, length(h.keys))
        return -index, sh
    end
    iter = 0
    maxprobe = h.maxprobe
    index, sh = hashindex(key, sz)
    avail = 0
    keys = h.keys

    @inbounds while true
        if isslotempty(h,index)
            return (avail < 0 ? avail : -index), sh
        end

        if isslotmissing(h,index)
            if avail == 0
                # found an available slot, but need to keep scanning
                # in case "key" already exists in a later collided slot.
                avail = -index
            end
        elseif h.slots[index] == sh
            k = keys[index]
            if key === k || isequal(key, k)
                return index, sh
            end
        end

        index = (index & (sz-1)) + 1
        iter += 1
        iter > maxprobe && break
    end

    avail < 0 && return avail, sh

    maxallowed = max(maxallowedprobe, sz>>maxprobeshift)
    # Check if key is not present, may need to keep searching to find slot
    @inbounds while iter < maxallowed
        if !isslotfilled(h,index)
            h.maxprobe = iter
            return -index, sh
        end
        index = (index & (sz-1)) + 1
        iter += 1
    end

    rehash!(h, h.count > 64000 ? sz*2 : sz*4)

    return ht_keyindex2_shorthash!(h, key)
end
```
-/
def htKeyindex2Loop {K V Q : Type} (hashStored : K → JInt .u64)
    (hashQuery : Q → JInt .u64) (matchesQuery : Q → K → Bool)
    (tablesz : Nat → Nat) : Nat → DictState K V → Q →
    DictResult (Int × Nat × DictState K V)
  | 0, _, _ => .error .diverges
  | fuel + 1, h, key => do
    let size := h.size
    if size == 0 then
      let h ← rehash hashStored tablesz h 4
      let (index, shortHash) := hashindex hashQuery key h.size
      .ok (-(index : Int), shortHash, h)
    else
      let (index, shortHash) := hashindex hashQuery key size
      match ← keyindex2Loop1 matchesQuery key h shortHash size (h.maxprobe + 1) 0 index 0 with
      | .found found => .ok (found, shortHash, h)
      | .broken iter index avail =>
        if avail < 0 then
          .ok (avail, shortHash, h)
        else
          let maxallowed := max maxallowedprobe (size >>> maxprobeshift)
          match keyindex2Loop2 h size maxallowed maxallowed iter index with
          | some (iter, index) =>
            .ok (-(index : Int), shortHash, { h with maxprobe := iter })
          | none =>
            let newsize := if h.count > 64000 then size * 2 else size * 4
            let h ← rehash hashStored tablesz h newsize
            htKeyindex2Loop hashStored hashQuery matchesQuery tablesz fuel h key

def htKeyindex2 {K V : Type} (hash : K → JInt .u64) (matchesKey : K → K → Bool)
    (tablesz : Nat → Nat) (h : DictState K V) (key : K) :
    DictResult (Int × Nat × DictState K V) :=
  htKeyindex2Loop hash hash matchesKey tablesz (h.size + 64) h key

def htKeyindex2Query {K V Q : Type} (hashStored : K → JInt .u64)
    (hashQuery : Q → JInt .u64) (matchesQuery : Q → K → Bool)
    (tablesz : Nat → Nat) (h : DictState K V) (key : Q) :
    DictResult (Int × Nat × DictState K V) :=
  htKeyindex2Loop hashStored hashQuery matchesQuery tablesz (h.size + 64) h key

/--
Julia source: base/dict.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ht_keyindex2!(h::Dict, key) = ht_keyindex2_shorthash!(h, key)[1]
```
-/
def htKeyindex2Bang {K V : Type} (hash : K → JInt .u64) (matchesKey : K → K → Bool)
    (tablesz : Nat → Nat) (h : DictState K V) (key : K) : DictResult (Int × DictState K V) := do
  let (index, _, h) ← htKeyindex2 hash matchesKey tablesz h key
  .ok (index, h)

/--
Julia source: base/dict.jl:327-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _setindex!(h::Dict, v, key, index, sh = _shorthash7(hash(key)))
    h.ndel -= isslotmissing(h, index)
    h.slots[index] = sh
    h.keys[index] = key
    h.vals[index] = v
    h.count += 1
    h.age += 1
    if index < h.idxfloor
        h.idxfloor = index
    end

    sz = length(h.keys)
    # Rehash now if necessary
    if (h.count + h.ndel)*3 > sz*2
        # > 2/3 full (including tombstones)
        rehash!(h, h.count > 64000 ? h.count*2 : max(h.count*4, 4))
    end
    nothing
end
```
-/
def setindexAt {K V : Type} (hash : K → JInt .u64) (tablesz : Nat → Nat)
    (h : DictState K V) (value : V) (key : K) (index shortHash : Nat) :
    DictResult (Unit × DictState K V) := do
  let ndel := h.ndel - if isslotmissing h index then 1 else 0
  let count := h.count + 1
  let h := DictState.mk h.size (updateAt h.slots index shortHash)
    (updateAt h.keys index (some key)) (updateAt h.vals index (some value))
    ndel count (bumpAge h.age) (min h.idxfloor index) h.maxprobe h.popcursor
  let size := h.size
  if (h.count + h.ndel) * 3 > size * 2 then
    let newsize := if h.count > 64000 then h.count * 2 else max (h.count * 4) 4
    let h ← rehash hash tablesz h newsize
    .ok ((), h)
  else
    .ok ((), h)

structure KeyConv (Q K : Type) where
  isa : Q → Option K
  convert : Q → DictResult K
  isequal : Q → K → Bool

structure ValueConv (W V : Type) where
  isa : W → Option V
  convert : W → DictResult V

def convertValue {W V : Type} (conv : ValueConv W V) (value : W) : DictResult V :=
  match conv.isa value with
  | some typed => .ok typed
  | none => conv.convert value

/--
Julia source: base/dict.jl:359-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(h::Dict{K,V}, v0, key::K) where V where K
    v = v0 isa V ? v0 : convert(V, v0)::V
    index, sh = ht_keyindex2_shorthash!(h, key)

    if index > 0
        h.age += 1
        @inbounds h.keys[index] = key
        @inbounds h.vals[index] = v
    else
        @inbounds _setindex!(h, v, key, -index, sh)
    end

    return h
end
```
-/
def setindexTyped {K V W : Type} (hash : K → JInt .u64) (matchesKey : K → K → Bool)
    (tablesz : Nat → Nat) (valueConv : ValueConv W V) (h : DictState K V)
    (value : W) (key : K) : DictResult (DictState K V) := do
  let value ← convertValue valueConv value
  let (index, shortHash, h) ← htKeyindex2 hash matchesKey tablesz h key
  if index > 0 then
    .ok (DictState.mk h.size h.slots (updateAt h.keys index.toNat (some key))
      (updateAt h.vals index.toNat (some value)) h.ndel h.count (bumpAge h.age)
      h.idxfloor h.maxprobe h.popcursor)
  else
    let (_, h) ← setindexAt hash tablesz h value key (-index).toNat shortHash
    .ok h

/--
Julia source: base/dict.jl:374-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(h::Dict{K,Any}, v, key::K) where K
    @nospecialize v
    index, sh = ht_keyindex2_shorthash!(h, key)

    if index > 0
        h.age += 1
        @inbounds h.keys[index] = key
        @inbounds h.vals[index] = v
    else
        @inbounds _setindex!(h, v, key, -index, sh)
    end

    return h
end
```
-/
def setindexAny {K V : Type} (hash : K → JInt .u64) (matchesKey : K → K → Bool)
    (tablesz : Nat → Nat) (h : DictState K V) (value : V) (key : K) :
    DictResult (DictState K V) := do
  let (index, shortHash, h) ← htKeyindex2 hash matchesKey tablesz h key
  if index > 0 then
    .ok (DictState.mk h.size h.slots (updateAt h.keys index.toNat (some key))
      (updateAt h.vals index.toNat (some value)) h.ndel h.count (bumpAge h.age)
      h.idxfloor h.maxprobe h.popcursor)
  else
    let (_, h) ← setindexAt hash tablesz h value key (-index).toNat shortHash
    .ok h
/--
Julia source: base/dict.jl:347-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(h::Dict{K,V}, v0, key0) where V where K
    if key0 isa K
        key = key0
    else
        key = convert(K, key0)::K
        if !(isequal(key, key0)::Bool)
            throw(KeyTypeError(K, key0))
        end
    end
    setindex!(h, v0, key)
end
```
-/
def setindexConv {K V Q W : Type} (hash : K → JInt .u64) (matchesKey : K → K → Bool)
    (tablesz : Nat → Nat) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (h : DictState K V) (value : W) (key0 : Q) : DictResult (DictState K V) := do
  let key ←
    match keyConv.isa key0 with
    | some key => .ok key
    | none => do
      let key ← keyConv.convert key0
      if keyConv.isequal key0 key then .ok key else .error .keyTypeError
  setindexTyped hash matchesKey tablesz valueConv h value key

def valAt {K V : Type} (h : DictState K V) (index : Nat) : DictResult V :=
  match h.vals index with
  | some value => .ok value
  | none => .error .undefRef

def keyAt {K V : Type} (h : DictState K V) (index : Nat) : DictResult K :=
  match h.keys index with
  | some key => .ok key
  | none => .error .undefRef


/--
Julia source: base/dict.jl:457-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(default::Callable, h::Dict{K,V}, key::K) where V where K
    index, sh = ht_keyindex2_shorthash!(h, key)

    index > 0 && return h.vals[index]

    age0 = h.age
    v = default()
    if !isa(v, V)
        v = convert(V, v)::V
    end
    if h.age != age0
        index, sh = ht_keyindex2_shorthash!(h, key)
    end
    if index > 0
        h.age += 1
        @inbounds h.keys[index] = key
        @inbounds h.vals[index] = v
    else
        @inbounds _setindex!(h, v, key, -index, sh)
    end
    return v
end
```
-/
def getBang {K V W : Type} (hash : K → JInt .u64) (matchesKey : K → K → Bool)
    (tablesz : Nat → Nat) (valueConv : ValueConv W V) (h : DictState K V)
    (key : K) (default : DictState K V → DictResult (W × DictState K V)) :
    DictResult (V × DictState K V) := do
  let (index0, shortHash0, h) ← htKeyindex2 hash matchesKey tablesz h key
  if index0 > 0 then
    let value ← valAt h index0.toNat
    .ok (value, h)
  else
    let age0 := h.age
    let (value0, h) ← default h
    let value ← convertValue valueConv value0
    let (index, shortHash, h) ←
      if h.age != age0 then htKeyindex2 hash matchesKey tablesz h key
      else .ok (index0, shortHash0, h)
    if index > 0 then
      let h := DictState.mk h.size h.slots (updateAt h.keys index.toNat (some key))
        (updateAt h.vals index.toNat (some value)) h.ndel h.count (bumpAge h.age)
        h.idxfloor h.maxprobe h.popcursor
      .ok (value, h)
    else
      let (_, h) ← setindexAt hash tablesz h value key (-index).toNat shortHash
      .ok (value, h)

/--
Julia source: base/dict.jl:445-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(default::Callable, h::Dict{K,V}, key0) where V where K
    if key0 isa K
        key = key0
    else
        key = convert(K, key0)::K
        if !isequal(key, key0)
            throw(KeyTypeError(K, key0))
        end
    end
    return get!(default, h, key)
end
```
-/
def getBangConv {K V Q W : Type} (hash : K → JInt .u64) (matchesKey : K → K → Bool)
    (tablesz : Nat → Nat) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (h : DictState K V) (key0 : Q)
    (default : DictState K V → DictResult (W × DictState K V)) :
    DictResult (V × DictState K V) := do
  let key ←
    match keyConv.isa key0 with
    | some key => .ok key
    | none => do
      let key ← keyConv.convert key0
      if keyConv.isequal key0 key then .ok key else .error .keyTypeError
  getBang hash matchesKey tablesz valueConv h key default

/--
Julia source: base/dict.jl:480-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(h::Dict{K,V}, key) where V where K
    index = ht_keyindex(h, key)
    return index < 0 ? throw(KeyError(key)) : @assume_effects :noub @inbounds h.vals[index]::V
end
```
-/
def getindex {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) : DictResult V := do
  let index ← htKeyindex hash matchesKey h key
  if index < 0 then .error .keyError else valAt h index.toNat

/--
Julia source: base/dict.jl:507-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(h::Dict{K,V}, key, default) where V where K
    index = ht_keyindex(h, key)
    @inbounds return (index < 0) ? default : h.vals[index]::V
end
```
-/
def get {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) (default : V) : DictResult V := do
  let index ← htKeyindex hash matchesKey h key
  if index < 0 then .ok default else valAt h index.toNat

/--
Julia source: base/dict.jl:529-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(default::Callable, h::Dict{K,V}, key) where V where K
    index = ht_keyindex(h, key)
    @inbounds return (index < 0) ? default() : h.vals[index]::V
end
```
-/
def getF {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) (default : Unit → DictResult V) : DictResult V := do
  let index ← htKeyindex hash matchesKey h key
  if index < 0 then default () else valAt h index.toNat

/--
Julia source: base/dict.jl:553-553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(h::Dict, key) = (ht_keyindex(h, key) >= 0)
```
-/
def haskey {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) : DictResult Bool := do
  let index ← htKeyindex hash matchesKey h key
  .ok (index >= 0)

structure KeySet (K V : Type) where
  dict : DictState K V

/--
Julia source: base/dict.jl:554-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(key, v::KeySet{<:Any, <:Dict}) = (ht_keyindex(v.dict, key) >= 0)
```
-/
def inKeySet {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (keys : KeySet K V) (key : Q) : DictResult Bool := do
  let index ← htKeyindex hash matchesKey keys.dict key
  .ok (index >= 0)

/--
Julia source: base/dict.jl:575-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getkey(h::Dict{K,V}, key, default) where V where K
    index = ht_keyindex(h, key)
    @inbounds return (index<0) ? default : h.keys[index]::K
end
```
-/
def getkey {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) (default : K) : DictResult K := do
  let index ← htKeyindex hash matchesKey h key
  if index < 0 then .ok default else keyAt h index.toNat

def previousIndex (size index : Nat) : Nat :=
  Nat.land (intBits64 ((index : Int) - 2)) (size - 1) + 1

def clearBackward (size : Nat) (slots : Nat → Nat) : Nat → Nat → Int →
    (Nat → Nat) × Int
  | 0, _, ndel => (slots, ndel)
  | remaining + 1, index, ndel =>
    let ndel := ndel - 1
    let slots := updateAt slots index 0
    let index := previousIndex size index
    if slots index == 0x7f then
      clearBackward size slots remaining index ndel
    else
      (slots, ndel)

/--
Julia source: base/dict.jl:631-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _delete!(h::Dict{K,V}, index) where {K,V}
    @inbounds begin
    slots = h.slots
    sz = length(slots)
    unsetindex!(h.keys, index)
    unsetindex!(h.vals, index)
    # if the next slot is empty we don't need a tombstone
    # and can remove all tombstones that were required by the element we just deleted
    ndel = 1
    nextind = (index & (sz-1)) + 1
    if isslotempty(h, nextind)
        while true
            ndel -= 1
            slots[index] = 0x00
            index = ((index - 2) & (sz-1)) + 1
            isslotmissing(h, index) || break
        end
    else
        slots[index] = 0x7f
    end
    h.ndel += ndel
    h.count -= 1
    h.age += 1
    return h
    end
end
```
-/
def deleteAt {K V : Type} (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (index : Nat) : DictState K V := Id.run do
  let size := h.size
  let keys := unsetKey size h.keys index
  let vals := unsetVal size h.vals index
  let nextind := nextIndex size index
  let (slots, extraDel) :=
    if isslotempty h nextind then
      clearBackward size h.slots size index 1
    else
      (updateAt h.slots index 0x7f, 1)
  let ndel := ((h.ndel : Int) + extraDel).toNat
  return DictState.mk size slots keys vals ndel (h.count - 1) (bumpAge h.age)
    h.idxfloor h.maxprobe h.popcursor

/--
Julia source: base/dict.jl:580-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _pop!(h::Dict, index)
    @inbounds val = h.vals[index]
    _delete!(h, index)
    return val
end
```
-/
def popAt {K V : Type} (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (index : Nat) : DictResult (V × DictState K V) := do
  let value ← valAt h index
  .ok (value, deleteAt unsetKey unsetVal h index)

/--
Julia source: base/dict.jl:586-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(h::Dict, key)
    index = ht_keyindex(h, key)
    return index > 0 ? _pop!(h, index) : throw(KeyError(key))
end
```
-/
def popKey {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (key : Q) : DictResult (V × DictState K V) := do
  let index ← htKeyindex hash matchesKey h key
  if index > 0 then popAt unsetKey unsetVal h index.toNat else .error .keyError

/--
Julia source: base/dict.jl:615-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(h::Dict, key, default)
    index = ht_keyindex(h, key)
    return index > 0 ? _pop!(h, index) : default
end
```
-/
def popDefault {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (key : Q) (default : V) : DictResult (V × DictState K V) := do
  let index ← htKeyindex hash matchesKey h key
  if index > 0 then popAt unsetKey unsetVal h index.toNat else .ok (default, h)

/--
Julia source: base/dict.jl:689-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function skip_deleted(h::Dict, i)
    L = length(h.slots)
    for i = i:L
        @inbounds if isslotfilled(h,i)
            return  i
        end
    end
    return 0
end
```
-/
def skipDeleted {K V : Type} (h : DictState K V) (i : Nat) : Nat :=
  let rec loop (remaining index : Nat) : Nat :=
    match remaining with
    | 0 => 0
    | n + 1 => if isslotfilled h index then index else loop n (index + 1)
  if i > h.size then 0 else loop (h.size - i + 1) i

/--
Julia source: base/dict.jl:698-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function skip_deleted_floor!(h::Dict)
    idx = skip_deleted(h, h.idxfloor)
    if idx != 0
        h.idxfloor = idx
    end
    idx
end
```
-/
def skipDeletedFloor {K V : Type} (h : DictState K V) : Nat × DictState K V :=
  let index := skipDeleted h h.idxfloor
  (index, if index != 0 then
    DictState.mk h.size h.slots h.keys h.vals h.ndel h.count h.age index h.maxprobe h.popcursor
   else h)

/--
Julia source: base/dict.jl:620-629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(h::Dict)
    isempty(h) && throw(ArgumentError("dict must be non-empty"))
    idx = skip_deleted(h, h.popcursor)
    idx == 0 && (idx = skip_deleted_floor!(h))
    h.popcursor = idx + 1
    @inbounds key = h.keys[idx]
    @inbounds val = h.vals[idx]
    _delete!(h, idx)
    key => val
end
```
-/
def popAny {K V : Type} (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) : DictResult ((K × V) × DictState K V) := do
  if isempty h then
    .error .argumentError
  else
    let index0 := skipDeleted h h.popcursor
    let (index, h) := if index0 == 0 then skipDeletedFloor h else (index0, h)
    let h := DictState.mk h.size h.slots h.keys h.vals h.ndel h.count h.age h.idxfloor
      h.maxprobe (index + 1)
    let key ← keyAt h index
    let (value, h) ← popAt unsetKey unsetVal h index
    .ok ((key, value), h)

/--
Julia source: base/dict.jl:681-687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function delete!(h::Dict, key)
    index = ht_keyindex(h, key)
    if index > 0
        _delete!(h, index)
    end
    return h
end
```
-/
def deleteKey {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (key : Q) : DictResult (DictState K V) := do
  let index ← htKeyindex hash matchesKey h key
  if index > 0 then .ok (deleteAt unsetKey unsetVal h index.toNat) else .ok h

/--
Julia source: base/dict.jl:706-710 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds _iterate_dict(t::Dict{K,V}, i) where {K,V} = i == 0 ? nothing : (Pair{K,V}(t.keys[i],t.vals[i]), i == typemax(Int) ? 0 : i+1)
@propagate_inbounds function iterate(t::Dict)
    _iterate_dict(t, skip_deleted(t, t.idxfloor))
end
@propagate_inbounds iterate(t::Dict, i) = _iterate_dict(t, skip_deleted(t, i))
```
-/
def iterateDict {K V : Type} (h : DictState K V) (i : Nat) :
    DictResult (Option ((K × V) × Nat)) := do
  if i == 0 then .ok none
  else
    let key ← keyAt h i
    let value ← valAt h i
    let next := if i == 2 ^ 63 - 1 then 0 else i + 1
    .ok (some ((key, value), next))

/-- `iterate(t::Dict)`, `base/dict.jl:707-709`. -/
def iterateFirst {K V : Type} (h : DictState K V) : DictResult (Option ((K × V) × Nat)) :=
  iterateDict h (skipDeleted h h.idxfloor)

/-- `iterate(t::Dict, i)`, `base/dict.jl:710`. -/
def iterateNext {K V : Type} (h : DictState K V) (i : Nat) :
    DictResult (Option ((K × V) × Nat)) :=
  iterateDict h (skipDeleted h i)

/--
Julia source: base/dict.jl:715-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds Iterators.only(t::Dict) = Iterators._only(t, first)
```
-/
def onlyDict {K V : Type}
    (only : DictState K V → (DictState K V → DictResult (K × V)) → DictResult (K × V))
    (first : DictState K V → DictResult (K × V)) (h : DictState K V) : DictResult (K × V) :=
  only h first

inductive DictPart where
  | keys
  | vals
  deriving DecidableEq

def DictPart.Elem (K V : Type) : DictPart → Type
  | .keys => K
  | .vals => V

structure ValueIterator (K V : Type) where
  dict : DictState K V

def partAt {K V : Type} (h : DictState K V) :
    (part : DictPart) → Nat → DictResult (part.Elem K V)
  | .keys, index => keyAt h index
  | .vals, index => valAt h index

/--
Julia source: base/dict.jl:717-723 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function Base.iterate(v::T, i::Int = v.dict.idxfloor) where T <: Union{KeySet{<:Any, <:Dict}, ValueIterator{<:Dict}}
    i == 0 && return nothing
    i = skip_deleted(v.dict, i)
    i == 0 && return nothing
    vals = T <: KeySet ? v.dict.keys : v.dict.vals
    (@inbounds vals[i], i == typemax(Int) ? 0 : i+1)
end
```
-/
def iteratePart {K V : Type} (h : DictState K V) (part : DictPart) (i : Nat) :
    DictResult (Option (part.Elem K V × Nat)) := do
  if i == 0 then .ok none
  else
    let index := skipDeleted h i
    if index == 0 then .ok none
    else
      let value ← partAt h part index
      let next := if index == 2 ^ 63 - 1 then 0 else index + 1
      .ok (some (value, next))

abbrev JAny := Unit

/--
Julia source: base/dict.jl:91-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Dict{K,V}(kv) where V where K
    h = Dict{K,V}()
    haslength(kv) && sizehint!(h, Int(length(kv))::Int)
    for (k,v) in kv
        h[k] = v
    end
    return h
end
```
-/
def dictFromIterator {K V Q W : Type} (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat) (maxValues : Nat)
    (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (hasLength : Bool) (pairs : List (Q × W)) : DictResult (DictState K V) := do
  let h := dictEmpty K V
  let h ← if hasLength then
    sizehint hash tablesz maxValues cld h (JInt.lit .i64 (Int.ofNat pairs.length)) true
    else .ok h
  let rec insert : List (Q × W) → DictState K V → DictResult (DictState K V)
    | [], h => .ok h
    | (key, value) :: rest, h => do
      let h ← setindexConv hash matchesKey tablesz keyConv valueConv h value key
      insert rest h
  insert pairs h

/--
Julia source: base/dict.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Dict{K,V}(p::Pair) where {K,V} = setindex!(Dict{K,V}(), p.second, p.first)
```
-/
def dictFromPair {K V Q W : Type} (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pair : Q × W) :
    DictResult (DictState K V) :=
  setindexConv hash matchesKey tablesz keyConv valueConv (dictEmpty K V) pair.2 pair.1

/--
Julia source: base/dict.jl:100-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Dict{K,V}(ps::Pair...) where V where K
    h = Dict{K,V}()
    sizehint!(h, length(ps))
    for p in ps
        h[p.first] = p.second
    end
    return h
end
```
-/
def dictFromPairs {K V Q W : Type} (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat) (maxValues : Nat)
    (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (pairs : List (Q × W)) : DictResult (DictState K V) := do
  let h ← sizehint hash tablesz maxValues cld (dictEmpty K V)
    (JInt.lit .i64 (Int.ofNat pairs.length)) true
  let rec insert : List (Q × W) → DictState K V → DictResult (DictState K V)
    | [], h => .ok h
    | pair :: rest, h => do
      let h ← setindexConv hash matchesKey tablesz keyConv valueConv h pair.2 pair.1
      insert rest h
  insert pairs h

/--
Julia source: base/dict.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Dict() = Dict{Any,Any}()
```
-/
def dictAny : DictState JAny JAny := dictEmpty JAny JAny

/--
Julia source: base/dict.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Dict(kv::Tuple{}) = Dict()
```
-/
def dictEmptyTuple (_ : Unit) : DictState JAny JAny := dictAny

/--
Julia source: base/dict.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(d::Dict) = Dict(d)
```
-/
def copyDict {K V : Type} (copySlots : Nat → (Nat → Nat) → Nat → Nat)
    (copyKeys : Nat → (Nat → Option K) → Nat → Option K)
    (copyVals : Nat → (Nat → Option V) → Nat → Option V) (d : DictState K V) :
    DictState K V :=
  dictCopy copySlots copyKeys copyVals d

/--
Julia source: base/dict.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Dict(ps::Pair{K,V}...) where {K,V} = Dict{K,V}(ps)
```
-/
def dictTypedPairs {K V Q W : Type} (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat) (maxValues : Nat)
    (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (pairs : List (Q × W)) : DictResult (DictState K V) :=
  dictFromIterator hash matchesKey tablesz maxValues cld keyConv valueConv true pairs

/--
Julia source: base/dict.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Dict(kv) = dict_with_eltype((K, V) -> Dict{K, V}, kv, eltype(kv))
```
-/
def dictInferred {I K V : Type} (eltype : I → Type)
    (dictWithEltype : I → Type → DictResult (DictState K V)) (kv : I) :
    DictResult (DictState K V) :=
  dictWithEltype kv (eltype kv)

/--
Julia source: base/dict.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Dict(ps::Pair...)                  = Dict(ps)
```
-/
def dictPairsGeneric {K V Q W : Type} (eltype : List (Q × W) → Type)
    (dictWithEltype : List (Q × W) → Type → DictResult (DictState K V))
    (pairs : List (Q × W)) : DictResult (DictState K V) :=
  dictInferred eltype dictWithEltype pairs

/--
Julia source: base/dict.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(a::AbstractDict, ::Type{K}, ::Type{V}) where {K, V} = Dict{K, V}()
```
-/
def emptyDict {C : Type} (K V : Type) (_ : C) : DictState K V := dictEmpty K V

def filterLoop {K V : Type} (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (predicate : K × V → Bool) (h : DictState K V) :
    Nat → Nat → DictResult (DictState K V)
  | 0, _ => .ok h
  | remaining + 1, i => do
    if isslotfilled h i then
      let key ← keyAt h i
      let value ← valAt h i
      let h := if predicate (key, value) then h else deleteAt unsetKey unsetVal h i
      filterLoop unsetKey unsetVal predicate h remaining (i + 1)
    else
      filterLoop unsetKey unsetVal predicate h remaining (i + 1)

/--
Julia source: base/dict.jl:725-733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter!(pred, h::Dict{K,V}) where {K,V}
    h.count == 0 && return h
    @inbounds for i=1:length(h.slots)
        if ((h.slots[i] & 0x80) != 0) && !pred(Pair{K,V}(h.keys[i], h.vals[i]))
            _delete!(h, i)
        end
    end
    return h
end
```
-/
def filterBang {K V : Type}
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (predicate : K × V → Bool) (h : DictState K V) : DictResult (DictState K V) := do
  if h.count == 0 then
    .ok h
  else
    filterLoop unsetKey unsetVal predicate h h.size 1

def mapValuesLoop {K V : Type} (f : V → DictResult V) (h : DictState K V) :
    Nat → Nat → DictResult (DictState K V)
  | 0, _ => .ok h
  | remaining + 1, index => do
    if isslotfilled h index then
      let value ← valAt h index
      let value ← f value
      let h := DictState.mk h.size h.slots h.keys (updateAt h.vals index (some value))
        h.ndel h.count h.age h.idxfloor h.maxprobe h.popcursor
      mapValuesLoop f h remaining (index + 1)
    else
      mapValuesLoop f h remaining (index + 1)

/--
Julia source: base/dict.jl:741-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map!(f, iter::ValueIterator{<:Dict})
    dict = iter.dict
    vals = dict.vals
    # @inbounds is here so that it gets propagated to isslotfilled
    @inbounds for i = dict.idxfloor:lastindex(vals)
        if isslotfilled(dict, i)
            vals[i] = f(vals[i])
        end
    end
    return iter
end
```
-/
def mapBang {K V : Type} (f : V → DictResult V) (iter : ValueIterator K V) :
    DictResult (ValueIterator K V) := do
  let h := iter.dict
  let h ←
    if h.idxfloor > h.size then .ok h
    else mapValuesLoop f h (h.size - h.idxfloor + 1) h.idxfloor
  .ok ⟨h⟩
abbrev ImmutableDict (K V : Type) := List (K × V)

/--
Julia source: base/dict.jl:780-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ImmutableDict{K,V}() where {K,V} = new() # represents an empty dictionary
```
-/
def immutableEmpty (K V : Type) : ImmutableDict K V := []

/-- Conversion of a value already of the field type `T` (`convert(::Type{T}, x::T) = x`). -/
def fieldConv (T : Type) : ValueConv T T := ⟨some, .ok⟩

/--
Julia source: base/dict.jl:782-782 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ImmutableDict{K,V}(parent::ImmutableDict, key, value) where {K,V} = new(parent, key, value)
```
-/
def immutablePrepend {K V Q W : Type} (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (parent : ImmutableDict K V) (key : Q) (value : W) : DictResult (ImmutableDict K V) := do
  let key ← convertValue keyConv key
  let value ← convertValue valueConv value
  .ok ((key, value) :: parent)

/--
Julia source: base/dict.jl:781-781 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ImmutableDict{K,V}(key, value) where {K,V} = (empty = new(); new(empty, key, value))
```
-/
def immutableSingleton {K V Q W : Type} (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (key : Q) (value : W) : DictResult (ImmutableDict K V) :=
  let empty := immutableEmpty K V
  immutablePrepend keyConv valueConv empty key value

/--
Julia source: base/dict.jl:811-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ImmutableDict(KV::Pair{K,V}) where {K,V} = ImmutableDict{K,V}(KV[1], KV[2])
```
-/
def immutableFromPair {K V : Type} (pair : K × V) : DictResult (ImmutableDict K V) :=
  immutableSingleton (fieldConv K) (fieldConv V) pair.1 pair.2

/--
Julia source: base/dict.jl:812-812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ImmutableDict(t::ImmutableDict{K,V}, KV::Pair) where {K,V} = ImmutableDict{K,V}(t, KV[1], KV[2])
```
-/
def immutableExtend {K V Q W : Type} (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (dict : ImmutableDict K V) (pair : Q × W) : DictResult (ImmutableDict K V) :=
  immutablePrepend keyConv valueConv dict pair.1 pair.2

/--
Julia source: base/dict.jl:813-814 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ImmutableDict(t::ImmutableDict{K,V}, KV::Pair, rest::Pair...) where {K,V} =
    ImmutableDict(ImmutableDict(t, KV), rest...)
```
-/
def immutableExtendMany {K V Q W : Type} (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (dict : ImmutableDict K V) : List (Q × W) → DictResult (ImmutableDict K V)
  | [] => .ok dict
  | pair :: rest => do
    let dict ← immutableExtend keyConv valueConv dict pair
    immutableExtendMany keyConv valueConv dict rest

/--
Julia source: base/dict.jl:815-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ImmutableDict(KV::Pair, rest::Pair...) = ImmutableDict(ImmutableDict(KV), rest...)
```
-/
def immutableFromPairs {K V Q W : Type} (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (first : K × V) (rest : List (Q × W)) : DictResult (ImmutableDict K V) := do
  let dict ← immutableFromPair first
  immutableExtendMany keyConv valueConv dict rest

/--
Julia source: base/dict.jl:817-826 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function in(key_value::Pair, dict::ImmutableDict, valcmp=(==))
    key, value = key_value
    while isdefined(dict, :parent)
        if isequal(dict.key, key)
            valcmp(value, dict.value) && return true
        end
        dict = dict.parent
    end
    return false
end
```
-/
def immutableIn {K V Q W : Type} (eqKey : K → Q → Bool)
    (valueEq : W → V → DictResult (Option Bool)) (query : Q × W) :
    ImmutableDict K V → DictResult (Option Bool)
  | [] => .ok (some false)
  | (key, value) :: rest => do
    if eqKey key query.1 then
      match ← valueEq query.2 value with
      | some true => .ok (some true)
      | some false => immutableIn eqKey valueEq query rest
      | none => .error .typeError
    else
      immutableIn eqKey valueEq query rest

/--
Julia source: base/dict.jl:828-834 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function haskey(dict::ImmutableDict, key)
    while isdefined(dict, :parent)
        isequal(dict.key, key) && return true
        dict = dict.parent
    end
    return false
end
```
-/
def immutableHasKey {K V Q : Type} (eqKey : K → Q → Bool) :
    ImmutableDict K V → Q → Bool
  | [], _ => false
  | (key, _) :: rest, query => eqKey key query || immutableHasKey eqKey rest query

/--
Julia source: base/dict.jl:836-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(dict::ImmutableDict, key)
    while isdefined(dict, :parent)
        isequal(dict.key, key) && return dict.value
        dict = dict.parent
    end
    throw(KeyError(key))
end
```
-/
def immutableGetindex {K V Q : Type} (eqKey : K → Q → Bool) :
    ImmutableDict K V → Q → DictResult V
  | [], _ => .error .keyError
  | (key, value) :: rest, query =>
    if eqKey key query then .ok value else immutableGetindex eqKey rest query

/--
Julia source: base/dict.jl:843-849 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(dict::ImmutableDict, key, default)
    while isdefined(dict, :parent)
        isequal(dict.key, key) && return dict.value
        dict = dict.parent
    end
    return default
end
```
-/
def immutableGet {K V Q : Type} (eqKey : K → Q → Bool) :
    ImmutableDict K V → Q → V → V
  | [], _, default => default
  | (key, value) :: rest, query, default =>
    if eqKey key query then value else immutableGet eqKey rest query default

/--
Julia source: base/dict.jl:851-857 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(default::Callable, dict::ImmutableDict, key)
    while isdefined(dict, :parent)
        isequal(dict.key, key) && return dict.value
        dict = dict.parent
    end
    return default()
end
```
-/
def immutableGetF {K V Q : Type} (eqKey : K → Q → Bool) :
    ImmutableDict K V → Q → (Unit → V) → V
  | [], _, default => default ()
  | (key, value) :: rest, query, default =>
    if eqKey key query then value else immutableGetF eqKey rest query default

/--
Julia source: base/dict.jl:860-863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(d::ImmutableDict{K,V}, t=d) where {K, V}
    !isdefined(t, :parent) && return nothing
    (Pair{K,V}(t.key, t.value), t.parent)
end
```
-/
def immutableIterate {K V : Type} : ImmutableDict K V → Option ((K × V) × ImmutableDict K V)
  | [] => none
  | pair :: rest => some (pair, rest)

/--
Julia source: base/dict.jl:864-864 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::ImmutableDict) = count(Returns(true), t)
```
-/
def immutableLength {K V : Type} (count : (K × V → Bool) → ImmutableDict K V → Nat)
    (dict : ImmutableDict K V) : Nat :=
  count (fun _ => true) dict

/--
Julia source: base/dict.jl:865-865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(t::ImmutableDict) = !isdefined(t, :parent)
```
-/
def immutableIsEmpty {K V : Type} (dict : ImmutableDict K V) : Bool := dict.isEmpty

/--
Julia source: base/dict.jl:866-866 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(::ImmutableDict, ::Type{K}, ::Type{V}) where {K, V} = ImmutableDict{K,V}()
```
-/
def immutableEmptyLike (K V : Type) (_ : ImmutableDict K V) : ImmutableDict K V :=
  immutableEmpty K V

/--
Julia source: base/dict.jl:886-888 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex(d::ImmutableDict, value, key)
    ImmutableDict(d, key => value)
end
```
-/
def setindexImmutable {K V Q W : Type} (keyConv : ValueConv Q K)
    (valueConv : ValueConv W V) (d : ImmutableDict K V) (value : W) (key : Q) :
    DictResult (ImmutableDict K V) :=
  immutableExtend keyConv valueConv d (key, value)

/--
Julia source: base/dict.jl:890-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractDict, ::Type{Pair{K,V}}, itr, isz, len) where {K, V} = empty(c, K, V)
```
-/
def similarForPairs {C D : Type} (empty : C → D) (c : C) : D :=
  empty c

/--
Julia source: base/dict.jl:891-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractDict, ::Type{T}, itr, isz, len) where {T} =
    throw(ArgumentError("for AbstractDicts, similar requires an element type of Pair;\n  if calling map, consider a comprehension instead"))
```
-/
def similarForOther {C D : Type} (_ : C) : DictResult D :=
  .error .argumentError

structure DictShowOps (C D K V : Type) where
  ioContext : C → D → C
  getLimit : C → Bool
  typePrefix : C → D → String
  isEmpty : D → Bool
  circular : C → D → Bool
  pairs : D → List (K × V)
  showPair : C → K × V → String

/--
Julia source: base/dict.jl:3-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, t::AbstractDict{K,V}) where V where K
    recur_io = IOContext(io, :SHOWN_SET => t,
                             :typeinfo => eltype(t))

    limit = get(io, :limit, false)::Bool
    # show in a Julia-syntax-like form: Dict(k=>v, ...)
    print(io, typeinfo_prefix(io, t)[1])
    print(io, '(')
    if !isempty(t) && !show_circular(io, t)
        first = true
        n = 0
        for pair in t
            first || print(io, ", ")
            first = false
            show(recur_io, pair)
            n+=1
            limit && n >= 10 && (print(io, "…"); break)
        end
    end
    print(io, ')')
end
```
-/
def showDict {C D K V : Type} (ops : DictShowOps C D K V) (io : C) (dict : D) :
    List String := Id.run do
  let recurIo := ops.ioContext io dict
  let limit := ops.getLimit io
  let mut output : List String := []
  output := output ++ [ops.typePrefix io dict]
  output := output ++ ["("]
  if !ops.isEmpty dict && !ops.circular io dict then
    let mut first := true
    let mut n := 0
    for pair in ops.pairs dict do
      if !first then
        output := output ++ [", "]
      first := false
      output := output ++ [ops.showPair recurIo pair]
      n := n + 1
      if limit && n >= 10 then
        output := output ++ ["…"]
        break
  output := output ++ [")"]
  return output

def mergewithLoop {K V Q W : Type} (hashStored : K → JInt .u64)
    (hashQuery : Q → JInt .u64) (matchesQuery : Q → K → Bool)
    (tablesz : Nat → Nat) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combine : V → W → DictResult V) (d1 : DictState K V) :
    List (Q × W) → DictResult (DictState K V)
  | [] => .ok d1
  | (key, value) :: rest => do
    let (index, shortHash, d1) ← htKeyindex2Query hashStored hashQuery matchesQuery tablesz d1 key
    if index > 0 then
      let oldValue ← valAt d1 index.toNat
      let newValue ← combine oldValue value
      let d1 := DictState.mk d1.size d1.slots d1.keys
        (updateAt d1.vals index.toNat (some newValue)) d1.ndel d1.count d1.age
        d1.idxfloor d1.maxprobe d1.popcursor
      mergewithLoop hashStored hashQuery matchesQuery tablesz keyConv valueConv combine d1 rest
    else
      let key ←
        match keyConv.isa key with
        | some key => .ok key
        | none => do
          let converted ← keyConv.convert key
          if keyConv.isequal key converted then .ok converted else .error .keyTypeError
      let value ← convertValue valueConv value
      let (_, d1) ← setindexAt hashStored tablesz d1 value key (-index).toNat shortHash
      mergewithLoop hashStored hashQuery matchesQuery tablesz keyConv valueConv combine d1 rest

/--
Julia source: base/dict.jl:753-774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mergewith!(combine, d1::Dict{K, V}, d2::AbstractDict) where {K, V}
    haslength(d2) && sizehint!(d1, length(d1) + length(d2), shrink=false)
    for (k, v) in d2
        i, sh = ht_keyindex2_shorthash!(d1, k)
        if i > 0
            d1.vals[i] = combine(d1.vals[i], v)
        else
            if !(k isa K)
                k1 = convert(K, k)::K
                if !isequal(k, k1)
                    throw(KeyTypeError(K, k))
                end
                k = k1
            end
            if !isa(v, V)
                v = convert(V, v)::V
            end
            @inbounds _setindex!(d1, v, k, -i, sh)
        end
    end
    return d1
end
```
-/
def mergewithBang {K V Q W : Type} (hashStored : K → JInt .u64)
    (hashQuery : Q → JInt .u64) (matchesQuery : Q → K → Bool)
    (tablesz : Nat → Nat) (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combine : V → W → DictResult V) (hasLength : Bool) (d1 : DictState K V)
    (d2 : List (Q × W)) : DictResult (DictState K V) := do
  let d1 ←
    if hasLength then
      sizehint hashStored tablesz maxValues cld d1
        (JInt.lit .i64 (Int.ofNat (d1.count + d2.length))) false
    else .ok d1
  mergewithLoop hashStored hashQuery matchesQuery tablesz keyConv valueConv combine d1 d2

/--
Julia source: base/dict.jl:735-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reduce(::typeof(merge), items::Vector{<:Dict})
    K = mapreduce(keytype, promote_type, items)
    V = mapreduce(valtype, promote_type, items)
    return reduce(merge!, items; init=Dict{K,V}())
end
```
-/
def reduceMerge {D : Type} (keytype valtype : D → Type)
    (promoteType : Type → Type → Type)
    (mapreduce : (D → Type) → (Type → Type → Type) → List D → DictResult Type)
    (mergeItems : {K V : Type} → List D → DictState K V → DictResult (DictState K V))
    (items : List D) : DictResult (Σ K : Type, Σ V : Type, DictState K V) :=
  match mapreduce keytype promoteType items with
  | .error e => .error e
  | .ok K =>
    match mapreduce valtype promoteType items with
    | .error e => .error e
    | .ok V =>
      match mergeItems items (dictEmpty K V) with
      | .error e => .error e
      | .ok h => .ok ⟨K, V, h⟩
structure PersistentDict (K V H : Type) where
  trie : H

structure TriePath (H HS : Type) where
  found : Bool
  present : Bool
  trie : H
  index : Nat
  bitmapIndex : Nat
  top : H
  state : HS

/-- The `HAMT` operations of `base/hamt.jl` (not modelled here) used by a `PersistentDict{K,V}`
call whose key argument has type `Q` and whose value argument has type `W`: `HashState(key)`,
`HAMT{K,V}(key => val)` and `insert!` convert or compare these arguments. Typed methods
(`key::K`, `val::V`) use an instance with `Q = K` and `W = V`. -/
structure PersistentOps (K V Q W H HS S : Type) where
  empty : Unit → H
  singleton : Q × W → DictResult H
  hashState : Q → HS
  path : H → HS → Bool → TriePath H HS
  insert : H → H → Bool → Bool → Nat → Nat → HS → W → DictResult H
  deleteAt : H → H → Nat → H
  unset : H → H → Nat → H
  isLevelEmpty : H → Bool
  leafValue : H → Nat → Option V
  iterate : H → Option S → Option ((K × V) × S)
  length : H → Nat
  isEmpty : H → Bool

/--
Julia source: base/dict.jl:903-905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline function KeyValue.set(::Type{PersistentDict{K, V}}) where {K, V}
        new{K, V}(HAMT.HAMT{K,V}())
    end
```
-/
def persistentEmpty {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S) :
    PersistentDict K V H :=
  ⟨ops.empty ()⟩

/--
Julia source: base/dict.jl:906-908 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline function KeyValue.set(::Type{PersistentDict{K, V}}, ::Nothing, key, val) where {K, V}
        new{K, V}(HAMT.HAMT{K, V}(key => val))
    end
```
-/
def persistentSingleton {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (key : Q) (value : W) : DictResult (PersistentDict K V H) := do
  let trie ← ops.singleton (key, value)
  .ok ⟨trie⟩

/--
Julia source: base/dict.jl:913-919 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global function _keyvalueset(dict::PersistentDict{K, V}, key, @nospecialize(val)) where {K, V}
        trie = dict.trie
        h = HAMT.HashState(key)
        found, present, trie, i, bi, top, hs = HAMT.path(trie, h, #=persistent=#true)
        HAMT.insert!(found, present, trie, i, bi, hs, val)
        return new{K, V}(top)
    end
```
-/
def persistentInsert {K V Q W H HS S : Type}
    (ops : PersistentOps K V Q W H HS S) (dict : PersistentDict K V H)
    (key : Q) (value : W) : DictResult (PersistentDict K V H) := do
  let trie := dict.trie
  let h := ops.hashState key
  let path := ops.path trie h true
  let top ← ops.insert path.top path.trie path.found path.present path.index
    path.bitmapIndex path.state value
  .ok ⟨top⟩

/--
Julia source: base/dict.jl:909-910 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline Base.@assume_effects :effect_free :terminates_globally KeyValue.set(
        dict::PersistentDict{K, V}, key, val) where {K, V} = @inline _keyvalueset(dict, key, val)
```
-/
def persistentSet {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (key : Q) (value : W) :
    DictResult (PersistentDict K V H) :=
  persistentInsert ops dict key value
/--
Julia source: base/dict.jl:911-912 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline Base.@assume_effects :nothrow :effect_free :terminates_globally KeyValue.set(
        dict::PersistentDict{K, V}, key::K, val::V) where {K, V} = @inline _keyvalueset(dict, key, val)
```
-/
def persistentSetTyped {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) (value : V) :
    DictResult (PersistentDict K V H) :=
  persistentInsert ops dict key value

/--
Julia source: base/dict.jl:924-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global function _keyvalueset(dict::PersistentDict{K, V}, key) where {K, V}
        trie = dict.trie
        h = HAMT.HashState(key)
        found, present, trie, i, bi, top, _ = HAMT.path(trie, h, #=persistent=#true)
        if found && present
            deleteat!(trie.data, i)
            HAMT.unset!(trie, bi)
        end
        return new{K, V}(top)
    end
```
-/
def persistentDeleteKey {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (key : Q) : PersistentDict K V H := Id.run do
  let trie := dict.trie
  let h := ops.hashState key
  let path := ops.path trie h true
  let top :=
    if path.found && path.present then
      let top := ops.deleteAt path.top path.trie path.index
      ops.unset top path.trie path.bitmapIndex
    else
      path.top
  return ⟨top⟩

/--
Julia source: base/dict.jl:969-969 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PersistentDict{K,V}() where {K, V} = KeyValue.set(PersistentDict{K,V})
```
-/
def persistentEmptyConstructor {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S) :
    PersistentDict K V H :=
  persistentEmpty ops

/--
Julia source: base/dict.jl:970-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function PersistentDict{K,V}(KV::Pair) where {K,V}
    KeyValue.set(
        PersistentDict{K, V},
        nothing,
        KV...)
end
```
-/
def persistentTypedPair {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (pair : Q × W) : DictResult (PersistentDict K V H) :=
  persistentSingleton ops pair.1 pair.2

/--
Julia source: base/dict.jl:976-981 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function PersistentDict(KV::Pair{K,V}) where {K,V}
    KeyValue.set(
        PersistentDict{K, V},
        nothing,
        KV...)
end
```
-/
def persistentPair {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (pair : K × V) : DictResult (PersistentDict K V H) :=
  persistentSingleton ops pair.1 pair.2

/--
Julia source: base/dict.jl:986-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function PersistentDict(dict::PersistentDict{K,V}, key, val) where {K,V}
    key = convert(K, key)
    val = convert(V, val)
    return KeyValue.set(dict, key, val)
end
```
-/
def persistentExtend {K V H HS S Q W : Type} (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (dict : PersistentDict K V H) (key : Q) (value : W) :
    DictResult (PersistentDict K V H) := do
  let key ← keyConv.convert key
  let value ← valueConv.convert value
  persistentSetTyped ops dict key value

/--
Julia source: base/dict.jl:982-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PersistentDict(dict::PersistentDict, pair::Pair) = PersistentDict(dict, pair...)
```
-/
def persistentExtendPair {K V H HS S Q W : Type} (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (dict : PersistentDict K V H) (pair : Q × W) : DictResult (PersistentDict K V H) :=
  persistentExtend ops keyConv valueConv dict pair.1 pair.2

/--
Julia source: base/dict.jl:983-983 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PersistentDict{K,V}(dict::PersistentDict{K,V}, pair::Pair) where {K,V} = PersistentDict(dict, pair...)
```
-/
def persistentTypedExtendPair {K V H HS S Q W : Type} (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (dict : PersistentDict K V H) (pair : Q × W) : DictResult (PersistentDict K V H) :=
  persistentExtend ops keyConv valueConv dict pair.1 pair.2

def persistentExtendMany {K V H HS S Q W : Type} (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (dict : PersistentDict K V H) : List (Q × W) → DictResult (PersistentDict K V H)
  | [] => .ok dict
  | (key, value) :: rest => do
    let dict ← persistentExtend ops keyConv valueConv dict key value
    persistentExtendMany ops keyConv valueConv dict rest

/--
Julia source: base/dict.jl:992-998 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function PersistentDict{K,V}(KV::Pair, rest::Pair...) where {K,V}
    dict = PersistentDict{K,V}(KV)
    for (key, value) in rest
        dict = PersistentDict(dict, key, value)
    end
    return dict
end
```
-/
def persistentTypedPairs {K V H HS S HS' S' Q W : Type}
    (opsPair : PersistentOps K V Q W H HS' S') (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (key : Q) (value : W) (rest : List (Q × W)) : DictResult (PersistentDict K V H) := do
  let dict ← persistentTypedPair opsPair (key, value)
  persistentExtendMany ops keyConv valueConv dict rest

/--
Julia source: base/dict.jl:1000-1006 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function PersistentDict(kv::Pair, rest::Pair...)
    dict = PersistentDict(kv)
    for (key, value) in rest
        dict = PersistentDict(dict, key, value)
    end
    return dict
end
```
-/
def persistentPairs {K V H HS S Q W : Type} (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (first : K × V) (rest : List (Q × W)) : DictResult (PersistentDict K V H) := do
  let dict ← persistentPair ops first
  persistentExtendMany ops keyConv valueConv dict rest

/--
Julia source: base/dict.jl:1008-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::PersistentDict{K,V}) where {K,V} = Pair{K,V}
```
-/
def persistentEltype (K V : Type) : Type := K × V

/--
Julia source: base/dict.jl:1033-1045 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function KeyValue.get(dict::PersistentDict{K, V}, key) where {K, V}
    trie = dict.trie
    if HAMT.islevel_empty(trie)
        return nothing
    end
    h = HAMT.HashState(key)
    found, present, trie, i, _, _, _ = HAMT.path(trie, h)
    if found && present
        leaf = @inbounds trie.data[i]::HAMT.Leaf{K,V}
        return Some{V}(leaf.val)
    end
    return nothing
end
```
-/
def persistentKeyGet {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (key : Q) : Option V :=
  Id.run do
  let trie := dict.trie
  if ops.isLevelEmpty trie then
    return none
  let h := ops.hashState key
  let path := ops.path trie h false
  if path.found && path.present then
    return ops.leafValue path.trie path.index
  return none

/--
Julia source: base/dict.jl:1010-1015 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function in(key_val::Pair{K,V}, dict::PersistentDict{K,V}, valcmp=(==)) where {K,V}
    key, val = key_val
    found = KeyValue.get(dict, key)
    found === nothing && return false
    return valcmp(val, something(found))
end
```
-/
def persistentIn {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (valueEq : V → V → DictResult Bool) (dict : PersistentDict K V H)
    (pair : K × V) : DictResult Bool := do
  match persistentKeyGet ops dict pair.1 with
  | none => .ok false
  | some value => valueEq pair.2 value

/--
Julia source: base/dict.jl:1017-1019 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function haskey(dict::PersistentDict{K}, key::K) where K
    return KeyValue.get(dict, key) !== nothing
end
```
-/
def persistentHasKey {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) : Bool :=
  (persistentKeyGet ops dict key).isSome

/--
Julia source: base/dict.jl:1021-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(dict::PersistentDict{K,V}, key::K) where {K,V}
    found = KeyValue.get(dict, key)
    found === nothing && throw(KeyError(key))
    return something(found)
end
```
-/
def persistentGetindex {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) : DictResult V :=
  match persistentKeyGet ops dict key with
  | some value => .ok value
  | none => .error .keyError

/--
Julia source: base/dict.jl:1027-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(dict::PersistentDict{K,V}, key::K, default) where {K,V}
    found = KeyValue.get(dict, key)
    found === nothing && return default
    return something(found)
end
```
-/
def persistentGet {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) (default : V) : V :=
  (persistentKeyGet ops dict key).getD default

/--
Julia source: base/dict.jl:1047-1051 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function KeyValue.get(default, dict::PersistentDict, key)
    found = KeyValue.get(dict, key)
    found === nothing && return default()
    return something(found)
end
```
-/
def persistentGetDefault {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (key : Q) (default : Unit → DictResult V) :
    DictResult V := do
  match persistentKeyGet ops dict key with
  | none => default ()
  | some value => .ok value

/--
Julia source: base/dict.jl:1053-1057 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(default::Callable, dict::PersistentDict{K,V}, key::K) where {K,V}
    found = KeyValue.get(dict, key)
    found === nothing && return default()
    return something(found)
end
```
-/
def persistentGetTypedDefault {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) (default : Unit → DictResult V) :
    DictResult V := do
  match persistentKeyGet ops dict key with
  | none => default ()
  | some value => .ok value

/--
Julia source: base/dict.jl:920-921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline Base.@assume_effects :effect_free :terminates_globally KeyValue.set(
        dict::PersistentDict{K, V}, key) where {K, V} = @inline _keyvalueset(dict, key)
```
-/
def persistentSetDelete {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (key : Q) : PersistentDict K V H :=
  persistentDeleteKey ops dict key

/--
Julia source: base/dict.jl:922-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline Base.@assume_effects :nothrow :effect_free :terminates_globally KeyValue.set(
        dict::PersistentDict{K, V}, key::K) where {K, V} = @inline _keyvalueset(dict, key)
```
-/
def persistentSetTypedDelete {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) : PersistentDict K V H :=
  persistentDeleteKey ops dict key

/--
Julia source: base/dict.jl:1059-1061 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function delete(dict::PersistentDict{K}, key::K) where K
    return KeyValue.set(dict, key)
end
```
-/
def persistentDelete {K V H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) : PersistentDict K V H :=
  persistentSetTypedDelete ops dict key

/--
Julia source: base/dict.jl:1063-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(dict::PersistentDict, state=nothing) = HAMT.iterate(dict.trie, state)
```
-/
def persistentIterate {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (state : Option S) : Option ((K × V) × S) :=
  ops.iterate dict.trie state

/--
Julia source: base/dict.jl:1065-1065 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(dict::PersistentDict) = HAMT.length(dict.trie)
```
-/
def persistentLength {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) : Nat :=
  ops.length dict.trie

/--
Julia source: base/dict.jl:1066-1066 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(dict::PersistentDict) = HAMT.isempty(dict.trie)
```
-/
def persistentIsEmpty {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) : Bool :=
  ops.isEmpty dict.trie

/--
Julia source: base/dict.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(::PersistentDict, ::Type{K}, ::Type{V}) where {K, V} = PersistentDict{K, V}()
```
-/
def persistentEmptyLike {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (_ : PersistentDict K V H) : PersistentDict K V H :=
  persistentEmpty ops
/--
Julia source: base/dict.jl:1069-1069 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds Iterators.only(dict::PersistentDict) = Iterators._only(dict, first)
```
-/
def persistentOnly {K V H : Type}
    (only : PersistentDict K V H → (PersistentDict K V H → DictResult (K × V)) → DictResult (K × V))
    (first : PersistentDict K V H → DictResult (K × V))
    (dict : PersistentDict K V H) : DictResult (K × V) :=
  only dict first
end JuliaLean.base.dict
