import JuliaLean.Core
import JuliaLean.Runtime.Collections
import JuliaLean.base.abstractdict
import JuliaLean.base.iterators
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

inductive DictError where
  | keyError
  | keyTypeError
  | argumentError
  | undefRef
  | thrownDict
  | diverges
  | typeError
  | concurrentWrite
  | inexactError
  deriving Repr, DecidableEq

universe u
abbrev DictResult (α : Type u) := Except DictError α

/-- The `Int(x)::Int` call for an argument of an arbitrary Julia `Integer` type. -/
class DictInteger (I : Type) where
  toInt : I → DictResult (JInt .i64)

instance (priority := 1100) : DictInteger (JInt .i64) where
  toInt := .ok

instance (t : IntTy) : DictInteger (JInt t) where
  toInt x := (JInt.convert (IntTy.i64.name) .i64 x.val).mapError (fun _ => .inexactError)

instance : DictInteger Int where
  toInt x := (JInt.convert (IntTy.i64.name) .i64 x).mapError (fun _ => .inexactError)

instance : DictInteger Nat where
  toInt x := (JInt.convert (IntTy.i64.name) .i64 (Int.ofNat x)).mapError (fun _ => .inexactError)
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
def hashindex {K I : Type} [DictInteger I] (hash : K → JInt .u64) (key : K)
    (sz : I) : DictResult (Nat × Nat) := do
  let sz ← DictInteger.toInt sz
  let hsh := hash key
  let idx := Nat.land hsh.val.toNat (sz.val - 1).toNat + 1
  return (idx, shorthash7 hsh)

/-- dict.lean `hashindex` (dict.jl:128-133) whose `hash(key)::UInt` is the key's own
`hash`, which may throw (char.jl:271 converts a non-`Char` `AbstractChar` with `Char(x)`). -/
def hashindexM {K I E : Type} [DictInteger I] (liftD : DictError → E)
    (hash : K → Except E (JInt .u64)) (key : K) (sz : I) : Except E (Nat × Nat) := do
  let sz ← (DictInteger.toInt sz).mapError liftD
  let hsh ← hash key
  pure (Nat.land hsh.val.toNat (sz.val - 1).toNat + 1, shorthash7 hsh)

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


def nextIndex (size index : Nat) : Nat := Nat.land index (size - 1) + 1

def bumpAge (age : JInt .u64) : JInt .u64 := age + JInt.lit .u64 1

def updateAt {α : Type} (f : Nat → α) (i : Nat) (value : α) : Nat → α :=
  fun j => if j == i then value else f j

def intBits64 (size : Nat) (x : Int) : Nat := (if x < 0 then x + (size : Int) else x).toNat

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
        let (index0, _) ← hashindex hash key (JInt.lit .i64 (Int.ofNat newsize))
        match rehashProbe acc.slots newsize newsize index0 with
        | none => .error .diverges
        | some index =>
          let probe := Nat.land (intBits64 newsize ((index : Int) - (index0 : Int))) (newsize - 1)
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
    (h : DictState K V) (newsize0 : Nat := h.size)
    (observedAge : JInt .u64 := bumpAge h.age) : DictResult (DictState K V) := do
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
    let age0 := h.age
    let initial : RehashAcc K V := RehashAcc.mk (fun _ => 0) (fun _ => none)
      (fun _ => none) 0 0
    let acc ← rehashCopyLoop hash newsize oldslots oldkeys oldvals oldsize 1 initial
    if observedAge ≠ age0 then
      throw .concurrentWrite
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
def sizehint {K V I : Type} [DictInteger I] (hash : K → JInt .u64) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → DictResult (JInt .i64)) (d : DictState K V)
    (newsize : I) (shrink : Bool := true) : DictResult (DictState K V) := do
  let newsize ← DictInteger.toInt newsize
  let oldsize := d.size
  let newsize := clampSizeHint d.count maxValues newsize
  let cldSize ← cld (JInt.lit .i64 (3 * newsize.val))
  let newsize := tablesz cldSize.val.toNat
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
  let slots := fillSlots h.size 0 h.slots
  let sz := h.size
  let mut keys := h.keys
  let mut vals := h.vals
  for i in [1:sz + 1] do
    keys := unsetKey sz keys i
    vals := unsetVal sz vals i
  return DictState.mk sz slots keys vals 0 0 (bumpAge h.age) (max 1 sz) 0 1

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

/-- dict.lean `keyindexLoop` (dict.jl:250-261) whose `key === k || isequal(key, k)`
may throw. -/
def keyindexLoopM {K V Q E : Type} (liftD : DictError → E)
    (matchesKey : Q → K → Except E Bool) (query : Q) (h : DictState K V) (sh : Nat) :
    Nat → Nat → Except E Int
  | 0, _ => pure (-1)
  | remaining + 1, index => do
    if isslotempty h index then pure (-1)
    else if sh == h.slots index then
      match h.keys index with
      | none => throw (liftD .undefRef)
      | some stored =>
        if ← matchesKey query stored then pure (index : Int)
        else keyindexLoopM liftD matchesKey query h sh remaining (nextIndex h.size index)
    else keyindexLoopM liftD matchesKey query h sh remaining (nextIndex h.size index)

def htKeyindex {K V Q : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) : DictResult Int := do
  if isempty h then
    .ok (-1)
  else
    let size := h.size
    if !(h.maxprobe < size) then
      .error .thrownDict
    else
      let (index, sh) ← hashindex hash key (JInt.lit .i64 (Int.ofNat size))
      keyindexLoop matchesKey key h sh (h.maxprobe + 1) index

/-- dict.lean `htKeyindex` (dict.jl:241-263) with the throwing `hash` and key
comparison above. -/
def htKeyindexM {K V Q E : Type} (liftD : DictError → E) (hash : Q → Except E (JInt .u64))
    (matchesKey : Q → K → Except E Bool) (h : DictState K V) (key : Q) : Except E Int := do
  if isempty h then pure (-1)
  else
    let size := h.size
    if !(h.maxprobe < size) then throw (liftD .thrownDict)
    else
      let (index, sh) ← hashindexM liftD hash key (JInt.lit .i64 (Int.ofNat size))
      keyindexLoopM liftD matchesKey key h sh (h.maxprobe + 1) index

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
      let (index, shortHash) ← hashindex hashQuery key (JInt.lit .i64 (Int.ofNat h.size))
      .ok (-(index : Int), shortHash, h)
    else
      let (index, shortHash) ← hashindex hashQuery key (JInt.lit .i64 (Int.ofNat size))
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
    (h : DictState K V) (value : V) (key : K) (index : Nat)
    (shortHash : Nat := shorthash7 (hash key)) :
    DictResult (Unit × DictState K V) := do
  let ndel := h.ndel - if isslotmissing h index then 1 else 0
  let count := h.count + 1
  let h := DictState.mk h.size (updateAt h.slots index shortHash)
    (updateAt h.keys index (some key)) (updateAt h.vals index (some value))
    ndel count (bumpAge h.age) (min h.idxfloor index) h.maxprobe h.popcursor
  let size := h.size
  if (JInt.lit .i64 (Int.ofNat h.count) + JInt.lit .i64 (Int.ofNat h.ndel)) * JInt.lit .i64 3 >
      JInt.lit .i64 (Int.ofNat size) * JInt.lit .i64 2 then
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

def convertKey {Q K : Type} (conv : KeyConv Q K) (key : Q) : DictResult K :=
  match conv.isa key with
  | some key => .ok key
  | none =>
    match conv.convert key with
    | .ok converted => if conv.isequal key converted then .ok converted else .error .keyTypeError
    | .error e => .error e

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

class AnyValue (W V : Type) where
  toAny : W → V

instance {V : Type} : AnyValue V V where
  toAny v := v

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
def setindexAny {K V W : Type} [AnyValue W V] (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat) (h : DictState K V)
    (value : W) (key : K) : DictResult (DictState K V) := do
  let value := AnyValue.toAny value
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
def get {K V Q D : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) (default : D) : DictResult (V ⊕ D) := do
  let index ← htKeyindex hash matchesKey h key
  if index < 0 then .ok (.inr default) else .inl <$> valAt h index.toNat

/--
Julia source: base/dict.jl:529-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(default::Callable, h::Dict{K,V}, key) where V where K
    index = ht_keyindex(h, key)
    @inbounds return (index < 0) ? default() : h.vals[index]::V
end
```
-/
def getF {K V Q D : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) (default : Unit → DictResult D) : DictResult (V ⊕ D) := do
  let index ← htKeyindex hash matchesKey h key
  if index < 0 then .inr <$> default () else .inl <$> valAt h index.toNat

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
def getkey {K V Q D : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (h : DictState K V) (key : Q) (default : D) : DictResult (K ⊕ D) := do
  let index ← htKeyindex hash matchesKey h key
  if index < 0 then .ok (.inr default) else .inl <$> keyAt h index.toNat

def previousIndex (size index : Nat) : Nat :=
  Nat.land (intBits64 size ((index : Int) - 2)) (size - 1) + 1

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
def popDefault {K V Q D : Type} (hash : Q → JInt .u64) (matchesKey : Q → K → Bool)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (key : Q) (default : D) : DictResult ((V ⊕ D) × DictState K V) := do
  let index ← htKeyindex hash matchesKey h key
  if index > 0 then
    let (value, h) ← popAt unsetKey unsetVal h index.toNat
    .ok (.inl value, h)
  else
    .ok (.inr default, h)

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

def firstDict {K V : Type} (t : DictState K V) : Jl (K × V) :=
  match iterateFirst t with
  | .ok (some (pair, _)) => .ok pair
  | _ => .error (.argumentError "Dict must be non-empty")

/--
Julia source: base/dict.jl:715-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds Iterators.only(t::Dict) = Iterators._only(t, first)
```
-/
def onlyDict {K V : Type} (t : DictState K V) (boundscheck : Bool := true) :
    Jl (K × V) :=
  JuliaLean.base.iterators.sourceMethod1673 (fun d => .ok (length d))
    (fun n => pure (decide (n ≠ 1))) pure firstDict
    (fun message => .error (.argumentError message)) t boundscheck

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
def iteratePart {K V : Type} (h : DictState K V) (part : DictPart) (i : Nat := h.idxfloor) :
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

def listIterate {α : Type} (xs : List α) (state : Option (List α)) :
    DictResult (Option (α × List α)) :=
  match state.getD xs with
  | [] => .ok none
  | x :: rest => .ok (some (x, rest))

def dictInsertLoop {K V Q W C S : Type} (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (iterate : C → Option S → DictResult (Option ((Q × W) × S)))
    (kv : C) : Nat → Option S → DictState K V → DictResult (DictState K V)
  | 0, _, h => .ok h
  | fuel + 1, state, h => do
    match ← iterate kv state with
    | none => .ok h
    | some ((key, value), nextState) =>
      let h ← setindexConv hash matchesKey tablesz keyConv valueConv h value key
      dictInsertLoop hash matchesKey tablesz keyConv valueConv iterate kv fuel (some nextState) h

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
def dictFromIterator {K V Q W C S I : Type} [DictInteger I] (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat) (maxValues : Nat)
    (cld : JInt .i64 → DictResult (JInt .i64)) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (haslength : C → Bool) (length : C → DictResult I)
    (iterate : C → Option S → DictResult (Option ((Q × W) × S))) (bound : C → Nat)
    (kv : C) : DictResult (DictState K V) := do
  let h := dictEmpty K V
  let h ← if haslength kv then do
    let len ← DictInteger.toInt (← length kv)
    sizehint hash tablesz maxValues cld h len true
    else .ok h
  dictInsertLoop hash matchesKey tablesz keyConv valueConv iterate kv (bound kv) none h

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
    (cld : JInt .i64 → DictResult (JInt .i64)) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
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
    (cld : JInt .i64 → DictResult (JInt .i64)) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (pairs : List (Q × W)) : DictResult (DictState K V) :=
  dictFromIterator hash matchesKey tablesz maxValues cld keyConv valueConv
    (fun _ => true) (fun xs => .ok (JInt.lit .i64 (Int.ofNat xs.length)))
    listIterate (fun xs => xs.length + 1) pairs

/--
Julia source: base/dict.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Dict(kv) = dict_with_eltype((K, V) -> Dict{K, V}, kv, eltype(kv))
```
-/
def dictInferred {K V Q W C S I : Type} [DictInteger I] (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat) (maxValues : Nat)
    (cld : JInt .i64 → DictResult (JInt .i64)) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (haslength : C → Bool) (length : C → DictResult I)
    (iterate : C → Option S → DictResult (Option ((Q × W) × S))) (bound : C → Nat)
    (eltype : C → Type)
    (dictWithEltype : (C → DictResult (DictState K V)) → C → Type → DictResult (DictState K V))
    (kv : C) : DictResult (DictState K V) :=
  dictWithEltype (dictFromIterator hash matchesKey tablesz maxValues cld keyConv valueConv
    haslength length iterate bound) kv (eltype kv)

/--
Julia source: base/dict.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Dict(ps::Pair...)                  = Dict(ps)
```
-/
def dictPairsGeneric {K V Q W : Type} (hash : K → JInt .u64)
    (matchesKey : K → K → Bool) (tablesz : Nat → Nat) (maxValues : Nat)
    (cld : JInt .i64 → DictResult (JInt .i64)) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (eltype : List (Q × W) → Type)
    (dictWithEltype : (List (Q × W) → DictResult (DictState K V)) → List (Q × W) → Type → DictResult (DictState K V))
    (pairs : List (Q × W)) : DictResult (DictState K V) :=
  dictInferred hash matchesKey tablesz maxValues cld keyConv valueConv
    (fun _ => true) (fun xs => .ok (JInt.lit .i64 (Int.ofNat xs.length)))
    listIterate (fun xs => xs.length + 1) eltype dictWithEltype pairs

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

def mapValuesLoop {K V W : Type} (valueConv : ValueConv W V) (f : V → DictResult W)
    (h : DictState K V) : Nat → Nat → DictResult (DictState K V)
  | 0, _ => .ok h
  | remaining + 1, index => do
    if isslotfilled h index then
      let value ← valAt h index
      let mapped ← f value
      let value ← convertValue valueConv mapped
      let h := DictState.mk h.size h.slots h.keys (updateAt h.vals index (some value))
        h.ndel h.count h.age h.idxfloor h.maxprobe h.popcursor
      mapValuesLoop valueConv f h remaining (index + 1)
    else
      mapValuesLoop valueConv f h remaining (index + 1)

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
def mapBang {K V W : Type} (valueConv : ValueConv W V) (f : V → DictResult W)
    (iter : ValueIterator K V) : DictResult (ValueIterator K V) := do
  let h := iter.dict
  let h ←
    if h.idxfloor > h.size then .ok h
    else mapValuesLoop valueConv f h (h.size - h.idxfloor + 1) h.idxfloor
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
def immutableGet {K V Q D : Type} (eqKey : K → Q → Bool) :
    ImmutableDict K V → Q → D → V ⊕ D
  | [], _, default => .inr default
  | (key, value) :: rest, query, default =>
    if eqKey key query then .inl value else immutableGet eqKey rest query default

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
def immutableGetF {K V Q D : Type} (eqKey : K → Q → Bool) :
    ImmutableDict K V → Q → (Unit → DictResult D) → DictResult (V ⊕ D)
  | [], _, default => .inr <$> default ()
  | (key, value) :: rest, query, default =>
    if eqKey key query then .ok (.inl value) else immutableGetF eqKey rest query default

/--
Julia source: base/dict.jl:860-863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(d::ImmutableDict{K,V}, t=d) where {K, V}
    !isdefined(t, :parent) && return nothing
    (Pair{K,V}(t.key, t.value), t.parent)
end
```
-/
def immutableIterate {K V : Type} (d : ImmutableDict K V)
    (t : ImmutableDict K V := d) : Option ((K × V) × ImmutableDict K V) :=
  match t with
  | [] => none
  | pair :: rest => some (pair, rest)

/--
Julia source: base/dict.jl:864-864 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::ImmutableDict) = count(Returns(true), t)
```
-/
def immutableLength {K V : Type} (count : (K × V → Bool) → ImmutableDict K V → DictResult Nat)
    (dict : ImmutableDict K V) : DictResult Nat :=
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
def immutableEmptyLike {K₀ V₀ : Type} (K V : Type) (_ : ImmutableDict K₀ V₀) : ImmutableDict K V :=
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

class AbstractDictEmpty (C : Type) (K V : Type) (D : outParam Type) where
  empty : C → D

instance (priority := 900) {C K V : Type} : AbstractDictEmpty C K V (DictState K V) where
  empty c := emptyDict K V c

instance {K₀ V₀ K V : Type} : AbstractDictEmpty (DictState K₀ V₀) K V (DictState K V) where
  empty c := emptyDict K V c

instance {K₀ V₀ K V : Type} : AbstractDictEmpty (ImmutableDict K₀ V₀) K V (ImmutableDict K V) where
  empty c := immutableEmptyLike K V c

/--
Julia source: base/dict.jl:890-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_for(c::AbstractDict, ::Type{Pair{K,V}}, itr, isz, len) where {K, V} = empty(c, K, V)
```
-/
def similarForPairs {C D : Type} (K V : Type) [AbstractDictEmpty C K V D]
    (c : C) : D :=
  AbstractDictEmpty.empty (K := K) (V := V) c

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

def mergewithStep {K V Q W R : Type} (hashStored : K → JInt .u64)
    (hashQuery : Q → JInt .u64) (matchesQuery : Q → K → Bool)
    (tablesz : Nat → Nat) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combineConv : ValueConv R V) (combine : V → W → DictResult R)
    (d0 : DictState K V) (key0 : Q) (value0 : W) : DictResult (DictState K V) := do
  let (index, shortHash, d1) ← htKeyindex2Query hashStored hashQuery matchesQuery tablesz d0 key0
  if index > 0 then
    let oldValue ← valAt d1 index.toNat
    let combined ← combine oldValue value0
    let newValue ← convertValue combineConv combined
    .ok (DictState.mk d1.size d1.slots d1.keys
      (updateAt d1.vals index.toNat (some newValue)) d1.ndel d1.count d1.age
      d1.idxfloor d1.maxprobe d1.popcursor)
  else
    let key ← convertKey keyConv key0
    let value ← convertValue valueConv value0
    let r ← setindexAt hashStored tablesz d1 value key (-index).toNat shortHash
    .ok r.2

def mergewithLoop {K V Q W R D S : Type} (hashStored : K → JInt .u64)
    (hashQuery : Q → JInt .u64) (matchesQuery : Q → K → Bool)
    (tablesz : Nat → Nat) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combineConv : ValueConv R V) (combine : V → W → DictResult R)
    (iterateD2 : D → Option S → DictResult (Option ((Q × W) × S)))
    (d2 : D) : Nat → Option S → DictState K V → DictResult (DictState K V)
  | 0, _, d0 => .ok d0
  | fuel + 1, state, d0 => do
    match ← iterateD2 d2 state with
    | none => .ok d0
    | some ((key, value), nextState) =>
      let d1 ← mergewithStep hashStored hashQuery matchesQuery tablesz keyConv valueConv
        combineConv combine d0 key value
      mergewithLoop hashStored hashQuery matchesQuery tablesz keyConv valueConv
        combineConv combine iterateD2 d2 fuel (some nextState) d1
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
def mergewithBang {K V Q W R D S I : Type} [DictInteger I] (hashStored : K → JInt .u64)
    (hashQuery : Q → JInt .u64) (matchesQuery : Q → K → Bool)
    (tablesz : Nat → Nat) (maxValues : Nat) (cld : JInt .i64 → DictResult (JInt .i64))
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combineConv : ValueConv R V) (combine : V → W → DictResult R)
    (haslength : D → Bool) (lengthD2 : D → DictResult I)
    (iterateD2 : D → Option S → DictResult (Option ((Q × W) × S))) (boundD2 : D → Nat)
    (d1 : DictState K V) (d2 : D) : DictResult (DictState K V) := do
  let d1 ←
    if haslength d2 then do
      let len2 ← DictInteger.toInt (← lengthD2 d2)
      sizehint hashStored tablesz maxValues cld d1
        (JInt.lit .i64 (Int.ofNat (length d1) + len2.val)) false
    else .ok d1
  mergewithLoop hashStored hashQuery matchesQuery tablesz keyConv valueConv
    combineConv combine iterateD2 d2 (boundD2 d2) none d1

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
  insert : H → H → Bool → Bool → Nat → Nat → HS → W → Option (DictResult H)
  deleteAt : H → H → Nat → H
  unset : H → H → Nat → H
  isLevelEmpty : H → Bool
  leafValue : H → Nat → Option V
  iterate : H → Option S → Option ((K × V) × S)
  length : H → Option (DictResult (JInt .i64))
  isEmpty : H → Option (DictResult Bool)

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
    (key : Q) (value : W) : Option (DictResult (PersistentDict K V H)) :=
  let trie := dict.trie
  let h := ops.hashState key
  let path := ops.path trie h true
  (ops.insert path.top path.trie path.found path.present path.index
    path.bitmapIndex path.state value).map (Except.map PersistentDict.mk)

/--
Julia source: base/dict.jl:909-910 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline Base.@assume_effects :effect_free :terminates_globally KeyValue.set(
        dict::PersistentDict{K, V}, key, val) where {K, V} = @inline _keyvalueset(dict, key, val)
```
-/
def persistentSet {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (key : Q) (value : W) :
    Option (DictResult (PersistentDict K V H)) :=
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
    Option (DictResult (PersistentDict K V H)) :=
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
    Option (DictResult (PersistentDict K V H)) :=
  match keyConv.convert key with
  | .error error => some (.error error)
  | .ok key =>
      match valueConv.convert value with
      | .error error => some (.error error)
      | .ok value => persistentSetTyped ops dict key value

/--
Julia source: base/dict.jl:982-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PersistentDict(dict::PersistentDict, pair::Pair) = PersistentDict(dict, pair...)
```
-/
def persistentExtendPair {K V H HS S Q W : Type} (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (dict : PersistentDict K V H) (pair : Q × W) : Option (DictResult (PersistentDict K V H)) :=
  persistentExtend ops keyConv valueConv dict pair.1 pair.2

/--
Julia source: base/dict.jl:983-983 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PersistentDict{K,V}(dict::PersistentDict{K,V}, pair::Pair) where {K,V} = PersistentDict(dict, pair...)
```
-/
def persistentTypedExtendPair {K V H HS S Q W : Type} (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (dict : PersistentDict K V H) (pair : Q × W) : Option (DictResult (PersistentDict K V H)) :=
  persistentExtend ops keyConv valueConv dict pair.1 pair.2

def persistentExtendMany {K V H HS S Q W : Type} (ops : PersistentOps K V K V H HS S)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (dict : PersistentDict K V H) : List (Q × W) → Option (DictResult (PersistentDict K V H))
  | [] => some (.ok dict)
  | (key, value) :: rest =>
      match persistentExtend ops keyConv valueConv dict key value with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok dict) => persistentExtendMany ops keyConv valueConv dict rest

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
    (key : Q) (value : W) (rest : List (Q × W)) : Option (DictResult (PersistentDict K V H)) :=
  match persistentTypedPair opsPair (key, value) with
  | .error error => some (.error error)
  | .ok dict => persistentExtendMany ops keyConv valueConv dict rest

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
    (first : K × V) (rest : List (Q × W)) : Option (DictResult (PersistentDict K V H)) :=
  match persistentPair ops first with
  | .error error => some (.error error)
  | .ok dict => persistentExtendMany ops keyConv valueConv dict rest

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
def persistentIn {K V R H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (valueEq : V → V → DictResult R) (dict : PersistentDict K V H)
    (pair : K × V) : DictResult (Bool ⊕ R) := do
  match persistentKeyGet ops dict pair.1 with
  | none => .ok (.inl false)
  | some value => .inr <$> valueEq pair.2 value

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
def persistentGet {K V D H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) (default : D) : V ⊕ D :=
  match persistentKeyGet ops dict key with
  | none => .inr default
  | some value => .inl value

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
def persistentGetDefault {K V Q W D H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (key : Q) (default : Unit → DictResult D) :
    DictResult (V ⊕ D) := do
  match persistentKeyGet ops dict key with
  | none => .inr <$> default ()
  | some value => .ok (.inl value)

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
def persistentGetTypedDefault {K V D H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (dict : PersistentDict K V H) (key : K) (default : Unit → DictResult D) :
    DictResult (V ⊕ D) := do
  match persistentKeyGet ops dict key with
  | none => .inr <$> default ()
  | some value => .ok (.inl value)

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
    (dict : PersistentDict K V H) (state : Option S := none) : Option ((K × V) × S) :=
  ops.iterate dict.trie state

/--
Julia source: base/dict.jl:1065-1065 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(dict::PersistentDict) = HAMT.length(dict.trie)
```
-/
def persistentLength {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) : Option (DictResult (JInt .i64)) :=
  ops.length dict.trie

/--
Julia source: base/dict.jl:1066-1066 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(dict::PersistentDict) = HAMT.isempty(dict.trie)
```
-/
def persistentIsEmpty {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) : Option (DictResult Bool) :=
  ops.isEmpty dict.trie

/--
Julia source: base/dict.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(::PersistentDict, ::Type{K}, ::Type{V}) where {K, V} = PersistentDict{K, V}()
```
-/
def persistentEmptyLike {K₀ V₀ K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (_ : PersistentDict K₀ V₀ H) : PersistentDict K V H :=
  persistentEmptyConstructor ops

def persistentEmptyDictInst {K₀ V₀ K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S) :
    AbstractDictEmpty (PersistentDict K₀ V₀ H) K V (PersistentDict K V H) where
  empty c := persistentEmptyLike ops c

def firstPersistent {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) : Jl (K × V) :=
  match persistentIterate ops dict none with
  | some (pair, _) => .ok pair
  | none => .error (.argumentError "PersistentDict must be non-empty")

/--
Julia source: base/dict.jl:1069-1069 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds Iterators.only(dict::PersistentDict) = Iterators._only(dict, first)
```
-/
def persistentOnly {K V Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (dict : PersistentDict K V H) (boundscheck : Bool := true) :
    Option (Except (DictError ⊕ JlError) (K × V)) :=
  if boundscheck then do
    let length ← persistentLength ops dict
    match length with
    | .error error => some (.error (.inl error))
    | .ok n => some ((JuliaLean.base.iterators.sourceMethod1673
        (fun _ => .ok n.val.toNat) (fun n => pure (decide (n ≠ 1))) pure
        (firstPersistent ops) (fun message => .error (.argumentError message)) dict true).mapError Sum.inr)
  else some ((firstPersistent ops dict).mapError Sum.inr)
end JuliaLean.base.dict
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

end JuliaLean.Dicts

namespace JuliaLean.Dicts

variable {K Q : Type}
/-- Elements that already have the key type. -/
def Conv.self (o : KeyOps K) : Conv K K := ⟨some, pure, o.hash, o.eq, true⟩

/-- `setindex!(h, v0, key0)`, `base/dict.jl:347-357`: convert a foreign key and
throw `KeyTypeError` unless `isequal(key, key0)`. -/
def setindexConv {V : Type} (o : KeyOps K) (c : Conv Q K) (t : Table K V) (v : V) (key0 : Q) :
    DR (Table K V) :=
  match c.isa key0 with
  | some k => setindex o t v k
  | none => do
    let k ← c.convert key0
    if !(c.iseq key0 k) then throw .keyTypeError
    setindex o t v k

end JuliaLean.Dicts
/-!
# `Dict` methods of `base/dict.jl` (master `bbfa0ce4150`)

The table, probing, insertion, deletion and rehashing are the mirrored
definitions of `JuliaLean.Dicts` in this module. This file mirrors the
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
  | _ => items.foldlM (fun acc d => dictMerge sizehint iterList setindex o acc d) Table.empty

end JuliaLean.DictsCov

namespace JuliaLean.Dicts

variable {K V : Type}

/-- `get(dict::ImmutableDict, key, default)`, `base/dict.jl:843-849`:
`isequal(dict.key, key)` on the chain. -/
def idGet (eq : K → K → Bool) : IDict K V → K → Option V
  | [], _ => none
  | (k, v) :: d, q => if eq k q then some v else idGet eq d q

/-- `in(key_value::Pair, dict::ImmutableDict, valcmp)`, `base/dict.jl:817-826`. -/
def idIn (eq : K → K → Bool) (valcmp : V → V → Bool) : IDict K V → K × V → Bool
  | [], _ => false
  | (k, v) :: d, (q, w) => if eq k q && valcmp w v then true else idIn eq valcmp d (q, w)

/-- `length(t::ImmutableDict) = count(Returns(true), t)`, `base/dict.jl:864`. -/
def idLength (d : IDict K V) : Nat := d.length

/-- `Dict{K,V}(kv)`, `base/dict.jl:91-98`: `sizehint!(h, length(kv))`, then
`h[k] = v` for each pair in iteration order. -/
def dictOfPairs {K V : Type} (o : KeyOps K) (kv : List (K × V)) : DR (Table K V) := do
  let h ← sizehint o Table.empty (JInt.lit .i64 kv.length) true
  kv.foldlM (fun h p => setindex o h p.2 p.1) h

/-- `in(key_value::Pair, dict::ImmutableDict, valcmp)`, `base/dict.jl:817-826`,
with a three-valued `valcmp` (`none` is `missing`): `valcmp(value, dict.value)
&& return true` throws `TypeError` on `missing`. The result is `in`'s value,
`some b` or `missing`. -/
def idIn3 {K V : Type} (eq : K → K → Bool) (valcmp : V → V → Option Bool) :
    IDict K V → K × V → Except String (Option Bool)
  | [], _ => .ok (some false)
  | (k, v) :: d, (q, w) =>
    if eq k q then
      match valcmp w v with
      | some true => .ok (some true)
      | some false => idIn3 eq valcmp d (q, w)
      | none => .error "TypeError: non-boolean (Missing) used in boolean context"
    else idIn3 eq valcmp d (q, w)

end JuliaLean.Dicts
/-!
# `ImmutableDict`, `base/dict.jl:776-892` (master `bbfa0ce4150`)

An `ImmutableDict{K,V}` is its chain of pairs, most recent first
(`JuliaLean.Dicts.IDict`). `new(parent, key, value)` converts `key` to `K` and
`value` to `V` (the field types); those conversions are `ck` and `cv`. A
lookup key of type `Q` meets stored keys through `eq k q`, which is
`isequal(dict.key, key)`.
-/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

variable {K V Q W : Type}

/-- `ImmutableDict{K,V}() = new()`, `base/dict.jl:780`. -/
def immNew : IDict K V := []

/-- `ImmutableDict{K,V}(key, value) = (empty = new(); new(empty, key, value))`, `base/dict.jl:781`. -/
def immNew2 (ck : Q → DR K) (cv : W → DR V) (key : Q) (value : W) : DR (IDict K V) := do
  let k ← ck key
  let v ← cv value
  pure [(k, v)]

/-- `ImmutableDict{K,V}(parent::ImmutableDict, key, value) = new(parent, key, value)`, `base/dict.jl:782`. -/
def immNew3 (ck : Q → DR K) (cv : W → DR V) (parent : IDict K V) (key : Q) (value : W) :
    DR (IDict K V) := do
  let k ← ck key
  let v ← cv value
  pure ((k, v) :: parent)

/-- `ImmutableDict(KV::Pair{K,V}) = ImmutableDict{K,V}(KV[1], KV[2])`, `base/dict.jl:811`
(the pair already has the field types). -/
def immOfPair (kv : K × V) : DR (IDict K V) := immNew2 pure pure kv.1 kv.2

/-- `ImmutableDict(t::ImmutableDict{K,V}, KV::Pair) = ImmutableDict{K,V}(t, KV[1], KV[2])`,
`base/dict.jl:812`. -/
def immPush (ck : Q → DR K) (cv : W → DR V) (t : IDict K V) (kv : Q × W) : DR (IDict K V) :=
  immNew3 ck cv t kv.1 kv.2

/-- `ImmutableDict(t::ImmutableDict{K,V}, KV::Pair, rest::Pair...) =
ImmutableDict(ImmutableDict(t, KV), rest...)`, `base/dict.jl:813-814`. -/
def immPushMany (ck : Q → DR K) (cv : W → DR V) (t : IDict K V) (kv : Q × W) :
    List (Q × W) → DR (IDict K V)
  | [] => immPush ck cv t kv
  | r :: rest => do
    let t ← immPush ck cv t kv
    immPushMany ck cv t r rest

/-- `ImmutableDict(KV::Pair, rest::Pair...) = ImmutableDict(ImmutableDict(KV), rest...)`,
`base/dict.jl:815`. -/
def immOfPairs (ck : Q → DR K) (cv : W → DR V) (kv : K × V) : List (Q × W) → DR (IDict K V)
  | [] => immOfPair kv
  | r :: rest => do
    let t ← immOfPair kv
    immPushMany ck cv t r rest

/-- `haskey(dict::ImmutableDict, key)`, `base/dict.jl:828-834`. -/
def immHaskey (eq : K → Q → Bool) : IDict K V → Q → Bool
  | [], _ => false
  | (k, _) :: parent, key => if eq k key then true else immHaskey eq parent key

/-- `getindex(dict::ImmutableDict, key)`, `base/dict.jl:836-842`. -/
def immGetindex (eq : K → Q → Bool) : IDict K V → Q → DR V
  | [], _ => throw .keyError
  | (k, v) :: parent, key => if eq k key then pure v else immGetindex eq parent key

/-- `get(dict::ImmutableDict, key, default)`, `base/dict.jl:843-849`. -/
def immGet (eq : K → Q → Bool) : IDict K V → Q → V → V
  | [], _, default => default
  | (k, v) :: parent, key, default => if eq k key then v else immGet eq parent key default

/-- `get(default::Callable, dict::ImmutableDict, key)`, `base/dict.jl:851-857`. -/
def immGetF (eq : K → Q → Bool) : IDict K V → Q → (Unit → DR V) → DR V
  | [], _, default => default ()
  | (k, v) :: parent, key, default => if eq k key then pure v else immGetF eq parent key default

/-- `iterate(d::ImmutableDict{K,V}, t=d)`, `base/dict.jl:860-863`. -/
def immIterate (t : IDict K V) : Option ((K × V) × IDict K V) :=
  match t with
  | [] => none
  | (k, v) :: parent => some ((k, v), parent)

/-- `for pair in t` to exhaustion through `immIterate`. -/
def immCollect : IDict K V → List (K × V)
  | [] => []
  | e :: parent => match immIterate (e :: parent) with
    | none => []
    | some (p, _) => p :: immCollect parent

/-- `length(t::ImmutableDict) = count(Returns(true), t)`, `base/dict.jl:864`. -/
def immLength (t : IDict K V) : Nat := ((immCollect t).filter fun _ => true).length

/-- `isempty(t::ImmutableDict) = !isdefined(t, :parent)`, `base/dict.jl:865`. -/
def immIsempty (t : IDict K V) : Bool := t.isEmpty

/-- `empty(::ImmutableDict, ::Type{K}, ::Type{V}) = ImmutableDict{K,V}()`, `base/dict.jl:866`. -/
def immEmpty (_ : IDict K V) : IDict K V := immNew
/-! ## `show(io, t::AbstractDict)`, `base/dict.jl:3-23` -/

/-- What `show` prints: literal text or `show(recur_io, pair)` of a pair. -/
inductive ShowTok (α : Type) where
  | text (s : String)
  | pair (x : α)
  deriving Repr, DecidableEq

/-- The loop `for pair in t ... end` of `show`, with the counter `n` and the
flag `first`. -/
def showDictLoop {α : Type} (limit : Bool) : Nat → Bool → List α → List (ShowTok α)
  | _, _, [] => []
  | n, first, pair :: rest =>
    let sep : List (ShowTok α) := if first then [] else [.text ", "]
    let n := n + 1
    if limit && n ≥ 10 then sep ++ [.pair pair, .text "…"]
    else sep ++ .pair pair :: showDictLoop limit n false rest

/-- `show(io, t::AbstractDict)`: `pfx` is `typeinfo_prefix(io, t)[1]`, `limit`
is `get(io, :limit, false)`, `circular` is `show_circular(io, t)`, and `pairs`
the iteration of `t` (`isempty(t)` is `pairs = []`). -/
def showDictAD {α : Type} (pfx : String) (limit circular : Bool) (pairs : List α) : List (ShowTok α) :=
  [.text pfx, .text "("] ++
    (if !pairs.isEmpty && !circular then showDictLoop limit 0 true pairs else []) ++ [.text ")"]

end JuliaLean.DictsCov

namespace JuliaLean.Dicts

variable {K Q V : Type}
/-- `haskey(t, q)` for a key of type `Q` (`base/dict.jl:553`). -/
def haskeyConv (c : Conv Q K) (t : Table K V) (q : Q) : DR Bool := do
  let index ← htKeyindex t (c.hash q) (c.iseq q)
  pure (index ≥ 0)
/-- `ImmutableDict{K,V}(parent, key, value) = new(parent, key, value)`
(`base/dict.jl:782`): `new` converts the key field with `convert(K, key)`.
`ImmutableDict(t, KV::Pair)` (`base/dict.jl:812`) and `setindex(d, value, key)`
(`base/dict.jl:886-888`) call it. -/
def idSetConv (c : Conv Q K) (d : IDict K V) (key : Q) (value : V) : DR (IDict K V) := do
  let k ← c.convert key
  pure ((k, value) :: d)

/-- `get(dict::ImmutableDict, key, default)` for a key of type `Q`,
`base/dict.jl:843-849`. -/
def idGetConv (c : Conv Q K) : IDict K V → Q → Option V
  | [], _ => none
  | (k, v) :: d, q => if c.iseq q k then some v else idGetConv c d q

end JuliaLean.Dicts

namespace JuliaLean.DictsCov.DictRows


abbrev R (α : Type) := Except String α

/-! ## Generic Dict forwarding methods -/

def method116 (construct : List (K × V) → D) (pairs : List (K × V)) : D := construct pairs

def method118 (eltype : I → T) (dictWithEltype : I → T → D) (kv : I) : D :=
  dictWithEltype kv (eltype kv)

def method120 (emptyDict : Unit → D) : D := emptyDict ()

abbrev Imm (K V : Type) := List (K × V)

def method780 : Imm K V := []

def method781 (key : K) (value : V) : Imm K V := [(key, value)]

def method782 (parent : Imm K V) (key : K) (value : V) : Imm K V :=
  (key, value) :: parent

def method811 (pair : K × V) : Imm K V := method781 pair.1 pair.2

def method812 (convertKey : Q → R K) (convertValue : W → R V)
    (dict : Imm K V) (pair : Q × W) : R (Imm K V) := do
  let key ← convertKey pair.1
  let value ← convertValue pair.2
  return method782 dict key value

def immAppend (add : Imm K V → Q × W → R (Imm K V)) :
    Imm K V → List (Q × W) → R (Imm K V)
  | dict, [] => .ok dict
  | dict, pair :: rest => do
      let dict ← add dict pair
      immAppend add dict rest

def method813 (add : Imm K V → Q × W → R (Imm K V))
    (dict : Imm K V) (pair : Q × W) (rest : List (Q × W)) : R (Imm K V) := do
  let dict ← add dict pair
  immAppend add dict rest

def method815 (first : Q × W → R (Imm K V))
    (add : Imm K V → Q × W → R (Imm K V))
    (pair : Q × W) (rest : List (Q × W)) : R (Imm K V) := do
  let dict ← first pair
  immAppend add dict rest

def method828 (isequal : K → Q → Bool) : Imm K V → Q → Bool
  | [], _ => false
  | (key, _) :: parent, query => if isequal key query then true else method828 isequal parent query

def method836 (isequal : K → Q → Bool) : Imm K V → Q → R V
  | [], _ => .error "KeyError"
  | (key, value) :: parent, query =>
      if isequal key query then .ok value else method836 isequal parent query

def method843 (isequal : K → Q → Bool) : Imm K V → Q → V → V
  | [], _, default => default
  | (key, value) :: parent, query, default =>
      if isequal key query then value else method843 isequal parent query default

def method851 (isequal : K → Q → Bool) : Imm K V → Q → (Unit → R V) → R V
  | [], _, default => default ()
  | (key, value) :: parent, query, default =>
      if isequal key query then .ok value else method851 isequal parent query default

def method860 (state : Imm K V) : Option ((K × V) × Imm K V) :=
  match state with | [] => none | pair :: parent => some (pair, parent)

def method864 (dict : Imm K V) : Nat := dict.length

def method865 (dict : Imm K V) : Bool := dict.isEmpty

def method866 : Imm K V := []

def method890 (empty : D → T → T → D) (dict : D) (keyType valueType : T) : D :=
  empty dict keyType valueType

def method891 (_dict : D) (_elementType : T) : R D :=
  .error "for AbstractDicts, similar requires an element type of Pair;\n  if calling map, consider a comprehension instead"

structure Persistent (H : Type) where
  trie : H
  deriving Repr

structure PathResult (H I B S : Type) where
  found : Bool
  present : Bool
  trie : H
  index : I
  bitmap : B
  top : H
  state : S

def method903 (emptyHamt : Unit → H) : Persistent H := ⟨emptyHamt ()⟩

def method906 (singleton : K → V → H) (key : K) (value : V) : Persistent H :=
  ⟨singleton key value⟩

def method909 (set : Persistent H → K → V → Persistent H)
    (dict : Persistent H) (key : K) (value : V) : Persistent H := set dict key value

def method913 (hashState : K → S)
    (path : H → S → Bool → PathResult H I B S)
    (insert : Bool → Bool → H → I → B → S → V → H)
    (dict : Persistent H) (key : K) (value : V) : Persistent H :=
  let trie := dict.trie
  let state := hashState key
  let result := path trie state true
  ⟨insert result.found result.present result.trie result.index result.bitmap
    result.state value⟩

def method920 (delete : Persistent H → K → Persistent H) (dict : Persistent H) (key : K) :=
  delete dict key

def method922 (delete : Persistent H → K → Persistent H) (dict : Persistent H) (key : K) :=
  delete dict key

def method924 (hashState : K → S)
    (path : H → S → Bool → PathResult H I B S)
    (deleteAt : H → I → H) (unset : H → B → H)
    (dict : Persistent H) (key : K) : Persistent H :=
  let result := path dict.trie (hashState key) true
  if result.found && result.present then
    ⟨unset (deleteAt result.top result.index) result.bitmap⟩
  else ⟨result.top⟩

def method969 (keyValueSet : Unit → Persistent H) : Persistent H := keyValueSet ()

def method970 (keyValueSet : K → V → Persistent H) (pair : K × V) : Persistent H :=
  keyValueSet pair.1 pair.2

def method976 (keyValueSet : K → V → Persistent H) (pair : K × V) : Persistent H :=
  keyValueSet pair.1 pair.2

def method982 (construct : Persistent H → K → V → Persistent H)
    (dict : Persistent H) (pair : K × V) := construct dict pair.1 pair.2

def method983 (construct : Persistent H → K → V → Persistent H)
    (dict : Persistent H) (pair : K × V) := construct dict pair.1 pair.2

def method986 (convertKey : Q → R K) (convertValue : W → R V)
    (set : Persistent H → K → V → Persistent H) (dict : Persistent H)
    (key : Q) (value : W) : R (Persistent H) := do
  let key ← convertKey key
  let value ← convertValue value
  return set dict key value

def persistentFold (add : Persistent H → K → V → R (Persistent H)) :
    Persistent H → List (K × V) → R (Persistent H)
  | dict, [] => .ok dict
  | dict, (key, value) :: rest => do
      let dict ← add dict key value
      persistentFold add dict rest

def method992 (first : K × V → R (Persistent H))
    (add : Persistent H → K → V → R (Persistent H))
    (pair : K × V) (rest : List (K × V)) : R (Persistent H) := do
  let dict ← first pair
  persistentFold add dict rest

def method1000 (first : K × V → R (Persistent H))
    (add : Persistent H → K → V → R (Persistent H))
    (pair : K × V) (rest : List (K × V)) : R (Persistent H) := do
  let dict ← first pair
  persistentFold add dict rest

structure PairType (K V : Type) where

def method1008 : PairType K V := ⟨⟩

def method1010 (get : Persistent H → K → Option V) (valcmp : V → V → Bool)
    (dict : Persistent H) (pair : K × V) : Bool :=
  match get dict pair.1 with | none => false | some value => valcmp pair.2 value

def method1017 (get : Persistent H → K → Option V) (dict : Persistent H) (key : K) : Bool :=
  (get dict key).isSome

def method1021 (get : Persistent H → K → Option V) (dict : Persistent H) (key : K) : R V :=
  match get dict key with | none => .error "KeyError" | some value => .ok value

def method1027 (get : Persistent H → K → Option V)
    (dict : Persistent H) (key : K) (default : V) : V :=
  match get dict key with | none => default | some value => value

def method1033 (isLevelEmpty : H → Bool) (hashState : K → S)
    (path : H → S → PathResult H I B S) (leafAt : H → I → Option V)
    (dict : Persistent H) (key : K) : Option V :=
  if isLevelEmpty dict.trie then none
  else
    let result := path dict.trie (hashState key)
    if result.found && result.present then leafAt result.trie result.index else none

def method1047 (get : Persistent H → K → Option V) (default : Unit → R V)
    (dict : Persistent H) (key : K) : R V :=
  match get dict key with | none => default () | some value => .ok value

def method1053 (get : Persistent H → K → Option V) (default : Unit → R V)
    (dict : Persistent H) (key : K) : R V :=
  match get dict key with | none => default () | some value => .ok value

def method1059 (delete : Persistent H → K → Persistent H) (dict : Persistent H) (key : K) :=
  delete dict key

def method1063 (iterateHamt : H → Option S → Option (P × S))
    (dict : Persistent H) (state : Option S) := iterateHamt dict.trie state

def method1065 (lengthHamt : H → Nat) (dict : Persistent H) : Nat := lengthHamt dict.trie

def method1066 (emptyHamt : H → Bool) (dict : Persistent H) : Bool := emptyHamt dict.trie

def method1067 (emptyPersistent : Unit → Persistent H) : Persistent H := emptyPersistent ()

def method1069 (only : Persistent H → (Persistent H → Option (K × V)) → R (K × V))
    (first : Persistent H → Option (K × V)) (dict : Persistent H) : R (K × V) :=
  only dict first

end JuliaLean.DictsCov.DictRows

namespace JuliaLean.Dicts

/-- `in(key_val::Pair{K,V}, dict::PersistentDict{K,V})`, `base/dict.jl:1010-1015`:
the pair whose key is `===` to the query. -/
def pdIn {V : Type} (valcmp : V → V → Bool) (pairs : List (OneKey × V)) (kv : OneKey × V) : Bool :=
  match pairs.find? (fun e => decide (e.1 = kv.1)) with
  | some (_, v) => valcmp kv.2 v
  | none => false

end JuliaLean.Dicts

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

/-- The message of `_similar_for(c::AbstractDict, ::Type{T}, ...)`, `base/dict.jl:891-892`. -/
def similarMsg : String :=
  "for AbstractDicts, similar requires an element type of Pair;\n  if calling map, consider a comprehension instead"

/-- `_similar_for(c::AbstractDict, ::Type{Pair{K,V}}, itr, isz, len) = empty(c, K, V)` and
`_similar_for(c::AbstractDict, ::Type{T}, ...) = throw(ArgumentError(...))`,
`base/dict.jl:890-892`: `pairParams T` is `some (K, V)` for `T = Pair{K,V}`. -/
def similarFor {T D K' V' : Type} (ops : DictOps T D K' V') (c : D) (pairParams : Option (T × T)) : GR D :=
  match pairParams with
  | some (k, v) => pure (ops.emptyT c k v)
  | none => throw (.argumentError similarMsg)

end JuliaLean.DictsCov
