import JuliaLean.Core

/-!
Mutating `Vector` operations of `base/array.jl` and `base/abstractarray.jl`
(master `bbfa0ce4150`).

A `Vector{T}` is modelled by its contents, a list of slots: `some x` is an
assigned element, `none` an unassigned slot (`#undef` for reference types,
uninitialized memory for bits types). Operations that grow the vector create
`none` slots exactly where Julia's `_growbeg!`/`_growend!`/`_growat!` do.
The capacity of the backing `Memory` is not modelled; every growth succeeds
(no `OutOfMemoryError`). A mutating call returns the final contents together
with its result or exception (`Out`), because Julia keeps the mutations made
before an exception.

Julia indices are `Int`. User-supplied indices of any `BitInteger` type are
`JInt t` and go through `Int(i)` (`InexactError` when not representable).
Loop counters that Julia keeps in `Int` and that stay within
`0:length(a)+1` are mathematical integers here: they cannot wrap, because a
vector has fewer than `2^62` elements.
-/

namespace JuliaLean.ArrayOps

open JuliaLean

/-- Slots of a `Vector`; `none` is an unassigned slot. -/
abbrev Vec (α : Type) := List (Option α)

/-- Final contents of the mutated vector and the result or exception. -/
structure Out (α β : Type) where
  vec : Vec α
  res : Jl β

section
variable {α β : Type}

/-- `a + b` for `BitInteger`s of possibly different types: both operands are reduced
into the promoted type with `%` and added with wrapping (`base/int.jl`, the mixed
`+(a::Integer, b::Integer)` methods over `promote_typeof`). -/
def addMixed {s t : IntTy} (a : JInt s) (b : JInt t) : JInt (IntTy.promote s t) :=
  JInt.wrap _ (a.val + b.val)

/-- `Int(x)` for a value of any integer type. -/
def toInt {t : IntTy} (x : JInt t) : Jl JInt64 := JInt.convert .i64 x.val

/-- `memoryref(ref, k)` with its bounds check (`base/boot.jl:770`): `Int(k)`, then
`1 ≤ k ≤ length` of the backing memory. The memory is modelled as exactly as long
as the vector; the only calls that differ are those with `k ≥ 2^62`, which fail
in Julia as well. -/
def memoryrefCheck {t : IntTy} (len : Nat) (k : JInt t) : Jl Unit := do
  let k ← toInt k
  if 1 ≤ k.val ∧ k.val ≤ len then pure () else throw .boundsError

/-- `unsafe_copyto!(dest::Array, doffs, src::Array, soffs, n)` with `dest === src`,
`base/array.jl:276-280`: nothing for `n == 0`, otherwise the two `memoryref`
bounds checks. Only the checks are modelled; callers compute the moved contents. -/
def selfCopyCheck {s t u : IntTy} (len : Nat) (doffs : JInt s) (soffs : JInt t) (n : JInt u) :
    Jl Unit :=
  if n.val = 0 then pure () else do
    memoryrefCheck len doffs
    memoryrefCheck len soffs

/-- `_deletebeg!(a, delta)`, `base/array.jl:1278-1295`. -/
def deletebeg {t : IntTy} (a : Vec α) (delta : JInt t) : Out α Unit :=
  match toInt delta with
  | .error e => ⟨a, .error e⟩
  | .ok d =>
    -- `unsigned(delta) > unsigned(len)`: a negative delta is a huge unsigned value
    if d.val < 0 ∨ d.val > a.length then
      ⟨a, .error (.argumentError "_deletebeg! requires delta in 0:length(a)")⟩
    else ⟨a.drop d.val.toNat, .ok ()⟩

/-- `_deleteend!(a, delta)`, `base/array.jl:1296-1311`. -/
def deleteend {t : IntTy} (a : Vec α) (delta : JInt t) : Out α Unit :=
  match toInt delta with
  | .error e => ⟨a, .error e⟩
  | .ok d =>
    if d.val < 0 ∨ d.val > a.length then
      ⟨a, .error (.argumentError "_deleteend! requires delta in 0:length(a)")⟩
    else ⟨a.take (a.length - d.val.toNat), .ok ()⟩

/-- `_growbeg!(a, delta)`, `base/array.jl:1151-1168`: `delta` unassigned slots in front. -/
def growbeg {t : IntTy} (a : Vec α) (delta : JInt t) : Out α Unit :=
  match toInt delta with
  | .error e => ⟨a, .error e⟩
  | .ok d =>
    if d.val = 0 then ⟨a, .ok ()⟩
    else if ¬ 0 ≤ d.val then ⟨a, .error (.argumentError "grow requires delta >= 0")⟩
    else ⟨List.replicate d.val.toNat none ++ a, .ok ()⟩

/-- `_growend!(a, delta)`, `base/array.jl:1213-1228`: `delta` unassigned slots at the end. -/
def growend {t : IntTy} (a : Vec α) (delta : JInt t) : Out α Unit :=
  match toInt delta with
  | .error e => ⟨a, .error e⟩
  | .ok d =>
    if ¬ 0 ≤ d.val then ⟨a, .error (.argumentError "grow requires delta >= 0")⟩
    else ⟨a ++ List.replicate d.val.toNat none, .ok ()⟩

/-- `_growat!(a, i, delta)`, `base/array.jl:1230-1275`: `delta` unassigned slots
before position `i`. The three memory strategies move the same contents. -/
def growat {s t : IntTy} (a : Vec α) (i : JInt s) (delta : JInt t) : Out α Unit :=
  match toInt delta, toInt i with
  | .error e, _ => ⟨a, .error e⟩
  | .ok _, .error e => ⟨a, .error e⟩
  | .ok d, .ok i =>
    let len : Int := a.length
    if i.val = 1 then growbeg a d
    else if len < IntTy.i64.max ∧ i.val = len + 1 then growend a d
    else if ¬ 0 ≤ d.val then ⟨a, .error (.argumentError "grow requires delta >= 0")⟩
    else if ¬ (1 < i.val ∧ i.val ≤ len) then ⟨a, .error .boundsError⟩
    else
      let k := (i.val - 1).toNat
      ⟨a.take k ++ List.replicate d.val.toNat none ++ a.drop k, .ok ()⟩

/-- `_deleteat!(a, i, delta)`, `base/array.jl:1312-1327`. `delta` keeps its own type
(the `length` of the caller's range), so `i + delta` and `2*i + delta` are computed
in the promoted type, wrapping. The first branch moves the `i-1` leading elements
right by `delta` and drops `delta` from the front, the second moves the tail left
and drops `delta` from the end; both leave `a[1:i-1]` followed by `a[i+delta:end]`. -/
def deleteatAt {s t : IntTy} (a : Vec α) (i : JInt s) (delta : JInt t) : Out α Unit :=
  match toInt i with
  | .error e => ⟨a, .error e⟩
  | .ok i =>
    let len : Int := a.length
    let one : JInt64 := JInt.lit .i64 1
    let rest := a.take (i.val - 1).toNat ++ a.drop (i.val - 1 + delta.val).toNat
    if ¬ 0 ≤ delta.val then ⟨a, .error (.argumentError "_deleteat! requires delta >= 0")⟩
    else if ¬ (1 ≤ i.val ∧ i.val ≤ len) then ⟨a, .error .boundsError⟩
    else if ¬ (addMixed i delta).val ≤ len + 1 then ⟨a, .error .boundsError⟩
    else if (addMixed (JInt.lit .i64 2 * i) delta).val ≤ len then
      -- unsafe_copyto!(newa, 1 + delta, a, 1, i - 1); _deletebeg!(a, delta)
      match selfCopyCheck a.length (addMixed one delta) one (i - one) with
      | .error e => ⟨a, .error e⟩
      | .ok () =>
        match deletebeg a delta with
        | ⟨_, .error e⟩ => ⟨a, .error e⟩
        | ⟨_, .ok ()⟩ => ⟨rest, .ok ()⟩
    else
      -- unsafe_copyto!(newa, i, a, i + delta, len + 1 - delta - i); _deleteend!(a, delta)
      let n := JInt.wrap (IntTy.promote .i64 t) (len + 1 - delta.val - i.val)
      match selfCopyCheck a.length i (addMixed i delta) n with
      | .error e => ⟨a, .error e⟩
      | .ok () =>
        match deleteend a delta with
        | ⟨_, .error e⟩ => ⟨a, .error e⟩
        | ⟨_, .ok ()⟩ => ⟨rest, .ok ()⟩

/-! ### Dequeue operations -/

/-- `push!(a, item)`, `base/array.jl:1358-1370` (item already converted). -/
def push (a : Vec α) (x : α) : Out α Unit :=
  match growend a (JInt.lit .i64 1) with
  | ⟨a, .ok ()⟩ => ⟨a.set (a.length - 1) (some x), .ok ()⟩
  | o => o

/-- `pop!(a)`, `base/array.jl:1700-1707`. -/
def pop (a : Vec α) : Out α (Option α) :=
  if a.isEmpty then ⟨a, .error (.argumentError "array must be non-empty")⟩
  else
    let item := a.getLast?.join
    match deleteend a (JInt.lit .i64 1) with
    | ⟨a, .ok ()⟩ => ⟨a, .ok item⟩
    | ⟨a, .error e⟩ => ⟨a, .error e⟩

/-- `pushfirst!(a, item)`, `base/array.jl:1777-1786` (item already converted). -/
def pushfirst (a : Vec α) (x : α) : Out α Unit :=
  match growbeg a (JInt.lit .i64 1) with
  | ⟨a, .ok ()⟩ => ⟨a.set 0 (some x), .ok ()⟩
  | o => o

/-- `popfirst!(a)`, `base/array.jl:1836-1843`. -/
def popfirst (a : Vec α) : Out α (Option α) :=
  if a.isEmpty then ⟨a, .error (.argumentError "array must be non-empty")⟩
  else
    let item := a.head?.join
    match deletebeg a (JInt.lit .i64 1) with
    | ⟨a, .ok ()⟩ => ⟨a, .ok item⟩
    | ⟨a, .error e⟩ => ⟨a, .error e⟩

/-- `insert!(a, i, item)`, `base/array.jl:1866-1878` (item already converted):
`_growat!(a, i, 1)`, then `a[i] = item`. -/
def insert {t : IntTy} (a : Vec α) (i : JInt t) (x : α) : Out α Unit :=
  match growat a i (JInt.lit .i64 1) with
  | ⟨a', .ok ()⟩ => ⟨a'.set (i.val - 1).toNat (some x), .ok ()⟩
  | o => o

/-! ### Deletion -/

/-- `deleteat!(a, i::Integer)`, `base/array.jl:1899-1903`. -/
def deleteatIndex {t : IntTy} (a : Vec α) (i : JInt t) : Out α Unit :=
  deleteatAt a i (JInt.lit .i64 1)

/-- `length(r::UnitRange{T})` for a nonempty range, `base/range.jl:794-804, 859`:
`Int(last) - Int(first) + 1` for types narrower than `Int`, else
`last - first + 1` in `T`, wrapping. The result type is `Int` or `T`. -/
def unitLengthTy (t : IntTy) : IntTy := if t.bits ≤ 32 then .i64 else t

def unitLength {t : IntTy} (lo hi : JInt t) : JInt (unitLengthTy t) :=
  JInt.wrap _ (hi.val - lo.val + 1)

/-- `deleteat!(a, r::AbstractUnitRange{<:Integer})` for `r = lo:hi` of a non-`Bool`
type, `base/array.jl:1905-1914`. -/
def deleteatRange {t : IntTy} (a : Vec α) (lo hi : JInt t) : Out α Unit :=
  if lo.val > hi.val then ⟨a, .ok ()⟩ else deleteatAt a lo (unitLength lo hi)

/-- `_copy_item!(a, p, q)`, `base/array.jl:1961-1968`: `a[p] = a[q]`, or unset. -/
def copyItem (a : Vec α) (p q : Int) : Vec α :=
  a.set (p - 1).toNat (a[(q - 1).toNat]?.join)

/-- `while q < i; _copy_item!(a, p, q); p += 1; q += 1; end` (`k = i - q` steps). -/
def compact (a : Vec α) (p q : Int) : Nat → Vec α × Int × Int
  | 0 => (a, p, q)
  | k + 1 => compact (copyItem a p q) (p + 1) (q + 1) k

/-- The loop of `_deleteat!(a, inds)` after the first index, `base/array.jl:1977-2000`. -/
def deleteatLoop (a : Vec α) (n : Nat) (p q : Int) : List JInt64 → Out α Unit
  | [] =>
    let (a, p, _) := compact a p q (n + 1 - q).toNat
    deleteend a (JInt.wrap .i64 (n - p + 1))
  | i :: rest =>
    if ¬ (q ≤ i.val ∧ i.val ≤ n) then
      if i.val < q then ⟨a, .error (.argumentError "indices must be unique and sorted")⟩
      else ⟨a, .error .boundsError⟩
    else
      let (a, p, _) := compact a p q (i.val - q).toNat
      deleteatLoop a n p (i.val + 1) rest

/-- `deleteat!(a, inds)` for a vector `inds` of `Int`, `base/array.jl:1946, 1970-2002`
(`to_indices` returns `inds` itself; deleted items go to `Nowhere`). -/
def deleteatInds (a : Vec α) (inds : List JInt64) : Out α Unit :=
  match inds with
  | [] => ⟨a, .ok ()⟩
  | p :: rest =>
    if ¬ (1 ≤ p.val ∧ p.val ≤ a.length) then ⟨a, .error .boundsError⟩
    else deleteatLoop a a.length p.val (p.val + 1) rest

/-- The loop `for (q, i) in enumerate(inds); _copy_item!(a, p, q); p += !i; end`. -/
def maskLoop (a : Vec α) (p q : Int) : List Bool → Vec α × Int
  | [] => (a, p)
  | i :: rest => maskLoop (copyItem a p q) (if i then p else p + 1) (q + 1) rest

/-- `deleteat!(a, inds::AbstractVector{Bool})`, `base/array.jl:2005-2015`. -/
def deleteatMask (a : Vec α) (mask : List Bool) : Out α Unit :=
  if mask.length ≠ a.length then ⟨a, .error .boundsError⟩
  else
    let (a', p) := maskLoop a 1 1 mask
    deleteend a' (JInt.wrap .i64 (a.length - p + 1))

/-- The loop of `_keepat!(a, inds)`, `base/abstractarray.jl:3699-3715`, after `prev`
is defined. Reading an unassigned slot is modelled as copying the slot. -/
def keepatLoop (a : Vec α) (i : Int) (prev : Option Int) : List JInt64 → Out α Int
  | [] => ⟨a, .ok i⟩
  | k :: rest =>
    if (match prev with | some p => decide (¬ p < k.val) | none => false) then
      ⟨a, .error (.argumentError "indices must be unique and sorted")⟩
    else if ¬ (1 ≤ k.val ∧ k.val ≤ a.length) then ⟨a, .error .boundsError⟩
    else
      let a := if i ≠ k.val then copyItem a i k.val else a
      keepatLoop a (i + 1) (some k.val) rest

/-- `keepat!(a, inds)` for a vector `inds` of `Int`, `base/array.jl:3134`:
the loop, then `deleteat!(a, i:lastindex(a))`. -/
def keepat (a : Vec α) (inds : List JInt64) : Out α Unit :=
  match keepatLoop a 1 none inds with
  | ⟨a, .error e⟩ => ⟨a, .error e⟩
  | ⟨a, .ok i⟩ => deleteatRange a (JInt.wrap .i64 i) (JInt.wrap .i64 a.length)

/-- `filter!(f, a)` for a `Vector`, `base/array.jl:3066-3079`: compaction loop
(`j` is advanced after storing), then `resize!(a, j-1)`. `f` sees the stored value;
unassigned slots are not supported (they throw `UndefRefError` in Julia), so the
loop stores `none` and skips it. -/
def filterLoop (f : α → Bool) (a : Vec α) (j : Nat) : List (Option α) → Vec α × Nat
  | [] => (a, j)
  | ai :: rest =>
    let a := a.set (j - 1) ai
    filterLoop f a (if ai.any f then j + 1 else j) rest

def filterBang (f : α → Bool) (a : Vec α) : Vec α :=
  let (a', j) := filterLoop f a 1 a
  if j > a.length then a' else a'.take (j - 1)

/-! ### `splice!` -/

/-- Store the replacement values `a[f+k-1] = x` for `k = 1, 2, ...`
(`base/array.jl:2079-2083, 2145-2149`). Each store converts its value to the
element type (`conv`), which may throw; earlier stores remain. -/
def storeAll {β : Type} (conv : β → Jl α) (a : Vec α) (f : Int) : List β → Out α Unit
  | [] => ⟨a, .ok ()⟩
  | x :: rest =>
    match conv x with
    | .error e => ⟨a, .error e⟩
    | .ok y =>
      if ¬ (1 ≤ f ∧ f ≤ a.length) then ⟨a, .error .boundsError⟩
      else storeAll conv (a.set (f - 1).toNat (some y)) (f + 1) rest

/-- `splice!(a, r::AbstractUnitRange{Int}, ins)` for `r = f:l` (`l ≥ f - 1`),
`base/array.jl:2125-2151`. `ins` holds values of a source type `β`, each converted
to the element type by `conv` when stored. Returns the removed items `a[r]`. -/
def spliceRange {β : Type} (conv : β → Jl α) (a : Vec α) (f l : JInt64) (ins : List β) :
    Out α (Vec α) :=
  -- v = a[r]: checkbounds(a, r), then copy
  if ¬ (f.val > l.val ∨ (1 ≤ f.val ∧ l.val ≤ a.length)) then ⟨a, .error .boundsError⟩
  else
    let v := (a.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat
    let m : JInt64 := JInt.wrap .i64 ins.length
    if m.val = 0 then
      match deleteatRange a f l with
      | ⟨a, .ok ()⟩ => ⟨a, .ok v⟩
      | ⟨a, .error e⟩ => ⟨a, .error e⟩
    else
      let n : JInt64 := JInt.wrap .i64 a.length
      let one : JInt64 := JInt.lit .i64 1
      let d : JInt64 := l - f + one
      let front := (f - one).val < (n - l).val
      let shaped : Out α Unit :=
        if m.val < d.val then
          let delta := d - m
          deleteatAt a (if front then f else l - delta + one) delta
        else if m.val > d.val then
          growat a (if front then f else l + one) (m - d)
        else ⟨a, .ok ()⟩
      match shaped with
      | ⟨a, .error e⟩ => ⟨a, .error e⟩
      | ⟨a, .ok ()⟩ =>
        match storeAll conv a f.val ins with
        | ⟨a, .ok ()⟩ => ⟨a, .ok v⟩
        | ⟨a, .error e⟩ => ⟨a, .error e⟩

/-! ### `resize!` -/

/-- `resize!(a, n; first)`, `base/array.jl:1564-1579`. -/
def resize {t : IntTy} (a : Vec α) (n : JInt t) (first : Bool := false) : Out α Unit :=
  match toInt n with
  | .error e => ⟨a, .error e⟩
  | .ok nl =>
    let l : Int := a.length
    if nl.val > l then
      let d := JInt.wrap .i64 (nl.val - l)
      if first then growbeg a d else growend a d
    else if nl.val ≠ l then
      if nl.val < 0 then ⟨a, .error (.argumentError "new length must be ≥ 0")⟩
      else
        let d := JInt.wrap .i64 (l - nl.val)
        if first then deletebeg a d else deleteend a d
    else ⟨a, .ok ()⟩

/-! ### `append!` and `prepend!` -/

/-- A collection argument of `append!`/`prepend!`: the vector being mutated itself,
or another vector with the given contents (already of the element type). -/
inductive Src (α : Type) where
  | self
  | other (xs : Vec α)

/-- The contents a source has when it is read, given the current vector. -/
def Src.read (a : Vec α) : Src α → Vec α
  | .self => a
  | .other xs => xs

/-- `append!(a::Vector{T}, items::AbstractVector{<:T})`, `base/array.jl:1427-1433`:
`_growend!(a, n)`, then `copyto!(a, length(a)-n+1, items, firstindex(items), n)`.
For `items === a` the copy reads the first `n` elements, which are the old contents. -/
def append1 (a : Vec α) (items : Src α) : Vec α :=
  let xs := items.read a
  a ++ xs

/-- `append!(a, iter...)`, `base/array.jl:1437`: `foreach(v -> append!(a, v), iter)`. -/
def append (a : Vec α) : List (Src α) → Vec α
  | [] => a
  | s :: rest => append (append1 a s) rest

/-- `prepend!(a::Vector{T}, items::AbstractVector{<:T})`, `base/array.jl:1485-1498`:
items other than `a` are unaliased; `_growbeg!(a, n)` then
`copyto!(a, 1, items, lastindex(items)-n+1, n)`, which for `items === a` reads the
last `n` elements, i.e. the old contents. -/
def prepend1 (a : Vec α) (items : Src α) : Vec α :=
  items.read a ++ a

/-- `prepend!(a, iter...)`, `base/array.jl:1502`: `for v = reverse(iter); prepend!(a, v); end`. -/
def prepend (a : Vec α) (srcs : List (Src α)) : Vec α :=
  srcs.reverse.foldl prepend1 a

end

end JuliaLean.ArrayOps
