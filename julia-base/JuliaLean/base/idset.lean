import JuliaLean.Core
import JuliaLean.base.iddict
import JuliaLean.base.cmem

/-!
# Model of `base/idset.jl`

Typed model of every method in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
The list memory records assigned and unassigned `Any` slots; index memory and C table calls,
allocation/copy, generic set calls, and type assertions are typed parameters. `IdDict.RuntimeOps`
supplies the shared memory and `===` operations. `_zero!` threads index-memory state through
the byte-level `MemsetLaw` of `base/cmem.jl`, lifted through `indexHeap` and `pointerView`.
Julia `Int` fields use `JInt .i64`.
-/

namespace JuliaLean.base.idset

open JuliaLean JuliaLean.base.iddict
open JuliaLean.base.pointer

/--
Julia source: base/idset.jl:29-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct IdSet{K} <: AbstractSet{K}
    list::Memory{Any}
    idxs::Union{Memory{UInt8}, Memory{UInt16}, Memory{UInt32}}
    count::Int
    max::Int # n.b. always <= length(list)
```
-/
structure IdSet (K A I : Type) where
  list : List (Option A)
  idxs : I
  count : JInt .i64
  max : JInt .i64

structure Runtime (A I E Ptr Preserve : Type) where
  iddict : JuliaLean.base.iddict.RuntimeOps A A A (List (Option A)) E Ptr Preserve
  allocateIndices8 : Nat → Except E I
  copyIndices : I → Except E I
  peekBucket : List (Option A) → I → A → JInt .i64
  putKey : List (Option A) → A → JInt .i64 →
    Except E (List (Option A) × JInt .u64 × JInt .i64)
  putIndex : List (Option A) → I → JInt .i64 → Except E I
  popKey : List (Option A) → I → A →
    Except E (List (Option A) × I × JInt .i64)
  boundsError : E
  assertionError : String → E
  keyError : A → E
  uintToInt : JInt .u64 → Except E (JInt .i64)
  preserveBegin : I → Preserve
  unsafeConvert : I → Ptr
  eltype : I → IntTy
  sizeof : IntTy → JInt .i64
  memoryLength : I → JInt .i64
  indexHeap : I → ByteHeap
  pointerView : Ptr → JuliaLean.base.pointer.Ptr Unit
  memset : I → Ptr → JuliaLean.base.cmem.CInt → JInt .u64 → I × Ptr
  memsetStandard : ∀ memory p value size,
    JuliaLean.base.cmem.validRange (indexHeap memory) (pointerView p) size →
    let (after, result) := memset memory p value size
    (pointerView result).address = (pointerView p).address ∧
      JuliaLean.base.cmem.fillEffect (indexHeap memory) (indexHeap after)
        (pointerView p) size (JInt.wrap .u8 value.val)
  preserveEnd : Preserve → Unit
  castTo : {K : Type} → A → Except E K
  union : {K Itr : Type} → IdSet K A I → Itr → CallResult E (IdSet K A I) (IdSet K A I)
  setdiff : {K Itr : Type} → IdSet K A I → Itr → CallResult E (IdSet K A I) (IdSet K A I)
  unsafeFilter : {K : Type} → (A → Bool) → IdSet K A I →
    CallResult E (IdSet K A I) (IdSet K A I)

def memoryPosition (index : JInt .i64) : Option Nat :=
  if index.val ≤ 0 then none else some (index.val.toNat - 1)

def isAssigned {A : Type} (memory : List (Option A)) (index : JInt .i64) : Bool :=
  match memoryPosition index with
  | none => false
  | some position =>
      match memory[position]? with
      | none => false
      | some value => value.isSome

def setMemory {A E : Type} (boundsError : E) (memory : List (Option A))
    (index : JInt .i64) (value : Option A) : Except E (List (Option A)) :=
  match memoryPosition index with
  | none => .error boundsError
  | some position =>
      match memory[position]? with
      | none => .error boundsError
      | some _ => .ok (memory.take position ++ [value] ++ memory.drop (position + 1))


/--
Julia source: base/idset.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IdSet{T}() where {T} = new(Memory{Any}(undef, 0), Memory{UInt8}(undef, 0), 0, 0)
```
-/
def emptyTyped {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve) :
    Except E (IdSet K A I) := do
  let list ← ops.iddict.allocate 0
  let idxs ← ops.allocateIndices8 0
  .ok ⟨list, idxs, JInt.wrap .i64 0, JInt.wrap .i64 0⟩

/--
Julia source: base/idset.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    IdSet{T}(s::IdSet{T}) where {T} = new(copy(s.list), copy(s.idxs), s.count, s.max)
```
-/
def copyConstruct {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) : Except E (IdSet K A I) := do
  let list ← ops.iddict.copyMemory s.list
  let idxs ← ops.copyIndices s.idxs
  .ok ⟨list, idxs, s.count, s.max⟩

/--
Julia source: base/idset.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdSet{T}(itr) where {T} = union!(IdSet{T}(), itr)
```
-/
def fromIterator {K A I E Ptr Preserve Itr : Type} (ops : Runtime A I E Ptr Preserve)
    (itr : Itr) : Except E (IdSet K A I) := do
  let s ← emptyTyped ops
  let united := ops.union s itr
  match united.result with
  | .error e => .error e
  | .ok _ => .ok united.state

/--
Julia source: base/idset.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IdSet() = IdSet{Any}()
```
-/
def emptyAny {A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve) :
    Except E (IdSet A A I) := emptyTyped ops

/--
Julia source: base/idset.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copymutable(s::IdSet) = typeof(s)(s)
```
-/
def copymutable {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) : Except E (IdSet K A I) := copyConstruct ops s

/--
Julia source: base/idset.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
emptymutable(s::IdSet{T}, ::Type{U}=T) where {T,U} = IdSet{U}()
```
-/
def emptymutable {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (_s : IdSet K A I) : Except E (IdSet K A I) := emptyTyped ops

/--
Julia source: base/idset.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
emptymutable(s::IdSet{T}, ::Type{U}=T) where {T,U} = IdSet{U}()
```
-/
def emptymutableAs {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (_s : IdSet K A I) (U : Type) : Except E (IdSet U A I) := emptyTyped ops

/--
Julia source: base/idset.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(s::IdSet) = typeof(s)(s)
```
-/
def copy {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) : Except E (IdSet K A I) := copyConstruct ops s

/--
Julia source: base/idset.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(s::IdSet, @nospecialize(key)) = ccall(:jl_idset_peek_bp, Int, (Any, Any, Any), s.list, s.idxs, key) != -1
```
-/
def haskey {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) (key : A) : Bool :=
  decide (ops.peekBucket s.list s.idxs key ≠ JInt.wrap .i64 (-1))

/--
Julia source: base/idset.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(s::IdSet) = s.count == 0
```
-/
def isempty {K A I : Type} (s : IdSet K A I) : Bool := s.count.val == 0

/--
Julia source: base/idset.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(s::IdSet)  = s.count
```
-/
def length {K A I : Type} (s : IdSet K A I) : JInt .i64 := s.count

/--
Julia source: base/idset.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(@nospecialize(x), s::IdSet) = haskey(s, x)
```
-/
def «in» {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (x : A) (s : IdSet K A I) : Bool := haskey ops s x

/--
Julia source: base/idset.jl:48-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(s::IdSet, @nospecialize(x))
    idx = ccall(:jl_idset_peek_bp, Int, (Any, Any, Any), s.list, s.idxs, x)
    if idx >= 0
        s.list[idx + 1] = x
    else
        if s.max < length(s.list)
            idx = s.max
            @assert !isassigned(s.list, idx + 1) "bucket is already occupied"
            s.list[idx + 1] = x
            s.max = idx + 1
        else
            newidx = RefValue{Int}(0)
            newmax = RefValue{Csize_t}(s.max)
            setfield!(s, :list, ccall(:jl_idset_put_key, Any, (Any, Any, Ptr{Csize_t}, Ptr{Int}), s.list, x, newmax, newidx))
            idx = newidx[]
            s.max = Int(newmax[])
        end
        @assert s.list[s.max] === x "unexpected object in bucket"
        setfield!(s, :idxs, ccall(:jl_idset_put_idx, Any, (Any, Any, Int), s.list, s.idxs, idx))
        s.count += 1
    end
    s
end
```
-/
def push! {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) (x : A) : CallResult E (IdSet K A I) (IdSet K A I) :=
  let idx := ops.peekBucket s.list s.idxs x
  if idx.val ≥ 0 then
    match setMemory ops.boundsError s.list (idx + JInt.wrap .i64 1) (some x) with
    | .error e => resultWithState (.error e) s
    | .ok list =>
        let updated := { s with list := list }
        resultWithState (.ok updated) updated
  else
    let prepared : CallResult E (IdSet K A I) (IdSet K A I × JInt .i64) :=
      if s.max.val < (JInt.wrap .i64 (Int.ofNat s.list.length)).val then
        let idx := s.max
        if isAssigned s.list (idx + JInt.wrap .i64 1) then
          resultWithState (.error (ops.assertionError "bucket is already occupied")) s
        else
          match setMemory ops.boundsError s.list (idx + JInt.wrap .i64 1) (some x) with
          | .error e => resultWithState (.error e) s
          | .ok list =>
              let updated := { s with list := list, max := idx + JInt.wrap .i64 1 }
              resultWithState (.ok (updated, idx)) updated
      else
        match ops.putKey s.list x s.max with
        | .error e => resultWithState (.error e) s
        | .ok (list, newmax, newidx) =>
            let withList := { s with list := list }
            match ops.uintToInt newmax with
            | .error e => resultWithState (.error e) withList
            | .ok max =>
                let updated := { withList with max := max }
                resultWithState (.ok (updated, newidx)) updated
    match prepared.result with
    | .error e => resultWithState (.error e) prepared.state
    | .ok (updated, idx) =>
        match ops.iddict.memoryAt updated.list updated.max with
        | .error e => resultWithState (.error e) updated
        | .ok value =>
            if ops.iddict.sameIdentity value x then
              match ops.putIndex updated.list updated.idxs idx with
              | .error e => resultWithState (.error e) updated
              | .ok idxs =>
                  let final := { updated with idxs := idxs, count := updated.count + JInt.wrap .i64 1 }
                  resultWithState (.ok final) final
            else resultWithState (.error (ops.assertionError "unexpected object in bucket")) updated

def shrinkMax {A : Type} (list : List (Option A)) (max : JInt .i64) : Nat → JInt .i64
  | 0 => max
  | fuel + 1 =>
      if max.val > 0 && !isAssigned list max then
        shrinkMax list (max - JInt.wrap .i64 1) fuel
      else max

/--
Julia source: base/idset.jl:71-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _pop!(s::IdSet, @nospecialize(x))
    removed = ccall(:jl_idset_pop, Int, (Any, Any, Any), s.list, s.idxs, x)
    if removed != -1
        s.count -= 1
        while s.max > 0 && !isassigned(s.list, s.max)
            s.max -= 1
        end
    end
    removed
end
```
-/
def _pop! {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) (x : A) : CallResult E (IdSet K A I) (JInt .i64) :=
  match ops.popKey s.list s.idxs x with
  | .error e => resultWithState (.error e) s
  | .ok (list, idxs, removed) =>
      let updated := { s with list := list, idxs := idxs }
      if removed.val ≠ -1 then
        let max := shrinkMax updated.list updated.max (updated.max.val.toNat + 1)
        let final := { updated with count := updated.count - JInt.wrap .i64 1, max := max }
        resultWithState (.ok removed) final
      else resultWithState (.ok removed) updated

/--
Julia source: base/idset.jl:81-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pop!(s::IdSet, @nospecialize(x)) = _pop!(s, x) == -1 ? throw(KeyError(x)) : x
```
-/
def pop! {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) (x : A) : CallResult E (IdSet K A I) A :=
  let removed := _pop! ops s x
  match removed.result with
  | .error e => resultWithState (.error e) removed.state
  | .ok index =>
      if index.val == -1 then resultWithState (.error (ops.keyError x)) removed.state
      else resultWithState (.ok x) removed.state

/--
Julia source: base/idset.jl:82-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pop!(s::IdSet, @nospecialize(x), @nospecialize(default)) = _pop!(s, x) == -1 ? default : x
```
-/
def popDefault {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) (x default : A) : CallResult E (IdSet K A I) A :=
  let removed := _pop! ops s x
  match removed.result with
  | .error e => resultWithState (.error e) removed.state
  | .ok index =>
      if index.val == -1 then resultWithState (.ok default) removed.state
      else resultWithState (.ok x) removed.state

/--
Julia source: base/idset.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
delete!(s::IdSet, @nospecialize(x)) = (_pop!(s, x); s)
```
-/
def delete! {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) (x : A) : CallResult E (IdSet K A I) (IdSet K A I) :=
  let removed := _pop! ops s x
  match removed.result with
  | .error e => resultWithState (.error e) removed.state
  | .ok _ => resultWithState (.ok removed.state) removed.state

/--
Julia source: base/idset.jl:85-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sizehint!(s::IdSet, newsz::Integer)
    # TODO: grow/compact list and perform rehash, if profitable?
    # TODO: shrink?
    # s.list = resize(s.list, newsz)
    # newsz = _tablesz(newsz)
    # oldsz = length(s.idxs)
    # #grow at least 25%
    # if newsz < (oldsz*5)>>2
    #     return s
    # end
    # rehash!(s, newsz)
    nothing
end
```
-/
def sizehint! {K A I E N : Type} (s : IdSet K A I) (_newsz : N) :
    CallResult E (IdSet K A I) Unit := resultWithState (.ok ()) s

/--
Julia source: base/idset.jl:99-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _zero!(a::Memory{<:BitInteger})
    t = @_gc_preserve_begin a
    p = unsafe_convert(Ptr{Cvoid}, a)
    T = eltype(a)
    memset(p, 0x0, (sizeof(T) * length(a)) % UInt)
    @_gc_preserve_end t
    return a
end
```
-/
def _zero! {A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve) (a : I) : I :=
  let t := ops.preserveBegin a
  let p := ops.unsafeConvert a
  let T := ops.eltype a
  let (after, _) := ops.memset a p (JInt.wrap .i32 0)
    ((ops.sizeof T * ops.memoryLength a).rem .u64)
  let _ := ops.preserveEnd t
  after

/--
Julia source: base/idset.jl:108-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(s::IdSet)
    _zero!(s.idxs)
    list = s.list
    for i = 1:s.max
        unsetindex!(list, i)
    end
    s.count = 0
    s.max = 0
    s
end
```
-/
def clearSlots {A E : Type} (boundsError : E) (max : Int)
    (slots : List (Option A)) (index fuel : Nat) : CallResult E (List (Option A)) Unit :=
  match fuel with
  | 0 => resultWithState (.ok ()) slots
  | fuel + 1 =>
      if Int.ofNat index > max then resultWithState (.ok ()) slots
      else
        match setMemory boundsError slots (JInt.wrap .i64 (Int.ofNat index)) none with
        | .error e => resultWithState (.error e) slots
        | .ok list => clearSlots boundsError max list (index + 1) fuel

def clearList {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) (index fuel : Nat) : CallResult E (IdSet K A I) Unit :=
  let cleared := clearSlots ops.boundsError s.max.val s.list index fuel
  resultWithState cleared.result { s with list := cleared.state }

def empty! {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) : CallResult E (IdSet K A I) (IdSet K A I) :=
  let idxs := _zero! ops s.idxs
  let before := { s with idxs := idxs }
  let cleared := clearList ops before 1 s.max.val.toNat
  match cleared.result with
  | .error e => resultWithState (.error e) cleared.state
  | .ok _ =>
      let final := { cleared.state with count := JInt.wrap .i64 0, max := JInt.wrap .i64 0 }
      resultWithState (.ok final) final

/--
Julia source: base/idset.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter!(f, d::IdSet) = unsafe_filter!(f, d)
```
-/
def filter! {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (f : A → Bool) (d : IdSet K A I) : CallResult E (IdSet K A I) (IdSet K A I) :=
  ops.unsafeFilter f d

/--
Julia source: base/idset.jl:121-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(s::IdSet{S}, state=0) where {S}
    while true
        state += 1
        state > s.max && return nothing
        isassigned(s.list, state) && return s.list[state]::S, state
    end
end
```
-/
def findAssigned {A : Type} (slots : List (Option A)) (index fuel : Nat) : Option (A × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match slots with
      | [] => none
      | some value :: _ => some (value, index)
      | none :: rest => findAssigned rest (index + 1) fuel

def iterate {K A I E Ptr Preserve : Type} (ops : Runtime A I E Ptr Preserve)
    (s : IdSet K A I) (state : JInt .i64 := JInt.wrap .i64 0) :
    CallResult E (IdSet K A I) (Option (K × JInt .i64)) :=
  let state := state + JInt.wrap .i64 1
  if state.val > s.max.val then resultWithState (.ok none) s
  else
    let first := if state.val > 0 then state.val.toNat else 1
    let fuel := (s.max.val - Int.ofNat first + 1).toNat
    let slots := s.list.drop (first - 1)
    match findAssigned slots first fuel with
    | none => resultWithState (.ok none) s
    | some (_, position) =>
        let index := JInt.wrap .i64 (Int.ofNat position)
        match ops.iddict.memoryAt s.list index with
        | .error e => resultWithState (.error e) s
        | .ok stored =>
            match ops.castTo stored with
            | .error e => resultWithState (.error e) s
            | .ok typed => resultWithState (.ok (some (typed, index))) s

end JuliaLean.base.idset
