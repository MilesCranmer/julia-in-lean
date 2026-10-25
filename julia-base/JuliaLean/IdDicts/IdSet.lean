import JuliaLean.IdDicts.Value

/-!
# `IdSet`, base/idset.jl (master `bbfa0ce4150`)

`s.list::Memory{Any}` is modelled slot by slot (`none` = `#undef`), because
the Julia code reads and writes it directly (`s.list[idx + 1] = x`,
`isassigned`, the `s.max` scan, `iterate`). The hash index `s.idxs` is only
touched by the C functions `jl_idset_peek_bp`, `jl_idset_put_idx` and
`jl_idset_pop` (src/idset.c), modelled as a primitive with `===` semantics:
`peek` returns the slot holding a `===` element, `put_idx` has no state of
its own in the model. `jl_idset_put_key` (src/idset.c:83-108) is mirrored:
stable compaction of the keys when the list is full, growth by 50% when less
than a third is free afterwards, then the new key at the first free slot.

Modelling decisions:
* The `newidx` result of `jl_idset_put_key` only feeds `jl_idset_put_idx`,
  i.e. the abstract index; it is not modelled.
* `count` and `max` are `Nat` (indices of an in-memory list cannot wrap).
* 1.13.2 differs only in how `push!` learns the new `max`
  (`s.max = idx < 0 ? -idx : idx + 1`, base/idset.jl:62 in 1.13.2), which
  computes the same value.
-/

namespace JuliaLean.IdDicts

/-- `IdSet{T}` fields, base/idset.jl:29-36. -/
structure IdSet where
  T : JTy
  list : List (Option JVal)
  count : Nat
  max : Nat

/-- `IdSet{T}()`, base/idset.jl:34. -/
def IdSet.new (T : JTy) : IdSet := ⟨T, [], 0, 0⟩

/-- `jl_idset_peek_bp(list, idxs, x)`, src/idset.c:36-40: the 0-based slot of
the element `=== x`, or `-1` (`none`). -/
def peek : List (Option JVal) → JVal → Option Nat
  | [], _ => none
  | o :: t, x => if o = some x then some 0 else (peek t x).map (· + 1)

/-- The compaction loop `idset_compact`, src/idset.c:51-68: the assigned slots
moved to the front in order. -/
def compact (l : List (Option JVal)) : List (Option JVal) :=
  (l.filterMap id).map some ++ List.replicate (l.length - (l.filterMap id).length) none

/-- `jl_idset_put_key(keys, key, &max, &newidx)`, src/idset.c:83-108: the new
keys array and the new `max`. -/
def putKey (keys : List (Option JVal)) (key : JVal) (max : Nat) : List (Option JVal) × Nat :=
  let l := keys.length
  let (keys, i) :=
    if max = l then
      let keys := compact keys
      let i := (keys.filterMap id).length
      if i ≥ l / 3 * 2 then
        let nl := if l < 4 then 4 else (l * 3) / 2
        (keys.take i ++ List.replicate (nl - i) none, i)
      else (keys, i)
    else (keys, max)
  (keys.set i (some key), i + 1)

/-- `push!(s, x)`, base/idset.jl:48-70. -/
def IdSet.push (s : IdSet) (x : JVal) : Out IdSet Unit :=
  match peek s.list x with
  | some idx => ({ s with list := s.list.set idx (some x) }, .ok ())
  | none =>
    let r : Except IErr (List (Option JVal) × Nat) :=
      if s.max < s.list.length then
        -- `@assert !isassigned(s.list, idx + 1)`
        if (s.list[s.max]?).join.isSome then .error .assertionError
        else .ok (s.list.set s.max (some x), s.max + 1)
      else .ok (putKey s.list x s.max)
    match r with
    | .error e => (s, .error e)
    | .ok (list, max) =>
      let s := { s with list := list, max := max }
      -- `@assert s.list[s.max] === x`
      if (s.list[s.max - 1]?).join != some x then (s, .error .assertionError)
      else ({ s with count := s.count + 1 }, .ok ())

/-- `while s.max > 0 && !isassigned(s.list, s.max); s.max -= 1; end`,
base/idset.jl:75-77. -/
def shrinkMax (l : List (Option JVal)) : Nat → Nat
  | 0 => 0
  | m + 1 => if (l[m]?).join.isNone then shrinkMax l m else m + 1

/-- `_pop!(s, x)`, base/idset.jl:71-80; `jl_idset_pop` (src/idset.c:132-139)
unsets the slot. Returns whether `x` was removed. -/
def IdSet.pop! (s : IdSet) (x : JVal) : IdSet × Bool :=
  match peek s.list x with
  | none => (s, false)
  | some idx =>
    let l := s.list.set idx none
    ({ s with list := l, count := s.count - 1, max := shrinkMax l s.max }, true)

/-- `pop!(s, x)`, base/idset.jl:81. -/
def IdSet.pop (s : IdSet) (x : JVal) : Out IdSet JVal :=
  let r := s.pop! x
  (r.1, if r.2 then .ok x else .error .keyError)

/-- `delete!(s, x)`, base/idset.jl:83. -/
def IdSet.delete (s : IdSet) (x : JVal) : IdSet := (s.pop! x).1

/-- `for i = 1:m; unsetindex!(list, i); end` -/
def unsetPrefix (l : List (Option JVal)) (m : Nat) : List (Option JVal) :=
  List.replicate (min m l.length) none ++ l.drop m

/-- `empty!(s)`, base/idset.jl:108-117 (`_zero!(s.idxs)` clears the index). -/
def IdSet.empty (s : IdSet) : IdSet :=
  { s with list := unsetPrefix s.list s.max, count := 0, max := 0 }

/-- The slots `iterate` visits, base/idset.jl:121-126: `1:s.max`, assigned
ones only, in order. -/
def IdSet.elems (s : IdSet) : List JVal := (s.list.take s.max).filterMap id

/-- `iterate(s)` to exhaustion, with the `s.list[state]::S` cast. -/
def IdSet.iterate (s : IdSet) : Except IErr (List JVal) := s.elems.mapM (cast' s.T)
where cast' (T : JTy) (x : JVal) : Except IErr JVal := if isa x T then .ok x else .error .typeError

/-- `in(x, s)`, base/idset.jl:44,47. -/
def IdSet.mem (s : IdSet) (x : JVal) : Bool := (peek s.list x).isSome

/-- `length(s) = s.count`, base/idset.jl:46. -/
def IdSet.length (s : IdSet) : Nat := s.count

/-- `max_values(T)`, base/abstractset.jl:92-103: `typemax(Int)` except
`Nothing` (1); none of the other types of the universe is a small bits type. -/
def maxValues : JTy → Nat
  | .nothing => 1
  | _ => 2 ^ 63 - 1

/-- `union!(s::AbstractSet{T}, itr)`, base/abstractset.jl:105-112 (the
`sizehint!` call is a no-op for `IdSet`, base/idset.jl:85-97). -/
def IdSet.union (s : IdSet) : List JVal → Out IdSet Unit
  | [] => (s, .ok ())
  | x :: xs =>
    let r := s.push x
    match r.2 with
    | .error e => (r.1, .error e)
    | .ok () => if r.1.length == maxValues s.T then (r.1, .ok ()) else r.1.union xs

/-- `setdiff!(s, itr)`, base/abstractset.jl:250-255. -/
def IdSet.setdiff (s : IdSet) (xs : List JVal) : IdSet := xs.foldl IdSet.delete s

/-- `IdSet{T}(itr) = union!(IdSet{T}(), itr)`, base/idset.jl:37. -/
def IdSet.ofList (T : JTy) (xs : List JVal) : IdSet := ((IdSet.new T).union xs).1

/-! ## Call sequences -/

inductive SOp where
  | push (x : JVal)
  | pop (x : JVal)
  | pop3 (x default : JVal)
  | delete (x : JVal)
  | empty
  | sizehint (n : JInt .i64)
  | union (xs : List JVal)
  | setdiff (xs : List JVal)

/-- One call; a throwing call leaves the state it reached. -/
def SOp.run (s : IdSet) : SOp → IdSet
  | .push x => (s.push x).1
  | .pop x => (s.pop x).1
  | .pop3 x _ => (s.pop! x).1
  | .delete x => s.delete x
  | .empty => s.empty
  | .sizehint _ => s
  | .union xs => (s.union xs).1
  | .setdiff xs => s.setdiff xs

def runS (T : JTy) (ops : List SOp) : IdSet := ops.foldl SOp.run (IdSet.new T)

/-- Number of elements a call sequence mentions (an upper bound on the size
of the set). -/
def SOp.size : SOp → Nat
  | .push _ => 1
  | .union xs => xs.length
  | _ => 0

/-! ## Reference `===` set (insertion-ordered list) -/

def rPush (xs : List JVal) (x : JVal) : List JVal := if x ∈ xs then xs else xs ++ [x]

def SOp.ref (xs : List JVal) : SOp → List JVal
  | .push x => rPush xs x
  | .pop x | .pop3 x _ | .delete x => xs.erase x
  | .empty => []
  | .sizehint _ => xs
  | .union ys => ys.foldl rPush xs
  | .setdiff ys => ys.foldl List.erase xs

def refS (ops : List SOp) : List JVal := ops.foldl SOp.ref []

/-! ## Collections on the other side of the generic set functions -/

/-- `Set(itr)` on the universe: an `isequal`-keyed set. `push!` of an
`isequal` element replaces the stored key (`h.keys[index] = key`,
base/dict.jl `setindex!`), so the last representative wins. The Dicts area
proves the `Set` table agrees with an `isequal` reference (`dicts-set-*`).
Iteration order is the hash order in Julia, insertion order here; the uses
below depend only on membership and length. -/
def jsetOf (xs : List JVal) : List JVal :=
  xs.foldl (fun acc x => if acc.any (isequal x) then acc.map (fun y => if isequal x y then x else y)
    else acc ++ [x]) []

/-- The collections handed to the generic set functions. -/
inductive Coll where
  /-- a `Vector{Any}`: `haslength`, no fast `in`, `in` uses `==` -/
  | vec (xs : List JVal)
  /-- a `Set{Any}` with these (pairwise non-`isequal`) elements -/
  | set (xs : List JVal)
  /-- an `IdSet{Any}` -/
  | ids (s : IdSet)

def Coll.isSet : Coll → Bool
  | .vec _ => false
  | _ => true

/-- `hasfastin`, base/abstractset.jl:367-368 -/
def Coll.hasfastin : Coll → Bool := Coll.isSet

def Coll.length : Coll → Nat
  | .vec xs | .set xs => xs.length
  | .ids s => s.length

/-- Iteration (for an `IdSet{Any}` the `::Any` cast never throws). -/
def Coll.elems : Coll → List JVal
  | .vec xs | .set xs => xs
  | .ids s => s.elems

def Coll.mem : Coll → JVal → Bool
  | .vec xs, x => xs.any (isequal x)
  | .set xs, x => xs.any (isequal x)
  | .ids s, x => s.mem x

/-- The body of `issubset(a, b)`, base/abstractset.jl:335-350, once `b` is
known to have fast `in` (a `Set` or `IdSet`). -/
def issubsetFast (a b : Coll) : Bool :=
  if a.isSet && a.length > b.length then false else a.elems.all b.mem

/-- `issubset(a, b)`, base/abstractset.jl:335-350: a vector `b` longer than
`FASTIN_SET_THRESHOLD = 70` is replaced by `Set(b)` and the call repeated. -/
def issubset (a b : Coll) : Bool :=
  if b.hasfastin then issubsetFast a b
  else if a.isSet && a.length > b.length then false
  else if b.length > 70 then issubsetFast a (.set (jsetOf b.elems))
  else a.elems.all b.mem

/-- `==(a::AbstractSet, b::AbstractSet)`, base/abstractset.jl:622. -/
def setEq (a b : Coll) : Bool := a.length == b.length && issubset a b

/-- `issetequal(a, b)`, base/abstractset.jl:521-536. -/
def issetequal (a b : Coll) : Bool :=
  match a.isSet, b.isSet with
  | true, true => setEq a b
  | true, false => setEq a (.set (jsetOf b.elems))
  | false, true => if a.length < b.length then false else setEq (.set (jsetOf a.elems)) b
  | false, false => setEq (.set (jsetOf a.elems)) (.set (jsetOf b.elems))

/-- `symdiff!(s::AbstractSet, itr::AbstractSet)`, base/abstractset.jl:299-304. -/
def IdSet.symdiffSet (s : IdSet) : List JVal → IdSet
  | [] => s
  | x :: xs => (if s.mem x then s.delete x else (s.push x).1).symdiffSet xs

/-- `symdiff!(s, itr)` for a vector `itr`: `symdiff!(s, Set(itr))`,
base/abstractset.jl:297. -/
def IdSet.symdiffVec (s : IdSet) (xs : List JVal) : IdSet := s.symdiffSet (jsetOf xs)

end JuliaLean.IdDicts
