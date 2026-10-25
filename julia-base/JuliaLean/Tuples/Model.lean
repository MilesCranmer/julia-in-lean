import JuliaLean.Core

/-!
Model of Julia tuples (`base/tuple.jl`, `base/ntuple.jl`, the tuple methods of
`base/range.jl`, `base/operators.jl`, `base/array.jl`, `base/bitarray.jl`).

A tuple is a `List α` of its elements. Methods whose body differs between short
tuples and `Any32` tuples (32 or more elements) are modelled by both bodies and
a dispatcher on the lengths. Loops over `1:n` are index recursions (`go i k`
visits `i+1, ..., i+k` in Julia's one-based numbering).

Exceptions: `Err.jl` wraps the shared `JlError`; `TypeError`, `FieldError` and
`ErrorException` have their own constructors because `Core` has none. Element
comparisons are abstract (`Ops`), with `none` for `missing`.
-/

namespace JuliaLean.Tuples

inductive Err where
  | jl (e : JlError)
  | typeError
  | fieldError
  | errorException
  deriving Repr, DecidableEq, Inhabited

abbrev R (α : Type) := Except Err α

def bounds {α : Type} : R α := .error (.jl .boundsError)
def argErr {α : Type} (msg : String) : R α := .error (.jl (.argumentError msg))
def liftJ {α : Type} : Jl α → R α
  | .ok a => .ok a
  | .error e => .error (.jl e)

/-- Julia exception type of an error (messages are ignored). -/
def Err.kind : Err → String
  | .jl (.overflowError _) => "OverflowError"
  | .jl (.argumentError _) => "ArgumentError"
  | .jl .boundsError => "BoundsError"
  | .jl (.inexactError _) => "InexactError"
  | .jl .divideError => "DivideError"
  | .jl (.domainError _) => "DomainError"
  | .jl (.methodError _) => "MethodError"
  | .typeError => "TypeError"
  | .fieldError => "FieldError"
  | .errorException => "ErrorException"

/-- Same value, or exceptions of the same type. -/
def SameOutcome {α : Type} : R α → R α → Prop
  | .ok a, .ok b => a = b
  | .error e, .error f => e.kind = f.kind
  | _, _ => False

/-! ## Scalar indices -/

/-- A scalar `Integer` index: one of the ten `BitInteger` types, or `Bool`. -/
inductive Idx where
  | int (t : IntTy) (v : JInt t)
  | bool (b : Bool)

/-- The mathematical value of an index (`true` is 1). -/
def Idx.val : Idx → Int
  | .int _ v => v.val
  | .bool b => if b then 1 else 0

/-- `getfield(t, i::Int)` with bounds checking. -/
def getfield {α : Type} (t : List α) (i : Int) : R α :=
  if 1 ≤ i then
    match t[(i - 1).toNat]? with
    | some a => .ok a
    | none => bounds
  else bounds

/-- `getindex(t, i::Int)` (`base/tuple.jl:33`) and `getindex(t, i::Integer) =
getfield(t, convert(Int, i))` (`base/tuple.jl:34`); `Bool <: Integer` takes the
second method. -/
def getindex {α : Type} (t : List α) : Idx → R α
  | .int ty v =>
    if ty = .i64 then getfield t v.val
    else do let j ← liftJ (JInt.convert .i64 v.val); getfield t j.val
  | .bool b => do let j ← liftJ (JInt.convert .i64 (if b then 1 else 0)); getfield t j.val

/-- `setindex(x, v, i::Integer)`, `base/tuple.jl:55-64`: `1 <= i <= length(x)`
(exact mixed-type comparison), then `_setindex` rebuilds the tuple with
`ifelse(j == i, v, args[j])`. -/
def setindex {α : Type} (t : List α) (v : α) (i : Idx) : R (List α) :=
  if 1 ≤ i.val ∧ i.val ≤ t.length then
    .ok ((List.range t.length).zipWith (fun (j : Nat) a => if ((j : Int) + 1) = i.val then v else a) t)
  else bounds

/-- `get(t, i::Integer, default)`, `base/tuple.jl:40`. -/
def get {α : Type} (t : List α) (i : Idx) (d : α) : R α :=
  if 1 ≤ i.val ∧ i.val ≤ t.length then getindex t i else .ok d

/-- `isassigned(v::Tuple, i::Integer)`, `base/tuple.jl:681-684`. -/
def isassigned {α : Type} (t : List α) (i : Idx) : R Bool :=
  .ok (decide (1 ≤ i.val ∧ i.val ≤ t.length))

/-- The `Vector` methods with a `Bool` scalar index: `to_index(i::Bool)` throws
(`base/indices.jl:259`); `get`/`isassigned` reject `Bool` the same way. -/
def vecBoolIndex {β : Type} : R β := argErr "invalid index: true of type Bool"

/-! ## Front, tail, first, last -/

/-- `_front`, `base/tuple.jl:348-353`. -/
def frontRec {α : Type} : List α → R (List α)
  | [] => argErr "Cannot call front on an empty tuple."
  | [_] => .ok []
  | v :: t => do let r ← frontRec t; pure (v :: r)

/-- `index loop` helper: `(t[i+1], ..., t[i+k])` (one-based), or `BoundsError`. -/
def readRange {α : Type} (t : List α) : Nat → Nat → R (List α)
  | _, 0 => .ok []
  | i, k + 1 => do
    let a ← getfield t (i + 1)
    let r ← readRange t (i + 1) k
    pure (a :: r)

/-- `front(t::Any32)`, `base/tuple.jl:380-384`: `ntuple(i -> getfield(t, i), n-1)`. -/
def frontAny32 {α : Type} (t : List α) : R (List α) := readRange t 0 (t.length - 1)

/-- `front(t)`: `base/tuple.jl:344-347`, `375-378` (exactly 32), `380-384` (longer). -/
def front {α : Type} (t : List α) : R (List α) :=
  if t.length > 32 then frontAny32 t else frontRec t

/-- `tail(x) = argtail(x...)`, `tail(()) = ArgumentError`, `base/essentials.jl:523,541-542`. -/
def tail {α : Type} : List α → R (List α)
  | [] => argErr "Cannot call tail on an empty tuple."
  | _ :: r => .ok r

/-- `first(()) = ArgumentError`, `first(t) = t[1]`, `base/tuple.jl:270-271`. -/
def first {α : Type} : List α → R α
  | [] => argErr "tuple must be non-empty"
  | t => getfield t 1

/-- `last(a) = a[end]` (`base/abstractarray.jl`), `lastindex(t) = length(t)`, `base/tuple.jl:30`. -/
def last {α : Type} (t : List α) : R α := getfield t t.length

/-! ## ntuple, fill_to_length, reverse -/

/-- `ntuple(f, n::Int)`, `base/ntuple.jl:17-32,36-40`: lengths 0..10 are unrolled,
other lengths go to `_ntuple`, which rejects negative `n`. -/
def ntupleInt {α : Type} (f : Nat → α) (n : Int) : R (List α) :=
  if 0 ≤ n ∧ n ≤ 10 then .ok ((List.range n.toNat).map fun k => f (k + 1))
  else if n ≥ 0 then .ok ((List.range n.toNat).map fun k => f (k + 1))
  else argErr s!"tuple length should be ≥ 0, got {n}"

/-- `ntuple(f, n::Integer) = ntuple(f, convert(Int, n))`, `base/ntuple.jl:33`. -/
def ntuple {α : Type} (f : Nat → α) (t : IntTy) (n : JInt t) : R (List α) := do
  let m ← liftJ (JInt.convert .i64 n.val)
  ntupleInt f m.val

/-- `ntuple(f, ::Val{N})`, `base/ntuple.jl:65-72` (`N::Int`). -/
def ntupleVal {α : Type} (f : Nat → α) (N : JInt .i64) : R (List α) :=
  if N.val ≥ 0 then .ok ((List.range N.val.toNat).map fun k => f (k + 1))
  else argErr s!"tuple length should be ≥ 0, got {N.val}"

/-- `fill_to_length`, the specialised methods `base/tuple.jl:442-445` and the
general method `base/ntuple.jl:74-85`. -/
def fillToLength {α : Type} (t : List α) (v : α) (N : JInt .i64) : R (List α) :=
  if (t.length : Int) = N.val then .ok t
  else if t.length = 0 ∧ N.val = 1 then .ok [v]
  else if t.length = 1 ∧ N.val = 2 then .ok (t ++ [v])
  else if t.length = 0 ∧ N.val = 2 then .ok [v, v]
  else if (t.length : Int) > N.val then argErr "input tuple of length M, requested N"
  else .ok (t ++ List.replicate (N.val - t.length).toNat v)

/-- `revargs`, `base/tuple.jl:668-671`. -/
def revargs {α : Type} : List α → List α
  | [] => []
  | x :: r => revargs r ++ [x]

/-- `reverse(t::NTuple{N})`, `base/ntuple.jl:89-93`: `ntuple(i -> t[end+1-i], Val(N))`. -/
def reverseNTuple {α : Type} (t : List α) : R (List α) :=
  (List.range t.length).mapM fun (k : Nat) => getfield t ((t.length : Int) + 1 - ((k : Int) + 1))

/-! ## map -/

/-- One-argument `map`, `base/tuple.jl:358-362`. -/
def map1Rec {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | [a] => [f a]
  | [a, b] => [f a, f b]
  | [a, b, c] => [f a, f b, f c]
  | a :: r => f a :: map1Rec f r

/-- `map(f, t::Any32)`, `base/tuple.jl:394-401`: `A[i] = f(t[i])` for `i = 1:n`. -/
def map1Loop {α β : Type} (f : α → β) (t : List α) : Nat → Nat → List β
  | _, 0 => []
  | i, k + 1 => match t[i]? with
    | some a => f a :: map1Loop f t (i + 1) k
    | none => []

def map1 {α β : Type} (f : α → β) (t : List α) : List β :=
  if t.length ≥ 32 then map1Loop f t 0 t.length else map1Rec f t

/-- Two-argument `map`, `base/tuple.jl:403-411`. -/
def map2Rec {α β γ : Type} (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | [a], [b] => [f a b]
  | [a, a'], [b, b'] => [f a b, f a' b']
  | a :: r, b :: s => f a b :: map2Rec f r s

/-- `map(f, t::Any32, s::Any32)`, `base/tuple.jl:412-419`, `n = min(length(t), length(s))`. -/
def map2Loop {α β γ : Type} (f : α → β → γ) (t : List α) (s : List β) : Nat → Nat → List γ
  | _, 0 => []
  | i, k + 1 => match t[i]?, s[i]? with
    | some a, some b => f a b :: map2Loop f t s (i + 1) k
    | _, _ => []

def map2 {α β γ : Type} (f : α → β → γ) (t : List α) (s : List β) : List γ :=
  if t.length ≥ 32 ∧ s.length ≥ 32 then map2Loop f t s 0 (min t.length s.length)
  else map2Rec f t s

/-- Three-argument `map`, `base/tuple.jl:421-431` (`anyempty`, `heads`, `tails`). -/
def map3Rec {α β γ δ : Type} (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | a :: r, b :: s, c :: u => f a b c :: map3Rec f r s u
  | _, _, _ => []

/-- `map(f, t1::Any32, t2::Any32, ts::Any32...)`, `base/tuple.jl:432-439`. -/
def map3Loop {α β γ δ : Type} (f : α → β → γ → δ) (t : List α) (s : List β) (u : List γ) :
    Nat → Nat → List δ
  | _, 0 => []
  | i, k + 1 => match t[i]?, s[i]?, u[i]? with
    | some a, some b, some c => f a b c :: map3Loop f t s u (i + 1) k
    | _, _, _ => []

def map3 {α β γ δ : Type} (f : α → β → γ → δ) (t : List α) (s : List β) (u : List γ) : List δ :=
  if t.length ≥ 32 ∧ s.length ≥ 32 ∧ u.length ≥ 32 then
    map3Loop f t s u 0 (min t.length (min s.length u.length))
  else map3Rec f t s u

/-! ## find, filter, in -/

/-- `_findfirst_rec`, `base/tuple.jl:522-523`. -/
def findfirstRec {α : Type} (f : α → Bool) (i : Nat) : List α → Option Nat
  | [] => none
  | a :: r => if f a then some i else findfirstRec f (i + 1) r

/-- `_findfirst_loop`, `base/tuple.jl:524-529`. -/
def findfirstLoop {α : Type} (f : α → Bool) (t : List α) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, k + 1 => match t[i]? with
    | some a => if f a then some (i + 1) else findfirstLoop f t (i + 1) k
    | none => none

/-- `findfirst(f::Function, t::Tuple)`, `base/tuple.jl:530`. -/
def findfirst {α : Type} (f : α → Bool) (t : List α) : Option Nat :=
  if t.length < 32 then findfirstRec f 1 t else findfirstLoop f t 0 t.length

/-- `_findlast_loop`, `base/tuple.jl:537-542`: `for i in reverse(1:length(t))`
(`i = k, k-1, ..., 1`). -/
def findlastLoop {α : Type} (f : α → Bool) (t : List α) : Nat → Option Nat
  | 0 => none
  | k + 1 => match t[k]? with
    | some a => if f a then some (k + 1) else findlastLoop f t k
    | none => none

/-- `findlast(f::Function, t::Tuple)`, `base/tuple.jl:532-536`: the short path
reverses the tuple and calls `findfirst` on it. -/
def findlast {α : Type} (f : α → Bool) (t : List α) : Option Nat :=
  if t.length < 32 then
    match findfirst f (revargs t) with
    | none => none
    | some r => some (t.length - r + 1)
  else findlastLoop f t t.length

/-- `filter_rec` (`afoldl`), `base/tuple.jl:546`. -/
def filterRec {α : Type} (f : α → Bool) (t : List α) : List α :=
  t.foldl (fun ys x => if f x then ys ++ [x] else ys) []

/-- `filter(f, t::Tuple)`, `base/tuple.jl:549`: long tuples use `filter` on `collect(t)`. -/
def filter {α : Type} (f : α → Bool) (t : List α) : List α :=
  if t.length < 32 then filterRec f t else t.filter f

/-- Three-valued `|`: `false | missing === missing`. -/
def or3 : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- `_in_tuple`, `base/operators.jl:1463-1471`; `eq` is three-valued `==`. -/
def inTupleRec {α : Type} (eq : α → α → Option Bool) (x : α) : List α → Option Bool → Option Bool
  | [], result => result
  | a :: r, result =>
    let v := eq a x
    if v = some true then some true else inTupleRec eq x r (or3 result v)

/-- `any(f, itr)` with three-valued logic (`base/reduce.jl`), used by
`in(x, itr::Any32)` through `invoke(in, Tuple{Any,Any}, ...)`, `base/operators.jl:1474`. -/
def anyGo {α : Type} (f : α → Option Bool) : List α → Bool → Option Bool
  | [], anymissing => if anymissing then none else some false
  | a :: r, anymissing => match f a with
    | none => anyGo f r true
    | some true => some true
    | some false => anyGo f r anymissing

/-- `in(x, itr::Tuple)`, `base/operators.jl:1459,1474`. -/
def inTuple {α : Type} (eq : α → α → Option Bool) (x : α) (t : List α) : Option Bool :=
  if t.length ≥ 32 then anyGo (fun y => eq y x) t false else inTupleRec eq x t (some false)

/-- `findall(pred::Fix2{typeof(in)}, x::Tuple) = _findin(x, pred.x)`,
`base/array.jl:2967`; `_findin(a, b) = _findin(a, Set(b))` and
`ai in b && push!(ind, i)` (`base/array.jl:2903-2910`). Membership in a `Set`
is `isequal` membership. -/
def findallIn {α : Type} (isequal : α → α → Bool) (t : List α) (b : List α) : List Nat :=
  ((List.range t.length).zip t).filterMap fun (i, a) =>
    if b.any (isequal a) then some (i + 1) else none

/-- `findall(x -> x in b, t)` for a `Vector` `b` with `Bool`-valued `==`:
`in(x, itr) = any(==(x), itr)`, `base/operators.jl:1456`. -/
def findallPred {α : Type} (eq : α → α → Bool) (t : List α) (b : List α) : List Nat :=
  ((List.range t.length).zip t).filterMap fun (i, a) =>
    if b.any (fun y => eq y a) then some (i + 1) else none

/-! ## Integer unit ranges -/

/-- `t[r]` for `r::UnitRange{Int}` with `first(r) = a` and `length(r) = len`
(`last(r) = a + len - 1` lies in `Int`), `base/range.jl:451-466`. -/
def getindexUnitRange {α : Type} (t : List α) (a : Int) (len : Nat) : R (List α) := do
  let generic := (List.range len).mapM fun (k : Nat) => getfield t (a + k)
  if len ≤ 10 then (List.range len).mapM fun (k : Nat) => getfield t (((k : Int) + 1) + a - 1)
  else if a = 1 then
    if a + len - 1 = t.length then pure t
    else if a + len - 1 = t.length - 1 then front t
    else if a + len - 1 = t.length - 2 then do let f ← front t; front f
    else generic
  else if a + len - 1 = t.length then
    if a = 2 then tail t
    else if a = 3 then do let r ← tail t; tail r
    else generic
  else generic

/-- `UnitRange(a, b)` for `Int` endpoints as `(first, length)` (`last` is
`a - 1` when `b < a`); assumes `b - a + 1` does not overflow. -/
def unitRange (a b : JInt .i64) : Int × Nat :=
  (a.val, if b.val ≥ a.val then (b.val - a.val + 1).toNat else 0)

/-- `t[a:b]` for `Int` endpoints. -/
def getindexColon {α : Type} (t : List α) (a b : JInt .i64) : R (List α) :=
  getindexUnitRange t (unitRange a b).1 (unitRange a b).2

/-- `t[b]` for a `UnitRange{Bool}` `b` (first value `lo`, length `len`): it
dispatches to the `AbstractUnitRange` method of `base/range.jl:451-466`, where
`i + first(r) - 1` computes with `first(r)` as an integer. -/
def getindexBoolRange {α : Type} (t : List α) (lo : Bool) (len : Nat) : R (List α) :=
  getindexUnitRange t (if lo then 1 else 0) len

/-- The values of a `UnitRange{Bool}` with first value `lo` and length `len ≤ 2`. -/
def boolRangeValues (lo : Bool) (len : Nat) : List Bool :=
  (List.range len).map fun k => if lo then true else k == 1

/-- Logical indexing `t[b::AbstractArray{Bool,1}]`, `base/tuple.jl:37`:
`length(b) == length(t) ? getindex(t, findall(b)) : BoundsError`. -/
def getindexLogical {α : Type} (t : List α) (b : List Bool) : R (List α) :=
  if b.length = t.length then
    ((List.range b.length).zip b).filterMap (fun (i, x) => if x then some (i + 1) else none)
      |>.mapM fun i => getfield t i
  else bounds

/-! ## split_rest and rest -/

/-- `_split_tuple(t, n, i) = (t[i:n], t[n+1:end])` and
`split_rest(t::Tuple, n, i) = _split_tuple(t, length(t)-n, Int(i))`,
`base/tuple.jl:265-267`. Both slices are `UnitRange{Int}` indexing. -/
def splitRestTuple {α : Type} (t : List α) (n i : JInt .i64) : R (List α × List α) := do
  let m : JInt .i64 := JInt.lit .i64 t.length - n
  let x ← getindexColon t i m
  let y ← getindexColon t (m + JInt.lit .i64 1) (JInt.lit .i64 t.length)
  pure (x, y)

/-- `_check_length_split_rest`, `base/tuple.jl:255-259`. -/
def checkLengthSplitRest (len : Nat) (n : JInt .i64) : R Unit :=
  if (len : Int) < n.val then argErr "The iterator only contains len elements, but at least n were requested."
  else .ok ()

/-- `split_rest(v::Vector, n, i)`: `rest(a, i) = a[i:end]` (`base/tuple.jl:212`),
then `_split_rest(a::Vector, n)` (`base/bitarray.jl:1932-1937`): check the
length, `last_n = a[end-n+1:end]`, `resize!(a, length(a) - n)`. -/
def splitRestVector {α : Type} (v : List α) (n i : JInt .i64) : R (List (Option α) × List α) := do
  let r ← if i.val ≤ v.length then (if 1 ≤ i.val then pure (v.drop (i.val - 1).toNat) else bounds)
    else pure []
  checkLengthSplitRest r.length n
  let lastN := if n.val ≥ 0 then r.drop (r.length - n.val.toNat) else []
  let frontPart := if n.val ≥ 0 then (r.take (r.length - n.val.toNat)).map some
    else r.map some ++ List.replicate n.val.natAbs none
  pure (frontPart, lastN)

/-- `rest(t::Tuple, i)`, `base/tuple.jl:207-211`. -/
def restTuple {α : Type} (t : List α) (i : JInt .i64) : R (List α) :=
  ntupleInt (fun x => x) (JInt.lit .i64 t.length - i + JInt.lit .i64 1).val >>= fun ks =>
    ks.mapM fun (x : Nat) => getfield t (JInt.lit .i64 x + i - JInt.lit .i64 1).val

/-- `indexed_iterate(t::Tuple, i, state) = (getfield(t, i), i+1)`, `base/tuple.jl:161`. -/
def indexedIterate {α : Type} (t : List α) (i : Nat) : R (α × Nat) := do
  let a ← getfield t i
  pure (a, i + 1)

/-- Lowering of `a, b..., c = t`: `indexed_iterate`, then
`split_rest(t, 1, state)`, then `indexed_iterate(last_n, 1)`. -/
def destructureMid {α : Type} (t : List α) : R (α × List α × α) := do
  let (a, s) ← indexedIterate t 1
  let (b, l) ← splitRestTuple t (JInt.lit .i64 1) (JInt.lit .i64 s)
  let (c, _) ← indexedIterate l 1
  pure (a, b, c)

/-! ## prod -/

/-- `prod(x::Tuple{}) = 1` and `prod(x::Tuple{Int, Vararg{Int}}) = *(x...)`,
`base/tuple.jl:688,693`. -/
def prodTuple (t : List (JInt .i64)) : R (JInt .i64) :=
  match t with
  | [] => .ok (JInt.lit .i64 1)
  | a :: r => .ok (r.foldl (· * ·) a)

/-- `prod(f, t) = mapreduce(f, mul_prod, t)` for `Int` elements: an empty
tuple has element type `Union{}` and `reduce_empty(mul_prod, Union{})` throws
(`base/reduce.jl:389-390`). -/
def prodGeneric (t : List (JInt .i64)) : R (JInt .i64) :=
  match t with
  | [] => argErr "reducing over an empty collection is not allowed; consider supplying `init` to the reducer"
  | a :: r => .ok (r.foldl (· * ·) a)

/-! ## Comparison and hashing -/

/-- Element operations: `isequal`, `isless`, three-valued `==` and `<`
(`none` is `missing`), and `hash(x, h)`. -/
structure Ops (α : Type) where
  isequal : α → α → Bool
  isless : α → α → Bool
  eq : α → α → Option Bool
  lt : α → α → Option Bool
  hash : α → Nat → Nat

variable {α : Type}

/-- `_isequal`, `base/tuple.jl:554-557`. -/
def isequalRec (o : Ops α) : List α → List α → Bool
  | [], [] => true
  | a :: r, b :: s => o.isequal a b && isequalRec o r s
  | _, _ => false

/-- `_isequal(t1::Any32, t2::Any32)`, `base/tuple.jl:558-565`. -/
def isequalLoop (o : Ops α) (t s : List α) : Nat → Nat → Bool
  | _, 0 => true
  | i, k + 1 => match t[i]?, s[i]? with
    | some a, some b => if !o.isequal a b then false else isequalLoop o t s (i + 1) k
    | _, _ => true

/-- `isequal(t1::Tuple, t2::Tuple)`, `base/tuple.jl:553`. -/
def isequal (o : Ops α) (t s : List α) : Bool :=
  t.length == s.length &&
    (if t.length ≥ 32 then isequalLoop o t s 0 t.length else isequalRec o t s)

/-- `_eq_missing`, `base/tuple.jl:569,580-587`. -/
def eqMissing (o : Ops α) : List α → List α → Option Bool
  | a :: r, b :: s => if o.eq a b = some false then some false else eqMissing o r s
  | _, _ => none

/-- `_eq`, `base/tuple.jl:568-579`. -/
def eqRec (o : Ops α) : List α → List α → Option Bool
  | a :: r, b :: s => match o.eq a b with
    | some false => some false
    | none => eqMissing o r s
    | some true => eqRec o r s
  | _, _ => some true

/-- `_eq(t1::Any32, t2::Any32)`, `base/tuple.jl:588-599`. -/
def eqLoop (o : Ops α) (t s : List α) : Nat → Nat → Bool → Option Bool
  | _, 0, anymissing => if anymissing then none else some true
  | i, k + 1, anymissing => match t[i]?, s[i]? with
    | some a, some b => match o.eq a b with
      | none => eqLoop o t s (i + 1) k true
      | some false => some false
      | some true => eqLoop o t s (i + 1) k anymissing
    | _, _ => if anymissing then none else some true

/-- `==(t1::Tuple, t2::Tuple)`, `base/tuple.jl:567`. -/
def eq (o : Ops α) (t s : List α) : Option Bool :=
  if t.length = s.length then
    (if t.length ≥ 32 then eqLoop o t s 0 t.length false else eqRec o t s)
  else some false

/-- `<` on tuples, `base/tuple.jl:612-624`. -/
def ltRec (o : Ops α) : List α → List α → Option Bool
  | [], [] => some false
  | [], _ :: _ => some true
  | _ :: _, [] => some false
  | a :: r, b :: s => match o.eq a b with
    | none => none
    | some false => o.lt a b
    | some true => ltRec o r s

/-- `<(t1::Any32, t2::Any32)`, `base/tuple.jl:625-637`. -/
def ltLoop (o : Ops α) (t s : List α) : Nat → Nat → Option Bool
  | _, 0 => some (decide (t.length < s.length))
  | i, k + 1 => match t[i]?, s[i]? with
    | some a, some b => match o.eq a b with
      | none => none
      | some false => o.lt a b
      | some true => ltLoop o t s (i + 1) k
    | _, _ => some (decide (t.length < s.length))

def lt (o : Ops α) (t s : List α) : Option Bool :=
  if t.length ≥ 32 ∧ s.length ≥ 32 then ltLoop o t s 0 (min t.length s.length) else ltRec o t s

/-- `isless` on tuples, `base/tuple.jl:639-651`. -/
def islessRec (o : Ops α) : List α → List α → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: r, b :: s => o.isless a b || (o.isequal a b && islessRec o r s)

/-- `isless(t1::Any32, t2::Any32)`, `base/tuple.jl:652-661`. -/
def islessLoop (o : Ops α) (t s : List α) : Nat → Nat → Bool
  | _, 0 => decide (t.length < s.length)
  | i, k + 1 => match t[i]?, s[i]? with
    | some a, some b => if !o.isequal a b then o.isless a b else islessLoop o t s (i + 1) k
    | _, _ => decide (t.length < s.length)

def isless (o : Ops α) (t s : List α) : Bool :=
  if t.length ≥ 32 ∧ s.length ≥ 32 then islessLoop o t s 0 (min t.length s.length)
  else islessRec o t s

/-- `isless(a::Tuple{BitInteger,BitInteger}, b::Tuple{BitInteger,BitInteger})`,
`base/operators.jl:248-249` (non-short-circuit `|` and `&`). -/
def islessPair (o : Ops α) (a1 a2 b1 b2 : α) : Bool :=
  o.isless a1 b1 || (o.isequal a1 b1 && o.isless a2 b2)

/-- `cmp(x, y) = isless(x, y) ? -1 : ifelse(isless(y, x), 1, 0)`, `base/operators.jl`. -/
def cmp (o : Ops α) (t s : List α) : Int :=
  if isless o t s then -1 else if isless o s t then 1 else 0

def tuplehashSeed : Nat := 0x77cfa1eef01bca90

/-- `hash(t::Tuple, h)`, `base/tuple.jl:602-603`. -/
def hashRec (o : Ops α) : List α → Nat → Nat
  | [], h => h ^^^ tuplehashSeed
  | a :: r, h => o.hash a (hashRec o r h)

/-- `hash(t::Any32, h)`, `base/tuple.jl:604-610`: `for i = length(t):-1:1`. -/
def hashLoop (o : Ops α) (t : List α) : Nat → Nat → Nat
  | 0, out => out
  | k + 1, out => match t[k]? with
    | some a => hashLoop o t k (o.hash a out)
    | none => out

def hash (o : Ops α) (t : List α) (h : Nat) : Nat :=
  if t.length ≥ 32 then hashLoop o t t.length (h ^^^ tuplehashSeed) else hashRec o t h

end JuliaLean.Tuples
