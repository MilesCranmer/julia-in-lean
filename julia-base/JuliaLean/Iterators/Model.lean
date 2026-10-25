import JuliaLean.Core
import JuliaLean.IntArith.Checked

/-!
# Model of `base/iterators.jl` (master `bbfa0ce4150`)

Julia values and iterators are modelled by a deep embedding, so that Julia's
method dispatch on the type of an iterator (`drop(xs::Take, n)`,
`nth(itr::Cycle, n)`, ...) can be mirrored by pattern matching.

* `Ty` is the part of a Julia type the traits look at (`eltype`, `NTuple{N}`).
* `Val` is a Julia value: an `Int64`, a tuple, a `Vector`, a `UnitRange{Int64}`,
  a lazily reversed value, or an unassigned array slot (`undef`).
* `St` is an iteration state.
* `Itr` is an iterator object. Leaves are vectors, tuples, unit ranges
  (`UnitRange` or `Base.IdentityUnitRange`) and `Iterators.Stateful` wrappers of
  vectors; the other constructors are the wrappers of `base/iterators.jl`.

`iter fuel it st` is `iterate(it)` (`st = none`) or `iterate(it, s)`
(`st = some s`). `fuel` bounds the `while` loops of `dropwhile`, `flatten` and
`partition`; running out is the model-only error `Err.fuel`, never a Julia
result. `Err.oob` is an out-of-bounds store under `@inbounds` (memory
corruption in Julia).

Modelling notes:
* `Stateful` is mutable in Julia. Its model iterates over the position in the
  wrapped vector; `isdone(s)` uses the position at construction and
  `isdone(s, st)` the position in `st`, which is the object's position whenever
  every consumption goes through the iterator under study. Where Julia
  restarts or queries an iterator it is already iterating (`Cycle`,
  `ProductIterator`), a `Stateful` continues from its current position
  (`statefulCur`).
* Array iteration states are linear indices; Julia's `Vector` state is the same
  index (base/abstractarray.jl:1250).
* Elements of vectors are `Int64`s unless a property says otherwise; every
  element type has an 8-byte array slot (inline `Int64` or a boxed pointer).
-/

namespace JuliaLean.Iterators

open JuliaLean

/-- The part of a Julia type the iterator traits inspect. `tuple ts` is
`Tuple{ts...}` (an `NTuple{length ts}`), `vector t` is `Vector{t}`, `range` is
`UnitRange{Int64}`, `bottom` is `Union{}`. -/
inductive Ty where
  | int
  | tuple (ts : List Ty)
  | vector (t : Ty)
  | range
  | any
  | bottom
  deriving Repr, Inhabited

mutual
/-- Structural equality of types. -/
def Ty.beq : Ty → Ty → Bool
  | .int, .int => true
  | .tuple as, .tuple bs => Ty.beqList as bs
  | .vector a, .vector b => Ty.beq a b
  | .range, .range => true
  | .any, .any => true
  | .bottom, .bottom => true
  | _, _ => false
def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

/-- Julia values. `rev v` is `Iterators.reverse(v)` of a value; `undef` is an
unassigned slot of a freshly allocated array (`#undef`, or garbage bits for
`Int64`). -/
inductive Val where
  | int (x : Int)
  | tup (vs : List Val)
  | vec (et : Ty) (vs : List Val)
  | rng (lo hi : Int)
  | rev (v : Val)
  | undef
  deriving Repr, Inhabited

/-- Errors: Julia exceptions, plus the model-only `fuel` (loop bound reached)
and `oob` (an `@inbounds` store past the end of an array). -/
inductive Err where
  | jl (e : JlError)
  | eof
  | dimMismatch
  | fuel
  | oob
  deriving Repr, DecidableEq, Inhabited

abbrev M (α : Type) := Except Err α

def jthrow {α : Type} (e : JlError) : M α := .error (.jl e)

def liftJ {α : Type} : Jl α → M α
  | .ok a => .ok a
  | .error e => .error (.jl e)

/-- Iteration states. `cut` is `IterationCutShort()` (base/iterators.jl:1482). -/
inductive St where
  | nothing
  | int (x : Int)
  | nat (n : Nat)
  | val (v : Val)
  | tup (ss : List St)
  | cut
  deriving Repr, Inhabited

/-- Is the state `IterationCutShort()`? -/
def isCutSt : Option St → Bool
  | some .cut => true
  | _ => false

/-- `UnitRange{Int64}` (`firstindex == 1`) or `Base.IdentityUnitRange`. -/
inductive URKind where
  | unit
  | identity
  deriving Repr, DecidableEq, Inhabited

/-- Iterator objects. `urange k fi li d` has indices `fi:li` and value `i + d`
at index `i` (`UnitRange a:b` is `urange .unit 1 (b-a+1) (a-1)`;
`IdentityUnitRange(a:b)` is `urange .identity a b 0`). `stateful et xs pos` is
an `Iterators.Stateful(::Vector{et})` that has already produced `pos` elements.
`revEnum ri` is `Iterators.Reverse{<:Enumerate}` with the reversed inner
iterator `ri = reverse(r.itr.itr)` (base/iterators.jl:225) computed once;
`revEach it` is the generator `(reverse(x) for x in it)` of
`reverse(::Flatten)` (base/iterators.jl:1379). -/
inductive Itr where
  | vec (et : Ty) (xs : List Val)
  | tuple (xs : List Val)
  | urange (k : URKind) (fi li : JInt64) (d : Int)
  | stateful (et : Ty) (xs : List Val) (pos : Nat)
  | take (it : Itr) (n : JInt64)
  | drop (it : Itr) (n : JInt64)
  | takeWhile (p : Val → Bool) (it : Itr)
  | dropWhile (p : Val → Bool) (it : Itr)
  | enumerate (it : Itr)
  | zip (its : List Itr)
  | repeated (x : Val)
  | cycle (it : Itr)
  | flatten (it : Itr)
  | product (its : List Itr)
  | partition (it : Itr) (n : JInt64)
  | rest (it : Itr) (st : St)
  | accumulate (f : Val → Val → Val) (it : Itr) (init : Option Val)
  | count (start step : JInt64)
  | reverse (it : Itr)
  | revEnum (ri : Itr)
  | revEach (it : Itr)

instance : Inhabited Itr := ⟨.tuple []⟩

/-- `Base.IteratorSize` values, base/generator.jl:84-88. -/
inductive Isz where
  | sizeUnknown
  | hasLength
  | hasShape (n : Nat)
  | isInfinite
  deriving Repr, DecidableEq, Inhabited

/-- `Int64` literal. -/
abbrev i64 (x : Int) : JInt64 := JInt.lit .i64 x

/-! ## Types -/

/-- `promote_typejoin` over the field types of a tuple type, as `eltype(Tuple{...})`
computes it; distinct field types join to `Any` (a supertype the traits treat
like any other non-tuple, non-number type). -/
def tyJoin : List Ty → Ty
  | [] => .bottom
  | t :: ts => if ts.all (· == t) then t else .any

/-- `eltype(T)` of a type. -/
def Ty.eltype : Ty → Ty
  | .int => .int
  | .tuple ts => tyJoin ts
  | .vector t => t
  | .range => .int
  | .any => .any
  | .bottom => .bottom

mutual
/-- `typeof(v)`. -/
def Val.ty : Val → Ty
  | .int _ => .int
  | .tup vs => .tuple (Val.tys vs)
  | .vec et _ => .vector et
  | .rng _ _ => .range
  | .rev v => Val.ty v
  | .undef => .any
def Val.tys : List Val → List Ty
  | [] => []
  | v :: vs => Val.ty v :: Val.tys vs
end

/-! ## Leaf iteration of values -/

/-- `iterate(t::Tuple, i=1)` (base/tuple.jl:69-73) and `iterate(A::Vector, i)`
(base/abstractarray.jl:1250): the state is the next index. -/
def idxIter (vs : List Val) : Option St → M (Option (Val × St))
  | none => if 1 ≤ vs.length then pure (some (vs.getD 0 .undef, .int 2)) else pure none
  | some (.int i) =>
    if 1 ≤ i ∧ i ≤ vs.length then pure (some (vs.getD (i - 1).toNat .undef, .int (i + 1)))
    else pure none
  | some _ => jthrow (.methodError "iterate")

/-- `iterate(r::OrdinalRange)` and `iterate(r, i)` for `UnitRange{Int64}`
`lo:hi`, base/range.jl:935-942: the state is the last value produced. -/
def rangeIter (lo hi : Int) : Option St → M (Option (Val × St))
  | none => if lo > hi then pure none else pure (some (.int lo, .int lo))
  | some (.int v) =>
    if v = hi then pure none
    else let nx := (i64 v + i64 1).val; pure (some (.int nx, .int nx))
  | some _ => jthrow (.methodError "iterate")

/-- Reverse iteration of a vector or tuple (base/iterators.jl:136-150,162):
indices from `length` down to 1. -/
def revIdxIter (vs : List Val) : Option St → M (Option (Val × St))
  | none =>
    if vs.length < 1 then pure none
    else pure (some (vs.getD (vs.length - 1) .undef, .int (vs.length - 1)))
  | some (.int i) =>
    if i < 1 then pure none else pure (some (vs.getD (i - 1).toNat .undef, .int (i - 1)))
  | some _ => jthrow (.methodError "iterate")

/-- `iterate` on a value used as an iterator (inner iterators of `flatten`):
numbers iterate once (base/number.jl:329-330), tuples and vectors by index,
ranges by value. `Iterators.reverse` of a range is the reversed range
`hi:-1:lo` (base/iterators.jl:156). -/
def valIter : Val → Option St → M (Option (Val × St))
  | .int x, none => pure (some (.int x, .nothing))
  | .int _, some _ => pure none
  | .tup vs, s => idxIter vs s
  | .vec _ vs, s => idxIter vs s
  | .rng lo hi, s => rangeIter lo hi s
  | .rev (.tup vs), s => revIdxIter vs s
  | .rev (.vec _ vs), s => revIdxIter vs s
  | .rev (.rng lo hi), none => if lo > hi then pure none else pure (some (.int hi, .int hi))
  | .rev (.rng lo _), some (.int v) =>
    if v = lo then pure none
    else let nx := (i64 v - i64 1).val; pure (some (.int nx, .int nx))
  | .rev (.int x), s => valIter (.int x) s
  | _, _ => jthrow (.methodError "iterate")

/-- `Iterators.reverse(x)` of a value: numbers are their own reverse and
`reverse(r::Reverse) = r.itr` (base/iterators.jl:158-159). -/
def Val.reverse : Val → Val
  | .int x => .int x
  | .rev v => v
  | v => .rev v

/-- `length(x)` of a value used as an iterator. -/
def Val.length : Val → M JInt64
  | .int _ => pure (i64 1)
  | .tup vs => pure (i64 vs.length)
  | .vec _ vs => pure (i64 vs.length)
  | .rng lo hi => pure (i64 (hi - lo + 1))
  | .rev v => match v with
    | .tup vs => pure (i64 vs.length)
    | .vec _ vs => pure (i64 vs.length)
    | .rng lo hi => pure (i64 (hi - lo + 1))
    | _ => jthrow (.methodError "length")
  | .undef => jthrow (.methodError "length")

/-- `IteratorSize(typeof(x))` of a value. Numbers are `HasShape{0}`
(base/number.jl). -/
def Val.isz : Val → Isz
  | .int _ => .hasShape 0
  | .tup _ => .hasLength
  | .vec _ _ => .hasShape 1
  | .rng _ _ => .hasShape 1
  | .rev v => match v with
    | .tup _ => .hasLength
    | .vec _ _ => .hasShape 1
    | .rng _ _ => .hasShape 1
    | _ => .hasLength
  | .undef => .hasLength

/-! ## Traits -/

/-- `and_iteratorsize`, base/iterators.jl:71-76. -/
def andIsz : Isz → Isz → Isz
  | a, b => if a = b then a else
    match a, b with
    | .hasLength, .hasShape _ => .hasLength
    | .hasShape _, .hasLength => .hasLength
    | .hasShape _, .hasShape _ => .hasLength
    | _, _ => .sizeUnknown

/-- `zip_iteratorsize(a, b)`, base/iterators.jl:508-512. -/
def zipIsz2 : Isz → Isz → Isz
  | .isInfinite, .isInfinite => .isInfinite
  | .hasLength, .isInfinite => .hasLength
  | .hasShape _, .isInfinite => .hasLength
  | .isInfinite, .hasLength => .hasLength
  | .isInfinite, .hasShape _ => .hasLength
  | .isInfinite, b => andIsz b .isInfinite
  | a, b => andIsz a b

/-- `zip_iteratorsize(...)`, base/iterators.jl:506-513. -/
def zipIsz : List Isz → Isz
  | [] => .isInfinite
  | [a] => a
  | a :: b :: rest => zipIsz2 a (zipIsz (b :: rest))

/-- `prod_iteratorsize(a, b)`, base/iterators.jl:1157-1166. -/
def prodIsz2 : Isz → Isz → Isz
  | .hasLength, .hasLength => .hasShape 2
  | .hasLength, .hasShape n => .hasShape (n + 1)
  | .hasShape n, .hasLength => .hasShape (n + 1)
  | .hasShape m, .hasShape n => .hasShape (m + n)
  | .isInfinite, _ => .isInfinite
  | _, .isInfinite => .isInfinite
  | _, _ => .sizeUnknown

/-- `prod_iteratorsize(...)`, base/iterators.jl:1154-1167. -/
def prodIszList : List Isz → Isz
  | [] => .hasShape 0
  | [a] => a
  | a :: b :: rest => prodIsz2 a (prodIszList (b :: rest))

/-- `flatten_iteratorsize(sz, T)`, base/iterators.jl:1310-1316. -/
def flattenIsz (sz : Isz) (t : Ty) : Isz :=
  match sz with
  | .hasLength | .hasShape _ =>
    match t with
    | .bottom | .tuple _ | .int => .hasLength
    | _ => .sizeUnknown
  | _ => .sizeUnknown

/-- Is `it` the empty tuple (`Flatten{Tuple{}}`, base/iterators.jl:1306,1320,1333)? -/
def isEmptyTuple : Itr → Bool
  | .tuple [] => true
  | _ => false

mutual
/-- `Base.IteratorSize(typeof(it))`. -/
def isz : Itr → Isz
  | .vec _ _ => .hasShape 1
  | .tuple _ => .hasLength
  | .urange _ _ _ _ => .hasShape 1
  -- base/iterators.jl:1625
  | .stateful _ _ _ => .sizeUnknown
  -- base/iterators.jl:820-822
  | .take it _ => if isz it = .sizeUnknown then .sizeUnknown else .hasLength
  -- base/iterators.jl:877-880
  | .drop it _ => match isz it with
    | .sizeUnknown => .sizeUnknown
    | .isInfinite => .isInfinite
    | _ => .hasLength
  -- base/iterators.jl:937,988
  | .takeWhile _ _ => .sizeUnknown
  | .dropWhile _ _ => .sizeUnknown
  -- base/iterators.jl:221
  | .enumerate it => isz it
  -- base/iterators.jl:503
  | .zip its => zipIsz (iszList its)
  -- base/iterators.jl:1117,1063
  | .repeated _ => .isInfinite
  | .cycle _ => .isInfinite
  -- base/iterators.jl:1318-1322
  | .flatten it =>
    if !(ieltype it) then .sizeUnknown
    else if isEmptyTuple it then .hasLength
    else flattenIsz (isz it) (eltype it)
  -- base/iterators.jl:1150-1152
  | .product its => prodIszList (iszList its ++ [.hasShape 0])
  -- base/iterators.jl:1459-1463
  | .partition c _ => match isz c with
    | .hasShape _ => .hasLength
    | s => s
  -- base/iterators.jl:737-739
  | .rest it _ => if isz it = .isInfinite then .isInfinite else .sizeUnknown
  -- base/iterators.jl:664
  | .accumulate _ it _ => isz it
  -- base/iterators.jl:774
  | .count _ _ => .isInfinite
  -- base/iterators.jl:131
  | .reverse it => isz it
  | .revEnum ri => isz ri
  -- base/generator.jl:139 (Generator{I}: IteratorSize(I))
  | .revEach it => isz it
def iszList : List Itr → List Isz
  | [] => []
  | it :: its => isz it :: iszList its

/-- `Base.IteratorEltype(typeof(it)) isa HasEltype`. -/
def ieltype : Itr → Bool
  | .vec _ _ | .tuple _ | .urange _ _ _ _ | .stateful _ _ _ => true
  | .take it _ | .drop it _ | .takeWhile _ it | .dropWhile _ it => ieltype it
  | .enumerate it => ieltype it
  -- base/iterators.jl:504,515-517
  | .zip its => ieltypeAll its
  | .repeated _ => true
  | .cycle it => ieltype it
  -- base/iterators.jl:1305-1308: IteratorEltype(eltype(I)); IteratorEltype(Any) is unknown
  | .flatten it => isEmptyTuple it || (ieltype it && eltype it != .any)
  -- base/iterators.jl:1188-1195
  | .product [] => true
  | .product [i] => ieltype i
  | .product its => ieltypeAll its
  -- base/iterators.jl:1455-1457, base/multidimensional.jl:657
  | .partition (.vec _ _) _ => true
  | .partition (.urange .unit _ _ _) _ => true
  | .partition (.urange .identity _ _ _) _ => false
  | .partition c _ => ieltype c
  | .rest it _ => ieltype it
  -- base/iterators.jl:665
  | .accumulate _ _ _ => false
  | .count _ _ => true
  | .reverse it => ieltype it
  | .revEnum ri => ieltype ri
  -- base/generator.jl:173
  | .revEach _ => false
def ieltypeAll : List Itr → Bool
  | [] => true
  | it :: its => ieltype it && ieltypeAll its

/-- `eltype(typeof(it))`. -/
def eltype : Itr → Ty
  | .vec et _ => et
  | .tuple xs => tyJoin (Val.tys xs)
  | .urange _ _ _ _ => .int
  | .stateful et _ _ => et
  | .take it _ | .drop it _ | .takeWhile _ it | .dropWhile _ it => eltype it
  | .enumerate it => .tuple [.int, eltype it]
  | .zip its => .tuple (eltypeList its)
  | .repeated x => x.ty
  | .cycle it => eltype it
  | .flatten it => (eltype it).eltype
  | .product its => .tuple (eltypeList its)
  | .partition c _ => .vector (eltype c)
  | .rest it _ => eltype it
  | .accumulate _ _ _ => .any
  | .count _ _ => .int
  | .reverse it => eltype it
  | .revEnum ri => .tuple [.int, eltype ri]
  | .revEach _ => .any
def eltypeList : List Itr → List Ty
  | [] => []
  | it :: its => eltype it :: eltypeList its
end

/-! ## `isdone` -/

/-- Julia's three-valued `|` on `Union{Bool, Missing}`. -/
def or3 : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- `isdone(x)` on an object whose last state is `s`: a `Stateful` answers from
its current (mutated) position, which is the position in `s`; any other
iterator answers from its start. Used where Julia calls `isdone(x)` on an
iterator it is already iterating (base/iterators.jl:1209,1239). -/
def statefulCur : Itr → St → Option St
  | .stateful _ _ _, s => some s
  | _, _ => none

/-- The state component of a `ProductIterator` state entry `Pair(value, state)`. -/
def pairState : St → St
  | .tup [_, s] => s
  | s => s

mutual
/-- `isdone(it)` (no state). The default `isdone(_, _...) = missing` is `none`
(base/essentials.jl:1591). -/
def isdone0 : Itr → M (Option Bool)
  -- base/iterators.jl:1607
  | .stateful _ xs pos => pure (some (decide (xs.length ≤ pos)))
  -- base/iterators.jl:824
  | .take xs _ => isdone0 xs
  -- base/iterators.jl:430
  | .zip its => zipAnyIsdone0 its
  -- base/iterators.jl:1066
  | .cycle xs => isdone0 xs
  -- base/iterators.jl:1204
  | .product its => anyIsdone0 its
  -- base/iterators.jl:733: isdone(i::Rest) = isdone(i.itr)
  | .rest it _ => isdone0 it
  -- base/generator.jl:59
  | .revEach it => isdone0 it
  | _ => pure none
/-- `_zip_any_isdone(is, ())`, base/iterators.jl:433-438. -/
def zipAnyIsdone0 : List Itr → M (Option Bool)
  | [] => pure (some false)
  | it :: its => do
    let d1 ← isdone0 it
    if d1 = some true then pure (some true) else pure (or3 d1 (← zipAnyIsdone0 its))
/-- `any(isdone, P.iterators)`, base/anyall.jl:115-133. -/
def anyIsdone0 : List Itr → M (Option Bool)
  | [] => pure (some false)
  | it :: its => do
    match ← isdone0 it with
    | some true => pure (some true)
    | none => do
      let r ← anyIsdone0 its
      pure (if r = some true then some true else none)
    | some false => anyIsdone0 its
end

mutual
/-- `isdone(it, s)`. -/
def isdoneS : Itr → St → M (Option Bool)
  | .stateful _ xs _, .nat p => pure (some (decide (xs.length ≤ p)))
  | .stateful _ xs pos, _ => pure (some (decide (xs.length ≤ pos)))
  -- base/iterators.jl:825
  | .take xs _, .tup (.int n :: rest) => do
    let inner ← match rest with
      | [] => isdone0 xs
      | s :: _ => isdoneS xs s
    pure (or3 (some (decide (n ≤ 0))) inner)
  -- base/iterators.jl:892
  | .drop xs _, s => isdoneS xs s
  -- base/iterators.jl:431
  | .zip its, .tup ss => zipAnyIsdoneS its ss
  -- base/iterators.jl:1067
  | .cycle _, _ => pure (some false)
  -- base/iterators.jl:1213
  | .product [], _ => pure (some true)
  -- base/iterators.jl:1214
  | .product its, .tup sts => pisdone its sts
  -- base/iterators.jl:733
  | .rest it _, s => isdoneS it s
  | .revEach it, s => isdoneS it s
  | _, _ => pure none
/-- `_zip_any_isdone(is, map(tuple, ss))`, base/iterators.jl:433-438. -/
def zipAnyIsdoneS : List Itr → List St → M (Option Bool)
  | it :: its, s :: ss => do
    let d1 ← isdoneS it s
    if d1 = some true then pure (some true) else pure (or3 d1 (← zipAnyIsdoneS its ss))
  | _, _ => pure (some false)
/-- `_pisdone(iters, states)`, base/iterators.jl:1205-1212. There is no method
for empty tuples: when every factor is done, `first(())` throws
`ArgumentError("tuple must be non-empty")`. -/
def pisdone : List Itr → List St → M (Option Bool)
  | it :: its, s :: ss => do
    let d1 ← isdoneS it (pairState s)
    if d1 ≠ some true then pure d1 else
    let d2 ← match statefulCur it (pairState s) with
      | some c => isdoneS it c
      | none => isdone0 it
    if d2 ≠ some true then pure d2 else pisdone its ss
  | _, _ => jthrow (.argumentError "tuple must be non-empty")
end

/-! ## `length` and `size` -/

/-- `min(x, y)` (base/promotion.jl: `ifelse(y < x, y, x)`). -/
def jmin (x y : JInt64) : JInt64 := if y < x then y else x

/-- `checked_mul` on `Int64`, base/checked.jl:290-295. -/
def checkedMul64 (x y : JInt64) : M JInt64 := liftJ (JuliaLean.IntArith.Checked.checkedMul x y)

/-- `reduce(checked_mul, dims; init=1)`: a left fold. -/
def foldCheckedMul : JInt64 → List JInt64 → M JInt64
  | acc, [] => pure acc
  | acc, d :: ds => do foldCheckedMul (← checkedMul64 acc d) ds

/-- `_promote_tuple_shape(a, b)` for sizes, base/iterators.jl:415-416: two
one-dimensional sizes give the minimum; other sizes must agree
(`promote_shape`, base/indices.jl). -/
def promoteShape (a b : List JInt64) : M (List JInt64) :=
  match a, b with
  | [m], [n] => pure [jmin m n]
  | _, _ => if a = b then pure a else .error .dimMismatch

/-- `_promote_tuple_shape(a, b...) = _promote_tuple_shape(a, _promote_tuple_shape(b...))`,
base/iterators.jl:417-418. -/
def promoteAll : List (List JInt64) → M (List JInt64)
  | [] => pure []
  | [a] => pure a
  | a :: b :: rest => do promoteShape a (← promoteAll (b :: rest))

mutual
/-- `length(it)`. Iterators without a `length` method throw `MethodError`. -/
def len : Itr → M JInt64
  | .vec _ xs => pure (i64 xs.length)
  | .tuple xs => pure (i64 xs.length)
  -- base/range.jl:794-804
  | .urange _ fi li _ => pure (li - fi + i64 1)
  -- base/iterators.jl:823 and 58-61; length(1:n) == n for n >= 0
  | .take xs n => if isz xs = .isInfinite then pure n else do pure (jmin (← len xs) n)
  -- base/iterators.jl:881 and 63-69
  | .drop xs n => do
    if isz xs = .isInfinite then len xs else
    let m ← len xs
    pure (if n < m then m - n else i64 0)
  -- base/iterators.jl:209
  | .enumerate it => len it
  -- base/iterators.jl:380-394
  | .zip its => do
    match ← zipMinLength its with
    | none => jthrow (.argumentError "iterator is of undefined length")
    | some n => pure n
  -- base/iterators.jl:1324-1333
  | .flatten (.tuple []) => pure (i64 0)
  | .flatten it => match eltype it with
    | .bottom => pure (i64 0)
    | .tuple ts => do checkedMul64 (i64 ts.length) (← len it)
    | .int => len it
    | _ => jthrow (.argumentError "Iterates of the argument to Flatten are not known to have constant length")
  -- base/iterators.jl:1186
  | .product its => do foldCheckedMul (i64 1) (← prodSize its)
  -- base/iterators.jl:1465-1468
  | .partition c n => do liftJ (JInt.cld (← len c) n)
  -- base/iterators.jl:661
  | .accumulate _ it _ => len it
  -- base/iterators.jl:129
  | .reverse it => len it
  | .revEnum ri => len ri
  | .revEach it => len it
  | _ => jthrow (.methodError "length")
/-- `_zip_min_length(is)`, base/iterators.jl:385-394. -/
def zipMinLength : List Itr → M (Option JInt64)
  | [] => pure none
  | it :: its => do
    let n ← zipMinLength its
    if isz it = .isInfinite then pure n else
    let l ← len it
    match n with
    | none => pure (some l)
    | some m => pure (some (jmin m l))
/-- `size(it)`. -/
def size : Itr → M (List JInt64)
  | .vec _ xs => pure [i64 xs.length]
  | .urange _ fi li _ => pure [li - fi + i64 1]
  | .enumerate it => size it
  -- base/iterators.jl:412
  | .zip its => do promoteAll (← sizeList its)
  -- base/iterators.jl:1169-1175
  | .product its => prodSize its
  | .accumulate _ it _ => size it
  | .reverse it => size it
  | .revEnum ri => size ri
  | .revEach it => size it
  | _ => jthrow (.methodError "size")
def sizeList : List Itr → M (List (List JInt64))
  | [] => pure []
  | it :: its => do pure ((← size it) :: (← sizeList its))
/-- `_prod_size(t)`, base/iterators.jl:1170-1175. -/
def prodSize : List Itr → M (List JInt64)
  | [] => pure []
  | it :: its => do
    let here ← match isz it with
      | .hasShape _ => size it
      | .hasLength => do pure [← len it]
      | _ => jthrow (.argumentError "Cannot compute size for object of type")
    pure (here ++ (← prodSize its))
end

/-! ## Allocation -/

/-- `MAXINTVAL` of src/julia_internal.h (`typemax(Int)`). -/
def maxIntVal : Int := 2 ^ 63 - 1

/-- `Vector{T}(undef, n)` with 8-byte slots: src/genericmemory.c:55-66 throws
`ArgumentError("invalid GenericMemory size ...")` when `n` (as `size_t`) or the
byte count `8n` reaches `MAXINTVAL - 1`, or the multiplication overflows. -/
def allocCheck (n : Int) : M Unit :=
  if n = 0 then pure ()
  else
    let nel : Int := n % 2 ^ 64
    if nel ≥ maxIntVal - 1 ∨ nel * 8 ≥ maxIntVal - 1 then
      jthrow (.argumentError "invalid GenericMemory size")
    else pure ()

/-! ## Iteration -/

/-- The `for _ in 1:n` loop of `iterate(::Drop)`, base/iterators.jl:883-890. -/
def dropLoop (step : St → M (Option (Val × St))) : Nat → Option (Val × St) → M (Option (Val × St))
  | 0, y => pure y
  | _ + 1, none => pure none
  | k + 1, some (_, s) => do dropLoop step k (← step s)

/-- The `while` loop of `iterate(::DropWhile)`, base/iterators.jl:979-986. -/
def whileLoop (step : St → M (Option (Val × St))) (p : Val → Bool) :
    Nat → Option (Val × St) → M (Option (Val × St))
  | _, none => pure none
  | 0, some _ => .error .fuel
  | k + 1, some (x, s) => if p x then do whileLoop step p k (← step s) else pure (some (x, s))

/-- The outer-advancing `while` loops of `iterate(::Flatten)`,
base/iterators.jl:1342-1351 and 1365-1376: `r` is the result of iterating the
current inner value `inner`; `so` is the next outer state. -/
def flatLoop (step : St → M (Option (Val × St))) :
    Nat → Val → St → Option (Val × St) → M (Option (Val × St))
  | _, inner, so, some (item, si) => pure (some (item, .tup [so, .val inner, si]))
  | 0, _, _, none => .error .fuel
  | k + 1, _, so, none => do
    match ← step so with
    | none => pure none
    | some (inner', so') => flatLoop step k inner' so' (← valIter inner' none)

/-- The fill loop of the generic `iterate(::PartitionIterator)`,
base/iterators.jl:1490-1499: `acc` holds the `i` elements stored so far. -/
def partLoop (step : St → M (Option (Val × St))) (n : Int) :
    Nat → List Val → Option (Val × St) → M (List Val × Option (Val × St))
  | _, acc, none => pure (acc, none)
  | 0, _, some _ => .error .fuel
  | k + 1, acc, some (x, s) =>
    let acc' := acc ++ [x]
    if n ≤ acc'.length then pure (acc', some (x, s))
    else do partLoop step n k acc' (← step s)

/-- `UnitRange(start, stop)` normalisation, base/range.jl:428,439-441. -/
def unitRangeLast (start stop : JInt64) : JInt64 :=
  if start ≤ stop then stop else start - i64 1

/-- `c[s:r]` for `c = urange k fi li d` without bounds checks: an
`IdentityUnitRange` returns the index range itself (base/indices.jl:380-384);
a `UnitRange` shifts it, base/range.jl:1002-1015. -/
def urangeSlice (k : URKind) (fi : JInt64) (d : Int) (s r : JInt64) : Val :=
  let stop := unitRangeLast s r
  match k with
  | .identity => .rng s.val stop.val
  | .unit =>
    let f := fi + i64 d
    let start := f + s - fi
    let len := stop - s + i64 1
    let stop' := start + (len - i64 1)
    .rng start.val (unitRangeLast start stop').val

/-- Decode a `Take`/`Enumerate` state `(n, rest...)`. -/
def splitCountState : Option St → JInt64 → M (JInt64 × Option St)
  | none, n => pure (n, none)
  | some (.tup [.int m]), _ => pure (i64 m, none)
  | some (.tup [.int m, s]), _ => pure (i64 m, some s)
  | some _, _ => jthrow (.methodError "iterate")

mutual
/-- `iterate(it)` (`st = none`) and `iterate(it, s)` (`st = some s`). -/
def iter (fuel : Nat) : Itr → Option St → M (Option (Val × St))
  | .vec _ xs, st => idxIter xs st
  | .tuple xs, st => idxIter xs st
  -- base/range.jl:935-942 on the values i + d
  | .urange _ fi li d, st => rangeIter (fi.val + d) (li.val + d) st
  -- base/iterators.jl:1624, 1609-1618
  | .stateful _ xs pos, st =>
    let p := match st with
      | some (.nat q) => q
      | _ => pos
    if xs.length ≤ p then pure none else pure (some (xs.getD p .undef, .nat (p + 1)))
  -- base/iterators.jl:827-833
  | .take xs n, st => do
    let (m, rest) ← splitCountState st n
    if m ≤ i64 0 then pure none else
    match ← iter fuel xs rest with
    | none => pure none
    | some (y, s) => pure (some (y, .tup [.int (m - i64 1).val, s]))
  -- base/iterators.jl:883-891
  | .drop xs n, none => do
    let y ← iter fuel xs none
    dropLoop (fun s => iter fuel xs (some s)) n.val.toNat y
  | .drop xs _, some s => iter fuel xs (some s)
  -- base/iterators.jl:930-935
  | .takeWhile p xs, st => do
    match ← iter fuel xs st with
    | none => pure none
    | some (y, s) => if p y then pure (some (y, s)) else pure none
  -- base/iterators.jl:978-986
  | .dropWhile p xs, none => do
    whileLoop (fun s => iter fuel xs (some s)) p fuel (← iter fuel xs none)
  | .dropWhile _ xs, some s => iter fuel xs (some s)
  -- base/iterators.jl:211-216
  | .enumerate it, st => do
    let (i, rest) ← splitCountState st (i64 1)
    match ← iter fuel it rest with
    | none => pure none
    | some (x, s) => pure (some (.tup [.int i.val, x], .tup [.int (i + i64 1).val, s]))
  -- base/iterators.jl:440-460
  | .zip its, st => do
    let ss : List (Option St) := match st with
      | some (.tup ss) => ss.map some
      | _ => its.map (fun _ => none)
    let ds ← zipIsdones its ss
    if ds.any (· = some true) then pure none else
    let xs ← if ds.all (· = none) then zipInOrder fuel its ss
      else do
        match ← zipUnknown fuel its ss ds with
        | none => pure none
        | some xs1 => zipRest fuel its ss xs1
    match xs with
    | none => pure none
    | some xs => pure (some (.tup (xs.map (·.1)), .tup (xs.map (·.2))))
  -- base/iterators.jl:1115
  | .repeated x, _ => pure (some (x, .nothing))
  -- base/iterators.jl:1065-1072
  | .cycle xs, none => iter fuel xs none
  | .cycle xs, some s => do
    match ← iter fuel xs (some s) with
    | none => iter fuel xs (statefulCur xs s)
    | some y => pure (some y)
  -- base/iterators.jl:1335-1352
  | .flatten it, none => do
    match ← iter fuel it none with
    | none => pure none
    | some (inner, so) => flatLoop (fun s => iter fuel it (some s)) fuel inner so (← valIter inner none)
  -- base/iterators.jl:1354-1377
  | .flatten it, some (.tup [so, .val inner, si]) => do
    match ← valIter inner (some si) with
    | some (item, si') => pure (some (item, .tup [so, .val inner, si']))
    | none => flatLoop (fun s => iter fuel it (some s)) fuel inner so none
  | .flatten _, some _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:1201-1202
  | .product [], none => pure (some (.tup [], .nat 1))
  | .product [], some _ => pure none
  -- base/iterators.jl:1226-1231
  | .product its, none => do
    if (← anyIsdone0 its) = some true then pure none else
    match ← pIterate fuel its with
    | none => pure none
    | some nx => pure (some (.tup (nx.map (·.1)), .tup (nx.map (fun p => .tup [.val p.1, p.2]))))
  -- base/iterators.jl:1248-1253
  | .product its, some (.tup sts) => do
    if (← pisdone its sts) = some true then pure none else
    match ← pIterate1 fuel its sts with
    | none => pure none
    | some nx => pure (some (.tup (nx.map (·.1)), .tup (nx.map (fun p => .tup [.val p.1, p.2]))))
  | .product _, some _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:1470-1474
  | .partition (.urange k fi li d) n, st => do
    let s : JInt64 := match st with
      | some (.int x) => i64 x
      | _ => fi
    if li < s then pure none else
    let r := jmin (s + n - i64 1) li
    pure (some (urangeSlice k fi d s r, .int (r + i64 1).val))
  -- base/iterators.jl:1476-1480
  | .partition (.vec et xs) n, st => do
    let s : JInt64 := match st with
      | some (.int x) => i64 x
      | _ => i64 1
    if i64 xs.length < s then pure none else
    let r := jmin (s + n - i64 1) (i64 xs.length)
    if s.val < 1 then .error .oob else
    pure (some (.vec et ((xs.drop (s.val - 1).toNat).take (r.val - s.val + 1).toNat), .int (r + i64 1).val))
  -- base/iterators.jl:1484-1502
  | .partition c n, st => do
    if isCutSt st then pure none else
    allocCheck n.val
    let (acc, y) ← partLoop (fun s => iter fuel c (some s)) n.val fuel [] (← iter fuel c st)
    if acc.isEmpty then pure none else
    pure (some (.vec (eltype c) acc, match y with
      | none => .cut
      | some (_, s) => s))
  -- base/iterators.jl:732
  | .rest it s0, none => iter fuel it (some s0)
  | .rest it _, some s => iter fuel it (some s)
  -- base/iterators.jl:643-659
  | .accumulate f it init, none => do
    match ← iter fuel it none with
    | none => pure none
    | some (x, s) =>
      let v := match init with
        | none => x
        | some i => f i x
      pure (some (v, .tup [.val v, s]))
  | .accumulate f it _, some (.tup [.val v, s]) => do
    match ← iter fuel it (some s) with
    | none => pure none
    | some (x, s') => let v' := f v x; pure (some (v', .tup [.val v', s']))
  | .accumulate _ _ _, some _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:772
  | .count start _, none => pure (some (.int start.val, .int start.val))
  | .count _ step, some (.int v) =>
    pure (some (.int (i64 v + step).val, .int (i64 v + step).val))
  | .count _ _, some _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:136-150 (vectors), 162 (tuples), 156 (ranges, reversed by Base.reverse)
  | .reverse (.vec _ xs), st => revIdxIter xs st
  | .reverse (.tuple xs), st => revIdxIter xs st
  | .reverse (.urange _ fi li d), st => valIter (.rev (.rng (fi.val + d) (li.val + d))) st
  | .reverse _, _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:224-232
  | .revEnum ri, st => do
    let (i, rest) ← match st with
      | none => do pure (← len ri, none)
      | some s => splitCountState (some s) (i64 0)
    match ← iter fuel ri rest with
    | none => pure none
    | some (x, s) => pure (some (.tup [.int i.val, x], .tup [.int (i - i64 1).val, s]))
  -- base/generator.jl:52-58
  | .revEach it, st => do
    match ← iter fuel it st with
    | none => pure none
    | some (x, s) => pure (some (x.reverse, s))
/-- `_zip_isdone(is, ss)`, base/iterators.jl:496-501 (only the `ds` list). -/
def zipIsdones : List Itr → List (Option St) → M (List (Option Bool))
  | it :: its, s :: ss => do
    let d ← match s with
      | none => isdone0 it
      | some s => isdoneS it s
    pure (d :: (← zipIsdones its ss))
  | _, _ => pure []
/-- `_zip_iterate_in_order`, base/iterators.jl:465-472. -/
def zipInOrder (fuel : Nat) : List Itr → List (Option St) → M (Option (List (Val × St)))
  | it :: its, s :: ss => do
    match ← iter fuel it s with
    | none => pure none
    | some x => do
      match ← zipInOrder fuel its ss with
      | none => pure none
      | some y => pure (some (x :: y))
  | _, _ => pure (some [])
/-- `_zip_iterate_unknown`, base/iterators.jl:478-485: `none` entries are `_ZipSkip()`. -/
def zipUnknown (fuel : Nat) : List Itr → List (Option St) → List (Option Bool) →
    M (Option (List (Option (Val × St))))
  | it :: its, s :: ss, d :: ds => do
    let x ← if d = none then do
        match ← iter fuel it s with
        | none => pure none
        | some x => pure (some (some x))
      else pure (some none)
    match x with
    | none => pure none
    | some x => do
      match ← zipUnknown fuel its ss ds with
      | none => pure none
      | some y => pure (some (x :: y))
  | _, _, _ => pure (some [])
/-- `_zip_iterate_rest`, base/iterators.jl:487-494. -/
def zipRest (fuel : Nat) : List Itr → List (Option St) → List (Option (Val × St)) →
    M (Option (List (Val × St)))
  | it :: its, s :: ss, x :: xs => do
    let x ← match x with
      | some x => pure (some x)
      | none => iter fuel it s
    match x with
    | none => pure none
    | some x => do
      match ← zipRest fuel its ss xs with
      | none => pure none
      | some y => pure (some (x :: y))
  | _, _, _ => pure (some [])
/-- `_piterate(iters...)`, base/iterators.jl:1216-1225. -/
def pIterate (fuel : Nat) : List Itr → M (Option (List (Val × St)))
  | [] => pure (some [])
  | it :: its => do
    match ← iter fuel it none with
    | none => pure none
    | some nx => do
      match ← pIterate fuel its with
      | none => pure none
      | some rest => pure (some (nx :: rest))
/-- `_piterate1(iters, states)`, base/iterators.jl:1233-1247. States are
`Pair(value, state)` entries. -/
def pIterate1 (fuel : Nat) : List Itr → List St → M (Option (List (Val × St)))
  | it :: its, st1 :: sts => do
    let old : List (Val × St) := sts.map fun
      | .tup [.val v, s] => (v, s)
      | s => (.undef, s)
    match ← iter fuel it (some (pairState st1)) with
    | some nx => pure (some (nx :: old))
    | none => do
      let d ← match statefulCur it (pairState st1) with
        | some c => isdoneS it c
        | none => isdone0 it
      if d = some true then pure none else
      match ← pIterate1 fuel its sts with
      | none => pure none
      | some restnext => do
        match ← iter fuel it (statefulCur it (pairState st1)) with
        | none => pure none
        | some nx => pure (some (nx :: restnext))
  | _, _ => pure none
end

/-! ## Running an iterator -/

/-- Iterate until `nothing`, at most `fuel` steps: the elements in order. -/
def runFrom (step : St → M (Option (Val × St))) : Nat → Option (Val × St) → M (List Val)
  | _, none => pure []
  | 0, some _ => .error .fuel
  | k + 1, some (x, s) => do pure (x :: (← runFrom step k (← step s)))

/-- All elements `itr` yields (`for x in itr`), with `fuel` bounding both the
number of elements and the inner loops. -/
def elems (fuel : Nat) (it : Itr) : M (List Val) := do
  runFrom (fun s => iter fuel it (some s)) fuel (← iter fuel it none)

/-- `copyto!(dest, src)` into `n` fresh slots, base/abstractarray.jl:941-951:
`ArgumentError` when `src` has more than `n` elements; unwritten slots stay
`undef`. -/
def copyFrom (step : St → M (Option (Val × St))) : Nat → Nat → Option (Val × St) → M (List Val)
  | _, n, none => pure (List.replicate n .undef)
  | 0, _, some _ => .error .fuel
  | _ + 1, 0, some _ => jthrow (.argumentError "destination has fewer elements than required")
  | k + 1, n + 1, some (x, s) => do pure (x :: (← copyFrom step k n (← step s)))

/-- `collect_to!(dest, itr, i, st)` with `@inbounds` stores, base/array.jl:896-911:
a store past the `n` remaining slots is `Err.oob`. -/
def collectTo (step : St → M (Option (Val × St))) : Nat → Nat → Option (Val × St) → M (List Val)
  | _, n, none => pure (List.replicate n .undef)
  | 0, _, some _ => .error .fuel
  | _ + 1, 0, some _ => .error .oob
  | k + 1, n + 1, some (x, s) => do pure (x :: (← collectTo step k n (← step s)))

/-- `collect(itr)`, base/array.jl:759-860 (`_collect` methods). -/
def collect (fuel : Nat) (it : Itr) : M (List Val) := do
  let step := fun s => iter fuel it (some s)
  let n ← match isz it with
    | .isInfinite => jthrow (.methodError "_collect")
    | .sizeUnknown => pure none
    | .hasLength => do pure (some (← len it).val)
    | .hasShape _ => do pure (some ((← size it).foldl (fun a d => a * d.val) 1))
  match n with
  | none => elems fuel it
  | some n =>
    if ieltype it then do
      allocCheck n
      copyFrom step fuel n.toNat (← iter fuel it none)
    else do
      match ← iter fuel it none with
      | none => do allocCheck n; pure (List.replicate n.toNat .undef)
      | some (v1, s) => do
        allocCheck n
        if n ≤ 0 then jthrow .boundsError else
        pure (v1 :: (← collectTo step fuel (n.toNat - 1) (← step s)))

end JuliaLean.Iterators
