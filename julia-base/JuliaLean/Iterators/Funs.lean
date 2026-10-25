import JuliaLean.Iterators.Model

/-!
# Julia-level functions of `base/iterators.jl`

Constructors with their dispatch on the argument's type (`take(xs::Take, n)`,
`drop(xs::Drop, n)`, `Iterators.reverse(::Zip)`, ...), `nth`, `first(itr, n)`,
`last(itr, n)`, `only`, `isempty`, `peel`/`rest` and the `Stateful` operations.
Counts of any integer type are `JInt t`.
-/

namespace JuliaLean.Iterators

open JuliaLean

/-- `Int(n)` for an integer of type `t`: `InexactError` when out of range. -/
def toInt {t : IntTy} (n : JInt t) : M JInt64 := liftJ (JInt.convert .i64 n.val)

/-- The `Take` inner constructor, base/iterators.jl:781-784. -/
def mkTake (xs : Itr) (n : JInt64) : M Itr :=
  if n < i64 0 then jthrow (.argumentError "Take length must be non-negative") else pure (.take xs n)

/-- The `Drop` inner constructor, base/iterators.jl:840-843. -/
def mkDrop (xs : Itr) (n : JInt64) : M Itr :=
  if n < i64 0 then jthrow (.argumentError "Drop length must be non-negative") else pure (.drop xs n)

/-- `take(xs, n)`, base/iterators.jl:815-816. -/
def take {t : IntTy} (xs : Itr) (n : JInt t) : M Itr := do
  match xs with
  | .take ys m => mkTake ys (jmin (← toInt n) m)
  | _ => mkTake xs (← toInt n)

/-- `drop(xs, n)`, base/iterators.jl:871-873. -/
def drop {t : IntTy} (xs : Itr) (n : JInt t) : M Itr := do
  match xs with
  | .take ys m => do
    let n' ← toInt n
    let d ← match ys with
      | .drop zs k => mkDrop zs (n' + k)
      | _ => mkDrop ys n'
    let r := m - n'
    mkTake d (if i64 0 < r then r else i64 0)
  | .drop ys m => mkDrop ys ((← toInt n) + m)
  | _ => mkDrop xs (← toInt n)

/-- `repeated(x, n) = take(repeated(x), Int(n))`, base/iterators.jl:1111. -/
def repeatedN {t : IntTy} (x : Val) (n : JInt t) : M Itr := do take (.repeated x) (← toInt n)

/-- `cycle(xs, n) = flatten(repeated(xs, n))`, base/iterators.jl:1059. -/
def cycleN {t : IntTy} (xs : Val) (n : JInt t) : M Itr := do pure (.flatten (← repeatedN xs n))

/-- `partition(c, n)`, base/iterators.jl:1436-1439. -/
def partition {t : IntTy} (c : Itr) (n : JInt t) : M Itr := do
  if n.val < 1 then jthrow (.argumentError "cannot create partitions of length n") else
  pure (.partition c (← toInt n))

/-- `_zip_lengths_finite_equal(is)`, base/iterators.jl:401-411 (the flag). -/
def zipLengthsFiniteEqual : List Itr → M (Bool × Option JInt64)
  | [] => pure (true, none)
  | i :: is => do
    match isz i with
    | .isInfinite | .sizeUnknown => pure (false, none)
    | _ => do
      let m ← len i
      let (b, n) ← zipLengthsFiniteEqual is
      pure (b && (n.isNone || n = some m), some m)

mutual
/-- `Iterators.reverse(itr)`, base/iterators.jl:113-160, 521-526, 1074,
1120, 1255, 1379. -/
def reverse : Itr → M Itr
  | .urange k fi li d => pure (.reverse (.urange k fi li d))
  | .reverse it => pure it
  | .zip its => do
    if !(← zipLengthsFiniteEqual its).1 then
      jthrow (.argumentError "Cannot reverse zipped iterators of unknown, infinite, or unequal lengths")
    else pure (.zip (← reverseList its))
  | .cycle it => do pure (.cycle (← reverse it))
  | .repeated x => pure (.repeated x)
  | .take (.repeated x) n => pure (.take (.repeated x) n)
  | .product its => do pure (.product (← reverseList its))
  | .flatten it => do pure (.flatten (.revEach (← reverse it)))
  | .enumerate it => do pure (.revEnum (← reverse it))
  | .revEach it => do pure (.revEach (← reverse it))
  | it => pure (.reverse it)
def reverseList : List Itr → M (List Itr)
  | [] => pure []
  | it :: its => do pure ((← reverse it) :: (← reverseList its))
end

/-- `isempty(itr)`: base/abstractarray.jl:1262 for arrays, base/range.jl:711 for
unit ranges, base/tuple.jl:665-666 for tuples, base/generator.jl:58 for
generators, otherwise base/essentials.jl:1225-1229. -/
def isempty (fuel : Nat) : Itr → M Bool
  | .vec _ xs => pure (xs.length = 0)
  | .tuple xs => pure (xs = [])
  | .urange _ fi li _ => pure (li < fi)
  | .revEach it => isempty fuel it
  | it => do
    match ← isdone0 it with
    | some d => pure d
    | none => do pure (← iter fuel it none).isNone

/-- `first(itr)`, base/abstractarray.jl:474-478. -/
def first (fuel : Nat) (it : Itr) : M Val := do
  match ← iter fuel it none with
  | none => jthrow (.argumentError "collection must be non-empty")
  | some (x, _) => pure x

/-- `first(itr, n)`: base/abstractarray.jl:505 and the vector method 507-510. -/
def firstN {t : IntTy} (fuel : Nat) (it : Itr) (n : JInt t) : M (List Val) :=
  match it with
  | .vec _ xs =>
    if n.val < 0 then jthrow (.argumentError "Number of elements must be non-negative")
    else pure (xs.take (min n.val xs.length).toNat)
  | _ => do collect fuel (← take it n)

/-- `last(itr, n)`: base/abstractarray.jl:555 and the vector method 557-560. -/
def lastN {t : IntTy} (fuel : Nat) (it : Itr) (n : JInt t) : M (List Val) :=
  match it with
  | .vec _ xs =>
    if n.val < 0 then jthrow (.argumentError "Number of elements must be non-negative")
    else pure (xs.drop (xs.length - (min n.val xs.length).toNat))
  | _ => do pure (← collect fuel (← take (← reverse it) n)).reverse

/-- `only(x)`, base/iterators.jl:1659-1690. -/
def only (fuel : Nat) : Itr → M Val
  | .tuple [x] => pure x
  | .tuple _ => jthrow (.argumentError "Tuple contains n elements, must contain exactly 1 element")
  | it => do
    match ← iter fuel it none with
    | none => jthrow (.argumentError "Collection is empty, must contain exactly 1 element")
    | some (ret, s) => do
      if (← iter fuel it (some s)).isSome then
        jthrow (.argumentError "Collection has multiple elements, must contain exactly 1 element")
      else pure ret

mutual
/-- `last(x)`: `a[end]` for vectors (base/abstractarray.jl:530), the end point
of a unit range even when empty (base/range.jl), `map(last, p.iterators)` for
products (base/iterators.jl:1256). -/
def lastOf : Itr → M Val
  | .vec _ xs => match xs.getLast? with
    | some x => pure x
    | none => jthrow .boundsError
  | .urange _ _ li d => pure (.int (li.val + d))
  | .product its => do pure (.tup (← lastList its))
  | _ => jthrow (.methodError "last")
def lastList : List Itr → M (List Val)
  | [] => pure []
  | it :: its => do pure ((← lastOf it) :: (← lastList its))
end

/-- Integer value of a promoted Julia integer operation. -/
def promotedWrap (t s : IntTy) (x : Int) : Int := wrapInt (IntTy.promote t s) x

/-- `A[begin + n - 1]` for a vector or a unit range, base/iterators.jl:1756:
`begin + n - 1` is computed in `promote_type(Int, typeof(n))`, then bounds
checked. The index `n` has type `t` and value `n`. -/
def arrayNth (it : Itr) (t : IntTy) (n : Int) : M Val :=
  match it with
  | .vec _ xs =>
    let i := promotedWrap .i64 t (1 + n - 1)
    if 1 ≤ i ∧ i ≤ xs.length then pure (xs.getD (i - 1).toNat .undef) else jthrow .boundsError
  | .urange _ fi li d =>
    let i := promotedWrap .i64 t (fi.val + n - 1)
    if fi.val ≤ i ∧ i ≤ li.val then pure (.int (i + d)) else jthrow .boundsError
  | _ => jthrow (.methodError "getindex")

/-- The `for _ in 1:n-1` loop of the generic `_nth`. -/
def nthLoop (fuel : Nat) (it : Itr) : Nat → Option (Val × St) → M (Option (Val × St))
  | 0, y => pure y
  | _ + 1, none => pure none
  | k + 1, some (_, s) => do nthLoop fuel it k (← iter fuel it (some s))

/-- The generic `_nth(::IteratorSize, itr, n)`, base/iterators.jl:1777-1787. -/
def genericNth (fuel : Nat) (it : Itr) (n : Int) : M Val := do
  if n ≤ 0 then jthrow .boundsError else
  match ← nthLoop fuel it (n - 1).toNat (← iter fuel it none) with
  | none => jthrow .boundsError
  | some (x, _) => pure x

/-- `Val` as the iterator it denotes (vectors, tuples, ranges). -/
def Val.toItr : Val → Itr
  | .vec et xs => .vec et xs
  | .tup xs => .tuple xs
  | .rng lo hi => .urange .unit (i64 1) (i64 (hi - lo + 1)) (lo - 1)
  | v => .flatten (.tuple [v])

/-- `nth` of a value: arrays index, tuples and numbers iterate. -/
def nthVal (fuel : Nat) (v : Val) (t : IntTy) (n : Int) : M Val :=
  match v with
  | .vec _ _ | .rng _ _ => arrayNth v.toItr t n
  | .tup _ => genericNth fuel v.toItr n
  | .int x =>
    if n ≤ 0 then jthrow .boundsError
    else if n = 1 then pure (.int x) else jthrow .boundsError
  | _ => jthrow (.methodError "nth")

/-- `mod1(n, k)` for `n > 0`, `k > 0` (exact in the promoted type). -/
def mod1Pos (n k : Int) : Int := (n - 1) % k + 1

mutual
/-- `nth(itr, n)` for `n` of type `t`, base/iterators.jl:1753-1789. -/
def nth (fuel : Nat) : Itr → IntTy → Int → M Val
  | .vec et xs, t, n => arrayNth (.vec et xs) t n
  | .urange k fi li d, t, n => arrayNth (.urange k fi li d) t n
  -- base/iterators.jl:1754, 1758-1764
  | .cycle xs, t, n =>
    match isz xs with
    | .hasShape _ | .hasLength => do
      let bigN ← len xs
      if bigN = i64 0 then jthrow .boundsError else
      if 0 < n then nth fuel xs (IntTy.promote t .i64) (mod1Pos n bigN.val)
      else nth fuel xs t n
    | _ => genericNth fuel (.cycle xs) n
  -- base/iterators.jl:1755, 1767-1775
  | .flatten (.take (.repeated x) cycles), t, n =>
    match x.isz with
    | .hasShape _ | .hasLength => do
      let k ← x.length
      if n > (k * cycles).val ∨ k = i64 0 then jthrow .boundsError else
      if 0 < n then nthVal fuel x (IntTy.promote t .i64) (mod1Pos n k.val)
      else nthVal fuel x t n
    | _ => genericNth fuel (.flatten (.take (.repeated x) cycles)) n
  -- base/iterators.jl:1789
  | .zip its, t, n => do pure (.tup (← nthList fuel its t n))
  | it, _, n => genericNth fuel it n
def nthList (fuel : Nat) : List Itr → IntTy → Int → M (List Val)
  | [], _, _ => pure []
  | it :: its, t, n => do pure ((← nth fuel it t n) :: (← nthList fuel its t n))
end

/-- `Iterators.nth(itr, n)` with `n::t`. -/
def nthJ {t : IntTy} (fuel : Nat) (it : Itr) (n : JInt t) : M Val := nth fuel it t n.val

/-- `Iterators.peel(itr)`, base/iterators.jl:725-730: the first element and
`rest(itr, state)`. -/
def peel (fuel : Nat) (it : Itr) : M (Option (Val × Itr)) := do
  match ← iter fuel it none with
  | none => pure none
  | some (x, s) => pure (some (x, .rest it s))

/-! ## `Iterators.Stateful` -/

/-- `popfirst!(s)`, base/iterators.jl:1609-1618: the value and the advanced
object. -/
def popfirst : Itr → M (Val × Itr)
  | .stateful et xs pos =>
    if xs.length ≤ pos then .error .eof else pure (xs.getD pos .undef, .stateful et xs (pos + 1))
  | _ => jthrow (.methodError "popfirst!")

/-- `peek(s, sentinel)`, base/iterators.jl:1620-1623. -/
def peek (sentinel : Val) : Itr → M Val
  | .stateful _ xs pos => pure (if pos < xs.length then xs.getD pos .undef else sentinel)
  | _ => jthrow (.methodError "peek")

end JuliaLean.Iterators
