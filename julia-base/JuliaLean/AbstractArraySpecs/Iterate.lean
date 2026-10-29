import JuliaLean.AbstractArraySpecs.Model

/-!
Models of array iteration (base/abstractarray.jl:1239-1260, with `CartesianIndices`
iteration from base/multidimensional.jl:445-486) and of the loops built on it:
`isequal` and `==` (base/abstractarray.jl:3106-3117, 3149-3163) over
`zip(A, B)`, and `map!(f, dest, A)` (lines 3482-3488) over
`zip(eachindex(dest), eachindex(A))`.
-/

namespace JuliaLean.AbstractArraySpecs

/-- Iteration states: the integer state of an `IndexLinear` array, or the tuple
state `(eachindex(A),)` / `(CartesianIndices, CartesianIndex)` of the other style;
a 0-d `CartesianIndices` uses a `done::Bool` state (multidimensional.jl:486). -/
inductive IterState where
  | lin (k : I64)
  | cartStart
  | cart (I : List I64)
  | cart0 (done : Bool)
  /-- Iteration of an `AbstractUnitRange` before the first element / after yielding `i`. -/
  | rngStart
  | rng (i : I64)
  deriving DecidableEq, Repr

/-- `iterate_starting_state(A)` (base/abstractarray.jl:1245-1247):
`firstindex(A)` for `IndexLinear`, `(eachindex(A),)` otherwise. -/
def iterStart {α : Type} (A : Arr α) : IterState :=
  match A.style with
  | .linear => .lin (linearAxis A).lo
  | .cartesian => .cartStart

/-- `i in r` for a unit range. -/
def inAx (i : I64) (r : Ax) : Bool := decide (r.lo ≤ i) && decide (i ≤ r.hi)

/-- `__inc(state, indices)` (base/multidimensional.jl:468-483) for unit ranges
(`step(rng) == 1`). -/
def ciInc : List I64 → List Ax → Bool × List I64
  | [s], [r] => (s != r.hi, [s + i64 1])
  | s :: s2 :: ss, r :: r2 :: rs =>
      if s != r.hi then (true, (s + i64 1) :: s2 :: ss)
      else
        let t := ciInc (s2 :: ss) (r2 :: rs)
        (t.1, r.lo :: t.2)
  | _, _ => (false, [])

/-- `iterate(A, state)` (base/abstractarray.jl:1250-1259). The `IndexLinear` method
checks `checkbounds(Bool, A, state)` and steps by one; the tuple method iterates
`CartesianIndices(axes(A))` and indexes `A` with the resulting `CartesianIndex`,
which `to_indices` splats into `ndims(A)` integer indices. -/
def iterateA {α : Type} (A : Arr α) : IterState → R (Option (α × IterState))
  | .lin k =>
      if checkboundsBool A [k] then do
        let x ← getindex A [k]
        .ok (some (x, .lin (k + i64 1)))
      else .ok none
  | .cartStart =>
      match A.axes with
      | [] => do
          let x ← getindex A []
          .ok (some (x, .cart0 true))
      | axs =>
          let f := axs.map (·.lo)
          if (f.zip axs).all (fun p => inAx p.1 p.2) then do
            let x ← getindex A f
            .ok (some (x, .cart f))
          else .ok none
  | .cart I =>
      let t := ciInc I A.axes
      if t.1 then do
        let x ← getindex A t.2
        .ok (some (x, .cart t.2))
      else .ok none
  | .cart0 done =>
      if done then .ok none
      else do
        let x ← getindex A []
        .ok (some (x, .cart0 true))
  | .rngStart => .ok none
  | .rng _ => .ok none

/-- `collect`-style consumption of `iterate(A)` with fuel. -/
def iterAll {α : Type} (A : Arr α) : Nat → IterState → R (List α)
  | 0, _ => .ok []
  | f + 1, st => do
      match ← iterateA A st with
      | none => .ok []
      | some (x, st') => do
          let rest ← iterAll A f st'
          .ok (x :: rest)

/-- `for (a, b) in zip(A, B)` with fuel: `zip` iterates `A` then `B` and stops when
either is exhausted. `step a b` returns `some r` to leave the loop early with `r`. -/
def zipLoop {α β γ : Type} (A : Arr α) (B : Arr β) (step : α → β → Option γ) (done : γ) :
    Nat → IterState → IterState → R γ
  | 0, _, _ => .ok done
  | f + 1, sa, sb => do
      match ← iterateA A sa with
      | none => .ok done
      | some (a, sa') =>
        match ← iterateA B sb with
        | none => .ok done
        | some (b, sb') =>
          match step a b with
          | some r => .ok r
          | none => zipLoop A B step done f sa' sb'

/-- Fuel for loops over the elements of `A`. -/
def fuelOf {α : Type} (A : Arr α) : Nat := A.data.length + 1

/-- `isequal(A, B)` (base/abstractarray.jl:3106-3117), with `iseq` the element
`isequal`; `A === B` cannot be observed on values. -/
def isequalA {α : Type} (iseq : α → α → Bool) (A B : Arr α) : R Bool :=
  if !axesEq A.axes B.axes then .ok false
  else zipLoop A B (fun a b => if !iseq a b then some false else none) true
    (fuelOf A) (iterStart A) (iterStart B)

/-- Three-valued element `==`: `some b` or `none` for `missing`. -/
abbrev Eq3 (α : Type) := α → α → Option Bool

/-- `==(A, B)` (base/abstractarray.jl:3149-3163): `false` at the first `false`,
otherwise `missing` if any comparison was `missing`, otherwise `true`. The running
`anymissing` flag is threaded through the loop state. -/
def eqLoop {α : Type} (A B : Arr α) (eq : Eq3 α) :
    Nat → Bool → IterState → IterState → R (Option Bool)
  | 0, m, _, _ => .ok (if m then none else some true)
  | f + 1, m, sa, sb => do
      match ← iterateA A sa with
      | none => .ok (if m then none else some true)
      | some (a, sa') =>
        match ← iterateA B sb with
        | none => .ok (if m then none else some true)
        | some (b, sb') =>
          match eq a b with
          | none => eqLoop A B eq f true sa' sb'
          | some false => .ok (some false)
          | some true => eqLoop A B eq f m sa' sb'

def eqA {α : Type} (eq : Eq3 α) (A B : Arr α) : R (Option Bool) :=
  if !axesEq A.axes B.axes then .ok (some false)
  else eqLoop A B eq (fuelOf A) false (iterStart A) (iterStart B)

/-- Whether `eachindex(A)` is a unit range of linear indices: `eachindex(A::AbstractVector)
= axes1(A)` for every vector, `eachindex(IndexLinear(), A) = oneto(length(A))` for other
`IndexLinear` arrays, and `CartesianIndices(axes(A))` otherwise
(base/abstractarray.jl:325, 384, 394-396; base/multidimensional.jl:435). -/
def eachRange {α : Type} (A : Arr α) : Bool :=
  match A.style, A.axes with
  | .linear, _ => true
  | .cartesian, [_] => true
  | .cartesian, _ => false

/-- Starting state of `eachindex(A)`. -/
def eachStart {α : Type} (A : Arr α) : IterState :=
  if eachRange A then .rngStart else .cartStart

/-- `eachindex(A)`'s iteration as index lists: `eachindex(IndexLinear(), A)` for
linear arrays, a unit range iterated by `iterate(r) = isempty(r) ? nothing :
(first(r), first(r))` and `iterate(r, i) = i == last(r) ? nothing : (i + 1, i + 1)`
(base/range.jl), and `CartesianIndices(axes(A))` otherwise. -/
def eachindexStep {α : Type} (A : Arr α) : IterState → Option (List I64 × IterState)
  | .rngStart =>
      let r := linearAxis A
      if axIsEmpty r then none else some ([r.lo], .rng r.lo)
  | .rng i =>
      let r := linearAxis A
      if i = r.hi then none else some ([i + i64 1], .rng (i + i64 1))
  | .lin _ => none
  | .cartStart =>
      match A.axes with
      | [] => some ([], .cart0 true)
      | axs =>
          let f := axs.map (·.lo)
          if (f.zip axs).all (fun p => inAx p.1 p.2) then some (f, .cart f) else none
  | .cart I =>
      let t := ciInc I A.axes
      if t.1 then some (t.2, .cart t.2) else none
  | .cart0 done => if done then none else some ([], .cart0 true)

/-- `map!(f, dest, A)` (base/abstractarray.jl:3482-3488):
`for (i, j) in zip(eachindex(dest), eachindex(A)); dest[i] = f(A[j]); end`. -/
def mapLoop {α : Type} (f : α → α) (A : Arr α) :
    Nat → Arr α → IterState → IterState → R (Arr α)
  | 0, dest, _, _ => .ok dest
  | n + 1, dest, si, sj =>
      match eachindexStep dest si with
      | none => .ok dest
      | some (i, si') =>
        match eachindexStep A sj with
        | none => .ok dest
        | some (j, sj') => do
            let a ← getindex A j
            let dest' ← setindex dest (f a) i
            mapLoop f A n dest' si' sj'

def mapBang {α : Type} (f : α → α) (dest A : Arr α) : R (Arr α) :=
  mapLoop f A (fuelOf dest) dest (eachStart dest) (eachStart A)

/-- `cmp(x::Int, y::Int)` (base/operators.jl:`cmp(x, y) = isless(x, y) ? -1 : ifelse(isless(y, x), 1, 0)`). -/
def cmpI (x y : I64) : Int := if x < y then -1 else if y < x then 1 else 0

/-- `cmp(A::AbstractVector, B::AbstractVector)` (base/abstractarray.jl:3119-3128) with
element `isequal` `iseq` and `isless` `lt`: `firstindex(v) = first(axes1(v))` for
vectors (lines 452, 140-141). -/
def cmpV {α : Type} (iseq lt : α → α → Bool) (A B : Arr α) : R Int :=
  let ai1 := (linearAxis A).lo
  let bi1 := (linearAxis B).lo
  if !(ai1 == bi1) then .ok (cmpI ai1 bi1)
  else zipLoop A B (fun a b => if !iseq a b then some (if lt a b then -1 else 1) else none)
    (cmpI (lengthA A) (lengthA B)) (fuelOf A) (iterStart A) (iterStart B)

/-- `isless(A::AbstractVector, B::AbstractVector) = cmp(A, B) < 0` (line 3145). -/
def islessV {α : Type} (iseq lt : α → α → Bool) (A B : Arr α) : R Bool := do
  let c ← cmpV iseq lt A B
  .ok (decide (c < 0))

end JuliaLean.AbstractArraySpecs
