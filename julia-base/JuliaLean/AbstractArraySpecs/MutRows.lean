import JuliaLean.AbstractArraySpecs.CopyRows

/-!
Models of `map!` with several sources, `push!`/`pushfirst!` and `circshift!` from
`base/abstractarray.jl` (master `bbfa0ce4150`, lines 3527-3618, 3649-3682, 3756-3766),
on the array model of `Model.lean`.

Methods of the vector's own type that these bodies call (`resize!`, the one-item `push!`
and `pushfirst!`) are parameters constrained by their documented contracts in
`MutRowsProps.lean`. `reverse!(v, start, stop)` (base/array.jl:2317-2333) is modelled
line by line, and `reverse!(v)` is `reverse!(v, firstindex(v), lastindex(v))`
(base/array.jl:2269-2279).
-/

namespace JuliaLean.AbstractArraySpecs

/-! ## `map!` with two sources -/

/-- `for (i, j, k) in zip(eachindex(dest), eachindex(A), eachindex(B)); a, b = A[j], B[k];
dest[i] = f(a, b); end` (lines 3528-3532). -/
def map2Loop {α : Type} (f : α → α → α) (A B : Arr α) :
    Nat → Arr α → IterState → IterState → IterState → R (Arr α)
  | 0, dest, _, _, _ => .ok dest
  | n + 1, dest, si, sj, sk =>
    match eachindexStep dest si with
    | none => .ok dest
    | some (i, si') =>
      match eachindexStep A sj with
      | none => .ok dest
      | some (j, sj') =>
        match eachindexStep B sk with
        | none => .ok dest
        | some (k, sk') => do
          let a ← getindex A j
          let b ← getindex B k
          let dest' ← setindex dest (f a b) i
          map2Loop f A B n dest' si' sj' sk'

/-- `map!(f, dest, A, B)` (lines 3527-3534). -/
def mapBang2 {α : Type} (f : α → α → α) (dest A B : Arr α) : R (Arr α) :=
  map2Loop f A B (fuelOf dest) dest (eachStart dest) (eachStart A) (eachStart B)

/-! ## `map!` with any number of sources -/

/-- `ith_all(i, as)` (lines 3538-3542): `(as[1][i], ith_all(i, tail(as))...)`. -/
def ithAll {α : Type} (i : I64) : List (Arr α) → R (List α)
  | [] => .ok []
  | a :: as => do
    let x ← getindex a [i]
    let rest ← ithAll i as
    .ok (x :: rest)

/-- `for i in idxs; as = ith_all(i, As); dest[i] = f(as...); end` (lines 3547-3551), with
`idxs = LinearIndices(dest)` iterating the range `linearAxis dest`. -/
def mapNLin {α : Type} (f : List α → α) (D0 : Arr α) (As : List (Arr α)) :
    Nat → Arr α → IterState → R (Arr α)
  | 0, dest, _ => .ok dest
  | n + 1, dest, st =>
    match eachindexStep D0 st with
    | none => .ok dest
    | some (I, st') => do
      let as ← ithAll (I.headD (i64 0)) As
      let dest' ← setindex dest (f as) I
      mapNLin f D0 As n dest' st'

/-- One step of `map(eachindex, As)` zipped: every source yields its next index, or the
zip is exhausted. -/
def stepAll {α : Type} : List (Arr α) → List IterState → Option (List (List I64) × List IterState)
  | [], _ => some ([], [])
  | a :: as, s :: ss =>
    match eachindexStep a s with
    | none => none
    | some (I, s') => (stepAll as ss).map (fun p => (I :: p.1, s' :: p.2))
  | _ :: _, [] => none

/-- `ntuple(j -> getindex(As[j], Is[j]), length(As))` (line 3554). -/
def getAll {α : Type} : List (Arr α) → List (List I64) → R (List α)
  | a :: as, I :: Is => do
    let x ← getindex a I
    let rest ← getAll as Is
    .ok (x :: rest)
  | _, _ => .ok []

/-- `for (i, Is...) in zip(eachindex(dest), map(eachindex, As)...); ...; dest[i] = val; end`
(lines 3553-3557). -/
def mapNZip {α : Type} (f : List α → α) (As : List (Arr α)) :
    Nat → Arr α → IterState → List IterState → R (Arr α)
  | 0, dest, _, _ => .ok dest
  | n + 1, dest, si, ss =>
    match eachindexStep dest si with
    | none => .ok dest
    | some (i, si') =>
      match stepAll As ss with
      | none => .ok dest
      | some (Is, ss') => do
        let as ← getAll As Is
        let dest' ← setindex dest (f as) i
        mapNZip f As n dest' si' ss'

/-- `LinearIndices(x) == LinearIndices(dest)`: two `LinearIndices` arrays are `==` when
their axes (those of `x` and `dest`) are `==`, since equal axes give equal values. -/
def linIdxEq {α : Type} (x dest : Arr α) : Bool := axesEq x.axes dest.axes

/-- `map_n!(f, dest, As)` (lines 3544-3560). -/
def mapN {α : Type} (f : List α → α) (dest : Arr α) (As : List (Arr α)) : R (Arr α) :=
  if As.all (fun x => linIdxEq x dest) then mapNLin f dest As (fuelOf dest) dest .rngStart
  else mapNZip f As (fuelOf dest) dest (eachStart dest) (As.map eachStart)

/-- `map!(f, dest, As...)` (lines 3593-3596). -/
def mapBangN {α : Type} (f : List α → α) (dest : Arr α) (As : List (Arr α)) : R (Arr α) :=
  if As.isEmpty then .error .assertionError else mapN f dest As

/-- `map!(f, inout) = map!(f, inout, inout)` (line 3618), the one-source `map!`. -/
def mapBangInplace {α : Type} (f : α → α) (inout : Arr α) : R (Arr α) := mapBang f inout inout

/-! ## `push!` and `pushfirst!` -/

/-- `push!(a::AbstractVector{T}, item)` (lines 3649-3656); `conv` is
`item isa T ? item : convert(T, item)::T` and `resize` is `resize!` of `a`'s type. -/
def pushOne {α β : Type} (conv : β → R α) (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (item : β) :
    R (Arr α) := do
  let itemT ← conv item
  let newLength := lengthA a + i64 1
  let a ← resize a newLength
  setindex a itemT [(linearAxis a).hi]

/-- `push!(a::AbstractVector{Any}, x)` (lines 3659-3664). -/
def pushOneAny {α : Type} (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (x : α) : R (Arr α) := do
  let newLength := lengthA a + i64 1
  let a ← resize a newLength
  setindex a x [(linearAxis a).hi]

/-- `for i = 1:nx; a[e+i] = x[i]; end` (lines 3671-3673). -/
def pushManyLoop {α : Type} (e : I64) : Nat → Arr α → List α → R (Arr α)
  | _, a, [] => .ok a
  | i, a, x :: xs => do
    let a' ← setindex a x [e + i64 (i : Int)]
    pushManyLoop e (i + 1) a' xs

/-- `push!(a::AbstractVector{Any}, x...)` (lines 3665-3675). -/
def pushManyAny {α : Type} (resize : Arr α → I64 → R (Arr α)) (a : Arr α) (x : List α) : R (Arr α) := do
  let na := lengthA a
  let nx := i64 x.length
  let a ← resize a (na + nx)
  let e := (linearAxis a).hi - nx
  pushManyLoop e 1 a x

/-- `push!(A, a, b) = push!(push!(A, a), b)` (line 3679) for a collection `A` of any type
`C` (an `AbstractVector` dispatches to `push!(a::AbstractVector, iter...)` in
base/array.jl instead); `push` is the one-item `push!` of `C`. -/
def push2 {C α : Type} (push : C → α → R C) (A : C) (a b : α) : R C := do
  let A' ← push A a
  push A' b

/-- `push!(A, a, b, c...) = push!(push!(A, a, b), c...)` (line 3680) for a nonempty `c`,
with the call `push!(X, c...)` dispatching on the number of items. -/
def pushVar {C α : Type} (push : C → α → R C) : C → α → α → α → List α → R C
  | A, a, b, c, [] => do
    let A' ← push2 push A a b
    push A' c
  | A, a, b, c, d :: [] => do
    let A' ← push2 push A a b
    push2 push A' c d
  | A, a, b, c, d :: e :: es => do
    let A' ← push2 push A a b
    pushVar push A' c d e es

/-- `pushfirst!(A, a, b) = pushfirst!(pushfirst!(A, b), a)` (line 3681) for a collection
`A` that is not an `AbstractVector`. -/
def pushfirst2 {C α : Type} (pushfirst : C → α → R C) (A : C) (a b : α) : R C := do
  let A' ← pushfirst A b
  pushfirst A' a

/-- `pushfirst!(A, a, b, c...) = pushfirst!(pushfirst!(A, c...), a, b)` (line 3682) for a
nonempty `c`, with `pushfirst!(X, c...)` dispatching on the number of items. -/
def pushfirstVar {C α : Type} (pushfirst : C → α → R C) : C → α → α → α → List α → R C
  | A, a, b, c, [] => do
    let A' ← pushfirst A c
    pushfirst2 pushfirst A' a b
  | A, a, b, c, d :: [] => do
    let A' ← pushfirst2 pushfirst A c d
    pushfirst2 pushfirst A' a b
  | A, a, b, c, d :: e :: es => do
    let A' ← pushfirstVar pushfirst A c d e es
    pushfirst2 pushfirst A' a b

/-! ## `circshift!` -/

/-- `@inbounds for i in s:midpoint(s, n-1); v[i], v[r] = v[r], v[i]; r -= 1; end`
(base/array.jl:2326-2330); `k` is the number of iterations left. -/
def revLoop {α : Type} : Nat → Arr α → I64 → I64 → R (Arr α)
  | 0, v, _, _ => .ok v
  | k + 1, v, i, r => do
    let x ← getindex v [r]
    let y ← getindex v [i]
    let v1 ← setindex v x [i]
    let v2 ← setindex v1 y [r]
    revLoop k v2 (i + i64 1) (r - i64 1)

/-- `midpoint(lo, hi) = lo +% ((hi -% lo) >>> 0x01)` (base/array.jl:2288) for `Int`s. -/
def midpoint (lo hi : I64) : I64 := lo + i64 (wrapInt .u64 (hi - lo).val / 2)

/-- `reverse!(v::AbstractVector, start, stop)` (base/array.jl:2317-2333) for `Int`
arguments; `liv = LinearIndices(v)` is the range `linearAxis v`. -/
def reverseRange {α : Type} (v : Arr α) (s n : I64) : R (Arr α) :=
  if n > s then
    let liv := linearAxis v
    if ¬(liv.lo ≤ s ∧ s ≤ liv.hi) then .error .boundsError
    else if ¬(liv.lo ≤ n ∧ n ≤ liv.hi) then .error .boundsError
    else
      let m := midpoint s (n - i64 1)
      revLoop (if s ≤ m then (m.val - s.val + 1).toNat else 0) v s n
  else .ok v

/-- `mod(x, n)` for a positive `Int` `n`: the result in `0:n-1`. -/
def modI (x : Int) (n : I64) : I64 := i64 (x % n.val)

/-- `circshift!(a::AbstractVector, shift::Integer)` (lines 3756-3766); `shift` is the
value of any `Integer` (`mod(shift, n)` is exact and lies in `0:n-1`). -/
def circshiftBang {α : Type} (a : Arr α) (shift : Int) : R (Arr α) :=
  let n := lengthA a
  if n == i64 0 then .ok a
  else
    let shift := modI shift n
    if shift == i64 0 then .ok a
    else do
      let l := (linearAxis a).hi
      let a ← reverseRange a (linearAxis a).lo (l - shift)
      let a ← reverseRange a (l - shift + i64 1) (linearAxis a).hi
      reverseRange a (linearAxis a).lo (linearAxis a).hi

end JuliaLean.AbstractArraySpecs
