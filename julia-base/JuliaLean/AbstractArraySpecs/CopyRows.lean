import JuliaLean.AbstractArraySpecs.Copy

/-!
Models of the remaining `copyto!`, `copy!` and `copyto_axcheck!` methods of
`base/abstractarray.jl` (master `bbfa0ce4150`, lines 920-1189), built on the array
model of `Model.lean` and `Copy.lean`.

An iterable `src` (any collection, possibly without a length) is the list of the
elements `iterate(src)` yields, in order; `hasLen` is `haslength(src)`.
-/

namespace JuliaLean.AbstractArraySpecs

/-! ## From an iterable source -/

/-- The loop of `copyto!(dest::AbstractArray, src)` (lines 941-951): `y` is the current
`iterate(destiter)` result, `D` the array whose `eachindex` is `destiter`. -/
def copyIterLoop {α : Type} (D : Arr α) : Arr α → Option (List I64 × IterState) → List α → R (Arr α)
  | dest, _, [] => .ok dest
  | _, none, _ :: _ => .error .argumentError
  | dest, some (I, st), x :: xs => do
      let dest' ← setindex dest x I
      copyIterLoop D dest' (eachindexStep D st) xs

/-- `copyto!(dest::AbstractArray, src)` (lines 941-951). -/
def copytoIter {α : Type} (dest : Arr α) (src : List α) : R (Arr α) :=
  copyIterLoop dest dest (eachindexStep dest (eachStart dest)) src

/-- `for x in src; dest[i] = x; i += 1; end` (lines 960-968, 993-998). -/
def writeLinear {α : Type} : Arr α → I64 → List α → R (Arr α)
  | dest, _, [] => .ok dest
  | dest, i, x :: xs => do
      let dest' ← setindex dest x [i]
      writeLinear dest' (i + i64 1) xs

/-- `copyto!(dest::AbstractArray, dstart::Integer, src)` (lines 953-971) for an `Int`
`dstart`. -/
def copytoIterAt {α : Type} (hasLen : Bool) (dest : Arr α) (dstart : I64) (src : List α) :
    R (Arr α) :=
  let i := dstart
  if hasLen && decide (i64 0 < lengthA dest) then
    let n := i64 src.length
    if n == i64 0 then .ok dest
    else do
      checkbounds dest [i]
      if !decide (n ≤ (linearAxis dest).hi - i + i64 1) then .error .boundsError
      else writeLinear dest i src
  else writeLinear dest i src

/-- The skip loop `for j = 1:(sstart-1)` (lines 977-985 and 1013-1021): `ys` is the rest
of `src` starting at `y`; each step throws `ArgumentError` when `y === nothing`. -/
def skipSrc {α : Type} : Nat → List α → R (List α)
  | 0, ys => .ok ys
  | _ + 1, [] => .error .argumentError
  | k + 1, _ :: ys => skipSrc k ys

/-- `copyto!(dest::AbstractArray, dstart::Integer, src, sstart::Integer)` (lines 973-1000)
for `Int` arguments. -/
def copytoIterFrom {α : Type} (dest : Arr α) (dstart : I64) (src : List α) (sstart : I64) :
    R (Arr α) :=
  if sstart < i64 1 then .error .argumentError
  else do
    let ys ← skipSrc (sstart.val - 1).toNat src
    match ys with
    | [] => .error .argumentError
    | _ :: _ => writeLinear dest dstart ys

/-- `for val in Iterators.take(Iterators.rest(src, st), n-1); i += 1; dest[i] = val; end`
(lines 1031-1034), returning `dest` and the final `i`. -/
def takeLoop {α : Type} : Arr α → I64 → List α → R (Arr α × I64)
  | dest, i, [] => .ok (dest, i)
  | dest, i, x :: xs => do
      let dest' ← setindex dest x [i + i64 1]
      takeLoop dest' (i + i64 1) xs

/-- `copyto!(dest::AbstractArray, dstart::Integer, src, sstart::Integer, n::Integer)`
(lines 1003-1037) for `Int` arguments; `dstart ∈ inds` with `inds = LinearIndices(dest)`. -/
def copytoIterN {α : Type} (dest : Arr α) (dstart : I64) (src : List α) (sstart n : I64) :
    R (Arr α) :=
  if n < i64 0 then .error .argumentError
  else if n == i64 0 then .ok dest
  else
    let inds := linearAxis dest
    if sstart < i64 1 then .error .argumentError
    else if !(inAx dstart inds && decide (n ≤ inds.hi - dstart + i64 1)) then .error .boundsError
    else
      let dmax := dstart + n - i64 1
      do
        let ys ← skipSrc (sstart.val - 1).toNat src
        match ys with
        | [] => .error .argumentError
        | val :: rest =>
          let dest ← setindex dest val [dstart]
          let (dest, i) ← takeLoop dest dstart (rest.take (n.val - 1).toNat)
          if i < dmax then .error .boundsError else .ok dest

/-! ## Between arrays, with start indices -/

/-- `@inbounds for i = 0:n-1; dest[dstart+i] = src′[sstart+i]; end` (lines 1149-1151). -/
def copyNLoop {α : Type} (src : Arr α) (dstart sstart : I64) : Nat → Nat → Arr α → R (Arr α)
  | 0, _, D => .ok D
  | k + 1, i, D => do
      let v ← getindex src [sstart + i64 i]
      let D' ← setindex D v [dstart + i64 i]
      copyNLoop src dstart sstart k (i + 1) D'

/-- `copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray, sstart::Integer,
n::Integer)` (lines 1135-1153) for `Int` arguments; `aliased` is `mightalias(dest, src)`. -/
def copytoN {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α)
    (sstart n : I64) : R (Arr α) :=
  if n == i64 0 then .ok dest
  else if n < i64 0 then .error .argumentError
  else
    let destinds := linearAxis dest
    let srcinds := linearAxis src
    if !(checkindex destinds dstart && decide (n ≤ destinds.hi - dstart + i64 1)) then
      .error .boundsError
    else if !(checkindex srcinds sstart && decide (n ≤ srcinds.hi - sstart + i64 1)) then
      .error .boundsError
    else
      let src' := unaliasA aliased src
      copyNLoop src' dstart sstart n.val.toNat 0 dest

/-- `copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray)` (lines 1125-1127). -/
def copytoAt {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α) : R (Arr α) :=
  copytoN aliased dest dstart src (linearAxis src).lo (lengthA src)

/-- `copyto!(dest::AbstractArray, dstart::Integer, src::AbstractArray, sstart::Integer)`
(lines 1129-1133); `checkbounds(Bool, srcinds, sstart)` checks `sstart` against
`eachindex(IndexLinear(), LinearIndices(src))`, the range `linearAxis src`. -/
def copytoFrom {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α)
    (sstart : I64) : R (Arr α) :=
  let srcinds := linearAxis src
  if !checkindex srcinds sstart then .error .boundsError
  else copytoN aliased dest dstart src sstart (srcinds.hi - sstart + i64 1)

/-! ## Rectangular blocks -/

/-- An `AbstractRange{Int}` whose elements are `first + k * step` for `k < len`
(`UnitRange`, `StepRange`, `OneTo`, `StepRangeLen` with `Int` step). -/
structure Rg where
  first : I64
  step : I64
  len : Nat
  deriving DecidableEq, Repr

/-- The `k`-th element (0-based). -/
def Rg.at (r : Rg) (k : Nat) : I64 := i64 (r.first.val + (k : Int) * r.step.val)

/-- The elements from the `k`-th on, `m` of them. -/
def Rg.elemsFrom (r : Rg) : Nat → Nat → List I64
  | _, 0 => []
  | k, m + 1 => r.at k :: r.elemsFrom (k + 1) m

/-- The elements in iteration order. -/
def Rg.elems (r : Rg) : List I64 := r.elemsFrom 0 r.len

/-- A range object: its length is an `Int` and every element is an `Int`. -/
def Rg.WF (r : Rg) : Prop :=
  (r.len : Int) ≤ tmax ∧ ∀ k < r.len, tmin ≤ r.first.val + (k : Int) * r.step.val ∧
    r.first.val + (k : Int) * r.step.val ≤ tmax

/-- `checkindex(Bool, inds, r::AbstractRange)` (base/abstractarray.jl:756-757):
`isempty(r) | (checkindex(Bool, inds, first(r)) & checkindex(Bool, inds, last(r)))`. -/
def checkindexRg (inds : Ax) (r : Rg) : Bool :=
  decide (r.len = 0) || (checkindex inds r.first && checkindex inds (r.at (r.len - 1)))

/-- `checkbounds_indices(Bool, inds, I)` (lines 722-728) for range indices. -/
def checkboundsRgs : List Ax → List Rg → Bool
  | inds, [] => inds.all (fun x => axLength x == i64 1)
  | inds, r :: I => checkindexRg (inds.headD (oneTo (i64 1))) r && checkboundsRgs inds.tail I

/-- The inner loop of lines 1171-1175: `idest = first(ir_dest); for isrc in ir_src;
B[idest,jdest] = A′[isrc,jsrc]; idest += step(ir_dest); end`. -/
def blockInner {α : Type} (A : Arr α) (stepI jdest jsrc : I64) : I64 → List I64 → Arr α → R (Arr α)
  | _, [], B => .ok B
  | idest, isrc :: is, B => do
      let v ← getindex A [isrc, jsrc]
      let B' ← setindex B v [idest, jdest]
      blockInner A stepI jdest jsrc (idest + stepI) is B'

/-- The outer loop of lines 1170-1177: `for jsrc in jr_src; ...; jdest += step(jr_dest); end`. -/
def blockOuter {α : Type} (A : Arr α) (ird : Rg) (stepJ : I64) (irs : List I64) :
    I64 → List I64 → Arr α → R (Arr α)
  | _, [], B => .ok B
  | jdest, jsrc :: js, B => do
      let B' ← blockInner A ird.step jdest jsrc ird.first irs B
      blockOuter A ird stepJ irs (jdest + stepJ) js B'

/-- `copyto!(B::AbstractVecOrMat, ir_dest, jr_dest, A::AbstractVecOrMat, ir_src, jr_src)`
(lines 1159-1181); `aliased` is `mightalias(B, A)`. -/
def copytoBlock {α : Type} (aliased : Bool) (B : Arr α) (ird jrd : Rg) (A : Arr α) (irs jrs : Rg) :
    R (Arr α) :=
  if i64 ird.len ≠ i64 irs.len then .error .argumentError
  else if i64 jrd.len ≠ i64 jrs.len then .error .argumentError
  else do
    if !checkboundsRgs B.axes [ird, jrd] then .error .boundsError
    if !checkboundsRgs A.axes [irs, jrs] then .error .boundsError
    let A' := unaliasA aliased A
    blockOuter A' ird jrd.step irs.elems jrd.first jrs.elems B

/-! ## With an axes check -/

/-- `_checkaxs(axd, axs) = axd == axs || throw(DimensionMismatch(...))` (line 1184). -/
def checkaxs (axd axs : List Ax) : R Bool :=
  if axesEq axd axs then .ok true else .error .dimensionMismatch

/-- `copyto_axcheck!(dest, src)` (lines 1186-1189). -/
def copytoAxcheck {α : Type} (destBit aliased : Bool) (dest src : Arr α) : R (Arr α) := do
  let _ ← checkaxs dest.axes src.axes
  copytoA destBit aliased dest src

/-- `copy!(dst::AbstractArray, src::AbstractArray)` (lines 929-933). -/
def copyBangA {α : Type} (destBit aliased : Bool) (dst src : Arr α) : R (Arr α) :=
  if !axesEq dst.axes src.axes then .error .argumentError
  else copytoA destBit aliased dst src

/-- `copy!(dst::AbstractVector, src::AbstractVector)` (lines 920-927); `resize` is the
`resize!` method of `dst`'s type. -/
def copyBangV {α : Type} (resize : Arr α → I64 → R (Arr α)) (destBit aliased : Bool)
    (dst src : Arr α) : R (Arr α) :=
  if !((linearAxis dst).lo == (linearAxis src).lo) then .error .argumentError
  else do
    let dst ← if lengthA dst ≠ lengthA src then resize dst (lengthA src) else .ok dst
    copytoA destBit aliased dst src

end JuliaLean.AbstractArraySpecs
