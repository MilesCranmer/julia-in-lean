import JuliaLean.AbstractArraySpecs.Iterate

/-!
Model of `copyto!(dest::AbstractArray, src::AbstractArray)` (base/abstractarray.jl:1072-1080),
`copyto!(deststyle, dest, srcstyle, src)` (lines 1082-1086) and `copyto_unaliased!`
(lines 1088-1123), including the `BitArray` destination path `_copyto_bitarray!`
(base/bitarray.jl:507-532) and `unalias` (lines 1566, 1582).
-/

namespace JuliaLean.AbstractArraySpecs

/-- Single-index implementation (lines 1095-1098):
`for i in srcinds; dest[i + Δi] = src[i]; end`. `srcinds = LinearIndices(src)` iterates
the unit range `linearAxis src` (the same range as `eachindex(IndexLinear(), src)`) for
either style of `src`; `eachindexStep` from `.rngStart` walks that range. -/
def copyLL {α : Type} (src : Arr α) (Δ : I64) : Nat → Arr α → IterState → R (Arr α)
  | 0, D, _ => .ok D
  | n + 1, D, st =>
    match eachindexStep src st with
    | none => .ok D
    | some (I, st') => do
        let v ← getindex src I
        let D' ← setindex D v (I.map (· + Δ))
        copyLL src Δ n D' st'

/-- Dual-index implementation (lines 1100-1104):
`i = idf - 1; for a in src; dest[i += 1] = a; end`. -/
def copyLC {α : Type} (src : Arr α) : Nat → Arr α → I64 → IterState → R (Arr α)
  | 0, D, _, _ => .ok D
  | n + 1, D, i, st => do
    match ← iterateA src st with
    | none => .ok D
    | some (a, st') =>
      let i' := i + i64 1
      let D' ← setindex D a [i']
      copyLC src n D' i' st'

/-- Shared-iterator implementation (lines 1109-1112):
`for I in iterdest; dest[I] = src[I]; end`. -/
def copyShared {α : Type} (src : Arr α) : Nat → Arr α → IterState → R (Arr α)
  | 0, D, _ => .ok D
  | n + 1, D, st =>
    match eachindexStep D st with
    | none => .ok D
    | some (I, st') => do
        let v ← getindex src I
        let D' ← setindex D v I
        copyShared src n D' st'

/-- `iterdest == itersrc` (line 1108) for `eachindex(dest)` and `eachindex(src)`: two
unit ranges compare with range `==` (base/range.jl:1141-1180); two `CartesianIndices`
compare as arrays, equal exactly when their index ranges are pairwise `==`
(base/abstractarray.jl:3149-3163); a unit range never equals a `CartesianIndices` of
another dimensionality (their axes differ). -/
def iterEq {α : Type} (dest src : Arr α) : Bool :=
  match eachRange dest, eachRange src with
  | true, true => axEq (linearAxis dest) (linearAxis src)
  | false, false => axesEq dest.axes src.axes
  | _, _ => false

/-- `copyto_unaliased!(deststyle, dest, srcstyle, src)` (lines 1088-1123) for the given
style arguments `ds` and `ss` (which `copyto!(deststyle, dest, srcstyle, src)` may pass
independently of `IndexStyle(dest)` and `IndexStyle(src)`). -/
def copytoUnaliasedS {α : Type} (ds ss : Style) (dest src : Arr α) : R (Arr α) :=
  if isemptyA src then .ok dest
  else
    let destinds := linearAxis dest
    let srcinds := linearAxis src
    let idf := destinds.lo
    let isf := srcinds.lo
    let Δ := idf - isf
    if !(checkindex destinds (isf + Δ) && checkindex destinds (srcinds.hi + Δ)) then
      .error .boundsError
    else
      match ds, ss with
      | .linear, .linear => copyLL src Δ (fuelOf src) dest .rngStart
      | .linear, .cartesian => copyLC src (fuelOf src) dest (idf - i64 1) (iterStart src)
      | .cartesian, _ =>
        if iterEq dest src then copyShared src (fuelOf dest) dest (eachStart dest)
        else mapLoop id src (fuelOf dest) dest (eachStart dest) (eachStart src)

/-- `copyto_unaliased!(IndexStyle(dest), dest, IndexStyle(src), src)`. -/
def copytoUnaliased {α : Type} (dest src : Arr α) : R (Arr α) :=
  copytoUnaliasedS dest.style src.style dest src

/-- `unalias(dest, A) = mightalias(dest, A) ? unaliascopy(A) : A` (line 1566) with
`unaliascopy(A) = copy(A)` (line 1582). Arrays are values here, so a copy of `src` has the
same contents as `src`; `aliased` is the outcome of `mightalias(dest, src)`. -/
def unaliasA {α : Type} (aliased : Bool) (src : Arr α) : Arr α :=
  if aliased then { src with data := src.data } else src

/-- The element loop of `_copyto_bitarray!(B, A)` (base/bitarray.jl:513-531): starting from
`Ai = first(eachindex(A))`, bit `k` of `B` (element `k` of the 1-based `B`) becomes
`A[Ai]` and `Ai = nextind(A, Ai)` advances through `eachindex(A)`; the chunk masks keep
the other bits of `B`. -/
def bitLoop {α : Type} (A : Arr α) : Nat → Arr α → I64 → IterState → R (Arr α)
  | 0, B, _, _ => .ok B
  | n + 1, B, k, st =>
    match eachindexStep A st with
    | none => .ok B
    | some (I, st') => do
        let v ← getindex A I
        let B' ← setindex B v [k]
        bitLoop A n B' (k + i64 1) st'

/-- `_copyto_bitarray!(B::BitArray, A::AbstractArray)` (base/bitarray.jl:507-532). -/
def copytoBitarray {α : Type} (B A : Arr α) : R (Arr α) :=
  let l := lengthA A
  if l == i64 0 then .ok B
  else if lengthA B < l then .error .boundsError
  else bitLoop A (fuelOf A) B (i64 1) (eachStart A)

/-- `copyto!(dest::AbstractArray, src::AbstractArray)` (lines 1072-1080); `destBit` is
`dest isa BitArray`, `aliased` is `mightalias(dest, src)`. -/
def copytoA {α : Type} (destBit aliased : Bool) (dest src : Arr α) : R (Arr α) :=
  if isemptyA src then .ok dest
  else if destBit then copytoBitarray dest src
  else
    let src' := unaliasA aliased src
    copytoUnaliased dest src'

/-- `copyto!(deststyle::IndexStyle, dest, srcstyle::IndexStyle, src)` (lines 1082-1086). -/
def copytoStyles {α : Type} (ds ss : Style) (aliased : Bool) (dest src : Arr α) : R (Arr α) :=
  if isemptyA src then .ok dest
  else
    let src' := unaliasA aliased src
    copytoUnaliasedS ds ss dest src'

/-- `similar(a)` (base/abstractarray.jl:819-834) when every axis of `a` is a `Base.OneTo`:
`similar(a, T, axes(a))` converts the axes with `to_shape` (`last` of each `OneTo`) and
returns `Array{T,N}(undef, dims)`, an `IndexLinear` array with axes `OneTo.(dims)` whose
uninitialized contents are `junk`. For other axes Base defines no method; the array type
must provide its own `similar` (doc/src/manual/interfaces.md, "Abstract arrays"), so the
result is `none`. -/
def similarArr {α : Type} (a : Arr α) (junk : List α) : Option (Arr α) :=
  if a.axes.all (fun r => decide (r.kind = .oneTo)) then
    some ⟨a.axes.map (fun r => oneTo r.hi), .linear, junk⟩
  else none

/-- `copy(a::AbstractArray) = copymutable(a) = copyto!(similar(a), a)`
(base/abstractarray.jl:1154-1157, 1211-1214). -/
def copyA {α : Type} (a : Arr α) (junk : List α) : Option (R (Arr α)) :=
  (similarArr a junk).map (fun s => copytoA false false s a)

end JuliaLean.AbstractArraySpecs
