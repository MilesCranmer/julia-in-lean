import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.PermutedDimsFaithfulFinal

open JuliaLean.Registry

inductive Error where
  | type | argument | bounds | operation
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure Wrapper (D : Type) where
  parent : D
  deriving Repr

inductive DimParam where
  | intTuple (values : List Int)
  | other
  deriving Repr

def checkedIndex (values : List α) (index : Int) : Result α :=
  if index < 1 then .error .bounds
  else match values[(index - 1).toNat]? with
    | some value => .ok value
    | none => .error .bounds

def isPermutation (values : List Int) (rank : Nat) : Bool :=
  values.length == rank &&
    (List.range rank).all fun dimension =>
      values.count ((dimension + 1 : Nat) : Int) == 1

def inverseEntries : List Nat → List Int → List Int → Result Bool
  | [], _, _ => .ok true
  | dimension :: dimensions, perm, inverse => do
      let source ← checkedIndex perm ((dimension + 1 : Nat) : Int)
      let restored ← checkedIndex inverse source
      if restored = ((dimension + 1 : Nat) : Int) then
        inverseEntries dimensions perm inverse
      else .ok false

/-- `base/permuteddimsarray.jl:12-17`. The type-parameter checks precede
permutation validation, inverse validation, and storage of `data` by `new`. -/
def m12 (data : D) (rank : Nat) (perm iperm : DimParam) : Result (Wrapper D) := do
  let p ← match perm with
    | .intTuple values => .ok values
    | .other => .error .type
  let inverse ← match iperm with
    | .intTuple values => .ok values
    | .other => .error .type
  if p.length != rank || inverse.length != rank then .error .type
  else if !isPermutation p rank then .error .argument
  else
    let areInverses ← inverseEntries (List.range rank) p inverse
    if !areInverses then .error .argument else .ok ⟨data⟩

def P12 : Prop := ∀ {D : Type} data rank perm iperm,
  m12 (D := D) data rank perm iperm = do
    let p ← match perm with
      | .intTuple values => .ok values
      | .other => .error .type
    let inverse ← match iperm with
      | .intTuple values => .ok values
      | .other => .error .type
    if p.length != rank || inverse.length != rank then .error .type
    else if !isPermutation p rank then .error .argument
    else
      let areInverses ← inverseEntries (List.range rank) p inverse
      if !areInverses then .error .argument else .ok ⟨data⟩

theorem p12 : P12 := by unfold P12 m12; intros; rfl

/-- `base/permuteddimsarray.jl:42-46`. `P` and `IP` stay abstract so tuples,
vectors, BigInt values, and custom Integer iterables all remain in scope. -/
def m42 (length : P → Result Nat) (invperm : P → Result IP)
    (splat : P → Result DimParam) (splatInverse : IP → Result DimParam)
    (data : D) (rank : Nat) (perm : P) : Result (Wrapper D) := do
  let count ← length perm
  if count != rank then .error .argument
  else
    let inverse ← invperm perm
    let p ← splat perm
    let ip ← splatInverse inverse
    m12 data rank p ip

def P42 : Prop := ∀ {P IP D : Type} length invperm splat splatInverse data rank perm,
  m42 (P := P) (IP := IP) (D := D) length invperm splat splatInverse data rank perm = do
    let count ← length perm
    if count != rank then .error .argument
    else
      let inverse ← invperm perm
      let p ← splat perm
      let ip ← splatInverse inverse
      m12 data rank p ip

theorem p42 : P42 := by unfold P42 m42; intros; rfl

/-- `base/permuteddimsarray.jl:70-74`. Both the bounds check and the parent
read can fail; the latter includes in-bounds unassigned elements. -/
def m70 (checkbounds : A → List Int → Result Unit)
    (getindex : P → List Int → Result V) (genperm : List Int → Result (List Int))
    (array : A) (parent : P) (indices : List Int) : Result V := do
  checkbounds array indices
  let parentIndices ← genperm indices
  getindex parent parentIndices

def P70 : Prop := ∀ {A P V : Type} checkbounds getindex genperm array parent indices,
  m70 (A := A) (P := P) (V := V) checkbounds getindex genperm array parent indices = do
    checkbounds array indices
    let parentIndices ← genperm indices
    getindex parent parentIndices

theorem p70 : P70 := by unfold P70 m70; intros; rfl

def genpermValues (input : List α) (perm : List Int) : Result (List α) :=
  perm.mapM (checkedIndex input)

/-- `base/permuteddimsarray.jl:87`. Signed permutation entries preserve the
BoundsError path for zero, negative, and oversized indices. -/
def m87 (input : List α) (perm : List Int) : Result (List α) :=
  genpermValues input perm

def P87 : Prop := ∀ {α : Type} input perm,
  m87 (α := α) input perm = perm.mapM (checkedIndex input)

theorem p87 : P87 := by unfold P87 m87 genpermValues; intros; rfl

structure VectorIteration where
  steps : List (Result Int)

/-- `base/permuteddimsarray.jl:88`. Splatting consumes the abstract vector in
iteration order, preserves iteration failures, builds the tuple, and only then
dispatches to tuple `genperm`. -/
def m88 (input : List α) (perm : VectorIteration) : Result (List α) := do
  let tuple ← perm.steps.mapM id
  genpermValues input tuple

def P88 : Prop := ∀ {α : Type} input perm,
  m88 (α := α) input perm = do
    let tuple ← perm.steps.mapM id
    genpermValues input tuple

theorem p88 : P88 := by unfold P88 m88; intros; rfl

/-- `base/permuteddimsarray.jl:286-291`. The two `axes` calls occur before
dimension validation, followed by inverse construction, wrapping, and copy. -/
def m286 (axesDest : D → Result DA) (axesSrc : S → Result SA)
    (checkdims : DA → SA → P → Result Unit) (invperm : P → Result IP)
    (wrap : D → IP → Result W) (copy : W → S → Result Unit)
    (dest : D) (src : S) (perm : P) : Result D := do
  let destinationAxes ← axesDest dest
  let sourceAxes ← axesSrc src
  checkdims destinationAxes sourceAxes perm
  let inverse ← invperm perm
  let target ← wrap dest inverse
  copy target src
  .ok dest

def P286 : Prop := ∀ {D S DA SA P IP W : Type}
    axesDest axesSrc checkdims invperm wrap copy dest src perm,
  m286 (D := D) (S := S) (DA := DA) (SA := SA) (P := P) (IP := IP) (W := W)
      axesDest axesSrc checkdims invperm wrap copy dest src perm = do
    let destinationAxes ← axesDest dest
    let sourceAxes ← axesSrc src
    checkdims destinationAxes sourceAxes perm
    let inverse ← invperm perm
    let target ← wrap dest inverse
    copy target src
    .ok dest

theorem p286 : P286 := by unfold P286 m286; intros; rfl

def fixedPrefix : List Nat → Nat → Nat
  | [], dimension => dimension
  | value :: values, dimension =>
      if value = dimension + 1 then fixedPrefix values (dimension + 1) else dimension

/-- `base/permuteddimsarray.jl:300-317`. The three Cartesian ranges receive
the actual, distinct axis slices `1:d`, `d+2:d1-1`, and `d1+1:end`. -/
def m300 (rank : S → Nat) (parent : P → D) (copyto : D → S → Result Unit)
    (axes : S → Result (List AX)) (cartesian : List AX → Result R)
    (findDest : Nat → List Nat → Result Nat)
    (kernel : P → S → R → R → R → Nat → Nat → Result Unit)
    (target : P) (src : S) (perm : List Nat) : Result P := do
  let dimension := fixedPrefix perm 0
  if dimension = rank src then copyto (parent target) src
  else
    let sourceAxes ← axes src
    let firstRange ← cartesian (sourceAxes.take dimension)
    let destinationDimension ← findDest (dimension + 1) perm
    let middleRange ← cartesian
      ((sourceAxes.drop (dimension + 1)).take (destinationDimension - dimension - 2))
    let finalRange ← cartesian (sourceAxes.drop destinationDimension)
    kernel target src firstRange middleRange finalRange
      (dimension + 1) destinationDimension
  .ok target

def P300 : Prop := ∀ {S P D AX R : Type}
    rank parent copyto axes cartesian findDest kernel target src perm,
  m300 (S := S) (P := P) (D := D) (AX := AX) (R := R)
      rank parent copyto axes cartesian findDest kernel target src perm = do
    let dimension := fixedPrefix perm 0
    if dimension = rank src then copyto (parent target) src
    else
      let sourceAxes ← axes src
      let firstRange ← cartesian (sourceAxes.take dimension)
      let destinationDimension ← findDest (dimension + 1) perm
      let middleRange ← cartesian
        ((sourceAxes.drop (dimension + 1)).take (destinationDimension - dimension - 2))
      let finalRange ← cartesian (sourceAxes.drop destinationDimension)
      kernel target src firstRange middleRange finalRange
        (dimension + 1) destinationDimension
    .ok target

theorem p300 : P300 := by unfold P300 m300; intros; rfl

def tiles8 (axis : List Int) : List (List Int) :=
  (List.range ((axis.length + 7) / 8)).map fun tile =>
    (axis.drop (tile * 8)).take 8

def tiledKernel (prefixes middle finals : List (List Int))
    (getindex : S → List Int → Result V)
    (setindex : P → List Int → V → Result P)
    (initial : P) (source : S) (permuted sourceAxis : List Int) : Result P :=
  (tiles8 permuted).foldlM (fun afterColumn columnTile =>
    (tiles8 sourceAxis).foldlM (fun afterRow rowTile =>
      finals.foldlM (fun afterFinal finalIndex =>
        middle.foldlM (fun afterMiddle middleIndex =>
          columnTile.foldlM (fun afterColumnIndex columnIndex =>
            rowTile.foldlM (fun afterRowIndex rowIndex =>
              prefixes.foldlM (fun output prefixIndex => do
                let index := prefixIndex ++ [rowIndex] ++ middleIndex ++ [columnIndex] ++ finalIndex
                let value ← getindex source index
                setindex output index value) afterRowIndex) afterColumnIndex) afterMiddle) afterFinal)
          afterRow) afterColumn) initial

/-- `base/permuteddimsarray.jl:319-331`. Axis lookup precedes the exact
`jo`, `io`, `R3`, `R2`, `j`, `i` nesting; the zero-dimensional prefix adds no index. -/
def m319 (axes : S → Nat → Result (List Int))
    (getindex : S → List Int → Result V) (setindex : P → List Int → V → Result P)
    (target : P) (source : S) (middle finals : List (List Int))
    (sourceDimension destinationDimension : Nat) : Result P := do
  let permutedAxis ← axes source destinationDimension
  let sourceAxis ← axes source sourceDimension
  tiledKernel [[]] middle finals getindex setindex target source permutedAxis sourceAxis

def P319 : Prop := ∀ {S P V : Type} axes getindex setindex target source middle finals ds dp,
  m319 (S := S) (P := P) (V := V) axes getindex setindex target source middle finals ds dp = do
    let permutedAxis ← axes source dp
    let sourceAxis ← axes source ds
    tiledKernel [[]] middle finals getindex setindex target source permutedAxis sourceAxis

theorem p319 : P319 := by unfold P319 m319; intros; rfl

/-- `base/permuteddimsarray.jl:333-347`. The general kernel adds the `R1`
loop inside `i`, after the same axis-derived tiling and outer loop order. -/
def m333 (axes : S → Nat → Result (List Int))
    (getindex : S → List Int → Result V) (setindex : P → List Int → V → Result P)
    (target : P) (source : S) (prefixes middle finals : List (List Int))
    (sourceDimension destinationDimension : Nat) : Result P := do
  let permutedAxis ← axes source destinationDimension
  let sourceAxis ← axes source sourceDimension
  tiledKernel prefixes middle finals getindex setindex target source permutedAxis sourceAxis

def P333 : Prop := ∀ {S P V : Type} axes getindex setindex target source prefixes middle finals ds dp,
  m333 (S := S) (P := P) (V := V) axes getindex setindex target source prefixes middle finals ds dp = do
    let permutedAxis ← axes source dp
    let sourceAxis ← axes source ds
    tiledKernel prefixes middle finals getindex setindex target source permutedAxis sourceAxis

theorem p333 : P333 := by unfold P333 m333; intros; rfl

/-- `base/permuteddimsarray.jl:369-375`. IO state is threaded through each
mutation, including `showarg(io, parent, false)` and the conditional eltype. -/
def m369 (printOpen : O → Result O) (showParent : O → P → Bool → Result O)
    (printPermClose : O → Perm → Result O) (printEltypeLabel : O → Result O)
    (showEltype : O → A → Result O) (parent : A → P)
    (output : O) (array : A) (perm : Perm) (toplevel : Bool) : Result O := do
  let output ← printOpen output
  let output ← showParent output (parent array) false
  let output ← printPermClose output perm
  if toplevel then
    let output ← printEltypeLabel output
    showEltype output array
  else .ok output

def P369 : Prop := ∀ {O P Perm A : Type}
    printOpen showParent printPermClose printEltypeLabel showEltype parent output array perm top,
  m369 (O := O) (P := P) (Perm := Perm) (A := A)
      printOpen showParent printPermClose printEltypeLabel showEltype parent output array perm top = do
    let output ← printOpen output
    let output ← showParent output (parent array) false
    let output ← printPermClose output perm
    if top then
      let output ← printEltypeLabel output
      showEltype output array
    else .ok output

theorem p369 : P369 := by unfold P369 m369; intros; rfl

private def entry (line : Nat) (fn statement : String) (prop proof : Lean.Name) : Entry :=
  { id := s!"multidimcov-permuteddims-faithful-{line}"
    juliaFile := "base/permuteddimsarray.jl"
    juliaFns := [fn]
    statement
    source := s!"base/permuteddimsarray.jl:{line}"
    status := .proven
    prop
    thm := some proof }

def entries : List Entry := []

end JuliaLean.MultidimCov.PermutedDimsFaithfulFinal
