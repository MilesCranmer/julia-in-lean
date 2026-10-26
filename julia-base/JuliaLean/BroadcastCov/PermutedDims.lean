import JuliaLean.Core

/-!
List model of `base/permuteddimsarray.jl`. Dimension numbers are one-based,
as in Julia. The model records the parent index used by reads and writes, plus
the shape, axes and stride projections used by the forwarding methods.
-/

namespace JuliaLean.BroadcastCov.PermutedDims

inductive PermError where
  | errorException
  | argumentError
  | boundsError
  | pointerUnsupported
  deriving Repr, DecidableEq

abbrev R (α : Type) := Except PermError α

/-- `genperm`, lines 87-88. -/
def genperm {α : Type} [Inhabited α] (xs : List α) (perm : List Int) : List α :=
  perm.map (fun d => xs.getD (d - 1).toNat default)

def oneTo (n : Nat) : List Int := (List.range n).map (fun (i : Nat) => (i : Int) + 1)

def validPerm (n : Nat) (perm : List Int) : Bool :=
  perm.length == n && (oneTo n).all perm.contains

def inversePerm (perm : List Int) : List Int :=
  (oneTo perm.length).map fun d =>
    match perm.findIdx? (· == d) with
    | some i => (i : Int) + 1
    | none => 0

/-- Inner constructor at lines 12-17. `typed` represents both tuple type checks. -/
def innerConstructor (n : Nat) (typed : Bool) (perm iperm : List Int) : R Unit :=
  if !typed then .error .errorException
  else if !validPerm n perm then .error .argumentError
  else if !(oneTo n).all (fun d => iperm.getD (perm.getD (d - 1).toNat 0 - 1).toNat 0 == d) then
    .error .argumentError
  else .ok ()

/-- Public constructor at lines 42-46. -/
def publicConstructor (n : Nat) (perm : List Int) : R (List Int × List Int) :=
  if perm.length != n then .error .argumentError
  else
    let iperm := inversePerm perm
    match innerConstructor n true perm iperm with
    | .ok _ => .ok (perm, iperm)
    | .error e => .error e

/-- Parent, size, axes, strides, dataids, cconvert and elsize forwarding methods,
lines 48-55 and 64-68. -/
def parent {α : Type} (x : α) : α := x
def permutedSize (size perm : List Int) : List Int := genperm size perm
def permutedAxes (axes : List (List Int)) (perm : List Int) : List (List Int) :=
  perm.map (fun d => axes.getD (d - 1).toNat [])
def hasOffsetAxes (parentHasOffset : Bool) : Bool := parentHasOffset
def similarDims (dims : List Int) : List Int := dims
def dataids (ids : List Nat) : List Nat := ids
def cconvert (pointer : Nat) : Nat := pointer
def permutedStrides (strides perm : List Int) : List Int := genperm strides perm
def elsize (parentElsize : Nat) : Nat := parentElsize

/-- `unaliascopy` at line 54 retains both type permutations and copies the parent. -/
def unaliascopy (parentCopy : List Int) : List Int := parentCopy

/-- `pointer(A, i)`, line 62. -/
def pointerAt (_ : Int) : R Nat := .error .pointerUnsupported

/-- `getindex`, lines 70-74: bounds-check the view, then permute with `iperm`. -/
def getindex (inBounds : Bool) (iperm index : List Int) : R (List Int) :=
  if inBounds then .ok (genperm index iperm) else .error .boundsError

/-- `setindex!`, lines 75-79. The returned pair is the parent index and Julia's
returned value. -/
def setindex (inBounds : Bool) (iperm index : List Int) (value : Int) :
    R (List Int × Int) :=
  if inBounds then .ok (genperm index iperm, value) else .error .boundsError

/-- `isassigned`, lines 81-85. -/
def isassigned (inBounds parentAssigned : Bool) : Bool :=
  if inBounds then parentAssigned else false

/-- `permutedims(A, perm)`, lines 198-201, at the axes level. -/
def permutedimsAxes (axes : List (List Int)) (perm : List Int) : List (List Int) :=
  genperm axes perm

/-- Matrix and vector convenience overloads at lines 203 and 273. -/
def permutedimsMatrix (axes : List (List Int)) : List (List Int) := genperm axes [2, 1]
def permutedimsVectorShape (length : Nat) : List Nat := [1, length]

/-- `permutedims!`, lines 286-291, returns the destination after checking the
permuted axes. -/
def permutedimsBang (destAxes srcAxes : List (List Int)) (perm : List Int) : R Unit :=
  if destAxes == genperm srcAxes perm then .ok () else .error .argumentError

/-- `copyto!`, lines 293-298. -/
def copytoPermuted (sourceEmpty axesFit : Bool) : R Unit :=
  if sourceEmpty then .ok () else if axesFit then .ok () else .error .boundsError

/-- `_copy!`, lines 300-317: count the unpermuted prefix and select direct copy
or the tiled kernel. -/
def firstMovedDim (perm : List Int) : Nat :=
  let rec go : List Int → Nat → Nat
    | [], d => d
    | p :: ps, d => if p == (d : Int) + 1 then go ps (d + 1) else d
  go perm 0

inductive CopyPath where
  | direct
  | tiled (sourceDim destinationDim : Nat)
  deriving Repr, DecidableEq

def copyPath (perm : List Int) : CopyPath :=
  let d := firstMovedDim perm
  if d == perm.length then .direct
  else
    let destination := (perm.findIdx? (· == (d : Int) + 1)).getD 0
    .tiled (d + 1) (destination + 1)

/-- Both `_mapreduce_dim` overloads at lines 351-356 forward to the parent. -/
def mapreduceDim (parentValues : List Int) : List Int := parentValues

/-- Both `mapreducedim!` overloads at lines 358-367 return `B` after reducing
through its inverse-permutation view. -/
def mapreduceDimBang (destination : List Int) : List Int := destination

/-- Observable pieces printed by `showarg`, lines 369-375. -/
def showargParts (perm : List Int) (toplevel : Bool) : List String :=
  ["PermutedDimsArray(", toString perm, ")"] ++
    if toplevel then [" with eltype"] else []

def ConstructorAndIndexMethods : Prop :=
  (∀ n typed perm iperm,
    innerConstructor n typed perm iperm =
      if !typed then .error .errorException
      else if !validPerm n perm then .error .argumentError
      else if !(oneTo n).all (fun d =>
          iperm.getD (perm.getD (d - 1).toNat 0 - 1).toNat 0 == d) then
        .error .argumentError
      else .ok ()) ∧
  (∀ n perm,
    publicConstructor n perm =
      if perm.length != n then .error .argumentError
      else
        let iperm := inversePerm perm
        match innerConstructor n true perm iperm with
        | .ok _ => .ok (perm, iperm)
        | .error e => .error e) ∧
  (∀ inBounds iperm index, getindex inBounds iperm index =
    if inBounds then .ok (genperm index iperm) else .error .boundsError) ∧
  (∀ inBounds iperm index value, setindex inBounds iperm index value =
    if inBounds then .ok (genperm index iperm, value) else .error .boundsError) ∧
  (∀ inBounds assigned, isassigned inBounds assigned = if inBounds then assigned else false)

theorem constructorAndIndexMethods : ConstructorAndIndexMethods := by
  exact ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩

def ProjectionMethods : Prop :=
  (∀ x : Int, parent x = x) ∧
  (∀ size perm, permutedSize size perm = genperm size perm) ∧
  (∀ axes perm, permutedAxes axes perm = perm.map (fun d => axes.getD (d - 1).toNat [])) ∧
  (∀ b, hasOffsetAxes b = b) ∧
  (∀ dims, similarDims dims = dims) ∧
  (∀ ids, dataids ids = ids) ∧
  (∀ p, cconvert p = p) ∧
  (∀ strides perm, permutedStrides strides perm = genperm strides perm) ∧
  (∀ n, elsize n = n) ∧
  (∀ xs, unaliascopy xs = xs) ∧
  (∀ i, pointerAt i = .error .pointerUnsupported)

theorem projectionMethods : ProjectionMethods := by
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl⟩

def CopyAndReductionMethods : Prop :=
  (∀ axes perm, permutedimsAxes axes perm = genperm axes perm) ∧
  (∀ axes, permutedimsMatrix axes = genperm axes [2, 1]) ∧
  (∀ n, permutedimsVectorShape n = [1, n]) ∧
  (∀ dest src perm, permutedimsBang dest src perm =
    if dest == genperm src perm then .ok () else .error .argumentError) ∧
  (∀ empty fit, copytoPermuted empty fit =
    if empty then .ok () else if fit then .ok () else .error .boundsError) ∧
  (∀ perm, copyPath perm =
    let d := firstMovedDim perm
    if d == perm.length then .direct
    else .tiled (d + 1) ((perm.findIdx? (· == (d : Int) + 1)).getD 0 + 1)) ∧
  (∀ xs, mapreduceDim xs = xs) ∧
  (∀ xs, mapreduceDimBang xs = xs) ∧
  (∀ perm top, showargParts perm top =
    ["PermutedDimsArray(", toString perm, ")"] ++
      if top then [" with eltype"] else [])

theorem copyAndReductionMethods : CopyAndReductionMethods := by
  exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end JuliaLean.BroadcastCov.PermutedDims
