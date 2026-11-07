import JuliaLean.base.broadcast
import JuliaLean.base.multidimensional

/-! Properties of broadcast assignment between aliasing views, and their refutations. -/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- `dest .= src` computed into a fresh array first (`dest .= copy(src)`). -/
def freshAssign (dims : List Nat) (mem : List Int) (I J : List Idx) : List Int :=
  let dpos := (positions I).map (linIdx dims)
  let spos := (positions J).map (linIdx dims)
  (dpos.zip spos).foldl (fun m (p : Nat × Nat) => m.set p.1 (mem.getD p.2 0)) mem

/-- `dest .= dest .+ c` with the right-hand side computed into a fresh array first, as
`P[I...] .+= c` (which reads `P[I...]`, a copy) does. -/
def freshSelfAdd (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int) : List Int :=
  let dpos := (positions I).map (linIdx dims)
  dpos.foldl (fun m p => m.set p (mem.getD p 0 + c)) mem

/-- Every subscript tuple lies inside a parent of size `dims`. -/
abbrev InBounds (dims : List Nat) (ps : List (List Int)) : Prop :=
  ps.all (fun p => p.length == dims.length && (p.zip dims).all (fun q => 1 ≤ q.1 && q.1 ≤ (q.2 : Int))) = true

/-- `dest .= src` for two views of the same parent with the same number of elements equals
assigning a fresh copy of `src`, whenever `dest` does not select a parent element twice. -/
def AliasAssignFresh : Prop :=
  ∀ (dims : List Nat) (mem : List Int) (I J : List Idx),
    mem.length = dims.foldr (· * ·) 1 →
    InBounds dims (positions I) → InBounds dims (positions J) →
    (positions I).length = (positions J).length →
    ((positions I).map (linIdx dims)).Nodup →
    bcAssign dims mem I J = .ok (freshAssign dims mem I J)

/-- `dest .= dest .+ c` for a view `dest` equals computing `dest .+ c` into a fresh array and then
assigning it, as `P[I...] .+= c` does. -/
def SelfAssignFresh : Prop :=
  ∀ (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int),
    mem.length = dims.foldr (· * ·) 1 → InBounds dims (positions I) →
    bcSelfAdd dims mem I c = freshSelfAdd dims mem I c

/-- `M = [1 2 3; 4 5 6; 7 8 9]`; `@views M[1, :] .= M[[CartesianIndex(3,3), CartesianIndex(2,2),
CartesianIndex(1,1)]]` writes row `[9, 5, 9]` (column-major memory below), while assigning a copy
writes `[9, 5, 1]`: `_indicesmightoverlap((1, 1:3), (cartesian array,))` tests `1 in [CartesianIndex…]`,
which is false. -/
theorem cartesianAlias_example :
    indicesMightOverlap [.scalar 1, .urange 1 3] [.carts 2 [[3, 3], [2, 2], [1, 1]]] = .ok false ∧
    bcAssign [3, 3] [1, 4, 7, 2, 5, 8, 3, 6, 9] [.scalar 1, .urange 1 3] [.carts 2 [[3, 3], [2, 2], [1, 1]]] =
      .ok [9, 4, 7, 5, 5, 8, 9, 6, 9] ∧
    freshAssign [3, 3] [1, 4, 7, 2, 5, 8, 3, 6, 9] [.scalar 1, .urange 1 3] [.carts 2 [[3, 3], [2, 2], [1, 1]]] =
      [9, 4, 7, 5, 5, 8, 1, 6, 9] := by
  decide

theorem aliasAssignFresh_refuted : ¬ AliasAssignFresh := by
  intro h
  have := h [3, 3] [1, 4, 7, 2, 5, 8, 3, 6, 9] [.scalar 1, .urange 1 3] [.carts 2 [[3, 3], [2, 2], [1, 1]]]
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [cartesianAlias_example.2.1, cartesianAlias_example.2.2] at this
  exact absurd this (by decide)

/-- `x = [10, 20, 30]; @views x[[1, 1, 2]] .+= 1` gives `[12, 21, 30]`; `x[[1, 1, 2]] .+= 1` gives
`[11, 21, 30]`. -/
theorem selfAssign_example :
    bcSelfAdd [3] [10, 20, 30] [.ints [1, 1, 2]] 1 = [12, 21, 30] ∧
    freshSelfAdd [3] [10, 20, 30] [.ints [1, 1, 2]] 1 = [11, 21, 30] := by
  decide

theorem selfAssignFresh_refuted : ¬ SelfAssignFresh := by
  intro h
  have := h [3] [10, 20, 30] [.ints [1, 1, 2]] 1 (by decide) (by decide)
  rw [selfAssign_example.1, selfAssign_example.2] at this
  exact absurd this (by decide)

end JuliaLean.BroadcastViews
