import JuliaLean.ReduceCov.Basic

namespace JuliaLean.ReduceCov.Dims

/-- `_check_valid_region`, `base/reducedim.jl:30-35`, for one integer
dimension. The source converts to `Int` before comparing with one. -/
def checkValidRegion (d : Int) : RJ Unit :=
  match JInt.convert .i64 d with
  | .error _ => .error (.jl (.inexactError "convert"))
  | .ok i => if i.val < 1 then .error (argErr s!"region dimension(s) must be ≥ 1, got {d}") else .ok ()

/-- Every integer dimension at least one is valid, including trailing dimensions
larger than `typemax(Int)`. -/
def ValidRegionUnsigned : Prop := ∀ d : Int, 1 ≤ d → checkValidRegion d = .ok ()

theorem validRegionUnsigned_refuted : ¬ ValidRegionUnsigned := by
  intro h
  have counterexample := h (2 ^ 63) (by omega)
  revert counterexample
  decide

/-- The effective scalar behavior of `findmax!` at `base/reducedim.jl:1164-1167`:
`rind` is filled with zero, so the first input replaces `rval` even with
`init=false`; the remaining inputs are compared normally. -/
def findMaxInplace (_init : Bool) (old : Int) : List Int → Int
  | [] => old
  | x :: xs => xs.foldl max x

/-- The symmetric `findmin!` wrapper, `base/reducedim.jl:1091-1094`. -/
def findMinInplace (_init : Bool) (old : Int) : List Int → Int
  | [] => old
  | x :: xs => xs.foldl min x

/-- `init=false` should combine the input with the value already stored in
`rval`, as the other in-place reductions do. -/
def FindInplaceInit : Prop :=
  (∀ old xs, findMaxInplace false old xs = xs.foldl max old) ∧
  (∀ old xs, findMinInplace false old xs = xs.foldl min old)

theorem findInplaceInit_refuted : ¬ FindInplaceInit := by
  intro h
  have counterexample := h.1 100 [1, 2]
  revert counterexample
  decide

/-- `initarray!` for min, max and extrema, `base/reducedim.jl:45-46`, calls
`mapfirst!`; its first-slice read throws `BoundsError` for an empty reduced axis. -/
def initExtremaInplace (init : Bool) (src : List Int) : RJ Unit :=
  if !init then .ok ()
  else match src with
    | [] => .error boundsErr
    | _ :: _ => .ok ()

/-- `mapfirst!` as reached by extrema initialization, `base/reducedim.jl:241-245`. -/
def mapfirstForInit (src : List Int) : RJ Unit := initExtremaInplace true src

/-- The generated in-place min/max/extrema wrapper, `base/reducedim.jl:1020-1021`. -/
def inplaceExtrema (init : Bool) (src : List Int) : RJ Unit :=
  if init then mapfirstForInit src else .ok ()

/-- In-place min, max and extrema use the same empty-reduction `ArgumentError`
as their allocating forms. -/
def InplaceEmptyError : Prop :=
  ∀ _ : Unit,
    initExtremaInplace true [] = .error (argErr "reducing over an empty collection is not allowed") ∧
    mapfirstForInit [] = .error (argErr "reducing over an empty collection is not allowed") ∧
    inplaceExtrema true [] = .error (argErr "reducing over an empty collection is not allowed")

theorem inplaceEmptyError_refuted : ¬ InplaceEmptyError := by
  intro h
  have counterexample := h ()
  simp [initExtremaInplace, mapfirstForInit, inplaceExtrema, boundsErr, argErr] at counterexample

end JuliaLean.ReduceCov.Dims
