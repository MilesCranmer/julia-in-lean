import JuliaLean.base.accumulate
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.Accumulate

def WrapperMethods : Prop :=
  (∀ op xs, accumulatePairwiseWrapper op xs =
    JuliaLean.Reduce.accumulateVec op id none xs) ∧
  (∀ xs, cumsumBang xs = JuliaLean.Reduce.accumulateVec (· + ·) id none xs) ∧
  (∀ xs, cumprodBang xs = JuliaLean.Reduce.accumulateVec (· * ·) id none xs) ∧
  (∀ kind dim xs, cumsumDispatch kind dim xs =
    match kind with
    | .rounds | .unknown => if dim = 1 then accumulatePairwiseWrapper (· + ·) xs else xs
    | .other => if dim = 1 then cumsumBang xs else xs) ∧
  (∀ op xs init, accumulateTuple op xs init =
    JuliaLean.Reduce.accumulateVec op id init xs) ∧
  (∀ xs, cumsum xs = cumsumBang xs) ∧
  (∀ xs, cumprod xs = cumprodBang xs)

theorem wrapperMethods : WrapperMethods := by
  exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

def DispatchAndPromotionMethods : Prop :=
  (∀ op v1 xs dim, accumulate1 op v1 xs dim =
    if dim ≤ 0 then .error .argumentError
    else if dim > 1 then .ok xs
    else match xs with
      | [] => .ok []
      | _ :: rest => .ok (v1 :: JuliaLean.Reduce.accumulateLoop op v1 rest)) ∧
  (∀ keywords, accumulateBangDispatch keywords =
    match keywords with
    | .none => .ok false
    | .init => .ok true
    | .unsupported => .error .argumentError) ∧
  (∀ isVector dims keywords, accumulateDispatch isVector dims keywords =
    if dims.isNone && !isVector then .ok .iterator
    else match keywords with
      | .none => .ok (.array false)
      | .init => .ok (.array true)
      | .unsupported => .error .argumentError) ∧
  (∀ op xs init, promoteF op xs init =
    match xs with
    | [] => .error .emptyIterator
    | x :: _ => .ok (match init with | none => x | some i => op i x)) ∧
  (∀ op xs r, promoteG op xs r =
    match xs with
    | [] => .error .undefinedLocal
    | x :: rest => .ok (rest.foldl (fun _ val => op r val) (op r x))) ∧
  (∀ op xs r, promoteH op xs r = xs.foldl op r) ∧
  (∀ op xs init, promotePasses op xs init = do
    let r ← promoteF op xs init
    pure (r, promoteG op xs r, promoteH op xs r))

theorem dispatchAndPromotionMethods : DispatchAndPromotionMethods := by
  exact ⟨fun _ _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl⟩

end JuliaLean.BroadcastCov.Accumulate

namespace JuliaLean.BroadcastCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [


  { id := "broadcastcov-accumulate-wrappers", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate_pairwise", "cumsum!", "_cumsum!", "cumsum", "cumprod!",
      "cumprod", "accumulate(::Tuple)"]
    statement := "The public cumulative wrappers dispatch to the pairwise or ordinary prefix scan selected in the source and return the corresponding prefix values."
    source := "base/accumulate.jl:38-303; cumsum, cumprod and accumulate docstrings"
    status := .proven, prop := ``Accumulate.WrapperMethods
    thm := some ``Accumulate.wrapperMethods },
  { id := "broadcastcov-accumulate-dispatch-promote", juliaFile := "base/accumulate.jl"
    juliaFns := ["accumulate", "accumulate!", "_accumulate1!", "_accumulate_promote_op", "f", "g", "h"]
    statement := "Accumulation validates keywords in source order, the one-dimensional loop scans or copies according to dims, and the three inference-only mock functions perform their written passes."
    source := "base/accumulate.jl:281-303,347-356,436-491"
    status := .proven, prop := ``Accumulate.DispatchAndPromotionMethods
    thm := some ``Accumulate.dispatchAndPromotionMethods }

]

end JuliaLean.BroadcastCov
