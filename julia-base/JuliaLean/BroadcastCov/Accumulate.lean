import JuliaLean.Core
import JuliaLean.Reduce.Model
import JuliaLean.MemSafety.G5.Model

/-!
Value and dispatch models for `base/accumulate.jl`. The existing Reduce model
contains the scan loops, while the existing MemSafety model contains the exact
pairwise recursion and access offsets. This file models every wrapper plus the
three mock functions used by `_accumulate_promote_op`.
-/

namespace JuliaLean.BroadcastCov.Accumulate

inductive AccError where
  | argumentError
  | dimensionMismatch
  | emptyIterator
  | undefinedLocal
  deriving Repr, DecidableEq

abbrev R (α : Type) := Except AccError α

/-- `accumulate_pairwise`, lines 38-41, after allocating the output. -/
def accumulatePairwiseWrapper (op : Int → Int → Int) (xs : List Int) : List Int :=
  JuliaLean.Reduce.accumulateVec op id none xs

/-- `cumsum!` at lines 51-52 and `cumprod!` at lines 161-162 delegate to
`accumulate!`. -/
def cumsumBang (xs : List Int) : List Int :=
  JuliaLean.Reduce.accumulateVec (· + ·) id none xs

def cumprodBang (xs : List Int) : List Int :=
  JuliaLean.Reduce.accumulateVec (· * ·) id none xs

/-- `_cumsum!`, lines 59-67. Rounds selects pairwise only in dimension one;
the ordinary style selects the normal accumulator there. Other dimensions copy. -/
inductive ArithmeticKind where
  | rounds
  | unknown
  | other
  deriving Repr, DecidableEq

def cumsumDispatch (kind : ArithmeticKind) (dim : Int) (xs : List Int) : List Int :=
  match kind with
  | .rounds | .unknown =>
      if dim = 1 then accumulatePairwiseWrapper (· + ·) xs else xs
  | .other => if dim = 1 then cumsumBang xs else xs

/-- `cumsum(A; dims)`, lines 116-119, and iterator `cumsum`, line 150. -/
def cumsum (xs : List Int) : List Int := cumsumBang xs

/-- The four public `cumprod` wrappers at lines 172, 196-198 and 230-231. -/
def cumprod (xs : List Int) : List Int := cumprodBang xs

/-- `accumulate(op, xs::Tuple; init)`, lines 296-303. -/
def accumulateTuple (op : Int → Int → Int) (xs : List Int) (init : Option Int) : List Int :=
  JuliaLean.Reduce.accumulateVec op id init xs

/-- `_accumulate1!`, lines 436-452. A dimension past one copies; dimension zero
throws; dimension one stores `v1` and scans the tail. -/
def accumulate1 (op : Int → Int → Int) (v1 : Int) (xs : List Int) (dim : Int) : R (List Int) :=
  if dim ≤ 0 then .error .argumentError
  else if dim > 1 then .ok xs
  else
    match xs with
    | [] => .ok []
    | _ :: rest => .ok (v1 :: JuliaLean.Reduce.accumulateLoop op v1 rest)

inductive KeywordShape where
  | none
  | init
  | unsupported
  deriving Repr, DecidableEq

/-- `accumulate!`, lines 347-356, reduced to its keyword dispatch. -/
def accumulateBangDispatch (keywords : KeywordShape) : R Bool :=
  match keywords with
  | .none => .ok false
  | .init => .ok true
  | .unsupported => .error .argumentError

/-- `accumulate`, lines 281-294. `isVector=false` with no dimension takes the
iterator path before keyword validation, as the Julia source does. -/
inductive AccumulatePath where
  | iterator
  | array (hasInit : Bool)
  deriving Repr, DecidableEq

def accumulateDispatch (isVector : Bool) (dims : Option Int) (keywords : KeywordShape) :
    R AccumulatePath :=
  if dims.isNone && !isVector then .ok .iterator
  else
    match keywords with
    | .none => .ok (.array false)
    | .init => .ok (.array true)
    | .unsupported => .error .argumentError

/-- Nested mock `f`, lines 461-464. -/
def promoteF (op : Int → Int → Int) (xs : List Int) (init : Option Int) : R Int :=
  match xs with
  | [] => .error .emptyIterator
  | x :: _ => .ok (match init with | none => x | some i => op i x)

/-- Nested mock `g`, lines 470-476. `k` is undefined for an empty input. -/
def promoteG (op : Int → Int → Int) (xs : List Int) (r : Int) : R Int :=
  match xs with
  | [] => .error .undefinedLocal
  | x :: rest => .ok (rest.foldl (fun _ val => op r val) (op r x))

/-- Nested mock `h`, lines 481-486. -/
def promoteH (op : Int → Int → Int) (xs : List Int) (r : Int) : Int :=
  xs.foldl op r

/-- `_accumulate_promote_op`, lines 455-491, invokes the three inference passes
in order. The observation records their results on a representative value pass. -/
def promotePasses (op : Int → Int → Int) (xs : List Int) (init : Option Int) :
    R (Int × R Int × Int) := do
  let r ← promoteF op xs init
  pure (r, promoteG op xs r, promoteH op xs r)

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
