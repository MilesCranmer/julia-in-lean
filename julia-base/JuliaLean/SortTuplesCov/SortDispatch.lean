import JuliaLean.SortTuplesCov.SortPipeline

/-! Algorithm-selection methods from `base/sort.jl` (master
`bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

/-! ### Generic dispatch components -/

def isUIntMappableDispatch {R : Type} (mappable : Bool) (yes no : R) : R :=
  if mappable then yes else no

structure SmallAlgorithm (R : Type) where
  threshold : Int
  small : R
  big : R

/-- `Small{N}(small,big)` and `Small{N}(big)`, `base/sort.jl:793-794`. -/
def smallExplicit {R : Type} (n : Int) (small big : R) : SmallAlgorithm R := ⟨n, small, big⟩
def smallDefault {R : Type} (n : Int) (defaultSmall big : R) : SmallAlgorithm R :=
  smallExplicit n defaultSmall big

/-- `_sort!(..., a::Small{N}, ...)`, `base/sort.jl:795-802`. -/
def smallDispatch {R : Type} (a : SmallAlgorithm R) (lo hi : Int) : R :=
  if hi - lo < a.threshold then a.small else a.big

inductive CheckSortedRoute where
  | alreadySorted | reversed | next
  deriving DecidableEq

/-- `CheckSorted`, `base/sort.jl:864-879`. -/
def checkSortedDispatch (sorted reverseSorted : Bool) (lo hi : Int) : CheckSortedRoute :=
  if sorted then .alreadySorted
  else if hi - lo ≥ 500 && reverseSorted then .reversed
  else .next

inductive StableCheckRoute where
  | alreadySorted | strictlyReversed | next
  deriving DecidableEq

/-- `StableCheckSorted`, `base/sort.jl:1368-1379`. -/
def stableCheckDispatch (sorted strictlyReverseSorted : Bool) : StableCheckRoute :=
  if sorted then .alreadySorted else if strictlyReverseSorted then .strictlyReversed else .next

structure Extrema (V : Type) where
  min : V
  max : V

/-- The loop of `ComputeExtrema`, `base/sort.jl:893-905`. -/
def computeExtremaLoop {V : Type} (lt : V → V → Bool) (v : Array V) :
    Nat → Nat → Extrema V → Extrema V
  | _, 0, e => e
  | i, fuel + 1, e =>
    match v[i]? with
    | none => e
    | some x => computeExtremaLoop lt v (i + 1) fuel
        ⟨if lt x e.min then x else e.min, if lt e.max x then x else e.max⟩

def computeExtrema {V : Type} (lt : V → V → Bool) (v : Array V) : Option (Extrema V) :=
  match v[0]? with
  | none => none
  | some x => some (computeExtremaLoop lt v 1 (v.size - 1) ⟨x, x⟩)

inductive ExtremaRoute where
  | allEquivalent | next
  deriving DecidableEq

def computeExtremaRoute {V : Type} (lt : V → V → Bool) (e : Extrema V) : ExtremaRoute :=
  if lt e.min e.max then .next else .allEquivalent

structure CountingChoice where
  useCounting : Bool
  threshold : Int

/-- `ConsiderCountingSort`, `base/sort.jl:923-933`, after the source's
wrapping range computation. -/
def considerCounting (elementBytes : Nat) (range span : Int) : CountingChoice :=
  let threshold := if elementBytes > 8 then 5 * span - 100 else span / 2
  ⟨range < threshold, threshold⟩

/-- `maybe_reverse`, `base/sort.jl:946-947`. -/
def maybeReverse {V : Type} (reverse : Bool) (xs : List V) : List V :=
  if reverse then xs.reverse else xs

structure RadixChoice where
  useRadix : Bool

/-- `ConsiderRadixSort`, `base/sort.jl:983-992`, with `scaledLog` equal to
the already evaluated source expression `22log(hi-lo)`. -/
def considerRadix (elementBytes bits scaledLog : Nat) : RadixChoice :=
  ⟨elementBytes ≤ 8 && bits + 70 < scaledLog⟩

def SortDispatchCorrect : Prop :=
  (∀ (R : Type) (yes no : R),
    isUIntMappableDispatch true yes no = yes ∧ isUIntMappableDispatch false yes no = no) ∧
  (∀ (R : Type) n (s b : R), smallExplicit n s b = ⟨n, s, b⟩ ∧
    smallDefault n s b = ⟨n, s, b⟩) ∧
  (∀ (R : Type) (a : SmallAlgorithm R) lo hi,
    smallDispatch a lo hi = if hi - lo < a.threshold then a.small else a.big) ∧
  (∀ rs lo hi, checkSortedDispatch true rs lo hi = .alreadySorted) ∧
  (∀ rs, stableCheckDispatch true rs = .alreadySorted) ∧
  (∀ (V : Type) lt (v : Array V), v.size = 0 → computeExtrema lt v = none) ∧
  (∀ bytes range span, (considerCounting bytes range span).useCounting =
    decide (range < if bytes > 8 then 5 * span - 100 else span / 2)) ∧
  (∀ (V : Type) (xs : List V), maybeReverse false xs = xs ∧
    maybeReverse true xs = xs.reverse) ∧
  (∀ bytes bits log, (considerRadix bytes bits log).useRadix =
    (bytes ≤ 8 && bits + 70 < log))

theorem sortDispatchCorrect : SortDispatchCorrect := by
  refine ⟨by simp [isUIntMappableDispatch], by simp [smallExplicit, smallDefault],
    by simp [smallDispatch], by simp [checkSortedDispatch], by simp [stableCheckDispatch],
    ?_, by simp [considerCounting], by simp [maybeReverse], by simp [considerRadix]⟩
  intro V lt v h
  simp [computeExtrema, Array.size_eq_zero_iff.mp h]

/-! ### Pipeline construction and defaults -/

inductive PipelineStage where
  | subarray | missing | bool_ | small (n : Int) | ieee | uintMappable
  | checkSorted | computeExtrema | considerCounting | considerRadix
  | stableCheckSorted | insertion | scratchQuick
  deriving Repr, DecidableEq

/-- `InitialOptimizations(next)`, `base/sort.jl:1473-1478`. -/
def initialOptimizationStages (next : List PipelineStage) : List PipelineStage :=
  [.subarray, .missing, .bool_, .small 10, .ieee] ++ next

/-- `_DEFAULT_ALGORITHMS_FOR_VECTORS` and the default `_sort!` method,
`base/sort.jl:1580-1593`. -/
def defaultVectorStages : List PipelineStage :=
  initialOptimizationStages [.uintMappable, .small 40, .checkSorted, .computeExtrema,
    .considerCounting, .considerRadix, .small 80, .scratchQuick, .stableCheckSorted,
    .scratchQuick]

def defaultSortDispatch (_stable : Bool) : List PipelineStage := defaultVectorStages

inductive DefaultAlgorithm where
  | stable | unstable
  deriving DecidableEq

inductive ValueClass where
  | numericArray | missingArray | bottomArray | otherArray | other
  deriving DecidableEq

/-- `defalg`, `base/sort.jl:1620-1624`. -/
def defalg : ValueClass → DefaultAlgorithm
  | .numericArray | .missingArray | .bottomArray => .unstable
  | .otherArray | .other => .stable

def InitialPipelineCorrect : Prop :=
  (∀ next, initialOptimizationStages next =
    [.subarray, .missing, .bool_, .small 10, .ieee] ++ next) ∧
  defaultSortDispatch true = defaultVectorStages ∧
  defaultSortDispatch false = defaultVectorStages ∧
  defalg .numericArray = .unstable ∧ defalg .missingArray = .unstable ∧
  defalg .bottomArray = .unstable ∧ defalg .otherArray = .stable ∧ defalg .other = .stable

theorem initialPipelineCorrect : InitialPipelineCorrect := by
  exact ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Algorithm display -/

structure AlgorithmNode where
  typeName : String
  fields : List (String × Option AlgorithmNode)
  depth : Nat

inductive PrintToken where
  | indent (columns : Nat) | typeName (name : String) | openParen | closeParen
  | comma | newline | value (text : String)
  deriving Repr, DecidableEq

/-- `print_tree`, `base/sort.jl:1600-1616`.  Fuel is a structural model
parameter; callers supply more than the nesting depth. -/
def printAlgorithmTree : Nat → AlgorithmNode → Nat → List PrintToken
  | 0, _, _ => []
  | fuel + 1, alg, columns =>
    [.indent columns, .typeName alg.typeName, .openParen] ++
      (alg.fields.zipIdx.flatMap fun (field, i) =>
        (if i > 0 then [.comma] else []) ++
        match field.2 with
        | some child => [.newline] ++ printAlgorithmTree fuel child (columns + 1)
        | none => (if i > 0 then [.value " "] else []) ++ [.value field.1]) ++
      [.closeParen]

/-- `show` calls `print_tree(io, alg, 0)`, `base/sort.jl:1597-1599`. -/
def showAlgorithm (alg : AlgorithmNode) : List PrintToken := printAlgorithmTree (alg.depth + 1) alg 0

/-- `show_type`, `base/sort.jl:1617-1618`. -/
def showAlgorithmType (smallN : Option Int) (name : String) : String :=
  match smallN with
  | none => name
  | some n => "Base.Sort.Small{" ++ toString n ++ "}"

def AlgorithmShowCorrect : Prop :=
  (∀ alg, showAlgorithm alg = printAlgorithmTree (alg.depth + 1) alg 0) ∧
  (∀ name, showAlgorithmType none name = name) ∧
  (∀ n name, showAlgorithmType (some n) name = "Base.Sort.Small{" ++ toString n ++ "}")

theorem algorithmShowCorrect : AlgorithmShowCorrect := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end JuliaLean.SortTuplesCov
