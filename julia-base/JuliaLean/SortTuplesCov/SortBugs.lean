import JuliaLean.Sort

/-!
Small executable models for the seven `base/sort.jl` findings catalogued by
the `SortTuplesCov` area.  Each model keeps the branches responsible for the
observed behaviour; the public Julia reproducers exercise the complete methods.
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean

/-! ### Float-range search overflow -/

/-- The finite values and overflow result needed to model the Float64 execution
of `searchsortedlast(range(-1e308, 1e308, length=3), 9e307)`. -/
inductive F64 where
  | negHuge | zero | nearPosHuge | posHuge | posInf
  deriving DecidableEq

def F64.isFinite : F64 → Bool
  | .posInf => false
  | _ => true

def F64.lt : F64 → F64 → Bool
  | .negHuge, .negHuge => false
  | .negHuge, _ => true
  | .zero, .negHuge | .zero, .zero => false
  | .zero, _ => true
  | .nearPosHuge, .posHuge | .nearPosHuge, .posInf => true
  | .nearPosHuge, _ => false
  | .posHuge, .posInf => true
  | .posHuge, _ => false
  | .posInf, _ => false

/-- Float64 subtraction in the model.  The important IEEE-754 operation is
`9e307 - (-1e308) == Inf`; all other cases used by the method stay finite. -/
def F64.sub : F64 → F64 → F64
  | .nearPosHuge, .negHuge => .posInf
  | a, .zero => a
  | .posHuge, .negHuge => .posInf
  | _, _ => .zero

/-- `(x-f)/h + 1`; an infinite numerator stays infinite. -/
def F64.divAddOne (x h : F64) : F64 :=
  match x, h with
  | .posInf, _ => .posInf
  | _, _ => .nearPosHuge

/-- `round(Integer, x)` throws `InexactError` on infinity. -/
def F64.roundInteger : F64 → Jl Int
  | .posInf => .error (.inexactError "Int64")
  | _ => .ok 2

structure FloatRange where
  first : F64
  step : F64
  last : F64
  length : Nat

/-- `searchsortedlast(a::AbstractRange{<:Real}, x, o)`,
`base/sort.jl:243-254`, for `Forward`. -/
def floatRangeSearchLast (a : FloatRange) (x : F64) : Jl Int :=
  if F64.lt x a.first then .ok 0
  else if a.step = .zero || !F64.lt x a.last then .ok a.length
  else do
    let n ← F64.roundInteger (F64.divAddOne (F64.sub x a.first) a.step)
    pure (if n = 3 then 2 else n)

/-- `searchsortedfirst(a::AbstractRange{<:Real}, x, o)`,
`base/sort.jl:256-267`, for `Forward`. -/
def floatRangeSearchFirst (a : FloatRange) (x : F64) : Jl Int :=
  if !F64.lt a.first x then .ok 1
  else if a.step = .zero || F64.lt a.last x then .ok (a.length + 1)
  else do
    let n ← F64.roundInteger (F64.divAddOne (F64.sub x a.first) a.step)
    pure (if n = 2 then 3 else n)

/-- `searchsorted(a::AbstractRange{<:Real}, x, o)`, `base/sort.jl:301-302`. -/
def floatRangeSearch (a : FloatRange) (x : F64) : Jl (Int × Int) := do
  pure ((← floatRangeSearchFirst a x), (← floatRangeSearchLast a x))

def finiteFloatRange (a : FloatRange) (x : F64) : Prop :=
  a.first.isFinite = true ∧ a.step.isFinite = true ∧ a.last.isFinite = true ∧
    x.isFinite = true ∧ a.length > 0

/-- The optimized range search must return an index rather than throw for a
nonempty range and finite search value, as required by the search docstring. -/
def FloatRangeSearchNoThrow : Prop :=
  ∀ a x, finiteFloatRange a x →
    ∃ first last both, floatRangeSearchFirst a x = .ok first ∧
      floatRangeSearchLast a x = .ok last ∧ floatRangeSearch a x = .ok both

theorem floatRangeSearchNoThrow_refuted : ¬ FloatRangeSearchNoThrow := by
  intro h
  let r : FloatRange := ⟨.negHuge, .posHuge, .posHuge, 3⟩
  obtain ⟨first, last, both, -, hi, -⟩ :=
    h r .nearPosHuge (by simp [r, finiteFloatRange, F64.isFinite])
  change Except.error (JlError.inexactError "Int64") = Except.ok last at hi
  cases hi

/-! ### `insorted` equivalence -/

inductive SortValue where
  | negZero | posZero | one | missing
  deriving DecidableEq

/-- Julia `==` for the values used by the reproducer (`none` is `missing`). -/
def SortValue.eq : SortValue → SortValue → Option Bool
  | .missing, _ | _, .missing => none
  | .negZero, .posZero | .posZero, .negZero => some true
  | a, b => some (a = b)

/-- Julia `isless`: signed zeroes are ordered and `missing` sorts last. -/
def SortValue.lt : SortValue → SortValue → Bool
  | .negZero, .posZero | .negZero, .one | .negZero, .missing => true
  | .posZero, .one | .posZero, .missing => true
  | .one, .missing => true
  | _, _ => false

def orMissing : Option Bool → Option Bool → Option Bool
  | some true, _ | _, some true => some true
  | none, _ | _, none => none
  | _, _ => some false

/-- `in(x, r)` used by `insorted(x, r::AbstractRange)`, `base/sort.jl:466`. -/
def insortedRange (x : SortValue) (r : List SortValue) : Option Bool :=
  r.foldl (fun acc y => orMissing acc (SortValue.eq x y)) (some false)

/-- `!isempty(searchsorted(v, x))`, `base/sort.jl:465`: membership under the
sort-order equivalence `!lt(x,y) && !lt(y,x)`. -/
def insortedVector (x : SortValue) (v : List SortValue) : Bool :=
  v.any fun y => !SortValue.lt x y && !SortValue.lt y x

def InsortedRangeAgrees : Prop :=
  ∀ x r, insortedRange x r = some (insortedVector x r)

theorem insortedRangeAgrees_refuted : ¬ InsortedRangeAgrees := by
  intro h
  have hne : insortedRange .negZero [.posZero, .one] ≠
      some (insortedVector .negZero [.posZero, .one]) := by decide
  exact hne (h .negZero [.posZero, .one])

/-! ### Legacy six-argument sort -/

inductive LegacyAlg where
  | quick | merge | partialQuick | custom
  deriving DecidableEq

/-- `_sort!(v, a::Algorithm, o, kw)`, `base/sort.jl:2586-2595`. -/
def legacySortFallback (a legacyEntry : LegacyAlg) : Jl Unit :=
  if legacyEntry = a then
    .error (.argumentError "Base.Sort._sort! is not defined")
  else .ok ()

/-- The six-argument `sort!(..., scratch::Vector)`, `base/sort.jl:2578-2582`:
after a bounds check it enters `_sort!` with `legacy_dispatch_entry=a`. -/
def legacySortWithScratch (length lo hi : Int) (a : LegacyAlg) : Jl Unit :=
  if 1 ≤ lo ∧ hi ≤ length then legacySortFallback a a else .error .boundsError

/-- Supported old five-argument methods, `base/sort.jl:2454-2457,2482-2486,
2533-2537`. -/
def legacySortWithoutScratch (length lo hi : Int) (a : LegacyAlg) : Jl Unit :=
  if 1 ≤ lo ∧ hi ≤ length then
    match a with
    | .quick | .merge | .partialQuick => .ok ()
    | .custom => legacySortFallback a a
  else .error .boundsError

/-- Supplying an accepted scratch vector must not make a supported legacy sort
entry throw on a valid window. -/
def LegacySortScratch : Prop :=
  ∀ (n lo hi : Int) (a : LegacyAlg), 1 ≤ lo → hi ≤ n →
    legacySortWithoutScratch n lo hi a = .ok () →
    legacySortWithScratch n lo hi a = .ok ()

theorem legacySortScratch_refuted : ¬ LegacySortScratch := by
  intro h
  have hne : legacySortWithScratch 5 2 4 .quick ≠ .ok () := by
    simp [legacySortWithScratch, legacySortFallback]
  exact hne (h 5 2 4 .quick (by decide) (by decide)
    (by simp [legacySortWithoutScratch]))

/-! ### Descending `PartialQuickSort` target -/

inductive PartialAction where
  | skipLower | skipUpper | recurseLower | recurseUpper
  deriving DecidableEq

/-- The branch after `partition!` in `_partialquicksort!`,
`base/sort.jl:2546-2562`. -/
def partialQuickAction (lo hi firstTarget lastTarget pivot : Int) : PartialAction :=
  if pivot ≤ firstTarget then .skipLower
  else if pivot ≥ lastTarget then .skipUpper
  else if pivot - lo < hi - pivot then .recurseLower
  else .recurseUpper

def targetIndices (first step : Int) (length : Nat) : List Int :=
  (List.range length).map fun (i : Nat) => first + (i : Int) * step

/-- A partial quicksort branch must not discard a side containing a requested
target position.  This is the local invariant required by the
`PartialQuickSort(k)` docstring. -/
def PartialQuickSortCorrect : Prop :=
  ∀ (lo hi firstTarget lastTarget : Int) (targets : List Int) (pivot : Int),
    targets.getLast? = some lastTarget →
    lo ≤ pivot → pivot ≤ hi →
    (targets.any fun k => k < pivot) →
    (targets.any fun k => pivot < k) →
    partialQuickAction lo hi firstTarget lastTarget pivot ≠ .skipLower ∧
      partialQuickAction lo hi firstTarget lastTarget pivot ≠ .skipUpper

theorem partialQuickSortCorrect_refuted : ¬ PartialQuickSortCorrect := by
  intro h
  have := h 1 22 5 3 [5, 4, 3] 4 (by simp) (by decide) (by decide)
    (by decide) (by decide)
  exact this.1 (by simp [partialQuickAction])

/-! ### Tuple algorithm dispatch -/

inductive TupleAlg where
  | defaultStable | defaultUnstable | insertion | quick | merge | partialQuick
  deriving DecidableEq

/-- `_sort(x::NTuple, a, o, kw)`, `base/sort.jl:1798-1808`: only the two
default algorithm tags have a method. -/
def sortTupleDispatch (a : TupleAlg) : Jl Unit :=
  match a with
  | .defaultStable | .defaultUnstable => .ok ()
  | _ => .error (.methodError "Base.Sort._sort")

/-- `sort(x::NTuple; alg=...)`, `base/sort.jl:1785-1795`, promises a sorted
tuple for each built-in `Algorithm` accepted by its signature. -/
def SortNTupleAlgs : Prop := ∀ a : TupleAlg, ∃ r, sortTupleDispatch a = .ok r

theorem sortNTupleAlgs_refuted : ¬ SortNTupleAlgs := by
  intro h
  obtain ⟨r, hr⟩ := h .quick
  simp [sortTupleDispatch] at hr

/-! ### `dims` default evaluation order -/

/-- `size(A, dims)` for a two-dimensional array, including its exception at
dimension zero. -/
def matrixSize (dims : Int) : Jl Nat :=
  if dims < 1 then .error .boundsError
  else if dims ≤ 2 then .ok 2 else .ok 1

/-- `sort!(A; dims, scratch=<default>)`, `base/sort.jl:2187-2223`.  Julia
evaluates the scratch default's `size(A,dims)` before the body's explicit
dimension check. -/
def sortDimsDefault (nd dims : Int) : Jl Unit := do
  let n ← matrixSize dims
  let _scratchAllocated := !(n < 10)
  if 1 ≤ dims ∧ dims ≤ nd then .ok ()
  else .error (.argumentError "dimension out of range")

def SortDimsChecked : Prop :=
  ∀ nd dims, (dims < 1 ∨ nd < dims) →
    sortDimsDefault nd dims = .error (.argumentError "dimension out of range")

theorem sortDimsChecked_refuted : ¬ SortDimsChecked := by
  intro h
  have hne : sortDimsDefault 2 0 ≠ .error (.argumentError "dimension out of range") := by
    intro hbad
    change Except.error JlError.boundsError =
      Except.error (JlError.argumentError "dimension out of range") at hbad
    cases hbad
  exact hne (h 2 0 (by decide))

/-! ### Missing values and caller-provided scratch -/

inductive ScratchEltype where
  | int32 | missingOrInt32
  deriving DecidableEq

/-- `make_scratch(scratch::Vector, T, len)`, `base/sort.jl:511-516`: a scratch
whose element type differs from `T` is reinterpreted, which requires both
element types to be bitstypes. -/
def makeScratch (scratchType targetType : ScratchEltype) : Jl Unit :=
  if scratchType = targetType then .ok ()
  else match scratchType, targetType with
    | .int32, .int32 => .ok ()
    | _, _ => .error (.argumentError "cannot reinterpret")

/-- `MissingOptimization` keeps the caller scratch while changing the view's
element type to the non-missing type, and `RadixSort` passes both to
`make_scratch`, `base/sort.jl:651-655,1017-1046`. -/
def sortMissingWithScratch (scratchType : ScratchEltype) : Jl Unit :=
  makeScratch scratchType .int32

/-- The keyword signature accepts `Vector{eltype(v)}` as scratch, so the sort
must succeed for a valid `Vector{Union{Missing,Int32}}` input. -/
def SortScratchAccepted : Prop :=
  ∀ scratchType, scratchType = .missingOrInt32 →
    sortMissingWithScratch scratchType = .ok ()

theorem sortScratchAccepted_refuted : ¬ SortScratchAccepted := by
  intro h
  have hne : sortMissingWithScratch .missingOrInt32 ≠ .ok () := by
    simp [sortMissingWithScratch, makeScratch]
  exact hne (h .missingOrInt32 rfl)

end JuliaLean.SortTuplesCov
