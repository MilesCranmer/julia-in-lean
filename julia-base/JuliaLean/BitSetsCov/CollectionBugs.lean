import JuliaLean.BitSetsCov.BitSetFilterProof

/-!
# Refuted collection properties

Small executable models of the six source paths reproduced in Julia. Each
property quantifies over the source method's inputs and each refutation reduces
a concrete counterexample.
-/

namespace JuliaLean.BitSetsCov

namespace Bugs


def insertUnique (x : Nat) (xs : List Nat) : List Nat :=
  if x ∈ xs then xs else xs ++ [x]

def setOf (xs : List Nat) : List Nat := xs.foldl (fun s x => insertUnique x s) []

/-- `_replace!(new, res::AbstractSet, A::AbstractSet, count)`,
`base/set.jl:909-943`, in the `res !== A` branch. -/
def replaceSeparate (f : Nat → Nat) (source result : List Nat) : List Nat :=
  source.foldl (fun result x =>
    let y := f x
    if x = y then result else insertUnique y (result.erase x)) result

def replaceExpected (f : Nat → Nat) (source : List Nat) : List Nat :=
  setOf (source.map f)

/-- `replace(f, s)` must replace every original member simultaneously. -/
def ReplaceGenericSetSpec : Prop :=
  ∀ (f : Nat → Nat) (source : List Nat), source.Nodup →
    setOf (replaceSeparate f source source) = setOf (replaceExpected f source)

theorem replaceGenericSetSpec_refuted : ¬ ReplaceGenericSetSpec := by
  intro h
  have := h (fun x => x + 1) [1, 2] (by decide)
  simp [replaceSeparate, replaceExpected, setOf, insertUnique] at this

inductive RangeOutcome where
  | value (disjoint : Bool)
  | divideError
  deriving DecidableEq

/-- Integer `_overlapping_range_isdisjoint`, `base/abstractset.jl:612-618`:
equal absolute steps compare the minima modulo `step(a)`. -/
def overlappingRangeIsdisjoint (minimumA stepA minimumB stepB : Int) : RangeOutcome :=
  if Int.natAbs stepA = Int.natAbs stepB then
    if stepA = 0 then .divideError
    else .value (decide (minimumA % stepA ≠ minimumB % stepA))
  else .value false

def RangeIsdisjointSpec : Prop :=
  ∀ minimumA stepA minimumB stepB,
    ∃ result, overlappingRangeIsdisjoint minimumA stepA minimumB stepB = .value result

theorem rangeIsdisjointSpec_refuted : ¬ RangeIsdisjointSpec := by
  intro h
  obtain ⟨result, hr⟩ := h 1 0 1 0
  simp [overlappingRangeIsdisjoint] at hr

inductive EqValue where
  | positiveZero
  | negativeZero
  | one
  deriving DecidableEq

/-- Julia `==` identifies signed zeros. -/
def valueEq : EqValue → EqValue → Bool
  | .positiveZero, .negativeZero | .negativeZero, .positiveZero => true
  | x, y => decide (x = y)

/-- Julia `isequal` distinguishes signed zeros. -/
def valueIsequal (x y : EqValue) : Bool := decide (x = y)

def anyEqual (eq : EqValue → EqValue → Bool) (a b : List EqValue) : Bool :=
  a.any (fun x => b.any (eq x))

/-- The generic `isdisjoint` path, `base/abstractset.jl:572-584`: short
vectors scan with `in` (`==`); vectors of at least 70 elements are converted
to `Set` and use `isequal`. -/
def isdisjointThreshold (a b : List EqValue) : Bool :=
  if b.length < 70 then !anyEqual valueEq a b else !anyEqual valueIsequal a b

def IsdisjointSizeIndependent : Prop :=
  ∀ n, isdisjointThreshold [.positiveZero] (.negativeZero :: List.replicate n .one) =
    isdisjointThreshold [.positiveZero] (.negativeZero :: List.replicate (n + 1) .one)

theorem isdisjointSizeIndependent_refuted : ¬ IsdisjointSizeIndependent := by
  intro h
  have := h 68
  simp [isdisjointThreshold, anyEqual, valueEq, valueIsequal] at this

structure IdValue where
  identity : Nat
  value : Nat
  deriving DecidableEq

/-- `allunique(::Union{AbstractSet,AbstractDict}) = true`, `base/set.jl:544`. -/
def alluniqueIdSet (_xs : List IdValue) : Bool := true

def AlluniqueSetSpec : Prop :=
  ∀ xs : List IdValue, (xs.map IdValue.identity).Nodup →
    (alluniqueIdSet xs = true ↔ (xs.map IdValue.value).Nodup)

theorem alluniqueSetSpec_refuted : ¬ AlluniqueSetSpec := by
  intro h
  have := h [⟨1, 7⟩, ⟨2, 7⟩] (by decide)
  simp [alluniqueIdSet] at this

inductive SizehintOutcome where
  | ok
  | methodError
  deriving DecidableEq

/-- `sizehint!(::BitVector, sz::Integer)`, `base/bitarray.jl:798-801`, passes
`_div64(sz + 63)` to `_resize_int!(..., ::Int, ...)` without converting it. -/
def bitSizehint (isMachineInt : Bool) (_n : Nat) : SizehintOutcome :=
  if isMachineInt then .ok else .methodError

def BitSizehintSpec : Prop := ∀ isMachineInt n, bitSizehint isMachineInt n = .ok

theorem bitSizehintSpec_refuted : ¬ BitSizehintSpec := by
  intro h
  have := h false 1
  simp [bitSizehint] at this

inductive ReplaceSingletonOutcome where
  | ok
  | methodError
  deriving DecidableEq

/-- The omitted-count type path of `replace(A, old_new...)`,
`base/set.jl:842-864`: removing a singleton from the element type may make the
temporary set unable to hold the unreplaced members. -/
def replaceSetSingleton (hasUnreplacedValue : Bool) : ReplaceSingletonOutcome :=
  if hasUnreplacedValue then .methodError else .ok

def ReplaceSetSingletonSpec : Prop := ∀ hasUnreplacedValue, replaceSetSingleton hasUnreplacedValue = .ok

theorem replaceSetSingletonSpec_refuted : ¬ ReplaceSetSingletonSpec := by
  intro h
  have := h true
  simp [replaceSetSingleton] at this

end Bugs

abbrev ReplaceGenericSetSpec := Bugs.ReplaceGenericSetSpec
abbrev RangeIsdisjointSpec := Bugs.RangeIsdisjointSpec
abbrev IsdisjointSizeIndependent := Bugs.IsdisjointSizeIndependent
abbrev AlluniqueSetSpec := Bugs.AlluniqueSetSpec
abbrev BitSizehintSpec := Bugs.BitSizehintSpec
abbrev ReplaceSetSingletonSpec := Bugs.ReplaceSetSingletonSpec

theorem replaceGenericSetSpec_refuted : ¬ ReplaceGenericSetSpec := Bugs.replaceGenericSetSpec_refuted
theorem rangeIsdisjointSpec_refuted : ¬ RangeIsdisjointSpec := Bugs.rangeIsdisjointSpec_refuted
theorem isdisjointSizeIndependent_refuted : ¬ IsdisjointSizeIndependent := Bugs.isdisjointSizeIndependent_refuted
theorem alluniqueSetSpec_refuted : ¬ AlluniqueSetSpec := Bugs.alluniqueSetSpec_refuted
theorem bitSizehintSpec_refuted : ¬ BitSizehintSpec := Bugs.bitSizehintSpec_refuted
theorem replaceSetSingletonSpec_refuted : ¬ ReplaceSetSingletonSpec := Bugs.replaceSetSingletonSpec_refuted

end JuliaLean.BitSetsCov
