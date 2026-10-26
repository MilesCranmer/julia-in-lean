import JuliaLean.SortTuplesCov.SortWrappers

/-! Executable branch and mutation models for the optimization pipeline in
`base/sort.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

/-! ### SubArray optimization -/

inductive SubarrayRoute where
  | view | parentVector
  deriving DecidableEq

/-- Generic `SubArrayOptimization`, `base/sort.jl:559`. -/
def subarrayOptimization {R : Type} (next : R) : R := next

/-- Unwrappable SubArray method, `base/sort.jl:560-574`. -/
def unwrappableSubarrayOptimization (parentIsArray parentIsVector : Bool)
    (hi lo offset : Int) : SubarrayRoute :=
  if (parentIsArray && !parentIsVector && hi - lo < 100) || offset ≠ 0 then .view
  else .parentVector

def SubarrayOptimizationCorrect : Prop :=
  (∀ (R : Type) (next : R), subarrayOptimization next = next) ∧
  (∀ pa pv hi lo off, ((pa && !pv && decide (hi - lo < 100)) || decide (off ≠ 0)) = true →
    unwrappableSubarrayOptimization pa pv hi lo off = .view) ∧
  (∀ pa pv hi lo off, ((pa && !pv && decide (hi - lo < 100)) || decide (off ≠ 0)) = false →
    unwrappableSubarrayOptimization pa pv hi lo off = .parentVector)

theorem subarrayOptimizationCorrect : SubarrayOptimizationCorrect := by
  refine ⟨by simp [subarrayOptimization], ?_, ?_⟩ <;>
    intro pa pv hi lo off h <;>
    cases pa <;> cases pv <;> simp_all [unwrappableSubarrayOptimization]

/-! ### WithoutMissingVector -/

/-- Constructor, `base/sort.jl:591-596`. `none` represents `missing`. -/
def withoutMissingVector {V : Type} (data : Array (Option V)) (unsafeFlag : Bool := false) :
    Jl (Array (Option V)) :=
  if !unsafeFlag && data.any (fun x => x.isNone) then
    .error (.argumentError "data must not contain missing values")
  else .ok data

/-- `getindex`, `base/sort.jl:598-602`, including its assertion. -/
def withoutMissingGet {V : Type} (data : Array (Option V)) (i : Int) : Jl V :=
  match JuliaLean.Sort.rd data i with
  | some x => .ok x
  | none => .error (.argumentError "encountered missing in WithoutMissingVector")

/-- `setindex!`, `size`, and `axes`, `base/sort.jl:603-608`. -/
def withoutMissingSet {V : Type} (data : Array (Option V)) (x : V) (i : Int) : Array (Option V) :=
  JuliaLean.Sort.wr data i (some x)
def withoutMissingSize {V : Type} (data : Array (Option V)) : Nat := data.size
def withoutMissingAxes {V : Type} (data : Array (Option V)) : Nat × Nat := (1, data.size)

def WithoutMissingVectorCorrect : Prop :=
  (∀ (V : Type) (data : Array (Option V)), data.any (fun x => x.isNone) = true →
    withoutMissingVector data false =
      .error (.argumentError "data must not contain missing values")) ∧
  (∀ (V : Type) (data : Array (Option V)), withoutMissingVector data true = .ok data) ∧
  (∀ (V : Type) (data : Array (Option V)) x i,
    withoutMissingSet data x i = JuliaLean.Sort.wr data i (some x)) ∧
  (∀ (V : Type) (data : Array (Option V)),
    withoutMissingSize data = data.size ∧ withoutMissingAxes data = (1, data.size))

theorem withoutMissingVectorCorrect : WithoutMissingVectorCorrect := by
  refine ⟨?_, by simp [withoutMissingVector], ?_, by simp [withoutMissingSize, withoutMissingAxes]⟩
  · intro V data h
    simp [withoutMissingVector, h]
  · intro V data x i
    rfl

/-! ### send_to_end! -/

section SendToEnd

variable {V : Type} [Inhabited V]

def sendScan (f : V → Bool) (hi : Int) : Nat → Array V → Int → Array V × Int
  | 0, v, i => (v, i)
  | fuel + 1, v, i =>
    if i ≤ hi && !f (JuliaLean.Sort.rd v i) then sendScan f hi fuel v (i + 1) else (v, i)

def sendLoop (f : V → Bool) (hi : Int) : Nat → Array V → Int → Int → Array V × Int
  | 0, v, i, _ => (v, i)
  | fuel + 1, v, i, j =>
    if j ≤ hi then
      if !f (JuliaLean.Sort.rd v j) then
        let a := JuliaLean.Sort.rd v i
        let b := JuliaLean.Sort.rd v j
        sendLoop f hi fuel (JuliaLean.Sort.wr (JuliaLean.Sort.wr v i b) j a) (i + 1) (j + 1)
      else sendLoop f hi fuel v i (j + 1)
    else (v, i)

/-- `send_to_end!(f, v; lo, hi)`, `base/sort.jl:620-634`. -/
def sendToEnd (f : V → Bool) (v : Array V) (lo hi : Int) : Array V × Int :=
  let first := sendScan f hi (hi - lo + 2).toNat v lo
  let out := sendLoop f hi (hi - first.2 + 1).toNat first.1 first.2 (first.2 + 1)
  (out.1, out.2 - 1)

/-- Direct-order wrappers, `base/sort.jl:645-648`, recorded as the exact
choice of direction, predicate complement, and stability flag. -/
inductive SendRoute where
  | forward (complement reverseView : Bool)
  | reverse (complement reverseView : Bool)
  deriving DecidableEq

def sendToEndRoute (reverseOrder endStable : Bool) : SendRoute :=
  if !reverseOrder then
    if endStable then .forward true true else .forward false false
  else if endStable then .reverse true false else .reverse false true

def SendToEndCorrect : Prop :=
  (∀ (V : Type) [Inhabited V] f (v : Array V) lo hi,
    sendToEnd f v lo hi =
      let first := sendScan f hi (hi - lo + 2).toNat v lo
      let out := sendLoop f hi (hi - first.2 + 1).toNat first.1 first.2 (first.2 + 1)
      (out.1, out.2 - 1)) ∧
  sendToEndRoute false false = .forward false false ∧
  sendToEndRoute false true = .forward true true ∧
  sendToEndRoute true false = .reverse false true ∧
  sendToEndRoute true true = .reverse true false

theorem sendToEndCorrect : SendToEndCorrect := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  intro V inst f v lo hi
  rfl

end SendToEnd

/-! ### Missing and IEEE dispatch -/

inductive MissingRoute where
  | direct | permutation | pass
  deriving DecidableEq

/-- Branch conditions of `MissingOptimization`, `base/sort.jl:651-686`. -/
def missingOptimizationRoute (direct hasMissingEltype perm permDirect integerIndices
    dataHasMissing identityIndices : Bool) : MissingRoute :=
  if direct && hasMissingEltype then .direct
  else if perm && permDirect && integerIndices && dataHasMissing && identityIndices then .permutation
  else .pass

def MissingOptimizationCorrect : Prop :=
  (∀ d hm p pd ii dh id,
    d && hm = true → missingOptimizationRoute d hm p pd ii dh id = .direct) ∧
  (∀ p pd ii dh id,
    p && pd && ii && dh && id = true →
      missingOptimizationRoute false false p pd ii dh id = .permutation) ∧
  missingOptimizationRoute false false false false false false false = .pass

theorem missingOptimizationCorrect : MissingOptimizationCorrect := by
  refine ⟨?_, ?_, by decide⟩
  · intro d hm p pd ii dh id h
    cases d <;> cases hm <;> simp_all [missingOptimizationRoute]
  · intro p pd ii dh id h
    cases p <;> cases pd <;> cases ii <;> cases dh <;> cases id <;>
      simp_all [missingOptimizationRoute]

def afterZero (reverse signbit : Bool) : Bool := if reverse then signbit else !signbit
def isConcreteIEEEFloat (isIEEE concrete : Bool) : Bool := isIEEE && concrete

inductive IEEERoute where
  | values | permutation | pass
  deriving DecidableEq

/-- The three branches of `IEEEFloatOptimization`, `base/sort.jl:706-731`. -/
def ieeeOptimizationRoute (valueIEEE direct integerIndices perm permDirect dataIEEE : Bool) : IEEERoute :=
  if valueIEEE && direct then .values
  else if integerIndices && perm && permDirect && dataIEEE then .permutation
  else .pass

def IEEEOptimizationCorrect : Prop :=
  (∀ s, afterZero false s = !s ∧ afterZero true s = s) ∧
  (∀ i c, isConcreteIEEEFloat i c = (i && c)) ∧
  (∀ vi d ii p pd di, vi && d = true →
    ieeeOptimizationRoute vi d ii p pd di = .values) ∧
  (∀ ii p pd di, ii && p && pd && di = true →
    ieeeOptimizationRoute false false ii p pd di = .permutation) ∧
  ieeeOptimizationRoute false false false false false false = .pass

theorem ieeeOptimizationCorrect : IEEEOptimizationCorrect := by
  refine ⟨by intro s; cases s <;> decide, by simp [isConcreteIEEEFloat], ?_, ?_, by decide⟩
  · intro vi d ii p pd di h
    cases vi <;> cases d <;> simp_all [ieeeOptimizationRoute]
  · intro ii p pd di h
    cases ii <;> cases p <;> cases pd <;> cases di <;> simp_all [ieeeOptimizationRoute]

/-! ### Bool optimization -/

def fillBoolRange (v : Array Bool) (lo hi : Int) (x : Bool) : Array Bool :=
  (List.range (hi - lo + 1).toNat).foldl
    (fun out (k : Nat) => JuliaLean.Sort.wr out (lo + (k : Int)) x) v

/-- Specialized Bool sort, `base/sort.jl:746-758`. -/
def boolOptimization (lt : Bool → Bool → Bool) (v : Array Bool) (lo hi : Int) : Array Bool :=
  let first := if lt false true then some false else if lt true false then some true else none
  match first with
  | none => v
  | some x =>
    let count := (List.range (hi - lo + 1).toNat).foldl
      (fun n (k : Nat) => if JuliaLean.Sort.rd v (lo + (k : Int)) = x then n + 1 else n) 0
    fillBoolRange (fillBoolRange v lo (lo + count - 1) x) (lo + count) hi (!x)

def boolOptimizationGeneric {R : Type} (next : R) : R := next

def BoolOptimizationCorrect : Prop :=
  (∀ (R : Type) (next : R), boolOptimizationGeneric next = next) ∧
  (∀ lt v lo hi, boolOptimization lt v lo hi =
    let first := if lt false true then some false else if lt true false then some true else none
    match first with
    | none => v
    | some x =>
      let count := (List.range (hi - lo + 1).toNat).foldl
        (fun n (k : Nat) => if JuliaLean.Sort.rd v (lo + (k : Int)) = x then n + 1 else n) 0
      fillBoolRange (fillBoolRange v lo (lo + count - 1) x) (lo + count) hi (!x)) ∧
  (∀ v lo hi, boolOptimization (fun _ _ => false) v lo hi = v)

theorem boolOptimizationCorrect : BoolOptimizationCorrect := by
  exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, by simp [boolOptimization]⟩

end JuliaLean.SortTuplesCov
