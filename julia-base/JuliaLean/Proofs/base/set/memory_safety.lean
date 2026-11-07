import JuliaLean.Proofs.base.abstractarray.memory_safety_access

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

def uniqueAccesses (capacity : Nat) : Nat → Nat → List Bool → List Access
  | _, _, [] => []
  | current, i, fresh :: rest =>
      at0 capacity i ::
        if fresh then at0 capacity (current + 1) :: uniqueAccesses capacity (current + 1) (i + 1) rest
        else uniqueAccesses capacity current (i + 1) rest

private theorem uniqueAccesses_safe (capacity current i : Nat) (fresh : List Bool)
    (hc : current < i) (hi : i + fresh.length ≤ capacity) :
    accessesSafe (uniqueAccesses capacity current i fresh) := by
  induction fresh generalizing current i with
  | nil => simp [uniqueAccesses, accessesSafe]
  | cons b rest ih =>
      cases b with
      | false =>
          simp only [uniqueAccesses, Bool.false_eq_true, ↓reduceIte, accessesSafe,
            List.mem_cons, forall_eq_or_imp]
          constructor
          · simp [Access.safe, at0]
            simp only [List.length_cons] at hi
            omega
          · apply ih <;> simp only [List.length_cons] at hi ⊢ <;> omega
      | true =>
          simp only [uniqueAccesses, ↓reduceIte, accessesSafe, List.mem_cons,
            forall_eq_or_imp]
          refine ⟨?_, ?_, ?_⟩
          · simp [Access.safe, at0]
            simp only [List.length_cons] at hi
            omega
          · simp [Access.safe, at0]
            simp only [List.length_cons] at hi
            omega
          · apply ih <;> simp only [List.length_cons] at hi ⊢ <;> omega

/-- `unique!`, `base/set.jl:373-405`: the first input is read at `firstindex`,
then `i` advances every iteration while `current` advances only for a fresh
value. -/
def uniqueTrace (fresh : List Bool) : List Access :=
  if fresh = [] then []
  else at0 (fresh.length + 1) 0 :: uniqueAccesses (fresh.length + 1) 0 1 fresh

def UniqueInBounds : Prop := ∀ fresh, accessesSafe (uniqueTrace fresh)

theorem uniqueInBounds_proven : UniqueInBounds := by
  intro fresh
  by_cases h : fresh = []
  · simp [uniqueTrace, h, accessesSafe]
  · simp only [uniqueTrace, h, ↓reduceIte, accessesSafe, List.mem_cons, forall_eq_or_imp]
    constructor
    · simp [Access.safe, at0]
    · apply uniqueAccesses_safe <;> omega

/-- `_indexed_allunique`, `base/set.jl:579-592`, compares each position only
with later indices from the same `eachindex` iterator. -/
def indexedAlluniqueAccesses (length : Nat) : List Access :=
  (List.range length).flatMap fun i =>
    at0 length i :: (List.range (length - i - 1)).map fun k => at0 length (i + k + 1)

def IndexedAlluniqueInBounds : Prop :=
  ∀ length, accessesSafe (indexedAlluniqueAccesses length)

theorem indexedAlluniqueInBounds_proven : IndexedAlluniqueInBounds := by
  intro length a ha
  simp only [indexedAlluniqueAccesses, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_map] at ha
  obtain ⟨i, hi, rfl | ⟨k, hk, rfl⟩⟩ := ha
  · simp [Access.safe, at0]
    omega
  · simp [Access.safe, at0]
    omega

def SetUniqueInBounds : Prop := UniqueInBounds ∧ IndexedAlluniqueInBounds

theorem setUniqueInBounds_proven : SetUniqueInBounds :=
  ⟨uniqueInBounds_proven, indexedAlluniqueInBounds_proven⟩

private def firstLive : List Bool → Nat → Option Nat
  | [], _ => none
  | live :: rest, k => if live then some k else firstLive rest (k + 1)

private theorem firstLive_lt (slots : List Bool) (base k : Nat)
    (h : firstLive slots base = some k) : k < base + slots.length := by
  induction slots generalizing base with
  | nil => simp [firstLive] at h
  | cons live rest ih =>
      simp only [firstLive] at h
      split at h
      · simp_all
      · have := ih (base + 1) h
        simp only [List.length_cons]
        omega

/-- `pop!(::Set)`, `base/set.jl:139-157`.  `ht_keyindex` is represented by a
search over the Dict slot array and therefore can return only an existing slot. -/
def setPopAccesses (slots : List Bool) : List Access :=
  match firstLive slots 0 with
  | none => []
  | some i => [at0 slots.length i]

def SetPopInBounds : Prop := ∀ slots, accessesSafe (setPopAccesses slots)

theorem setPopInBounds_proven : SetPopInBounds := by
  intro slots
  unfold setPopAccesses
  split
  · simp [accessesSafe]
  · rename_i i h
    simp only [accessesSafe, List.mem_singleton, forall_eq, Access.safe, at0]
    have := firstLive_lt slots 0 i h
    omega

/-- Array `replace` and `replace!`, `base/set.jl:804-896,947-976`.  The public
paths pass either `A` itself or `_similar_or_copy(A)`, which has the same axes;
the loop obtains every index from `eachindex(A)`. -/
def replaceArrayAccesses (length : Nat) : List Access :=
  (List.range length).flatMap fun i => [at0 length i, at0 length i]

def ReplaceArrayInBounds : Prop := ∀ length, accessesSafe (replaceArrayAccesses length)

theorem replaceArrayInBounds_proven : ReplaceArrayInBounds := by
  intro length a ha
  simp only [replaceArrayAccesses, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
  obtain ⟨i, hi, ha⟩ := ha
  rcases ha with rfl | rfl <;> simp [Access.safe, at0] <;> omega

/-- Dict `replace!`, `base/set.jl:980-1009`.  `skip_deleted_floor!` and each
subsequent `skip_deleted` search the slot vector and return the next live slot. -/
def replaceDictAccesses (slots : List Bool) : List Access :=
  (List.range slots.length).filterMap fun i => if slots[i]? = some true then some (at0 slots.length i) else none

def ReplaceDictInBounds : Prop := ∀ slots, accessesSafe (replaceDictAccesses slots)

theorem replaceDictInBounds_proven : ReplaceDictInBounds := by
  intro slots a ha
  simp only [replaceDictAccesses, List.mem_filterMap] at ha
  obtain ⟨i, hi, h⟩ := ha
  split at h
  · simp only [Option.some.injEq] at h
    subst a
    simp only [Access.safe, at0]
    exact Nat.succ_le_iff.mpr (List.mem_range.mp hi)
  · simp at h

def SetReplaceInBounds : Prop := ReplaceArrayInBounds ∧ ReplaceDictInBounds

theorem setReplaceInBounds_proven : SetReplaceInBounds :=
  ⟨replaceArrayInBounds_proven, replaceDictInBounds_proven⟩

end JuliaLean.MemSafety.G1
