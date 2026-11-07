import JuliaLean.base.refpointer

namespace JuliaLean.NumMisc

def PointerRefSemantics : Prop :=
  (∀ p : Ptr64, ∀ offset : Int,
      (ptrAdd p offset).val = wrapInt .u64 (p.val + offset) ∧
      (ptrSub p offset).val = wrapInt .u64 (p.val - offset)) ∧
  (∀ p : Ptr64, ∀ elementBytes index : Int,
      refPointer p elementBytes index = ptrAdd p ((index - 1) * elementBytes)) ∧
  (∀ len index slot, derefArray len index = .ok slot ↔
      1 ≤ index ∧ index ≤ len ∧ slot = (index - 1).toNat) ∧
  (∀ xs : List Nat, tupleRef xs = xs)
theorem pointerRefSemantics_proven : PointerRefSemantics := by
  constructor
  · intro p offset
    exact ⟨rfl, rfl⟩
  constructor
  · intro p elementBytes index
    rfl
  constructor
  · intro len index slot
    unfold derefArray
    split
    · rename_i h
      simp only [Except.ok.injEq]
      omega
    · rename_i h
      constructor
      · intro heq
        cases heq
      · intro hr
        exact (h ⟨hr.1, hr.2.1⟩).elim
  · intro xs
    rfl

end JuliaLean.NumMisc

namespace JuliaLean.NumMisc.Coverage

def RefCoreBehavior : Prop :=
  (∀ ref, refLength ref = 1 ∧ refEmpty ref = false ∧ refDims ref = 0 ∧
    refSize ref = [] ∧ refAxes ref = []) ∧
  (∀ tag, refElementType tag = tag) ∧ refIteratorRank = 0 ∧
  (∀ ref started, refIterate ref started =
    if started then none else some (ref.values.getD (ref.index - 1).toNat none)) ∧
  (∀ values index roots, makeRefArray values index roots = ⟨values, index, roots⟩) ∧
  (∀ inline union, refPointerRoute inline union =
    if inline then .inline else if union then .unionLayout else .boxed) ∧
  (∀ index, singleRefIndex index =
    if index == 1 then .ok () else .error (.argumentError "Ref only has one element")) ∧
  (∀ pointer size index, refPointer pointer size index = ptrAdd pointer ((index - 1) * size))

theorem refCoreBehavior : RefCoreBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ref; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intros; rfl
  · rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
def RefArrayTupleBehavior : Prop :=
  (∀ pointers roots, rootPointerArray pointers roots = ⟨pointers ++ [0], roots, true⟩) ∧
  (∀ values, tupleRoot values = values) ∧
  (∀ values index roots, refArrayAt values index roots = ⟨values, index, roots⟩) ∧
  (∀ ref, refGet ref = ref.values.getD (ref.index - 1).toNat none) ∧
  (∀ ref value, refSet ref value =
    { ref with values := ref.values.set (ref.index - 1).toNat value })

theorem refArrayTupleBehavior : RefArrayTupleBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

end JuliaLean.NumMisc.Coverage
