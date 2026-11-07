import JuliaLean.base.pointer

namespace JuliaLean.NumMisc.Coverage

def PointerConversionBehavior : Prop :=
  (∀ address, pointerConvert address = address % 2^64) ∧
  (∀ memory, unsafeWrapRoute memory = if memory then .wrapMemory else .wrapArray) ∧
  (∀ base offset size array union,
    pointerMemoryOffset base offset size array union =
      if array == union || size == 0 then base + offset * size else base + offset) ∧
  (∀ mutable address, pointerFromObject mutable address =
    if mutable then .ok address
    else .error (.argumentError "pointer_from_objref cannot be used on immutable objects")) ∧
  (∀ event index order, pointerAccessEvent event index order = (event, index, order)) ∧
  (∀ index order, pointerModifyEvents index order =
    [(.load, index, order), (.modify, index, order), (.replace, index, order)])

theorem pointerConversionBehavior : PointerConversionBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl
def PointerArithmeticBehavior : Prop :=
  (∀ left right, pointerDifference left right = JInt.wrap .u64 (left.val - right.val)) ∧
  (∀ left right, pointerEqual left right = (left.val == right.val)) ∧
  (∀ left right, pointerLess left right = decide (left.val < right.val)) ∧
  (∀ pointer offset, ptrAdd pointer offset = JInt.wrap .u64 (pointer.val + offset)) ∧
  (∀ pointer offset, ptrSub pointer offset = JInt.wrap .u64 (pointer.val - offset)) ∧
  (∀ pointer, pointerUnsigned pointer = pointer) ∧
  (∀ pointer, pointerSigned pointer = JInt.wrap .i64 pointer.val)

theorem pointerArithmeticBehavior : PointerArithmeticBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

end JuliaLean.NumMisc.Coverage
