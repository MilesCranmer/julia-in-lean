import JuliaLean.base.genericmemory

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

def GenericMemoryCoreBehavior : Prop :=
  memoryIndexStyle = 1 ∧
  (∀ aligned, memoryElementSize aligned = aligned) ∧
  (∀ offset, memoryIndex offset = offset) ∧
  (∀ memory, memoryParent memory = memory) ∧
  (∀ count same bits dp sp ep, copyRoute count same bits dp sp ep =
    if count == 0 then .zero else if same then if bits then .bits else .boxed
    else if dp < sp || dp > ep then .forward else .backward) ∧
  (∀ length, similarMemory length = List.replicate length none) ∧
  (∀ already same converted, convertMemory already same converted = if already then same else converted) ∧
  (∀ memory index, unsetAt memory index = memory.set (index - 1) none) ∧
  (∀ memory index, memoryIsAssigned memory index = (memory.getD (index - 1) none).isSome) ∧
  (∀ length value, fillByteMemory length value = List.replicate length (some (value % 256))) ∧
  (∀ dest src destOffset sourceOffset count backward,
    copySlots dest src destOffset sourceOffset count backward =
      let indices := if backward then (List.range count).reverse else List.range count
      indices.foldl (fun out k => out.set (destOffset + k) (src.getD (sourceOffset + k) none)) dest)

theorem genericMemoryCoreBehavior : GenericMemoryCoreBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl
def GenericMemoryIndexBehavior : Prop :=
  (∀ memory first count, memoryRange memory first count = (memory.drop first).take count) ∧
  (∀ memory index value, memorySet memory index value = memory.set index value) ∧
  (∀ left right, memoryCompare left right = if left < right then -1 else if right < left then 1 else 0) ∧
  (∀ left right, sortedFindRoute left right = (left && right)) ∧
  (∀ destination source, sameShape destination source = (destination.length == source.length)) ∧
  (∀ second rest, trailingIndexValid second rest = (second == 1 && rest.all (· == 1))) ∧
  (∀ sizes count, indcopyScale sizes count = match sizes[count]? with
    | none => 0
    | some first => (sizes.drop (count + 1)).foldl (· * ·) first) ∧
  (∀ operation index success fail, atomicEvent operation index success fail =
    ⟨operation, index, success, fail⟩)

theorem genericMemoryIndexBehavior : GenericMemoryIndexBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

end JuliaLean.NumMisc.Coverage
