import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.common.copy

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection

open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
variable {α : Type}

/-- `item isa T ? item : convert(T, item)` failing: `push!`/`pushfirst!` throw before growing. -/
theorem push_value_error {β : Type} (alreadyTyped : β → Bool) (asTyped : β → α)
    (conv : β → Except Error α) (pushTyped : Nat → α → MutationM α Nat) (s : MutableMemory α)
    (handle : Nat) (item : β) (e : Error)
    (hvalue : (if alreadyTyped item then .ok (asTyped item) else conv item) = .error e) :
    (JuliaLean.base.array.push alreadyTyped asTyped (fun x => stateExceptLift (conv x))
      pushTyped handle item).run s = (.error e, s) ∧
    (pushfirst alreadyTyped asTyped (fun x => stateExceptLift (conv x))
      pushTyped handle item).run s = (.error e, s) := by
  cases ht : alreadyTyped item
  · have hc : conv item = .error e := by simpa [ht] using hvalue
    constructor
    · simp only [JuliaLean.base.array.push, ht, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExceptLift_run, hc]
    · simp only [pushfirst, ht, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExceptLift_run, hc]
  · simp [ht] at hvalue

theorem push_value_ok {β : Type} (alreadyTyped : β → Bool) (asTyped : β → α)
    (conv : β → Except Error α) (pushTyped : Nat → α → MutationM α Nat) (s : MutableMemory α)
    (handle : Nat) (item : β) (x : α)
    (hvalue : (if alreadyTyped item then .ok (asTyped item) else conv item) = .ok x) :
    (JuliaLean.base.array.push alreadyTyped asTyped (fun x => stateExceptLift (conv x))
      pushTyped handle item).run s = (pushTyped handle x).run s ∧
    (pushfirst alreadyTyped asTyped (fun x => stateExceptLift (conv x))
      pushTyped handle item).run s = (pushTyped handle x).run s := by
  cases ht : alreadyTyped item
  · have hc : conv item = .ok x := by simpa [ht] using hvalue
    constructor
    · simp only [JuliaLean.base.array.push, ht, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExceptLift_run, hc]
    · simp only [pushfirst, ht, Bool.false_eq_true, ite_false, stateExcept_bind,
        stateExceptLift_run, hc]
  · have hc : asTyped item = x := by simpa [ht] using hvalue
    constructor
    · simp only [JuliaLean.base.array.push, ht, ite_true, stateExcept_bind, stateExcept_pure, hc]
    · simp only [pushfirst, ht, ite_true, stateExcept_bind, stateExcept_pure, hc]
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {α : Type}

/-- `Vector{T}(undef, 0)` in the store: a fresh empty memory and a fresh header at the next
handle. -/
theorem mutableAllocate_zero_run (l : MemoryLayout) (s : MutableMemory α) :
    (mutableAllocate (some l) 0 zero).run s =
      (.ok s.arrays.length,
        { memories := s.memories ++ [[]], arrays := s.arrays ++ [⟨(s.memories.length, one), zero⟩] }) := by
  have hz : ((zero : I).val % 2 ^ 64).toNat = 0 := by rw [ival_zero]; rfl
  first
  | rfl
  | (simp only [mutableAllocate, arrayUndef1, memoryUndef, memorynew, allocGenericMemory, hz,
      mutableFreshMemory, stateExcept_bind, mutation_get_run, stateExcept_pure,
      List.replicate_zero, ↓reduceIte]; rfl)
  | (simp [mutableAllocate, arrayUndef1, memoryUndef, memorynew, allocGenericMemory, hz,
      mutableFreshMemory]; done)
  | (simp [mutableAllocate, arrayUndef1, memoryUndef, memorynew, allocGenericMemory, hz,
      mutableFreshMemory]; rfl)
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {α : Type}

theorem splice_window {β : Type} (sl X : List β) (o d k nA : Nat) (hlen : o + nA ≤ sl.length)
    (hd : d + k ≤ nA) (hX : X.length = k) :
    ((sl.take (o + d) ++ X ++ sl.drop (o + d + k)).drop o).take nA =
      ((sl.drop o).take nA).take d ++ X ++ ((sl.drop o).take nA).drop (d + k) := by
  have hW : nA ≤ (sl.drop o).length := by rw [List.length_drop]; omega
  have hlo : (sl.take o).length = o := by rw [List.length_take]; omega
  rw [List.take_add, List.append_assoc, List.append_assoc, List.drop_left' hlo,
    show o + d + k = o + (d + k) by omega, ← List.drop_drop]
  generalize sl.drop o = W at hW ⊢
  rw [List.take_take, Nat.min_eq_left (by omega : d ≤ nA), List.drop_take, List.take_append,
    List.take_of_length_le (by rw [List.length_take]; omega : (W.take d).length ≤ nA),
    List.length_take, Nat.min_eq_left (by omega : d ≤ W.length), List.take_append,
    List.take_of_length_le (by omega : X.length ≤ nA - d), hX, List.append_assoc, Nat.sub_sub]

theorem splice_length {β : Type} (sl X : List β) (p k : Nat) (hlen : p + k ≤ sl.length)
    (hX : X.length = k) : (sl.take p ++ X ++ sl.drop (p + k)).length = sl.length := by
  simp only [List.length_append, List.length_take, List.length_drop, hX]
  omega

/-- `copyto!(dest, doffs, src, soffs, k)` between two vector windows (array.jl:288, 299-315),
`k ≥ 1` and both ranges inside the windows: one `memmove` of the source snapshot into the
destination memory. -/
theorem vwCopyto_run (s : MutableMemory α) {a b memA memB : Nat} {offA nA offB nB : I}
    {slotsA slotsB : List (Option α)} (ha : VecAt s a memA offA nA slotsA)
    (hb : VecAt s b memB offB nB slotsB) (doffs soffs k : I) (hk : 1 ≤ k.val)
    (hd1 : 1 ≤ doffs.val) (hde : doffs.val - 1 + k.val ≤ nA.val)
    (hs1 : 1 ≤ soffs.val) (hse : soffs.val - 1 + k.val ≤ nB.val) :
    (mutableCopyto a doffs b soffs k).run s =
      (.ok (), { s with
        memories := s.memories.set memA (slotsA.take ((offA.val - 1).toNat + (doffs.val - 1).toNat) ++
          (slotsB.drop ((offB.val - 1).toNat + (soffs.val - 1).toNat)).take k.val.toNat ++
          slotsA.drop ((offA.val - 1).toNat + (doffs.val - 1).toNat + k.val.toNat)) }) := by
  obtain ⟨haa, ham, hao, han, hae, hac⟩ := ha
  obtain ⟨hba, hbm, hbo, hbn, hbe, hbc⟩ := hb
  have hdb := ival_bounds doffs
  have hsb := ival_bounds soffs
  have hkb := ival_bounds k
  have hnab := ival_bounds nA
  have hnbb := ival_bounds nB
  have hoab := ival_bounds offA
  have hobb := ival_bounds offB
  have hdaddr : (offA + doffs - one).val = offA.val + doffs.val - 1 :=
    ival_add_sub_one _ _ (by omega)
  have hsaddr : (offB + soffs - one).val = offB.val + soffs.val - 1 :=
    ival_add_sub_one _ _ (by omega)
  have hmove := vwMemoryMove_run s memA memB (offA + doffs - one) (offB + soffs - one) k slotsA
    slotsB ham hbm (by omega) (by rw [hdaddr]; omega) (by rw [hdaddr]; omega)
    (by rw [hsaddr]; omega) (by rw [hsaddr]; omega) hac
  rw [hdaddr, hsaddr,
    show (offA.val + doffs.val - 1 - 1).toNat = (offA.val - 1).toNat + (doffs.val - 1).toNat by omega,
    show (offB.val + soffs.val - 1 - 1).toNat = (offB.val - 1).toNat + (soffs.val - 1).toNat by omega,
    show (offA.val + doffs.val - 1 - 1 + k.val).toNat =
      (offA.val - 1).toNat + (doffs.val - 1).toNat + k.val.toNat by omega] at hmove
  have hk0 : ¬ k.val = 0 := by omega
  have hkp : 0 < k.val := by omega
  have hinA : one ≤ doffs ∧ doffs ≤ nA := ⟨by rw [jle_iff, ival_one]; omega, by rw [jle_iff]; omega⟩
  have hinB : one ≤ soffs ∧ soffs ≤ nB := ⟨by rw [jle_iff, ival_one]; omega, by rw [jle_iff]; omega⟩
  have hfitA : k.val ≤ (nA - doffs + one).val := by
    rw [ival_add _ _ (by rw [ival_sub _ _ (by omega), ival_one]; omega), ival_sub _ _ (by omega),
      ival_one]
    omega
  have hfitB : k.val ≤ (nB - soffs + one).val := by
    rw [ival_add _ _ (by rw [ival_sub _ _ (by omega), ival_one]; omega), ival_sub _ _ (by omega),
      ival_one]
    omega
  simp only [mutableCopyto, copyto288, copytoImpl, stateExcept_bind, stateExcept_pure,
    mutableBounds, mutableInBounds, mutableLength_run s a _ haa, mutableLength_run s b _ hba,
    hk0, gt_iff_lt, hkp, hinA, hinB, hfitA, hfitB, and_self, decide_false, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false, mutableMemoryref_run s a _ haa,
    mutableMemoryref_run s b _ hba, hmove]
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
variable {α : Type}

theorem ms_checkedMul_overflow {layout : MemoryLayoutMetadata} (s : MutableMemory α) (x y : I)
    (h : ¬ (-9223372036854775808 ≤ x.val * y.val ∧ x.val * y.val ≤ 9223372036854775807)) :
    ((mutableStorage layout).checkedMul x y).run s = (.error .overflow, s) := by
  have h' : ¬ (IntTy.i64.min ≤ x.val * y.val ∧ x.val * y.val ≤ IntTy.i64.max) := h
  change (if _ then (pure (x * y) : MutationM α I) else throw Error.overflow).run s = _
  simp only [h', ite_false, stateExcept_throw]

theorem wval2' : (JInt.wrap .i64 2).val = 2 := ival_wrap 2 (by decide)

/-- Facts shared by the `_growbeg_internal!` cases. -/
theorem growbegInternal_facts {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 < delta.val)
    (hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807) :
    (n + delta).val = n.val + delta.val ∧
    ((mutableStorage layout).checkedAdd n delta).run s = (.ok (n + delta), s) ∧
    ((mutableStorage layout).checkedMul (JInt.wrap .i64 2) delta).run s =
      (.ok (JInt.wrap .i64 2 * delta), s) ∧
    ((mutableStorage layout).checkedAdd n (JInt.wrap .i64 2 * delta)).run s =
      (.ok (n + JInt.wrap .i64 2 * delta), s) ∧
    ((mutableStorage layout).checkedAdd (n + JInt.wrap .i64 2 * delta) one).run s =
      (.ok (n + JInt.wrap .i64 2 * delta + one), s) ∧
    (n + JInt.wrap .i64 2 * delta + one).val = n.val + 2 * delta.val + 1 := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have h2d : (JInt.wrap .i64 2 * delta).val = 2 * delta.val := by
    rw [show JInt.wrap .i64 2 * delta = JInt.wrap .i64 ((JInt.wrap .i64 2).val * delta.val) from rfl,
      wval2']
    exact ival_wrap _ (by omega)
  have hn2d : (n + JInt.wrap .i64 2 * delta).val = n.val + 2 * delta.val := by
    rw [ival_add _ _ (by rw [h2d]; omega), h2d]
  refine ⟨ival_add _ _ (by omega), ms_checkedAdd_run s n delta (by omega),
    ms_checkedMul_run s _ delta (by rw [wval2']; omega),
    ms_checkedAdd_run s n _ (by rw [h2d]; omega),
    ms_checkedAdd_run s _ one (by rw [hn2d, ival_one]; omega), ?_⟩
  rw [ival_add _ _ (by rw [hn2d, ival_one]; omega), hn2d, ival_one]
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
variable {α : Type}


theorem sameRef_self {layout : MemoryLayoutMetadata} (r : Nat × I) :
    (mutableStorage (α := α) layout).sameRef r r = true := by
  simp only [ms_sameRef, beq_self_eq_true]

theorem imin_val_native (a b : I) :
    (@min I JuliaLean.base.genericmemory.instMinI64 a b).val = min a.val b.val := by
  change (if a.val ≤ b.val then a else b).val = min a.val b.val
  split <;> rename_i h
  · exact (Int.min_eq_left h).symm
  · exact (Int.min_eq_right (by omega)).symm

/-- `_growbeg_internal!` recentring the data inside its own memory; `K` is
`max(overallocation(len), len + 2*delta + 1)`. -/
theorem growbegInternal_inplace {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 < delta.val) (hslow : off.val - 1 < delta.val)
    (hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807)
    (K : Nat) (hK : K = max (overallocationNat n.val.toNat) (n.val.toNat + 2 * delta.val.toNat + 1))
    (hi1 : n.val + delta.val < slots.length)
    (hi2 : ((K : Int) - (n.val + delta.val)) / 2 + 1 < slots.length - (n.val + delta.val)) :
    ∃ (newoff : I) (slots' : List (Option α)),
      (growbegInternal (mutableStorage layout) handle delta n).run s =
        (.ok (), { s with
          memories := s.memories.set mem slots'
          arrays := s.arrays.set handle ⟨(mem, newoff), n⟩ }) ∧
      newoff.val = (slots.length - (n.val + delta.val)) / 2 + 1 ∧ slots'.length = slots.length ∧
      (slots'.drop (newoff.val - 1 + delta.val).toNat).take n.val.toNat = vwWindow slots off n := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  obtain ⟨hnd, hadd1, hmul, hadd2, hadd3, hn2d1⟩ := growbegInternal_facts (layout := layout) h' delta hd hov
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h'
  obtain ⟨c, hcrun, hcv⟩ := ms_overallocation_val (layout := layout) s n hn0
  have hml := mutableMemLength_run (layout := layout) s mem slots hm
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  -- name every computed Int so later steps never see nested wraps
  generalize JInt.wrap .i64 (slots.length : Int) = WL at hml hL hc2 hc3
  generalize n + delta = NL at hnd hadd1
  generalize JInt.wrap .i64 2 * delta = D2 at hmul hadd2 hadd3 hn2d1
  generalize n + D2 = A2 at hadd2 hadd3 hn2d1
  generalize A2 + one = A3 at hadd3 hn2d1
  have hKv : (max c A3).val = (K : Int) := by
    rw [imax_val, hcv, hn2d1, hK]; omega
  have hKlo : n.val + 2 * delta.val + 1 ≤ (K : Int) := by rw [← hKv, imax_val, hn2d1]; omega
  clear hcv hK
  have hMb := ival_bounds (max c A3)
  have hKsub : (max c A3 - NL).val = (K : Int) - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hKv, hnd]; omega), hKv, hnd]
  generalize hQ0 : ((K : Int) - (n.val + delta.val)) / 2 = Q0 at hi2
  have hQ0b : 0 ≤ Q0 := by omega
  obtain ⟨Q, hdivA, hQ⟩ : ∃ Q : I, ((mutableStorage layout).divide (max c A3 - NL)
      (JInt.wrap .i64 2)).run s = (.ok Q, s) ∧ Q.val = Q0 :=
    ⟨_, ms_divide_run (layout := layout) s _ _ (by rw [wval2']; decide),
      by rw [wval2', tdiv_nonneg_val _ 2 (by rw [hKsub]; omega) (by decide) (by decide), hKsub, hQ0]⟩
  clear hQ0 hKsub
  have hLsub : (WL - NL).val = slots.length - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hL, hnd]; omega), hL, hnd]
  have hbr : (decide (NL < WL) && decide (Q + one < WL - NL)) = true := by
    have h1 : NL < WL := by rw [jlt_iff, hnd, hL]; exact hi1
    have h2 : Q + one < WL - NL := by
      rw [jlt_iff, hLsub, ival_add_one Q (by rw [hQ]; omega), hQ]; exact hi2
    simp only [h1, h2, decide_true, Bool.and_self]
  generalize hQ1 : ((slots.length : Int) - (n.val + delta.val)) / 2 = Q1
  have hQ1b : 2 * Q1 ≤ slots.length - (n.val + delta.val) ∧ 0 ≤ Q1 := by omega
  obtain ⟨Q', hdivB, hQ'⟩ : ∃ Q' : I, ((mutableStorage layout).divide (WL - NL)
      (JInt.wrap .i64 2)).run s = (.ok Q', s) ∧ Q'.val = Q1 :=
    ⟨_, ms_divide_run (layout := layout) s _ _ (by rw [wval2']; decide),
      by rw [wval2', tdiv_nonneg_val _ 2 (by rw [hLsub]; omega) (by decide) (by decide), hLsub, hQ1]⟩
  clear hQ1
  simp only [growbegInternal, ms_ref, ms_memory, ms_offset, ms_memoryref, ms_copyMemory,
    ms_unsetMemory, stateExcept_bind, stateExcept_pure,
    mutableRef_run s handle _ ha, hml, hadd1,
    gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
    hcrun, hmul, hadd2, hadd3, hdivA, hbr, ite_true, hdivB]
  have hno : (Q' + one).val = Q1 + 1 := by rw [ival_add_one Q' (by rw [hQ']; omega), hQ']
  generalize Q' + one = newoff at hno ⊢
  clear hbr hdivA hdivB hi2 hQ0b hcrun hmul hadd2 hadd3 hn2d1 hQ hQ' hLsub hKv hMb
  have hdo : (newoff + delta).val = Q1 + 1 + delta.val := by
    rw [ival_add _ _ (by rw [hno]; omega), hno]
  have hmove := vwMemoryMove_run s mem mem (newoff + delta) off n slots slots hm hm hn0
    (by rw [hdo]; omega) (by rw [hdo]; omega) ho he hc
  simp only [hmove]
  generalize hS1 : slots.take ((newoff + delta).val - 1).toNat ++
      (slots.drop (off.val - 1).toNat).take n.val.toNat ++
      slots.drop ((newoff + delta).val - 1 + n.val).toNat = S1
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have hS1len : S1.length = slots.length := by
    rw [← hS1]
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [hdo]
    omega
  have hon : (off + n).val = off.val + n.val := ival_add _ _ (by omega)
  have hm1 : (@min I JuliaLean.base.genericmemory.instMinI64 (newoff + delta) (off + n) - one).val = min (Q1 + 1 + delta.val) (off.val + n.val) - 1 := by
    rw [ival_sub_one _ (by rw [imin_val_native, hdo, hon]; omega),
      imin_val_native, hdo, hon]
  have hjs : ∀ j ∈ intRange off (@min I JuliaLean.base.genericmemory.instMinI64 (newoff + delta) (off + n) - one),
      1 ≤ j.val ∧ j.val ≤ (S1.length : Int) := by
    intro j hj
    have hr := intRange_mem _ _ j hj
    rw [hm1] at hr
    rw [hS1len]
    omega
  rw [vwClearLoop_run mem _ _ S1 (List.getElem?_set_self hlt) ?hjs]
  case hjs => exact hjs
  simp only [List.set_set]
  generalize hS2 : vwClear (unsetRuntime := layout.runtime) S1 (intRange off (@min I JuliaLean.base.genericmemory.instMinI64 (newoff + delta) (off + n) - one)) = S2
  have href2 : (mutableRef handle).run { s with memories := s.memories.set mem S2 } =
      (.ok (mem, off), { s with memories := s.memories.set mem S2 }) :=
    mutableRef_run { s with memories := s.memories.set mem S2 } handle _ ha
  have hset := ms_setRef_run (layout := layout)
    { s with memories := s.memories.set mem S2 } handle ⟨(mem, off), n⟩ ha (mem, newoff)
  simp only [href2, sameRef_self, Bool.not_true, Bool.false_eq_true, ite_false, stateExcept_bind,
    stateExcept_pure, hset]
  refine ⟨newoff, S2, rfl, hno, by rw [← hS2, vwClear_length, hS1len], ?_⟩
  have hk : ∀ j ∈ intRange off (@min I JuliaLean.base.genericmemory.instMinI64 (newoff + delta) (off + n) - one),
      (j.val - 1).toNat < (newoff.val - 1 + delta.val).toNat := by
    intro j hj
    have hr := intRange_mem _ _ j hj
    rw [hm1] at hr
    omega
  have hdrop := vwClear_drop (unsetRuntime := layout.runtime) S1 _ _ hk
  have hA : (slots.take ((newoff + delta).val - 1).toNat).length = (newoff.val - 1 + delta.val).toNat := by
    rw [List.length_take, hdo, hno]; omega
  have hW : ((slots.drop (off.val - 1).toNat).take n.val.toNat).length = n.val.toNat := by
    simp only [List.length_take, List.length_drop]; omega
  rw [← hS2, hdrop, ← hS1, take_three hA hW]
  rfl
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
variable {α : Type}


/-- `_growbeg_internal!` moving the data to a new memory of `K =
max(overallocation(len), len + 2*delta + 1)` slots, `delta` slots after its new offset. -/
theorem growbegInternal_alloc (l : DictLayout) {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 < delta.val)
    (hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807)
    (K : Nat) (hK : K = max (overallocationNat n.val.toNat) (n.val.toNat + 2 * delta.val.toNat + 1))
    (hns : ¬ (n.val + delta.val < slots.length ∧
      ((K : Int) - (n.val + delta.val)) / 2 + 1 < slots.length - (n.val + delta.val))) :
    (¬ memoryFits l K → (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle delta n).run s =
      (.error (.argument genericMemorySizeMessage), s)) ∧
    (memoryFits l K → ∃ (newoff : I) (D : List (Option α)),
      (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) handle delta n).run s =
        (.ok (), { s with
          memories := (s.memories ++ [List.replicate K none]).set s.memories.length D
          arrays := s.arrays.set handle ⟨(s.memories.length, newoff), n⟩ }) ∧
      newoff.val = ((K : Int) - (n.val + delta.val)) / 2 + 1 ∧ D.length = K ∧
      (D.drop (newoff.val - 1 + delta.val).toNat).take n.val.toNat = vwWindow slots off n) := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  obtain ⟨hnd, hadd1, hmul, hadd2, hadd3, hn2d1⟩ := growbegInternal_facts (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd hov
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h'
  obtain ⟨c, hcrun, hcv⟩ := ms_overallocation_val (layout := MemoryLayoutMetadata.ofRuntime l) s n hn0
  have hml := mutableMemLength_run (layout := MemoryLayoutMetadata.ofRuntime l) s mem slots hm
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  generalize JInt.wrap .i64 (slots.length : Int) = WL at hml hL hc2 hc3
  generalize n + delta = NL at hnd hadd1
  generalize JInt.wrap .i64 2 * delta = D2 at hmul hadd2 hadd3 hn2d1
  generalize n + D2 = A2 at hadd2 hadd3 hn2d1
  generalize A2 + one = A3 at hadd3 hn2d1
  have hKv : (max c A3).val = (K : Int) := by
    rw [imax_val, hcv, hn2d1, hK]; omega
  have hKlo : n.val + 2 * delta.val + 1 ≤ (K : Int) := by rw [← hKv, imax_val, hn2d1]; omega
  clear hcv hK
  have hMb := ival_bounds (max c A3)
  have hKsub : (max c A3 - NL).val = (K : Int) - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hKv, hnd]; omega), hKv, hnd]
  generalize hQ0 : ((K : Int) - (n.val + delta.val)) / 2 = Q0 at hns ⊢
  have hQ0b : 2 * Q0 ≤ (K : Int) - (n.val + delta.val) ∧ 0 ≤ Q0 := by omega
  obtain ⟨Q, hdivA, hQ⟩ : ∃ Q : I, ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).divide (max c A3 - NL)
      (JInt.wrap .i64 2)).run s = (.ok Q, s) ∧ Q.val = Q0 :=
    ⟨_, ms_divide_run (layout := MemoryLayoutMetadata.ofRuntime l) s _ _ (by rw [wval2']; decide),
      by rw [wval2', tdiv_nonneg_val _ 2 (by rw [hKsub]; omega) (by decide) (by decide), hKsub, hQ0]⟩
  clear hQ0 hKsub
  have hLsub : (WL - NL).val = slots.length - (n.val + delta.val) := by
    rw [ival_sub _ _ (by rw [hL, hnd]; omega), hL, hnd]
  have hbr : (decide (NL < WL) && decide (Q + one < WL - NL)) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases hs1 : n.val + delta.val < slots.length
    · right
      rw [decide_eq_false_iff_not, jlt_iff, hLsub, ival_add_one Q (by rw [hQ]; omega), hQ]
      exact fun h2 => hns ⟨hs1, h2⟩
    · left
      rw [decide_eq_false_iff_not, jlt_iff, hnd, hL]
      exact hs1
  have hA := arrayNewMemorySpec α l s mem (max c A3)
  simp only at hA
  have hK0 : 0 ≤ (max c A3).val := by rw [hKv]; omega
  have hKn : (max c A3).val.toNat = K := by rw [hKv]; omega
  rw [hKn] at hA
  simp only [growbegInternal, ms_ref, ms_memory, ms_offset, ms_memoryref, ms_copyMemory,
    stateExcept_bind, stateExcept_pure,
    mutableRef_run s handle _ ha, hml, hadd1,
    gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
    hcrun, hmul, hadd2, hadd3, hdivA, hbr]
  have hno : (Q + one).val = Q0 + 1 := by rw [ival_add_one Q (by rw [hQ]; omega), hQ]
  generalize Q + one = newoff at hno ⊢
  clear hbr hdivA hns hcrun hmul hadd2 hadd3 hn2d1 hQ hLsub
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  refine ⟨fun hnf => ?_, fun hfit => ?_⟩
  · have hE : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max c A3)).run s =
        (.error (.argument genericMemorySizeMessage), s) := hA.2.1 hK0 hnf
    simp only [hE]
  · have hOk : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max c A3)).run s =
        (.ok s.memories.length, { s with memories := s.memories ++ [List.replicate K none] }) :=
      hA.2.2 hK0 hfit
    have hk63 : K < 2 ^ 63 := by have := hfit.1; unfold maxIntVal at this; omega
    have hdM : ({ s with memories := s.memories ++ [List.replicate K none] } : MutableMemory α).memories[s.memories.length]? =
        some (List.replicate K none) := by simp
    have hsM : ({ s with memories := s.memories ++ [List.replicate K none] } : MutableMemory α).memories[mem]? =
        some slots := by
      show (s.memories ++ [List.replicate K none])[mem]? = some slots
      rw [List.getElem?_append_left hlt]; exact hm
    have hdo : (newoff + delta).val = Q0 + 1 + delta.val := by
      rw [ival_add _ _ (by rw [hno]; omega), hno]
    have hmove := vwMemoryMove_run { s with memories := s.memories ++ [List.replicate K none] }
      s.memories.length mem (newoff + delta) off n (List.replicate K none) slots hdM hsM hn0
      (by rw [hdo]; omega) (by rw [List.length_replicate, hdo]; omega) ho he
      (by rw [List.length_replicate]; exact hk63)
    simp only [hOk, hmove]
    generalize hD : (List.replicate K none).take ((newoff + delta).val - 1).toNat ++
        (slots.drop (off.val - 1).toNat).take n.val.toNat ++
        (List.replicate K none).drop ((newoff + delta).val - 1 + n.val).toNat = D
    have href2 : (mutableRef handle).run
        { s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D } =
        (.ok (mem, off), { s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D }) :=
      mutableRef_run { s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D }
        handle _ ha
    have hset := ms_setRef_run (layout := MemoryLayoutMetadata.ofRuntime l)
      { s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D }
      handle ⟨(mem, off), n⟩ ha (s.memories.length, newoff)
    simp only [stateExcept_bind, href2, sameRef_self, Bool.not_true, Bool.false_eq_true,
      ite_false, stateExcept_pure, hset]
    have hA' : ((List.replicate K (none : Option α)).take ((newoff + delta).val - 1).toNat).length =
        (newoff.val - 1 + delta.val).toNat := by
      rw [List.length_take, List.length_replicate, hdo, hno]; omega
    have hW : ((slots.drop (off.val - 1).toNat).take n.val.toNat).length = n.val.toNat := by
      simp only [List.length_take, List.length_drop]; omega
    refine ⟨newoff, D, rfl, hno, ?_, ?_⟩
    · rw [← hD]
      simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate]
      rw [hdo]
      omega
    · rw [← hD, take_three hA' hW]
      rfl

/-- `_growbeg_internal!` when `len + 2*delta + 1` is not an `Int`: `OverflowError`, store unchanged. -/
theorem growbegInternal_overflow {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 < delta.val) (hov1 : n.val + delta.val ≤ 9223372036854775807)
    (hov : 9223372036854775807 < n.val + 2 * delta.val + 1) :
    (growbegInternal (mutableStorage layout) handle delta n).run s = (.error .overflow, s) := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have hadd1 := ms_checkedAdd_run (layout := layout) s n delta (by omega)
  obtain ⟨hc1, hc2, hc3⟩ := growendInternal_checks h'
  obtain ⟨c, hcrun, hcv⟩ := ms_overallocation_val (layout := layout) s n hn0
  by_cases h2 : 2 * delta.val ≤ 9223372036854775807
  · have hmul := ms_checkedMul_run (layout := layout) s (JInt.wrap .i64 2) delta (by rw [wval2']; omega)
    have h2d : (JInt.wrap .i64 2 * delta).val = 2 * delta.val := by
      rw [show JInt.wrap .i64 2 * delta = JInt.wrap .i64 ((JInt.wrap .i64 2).val * delta.val) from rfl,
        wval2']
      exact ival_wrap _ (by omega)
    by_cases h3 : n.val + 2 * delta.val ≤ 9223372036854775807
    · have hadd2 := ms_checkedAdd_run (layout := layout) s n (JInt.wrap .i64 2 * delta)
        (by rw [h2d]; omega)
      have hn2d : (n + JInt.wrap .i64 2 * delta).val = n.val + 2 * delta.val := by
        rw [ival_add _ _ (by rw [h2d]; omega), h2d]
      have hadd3 := ms_checkedAdd_overflow (layout := layout) s (n + JInt.wrap .i64 2 * delta) one
        (by rw [hn2d, ival_one]; omega)
      simp only [growbegInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind,
        mutableRef_run s handle _ ha, mutableMemLength_run s mem slots hm, hadd1,
        gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
        hcrun, hmul, hadd2, hadd3]
    · have hadd2 := ms_checkedAdd_overflow (layout := layout) s n (JInt.wrap .i64 2 * delta)
        (by rw [h2d]; omega)
      simp only [growbegInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind,
        mutableRef_run s handle _ ha, mutableMemLength_run s mem slots hm, hadd1,
        gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
        hcrun, hmul, hadd2]
  · have hmul := ms_checkedMul_overflow (layout := layout) s (JInt.wrap .i64 2) delta
      (by rw [wval2']; omega)
    simp only [growbegInternal, ms_ref, ms_memory, ms_offset, stateExcept_bind,
      mutableRef_run s handle _ ha, mutableMemLength_run s mem slots hm, hadd1,
      gt_iff_lt, hc1, hc2, hc3, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      hcrun, hmul]
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
variable {α : Type}

theorem growbeg_zero_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat)
    (delta : I) (hz : delta.val = 0) :
    (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)) handle delta).run s =
      (.ok (), s) := by
  simp only [growbeg, stateExcept_bind, stateExcept_pure, hz, ite_true]

theorem growbeg_overflow_run {layout : MemoryLayoutMetadata} {s : MutableMemory α} {handle mem : Nat}
    {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd : 0 < delta.val) (hov : 9223372036854775807 < n.val + delta.val) :
    (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)) handle delta).run s =
      (.error .overflow, s) := by
  have hdz : ¬ delta.val = 0 := by omega
  have hpos : delta ≥ zero := by rw [ge_iff_le, jle_iff, ival_zero]; omega
  have hadd := ms_checkedAdd_overflow (layout := layout) s n delta (by omega)
  simp only [growbeg, ms_ref, ms_length, ms_offset, stateExcept_bind, stateExcept_pure, hdz,
    ite_false, hpos, decide_true, Bool.not_true, Bool.false_eq_true,
    mutableRef_run s handle _ h.1, mutableLength_run s handle _ h.1, hadd]

theorem growbeg_fast_run {layout : MemoryLayoutMetadata} {s : MutableMemory α} {handle mem : Nat}
    {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd : 0 < delta.val) (hov : n.val + delta.val ≤ 9223372036854775807)
    (hfast : delta.val ≤ off.val - 1) :
    (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)) handle delta).run s =
      (.ok (), { s with arrays := s.arrays.set handle ⟨(mem, off + (one - delta) - one), n + delta⟩ }) := by
  have hdz : ¬ delta.val = 0 := by omega
  have hpos : delta ≥ zero := by rw [ge_iff_le, jle_iff, ival_zero]; omega
  have hnb := ival_bounds n
  have hob := ival_bounds off
  have hadd := ms_checkedAdd_run (layout := layout) s n delta (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by have := h.2.2.1; omega)
  have hle : delta ≤ off - one := by rw [jle_iff, hoff1]; exact hfast
  have halt := (List.getElem?_eq_some_iff.mp h.1).choose
  have hset := vwSetRef_run (layout := layout) s handle mem off n slots h (mem, off + (one - delta) - one)
  simp only [growbeg, ms_ref, ms_length, ms_offset, ms_shiftref, stateExcept_bind, stateExcept_pure, hdz,
    ite_false, hpos, decide_true, Bool.not_true, Bool.false_eq_true,
    mutableRef_run s handle _ h.1, mutableLength_run s handle _ h.1, hadd, hle, ite_true, hset]
  rw [setSize_after s s.memories handle _ halt]

theorem growbeg_slow_run {layout : MemoryLayoutMetadata} {s : MutableMemory α} {handle mem : Nat}
    {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd : 0 < delta.val) (hov : n.val + delta.val ≤ 9223372036854775807)
    (hslow : off.val - 1 < delta.val)
    (r : Except Error Unit) (st : MutableMemory α)
    (hint : (growbegInternal (mutableStorage layout) handle delta n).run s = (r, st)) :
    (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)) handle delta).run s =
      (match r with
        | .error e => (.error e, st)
        | .ok _ => ((mutableStorage layout).setSize handle (n + delta)).run st) := by
  have hdz : ¬ delta.val = 0 := by omega
  have hpos : delta ≥ zero := by rw [ge_iff_le, jle_iff, ival_zero]; omega
  have hnb := ival_bounds n
  have hob := ival_bounds off
  have hadd := ms_checkedAdd_run (layout := layout) s n delta (by omega)
  have hoff1 : (off - one).val = off.val - 1 := ival_sub_one off (by have := h.2.2.1; omega)
  have hle : ¬ delta ≤ off - one := by rw [jle_iff, hoff1]; omega
  simp only [growbeg, ms_ref, ms_length, ms_offset, stateExcept_bind, stateExcept_pure, hdz,
    ite_false, hpos, decide_true, Bool.not_true, Bool.false_eq_true,
    mutableRef_run s handle _ h.1, mutableLength_run s handle _ h.1, hadd, hle, hint]
  cases r <;> rfl

/-- The conclusion of `growbeg_plan` for one starting vector and `delta`. -/
def GrowbegPost (l : DictLayout) (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (delta : I) : Prop :=
    (∀ e, growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat = .error e →
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
        handle delta).run s = (.error e, s)) ∧
    (∀ g', growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat = .ok g' →
      ∃ next mem' off' slots',
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
          handle delta).run s = (.ok (), next) ∧
        VecAt next handle mem' off' (n + delta) slots' ∧
        next.arrays = s.arrays.set handle ⟨(mem', off'), n + delta⟩ ∧
        (n + delta).val = n.val + delta.val ∧
        (vwWindow slots' off' (n + delta)).drop delta.val.toNat = vwWindow slots off n ∧
        geometryOf next handle = g' ∧
        s.memories.length ≤ next.memories.length ∧
        (∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) ∧
        (mem' = mem ∨ mem' = s.memories.length))

/-- The front window of `n + delta` slots at `o`, without its first `delta` slots. -/
theorem growbeg_window (sl : List (Option α)) (o n delta : I) (ho' : 1 ≤ o.val)
    (hn0 : 0 ≤ n.val) (hd : 0 ≤ delta.val) (hnd : (n + delta).val = n.val + delta.val) :
    (vwWindow sl o (n + delta)).drop delta.val.toNat =
      (sl.drop (o.val - 1 + delta.val).toNat).take n.val.toNat := by
  simp only [vwWindow, List.drop_take, List.drop_drop]
  congr 1
  · rw [hnd]; omega
  · congr 1; omega

/-- A plan error that the run reproduces with the store untouched. -/
theorem growbegPost_error (l : DictLayout) {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (delta : I) (e : Error)
    (hplan : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat = .error e)
    (hrun : (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
        handle delta).run s = (.error e, s)) :
    GrowbegPost l s handle mem off n slots delta := by
  refine ⟨fun e' he => ?_, fun g' hg' => by rw [hplan] at hg'; cases hg'⟩
  rw [hplan] at he
  cases he
  exact hrun

theorem growbeg_case_inplace (l : DictLayout) {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd0 : 0 < delta.val) (hov1 : n.val + delta.val ≤ 9223372036854775807)
    (hslow : off.val - 1 < delta.val) (hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807)
    (K : Nat) (hK : K = max (overallocationNat n.val.toNat) (n.val.toNat + 2 * delta.val.toNat + 1))
    (hs : n.val + delta.val < slots.length ∧
      ((K : Int) - (n.val + delta.val)) / 2 + 1 < slots.length - (n.val + delta.val)) :
    GrowbegPost l s handle mem off n slots delta := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have hlt := (List.getElem?_eq_some_iff.mp hm).choose
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hdN : delta.val.toNat ≠ 0 := by omega
  have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
  have hov1N : ¬ (typemaxNat < n.val.toNat + delta.val.toNat) := by unfold typemaxNat; omega
  have hfastN : ¬ (delta.val.toNat ≤ off.val.toNat - 1) := by omega
  have hovN : ¬ (typemaxNat < n.val.toNat + 2 * delta.val.toNat + 1) := by
    unfold typemaxNat; omega
  obtain ⟨newoff, slots', hint, hnewoff, hlen, hwin'⟩ :=
    growbegInternal_inplace (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd0 hslow hov K hK hs.1 hs.2
  have hsN : n.val.toNat + delta.val.toNat < slots.length ∧
      (max (overallocationNat n.val.toNat) (n.val.toNat + 2 * delta.val.toNat + 1) -
        (n.val.toNat + delta.val.toNat)) / 2 + 1 <
        slots.length - (n.val.toNat + delta.val.toNat) := by
    rw [← hK]; omega
  have hplan : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
      .ok ⟨slots.length, (slots.length - (n.val.toNat + delta.val.toNat)) / 2 + 1,
        n.val.toNat + delta.val.toNat⟩ := by
    simp only [growbegPlan, growbegInternalPlan, hdN, hov1N, hfastN, hovN, hsN, ite_false,
      ite_true, and_self]
    rfl
  have hrun := growbeg_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd0 hov1 hslow _ _ hint
  rw [setSize_after s _ handle _ halt] at hrun
  refine ⟨fun e he => (by rw [hplan] at he; cases he), fun g' hg' => ?_⟩
  rw [hplan] at hg'
  cases hg'
  have hv : VecAt { s with
      memories := s.memories.set mem slots'
      arrays := s.arrays.set handle ⟨(mem, newoff), n + delta⟩ } handle mem newoff
      (n + delta) slots' :=
    ⟨List.getElem?_set_self halt, List.getElem?_set_self hlt, by omega, by omega,
      by rw [hlen, hnewoff, hnd]; omega, by rw [hlen]; exact hc⟩
  refine ⟨{ s with
      memories := s.memories.set mem slots'
      arrays := s.arrays.set handle ⟨(mem, newoff), n + delta⟩ }, mem, newoff, slots', hrun, hv, rfl,
    hnd, ?_, ?_, by simp, ?_, Or.inl rfl⟩
  · rw [growbeg_window slots' newoff n delta (by rw [hnewoff]; omega) hn0 (by omega) hnd]
    exact hwin'
  · rw [VecAt.geometry hv, hnd, hlen, hnewoff]
    simp only [VectorGeometry.mk.injEq, true_and]
    omega
  · intro m _ hne
    exact List.getElem?_set_ne (fun he => hne he.symm)

theorem growbeg_case_alloc (l : DictLayout) {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd0 : 0 < delta.val) (hov1 : n.val + delta.val ≤ 9223372036854775807)
    (hslow : off.val - 1 < delta.val) (hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807)
    (K : Nat) (hK : K = max (overallocationNat n.val.toNat) (n.val.toNat + 2 * delta.val.toNat + 1))
    (hs : ¬ (n.val + delta.val < slots.length ∧
      ((K : Int) - (n.val + delta.val)) / 2 + 1 < slots.length - (n.val + delta.val))) :
    GrowbegPost l s handle mem off n slots delta := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hdN : delta.val.toNat ≠ 0 := by omega
  have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
  have hov1N : ¬ (typemaxNat < n.val.toNat + delta.val.toNat) := by unfold typemaxNat; omega
  have hfastN : ¬ (delta.val.toNat ≤ off.val.toNat - 1) := by omega
  have hovN : ¬ (typemaxNat < n.val.toNat + 2 * delta.val.toNat + 1) := by
    unfold typemaxNat; omega
  have hKlo : n.val.toNat + 2 * delta.val.toNat + 1 ≤ K := by rw [hK]; exact Nat.le_max_right _ _
  obtain ⟨hnf, hok⟩ := growbegInternal_alloc l h' delta hd0 hov K hK hs
  have hsN : ¬ (n.val.toNat + delta.val.toNat < slots.length ∧
      (max (overallocationNat n.val.toNat) (n.val.toNat + 2 * delta.val.toNat + 1) -
        (n.val.toNat + delta.val.toNat)) / 2 + 1 <
        slots.length - (n.val.toNat + delta.val.toNat)) := by
    rw [← hK]; omega
  have hplan : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
      (allocationPlan l K ⟨K, (K - (n.val.toNat + delta.val.toNat)) / 2 + 1, n.val.toNat⟩).map
        fun g' => { g' with length := n.val.toNat + delta.val.toNat } := by
    simp only [growbegPlan, growbegInternalPlan, hdN, hov1N, hfastN, hovN, hsN, ite_false]
    rw [← hK]
  by_cases hfit : memoryFits l K
  · obtain ⟨newoff, D, hint, hnewoff, hDlen, hDwin⟩ := hok hfit
    have hk63 : K < 2 ^ 63 := by
      have := hfit.1; unfold maxIntVal at this; omega
    have hplan' : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
        .ok ⟨K, (K - (n.val.toNat + delta.val.toNat)) / 2 + 1, n.val.toNat + delta.val.toNat⟩ := by
      rw [hplan]; simp only [allocationPlan, hfit, ite_true]; rfl
    have hrun := growbeg_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd0 hov1 hslow _ _ hint
    rw [setSize_after s _ handle _ halt] at hrun
    refine ⟨fun e he => (by rw [hplan'] at he; cases he), fun g' hg' => ?_⟩
    rw [hplan'] at hg'
    cases hg'
    have hMlt : s.memories.length < (s.memories ++ [List.replicate K none]).length := by
      simp
    have hv : VecAt { s with
        memories := (s.memories ++ [List.replicate K none]).set s.memories.length D
        arrays := s.arrays.set handle ⟨(s.memories.length, newoff), n + delta⟩ } handle
        s.memories.length newoff (n + delta) D :=
      ⟨List.getElem?_set_self halt, List.getElem?_set_self hMlt, by rw [hnewoff]; omega, by omega,
        by rw [hDlen, hnd, hnewoff]; omega, by rw [hDlen]; exact hk63⟩
    refine ⟨{ s with
        memories := (s.memories ++ [List.replicate K none]).set s.memories.length D
        arrays := s.arrays.set handle ⟨(s.memories.length, newoff), n + delta⟩ },
      s.memories.length, newoff, D, hrun, hv, rfl, hnd, ?_, ?_, by simp, ?_, Or.inr rfl⟩
    · rw [growbeg_window D newoff n delta (by rw [hnewoff]; omega) hn0 (by omega) hnd]
      exact hDwin
    · rw [VecAt.geometry hv, hnd, hDlen, hnewoff]
      simp only [VectorGeometry.mk.injEq, true_and]
      omega
    · intro m hm' _
      rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hm']
  · have hplan' : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
        .error (.argument genericMemorySizeMessage) := by
      rw [hplan]; simp only [allocationPlan, hfit, ite_false]; rfl
    exact growbegPost_error l delta _ hplan'
      (growbeg_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd0 hov1 hslow _ _ (hnf hfit))

theorem growbeg_case_fast (l : DictLayout) {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I)
    (hd0 : 0 < delta.val) (hov1 : n.val + delta.val ≤ 9223372036854775807)
    (hfast : delta.val ≤ off.val - 1) :
    GrowbegPost l s handle mem off n slots delta := by
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hdN : delta.val.toNat ≠ 0 := by omega
  have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
  have hov1N : ¬ (typemaxNat < n.val.toNat + delta.val.toNat) := by unfold typemaxNat; omega
  have hfastN : delta.val.toNat ≤ off.val.toNat - 1 := by omega
  have hplan : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
      .ok ⟨slots.length, off.val.toNat - delta.val.toNat, n.val.toNat + delta.val.toNat⟩ := by
    simp only [growbegPlan, hdN, hov1N, hfastN, ite_false, ite_true]
  have hoffv : (off + (one - delta) - one).val = off.val - delta.val := by
    have h1 : (one - delta).val = 1 - delta.val := ival_sub _ _ (by rw [ival_one]; omega)
    rw [ival_add_sub_one _ _ (by rw [h1]; omega), h1]; omega
  refine ⟨fun e he => (by rw [hplan] at he; cases he), fun g' hg' => ?_⟩
  rw [hplan] at hg'
  cases hg'
  have hv : VecAt { s with arrays := s.arrays.set handle ⟨(mem, off + (one - delta) - one), n + delta⟩ }
      handle mem (off + (one - delta) - one) (n + delta) slots :=
    ⟨List.getElem?_set_self halt, hm, by rw [hoffv]; omega, by omega,
      by rw [hoffv, hnd]; omega, hc⟩
  refine ⟨_, mem, _, slots, growbeg_fast_run h' delta hd0 hov1 hfast, hv, rfl, hnd, ?_, ?_,
    Nat.le_refl _, fun _ _ _ => rfl, Or.inl rfl⟩
  · rw [growbeg_window slots _ n delta (by rw [hoffv]; omega) hn0 (by omega) hnd, hoffv,
      show off.val - delta.val - 1 + delta.val = off.val - 1 by omega]
    rfl
  · rw [VecAt.geometry hv, hnd, hoffv]
    simp only [VectorGeometry.mk.injEq, true_and]
    omega

/-- `_growbeg!(a, delta)` on a valid vector follows `growbegPlan`: the plan's error with `a`
untouched, or `a` lengthened by `delta` slots in front with its old elements as suffix and the
planned geometry; other array headers and other memories are untouched. -/
theorem growbeg_plan (l : DictLayout) {s : MutableMemory α} {handle mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s handle mem off n slots) (delta : I) (hd : 0 ≤ delta.val) :
    (∀ e, growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat = .error e →
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
        handle delta).run s = (.error e, s)) ∧
    (∀ g', growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat = .ok g' →
      ∃ next mem' off' slots',
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
          handle delta).run s = (.ok (), next) ∧
        VecAt next handle mem' off' (n + delta) slots' ∧
        next.arrays = s.arrays.set handle ⟨(mem', off'), n + delta⟩ ∧
        (n + delta).val = n.val + delta.val ∧
        (vwWindow slots' off' (n + delta)).drop delta.val.toNat = vwWindow slots off n ∧
        geometryOf next handle = g' ∧
        s.memories.length ≤ next.memories.length ∧
        (∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) ∧
        (mem' = mem ∨ mem' = s.memories.length)) := by
  show GrowbegPost l s handle mem off n slots delta
  have h' := h
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hob := ival_bounds off
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  by_cases hz : delta.val = 0
  · have hnd : (n + delta).val = n.val + delta.val := ival_add _ _ (by omega)
    have hnn : n + delta = n := Subtype.ext (by rw [hnd, hz]; omega)
    have hplan : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
        .ok ⟨slots.length, off.val.toNat, n.val.toNat⟩ := by
      simp only [growbegPlan, show delta.val.toNat = 0 by omega, ite_true]
    refine ⟨fun e he => (by rw [hplan] at he; cases he), fun g' hg' => ?_⟩
    rw [hplan] at hg'
    cases hg'
    have hself : s.arrays.set handle ⟨(mem, off), n⟩ = s.arrays := by
      rw [← (List.getElem?_eq_some_iff.mp ha).choose_spec]
      exact List.set_getElem_self halt
    refine ⟨s, mem, off, slots, growbeg_zero_run s handle delta hz, by rw [hnn]; exact h', ?_, hnd,
      ?_, VecAt.geometry h', Nat.le_refl _, fun _ _ _ => rfl, Or.inl rfl⟩
    · rw [hnn, hself]
    · rw [growbeg_window slots off n delta ho hn0 (by omega) hnd, hz, Int.add_zero]; rfl
  · have hd0 : 0 < delta.val := by omega
    have hdN : delta.val.toNat ≠ 0 := by omega
    by_cases hov1 : n.val + delta.val ≤ 9223372036854775807
    · have hov1N : ¬ (typemaxNat < n.val.toNat + delta.val.toNat) := by unfold typemaxNat; omega
      by_cases hfast : delta.val ≤ off.val - 1
      · exact growbeg_case_fast l h' delta hd0 hov1 hfast
      · have hslow : off.val - 1 < delta.val := by omega
        have hfastN : ¬ (delta.val.toNat ≤ off.val.toNat - 1) := by omega
        by_cases hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807
        · obtain ⟨K, hK⟩ : ∃ K, K = max (overallocationNat n.val.toNat)
              (n.val.toNat + 2 * delta.val.toNat + 1) := ⟨_, rfl⟩
          by_cases hs : n.val + delta.val < slots.length ∧
              ((K : Int) - (n.val + delta.val)) / 2 + 1 < slots.length - (n.val + delta.val)
          · exact growbeg_case_inplace l h' delta hd0 hov1 hslow hov K hK hs
          · exact growbeg_case_alloc l h' delta hd0 hov1 hslow hov K hK hs
        · have hplan : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
              .error .overflow := by
            have hovN : typemaxNat < n.val.toNat + 2 * delta.val.toNat + 1 := by
              unfold typemaxNat; omega
            simp only [growbegPlan, growbegInternalPlan, hdN, hov1N, hfastN, hovN, ite_false, ite_true]
            rfl
          exact growbegPost_error l delta _ hplan
            (growbeg_slow_run (layout := MemoryLayoutMetadata.ofRuntime l) h' delta hd0 hov1 hslow _ _
              (growbegInternal_overflow h' delta hd0 hov1 (by omega)))
    · have hplan : growbegPlan l ⟨slots.length, off.val.toNat, n.val.toNat⟩ delta.val.toNat =
          .error .overflow := by
        have hovN : typemaxNat < n.val.toNat + delta.val.toNat := by unfold typemaxNat; omega
        simp only [growbegPlan, hdN, hovN, ite_false, ite_true]
      exact growbegPost_error l delta _ hplan (growbeg_overflow_run h' delta hd0 (by omega))
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
variable {α : Type}

theorem integerValue_toInt {ops : round4.BigIntegerOps} (hops : ops.Lawful) (x : round4.IntegerValue) :
    x.toInt ops = if IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max then .ok (JInt.wrap .i64 x.val)
      else .error .inexact := by
  unfold round4.IntegerValue.toInt
  cases x with
  | bit t y =>
    simp only [round4.IntegerValue.convertTo, round4.IntegerValue.val, JuliaLean.base.int.convert,
      JInt.convert]
    split
    · rename_i h
      have h' : -9223372036854775808 ≤ y.val ∧ y.val ≤ 9223372036854775807 := h
      simp only [h.1, h.2, and_self, ite_true, Except.mapError]
      exact congrArg Except.ok (Subtype.ext (ival_wrap _ h').symm)
    · rename_i h
      simp only [h, ite_false, Except.mapError]
  | bool b =>
    simp only [round4.IntegerValue.convertTo, round4.IntegerValue.val, hops.1]
    split <;> rename_i h1 <;> split <;> rename_i h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  | big v =>
    simp only [round4.IntegerValue.convertTo, round4.IntegerValue.val, hops.1]
    by_cases h1 : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max <;> simp [h1]

theorem integerToInt_run {ops : round4.BigIntegerOps} (x : round4.IntegerValue) (s : MutableMemory α) :
    (round4.integerToInt ops x : MutationM α I).run s = (x.toInt ops, s) := rfl

theorem growend_neg_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat)
    (x : I) (hx : x.val < 0) :
    (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)) handle x).run s =
      (.error (.argument "grow requires delta >= 0"), s) := by
  have hn : ¬ (x ≥ zero) := by rw [ge_iff_le, jle_iff, ival_zero]; omega
  simp only [growend, stateExcept_bind, stateExcept_pure, hn, decide_false,
    Bool.not_false, ite_true, stateExcept_throw]
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
variable {α : Type}

/-- `jl_alloc_genericmemory`'s size checks on the shared heap are exactly `memoryFits`. -/
theorem heapAllocGenericMemory_run (l : MemoryLayout) (nel : Nat) (heap : VectorHeap α) :
    (allocGenericMemory (some l) (heapAllocate 0) heapAllocate nel).run heap =
      if memoryFits l nel then .ok (heap.length, heap ++ [List.replicate nel none])
      else .error (.argument genericMemorySizeMessage) := by
  by_cases hz : nel = 0
  · subst hz
    have hf : memoryFits l 0 := by unfold memoryFits maxIntVal; simp
    simp only [allocGenericMemory, ite_true, hf]
    rfl
  · cases l with
    | mk size isboxed isunion =>
      have hM : maxIntVal - 1 = 9223372036854775806 := rfl
      unfold memoryFits
      dsimp only
      simp only [allocGenericMemory, hz, ite_false, newGenericMemory]
      cases isboxed <;> cases isunion <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        sizeMulOverflow, sizeAddOverflow] <;> split <;> rename_i hg
      · rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, hM, Nat.reducePow] at hg; (try generalize nel * 8 = P at hg ⊢); omega)]; rfl
      · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, hM, Nat.reducePow] at hg; (try generalize nel * 8 = P at hg ⊢); omega)]; rfl
      · rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, hM, Nat.reducePow] at hg; (try generalize nel * 8 = P at hg ⊢); omega)]; rfl
      · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, hM, Nat.reducePow] at hg; (try generalize nel * 8 = P at hg ⊢); omega)]; rfl
      · rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, hM, Nat.reducePow] at hg; (try generalize nel * 8 = P at hg ⊢); omega)]; rfl
      · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, hM, Nat.reducePow] at hg; (try generalize nel * 8 = P at hg ⊢); omega)]; rfl
      · rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, hM, Nat.reducePow] at hg; (try generalize nel * 8 = P at hg ⊢); omega)]; rfl
      · rw [if_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, hM, Nat.reducePow] at hg; (try generalize nel * 8 = P at hg ⊢); omega)]; rfl

/-- `memorynew(T, n)` on the shared heap: a fresh object of `n` unassigned slots, or the size
`ArgumentError` for a negative or too large `n`. -/
theorem heapMemorynew_run (l : MemoryLayout) (n : I) (heap : VectorHeap α) :
    (memorynew (some l) (heapAllocate 0) heapAllocate n).run heap =
      if 0 ≤ n.val ∧ memoryFits l n.val.toNat then
        .ok (heap.length, heap ++ [List.replicate n.val.toNat none])
      else .error (.argument genericMemorySizeMessage) := by
  have hb := ival_bounds n
  simp only [memorynew, heapAllocGenericMemory_run]
  by_cases hn : 0 ≤ n.val
  · have hmod : (n.val % 2 ^ 64).toNat = n.val.toNat := by
      rw [Int.emod_eq_of_lt hn (by omega)]
    rw [hmod]
    simp only [hn, true_and]
  · have hmod : (n.val % 2 ^ 64).toNat = (n.val + 2 ^ 64).toNat := by
      rw [show n.val % 2 ^ 64 = n.val + 2 ^ 64 by omega]
    rw [hmod]
    have hf : ¬ memoryFits l (n.val + 2 ^ 64).toNat := by
      unfold memoryFits maxIntVal; omega
    simp only [hf, hn, ite_false, false_and]

theorem ule_typemax (x : I) :
    JuliaLean.base.int.ule_int typemaxInt x = decide (x.val < 0 ∨ x.val = 9223372036854775807) := by
  have htv : typemaxInt.val = 9223372036854775807 := ival_wrap _ (by decide)
  have hx : ((JuliaLean.C.fromJInt x).toNat : Int) = x.val % 18446744073709551616 := by
    rw [JuliaLean.Proofs.base.int.fromJInt_toNat]; rfl
  have ht : ((JuliaLean.C.fromJInt typemaxInt).toNat : Int) = 9223372036854775807 := by
    rw [JuliaLean.Proofs.base.int.fromJInt_toNat, htv]; rfl
  have hb := ival_bounds x
  simp only [JuliaLean.base.int.ule_int, JuliaLean.C.jlUleInt]
  by_cases hl : x.val < 0 ∨ x.val = 9223372036854775807
  · simp [hl]; omega
  · simp [hl]; omega

theorem checkedSmulInt_fst (a b : I) : (checkedSmulInt a b).1.val = wrapInt .i64 (a.val * b.val) :=
  JuliaLean.Proofs.base.int.mul_int_val a b

theorem checkedSmulInt_snd (a b : I) :
    (checkedSmulInt a b).2 =
      !decide (-9223372036854775808 ≤ a.val * b.val ∧ a.val * b.val ≤ 9223372036854775807) := rfl

theorem checkedSmulInt_exact (a b : I)
    (h : -9223372036854775808 ≤ a.val * b.val ∧ a.val * b.val ≤ 9223372036854775807) :
    (checkedSmulInt a b).1.val = a.val * b.val := by
  rw [checkedSmulInt_fst]; exact wrapInt_of_inRange .i64 _ h

/-- A dimension `checked_dims` rejects: negative, or `typemax(Int)`. -/
def badDim (x : I) : Prop := x.val < 0 ∨ x.val = 9223372036854775807

instance : DecidablePred badDim := fun x => by unfold badDim; infer_instance

/-- The product of the dimension values. -/
def dimProd (d : List I) : Int := (d.map (·.val)).prod

theorem loop_neg (rest : List I) : ∀ (a : I) (ov neg z : Bool),
    (neg = true ∨ ∃ x ∈ rest, badDim x) → (checkedMulDimsLoop rest a ov neg z).2 = true := by
  induction rest with
  | nil =>
    intro a ov neg z h
    rcases h with h | ⟨x, hx, _⟩
    · simp [checkedMulDimsLoop, h]
    · cases hx
  | cons di rest ih =>
    intro a ov neg z h
    simp only [checkedMulDimsLoop]
    apply ih
    rcases h with h | ⟨x, hx, hb⟩
    · left; simp [h]
    · rcases List.mem_cons.mp hx with he | hx'
      · left; subst he; simp only [ule_typemax]; unfold badDim at hb; simp [hb]
      · right; exact ⟨x, hx', hb⟩

/-- The loop with no rejected dimension: the overflow flag is `typemax(Int) < product`, and the
running value is the product otherwise. `Q` is the exact product so far. -/
theorem loop_good (rest : List I) : ∀ (a : I) (ov z : Bool) (Q : Int),
    0 ≤ Q → (∀ x ∈ rest, ¬ badDim x) →
    (ov = false → z = false → a.val = Q ∧ Q ≤ 9223372036854775807) →
    (ov = true → z = false → 9223372036854775807 < Q) →
    (z = true → Q = 0 ∧ a.val = 0) →
    (checkedMulDimsLoop rest a ov false z).2 = decide (9223372036854775807 < Q * dimProd rest) ∧
    ((checkedMulDimsLoop rest a ov false z).2 = false →
      (checkedMulDimsLoop rest a ov false z).1.val = Q * dimProd rest) := by
  induction rest with
  | nil =>
    intro a ov z Q hQ _ h1 h2 h3
    simp only [checkedMulDimsLoop, dimProd, List.map_nil, List.prod_nil, Int.mul_one,
      Bool.false_or]
    cases z
    · cases ov
      · obtain ⟨ha, hle⟩ := h1 rfl rfl
        have : ¬ 9223372036854775807 < Q := by omega
        simp [this, ha]
      · have := h2 rfl rfl
        simp [this]
    · obtain ⟨hq, ha⟩ := h3 rfl
      subst hq
      simp [ha]
  | cons di rest ih =>
    intro a ov z Q hQ hgood h1 h2 h3
    have hdi := hgood di (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, ¬ badDim x := fun x hx => hgood x (List.mem_cons_of_mem _ hx)
    unfold badDim at hdi
    have hdb := ival_bounds di
    have hab := ival_bounds a
    have hneg : JuliaLean.base.int.ule_int typemaxInt di = false := by
      rw [ule_typemax]; simp only [decide_eq_false_iff_not]; exact hdi
    have hprod : Q * dimProd (di :: rest) = (Q * di.val) * dimProd rest := by
      simp only [dimProd, List.map_cons, List.prod_cons]; rw [Int.mul_assoc]
    simp only [checkedMulDimsLoop, hneg, Bool.false_or]
    rw [hprod]
    have hQd : 0 ≤ Q * di.val := Int.mul_nonneg hQ (by omega)
    apply ih _ _ _ _ hQd hrest
    · -- no overflow, no zero yet
      intro hov hz
      simp only [Bool.or_eq_false_iff] at hov hz
      obtain ⟨hov0, hov1⟩ := hov
      obtain ⟨hz0, hz1⟩ := hz
      obtain ⟨ha, hle⟩ := h1 hov0 hz0
      rw [checkedSmulInt_snd, Bool.not_eq_false', decide_eq_true_eq] at hov1
      rw [checkedSmulInt_exact _ _ hov1, ha]
      exact ⟨rfl, by rw [← ha]; exact hov1.2⟩
    · intro hov hz
      simp only [Bool.or_eq_false_iff] at hz
      obtain ⟨hz0, hz1⟩ := hz
      have hd1 : 1 ≤ di.val := by simp at hz1; omega
      have hmono : Q ≤ Q * di.val := by
        have := Int.mul_nonneg hQ (show 0 ≤ di.val - 1 by omega)
        rw [Int.mul_sub, Int.mul_one] at this; omega
      cases ov
      · simp only [Bool.false_or, checkedSmulInt_snd, Bool.not_eq_true',
          decide_eq_false_iff_not] at hov
        obtain ⟨ha, _⟩ := h1 rfl hz0
        rw [ha] at hov
        omega
      · have := h2 rfl hz0; omega
    · intro hz
      cases hz0 : z
      · rw [hz0] at hz
        simp only [Bool.false_or, decide_eq_true_eq] at hz
        rw [hz, Int.mul_zero]
        refine ⟨rfl, ?_⟩
        rw [checkedSmulInt_fst, hz, Int.mul_zero]; rfl
      · obtain ⟨hq, ha⟩ := h3 hz0
        rw [hq, Int.zero_mul]
        refine ⟨rfl, ?_⟩
        rw [checkedSmulInt_fst, ha, Int.zero_mul]; rfl

/-- `_checked_mul_dims(d...)` for two or more dimensions. -/
theorem checkedMulDims_spec (d : List I) (hd : 2 ≤ d.length) :
    ((∃ x ∈ d, badDim x) → (checkedMulDims d).2 = true) ∧
    ((∀ x ∈ d, ¬ badDim x) →
      (checkedMulDims d).2 = decide (9223372036854775807 < dimProd d) ∧
      ((checkedMulDims d).2 = false → (checkedMulDims d).1.val = dimProd d)) := by
  match d, hd with
  | [m, n], _ =>
    have hmb := ival_bounds m
    have hnb := ival_bounds n
    simp only [checkedMulDims, checkedMulDims2, ule_typemax]
    refine ⟨fun ⟨x, hx, hb⟩ => ?_, fun hg => ?_⟩
    · unfold badDim at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [hb]
    · have hm := hg m (by simp)
      have hn := hg n (by simp)
      unfold badDim at hm hn
      have hp : 0 ≤ m.val * n.val := Int.mul_nonneg (by omega) (by omega)
      have hdp : dimProd [m, n] = m.val * n.val := by simp [dimProd]
      rw [hdp]
      simp only [hm, hn, decide_false, Bool.or_false, checkedSmulInt_snd]
      by_cases hle : m.val * n.val ≤ 9223372036854775807
      · have hr : -9223372036854775808 ≤ m.val * n.val ∧ m.val * n.val ≤ 9223372036854775807 :=
          ⟨by omega, hle⟩
        have : ¬ 9223372036854775807 < m.val * n.val := by omega
        simp only [hr, this, decide_true, decide_false, Bool.not_true, true_and]
        intro _
        exact checkedSmulInt_exact _ _ hr
      · have hr : ¬ (-9223372036854775808 ≤ m.val * n.val ∧ m.val * n.val ≤ 9223372036854775807) := by
          omega
        have : 9223372036854775807 < m.val * n.val := by omega
        simp [hr, this]
  | m :: n :: o :: rest, _ =>
    have hmb := ival_bounds m
    simp only [checkedMulDims, checkedMulDimsMany]
    refine ⟨fun ⟨x, hx, hb⟩ => ?_, fun hg => ?_⟩
    · rcases List.mem_cons.mp hx with he | hx'
      · subst he
        apply loop_neg
        left; rw [ule_typemax]; unfold badDim at hb; simp [hb]
      · exact loop_neg _ _ _ _ _ (Or.inr ⟨x, hx', hb⟩)
    · have hm := hg m (by simp)
      unfold badDim at hm
      have hneg : JuliaLean.base.int.ule_int typemaxInt m = false := by
        rw [ule_typemax]; simp only [decide_eq_false_iff_not]; exact hm
      rw [hneg]
      have hdp : dimProd (m :: n :: o :: rest) = m.val * dimProd (n :: o :: rest) := by
        simp [dimProd]
      rw [hdp]
      exact loop_good _ m false false m.val (by omega)
        (fun x hx => hg x (List.mem_cons_of_mem _ hx))
        (fun _ _ => ⟨rfl, by omega⟩) (fun h => by cases h) (fun h => by cases h)

theorem dimProd_nonneg (d : List I) (h : ∀ x ∈ d, 0 ≤ x.val) : 0 ≤ dimProd d := by
  induction d with
  | nil => simp [dimProd]
  | cons x d ih =>
    have hd : ∀ y ∈ d, 0 ≤ y.val := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have := ih hd
    simp only [dimProd, List.map_cons, List.prod_cons] at this ⊢
    exact Int.mul_nonneg (h x (List.mem_cons_self ..)) this

theorem dimProd_toNat (d : List I) (h : ∀ x ∈ d, 0 ≤ x.val) :
    ((d.map (·.val)).map Int.toNat).prod = (dimProd d).toNat := by
  induction d with
  | nil => simp [dimProd]
  | cons x d ih =>
    have hx := h x (List.mem_cons_self ..)
    have hd : ∀ y ∈ d, 0 ≤ y.val := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hp := dimProd_nonneg d hd
    simp only [List.map_cons, List.prod_cons, ih hd]
    simp only [dimProd, List.map_cons, List.prod_cons] at hp ⊢
    rw [Int.toNat_mul hx hp]


theorem memoryFits_zero (l : MemoryLayout) : memoryFits l 0 := by
  unfold memoryFits maxIntVal; simp

theorem arrayAllocError_many (l : MemoryLayout) (D : List I) (hD : 2 ≤ D.length) :
    arrayAllocError l (D.map (·.val)) =
      if (∃ x ∈ D, badDim x) ∨ 9223372036854775807 < dimProd D then
        some (Error.argument "invalid Array dimensions")
      else if ¬ memoryFits l (dimProd D).toNat then some (Error.argument genericMemorySizeMessage)
      else none := by
  have hlen : 2 ≤ (D.map (·.val)).length := by simpa using hD
  have hne : ∀ d, D.map (·.val) ≠ [d] := by
    intro d h; rw [h] at hlen; simp at hlen
  have hex : (∃ d ∈ D.map (·.val), d < 0 ∨ d = 9223372036854775807) ↔ ∃ x ∈ D, badDim x := by
    simp [badDim]
  unfold arrayAllocError
  split
  · rename_i d h; exact absurd h (hne d)
  · simp only [hlen, true_and, hex]
    rfl

/-- `Array{T,N}(undef, dims)` on the shared heap is `allocOutcome`. -/
theorem heapArrayUndef_run {Tag : Type} (layout : Tag → Option MemoryLayout) (target : Tag)
    (l : MemoryLayout) (hl : layout target = some l) (dims : List I) (heap : VectorHeap α) :
    (heapArrayUndef layout target dims).run heap = allocOutcome l target (dims.map (·.val)) heap := by
  have hdims : ∀ d : List I, (∀ x ∈ d, 0 ≤ x.val) →
      d.map (fun x => x.val.toNat) = (d.map (·.val)).map Int.toNat := by
    intro d _; simp
  match dims with
  | [m] =>
    have hb := ival_bounds m
    simp only [heapArrayUndef, arrayUndef, arrayUndef1, memoryUndef, hl, vector_bind_run,
      heapMemorynew_run]
    unfold allocOutcome arrayAllocError
    simp only [List.map_cons, List.map_nil]
    by_cases hc : 0 ≤ m.val ∧ memoryFits l m.val.toNat
    · have hneg : ¬ m.val < 0 := by omega
      simp only [hc, hneg, and_self, ite_true, ite_false, vector_pure_run, List.prod_cons,
        List.prod_nil, Nat.mul_one, not_true_eq_false, or_false]
    · have hc' : m.val < 0 ∨ ¬ memoryFits l m.val.toNat := by
        by_cases h0 : 0 ≤ m.val
        · exact Or.inr (fun hf => hc ⟨h0, hf⟩)
        · exact Or.inl (by omega)
      simp only [hc, hc', ite_true, ite_false]
  | [] =>
    simp only [heapArrayUndef, arrayUndef, arrayUndefN, newAsMemoryref, memoryUndef, checkedDims,
      checkedDims0, hl, vector_bind_run, vector_pure_run, heapMemorynew_run]
    have hone : (one : I).val = 1 := rfl
    unfold allocOutcome arrayAllocError
    by_cases hf : memoryFits l 1
    · simp only [hone, Int.toNat_one, hf, show (0 : Int) ≤ 1 by decide, and_self, ite_true]
      simp [hf]
    · simp only [hone, Int.toNat_one, hf, and_false, ite_false]
      simp [hf]
  | m :: n :: rest =>
    have hlen : 2 ≤ (m :: n :: rest).length := by simp
    obtain ⟨hbad, hgood⟩ := checkedMulDims_spec (m :: n :: rest) hlen
    have hcm :
        (arrayUndef (layout target) (heapAllocate 0) heapAllocate
          (fun handle ds => (pure ⟨handle, target, ds.map (·.val.toNat), ds.map (fun d => (1, d.val.toNat))⟩ :
            VectorM α (HeapArray Tag))) (m :: n :: rest)) =
        (do
          let mem ← newAsMemoryref (layout target) (heapAllocate 0) heapAllocate
            (← checkedDimsMany (m := VectorM α) (m :: n :: rest))
          pure ⟨mem, target, (m :: n :: rest).map (·.val.toNat),
            (m :: n :: rest).map (fun d => (1, d.val.toNat))⟩) := by
      match rest with
      | [] => rfl
      | [o] => rfl
      | _ :: _ :: _ => rfl
    simp only [heapArrayUndef]
    rw [hcm]
    simp only [checkedDimsMany, newAsMemoryref, memoryUndef, hl, vector_bind_run]
    unfold allocOutcome
    rw [arrayAllocError_many l (m :: n :: rest) hlen]
    by_cases hb : ∃ d ∈ m :: n :: rest, badDim d
    · have := hbad hb
      simp only [this, ite_true, hb, true_or, vector_bind_run, vector_throw_run, vector_pure_run]
    · have hg : ∀ x ∈ m :: n :: rest, ¬ badDim x := fun x hx h => hb ⟨x, hx, h⟩
      obtain ⟨hflag, hval⟩ := hgood hg
      by_cases hp : 9223372036854775807 < dimProd (m :: n :: rest)
      · have : (checkedMulDims (m :: n :: rest)).2 = true := by rw [hflag]; simp [hp]
        simp only [this, ite_true, hp, or_true, vector_bind_run, vector_throw_run, vector_pure_run]
      · have hf2 : (checkedMulDims (m :: n :: rest)).2 = false := by rw [hflag]; simp [hp]
        have hv := hval hf2
        have hnn : ∀ x ∈ m :: n :: rest, 0 ≤ x.val := fun x hx => by
          have := hg x hx; unfold badDim at this; omega
        have hp0 := dimProd_nonneg _ hnn
        have hprod : (List.map (Int.toNat ∘ fun x : I => x.val) (m :: n :: rest)).prod =
            (dimProd (m :: n :: rest)).toNat := by
          rw [← List.map_map]; exact dimProd_toNat _ hnn
        simp only [hf2, Bool.false_eq_true, ite_false, hb, hp, or_self, vector_bind_run, vector_throw_run, vector_pure_run, heapMemorynew_run]
        rw [hv]
        simp only [hp0, true_and, List.map_map, hprod]
        by_cases hfit : memoryFits l (dimProd (m :: n :: rest)).toNat
        · simp only [hfit, ite_true, not_true_eq_false, ite_false]
          rfl
        · simp only [hfit, ite_false, not_false_eq_true, ite_true]
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
section
variable {α : Type}


theorem prod_toNat_cast : ∀ (ds : List Int), (∀ d ∈ ds, 0 ≤ d) →
    (((ds.map Int.toNat).prod : Nat) : Int) = ds.prod ∧ 0 ≤ ds.prod := by
  intro ds
  induction ds with
  | nil => intro _; simp
  | cons d ds ih =>
    intro h
    have hd := h d (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.prod_cons]
    refine ⟨by rw [Int.natCast_mul, h1, Int.toNat_of_nonneg hd], Int.mul_nonneg hd h2⟩
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
variable {α : Type}

theorem growbegInternal_facts0 {layout : MemoryLayoutMetadata} {s : MutableMemory α}
    {handle mem : Nat} {off n : I} {slots : List (Option α)} (h : VecAt s handle mem off n slots)
    (delta : I) (hd : 0 ≤ delta.val)
    (hov : n.val + 2 * delta.val + 1 ≤ 9223372036854775807) :
    (n + delta).val = n.val + delta.val ∧
    ((mutableStorage layout).checkedAdd n delta).run s = (.ok (n + delta), s) ∧
    ((mutableStorage layout).checkedMul (JInt.wrap .i64 2) delta).run s =
      (.ok (JInt.wrap .i64 2 * delta), s) ∧
    ((mutableStorage layout).checkedAdd n (JInt.wrap .i64 2 * delta)).run s =
      (.ok (n + JInt.wrap .i64 2 * delta), s) ∧
    ((mutableStorage layout).checkedAdd (n + JInt.wrap .i64 2 * delta) one).run s =
      (.ok (n + JInt.wrap .i64 2 * delta + one), s) ∧
    (n + JInt.wrap .i64 2 * delta + one).val = n.val + 2 * delta.val + 1 := by
  obtain ⟨ha, hm, ho, hn0, he, hc⟩ := h
  have hnb := ival_bounds n
  have hdb := ival_bounds delta
  have h2d : (JInt.wrap .i64 2 * delta).val = 2 * delta.val := by
    rw [show JInt.wrap .i64 2 * delta = JInt.wrap .i64 ((JInt.wrap .i64 2).val * delta.val) from rfl,
      wval2']
    exact ival_wrap _ (by omega)
  have hn2d : (n + JInt.wrap .i64 2 * delta).val = n.val + 2 * delta.val := by
    rw [ival_add _ _ (by rw [h2d]; omega), h2d]
  refine ⟨ival_add _ _ (by omega), ms_checkedAdd_run s n delta (by omega),
    ms_checkedMul_run s _ delta (by rw [wval2']; omega),
    ms_checkedAdd_run s n _ (by rw [h2d]; omega),
    ms_checkedAdd_run s _ one (by rw [hn2d, ival_one]; omega), ?_⟩
  rw [ival_add _ _ (by rw [hn2d, ival_one]; omega), hn2d, ival_one]
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
open JuliaLean.Proofs.base.array.round6dcollect2
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
open JuliaLean.base.range (OneTo)
open JuliaLean.base.generator (IteratorSize)
section
variable {E U α R V A C X B Tag : Type}

theorem convertInteger_i64 {ops : BigIntegerOps} (hops : ops.Lawful) (x : IntegerValue) :
    JuliaLean.Proofs.base.array.round8.convertInteger ops .i64 x =
      if IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max then .ok (JInt.wrap .i64 x.val)
      else .error .inexact := by
  cases x with
  | bit t y =>
    simp only [JuliaLean.Proofs.base.array.round8.convertInteger, IntegerValue.val, JuliaLean.base.int.convert, JInt.convert]
    split
    · rename_i h
      have h' : -9223372036854775808 ≤ y.val ∧ y.val ≤ 9223372036854775807 := h
      simp only [h.1, h.2, and_self, ite_true, Except.mapError]
      exact congrArg Except.ok (Subtype.ext (ival_wrap _ h').symm)
    · rename_i h
      simp only [h, ite_false, Except.mapError]
  | bool b =>
    have hb : IntTy.i64.min ≤ (IntegerValue.bool b).val ∧ (IntegerValue.bool b).val ≤ IntTy.i64.max := by
      cases b <;> decide
    rw [if_pos hb]
    cases b <;> rfl
  | big v =>
    simp only [JuliaLean.Proofs.base.array.round8.convertInteger, IntegerValue.val, hops.1]
    by_cases h1 : IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max <;> simp [h1]
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt


theorem dims_cast_toNat (ds : List Nat) : (ds.map (fun n : Nat => (n : Int))).map Int.toNat = ds := by
  simp [List.map_map, Function.comp_def]

theorem dims_wrap_val (dims : List Nat) (hfit : heapDimensionsFit dims = true) :
    (dims.map (fun n : Nat => JInt.wrap .i64 (Int.ofNat n))).map (·.val) =
      dims.map (fun n : Nat => (n : Int)) := by
  revert hfit
  induction dims with
  | nil => intro _; rfl
  | cons n ns ih =>
    intro hfit
    have htail : heapDimensionsFit ns = true := by
      apply List.all_eq_true.mpr
      intro value hvalue
      exact List.all_eq_true.mp hfit value (List.mem_cons_of_mem n hvalue)
    exact List.cons_eq_cons.mpr
      ⟨heapNatDimension_value (n :: ns) hfit n (by simp), ih htail⟩
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- `checkbounds(a, i)` on a vector window of length `n`. -/
theorem vwBounds_run (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i : I) :
    (mutableBounds handle i).run s =
      (if 1 ≤ i.val ∧ i.val ≤ n.val then .ok () else .error .bounds, s) := by
  have hlen := mutableLength_run s handle _ h.1
  by_cases hi : 1 ≤ i.val ∧ i.val ≤ n.val
  · have hin : (one ≤ i ∧ i ≤ n) := ⟨by rw [jle_iff, ival_one]; omega, by rw [jle_iff]; omega⟩
    simp only [mutableBounds, mutableInBounds, stateExcept_bind, hlen, stateExcept_pure, hin,
      and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, hi, ite_true]
  · have hin : ¬ (one ≤ i ∧ i ≤ n) := by
      rw [jle_iff, jle_iff, ival_one]; exact hi
    simp only [mutableBounds, mutableInBounds, stateExcept_bind, hlen, stateExcept_pure, hin,
      decide_false, Bool.not_false, ite_true, hi, ite_false, stateExcept_throw]

/-- `_push_deleted!(Nowhere(), a, i)` reads slot `i` and changes nothing. -/
theorem vwPushNowhere_run (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i : I)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val) :
    (pushDeleted mutableAssigned mutableGet (fun (_ : Unit) x => pure (pushNowhere x))
      (fun (_ : Unit) d => pure (growendNowhere d)) () handle i).run s = (.ok (), s) := by
  have hasg := vwAssigned_run s handle mem off n slots h i hi
  have hget := vwGet_run s handle mem off n slots h i hi
  have hwl := vwWindow_length h
  have hlt : (i.val - 1).toNat < (vwWindow slots off n).length := by rw [hwl]; omega
  obtain ⟨v, hv⟩ : ∃ v, (vwWindow slots off n)[(i.val - 1).toNat]? = some v :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  rw [hv] at hasg hget
  cases v with
  | some x =>
    simp only [pushDeleted, stateExcept_bind, hasg, Option.join_some, Option.isSome_some, ite_true,
      hget, stateExcept_pure]
  | none =>
    simp only [pushDeleted, stateExcept_bind, hasg, Option.join_some, Option.isSome_none,
      Bool.false_eq_true, ite_false, stateExcept_pure]
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- `_deleteat!` reaching an index `i` after the valid sorted indices `pre` (last `j0`) with
`i ≤ j0` or `i > length(a)`. -/


theorem deleteatList_eq (layout : MemoryLayoutMetadata) (a : Nat) (inds : List I) :
    (mutableDeleteatList (α := α) layout a inds) =
      deleteatIterator (m := MutationM α) mutableLength (listIterator inds) Subtype.val
        (· + one) mutableBounds
        (pushDeleted mutableAssigned mutableGet (fun (_ : Unit) x => pure (pushNowhere x))
          (fun (_ : Unit) d => pure (growendNowhere d)))
        (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)) (· - ·)
        (deleteend (mutableStorage layout) pure) a () := rfl

theorem deleteatVector_run (layout : MemoryLayoutMetadata) (a : Nat) (inds : List I)
    (s : MutableMemory α) :
    (mutableDeleteatVector layout a inds).run s = (mutableDeleteatList layout a inds).run s := by
  simp only [mutableDeleteatVector, deleteatIndexVector, stateExcept_bind, stateExcept_pure]
  rfl
end
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4 JuliaLean.Proofs.base.array.round7
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 1000000

theorem deleteOne_run {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i delta : I)
    (hi1 : 1 ≤ i.val) (hin : i.val ≤ n.val)
    (hdv : delta.val = 1) :
    ∃ next, (vecDeleteat α (layout := layout) handle i delta).run s = (.ok (), next) ∧ next.validVector handle ∧
      next.contents handle = (vwWindow slots off n).take (i.val - 1).toNat ++
        (vwWindow slots off n).drop (i.val - 1 + delta.val).toNat ∧
      ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']? := by
  have hd : 0 ≤ delta.val := by omega
  have hdi : delta.val ≤ n.val + 1 - i.val := by rw [hdv]; omega
  have hnb := ival_bounds n
  have hib := ival_bounds i
  have hdb := ival_bounds delta
  have hn0 := h.2.2.2.1
  have hwl := vwWindow_length h
  have hlen := mutableLength_run s handle _ h.1
  have hin' : (one ≤ i ∧ i ≤ n) := ⟨by rw [jle_iff, ival_one]; exact hi1, by rw [jle_iff]; exact hin⟩
  have hl1 : (n + one - i).val = n.val + 1 - i.val := by
    rw [ival_add_sub n one i (by rw [ival_one]; omega), ival_one]
  have hcnt : delta.val ≤ (n + one - i).val := by rw [hl1]; exact hdi
  by_cases hbr : JInt.wrap .i64 2 * i + delta ≤ n
  · have hle := hbr
    have h1d : (one + delta).val = 1 + delta.val := by
      rw [ival_add _ _ (by rw [ival_one]; omega), ival_one]
    have him : (i - one).val = i.val - 1 := ival_sub_one i (by omega)
    obtain ⟨slots1, hcp, hv1, hw1⟩ := vwCopy_run s handle mem off n slots h (one + delta) one
      (i - one) (by rw [him]; omega) (by rw [h1d]; omega) (by rw [h1d, him]; omega)
      (by rw [ival_one]; exact Int.le_refl 1) (by rw [ival_one, him]; omega)
    obtain ⟨next, off', slots', hdel, hv2, _, harr, hw2⟩ :=
      vwDeletebeg_run (layout := layout) _ handle mem off n slots1 hv1 delta hd (by omega)
    refine ⟨next, ?_, hv2.valid, ?_, ?_⟩
    · simp only [vecDeleteat, deleteatWindow, stateExcept_bind, stateExcept_pure, hlen, hd,
        decide_true, Bool.not_true, Bool.false_eq_true, ite_false, hin', and_self, hcnt, hle,
        eq_self_iff_true, ite_true, hcp, hdel]
    · rw [hv2.contents, hw2, hw1, h1d, him, ival_one]
      rw [show (1 + delta.val - 1).toNat = delta.val.toNat by omega,
        show ((1 : Int) - 1).toNat = 0 by rfl,
        show (1 + delta.val - 1 + (i.val - 1)).toNat = delta.val.toNat + (i.val - 1).toNat by omega,
        show (i.val - 1 + delta.val).toNat = (i.val - 1).toNat + delta.val.toNat by omega]
      have := window_drop_prefix (vwWindow slots off n) delta.val.toNat (i.val.toNat) n.val.toNat
        hwl (by omega) (by omega)
      rw [show i.val.toNat - 1 = (i.val - 1).toNat by omega] at this
      exact this
    · intro h' hne
      rw [harr, List.getElem?_set_ne (by omega)]
  · have hgt := hbr
    have himax : i.val < 9223372036854775807 := by
      by_cases hip : i.val < 9223372036854775807
      · exact hip
      · have hib' := i.property
        have him : i.val = 9223372036854775807 := by
          change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at hib'
          omega
        have hnm : n.val = 9223372036854775807 := by
          have hnb' := n.property
          change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hnb'
          omega
        have hieq : i = JInt.typemax .i64 := Subtype.ext him
        have hneq : n = JInt.typemax .i64 := Subtype.ext hnm
        have hdeq : delta = one := Subtype.ext (hdv.trans ival_one.symm)
        have hyes : JInt.wrap .i64 2 * i + delta ≤ n := by
          rw [hieq, hneq, hdeq]
          decide
        exact (hbr hyes).elim
    have hid : (i + delta).val = i.val + delta.val := ival_add _ _ (by omega)
    have hn1d : (n + one - delta).val = n.val + 1 - delta.val := by
      rw [ival_add_sub n one delta (by rw [ival_one]; omega), ival_one]
    have hk : (n + one - delta - i).val = n.val + 1 - delta.val - i.val := by
      rw [ival_sub _ _ (by rw [hn1d]; omega), hn1d]
    obtain ⟨slots1, hcp, hv1, hw1⟩ := vwCopy_run s handle mem off n slots h i (i + delta)
      (n + one - delta - i) (by rw [hk]; omega) hi1 (by rw [hk]; omega) (by rw [hid]; omega)
      (by rw [hid, hk]; omega)
    obtain ⟨next, slots', hdel, hv2, _, harr, hw2⟩ :=
      vwDeleteend_run (layout := layout) _ handle mem off n slots1 hv1 delta hd (by omega) (by omega)
    refine ⟨next, ?_, hv2.valid, ?_, ?_⟩
    · simp only [vecDeleteat, deleteatWindow, stateExcept_bind, stateExcept_pure, hlen, hd,
        decide_true, Bool.not_true, Bool.false_eq_true, ite_false, hin', and_self, hcnt, hgt,
        decide_false, hcp, hdel]
    · rw [hv2.contents, hw2, hw1, hid, hk]
      rw [show (i.val + delta.val - 1).toNat = i.val.toNat + delta.val.toNat - 1 by omega,
        show (n.val + 1 - delta.val - i.val).toNat = n.val.toNat + 1 - delta.val.toNat - i.val.toNat
          by omega,
        show (i.val - 1 + (n.val + 1 - delta.val - i.val)).toNat =
          (i.val.toNat - 1) + (n.val.toNat + 1 - delta.val.toNat - i.val.toNat) by omega,
        show (n.val - delta.val).toNat = n.val.toNat - delta.val.toNat by omega,
        show (i.val - 1).toNat = i.val.toNat - 1 by omega,
        show (i.val - 1 + delta.val).toNat = i.val.toNat - 1 + delta.val.toNat by omega]
      exact window_drop_suffix (vwWindow slots off n) delta.val.toNat i.val.toNat n.val.toNat
        hwl (by omega) (by omega)
    · intro h' hne
      rw [harr, List.getElem?_set_ne (by omega)]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 1000000

theorem convertingSet_eq (already : α → Bool) (convert : α → Except Error α)
    (a : Nat) (x : α) (i : I) :
    (do let _ ← setindexScalar already id (fun v => stateExceptLift (convert v)) mutableTypedSet a x i
        pure ()) =
      (do let value ← stateExceptLift (storedValue already convert x); mutableSet a value i) := by
  unfold setindexScalar storedValue
  cases hx : already x <;>
    simp only [hx, Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc, mutableSet,
      mutableTypedSet]
  all_goals rfl
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth

theorem growat_one_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadExceptOf Error m]
    (st : Storage m A Mem R) (growb growe : A → I → m Unit) (a : A) (d : I) :
    growat st pure pure growb growe a one d = growb a d := by
  simp only [growat, pure_bind, ite_true]

theorem growat_one_plan (l : DictLayout) (s : MutableMemory α) (a mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (d : I) (hd : 0 ≤ d.val) :
    Follows s (growatPlan l (geometryOf s a) 1 d.val.toNat)
      ((growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a one d).run s)
      (fun _ next => next.validVector a ∧
        ((next.contents a).length : Int) = (s.contents a).length + d.val ∧
        (next.contents a).drop d.val.toNat = s.contents a ∧
        (∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) ∧
        ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) := by
  rw [growat_one_eq, opusGrowth.VecAt.geometry h]
  simp only [growatPlan, ite_true]
  obtain ⟨herr, hok⟩ := growbeg_plan l h d hd
  refine ⟨herr, fun g hg => ?_⟩
  obtain ⟨next,mem',off',slots',hr,hv,harrays,hlen,hwindow,_,_,hOther,_⟩ := hok g hg
  refine ⟨(),next,hr,hv.valid,?_,?_,?_,hOther⟩
  · rw [hv.contents, vwWindow_length hv, hlen, h.contents, vwWindow_length h]
    have := h.2.2.2.1
    omega
  · rw [hv.contents, hwindow, h.contents]
  · intro other hne
    rw [harrays,List.getElem?_set_ne (by omega)]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 2000000

theorem growat_endroom_run (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (a mem : Nat) (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hpref : n.val / 2 < i.val) (hroom : off.val - 1 + n.val + d.val ≤ (slots.length : Int)) :
    ∃ next result,
      (growat (mutableStorage layout) pure pure
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i d).run s =
        (.ok (), next) ∧ VecAt next a mem off (n+d) result ∧
      next.arrays = s.arrays.set a ⟨(mem,off),n+d⟩ ∧ result.length = slots.length ∧
      result = vwUnset (unsetRuntime := layout.runtime) (slots.take ((off-one+d+i).val-1).toNat ++
        (slots.drop ((off-one+i).val-1).toNat).take (n-i+one).val.toNat ++
        slots.drop ((off-one+d+i).val-1+(n-i+one).val).toNat) off (intRange i (i+d-one)) ∧
      ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]? := by
  have ho := h.2.2.1
  have hn := h.2.2.2.1
  have he := h.2.2.2.2.1
  have hc := h.2.2.2.2.2
  have hm := h.2.1
  have ha := h.1
  have hnb := ival_bounds n
  have hob := ival_bounds off
  have hdb := ival_bounds d
  have hib := ival_bounds i
  have hmem := mutableMemLength_run (layout := layout) s mem slots hm
  have hM : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hnd : (n+d).val = n.val+d.val := ival_add _ _ (by omega)
  have hom : (off-one).val = off.val-1 := ival_sub_one off (by omega)
  have hsum : (off-one+(n+d)).val = off.val-1+n.val+d.val := by
    rw [ival_add _ _ (by rw [hom,hnd]; omega),hom,hnd]; omega
  have hca := ms_checkedAdd_run (layout := layout) s n d (by omega)
  have hcb := ms_checkedAdd_run (layout := layout) s (off-one) (n+d) (by rw [hom,hnd]; omega)
  have hdiv := ms_divide_run (layout := layout) s n (JInt.wrap .i64 2) (by rw [wval2]; decide)
  have hQ : (JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)).val = n.val/2 := by
    rw [wval2]
    exact tdiv_nonneg_val n 2 hn (by decide) (by decide)
  have hi1 : i ≠ one := by intro hh; have := congrArg Subtype.val hh; rw [ival_one] at this; omega
  have hend : ¬ (n < JInt.typemax .i64 ∧ i = n+one) := by
    intro hh
    have hn1 : (n+one).val = n.val+1 := ival_add_one n (by
      have := hh.1
      change n.val < (JInt.typemax .i64).val at this
      have hmax : (JInt.typemax .i64).val = 9223372036854775807 := by decide
      rw [hmax] at this; omega)
    have := congrArg Subtype.val hh.2
    rw [hn1] at this
    omega
  have hendb : (decide (n < JInt.typemax .i64) && decide (i = n+one)) = false := by
    by_cases hnless : n < JInt.typemax .i64
    · have hne : i ≠ n+one := fun hh => hend ⟨hnless,hh⟩
      simp only [hnless,decide_true,hne,decide_false,Bool.true_and]
    · simp only [hnless,decide_false,Bool.false_and]
  have hd0 : d ≥ zero := by rw [ge_iff_le,jle_iff,ival_zero]; exact hd
  have hirange : one < i ∧ i ≤ n := by rw [jlt_iff,jle_iff,ival_one]; exact ⟨hi,hin⟩
  have hp : ¬ (i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)) := by rw [jle_iff,hQ]; omega
  have hfit : off-one+(n+d) ≤ JInt.wrap .i64 (slots.length : Int) := by rw [jle_iff,hsum,hM]; exact hroom
  have hod : (off-one+d).val = off.val-1+d.val := by
    rw [ival_add _ _ (by rw [hom]; omega),hom]
  have hdest : (off-one+d+i).val = off.val-1+d.val+i.val := by
    rw [ival_add _ _ (by rw [hod]; omega),hod]
  have hsrc : (off-one+i).val = off.val-1+i.val := by
    rw [ival_add _ _ (by rw [hom]; omega),hom]
  have hnmi : (n-i).val = n.val-i.val := ival_sub _ _ (by omega)
  have hk : (n-i+one).val = n.val-i.val+1 := by
    rw [ival_add_one (n-i) (by rw [hnmi]; omega),hnmi]
  let D := slots.take ((off-one+d+i).val-1).toNat ++
    (slots.drop ((off-one+i).val-1).toNat).take (n-i+one).val.toNat ++
    slots.drop ((off-one+d+i).val-1+(n-i+one).val).toNat
  have hmove := vwMemoryMove_run s mem mem (off-one+d+i) (off-one+i) (n-i+one) slots slots
    hm hm (by rw [hk]; omega) (by rw [hdest]; omega) (by rw [hdest,hk]; omega)
    (by rw [hsrc]; omega) (by rw [hsrc,hk]; omega) hc
  have hDl : D.length = slots.length := by
    simp only [D,List.length_append,List.length_take,List.length_drop,hdest,hsrc,hk]
    omega
  let mid : MutableMemory α := {s with memories := s.memories.set mem D}
  have hmlt := (List.getElem?_eq_some_iff.mp hm).choose
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hm1 : VecAt mid a mem off n D :=
    ⟨ha,List.getElem?_set_self hmlt,ho,hn,by rw [hDl]; exact he,by rw [hDl]; exact hc⟩
  have hsize := vwSetSize_run (layout := layout) mid a mem off n D hm1 (n+d)
  let mid2 : MutableMemory α := {mid with arrays := s.arrays.set a ⟨(mem,off),n+d⟩}
  have hm2 : VecAt mid2 a mem off (n+d) D :=
    ⟨List.getElem?_set_self halt,List.getElem?_set_self hmlt,ho,by rw [hnd]; omega,
      by rw [hDl,hnd]; omega,by rw [hDl]; exact hc⟩
  have hstop : (i+d-one).val = i.val+d.val-1 := by
    rw [ival_add_sub_one i d (by omega)]
  have hjs : ∀ j ∈ intRange i (i+d-one), 1 ≤ j.val ∧ j.val ≤ (n+d).val := by
    intro j hj
    have hjb := intRange_mem i (i+d-one) j hj
    rw [hstop] at hjb
    rw [hnd]
    omega
  have hloop := vwUnsetLoop_run (unsetRuntime := layout.runtime) a mem off (n+d) (intRange i (i+d-one)) mid2 D hm2 hjs
  let final : MutableMemory α := {mid2 with memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) D off (intRange i (i+d-one)))}
  have hv : VecAt final a mem off (n+d) (vwUnset (unsetRuntime := layout.runtime) D off (intRange i (i+d-one))) :=
    ⟨List.getElem?_set_self halt,List.getElem?_set_self hmlt,ho,hm2.2.2.2.1,
      by rw [vwUnset_length]; exact hm2.2.2.2.2.1,
      by rw [vwUnset_length]; exact hm2.2.2.2.2.2⟩
  have hOther : ∀ m, m < s.memories.length → m ≠ mem → final.memories[m]? = s.memories[m]? := by
    intro m _ hne
    change (s.memories.set mem _)[m]? = s.memories[m]?
    exact List.getElem?_set_ne (Ne.symm hne)
  refine ⟨final,_,?_,hv,rfl,(by rw [vwUnset_length,hDl]),rfl,hOther⟩
  dsimp only [mid,D] at hsize
  dsimp only [mid2,mid,D] at hloop
  simp only [List.set_set] at hloop
  simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,
    mutableLength_run s a _ ha,hendb,hd0,decide_true,Bool.not_true,Bool.false_eq_true,
    hirange,and_self,ms_length,ms_ref,ms_memory,ms_offset,mutableRef_run s a _ ha,
    hmem,hca,hcb,hdiv,hp,decide_false,Bool.false_and,Bool.not_false,hfit,
    Bool.true_and,ite_true,ms_copyMemory,hmove,hsize,ms_unsetArray,hloop]
  simp only [final,mid2,mid,D,List.set_set]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 2000000

theorem growat_startroom_run (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (a mem : Nat) (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hpref : i.val ≤ n.val / 2) (hstart : d.val ≤ off.val-1)
    (hov : off.val-1+n.val+d.val ≤ 9223372036854775807) :
    ∃ next result,
      (growat (mutableStorage layout) pure pure
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i d).run s =
        (.ok (), next) ∧ VecAt next a mem (off-d) (n+d) result ∧
      next.arrays = s.arrays.set a ⟨(mem,off-d),n+d⟩ ∧ result.length = slots.length ∧
      result = vwUnset (unsetRuntime := layout.runtime) (slots.take ((off-d).val-1).toNat ++
        (slots.drop (off.val-1).toNat).take i.val.toNat ++
        slots.drop ((off-d).val-1+i.val).toNat) (off-d) (intRange i (i+d-one)) ∧
      ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]? := by
  have ho := h.2.2.1
  have hn := h.2.2.2.1
  have he := h.2.2.2.2.1
  have hc := h.2.2.2.2.2
  have hm := h.2.1
  have ha := h.1
  have hnb := ival_bounds n
  have hob := ival_bounds off
  have hdb := ival_bounds d
  have hib := ival_bounds i
  have hmem := mutableMemLength_run (layout := layout) s mem slots hm
  have hM : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hnd : (n+d).val = n.val+d.val := ival_add _ _ (by omega)
  have hom : (off-one).val = off.val-1 := ival_sub_one off (by omega)
  have hsum : (off-one+(n+d)).val = off.val-1+n.val+d.val := by
    rw [ival_add _ _ (by rw [hom,hnd]; omega),hom,hnd]; omega
  have hca := ms_checkedAdd_run (layout := layout) s n d (by omega)
  have hcb := ms_checkedAdd_run (layout := layout) s (off-one) (n+d) (by rw [hom,hnd]; omega)
  have hdiv := ms_divide_run (layout := layout) s n (JInt.wrap .i64 2) (by rw [wval2]; decide)
  have hQ : (JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)).val = n.val/2 := by
    rw [wval2]
    exact tdiv_nonneg_val n 2 hn (by decide) (by decide)
  have hi1 : i ≠ one := by intro hh; have := congrArg Subtype.val hh; rw [ival_one] at this; omega
  have hend : ¬ (n < JInt.typemax .i64 ∧ i = n+one) := by
    intro hh
    have hn1 : (n+one).val = n.val+1 := ival_add_one n (by
      have := hh.1
      change n.val < (JInt.typemax .i64).val at this
      have hmax : (JInt.typemax .i64).val = 9223372036854775807 := by decide
      rw [hmax] at this; omega)
    have := congrArg Subtype.val hh.2
    rw [hn1] at this
    omega
  have hendb : (decide (n < JInt.typemax .i64) && decide (i = n+one)) = false := by
    by_cases hnless : n < JInt.typemax .i64
    · have hne : i ≠ n+one := fun hh => hend ⟨hnless,hh⟩
      simp only [hnless,decide_true,hne,decide_false,Bool.true_and]
    · simp only [hnless,decide_false,Bool.false_and]
  have hd0 : d ≥ zero := by rw [ge_iff_le,jle_iff,ival_zero]; exact hd
  have hirange : one < i ∧ i ≤ n := by rw [jlt_iff,jle_iff,ival_one]; exact ⟨hi,hin⟩
  have hp : i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val) := by rw [jle_iff,hQ]; exact hpref
  have hsp : d ≤ off-one := by rw [jle_iff,hom]; exact hstart
  have hno : (off-d).val = off.val-d.val := ival_sub _ _ (by omega)
  let D := slots.take ((off-d).val-1).toNat ++
    (slots.drop (off.val-1).toNat).take i.val.toNat ++
    slots.drop ((off-d).val-1+i.val).toNat
  have hmove := vwMemoryMove_run s mem mem (off-d) off i slots slots hm hm
    (by omega) (by rw [hno]; omega) (by rw [hno]; omega) ho (by omega) hc
  have hDl : D.length = slots.length := by
    simp only [D,List.length_append,List.length_take,List.length_drop,hno]
    omega
  let mid : MutableMemory α := {s with memories := s.memories.set mem D}
  have hmlt := (List.getElem?_eq_some_iff.mp hm).choose
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hm1 : VecAt mid a mem off n D :=
    ⟨ha,List.getElem?_set_self hmlt,ho,hn,by rw [hDl]; exact he,by rw [hDl]; exact hc⟩
  have href := vwSetRef_run (layout := layout) mid a mem off n D hm1 (mem,off-d)
  let midref : MutableMemory α := {mid with arrays := s.arrays.set a ⟨(mem,off-d),n⟩}
  have hmr : VecAt midref a mem (off-d) n D :=
    ⟨List.getElem?_set_self halt,List.getElem?_set_self hmlt,by rw [hno]; omega,hn,
      by rw [hDl,hno]; omega,by rw [hDl]; exact hc⟩
  have hsize := vwSetSize_run (layout := layout) midref a mem (off-d) n D hmr (n+d)
  let mid2 : MutableMemory α := {midref with arrays := s.arrays.set a ⟨(mem,off-d),n+d⟩}
  have hm2 : VecAt mid2 a mem (off-d) (n+d) D :=
    ⟨List.getElem?_set_self halt,List.getElem?_set_self hmlt,by rw [hno]; omega,
      by rw [hnd]; omega,by rw [hDl,hno,hnd]; omega,by rw [hDl]; exact hc⟩
  have hstop : (i+d-one).val = i.val+d.val-1 := by
    rw [ival_add_sub_one i d (by omega)]
  have hjs : ∀ j ∈ intRange i (i+d-one), 1 ≤ j.val ∧ j.val ≤ (n+d).val := by
    intro j hj
    have hjb := intRange_mem i (i+d-one) j hj
    rw [hstop] at hjb
    rw [hnd]
    omega
  have hloop := vwUnsetLoop_run (unsetRuntime := layout.runtime) a mem (off-d) (n+d) (intRange i (i+d-one)) mid2 D hm2 hjs
  let final : MutableMemory α := {mid2 with memories := s.memories.set mem (vwUnset (unsetRuntime := layout.runtime) D (off-d) (intRange i (i+d-one)))}
  have hv : VecAt final a mem (off-d) (n+d) (vwUnset (unsetRuntime := layout.runtime) D (off-d) (intRange i (i+d-one))) :=
    ⟨List.getElem?_set_self halt,List.getElem?_set_self hmlt,hm2.2.2.1,hm2.2.2.2.1,
      by rw [vwUnset_length]; exact hm2.2.2.2.2.1,
      by rw [vwUnset_length]; exact hm2.2.2.2.2.2⟩
  have hOther : ∀ m, m < s.memories.length → m ≠ mem → final.memories[m]? = s.memories[m]? := by
    intro m _ hne
    change (s.memories.set mem _)[m]? = s.memories[m]?
    exact List.getElem?_set_ne (Ne.symm hne)
  refine ⟨final,_,?_,hv,rfl,(by rw [vwUnset_length,hDl]),rfl,hOther⟩
  dsimp only [mid,D] at href
  dsimp only [midref,mid,D] at hsize
  dsimp only [mid2,midref,mid,D] at hloop
  simp only [List.set_set] at hsize hloop
  simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,
    mutableLength_run s a _ ha,hendb,hd0,decide_true,Bool.not_true,Bool.false_eq_true,
    hirange,and_self,ms_length,ms_ref,ms_memory,ms_offset,mutableRef_run s a _ ha,
    hmem,hca,hcb,hdiv,hp,hsp,Bool.true_and,ite_true,ms_memoryref,ms_copyRef,
    hmove,href,hsize,ms_unsetArray,hloop]
  simp only [final,mid2,midref,mid,D,List.set_set]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth

theorem shiftedSuffix_window {β : Type} (slots : List β) (o n i d : Nat)
    (hi : 1 ≤ i) (hin : i ≤ n) (hroom : o+n+d ≤ slots.length) :
    ((slots.take (o+(i+d-1)) ++
      (slots.drop (o+i-1)).take (n-i+1) ++ slots.drop (o+n+d)).drop o).take (n+d) =
      ((slots.drop o).take (n+d)).take (i+d-1) ++ ((slots.drop o).take n).drop (i-1) := by
  have hX : ((slots.drop (o+i-1)).take (n-i+1)).length = n-i+1 := by
    simp only [List.length_take,List.length_drop]
    omega
  have hcap : o+(n+d) ≤ slots.length := by omega
  have hwrite : i+d-1+(n-i+1) ≤ n+d := by omega
  have hsp := splice_window (sl := slots)
    (X := (slots.drop (o+i-1)).take (n-i+1)) (o := o) (d := i+d-1)
    (k := n-i+1) (nA := n+d) (hlen := hcap) (hd := hwrite) (hX := hX)
  have he : o+(i+d-1)+(n-i+1) = o+n+d := by omega
  rw [he] at hsp
  rw [hsp]
  have hlen : ((slots.drop o).take (n+d)).length = n+d := by
    simp only [List.length_take,List.length_drop]
    omega
  have hzero : (((slots.drop o).take (n+d)).drop ((i+d-1)+(n-i+1))) = [] :=
    List.drop_eq_nil_of_le (by rw [hlen]; omega)
  rw [hzero,List.append_nil]
  have hdrop : ((slots.drop o).take n).drop (i-1) = (slots.drop (o+i-1)).take (n-i+1) := by
    rw [List.drop_take,List.drop_drop]
    congr 2 <;> omega
  rw [hdrop]

theorem shiftedSuffix_sides {β : Type} (slots : List β) (o n i d : Nat)
    (hi : 1 ≤ i) (hin : i ≤ n) (hroom : o+n+d ≤ slots.length) :
    let w := ((slots.take (o+(i+d-1)) ++
      (slots.drop (o+i-1)).take (n-i+1) ++ slots.drop (o+n+d)).drop o).take (n+d)
    w.take (i-1) = ((slots.drop o).take n).take (i-1) ∧
    w.drop (i+d-1) = ((slots.drop o).take n).drop (i-1) := by
  dsimp only
  rw [shiftedSuffix_window slots o n i d hi hin hroom]
  have hp : (((slots.drop o).take (n+d)).take (i+d-1)).length = i+d-1 := by
    simp only [List.length_take,List.length_drop]
    omega
  constructor
  · rw [List.take_append_of_le_length (by rw [hp]; omega)]
    simp only [List.take_take]
    congr 1 <;> omega
  · rw [List.drop_append_of_le_length (by rw [hp]; omega)]
    rw [List.drop_eq_nil_of_le (by rw [hp]; omega)]
    rfl

theorem shiftedPrefix_sides {β : Type} (slots : List β) (o n i d : Nat)
    (hi : 1 ≤ i) (hin : i ≤ n) (hd : d ≤ o) (hroom : o+n ≤ slots.length) :
    let w := ((slots.take (o-d) ++ (slots.drop o).take i ++
      slots.drop (o-d+i)).drop (o-d)).take (n+d)
    w.take (i-1) = ((slots.drop o).take n).take (i-1) ∧
    w.drop (i+d-1) = ((slots.drop o).take n).drop (i-1) := by
  dsimp only
  have hX : ((slots.drop o).take i).length = i := by
    simp only [List.length_take,List.length_drop]
    omega
  have hcap : o-d+(n+d) ≤ slots.length := by omega
  have hwrite : 0+i ≤ n+d := by omega
  have hsp := splice_window (sl := slots) (X := (slots.drop o).take i)
    (o := o-d) (d := 0) (k := i) (nA := n+d)
    (hlen := hcap) (hd := hwrite) (hX := hX)
  simp only [Nat.add_zero,Nat.zero_add,List.take_zero,List.nil_append] at hsp
  rw [hsp]
  constructor
  · rw [List.take_append_of_le_length (by rw [hX]; omega)]
    simp only [List.take_take]
    congr 1 <;> omega
  · by_cases hz : d = 0
    · subst d
      simp only [Nat.add_zero,Nat.sub_zero]
      have hx : (slots.drop o).take i = ((slots.drop o).take n).take i := by
        simp only [List.take_take]
        congr 1 <;> omega
      rw [hx,List.take_append_drop]
    · rw [List.drop_append]
      have hzero : ((slots.drop o).take i).drop (i+d-1) = [] :=
        List.drop_eq_nil_of_le (by rw [hX]; omega)
      rw [hzero]
      simp only [List.nil_append,List.drop_take,List.drop_drop,hX,Nat.zero_add]
      have hA : n+d-i-(i+d-1-i) = n-(i-1) := by omega
      have hB : o-d+i+(i+d-1-i) = o+(i-1) := by omega
      rw [hA,hB]

theorem unset_window_prefix {unsetRuntime : DictLayout} {α : Type} (slots : List (Option α)) (off n : I) (js : List I) (k : Nat)
    (ho : 1 ≤ off.val) (hj : ∀ j ∈ js, (k : Int) < j.val) :
    (vwWindow (vwUnset (unsetRuntime := unsetRuntime) slots off js) off n).take k = (vwWindow slots off n).take k := by
  apply List.ext_getElem?
  intro p
  simp only [vwWindow,List.getElem?_take,List.getElem?_drop]
  by_cases hp : p < k
  · simp only [hp,ite_true]
    by_cases hn : p < n.val.toNat
    · simp only [hn,ite_true]
      exact vwUnset_get (unsetRuntime := unsetRuntime) slots off js ((off.val-1).toNat+p) (by
        intro j hmem
        have := hj j hmem
        omega)
    · simp only [hn,ite_false]
  · simp only [hp,ite_false]

theorem unset_window_suffix {unsetRuntime : DictLayout} {α : Type} (slots : List (Option α)) (off n : I) (js : List I) (k : Nat)
    (ho : 1 ≤ off.val) (hj : ∀ j ∈ js, 1 ≤ j.val ∧ j.val ≤ (k : Int)) :
    (vwWindow (vwUnset (unsetRuntime := unsetRuntime) slots off js) off n).drop k = (vwWindow slots off n).drop k := by
  apply List.ext_getElem?
  intro p
  simp only [vwWindow,List.getElem?_take,List.getElem?_drop]
  by_cases hn : k+p < n.val.toNat
  · simp only [hn,ite_true]
    exact vwUnset_get (unsetRuntime := unsetRuntime) slots off js ((off.val-1).toNat+(k+p)) (by
      intro j hmem
      have := hj j hmem
      omega)
  · simp only [hn,ite_false]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth

theorem allocatedHole_window {α : Type} (K o p d q : Nat) (X Y : List (Option α))
    (hX : X.length = p) (hY : Y.length = q) (hroom : o+p+d+q ≤ K) :
    let D1 := (List.replicate K (none : Option α)).take o ++ X ++
      (List.replicate K none).drop (o+p)
    let D2 := D1.take (o+p+d) ++ Y ++ D1.drop (o+p+d+q)
    (D2.drop o).take (p+d+q) = X ++ List.replicate d none ++ Y := by
  dsimp only
  let initial : List (Option α) := List.replicate K none
  let D1 := initial.take o ++ X ++ initial.drop (o+p)
  have hDl : D1.length = K := by
    simp only [D1,initial,List.length_append,List.length_take,List.length_drop,List.length_replicate,hX]
    omega
  have hcap : o+(p+d+q) ≤ initial.length := by simp only [initial,List.length_replicate]; omega
  have hcap2 : o+(p+d+q) ≤ D1.length := by rw [hDl]; omega
  have hwrite1 : 0+p ≤ p+d+q := by omega
  have hwrite2 : p+d+q ≤ p+d+q := by omega
  have hsp1 := splice_window (sl := initial) (X := X) (o := o) (d := 0) (k := p)
    (nA := p+d+q) (hlen := hcap) (hd := hwrite1) (hX := hX)
  have hbase : (initial.drop o).take (p+d+q) = List.replicate (p+d+q) none := by
    simp only [initial,List.drop_replicate,List.take_replicate]
    congr 1 <;> omega
  have hw1 : (D1.drop o).take (p+d+q) = X ++ List.replicate (d+q) none := by
    dsimp only [D1]
    simpa only [Nat.add_zero,Nat.zero_add,List.take_zero,List.nil_append,hbase,List.drop_replicate,
      show p+d+q-p = d+q by omega] using hsp1
  have hsp2 := splice_window (sl := D1) (X := Y) (o := o) (d := p+d) (k := q)
    (nA := p+d+q) (hlen := hcap2) (hd := hwrite2) (hX := hY)
  have hEnd : o+(p+d)+q = o+p+d+q := by omega
  rw [hEnd] at hsp2
  have hStart : o+(p+d) = o+p+d := by omega
  rw [hStart] at hsp2
  change ((D1.take (o+p+d) ++ Y ++ D1.drop (o+p+d+q)).drop o).take (p+d+q) = _
  rw [hsp2,hw1]
  have hlen : (X ++ List.replicate (d+q) (none : Option α)).length = p+d+q := by
    simp only [List.length_append,hX,List.length_replicate]
    omega
  have hzero : (X ++ List.replicate (d+q) (none : Option α)).drop (p+d+q) = [] :=
    List.drop_eq_nil_of_le (by rw [hlen]; omega)
  rw [hzero,List.append_nil,List.take_append]
  rw [List.take_of_length_le (by rw [hX]; omega),hX]
  simp only [List.take_replicate]
  have hnum : min (p+d-p) (d+q) = d := by omega
  rw [hnum]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 3000000
attribute [local irreducible] JInt.wrap

theorem vecAt_length_int {s : MutableMemory α} {a mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s a mem off n slots) : ((s.contents a).length : Int) = n.val := by
  rw [h.contents,vwWindow_length h]
  have hn := h.2.2.2.1
  omega
theorem growth_end_casts (o n i d : Int) (ho : 1 ≤ o) (hn : 0 ≤ n)
    (hi : 1 ≤ i) (hin : i ≤ n) (hd : 0 ≤ d) :
    (o-1+d+i-1).toNat = (o-1).toNat+(i.toNat+d.toNat-1) ∧
    (o-1+i-1).toNat = (o-1).toNat+i.toNat-1 ∧
    (n-i+1).toNat = n.toNat-i.toNat+1 ∧
    (o-1+d+i-1+(n-i+1)).toNat = (o-1).toNat+n.toNat+d.toNat ∧
    (n+d).toNat = n.toNat+d.toNat ∧
    (i-1).toNat = i.toNat-1 ∧
    (i-1+d).toNat = i.toNat+d.toNat-1 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

theorem growth_start_casts (o n i d : Int) (ho : 1 ≤ o) (hn : 0 ≤ n)
    (hi : 1 ≤ i) (hd : 0 ≤ d) (hstart : d ≤ o-1) :
    (o-d-1).toNat = (o-1).toNat-d.toNat ∧
    (o-d-1+i).toNat = (o-1).toNat-d.toNat+i.toNat ∧
    (n+d).toNat = n.toNat+d.toNat ∧
    (i-1).toNat = i.toNat-1 ∧
    (i-1+d).toNat = i.toNat+d.toNat-1 ∧
    (o-d).toNat = o.toNat-d.toNat ∧ 1 ≤ o-d := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

theorem growth_nat_bounds (o n i d : Int) (K : Nat) (ho : 1 ≤ o) (hn : 0 ≤ n)
    (hi : 1 ≤ i) (hin : i ≤ n) (hd : 0 ≤ d) (hroom : o-1+n+d ≤ K) :
    1 ≤ i.toNat ∧ i.toNat ≤ n.toNat ∧ (o-1).toNat+n.toNat+d.toNat ≤ K := by
  refine ⟨?_,?_,?_⟩ <;> omega

theorem growth_start_nat_bounds (o n i d : Int) (K : Nat) (ho : 1 ≤ o) (hn : 0 ≤ n)
    (hi : 1 ≤ i) (hin : i ≤ n) (hd : 0 ≤ d) (hstart : d ≤ o-1) (hroom : o-1+n ≤ K) :
    1 ≤ i.toNat ∧ i.toNat ≤ n.toNat ∧ d.toNat ≤ (o-1).toNat ∧ (o-1).toNat+n.toNat ≤ K := by
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem intRange_hole_bounds (i d z : I) (hz : z.val = i.val+d.val-1)
    (hi : 1 ≤ i.val) (hd : 0 ≤ d.val) :
    (∀ j ∈ intRange i z, ((i.val-1).toNat : Int) < j.val) ∧
    (∀ j ∈ intRange i z, 1 ≤ j.val ∧ j.val ≤ ((i.val-1+d.val).toNat : Int)) := by
  constructor
  · intro j hj
    have hb := intRange_mem i z j hj
    omega
  · intro j hj
    have hb := intRange_mem i z j hj
    rw [hz] at hb
    omega


theorem growat_endroom_window {unsetRuntime : DictLayout} {α : Type} (slots : List (Option α)) (off n i d : I)
    (ho : 1 ≤ off.val) (hn : 0 ≤ n.val) (hc : slots.length < 2^63)
    (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hroom : off.val-1+n.val+d.val ≤ (slots.length : Int)) :
    let R := slots.take ((off-one+d+i).val-1).toNat ++
      (slots.drop ((off-one+i).val-1).toNat).take (n-i+one).val.toNat ++
      slots.drop ((off-one+d+i).val-1+(n-i+one).val).toNat
    (n+d).val = n.val+d.val ∧ (n+d).val.toNat = n.val.toNat+d.val.toNat ∧
    (vwWindow (vwUnset (unsetRuntime := unsetRuntime) R off (intRange i (i+d-one))) off (n+d)).take (i.val-1).toNat =
      (vwWindow slots off n).take (i.val-1).toNat ∧
    (vwWindow (vwUnset (unsetRuntime := unsetRuntime) R off (intRange i (i+d-one))) off (n+d)).drop (i.val-1+d.val).toNat =
      (vwWindow slots off n).drop (i.val-1).toNat := by
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := growth_end_casts off.val n.val i.val d.val ho hn (Int.le_of_lt hi) hin hd
  obtain ⟨bi,bn,br⟩ := growth_nat_bounds off.val n.val i.val d.val slots.length ho hn (Int.le_of_lt hi) hin hd hroom
  have hnd : (n+d).val = n.val+d.val := ival_add _ _ (by omega)
  have hom : (off-one).val = off.val-1 := ival_sub_one off (by omega)
  have hod : (off-one+d).val = off.val-1+d.val := by
    rw [ival_add _ _ (by rw [hom]; omega),hom]
  have hdest : (off-one+d+i).val = off.val-1+d.val+i.val := by
    rw [ival_add _ _ (by rw [hod]; omega),hod]
  have hsrc : (off-one+i).val = off.val-1+i.val := by
    rw [ival_add _ _ (by rw [hom]; omega),hom]
  have hni : (n-i).val = n.val-i.val := ival_sub _ _ (by omega)
  have hk : (n-i+one).val = n.val-i.val+1 := by rw [ival_add_one _ (by rw [hni]; omega),hni]
  have hstop : (i+d-one).val = i.val+d.val-1 := ival_add_sub_one i d (by omega)
  have hdestN : ((off-one+d+i).val-1).toNat = (off.val-1).toNat+(i.val.toNat+d.val.toNat-1) := by rw [hdest]; exact e0
  have hsrcN : ((off-one+i).val-1).toNat = (off.val-1).toNat+i.val.toNat-1 := by rw [hsrc]; exact e1
  have hkN : (n-i+one).val.toNat = n.val.toNat-i.val.toNat+1 := by rw [hk]; exact e2
  have htailN : ((off-one+d+i).val-1+(n-i+one).val).toNat = (off.val-1).toNat+n.val.toNat+d.val.toNat := by rw [hdest,hk]; exact e3
  have hndN : (n+d).val.toNat = n.val.toNat+d.val.toNat := by rw [hnd]; exact e4
  have hpN : (i.val-1).toNat = i.val.toNat-1 := e5
  have hqN : (i.val-1+d.val).toNat = i.val.toNat+d.val.toNat-1 := e6
  have hbnds := intRange_hole_bounds i d (i+d-one) hstop (Int.le_of_lt hi) hd
  have hpure := shiftedSuffix_sides slots (off.val-1).toNat n.val.toNat i.val.toNat d.val.toNat
    bi bn br
  dsimp only at hpure
  let R := slots.take ((off-one+d+i).val-1).toNat ++
    (slots.drop ((off-one+i).val-1).toNat).take (n-i+one).val.toNat ++
    slots.drop ((off-one+d+i).val-1+(n-i+one).val).toNat
  have hup := unset_window_prefix (unsetRuntime := unsetRuntime) R off (n+d) (intRange i (i+d-one)) (i.val-1).toNat ho hbnds.1
  have hus := unset_window_suffix (unsetRuntime := unsetRuntime) R off (n+d) (intRange i (i+d-one)) (i.val-1+d.val).toNat ho hbnds.2
  refine ⟨hnd,hndN,?_,?_⟩
  · rw [hup]
    simpa only [vwWindow,R,hdestN,hsrcN,hkN,htailN,hndN,hpN] using hpure.1
  · rw [hus]
    simpa only [vwWindow,R,hdestN,hsrcN,hkN,htailN,hndN,hpN,hqN] using hpure.2

theorem growat_startroom_window {unsetRuntime : DictLayout} {α : Type} (slots : List (Option α)) (off n i d : I)
    (ho : 1 ≤ off.val) (hn : 0 ≤ n.val) (he : off.val-1+n.val ≤ (slots.length : Int))
    (hc : slots.length < 2^63) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hstart : d.val ≤ off.val-1) (hov : off.val-1+n.val+d.val ≤ 9223372036854775807) :
    let R := slots.take ((off-d).val-1).toNat ++
      (slots.drop (off.val-1).toNat).take i.val.toNat ++ slots.drop ((off-d).val-1+i.val).toNat
    (n+d).val = n.val+d.val ∧ (n+d).val.toNat = n.val.toNat+d.val.toNat ∧
    (off-d).val.toNat = off.val.toNat-d.val.toNat ∧
    (vwWindow (vwUnset (unsetRuntime := unsetRuntime) R (off-d) (intRange i (i+d-one))) (off-d) (n+d)).take (i.val-1).toNat =
      (vwWindow slots off n).take (i.val-1).toNat ∧
    (vwWindow (vwUnset (unsetRuntime := unsetRuntime) R (off-d) (intRange i (i+d-one))) (off-d) (n+d)).drop (i.val-1+d.val).toNat =
      (vwWindow slots off n).drop (i.val-1).toNat := by
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := growth_start_casts off.val n.val i.val d.val ho hn (Int.le_of_lt hi) hd hstart
  obtain ⟨bi,bn,bd,br⟩ := growth_start_nat_bounds off.val n.val i.val d.val slots.length ho hn (Int.le_of_lt hi) hin hd hstart he
  have hnd : (n+d).val = n.val+d.val := ival_add _ _ (by omega)
  have hno : (off-d).val = off.val-d.val := ival_sub _ _ (by omega)
  have hstop : (i+d-one).val = i.val+d.val-1 := ival_add_sub_one i d (by omega)
  have hnewN : ((off-d).val-1).toNat = (off.val-1).toNat-d.val.toNat := by rw [hno]; exact e0
  have htailN : ((off-d).val-1+i.val).toNat = (off.val-1).toNat-d.val.toNat+i.val.toNat := by rw [hno]; exact e1
  have hndN : (n+d).val.toNat = n.val.toNat+d.val.toNat := by rw [hnd]; exact e2
  have hpN : (i.val-1).toNat = i.val.toNat-1 := e3
  have hqN : (i.val-1+d.val).toNat = i.val.toNat+d.val.toNat-1 := e4
  have hOffNat : (off-d).val.toNat = off.val.toNat-d.val.toNat := by rw [hno]; exact e5
  have hbnds := intRange_hole_bounds i d (i+d-one) hstop (Int.le_of_lt hi) hd
  have hnewpos : 1 ≤ (off-d).val := by rw [hno]; exact e6
  have hpure := shiftedPrefix_sides slots (off.val-1).toNat n.val.toNat i.val.toNat d.val.toNat
    bi bn bd br
  dsimp only at hpure
  let R := slots.take ((off-d).val-1).toNat ++
    (slots.drop (off.val-1).toNat).take i.val.toNat ++
    slots.drop ((off-d).val-1+i.val).toNat
  have hup := unset_window_prefix (unsetRuntime := unsetRuntime) R (off-d) (n+d) (intRange i (i+d-one)) (i.val-1).toNat hnewpos hbnds.1
  have hus := unset_window_suffix (unsetRuntime := unsetRuntime) R (off-d) (n+d) (intRange i (i+d-one)) (i.val-1+d.val).toNat hnewpos hbnds.2
  refine ⟨hnd,hndN,hOffNat,?_,?_⟩
  · rw [hup]
    simpa only [vwWindow,R,hnewN,htailN,hndN,hpN] using hpure.1
  · rw [hus]
    simpa only [vwWindow,R,hnewN,htailN,hndN,hpN,hqN] using hpure.2

theorem growat_endroom_post (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (a mem : Nat) (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hpref : n.val/2 < i.val) (hroom : off.val-1+n.val+d.val ≤ (slots.length : Int)) :
    ∃ next,
      (growat (mutableStorage layout) pure pure
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i d).run s =
        (.ok (),next) ∧ next.validVector a ∧
      ((next.contents a).length : Int) = (s.contents a).length+d.val ∧
      (next.contents a).take (i.val-1).toNat = (s.contents a).take (i.val-1).toNat ∧
      (next.contents a).drop (i.val-1+d.val).toNat = (s.contents a).drop (i.val-1).toNat ∧
      geometryOf next a = ⟨slots.length,off.val.toNat,n.val.toNat+d.val.toNat⟩ ∧
      (∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) ∧
      ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]? := by
  obtain ⟨next,result,hr,hv,harrays,hlen,hresult,hOther⟩ := growat_endroom_run layout s a mem off n slots h i d hi hin hd hpref hroom
  obtain ⟨hnd,hndN,hpre,hsuf⟩ := growat_endroom_window (unsetRuntime := layout.runtime) slots off n i d h.2.2.1 h.2.2.2.1 h.2.2.2.2.2 hi hin hd hroom
  refine ⟨next,hr,hv.valid,?_,?_,?_,?_,?_,hOther⟩
  · rw [vecAt_length_int hv,vecAt_length_int h,hnd]
  · rw [hv.contents,hresult,h.contents]
    exact hpre
  · rw [hv.contents,hresult,h.contents]
    exact hsuf
  · rw [opusGrowth.VecAt.geometry hv,hlen,hndN]
  · intro other hne
    rw [harrays,List.getElem?_set_ne (Ne.symm hne)]

theorem growat_startroom_post (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (a mem : Nat) (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hpref : i.val ≤ n.val/2) (hstart : d.val ≤ off.val-1)
    (hov : off.val-1+n.val+d.val ≤ 9223372036854775807) :
    ∃ next,
      (growat (mutableStorage layout) pure pure
        (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
        (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i d).run s =
        (.ok (),next) ∧ next.validVector a ∧
      ((next.contents a).length : Int) = (s.contents a).length+d.val ∧
      (next.contents a).take (i.val-1).toNat = (s.contents a).take (i.val-1).toNat ∧
      (next.contents a).drop (i.val-1+d.val).toNat = (s.contents a).drop (i.val-1).toNat ∧
      geometryOf next a = ⟨slots.length,off.val.toNat-d.val.toNat,n.val.toNat+d.val.toNat⟩ ∧
      (∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) ∧
      ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]? := by
  obtain ⟨next,result,hr,hv,harrays,hlen,hresult,hOther⟩ := growat_startroom_run layout s a mem off n slots h i d hi hin hd hpref hstart hov
  obtain ⟨hnd,hndN,hOffNat,hpre,hsuf⟩ := growat_startroom_window (unsetRuntime := layout.runtime) slots off n i d h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 hi hin hd hstart hov
  refine ⟨next,hr,hv.valid,?_,?_,?_,?_,?_,hOther⟩
  · rw [vecAt_length_int hv,vecAt_length_int h,hnd]
  · rw [hv.contents,hresult,h.contents]
    exact hpre
  · rw [hv.contents,hresult,h.contents]
    exact hsuf
  · rw [opusGrowth.VecAt.geometry hv,hlen,hndN,hOffNat]
  · intro other hne
    rw [harrays,List.getElem?_set_ne (Ne.symm hne)]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 3000000
attribute [local irreducible] JInt.wrap

theorem growat_alloc_run (l : DictLayout) (s : MutableMemory α)
    (a mem : Nat) (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hstart : i.val ≤ n.val/2 → off.val-1 < d.val)
    (hendroom : n.val/2 < i.val → (slots.length : Int) < off.val-1+n.val+d.val)
    (hov : off.val-1+n.val+d.val ≤ 9223372036854775807)
    (hov2 : n.val+2*d.val+1 ≤ 9223372036854775807)
    (K : Nat) (hK : K = max (overallocationNat slots.length)
      (n.val.toNat+2*d.val.toNat+1)) :
    (¬ memoryFits l K →
      (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a i d).run s =
        (.error (.argument genericMemorySizeMessage),s)) ∧
    (memoryFits l K → ∃ next newoff D1 result,
      (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a i d).run s =
        (.ok (),next) ∧ VecAt next a s.memories.length newoff (n+d) result ∧
      newoff.val = ((K : Int)-(n.val+d.val))/2+1 ∧ result.length = K ∧
      next.arrays = s.arrays.set a ⟨(s.memories.length,newoff),n+d⟩ ∧
      D1 = (List.replicate K none).take (newoff.val-1).toNat ++
        (slots.drop (off.val-1).toNat).take (i-one).val.toNat ++
        (List.replicate K none).drop (newoff.val-1+(i-one).val).toNat ∧
      result = D1.take ((newoff+d+i-one).val-1).toNat ++
        (slots.drop ((off+i-one).val-1).toNat).take (n-i+one).val.toNat ++
        D1.drop ((newoff+d+i-one).val-1+(n-i+one).val).toNat ∧
      ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) := by
  have ho := h.2.2.1
  have hn := h.2.2.2.1
  have he := h.2.2.2.2.1
  have hc := h.2.2.2.2.2
  have hm := h.2.1
  have ha := h.1
  have hnb := ival_bounds n
  have hob := ival_bounds off
  have hdb := ival_bounds d
  have hib := ival_bounds i
  have hmem := mutableMemLength_run (layout := MemoryLayoutMetadata.ofRuntime l) s mem slots hm
  have hM : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hnd : (n+d).val = n.val+d.val := ival_add _ _ (by omega)
  have hom : (off-one).val = off.val-1 := ival_sub_one off (by omega)
  have hsum : (off-one+(n+d)).val = off.val-1+n.val+d.val := by
    rw [ival_add _ _ (by rw [hom,hnd]; omega),hom,hnd]; omega
  have hca := ms_checkedAdd_run (layout := MemoryLayoutMetadata.ofRuntime l) s n d (by omega)
  have hcb := ms_checkedAdd_run (layout := MemoryLayoutMetadata.ofRuntime l) s (off-one) (n+d) (by rw [hom,hnd]; omega)
  have hdiv := ms_divide_run (layout := MemoryLayoutMetadata.ofRuntime l) s n (JInt.wrap .i64 2) (by rw [wval2]; decide)
  have hQ : (JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)).val = n.val/2 := by
    rw [wval2]
    exact tdiv_nonneg_val n 2 hn (by decide) (by decide)
  have hi1 : i ≠ one := by intro hh; have := congrArg Subtype.val hh; rw [ival_one] at this; omega
  have hend : ¬ (n < JInt.typemax .i64 ∧ i = n+one) := by
    intro hh
    have hn1 : (n+one).val = n.val+1 := ival_add_one n (by
      have := hh.1
      change n.val < (JInt.typemax .i64).val at this
      have hmax : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
      rw [hmax] at this; omega)
    have := congrArg Subtype.val hh.2
    rw [hn1] at this
    omega
  have hendb : (decide (n < JInt.typemax .i64) && decide (i = n+one)) = false := by
    by_cases hnless : n < JInt.typemax .i64
    · have hne : i ≠ n+one := fun hh => hend ⟨hnless,hh⟩
      simp only [hnless,decide_true,hne,decide_false,Bool.true_and]
    · simp only [hnless,decide_false,Bool.false_and]
  have hd0 : d ≥ zero := by rw [ge_iff_le,jle_iff,ival_zero]; exact hd
  have hirange : one < i ∧ i ≤ n := by rw [jlt_iff,jle_iff,ival_one]; exact ⟨hi,hin⟩
  have hbr1 : (decide (i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)) &&
      decide (d ≤ off-one)) = false := by
    by_cases hp : i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)
    · have hpf : i.val ≤ n.val/2 := by simpa only [jle_iff,hQ] using hp
      have hs : ¬ d ≤ off-one := by rw [jle_iff,hom]; have := hstart hpf; omega
      simp only [hp,decide_true,hs,decide_false,Bool.true_and]
    · simp only [hp,decide_false,Bool.false_and]
  have hbr2 : (!decide (i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)) &&
      decide (JInt.wrap .i64 (slots.length : Int) ≥ off-one+(n+d))) = false := by
    by_cases hp : i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)
    · simp only [hp,decide_true,Bool.not_true,Bool.false_and]
    · have hpf : n.val/2 < i.val := by rw [jle_iff,hQ] at hp; omega
      have hs : ¬ JInt.wrap .i64 (slots.length : Int) ≥ off-one+(n+d) := by
        rw [ge_iff_le,jle_iff,hM,hsum]; have := hendroom hpf; omega
      simp only [hp,decide_false,Bool.not_false,hs,decide_false,Bool.true_and]
  obtain ⟨_,_,hmul,hadd2,hadd3,hsizeval⟩ := growbegInternal_facts0 (layout := MemoryLayoutMetadata.ofRuntime l) h d hd hov2
  obtain ⟨c,hcRun,hcVal⟩ := ms_overallocation_val (layout := MemoryLayoutMetadata.ofRuntime l) s
    (JInt.wrap .i64 (slots.length : Int)) (by rw [hM]; omega)
  have hcVal' : c.val = (overallocationNat slots.length : Int) := by rw [hM] at hcVal; simpa using hcVal
  let cap := max c (n+JInt.wrap .i64 2*d+one)
  have hcap : cap.val = K := by
    dsimp only [cap]
    rw [imax_val,hcVal',hsizeval,hK]
    omega
  have hKlo : n.val+2*d.val+1 ≤ (K : Int) := by
    rw [← hcap]
    dsimp only [cap]
    rw [imax_val,hsizeval]
    omega
  have hcapB := ival_bounds cap
  have hdiff : (cap-(n+d)).val = (K : Int)-(n.val+d.val) := by
    rw [ival_sub _ _ (by rw [hcap,hnd]; omega),hcap,hnd]
  have hdivA := ms_divide_run (layout := MemoryLayoutMetadata.ofRuntime l) s (cap-(n+d)) (JInt.wrap .i64 2) (by rw [wval2]; decide)
  let q : I := JInt.wrap .i64 ((cap-(n+d)).val.tdiv (JInt.wrap .i64 2).val)
  have hq : q.val = ((K : Int)-(n.val+d.val))/2 := by
    dsimp only [q]
    rw [wval2,tdiv_nonneg_val _ 2 (by rw [hdiff]; omega) (by decide) (by decide),hdiff]
  have hq0 : 0 ≤ q.val := by rw [hq]; omega
  have hqroom : q.val+n.val+d.val ≤ (K : Int) := by rw [hq]; omega
  have hno : (q+one).val = ((K : Int)-(n.val+d.val))/2+1 := by
    rw [ival_add_one q (by rw [hq]; rw [hcap] at hcapB; omega),hq]
  let newoff := q+one
  have hnob : 1 ≤ newoff.val := by rw [hno]; omega
  have halloc := arrayNewMemorySpec α l s mem cap
  simp only at halloc
  have hcap0 : 0 ≤ cap.val := by rw [hcap]; omega
  have hcapNat : cap.val.toNat = K := by rw [hcap]; omega
  rw [hcapNat] at halloc
  have him : (i-one).val = i.val-1 := ival_sub_one i (by omega)
  have hsrc : (off+i-one).val = off.val+i.val-1 := ival_add_sub_one off i (by omega)
  have hndi : (newoff+d+i-one).val = newoff.val+d.val+i.val-1 := by
    have h1 : (newoff+d).val = newoff.val+d.val := ival_add _ _ (by rw [hno]; rw [hcap] at hcapB; omega)
    rw [ival_add_sub_one (newoff+d) i (by rw [h1,hno]; rw [hcap] at hcapB; omega),h1]
  have hni : (n-i).val = n.val-i.val := ival_sub _ _ (by omega)
  have hk : (n-i+one).val = n.val-i.val+1 := by rw [ival_add_one _ (by rw [hni]; omega),hni]
  have hmlt := (List.getElem?_eq_some_iff.mp hm).choose
  have halt := (List.getElem?_eq_some_iff.mp ha).choose
  have hrunEq :
      (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a i d).run s =
      (do
        let newmem ← (mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem cap
        let newref ← (mutableStorage (MemoryLayoutMetadata.ofRuntime l)).memoryref newmem newoff
        (mutableStorage (MemoryLayoutMetadata.ofRuntime l)).copyRef newref (mem,off) (i-one)
        (mutableStorage (MemoryLayoutMetadata.ofRuntime l)).copyMemory newmem (newoff+d+i-one) mem (off+i-one) (n-i+one)
        (mutableStorage (MemoryLayoutMetadata.ofRuntime l)).setRef a newref
        (mutableStorage (MemoryLayoutMetadata.ofRuntime l)).setSize a (n+d)).run s := by
    simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,
      mutableLength_run s a _ ha,hendb,hd0,decide_true,Bool.not_true,Bool.false_eq_true,
      hirange,and_self,ms_length,ms_ref,ms_memory,ms_offset,mutableRef_run s a _ ha,
      hmem,hca,hcb,hdiv,hbr2,ite_false]
    split
    · rename_i hb
      have hbi : i.val ≤ n.val/2 ∧ d.val ≤ off.val-1 := by
        simpa only [Bool.and_eq_true,decide_eq_true_eq,jle_iff,hQ,hom] using hb
      have := hstart hbi.1
      omega
    · dsimp only [cap] at hdivA
      simp only [stateExcept_bind,hcRun,hmul,hadd2,hadd3,hdivA]
      rfl
  rw [hrunEq]
  refine ⟨fun hnf => ?_,fun hfit => ?_⟩
  · have hE : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem cap).run s =
        (.error (.argument genericMemorySizeMessage),s) := halloc.2.1 hcap0 hnf
    simp only [stateExcept_bind,hE]
  · have hA : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem cap).run s =
        (.ok s.memories.length,{s with memories := s.memories ++ [List.replicate K none]}) :=
      halloc.2.2 hcap0 hfit
    have hK63 : K < 2^63 := by have := hfit.1; unfold maxIntVal at this; omega
    have hnewlen0 : 0 ≤ (n+d).val := by rw [hnd]; omega
    have hnewroom : newoff.val-1+(n+d).val ≤ (K : Int) := by rw [hno,hnd]; omega
    have hCopy2Count : 0 ≤ (n-i+one).val := by rw [hk]; omega
    have hCopy2Dest : 1 ≤ (newoff+d+i-one).val := by rw [hndi,hno]; omega
    have hCopy2DestRoom : (newoff+d+i-one).val-1+(n-i+one).val ≤ (K : Int) := by
      rw [hndi,hk,hno]
      omega
    have hCopy2Src : 1 ≤ (off+i-one).val := by rw [hsrc]; omega
    have hCopy2SrcRoom : (off+i-one).val-1+(n-i+one).val ≤ (slots.length : Int) := by
      rw [hsrc,hk]
      omega
    have hSlice1 : ((slots.drop (off.val-1).toNat).take (i-one).val.toNat).length =
        (i-one).val.toNat := by
      simp only [List.length_take,List.length_drop,him]
      omega
    have hSlice2 : ((slots.drop ((off+i-one).val-1).toNat).take (n-i+one).val.toNat).length =
        (n-i+one).val.toNat := by
      simp only [List.length_take,List.length_drop,hsrc,hk]
      omega
    have hTail1 : (newoff.val-1+(i-one).val).toNat =
        (newoff.val-1).toNat+(i-one).val.toNat := by rw [him]; omega
    have hTail2 : ((newoff+d+i-one).val-1+(n-i+one).val).toNat =
        ((newoff+d+i-one).val-1).toNat+(n-i+one).val.toNat := by rw [hndi,hk]; omega
    have hSpace1 : (newoff.val-1).toNat+(i-one).val.toNat ≤ K := by
      rw [him]
      dsimp only [newoff]
      rw [hno]
      omega
    have hSpace2 : ((newoff+d+i-one).val-1).toNat+(n-i+one).val.toNat ≤ K := by
      rw [hndi,hk]
      dsimp only [newoff]
      rw [hno]
      omega
    let s0 : MutableMemory α := {s with memories := s.memories ++ [List.replicate K none]}
    have hdM : s0.memories[s.memories.length]? = some (List.replicate K none) := by simp [s0]
    have hsM : s0.memories[mem]? = some slots := by
      dsimp only [s0]
      rw [List.getElem?_append_left hmlt]
      exact hm
    have hmove1 := vwMemoryMove_run s0 s.memories.length mem newoff off (i-one)
      (List.replicate K none) slots hdM hsM (by rw [him]; omega) hnob
      (by rw [List.length_replicate,him,hno]; omega) ho (by rw [him]; omega)
      (by rw [List.length_replicate]; exact hK63)
    let D1 := (List.replicate K none).take (newoff.val-1).toNat ++
      (slots.drop (off.val-1).toNat).take (i-one).val.toNat ++
      (List.replicate K none).drop (newoff.val-1+(i-one).val).toNat
    have hD1 : D1.length = K := by
      dsimp only [D1]
      rw [hTail1]
      exact (splice_length (List.replicate K (none : Option α))
        ((slots.drop (off.val-1).toNat).take (i-one).val.toNat)
        (newoff.val-1).toNat (i-one).val.toNat
        (by rw [List.length_replicate]; exact hSpace1) hSlice1).trans (by simp only [List.length_replicate])
    let s1 : MutableMemory α := {s0 with memories := s0.memories.set s.memories.length D1}
    have hdM1 : s1.memories[s.memories.length]? = some D1 := by
      exact List.getElem?_set_self (by simp [s0])
    have hsM1 : s1.memories[mem]? = some slots := by
      dsimp only [s1]
      rw [List.getElem?_set_ne (by omega)]
      exact hsM
    have hmove2 := vwMemoryMove_run s1 s.memories.length mem (newoff+d+i-one) (off+i-one)
      (n-i+one) D1 slots hdM1 hsM1 hCopy2Count hCopy2Dest
      (by rw [hD1]; exact hCopy2DestRoom) hCopy2Src hCopy2SrcRoom
      (by rw [hD1]; exact hK63)
    let D2 := D1.take ((newoff+d+i-one).val-1).toNat ++
      (slots.drop ((off+i-one).val-1).toNat).take (n-i+one).val.toNat ++
      D1.drop ((newoff+d+i-one).val-1+(n-i+one).val).toNat
    have hD2 : D2.length = K := by
      dsimp only [D2]
      rw [hTail2]
      exact (splice_length D1
        ((slots.drop ((off+i-one).val-1).toNat).take (n-i+one).val.toNat)
        ((newoff+d+i-one).val-1).toNat (n-i+one).val.toNat
        (by rw [hD1]; exact hSpace2) hSlice2).trans hD1
    let s2 : MutableMemory α := {s with memories := (s.memories ++ [List.replicate K none]).set s.memories.length D2}
    have ha2 : s2.arrays[a]? = some ⟨(mem,off),n⟩ := ha
    have href := ms_setRef_run (layout := MemoryLayoutMetadata.ofRuntime l) s2 a _ ha2 (s.memories.length,newoff)
    let s3 : MutableMemory α := {s2 with arrays := s.arrays.set a ⟨(s.memories.length,newoff),n⟩}
    have ha3 : s3.arrays[a]? = some ⟨(s.memories.length,newoff),n⟩ := List.getElem?_set_self halt
    have hsize := ms_setSize_run (layout := MemoryLayoutMetadata.ofRuntime l) s3 a _ ha3 (n+d)
    let final : MutableMemory α := {s2 with arrays := s.arrays.set a ⟨(s.memories.length,newoff),n+d⟩}
    have hv : VecAt final a s.memories.length newoff (n+d) D2 :=
      ⟨List.getElem?_set_self halt,List.getElem?_set_self (by simp),hnob,
        hnewlen0,by rw [hD2]; exact hnewroom,by rw [hD2]; exact hK63⟩
    have hOther : ∀ m, m < s.memories.length → m ≠ mem → final.memories[m]? = s.memories[m]? := by
      intro m hlt _
      change ((s.memories ++ [List.replicate K none]).set s.memories.length D2)[m]? = s.memories[m]?
      rw [List.getElem?_set_ne (Nat.ne_of_gt hlt),List.getElem?_append_left hlt]
    refine ⟨final,newoff,D1,D2,?_,hv,hno,hD2,rfl,rfl,rfl,hOther⟩
    dsimp only [s0] at hmove1
    dsimp only [s1,s0,D1] at hmove2
    dsimp only [s2,D2,D1] at href
    dsimp only [s3,s2,D2,D1] at hsize
    simp only [List.set_set] at hmove2 hsize
    simp only [stateExcept_bind,hA,ms_memoryref,stateExcept_pure,ms_copyRef,ms_copyMemory,
      hmove1,hmove2,href,hsize]
    simp only [final,s2,D2,D1,List.set_set]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 3000000
attribute [local irreducible] JInt.wrap

theorem growat_alloc_window {α : Type} (slots : List (Option α)) (off n i d newoff : I) (K : Nat)
    (ho : 1 ≤ off.val) (hn : 0 ≤ n.val) (he : off.val-1+n.val ≤ (slots.length : Int))
    (hc : slots.length < 2^63)
    (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hKlo : n.val+2*d.val+1 ≤ (K : Int)) (hKmax : (K : Int) ≤ 9223372036854775807)
    (hno : newoff.val = ((K : Int)-(n.val+d.val))/2+1) :
    let D1 := (List.replicate K none).take (newoff.val-1).toNat ++
      (slots.drop (off.val-1).toNat).take (i-one).val.toNat ++
      (List.replicate K none).drop (newoff.val-1+(i-one).val).toNat
    let D2 := D1.take ((newoff+d+i-one).val-1).toNat ++
      (slots.drop ((off+i-one).val-1).toNat).take (n-i+one).val.toNat ++
      D1.drop ((newoff+d+i-one).val-1+(n-i+one).val).toNat
    (n+d).val = n.val+d.val ∧
    (vwWindow D2 newoff (n+d)).take (i.val-1).toNat = (vwWindow slots off n).take (i.val-1).toNat ∧
    (vwWindow D2 newoff (n+d)).drop (i.val-1+d.val).toNat = (vwWindow slots off n).drop (i.val-1).toNat := by
  have hnob : 1 ≤ newoff.val := by rw [hno]; omega
  have hroom : newoff.val-1+n.val+d.val ≤ (K : Int) := by rw [hno]; omega
  have hnd : (n+d).val = n.val+d.val := ival_add _ _ (by omega)
  have him : (i-one).val = i.val-1 := ival_sub_one i (by omega)
  have hsrc : (off+i-one).val = off.val+i.val-1 := ival_add_sub_one off i (by omega)
  have hndi : (newoff+d+i-one).val = newoff.val+d.val+i.val-1 := by
    have h1 : (newoff+d).val = newoff.val+d.val := ival_add _ _ (by omega)
    rw [ival_add_sub_one (newoff+d) i (by rw [h1]; omega),h1]
  have hni : (n-i).val = n.val-i.val := ival_sub _ _ (by omega)
  have hk : (n-i+one).val = n.val-i.val+1 := by rw [ival_add_one _ (by rw [hni]; omega),hni]
  let X := (slots.drop (off.val-1).toNat).take (i.val-1).toNat
  let Y := (slots.drop (off.val-1+i.val-1).toNat).take (n.val-i.val+1).toNat
  have hX : X.length = (i.val-1).toNat := by
    simp only [X,List.length_take,List.length_drop]
    omega
  have hY : Y.length = (n.val-i.val+1).toNat := by
    simp only [Y,List.length_take,List.length_drop]
    omega
  have hspace : (newoff.val-1).toNat+(i.val-1).toNat+d.val.toNat+(n.val-i.val+1).toNat ≤ K := by omega
  have hw := allocatedHole_window K (newoff.val-1).toNat (i.val-1).toNat d.val.toNat
    (n.val-i.val+1).toNat X Y hX hY hspace
  dsimp only at hw
  have hD1end : (newoff.val-1+(i-one).val).toNat = (newoff.val-1).toNat+(i.val-1).toNat := by rw [him]; omega
  have hD2start : ((newoff+d+i-one).val-1).toNat = (newoff.val-1).toNat+(i.val-1).toNat+d.val.toNat := by rw [hndi]; omega
  have hD2end : ((newoff+d+i-one).val-1+(n-i+one).val).toNat =
      (newoff.val-1).toNat+(i.val-1).toNat+d.val.toNat+(n.val-i.val+1).toNat := by rw [hndi,hk]; omega
  have hnewN : (n+d).val.toNat = (i.val-1).toNat+d.val.toNat+(n.val-i.val+1).toNat := by rw [hnd]; omega
  have hYeq : (vwWindow slots off n).drop (i.val-1).toNat = Y := by
    simp only [vwWindow,Y,List.drop_take,List.drop_drop]
    congr 2 <;> omega
  have hXeq : (vwWindow slots off n).take (i.val-1).toNat = X := by
    simp only [vwWindow,X,List.take_take]
    congr 1 <;> omega
  have hsrcN : ((off+i-one).val-1).toNat = (off.val-1+i.val-1).toNat := by rw [hsrc]; omega
  have hq : (i.val-1+d.val).toNat = (i.val-1).toNat+d.val.toNat := by omega
  dsimp only
  simp only [hD1end,hD2start,hD2end]
  refine ⟨hnd,?_,?_⟩
  · have htake : (X ++ List.replicate d.val.toNat none ++ Y).take (i.val-1).toNat = X := by
      rw [List.append_assoc,List.take_append_of_le_length (by rw [hX]; omega)]
      exact List.take_of_length_le (by rw [hX]; omega)
    simpa only [vwWindow,him,hnewN,hsrcN,hk,X,Y] using
      ((congrArg (fun w => w.take (i.val-1).toNat) hw).trans htake).trans hXeq.symm
  · have hpref : (X ++ List.replicate d.val.toNat (none : Option α)).length = (i.val-1).toNat+d.val.toNat := by
      simp only [List.length_append,hX,List.length_replicate]
    have hzero : (X ++ List.replicate d.val.toNat (none : Option α)).drop ((i.val-1).toNat+d.val.toNat) = [] :=
      List.drop_eq_nil_of_le (by rw [hpref]; omega)
    have hdrop : (X ++ List.replicate d.val.toNat none ++ Y).drop ((i.val-1).toNat+d.val.toNat) = Y := by
      rw [List.drop_append_of_le_length (by rw [hpref]; omega),hzero]
      rfl
    simpa only [vwWindow,him,hnewN,hsrcN,hk,hq,X,Y] using
      ((congrArg (fun w => w.drop ((i.val-1).toNat+d.val.toNat)) hw).trans hdrop).trans hYeq.symm

theorem memoryFits_i64_bound (l : MemoryLayout) (K : Nat) (h : memoryFits l K) :
    (K : Int) ≤ 9223372036854775807 := by
  have hk := h.1
  unfold maxIntVal at hk
  omega

theorem growat_alloc_post (l : DictLayout) (s : MutableMemory α)
    (a mem : Nat) (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hstart : i.val ≤ n.val/2 → off.val-1 < d.val)
    (hendroom : n.val/2 < i.val → (slots.length : Int) < off.val-1+n.val+d.val)
    (hov : off.val-1+n.val+d.val ≤ 9223372036854775807)
    (hov2 : n.val+2*d.val+1 ≤ 9223372036854775807)
    (K : Nat) (hK : K = max (overallocationNat slots.length) (n.val.toNat+2*d.val.toNat+1)) :
    (¬ memoryFits l K →
      (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a i d).run s =
        (.error (.argument genericMemorySizeMessage),s)) ∧
    (memoryFits l K → ∃ next,
      (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a i d).run s =
        (.ok (),next) ∧ next.validVector a ∧
      ((next.contents a).length : Int) = (s.contents a).length+d.val ∧
      (next.contents a).take (i.val-1).toNat = (s.contents a).take (i.val-1).toNat ∧
      (next.contents a).drop (i.val-1+d.val).toNat = (s.contents a).drop (i.val-1).toNat ∧
      (∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) ∧
      ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) := by
  have hKlo : n.val+2*d.val+1 ≤ (K : Int) := by
    have hnat := Nat.le_max_right (overallocationNat slots.length) (n.val.toNat+2*d.val.toNat+1)
    rw [← hK] at hnat
    have hn := h.2.2.2.1
    omega
  obtain ⟨herr,hok⟩ := growat_alloc_run l s a mem off n slots h i d hi hin hd hstart hendroom hov hov2 K hK
  refine ⟨herr,fun hfit => ?_⟩
  have hKmax := memoryFits_i64_bound l K hfit
  obtain ⟨next,newoff,D1,result,hr,hv,hno,hlen,harrays,hD1,hresult,hOther⟩ := hok hfit
  obtain ⟨hnd,hpre,hsuf⟩ := growat_alloc_window slots off n i d newoff K h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2 hi hin hd hKlo hKmax hno
  refine ⟨next,hr,hv.valid,?_,?_,?_,?_,hOther⟩
  · rw [vecAt_length_int hv,vecAt_length_int h,hnd]
  · rw [hv.contents,hresult,hD1,h.contents]
    exact hpre
  · rw [hv.contents,hresult,hD1,h.contents]
    exact hsuf
  · intro other hne
    rw [harrays,List.getElem?_set_ne (Ne.symm hne)]

theorem growat_last_plan (l : DictLayout) (s : MutableMemory α) (a mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (hn : 0 < n.val) (hnmax : n.val < 9223372036854775807) (d : I) (hd : 0 ≤ d.val) :
    Follows s (growendPlan l (geometryOf s a) d.val.toNat)
      ((growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a (n+one) d).run s)
      (fun _ next => next.validVector a ∧
        ((next.contents a).length : Int) = (s.contents a).length+d.val ∧
        (next.contents a).take n.val.toNat = s.contents a ∧
        (∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) ∧
        ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) := by
  have hni : (n+one).val = n.val+1 := ival_add_one n (by omega)
  have hi1 : n+one ≠ one := by
    intro hh
    have := congrArg Subtype.val hh
    rw [hni,ival_one] at this
    omega
  have hnlt : n < JInt.typemax .i64 := by
    rw [jlt_iff]
    have hm : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
    rw [hm]
    exact hnmax
  have hrun :
      (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a (n+one) d).run s =
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) a d).run s := by
    simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,ms_length,
      mutableLength_run s a _ h.1,hnlt,decide_true,eq_self_iff_true,Bool.true_and,ite_true]
  rw [hrun,opusGrowth.VecAt.geometry h]
  obtain ⟨herr,hok⟩ := growend_plan l h d hd
  refine ⟨herr,fun g hg => ?_⟩
  obtain ⟨next,mem',off',slots',hr,hv,harrays,hlen,hwindow,_,_,hOther,_⟩ := hok g hg
  refine ⟨(),next,hr,hv.valid,?_,?_,?_,hOther⟩
  · rw [vecAt_length_int hv,vecAt_length_int h,hlen]
  · rw [hv.contents,hwindow,h.contents]
  · intro other hne
    rw [harrays,List.getElem?_set_ne (Ne.symm hne)]

theorem growat_middle_overflow (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (a mem : Nat) (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hover : 9223372036854775807 < off.val-1+n.val+d.val) :
    (growat (mutableStorage layout) pure pure
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i d).run s =
      (.error .overflow,s) := by
  have hn := h.2.2.2.1
  have ho := h.2.2.1
  have hnb := ival_bounds n
  have hob := ival_bounds off
  have hdb := ival_bounds d
  have hi1 : i ≠ one := by intro hh; have := congrArg Subtype.val hh; rw [ival_one] at this; omega
  have hendb : (decide (n < JInt.typemax .i64) && decide (i = n+one)) = false := by
    by_cases hlt : n < JInt.typemax .i64
    · have hltN : n.val < 9223372036854775807 := by
        change n.val < (JInt.typemax .i64).val at hlt
        have hm : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
        rwa [hm] at hlt
      have hn1 : (n+one).val = n.val+1 := ival_add_one n (by omega)
      have hne : i ≠ n+one := by intro hh; have := congrArg Subtype.val hh; rw [hn1] at this; omega
      simp only [hlt,decide_true,hne,decide_false,Bool.true_and]
    · simp only [hlt,decide_false,Bool.false_and]
  have hd0 : d ≥ zero := by rw [ge_iff_le,jle_iff,ival_zero]; exact hd
  have hib : one < i ∧ i ≤ n := by rw [jlt_iff,jle_iff,ival_one]; exact ⟨hi,hin⟩
  have hom : (off-one).val = off.val-1 := ival_sub_one off (by omega)
  have hmem := mutableMemLength_run (layout := layout) s mem slots h.2.1
  simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,ms_length,mutableLength_run s a _ h.1,
    hendb,Bool.false_eq_true,hd0,decide_true,Bool.not_true,hib,and_self,ms_ref,ms_memory,ms_offset,
    mutableRef_run s a _ h.1,hmem]
  by_cases hfit : n.val+d.val ≤ 9223372036854775807
  · have hnd : (n+d).val = n.val+d.val := ival_add _ _ (by omega)
    have ha := ms_checkedAdd_run (layout := layout) s n d (by omega)
    have hb := ms_checkedAdd_overflow (layout := layout) s (off-one) (n+d) (by rw [hom,hnd]; omega)
    simp only [stateExcept_bind,ha,hb]
  · have ha := ms_checkedAdd_overflow (layout := layout) s n d (by omega)
    simp only [stateExcept_bind,ha]

theorem growth_extra_overflow_tail {β : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (n d : I) (hn : 0 ≤ n.val) (hd : 0 ≤ d.val)
    (hover : 9223372036854775807 < n.val+2*d.val+1) (next : I → MutationM α β) :
    (do
      let d2 ← (mutableStorage layout).checkedMul (JInt.wrap .i64 2) d
      let n2 ← (mutableStorage layout).checkedAdd n d2
      let n3 ← (mutableStorage layout).checkedAdd n2 one
      next n3).run s = (.error .overflow,s) := by
  by_cases hm : 2*d.val ≤ 9223372036854775807
  · have h2 : (JInt.wrap .i64 2*d).val = 2*d.val := ival_two_mul d hd hm
    have hmul := ms_checkedMul_run (layout := layout) s (JInt.wrap .i64 2) d (by rw [wval2]; omega)
    by_cases ha : n.val+2*d.val ≤ 9223372036854775807
    · have hn2 : (n+JInt.wrap .i64 2*d).val = n.val+2*d.val := by
        rw [ival_add _ _ (by rw [h2]; omega),h2]
      have hadd := ms_checkedAdd_run (layout := layout) s n (JInt.wrap .i64 2*d) (by rw [h2]; omega)
      have hlast := ms_checkedAdd_overflow (layout := layout) s (n+JInt.wrap .i64 2*d) one (by rw [hn2,ival_one]; omega)
      simp only [stateExcept_bind,hmul,hadd,hlast]
    · have hadd := ms_checkedAdd_overflow (layout := layout) s n (JInt.wrap .i64 2*d) (by rw [h2]; omega)
      simp only [stateExcept_bind,hmul,hadd]
  · have hmul := ms_checkedMul_overflow (layout := layout) s (JInt.wrap .i64 2) d (by rw [wval2]; omega)
    simp only [stateExcept_bind,hmul]

theorem growat_middle_extra_overflow (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (a mem : Nat) (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hi : 1 < i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ d.val)
    (hstart : i.val ≤ n.val/2 → off.val-1 < d.val)
    (hendroom : n.val/2 < i.val → (slots.length : Int) < off.val-1+n.val+d.val)
    (hov : off.val-1+n.val+d.val ≤ 9223372036854775807)
    (hover : 9223372036854775807 < n.val+2*d.val+1) :
    (growat (mutableStorage layout) pure pure
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i d).run s =
      (.error .overflow,s) := by
  have ho := h.2.2.1
  have hn := h.2.2.2.1
  have he := h.2.2.2.2.1
  have hc := h.2.2.2.2.2
  have hm := h.2.1
  have ha := h.1
  have hnb := ival_bounds n
  have hob := ival_bounds off
  have hdb := ival_bounds d
  have hib := ival_bounds i
  have hmem := mutableMemLength_run (layout := layout) s mem slots hm
  have hM : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hnd : (n+d).val = n.val+d.val := ival_add _ _ (by omega)
  have hom : (off-one).val = off.val-1 := ival_sub_one off (by omega)
  have hsum : (off-one+(n+d)).val = off.val-1+n.val+d.val := by
    rw [ival_add _ _ (by rw [hom,hnd]; omega),hom,hnd]; omega
  have hca := ms_checkedAdd_run (layout := layout) s n d (by omega)
  have hcb := ms_checkedAdd_run (layout := layout) s (off-one) (n+d) (by rw [hom,hnd]; omega)
  have hdiv := ms_divide_run (layout := layout) s n (JInt.wrap .i64 2) (by rw [wval2]; decide)
  have hQ : (JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)).val = n.val/2 := by
    rw [wval2]
    exact tdiv_nonneg_val n 2 hn (by decide) (by decide)
  have hi1 : i ≠ one := by intro hh; have := congrArg Subtype.val hh; rw [ival_one] at this; omega
  have hend : ¬ (n < JInt.typemax .i64 ∧ i = n+one) := by
    intro hh
    have hn1 : (n+one).val = n.val+1 := ival_add_one n (by
      have := hh.1
      change n.val < (JInt.typemax .i64).val at this
      have hmax : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
      rw [hmax] at this; omega)
    have := congrArg Subtype.val hh.2
    rw [hn1] at this
    omega
  have hendb : (decide (n < JInt.typemax .i64) && decide (i = n+one)) = false := by
    by_cases hnless : n < JInt.typemax .i64
    · have hne : i ≠ n+one := fun hh => hend ⟨hnless,hh⟩
      simp only [hnless,decide_true,hne,decide_false,Bool.true_and]
    · simp only [hnless,decide_false,Bool.false_and]
  have hd0 : d ≥ zero := by rw [ge_iff_le,jle_iff,ival_zero]; exact hd
  have hirange : one < i ∧ i ≤ n := by rw [jlt_iff,jle_iff,ival_one]; exact ⟨hi,hin⟩
  have hbr1 : (decide (i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)) &&
      decide (d ≤ off-one)) = false := by
    by_cases hp : i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)
    · have hpf : i.val ≤ n.val/2 := by simpa only [jle_iff,hQ] using hp
      have hs : ¬ d ≤ off-one := by rw [jle_iff,hom]; have := hstart hpf; omega
      simp only [hp,decide_true,hs,decide_false,Bool.true_and]
    · simp only [hp,decide_false,Bool.false_and]
  have hbr2 : (!decide (i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)) &&
      decide (JInt.wrap .i64 (slots.length : Int) ≥ off-one+(n+d))) = false := by
    by_cases hp : i ≤ JInt.wrap .i64 (n.val.tdiv (JInt.wrap .i64 2).val)
    · simp only [hp,decide_true,Bool.not_true,Bool.false_and]
    · have hpf : n.val/2 < i.val := by rw [jle_iff,hQ] at hp; omega
      have hs : ¬ JInt.wrap .i64 (slots.length : Int) ≥ off-one+(n+d) := by
        rw [ge_iff_le,jle_iff,hM,hsum]; have := hendroom hpf; omega
      simp only [hp,decide_false,Bool.not_false,hs,decide_false,Bool.true_and]
  obtain ⟨c,hcRun,_⟩ := ms_overallocation_val (layout := layout) s
    (JInt.wrap .i64 (slots.length : Int)) (by rw [hM]; omega)
  simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,
    mutableLength_run s a _ ha,hendb,hd0,decide_true,Bool.not_true,Bool.false_eq_true,
    hirange,and_self,ms_length,ms_ref,ms_memory,ms_offset,mutableRef_run s a _ ha,
    hmem,hca,hcb,hdiv,hbr2,ite_false]
  split
  · rename_i hb
    have hbi : i.val ≤ n.val/2 ∧ d.val ≤ off.val-1 := by
      simpa only [Bool.and_eq_true,decide_eq_true_eq,jle_iff,hQ,hom] using hb
    have := hstart hbi.1
    omega
  · simp only [stateExcept_bind,hcRun]
    have H := growth_extra_overflow_tail layout s n d hn hd hover (fun x => do
      let k := max c x
      let q ← (mutableStorage layout).divide (k-(n+d)) (JInt.wrap .i64 2)
      let newmem ← (mutableStorage layout).allocate mem k
      let newref ← (mutableStorage layout).memoryref newmem (q+one)
      (mutableStorage layout).copyRef newref (mem,off) (i-one)
      (mutableStorage layout).copyMemory newmem (q+one+d+i-one) mem (off+i-one) (n-i+one)
      (mutableStorage layout).setRef a newref
      (mutableStorage layout).setSize a (n+d))
    simpa only [stateExcept_bind] using H

theorem growat_native_bounds (layout : MemoryLayoutMetadata) (s : MutableMemory α) (a : Nat)
    (v : MutableVector) (ha : s.arrays[a]? = some v) (i d : I)
    (hi1 : i ≠ one) (hend : ¬ (v.size < JInt.typemax .i64 ∧ i = v.size+one))
    (hd : 0 ≤ d.val) (hout : ¬ (one < i ∧ i ≤ v.size)) :
    (growat (mutableStorage layout) pure pure
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i d).run s =
      (.error .bounds,s) := by
  have hendb : (decide (v.size < JInt.typemax .i64) && decide (i = v.size+one)) = false := by
    by_cases hn : v.size < JInt.typemax .i64
    · have hne : i ≠ v.size+one := fun hh => hend ⟨hn,hh⟩
      simp only [hn,decide_true,hne,decide_false,Bool.true_and]
    · simp only [hn,decide_false,Bool.false_and]
  have hd0 : d ≥ zero := by rw [ge_iff_le,jle_iff,ival_zero]; exact hd
  simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,ms_length,
    mutableLength_run s a v ha,hendb,Bool.false_eq_true,hd0,decide_true,Bool.not_true,
    hout,decide_false,Bool.not_false,ite_true,stateExcept_throw]

theorem follows_error_of_run {α ρ : Type} (s : MutableMemory α) (run : Except Error ρ × MutableMemory α)
    (post : ρ → MutableMemory α → Prop) (e : Error) (hr : run = (.error e,s)) :
    Follows s (.error e) run post := by
  refine ⟨fun e' he => ?_,fun g hg => ?_⟩
  · cases he
    exact hr
  · cases hg

theorem follows_ok_of_run {α ρ : Type} (s : MutableMemory α) (run : Except Error ρ × MutableMemory α)
    (post : ρ → MutableMemory α → Prop) (g : VectorGeometry)
    (hr : ∃ value next, run = (.ok value,next) ∧ post value next) :
    Follows s (.ok g) run post := by
  refine ⟨?_,fun _ _ => hr⟩
  intro e he
  cases he

theorem growth_length_nat (m : Nat) (n d : Int) (hn : 0 ≤ n) (hd : 0 ≤ d)
    (hm : (m : Int) = n+d) : m = n.toNat+d.toNat := by omega

theorem growat_plan_native (l : DictLayout) (s : MutableMemory α) (a mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hd : 0 ≤ d.val) :
    Follows s (growatPlan l (geometryOf s a) i.val d.val.toNat)
      ((growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a i d).run s)
      (fun _ next => next.validVector a ∧
        ((next.contents a).length : Int) = (s.contents a).length+d.val ∧
        (next.contents a).take (i.val-1).toNat = (s.contents a).take (i.val-1).toNat ∧
        (next.contents a).drop (i.val-1+d.val).toNat = (s.contents a).drop (i.val-1).toNat ∧
        (∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) ∧
        ∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) := by
  have ho := h.2.2.1
  have hn := h.2.2.2.1
  have he := h.2.2.2.2.1
  have hc := h.2.2.2.2.2
  have hnB := ival_bounds n
  have hiB := ival_bounds i
  have hN : ((n.val.toNat : Nat) : Int) = n.val := by omega
  have hD : ((d.val.toNat : Nat) : Int) = d.val := by omega
  have hO : ((off.val.toNat : Nat) : Int) = off.val := by omega
  have hOld : (s.contents a).length = n.val.toNat := by rw [h.contents,vwWindow_length h]
  have hMax : typemaxNat = 9223372036854775807 := by decide
  have hHalf : ((n.val.toNat/2 : Nat) : Int) = n.val/2 := by omega
  have hSum : (((off.val.toNat-1+(n.val.toNat+d.val.toNat)) : Nat) : Int) =
      off.val-1+n.val+d.val := by omega
  have hExtra : (((n.val.toNat+2*d.val.toNat+1) : Nat) : Int) = n.val+2*d.val+1 := by omega
  rw [opusGrowth.VecAt.geometry h]
  dsimp only [growatPlan]
  by_cases hfirst : i.val = 1
  · have hieq : i = one := Subtype.ext (hfirst.trans ival_one.symm)
    subst i
    simp only [ival_one,ite_true]
    have H := growat_one_plan l s a mem off n slots h d hd
    rw [opusGrowth.VecAt.geometry h] at H
    simp only [growatPlan,ite_true] at H
    refine ⟨H.1,fun g hg => ?_⟩
    obtain ⟨value,next,hr,hv,hlen,hdrop,hframe,hOther⟩ := H.2 g hg
    refine ⟨value,next,hr,hv,hlen,?_,?_,hframe,hOther⟩
    · simp only [ival_one,Int.sub_self,Int.toNat_zero,List.take_zero]
    · simpa only [ival_one,Int.sub_self,Int.zero_add,Int.toNat_zero,List.drop_zero] using hdrop
  · simp only [hfirst,ite_false]
    have hi1 : i ≠ one := by intro hh; have := congrArg Subtype.val hh; rw [ival_one] at this; exact hfirst this
    by_cases hend : n.val.toNat < typemaxNat ∧ i.val = (n.val.toNat : Int)+1
    · simp only [hend,ite_true]
      have hnmax : n.val < 9223372036854775807 := by rw [hMax] at hend; omega
      have hnpos : 0 < n.val := by omega
      have hn1 : (n+one).val = n.val+1 := ival_add_one n (by omega)
      have hieq : i = n+one := Subtype.ext (by rw [hn1]; omega)
      have hp : (((n.val.toNat : Int)+1)-1).toNat = n.val.toNat := by omega
      have hq : (((n.val.toNat : Int)+1)-1+d.val).toNat = n.val.toNat+d.val.toNat := by omega
      have H := growat_last_plan l s a mem off n slots h hnpos hnmax d hd
      rw [opusGrowth.VecAt.geometry h] at H
      rw [hieq]
      refine ⟨H.1,fun g hg => ?_⟩
      obtain ⟨value,next,hr,hv,hlen,hpre,hframe,hOther⟩ := H.2 g hg
      have hLenInt : ((next.contents a).length : Int) = n.val+d.val := by
        rw [vecAt_length_int h] at hlen
        exact hlen
      have hLenNat := growth_length_nat (next.contents a).length n.val d.val hn hd hLenInt
      refine ⟨value,next,hr,hv,hlen,?_,?_,hframe,hOther⟩
      · rw [hp,List.take_of_length_le (Nat.le_of_eq hOld)]
        exact hpre
      · rw [hq,hp]
        have hnew : (next.contents a).drop (n.val.toNat+d.val.toNat) = [] :=
          List.drop_eq_nil_of_le (by rw [hLenNat]; exact Nat.le_refl _)
        have hold : (s.contents a).drop n.val.toNat = [] := List.drop_eq_nil_of_le (by rw [hOld]; exact Nat.le_refl _)
        rw [hnew,hold]
    · simp only [hend,ite_false]
      have hendNative : ¬ (n < JInt.typemax .i64 ∧ i = n+one) := by
        intro hh
        have hmaxV : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
        have hnlt : n.val < 9223372036854775807 := by simpa only [jlt_iff,hmaxV] using hh.1
        have hn1 : (n+one).val = n.val+1 := ival_add_one n (by omega)
        have hiv := congrArg Subtype.val hh.2
        rw [hn1] at hiv
        apply hend
        rw [hMax]
        exact ⟨by omega,by omega⟩
      by_cases hidx : 1 < i.val ∧ i.val ≤ (n.val.toNat : Int)
      · simp only [hidx,not_true_eq_false,ite_false]
        have hii : 1 < i.val := hidx.1
        have hin : i.val ≤ n.val := by omega
        by_cases hover : typemaxNat < off.val.toNat-1+(n.val.toNat+d.val.toNat)
        · simp only [hover,ite_true]
          apply follows_error_of_run
          apply growat_middle_overflow (MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h i d hii hin hd
          rw [hMax] at hover
          omega
        · simp only [hover,ite_false]
          have hov : off.val-1+n.val+d.val ≤ 9223372036854775807 := by rw [hMax] at hover; omega
          by_cases hstart : i.val ≤ ((n.val.toNat/2 : Nat) : Int) ∧ d.val.toNat ≤ off.val.toNat-1
          · simp only [hstart,ite_true]
            apply follows_ok_of_run
            obtain ⟨next,hr,hv,hlen,hpre,hsuf,_,hframe,hOther⟩ := growat_startroom_post (MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h i d
              hii hin hd (by rw [← hHalf]; exact hstart.1) (by omega) hov
            exact ⟨(),next,hr,hv,hlen,hpre,hsuf,hframe,hOther⟩
          · simp only [hstart,ite_false]
            by_cases hendroom : ¬ i.val ≤ ((n.val.toNat/2 : Nat) : Int) ∧
                off.val.toNat-1+(n.val.toNat+d.val.toNat) ≤ slots.length
            · simp only [hendroom,ite_true]
              apply follows_ok_of_run
              obtain ⟨next,hr,hv,hlen,hpre,hsuf,_,hframe,hOther⟩ := growat_endroom_post (MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h i d
                hii hin hd (by rw [← hHalf]; omega) (by omega)
              exact ⟨(),next,hr,hv,hlen,hpre,hsuf,hframe,hOther⟩
            · simp only [hendroom,ite_false]
              have hNoStart : i.val ≤ n.val/2 → off.val-1 < d.val := by
                intro hp
                by_cases hfit : d.val ≤ off.val-1
                · exact False.elim (hstart ⟨by omega,by omega⟩)
                · omega
              have hNoEnd : n.val/2 < i.val → (slots.length : Int) < off.val-1+n.val+d.val := by
                intro hp
                by_cases hfit : off.val-1+n.val+d.val ≤ (slots.length : Int)
                · exact False.elim (hendroom ⟨by omega,by omega⟩)
                · omega
              by_cases hover2 : typemaxNat < n.val.toNat+2*d.val.toNat+1
              · simp only [hover2,ite_true]
                apply follows_error_of_run
                apply growat_middle_extra_overflow (MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h i d hii hin hd hNoStart hNoEnd hov
                rw [hMax] at hover2
                omega
              · simp only [hover2,ite_false]
                have hov2 : n.val+2*d.val+1 ≤ 9223372036854775807 := by rw [hMax] at hover2; omega
                let K := max (overallocationNat slots.length) (n.val.toNat+2*d.val.toNat+1)
                change Follows s (allocationPlan l K _) _ _
                obtain ⟨herr,hok⟩ := growat_alloc_post l s a mem off n slots h i d hii hin hd hNoStart hNoEnd hov hov2 K rfl
                by_cases hfit : memoryFits l K
                · simp only [allocationPlan,hfit,ite_true]
                  apply follows_ok_of_run
                  obtain ⟨next,hr,hv,hlen,hpre,hsuf,hframe,hOther⟩ := hok hfit
                  exact ⟨(),next,hr,hv,hlen,hpre,hsuf,hframe,hOther⟩
                · simp only [allocationPlan,hfit,ite_false]
                  exact follows_error_of_run _ _ _ _ (herr hfit)
      · simp only [hidx,not_false_eq_true,ite_true]
        apply follows_error_of_run
        apply growat_native_bounds (MemoryLayoutMetadata.ofRuntime l) s a ⟨(mem,off),n⟩ h.1 i d hi1 hendNative hd
        simpa only [jlt_iff,jle_iff,ival_one,hN] using hidx
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 3000000
attribute [local irreducible] JInt.wrap

theorem list_set_splice (xs : List α) (p : Nat) (x : α) (hp : p < xs.length) :
    xs.set p x = xs.take p ++ [x] ++ xs.drop (p+1) := by
  have H := (List.take_append_drop (p+1) (xs.set p x)).symm
  rw [list_set_take_succ xs p x hp,list_set_drop_of_lt xs p (p+1) x (by omega)] at H
  exact H
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 3000000
attribute [local irreducible] JInt.wrap

theorem growatPlan_ok_index (l : MemoryLayout) (g : VectorGeometry) (i : Int) (d : Nat)
    (next : VectorGeometry) (h : growatPlan l g i d = .ok next) :
    1 ≤ i ∧ i ≤ (g.length : Int)+1 := by
  by_cases h1 : i = 1
  · omega
  · by_cases he : g.length < typemaxNat ∧ i = (g.length : Int)+1
    · omega
    · by_cases hi : 1 < i ∧ i ≤ (g.length : Int)
      · omega
      · simp only [growatPlan,h1,ite_false,he,hi,not_false_eq_true,ite_true] at h
        cases h
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.ArrayFilter
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

attribute [local irreducible] JInt.wrap wrapInt

/-- A store into the first unused result slot preserves the accumulated prefix. -/
theorem batch1_filterStore (heap : VectorHeap α) (pre : List α) (old : Option α)
    (tail : List (Option α)) (x : α)
    (hn : pre.length + (old :: tail).length < 2 ^ 62) :
    (heapSet heap.length x (JInt.wrap .i64 ((pre.length : Int) + 1))).run
      (heap ++ [pre.map some ++ old :: tail]) =
      .ok ((), heap ++ [pre.map some ++ some x :: tail]) := by
  have hi : (JInt.wrap .i64 ((pre.length : Int) + 1)).val = pre.length + 1 :=
    ival_wrap _ (by simp only [List.length_cons] at hn; omega)
  have hs : (heap ++ [pre.map some ++ old :: tail])[heap.length]? =
      some (pre.map some ++ old :: tail) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  rw [heapSet_run _ _ _ hs _ (by rw [hi]; omega)
    (by rw [hi]; simp only [List.length_append, List.length_map, List.length_cons]; omega)]
  have hindex : ((pre.length : Int) + 1 - 1).toNat = pre.length := by omega
  rw [hi, hindex]
  have hslot : (pre.map some ++ old :: tail).set pre.length (some x) =
      pre.map some ++ some x :: tail := by
    rw [List.set_append_right _ _ (by simp only [List.length_map]; omega)]
    simp only [List.length_map, Nat.sub_self, List.set_cons_zero]
  rw [hslot, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
  rfl
end ChatGPTBatch1.ArrayFilter
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.ArrayRange
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4

attribute [local irreducible] JInt.wrap wrapInt

theorem batch1_integer_intLe (ops : BigIntegerOps) (ho : ops.Lawful) (i : I)
    (v : IntegerValue) : IntegerValue.intLe ops i v = decide (i.val ≤ v.val) := by
  cases v with
  | bit t v => exact JuliaLean.Proofs.base.int.le_eq i v
  | bool b =>
    cases b <;> simp only [IntegerValue.intLe, IntegerValue.val,
      JuliaLean.Proofs.base.int.le_eq, Bool.false_eq_true, ite_false, ite_true,
      show (JInt.wrap .i64 0).val = 0 from ival_wrap _ (by omega),
      show (JInt.wrap .i64 1).val = 1 from ival_wrap _ (by omega)]
  | big v => exact ho.2.2.2.2 i.val v

theorem batch1_integer_leInt (ops : BigIntegerOps) (ho : ops.Lawful) (v : IntegerValue)
    (i : I) : IntegerValue.leInt ops v i = decide (v.val ≤ i.val) := by
  cases v with
  | bit t v => exact JuliaLean.Proofs.base.int.le_eq v i
  | bool b =>
    cases b <;> simp only [IntegerValue.leInt, IntegerValue.val,
      JuliaLean.Proofs.base.int.le_eq, Bool.false_eq_true, ite_false, ite_true,
      show (JInt.wrap .i64 0).val = 0 from ival_wrap _ (by omega),
      show (JInt.wrap .i64 1).val = 1 from ival_wrap _ (by omega)]
  | big v => exact ho.2.2.2.2 v i.val
end ChatGPTBatch1.ArrayRange
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.Array

open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayFilter
open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayRange




open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

open JuliaLean.Proofs.base.array.round6b (IntegerArgument bytePointer)

attribute [local irreducible] JInt.wrap wrapInt

theorem batch1_stateBind_run (x : StateT σ (Except ε) α) (f : α → StateT σ (Except ε) β)
    (s : σ) : (x >>= f).run s =
      match x.run s with
      | .error e => .error e
      | .ok (a, s') => (f a).run s' := by
  simp only [StateT.run, StateT.bind, Bind.bind, Except.bind]
  cases x s with
  | error e => rfl
  | ok pair => cases pair; rfl

theorem batch1_statePure_run (a : α) (s : σ) :
    (pure a : StateT σ (Except ε) α).run s = .ok (a, s) := rfl
end ChatGPTBatch1.Array
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.src.genericmemory_c

theorem integerLiftRun {α β : Type} (x : Except Error β) (s : MutableMemory α) :
    (round4.stateExceptLift x : MutationM α β).run s = (x, s) := rfl

/-- A conversion error happens before the frozen unsetting call touches the store. -/
theorem unsetIntegerConversionError {α : Type} (runtime : DictLayout)
    (ops : round4.BigIntegerOps) (s : MutableMemory α) (a : Nat)
    (i : round4.IntegerValue) (e : Error)
    (he : round4.arrayToIndex ops i = .error e) :
    (unsetindexInteger (fun i => round4.stateExceptLift (round4.arrayToIndex ops i))
      (fun a i => do mutableUnset runtime a i; pure a) a i).run s = (.error e, s) := by
  simp only [unsetindexInteger, stateExcept_bind, integerLiftRun, he]
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


/- Allocation and collection partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

/-- Allocation of natural dimensions, retaining the actual allocation outcome. -/
theorem allocationNaturalDimensionsRun {Tag α : Type}
    (layout : Tag → Option MemoryLayout) (target : Tag) (el : MemoryLayout)
    (shape : List Nat) (heap : VectorHeap α)
    (hel : layout target = some el) (hfit : heapDimensionsFit shape = true) :
    (heapAllocateArray layout target shape).run heap =
      allocOutcome el target (shape.map (fun n : Nat => (n : Int))) heap := by
  unfold heapAllocateArray
  simp only [hfit, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [opusGrowth.heapArrayUndef_run layout target el hel,
    opusGrowth.dims_wrap_val shape hfit]

/-- The public allocation-domain checks suffice for the fresh heap allocation premise. -/
theorem allocationNaturalDimensionsSuccess {Tag α : Type}
    (layout : Tag → Option MemoryLayout) (target : Tag) (el : MemoryLayout)
    (shape : List Nat) (heap : VectorHeap α)
    (hel : layout target = some el) (hfit : heapDimensionsFit shape = true)
    (ha : arrayAllocError el (shape.map (fun n : Nat => (n : Int))) = none) :
    (heapAllocateArray layout target shape).run heap =
      .ok (⟨heap.length, target, shape, shape.map (fun n => (1, n))⟩,
        heap ++ [List.replicate shape.prod none]) := by
  rw [allocationNaturalDimensionsRun layout target el shape heap hel hfit]
  simp only [allocOutcome, ha, opusGrowth.dims_cast_toNat]
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


/- Allocation and collection partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192




/- Complete sorted deletion and splice proof -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.src.genericmemory_c
open JuliaLean.Proofs.base.array


/-- A bad second index is checked before any compaction; the Nowhere sink has changed nothing. -/
theorem deleteSecondInvalid {α : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (hv : VecAt s a mem off n slots) (i j : I) (post : List I)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val)
    (hbad : ¬ ((i + one).val ≤ j.val ∧ j.val ≤ n.val)) :
    (mutableDeleteatList layout a (i :: j :: post)).run s =
      (.error (if j.val < (i + one).val then .argument "indices must be unique and sorted"
        else .bounds), s) := by
  have hlen := mutableLength_run s a _ hv.1
  have hb : (mutableBounds a i).run s = (.ok (), s) := by
    rw [opusGrowth.vwBounds_run s a mem off n slots hv i, if_pos hi]
  have hpush := opusGrowth.vwPushNowhere_run s a mem off n slots hv i hi
  rw [opusGrowth.deleteatList_eq]
  simp only [deleteatIterator, stateExcept_bind, hlen, listIterator, stateExcept_pure,
    hb, hpush]
  rw [deleteatIterator.loop]
  simp only [listIterator, stateExcept_bind, stateExcept_pure, hbad, decide_false,
    Bool.not_false, ite_true]
  by_cases hj : j.val < (i + one).val <;>
    simp only [hj, ite_true, ite_false, stateExcept_throw, stateExcept_bind]
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


/- Allocation and collection partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192




/- Complete sorted deletion and splice proof -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192


/- Filtering partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4

attribute [local irreducible] JInt.wrap wrapInt

theorem filterBaseLiftRun {σ β : Type} (r : Except Error β) (s : σ) :
    (baseLift r : BaseM σ β).run s = (r, s) := by
  cases r <;> rfl

theorem filterLiftRun {σ K β : Type} (action : BaseM σ β)
    (q : JuliaLean.base.set.SetModel K) (s : σ) :
    ((liftV action).run q).run s =
      let r := action.run s
      (r.1.map (fun x => (x, q)), r.2) := by
  change (action >>= fun x => pure (x, q)).run s = _
  rw [stateExcept_bind]
  cases h : action.run s with
  | mk r state => cases r <;> rfl

theorem filterBindRun {σ K α β : Type} (action : SetVecG σ K α)
    (next : α → SetVecG σ K β) (q : JuliaLean.base.set.SetModel K) (s : σ) :
    ((action >>= next).run q).run s =
      let r := (action.run q).run s
      match r.1 with
      | .error e => (.error e, r.2)
      | .ok (x, q') => ((next x).run q').run r.2 := by
  change ((action.run q) >>= fun (x, q') => (next x).run q').run s = _
  rw [stateExcept_bind]
  cases h : (action.run q).run s with
  | mk r state =>
    cases r with
    | error e => rfl
    | ok pair => cases pair; rfl

/-- One filter iteration, after choosing the next input index and the current output index. -/
def filterIndexStep {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (input output : I) : SetVecG σ K (ForInStep I) := do
  let x ← liftV (v.ops.getAt input)
  liftV (v.ops.setAt x output)
  let keep ← liftV (baseLift (round4.boolResult f x))
  pure (.yield (if keep then output + one else output))

/-- Predicate errors stop a filter iteration after the element's output write. -/
theorem filterIndexStepPredicateError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (input output : I)
    (q : JuliaLean.base.set.SetModel K) (s afterRead afterWrite : σ) (x : K) (e : Error)
    (hread : (v.ops.getAt input).run s = (.ok x, afterRead))
    (hwrite : (v.ops.setAt x output).run afterRead = (.ok (), afterWrite))
    (hpred : round4.boolResult f x = .error e) :
    ((filterIndexStep v f input output).run q).run s = (.error e, afterWrite) := by
  simp only [filterIndexStep, filterBindRun, filterLiftRun, hread, hwrite, Except.map,
    filterBaseLiftRun, hpred]

/-- A finite filter loop stops at the first predicate error before its tail or final shrinking. -/
theorem filterIndexLoopPredicateError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (input output : I) (rest : List I)
    (q : JuliaLean.base.set.SetModel K) (s afterRead afterWrite : σ) (x : K) (e : Error)
    (hread : (v.ops.getAt input).run s = (.ok x, afterRead))
    (hwrite : (v.ops.setAt x output).run afterRead = (.ok (), afterWrite))
    (hpred : round4.boolResult f x = .error e) :
    ((forIn (input :: rest) output (filterIndexStep v f)).run q).run s = (.error e, afterWrite) := by
  simp only [List.forIn_cons, filterBindRun,
    filterIndexStepPredicateError v f input output q s afterRead afterWrite x e hread hwrite hpred]

/-- The source's post-loop resizing or tail-deletion phase. -/
def filterFinish {σ K : Type} (v : VectorOf σ K) (output : I) : SetVecG σ K (VectorOf σ K) := do
  if output > (← liftV v.ops.lastindex) then return v
  if v.ops.isVector then
    liftV (v.ops.resizeTo (output - one))
    liftV (v.ops.sizehintTo (output - one))
  else
    liftV (v.ops.deleteRange output (← liftV v.ops.lastindex))
  pure v

/-- The exact source filter consists of its indexed loop followed by its finalization phase. -/
theorem filterForInVector {σ K β : Type} (v : VectorOf σ K) (initial : β)
    (body : K → β → SetVecG σ K (ForInStep β)) :
    forIn v initial body = (do
      let first ← liftV v.ops.firstindex
      let last ← liftV v.ops.lastindex
      forIn (intRange first last) initial (fun i b => do
        body (← liftV (v.ops.getAt i)) b)) := rfl

/-- Expanding only the iteration interface exposes the exact source filter's indexed loop. -/
theorem filterVectorExpand {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) :
    vecFilterBangG (fun x => liftV (baseLift (round4.boolResult f x))) v = (do
      let output ← liftV v.ops.firstindex
      let first ← liftV v.ops.firstindex
      let last ← liftV v.ops.lastindex
      let output ← forIn (intRange first last) output (filterIndexStep v f)
      filterFinish v output) := by
  simp only [vecFilterBangG, filterBang, filterFinish,
    filterForInVector, pure_bind, bind_assoc]
  rfl
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion
open JuliaLean JuliaLean.base.array
open JuliaLean.Registry

abbrev Probe (A : Type) := ExceptT Error (StateM (List Nat)) A

def call (event : Nat) (answer : Except Error A) : Probe A := do
  modify (· ++ [event])
  match answer with
  | .ok value => pure value
  | .error error => throw error
end JuliaLean.Proofs.base.array.Completion


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion2
open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Completion2
abbrev Probe (A : Type) := ExceptT Error (StateM (List Nat)) A

def call (event : Nat) (answer : Except Error A) : Probe A := do
  modify (· ++ [event])
  match answer with
  | .ok value => pure value
  | .error error => throw error
end JuliaLean.Proofs.base.array.Completion2


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

abbrev Probe (A : Type) := ExceptT Error (StateM (List Nat)) A

def call (event : Nat) (answer : Except Error A) : Probe A := do
  modify (· ++ [event])
  match answer with
  | .ok value => pure value
  | .error error => throw error

/-- Every failure channel and divergence of the first native operation remains
observable, with the exact post-error world and without a later operation. -/
def FirstNativeFailure (first : NativeCopyM W X) (actual : NativeCopyM W Y) (before : W) : Prop :=
  match first.run.run before with
  | none => actual.run.run before = none
  | some (.error error) => actual.run.run before = some (.error error)
  | some (.ok (.error error, after)) => actual.run.run before = some (.ok (.error error, after))
  | some (.ok (.ok (.error error), after)) =>
    actual.run.run before = some (.ok (.ok (.error error), after))
  | some (.ok (.ok (.ok _), _)) => True
end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion4
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion4
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

abbrev M (W A : Type) := ExceptT JuliaLean.base.ntuple.NtupleError (ExceptT Error (StateM W)) A
end JuliaLean.Proofs.base.array.Completion4


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Models1Group13

/-- An allocation preserves pre-existing header and memory objects. This says
nothing about fresh backing identity for zero-length memories. -/
def PriorObjectsPreserved {α : Type} (before after : MutableMemory α) : Prop :=
  after.arrays.take before.arrays.length = before.arrays ∧
  after.memories.take before.memories.length = before.memories

/-- A fresh vector exposes exactly the supplied values, preserving their
reference identities and order, and has the specified native length. -/
def FreshVectorContents {α : Type} (before after : MutableMemory α)
    (handle : Nat) (values : List α) : Prop :=
  before.arrays.length ≤ handle ∧
  after.validVector handle ∧
  after.contents handle = values.map some ∧
  (mutableLength (α := α) handle).run after =
    (.ok (JInt.wrap .i64 values.length), after) ∧
  PriorObjectsPreserved before after
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean
open JuliaLean.base.array.Models1Group13

abbrev NativeM := JuliaLean.base.io.M
abbrev NativeError := JuliaLean.base.io.Error

/-- An observation of the existing Core/C and RefValue interface dependencies,
before computing a Julia stride. `inlineExtent` contains raw payload/alignment
numbers, never a model result. Native allocator and RefValue semantics remain
at their existing supplied boundary; no correctness law is assumed. -/
inductive LayoutObservation (World : Type) where
  | diverged
  | failed (error : NativeError) (world : World)
  | pointerSlot (world : World)
  | inlineExtent (payload alignment : Int) (world : World)

/-- Destruct one existing runtime/interface boundary operation's result.
A failure records its resulting world; a diverging operation has no continuation.
The same observer handles Core/C operations and the existing RefValue constructor
and index interfaces. It assumes no correctness law about any operation. -/
def ObserveNative {World A : Type} (action : NativeM World A) (before : World)
    (next : A → World → LayoutObservation World → Prop)
    (observed : LayoutObservation World) : Prop :=
  match action before with
  | none => observed = .diverged
  | some (.error (error, after)) => observed = .failed error after
  | some (.ok (value, after)) => next value after observed

/-- Native datatype-layout observation. Uses only the raw layout pointer and
load, not the modeled datatypeAlignment or alignedSizeof functions. The null
layout exception is the source DataTypeLayout guard (base/runtime_internals.jl:644). -/
def ObserveAlignment
    (types : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym)
    (datatype : D) (before : World)
    (next : Int → World → LayoutObservation World → Prop)
    (observed : LayoutObservation World) : Prop :=
  if types.isNull (types.layout datatype) then
    observed = .failed (.foreignError "UndefRefError" "null datatype layout") before
  else
    ObserveNative (types.loadLayout (types.layout datatype)) before
      (fun layout after => next layout.alignment.val after) observed

/-- Observe the existing RefValue constructor/index interfaces, raw union-layout
C boundary, and the two checked UInt-to-Int conversions. The C call's boolean is deliberately not treated as a correctness
promise: aligned_sizeof ignores it after selecting the inline union branch. -/
def ObserveUnionLayout
    (runtime : LayoutBoundary World V D N Mod P Sym Ref)
    (elementType : V) (before : World) (observed : LayoutObservation World) : Prop :=
  ObserveNative (runtime.newRef (JInt.wrap .u64 0)) before
    (fun sizeRef afterSizeRef =>
      ObserveNative (runtime.newRef (JInt.wrap .u64 0)) afterSizeRef
        (fun alignmentRef afterAlignmentRef =>
          ObserveNative (runtime.jlIslayoutInline elementType sizeRef alignmentRef)
            afterAlignmentRef
            (fun _ afterCall =>
              ObserveNative (runtime.readRef sizeRef) afterCall
                (fun size afterSizeRead observed =>
                  if IntTy.i64.max < size.val then
                    observed = .failed (.jl (.inexactError "convert")) afterSizeRead
                  else
                    ObserveNative (runtime.readRef alignmentRef) afterSizeRead
                      (fun alignment afterAlignmentRead observed =>
                        if IntTy.i64.max < alignment.val then
                          observed = .failed (.jl (.inexactError "convert")) afterAlignmentRead
                        else
                          observed = .inlineExtent size.val alignment.val afterAlignmentRead)
                      observed)))) observed

/-- Observe nonunion inline native metadata. The singleton type alias is
normalized before the datatype layout is loaded; alignment precedes Core.sizeof,
in contrast to the Ptr method. -/
def ObserveInlineDatatype
    (types : JuliaLean.base.runtime_internals.TypeOps World V D N Mod P Sym)
    (elementType : V) (before : World) (observed : LayoutObservation World) : Prop :=
  let effectiveType :=
    if types.egal elementType types.typeOfBottomType then types.coreTypeofBottom
    else elementType
  match types.asDatatype effectiveType with
  | none =>
      observed = .failed (.foreignError "MethodError" "datatype_alignment") before
  | some datatype =>
      ObserveAlignment types datatype before
        (fun alignment afterAlignment =>
          ObserveNative (types.coreSizeof effectiveType) afterAlignment
            (fun payload final observed =>
              observed = .inlineExtent payload.val alignment final)) observed

/-- Raw storage-layout observations selected by the native Julia type metadata.
No invocation of elsizeArrayRuntime, alignedSizeof, uniontypeLayout, or alignInt
appears in this relation. It produces raw metadata, not an expected stride. -/
def ObserveArrayLayout
    (runtime : LayoutBoundary World V D N Mod P Sym Ref)
    (elementType : V) (before : World) (observed : LayoutObservation World) : Prop :=
  if (runtime.types.asUnion elementType).isSome then
    if (runtime.jlStoredInline elementType).val = 0 then
      observed = .pointerSlot before
    else
      ObserveUnionLayout runtime elementType before observed
  else if (runtime.jlStoredInline elementType).val = 0 then
    observed = .pointerSlot before
  else
    ObserveInlineDatatype runtime.types elementType before observed

/-- Mathematical minimal aligned extent, independently of LLT_ALIGN's bitwise
expression. Signed-word residues allow wraparound without imposing an invented
no-overflow restriction. The power-of-two guard is an actual native layout
invariant; malformed boundary alignments are still included in the protocol. -/
def MinimalAlignedWord (payload alignment : Int) (result : JInt .i64) : Prop :=
  ∀ k : Nat, alignment = (2 : Int) ^ k →
    ∃ padded : Int,
      payload ≤ padded ∧ padded < payload + alignment ∧ padded % alignment = 0 ∧
      result.val % (2 : Int) ^ 64 = padded % (2 : Int) ^ 64
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

abbrev NativeCopyFailure :=
  Sum Error (Sum JuliaLean.base.abstractarray.ArrayError JuliaLean.base.io.Error)

abbrev NativeCopyResult (World A : Type) :=
  Option (Except (NativeCopyFailure × World) (A × World))

/-- Observe each error family without collapsing its class, preserve the exact
post-error world, and retain divergence. This is a result representation map. -/
def NativeCopyObserve (action : NativeCopyM World A) (before : World) : NativeCopyResult World A :=
  match action.run.run before with
  | none => none
  | some (.error (error, after)) => some (.error (.inr (.inr error), after))
  | some (.ok (.error error, after)) => some (.error (.inr (.inl error), after))
  | some (.ok (.ok (.error error), after)) => some (.error (.inl error, after))
  | some (.ok (.ok (.ok value), after)) => some (.ok (value, after))

/-- Mathematical cardinality, independent of the model's native length code. -/
def NativeCopyArrayCount (a : NativeCopyArray T) : Nat :=
  (a.dimensions.map (fun dimension => dimension.val.toNat)).prod

/-- Independent physical reference at an element offset. Arithmetic here is
mathematical and converts to the stored UInt representation only at the end.
Sources: src/genericmemory.c:262,311-323; base/pointer.jl:75-87. -/
def NativeCopyRefAt (memory : NativeCopyMemory T) (offset : Nat) : NativeCopyRef T :=
  ⟨memory, JInt.wrap .u64
    (if memory.arrayElement = 2 ∨ memory.layoutBytes.val = 0 then (offset : Int)
     else memory.ptr.address.val + (offset : Int) * memory.layoutBytes.val)⟩

/-- Necessary native header/byte-range invariants, including wrapped Memory's
larger admissible capacity. Distinct memories may share any byte addresses.
This does not certify allocator/collector metadata or native type construction.
Source: src/genericmemory.c:109-165; base/pointer.jl:75-87. -/
def NativeCopyMemoryValid (world : NativeCopyWorld State) (memory : NativeCopyMemory T) : Prop :=
  0 ≤ memory.capacity.val ∧ memory.capacity.val < 2 ^ 63 - 1 ∧
  0 ≤ memory.layoutBytes.val ∧
  (memory.arrayElement = 0 ∨ memory.arrayElement = 1 ∨ memory.arrayElement = 2) ∧
  let footprint := memory.capacity.val * memory.layoutBytes.val +
    (if memory.arrayElement = 2 then memory.capacity.val else 0)
  footprint < 2 ^ 63 - 1 ∧ memory.ptr.address.val + footprint ≤ 2 ^ 64 ∧
  ∀ byte : Nat, (byte : Int) < footprint →
    world.bytes.validByte (memory.ptr.address.val.toNat + byte) = true

/-- Every actual native rank is admitted; dimensions and the represented
reference window are checked independently of the model's length/ref helpers.
No separation from any other Array/Memory is required. -/
def NativeCopyArrayValid (world : NativeCopyWorld State) (a : NativeCopyArray T) : Prop :=
  NativeCopyMemoryValid world a.ref.mem ∧ a.dimensions.length < 2 ^ 63 ∧
  (∀ dimension ∈ a.dimensions, 0 ≤ dimension.val) ∧
  ∃ offset : Nat, offset + NativeCopyArrayCount a ≤ a.ref.mem.capacity.val.toNat ∧
    a.ref = NativeCopyRefAt a.ref.mem offset

/-- Discard only a successful native Cvoid result. Errors, their post-error
worlds, and divergence are preserved exactly; this is not a callee law. -/
def NativeCopyReturn (dest : A) (observed : NativeCopyResult World Unit) : NativeCopyResult World A :=
  match observed with
  | none => none
  | some (.error error) => some (.error error)
  | some (.ok (_, after)) => some (.ok (dest, after))

/-- Independent Cvoid address observation. The raw field is already a physical
address for ordinary nonzero-size storage; unions and zero-size storage use an
element offset, so their byte address is base plus offset times layout size.
Only the final mathematical residue is represented as a native UInt pointer.
No modeled pointer-conversion or reference-shift function is called. Sources:
base/pointer.jl:75-87; src/genericmemory.c:262. -/
def NativeCopyCvoidAddress (reference : NativeCopyRef T) :
    JuliaLean.base.pointer.Ptr Unit :=
  let address : Int :=
    if reference.mem.arrayElement = 2 ∨ reference.mem.layoutBytes.val = 0 then
      reference.mem.ptr.address.val +
        reference.ptr_or_offset.val * reference.mem.layoutBytes.val
    else
      reference.ptr_or_offset.val
  ⟨JInt.wrap .u64 (address % (2 : Int) ^ 64)⟩
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Observe an existing raw native operation, preserving its exact error and
post-error world or its divergence. The continuation runs only after success.
This is a result representation observer, not a Base implementation. -/
def NativeAllocationContinue
    (action : LayoutM (NativeCopyWorld State) A) (before : NativeCopyWorld State)
    (next : A → NativeCopyWorld State → NativeCopyResult (NativeCopyWorld State) B) :
    NativeCopyResult (NativeCopyWorld State) B :=
  match action before with
  | none => none
  | some (.error (error, after)) => some (.error (.inr (.inr error), after))
  | some (.ok (value, after)) => next value after

/-- Independent native Memory allocation request. Type validity precedes the
zero-count branch. Mathematical unsigned element and payload/tag byte counts
express the address-width bounds without executing overflow intrinsics or any
modeled allocation/check function. The native empty/allocate action is then
observed directly, without a success or freshness law. Sources:
src/genericmemory.c:55-102; src/builtins.c:2233-2241. -/
def NativeMemoryRequest (allocation : NativeAllocationBoundary State T)
    (signedCount : Int) (before : NativeCopyWorld State)
    (next : NativeCopyMemory T → NativeCopyWorld State →
      NativeCopyResult (NativeCopyWorld State) A) :
    NativeCopyResult (NativeCopyWorld State) A :=
  match allocation.layout with
  | none => some (.error (.inl (.typeError "GenericMemory"), before))
  | some metadata =>
      let count := (signedCount % (2 : Int) ^ 64).toNat
      if count = 0 then
        NativeAllocationContinue allocation.empty before next
      else
        let bytes := count * (if metadata.isboxed then 8 else metadata.size) +
          (if metadata.isunion then count else 0)
        if count < 2 ^ 63 - 2 ∧ bytes < 2 ^ 63 - 2 then
          NativeAllocationContinue (allocation.allocate count) before next
        else
          some (.error (.inl (.argument
            "invalid GenericMemory size: the number of elements is either negative or too large for system address width"), before))

/-- Independently requested Core Array header. Its reference is constructed
mathematically at Memory offset zero. The result records precisely the native
identity, selected static element type T, raw reference and requested shape.
The supplied native identity itself is not presumed fresh. Sources:
base/boot.jl:821-838; src/genericmemory.c:262. -/
def NativeHeaderRequest (allocation : NativeAllocationBoundary State T)
    (dimensions : List I) (memory : NativeCopyMemory T) (before : NativeCopyWorld State) :
    NativeCopyResult (NativeCopyWorld State) (NativeCopyArray T) :=
  let reference := NativeCopyRefAt memory 0
  NativeAllocationContinue (allocation.headerIdentity reference dimensions) before
    (fun identity after => some (.ok (⟨identity, reference, dimensions⟩, after)))

/-- Mathematical element count for a native shape. An empty tuple has count
one; a zero dimension makes the product zero without an overflow limit on
intermediate mathematical products. -/
def NativeRequestedCount (dimensions : List I) : Int :=
  (dimensions.map (fun dimension => dimension.val)).prod

/-- Independent Array-dimension rejection. Rank zero and one defer directly
to Memory allocation. At rank at least two, every dimension must be nonnegative
and strictly below typemax(Int); absent a zero dimension, the complete product
must fit signed Int. Using the complete mathematical product includes source
zero-product suppression of earlier multiplication overflow. Sources:
base/boot.jl:782-818. -/
def NativeArrayDimensionsRejected (dimensions : List I) : Bool :=
  decide (2 ≤ dimensions.length) &&
    (dimensions.any (fun dimension =>
      decide (dimension.val < 0 ∨ (2 : Int) ^ 63 - 1 ≤ dimension.val)) ||
      decide ((2 : Int) ^ 63 - 1 < NativeRequestedCount dimensions))

/-- Complete independent Array allocation/header protocol. Invalid multidimensional
shapes fail before type/native allocation checks. Otherwise the mathematical
count selects the native Memory request, then the Core header request. Every
native error/effect/divergence is retained; no uninitialized value is fabricated.
Sources: base/boot.jl:782-838; src/genericmemory.c:55-102. -/
def NativeUndefRequest (allocation : NativeAllocationBoundary State T)
    (dimensions : List I) (before : NativeCopyWorld State) :
    NativeCopyResult (NativeCopyWorld State) (NativeCopyArray T) :=
  if NativeArrayDimensionsRejected dimensions then
    some (.error (.inl (.argument "invalid Array dimensions"), before))
  else
    NativeMemoryRequest allocation (NativeRequestedCount dimensions) before
      (fun memory after => NativeHeaderRequest allocation dimensions memory after)
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
namespace JuliaLean.Proofs.base.array.Completion3

theorem nativeCopy_bind_run {W X Y : Type} (first : NativeCopyM W X)
    (next : X → NativeCopyM W Y) (before : W) :
    (first >>= next).run.run before =
      match first.run.run before with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok (.error error, world)) => some (.ok (.error error, world))
      | some (.ok (.ok (.error error), world)) => some (.ok (.ok (.error error), world))
      | some (.ok (.ok (.ok value), world)) => (next value).run.run world := by
  cases h : first.run.run before with
  | none =>
    simp_all [ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, bind, pure]
  | some result =>
    cases result with
    | error error =>
      simp_all [ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, bind, pure]
    | ok result =>
      rcases result with ⟨result, world⟩
      cases result with
      | error error =>
        simp_all [ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, bind, pure]
      | ok result =>
        cases result <;>
          simp_all [ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, bind, pure]

theorem firstNativeFailure_bind {W X Y : Type} (first : NativeCopyM W X)
    (next : X → NativeCopyM W Y) (before : W) :
    FirstNativeFailure first (first >>= next) before := by
  unfold FirstNativeFailure
  rw [nativeCopy_bind_run]
  cases h : first.run.run before with
  | none => rfl
  | some result =>
    cases result with
    | error error => rfl
    | ok result =>
      rcases result with ⟨result, world⟩
      cases result with
      | error error => rfl
      | ok result =>
        cases result with
        | error error => rfl
        | ok value => trivial
theorem firstNativeFailure_bind_right {W X Y Z : Type}
    (first : NativeCopyM W X) (middle : NativeCopyM W Y)
    (next : Y → NativeCopyM W Z) (before : W)
    (h : FirstNativeFailure first middle before) :
    FirstNativeFailure first (middle >>= next) before := by
  unfold FirstNativeFailure at *
  rw [nativeCopy_bind_run]
  cases hf : first.run.run before with
  | none => simp_all
  | some result =>
    cases result with
    | error error => simp_all
    | ok result =>
      rcases result with ⟨result, world⟩
      cases result with
      | error error => simp_all
      | ok result =>
        cases result with
        | error error => simp_all
        | ok value => trivial

end JuliaLean.Proofs.base.array.Completion3
