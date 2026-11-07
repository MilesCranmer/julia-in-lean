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
import JuliaLean.Proofs.base.array.common.grow
import JuliaLean.Proofs.base.array.deleteat_splice

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
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
set_option maxHeartbeats 1000000

theorem spliceStores_error {α β : Type} (convert : β → Except Error α)
    (a mem : Nat) (off n i : I) (hi : 1 ≤ i.val) :
    ∀ (xs : List β) (s : MutableMemory α) (slots : List (Option α)) (p : Nat) (k : I) (error : Error),
    VecAt s a mem off n slots → i.val - 1 + p + xs.length ≤ n.val →
    (xs ≠ [] → k.val = p + 1) → xs.mapM convert = .error error →
    ((forIn xs k (fun x k => do
        let value ← stateExceptLift (convert x)
        mutableSet a value (i + k - one)
        pure (ForInStep.yield (k + one)))).run s).1 = .error error := by
  intro xs
  induction xs with
  | nil =>
    intro s slots p k error hv hcap hk hmap
    simp [List.mapM_nil, pure, Except.pure] at hmap
  | cons x xs ih =>
    intro s slots p k error hv hcap hk hmap
    have hkval := hk (by simp)
    cases hc : convert x with
    | error headError =>
      have he : headError = error := by
        simpa [List.mapM_cons, hc, Bind.bind, Except.bind, pure, Except.pure] using hmap
      subst headError
      simp only [List.forIn_cons,stateExcept_bind,stateExceptLift_run,hc]
    | ok replacement =>
      have hm : xs.mapM convert = .error error := by
        cases hrest : xs.mapM convert with
        | error e =>
          simpa [List.mapM_cons, hc, hrest, Bind.bind, Except.bind, pure, Except.pure] using hmap
        | ok values =>
          simp [List.mapM_cons, hc, hrest, Bind.bind, Except.bind, pure, Except.pure] at hmap
      have hn0 := hv.2.2.2.1
      have hnb := ival_bounds n
      have hj : (i + k - one).val = i.val + p := by
        rw [ival_add_sub_one i k (by simp only [List.length_cons] at hcap; rw [hkval]; omega), hkval]
        omega
      have hjin : 1 ≤ (i + k - one).val ∧ (i + k - one).val ≤ n.val := by
        rw [hj]
        simp only [List.length_cons] at hcap
        omega
      let mid : MutableMemory α :=
        { s with memories := s.memories.set mem (slots.set (off.val - 1 + (i + k - one).val - 1).toNat (some replacement)) }
      have hmid : VecAt mid a mem off n
          (slots.set (off.val - 1 + (i + k - one).val - 1).toNat (some replacement)) := hv.set _ _
      have hnext : xs ≠ [] → (k + one).val = (p + 1 : Nat) + 1 := by
        intro hne
        have hxlen : 0 < xs.length := List.length_pos_iff.mpr hne
        simp only [List.length_cons] at hcap
        rw [ival_add_one k (by rw [hkval]; omega), hkval]
        omega
      have hr := ih mid _ (p + 1) (k + one) error hmid
        (by simp only [List.length_cons] at hcap; omega) hnext hm
      simp only [List.forIn_cons,stateExcept_bind,stateExceptLift_run,hc,
        vwSet_run s a mem off n slots hv (i + k - one) hjin replacement,stateExcept_pure]
      exact hr
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
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4
set_option maxHeartbeats 1000000

theorem deleteatWindow_index_inexact {layout : MemoryLayoutMetadata} (α : Type)
    (ops : BigIntegerOps)
    (hops : ops.Lawful) (s : MutableMemory α) (handle : Nat) (i delta : IntegerValue)
    (hi : ¬ i.fits) :
    (windowDelete α (layout := layout) ops handle i delta).run s = (.error .inexact, s) := by
  have hf : ¬ (IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max) := hi
  unfold windowDelete deleteatWindow
  rw [stateExcept_bind, JuliaLean.Proofs.base.array.opusGrowth.integerToInt_run,
    JuliaLean.Proofs.base.array.opusGrowth.integerValue_toInt hops]
  rw [if_neg hf]

theorem deleteatWindow_negative {layout : MemoryLayoutMetadata} (α : Type)
    (ops : BigIntegerOps) (hops : ops.Lawful) (s : MutableMemory α) (handle : Nat)
    (i delta : IntegerValue) (hvalid : s.validVector handle)
    (hi : i.fits) (hdelta : delta.val < 0) :
    (windowDelete α (layout := layout) ops handle i delta).run s =
      (.error (.argument "_deleteat! requires delta >= 0"), s) := by
  obtain ⟨_, _, _, _, h⟩ := validVector_vecAt hvalid
  have hi' : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := by
    simpa [IntegerValue.fits] using hi
  have hnot : ¬ (0 ≤ delta.val) := by omega
  unfold windowDelete
  simp only [deleteatWindow, stateExcept_bind,
    JuliaLean.Proofs.base.array.opusGrowth.integerToInt_run,
    JuliaLean.Proofs.base.array.opusGrowth.integerValue_toInt hops,
    if_pos hi', mutableLength_run s handle _ h.1, hnot, decide_false, Bool.not_false,
    ite_true, stateExcept_throw]

theorem deleteatWindow_index_bounds {layout : MemoryLayoutMetadata} (α : Type)
    (ops : BigIntegerOps) (hops : ops.Lawful) (s : MutableMemory α) (handle : Nat)
    (i delta : IntegerValue) (hvalid : s.validVector handle) (hi : i.fits)
    (hdelta : 0 ≤ delta.val)
    (hout : i.val < 1 ∨ (s.contents handle).length < i.val) :
    (windowDelete α (layout := layout) ops handle i delta).run s = (.error .bounds, s) := by
  obtain ⟨_, _, n, _, h⟩ := validVector_vecAt hvalid
  have hwl := vwWindow_length h
  have hc := h.contents
  have hlen : ((s.contents handle).length : Int) = n.val := by
    have hn0 := h.2.2.2.1
    rw [hc, hwl]
    omega
  have hi' : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := by
    simpa [IntegerValue.fits] using hi
  have hw : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ hi'
  have hnot : ¬ (one ≤ JInt.wrap .i64 i.val ∧ JInt.wrap .i64 i.val ≤ n) := by
    rw [jle_iff, jle_iff, ival_one, ← hlen]
    omega
  unfold windowDelete
  simp only [deleteatWindow, stateExcept_bind,
    JuliaLean.Proofs.base.array.opusGrowth.integerToInt_run,
    JuliaLean.Proofs.base.array.opusGrowth.integerValue_toInt hops, if_pos hi',
    mutableLength_run s handle _ h.1, hdelta, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, hnot, decide_false, Bool.not_false, ite_true,
    stateExcept_throw]

theorem deleteatWindow_count_bounds {layout : MemoryLayoutMetadata} (α : Type)
    (ops : BigIntegerOps) (hops : ops.Lawful) (s : MutableMemory α) (handle : Nat)
    (i delta : IntegerValue) (hvalid : s.validVector handle)
    (hlenSmall : ((s.contents handle).length : Int) < 2 ^ 62)
    (hi : i.fits) (hdelta : 0 ≤ delta.val) (hi1 : 1 ≤ i.val)
    (hin : i.val ≤ (s.contents handle).length)
    (hbig : (s.contents handle).length + 1 - i.val < delta.val) :
    (windowDelete α (layout := layout) ops handle i delta).run s = (.error .bounds, s) := by
  obtain ⟨_, _, n, _, h⟩ := validVector_vecAt hvalid
  have hwl := vwWindow_length h
  have hc := h.contents
  have hn0 := h.2.2.2.1
  have hlen : ((s.contents handle).length : Int) = n.val := by rw [hc, hwl]; omega
  have hi' : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := by
    simpa [IntegerValue.fits] using hi
  have hw : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ hi'
  have hbound : 1 ≤ i.val ∧ i.val ≤ n.val := by rw [← hlen]; exact ⟨hi1, hin⟩
  have hidx : one ≤ JInt.wrap .i64 i.val ∧ JInt.wrap .i64 i.val ≤ n := by
    rw [jle_iff, jle_iff, ival_one, hw]
    exact hbound
  have hnsmall : n.val < 2 ^ 62 := by rw [← hlen]; exact hlenSmall
  have hsum : IntTy.i64.min ≤ n.val + 1 - i.val ∧ n.val + 1 - i.val ≤ IntTy.i64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hleft : (n + one - JInt.wrap .i64 i.val).val = n.val + 1 - i.val := by
    have h := ival_add_sub n one (JInt.wrap .i64 i.val) (by rw [ival_one, hw]; exact hsum)
    rw [ival_one, hw] at h
    exact h
  have hbig' : n.val + 1 - i.val < delta.val := by rw [← hlen]; exact hbig
  have hcount : ¬ (delta.val ≤ (n + one - JInt.wrap .i64 i.val).val) := by
    rw [hleft]
    omega
  unfold windowDelete
  simp only [deleteatWindow, stateExcept_bind,
    JuliaLean.Proofs.base.array.opusGrowth.integerToInt_run,
    JuliaLean.Proofs.base.array.opusGrowth.integerValue_toInt hops, if_pos hi',
    mutableLength_run s handle _ h.1, hdelta, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, hidx, and_self, hcount, decide_false,
    Bool.not_false, ite_true, stateExcept_throw]
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
open JuliaLean.Proofs.base.array.round4 JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 2000000
attribute [local irreducible] JInt.wrap

theorem bool64_val (b : Bool) : (JInt.wrap .i64 (if b then 1 else 0)).val = (if b then 1 else 0) := by
  cases b <;> apply ival_wrap <;> decide

theorem promote_ri64_range (t : IntTy) :
    (t.promote .i64).min ≤ 0 ∧ 9223372036854775807 ≤ (t.promote .i64).max := by
  cases t <;> decide

theorem addInteger_val (ops : BigIntegerOps) (hops : ops.Lawful) (a : I) (x : IntegerValue)
    (hb : 0 ≤ a.val+x.val ∧ a.val+x.val ≤ 9223372036854775807) :
    (x.addInt ops a).val = a.val+x.val := by
  cases x with
  | bit t y =>
    simp only [IntegerValue.val] at hb
    simp only [IntegerValue.addInt,IntegerValue.val]
    rw [JuliaLean.Proofs.base.range.binop_val JuliaLean.base.int.add
      (fun a b => JuliaLean.Proofs.base.int.add_int_val a b)]
    obtain ⟨hmin,hmax⟩ := promote_i64_range t
    exact wrapInt_of_inRange _ _ ⟨by omega,by omega⟩
  | bool b =>
    simp only [IntegerValue.val] at hb
    simp only [IntegerValue.addInt,IntegerValue.val,JuliaLean.base.int.add,
      JuliaLean.Proofs.base.int.add_int_val,bool64_val]
    exact wrapInt_of_inRange _ _ ⟨by change -9223372036854775808 ≤ _; omega,by exact hb.2⟩
  | big v => simp only [IntegerValue.addInt,IntegerValue.val,hops.2.1]

theorem subFromInteger_val (ops : BigIntegerOps) (hops : ops.Lawful) (a : I) (x : IntegerValue)
    (hb : 0 ≤ a.val-x.val ∧ a.val-x.val ≤ 9223372036854775807) :
    (x.subFromInt ops a).val = a.val-x.val := by
  cases x with
  | bit t y =>
    simp only [IntegerValue.val] at hb
    simp only [IntegerValue.subFromInt,IntegerValue.val]
    rw [JuliaLean.Proofs.base.range.binop_val_sub JuliaLean.base.int.sub
      (fun a b => JuliaLean.Proofs.base.int.sub_int_val a b)]
    obtain ⟨hmin,hmax⟩ := promote_i64_range t
    exact wrapInt_of_inRange _ _ ⟨by omega,by omega⟩
  | bool b =>
    simp only [IntegerValue.val] at hb
    simp only [IntegerValue.subFromInt,IntegerValue.val,JuliaLean.base.int.sub,
      JuliaLean.Proofs.base.int.sub_int_val,bool64_val]
    exact wrapInt_of_inRange _ _ ⟨by change -9223372036854775808 ≤ _; omega,by exact hb.2⟩
  | big v => simp only [IntegerValue.subFromInt,IntegerValue.val,hops.2.2.1]

theorem subInteger_val (ops : BigIntegerOps) (hops : ops.Lawful) (x : IntegerValue) (a : I)
    (hb : 0 ≤ x.val-a.val ∧ x.val-a.val ≤ 9223372036854775807) :
    (x.subInt ops a).val = x.val-a.val := by
  cases x with
  | bit t y =>
    simp only [IntegerValue.val] at hb
    simp only [IntegerValue.subInt,IntegerValue.val]
    rw [JuliaLean.Proofs.base.range.binop_val_sub JuliaLean.base.int.sub
      (fun a b => JuliaLean.Proofs.base.int.sub_int_val a b)]
    obtain ⟨hmin,hmax⟩ := promote_ri64_range t
    exact wrapInt_of_inRange _ _ ⟨by omega,by omega⟩
  | bool b =>
    simp only [IntegerValue.val] at hb
    simp only [IntegerValue.subInt,IntegerValue.val,JuliaLean.base.int.sub,
      JuliaLean.Proofs.base.int.sub_int_val,bool64_val]
    exact wrapInt_of_inRange _ _ ⟨by change -9223372036854775808 ≤ _; omega,by exact hb.2⟩
  | big v => simp only [IntegerValue.subInt,IntegerValue.val,hops.2.2.1]

theorem leInteger_val (ops : BigIntegerOps) (hops : ops.Lawful) (x : IntegerValue) (a : I) :
    x.leInt ops a = decide (x.val ≤ a.val) := by
  cases x <;> simp only [IntegerValue.leInt,IntegerValue.val,
    JuliaLean.Proofs.base.int.le_eq,bool64_val,hops.2.2.2.2]
  all_goals
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hp
      exact decide_eq_true (of_decide_eq_true hp)
    · intro hp
      exact decide_eq_true (of_decide_eq_true hp)

theorem integerToInt_of_val (ops : BigIntegerOps) (hops : ops.Lawful) (x : IntegerValue)
    (a : I) (hx : x.val = a.val) : (integerToInt ops x : MutationM α I) = pure a := by
  have hb : IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max := by rw [hx]; exact a.property
  have ht : x.toInt ops = .ok a := by
    rw [integerValue_toInt hops,if_pos hb]
    apply congrArg Except.ok
    apply Subtype.ext
    rw [ival_wrap _ hb,hx]
  unfold integerToInt
  rw [ht]
  rfl

theorem windowDelete_valid_eq (layout : MemoryLayoutMetadata) (ops : BigIntegerOps)
    (hops : ops.Lawful) (s : MutableMemory α) (a mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s a mem off n slots) (i delta : IntegerValue)
    (hnsmall : n.val < 2^62) (hi : 1 ≤ i.val) (hin : i.val ≤ n.val)
    (hd : 0 ≤ delta.val) (hcount : delta.val ≤ n.val+1-i.val) :
    (windowDelete α (layout := layout) ops a i delta).run s =
      (vecDeleteat α (layout := layout) a (JInt.wrap .i64 i.val) (JInt.wrap .i64 delta.val)).run s := by
  have hn := h.2.2.2.1
  have hbI : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := by
    change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807
    omega
  have hbD : IntTy.i64.min ≤ delta.val ∧ delta.val ≤ IntTy.i64.max := by
    change -9223372036854775808 ≤ delta.val ∧ delta.val ≤ 9223372036854775807
    omega
  let wi := JInt.wrap .i64 i.val
  let wd := JInt.wrap .i64 delta.val
  have hiv : wi.val = i.val := ival_wrap _ hbI
  have hdv : wd.val = delta.val := ival_wrap _ hbD
  have hirange : one ≤ wi ∧ wi ≤ n := by
    rw [jle_iff,jle_iff,ival_one,hiv]
    exact ⟨hi,hin⟩
  have hlimit : (n+one-wi).val = n.val+1-i.val := by
    rw [ival_add_sub n one wi (by rw [ival_one,hiv]; omega),ival_one,hiv]
  have hcnt : delta.val ≤ (n+one-wi).val := by rw [hlimit]; exact hcount
  have hdn : 0 ≤ wd.val := by rw [hdv]; exact hd
  have hcntN : wd.val ≤ (n+one-wi).val := by rw [hdv]; exact hcnt
  have hic : (integerToInt ops i : MutationM α I) = pure wi := integerToInt_of_val ops hops i wi hiv.symm
  have hdc : (integerToInt ops delta : MutationM α I) = pure wd := integerToInt_of_val ops hops delta wd hdv.symm
  have hn1 : (n+one).val = n.val+1 := ival_add_one n (by omega)
  have h2i : (JInt.wrap .i64 2*wi).val = 2*i.val := by
    rw [ival_two_mul wi (by rw [hiv]; omega) (by rw [hiv]; omega),hiv]
  have hsum : (JInt.wrap .i64 2*wi+wd).val = 2*i.val+delta.val := by
    rw [ival_add _ _ (by rw [h2i,hdv]; omega),h2i,hdv]
  have h1d : (one+wd).val = 1+delta.val := by
    rw [ival_add _ _ (by rw [ival_one,hdv]; omega),ival_one,hdv]
  have hid : (wi+wd).val = i.val+delta.val := by
    rw [ival_add _ _ (by rw [hiv,hdv]; omega),hiv,hdv]
  have hnd : (n+one-wd).val = n.val+1-delta.val := by
    rw [ival_sub _ _ (by rw [hn1,hdv]; omega),hn1,hdv]
  have hk : (n+one-wd-wi).val = n.val+1-delta.val-i.val := by
    rw [ival_sub _ _ (by rw [hnd,hiv]; omega),hnd,hiv]
  have hc1 : (integerToInt ops (delta.addInt ops one) : MutationM α I) = pure (one+wd) := by
    apply integerToInt_of_val ops hops
    rw [addInteger_val ops hops one delta (by rw [ival_one]; omega),ival_one,h1d]
  have hc2 : (integerToInt ops (delta.addInt ops wi) : MutationM α I) = pure (wi+wd) := by
    apply integerToInt_of_val ops hops
    rw [addInteger_val ops hops wi delta (by rw [hiv]; omega),hiv,hid]
  have hm : (delta.subFromInt ops (n+one)).val = n.val+1-delta.val := by
    rw [subFromInteger_val ops hops (n+one) delta (by rw [hn1]; omega),hn1]
  have hc3 : (integerToInt ops ((delta.subFromInt ops (n+one)).subInt ops wi) : MutationM α I) =
      pure (n+one-wd-wi) := by
    apply integerToInt_of_val ops hops
    rw [subInteger_val ops hops _ wi (by rw [hm,hiv]; omega),hm,hiv,hk]
  have hle : (delta.addInt ops (JInt.wrap .i64 2*wi)).leInt ops n =
      decide (JInt.wrap .i64 2*wi+wd ≤ n) := by
    rw [leInteger_val ops hops]
    have heq : (delta.addInt ops (JInt.wrap .i64 2*wi)).val =
        (JInt.wrap .i64 2*wi+wd).val := by
      rw [addInteger_val ops hops _ delta (by rw [h2i]; omega),h2i,hsum]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hp
      apply decide_eq_true
      have hh := of_decide_eq_true hp
      change (JInt.wrap .i64 2*wi+wd).val ≤ n.val
      rw [← heq]
      exact hh
    · intro hp
      apply decide_eq_true
      have hh := of_decide_eq_true hp
      change (JInt.wrap .i64 2*wi+wd).val ≤ n.val at hh
      rw [heq]
      exact hh
  have hbeg : deletebeg (mutableStorage (α := α) layout) (integerToInt ops) a delta =
      deletebeg (mutableStorage (α := α) layout) pure a wd := by
    simp only [deletebeg,hdc,pure_bind]
  have hend : deleteend (mutableStorage (α := α) layout) (integerToInt ops) a delta =
      deleteend (mutableStorage (α := α) layout) pure a wd := by
    simp only [deleteend,hdc,pure_bind]
  change (windowDelete α (layout := layout) ops a i delta).run s =
    (vecDeleteat α (layout := layout) a wi wd).run s
  simp only [windowDelete,vecDeleteat,deleteatWindow,hic,stateExcept_bind,stateExcept_pure,
    mutableLength_run s a _ h.1,hbeg,hend,hle,hc1,hc2,hc3,pure_bind,
    hd,hdn,hirange,and_self,hcnt,hcntN,decide_true,Bool.not_true,Bool.false_eq_true,ite_false]

theorem deleteatWindowSpec : round4.DeleteatWindowSpec := by
  intro α layout ops hops s a i delta hvalid
  dsimp only
  intro hsmall
  refine ⟨deleteatWindow_index_inexact α ops hops s a i delta,
    deleteatWindow_negative α ops hops s a i delta hvalid, ?_, ?_⟩
  · intro hfit hd hbad
    rcases hbad with hlo | hhi | hcount
    · exact deleteatWindow_index_bounds α ops hops s a i delta hvalid hfit hd (Or.inl hlo)
    · exact deleteatWindow_index_bounds α ops hops s a i delta hvalid hfit hd (Or.inr hhi)
    · by_cases hout : i.val < 1 ∨ (s.contents a).length < i.val
      · exact deleteatWindow_index_bounds α ops hops s a i delta hvalid hfit hd hout
      · exact deleteatWindow_count_bounds α ops hops s a i delta hvalid hsmall hfit hd
          (by omega) (by omega) hcount
  · intro hd hi hin hcount
    obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
    have hn := h.2.2.2.1
    have hlen : ((s.contents a).length : Int) = n.val := by
      rw [h.contents,vwWindow_length h]
      omega
    have hnsmall : n.val < 2^62 := by rw [← hlen]; exact hsmall
    have hbI : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := by
      change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807
      omega
    have hbD : IntTy.i64.min ≤ delta.val ∧ delta.val ≤ IntTy.i64.max := by
      change -9223372036854775808 ≤ delta.val ∧ delta.val ≤ 9223372036854775807
      omega
    have hiv := ival_wrap i.val hbI
    have hdv := ival_wrap delta.val hbD
    obtain ⟨after,hr,hv,hcontents,hframe,_,_⟩ := vwDeleteat_run (layout := layout) s a mem off n slots h
      (JInt.wrap .i64 i.val) (JInt.wrap .i64 delta.val) hnsmall
      (by rw [hiv]; exact hi) (by rw [hiv,← hlen]; exact hin)
      (by rw [hdv]; exact hd) (by rw [hdv,hiv,← hlen]; exact hcount)
    refine ⟨after,?_,hv,?_,hframe⟩
    · rw [windowDelete_valid_eq layout ops hops s a mem off n slots h i delta hnsmall hi
        (by rw [← hlen]; exact hin) hd (by rw [← hlen]; exact hcount)]
      exact hr
    · rw [hcontents,hiv,hdv,← h.contents]
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

theorem spliceIndex_many {m : Type → Type} [Monad m] [LawfulMonad m]
    [ForIn m Ins β] (get : A → Z → m α) (length : Ins → I)
    (deleteat grow : A → Z → I → m Unit) (only : Ins → m β)
    (set : A → β → Z → m Unit) (add : Z → I → Z) (sub : Z → Z)
    (a : A) (i : Z) (ins : Ins) (n : I)
    (hlen : length ins = n) (h0 : n ≠ zero) (h1 : n ≠ one) :
    spliceIndex get length deleteat grow only set add sub a i ins =
      (do let value ← get a i
          grow a i (n-one)
          let _ ← forIn ins one (fun x k => do
            set a x (sub (add i k))
            pure (ForInStep.yield (k+one)))
          pure value) := by
  simp only [spliceIndex,hlen,h0,h1,ite_false]

theorem spliceIndex_many_eq (layout : MemoryLayoutMetadata) (already : α → Bool)
    (convert : α → Except Error α) (a : Nat) (i : I) (ins : List α) (n : I)
    (hlen : JInt.wrap .i64 (ins.length : Int) = n) (h0 : n ≠ zero) (h1 : n ≠ one) :
    mutableSpliceIndex layout already convert a i ins =
      (do let value ← mutableGet a i
          growat (mutableStorage layout) pure pure
            (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
            (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i (n-one)
          let _ ← forIn ins one (fun x k => do
            let _ ← setindexScalar already id (fun v => stateExceptLift (convert v)) mutableTypedSet
              a x (i+k-one)
            pure (ForInStep.yield (k+one)))
          pure value) := by
  unfold mutableSpliceIndex
  rw [spliceIndex_many (m := MutationM α) (Ins := List α) (ins := ins) (n := n)
    (length := fun xs : List α => JInt.wrap .i64 (xs.length : Int))
    (hlen := hlen) (h0 := h0) (h1 := h1)]
  simp only [bind_assoc,pure_bind]

theorem stateExcept_bind_error_first (action : MutationM α β) (next : β → MutationM α γ)
    (s : MutableMemory α) (e : Error) (h : (action.run s).1 = .error e) :
    ((action >>= next).run s).1 = .error e := by
  simp only [stateExcept_bind]
  cases hh : action.run s with
  | mk value state =>
    cases value with
    | error err =>
      have he : err = e := Except.error.inj (by simpa only [hh] using h)
      cases he
      rfl
    | ok value =>
      have he : (Except.ok value : Except Error β) = .error e := by simpa only [hh] using h
      cases he

theorem splice_growth_counts (length : Nat) (d i : Int) (hMany : 2 ≤ length)
    (hd : d = (length : Int)-1) (hi : 1 ≤ i) :
    0 ≤ d ∧ d.toNat = length-1 ∧
      (i-1+d).toNat+1 = (i-1+(length : Int)).toNat ∧ (i-1).toNat+1 = i.toNat := by
  omega

theorem spliceIndex_many_result (l : DictLayout) (already : α → Bool)
    (convert : α → Except Error α) (s : MutableMemory α) (a mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s a mem off n slots) (i : I) (ins : List α)
    (hMany : 2 ≤ ins.length) (hMax : ins.length ≤ typemaxNat) (value : α)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val)
    (hslot : (vwWindow slots off n)[(i.val-1).toNat]? = some (some value)) :
    (∀ e, growatPlan l (geometryOf s a) i.val (ins.length-1) = .error e →
      (mutableSpliceIndex (MemoryLayoutMetadata.ofRuntime l) already convert a i ins).run s = (.error e,s)) ∧
    (∀ g, growatPlan l (geometryOf s a) i.val (ins.length-1) = .ok g →
      (∀ cs, ins.mapM (storedValue already convert) = .ok cs →
        ∃ next, (mutableSpliceIndex (MemoryLayoutMetadata.ofRuntime l) already convert a i ins).run s = (.ok value,next) ∧
          next.validVector a ∧ next.contents a =
            (s.contents a).take (i.val-1).toNat ++ cs.map some ++ (s.contents a).drop i.val.toNat) ∧
      (∀ e, ins.mapM (storedValue already convert) = .error e →
        ((mutableSpliceIndex (MemoryLayoutMetadata.ofRuntime l) already convert a i ins).run s).1 = .error e)) := by
  let m : I := JInt.wrap .i64 (ins.length : Int)
  have hM : m.val = (ins.length : Int) := ival_wrap _ (by
    have hm : typemaxNat = 9223372036854775807 := by decide
    rw [hm] at hMax
    omega)
  have hm0 : m ≠ zero := by
    intro he
    have he' := congrArg Subtype.val he
    rw [hM,ival_zero] at he'
    omega
  have hm1 : m ≠ one := by
    intro he
    have he' := congrArg Subtype.val he
    rw [hM,ival_one] at he'
    omega
  let d : I := m-one
  have hDv : d.val = (ins.length : Int)-1 := by
    dsimp only [d]
    rw [ival_sub_one m (by rw [hM]; omega),hM]
  obtain ⟨hd,hDn,hNextDrop,hOldDrop⟩ := splice_growth_counts ins.length d.val i.val hMany hDv hi.1
  have hget := vwGet_run s a mem off n slots h i hi
  rw [hslot] at hget
  have hEq := spliceIndex_many_eq (MemoryLayoutMetadata.ofRuntime l) already convert a i ins m rfl hm0 hm1
  have H := growat_plan_native l s a mem off n slots h i d hd
  rw [hDn] at H
  refine ⟨fun error he => ?_,fun g hg => ?_⟩
  · have hGrow := H.1 error he
    dsimp only [d] at hGrow
    rw [hEq]
    simp only [stateExcept_bind,hget,hGrow]
  · obtain ⟨result,grown,hGrow,hValid,hLen,hPre,hSuf,_⟩ := H.2 g hg
    cases result
    dsimp only [d] at hGrow
    obtain ⟨memG,offG,nG,slotsG,hG⟩ := validVector_vecAt hValid
    have hcap : i.val-1+(0 : Nat)+(ins.length : Int) ≤ nG.val := by
      rw [vecAt_length_int hG,vecAt_length_int h,hDv] at hLen
      have := hi.2
      omega
    have hSuffix : (grown.contents a).drop (i.val-1+(ins.length : Int)).toNat =
        (s.contents a).drop i.val.toNat := by
      have hh := congrArg (fun xs : List (Option α) => xs.drop 1) hSuf
      simp only [List.drop_drop] at hh
      rw [hNextDrop,hOldDrop] at hh
      exact hh
    refine ⟨fun cs hmap => ?_,fun error hmap => ?_⟩
    · have hCS := converted_length (storedValue already convert) ins cs hmap
      obtain ⟨finalK,after,hStore,hValidAfter,hContents,_,_⟩ := spliceStores_run (MemoryLayoutMetadata.ofRuntime l) (storedValue already convert)
        a memG offG nG i hi.1 ins cs grown slotsG 0 one hG hcap
        (fun _ => by simpa only [Int.natCast_zero,Int.zero_add] using ival_one) hmap
      simp only [Int.natCast_zero,Int.add_zero,hCS] at hContents
      refine ⟨after,?_,hValidAfter,?_⟩
      · rw [hEq]
        simp only [stateExcept_bind,hget,hGrow,convertingStep_eq,hStore,stateExcept_pure]
      · rw [hContents,hPre,hSuffix]
    · let loop : MutationM α I := forIn ins one (fun x k => do
        let _ ← setindexScalar already id (fun v => stateExceptLift (convert v)) mutableTypedSet
          a x (i+k-one)
        pure (ForInStep.yield (k+one)))
      have hLoop : (loop.run grown).1 = .error error := by
        simpa only [loop,convertingStep_eq] using spliceStores_error (storedValue already convert) a memG offG nG i
          hi.1 ins grown slotsG 0 one error hG hcap
          (fun _ => by simpa only [Int.natCast_zero,Int.zero_add] using ival_one) hmap
      have hBind := stateExcept_bind_error_first loop (fun _ => pure value) grown error hLoop
      rw [hEq]
      simp only [stateExcept_bind,hget,hGrow,stateExcept_pure]
      simpa only [loop,stateExcept_bind,stateExcept_pure] using hBind

theorem mapM_singleton_ok (f : α → Except Error β) (x : α) (ys : List β)
    (h : [x].mapM f = .ok ys) : ∃ y, f x = .ok y ∧ ys = [y] := by
  cases hc : f x with
  | error error =>
    simp only [List.mapM_cons,hc,Bind.bind,Except.bind] at h
    all_goals cases h
  | ok y =>
    refine ⟨y,rfl,?_⟩
    have hy : [y] = ys := by
      simpa only [List.mapM_cons,hc,List.mapM_nil,Bind.bind,Except.bind,Pure.pure,Except.pure,
        Except.ok.injEq] using h
    exact hy.symm

theorem mapM_singleton_error (f : α → Except Error β) (x : α) (error : Error)
    (h : [x].mapM f = .error error) : f x = .error error := by
  cases hc : f x with
  | error err =>
    have he : err = error := Except.error.inj (by
      simpa only [List.mapM_cons,hc,List.mapM_nil,Bind.bind,Except.bind,Pure.pure,Except.pure] using h)
    cases he
    rfl
  | ok y =>
    simp only [List.mapM_cons,hc,List.mapM_nil,Bind.bind,Except.bind,Pure.pure,Except.pure] at h
    all_goals cases h

theorem spliceIndexSpec : SpliceIndexSpec := by
  intro α l s a i ins already convert hvalid hMax
  dsimp only
  obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
  have hOldInt := vecAt_length_int h
  refine ⟨?_,?_,?_⟩
  · intro hout
    apply spliceIndex_outside l s a i ins already convert hvalid
    omega
  · exact spliceIndex_undefined l s a i ins already convert hvalid
  · intro value hi1 hin hslot
    have hi : 1 ≤ i.val ∧ i.val ≤ n.val := ⟨hi1,by rw [← hOldInt]; exact hin⟩
    have hslotW : (vwWindow slots off n)[(i.val-1).toNat]? = some (some value) := by
      rw [← h.contents]
      exact hslot
    have hDrop : (i.val-1).toNat+1 = i.val.toNat := by omega
    cases ins with
    | nil =>
      simp only [List.length_nil,show ¬ (2 : Nat) ≤ 0 by decide,ite_false]
      refine ⟨(by intro e he; cases he),fun g hg => ?_⟩
      refine ⟨fun cs hmap => ?_,fun error hmap => ?_⟩
      · have hcs : cs = [] := by simpa only [List.mapM_nil,Pure.pure,Except.pure,Except.ok.injEq] using hmap.symm
        subst cs
        obtain ⟨after,hr,hv,hContents⟩ := spliceIndex_empty (MemoryLayoutMetadata.ofRuntime l) already convert s a mem off n slots h i value hi hslotW
        refine ⟨after,hr,hv,?_⟩
        simpa only [List.map_nil,List.append_nil,List.nil_append,List.eraseIdx_eq_take_drop_succ,hDrop] using hContents
      · simp only [List.mapM_nil,Pure.pure,Except.pure] at hmap
        all_goals cases hmap
    | cons x tail =>
      cases tail with
      | nil =>
        simp only [List.length_cons,List.length_nil,show ¬ (2 : Nat) ≤ 0+1 by decide,ite_false]
        have H := spliceIndex_single (MemoryLayoutMetadata.ofRuntime l) already convert s a mem off n slots h i x value hi hslotW
        refine ⟨(by intro e he; cases he),fun g hg => ?_⟩
        refine ⟨fun cs hmap => ?_,fun error hmap => ?_⟩
        · obtain ⟨replacement,hc,hcs⟩ := mapM_singleton_ok (storedValue already convert) x cs hmap
          subst cs
          obtain ⟨after,hr,hv,hContents⟩ := H.1 replacement hc
          refine ⟨after,hr,hv,?_⟩
          have hp : (i.val-1).toNat < (s.contents a).length := by omega
          rw [hContents,list_set_splice _ _ _ hp,hDrop]
          rfl
        · have hc := mapM_singleton_error (storedValue already convert) x error hmap
          have hr := H.2 error hc
          exact congrArg Prod.fst hr
      | cons y rest =>
        have hMany : 2 ≤ (x::y::rest).length := by simp only [List.length_cons]; omega
        simp only [hMany,ite_true]
        exact spliceIndex_many_result l already convert s a mem off n slots h i (x::y::rest) hMany hMax value hi hslotW
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

abbrev typedWindowRemove (α : Type) (layout : MemoryLayoutMetadata) (κ ρ : IntTy)
    (a : Nat) (i : JInt t) (d : JInt κ) : MutationM α Unit :=
  deleteatWindow (fun i : JInt t => liftM (indexConvert i)) mutableLength
    (fun d : JInt κ => d.val)
    (fun a d => JInt.wrap ρ (a.val+d.val)) (fun a d => JInt.wrap ρ (a.val-d.val))
    (fun a b => decide (a.val ≤ b.val)) (fun a i => JInt.wrap ρ (a.val-i.val))
    (fun a d b s n => do mutableCopy a (← liftM (indexConvert d)) b s n)
    (fun a d b s n => do mutableCopy a d b (← liftM (indexConvert s)) (← liftM (indexConvert n)))
    (deletebeg (mutableStorage layout) (fun d => liftM (indexConvert d)))
    (deleteend (mutableStorage layout) (fun d => liftM (indexConvert d))) a i d

theorem generic_wrap_val (t : IntTy) (z : Int) (h : t.min ≤ z ∧ z ≤ t.max) :
    (JInt.wrap t z).val = z := by
  unfold JInt.wrap
  exact wrapInt_of_inRange t z h

theorem indexConvert_of_val {t : IntTy} (x : JInt t) (i : I) (h : x.val = i.val) :
    indexConvert x = .ok i := by
  have hx : IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max := by rw [h]; exact i.property
  unfold indexConvert
  rw [JInt.convert,dif_pos hx]
  change Except.ok (⟨x.val,hx⟩ : I) = Except.ok i
  apply congrArg Except.ok
  exact Subtype.ext h

theorem lift_index_of_val {α : Type} {t : IntTy} (x : JInt t) (i : I) (h : x.val = i.val) :
    (liftM (indexConvert x) : MutationM α I) = pure i := by
  rw [indexConvert_of_val x i h]
  rfl

theorem deletebeg_convert_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadExceptOf Error m]
    (st : Storage m A Mem R) (toInt : D → m I) (a : A) (d : D) :
    deletebeg st toInt a d = (do let delta ← toInt d; deletebeg st pure a delta) := by
  simp only [deletebeg,pure_bind]

theorem deleteend_convert_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadExceptOf Error m]
    (st : Storage m A Mem R) (toInt : D → m I) (a : A) (d : D) :
    deleteend st toInt a d = (do let delta ← toInt d; deleteend st pure a delta) := by
  simp only [deleteend,pure_bind]

theorem typedWindowRemove_native {t : IntTy} (layout : MemoryLayoutMetadata) (κ ρ : IntTy)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (i : JInt t) (d : JInt κ) (wi wd : I)
    (hiVal : i.val = wi.val) (hdVal : d.val = wd.val)
    (hnSmall : n.val < 2^62) (hi1 : 1 ≤ wi.val) (hin : wi.val ≤ n.val)
    (hd : 0 ≤ wd.val) (hcount : wd.val ≤ n.val+1-wi.val)
    (hρmin : ρ.min ≤ 0) (hρmax : 9223372036854775807 ≤ ρ.max) :
    (typedWindowRemove α layout κ ρ a i d).run s = (vecDeleteat α (layout := layout) a wi wd).run s := by
  have hn0 := h.2.2.2.1
  have hnB := ival_bounds n
  have hiB := ival_bounds wi
  have hdB := ival_bounds wd
  have hR : ∀ z : Int, 0 ≤ z → z ≤ 9223372036854775807 → ρ.min ≤ z ∧ z ≤ ρ.max := by
    intro z hz hm
    exact ⟨Int.le_trans hρmin hz,Int.le_trans hm hρmax⟩
  have hIConv := lift_index_of_val (α := α) i wi hiVal
  have hDConv := lift_index_of_val (α := α) d wd hdVal
  have hn1 : (n+one).val = n.val+1 := ival_add_one n (by omega)
  have hrem : (n+one-wi).val = n.val+1-wi.val := by
    rw [ival_sub (n+one) wi (by rw [hn1]; omega),hn1]
  have htwo : (JInt.wrap .i64 2 * wi).val = 2*wi.val := ival_two_mul wi (by omega) (by omega)
  have htestNative : (JInt.wrap .i64 2 * wi+wd).val = 2*wi.val+wd.val := by
    rw [ival_add _ _ (by rw [htwo]; omega),htwo]
  have htestR : (JInt.wrap ρ ((JInt.wrap .i64 2 * wi).val+d.val)).val = 2*wi.val+wd.val := by
    rw [htwo,hdVal]
    exact generic_wrap_val ρ _ (hR _ (by omega) (by omega))
  have htest : decide ((JInt.wrap ρ ((JInt.wrap .i64 2 * wi).val+d.val)).val ≤ n.val) =
      decide (JInt.wrap .i64 2 * wi+wd ≤ n) := by
    simp only [htestR,jle_iff,htestNative]
  have hp1 : (one+wd).val = 1+wd.val := by
    rw [ival_add one wd (by rw [ival_one]; omega),ival_one]
  have hpI : (wi+wd).val = wi.val+wd.val := ival_add _ _ (by omega)
  have hmN : (n+one-wd).val = n.val+1-wd.val := by
    rw [ival_sub (n+one) wd (by rw [hn1]; omega),hn1]
  have hmI : (n+one-wd-wi).val = n.val+1-wd.val-wi.val := by
    rw [ival_sub (n+one-wd) wi (by rw [hmN]; omega),hmN]
  have hmR : (JInt.wrap ρ ((n+one).val-d.val)).val = n.val+1-wd.val := by
    rw [hn1,hdVal]
    exact generic_wrap_val ρ _ (hR _ (by omega) (by omega))
  have hp1R : (JInt.wrap ρ (one.val+d.val)).val = (one+wd).val := by
    rw [ival_one,hdVal,hp1]
    exact generic_wrap_val ρ _ (hR _ (by omega) (by omega))
  have hpIR : (JInt.wrap ρ (wi.val+d.val)).val = (wi+wd).val := by
    rw [hdVal,hpI]
    exact generic_wrap_val ρ _ (hR _ (by omega) (by omega))
  have hmIR : (JInt.wrap ρ ((JInt.wrap ρ ((n+one).val-d.val)).val-wi.val)).val = (n+one-wd-wi).val := by
    rw [hmR,hmI]
    exact generic_wrap_val ρ _ (hR _ (by omega) (by omega))
  have hCP := lift_index_of_val (α := α) (JInt.wrap ρ (one.val+d.val)) (one+wd) hp1R
  have hCS := lift_index_of_val (α := α) (JInt.wrap ρ (wi.val+d.val)) (wi+wd) hpIR
  have hCN := lift_index_of_val (α := α)
    (JInt.wrap ρ ((JInt.wrap ρ ((n+one).val-d.val)).val-wi.val)) (n+one-wd-wi) hmIR
  have hBeg : deletebeg (mutableStorage (α := α) layout) (fun d : JInt κ => liftM (indexConvert d)) a d =
      deletebeg (mutableStorage layout) pure a wd := by
    rw [deletebeg_convert_eq]
    simp only [hDConv,pure_bind]
  have hEnd : deleteend (mutableStorage (α := α) layout) (fun d : JInt κ => liftM (indexConvert d)) a d =
      deleteend (mutableStorage layout) pure a wd := by
    rw [deleteend_convert_eq]
    simp only [hDConv,pure_bind]
  have hD0 : 0 ≤ d.val := by rw [hdVal]; exact hd
  have hRange : one ≤ wi ∧ wi ≤ n := by simpa only [jle_iff,ival_one] using (And.intro hi1 hin)
  have hCount : d.val ≤ (n+one-wi).val := by rw [hdVal,hrem]; exact hcount
  have hCountN : wd.val ≤ (n+one-wi).val := by rw [hrem]; exact hcount
  simp only [typedWindowRemove,vecDeleteat,deleteatWindow,hIConv,pure_bind,stateExcept_bind,stateExcept_pure,
    mutableLength_run s a _ h.1,hD0,hd,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,
    hRange,and_self,hCount,hCountN,htest,hCP,hCS,hCN,hBeg,hEnd]

theorem typedWindowRemove_error {t : IntTy} (layout : MemoryLayoutMetadata) (κ ρ : IntTy)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (i : JInt t) (d : JInt κ) (wi : I)
    (hiVal : i.val = wi.val) (hd : 0 ≤ d.val) (hnSmall : n.val < 2^62)
    (hout : wi.val < 1 ∨ n.val < wi.val ∨ n.val+1-wi.val < d.val) :
    (typedWindowRemove α layout κ ρ a i d).run s = (.error .bounds,s) := by
  have hn0 := h.2.2.2.1
  have hnB := ival_bounds n
  have hiB := ival_bounds wi
  have hIConv := lift_index_of_val (α := α) i wi hiVal
  by_cases hindex : one ≤ wi ∧ wi ≤ n
  · have hidx : 1 ≤ wi.val ∧ wi.val ≤ n.val := by simpa only [jle_iff,ival_one] using hindex
    have hn1 : (n+one).val = n.val+1 := ival_add_one n (by omega)
    have hrem : (n+one-wi).val = n.val+1-wi.val := by
      rw [ival_sub (n+one) wi (by rw [hn1]; omega),hn1]
    have hCount : ¬ d.val ≤ (n+one-wi).val := by rw [hrem]; omega
    simp only [typedWindowRemove,deleteatWindow,hIConv,pure_bind,stateExcept_bind,stateExcept_pure,
      mutableLength_run s a _ h.1,hd,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,
      hindex,and_self,hCount,decide_false,Bool.not_false,ite_true,stateExcept_throw]
  · simp only [typedWindowRemove,deleteatWindow,hIConv,pure_bind,stateExcept_bind,stateExcept_pure,
      mutableLength_run s a _ h.1,hd,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,
      hindex,decide_false,Bool.not_false,ite_true,stateExcept_throw]

theorem deletion_count_types (t : IntTy) :
    let κ := if t.bits < 64 then IntTy.i64 else t
    let ρ := IntTy.promote .i64 κ
    κ.min ≤ 0 ∧ 9223372036854775807 ≤ κ.max ∧ ρ.min ≤ 0 ∧ 9223372036854775807 ≤ ρ.max := by
  cases t <;> decide

theorem deleteatRangeInboundsSpec : DeleteatRangeInboundsSpec := by
  intro α layout t xs lo hi initial hvalid hxs hSmall hOrder hLoMin hHiMax
  dsimp only
  let κ := if t.bits < 64 then IntTy.i64 else t
  let ρ := IntTy.promote .i64 κ
  let operation : MutationM α Nat := deleteatRange
    (fun _ => false) (fun a _ => pure a) Prod.fst (fun _ => false)
    (fun _ _ => pure ()) (fun r : JInt t × JInt t => decide (r.1.val > r.2.val))
    (fun r => JInt.wrap κ (if r.1.val > r.2.val then 0 else r.2.val-r.1.val+1))
    (typedWindowRemove α layout κ ρ) 0 (lo,hi)
  change (lo.val > hi.val → ((operation.run initial).1,(operation.run initial).2.contents 0) = (.ok 0,xs.map some)) ∧
    (1 ≤ lo.val → lo.val ≤ hi.val → hi.val ≤ (xs.length : Int) →
      ((operation.run initial).1,(operation.run initial).2.contents 0) =
        (.ok 0,(xs.take (lo.val-1).toNat ++ xs.drop hi.val.toNat).map some)) ∧
    (lo.val ≤ hi.val → ¬ (1 ≤ lo.val ∧ hi.val ≤ (xs.length : Int)) →
      hi.val-lo.val+1 ≤ κ.max →
      ((operation.run initial).1,(operation.run initial).2.contents 0) = (.error .bounds,xs.map some))
  obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
  have hLen : (xs.length : Int) = n.val := by
    have hh := vecAt_length_int h
    rw [hxs,List.length_map] at hh
    exact hh
  have hnSmall : n.val < 2^62 := by omega
  have hn0 := h.2.2.2.1
  obtain ⟨hκmin,hκmax,hρmin,hρmax⟩ := deletion_count_types t
  refine ⟨fun hEmpty => ?_,fun hlo hle hhi => ?_,fun hle hbad hCountMax => ?_⟩
  · simp only [operation,deleteatRange,Bool.false_eq_true,ite_false,hEmpty,decide_true,
      Bool.not_true,stateExcept_bind,stateExcept_pure,pure_bind,hxs]
  · have hNonempty : ¬ lo.val > hi.val := by omega
    let c := hi.val-lo.val+1
    have hc0 : 0 ≤ c := by dsimp only [c]; omega
    have hcBound : c ≤ n.val+1-lo.val := by dsimp only [c]; omega
    have hLoFits : IntTy.i64.min ≤ lo.val ∧ lo.val ≤ IntTy.i64.max := ⟨hLoMin,by omega⟩
    have hcFits : IntTy.i64.min ≤ c ∧ c ≤ IntTy.i64.max := by
      change -9223372036854775808 ≤ c ∧ c ≤ 9223372036854775807
      omega
    let wi : I := JInt.wrap .i64 lo.val
    let wd : I := JInt.wrap .i64 c
    let dT : JInt κ := JInt.wrap κ c
    have hWI : wi.val = lo.val := ival_wrap _ hLoFits
    have hWD : wd.val = c := ival_wrap _ hcFits
    have hDT : dT.val = c := generic_wrap_val κ c ⟨Int.le_trans hκmin hc0,Int.le_trans (by omega) hκmax⟩
    have hBound : wd.val ≤ n.val+1-wi.val := by rw [hWI,hWD]; exact hcBound
    have hi1 : 1 ≤ wi.val := by rw [hWI]; exact hlo
    have hin : wi.val ≤ n.val := by rw [hWI]; omega
    have hd0 : 0 ≤ wd.val := by rw [hWD]; exact hc0
    obtain ⟨next,hr,hv,hContents,_⟩ := vwDeleteat_run (layout := layout) initial 0 mem off n slots h wi wd
      hnSmall hi1 hin hd0 hBound
    have hSource := (typedWindowRemove_native layout κ ρ initial 0 mem off n slots h lo dT wi wd
      hWI.symm (hDT.trans hWD.symm) hnSmall hi1 hin hd0 hBound hρmin hρmax).trans hr
    dsimp only [dT,c] at hSource
    have hDrop : (wi.val-1+wd.val).toNat = hi.val.toNat := by
      rw [hWI,hWD]
      dsimp only [c]
      congr 1
      omega
    rw [← h.contents,hDrop,hWI,hxs] at hContents
    have hFinalContents : next.contents 0 = (xs.take (lo.val-1).toNat ++ xs.drop hi.val.toNat).map some := by
      simpa using hContents
    have hOp : operation.run initial = (.ok 0,next) := by
      simp only [operation,deleteatRange,Bool.false_eq_true,ite_false,hNonempty,decide_false,
        Bool.not_false,ite_true,stateExcept_bind,stateExcept_pure,pure_bind,hSource]
    rw [hOp,hFinalContents]
  · have hNonempty : ¬ lo.val > hi.val := by omega
    let c := hi.val-lo.val+1
    have hc0 : 0 ≤ c := by dsimp only [c]; omega
    have hLoFits : IntTy.i64.min ≤ lo.val ∧ lo.val ≤ IntTy.i64.max := ⟨hLoMin,Int.le_trans hle hHiMax⟩
    let wi : I := JInt.wrap .i64 lo.val
    let dT : JInt κ := JInt.wrap κ c
    have hWI : wi.val = lo.val := ival_wrap _ hLoFits
    have hDT : dT.val = c := generic_wrap_val κ c ⟨Int.le_trans hκmin hc0,hCountMax⟩
    have hOut : wi.val < 1 ∨ n.val < wi.val ∨ n.val+1-wi.val < dT.val := by
      rw [hWI,hDT]
      dsimp only [c]
      omega
    have hSource := typedWindowRemove_error layout κ ρ initial 0 mem off n slots h lo dT wi
      hWI.symm (by rw [hDT]; exact hc0) hnSmall hOut
    dsimp only [dT,c] at hSource
    have hOp : operation.run initial = (.error .bounds,initial) := by
      simp only [operation,deleteatRange,Bool.false_eq_true,ite_false,hNonempty,decide_false,
        Bool.not_false,ite_true,stateExcept_bind,stateExcept_pure,pure_bind,hSource]
    rw [hOp,hxs]
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

/-- The left-to-right filter specification, including errors before later elements. -/
def batch1_keepSlots (f : α → Except Error (Option Bool)) :
    List (Option α) → Except Error (List α)
  | [] => .ok []
  | none :: _ => .error .undefinedReference
  | some x :: xs =>
      match boolResult f x with
      | .error e => .error e
      | .ok b =>
          match batch1_keepSlots f xs with
          | .error e => .error e
          | .ok ys => .ok (if b then x :: ys else ys)

/-- One iteration of the source filter loop. It writes before testing the predicate. -/
def batch1_filterStep (f : α → Except Error (Option Bool)) (handle : Nat)
    (o : Option α) (j : I) : VectorM α (ForInStep I) :=
  match o with
  | none => throw .undefinedReference
  | some x => do
      heapSet handle x j
      let b ← liftM (boolResult f x)
      pure (.yield (if b then j + one else j))

/-- Loop invariant: the kept prefix is exact, and arbitrary unused slots remain after it. -/
theorem batch1_filterLoop (f : α → Except Error (Option Bool)) (heap : VectorHeap α)
    (slots : List (Option α)) :
    ∀ (pre : List α) (tail : List (Option α)), slots.length ≤ tail.length →
      pre.length + tail.length < 2 ^ 62 →
      match batch1_keepSlots f slots with
      | .error e =>
          (forIn slots (JInt.wrap .i64 ((pre.length : Int) + 1))
            (batch1_filterStep f heap.length)).run (heap ++ [pre.map some ++ tail]) = .error e
      | .ok kept =>
          ∃ rest, rest.length + kept.length = tail.length ∧
            (forIn slots (JInt.wrap .i64 ((pre.length : Int) + 1))
              (batch1_filterStep f heap.length)).run (heap ++ [pre.map some ++ tail]) =
              .ok (JInt.wrap .i64 (((pre ++ kept).length : Int) + 1),
                heap ++ [(pre ++ kept).map some ++ rest]) := by
  induction slots with
  | nil =>
    intro pre tail _ _
    exact ⟨tail, by simp only [List.length_nil, Nat.add_zero], by
      simp only [batch1_keepSlots, List.forIn_nil, vector_pure_run, List.append_nil]⟩
  | cons o slots ih =>
    intro pre tail hreserve hsize
    cases tail with
    | nil => simp only [List.length_nil, List.length_cons] at hreserve; omega
    | cons old tail =>
      cases o with
      | none =>
        simp only [batch1_keepSlots, List.forIn_cons, batch1_filterStep, vector_bind_run,
          vector_throw_run]
      | some x =>
        have hs := batch1_filterStore heap pre old tail x hsize
        have hcurrent : (JInt.wrap .i64 ((pre.length : Int) + 1)).val = pre.length + 1 :=
          ival_wrap _ (by simp only [List.length_cons] at hsize; omega)
        have hnext : JInt.wrap .i64 ((pre.length : Int) + 1) + one =
            JInt.wrap .i64 (((pre ++ [x]).length : Int) + 1) := by
          apply Subtype.ext
          rw [ival_add _ _ (by
            rw [hcurrent, ival_one]
            simp only [List.length_cons] at hsize
            omega), hcurrent, ival_one]
          rw [ival_wrap _ (by
            simp only [List.length_append, List.length_cons, List.length_nil,
              Int.natCast_add, Int.natCast_zero, Int.natCast_one]
            simp only [List.length_cons] at hsize
            omega)]
          simp only [List.length_append, List.length_cons, List.length_nil,
            Int.natCast_add, Int.natCast_zero, Int.natCast_one]
          omega
        cases hb : boolResult f x with
        | error e =>
          have hstep : (batch1_filterStep f heap.length (some x)
              (JInt.wrap .i64 ((pre.length : Int) + 1))).run
              (heap ++ [pre.map some ++ old :: tail]) = .error e := by
            simp only [batch1_filterStep, vector_bind_run, hs, vector_lift_run, hb, Except.map]
          simp only [batch1_keepSlots, hb, List.forIn_cons, vector_bind_run, hstep]
        | ok b =>
          cases b with
          | false =>
            have hstep : (batch1_filterStep f heap.length (some x)
                (JInt.wrap .i64 ((pre.length : Int) + 1))).run
                (heap ++ [pre.map some ++ old :: tail]) =
                .ok (.yield (JInt.wrap .i64 ((pre.length : Int) + 1)),
                  heap ++ [pre.map some ++ some x :: tail]) := by
              simp only [batch1_filterStep, vector_bind_run, hs, vector_lift_run, hb,
                Except.map, Bool.false_eq_true, ite_false, vector_pure_run]
            have hreserve' : slots.length ≤ (some x :: tail).length := by
              simp only [List.length_cons] at hreserve ⊢
              omega
            have hih := ih pre (some x :: tail) hreserve'
              (by simpa only [List.length_cons] using hsize)
            cases hk : batch1_keepSlots f slots with
            | error e =>
              simp only [batch1_keepSlots, hb, hk, List.forIn_cons, vector_bind_run, hstep]
              simpa only [hk] using hih
            | ok kept =>
              obtain ⟨rest, hrest, hrun⟩ := (show ∃ rest,
                  rest.length + kept.length = (some x :: tail).length ∧
                  (forIn slots (JInt.wrap .i64 ((pre.length : Int) + 1))
                    (batch1_filterStep f heap.length)).run
                      (heap ++ [pre.map some ++ some x :: tail]) =
                    .ok (JInt.wrap .i64 (((pre ++ kept).length : Int) + 1),
                      heap ++ [(pre ++ kept).map some ++ rest]) from by simpa only [hk] using hih)
              simp only [batch1_keepSlots, hb, hk, Bool.false_eq_true, ite_false]
              refine ⟨rest, hrest, ?_⟩
              simp only [List.forIn_cons, vector_bind_run, hstep, hrun]
          | true =>
            have hstep : (batch1_filterStep f heap.length (some x)
                (JInt.wrap .i64 ((pre.length : Int) + 1))).run
                (heap ++ [pre.map some ++ old :: tail]) =
                .ok (.yield (JInt.wrap .i64 (((pre ++ [x]).length : Int) + 1)),
                  heap ++ [(pre ++ [x]).map some ++ tail]) := by
              simp only [batch1_filterStep, vector_bind_run, hs, vector_lift_run, hb,
                Except.map, ite_true, vector_pure_run, hnext, List.map_append,
                List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
            have hih := ih (pre ++ [x]) tail
              (by simp only [List.length_cons] at hreserve; omega)
              (by simp only [List.length_append, List.length_cons, List.length_nil] at hsize ⊢; omega)
            cases hk : batch1_keepSlots f slots with
            | error e =>
              simp only [batch1_keepSlots, hb, hk, List.forIn_cons, vector_bind_run, hstep]
              simpa only [hk] using hih
            | ok kept =>
              simp only [hk] at hih
              obtain ⟨rest, hrest, hrun⟩ := hih
              simp only [batch1_keepSlots, hb, hk, ite_true]
              refine ⟨rest, by simp only [List.length_cons]; omega, ?_⟩
              simp only [List.forIn_cons, vector_bind_run, hstep, hrun,
                List.append_assoc, List.cons_append, List.nil_append]


theorem batch1_filterForIn (f : α → Except Error (Option Bool))
    (slots : List (Option α)) (b : Nat) (j : I) :
    forIn (⟨slots⟩ : SlotArray α) j (fun x j => do
      heapSet b x j
      let keep ← liftM (boolResult f x)
      pure (.yield (if keep then j + one else j))) =
      forIn slots j (batch1_filterStep f b) := by
  change (forIn slots j _ : VectorM α I) = forIn slots j _
  congr 1
  funext o k
  cases o <;> rfl

/-- Finishing the source loop trims precisely its kept prefix. -/
theorem batch1_filterArray_run (f : α → Except Error (Option Bool))
    (slots : List (Option α)) (heap : VectorHeap α) (hn : slots.length < 2 ^ 62) :
    (heapFilterArray f slots).run heap =
      (batch1_keepSlots f slots).map (fun kept => (heap.length, heap ++ [kept.map some])) := by
  have hnat : (JInt.wrap .i64 (slots.length : Int)).val.toNat = slots.length := by
    rw [ival_wrap _ (by omega), Int.toNat_natCast]
  have hloop := batch1_filterLoop f heap slots [] (List.replicate slots.length none)
    (by simp only [List.length_replicate]; omega)
    (by simp only [List.length_nil, Nat.zero_add, List.length_replicate]; exact hn)
  simp only [List.length_nil, List.map_nil, List.nil_append, List.length_replicate,
    Int.natCast_zero, Int.zero_add] at hloop
  have hone : JInt.wrap .i64 1 = one := rfl
  rw [hone] at hloop
  simp only [heapFilterArray, filterArray, pure_bind, batch1_filterForIn]
  change (do
    let b ← heapAllocate (JInt.wrap .i64 (slots.length : Int)).val.toNat
    let j ← forIn slots one (batch1_filterStep f b)
    modify (fun heap => heap.set b ((heap[b]?.getD []).take (j - one).val.toNat))
    let _ ← heapLength b
    pure b : VectorM α Nat).run heap = _
  rw [hnat]
  simp only [vector_bind_run, heapAllocate_run]
  cases hk : batch1_keepSlots f slots with
  | error e =>
    simp only [hk] at hloop
    simp only [hloop, Except.map]
  | ok kept =>
    simp only [hk] at hloop
    obtain ⟨rest, hrest, hrun⟩ := hloop
    have hklen : kept.length ≤ slots.length := by omega
    have hj : (JInt.wrap .i64 ((kept.length : Int) + 1) - one).val.toNat = kept.length := by
      have hv : (JInt.wrap .i64 ((kept.length : Int) + 1)).val = kept.length + 1 :=
        ival_wrap _ (by omega)
      rw [ival_sub _ _ (by rw [hv, ival_one]; omega), hv, ival_one]
      omega
    have hget : (heap ++ [kept.map some ++ rest])[heap.length]? =
        some (kept.map some ++ rest) := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have htrim : (kept.map some ++ rest).take kept.length = kept.map some := by
      rw [← List.length_map (f := some) (as := kept), List.take_append_length]
    have hset : (heap ++ [kept.map some ++ rest]).set heap.length (kept.map some) =
        heap ++ [kept.map some] := by
      rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
      rfl
    have hlen : (heapLength heap.length).run (heap ++ [kept.map some]) =
        .ok (JInt.wrap .i64 (kept.length : Int), heap ++ [kept.map some]) := by
      rw [heapLength_run, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      simp only [List.getElem?_cons_zero, List.length_map]
    simp only [hrun, vector_modify_run, hj, hget, Option.getD_some, htrim, hset,
      hlen, vector_pure_run, Except.map]

/-- The recursive specification agrees with the ordinary zip/filter expression. -/
theorem batch1_keepSlots_success (f : α → Except Error (Option Bool))
    (xs : List α) (bs : List Bool) (h : xs.mapM (boolResult f) = .ok bs) :
    batch1_keepSlots f (xs.map some) =
      .ok (((xs.zip bs).filter (·.2)).map Prod.fst) := by
  induction xs generalizing bs with
  | nil =>
    change Except.ok [] = Except.ok bs at h
    cases h
    rfl
  | cons x xs ih =>
    cases hb : boolResult f x with
    | error e =>
      simp only [List.mapM_cons, hb, Except.bind] at h
      cases h
    | ok b =>
      cases ht : xs.mapM (boolResult f) with
      | error e =>
        simp only [List.mapM_cons, hb, ht, Except.bind] at h
        cases h
      | ok bs' =>
        simp only [List.mapM_cons, hb, ht, Except.bind, Except.pure] at h
        cases h
        rw [List.map_cons, batch1_keepSlots, hb, ih bs' ht]
        cases b <;> rfl

def batch1_slotBool (f : α → Except Error (Option Bool)) : Option α → Except Error Bool
  | none => .error .undefinedReference
  | some x => boolResult f x

/-- Mapping only the predicates and filtering have the same first error. -/
theorem batch1_keepSlots_error (f : α → Except Error (Option Bool))
    (slots : List (Option α)) (e : Error)
    (h : slots.mapM (batch1_slotBool f) = .error e) : batch1_keepSlots f slots = .error e := by
  induction slots generalizing e with
  | nil => cases h
  | cons o slots ih =>
    cases o with
    | none =>
      simp only [List.mapM_cons, batch1_slotBool, Except.bind] at h
      cases h
      rfl
    | some x =>
      cases hb : boolResult f x with
      | error e' =>
        simp only [List.mapM_cons, batch1_slotBool, hb, Except.bind] at h
        cases h
        simp only [batch1_keepSlots, hb]
      | ok b =>
        cases ht : slots.mapM (batch1_slotBool f) with
        | error e' =>
          simp only [List.mapM_cons, batch1_slotBool, hb, ht, Except.bind] at h
          cases h
          simp only [batch1_keepSlots, hb, ih _ ht]
        | ok bs =>
          simp only [List.mapM_cons, batch1_slotBool, hb, ht, Except.bind, Except.pure] at h
          cases h

/-- Filtering preserves order and all old arrays, and propagates the first iteration error. -/
theorem MultidimcovArrayV2FilterArray_proven : JuliaLean.Proofs.base.array.FilterArraySpec := by
  intro α f slots heap hn
  have hrun := batch1_filterArray_run f slots heap hn
  constructor
  · intro xs hslots bs hbs
    subst slots
    rw [batch1_keepSlots_success f xs bs hbs] at hrun
    simpa only [Except.map, List.map_map, Function.comp_def] using hrun
  · intro e he
    have herr := batch1_keepSlots_error f slots e
      (by
        refine Eq.trans ?_ he
        apply congrArg (fun g => slots.mapM g)
        funext o
        cases o <;> rfl)
    rw [herr] at hrun
    exact hrun
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
namespace ChatGPTBatch1.Splice
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.opusGrowth JuliaLean.Proofs.base.int
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] JInt.wrap

/-- Deletion remains correct when the optimization's doubled index wraps; both move directions
implement the same splice. The bound is on the deletion count, not half the source size. -/
theorem batchDeleteatWide {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s handle mem off n slots) (i delta : I)
    (hdelta : delta.val < 9223372036854775807) (hi1 : 1 ≤ i.val) (hin : i.val ≤ n.val) (hd : 0 ≤ delta.val)
    (hdi : delta.val ≤ n.val + 1 - i.val) :
    ∃ next, (vecDeleteat α (layout := layout) handle i delta).run s = (.ok (), next) ∧ next.validVector handle ∧
      next.contents handle = (vwWindow slots off n).take (i.val - 1).toNat ++
        (vwWindow slots off n).drop (i.val - 1 + delta.val).toNat ∧
      (∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?) ∧
      (∀ m, m < s.memories.length → m ≠ mem → next.memories[m]? = s.memories[m]?) ∧
      ∃ off' slots', VecAt next handle mem off' (n-delta) slots' := by
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
  · have hle : (JInt.wrap .i64 2 * i + delta ≤ n) := hbr
    have h1d : (one + delta).val = 1 + delta.val := by
      rw [ival_add _ _ (by rw [ival_one]; omega), ival_one]
    have him : (i - one).val = i.val - 1 := ival_sub_one i (by omega)
    obtain ⟨slots1, hcp, hv1, hw1⟩ := vwCopy_run s handle mem off n slots h (one + delta) one
      (i - one) (by rw [him]; omega) (by rw [h1d]; omega) (by rw [h1d, him]; omega)
      (by rw [ival_one]; exact Int.le_refl 1) (by rw [ival_one, him]; omega)
    obtain ⟨next, off', slots', hdel, hv2, hmem, harr, hw2⟩ :=
      vwDeletebeg_run (layout := layout) _ handle mem off n slots1 hv1 delta hd (by omega)
    refine ⟨next,?_,hv2.valid,?_,?_,?_,off',slots',hv2⟩
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
    · intro m _ hne
      rw [hmem]
      simp only [List.getElem?_set_ne (Ne.symm hne)]
  · have hgt : ¬ (JInt.wrap .i64 2 * i + delta ≤ n) := hbr
    have hnmax : n.val < 9223372036854775807 := by
      have hterm := ival_bounds (JInt.wrap .i64 2 * i + delta)
      rw [jle_iff] at hbr
      omega
    have hid : (i + delta).val = i.val + delta.val := ival_add _ _ (by omega)
    have hn1 : (n + one).val = n.val + 1 := ival_add_one n (by omega)
    have hn1d : (n + one - delta).val = n.val + 1 - delta.val := by
      rw [ival_sub _ _ (by rw [hn1]; omega), hn1]
    have hk : (n + one - delta - i).val = n.val + 1 - delta.val - i.val := by
      rw [ival_sub _ _ (by rw [hn1d]; omega), hn1d]
    obtain ⟨slots1, hcp, hv1, hw1⟩ := vwCopy_run s handle mem off n slots h i (i + delta)
      (n + one - delta - i) (by rw [hk]; omega) hi1 (by rw [hk]; omega) (by rw [hid]; omega)
      (by rw [hid, hk]; omega)
    obtain ⟨next, slots', hdel, hv2, hmem, harr, hw2⟩ :=
      vwDeleteend_run (layout := layout) _ handle mem off n slots1 hv1 delta hd (by omega) (by omega)
    refine ⟨next,?_,hv2.valid,?_,?_,?_,off,slots',hv2⟩
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
    · intro m _ hne
      rw [hmem]
      simp only [List.getElem?_set_ne (Ne.symm hne)]



theorem batchAllocGenericMemoryRun (l : MemoryLayout) (nel : Nat) (s : MutableMemory α) :
    (allocGenericMemory (some l) (mutableFreshMemory 0) mutableFreshMemory nel).run s =
      if memoryFits l nel then (.ok s.memories.length,
        {s with memories := s.memories ++ [List.replicate nel none]})
      else (.error (.argument genericMemorySizeMessage), s) := by
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

theorem batchMemorynewRun (l : MemoryLayout) (n : I) (s : MutableMemory α) :
    (memorynew (some l) (mutableFreshMemory 0) mutableFreshMemory n).run s =
      if 0 ≤ n.val ∧ memoryFits l n.val.toNat then
        (.ok s.memories.length, {s with memories := s.memories ++ [List.replicate n.val.toNat none]})
      else (.error (.argument genericMemorySizeMessage), s) := by
  have hb := ival_bounds n
  simp only [memorynew, batchAllocGenericMemoryRun]
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


/-- A native vector allocation either returns its exact fresh header and memory, or the
installed size error without changing the store. -/
theorem batchAllocateRun (l : MemoryLayout) (s : MutableMemory α) (a : Nat) (n : I) :
    (mutableAllocate (some l) a n).run s =
      if 0 ≤ n.val ∧ memoryFits l n.val.toNat then
        (.ok s.arrays.length,
          { memories := s.memories ++ [List.replicate n.val.toNat none]
            arrays := s.arrays ++ [⟨(s.memories.length, one), n⟩] })
      else (.error (.argument genericMemorySizeMessage), s) := by
  simp only [mutableAllocate, arrayUndef1, memoryUndef, stateExcept_bind, batchMemorynewRun]
  by_cases h : 0 ≤ n.val ∧ memoryFits l n.val.toNat
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]

/-- Nonempty out-of-bounds splice ranges fail before allocating the removed vector. -/
theorem batchSpliceOutside (l : DictLayout) (convert : β → Except Error α)
    (s : MutableMemory α) (a : Nat) (lo hi : I) (ins : List β)
    (hv : s.validVector a) (hne : lo.val ≤ hi.val)
    (hout : ¬ (1 ≤ lo.val ∧ hi.val ≤ (s.contents a).length)) :
    (mutableSpliceRange (MemoryLayoutMetadata.ofRuntime l) convert a lo hi ins).run s = (.error .bounds, s) := by
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hv
  have hlen : ((s.contents a).length : Int) = n.val := by
    rw [h.contents, vwWindow_length h]
    have hn := h.2.2.2.1
    omega
  have hnot : ¬ (lo > hi) := by rw [gt_iff_lt, jlt_iff]; omega
  have hnotin : ¬ (one ≤ lo ∧ hi ≤ n) := by
    rw [jle_iff, jle_iff, ival_one]
    omega
  simp only [mutableSpliceRange, spliceRange, getindexUnitRange, stateExcept_bind,
    stateExcept_pure, mutableLength_run s a _ h.1, hnot, hnotin, decide_false,
    Bool.not_false, Bool.and_self, ite_true, stateExcept_throw]
end ChatGPTBatch1.Splice
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
namespace ChatGPTBatch1.Splice
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.opusGrowth JuliaLean.Proofs.base.int
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] JInt.wrap



open solArrayGrow

/-- Growth keeps the old memory or chooses the next fresh memory identifier. -/
theorem batchGrowatMemory (l : DictLayout) (s : MutableMemory α) (a mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots)
    (i d : I) (hd : 0 ≤ d.val) (g : VectorGeometry)
    (hp : growatPlan l (geometryOf s a) i.val d.val.toNat = .ok g)
    (next : MutableMemory α)
    (hr : (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a i d).run s =
      (.ok (), next)) :
    ∃ mem' off' slots', VecAt next a mem' off' (n+d) slots' ∧
      (mem' = mem ∨ mem' = s.memories.length) := by
  have ho := h.2.2.1
  have hn := h.2.2.2.1
  have hc := h.2.2.2.2.2
  have hN : ((n.val.toNat : Nat) : Int) = n.val := by omega
  have hO : ((off.val.toNat : Nat) : Int) = off.val := by omega
  have hD : ((d.val.toNat : Nat) : Int) = d.val := by omega
  have hMax : typemaxNat = 9223372036854775807 := by decide
  have hHalf : ((n.val.toNat/2 : Nat) : Int) = n.val/2 := by omega
  rw [opusGrowth.VecAt.geometry h] at hp
  dsimp only [growatPlan] at hp
  by_cases hfirst : i.val = 1
  · have hieq : i = one := Subtype.ext (hfirst.trans ival_one.symm)
    subst i
    simp only [ival_one,ite_true] at hp
    obtain ⟨grown,mem',off',slots',hr',hv,_,_,_,_,_,_,hm⟩ := (growbeg_plan l h d hd).2 g hp
    have hrun : (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a one d).run s =
      (.ok (),grown) := by simpa only [growat,stateExcept_bind,stateExcept_pure,ite_true] using hr'
    have he : grown = next := (Prod.mk.inj (hrun.symm.trans hr)).2
    subst grown
    exact ⟨mem',off',slots',hv,hm⟩
  · simp only [hfirst,ite_false] at hp
    have hi1 : i ≠ one := by intro hh; have := congrArg Subtype.val hh; rw [ival_one] at this; omega
    by_cases hend : n.val.toNat < typemaxNat ∧ i.val = (n.val.toNat : Int)+1
    · simp only [hend,ite_true] at hp
      have hnmax : n.val < 9223372036854775807 := by rw [hMax] at hend; omega
      have hn1 : (n+one).val = n.val+1 := ival_add_one n (by omega)
      have hieq : i = n+one := Subtype.ext (by rw [hn1]; omega)
      have hnlt : n < JInt.typemax .i64 := by
        change n.val < (JInt.typemax .i64).val
        have hm : (JInt.typemax .i64).val = 9223372036854775807 := ival_wrap _ (by decide)
        rw [hm]
        exact hnmax
      obtain ⟨grown,mem',off',slots',hr',hv,_,_,_,_,_,_,hm⟩ := (growend_plan l h d hd).2 g hp
      have hrun : (growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))) a i d).run s =
        (.ok (),grown) := by
        simpa only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,ms_length,
          mutableLength_run s a _ h.1,hnlt,decide_true,show i = n+one from hieq,eq_self_iff_true,Bool.true_and,ite_true,
          show n+one ≠ one from fun hh => hi1 (hieq.trans hh)] using hr'
      have he : grown = next := (Prod.mk.inj (hrun.symm.trans hr)).2
      subst grown
      exact ⟨mem',off',slots',hv,hm⟩
    · simp only [hend,ite_false] at hp
      by_cases hidx : 1 < i.val ∧ i.val ≤ (n.val.toNat : Int)
      · simp only [hidx,not_true_eq_false,ite_false] at hp
        have hii : 1 < i.val := hidx.1
        have hin : i.val ≤ n.val := by omega
        by_cases hover : typemaxNat < off.val.toNat-1+(n.val.toNat+d.val.toNat)
        · simp only [hover,ite_true] at hp
          cases hp
        · simp only [hover,ite_false] at hp
          have hov : off.val-1+n.val+d.val ≤ 9223372036854775807 := by rw [hMax] at hover; omega
          by_cases hstart : i.val ≤ ((n.val.toNat/2 : Nat) : Int) ∧ d.val.toNat ≤ off.val.toNat-1
          · obtain ⟨grown,result,hr',hv,_⟩ := growat_startroom_run (MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h i d
              hii hin hd (by omega) (by omega) hov
            have he : grown = next := (Prod.mk.inj (hr'.symm.trans hr)).2
            subst grown
            exact ⟨mem,off-d,result,hv,Or.inl rfl⟩
          · simp only [hstart,ite_false] at hp
            by_cases hendroom : ¬ i.val ≤ ((n.val.toNat/2 : Nat) : Int) ∧
                off.val.toNat-1+(n.val.toNat+d.val.toNat) ≤ slots.length
            · obtain ⟨grown,result,hr',hv,_⟩ := growat_endroom_run (MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h i d
                hii hin hd (by omega) (by omega)
              have he : grown = next := (Prod.mk.inj (hr'.symm.trans hr)).2
              subst grown
              exact ⟨mem,off,result,hv,Or.inl rfl⟩
            · simp only [hendroom,ite_false] at hp
              have hNoStart : i.val ≤ n.val/2 → off.val-1 < d.val := by
                intro hp; by_cases hfit : d.val ≤ off.val-1
                · exact False.elim (hstart ⟨by omega,by omega⟩)
                · omega
              have hNoEnd : n.val/2 < i.val → (slots.length : Int) < off.val-1+n.val+d.val := by
                intro hp; by_cases hfit : off.val-1+n.val+d.val ≤ (slots.length : Int)
                · exact False.elim (hendroom ⟨by omega,by omega⟩)
                · omega
              by_cases hover2 : typemaxNat < n.val.toNat+2*d.val.toNat+1
              · simp only [hover2,ite_true] at hp
                cases hp
              · simp only [hover2,ite_false] at hp
                have hov2 : n.val+2*d.val+1 ≤ 9223372036854775807 := by rw [hMax] at hover2; omega
                let K := max (overallocationNat slots.length) (n.val.toNat+2*d.val.toNat+1)
                have hfit : memoryFits l K := by
                  by_cases hh : memoryFits l K
                  · exact hh
                  · simp only [allocationPlan,show ¬ memoryFits l (max (overallocationNat slots.length)
                    (n.val.toNat+2*d.val.toNat+1)) from hh,ite_false] at hp
                    cases hp
                obtain ⟨grown,newoff,D1,result,hr',hv,_⟩ := (growat_alloc_run l s a mem off n slots h i d
                  hii hin hd hNoStart hNoEnd hov hov2 K rfl).2 hfit
                have he : grown = next := (Prod.mk.inj (hr'.symm.trans hr)).2
                subst grown
                exact ⟨s.memories.length,newoff,result,hv,Or.inr rfl⟩
      · simp only [hidx,not_false_eq_true,ite_true] at hp
        cases hp



/-- The exact range-copy action at the front of `spliceRange`. -/
abbrev batchRangeGet {α : Type} (l : MemoryLayout) (a : Nat) (lo hi : I) : MutationM α Nat :=
  getindexUnitRange (fun x : I => pure (decide (x.val > 0)))
    (fun a (r : I × I) => do
      let n ← mutableLength a
      if !(r.1 > r.2) && !(one ≤ r.1 ∧ r.2 ≤ n) then throw .bounds)
    (fun r => pure (r.2-r.1+one)) (fun r => pure (r.2-r.1+one))
    (fun a n => similar419 (mutableAllocate (some l) a) a n)
    (fun _ => pure one) (fun r => pure r.1) mutableCopyto a (lo,hi)

private theorem batchRangeCount (n lo hi : I) (hn : 0 ≤ n.val)
    (hr : lo.val ≤ hi.val+1) (hb : hi.val < lo.val ∨ 1 ≤ lo.val ∧ hi.val ≤ n.val) :
    (hi-lo+one).val = hi.val-lo.val+1 ∧ 0 ≤ (hi-lo+one).val ∧ (hi-lo+one).val ≤ n.val := by
  have hnmax := ival_bounds n
  have hv : (hi-lo).val = hi.val-lo.val := ival_sub _ _ (by rcases hb with hb|hb <;> omega)
  have hv' : (hi-lo+one).val = hi.val-lo.val+1 := by
    rw [ival_add _ _ (by rw [hv,ival_one]; rcases hb with hb|hb <;> omega),hv,ival_one]
  exact ⟨hv',by rw [hv']; omega,by rw [hv']; rcases hb with hb|hb <;> omega⟩

private theorem batchVecAppend (s : MutableMemory α) (a mem : Nat) (off n : I)
    (slots : List (Option α)) (h : VecAt s a mem off n slots) (d : I) (xs : List (Option α))
    (hd : 0 ≤ d.val) (hlen : xs.length = d.val.toNat) (hmax : xs.length < 2^63) :
    let next : MutableMemory α :=
      ⟨s.memories ++ [xs],s.arrays ++ [⟨(s.memories.length,one),d⟩]⟩
    VecAt next a mem off n slots ∧ VecAt next s.arrays.length s.memories.length one d xs := by
  have ha := (List.getElem?_eq_some_iff.mp h.1).choose
  have hm := (List.getElem?_eq_some_iff.mp h.2.1).choose
  refine ⟨⟨?_,?_,h.2.2⟩,⟨?_,?_,?_,hd,?_,hmax⟩⟩
  · exact (List.getElem?_append_left ha).trans h.1
  · exact (List.getElem?_append_left hm).trans h.2.1
  · simp
  · simp
  · simp only [ival_one,Int.le_refl]
  · rw [ival_one,hlen]
    omega

private theorem batchVecFrame {s t : MutableMemory α} {a mem : Nat} {off n : I}
    {xs : List (Option α)} (h : VecAt s a mem off n xs)
    (ha : t.arrays[a]? = s.arrays[a]?) (hm : t.memories[mem]? = s.memories[mem]?) :
    VecAt t a mem off n xs := ⟨ha.trans h.1,hm.trans h.2.1,h.2.2⟩

/-- Range extraction returns a fresh vector while preserving the source window. -/
theorem batchRangeGetRun (l : MemoryLayout) (s : MutableMemory α) (a mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots) (lo hi : I)
    (hr : lo.val ≤ hi.val+1) (hb : hi.val < lo.val ∨ 1 ≤ lo.val ∧ hi.val ≤ n.val) :
    let d := hi-lo+one
    let removed := ((s.contents a).drop (lo.val-1).toNat).take d.val.toNat
    (¬ memoryFits l d.val.toNat → (batchRangeGet l a lo hi).run s =
      (.error (.argument genericMemorySizeMessage),s)) ∧
    (memoryFits l d.val.toNat → ∃ next,
      (batchRangeGet l a lo hi).run s = (.ok s.arrays.length,next) ∧
      VecAt next a mem off n slots ∧
      VecAt next s.arrays.length s.memories.length one d removed ∧
      next.contents s.arrays.length = removed ∧
      next.memories.length = s.memories.length+1) := by
  dsimp only
  obtain ⟨hdv,hd0,hdn⟩ := batchRangeCount n lo hi h.2.2.2.1 hr hb
  have hbound : (decide (¬lo > hi) && decide (¬(one ≤ lo ∧ hi ≤ n))) = false := by
    rcases hb with hb|hb
    · have ht : lo > hi := hb
      simp only [ht,not_true_eq_false,decide_false,Bool.false_and]
    · have hin : one ≤ lo ∧ hi ≤ n := ⟨by rw [jle_iff,ival_one]; exact hb.1, hb.2⟩
      simp only [hin,true_and,not_true_eq_false,decide_false,Bool.and_false]
  have hbound' : (!(decide (lo > hi)) && !(decide (one ≤ lo ∧ hi ≤ n))) = false := by
    simpa only [decide_not] using hbound
  have heq : (batchRangeGet l a lo hi).run s =
      ((do let v ← mutableAllocate (some l) a (hi-lo+one)
           if (hi-lo+one).val > 0 then mutableCopyto v one a lo (hi-lo+one)
           pure v) : MutationM α Nat).run s := by
    simp only [batchRangeGet,getindexUnitRange,stateExcept_bind,stateExcept_pure,
      mutableLength_run s a _ h.1,hbound',Bool.false_eq_true,ite_false,similar419,
      decide_eq_true_eq,pure_bind]
  rw [heq]
  refine ⟨fun hnf => ?_,fun hfit => ?_⟩
  · simp only [stateExcept_bind,batchAllocateRun,hd0,hnf,true_and,ite_false]
  · let d := hi-lo+one
    have hdvD : d.val = hi.val-lo.val+1 := hdv
    have hd0D : 0 ≤ d.val := hd0
    have hdnD : d.val ≤ n.val := hdn
    let r := ((s.contents a).drop (lo.val-1).toNat).take d.val.toNat
    have hlen : r.length = d.val.toNat := by
      dsimp only [r]
      rw [List.length_take,List.length_drop,h.contents,vwWindow_length h]
      apply Nat.min_eq_left
      dsimp only [d]
      rcases hb with hb|hb <;> omega
    have hmax : d.val.toNat < 2^63 := by
      have := hfit.1
      unfold maxIntVal at this
      exact Nat.lt_trans this (by decide)
    let fresh : MutableMemory α :=
      ⟨s.memories ++ [List.replicate d.val.toNat none],
        s.arrays ++ [⟨(s.memories.length,one),d⟩]⟩
    let next : MutableMemory α :=
      ⟨s.memories ++ [r],s.arrays ++ [⟨(s.memories.length,one),d⟩]⟩
    obtain ⟨ha,hv⟩ := batchVecAppend s a mem off n slots h d r hd0 hlen (by rw [hlen]; exact hmax)
    refine ⟨next,?_,ha,hv,?_,?_⟩
    · have hAlloc : (mutableAllocate (some l) a d).run s = (.ok s.arrays.length,fresh) := by
        rw [batchAllocateRun,if_pos ⟨hd0,hfit⟩]
      by_cases hdpos : 0 < d.val
      · obtain ⟨hA,hV⟩ := batchVecAppend s a mem off n slots h d (List.replicate d.val.toNat none)
          hd0 (List.length_replicate ..) (by rw [List.length_replicate]; exact hmax)
        have hc := vwCopyto_run fresh hV hA one lo d (by omega) (by simp only [ival_one,Int.le_refl])
          (by rw [ival_one]; omega) (by rcases hb with hb|hb <;> omega)
          (by dsimp only [d]; rw [hdv]; omega)
        have hrSlots : (slots.drop ((off.val-1).toNat+(lo.val-1).toNat)).take d.val.toNat = r := by
          dsimp only [r]
          rw [h.contents]
          simp only [vwWindow,List.drop_take,List.drop_drop,List.take_take]
          rw [Nat.min_eq_left (by rcases hb with hb|hb <;> omega)]
        simp only [ival_one,Int.sub_self,Int.toNat_zero,Nat.zero_add,List.take_zero,List.nil_append,
          List.drop_replicate,Nat.sub_self,List.replicate_zero,List.append_nil,hrSlots] at hc
        have hmem : fresh.memories.set s.memories.length r = next.memories := by
          dsimp only [fresh,next]
          rw [List.set_append_right _ _ (Nat.le_refl _)]
          simp only [Nat.sub_self,List.set_cons_zero]
        have hstate : {fresh with memories := fresh.memories.set s.memories.length r} = next := by
          rw [hmem]
        rw [hstate] at hc
        simpa only [d,stateExcept_bind,hAlloc,hdpos,ite_true,hc,stateExcept_pure] using
          (show ((do let v ← mutableAllocate (some l) a d
                     if d.val > 0 then mutableCopyto v one a lo d
                     pure v) : MutationM α Nat).run s = (.ok s.arrays.length,next) by
            simp only [stateExcept_bind,hAlloc,hdpos,ite_true,hc,stateExcept_pure])
      · have hz : d.val.toNat = 0 := by omega
        have hrnil : r = [] := by simp only [r,hz,List.take_zero]
        have hstates : fresh = next := by simp only [fresh,next,hz,hrnil,List.replicate_zero]
        change ((do let v ← mutableAllocate (some l) a d
                    if d.val > 0 then mutableCopyto v one a lo d
                    pure v) : MutationM α Nat).run s = _
        simp only [stateExcept_bind,hAlloc,hdpos,ite_false,stateExcept_pure,hstates]
    · rw [hv.contents]
      simp only [vwWindow,ival_one,Int.sub_self,Int.toNat_zero,List.drop_zero]
      exact List.take_of_length_le (by rw [hlen]; exact Nat.le_refl _)
    · simp only [next,List.length_append,List.length_cons,List.length_nil]




private theorem batchDeletedEnds (w : List α) (p d start count : Nat)
    (hp : p ≤ w.length) (hl : start ≤ p) (hr : p ≤ start+count) :
    (w.take p ++ w.drop (p+d)).take start = w.take start ∧
    (w.take p ++ w.drop (p+d)).drop (start+count) = w.drop (start+count+d) := by
  have hlen : (w.take p).length = p := by rw [List.length_take,Nat.min_eq_left hp]
  refine ⟨?_,?_⟩
  · rw [List.take_append_of_le_length (by rw [hlen]; exact hl),List.take_take,Nat.min_eq_left hl]
  · rw [List.drop_append,List.drop_eq_nil_of_le (by rw [hlen]; exact hr),List.nil_append,
      List.drop_drop,hlen]
    congr 1
    omega

private theorem batchGrownEnds (w grown : List α) (p d start stop : Nat)
    (hl : start ≤ p) (hr : p ≤ stop)
    (hpre : grown.take p = w.take p) (hsuf : grown.drop (p+d) = w.drop p) :
    grown.take start = w.take start ∧ grown.drop (stop+d) = w.drop stop := by
  refine ⟨?_,?_⟩
  · have hh := congrArg (fun xs : List α => xs.take start) hpre
    simpa only [List.take_take,Nat.min_eq_left hl] using hh
  · have hh := congrArg (fun xs : List α => xs.drop (stop-p)) hsuf
    simp only [List.drop_drop] at hh
    rwa [show p+d+(stop-p) = stop+d by omega,show p+(stop-p) = stop by omega] at hh

abbrev batchSpliceFinish (convert : β → Except Error α) (a : Nat) (lo : I)
    (ins : List β) (v : Nat) : MutationM α Nat := do
  let _ ← forIn ins one (fun x k => do
    let value ← stateExceptLift (convert x)
    mutableSet a value (lo+k-one)
    pure (ForInStep.yield (k+one)))
  pure v

private theorem batchSpliceFinishRun {α β : Type} (l : MemoryLayout) (convert : β → Except Error α)
    (s : MutableMemory α) (a mem v vmem : Nat) (off n vo vn lo : I)
    (slots saved : List (Option α)) (h : VecAt s a mem off n slots)
    (hv : VecAt s v vmem vo vn saved) (hne : vmem ≠ mem)
    (ins : List β) (hlo : 1 ≤ lo.val) (hcap : lo.val-1+ins.length ≤ n.val) :
    (∀ cs, ins.mapM convert = .ok cs → ∃ after,
      (batchSpliceFinish convert a lo ins v).run s = (.ok v,after) ∧
      after.validVector a ∧ VecAt after v vmem vo vn saved ∧
      after.contents a = (s.contents a).take (lo.val-1).toNat ++ cs.map some ++
        (s.contents a).drop (lo.val-1+ins.length).toNat) ∧
    (∀ e, ins.mapM convert = .error e → ((batchSpliceFinish convert a lo ins v).run s).1 = .error e) := by
  refine ⟨fun cs hm => ?_,fun e hm => ?_⟩
  · have hcs := converted_length convert ins cs hm
    obtain ⟨k,after,hr,ha,hc,harr,hmem⟩ := spliceStores_run (some l) convert a mem off n lo hlo
      ins cs s slots 0 one h (by simpa using hcap) (fun _ => by simp only [ival_one,Int.natCast_zero,Int.zero_add]) hm
    refine ⟨after,?_,ha,batchVecFrame hv (by rw [harr]) (hmem _ hne),?_⟩
    · simp only [batchSpliceFinish,stateExcept_bind,hr,stateExcept_pure]
    · simpa only [Int.natCast_zero,Int.add_zero,hcs] using hc
  · have hloop := spliceStores_error convert a mem off n lo hlo ins s slots 0 one e h
      (by simpa using hcap) (fun _ => by simp only [ival_one,Int.natCast_zero,Int.zero_add]) hm
    exact stateExcept_bind_error_first _ _ s e hloop

abbrev batchRangeTail (l : DictLayout) (convert : β → Except Error α)
    (a : Nat) (lo hi : I) (ins : List β) (v : Nat) : MutationM α Nat := do
  let m := JInt.wrap .i64 (ins.length : Int)
  if m = zero then
    if ¬ (lo > hi) then vecDeleteat α (layout := MemoryLayoutMetadata.ofRuntime l) a lo (hi-lo+one)
    return v
  let n ← mutableLength a
  let d := hi-lo+one
  if m.val < d.val then
    let delta := d-m
    vecDeleteat α (layout := MemoryLayoutMetadata.ofRuntime l) a (if lo-one < n-hi then lo else hi-delta+one) delta
  else if m.val > d.val then
    growat (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure pure
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      a (if lo-one < n-hi then lo else hi+one) (m-d)
  batchSpliceFinish convert a lo ins v

private theorem batchSpliceFactor (l : DictLayout) (convert : β → Except Error α)
    (a : Nat) (lo hi : I) (ins : List β) :
    mutableSpliceRange (MemoryLayoutMetadata.ofRuntime l) convert a lo hi ins =
      (do let v ← batchRangeGet l a lo hi
          batchRangeTail l convert a lo hi ins v) := by
  by_cases he : lo > hi <;>
    simp only [mutableSpliceRange,spliceRange,batchRangeTail,batchSpliceFinish,batchRangeGet,
      deleteatRange,Bool.false_eq_true,ite_false,pure_bind,bind_assoc,decide_eq_true_eq,
      he,decide_true,decide_false,Bool.not_true,Bool.not_false,ite_true,
      not_true_eq_false,not_false_eq_true] <;> rfl

/-- The growth plan agrees even at the signed endpoint where `hi+1` wraps. -/
private theorem batchRangeGrowPlan (l : MemoryLayout) (s : MutableMemory α) (a mem : Nat)
    (off n : I) (slots : List (Option α)) (h : VecAt s a mem off n slots) (lo hi : I)
    (hr : lo.val ≤ hi.val+1) (hb : hi.val < lo.val ∨ 1 ≤ lo.val ∧ hi.val ≤ n.val)
    (count : Nat) :
    growatPlan l (geometryOf s a) (if lo-one < n-hi then lo else hi+one).val count =
      growatPlan l (geometryOf s a) (if lo.val-1 < n.val-hi.val then lo.val else hi.val+1) count := by
  have hnb := ival_bounds n
  have hlb := ival_bounds lo
  have hhb := ival_bounds hi
  have hn := h.2.2.2.1
  rcases hb with hempty|hb
  · have heq : lo.val = hi.val+1 := by omega
    have hhi : (hi+one).val = hi.val+1 := ival_add_one hi (by omega)
    have hEq : hi+one = lo := Subtype.ext (by rw [hhi,heq])
    simp only [hEq,ite_self,← heq]
  · have hL : (lo-one).val = lo.val-1 := ival_sub_one lo (by omega)
    have hR : (n-hi).val = n.val-hi.val := ival_sub _ _ (by omega)
    have hcond : (lo-one < n-hi) ↔ lo.val-1 < n.val-hi.val := by rw [jlt_iff,hL,hR]
    by_cases hc : lo.val-1 < n.val-hi.val
    · simp only [hcond,hc,ite_true]
    · simp only [hcond,hc,ite_false]
      by_cases hmax : hi.val < 9223372036854775807
      · rw [ival_add_one hi (by omega)]
      · have hh : hi.val = 9223372036854775807 := by omega
        have hN : n.val = 9223372036854775807 := by omega
        have hwrap : (hi+one).val = -9223372036854775808 := by
          change (JInt.wrap .i64 (hi.val+one.val)).val = _
          rw [hh,ival_one]
          unfold JInt.wrap
          rfl
        rw [hwrap,hh,opusGrowth.VecAt.geometry h]
        have hnt : n.val.toNat = typemaxNat := by rw [hN]; rfl
        simp only [growatPlan,hnt,show ¬(-9223372036854775808 : Int) = 1 by decide,
          show ¬(9223372036854775807+1 : Int) = 1 by decide,ite_false,
          Nat.lt_irrefl,false_and,show ¬ (1 < (-9223372036854775808 : Int) ∧
            (-9223372036854775808 : Int) ≤ (typemaxNat : Int)) by decide,
          show ¬ (1 < (9223372036854775807+1 : Int) ∧
            (9223372036854775807+1 : Int) ≤ (typemaxNat : Int)) by decide,
          not_false_eq_true,ite_true]




private theorem batchRangePositionBounds (n lo hi : I)
    (hr : lo.val ≤ hi.val+1) (hb : hi.val < lo.val ∨ 1 ≤ lo.val ∧ hi.val ≤ n.val)
    (hp : 1 ≤ (if lo-one < n-hi then lo else hi+one).val ∧
      (if lo-one < n-hi then lo else hi+one).val ≤ n.val+1) :
    1 ≤ lo.val ∧ hi.val ≤ n.val ∧
      lo.val ≤ (if lo-one < n-hi then lo else hi+one).val ∧
      (if lo-one < n-hi then lo else hi+one).val ≤ hi.val+1 := by
  have hlb := ival_bounds lo
  have hhb := ival_bounds hi
  rcases hb with he|hb
  · have heq : lo.val = hi.val+1 := by omega
    have hhi : (hi+one).val = hi.val+1 := ival_add_one hi (by omega)
    have hEq : hi+one = lo := Subtype.ext (by rw [hhi,heq])
    simp only [hEq,ite_self] at hp ⊢
    omega
  · refine ⟨hb.1,hb.2,?_⟩
    by_cases hc : lo-one < n-hi
    · simp only [hc,ite_true]
      omega
    · simp only [hc,ite_false] at hp ⊢
      have hmax : hi.val < 9223372036854775807 := by
        by_cases hh : hi.val = 9223372036854775807
        · have hw : (hi+one).val = -9223372036854775808 := by
            change (JInt.wrap .i64 (hi.val+one.val)).val = _
            rw [hh,ival_one]
            unfold JInt.wrap
            rfl
          rw [hw] at hp
          omega
        · omega
      rw [ival_add_one hi (by omega)]
      omega
end ChatGPTBatch1.Splice
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
namespace ChatGPTBatch1.Splice
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.opusGrowth JuliaLean.Proofs.base.int
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] JInt.wrap



open solArrayGrow


attribute [local irreducible] growat

private theorem batchRangeTailSpec {α β : Type} (l : DictLayout) (convert : β → Except Error α)
    (s : MutableMemory α) (a mem v vmem : Nat) (off n vo vn : I)
    (slots saved : List (Option α)) (h : VecAt s a mem off n slots)
    (hv : VecAt s v vmem vo vn saved) (hva : v ≠ a) (hvm : vmem ≠ mem)
    (hvmlt : vmem < s.memories.length) (lo hi : I) (ins : List β)
    (hr : lo.val ≤ hi.val+1) (hb : hi.val < lo.val ∨ 1 ≤ lo.val ∧ hi.val ≤ n.val)
    (hmax : ins.length ≤ typemaxNat) (hfit : memoryFits l (hi-lo+one).val.toNat) :
    let d := (hi-lo+one).val.toNat
    let pos := if lo.val-1 < n.val-hi.val then lo.val else hi.val+1
    let plan := if d < ins.length then growatPlan l (geometryOf s a) pos (ins.length-d)
      else .ok (geometryOf s a)
    (∀ e, plan = .error e → (batchRangeTail l convert a lo hi ins v).run s = (.error e,s)) ∧
    (∀ g, plan = .ok g →
      (∀ cs, ins.mapM convert = .ok cs → ∃ after,
        (batchRangeTail l convert a lo hi ins v).run s = (.ok v,after) ∧
        after.validVector a ∧ VecAt after v vmem vo vn saved ∧
        after.contents a = (s.contents a).take (lo.val-1).toNat ++ cs.map some ++
          (s.contents a).drop hi.val.toNat) ∧
      (∀ e, ins.mapM convert = .error e → ((batchRangeTail l convert a lo hi ins v).run s).1 = .error e)) := by
  dsimp only
  obtain ⟨hdv,hd0,hdn⟩ := batchRangeCount n lo hi h.2.2.2.1 hr hb
  have hnb := ival_bounds n
  have hhib := ival_bounds hi
  have hlob := ival_bounds lo
  have hn := h.2.2.2.1
  have hdmax : (hi-lo+one).val < 9223372036854775807 := by
    have := hfit.1
    unfold maxIntVal at this
    omega
  by_cases hnil : ins = []
  · subst ins
    simp only [List.length_nil,Nat.not_lt_zero,ite_false]
    have hzero : JInt.wrap .i64 (0 : Int) = zero := rfl
    have H : ∃ after,
        (batchRangeTail l convert a lo hi [] v).run s = (.ok v,after) ∧
        after.validVector a ∧ VecAt after v vmem vo vn saved ∧
        after.contents a = (s.contents a).take (lo.val-1).toNat ++ (s.contents a).drop hi.val.toNat := by
      by_cases hempty : hi.val < lo.val
      · have hp : (lo.val-1).toNat = hi.val.toNat := by omega
        refine ⟨s,?_,h.valid,hv,?_⟩
        · simp only [batchRangeTail,List.length_nil,Int.natCast_zero,hzero,ite_true,
            show lo > hi from hempty,not_true_eq_false,ite_false,stateExcept_pure]
        · rw [hp,List.take_append_drop]
      · have hin : 1 ≤ lo.val ∧ hi.val ≤ n.val := by rcases hb with hb|hb; omega; exact hb
        obtain ⟨after,hdel,ha,hcontent,harr,hmem,_,_,_⟩ := batchDeleteatWide (layout := MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h
          lo (hi-lo+one) hdmax hin.1 (by omega) hd0 (by rw [hdv]; omega)
        have hsaved := batchVecFrame hv (harr _ hva) (hmem _ hvmlt hvm)
        refine ⟨after,?_,ha,hsaved,?_⟩
        · simp only [batchRangeTail,List.length_nil,Int.natCast_zero,hzero,ite_true,
            show ¬lo > hi from hempty,not_false_eq_true,stateExcept_bind,hdel,stateExcept_pure]
        · rw [hcontent,← h.contents,hdv,show (lo.val-1+(hi.val-lo.val+1)).toNat = hi.val.toNat by omega]
    refine ⟨(fun e he => by cases he),fun g hg => ⟨fun cs hm => ?_,fun e hm => ?_⟩⟩
    · have hcs : cs = [] := by simpa only [List.mapM_nil,Pure.pure,Except.pure,Except.ok.injEq] using hm.symm
      subst cs
      simpa only [List.map_nil,List.append_nil] using H
    · simp only [List.mapM_nil,Pure.pure,Except.pure] at hm
      cases hm
  · have hins : 0 < ins.length := List.length_pos_iff.mpr hnil
    obtain ⟨m,hMdef⟩ : ∃ m : I, m = JInt.wrap .i64 (ins.length : Int) := ⟨_,rfl⟩
    obtain ⟨d,hDdef⟩ : ∃ d : I, d = hi-lo+one := ⟨_,rfl⟩
    have hM : m.val = ins.length := by rw [hMdef]; exact ival_wrap _ (by unfold typemaxNat at hmax; omega)
    have hD : d.val = hi.val-lo.val+1 := by rw [hDdef]; exact hdv
    have hD0 : 0 ≤ d.val := by rw [hDdef]; exact hd0
    have hDn : d.val ≤ n.val := by rw [hDdef]; exact hdn
    have hDmax : d.val < 9223372036854775807 := by rw [hDdef]; exact hdmax
    have hMb := ival_bounds m
    have hM0 : m ≠ zero := by intro hh; have := congrArg Subtype.val hh; rw [hM,ival_zero] at this; omega
    have hLen := mutableLength_run s a _ h.1
    by_cases hsmall : m.val < d.val
    · have hnGrow : ¬ d.val.toNat < ins.length := by omega
      simp only [show ¬ (hi-lo+one).val.toNat < ins.length from by rw [← hDdef]; exact hnGrow,ite_false]
      have hin : 1 ≤ lo.val ∧ hi.val ≤ n.val := by rcases hb with hb|hb; omega; exact hb
      obtain ⟨delta,hDeltaDef⟩ : ∃ delta : I, delta = d-m := ⟨_,rfl⟩
      have hdelta : delta.val = d.val-m.val := by rw [hDeltaDef]; exact ival_sub _ _ (by omega)
      have hdpos : 0 < delta.val := by rw [hdelta]; omega
      have hiDelta : (hi-delta).val = hi.val-delta.val := ival_sub _ _ (by rw [hdelta]; omega)
      have hEnd : (hi-delta+one).val = hi.val-delta.val+1 := by
        rw [ival_add_one _ (by rw [hiDelta,hdelta]; omega),hiDelta]
      obtain ⟨pos,hPosDef⟩ : ∃ pos : I, pos = (if lo-one < n-hi then lo else hi-delta+one) := ⟨_,rfl⟩
      have hpBounds : lo.val ≤ pos.val ∧ pos.val ≤ lo.val+m.val := by
        rw [hPosDef]
        split <;> (try rw [hEnd]) <;> omega
      obtain ⟨mid,hdel,ha,hcontent,harr,hmem,off',slots',hmid⟩ := batchDeleteatWide (layout := MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h
        pos delta (by rw [hdelta]; omega) (by omega) (by omega)
        (by omega) (by rw [hdelta]; omega)
      have hsaved := batchVecFrame hv (harr _ hva) (hmem _ hvmlt hvm)
      have hN : (n-delta).val = n.val-delta.val := ival_sub _ _ (by rw [hdelta]; omega)
      have hcap : lo.val-1+ins.length ≤ (n-delta).val := by rw [hN,hdelta]; omega
      have hcount : (pos.val-1+delta.val).toNat = (pos.val-1).toNat+delta.val.toNat := by omega
      obtain ⟨hpref,hsuff⟩ := batchDeletedEnds (s.contents a) (pos.val-1).toNat delta.val.toNat
        (lo.val-1).toNat ins.length (by have hh := vecAt_length_int h; omega) (by omega) (by omega)
      have hcontent' : mid.contents a = (s.contents a).take (pos.val-1).toNat ++
          (s.contents a).drop ((pos.val-1).toNat+delta.val.toNat) := by rw [hcontent,← h.contents,hcount]
      rw [← hcontent'] at hpref hsuff
      have hsuffix : (mid.contents a).drop (lo.val-1+ins.length).toNat = (s.contents a).drop hi.val.toNat := by
        simpa only [show (lo.val-1+ins.length).toNat = (lo.val-1).toNat+ins.length by omega,
          show (lo.val-1).toNat+ins.length+delta.val.toNat = hi.val.toNat by rw [hdelta]; omega] using hsuff
      have HF := batchSpliceFinishRun l convert mid a mem v vmem off' (n-delta) vo vn lo slots' saved
        hmid hsaved hvm ins hin.1 hcap
      refine ⟨(fun e he => by cases he),fun g hg => ⟨fun cs hm => ?_,fun e hm => ?_⟩⟩
      · obtain ⟨after,hfinish,hva',hvv,hcontents⟩ := HF.1 cs hm
        refine ⟨after,?_,hva',hvv,?_⟩
        · simpa only [batchRangeTail,← hMdef,hM0,ite_false,
            stateExcept_bind,hLen,stateExcept_pure,← hDdef,hsmall,ite_true,
            ← hDeltaDef,← hPosDef,hdel] using hfinish
        · rw [hcontents,hpref,hsuffix]
      · have herr := HF.2 e hm
        simpa only [batchRangeTail,← hMdef,hM0,ite_false,
          stateExcept_bind,hLen,stateExcept_pure,← hDdef,hsmall,ite_true,
          ← hDeltaDef,← hPosDef,hdel] using herr
    · by_cases hlarge : d.val < m.val
      · have hgrow : d.val.toNat < ins.length := by omega
        simp only [show (hi-lo+one).val.toNat < ins.length from by rw [← hDdef]; exact hgrow,ite_true]
        obtain ⟨delta,hDeltaDef⟩ : ∃ delta : I, delta = m-d := ⟨_,rfl⟩
        obtain ⟨pos,hPosDef⟩ : ∃ pos : I, pos = (if lo-one < n-hi then lo else hi+one) := ⟨_,rfl⟩
        have hdelta : delta.val = m.val-d.val := by rw [hDeltaDef]; exact ival_sub _ _ (by omega)
        have hdelta0 : 0 ≤ delta.val := by rw [hdelta]; omega
        have hdnat : delta.val.toNat = ins.length-d.val.toNat := by rw [hdelta]; omega
        have hPlan := batchRangeGrowPlan l s a mem off n slots h lo hi hr hb delta.val.toNat
        have HG := growat_plan_native l s a mem off n slots h pos delta hdelta0
        have hPE : growatPlan l (geometryOf s a) pos.val delta.val.toNat =
            growatPlan l (geometryOf s a) (if lo.val-1 < n.val-hi.val then lo.val else hi.val+1)
              (ins.length-(hi-lo+one).val.toNat) := by
          rw [hPosDef,hPlan,hdnat,hDdef]
        refine ⟨fun e he => ?_,fun g hg => ?_⟩
        · have hge := HG.1 e (hPE.trans he)
          simp only [batchRangeTail,← hMdef,hM0,ite_false,
            stateExcept_bind,hLen,stateExcept_pure,← hDdef,hsmall,hlarge,ite_true,
            ← hDeltaDef,← hPosDef,hge]
        · have hgp := hPE.trans hg
          obtain ⟨result,mid,hgrowRun,hvalid,hlen,hpre,hsuf,harr,hmem⟩ := HG.2 g hgp
          cases result
          obtain ⟨mem',off',slots',hmid,hmemid⟩ := batchGrowatMemory l s a mem off n slots h pos delta
            hdelta0 g hgp mid hgrowRun
          have hsaved := batchVecFrame hv (harr _ hva) (hmem _ hvmlt hvm)
          have hsep : vmem ≠ mem' := by rcases hmemid with hh|hh <;> rw [hh]; exact hvm; omega
          have hpidx := growatPlan_ok_index l (geometryOf s a) pos.val delta.val.toNat g hgp
          rw [opusGrowth.VecAt.geometry h] at hpidx
          obtain ⟨hlo,hhi,hpLo,hpHi⟩ := batchRangePositionBounds n lo hi hr hb
            (by rw [← hPosDef]; exact ⟨hpidx.1,by simpa only [Int.toNat_of_nonneg hn] using hpidx.2⟩)
          rw [← hPosDef] at hpLo hpHi
          have hN : (n+delta).val = n.val+delta.val := by
            rw [vecAt_length_int hmid,vecAt_length_int h] at hlen
            exact hlen
          have hcap : lo.val-1+ins.length ≤ (n+delta).val := by rw [hN,hdelta]; omega
          have hpD : (pos.val-1+delta.val).toNat = (pos.val-1).toNat+delta.val.toNat := by omega
          rw [hpD] at hsuf
          obtain ⟨hpref,hsuff⟩ := batchGrownEnds (s.contents a) (mid.contents a) (pos.val-1).toNat
            delta.val.toNat (lo.val-1).toNat hi.val.toNat (by omega) (by omega) hpre hsuf
          have hsuffix : (mid.contents a).drop (lo.val-1+ins.length).toNat = (s.contents a).drop hi.val.toNat := by
            simpa only [show (lo.val-1+ins.length).toNat = hi.val.toNat+delta.val.toNat by rw [hdelta]; omega] using hsuff
          have HF := batchSpliceFinishRun l convert mid a mem' v vmem off' (n+delta) vo vn lo slots' saved
            hmid hsaved hsep ins hlo hcap
          refine ⟨fun cs hm => ?_,fun e hm => ?_⟩
          · obtain ⟨after,hfinish,hva',hvv,hcontents⟩ := HF.1 cs hm
            refine ⟨after,?_,hva',hvv,?_⟩
            · simpa only [batchRangeTail,← hMdef,hM0,ite_false,
                stateExcept_bind,hLen,stateExcept_pure,← hDdef,hsmall,hlarge,ite_true,
                ← hDeltaDef,← hPosDef,hgrowRun] using hfinish
            · rw [hcontents,hpref,hsuffix]
          · have herr := HF.2 e hm
            simpa only [batchRangeTail,← hMdef,hM0,ite_false,
              stateExcept_bind,hLen,stateExcept_pure,← hDdef,hsmall,hlarge,ite_true,
              ← hDeltaDef,← hPosDef,hgrowRun] using herr
      · have hequal : m.val = d.val := by omega
        have hnGrow : ¬ d.val.toNat < ins.length := by omega
        simp only [show ¬ (hi-lo+one).val.toNat < ins.length from by rw [← hDdef]; exact hnGrow,ite_false]
        have hin : 1 ≤ lo.val ∧ hi.val ≤ n.val := by rcases hb with hb|hb; omega; exact hb
        have hcap : lo.val-1+ins.length ≤ n.val := by omega
        have hsuffix : (lo.val-1+ins.length).toNat = hi.val.toNat := by omega
        have HF := batchSpliceFinishRun l convert s a mem v vmem off n vo vn lo slots saved
          h hv hvm ins hin.1 hcap
        refine ⟨(fun e he => by cases he),fun g hg => ⟨fun cs hm => ?_,fun e hm => ?_⟩⟩
        · obtain ⟨after,hfinish,hva',hvv,hcontents⟩ := HF.1 cs hm
          refine ⟨after,?_,hva',hvv,?_⟩
          · simpa only [batchRangeTail,← hMdef,hM0,ite_false,
              stateExcept_bind,hLen,stateExcept_pure,← hDdef,hsmall,hlarge,ite_false] using hfinish
          · rwa [hsuffix] at hcontents
        · have herr := HF.2 e hm
          simpa only [batchRangeTail,← hMdef,hM0,ite_false,
            stateExcept_bind,hLen,stateExcept_pure,← hDdef,hsmall,hlarge,ite_false] using herr




/-- The frozen range-splice contract, including extraction allocation, growth failures,
conversion failures, both movement directions, empty ranges, and signed endpoints. -/
theorem MultidimcovArrayV2SpliceRange_proven : SpliceRangeSpec := by
  intro α β l convert s a lo hi ins hvalid hr hmax
  dsimp only
  obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
  have hlen := vecAt_length_int h
  refine ⟨batchSpliceOutside l convert s a lo hi ins hvalid,?_⟩
  intro hb
  have hbounds : hi.val < lo.val ∨ 1 ≤ lo.val ∧ hi.val ≤ n.val := by
    simpa only [hlen] using hb
  obtain ⟨hdv,hd0,hdn⟩ := batchRangeCount n lo hi h.2.2.2.1 hr hbounds
  have HG := batchRangeGetRun l s a mem off n slots h lo hi hr hbounds
  dsimp only at HG
  rw [hdv] at HG
  refine ⟨fun hnf => ?_,fun hfit => ?_⟩
  · have he := HG.1 hnf
    rw [batchSpliceFactor]
    simp only [stateExcept_bind,he]
  · obtain ⟨mid,hget,ha,hv,hvcontent,hmLen⟩ := HG.2 hfit
    have hSource : mid.contents a = s.contents a := ha.contents.trans h.contents.symm
    have hGeo : geometryOf mid a = geometryOf s a := by rw [opusGrowth.VecAt.geometry ha,opusGrowth.VecAt.geometry h]
    have hm : mem < s.memories.length := (List.getElem?_eq_some_iff.mp h.2.1).choose
    have hA : a < s.arrays.length := (List.getElem?_eq_some_iff.mp h.1).choose
    have hfit' : memoryFits l (hi-lo+one).val.toNat := by rwa [hdv]
    have HT := batchRangeTailSpec l convert mid a mem s.arrays.length s.memories.length off n one
      (hi-lo+one) slots (((s.contents a).drop (lo.val-1).toNat).take (hi.val-lo.val+1).toNat)
      ha hv (by omega) (by omega) (by rw [hmLen]; omega) lo hi ins hr hbounds hmax hfit'
    dsimp only at HT
    rw [hdv,hGeo,← hlen] at HT
    have hrun : (mutableSpliceRange (MemoryLayoutMetadata.ofRuntime l) convert a lo hi ins).run s =
        (batchRangeTail l convert a lo hi ins s.arrays.length).run mid := by
      rw [batchSpliceFactor]
      simp only [stateExcept_bind,hget]
    refine ⟨fun e he => ?_,fun g hg => ⟨fun cs hc => ?_,fun e hc => ?_⟩⟩
    · have he' := HT.1 e he
      rw [hrun,he']
      exact ⟨rfl,hSource⟩
    · obtain ⟨after,hafter,hva,hvv,hcontents⟩ := (HT.2 g hg).1 cs hc
      refine ⟨after,s.arrays.length,hrun.trans hafter,hva,hvv.valid,?_,?_⟩
      · exact hvv.contents.trans (hv.contents.symm.trans hvcontent)
      · rwa [hSource] at hcontents
    · rw [hrun]
      exact (HT.2 g hg).2 e hc
end ChatGPTBatch1.Splice
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
section MaskProofs

variable {α : Type}

attribute [local irreducible] JInt.wrap wrapInt

/-- Copying a visible slot agrees with its logical value when an unassigned source
has a layout for which unsetting clears the destination. -/
theorem mask_copy_slot (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (handle mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s handle mem off n slots) (p q : I)
    (hp : 1 ≤ p.val ∧ p.val ≤ n.val) (hq : 1 ≤ q.val ∧ q.val ≤ n.val)
    (value : Option α) (hv : (vwWindow slots off n)[(q.val - 1).toNat]? = some value)
    (hclear : value = none → unsetClears layout.runtime = true) :
    ∃ slots', (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
        handle p q).run s = (.ok (), {s with memories := s.memories.set mem slots'}) ∧
      VecAt {s with memories := s.memories.set mem slots'} handle mem off n slots' ∧
      vwWindow slots' off n = (vwWindow slots off n).set (p.val - 1).toNat value := by
  obtain ⟨slots', hr, hnext, hc⟩ :=
    vwCopyItem_run (unsetRuntime := layout.runtime) s handle mem off n slots h p q hp hq
  refine ⟨slots', hr, hnext, ?_⟩
  rw [hv] at hc
  cases value with
  | some x => exact hc
  | none =>
    simpa only [Option.join_some, expectedUnset, hclear rfl, ite_true] using hc

/-- One iteration of deleteat!'s Boolean-mask loop. The copy takes place for both
mask values; a discarded value is copied just beyond the already-kept prefix. -/
theorem mask_step (layout : MemoryLayoutMetadata) (handle mem : Nat) (off n : I)
    (w0 : List (Option α)) (mask : List Bool) (k : Nat) (pq : I × I)
    (st : MutableMemory α) (b : Bool) (value : Option α)
    (hsmall : n.val < 9223372036854775806) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots layout.runtime w0)
    (hw : w0[k]? = some value) (hm : mask[k]? = some b)
    (hinv : MaskInv handle mem off n w0 mask k pq st) :
    ∃ st', (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
        handle pq.1 pq.2).run st = (.ok (), st') ∧
      MaskInv handle mem off n w0 mask (k + 1)
        (pq.1 + (if !b then one else zero), pq.2 + one) st' := by
  obtain ⟨sl, hv, hq, hp, htake, hdrop⟩ := hinv
  have hn0 := hv.2.2.2.1
  have hk : k < w0.length := (List.getElem?_eq_some_iff.mp hw).choose
  have hkept := keptPrefix_length_le w0 mask k
  have hwl := vwWindow_length hv
  have hpq : 1 ≤ pq.1.val ∧ pq.1.val ≤ n.val := by omega
  have hqq : 1 ≤ pq.2.val ∧ pq.2.val ≤ n.val := by omega
  have hqidx : (pq.2.val - 1).toNat = k := by omega
  have hpidx : (pq.1.val - 1).toNat = (keptPrefix w0 mask k).length := by omega
  have hsrc : (vwWindow sl off n)[(pq.2.val - 1).toNat]? = some value := by
    have hd := congrArg (fun xs => xs[0]?) hdrop
    simp only [List.getElem?_drop, Nat.add_zero] at hd
    rw [hqidx, hd, hw]
  have hclear : value = none → unsetClears layout.runtime = true := by
    intro hnone
    cases huc : unsetClears layout.runtime with
    | true => rfl
    | false =>
      have ha := hvalid huc k hk
      rw [hw, hnone] at ha
      cases ha
  obtain ⟨sl', hcopy, hv', hc⟩ :=
    mask_copy_slot layout st handle mem off n sl hv pq.1 pq.2 hpq hqq value hsrc hclear
  rw [hpidx] at hc
  refine ⟨{st with memories := st.memories.set mem sl'}, hcopy, sl', hv', ?_, ?_, ?_, ?_⟩
  · rw [ival_add_one pq.2 (by omega), hq]
    omega
  · have hsucc := keptPrefix_succ w0 mask k value b hw hm
    cases b with
    | false =>
      simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false] at hsucc ⊢
      rw [ival_add_one pq.1 (by omega), hsucc]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
        List.append_nil] at hsucc ⊢
      rw [ival_add pq.1 zero (by rw [ival_zero]; omega), ival_zero, hsucc]
      omega
  · have hsucc := keptPrefix_succ w0 mask k value b hw hm
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hsucc
      rw [hsucc]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      rw [hc, list_set_take_succ _ _ _ (by omega), htake]
    | true =>
      simp only [ite_true, List.append_nil] at hsucc
      rw [hsucc, hc, list_set_take_self, htake]
  · rw [hc, list_set_drop_of_lt _ _ _ _ (by omega)]
    exact drop_succ_of_drop_eq _ _ k hdrop

/-- The complete mask loop preserves the compacted prefix and untouched suffix. -/
theorem mask_loop (layout : MemoryLayoutMetadata) (handle mem : Nat) (off n : I)
    (w0 : List (Option α)) (mask : List Bool)
    (hsmall : n.val < 2 ^ 62) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots layout.runtime w0) (hmlen : mask.length = w0.length) :
    ∀ (rest : List Bool) (k : Nat) (pq : I × I) (st : MutableMemory α),
      mask.drop k = rest → MaskInv handle mem off n w0 mask k pq st →
      ∃ pq' st',
        (forIn (m := MutationM α) rest pq (fun b pq => do
          copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
            handle pq.1 pq.2
          pure (ForInStep.yield
            (pq.1 + (if !b then one else zero), pq.2 + one)))).run st = (.ok pq', st') ∧
        MaskInv handle mem off n w0 mask (k + rest.length) pq' st' := by
  intro rest
  induction rest with
  | nil =>
    intro k pq st _ hinv
    exact ⟨pq, st, rfl, by simpa only [List.length_nil, Nat.add_zero] using hinv⟩
  | cons b rest ih =>
    intro k pq st hrest hinv
    have hlength := congrArg List.length hrest
    simp only [List.length_drop, List.length_cons] at hlength
    have hk : k < w0.length := by omega
    have hm : mask[k]? = some b := by
      have hhead := congrArg (fun xs => xs[0]?) hrest
      simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using hhead
    obtain ⟨st1, hcopy, hinv1⟩ :=
      mask_step layout handle mem off n w0 mask k pq st b w0[k] (by omega) hwlen hvalid
        (List.getElem?_eq_getElem hk) hm hinv
    have htail : mask.drop (k + 1) = rest := by
      rw [← List.drop_drop, hrest]
      rfl
    obtain ⟨pq', st', hrun, hfinal⟩ :=
      ih (k + 1) (pq.1 + (if !b then one else zero), pq.2 + one) st1 htail hinv1
    refine ⟨pq', st', ?_, ?_⟩
    · simp only [List.forIn_cons, stateExcept_bind, hcopy, stateExcept_pure]
      exact hrun
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal
end MaskProofs
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

theorem MultidimcovArrayV2DeleteatMask_proven :
    JuliaLean.Proofs.base.array.DeleteatMaskSpec := by
  intro α layout s handle mask hvalid hslots
  dsimp only
  intro hsmall
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  have hn0 := h.2.2.2.1
  have hwl := vwWindow_length h
  have hwlen : (s.contents handle).length = n.val.toNat := by rw [h.contents, hwl]
  have hlen : ((s.contents handle).length : Int) = n.val := by rw [hwlen]; omega
  have hsmalln : n.val < 2 ^ 62 := by omega
  have hlength := mutableLength_run s handle _ h.1
  constructor
  · intro hne
    have hbad : ((mask.length : Int) != n.val) = true := by
      simp only [bne_iff_ne]
      omega
    simp only [deleteatMask, stateExcept_bind, hlength, hbad, ite_true, stateExcept_throw]
  · intro heq
    have hbad : ((mask.length : Int) != n.val) = false := by
      have heq' : (mask.length : Int) = n.val := by omega
      rw [heq']
      exact bne_self_eq_false n.val
    have hstart : MaskInv handle mem off n (s.contents handle) mask 0 (one, one) s := by
      refine ⟨slots, h, ?_, ?_, ?_, ?_⟩
      · simp only [ival_one, Int.natCast_zero, Int.zero_add]
      · simp only [keptPrefix, List.take_zero, List.filter_nil, List.map_nil, List.length_nil,
          Int.natCast_zero, Int.zero_add, ival_one]
      · simp only [keptPrefix, List.take_zero, List.filter_nil, List.map_nil, List.length_nil]
      · simpa only [List.drop_zero] using h.contents.symm
    obtain ⟨pq, st, hloop, hinv⟩ := mask_loop layout handle mem off n (s.contents handle) mask
      hsmalln hwlen hslots heq mask 0 (one, one) s rfl hstart
    simp only [Nat.zero_add] at hinv
    obtain ⟨slots1, hv1, hq, hp, htake, hdrop⟩ := hinv
    have hkept := keptPrefix_length_le (s.contents handle) mask mask.length
    let d := n - pq.1 + one
    have hsub : (n - pq.1).val = n.val - pq.1.val := ival_sub _ _ (by omega)
    have hd : d.val = n.val - (keptPrefix (s.contents handle) mask mask.length).length := by
      dsimp only [d]
      rw [ival_add (n - pq.1) one (by rw [hsub, ival_one]; omega), hsub, ival_one]
      omega
    obtain ⟨next, slots2, hdel, hv2, _, _, hc⟩ :=
      vwDeleteend_run (layout := layout) st handle mem off n slots1 hv1 d
        (by rw [hd]; omega) (by rw [hd]; omega) (by rw [hd]; omega)
    dsimp only [d] at hdel
    refine ⟨next, ?_, hv2.valid, ?_⟩
    · simp only [deleteatMask, stateExcept_bind, hlength, hbad, Bool.false_eq_true,
        ite_false, hloop, hdel, stateExcept_pure]
    · rw [hv2.contents, hc]
      have hnat : (n.val - d.val).toNat =
          (keptPrefix (s.contents handle) mask mask.length).length := by rw [hd]; omega
      rw [hnat, htake, keptPrefix_full]

theorem ArrayopsDeleteatMask_proven : JuliaLean.Proofs.base.array.DeleteatMaskSpec :=
  MultidimcovArrayV2DeleteatMask_proven
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Partial target 44: the list deletion entry point rejects a first out-of-bounds index. -/
theorem deleteatListFirstInvalid {α : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (a : Nat) (i : I) (post : List I)
    (hvalid : s.validVector a)
    (hbad : ¬(1 ≤ i.val ∧ i.val ≤ ((s.contents a).length : Int))) :
    ((mutableDeleteatList layout a (i :: post)).run s).1 = .error .bounds := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvalid
  have hlen : ((s.contents a).length : Int) = n.val := by
    rw [hv.contents, vwWindow_length hv]
    have hn0 := hv.2.2.2.1
    omega
  rw [opusGrowth.deleteatList_eq]
  exact opusGrowth.deleteIter_err0 s a mem off n slots hv i post
    (by simpa only [hlen] using hbad)

/-- Partial target 44: the vector-of-indices overload has the same first-index error. -/
theorem deleteatVectorFirstInvalid {α : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (a : Nat) (i : I) (post : List I)
    (hvalid : s.validVector a)
    (hbad : ¬(1 ≤ i.val ∧ i.val ≤ ((s.contents a).length : Int))) :
    ((mutableDeleteatVector layout a (i :: post)).run s).1 = .error .bounds := by
  rw [opusGrowth.deleteatVector_run]
  exact deleteatListFirstInvalid layout s a i post hvalid hbad

/-- Curried filtering constructs a first-argument closure and calls that closure directly. -/
theorem ArrayFilterCurried_proven :
    JuliaLean.Proofs.base.array.round4.FilterCurriedSpec := by
  intro F A B σ τ showInt typeName stableTypeFunction stableTypeValue filter f x
  exact ⟨⟨(fun g a _ => filter g a), f⟩, rfl, rfl⟩
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A one-based cursor immediately after a prefix. -/
def prefixCursor (n : Nat) : I := JInt.wrap .i64 ((n : Int) + 1)

theorem prefixCursor_next (n : Nat) (hn : n < 2 ^ 62) :
    prefixCursor n + one = prefixCursor (n + 1) := by
  apply Subtype.ext
  have hc : (prefixCursor n).val = (n : Int) + 1 := ival_wrap _ (by omega)
  rw [ival_add _ _ (by rw [hc, ival_one]; omega), hc, ival_one]
  rw [show (prefixCursor (n + 1)).val = ((n + 1 : Nat) : Int) + 1 from
    ival_wrap _ (by omega)]
  omega

/-- The generated one-dimensional gather loop used by range indexing. -/
def gatherRangeValues (D : List I) (r : I × I) (ks : List I) (dest : Nat × Nat) (j : I) :
    VectorM I (Nat × Nat) :=
  JuliaLean.base.multidimensional.gatherLoop D
    (fun _ (s : I) => pure (s + one, s + one))
    (fun (r : I × I) (is : List I) => pure (r.1 + (is.headD one - one)))
    (fun (d : Nat × Nat) (v : I) (k : I) => do heapSet d.1 v k; pure d)
    r (ks.map (fun k => [k])) dest (j, j)

/-- A gather fills the unprocessed suffix in order while keeping every old heap object. -/
theorem gatherRangeValues_run (D : List I) (r : I × I) (ks : List I) (heap : VectorHeap I)
    (n : Nat) : ∀ (pre : List I) (tail : List (Option I)),
    ks.length = tail.length → pre.length + tail.length < 2 ^ 62 →
    (gatherRangeValues D r ks (heap.length, n) (prefixCursor pre.length)).run
      (heap ++ [pre.map some ++ tail]) =
      .ok ((heap.length, n), heap ++ [(pre ++ ks.map (fun k => r.1 + (k - one))).map some]) := by
  induction ks with
  | nil =>
    intro pre tail hlen _
    have ht : tail = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst tail
    simp only [gatherRangeValues, List.map_nil,
      JuliaLean.base.multidimensional.gatherLoop, vector_pure_run, List.append_nil]
  | cons k ks ih =>
    intro pre tail hlen hsmall
    cases tail with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons old tail =>
      let value := r.1 + (k - one)
      have hstore := ChatGPTBatch1.ArrayFilter.batch1_filterStore heap pre old tail value hsmall
      change (heapSet heap.length value (prefixCursor pre.length)).run
          (heap ++ [pre.map some ++ old :: tail]) =
        .ok ((), heap ++ [pre.map some ++ some value :: tail]) at hstore
      have hc : prefixCursor pre.length + one = prefixCursor (pre ++ [value]).length := by
        rw [List.length_append, List.length_singleton]
        exact prefixCursor_next pre.length (by omega)
      have hslots : pre.map some ++ some value :: tail = (pre ++ [value]).map some ++ tail := by
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append]
      have hstep : gatherRangeValues D r (k :: ks) (heap.length, n)
          (prefixCursor pre.length) = (do
            heapSet heap.length value (prefixCursor pre.length)
            gatherRangeValues D r ks (heap.length, n) (prefixCursor pre.length + one)) := by
        simp only [gatherRangeValues, List.map_cons,
          JuliaLean.base.multidimensional.gatherLoop, List.headD_cons, pure_bind, bind_assoc]
        rfl
      rw [hstep, vector_bind_run, hstore]
      rw [hc, hslots]
      have htlen : ks.length = tail.length := by
        simp only [List.length_cons] at hlen
        omega
      have htbound : (pre ++ [value]).length + tail.length < 2 ^ 62 := by
        simp only [List.length_append, List.length_singleton, List.length_cons,
          List.length_nil] at hsmall ⊢
        omega
      simpa only [List.map_cons, List.append_assoc, List.singleton_append] using
        (ih (pre ++ [value]) tail htlen htbound)

/-- Bounds checks made before gathering a vector of range indices. -/
def rangeKeysCheck (r : I × I) (ks : List I) : VectorM I Unit :=
  forIn ks () fun k _ =>
    if !(1 ≤ k.val ∧ k.val ≤ (round4.unitRangeLength r).val) then do
      throw .bounds
      pure (.yield ())
    else pure (.yield ())

theorem rangeKeysCheck_eq (r : I × I) (ks : List I)
    (hks : ∀ k ∈ ks, 1 ≤ k.val ∧ k.val ≤ (round4.unitRangeLength r).val) :
    rangeKeysCheck r ks = pure () := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have hk := hks k (List.mem_cons_self ..)
    have ht := ih (fun j hj => hks j (List.mem_cons_of_mem k hj))
    unfold rangeKeysCheck
    rw [List.forIn_cons]
    simp only [hk, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, pure_bind]
    exact ht

/-- A range gathered at valid indices allocates exactly its selected values. -/
theorem rangeGetIndices_run (r : I × I) (ks : List I) (heap : VectorHeap I)
    (hn : ks.length < 2 ^ 62)
    (hks : ∀ k ∈ ks, 1 ≤ k.val ∧ k.val ≤ (round4.unitRangeLength r).val) :
    (round4.rangeGetIndices r ks).run heap =
      .ok ((heap.length, ks.length),
        heap ++ [(ks.map (fun k => r.1 + (k - one))).map some]) := by
  have hc := rangeKeysCheck_eq r ks hks
  have hint : (JuliaLean.base.multidimensional.int 1).val.toNat = 1 := by decide
  have houter : (do
      for is in [ks] do
        for k in is do
          if !(1 ≤ k.val ∧ k.val ≤ (round4.unitRangeLength r).val) then throw .bounds
        : VectorM I Unit) = pure () := by
    simp only [List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]
    change (do rangeKeysCheck r ks; pure ()) = pure ()
    rw [hc, pure_bind]
  simp only [round4.rangeGetIndices, JuliaLean.base.multidimensional.getindexAbstract,
    houter, pure_bind, JuliaLean.base.multidimensional.maybeReshapeLinear,
    JuliaLean.base.multidimensional.unsafeGetindex, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Nat.mul_one, vector_bind_run, heapAllocate_run,
    vector_pure_run]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, pure_bind,
    JuliaLean.base.multidimensional.unsafeGetindexBangOne,
    JuliaLean.base.multidimensional.generateUnsafeGetindexBody,
    hint, JuliaLean.base.multidimensional.takeN,
    JuliaLean.base.multidimensional.columnMajor, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, pure_bind, vector_pure_run]
  change (gatherRangeValues (intRange one (JInt.wrap .i64 ks.length)) r ks
      (heap.length, ks.length) one).run (heap ++ [List.replicate ks.length none]) = _
  simpa only [List.length_nil, List.map_nil, List.nil_append, List.length_replicate,
    Nat.zero_add, prefixCursor, Int.natCast_zero, Int.zero_add, one] using
    (gatherRangeValues_run (intRange one (JInt.wrap .i64 ks.length)) r ks heap ks.length
      [] (List.replicate ks.length none) (by rw [List.length_replicate])
      (by simpa only [List.length_nil, List.length_replicate, Nat.zero_add] using hn))

/-- Range lengths agree with their nonnegative mathematical counts below the size bound. -/
theorem filterRangeLength_value (lo hi : I) (hn : hi.val - lo.val + 1 < 2 ^ 62) :
    (round4.unitRangeLength (lo, hi)).val = ((hi.val - lo.val + 1).toNat : Int) := by
  have hlo := ival_bounds lo
  have hhi := ival_bounds hi
  change (if hi.val < lo.val then zero else hi - lo + one).val = _
  by_cases h : hi.val < lo.val
  · rw [if_pos h, ival_zero]
    omega
  · have hd : (hi - lo).val = hi.val - lo.val := ival_sub _ _ (by omega)
    rw [if_neg h,
      ival_add _ _ (by rw [hd, ival_one]; omega), hd, ival_one]
    omega

/-- The one-based range keys have exactly the range's mathematical length. -/
theorem filterRangeKeys_length (lo hi : I) (hn : hi.val - lo.val + 1 < 2 ^ 62) :
    (intRange one (round4.unitRangeLength (lo, hi))).length =
      (hi.val - lo.val + 1).toNat := by
  simp only [intRange, List.length_map, List.length_range, ival_one]
  rw [filterRangeLength_value lo hi hn]
  omega

/-- Selecting each range key yields the range values in order. -/
theorem filterRangeKeys_values (lo hi : I) (hn : hi.val - lo.val + 1 < 2 ^ 62) :
    (intRange one (round4.unitRangeLength (lo, hi))).map (fun k => lo + (k - one)) =
      intRange lo hi := by
  have hsize := filterRangeLength_value lo hi hn
  have hcount : ((round4.unitRangeLength (lo, hi)).val - one.val + 1).toNat =
      (hi.val - lo.val + 1).toNat := by rw [hsize, ival_one]; omega
  simp only [intRange, hcount, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  have hlo := ival_bounds lo
  have hhi := ival_bounds hi
  have hj : (JInt.wrap .i64 (one.val + (k : Int))).val = (k : Int) + 1 := by
    rw [ival_wrap _ (by rw [ival_one]; omega), ival_one]
    omega
  have hm : (JInt.wrap .i64 (one.val + (k : Int)) - one).val = (k : Int) := by
    rw [ival_sub _ _ (by rw [hj, ival_one]; omega), hj, ival_one]
    omega
  apply Subtype.ext
  change (lo + (JInt.wrap .i64 (one.val + (k : Int)) - one)).val =
    (JInt.wrap .i64 (lo.val + (k : Int))).val
  rw [ival_add _ _ (by rw [hm]; omega), hm, ival_wrap _ (by omega)]

/-- Every enumerated range key is a valid one-based position. -/
theorem filterRangeKeys_bounds (lo hi : I) (hn : hi.val - lo.val + 1 < 2 ^ 62) :
    ∀ k ∈ intRange one (round4.unitRangeLength (lo, hi)),
      1 ≤ k.val ∧ k.val ≤ (round4.unitRangeLength (lo, hi)).val := by
  intro k hk
  simp only [intRange, List.mem_map, List.mem_range] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hsize := filterRangeLength_value lo hi hn
  have hv : (JInt.wrap .i64 (one.val + (j : Int))).val = 1 + j := by
    rw [ival_wrap _ (by rw [ival_one] at *; omega), ival_one]
  rw [hv, hsize]
  rw [hsize, ival_one] at hj
  constructor <;> omega

/-- The range filter's index buffer phase, followed by gathering and releasing that buffer. -/
def rangeFilterKeys (f : I → Except Error (Option Bool)) (r : I × I) (keys : List I) :
    VectorM I (Nat × Nat) := do
  let b ← heapAllocate (α := I) keys.length
  let j ← forIn (keys.map some) one
    (ChatGPTBatch1.ArrayFilter.batch1_filterStep (fun k => f (r.1 + (k - one))) b)
  modify (fun heap => heap.set b ((heap[b]?.getD []).take (j - one).val.toNat))
  let slots ← heapSlots b
  let result ← round4.rangeGetIndices r (slots.filterMap id)
  modify (fun heap => heap.set b [])
  pure result

theorem rangeFilter_eq_keys (f : I → Except Error (Option Bool)) (lo hi : I)
    (hn : hi.val - lo.val + 1 < 2 ^ 62) :
    round4.rangeFilter f (lo, hi) =
      rangeFilterKeys f (lo, hi) (intRange one (round4.unitRangeLength (lo, hi))) := by
  have hlen : (round4.unitRangeLength (lo, hi)).val.toNat =
      (intRange one (round4.unitRangeLength (lo, hi))).length := by
    rw [filterRangeLength_value lo hi hn, filterRangeKeys_length lo hi hn,
      Int.toNat_natCast]
  simp only [round4.rangeFilter, filterAbstractArray, rangeFilterKeys, pure_bind,
    Bool.not_true, Bool.false_eq_true, ite_false, hlen, List.forIn_map,
    ChatGPTBatch1.ArrayFilter.batch1_filterStep, bind_assoc]
  rfl

/-- First predicate errors are preserved by the index-buffer phase. -/
theorem rangeFilterKeys_error (f : I → Except Error (Option Bool)) (r : I × I)
    (keys : List I) (heap : VectorHeap I) (hn : keys.length < 2 ^ 62) (e : Error)
    (he : keys.mapM (fun k => boolResult f (r.1 + (k - one))) = .error e) :
    (rangeFilterKeys f r keys).run heap = .error e := by
  let g := fun k => f (r.1 + (k - one))
  have hs : (keys.map some).mapM (ChatGPTBatch1.ArrayFilter.batch1_slotBool g) =
      .error e := by
    simpa only [List.mapM_map, Function.comp_def,
      ChatGPTBatch1.ArrayFilter.batch1_slotBool, g, boolResult] using he
  have hk := ChatGPTBatch1.ArrayFilter.batch1_keepSlots_error g (keys.map some) e hs
  have hloop := ChatGPTBatch1.ArrayFilter.batch1_filterLoop g heap (keys.map some) []
    (List.replicate keys.length none)
    (by simp only [List.length_map, List.length_replicate]; omega)
    (by simpa only [List.length_nil, Nat.zero_add, List.length_replicate] using hn)
  simp only [hk, List.length_nil, Int.natCast_zero, Int.zero_add, List.map_nil,
    List.nil_append] at hloop
  change (forIn (keys.map some) one
      (ChatGPTBatch1.ArrayFilter.batch1_filterStep
        (fun k => f (r.1 + (k - one))) heap.length)).run
      (heap ++ [List.replicate keys.length none]) = .error e at hloop
  simp only [rangeFilterKeys, vector_bind_run, heapAllocate_run]
  rw [hloop]

/-- The successful index-buffer phase gathers precisely its retained indices. -/
theorem rangeFilterKeys_success (f : I → Except Error (Option Bool)) (r : I × I)
    (keys : List I) (heap : VectorHeap I) (hn : keys.length < 2 ^ 62)
    (hkeys : ∀ k ∈ keys, 1 ≤ k.val ∧ k.val ≤ (round4.unitRangeLength r).val)
    (bs : List Bool)
    (hb : keys.mapM (fun k => boolResult f (r.1 + (k - one))) = .ok bs) :
    let kept := ((keys.zip bs).filter (·.2)).map Prod.fst
    (rangeFilterKeys f r keys).run heap =
      .ok ((heap.length + 1, kept.length),
        heap ++ [[], (kept.map (fun k => r.1 + (k - one))).map some]) := by
  let g := fun k => f (r.1 + (k - one))
  let kept := ((keys.zip bs).filter (·.2)).map Prod.fst
  have hk : ChatGPTBatch1.ArrayFilter.batch1_keepSlots g (keys.map some) = .ok kept :=
    ChatGPTBatch1.ArrayFilter.batch1_keepSlots_success g keys bs hb
  have hloop := ChatGPTBatch1.ArrayFilter.batch1_filterLoop g heap (keys.map some) []
    (List.replicate keys.length none)
    (by simp only [List.length_map, List.length_replicate]; omega)
    (by simpa only [List.length_nil, Nat.zero_add, List.length_replicate] using hn)
  simp only [hk, List.length_nil, Int.natCast_zero, Int.zero_add, List.map_nil,
    List.nil_append, List.length_replicate] at hloop
  obtain ⟨rest, hrest, hrun⟩ := hloop
  change (forIn (keys.map some) one
      (ChatGPTBatch1.ArrayFilter.batch1_filterStep
        (fun k => f (r.1 + (k - one))) heap.length)).run
      (heap ++ [List.replicate keys.length none]) =
    .ok (JInt.wrap .i64 ((kept.length : Int) + 1), heap ++ [kept.map some ++ rest]) at hrun
  have hkept : kept.length ≤ keys.length := by omega
  have hvalid : ∀ k ∈ kept, 1 ≤ k.val ∧ k.val ≤ (round4.unitRangeLength r).val := by
    intro k hk
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hk
    rw [← hpk]
    exact hkeys p.1 (List.of_mem_zip (List.mem_filter.mp hp).1).1
  have hj : (JInt.wrap .i64 ((kept.length : Int) + 1) - one).val.toNat = kept.length := by
    have hv : (JInt.wrap .i64 ((kept.length : Int) + 1)).val = kept.length + 1 :=
      ival_wrap _ (by omega)
    rw [ival_sub _ _ (by rw [hv, ival_one]; omega), hv, ival_one]
    omega
  have hget : (heap ++ [kept.map some ++ rest])[heap.length]? =
      some (kept.map some ++ rest) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have htrim : (kept.map some ++ rest).take kept.length = kept.map some := by
    rw [← List.length_map (f := some) (as := kept), List.take_append_length]
  have hset : (heap ++ [kept.map some ++ rest]).set heap.length (kept.map some) =
      heap ++ [kept.map some] := by
    rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  have hslots : (heapSlots heap.length).run (heap ++ [kept.map some]) =
      .ok (kept.map some, heap ++ [kept.map some]) := by
    rw [heapSlots_run, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hgather := rangeGetIndices_run r kept (heap ++ [kept.map some]) (by omega) hvalid
  have hrelease : (heap ++ [kept.map some] ++
      [(kept.map (fun k => r.1 + (k - one))).map some]).set heap.length [] =
      heap ++ [[], (kept.map (fun k => r.1 + (k - one))).map some] := by
    rw [List.append_assoc, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  simp only [rangeFilterKeys, vector_bind_run, heapAllocate_run, hrun, vector_modify_run,
    hj, hget, Option.getD_some, htrim, hset, hslots, List.filterMap_map, Function.comp_def, id_eq,
    List.filterMap_some, hgather, hrelease, vector_pure_run, List.length_append,
    List.length_singleton]
  rfl

/-- Selecting values after filtering their keys preserves the same zip/filter order. -/
theorem filterKeys_map (keys : List I) (bs : List Bool) (value : I → I) :
    ((((keys.zip bs).filter (·.2)).map Prod.fst).map value).map some =
      (((keys.map value).zip bs).filter (·.2)).map (fun p => some p.1) := by
  rw [List.zip_map_left, List.filter_map]
  simp only [List.map_map]
  rfl

/-- Range filtering preserves every old heap object and reports the first predicate error. -/
theorem ArrayFilterAbstractarray_proven :
    JuliaLean.Proofs.base.array.round4.FilterAbstractArraySpec := by
  intro f lo hi heap hn
  let keys := intRange one (round4.unitRangeLength (lo, hi))
  let values := intRange lo hi
  have hlen := filterRangeKeys_length lo hi hn
  have hkeys : keys.length < 2 ^ 62 := by dsimp only [keys]; rw [hlen]; omega
  have hvalid := filterRangeKeys_bounds lo hi hn
  have hvalues : keys.map (fun k => lo + (k - one)) = values :=
    filterRangeKeys_values lo hi hn
  have hmap : keys.mapM (fun k => boolResult f (lo + (k - one))) =
      values.mapM (boolResult f) := by
    rw [← hvalues, List.mapM_map]
    rfl
  have hr := rangeFilter_eq_keys f lo hi hn
  constructor
  · intro bs hb
    have hb' : keys.mapM (fun k => boolResult f (lo + (k - one))) = .ok bs := by
      rw [hmap]
      exact hb
    have hs := rangeFilterKeys_success f (lo, hi) keys heap hkeys hvalid bs hb'
    rw [hr]
    have hout := filterKeys_map keys bs (fun k => lo + (k - one))
    rw [hvalues] at hout
    have hcount : (((keys.zip bs).filter (·.2)).map Prod.fst).length =
        (((values.zip bs).filter (·.2)).map (fun p => some p.1)).length := by
      have h := congrArg List.length hout
      simpa only [List.length_map] using h
    simp only [hout, hcount] at hs
    simpa only [keys, values, intRange] using hs
  · intro e he
    rw [hr]
    apply rangeFilterKeys_error f (lo, hi) keys heap hkeys e
    rw [hmap]
    exact he
end JuliaLean.ChatGPT.Batch4.Group2
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c
section MaskProofs

variable {α : Type}

attribute [local irreducible] JInt.wrap wrapInt

/-- Copying a visible slot agrees with its logical value when an unassigned source
has a layout for which unsetting clears the destination. -/
theorem mask_copy_slot (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (handle mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s handle mem off n slots) (p q : I)
    (hp : 1 ≤ p.val ∧ p.val ≤ n.val) (hq : 1 ≤ q.val ∧ q.val ≤ n.val)
    (value : Option α) (hv : (vwWindow slots off n)[(q.val - 1).toNat]? = some value)
    (hclear : value = none → unsetClears layout.runtime = true) :
    ∃ slots', (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
        handle p q).run s = (.ok (), {s with memories := s.memories.set mem slots'}) ∧
      VecAt {s with memories := s.memories.set mem slots'} handle mem off n slots' ∧
      vwWindow slots' off n = (vwWindow slots off n).set (p.val - 1).toNat value := by
  obtain ⟨slots', hr, hnext, hc⟩ :=
    vwCopyItem_run (unsetRuntime := layout.runtime) s handle mem off n slots h p q hp hq
  refine ⟨slots', hr, hnext, ?_⟩
  rw [hv] at hc
  cases value with
  | some x => exact hc
  | none =>
    simpa only [Option.join_some, expectedUnset, hclear rfl, ite_true] using hc

/-- Copying inside one vector changes no array header and no other memory object. -/
theorem mask_copy_frame (layout : MemoryLayoutMetadata) (s : MutableMemory α)
    (handle mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s handle mem off n slots) (p q : I)
    (hp : 1 ≤ p.val ∧ p.val ≤ n.val) (hq : 1 ≤ q.val ∧ q.val ≤ n.val)
    (st' : MutableMemory α)
    (hr : (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
      handle p q).run s = (.ok (), st')) :
    st'.arrays = s.arrays ∧ ∀ other, other ≠ mem → st'.memories[other]? = s.memories[other]? := by
  obtain ⟨slots', hcopy, _, _⟩ :=
    vwCopyItem_run (unsetRuntime := layout.runtime) s handle mem off n slots h p q hp hq
  have hst : st' = {s with memories := s.memories.set mem slots'} :=
    congrArg Prod.snd (hr.symm.trans hcopy)
  rw [hst]
  refine ⟨rfl, ?_⟩
  intro other hne
  exact List.getElem?_set_ne (Ne.symm hne)

/-- One iteration of deleteat!'s Boolean-mask loop. The copy takes place for both
mask values; a discarded value is copied just beyond the already-kept prefix. -/
theorem mask_step (layout : MemoryLayoutMetadata) (handle mem : Nat) (off n : I)
    (w0 : List (Option α)) (mask : List Bool) (k : Nat) (pq : I × I)
    (st : MutableMemory α) (b : Bool) (value : Option α)
    (hsmall : n.val < 9223372036854775806) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots layout.runtime w0)
    (hw : w0[k]? = some value) (hm : mask[k]? = some b)
    (hinv : MaskInv handle mem off n w0 mask k pq st) :
    ∃ st', (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
        handle pq.1 pq.2).run st = (.ok (), st') ∧
      MaskInv handle mem off n w0 mask (k + 1)
        (pq.1 + (if !b then one else zero), pq.2 + one) st' := by
  obtain ⟨sl, hv, hq, hp, htake, hdrop⟩ := hinv
  have hn0 := hv.2.2.2.1
  have hk : k < w0.length := (List.getElem?_eq_some_iff.mp hw).choose
  have hkept := keptPrefix_length_le w0 mask k
  have hwl := vwWindow_length hv
  have hpq : 1 ≤ pq.1.val ∧ pq.1.val ≤ n.val := by omega
  have hqq : 1 ≤ pq.2.val ∧ pq.2.val ≤ n.val := by omega
  have hqidx : (pq.2.val - 1).toNat = k := by omega
  have hpidx : (pq.1.val - 1).toNat = (keptPrefix w0 mask k).length := by omega
  have hsrc : (vwWindow sl off n)[(pq.2.val - 1).toNat]? = some value := by
    have hd := congrArg (fun xs => xs[0]?) hdrop
    simp only [List.getElem?_drop, Nat.add_zero] at hd
    rw [hqidx, hd, hw]
  have hclear : value = none → unsetClears layout.runtime = true := by
    intro hnone
    cases huc : unsetClears layout.runtime with
    | true => rfl
    | false =>
      have ha := hvalid huc k hk
      rw [hw, hnone] at ha
      cases ha
  obtain ⟨sl', hcopy, hv', hc⟩ :=
    mask_copy_slot layout st handle mem off n sl hv pq.1 pq.2 hpq hqq value hsrc hclear
  rw [hpidx] at hc
  refine ⟨{st with memories := st.memories.set mem sl'}, hcopy, sl', hv', ?_, ?_, ?_, ?_⟩
  · rw [ival_add_one pq.2 (by omega), hq]
    omega
  · have hsucc := keptPrefix_succ w0 mask k value b hw hm
    cases b with
    | false =>
      simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false] at hsucc ⊢
      rw [ival_add_one pq.1 (by omega), hsucc]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
        List.append_nil] at hsucc ⊢
      rw [ival_add pq.1 zero (by rw [ival_zero]; omega), ival_zero, hsucc]
      omega
  · have hsucc := keptPrefix_succ w0 mask k value b hw hm
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hsucc
      rw [hsucc]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      rw [hc, list_set_take_succ _ _ _ (by omega), htake]
    | true =>
      simp only [ite_true, List.append_nil] at hsucc
      rw [hsucc, hc, list_set_take_self, htake]
  · rw [hc, list_set_drop_of_lt _ _ _ _ (by omega)]
    exact drop_succ_of_drop_eq _ _ k hdrop
end MaskProofs
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

/-- Empty index iterators return the original vector without touching any slot or sink. -/
theorem deleteIteratorEmpty {α D : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (hv : VecAt s a mem off n slots) (sink : D → Nat → I → MutationM α Unit) (d : D) :
    (deleteatIterator mutableLength (listIterator ([] : List I)) Subtype.val (· + one)
      mutableBounds sink
      (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime))
      (· - ·) (deleteend (mutableStorage layout) pure) a d).run s = (.ok a, s) := by
  have hlen := mutableLength_run s a _ hv.1
  simp only [deleteatIterator, stateExcept_bind, hlen, listIterator, stateExcept_pure]

theorem deleteIndicesEmpty {α : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (a : Nat) (hv : s.validVector a) :
    (mutableDeleteatList layout a []).run s = (.ok a, s) ∧
    (mutableDeleteatVector layout a []).run s = (.ok a, s) := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hv
  have hlist : (mutableDeleteatList layout a []).run s = (.ok a, s) := by
    rw [opusGrowth.deleteatList_eq]
    exact deleteIteratorEmpty layout s a mem off n slots hv _ ()
  exact ⟨hlist, (opusGrowth.deleteatVector_run layout a [] s).trans hlist⟩

/-- Empty splicing allocates its empty result and preserves the source vector. -/
theorem spliceIndicesEmpty {α : Type} (layout : DictLayout)
    (s : MutableMemory α) (a : Nat) (hv : s.validVector a) :
    (mutableSpliceIndices (MemoryLayoutMetadata.ofRuntime layout) a []).run s =
      (.ok s.arrays.length, opusGrowth.spliceStart s) := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hv
  apply opusGrowth.splice_ok_of layout a [] s a (opusGrowth.spliceStart s)
  exact deleteIteratorEmpty (MemoryLayoutMetadata.ofRuntime layout) (opusGrowth.spliceStart s)
    a mem off n slots (opusGrowth.spliceStart_vecAt hv) _ s.arrays.length

/-- The splice entry point checks an invalid first index before pushing any removed value. -/
theorem spliceIndicesFirstBounds {α : Type} (layout : DictLayout)
    (s : MutableMemory α) (a : Nat) (i : I) (post : List I)
    (hv : s.validVector a) (hi : ¬ (1 ≤ i.val ∧ i.val ≤ (s.contents a).length)) :
    ((mutableSpliceIndices (MemoryLayoutMetadata.ofRuntime layout) a (i :: post)).run s).1 =
      .error .bounds := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hv
  have hn : ((s.contents a).length : Int) = n.val := by
    rw [hv.contents, vwWindow_length hv, Int.toNat_of_nonneg hv.2.2.2.1]
  apply opusGrowth.splice_err_of layout a (i :: post) s .bounds
  exact opusGrowth.spliceIter_err0 layout (opusGrowth.spliceStart s) a mem s.arrays.length
    off n slots (opusGrowth.spliceStart_vecAt hv) i post (by simpa only [hn] using hi)

/-- A nonincreasing second index produces the specified argument error in both deletion overloads. -/
theorem deleteSecondNonIncreasing {α : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (hv : VecAt s a mem off n slots) (i j : I) (post : List I)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val) (hroom : i.val < 9223372036854775807)
    (hj : j.val ≤ i.val) :
    (mutableDeleteatList layout a (i :: j :: post)).run s =
      (.error (.argument "indices must be unique and sorted"), s) ∧
    (mutableDeleteatVector layout a (i :: j :: post)).run s =
      (.error (.argument "indices must be unique and sorted"), s) := by
  have hinc : (i + one).val = i.val + 1 := ival_add_one i (by omega)
  have hbad : ¬ ((i + one).val ≤ j.val ∧ j.val ≤ n.val) := by rw [hinc]; omega
  have hlt : j.val < (i + one).val := by rw [hinc]; omega
  have hrun := deleteSecondInvalid layout s a mem off n slots hv i j post hi hbad
  rw [if_pos hlt] at hrun
  exact ⟨hrun, (opusGrowth.deleteatVector_run layout a (i :: j :: post) s).trans hrun⟩
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

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c
section

variable {α β : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- The deletion mask after a read cursor is determined by the indices still
to be processed. Positions before that cursor are outside this invariant. -/
def remainingDeletionMask (mask : List Bool) (k n : Nat) (indices : List I) : Prop :=
  ∀ j, k ≤ j → j < n →
    mask[j]? = some (indices.any (fun i => decide (i.val = (j : Int) + 1)))

theorem remainingDeletionMask_start (w : List β) (indices : List I) :
    remainingDeletionMask (opusGrowth.indexMask w indices) 0 w.length indices := by
  intro j _ hj
  exact opusGrowth.indexMask_get w indices j hj

/-- Once the read cursor has passed the current deleted position, that index
can be removed from the description of the remaining mask. -/
theorem remainingDeletionMask_tail (mask : List Bool) (k k' n : Nat) (i : I)
    (rest : List I) (h : remainingDeletionMask mask k n (i :: rest))
    (hkk : k ≤ k') (hi : i.val ≤ (k' : Int)) :
    remainingDeletionMask mask k' n rest := by
  intro j hj hn
  have hx := h j (by omega) hn
  have hne : decide (i.val = (j : Int) + 1) = false := by
    apply decide_eq_false
    omega
  simpa only [List.any_cons, hne, Bool.false_or] using hx

/-- Every position before the next remaining index is retained. -/
theorem remainingDeletionMask_gap (mask : List Bool) (k n : Nat) (i : I)
    (rest : List I) (h : remainingDeletionMask mask k n (i :: rest))
    (horder : ∀ x ∈ rest, i.val < x.val) (j : Nat)
    (hjk : k ≤ j) (hjn : j < n) (hji : (j : Int) + 1 < i.val) :
    mask[j]? = some false := by
  rw [h j hjk hjn]
  congr 1
  apply List.any_eq_false.mpr
  intro x hx
  simp only [decide_eq_true_eq]
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · omega
  · have := horder x hx
    omega

theorem remainingDeletionMask_hit (mask : List Bool) (k n : Nat) (i : I)
    (rest : List I) (h : remainingDeletionMask mask k n (i :: rest)) (j : Nat)
    (hjk : k ≤ j) (hjn : j < n) (hji : i.val = (j : Int) + 1) :
    mask[j]? = some true := by
  rw [h j hjk hjn]
  congr 1
  apply List.any_eq_true.mpr
  exact ⟨i, List.mem_cons_self, decide_eq_true hji⟩

/-- The actual memory-allocation bound leaves room to increment a read cursor
past the last visible position without machine-integer overflow. -/
theorem deleteGap_size_bound (layout : MemoryLayout)
    {s : MutableMemory α} {a mem : Nat} {off n : I} {slots : List (Option α)}
    (hv : VecAt s a mem off n slots) (hmem : vectorMemory s a (memoryFits layout)) :
    n.val < 9223372036854775806 := by
  have hfit := (hmem _ _ hv.1 hv.2.1).1
  change slots.length < 9223372036854775806 at hfit
  have hoff := hv.2.2.1
  have hend := hv.2.2.2.2.1
  omega

/-- A run of positions retained between two deleted indices compacts those positions,
preserving every array header and every memory object other than the source's memory.
The iteration labels are immaterial; in `_deleteat!` they are a finite `List.range`. -/
theorem deleteGap_run (layout : MemoryLayoutMetadata) (handle mem : Nat) (off n : I)
    (w0 : List (Option α)) (mask : List Bool)
    (hsmall : n.val < 9223372036854775806) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots layout.runtime w0) :
    ∀ (ticks : List β) (k : Nat) (pq : I × I) (st : MutableMemory α),
      k + ticks.length ≤ w0.length →
      (∀ j, k ≤ j → j < k + ticks.length → mask[j]? = some false) →
      MaskInv handle mem off n w0 mask k pq st →
      ∃ pq' st',
        (forIn (m := MutationM α) ticks pq (fun _ pq => do
          copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
            handle pq.1 pq.2
          pure (ForInStep.yield (pq.1 + one, pq.2 + one)))).run st = (.ok pq', st') ∧
        MaskInv handle mem off n w0 mask (k + ticks.length) pq' st' ∧
        st'.arrays = st.arrays ∧
        (∀ other, other ≠ mem → st'.memories[other]? = st.memories[other]?) := by
  intro ticks
  induction ticks with
  | nil =>
    intro k pq st _ _ hinv
    exact ⟨pq, st, rfl, by simpa only [List.length_nil, Nat.add_zero] using hinv,
      rfl, fun _ _ => rfl⟩
  | cons tick ticks ih =>
    intro k pq st hbound hfalse hinv
    have hk : k < w0.length := by simp only [List.length_cons] at hbound; omega
    have hmask : mask[k]? = some false := hfalse k (Nat.le_refl _) (by simp)
    obtain ⟨st1, hcopy, hinv1⟩ :=
      mask_step layout handle mem off n w0 mask k pq st false w0[k]
        hsmall hwlen hvalid (List.getElem?_eq_getElem hk) hmask hinv
    simp only [Bool.not_false, ite_true] at hinv1
    have hframe : st1.arrays = st.arrays ∧
        ∀ other, other ≠ mem → st1.memories[other]? = st.memories[other]? := by
      obtain ⟨sl, hv, hq, hp, _, _⟩ := hinv
      have hn0 := hv.2.2.2.1
      have hpbound := keptPrefix_length_le w0 mask k
      exact mask_copy_frame layout st handle mem off n sl hv pq.1 pq.2
        (by omega) (by omega) st1 hcopy
    obtain ⟨pq', st', hrun, hfinal, harrays, hmemories⟩ :=
      ih (k + 1) (pq.1 + one, pq.2 + one) st1
        (by simp only [List.length_cons] at hbound; omega)
        (fun j hj hje => hfalse j (by omega) (by simp only [List.length_cons]; omega)) hinv1
    refine ⟨pq', st', ?_, ?_, harrays.trans hframe.1, ?_⟩
    · simp only [List.forIn_cons, stateExcept_bind, hcopy, stateExcept_pure]
      exact hrun
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal
    · intro other hne
      exact (hmemories other hne).trans (hframe.2 other hne)

/-- Once every deleted index has been processed, the final tail-copy loop and
the shrinking operation produce exactly the retained subsequence. -/
theorem deleteGap_tail_run (layout : MemoryLayoutMetadata) (handle mem : Nat)
    (off n : I) (w0 : List (Option α)) (mask : List Bool)
    (hsmall : n.val < 9223372036854775806) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots layout.runtime w0) (hmlen : mask.length = w0.length)
    (k : Nat) (pq : I × I) (st : MutableMemory α) (hk : k ≤ w0.length)
    (hremain : remainingDeletionMask mask k w0.length [])
    (hinv : MaskInv handle mem off n w0 mask k pq st) :
    ∃ next,
      (do
        let final ← forIn (m := MutationM α)
          (List.range (n.val - pq.2.val + 1).toNat) pq (fun _ cursors => do
            copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
              handle cursors.1 cursors.2
            pure (ForInStep.yield (cursors.1 + one, cursors.2 + one)))
        deleteend (mutableStorage layout) pure handle (n - final.1 + one)
        pure handle).run st = (.ok handle, next) ∧
      next.validVector handle ∧
      next.contents handle = ((w0.zip mask).filter (fun p => !p.2)).map Prod.fst ∧
      (∀ other, other ≠ handle → next.arrays[other]? = st.arrays[other]?) ∧
      (∀ other, other ≠ mem → next.memories[other]? = st.memories[other]?) := by
  have hstart := hinv
  obtain ⟨sl, hv, hq, _, _, _⟩ := hstart
  have hn0 := hv.2.2.2.1
  have hspan : (List.range (n.val - pq.2.val + 1).toNat).length = w0.length - k := by
    simp only [List.length_range]
    omega
  obtain ⟨final, st1, hloop, hfinal, harrays1, hmemories1⟩ :=
    deleteGap_run layout handle mem off n w0 mask hsmall hwlen hvalid
      (List.range (n.val - pq.2.val + 1).toNat) k pq st
      (by rw [hspan]; omega)
      (fun j hj hje => hremain j hj (by rw [hspan] at hje; omega)) hinv
  have hend : k + (List.range (n.val - pq.2.val + 1).toNat).length = mask.length := by
    rw [hspan, hmlen]
    omega
  rw [hend] at hfinal
  obtain ⟨slots1, hv1, _, hp, htake, _⟩ := hfinal
  have hkept := keptPrefix_length_le w0 mask mask.length
  let d := n - final.1 + one
  have hsub : (n - final.1).val = n.val - final.1.val := ival_sub _ _ (by omega)
  have hd : d.val = n.val - (keptPrefix w0 mask mask.length).length := by
    dsimp only [d]
    rw [ival_add (n - final.1) one (by rw [hsub, ival_one]; omega), hsub, ival_one]
    omega
  obtain ⟨next, slots2, hdel, hv2, hmemories2, harrays2, hc⟩ :=
    vwDeleteend_run (layout := layout) st1 handle mem off n slots1 hv1 d
      (by rw [hd]; omega) (by rw [hd]; omega) (by rw [hd]; omega)
  dsimp only [d] at hdel
  refine ⟨next, ?_, hv2.valid, ?_, ?_, ?_⟩
  · simp only [stateExcept_bind, hloop, hdel, stateExcept_pure]
  · rw [hv2.contents, hc]
    have hnat : (n.val - d.val).toNat = (keptPrefix w0 mask mask.length).length := by
      rw [hd]
      omega
    rw [hnat, htake, keptPrefix_full]
  · intro other hne
    rw [harrays2, List.getElem?_set_ne (Ne.symm hne), harrays1]
  · intro other hne
    rw [hmemories2, List.getElem?_set_ne (Ne.symm hne)]
    exact hmemories1 other hne

/-- The copy-gap frame also preserves an independently allocated splice result. -/
theorem deleteGap_preserves_sink
    {s s' : MutableMemory α} {a mem dh : Nat} {g : VectorGeometry}
    {done : List (Option α)}
    (hinv : opusGrowth.DltInv a mem dh s g done)
    (ha : s'.arrays = s.arrays)
    (hm : ∀ other, other ≠ mem → s'.memories[other]? = s.memories[other]?) :
    opusGrowth.DltInv a mem dh s' g done := by
  exact opusGrowth.dltInv_congr hinv (by rw [ha]) hm
end
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- The existing sorted-index deletion loop with the non-collecting sink. -/
abbrev deleteNowhereLoop (layout : MemoryLayoutMetadata) (handle : Nat) (n : I)
    (initial : List I) (pq : I × I) (rest : List I) : MutationM α (I × I) :=
  deleteatIterator.loop (listIterator initial) Subtype.val (· + one)
    (pushDeleted mutableAssigned mutableGet (fun (_ : Unit) x => pure (pushNowhere x))
      (fun (_ : Unit) d => pure (growendNowhere d)))
    (copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime))
    handle () n pq.1 pq.2 rest

/-- A sorted, bounded remainder of the deletion iterator preserves compaction
and its memory frame, and consumes exactly the remaining deletion mask. -/
theorem deleteNowhereLoop_run (layout : MemoryLayoutMetadata) (handle mem : Nat)
    (off n : I) (w0 : List (Option α)) (mask : List Bool) (initial : List I)
    (hsmall : n.val < 9223372036854775806) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots layout.runtime w0) :
    ∀ (rest : List I) (k : Nat) (pq : I × I) (st : MutableMemory α),
      k ≤ w0.length →
      rest.Pairwise (fun i j => i.val < j.val) →
      (∀ i ∈ rest, pq.2.val ≤ i.val ∧ i.val ≤ n.val) →
      remainingDeletionMask mask k w0.length rest →
      MaskInv handle mem off n w0 mask k pq st →
      ∃ k' pq' st',
        k ≤ k' ∧ k' ≤ w0.length ∧
        (deleteNowhereLoop layout handle n initial pq rest).run st = (.ok pq', st') ∧
        remainingDeletionMask mask k' w0.length [] ∧
        MaskInv handle mem off n w0 mask k' pq' st' ∧
        st'.arrays = st.arrays ∧
        (∀ other, other ≠ mem → st'.memories[other]? = st.memories[other]?) := by
  intro rest
  induction rest with
  | nil =>
    intro k pq st hk _ _ hremain hinv
    refine ⟨k, pq, st, Nat.le_refl _, hk, ?_, hremain, hinv, rfl, fun _ _ => rfl⟩
    unfold deleteNowhereLoop
    rw [deleteatIterator.loop]
    simp only [listIterator, stateExcept_bind, stateExcept_pure]
  | cons i rest ih =>
    intro k pq st hk hsorted hbounds hremain hinv
    obtain ⟨hfirst, hsorted'⟩ := List.pairwise_cons.mp hsorted
    have hi := hbounds i List.mem_cons_self
    have hstart := hinv
    obtain ⟨slots, hv, hq, hp, _, _⟩ := hstart
    have hn0 := hv.2.2.2.1
    let ticks := List.range (i.val - pq.2.val).toNat
    let k1 := k + ticks.length
    have hk1 : (k1 : Int) + 1 = i.val := by
      dsimp only [k1, ticks]
      rw [List.length_range]
      omega
    have hk1lt : k1 < w0.length := by rw [hwlen]; omega
    have hkgap : k ≤ k1 := by dsimp only [k1]; omega
    obtain ⟨pq1, st1, hgap, hinv1, harrays1, hmemories1⟩ :=
      deleteGap_run layout handle mem off n w0 mask hsmall hwlen hvalid
        ticks k pq st (by omega)
        (fun j hj hje => remainingDeletionMask_gap mask k w0.length i rest
          hremain hfirst j hj (by omega) (by omega)) hinv
    have hmid := hinv1
    obtain ⟨slots1, hv1, hq1, _, _, _⟩ := hmid
    have hqeq : pq1.2 = i := by
      apply Subtype.ext
      change pq1.2.val = i.val
      change pq1.2.val = (k1 : Int) + 1 at hq1
      omega
    have hpush := opusGrowth.vwPushNowhere_run st1 handle mem off n slots1 hv1 i (by omega)
    have hhit : mask[k1]? = some true :=
      remainingDeletionMask_hit mask k w0.length i rest hremain k1 hkgap hk1lt (by omega)
    have hskip := opusGrowth.maskInv_skip handle mem off n w0 mask k1 pq1 st1 w0[k1]
      (List.getElem?_eq_getElem hk1lt) hhit (by omega) hinv1
    rw [hqeq] at hskip
    have hremain' : remainingDeletionMask mask (k1 + 1) w0.length rest :=
      remainingDeletionMask_tail mask k (k1 + 1) w0.length i rest hremain (by omega) (by omega)
    have hinc : (i + one).val = i.val + 1 := ival_add_one i (by omega)
    obtain ⟨k', pq', st', hmono, hfinalbound, hrest, hrestmask, hfinal,
        harrays2, hmemories2⟩ :=
      ih (k1 + 1) (pq1.1, i + one) st1 (by omega) hsorted'
        (by
          intro j hj
          have hjfirst := hfirst j hj
          have hjbound := hbounds j (List.mem_cons_of_mem _ hj)
          change (i + one).val ≤ j.val ∧ j.val ≤ n.val
          rw [hinc]
          omega) hremain' hskip
    refine ⟨k', pq', st', by omega, hfinalbound, ?_, hrestmask, hfinal,
      harrays2.trans harrays1, ?_⟩
    · unfold deleteNowhereLoop
      rw [deleteatIterator.loop]
      simp only [listIterator, stateExcept_bind, stateExcept_pure]
      have hgood : pq.2.val ≤ i.val ∧ i.val ≤ n.val := hi
      simp only [hgood, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change (do
        let cursors ← forIn (m := MutationM α) ticks pq (fun _ cursors => do
          copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
            handle cursors.1 cursors.2
          pure (ForInStep.yield (cursors.1 + one, cursors.2 + one)))
        pushDeleted mutableAssigned mutableGet (fun (_ : Unit) x => pure (pushNowhere x))
          (fun (_ : Unit) d => pure (growendNowhere d)) () handle i
        deleteNowhereLoop layout handle n initial (cursors.1, i + one) rest).run st = _
      simp only [stateExcept_bind, hgap, hpush, stateExcept_pure]
      exact hrest
    · intro other hne
      exact (hmemories2 other hne).trans (hmemories1 other hne)
end
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- The complete successful list-index deletion path: strictly increasing valid
indices compact the retained slots in order and preserve all unrelated objects. -/
theorem deleteSortedListSuccess (layout : MemoryLayoutMetadata) (handle mem : Nat)
    (off n : I) (slots : List (Option α)) (st : MutableMemory α)
    (hv : VecAt st handle mem off n slots)
    (hsmall : n.val < 9223372036854775806)
    (hvalid : ValidArraySlots layout.runtime (vwWindow slots off n))
    (i : I) (rest : List I)
    (hsorted : (i :: rest).Pairwise (fun x y => x.val < y.val))
    (hbounds : ∀ x ∈ i :: rest, 1 ≤ x.val ∧ x.val ≤ n.val) :
    ∃ next,
      (mutableDeleteatList layout handle (i :: rest)).run st = (.ok handle, next) ∧
      next.validVector handle ∧
      next.contents handle =
        (((vwWindow slots off n).zipIdx.filter
          (fun p => !((i :: rest).any (fun x => decide (x.val = (p.2 : Int) + 1))))).map
          Prod.fst) ∧
      (∀ other, other ≠ handle → next.arrays[other]? = st.arrays[other]?) ∧
      (∀ other, other ≠ mem → next.memories[other]? = st.memories[other]?) := by
  let w0 := vwWindow slots off n
  let mask := opusGrowth.indexMask w0 (i :: rest)
  have hwlen : w0.length = n.val.toNat := vwWindow_length hv
  have hmlen : mask.length = w0.length := opusGrowth.indexMask_length _ _
  have hi := hbounds i List.mem_cons_self
  have hn0 := hv.2.2.2.1
  obtain ⟨hfirst, hsorted'⟩ := List.pairwise_cons.mp hsorted
  have hremain0 : remainingDeletionMask mask 0 w0.length (i :: rest) :=
    remainingDeletionMask_start w0 (i :: rest)
  have hbefore : ∀ j : Nat, (j : Int) + 1 < i.val → mask[j]? = some false := by
    intro j hj
    exact remainingDeletionMask_gap mask 0 w0.length i rest hremain0 hfirst j
      (Nat.zero_le _) (by rw [hwlen]; omega) hj
  have hhit : mask[(i.val - 1).toNat]? = some true :=
    remainingDeletionMask_hit mask 0 w0.length i rest hremain0 (i.val - 1).toNat
      (Nat.zero_le _) (by rw [hwlen]; omega) (by omega)
  have hinv := opusGrowth.maskInv_start st handle mem off n slots hv mask
    (hmlen.trans hwlen) i hi hsmall hbefore hhit
  have hremain : remainingDeletionMask mask i.val.toNat w0.length rest :=
    remainingDeletionMask_tail mask 0 i.val.toNat w0.length i rest hremain0
      (Nat.zero_le _) (by omega)
  have hinc : (i + one).val = i.val + 1 := ival_add_one i (by omega)
  obtain ⟨k', pq', st1, _, hk', hloop, hrem', hinv', harrays1, hmemories1⟩ :=
    deleteNowhereLoop_run layout handle mem off n w0 mask (i :: rest)
      hsmall hwlen hvalid rest i.val.toNat (i, i + one) st
      (by rw [hwlen]; omega) hsorted'
      (by
        intro j hj
        have hjfirst := hfirst j hj
        have hjbounds := hbounds j (List.mem_cons_of_mem _ hj)
        change (i + one).val ≤ j.val ∧ j.val ≤ n.val
        rw [hinc]
        omega) hremain hinv
  obtain ⟨next, htail, hvnext, hcontents, harrays2, hmemories2⟩ :=
    deleteGap_tail_run layout handle mem off n w0 mask hsmall hwlen hvalid hmlen
      k' pq' st1 hk' hrem' hinv'
  have hlen := mutableLength_run st handle _ hv.1
  have hbound : (mutableBounds handle i).run st = (.ok (), st) := by
    rw [opusGrowth.vwBounds_run st handle mem off n slots hv i, if_pos hi]
  have hpush := opusGrowth.vwPushNowhere_run st handle mem off n slots hv i hi
  refine ⟨next, ?_, hvnext, ?_, ?_, ?_⟩
  · rw [opusGrowth.deleteatList_eq]
    simp only [deleteatIterator, stateExcept_bind, hlen, listIterator,
      stateExcept_pure, hbound, hpush]
    dsimp only [deleteNowhereLoop, listIterator] at hloop
    rw [hloop]
    dsimp only
    simpa only [stateExcept_bind, stateExcept_pure] using htail
  · rw [hcontents]
    exact opusGrowth.indexMask_keep w0 (i :: rest)
  · intro other hne
    rw [harrays2 other hne, harrays1]
  · intro other hne
    exact (hmemories2 other hne).trans (hmemories1 other hne)
end
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The successful deletion half of `DeleteatIndicesSpec`, for both the generic
index list and vector overloads, including the empty list. The splice result and
arbitrary error-prefix clauses are separate obligations. -/
theorem deleteIndicesSuccessPartial {α : Type} (layout : DictLayout)
    (st : MutableMemory α) (handle : Nat) (indices : List I)
    (hvector : st.validVector handle)
    (hmemory : vectorMemory st handle (memoryFits (allocationSummary layout)))
    (hslots : ValidArraySlots layout (st.contents handle))
    (hsorted : indices.Pairwise (fun i j => i.val < j.val))
    (hbounds : ∀ i ∈ indices, 1 ≤ i.val ∧ i.val ≤ ((st.contents handle).length : Int)) :
    ∀ op ∈ [mutableDeleteatList (MemoryLayoutMetadata.ofRuntime layout) handle indices,
      mutableDeleteatVector (MemoryLayoutMetadata.ofRuntime layout) handle indices],
      ∃ next, op.run st = (.ok handle, next) ∧ next.validVector handle ∧
        next.contents handle =
          (((st.contents handle).zipIdx.filter
            (fun p => !(indices.any (fun i => decide (i.val = (p.2 : Int) + 1))))).map
            Prod.fst) := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvector
  have hn : ((st.contents handle).length : Int) = n.val := by
    rw [hv.contents, vwWindow_length hv, Int.toNat_of_nonneg hv.2.2.2.1]
  have hlist : ∃ next,
      (mutableDeleteatList (MemoryLayoutMetadata.ofRuntime layout) handle indices).run st =
        (.ok handle, next) ∧ next.validVector handle ∧
      next.contents handle =
        (((st.contents handle).zipIdx.filter
          (fun p => !(indices.any (fun i => decide (i.val = (p.2 : Int) + 1))))).map
          Prod.fst) := by
    cases indices with
    | nil =>
      refine ⟨st, ?_, hvector, ?_⟩
      · have hlen := mutableLength_run st handle _ hv.1
        rw [opusGrowth.deleteatList_eq]
        simp only [deleteatIterator, stateExcept_bind, hlen, listIterator, stateExcept_pure]
      · simp only [List.any_nil, Bool.not_false]
        rw [List.filter_eq_self.mpr (fun _ _ => rfl), List.zipIdx_map_fst]
    | cons i rest =>
      have hsmall := deleteGap_size_bound (allocationSummary layout) hv hmemory
      have hvalid : ValidArraySlots layout (vwWindow slots off n) := by
        rw [← hv.contents]
        exact hslots
      obtain ⟨next, hrun, hvalidnext, hcontents, _, _⟩ :=
        deleteSortedListSuccess (MemoryLayoutMetadata.ofRuntime layout) handle mem off n slots st
          hv hsmall hvalid i rest hsorted (by simpa only [hn] using hbounds)
      refine ⟨next, hrun, hvalidnext, ?_⟩
      rw [hv.contents]
      exact hcontents
  intro op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · exact hlist
  · obtain ⟨next, hrun, hvalid, hcontents⟩ := hlist
    exact ⟨next, (opusGrowth.deleteatVector_run _ _ _ _).trans hrun, hvalid, hcontents⟩
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- Error selected by the first invalid index after a processed prefix. -/
def deletePrefixError (cursor bad : Int) : Error :=
  if bad < cursor then .argument "indices must be unique and sorted" else .bounds

/-- An arbitrary sorted, bounded prefix is processed before the first bad suffix
index raises its ordering or bounds error. The mask describes only that prefix;
no condition is imposed on indices after the first bad one. -/
theorem deleteNowherePrefixError_run (layout : MemoryLayoutMetadata) (handle mem : Nat)
    (off n : I) (w0 : List (Option α)) (mask : List Bool) (initial : List I)
    (hsmall : n.val < 9223372036854775806) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots layout.runtime w0) (bad : I) (post : List I) :
    ∀ (pre : List I) (k : Nat) (pq : I × I) (st : MutableMemory α),
      k ≤ w0.length →
      pre.Pairwise (fun i j => i.val < j.val) →
      (∀ i ∈ pre, pq.2.val ≤ i.val ∧ i.val ≤ n.val) →
      remainingDeletionMask mask k w0.length pre →
      MaskInv handle mem off n w0 mask k pq st →
      ¬ (opusGrowth.qlast pre pq.2.val ≤ bad.val ∧ bad.val ≤ n.val) →
      ∃ next,
        (deleteNowhereLoop layout handle n initial pq (pre ++ bad :: post)).run st =
          (.error (deletePrefixError (opusGrowth.qlast pre pq.2.val) bad.val), next) := by
  intro pre
  induction pre with
  | nil =>
    intro k pq st _ _ _ _ _ hbad
    change ¬ (pq.2.val ≤ bad.val ∧ bad.val ≤ n.val) at hbad
    refine ⟨st, ?_⟩
    change (deleteNowhereLoop layout handle n initial pq (bad :: post)).run st =
      (.error (deletePrefixError pq.2.val bad.val), st)
    unfold deleteNowhereLoop
    rw [deleteatIterator.loop]
    simp only [listIterator, stateExcept_bind, stateExcept_pure, hbad,
      decide_false, Bool.not_false, ite_true]
    unfold deletePrefixError
    by_cases hlt : bad.val < pq.2.val <;>
      simp only [hlt, ite_true, ite_false, stateExcept_throw, stateExcept_bind]
  | cons i pre ih =>
    intro k pq st hk hsorted hbounds hremain hinv hbad
    obtain ⟨hfirst, hsorted'⟩ := List.pairwise_cons.mp hsorted
    have hi := hbounds i List.mem_cons_self
    have hstart := hinv
    obtain ⟨slots, hv, hq, hp, _, _⟩ := hstart
    have hn0 := hv.2.2.2.1
    let ticks := List.range (i.val - pq.2.val).toNat
    let k1 := k + ticks.length
    have hk1 : (k1 : Int) + 1 = i.val := by
      dsimp only [k1, ticks]
      rw [List.length_range]
      omega
    have hk1lt : k1 < w0.length := by rw [hwlen]; omega
    have hkgap : k ≤ k1 := by dsimp only [k1]; omega
    obtain ⟨pq1, st1, hgap, hinv1, _, _⟩ :=
      deleteGap_run layout handle mem off n w0 mask hsmall hwlen hvalid
        ticks k pq st (by omega)
        (fun j hj hje => remainingDeletionMask_gap mask k w0.length i pre
          hremain hfirst j hj (by omega) (by omega)) hinv
    have hmid := hinv1
    obtain ⟨slots1, hv1, hq1, _, _, _⟩ := hmid
    have hqeq : pq1.2 = i := by
      apply Subtype.ext
      change pq1.2.val = i.val
      change pq1.2.val = (k1 : Int) + 1 at hq1
      omega
    have hpush := opusGrowth.vwPushNowhere_run st1 handle mem off n slots1 hv1 i (by omega)
    have hhit : mask[k1]? = some true :=
      remainingDeletionMask_hit mask k w0.length i pre hremain k1 hkgap hk1lt (by omega)
    have hskip := opusGrowth.maskInv_skip handle mem off n w0 mask k1 pq1 st1 w0[k1]
      (List.getElem?_eq_getElem hk1lt) hhit (by omega) hinv1
    rw [hqeq] at hskip
    have hremain' : remainingDeletionMask mask (k1 + 1) w0.length pre :=
      remainingDeletionMask_tail mask k (k1 + 1) w0.length i pre hremain (by omega) (by omega)
    have hinc : (i + one).val = i.val + 1 := ival_add_one i (by omega)
    have hlast : opusGrowth.qlast (i :: pre) pq.2.val =
        opusGrowth.qlast pre (i + one).val := by
      rw [opusGrowth.qlast_cons, hinc]
    obtain ⟨next, hrest⟩ :=
      ih (k1 + 1) (pq1.1, i + one) st1 (by omega) hsorted'
        (by
          intro j hj
          have hjfirst := hfirst j hj
          have hjbound := hbounds j (List.mem_cons_of_mem _ hj)
          change (i + one).val ≤ j.val ∧ j.val ≤ n.val
          rw [hinc]
          omega) hremain' hskip (by simpa only [hlast] using hbad)
    refine ⟨next, ?_⟩
    rw [hlast]
    unfold deleteNowhereLoop
    rw [deleteatIterator.loop]
    simp only [List.cons_append, listIterator, stateExcept_bind, stateExcept_pure]
    have hgood : pq.2.val ≤ i.val ∧ i.val ≤ n.val := hi
    simp only [hgood, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    change (do
      let cursors ← forIn (m := MutationM α) ticks pq (fun _ cursors => do
        copyItem mutableAssigned mutableGet mutableSet (mutableUnset layout.runtime)
          handle cursors.1 cursors.2
        pure (ForInStep.yield (cursors.1 + one, cursors.2 + one)))
      pushDeleted mutableAssigned mutableGet (fun (_ : Unit) x => pure (pushNowhere x))
        (fun (_ : Unit) d => pure (growendNowhere d)) () handle i
      deleteNowhereLoop layout handle n initial (cursors.1, i + one) (pre ++ bad :: post)).run st = _
    simp only [stateExcept_bind, hgap, hpush, stateExcept_pure]
    exact hrest
end
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- Both deletion entry points propagate the first invalid-index error after
an arbitrary nonempty sorted valid prefix. Later suffix indices are unrestricted. -/
theorem deleteSortedPrefixError (layout : MemoryLayoutMetadata) (handle mem : Nat)
    (off n : I) (slots : List (Option α)) (st : MutableMemory α)
    (hv : VecAt st handle mem off n slots)
    (hsmall : n.val < 9223372036854775806)
    (hvalid : ValidArraySlots layout.runtime (vwWindow slots off n))
    (first : I) (pre : List I) (bad : I) (post : List I)
    (hsorted : (first :: pre).Pairwise (fun x y => x.val < y.val))
    (hbounds : ∀ x ∈ first :: pre, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hbad : ¬ (opusGrowth.qlast pre (first + one).val ≤ bad.val ∧ bad.val ≤ n.val)) :
    ∃ next,
      (mutableDeleteatList layout handle ((first :: pre) ++ bad :: post)).run st =
        (.error (deletePrefixError (opusGrowth.qlast pre (first + one).val) bad.val), next) ∧
      (mutableDeleteatVector layout handle ((first :: pre) ++ bad :: post)).run st =
        (.error (deletePrefixError (opusGrowth.qlast pre (first + one).val) bad.val), next) := by
  let w0 := vwWindow slots off n
  let mask := opusGrowth.indexMask w0 (first :: pre)
  have hwlen : w0.length = n.val.toNat := vwWindow_length hv
  have hmlen : mask.length = w0.length := opusGrowth.indexMask_length _ _
  have hi := hbounds first List.mem_cons_self
  have hn0 := hv.2.2.2.1
  obtain ⟨hfirst, hsorted'⟩ := List.pairwise_cons.mp hsorted
  have hremain0 : remainingDeletionMask mask 0 w0.length (first :: pre) :=
    remainingDeletionMask_start w0 (first :: pre)
  have hbefore : ∀ j : Nat, (j : Int) + 1 < first.val → mask[j]? = some false := by
    intro j hj
    exact remainingDeletionMask_gap mask 0 w0.length first pre hremain0 hfirst j
      (Nat.zero_le _) (by rw [hwlen]; omega) hj
  have hhit : mask[(first.val - 1).toNat]? = some true :=
    remainingDeletionMask_hit mask 0 w0.length first pre hremain0 (first.val - 1).toNat
      (Nat.zero_le _) (by rw [hwlen]; omega) (by omega)
  have hinv := opusGrowth.maskInv_start st handle mem off n slots hv mask
    (hmlen.trans hwlen) first hi hsmall hbefore hhit
  have hremain : remainingDeletionMask mask first.val.toNat w0.length pre :=
    remainingDeletionMask_tail mask 0 first.val.toNat w0.length first pre hremain0
      (Nat.zero_le _) (by omega)
  have hinc : (first + one).val = first.val + 1 := ival_add_one first (by omega)
  obtain ⟨next, hloop⟩ :=
    deleteNowherePrefixError_run layout handle mem off n w0 mask
      ((first :: pre) ++ bad :: post) hsmall hwlen hvalid bad post pre
      first.val.toNat (first, first + one) st (by rw [hwlen]; omega) hsorted'
      (by
        intro j hj
        have hjfirst := hfirst j hj
        have hjbounds := hbounds j (List.mem_cons_of_mem _ hj)
        change (first + one).val ≤ j.val ∧ j.val ≤ n.val
        rw [hinc]
        omega) hremain hinv hbad
  have hlen := mutableLength_run st handle _ hv.1
  have hbound : (mutableBounds handle first).run st = (.ok (), st) := by
    rw [opusGrowth.vwBounds_run st handle mem off n slots hv first, if_pos hi]
  have hpush := opusGrowth.vwPushNowhere_run st handle mem off n slots hv first hi
  have hlist : (mutableDeleteatList layout handle ((first :: pre) ++ bad :: post)).run st =
      (.error (deletePrefixError (opusGrowth.qlast pre (first + one).val) bad.val), next) := by
    rw [opusGrowth.deleteatList_eq]
    simp only [deleteatIterator, stateExcept_bind, hlen, List.cons_append,
      listIterator, stateExcept_pure, hbound, hpush]
    dsimp only [deleteNowhereLoop, listIterator, List.cons_append] at hloop
    rw [hloop]
  exact ⟨next, hlist, (opusGrowth.deleteatVector_run _ _ _ _).trans hlist⟩
end
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- The sorted-index loop with the fresh result vector as its sink. -/
abbrev spliceDeletionLoop (l : DictLayout) (a dh : Nat) (n : I)
    (initial : List I) (pq : I × I) (rest : List I) : MutationM α (I × I) :=
  deleteatIterator.loop (listIterator initial) Subtype.val (· + one)
    (opusGrowth.spliceSink l)
    (copyItem mutableAssigned mutableGet mutableSet (mutableUnset l))
    a dh n pq.1 pq.2 rest

/-- Consuming a sorted valid prefix follows the result-vector growth plan. On
success the original unread suffix, source compaction invariant, and accumulated
removed slots are all available to the continuation. -/
theorem spliceDeletionPrefix (l : DictLayout) (a mem dh : Nat)
    (off n : I) (w0 : List (Option α)) (mask : List Bool) (initial suffix : List I)
    (hsmall : n.val < 9223372036854775806) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots l w0) :
    ∀ (pre : List I) (k : Nat) (pq : I × I) (st : MutableMemory α)
      (g : VectorGeometry) (done : List (Option α)),
      k ≤ w0.length →
      pre.Pairwise (fun i j => i.val < j.val) →
      (∀ i ∈ pre, pq.2.val ≤ i.val ∧ i.val ≤ n.val) →
      remainingDeletionMask mask k w0.length pre →
      MaskInv a mem off n w0 mask k pq st →
      opusGrowth.DltInv a mem dh st g done →
      (∀ e, pushesPlan (allocationSummary l) g pre.length = .error e →
        ((spliceDeletionLoop l a dh n initial pq (pre ++ suffix)).run st).1 = .error e) ∧
      (∀ g', pushesPlan (allocationSummary l) g pre.length = .ok g' →
        ∃ k' pq' st', k ≤ k' ∧ k' ≤ w0.length ∧
          (spliceDeletionLoop l a dh n initial pq (pre ++ suffix)).run st =
            (spliceDeletionLoop l a dh n initial pq' suffix).run st' ∧
          pq'.2.val = opusGrowth.qlast pre pq.2.val ∧
          remainingDeletionMask mask k' w0.length [] ∧
          MaskInv a mem off n w0 mask k' pq' st' ∧
          opusGrowth.DltInv a mem dh st' g'
            (done ++ pre.map (fun i => w0[(i.val - 1).toNat]?.join))) := by
  intro pre
  induction pre with
  | nil =>
    intro k pq st g done hk _ _ hremain hinv hdlt
    constructor
    · intro e he
      cases he
    · intro g' hg
      have hg' : g = g' := Except.ok.inj hg
      subst g'
      exact ⟨k, pq, st, Nat.le_refl _, hk, rfl, rfl, hremain, hinv,
        by simpa only [List.map_nil, List.append_nil] using hdlt⟩
  | cons i pre ih =>
    intro k pq st g done hk hsorted hbounds hremain hinv hdlt
    obtain ⟨hfirst, hsorted'⟩ := List.pairwise_cons.mp hsorted
    have hi := hbounds i List.mem_cons_self
    have hstart := hinv
    obtain ⟨slots, hv, hq, hp, _, _⟩ := hstart
    have hn0 := hv.2.2.2.1
    let ticks := List.range (i.val - pq.2.val).toNat
    let k1 := k + ticks.length
    have hk1 : (k1 : Int) + 1 = i.val := by
      dsimp only [k1, ticks]
      rw [List.length_range]
      omega
    have hk1lt : k1 < w0.length := by rw [hwlen]; omega
    have hkgap : k ≤ k1 := by dsimp only [k1]; omega
    obtain ⟨pq1, st1, hgap, hinv1, harrays1, hmemories1⟩ :=
      deleteGap_run (MemoryLayoutMetadata.ofRuntime l) a mem off n w0 mask hsmall hwlen hvalid
        ticks k pq st (by omega)
        (fun j hj hje => remainingDeletionMask_gap mask k w0.length i pre
          hremain hfirst j hj (by omega) (by omega)) hinv
    dsimp only [MemoryLayoutMetadata.ofRuntime] at hgap
    have hdlt1 := deleteGap_preserves_sink hdlt harrays1 hmemories1
    have hmid := hinv1
    obtain ⟨slots1, hv1, hq1, _, _, hdrop1⟩ := hmid
    have hqeq : pq1.2 = i := by
      apply Subtype.ext
      change pq1.2.val = i.val
      change pq1.2.val = (k1 : Int) + 1 at hq1
      omega
    have hidx : (i.val - 1).toNat = k1 := by omega
    have hslot : (vwWindow slots1 off n)[(i.val - 1).toNat]?.join =
        w0[(i.val - 1).toNat]?.join := by
      have hx := congrArg (fun xs => xs[0]?.join) hdrop1
      simpa only [List.getElem?_drop, Nat.add_zero, hidx] using hx
    have hhit : mask[k1]? = some true :=
      remainingDeletionMask_hit mask k w0.length i pre hremain k1 hkgap hk1lt (by omega)
    have hskip := opusGrowth.maskInv_skip a mem off n w0 mask k1 pq1 st1 w0[k1]
      (List.getElem?_eq_getElem hk1lt) hhit (by omega) hinv1
    rw [hqeq] at hskip
    have hremain' : remainingDeletionMask mask (k1 + 1) w0.length pre :=
      remainingDeletionMask_tail mask k (k1 + 1) w0.length i pre hremain (by omega) (by omega)
    have hinc : (i + one).val = i.val + 1 := ival_add_one i (by omega)
    have hlast : opusGrowth.qlast (i :: pre) pq.2.val =
        opusGrowth.qlast pre (i + one).val := by
      rw [opusGrowth.qlast_cons, hinc]
    have hstep := opusGrowth.sinkStep l hv1 i (by omega) hdlt1
    have hfactor : (spliceDeletionLoop l a dh n initial pq ((i :: pre) ++ suffix)).run st =
        (do
          opusGrowth.spliceSink l dh a i
          spliceDeletionLoop l a dh n initial (pq1.1, i + one) (pre ++ suffix)).run st1 := by
      unfold spliceDeletionLoop
      rw [deleteatIterator.loop]
      simp only [List.cons_append, listIterator, stateExcept_bind, stateExcept_pure,
        hi, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      change (do
        let cursors ← forIn (m := MutationM α) ticks pq (fun _ cursors => do
          copyItem mutableAssigned mutableGet mutableSet (mutableUnset l)
            a cursors.1 cursors.2
          pure (ForInStep.yield (cursors.1 + one, cursors.2 + one)))
        opusGrowth.spliceSink l dh a i
        spliceDeletionLoop l a dh n initial (cursors.1, i + one) (pre ++ suffix)).run st = _
      rw [stateExcept_bind, hgap]
      simp only [stateExcept_bind, spliceDeletionLoop, listIterator]
    cases hplan : growendPlan (allocationSummary l) g 1 with
    | error err =>
      have hpush := hstep.1 err hplan
      have hrun : ((spliceDeletionLoop l a dh n initial pq ((i :: pre) ++ suffix)).run st).1 =
          .error err := by
        rw [hfactor, stateExcept_bind, hpush]
      constructor
      · intro e he
        simp only [List.length_cons, pushesPlan, hplan, Except.bind] at he
        cases he
        exact hrun
      · intro g' hg'
        simp only [List.length_cons, pushesPlan, hplan, Except.bind] at hg'
        cases hg'
    | ok g1 =>
      obtain ⟨st2, hpush, ha2, hm2, hdlt2⟩ := hstep.2 g1 hplan
      rw [hslot] at hdlt2
      have hinv2 := opusGrowth.maskInv_congr hskip ha2 hm2
      have hih := ih (k1 + 1) (pq1.1, i + one) st2 g1
        (done ++ [w0[(i.val - 1).toNat]?.join]) (by omega) hsorted'
        (by
          intro j hj
          have hjfirst := hfirst j hj
          have hjbound := hbounds j (List.mem_cons_of_mem _ hj)
          change (i + one).val ≤ j.val ∧ j.val ≤ n.val
          rw [hinc]
          omega) hremain' hinv2 hdlt2
      have hrun : (spliceDeletionLoop l a dh n initial pq ((i :: pre) ++ suffix)).run st =
          (spliceDeletionLoop l a dh n initial (pq1.1, i + one) (pre ++ suffix)).run st2 := by
        rw [hfactor, stateExcept_bind, hpush]
      constructor
      · intro e he
        simp only [List.length_cons, pushesPlan, hplan, Except.bind] at he
        rw [hrun]
        exact hih.1 e he
      · intro g' hg'
        simp only [List.length_cons, pushesPlan, hplan, Except.bind] at hg'
        obtain ⟨k', pq', st', hmono, hbound, hrest, hlast', hmask', hinv', hdlt'⟩ :=
          hih.2 g' hg'
        refine ⟨k', pq', st', by omega, hbound, hrun.trans hrest, ?_, hmask', hinv', ?_⟩
        · rw [hlast]
          exact hlast'
        · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using hdlt'
end
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c
section
variable {α β γ : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- Error propagation through a stateful continuation, with no claim about state. -/
theorem mutationBindError (action : MutationM α β) (next : β → MutationM α γ)
    (st : MutableMemory α) (e : Error) (h : (action.run st).1 = .error e) :
    ((action >>= next).run st).1 = .error e := by
  rw [stateExcept_bind]
  cases hr : action.run st with
  | mk result after =>
    have he : result = .error e := by simpa only [hr] using h
    rw [he]

abbrev spliceDeleteIterator (l : DictLayout) (a dh : Nat) (indices : List I) :
    MutationM α Nat :=
  deleteatIterator mutableLength (listIterator indices) Subtype.val (· + one)
    mutableBounds (opusGrowth.spliceSink l)
    (copyItem mutableAssigned mutableGet mutableSet (mutableUnset l))
    (· - ·) (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) a dh

abbrev deletionTail (l : DictLayout) (a : Nat) (n : I) (pq : I × I) : MutationM α Nat := do
  let final ← forIn (m := MutationM α)
    (List.range (n.val - pq.2.val + 1).toNat) pq (fun _ cursors => do
      copyItem mutableAssigned mutableGet mutableSet (mutableUnset l)
        a cursors.1 cursors.2
      pure (ForInStep.yield (cursors.1 + one, cursors.2 + one)))
  deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure a (n - final.1 + one)
  pure a

theorem spliceDeleteIterator_start (l : DictLayout) (a mem dh : Nat) (off n : I)
    (slots : List (Option α)) (st : MutableMemory α) (hv : VecAt st a mem off n slots)
    (first : I) (rest : List I) (hi : 1 ≤ first.val ∧ first.val ≤ n.val) :
    (spliceDeleteIterator l a dh (first :: rest)).run st =
      (do
        opusGrowth.spliceSink l dh a first
        let pq ← spliceDeletionLoop l a dh n (first :: rest) (first, first + one) rest
        deletionTail l a n pq).run st := by
  have hlen := mutableLength_run st a _ hv.1
  have hbounds : (mutableBounds a first).run st = (.ok (), st) := by
    rw [opusGrowth.vwBounds_run st a mem off n slots hv first, if_pos hi]
  simp only [spliceDeleteIterator, deleteatIterator, stateExcept_bind, hlen,
    listIterator, stateExcept_pure, hbounds]
  rfl

theorem spliceDeletionLoop_nil (l : DictLayout) (a dh : Nat) (n : I)
    (initial : List I) (pq : I × I) (st : MutableMemory α) :
    (spliceDeletionLoop l a dh n initial pq []).run st = (.ok pq, st) := by
  unfold spliceDeletionLoop
  rw [deleteatIterator.loop]
  simp only [listIterator, stateExcept_bind, stateExcept_pure]

theorem deletionTail_preserves_result (l : DictLayout) (a mem dh : Nat)
    (off n : I) (w0 : List (Option α)) (mask : List Bool)
    (hsmall : n.val < 9223372036854775806) (hwlen : w0.length = n.val.toNat)
    (hvalid : ValidArraySlots l w0) (hmlen : mask.length = w0.length)
    (k : Nat) (pq : I × I) (st : MutableMemory α) (g : VectorGeometry)
    (done : List (Option α)) (hk : k ≤ w0.length)
    (hremain : remainingDeletionMask mask k w0.length [])
    (hinv : MaskInv a mem off n w0 mask k pq st)
    (hdlt : opusGrowth.DltInv a mem dh st g done) :
    ∃ next, (deletionTail l a n pq).run st = (.ok a, next) ∧
      next.validVector a ∧
      next.contents a = ((w0.zip mask).filter (fun p => !p.2)).map Prod.fst ∧
      opusGrowth.DltInv a mem dh next g done := by
  obtain ⟨next, hrun, hvalid, hcontents, harrays, hmemories⟩ :=
    deleteGap_tail_run (MemoryLayoutMetadata.ofRuntime l) a mem off n w0 mask
      hsmall hwlen hvalid hmlen k pq st hk hremain hinv
  have hdne : dh ≠ a := by
    obtain ⟨_, _, _, _, hne, _⟩ := hdlt
    exact hne
  exact ⟨next, hrun, hvalid, hcontents,
    opusGrowth.dltInv_congr hdlt (harrays dh hdne) hmemories⟩

/-- A nonempty successful index list, including every result-growth failure. -/
theorem spliceIteratorSorted (l : DictLayout) (a mem dh : Nat)
    (off n : I) (slots : List (Option α)) (st : MutableMemory α)
    (g : VectorGeometry) (done : List (Option α))
    (hv : VecAt st a mem off n slots)
    (hsmall : n.val < 9223372036854775806)
    (hvalid : ValidArraySlots l (vwWindow slots off n))
    (hdlt : opusGrowth.DltInv a mem dh st g done)
    (first : I) (rest : List I)
    (hsorted : (first :: rest).Pairwise (fun i j => i.val < j.val))
    (hbounds : ∀ i ∈ first :: rest, 1 ≤ i.val ∧ i.val ≤ n.val) :
    (∀ e, pushesPlan (allocationSummary l) g (first :: rest).length = .error e →
      ((spliceDeleteIterator l a dh (first :: rest)).run st).1 = .error e) ∧
    (∀ g', pushesPlan (allocationSummary l) g (first :: rest).length = .ok g' →
      ∃ next, (spliceDeleteIterator l a dh (first :: rest)).run st = (.ok a, next) ∧
        next.validVector a ∧
        next.contents a =
          (((vwWindow slots off n).zipIdx.filter
            (fun p => !((first :: rest).any (fun i => decide (i.val = (p.2 : Int) + 1))))).map
            Prod.fst) ∧
        opusGrowth.DltInv a mem dh next g'
          (done ++ (first :: rest).map (fun i => (vwWindow slots off n)[(i.val - 1).toNat]?.join))) := by
  let w0 := vwWindow slots off n
  let mask := opusGrowth.indexMask w0 (first :: rest)
  have hwlen : w0.length = n.val.toNat := vwWindow_length hv
  have hmlen : mask.length = w0.length := opusGrowth.indexMask_length _ _
  have hi := hbounds first List.mem_cons_self
  have hn0 := hv.2.2.2.1
  obtain ⟨hfirst, hsorted'⟩ := List.pairwise_cons.mp hsorted
  have hremain0 : remainingDeletionMask mask 0 w0.length (first :: rest) :=
    remainingDeletionMask_start w0 (first :: rest)
  have hbefore : ∀ j : Nat, (j : Int) + 1 < first.val → mask[j]? = some false := by
    intro j hj
    exact remainingDeletionMask_gap mask 0 w0.length first rest hremain0 hfirst j
      (Nat.zero_le _) (by rw [hwlen]; omega) hj
  have hhit : mask[(first.val - 1).toNat]? = some true :=
    remainingDeletionMask_hit mask 0 w0.length first rest hremain0 (first.val - 1).toNat
      (Nat.zero_le _) (by rw [hwlen]; omega) (by omega)
  have hinv := opusGrowth.maskInv_start st a mem off n slots hv mask
    (hmlen.trans hwlen) first hi hsmall hbefore hhit
  have hremain : remainingDeletionMask mask first.val.toNat w0.length rest :=
    remainingDeletionMask_tail mask 0 first.val.toNat w0.length first rest hremain0
      (Nat.zero_le _) (by omega)
  have hinc : (first + one).val = first.val + 1 := ival_add_one first (by omega)
  have hstep := opusGrowth.sinkStep l hv first hi hdlt
  have hstart := spliceDeleteIterator_start l a mem dh off n slots st hv first rest hi
  cases hplan : growendPlan (allocationSummary l) g 1 with
  | error err =>
    have hpush := hstep.1 err hplan
    have hrun : ((spliceDeleteIterator l a dh (first :: rest)).run st).1 = .error err := by
      rw [hstart, stateExcept_bind, hpush]
    constructor
    · intro e he
      simp only [List.length_cons, pushesPlan, hplan, Except.bind] at he
      cases he
      exact hrun
    · intro g' hg'
      simp only [List.length_cons, pushesPlan, hplan, Except.bind] at hg'
      cases hg'
  | ok g1 =>
    obtain ⟨st1, hpush, ha1, hm1, hdlt1⟩ := hstep.2 g1 hplan
    have hinv1 := opusGrowth.maskInv_congr hinv ha1 hm1
    have hpref := spliceDeletionPrefix l a mem dh off n w0 mask (first :: rest) []
      hsmall hwlen hvalid rest first.val.toNat (first, first + one) st1 g1
      (done ++ [w0[(first.val - 1).toNat]?.join])
      (by rw [hwlen]; omega) hsorted'
      (by
        intro j hj
        have hjfirst := hfirst j hj
        have hjbounds := hbounds j (List.mem_cons_of_mem _ hj)
        change (first + one).val ≤ j.val ∧ j.val ≤ n.val
        rw [hinc]
        omega) hremain hinv1 hdlt1
    simp only [List.append_nil] at hpref
    have hrun : (spliceDeleteIterator l a dh (first :: rest)).run st =
        (do
          let pq ← spliceDeletionLoop l a dh n (first :: rest) (first, first + one) rest
          deletionTail l a n pq).run st1 := by
      rw [hstart, stateExcept_bind, hpush]
    constructor
    · intro e he
      simp only [List.length_cons, pushesPlan, hplan, Except.bind] at he
      rw [hrun]
      exact mutationBindError _ _ st1 e (hpref.1 e he)
    · intro g' hg'
      simp only [List.length_cons, pushesPlan, hplan, Except.bind] at hg'
      obtain ⟨k', pq', st2, _, hk', hloop, _, hremain', hinv2, hdlt2⟩ := hpref.2 g' hg'
      rw [spliceDeletionLoop_nil] at hloop
      obtain ⟨next, htail, hvalidnext, hcontents, hdltNext⟩ :=
        deletionTail_preserves_result l a mem dh off n w0 mask hsmall hwlen hvalid hmlen
          k' pq' st2 g' _ hk' hremain' hinv2 hdlt2
      refine ⟨next, ?_, hvalidnext, ?_, ?_⟩
      · rw [hrun, stateExcept_bind, hloop]
        exact htail
      · rw [hcontents]
        exact opusGrowth.indexMask_keep _ _
      · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using hdltNext
end
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c

/-- The complete successful-splicing half of the frozen index-list contract,
with its exact allocation-growth plan and representation-validity premises. -/
theorem spliceIndicesSuccessPartial {α : Type} (l : DictLayout)
    (s : MutableMemory α) (a : Nat) (indices : List I)
    (hvector : s.validVector a)
    (hmemory : vectorMemory s a (memoryFits (allocationSummary l)))
    (hslots : ValidArraySlots l (s.contents a))
    (hsorted : indices.Pairwise (fun i j => i.val < j.val))
    (hbounds : ∀ i ∈ indices, 1 ≤ i.val ∧ i.val ≤ ((s.contents a).length : Int)) :
    FollowsSteps (pushesPlan (allocationSummary l) emptyGeometry indices.length)
      ((mutableSpliceIndices (MemoryLayoutMetadata.ofRuntime l) a indices).run s)
      (fun d next => next.validVector a ∧
        next.contents a =
          (((s.contents a).zipIdx.filter
            (fun p => !(indices.any (fun i => decide (i.val = (p.2 : Int) + 1))))).map
            Prod.fst) ∧
        next.validVector d ∧
        next.contents d = indices.map (fun i => (s.contents a)[(i.val - 1).toNat]?.join)) := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvector
  have hn : ((s.contents a).length : Int) = n.val := by
    rw [hv.contents, vwWindow_length hv, Int.toNat_of_nonneg hv.2.2.2.1]
  have hv0 := opusGrowth.spliceStart_vecAt hv
  have hd0 := opusGrowth.spliceStart_dltInv hv
  cases indices with
  | nil =>
    constructor
    · intro e he
      cases he
    · intro g hg
      obtain ⟨md, nd, dsl, hvd, _, _, _, hdone, _⟩ := hd0
      refine ⟨s.arrays.length, opusGrowth.spliceStart s,
        spliceIndicesEmpty l s a hvector, hv0.valid, ?_, hvd.valid, ?_⟩
      · rw [hv0.contents, ← hv.contents]
        simp only [List.any_nil, Bool.not_false]
        rw [List.filter_eq_self.mpr (fun _ _ => rfl), List.zipIdx_map_fst]
      · rw [hvd.contents, hdone]
        rfl
  | cons first rest =>
    have hsmall := deleteGap_size_bound (allocationSummary l) hv hmemory
    have hvalid : ValidArraySlots l (vwWindow slots off n) := by
      rw [← hv.contents]
      exact hslots
    have hmain := spliceIteratorSorted l a mem s.arrays.length off n slots
      (opusGrowth.spliceStart s) emptyGeometry [] hv0 hsmall hvalid hd0 first rest hsorted
      (by simpa only [hn] using hbounds)
    constructor
    · intro e he
      exact opusGrowth.splice_err_of l a (first :: rest) s e (hmain.1 e he)
    · intro g hg
      obtain ⟨next, hrun, hvalidnext, hcontents, hdone⟩ := hmain.2 g hg
      obtain ⟨md, nd, dsl, hvd, _, _, _, hremoved, _⟩ := hdone
      refine ⟨s.arrays.length, next, opusGrowth.splice_ok_of l a (first :: rest) s a next hrun,
        hvalidnext, ?_, hvd.valid, ?_⟩
      · rw [hv.contents]
        exact hcontents
      · rw [hvd.contents, hremoved, hv.contents]
        rfl
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c
section
variable {α : Type}
attribute [local irreducible] JInt.wrap wrapInt

/-- Invalid subsequent indices are rejected before copying a gap or extending the sink. -/
theorem spliceDeletionLoop_bad (l : DictLayout) (a dh : Nat) (n : I)
    (initial : List I) (pq : I × I) (bad : I) (post : List I)
    (st : MutableMemory α) (hbad : ¬ (pq.2.val ≤ bad.val ∧ bad.val ≤ n.val)) :
    (spliceDeletionLoop l a dh n initial pq (bad :: post)).run st =
      (.error (deletePrefixError pq.2.val bad.val), st) := by
  unfold spliceDeletionLoop
  rw [deleteatIterator.loop]
  simp only [listIterator, stateExcept_bind, stateExcept_pure, hbad,
    decide_false, Bool.not_false, ite_true]
  unfold deletePrefixError
  by_cases hlt : bad.val < pq.2.val <;>
    simp only [hlt, ite_true, ite_false, stateExcept_throw, stateExcept_bind]

/-- An invalid index after a valid sorted prefix is reached exactly when all
preceding sink extensions succeeded; otherwise the earlier growth error wins. -/
theorem spliceIteratorPrefixError (l : DictLayout) (a mem dh : Nat)
    (off n : I) (slots : List (Option α)) (st : MutableMemory α)
    (g : VectorGeometry) (done : List (Option α))
    (hv : VecAt st a mem off n slots)
    (hsmall : n.val < 9223372036854775806)
    (hvalid : ValidArraySlots l (vwWindow slots off n))
    (hdlt : opusGrowth.DltInv a mem dh st g done)
    (first : I) (pre : List I) (bad : I) (post : List I)
    (hsorted : (first :: pre).Pairwise (fun i j => i.val < j.val))
    (hbounds : ∀ i ∈ first :: pre, 1 ≤ i.val ∧ i.val ≤ n.val)
    (hbad : ¬ (opusGrowth.qlast pre (first + one).val ≤ bad.val ∧ bad.val ≤ n.val)) :
    ((spliceDeleteIterator l a dh (first :: (pre ++ bad :: post))).run st).1 =
      .error (match pushesPlan (allocationSummary l) g (first :: pre).length with
        | .error e => e
        | .ok _ => deletePrefixError (opusGrowth.qlast pre (first + one).val) bad.val) := by
  let w0 := vwWindow slots off n
  let mask := opusGrowth.indexMask w0 (first :: pre)
  have hwlen : w0.length = n.val.toNat := vwWindow_length hv
  have hmlen : mask.length = w0.length := opusGrowth.indexMask_length _ _
  have hi := hbounds first List.mem_cons_self
  have hn0 := hv.2.2.2.1
  obtain ⟨hfirst, hsorted'⟩ := List.pairwise_cons.mp hsorted
  have hremain0 : remainingDeletionMask mask 0 w0.length (first :: pre) :=
    remainingDeletionMask_start w0 (first :: pre)
  have hbefore : ∀ j : Nat, (j : Int) + 1 < first.val → mask[j]? = some false := by
    intro j hj
    exact remainingDeletionMask_gap mask 0 w0.length first pre hremain0 hfirst j
      (Nat.zero_le _) (by rw [hwlen]; omega) hj
  have hhit : mask[(first.val - 1).toNat]? = some true :=
    remainingDeletionMask_hit mask 0 w0.length first pre hremain0 (first.val - 1).toNat
      (Nat.zero_le _) (by rw [hwlen]; omega) (by omega)
  have hinv := opusGrowth.maskInv_start st a mem off n slots hv mask
    (hmlen.trans hwlen) first hi hsmall hbefore hhit
  have hremain : remainingDeletionMask mask first.val.toNat w0.length pre :=
    remainingDeletionMask_tail mask 0 first.val.toNat w0.length first pre hremain0
      (Nat.zero_le _) (by omega)
  have hinc : (first + one).val = first.val + 1 := ival_add_one first (by omega)
  have hstep := opusGrowth.sinkStep l hv first hi hdlt
  have hstart := spliceDeleteIterator_start l a mem dh off n slots st hv first
    (pre ++ bad :: post) hi
  cases hplan : growendPlan (allocationSummary l) g 1 with
  | error err =>
    have hpush := hstep.1 err hplan
    rw [hstart, stateExcept_bind, hpush]
    simp only [List.length_cons, pushesPlan, hplan, Except.bind]
  | ok g1 =>
    obtain ⟨st1, hpush, ha1, hm1, hdlt1⟩ := hstep.2 g1 hplan
    have hinv1 := opusGrowth.maskInv_congr hinv ha1 hm1
    have hpref := spliceDeletionPrefix l a mem dh off n w0 mask
      (first :: (pre ++ bad :: post)) (bad :: post) hsmall hwlen hvalid
      pre first.val.toNat (first, first + one) st1 g1
      (done ++ [w0[(first.val - 1).toNat]?.join])
      (by rw [hwlen]; omega) hsorted'
      (by
        intro j hj
        have hjfirst := hfirst j hj
        have hjbounds := hbounds j (List.mem_cons_of_mem _ hj)
        change (first + one).val ≤ j.val ∧ j.val ≤ n.val
        rw [hinc]
        omega) hremain hinv1 hdlt1
    have hrun : (spliceDeleteIterator l a dh (first :: (pre ++ bad :: post))).run st =
        (do
          let pq ← spliceDeletionLoop l a dh n (first :: (pre ++ bad :: post))
            (first, first + one) (pre ++ bad :: post)
          deletionTail l a n pq).run st1 := by
      rw [hstart, stateExcept_bind, hpush]
    rw [hrun]
    simp only [List.length_cons, pushesPlan, hplan, Except.bind]
    cases hrestPlan : pushesPlan (allocationSummary l) g1 pre.length with
    | error err =>
      exact mutationBindError _ _ st1 err (hpref.1 err hrestPlan)
    | ok g2 =>
      obtain ⟨k', pq', st2, _, _, hprefix, hlast, _, _, _⟩ := hpref.2 g2 hrestPlan
      have herr := spliceDeletionLoop_bad l a dh n (first :: (pre ++ bad :: post))
        pq' bad post st2 (by simpa only [hlast] using hbad)
      rw [stateExcept_bind, hprefix, herr]
      rw [hlast]
end
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
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array JuliaLean.src.genericmemory_c

/-- Both deletion overloads and splicing select the same invalid-index error,
with splicing giving precedence to an earlier result-vector growth failure. -/
theorem deleteAndSplicePrefixError {α : Type} (l : DictLayout)
    (s : MutableMemory α) (a : Nat)
    (hvector : s.validVector a)
    (hmemory : vectorMemory s a (memoryFits (allocationSummary l)))
    (hslots : ValidArraySlots l (s.contents a))
    (first : I) (pre : List I) (bad : I) (post : List I)
    (hsorted : (first :: pre).Pairwise (fun i j => i.val < j.val))
    (hbounds : ∀ i ∈ first :: pre, 1 ≤ i.val ∧ i.val ≤ ((s.contents a).length : Int))
    (hbad : ¬ (opusGrowth.qlast pre (first + one).val ≤ bad.val ∧
      bad.val ≤ ((s.contents a).length : Int))) :
    (∀ op ∈ [mutableDeleteatList (MemoryLayoutMetadata.ofRuntime l) a ((first :: pre) ++ bad :: post),
        mutableDeleteatVector (MemoryLayoutMetadata.ofRuntime l) a ((first :: pre) ++ bad :: post)],
      (op.run s).1 = .error (deletePrefixError (opusGrowth.qlast pre (first + one).val) bad.val)) ∧
    ((mutableSpliceIndices (MemoryLayoutMetadata.ofRuntime l) a
      ((first :: pre) ++ bad :: post)).run s).1 =
      .error (match pushesPlan (allocationSummary l) emptyGeometry (first :: pre).length with
        | .error e => e
        | .ok _ => deletePrefixError (opusGrowth.qlast pre (first + one).val) bad.val) := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvector
  have hn : ((s.contents a).length : Int) = n.val := by
    rw [hv.contents, vwWindow_length hv, Int.toNat_of_nonneg hv.2.2.2.1]
  have hsmall := deleteGap_size_bound (allocationSummary l) hv hmemory
  have hvalid : ValidArraySlots l (vwWindow slots off n) := by
    rw [← hv.contents]
    exact hslots
  have hbounds' : ∀ i ∈ first :: pre, 1 ≤ i.val ∧ i.val ≤ n.val := by
    simpa only [hn] using hbounds
  have hbad' : ¬ (opusGrowth.qlast pre (first + one).val ≤ bad.val ∧ bad.val ≤ n.val) := by
    simpa only [hn] using hbad
  obtain ⟨next, hlist, hvectorRun⟩ :=
    deleteSortedPrefixError (MemoryLayoutMetadata.ofRuntime l) a mem off n slots s hv hsmall
      hvalid first pre bad post hsorted hbounds' hbad'
  refine ⟨?_, ?_⟩
  · intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · rw [hlist]
    · rw [hvectorRun]
  · apply opusGrowth.splice_err_of l a ((first :: pre) ++ bad :: post) s
    exact spliceIteratorPrefixError l a mem s.arrays.length off n slots (opusGrowth.spliceStart s)
      emptyGeometry [] (opusGrowth.spliceStart_vecAt hv) hsmall hvalid
      (opusGrowth.spliceStart_dltInv hv) first pre bad post hsorted hbounds' hbad'

/-- A first bad index fails before either deletion overload alters the source. -/
theorem deletionFirstBounds {α : Type} (layout : MemoryLayoutMetadata)
    (s : MutableMemory α) (a : Nat) (i : I) (post : List I)
    (hv : s.validVector a) (hi : ¬ (1 ≤ i.val ∧ i.val ≤ ((s.contents a).length : Int))) :
    ∀ op ∈ [mutableDeleteatList layout a (i :: post), mutableDeleteatVector layout a (i :: post)],
      (op.run s).1 = .error .bounds := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hv
  have hn : ((s.contents a).length : Int) = n.val := by
    rw [hv.contents, vwWindow_length hv, Int.toNat_of_nonneg hv.2.2.2.1]
  have hl : ((mutableDeleteatList layout a (i :: post)).run s).1 = .error .bounds := by
    rw [opusGrowth.deleteatList_eq]
    exact opusGrowth.deleteIter_err0 s a mem off n slots hv i post (by simpa only [hn] using hi)
  intro op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · exact hl
  · rw [opusGrowth.deleteatVector_run]
    exact hl

/-- The logical next cursor after a nonempty valid prefix is one past its last index. -/
theorem deletionCursorLast (first : I) (pre : List I) (last : I)
    (hinc : (first + one).val = first.val + 1)
    (hlast : (first :: pre).getLast? = some last) :
    opusGrowth.qlast pre (first + one).val = last.val + 1 := by
  have hq : opusGrowth.qlast (first :: pre) 1 = last.val + 1 := by
    simp only [opusGrowth.qlast, hlast, Option.map_some, Option.getD_some]
  rw [opusGrowth.qlast_cons, ← hinc] at hq
  exact hq

/-- The exact frozen contract for deleting or splicing at sorted integer indices. -/
theorem MultidimcovArrayV2DeleteatInternal_proven :
    JuliaLean.Proofs.base.array.DeleteatIndicesSpec := by
  intro α l s a indices hvector hmemory hslots
  dsimp only
  constructor
  · intro hsorted hbounds
    exact ⟨deleteIndicesSuccessPartial l s a indices hvector hmemory hslots hsorted hbounds,
      spliceIndicesSuccessPartial l s a indices hvector hmemory hslots hsorted hbounds⟩
  · intro pre i post hindices hsorted hbounds
    subst indices
    refine ⟨?_, ?_, ?_⟩
    · intro hnil hbad
      subst pre
      exact ⟨deletionFirstBounds (MemoryLayoutMetadata.ofRuntime l) s a i post hvector hbad,
        spliceIndicesFirstBounds l s a i post hvector hbad⟩
    · intro j hlast hle
      cases pre with
      | nil => cases hlast
      | cons first pre =>
        obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvector
        have hn : ((s.contents a).length : Int) = n.val := by
          rw [hv.contents, vwWindow_length hv, Int.toNat_of_nonneg hv.2.2.2.1]
        have hsmall := deleteGap_size_bound (allocationSummary l) hv hmemory
        have hfirst := hbounds first List.mem_cons_self
        have hinc : (first + one).val = first.val + 1 := ival_add_one first (by rw [hn] at hfirst; omega)
        have hq := deletionCursorLast first pre j hinc hlast
        have hbad : ¬ (opusGrowth.qlast pre (first + one).val ≤ i.val ∧
            i.val ≤ ((s.contents a).length : Int)) := by rw [hq]; omega
        have he : deletePrefixError (opusGrowth.qlast pre (first + one).val) i.val =
            .argument "indices must be unique and sorted" := by
          unfold deletePrefixError
          rw [if_pos (by rw [hq]; omega)]
        obtain ⟨hd, hs⟩ :=
          deleteAndSplicePrefixError l s a hvector hmemory hslots first pre i post hsorted hbounds hbad
        constructor
        · simpa only [he] using hd
        · cases hp : pushesPlan (allocationSummary l) emptyGeometry (first :: pre).length <;>
            simpa only [hp, he] using hs
    · intro j hlast hlt habove
      cases pre with
      | nil => cases hlast
      | cons first pre =>
        obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvector
        have hn : ((s.contents a).length : Int) = n.val := by
          rw [hv.contents, vwWindow_length hv, Int.toNat_of_nonneg hv.2.2.2.1]
        have hsmall := deleteGap_size_bound (allocationSummary l) hv hmemory
        have hfirst := hbounds first List.mem_cons_self
        have hinc : (first + one).val = first.val + 1 := ival_add_one first (by rw [hn] at hfirst; omega)
        have hq := deletionCursorLast first pre j hinc hlast
        have hbad : ¬ (opusGrowth.qlast pre (first + one).val ≤ i.val ∧
            i.val ≤ ((s.contents a).length : Int)) := by omega
        have he : deletePrefixError (opusGrowth.qlast pre (first + one).val) i.val = .bounds := by
          unfold deletePrefixError
          rw [if_neg (by rw [hq]; omega)]
        obtain ⟨hd, hs⟩ :=
          deleteAndSplicePrefixError l s a hvector hmemory hslots first pre i post hsorted hbounds hbad
        constructor
        · simpa only [he] using hd
        · cases hp : pushesPlan (allocationSummary l) emptyGeometry (first :: pre).length <;>
            simpa only [hp, he] using hs
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

theorem filterPureRun {σ K β : Type} (x : β)
    (q : JuliaLean.base.set.SetModel K) (s : σ) :
    ((pure x : SetVecG σ K β).run q).run s = (.ok (x, q), s) := rfl

/-- A read error stops a filter iteration before any output write or predicate call. -/
theorem filterIndexStepReadError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (input output : I)
    (q : JuliaLean.base.set.SetModel K) (s next : σ) (e : Error)
    (hread : (v.ops.getAt input).run s = (.error e, next)) :
    ((filterIndexStep v f input output).run q).run s = (.error e, next) := by
  simp only [filterIndexStep, filterBindRun, filterLiftRun, hread, Except.map]

/-- A finite filter loop stops at its first failed read, without examining the remaining indices. -/
theorem filterIndexLoopReadError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (input output : I) (rest : List I)
    (q : JuliaLean.base.set.SetModel K) (s next : σ) (e : Error)
    (hread : (v.ops.getAt input).run s = (.error e, next)) :
    ((forIn (input :: rest) output (filterIndexStep v f)).run q).run s = (.error e, next) := by
  simp only [List.forIn_cons, filterBindRun,
    filterIndexStepReadError v f input output q s next e hread]

/-- The next output cursor returned by a completed filter iteration. -/
def filterIndexCursor {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (input output : I) : SetVecG σ K I := do
  let x ← liftV (v.ops.getAt input)
  liftV (v.ops.setAt x output)
  let keep ← liftV (baseLift (round4.boolResult f x))
  pure (if keep then output + one else output)

theorem filterIndexStepYield {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (input output : I) :
    filterIndexStep v f input output = ForInStep.yield <$> filterIndexCursor v f input output := by
  simp only [filterIndexStep, filterIndexCursor, map_eq_pure_bind, bind_assoc, pure_bind]

theorem filterIndexLoopFold {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (keys : List I) (output : I) :
    forIn keys output (filterIndexStep v f) =
      keys.foldlM (fun output input => filterIndexCursor v f input output) output := by
  have hstep : filterIndexStep v f =
      fun input output => (fun cursor => ForInStep.yield cursor) <$>
        filterIndexCursor v f input output := by
    funext input output
    exact filterIndexStepYield v f input output
  rw [hstep]
  simpa only [id_map'] using
    (List.forIn_yield_eq_foldlM (filterIndexCursor v f) (fun _ _ cursor => cursor) output
      (l := keys))

/-- Successful filter prefixes compose; the source loop has no early-success break. -/
theorem filterIndexLoopAppend {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (pre rest : List I) (output : I) :
    forIn (pre ++ rest) output (filterIndexStep v f) =
      (forIn pre output (filterIndexStep v f) >>= fun cursor =>
        forIn rest cursor (filterIndexStep v f)) := by
  simp only [filterIndexLoopFold, List.foldlM_append]

/-- After any successful prefix, the next failed read is the loop's error. -/
theorem filterIndexLoopPrefixReadError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (pre rest : List I) (first input output : I)
    (q q' : JuliaLean.base.set.SetModel K) (s afterPrefix next : σ) (e : Error)
    (hprefix : ((forIn pre first (filterIndexStep v f)).run q).run s =
      (.ok (output, q'), afterPrefix))
    (hread : (v.ops.getAt input).run afterPrefix = (.error e, next)) :
    ((forIn (pre ++ input :: rest) first (filterIndexStep v f)).run q).run s =
      (.error e, next) := by
  rw [filterIndexLoopAppend]
  simp only [filterBindRun, hprefix,
    filterIndexLoopReadError v f input output rest q' afterPrefix next e hread]

/-- After any successful prefix, the first predicate failure determines the loop's error. -/
theorem filterIndexLoopPrefixPredicateError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (pre rest : List I) (first input output : I)
    (q q' : JuliaLean.base.set.SetModel K) (s afterPrefix afterRead afterWrite : σ)
    (x : K) (e : Error)
    (hprefix : ((forIn pre first (filterIndexStep v f)).run q).run s =
      (.ok (output, q'), afterPrefix))
    (hread : (v.ops.getAt input).run afterPrefix = (.ok x, afterRead))
    (hwrite : (v.ops.setAt x output).run afterRead = (.ok (), afterWrite))
    (hpred : round4.boolResult f x = .error e) :
    ((forIn (pre ++ input :: rest) first (filterIndexStep v f)).run q).run s =
      (.error e, afterWrite) := by
  rw [filterIndexLoopAppend]
  simp only [filterBindRun, hprefix,
    filterIndexLoopPredicateError v f input output rest q' afterPrefix afterRead afterWrite x e
      hread hwrite hpred]

/-- An error reading the first iteration slot propagates from the exact filter entry point. -/
theorem filterVectorFirstReadError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (first last : I) (rest : List I)
    (s next : σ) (e : Error)
    (hfirst : v.ops.firstindex.run s = (.ok first, s))
    (hlast : v.ops.lastindex.run s = (.ok last, s))
    (hrange : intRange first last = first :: rest)
    (hread : (v.ops.getAt first).run s = (.error e, next)) :
    setVecRunG (vecFilterBangG (fun x => liftV (baseLift (round4.boolResult f x))) v) s =
      (.error e, next) := by
  unfold setVecRunG
  rw [filterVectorExpand]
  simp only [filterBindRun, filterLiftRun, hfirst, hlast, Except.map, hrange,
    filterIndexLoopReadError v f first first rest _ s next e hread]

/-- Any error from the indexed loop propagates before the source's shrinking phase. -/
theorem filterVectorLoopError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (first last : I)
    (s next : σ) (e : Error)
    (hfirst : v.ops.firstindex.run s = (.ok first, s))
    (hlast : v.ops.lastindex.run s = (.ok last, s))
    (hloop : ((forIn (intRange first last) first (filterIndexStep v f)).run
      (JuliaLean.base.set.setConstructorEmpty (K := K) 0)).run s = (.error e, next)) :
    setVecRunG (vecFilterBangG (fun x => liftV (baseLift (round4.boolResult f x))) v) s =
      (.error e, next) := by
  unfold setVecRunG
  rw [filterVectorExpand]
  simp only [filterBindRun, filterLiftRun, hfirst, hlast, Except.map, hloop]

/-- The exact filter propagates a failed read after any successful prefix. -/
theorem filterVectorPrefixReadError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (pre rest : List I) (first last input output : I)
    (q : JuliaLean.base.set.SetModel K) (s afterPrefix next : σ) (e : Error)
    (hfirst : v.ops.firstindex.run s = (.ok first, s))
    (hlast : v.ops.lastindex.run s = (.ok last, s))
    (hrange : intRange first last = pre ++ input :: rest)
    (hprefix : ((forIn pre first (filterIndexStep v f)).run
      (JuliaLean.base.set.setConstructorEmpty (K := K) 0)).run s =
      (.ok (output, q), afterPrefix))
    (hread : (v.ops.getAt input).run afterPrefix = (.error e, next)) :
    setVecRunG (vecFilterBangG (fun x => liftV (baseLift (round4.boolResult f x))) v) s =
      (.error e, next) := by
  apply filterVectorLoopError v f first last s next e hfirst hlast
  rw [hrange]
  exact filterIndexLoopPrefixReadError v f pre rest first input output _ q s afterPrefix next e
    hprefix hread

/-- The exact filter propagates the first predicate failure after any successful prefix. -/
theorem filterVectorPrefixPredicateError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (pre rest : List I) (first last input output : I)
    (q : JuliaLean.base.set.SetModel K) (s afterPrefix afterRead afterWrite : σ) (x : K) (e : Error)
    (hfirst : v.ops.firstindex.run s = (.ok first, s))
    (hlast : v.ops.lastindex.run s = (.ok last, s))
    (hrange : intRange first last = pre ++ input :: rest)
    (hprefix : ((forIn pre first (filterIndexStep v f)).run
      (JuliaLean.base.set.setConstructorEmpty (K := K) 0)).run s =
      (.ok (output, q), afterPrefix))
    (hread : (v.ops.getAt input).run afterPrefix = (.ok x, afterRead))
    (hwrite : (v.ops.setAt x output).run afterRead = (.ok (), afterWrite))
    (hpred : round4.boolResult f x = .error e) :
    setVecRunG (vecFilterBangG (fun x => liftV (baseLift (round4.boolResult f x))) v) s =
      (.error e, afterWrite) := by
  apply filterVectorLoopError v f first last s afterWrite e hfirst hlast
  rw [hrange]
  exact filterIndexLoopPrefixPredicateError v f pre rest first input output _ q s afterPrefix
    afterRead afterWrite x e hprefix hread hwrite hpred
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion5
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion5
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

/-- Delete-at converts the original index before observing length or comparing,
converting or performing arithmetic on the original delta. -/
def DeleteatIndexConversionFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref Z Index BadIndex Offset Remainder Count : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (toIndexInt : Index → NativeGrowthM State T I) (toDeltaInt : Z → NativeGrowthM State T I)
    (nonnegative : Z → NativeGrowthM State T (Option Bool))
    (fits : Z → I → NativeGrowthM State T (Option Bool))
    (plusDelta : I → Z → NativeGrowthM State T Offset)
    (subtractOne : Offset → NativeGrowthM State T BadIndex)
    (leLength : Offset → I → NativeGrowthM State T (Option Bool))
    (minusDelta : I → Z → NativeGrowthM State T Remainder)
    (minusIndex : Remainder → I → NativeGrowthM State T Count)
    (copyFirst : Nat → Offset → Nat → I → I → NativeGrowthM State T Unit)
    (copyLast : Nat → I → Nat → Offset → Count → NativeGrowthM State T Unit)
    (a : Nat) (index : Index) (delta : Z) (before : NativeGrowthWorld State T),
    FirstNativeFailure (toIndexInt index)
      (deleteat layout elementType native ccall allocation access references toIndexInt toDeltaInt
        nonnegative fits plusDelta subtractOne leLength minusDelta minusIndex copyFirst copyLast a index delta) before
end JuliaLean.Proofs.base.array.Completion5


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- An exception from either length observation or from their comparison is
propagated with its effects intact; a false comparison raises `BoundsError`
before iteration or array writes. Every successful call returns the same array
handle. Julia source: base/array.jl:2000-2010. Documentation:
base/array.jl:1911-1939 and doc/src/manual/interfaces.md:9-54,209-238.

The observed outcomes below are conditions on one actual boundary call, not
correctness laws supplied for a callee. They include effectful and throwing
implementations without asserting that any custom implementation is available.
No list-size, index-origin, or non-aliasing restriction is imposed on this
boundary-level invariant. -/
def DeleteatMaskBoundarySpec : Prop :=
  ∀ (World A Mem Ref Mask Count E : Type)
    (iteration : ForIn (ExceptT Error (StateM World)) Mask Bool)
    (o : JuliaLean.base.array.Models1Group14.MaskOps
      (ExceptT Error (StateM World)) A Mem Ref Mask Count E)
    (a : A) (inds : Mask) (before : World),
    letI := iteration
    let run := (JuliaLean.base.array.Models1Group14.deleteatMask o a inds).run before
    (∀ error after,
      (o.storage.length a).run before = (.error error, after) →
      run = (.error error, after)) ∧
    (∀ n afterLength error afterMask,
      (o.storage.length a).run before = (.ok n, afterLength) →
      (o.maskLength inds).run afterLength = (.error error, afterMask) →
      run = (.error error, afterMask)) ∧
    (∀ n afterLength count afterMask error afterComparison,
      (o.storage.length a).run before = (.ok n, afterLength) →
      (o.maskLength inds).run afterLength = (.ok count, afterMask) →
      (o.sameLength count n).run afterMask = (.error error, afterComparison) →
      run = (.error error, afterComparison)) ∧
    (∀ n afterLength count afterMask afterComparison,
      (o.storage.length a).run before = (.ok n, afterLength) →
      (o.maskLength inds).run afterLength = (.ok count, afterMask) →
      (o.sameLength count n).run afterMask = (.ok false, afterComparison) →
      run = (.error .bounds, afterComparison)) ∧
    match run.1 with
    | .ok returned => returned = a
    | .error _ => True
end JuliaLean.Proofs.base.array.Models1Group14


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry

def CurriedFilterContents : Prop := round4.FilterCurriedSpec ∧ FilterArraySpec

theorem curriedFilterContents : CurriedFilterContents :=
  ⟨JuliaLean.ChatGPT.Batch4.Group2.ArrayFilterCurried_proven,
    ChatGPTBatch1.ArrayFilter.MultidimcovArrayV2FilterArray_proven⟩
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean JuliaLean.base.array JuliaLean.Registry
open JuliaLean.Proofs.base.array.round4

def DeleteIndexRangeContents : Prop :=
  DeleteatIndexSpec ∧ JuliaLean.Proofs.base.array.round4.DeleteatRangeSpec ∧ EmptySpec

def KeptIndicesContents : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (ops : BigIntegerOps), ops.Lawful →
  ∀ (initial : MutableMemory α) (indices : List IntegerValue),
    initial.validVector 0 → (initial.contents 0).length < 2 ^ 62 →
    (∀ i ∈ indices, match i with | .bool _ => False | _ => True) →
    let before := initial.contents 0
    let inside := fun i : IntegerValue => 1 ≤ i.val ∧ i.val ≤ (before.length : Int)
    let assigned := fun i : IntegerValue => (before[(i.val - 1).toNat]?.join).isSome
    let action : KeepatM α Nat := keepat3129
      (JuliaLean.base.abstractarray.keepAtIndices
        (fun _ => pure one) (fun a => liftM (mutableLength (α := α) a))
        (fun p k : IntegerValue => pure (decide (p.val < k.val)))
        (fun i k => pure (decide (i.val = k.val)))
        (fun a k => liftM (vectorGetInteger ops a k)) keepatStore
        (fun _ i => pure (i + one)) (fun i j => pure (i, j))
        (fun a r => liftM (keepatDeleteRange (α := α) (layout := layout) a r))) 0 indices
    let result := (action.run).run initial
    (indices.Pairwise (fun a b => a.val < b.val) →
      (∀ i ∈ indices, inside i ∧ assigned i = true) →
      ∃ after, result = (.ok (.ok 0), after) ∧ after.validVector 0 ∧
        after.contents 0 = indices.map (fun i => before[(i.val - 1).toNat]?.join)) ∧
    ((∀ i ∈ indices, inside i ∧ assigned i = true) →
      ¬ indices.Pairwise (fun a b => a.val < b.val) →
      result.1 = .ok (.error (.julia (.argumentError "indices must be unique and sorted")))) ∧
    (indices.Pairwise (fun a b => a.val < b.val) →
      (∀ i ∈ indices, inside i → assigned i = true) →
      (∃ i ∈ indices, ¬ inside i) → result.1 = .error .bounds)
end JuliaLean.Proofs.base.array.LegacyRetired

