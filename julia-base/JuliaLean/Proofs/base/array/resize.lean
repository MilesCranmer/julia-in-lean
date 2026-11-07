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

/-- `resize!(a, nl; first)` (array.jl:1559-1574): growth at the chosen end, the negative-length
`ArgumentError`, or deletion at the chosen end (no memory request). -/
def resizePlan (l : MemoryLayout) (g : VectorGeometry) (nl : Int) (first : Bool) :
    Except Error VectorGeometry :=
  if (g.length : Int) < nl then
    (if first then growbegPlan else growendPlan) l g (nl - g.length).toNat
  else if nl < 0 then .error (.argument "new length must be ≥ 0")
  else if first then
    .ok ⟨g.memlen, if nl = 0 then g.offset else g.offset + (g.length - nl.toNat), nl.toNat⟩
  else .ok { g with length := nl.toNat }

/-- A fact kept out of `omega`'s view: `omega` slows down sharply when the context holds several
equations between values of wrapped-`Int` sums and differences. -/
structure Hide (p : Prop) : Prop where
  out : p

/-- `x & typemax(Int)` (int.jl:899) leaves a nonnegative `Int` unchanged. -/
theorem band_typemax (d : I) (h : 0 ≤ d.val) :
    (JuliaLean.base.int.band d (JInt.typemax .i64)).val = d.val := by
  have hb := ival_bounds d
  rw [JuliaLean.Proofs.base.int.val_eq_wrap_pattern (JuliaLean.base.int.band d (JInt.typemax .i64)),
    JuliaLean.Proofs.base.int.pattern_band, JuliaLean.Proofs.base.int.pattern_of_nonneg d h,
    JuliaLean.Proofs.base.int.pattern_of_nonneg (JInt.typemax .i64) (by decide)]
  have ht : (JInt.typemax .i64).val.toNat = 2 ^ 63 - 1 := by decide
  rw [ht, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega), Int.toNat_of_nonneg h]
  exact wrapInt_of_inRange .i64 _ hb
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorWindows

/- Wrapped `Int` values are compared through the `ival_*` lemmas; unfolding `JInt.wrap` inside
arithmetic decision procedures is exponential. -/
attribute [local irreducible] JInt.wrap

/-! ### End growth -/

theorem vwGrowend_negative {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat) (delta : I)
    (hd : delta.val < 0) :
    (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)) handle delta).run s =
      (.error (.argument "grow requires delta >= 0"), s) := by
  have hneg : ¬ (delta ≥ zero) := by rw [ge_iff_le, jle_iff, ival_zero]; omega
  simp only [growend, stateExcept_bind, stateExcept_pure, hneg, decide_false, Bool.not_false,
    ite_true, stateExcept_throw]

theorem emptySpec : EmptySpec := by
  intro α layout s handle hvalid
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hvalid
  have hn0 := h.2.2.2.1
  obtain ⟨next, slots', hrun, hv', _, _, hw⟩ :=
    vwDeleteend_run (layout := layout) s handle mem off n slots h n hn0 (Int.le_refl _) (by omega)
  refine ⟨next, ?_, ?_, hv'.valid⟩
  · simp only [empty, stateExcept_bind, mutableLength_run s handle _ h.1, hrun, stateExcept_pure]
  · rw [hv'.contents, hw]
    simp

theorem vwGrowbeg_negative {layout : MemoryLayoutMetadata} (s : MutableMemory α) (handle : Nat) (delta : I)
    (hd : delta.val < 0) :
    (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)) handle delta).run s =
      (.error (.argument "grow requires delta >= 0"), s) := by
  have hz : ¬ delta.val = 0 := by omega
  have hneg : ¬ (delta ≥ zero) := by rw [ge_iff_le, jle_iff, ival_zero]; omega
  simp only [growbeg, stateExcept_bind, stateExcept_pure, hz, ite_false, hneg, decide_false,
    Bool.not_false, ite_true, stateExcept_throw]

theorem resize_lengthToInt_run {α : Type} {t : IntTy} (s : MutableMemory α) (handle : Nat)
    (nl : JInt t) (first : Bool) (growb growe deleteb deletee : Nat → I → MutationM α Unit) :
    (resize (m := MutationM α) lengthToInt mutableLength JuliaLean.base.int.band
      growb growe deleteb deletee handle nl first).run s =
    if IntTy.i64.min ≤ nl.val ∧ nl.val ≤ IntTy.i64.max then
      (resize (m := MutationM α) pure mutableLength JuliaLean.base.int.band
        growb growe deleteb deletee handle (JInt.wrap .i64 nl.val) first).run s
    else (.error .inexact, s) := by
  by_cases hx : IntTy.i64.min ≤ nl.val ∧ nl.val ≤ IntTy.i64.max
  · simp only [hx, and_self, ite_true, resize, lengthToInt, stateExcept_bind, stateExceptLift_run,
      bitinteger_array_conversion, stateExcept_pure]
  · simp only [hx, ite_false, resize, lengthToInt, stateExcept_bind, stateExceptLift_run,
      bitinteger_array_conversion]

/-- `resize!(a, n; first)` (array.jl:1559; docstring at array.jl:1522-1558) for a new length `n`
of any BitInteger type: a value that is not an `Int` raises `InexactError`, and a negative one
`ArgumentError`, with `a` untouched; otherwise `a` gets exactly `n` elements, the first
`min(length(a), n)` old elements kept as its prefix (`first = false`) or the last ones as its
suffix (`first = true`), in a valid vector. The size precondition is that the memory length plus
`2n + 1` is an `Int`, as the checked growth arithmetic requires. -/
def ResizeSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (t : IntTy) (s : MutableMemory α) (handle : Nat) (nl : JInt t)
    (first : Bool),
    s.validVector handle →
    let len : Int := (s.contents handle).length
    let run := (resize (m := MutationM α) lengthToInt mutableLength JuliaLean.base.int.band
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (deletebeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure)
      handle nl first).run s
    (¬ (IntTy.i64.min ≤ nl.val ∧ nl.val ≤ IntTy.i64.max) → run = (.error .inexact, s)) ∧
    (IntTy.i64.min ≤ nl.val → nl.val ≤ IntTy.i64.max →
      Follows s (resizePlan l (geometryOf s handle) nl.val first) run (fun r next =>
        r = handle ∧ next.validVector handle ∧ ((next.contents handle).length : Int) = nl.val ∧
        (first = false → (next.contents handle).take (min len nl.val).toNat =
          (s.contents handle).take (min len nl.val).toNat) ∧
        (first = true → (next.contents handle).drop (nl.val - min len nl.val).toNat =
          (s.contents handle).drop (len - min len nl.val).toNat)))
end VectorWindows
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def SizehintSpec : Prop :=
  ∀ (α : Type) (l : DictLayout) (t : IntTy) (s : MutableMemory α) (handle : Nat) (sz : JInt t)
    (first shrink : Bool),
    s.validVector handle →
    let run := (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) lengthToInt
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      handle sz first shrink).run s
    (¬ (IntTy.i64.min ≤ sz.val ∧ sz.val ≤ IntTy.i64.max) → run = (.error .inexact, s)) ∧
    (IntTy.i64.min ≤ sz.val → sz.val ≤ IntTy.i64.max →
      Follows s (sizehintPlan l (geometryOf s handle) sz.val first shrink) run (fun r next =>
        r = handle ∧ next.validVector handle ∧ next.contents handle = s.contents handle ∧
        ∀ h', h' ≠ handle → next.arrays[h']? = s.arrays[h']?))
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def elementConversion (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (x : β) : Except Error α :=
  if already x then .ok (asTyped x) else convert x
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArray
section
open JuliaLean JuliaLean.base.array
set_option maxHeartbeats 1000000
attribute [local irreducible] JInt.wrap wrapInt

theorem resize_map_run {α : Type} (action : MutationM α Unit) (a : Nat) (s : MutableMemory α) :
    ((Except.map (fun _ : Unit => a)) <$> action.run) s =
      match action.run s with
      | (.error e,after) => (.error e,after)
      | (.ok _,after) => (.ok a,after) := by
  change (Except.map (fun _ : Unit => a) (action.run s).1,(action.run s).2) = _
  rcases hr : action.run s with ⟨r,after⟩
  cases r <;> rfl

 theorem resize_native_run {α : Type} (s : MutableMemory α) (a : Nat) (v : MutableVector)
    (ha : s.arrays[a]? = some v) (nl : I) (first : Bool)
    (growb growe deleteb deletee : Nat → I → MutationM α Unit) :
    (resize (m := MutationM α) pure mutableLength JuliaLean.base.int.band
      growb growe deleteb deletee a nl first).run s =
      if v.size.val < nl.val then
        match ((if first then growb else growe) a
            (JuliaLean.base.int.band (nl-v.size) (JInt.typemax .i64))).run s with
        | (.error e,after) => (.error e,after)
        | (.ok _,after) => (.ok a,after)
      else if nl ≠ v.size then
        if nl.val < 0 then (.error (.argument "new length must be ≥ 0"),s)
        else match ((if first then deleteb else deletee) a (v.size-nl)).run s with
          | (.error e,after) => (.error e,after)
          | (.ok _,after) => (.ok a,after)
      else (.ok a,s) := by
  cases first <;> by_cases hg : v.size.val < nl.val <;>
    by_cases he : nl = v.size <;> by_cases hn : nl.val < 0 <;>
    simp [hg,he,hn,resize,stateExcept_bind,stateExcept_pure,mutableLength_run s a v ha,
      jlt_iff,ival_zero,bne_iff_ne,stateExcept_throw,resize_map_run] <;> rfl

 theorem resize_conversion_error {α : Type} {t : IntTy} (s : MutableMemory α) (a : Nat)
    (nl : JInt t) (first : Bool) (growb growe deleteb deletee : Nat → I → MutationM α Unit)
    (hn : ¬ (IntTy.i64.min ≤ nl.val ∧ nl.val ≤ IntTy.i64.max)) :
    (resize (m := MutationM α) lengthToInt mutableLength JuliaLean.base.int.band
      growb growe deleteb deletee a nl first).run s = (.error .inexact,s) := by
  rw [resize_lengthToInt_run,if_neg hn]

 theorem resize_delta_val {α : Type} {s : MutableMemory α} {a mem : Nat} {off n : I}
    {slots : List (Option α)} (h : VecAt s a mem off n slots) (nl : I) (hg : n.val < nl.val) :
    (JuliaLean.base.int.band (nl-n) (JInt.typemax .i64)).val = nl.val-n.val := by
  have hsub : (nl-n).val = nl.val-n.val := ival_sub _ _ (by
    have := ival_bounds nl; have := h.2.2.2.1; omega)
  rw [band_typemax _ (by rw [hsub]; omega),hsub]

theorem chosenGrow_follows {α : Type} (l : DictLayout) {s : MutableMemory α}
    {a mem : Nat} {off n : I} {slots : List (Option α)}
    (h : VecAt s a mem off n slots) (delta : I) (hd : 0 ≤ delta.val) (first : Bool) :
    Follows s ((if first then growbegPlan else growendPlan) l (geometryOf s a) delta.val.toNat)
      (((if first then
        growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
        else growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
          a delta).run s)
      (fun _ next => next.validVector a ∧
        ((next.contents a).length : Int) = n.val + delta.val ∧
        (first = false → (next.contents a).take n.val.toNat = s.contents a) ∧
        (first = true → (next.contents a).drop delta.val.toNat = s.contents a)) := by
  have hn0 := h.2.2.2.1
  rw [opusGrowth.VecAt.geometry h]
  cases first with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    obtain ⟨herr,hok⟩ := opusGrowth.growend_plan l h delta hd
    refine ⟨herr,fun g hg => ?_⟩
    obtain ⟨next,mem',off',sl',hr,hv,_,hnd,hw,_⟩ := hok g hg
    refine ⟨(),next,hr,hv.valid,?_,fun _ => ?_,by simp⟩
    · rw [hv.contents,vwWindow_length hv,hnd]
      omega
    · rw [hv.contents,hw,h.contents]
  | true =>
    simp only [ite_true]
    obtain ⟨herr,hok⟩ := opusGrowth.growbeg_plan l h delta hd
    refine ⟨herr,fun g hg => ?_⟩
    obtain ⟨next,mem',off',sl',hr,hv,_,hnd,hw,_⟩ := hok g hg
    refine ⟨(),next,hr,hv.valid,?_,by simp,fun _ => ?_⟩
    · rw [hv.contents,vwWindow_length hv,hnd]
      omega
    · rw [hv.contents,hw,h.contents]

theorem chosenDelete_result {α : Type} (l : DictLayout) {s : MutableMemory α}
    {a mem : Nat} {off n : I} {slots : List (Option α)}
    (h : VecAt s a mem off n slots) (nl : I) (hnl : 0 ≤ nl.val) (hsmall : nl.val < n.val)
    (first : Bool) :
    ∃ next,
      (((if first then deletebeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        else deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) a (n-nl)).run s) = (.ok (),next) ∧
      next.validVector a ∧ ((next.contents a).length : Int) = nl.val ∧
      (first = false → next.contents a = (s.contents a).take nl.val.toNat) ∧
      (first = true → next.contents a = (s.contents a).drop (n.val-nl.val).toNat) := by
  have hn0 := h.2.2.2.1
  have hdelta : (n-nl).val = n.val-nl.val := ival_sub _ _ (by have := ival_bounds n; omega)
  have hnew : (n-(n-nl)).val = nl.val := by
    rw [ival_sub _ _ (by rw [hdelta]; have := ival_bounds nl; omega),hdelta]
    omega
  cases first with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    obtain ⟨next,sl',hr,hv,_,_,hw⟩ := vwDeleteend_run (layout := MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h
      (n-nl) (by rw [hdelta]; omega) (by rw [hdelta]; omega)
      (by rw [hdelta]; have := ival_bounds n; omega)
    refine ⟨next,hr,hv.valid,?_,fun _ => ?_,by simp⟩
    · rw [hv.contents,vwWindow_length hv,hnew]
      omega
    · rw [hv.contents,hw,hdelta,← h.contents]
      congr 1
      omega
  | true =>
    simp only [ite_true]
    obtain ⟨next,off',sl',hr,hv,_,_,hw⟩ := vwDeletebeg_run (layout := MemoryLayoutMetadata.ofRuntime l) s a mem off n slots h
      (n-nl) (by rw [hdelta]; omega) (by rw [hdelta]; omega)
    refine ⟨next,hr,hv.valid,?_,by simp,fun _ => ?_⟩
    · rw [hv.contents,vwWindow_length hv,hnew]
      omega
    · rw [hv.contents,hw,hdelta,← h.contents]

theorem resize_native_follows {α : Type} (l : DictLayout) {s : MutableMemory α}
    {a mem : Nat} {off n : I} {slots : List (Option α)}
    (h : VecAt s a mem off n slots) (nl : I) (first : Bool) :
    Follows s (resizePlan l (geometryOf s a) nl.val first)
      ((resize (m := MutationM α) pure mutableLength JuliaLean.base.int.band
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (deletebeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure) (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure)
        a nl first).run s)
      (fun r next => r = a ∧ next.validVector a ∧ ((next.contents a).length : Int) = nl.val ∧
        (first = false → (next.contents a).take (min n.val nl.val).toNat =
          (s.contents a).take (min n.val nl.val).toNat) ∧
        (first = true → (next.contents a).drop (nl.val-min n.val nl.val).toNat =
          (s.contents a).drop (n.val-min n.val nl.val).toNat)) := by
  have hn0 := h.2.2.2.1
  have hglen : ((geometryOf s a).length : Int) = n.val := by
    rw [opusGrowth.VecAt.geometry h]
    simp only
    omega
  have hlen : (s.contents a).length = n.val.toNat := by rw [h.contents,vwWindow_length h]
  rw [resize_native_run s a _ h.1 nl first]
  by_cases hg : n.val < nl.val
  · let delta := JuliaLean.base.int.band (nl-n) (JInt.typemax .i64)
    have hd : delta.val = nl.val-n.val := resize_delta_val h nl hg
    have hplan : resizePlan l (geometryOf s a) nl.val first =
        (if first then growbegPlan else growendPlan) l (geometryOf s a) delta.val.toNat := by
      simp only [resizePlan,hglen,hg,ite_true]
      rw [hd]
    rw [hplan]
    have hc := chosenGrow_follows l h delta (by rw [hd]; omega) first
    simp only [hg,ite_true]
    refine ⟨fun e he => ?_,fun g he => ?_⟩
    · rw [hc.1 e he]
    · obtain ⟨r,next,hr,hvalid,hln,hpre,hsuf⟩ := hc.2 g he
      refine ⟨a,next,?_,rfl,hvalid,by omega,?_,?_⟩
      · rw [hr]
      · intro hf
        rw [show min n.val nl.val = n.val by omega,hpre hf,← hlen,List.take_length]
      · intro hf
        rw [show min n.val nl.val = n.val by omega,show (nl.val-n.val).toNat = delta.val.toNat by rw [hd],
          hsuf hf,Int.sub_self,Int.toNat_zero,List.drop_zero]
  · simp only [hg,ite_false]
    by_cases hneg : nl.val < 0
    · have hne : nl ≠ n := by intro he; rw [he] at hneg; omega
      rw [if_pos hne,if_pos hneg]
      simp only [resizePlan,hglen,hg,ite_false,hneg,ite_true,Follows]
      exact ⟨fun e he => by cases he; rfl,fun g he => by cases he⟩
    · have hnl : 0 ≤ nl.val := by omega
      by_cases heq : nl = n
      · subst nl
        simp only [ne_self_iff_false,ite_false]
        have hplan : ∃ g, resizePlan l (geometryOf s a) n.val first = .ok g := by
          simp only [resizePlan,hglen,show ¬n.val < n.val by omega,ite_false,Int.not_lt.mpr hn0]
          cases first <;> simp
        obtain ⟨g,hg'⟩ := hplan
        rw [hg']
        constructor
        · intro e he
          cases he
        · intro g' he
          refine ⟨a,s,rfl,rfl,h.valid,?_,?_,?_⟩
          · rw [hlen]; omega
          · intro _; rfl
          · intro _; rfl
      · have hstrict : nl.val < n.val := by
          have hnev : nl.val ≠ n.val := by intro hv; exact heq (Subtype.ext hv)
          omega
        rw [if_pos heq,if_neg hneg]
        obtain ⟨next,hr,hvalid,hln,hpre,hsuf⟩ := chosenDelete_result l h nl hnl hstrict first
        rw [hr]
        have hplan : ∃ g, resizePlan l (geometryOf s a) nl.val first = .ok g := by
          simp only [resizePlan,hglen,hg,ite_false,hneg]
          cases first <;> simp
        obtain ⟨g,hg'⟩ := hplan
        rw [hg']
        constructor
        · intro e he
          cases he
        · intro g' he
          refine ⟨a,next,rfl,rfl,hvalid,hln,?_,?_⟩
          · intro hf
            rw [show min n.val nl.val = nl.val by omega,hpre hf,List.take_take]
            simp
          · intro hf
            rw [show min n.val nl.val = nl.val by omega,Int.sub_self,Int.toNat_zero,List.drop_zero,hsuf hf]

theorem resizeSpec : ResizeSpec := by
  intro α l t s a nl first hvalid
  obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
  have hlen : ((s.contents a).length : Int) = n.val := by
    rw [h.contents,vwWindow_length h]
    have := h.2.2.2.1
    omega
  dsimp only
  constructor
  · exact resize_conversion_error s a nl first _ _ _ _
  · intro hlo hhi
    rw [resize_lengthToInt_run,if_pos ⟨hlo,hhi⟩]
    have hv : (JInt.wrap .i64 nl.val).val = nl.val := ival_wrap _ ⟨hlo,hhi⟩
    have hc := resize_native_follows l h (JInt.wrap .i64 nl.val) first
    simpa only [hv,hlen] using hc
end
end solArray
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArray
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
attribute [local irreducible] JInt.wrap wrapInt

 theorem sizehint_conversion_error {α : Type} {t : IntTy} (l : DictLayout)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (sz : JInt t) (first shrink : Bool)
    (growb growe : Nat → I → MutationM α Unit)
    (hsz : ¬ (IntTy.i64.min ≤ sz.val ∧ sz.val ≤ IntTy.i64.max)) :
    (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) lengthToInt growb growe a sz first shrink).run s =
      (.error .inexact,s) := by
  simp only [sizehint,ms_length,ms_ref,ms_memory,stateExcept_bind,
    mutableLength_run s a _ h.1,mutableRef_run s a _ h.1,
    mutableMemLength_run s mem slots h.2.1,lengthToInt,stateExceptLift_run,
    bitinteger_array_conversion,hsz,ite_false]

 theorem sizehint_lengthToInt_run {α : Type} {t : IntTy} (l : DictLayout)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (sz : JInt t) (first shrink : Bool)
    (growb growe : Nat → I → MutationM α Unit) :
    (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) lengthToInt growb growe a sz first shrink).run s =
      if IntTy.i64.min ≤ sz.val ∧ sz.val ≤ IntTy.i64.max then
        (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure growb growe a (JInt.wrap .i64 sz.val) first shrink).run s
      else (.error .inexact,s) := by
  by_cases hsz : IntTy.i64.min ≤ sz.val ∧ sz.val ≤ IntTy.i64.max
  · simp only [hsz,and_self,ite_true,sizehint,ms_length,ms_ref,ms_memory,stateExcept_bind,
      mutableLength_run s a _ h.1,mutableRef_run s a _ h.1,
      mutableMemLength_run s mem slots h.2.1,lengthToInt,stateExceptLift_run,
      bitinteger_array_conversion,stateExcept_pure]
  · rw [if_neg hsz]
    exact sizehint_conversion_error l s a mem off n slots h sz first shrink growb growe hsz

theorem sizehint_unchanged_run {α : Type} (l : DictLayout)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (sz : I) (first shrink : Bool)
    (growb growe : Nat → I → MutationM α Unit)
    (hroom : (max sz n).val ≤ (slots.length : Int))
    (hkeep : shrink = false ∨
      (slots.length : Int) - (max sz n).val ≤ (slots.length : Int) / 8) :
    (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure growb growe a sz first shrink).run s =
      (.ok a,s) := by
  have hcap := h.2.2.2.2.2
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hn0 := h.2.2.2.1
  have hmx := imax_val sz n
  have hb := ival_bounds sz
  have hmxb := ival_bounds (max sz n)
  have hm0 : 0 ≤ (max sz n).val := by
    rw [hmx]
    exact Int.le_trans hn0 (by omega)
  have hd : (JInt.wrap .i64 (slots.length : Int) - max sz n).val =
      (slots.length : Int) - (max sz n).val := by
    rw [ival_sub _ _ (by rw [hL]; omega),hL]
  have hdiv := ms_divide_run (layout := MemoryLayoutMetadata.ofRuntime l) s
    (JInt.wrap .i64 (slots.length : Int)) (JInt.wrap .i64 8) (by rw [wval8]; decide)
  have hq : (JInt.wrap .i64
      ((JInt.wrap .i64 (slots.length : Int)).val.tdiv (JInt.wrap .i64 8).val)).val =
      (slots.length : Int) / 8 := by
    rw [wval8,tdiv_nonneg_val _ 8 (by rw [hL]; omega) (by decide) (by decide),hL]
  have hcond : max sz n ≤ JInt.wrap .i64 (slots.length : Int) := by
    change (max sz n).val ≤ _
    rw [hL]
    exact hroom
  simp only [sizehint,ms_length,ms_ref,ms_memory,stateExcept_bind,
    mutableLength_run s a _ h.1,mutableRef_run s a _ h.1,
    mutableMemLength_run s mem slots h.2.1,stateExcept_pure,hcond,ite_true,hdiv]
  rcases hkeep with hkeep | hkeep
  · simp [hkeep,stateExcept_pure]
  · have hle : JInt.wrap .i64 (slots.length : Int) - max sz n ≤
        JInt.wrap .i64 ((JInt.wrap .i64 (slots.length : Int)).val.tdiv (JInt.wrap .i64 8).val) := by
      change (JInt.wrap .i64 (slots.length : Int) - max sz n).val ≤
        (JInt.wrap .i64 ((JInt.wrap .i64 (slots.length : Int)).val.tdiv (JInt.wrap .i64 8).val)).val
      rw [hd,hq]
      exact hkeep
    simp only [hle,decide_true,Bool.or_true,ite_true,stateExcept_pure]

theorem sizehint_growend_run {α : Type} (l : DictLayout)
    (s next : MutableMemory α) (a mem mem' : Nat) (off n off' : I)
    (slots slots' : List (Option α)) (h : VecAt s a mem off n slots) (sz : I)
    (shrink : Bool)
    (hslow : (slots.length : Int) < (max sz n).val)
    (hnxt : VecAt next a mem' off' (n + (max sz n - n)) slots')
    (hrun : (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
      (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) a (max sz n - n)).run s = (.ok (),next)) :
    (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      a sz false shrink).run s =
      (.ok a,{next with arrays := next.arrays.set a ⟨(mem',off'),n⟩}) := by
  have hcap := h.2.2.2.2.2
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hcond : ¬max sz n ≤ JInt.wrap .i64 (slots.length : Int) := by
    change ¬(max sz n).val ≤ _
    rw [hL]
    omega
  simp only [sizehint,ms_length,ms_ref,ms_memory,stateExcept_bind,
    mutableLength_run s a _ h.1,mutableRef_run s a _ h.1,
    mutableMemLength_run s mem slots h.2.1,stateExcept_pure,hcond,ite_false,
    Bool.false_eq_true,hrun,vwSetSize_run next a mem' off' _ slots' hnxt n]

theorem sizehint_restore_end {α : Type} (s next : MutableMemory α)
    (a mem mem' : Nat) (off n off' delta : I) (slots slots' : List (Option α))
    (h : VecAt s a mem off n slots) (hnxt : VecAt next a mem' off' (n + delta) slots')
    (hd : 0 ≤ delta.val) (hnd : (n + delta).val = n.val + delta.val)
    (hprefix : (vwWindow slots' off' (n + delta)).take n.val.toNat = vwWindow slots off n)
    (harrays : next.arrays = s.arrays.set a ⟨(mem',off'),n + delta⟩) :
    let final : MutableMemory α := {next with arrays := next.arrays.set a ⟨(mem',off'),n⟩}
    final.validVector a ∧ final.contents a = s.contents a ∧
      ∀ other, other ≠ a → final.arrays[other]? = s.arrays[other]? := by
  intro final
  have halt := (List.getElem?_eq_some_iff.mp hnxt.1).choose
  have hn := h.2.2.2.1
  have hv : VecAt final a mem' off' n slots' :=
    ⟨List.getElem?_set_self halt,hnxt.2.1,hnxt.2.2.1,hn,
      by have hh := hnxt.2.2.2.2.1; rw [hnd] at hh; omega,hnxt.2.2.2.2.2⟩
  refine ⟨hv.valid,?_,?_⟩
  · rw [hv.contents,h.contents]
    have ht : (vwWindow slots' off' (n + delta)).take n.val.toNat =
        vwWindow slots' off' n := by
      simp only [vwWindow,List.take_take]
      rw [Nat.min_eq_left (by omega)]
    rw [←ht]
    exact hprefix
  · intro other hne
    change (next.arrays.set a ⟨(mem',off'),n⟩)[other]? = _
    rw [List.getElem?_set_ne (Ne.symm hne),harrays,List.getElem?_set_ne (Ne.symm hne)]

theorem sizehint_shiftref_offset (off delta : I) :
    off + (delta + one) - one = off + delta := by
  apply Subtype.ext
  dsimp only [HAdd.hAdd,Add.add,HSub.hSub,Sub.sub,JInt.wrap]
  unfold JInt.wrap
  change wrapInt .i64 (wrapInt .i64 (off.val + wrapInt .i64 (delta.val + one.val)) - one.val) =
    wrapInt .i64 (off.val + delta.val)
  rw [JuliaLean.Proofs.base.int.wrapInt_sub_left]
  have hassoc : off.val + wrapInt .i64 (delta.val + one.val) - one.val =
      (off.val-one.val) + wrapInt .i64 (delta.val+one.val) := by omega
  rw [hassoc,JuliaLean.Proofs.base.int.wrapInt_add_right]
  congr 1
  omega

theorem sizehint_restore_beg {α : Type} (s next : MutableMemory α)
    (a mem mem' : Nat) (off n off' delta : I) (slots slots' : List (Option α))
    (h : VecAt s a mem off n slots) (hnxt : VecAt next a mem' off' (n + delta) slots')
    (hd : 0 ≤ delta.val) (hnd : (n + delta).val = n.val + delta.val)
    (hoff : (off' + delta).val = off'.val + delta.val)
    (hsuffix : (vwWindow slots' off' (n + delta)).drop delta.val.toNat = vwWindow slots off n)
    (harrays : next.arrays = s.arrays.set a ⟨(mem',off'),n + delta⟩) :
    let final : MutableMemory α := {next with arrays := next.arrays.set a ⟨(mem',off'+delta),n⟩}
    final.validVector a ∧ final.contents a = s.contents a ∧
      ∀ other, other ≠ a → final.arrays[other]? = s.arrays[other]? := by
  intro final
  have halt := (List.getElem?_eq_some_iff.mp hnxt.1).choose
  have hn := h.2.2.2.1
  have hv : VecAt final a mem' (off'+delta) n slots' :=
    ⟨List.getElem?_set_self halt,hnxt.2.1,by rw [hoff]; have := hnxt.2.2.1; omega,hn,
      by rw [hoff]; have hh := hnxt.2.2.2.2.1; rw [hnd] at hh; omega,hnxt.2.2.2.2.2⟩
  refine ⟨hv.valid,?_,?_⟩
  · rw [hv.contents,h.contents]
    have ht : (vwWindow slots' off' (n+delta)).drop delta.val.toNat =
        vwWindow slots' (off'+delta) n := by
      simp only [vwWindow,List.drop_take,List.drop_drop]
      rw [hnd,hoff]
      have ho := hnxt.2.2.1
      congr 2 <;> omega
    rw [←ht]
    exact hsuffix
  · intro other hne
    change (next.arrays.set a ⟨(mem',off'+delta),n⟩)[other]? = _
    rw [List.getElem?_set_ne (Ne.symm hne),harrays,List.getElem?_set_ne (Ne.symm hne)]

theorem sizehint_growbeg_run {α : Type} (l : DictLayout)
    (s next : MutableMemory α) (a mem mem' : Nat) (off n off' : I)
    (slots slots' : List (Option α)) (h : VecAt s a mem off n slots) (sz : I)
    (shrink : Bool)
    (hslow : (slots.length : Int) < (max sz n).val)
    (hnxt : VecAt next a mem' off' (n + (max sz n - n)) slots')
    (hrun : (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
      (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))) a (max sz n - n)).run s = (.ok (),next)) :
    (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      a sz true shrink).run s =
      (.ok a,{next with arrays := next.arrays.set a ⟨(mem',off'+(max sz n - n)),n⟩}) := by
  have hcap := h.2.2.2.2.2
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hcond : ¬max sz n ≤ JInt.wrap .i64 (slots.length : Int) := by
    change ¬(max sz n).val ≤ _
    rw [hL]
    omega
  have halt := (List.getElem?_eq_some_iff.mp hnxt.1).choose
  have hset := ms_setRef_run (layout := MemoryLayoutMetadata.ofRuntime l)
    {next with arrays := next.arrays.set a ⟨(mem',off'),n⟩} a ⟨(mem',off'),n⟩
    (List.getElem?_set_self halt) (mem',off'+(max sz n-n))
  simp only [sizehint,ms_length,ms_ref,ms_memory,ms_shiftref,stateExcept_bind,
    mutableLength_run s a _ h.1,mutableRef_run s a _ h.1,
    mutableMemLength_run s mem slots h.2.1,stateExcept_pure,hcond,ite_false,
    ite_true,hrun,mutableRef_run next a _ hnxt.1,sizehint_shiftref_offset,
    vwSetSize_run next a mem' off' _ slots' hnxt n,hset,List.set_set]

theorem sizehint_grow_error_run {α : Type} (l : DictLayout)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (sz : I) (first shrink : Bool) (e : Error)
    (hslow : (slots.length : Int) < (max sz n).val)
    (hrun : (((if first then
      growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l)))
      else growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      a (max sz n-n)).run s) = (.error e,s)) :
    (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
      (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
      a sz first shrink).run s = (.error e,s) := by
  have hcap := h.2.2.2.2.2
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hcond : ¬max sz n ≤ JInt.wrap .i64 (slots.length : Int) := by
    change ¬(max sz n).val ≤ _
    rw [hL]
    omega
  cases first <;>
    simp only [sizehint,ms_length,ms_ref,ms_memory,stateExcept_bind,
      mutableLength_run s a _ h.1,mutableRef_run s a _ h.1,
      mutableMemLength_run s mem slots h.2.1,stateExcept_pure,hcond,ite_false,
      Bool.false_eq_true,ite_true] at hrun ⊢ <;>
    rw [hrun]

theorem sizehint_growbeg_memlen_bound (l : MemoryLayout) (g out : VectorGeometry) (d : Nat)
    (hmem : g.memlen < maxIntVal) (hrun : growbegPlan l g d = .ok out) :
    out.memlen < maxIntVal := by
  unfold growbegPlan at hrun
  split at hrun
  · cases hrun
    exact hmem
  · split at hrun
    · cases hrun
    · split at hrun
      · cases hrun
        exact hmem
      · unfold growbegInternalPlan at hrun
        split at hrun
        · cases hrun
        · dsimp only at hrun
          split at hrun
          · simp only [Except.map] at hrun
            cases hrun
            exact hmem
          · unfold allocationPlan at hrun
            split at hrun
            · rename_i hfit
              simp only [Except.map] at hrun
              cases hrun
              have := hfit.1
              dsimp only
              omega
            · simp only [Except.map] at hrun
              cases hrun

theorem sizehint_growth_follows {α : Type} (l : DictLayout)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (sz : I) (first shrink : Bool)
    (hslow : (slots.length : Int) < (max sz n).val) :
    Follows s
      (if first then
        (growbegPlan l (geometryOf s a) (max sz n-n).val.toNat).map
          (fun g' => ⟨g'.memlen,g'.offset+(max sz n-n).val.toNat,n.val.toNat⟩)
      else (growendPlan l (geometryOf s a) (max sz n-n).val.toNat).map
          (fun g' => {g' with length := n.val.toNat}))
      ((sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        a sz first shrink).run s)
      (fun r next => r = a ∧ next.validVector a ∧ next.contents a = s.contents a ∧
        ∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) := by
  have hn0 := h.2.2.2.1
  have hmx := imax_val sz n
  have hmb := ival_bounds (max sz n)
  have hdval : (max sz n-n).val = (max sz n).val-n.val :=
    ival_sub _ _ (by omega)
  have hd : 0 ≤ (max sz n-n).val := by rw [hdval]; omega
  have hmemlt : slots.length < maxIntVal := by unfold maxIntVal; omega
  rw [VecAt.geometry h]
  cases first with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    obtain ⟨herr,hok⟩ := growend_plan l h (max sz n-n) hd
    cases hp : growendPlan l ⟨slots.length,off.val.toNat,n.val.toNat⟩
        (max sz n-n).val.toNat with
    | error e =>
      have hr := sizehint_grow_error_run l s a mem off n slots h sz false shrink e hslow (herr e hp)
      simp only [Except.map]
      constructor
      · intro e' he
        cases he
        exact hr
      · intro g he
        cases he
    | ok g =>
      obtain ⟨next,mem',off',slots',hr,hv,ha,hnd,hpre,_⟩ := hok g hp
      have hrestore := sizehint_restore_end s next a mem mem' off n off' (max sz n-n)
        slots slots' h hv hd hnd hpre ha
      have hrun := sizehint_growend_run l s next a mem mem' off n off' slots slots'
        h sz shrink hslow hv hr
      simp only [Except.map]
      constructor
      · intro e he
        cases he
      · intro g' he
        exact ⟨a,_,hrun,rfl,hrestore⟩
  | true =>
    simp only [ite_true]
    obtain ⟨herr,hok⟩ := growbeg_plan l h (max sz n-n) hd
    cases hp : growbegPlan l ⟨slots.length,off.val.toNat,n.val.toNat⟩
        (max sz n-n).val.toNat with
    | error e =>
      have hr := sizehint_grow_error_run l s a mem off n slots h sz true shrink e hslow (herr e hp)
      simp only [Except.map]
      constructor
      · intro e' he
        cases he
        exact hr
      · intro g he
        cases he
    | ok g =>
      obtain ⟨next,mem',off',slots',hr,hv,ha,hnd,hsuf,hgeom,_⟩ := hok g hp
      have hmem := sizehint_growbeg_memlen_bound l _ g (max sz n-n).val.toNat hmemlt hp
      have hlen : slots'.length = g.memlen := by
        rw [VecAt.geometry hv] at hgeom
        exact congrArg VectorGeometry.memlen hgeom
      have hcap : slots'.length < maxIntVal := by rw [hlen]; exact hmem
      have hoff : (off'+(max sz n-n)).val = off'.val+(max sz n-n).val := by
        apply ival_add
        have he := hv.2.2.2.2.1
        rw [hnd] at he
        have ho := hv.2.2.1
        unfold maxIntVal at hcap
        omega
      have hrestore := sizehint_restore_beg s next a mem mem' off n off' (max sz n-n)
        slots slots' h hv hd hnd hoff hsuf ha
      have hrun := sizehint_growbeg_run l s next a mem mem' off n off' slots slots'
        h sz shrink hslow hv hr
      simp only [Except.map]
      constructor
      · intro e he
        cases he
      · intro g' he
        exact ⟨a,_,hrun,rfl,hrestore⟩


theorem sizehint_memlen_div8 (count : Nat) (hcount : count < 2 ^ 63) :
    (JInt.wrap .i64
      ((JInt.wrap .i64 (count : Int)).val.tdiv (JInt.wrap .i64 8).val)).val =
      (count : Int) / 8 := by
  have hc : (JInt.wrap .i64 (count : Int)).val = count := ival_wrap _ (by omega)
  rw [wval8,tdiv_nonneg_val _ 8 (by rw [hc]; omega) (by decide) (by decide),hc]

theorem sizehint_memlen_sub (count : Nat) (hcount : count < 2 ^ 63)
    (target : I) (hlo : 0 ≤ target.val) (hhi : target.val ≤ (count : Int)) :
    (JInt.wrap .i64 (count : Int)-target).val = (count : Int)-target.val := by
  have hc : (JInt.wrap .i64 (count : Int)).val = count := ival_wrap _ (by omega)
  rw [ival_sub _ _ (by rw [hc]; omega),hc]

theorem sizehint_shrink_run {α : Type} (l : DictLayout)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (sz : I) (first : Bool)
    (hroom : (max sz n).val ≤ (slots.length : Int))
    (hshrink : (slots.length : Int) / 8 < (slots.length : Int) - (max sz n).val) :
    let k := (max sz n).val.toNat
    let j := if first && n.val != 0 then max sz n - n + one else one
    (¬memoryFits l k →
      (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        a sz first true).run s = (.error (.argument genericMemorySizeMessage),s)) ∧
    (memoryFits l k → ∃ D : List (Option α),
      (sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        a sz first true).run s =
          (.ok a,{s with
            memories := (s.memories ++ [List.replicate k none]).set s.memories.length D
            arrays := s.arrays.set a ⟨(s.memories.length,j),n⟩}) ∧
      D.length = k ∧ vwWindow D j n = vwWindow slots off n ∧
      1 ≤ j.val ∧ j.val - 1 + n.val ≤ (k : Int)) := by
  intro k j
  have hcap := h.2.2.2.2.2
  have hn0 := h.2.2.2.1
  have ho := h.2.2.1
  have hend := h.2.2.2.2.1
  have hL : (JInt.wrap .i64 (slots.length : Int)).val = slots.length := ival_wrap _ (by omega)
  have hmx := imax_val sz n
  have hbounds := ival_bounds (max sz n)
  have ht0 : 0 ≤ (max sz n).val := by rw [hmx]; omega
  have htn : n.val ≤ (max sz n).val := by rw [hmx]; omega
  have hdiff : (max sz n - n).val = (max sz n).val - n.val :=
    ival_sub _ _ (by omega)
  have hj : 1 ≤ j.val ∧ j.val - 1 + n.val ≤ (k : Int) := by
    dsimp only [j]
    split
    · rename_i hc
      have hnne : n.val ≠ 0 := by
        have hparts : first = true ∧ n.val ≠ 0 := by
          simpa only [Bool.and_eq_true,bne_iff_ne] using hc
        exact hparts.2
      have hv : (max sz n - n + one).val = (max sz n).val - n.val + 1 := by
        rw [ival_add _ _ (by rw [hdiff,ival_one]; omega),hdiff,ival_one]
      rw [hv]
      dsimp only [k]
      omega
    · rw [ival_one]
      dsimp only [k]
      omega
  have hd := sizehint_memlen_sub slots.length hcap (max sz n) ht0 hroom
  have hdiv := ms_divide_run (layout := MemoryLayoutMetadata.ofRuntime l) s
    (JInt.wrap .i64 (slots.length : Int)) (JInt.wrap .i64 8) (by rw [wval8]; decide)
  have hq := sizehint_memlen_div8 slots.length hcap
  have hcond : max sz n ≤ JInt.wrap .i64 (slots.length : Int) := by
    change (max sz n).val ≤ _
    rw [hL]
    exact hroom
  have hlt : ¬JInt.wrap .i64 (slots.length : Int) - max sz n ≤
        JInt.wrap .i64 ((JInt.wrap .i64 (slots.length : Int)).val.tdiv (JInt.wrap .i64 8).val) := by
    change ¬(JInt.wrap .i64 (slots.length : Int) - max sz n).val ≤
      (JInt.wrap .i64 ((JInt.wrap .i64 (slots.length : Int)).val.tdiv (JInt.wrap .i64 8).val)).val
    rw [hd,hq]
    exact Int.not_le_of_gt hshrink
  have hA := arrayNewMemorySpec α l s mem (max sz n)
  simp only at hA
  simp only [sizehint,ms_length,ms_ref,ms_memory,ms_memoryref,ms_copyRef,stateExcept_bind,
    mutableLength_run s a _ h.1,mutableRef_run s a _ h.1,
    mutableMemLength_run s mem slots h.2.1,stateExcept_pure,hcond,ite_true,hdiv,
    Bool.not_true,Bool.false_or,hlt,decide_false,Bool.false_eq_true,ite_false]
  refine ⟨fun hnf => ?_,fun hfit => ?_⟩
  · have hE : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max sz n)).run s =
        (.error (.argument genericMemorySizeMessage),s) := hA.2.1 ht0 hnf
    simp only [hE]
  · have hOk : ((mutableStorage (MemoryLayoutMetadata.ofRuntime l)).allocate mem (max sz n)).run s =
        (.ok s.memories.length,{s with memories := s.memories ++ [List.replicate k none]}) :=
      hA.2.2 ht0 hfit
    have hk63 : k < 2 ^ 63 := by have := hfit.1; unfold maxIntVal at this; omega
    have hmlt := (List.getElem?_eq_some_iff.mp h.2.1).choose
    have halt := (List.getElem?_eq_some_iff.mp h.1).choose
    have hdM : (s.memories ++ [List.replicate k (none : Option α)])[s.memories.length]? =
        some (List.replicate k none) := by simp
    have hsM : (s.memories ++ [List.replicate k (none : Option α)])[mem]? = some slots := by
      rw [List.getElem?_append_left hmlt]
      exact h.2.1
    have hmove := vwMemoryMove_run {s with memories := s.memories ++ [List.replicate k none]}
      s.memories.length mem j off n (List.replicate k none) slots hdM hsM hn0 hj.1
      (by simpa only [List.length_replicate] using hj.2) ho hend
      (by simpa only [List.length_replicate] using hk63)
    simp only [hOk]
    generalize hD : (List.replicate k (none : Option α)).take (j.val - 1).toNat ++
      (slots.drop (off.val - 1).toNat).take n.val.toNat ++
      (List.replicate k (none : Option α)).drop (j.val - 1 + n.val).toNat = D
    have hset := ms_setRef_run (layout := MemoryLayoutMetadata.ofRuntime l)
      {s with memories := (s.memories ++ [List.replicate k none]).set s.memories.length D}
      a ⟨(mem,off),n⟩ h.1 (s.memories.length,j)
    have hpre : ((List.replicate k (none : Option α)).take (j.val - 1).toNat).length =
        (j.val - 1).toNat := by simp only [List.length_take,List.length_replicate]; omega
    have hwin : ((slots.drop (off.val - 1).toNat).take n.val.toNat).length = n.val.toNat := by
      simpa only [vwWindow] using vwWindow_length h
    refine ⟨D,?_,?_,?_,hj.1,hj.2⟩
    · rw [hD] at hmove
      by_cases hc : (first && (n.val != 0)) = true
      all_goals
        simp only [j,hc,Bool.false_eq_true,ite_true,ite_false] at hmove hset ⊢
        simpa only [hmove,hset,stateExcept_bind,stateExcept_pure,List.set_set]
    · rw [←hD]
      rw [List.length_append,List.length_append,hpre,hwin,List.length_drop,List.length_replicate]
      omega
    · rw [vwWindow,←hD,take_three hpre hwin]
      rfl

theorem sizehint_shrink_post {α : Type} (s : MutableMemory α) (a mem : Nat)
    (off n j : I) (slots D : List (Option α)) (k : Nat)
    (h : VecAt s a mem off n slots) (hk : k < 2 ^ 63)
    (hD : D.length = k) (hwin : vwWindow D j n = vwWindow slots off n)
    (hj : 1 ≤ j.val) (hend : j.val-1+n.val ≤ (k : Int)) :
    let final : MutableMemory α := {s with
      memories := (s.memories ++ [List.replicate k none]).set s.memories.length D
      arrays := s.arrays.set a ⟨(s.memories.length,j),n⟩}
    final.validVector a ∧ final.contents a = s.contents a ∧
      ∀ other, other ≠ a → final.arrays[other]? = s.arrays[other]? := by
  intro final
  have halt := (List.getElem?_eq_some_iff.mp h.1).choose
  have hnew : s.memories.length < (s.memories ++ [List.replicate k (none : Option α)]).length := by
    simp only [List.length_append,List.length_singleton]
    omega
  have hv : VecAt final a s.memories.length j n D :=
    ⟨List.getElem?_set_self halt,List.getElem?_set_self hnew,hj,h.2.2.2.1,
      by rw [hD]; exact hend,by rw [hD]; exact hk⟩
  refine ⟨hv.valid,?_,?_⟩
  · rw [hv.contents,h.contents,hwin]
  · intro other hne
    exact List.getElem?_set_ne (Ne.symm hne)

theorem sizehint_shrink_follows {α : Type} (l : DictLayout)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (sz : I) (first : Bool) (g : VectorGeometry)
    (hroom : (max sz n).val ≤ (slots.length : Int))
    (hshrink : (slots.length : Int) / 8 < (slots.length : Int)-(max sz n).val) :
    Follows s (allocationPlan l (max sz n).val.toNat g)
      ((sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        a sz first true).run s)
      (fun r next => r = a ∧ next.validVector a ∧ next.contents a = s.contents a ∧
        ∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) := by
  obtain ⟨herr,hok⟩ := sizehint_shrink_run l s a mem off n slots h sz first hroom hshrink
  by_cases hfit : memoryFits l (max sz n).val.toNat
  · obtain ⟨D,hrun,hlen,hwin,hj,hend⟩ := hok hfit
    have hk : (max sz n).val.toNat < 2 ^ 63 := by
      have := hfit.1
      unfold maxIntVal at this
      omega
    have hpost := sizehint_shrink_post s a mem off n _ slots D _ h hk hlen hwin hj hend
    simp only [allocationPlan,hfit,ite_true]
    constructor
    · intro e he
      cases he
    · intro g' he
      exact ⟨a,_,hrun,rfl,hpost⟩
  · simp only [allocationPlan,hfit,ite_false]
    constructor
    · intro e he
      cases he
      exact herr hfit
    · intro g' he
      cases he


theorem sizehint_native_follows {α : Type} (l : DictLayout)
    (s : MutableMemory α) (a mem : Nat) (off n : I) (slots : List (Option α))
    (h : VecAt s a mem off n slots) (sz : I) (first shrink : Bool) :
    Follows s (sizehintPlan l (geometryOf s a) sz.val first shrink)
      ((sizehint (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure
        (growbeg (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growbegInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        (growend (mutableStorage (MemoryLayoutMetadata.ofRuntime l)) pure (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime l))))
        a sz first shrink).run s)
      (fun r next => r = a ∧ next.validVector a ∧ next.contents a = s.contents a ∧
        ∀ other, other ≠ a → next.arrays[other]? = s.arrays[other]?) := by
  have hn0 := h.2.2.2.1
  have hmx := imax_val sz n
  have hmb := ival_bounds (max sz n)
  have ht : (max sz n).val.toNat = max sz.val.toNat n.val.toNat := by rw [hmx]; omega
  have hdval : (max sz n-n).val = (max sz n).val-n.val := ival_sub _ _ (by omega)
  have hd : (max sz n-n).val.toNat = (max sz n).val.toNat-n.val.toNat := by
    rw [hdval]
    omega
  simp only [VecAt.geometry h,sizehintPlan]
  rw [←ht,←hd]
  by_cases hroom : (max sz n).val ≤ (slots.length : Int)
  · have hroomN : (max sz n).val.toNat ≤ slots.length := by omega
    rw [if_pos hroomN]
    by_cases hkeep : (!shrink || slots.length-(max sz n).val.toNat ≤ slots.length/8) = true
    · rw [if_pos hkeep]
      have hkeep' : shrink = false ∨
          (slots.length : Int)-(max sz n).val ≤ (slots.length : Int)/8 := by
        cases hs : shrink with
        | false => exact Or.inl rfl
        | true =>
          right
          simp only [hs,Bool.not_true,Bool.false_or,decide_eq_true_eq] at hkeep
          omega
      rw [sizehint_unchanged_run l s a mem off n slots h sz first shrink _ _ hroom hkeep']
      constructor
      · intro e he
        cases he
      · intro g he
        exact ⟨a,s,rfl,rfl,h.valid,rfl,fun _ _ => rfl⟩
    · rw [if_neg hkeep]
      have hs : shrink = true := by
        cases hh : shrink with
        | false => simp only [hh,Bool.not_false,Bool.true_or] at hkeep; contradiction
        | true => rfl
      have hshrink : (slots.length : Int)/8 < (slots.length : Int)-(max sz n).val := by
        simp only [hs,Bool.not_true,Bool.false_or,decide_eq_true_eq] at hkeep
        omega
      rw [hs]
      exact sizehint_shrink_follows l s a mem off n slots h sz first _ hroom hshrink
  · have hslow : (slots.length : Int) < (max sz n).val := by omega
    have hroomN : ¬(max sz n).val.toNat ≤ slots.length := by omega
    rw [if_neg hroomN]
    have hg := sizehint_growth_follows l s a mem off n slots h sz first shrink hslow
    simpa only [VecAt.geometry h] using hg

theorem sizehintSpec : SizehintSpec := by
  intro α l t s a sz first shrink hvalid
  obtain ⟨mem,off,n,slots,h⟩ := validVector_vecAt hvalid
  constructor
  · exact sizehint_conversion_error l s a mem off n slots h sz first shrink _ _
  · intro hlo hhi
    rw [sizehint_lengthToInt_run l s a mem off n slots h sz first shrink _ _,if_pos ⟨hlo,hhi⟩]
    have hw : (JInt.wrap .i64 sz.val).val = sz.val := ival_wrap _ ⟨hlo,hhi⟩
    have hn := sizehint_native_follows l s a mem off n slots h (JInt.wrap .i64 sz.val) first shrink
    simpa only [hw] using hn
end solArray
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

theorem growat_native_negative (layout : MemoryLayoutMetadata) (s : MutableMemory α) (a : Nat)
    (v : MutableVector) (ha : s.arrays[a]? = some v) (i d : I) (hd : d.val < 0) :
    (growat (mutableStorage layout) pure pure
      (growbeg (mutableStorage layout) pure (growbegInternal (mutableStorage layout)))
      (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout))) a i d).run s =
      (.error (.argument "grow requires delta >= 0"),s) := by
  by_cases hi1 : i = one
  · subst i
    simp only [growat_one_eq]
    exact vwGrowbeg_negative (layout := layout) s a d hd
  · have hneg : ¬ d ≥ zero := by rw [ge_iff_le,jle_iff,ival_zero]; omega
    by_cases hend : (decide (v.size < JInt.typemax .i64) && decide (i = v.size+one)) = true
    · simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,ms_length,
        mutableLength_run s a v ha,hend,ite_true]
      exact growend_neg_run (layout := layout) s a d hd
    · simp only [growat,stateExcept_bind,stateExcept_pure,hi1,ite_false,ms_length,
        mutableLength_run s a v ha,hend,Bool.false_eq_true,hneg,decide_false,Bool.not_false,ite_true,ite_false,stateExcept_throw]
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

/-- Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable. -/
def GrowbegConversionFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref Z : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) (before : NativeGrowthWorld State T),
    FirstNativeFailure (toInt delta)
      (JuliaLean.base.array.Completion3.growbeg layout elementType native ccall allocation access references
        toInt a delta) before

/-- Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable. -/
def GrowendConversionFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref Z : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) (before : NativeGrowthWorld State T),
    FirstNativeFailure (toInt delta)
      (JuliaLean.base.array.Completion3.growend layout elementType native ccall allocation access references
        toInt a delta) before

/-- Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable. -/
def DeletebegConversionFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref Z : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) (before : NativeGrowthWorld State T),
    FirstNativeFailure (toInt delta)
      (JuliaLean.base.array.Completion3.deletebeg layout elementType native ccall allocation access references
        toInt a delta) before

/-- Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable. -/
def DeleteendConversionFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref Z : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) (before : NativeGrowthWorld State T),
    FirstNativeFailure (toInt delta)
      (JuliaLean.base.array.Completion3.deleteend layout elementType native ccall allocation access references
        toInt a delta) before
end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion5
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion5
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

/-- Grow-at converts delta before index, header inspection or allocation,
retaining every conversion error, partial native state and divergence. -/
def GrowatConversionFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref Z Index : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (toDeltaInt : Z → NativeGrowthM State T I) (toIndexInt : Index → NativeGrowthM State T I)
    (a : Nat) (index : Index) (delta : Z) (before : NativeGrowthWorld State T),
    FirstNativeFailure (toDeltaInt delta)
      (growat layout elementType native ccall allocation access references toDeltaInt toIndexInt a index delta) before
end JuliaLean.Proofs.base.array.Completion5


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Overflow in the first checked length addition precedes allocation, copying,
unsetting and header writes. Successful beginning growth returns the reference
actually installed in the final header. These invariants quantify over every
native delta/length and every supplied native boundary, without native laws.
Source: base/array.jl:1116-1149. -/
def GrowbegEarlyOverflowAndReturnInvariant : Prop :=
  ∀ (State T V D N Mod P Sym Ref : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove)
    (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (handle : Nat) (delta len : I) (before : NativeGrowthWorld State T),
    let result := NativeCopyObserve
      (nativeGrowbegInternal layout elementType native ccall allocation access references handle delta len) before
    ((len.val + delta.val < -(2 : Int) ^ 63 ∨ (2 : Int) ^ 63 ≤ len.val + delta.val) →
      ∃ message, result = some (.error (.inr (.inr (.jl (.overflowError message))), before))) ∧
    (∀ returned after, result = some (.ok (returned, after)) →
      (after.other.headers handle).reference = returned)

/-- Ending growth must reject an overflowing mathematical new length before
any native effect. No nonnegative-delta, success or finite-copy assumption is
imposed. Source: base/array.jl:1171-1210. -/
def GrowendEarlyOverflowInvariant : Prop :=
  ∀ (State T V D N Mod P Sym Ref : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove)
    (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (handle : Nat) (delta len : I) (before : NativeGrowthWorld State T),
    (len.val + delta.val < -(2 : Int) ^ 63 ∨ (2 : Int) ^ 63 ≤ len.val + delta.val) →
      ∃ message, NativeCopyObserve
        (nativeGrowendInternal layout elementType native ccall allocation access references handle delta len) before =
        some (.error (.inr (.inr (.jl (.overflowError message))), before))
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.MemSafetyRetired

open JuliaLean JuliaLean.base.array

/-- Checked storage primitives detect invalid copy and clearing spans, while the
final vector invariant includes the reference and complete live storage window. -/
def GrowbegPublicSafety : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (before : MutableMemory α)
    (handle : Nat) (delta : I), before.validVector handle → 0 ≤ delta.val →
    let result := (growbeg (mutableStorage layout) pure
      (growbegInternal (mutableStorage layout)) handle delta).run before
    (∀ after, result ≠ (.error .bounds, after)) ∧
    (∀ after, result = (.ok (), after) → after.validVector handle)

def GrowendPublicSafety : Prop :=
  ∀ (α : Type) (layout : MemoryLayoutMetadata) (before : MutableMemory α)
    (handle : Nat) (delta : I), before.validVector handle → 0 ≤ delta.val →
    let result := (growend (mutableStorage layout) pure
      (growendInternal (mutableStorage layout)) handle delta).run before
    (∀ after, result ≠ (.error .bounds, after)) ∧
    (∀ after, result = (.ok (), after) → after.validVector handle)
end JuliaLean.Proofs.base.array.MemSafetyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.MemSafetyRetired

open JuliaLean JuliaLean.base.array

open JuliaLean.Registry
def entriesResize1 : List JuliaLean.Registry.Entry := [
  { id := "memsafety-array-growbeg-accesses", juliaFile := "base/array.jl"
    juliaFns := ["_growbeg!", "_growbeg_internal!"]
    statement := "Every unchecked reference, copy span, and clearing index reached from valid public grow-begin calls is in bounds."
    source := "base/array.jl:1116-1168"
    status := .todo, prop := ``GrowbegPublicSafety
    notes := "The installed growbeg/growbegInternal methods use native checked arithmetic and the real mutableStorage model. Excluding bounds failures and preserving the live-window invariant still need proofs; native Core memoryref pointer extents require a further memory-domain connection." },
  { id := "memsafety-array-growend-accesses", juliaFile := "base/array.jl"
    juliaFns := ["_growend!", "_growend_internal!"]
    statement := "Every unchecked reference, copy span, and clearing index reached from valid public grow-end calls is in bounds."
    source := "base/array.jl:1171-1222"
    status := .todo, prop := ``GrowendPublicSafety
    notes := "The installed growend/growendInternal methods use native checked arithmetic and the real mutableStorage model. Excluding bounds failures and preserving the live-window invariant still need proofs; native Core memoryref pointer extents require a further memory-domain connection." }
]
end JuliaLean.Proofs.base.array.MemSafetyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesResize2 : List JuliaLean.Registry.Entry := [
  { id := "array-empty-clears", juliaFile := "base/array.jl",
    juliaFns := ["empty!(::Vector)"],
    statement := "empty!(a) removes every element of a valid vector, which stays valid.",
    source := "base/array.jl:2150-2153; empty! contract",
    status := .proven, prop := ``EmptySpec, thm := some ``emptySpec}
]
def entriesResize3 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-resize", juliaFile := "base/array.jl",
    juliaFns := ["resize!(::Vector, ::Integer; first)"],
    statement := "resize!(a, n; first) for n of any BitInteger type throws InexactError when n is not an Int and ArgumentError when n < 0, with a untouched, and otherwise yields a valid vector of length n keeping the first (first=false) or last (first=true) min(n, length(a)) old elements; the memory length plus 2n+1 must be an Int.",
    source := "base/array.jl:1522-1558 (docstring),1559-1574",
    status := .proven, prop := ``ResizeSpec, thm := some ``solArray.resizeSpec}
]
def entriesResize4 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-sizehint-first-empty", juliaFile := "base/array.jl",
    juliaFns := ["sizehint!(a::Vector, sz::Integer; first::Bool=false, shrink::Bool=true)"],
    statement := "sizehint!(a, sz; first, shrink) for sz of any BitInteger type raises InexactError when sz is not an Int value, and otherwise returns a with exactly the same elements in a valid vector, whether it shrinks, grows at the front or end, or leaves the memory, with no other header changed.",
    source := "base/array.jl:1574-1645 (sizehint! docstring)", status := .proven, prop := ``SizehintSpec, thm := some ``solArray.sizehintSpec }
]
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion3.GrowbegConversionFailures_proven : JuliaLean.Proofs.base.array.Completion3.GrowbegConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion3.GrowbegConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion3.growbeg, JuliaLean.base.array.growbeg]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion3.GrowendConversionFailures_proven : JuliaLean.Proofs.base.array.Completion3.GrowendConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion3.GrowendConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion3.growend, JuliaLean.base.array.growend]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion3.DeletebegConversionFailures_proven : JuliaLean.Proofs.base.array.Completion3.DeletebegConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion3.DeletebegConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion3.deletebeg, JuliaLean.base.array.deletebeg]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion3.DeleteendConversionFailures_proven : JuliaLean.Proofs.base.array.Completion3.DeleteendConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion3.DeleteendConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion3.deleteend, JuliaLean.base.array.deleteend]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion5.GrowatConversionFailures_proven : JuliaLean.Proofs.base.array.Completion5.GrowatConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion5.GrowatConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion5.growat]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


namespace JuliaLean.Proofs.base.array
def entriesResize5 : List JuliaLean.Registry.Entry := [
{ id := "array-growbeg-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["_growbeg!(a::Vector, delta::Integer)"],
  statement := "Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable.",
  source := "base/array.jl:1151-1169", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.GrowbegConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.GrowbegConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-growend-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["_growend!(a::Vector, delta::Integer)"],
  statement := "Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable.",
  source := "base/array.jl:1212-1223", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.GrowendConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.GrowendConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-deletebeg-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["_deletebeg!(a::Vector, delta::Integer)"],
  statement := "Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable.",
  source := "base/array.jl:1273-1290", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.DeletebegConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.DeletebegConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-deleteend-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["_deleteend!(a::Vector, delta::Integer)"],
  statement := "Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable.",
  source := "base/array.jl:1291-1306", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.DeleteendConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.DeleteendConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesResize6 : List JuliaLean.Registry.Entry := [
{ id := "array-growat-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["_growat!(a::Vector, i::Integer, delta::Integer)"],
  statement := "Grow-at converts delta before index, header inspection or allocation, retaining every conversion error, partial native state and divergence.",
  source := "base/array.jl:1225-1270", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion5.GrowatConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion5.GrowatConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean.Registry
def entriesResize7 : List JuliaLean.Registry.Entry := [
  { id := "array-growbeg-overflow-return", juliaFile := "base/array.jl",
    juliaFns := ["_growbeg_internal!(a::Vector, delta::Int, len::Int)"],
    statement := "For all native delta and length values, initial checked length overflow raises OverflowError before mutation; every successful beginning growth returns the reference installed in the final header.",
    source := "base/array.jl:1116-1149", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.GrowbegEarlyOverflowAndReturnInvariant, thm := none },
  { id := "array-growend-overflow", juliaFile := "base/array.jl",
    juliaFns := ["_growend_internal!(a::Vector, delta::Int, len::Int)"],
    statement := "For all native delta and length values, initial checked length overflow in ending growth raises OverflowError before any mutation or native effect.",
    source := "base/array.jl:1171-1210", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.GrowendEarlyOverflowInvariant, thm := none }
]
end JuliaLean.Proofs.base.array

