import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.Channels

set_option maxRecDepth 4096

private abbrev ti (x : Int) : JInt .i64 := JInt.lit .i64 x

private theorem threads_bind {α β : Type} (a : α) (g : α → Jl β) :
    ((.ok a : Jl α) >>= g) = g a := rfl

private theorem threads_pure {α : Type} (a : α) : (pure a : Jl α) = .ok a := rfl

/-- `base/threadingconstructs.jl:498-509` (master): the wrapping endpoint
arithmetic after the short-range branch of `_work_distribution_code`. -/
def threadsEndpoints (f len rem tid : JInt .i64) : JInt .i64 × JInt .i64 :=
  let loop_first := f + ((tid - ti 1) * len)
  let loop_last := loop_first + len - ti 1
  if rem.val > 0 then
    if tid ≤ rem then (loop_first + (tid - ti 1), loop_last + tid)
    else (loop_first + rem, loop_last + rem)
  else (loop_first, loop_last)

/-- `base/threadingconstructs.jl:484-510` (master): checked `divrem`, the
short-range return, and the endpoint arithmetic, in source order. -/
def threadsWorkDistribution (f lenr n tid : JInt .i64) :
    Jl (Option (JInt .i64 × JInt .i64)) := do
  let len ← JInt.div lenr n
  let rem ← JInt.remInt lenr n
  if len.val = 0 then
    if tid > rem then return none
    else return some (threadsEndpoints f (ti 1) (ti 0) tid)
  else return some (threadsEndpoints f len rem tid)

/-- Mathematical observation of a Julia `UnitRange`, `base/threadingconstructs.jl:520`:
its values increase by one, and it is empty when the last endpoint is smaller. -/
def threadsUnitRange (first last : JInt .i64) : List Int :=
  (List.range (last.val - first.val + 1).toNat).map (fun k : Nat => first.val + (k : Int))

/-- `base/threadingconstructs.jl:491-520` (master): one task returns immediately
or iterates its inclusive Julia `UnitRange`. Errors remain observable. -/
def threadsIterations (f lenr n tid : JInt .i64) : Jl (List Int) := do
  let bounds ← threadsWorkDistribution f lenr n tid
  return match bounds with
    | none => []
    | some (first, last) => threadsUnitRange first last

/-- Task-order concatenation for tids `1,...,count`. This is an observation of
`base/threadingconstructs.jl:498-520`, not a claim about execution order. -/
def threadsPrefix (f lenr n : JInt .i64) : Nat → Jl (List Int)
  | 0 => .ok []
  | k + 1 => do
    let earlier ← threadsPrefix f lenr n k
    let current ← threadsIterations f lenr n (ti ((k : Int) + 1))
    return earlier ++ current

/-- Each source index occurs exactly once in the concatenation of task ranges,
in increasing task order. The upper endpoint condition uses mathematical
integers, including when intermediate machine arithmetic wraps. -/
def ThreadsPartition : Prop :=
  ∀ (f lenr n : JInt .i64),
    0 ≤ lenr.val → 1 ≤ n.val →
    f.val + lenr.val - 1 ≤ IntTy.i64.max →
    threadsPrefix f lenr n n.val.toNat =
      .ok ((List.range lenr.val.toNat).map (fun k : Nat => f.val + (k : Int)))

private theorem ti_val (x : Int) (h : IntTy.i64.min ≤ x ∧ x ≤ IntTy.i64.max) :
    (ti x).val = x := wrapInt_of_inRange .i64 x h

private theorem one_val : (ti 1).val = 1 := by decide
private theorem zero_val : (ti 0).val = 0 := by decide

private theorem add_val (a b : JInt .i64)
    (h : IntTy.i64.min ≤ a.val + b.val ∧ a.val + b.val ≤ IntTy.i64.max) :
    (a + b).val = a.val + b.val := wrapInt_of_inRange .i64 _ h

private theorem end_val (a b : JInt .i64)
    (h : IntTy.i64.min ≤ a.val + b.val - 1 ∧
      a.val + b.val - 1 ≤ IntTy.i64.max) :
    (a + b - ti 1).val = a.val + b.val - 1 := by
  change wrapInt .i64 (wrapInt .i64 (a.val + b.val) - (ti 1).val) = _
  rw [one_val]
  change -(9223372036854775808 : Int) ≤ a.val + b.val - 1 ∧
    a.val + b.val - 1 ≤ 9223372036854775807 at h
  change (((a.val + b.val + 9223372036854775808) % 18446744073709551616 -
    9223372036854775808 - 1 + 9223372036854775808) % 18446744073709551616 -
    9223372036854775808) = a.val + b.val - 1
  omega

private def boundary (q r : Int) (k : Nat) : Int :=
  (k : Int) * q + min (k : Int) r

private theorem boundary_zero (q r : Int) (hr : 0 ≤ r) : boundary q r 0 = 0 := by
  simp only [boundary, Int.natCast_zero, Int.zero_mul, Int.zero_add]
  omega

private theorem boundary_mono (q r : Int) (hq : 0 ≤ q) (a b : Nat) (hab : a ≤ b) :
    boundary q r a ≤ boundary q r b := by
  have hm := Int.mul_le_mul_of_nonneg_right (show (a : Int) ≤ b by omega) hq
  unfold boundary
  omega

private theorem endpoints_exact (f q r tid : JInt .i64) (k : Nat)
    (ht : tid.val = (k : Int)+1) (hq : 1 ≤ q.val) (hr : 0 ≤ r.val)
    (hp : (k : Int)*q.val + q.val + r.val ≤ IntTy.i64.max)
    (hf : f.val + ((k : Int)*q.val + q.val + r.val) - 1 ≤ IntTy.i64.max) :
    (threadsEndpoints f q r tid).1.val = f.val + boundary q.val r.val k ∧
    (threadsEndpoints f q r tid).2.val = f.val + boundary q.val r.val (k+1) - 1 := by
  have hk : 0 ≤ (k : Int) := by omega
  have hprod : 0 ≤ (k : Int)*q.val := Int.mul_nonneg hk (by omega)
  have ht0 : (tid - ti 1).val = (k : Int) := by
    change wrapInt .i64 (tid.val - (ti 1).val) = _
    rw [one_val, ht]
    simp only [Int.add_sub_cancel]
    apply wrapInt_of_inRange
    have hb := tid.property
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
    omega
  have hp0 : ((tid - ti 1)*q).val = (k : Int)*q.val := by
    change wrapInt .i64 ((tid-ti 1).val*q.val) = _
    rw [ht0]
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hp ⊢
    omega
  have hfirst : (f + ((tid-ti 1)*q)).val = f.val + (k : Int)*q.val := by
    rw [add_val]
    · rw [hp0]
    · rw [hp0]
      have hb := f.property
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb hf ⊢
      omega
  have hlast : (f + ((tid-ti 1)*q) + q - ti 1).val =
      f.val + (k : Int)*q.val + q.val - 1 := by
    rw [end_val]
    · rw [hfirst]
    · rw [hfirst]
      have hb := f.property
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb hf ⊢
      omega
  unfold threadsEndpoints
  by_cases hr0 : 0 < r.val
  · rw [if_pos hr0]
    by_cases htr : tid ≤ r
    · rw [if_pos htr]
      change tid.val ≤ r.val at htr
      simp only [boundary, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
      constructor
      · rw [add_val]
        · rw [hfirst, ht0]; omega
        · rw [hfirst, ht0]
          have hb := f.property
          simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb hf ⊢
          omega
      · rw [add_val]
        · rw [hlast, ht]; omega
        · rw [hlast, ht]
          have hb := f.property
          simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb hf ⊢
          omega
    · rw [if_neg htr]
      change ¬ tid.val ≤ r.val at htr
      simp only [boundary, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
      constructor
      · rw [add_val]
        · rw [hfirst]; omega
        · rw [hfirst]
          have hb := f.property
          simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb hf ⊢
          omega
      · rw [add_val]
        · rw [hlast]; omega
        · rw [hlast]
          have hb := f.property
          simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb hf ⊢
          omega
  · rw [if_neg hr0]
    simp only [hfirst, hlast, boundary, Int.natCast_add, Int.natCast_one,
      Int.add_mul, Int.one_mul]
    omega

private def segment (f : Int) (a b : Int) : List Int :=
  (List.range (b-a).toNat).map (fun k : Nat => f+a+(k : Int))

private theorem segment_append (f a b c : Int) (hab : a ≤ b) (hbc : b ≤ c) :
    segment f a b ++ segment f b c = segment f a c := by
  unfold segment
  have he : (c-a).toNat = (b-a).toNat + (c-b).toNat := by omega
  rw [he, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_def, Int.natCast_add]
  omega

private theorem distribution_divrem (lenr n : JInt .i64)
    (hl : 0 ≤ lenr.val) (hn : 1 ≤ n.val) :
    ∃ q r : JInt .i64, JInt.div lenr n = .ok q ∧
      JInt.remInt lenr n = .ok r ∧
      0 ≤ q.val ∧ 0 ≤ r.val ∧ r.val < n.val ∧
      q.val * n.val + r.val = lenr.val := by
  have hq0 := Int.ediv_nonneg hl (show 0 ≤ n.val by omega)
  have hq1 := Int.ediv_le_self n.val hl
  have hr0 := Int.emod_nonneg lenr.val (show n.val ≠ 0 by omega)
  have hr1 := Int.emod_lt_of_pos lenr.val (show 0 < n.val by omega)
  have hq : (JInt.wrap .i64 (lenr.val / n.val)).val = lenr.val / n.val := by
    change wrapInt .i64 (lenr.val / n.val) = _
    apply wrapInt_of_inRange
    have hb := lenr.property
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
    omega
  have hr : (JInt.wrap .i64 (lenr.val % n.val)).val = lenr.val % n.val := by
    change wrapInt .i64 (lenr.val % n.val) = _
    apply wrapInt_of_inRange
    have hb := n.property
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
    omega
  refine ⟨JInt.wrap .i64 (lenr.val / n.val), JInt.wrap .i64 (lenr.val % n.val), ?_, ?_, ?_⟩
  · simp only [JInt.div, show n.val ≠ 0 by omega, ↓reduceIte,
      Int.tdiv_eq_ediv_of_nonneg hl]
    rw [if_neg (by intro h; omega)]
  · simp [JInt.remInt, show n.val ≠ 0 by omega, Int.tmod_eq_emod_of_nonneg hl]
  · simp only [hq, hr]
    exact ⟨hq0, hr0, hr1, by
      have he := Int.emod_add_ediv_mul lenr.val n.val
      omega⟩

private theorem iteration_exact (f lenr n q r : JInt .i64)
    (hl : 0 ≤ lenr.val) (hn : 1 ≤ n.val)
    (hf : f.val + lenr.val - 1 ≤ IntTy.i64.max)
    (hd : JInt.div lenr n = .ok q) (hrm : JInt.remInt lenr n = .ok r)
    (hq : 0 ≤ q.val) (hr : 0 ≤ r.val) (hrn : r.val < n.val)
    (he : q.val*n.val+r.val = lenr.val)
    (k : Nat) (hk : (k : Int) < n.val) :
    threadsIterations f lenr n (ti ((k : Int)+1)) =
      .ok (segment f.val (boundary q.val r.val k) (boundary q.val r.val (k+1))) := by
  have ht : (ti ((k : Int)+1)).val = (k : Int)+1 := by
    apply ti_val
    have hb := n.property
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
    omega
  unfold threadsIterations threadsWorkDistribution
  simp only [hd, hrm, threads_bind]
  by_cases hq0 : q.val = 0
  · rw [if_pos hq0]
    by_cases hkr : ti ((k : Int)+1) > r
    · rw [if_pos hkr]
      simp only [threads_pure, threads_bind]
      change r.val < (ti ((k : Int)+1)).val at hkr
      simp only [segment, boundary, hq0, Int.mul_zero, Int.zero_add]
      have hz : (min ((k : Int)+1) r.val - min (k : Int) r.val).toNat = 0 := by omega
      simpa [hz]
    · rw [if_neg hkr]
      simp only [threads_pure, threads_bind]
      change ¬ r.val < (ti ((k : Int)+1)).val at hkr
      rw [ht] at hkr
      have hlen : r.val = lenr.val := by
        simpa only [hq0, Int.zero_mul, Int.zero_add] using he
      change (Except.ok (threadsUnitRange
        (threadsEndpoints f (ti 1) (ti 0) (ti ((k : Int)+1))).1
        (threadsEndpoints f (ti 1) (ti 0) (ti ((k : Int)+1))).2) : Jl (List Int)) = _
      have hend := endpoints_exact f (ti 1) (ti 0) (ti ((k : Int)+1)) k ht
        (by rw [one_val]; omega) (by rw [zero_val]; omega)
        (by
          simp only [one_val, zero_val, Int.mul_one, Int.add_zero]
          have hb := lenr.property
          change -(9223372036854775808 : Int) ≤ lenr.val ∧ lenr.val ≤ 9223372036854775807 at hb
          change (k : Int) + 1 ≤ (9223372036854775807 : Int)
          omega)
        (by
          simp only [one_val, zero_val, Int.mul_one, Int.add_zero]
          omega)
      have hs : (threadsEndpoints f (ti 1) (ti 0) (ti ((k : Int)+1))).1.val = f.val + (k : Int) := by
        rw [hend.1]
        simp only [boundary, one_val, zero_val, Int.mul_one]
        omega
      have he' : (threadsEndpoints f (ti 1) (ti 0) (ti ((k : Int)+1))).2.val = f.val + (k : Int) := by
        rw [hend.2]
        simp only [boundary, one_val, zero_val, Int.mul_one, Int.natCast_add, Int.natCast_one]
        omega
      have hb0 : boundary q.val r.val k = (k : Int) := by
        simp only [boundary, hq0, Int.mul_zero, Int.zero_add]
        omega
      have hb1 : boundary q.val r.val (k+1) = (k : Int)+1 := by
        simp only [boundary, hq0, Int.mul_zero, Int.zero_add, Int.natCast_add, Int.natCast_one]
        omega
      simp only [threadsUnitRange, hs, he', hb0, hb1, segment]
      have hc : (f.val + (k : Int) - (f.val + (k : Int)) + 1).toNat = 1 := by omega
      have hc' : ((k : Int)+1-(k : Int)).toNat = 1 := by omega
      rw [hc, hc']
  · rw [if_neg hq0]
    simp only [threads_pure, threads_bind]
    have hm := Int.mul_le_mul_of_nonneg_right (show (k : Int)+1 ≤ n.val by omega) hq
    have hkp : (k : Int)*q.val+q.val+r.val ≤ lenr.val := by
      rw [Int.add_mul, Int.one_mul] at hm
      rw [Int.mul_comm n.val q.val] at hm
      omega
    have hend := endpoints_exact f q r (ti ((k : Int)+1)) k ht (by omega) hr
      (by have hb := lenr.property; omega) (by omega)
    change (Except.ok (threadsUnitRange (threadsEndpoints f q r (ti ((k : Int)+1))).1
      (threadsEndpoints f q r (ti ((k : Int)+1))).2) : Jl (List Int)) = _
    simp only [threadsUnitRange, hend.1, hend.2, segment]
    have hc : (f.val + boundary q.val r.val (k+1) - 1 -
      (f.val + boundary q.val r.val k) + 1).toNat =
      (boundary q.val r.val (k+1) - boundary q.val r.val k).toNat := by omega
    rw [hc]

/-- Task ranges partition all indices, despite wrapping intermediate additions.
`base/threadingconstructs.jl:484-520,572-576` (master). -/
theorem threadsPartition : ThreadsPartition := by
  intro f lenr n hl hn hf
  obtain ⟨q, r, hd, hrm, hq, hr, hrn, he⟩ := distribution_divrem lenr n hl hn
  have hzero := boundary_zero q.val r.val hr
  have hp : ∀ k : Nat, (k : Int) ≤ n.val →
      threadsPrefix f lenr n k = .ok (segment f.val 0 (boundary q.val r.val k)) := by
    intro k
    induction k with
    | zero => simp [threadsPrefix, hzero, segment]
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hit := iteration_exact f lenr n q r hl hn hf hd hrm hq hr hrn he k (by omega)
      simp only [threadsPrefix, hi, hit, threads_bind, threads_pure]
      rw [segment_append]
      · have h := boundary_mono q.val r.val hq 0 k (by omega); omega
      · exact boundary_mono q.val r.val hq k (k+1) (by omega)
  rw [hp n.val.toNat (by omega)]
  have hend : boundary q.val r.val n.val.toNat = lenr.val := by
    have hcast : (n.val.toNat : Int) = n.val := Int.toNat_of_nonneg (by omega)
    unfold boundary
    rw [hcast, Int.min_eq_right (by omega), Int.mul_comm]
    exact he
  simp [hend, segment]


def threadsEntries : List JuliaLean.Registry.Entry := [
  { id := "channels-threads-partition"
    juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["_work_distribution_code", "default_func", "threading_run", "@threads :static/:dynamic"]
    statement := "For every representable nonnegative iteration count, positive thread count, and representable inclusive index range, concatenating the per-task UnitRanges for tids 1 through n visits exactly the original index list, once each and in order."
    source := "base/threadingconstructs.jl:572-576 (master): 'The iteration space is distributed to coarse-grained tasks'; 'execution of the loop waits for the evaluation of all iterations'; invariant: each iteration runs once. Task-order concatenation does not assert temporal execution order."
    status := .proven
    prop := ``JuliaLean.Channels.ThreadsPartition
    thm := some ``JuliaLean.Channels.threadsPartition
    notes := "Master bbfa0ce4150 factors the arithmetic into _work_distribution_code at lines 484-510. Julia 1.13.2 has the same divrem, short-range branch, and wrapping endpoint arithmetic inline in default_func within the _threadsfor expansion, lines 266-286; its additional onethread path is outside this threadpool partition model. No practical upper bound on threadpoolsize is assumed beyond the Int64 input type and n >= 1. Intermediate loop_first + len may wrap at typemax+1; the proof establishes exact final endpoints. Ordered concatenation is the indexing invariant used by the comprehension path, not a scheduling guarantee." }
]

end JuliaLean.Channels
