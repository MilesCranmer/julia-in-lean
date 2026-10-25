import JuliaLean.ReinterpretArrays.IndexProps
import JuliaLean.ReinterpretArrays.MultInvProps
import JuliaLean.ReinterpretArrays.Wrap

/-!
Proofs of the `reshape` size checks, `ReshapedArray` subscript conversion, fast linear `SubArray`
indexing and `PermutedDimsArray` construction properties.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-! ### Generic helpers -/

private theorem min64 : IntTy.min .i64 = -9223372036854775808 := by decide
private theorem max64 : IntTy.max .i64 = 9223372036854775807 := by decide

private theorem bnd64 (x : JInt64) : -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 := by
  have h := x.property
  have e1 := min64
  have e2 := max64
  omega

private theorem wrap64 {x : Int} (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    wrapInt .i64 x = x :=
  wrapInt_of_inRange .i64 x (by rw [min64, max64]; exact ⟨h1, h2⟩)

private theorem lit1_val : (JInt.lit .i64 1).val = 1 := by decide

private theorem throw_eq {α : Type} (e : JlError) : (throw e : Jl α) = .error e := rfl

private theorem ok_inj {α : Type} {a b : α} (h : (Except.ok a : Jl α) = .ok b) : a = b := by
  cases h; rfl

private theorem bind_eq_ok {α β : Type} {x : Jl α} {f : α → Jl β} {r : β} (h : (x >>= f) = .ok r) :
    ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem bor_false {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

private theorem bor_true {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | cases h

private theorem dimProd_cons (x : JInt64) (l : List JInt64) : dimProd (x :: l) = x.val * dimProd l := rfl

private theorem dimProd_nonneg : ∀ (l : List JInt64), (∀ d ∈ l, 0 ≤ d.val) → 0 ≤ dimProd l
  | [], _ => by decide
  | x :: l, h => by
    rw [dimProd_cons]
    exact Int.mul_nonneg (h x List.mem_cons_self)
      (dimProd_nonneg l (fun d hd => h d (List.mem_cons_of_mem _ hd)))

private theorem dimProd_pos : ∀ (l : List JInt64), (∀ d ∈ l, 0 ≤ d.val) → 0 < dimProd l →
    ∀ d ∈ l, 1 ≤ d.val
  | [], _, _ => fun d hd => by cases hd
  | x :: l, h, hp => by
    rw [dimProd_cons] at hp
    have hx := h x List.mem_cons_self
    have hl := dimProd_nonneg l (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hx1 : x.val ≠ 0 := fun h0 => by rw [h0, Int.zero_mul] at hp; exact Int.lt_irrefl 0 hp
    have hl1 : dimProd l ≠ 0 := fun h0 => by rw [h0, Int.mul_zero] at hp; exact Int.lt_irrefl 0 hp
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · omega
    · exact dimProd_pos l (fun d hd => h d (List.mem_cons_of_mem _ hd)) (by omega) d hd

private theorem sub2indMath_cons (s j : Int) (rest js : List Int) (h : rest ≠ []) :
    sub2indMath (s :: rest) (j :: js) = j + s * (sub2indMath rest js - 1) := by
  cases rest with
  | nil => exact absurd rfl h
  | cons x r => cases js <;> rfl

/-! ### `reshape` size checks -/

private theorem uleTypemax_false {x : JInt64} (h : uleTypemax x = false) : 0 ≤ x.val := by
  have h' : ¬ (x.val < 0 ∨ x.val = IntTy.max .i64) := of_decide_eq_false h
  omega

private theorem checkedSmul_exact {a b : JInt64} (h : (checkedSmul a b).2 = false) :
    (checkedSmul a b).1.val = a.val * b.val := by
  have h' : ¬ ¬ (IntTy.min .i64 ≤ a.val * b.val ∧ a.val * b.val ≤ IntTy.max .i64) :=
    of_decide_eq_false h
  have h'' := Classical.not_not.mp h'
  have e1 := min64
  have e2 := max64
  exact wrap64 (by omega) (by omega)

private theorem loop_sound : ∀ (d : List JInt64) (a : JInt64) (ovflw neg zero : Bool) (ex : Int),
    (ovflw = false → a.val = ex) → (zero = true → a.val = 0 ∧ ex = 0) →
    (checkedMulDimsLoop d a ovflw neg zero).2 = false →
    neg = false ∧ (∀ x ∈ d, 0 ≤ x.val) ∧ (checkedMulDimsLoop d a ovflw neg zero).1.val = ex * dimProd d
  | [], a, ovflw, neg, zero, ex, h1, h2, h => by
    have hd : dimProd ([] : List JInt64) = 1 := rfl
    have hf : (neg || (ovflw && !zero)) = false := h
    rw [hd, Int.mul_one]
    refine ⟨?_, fun x hx => (by simp at hx), ?_⟩
    · cases neg with
      | false => rfl
      | true => cases hf
    · show a.val = ex
      cases ovflw with
      | false => exact h1 rfl
      | true =>
        cases zero with
        | false => cases neg <;> cases hf
        | true =>
          obtain ⟨ha, hex⟩ := h2 rfl
          omega
  | x :: d, a, ovflw, neg, zero, ex, h1, h2, h => by
    have hstep : checkedMulDimsLoop (x :: d) a ovflw neg zero =
        checkedMulDimsLoop d (checkedSmul a x).1 (ovflw || (checkedSmul a x).2) (neg || uleTypemax x)
          (zero || decide (x.val = 0)) := rfl
    rw [hstep] at h ⊢
    have p1 : (ovflw || (checkedSmul a x).2) = false → (checkedSmul a x).1.val = ex * x.val := by
      intro ho
      obtain ⟨ho1, ho2⟩ := bor_false ho
      rw [checkedSmul_exact ho2, h1 ho1]
    have p2 : (zero || decide (x.val = 0)) = true → (checkedSmul a x).1.val = 0 ∧ ex * x.val = 0 := by
      intro hz
      show wrapInt .i64 (a.val * x.val) = 0 ∧ ex * x.val = 0
      rcases bor_true hz with hz | hz
      · obtain ⟨ha, hex⟩ := h2 hz
        rw [ha, hex, Int.zero_mul]
        exact ⟨wrapInt_zero _, rfl⟩
      · have hx0 : x.val = 0 := of_decide_eq_true hz
        rw [hx0, Int.mul_zero, Int.mul_zero]
        exact ⟨wrapInt_zero _, rfl⟩
    obtain ⟨hn, hd, hv⟩ := loop_sound d (checkedSmul a x).1 (ovflw || (checkedSmul a x).2)
      (neg || uleTypemax x) (zero || decide (x.val = 0)) (ex * x.val) p1 p2 h
    obtain ⟨hn1, hn2⟩ := bor_false hn
    refine ⟨hn1, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact uleTypemax_false hn2
      · exact hd y hy
    · rw [hv, dimProd_cons, Int.mul_assoc]

private theorem mulDims_sound : ∀ (m m2 : JInt64) (r : List JInt64),
    (checkedMulDims (m :: m2 :: r)).2 = false →
    (∀ d ∈ m :: m2 :: r, 0 ≤ d.val) ∧ (checkedMulDims (m :: m2 :: r)).1.val = dimProd (m :: m2 :: r)
  | m, m2, [], h => by
    have hf : ((checkedSmul m m2).2 || uleTypemax m || uleTypemax m2) = false := h
    obtain ⟨h12, h3⟩ := bor_false hf
    obtain ⟨h1, h2⟩ := bor_false h12
    refine ⟨?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact uleTypemax_false h2
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact uleTypemax_false h3
        · cases hd
    · show (checkedSmul m m2).1.val = m.val * (m2.val * 1)
      rw [checkedSmul_exact h1, Int.mul_one]
  | m, m2, x :: r, h => by
    have hloop : checkedMulDims (m :: m2 :: x :: r) =
        checkedMulDimsLoop (m2 :: x :: r) m false (uleTypemax m) false := rfl
    rw [hloop] at h ⊢
    obtain ⟨hn, hd, hv⟩ := loop_sound (m2 :: x :: r) m false (uleTypemax m) false m.val
      (fun _ => rfl) (fun h => by cases h) h
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact uleTypemax_false hn
      · exact hd y hy
    · rw [hv]; rfl

theorem reshapeCheckSound : ReshapeCheckSound := by
  intro n dims hn h
  unfold reshapeCheck at h
  obtain ⟨p, hp, hpn⟩ := bind_eq_ok h
  have hpe : p = n := by
    by_cases hpe : p = n
    · exact hpe
    · rw [ite_eq_right hpe, throw_eq] at hpn
      cases hpn
  subst hpe
  match dims, hp with
  | [], hp =>
    have := ok_inj hp
    subst this
    exact ⟨fun d hd => (by simp at hd), lit1_val.symm⟩
  | [m], hp =>
    have := ok_inj hp
    subst this
    refine ⟨fun d hd => ?_, Int.mul_one _⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hn
    · cases hd
  | m :: m2 :: r, hp =>
    have hc : checkedDims (m :: m2 :: r) =
        if (checkedMulDims (m :: m2 :: r)).2 then .error (.argumentError "invalid Array dimensions")
        else .ok (checkedMulDims (m :: m2 :: r)).1 := rfl
    rw [hc] at hp
    cases hf : (checkedMulDims (m :: m2 :: r)).2 with
    | false =>
      rw [hf, ite_eq_right Bool.false_ne_true] at hp
      have := ok_inj hp
      subst this
      exact ⟨(mulDims_sound m m2 r hf).1, (mulDims_sound m m2 r hf).2.symm⟩
    | true =>
      rw [hf, ite_eq_left rfl] at hp
      cases hp

theorem reshapeColonSound : ReshapeColonSound := by
  intro len pre post dims hlen h
  unfold reshapeColon at h
  obtain ⟨d0, hu, h⟩ := bind_eq_ok h
  obtain ⟨u, hc, h⟩ := bind_eq_ok h
  have hd : d0 = dims := ok_inj h
  subst hd
  cases u
  obtain ⟨hnn, hprod⟩ := reshapeCheckSound len d0 hlen hc
  refine ⟨?_, hnn, hprod⟩
  unfold reshapeUncolon at hu
  try dsimp only at hu
  split at hu
  · exact ⟨_, (ok_inj hu).symm⟩
  · obtain ⟨pr, _, hu⟩ := bind_eq_ok hu
    try dsimp only at hu
    split at hu
    · first | cases hu | simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hu
    · obtain ⟨quo, _, hu⟩ := bind_eq_ok hu
      obtain ⟨rem, _, hu⟩ := bind_eq_ok hu
      try dsimp only at hu
      split at hu
      · first | cases hu | simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hu
      · exact ⟨quo, (ok_inj hu).symm⟩

/-! ### `ReshapedArray` subscripts -/

private theorem smiNew_divisor {t : IntTy} {d : JInt t} {mi : SignedMI t} (h : SmiNew d mi) :
    mi.divisor = d := by
  obtain ⟨_, _, _, _, _, _, hf⟩ := h
  dsimp only [smiFinish] at hf
  obtain ⟨_, _, hf⟩ := bind_eq_ok hf
  have := ok_inj hf
  subst this
  rfl

private theorem smiDiv_pos (h : SmiDivCorrect) {a s : JInt64} {mi : SignedMI .i64} (hm : SmiNew s mi)
    (ha : 0 ≤ a.val) (hs : 1 ≤ s.val) : (smiDiv a mi).val = a.val / s.val := by
  have e := (h .i64 rfl a s (by omega) (fun hc => by omega)).2 mi hm
  have hdiv : JInt.div a s = .ok (JInt.wrap .i64 (a.val.tdiv s.val)) := by
    unfold JInt.div
    rw [ite_eq_right (by omega), ite_eq_right (fun hc => by omega)]
  rw [hdiv] at e
  rw [ok_inj e]
  show wrapInt .i64 (a.val.tdiv s.val) = a.val / s.val
  rw [Int.tdiv_eq_ediv_of_nonneg ha]
  have := bnd64 a
  have h0 : 0 ≤ a.val / s.val := Int.ediv_nonneg ha (by omega)
  have h1 : a.val / s.val ≤ a.val := Int.ediv_le_self _ ha
  exact wrap64 (by omega) (by omega)

private theorem ind2subAux (h : SmiDivCorrect) (last : JInt64) (hlast : 1 ≤ last.val) :
    ∀ (szs : List JInt64) (mis : List (SignedMI .i64)) (ind : JInt64),
      SmiNewAll szs mis → (∀ s ∈ szs, 1 ≤ s.val) →
      dimProd (szs ++ [last]) ≤ IntTy.max .i64 → 0 ≤ ind.val → ind.val < dimProd (szs ++ [last]) →
      (ind2subRsAux (List.replicate (szs.length + 1) (JInt.lit .i64 1)) mis ind).length = szs.length + 1 ∧
      (∀ p ∈ (ind2subRsAux (List.replicate (szs.length + 1) (JInt.lit .i64 1)) mis ind).zip
          (szs ++ [last]), 1 ≤ p.1.val ∧ p.1.val ≤ p.2.val) ∧
      sub2indMath ((szs ++ [last]).map (·.val))
        ((ind2subRsAux (List.replicate (szs.length + 1) (JInt.lit .i64 1)) mis ind).map (·.val)) =
          ind.val + 1
  | [], [], ind, _, _, hmax, h0, hlt => by
    have hJ : ind2subRsAux (List.replicate (([] : List JInt64).length + 1) (JInt.lit .i64 1)) [] ind =
        [ind + JInt.lit .i64 1] := rfl
    have hP : dimProd ([] ++ [last]) = last.val := Int.mul_one _
    have hv : (ind + JInt.lit .i64 1).val = ind.val + 1 := by
      have := bnd64 last
      rw [val_add, lit1_val]
      exact wrap64 (by omega) (by omega)
    rw [hJ]
    refine ⟨rfl, ?_, ?_⟩
    · intro p hp
      have hp' := List.mem_singleton.mp hp
      subst hp'
      show 1 ≤ (ind + JInt.lit .i64 1).val ∧ (ind + JInt.lit .i64 1).val ≤ last.val
      rw [hv]
      omega
    · show (ind + JInt.lit .i64 1).val = ind.val + 1
      exact hv
  | [], _ :: _, _, hall, _, _, _, _ => False.elim hall
  | _ :: _, [], _, hall, _, _, _, _ => False.elim hall
  | s :: szs, m :: mis, ind, hall, hs, hmax, h0, hlt => by
    obtain ⟨hm, hall'⟩ := hall
    have hs1 : 1 ≤ s.val := hs s List.mem_cons_self
    rw [ite_eq_right (by omega)] at hm
    have hdiv : m.divisor = s := smiNew_divisor hm
    have hP : dimProd ((s :: szs) ++ [last]) = s.val * dimProd (szs ++ [last]) := rfl
    rw [hP] at hmax hlt
    have hPnn : 0 ≤ dimProd (szs ++ [last]) := dimProd_nonneg _ (fun d hd => by
      rcases List.mem_append.mp hd with hd | hd
      · have := hs d (List.mem_cons_of_mem _ hd); omega
      · rw [List.mem_singleton.mp hd]; omega)
    have hPle : 1 * dimProd (szs ++ [last]) ≤ s.val * dimProd (szs ++ [last]) :=
      Int.mul_le_mul_of_nonneg_right hs1 hPnn
    rw [Int.one_mul] at hPle
    have hq := smiDiv_pos h hm h0 hs1
    have hr := Int.emod_def ind.val s.val
    have hr0 := Int.emod_nonneg ind.val (show s.val ≠ 0 by omega)
    have hr1 := Int.emod_lt_of_pos ind.val (show 0 < s.val by omega)
    have hq0 := Int.ediv_nonneg h0 (show 0 ≤ s.val by omega)
    have hqlt : ind.val / s.val < dimProd (szs ++ [last]) :=
      Int.ediv_lt_of_lt_mul (by omega) (by rw [Int.mul_comm]; exact hlt)
    generalize ind.val / s.val = q at hq hr hq0 hqlt
    generalize ind.val % s.val = ρ at hr hr0 hr1
    obtain ⟨ihlen, ihzip, ihsub⟩ := ind2subAux h last hlast szs mis (smiDiv ind m) hall'
      (fun s hs' => hs s (List.mem_cons_of_mem _ hs')) (by omega) (by omega) (by omega)
    have hrv : (ind - smiDiv ind m * m.divisor + JInt.lit .i64 1).val = ρ + 1 := by
      have hb := bnd64 ind
      have hbs := bnd64 s
      have hqs0 : 0 ≤ q * s.val := Int.mul_nonneg hq0 (by omega)
      have hsq : s.val * q = q * s.val := Int.mul_comm _ _
      have e1 : (smiDiv ind m * m.divisor).val = q * s.val := by
        rw [val_mul, hq, hdiv]
        exact wrap64 (by omega) (by omega)
      have e2 : (ind - smiDiv ind m * m.divisor).val = ρ := by
        rw [val_sub, e1]
        exact (wrap64 (by omega) (by omega)).trans (by omega)
      rw [val_add, e2, lit1_val]
      exact wrap64 (by omega) (by omega)
    have hJ : ind2subRsAux (List.replicate ((s :: szs).length + 1) (JInt.lit .i64 1)) (m :: mis) ind =
        (ind - smiDiv ind m * m.divisor + JInt.lit .i64 1) ::
          ind2subRsAux (List.replicate (szs.length + 1) (JInt.lit .i64 1)) mis (smiDiv ind m) := rfl
    rw [hJ]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_cons, ihlen]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · show 1 ≤ (ind - smiDiv ind m * m.divisor + JInt.lit .i64 1).val ∧
          (ind - smiDiv ind m * m.divisor + JInt.lit .i64 1).val ≤ s.val
        rw [hrv]
        omega
      · exact ihzip p hp
    · have hne : (szs ++ [last]).map (·.val) ≠ [] := by simp
      rw [List.cons_append, List.map_cons, List.map_cons, sub2indMath_cons _ _ _ _ hne, ihsub, hrv, hq,
        Int.add_sub_cancel]
      omega

theorem ind2subCorrect_of (h : SmiDivCorrect) : Ind2subCorrect := by
  intro szs last mis i hall hnn hlast hmax hi1 hi2
  have hpos := dimProd_pos (szs ++ [last]) (fun d hd => by
    rcases List.mem_append.mp hd with hd | hd
    · exact hnn d hd
    · rw [List.mem_singleton.mp hd]; exact hlast) (by omega)
  have hs1 : ∀ s ∈ szs, 1 ≤ s.val := fun s hs => hpos s (List.mem_append_left _ hs)
  have hl1 : 1 ≤ last.val := hpos last (List.mem_append_right _ (List.mem_singleton_self _))
  cases mis with
  | nil =>
    cases szs with
    | cons s szs => exact False.elim hall
    | nil =>
      have hP : dimProd ([] ++ [last]) = last.val := Int.mul_one _
      dsimp only
      refine ⟨rfl, ?_, rfl⟩
      intro p hp
      have hp' := List.mem_singleton.mp hp
      subst hp'
      show 1 ≤ i.val ∧ i.val ≤ last.val
      exact ⟨hi1, by omega⟩
  | cons m mis =>
    have hJ : ind2subRs (List.replicate (szs.length + 1) (JInt.lit .i64 1)) (m :: mis) i =
        ind2subRsAux (List.replicate (szs.length + 1) (JInt.lit .i64 1)) (m :: mis)
          (i - JInt.lit .i64 1) := rfl
    have hiv : (i - JInt.lit .i64 1).val = i.val - 1 := by
      have := bnd64 i
      rw [val_sub, lit1_val]
      exact wrap64 (by omega) (by omega)
    obtain ⟨h1, h2, h3⟩ := ind2subAux h last hl1 szs (m :: mis) (i - JInt.lit .i64 1) hall hs1 hmax
      (by omega) (by omega)
    dsimp only
    rw [hJ]
    refine ⟨h1, h2, ?_⟩
    rw [h3, hiv]
    omega

/-! ### `SubArray` linear indexing -/

/-- Congruence modulo `2^64`. -/
private def C (a b : Int) : Prop := wrapInt .i64 a = wrapInt .i64 b

private theorem cg_refl (a : Int) : C a a := rfl

private theorem cg_trans {a b c : Int} (h1 : C a b) (h2 : C b c) : C a c := Eq.trans h1 h2

private theorem cg_of_eq {a b : Int} (h : a = b) : C a b := by rw [h]; exact cg_refl b

private theorem cg_add {a a' b b' : Int} (h1 : C a a') (h2 : C b b') : C (a + b) (a' + b') := by
  unfold C at *
  rw [← wrapInt_add .i64 a b, h1, h2, wrapInt_add]

private theorem cg_sub {a a' b b' : Int} (h1 : C a a') (h2 : C b b') : C (a - b) (a' - b') := by
  unfold C at *
  rw [← wrapInt_sub .i64 a b, h1, h2, wrapInt_sub]

private theorem cg_mul {a a' b b' : Int} (h1 : C a a') (h2 : C b b') : C (a * b) (a' * b') := by
  unfold C at *
  rw [← wrapInt_mul .i64 a b, h1, h2, wrapInt_mul]

private theorem cg_val_add (x y : JInt64) : C (x + y).val (x.val + y.val) := by
  unfold C; rw [val_add, wrapInt_wrapInt]

private theorem cg_val_sub (x y : JInt64) : C (x - y).val (x.val - y.val) := by
  unfold C; rw [val_sub, wrapInt_wrapInt]

private theorem cg_val_mul (x y : JInt64) : C (x * y).val (x.val * y.val) := by
  unfold C; rw [val_mul, wrapInt_wrapInt]

private theorem cl_step (f s i : JInt64) :
    C (f + (i - JInt.lit .i64 1) * s).val (f.val + (i.val - 1) * s.val) :=
  cg_trans (cg_val_add _ _) (cg_add (cg_refl _) (cg_trans (cg_val_mul _ _)
    (cg_mul (cg_trans (cg_val_sub _ _) (cg_of_eq (by rw [lit1_val]))) (cg_refl _))))

private theorem cl_cong : ∀ (is ips : List JInt64) (f s : JInt64), is ≠ [] → ips.length = is.length →
    C (computeLinindex f s ips is).val
      (f.val + s.val * (sub2indMath (ips.map (·.val)) (is.map (·.val)) - 1))
  | [], _, _, _, h, _ => absurd rfl h
  | [_], [], _, _, _, hl => by simp at hl
  | [i], [p], f, s, _, _ =>
    cg_trans (cl_step f s i) (cg_of_eq (by
      show f.val + (i.val - 1) * s.val = f.val + s.val * (i.val - 1)
      rw [Int.mul_comm]))
  | [_], _ :: _ :: _, _, _, _, hl => by simp at hl
  | _ :: _ :: _, [], _, _, _, hl => by simp at hl
  | i :: j :: is, p :: ips, f, s, _, hl => by
    have hne : ips ≠ [] := by
      intro h0
      subst h0
      simp at hl
    have ih := cl_cong (j :: is) ips (f + (i - JInt.lit .i64 1) * s) (s * p) (by simp)
      (by simpa using hl)
    show C (computeLinindex (f + (i - JInt.lit .i64 1) * s) (s * p) ips (j :: is)).val
      (f.val + s.val * (sub2indMath (p.val :: ips.map (·.val)) (i.val :: (j :: is).map (·.val)) - 1))
    rw [sub2indMath_cons p.val i.val (ips.map (·.val)) ((j :: is).map (·.val))
      (fun h0 => hne (List.map_eq_nil_iff.mp h0))]
    refine cg_trans ih (cg_trans (cg_add (cl_step f s i) (cg_mul (cg_val_mul s p) (cg_refl _)))
      (cg_of_eq ?_))
    grind

private theorem sub2_bounds : ∀ (js ss : List JInt64), ss.length = js.length → js ≠ [] →
    (∀ p ∈ js.zip ss, 1 ≤ p.1.val ∧ p.1.val ≤ p.2.val) →
    1 ≤ sub2indMath (ss.map (·.val)) (js.map (·.val)) ∧
      sub2indMath (ss.map (·.val)) (js.map (·.val)) ≤ dimProd ss
  | [], _, _, h, _ => absurd rfl h
  | [j], [s], _, _, hz => by
    have := hz (j, s) List.mem_cons_self
    show 1 ≤ j.val ∧ j.val ≤ s.val * 1
    rw [Int.mul_one]
    exact this
  | [_], _ :: _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl
  | _ :: _ :: _, [_], hl, _, _ => by simp at hl
  | j :: j' :: js, s :: s' :: ss, hl, _, hz => by
    have hz0 : 1 ≤ j.val ∧ j.val ≤ s.val := hz (j, s) List.mem_cons_self
    have ih := sub2_bounds (j' :: js) (s' :: ss) (by simpa using hl) (by simp)
      (fun p hp => hz p (List.mem_cons_of_mem _ hp))
    have e : sub2indMath ((s :: s' :: ss).map (·.val)) ((j :: j' :: js).map (·.val)) =
        j.val + s.val * (sub2indMath ((s' :: ss).map (·.val)) ((j' :: js).map (·.val)) - 1) := rfl
    rw [e, dimProd_cons]
    generalize sub2indMath ((s' :: ss).map (·.val)) ((j' :: js).map (·.val)) = T at ih ⊢
    generalize dimProd (s' :: ss) = D at ih ⊢
    have h1 : s.val * 0 ≤ s.val * (T - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h2 : s.val * (T - 1) ≤ s.val * (D - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h3 : s.val * (D - 1) = s.val * D - s.val := by rw [Int.mul_sub, Int.mul_one]
    rw [Int.mul_zero] at h1
    omega

theorem viewIndexCorrect : ViewIndexCorrect := by
  intro s1 rest cs start step len hlen _ hmax hcs hr i hi1 hi2
  obtain ⟨hx1, hx2⟩ := hr i.val hi1 hi2
  have hst : C (JInt.lit .i64 1 * step).val step.val :=
    cg_trans (cg_val_mul _ _) (cg_of_eq (by rw [lit1_val, Int.one_mul]))
  have hst1 : C (JInt.lit .i64 1 * step * JInt.lit .i64 1).val step.val :=
    cg_trans (cg_val_mul _ _) (cg_trans (cg_mul hst (cg_refl _)) (cg_of_eq (by rw [lit1_val, Int.mul_one])))
  have hsi : C (JInt.lit .i64 1 * step * i).val (step.val * i.val) :=
    cg_trans (cg_val_mul _ _) (cg_mul hst (cg_refl _))
  have fin : ∀ E : Int, C (viewParentIndex (viewLayout (s1 :: rest) start step cs) i).val E →
      1 ≤ E → E ≤ IntTy.max .i64 → (viewParentIndex (viewLayout (s1 :: rest) start step cs) i).val = E := by
    intro E hE h1 h2
    unfold C at hE
    rw [← val_eq_wrap] at hE
    rw [hE]
    have e2 := max64
    exact wrap64 (by omega) (by omega)
  cases cs with
  | nil =>
    have hr0 : rest = [] := List.eq_nil_of_length_eq_zero hlen
    subst hr0
    have hv : C (viewParentIndex (viewLayout [s1] start step []) i).val
        (start.val + (i.val - 1) * step.val) := by
      show C ((start - JInt.lit .i64 1 * step * JInt.lit .i64 1) + JInt.lit .i64 1 * step * i).val _
      refine cg_trans (cg_val_add _ _) (cg_trans (cg_add (cg_trans (cg_val_sub _ _)
        (cg_sub (cg_refl _) hst1)) hsi) (cg_of_eq ?_))
      grind
    have hb := bnd64 s1
    have e2 := max64
    have hfin := fin _ hv (by omega) (by omega)
    exact hfin
  | cons c cs' =>
    cases rest with
    | nil => simp at hlen
    | cons r rest' =>
      have hL := cl_cong (start :: c :: cs') (s1 :: r :: rest') (JInt.lit .i64 1) (JInt.lit .i64 1)
        (by simp) (by simpa using hlen)
      rw [lit1_val] at hL
      have hS : sub2indMath ((s1 :: r :: rest').map (·.val)) ((start :: c :: cs').map (·.val)) =
          start.val + s1.val * (sub2indMath ((r :: rest').map (·.val)) ((c :: cs').map (·.val)) - 1) :=
        rfl
      rw [hS] at hL
      have hT := sub2_bounds (c :: cs') (r :: rest') (by simpa using hlen) (by simp) hcs
      have hE : sub2indMath ((s1 :: r :: rest').map (·.val))
          ((start.val + (i.val - 1) * step.val) :: (c :: cs').map (·.val)) =
          start.val + (i.val - 1) * step.val +
            s1.val * (sub2indMath ((r :: rest').map (·.val)) ((c :: cs').map (·.val)) - 1) := rfl
      rw [hE]
      have hD : dimProd (s1 :: r :: rest') = s1.val * dimProd (r :: rest') := rfl
      rw [hD] at hmax
      generalize sub2indMath ((r :: rest').map (·.val)) ((c :: cs').map (·.val)) = T at hL hT ⊢
      generalize dimProd (r :: rest') = D at hT hmax
      have hv : C (viewParentIndex (viewLayout (s1 :: r :: rest') start step (c :: cs')) i).val
          (start.val + (i.val - 1) * step.val + s1.val * (T - 1)) := by
        show C ((computeLinindex (JInt.lit .i64 1) (JInt.lit .i64 1) (s1 :: r :: rest') (start :: c :: cs') -
          JInt.lit .i64 1 * step * JInt.lit .i64 1) + JInt.lit .i64 1 * step * i).val _
        refine cg_trans (cg_val_add _ _) (cg_trans (cg_add (cg_trans (cg_val_sub _ _)
          (cg_sub hL hst1)) hsi) (cg_of_eq ?_))
        grind
      have h1 : s1.val * 0 ≤ s1.val * (T - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have h2 : s1.val * (T - 1) ≤ s1.val * (D - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have h3 : s1.val * (D - 1) = s1.val * D - s1.val := by rw [Int.mul_sub, Int.mul_one]
      rw [Int.mul_zero] at h1
      have hfin := fin _ hv (by omega) (by omega)
      exact hfin

/-! ### `PermutedDimsArray` -/

/-- The loop body of `invperm`, `base/combinatorics.jl:286-296`. -/
private def invStep (n : Nat) (b : List Int) (p : Int × Nat) : Jl (List Int) :=
  let (j, i) := p
  if 1 ≤ j ∧ j ≤ n ∧ b.getD (j - 1).toNat 0 = 0 then .ok (b.set (j - 1).toNat i)
  else .error (.argumentError "argument is not a permutation")

private theorem invperm_eq (a : List Int) :
    invperm a = (a.zipIdx 1).foldlM (invStep a.length) (List.replicate a.length 0) := rfl

private theorem getD_replicate_zero (n j : Nat) : (List.replicate n (0 : Int)).getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

private theorem invFold (n : Nat) : ∀ (xs : List Int) (k : Nat) (b : List Int), b.length = n →
    (∀ x ∈ xs, 1 ≤ x ∧ x ≤ n) → xs.Nodup → (∀ x ∈ xs, b.getD (x - 1).toNat 0 = 0) →
    ∃ b', (xs.zipIdx k).foldlM (invStep n) b = .ok b' ∧ b'.length = n ∧
      (∀ j, (∀ y ∈ xs, (y - 1).toNat ≠ j) → b'.getD j 0 = b.getD j 0) ∧
      ∀ i < xs.length, b'.getD ((xs.getD i 0) - 1).toNat 0 = ((k + i : Nat) : Int)
  | [], _, b, hb, _, _, _ => ⟨b, rfl, hb, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | x :: xs, k, b, hb, hr, hnd, hz => by
    have hx := hr x List.mem_cons_self
    have hbx := hz x List.mem_cons_self
    obtain ⟨hxn, hnd⟩ := List.nodup_cons.mp hnd
    have hstep : invStep n b (x, k) = .ok (b.set (x - 1).toNat (k : Int)) := by
      have e : invStep n b (x, k) = if 1 ≤ x ∧ x ≤ n ∧ b.getD (x - 1).toNat 0 = 0 then
          .ok (b.set (x - 1).toNat (k : Int)) else .error (.argumentError "argument is not a permutation") :=
        rfl
      rw [e, ite_eq_left ⟨hx.1, hx.2, hbx⟩]
    have hb1 : (b.set (x - 1).toNat (k : Int)).length = n := by rw [List.length_set, hb]
    have hne : ∀ y ∈ xs, (y - 1).toNat ≠ (x - 1).toNat := fun y hy h0 => by
      have hy1 := (hr y (List.mem_cons_of_mem _ hy)).1
      have hyx : y = x := by omega
      exact hxn (hyx ▸ hy)
    have hb1get : ∀ j, j ≠ (x - 1).toNat → (b.set (x - 1).toNat (k : Int)).getD j 0 = b.getD j 0 := by
      intro j hj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]
    have hz1 : ∀ y ∈ xs, (b.set (x - 1).toNat (k : Int)).getD (y - 1).toNat 0 = 0 := fun y hy => by
      rw [hb1get _ (hne y hy)]
      exact hz y (List.mem_cons_of_mem _ hy)
    obtain ⟨b', hf, hl, hag, hval⟩ := invFold n xs (k + 1) _ hb1
      (fun y hy => hr y (List.mem_cons_of_mem _ hy)) hnd hz1
    refine ⟨b', ?_, hl, ?_, ?_⟩
    · show (invStep n b (x, k) >>= fun b'' => (xs.zipIdx (k + 1)).foldlM (invStep n) b'') = .ok b'
      rw [hstep]
      exact hf
    · intro j hj
      rw [hag j (fun y hy => hj y (List.mem_cons_of_mem _ hy)),
        hb1get j (fun h0 => hj x List.mem_cons_self h0.symm)]
    · intro i hi
      cases i with
      | zero =>
        show b'.getD (x - 1).toNat 0 = ((k + 0 : Nat) : Int)
        rw [hag _ (fun y hy => hne y hy)]
        have hlt : (x - 1).toNat < b.length := by rw [hb]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlt]
        rfl
      | succ i =>
        show b'.getD ((xs.getD i 0) - 1).toNat 0 = ((k + (i + 1) : Nat) : Int)
        rw [hval i (by simpa using hi)]
        omega

/-- The list `[1, 2, ..., n]`. -/
private def iota1 (n : Nat) : List Int := (List.range n).map (fun k : Nat => (k : Int) + 1)

private theorem mem_iota1 {n : Nat} {y : Int} (h : y ∈ iota1 n) : 1 ≤ y ∧ y ≤ n := by
  unfold iota1 at h
  rw [List.mem_map] at h
  obtain ⟨k, hk, hky⟩ := h
  rw [List.mem_range] at hk
  omega

private theorem iota1_nodup (n : Nat) : (iota1 n).Nodup := by
  unfold iota1 List.Nodup
  exact List.Pairwise.map _ (fun a b hab heq => hab (by
    have h' : (a : Int) + 1 = (b : Int) + 1 := heq
    omega)) List.nodup_range

private theorem isperm_mem {p : List Int} (h : isperm p = true) : ∀ k < p.length, ((k : Int) + 1) ∈ p := by
  intro k hk
  unfold isperm at h
  have h1 := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  have hc : p.count ((k : Int) + 1) = 1 := of_decide_eq_true h1
  exact List.count_pos_iff.mp (by omega)

private theorem isperm_range {p : List Int} (h : isperm p = true) : ∀ x ∈ p, 1 ≤ x ∧ x ≤ p.length := by
  intro x hx
  apply Classical.byContradiction
  intro hn
  have hxL : x ∉ iota1 p.length := fun hm => hn (mem_iota1 hm)
  have hsub : (x :: iota1 p.length) ⊆ p := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · unfold iota1 at hy
      rw [List.mem_map] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact isperm_mem h k (List.mem_range.mp hk)
  have hle := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hxL, iota1_nodup _⟩) hsub
  have hl : (x :: iota1 p.length).length = p.length + 1 := by simp [iota1]
  omega

private theorem isperm_nodup {p : List Int} (h : isperm p = true) : p.Nodup := by
  rw [List.nodup_iff_count]
  intro a
  by_cases ha : a ∈ p
  · have hr := isperm_range h a ha
    have h' := h
    unfold isperm at h'
    have h1 := List.all_eq_true.mp h' (a - 1).toNat (List.mem_range.mpr (by omega))
    have hc : p.count (((a - 1).toNat : Int) + 1) = 1 := of_decide_eq_true h1
    have he : (((a - 1).toNat : Int) + 1) = a := by omega
    rw [he] at hc
    omega
  · rw [List.count_eq_zero_of_not_mem ha]
    omega

private theorem mem_getD {l : List Int} {x : Int} (h : x ∈ l) : ∃ d < l.length, l.getD d 0 = x := by
  obtain ⟨d, hd, hx⟩ := List.mem_iff_getElem.mp h
  refine ⟨d, hd, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd]
  exact hx

private theorem getD_mem {l : List Int} {d : Nat} (h : d < l.length) : l.getD d 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

private theorem genperm_length (I perm : List Int) : (genperm I perm).length = perm.length := by
  simp [genperm]

private theorem genperm_getD (I perm : List Int) (k : Nat) (hk : k < perm.length) :
    (genperm I perm).getD k 0 = I.getD ((perm.getD k 0) - 1).toNat 0 := by
  simp [genperm, List.getElem?_eq_getElem hk] <;> rfl

private theorem forall_zip_getD : ∀ (l₁ l₂ : List Int), l₁.length = l₂.length →
    ((∀ p ∈ l₁.zip l₂, 1 ≤ p.1 ∧ p.1 ≤ p.2) ↔
      ∀ k < l₁.length, 1 ≤ l₁.getD k 0 ∧ l₁.getD k 0 ≤ l₂.getD k 0)
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    have ih := forall_zip_getD l₁ l₂ (by simpa using h)
    constructor
    · intro hz k hk
      cases k with
      | zero => exact hz (a, b) List.mem_cons_self
      | succ k =>
        exact (ih.mp (fun p hp => hz p (List.mem_cons_of_mem _ hp))) k (by simpa using hk)
    · intro hk p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hk 0 (by simp)
      · exact ih.mpr (fun k hk' => hk (k + 1) (by simpa using hk')) p hp

theorem permutedCorrect : PermutedCorrect := by
  intro perm dims hlen
  refine ⟨fun hf => ?_, fun hp => ?_⟩
  · cases hi : invperm perm with
    | error e =>
      refine ⟨e, ?_⟩
      simp only [pdaNew, hlen, ne_eq, not_true_eq_false, reduceIte, hi, bind, Except.bind]
    | ok ip =>
      refine ⟨.argumentError "not a valid permutation", ?_⟩
      simp only [pdaNew, hlen, ne_eq, not_true_eq_false, reduceIte, hi, hf, Bool.not_false, bind,
        Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have hrange := isperm_range hp
    have hnd := isperm_nodup hp
    obtain ⟨ip, hfold, hiplen, -, hval⟩ := invFold perm.length perm 1 (List.replicate perm.length 0)
      List.length_replicate hrange hnd (fun _ _ => getD_replicate_zero _ _)
    have hinv : invperm perm = .ok ip := by rw [invperm_eq]; exact hfold
    have hval' : ∀ d < perm.length, ip.getD ((perm.getD d 0) - 1).toNat 0 = (d : Int) + 1 := by
      intro d hd
      rw [hval d hd]
      omega
    have hc : (List.range perm.length).all
        (fun d => decide (ip.getD ((perm.getD d 0) - 1).toNat 0 = (d : Int) + 1)) = true :=
      List.all_eq_true.mpr (fun d hd => decide_eq_true (hval' d (List.mem_range.mp hd)))
    refine ⟨ip, ?_, ?_⟩
    · rw [← hlen]
      simp only [pdaNew, ne_eq, not_true_eq_false, reduceIte, Bool.false_eq_true, hinv, hp, hc, Bool.not_true, bind,
        Except.bind, pure, Except.pure]
    · intro I hIlen hIb
      dsimp only
      refine ⟨by rw [genperm_length, hiplen, hlen], ?_, ?_⟩
      · refine (forall_zip_getD (genperm I ip) dims (by rw [genperm_length, hiplen, hlen])).mpr ?_
        intro k hk
        rw [genperm_length, hiplen] at hk
        obtain ⟨d, hd, hpd⟩ := mem_getD (isperm_mem hp k hk)
        have hipk : ip.getD k 0 = (d : Int) + 1 := by
          have h1 := hval' d hd
          rwa [hpd, (by omega : (((k : Int) + 1) - 1).toNat = k)] at h1
        have hb := (forall_zip_getD I (genperm dims perm)
          (by rw [genperm_length, hIlen, hlen])).mp hIb d (by omega)
        rw [genperm_getD dims perm d hd, hpd, (by omega : (((k : Int) + 1) - 1).toNat = k)] at hb
        rw [genperm_getD I ip k (by omega), hipk, (by omega : (((d : Int) + 1) - 1).toNat = d)]
        exact hb
      · intro d hd
        rw [← hlen] at hd
        have hk2 : ((perm.getD d 0) - 1).toNat < ip.length := by
          have := hrange _ (getD_mem hd)
          omega
        rw [genperm_getD I ip _ hk2, hval' d hd, (by omega : (((d : Int) + 1) - 1).toNat = d)]

end JuliaLean.ReinterpretArrays
