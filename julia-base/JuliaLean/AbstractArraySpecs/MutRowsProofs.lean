import JuliaLean.AbstractArraySpecs.MutRowsProps
import JuliaLean.AbstractArraySpecs.CopyRowsProofs

/-! Proofs of the `map!`, `push!`/`pushfirst!` and `circshift!` row contracts. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

/-! ## `map!` with two sources -/

theorem map2Loop_from {α : Type} (f : α → α → α) (dest A B : Arr α) (hd : dest.WF) (hA : A.WF)
    (hB : B.WF) (m : Nat) (hzl : (List.zipWith f A.data B.data).length = m) (hmA : m ≤ A.data.length)
    (hmB : m ≤ B.data.length) (hm : m = A.data.length ∨ m = B.data.length) :
    ∀ (n j : Nat) (sd sa sb : IterState), GoodE dest j sd → GoodE A j sa → GoodE B j sb →
      j ≤ dest.data.length → j ≤ A.data.length → j ≤ B.data.length → dest.data.length - j < n →
      map2Loop f A B n { dest with data := (List.zipWith f A.data B.data).take j ++ dest.data.drop j } sd sa sb =
        .ok { dest with data := (List.zipWith f A.data B.data).take dest.data.length ++ dest.data.drop m } := by
  intro n
  induction n with
  | zero => intro j sd sa sb _ _ _ _ _ _ h; omega
  | succ n ih =>
    intro j sd sa sb gd ga gb hjd hja hjb hn
    by_cases h1 : j < dest.data.length
    · by_cases h2 : j < A.data.length
      · by_cases h3 : j < B.data.length
        · have hjm : j < m := by omega
          have hn1 : dest.data.length - (j + 1) < n := by omega
          have hzj : j < (List.zipWith f A.data B.data).length := by rw [hzl]; exact hjm
          have hlen : ((List.zipWith f A.data B.data).take j ++ dest.data.drop j).length = dest.data.length := by
            rw [List.length_append, List.length_take, List.length_drop, hzl, Nat.min_eq_left (Nat.le_of_lt hjm)]
            omega
          have hD : ({ dest with data := (List.zipWith f A.data B.data).take j ++ dest.data.drop j } : Arr α).WF :=
            wf_data dest _ hd hlen
          obtain ⟨d1, -⟩ := each_step dest hd j sd gd hjd
          obtain ⟨a1, -⟩ := each_step A hA j sa ga hja
          obtain ⟨b1, -⟩ := each_step B hB j sb gb hjb
          rw [map2Loop, eachindexStep_data]
          obtain ⟨I, sd', hsd, hIl, hIp, gd'⟩ := d1 h1
          rw [hsd]
          simp only []
          obtain ⟨J, sa', hsa, hJl, hJp, ga'⟩ := a1 h2
          rw [hsa]
          simp only []
          obtain ⟨K, sb', hsb, hKl, hKp, gb'⟩ := b1 h3
          rw [hsb]
          simp only []
          rw [getindex_at A hA J j hJl hJp, bind_ok, getindex_at B hB K j hKl hKp, bind_ok,
            setindex_at _ hD I j _ hIl (by rw [refPos_data]; exact hIp), bind_ok]
          have hval : f (A.data[j]'(refPos_lt A hA J j hJp)) (B.data[j]'(refPos_lt B hB K j hKp)) =
              (List.zipWith f A.data B.data)[j]'hzj := by simp
          rw [hval, set_prefix_id _ dest.data j hzj h1]
          exact ih (j + 1) sd' sa' sb' gd' ga' gb' h1 h2 h3 hn1
        · have hjm : j = m := by omega
          have hjB : j = B.data.length := by omega
          have e1 : (List.zipWith f A.data B.data).take j = List.zipWith f A.data B.data :=
            List.take_of_length_le (by rw [hzl]; omega)
          have e2 : (List.zipWith f A.data B.data).take dest.data.length = List.zipWith f A.data B.data :=
            List.take_of_length_le (by rw [hzl]; omega)
          obtain ⟨d1, -⟩ := each_step dest hd j sd gd hjd
          obtain ⟨a1, -⟩ := each_step A hA j sa ga hja
          obtain ⟨-, b2⟩ := each_step B hB j sb gb hjb
          rw [map2Loop, eachindexStep_data]
          obtain ⟨I, sd', hsd, -, -, -⟩ := d1 h1
          rw [hsd]
          simp only []
          obtain ⟨J, sa', hsa, -, -, -⟩ := a1 h2
          rw [hsa]
          simp only []
          rw [b2 hjB]
          simp only []
          rw [e1, e2, hjm]
      · have hjm : j = m := by omega
        have hjA : j = A.data.length := by omega
        have e1 : (List.zipWith f A.data B.data).take j = List.zipWith f A.data B.data :=
          List.take_of_length_le (by rw [hzl]; omega)
        have e2 : (List.zipWith f A.data B.data).take dest.data.length = List.zipWith f A.data B.data :=
          List.take_of_length_le (by rw [hzl]; omega)
        obtain ⟨d1, -⟩ := each_step dest hd j sd gd hjd
        obtain ⟨-, a2⟩ := each_step A hA j sa ga hja
        rw [map2Loop, eachindexStep_data]
        obtain ⟨I, sd', hsd, -, -, -⟩ := d1 h1
        rw [hsd]
        simp only []
        rw [a2 hjA]
        simp only []
        rw [e1, e2, hjm]
    · have hjd' : j = dest.data.length := by omega
      have hdm : dest.data.length ≤ m := by omega
      obtain ⟨-, d2⟩ := each_step dest hd j sd gd hjd
      rw [map2Loop, eachindexStep_data, d2 hjd']
      simp only []
      rw [hjd', List.drop_length, List.drop_eq_nil_of_le hdm]

theorem mapBang2Prefix_proven : MapBang2Prefix := by
  intro α f dest A B hd hA hB
  have hm : min A.data.length B.data.length = A.data.length ∨ min A.data.length B.data.length = B.data.length := by
    rw [Nat.min_def]; split <;> simp
  have h := map2Loop_from f dest A B hd hA hB (min A.data.length B.data.length) (by simp)
    (Nat.min_le_left _ _) (Nat.min_le_right _ _) hm
    (fuelOf dest) 0 _ _ _ (goodE_start dest) (goodE_start A)
    (goodE_start B) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (by simp [fuelOf])
  have e : ({ dest with data := (List.zipWith f A.data B.data).take 0 ++ dest.data.drop 0 } : Arr α) = dest := by
    cases dest; simp
  rw [e] at h
  exact h

/-! ## `ith_all` and `map!(f, A)` -/

theorem ithAll_proven : IthAllSpec := by
  intro α i As hAs
  induction As with
  | nil => rfl
  | cons a as ih =>
    have ha : a.WF := hAs a (by simp)
    rw [ithAll, (indexing_linear a ha i).1, List.mapM_cons,
      ih (fun x hx => hAs x (by simp [hx]))]
    rfl

theorem mapBangInplace_proven : MapBangInplaceSpec := by
  intro α f A hA
  unfold mapBangInplace
  rw [mapBangPrefix_proven f A A hA hA, List.take_length, List.drop_length, List.append_nil]

/-! ## `push!` -/

theorem set_last {α : Type} (l : List α) (x : α) (n : Nat) (hl : l.length = n + 1) :
    l.set n x = l.take n ++ [x] := by
  rw [List.set_eq_take_append_cons_drop, if_pos (by omega), List.drop_of_length_le (by omega)]

theorem take_set_succ {α : Type} (d : List α) (p : Nat) (y : α) (hp : p < d.length) :
    (d.set p y).take (p + 1) = d.take p ++ [y] := by
  rw [List.set_eq_take_append_cons_drop, if_pos hp, List.take_append]
  have hl : (d.take p).length = p := by simp; omega
  rw [hl, List.take_of_length_le (by omega), show p + 1 - p = 1 by omega]
  rfl

/-- After `resize!(a, length(a) + 1)`, writing `a[end]` appends the item. -/
theorem write_end {α : Type} (a a' : Arr α) (x : α) (ha' : a'.WF) (hlen : a'.data.length = a.data.length + 1)
    (hkeep : a'.data.take a.data.length = a.data) :
    setindex a' x [(linearAxis a').hi] = .ok { a' with data := a.data ++ [x] } := by
  have hhi := linAx_len a' ha'
  have hhb := bnd (linearAxis a').hi
  have hst := refLin_step a' ha' a.data.length (by omega)
  rw [if_pos (by omega)] at hst
  have hp : refPos a' [(linearAxis a').hi] = some a.data.length := by
    show refLinPos a' (linearAxis a').hi.val = some a.data.length
    rw [← wrap_id (linearAxis a').hi.val hhb.1 hhb.2,
      show (linearAxis a').hi.val = (linearAxis a').lo.val + (a.data.length : Int) by omega, hst]
  rw [setindex_at a' ha' _ a.data.length x (Or.inr rfl) hp, set_last a'.data x _ hlen, hkeep]

/-- `resize!(a, length(a) + k)` keeps `a`'s elements in front. -/
theorem resize_grow {α : Type} (resize : Arr α → I64 → R (Arr α)) (hR : ResizeKeeps resize) (a : Arr α)
    (ha : a.WF) (h1 : a.axes.length = 1) (k : Nat) (hk : (a.data.length : Int) + k ≤ tmax) :
    ∃ a', resize a (lengthA a + i64 (k : Int)) = .ok a' ∧ a'.WF ∧ a'.data.length = a.data.length + k ∧
      (linearAxis a').lo = (linearAxis a).lo ∧ a'.data.take a.data.length = a.data := by
  have hl := lengthA_val a ha
  have hkv : (i64 (k : Int)).val = k := by
    rw [vlit, wrap_id _ (by omega) (by rw [tmax_eq] at hk; omega)]
  have hnl : (lengthA a + i64 (k : Int)).val = a.data.length + k := by
    rw [vadd, hl, hkv, wrap_id _ (by omega) (by rw [tmax_eq] at hk; omega)]
  obtain ⟨a', hres, hwf, -, hlen, hlo, hkeep⟩ := hR a (lengthA a + i64 (k : Int)) ha h1 (by omega)
  refine ⟨a', hres, hwf, by omega, hlo, ?_⟩
  rw [hkeep, List.take_of_length_le (by omega)]

theorem pushOne_proven : PushOneSpec := by
  intro α β conv resize a item hR ha h1 hlt
  refine ⟨fun e he => ?_, fun x hx => ?_⟩
  · simp only [pushOne, he]; rfl
  · obtain ⟨a', hres, hwf, hlen, hlo, hkeep⟩ := resize_grow resize hR a ha h1 1 (by push_cast; omega)
    refine ⟨{ a' with data := a.data ++ [x] }, ?_, rfl, hlo⟩
    simp only [pushOne, hx, bind_ok]
    rw [show (i64 1) = i64 ((1 : Nat) : Int) from rfl, hres, bind_ok]
    exact write_end a a' x hwf hlen hkeep

theorem pushOneAny_proven : PushOneAnySpec := by
  intro α resize a x hR ha h1 hlt
  obtain ⟨a', hres, hwf, hlen, hlo, hkeep⟩ := resize_grow resize hR a ha h1 1 (by push_cast; omega)
  refine ⟨{ a' with data := a.data ++ [x] }, ?_, rfl, hlo⟩
  simp only [pushOneAny]
  rw [show (i64 1) = i64 ((1 : Nat) : Int) from rfl, hres, bind_ok]
  exact write_end a a' x hwf hlen hkeep

theorem pushManyLoop_from {α : Type} (a' : Arr α) (ha' : a'.WF) (e : I64) (c : Int) (hc1 : -1 ≤ c)
    (he : e.val = wrapInt .i64 ((linearAxis a').lo.val + c)) :
    ∀ (ys : List α) (i p : Nat) (d : List α), d.length = a'.data.length →
      p + ys.length = a'.data.length → c + (i : Int) = p →
      pushManyLoop e i { a' with data := d } ys = .ok { a' with data := d.take p ++ ys } := by
  have hlt := ha'.2.2
  have hlen := ha'.2.1
  rw [tmax_eq] at hlt
  intro ys
  induction ys with
  | nil =>
    intro i p d hd hp _
    simp only [pushManyLoop, List.append_nil]
    rw [List.take_of_length_le (by simp at hp; omega)]
  | cons y ys ih =>
    intro i p d hd hp hc
    simp only [List.length_cons] at hp
    have hD := wf_data a' d ha' hd
    have hpl : p < a'.data.length := by omega
    have hst := refLin_step a' ha' p (by omega)
    rw [if_pos hpl] at hst
    have hiv : (i64 (i : Int)).val = i := by
      rw [vlit, wrap_id _ (by omega) (by omega)]
    have hev : (e + i64 (i : Int)).val = wrapInt .i64 ((linearAxis a').lo.val + (p : Int)) := by
      rw [vadd, hiv, he, wrap_add', show (linearAxis a').lo.val + c + (i : Int) = (linearAxis a').lo.val + p by omega]
    have hpos : refPos { a' with data := d } [e + i64 (i : Int)] = some p := by
      rw [refPos_data]; show refLinPos a' (e + i64 (i : Int)).val = some p; rw [hev, hst]
    rw [pushManyLoop, setindex_at _ hD _ p y (Or.inr rfl) hpos, bind_ok]
    refine (ih (i + 1) (p + 1) (d.set p y) (by simp [hd]) (by omega) (by push_cast; omega)).trans ?_
    rw [take_set_succ d p y (by omega), List.append_assoc, List.singleton_append]

theorem pushManyAny_proven : PushManyAnySpec := by
  intro α resize a xs hR ha h1 hle
  obtain ⟨a', hres, hwf, hlen, hlo, hkeep⟩ := resize_grow resize hR a ha h1 xs.length hle
  refine ⟨{ a' with data := a.data ++ xs }, ?_, rfl, hlo⟩
  simp only [pushManyAny]
  rw [hres, bind_ok]
  have hhi := linAx_len a' hwf
  have hxl : (i64 (xs.length : Int)).val = xs.length := by
    rw [vlit, wrap_id _ (by omega) (by rw [tmax_eq] at hle; omega)]
  have he : ((linearAxis a').hi - i64 (xs.length : Int)).val =
      wrapInt .i64 ((linearAxis a').lo.val + ((a.data.length : Int) - 1)) := by
    rw [vsub, hxl, show (linearAxis a').hi.val - (xs.length : Int) =
      (linearAxis a').lo.val + ((a.data.length : Int) - 1) by omega]
  have h := pushManyLoop_from a' hwf _ _ (by omega) he xs 1 a.data.length a'.data rfl (by omega)
    (by push_cast; omega)
  refine h.trans ?_
  rw [hkeep]

theorem push2_proven : Push2Spec := by
  intro C α elems push A a b hP
  obtain ⟨A1, e1, d1⟩ := hP A a
  obtain ⟨A2, e2, d2⟩ := hP A1 b
  exact ⟨A2, by simp only [push2, e1, bind_ok, e2], by rw [d2, d1]; simp⟩

theorem pushVar_gen {C α : Type} (elems : C → List α) (push : C → α → R C) (hP : PushContract elems push) :
    ∀ (cs : List α) (A : C) (a b c : α),
      ∃ r, pushVar push A a b c cs = .ok r ∧ elems r = elems A ++ (a :: b :: c :: cs)
  | [], A, a, b, c => by
    obtain ⟨A1, e1, d1⟩ := push2_proven elems push A a b hP
    obtain ⟨A2, e2, d2⟩ := hP A1 c
    exact ⟨A2, by simp only [pushVar, e1, bind_ok, e2], by rw [d2, d1]; simp⟩
  | [d], A, a, b, c => by
    obtain ⟨A1, e1, d1⟩ := push2_proven elems push A a b hP
    obtain ⟨A2, e2, d2⟩ := push2_proven elems push A1 c d hP
    exact ⟨A2, by simp only [pushVar, e1, bind_ok, e2], by rw [d2, d1]; simp⟩
  | d :: e :: es, A, a, b, c => by
    obtain ⟨A1, e1, d1⟩ := push2_proven elems push A a b hP
    obtain ⟨A2, e2, d2⟩ := pushVar_gen elems push hP es A1 c d e
    exact ⟨A2, by simp only [pushVar, e1, bind_ok, e2], by rw [d2, d1]; simp⟩

theorem pushVar_proven : PushVarSpec := by
  intro C α elems push A a b c cs hP
  exact pushVar_gen elems push hP cs A a b c

theorem pushfirst2_proven : Pushfirst2Spec := by
  intro C α elems pf A a b hP
  obtain ⟨A1, e1, d1⟩ := hP A b
  obtain ⟨A2, e2, d2⟩ := hP A1 a
  exact ⟨A2, by simp only [pushfirst2, e1, bind_ok, e2], by rw [d2, d1]⟩

theorem pushfirstVar_gen {C α : Type} (elems : C → List α) (pf : C → α → R C)
    (hP : PushfirstContract elems pf) :
    ∀ (cs : List α) (A : C) (a b c : α),
      ∃ r, pushfirstVar pf A a b c cs = .ok r ∧ elems r = (a :: b :: c :: cs) ++ elems A
  | [], A, a, b, c => by
    obtain ⟨A1, e1, d1⟩ := hP A c
    obtain ⟨A2, e2, d2⟩ := pushfirst2_proven elems pf A1 a b hP
    exact ⟨A2, by simp only [pushfirstVar, e1, bind_ok, e2], by rw [d2, d1]; simp⟩
  | [d], A, a, b, c => by
    obtain ⟨A1, e1, d1⟩ := pushfirst2_proven elems pf A c d hP
    obtain ⟨A2, e2, d2⟩ := pushfirst2_proven elems pf A1 a b hP
    exact ⟨A2, by simp only [pushfirstVar, e1, bind_ok, e2], by rw [d2, d1]; simp⟩
  | d :: e :: es, A, a, b, c => by
    obtain ⟨A1, e1, d1⟩ := pushfirstVar_gen elems pf hP es A c d e
    obtain ⟨A2, e2, d2⟩ := pushfirst2_proven elems pf A1 a b hP
    exact ⟨A2, by simp only [pushfirstVar, e1, bind_ok, e2], by rw [d2, d1]; simp⟩

theorem pushfirstVar_proven : PushfirstVarSpec := by
  intro C α elems pf A a b c cs hP
  exact pushfirstVar_gen elems pf hP cs A a b c

end JuliaLean.AbstractArraySpecs
