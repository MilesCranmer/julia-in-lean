import JuliaLean.MultidimCov.SubarrayV2Linear

/-!
Cartesian access through `reindex` (`base/subarray.jl:292-321`) selects the
element of `A[I...][J...]` that the manual defines (`specPos`), for every index
kind, including arrays of `CartesianIndex`.
-/

namespace JuliaLean.MultidimCov.SubarrayV2

open JuliaLean.MultidimCov.ArrayV2 (wrap64)

/-- Index tuples valid for parent axes, with `CartesianIndex{k}` arrays consuming
`k` parent dimensions. -/
def IdxsOKC : List Ax → List Idx → Prop
  | axs, [] => axs = []
  | axs, .carr k dims xs :: is => ∃ a1 a2, axs = a1 ++ a2 ∧ a1.length = k ∧
      xs.length = dims.prod ∧ (∀ x ∈ xs, inAxes a1 x) ∧ IdxsOKC a2 is
  | [], _ :: _ => False
  | a :: axs, i :: is => IdxOK a i ∧ IdxsOKC axs is

theorem truePosFrom_length : ∀ (k : Int) (bs : List Bool), ((truePosFrom k bs).length : Int) = countTrue bs
  | _, [] => rfl
  | k, b :: bs => by
      cases b <;> simp [truePosFrom, countTrue, truePosFrom_length (k + 1) bs] <;> omega

theorem truePosFrom_mem : ∀ (k : Int) (bs : List Bool) (v : Int), v ∈ truePosFrom k bs →
    k ≤ v ∧ v ≤ k + bs.length - 1
  | _, [], _, h => by simp [truePosFrom] at h
  | k, b :: bs, v, h => by
      cases b
      · simp [truePosFrom] at h
        have := truePosFrom_mem (k + 1) bs v h
        simp; omega
      · simp [truePosFrom] at h
        rcases h with h | h
        · subst h; simp; omega
        · have := truePosFrom_mem (k + 1) bs v h
          simp; omega

theorem cmOff_lt : ∀ (dims : List Nat) (js : List Int),
    inAxes (dims.map (fun (d : Nat) => oneAx (d : Int))) js → ∃ k, cmOff dims js = some k ∧ k < dims.prod
  | [], [], _ => ⟨0, rfl, by simp⟩
  | d :: ds, j :: js, h => by
      obtain ⟨h1, h2, h3⟩ := h
      simp only [oneAx] at h1 h2
      obtain ⟨k, hk, hlt⟩ := cmOff_lt ds js h3
      refine ⟨(j - 1).toNat + d * k, ?_, ?_⟩
      · simp [cmOff, h1, h2, hk]
      · simp only [List.prod_cons]
        have : (j - 1).toNat < d := by omega
        have : d * k + d ≤ d * ds.prod := by
          have := Nat.mul_le_mul_left d (show k + 1 ≤ ds.prod by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; exact this
        omega
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem inAxesB_iff : ∀ (as : List Ax) (js : List Int), inAxesB as js = true ↔ inAxes as js
  | [], [] => by simp [inAxesB, inAxes]
  | a :: as, j :: js => by
      simp only [inAxesB, inAxes, Bool.and_eq_true, decide_eq_true_eq, inAxesB_iff as js]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  | [], _ :: _ => by simp [inAxesB, inAxes]
  | _ :: _, [] => by simp [inAxesB, inAxes]

theorem axOK_small (ax : Ax) (h : AxOK ax) (v : Int) (h1 : ax.lo ≤ v) (h2 : v ≤ ax.hi) :
    -2^63 ≤ v ∧ v < 2^63 := by unfold AxOK at h; omega

/-- One non-scalar, non-`CartesianIndex` index read at in-bounds subscripts. -/
theorem idxGet_spec (ax : Ax) (hax : AxOK ax) (i : Idx) (hi : IdxOK ax i) (hs : i.isScalar = false)
    (js : List Int) (hj : inAxes (idxAxes i) js) :
    ∃ v, idxAt i js = some [v] ∧ idxGetInt i js = .ok [v] ∧ ax.lo ≤ v ∧ v ≤ ax.hi := by
  cases i with
  | int _ => simp [Idx.isScalar] at hs
  | carr _ _ _ => exact hi.elim
  | arr dims xs =>
      obtain ⟨k, hk, hlt⟩ := cmOff_lt dims js (by simpa [idxAxes] using hj)
      have hkx : k < xs.length := by rw [hi.1]; exact hlt
      refine ⟨xs[k], ?_, ?_, (hi.2 _ (List.getElem_mem hkx)).1, (hi.2 _ (List.getElem_mem hkx)).2⟩
      · simp [idxAt, hk, List.getElem?_eq_getElem hkx]
      · simp [idxGetInt, hk, List.getElem?_eq_getElem hkx]
  | mask bs =>
      match js, hj with
      | [j], hj =>
        simp [idxAxes, inAxes, oneAx] at hj
        have hl := truePosFrom_length 1 bs
        have hlt : (j - 1).toNat < (truePos bs).length := by unfold truePos; omega
        have hm := truePosFrom_mem 1 bs _ (List.getElem_mem hlt)
        obtain ⟨hlen, hlo⟩ := hi
        have hlen' := Ax.len_eq ax (by unfold AxOK at hax; omega)
        refine ⟨(truePos bs)[(j - 1).toNat], ?_, ?_, ?_, ?_⟩
        · simp [idxAt, hj.1, List.getElem?_eq_getElem hlt]
        · simp only [idxGetInt]; rw [List.getElem?_eq_getElem hlt]; simp [hj.1]
        · unfold truePos at hm ⊢; omega
        · unfold truePos at hm ⊢; omega
  | slice a =>
      match js, hj with
      | [j], hj =>
        simp [idxAxes, inAxes] at hj
        simp [IdxOK] at hi; subst hi
        exact ⟨j, by simp [idxAt, Ax.mem, hj.1, hj.2], rfl, hj.1, hj.2⟩
  | ident a =>
      match js, hj with
      | [j], hj =>
        simp [idxAxes, inAxes] at hj
        have := hi.2 (by omega)
        exact ⟨j, by simp [idxAt, Ax.mem, hj.1, hj.2], rfl, by omega, by omega⟩
  | oneto n =>
      match js, hj with
      | [j], hj =>
        simp [idxAxes, inAxes, oneAx] at hj
        have := hi.2 (by omega)
        exact ⟨j, by simp [idxAt, hj.1, hj.2], rfl, by omega, by omega⟩
  | unit a =>
      match js, hj with
      | [j], hj =>
        have hv := rangeVal_in ax (.unit a) rfl hi j (by simpa [axes1Idx, idxAxes, inAxes] using hj)
        simp [idxAxes, inAxes, oneAx] at hj
        have hv' : ax.lo ≤ a.lo + (j - 1) ∧ a.lo + (j - 1) ≤ ax.hi := by
          simpa [rangeVal, fv, strideOf, idxStep, axes1Idx, idxAxes, oneAx] using hv
        have hsm := axOK_small ax hax _ hv'.1 hv'.2
        refine ⟨a.lo + (j - 1), by simp [idxAt, hj.1, hj.2], ?_, hv'.1, hv'.2⟩
        simp only [idxGetInt, iadd, isub, w_add_r]
        rw [w_id hsm.1 hsm.2]
  | step s st n =>
      match js, hj with
      | [j], hj =>
        have hv := rangeVal_in ax (.step s st n) rfl hi j (by simpa [axes1Idx, idxAxes, inAxes] using hj)
        simp [idxAxes, inAxes, oneAx] at hj
        simp [rangeVal, fv, strideOf, idxStep, axes1Idx, idxAxes, oneAx] at hv
        have e : st * (j - 1) = (j - 1) * st := Int.mul_comm _ _
        rw [e] at hv
        have hsm := axOK_small ax hax _ hv.1 hv.2
        refine ⟨s + (j - 1) * st, by simp [idxAt, hj.1, hj.2], ?_, hv.1, hv.2⟩
        simp only [idxGetInt, iadd, isub, imul, w_add_r, w_mul_l]
        rw [w_id hsm.1 hsm.2]

theorem reindexS_unfold (i : Idx) (I : List Idx) (J : List Int) (hi1 : i.isScalar = false)
    (hi2 : i.isSlice = false) :
    reindexS (i :: I) J =
    (if idxRank i = 1 then
      match J with
      | j :: js' => (do
          let v ← idxGetInt i [j]
          let r ← reindexS I js'
          pure (v ++ r))
      | [] => .error .bounds
    else if idxRank i = 2 then
      match J with
      | j1 :: j2 :: js' => (do
          let v ← idxGetInt i [j1, j2]
          let r ← reindexS I js'
          pure (v ++ r))
      | _ => .error .bounds
    else if J.length < idxRank i then .error .bounds
    else (do
      let v ← idxGetInt i (J.take (idxRank i))
      let r ← reindexS I (J.drop (idxRank i))
      pure (v ++ r))) := by
  cases i <;> simp [Idx.isScalar, Idx.isSlice] at hi1 hi2 <;> rfl

theorem reindexS_gen (i : Idx) (I : List Idx) (J : List Int) (hi1 : i.isScalar = false)
    (hi2 : i.isSlice = false) (hJ : idxRank i ≤ J.length) :
    reindexS (i :: I) J = (do
      let v ← idxGetInt i (J.take (idxRank i))
      let r ← reindexS I (J.drop (idxRank i))
      pure (v ++ r)) := by
  rw [reindexS_unfold i I J hi1 hi2]
  by_cases h1 : idxRank i = 1
  · rw [if_pos h1]
    match J, hJ with
    | j :: J', _ => simp [h1]
    | [], h => simp [h1] at h
  · rw [if_neg h1]
    by_cases h2 : idxRank i = 2
    · rw [if_pos h2]
      match J, hJ with
      | j1 :: j2 :: J', _ => simp [h2]
      | [], h => simp [h2] at h
      | [_], h => simp [h2] at h
    · rw [if_neg h2, if_neg (by omega)]

theorem inAxes_split : ∀ (a1 a2 : List Ax) (J : List Int), inAxes (a1 ++ a2) J →
    inAxes a1 (J.take a1.length) ∧ inAxes a2 (J.drop a1.length)
  | [], a2, J, h => ⟨trivial, by simpa using h⟩
  | a :: a1, a2, j :: J, h => by
      have := inAxes_split a1 a2 J h.2.2
      exact ⟨⟨h.1, h.2.1, this.1⟩, this.2⟩
  | _ :: _, _, [], h => h.elim

theorem idxRank_eq (i : Idx) : idxRank i = (idxAxes i).length := rfl

/-- `reindex` (lines 292-312) maps in-bounds subscripts to the manual's parent position. -/
theorem reindexS_spec : ∀ (I : List Idx) (axs : List Ax) (J : List Int), (∀ a ∈ axs, AxOK a) →
    IdxsOKC axs I → inAxes (viewAxes I) J →
    ∃ pos, specPos I J = some pos ∧ reindexS I J = .ok pos ∧ inAxes axs pos
  | [], axs, J, _, hok, hJ => by
      simp only [IdxsOKC] at hok; subst hok
      cases J with
      | nil => exact ⟨[], rfl, rfl, trivial⟩
      | cons _ _ => exact hJ.elim
  | i :: I, axs, J, hax, hok, hJ => by
      rw [viewAxes_cons] at hJ
      have hsp := inAxes_split _ _ J hJ
      rw [← idxRank_eq] at hsp
      have hlenJ : idxRank i ≤ J.length := by
        have := inAxes_length hsp.1
        rw [List.length_take] at this
        rw [idxRank_eq]; omega
      cases hci : i with
      | carr k dims xs =>
          subst hci
          obtain ⟨a1, a2, he, hl, hxl, hxin, hrest⟩ := hok
          obtain ⟨c, hc, hclt⟩ := cmOff_lt dims (J.take (idxRank (.carr k dims xs)))
            (by simpa [idxAxes] using hsp.1)
          have hcx : c < xs.length := by rw [hxl]; exact hclt
          obtain ⟨pos, h1, h2, h3⟩ := reindexS_spec I a2 _
            (fun x hx => hax x (by rw [he]; exact List.mem_append_right _ hx)) hrest hsp.2
          refine ⟨xs[c] ++ pos, ?_, ?_, ?_⟩
          · rw [specPos]; simp [idxAt, hc, List.getElem?_eq_getElem hcx, h1]
          · rw [reindexS_gen _ I J rfl rfl hlenJ]
            simp [idxGetInt, hc, List.getElem?_eq_getElem hcx, h2]
          · rw [he]; exact inAxes_append (hxin _ (List.getElem_mem hcx)) h3
      | int n =>
          subst hci
          match axs, hok with
          | a :: axs', ⟨hi, hrest⟩ =>
            obtain ⟨pos, h1, h2, h3⟩ := reindexS_spec I axs' J
              (fun x hx => hax x (List.mem_cons_of_mem _ hx)) hrest (by simpa [idxRank, idxAxes] using hsp.2)
            refine ⟨n :: pos, ?_, ?_, ⟨hi.1, hi.2, h3⟩⟩
            · simp [specPos, idxRank, idxAxes, idxAt, h1]
            · simp [reindexS, h2]
      | slice a =>
          subst hci
          match axs, hok, J, hsp with
          | b :: axs', ⟨hi, hrest⟩, j :: J', hsp =>
            obtain ⟨v, hv1, hv2, hv3, hv4⟩ := idxGet_spec b (hax b (by simp)) (.slice a) hi rfl [j]
              (by simpa [idxRank, idxAxes] using hsp.1)
            obtain ⟨pos, h1, h2, h3⟩ := reindexS_spec I axs' J'
              (fun x hx => hax x (List.mem_cons_of_mem _ hx)) hrest (by simpa [idxRank, idxAxes] using hsp.2)
            have hvj : v = j := by simp [idxGetInt] at hv2; exact hv2.symm
            subst hvj
            refine ⟨v :: pos, ?_, ?_, ⟨hv3, hv4, h3⟩⟩
            · rw [specPos]; simp [idxRank, idxAxes] at hv1 ⊢; simp [hv1, h1]
            · simp [reindexS, h2]
          | b :: axs', _, [], hsp => simp [idxRank, idxAxes, inAxes] at hsp
      | _ =>
          subst hci
          match axs, hok with
          | b :: axs', ⟨hi, hrest⟩ =>
            obtain ⟨v, hv1, hv2, hv3, hv4⟩ := idxGet_spec b (hax b (by simp)) _ hi rfl _ hsp.1
            obtain ⟨pos, h1, h2, h3⟩ := reindexS_spec I axs' _
              (fun x hx => hax x (List.mem_cons_of_mem _ hx)) hrest hsp.2
            refine ⟨v :: pos, ?_, ?_, ⟨hv3, hv4, h3⟩⟩
            · rw [specPos]; simp [hv1, h1]
            · rw [reindexS_gen _ I J rfl rfl hlenJ]; simp [hv2, h2]

end JuliaLean.MultidimCov.SubarrayV2
