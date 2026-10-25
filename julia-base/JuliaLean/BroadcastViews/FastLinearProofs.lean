import JuliaLean.BroadcastViews.FastLinear
import JuliaLean.ReinterpretArrays.Wrap

/-! Fast linear indexing of views reads the element that Cartesian indexing reads. -/

namespace JuliaLean.BroadcastViews

open JuliaLean JuliaLean.ReinterpretArrays

/-- Product of the parent dimensions. -/
def prodDims : List Int → Int
  | [] => 1
  | n :: ns => n * prodDims ns

/-- Every index lies inside its parent axis `1:n` (ranges: every element; empty ranges allowed). -/
def IdxInBounds : List I64 → List LIdx → Prop
  | [], [] => True
  | n :: ns, .scalar c :: is => 1 ≤ c.val ∧ c.val ≤ n.val ∧ IdxInBounds ns is
  | n :: ns, .slice :: is => 0 ≤ n.val ∧ IdxInBounds ns is
  | n :: ns, .urange lo len :: is =>
    0 ≤ n.val ∧ 0 ≤ len.val ∧ (0 < len.val → 1 ≤ lo.val ∧ lo.val + len.val - 1 ≤ n.val) ∧ IdxInBounds ns is
  | n :: ns, .srange st step len :: is =>
    0 ≤ n.val ∧ 0 ≤ len.val ∧
      (∀ k : Int, 1 ≤ k → k ≤ len.val → 1 ≤ st.val + (k - 1) * step.val ∧ st.val + (k - 1) * step.val ≤ n.val) ∧
      IdxInBounds ns is
  | _, _ => False

/-- One view subscript per view dimension, each in `1:d`. -/
def JsInBounds : List Int → List Int → Prop
  | [], [] => True
  | d :: ds, j :: js => 1 ≤ j ∧ j ≤ d ∧ JsInBounds ds js
  | _, _ => False

/-- For a view `V = view(A, I...)` of an `Array` `A` whose indices make `V` a fast linear
`SubArray` (`IndexStyle(V) == IndexLinear()`), `V[i]` with `i = LinearIndices(V)[js...]` reads the
parent element `A[reindex(I, js)...]` that Cartesian indexing `V[js...]` reads, for every
in-bounds view of a parent whose length is an `Int`. -/
def FastLinearView : Prop :=
  ∀ (ns : List I64) (I : List LIdx) (js : List Int),
    viewLinear I = true → IdxInBounds ns I → prodDims (ns.map (·.val)) ≤ IntTy.max .i64 →
    JsInBounds (viewDims (ns.map (·.val)) I) js →
    (fastParentIndex ns I (JInt.lit .i64 (1 + colMajor 1 (viewDims (ns.map (·.val)) I) js))).val =
      1 + colMajor 1 (ns.map (·.val)) (parentSubs I js)

/-! ### Exact arithmetic -/

/-- `Σ (first(I[d]) - 1) * P_d`: the exact `compute_linindex` offset. -/
def linAcc (P : Int) : List Int → List LIdx → Int
  | n :: ns, i :: is => (i.first.val - 1) * P + linAcc (P * n) ns is
  | _, _ => 0

/-- `compute_stride1` in exact arithmetic. -/
def stE (s : Int) : List Int → List LIdx → Int
  | _, [] => s
  | ns, i :: is =>
    if (i :: is).all LIdx.isScalar then s
    else match i, ns with
      | .scalar _, n :: ns' => stE (s * n) ns' is
      | .scalar _, [] => stE (s * 1) [] is
      | .slice, _ => s
      | .urange _ _, _ => s * 1
      | .srange _ st _, _ => s * st.val

private theorem colMajor_homog (c : Int) : ∀ (P : Int) (ds js : List Int),
    colMajor (c * P) ds js = c * colMajor P ds js
  | _, [], _ => by simp [colMajor]
  | _, _ :: _, [] => by simp [colMajor]
  | P, d :: ds, j :: js => by
    simp only [colMajor]
    rw [show c * P * d = c * (P * d) by rw [Int.mul_assoc], colMajor_homog c (P * d) ds js]
    rw [Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm (j - 1) c]

private theorem allScalar_parts : ∀ (P : Int) (ns : List Int) (is : List LIdx) (js : List Int),
    is.all LIdx.isScalar = true → ns.length = is.length →
    viewDims ns is = [] ∧ colMajor P ns (parentSubs is js) = linAcc P ns is
  | _, [], [], _, _, _ => by simp [viewDims, parentSubs, colMajor, linAcc]
  | P, n :: ns, .scalar c :: is, js, h, hl => by
    simp only [List.all_cons, LIdx.isScalar, Bool.true_and] at h
    obtain ⟨h1, h2⟩ := allScalar_parts (P * n) ns is js h (by simpa using hl)
    refine ⟨by simpa [viewDims] using h1, ?_⟩
    simp only [parentSubs, colMajor, linAcc, LIdx.first]
    rw [h2]
  | _, _ :: _, .slice :: _, _, h, _ => by simp [LIdx.isScalar] at h
  | _, _ :: _, .urange _ _ :: _, _, h, _ => by simp [LIdx.isScalar] at h
  | _, _ :: _, .srange _ _ _ :: _, _, h, _ => by simp [LIdx.isScalar] at h
  | _, [], _ :: _, _, _, hl => by simp at hl
  | _, _ :: _, [], _, _, hl => by simp at hl

/-- The `Slice…Slice[, UnitRange], scalars…` tail accepted after a leading `Slice`. -/
def sliceChain : List LIdx → Bool
  | .slice :: is => sliceChain is
  | .urange _ _ :: is => is.all LIdx.isScalar
  | is => is.all LIdx.isScalar

private theorem viewLinear_slice : ∀ (is : List LIdx), viewLinear (.slice :: is) = true → sliceChain is = true
  | [], _ => by simp [sliceChain]
  | .slice :: is, h => by
    simp only [viewLinear] at h
    simpa [sliceChain] using viewLinear_slice is h
  | .urange _ _ :: is, h => by simpa [viewLinear, sliceChain] using h
  | .scalar c :: is, h => by simpa [viewLinear, sliceChain] using h
  | .srange _ _ _ :: is, h => by simp [viewLinear, LIdx.isScalar] at h

private theorem chain_exact : ∀ (P : Int) (ns : List Int) (C : List LIdx) (js : List Int),
    sliceChain C = true → ns.length = C.length → (viewDims ns C).length = js.length →
    colMajor P ns (parentSubs C js) = linAcc P ns C + P * colMajor 1 (viewDims ns C) js
  | P, ns, [], js, _, _, hj => by
    cases ns <;> simp [parentSubs, colMajor, linAcc, viewDims]
  | P, n :: ns, .slice :: C, j :: js, hc, hl, hj => by
    simp only [sliceChain] at hc
    have ih := chain_exact (P * n) ns C js hc (by simpa using hl) (by simpa [viewDims] using hj)
    simp only [parentSubs, colMajor, linAcc, viewDims, LIdx.sub, LIdx.first, LIdx.vlen,
      List.headD_cons, List.tail_cons]
    rw [ih, show (1 : Int) * n = n * 1 by rw [Int.one_mul, Int.mul_one], colMajor_homog]
    have e : (i64 1).val = 1 := by decide
    rw [e]
    generalize linAcc (P * n) ns C = A
    generalize colMajor 1 (viewDims ns C) js = B
    grind
  | _, n :: ns, .slice :: C, [], hc, hl, hj => by simp [viewDims] at hj
  | P, n :: ns, .urange lo len :: C, js, hc, hl, hj => by
    simp only [sliceChain] at hc
    obtain ⟨hv, hs⟩ := allScalar_parts (P * n) ns C (js.drop 1) hc (by simpa using hl)
    cases js with
    | nil => simp [viewDims, hv] at hj
    | cons j js =>
      have hjs : js = [] := by simpa [viewDims, hv] using hj
      subst hjs
      have hs' := allScalar_parts (P * n) ns C [] hc (by simpa using hl)
      simp only [parentSubs, colMajor, linAcc, viewDims, List.tail_cons, List.headD_cons, hv, LIdx.sub,
        LIdx.first, LIdx.vlen, hs'.2]
      generalize linAcc (P * n) ns C = A
      grind
  | P, n :: ns, .scalar c :: C, js, hc, hl, hj => by
    have hc' : (LIdx.scalar c :: C).all LIdx.isScalar = true := by simpa [sliceChain] using hc
    obtain ⟨hv, hs⟩ := allScalar_parts P (n :: ns) (.scalar c :: C) js hc' (by simpa using hl)
    rw [hs, hv]
    simp [colMajor]
  | _, _ :: _, .srange _ _ _ :: _, _, hc, _, _ => by simp [sliceChain, LIdx.isScalar] at hc
  | _, [], _ :: _, _, _, hl, _ => by simp at hl

private theorem lin_exact : ∀ (P : Int) (ns : List Int) (I : List LIdx) (js : List Int),
    viewLinear I = true → ns.length = I.length → (viewDims ns I).length = js.length →
    colMajor P ns (parentSubs I js) = linAcc P ns I + stE P ns I * colMajor 1 (viewDims ns I) js
  | P, ns, [], js, _, _, _ => by cases ns <;> simp [parentSubs, colMajor, linAcc, stE, viewDims]
  | P, n :: ns, .scalar c :: is, js, h, hl, hj => by
    simp only [viewLinear] at h
    have ih := lin_exact (P * n) ns is js h (by simpa using hl) (by simpa [viewDims] using hj)
    simp only [parentSubs, colMajor, linAcc, LIdx.first, viewDims, List.tail_cons]
    rw [ih]
    by_cases ha : (LIdx.scalar c :: is).all LIdx.isScalar = true
    · have e : stE P (n :: ns) (.scalar c :: is) = P := by simp [stE, ha]
      have hv := (allScalar_parts (P * n) ns is js (by simpa [LIdx.isScalar] using ha) (by simpa using hl)).1
      rw [e, hv]
      simp [colMajor]
    · have e : stE P (n :: ns) (.scalar c :: is) = stE (P * n) ns is := by simp [stE, ha]
      rw [e, Int.add_assoc]
  | P, n :: ns, .slice :: is, js, h, hl, hj => by
    have hc := chain_exact P (n :: ns) (.slice :: is) js (by simpa [sliceChain] using viewLinear_slice is h) hl hj
    rw [hc]
    have : stE P (n :: ns) (.slice :: is) = P := by simp [stE, LIdx.isScalar]
    rw [this]
  | P, n :: ns, .urange lo len :: is, js, h, hl, hj => by
    have hc := chain_exact P (n :: ns) (.urange lo len :: is) js (by simpa [viewLinear, sliceChain] using h) hl hj
    rw [hc]
    have : stE P (n :: ns) (.urange lo len :: is) = P := by simp [stE, LIdx.isScalar]
    rw [this]
  | P, n :: ns, .srange st step len :: is, js, h, hl, hj => by
    simp only [viewLinear] at h
    obtain ⟨hv, hs⟩ := allScalar_parts (P * n) ns is [] h (by simpa using hl)
    cases js with
    | nil => simp [viewDims, hv] at hj
    | cons j js =>
      have hjs : js = [] := by simpa [viewDims, hv] using hj
      subst hjs
      have hst : stE P (n :: ns) (.srange st step len :: is) = P * step.val := by simp [stE, LIdx.isScalar]
      rw [hst]
      simp only [parentSubs, colMajor, linAcc, viewDims, hv, LIdx.sub, LIdx.first, LIdx.vlen, hs,
        List.tail_cons]
      generalize linAcc (P * n) ns is = A
      grind
  | _, [], _ :: _, _, _, hl, _ => by simp at hl

/-! ### Congruence modulo `2^64` -/

/-- Congruence modulo `2^64`. -/
private def C (a b : Int) : Prop := wrapInt .i64 a = wrapInt .i64 b

private theorem cg_refl (a : Int) : C a a := rfl
private theorem cg_trans {a b c : Int} (h1 : C a b) (h2 : C b c) : C a c := Eq.trans h1 h2
private theorem cg_of_eq {a b : Int} (h : a = b) : C a b := by rw [h]; exact cg_refl b
private theorem cg_add {a a' b b' : Int} (h1 : C a a') (h2 : C b b') : C (a + b) (a' + b') := by
  unfold C at *; rw [← wrapInt_add .i64 a b, h1, h2, wrapInt_add]
private theorem cg_sub {a a' b b' : Int} (h1 : C a a') (h2 : C b b') : C (a - b) (a' - b') := by
  unfold C at *; rw [← wrapInt_sub .i64 a b, h1, h2, wrapInt_sub]
private theorem cg_mul {a a' b b' : Int} (h1 : C a a') (h2 : C b b') : C (a * b) (a' * b') := by
  unfold C at *; rw [← wrapInt_mul .i64 a b, h1, h2, wrapInt_mul]
private theorem cg_val_add (x y : I64) : C (x + y).val (x.val + y.val) := by
  unfold C; rw [val_add, wrapInt_wrapInt]
private theorem cg_val_sub (x y : I64) : C (x - y).val (x.val - y.val) := by
  unfold C; rw [val_sub, wrapInt_wrapInt]
private theorem cg_val_mul (x y : I64) : C (x * y).val (x.val * y.val) := by
  unfold C; rw [val_mul, wrapInt_wrapInt]
private theorem cg_lit (x : Int) : C (JInt.lit .i64 x).val x := by
  unfold C; rw [val_lit, wrapInt_wrapInt]

private theorem i64_one : (i64 1).val = 1 := by decide

private theorem stride_cg : ∀ (s : I64) (a : Int) (ns : List I64) (I : List LIdx), C s.val a →
    C (computeStride1 s ns I).val (stE a (ns.map (·.val)) I)
  | s, a, ns, [], h => by simpa [computeStride1, stE] using h
  | s, a, ns, i :: is, h => by
    unfold computeStride1 stE
    by_cases ha : (i :: is).all LIdx.isScalar = true
    · rw [if_pos ha, if_pos ha]; exact h
    · rw [if_neg ha, if_neg ha]
      cases i with
      | scalar c =>
        cases ns with
        | nil =>
          exact stride_cg _ _ [] is (cg_trans (cg_val_mul _ _) (cg_mul h (cg_of_eq i64_one)))
        | cons n ns => exact stride_cg _ _ ns is (cg_trans (cg_val_mul _ _) (cg_mul h (cg_refl _)))
      | slice => cases ns <;> exact h
      | urange lo len =>
        cases ns <;> exact cg_trans (cg_val_mul _ _) (cg_mul h (cg_of_eq i64_one))
      | srange st step len => cases ns <;> exact cg_trans (cg_val_mul _ _) (cg_mul h (cg_refl _))

private theorem linindex_cg : ∀ (f s : I64) (fa sa : Int) (ns : List I64) (I : List LIdx),
    ns.length = I.length → C f.val fa → C s.val sa →
    C (computeLinindex f s ns I).val (fa + linAcc sa (ns.map (·.val)) I)
  | f, s, fa, sa, [], [], _, hf, _ => by simpa [computeLinindex, linAcc] using hf
  | f, s, fa, sa, [n], [i], _, hf, hs => by
    simp only [computeLinindex, List.map_cons, List.map_nil, linAcc]
    refine cg_trans (cg_val_add _ _) (cg_trans (cg_add hf (cg_trans (cg_val_mul _ _)
      (cg_mul (cg_trans (cg_val_sub _ _) (cg_of_eq (by rw [i64_one]))) hs))) (cg_of_eq ?_))
    simp [linAcc]
  | f, s, fa, sa, n :: n' :: ns, i :: i' :: is, hl, hf, hs => by
    have ih := linindex_cg (f + (i.first - i64 1) * s) (s * n) (fa + (i.first.val - 1) * sa) (sa * n.val)
      (n' :: ns) (i' :: is) (by simpa using hl)
      (cg_trans (cg_val_add _ _) (cg_add hf (cg_trans (cg_val_mul _ _)
        (cg_mul (cg_trans (cg_val_sub _ _) (cg_of_eq (by rw [i64_one]))) hs))))
      (cg_trans (cg_val_mul _ _) (cg_mul hs (cg_refl _)))
    show C (computeLinindex (f + (i.first - i64 1) * s) (s * n) (n' :: ns) (i' :: is)).val _
    refine cg_trans ih (cg_of_eq ?_)
    simp only [List.map_cons, linAcc]
    omega
  | _, _, _, _, [], _ :: _, hl, _, _ => by simp at hl
  | _, _, _, _, _ :: _, [], hl, _, _ => by simp at hl
  | _, _, _, _, [_], _ :: _ :: _, hl, _, _ => by simp at hl
  | _, _, _, _, _ :: _ :: _, [_], hl, _, _ => by simp at hl

/-! ### Bounds -/

private theorem idx_len : ∀ (ns : List I64) (I : List LIdx), IdxInBounds ns I → ns.length = I.length
  | [], [], _ => rfl
  | _ :: ns, .scalar _ :: is, h => by simpa using idx_len ns is h.2.2
  | _ :: ns, .slice :: is, h => by simpa using idx_len ns is h.2
  | _ :: ns, .urange _ _ :: is, h => by simpa using idx_len ns is h.2.2.2
  | _ :: ns, .srange _ _ _ :: is, h => by simpa using idx_len ns is h.2.2.2
  | [], _ :: _, h => by simp [IdxInBounds] at h
  | _ :: _, [], h => by simp [IdxInBounds] at h

private theorem js_len : ∀ (ds js : List Int), JsInBounds ds js → ds.length = js.length
  | [], [], _ => rfl
  | _ :: ds, _ :: js, h => by simpa using js_len ds js h.2.2
  | [], _ :: _, h => by simp [JsInBounds] at h
  | _ :: _, [], h => by simp [JsInBounds] at h

/-- Every parent subscript lies in `1:n`. -/
private def SubsIn : List Int → List Int → Prop
  | [], [] => True
  | n :: ns, s :: ss => 1 ≤ s ∧ s ≤ n ∧ SubsIn ns ss
  | _, _ => False

private theorem subs_in : ∀ (ns : List I64) (I : List LIdx) (js : List Int),
    IdxInBounds ns I → JsInBounds (viewDims (ns.map (·.val)) I) js →
    SubsIn (ns.map (·.val)) (parentSubs I js)
  | [], [], js, _, hj => by
    cases js <;> simp_all [parentSubs, SubsIn, viewDims, JsInBounds]
  | n :: ns, .scalar c :: is, js, h, hj => by
    simp only [IdxInBounds] at h
    simp only [viewDims, List.map_cons, List.tail_cons] at hj
    exact ⟨h.1, h.2.1, subs_in ns is js h.2.2 hj⟩
  | n :: ns, .slice :: is, j :: js, h, hj => by
    simp only [IdxInBounds] at h
    simp only [viewDims, List.map_cons, List.tail_cons, List.headD_cons, LIdx.vlen, JsInBounds] at hj
    exact ⟨hj.1, hj.2.1, subs_in ns is js h.2 hj.2.2⟩
  | n :: ns, .urange lo len :: is, j :: js, h, hj => by
    simp only [IdxInBounds] at h
    simp only [viewDims, List.map_cons, List.tail_cons, List.headD_cons, LIdx.vlen, JsInBounds] at hj
    have hb := h.2.2.1 (by omega)
    exact ⟨by simp only [LIdx.sub]; omega, by simp only [LIdx.sub]; omega, subs_in ns is js h.2.2.2 hj.2.2⟩
  | n :: ns, .srange st step len :: is, j :: js, h, hj => by
    simp only [IdxInBounds] at h
    simp only [viewDims, List.map_cons, List.tail_cons, List.headD_cons, LIdx.vlen, JsInBounds] at hj
    have hb := h.2.2.1 j hj.1 hj.2.1
    exact ⟨hb.1, hb.2, subs_in ns is js h.2.2.2 hj.2.2⟩
  | _ :: _, .slice :: _, [], _, hj => by simp [viewDims, JsInBounds] at hj
  | _ :: _, .urange _ _ :: _, [], _, hj => by simp [viewDims, JsInBounds] at hj
  | _ :: _, .srange _ _ _ :: _, [], _, hj => by simp [viewDims, JsInBounds] at hj
  | [], _ :: _, _, h, _ => by simp [IdxInBounds] at h
  | _ :: _, [], _, h, _ => by simp [IdxInBounds] at h

private theorem colMajor_bounds : ∀ (P : Int) (ns ss : List Int), 0 ≤ P → SubsIn ns ss →
    0 ≤ colMajor P ns ss ∧ colMajor P ns ss ≤ P * prodDims ns - P
  | P, [], [], hP, _ => by simp [colMajor, prodDims]
  | P, n :: ns, s :: ss, hP, h => by
    obtain ⟨h1, h2, h3⟩ := h
    have hn : 0 ≤ P * n := Int.mul_nonneg hP (by omega)
    obtain ⟨ih1, ih2⟩ := colMajor_bounds (P * n) ns ss hn h3
    simp only [colMajor, prodDims]
    have a1 : 0 ≤ (s - 1) * P := Int.mul_nonneg (by omega) hP
    have a2 : (s - 1) * P ≤ (n - 1) * P := Int.mul_le_mul_of_nonneg_right (by omega) hP
    have a3 : P * (n * prodDims ns) = P * n * prodDims ns := by rw [Int.mul_assoc]
    have a4 : (n - 1) * P = P * n - P := by rw [Int.sub_mul, Int.one_mul, Int.mul_comm]
    constructor
    · omega
    · omega
  | _, [], _ :: _, _, h => by simp [SubsIn] at h
  | _, _ :: _, [], _, h => by simp [SubsIn] at h

private theorem max64 : IntTy.max .i64 = 9223372036854775807 := by decide
private theorem min64 : IntTy.min .i64 = -9223372036854775808 := by decide

theorem fastLinearView : FastLinearView := by
  intro ns I js hlin hI hmax hj
  have hlen := idx_len ns I hI
  have hlen' : (ns.map (·.val)).length = I.length := by simpa using hlen
  have hjl := js_len _ js hj
  -- exact identity
  have hex := lin_exact 1 (ns.map (·.val)) I js hlin hlen' hjl
  -- congruences
  have hst := stride_cg (i64 1) 1 ns I (cg_of_eq i64_one)
  have hL := linindex_cg (i64 1) (i64 1) 1 1 ns I hlen (cg_of_eq i64_one) (cg_of_eq i64_one)
  generalize hS : stE 1 (ns.map (·.val)) I = S at hst hex
  generalize hA : linAcc 1 (ns.map (·.val)) I = A at hL hex
  generalize hV : colMajor 1 (viewDims (ns.map (·.val)) I) js = V at hex ⊢
  have hcg : C (fastParentIndex ns I (JInt.lit .i64 (1 + V))).val (1 + colMajor 1 (ns.map (·.val)) (parentSubs I js)) := by
    unfold fastParentIndex computeOffset1
    dsimp only
    rw [hex]
    split
    · refine cg_trans (cg_val_add _ _) (cg_trans (cg_add (cg_trans (cg_val_sub _ _)
        (cg_sub hL (cg_trans (cg_val_mul _ _) (cg_mul hst (cg_of_eq i64_one))))) (cg_trans (cg_val_mul _ _)
        (cg_mul hst (cg_lit _)))) (cg_of_eq ?_))
      rw [Int.mul_add]; omega
    · refine cg_trans (cg_val_add _ _) (cg_trans (cg_add (cg_trans (cg_val_sub _ _) (cg_sub hL hst))
        (cg_trans (cg_val_mul _ _) (cg_mul hst (cg_lit _)))) (cg_of_eq ?_))
      rw [Int.mul_add]; omega
  -- bounds of the exact parent index
  have hsub := subs_in ns I js hI hj
  obtain ⟨b1, b2⟩ := colMajor_bounds 1 (ns.map (·.val)) (parentSubs I js) (by decide) hsub
  rw [Int.one_mul] at b2
  unfold C at hcg
  rw [← val_eq_wrap] at hcg
  rw [hcg]
  have e1 := min64
  have e2 := max64
  exact wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩

end JuliaLean.BroadcastViews
