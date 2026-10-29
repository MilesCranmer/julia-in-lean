import JuliaLean.MultidimCov.ArrayV2Collect
import JuliaLean.MultidimCov.ArrayV2LiteralsProps

/-! Contracts of the models in `ArrayV2Collect`. -/

namespace JuliaLean.MultidimCov.ArrayV2

/-! ### The type universe -/

theorem subT_refl (a : VT) : subT a a = true := by cases a <;> rfl

theorem subT_trans : ∀ a b c : VT, subT a b = true → subT b c = true → subT a c = true := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

theorem subT_join_left : ∀ a b : VT, subT a (typejoinT a b) = true := by
  intro a b; cases a <;> cases b <;> decide

theorem subT_join_right : ∀ a b : VT, subT b (typejoinT a b) = true := by
  intro a b; cases a <;> cases b <;> decide

theorem join_of_sub : ∀ a b : VT, subT b a = true → typejoinT a b = a := by
  intro a b; cases a <;> cases b <;> decide

theorem join_ptj : ∀ a b U : VT, subT a (ptjUnion U) = true → subT b (ptjUnion U) = true →
    subT (typejoinT a b) (ptjUnion U) = true := by
  intro a b U; cases a <;> cases b <;> cases U <;> decide

theorem sub_ptj : ∀ t U : VT, subT t U = true → subT t (ptjUnion U) = true := by
  intro t U; cases t <;> cases U <;> decide

theorem concrete_sub : ∀ t c : VT, isConcreteT c = true → subT t c = true → t = c := by
  intro t c; cases t <;> cases c <;> decide

theorem convertV_isa {x : JV} {T : VT} (h : isaV x T = true) : convertV T x = .ok x := by
  unfold convertV; rw [if_pos h]

theorem convList_isa {T : VT} : ∀ xs : List JV, (∀ x ∈ xs, isaV x T = true) → convList (convertV T) xs = .ok xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [convList, convertV_isa (h x (by simp)), bind_ok,
      convList_isa xs (fun y hy => h y (by simp [hy])), pure_ok]

/-- `promote_typejoin` of the types of the values, starting from `T`. -/
def joinTypes (T : VT) (xs : List JV) : VT := xs.foldl (fun T y => typejoinT T (typeofV y)) T

theorem joinTypes_isa : ∀ (xs : List JV) (T : VT), (∀ x ∈ xs, isaV x (joinTypes T xs) = true) ∧
    subT T (joinTypes T xs) = true
  | [], T => ⟨by simp, subT_refl T⟩
  | x :: xs, T => by
    obtain ⟨h1, h2⟩ := joinTypes_isa xs (typejoinT T (typeofV x))
    refine ⟨fun y hy => ?_, subT_trans _ _ _ (subT_join_left T (typeofV x)) h2⟩
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact subT_trans _ _ _ (subT_join_right T (typeofV y)) h2
    · exact h1 y hy

theorem joinTypes_bound (B : VT) : ∀ (xs : List JV) (T : VT), subT T (ptjUnion B) = true →
    (∀ x ∈ xs, subT (typeofV x) B = true) → subT (joinTypes T xs) (ptjUnion B) = true
  | [], _, h, _ => h
  | x :: xs, T, h, hx =>
    joinTypes_bound B xs _ (join_ptj _ _ _ h (sub_ptj _ _ (hx x (by simp))))
      (fun y hy => hx y (by simp [hy]))

/-! ### Slots during `collect_to!` -/

/-- The destination during `collect_to!`: a valid array of size `D` (nonnegative,
`N` elements) whose first slots hold `pre` and whose other slots are unset. -/
def SlotInv (a : Arr JV) (D : List Int) (N : Int) (pre : List JV) : Prop :=
  Valid a ∧ a.dims = D ∧ length a = N ∧ (∀ d ∈ D, 0 ≤ d) ∧ N ≤ 2 ^ 59 ∧
    ∀ k : Nat, (k : Int) < N → a.at ((k : Int) + 1) = pre[k]?

theorem getElem?_append_one (pre : List JV) (el : JV) (k : Nat) :
    (pre ++ [el])[k]? = if k = pre.length then some el else pre[k]? := by
  by_cases h : k < pre.length
  · rw [List.getElem?_append_left h, if_neg (by omega)]
  · rw [List.getElem?_append_right (by omega)]
    by_cases h2 : k = pre.length
    · subst h2; simp
    · rw [if_neg h2, List.getElem?_eq_none (show pre.length ≤ k by omega)]
      have : k - pre.length ≠ 0 := by omega
      simp [this]

theorem valid_setU {a : Arr α} (i : Int) (x : Option α) (h : Valid a) : Valid (setU a i x) := by
  simpa [Valid] using h

theorem slotInv_set {a : Arr JV} {D : List Int} {N : Int} {pre : List JV} (h : SlotInv a D N pre) (el : JV) :
    SlotInv (setU a (pre.length + 1) (some el)) D N (pre ++ [el]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨valid_setU _ _ h1, by simpa using h2, by simpa using h3, h4, h5, fun k hk => ?_⟩
  rw [setU_at, getElem?_append_one]
  by_cases hk2 : k = pre.length
  · subst hk2; simp
  · rw [if_neg (by omega), if_neg hk2, h6 k hk]

theorem fresh_slotInv {b : Arr JV} {D : List Int} (hf : Fresh b D) (h0 : ∀ d ∈ D, 0 ≤ d)
    (hN : D.foldr (· * ·) 1 ≤ 2 ^ 59) : SlotInv b D (D.foldr (· * ·) 1) [] := by
  obtain ⟨h1, h2, h3⟩ := hf
  have hl : length b = D.foldr (· * ·) 1 := by simp [length, h1]
  refine ⟨h2, h1, hl, h0, hN, fun k hk => ?_⟩
  have hk' : k < (contents b).length := by simp [contents_length, hl]; omega
  rw [← getElem_contents b k hk']
  simp [h3]

theorem m895_spec : ∀ (rest : List JV) (d : TA) (pre : List JV) (D : List Int) (N : Int),
    SlotInv d.a D N pre → pre ≠ [] → pre.length + rest.length = N → (∀ x ∈ pre, isaV x d.et = true) →
    ∃ a', m895 d rest (pre.length + 1) = .ok ⟨joinTypes d.et rest, a'⟩ ∧ SlotInv a' D N (pre ++ rest)
  | [], d, pre, D, N, h, _, _, _ => ⟨d.a, by simp [m895, joinTypes], by simpa using h⟩
  | el :: rest, d, pre, D, N, h, hne, hl, hisa => by
    simp only [List.length_cons] at hl
    unfold m895
    by_cases hel : isaV el d.et = true
    · rw [if_pos hel]
      obtain ⟨a', e, h'⟩ := m895_spec rest ⟨d.et, setU d.a (pre.length + 1) (some el)⟩ (pre ++ [el]) D N
        (slotInv_set h el) (by simp) (by simp; omega)
        (fun x hx => by simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact hisa x hx; exact hel)
      have hj : joinTypes d.et (el :: rest) = joinTypes d.et rest := by
        simp only [joinTypes, List.foldl_cons]; rw [join_of_sub _ _ hel]
      refine ⟨a', ?_, by simpa using h'⟩
      rw [hj]; simpa [Int.add_assoc, Int.add_comm 1] using e
    · rw [if_neg hel]
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      have hpl : 1 ≤ pre.length := by cases pre; exact absurd rfl hne; simp
      have hN0 : 0 ≤ N := by omega
      have hD : D.foldr (· * ·) 1 = N := by rw [← h3]; simp [length, h2]
      obtain ⟨b, eb, hfb⟩ := newArray_ok (α := JV) (dims := D) h4 (by unfold typemaxInt; omega)
      obtain ⟨bd, bv, bc⟩ := hfb
      have hlb : length b = N := by simp [length, bd, hD]
      obtain ⟨c, ec, hcd, hcv, hcp⟩ := m299_vec (c := (pre.length : Int)) bv h1 (by omega) (by omega)
        (doffs := 1) (soffs := 1) (by omega) (Int.le_refl _) (by omega) (Int.le_refl _) (by omega)
      have hbat : ∀ k : Nat, (k : Int) < N → b.at ((k : Int) + 1) = none := by
        intro k hk
        have hk' : k < (contents b).length := by simp [contents_length, hlb]; omega
        rw [← getElem_contents b k hk']; simp [bc]
      have hinv : SlotInv c D N pre := by
        refine ⟨hcv, by rw [hcd, bd], by simp [length, hcd, bd, hD], h4, h5, fun k hk => ?_⟩
        rw [hcp _ (by omega) (by simp [hlb]; omega)]
        by_cases hk2 : (k : Int) + 1 < 1 + pre.length
        · rw [if_pos ⟨by omega, hk2⟩, show (k : Int) + 1 - 1 + 1 = (k : Int) + 1 by omega, h6 k hk]
        · rw [if_neg (by omega), hbat k hk, List.getElem?_eq_none (by omega)]
      have hm886 : m886 d el (pre.length + 1) =
          .ok ⟨typejoinT d.et (typeofV el), setU c (pre.length + 1) (some el)⟩ := by
        unfold m886; rw [h2, eb, bind_ok]; unfold m288
        rw [show (pre.length : Int) + 1 - 1 = pre.length by omega, ec, bind_ok]; rfl
      rw [hm886, bind_ok]
      obtain ⟨a', e, h'⟩ := m895_spec rest ⟨typejoinT d.et (typeofV el), setU c (pre.length + 1) (some el)⟩
        (pre ++ [el]) D N (slotInv_set hinv el) (by simp) (by simp; omega)
        (fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact subT_trans _ _ _ (hisa x hx) (subT_join_left _ _)
          · exact subT_join_right _ _)
      refine ⟨a', ?_, by simpa using h'⟩
      simpa [joinTypes, Int.add_assoc, Int.add_comm 1] using e

theorem slotInv_contents {a : Arr JV} {D : List Int} {xs : List JV} (h : SlotInv a D xs.length xs) :
    contents a = xs.map some := by
  obtain ⟨_, _, h3, _, _, h6⟩ := h
  apply contents_ext (by simp [h3])
  intro k hk
  simp only [List.length_map] at hk
  rw [h6 k (by omega)]; simp [List.getElem?_eq_getElem hk]

/-! ### Collecting an iterator of known size -/

/-- A well-formed iterator: its size trait matches its elements, a declared element
type covers them, inference's bound covers them (inference is sound), and a
`Generator` whose function is a type `F` produces values of type `F`. -/
def WFIter (it : Iter) : Prop :=
  (match it.size with
   | .unknown => True
   | .len n => n = it.xs.length
   | .shape dims => (∀ d ∈ dims, 0 ≤ d) ∧ dims.foldr (· * ·) 1 = (it.xs.length : Int)) ∧
  (∀ T, it.eltype = some T → ∀ x ∈ it.xs, isaV x T = true) ∧
  (∀ x ∈ it.xs, subT (typeofV x) it.inferred = true) ∧
  (∀ F, it.fType = some F → ∀ x ∈ it.xs, typeofV x = F) ∧
  it.xs.length < 2 ^ 58

/-- The documented shape: `size(itr)` for `HasShape`, else a vector of the elements. -/
def resultDims (it : Iter) : List Int :=
  match it.size with
  | .shape d => d
  | _ => [(it.xs.length : Int)]

/-- The documented element type when the iterator does not declare one: "based on the
types of the values collected" (their `promote_typejoin`), or, for an empty iterator,
"determined by type inference" (`@default_eltype`). -/
def valuesEltype (it : Iter) : VT :=
  match it.xs with
  | [] => m821 it
  | x :: rest => joinTypes (typeofV x) rest

def Sized (it : Iter) : Prop := match it.size with
  | .unknown => False
  | _ => True

theorem resultDims_ok {it : Iter} (hw : WFIter it) (hs : Sized it) :
    (∀ d ∈ resultDims it, 0 ≤ d) ∧ (resultDims it).foldr (· * ·) 1 = (it.xs.length : Int) := by
  obtain ⟨h1, -, -, -, -⟩ := hw
  rcases it with ⟨xs, sz, e, inf, f⟩
  cases sz with
  | unknown => exact absurd hs (by simp [Sized])
  | len n => simp [resultDims]
  | shape d => exact h1

/-- Both allocators (`_array_for_inner`, `_similar_for` on an array) give a fresh array of
the documented shape. -/
theorem alloc_fresh {it : Iter} (hw : WFIter it) (hs : Sized it) (T : VT) :
    (∃ b, arrayForInner T (m700 it) = .ok ⟨T, b⟩ ∧ Fresh b (resultDims it)) ∧
    (∃ b, similarFor T (m700 it) = .ok ⟨T, b⟩ ∧ Fresh b (resultDims it)) := by
  have hl : it.xs.length < 2 ^ 58 := hw.2.2.2.2
  obtain ⟨h0, hp⟩ := resultDims_ok hw hs
  obtain ⟨b, eb, hb⟩ := newArray_ok (α := JV) h0 (by rw [hp]; unfold typemaxInt; omega)
  obtain ⟨h1, -, -, -, -⟩ := hw
  rcases it with ⟨xs, sz, e, inf, f⟩
  cases sz with
  | unknown => exact absurd hs (by simp [Sized])
  | len n =>
    simp only at h1; subst h1
    simp only at hl
    refine ⟨⟨b, ?_, hb⟩, ⟨b, ?_, hb⟩⟩ <;>
      simp only [m700, arrayForInner, similarFor, m712, m705] <;>
      rw [toInt_ok (by omega) (by omega), bind_ok] <;>
      simp only [resultDims] at eb <;> rw [eb, bind_ok] <;> rfl
  | shape d =>
    simp only [resultDims] at eb hb
    refine ⟨⟨b, ?_, hb⟩, ⟨b, ?_, hb⟩⟩ <;> simp only [m700, arrayForInner, similarFor, m713, m707, eb, bind_ok] <;> rfl

theorem fresh_length {b : Arr α} {D : List Int} (h : Fresh b D) : length b = D.foldr (· * ·) 1 := by
  simp [length, h.1]

/-- `collectSized` with either allocator: the values in order, the element type from
the values, the documented shape. -/
theorem collectSized_spec (alloc : VT → Shp → R TA)
    (halloc : ∀ T, ∃ b, alloc T (m700 it) = .ok ⟨T, b⟩ ∧ Fresh b (resultDims it))
    (hw : WFIter it) (hs : Sized it) (B : VT) (hB : ∀ x ∈ it.xs, subT (typeofV x) B = true)
    (hcon : ∀ v1 rest, it.xs = v1 :: rest → isConcreteT (ptjUnion B) = true → ∀ x ∈ it.xs, typeofV x = ptjUnion B) :
    ∃ d, collectSized alloc (ptjUnion B) it = .ok d ∧
      d.et = (match it.xs with | [] => ptjUnion B | x :: rest => joinTypes (typeofV x) rest) ∧
      d.a.dims = resultDims it ∧ contents d.a = it.xs.map some := by
  obtain ⟨h0, hp⟩ := resultDims_ok hw hs
  have hl : it.xs.length < 2 ^ 58 := hw.2.2.2.2
  unfold collectSized
  cases hx : it.xs with
  | nil =>
    obtain ⟨b, eb, hb⟩ := halloc (ptjUnion B)
    refine ⟨_, eb, rfl, hb.1, ?_⟩
    rw [hb.2.2]; rw [hx] at hp; simp [hp]
  | cons v1 rest =>
    rw [hx] at hp hl
    obtain ⟨b, eb, hb⟩ := halloc (typeofV v1)
    simp only []
    rw [eb, bind_ok]
    have hinv0 := fresh_slotInv hb h0 (by rw [hp]; simp at hl ⊢; omega)
    rw [hp] at hinv0
    have hlen : length b = ((v1 :: rest).length : Int) := by rw [fresh_length hb, hp]
    have e1 : m1031 (convertV (typeofV v1)) b v1 1 = .ok (setU b 1 (some v1)) := by
      unfold m1031; rw [convertV_isa (subT_refl _), bind_ok]; unfold m1036
      rw [if_neg (by simp [inBounds, hlen]; omega)]
    have hinv1 : SlotInv (setU b 1 (some v1)) (resultDims it) ((v1 :: rest).length : Int) [v1] := by
      simpa using slotInv_set hinv0 v1
    obtain ⟨a', e, h'⟩ := m895_spec rest ⟨typeofV v1, setU b 1 (some v1)⟩ [v1] _ _ hinv1 (by simp)
      (by simp; omega) (by simp [isaV, subT_refl])
    have e875 : m875 ⟨typeofV v1, b⟩ v1 rest = .ok ⟨joinTypes (typeofV v1) rest, a'⟩ := by
      unfold m875; rw [e1, bind_ok]; simpa using e
    rw [e875, bind_ok]
    have hF : subT (joinTypes (typeofV v1) rest) (ptjUnion B) = true :=
      joinTypes_bound B rest _ (sub_ptj _ _ (hB v1 (by simp [hx])))
        (fun y hy => hB y (by simp [hx, hy]))
    have hrt : rtCheck (ptjUnion B) ⟨joinTypes (typeofV v1) rest, a'⟩ = .ok ⟨joinTypes (typeofV v1) rest, a'⟩ := by
      unfold rtCheck
      by_cases hc : isConcreteT (ptjUnion B) = true
      · rw [if_pos hc, if_pos (concrete_sub _ _ hc hF)]
      · rw [if_neg hc, if_pos hF]
    refine ⟨_, hrt, rfl, h'.2.1, ?_⟩
    simpa using slotInv_contents h'

/-- The bound `@default_eltype` starts from: the function when it is a type, else
inference's bound. -/
def baseEltype (it : Iter) : VT :=
  match it.fType with
  | some F => F
  | none => it.inferred

theorem m821_eq (it : Iter) : m821 it = ptjUnion (baseEltype it) := rfl

theorem base_bound {it : Iter} (hw : WFIter it) : ∀ x ∈ it.xs, subT (typeofV x) (baseEltype it) = true := by
  obtain ⟨-, -, h3, h4, -⟩ := hw
  intro x hx
  unfold baseEltype
  cases hf : it.fType with
  | none => exact h3 x hx
  | some F => rw [h4 F hf x hx]; exact subT_refl F

theorem base_concrete {it : Iter} (hw : WFIter it) (v1 : JV) (rest : List JV) (hx : it.xs = v1 :: rest)
    (hc : isConcreteT (ptjUnion (baseEltype it)) = true) : ∀ x ∈ it.xs, typeofV x = ptjUnion (baseEltype it) :=
  fun x hx' => concrete_sub _ _ hc (sub_ptj _ _ (base_bound hw x hx'))

/-! ### Growing vectors (`grow_to!`, `push_widen`) -/

theorem refCopy_len {dm sm m : Mem α} {doff soff n : Int} (h : refCopy dm doff sm soff n = .ok m) :
    m.len = dm.len := by
  unfold refCopy at h
  split at h
  · cases h; rfl
  · cases h1 : refIndex dm doff n with
    | error e => rw [h1, bind_error] at h; cases h
    | ok x =>
      rw [h1, bind_ok] at h
      cases h2 : refIndex sm soff n with
      | error e => rw [h2, bind_error] at h; cases h
      | ok y =>
        rw [h2, bind_ok] at h
        split at h
        · cases h
        · rw [pure_ok] at h; cases h; rfl

theorem m299_mem {d s d' : Arr α} {doffs soffs n : Int} (h : m299 d doffs s soffs n = .ok d') :
    d'.off = d.off ∧ d'.mem.len = d.mem.len := by
  unfold m299 at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  cases h1 : toInt doffs with
  | error e => rw [h1, bind_error] at h; cases h
  | ok x =>
    rw [h1, bind_ok] at h
    cases h2 : toInt soffs with
    | error e => rw [h2, bind_error] at h; cases h
    | ok y =>
      rw [h2, bind_ok] at h
      cases h3 : toInt n with
      | error e => rw [h3, bind_error] at h; cases h
      | ok z =>
        rw [h3, bind_ok] at h
        cases h4 : refCopy d.mem (d.off + x - 1) s.mem (s.off + y - 1) z with
        | error e => rw [h4, bind_error] at h; cases h
        | ok m => rw [h4, bind_ok, pure_ok] at h; cases h; exact ⟨rfl, refCopy_len h4⟩

/-- `append!(a, b)` of a vector keeps the growth invariant. -/
theorem m1427_vec (conv : β → R α) {a b : Arr α} {n : Int} (ha : VecOK a n) (hb : Valid b)
    (hl : a.off - 1 + n + length b ≤ 576460752303423488) :
    ∃ a', m1427 conv a (.vec b) = .ok a' ∧ VecOK a' (n + length b) ∧ a'.off ≤ a.off ∧
      contents a' = contents a ++ contents b := by
  obtain ⟨hn, ho, hn0, _, hs, _⟩ := vecOK_unpack ha
  obtain ⟨b1, b2, b3⟩ := hb
  obtain ⟨a1, e1, ha1, ho1, hp⟩ := m1212_vec ha (delta := length b) b2 (by omega)
  obtain ⟨hl1, _, _, _, _, hv1⟩ := vecOK_unpack ha1
  have hval1 := ha1.2.1
  simp only [m1427]; rw [toInt_ok (by omega) (by omega), bind_ok, e1, bind_ok, hl1]
  unfold m288
  obtain ⟨a2, e2, hd2, hv2, hp2⟩ := m299_vec (c := length b) hval1 ⟨b1, b2, b3⟩ (by omega) (by omega)
    (doffs := n + length b - length b + 1) (soffs := 1) b2 (by omega) (by omega) (by omega) (by omega)
  obtain ⟨o2, m2⟩ := m299_mem e2
  refine ⟨a2, e2, ⟨by unfold IsVec; rw [hd2]; exact hv1, hv2, by unfold Small; rw [m2]; exact ha1.2.2⟩,
    by omega, ?_⟩
  apply splice_end _ hn hn0 (by rw [show length a2 = length a1 by simp [length, hd2], hl1]; simp; omega)
  · intro k k1 k2; rw [hp2 k k1 (by omega), if_neg (by omega), hp k k1 k2]
  · intro j hj; simp only [contents_length] at hj
    rw [hp2 _ (by omega) (by omega), if_pos (by omega), getElem_contents]; congr 1; omega

/-- `Vector{T}()`. -/
def emptyVec : Arr α := ⟨Mem.undef 0, 1, [0]⟩

theorem newArray_empty : (newArray [0] : R (Arr α)) = .ok emptyVec := by
  unfold newArray; rw [if_pos (by simp [typemaxInt])]; rfl

theorem emptyVec_ok : VecOK (emptyVec : Arr α) 0 ∧ (emptyVec : Arr α).off = 1 ∧ contents (emptyVec : Arr α) = [] :=
  ⟨⟨rfl, by simp [Valid, emptyVec, length], by simp [Small, emptyVec]⟩, rfl, by simp [contents, emptyVec, length]⟩

/-- `sizehint!` with the default `shrink = true` on an empty fresh vector grows it as
`shrink = false` would. -/
theorem m1617_emptyVec (sz : Int) (h0 : 0 ≤ sz) (h1 : sz ≤ 2 ^ 58) :
    ∃ a', m1617 (emptyVec : Arr α) sz false true = .ok a' ∧ VecOK a' 0 ∧ a'.off ≤ 1 ∧ contents a' = [] := by
  have he : m1617 (emptyVec : Arr α) sz false true = m1617 emptyVec sz false false := by
    unfold m1617
    rw [toInt_ok (by omega) (by omega), bind_ok, bind_ok]
    simp only [emptyVec, length, List.foldr, Mem.undef_len]
    by_cases hz : max sz (0 * 1) ≤ 0
    · have h8 : Int.tdiv 0 8 = 0 := by decide
      rw [if_pos hz, if_pos hz, if_pos (Or.inr (by rw [h8]; omega)), if_pos (Or.inl (by simp))]
    · rw [if_neg hz, if_neg hz]
  obtain ⟨hv, ho, hc⟩ := emptyVec_ok (α := α)
  obtain ⟨a', e, h1', h2', h3'⟩ := m1617_end hv h0 (by rw [ho]; omega)
  exact ⟨a', he ▸ e, h1', by omega, by rw [h3', hc]⟩

theorem m922_spec {d : TA} {pre : List JV} (el : JV) (ha : VecOK d.a pre.length) (hc : contents d.a = pre.map some)
    (hl : pre.length + 1 ≤ 2 ^ 58) :
    ∃ a', m922 d el = .ok ⟨typejoinT d.et (typeofV el), a'⟩ ∧ VecOK a' (pre.length + 1) ∧ a'.off ≤ 1 ∧
      contents a' = (pre ++ [el]).map some := by
  obtain ⟨hn, _, hn0, _, _, _⟩ := vecOK_unpack ha
  obtain ⟨b1, e1, hv1, ho1, hc1⟩ := m1617_emptyVec (α := JV) (length d.a) (by omega) (by omega)
  obtain ⟨b2, e2, hv2, ho2, hc2⟩ := m1427_vec (convertV (typejoinT d.et (typeofV el))) hv1 ha.2.1
    (b := d.a) (by omega)
  obtain ⟨b3, e3, hv3, ho3, hc3⟩ := m1366_vec hv2 (by omega) el
  refine ⟨b3, ?_, by simpa [hn] using hv3, by omega, by rw [hc3, hc2, hc1, hc]; simp⟩
  unfold m922
  simp only []
  rw [newArray_empty, bind_ok, e1, bind_ok, e2, bind_ok]
  unfold m1358; rw [convertV_isa (subT_join_right _ _), bind_ok, e3, bind_ok]; rfl

theorem m935_spec : ∀ (rest : List JV) (d : TA) (pre : List JV), VecOK d.a pre.length → d.a.off ≤ 1 →
    contents d.a = pre.map some → (∀ x ∈ pre, isaV x d.et = true) → pre.length + rest.length ≤ 2 ^ 58 →
    ∃ r, m935 d rest = .ok r ∧ r.et = joinTypes d.et rest ∧ VecOK r.a (pre ++ rest).length ∧ r.a.off ≤ 1 ∧
      contents r.a = (pre ++ rest).map some
  | [], d, pre, ha, ho, hc, _, _ => ⟨d, rfl, rfl, by simpa using ha, ho, by simpa using hc⟩
  | el :: rest, d, pre, ha, ho, hc, hisa, hl => by
    simp only [List.length_cons] at hl
    unfold m935
    by_cases hel : isaV el d.et = true
    · rw [if_pos hel]
      obtain ⟨a1, e, ha1, ho1, hc1⟩ := m1366_vec ha (by omega) el
      have e1 : m1358 (convertV d.et) d.a el = .ok a1 := by unfold m1358; rw [convertV_isa hel, bind_ok, e]
      rw [e1, bind_ok]
      obtain ⟨r, er, h1, h2, h3, h4⟩ := m935_spec rest ⟨d.et, a1⟩ (pre ++ [el]) (by simpa using ha1) (by simp; omega)
        (by simp only []; rw [hc1, hc]; simp)
        (fun x hx => by simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact hisa x hx; exact hel)
        (by simp; omega)
      refine ⟨r, er, by rw [h1]; simp [joinTypes, join_of_sub _ _ hel], by simpa using h2, h3, by simpa using h4⟩
    · rw [if_neg hel]
      obtain ⟨a1, e, ha1, ho1, hc1⟩ := m922_spec el ha hc (by omega)
      rw [e, bind_ok]
      obtain ⟨r, er, h1, h2, h3, h4⟩ := m935_spec rest ⟨typejoinT d.et (typeofV el), a1⟩ (pre ++ [el])
        (by simpa using ha1) ho1 hc1
        (fun x hx => by
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact subT_trans _ _ _ (hisa x hx) (subT_join_left _ _)
          · exact subT_join_right _ _)
        (by simp; omega)
      exact ⟨r, er, by rw [h1]; rfl, by simpa using h2, h3, by simpa using h4⟩

theorem m914_spec (d : TA) (xs : List JV) (hl : xs.length ≤ 2 ^ 58) :
    ∃ r, m914 d xs = .ok r ∧ (∀ x rest, xs = x :: rest → r.et = joinTypes (typeofV x) rest) ∧
      (xs = [] → r = d) ∧ (xs ≠ [] → IsVec r.a xs.length ∧ contents r.a = xs.map some) := by
  cases xs with
  | nil => exact ⟨d, rfl, fun _ _ h => absurd h (by simp), fun _ => rfl, fun h => absurd rfl h⟩
  | cons y rest =>
    obtain ⟨hv, ho, hc⟩ := emptyVec_ok (α := JV)
    obtain ⟨a1, e, ha1, ho1, hc1⟩ := m1366_vec hv (by rw [ho]; omega) y
    obtain ⟨r, er, h1, h2, h3, h4⟩ := m935_spec rest ⟨typeofV y, a1⟩ [y] (by simpa using ha1) (show a1.off ≤ 1 by omega)
      (by simp only []; rw [hc1, hc]; simp) (by simp [isaV, subT_refl]) (by simp at hl ⊢; omega)
    refine ⟨r, ?_, fun x r' h => by simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact h1,
      fun h => absurd h (by simp), fun _ => ⟨by simpa using h2.1, by simpa using h4⟩⟩
    simp only [m914, newArray_empty, bind_ok]
    unfold m1358; rw [convertV_isa (subT_refl _), bind_ok, e, bind_ok]; exact er

/-! ### `copyto!` from an iterator -/

theorem copytoIter_eq (conv : β → R α) : ∀ (xs : List β) (a : Arr α) (i : Int), 1 ≤ i →
    i - 1 + xs.length ≤ length a → copytoIter conv a i xs = convWrites (m1031 conv) a i xs
  | [], _, _, _, _ => rfl
  | x :: xs, a, i, h1, h2 => by
    simp only [List.length_cons] at h2
    simp only [copytoIter, convWrites]
    rw [if_neg (by omega)]
    cases e : m1031 conv a x i with
    | error e' => rfl
    | ok a' =>
      simp only [bind_ok]
      have hl : length a' = length a := by
        unfold m1031 at e
        cases hc : conv x with
        | error _ => rw [hc, bind_error] at e; cases e
        | ok y =>
          rw [hc, bind_ok] at e; unfold m1036 at e
          split at e
          · cases e
          · cases e; simp
      exact copytoIter_eq conv xs a' (i + 1) (by omega) (by omega)

/-- `copyto!(dest, itr)` into a fresh array of exactly the iterator's length: the
converted elements, or the first conversion error. -/
theorem copytoIter_fresh (conv : β → R α) {b : Arr α} {D : List Int} (hf : Fresh b D) (xs : List β)
    (hlen : D.foldr (· * ·) 1 = (xs.length : Int)) :
    (∀ e, convList conv xs = .error e → copytoIter conv b 1 xs = .error e) ∧
    (∀ ys, convList conv xs = .ok ys → ∃ a, copytoIter conv b 1 xs = .ok a ∧ a.dims = D ∧
      contents a = ys.map some) := by
  have hl : length b = xs.length := by rw [fresh_length hf, hlen]
  rw [copytoIter_eq conv xs b 1 (Int.le_refl 1) (by omega)]
  have hw := convWrites_spec conv (m1031 conv) (hw1031 conv) xs b 1 (Int.le_refl 1) (by omega)
  refine ⟨hw.1, fun ys hys => ⟨_, hw.2 ys hys, by rw [(safeWrites_spec ys b 1).1, hf.1], ?_⟩⟩
  exact contents_safeWrites_full (by rw [hl, convList_length conv xs ys hys])

/-! ### `collect(T, itr)` -/

/-- `collect(element_type, collection)` (docstring base/array.jl:669-683): an `Array` with
element type `T` of the items converted to `T` in iteration order, with the shape of a
`HasShape` collection and as a vector otherwise; a failing conversion throws. -/
def P684 : Prop := ∀ (T : VT) (it : Iter), WFIter it →
    (∀ ys, convList (convertV T) it.xs = .ok ys →
      ∃ d, m684 T it = .ok d ∧ d.et = T ∧ d.a.dims = resultDims it ∧ contents d.a = ys.map some) ∧
    (∀ e, convList (convertV T) it.xs = .error e → m684 T it = .error e)

theorem p684 : P684 := by
  intro T it hw
  have hl : it.xs.length < 2 ^ 58 := hw.2.2.2.2
  cases hsz : it.size with
  | unknown =>
    have e0 : m684 T it = m688 T it := by simp [m684, hsz]
    obtain ⟨hv, ho, hc⟩ := emptyVec_ok (α := JV)
    have hp := pushEach_spec (convertV T) it.xs emptyVec 0 hv (by rw [ho]; omega)
    refine ⟨fun ys hys => ?_, fun e he => ?_⟩
    · obtain ⟨a, ea, ha, _, hca⟩ := hp.2 ys hys
      refine ⟨⟨T, a⟩, by rw [e0]; simp [m688, newArray_empty, ea], rfl, ?_, by rw [hca, hc]; simp⟩
      simp only [resultDims, hsz]; rw [ha.1]; simp
    · rw [e0]; simp [m688, newArray_empty, hp.1 e he]
  | len n =>
    have hs : Sized it := by simp [Sized, hsz]
    have e0 : m684 T it = m686 T it := by simp [m684, hsz]
    obtain ⟨b, eb, hb⟩ := (alloc_fresh hw hs T).1
    have hc := copytoIter_fresh (convertV T) hb it.xs (resultDims_ok hw hs).2
    refine ⟨fun ys hys => ?_, fun e he => ?_⟩
    · obtain ⟨a, ea, hd, hca⟩ := hc.2 ys hys
      exact ⟨⟨T, a⟩, by rw [e0]; simp [m686, eb, ea], rfl, hd, hca⟩
    · rw [e0]; simp [m686, eb, hc.1 e he]
  | shape dims =>
    have hs : Sized it := by simp [Sized, hsz]
    have e0 : m684 T it = m686 T it := by simp [m684, hsz]
    obtain ⟨b, eb, hb⟩ := (alloc_fresh hw hs T).1
    have hc := copytoIter_fresh (convertV T) hb it.xs (resultDims_ok hw hs).2
    refine ⟨fun ys hys => ?_, fun e he => ?_⟩
    · obtain ⟨a, ea, hd, hca⟩ := hc.2 ys hys
      exact ⟨⟨T, a⟩, by rw [e0]; simp [m686, eb, ea], rfl, hd, hca⟩
    · rw [e0]; simp [m686, eb, hc.1 e he]

/-- The allocators: `_array_for(T, itr, isz)`, `_array_for_inner` and `_similar_for` on an
array give a fresh array of element type `T` and the iterator's documented shape;
`_similar_for(c, T, …) = similar(c, T)` gives one of `c`'s size. -/
def P716 : Prop :=
  (∀ (T : VT) (it : Iter), WFIter it → Sized it →
    (∃ b, m716 T it = .ok ⟨T, b⟩ ∧ Fresh b (resultDims it)) ∧
    (∃ b, similarFor T (m700 it) = .ok ⟨T, b⟩ ∧ Fresh b (resultDims it))) ∧
  (∀ (T : VT), (∃ b, m711 T = .ok ⟨T, b⟩ ∧ Fresh b [0]) ∧ (∃ b, m703 T = .ok ⟨T, b⟩ ∧ Fresh b [0])) ∧
  (∀ (T : VT) (cdims : List Int), (∀ d ∈ cdims, 0 ≤ d) → cdims.foldr (· * ·) 1 ≤ typemaxInt →
    ∃ b, m697 T cdims = .ok ⟨T, b⟩ ∧ Fresh b cdims)

theorem p716 : P716 := by
  refine ⟨fun T it hw hs => alloc_fresh hw hs T, fun T => ?_, fun T cdims h0 h1 => ?_⟩
  · have hf : Fresh (emptyVec : Arr JV) [0] := ⟨rfl, emptyVec_ok.1.2.1, by simp [emptyVec_ok.2.2]⟩
    exact ⟨⟨emptyVec, by simp [m711, newArray_empty], hf⟩, ⟨emptyVec, by simp [m703, newArray_empty], hf⟩⟩
  · obtain ⟨b, eb, hb⟩ := newArray_ok (α := JV) h0 h1
    exact ⟨b, by simp [m697, eb], hb⟩

/-! ### `collect(itr)` and `collect(itr::Generator)` -/

/-- `collect(itr)` (docstring base/array.jl:719-770; also `collect_similar` with an array
container): the items in iteration order, shaped like a `HasShape` iterator and as a
vector otherwise; with a declared element type `T` the result has element type `T`;
otherwise the element type is "based on the types of the values collected" (their
`promote_typejoin`), and for an empty iterator "determined by type inference". -/
def P771 : Prop := ∀ it : Iter, WFIter it →
    (∀ T, it.eltype = some T →
      ∃ d, m771 it = .ok d ∧ d.et = T ∧ d.a.dims = resultDims it ∧ contents d.a = it.xs.map some) ∧
    (it.eltype = none →
      ∃ d, m771 it = .ok d ∧ d.et = valuesEltype it ∧ d.a.dims = resultDims it ∧ contents d.a = it.xs.map some)

/-- The `EltypeUnknown` paths (`_collect` at base/array.jl:855/858 and `collect(::Generator)`). -/
theorem unknown_spec (it : Iter) (hw : WFIter it) :
    (∃ d, m855 it = .ok d ∧ d.et = valuesEltype it ∧ d.a.dims = [(it.xs.length : Int)] ∧
      contents d.a = it.xs.map some) ∧
    (Sized it → ∃ d, m858 it = .ok d ∧ d.et = valuesEltype it ∧ d.a.dims = resultDims it ∧
      contents d.a = it.xs.map some) ∧
    (∃ d, m833 it = .ok d ∧ d.et = valuesEltype it ∧ d.a.dims = resultDims it ∧
      contents d.a = it.xs.map some) := by
  have hl : it.xs.length < 2 ^ 58 := hw.2.2.2.2
  have hgrow : ∃ d, m914 ⟨m821 it, emptyVec⟩ it.xs = .ok d ∧ d.et = valuesEltype it ∧
      d.a.dims = [(it.xs.length : Int)] ∧ contents d.a = it.xs.map some := by
    obtain ⟨r, er, h1, h2, h3⟩ := m914_spec ⟨m821 it, emptyVec⟩ it.xs (by omega)
    refine ⟨r, er, ?_, ?_, ?_⟩
    · unfold valuesEltype
      cases hx : it.xs with
      | nil => rw [h2 hx]
      | cons x rest => exact h1 x rest hx
    · by_cases hx : it.xs = []
      · rw [h2 hx, hx]; rfl
      · exact (h3 hx).1
    · by_cases hx : it.xs = []
      · rw [h2 hx, hx]; simp [emptyVec_ok.2.2]
      · exact (h3 hx).2
  have hsized : ∀ alloc : VT → Shp → R TA, Sized it →
      (∀ T, ∃ b, alloc T (m700 it) = .ok ⟨T, b⟩ ∧ Fresh b (resultDims it)) →
      ∃ d, collectSized alloc (m821 it) it = .ok d ∧ d.et = valuesEltype it ∧ d.a.dims = resultDims it ∧
        contents d.a = it.xs.map some := by
    intro alloc hs halloc
    obtain ⟨d, e, h1, h2, h3⟩ := collectSized_spec alloc halloc hw hs (baseEltype it) (base_bound hw)
      (fun v1 rest hx hc => base_concrete hw v1 rest hx hc)
    refine ⟨d, by rw [m821_eq]; exact e, ?_, h2, h3⟩
    rw [h1]; unfold valuesEltype; cases it.xs <;> rfl
  refine ⟨?_, fun hs => hsized similarFor hs (fun T => (alloc_fresh hw hs T).2), ?_⟩
  · simpa [m855, similarFor, m703, newArray_empty] using hgrow
  · cases hsz : it.size with
    | unknown =>
      obtain ⟨d, e, h1, h2, h3⟩ := hgrow
      refine ⟨d, by simp [m833, hsz, newArray_empty, e], h1, by simp [resultDims, hsz, h2], h3⟩
    | len n =>
      have hs : Sized it := by simp [Sized, hsz]
      obtain ⟨d, e, h⟩ := hsized arrayForInner hs (fun T => (alloc_fresh hw hs T).1)
      exact ⟨d, by simp only [m833, hsz]; exact e, h⟩
    | shape dims =>
      have hs : Sized it := by simp [Sized, hsz]
      obtain ⟨d, e, h⟩ := hsized arrayForInner hs (fun T => (alloc_fresh hw hs T).1)
      exact ⟨d, by simp only [m833, hsz]; exact e, h⟩

theorem p771 : P771 := by
  intro it hw
  have hl : it.xs.length < 2 ^ 58 := hw.2.2.2.2
  refine ⟨fun T hT => ?_, fun hT => ?_⟩
  · have hys := convList_isa it.xs (hw.2.1 T hT)
    cases hsz : it.size with
    | unknown =>
      obtain ⟨hv, ho, hc⟩ := emptyVec_ok (α := JV)
      obtain ⟨a, ea, ha, _, hca⟩ := (pushEach_spec (convertV T) it.xs emptyVec 0 hv (by rw [ho]; omega)).2 _ hys
      refine ⟨⟨T, a⟩, by simp [m771, hT, hsz, m780, similarFor, m703, newArray_empty, ea], rfl, ?_,
        by rw [hca, hc]; simp⟩
      simp only [resultDims, hsz]; rw [ha.1]; simp
    | len n =>
      have hs : Sized it := by simp [Sized, hsz]
      obtain ⟨b, eb, hb⟩ := (alloc_fresh hw hs T).2
      obtain ⟨a, ea, hd, hca⟩ := (copytoIter_fresh (convertV T) hb it.xs (resultDims_ok hw hs).2).2 _ hys
      exact ⟨⟨T, a⟩, by simp only [m771, hT, hsz]; simp only [m777, eb, bind_ok, ea, pure_ok], rfl, hd, hca⟩
    | shape dims =>
      have hs : Sized it := by simp [Sized, hsz]
      obtain ⟨b, eb, hb⟩ := (alloc_fresh hw hs T).2
      obtain ⟨a, ea, hd, hca⟩ := (copytoIter_fresh (convertV T) hb it.xs (resultDims_ok hw hs).2).2 _ hys
      exact ⟨⟨T, a⟩, by simp only [m771, hT, hsz]; simp only [m777, eb, bind_ok, ea, pure_ok], rfl, hd, hca⟩
  · obtain ⟨u1, u2, _⟩ := unknown_spec it hw
    cases hsz : it.size with
    | unknown =>
      obtain ⟨d, e, h1, h2, h3⟩ := u1
      exact ⟨d, by simp [m771, hT, hsz, e], h1, by simp [resultDims, hsz, h2], h3⟩
    | len n =>
      obtain ⟨d, e, h⟩ := u2 (by simp [Sized, hsz])
      exact ⟨d, by simp [m771, hT, hsz, e], h⟩
    | shape dims =>
      obtain ⟨d, e, h⟩ := u2 (by simp [Sized, hsz])
      exact ⟨d, by simp [m771, hT, hsz, e], h⟩

/-- `collect(itr::Generator)` and comprehensions (docstring base/array.jl:727-770): the
generated values in order, shaped like the underlying iterator, with the element type
from the values (from the function when it is a type, or inference, when empty). -/
def P833 : Prop := ∀ it : Iter, WFIter it →
    ∃ d, m833 it = .ok d ∧ d.et = valuesEltype it ∧ d.a.dims = resultDims it ∧ contents d.a = it.xs.map some

theorem p833 : P833 := fun it hw => (unknown_spec it hw).2.2

/-- `collect_to_with_first!(dest, v1, itr, st)` for a vector-like destination of element
type `typeof(v1)` pushes `v1` and grows with the rest: all values in order, the element
type from the values. -/
def P881 : Prop := ∀ (v1 : JV) (rest : List JV), rest.length + 1 ≤ 2 ^ 58 →
    ∃ r, m881 ⟨typeofV v1, emptyVec⟩ v1 rest = .ok r ∧ r.et = joinTypes (typeofV v1) rest ∧
      contents r.a = (v1 :: rest).map some

theorem p881 : P881 := by
  intro v1 rest hl
  obtain ⟨hv, ho, hc⟩ := emptyVec_ok (α := JV)
  obtain ⟨a1, e, ha1, ho1, hc1⟩ := m1366_vec hv (by rw [ho]; omega) v1
  obtain ⟨r, er, h1, _, _, h4⟩ := m935_spec rest ⟨typeofV v1, a1⟩ [v1] (by simpa using ha1)
    (show a1.off ≤ 1 by omega) (by simp only []; rw [hc1, hc]; simp) (by simp [isaV, subT_refl]) (by simp; omega)
  refine ⟨r, ?_, h1, by simpa using h4⟩
  unfold m881 m1358; rw [convertV_isa (subT_refl _), bind_ok, e, bind_ok]; exact er

/-- `_iterator_upper_bound` is "not meant to be called, only inferred" (comment
base/array.jl:803-804): a call never returns a value. -/
def P805 : Prop := ∀ it : Iter, m805 it = .error .thrownNothing

theorem p805 : P805 := fun _ => rfl

/-! ### `collect(A::AbstractArray)` -/

/-- Reading a source slot: `UndefRefError` for `#undef`, else the conversion. -/
def readConv (et : VT) : Option JV → R JV
  | none => .error .undefRef
  | some x => convertV et x

theorem hwRead (et : VT) : ∀ (a : Arr JV) (x : Option JV) (j : Int), 1 ≤ j → j ≤ length a →
    readWrite (convertV et) a x j = (readConv et x >>= fun y => .ok (setU a j (some y))) := by
  intro a x j h1 h2
  cases x with
  | none => rfl
  | some x => exact hw1031 (convertV et) a x j h1 h2

theorem convList_read (et : VT) : ∀ (l : List (Option JV)), (∀ x, some x ∈ l → isaV x et = true) →
    (∀ xs : List JV, l = xs.map some → convList (readConv et) l = .ok xs) ∧
      (none ∈ l → convList (readConv et) l = .error .undefRef)
  | [], _ => ⟨fun xs h => by cases xs with | nil => rfl | cons _ _ => simp at h, fun h => by cases h⟩
  | o :: l, hisa => by
    obtain ⟨ih1, ih2⟩ := convList_read et l (fun x hx => hisa x (by simp [hx]))
    refine ⟨fun xs h => ?_, fun h => ?_⟩
    · cases xs with
      | nil => simp at h
      | cons x xs =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [convList, readConv, convertV_isa (hisa x (by simp)), bind_ok, ih1 xs rfl, pure_ok]
    · cases o with
      | none => simp [convList, readConv]
      | some x =>
        simp only [List.mem_cons, reduceCtorEq, false_or] at h
        simp only [convList, readConv, convertV_isa (hisa x (by simp)), bind_ok, ih2 h, bind_error]

theorem foldr_mul_nonneg : ∀ (l : List Int), (∀ d ∈ l, 0 ≤ d) → 0 ≤ l.foldr (· * ·) 1
  | [], _ => by simp
  | d :: l, h => by
    simp only [List.foldr_cons]
    exact Int.mul_nonneg (h d (by simp)) (foldr_mul_nonneg l (fun x hx => h x (by simp [hx])))

/-- `collect(A::AbstractArray)` (docstring base/array.jl:719-725): an `Array{eltype(A)}` with
`A`'s size (and 1-based axes) holding `A`'s elements in the same order; an `#undef`
element throws `UndefRefError`. -/
def P773 : Prop := ∀ A : SrcA, A.src.elems.length = (A.src.size.foldr (· * ·) 1).toNat →
    A.src.size.foldr (· * ·) 1 ≤ typemaxInt → (∀ x, some x ∈ A.src.elems → isaV x A.et = true) →
    (∀ xs : List JV, A.src.elems = xs.map some →
      ∃ d, m773 A = .ok d ∧ d.et = A.et ∧ d.a.dims = A.src.size ∧ contents d.a = xs.map some) ∧
    (none ∈ A.src.elems → m773 A = .error .undefRef)

theorem p773 : P773 := by
  intro A hlen hmax hisa
  have h0 : ∀ d ∈ A.src.size, 0 ≤ d := by
    intro d hd; simp only [SrcArr.size, List.mem_map] at hd; obtain ⟨ax, _, rfl⟩ := hd; omega
  obtain ⟨b, eb, hb⟩ := newArray_ok (α := JV) h0 hmax
  have hp0 : 0 ≤ A.src.size.foldr (· * ·) 1 := foldr_mul_nonneg _ h0
  have hbl : length b = A.src.elems.length := by rw [fresh_length hb]; omega
  have hw := convWrites_spec (readConv A.et) (readWrite (convertV A.et)) (hwRead A.et) A.src.elems b 1
    (Int.le_refl 1) (by omega)
  obtain ⟨c1, c2⟩ := convList_read A.et A.src.elems hisa
  have hcopy : (∀ xs : List JV, A.src.elems = xs.map some → ∃ a, copyAll A.et b A.src = .ok a ∧ a.dims = A.src.size ∧
      contents a = xs.map some) ∧ (none ∈ A.src.elems → copyAll A.et b A.src = .error .undefRef) := by
    refine ⟨fun xs hxs => ⟨_, hw.2 xs (c1 xs hxs), by rw [(safeWrites_spec xs b 1).1, hb.1], ?_⟩,
      fun hn => hw.1 _ (c2 hn)⟩
    exact contents_safeWrites_full (by rw [hbl, hxs]; simp)
  have hempty : ∀ xs : List JV, A.src.elems = xs.map some → A.src.elems = [] →
      ∃ d, (pure ⟨A.et, b⟩ : R TA) = .ok d ∧ d.et = A.et ∧ d.a.dims = A.src.size ∧ contents d.a = xs.map some := by
    intro xs hxs he
    rw [he] at hxs
    have : xs = [] := by
      cases xs with
      | nil => rfl
      | cons _ _ => simp at hxs
    subst this
    refine ⟨_, rfl, rfl, hb.1, ?_⟩
    rw [hb.2.2]; rw [he] at hlen; simp at hlen; simp; omega
  have hsz : A.src.axs = [] → A.src.size = [] := by intro h; simp [SrcArr.size, h]
  unfold m773
  split
  · rename_i hax
    have eb' : (newArray [] : R (Arr JV)) = .ok b := by rw [← hsz hax]; exact eb
    unfold m788; rw [eb', bind_ok]
    refine ⟨fun xs hxs => ?_, fun hn => ?_⟩
    · split
      · exact hempty xs hxs (by assumption)
      · obtain ⟨a, ea, h1, h2⟩ := hcopy.1 xs hxs; exact ⟨_, by rw [ea, bind_ok]; rfl, rfl, h1, h2⟩
    · rw [if_neg (by intro h; rw [h] at hn; simp at hn), hcopy.2 hn, bind_error]
  · split
    · unfold m793; rw [eb, bind_ok]
      refine ⟨fun xs hxs => ?_, fun hn => ?_⟩
      · split
        · exact hempty xs hxs (by assumption)
        · obtain ⟨a, ea, h1, h2⟩ := hcopy.1 xs hxs; exact ⟨_, by rw [ea, bind_ok]; rfl, rfl, h1, h2⟩
      · rw [if_neg (by intro h; rw [h] at hn; simp at hn), hcopy.2 hn, bind_error]
    · unfold m798; rw [eb, bind_ok]
      refine ⟨fun xs hxs => ?_, fun hn => ?_⟩
      · obtain ⟨a, ea, h1, h2⟩ := hcopy.1 xs hxs; exact ⟨_, by rw [ea, bind_ok]; rfl, rfl, h1, h2⟩
      · rw [hcopy.2 hn, bind_error]

end JuliaLean.MultidimCov.ArrayV2
