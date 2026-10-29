import JuliaLean.Reduce.ProofsGeneric
import JuliaLean.Reduce.ProofsSumDims

namespace JuliaLean.Reduce

open SumDimsProof

private def Good (v : Val) (s : Int) : Prop :=
  ∃ x : JInt .i64, v = .int .i64 x ∧ wrapInt .i64 x.val = wrapInt .i64 s

private theorem goodElem {v : Val} (h : ∃ x, v = .int .i64 x) : Good v v.intVal := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, rfl, rfl⟩

private theorem goodAdd {a b : Val} {x y : Int} (ha : Good a x) (hb : Good b y) :
    Good (Val.addSum a b) (x + y) := by
  obtain ⟨a, rfl, ha⟩ := ha
  obtain ⟨b, rfl, hb⟩ := hb
  rw [addSum_int .i64 .i64 rfl (Or.inl rfl) (Or.inl rfl)]
  refine ⟨_, rfl, ?_⟩
  change wrapInt .i64 (wrapInt .i64 (a.val + b.val)) = wrapInt .i64 (x + y)
  rw [wrapInt_wrapInt]
  exact wrapInt_add_congr .i64 ha hb

private theorem goodFold (xs : List Val) (hx : ∀ x ∈ xs, ∃ y, x = .int .i64 y) :
    ∀ a s, Good a s → Good (xs.foldl Val.addSum a) (s + (xs.map Val.intVal).sum) := by
  induction xs with
  | nil => intro a s h; simpa using h
  | cons x xs ih =>
    intro a s h
    have h' := ih (fun y hy => hx y (by simp [hy])) _ _
      (goodAdd h (goodElem (hx x (by simp))))
    simpa [List.foldl_cons, List.map_cons, List.sum_cons, Int.add_assoc] using h'

private theorem goodMr : ∀ (n : Nat) (a : Val) (rest : List Val),
    rest.length < n → (∀ x ∈ a :: rest, ∃ y, x = .int .i64 y) →
    Good (mrImpl id Val.addSum Val.firstAddSum 1024 a rest)
      ((a :: rest).map Val.intVal).sum := by
  intro n
  induction n with
  | zero => intro a rest h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro a rest hlen hall
    have ha := hall a (by simp)
    cases rest with
    | nil =>
      obtain ⟨x, rfl⟩ := ha
      rw [mrImpl]
      simpa [Val.firstAddSum, Val.smallSigned, Val.smallUnsigned] using
        (goodElem (v := .int .i64 x) ⟨x, rfl⟩)
    | cons b rest =>
      have hb := hall b (by simp)
      rw [mrImpl]
      split
      · have h := goodFold rest (fun x hx => hall x (by simp [hx])) _ _
          (goodAdd (goodElem ha) (goodElem hb))
        simpa [List.map_cons, List.sum_cons, Int.add_assoc] using h
      · split
        · rename_i h
          have h' := congrArg List.length h
          simp only [List.length_drop, List.length_cons, List.length_nil] at h'
          omega
        · rename_i c rest2 h
          have hsum : ((a :: b :: rest).map Val.intVal).sum =
              ((a :: (b :: rest).take ((rest.length + 1) / 2)).map Val.intVal).sum +
                ((c :: rest2).map Val.intVal).sum := by
            have e : ((b :: rest).map Val.intVal).sum =
                (((b :: rest).take ((rest.length + 1) / 2)).map Val.intVal).sum +
                  (((b :: rest).drop ((rest.length + 1) / 2)).map Val.intVal).sum := by
              rw [← List.sum_append, ← List.map_append, List.take_append_drop]
            rw [← h]
            simp only [List.map_cons, List.sum_cons] at e ⊢
            omega
          rw [hsum]
          have hlen2 := congrArg List.length h
          simp only [List.length_drop, List.length_cons] at hlen2 hlen
          refine goodAdd (ih _ _ ?_ ?_) (ih _ _ ?_ ?_)
          · simp only [List.length_take, List.length_cons]; omega
          · intro x hx
            rcases List.mem_cons.1 hx with hx | hx
            · exact hall x (by simp [hx])
            · exact hall x (List.mem_cons_of_mem _ (List.mem_of_mem_take hx))
          · omega
          · intro x hx
            rw [← h] at hx
            exact hall x (List.mem_cons_of_mem _ (List.mem_of_mem_drop hx))

private theorem goodEq {a b : Val} {s : Int} (ha : Good a s) (hb : Good b s) : a = b := by
  obtain ⟨a, rfl, ha⟩ := ha
  obtain ⟨b, rfl, hb⟩ := hb
  congr 1
  apply Subtype.ext
  have h : wrapInt .i64 a.val = wrapInt .i64 b.val := ha.trans hb.symm
  rwa [wrapInt_of_inRange .i64 a.val a.property,
    wrapInt_of_inRange .i64 b.val b.property] at h

theorem flattenSumAgrees_proven : FlattenSumAgrees := by
  intro vs hv
  have hv' : ∀ x ∈ vs.flatten, ∃ y, x = .int .i64 y := by
    intro x hx
    obtain ⟨v, hvm, hxm⟩ := List.mem_flatten.mp hx
    exact hv v hvm x hxm
  cases h : vs.flatten with
  | nil =>
    rw [flattenEmptySum_proven vs h]
    rfl
  | cons a rest =>
    have ha := hv' a (by rw [h]; simp)
    have hr : ∀ x ∈ rest, ∃ y, x = .int .i64 y := by
      intro x hx
      exact hv' x (by rw [h]; simp [hx])
    have hf : Vec.foldlFlatten Val.addSum Val.firstAddSum Vec.emptyAddSum
        (.vector (.int .i64)) vs = .ok (rest.foldl Val.addSum (Val.firstAddSum a)) := by
      unfold Vec.foldlFlatten
      dsimp only
      rw [foldl_nested, h]
      simp only [List.foldl_cons]
      rw [foldl_optStep Val.addSum _ (by intro _ _; rfl)]
    rw [hf]
    unfold Vec.sum
    cases rest with
    | nil => rfl
    | cons b rest =>
      simp only [mapreduceArr]
      have hg := goodFold (b :: rest) hr _ _ (goodElem ha)
      have hfirst : Val.firstAddSum a = a := by
        obtain ⟨x, rfl⟩ := ha
        rfl
      rw [hfirst]
      split
      · rfl
      · congr 1
        apply goodEq hg
        simpa [List.map_cons, List.sum_cons, Int.add_assoc] using
          (goodMr (rest.length + 2) a (b :: rest) (by simp) (by simpa [h] using hv'))

example : Vec.foldlFlatten Val.addSum Val.firstAddSum Vec.emptyAddSum
    (.vector (.int .u8)) [[]] = .ok (.int .u64 (JInt.lit .u64 0)) := by decide

example : Vec.foldlFlatten Val.addSum Val.firstAddSum Vec.emptyAddSum
    (.vector (.int .i64)) [[Val.i64 IntTy.i64.max, Val.i64 1]] =
      .ok (Val.i64 IntTy.i64.min) := by decide

end JuliaLean.Reduce
