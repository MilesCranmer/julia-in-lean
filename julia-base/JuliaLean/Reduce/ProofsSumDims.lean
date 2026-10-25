import JuliaLean.Reduce.Props

/-!
Proof of `SumDimsExact`: `sum(A; dims = d)` of a `BitInteger` matrix holds the wrapped
exact slice sums in the reduced shape, on every code path of `mapreducedim`.
-/

namespace JuliaLean.Reduce

namespace SumDimsProof

/-! ### Wrapping arithmetic -/

theorem wrapInt_wrapInt_add (s : IntTy) (a b : Int) :
    wrapInt s (wrapInt s a + b) = wrapInt s (a + b) := by
  cases s <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_add_wrapInt (s : IntTy) (a b : Int) :
    wrapInt s (a + wrapInt s b) = wrapInt s (a + b) := by
  cases s <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_wrapInt (s : IntTy) (a : Int) : wrapInt s (wrapInt s a) = wrapInt s a := by
  have := wrapInt_wrapInt_add s a 0
  simpa using this

theorem wrapInt_add_congr (s : IntTy) {a a' b b' : Int} (ha : wrapInt s a = wrapInt s a')
    (hb : wrapInt s b = wrapInt s b') : wrapInt s (a + b) = wrapInt s (a' + b') := by
  rw [← wrapInt_wrapInt_add, ha, wrapInt_wrapInt_add, ← wrapInt_add_wrapInt, hb,
    wrapInt_add_wrapInt]

theorem wrap_eq {s : IntTy} {a b : Int} (h : wrapInt s a = wrapInt s b) :
    JInt.wrap s a = JInt.wrap s b := Subtype.ext h

/-! ### `add_sum` on integers of type `t` and `sumTy t` -/

theorem plus_int (s t u : IntTy) (h : IntTy.promote s t = u) (x : JInt s) (y : JInt t) :
    Val.plus (.int s x) (.int t y) = .int u (JInt.wrap u (x.val + y.val)) := by
  subst h
  show Val.int (IntTy.promote s t) (JInt.rem _ x + JInt.rem _ y) =
    Val.int (IntTy.promote s t) (JInt.wrap _ (x.val + y.val))
  refine congrArg (Val.int _) (Subtype.ext ?_)
  show wrapInt _ (wrapInt _ x.val + wrapInt _ y.val) = wrapInt _ (x.val + y.val)
  rw [wrapInt_wrapInt_add, wrapInt_add_wrapInt]

theorem addSum_int (t S : IntTy) (hS : sumTy t = S) {s1 s2 : IntTy} (h1 : s1 = t ∨ s1 = S)
    (h2 : s2 = t ∨ s2 = S) (x : JInt s1) (y : JInt s2) :
    Val.addSum (.int s1 x) (.int s2 y) = .int S (JInt.wrap S (x.val + y.val)) := by
  cases t <;> simp only [sumTy, Val.smallSigned, Val.smallUnsigned] at hS <;> subst hS <;>
    (rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl) <;>
    first
    | exact plus_int _ _ _ rfl x y
    | rfl

/-- `v` is an integer of type `t` or of type `sumTy t`. -/
def SumG (t : IntTy) (v : Val) : Prop :=
  (∃ x, v = .int t x) ∨ (∃ a, v = .int (sumTy t) a)

theorem addSum_G (t : IntTy) {u v : Val} (hu : SumG t u) (hv : SumG t v) :
    Val.addSum u v = .int (sumTy t) (JInt.wrap (sumTy t) (u.intVal + v.intVal)) := by
  rcases hu with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rcases hv with ⟨y, rfl⟩ | ⟨y, rfl⟩ <;>
    exact addSum_int t _ rfl (by simp) (by simp) x y

theorem addW (t : IntTy) (z : Int) {v : Val} (hv : SumG t v) :
    Val.addSum (.int (sumTy t) (JInt.wrap (sumTy t) z)) v =
      .int (sumTy t) (JInt.wrap (sumTy t) (z + v.intVal)) := by
  rw [addSum_G t (Or.inr ⟨_, rfl⟩) hv]
  exact congrArg (Val.int _) (wrap_eq (wrapInt_wrapInt_add _ z _))

/-! ### Pairwise blocks -/

/-- `add_sum` as the reduction operator of `mapreducedim`. -/
abbrev opS : Val → Val → R Val := fun x y => .ok (Val.addSum x y)

theorem ok_bind {α β : Type} (a : α) (f : α → R β) : (Except.ok a >>= f) = f a := rfl

/-- A block result: an integer of type `t` or `sumTy t` congruent to `s`. -/
def MrGood (t : IntTy) (r : R Val) (s : Int) : Prop :=
  ∃ w, r = .ok w ∧ SumG t w ∧ wrapInt (sumTy t) w.intVal = wrapInt (sumTy t) s

theorem liftOp_good (t : IntTy) {r1 r2 : R Val} {s1 s2 : Int} (h1 : MrGood t r1 s1)
    (h2 : MrGood t r2 s2) : MrGood t (liftOp opS r1 r2) (s1 + s2) := by
  obtain ⟨w1, rfl, g1, e1⟩ := h1
  obtain ⟨w2, rfl, g2, e2⟩ := h2
  refine ⟨.int (sumTy t) (JInt.wrap (sumTy t) (w1.intVal + w2.intVal)), ?_, Or.inr ⟨_, rfl⟩, ?_⟩
  · show Except.ok (Val.addSum w1 w2) = _
    rw [addSum_G t g1 g2]
  · show wrapInt _ (wrapInt _ (w1.intVal + w2.intVal)) = _
    rw [wrapInt_wrapInt]
    exact wrapInt_add_congr _ e1 e2

theorem elem_good (t : IntTy) {x : Val} (hx : ∃ y, x = .int t y) :
    MrGood t (.ok x) x.intVal :=
  ⟨x, rfl, Or.inl hx, rfl⟩

theorem fold_good (t : IntTy) (xs : List Val) (hx : ∀ x ∈ xs, ∃ y, x = .int t y) :
    ∀ (r : R Val) (s : Int), MrGood t r s →
      MrGood t (xs.foldl (fun v x => liftOp opS v (.ok x)) r) (s + (xs.map Val.intVal).sum) := by
  induction xs with
  | nil => intro r s h; simpa using h
  | cons x xs ih =>
    intro r s h
    have := ih (fun y hy => hx y (by simp [hy])) _ _
      (liftOp_good t h (elem_good t (hx x (by simp))))
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ← Int.add_assoc]
    exact this

theorem mr_good (t : IntTy) (blk : Nat) : ∀ (n : Nat) (a : Val) (rest : List Val),
    rest.length < n → (∀ x ∈ a :: rest, ∃ y, x = .int t y) →
    MrGood t (mrImpl (fun x => (Except.ok x : R Val)) (liftOp opS) (fun x => .ok x) blk a rest)
      ((a :: rest).map Val.intVal).sum := by
  intro n
  induction n with
  | zero => intro a rest h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro a rest hlen hall
    have ha := hall a (by simp)
    cases rest with
    | nil =>
      rw [mrImpl]
      simpa using elem_good t ha
    | cons b rest' =>
      have hb := hall b (by simp)
      rw [mrImpl]
      split
      · have := fold_good t rest' (fun x hx => hall x (by simp [hx])) _ _
          (liftOp_good t (elem_good t ha) (elem_good t hb))
        rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ← Int.add_assoc]
        exact this
      · split
        · rename_i h
          have := congrArg List.length h
          simp only [List.length_drop, List.length_cons, List.length_nil] at this
          omega
        · rename_i c rest2 h
          have hsum : ((a :: b :: rest').map Val.intVal).sum =
              ((a :: (b :: rest').take ((rest'.length + 1) / 2)).map Val.intVal).sum +
                ((c :: rest2).map Val.intVal).sum := by
            have e1 : ((b :: rest').map Val.intVal).sum =
                (((b :: rest').take ((rest'.length + 1) / 2)).map Val.intVal).sum +
                  (((b :: rest').drop ((rest'.length + 1) / 2)).map Val.intVal).sum := by
              rw [← List.sum_append, ← List.map_append, List.take_append_drop]
            rw [← h]
            simp only [List.map_cons, List.sum_cons] at e1 ⊢
            omega
          rw [hsum]
          have hlen2 := congrArg List.length h
          simp only [List.length_drop, List.length_cons] at hlen2 hlen
          refine liftOp_good t (ih _ _ ?_ ?_) (ih _ _ ?_ ?_)
          · simp only [List.length_take, List.length_cons]; omega
          · intro x hx
            rcases List.mem_cons.1 hx with hx | hx
            · exact hall x (by simp [hx])
            · exact hall x (List.mem_cons_of_mem _ (List.mem_of_mem_take hx))
          · omega
          · intro x hx
            rw [← h] at hx
            exact hall x (List.mem_cons_of_mem _ (List.mem_of_mem_drop hx))

theorem foldM_add (t : IntTy) (xs : List Val) (hx : ∀ x ∈ xs, ∃ y, x = .int t y)
    (g : Val → Val → R Val) (z : Int) (hg : ∀ r a, g r a = .ok (Val.addSum r a)) :
    xs.foldlM g (.int (sumTy t) (JInt.wrap (sumTy t) z)) =
      .ok (.int (sumTy t) (JInt.wrap (sumTy t) (z + (xs.map Val.intVal).sum))) := by
  revert z
  induction xs with
  | nil =>
    intro z
    show Except.ok _ = Except.ok _
    simp
  | cons x xs ih =>
    intro z
    rw [List.foldlM_cons, hg, ok_bind, addW t z (Or.inl (hx x (by simp))),
      ih (fun y hy => hx y (by simp [hy])) (z + x.intVal), List.map_cons, List.sum_cons,
      Int.add_assoc]

/-! ### Loops and result arrays -/

theorem foldlM_range {σ : Type} (step : σ → Nat → R σ) (I : Nat → σ → Prop) (Q : σ → Prop)
    (n : Nat) (s0 : σ) (h0 : I 0 s0)
    (hs : ∀ j < n, ∀ s, I j s → ∃ s', step s j = .ok s' ∧ I (j + 1) s')
    (hQ : ∀ s, I n s → Q s) : ∃ s, (List.range n).foldlM step s0 = .ok s ∧ Q s := by
  suffices h : ∃ s, (List.range n).foldlM step s0 = .ok s ∧ I n s by
    obtain ⟨s, h1, h2⟩ := h
    exact ⟨s, h1, hQ s h2⟩
  clear hQ
  induction n with
  | zero => exact ⟨s0, rfl, h0⟩
  | succ n ih =>
    obtain ⟨s, h1, h2⟩ := ih (fun j hj => hs j (by omega))
    obtain ⟨s', e, h3⟩ := hs n (by omega) s h2
    refine ⟨s', ?_, h3⟩
    rw [List.range_succ, List.foldlM_append, h1]
    show List.foldlM step s [n] = _
    rw [List.foldlM_cons, e]
    rfl

theorem store_int (Rr : Arr) (S : IntTy) (hty : Rr.ty = .int S) (k : Nat) (z : JInt S) :
    Rr.store k (.int S z) = .ok { Rr with data := Rr.data.set k (.int S z) } := by
  have hc : Rr.ty.convert (.int S z) = .ok (.int S z) := by
    rw [hty]
    cases S <;> rfl
  unfold Arr.store
  rw [hc]
  rfl

theorem get_set (Rr : Arr) (k i : Nat) (w : Val) (hk : k < Rr.data.length) :
    Arr.get { Rr with data := Rr.data.set k w } i = if k = i then w else Rr.get i := by
  unfold Arr.get
  by_cases h : k = i
  · subst h; simp [List.getD_eq_getElem?_getD, hk]
  · simp [List.getD_eq_getElem?_getD, h]

/-- `R` has element type `sumTy`, shape `rm × rn`, and entries `wrap (P i)`. -/
def Inv (S : IntTy) (rm rn : Nat) (P : Nat → Int) (Rr : Arr) : Prop :=
  Rr.ty = .int S ∧ Rr.m = rm ∧ Rr.n = rn ∧ Rr.data.length = rm * rn ∧
    ∀ i < rm * rn, Rr.get i = .int S (JInt.wrap S (P i))

theorem Inv.congr {S : IntTy} {rm rn : Nat} {P P' : Nat → Int} {Rr : Arr}
    (h : Inv S rm rn P Rr) (hP : ∀ i < rm * rn, wrapInt S (P i) = wrapInt S (P' i)) :
    Inv S rm rn P' Rr := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun i hi => by rw [h5 i hi, wrap_eq (hP i hi)]⟩

theorem Inv.store {S : IntTy} {rm rn : Nat} {P : Nat → Int} {Rr : Arr}
    (h : Inv S rm rn P Rr) {k : Nat} (hk : k < rm * rn) (z : Int) (P' : Nat → Int)
    (hP : ∀ i < rm * rn, wrapInt S (P' i) = wrapInt S (if i = k then z else P i)) :
    ∃ Rr', Rr.store k (.int S (JInt.wrap S z)) = .ok Rr' ∧ Inv S rm rn P' Rr' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨_, store_int Rr S h1 k _, h1, h2, h3, by simp [h4], fun i hi => ?_⟩
  rw [get_set _ _ _ _ (by omega), wrap_eq (hP i hi)]
  by_cases hki : k = i
  · subst hki; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hki, if_neg (Ne.symm hki)]; exact h5 i hi

theorem inv_init (S : IntTy) (rm rn : Nat) :
    Inv S rm rn (fun _ => 0)
      { ty := .int S, m := rm, n := rn,
        data := List.replicate (rm * rn) (.int S (JInt.wrap S 0)) } := by
  refine ⟨rfl, rfl, rfl, by simp, fun i hi => ?_⟩
  simp [Arr.get, List.getD_eq_getElem?_getD, hi]

theorem init_eq (t : IntTy) (A : Mat Val) (d rm rn : Nat)
    (hs : reducedShape A.m A.n d = (rm, rn)) :
    initSumProd (fun x => .ok x) Val.addSum zeroOf (.int t) A d = .ok
      { ty := .int (sumTy t), m := rm, n := rn,
        data := List.replicate (rm * rn) (.int (sumTy t) (JInt.wrap (sumTy t) 0)) } := by
  have hz : Val.addSum (.int t (JInt.lit t 0)) (.int t (JInt.lit t 0)) =
      .int (sumTy t) (JInt.wrap (sumTy t) 0) := by
    rw [addSum_int t _ rfl (Or.inl rfl) (Or.inl rfl)]
    exact congrArg (Val.int _) (wrap_eq (by cases t <;> decide))
  have hc : Ty.convert (.int (sumTy t)) (.int (sumTy t) (JInt.wrap (sumTy t) 0)) =
      .ok (.int (sumTy t) (JInt.wrap (sumTy t) 0)) := by
    cases t <;> rfl
  show initArray (Val.addSum (.int t (JInt.lit t 0)) (.int t (JInt.lit t 0))).typeOf A.m A.n d
    (Val.addSum (.int t (JInt.lit t 0)) (.int t (JInt.lit t 0))) = _
  rw [hz]
  unfold initArray
  simp only [Val.typeOf]
  rw [hc, hs]
  rfl

/-! ### Slices -/

/-- Entry `(i, j)` of `A` as an integer. -/
def rowTerm (A : Mat Val) (i j : Nat) : Int := (A.data.getD (i + A.m * j) .missing).intVal

/-- `g 0 + ... + g (j - 1)`. -/
def rs (g : Nat → Int) (j : Nat) : Int := ((List.range j).map g).sum

theorem rs_zero (g : Nat → Int) : rs g 0 = 0 := rfl

theorem rs_succ (g : Nat → Int) (j : Nat) : rs g (j + 1) = rs g j + g j := by
  simp [rs, List.range_succ, List.sum_append]

theorem slice_one (A : Mat Val) (k : Nat) : A.slice 1 k = A.col k := by simp [Mat.slice]

theorem slice_two (A : Mat Val) (k : Nat) : A.slice 2 k = A.row k := by simp [Mat.slice]

theorem row_sum (A : Mat Val) (i : Nat) :
    ((A.row i).map Val.intVal).sum = rs (rowTerm A i) A.n := by
  unfold Mat.row rs rowTerm
  rw [List.map_map]
  rfl

theorem getD_mem {l : List Val} {i : Nat} (hi : i < l.length) : l.getD i .missing ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem col_one (A : Mat Val) (hm : A.m = 1) {j : Nat} (hj : j < A.data.length) :
    ((A.col j).map Val.intVal).sum = rowTerm A 0 j := by
  unfold Mat.col rowTerm
  rw [hm, Nat.one_mul, Nat.zero_add, List.drop_eq_getElem_cons hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some]
  show ((A.data[j] :: List.take 0 (List.drop (j + 1) A.data)).map Val.intVal).sum = _
  simp

theorem sum_one (A : Mat Val) (hm : A.m = 1) (hWF : A.data.length = A.m * A.n) :
    rs (rowTerm A 0) A.n = (A.data.map Val.intVal).sum := by
  unfold rs
  congr 1
  apply List.ext_getElem
  · simp [hWF, hm]
  · intro i _ h2
    simp only [List.length_map] at h2
    simp only [List.getElem_map, List.getElem_range, rowTerm, hm, Nat.one_mul, Nat.zero_add]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-! ### The three paths of `mapreducedim` -/

/-- The `lsiz > 16` path: pairwise `mapreduce_impl` over each contiguous block. -/
theorem fast_path (t : IntTy) (A : Mat Val) (hall : ∀ x ∈ A.data, ∃ y, x = .int t y)
    (d rm rn ls : Nat) (Q : Nat → Int) (R0 : Arr) (h0 : Inv (sumTy t) rm rn (fun _ => 0) R0)
    (hmn : ¬ A.m * A.n = 0) (hlsd : lsiz A.m A.n d = ls) (hls : ls > 16)
    (hblk : ∀ k < rm * rn, k * ls + ls ≤ A.data.length)
    (hQ : ∀ k < rm * rn, (((A.data.drop (k * ls)).take ls).map Val.intVal).sum = Q k) :
    ∃ Rr, mapreducedim (fun x => .ok x) opS 1024 R0 A d = .ok Rr ∧
      Inv (sumTy t) rm rn Q Rr := by
  unfold mapreducedim
  rw [if_neg hmn]
  try dsimp only
  rw [hlsd, if_pos hls, h0.2.2.2.1]
  apply foldlM_range (I := fun j Rr => Inv (sumTy t) rm rn (fun i => if i < j then Q i else 0) Rr)
  · exact h0.congr fun i _ => by simp
  · intro k hk Rr hI
    have hlen := hblk k hk
    obtain ⟨a, rest, hD⟩ : ∃ a rest, A.data.drop (k * ls) = a :: rest := by
      cases h : A.data.drop (k * ls) with
      | nil =>
        have := congrArg List.length h
        simp only [List.length_drop, List.length_nil] at this
        omega
      | cons a rest => exact ⟨a, rest, rfl⟩
    have hblock : a :: rest.take (ls - 1) = (A.data.drop (k * ls)).take ls := by
      rw [hD]
      obtain ⟨l, rfl⟩ : ∃ l, ls = l + 1 := ⟨ls - 1, by omega⟩
      simp
    have hmem : ∀ x ∈ a :: rest.take (ls - 1), ∃ y, x = .int t y := by
      intro x hx
      rw [hblock] at hx
      exact hall x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    obtain ⟨w, hw, gw, ew⟩ := mr_good t 1024 _ a (rest.take (ls - 1)) (Nat.lt_add_one _) hmem
    obtain ⟨hty, hm, hn, hl, hg⟩ := hI
    obtain ⟨Rr', hst, hI'⟩ := Inv.store ⟨hty, hm, hn, hl, hg⟩ hk
      ((if k < k then Q k else 0) + w.intVal) (fun i => if i < k + 1 then Q i else 0) (by
        intro i hi
        try dsimp only
        by_cases hik : i = k
        · subst hik
          rw [if_pos (Nat.lt_add_one i), if_pos rfl, if_neg (Nat.lt_irrefl i), Int.zero_add,
            ← hQ i hi, ← hblock]
          exact ew.symm
        · rw [if_neg hik]
          by_cases hlt : i < k
          · rw [if_pos hlt, if_pos (show i < k + 1 by omega)]
          · rw [if_neg hlt, if_neg (show ¬ i < k + 1 by omega)])
    refine ⟨Rr', ?_, hI'⟩
    try dsimp only
    rw [hD]
    try dsimp only
    rw [hw, ok_bind, hg k hk, ok_bind, addW t _ gw]
    exact hst
  · intro Rr h
    exact h.congr fun i hi => by
      try dsimp only
      rw [if_pos hi]

/-- The `size(R, 1) == 1` path for `dims = 1`: fold each column into `R[j]`. -/
theorem col_path (t : IntTy) (A : Mat Val) (hall : ∀ x ∈ A.data, ∃ y, x = .int t y)
    (hm16 : A.m ≤ 16) (hmn : ¬ A.m * A.n = 0) (R0 : Arr)
    (h0 : Inv (sumTy t) 1 A.n (fun _ => 0) R0) :
    ∃ Rr, mapreducedim (fun x => .ok x) opS 1024 R0 A 1 = .ok Rr ∧
      Inv (sumTy t) 1 A.n (fun k => ((A.slice 1 k).map Val.intVal).sum) Rr := by
  have hls : ¬ lsiz A.m A.n 1 > 16 := by
    unfold lsiz
    rw [if_pos rfl]
    split <;> omega
  unfold mapreducedim
  rw [if_neg hmn]
  try dsimp only
  rw [if_neg hls, if_pos h0.2.1]
  apply foldlM_range (I := fun j Rr => Inv (sumTy t) 1 A.n
    (fun i => if i < j then ((A.col i).map Val.intVal).sum else 0) Rr)
  · exact h0.congr fun i _ => by simp
  · intro j hj Rr hI
    obtain ⟨hty, hm, hn, hl, hg⟩ := hI
    have hjr : (if Rr.n = 1 then 0 else j) = j := by
      by_cases h : Rr.n = 1 <;> simp [h] <;> omega
    have hcol : ∀ x ∈ A.col j, ∃ y, x = .int t y :=
      fun x hx => hall x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    obtain ⟨Rr', hst, hI'⟩ := Inv.store ⟨hty, hm, hn, hl, hg⟩ (k := j) (by omega)
      ((if j < j then ((A.col j).map Val.intVal).sum else 0) + ((A.col j).map Val.intVal).sum)
      (fun i => if i < j + 1 then ((A.col i).map Val.intVal).sum else 0) (by
        intro i hi
        try dsimp only
        by_cases hij : i = j
        · subst hij
          rw [if_pos (Nat.lt_add_one i), if_pos rfl, if_neg (Nat.lt_irrefl i), Int.zero_add]
        · rw [if_neg hij]
          by_cases hlt : i < j
          · rw [if_pos hlt, if_pos (show i < j + 1 by omega)]
          · rw [if_neg hlt, if_neg (show ¬ i < j + 1 by omega)])
    refine ⟨Rr', ?_, hI'⟩
    try dsimp only
    rw [hjr, hg j (by omega), foldM_add t _ hcol, ok_bind]
    · exact hst
    · intro r a; rfl
  · intro Rr h
    exact h.congr fun i hi => by
      simp only [slice_one]
      rw [if_pos (show i < A.n by omega)]

/-- The `size(R, 1) == 1` path for `dims = 2` with one row: fold every column into `R[1]`. -/
theorem one_row_path (t : IntTy) (A : Mat Val) (hall : ∀ x ∈ A.data, ∃ y, x = .int t y)
    (hWF : A.data.length = A.m * A.n) (hm : A.m = 1) (hn16 : A.n ≤ 16)
    (hmn : ¬ A.m * A.n = 0) (R0 : Arr) (h0 : Inv (sumTy t) A.m 1 (fun _ => 0) R0) :
    ∃ Rr, mapreducedim (fun x => .ok x) opS 1024 R0 A 2 = .ok Rr ∧
      Inv (sumTy t) A.m 1 (fun k => ((A.slice 2 k).map Val.intVal).sum) Rr := by
  have hls : ¬ lsiz A.m A.n 2 > 16 := by
    unfold lsiz
    rw [if_neg (show ¬ (2 = 1) by decide), if_pos rfl, if_pos hm]
    split <;> omega
  unfold mapreducedim
  rw [if_neg hmn]
  try dsimp only
  rw [if_neg hls, if_pos (h0.2.1.trans hm)]
  apply foldlM_range (I := fun j Rr => Inv (sumTy t) A.m 1 (fun _ => rs (rowTerm A 0) j) Rr)
  · exact h0.congr fun i _ => by simp [rs]
  · intro j hj Rr hI
    obtain ⟨hty, hm', hn', hl, hg⟩ := hI
    have hjr : (if Rr.n = 1 then 0 else j) = 0 := if_pos hn'
    have hcol : ∀ x ∈ A.col j, ∃ y, x = .int t y :=
      fun x hx => hall x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    have hjd : j < A.data.length := by rw [hWF, hm]; omega
    obtain ⟨Rr', hst, hI'⟩ := Inv.store ⟨hty, hm', hn', hl, hg⟩ (k := 0) (by rw [hm]; omega)
      (rs (rowTerm A 0) j + ((A.col j).map Val.intVal).sum)
      (fun _ => rs (rowTerm A 0) (j + 1)) (by
        intro i hi
        have hi0 : i = 0 := by rw [hm] at hi; omega
        subst hi0
        try dsimp only
        rw [if_pos rfl, rs_succ, col_one A hm hjd])
    refine ⟨Rr', ?_, hI'⟩
    try dsimp only
    rw [hjr, hg 0 (by rw [hm]; omega), foldM_add t _ hcol, ok_bind]
    · exact hst
    · intro r a; rfl
  · intro Rr h
    exact h.congr fun i hi => by
      have hi0 : i = 0 := by rw [hm] at hi; omega
      subst hi0
      simp only [slice_two, row_sum]

/-- The general path (`dims = 2`, several rows): accumulate each column into `R`. -/
theorem row_path (t : IntTy) (A : Mat Val) (hall : ∀ x ∈ A.data, ∃ y, x = .int t y)
    (hWF : A.data.length = A.m * A.n) (hm2 : 2 ≤ A.m) (hmn : ¬ A.m * A.n = 0) (R0 : Arr)
    (h0 : Inv (sumTy t) A.m 1 (fun _ => 0) R0) :
    ∃ Rr, mapreducedim (fun x => .ok x) opS 1024 R0 A 2 = .ok Rr ∧
      Inv (sumTy t) A.m 1 (fun k => ((A.slice 2 k).map Val.intVal).sum) Rr := by
  have hls : ¬ lsiz A.m A.n 2 > 16 := by
    unfold lsiz
    rw [if_neg (show ¬ (2 = 1) by decide), if_pos rfl, if_neg (show ¬ A.m = 1 by omega)]
    split <;> omega
  have hR0 : ¬ R0.m = 1 := by rw [h0.2.1]; omega
  unfold mapreducedim
  rw [if_neg hmn]
  try dsimp only
  rw [if_neg hls, if_neg hR0]
  apply foldlM_range (I := fun j Rr => Inv (sumTy t) A.m 1 (fun i => rs (rowTerm A i) j) Rr)
  · exact h0.congr fun i _ => by simp [rs]
  · intro j hj Rr hI
    have hjr : (if Rr.n = 1 then 0 else j) = 0 := if_pos hI.2.2.1
    try dsimp only
    rw [hjr]
    apply foldlM_range (I := fun i' Rr' => Inv (sumTy t) A.m 1
      (fun i => rs (rowTerm A i) j + if i < i' then rowTerm A i j else 0) Rr')
    · exact hI.congr fun i _ => by simp
    · intro i' hi' Rr' hJ
      obtain ⟨hty, hm', hn', hl, hg⟩ := hJ
      have hidx : i' + A.m * j < A.data.length := by
        have h1 : A.m * (j + 1) ≤ A.m * A.n := Nat.mul_le_mul_left A.m (by omega)
        rw [Nat.mul_add, Nat.mul_one] at h1
        omega
      obtain ⟨Rr'', hst, hJ'⟩ := Inv.store ⟨hty, hm', hn', hl, hg⟩ (k := i') (by omega)
        ((rs (rowTerm A i') j + if i' < i' then rowTerm A i' j else 0) +
          (A.data.getD (i' + A.m * j) .missing).intVal)
        (fun i => rs (rowTerm A i) j + if i < i' + 1 then rowTerm A i j else 0) (by
          intro i hi
          try dsimp only
          by_cases hii : i = i'
          · subst hii
            (rw [if_pos (Nat.lt_add_one i), if_pos rfl, if_neg (Nat.lt_irrefl i), Int.add_zero])
              <;> rfl
          · rw [if_neg hii]
            by_cases hlt : i < i'
            · rw [if_pos hlt, if_pos (show i < i' + 1 by omega)]
            · rw [if_neg hlt, if_neg (show ¬ i < i' + 1 by omega)])
      refine ⟨Rr'', ?_, hJ'⟩
      try dsimp only
      try simp only [Nat.mul_zero, Nat.add_zero]
      rw [ok_bind, hg i' (by omega), ok_bind, addW t _ (Or.inl (hall _ (getD_mem hidx)))]
      exact hst
    · intro Rr' hJ
      exact hJ.congr fun i hi => by
        try dsimp only
        rw [if_pos (show i < A.m by omega), rs_succ]
  · intro Rr h
    exact h.congr fun i _ => by simp only [slice_two, row_sum]

end SumDimsProof

open SumDimsProof in
theorem sumDimsExact_proven : SumDimsExact := by
  intro t A d hWF hd hall
  have hWF' : A.data.length = A.m * A.n := hWF
  suffices h : ∃ rm rn, reducedShape A.m A.n d = (rm, rn) ∧ ∃ Rr,
      mapreducedim (fun x => .ok x) opS 1024
        { ty := .int (sumTy t), m := rm, n := rn,
          data := List.replicate (rm * rn) (.int (sumTy t) (JInt.wrap (sumTy t) 0)) } A d
        = .ok Rr ∧
      Inv (sumTy t) rm rn (fun k => ((A.slice d k).map Val.intVal).sum) Rr by
    obtain ⟨rm, rn, hs, Rr, h1, hty, hm, hn, hl, hg⟩ := h
    refine ⟨Rr, ?_, by rw [hm, hn, hs], by rw [hl, hm, hn], fun k hk => hg k (hl ▸ hk)⟩
    unfold sumDims
    rw [init_eq t A d rm rn hs]
    exact h1
  rcases hd with rfl | rfl
  · refine ⟨1, A.n, by simp [reducedShape], ?_⟩
    by_cases hmn : A.m * A.n = 0
    · refine ⟨_, by unfold mapreducedim; rw [if_pos hmn], (inv_init _ 1 A.n).congr fun i hi => ?_⟩
      have hm0 : A.m = 0 := by
        rcases Nat.eq_zero_or_pos A.m with h | h
        · exact h
        · exact absurd hmn (Nat.pos_iff_ne_zero.1 (Nat.mul_pos h (by omega)))
      simp only [slice_one, Mat.col, hm0, List.take_zero, List.map_nil, List.sum_nil]
    · by_cases h16 : A.m > 16
      · refine fast_path t A hall 1 1 A.n A.m _ _ (inv_init _ 1 A.n) hmn ?_ h16 ?_ ?_
        · unfold lsiz
          rw [if_pos rfl, if_pos (show A.m > 1 by omega)]
        · intro k hk
          have h1 : (k + 1) * A.m ≤ A.n * A.m := Nat.mul_le_mul_right A.m (by omega)
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm A.n] at h1
          omega
        · intro k _
          rw [slice_one]
          unfold Mat.col
          rw [Nat.mul_comm]
      · exact col_path t A hall (by omega) hmn _ (inv_init _ 1 A.n)
  · refine ⟨A.m, 1, by simp [reducedShape], ?_⟩
    by_cases hmn : A.m * A.n = 0
    · refine ⟨_, by unfold mapreducedim; rw [if_pos hmn], (inv_init _ A.m 1).congr fun i hi => ?_⟩
      have hn0 : A.n = 0 := by
        rcases Nat.eq_zero_or_pos A.n with h | h
        · exact h
        · exact absurd hmn (Nat.pos_iff_ne_zero.1 (Nat.mul_pos (by omega) h))
      simp only [slice_two, row_sum, hn0, rs_zero]
    · by_cases hm1 : A.m = 1
      · by_cases h16 : A.n > 16
        · refine fast_path t A hall 2 A.m 1 A.n _ _ (inv_init _ A.m 1) hmn ?_ h16 ?_ ?_
          · unfold lsiz
            rw [if_neg (show ¬ (2 = 1) by decide), if_pos rfl, if_pos hm1,
              if_pos (show A.n > 1 by omega)]
          · intro k hk
            have : k = 0 := by rw [hm1] at hk; omega
            subst this
            rw [hWF', hm1]
            omega
          · intro k hk
            have : k = 0 := by rw [hm1] at hk; omega
            subst this
            rw [Nat.zero_mul, List.drop_zero,
              List.take_of_length_le (by rw [hWF', hm1]; omega), slice_two, row_sum,
              sum_one A hm1 hWF']
        · exact one_row_path t A hall hWF' hm1 (by omega) hmn _ (inv_init _ A.m 1)
      · have hm0 : A.m ≠ 0 := fun h => hmn (by rw [h, Nat.zero_mul])
        exact row_path t A hall hWF' (by omega) hmn _ (inv_init _ A.m 1)

end JuliaLean.Reduce
