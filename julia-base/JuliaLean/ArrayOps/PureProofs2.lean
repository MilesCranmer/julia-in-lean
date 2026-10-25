import JuliaLean.ArrayOps.PureProps

/-!
Proofs of the `findmax`/`findmin`, `sum`/`prod`, `accumulate`/`cumsum`, `diff` and
`vcat` statements of `PureProps`.
-/

namespace JuliaLean.ArrayOps

open JuliaLean
open JuliaLean.Float

/-! ### `findmax` and `findmin` -/

/-- `isless` is `<` on this key: NaN last, then by sign and magnitude. -/
private def lessKey (x : F64) : Int :=
  if F64.isnan x then 2 ^ 65 else if F64.signbit x then -(F64.toBits x : Int) else (F64.toBits x : Int)

/-- `isgreater` is `<` on this key: NaN first among the minima. -/
private def greatKey (x : F64) : Int :=
  if F64.isnan x then 2 ^ 65 else if F64.signbit x then (F64.toBits x : Int) else -(F64.toBits x : Int)

private theorem toBits_lt (x : F64) : F64.toBits x < 2 ^ 64 := x.isLt

private theorem key_isless (x y : F64) : decide (lessKey x < lessKey y) = F64.isless x y := by
  unfold F64.isless lessKey F64.signbit
  have hx := toBits_lt x
  have hy := toBits_lt y
  revert hx hy
  generalize F64.isnan x = a
  generalize F64.isnan y = b
  generalize F64.toBits x = m
  generalize F64.toBits y = n
  intro hx hy
  cases a <;> cases b <;> cases hsx : decide (m ≥ 2 ^ 63) <;> cases hsy : decide (n ≥ 2 ^ 63) <;>
    simp at hsx hsy ⊢ <;> first | omega | (constructor <;> intro <;> omega)

private theorem key_isgreater (x y : F64) : decide (greatKey x < greatKey y) = isgreater x y := by
  unfold isgreater F64.isless greatKey F64.signbit
  have hx := toBits_lt x
  have hy := toBits_lt y
  revert hx hy
  generalize F64.isnan x = a
  generalize F64.isnan y = b
  generalize F64.toBits x = m
  generalize F64.toBits y = n
  intro hx hy
  cases a <;> cases b <;> cases hsx : decide (m ≥ 2 ^ 63) <;> cases hsy : decide (n ≥ 2 ^ 63) <;>
    simp at hsx hsy ⊢ <;> first | omega | (constructor <;> intro <;> omega)

private theorem first_single {K : F64 → Int} (lt : F64 → F64 → Bool)
    (hK : ∀ x y, lt x y = decide (K x < K y)) (x : F64) : IsFirstExtremum lt [x] (x, 1) := by
  unfold IsFirstExtremum
  dsimp only
  refine ⟨Nat.le_refl 1, Nat.le_refl 1, rfl, ?_, ?_⟩
  · intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    rw [hK]
    exact decide_eq_false (Int.lt_irrefl _)
  · intro j h1 h2
    omega

/-- `findFold` with a strict-key comparison keeps the first maximum of the key. -/
private theorem first_fold {K : F64 → Int} (lt : F64 → F64 → Bool)
    (hK : ∀ x y, lt x y = decide (K x < K y)) :
    ∀ (l pre : List F64) (acc : F64 × Nat), IsFirstExtremum lt pre acc →
      IsFirstExtremum lt (pre ++ l) (findFold lt acc l (pre.length + 1))
  | [], pre, acc, h => by
    rw [List.append_nil]
    exact h
  | x :: rest, pre, acc, h => by
    have step : IsFirstExtremum lt (pre ++ [x])
        (if lt acc.1 x then (x, pre.length + 1) else acc) := by
      obtain ⟨m, p⟩ := acc
      unfold IsFirstExtremum at h ⊢
      dsimp only at h ⊢
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      simp only [hK, decide_eq_false_iff_not, decide_eq_true_eq] at h4 h5 ⊢
      by_cases hlt : K m < K x
      · rw [if_pos hlt]
        dsimp only
        refine ⟨by omega, by simp, by simp, ?_, ?_⟩
        · intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · have := h4 y hy
            omega
          · rw [List.mem_singleton] at hy
            subst hy
            omega
        · intro j hj1 hj2 y hy
          rw [List.getElem?_append_left (l₂ := [x]) (show j - 1 < pre.length by omega)] at hy
          have := h4 y (List.mem_iff_getElem?.2 ⟨_, hy⟩)
          omega
      · rw [if_neg hlt]
        dsimp only
        refine ⟨h1, by simp; omega, ?_, ?_, ?_⟩
        · rw [List.getElem?_append_left (l₂ := [x]) (show p - 1 < pre.length by omega)]
          exact h3
        · intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact h4 y hy
          · rw [List.mem_singleton] at hy
            subst hy
            exact hlt
        · intro j hj1 hj2 y hy
          rw [List.getElem?_append_left (l₂ := [x]) (show j - 1 < pre.length by omega)] at hy
          exact h5 j hj1 hj2 y hy
    have ih := first_fold lt hK rest (pre ++ [x]) _ step
    rw [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at ih
    exact ih

theorem findExtremaSpec : FindExtremaSpec := by
  intro v _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · obtain ⟨x, rest, rfl⟩ : ∃ x rest, v = x :: rest := by
      cases v with
      | nil => exact absurd rfl h
      | cons x rest => exact ⟨x, rest, rfl⟩
    have hl : ∀ a b, F64.isless a b = decide (lessKey a < lessKey b) :=
      fun a b => (key_isless a b).symm
    have hg : ∀ a b, isgreater a b = decide (greatKey a < greatKey b) :=
      fun a b => (key_isgreater a b).symm
    refine ⟨_, _, rfl, ?_, rfl, ?_⟩
    · exact first_fold F64.isless hl rest [x] (x, 1) (first_single F64.isless hl x)
    · exact first_fold isgreater hg rest [x] (x, 1) (first_single isgreater hg x)

/-! ### `sum` and `prod` -/

private theorem wrapInt_emod (t : IntTy) (x : Int) : wrapInt t x % 2 ^ t.bits = x % 2 ^ t.bits := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

private theorem wrapInt_congr (t : IntTy) (x y : Int) (h : x % 2 ^ t.bits = y % 2 ^ t.bits) :
    wrapInt t x = wrapInt t y := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> omega

private theorem wrap_val {T : IntTy} (u : JInt T) : JInt.wrap T u.val = u :=
  Subtype.ext (wrapInt_of_inRange T u.val u.property)

private theorem wrap_add (T : IntTy) (a b : Int) :
    JInt.wrap T a + JInt.wrap T b = JInt.wrap T (a + b) := by
  apply Subtype.ext
  show wrapInt T (wrapInt T a + wrapInt T b) = wrapInt T (a + b)
  apply wrapInt_congr
  rw [Int.add_emod, wrapInt_emod, wrapInt_emod, ← Int.add_emod]

private theorem wrap_mul (T : IntTy) (a b : Int) :
    JInt.wrap T a * JInt.wrap T b = JInt.wrap T (a * b) := by
  apply Subtype.ext
  show wrapInt T (wrapInt T a * wrapInt T b) = wrapInt T (a * b)
  apply wrapInt_congr
  rw [Int.mul_emod, wrapInt_emod, wrapInt_emod, ← Int.mul_emod]

private theorem widen_val {t : IntTy} (x : JInt t) : (widen x).val = x.val := by
  obtain ⟨v, h1, h2⟩ := x
  show wrapInt (sumTy t) v = v
  apply wrapInt_of_inRange
  cases t <;> simp [sumTy, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h1 h2 ⊢ <;> omega

private structure MonoidLaws (c : Int → Int → Int) (e : Int) : Prop where
  assoc : ∀ a b d, c (c a b) d = c a (c b d)
  left : ∀ a, c e a = a
  right : ∀ a, c a e = a

private theorem addLaws : MonoidLaws (· + ·) 0 :=
  ⟨fun a b d => Int.add_assoc a b d, fun a => Int.zero_add a, fun a => Int.add_zero a⟩

private theorem mulLaws : MonoidLaws (· * ·) 1 :=
  ⟨fun a b d => Int.mul_assoc a b d, fun a => Int.one_mul a, fun a => Int.mul_one a⟩

/-- `c`-combination of `g i, g (i+1), ..., g (i+n-1)`, from the left. -/
private def seg (c : Int → Int → Int) (e : Int) (g : Nat → Int) (i : Nat) : Nat → Int
  | 0 => e
  | n + 1 => c (seg c e g i n) (g (i + n))

private theorem seg_one (c : Int → Int → Int) (e : Int) (g : Nat → Int) (i : Nat) :
    seg c e g i 1 = c e (g i) := rfl

private theorem seg_two (c : Int → Int → Int) (e : Int) (g : Nat → Int) (i : Nat) :
    seg c e g i 2 = c (c e (g i)) (g (i + 1)) := rfl

private theorem seg_add {c : Int → Int → Int} {e : Int} (M : MonoidLaws c e) (g : Nat → Int)
    (i a : Nat) : ∀ b, seg c e g i (a + b) = c (seg c e g i a) (seg c e g (i + a) b)
  | 0 => by simp only [Nat.add_zero, seg, M.right]
  | b + 1 => by
    show seg c e g i ((a + b) + 1) = _
    simp only [seg]
    rw [seg_add M g i a b, M.assoc, Nat.add_assoc]

private theorem block_eq {T : IntTy} (op : JInt T → JInt T → JInt T) (c : Int → Int → Int) (e : Int)
    (M : MonoidLaws c e) (hop : ∀ a b, op (JInt.wrap T a) (JInt.wrap T b) = JInt.wrap T (c a b))
    (xs : List (JInt T)) (s : Nat) : ∀ (n : Nat) (a : Int),
    ((List.range n).map (· + s)).foldl (fun v k => op v (xs.getD k (JInt.lit T 0))) (JInt.wrap T a) =
      JInt.wrap T (c a (seg c e (fun k => (xs.getD k (JInt.lit T 0)).val) s n))
  | 0, a => by simp [seg, M.right]
  | n + 1, a => by
    rw [List.range_succ, List.map_append, List.foldl_append, block_eq op c e M hop xs s n a]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, seg]
    rw [← wrap_val (xs.getD (n + s) (JInt.lit T 0)), hop, M.assoc, Nat.add_comm n s]

private theorem impl_eq {T : IntTy} (op : JInt T → JInt T → JInt T) (c : Int → Int → Int) (e : Int)
    (M : MonoidLaws c e) (hop : ∀ a b, op (JInt.wrap T a) (JInt.wrap T b) = JInt.wrap T (c a b))
    (xs : List (JInt T)) (blk i j : Nat) (hij : i ≤ j) :
    mapreduceImpl op xs blk i j =
      JInt.wrap T (seg c e (fun k => (xs.getD k (JInt.lit T 0)).val) i (j + 1 - i)) := by
  rw [mapreduceImpl]
  dsimp only
  split
  · rename_i h
    rw [show j + 1 - i = 1 by omega]
    simp only [seg_one, M.left, wrap_val]
  · split
    · rename_i h1 h2
      have hxy : op (xs.getD i (JInt.lit T 0)) (xs.getD (i + 1) (JInt.lit T 0)) =
          JInt.wrap T (c (xs.getD i (JInt.lit T 0)).val (xs.getD (i + 1) (JInt.lit T 0)).val) := by
        rw [← hop, wrap_val, wrap_val]
      rw [hxy, block_eq op c e M hop xs (i + 2)]
      congr 1
      rw [show j + 1 - i = 2 + (j + 1 - (i + 2)) by omega, seg_add M, seg_two, M.left]
    · rename_i h1 h2
      rw [impl_eq op c e M hop xs blk i (i + (j - i) / 2) (by omega),
        impl_eq op c e M hop xs blk (i + (j - i) / 2 + 1) j (by omega), hop]
      congr 1
      rw [show j + 1 - i = (i + (j - i) / 2 + 1 - i) + (j + 1 - (i + (j - i) / 2 + 1)) by omega,
        seg_add M, show i + (i + (j - i) / 2 + 1 - i) = i + (j - i) / 2 + 1 by omega]
termination_by j - i
decreasing_by all_goals omega

private theorem foldl_eq {T : IntTy} (op : JInt T → JInt T → JInt T) (c : Int → Int → Int) (e : Int)
    (M : MonoidLaws c e) (hop : ∀ a b, op (JInt.wrap T a) (JInt.wrap T b) = JInt.wrap T (c a b)) :
    ∀ (l : List (JInt T)) (a : Int),
      l.foldl op (JInt.wrap T a) = JInt.wrap T (c a ((l.map (·.val)).foldr c e))
  | [], a => by simp [M.right]
  | u :: l, a => by
    have hu : op (JInt.wrap T a) u = JInt.wrap T (c a u.val) := by rw [← hop, wrap_val]
    rw [List.foldl_cons, hu, foldl_eq op c e M hop l, List.map_cons, List.foldr_cons, M.assoc]

private theorem seg_full {T : IntTy} (c : Int → Int → Int) (e : Int) (M : MonoidLaws c e) :
    ∀ (xs pre : List (JInt T)),
      seg c e (fun k => ((pre ++ xs).getD k (JInt.lit T 0)).val) pre.length xs.length =
        (xs.map (·.val)).foldr c e
  | [], _ => rfl
  | x :: xs, pre => by
    have h := seg_full c e M xs (pre ++ [x])
    rw [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at h
    rw [List.length_cons, show xs.length + 1 = 1 + xs.length from Nat.add_comm _ _, seg_add M, h,
      List.map_cons, List.foldr_cons, seg_one, M.left]
    congr 1
    simp

private theorem seg_full0 {T : IntTy} (c : Int → Int → Int) (e : Int) (M : MonoidLaws c e)
    (xs : List (JInt T)) :
    seg c e (fun k => (xs.getD k (JInt.lit T 0)).val) 0 xs.length = (xs.map (·.val)).foldr c e := by
  have h := seg_full c e M xs []
  simp only [List.nil_append, List.length_nil] at h
  exact h

private theorem linear_eq {T : IntTy} (op : JInt T → JInt T → JInt T) (c : Int → Int → Int) (e : Int)
    (M : MonoidLaws c e) (hop : ∀ a b, op (JInt.wrap T a) (JInt.wrap T b) = JInt.wrap T (c a b))
    (xs : List (JInt T)) :
    mapreduceLinear op (JInt.lit T e) xs = JInt.wrap T ((xs.map (·.val)).foldr c e) := by
  match xs with
  | [] => rfl
  | [x] =>
    show x = JInt.wrap T (c x.val e)
    rw [M.right, wrap_val]
  | x :: y :: rest =>
    have h0 : ¬ (x :: y :: rest).length = 0 := by simp
    have h1 : ¬ (x :: y :: rest).length = 1 := by simp
    unfold mapreduceLinear
    simp only [h0, h1, ↓reduceIte]
    split
    · show rest.foldl op (op x y) = _
      have hxy : op x y = JInt.wrap T (c x.val y.val) := by rw [← hop, wrap_val, wrap_val]
      rw [hxy, foldl_eq op c e M hop, List.map_cons, List.map_cons, List.foldr_cons,
        List.foldr_cons, M.assoc]
    · rw [impl_eq op c e M hop _ 1024 0 _ (Nat.zero_le _)]
      have hlen : (x :: y :: rest).length - 1 + 1 - 0 = (x :: y :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [hlen, seg_full0 c e M]

theorem sumProdSpec : SumProdSpec := by
  intro t v _
  have hv : (v.map widen).map (·.val) = v.map (·.val) := by
    rw [List.map_map]
    congr 1
    funext x
    exact widen_val x
  constructor
  · unfold sum
    rw [linear_eq (T := sumTy t) (· + ·) (· + ·) 0 addLaws (fun a b => wrap_add _ a b), hv, sumVal]
  · unfold prod
    rw [linear_eq (T := sumTy t) (· * ·) (· * ·) 1 mulLaws (fun a b => wrap_mul _ a b), hv, prodVal]

/-! ### `accumulate`, `cumsum`, `diff` -/

private theorem scanl_eq_cons_tail {α β : Type} (f : β → α → β) (a : β) (l : List α) :
    l.scanl f a = a :: (l.scanl f a).tail := by
  cases l <;> simp

private theorem accLoop_eq {α β : Type} (op : β → α → β) :
    ∀ (c : β) (l : List α), accumulateLoop op c l = (l.scanl op c).tail
  | _, [] => rfl
  | c, x :: rest => by
    simp only [accumulateLoop]
    rw [accLoop_eq op (op c x) rest, ← scanl_eq_cons_tail]
    simp

private theorem cumLoop {t : IntTy} : ∀ (l : List (JInt t)) (s : Int),
    (accumulateLoop (fun c x => c + widen x) (JInt.wrap (sumTy t) s) l).map (·.val) =
      (List.range l.length).map fun k => wrapInt (sumTy t) (s + sumVal (l.take (k + 1)))
  | [], _ => rfl
  | y :: l, s => by
    have hc : JInt.wrap (sumTy t) s + widen y = JInt.wrap (sumTy t) (s + y.val) := by
      unfold widen
      exact wrap_add _ _ _
    simp only [accumulateLoop, List.map_cons, hc, cumLoop l (s + y.val), List.length_cons,
      List.range_succ_eq_map, List.map_map]
    simp [sumVal, JInt.wrap, Int.add_assoc]

theorem accumulateSpec : AccumulateSpec := by
  refine ⟨fun α β op init first v => ?_, fun t v _ => ?_⟩
  · cases v with
    | nil => rfl
    | cons x rest =>
      simp only [accumulate]
      rw [accLoop_eq, ← scanl_eq_cons_tail]
      simp
  · have h : cumsum v = accumulateLoop (fun c x => c + widen x) (JInt.wrap (sumTy t) 0) v := by
      cases v with
      | nil => rfl
      | cons x rest =>
        have hx : JInt.wrap (sumTy t) 0 + widen x = widen x := by
          unfold widen
          rw [wrap_add, Int.zero_add]
        simp only [cumsum, accumulate, accumulateLoop, hx]
    rw [h, cumLoop v 0]
    simp only [Int.zero_add]

theorem diffSpec : DiffSpec := by
  intro t v _
  refine ⟨by simp only [diff, List.length_zipWith, List.length_tail]; omega, fun k h => ?_⟩
  have h1 : k < v.length := by omega
  simp [diff, List.getElem?_zipWith, h, h1]
  try rfl

/-! ### `vcat` of unit ranges -/

private theorem ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x : Except ε α) >>= f = f x := rfl

private theorem error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α) >>= f = Except.error e := rfl

private theorem i64_max : IntTy.i64.max = 9223372036854775807 := by decide

private theorem i64_min : IntTy.i64.min = -9223372036854775808 := by decide

private theorem vcat_tot_nonneg : ∀ (rs : List (JInt64 × JInt64)),
    (∀ r ∈ rs, r.1.val ≤ r.2.val + 1 ∧ r.2.val - r.1.val + 1 ≤ IntTy.i64.max) →
    0 ≤ (rs.map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0
  | [], _ => by simp
  | r :: rs, h => by
    have h1 := (h r (by simp)).1
    have h2 := vcat_tot_nonneg rs (fun r' hr' => h r' (by simp [hr']))
    simp only [List.map_cons, List.foldr_cons]
    omega

private theorem vcat_len : ∀ (rs : List (JInt64 × JInt64)),
    (∀ r ∈ rs, r.1.val ≤ r.2.val + 1 ∧ r.2.val - r.1.val + 1 ≤ IntTy.i64.max) →
    ((rs.flatMap fun r => unitElems r.1 r.2).length : Int) =
      (rs.map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0
  | [], _ => by simp
  | r :: rs, h => by
    have h1 := (h r (by simp)).1
    have ih := vcat_len rs (fun r' hr' => h r' (by simp [hr']))
    have h3 : ((r.2.val - r.1.val + 1).toNat : Int) = r.2.val - r.1.val + 1 :=
      Int.toNat_of_nonneg (by omega)
    have hu : (unitElems r.1 r.2).length = (r.2.val - r.1.val + 1).toNat := by simp [unitElems]
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.foldr_cons, hu]
    omega

private theorem vcat_fold : ∀ (rs : List (JInt64 × JInt64)) (a : JInt64),
    (∀ r ∈ rs, r.1.val ≤ r.2.val + 1 ∧ r.2.val - r.1.val + 1 ≤ IntTy.i64.max) → 0 ≤ a.val →
    rs.foldlM (fun n r => checkedAdd64 n (JInt.wrap .i64 (r.2.val - r.1.val + 1))) a =
      if a.val + (rs.map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0 ≤ IntTy.i64.max
      then .ok (JInt.wrap .i64 (a.val + (rs.map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0))
      else .error (.overflowError "checked_add")
  | [], a, _, _ => by
    have := a.property.2
    simp only [List.foldlM_nil, List.map_nil, List.foldr_nil, Int.add_zero, this, ↓reduceIte,
      wrap_val]
    all_goals rfl
  | r :: rs, a, h, ha => by
    obtain ⟨h1, h2⟩ := h r (by simp)
    have hT := vcat_tot_nonneg rs (fun r' hr' => h r' (by simp [hr']))
    have hmax := i64_max
    have hmin := i64_min
    have hl : (JInt.wrap .i64 (r.2.val - r.1.val + 1)).val = r.2.val - r.1.val + 1 :=
      wrapInt_of_inRange _ _ ⟨by omega, h2⟩
    simp only [List.foldlM_cons]
    rw [checkedAdd64, hl]
    by_cases hs : a.val + (r.2.val - r.1.val + 1) ≤ IntTy.i64.max
    · rw [if_pos ⟨by omega, hs⟩]
      simp only [ok_bind]
      have hv : (JInt.wrap .i64 (a.val + (r.2.val - r.1.val + 1))).val =
          a.val + (r.2.val - r.1.val + 1) :=
        wrapInt_of_inRange _ _ ⟨by omega, hs⟩
      rw [vcat_fold rs _ (fun r' hr' => h r' (by simp [hr'])) (by omega), hv]
      simp only [List.map_cons, List.foldr_cons, Int.add_assoc]
    · rw [if_neg (fun hh => hs hh.2), error_bind]
      have hn : ¬ (a.val + ((r :: rs).map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0 ≤
          IntTy.i64.max) := by
        simp only [List.map_cons, List.foldr_cons]
        omega
      rw [if_neg hn]

theorem vcatRangesSpec : VcatRangesSpec := by
  intro rs h
  have h0 : (JInt.lit .i64 0).val = 0 := by decide
  have hmax := i64_max
  have hmin := i64_min
  unfold vcatRanges
  rw [vcat_fold rs (JInt.lit .i64 0) h (by rw [h0]; exact Int.le_refl 0), h0, Int.zero_add]
  by_cases hc : (rs.map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0 ≤ IntTy.i64.max
  · rw [if_pos hc, if_pos hc]
    simp only [ok_bind]
    have hT := vcat_tot_nonneg rs h
    have hv : (JInt.wrap .i64 ((rs.map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0)).val =
        (rs.map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0 :=
      wrapInt_of_inRange _ _ ⟨by omega, hc⟩
    rw [hv, if_pos (Int.le_of_eq (vcat_len rs h))]
    all_goals rfl
  · rw [if_neg hc, if_neg hc, error_bind]

end JuliaLean.ArrayOps
