import JuliaLean.Reduce.Props

/-!
Proofs of `MaxDimsInt` and `FindDimsSlices`: `maximum`/`minimum` and `findmax`/`findmin`
along a dimension hold the whole-collection reduction of every slice.
-/

namespace JuliaLean.Reduce

open JuliaLean.Float

/-! ### Generic facts -/

section generic
variable {α β γ σ : Type}

private theorem ok_bind {ε : Type} (a : α) (g : α → Except ε β) :
    (Except.ok a >>= g) = g a := rfl

private theorem pure_eq {ε : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem range_foldlM {step : σ → Nat → R σ} (F : Nat → σ) :
    ∀ {N : Nat} {s0 X : σ}, F 0 = s0 → F N = X → (∀ k < N, step (F k) k = .ok (F (k + 1))) →
      (List.range N).foldlM step s0 = .ok X
  | 0, _, _, h0, hX, _ => by subst h0; subst hX; rfl
  | N + 1, _, _, h0, hX, h => by
    subst h0; subst hX
    rw [List.range_succ, List.foldlM_append,
      range_foldlM F (N := N) rfl rfl (fun k hk => h k (by omega))]
    show List.foldlM step (F N) [N] = _
    rw [List.foldlM_cons, h N (Nat.lt_succ_self N)] <;> rfl

private theorem foldlM_ok (op : β → γ → β) :
    ∀ (l : List γ) (b : β), l.foldlM (fun r a => (Except.ok (op r a) : R β)) b = .ok (l.foldl op b)
  | [], _ => rfl
  | a :: l, b => foldlM_ok op l (op b a)

private theorem getD_eq {l : List γ} {i : Nat} (d : γ) (h : i < l.length) : l.getD i d = l[i] := by
  first
  | exact List.getD_eq_getElem _ _ h
  | simp [List.getD_eq_getElem?_getD, h]

private theorem getD_mem {l : List γ} {i : Nat} (d : γ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [getD_eq d h]; exact List.getElem_mem h

private theorem getD_map_range (g : Nat → γ) (dflt : γ) {N k : Nat} (hk : k < N) :
    ((List.range N).map g).getD k dflt = g k := by
  rw [getD_eq _ (by simp [hk])]; simp

private theorem getD_step (T U : Nat → γ) (dflt : γ) {N k : Nat} (hk : k < N) :
    ((List.range N).map fun j => if j < k then T j else U j).getD k dflt = U k := by
  rw [getD_map_range _ _ hk]; simp

private theorem getElem?_map_range (g : Nat → γ) {N k : Nat} (hk : k < N) :
    ((List.range N).map g)[k]? = some (g k) := by
  simp [hk]

private theorem map_range_const (c : γ) (N : Nat) :
    (List.range N).map (fun _ => c) = List.replicate N c :=
  List.ext_getElem (by simp) (fun i _ _ => by simp)

private theorem set_range_step (T U : Nat → γ) (N k : Nat) (hk : k < N) :
    ((List.range N).map fun j => if j < k then T j else U j).set k (T k) =
      (List.range N).map fun j => if j < k + 1 then T j else U j := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_set]
  simp only [List.getElem_map, List.getElem_range]
  by_cases hik : k = i
  · subst hik; simp
  · rw [if_neg hik]
    by_cases hi : i < k
    · have hi' : i < k + 1 := by omega
      rw [if_pos hi, if_pos hi']
    · have hi' : ¬ i < k + 1 := by omega
      rw [if_neg hi, if_neg hi']

private theorem range_step_same (T U : Nat → γ) (N k : Nat) (h : T k = U k) :
    ((List.range N).map fun j => if j < k then T j else U j) =
      (List.range N).map fun j => if j < k + 1 then T j else U j := by
  apply List.map_congr_left
  intro j _
  by_cases hjk : j = k
  · subst hjk; simp [h]
  · by_cases hj : j < k
    · have hj' : j < k + 1 := by omega
      rw [if_pos hj, if_pos hj']
    · have hj' : ¬ j < k + 1 := by omega
      rw [if_neg hj, if_neg hj']

private theorem range_full (T U : Nat → γ) (N : Nat) :
    ((List.range N).map fun j => if j < N then T j else U j) = (List.range N).map T := by
  apply List.map_congr_left
  intro j hj
  rw [if_pos (List.mem_range.1 hj)]

private theorem take_cons_pos {a : γ} {l : List γ} {n : Nat} (h : 0 < n) :
    (a :: l).take n = a :: l.take (n - 1) := by
  cases n with
  | zero => omega
  | succ n => simp

private theorem idx_lt {m n i j : Nat} (hi : i < m) (hj : j < n) : i + m * j < m * n := by
  have := Nat.mul_le_mul_left m (show j + 1 ≤ n by omega)
  rw [Nat.mul_add, Nat.mul_one] at this; omega

private theorem foldl_mem (op : β → β → β) (P : β → Prop) (hcl : ∀ a b, P a → P b → P (op a b)) :
    ∀ (l : List β) (y : β), P y → (∀ z ∈ l, P z) → P (l.foldl op y)
  | [], _, hy, _ => hy
  | z :: l, y, hy, hl =>
    foldl_mem op P hcl l (op y z) (hcl _ _ hy (hl z (by simp))) (fun w hw => hl w (by simp [hw]))

private theorem foldl_memf (f : α → β) (op : β → β → β) (P : β → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b)) :
    ∀ (l : List α) (y : β), P y → (∀ z ∈ l, P (f z)) → P (l.foldl (fun v z => op v (f z)) y)
  | [], _, hy, _ => hy
  | z :: l, y, hy, hl =>
    foldl_memf f op P hcl l (op y (f z)) (hcl _ _ hy (hl z (by simp)))
      (fun w hw => hl w (by simp [hw]))

private theorem foldl_assoc (op : β → β → β) (P : β → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (has : ∀ a b c, P a → P b → P c → op (op a b) c = op a (op b c)) :
    ∀ (l : List β) (x y : β), P x → P y → (∀ z ∈ l, P z) →
      op x (l.foldl op y) = l.foldl op (op x y)
  | [], _, _, _, _, _ => rfl
  | z :: l, x, y, hx, hy, hl => by
    have hz : P z := hl z (by simp)
    simp only [List.foldl_cons]
    rw [foldl_assoc op P hcl has l x _ hx (hcl _ _ hy hz) (fun w hw => hl w (by simp [hw])),
      has _ _ _ hx hy hz]

private theorem foldl_assocf (f : α → β) (op : β → β → β) (P : β → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (has : ∀ a b c, P a → P b → P c → op (op a b) c = op a (op b c)) :
    ∀ (l : List α) (x y : β), P x → P y → (∀ z ∈ l, P (f z)) →
      op x (l.foldl (fun v z => op v (f z)) y) = l.foldl (fun v z => op v (f z)) (op x y)
  | [], _, _, _, _, _ => rfl
  | z :: l, x, y, hx, hy, hl => by
    have hz : P (f z) := hl z (by simp)
    simp only [List.foldl_cons]
    rw [foldl_assocf f op P hcl has l x _ hx (hcl _ _ hy hz) (fun w hw => hl w (by simp [hw])),
      has _ _ _ hx hy hz]

/-! ### `mapreduce_impl` of an operation associative on a closed subset -/

private theorem mrImpl_nil' (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat) (a : α) :
    mrImpl f op first blk a [] = first a := by
  rw [mrImpl]

private theorem mrImpl_small' (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat) (a b : α)
    (rest : List α) (hc : rest.length + 1 < blk) :
    mrImpl f op first blk a (b :: rest) = rest.foldl (fun v x => op v (f x)) (op (f a) (f b)) := by
  rw [mrImpl]; simp only [hc, if_true]

private theorem mrImpl_split' (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat) (a b c : α)
    (rest rest2 : List α) (hc : ¬ rest.length + 1 < blk)
    (hd : (b :: rest).drop ((rest.length + 1) / 2) = c :: rest2) :
    mrImpl f op first blk a (b :: rest) =
      op (mrImpl f op first blk a ((b :: rest).take ((rest.length + 1) / 2)))
        (mrImpl f op first blk c rest2) := by
  rw [mrImpl]; simp only [hc, if_false]
  split
  · rename_i h; rw [hd] at h; cases h
  · rename_i c' rest2' h; rw [hd] at h; cases h; rfl

private theorem drop_half_cons' (b : α) (rest : List α) :
    ∃ c rest2, (b :: rest).drop ((rest.length + 1) / 2) = c :: rest2 := by
  cases h : (b :: rest).drop ((rest.length + 1) / 2) with
  | nil =>
    have := congrArg List.length h
    simp only [List.length_drop, List.length_cons, List.length_nil] at this; omega
  | cons c rest2 => exact ⟨c, rest2, rfl⟩

private theorem mrImpl_foldlP (f : α → β) (op : β → β → β) (blk : Nat) (P : β → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (has : ∀ a b c, P a → P b → P c → op (op a b) c = op a (op b c)) :
    ∀ (n : Nat) (a : α) (rest : List α), rest.length < n → P (f a) → (∀ z ∈ rest, P (f z)) →
      mrImpl f op f blk a rest = rest.foldl (fun v y => op v (f y)) (f a)
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, [], _, _, _ => mrImpl_nil' f op f blk a
  | n + 1, a, b :: rest, hlen, ha, hr => by
    by_cases hc : rest.length + 1 < blk
    · rw [mrImpl_small' f op f blk a b rest hc]; rfl
    · obtain ⟨c, rest2, hd⟩ := drop_half_cons' b rest
      simp only [List.length_cons] at hlen
      have hmem : ∀ z ∈ (b :: rest).drop ((rest.length + 1) / 2), P (f z) :=
        fun z hz => hr z (List.mem_of_mem_drop hz)
      rw [hd] at hmem
      have htk : ∀ z ∈ (b :: rest).take ((rest.length + 1) / 2), P (f z) :=
        fun z hz => hr z (List.mem_of_mem_take hz)
      have hc' : P (f c) := hmem c (by simp)
      have hr2 : ∀ z ∈ rest2, P (f z) := fun z hz => hmem z (by simp [hz])
      have hl2 : rest2.length < n := by
        have := congrArg List.length hd
        simp only [List.length_drop, List.length_cons] at this; omega
      have htl : ((b :: rest).take ((rest.length + 1) / 2)).length < n := by
        simp only [List.length_take, List.length_cons]; omega
      rw [mrImpl_split' f op f blk a b c rest rest2 hc hd,
        mrImpl_foldlP f op blk P hcl has n a _ htl ha htk,
        mrImpl_foldlP f op blk P hcl has n c rest2 hl2 hc' hr2,
        foldl_assocf f op P hcl has rest2 _ _ (foldl_memf f op P hcl _ _ ha htk) hc' hr2,
        ← List.foldl_cons, ← List.foldl_append, ← hd, List.take_append_drop]

end generic

/-- `r` is `.ok v` for a `v` in `P`. -/
private def OkP (P : Val → Prop) (r : R Val) : Prop := ∃ v, r = .ok v ∧ P v

private theorem foldl_lift (op : Val → Val → Val) : ∀ (l : List Val) (v : Val),
    l.foldl (fun r y => liftOp (fun x y => .ok (op x y)) r (.ok y)) (.ok v) = .ok (l.foldl op v)
  | [], _ => rfl
  | y :: l, v => foldl_lift op l (op v y)

private theorem fast_block (op : Val → Val → Val) (P : Val → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (has : ∀ a b c, P a → P b → P c → op (op a b) c = op a (op b c)) (blk : Nat)
    (a : Val) (rest : List Val) (ha : P a) (hr : ∀ z ∈ rest, P z) :
    mrImpl (fun x : Val => (Except.ok x : R Val)) (liftOp fun x y => .ok (op x y))
      (fun x => .ok x) blk a rest = .ok (rest.foldl op a) := by
  have hclQ : ∀ r s, OkP P r → OkP P s → OkP P (liftOp (fun x y => .ok (op x y)) r s) := by
    rintro _ _ ⟨v, rfl, hv⟩ ⟨w, rfl, hw⟩
    exact ⟨op v w, rfl, hcl v w hv hw⟩
  have hasQ : ∀ r s t, OkP P r → OkP P s → OkP P t →
      liftOp (fun x y => .ok (op x y)) (liftOp (fun x y => .ok (op x y)) r s) t =
        liftOp (fun x y => .ok (op x y)) r (liftOp (fun x y => .ok (op x y)) s t) := by
    rintro _ _ _ ⟨u, rfl, hu⟩ ⟨v, rfl, hv⟩ ⟨w, rfl, hw⟩
    exact congrArg (Except.ok (ε := Err)) (has u v w hu hv hw)
  rw [mrImpl_foldlP _ _ blk (OkP P) hclQ hasQ (rest.length + 1) a rest (Nat.lt_succ_self _)
    ⟨a, rfl, ha⟩ (fun z hz => ⟨z, rfl, hr z hz⟩)]
  exact foldl_lift op rest a

private theorem mapreduceArr_P (op : Val → Val → Val) (P : Val → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (has : ∀ a b c, P a → P b → P c → op (op a b) c = op a (op b c))
    (e : R Val) (a : Val) (rest : List Val) (ha : P a) (hr : ∀ z ∈ rest, P z) :
    mapreduceArr id op id e 1024 (a :: rest) = .ok (rest.foldl op a) := by
  cases rest with
  | nil => rfl
  | cons b rest' =>
    simp only [mapreduceArr]
    split
    · rfl
    · exact congrArg (Except.ok (ε := Err))
        (mrImpl_foldlP id op 1024 P hcl has _ a _ (Nat.lt_succ_self _) ha hr)

/-! ### Matrices -/

private theorem mem_col {A : Mat Val} {j : Nat} {x : Val} (h : x ∈ A.col j) : x ∈ A.data :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

private theorem mem_row (A : Mat Val) (hwf : A.data.length = A.m * A.n) {k : Nat} (hk : k < A.m) {x : Val}
    (h : x ∈ A.row k) : x ∈ A.data := by
  unfold Mat.row at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  exact getD_mem _ (by rw [hwf]; exact idx_lt hk (List.mem_range.1 hj))

private theorem col_length (A : Mat Val) (hwf : A.data.length = A.m * A.n) {j : Nat} (hj : j < A.n) :
    (A.col j).length = A.m := by
  have := Nat.mul_le_mul_left A.m (show j + 1 ≤ A.n by omega)
  rw [Nat.mul_add, Nat.mul_one] at this
  simp only [Mat.col, List.length_take, List.length_drop, hwf]; omega

private theorem col_cons (A : Mat Val) (hwf : A.data.length = A.m * A.n) {k : Nat} (hk : k < A.n) (hm : 0 < A.m) :
    ∃ rest, A.data.drop (k * A.m) = A.data.getD (A.m * k) .missing :: rest ∧
      A.col k = A.data.getD (A.m * k) .missing :: rest.take (A.m - 1) := by
  have hlt : A.m * k < A.data.length := by
    have := idx_lt hm hk
    rw [hwf]; omega
  have hdr0 : A.data.drop (A.m * k) =
      A.data.getD (A.m * k) .missing :: A.data.drop (A.m * k + 1) := by
    rw [getD_eq _ hlt]; exact List.drop_eq_getElem_cons hlt
  refine ⟨_, by rw [Nat.mul_comm k A.m]; exact hdr0, ?_⟩
  unfold Mat.col
  rw [hdr0, take_cons_pos hm]

private theorem row_cons (A : Mat Val) (k : Nat) (hn : 0 < A.n) :
    ∃ rest, A.row k = A.data.getD k .missing :: rest := by
  obtain ⟨n', hn'⟩ : ∃ n', A.n = n' + 1 := ⟨A.n - 1, by omega⟩
  unfold Mat.row
  rw [hn', List.range_succ_eq_map]
  simp only [List.map_cons, Nat.mul_zero, Nat.add_zero]
  exact ⟨_, rfl⟩

private theorem getD_mem_col0 (A : Mat Val) (hwf : A.data.length = A.m * A.n) {k : Nat} (hk : k < A.m)
    (hn : 0 < A.n) : A.data.getD k .missing ∈ A.col 0 := by
  have hlt : k < A.data.length := by
    have := idx_lt hk hn
    rw [hwf]; omega
  have hc0 : A.col 0 = A.data.take A.m := by simp [Mat.col]
  rw [hc0, getD_eq _ hlt]
  exact List.mem_iff_getElem.2 ⟨k, by simp only [List.length_take]; omega, by simp⟩

private theorem getD_mem_row0 (A : Mat Val) {k : Nat} (hk : k < A.n) :
    A.data.getD (A.m * k) .missing ∈ A.row 0 := by
  unfold Mat.row
  refine List.mem_map.2 ⟨k, List.mem_range.2 hk, ?_⟩
  show A.data.getD (0 + A.m * k) default = _
  rw [Nat.zero_add]; rfl

private theorem row0_m1 (A : Mat Val) (hwf : A.data.length = A.m * A.n) (hm : A.m = 1) : A.row 0 = A.data := by
  apply List.ext_getElem
  · simp [Mat.row, hwf, hm]
  · intro i h1 h2
    simp only [Mat.row, List.getElem_map, List.getElem_range, hm, Nat.zero_add, Nat.one_mul]
    exact getD_eq _ h2

private theorem col_getElem (A : Mat Val) (hwf : A.data.length = A.m * A.n) {i j : Nat} (hi : i < A.m) (hj : j < A.n)
    (h : i < (A.col j).length) : (A.col j)[i] = A.data.getD (i + A.m * j) .missing := by
  have hlt : i + A.m * j < A.data.length := by rw [hwf]; exact idx_lt hi hj
  rw [getD_eq _ hlt]
  simp only [Mat.col, List.getElem_take, List.getElem_drop]
  congr 1; omega

/-! ### `_mapreducedim!` with an operation associative on a closed subset -/

private theorem get_step (Rr : Arr) (T U : Nat → Val) {N k : Nat} (hk : k < N) :
    Arr.get { Rr with data := (List.range N).map fun j => if j < k then T j else U j } k = U k := by
  simp only [Arr.get]; rw [getD_step _ _ _ hk]

private theorem get_single (Rr : Arr) (x : Val) : Arr.get { Rr with data := [x] } 0 = x := rfl

private theorem store_single (Rr : Arr) (x y : Val) (hc : Rr.ty.convert y = .ok y) :
    Arr.store { Rr with data := [x] } 0 y = .ok { Rr with data := [y] } := by
  simp only [Arr.store, hc, ok_bind, pure_eq] <;> rfl

private theorem mrd_fast (op : Val → Val → Val) (P : Val → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (has : ∀ a b c, P a → P b → P c → op (op a b) c = op a (op b c))
    (Rr : Arr) (A : Mat Val) (d N : Nat) (v0 : Val) (S : Nat → List Val)
    (hconv : ∀ v, P v → Rr.ty.convert v = .ok v) (hv0 : P v0)
    (hpos : A.m * A.n ≠ 0) (hls : lsiz A.m A.n d > 16) (hdata : Rr.data = List.replicate N v0)
    (hblk : ∀ k < N, ∃ a rest, A.data.drop (k * lsiz A.m A.n d) = a :: rest ∧
      a :: rest.take (lsiz A.m A.n d - 1) = S k ∧ ∀ x ∈ S k, P x) :
    mapreducedim (fun x => .ok x) (fun x y => .ok (op x y)) 1024 Rr A d =
      .ok { Rr with data := (List.range N).map fun k => (S k).foldl op v0 } := by
  unfold mapreducedim
  rw [if_neg hpos]
  dsimp only
  rw [if_pos hls, hdata, List.length_replicate]
  refine range_foldlM (fun k' => { Rr with data := ((List.range N).map fun k =>
    if k < k' then (S k).foldl op v0 else v0) }) ?_ ?_ ?_
  · rcases Rr with ⟨ty, rm, rn, data⟩
    simp only at hdata
    subst hdata
    simp only [Nat.not_lt_zero, ↓reduceIte, map_range_const]
  · try dsimp only
    rw [range_full]
  · intro k hk
    obtain ⟨a, rest, hdr, hsk, hP⟩ := hblk k hk
    have haP : P a := hP a (by rw [← hsk]; simp)
    have hrP : ∀ z ∈ rest.take (lsiz A.m A.n d - 1), P z :=
      fun z hz => hP z (by rw [← hsk]; simp [hz])
    have hTP : P ((S k).foldl op v0) := foldl_mem op P hcl _ _ hv0 hP
    have hval : op v0 ((rest.take (lsiz A.m A.n d - 1)).foldl op a) = (S k).foldl op v0 := by
      rw [← hsk, List.foldl_cons, foldl_assoc op P hcl has _ _ _ hv0 haP hrP]
    simp only [hdr]
    rw [fast_block op P hcl has 1024 a _ haP hrP]
    simp only [ok_bind, get_step _ _ _ hk, hval, Arr.store, hconv _ hTP, pure_eq]
    rw [set_range_step (fun k => (S k).foldl op v0) (fun _ => v0) N k hk]

private theorem mrd_cols (op : Val → Val → Val) (P : Val → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (Rr : Arr) (A : Mat Val) (d : Nat) (v0 : Val)
    (hconv : ∀ v, P v → Rr.ty.convert v = .ok v) (hv0 : P v0) (hA : ∀ x ∈ A.data, P x)
    (hpos : A.m * A.n ≠ 0) (hls : ¬ lsiz A.m A.n d > 16) (hRm : Rr.m = 1) (hRn : Rr.n = A.n)
    (hdata : Rr.data = List.replicate A.n v0) :
    mapreducedim (fun x => .ok x) (fun x y => .ok (op x y)) 1024 Rr A d =
      .ok { Rr with data := (List.range A.n).map fun j => (A.col j).foldl op v0 } := by
  unfold mapreducedim
  rw [if_neg hpos]
  dsimp only
  rw [if_neg hls, if_pos hRm]
  refine range_foldlM (fun k' => { Rr with data := ((List.range A.n).map fun k =>
    if k < k' then (A.col k).foldl op v0 else v0) }) ?_ ?_ ?_
  · rcases Rr with ⟨ty, rm, rn, data⟩
    simp only at hdata
    subst hdata
    simp only [Nat.not_lt_zero, ↓reduceIte, map_range_const]
  · try dsimp only
    rw [range_full]
  · intro j hj
    have hjr : (if Rr.n = 1 then 0 else j) = j := by rw [hRn]; split <;> omega
    have hTP : P ((A.col j).foldl op v0) :=
      foldl_mem op P hcl _ _ hv0 (fun x hx => hA x (mem_col hx))
    simp only [hjr, ok_bind, foldlM_ok, get_step _ _ _ hj, Arr.store, hconv _ hTP, pure_eq]
    rw [set_range_step (fun k => (A.col k).foldl op v0) (fun _ => v0) A.n j hj]

private theorem mrd_one (op : Val → Val → Val) (P : Val → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (Rr : Arr) (A : Mat Val) (d : Nat) (v0 : Val)
    (hconv : ∀ v, P v → Rr.ty.convert v = .ok v) (hv0 : P v0) (hA : ∀ x ∈ A.data, P x)
    (hwf : A.data.length = A.m * A.n) (hpos : A.m * A.n ≠ 0) (hls : ¬ lsiz A.m A.n d > 16)
    (hRm : Rr.m = 1) (hRn : Rr.n = 1) (hm : A.m = 1) (hdata : Rr.data = [v0]) :
    mapreducedim (fun x => .ok x) (fun x y => .ok (op x y)) 1024 Rr A d =
      .ok { Rr with data := [A.data.foldl op v0] } := by
  unfold mapreducedim
  rw [if_neg hpos]
  dsimp only
  rw [if_neg hls, if_pos hRm]
  refine range_foldlM (fun k' => { Rr with data := [(A.data.take k').foldl op v0] }) ?_ ?_ ?_
  · rcases Rr with ⟨ty, rm, rn, data⟩
    simp only at hdata
    subst hdata
    rfl
  · try dsimp only
    rw [List.take_of_length_le (by rw [hwf, hm]; omega)]
  · intro j _
    have hjr : (if Rr.n = 1 then 0 else j) = 0 := by rw [hRn]; rfl
    have hcol : A.col j = (A.data.drop j).take 1 := by simp [Mat.col, hm]
    have htake : A.data.take (j + 1) = A.data.take j ++ A.col j := by rw [hcol, List.take_add]
    have hTP : P ((A.data.take (j + 1)).foldl op v0) :=
      foldl_mem op P hcl _ _ hv0 (fun x hx => hA x (List.mem_of_mem_take hx))
    simp only [hjr, ok_bind, foldlM_ok, get_single]
    rw [← List.foldl_append, ← htake, store_single Rr _ _ (hconv _ hTP)]

/-- The rows of a matrix truncated to their first `j'` entries. -/
private def rowp (A : Mat Val) (i j' : Nat) : List Val :=
  (List.range j').map fun j => A.data.getD (i + A.m * j) .missing

private theorem mrd_rows (op : Val → Val → Val) (P : Val → Prop)
    (hcl : ∀ a b, P a → P b → P (op a b))
    (Rr : Arr) (A : Mat Val) (d : Nat) (v0 : Val)
    (hconv : ∀ v, P v → Rr.ty.convert v = .ok v) (hv0 : P v0) (hA : ∀ x ∈ A.data, P x)
    (hwf : A.data.length = A.m * A.n) (hpos : A.m * A.n ≠ 0) (hls : ¬ lsiz A.m A.n d > 16)
    (hRm : Rr.m ≠ 1) (hRn : Rr.n = 1) (hdata : Rr.data = List.replicate A.m v0) :
    mapreducedim (fun x => .ok x) (fun x y => .ok (op x y)) 1024 Rr A d =
      .ok { Rr with data := (List.range A.m).map fun i => (A.row i).foldl op v0 } := by
  unfold mapreducedim
  rw [if_neg hpos]
  dsimp only
  rw [if_neg hls, if_neg hRm]
  refine range_foldlM (fun j' => { Rr with data := ((List.range A.m).map fun i =>
    (rowp A i j').foldl op v0) }) ?_ ?_ ?_
  · rcases Rr with ⟨ty, rm, rn, data⟩
    simp only at hdata
    subst hdata
    simp only [rowp, List.range_zero, List.map_nil, List.foldl_nil, map_range_const]
  · rfl
  · intro j hj
    have hjr : (if Rr.n = 1 then 0 else j) = 0 := by rw [hRn]; rfl
    simp only [hjr]
    refine range_foldlM (fun i' => { Rr with data := ((List.range A.m).map fun i =>
      if i < i' then (rowp A i (j + 1)).foldl op v0 else (rowp A i j).foldl op v0) }) ?_ ?_ ?_
    · simp only [Nat.not_lt_zero, ↓reduceIte]
    · try dsimp only
      rw [range_full]
    · intro i hi
      have hrow : rowp A i (j + 1) = rowp A i j ++ [A.data.getD (i + A.m * j) .missing] := by
        simp only [rowp, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      have hval : op ((rowp A i j).foldl op v0) (A.data.getD (i + A.m * j) .missing) =
          (rowp A i (j + 1)).foldl op v0 := by
        rw [hrow, List.foldl_append]; rfl
      have hTP : P ((rowp A i (j + 1)).foldl op v0) := by
        refine foldl_mem op P hcl _ _ hv0 (fun x hx => ?_)
        unfold rowp at hx
        obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hx
        have hj'' : j' < A.n := by have := List.mem_range.1 hj'; omega
        exact hA _ (getD_mem _ (by rw [hwf]; exact idx_lt hi hj''))
      simp only [Nat.mul_zero, Nat.add_zero, ok_bind, get_step _ _ _ hi, hval, Arr.store,
        hconv _ hTP, pure_eq]
      rw [set_range_step (fun k => (rowp A k (j + 1)).foldl op v0)
        (fun k => (rowp A k j).foldl op v0) A.m i hi]

/-! ### `maximum`/`minimum` on `Int64` -/

/-- An `Int64` value. -/
private def IsI64 (v : Val) : Prop := ∃ y, v = .int .i64 y

private theorem rem_i64 (x : JInt .i64) : JInt.rem .i64 x = x :=
  Subtype.ext (wrapInt_of_inRange _ _ x.property)

private theorem vmax_ii (x y : JInt .i64) :
    Val.vmax (.int .i64 x) (.int .i64 y) = .int .i64 (if y.val < x.val then x else y) := by
  show Val.int .i64 (if (JInt.rem .i64 y).val < (JInt.rem .i64 x).val then JInt.rem .i64 x
    else JInt.rem .i64 y) = _
  rw [rem_i64, rem_i64]

private theorem vmin_ii (x y : JInt .i64) :
    Val.vmin (.int .i64 x) (.int .i64 y) = .int .i64 (if y.val < x.val then y else x) := by
  show Val.int .i64 (if (JInt.rem .i64 y).val < (JInt.rem .i64 x).val then JInt.rem .i64 y
    else JInt.rem .i64 x) = _
  rw [rem_i64, rem_i64]

private theorem vmax_cl (a b : Val) (ha : IsI64 a) (hb : IsI64 b) : IsI64 (Val.vmax a b) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb
  exact ⟨_, vmax_ii x y⟩

private theorem vmin_cl (a b : Val) (ha : IsI64 a) (hb : IsI64 b) : IsI64 (Val.vmin a b) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb
  exact ⟨_, vmin_ii x y⟩

private theorem mop_cl (isMax : Bool) (a b : Val) (ha : IsI64 a) (hb : IsI64 b) :
    IsI64 ((if isMax then Val.vmax else Val.vmin) a b) := by
  cases isMax
  · exact vmin_cl a b ha hb
  · exact vmax_cl a b ha hb

private theorem mop'_cl (isMax : Bool) (a b : Val) (ha : IsI64 a) (hb : IsI64 b) :
    IsI64 ((if isMax then Val.vmin else Val.vmax) a b) := by
  cases isMax
  · exact vmax_cl a b ha hb
  · exact vmin_cl a b ha hb

private theorem mop_assoc (isMax : Bool) (a b c : Val) (ha : IsI64 a) (hb : IsI64 b)
    (hc : IsI64 c) :
    (if isMax then Val.vmax else Val.vmin) ((if isMax then Val.vmax else Val.vmin) a b) c =
      (if isMax then Val.vmax else Val.vmin) a ((if isMax then Val.vmax else Val.vmin) b c) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; obtain ⟨z, rfl⟩ := hc
  cases isMax <;> simp only [Bool.false_eq_true, ↓reduceIte, vmax_ii, vmin_ii] <;>
    apply congrArg (Val.int .i64) <;>
    by_cases h1 : y.val < x.val <;> by_cases h2 : z.val < y.val <;>
    by_cases h3 : z.val < x.val <;> simp [h1, h2, h3] <;> (try apply Subtype.ext) <;> omega

private theorem foldl_vmin_le : ∀ (l : List Val) (v : Val), IsI64 v → (∀ z ∈ l, IsI64 z) →
    ∀ c ∈ v :: l, (l.foldl Val.vmin v).intVal ≤ c.intVal
  | [], v, _, _, c, hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; exact Int.le_refl _
  | z :: l, v, hv, hl, c, hc => by
    have hz : IsI64 z := hl z (by simp)
    have hl' : ∀ w ∈ l, IsI64 w := fun w hw => hl w (by simp [hw])
    have ih := foldl_vmin_le l (Val.vmin v z) (vmin_cl v z hv hz) hl'
    obtain ⟨x, rfl⟩ := hv; obtain ⟨y, rfl⟩ := hz
    have hmin : (Val.vmin (.int .i64 x) (.int .i64 y)).intVal ≤ (Val.int .i64 x).intVal ∧
        (Val.vmin (.int .i64 x) (.int .i64 y)).intVal ≤ (Val.int .i64 y).intVal := by
      rw [vmin_ii]
      show (if y.val < x.val then y else x).val ≤ x.val ∧ (if y.val < x.val then y else x).val ≤ y.val
      split <;> omega
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hc with rfl | hc'
    · exact Int.le_trans (ih _ (by simp)) hmin.1
    · rcases List.mem_cons.1 hc' with rfl | hc''
      · exact Int.le_trans (ih _ (by simp)) hmin.2
      · exact ih c (by simp [hc''])

private theorem foldl_vmax_ge : ∀ (l : List Val) (v : Val), IsI64 v → (∀ z ∈ l, IsI64 z) →
    ∀ c ∈ v :: l, c.intVal ≤ (l.foldl Val.vmax v).intVal
  | [], v, _, _, c, hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; exact Int.le_refl _
  | z :: l, v, hv, hl, c, hc => by
    have hz : IsI64 z := hl z (by simp)
    have hl' : ∀ w ∈ l, IsI64 w := fun w hw => hl w (by simp [hw])
    have ih := foldl_vmax_ge l (Val.vmax v z) (vmax_cl v z hv hz) hl'
    obtain ⟨x, rfl⟩ := hv; obtain ⟨y, rfl⟩ := hz
    have hmax : (Val.int .i64 x).intVal ≤ (Val.vmax (.int .i64 x) (.int .i64 y)).intVal ∧
        (Val.int .i64 y).intVal ≤ (Val.vmax (.int .i64 x) (.int .i64 y)).intVal := by
      rw [vmax_ii]
      show x.val ≤ (if y.val < x.val then x else y).val ∧ y.val ≤ (if y.val < x.val then x else y).val
      split <;> omega
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hc with rfl | hc'
    · exact Int.le_trans hmax.1 (ih _ (by simp))
    · rcases List.mem_cons.1 hc' with rfl | hc''
      · exact Int.le_trans hmax.2 (ih _ (by simp))
      · exact ih c (by simp [hc''])

/-- The initial value `v0` (the opposite extremum of the first slice) is absorbed by every
element of the first slice. -/
private theorem absorb (isMax : Bool) (s : Val) (rest : List Val) (hs : IsI64 s)
    (hr : ∀ z ∈ rest, IsI64 z) (c : Val) (hc : c ∈ s :: rest) :
    (if isMax then Val.vmax else Val.vmin) (rest.foldl (if isMax then Val.vmin else Val.vmax) s) c
      = c := by
  have hcP : IsI64 c := by
    rcases List.mem_cons.1 hc with rfl | h
    · exact hs
    · exact hr _ h
  obtain ⟨y, rfl⟩ := hcP
  cases isMax
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hle := foldl_vmax_ge rest s hs hr _ hc
    obtain ⟨x, hx⟩ := foldl_mem Val.vmax IsI64 vmax_cl rest s hs hr
    rw [hx] at hle ⊢
    simp only [Val.intVal] at hle
    rw [vmin_ii]
    by_cases h : y.val < x.val
    · rw [if_pos h]
    · rw [if_neg h]
      exact congrArg (Val.int .i64) (Subtype.ext (by omega))
  · simp only [↓reduceIte]
    have hle := foldl_vmin_le rest s hs hr _ hc
    obtain ⟨x, hx⟩ := foldl_mem Val.vmin IsI64 vmin_cl rest s hs hr
    rw [hx] at hle ⊢
    simp only [Val.intVal] at hle
    rw [vmax_ii, if_neg (by omega)]

private theorem conv_i64 (v : Val) (h : IsI64 v) : Ty.convert (.int .i64) v = .ok v := by
  obtain ⟨y, rfl⟩ := h
  first
  | rfl
  | simp [Ty.convert, Ty.isa, Val.typeOf]

private theorem foldView_ok (op : Val → Val → Val) (s : Val) (rest : List Val) :
    foldView (fun x => .ok x) op (s :: rest) = .ok (rest.foldl op s) := by
  unfold foldView
  simp only [ok_bind, pure_eq]
  exact foldlM_ok op rest s

private theorem isa_i64 (y : JInt .i64) : Ty.isa (.int .i64 y) (.int .i64) = true := by
  first
  | rfl
  | simp [Ty.isa, Val.typeOf]

private theorem init_spec (isMax : Bool) (A : Mat Val) (d rm rn : Nat) (s : Val) (rest : List Val)
    (hsh : reducedShape A.m A.n d = (rm, rn)) (hne : ¬((d = 1 ∧ A.m = 0) ∨ (d = 2 ∧ A.n = 0)))
    (hfs : firstSlice A d = s :: rest) (hs : IsI64 s) (hr : ∀ z ∈ rest, IsI64 z) :
    initMinMax (fun x => .ok x) isMax (.int .i64) (.int .i64) A d =
      .ok { ty := .int .i64, m := rm, n := rn,
            data := List.replicate (rm * rn) (rest.foldl (if isMax then Val.vmin else Val.vmax) s) } := by
  obtain ⟨y, hy⟩ := foldl_mem _ IsI64 (mop'_cl isMax) rest s hs hr
  have hconv : Ty.convert (.int .i64) (.int .i64 y) = .ok (.int .i64 y) := conv_i64 _ ⟨y, rfl⟩
  have hnan : Val.isnan (.int .i64 y) = false := rfl
  have hun : Val.isunordered (.int .i64 y) = false := rfl
  simp only [initMinMax, initArray, hsh, eq_false hne, ↓reduceIte, hfs, List.cons_ne_nil]
  rw [foldView_ok]
  simp only [ok_bind, hy, hnan, hun, Bool.false_eq_true, ↓reduceIte, isa_i64, hconv, pure_eq]

private theorem promoteUnion_i64 : Ty.promoteUnion (.int .i64) = .int .i64 := rfl

private theorem maxmin_spec (isMax : Bool) (s c : Val) (rest xs : List Val)
    (hs : IsI64 s) (hr : ∀ z ∈ rest, IsI64 z) (hc : IsI64 c) (hxs : ∀ z ∈ xs, IsI64 z)
    (hcm : c ∈ s :: rest) :
    (if isMax then Vec.maximum (c :: xs) else Vec.minimum (c :: xs)) =
      .ok ((c :: xs).foldl (if isMax then Val.vmax else Val.vmin)
        (rest.foldl (if isMax then Val.vmin else Val.vmax) s)) := by
  have hif : (if isMax then Vec.maximum (c :: xs) else Vec.minimum (c :: xs)) =
      mapreduceArr id (if isMax then Val.vmax else Val.vmin) id (.error .argumentError) 1024
        (c :: xs) := by
    cases isMax <;> rfl
  rw [hif, mapreduceArr_P _ IsI64 (mop_cl isMax) (mop_assoc isMax) _ c xs hc hxs,
    List.foldl_cons, absorb isMax s rest hs hr c hcm]

private theorem maxDims1 (A : Mat Val) (isMax : Bool) (hwf : A.data.length = A.m * A.n)
    (hm : 0 < A.m) (hn : 0 < A.n) (hA : ∀ x ∈ A.data, IsI64 x) :
    ∃ Rr, maxminDims (fun x => .ok x) isMax (.int .i64) A 1 = .ok Rr ∧
      (Rr.m, Rr.n) = reducedShape A.m A.n 1 ∧ Rr.data.length = Rr.m * Rr.n ∧
      ∀ k < Rr.data.length,
        (if isMax then Vec.maximum (A.slice 1 k) else Vec.minimum (A.slice 1 k)) = .ok (Rr.get k) := by
  have hpos : A.m * A.n ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.mul_pos hm hn)
  obtain ⟨s, rest, hrow⟩ : ∃ s rest, A.row 0 = s :: rest := by
    cases h : A.row 0 with
    | nil => have := congrArg List.length h; simp [Mat.row] at this <;> omega
    | cons s rest => exact ⟨s, rest, rfl⟩
  have hsr : ∀ z ∈ s :: rest, IsI64 z :=
    fun z hz => hA z (mem_row A hwf hm (by rw [hrow]; exact hz))
  have hs : IsI64 s := hsr s (by simp)
  have hr : ∀ z ∈ rest, IsI64 z := fun z hz => hsr z (by simp [hz])
  have hfs : firstSlice A 1 = s :: rest := by
    have hm0 : ¬ A.m = 0 := by omega
    show (if A.m = 0 then [] else A.row 0) = _
    rw [if_neg hm0, hrow]
  have hinit := init_spec isMax A 1 1 A.n s rest rfl (by omega) hfs hs hr
  have hv0P : IsI64 (rest.foldl (if isMax then Val.vmin else Val.vmax) s) :=
    foldl_mem _ IsI64 (mop'_cl isMax) rest s hs hr
  generalize hv0 : rest.foldl (if isMax then Val.vmin else Val.vmax) s = v0 at hinit hv0P
  have hls1 : lsiz A.m A.n 1 = if A.m > 1 then A.m else 1 := rfl
  have hres : mapreducedim (fun x => .ok x)
      (fun x y => .ok ((if isMax then Val.vmax else Val.vmin) x y)) 1024
      { ty := .int .i64, m := 1, n := A.n, data := List.replicate (1 * A.n) v0 } A 1 =
      .ok { ty := .int .i64, m := 1, n := A.n, data := ((List.range A.n).map fun k =>
        (A.col k).foldl (if isMax then Val.vmax else Val.vmin) v0) } := by
    by_cases h16 : 16 < A.m
    · have hm1 : A.m > 1 := by omega
      have hl : lsiz A.m A.n 1 = A.m := by rw [hls1, if_pos hm1]
      have hblk : ∀ k < A.n, ∃ a rest, A.data.drop (k * lsiz A.m A.n 1) = a :: rest ∧
          a :: rest.take (lsiz A.m A.n 1 - 1) = A.col k ∧ ∀ x ∈ A.col k, IsI64 x := by
        intro k hk
        obtain ⟨rest0, hdr, hck⟩ := col_cons A hwf hk hm
        exact ⟨_, _, by rw [hl]; exact hdr, by rw [hl]; exact hck.symm,
          fun x hx => hA x (mem_col hx)⟩
      exact mrd_fast (if isMax then Val.vmax else Val.vmin) IsI64 (mop_cl isMax)
        (mop_assoc isMax) { ty := .int .i64, m := 1, n := A.n, data := List.replicate (1 * A.n) v0 }
        A 1 A.n v0 A.col conv_i64 hv0P hpos (by rw [hl]; exact h16) (by simp) hblk
    · exact mrd_cols (if isMax then Val.vmax else Val.vmin) IsI64 (mop_cl isMax)
        { ty := .int .i64, m := 1, n := A.n, data := List.replicate (1 * A.n) v0 } A 1 v0
        conv_i64 hv0P hA hpos (by rw [hls1]; split <;> omega) rfl rfl (by simp)
  refine ⟨{ ty := .int .i64, m := 1, n := A.n, data := ((List.range A.n).map fun k =>
      (A.col k).foldl (if isMax then Val.vmax else Val.vmin) v0) }, ?_, rfl, by simp, ?_⟩
  · unfold maxminDims
    rw [promoteUnion_i64, hinit, ok_bind]
    exact hres
  · intro k hk
    simp only [List.length_map, List.length_range] at hk
    obtain ⟨rest0, -, hck⟩ := col_cons A hwf hk hm
    have hcm : A.data.getD (A.m * k) .missing ∈ s :: rest := by
      rw [← hrow]; exact getD_mem_row0 A hk
    have hcol : ∀ x ∈ A.col k, IsI64 x := fun x hx => hA x (mem_col hx)
    rw [hck] at hcol
    show _ = Except.ok (((List.range A.n).map fun k =>
      (A.col k).foldl (if isMax then Val.vmax else Val.vmin) v0).getD k .missing)
    rw [getD_map_range _ _ hk, show A.slice 1 k = A.col k from rfl, hck, ← hv0]
    exact maxmin_spec isMax s (A.data.getD (A.m * k) .missing) rest (rest0.take (A.m - 1)) hs hr
      (hcol _ (by simp)) (fun z hz => hcol z (by simp [hz])) hcm

private theorem maxDims2 (A : Mat Val) (isMax : Bool) (hwf : A.data.length = A.m * A.n)
    (hm : 0 < A.m) (hn : 0 < A.n) (hA : ∀ x ∈ A.data, IsI64 x) :
    ∃ Rr, maxminDims (fun x => .ok x) isMax (.int .i64) A 2 = .ok Rr ∧
      (Rr.m, Rr.n) = reducedShape A.m A.n 2 ∧ Rr.data.length = Rr.m * Rr.n ∧
      ∀ k < Rr.data.length,
        (if isMax then Vec.maximum (A.slice 2 k) else Vec.minimum (A.slice 2 k)) = .ok (Rr.get k) := by
  have hpos : A.m * A.n ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.mul_pos hm hn)
  obtain ⟨s, rest, hc0⟩ : ∃ s rest, A.col 0 = s :: rest := by
    cases h : A.col 0 with
    | nil =>
      have := congrArg List.length h
      rw [col_length A hwf hn] at this; simp at this; omega
    | cons s rest => exact ⟨s, rest, rfl⟩
  have hsr : ∀ z ∈ s :: rest, IsI64 z :=
    fun z hz => hA z (mem_col (j := 0) (by rw [hc0]; exact hz))
  have hs : IsI64 s := hsr s (by simp)
  have hr : ∀ z ∈ rest, IsI64 z := fun z hz => hsr z (by simp [hz])
  have hfs : firstSlice A 2 = s :: rest := by
    have hn0 : ¬ A.n = 0 := by omega
    show (if A.n = 0 then [] else A.col 0) = _
    rw [if_neg hn0, hc0]
  have hinit := init_spec isMax A 2 A.m 1 s rest rfl (by omega) hfs hs hr
  have hv0P : IsI64 (rest.foldl (if isMax then Val.vmin else Val.vmax) s) :=
    foldl_mem _ IsI64 (mop'_cl isMax) rest s hs hr
  generalize hv0 : rest.foldl (if isMax then Val.vmin else Val.vmax) s = v0 at hinit hv0P
  have hls2 : lsiz A.m A.n 2 =
      if A.m = 1 then (if A.n > 1 then A.n else 1) else if A.n > 1 then 0 else 1 := rfl
  have hres : mapreducedim (fun x => .ok x)
      (fun x y => .ok ((if isMax then Val.vmax else Val.vmin) x y)) 1024
      { ty := .int .i64, m := A.m, n := 1, data := List.replicate (A.m * 1) v0 } A 2 =
      .ok { ty := .int .i64, m := A.m, n := 1, data := ((List.range A.m).map fun k =>
        (A.row k).foldl (if isMax then Val.vmax else Val.vmin) v0) } := by
    by_cases hm1 : A.m = 1
    · by_cases h16 : 16 < A.n
      · have hn1 : A.n > 1 := by omega
        have hl : lsiz A.m A.n 2 = A.n := by rw [hls2, if_pos hm1, if_pos hn1]
        have hblk : ∀ k < A.m, ∃ a rest, A.data.drop (k * lsiz A.m A.n 2) = a :: rest ∧
            a :: rest.take (lsiz A.m A.n 2 - 1) = A.row k ∧ ∀ x ∈ A.row k, IsI64 x := by
          intro k hk
          have hk0 : k = 0 := by omega
          subst hk0
          obtain ⟨a, rest1, hdat⟩ : ∃ a rest1, A.data = a :: rest1 := by
            cases h : A.data with
            | nil => rw [h] at hwf; simp at hwf; omega
            | cons a rest1 => exact ⟨a, rest1, rfl⟩
          have hlen : rest1.length = A.n - 1 := by
            have := hwf; rw [hdat, hm1] at this; simp at this; omega
          refine ⟨a, rest1, by rw [Nat.zero_mul, List.drop_zero, hdat], ?_,
            fun x hx => hA x (mem_row A hwf hk hx)⟩
          rw [hl, row0_m1 A hwf hm1, hdat, List.take_of_length_le (by omega)]
        exact mrd_fast (if isMax then Val.vmax else Val.vmin) IsI64 (mop_cl isMax)
          (mop_assoc isMax) { ty := .int .i64, m := A.m, n := 1, data := List.replicate (A.m * 1) v0 }
          A 2 A.m v0 A.row conv_i64 hv0P hpos (by rw [hl]; exact h16) (by simp) hblk
      · refine (mrd_one (if isMax then Val.vmax else Val.vmin) IsI64 (mop_cl isMax)
          { ty := .int .i64, m := A.m, n := 1, data := List.replicate (A.m * 1) v0 } A 2 v0
          conv_i64 hv0P hA hwf hpos (by rw [hls2, if_pos hm1]; split <;> omega) hm1 rfl hm1
          (by simp [hm1])).trans ?_
        have hr1 : List.range A.m = [0] := by rw [hm1]; rfl
        rw [hr1]
        simp only [List.map_cons, List.map_nil, row0_m1 A hwf hm1]
    · exact mrd_rows (if isMax then Val.vmax else Val.vmin) IsI64 (mop_cl isMax)
        { ty := .int .i64, m := A.m, n := 1, data := List.replicate (A.m * 1) v0 } A 2 v0
        conv_i64 hv0P hA hwf hpos (by rw [hls2, if_neg hm1]; split <;> omega) hm1 rfl (by simp)
  refine ⟨{ ty := .int .i64, m := A.m, n := 1, data := ((List.range A.m).map fun k =>
      (A.row k).foldl (if isMax then Val.vmax else Val.vmin) v0) }, ?_, rfl, by simp, ?_⟩
  · unfold maxminDims
    rw [promoteUnion_i64, hinit, ok_bind]
    exact hres
  · intro k hk
    simp only [List.length_map, List.length_range] at hk
    obtain ⟨xs, hrk⟩ := row_cons A k hn
    have hcm : A.data.getD k .missing ∈ s :: rest := by
      rw [← hc0]; exact getD_mem_col0 A hwf hk hn
    have hrw : ∀ x ∈ A.row k, IsI64 x := fun x hx => hA x (mem_row A hwf hk hx)
    rw [hrk] at hrw
    show _ = Except.ok (((List.range A.m).map fun k =>
      (A.row k).foldl (if isMax then Val.vmax else Val.vmin) v0).getD k .missing)
    rw [getD_map_range _ _ hk, show A.slice 2 k = A.row k from rfl, hrk, ← hv0]
    exact maxmin_spec isMax s (A.data.getD k .missing) rest xs hs hr
      (hrw _ (by simp)) (fun z hz => hrw z (by simp [hz])) hcm

theorem maxDimsInt_proven : MaxDimsInt := by
  intro A d isMax hwf hd hm hn hA
  have hwf : A.data.length = A.m * A.n := hwf
  rcases hd with rfl | rfl
  · exact maxDims1 A isMax hwf hm hn hA
  · exact maxDims2 A isMax hwf hm hn hA

/-! ### `findmax`/`findmin` on `Float64` -/

/-- One step of `findminmax!` on a slice cell: the `(0, 0)` sentinel or `op(value, x)`
replaces the cell by `x` and its index `e p`. -/
private def fstep (op : Val → Val → Bool) (e : Nat → Nat × Nat) (acc : Val × (Nat × Nat))
    (x : Val × Nat) : Val × (Nat × Nat) :=
  if acc.2 = (0, 0) ∨ op acc.1 x.1 = true then (x.1, e x.2) else acc

private theorem find_fold_aux (op : Val → Val → Bool) (e : Nat → Nat × Nat)
    (he : ∀ p, 1 ≤ p → e p ≠ (0, 0)) :
    ∀ (xs : List Val) (s : Nat) (w : Val) (p : Nat), 1 ≤ s → 1 ≤ p →
      (xs.zipIdx s).foldl (fstep op e) (w, e p) =
        (((xs.zipIdx s).foldl (fun (a b : Val × Nat) => if op a.1 b.1 then b else a) (w, p)).1,
          e ((xs.zipIdx s).foldl (fun (a b : Val × Nat) => if op a.1 b.1 then b else a) (w, p)).2)
  | [], _, _, _, _, _ => rfl
  | x :: xs, s, w, p, hs, hp => by
    simp only [List.zipIdx_cons, List.foldl_cons]
    by_cases hop : op w x = true
    · have h1 : fstep op e (w, e p) (x, s) = (x, e s) := by simp [fstep, hop]
      rw [h1, if_pos hop]
      exact find_fold_aux op e he xs (s + 1) x s (by omega) hs
    · have h2 : fstep op e (w, e p) (x, s) = (w, e p) := by simp [fstep, hop, he p hp]
      rw [h2, if_neg hop]
      exact find_fold_aux op e he xs (s + 1) w p (by omega) hp

private theorem find_fold (op : Val → Val → Bool) (e : Nat → Nat × Nat)
    (he : ∀ p, 1 ≤ p → e p ≠ (0, 0)) (x0 : Val) (xs : List Val) (w : Val) :
    ((x0 :: xs).zipIdx 1).foldl (fstep op e) (w, (0, 0)) =
      (((xs.zipIdx 2).foldl (fun (a b : Val × Nat) => if op a.1 b.1 then b else a) (x0, 1)).1,
        e ((xs.zipIdx 2).foldl (fun (a b : Val × Nat) => if op a.1 b.1 then b else a) (x0, 1)).2) := by
  have h1 : fstep op e (w, (0, 0)) (x0, 1) = (x0, e 1) := by simp [fstep]
  simp only [List.zipIdx_cons, List.foldl_cons, h1]
  exact find_fold_aux op e he xs 2 x0 1 (by omega) (by omega)

/-- The order of `findmax` (`isless`) or `findmin` (`isgreater`). -/
private def fop (isMax : Bool) : Val → Val → Bool := if isMax then Val.visless else Vec.isgreater

private theorem vec_find_eq (isMax : Bool) (x0 : Val) (xs : List Val) :
    (if isMax then Vec.findmax (x0 :: xs) else Vec.findmin (x0 :: xs)) =
      .ok ((xs.zipIdx 2).foldl (fun (a b : Val × Nat) => if fop isMax a.1 b.1 then b else a)
        (x0, 1)) := by
  cases isMax <;> rfl

private theorem fstep_P (op : Val → Val → Bool) (e : Nat → Nat × Nat) (P : Val → Prop) :
    ∀ (zs : List (Val × Nat)) (st : Val × (Nat × Nat)), P st.1 → (∀ z ∈ zs, P z.1) →
      P (zs.foldl (fstep op e) st).1
  | [], _, h, _ => h
  | z :: zs, st, h, hz => by
    refine fstep_P op e P zs _ ?_ (fun w hw => hz w (by simp [hw]))
    unfold fstep
    split
    · exact hz z (by simp)
    · exact h

private theorem zipIdx_P (P : Val → Prop) :
    ∀ (l : List Val) (s : Nat), (∀ x ∈ l, P x) → ∀ z ∈ l.zipIdx s, P z.1
  | [], _, _, _, hz => by simp at hz
  | x :: l, s, h, z, hz => by
    simp only [List.zipIdx_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact h x (by simp)
    · exact zipIdx_P P l (s + 1) (fun y hy => h y (by simp [hy])) z hz

/-- The cell of column `k` after `findminmax!` over the column. -/
private def colC (op : Val → Val → Bool) (A : Mat Val) (fA : Val) (k : Nat) :
    Val × (Nat × Nat) :=
  ((A.col k).zipIdx 1).foldl (fstep op fun p => (p, k + 1)) (fA, (0, 0))

/-- The cell of row `i` after `findminmax!` over the first `j'` columns. -/
private def rowE (op : Val → Val → Bool) (A : Mat Val) (fA : Val) (i j' : Nat) :
    Val × (Nat × Nat) :=
  ((List.range j').map fun j => (A.data.getD (i + A.m * j) .missing, j + 1)).foldl
    (fstep op fun p => (i + 1, p)) (fA, (0, 0))

private theorem zip_col (A : Mat Val) (hwf : A.data.length = A.m * A.n) {j : Nat} (hj : j < A.n) :
    (A.col j).zipIdx 1 =
      (List.range A.m).map fun i => (A.data.getD (i + A.m * j) .missing, i + 1) := by
  have hlen := col_length A hwf hj
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  have hi : i < A.m := by simpa using h2
  rw [List.getElem_zipIdx, List.getElem_map, List.getElem_range,
    col_getElem A hwf hi hj (by rw [hlen]; exact hi)]
  exact Prod.ext rfl (Nat.add_comm 1 i)

private theorem zip_row (A : Mat Val) (i : Nat) :
    (A.row i).zipIdx 1 =
      (List.range A.n).map fun j => (A.data.getD (i + A.m * j) .missing, j + 1) := by
  apply List.ext_getElem (by simp [Mat.row])
  intro j h1 h2
  simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range, Mat.row]
  exact Prod.ext rfl (Nat.add_comm 1 j)

private theorem fold_col (op : Val → Val → Bool) (A : Mat Val) (fA : Val)
    (hwf : A.data.length = A.m * A.n) {j : Nat} (hj : j < A.n) :
    (List.range A.m).foldl (fun (acc : Val × (Nat × Nat)) i =>
        if acc.2 = (0, 0) ∨ op acc.1 (A.data.getD (i + A.m * j) .missing) = true then
          (A.data.getD (i + A.m * j) .missing, (i + 1, j + 1)) else acc) (fA, (0, 0)) =
      ((colC op A fA j).1, (colC op A fA j).2) := by
  unfold colC
  rw [zip_col A hwf hj, List.foldl_map] <;> rfl

private theorem rowE_succ (op : Val → Val → Bool) (A : Mat Val) (fA : Val) (i j : Nat) :
    rowE op A fA i (j + 1) =
      fstep op (fun p => (i + 1, p)) (rowE op A fA i j)
        (A.data.getD (i + A.m * j) .missing, j + 1) := by
  simp only [rowE, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem rowE_full (op : Val → Val → Bool) (A : Mat Val) (fA : Val) (i : Nat) :
    rowE op A fA i A.n =
      ((A.row i).zipIdx 1).foldl (fstep op fun p => (i + 1, p)) (fA, (0, 0)) := by
  rw [zip_row] <;> rfl

private theorem rowE_P (op : Val → Val → Bool) (P : Val → Prop) (A : Mat Val) (fA : Val)
    (hwf : A.data.length = A.m * A.n) (hA : ∀ x ∈ A.data, P x) (hfA : P fA) {i j' : Nat}
    (hi : i < A.m) (hj : j' ≤ A.n) : P (rowE op A fA i j').1 := by
  unfold rowE
  refine fstep_P op _ P _ _ hfA (fun z hz => ?_)
  obtain ⟨j, hj', rfl⟩ := List.mem_map.1 hz
  have hj'' : j < A.n := by have := List.mem_range.1 hj'; omega
  exact hA _ (getD_mem _ (by rw [hwf]; exact idx_lt hi hj''))

private theorem fold_one (op : Val → Val → Bool) (A : Mat Val) (fA : Val) (hm1 : A.m = 1)
    (j : Nat) :
    (List.range A.m).foldl (fun (acc : Val × (Nat × Nat)) i =>
        if acc.2 = (0, 0) ∨ op acc.1 (A.data.getD (i + A.m * j) .missing) = true then
          (A.data.getD (i + A.m * j) .missing, (i + 1, j + 1)) else acc)
      ((rowE op A fA 0 j).1, (rowE op A fA 0 j).2) =
    ((rowE op A fA 0 (j + 1)).1, (rowE op A fA 0 (j + 1)).2) := by
  have hr1 : List.range A.m = [0] := by rw [hm1]; rfl
  rw [hr1, rowE_succ]
  simp only [List.foldl_cons, List.foldl_nil, fstep]

private theorem get_single' (Rv : Arr) (x : Val) : Arr.get { Rv with data := [x] } 0 = x := rfl

private theorem getD_single (x d : Nat × Nat) : [x].getD 0 d = x := rfl

private theorem fmm_cols (op : Val → Val → Bool) (P : Val → Prop) (Rv : Arr)
    (Ri : List (Nat × Nat)) (A : Mat Val) (fA : Val)
    (hconv : ∀ v, P v → Rv.ty.convert v = .ok v) (hfA : P fA) (hA : ∀ x ∈ A.data, P x)
    (hwf : A.data.length = A.m * A.n) (hpos : A.m * A.n ≠ 0) (hRm : Rv.m = 1)
    (hRn : Rv.n = A.n) (hdata : Rv.data = List.replicate A.n fA)
    (hRi : Ri = List.replicate A.n (0, 0)) :
    findminmax id op Rv Ri A =
      .ok ⟨{ Rv with data := (List.range A.n).map fun k => (colC op A fA k).1 },
        (List.range A.n).map fun k => (colC op A fA k).2⟩ := by
  subst hRi
  have hn0 : A.n ≠ 0 := fun h => hpos (by rw [h, Nat.mul_zero])
  have hne : ¬(Rv.data.length = 0 ∨ A.m * A.n = 0) := by
    rw [hdata, List.length_replicate]; omega
  unfold findminmax
  rw [if_neg hne, if_pos hRm]
  refine range_foldlM (fun j' => (⟨{ Rv with data := ((List.range A.n).map fun k =>
      if k < j' then (colC op A fA k).1 else fA) },
    (List.range A.n).map fun k => if k < j' then (colC op A fA k).2 else (0, 0)⟩ : FindRes))
    ?_ ?_ ?_
  · rcases Rv with ⟨ty, rm, rn, data⟩
    simp only at hdata
    subst hdata
    simp only [Nat.not_lt_zero, ↓reduceIte, map_range_const]
  · try dsimp only
    rw [range_full, range_full]
  · intro j hj
    have hjr : (if Rv.n = 1 then 0 else j) = j := by rw [hRn]; split <;> omega
    have hcP : P (colC op A fA j).1 := by
      unfold colC
      exact fstep_P op _ P _ _ hfA (zipIdx_P P _ 1 (fun x hx => hA x (mem_col hx)))
    simp only [hjr, id_eq, get_step _ _ _ hj, getD_step _ _ _ hj]
    rw [fold_col op A fA hwf hj]
    simp only [Arr.store, hconv _ hcP, ok_bind, pure_eq]
    rw [set_range_step (fun k => (colC op A fA k).1) (fun _ => fA) A.n j hj,
      set_range_step (fun k => (colC op A fA k).2) (fun _ => ((0 : Nat), (0 : Nat))) A.n j hj]

private theorem fmm_one (op : Val → Val → Bool) (P : Val → Prop) (Rv : Arr)
    (Ri : List (Nat × Nat)) (A : Mat Val) (fA : Val)
    (hconv : ∀ v, P v → Rv.ty.convert v = .ok v) (hfA : P fA) (hA : ∀ x ∈ A.data, P x)
    (hwf : A.data.length = A.m * A.n) (hpos : A.m * A.n ≠ 0) (hRm : Rv.m = 1) (hRn : Rv.n = 1)
    (hm1 : A.m = 1) (hdata : Rv.data = [fA]) (hRi : Ri = [(0, 0)]) :
    findminmax id op Rv Ri A =
      .ok ⟨{ Rv with data := (List.range A.m).map fun i => (rowE op A fA i A.n).1 },
        (List.range A.m).map fun i => (rowE op A fA i A.n).2⟩ := by
  subst hRi
  have hr1 : List.range A.m = [0] := by rw [hm1]; rfl
  have hne : ¬(Rv.data.length = 0 ∨ A.m * A.n = 0) := by
    rw [hdata]; simp only [List.length_cons, List.length_nil]; omega
  unfold findminmax
  rw [if_neg hne, if_pos hRm]
  refine range_foldlM (fun j' => (⟨{ Rv with data := [(rowE op A fA 0 j').1] },
    [(rowE op A fA 0 j').2]⟩ : FindRes)) ?_ ?_ ?_
  · rcases Rv with ⟨ty, rm, rn, data⟩
    simp only at hdata
    subst hdata
    rfl
  · try dsimp only
    rw [hr1] <;> rfl
  · intro j hj
    have hjr : (if Rv.n = 1 then 0 else j) = 0 := by rw [hRn]; rfl
    have hP : P (rowE op A fA 0 (j + 1)).1 :=
      rowE_P op P A fA hwf hA hfA (by omega) (by omega)
    simp only [hjr, id_eq, get_single', getD_single]
    rw [fold_one op A fA hm1 j]
    simp only [store_single Rv _ _ (hconv _ hP), ok_bind, pure_eq] <;> rfl

private theorem fmm_rows (op : Val → Val → Bool) (P : Val → Prop) (Rv : Arr)
    (Ri : List (Nat × Nat)) (A : Mat Val) (fA : Val)
    (hconv : ∀ v, P v → Rv.ty.convert v = .ok v) (hA : ∀ x ∈ A.data, P x)
    (hwf : A.data.length = A.m * A.n) (hpos : A.m * A.n ≠ 0) (hRm : Rv.m ≠ 1) (hRn : Rv.n = 1)
    (hdata : Rv.data = List.replicate A.m fA) (hRi : Ri = List.replicate A.m (0, 0)) :
    findminmax id op Rv Ri A =
      .ok ⟨{ Rv with data := (List.range A.m).map fun i => (rowE op A fA i A.n).1 },
        (List.range A.m).map fun i => (rowE op A fA i A.n).2⟩ := by
  subst hRi
  have hm0 : A.m ≠ 0 := fun h => hpos (by rw [h, Nat.zero_mul])
  have hne : ¬(Rv.data.length = 0 ∨ A.m * A.n = 0) := by
    rw [hdata, List.length_replicate]; omega
  unfold findminmax
  rw [if_neg hne, if_neg hRm]
  refine range_foldlM (fun j' => (⟨{ Rv with data := ((List.range A.m).map fun i =>
      (rowE op A fA i j').1) },
    (List.range A.m).map fun i => (rowE op A fA i j').2⟩ : FindRes)) ?_ ?_ ?_
  · rcases Rv with ⟨ty, rm, rn, data⟩
    simp only at hdata
    subst hdata
    simp only [rowE, List.range_zero, List.map_nil, List.foldl_nil, map_range_const]
  · rfl
  · intro j hj
    have hjr : (if Rv.n = 1 then 0 else j) = 0 := by rw [hRn]; rfl
    simp only [hjr]
    refine range_foldlM (fun i' => (⟨{ Rv with data := ((List.range A.m).map fun i =>
        if i < i' then (rowE op A fA i (j + 1)).1 else (rowE op A fA i j).1) },
      (List.range A.m).map fun i =>
        if i < i' then (rowE op A fA i (j + 1)).2 else (rowE op A fA i j).2⟩ : FindRes))
      ?_ ?_ ?_
    · simp only [Nat.not_lt_zero, ↓reduceIte]
    · try dsimp only
      rw [range_full, range_full]
    · intro i hi
      have hlt : i + A.m * j < A.data.length := by rw [hwf]; exact idx_lt hi hj
      have hP' : P (A.data.getD (i + A.m * j) .missing) := hA _ (getD_mem _ hlt)
      simp only [Nat.mul_zero, Nat.add_zero, id_eq, get_step _ _ _ hi, getD_step _ _ _ hi]
      by_cases hc : (rowE op A fA i j).2 = (0, 0) ∨
          op (rowE op A fA i j).1 (A.data.getD (i + A.m * j) .missing) = true
      · have hE : rowE op A fA i (j + 1) =
            (A.data.getD (i + A.m * j) .missing, (i + 1, j + 1)) := by
          rw [rowE_succ]; unfold fstep; exact if_pos hc
        rw [if_pos hc]
        simp only [Arr.store, hconv _ hP', ok_bind, pure_eq]
        rw [show A.data.getD (i + A.m * j) .missing = (rowE op A fA i (j + 1)).1 by rw [hE],
          show ((i + 1, j + 1) : Nat × Nat) = (rowE op A fA i (j + 1)).2 by rw [hE],
          set_range_step (fun k => (rowE op A fA k (j + 1)).1) (fun k => (rowE op A fA k j).1)
            A.m i hi,
          set_range_step (fun k => (rowE op A fA k (j + 1)).2) (fun k => (rowE op A fA k j).2)
            A.m i hi]
      · have hE : rowE op A fA i (j + 1) = rowE op A fA i j := by
          rw [rowE_succ]; unfold fstep; exact if_neg hc
        rw [if_neg hc, pure_eq,
          range_step_same (fun k => (rowE op A fA k (j + 1)).1) (fun k => (rowE op A fA k j).1)
            A.m i (by rw [hE]),
          range_step_same (fun k => (rowE op A fA k (j + 1)).2) (fun k => (rowE op A fA k j).2)
            A.m i (by rw [hE])]

/-- A `Float64` value. -/
private def IsF64 (v : Val) : Prop := ∃ y, v = .f64 y

private theorem conv_f64 (v : Val) (h : IsF64 v) : Ty.convert .f64 v = .ok v := by
  obtain ⟨y, rfl⟩ := h
  first
  | rfl
  | simp [Ty.convert, Ty.isa, Val.typeOf]

private theorem findInitType_f64 (y : F64) : findInitType .f64 (.f64 y) = .f64 := by
  first
  | rfl
  | simp [findInitType, Ty.promoteUnion, Ty.isa, Val.typeOf]

private theorem findDims_eq (isMax : Bool) (A : Mat Val) (d rm rn : Nat) (y0 : F64)
    (hsh : reducedShape0 A.m A.n d = (rm, rn)) (hpos : A.m * A.n ≠ 0)
    (h0 : A.data.getD 0 .missing = .f64 y0) :
    findDims id isMax .f64 A d =
      findminmax id (fop isMax)
        { ty := .f64, m := rm, n := rn, data := List.replicate (rm * rn) (.f64 y0) }
        (List.replicate (rm * rn) (0, 0)) A := by
  have hconv : Ty.convert .f64 (.f64 y0) = .ok (.f64 y0) := conv_f64 _ ⟨y0, rfl⟩
  simp only [findDims, findDims.initArrayShape, hsh, hpos, ↓reduceIte, id_eq, h0,
    findInitType_f64, hconv, ok_bind, pure_eq]
  rfl

/-- The slice-wise conclusion of `FindDimsSlices` for one cell holding the result of
`findminmax!` over the slice `x0 :: xs` with the index map `e`. -/
private theorem find_cell (isMax : Bool) (e : Nat → Nat × Nat)
    (he : ∀ p, 1 ≤ p → e p ≠ (0, 0)) (x0 w : Val) (xs : List Val) (cell : Val × (Nat × Nat))
    (hcell : cell = ((x0 :: xs).zipIdx 1).foldl (fstep (fop isMax) e) (w, (0, 0))) :
    ∃ i, (if isMax then Vec.findmax (x0 :: xs) else Vec.findmin (x0 :: xs)) =
      .ok (cell.1, i) ∧ cell.2 = e i := by
  rw [find_fold _ e he] at hcell
  subst hcell
  exact ⟨_, by rw [vec_find_eq], rfl⟩

theorem findDimsSlices_proven : FindDimsSlices := by
  intro A d isMax hwf hd hm hn hA
  have hwf : A.data.length = A.m * A.n := hwf
  have hpos : A.m * A.n ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.mul_pos hm hn)
  have h0lt : 0 < A.data.length := by rw [hwf]; exact Nat.mul_pos hm hn
  obtain ⟨y0, hy0⟩ : IsF64 (A.data.getD 0 .missing) := hA _ (getD_mem _ h0lt)
  have hA' : ∀ x ∈ A.data, IsF64 x := hA
  rcases hd with rfl | rfl
  · have hm0 : ¬ A.m = 0 := by omega
    have hsh : reducedShape0 A.m A.n 1 = (1, A.n) := by
      show (if A.m = 0 then 0 else 1, A.n) = _
      rw [if_neg hm0]
    rw [findDims_eq isMax A 1 1 A.n y0 hsh hpos hy0,
      fmm_cols (fop isMax) IsF64
        { ty := .f64, m := 1, n := A.n, data := List.replicate (1 * A.n) (.f64 y0) }
        (List.replicate (1 * A.n) (0, 0)) A (.f64 y0) conv_f64 ⟨y0, rfl⟩ hA' hwf hpos rfl rfl
        (by simp) (by simp)]
    refine ⟨_, rfl, rfl, by simp, by simp, ?_⟩
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    obtain ⟨rest0, -, hck⟩ := col_cons A hwf hk hm
    obtain ⟨i, hi1, hi2⟩ := find_cell isMax (fun p => (p, k + 1)) (by intro p _ h; simp at h)
      (A.data.getD (A.m * k) .missing) (.f64 y0) (rest0.take (A.m - 1))
      (colC (fop isMax) A (.f64 y0) k) (by unfold colC; rw [hck])
    refine ⟨i, ?_, ?_⟩
    · rw [show A.slice 1 k = A.col k from rfl, hck, hi1]
      show _ = Except.ok ((((List.range A.n).map fun k =>
        (colC (fop isMax) A (.f64 y0) k).1).getD k .missing), i)
      rw [getD_map_range _ _ hk]
    · show ((List.range A.n).map fun k => (colC (fop isMax) A (.f64 y0) k).2)[k]? = _
      rw [getElem?_map_range _ hk, hi2] <;> rfl
  · have hn0 : ¬ A.n = 0 := by omega
    have hsh : reducedShape0 A.m A.n 2 = (A.m, 1) := by
      show (A.m, if A.n = 0 then 0 else 1) = _
      rw [if_neg hn0]
    rw [findDims_eq isMax A 2 A.m 1 y0 hsh hpos hy0]
    have hres : findminmax id (fop isMax)
        { ty := .f64, m := A.m, n := 1, data := List.replicate (A.m * 1) (.f64 y0) }
        (List.replicate (A.m * 1) (0, 0)) A =
        .ok ⟨{ ty := .f64, m := A.m, n := 1, data := ((List.range A.m).map fun i =>
            (rowE (fop isMax) A (.f64 y0) i A.n).1) },
          (List.range A.m).map fun i => (rowE (fop isMax) A (.f64 y0) i A.n).2⟩ := by
      by_cases hm1 : A.m = 1
      · exact fmm_one (fop isMax) IsF64
          { ty := .f64, m := A.m, n := 1, data := List.replicate (A.m * 1) (.f64 y0) }
          (List.replicate (A.m * 1) (0, 0)) A (.f64 y0) conv_f64 ⟨y0, rfl⟩ hA' hwf hpos hm1 rfl
          hm1 (by simp [hm1]) (by simp [hm1])
      · exact fmm_rows (fop isMax) IsF64
          { ty := .f64, m := A.m, n := 1, data := List.replicate (A.m * 1) (.f64 y0) }
          (List.replicate (A.m * 1) (0, 0)) A (.f64 y0) conv_f64 hA' hwf hpos hm1 rfl
          (by simp) (by simp)
    rw [hres]
    refine ⟨_, rfl, rfl, by simp, by simp, ?_⟩
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    obtain ⟨xs, hrk⟩ := row_cons A k hn
    obtain ⟨i, hi1, hi2⟩ := find_cell isMax (fun p => (k + 1, p)) (by intro p _ h; simp at h)
      (A.data.getD k .missing) (.f64 y0) xs (rowE (fop isMax) A (.f64 y0) k A.n)
      (by rw [rowE_full, hrk])
    refine ⟨i, ?_, ?_⟩
    · rw [show A.slice 2 k = A.row k from rfl, hrk, hi1]
      show _ = Except.ok ((((List.range A.m).map fun i =>
        (rowE (fop isMax) A (.f64 y0) i A.n).1).getD k .missing), i)
      rw [getD_map_range _ _ hk]
    · show ((List.range A.m).map fun i => (rowE (fop isMax) A (.f64 y0) i A.n).2)[k]? = _
      rw [getElem?_map_range _ hk, hi2] <;> rfl

end JuliaLean.Reduce
