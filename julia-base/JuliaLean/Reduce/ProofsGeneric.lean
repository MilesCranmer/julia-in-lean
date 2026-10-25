import JuliaLean.Reduce.Props

/-!
Proofs of the generic reduction properties: pairwise reduction of an associative
operation is the left fold, `extrema` is `(minimum, maximum)`, folds with `init`,
flattened folds, `reduce(vcat/hcat)` and empty reductions.
-/

namespace JuliaLean.Reduce

section
variable {α β : Type}

/-- `mrImpl` of a single element is `first`. -/
theorem mrImpl_nil (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat) (a : α) :
    mrImpl f op first blk a [] = first a := by
  rw [mrImpl]

/-- `mrImpl` below the block size is the left fold. -/
theorem mrImpl_small (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat) (a b : α)
    (rest : List α) (hc : rest.length + 1 < blk) :
    mrImpl f op first blk a (b :: rest) = rest.foldl (fun v x => op v (f x)) (op (f a) (f b)) := by
  rw [mrImpl]; simp only [hc, ite_true]

/-- `mrImpl` at or above the block size splits into halves. -/
theorem mrImpl_split (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat) (a b c : α)
    (rest rest2 : List α) (hc : ¬ rest.length + 1 < blk)
    (hd : (b :: rest).drop ((rest.length + 1) / 2) = c :: rest2) :
    mrImpl f op first blk a (b :: rest) =
      op (mrImpl f op first blk a ((b :: rest).take ((rest.length + 1) / 2)))
        (mrImpl f op first blk c rest2) := by
  rw [mrImpl]; simp only [hc, ite_false]
  split
  · rename_i h; rw [hd] at h; cases h
  · rename_i c' rest2' h; rw [hd] at h; cases h; rfl

theorem drop_half_cons (b : α) (rest : List α) :
    ∃ c rest2, (b :: rest).drop ((rest.length + 1) / 2) = c :: rest2 ∧
      rest2.length + 1 + (rest.length + 1) / 2 = rest.length + 1 := by
  cases h : (b :: rest).drop ((rest.length + 1) / 2) with
  | nil =>
    have := congrArg List.length h
    simp only [List.length_drop, List.length_cons, List.length_nil] at this; omega
  | cons c rest2 =>
    refine ⟨c, rest2, rfl, ?_⟩
    have := congrArg List.length h
    simp only [List.length_drop, List.length_cons] at this; omega

theorem foldl_op_assoc (f : α → β) (op : β → β → β)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) :
    ∀ (l : List α) (x y : β),
      op x (l.foldl (fun v z => op v (f z)) y) = l.foldl (fun v z => op v (f z)) (op x y)
  | [], _, _ => rfl
  | z :: l, x, y => by
    simp only [List.foldl_cons]
    rw [foldl_op_assoc f op hassoc l x, hassoc]

theorem foldl_merge (f : α → β) (op : β → β → β)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) (a c : α) (l1 l2 : List α) :
    op (l1.foldl (fun v y => op v (f y)) (f a)) (l2.foldl (fun v y => op v (f y)) (f c)) =
      (l1 ++ c :: l2).foldl (fun v y => op v (f y)) (f a) := by
  rw [List.foldl_append, List.foldl_cons, foldl_op_assoc f op hassoc]

theorem mrImpl_foldl_aux (f : α → β) (op : β → β → β) (blk : Nat)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) :
    ∀ (n : Nat) (a : α) (rest : List α), rest.length < n →
      mrImpl f op f blk a rest = rest.foldl (fun v y => op v (f y)) (f a)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, [], _ => mrImpl_nil f op f blk a
  | n + 1, a, b :: rest, hlen => by
    by_cases hc : rest.length + 1 < blk
    · rw [mrImpl_small f op f blk a b rest hc]; rfl
    · obtain ⟨c, rest2, hd, hl⟩ := drop_half_cons b rest
      simp only [List.length_cons] at hlen
      rw [mrImpl_split f op f blk a b c rest rest2 hc hd,
        mrImpl_foldl_aux f op blk hassoc n a ((b :: rest).take ((rest.length + 1) / 2))
          (by simp only [List.length_take, List.length_cons]; omega),
        mrImpl_foldl_aux f op blk hassoc n c rest2 (by omega),
        foldl_merge f op hassoc, ← hd, List.take_append_drop]

/-- For an associative `op`, `mapreduce_impl` with `mapreduce_first = f` is the left fold. -/
theorem mrImpl_foldl (f : α → β) (op : β → β → β) (blk : Nat)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) (a : α) (rest : List α) :
    mrImpl f op f blk a rest = rest.foldl (fun v y => op v (f y)) (f a) :=
  mrImpl_foldl_aux f op blk hassoc (rest.length + 1) a rest (Nat.lt_succ_self _)

section pair
variable {γ : Type}

theorem foldl_pair (f1 : α → β) (f2 : α → γ) (op1 : β → β → β) (op2 : γ → γ → γ) :
    ∀ (l : List α) (s1 : β) (s2 : γ),
      l.foldl (fun (s : β × γ) x => (op1 s.1 (f1 x), op2 s.2 (f2 x))) (s1, s2) =
        (l.foldl (fun v x => op1 v (f1 x)) s1, l.foldl (fun v x => op2 v (f2 x)) s2)
  | [], _, _ => rfl
  | x :: l, s1, s2 => foldl_pair f1 f2 op1 op2 l (op1 s1 (f1 x)) (op2 s2 (f2 x))

theorem mrImpl_pair_aux (f1 g1 : α → β) (f2 g2 : α → γ) (op1 : β → β → β) (op2 : γ → γ → γ)
    (blk : Nat) :
    ∀ (n : Nat) (a : α) (rest : List α), rest.length < n →
      mrImpl (fun x => (f1 x, f2 x)) (fun s t => (op1 s.1 t.1, op2 s.2 t.2))
          (fun x => (g1 x, g2 x)) blk a rest =
        (mrImpl f1 op1 g1 blk a rest, mrImpl f2 op2 g2 blk a rest)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, [], _ => by simp only [mrImpl_nil]
  | n + 1, a, b :: rest, hlen => by
    by_cases hc : rest.length + 1 < blk
    · rw [mrImpl_small _ _ _ _ _ _ _ hc, mrImpl_small _ _ _ _ _ _ _ hc,
        mrImpl_small _ _ _ _ _ _ _ hc]
      exact foldl_pair f1 f2 op1 op2 rest _ _
    · obtain ⟨c, rest2, hd, hl⟩ := drop_half_cons b rest
      simp only [List.length_cons] at hlen
      rw [mrImpl_split _ _ _ _ _ _ _ _ _ hc hd, mrImpl_split _ _ _ _ _ _ _ _ _ hc hd,
        mrImpl_split _ _ _ _ _ _ _ _ _ hc hd,
        mrImpl_pair_aux f1 g1 f2 g2 op1 op2 blk n a ((b :: rest).take ((rest.length + 1) / 2))
          (by simp only [List.length_take, List.length_cons]; omega),
        mrImpl_pair_aux f1 g1 f2 g2 op1 op2 blk n c rest2 (by omega)]

/-- `mapreduce_impl` of a componentwise pair map and operation is the pair of the two
`mapreduce_impl`s: the recursion tree depends only on the length. -/
theorem mrImpl_pair (f1 g1 : α → β) (f2 g2 : α → γ) (op1 : β → β → β) (op2 : γ → γ → γ)
    (blk : Nat) (a : α) (rest : List α) :
    mrImpl (fun x => (f1 x, f2 x)) (fun s t => (op1 s.1 t.1, op2 s.2 t.2))
        (fun x => (g1 x, g2 x)) blk a rest =
      (mrImpl f1 op1 g1 blk a rest, mrImpl f2 op2 g2 blk a rest) :=
  mrImpl_pair_aux f1 g1 f2 g2 op1 op2 blk (rest.length + 1) a rest (Nat.lt_succ_self _)

/-- `_mapreduce` of a componentwise pair map and operation, with an error for the empty
collection, is the pair of the two `_mapreduce`s. -/
theorem mapreduceArr_pair (f1 g1 : α → β) (f2 g2 : α → γ) (op1 : β → β → β)
    (op2 : γ → γ → γ) (e : Err) (blk : Nat) (v : List α) :
    mapreduceArr (fun x => (f1 x, f2 x)) (fun s t => (op1 s.1 t.1, op2 s.2 t.2))
        (fun x => (g1 x, g2 x)) (.error e) blk v =
      (do let a ← mapreduceArr f1 op1 g1 (.error e) blk v
          let b ← mapreduceArr f2 op2 g2 (.error e) blk v
          pure (a, b)) := by
  match v with
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest =>
    simp only [mapreduceArr]
    by_cases hc : rest.length + 2 < 16
    · simp only [hc, ite_true]
      exact congrArg Except.ok (foldl_pair f1 f2 op1 op2 rest _ _)
    · simp only [hc, ite_false]
      exact congrArg Except.ok (mrImpl_pair f1 g1 f2 g2 op1 op2 blk a (b :: rest))

end pair

end

theorem pairwiseFoldl_proven : PairwiseFoldl := by
  intro α β f op blk e x xs hassoc
  match xs with
  | [] => rfl
  | b :: rest =>
    simp only [mapreduceArr]
    by_cases hc : rest.length + 2 < 16
    · simp only [hc, ite_true]; rfl
    · simp only [hc, ite_false]; rw [mrImpl_foldl f op blk hassoc]

theorem extremaAgree_proven : ExtremaAgree := by
  intro v
  exact mapreduceArr_pair id id id id Val.vmin Val.vmax .argumentError 1024 v

theorem foldInit_proven : FoldInit := by
  intro α β f op init v
  refine ⟨?_, ?_⟩
  · simp only [mapfoldlInit, List.foldl_map]
  · simp only [mapfoldrInit, List.foldl_reverse, List.foldr_map]

theorem foldl_nested {γ δ : Type} (g : γ → δ → γ) :
    ∀ (vs : List (List δ)) (init : γ),
      vs.foldl (fun acc v => v.foldl g acc) init = vs.flatten.foldl g init
  | [], _ => rfl
  | v :: vs, init => by
    rw [List.foldl_cons, foldl_nested g vs, List.flatten_cons, List.foldl_append]

theorem foldl_optStep (op : Val → Val → Val) (step : Option Val → Val → Option Val)
    (hs : ∀ a x, step (some a) x = some (op a x)) :
    ∀ (l : List Val) (a : Val), l.foldl step (some a) = some (l.foldl op a)
  | [], _ => rfl
  | y :: l, a => by
    rw [List.foldl_cons, hs, foldl_optStep op step hs l]; rfl

theorem flattenFoldl_proven : FlattenFoldl := by
  intro op first init vs
  refine ⟨foldl_nested op vs init, ?_⟩
  intro x rest h
  unfold Vec.foldlFlatten
  dsimp only
  rw [foldl_nested, h]
  simp only [List.foldl_cons]
  rw [foldl_optStep op _ ?hs]
  case hs => intro _ _; rfl
  all_goals rfl

theorem foldl_append_acc {α : Type} :
    ∀ (vs : List (List α)) (acc : List α), vs.foldl (fun a v => a ++ v) acc = acc ++ vs.flatten
  | [], acc => by simp
  | v :: vs, acc => by
    rw [List.foldl_cons, foldl_append_acc vs, List.flatten_cons, List.append_assoc]

theorem reduceCatSpec_proven : ReduceCatSpec := by
  intro vs hne
  refine ⟨?_, ?_⟩
  · unfold Cat.reduceVcat
    simp only [hne, ite_false, foldl_append_acc, List.nil_append]
  · intro v1 rest hvs
    subst hvs
    refine ⟨?_, ?_⟩
    · intro hall
      simp only [Cat.reduceHcat]
      have : ((v1 :: rest).all fun v => decide (v.length = v1.length)) = true := by
        simp only [List.all_eq_true, decide_eq_true_eq]; exact hall
      simp only [this, ite_true, foldl_append_acc, List.nil_append]
    · intro ⟨v, hv, hlen⟩
      simp only [Cat.reduceHcat]
      have : ¬ ((v1 :: rest).all fun v => decide (v.length = v1.length)) = true := by
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro hall; exact hlen (hall v hv)
      simp only [this, Bool.false_eq_true, ite_false]

theorem emptyReductions_proven : EmptyReductions := by
  intro init t
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · cases t <;> rfl
  · cases t <;> rfl

end JuliaLean.Reduce
