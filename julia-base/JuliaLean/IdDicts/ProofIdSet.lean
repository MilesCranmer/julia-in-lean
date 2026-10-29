import JuliaLean.IdDicts.Props

/-!
# Proofs for `IdSet`

Invariant `SInv`: `max ≤ length(list)`, every slot from `max` on is `#undef`,
the assigned slots hold pairwise distinct elements, and `count` is their
number. Every call keeps it, and moves the assigned elements (in slot order)
exactly like the insertion-ordered reference set.
-/

namespace JuliaLean.IdDicts

/-- The assigned slots in order. -/
def allE (l : List (Option JVal)) : List JVal := l.filterMap id

/-- Every slot from `m` on is `#undef`. -/
def NoneFrom (l : List (Option JVal)) (m : Nat) : Prop := ∀ i, m ≤ i → (l[i]?).join = none

def SInv (s : IdSet) : Prop :=
  s.max ≤ s.list.length ∧ NoneFrom s.list s.max ∧ (allE s.list).Nodup ∧ s.count = (allE s.list).length

/-! ## List lemmas -/

theorem allE_cons (o : Option JVal) (t : List (Option JVal)) :
    allE (o :: t) = o.toList ++ allE t := by
  cases o <;> simp [allE, List.filterMap_cons]

theorem allE_append (a b : List (Option JVal)) : allE (a ++ b) = allE a ++ allE b := by
  simp [allE, List.filterMap_append]

theorem allE_nil_of {l : List (Option JVal)} (h : NoneFrom l 0) : allE l = [] := by
  induction l with
  | nil => rfl
  | cons o t ih =>
    have h0 := h 0 (Nat.zero_le _)
    simp at h0
    subst h0
    rw [allE_cons]
    simp only [Option.toList_none, List.nil_append]
    exact ih (fun i _ => by simpa using h (i + 1) (by omega))

theorem NoneFrom.tail {o : Option JVal} {t : List (Option JVal)} {m : Nat}
    (h : NoneFrom (o :: t) (m + 1)) : NoneFrom t m :=
  fun i hi => by simpa using h (i + 1) (by omega)

theorem allE_take {l : List (Option JVal)} {m : Nat} (h : NoneFrom l m) :
    allE (l.take m) = allE l := by
  induction l generalizing m with
  | nil => simp [allE]
  | cons o t ih =>
    cases m with
    | zero => rw [List.take_zero, allE_nil_of h]; rfl
    | succ m =>
      rw [List.take_succ_cons, allE_cons, allE_cons, ih h.tail]

theorem allE_spare {x : JVal} : ∀ {l : List (Option JVal)} {m : Nat}, m < l.length → NoneFrom l m →
    allE (l.set m (some x)) = allE l ++ [x]
  | [], _, hm, _ => by simp at hm
  | o :: t, 0, _, h => by
    have h0 := h 0 (Nat.le_refl _)
    simp at h0
    subst h0
    have ht : allE t = [] := allE_nil_of (fun i _ => by simpa using h (i + 1) (by omega))
    simp [allE_cons, ht]
  | o :: t, m + 1, hm, h => by
    simp only [List.set_cons_succ, allE_cons]
    rw [allE_spare (by simpa using hm) h.tail, List.append_assoc]

theorem getElem?_join_set_ne (l : List (Option JVal)) (i j : Nat) (v : Option JVal) (h : i ≠ j) :
    ((l.set i v)[j]?).join = (l[j]?).join := by
  rw [List.getElem?_set_ne h]

theorem NoneFrom.set_lt {l : List (Option JVal)} {m i : Nat} (h : NoneFrom l m) (hi : i < m)
    (v : Option JVal) : NoneFrom (l.set i v) m := by
  intro j hj
  rw [getElem?_join_set_ne l i j v (by omega)]
  exact h j hj

theorem NoneFrom.set_spare {l : List (Option JVal)} {m : Nat} (h : NoneFrom l m) (v : Option JVal) :
    NoneFrom (l.set m v) (m + 1) := by
  intro j hj
  rw [getElem?_join_set_ne l m j v (by omega)]
  exact h j (by omega)

theorem NoneFrom.mono {l : List (Option JVal)} {m n : Nat} (h : NoneFrom l m) (hmn : m ≤ n) :
    NoneFrom l n := fun i hi => h i (by omega)

/-! ## `peek` -/

theorem peek_none_iff (l : List (Option JVal)) (x : JVal) : peek l x = none ↔ x ∉ allE l := by
  induction l with
  | nil => simp [peek, allE]
  | cons o t ih =>
    rw [allE_cons]
    by_cases ho : o = some x
    · subst ho; simp [peek]
    · cases o with
      | none => simp [peek, ih]
      | some y =>
        have hy : ¬ x = y := fun e => ho (e ▸ rfl)
        simp [peek, ho, ih, hy]

theorem peek_some {l : List (Option JVal)} {x : JVal} :
    ∀ {i}, peek l x = some i → l[i]? = some (some x) := by
  induction l with
  | nil => intro i h; simp [peek] at h
  | cons o t ih =>
    intro i h
    by_cases ho : o = some x
    · subst ho; simp [peek] at h; subst h; rfl
    · simp only [peek, ho, if_false] at h
      cases hp : peek t x with
      | none => simp [hp] at h
      | some j =>
        simp [hp] at h
        subst h
        simpa using ih hp

theorem peek_set_self {l : List (Option JVal)} {x : JVal} {i : Nat} (h : peek l x = some i) :
    l.set i (some x) = l := by
  have := peek_some h
  apply List.ext_getElem?
  intro j
  by_cases hj : i = j
  · subst hj
    rw [List.getElem?_set_self (by
      have := List.getElem?_eq_some_iff.1 this
      exact this.1)]
    exact this.symm
  · rw [List.getElem?_set_ne hj]

theorem peek_erase {x : JVal} : ∀ {l : List (Option JVal)} {i : Nat}, peek l x = some i →
    allE (l.set i none) = (allE l).erase x
  | [], _, h => by simp [peek] at h
  | o :: t, i, h => by
    by_cases ho : o = some x
    · subst ho
      simp [peek] at h
      subst h
      simp [allE_cons]
    · simp only [peek, ho, if_false] at h
      cases hp : peek t x with
      | none => simp [hp] at h
      | some j =>
        simp [hp] at h
        subst h
        simp only [List.set_cons_succ, allE_cons]
        rw [peek_erase hp]
        cases o with
        | none => simp
        | some y =>
          have hy : ¬ (y == x) = true := by
            intro e; apply ho; simp at e; rw [e]
          simp only [Option.toList_some, List.singleton_append]
          rw [List.erase_cons_tail hy]

theorem peek_lt {l : List (Option JVal)} {x : JVal} {i m : Nat} (hn : NoneFrom l m)
    (h : peek l x = some i) : i < m := by
  have := peek_some h
  have hj := hn i
  rw [this] at hj
  simp at hj
  omega

/-! ## `shrinkMax` -/

theorem shrinkMax_spec (l : List (Option JVal)) : ∀ m, NoneFrom l m →
    NoneFrom l (shrinkMax l m) ∧ shrinkMax l m ≤ m
  | 0, h => ⟨h, Nat.le_refl _⟩
  | m + 1, h => by
    simp only [shrinkMax]
    split
    · rename_i hn
      have h' : NoneFrom l m := by
        intro i hi
        by_cases him : i = m
        · subst him; simpa using hn
        · exact h i (by omega)
      have := shrinkMax_spec l m h'
      exact ⟨this.1, by omega⟩
    · exact ⟨h, Nat.le_refl _⟩

/-! ## `jl_idset_put_key` -/

theorem set_after (x : JVal) (r : Nat) : ∀ xs : List JVal,
    (xs.map some ++ List.replicate (r + 1) none).set xs.length (some x) =
      xs.map some ++ some x :: List.replicate r none
  | [] => by simp [List.replicate_succ]
  | a :: xs => by simp [set_after x r xs]

theorem take_map_some (xs : List JVal) (ys : List (Option JVal)) :
    (xs.map some ++ ys).take xs.length = xs.map some := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem allE_map_some (xs : List JVal) (r : Nat) :
    allE (xs.map some ++ List.replicate r none) = xs := by
  induction xs with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    induction r with
    | zero => rfl
    | succ r ih => simp [List.replicate_succ, allE_cons, ih]
  | cons a xs ih => simp [allE_cons, ih]

theorem allE_length_le (l : List (Option JVal)) : (allE l).length ≤ l.length :=
  List.length_filterMap_le _ _

theorem putKey_form (l : List (Option JVal)) (x : JVal) :
    ∃ r, putKey l x l.length = ((allE l).map some ++ some x :: List.replicate r none, (allE l).length + 1) := by
  have hj := allE_length_le l
  have hc : compact l = (allE l).map some ++ List.replicate (l.length - (allE l).length) none := rfl
  have hca : allE (compact l) = allE l := by rw [hc, allE_map_some]
  unfold putKey
  simp only [if_true]
  rw [show (compact l).filterMap id = allE l from hca]
  split
  · rename_i hg
    rw [show (compact l).take (allE l).length = (allE l).map some by rw [hc, take_map_some]]
    have hpos : (if l.length < 4 then 4 else l.length * 3 / 2) - (allE l).length ≥ 1 := by
      split <;> omega
    refine ⟨(if l.length < 4 then 4 else l.length * 3 / 2) - (allE l).length - 1, ?_⟩
    have := set_after x ((if l.length < 4 then 4 else l.length * 3 / 2) - (allE l).length - 1) (allE l)
    rw [Nat.sub_add_cancel hpos] at this
    skip
    rw [this]
  · rename_i hg
    have hpos : l.length - (allE l).length ≥ 1 := by omega
    refine ⟨l.length - (allE l).length - 1, ?_⟩
    have := set_after x (l.length - (allE l).length - 1) (allE l)
    rw [Nat.sub_add_cancel hpos] at this
    skip
    rw [hc, this]

theorem form_props (xs : List JVal) (x : JVal) (r : Nat) :
    let l := xs.map some ++ some x :: List.replicate r none
    allE l = xs ++ [x] ∧ xs.length + 1 ≤ l.length ∧ NoneFrom l (xs.length + 1) ∧
    l[xs.length]? = some (some x) := by
  intro l
  refine ⟨?_, by simp [l], ?_, by simp [l]⟩
  · have := allE_map_some (xs ++ [x]) r
    simpa [l] using this
  · intro i hi
    simp only [l]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map]
    rw [show i - xs.length = (i - xs.length - 1) + 1 by omega, List.getElem?_cons_succ]
    rw [List.getElem?_replicate]
    split <;> rfl

/-! ## Calls -/

theorem push_absent {s : IdSet} (h : SInv s) {x : JVal} (hx : x ∉ allE s.list) :
    (s.push x).2 = .ok () ∧ SInv (s.push x).1 ∧ allE (s.push x).1.list = allE s.list ++ [x] ∧
    (s.push x).1.T = s.T := by
  obtain ⟨hml, hn, hnd, hc⟩ := h
  have hp : peek s.list x = none := (peek_none_iff _ _).2 hx
  have hnd' : (allE s.list ++ [x]).Nodup :=
    List.pairwise_append.2 ⟨hnd, List.pairwise_singleton _ _, fun a ha b hb => by
      simp at hb; subst hb; exact fun e => hx (e ▸ ha)⟩
  suffices key : ∃ L M, s.push x = (⟨s.T, L, s.count + 1, M⟩, .ok ()) ∧ M ≤ L.length ∧
      NoneFrom L M ∧ allE L = allE s.list ++ [x] by
    obtain ⟨L, M, he, hM, hN, hA⟩ := key
    rw [he]
    exact ⟨rfl, ⟨hM, hN, by rw [hA]; exact hnd', by rw [hA, hc]; simp⟩, hA, rfl⟩
  by_cases hlt : s.max < s.list.length
  · have hslot : (s.list[s.max]?).join = none := hn s.max (Nat.le_refl _)
    have hslot' : s.list[s.max]'hlt = none := by
      rw [List.getElem?_eq_getElem hlt] at hslot; simpa using hslot
    have hset : (s.list.set s.max (some x))[s.max]? = some (some x) := List.getElem?_set_self hlt
    refine ⟨s.list.set s.max (some x), s.max + 1, ?_, by simp; omega, hn.set_spare _,
      allE_spare hlt hn⟩
    unfold IdSet.push
    simp [hp, hlt, hslot', hset]
  · have hmax : s.max = s.list.length := by omega
    obtain ⟨r, hr⟩ := putKey_form s.list x
    obtain ⟨ha, hlen, hn', hget⟩ := form_props (allE s.list) x r
    refine ⟨_, _, ?_, hlen, hn', ha⟩
    unfold IdSet.push
    simp [hp, hmax, hr, hget]

theorem push_present {s : IdSet} {x : JVal} (hx : x ∈ allE s.list) :
    (s.push x).2 = .ok () ∧ (s.push x).1 = s := by
  have hp : peek s.list x ≠ none := fun e => (peek_none_iff _ _).1 e hx
  cases hpk : peek s.list x with
  | none => exact absurd hpk hp
  | some i =>
    unfold IdSet.push
    simp [hpk, peek_set_self hpk]

theorem pop!_spec {s : IdSet} (h : SInv s) (x : JVal) :
    SInv (s.pop! x).1 ∧ allE (s.pop! x).1.list = (allE s.list).erase x ∧ (s.pop! x).1.T = s.T ∧
    ((s.pop! x).2 = true ↔ x ∈ allE s.list) := by
  obtain ⟨hml, hn, hnd, hc⟩ := h
  unfold IdSet.pop!
  cases hpk : peek s.list x with
  | none =>
    have hx := (peek_none_iff _ _).1 hpk
    simp only
    rw [List.erase_of_not_mem hx]
    exact ⟨⟨hml, hn, hnd, hc⟩, rfl, by simp, by simp [hx]⟩
  | some i =>
    have hx : x ∈ allE s.list := Classical.byContradiction fun hx =>
      by rw [(peek_none_iff _ _).2 hx] at hpk; cases hpk
    have hi := peek_lt hn hpk
    have he := peek_erase hpk
    have hn1 := hn.set_lt hi none
    obtain ⟨hn2, hle⟩ := shrinkMax_spec (s.list.set i none) s.max hn1
    simp only
    refine ⟨⟨?_, hn2, ?_, ?_⟩, he, by simp, by simp [hx]⟩
    · simp; omega
    · rw [he]; exact List.Pairwise.sublist (List.erase_sublist) hnd
    · rw [he, List.length_erase_of_mem hx, hc]

theorem empty_spec {s : IdSet} (h : SInv s) :
    SInv s.empty ∧ allE s.empty.list = [] ∧ s.empty.T = s.T := by
  obtain ⟨hml, hn, hnd, hc⟩ := h
  have hall : NoneFrom s.empty.list 0 := by
    intro i _
    simp only [IdSet.empty, unsetPrefix]
    by_cases hi : i < min s.max s.list.length
    · rw [List.getElem?_append_left (by simpa using hi)]
      simp [List.getElem?_replicate, hi]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getElem?_drop]
      exact hn _ (by omega)
  have he := allE_nil_of hall
  refine ⟨⟨Nat.zero_le _, hall, by rw [he]; exact List.nodup_nil, by rw [he]; rfl⟩, he, by simp [IdSet.empty]⟩

theorem union_spec : ∀ (xs : List JVal) (s : IdSet), SInv s → s.T = .any →
    s.count + xs.length < 2 ^ 63 - 1 →
    SInv (s.union xs).1 ∧ allE (s.union xs).1.list = xs.foldl rPush (allE s.list) ∧
    (s.union xs).1.T = s.T
  | [], s, h, _, _ => ⟨h, rfl, rfl⟩
  | x :: xs, s, h, hT, hb => by
    by_cases hx : x ∈ allE s.list
    · obtain ⟨hr, hs⟩ := push_present hx
      have hne : (s.count == maxValues s.T) = false := by
        rw [hT]; simp [maxValues]; simp at hb; omega
      have := union_spec xs s h hT (by simp at hb; omega)
      have hu : s.union (x :: xs) = s.union xs := by
        conv => lhs; rw [IdSet.union]
        simp only [hr, hs, IdSet.length, hne, Bool.and_false, Bool.false_eq_true, if_false]
      rw [hu]
      simp only [List.foldl_cons, rPush, hx, if_true]
      exact this
    · obtain ⟨hr, h', ha, hT'⟩ := push_absent h hx
      have hcnt : (s.push x).1.count = s.count + 1 := by
        rw [h'.2.2.2, ha, h.2.2.2]; simp
      have hne : ((s.push x).1.count == maxValues s.T) = false := by
        rw [hcnt, hT]; simp [maxValues]; simp at hb; omega
      have := union_spec xs (s.push x).1 h' (hT'.trans hT) (by rw [hcnt]; simp at hb; omega)
      have hu : s.union (x :: xs) = (s.push x).1.union xs := by
        conv => lhs; rw [IdSet.union]
        simp only [hr]
        simp only [IdSet.length, hne, Bool.and_false, Bool.false_eq_true, if_false]
      rw [hu]
      simp only [List.foldl_cons, rPush, hx, if_false]
      rw [← ha, ← hT']
      exact this

theorem setdiff_spec : ∀ (xs : List JVal) (s : IdSet), SInv s →
    SInv (s.setdiff xs) ∧ allE (s.setdiff xs).list = xs.foldl List.erase (allE s.list) ∧
    (s.setdiff xs).T = s.T
  | [], s, h => ⟨h, rfl, rfl⟩
  | x :: xs, s, h => by
    obtain ⟨h1, he, hT, -⟩ := pop!_spec h x
    have := setdiff_spec xs (s.pop! x).1 h1
    simp only [IdSet.setdiff, List.foldl_cons] at this ⊢
    rw [he, hT] at this
    exact this

/-! ## Reference lengths -/

theorem rPush_length (xs : List JVal) (x : JVal) : (rPush xs x).length ≤ xs.length + 1 := by
  unfold rPush; split <;> simp

theorem foldl_rPush_length : ∀ (ys xs : List JVal), (ys.foldl rPush xs).length ≤ xs.length + ys.length
  | [], xs => by simp
  | y :: ys, xs => by
    have := foldl_rPush_length ys (rPush xs y)
    have := rPush_length xs y
    simp only [List.foldl_cons, List.length_cons]; omega

theorem foldl_erase_length : ∀ (ys xs : List JVal), (ys.foldl List.erase xs).length ≤ xs.length
  | [], xs => by simp
  | y :: ys, xs => by
    have := foldl_erase_length ys (xs.erase y)
    have := List.length_erase_le (l := xs) (a := y)
    simp only [List.foldl_cons]; omega

theorem ref_length (r : List JVal) (op : SOp) : (op.ref r).length ≤ r.length + op.size := by
  cases op with
  | push x => exact rPush_length r x
  | pop x | pop3 x _ | delete x => simp [SOp.ref, SOp.size]; exact List.length_erase_le
  | empty => simp [SOp.ref]
  | sizehint _ => simp [SOp.ref, SOp.size]
  | union ys => exact foldl_rPush_length ys r
  | setdiff ys => simp only [SOp.ref, SOp.size]; have := foldl_erase_length ys r; omega

/-! ## Whole calls -/

theorem step_spec {s : IdSet} (h : SInv s) (hT : s.T = .any) (op : SOp)
    (hb : s.count + op.size < 2 ^ 62) :
    SInv (op.run s) ∧ allE (op.run s).list = op.ref (allE s.list) ∧ (op.run s).T = .any := by
  cases op with
  | push x =>
    by_cases hx : x ∈ allE s.list
    · obtain ⟨-, hs⟩ := push_present hx
      simp only [SOp.run, SOp.ref, rPush, hx, if_true, hs]; exact ⟨h, trivial, hT⟩
    · obtain ⟨-, h', ha, hT'⟩ := push_absent h hx
      simp only [SOp.run, SOp.ref, rPush, hx, if_false]; exact ⟨h', ha, hT'.trans hT⟩
  | pop x =>
    obtain ⟨h1, he, hT', -⟩ := pop!_spec h x
    exact ⟨h1, he, hT'.trans hT⟩
  | pop3 x _ =>
    obtain ⟨h1, he, hT', -⟩ := pop!_spec h x
    exact ⟨h1, he, hT'.trans hT⟩
  | delete x =>
    obtain ⟨h1, he, hT', -⟩ := pop!_spec h x
    exact ⟨h1, he, hT'.trans hT⟩
  | empty =>
    obtain ⟨h1, he, hT'⟩ := empty_spec h
    exact ⟨h1, he, hT'.trans hT⟩
  | sizehint _ => exact ⟨h, rfl, hT⟩
  | union xs =>
    obtain ⟨h1, he, hT'⟩ := union_spec xs s h hT (by simp [SOp.size] at hb; omega)
    exact ⟨h1, he, hT'.trans hT⟩
  | setdiff xs =>
    obtain ⟨h1, he, hT'⟩ := setdiff_spec xs s h
    exact ⟨h1, he, hT'.trans hT⟩

theorem fold_spec : ∀ (ops : List SOp) (s : IdSet), SInv s → s.T = .any →
    s.count + (ops.map SOp.size).sum < 2 ^ 62 →
    SInv (ops.foldl SOp.run s) ∧ allE (ops.foldl SOp.run s).list = ops.foldl SOp.ref (allE s.list) ∧
    (ops.foldl SOp.run s).T = .any
  | [], s, h, hT, _ => ⟨h, rfl, hT⟩
  | op :: ops, s, h, hT, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    obtain ⟨h1, he, hT1⟩ := step_spec h hT op (by omega)
    have hl := ref_length (allE s.list) op
    have hc1 : (op.run s).count ≤ s.count + op.size := by
      rw [h1.2.2.2, he, h.2.2.2] at *; exact hl
    have := fold_spec ops (op.run s) h1 hT1 (by omega)
    simp only [List.foldl_cons]
    rw [he] at this
    exact this

theorem idSetOpsAgree_proven : IdSetOpsAgree := by
  intro ops hb
  dsimp only
  have h0 : SInv (IdSet.new .any) :=
    ⟨Nat.le_refl _, fun i _ => by simp [IdSet.new], List.nodup_nil, rfl⟩
  obtain ⟨h, he, hT⟩ := fold_spec ops (IdSet.new .any) h0 rfl (by simpa [IdSet.new] using hb)
  change SInv (runS .any ops) at h
  change allE (runS .any ops).list = refS ops at he
  have hel : (runS .any ops).elems = refS ops := by
    rw [IdSet.elems, ← he]; exact allE_take h.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold IdSet.iterate
    have hT' : (runS .any ops).T = .any := hT
    rw [hel, hT']
    generalize refS ops = xs
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      rw [List.mapM_cons, ih]
      simp [IdSet.iterate.cast', isa, bind, Except.bind, pure, Except.pure]
  · rw [IdSet.length, h.2.2.2, he]
  · rw [← he]; exact h.2.2.1
  · intro x
    unfold IdSet.mem
    rw [← he]
    by_cases hx : x ∈ allE (runS .any ops).list
    · have : peek (runS .any ops).list x ≠ none := fun e => (peek_none_iff _ _).1 e hx
      cases hp : peek (runS .any ops).list x with
      | none => exact absurd hp this
      | some _ => simp [hx]
    · rw [(peek_none_iff _ _).2 hx]; simp [hx]

end JuliaLean.IdDicts
