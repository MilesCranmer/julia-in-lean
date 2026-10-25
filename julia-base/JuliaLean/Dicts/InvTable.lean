import JuliaLean.Dicts.InvArith
import JuliaLean.Dicts.Ops

/-!
# The table invariant

`Inv o t` describes every table the `Dict` API produces: a power-of-two size,
slot bytes `0x00`/`0x7f`/`shorthash7`, each filled slot reachable from its
key's home slot within `maxprobe` steps over non-empty slots, pairwise
non-`isequal` keys, and `count` equal to the number of filled slots. The
abstraction of a table is `tlist t`, its stored pairs in slot order.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-! ## `Except` steps -/

@[simp] theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

@[simp] theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = Except.error e := rfl

@[simp] theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = Except.ok a := rfl

theorem bind_of_ok {ε α β : Type} {x : Except ε α} {a : α} (h : x = .ok a) (f : α → Except ε β) :
    (x >>= f) = f a := by subst h; rfl

theorem upd_same {α : Type} (f : Nat → α) (i : Nat) (x : α) : upd f i x i = x := by
  simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) {i j : Nat} (x : α) (h : j ≠ i) : upd f i x j = f j := by
  simp [upd, h]

/-! ## Generic list lemmas -/

theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    have ih := filterMap_congr_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases hg : g a with
    | none => rw [List.filterMap_cons_none (ha.trans hg), List.filterMap_cons_none hg, ih]
    | some b => rw [List.filterMap_cons_some (ha.trans hg), List.filterMap_cons_some hg, ih]

theorem filterMap_update_perm {β : Type} {f g : Nat → Option β} {j : Nat} {e : β} :
    ∀ {l : List Nat}, l.Nodup → j ∈ l → (∀ x ∈ l, x ≠ j → g x = f x) → g j = some e →
      List.Perm (l.filterMap g) (e :: l.filterMap (fun x => if x = j then none else f x))
  | [], _, hj, _, _ => absurd hj List.not_mem_nil
  | a :: l, hnd, hj, hgf, hge => by
    rw [List.nodup_cons] at hnd
    by_cases haj : a = j
    · subst haj
      have hc : l.filterMap g = l.filterMap (fun x => if x = a then none else f x) := by
        apply filterMap_congr_mem
        intro x hx
        have hxa : x ≠ a := fun h => hnd.1 (h ▸ hx)
        rw [ite_eq_right hxa]
        exact hgf x (List.mem_cons_of_mem _ hx) hxa
      have e2 : (a :: l).filterMap (fun x => if x = a then none else f x) =
          l.filterMap (fun x => if x = a then none else f x) :=
        List.filterMap_cons_none (f := fun x => if x = a then none else f x) (by simp)
      rw [List.filterMap_cons_some hge, e2, hc]
    · have hjl : j ∈ l := by
        rcases List.mem_cons.1 hj with h | h
        · exact absurd h.symm haj
        · exact h
      have ih := filterMap_update_perm hnd.2 hjl
        (fun x hx hxj => hgf x (List.mem_cons_of_mem _ hx) hxj) hge
      have hga : g a = f a := hgf a List.mem_cons_self haj
      cases hfa : f a with
      | none =>
        have e2 : (a :: l).filterMap (fun x => if x = j then none else f x) =
            l.filterMap (fun x => if x = j then none else f x) :=
          List.filterMap_cons_none (f := fun x => if x = j then none else f x) (by simp [haj, hfa])
        rw [List.filterMap_cons_none (hga.trans hfa), e2]
        exact ih
      | some b =>
        have e2 : (a :: l).filterMap (fun x => if x = j then none else f x) =
            b :: l.filterMap (fun x => if x = j then none else f x) :=
          List.filterMap_cons_some (f := fun x => if x = j then none else f x) (by simp [haj, hfa])
        rw [List.filterMap_cons_some (hga.trans hfa), e2]
        exact (List.Perm.cons b ih).trans (List.Perm.swap e b _)

theorem filterMap_erase_eq_filter {β : Type} {f : Nat → Option β} {j : Nat} {p : β → Bool}
    {l : List Nat} (h : ∀ x ∈ l, ∀ b, f x = some b → (p b = true ↔ x ≠ j)) :
    l.filterMap (fun x => if x = j then none else f x) = (l.filterMap f).filter p := by
  rw [List.filter_filterMap]
  apply filterMap_congr_mem
  intro x hx
  show (if x = j then none else f x) = (f x).filter p
  cases hf : f x with
  | none => split <;> rfl
  | some b =>
    have hb := h x hx b hf
    by_cases hxj : x = j
    · have hp : p b = false := by
        cases hp : p b
        · rfl
        · exact absurd (hb.1 hp) (fun h => h hxj)
      rw [ite_eq_left hxj, Option.filter_some_neg hp]
    · rw [ite_eq_right hxj, Option.filter_some_pos (hb.2 hxj)]

/-! ## Stored pairs -/

/-- The pair stored at slot `i`, if the slot is filled. -/
def ent (t : Table K V) (i : Nat) : Option (K × V) :=
  if isFilledB (t.slots i) then
    match t.keys i, t.vals i with
    | some k, some v => some (k, v)
    | _, _ => none
  else none

/-- The stored pairs in slot order. -/
def tlist (t : Table K V) : List (K × V) := (List.range' 1 t.size).filterMap (ent t)

/-- The home slot of a key. -/
def home (o : KeyOps K) (sz : Nat) (k : K) : Nat := (hashindex (o.hash k) sz).1

/-- Slot `i` lies on the probe sequence of `k`, within `maxprobe` steps and
after non-empty slots only. -/
def Chain (o : KeyOps K) (t : Table K V) (k : K) (i : Nat) : Prop :=
  ∃ d, d ≤ t.maxprobe ∧ i = pr t.size (home o t.size k) d ∧
    ∀ e, e < d → t.slots (pr t.size (home o t.size k) e) ≠ 0

/-- Slot `i` is empty, deleted, or filled with a reachable key. -/
def SlotOK (o : KeyOps K) (t : Table K V) (i : Nat) : Prop :=
  t.slots i = 0 ∨ t.slots i = 127 ∨
  ∃ k v, t.keys i = some k ∧ t.vals i = some v ∧ t.slots i = shorthash7 (o.hash k) ∧ Chain o t k i

/-- The invariant of every table built by the API. -/
structure Inv (o : KeyOps K) (t : Table K V) : Prop where
  size : t.size = 0 ∨ IsPow t.size
  sizeLe : t.size ≤ 2 ^ 62
  slot : ∀ i, 1 ≤ i → i ≤ t.size → SlotOK o t i
  distinct : ∀ i j a b, 1 ≤ i → i ≤ t.size → 1 ≤ j → j ≤ t.size → i ≠ j →
    ent t i = some a → ent t j = some b → o.eq a.1 b.1 = false
  count : t.count = (tlist t).length
  maxprobe : t.size = 0 ∨ t.maxprobe < t.size
  idxfloor : 1 ≤ t.idxfloor
  floorLe : ∀ i, 1 ≤ i → i ≤ t.size → isFilledB (t.slots i) = true → t.idxfloor ≤ i
  popcursor : 1 ≤ t.popcursor

/-- `t` represents the reference map `m`. -/
def Rep (o : KeyOps K) (t : Table K V) (m : RMap K V) : Prop := Inv o t ∧ List.Perm (tlist t) m

theorem ent_some {t : Table K V} {i : Nat} {e : K × V} (h : ent t i = some e) :
    isFilledB (t.slots i) = true ∧ t.keys i = some e.1 ∧ t.vals i = some e.2 := by
  unfold ent at h
  split at h
  · split at h
    · cases h; exact ⟨‹_›, ‹_›, ‹_›⟩
    · cases h
  · cases h

theorem ent_of_not_filled {t : Table K V} {i : Nat} (h : isFilledB (t.slots i) = false) :
    ent t i = none := by
  unfold ent
  simp [h]

theorem ent_of_filled {t : Table K V} {i : Nat} {k : K} {v : V} (h : isFilledB (t.slots i) = true)
    (hk : t.keys i = some k) (hv : t.vals i = some v) : ent t i = some (k, v) := by
  unfold ent
  rw [ite_eq_left h, hk, hv]

theorem mem_tlist {t : Table K V} {e : K × V} :
    e ∈ tlist t ↔ ∃ i, 1 ≤ i ∧ i ≤ t.size ∧ ent t i = some e := by
  unfold tlist
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [List.mem_range'_1] at hi
    exact ⟨i, hi.1, by omega, he⟩
  · rintro ⟨i, h1, h2, he⟩
    exact ⟨i, List.mem_range'_1.2 ⟨h1, by omega⟩, he⟩

theorem nodup_range'1 (s n : Nat) : (List.range' s n).Nodup := List.nodup_range'

/-- Filled slots of an invariant table. -/
theorem Inv.filled {o : KeyOps K} {t : Table K V} (hi : Inv o t) {i : Nat} (h1 : 1 ≤ i)
    (h2 : i ≤ t.size) (hf : isFilledB (t.slots i) = true) :
    ∃ k v, t.keys i = some k ∧ t.vals i = some v ∧ ent t i = some (k, v) ∧
      t.slots i = shorthash7 (o.hash k) ∧ Chain o t k i := by
  rcases hi.slot i h1 h2 with h | h | ⟨k, v, hk, hv, hs, hc⟩
  · rw [h, isFilledB_zero] at hf; cases hf
  · rw [h, isFilledB_127] at hf; cases hf
  · exact ⟨k, v, hk, hv, ent_of_filled hf hk hv, hs, hc⟩

theorem Inv.pos_of_filled {o : KeyOps K} {t : Table K V} (hi : Inv o t) {i : Nat} (h1 : 1 ≤ i)
    (h2 : i ≤ t.size) : IsPow t.size := by
  rcases hi.size with h | h
  · omega
  · exact h

theorem tlist_pairwise {o : KeyOps K} {t : Table K V} (hi : Inv o t) :
    (tlist t).Pairwise (fun a b => o.eq a.1 b.1 = false) := by
  unfold tlist
  apply List.Pairwise.filterMap (R := fun x y : Nat => x < y ∧ 1 ≤ x ∧ y ≤ t.size)
  · intro x y hxy a ha b hb
    exact hi.distinct x y a b hxy.2.1 (by omega) (by omega) hxy.2.2 (by omega) ha hb
  · have hl := List.pairwise_lt_range' (s := 1) (n := t.size)
    refine hl.imp_of_mem ?_
    intro x y hx hy hxy
    rw [List.mem_range'_1] at hx hy
    exact ⟨hxy, hx.1, by omega⟩

theorem Inv.count_le_size {o : KeyOps K} {t : Table K V} (hi : Inv o t) : t.count ≤ t.size := by
  rw [hi.count]
  unfold tlist
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

/-- A table with the same slots, keys and filled values. -/
theorem tlist_congr {t t' : Table K V} (hs : t'.size = t.size)
    (he : ∀ i, 1 ≤ i → i ≤ t.size → ent t' i = ent t i) : tlist t' = tlist t := by
  unfold tlist
  rw [hs]
  apply filterMap_congr_mem
  intro x hx
  rw [List.mem_range'_1] at hx
  exact he x hx.1 (by omega)

/-- Storing `e` at slot `j`. -/
theorem tlist_store {o : KeyOps K} {t t' : Table K V} {j : Nat} {e : K × V} (hs : t'.size = t.size)
    (hj1 : 1 ≤ j) (hj2 : j ≤ t.size)
    (he : ∀ i, 1 ≤ i → i ≤ t.size → ent t' i = if i = j then some e else ent t i)
    (hdis : ∀ i b, 1 ≤ i → i ≤ t.size → i ≠ j → ent t i = some b → o.eq e.1 b.1 = false)
    (hsame : ∀ b, ent t j = some b → o.eq e.1 b.1 = true) :
    List.Perm (tlist t') (e :: (tlist t).filter (fun b => !o.eq e.1 b.1)) := by
  unfold tlist
  rw [hs]
  have hmem : j ∈ List.range' 1 t.size := List.mem_range'_1.2 ⟨hj1, by omega⟩
  have h1 := filterMap_update_perm (f := ent t) (g := ent t') (j := j) (e := e)
    (nodup_range'1 1 t.size) hmem
    (fun x hx hxj => by
      rw [List.mem_range'_1] at hx
      rw [he x hx.1 (by omega), ite_eq_right hxj])
    (by rw [he j hj1 hj2, ite_eq_left rfl])
  refine h1.trans (List.Perm.cons e ?_)
  rw [filterMap_erase_eq_filter (p := fun b => !o.eq e.1 b.1)]
  intro x hx b hb
  rw [List.mem_range'_1] at hx
  by_cases hxj : x = j
  · subst hxj
    simp [hsame b hb]
  · simp [hdis x b hx.1 (by omega) hxj hb, hxj]

/-- Clearing slot `j`. -/
theorem tlist_clear {o : KeyOps K} {t t' : Table K V} {j : Nat} {k : K} (hs : t'.size = t.size)
    (he : ∀ i, 1 ≤ i → i ≤ t.size → ent t' i = if i = j then none else ent t i)
    (hdis : ∀ i b, 1 ≤ i → i ≤ t.size → i ≠ j → ent t i = some b → o.eq k b.1 = false)
    (hsame : ∀ b, ent t j = some b → o.eq k b.1 = true) :
    tlist t' = (tlist t).filter (fun b => !o.eq k b.1) := by
  unfold tlist
  rw [hs]
  rw [filterMap_congr_mem (f := ent t') (g := fun x => if x = j then none else ent t x) (fun x hx => by
    rw [List.mem_range'_1] at hx
    exact he x hx.1 (by omega))]
  rw [filterMap_erase_eq_filter (p := fun b => !o.eq k b.1)]
  intro x hx b hb
  rw [List.mem_range'_1] at hx
  by_cases hxj : x = j
  · subst hxj
    simp [hsame b hb]
  · simp [hdis x b hx.1 (by omega) hxj hb, hxj]

/-! ## Chains -/

theorem home_range {o : KeyOps K} {sz : Nat} (h : IsPow sz) (k : K) :
    1 ≤ home o sz k ∧ home o sz k ≤ sz := hashindex_range h _

/-- A chain survives a larger `maxprobe` and slots that stay non-empty. -/
theorem Chain.mono {o : KeyOps K} {t t' : Table K V} {k : K} {i : Nat}
    (hpow : IsPow t.size) (hmp : t.maxprobe < t.size)
    (hs : t'.size = t.size) (hm : t.maxprobe ≤ t'.maxprobe)
    (hne : ∀ p, 1 ≤ p → p ≤ t.size → t.slots p ≠ 0 → t'.slots p ≠ 0)
    (hc : Chain o t k i) : Chain o t' k i := by
  obtain ⟨d, hd, hi, hall⟩ := hc
  refine ⟨d, Nat.le_trans hd hm, by rw [hs]; exact hi, fun e he => ?_⟩
  rw [hs]
  have hr := pr_range hpow (home_range hpow k (o := o)).1 (home_range hpow k (o := o)).2
    (show e < t.size by omega)
  exact hne _ hr.1 hr.2 (hall e he)

/-- Equal hashes have equal homes and tags. -/
theorem home_eq_of_eq {o : KeyOps K} (hl : o.Lawful) {a b : K} (h : o.eq a b = true) (sz : Nat) :
    home o sz a = home o sz b := by
  unfold home
  rw [hl.hash_eq a b h]

theorem SlotOK.transfer {o : KeyOps K} {t t' : Table K V} {i : Nat} (h : SlotOK o t i)
    (hs : t'.slots i = t.slots i) (hk : t'.keys i = t.keys i) (hv : t'.vals i = t.vals i)
    (hc : ∀ k, Chain o t k i → Chain o t' k i) : SlotOK o t' i := by
  rcases h with h | h | ⟨k, v, h1, h2, h3, h4⟩
  · exact Or.inl (hs.trans h)
  · exact Or.inr (Or.inl (hs.trans h))
  · exact Or.inr (Or.inr ⟨k, v, hk.trans h1, hv.trans h2, hs.trans h3, hc k h4⟩)

theorem upd_self {α : Type} (f : Nat → α) (i : Nat) : upd f i (f i) = f := by
  funext j
  unfold upd
  split
  · next h => rw [h]
  · rfl

theorem filled_ne_zero {b : Nat} (h : isFilledB b = true) : b ≠ 0 := by
  intro h0
  rw [h0, isFilledB_zero] at h
  cases h

theorem filled_ne_127 {b : Nat} (h : isFilledB b = true) : b ≠ 127 := by
  intro h0
  rw [h0, isFilledB_127] at h
  cases h

/-- A slot of an invariant table is empty, deleted, or filled. -/
theorem Inv.byte {o : KeyOps K} {t : Table K V} (hi : Inv o t) {i : Nat} (h1 : 1 ≤ i)
    (h2 : i ≤ t.size) : t.slots i = 0 ∨ t.slots i = 127 ∨ isFilledB (t.slots i) = true := by
  rcases hi.slot i h1 h2 with h | h | ⟨k, -, -, -, hs, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [hs]; exact shorthash7_filled _))

/-- Stored keys of a table are not `isequal` to `q`. -/
def Absent (o : KeyOps K) (t : Table K V) (q : K) : Prop := ∀ e ∈ tlist t, o.eq q e.1 = false

end JuliaLean.Dicts
