import JuliaLean.Dicts.Props
import JuliaLean.Dicts.ProofSet

/-!
# Reference sets

Membership in reference sets (`rmem`), the results of folding `rset`, `rdel`
and the `symdiff!` step over the pairwise non-`isequal` keys of another set,
and the pigeonhole bound behind the length tests of `issubset` and `==`.
-/

namespace JuliaLean.Dicts.SetProofs

variable {K : Type}

theorem perm_of_eq' {α : Type} {l₁ l₂ : List α} (h : l₁ = l₂) : List.Perm l₁ l₂ :=
  h ▸ List.Perm.refl _

theorem perm_all {α : Type} {l l' : List α} (h : List.Perm l l') (p : α → Bool) :
    l.all p = l'.all p := by
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, List.all_eq_true]
  exact ⟨fun H x hx => H x (h.mem_iff.2 hx), fun H x hx => H x (h.mem_iff.1 hx)⟩

theorem all_map_fst (p : K → Bool) : ∀ L : RMap K Unit, (L.map (·.1)).all p = L.all (fun e => p e.1)
  | [] => rfl
  | e :: L => by
    show (p e.1 && (L.map (·.1)).all p) = (p e.1 && L.all (fun e => p e.1))
    rw [all_map_fst p L]

theorem foldl_map_fst {α : Type} (g : α → K → α) :
    ∀ (L : RMap K Unit) (a : α), (L.map (·.1)).foldl g a = L.foldl (fun a e => g a e.1) a
  | [], _ => rfl
  | e :: L, a => foldl_map_fst g L (g a e.1)

theorem eq_comm_bool {o : KeyOps K} (hl : o.Lawful) (a b : K) : o.eq a b = o.eq b a := by
  cases h : o.eq b a
  · exact eq_false_symm hl h
  · exact hl.symm b a h

/-! ## Membership -/

theorem rmem_nil (o : KeyOps K) (x : K) : rmem o [] x = false := rfl

theorem rmem_cons (o : KeyOps K) (a : K × Unit) (m : RMap K Unit) (x : K) :
    rmem o (a :: m) x = (o.eq x a.1 || rmem o m x) := by
  unfold rmem rfind
  by_cases h : o.eq x a.1 = true
  · rw [List.find?_cons_of_pos (p := fun e : K × Unit => o.eq x e.1) h, h] <;> rfl
  · rw [List.find?_cons_of_neg (p := fun e : K × Unit => o.eq x e.1) h, Bool.eq_false_iff.2 h,
      Bool.false_or]

theorem rmem_true_iff {o : KeyOps K} {m : RMap K Unit} {x : K} :
    rmem o m x = true ↔ ∃ e ∈ m, o.eq x e.1 = true := by
  induction m with
  | nil =>
    refine ⟨fun h => absurd h (by rw [rmem_nil]; decide), ?_⟩
    rintro ⟨_, h, _⟩
    exact absurd h List.not_mem_nil
  | cons a m ih =>
    rw [rmem_cons, Bool.or_eq_true_iff, ih]
    constructor
    · rintro (h | ⟨e, he, hq⟩)
      · exact ⟨a, List.mem_cons_self, h⟩
      · exact ⟨e, List.mem_cons_of_mem _ he, hq⟩
    · rintro ⟨e, he, hq⟩
      rcases List.mem_cons.1 he with h | h
      · rw [h] at hq
        exact Or.inl hq
      · exact Or.inr ⟨e, h, hq⟩

theorem rmem_false_iff {o : KeyOps K} {m : RMap K Unit} {x : K} :
    rmem o m x = false ↔ ∀ e ∈ m, o.eq x e.1 = false := by
  constructor
  · intro h e he
    cases hq : o.eq x e.1
    · rfl
    · rw [rmem_true_iff.2 ⟨e, he, hq⟩] at h
      cases h
  · intro h
    cases hm : rmem o m x
    · rfl
    · obtain ⟨e, he, hq⟩ := rmem_true_iff.1 hm
      rw [h e he] at hq
      cases hq

theorem rmem_append (o : KeyOps K) (m₁ m₂ : RMap K Unit) (x : K) :
    rmem o (m₁ ++ m₂) x = (rmem o m₁ x || rmem o m₂ x) := by
  induction m₁ with
  | nil => rfl
  | cons a m ih => rw [List.cons_append, rmem_cons, rmem_cons, ih, Bool.or_assoc]

theorem rmem_perm {o : KeyOps K} {m m' : RMap K Unit} (h : List.Perm m m') (x : K) :
    rmem o m x = rmem o m' x := by
  apply Bool.eq_iff_iff.2
  rw [rmem_true_iff, rmem_true_iff]
  exact ⟨fun ⟨e, he, hq⟩ => ⟨e, h.mem_iff.1 he, hq⟩, fun ⟨e, he, hq⟩ => ⟨e, h.mem_iff.2 he, hq⟩⟩

theorem rmem_congr {o : KeyOps K} (hl : o.Lawful) (m : RMap K Unit) {x y : K}
    (h : o.eq x y = true) : rmem o m x = rmem o m y := by
  apply Bool.eq_iff_iff.2
  rw [rmem_true_iff, rmem_true_iff]
  exact ⟨fun ⟨e, he, hq⟩ => ⟨e, he, hl.trans y x e.1 (hl.symm x y h) hq⟩,
    fun ⟨e, he, hq⟩ => ⟨e, he, hl.trans x y e.1 h hq⟩⟩

/-- Membership in a filtered set, when the filter is constant on the keys `isequal` to `x`. -/
theorem rmem_filter {o : KeyOps K} {x : K} {p : K × Unit → Bool} {c : Bool} :
    ∀ m : RMap K Unit, (∀ b ∈ m, o.eq x b.1 = true → p b = c) →
      rmem o (m.filter p) x = (rmem o m x && c)
  | [], _ => rfl
  | a :: m, h => by
    have ih := rmem_filter m (fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [rmem_cons]
    cases hq : o.eq x a.1
    · rw [Bool.false_or, ← ih]
      cases hp : p a
      · rw [List.filter_cons_of_neg (by simp [hp])]
      · rw [List.filter_cons_of_pos hp, rmem_cons, hq, Bool.false_or]
    · have hpa := h a List.mem_cons_self hq
      rw [Bool.true_or, Bool.true_and]
      cases c
      · rw [List.filter_cons_of_neg (by simp [hpa]), ih, Bool.and_false]
      · rw [List.filter_cons_of_pos hpa, rmem_cons, hq, Bool.true_or]

/-- `x` is in `ms` and, as decided by `q`, in `mt` or not. -/
theorem rmem_filter_rmem {o : KeyOps K} (hl : o.Lawful) (ms mt : RMap K Unit) (q : Bool → Bool)
    (x : K) : rmem o (ms.filter (fun e => q (rmem o mt e.1))) x = (rmem o ms x && q (rmem o mt x)) :=
  rmem_filter ms (fun b _ hb => by
    show q (rmem o mt b.1) = q (rmem o mt x)
    rw [rmem_congr hl mt (hl.symm x b.1 hb)])

theorem rmem_inter {o : KeyOps K} (hl : o.Lawful) (ms mt : RMap K Unit) (x : K) :
    rmem o (ms.filter (fun e => rmem o mt e.1)) x = (rmem o ms x && rmem o mt x) :=
  rmem_filter_rmem hl ms mt (fun b => b) x

theorem rmem_diff {o : KeyOps K} (hl : o.Lawful) (ms mt : RMap K Unit) (x : K) :
    rmem o (ms.filter (fun e => !rmem o mt e.1)) x = (rmem o ms x && !rmem o mt x) :=
  rmem_filter_rmem hl ms mt (fun b => !b) x

theorem rmem_union {o : KeyOps K} (hl : o.Lawful) (ms mt : RMap K Unit) (x : K) :
    rmem o (mt ++ ms.filter (fun b => !rmem o mt b.1)) x = (rmem o ms x || rmem o mt x) := by
  rw [rmem_append, rmem_diff hl ms mt x]
  cases rmem o ms x <;> cases rmem o mt x <;> rfl

theorem rmem_symdiff {o : KeyOps K} (hl : o.Lawful) (ms mt : RMap K Unit) (x : K) :
    rmem o (ms.filter (fun b => !rmem o mt b.1) ++ mt.filter (fun e => !rmem o ms e.1)) x =
      (rmem o ms x != rmem o mt x) := by
  rw [rmem_append, rmem_diff hl ms mt x, rmem_diff hl mt ms x]
  cases rmem o ms x <;> cases rmem o mt x <;> rfl

theorem rmem_rdel {o : KeyOps K} (hl : o.Lawful) (m : RMap K Unit) (k x : K) :
    rmem o (rdel o m k) x = (rmem o m x && !o.eq x k) :=
  rmem_filter m (fun b _ hb => by
    show (!o.eq k b.1) = !o.eq x k
    rw [eq_comm_bool hl k b.1, eq_congr_left hl (hl.symm x b.1 hb)])

/-! ## Folds over the keys of another set -/

theorem filter_rdel_notin {o : KeyOps K} (hl : o.Lawful) (m L : RMap K Unit) (k : K) :
    (rdel o m k).filter (fun b => !rmem o L b.1) =
      m.filter (fun b => !rmem o ((k, ()) :: L) b.1) := by
  rw [rdel, List.filter_filter]
  apply List.filter_congr
  intro b _
  show ((!rmem o L b.1) && !o.eq k b.1) = !rmem o ((k, ()) :: L) b.1
  rw [rmem_cons, eq_comm_bool hl k b.1]
  show ((!rmem o L b.1) && !o.eq b.1 k) = !(o.eq b.1 k || rmem o L b.1)
  cases o.eq b.1 k <;> cases rmem o L b.1 <;> rfl

/-- `union!` on reference sets: the keys of `L`, then the rest of `m`. -/
theorem union_fold {o : KeyOps K} (hl : o.Lawful) :
    ∀ (L m : RMap K Unit), Distinct o L →
      List.Perm (L.foldl (fun m e => rset o m e.1 ()) m) (L ++ m.filter (fun b => !rmem o L b.1))
  | [], m, _ => by
    show List.Perm m (m.filter (fun b => !rmem o [] b.1))
    exact perm_of_eq' (List.filter_eq_self.2 (fun _ _ => rfl)).symm
  | (k, ()) :: L, m, hd => by
    obtain ⟨hd1, hd2⟩ := List.pairwise_cons.1 hd
    have hk : rmem o L k = false := rmem_false_iff.2 hd1
    refine (union_fold hl L (rset o m k ()) hd2).trans ?_
    have hf : (rset o m k ()).filter (fun b => !rmem o L b.1) =
        (k, ()) :: m.filter (fun b => !rmem o ((k, ()) :: L) b.1) := by
      rw [rset, List.filter_cons_of_pos (by simp [hk]), filter_rdel_notin hl]
    rw [hf]
    exact List.perm_middle

/-- `setdiff!` on reference sets: the members of `m` not in `L`. -/
theorem rdel_fold {o : KeyOps K} (hl : o.Lawful) :
    ∀ (L m : RMap K Unit),
      L.foldl (fun m e => rdel o m e.1) m = m.filter (fun b => !rmem o L b.1)
  | [], m => by
    show m = m.filter (fun b => !rmem o [] b.1)
    exact (List.filter_eq_self.2 (fun _ _ => rfl)).symm
  | (k, ()) :: L, m => by
    show L.foldl (fun m e => rdel o m e.1) (rdel o m k) = _
    rw [rdel_fold hl L, filter_rdel_notin hl]

/-- The step of `symdiff!` on reference sets. -/
def rsym (o : KeyOps K) (m : RMap K Unit) (x : K) : RMap K Unit :=
  if rmem o m x then rdel o m x else rset o m x ()

theorem rsym_of_mem {o : KeyOps K} {m : RMap K Unit} {k : K} (h : rmem o m k = true) :
    rsym o m k = rdel o m k := by
  unfold rsym
  rw [if_pos h]

theorem rsym_of_not_mem {o : KeyOps K} {m : RMap K Unit} {k : K} (h : rmem o m k = false) :
    rsym o m k = rset o m k () := by
  unfold rsym
  rw [if_neg (by simp [h])]

theorem rset_of_not_mem {o : KeyOps K} {m : RMap K Unit} {k : K} (h : rmem o m k = false) :
    rset o m k () = (k, ()) :: m := by
  rw [rset, rdel_of_absent (rmem_false_iff.1 h)]

theorem rdel_length_le (o : KeyOps K) (m : RMap K Unit) (k : K) : (rdel o m k).length ≤ m.length :=
  List.length_filter_le _ _

theorem rset_length_le (o : KeyOps K) (m : RMap K Unit) (k : K) :
    (rset o m k ()).length ≤ m.length + 1 := by
  rw [rset, List.length_cons]
  have := rdel_length_le o m k
  omega

/-- `symdiff!` on reference sets: the members of exactly one of `m` and `L`. -/
theorem symdiff_fold {o : KeyOps K} (hl : o.Lawful) :
    ∀ (L m : RMap K Unit), Distinct o L →
      List.Perm (L.foldl (fun m e => rsym o m e.1) m)
        (m.filter (fun b => !rmem o L b.1) ++ L.filter (fun e => !rmem o m e.1))
  | [], m, _ => by
    show List.Perm m (m.filter (fun b => !rmem o [] b.1) ++ [])
    rw [List.append_nil]
    exact perm_of_eq' (List.filter_eq_self.2 (fun _ _ => rfl)).symm
  | (k, ()) :: L, m, hd => by
    obtain ⟨hd1, hd2⟩ := List.pairwise_cons.1 hd
    have hkL : rmem o L k = false := rmem_false_iff.2 hd1
    have hLk : ∀ e ∈ L, o.eq e.1 k = false := fun e he => eq_false_symm hl (hd1 e he)
    show List.Perm (L.foldl (fun m e => rsym o m e.1) (rsym o m k)) _
    cases hm : rmem o m k with
    | true =>
      rw [rsym_of_mem hm]
      refine (symdiff_fold hl L _ hd2).trans (perm_of_eq' ?_)
      have h1 : ((k, ()) :: L).filter (fun e => !rmem o m e.1) = L.filter (fun e => !rmem o m e.1) :=
        List.filter_cons_of_neg (by simp [hm])
      have h2 : L.filter (fun e => !rmem o (rdel o m k) e.1) = L.filter (fun e => !rmem o m e.1) := by
        apply List.filter_congr
        intro e he
        show (!rmem o (rdel o m k) e.1) = !rmem o m e.1
        rw [rmem_rdel hl, hLk e he, Bool.not_false, Bool.and_true]
      rw [h1, h2, filter_rdel_notin hl]
    | false =>
      rw [rsym_of_not_mem hm, rset_of_not_mem hm]
      refine (symdiff_fold hl L _ hd2).trans ?_
      have h1 : ((k, ()) :: m).filter (fun b => !rmem o L b.1) =
          (k, ()) :: m.filter (fun b => !rmem o L b.1) :=
        List.filter_cons_of_pos (by simp [hkL])
      have h2 : L.filter (fun e => !rmem o ((k, ()) :: m) e.1) = L.filter (fun e => !rmem o m e.1) := by
        apply List.filter_congr
        intro e he
        show (!rmem o ((k, ()) :: m) e.1) = !rmem o m e.1
        rw [rmem_cons]
        show (!(o.eq e.1 k || rmem o m e.1)) = !rmem o m e.1
        rw [hLk e he, Bool.false_or]
      have h3 : m.filter (fun b => !rmem o ((k, ()) :: L) b.1) = m.filter (fun b => !rmem o L b.1) := by
        apply List.filter_congr
        intro b hb
        show (!rmem o ((k, ()) :: L) b.1) = !rmem o L b.1
        rw [rmem_cons]
        show (!(o.eq b.1 k || rmem o L b.1)) = !rmem o L b.1
        rw [eq_false_symm hl (rmem_false_iff.1 hm b hb), Bool.false_or]
      have h4 : ((k, ()) :: L).filter (fun e => !rmem o m e.1) =
          (k, ()) :: L.filter (fun e => !rmem o m e.1) :=
        List.filter_cons_of_pos (by simp [hm])
      rw [h1, h2, h3, h4]
      exact List.perm_middle.symm

/-! ## Pigeonhole -/

/-- Pairwise non-`isequal` members of `ms`, each `isequal` to a member of `mt`, are at most as
many as the members of `mt`. -/
theorem pigeon {o : KeyOps K} (hl : o.Lawful) :
    ∀ (ms mt : RMap K Unit), Distinct o ms → (∀ a ∈ ms, rmem o mt a.1 = true) →
      ms.length ≤ mt.length
  | [], _, _, _ => Nat.zero_le _
  | a :: ms, mt, hd, hin => by
    obtain ⟨hd1, hd2⟩ := List.pairwise_cons.1 hd
    obtain ⟨b, hb, hab⟩ := rmem_true_iff.1 (hin a List.mem_cons_self)
    obtain ⟨l₁, l₂, hsp⟩ := List.append_of_mem hb
    have ih := pigeon hl ms (l₁ ++ l₂) hd2 (fun a' ha' => by
      obtain ⟨b', hb', hab'⟩ := rmem_true_iff.1 (hin a' (List.mem_cons_of_mem _ ha'))
      rw [hsp, List.mem_append, List.mem_cons] at hb'
      apply rmem_true_iff.2
      rcases hb' with h | h | h
      · exact ⟨b', List.mem_append.2 (Or.inl h), hab'⟩
      · rw [h] at hab'
        have hx : o.eq a.1 a'.1 = false := hd1 a' ha'
        rw [hl.trans a.1 b.1 a'.1 hab (hl.symm a'.1 b.1 hab')] at hx
        cases hx
      · exact ⟨b', List.mem_append.2 (Or.inr h), hab'⟩)
    rw [hsp]
    simp only [List.length_append, List.length_cons] at ih ⊢
    omega

/-- The same with a member of `mt` missing from `ms`: strictly fewer. -/
theorem pigeon_lt {o : KeyOps K} (hl : o.Lawful) {ms mt : RMap K Unit} (hd : Distinct o ms)
    (hin : ∀ a ∈ ms, rmem o mt a.1 = true) {b : K × Unit} (hb : b ∈ mt)
    (hout : rmem o ms b.1 = false) : ms.length < mt.length := by
  obtain ⟨l₁, l₂, hsp⟩ := List.append_of_mem hb
  have hle := pigeon hl ms (l₁ ++ l₂) hd (fun a ha => by
    obtain ⟨b', hb', hab'⟩ := rmem_true_iff.1 (hin a ha)
    rw [hsp, List.mem_append, List.mem_cons] at hb'
    apply rmem_true_iff.2
    rcases hb' with h | h | h
    · exact ⟨b', List.mem_append.2 (Or.inl h), hab'⟩
    · rw [h] at hab'
      have hx : o.eq b.1 a.1 = false := rmem_false_iff.1 hout a ha
      rw [hl.symm a.1 b.1 hab'] at hx
      cases hx
    · exact ⟨b', List.mem_append.2 (Or.inr h), hab'⟩)
  rw [hsp]
  simp only [List.length_append, List.length_cons] at hle ⊢
  omega

/-- Equal lengths and inclusion give the reverse inclusion. -/
theorem all_rev {o : KeyOps K} (hl : o.Lawful) {ms mt : RMap K Unit} (hd : Distinct o ms)
    (hlen : ms.length = mt.length) (h : (ms.all fun e => rmem o mt e.1) = true) :
    (mt.all fun e => rmem o ms e.1) = true := by
  apply List.all_eq_true.2
  intro b hb
  show rmem o ms b.1 = true
  cases hout : rmem o ms b.1
  · exact absurd (pigeon_lt hl hd (fun a ha => List.all_eq_true.1 h a ha) hb hout) (by omega)
  · rfl

end JuliaLean.Dicts.SetProofs
