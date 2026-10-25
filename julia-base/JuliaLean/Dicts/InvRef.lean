import JuliaLean.Dicts.Ops

/-!
# Reference maps

Lemmas about the association-list semantics of `Ops.lean`: lookups in lists
with pairwise non-`isequal` keys, and the effect of `rset`/`rdel`.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-- Keys pairwise non-`isequal`. -/
abbrev Distinct (o : KeyOps K) (m : RMap K V) : Prop := m.Pairwise (fun a b => o.eq a.1 b.1 = false)

theorem eq_false_symm {o : KeyOps K} (hl : o.Lawful) {a b : K} (h : o.eq a b = false) :
    o.eq b a = false := by
  cases hb : o.eq b a
  · rfl
  · rw [hl.symm b a hb] at h; cases h

theorem eq_trans' {o : KeyOps K} (hl : o.Lawful) {q a b : K} (h1 : o.eq q a = true)
    (h2 : o.eq q b = true) : o.eq a b = true :=
  hl.trans a q b (hl.symm q a h1) h2

theorem Distinct.perm {o : KeyOps K} (hl : o.Lawful) {m m' : RMap K V} (h : Distinct o m)
    (hp : List.Perm m m') : Distinct o m' :=
  hp.pairwise h (fun h => eq_false_symm hl h)

theorem rfind_of_mem {o : KeyOps K} (hl : o.Lawful) {m : RMap K V} (hd : Distinct o m) {q : K}
    {e : K × V} (he : e ∈ m) (hq : o.eq q e.1 = true) : rfind o m q = some e := by
  induction m with
  | nil => cases he
  | cons a m ih =>
    replace hd := List.pairwise_cons.1 hd
    unfold rfind
    by_cases ha : o.eq q a.1 = true
    · rw [List.find?_cons_of_pos (p := fun e : K × V => o.eq q e.1) ha]
      rcases List.mem_cons.1 he with h | h
      · rw [h]
      · have h1 := hd.1 e h
        rw [eq_trans' hl ha hq] at h1
        cases h1
    · rw [List.find?_cons_of_neg (p := fun e : K × V => o.eq q e.1) ha]
      rcases List.mem_cons.1 he with h | h
      · subst h; exact absurd hq ha
      · exact ih hd.2 h

theorem rfind_none {o : KeyOps K} {m : RMap K V} {q : K} (h : ∀ e ∈ m, o.eq q e.1 = false) :
    rfind o m q = none := by
  unfold rfind
  rw [List.find?_eq_none]
  intro x hx
  have := h x hx
  simp [this]

theorem rfind_some {o : KeyOps K} {m : RMap K V} {q : K} {e : K × V} (h : rfind o m q = some e) :
    e ∈ m ∧ o.eq q e.1 = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some (p := fun e : K × V => o.eq q e.1) h⟩

theorem rfind_eq_none_iff {o : KeyOps K} {m : RMap K V} {q : K} :
    rfind o m q = none ↔ ∀ e ∈ m, o.eq q e.1 = false := by
  unfold rfind
  rw [List.find?_eq_none]
  constructor
  · intro h e he
    cases hq : o.eq q e.1
    · rfl
    · exact absurd hq (h e he)
  · intro h e he
    have := h e he
    simp [this]

/-- Lookups only depend on the elements of a distinct list. -/
theorem rfind_perm {o : KeyOps K} (hl : o.Lawful) {m m' : RMap K V} (hd : Distinct o m)
    (hp : List.Perm m m') (q : K) : rfind o m q = rfind o m' q := by
  have hd' := hd.perm hl hp
  cases h : rfind o m q with
  | none =>
    symm
    rw [rfind_eq_none_iff] at h ⊢
    exact fun e he => h e (hp.mem_iff.2 he)
  | some e =>
    have := rfind_some h
    exact (rfind_of_mem hl hd' (hp.mem_iff.1 this.1) this.2).symm

theorem distinct_filter {o : KeyOps K} {m : RMap K V} (h : Distinct o m) (p : K × V → Bool) :
    Distinct o (m.filter p) :=
  List.Pairwise.sublist List.filter_sublist h

theorem distinct_rset {o : KeyOps K} {m : RMap K V} (h : Distinct o m) (k : K)
    (v : V) : Distinct o (rset o m k v) := by
  unfold rset rdel
  refine List.pairwise_cons.2 ⟨fun b hb => ?_, distinct_filter h _⟩
  show o.eq k b.1 = false
  rw [List.mem_filter] at hb
  cases hk : o.eq k b.1
  · rfl
  · rw [hk] at hb; exact absurd hb.2 (by decide)

theorem distinct_rdel {o : KeyOps K} {m : RMap K V} (h : Distinct o m) (k : K) :
    Distinct o (rdel o m k) := distinct_filter h _

theorem mem_rdel {o : KeyOps K} {m : RMap K V} {k : K} {e : K × V} :
    e ∈ rdel o m k ↔ e ∈ m ∧ o.eq k e.1 = false := by
  unfold rdel
  rw [List.mem_filter]
  cases o.eq k e.1 <;> simp

theorem mem_rset {o : KeyOps K} {m : RMap K V} {k : K} {v : V} {e : K × V} :
    e ∈ rset o m k v ↔ e = (k, v) ∨ (e ∈ m ∧ o.eq k e.1 = false) := by
  unfold rset
  rw [List.mem_cons, mem_rdel]

end JuliaLean.Dicts
