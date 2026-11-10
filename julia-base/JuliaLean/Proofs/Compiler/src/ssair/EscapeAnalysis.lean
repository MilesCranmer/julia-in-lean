import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.ssair.EscapeAnalysis

/-!
Properties of `Compiler/src/ssair/EscapeAnalysis.jl` (the `EscapeInfo` lattice, the escape
queries, the `ignore_*` constructors and the interprocedural summaries). The model is
`JuliaLean/Compiler/src/ssair/EscapeAnalysis.lean`.

What the optimizer reads at f755f49a9e41: `has_no_escape` and `getaliases` on the result of
`analyze_escapes` for finalizer inlining (`Compiler/src/ssair/passes.jl:1846-1851`), and
`has_no_escape(ignore_argescape(x))` for the `:effect_free` refinement
(`Compiler/src/optimize.jl:827-848`); the `ArgEscapeCache` summaries feed `escape_invoke!` in
callers. Every change the fixed point makes is a `⊔ₑ` (`_propagate_escape_change!`, line 734),
so the soundness facts these uses rely on are: each query is monotone along `⊔ₑ` (a join never
reports less escape than either argument) and along `⊑ₑ`. Those are proven below for every
`EscapeInfo` and heap, with no precondition. Each query is also pinned exactly: by its value on
every constructor, by an exact join law where one holds, and, for the `Liveness` queries, by
the effect of an in-place `push!`. `⊔ₑ` is described field by field (`compiler-escape-join-exact`)
and `==` exactly (`compiler-escape-eq-sets`); from these the join is commutative, idempotent and
absorbing up to `==`, and an upper bound in `⊑ₑ` apart from the zero-field case. The order `⊑ₑ` itself breaks its own laws (it is
not transitive, it disagrees with `⊔ₑ`, it is not an upper-bound order for `⊔ₑ`, and its `⊥`
fast path disagrees with `==`); `⊑ₑ` is reached in the analysis only through `has_all_escape`
(`⊤ ⊑ₑ x`), which stops at the fast path, so these have no effect on the optimizer.

Sections: helper lemmas on the set and heap encodings; `⊑ₑ` and `⊔ₑ` case lemmas; the query
lemmas; constructors and summaries; refutations; the registry entries.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.EscapeAnalysis

open JuliaLean.Registry
open JuliaLean.Compiler.ssair.EA

/-! ## Helper lemmas -/


@[simp] theorem tset_beq_top (t : TSet) : (t == TSet.top) = decide (t = .top) := by cases t <;> rfl
@[simp] theorem tset_beq_bot (t : TSet) : (t == TSet.bot) = decide (t = .bot) := by cases t <;> rfl
@[simp] theorem lref_beq_top (t : LRef) : (t == LRef.top) = decide (t = .top) := by cases t <;> rfl
@[simp] theorem lref_beq_bot (t : LRef) : (t == LRef.bot) = decide (t = .bot) := by cases t <;> rfl
@[simp] theorem alias_beq_bool (t : AliasInfo) (b : Bool) :
    (t == AliasInfo.bool b) = decide (t = .bool b) := by
  cases t with
  | bool c => cases b <;> cases c <;> rfl
  | _ => rfl

theorem intset_mem (s : IntSet) (a : Int) : s.mem a = true ↔ a ∈ s := by
  simp [IntSet.mem]
theorem intset_mem_union (a b : IntSet) (x : Int) :
    (IntSet.union a b).mem x = true ↔ a.mem x = true ∨ b.mem x = true := by
  simp [IntSet.mem, IntSet.union, IntSet.norm, List.mem_eraseDups, List.mem_mergeSort]
theorem intset_subset (a b : IntSet) :
    IntSet.subset a b = true ↔ ∀ x, a.mem x = true → b.mem x = true := by
  simp [IntSet.subset, IntSet.mem]

def RefOk (h : Heap) : LRef → Prop
  | .ref n => n < h.sets.size
  | _ => True

theorem get_alloc_old (h : Heap) (s : IntSet) (r : LRef) (hr : RefOk h r) :
    (h.alloc s).2.get r = h.get r := by
  cases r with
  | ref n =>
    simp [RefOk] at hr
    have hne : n ≠ h.sets.size := by omega
    simp [Heap.alloc, Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_push, hne]
  | _ => rfl

theorem get_alloc_new (h : Heap) (s : IntSet) : (h.alloc s).2.get (h.alloc s).1 = s := by
  simp [Heap.alloc, Heap.get, Array.getD_eq_getD_getElem?]

theorem refok_alloc (h : Heap) (s : IntSet) (r : LRef) (hr : RefOk h r) : RefOk (h.alloc s).2 r := by
  cases r with
  | ref n => simp [RefOk, Heap.alloc] at *; omega
  | _ => trivial

def jthrown (x y : EscapeInfo) : TSet :=
  if x.thrown == .top || y.thrown == .top then .top
  else if x.thrown == .bot then y.thrown
  else if y.thrown == .bot then x.thrown
  else .fresh (IntSet.union x.thrown.elems y.thrown.elems)

def jlive (h : Heap) (x y : EscapeInfo) : LRef × Heap :=
  if x.live == .top || y.live == .top then (LRef.top, h)
  else if x.live == .bot then (y.live, h)
  else if y.live == .bot then (x.live, h)
  else h.alloc (IntSet.union (h.get x.live) (h.get y.live))

theorem join_slow (h : Heap) (x y : EscapeInfo) (ht : (isTop x || isTop y) = false)
    (hbx : isBot x = false) (hby : isBot y = false) :
    join h x y = (⟨x.analyzed || y.analyzed, x.returnEscape || y.returnEscape, jthrown x y,
      mergeAliasInfo x.alias y.alias, (jlive h x y).1⟩, (jlive h x y).2) := by
  unfold join
  simp only [ht, hbx, hby, Bool.false_eq_true, ite_false]
  rfl

theorem sqsub_true (h : Heap) (x y : EscapeInfo) (H : sqsub h x y = .ok true) :
    isTop y = true ∨ (isTop x = false ∧ isBot x = true) ∨
    (isTop y = false ∧ isTop x = false ∧ isBot y = false ∧
     (x.analyzed = true → y.analyzed = true) ∧ (x.returnEscape = true → y.returnEscape = true) ∧
     (x.thrown = .top → y.thrown = .top) ∧
     (y.thrown ≠ .top → IntSet.subset x.thrown.elems y.thrown.elems = true) ∧
     (x.live = .top → y.live = .top) ∧
     (y.live ≠ .top → IntSet.subset (h.get x.live) (h.get y.live) = true)) := by
  unfold sqsub at H
  by_cases t1 : isTop y = true
  · exact Or.inl t1
  simp only [t1] at H
  by_cases t2 : isTop x = true
  · simp [t2, pure, Except.pure] at H
  simp only [t2] at H
  by_cases t3 : isBot x = true
  · exact Or.inr (Or.inl ⟨by simpa using t2, t3⟩)
  simp only [t3] at H
  by_cases t4 : isBot y = true
  · simp [t4, pure, Except.pure] at H
  simp only [t4] at H
  right; right
  simp at t1 t2 t3 t4
  refine ⟨by simpa using t1, by simpa using t2, by simpa using t4, ?_⟩
  revert H
  cases x with | mk xa xr xt xal xl =>
  cases y with | mk ya yr yt yal yl =>
  simp only
  intro H
  simp only [isTop, isBot, Bool.and_eq_false_iff] at t1 t2 t3 t4
  cases xal <;> cases yal <;> simp only at H
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (intro A; apply Classical.byContradiction; intro B; try simp at B)
  all_goals (simp [A, B, pure, Except.pure, bind, Except.bind, bne] at H)
  all_goals (repeat' (split at H)) <;> simp at H

theorem isTop_fields {x : EscapeInfo} (H : isTop x = true) :
    x.analyzed = true ∧ x.returnEscape = true ∧ x.thrown = .top ∧ x.alias = .bool true ∧ x.live = .top := by
  simpa [isTop, and_assoc] using H
theorem isBot_fields {x : EscapeInfo} (H : isBot x = true) :
    x.analyzed = false ∧ x.returnEscape = false ∧ x.thrown = .bot ∧ x.alias = .bool false ∧ x.live = .bot := by
  simpa [isBot, and_assoc] using H

theorem hasAllEscape_iff (h : Heap) (x : EscapeInfo) : hasAllEscape h x = .ok true ↔ isTop x = true := by
  unfold hasAllEscape sqsub
  by_cases t : isTop x = true
  · simp [t, pure, Except.pure]
  · simp only [isTop, Bool.and_eq_true] at t
    simp [isTop, allEscape, pure, Except.pure, and_assoc]

theorem mem_nil_false (a : Int) : IntSet.mem [] a = false := rfl

theorem subset_mem {a b : IntSet} (H : IntSet.subset a b = true) {v : Int} (hv : a.mem v = true) :
    b.mem v = true := (intset_subset a b).1 H v hv

theorem isEmpty_of_subset_nil {a : IntSet} (H : IntSet.subset a [] = true) : a.isEmpty = true := by
  cases a with
  | nil => rfl
  | cons v t =>
    have := subset_mem H (v := v) (by simp [IntSet.mem])
    simp [IntSet.mem] at this

theorem elems_top_mem : TSet.top.elems.mem (-1) = true := by decide
theorem get_top_mem0 (h : Heap) : (h.get .top).mem 0 = true := by
  show IntSet.mem [-1, 0] 0 = true; decide
theorem get_top_memm1 (h : Heap) : (h.get .top).mem (-1) = true := by
  show IntSet.mem [-1, 0] (-1) = true; decide

/-- Monotonicity of has_no_escape along ⊑ₑ. -/
theorem noEscape_sqsub (h : Heap) (x y : EscapeInfo) (H : sqsub h x y = .ok true)
    (hy : hasNoEscape h y = true) : hasNoEscape h x = true := by
  rcases sqsub_true h x y H with t | ⟨_, b⟩ | ⟨_, _, _, _, hr, ht1, ht2, hl1, hl2⟩
  · have := isTop_fields t; simp [hasNoEscape, this.2.1] at hy
  · have := isBot_fields b; simp [hasNoEscape, this.2.1, this.2.2.1, this.2.2.2.2, TSet.elems, Heap.get, IntSet.mem]
  · simp only [hasNoEscape, Bool.and_eq_true, Bool.not_eq_true'] at hy ⊢
    obtain ⟨⟨r, e⟩, l⟩ := hy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · cases hx : x.returnEscape
      · rfl
      · simp [hr hx] at r
    · have hyt : y.thrown ≠ .top := by intro c; simp [c, TSet.elems] at e
      have := ht2 hyt
      cases hye : y.thrown.elems with
      | nil => rw [hye] at this; exact isEmpty_of_subset_nil this
      | cons _ _ => simp [hye] at e
    · have hyl : y.live ≠ .top := by intro c; rw [c] at l; simp [get_top_mem0] at l
      cases hx : (h.get x.live).mem 0
      · rfl
      · have := subset_mem (hl2 hyl) hx; simp [this] at l

theorem argEscape_sqsub (h : Heap) (x y : EscapeInfo) (H : sqsub h x y = .ok true)
    (hx : hasArgEscape h x = true) : hasArgEscape h y = true := by
  rcases sqsub_true h x y H with t | ⟨_, b⟩ | ⟨_, _, _, _, _, _, _, hl1, hl2⟩
  · simp [hasArgEscape, (isTop_fields t).2.2.2.2, get_top_mem0]
  · simp [hasArgEscape, (isBot_fields b).2.2.2.2, Heap.get, IntSet.mem] at hx
  · unfold hasArgEscape at *
    by_cases c : y.live = .top
    · simp [c, get_top_mem0]
    · exact subset_mem (hl2 c) hx

theorem returnEscape_sqsub (h : Heap) (x y : EscapeInfo) (H : sqsub h x y = .ok true)
    (hx : hasReturnEscape x = true) : hasReturnEscape y = true := by
  rcases sqsub_true h x y H with t | ⟨_, b⟩ | ⟨_, _, _, _, hr, _⟩
  · simp [hasReturnEscape, (isTop_fields t).2.1]
  · simp [hasReturnEscape, (isBot_fields b).2.1] at hx
  · exact hr hx

theorem returnEscapeAt_sqsub (h : Heap) (x y : EscapeInfo) (pc : Int) (H : sqsub h x y = .ok true)
    (hx : hasReturnEscapeAt h x pc = true) : hasReturnEscapeAt h y pc = true := by
  rcases sqsub_true h x y H with t | ⟨_, b⟩ | ⟨_, _, _, _, hr, _, _, hl1, hl2⟩
  · simp [hasReturnEscapeAt, (isTop_fields t).2.1, (isTop_fields t).2.2.2.2, get_top_memm1]
  · simp [hasReturnEscapeAt, (isBot_fields b).2.1] at hx
  · simp only [hasReturnEscapeAt, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
    refine ⟨hr hx.1, ?_⟩
    by_cases c : y.live = .top
    · simp [c, get_top_memm1]
    · rcases hx.2 with m | m
      · exact Or.inl (subset_mem (hl2 c) m)
      · exact Or.inr (subset_mem (hl2 c) m)

theorem thrownEscape_sqsub (h : Heap) (x y : EscapeInfo) (H : sqsub h x y = .ok true)
    (hx : hasThrownEscape x = true) : hasThrownEscape y = true := by
  rcases sqsub_true h x y H with t | ⟨_, b⟩ | ⟨_, _, _, _, _, ht1, ht2, _⟩
  · simp [hasThrownEscape, (isTop_fields t).2.2.1, TSet.elems]
  · simp [hasThrownEscape, (isBot_fields b).2.2.1, TSet.elems] at hx
  · unfold hasThrownEscape at *
    by_cases c : y.thrown = .top
    · simp [c, TSet.elems]
    · have hs := ht2 c
      cases he : x.thrown.elems with
      | nil => simp [he] at hx
      | cons v t =>
        have := subset_mem hs (v := v) (by simp [he, IntSet.mem])
        cases hy : y.thrown.elems with
        | nil => simp [hy, IntSet.mem] at this
        | cons _ _ => rfl

theorem thrownEscapeAt_sqsub (h : Heap) (x y : EscapeInfo) (pc : Int) (H : sqsub h x y = .ok true)
    (hx : hasThrownEscapeAt x pc = true) : hasThrownEscapeAt y pc = true := by
  rcases sqsub_true h x y H with t | ⟨_, b⟩ | ⟨_, _, _, _, _, ht1, ht2, _⟩
  · simp [hasThrownEscapeAt, (isTop_fields t).2.2.1, elems_top_mem]
  · simp [hasThrownEscapeAt, (isBot_fields b).2.2.1, TSet.elems, IntSet.mem] at hx
  · simp only [hasThrownEscapeAt, Bool.or_eq_true] at hx ⊢
    by_cases c : y.thrown = .top
    · simp [c, elems_top_mem]
    · rcases hx with m | m
      · exact Or.inl (subset_mem (ht2 c) m)
      · exact Or.inr (subset_mem (ht2 c) m)

theorem allEscape_sqsub (h : Heap) (x y : EscapeInfo) (H : sqsub h x y = .ok true)
    (hx : hasAllEscape h x = .ok true) : hasAllEscape h y = .ok true := by
  rw [hasAllEscape_iff] at hx ⊢
  rcases sqsub_true h x y H with t | ⟨t2, _⟩ | ⟨_, t2, _⟩
  · exact t
  · simp [hx] at t2
  · simp [hx] at t2

/-! join -/

theorem join_cases (h : Heap) (x y : EscapeInfo) :
    ((isTop x || isTop y) = true ∧ join h x y = (allEscape, h)) ∨
    ((isTop x || isTop y) = false ∧ isBot x = true ∧ join h x y = (y, h)) ∨
    ((isTop x || isTop y) = false ∧ isBot x = false ∧ isBot y = true ∧ join h x y = (x, h)) ∨
    ((isTop x || isTop y) = false ∧ isBot x = false ∧ isBot y = false ∧
      join h x y = (⟨x.analyzed || y.analyzed, x.returnEscape || y.returnEscape, jthrown x y,
        mergeAliasInfo x.alias y.alias, (jlive h x y).1⟩, (jlive h x y).2)) := by
  cases t : (isTop x || isTop y)
  · cases bx : isBot x
    · cases by_ : isBot y
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, join_slow h x y t bx by_⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, by simp [join, t, bx, by_]⟩))
    · exact Or.inr (Or.inl ⟨rfl, rfl, by simp [join, t, bx]⟩)
  · exact Or.inl ⟨rfl, by simp [join, t]⟩

theorem jthrown_spec (x y : EscapeInfo) :
    (jthrown x y = .top ∧ (x.thrown = .top ∨ y.thrown = .top)) ∨
    (∀ a, (jthrown x y).elems.mem a = true ↔ x.thrown.elems.mem a = true ∨ y.thrown.elems.mem a = true) := by
  unfold jthrown
  by_cases c : (x.thrown == .top || y.thrown == .top) = true
  · left; simp only [c, ite_true]; simpa using c
  · right; simp only [c]
    simp at c
    by_cases bx : x.thrown = .bot
    · simp [bx, TSet.elems, IntSet.mem]
    · by_cases bY : y.thrown = .bot
      · simp [bx, bY, TSet.elems, IntSet.mem]
      · simp only [tset_beq_bot, bx, bY, decide_false, Bool.false_eq_true, ite_false]
        intro a; exact intset_mem_union _ _ a

theorem jlive_spec (h : Heap) (x y : EscapeInfo) :
    ((jlive h x y).1 = .top ∧ (x.live = .top ∨ y.live = .top)) ∨
    (∀ a, ((jlive h x y).2.get (jlive h x y).1).mem a = true ↔
      (h.get x.live).mem a = true ∨ (h.get y.live).mem a = true) := by
  unfold jlive
  by_cases c : (x.live == .top || y.live == .top) = true
  · left; simp only [c, ite_true]; simpa using c
  · right; simp only [c]
    simp at c
    by_cases bx : x.live = .bot
    · simp [bx, Heap.get, IntSet.mem]
    · by_cases bY : y.live = .bot
      · simp [bx, bY, Heap.get, IntSet.mem]
      · simp only [lref_beq_bot, bx, bY, decide_false, Bool.false_eq_true, ite_false]
        intro a; rw [get_alloc_new]; exact intset_mem_union _ _ a

theorem isEmpty_iff_mem (l : IntSet) : l.isEmpty = true ↔ ∀ a, l.mem a = false := by
  cases l with
  | nil => simp [IntSet.mem]
  | cons v t => simp only [List.isEmpty_cons, Bool.false_eq_true, false_iff]; intro H; have := H v; simp [IntSet.mem] at this

theorem bot_noEscape (h : Heap) {x : EscapeInfo} (b : isBot x = true) : hasNoEscape h x = true := by
  have := isBot_fields b
  simp [hasNoEscape, this.2.1, this.2.2.1, this.2.2.2.2, TSet.elems, Heap.get, IntSet.mem]

theorem noEscape_join (h : Heap) (x y : EscapeInfo)
    (H : hasNoEscape (join h x y).2 (join h x y).1 = true) :
    hasNoEscape h x = true ∧ hasNoEscape h y = true := by
  rcases join_cases h x y with ⟨_, e⟩ | ⟨_, bx, e⟩ | ⟨_, _, by_, e⟩ | ⟨_, _, _, e⟩ <;> rw [e] at H
  · simp [hasNoEscape, allEscape] at H
  · exact ⟨bot_noEscape h bx, H⟩
  · exact ⟨H, bot_noEscape h by_⟩
  · simp only [hasNoEscape, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at H ⊢
    obtain ⟨⟨⟨rx, ry⟩, et⟩, l⟩ := H
    have et' : ∀ a, (jthrown x y).elems.mem a = false := (isEmpty_iff_mem _).1 et
    rcases jthrown_spec x y with ⟨tt, _⟩ | ti
    · have := et' (-1); rw [tt] at this; simp [elems_top_mem] at this
    rcases jlive_spec h x y with ⟨lt, _⟩ | li
    · rw [lt] at l; simp [get_top_mem0] at l
    have hx0 : ∀ a, x.thrown.elems.mem a = false := fun a => by
      have := et' a; cases c : x.thrown.elems.mem a <;> simp_all
    have hy0 : ∀ a, y.thrown.elems.mem a = false := fun a => by
      have := et' a; cases c : y.thrown.elems.mem a <;> simp_all
    have lx : (h.get x.live).mem 0 = false := by
      cases c : (h.get x.live).mem 0
      · rfl
      · have := (li 0).2 (Or.inl c); rw [l] at this; exact absurd this (by decide)
    have ly : (h.get y.live).mem 0 = false := by
      cases c : (h.get y.live).mem 0
      · rfl
      · have := (li 0).2 (Or.inr c); rw [l] at this; exact absurd this (by decide)
    exact ⟨⟨⟨rx, (isEmpty_iff_mem _).2 hx0⟩, lx⟩, ⟨⟨ry, (isEmpty_iff_mem _).2 hy0⟩, ly⟩⟩

theorem argEscape_join (h : Heap) (x y : EscapeInfo)
    (H : hasArgEscape h x = true ∨ hasArgEscape h y = true) :
    hasArgEscape (join h x y).2 (join h x y).1 = true := by
  rcases join_cases h x y with ⟨_, e⟩ | ⟨_, bx, e⟩ | ⟨_, _, by_, e⟩ | ⟨_, _, _, e⟩ <;> rw [e]
  · simp [hasArgEscape, allEscape, get_top_mem0]
  · rcases H with c | c
    · simp [hasArgEscape, (isBot_fields bx).2.2.2.2, Heap.get, IntSet.mem] at c
    · exact c
  · rcases H with c | c
    · exact c
    · simp [hasArgEscape, (isBot_fields by_).2.2.2.2, Heap.get, IntSet.mem] at c
  · simp only [hasArgEscape] at H ⊢
    rcases jlive_spec h x y with ⟨lt, _⟩ | li
    · rw [lt]; exact get_top_mem0 _
    · exact (li 0).2 H

theorem returnEscape_join (h : Heap) (x y : EscapeInfo)
    (H : hasReturnEscape x = true ∨ hasReturnEscape y = true) :
    hasReturnEscape (join h x y).1 = true := by
  rcases join_cases h x y with ⟨_, e⟩ | ⟨_, bx, e⟩ | ⟨_, _, by_, e⟩ | ⟨_, _, _, e⟩ <;> rw [e]
  · rfl
  · have := isBot_fields bx; simp [hasReturnEscape, this.2.1] at H; exact H
  · have := isBot_fields by_; simp [hasReturnEscape, this.2.1] at H; exact H
  · simpa [hasReturnEscape] using H

theorem returnEscapeAt_join (h : Heap) (x y : EscapeInfo) (pc : Int)
    (H : hasReturnEscapeAt h x pc = true ∨ hasReturnEscapeAt h y pc = true) :
    hasReturnEscapeAt (join h x y).2 (join h x y).1 pc = true := by
  rcases join_cases h x y with ⟨_, e⟩ | ⟨_, bx, e⟩ | ⟨_, _, by_, e⟩ | ⟨_, _, _, e⟩ <;> rw [e]
  · simp [hasReturnEscapeAt, allEscape, get_top_memm1]
  · rcases H with c | c
    · simp [hasReturnEscapeAt, (isBot_fields bx).2.1] at c
    · exact c
  · rcases H with c | c
    · exact c
    · simp [hasReturnEscapeAt, (isBot_fields by_).2.1] at c
  · simp only [hasReturnEscapeAt, Bool.and_eq_true, Bool.or_eq_true] at H ⊢
    refine ⟨by rcases H with ⟨r, _⟩ | ⟨r, _⟩ <;> simp [r], ?_⟩
    rcases jlive_spec h x y with ⟨lt, _⟩ | li
    · rw [lt]; exact Or.inl (get_top_memm1 _)
    · rcases H with ⟨_, m | m⟩ | ⟨_, m | m⟩
      · exact Or.inl ((li _).2 (Or.inl m))
      · exact Or.inr ((li _).2 (Or.inl m))
      · exact Or.inl ((li _).2 (Or.inr m))
      · exact Or.inr ((li _).2 (Or.inr m))

theorem nonempty_iff_mem (l : IntSet) : l.isEmpty = false ↔ ∃ a, l.mem a = true := by
  cases l with
  | nil => simp [IntSet.mem]
  | cons v t => simp only [List.isEmpty_cons, true_iff]; exact ⟨v, by simp [IntSet.mem]⟩

theorem hte_iff (x : EscapeInfo) : hasThrownEscape x = true ↔ ∃ a, x.thrown.elems.mem a = true := by
  unfold hasThrownEscape
  rw [Bool.not_eq_true', nonempty_iff_mem]

theorem hteAt_iff (x : EscapeInfo) (pc : Int) :
    hasThrownEscapeAt x pc = true ↔ x.thrown.elems.mem (-1) = true ∨ x.thrown.elems.mem pc = true := by
  unfold hasThrownEscapeAt; rw [Bool.or_eq_true]

theorem thrownEscape_join (h : Heap) (x y : EscapeInfo)
    (H : hasThrownEscape x = true ∨ hasThrownEscape y = true) :
    hasThrownEscape (join h x y).1 = true := by
  rcases join_cases h x y with ⟨_, e⟩ | ⟨_, bx, e⟩ | ⟨_, _, by_, e⟩ | ⟨_, _, _, e⟩ <;> rw [e]
  · rfl
  · rcases H with c | c
    · simp [hasThrownEscape, (isBot_fields bx).2.2.1, TSet.elems] at c
    · exact c
  · rcases H with c | c
    · exact c
    · simp [hasThrownEscape, (isBot_fields by_).2.2.1, TSet.elems] at c
  · rw [hte_iff]
    rcases jthrown_spec x y with ⟨tt, _⟩ | ti
    · show ∃ a, (jthrown x y).elems.mem a = true
      rw [tt]; exact ⟨-1, elems_top_mem⟩
    · rcases H with c | c <;> rw [hte_iff] at c <;> obtain ⟨a, m⟩ := c
      · exact ⟨a, (ti a).2 (Or.inl m)⟩
      · exact ⟨a, (ti a).2 (Or.inr m)⟩

theorem thrownEscapeAt_join (h : Heap) (x y : EscapeInfo) (pc : Int)
    (H : hasThrownEscapeAt x pc = true ∨ hasThrownEscapeAt y pc = true) :
    hasThrownEscapeAt (join h x y).1 pc = true := by
  rcases join_cases h x y with ⟨_, e⟩ | ⟨_, bx, e⟩ | ⟨_, _, by_, e⟩ | ⟨_, _, _, e⟩ <;> rw [e]
  · simp [hasThrownEscapeAt, allEscape, elems_top_mem]
  · rcases H with c | c
    · simp [hasThrownEscapeAt, (isBot_fields bx).2.2.1, TSet.elems, IntSet.mem] at c
    · exact c
  · rcases H with c | c
    · exact c
    · simp [hasThrownEscapeAt, (isBot_fields by_).2.2.1, TSet.elems, IntSet.mem] at c
  · rw [hteAt_iff]
    rcases jthrown_spec x y with ⟨tt, _⟩ | ti
    · show (jthrown x y).elems.mem (-1) = true ∨ _
      rw [tt]; exact Or.inl elems_top_mem
    · show (jthrown x y).elems.mem (-1) = true ∨ (jthrown x y).elems.mem pc = true
      rcases H with c | c <;> rw [hteAt_iff] at c <;> rcases c with m | m
      · exact Or.inl ((ti _).2 (Or.inl m))
      · exact Or.inr ((ti _).2 (Or.inl m))
      · exact Or.inl ((ti _).2 (Or.inr m))
      · exact Or.inr ((ti _).2 (Or.inr m))

theorem allEscape_join (h : Heap) (x y : EscapeInfo)
    (H : hasAllEscape h x = .ok true ∨ hasAllEscape h y = .ok true) :
    hasAllEscape (join h x y).2 (join h x y).1 = .ok true := by
  rw [hasAllEscape_iff, hasAllEscape_iff] at H
  rw [hasAllEscape_iff]
  have t : (isTop x || isTop y) = true := by rcases H with c | c <;> simp [c]
  simp [join, t]; rfl

theorem erase_mem (s : IntSet) (y a : Int) : (s.erase y).mem a = (s.mem a && a != y) := by
  simp only [IntSet.erase, IntSet.mem]
  cases h1 : s.contains a <;> cases h2 : (a != y) <;>
    simp_all [List.mem_filter, bne_iff_ne]

theorem ignoreArgescape_spec (h : Heap) (x : EscapeInfo) :
    hasArgEscape (ignoreArgescape h x).2 (ignoreArgescape h x).1 = false ∧
    hasNoEscape (ignoreArgescape h x).2 (ignoreArgescape h x).1 =
      (!x.returnEscape && x.thrown.elems.isEmpty) ∧
    hasReturnEscape (ignoreArgescape h x).1 = hasReturnEscape x ∧
    hasThrownEscape (ignoreArgescape h x).1 = hasThrownEscape x ∧
    (∀ pc, pc ≠ 0 → hasReturnEscapeAt (ignoreArgescape h x).2 (ignoreArgescape h x).1 pc =
      hasReturnEscapeAt h x pc) ∧
    (∀ pc, hasThrownEscapeAt (ignoreArgescape h x).1 pc = hasThrownEscapeAt x pc) := by
  refine ⟨?_, ?_, rfl, rfl, fun pc hpc => ?_, fun _ => rfl⟩
  · simp [ignoreArgescape, hasArgEscape, get_alloc_new, erase_mem]
  · simp [ignoreArgescape, hasNoEscape, get_alloc_new, erase_mem]
  · have hb : (pc != 0) = true := by simpa using hpc
    simp [ignoreArgescape, hasReturnEscapeAt, get_alloc_new, erase_mem, hb]

theorem ignoreThrownescapes_spec (h : Heap) (x : EscapeInfo) :
    hasThrownEscape (ignoreThrownescapes x) = false ∧
    (∀ pc, hasThrownEscapeAt (ignoreThrownescapes x) pc = false) ∧
    hasNoEscape h (ignoreThrownescapes x) = (!x.returnEscape && !(h.get x.live).mem 0) ∧
    hasReturnEscape (ignoreThrownescapes x) = hasReturnEscape x ∧
    hasArgEscape h (ignoreThrownescapes x) = hasArgEscape h x ∧
    (∀ pc, hasReturnEscapeAt h (ignoreThrownescapes x) pc = hasReturnEscapeAt h x pc) := by
  refine ⟨rfl, fun _ => rfl, ?_, rfl, rfl, fun _ => rfl⟩
  simp [hasNoEscape, ignoreThrownescapes, TSet.elems]

theorem ignoreLiveness_spec (h : Heap) (x : EscapeInfo) :
    hasArgEscape h (ignoreLiveness x) = false ∧
    (∀ pc, hasReturnEscapeAt h (ignoreLiveness x) pc = false) ∧
    hasNoEscape h (ignoreLiveness x) = (!x.returnEscape && x.thrown.elems.isEmpty) ∧
    hasReturnEscape (ignoreLiveness x) = hasReturnEscape x ∧
    hasThrownEscape (ignoreLiveness x) = hasThrownEscape x ∧
    (∀ pc, hasThrownEscapeAt (ignoreLiveness x) pc = hasThrownEscapeAt x pc) := by
  refine ⟨rfl, fun _ => ?_, ?_, rfl, rfl, fun _ => rfl⟩
  · simp [hasReturnEscapeAt, ignoreLiveness, Heap.get, IntSet.mem]
  · simp [hasNoEscape, ignoreLiveness, Heap.get, IntSet.mem]

theorem ignoreAliasinfo_spec (h : Heap) (x : EscapeInfo) :
    hasAllEscape h (ignoreAliasinfo x) = .ok false ∧
    hasNoEscape h (ignoreAliasinfo x) = hasNoEscape h x ∧
    hasArgEscape h (ignoreAliasinfo x) = hasArgEscape h x ∧
    hasReturnEscape (ignoreAliasinfo x) = hasReturnEscape x ∧
    (∀ pc, hasReturnEscapeAt h (ignoreAliasinfo x) pc = hasReturnEscapeAt h x pc) ∧
    hasThrownEscape (ignoreAliasinfo x) = hasThrownEscape x ∧
    (∀ pc, hasThrownEscapeAt (ignoreAliasinfo x) pc = hasThrownEscapeAt x pc) := by
  refine ⟨?_, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => rfl⟩
  simp [hasAllEscape, sqsub, isTop, ignoreAliasinfo, allEscape, pure, Except.pure]

theorem argEscapeInfo_bits (x : EscapeInfo) :
    (aHasAllEscape (argEscapeInfo x) = isTop x) ∧
    (aHasReturnEscape (argEscapeInfo x) = (!isTop x && hasReturnEscape x)) ∧
    (aHasThrownEscape (argEscapeInfo x) = (!isTop x && hasThrownEscape x)) ∧
    (aHasNoEscape (argEscapeInfo x) = (!isTop x && !hasReturnEscape x && !hasThrownEscape x)) := by
  unfold argEscapeInfo
  cases t : isTop x <;> cases r : hasReturnEscape x <;> cases e : hasThrownEscape x <;> decide

theorem interprocedural_spec (h : Heap) (x : EscapeInfo) (pc : Int) :
    (aHasAllEscape (argEscapeInfo x) = isTop x) ∧
    (aHasReturnEscape (argEscapeInfo x) = (!isTop x && hasReturnEscape x)) ∧
    (aHasThrownEscape (argEscapeInfo x) = (!isTop x && hasThrownEscape x)) ∧
    (aHasNoEscape (argEscapeInfo x) = (!isTop x && !hasReturnEscape x && !hasThrownEscape x)) ∧
    (isTop x = true → isTop (fromInterprocedural h (argEscapeInfo x) pc).1 = true) ∧
    (hasThrownEscape x = true → hasThrownEscapeAt (fromInterprocedural h (argEscapeInfo x) pc).1 pc = true) ∧
    (isTop x = false → hasReturnEscape (fromInterprocedural h (argEscapeInfo x) pc).1 = false ∧
      (fromInterprocedural h (argEscapeInfo x) pc).1.alias = .bool true ∧
      ((fromInterprocedural h (argEscapeInfo x) pc).2.get
        (fromInterprocedural h (argEscapeInfo x) pc).1.live) = [pc]) := by
  obtain ⟨ha, hr, ht, hn⟩ := argEscapeInfo_bits x
  refine ⟨ha, hr, ht, hn, fun t => ?_, fun e => ?_, fun t => ?_⟩
  · simp only [fromInterprocedural, ha, t, ite_true]; rfl
  · cases t : isTop x
    · simp only [fromInterprocedural, ha, ht, t, e, Bool.not_false, Bool.and_true,
        Bool.false_eq_true, ite_false, ite_true]
      show hasThrownEscapeAt ⟨true, false, .fresh [pc], .bool true, _⟩ pc = true
      simp [hasThrownEscapeAt, TSet.elems, IntSet.mem]
    · simp only [fromInterprocedural, ha, t, ite_true]; rfl
  · simp only [fromInterprocedural, ha, t, Bool.false_eq_true, ite_false]
    refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial | exact get_alloc_new _ _

theorem sqsubStrict_spec (h : Heap) (x y : EscapeInfo) :
    sqsubStrict h x x ≠ .ok true ∧
    (sqsubStrict h x y = .ok true → sqsub h x y = .ok true ∧ sqsub h y x = .ok false) := by
  unfold sqsubStrict
  constructor
  · cases e : sqsub h x x with
    | error _ => simp [bind, Except.bind]
    | ok b => cases b <;> simp [pure, Except.pure, bind, Except.bind]
  · cases e : sqsub h x y with
    | error _ => simp [bind, Except.bind]
    | ok b =>
      cases b
      · simp [pure, Except.pure, bind, Except.bind]
      · cases e2 : sqsub h y x with
        | error _ => simp [bind, Except.bind]
        | ok c => cases c <;> simp [pure, Except.pure, bind, Except.bind]

theorem sqsubNe_spec (h : Heap) (x y : EscapeInfo) (H : sqsub h x y = .ok true) :
    sqsubNe h x y = sqsubStrict h x y := by
  unfold sqsubNe sqsubStrict
  simp [H, pure, Except.pure, bind, Except.bind]

theorem mem_push (s : AInfo) (v k : Int) : k ∈ AInfo.push s v ↔ k ∈ s ∨ k = v := by
  unfold AInfo.push
  by_cases c : s.contains v = true
  · simp only [c, ite_true]
    constructor
    · exact Or.inl
    · rintro (m | rfl)
      · exact m
      · simpa using c
  · have c' : v ∉ s := by simpa using c
    simp [c']

theorem mem_ainfo_union (a b : AInfo) (k : Int) : k ∈ AInfo.union a b ↔ k ∈ a ∨ k ∈ b := by
  unfold AInfo.union
  induction b generalizing a with
  | nil => simp
  | cons v t ih =>
    simp only [List.foldl_cons]
    rw [ih, mem_push]
    simp [or_assoc, or_comm, or_left_comm]

theorem mem_mergeToUnindexable (info : AInfo) (infos : List AInfo) (k : Int) :
    k ∈ mergeToUnindexable info infos ↔ k ∈ info ∨ ∃ i ∈ infos, k ∈ i := by
  unfold mergeToUnindexable
  induction infos generalizing info with
  | nil => simp
  | cons v t ih =>
    simp only [List.foldl_cons]
    rw [ih, mem_ainfo_union]
    simp [or_assoc]

/-- `a`'s alias elements all appear in `b`, field by field where both are indexable. This is
the order `⊑ₑ` means to check on `AliasInfo`. -/
def AliasCovers : AliasInfo → AliasInfo → Prop
  | _, .bool true => True
  | .bool false, _ => True
  | .indexable xs, .indexable zs =>
    xs.length ≤ zs.length ∧ ∀ i k, i < xs.length → k ∈ xs.getD i [] → k ∈ zs.getD i []
  | .indexable xs, .unindexable z => ∀ i k, i < xs.length → k ∈ xs.getD i [] → k ∈ z
  | .unindexable x, .unindexable z => ∀ k, k ∈ x → k ∈ z
  | _, _ => False

theorem mergeAliasInfo_covers (xa ya : AliasInfo) :
    AliasCovers xa (mergeAliasInfo xa ya) ∧ AliasCovers ya (mergeAliasInfo xa ya) := by
  cases xa with
  | bool b =>
    cases b
    · cases ya with
      | bool c => cases c <;> simp [mergeAliasInfo, AliasCovers]
      | indexable ys =>
        simp [mergeAliasInfo, AliasCovers]
      | unindexable y =>
        simp [mergeAliasInfo, AliasCovers]
    · simp [mergeAliasInfo, AliasCovers]
  | indexable xs =>
    cases ya with
    | bool c => cases c <;> simp [mergeAliasInfo, AliasCovers]
    | indexable ys =>
      simp only [mergeAliasInfo, alias_beq_bool, reduceCtorEq, decide_false, Bool.or_false,
        Bool.false_eq_true, ite_false, AliasCovers, List.length_map, List.length_range]
      refine ⟨⟨Nat.le_max_left _ _, fun i k hi m => ?_⟩, ⟨Nat.le_max_right _ _, fun i k hi m => ?_⟩⟩
      · have hi' : i < max xs.length ys.length := Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi']
        simp only [Option.map_some, Option.getD_some]
        split
        · have : ys.length < xs.length := by omega
          simp only [this, ite_true]; exact m
        · rw [mem_ainfo_union]; exact Or.inl m
      · have hi' : i < max xs.length ys.length := Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _)
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi']
        simp only [Option.map_some, Option.getD_some]
        split
        · have : ¬ ys.length < xs.length := by omega
          simp only [this, ite_false]; exact m
        · rw [mem_ainfo_union]; exact Or.inr m
    | unindexable y =>
      simp only [mergeAliasInfo, alias_beq_bool, reduceCtorEq, decide_false, Bool.or_false,
        Bool.false_eq_true, ite_false, AliasCovers]
      refine ⟨fun i k hi m => ?_, fun k m => ?_⟩
      · rw [mem_mergeToUnindexable]; right
        refine ⟨xs.getD i [], ?_, m⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp
      · rw [mem_mergeToUnindexable]; exact Or.inl m
  | unindexable xi =>
    cases ya with
    | bool c => cases c <;> simp [mergeAliasInfo, AliasCovers]
    | indexable ys =>
      simp only [mergeAliasInfo, alias_beq_bool, reduceCtorEq, decide_false, Bool.or_false,
        Bool.false_eq_true, ite_false, AliasCovers]
      refine ⟨fun k m => ?_, fun i k hi m => ?_⟩
      · rw [mem_mergeToUnindexable]; exact Or.inl m
      · rw [mem_mergeToUnindexable]; right
        refine ⟨ys.getD i [], ?_, m⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp
    | unindexable y =>
      simp only [mergeAliasInfo, alias_beq_bool, reduceCtorEq, decide_false, Bool.or_false,
        Bool.false_eq_true, ite_false, AliasCovers]
      exact ⟨fun k m => (mem_ainfo_union _ _ _).2 (Or.inl m), fun k m => (mem_ainfo_union _ _ _).2 (Or.inr m)⟩

theorem seteq_refl (a : IntSet) : IntSet.seteq a a = true := by
  simp [IntSet.seteq, IntSet.subset]

theorem zip_seteq_refl (l : List AInfo) : ((l.zip l).all fun (p : AInfo × AInfo) => IntSet.seteq p.1 p.2) = true := by
  induction l with
  | nil => rfl
  | cons v t ih => simp only [List.zip_cons_cons, List.all_cons, seteq_refl, ih, Bool.and_self]

theorem eqE_refl (h : Heap) (x : EscapeInfo) : eqE h x x = true := by
  cases x with | mk a r t al l =>
  unfold eqE
  cases t <;> cases al <;> cases l <;>
    simp [seteq_refl, zip_seteq_refl, Id.run, bne] <;> rfl

theorem subset_refl' (a : IntSet) : IntSet.subset a a = true := by simp [IntSet.subset]

theorem zip_subset_refl (l : List AInfo) : ((l.zip l).all fun (p : AInfo × AInfo) => IntSet.subset p.1 p.2) = true := by
  induction l with
  | nil => rfl
  | cons v t ih => simp only [List.zip_cons_cons, List.all_cons, subset_refl', ih, Bool.and_self]

theorem sqsub_refl (h : Heap) (x : EscapeInfo) : sqsub h x x = .ok true := by
  cases x with | mk a r t al l =>
  unfold sqsub
  cases a <;> cases r <;> cases t <;> cases al <;> cases l <;>
    simp [subset_refl', zip_subset_refl, bne, isTop, isBot] <;> (try rfl) <;>
    (rename_i b; cases b <;> rfl)


/-! ## Exact descriptions of `merge_alias_info`, `⊔ₑ` and `==` -/

def mergeIdx (xinfos yinfos : List AInfo) : List AInfo :=
  let xn := xinfos.length
  let yn := yinfos.length
  let nmin := min xn yn
  let longer := if xn > yn then xinfos else yinfos
  (List.range (max xn yn)).map fun i =>
    if i + 1 > nmin then longer.getD i []
    else AInfo.union (xinfos.getD i []) (yinfos.getD i [])

theorem merge_idx_eq (xs ys : List AInfo) :
    mergeAliasInfo (.indexable xs) (.indexable ys) = .indexable (mergeIdx xs ys) := by
  simp [mergeAliasInfo, alias_beq_bool, mergeIdx]

theorem getD_ge (l : List AInfo) (i : Nat) (h : l.length ≤ i) : l.getD i [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem mergeIdx_length (xs ys : List AInfo) : (mergeIdx xs ys).length = max xs.length ys.length := by
  simp [mergeIdx]

theorem mem_mergeIdx (xs ys : List AInfo) (i : Nat) (k : Int) :
    k ∈ (mergeIdx xs ys).getD i [] ↔ k ∈ xs.getD i [] ∨ k ∈ ys.getD i [] := by
  by_cases hi : i < max xs.length ys.length
  · simp only [mergeIdx]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some]
    split
    · rename_i hgt
      split
      · rename_i hxy
        rw [getD_ge ys i (by omega)]; simp
      · rename_i hxy
        rw [getD_ge xs i (by omega)]; simp
    · exact mem_ainfo_union _ _ _
  · rw [getD_ge _ i (by rw [mergeIdx_length]; omega), getD_ge xs i (by omega), getD_ge ys i (by omega)]
    simp

theorem mem_mergeToUnindexable' (info : AInfo) (infos : List AInfo) (k : Int) :
    k ∈ mergeToUnindexable info infos ↔ k ∈ info ∨ ∃ i, k ∈ infos.getD i [] := by
  rw [mem_mergeToUnindexable]
  constructor
  · rintro (m | ⟨l, hl, m⟩)
    · exact Or.inl m
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      exact Or.inr ⟨i, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact m⟩
  · rintro (m | ⟨i, m⟩)
    · exact Or.inl m
    · by_cases hi : i < infos.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at m
        exact Or.inr ⟨_, List.getElem_mem hi, m⟩
      · rw [getD_ge _ _ (by omega)] at m; simp at m

/-- The exact result `merge_alias_info` is meant to compute. -/
def AliasExact (xa ya r : AliasInfo) : Prop :=
  match xa, ya with
  | .bool true, _ => r = .bool true
  | _, .bool true => r = .bool true
  | .bool false, _ => r = ya
  | _, .bool false => r = xa
  | .indexable xs, .indexable ys => ∃ zs, r = .indexable zs ∧ zs.length = max xs.length ys.length ∧
      ∀ i k, k ∈ zs.getD i [] ↔ k ∈ xs.getD i [] ∨ k ∈ ys.getD i []
  | .indexable xs, .unindexable y => ∃ z, r = .unindexable z ∧ ∀ k, k ∈ z ↔ k ∈ y ∨ ∃ i, k ∈ xs.getD i []
  | .unindexable x, .indexable ys => ∃ z, r = .unindexable z ∧ ∀ k, k ∈ z ↔ k ∈ x ∨ ∃ i, k ∈ ys.getD i []
  | .unindexable x, .unindexable y => ∃ z, r = .unindexable z ∧ ∀ k, k ∈ z ↔ k ∈ x ∨ k ∈ y

theorem mergeAliasInfo_exact (xa ya : AliasInfo) : AliasExact xa ya (mergeAliasInfo xa ya) := by
  cases xa with
  | bool b => cases b <;> cases ya <;> (try (rename_i c; cases c)) <;> simp [AliasExact, mergeAliasInfo, alias_beq_bool]
  | indexable xs =>
    cases ya with
    | bool c => cases c <;> simp [AliasExact, mergeAliasInfo, alias_beq_bool]
    | indexable ys =>
      rw [merge_idx_eq]
      exact ⟨_, rfl, mergeIdx_length xs ys, mem_mergeIdx xs ys⟩
    | unindexable y =>
      simp only [AliasExact, mergeAliasInfo, alias_beq_bool, reduceCtorEq, decide_false, Bool.or_false,
        Bool.false_eq_true, ite_false]
      exact ⟨_, rfl, mem_mergeToUnindexable' y xs⟩
  | unindexable x =>
    cases ya with
    | bool c => cases c <;> simp [AliasExact, mergeAliasInfo, alias_beq_bool]
    | indexable ys =>
      simp only [AliasExact, mergeAliasInfo, alias_beq_bool, reduceCtorEq, decide_false, Bool.or_false,
        Bool.false_eq_true, ite_false]
      exact ⟨_, rfl, mem_mergeToUnindexable' x ys⟩
    | unindexable y =>
      simp only [AliasExact, mergeAliasInfo, alias_beq_bool, reduceCtorEq, decide_false, Bool.or_false,
        Bool.false_eq_true, ite_false]
      exact ⟨_, rfl, mem_ainfo_union x y⟩

/-- Two `AliasInfo`s hold the same alias elements; this is what `==` tests. -/
def AliasEquiv : AliasInfo → AliasInfo → Prop
  | .bool a, .bool b => a = b
  | .indexable xs, .indexable ys => xs.length = ys.length ∧ ∀ i k, k ∈ xs.getD i [] ↔ k ∈ ys.getD i []
  | .unindexable x, .unindexable y => ∀ k, k ∈ x ↔ k ∈ y
  | _, _ => False

theorem aliasEquiv_refl (a : AliasInfo) : AliasEquiv a a := by
  cases a <;> simp [AliasEquiv]

theorem exact_idem (a r : AliasInfo) (H : AliasExact a a r) : AliasEquiv r a := by
  cases a with
  | bool b => cases b <;> simp [AliasExact] at H <;> subst H <;> exact aliasEquiv_refl _
  | indexable xs =>
    obtain ⟨zs, rfl, hl, hm⟩ := H
    exact ⟨by simp [hl], fun i k => by rw [hm]; exact or_self_iff⟩
  | unindexable x =>
    obtain ⟨z, rfl, hm⟩ := H
    exact fun k => by rw [hm]; exact or_self_iff

theorem exact_comm (a b r r' : AliasInfo) (H : AliasExact a b r) (H' : AliasExact b a r') : AliasEquiv r r' := by
  cases a with
  | bool c =>
    cases c <;> cases b <;> (try (rename_i d; cases d)) <;> simp only [AliasExact] at H H' <;> subst H H' <;>
      exact aliasEquiv_refl _
  | indexable xs =>
    cases b with
    | bool d => cases d <;> simp only [AliasExact] at H H' <;> subst H H' <;> exact aliasEquiv_refl _
    | indexable ys =>
      obtain ⟨zs, rfl, hl, hm⟩ := H
      obtain ⟨zs', rfl, hl', hm'⟩ := H'
      exact ⟨by rw [hl, hl', Nat.max_comm], fun i k => by rw [hm, hm', or_comm]⟩
    | unindexable y =>
      obtain ⟨z, rfl, hm⟩ := H
      obtain ⟨z', rfl, hm'⟩ := H'
      exact fun k => by rw [hm, hm']
  | unindexable x =>
    cases b with
    | bool d => cases d <;> simp only [AliasExact] at H H' <;> subst H H' <;> exact aliasEquiv_refl _
    | indexable ys =>
      obtain ⟨z, rfl, hm⟩ := H
      obtain ⟨z', rfl, hm'⟩ := H'
      exact fun k => by rw [hm, hm']
    | unindexable y =>
      obtain ⟨z, rfl, hm⟩ := H
      obtain ⟨z', rfl, hm'⟩ := H'
      exact fun k => by rw [hm, hm', or_comm]

theorem exact_absorb (a b r r' : AliasInfo) (H : AliasExact a b r) (H' : AliasExact r b r') : AliasEquiv r' r := by
  cases a with
  | bool c =>
    cases c
    · simp only [AliasExact] at H
      cases b with
      | bool d => cases d <;> simp only [AliasExact] at H H' <;> subst H <;> simp only [AliasExact] at H' <;> subst H' <;> exact aliasEquiv_refl _
      | _ => subst H; exact exact_idem _ _ H'
    · simp only [AliasExact] at H; subst H; cases b <;> (try (rename_i d; cases d)) <;> simp only [AliasExact] at H' <;> subst H' <;> exact aliasEquiv_refl _
  | indexable xs =>
    cases b with
    | bool d => cases d <;> simp only [AliasExact] at H <;> subst H <;> simp only [AliasExact] at H' <;> subst H' <;> exact aliasEquiv_refl _
    | indexable ys =>
      obtain ⟨zs, rfl, hl, hm⟩ := H
      obtain ⟨zs', rfl, hl', hm'⟩ := H'
      refine ⟨by rw [hl', hl]; omega, fun i k => ?_⟩
      rw [hm', hm]; constructor
      · rintro ((m | m) | m) <;> simp only [m, true_or, or_true]
      · rintro (m | m) <;> simp only [m, true_or, or_true]
    | unindexable y =>
      obtain ⟨z, rfl, hm⟩ := H
      obtain ⟨z', rfl, hm'⟩ := H'
      intro k; rw [hm', hm]; constructor
      · rintro ((m | m) | m) <;> simp only [m, true_or, or_true]
      · rintro (m | m) <;> simp only [m, true_or, or_true]
  | unindexable x =>
    cases b with
    | bool d => cases d <;> simp only [AliasExact] at H <;> subst H <;> simp only [AliasExact] at H' <;> subst H' <;> exact aliasEquiv_refl _
    | indexable ys =>
      obtain ⟨z, rfl, hm⟩ := H
      obtain ⟨z', rfl, hm'⟩ := H'
      intro k; rw [hm', hm]; constructor
      · rintro ((m | m) | m) <;> simp only [m, true_or, or_true]
      · rintro (m | m) <;> simp only [m, true_or, or_true]
    | unindexable y =>
      obtain ⟨z, rfl, hm⟩ := H
      obtain ⟨z', rfl, hm'⟩ := H'
      intro k; rw [hm', hm]; constructor
      · rintro ((m | m) | m) <;> simp only [m, true_or, or_true]
      · rintro (m | m) <;> simp only [m, true_or, or_true]

/-- What `x ⊔ₑ y` computes, field by field, as sets: the result `j` lives in heap `h'`. -/
def JoinExact (h : Heap) (x y j : EscapeInfo) (h' : Heap) : Prop :=
  j.analyzed = (x.analyzed || y.analyzed) ∧
  j.returnEscape = (x.returnEscape || y.returnEscape) ∧
  (j.thrown = .top ↔ x.thrown = .top ∨ y.thrown = .top) ∧
  (j.thrown ≠ .top → ∀ k, j.thrown.elems.mem k = true ↔
    x.thrown.elems.mem k = true ∨ y.thrown.elems.mem k = true) ∧
  AliasExact x.alias y.alias j.alias ∧
  (j.live = .top ↔ x.live = .top ∨ y.live = .top) ∧
  (j.live ≠ .top → ∀ k, (h'.get j.live).mem k = true ↔
    (h.get x.live).mem k = true ∨ (h.get y.live).mem k = true) ∧
  (∀ r, RefOk h r → RefOk h' r ∧ h'.get r = h.get r) ∧
  (RefOk h x.live → RefOk h y.live → RefOk h' j.live)

theorem jthrown_top_iff (x y : EscapeInfo) : jthrown x y = .top ↔ x.thrown = .top ∨ y.thrown = .top := by
  unfold jthrown
  cases x.thrown <;> cases y.thrown <;> simp

theorem jlive_top_iff (h : Heap) (x y : EscapeInfo) : (jlive h x y).1 = .top ↔ x.live = .top ∨ y.live = .top := by
  unfold jlive
  cases x.live <;> cases y.live <;> simp [Heap.alloc]

theorem jlive_heap (h : Heap) (x y : EscapeInfo) :
    (∀ r, RefOk h r → RefOk (jlive h x y).2 r ∧ (jlive h x y).2.get r = h.get r) ∧
    (RefOk h x.live → RefOk h y.live → RefOk (jlive h x y).2 (jlive h x y).1) := by
  unfold jlive
  split
  · exact ⟨fun r hr => ⟨hr, rfl⟩, fun _ _ => trivial⟩
  split
  · exact ⟨fun r hr => ⟨hr, rfl⟩, fun _ hy => hy⟩
  split
  · exact ⟨fun r hr => ⟨hr, rfl⟩, fun hx _ => hx⟩
  · exact ⟨fun r hr => ⟨refok_alloc _ _ r hr, get_alloc_old _ _ r hr⟩, fun _ _ => by simp [RefOk, Heap.alloc]⟩

theorem alias_exact_true (xa ya : AliasInfo) (H : xa = .bool true ∨ ya = .bool true) :
    AliasExact xa ya (.bool true) := by
  have e : mergeAliasInfo xa ya = .bool true := by
    rcases H with rfl | rfl <;> simp [mergeAliasInfo, alias_beq_bool]
  have := mergeAliasInfo_exact xa ya; rwa [e] at this

theorem alias_exact_false (ya : AliasInfo) : AliasExact (.bool false) ya ya := by
  have e : mergeAliasInfo (.bool false) ya = ya := by
    cases ya with
    | bool c => cases c <;> rfl
    | _ => simp [mergeAliasInfo, alias_beq_bool]
  have := mergeAliasInfo_exact (.bool false) ya; rwa [e] at this

theorem alias_exact_false_r (xa : AliasInfo) : AliasExact xa (.bool false) xa := by
  have e : mergeAliasInfo xa (.bool false) = xa := by
    cases xa with
    | bool c => cases c <;> rfl
    | _ => simp [mergeAliasInfo, alias_beq_bool]
  have := mergeAliasInfo_exact xa (.bool false); rwa [e] at this

theorem join_exact (h : Heap) (x y : EscapeInfo) : JoinExact h x y (join h x y).1 (join h x y).2 := by
  rcases join_cases h x y with ⟨t, e⟩ | ⟨_, bx, e⟩ | ⟨_, _, by_, e⟩ | ⟨_, _, _, e⟩ <;> rw [e]
  · have t' : isTop x = true ∨ isTop y = true := by simpa using t
    refine ⟨?_, ?_, ?_, fun c => absurd rfl c, ?_, ?_, fun c => absurd rfl c, fun r hr => ⟨hr, rfl⟩, fun _ _ => trivial⟩
    · rcases t' with c | c <;> simp [allEscape, (isTop_fields c).1]
    · rcases t' with c | c <;> simp [allEscape, (isTop_fields c).2.1]
    · rcases t' with c | c <;> simp [allEscape, (isTop_fields c).2.2.1]
    · exact alias_exact_true _ _ (by rcases t' with c | c <;> simp [(isTop_fields c).2.2.2.1])
    · rcases t' with c | c <;> simp [allEscape, (isTop_fields c).2.2.2.2]
  · obtain ⟨a, r, th, al, l⟩ := isBot_fields bx
    refine ⟨by simp [a], by simp [r], by simp [th], fun _ k => by simp [th, TSet.elems, IntSet.mem],
      by rw [al]; exact alias_exact_false _, by simp [l], fun _ k => by simp [l, Heap.get, IntSet.mem],
      fun r hr => ⟨hr, rfl⟩, fun _ hy => hy⟩
  · obtain ⟨a, r, th, al, l⟩ := isBot_fields by_
    refine ⟨by simp [a], by simp [r], by simp [th], fun _ k => by simp [th, TSet.elems, IntSet.mem],
      by rw [al]; exact alias_exact_false_r _, by simp [l], fun _ k => by simp [l, Heap.get, IntSet.mem],
      fun r hr => ⟨hr, rfl⟩, fun hx _ => hx⟩
  · obtain ⟨hh1, hh2⟩ := jlive_heap h x y
    refine ⟨rfl, rfl, jthrown_top_iff x y, fun c k => ?_, mergeAliasInfo_exact _ _, jlive_top_iff h x y,
      fun c k => ?_, hh1, hh2⟩
    · rcases jthrown_spec x y with ⟨tt, _⟩ | ti
      · exact absurd tt c
      · exact ti k
    · rcases jlive_spec h x y with ⟨lt, _⟩ | li
      · exact absurd lt c
      · exact li k

def tEq (a b : TSet) : Bool :=
  if a == .top then b == .top else if b == .top then false else IntSet.seteq a.elems b.elems
def lEq (h : Heap) (a b : LRef) : Bool :=
  if a == .top then b == .top else if b == .top then false else IntSet.seteq (h.get a) (h.get b)
def aEq : AliasInfo → AliasInfo → Bool
  | .bool a, .bool b => a == b
  | .indexable xs, .indexable ys => xs.length == ys.length && (xs.zip ys).all fun (p : AInfo × AInfo) => IntSet.seteq p.1 p.2
  | .unindexable x, .unindexable y => IntSet.seteq x y
  | _, _ => false

theorem lEq_do (h : Heap) (xl yl : LRef) :
    ((if (xl == LRef.top) = true then (if (yl != LRef.top) = true then pure false else pure true)
      else if (yl == LRef.top) = true then pure false
      else if (!(h.get xl).seteq (h.get yl)) = true then pure false else pure true : Id Bool)) = lEq h xl yl := by
  unfold lEq
  cases h1 : (xl == LRef.top) <;> cases h2 : (yl == LRef.top) <;> simp [bne, h2] <;>
    cases (h.get xl).seteq (h.get yl) <;> rfl

theorem ite_not_pf (c k : Bool) : ((if (!c) = true then pure false else k : Id Bool)) = (c && k) := by
  cases c <;> rfl

theorem alias_beq_bool'' (t : AliasInfo) (b : Bool) :
    (t == AliasInfo.bool b) = decide (t = .bool b) := by
  cases t with
  | bool c => cases b <;> cases c <;> rfl
  | _ => rfl

@[simp] theorem alias_bool_beq (a b : Bool) : (AliasInfo.bool a == AliasInfo.bool b) = (a == b) := by
  cases a <;> cases b <;> rfl

theorem eqE_eq (h : Heap) (x y : EscapeInfo) :
    eqE h x y = (x.analyzed == y.analyzed && x.returnEscape == y.returnEscape && tEq x.thrown y.thrown &&
      aEq x.alias y.alias && lEq h x.live y.live) := by
  cases x with | mk xa xr xt xal xl =>
  cases y with | mk ya yr yt yal yl =>
  simp only [eqE, Id.run, lEq_do]
  have tEq_do : ∀ k : Bool, ((if (xt == TSet.top) = true then (if (yt != TSet.top) = true then pure false else (k : Id Bool))
      else if (yt == TSet.top) = true then pure false
      else if (!xt.elems.seteq yt.elems) = true then pure false else (k : Id Bool) : Id Bool)) = (tEq xt yt && k) := by
    intro k; unfold tEq
    cases h1 : (xt == TSet.top) <;> cases h2 : (yt == TSet.top) <;> simp [bne, h2] <;>
      cases xt.elems.seteq yt.elems <;> rfl
  simp only [tEq_do]
  cases xal <;> cases yal <;> simp only [aEq, bne, ite_not_pf]
  all_goals (cases xa <;> cases ya <;> cases xr <;> cases yr <;> (try rfl))
  all_goals (try simp only [alias_beq_bool'']); all_goals (first | (simp [Bool.and_assoc]; done) | (simp <;> intros <;> rfl; done) | (rename_i b1 b2; cases b1 <;> cases b2 <;> simp))

theorem seteq_of (a b : IntSet) (H : ∀ k, a.mem k = true ↔ b.mem k = true) : IntSet.seteq a b = true := by
  simp only [IntSet.seteq, Bool.and_eq_true, intset_subset]
  exact ⟨fun k => (H k).1, fun k => (H k).2⟩

theorem ainfo_seteq_of (a b : AInfo) (H : ∀ k, k ∈ a ↔ k ∈ b) : IntSet.seteq a b = true :=
  seteq_of a b (fun k => by simp only [intset_mem]; exact H k)

theorem zip_all_seteq (xs ys : List AInfo) (hl : xs.length = ys.length)
    (H : ∀ i k, k ∈ xs.getD i [] ↔ k ∈ ys.getD i []) :
    ((xs.zip ys).all fun (p : AInfo × AInfo) => IntSet.seteq p.1 p.2) = true := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a as ih =>
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
      exact ⟨ainfo_seteq_of a b (fun k => by simpa using H 0 k),
        ih bs (by simpa using hl) (fun i k => by simpa using H (i + 1) k)⟩

theorem aEq_of (a b : AliasInfo) (H : AliasEquiv a b) : aEq a b = true := by
  cases a <;> cases b <;> simp only [AliasEquiv] at H <;> simp only [aEq]
  · subst H; simp
  · obtain ⟨hl, hm⟩ := H
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hl, zip_all_seteq _ _ hl hm⟩
  · exact ainfo_seteq_of _ _ H

/-- Sufficient condition for `x == y`: the same flags and the same sets in every field. -/
theorem eqE_of (h : Heap) (x y : EscapeInfo) (ha : x.analyzed = y.analyzed) (hr : x.returnEscape = y.returnEscape)
    (ht : x.thrown = .top ↔ y.thrown = .top)
    (ht2 : x.thrown ≠ .top → ∀ k, x.thrown.elems.mem k = true ↔ y.thrown.elems.mem k = true)
    (hal : AliasEquiv x.alias y.alias)
    (hl : x.live = .top ↔ y.live = .top)
    (hl2 : x.live ≠ .top → ∀ k, (h.get x.live).mem k = true ↔ (h.get y.live).mem k = true) :
    eqE h x y = true := by
  rw [eqE_eq]
  simp only [ha, hr, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨?_, aEq_of _ _ hal⟩, ?_⟩
  · unfold tEq
    by_cases c : x.thrown = .top
    · simp [c, ht.1 c]
    · have c' : y.thrown ≠ .top := fun e => c (ht.2 e)
      simp [c, c', seteq_of _ _ (ht2 c)]
  · unfold lEq
    by_cases c : x.live = .top
    · simp [c, hl.1 c]
    · have c' : y.live ≠ .top := fun e => c (hl.2 e)
      simp [c, c', seteq_of _ _ (hl2 c)]


/-! ## A sufficient condition for `⊑ₑ` -/

section
open JuliaLean.Compiler.ssair

/-- What the `AliasInfo` part of `⊑ₑ` accepts (sufficient form). -/
def AliasLe : AliasInfo → AliasInfo → Prop
  | .bool b, ya => b = true → ya = .bool true
  | .indexable xs, .indexable ys => xs.length ≤ ys.length ∧ ∀ i k, k ∈ xs.getD i [] → k ∈ ys.getD i []
  | .indexable xs, .unindexable y => xs ≠ [] ∧ ∀ i k, k ∈ xs.getD i [] → k ∈ y
  | .indexable _, .bool b => b = true
  | .unindexable x, .unindexable y => ∀ k, k ∈ x → k ∈ y
  | .unindexable _, .bool b => b = true
  | .unindexable _, .indexable _ => False

theorem ainfo_subset_of (a b : AInfo) (H : ∀ k, k ∈ a → k ∈ b) : IntSet.subset a b = true := by
  rw [intset_subset]; intro k; simp only [intset_mem]; exact H k

theorem zip_all_subset (xs ys : List AInfo) (hl : xs.length ≤ ys.length)
    (H : ∀ i k, k ∈ xs.getD i [] → k ∈ ys.getD i []) :
    ((xs.zip ys).all fun (p : AInfo × AInfo) => IntSet.subset p.1 p.2) = true := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a as ih =>
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
      exact ⟨ainfo_subset_of a b (fun k m => by simpa using H 0 k (by simpa using m)),
        ih bs (by simp at hl; omega) (fun i k m => by simpa using H (i + 1) k (by simpa using m))⟩

theorem aget_last (xs : List AInfo) (hne : xs ≠ []) :
    aget xs.toArray (xs.length : Int) = .ok (xs.getD (xs.length - 1) []) := by
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  unfold aget
  have hc : 1 ≤ (xs.length : Int) ∧ ((xs.length : Int) - 1).toNat < xs.toArray.size := by
    simp; omega
  split
  case isFalse hn => exact absurd hc hn
  have e : ((xs.length : Int) - 1).toNat = xs.length - 1 := by omega
  simp only [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : xs.length - 1 < xs.length)]
  simp [pure, Except.pure]

theorem sqsub_of (h : Heap) (x y : EscapeInfo) (t1 : isTop y = false) (t2 : isTop x = false)
    (t3 : isBot x = false) (t4 : isBot y = false)
    (ha : x.analyzed = true → y.analyzed = true) (hr : x.returnEscape = true → y.returnEscape = true)
    (ht : x.thrown = .top → y.thrown = .top)
    (ht2 : x.thrown ≠ .top → y.thrown ≠ .top → IntSet.subset x.thrown.elems y.thrown.elems = true)
    (hal : AliasLe x.alias y.alias)
    (hl : x.live = .top → y.live = .top)
    (hl2 : x.live ≠ .top → y.live ≠ .top → IntSet.subset (h.get x.live) (h.get y.live) = true) :
    sqsub h x y = .ok true := by
  unfold sqsub
  simp only [t1, t2, t3, t4, Bool.false_eq_true, ite_false]
  have L : (if (x.live == LRef.top) = true then (if (y.live != LRef.top) = true then pure false else pure true)
      else if (y.live != LRef.top) = true then
        (if (!(h.get x.live).subset (h.get y.live)) = true then pure false else pure true)
      else pure true : JM Bool) = pure true := by
    by_cases c : x.live = .top
    · simp [c, hl c, bne]
    · by_cases c' : y.live = .top
      · simp [c, c', bne]
      · simp [c, c', bne, hl2 c c']
  have T : ∀ K : JM Bool, (if (x.thrown == TSet.top) = true then (if (y.thrown != TSet.top) = true then pure false else K)
      else if (y.thrown != TSet.top) = true then
        (if (!x.thrown.elems.subset y.thrown.elems) = true then pure false else K)
      else K) = K := by
    intro K
    by_cases c : x.thrown = .top
    · simp [c, ht c, bne]
    · by_cases c' : y.thrown = .top
      · simp [c, c', bne]
      · simp [c, c', bne, ht2 c c']
  simp only [L, T]
  have A : (!(!x.analyzed || y.analyzed)) = false := by cases e : x.analyzed <;> simp_all
  have R : (!(!x.returnEscape || y.returnEscape)) = false := by cases e : x.returnEscape <;> simp_all
  simp only [A, R, Bool.false_eq_true, ite_false]
  generalize x.alias = xa at hal ⊢
  generalize y.alias = ya at hal ⊢
  cases xa <;> cases ya <;> simp only [AliasLe] at hal
  all_goals dsimp only
  · rename_i b c; cases b <;> cases c <;> simp_all [bne] <;> rfl
  · rename_i b l; cases b <;> simp_all [bne, alias_beq_bool] <;> rfl
  · rename_i b l; cases b <;> simp_all [bne, alias_beq_bool] <;> rfl
  · rename_i xs c; subst hal; rfl
  · rename_i xs ys
    simp only [gt_iff_lt, Nat.not_lt.mpr hal.1, ite_false, zip_all_subset xs ys hal.1 hal.2]; rfl
  · rename_i xs y
    rw [aget_last xs hal.1]
    simp only [bind, Except.bind, ainfo_subset_of _ _ (hal.2 _), Bool.not_true, Bool.false_eq_true, ite_false]; rfl
  · rename_i x c; subst hal; rfl
  · rename_i a b; simp only [ainfo_subset_of a b hal, Bool.not_true, Bool.false_eq_true, ite_false]; rfl

theorem sqsub_top_right (h : Heap) (x y : EscapeInfo) (t : isTop y = true) : sqsub h x y = .ok true := by
  unfold sqsub; simp [t]; rfl

theorem sqsub_bot_left (h : Heap) (x y : EscapeInfo) (b : isBot x = true) : sqsub h x y = .ok true := by
  have nt : isTop x = false := by
    obtain ⟨a, _⟩ := isBot_fields b; simp [isTop, a]
  unfold sqsub
  by_cases t : isTop y = true
  · simp [t]; rfl
  · simp [t, nt, b]; rfl

theorem jthrown_bot (x y : EscapeInfo) (H : jthrown x y = .bot) : x.thrown = .bot ∧ y.thrown = .bot := by
  revert H; unfold jthrown
  cases x.thrown <;> cases y.thrown <;> simp

theorem jlive_bot (h : Heap) (x y : EscapeInfo) (H : (jlive h x y).1 = .bot) : x.live = .bot ∧ y.live = .bot := by
  revert H; unfold jlive
  cases x.live <;> cases y.live <;> simp [Heap.alloc]

theorem merge_false (xa ya : AliasInfo) (H : mergeAliasInfo xa ya = .bool false) :
    xa = .bool false ∧ ya = .bool false := by
  revert H
  cases xa with
  | bool b => cases b <;> cases ya <;> (try (rename_i c; cases c)) <;> simp [mergeAliasInfo, alias_beq_bool]
  | indexable xs => cases ya <;> (try (rename_i c; cases c)) <;> simp [mergeAliasInfo, alias_beq_bool]
  | unindexable x => cases ya <;> (try (rename_i c; cases c)) <;> simp [mergeAliasInfo, alias_beq_bool]

theorem aliasLe_refl (a : AliasInfo) (hne : a ≠ .indexable []) : AliasLe a a := by
  cases a with
  | bool b => intro hb; rw [hb]
  | indexable xs => exact ⟨Nat.le_refl _, fun _ _ m => m⟩
  | unindexable x => exact fun _ m => m

theorem alias_le_left (xa ya r : AliasInfo) (H : AliasExact xa ya r) (hne : xa ≠ .indexable []) :
    AliasLe xa r := by
  cases xa with
  | bool b =>
    cases b
    · intro c; cases c
    · simp only [AliasExact] at H; intro _; exact H
  | indexable xs =>
    cases ya with
    | bool d => cases d <;> simp only [AliasExact] at H <;> subst H
                · exact aliasLe_refl _ hne
                · rfl
    | indexable ys =>
      obtain ⟨zs, rfl, hl, hm⟩ := H
      exact ⟨by rw [hl]; exact Nat.le_max_left _ _, fun i k m => (hm i k).2 (Or.inl m)⟩
    | unindexable y =>
      obtain ⟨z, rfl, hm⟩ := H
      exact ⟨fun e => hne (by rw [e]), fun i k m => (hm k).2 (Or.inr ⟨i, m⟩)⟩
  | unindexable x =>
    cases ya with
    | bool d => cases d <;> simp only [AliasExact] at H <;> subst H
                · exact aliasLe_refl _ (by simp)
                · rfl
    | indexable ys =>
      obtain ⟨z, rfl, hm⟩ := H
      exact fun k m => (hm k).2 (Or.inl m)
    | unindexable y =>
      obtain ⟨z, rfl, hm⟩ := H
      exact fun k m => (hm k).2 (Or.inl m)

theorem alias_le_right (xa ya r : AliasInfo) (H : AliasExact xa ya r) (hne : ya ≠ .indexable []) :
    AliasLe ya r := by
  cases xa with
  | bool b =>
    cases b
    · simp only [AliasExact] at H
      cases ya with
      | bool d => cases d <;> simp only [AliasExact] at H <;> subst H
                  · intro c; cases c
                  · intro _; rfl
      | _ => subst H; exact aliasLe_refl _ hne
    · simp only [AliasExact] at H; subst H
      cases ya with
      | bool d => intro _; rfl
      | _ => rfl
  | indexable xs =>
    cases ya with
    | bool d => cases d <;> simp only [AliasExact] at H <;> subst H
                · intro c; cases c
                · intro _; rfl
    | indexable ys =>
      obtain ⟨zs, rfl, hl, hm⟩ := H
      exact ⟨by rw [hl]; exact Nat.le_max_right _ _, fun i k m => (hm i k).2 (Or.inr m)⟩
    | unindexable y =>
      obtain ⟨z, rfl, hm⟩ := H
      exact fun k m => (hm k).2 (Or.inl m)
  | unindexable x =>
    cases ya with
    | bool d => cases d <;> simp only [AliasExact] at H <;> subst H
                · intro c; cases c
                · intro _; rfl
    | indexable ys =>
      obtain ⟨z, rfl, hm⟩ := H
      exact ⟨fun e => hne (by rw [e]), fun i k m => (hm k).2 (Or.inr ⟨i, m⟩)⟩
    | unindexable y =>
      obtain ⟨z, rfl, hm⟩ := H
      exact fun k m => (hm k).2 (Or.inr m)

theorem le_join (h h' : Heap) (z j : EscapeInfo) (hz : RefOk h z.live)
    (hh : ∀ r, RefOk h r → RefOk h' r ∧ h'.get r = h.get r)
    (tz : isTop z = false) (bz : isBot z = false) (bj : isBot j = false)
    (ha : z.analyzed = true → j.analyzed = true) (hr : z.returnEscape = true → j.returnEscape = true)
    (ht : z.thrown = .top → j.thrown = .top)
    (ht2 : j.thrown ≠ .top → ∀ k, z.thrown.elems.mem k = true → j.thrown.elems.mem k = true)
    (hal : AliasLe z.alias j.alias)
    (hl : z.live = .top → j.live = .top)
    (hl2 : j.live ≠ .top → ∀ k, (h.get z.live).mem k = true → (h'.get j.live).mem k = true) :
    sqsub h' z j = .ok true := by
  cases tj : isTop j
  · apply sqsub_of h' z j tj tz bz bj ha hr ht (fun _ c => ?_) hal hl (fun _ c => ?_)
    · rw [intset_subset]; exact ht2 c
    · rw [intset_subset, (hh _ hz).2]; exact hl2 c
  · exact sqsub_top_right _ _ _ tj

end

/-! ## Query values on the constructors, exact join laws, and in-place liveness pushes -/

theorem returnEscapeAt_fields (h : Heap) (p : Int) :
    (returnEscapeAt h p).1.returnEscape = true ∧ (returnEscapeAt h p).1.thrown = .bot ∧
    (returnEscapeAt h p).1.live ≠ .top ∧
    (returnEscapeAt h p).2.get (returnEscapeAt h p).1.live = [p] :=
  ⟨rfl, rfl, by simp [returnEscapeAt, Heap.alloc], get_alloc_new h [p]⟩

theorem mem_single (p k : Int) : IntSet.mem [p] k = decide (k = p) := by
  simp [IntSet.mem]

theorem hasNoEscape_split (h : Heap) (x : EscapeInfo) :
    hasNoEscape h x = (!hasReturnEscape x && !hasThrownEscape x && !hasArgEscape h x) := by
  simp [hasNoEscape, hasReturnEscape, hasThrownEscape, hasArgEscape]

theorem returnEscape_join_eq (h : Heap) (x y : EscapeInfo) :
    hasReturnEscape (join h x y).1 = (hasReturnEscape x || hasReturnEscape y) :=
  (join_exact h x y).2.1

theorem thrownEscape_join_eq (h : Heap) (x y : EscapeInfo) :
    hasThrownEscape (join h x y).1 = (hasThrownEscape x || hasThrownEscape y) := by
  obtain ⟨_, _, ht, ht2, _⟩ := join_exact h x y
  rw [Bool.eq_iff_iff, Bool.or_eq_true, hte_iff, hte_iff, hte_iff]
  by_cases c : (join h x y).1.thrown = .top
  · rw [c]
    refine ⟨fun _ => ?_, fun _ => ⟨-1, elems_top_mem⟩⟩
    rcases ht.1 c with e | e
    · exact Or.inl ⟨-1, by rw [e]; exact elems_top_mem⟩
    · exact Or.inr ⟨-1, by rw [e]; exact elems_top_mem⟩
  · constructor
    · rintro ⟨a, m⟩
      rcases (ht2 c a).1 m with m | m
      · exact Or.inl ⟨a, m⟩
      · exact Or.inr ⟨a, m⟩
    · rintro (⟨a, m⟩ | ⟨a, m⟩)
      · exact ⟨a, (ht2 c a).2 (Or.inl m)⟩
      · exact ⟨a, (ht2 c a).2 (Or.inr m)⟩

theorem thrownEscapeAt_join_eq (h : Heap) (x y : EscapeInfo) (pc : Int) :
    hasThrownEscapeAt (join h x y).1 pc = (hasThrownEscapeAt x pc || hasThrownEscapeAt y pc) := by
  obtain ⟨_, _, ht, ht2, _⟩ := join_exact h x y
  rw [Bool.eq_iff_iff, Bool.or_eq_true, hteAt_iff, hteAt_iff, hteAt_iff]
  by_cases c : (join h x y).1.thrown = .top
  · rw [c]
    refine ⟨fun _ => ?_, fun _ => Or.inl elems_top_mem⟩
    rcases ht.1 c with e | e
    · exact Or.inl (Or.inl (by rw [e]; exact elems_top_mem))
    · exact Or.inr (Or.inl (by rw [e]; exact elems_top_mem))
  · rw [ht2 c, ht2 c]
    cases x.thrown.elems.mem (-1) <;> cases y.thrown.elems.mem (-1) <;> cases x.thrown.elems.mem pc <;>
      cases y.thrown.elems.mem pc <;> simp

theorem argEscape_join_eq (h : Heap) (x y : EscapeInfo) :
    hasArgEscape (join h x y).2 (join h x y).1 = (hasArgEscape h x || hasArgEscape h y) := by
  obtain ⟨_, _, _, _, _, hl, hl2, _⟩ := join_exact h x y
  rw [Bool.eq_iff_iff, Bool.or_eq_true]
  unfold hasArgEscape
  by_cases c : (join h x y).1.live = .top
  · rw [c]
    refine ⟨fun _ => ?_, fun _ => get_top_mem0 _⟩
    rcases hl.1 c with e | e
    · exact Or.inl (by rw [e]; exact get_top_mem0 _)
    · exact Or.inr (by rw [e]; exact get_top_mem0 _)
  · exact hl2 c 0

theorem noEscape_join_eq (h : Heap) (x y : EscapeInfo) :
    hasNoEscape (join h x y).2 (join h x y).1 = (hasNoEscape h x && hasNoEscape h y) := by
  rw [hasNoEscape_split, hasNoEscape_split, hasNoEscape_split, returnEscape_join_eq, thrownEscape_join_eq,
    argEscape_join_eq]
  cases hasReturnEscape x <;> cases hasReturnEscape y <;> cases hasThrownEscape x <;>
    cases hasThrownEscape y <;> cases hasArgEscape h x <;> cases hasArgEscape h y <;> rfl

theorem get_push_mem (h : Heap) (n : Nat) (hn : n < h.sets.size) (p k : Int) :
    ((h.push (.ref n) p).get (.ref n)).mem k = true ↔ k = p ∨ (h.get (.ref n)).mem k = true := by
  simp only [Heap.push, Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  simp [hn, Array.getElem?_eq_getElem hn, IntSet.insert, IntSet.mem, IntSet.norm, List.mem_eraseDups,
    List.mem_mergeSort]

theorem argEscape_push (h : Heap) (x : EscapeInfo) (n : Nat) (hl : x.live = .ref n) (hn : n < h.sets.size)
    (p : Int) : hasArgEscape (h.push x.live p) x = (hasArgEscape h x || decide (p = 0)) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true]
  unfold hasArgEscape
  rw [hl, get_push_mem h n hn]
  simp only [decide_eq_true_eq]
  constructor <;> rintro (e | e)
  · exact Or.inr e.symm
  · exact Or.inl e
  · exact Or.inr e
  · exact Or.inl e.symm

theorem returnEscapeAt_push (h : Heap) (x : EscapeInfo) (n : Nat) (hl : x.live = .ref n)
    (hn : n < h.sets.size) (p : Int) : hasReturnEscapeAt (h.push x.live p) x p = hasReturnEscape x := by
  unfold hasReturnEscapeAt hasReturnEscape
  rw [hl]
  have : ((h.push (.ref n) p).get (.ref n)).mem p = true := (get_push_mem h n hn p p).2 (Or.inl rfl)
  simp [this]

theorem hasNoEscape_values (h : Heap) (p : Int) :
    hasNoEscape h noEscape = true ∧ hasNoEscape h notAnalyzed = true ∧ hasNoEscape h argEscape = false ∧
    hasNoEscape (returnEscapeAt h p).2 (returnEscapeAt h p).1 = false ∧
    hasNoEscape h allReturnEscape = false ∧ hasNoEscape h (thrownEscapeAt p) = false ∧
    hasNoEscape h allEscape = false := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, rfl⟩
  · simp [hasNoEscape, (returnEscapeAt_fields h p).1]
  · simp [hasNoEscape, thrownEscapeAt, TSet.elems]

theorem hasArgEscape_values (h : Heap) (p : Int) :
    hasArgEscape h noEscape = false ∧ hasArgEscape h notAnalyzed = false ∧ hasArgEscape h argEscape = true ∧
    hasArgEscape (returnEscapeAt h p).2 (returnEscapeAt h p).1 = decide (p = 0) ∧
    hasArgEscape h allReturnEscape = true ∧ hasArgEscape h (thrownEscapeAt p) = false ∧
    hasArgEscape h allEscape = true := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  rw [hasArgEscape, (returnEscapeAt_fields h p).2.2.2, mem_single]
  simp [eq_comm]

theorem hasReturnEscape_values (h : Heap) (p : Int) :
    hasReturnEscape noEscape = false ∧ hasReturnEscape notAnalyzed = false ∧ hasReturnEscape argEscape = false ∧
    hasReturnEscape (returnEscapeAt h p).1 = true ∧ hasReturnEscape allReturnEscape = true ∧
    hasReturnEscape (thrownEscapeAt p) = false ∧ hasReturnEscape allEscape = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hasReturnEscapeAt_values (h : Heap) (p pc : Int) :
    hasReturnEscapeAt h noEscape pc = false ∧ hasReturnEscapeAt h notAnalyzed pc = false ∧
    hasReturnEscapeAt h argEscape pc = false ∧
    hasReturnEscapeAt (returnEscapeAt h p).2 (returnEscapeAt h p).1 pc = (decide (p = -1) || decide (p = pc)) ∧
    hasReturnEscapeAt h allReturnEscape pc = true ∧ hasReturnEscapeAt h (thrownEscapeAt p) pc = false ∧
    hasReturnEscapeAt h allEscape pc = true := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_⟩
  · rw [hasReturnEscapeAt, (returnEscapeAt_fields h p).2.2.2, mem_single, mem_single,
      (returnEscapeAt_fields h p).1]
    simp [eq_comm]
  · simp [hasReturnEscapeAt, allReturnEscape, get_top_memm1]
  · simp [hasReturnEscapeAt, allEscape, get_top_memm1]

theorem hasThrownEscape_values (h : Heap) (p : Int) :
    hasThrownEscape noEscape = false ∧ hasThrownEscape notAnalyzed = false ∧ hasThrownEscape argEscape = false ∧
    hasThrownEscape (returnEscapeAt h p).1 = false ∧ hasThrownEscape allReturnEscape = false ∧
    hasThrownEscape (thrownEscapeAt p) = true ∧ hasThrownEscape allEscape = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hasThrownEscapeAt_values (h : Heap) (p pc : Int) :
    hasThrownEscapeAt noEscape pc = false ∧ hasThrownEscapeAt notAnalyzed pc = false ∧
    hasThrownEscapeAt argEscape pc = false ∧ hasThrownEscapeAt (returnEscapeAt h p).1 pc = false ∧
    hasThrownEscapeAt allReturnEscape pc = false ∧
    hasThrownEscapeAt (thrownEscapeAt p) pc = (decide (p = -1) || decide (p = pc)) ∧
    hasThrownEscapeAt allEscape pc = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [hasThrownEscapeAt, thrownEscapeAt, TSet.elems, mem_single, eq_comm]
  · simp [hasThrownEscapeAt, allEscape, elems_top_mem]

theorem hasReturnEscapeAt_imp (h : Heap) (x : EscapeInfo) (pc : Int) :
    hasReturnEscapeAt h x pc = true → hasReturnEscape x = true := by
  simp only [hasReturnEscapeAt, hasReturnEscape, Bool.and_eq_true]; exact fun H => H.1

theorem hasThrownEscapeAt_imp (x : EscapeInfo) (pc : Int) :
    hasThrownEscapeAt x pc = true → hasThrownEscape x = true := by
  rw [hteAt_iff, hte_iff]; rintro (m | m) <;> exact ⟨_, m⟩

/-! ## The `ignore_*` constructors, `from_interprocedural` and `⊏ₑ`, exactly -/

theorem ignoreArgescape_exact (h : Heap) (x : EscapeInfo) :
    (ignoreArgescape h x).1.analyzed = x.analyzed ∧ (ignoreArgescape h x).1.returnEscape = x.returnEscape ∧
    (ignoreArgescape h x).1.thrown = x.thrown ∧ (ignoreArgescape h x).1.alias = x.alias ∧
    (∀ k, ((ignoreArgescape h x).2.get (ignoreArgescape h x).1.live).mem k = true ↔
      (h.get x.live).mem k = true ∧ k ≠ 0) ∧
    (∀ r, RefOk h r → RefOk (ignoreArgescape h x).2 r ∧ (ignoreArgescape h x).2.get r = h.get r) ∧
    ¬ RefOk h (ignoreArgescape h x).1.live := by
  refine ⟨rfl, rfl, rfl, rfl, fun k => ?_, fun r hr => ⟨refok_alloc _ _ r hr, get_alloc_old _ _ r hr⟩, ?_⟩
  · simp [ignoreArgescape, get_alloc_new, erase_mem]
  · simp [ignoreArgescape, Heap.alloc, RefOk]

theorem ignoreAliasinfo_exact (x : EscapeInfo) :
    (∀ a, mergeAliasInfo (ignoreAliasinfo x).alias a = a ∧ mergeAliasInfo a (ignoreAliasinfo x).alias = a) ∧
    (ignoreAliasinfo x).analyzed = x.analyzed ∧ (ignoreAliasinfo x).returnEscape = x.returnEscape ∧
    (ignoreAliasinfo x).thrown = x.thrown ∧ (ignoreAliasinfo x).live = x.live := by
  refine ⟨fun a => ⟨?_, ?_⟩, rfl, rfl, rfl, rfl⟩
  · cases a with
    | bool c => cases c <;> rfl
    | _ => simp [ignoreAliasinfo, mergeAliasInfo, alias_beq_bool]
  · cases a with
    | bool c => cases c <;> rfl
    | _ => simp [ignoreAliasinfo, mergeAliasInfo, alias_beq_bool]

theorem ignoreLiveness_exact (x : EscapeInfo) :
    (∀ (h : Heap) k, (h.get (ignoreLiveness x).live).mem k = false) ∧
    (ignoreLiveness x).analyzed = x.analyzed ∧ (ignoreLiveness x).returnEscape = x.returnEscape ∧
    (ignoreLiveness x).thrown = x.thrown ∧ (ignoreLiveness x).alias = x.alias :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem fromInterprocedural_exact (h : Heap) (x : EscapeInfo) (pc : Int) (t : isTop x = false) :
    (fromInterprocedural h (argEscapeInfo x) pc).1.analyzed = true ∧
    (∀ k, (fromInterprocedural h (argEscapeInfo x) pc).1.thrown.elems.mem k = true ↔
      hasThrownEscape x = true ∧ k = pc) ∧
    (∀ r, RefOk h r → RefOk (fromInterprocedural h (argEscapeInfo x) pc).2 r ∧
      (fromInterprocedural h (argEscapeInfo x) pc).2.get r = h.get r) ∧
    ¬ RefOk h (fromInterprocedural h (argEscapeInfo x) pc).1.live := by
  obtain ⟨ha, _, ht, _⟩ := argEscapeInfo_bits x
  have na : aHasAllEscape (argEscapeInfo x) = false := by rw [ha, t]
  simp only [fromInterprocedural, na, Bool.false_eq_true, ite_false]
  refine ⟨by first | rfl | trivial, fun k => ?_, fun r hr => ⟨refok_alloc _ _ r hr, get_alloc_old _ _ r hr⟩, ?_⟩
  · rw [ht, t]
    cases e : hasThrownEscape x <;> simp [TSet.elems, IntSet.mem]
  · simp [Heap.alloc, RefOk]

theorem sqsubStrict_iff (h : Heap) (x y : EscapeInfo) :
    (sqsubStrict h x y = .ok true ↔ sqsub h x y = .ok true ∧ sqsub h y x = .ok false) ∧
    (sqsubStrict h x y = .ok false ↔
      sqsub h x y = .ok false ∨ (sqsub h x y = .ok true ∧ sqsub h y x = .ok true)) := by
  unfold sqsubStrict
  cases e : sqsub h x y with
  | error _ => simp [bind, Except.bind]
  | ok b =>
    cases b
    · simp [pure, Except.pure, bind, Except.bind]
    · cases e2 : sqsub h y x with
      | error _ => simp [bind, Except.bind]
      | ok c => cases c <;> simp [pure, Except.pure, bind, Except.bind]

theorem seteq_iff (a b : IntSet) : IntSet.seteq a b = true ↔ ∀ k, a.mem k = true ↔ b.mem k = true := by
  simp only [IntSet.seteq, Bool.and_eq_true, intset_subset]
  constructor
  · rintro ⟨H1, H2⟩ k; exact ⟨H1 k, H2 k⟩
  · intro H; exact ⟨fun k => (H k).1, fun k => (H k).2⟩

theorem zip_all_seteq_imp (xs ys : List AInfo) (hl : xs.length = ys.length)
    (H : ((xs.zip ys).all fun (p : AInfo × AInfo) => IntSet.seteq p.1 p.2) = true) :
    ∀ i k, k ∈ xs.getD i [] ↔ k ∈ ys.getD i [] := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => intro i k; simp
    | cons _ _ => simp at hl
  | cons a as ih =>
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at H
      intro i k
      cases i with
      | zero =>
        have := (seteq_iff a b).1 H.1 k
        simp only [intset_mem] at this; simpa using this
      | succ i => simpa using ih bs (by simpa using hl) H.2 i k

theorem aliasEquiv_of_aEq (a b : AliasInfo) (H : aEq a b = true) : AliasEquiv a b := by
  cases a <;> cases b <;> simp only [aEq, Bool.false_eq_true] at H <;> simp only [AliasEquiv]
  · simpa using H
  · simp only [Bool.and_eq_true, beq_iff_eq] at H
    exact ⟨H.1, zip_all_seteq_imp _ _ H.1 H.2⟩
  · intro k; have := (seteq_iff _ _).1 H k; simp only [intset_mem] at this; exact this

/-- `x == y` holds exactly when the two have the same flags and hold the same sets in every
field, with the `TOP` constants compared by identity. -/
theorem eqE_iff (h : Heap) (x y : EscapeInfo) :
    eqE h x y = true ↔
      (x.analyzed = y.analyzed ∧ x.returnEscape = y.returnEscape ∧
       (x.thrown = .top ↔ y.thrown = .top) ∧
       (x.thrown ≠ .top → ∀ k, x.thrown.elems.mem k = true ↔ y.thrown.elems.mem k = true) ∧
       AliasEquiv x.alias y.alias ∧
       (x.live = .top ↔ y.live = .top) ∧
       (x.live ≠ .top → ∀ k, (h.get x.live).mem k = true ↔ (h.get y.live).mem k = true)) := by
  constructor
  · intro H
    rw [eqE_eq] at H
    simp only [Bool.and_eq_true, beq_iff_eq] at H
    obtain ⟨⟨⟨⟨ha, hr⟩, ht⟩, hal⟩, hl⟩ := H
    refine ⟨ha, hr, ?_, ?_, aliasEquiv_of_aEq _ _ hal, ?_, ?_⟩
    · unfold tEq at ht
      by_cases c : x.thrown = .top
      · simp [c] at ht; simp [c, ht]
      · by_cases c' : y.thrown = .top
        · simp [c, c'] at ht
        · simp [c, c']
    · intro c
      have c' : y.thrown ≠ .top := by intro e; unfold tEq at ht; simp [c, e] at ht
      unfold tEq at ht; simp [c, c'] at ht
      exact (seteq_iff _ _).1 ht
    · unfold lEq at hl
      by_cases c : x.live = .top
      · simp [c] at hl; simp [c, hl]
      · by_cases c' : y.live = .top
        · simp [c, c'] at hl
        · simp [c, c']
    · intro c
      have c' : y.live ≠ .top := by intro e; unfold lEq at hl; simp [c, e] at hl
      unfold lEq at hl; simp [c, c'] at hl
      exact (seteq_iff _ _).1 hl
  · rintro ⟨ha, hr, ht, ht2, hal, hl, hl2⟩
    exact eqE_of h x y ha hr ht ht2 hal hl hl2

/-! ## Refutations -/

def infoA (a : AliasInfo) : EscapeInfo := { noEscape with alias := a }

def SqsubTransitive : Prop :=
  ∀ (h : Heap) (x y z : EscapeInfo), sqsub h x y = .ok true → sqsub h y z = .ok true →
    sqsub h x z = .ok true

theorem sqsubTransitive_refuted : ¬ SqsubTransitive := by
  intro H
  have := H {} (infoA (.indexable [[5]])) (infoA (.indexable [[5], []])) (infoA (.unindexable []))
    (by rfl) (by rfl)
  have e : sqsub {} (infoA (.indexable [[5]])) (infoA (.unindexable [])) = .ok false := by rfl
  rw [e] at this; cases this

def SqsubJoinAgree : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo), sqsub h x y = .ok true →
    eqE (join h x y).2 (join h x y).1 y = true

theorem sqsubJoinAgree_refuted : ¬ SqsubJoinAgree := by
  intro H
  have := H {} (infoA (.indexable [[5], []])) (infoA (.unindexable [])) (by rfl)
  revert this; decide

def JoinUpperBound : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo),
    sqsub (join h x y).2 x (join h x y).1 = .ok true ∧ sqsub (join h x y).2 y (join h x y).1 = .ok true

theorem joinUpperBound_refuted : ¬ JoinUpperBound := by
  intro H
  have := (H {} (infoA (.indexable [])) (infoA (.unindexable []))).1
  have e : sqsub (join {} (infoA (.indexable [])) (infoA (.unindexable []))).2 (infoA (.indexable []))
      (join {} (infoA (.indexable [])) (infoA (.unindexable []))).1 = .error "julia:BoundsError" := by rfl
  rw [e] at this; cases this

def SqsubRespectsEq : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo), eqE h x y = true → sqsub h x y = .ok true

theorem sqsubRespectsEq_refuted : ¬ SqsubRespectsEq := by
  intro H
  have := H (ignoreArgescape {} notAnalyzed).2 (ignoreArgescape {} notAnalyzed).1 notAnalyzed (by rfl)
  have e : sqsub (ignoreArgescape {} notAnalyzed).2 (ignoreArgescape {} notAnalyzed).1 notAnalyzed
      = .ok false := by rfl
  rw [e] at this; cases this


/-! ## Registry statements -/

/-- `has_no_escape` is antitone along `⊑ₑ`; on a join it is exactly "neither argument escapes";
it is "not returned, not thrown and not an argument"; and it has the value the `EscapeInfo`
docstring (lines 45-82) gives on every constructor. -/
def HasNoEscapeMonotone : Prop :=
  (∀ (h : Heap) (x y : EscapeInfo), sqsub h x y = .ok true →
      hasNoEscape h y = true → hasNoEscape h x = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo), hasNoEscape (join h x y).2 (join h x y).1 = true →
      hasNoEscape h x = true ∧ hasNoEscape h y = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo),
      hasNoEscape (join h x y).2 (join h x y).1 = (hasNoEscape h x && hasNoEscape h y)) ∧
  (∀ (h : Heap) (x : EscapeInfo),
      hasNoEscape h x = (!hasReturnEscape x && !hasThrownEscape x && !hasArgEscape h x)) ∧
  (∀ (h : Heap) (p : Int),
    hasNoEscape h noEscape = true ∧ hasNoEscape h notAnalyzed = true ∧ hasNoEscape h argEscape = false ∧
    hasNoEscape (returnEscapeAt h p).2 (returnEscapeAt h p).1 = false ∧
    hasNoEscape h allReturnEscape = false ∧ hasNoEscape h (thrownEscapeAt p) = false ∧
    hasNoEscape h allEscape = false)

theorem hasNoEscapeMonotone_proven : HasNoEscapeMonotone :=
  ⟨noEscape_sqsub, noEscape_join, noEscape_join_eq, hasNoEscape_split, hasNoEscape_values⟩

/-- `has_arg_escape` is monotone along `⊑ₑ`, exact on joins, turned on by pushing `0` into a
shared `Liveness` set and unchanged by pushing any other pc, and has the docstring's value
(`0 ∈ Liveness` marks a call argument) on every constructor. -/
def HasArgEscapeMonotone : Prop :=
  (∀ (h : Heap) (x y : EscapeInfo), sqsub h x y = .ok true →
      hasArgEscape h x = true → hasArgEscape h y = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo), hasArgEscape h x = true ∨ hasArgEscape h y = true →
      hasArgEscape (join h x y).2 (join h x y).1 = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo),
      hasArgEscape (join h x y).2 (join h x y).1 = (hasArgEscape h x || hasArgEscape h y)) ∧
  (∀ (h : Heap) (x : EscapeInfo) (n : Nat) (p : Int), x.live = .ref n → n < h.sets.size →
      hasArgEscape (h.push x.live p) x = (hasArgEscape h x || decide (p = 0))) ∧
  (∀ (h : Heap) (p : Int),
    hasArgEscape h noEscape = false ∧ hasArgEscape h notAnalyzed = false ∧ hasArgEscape h argEscape = true ∧
    hasArgEscape (returnEscapeAt h p).2 (returnEscapeAt h p).1 = decide (p = 0) ∧
    hasArgEscape h allReturnEscape = true ∧ hasArgEscape h (thrownEscapeAt p) = false ∧
    hasArgEscape h allEscape = true)

theorem hasArgEscapeMonotone_proven : HasArgEscapeMonotone :=
  ⟨argEscape_sqsub, argEscape_join, argEscape_join_eq,
    fun h x n p hl hn => argEscape_push h x n hl hn p, hasArgEscape_values⟩

/-- `has_return_escape` is monotone along `⊑ₑ`, exact on joins, and true exactly on the
constructors that return the value. -/
def HasReturnEscapeMonotone : Prop :=
  (∀ (h : Heap) (x y : EscapeInfo), sqsub h x y = .ok true →
      hasReturnEscape x = true → hasReturnEscape y = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo), hasReturnEscape x = true ∨ hasReturnEscape y = true →
      hasReturnEscape (join h x y).1 = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo),
      hasReturnEscape (join h x y).1 = (hasReturnEscape x || hasReturnEscape y)) ∧
  (∀ (h : Heap) (p : Int),
    hasReturnEscape noEscape = false ∧ hasReturnEscape notAnalyzed = false ∧ hasReturnEscape argEscape = false ∧
    hasReturnEscape (returnEscapeAt h p).1 = true ∧ hasReturnEscape allReturnEscape = true ∧
    hasReturnEscape (thrownEscapeAt p) = false ∧ hasReturnEscape allEscape = true)

theorem hasReturnEscapeMonotone_proven : HasReturnEscapeMonotone :=
  ⟨returnEscape_sqsub, returnEscape_join, returnEscape_join_eq, hasReturnEscape_values⟩

/-- `has_return_escape(x, pc)` is monotone along `⊑ₑ` and `⊔ₑ`, implies `has_return_escape(x)`,
holds for a returned `x` once `pc` is pushed into its shared `Liveness`, and on the
constructors is true exactly where the docstring says (`pc ∈ Liveness` or `-1 ∈ Liveness`). -/
def HasReturnEscapeAtMonotone : Prop :=
  (∀ (h : Heap) (x y : EscapeInfo) (pc : Int), sqsub h x y = .ok true →
      hasReturnEscapeAt h x pc = true → hasReturnEscapeAt h y pc = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo) (pc : Int),
      hasReturnEscapeAt h x pc = true ∨ hasReturnEscapeAt h y pc = true →
      hasReturnEscapeAt (join h x y).2 (join h x y).1 pc = true) ∧
  (∀ (h : Heap) (x : EscapeInfo) (pc : Int), hasReturnEscapeAt h x pc = true → hasReturnEscape x = true) ∧
  (∀ (h : Heap) (x : EscapeInfo) (n : Nat) (p : Int), x.live = .ref n → n < h.sets.size →
      hasReturnEscapeAt (h.push x.live p) x p = hasReturnEscape x) ∧
  (∀ (h : Heap) (p pc : Int),
    hasReturnEscapeAt h noEscape pc = false ∧ hasReturnEscapeAt h notAnalyzed pc = false ∧
    hasReturnEscapeAt h argEscape pc = false ∧
    hasReturnEscapeAt (returnEscapeAt h p).2 (returnEscapeAt h p).1 pc = (decide (p = -1) || decide (p = pc)) ∧
    hasReturnEscapeAt h allReturnEscape pc = true ∧ hasReturnEscapeAt h (thrownEscapeAt p) pc = false ∧
    hasReturnEscapeAt h allEscape pc = true)

theorem hasReturnEscapeAtMonotone_proven : HasReturnEscapeAtMonotone :=
  ⟨returnEscapeAt_sqsub, returnEscapeAt_join, hasReturnEscapeAt_imp,
    fun h x n p hl hn => returnEscapeAt_push h x n hl hn p, hasReturnEscapeAt_values⟩

/-- `has_thrown_escape` is monotone along `⊑ₑ`, exact on joins, and true exactly on the
constructors that may throw the value. -/
def HasThrownEscapeMonotone : Prop :=
  (∀ (h : Heap) (x y : EscapeInfo), sqsub h x y = .ok true →
      hasThrownEscape x = true → hasThrownEscape y = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo), hasThrownEscape x = true ∨ hasThrownEscape y = true →
      hasThrownEscape (join h x y).1 = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo),
      hasThrownEscape (join h x y).1 = (hasThrownEscape x || hasThrownEscape y)) ∧
  (∀ (h : Heap) (p : Int),
    hasThrownEscape noEscape = false ∧ hasThrownEscape notAnalyzed = false ∧ hasThrownEscape argEscape = false ∧
    hasThrownEscape (returnEscapeAt h p).1 = false ∧ hasThrownEscape allReturnEscape = false ∧
    hasThrownEscape (thrownEscapeAt p) = true ∧ hasThrownEscape allEscape = true)

theorem hasThrownEscapeMonotone_proven : HasThrownEscapeMonotone :=
  ⟨thrownEscape_sqsub, thrownEscape_join, thrownEscape_join_eq, hasThrownEscape_values⟩

/-- `has_thrown_escape(x, pc)` is monotone along `⊑ₑ`, exact on joins, implies
`has_thrown_escape(x)`, and on the constructors is true exactly where the docstring says
(`pc ∈ ThrownEscape` or `-1 ∈ ThrownEscape`). -/
def HasThrownEscapeAtMonotone : Prop :=
  (∀ (h : Heap) (x y : EscapeInfo) (pc : Int), sqsub h x y = .ok true →
      hasThrownEscapeAt x pc = true → hasThrownEscapeAt y pc = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo) (pc : Int),
      hasThrownEscapeAt x pc = true ∨ hasThrownEscapeAt y pc = true →
      hasThrownEscapeAt (join h x y).1 pc = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo) (pc : Int),
      hasThrownEscapeAt (join h x y).1 pc = (hasThrownEscapeAt x pc || hasThrownEscapeAt y pc)) ∧
  (∀ (x : EscapeInfo) (pc : Int), hasThrownEscapeAt x pc = true → hasThrownEscape x = true) ∧
  (∀ (h : Heap) (p pc : Int),
    hasThrownEscapeAt noEscape pc = false ∧ hasThrownEscapeAt notAnalyzed pc = false ∧
    hasThrownEscapeAt argEscape pc = false ∧ hasThrownEscapeAt (returnEscapeAt h p).1 pc = false ∧
    hasThrownEscapeAt allReturnEscape pc = false ∧
    hasThrownEscapeAt (thrownEscapeAt p) pc = (decide (p = -1) || decide (p = pc)) ∧
    hasThrownEscapeAt allEscape pc = true)

theorem hasThrownEscapeAtMonotone_proven : HasThrownEscapeAtMonotone :=
  ⟨thrownEscapeAt_sqsub, thrownEscapeAt_join, thrownEscapeAt_join_eq, hasThrownEscapeAt_imp,
    hasThrownEscapeAt_values⟩

/-- `has_all_escape(x)` holds exactly for `x === ⊤`, and it is monotone along `⊑ₑ` and `⊔ₑ`. -/
def HasAllEscapeMonotone : Prop :=
  (∀ (h : Heap) (x : EscapeInfo), hasAllEscape h x = .ok true ↔ isTop x = true) ∧
  (∀ (h : Heap) (x y : EscapeInfo), sqsub h x y = .ok true →
      hasAllEscape h x = .ok true → hasAllEscape h y = .ok true) ∧
  (∀ (h : Heap) (x y : EscapeInfo), hasAllEscape h x = .ok true ∨ hasAllEscape h y = .ok true →
      hasAllEscape (join h x y).2 (join h x y).1 = .ok true)

theorem hasAllEscapeMonotone_proven : HasAllEscapeMonotone :=
  ⟨hasAllEscape_iff, allEscape_sqsub, allEscape_join⟩

/-- `ignore_argescape` removes exactly the argument escape: what the `:effect_free` refinement
reads (`has_no_escape(ignore_argescape(x))`) is "not returned and not thrown". -/
def IgnoreArgescapeSpec : Prop :=
  ∀ (h : Heap) (x : EscapeInfo),
    hasArgEscape (ignoreArgescape h x).2 (ignoreArgescape h x).1 = false ∧
    hasNoEscape (ignoreArgescape h x).2 (ignoreArgescape h x).1 =
      (!x.returnEscape && x.thrown.elems.isEmpty) ∧
    hasReturnEscape (ignoreArgescape h x).1 = hasReturnEscape x ∧
    hasThrownEscape (ignoreArgescape h x).1 = hasThrownEscape x ∧
    (∀ pc, pc ≠ 0 → hasReturnEscapeAt (ignoreArgescape h x).2 (ignoreArgescape h x).1 pc =
      hasReturnEscapeAt h x pc) ∧
    (∀ pc, hasThrownEscapeAt (ignoreArgescape h x).1 pc = hasThrownEscapeAt x pc) ∧
    (ignoreArgescape h x).1.analyzed = x.analyzed ∧ (ignoreArgescape h x).1.returnEscape = x.returnEscape ∧
    (ignoreArgescape h x).1.thrown = x.thrown ∧ (ignoreArgescape h x).1.alias = x.alias ∧
    (∀ k, ((ignoreArgescape h x).2.get (ignoreArgescape h x).1.live).mem k = true ↔
      (h.get x.live).mem k = true ∧ k ≠ 0) ∧
    (∀ r, RefOk h r → RefOk (ignoreArgescape h x).2 r ∧ (ignoreArgescape h x).2.get r = h.get r) ∧
    ¬ RefOk h (ignoreArgescape h x).1.live

theorem ignoreArgescapeSpec_proven : IgnoreArgescapeSpec := fun h x =>
  ⟨(ignoreArgescape_spec h x).1, (ignoreArgescape_spec h x).2.1, (ignoreArgescape_spec h x).2.2.1,
    (ignoreArgescape_spec h x).2.2.2.1, (ignoreArgescape_spec h x).2.2.2.2.1,
    (ignoreArgescape_spec h x).2.2.2.2.2, ignoreArgescape_exact h x⟩

def IgnoreThrownescapesSpec : Prop :=
  ∀ (h : Heap) (x : EscapeInfo),
    hasThrownEscape (ignoreThrownescapes x) = false ∧
    (∀ pc, hasThrownEscapeAt (ignoreThrownescapes x) pc = false) ∧
    hasNoEscape h (ignoreThrownescapes x) = (!x.returnEscape && !(h.get x.live).mem 0) ∧
    hasReturnEscape (ignoreThrownescapes x) = hasReturnEscape x ∧
    hasArgEscape h (ignoreThrownescapes x) = hasArgEscape h x ∧
    (∀ pc, hasReturnEscapeAt h (ignoreThrownescapes x) pc = hasReturnEscapeAt h x pc)

theorem ignoreThrownescapesSpec_proven : IgnoreThrownescapesSpec := ignoreThrownescapes_spec

def IgnoreLivenessSpec : Prop :=
  ∀ (h : Heap) (x : EscapeInfo),
    hasArgEscape h (ignoreLiveness x) = false ∧
    (∀ pc, hasReturnEscapeAt h (ignoreLiveness x) pc = false) ∧
    hasNoEscape h (ignoreLiveness x) = (!x.returnEscape && x.thrown.elems.isEmpty) ∧
    hasReturnEscape (ignoreLiveness x) = hasReturnEscape x ∧
    hasThrownEscape (ignoreLiveness x) = hasThrownEscape x ∧
    (∀ pc, hasThrownEscapeAt (ignoreLiveness x) pc = hasThrownEscapeAt x pc) ∧
    (∀ (h' : Heap) k, (h'.get (ignoreLiveness x).live).mem k = false) ∧
    (ignoreLiveness x).analyzed = x.analyzed ∧ (ignoreLiveness x).returnEscape = x.returnEscape ∧
    (ignoreLiveness x).thrown = x.thrown ∧ (ignoreLiveness x).alias = x.alias

theorem ignoreLivenessSpec_proven : IgnoreLivenessSpec := fun h x =>
  ⟨(ignoreLiveness_spec h x).1, (ignoreLiveness_spec h x).2.1, (ignoreLiveness_spec h x).2.2.1,
    (ignoreLiveness_spec h x).2.2.2.1, (ignoreLiveness_spec h x).2.2.2.2.1,
    (ignoreLiveness_spec h x).2.2.2.2.2, ignoreLiveness_exact x⟩

def IgnoreAliasinfoSpec : Prop :=
  ∀ (h : Heap) (x : EscapeInfo),
    hasAllEscape h (ignoreAliasinfo x) = .ok false ∧
    hasNoEscape h (ignoreAliasinfo x) = hasNoEscape h x ∧
    hasArgEscape h (ignoreAliasinfo x) = hasArgEscape h x ∧
    hasReturnEscape (ignoreAliasinfo x) = hasReturnEscape x ∧
    (∀ pc, hasReturnEscapeAt h (ignoreAliasinfo x) pc = hasReturnEscapeAt h x pc) ∧
    hasThrownEscape (ignoreAliasinfo x) = hasThrownEscape x ∧
    (∀ pc, hasThrownEscapeAt (ignoreAliasinfo x) pc = hasThrownEscapeAt x pc) ∧
    (∀ a, mergeAliasInfo (ignoreAliasinfo x).alias a = a ∧ mergeAliasInfo a (ignoreAliasinfo x).alias = a) ∧
    (ignoreAliasinfo x).analyzed = x.analyzed ∧ (ignoreAliasinfo x).returnEscape = x.returnEscape ∧
    (ignoreAliasinfo x).thrown = x.thrown ∧ (ignoreAliasinfo x).live = x.live

theorem ignoreAliasinfoSpec_proven : IgnoreAliasinfoSpec := fun h x =>
  ⟨(ignoreAliasinfo_spec h x).1, (ignoreAliasinfo_spec h x).2.1, (ignoreAliasinfo_spec h x).2.2.1,
    (ignoreAliasinfo_spec h x).2.2.2.1, (ignoreAliasinfo_spec h x).2.2.2.2.1,
    (ignoreAliasinfo_spec h x).2.2.2.2.2.1, (ignoreAliasinfo_spec h x).2.2.2.2.2.2, ignoreAliasinfo_exact x⟩

/-- The interprocedural summary keeps the all-escape and thrown-escape facts at the call site;
the return escape is carried by the alias change `escape_invoke!` adds instead. -/
def InterproceduralSpec : Prop :=
  ∀ (h : Heap) (x : EscapeInfo) (pc : Int),
    (aHasAllEscape (argEscapeInfo x) = isTop x) ∧
    (aHasReturnEscape (argEscapeInfo x) = (!isTop x && hasReturnEscape x)) ∧
    (aHasThrownEscape (argEscapeInfo x) = (!isTop x && hasThrownEscape x)) ∧
    (aHasNoEscape (argEscapeInfo x) = (!isTop x && !hasReturnEscape x && !hasThrownEscape x)) ∧
    (isTop x = true → isTop (fromInterprocedural h (argEscapeInfo x) pc).1 = true) ∧
    (hasThrownEscape x = true →
      hasThrownEscapeAt (fromInterprocedural h (argEscapeInfo x) pc).1 pc = true) ∧
    (isTop x = false → hasReturnEscape (fromInterprocedural h (argEscapeInfo x) pc).1 = false ∧
      (fromInterprocedural h (argEscapeInfo x) pc).1.alias = .bool true ∧
      ((fromInterprocedural h (argEscapeInfo x) pc).2.get
        (fromInterprocedural h (argEscapeInfo x) pc).1.live) = [pc]) ∧
    (isTop x = false →
      (fromInterprocedural h (argEscapeInfo x) pc).1.analyzed = true ∧
      (∀ k, (fromInterprocedural h (argEscapeInfo x) pc).1.thrown.elems.mem k = true ↔
        hasThrownEscape x = true ∧ k = pc) ∧
      (∀ r, RefOk h r → RefOk (fromInterprocedural h (argEscapeInfo x) pc).2 r ∧
        (fromInterprocedural h (argEscapeInfo x) pc).2.get r = h.get r) ∧
      ¬ RefOk h (fromInterprocedural h (argEscapeInfo x) pc).1.live)

theorem interproceduralSpec_proven : InterproceduralSpec := fun h x pc =>
  ⟨(interprocedural_spec h x pc).1, (interprocedural_spec h x pc).2.1, (interprocedural_spec h x pc).2.2.1,
    (interprocedural_spec h x pc).2.2.2.1, (interprocedural_spec h x pc).2.2.2.2.1,
    (interprocedural_spec h x pc).2.2.2.2.2.1, (interprocedural_spec h x pc).2.2.2.2.2.2,
    fromInterprocedural_exact h x pc⟩

/-- `⊏ₑ` is irreflexive, and returns true exactly when `x ⊑ₑ y` and not `y ⊑ₑ x`, false exactly
when `x ⊑ₑ y` is false or both directions hold. -/
def SqsubStrictSpec : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo), sqsubStrict h x x ≠ .ok true ∧
    (sqsubStrict h x y = .ok true → sqsub h x y = .ok true ∧ sqsub h y x = .ok false) ∧
    (sqsubStrict h x y = .ok true ↔ sqsub h x y = .ok true ∧ sqsub h y x = .ok false) ∧
    (sqsubStrict h x y = .ok false ↔
      sqsub h x y = .ok false ∨ (sqsub h x y = .ok true ∧ sqsub h y x = .ok true))

theorem sqsubStrictSpec_proven : SqsubStrictSpec := fun h x y =>
  ⟨(sqsubStrict_spec h x y).1, (sqsubStrict_spec h x y).2, (sqsubStrict_iff h x y).1, (sqsubStrict_iff h x y).2⟩

/-- The `⋤ₑ` docstring: it agrees with `⊏ₑ` wherever `x ⊑ₑ y` holds. -/
def SqsubNeSpec : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo), sqsub h x y = .ok true → sqsubNe h x y = sqsubStrict h x y

theorem sqsubNeSpec_proven : SqsubNeSpec := sqsubNe_spec

/-- `⊑ₑ` is reflexive. -/
def SqsubRefl : Prop := ∀ (h : Heap) (x : EscapeInfo), sqsub h x x = .ok true

theorem sqsubRefl_proven : SqsubRefl := sqsub_refl

/-- `merge_alias_info` loses no alias element: each argument is covered by the result, field by
field where both are indexable. -/
def MergeAliasInfoCovers : Prop :=
  (∀ (xa ya : AliasInfo), AliasCovers xa (mergeAliasInfo xa ya) ∧ AliasCovers ya (mergeAliasInfo xa ya)) ∧
  (∀ (xa ya : AliasInfo), AliasExact xa ya (mergeAliasInfo xa ya)) ∧
  (∀ (info : AInfo) (infos : List AInfo) (k : Int),
    k ∈ mergeToUnindexable info infos ↔ k ∈ info ∨ ∃ i ∈ infos, k ∈ i)

theorem mergeAliasInfoCovers_proven : MergeAliasInfoCovers :=
  ⟨mergeAliasInfo_covers, mergeAliasInfo_exact, mem_mergeToUnindexable⟩

/-- `⊔ₑ` computes each field exactly: the flags are or-ed, `ThrownEscape` and `Liveness` are the
unions (or `TOP` when either is `TOP`), `AliasInfo` is the exact merge, and no existing
`Liveness` set in the heap is changed. -/
def JoinExactSpec : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo), JoinExact h x y (join h x y).1 (join h x y).2

theorem joinExactSpec_proven : JoinExactSpec := join_exact

/-- `==` holds exactly when both have the same flags and the same sets in every field (with
the `TOP` constants compared by identity). -/
def EqSpec : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo),
    eqE h x y = true ↔
      (x.analyzed = y.analyzed ∧ x.returnEscape = y.returnEscape ∧
       (x.thrown = .top ↔ y.thrown = .top) ∧
       (x.thrown ≠ .top → ∀ k, x.thrown.elems.mem k = true ↔ y.thrown.elems.mem k = true) ∧
       AliasEquiv x.alias y.alias ∧
       (x.live = .top ↔ y.live = .top) ∧
       (x.live ≠ .top → ∀ k, (h.get x.live).mem k = true ↔ (h.get y.live).mem k = true))

theorem eqSpec_proven : EqSpec := eqE_iff

/-- Liveness references allocated in the heap; the analysis only builds such `EscapeInfo`s. -/
def RefsOk (h : Heap) (x : EscapeInfo) : Prop := RefOk h x.live

/-- `⊔ₑ` is commutative up to `==`. -/
def JoinCommutative : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo), RefsOk h x → RefsOk h y →
    eqE (join (join h x y).2 y x).2 (join h x y).1 (join (join h x y).2 y x).1 = true

/-- `⊔ₑ` is idempotent up to `==`. -/
def JoinIdempotent : Prop :=
  ∀ (h : Heap) (x : EscapeInfo), RefsOk h x → eqE (join h x x).2 (join h x x).1 x = true

/-- Joining the same information again changes nothing (`==`), which the convergence test of
`_propagate_escape_change!` needs to stop. -/
def JoinAbsorbs : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo), RefsOk h x → RefsOk h y →
    eqE (join (join h x y).2 (join h x y).1 y).2 (join (join h x y).2 (join h x y).1 y).1
      (join h x y).1 = true

/-- `⊔ₑ` is an upper bound in `⊑ₑ` when no argument is an object with zero fields (the ordinary
case of `compiler-escape-join-upper-bound`). -/
def JoinUpperBoundNonempty : Prop :=
  ∀ (h : Heap) (x y : EscapeInfo), RefsOk h x → RefsOk h y →
    x.alias ≠ .indexable [] → y.alias ≠ .indexable [] →
    sqsub (join h x y).2 x (join h x y).1 = .ok true ∧ sqsub (join h x y).2 y (join h x y).1 = .ok true


theorem joinIdempotent_proven : JoinIdempotent := by
  intro h x hx
  obtain ⟨ha, hr, ht, ht2, hal, hl, hl2, hh, _⟩ := join_exact h x x
  apply eqE_of
  · simp [ha]
  · simp [hr]
  · simpa using ht
  · intro c k; rw [ht2 c k]; exact or_self_iff
  · exact exact_idem _ _ hal
  · simpa using hl
  · intro c k; rw [hl2 c k, (hh _ hx).2]; exact or_self_iff

theorem joinCommutative_proven : JoinCommutative := by
  intro h x y hx hy
  obtain ⟨ha, hr, ht, ht2, hal, hl, hl2, hh, hj⟩ := join_exact h x y
  obtain ⟨ha', hr', ht', ht2', hal', hl', hl2', hh', _⟩ :=
    join_exact (join h x y).2 y x
  apply eqE_of
  · simp [ha, ha', Bool.or_comm]
  · simp [hr, hr', Bool.or_comm]
  · rw [ht, ht', or_comm]
  · intro c k
    have c' : (join (join h x y).2 y x).1.thrown ≠ .top := by rw [ne_eq, ht', or_comm, ← ht]; exact c
    rw [ht2 c k, ht2' c' k, or_comm]
  · exact exact_comm _ _ _ _ hal hal'
  · rw [hl, hl', or_comm]
  · intro c k
    have c' : (join (join h x y).2 y x).1.live ≠ .top := by rw [ne_eq, hl', or_comm, ← hl]; exact c
    rw [(hh' _ (hj hx hy)).2, hl2 c k, hl2' c' k, (hh _ hx).2, (hh _ hy).2, or_comm]

theorem joinAbsorbs_proven : JoinAbsorbs := by
  intro h x y hx hy
  obtain ⟨ha, hr, ht, ht2, hal, hl, hl2, hh, hj⟩ := join_exact h x y
  obtain ⟨ha', hr', ht', ht2', hal', hl', hl2', hh', _⟩ :=
    join_exact (join h x y).2 (join h x y).1 y
  apply eqE_of
  · rw [ha', ha]; cases x.analyzed <;> cases y.analyzed <;> rfl
  · rw [hr', hr]; cases x.returnEscape <;> cases y.returnEscape <;> rfl
  · rw [ht', ht]; constructor
    · rintro ((m | m) | m) <;> simp [m]
    · rintro (m | m) <;> simp [m]
  · intro c k
    have c1 : (join h x y).1.thrown ≠ .top := fun e => c (ht'.2 (Or.inl e))
    rw [ht2' c k, ht2 c1 k]
    constructor
    · rintro ((m | m) | m) <;> simp [m]
    · rintro (m | m) <;> simp [m]
  · exact exact_absorb _ _ _ _ hal hal'
  · rw [hl', hl]; constructor
    · rintro ((m | m) | m) <;> simp [m]
    · rintro (m | m) <;> simp [m]
  · intro c k
    have c1 : (join h x y).1.live ≠ .top := fun e => c (hl'.2 (Or.inl e))
    rw [hl2' c k, (hh' _ (hj hx hy)).2, hl2 c1 k, (hh _ hy).2]
    constructor
    · rintro ((m | m) | m) <;> simp [m]
    · rintro (m | m) <;> simp [m]

theorem joinUpperBoundNonempty_proven : JoinUpperBoundNonempty := by
  intro h x y hx hy hnx hny
  obtain ⟨ha, hr, ht, ht2, hal, hl, hl2, hh, _⟩ := join_exact h x y
  rcases join_cases h x y with ⟨_, e⟩ | ⟨_, bx, e⟩ | ⟨_, _, by_, e⟩ | ⟨t, bx, by_, e⟩
  · rw [e]; exact ⟨sqsub_top_right _ _ _ rfl, sqsub_top_right _ _ _ rfl⟩
  · rw [e]; exact ⟨sqsub_bot_left _ _ _ bx, sqsub_refl _ _⟩
  · rw [e]; exact ⟨sqsub_refl _ _, sqsub_bot_left _ _ _ by_⟩
  · have tx : isTop x = false := by simp at t; simp [t.1]
    have ty : isTop y = false := by simp at t; simp [t.2]
    have bj : isBot (join h x y).1 = false := by
      rw [e]
      cases c : isBot (⟨x.analyzed || y.analyzed, x.returnEscape || y.returnEscape, jthrown x y,
        mergeAliasInfo x.alias y.alias, (jlive h x y).1⟩ : EscapeInfo)
      · rfl
      · obtain ⟨a, r, th, al, l⟩ := isBot_fields c
        simp only [Bool.or_eq_false_iff] at a r
        have := (jthrown_bot x y th).1
        have := (jlive_bot h x y l).1
        have := (merge_false _ _ al).1
        simp_all [isBot]
    refine ⟨le_join h _ x _ hx hh tx bx bj ?_ ?_ ?_ ?_ (alias_le_left _ _ _ hal hnx) ?_ ?_,
      le_join h _ y _ hy hh ty by_ bj ?_ ?_ ?_ ?_ (alias_le_right _ _ _ hal hny) ?_ ?_⟩
    · intro c; simp [ha, c]
    · intro c; simp [hr, c]
    · intro c; exact ht.2 (Or.inl c)
    · intro c k m; exact (ht2 c k).2 (Or.inl m)
    · intro c; exact hl.2 (Or.inl c)
    · intro c k m; exact (hl2 c k).2 (Or.inl m)
    · intro c; simp [ha, c]
    · intro c; simp [hr, c]
    · intro c; exact ht.2 (Or.inr c)
    · intro c k m; exact (ht2 c k).2 (Or.inr m)
    · intro c; exact hl.2 (Or.inr c)
    · intro c k m; exact (hl2 c k).2 (Or.inr m)


/-! ## Registry entries -/

private def ea : String := "Compiler/src/ssair/EscapeAnalysis.jl"

def entries : List Entry := [
  { id := "compiler-escape-has-no-escape-monotone", juliaFile := ea,
    juliaFns := ["has_no_escape(x::EscapeInfo)", "x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo ⊔ₑ y::EscapeInfo"],
    statement := "For every heap and EscapeInfos x, y: if x ⊑ₑ y returns true and has_no_escape(y), then has_no_escape(x); has_no_escape(x ⊔ₑ y) == has_no_escape(x) && has_no_escape(y); has_no_escape(x) == !has_return_escape(x) && !has_thrown_escape(x) && !has_arg_escape(x); and it is true on NoEscape() and ⊥ and false on ArgEscape(), ReturnEscape(pc), AllReturnEscape(), ThrownEscape(pc) and ⊤.",
    source := "invariant: every propagated change is a ⊔ₑ (Compiler/src/ssair/EscapeAnalysis.jl:734-743); finalizer inlining (passes.jl:1851) and the :effect_free refinement (optimize.jl:827-848) act on has_no_escape",
    status := .proven, prop := ``HasNoEscapeMonotone, thm := some ``hasNoEscapeMonotone_proven,
    notes := "No precondition on the heap. An unsound no-escape answer here would be a miscompile; none exists at the lattice level." },
  { id := "compiler-escape-has-arg-escape-monotone", juliaFile := ea,
    juliaFns := ["has_arg_escape(x::EscapeInfo)", "x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo ⊔ₑ y::EscapeInfo"],
    statement := "has_arg_escape is monotone along ⊑ₑ (when it returns true); has_arg_escape(x ⊔ₑ y) == has_arg_escape(x) || has_arg_escape(y); after push!(x.Liveness, p) on a non-constant set it is has_arg_escape(x) || p == 0; and it is true on ArgEscape(), AllReturnEscape() and ⊤, false on NoEscape(), ⊥ and ThrownEscape(pc), and p == 0 on ReturnEscape(p).",
    source := "invariant (lattice order, Compiler/src/ssair/EscapeAnalysis.jl:241-245)",
    status := .proven, prop := ``HasArgEscapeMonotone, thm := some ``hasArgEscapeMonotone_proven },
  { id := "compiler-escape-has-return-escape-monotone", juliaFile := ea,
    juliaFns := ["has_return_escape(x::EscapeInfo)", "x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo ⊔ₑ y::EscapeInfo"],
    statement := "has_return_escape is monotone along ⊑ₑ (when it returns true); has_return_escape(x ⊔ₑ y) == has_return_escape(x) || has_return_escape(y); and it is true on ReturnEscape(pc), AllReturnEscape() and ⊤ and false on NoEscape(), ⊥, ArgEscape() and ThrownEscape(pc).",
    source := "invariant (lattice order, Compiler/src/ssair/EscapeAnalysis.jl:241-245)",
    status := .proven, prop := ``HasReturnEscapeMonotone, thm := some ``hasReturnEscapeMonotone_proven },
  { id := "compiler-escape-has-return-escape-at-monotone", juliaFile := ea,
    juliaFns := ["has_return_escape(x::EscapeInfo, pc::Int)", "x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo ⊔ₑ y::EscapeInfo"],
    statement := "For every pc, has_return_escape(_, pc) is monotone along ⊑ₑ (when it returns true) and holds for x ⊔ₑ y whenever it holds for x or for y; it implies has_return_escape(x); after push!(x.Liveness, pc) on a non-constant set, has_return_escape(x, pc) == has_return_escape(x); on ReturnEscape(p) it is p == -1 || p == pc; it is true on AllReturnEscape() and ⊤ and false on NoEscape(), ⊥, ArgEscape() and ThrownEscape(p).",
    source := "invariant (lattice order, Compiler/src/ssair/EscapeAnalysis.jl:241-245)",
    status := .proven, prop := ``HasReturnEscapeAtMonotone, thm := some ``hasReturnEscapeAtMonotone_proven },
  { id := "compiler-escape-has-thrown-escape-monotone", juliaFile := ea,
    juliaFns := ["has_thrown_escape(x::EscapeInfo)", "x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo ⊔ₑ y::EscapeInfo"],
    statement := "has_thrown_escape is monotone along ⊑ₑ (when it returns true); has_thrown_escape(x ⊔ₑ y) == has_thrown_escape(x) || has_thrown_escape(y); and it is true on ThrownEscape(pc) and ⊤ and false on NoEscape(), ⊥, ArgEscape(), ReturnEscape(pc) and AllReturnEscape().",
    source := "invariant (lattice order, Compiler/src/ssair/EscapeAnalysis.jl:241-245)",
    status := .proven, prop := ``HasThrownEscapeMonotone, thm := some ``hasThrownEscapeMonotone_proven },
  { id := "compiler-escape-has-thrown-escape-at-monotone", juliaFile := ea,
    juliaFns := ["has_thrown_escape(x::EscapeInfo, pc::Int)", "x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo ⊔ₑ y::EscapeInfo"],
    statement := "For every pc, has_thrown_escape(_, pc) is monotone along ⊑ₑ (when it returns true); has_thrown_escape(x ⊔ₑ y, pc) == has_thrown_escape(x, pc) || has_thrown_escape(y, pc); it implies has_thrown_escape(x); on ThrownEscape(p) it is p == -1 || p == pc; it is true on ⊤ and false on NoEscape(), ⊥, ArgEscape(), ReturnEscape(p) and AllReturnEscape().",
    source := "invariant (lattice order, Compiler/src/ssair/EscapeAnalysis.jl:241-245); escape_exception! reads ThrownEscape (line 942)",
    status := .proven, prop := ``HasThrownEscapeAtMonotone, thm := some ``hasThrownEscapeAtMonotone_proven },
  { id := "compiler-escape-has-all-escape-monotone", juliaFile := ea,
    juliaFns := ["has_all_escape(x::EscapeInfo)", "AllEscape()", "x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo ⊔ₑ y::EscapeInfo"],
    statement := "has_all_escape(x) (⊤ ⊑ₑ x) is true exactly when x === ⊤; it is monotone along ⊑ₑ (when it returns true) and holds for x ⊔ₑ y whenever it holds for x or for y.",
    source := "invariant (lattice order, Compiler/src/ssair/EscapeAnalysis.jl:241-245)",
    status := .proven, prop := ``HasAllEscapeMonotone, thm := some ``hasAllEscapeMonotone_proven,
    notes := "So has_all_escape never reaches the slow path of ⊑ₑ, which is why the ⊑ₑ refutations below have no effect on the analysis." },
  { id := "compiler-escape-ignore-argescape", juliaFile := ea,
    juliaFns := ["ignore_argescape(x::EscapeInfo)"],
    statement := "ignore_argescape(x) has no argument escape, has_no_escape of it is !x.ReturnEscape && isempty(x.ThrownEscape), and it keeps has_return_escape, has_thrown_escape, has_thrown_escape(_, pc) and has_return_escape(_, pc) for pc ≠ 0; it keeps Analyzed, ReturnEscape, ThrownEscape and AliasInfo; its Liveness holds exactly the elements of x.Liveness other than 0, in a newly allocated set, and no existing set (x.Liveness included) is changed.",
    source := "name and Compiler/src/optimize.jl:827-828 (has_no_escape(ignore_argescape(x)) decides :effect_free_if_argmem_only)",
    status := .proven, prop := ``IgnoreArgescapeSpec, thm := some ``ignoreArgescapeSpec_proven },
  { id := "compiler-escape-ignore-thrownescapes", juliaFile := ea,
    juliaFns := ["ignore_thrownescapes(x::EscapeInfo)"],
    statement := "ignore_thrownescapes(x) has no thrown escape at any pc, its has_no_escape is !x.ReturnEscape && 0 ∉ x.Liveness, and the return and argument queries are unchanged.",
    source := "name (Compiler/src/ssair/EscapeAnalysis.jl:160)",
    status := .proven, prop := ``IgnoreThrownescapesSpec, thm := some ``ignoreThrownescapesSpec_proven,
    notes := "Removed on current master (unused there)." },
  { id := "compiler-escape-ignore-liveness", juliaFile := ea,
    juliaFns := ["ignore_liveness(x::EscapeInfo)"],
    statement := "ignore_liveness(x) has no argument escape and no return escape at any pc; has_no_escape is !x.ReturnEscape && isempty(x.ThrownEscape); the other queries are unchanged; its Liveness is empty in every heap (so no later push! into a shared set reaches it), and Analyzed, ReturnEscape, ThrownEscape and AliasInfo are kept.",
    source := "name (Compiler/src/ssair/EscapeAnalysis.jl:162)",
    status := .proven, prop := ``IgnoreLivenessSpec, thm := some ``ignoreLivenessSpec_proven },
  { id := "compiler-escape-ignore-aliasinfo", juliaFile := ea,
    juliaFns := ["ignore_aliasinfo(x::EscapeInfo)"],
    statement := "ignore_aliasinfo(x) is never has_all_escape, and every other escape query gives the same answer as on x; its AliasInfo is the identity of merge_alias_info on both sides (so joining it never changes another value's alias information); and it keeps Analyzed, ReturnEscape, ThrownEscape and the same Liveness object.",
    source := "name (Compiler/src/ssair/EscapeAnalysis.jl:161); used to pass an object's escapes to its fields (lines 1197, 1222, 1381)",
    status := .proven, prop := ``IgnoreAliasinfoSpec, thm := some ``ignoreAliasinfoSpec_proven },
  { id := "compiler-escape-interprocedural", juliaFile := ea,
    juliaFns := ["ArgEscapeInfo(x::EscapeInfo)", "has_no_escape(x::ArgEscapeInfo)", "has_all_escape(x::ArgEscapeInfo)",
      "has_return_escape(x::ArgEscapeInfo)", "has_thrown_escape(x::ArgEscapeInfo)", "from_interprocedural(argescape::ArgEscapeInfo, pc::Int)"],
    statement := "ArgEscapeInfo(x) has the all-escape bit exactly when x === ⊤, and otherwise the return and thrown bits of x; from_interprocedural(ArgEscapeInfo(x), pc) is ⊤ when x is, has a thrown escape at pc when x has any thrown escape, and otherwise is analyzed, not returned, unanalyzable (AliasInfo true), live exactly at pc in a newly allocated set (no existing set changes), and its ThrownEscape holds exactly pc when x has a thrown escape and nothing otherwise.",
    source := "docstring of from_interprocedural (Compiler/src/ssair/EscapeAnalysis.jl:1026-1031) and escape_invoke! (lines 1008-1023)",
    status := .proven, prop := ``InterproceduralSpec, thm := some ``interproceduralSpec_proven },
  { id := "compiler-escape-sqsub-strict", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊏ₑ y::EscapeInfo"],
    statement := "x ⊏ₑ x is never true; x ⊏ₑ y returns true exactly when x ⊑ₑ y returns true and y ⊑ₑ x returns false, and returns false exactly when x ⊑ₑ y returns false or both directions return true.",
    source := "docstring Compiler/src/ssair/EscapeAnalysis.jl:302-307 (the irreflexive kernel of ⊑ₑ)",
    status := .proven, prop := ``SqsubStrictSpec, thm := some ``sqsubStrictSpec_proven },
  { id := "compiler-escape-sqsub-ne", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⋤ₑ y::EscapeInfo"],
    statement := "Whenever x ⊑ₑ y returns true, x ⋤ₑ y gives the same result as x ⊏ₑ y.",
    source := "docstring Compiler/src/ssair/EscapeAnalysis.jl:310-315",
    status := .proven, prop := ``SqsubNeSpec, thm := some ``sqsubNeSpec_proven },
  { id := "compiler-escape-sqsub-refl", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊑ₑ y::EscapeInfo"],
    statement := "x ⊑ₑ x returns true for every EscapeInfo, including one with an empty IndexableFields.",
    source := "invariant (⊑ₑ is the partial order of the lattice, Compiler/src/ssair/EscapeAnalysis.jl:241-245)",
    status := .proven, prop := ``SqsubRefl, thm := some ``sqsubRefl_proven },
  { id := "compiler-escape-merge-alias-covers", juliaFile := ea,
    juliaFns := ["merge_alias_info(@nospecialize(xa), @nospecialize(ya))",
      "merge_to_unindexable(AliasInfo::Unindexable, AliasInfos::IndexableFields)",
      "merge_to_unindexable(info::AInfo, infos::Vector{AInfo})"],
    statement := "merge_alias_info(xa, ya) is exactly the merge: true when either is true; the other argument when one is false; for two IndexableFields, max(length) fields with field i holding exactly the union of field i of each; otherwise an Unindexable holding exactly the union of every set of both. merge_to_unindexable(info, infos) holds exactly info ∪ every set of infos. In particular no LocalDef/LocalUse is lost and none is added.",
    source := "invariant: add_alias_escapes! (Compiler/src/ssair/EscapeAnalysis.jl:828-835) reads the merged sets to connect loads with stores",
    status := .proven, prop := ``MergeAliasInfoCovers, thm := some ``mergeAliasInfoCovers_proven },
  { id := "compiler-escape-join-exact", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊔ₑ y::EscapeInfo", "merge_alias_info(@nospecialize(xa), @nospecialize(ya))"],
    statement := "For every heap and EscapeInfos x, y: x ⊔ₑ y has Analyzed = x.Analyzed | y.Analyzed and ReturnEscape = x.ReturnEscape | y.ReturnEscape; its ThrownEscape (and its Liveness) is TOP exactly when either argument's is, and otherwise holds exactly the union of the arguments' sets; its AliasInfo is the exact merge of compiler-escape-merge-alias-covers; no existing Liveness set changes; and its Liveness is allocated when the arguments' are.",
    source := "docstring Compiler/src/ssair/EscapeAnalysis.jl:318-322 (computes the join) and the EscapeInfo docstring (lines 45-82)",
    status := .proven, prop := ``JoinExactSpec, thm := some ``joinExactSpec_proven,
    notes := "Holds through the ⊤ and ⊥ fast paths too, so they agree with the general case." },
  { id := "compiler-escape-eq-sets", juliaFile := ea,
    juliaFns := ["x::EscapeInfo == y::EscapeInfo"],
    statement := "x == y returns true exactly when x and y have the same Analyzed and ReturnEscape, ThrownEscape is TOP in both or in neither (and then holds the same elements), AliasInfo is the same Bool or the same kind holding the same sets (field by field for IndexableFields, with the same number of fields), and Liveness is TOP in both or in neither (and then holds the same elements).",
    source := "invariant (== is the lattice equality, Compiler/src/ssair/EscapeAnalysis.jl:186-187); _propagate_escape_change! tests `old ≠ new` (line 738)",
    status := .proven, prop := ``EqSpec, thm := some ``eqSpec_proven,
    notes := "The model leaves out the `x === y` fast path, which never changes the result." },
  { id := "compiler-escape-sqsub-transitive", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊑ₑ y::EscapeInfo"],
    statement := "⊑ₑ is transitive: x ⊑ₑ y and y ⊑ₑ z imply x ⊑ₑ z.",
    source := "invariant (⊑ₑ is the partial order of the lattice, Compiler/src/ssair/EscapeAnalysis.jl:241-245)",
    status := .refuted, prop := ``SqsubTransitive, thm := some ``sqsubTransitive_refuted,
    issue := "none found (queries: EscapeAnalysis ⊑ₑ, EscapeAnalysis IndexableFields Unindexable, escape analysis lattice transitive, EscapeInfo BoundsError, EscapeAnalysis length(xinfos); issues and PRs)",
    notes := "x = IndexableFields([{LocalUse(2)}]), y = IndexableFields([{LocalUse(2)}, {}]), z = Unindexable({}), on NoEscape. The IndexableFields/Unindexable case loops `for i = length(xinfos)` (line 278) and checks only the last field. P3: ⊑ₑ is only reached through has_all_escape, which stops at the fast path." },
  { id := "compiler-escape-sqsub-join-agree", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo ⊔ₑ y::EscapeInfo"],
    statement := "⊑ₑ agrees with ⊔ₑ: x ⊑ₑ y implies x ⊔ₑ y == y.",
    source := "invariant (lattice order and join, Compiler/src/ssair/EscapeAnalysis.jl:241-245, 318-322)",
    status := .refuted, prop := ``SqsubJoinAgree, thm := some ``sqsubJoinAgree_refuted,
    issue := "none found (same queries as compiler-escape-sqsub-transitive)",
    notes := "x = IndexableFields([{LocalUse(2)}, {}]), y = Unindexable({}): x ⊑ₑ y, but x ⊔ₑ y = Unindexable({LocalUse(2)}). Same cause as compiler-escape-sqsub-transitive." },
  { id := "compiler-escape-join-upper-bound", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊔ₑ y::EscapeInfo", "x::EscapeInfo ⊑ₑ y::EscapeInfo"],
    statement := "⊔ₑ is an upper bound: x ⊑ₑ x ⊔ₑ y and y ⊑ₑ x ⊔ₑ y return true.",
    source := "docstring Compiler/src/ssair/EscapeAnalysis.jl:318-322 (computes the join)",
    status := .refuted, prop := ``JoinUpperBound, thm := some ``joinUpperBound_refuted,
    issue := "none found (same queries as compiler-escape-sqsub-transitive)",
    notes := "x = IndexableFields([]) (an object with no fields), y = Unindexable({}): x ⊑ₑ x ⊔ₑ y throws BoundsError (xinfos[0], line 279). The ordinary case is compiler-escape-join-upper-bound-nonempty." },
  { id := "compiler-escape-sqsub-respects-eq", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊑ₑ y::EscapeInfo", "x::EscapeInfo == y::EscapeInfo", "ignore_argescape(x::EscapeInfo)", "NotAnalyzed()"],
    statement := "⊑ₑ respects ==: x == y implies x ⊑ₑ y.",
    source := "invariant (== is the lattice equality, Compiler/src/ssair/EscapeAnalysis.jl:186-187)",
    status := .refuted, prop := ``SqsubRespectsEq, thm := some ``sqsubRespectsEq_refuted,
    issue := "none found (queries: EscapeAnalysis ⊑ₑ, EscapeAnalysis ignore_argescape, EscapeInfo BoundsError; issues and PRs)",
    notes := "x = ignore_argescape(⊥) has a fresh empty Liveness, so x == ⊥ but x !== ⊥, and the fast path `y === ⊥ && return false` (line 254) answers x ⊑ₑ ⊥ = false. P3: no consumer." },
  { id := "compiler-escape-join-commutative", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊔ₑ y::EscapeInfo", "x::EscapeInfo == y::EscapeInfo"],
    statement := "x ⊔ₑ y == y ⊔ₑ x for EscapeInfos whose Liveness sets are allocated.",
    source := "invariant (lattice join)",
    status := .proven, prop := ``JoinCommutative, thm := some ``joinCommutative_proven,
    notes := "Proven from compiler-escape-join-exact and compiler-escape-eq-sets." },
  { id := "compiler-escape-join-idempotent", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊔ₑ y::EscapeInfo", "x::EscapeInfo == y::EscapeInfo"],
    statement := "x ⊔ₑ x == x for EscapeInfos whose Liveness set is allocated.",
    source := "invariant (lattice join)",
    status := .proven, prop := ``JoinIdempotent, thm := some ``joinIdempotent_proven,
    notes := "Proven from compiler-escape-join-exact and compiler-escape-eq-sets." },
  { id := "compiler-escape-join-absorbs", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊔ₑ y::EscapeInfo", "x::EscapeInfo == y::EscapeInfo", "_propagate_escape_change!(@specialize(op), estate::EscapeState, xidx::Int, info::EscapeInfo)"],
    statement := "(x ⊔ₑ y) ⊔ₑ y == x ⊔ₑ y, so repeating a change is reported as no change and the fixed point can stop.",
    source := "invariant (termination of analyze_escapes, Compiler/src/ssair/EscapeAnalysis.jl:586-664)",
    status := .proven, prop := ``JoinAbsorbs, thm := some ``joinAbsorbs_proven,
    notes := "Proven from compiler-escape-join-exact and compiler-escape-eq-sets. So the `old ≠ new` test in _propagate_escape_change! (line 738) reports a repeated change as no change." },
  { id := "compiler-escape-join-upper-bound-nonempty", juliaFile := ea,
    juliaFns := ["x::EscapeInfo ⊔ₑ y::EscapeInfo", "x::EscapeInfo ⊑ₑ y::EscapeInfo"],
    statement := "x ⊑ₑ x ⊔ₑ y and y ⊑ₑ x ⊔ₑ y when neither AliasInfo is an IndexableFields with zero fields.",
    source := "docstring Compiler/src/ssair/EscapeAnalysis.jl:318-322",
    status := .proven, prop := ``JoinUpperBoundNonempty, thm := some ``joinUpperBoundNonempty_proven,
    notes := "Ordinary case of compiler-escape-join-upper-bound: only an object with zero fields joined with an Unindexable hits the BoundsError." }
]

end JuliaLean.Proofs.Compiler.src.ssair.EscapeAnalysis
