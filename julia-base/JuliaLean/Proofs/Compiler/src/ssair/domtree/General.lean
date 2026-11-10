import JuliaLean.Proofs.Compiler.src.ssair.domtree.Basic

/-!
General properties, over all inputs, of the CFG edits of `Compiler/src/ssair/ir.jl`, of the
tree queries `_dominates` and `nearest_common_dominator`, and of the small helpers of
`Compiler/src/ssair/domtree.jl`.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.domtree

open JuliaLean.Compiler.ssair

theorem erase_of_findIdx (xs : Array Int) (v : Int) (i : Nat)
    (h : xs.findIdx? (· == v) = some i) : (xs.eraseIdxIfInBounds i).toList = xs.toList.erase v := by
  rcases xs with ⟨l⟩
  simp only [List.findIdx?_toArray] at h
  rw [Array.toList_eraseIdxIfInBounds, List.erase_eq_eraseIdx]
  simp [List.idxOf?, h]

theorem findfirst_none (xs : Array Int) (v : Int) : v ∉ xs.toList → findfirstInt xs v = .error "julia:TypeError" := by
  intro hv
  unfold findfirstInt
  rcases xs with ⟨l⟩
  have : List.findIdx? (· == v) l = none := by
    rw [List.findIdx?_eq_none_iff]; intro x hx; simp; rintro rfl; exact hv (by simpa using hx)
  simp [List.findIdx?_toArray, this]; rfl

theorem findfirst_some (xs : Array Int) (v : Int) : v ∈ xs.toList → ∃ i, findfirstInt xs v = .ok i ∧ xs.findIdx? (· == v) = some i := by
  intro hv
  unfold findfirstInt
  cases h : xs.findIdx? (· == v) with
  | none =>
    rcases xs with ⟨l⟩
    simp only [List.findIdx?_toArray, List.findIdx?_eq_none_iff] at h
    have := h v (by simpa using hv); simp at this
  | some i => exact ⟨i, rfl, rfl⟩

def inR (blocks : Blocks) (x : Int) : Prop := 1 ≤ x ∧ (x - 1).toNat < blocks.size

theorem aget_ok {α} (a : Array α) (i : Int) (h : 1 ≤ i ∧ (i - 1).toNat < a.size) :
    aget a i = .ok (a[(i - 1).toNat]'h.2) := by unfold aget; rw [dite_eq_left_of_eq_true (eq_true h)]; rfl
theorem aget_err {α} (a : Array α) (i : Int) (h : ¬ (1 ≤ i ∧ (i - 1).toNat < a.size)) :
    aget a i = .error "julia:BoundsError" := by unfold aget; rw [dite_eq_right_of_eq_false (eq_false h)]; rfl
theorem aset_ok {α} (a : Array α) (i : Int) (v : α) (h : 1 ≤ i ∧ (i - 1).toNat < a.size) :
    aset a i v = .ok (a.setIfInBounds (i - 1).toNat v) := by unfold aset; rw [ite_eq_left_of_eq_true _ _ (eq_true h)]; rfl
theorem aset_err {α} (a : Array α) (i : Int) (v : α) (h : ¬ (1 ≤ i ∧ (i - 1).toNat < a.size)) :
    aset a i v = .error "julia:BoundsError" := by unfold aset; rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl
theorem aget_set_ok {α} {a : Array α} {j : Nat} {v : α} (i : Int) (h : 1 ≤ i ∧ (i - 1).toNat < a.size) :
    aget (a.setIfInBounds j v) i = .ok ((a.setIfInBounds j v)[(i - 1).toNat]'(by simpa using h.2)) :=
  aget_ok _ _ (by simpa using h)
theorem aget_set_err {α} {a : Array α} {j : Nat} {v : α} (i : Int) (h : ¬ (1 ≤ i ∧ (i - 1).toNat < a.size)) :
    aget (a.setIfInBounds j v) i = .error "julia:BoundsError" :=
  aget_err _ _ (by simpa using h)
theorem aset_set_ok {α} {a : Array α} {j : Nat} {v : α} (i : Int) (w : α) (h : 1 ≤ i ∧ (i - 1).toNat < a.size) :
    aset (a.setIfInBounds j v) i w = .ok ((a.setIfInBounds j v).setIfInBounds (i - 1).toNat w) :=
  aset_ok _ _ _ (by simpa using h)

/-- `cfg_insert_edge!(cfg, f, t)` (Compiler/src/ssair/ir.jl:14-19), for any blocks: a
`BoundsError` when `f` or `t` is not a block; otherwise it appends `t` to the successors of `f`
and `f` to the predecessors of `t` (both when `f = t`) and changes nothing else. -/
def CfgInsertSpec : Prop := ∀ (blocks : Blocks) (f t : Int),
  (¬ (inR blocks f ∧ inR blocks t) → cfgInsertEdge blocks f t = .error "julia:BoundsError") ∧
  (inR blocks f → inR blocks t → ∃ b2, cfgInsertEdge blocks f t = .ok b2 ∧ b2.size = blocks.size ∧
    ∀ i : Nat, i < blocks.size →
      (b2.getD i default).succs.toList = (blocks.getD i default).succs.toList ++ (if (i : Int) + 1 = f then [t] else []) ∧
      (b2.getD i default).preds.toList = (blocks.getD i default).preds.toList ++ (if (i : Int) + 1 = t then [f] else []))

theorem cfgInsertSpec_proven : CfgInsertSpec := by
  intro blocks f t
  constructor
  · intro h
    unfold cfgInsertEdge
    by_cases ht : inR blocks t
    · have hf : ¬ inR blocks f := fun hf => h ⟨hf, ht⟩
      simp only [aget_ok _ _ ht, aset_ok _ _ _ ht, bind, Except.bind, aget_set_err _ hf]
    · simp only [aget_err _ _ ht, bind, Except.bind]
  · intro hf ht
    unfold cfgInsertEdge
    simp only [aget_ok _ _ ht, aset_ok _ _ _ ht, bind, Except.bind, aget_set_ok _ hf, aset_set_ok _ _ hf]
    refine ⟨_, rfl, by simp, fun i hi => ?_⟩
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
    have e1 : ((f - 1).toNat = i) ↔ ((i : Int) + 1 = f) := by unfold inR at hf; omega
    have e2 : ((t - 1).toNat = i) ↔ ((i : Int) + 1 = t) := by unfold inR at ht; omega
    by_cases a1 : (i : Int) + 1 = f <;> by_cases a2 : (i : Int) + 1 = t <;>
      simp_all

/-- `cfg_delete_edge!(cfg, f, t)` (Compiler/src/ssair/ir.jl:21-28), for any blocks: a
`BoundsError` when `f` or `t` is not a block; a `TypeError` (the `::Int` assertion on
`findfirst`) when `f` is not a predecessor of `t`, or `t` not a successor of `f`; otherwise it
removes the first `f` from the predecessors of `t` and the first `t` from the successors of `f`
and changes nothing else. -/
def CfgDeleteSpec : Prop := ∀ (blocks : Blocks) (f t : Int),
  (¬ (inR blocks f ∧ inR blocks t) → cfgDeleteEdge blocks f t = .error "julia:BoundsError") ∧
  (inR blocks f → inR blocks t → f ∉ (blocks.getD (t - 1).toNat default).preds.toList →
    cfgDeleteEdge blocks f t = .error "julia:TypeError") ∧
  (inR blocks f → inR blocks t → f ∈ (blocks.getD (t - 1).toNat default).preds.toList →
    t ∉ (blocks.getD (f - 1).toNat default).succs.toList →
    cfgDeleteEdge blocks f t = .error "julia:TypeError") ∧
  (inR blocks f → inR blocks t → f ∈ (blocks.getD (t - 1).toNat default).preds.toList →
    t ∈ (blocks.getD (f - 1).toNat default).succs.toList →
    ∃ b2, cfgDeleteEdge blocks f t = .ok b2 ∧ b2.size = blocks.size ∧
    ∀ i : Nat, i < blocks.size →
      (b2.getD i default).succs.toList =
        (if (i : Int) + 1 = f then (blocks.getD i default).succs.toList.erase t
         else (blocks.getD i default).succs.toList) ∧
      (b2.getD i default).preds.toList =
        (if (i : Int) + 1 = t then (blocks.getD i default).preds.toList.erase f
         else (blocks.getD i default).preds.toList))

theorem getD_of_inR (blocks : Blocks) (x : Int) (h : inR blocks x) :
    blocks.getD (x - 1).toNat default = blocks[(x - 1).toNat]'h.2 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h.2]; rfl

theorem cfgDeleteSpec_proven : CfgDeleteSpec := by
  intro blocks f t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    unfold cfgDeleteEdge
    by_cases ht : inR blocks t
    · have hf : ¬ inR blocks f := fun hf => h ⟨hf, ht⟩
      simp only [aget_ok _ _ ht, bind, Except.bind, aget_err _ _ hf]
    · simp only [aget_err _ _ ht, bind, Except.bind]
  · intro hf ht hp
    rw [getD_of_inR _ _ ht] at hp
    unfold cfgDeleteEdge
    simp only [aget_ok _ _ ht, aget_ok _ _ hf, bind, Except.bind, findfirst_none _ _ hp]
  · intro hf ht hp hs
    rw [getD_of_inR _ _ ht] at hp
    rw [getD_of_inR _ _ hf] at hs
    obtain ⟨i, hi, _⟩ := findfirst_some _ _ hp
    unfold cfgDeleteEdge
    simp only [aget_ok _ _ ht, aget_ok _ _ hf, bind, Except.bind, hi, aset_ok _ _ _ ht,
      findfirst_none _ _ hs]
  · intro hf ht hp hs
    rw [getD_of_inR _ _ ht] at hp
    rw [getD_of_inR _ _ hf] at hs
    obtain ⟨i, hi, hi'⟩ := findfirst_some _ _ hp
    obtain ⟨j, hj, hj'⟩ := findfirst_some _ _ hs
    unfold cfgDeleteEdge
    simp only [aget_ok _ _ ht, aget_ok _ _ hf, bind, Except.bind, hi, aset_ok _ _ _ ht, hj,
      aget_set_ok _ hf, aset_set_ok _ _ hf]
    refine ⟨_, rfl, by simp, fun k hk => ?_⟩
    have e1 : ((f - 1).toNat = k) ↔ ((k : Int) + 1 = f) := by unfold inR at hf; omega
    have e2 : ((t - 1).toNat = k) ↔ ((k : Int) + 1 = t) := by unfold inR at ht; omega
    have E1 := erase_of_findIdx _ _ _ hi'
    have E2 := erase_of_findIdx _ _ _ hj'
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
    by_cases a1 : (k : Int) + 1 = f <;> by_cases a2 : (k : Int) + 1 = t <;>
      simp_all

/-! ### `_dominates` on any tree with consistent levels -/

def lvl (dt : GenericDomTree) (b : Int) : Int := (dt.nodes.getD (b - 1).toNat default).level
def idm (dt : GenericDomTree) (b : Int) : Int := if 1 ≤ b then dt.idomsBB.getD (b - 1).toNat 0 else 0
def inB (dt : GenericDomTree) (b : Int) : Prop := 1 ≤ b ∧ b ≤ dt.nodes.size

/-- A tree whose levels are consistent with its `idoms_bb`, as `compute_domtree_nodes!` and
`update_level!` are meant to leave it ("How deep we are in the DomTree", domtree.jl:214): one
`idoms_bb` entry per node, every level at least 1, a root (`idoms_bb[b] == 0`) at level 1, and
every other node one level below its parent, which is a node. Nothing else is assumed: there can be
several roots, as in a post-dominator tree or with unreachable blocks. -/
def LevelOK (dt : GenericDomTree) : Prop :=
  dt.idomsBB.size = dt.nodes.size ∧ ∀ b, inB dt b →
    1 ≤ lvl dt b ∧ (idm dt b = 0 → lvl dt b = 1) ∧
    (idm dt b ≠ 0 → inB dt (idm dt b) ∧ lvl dt (idm dt b) + 1 = lvl dt b)

/-- `idoms_bb` applied `k` times, staying at 0. `anc dt c x` (`∃ k, up dt k x = c`) is "`c` is
`x` or an ancestor of `x` in the tree". -/
def up (dt : GenericDomTree) : Nat → Int → Int
  | 0, b => b
  | k + 1, b => up dt k (idm dt b)

theorem up_zero (dt : GenericDomTree) : ∀ k, up dt k 0 = 0
  | 0 => rfl
  | k + 1 => by simp [up, idm, up_zero dt k]

theorem up_descend (dt : GenericDomTree) (h : LevelOK dt) : ∀ (k : Nat) b, inB dt b → (k : Int) < lvl dt b →
    inB dt (up dt k b) ∧ lvl dt (up dt k b) = lvl dt b - k := by
  intro k
  induction k with
  | zero => intro b hb _; simp [up, hb]
  | succ k ih =>
    intro b hb hk
    obtain ⟨_, h0, h1⟩ := h.2 b hb
    have hne : idm dt b ≠ 0 := fun e => by have := h0 e; omega
    obtain ⟨hi, hl⟩ := h1 hne
    obtain ⟨r1, r2⟩ := ih (idm dt b) hi (by omega)
    exact ⟨r1, by simp only [up]; omega⟩

theorem up_root (dt : GenericDomTree) (h : LevelOK dt) : ∀ (k : Nat) b, inB dt b → lvl dt b ≤ (k : Int) →
    up dt k b = 0 := by
  intro k
  induction k with
  | zero => intro b hb hk; have := (h.2 b hb).1; omega
  | succ k ih =>
    intro b hb hk
    obtain ⟨_, _, h1⟩ := h.2 b hb
    by_cases hz : idm dt b = 0
    · simp [up, hz, up_zero]
    · obtain ⟨hi, hl⟩ := h1 hz
      simp only [up]; exact ih _ hi (by omega)

def stepN (dt : GenericDomTree) : Nat → Int → JM Int
  | 0, b => pure b
  | m + 1, b => do stepN dt m (← aget dt.idomsBB b)

theorem foldlM_const (dt : GenericDomTree) : ∀ (l : List Int) (x : Int),
    l.foldlM (fun b _ => aget dt.idomsBB b) x = stepN dt l.length x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons a l ih => intro x; simp only [List.foldlM_cons, stepN, List.length_cons, ih]

theorem aget_idm (dt : GenericDomTree) (h : LevelOK dt) (b : Int) (hb : inB dt b) :
    aget dt.idomsBB b = .ok (idm dt b) := by
  have : 1 ≤ b ∧ (b - 1).toNat < dt.idomsBB.size := by unfold inB at hb; rw [h.1]; omega
  rw [aget_ok _ _ this]
  simp only [idm, ite_eq_left_of_eq_true _ _ (eq_true hb.1)]; rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem this.2]; rfl

theorem stepN_up (dt : GenericDomTree) (h : LevelOK dt) : ∀ (m : Nat) b, inB dt b → (m : Int) < lvl dt b →
    stepN dt m b = .ok (up dt m b) := by
  intro m
  induction m with
  | zero => intro b _ _; rfl
  | succ m ih =>
    intro b hb hm
    obtain ⟨_, h0, h1⟩ := h.2 b hb
    have hne : idm dt b ≠ 0 := fun e => by have := h0 e; omega
    obtain ⟨hi, hl⟩ := h1 hne
    simp only [stepN, aget_idm dt h b hb, bind, Except.bind, up]
    exact ih _ hi (by omega)

theorem aget_nodes (dt : GenericDomTree) (b : Int) (hb : inB dt b) :
    ∃ n, aget dt.nodes b = .ok n ∧ n.level = lvl dt b := by
  have : 1 ≤ b ∧ (b - 1).toNat < dt.nodes.size := by unfold inB at hb; omega
  refine ⟨_, aget_ok _ _ this, ?_⟩
  simp only [lvl]; rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem this.2]; rfl

/-- `_dominates(dt, a, b)` (Compiler/src/ssair/domtree.jl:659-668), which `dominates` and
`postdominates` (lines 645-657) call, on any tree with consistent levels and any nodes `a`, `b`:
it returns, and the result is true exactly when `a` is `b` or an ancestor of `b`. -/
def DominatesWalkSpec : Prop := ∀ dt, LevelOK dt → ∀ a b, inB dt a → inB dt b →
  ∃ r, dominates dt a b = .ok r ∧ (r = true ↔ ∃ k, up dt k b = a)

theorem dominatesWalkSpec_proven : DominatesWalkSpec := by
  intro dt h a b ha hb
  by_cases hab : a = b
  · subst hab; exact ⟨true, by simp [dominates]; rfl, by simp; exact ⟨0, rfl⟩⟩
  obtain ⟨na, hna, hla⟩ := aget_nodes dt a ha
  obtain ⟨nb, hnb, hlb⟩ := aget_nodes dt b hb
  have hab' : (a == b) = false := by simpa using hab
  -- every k with up k b = a is lvl b - lvl a
  have key : ∀ k, up dt k b = a → (k : Int) = lvl dt b - lvl dt a := by
    intro k hk
    by_cases hk' : (k : Int) < lvl dt b
    · have := (up_descend dt h k b hb hk').2; rw [hk] at this; omega
    · have := up_root dt h k b hb (by omega); rw [hk] at this; have := ha.1; omega
  have hpa := (h.2 a ha).1
  by_cases hlt : lvl dt b < lvl dt a
  · refine ⟨false, ?_, ?_⟩
    · simp only [dominates, hab', hna, hnb, bind, Except.bind, hla, hlb, hlt]; rfl
    · simp only [Bool.false_eq_true, false_iff, not_exists]
      intro k hk; have := key k hk; omega
  · have hm : ((lvl dt b - 1 - lvl dt a + 1).toNat : Int) < lvl dt b := by omega
    have hs := stepN_up dt h _ b hb hm
    refine ⟨up dt (lvl dt b - 1 - lvl dt a + 1).toNat b == a, ?_, ?_⟩
    · simp only [dominates, hab', hna, hnb, bind, Except.bind, hla, hlb, hlt, foldlM_const,
        irange, List.length_map, List.length_range, hs]
      rw [Bool.beq_comm]; rfl
    · simp only [beq_iff_eq]
      constructor
      · intro e; exact ⟨_, e⟩
      · rintro ⟨k, hk⟩
        have := key k hk
        have : k = (lvl dt b - 1 - lvl dt a + 1).toNat := by omega
        subst this; exact hk

/-! ### `nearest_common_dominator` on any tree with consistent levels -/

theorem up_add (dt : GenericDomTree) : ∀ (m n : Nat) x, up dt (m + n) x = up dt n (up dt m x)
  | 0, n, x => by simp [up]
  | m + 1, n, x => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [up]; exact up_add dt m n _

theorem up_level (dt : GenericDomTree) (h : LevelOK dt) (k : Nat) (x c : Int) (hx : inB dt x)
    (hc : inB dt c) (e : up dt k x = c) : (k : Int) < lvl dt x ∧ lvl dt c = lvl dt x - k := by
  by_cases hk : (k : Int) < lvl dt x
  · have := (up_descend dt h k x hx hk).2; rw [e] at this; exact ⟨hk, this⟩
  · have := up_root dt h k x hx (by omega); rw [e] at this; have := hc.1; omega

theorem levelLoop_up (dt : GenericDomTree) (h : LevelOK dt) (lb : Int) (hlb : 1 ≤ lb) :
    ∀ (fuel : Nat) x lx, inB dt x → lvl dt x = lx → lb ≤ lx → (lx - lb).toNat < fuel →
      ncdLevelLoop dt.idomsBB lb fuel x lx = .ok (up dt (lx - lb).toNat x) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro x lx hx hl hle hf
    unfold ncdLevelLoop
    by_cases hgt : lx > lb
    · obtain ⟨_, h0, h1⟩ := h.2 x hx
      have hne : idm dt x ≠ 0 := fun e => by have := h0 e; omega
      obtain ⟨hi, hli⟩ := h1 hne
      simp only [hgt, ite_true, aget_idm dt h x hx, bind, Except.bind]
      rw [ih _ _ hi (by omega) (by omega) (by omega)]
      rw [show (lx - lb).toNat = (lx - 1 - lb).toNat + 1 by omega]; rfl
    · simp only [hgt, ite_false]
      rw [show (lx - lb).toNat = 0 by omega]; rfl

theorem ncdLoop_up (dt : GenericDomTree) (h : LevelOK dt) : ∀ (fuel : Nat) a b,
    ((a = 0 ∧ b = 0 ∧ 0 < fuel) ∨ (inB dt a ∧ inB dt b ∧ lvl dt a = lvl dt b ∧ lvl dt a < fuel)) →
    ∃ j, ncdLoop dt.idomsBB fuel a b = .ok (up dt j a, up dt j b) ∧ up dt j a = up dt j b ∧
      ∀ i < j, up dt i a ≠ up dt i b := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b hc
    rcases hc with ⟨_, _, h0⟩ | ⟨ha, _, _, h0⟩
    · omega
    · have := (h.2 a ha).1; omega
  | succ fuel ih =>
    intro a b hc
    unfold ncdLoop
    by_cases hab : a = b
    · subst hab
      refine ⟨0, ?_, rfl, fun i hi => by omega⟩
      simp; rfl
    · rcases hc with ⟨ha0, hb0, _⟩ | ⟨ha, hb, hl, hf⟩
      · exact absurd (ha0.trans hb0.symm) hab
      have ha0 : a ≠ 0 := by have := ha.1; omega
      have hcond : (a != b && a != 0) = true := by simp [hab, ha0]
      simp only [hcond, ite_true, aget_idm dt h a ha, aget_idm dt h b hb, bind, Except.bind]
      obtain ⟨_, a0, a1⟩ := h.2 a ha
      obtain ⟨_, b0, b1⟩ := h.2 b hb
      have hnext : (idm dt a = 0 ∧ idm dt b = 0 ∧ 0 < fuel) ∨
          (inB dt (idm dt a) ∧ inB dt (idm dt b) ∧ lvl dt (idm dt a) = lvl dt (idm dt b) ∧
            lvl dt (idm dt a) < fuel) := by
        by_cases hz : idm dt a = 0
        · have l1 := a0 hz
          have hz' : idm dt b = 0 := by
            refine Classical.byContradiction fun hn => ?_; have := (b1 hn).2; have := (h.2 _ (b1 hn).1).1; omega
          left; exact ⟨hz, hz', by omega⟩
        · have hz' : idm dt b ≠ 0 := by
            intro hn; have := b0 hn; have := (a1 hz).2; have := (h.2 _ (a1 hz).1).1; omega
          right
          exact ⟨(a1 hz).1, (b1 hz').1, by have := (a1 hz).2; have := (b1 hz').2; omega,
            by have := (a1 hz).2; omega⟩
      obtain ⟨j, hj, he, hmin⟩ := ih _ _ hnext
      refine ⟨j + 1, ?_, he, ?_⟩
      · rw [hj]; rfl
      · intro i hi
        cases i with
        | zero => exact hab
        | succ i => exact hmin i (by omega)

def anc (dt : GenericDomTree) (c x : Int) : Prop := ∃ k, up dt k x = c

/-- `r` is the nearest common ancestor of `x` and `y` in the tree, or `0` when they have none. -/
def IsNCA (dt : GenericDomTree) (x y r : Int) : Prop :=
  (r = 0 ∨ (anc dt r x ∧ anc dt r y)) ∧ ∀ c, inB dt c → anc dt c x → anc dt c y → anc dt c r

theorem ncd_core (dt : GenericDomTree) (h : LevelOK dt)
    (hbound : ∀ b, inB dt b → lvl dt b ≤ dt.nodes.size) (x y : Int) (hx : inB dt x) (hy : inB dt y)
    (hle : lvl dt y ≤ lvl dt x) :
    ∃ r, (do
      let a ← ncdLevelLoop dt.idomsBB (lvl dt y) ((lvl dt x - lvl dt y).toNat + 1) x (lvl dt x)
      let (a, b) ← ncdLoop dt.idomsBB (2 * (dt.nodes.size + 2)) a y
      unless a == b do throw "julia:AssertionError"
      return a : JM Int) = .ok r ∧ IsNCA dt x y r := by
  have hy1 := (h.2 y hy).1
  have hx1 := (h.2 x hx).1
  rw [levelLoop_up dt h _ hy1 _ x _ hx rfl hle (by omega)]
  obtain ⟨d, hd⟩ : ∃ d, d = (lvl dt x - lvl dt y).toNat := ⟨_, rfl⟩
  rw [← hd]
  have ⟨ha', hla'⟩ := up_descend dt h d x hx (by omega)
  obtain ⟨j, hj, he, hmin⟩ := ncdLoop_up dt h (2 * (dt.nodes.size + 2)) (up dt d x) y
    (Or.inr ⟨ha', hy, by omega, by have := hbound y hy; omega⟩)
  refine ⟨up dt j (up dt d x), ?_, ?_, ?_⟩
  · simp only [bind, Except.bind, hj, he, beq_self_eq_true]; rfl
  · by_cases hr : up dt j (up dt d x) = 0
    · exact Or.inl hr
    · right; refine ⟨⟨d + j, by rw [up_add]⟩, ⟨j, he.symm⟩⟩
  · rintro c hc ⟨k1, hk1⟩ ⟨k2, hk2⟩
    have L1 := up_level dt h k1 x c hx hc hk1
    have L2 := up_level dt h k2 y c hy hc hk2
    have hmeet : up dt k2 (up dt d x) = up dt k2 y := by
      rw [← up_add, show d + k2 = k1 by omega, hk1, hk2]
    have hjk : j ≤ k2 := by
      refine Classical.byContradiction fun hn => ?_; exact hmin k2 (by omega) hmeet
    refine ⟨k2 - j, ?_⟩
    rw [he, ← up_add, show j + (k2 - j) = k2 by omega, hk2]

/-- `nearest_common_dominator(dt, a, b)` (Compiler/src/ssair/domtree.jl:699-719) on any tree
with consistent levels no deeper than its number of nodes, for nodes or the virtual exit `0`:
it returns (the `@assert` holds), it returns 0 when `a` or `b` is 0, and the result is the
nearest common ancestor: either 0 or an ancestor of both, and every common ancestor of `a` and
`b` is an ancestor of it (so 0 means there is none, as for an unreachable block, or roots of
different trees). -/
def NCDSpec : Prop := ∀ dt, LevelOK dt → (∀ b, inB dt b → lvl dt b ≤ dt.nodes.size) →
  ∀ a b, (a = 0 ∨ inB dt a) → (b = 0 ∨ inB dt b) →
    ∃ r, nearestCommonDominator dt a b = .ok r ∧ ((a = 0 ∨ b = 0) → r = 0) ∧ IsNCA dt a b r

theorem ncdSpec_proven : NCDSpec := by
  intro dt h hbound a b ha hb
  have zero_nca : ∀ x y, (x = 0 ∨ y = 0) → IsNCA dt x y 0 := by
    intro x y hxy
    refine ⟨Or.inl rfl, fun c hc ⟨k1, h1⟩ ⟨k2, h2⟩ => ?_⟩
    rcases hxy with rfl | rfl
    · rw [up_zero] at h1; have := hc.1; omega
    · rw [up_zero] at h2; have := hc.1; omega
  by_cases ha0 : a = 0
  · subst ha0; exact ⟨0, by simp [nearestCommonDominator]; rfl, fun _ => rfl, zero_nca _ _ (Or.inl rfl)⟩
  by_cases hb0 : b = 0
  · subst hb0
    exact ⟨0, by simp [nearestCommonDominator, ha0]; rfl, fun _ => rfl, zero_nca _ _ (Or.inr rfl)⟩
  have ha' : inB dt a := ha.resolve_left ha0
  have hb' : inB dt b := hb.resolve_left hb0
  obtain ⟨na, hna, hla⟩ := aget_nodes dt a ha'
  obtain ⟨nb, hnb, hlb⟩ := aget_nodes dt b hb'
  have e1 : (a == 0) = false := by simpa using ha0
  have e2 : (b == 0) = false := by simpa using hb0
  by_cases hlt : lvl dt a < lvl dt b
  · obtain ⟨r, hr, hn⟩ := ncd_core dt h hbound b a hb' ha' (by omega)
    refine ⟨r, ?_, fun h => by omega, ⟨hn.1.imp_right And.symm, fun c hc h1 h2 => hn.2 c hc h2 h1⟩⟩
    simp only [nearestCommonDominator, e1, e2, hna, hnb, bind, Except.bind, hla, hlb, hlt, ite_true]
    exact hr
  · obtain ⟨r, hr, hn⟩ := ncd_core dt h hbound a b ha' hb' (by omega)
    refine ⟨r, ?_, fun h => by omega, hn⟩
    simp only [nearestCommonDominator, e1, e2, hna, hnb, bind, Except.bind, hla, hlb, hlt, ite_false]
    exact hr

/-- `bb_unreachable(dt, bb)` (Compiler/src/ssair/domtree.jl:670) is false for block 1 and
otherwise whether `to_pre[bb]` is 0, with a `BoundsError` outside `to_pre`. -/
def BBUnreachableSpec : Prop := ∀ (dt : GenericDomTree) (bb : Int),
  bbUnreachable dt bb =
    if bb = 1 then .ok false
    else if h : 1 ≤ bb ∧ (bb - 1).toNat < dt.dfsTree.toPre.size then
      .ok (dt.dfsTree.toPre[(bb - 1).toNat]'h.2 == 0)
    else .error "julia:BoundsError"

theorem bbUnreachableSpec_proven : BBUnreachableSpec := by
  intro dt bb
  unfold bbUnreachable
  by_cases h1 : bb = 1
  · subst h1; simp; rfl
  · have : (bb != 1) = true := by simpa using h1
    simp only [this, ite_true, h1, ite_false]
    by_cases h : 1 ≤ bb ∧ (bb - 1).toNat < dt.dfsTree.toPre.size
    · rw [dite_eq_left_of_eq_true (eq_true h), aget_ok _ _ h]; rfl
    · rw [dite_eq_right_of_eq_false (eq_false h), aget_err _ _ h]; rfl

/-- `is_parent(D, x, y)` (Compiler/src/ssair/domtree.jl:544-548), for blocks `x` and `y`: whether
the preorder number of `x` is the recorded DFS-tree parent of the preorder number of `y`; a
`BoundsError` when `y` has no preorder number (`to_pre[y] == 0`, an unreachable block). -/
def IsParentSpec : Prop := ∀ (D : DFSTree) (x y : Int),
  1 ≤ x → (x - 1).toNat < D.toPre.size → 1 ≤ y → (y - 1).toNat < D.toPre.size →
  let xp := D.toPre.getD (x - 1).toNat 0
  let yp := D.toPre.getD (y - 1).toNat 0
  isParent D x y =
    if 1 ≤ yp ∧ (yp - 1).toNat < D.toParentPre.size then
      .ok (xp == D.toParentPre.getD (yp - 1).toNat 0)
    else .error "julia:BoundsError"

theorem isParentSpec_proven : IsParentSpec := by
  intro D x y hx1 hx2 hy1 hy2
  simp only
  unfold isParent
  rw [aget_ok _ _ ⟨hx1, hx2⟩, aget_ok _ _ ⟨hy1, hy2⟩]
  simp only [bind, Except.bind, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx2,
    Array.getElem?_eq_getElem hy2, Option.getD_some]
  by_cases h : 1 ≤ D.toPre[(y - 1).toNat] ∧ (D.toPre[(y - 1).toNat] - 1).toNat < D.toParentPre.size
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), aget_ok _ _ h]
    simp only [Array.getElem?_eq_getElem h.2, Option.getD_some]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), aget_err _ _ h]

theorem bind_ok {α β : Type} {x : JM α} {f : α → JM β} {r : β} (h : (x >>= f) = .ok r) :
    ∃ a, f a = .ok r := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, h⟩

theorem bind_ok' {α β : Type} {x : JM α} {f : α → JM β} {r : β} (h : (x >>= f) = .ok r) :
    ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem dfsLoop_stack (blocks : Blocks) (isPost : Bool) : ∀ fuel D stk p q r,
    dfsLoop blocks isPost fuel D stk p q = .ok r → r.2.2.2 = #[] := by
  intro fuel
  induction fuel with
  | zero => intro D stk p q r h; simp [dfsLoop, outOfBudget] at h
  | succ fuel ih =>
    intro D stk p q r h
    unfold dfsLoop at h
    split at h
    · rename_i hb
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact Array.back?_eq_none_iff.mp hb
    · repeat (first | exact ih _ _ _ _ _ h | (obtain ⟨_, h⟩ := bind_ok h) | (dsimp only at h) | split at h)

/-- `DFS!` (Compiler/src/ssair/domtree.jl:123-198) leaves `D._worklist` empty whenever it
returns, so with `DFSTree(n)` starting it empty (`compiler-domtree-dfstree-ctor`) the stack
"always starts empty" (line 126) on every later call. -/
def DFSWorklistSpec : Prop := ∀ (D : DFSTree) (blocks : Blocks) (isPost : Bool) (E : DFSTree),
  DFS! D blocks isPost = .ok E → E.worklist = #[]

theorem dfsWorklistSpec_proven : DFSWorklistSpec := by
  intro D blocks isPost E h
  unfold DFS! at h
  dsimp only at h
  obtain ⟨⟨D', p, q, stk⟩, hl, h⟩ := bind_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact dfsLoop_stack _ _ _ _ _ _ _ _ hl

end JuliaLean.Proofs.Compiler.src.ssair.domtree
