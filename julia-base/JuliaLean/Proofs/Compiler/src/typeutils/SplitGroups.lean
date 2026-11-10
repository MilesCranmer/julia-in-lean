import JuliaLean.Proofs.Compiler.src.typeutils.Groups

/-!
`_switchtupleunion` and `switchtupleunion(𝕃, argtypes; fargs)` (`Compiler/src/typeutils.jl:326-392`)
with alias groups and with the elements it splits after widening them.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## Pure loops -/

theorem forIn_list_run_yield {β γ : Type} (l : List γ) (body : γ → β → CM (ForInStep β))
    (f : γ → β → β) (hb : ∀ a b s, (body a b).run s = .ok (.yield (f a b), s)) :
    ∀ (init : β) (s : Nat), (forIn l init body).run s = .ok (l.foldl (fun b a => f a b) init, s) := by
  induction l with
  | nil => intro init s; rfl
  | cons a l ih =>
    intro init s
    rw [List.forIn_cons, run_bind_ok (hb a init s)]
    exact ih (f a init) s

theorem forIn_list_pure_run {β γ : Type} (l : List γ) (f : γ → β → β) (init : β) (s : Nat) :
    (forIn l init (fun a b => pure (ForInStep.yield (f a b))) : CM β).run s =
      .ok (l.foldl (fun b a => f a b) init, s) :=
  forIn_list_run_yield l _ f (fun _ _ _ => rfl) init s

theorem forIn_array_pure_run {β γ : Type} (l : Array γ) (f : γ → β → β) (init : β) (s : Nat) :
    (forIn l init (fun a b => pure (ForInStep.yield (f a b))) : CM β).run s =
      .ok (l.toList.foldl (fun b a => f a b) init, s) := by
  rw [← Array.forIn_toList]; exact forIn_list_pure_run _ f init s

/-! ## Setting a leader and its followers -/

/-- The followers of the leader at position `i` (1-based), in increasing order: the positions `j`
with `groups[j] == i` (`Compiler/src/typeutils.jl:352-357`). The leader itself is one of them. -/
def followersOf (g : Option (Array Nat)) (size i : Nat) : Array Nat :=
  match g with
  | some g => (List.range' 1 size).foldl (fun acc j => if g[j - 1]! == i then acc.push j else acc) #[]
  | none => #[]

/-- `t` with the leader at position `i` (1-based) and its followers `fl` set to `y`
(`Compiler/src/typeutils.jl:363-366`). -/
def setGroupFl (fl : Array Nat) (t : Array LElt) (i : Nat) (y : Val) : Array LElt :=
  (i :: fl.toList).foldl (fun t j => t.set! (j - 1) (.ty y)) t

theorem foldl_set_size (v : LElt) : ∀ (l : List Nat) (t0 : Array LElt),
    (l.foldl (fun t j => t.set! (j - 1) v) t0).size = t0.size := by
  intro l
  induction l with
  | nil => intro t0; rfl
  | cons j l ih => intro t0; simp only [List.foldl_cons]; rw [ih]; simp [Array.set!_eq_setIfInBounds]

theorem foldl_set_getElem? (v : LElt) : ∀ (l : List Nat) (t0 : Array LElt) (k : Nat),
    (l.foldl (fun t j => t.set! (j - 1) v) t0)[k]? =
      if (∃ j ∈ l, j - 1 = k) ∧ k < t0.size then some v else t0[k]? := by
  intro l
  induction l with
  | nil => intro t0 k; simp
  | cons j l ih =>
    intro t0 k
    simp only [List.foldl_cons]
    rw [ih]
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.getElem?_setIfInBounds,
      List.mem_cons]
    by_cases h1 : j - 1 = k
    · subst h1
      by_cases h2 : j - 1 < t0.size
      · simp [h2]
      · simp [h2, Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
    · by_cases h3 : ∃ j' ∈ l, j' - 1 = k
      · simp [h1, h3]
      · simp only [h1, h3, false_and, if_false]
        have : ¬ ((∃ a, (a = j ∨ a ∈ l) ∧ a - 1 = k) ∧ k < t0.size) := by
          rintro ⟨⟨a, ha | ha, hak⟩, _⟩
          · subst ha; exact h1 hak
          · exact h3 ⟨a, ha, hak⟩
        simp only [exists_eq_or_imp] at this
        rw [if_neg (by simpa [exists_eq_or_imp] using this)]

theorem setGroupFl_size (fl : Array Nat) (t : Array LElt) (i : Nat) (y : Val) :
    (setGroupFl fl t i y).size = t.size := foldl_set_size _ _ _

theorem setGroupFl_overwrite (fl : Array Nat) (t : Array LElt) (i : Nat) (y₁ y₂ : Val) :
    setGroupFl fl (setGroupFl fl t i y₁) i y₂ = setGroupFl fl t i y₂ := by
  apply Array.ext_getElem?
  intro k
  simp only [setGroupFl]
  rw [foldl_set_getElem?, foldl_set_getElem?, foldl_set_getElem?, foldl_set_size]
  by_cases h : (∃ j ∈ i :: fl.toList, j - 1 = k) ∧ k < t.size
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h]

/-! ## The relation `_switchtupleunion` computes -/

/-- The member types `_switchtupleunion` splits the element `a` into (`Compiler/src/typeutils.jl:360-389`):
a `Union`'s members; on a lattice with extended union splitting, the members of `widenconst(a)`
when that is a `Union` and `a` is neither a `Const` nor a `Vararg`; and no split (`none`)
otherwise. -/
def PartsRel (n : Nat) (E : CEnv) (L : Lattice) (a : LElt) (o : Option (List Val)) : Prop :=
  (∃ x y, a = .ty (.union x y) ∧ o = some (uniontypes (.union x y))) ∨
  ((∀ x y, a ≠ .ty (.union x y)) ∧ (hasExtendedUnionsplit L && !a.isConst && !a.isVarargElt) = true ∧
    ∃ w s₁ s₂, (widenconst n E a).run s₁ = .ok (w, s₂) ∧
      o = (if w.isUnion then some (uniontypes w) else none)) ∨
  ((∀ x y, a ≠ .ty (.union x y)) ∧ (hasExtendedUnionsplit L && !a.isConst && !a.isVarargElt) = false ∧
    o = none)

/-- The argument lists `_switchtupleunion(𝕃, t, i, tunion, origt, groups)` emits, in order
(`Compiler/src/typeutils.jl:333-392`): the positions are visited from `i` down to 1; a follower is
skipped (its type is set by its leader); a leader that splits into `ps` gives, for each `y` in
`ps` in turn, the lists of `t` with the leader and all its followers set to `y`. -/
def CartG (n : Nat) (E : CEnv) (L : Lattice) (g : Option (Array Nat)) :
    Array LElt → Nat → List (Array LElt) → Prop
  | t, 0, cs => cs = [t]
  | t, i + 1, cs =>
    (isLeader g (i + 1) = false ∧ CartG n E L g t i cs) ∨
    (isLeader g (i + 1) = true ∧ ∃ a, t[i]? = some a ∧
      ((PartsRel n E L a none ∧ CartG n E L g t i cs) ∨
       (∃ ps, PartsRel n E L a (some ps) ∧ ∃ Ls : List (List (Array LElt)),
          ListRel (fun y Ly => CartG n E L g (setGroupFl (followersOf g t.size (i + 1)) t (i + 1) y) i Ly)
            ps Ls ∧ cs = Ls.flatten)))

/-- What `_switchtupleunion` returns: `tunion` followed by one emitted value per list of `CartG`. -/
def CartRes {α : Type} (n : Nat) (E : CEnv) (L : Lattice) (R : Array LElt → α → Prop)
    (g : Option (Array Nat)) (t : Array LElt) (i : Nat) (tunion res : Array α) : Prop :=
  ∃ cs rs, CartG n E L g t i cs ∧ res.toList = tunion.toList ++ rs ∧ ListRel R cs rs

theorem listRel_flatten {α β : Type} {R : α → β → Prop} {Ls : List (List α)} {rs : List β}
    {L' : List α} {rs' : List β} (h1 : ListRel R L' rs') (h2 : ListRel R Ls.flatten rs) :
    ListRel R (L' ++ Ls.flatten) (rs' ++ rs) := h1.append h2

/-- The loop over the member types of a splitting leader, followed by the restore loop. -/
theorem split_cont (n : Nat) (E : CEnv) (L : Lattice) {α : Type} (emit : Array LElt → CM α)
    (R : Array LElt → α → Prop) (groups : Option (Array Nat)) (i : Nat) (t : Array LElt)
    (fl : Array Nat) (origti : LElt)
    (hrec : ∀ t' tu, t'.size = t.size →
      Returns (switchtupleunion_ n E L emit t' i tu groups) (CartRes n E L R groups t' i tu)) :
    ∀ (ps : List Val) (tunion : Array α) {s res s'},
    (do
      let st ← forIn ps (t, tunion) fun ty (st : Array LElt × Array α) => do
        let t' ← forIn fl (st.1.set! (i + 1 - 1) (LElt.ty ty)) fun j (t'' : Array LElt) =>
          pure (ForInStep.yield (t''.set! (j - 1) (LElt.ty ty)))
        let tu ← switchtupleunion_ n E L emit t' i st.2 groups
        pure (ForInStep.yield (t', tu))
      let _ ← forIn (fl.toList.zip (List.range fl.size)) (st.1.set! (i + 1 - 1) origti)
        fun x (t2 : Array LElt) =>
          pure (ForInStep.yield (t2.set! (x.1 - 1) (Array.map (fun j => t[j - 1]!) fl)[x.2]!))
      pure st.2 : CM (Array α)).run s = .ok (res, s') →
    ∃ Ls rs, ListRel (fun y Ly => CartG n E L groups (setGroupFl fl t (i + 1) y) i Ly) ps Ls ∧
      res.toList = tunion.toList ++ rs ∧ ListRel R Ls.flatten rs := by
  intro ps tunion s res s' h
  obtain ⟨st, s₁, hst, h⟩ := run_bind_inv h
  obtain ⟨_, s₂, _, h⟩ := run_bind_inv h
  cases h
  -- The loop over the member types.
  have loop : ∀ (ps : List Val) (t₀ : Array LElt) (tu : Array α), t₀.size = t.size →
      (∀ y, setGroupFl fl t₀ (i + 1) y = setGroupFl fl t (i + 1) y) →
      Returns (forIn ps (t₀, tu) fun ty (st : Array LElt × Array α) => do
        let t' ← forIn fl (st.1.set! (i + 1 - 1) (LElt.ty ty)) fun j (t'' : Array LElt) =>
          pure (ForInStep.yield (t''.set! (j - 1) (LElt.ty ty)))
        let tu ← switchtupleunion_ n E L emit t' i st.2 groups
        pure (ForInStep.yield (t', tu)))
      (fun st => ∃ Ls rs, ListRel (fun y Ly => CartG n E L groups (setGroupFl fl t (i + 1) y) i Ly) ps Ls ∧
        st.2.toList = tu.toList ++ rs ∧ ListRel R Ls.flatten rs) := by
    intro ps
    induction ps with
    | nil => intro t₀ tu _ _ s st s' h; cases h; exact ⟨[], [], .nil, by simp, .nil⟩
    | cons y ps ih =>
      intro t₀ tu hsz hinv s st s' h
      obtain ⟨st₁, s₁, h1, h2⟩ := forIn_cons_run h
      obtain ⟨t', s₃, ht', h1⟩ := run_bind_inv h1
      rw [forIn_array_pure_run] at ht'
      simp only [Except.ok.injEq, Prod.mk.injEq] at ht'
      obtain ⟨rfl, rfl⟩ := ht'
      obtain ⟨tu', s₄, htu, h1⟩ := run_bind_inv h1
      cases h1
      have hset : fl.toList.foldl (fun b a => b.set! (a - 1) (LElt.ty y)) (t₀.set! (i + 1 - 1) (LElt.ty y)) =
          setGroupFl fl t (i + 1) y := by
        rw [← hinv y]; rfl
      rw [hset] at htu h2
      obtain ⟨cs, rs1, hcs, hr1, hrel1⟩ := hrec _ tu (setGroupFl_size _ _ _ _) _ tu' _ htu
      obtain ⟨Ls, rs2, hLs, hr2, hrel2⟩ := ih _ tu' (setGroupFl_size _ _ _ _)
        (fun y' => setGroupFl_overwrite fl t (i + 1) y y') _ st s' h2
      refine ⟨cs :: Ls, rs1 ++ rs2, .cons hcs hLs, by rw [hr2, hr1, List.append_assoc], ?_⟩
      rw [List.flatten_cons]
      exact hrel1.append hrel2
  exact loop ps t tunion rfl (fun _ => rfl) s st s₁ hst

-- The step of `_switchtupleunion` at a leader, once its followers are collected: split by the
-- element's members (directly or after `widenconst`), or recurse without splitting. Shared by the
-- cases with and without alias groups.
set_option hygiene false in
macro "leader_tac" : tactic => `(tactic| (
  generalize hta : t[i] = a at h
  have hget : t[i]? = some a := by rw [Array.getElem?_eq_getElem hit, hta]
  by_cases hu : ∃ x y, a = .ty (.union x y)
  · obtain ⟨x, y, rfl⟩ := hu
    simp only [pure_bind] at h
    obtain ⟨Ls, rs, hLs, hr, hrel⟩ := split_cont n E L emit R _ i t _ _ hrec _ tunion h
    refine ⟨Ls.flatten, rs, ?_, hr, hrel⟩
    rw [CartG]
    exact .inr ⟨hl, _, hget, .inr ⟨_, .inl ⟨x, y, rfl, rfl⟩, Ls, hLs, rfl⟩⟩
  · have hnu : ∀ x y, a ≠ .ty (.union x y) := fun x y he => hu ⟨x, y, he⟩
    split at h
    · exact absurd rfl (hnu _ _)
    · split at h
      · rename_i hc
        obtain ⟨w, s₂, hw, h⟩ := run_bind_inv h
        split at h
        · rename_i hwu
          simp only [pure_bind] at h
          obtain ⟨Ls, rs, hLs, hr, hrel⟩ := split_cont n E L emit R _ i t _ _ hrec _ tunion h
          refine ⟨Ls.flatten, rs, ?_, hr, hrel⟩
          rw [CartG]
          exact .inr ⟨hl, _, hget, .inr ⟨_, .inr (.inl ⟨hnu, hc, w, _, _, hw, by simp [hwu]⟩), Ls,
            hLs, rfl⟩⟩
        · rename_i hwu
          simp only [pure_bind] at h
          obtain ⟨cs, rs, hcs, hr, hrel⟩ := hrec t tunion rfl _ res _ h
          refine ⟨cs, rs, ?_, hr, hrel⟩
          rw [CartG]
          exact .inr ⟨hl, _, hget, .inl ⟨.inr (.inl ⟨hnu, hc, w, _, _, hw, by simp [hwu]⟩), hcs⟩⟩
      · rename_i hc
        simp only [pure_bind] at h
        obtain ⟨cs, rs, hcs, hr, hrel⟩ := hrec t tunion rfl _ res _ h
        refine ⟨cs, rs, ?_, hr, hrel⟩
        rw [CartG]
        exact .inr ⟨hl, _, hget, .inl ⟨.inr (.inr ⟨hnu, by simpa using hc, rfl⟩), hcs⟩⟩))

theorem switchtupleunion_groups (n : Nat) (E : CEnv) (L : Lattice) {α : Type}
    (emit : Array LElt → CM α) (R : Array LElt → α → Prop)
    (hemit : ∀ c s r s', (emit c).run s = .ok (r, s') → R c r) (groups : Option (Array Nat)) :
    ∀ i (t : Array LElt) (tunion : Array α), i ≤ t.size →
      Returns (switchtupleunion_ n E L emit t i tunion groups) (CartRes n E L R groups t i tunion) := by
  intro i
  induction i with
  | zero =>
    intro t tunion _ s res s' h
    simp only [switchtupleunion_] at h
    obtain ⟨r, s₁, hr, h⟩ := run_bind_inv h
    have hR := hemit t s r s₁ hr
    cases h
    exact ⟨[t], [r], rfl, by simp, .cons hR .nil⟩
  | succ i ih =>
    intro t tunion hi s res s' h
    have hit : i < t.size := by omega
    have hrec : ∀ t' tu, t'.size = t.size →
        Returns (switchtupleunion_ n E L emit t' i tu groups) (CartRes n E L R groups t' i tu) :=
      fun t' tu hs => ih t' tu (by omega)
    have hget0 : t[i + 1 - 1]? = some t[i] := by simp [Array.getElem?_eq_getElem hit]
    cases groups with
    | none =>
      have hl : isLeader none (i + 1) = true := rfl
      simp only [switchtupleunion_] at h
      rw [hget0] at h
      simp only at h
      leader_tac
    | some g =>
      simp only [switchtupleunion_] at h
      split at h
      · rename_i hf
        have hl : isLeader (some g) (i + 1) = false := by
          simp only [isLeader, bne] at hf ⊢
          cases hx : (g[i + 1 - 1]! == i + 1) <;> simp_all
        obtain ⟨cs, rs, hcs, hr, hrel⟩ := hrec t tunion rfl s res s' h
        refine ⟨cs, rs, ?_, hr, hrel⟩
        rw [CartG]
        exact .inl ⟨hl, hcs⟩
      · rename_i hf
        have hl : isLeader (some g) (i + 1) = true := by
          simp only [isLeader, bne] at hf ⊢
          cases hx : (g[i + 1 - 1]! == i + 1) <;> simp_all
        rw [hget0] at h
        simp only at h
        obtain ⟨fl, s₁, hfl, h⟩ := run_bind_inv h
        rw [forIn_list_run_yield (List.range' 1 t.size) _
          (fun j acc => if (g[j - 1]! == i + 1) = true then acc.push j else acc) (by
            intro j acc s
            by_cases hc : (g[j - 1]! == i + 1) = true
            · rw [if_pos hc, if_pos hc]; rfl
            · rw [if_neg hc, if_neg hc]; rfl)] at hfl
        simp only [Except.ok.injEq, Prod.mk.injEq] at hfl
        obtain ⟨rfl, rfl⟩ := hfl
        leader_tac

end JuliaLean.Proofs.Compiler.src.typeutils
