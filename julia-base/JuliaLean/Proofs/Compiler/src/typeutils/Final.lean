import JuliaLean.Proofs.Compiler.src.typeutils.SplitGroups
import JuliaLean.Proofs.Compiler.src.typeutils.Alias

/-!
The registry statements that cover `argtypes_to_type`, `unionsplitcost` and both `switchtupleunion`
methods on every input: any lattice element, with or without alias groups.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## `argtypes_to_type` -/

theorem mapM_rel {α β : Type} (f : α → CM β) :
    ∀ (l : List α) s r s', (l.mapM f).run s = .ok (r, s') →
      ListRel (fun a b => ∃ s₁ s₂, (f a).run s₁ = .ok (b, s₂)) l r := by
  intro l
  induction l with
  | nil => intro s r s' h; cases h; exact .nil
  | cons a l ih =>
    intro s r s' h
    rw [List.mapM_cons] at h
    obtain ⟨b, s₁, hb, h⟩ := run_bind_inv h
    obtain ⟨bs, s₂, hbs, h⟩ := run_bind_inv h
    cases h
    exact .cons ⟨_, _, hb⟩ (ih s₁ bs _ hbs)

/-- `r` is `l` with some elements dropped: each kept element satisfies `P x true`, each dropped one
`P x false`. -/
inductive FilterRel {α : Type} (P : α → Bool → Prop) : List α → List α → Prop
  | nil : FilterRel P [] []
  | keep {a l r} : P a true → FilterRel P l r → FilterRel P (a :: l) (a :: r)
  | drop {a l r} : P a false → FilterRel P l r → FilterRel P (a :: l) r

theorem FilterRel.mono {α : Type} {P P' : α → Bool → Prop} {l r : List α} (h : FilterRel P l r)
    (hm : ∀ x b, P x b → P' x b) : FilterRel P' l r := by
  induction h with
  | nil => exact .nil
  | keep hp _ ih => exact .keep (hm _ _ hp) ih
  | drop hp _ ih => exact .drop (hm _ _ hp) ih

theorem filterAuxM_rel {α : Type} (p : α → CM Bool) :
    ∀ (l acc : List α) s r s', (List.filterAuxM p l acc).run s = .ok (r, s') →
      ∃ k, FilterRel (fun x b => ∃ s₁ s₂, (p x).run s₁ = .ok (b, s₂)) l k ∧ r = k.reverse ++ acc := by
  intro l
  induction l with
  | nil => intro acc s r s' h; cases h; exact ⟨[], .nil, rfl⟩
  | cons x l ih =>
    intro acc s r s' h
    simp only [List.filterAuxM] at h
    obtain ⟨b, s₁, hb, h⟩ := run_bind_inv h
    cases b
    · obtain ⟨k, hk, hr⟩ := ih acc s₁ r s' h
      exact ⟨k, .drop ⟨_, _, hb⟩ hk, hr⟩
    · obtain ⟨k, hk, hr⟩ := ih (x :: acc) s₁ r s' h
      exact ⟨x :: k, .keep ⟨_, _, hb⟩ hk, by rw [hr]; simp⟩

theorem filterM_rel {α : Type} (p : α → CM Bool) (l : List α) {s r s'}
    (h : (l.filterM p).run s = .ok (r, s')) :
    FilterRel (fun x b => ∃ s₁ s₂, (p x).run s₁ = .ok (b, s₂)) l r := by
  simp only [List.filterM] at h
  obtain ⟨as, s₁, has, h⟩ := run_bind_inv h
  obtain ⟨k, hk, rfl⟩ := filterAuxM_rel p l [] s as s₁ has
  cases h
  simpa using hk

/-- `argtypes_to_type(argtypes)` (`Compiler/src/typeutils.jl:40-45`) on every list of lattice
elements. Each argument is widened (`widenconst_split`) unless it is a `Vararg`; a `Vararg` whose
element type is not a valid type tag is dropped (the `filter!`); the result is
`Tuple{remaining...}` when every remaining non-`Vararg` is a valid type tag, and `Union{}` when one
is not. The widening of the lattice elements that carry more than a type is stated too: a `Const`
of a non-type value gives its type, a `PartialStruct` its `typ`, and a native type itself. -/
def ArgtypesToTypeFull : Prop :=
  ArgtypesToTypeSpec ∧
  (∀ n E (args : List LElt), Returns (argtypesToType n E args) (fun r =>
    ∃ ws, ListRel (fun a w => (a.isVarargElt = true ∧ a = .ty w) ∨
        (a.isVarargElt = false ∧ ∃ s₁ s₂, (widenconstSplit n E a).run s₁ = .ok (w, s₂))) args ws ∧
    ∃ fs, FilterRel (fun x b => (isvarargtype x = false ∧ b = true) ∨
        (isvarargtype x = true ∧ ∃ s₁ s₂, (validAsLattice n E (unwrapva x) true).run s₁ = .ok (b, s₂)))
        ws fs ∧
    (((∀ x ∈ fs, isvarargtype x = true ∨ ∃ s₁ s₂, (validAsLattice n E x true).run s₁ = .ok (true, s₂)) ∧
        ∃ s₁ s₂, (jlTuple n E fs).run s₁ = .ok (r, s₂)) ∨
     (r = .bottom ∧ ∃ x ∈ fs, isvarargtype x = false ∧
        ∃ s₁ s₂, (validAsLattice n E x true).run s₁ = .ok (false, s₂))))) ∧
  (∀ n E (v : Val) s, v.isType = false →
    (widenconstSplit (n + 1) E (.const v)).run s = .ok (typeOf v, s)) ∧
  (∀ n E typ u fs ui fi s,
    (widenconstSplit (n + 1) E (.partialStruct typ u fs ui fi)).run s = .ok (typ, s)) ∧
  (∀ n E (t : Val) s, t.isType = true → (widenconstSplit n E (.ty t)).run s = .ok (t, s))

theorem argtypesToTypeFull_proven : ArgtypesToTypeFull := by
  refine ⟨argtypesToTypeSpec_proven, fun n E args s r s' h => ?_, fun n E v s hv => ?_,
    fun n E typ u fs ui fi s => rfl, fun n E t s ht => widenconstSplit_ty_run n E t ht s⟩
  · simp only [argtypesToType] at h
    obtain ⟨ws, s₁, hws, h1⟩ := run_bind_inv h
    refine ⟨ws, (mapM_rel _ args s ws s₁ hws).mono_mem (fun a _ w hw => ?_), ?_⟩
    · obtain ⟨s₂, s₃, hw⟩ := hw
      cases a with
      | ty t =>
        simp only at hw
        cases hv : isvarargtype t
        · simp only [hv, Bool.false_eq_true, if_false] at hw
          exact .inr ⟨by simpa [LElt.isVarargElt, isvarargtype] using hv, _, _, hw⟩
        · simp only [hv, if_true] at hw
          have hw' : (Except.ok (t, s₂) : Except String (Val × Nat)) = .ok (w, s₃) := hw
          simp only [Except.ok.injEq, Prod.mk.injEq] at hw'
          obtain ⟨rfl, -⟩ := hw'
          exact .inl ⟨by simpa [LElt.isVarargElt, isvarargtype] using hv, rfl⟩
      | _ => exact .inr ⟨rfl, _, _, hw⟩
    · obtain ⟨fs, s₂, hfs, h2⟩ := run_bind_inv h1
      refine ⟨fs, (filterM_rel _ ws hfs).mono (fun x b hb => ?_), ?_⟩
      · obtain ⟨s₃, s₄, hb⟩ := hb
        cases hvx : isvarargtype x
        · simp only [hvx, Bool.not_false, if_true] at hb
          have hb' : (Except.ok (true, s₃) : Except String (Bool × Nat)) = .ok (b, s₄) := hb
          simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
          exact .inl ⟨rfl, hb'.1.symm⟩
        · simp only [hvx, Bool.not_true, Bool.false_eq_true, if_false] at hb
          exact .inr ⟨rfl, _, _, hb⟩
      · obtain ⟨st, s₃, hst, h3⟩ := run_bind_inv h2
        have key := forIn_test fs (fun x => do
            let b ← validAsLattice n E x true
            pure (isvarargtype x || b)) Val.bottom _ ?hF s₂ st s₃ hst
        case hF =>
          intro x _ s₀ st₀ s₀' hx
          obtain ⟨b, s₄, hb, hx⟩ := run_bind_inv hx
          refine ⟨isvarargtype x || b, ?_, ?_⟩
          · cases hc : (isvarargtype x || b)
            · simp only [hc, Bool.not_false, if_true] at hx
              cases hx; rw [run_bind_ok hb, hc]; rfl
            · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false] at hx
              cases hx; rw [run_bind_ok hb, hc]; rfl
          · cases hc : (isvarargtype x || b)
            · simp only [hc, Bool.not_false, if_true] at hx
              cases hx; rfl
            · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false] at hx
              cases hx; rfl
        rcases key with ⟨h5, h4⟩ | ⟨h5, y, hy, h4⟩
        · simp only [h5] at h3
          refine .inl ⟨fun x hx => ?_, _, _, h3⟩
          obtain ⟨s₅, s₆, ht⟩ := h4 x hx
          obtain ⟨b, s₇, hb, ht⟩ := run_bind_inv ht
          have ht' : (Except.ok (isvarargtype x || b, s₇) : Except String (Bool × Nat)) = .ok (true, s₆) := ht
          simp only [Except.ok.injEq, Prod.mk.injEq, Bool.or_eq_true] at ht'
          rcases ht'.1 with hv | hb'
          · exact .inl hv
          · subst hb'; exact .inr ⟨_, _, hb⟩
        · simp only [h5] at h3
          cases h3
          obtain ⟨s₅, s₆, ht⟩ := h4
          obtain ⟨b, s₇, hb, ht⟩ := run_bind_inv ht
          have ht' : (Except.ok (isvarargtype y || b, s₇) : Except String (Bool × Nat)) = .ok (false, s₆) := ht
          simp only [Except.ok.injEq, Prod.mk.injEq, Bool.or_eq_false_iff] at ht'
          obtain ⟨⟨hv, rfl⟩, -⟩ := ht'
          exact .inr ⟨rfl, y, hy, hv, _, _, hb⟩
  · simp [widenconstSplit, LElt.isConst, widenconst, hv]; rfl

/-! ## `unionsplitcost` -/

theorem unionLenOf_some_pos (e : LElt) (x : Nat) (h : unionLenOf e = some x) : 1 ≤ x := by
  cases e with
  | ty t =>
    cases t with
    | union a b => simp only [unionLenOf] at h; cases h; exact unionlen_pos _
    | _ => simp [unionLenOf] at h
  | _ => simp [unionLenOf] at h

/-- `unionsplitcost(𝕃, argtypes; fargs)` (`Compiler/src/typeutils.jl:285-316`) on every input. With
the alias groups `g` that `compute_alias_groups` returns, the loop reads a value at each position
(`CostOptAt`): nothing at a follower, and at a leader the `unionlen` of the argument, widened with
`widenconst_split` first on a lattice with extended union splitting unless it is a `Vararg`. The
result is twice the product of the lengths read divided by the largest one (or by 2), capped at
`typemax(Int)`; the loop stops before the last position only on that overflow. -/
def UnionsplitcostFull : Prop :=
  UnionsplitcostSpec ∧
  ∀ n E L argtypes isVector fargs, Returns (unionsplitcost n E L argtypes isVector fargs) (fun c =>
    ∃ g, (∃ s₁ s₂, (computeAliasGroups argtypes.length fargs
        (if isVector then some argtypes else none)).run s₁ = .ok (g, s₂)) ∧
      ∃ lens : List (Option Nat), lens.length ≤ argtypes.length ∧
        (∀ j (hj : j < lens.length), CostOptAt n E L g argtypes j lens[j]) ∧
        c = min typemaxInt ((2 * costP (lens.map lenOrOne) / costM (lens.map lenOrOne) : Nat) : Int) ∧
        (lens.length < argtypes.length → c = typemaxInt))

theorem unionsplitcostFull_proven : UnionsplitcostFull := by
  refine ⟨unionsplitcostSpec_proven, fun n E L argtypes isVector fargs s c s' h => ?_⟩
  obtain ⟨g, hg, lens, hl, hP, hc, hlt⟩ := unionsplitcost_groups n E L argtypes isVector fargs s c s' h
  refine ⟨g, hg, lens, hl, hP, ?_, hlt⟩
  have hpos : ∀ x, some x ∈ lens → 1 ≤ x := by
    intro x hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    obtain ⟨a, _, hf, hw, hn⟩ := hP j hj
    cases hlead : isLeader g (j + 1)
    · rw [hf hlead] at hjx; cases hjx
    · cases hc' : (hasExtendedUnionsplit L && !a.isVarargElt)
      · rw [hn hlead hc'] at hjx; exact unionLenOf_some_pos _ _ hjx
      · obtain ⟨w, _, _, _, hw'⟩ := hw hlead hc'
        rw [hw'] at hjx; exact unionLenOf_some_pos _ _ hjx
  rw [hc, costLoop_one_two lens hpos, costCapped, ← costF_eq_div]
  split <;> omega

/-! ## `switchtupleunion(𝕃, argtypes; fargs)` and `_switchtupleunion` -/

/-- `_switchtupleunion(𝕃, t, i, tunion, origt, groups)` (`Compiler/src/typeutils.jl:333-392`) on
every input, for any alias groups and any lattice: it appends to `tunion` one emitted value per
argument list of `CartG`, in that order. `CartG` visits the positions from `i` down to 1, skips a
follower, and at a leader either recurses (no split) or, for each member type of the leader's
`Union` (or of its `widenconst` on a lattice with extended union splitting, unless it is a `Const`
or `Vararg`), sets the leader and all its followers to that member. -/
def SwitchtupleunionGroupsSpec : Prop :=
  ∀ n E L {α : Type} (emit : Array LElt → CM α) (R : Array LElt → α → Prop),
    (∀ c s r s', (emit c).run s = .ok (r, s') → R c r) →
    ∀ groups i (t : Array LElt) (tunion : Array α), i ≤ t.size →
      Returns (switchtupleunion_ n E L emit t i tunion groups) (CartRes n E L R groups t i tunion)

theorem switchtupleunionGroupsSpec_proven : SwitchtupleunionGroupsSpec :=
  fun n E L _ emit R hemit groups => switchtupleunion_groups n E L emit R hemit groups

/-- `switchtupleunion(𝕃, argtypes; fargs)` (`Compiler/src/typeutils.jl:326-331`) on every input:
with the alias groups `compute_alias_groups` returns, the result is exactly the argument lists of
`CartG` over all positions. -/
def SwitchtupleunionLFull : Prop :=
  SwitchtupleunionLSpec ∧
  ∀ n E L argtypes fargs, Returns (switchtupleunionL n E L argtypes fargs) (fun rs =>
    ∃ g, (∃ s₁ s₂, (computeAliasGroups argtypes.length fargs (some argtypes)).run s₁ = .ok (g, s₂)) ∧
      ∃ cs, CartG n E L g argtypes.toArray argtypes.length cs ∧ rs = cs.map Array.toList)

theorem switchtupleunionLFull_proven : SwitchtupleunionLFull := by
  refine ⟨switchtupleunionLSpec_proven, fun n E L argtypes fargs s rs s' h => ?_⟩
  simp only [switchtupleunionL] at h
  obtain ⟨g, s₁, hg, h⟩ := run_bind_inv h
  obtain ⟨res, s₂, hres, h⟩ := run_bind_inv h
  obtain ⟨cs, rs', hcs, hr, hrel⟩ := switchtupleunion_groups n E L (fun t => pure t.toList)
    (fun c r => r = c.toList) (fun c s r s' h => by cases h; rfl) g argtypes.length argtypes.toArray
    #[] (by simp) s₁ res s₂ hres
  cases h
  refine ⟨g, ⟨_, _, hg⟩, cs, hcs, ?_⟩
  simp only [Array.toList_empty, List.nil_append] at hr
  rw [hr]
  exact listRel_toList hrel

end JuliaLean.Proofs.Compiler.src.typeutils
