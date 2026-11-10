import JuliaLean.Proofs.Compiler.src.typelimits.FastPath

/-!
Properties of the small helpers of `Compiler/src/typelimits.jl`: `tname_intersect`,
`union_causes`, `union_count_abstract`, `issimpleenoughtype` and `n_initialized`.
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

-- `okd` takes apart a hypothesis `h : m.run s = .ok (r, s')` along the binds, `if`s and
-- `match`es of `m`.
set_option hygiene false in
macro "okd" : tactic =>
  `(tactic| repeat (first
      | (obtain ⟨_, _, _, h⟩ := bind_ok_inv h)
      | (split at h)
      | (obtain ⟨_, _⟩ := pure_ok_inv h)))

/-! ## `tname_intersect` -/

/-- `tname_intersect(a, b)` answers `nothing` or one of its two arguments: it can only find a
common type name when one name is an ancestor of the other, never a third name (so for siblings
such as `Signed` and `AbstractFloat` it answers `nothing` although `Real` is common to both). It
answers `a` for `tname_intersect(a, a)`, and `Any` for `tname_intersect(Any, b)` whenever `Any` is
recorded as abstract. -/
def TnameIntersectArg : Prop :=
  (∀ n E (a b x : String) s s', (tnameIntersect n E a b).run s = .ok (some x, s') → x = a ∨ x = b) ∧
  (∀ n E (a : String) s, (tnameIntersect n E a a).run s = .ok (some a, s)) ∧
  (∀ n E (b : String) (tn : TypeName) s r s', E.types.names.find? anyName = some tn →
    tn.abstract = true → tn.wrapper = anyType →
    (tnameIntersect n E anyName b).run s = .ok (r, s') → r = some anyName)

theorem tnameIntersectArg_proven : TnameIntersectArg := by
  refine ⟨?_, fun n E a s => by simp [tnameIntersect]; rfl, ?_⟩
  rotate_left
  · intro n E b tn s r s' hf ha hw h
    unfold tnameIntersect at h
    split at h
    · exact (pure_ok_inv h).1.trans (by simp_all)
    have hta : (E.types.typename anyName).run s = .ok (tn, s) := by
      simp [Types.typename, Universe.find?] at hf ⊢; rw [hf]; rfl
    obtain ⟨ta, _, hta', h⟩ := bind_ok_inv h
    rw [hta] at hta'; cases hta'
    obtain ⟨tb, _, _, h⟩ := bind_ok_inv h
    obtain ⟨v1, _, hv1, h⟩ := bind_ok_inv h
    have : v1 = true := by
      rw [hw] at hv1
      simp only [isabstracttype, unwrapUnionall, Val.unwrapUnionall, isType, isTypeEq, isTypeEgal,
        Val.isTypeeq, Val.isTypeegal, anyType, Bool.or_self, Bool.false_eq_true, if_false] at hv1
      obtain ⟨tn', _, htn', hv1⟩ := bind_ok_inv hv1
      have : tn' = tn := by
        simp [Types.typename, Universe.find?, anyName] at hf htn'; rw [hf] at htn'; cases htn'; rfl
      subst this
      rw [← ha]; exact (pure_ok_inv hv1).1
    subst this
    obtain ⟨v2, _, _, h⟩ := bind_ok_inv h
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false,
      show (anyName == anyName) = true from rfl, if_true] at h
    exact (pure_ok_inv h).1
  intro n E a b x s s' h
  unfold tnameIntersect at h
  split at h
  · obtain ⟨h1, -⟩ := pure_ok_inv h; cases h1; exact .inl rfl
  obtain ⟨ta, _, _, h⟩ := bind_ok_inv h
  obtain ⟨tb, _, _, h⟩ := bind_ok_inv h
  obtain ⟨v1, _, _, h⟩ := bind_ok_inv h
  obtain ⟨v2, _, _, h⟩ := bind_ok_inv h
  split at h
  · obtain ⟨h1, -⟩ := pure_ok_inv h; cases h1
  split at h
  · obtain ⟨h1, -⟩ := pure_ok_inv h; cases h1; exact .inl rfl
  obtain ⟨ha, _, _, h⟩ := bind_ok_inv h
  split at h
  · obtain ⟨hb, _, _, h⟩ := bind_ok_inv h
    split at h
    · split at h
      · obtain ⟨_, _, _, h⟩ := bind_ok_inv h
        obtain ⟨h1, -⟩ := pure_ok_inv h
        split at h1 <;> simp_all
      · obtain ⟨h1, -⟩ := pure_ok_inv h
        split at h1 <;> simp_all
    · obtain ⟨h1, -⟩ := pure_ok_inv h; cases h1; exact .inl rfl
  · obtain ⟨h1, -⟩ := pure_ok_inv h; cases h1


/-! ## `union_causes` -/

theorem mem_idsetUnion_left {s t : List ObjId} {x : ObjId} (h : x ∈ s) : x ∈ idsetUnion s t := by
  unfold idsetUnion
  induction t generalizing s with
  | nil => exact h
  | cons y t ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · exact List.mem_append_left _ h

theorem mem_idsetUnion_right {s t : List ObjId} {x : ObjId} (h : x ∈ t) : x ∈ idsetUnion s t := by
  unfold idsetUnion
  induction t generalizing s with
  | nil => cases h
  | cons y t ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp h with
    | inl hx =>
      subst hx
      apply mem_idsetUnion_left (t := t)
      split
      · rename_i hc; exact List.contains_iff_mem.mp hc
      · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    | inr hx => exact ih hx

/-- `union_causes(a, b)` keeps every cause of both arguments, so the `LimitedAccuracy` that
`tmerge_limited` builds from two incomparable types is limited by all their causes. -/
def UnionCausesSuperset : Prop :=
  ∀ (a b r : List ObjId × ObjId) s s', (unionCauses a b).run s = .ok (r, s') →
    (∀ x ∈ a.1, x ∈ r.1) ∧ (∀ x ∈ b.1, x ∈ r.1)

theorem unionCausesSuperset_proven : UnionCausesSuperset := by
  intro a b r s s' h
  unfold unionCauses at h
  split at h
  · rename_i hab
    obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
    refine ⟨fun x hx => ?_, fun x hx => hx⟩
    have := List.all_eq_true.mp hab x hx
    exact List.contains_iff_mem.mp this
  split at h
  · rename_i hba
    obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
    refine ⟨fun x hx => hx, fun x hx => ?_⟩
    have := List.all_eq_true.mp hba x hx
    exact List.contains_iff_mem.mp this
  obtain ⟨c, _, hc, h⟩ := bind_ok_inv h
  obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
  unfold copyIdSet at hc
  obtain ⟨id, _, -, hc⟩ := bind_ok_inv hc
  obtain ⟨h2, -⟩ := pure_ok_inv hc; subst h2
  exact ⟨fun x hx => mem_idsetUnion_left hx, fun x hx => mem_idsetUnion_right hx⟩

/-! ## `union_count_abstract` -/

theorem uniontypes_nonunion {x : Val} (hx : ∀ a b, x ≠ .union a b) : uniontypes x = [x] := by
  cases x <;> simp_all [uniontypes]

theorem unionlen_nonunion {x : Val} (hx : ∀ a b, x ≠ .union a b) : unionlen x = 1 := by
  cases x <;> simp_all [unionlen]

/-- `union_count_abstract(t)` counts the members of the union that are not dispatch elements: at
most one per member (`≤ unionlen(t)`, the bound `issimpleenoughtype` relies on when it compares
`union_count_abstract(t) + 1` with `MAX_TYPEUNION_LENGTH`), and exactly `unionlen(t)` when no
member is a dispatch element. -/
def UnionCountAbstractSpec : Prop :=
  (∀ E (t : Val) s r s', (unionCountAbstract E t).run s = .ok (r, s') → r ≤ unionlen t) ∧
  (∀ E (t : Val), (∀ x ∈ uniontypes t, Returns (isdispatchelem E x) (· = false)) →
    Returns (unionCountAbstract E t) (· = unionlen t))

theorem unionCountAbstractSpec_proven : UnionCountAbstractSpec := by
  refine ⟨?_, ?_⟩
  · intro E t
    induction t using unionCountAbstract.induct with
    | case1 a b iha ihb =>
      intro s r s' h
      simp only [unionCountAbstract] at h
      obtain ⟨ra, s₁, ha, h⟩ := bind_ok_inv h
      obtain ⟨rb, s₂, hb, h⟩ := bind_ok_inv h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      have := iha _ _ _ ha; have := ihb _ _ _ hb
      simp only [unionlen]; omega
    | case2 x hx =>
      intro s r s' h
      rw [unionCountAbstract.eq_2 E x hx] at h
      obtain ⟨d, _, -, h⟩ := bind_ok_inv h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      rw [unionlen_nonunion hx]; split <;> omega
  · intro E t
    induction t using unionCountAbstract.induct with
    | case1 a b iha ihb =>
      intro hall s r s' h
      simp only [unionCountAbstract] at h
      obtain ⟨ra, s₁, ha, h⟩ := bind_ok_inv h
      obtain ⟨rb, s₂, hb, h⟩ := bind_ok_inv h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      have e1 := iha (fun x hx => hall x (by simp [uniontypes, hx])) _ _ _ ha
      have e2 := ihb (fun x hx => hall x (by simp [uniontypes, hx])) _ _ _ hb
      simp only [unionlen]; omega
    | case2 x hx =>
      intro hall s r s' h
      rw [unionCountAbstract.eq_2 E x hx] at h
      obtain ⟨d, s₁, hd, h⟩ := bind_ok_inv h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      have := hall x (by rw [uniontypes_nonunion hx]; exact List.mem_singleton.mpr rfl) _ _ _ hd
      subst this
      rw [unionlen_nonunion hx]; rfl

/-! ## `issimpleenoughtype` -/

/-- A type `issimpleenoughtype` accepts is either the wrapper of its own type name (`t == tn.wrapper`)
or a union of at most `MAX_TYPEUNION_LENGTH` (3) members, at most two of them non-dispatch
elements, with `unioncomplexity(t) ≤ MAX_TYPEUNION_COMPLEXITY` (3). -/
def IssimpleenoughtypeBound : Prop :=
  ∀ n E (t : Val) s s', (issimpleenoughtype n E t).run s = .ok (true, s') →
    (∃ name ps tn s₁ s₂, unwrapUnionall t = .datatype name ps ∧
      (E.types.typename name).run s₁ = .ok (tn, s₁) ∧ (tyEq n E tn.wrapper t).run s₁ = .ok (true, s₂)) ∨
    (unionlen t ≤ MAX_TYPEUNION_LENGTH ∧
      (∃ c s₁ s₂, (unionCountAbstract E t).run s₁ = .ok (c, s₂) ∧ c + 1 ≤ MAX_TYPEUNION_LENGTH) ∧
      (∃ k s₁ s₂, (unioncomplexity n t).run s₁ = .ok (k, s₂) ∧ k ≤ MAX_TYPEUNION_COMPLEXITY))

/-- The converse: a type with at most `MAX_TYPEUNION_LENGTH` members, at most two of them
non-dispatch elements, and union complexity at most `MAX_TYPEUNION_COMPLEXITY` is simple enough. -/
def IssimpleenoughtypeComplete : Prop :=
  ∀ n E (t : Val), unionlen t ≤ MAX_TYPEUNION_LENGTH →
    Returns (unionCountAbstract E t) (· + 1 ≤ MAX_TYPEUNION_LENGTH) →
    Returns (unioncomplexity n t) (· ≤ MAX_TYPEUNION_COMPLEXITY) →
    Returns (issimpleenoughtype n E t) (· = true)

theorem typename_run {T : Types} {name : String} {s s' : Nat} {tn : TypeName}
    (h : (T.typename name).run s = .ok (tn, s')) : s' = s ∧ (T.typename name).run s = .ok (tn, s) := by
  unfold Types.typename at h ⊢
  split at h
  · obtain ⟨h1, h2⟩ := pure_ok_inv h; subst h1 h2; exact ⟨rfl, rfl⟩
  · cases h

theorem issimpleenoughtypeBound_proven : IssimpleenoughtypeBound := by
  intro n E t s s' h
  unfold issimpleenoughtype at h
  have tail : ∀ s₀, (do
        if !(max (unionlen t) ((← unionCountAbstract E t) + 1) ≤ MAX_TYPEUNION_LENGTH) then
          return false
        return (← unioncomplexity n t) ≤ MAX_TYPEUNION_COMPLEXITY : CM Bool).run s₀ = .ok (true, s') →
      unionlen t ≤ MAX_TYPEUNION_LENGTH ∧
      (∃ c s₁ s₂, (unionCountAbstract E t).run s₁ = .ok (c, s₂) ∧ c + 1 ≤ MAX_TYPEUNION_LENGTH) ∧
      (∃ k s₁ s₂, (unioncomplexity n t).run s₁ = .ok (k, s₂) ∧ k ≤ MAX_TYPEUNION_COMPLEXITY) := by
    intro s₀ h
    obtain ⟨c, s₁, hc, h⟩ := bind_ok_inv h
    split at h
    · obtain ⟨h1, -⟩ := pure_ok_inv h; cases h1
    rename_i hle
    obtain ⟨k, s₂, hk, h⟩ := bind_ok_inv h
    obtain ⟨h1, -⟩ := pure_ok_inv h
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not] at hle
    refine ⟨by omega, ⟨c, s₀, s₁, hc, by omega⟩, ⟨k, s₁, s₂, hk, ?_⟩⟩
    exact of_decide_eq_true h1.symm
  simp only at h
  split at h
  · rename_i name ps hut
    obtain ⟨tn, s₁, htn, h⟩ := bind_ok_inv h
    obtain ⟨b, s₂, hb, h⟩ := bind_ok_inv h
    obtain ⟨rfl, htn'⟩ := typename_run htn
    cases b
    · exact .inr (tail _ h)
    · exact .inl ⟨name, ps, tn, _, s₂, hut, htn', hb⟩
  · exact .inr (tail _ h)

theorem issimpleenoughtypeComplete_proven : IssimpleenoughtypeComplete := by
  intro n E t hl hc hk s r s' h
  unfold issimpleenoughtype at h
  have tail : ∀ s₀ r s', (do
        if !(max (unionlen t) ((← unionCountAbstract E t) + 1) ≤ MAX_TYPEUNION_LENGTH) then
          return false
        return (← unioncomplexity n t) ≤ MAX_TYPEUNION_COMPLEXITY : CM Bool).run s₀ = .ok (r, s') →
      r = true := by
    intro s₀ r s' h
    obtain ⟨c, s₁, h₁, h⟩ := bind_ok_inv h
    have := hc _ _ _ h₁
    rw [if_neg (by simp; omega)] at h
    obtain ⟨k, s₂, h₂, h⟩ := bind_ok_inv h
    have := hk _ _ _ h₂
    obtain ⟨h1, -⟩ := pure_ok_inv h
    subst h1; simpa using this
  simp only at h
  split at h
  · obtain ⟨tn, s₁, -, h⟩ := bind_ok_inv h
    obtain ⟨b, s₂, -, h⟩ := bind_ok_inv h
    cases b
    · exact tail _ _ _ h
    · exact (pure_ok_inv h).1
  · exact tail _ _ _ h

/-! ## `n_initialized` -/

/-- `something(findfirst(p, 1:nf), nf + 1) - 1` on 0-based indices. -/
def firstK (p : Nat → Bool) (nf : Nat) : Nat :=
  (((List.range nf).find? p).map (· + 1)).getD (nf + 1) - 1

theorem firstK_spec (p : Nat → Bool) (nf : Nat) :
    firstK p nf ≤ nf ∧ (∀ i < firstK p nf, p i = false) ∧ (firstK p nf < nf → p (firstK p nf) = true) := by
  induction nf with
  | zero => simp [firstK]
  | succ m ih =>
    have hr : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    unfold firstK at ih ⊢
    rw [hr, List.find?_append]
    cases hf : (List.range m).find? p with
    | some i =>
      have hi := List.find?_some hf
      have hm := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      simp only [hf, Option.map_some, Option.getD_some, Option.some_or, Nat.add_sub_cancel] at ih ⊢
      refine ⟨by omega, ih.2.1, fun _ => hi⟩
    | none =>
      simp only [hf, Option.map_none, Option.getD_none, Nat.add_sub_cancel, Option.none_or] at ih ⊢
      cases hpm : p m
      · simp [hpm]
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact ih.2.1 i hi
        · subst hi; exact hpm
      · simp [hpm]
        exact ih.2.1

/-- `n_initialized(::PartialStruct)` is the number of leading fields known to be defined: every
field before it has `undefs[i] === false`, and the field at it (if any) does not. -/
def NInitializedPartialStructSpec : Prop :=
  ∀ (us : List (Option Bool)), let k := nInitializedPartialStruct us
    k ≤ us.length ∧ (∀ i < k, us[i]! = some false) ∧ (k < us.length → us[k]! ≠ some false)

theorem nInitializedPartialStructSpec_proven : NInitializedPartialStructSpec := by
  intro us
  have hk : nInitializedPartialStruct us = firstK (fun i => us[i]! != some false) us.length := rfl
  simp only [hk]
  obtain ⟨h1, h2, h3⟩ := firstK_spec (fun i => us[i]! != some false) us.length
  refine ⟨h1, fun i hi => ?_, fun hk => ?_⟩
  · have := h2 i hi; simpa using this
  · have := h3 hk; simpa using this

/-- `n_initialized(::Const)` is the number of leading defined fields of the value: whenever it
returns `k`, `nfields(val)` returned some `nf ≥ k`, fields `1..k` are defined, and field `k + 1`
(if `k < nf`) is not. -/
def NInitializedConstSpec : Prop :=
  ∀ E (v : Val) s k s', (nInitializedConst E v).run s = .ok (k, s') →
    ∃ nf s₁, (nfieldsOf E v).run s = .ok (nf, s₁) ∧ k ≤ nf ∧
      (∀ i < k, isdefinedField v (i + 1) = true) ∧ (k < nf → isdefinedField v (k + 1) = false)

theorem nInitializedConstSpec_proven : NInitializedConstSpec := by
  intro E v s k s' h
  unfold nInitializedConst at h
  obtain ⟨nf, s₁, hnf, h⟩ := bind_ok_inv h
  obtain ⟨h1, -⟩ := pure_ok_inv h
  obtain ⟨a1, a2, a3⟩ := firstK_spec (fun i => !isdefinedField v (i + 1)) nf
  unfold firstK at a1 a2 a3
  rw [← h1] at a1 a2 a3
  refine ⟨nf, s₁, hnf, a1, fun i hi => ?_, fun hk => ?_⟩
  · have := a2 i hi; simpa using this
  · have := a3 hk; simpa using this

end JuliaLean.Proofs.Compiler.src.typelimits
