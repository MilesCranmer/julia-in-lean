import JuliaLean.Proofs.Compiler.src.typelimits.Layers

/-!
Branch-by-branch statements of the type-size limits and the simplicity order of
`Compiler/src/typelimits.jl`: `limit_type_size`, `is_derived_type`, `type_more_complex`,
`tname_intersect` and `issimplertype`.
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## `limit_type_size` -/

/-- `limit_type_size(t, compare, source, ...)` (`Compiler/src/typelimits.jl:17-33`), with
`sources` the list of line 18-19 (`compare` and `source` unwrapped, one entry when they are
`===`):
* `t` itself when `type_more_complex(t, compare, sources, 1, ...)` is false;
* otherwise `r = _limit_type_size(t, compare, sources, 1, ...)` when `t <: r`;
* otherwise `r' = _limit_type_size(t, Any, sources, 1, ...)` when `t <: r'`;
* otherwise `Any`. -/
def LimitTypeSizeExact : Prop :=
  ∀ n E tm (t compare source : Val) (d l : Int) (e : Bool) (S : List Val),
    Gives (JuliaLean.Compiler.egal n E (unwrapUnionall compare) (unwrapUnionall source)) e →
    S = (if e then [unwrapUnionall compare] else [unwrapUnionall compare, unwrapUnionall source]) →
    (Gives (typeMoreComplex n E t compare S 1 d l) false →
      Gives (limitTypeSize n E tm t compare source d l) t) ∧
    (∀ r₁, Gives (typeMoreComplex n E t compare S 1 d l) true →
      Gives (limitTypeSize_ n E tm t compare S 1 l) r₁ → Gives (issub n E t r₁) true →
      Gives (limitTypeSize n E tm t compare source d l) r₁) ∧
    (∀ r₁ r₂, Gives (typeMoreComplex n E t compare S 1 d l) true →
      Gives (limitTypeSize_ n E tm t compare S 1 l) r₁ → Gives (issub n E t r₁) false →
      Gives (limitTypeSize_ n E tm t anyType S 1 l) r₂ → Gives (issub n E t r₂) true →
      Gives (limitTypeSize n E tm t compare source d l) r₂) ∧
    (∀ r₁ r₂, Gives (typeMoreComplex n E t compare S 1 d l) true →
      Gives (limitTypeSize_ n E tm t compare S 1 l) r₁ → Gives (issub n E t r₁) false →
      Gives (limitTypeSize_ n E tm t anyType S 1 l) r₂ → Gives (issub n E t r₂) false →
      Gives (limitTypeSize n E tm t compare source d l) anyType)

theorem limitTypeSizeExact_proven : LimitTypeSizeExact := by
  intro n E tm t compare source d l e S he hS
  subst hS
  refine ⟨fun h1 s r s' h => ?_, fun r₁ h1 h2 h3 s r s' h => ?_,
    fun r₁ r₂ h1 h2 h3 h4 h5 s r s' h => ?_, fun r₁ r₂ h1 h2 h3 h4 h5 s r s' h => ?_⟩ <;>
  · unfold limitTypeSize at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := he _ _ _ hx; subst x
    cases e <;> simp only [if_true, Bool.false_eq_true, if_false] at h h1 <;>
    · obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
      have := h1 _ _ _ hx; subst x
      first
        | (simp only [Bool.not_false, if_true] at h; exact (pure_ok_inv h).1)
        | (simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
           obtain ⟨x, s₃, hx, h⟩ := bind_ok_inv h
           have := h2 _ _ _ hx; subst x
           obtain ⟨x, s₄, hx, h⟩ := bind_ok_inv h
           have := h3 _ _ _ hx; subst x
           first
             | (simp only [Bool.not_true, Bool.false_eq_true, if_false] at h; exact (pure_ok_inv h).1)
             | (simp only [Bool.not_false, if_true] at h
                obtain ⟨x, s₅, hx, h⟩ := bind_ok_inv h
                have := h4 _ _ _ hx; subst x
                obtain ⟨x, s₆, hx, h⟩ := bind_ok_inv h
                have := h5 _ _ _ hx; subst x
                first
                  | (simp only [Bool.not_true, Bool.false_eq_true, if_false] at h; exact (pure_ok_inv h).1)
                  | (simp only [Bool.not_false, if_true] at h; exact (pure_ok_inv h).1)))

/-! ## `tname_intersect` -/

/-- `tname_intersect(a, b)` (`Compiler/src/typelimits.jl:791-816`) for two different names, given
whether their wrappers are abstract and what the height walks of lines 797-808 return:
* `nothing` when neither wrapper is abstract (the fast path);
* `a` when the walk up from `b` meets `a` (`a` is a supertype name of `b`);
* otherwise, with `heighta` and `heightb` the distances to `Any`, `b` when `a`'s ancestor at
  height `heightb` has name `b`, else `nothing`. -/
def TnameIntersectExact : Prop :=
  ∀ n E (a b : String) (ta tb : TypeName) (xa xb : Bool), a ≠ b →
    (∀ s, (E.types.typename a).run s = .ok (ta, s)) → (∀ s, (E.types.typename b).run s = .ok (tb, s)) →
    Gives (isabstracttype E ta.wrapper) xa → Gives (isabstracttype E tb.wrapper) xb →
    ((xa || xb) = false → Gives (tnameIntersect n E a b) none) ∧
    ((xa || xb) = true → a ≠ anyName → ∀ ha,
      Gives (superHeight n E (unwrapUnionall ta.wrapper) none) (.inl ha) →
      (Gives (superHeight n E (unwrapUnionall tb.wrapper) (some a)) (.inr ()) →
        Gives (tnameIntersect n E a b) (some a)) ∧
      (∀ hb, Gives (superHeight n E (unwrapUnionall tb.wrapper) (some a)) (.inl hb) →
        (hb < ha → ∀ x, Gives (superN n E (unwrapUnionall ta.wrapper) (ha - hb)) x →
          Gives (tnameIntersect n E a b) (if x.name? == some b then some b else none)) ∧
        (ha ≤ hb → Gives (tnameIntersect n E a b)
          (if (unwrapUnionall ta.wrapper).name? == some b then some b else none))))

theorem tnameIntersectExact_proven : TnameIntersectExact := by
  intro n E a b ta tb xa xb hab hta htb hxa hxb
  have hne : (a == b) = false := by simpa using hab
  have pre : ∀ s r s', (tnameIntersect n E a b).run s = .ok (r, s') → ∃ s₁, (do
      if !xa && !xb then return none
      if a == anyName then return some a
      let .inl heighta ← superHeight n E (unwrapUnionall ta.wrapper) none | return none
      let .inl heightb ← superHeight n E (unwrapUnionall tb.wrapper) (some a) | return some a
      let mut x := unwrapUnionall ta.wrapper
      if heighta > heightb then
        x ← superN n E x (heighta - heightb)
      return if x.name? == some b then some b else none : CM (Option String)).run s₁ = .ok (r, s') := by
    intro s r s' h
    unfold tnameIntersect at h
    simp only [hne, Bool.false_eq_true, if_false] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    rw [hta] at hx; cases hx
    obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
    rw [htb] at hx; cases hx
    obtain ⟨x, s₃, hx, h⟩ := bind_ok_inv h
    have := hxa _ _ _ hx; subst x
    obtain ⟨x, s₄, hx, h⟩ := bind_ok_inv h
    have := hxb _ _ _ hx; subst x
    exact ⟨_, h⟩
  refine ⟨fun h0 s r s' h => ?_, fun h0 hany ha hsa => ⟨fun hsb s r s' h => ?_,
    fun hb hsb => ⟨fun hlt x hx s r s' h => ?_, fun hle s r s' h => ?_⟩⟩⟩
  · obtain ⟨s₁, h⟩ := pre s r s' h
    have : (!xa && !xb) = true := by cases xa <;> cases xb <;> simp_all
    simp only [this, if_true] at h; exact (pure_ok_inv h).1
  all_goals
    obtain ⟨s₁, h⟩ := pre s r s' h
    have h1 : (!xa && !xb) = false := by cases xa <;> cases xb <;> simp_all
    have h2 : (a == anyName) = false := by simpa using hany
    simp only [h1, h2, Bool.false_eq_true, if_false] at h
    obtain ⟨y, s₂, hy, h⟩ := bind_ok_inv h
    have := hsa _ _ _ hy; subst y
    obtain ⟨y, s₃, hy, h⟩ := bind_ok_inv h
    have := hsb _ _ _ hy; subst y
  · exact (pure_ok_inv h).1
  · simp only [gt_iff_lt, hlt, if_true] at h
    obtain ⟨y, s₄, hy, h⟩ := bind_ok_inv h
    have := hx _ _ _ hy; subst y
    exact (pure_ok_inv h).1
  · have : ¬ hb < ha := by omega
    simp only [gt_iff_lt, this, if_false] at h
    exact (pure_ok_inv h).1

/-! ## `issimplertype` -/

/-- `issimplertype(𝕃, a, b)` (`Compiler/src/typelimits.jl:342-411`) on the wrappers other than
`PartialStruct`, for `a` and `b` that are not `===` (and not `LimitedAccuracy`), given what the
recursive queries answer:
* `Conditional`: `true` against a `Const`; against a `Conditional` on the same slot and
  definition, `issimplertype` of the then types and of the else types; otherwise `false`
  (lines 356-364). `InterConditional` alike on the slot (lines 365-373);
* `MustAlias`: against a `MustAlias`, `issubalias(b, a)` and `issimplertype` of the `vartyp`s and
  of the `fldtyp`s; otherwise `false` (lines 374-388). `InterMustAlias` alike;
* `PartialOpaque`: `false` (lines 389-399);
* `PartialTask`: against a `PartialTask`, `issimplertype` of the fetch types; otherwise `false`
  (lines 400-404). -/
def IssimplertypeBranches : Prop :=
  ∀ n E L (a b : LElt), a.isLimited = false → b.isLimited = false → Gives (eltEgal n E a b) false →
    (∀ s1 d1 t1 e1 i1, a = .conditional s1 d1 t1 e1 i1 →
      (b.isConst = true → Gives (issimplertype (n + 1) E L a b) true) ∧
      (∀ s2 d2 t2 e2 i2 x y, b = .conditional s2 d2 t2 e2 i2 →
        Gives (issimplertype n E L t1 t2) x → Gives (issimplertype n E L e1 e2) y →
        Gives (issimplertype (n + 1) E L a b) (s1 == s2 && d1 == d2 && x && y)) ∧
      (b.isConst = false → b.isConditional = false → Gives (issimplertype (n + 1) E L a b) false)) ∧
    (∀ s1 t1 e1, a = .interConditional s1 t1 e1 →
      (b.isConst = true → Gives (issimplertype (n + 1) E L a b) true) ∧
      (∀ s2 t2 e2 x y, b = .interConditional s2 t2 e2 →
        Gives (issimplertype n E L t1 t2) x → Gives (issimplertype n E L e1 e2) y →
        Gives (issimplertype (n + 1) E L a b) (s1 == s2 && x && y)) ∧
      (b.isConst = false → b.isInterConditional = false → Gives (issimplertype (n + 1) E L a b) false)) ∧
    (∀ s1 d1 v1 i1 f1, a = .mustAlias s1 d1 v1 i1 f1 →
      (∀ s2 d2 v2 i2 f2 z x y, b = .mustAlias s2 d2 v2 i2 f2 →
        Gives (issubalias (sqsub n E) b a) z → Gives (issimplertype n E L v1 v2) x →
        Gives (issimplertype n E L f1 f2) y → Gives (issimplertype (n + 1) E L a b) (z && x && y)) ∧
      (b.isMustAlias = false → Gives (issimplertype (n + 1) E L a b) false)) ∧
    (∀ s1 v1 i1 f1, a = .interMustAlias s1 v1 i1 f1 →
      (∀ s2 v2 i2 f2 z x y, b = .interMustAlias s2 v2 i2 f2 →
        Gives (issubalias (sqsub n E) b a) z → Gives (issimplertype n E L v1 v2) x →
        Gives (issimplertype n E L f1 f2) y → Gives (issimplertype (n + 1) E L a b) (z && x && y)) ∧
      (b.isInterMustAlias = false → Gives (issimplertype (n + 1) E L a b) false)) ∧
    (a.isPartialOpaque = true → Gives (issimplertype (n + 1) E L a b) false) ∧
    (∀ f1, a = .partialTask f1 →
      (∀ f2 x, b = .partialTask f2 → Gives (issimplertype n E L f1 f2) x →
        Gives (issimplertype (n + 1) E L a b) x) ∧
      (b.isPartialTask = false → Gives (issimplertype (n + 1) E L a b) false))

set_option hygiene false in
/-- Unfold `issimplertype` past the `LimitedAccuracy` and `===` checks. -/
macro "isimp_pre" : tactic => `(tactic| (
    unfold issimplertype at h
    simp only [hla, hlb, Bool.or_self, Bool.false_eq_true, if_false] at h
    obtain ⟨_e, _s₁, _he, h⟩ := bind_ok_inv h
    have := he _ _ _ _he; subst _e
    simp only [Bool.false_eq_true, if_false] at h))

theorem issimplertypeBranches_proven : IssimplertypeBranches := by
  intro n E L a b hla hlb he
  refine ⟨fun s1 d1 t1 e1 i1 ha => ⟨fun hc s r s' h => ?_, fun s2 d2 t2 e2 i2 x y hb hx hy s r s' h => ?_,
      fun hc hcd s r s' h => ?_⟩,
    fun s1 t1 e1 ha => ⟨fun hc s r s' h => ?_, fun s2 t2 e2 x y hb hx hy s r s' h => ?_,
      fun hc hcd s r s' h => ?_⟩,
    fun s1 d1 v1 i1 f1 ha => ⟨fun s2 d2 v2 i2 f2 z x y hb hz hx hy s r s' h => ?_, fun hm s r s' h => ?_⟩,
    fun s1 v1 i1 f1 ha => ⟨fun s2 v2 i2 f2 z x y hb hz hx hy s r s' h => ?_, fun hm s r s' h => ?_⟩,
    fun hpo s r s' h => ?_,
    fun f1 ha => ⟨fun f2 x hb hx s r s' h => ?_, fun hpt s r s' h => ?_⟩⟩
  -- Conditional
  · subst ha; isimp_pre
    simp only [hc, if_true] at h; exact (pure_ok_inv h).1
  · subst ha hb; isimp_pre
    simp only [LElt.isConst, Bool.false_eq_true, if_false, isSameConditionals, pure_bind] at h
    show r = _
    cases hsd : (s1 == s2 && d1 == d2)
    · simp only [hsd, Bool.not_false, if_true, Bool.false_and] at h ⊢; exact (pure_ok_inv h).1
    · simp only [hsd, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and] at h ⊢
      obtain ⟨x', s₂, hx', h⟩ := bind_ok_inv h
      have := hx _ _ _ hx'; subst x'
      cases x
      · simp only [Bool.not_false, if_true, Bool.false_and] at h ⊢; exact (pure_ok_inv h).1
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and] at h ⊢
        obtain ⟨y', s₃, hy', h⟩ := bind_ok_inv h
        have := hy _ _ _ hy'; subst y'
        cases y
        · simp only [Bool.not_false, if_true] at h; exact (pure_ok_inv h).1
        · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h; exact (pure_ok_inv h).1
  · subst ha; isimp_pre
    simp only [hc, Bool.false_eq_true, if_false] at h
    split at h
    · simp [LElt.isConditional] at hcd
    · exact (pure_ok_inv h).1
  -- InterConditional
  · subst ha; isimp_pre
    simp only [hc, if_true] at h; exact (pure_ok_inv h).1
  · subst ha hb; isimp_pre
    simp only [LElt.isConst, Bool.false_eq_true, if_false, isSameConditionals, pure_bind] at h
    show r = _
    cases hsd : (s1 == s2)
    · simp only [hsd, Bool.not_false, if_true, Bool.false_and] at h ⊢; exact (pure_ok_inv h).1
    · simp only [hsd, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and] at h ⊢
      obtain ⟨x', s₂, hx', h⟩ := bind_ok_inv h
      have := hx _ _ _ hx'; subst x'
      cases x
      · simp only [Bool.not_false, if_true, Bool.false_and] at h ⊢; exact (pure_ok_inv h).1
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and] at h ⊢
        obtain ⟨y', s₃, hy', h⟩ := bind_ok_inv h
        have := hy _ _ _ hy'; subst y'
        cases y
        · simp only [Bool.not_false, if_true] at h; exact (pure_ok_inv h).1
        · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h; exact (pure_ok_inv h).1
  · subst ha; isimp_pre
    simp only [hc, Bool.false_eq_true, if_false] at h
    split at h
    · simp [LElt.isInterConditional] at hcd
    · exact (pure_ok_inv h).1
  -- MustAlias
  all_goals try (
    subst ha hb; isimp_pre
    show r = _
    obtain ⟨z', s₂, hz', h⟩ := bind_ok_inv h
    have := hz _ _ _ hz'; subst z'
    cases z
    · simp only [Bool.not_false, if_true, Bool.false_and] at h ⊢; exact (pure_ok_inv h).1
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and] at h ⊢
      obtain ⟨x', s₃, hx', h⟩ := bind_ok_inv h
      have := hx _ _ _ hx'; subst x'
      cases x
      · simp only [Bool.not_false, if_true, Bool.false_and] at h ⊢; exact (pure_ok_inv h).1
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and] at h ⊢
        obtain ⟨y', s₄, hy', h⟩ := bind_ok_inv h
        have := hy _ _ _ hy'; subst y'
        cases y
        · simp only [Bool.not_false, if_true] at h; exact (pure_ok_inv h).1
        · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h; exact (pure_ok_inv h).1)
  all_goals try (
    subst ha; isimp_pre
    split at h
    · first | simp [LElt.isMustAlias] at hm | simp [LElt.isInterMustAlias] at hm
    · exact (pure_ok_inv h).1)
  -- PartialOpaque
  · cases a <;> simp [LElt.isPartialOpaque] at hpo
    isimp_pre
    exact (pure_ok_inv h).1
  -- PartialTask
  · subst ha hb; isimp_pre
    exact hx _ _ _ h
  · subst ha; isimp_pre
    split at h
    · simp [LElt.isPartialTask] at hpt
    · exact (pure_ok_inv h).1

/-! ## Loops that stop at the first `true` -/

/-- A `for x in l` loop that returns `true` at the first `x` whose query answers `true` ends with
`some true` exactly when some `x` answers `true`. -/
theorem forIn_firstTrue {α : Type} (l : List α) (g : α → CM Bool) (F : α → Bool)
    (hg : ∀ x ∈ l, Gives (g x) (F x)) :
    ∀ s (st : Option Bool × Unit) s', (forIn l ((none : Option Bool), ()) (fun x (_ : Option Bool × Unit) => do
        let b ← g x
        if b = true then pure (ForInStep.done (some true, ())) else pure (ForInStep.yield (none, ())))).run s
        = .ok (st, s') → st.1 = if l.any F then some true else none := by
  induction l with
  | nil =>
    intro s st s' h
    simp only [List.forIn_nil] at h
    obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1; rfl
  | cons x xs ih =>
    intro s st s' h
    rw [List.forIn_cons] at h
    obtain ⟨step, s₁, hs, h⟩ := bind_ok_inv h
    obtain ⟨b, s₂, hb, hs⟩ := bind_ok_inv hs
    have := hg x (List.mem_cons_self ..) _ _ _ hb; subst this
    cases hF : F x
    · simp only [hF, Bool.false_eq_true, if_false] at hs
      obtain ⟨h1, -⟩ := pure_ok_inv hs; subst h1
      have := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) _ _ _ h
      simp [hF, this]
    · simp only [hF, if_true] at hs
      obtain ⟨h1, -⟩ := pure_ok_inv hs; subst h1
      obtain ⟨h2, -⟩ := pure_ok_inv h; subst h2
      simp [hF]

/-! ## `is_derived_type` -/

/-- `is_derived_type(t, c, mindepth)` (`Compiler/src/typelimits.jl:37-77`) on `t` and `c` without
free type variables, given what `===` and the recursive searches answer; `t'` and `c'` are `t` and
`c` with a `Vararg` unwrapped (lines 47-48):
* `t === c`: `mindepth ≤ 1`;
* `c'` a `Union`: found in either member (line 51);
* `c'` a `UnionAll`: found in the bound or the body (line 55);
* `c'` a `Type{T}`: found in `T` (line 57);
* `c'` another `DataType`: `t'` is a strict supertype of `c'` below `Any` (lines 62-68, only when
  `t'` is a `DataType`), or found in one of the parameters at `mindepth - 1` (lines 72-74);
* anything else: `false`. -/
def IsDerivedTypeBranches : Prop :=
  ∀ n E (t c t' c' : Val) d,
    (JuliaLean.Compiler.hasFreeTypevars t || JuliaLean.Compiler.hasFreeTypevars c) = false →
    t' = (if isvarargtype t then unwrapva t else t) → c' = (if isvarargtype c then unwrapva c else c) →
    (Gives (JuliaLean.Compiler.egal n E t c) true → Gives (isDerivedType (n + 1) E t c d) (decide (d ≤ 1))) ∧
    (Gives (JuliaLean.Compiler.egal n E t c) false →
      (∀ ca cb x y, c' = .union ca cb → Gives (isDerivedType n E t' ca d) x →
        Gives (isDerivedType n E t' cb d) y → Gives (isDerivedType (n + 1) E t c d) (x || y)) ∧
      (∀ i nm lb ub body x y, c' = .unionall i nm lb ub body → Gives (isDerivedType n E t' ub d) x →
        Gives (isDerivedType n E t' body d) y → Gives (isDerivedType (n + 1) E t c d) (x || y)) ∧
      (∀ T x, c' = .typeeq T → Gives (isDerivedType n E t' T d) x →
        Gives (isDerivedType (n + 1) E t c d) x) ∧
      (∀ name ps sup ch (F : Val → Bool), c' = .datatype name ps → Gives (supertypeDT n E c') sup →
        Gives (superChainHas n E t' sup) ch →
        (∀ p ∈ ps, Gives (isDerivedType n E t' p (if d > 0 then d - 1 else d)) (F p)) →
        Gives (isDerivedType (n + 1) E t c d) ((t'.isDatatype && ch) || ps.any F)) ∧
      ((∀ a b, c' ≠ .union a b) → c'.isUnionall = false → isType c' = false → c'.isDatatype = false →
        Gives (isDerivedType (n + 1) E t c d) false))

theorem isDerivedTypeBranches_proven : IsDerivedTypeBranches := by
  intro n E t c t' c' d hf ht hc
  refine ⟨fun he s r s' h => ?_, fun he => ⟨fun ca cb x y hu hx hy s r s' h => ?_,
    fun i nm lb ub body x y hu hx hy s r s' h => ?_, fun T x hu hx s r s' h => ?_,
    fun name ps sup ch F hu hsup hch hF s r s' h => ?_, fun hnu hnua hnty hnd s r s' h => ?_⟩⟩
  · unfold isDerivedType at h
    simp only [hf, Bool.false_eq_true, if_false] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := he _ _ _ hx; subst x
    simp only [if_true] at h
    exact (pure_ok_inv h).1
  all_goals
    unfold isDerivedType at h
    simp only [hf, Bool.false_eq_true, if_false] at h
    obtain ⟨e, s₁, hx', h⟩ := bind_ok_inv h
    have := he _ _ _ hx'; subst e
    simp only [Bool.false_eq_true, if_false, ← ht, ← hc] at h
  · rw [hu] at h
    obtain ⟨x', s₂, hx', h⟩ := bind_ok_inv h
    have := hx _ _ _ hx'; subst x'
    cases x
    · simp only [Bool.false_eq_true, if_false, Bool.false_or] at h ⊢; exact hy _ _ _ h
    · simp only [if_true, Bool.true_or] at h ⊢; exact (pure_ok_inv h).1
  · rw [hu] at h
    obtain ⟨x', s₂, hx', h⟩ := bind_ok_inv h
    have := hx _ _ _ hx'; subst x'
    cases x
    · simp only [Bool.false_eq_true, if_false, Bool.false_or] at h ⊢; exact hy _ _ _ h
    · simp only [if_true, Bool.true_or] at h ⊢; exact (pure_ok_inv h).1
  · rw [hu] at h
    simp only [isType, isTypeEq, Val.isTypeeq, Bool.true_or, if_true, typeParameter, pure_bind] at h
    exact hx _ _ _ h
  · subst hu
    have hnt : isType (Val.datatype name ps) = false := rfl
    have hcd : (Val.datatype name ps).isDatatype = true := rfl
    simp only [hnt, hcd, Val.params, Bool.false_eq_true, if_false, if_true] at h
    show r = _
    have loop : ∀ s₀ r s₀', (do
        let __s ← forIn ps ((none : Option Bool), ()) (fun p (_ : Option Bool × Unit) => do
          let b ← isDerivedType n E t' p (if d > 0 then d - 1 else d)
          if b = true then pure (ForInStep.done (some true, ())) else pure (ForInStep.yield (none, ())))
        match __s.fst with
        | some r => pure r
        | none => pure false : CM Bool).run s₀ = .ok (r, s₀') → r = ps.any F := by
      intro s₀ r s₀' h
      obtain ⟨st, s₂, hst, h⟩ := bind_ok_inv h
      have := forIn_firstTrue ps _ F hF _ _ _ hst
      rw [this] at h
      cases hany : ps.any F
      · simp only [hany, Bool.false_eq_true, if_false] at h; exact (pure_ok_inv h).1
      · simp only [hany, if_true] at h; exact (pure_ok_inv h).1
    have loop' : ∀ s₀ r s₀', (do
        let __s ← forIn ps ((none : Option Bool), ()) (fun p (_ : Option Bool × Unit) => do
          let b ← isDerivedType n E t' p (if d > 0 then d - 1 else d)
          if b = true then pure (ForInStep.done (some true, ())) else pure (ForInStep.yield (none, ())))
        match __s.fst with
        | some r => pure r
        | none => pure false : CM Bool).run s₀ = .ok (r, s₀') → r = ps.any F := loop
    clear loop
    cases htd : t'.isDatatype
    · simp only [htd, Bool.false_eq_true, if_false] at h
      first | (rw [loop' _ _ _ h]; simp) | (obtain ⟨st, s₉, hst, h⟩ := bind_ok_inv h; have := forIn_firstTrue ps _ F hF _ _ _ hst; rw [this] at h; cases hany : ps.any F <;> simp [hany] at h ⊢ <;> exact (pure_ok_inv h).1)
    · simp only [htd, if_true] at h
      obtain ⟨x', s₂, hx', h⟩ := bind_ok_inv h
      have := hsup _ _ _ hx'; subst x'
      obtain ⟨x', s₃, hx', h⟩ := bind_ok_inv h
      have := hch _ _ _ hx'; subst x'
      cases ch
      · simp only [Bool.false_eq_true, if_false] at h
        first | (rw [loop' _ _ _ h]; simp) | (obtain ⟨st, s₉, hst, h⟩ := bind_ok_inv h; have := forIn_firstTrue ps _ F hF _ _ _ hst; rw [this] at h; cases hany : ps.any F <;> simp [hany] at h ⊢ <;> exact (pure_ok_inv h).1)
      · simp only [if_true] at h
        rw [(pure_ok_inv h).1]; simp
  · split at h
    · exact absurd rfl (hnu _ _)
    · simp [Val.isUnionall] at hnua
    · simp only [hnty, hnd, Bool.false_eq_true, if_false] at h
      exact (pure_ok_inv h).1

/-! ## `type_more_complex` -/

/-- `type_more_complex(t, c, sources, depth, tupledepth, allowed_tuplelen)`
(`Compiler/src/typelimits.jl:228-313`) past its trivial cases (lines 230-237: `t !== c`, `t` not
`Union{}`, not a parameterless `DataType`, and not derived from the sources), for `t` and `c` that
are not `Vararg`s or `UnionAll`s, given what the recursive comparisons answer:
* `c` a `TypeVar` (lines 252-259): against a `TypeVar` `t`, `true` when `t.lb` is neither
  `Union{}` nor `=== c.lb`, else the comparison of the upper bounds at `depth + 1`; against any
  other `t`, `true` when `c.lb` is not `Union{}`, else `t` against `c.ub`;
* `c` a `Union` (lines 260-266): member by member against a `Union` `t` (either one more complex),
  else `t` against both members (more complex than both);
* two `Int`s (lines 267-268): `t !== 1 && !(0 <= t < c)`;
* `t` a `Type{T}` (lines 270-287): `T` against `c`'s parameter when `c` is a `Type`, else `true` at
  tuple depth 0 ("cannot allow nesting"), else `T` against `Union{}`, at `depth + 1` with the tuple
  depth cut to 1 or 0;
* two `DataType`s (lines 289-310): `true` for different names or when `c` has fewer parameters;
  `false` for the depth-1 case of line 295; otherwise `true` exactly when some parameter `tP[i]` is
  more complex than `cP[i + ntail]` (1-based `i`);
* a `DataType` `t` against anything that is not a `DataType`, `Union` or `TypeVar`: `true`
  (line 312). -/
def TypeMoreComplexBranches : Prop :=
  ∀ n E (t c : Val) srcs (d td l : Int),
    Gives (JuliaLean.Compiler.egal n E t c) false → (t == .bottom) = false →
    (t.isDatatype && t.params.isEmpty) = false →
    Gives (isDerivedTypeFromAny n E (unwrapUnionall t) srcs d) false →
    isvarargtype t = false → isvarargtype c = false → t.isUnionall = false → c.isUnionall = false →
    (∀ ci cn clb cub, c = .typevar ci cn clb cub →
      ((∀ ti tn tlb tub, t ≠ .typevar ti tn tlb tub) → (clb != .bottom) = true →
        Gives (typeMoreComplex (n + 1) E t c srcs d td l) true) ∧
      ((∀ ti tn tlb tub, t ≠ .typevar ti tn tlb tub) → clb = .bottom → ∀ x,
        Gives (typeMoreComplex n E t cub srcs d 1 0) x → Gives (typeMoreComplex (n + 1) E t c srcs d td l) x) ∧
      (∀ ti tn tlb tub e x, t = .typevar ti tn tlb tub → Gives (JuliaLean.Compiler.egal n E tlb clb) e →
        Gives (typeMoreComplex n E tub cub srcs (d + 1) 1 0) x →
        Gives (typeMoreComplex (n + 1) E t c srcs d td l) (!(tlb == .bottom || e) || x))) ∧
    (∀ ca cb, c = .union ca cb →
      (∀ ta tb x y, t = .union ta tb → Gives (typeMoreComplex n E ta ca srcs d td l) x →
        Gives (typeMoreComplex n E tb cb srcs d td l) y →
        Gives (typeMoreComplex (n + 1) E t c srcs d td l) (x || y)) ∧
      ((∀ ta tb, t ≠ .union ta tb) → ∀ x y, Gives (typeMoreComplex n E t ca srcs d td l) x →
        Gives (typeMoreComplex n E t cb srcs d td l) y →
        Gives (typeMoreComplex (n + 1) E t c srcs d td l) (x && y))) ∧
    (∀ ti ci, t = .long ti → c = .long ci →
      Gives (typeMoreComplex (n + 1) E t c srcs d td l) (ti != 1 && !(decide (0 ≤ ti) && decide (ti < ci)))) ∧
    (∀ T, t = .typeeq T → (∀ a b, c ≠ .union a b) → (∀ i nm lb ub, c ≠ .typevar i nm lb ub) →
      (∀ C x, c = .typeeq C → Gives (typeMoreComplex n E T C srcs (d + 1) (if td > 1 then 1 else 0) 0) x →
        Gives (typeMoreComplex (n + 1) E t c srcs d td l) x) ∧
      (isType c = false → td = 0 → Gives (typeMoreComplex (n + 1) E t c srcs d td l) true) ∧
      (isType c = false → td ≠ 0 → ∀ x,
        Gives (typeMoreComplex n E T .bottom srcs (d + 1) (if td > 1 then 1 else 0) 0) x →
        Gives (typeMoreComplex (n + 1) E t c srcs d td l) x)) ∧
    (∀ tn tP cn cP, t = .datatype tn tP → c = .datatype cn cP →
      (tn ≠ cn → Gives (typeMoreComplex (n + 1) E t c srcs d td l) true) ∧
      (tn = cn → cP.length < tP.length → Gives (typeMoreComplex (n + 1) E t c srcs d td l) true) ∧
      (tn = cn → tP.length ≤ cP.length →
        (decide (cP.length > tP.length) && !isvarargtype tP.getLast! && d == 1) = true →
        Gives (typeMoreComplex (n + 1) E t c srcs d td l) false) ∧
      (tn = cn → tP.length ≤ cP.length →
        (decide (cP.length > tP.length) && !isvarargtype tP.getLast! && d == 1) = false →
        ∀ F : Nat → Bool, (∀ i ∈ List.range' 1 tP.length,
          Gives (typeMoreComplex n E tP[i - 1]! cP[i + (cP.length - tP.length) - 1]! srcs (d + 1)
            (if (tn == tupleName && decide (td > 0)) = true then td - 1 else 0) 0) (F i)) →
        Gives (typeMoreComplex (n + 1) E t c srcs d td l) ((List.range' 1 tP.length).any F))) ∧
    (∀ tn tP, t = .datatype tn tP → c.isDatatype = false → (∀ a b, c ≠ .union a b) →
      (∀ i nm lb ub, c ≠ .typevar i nm lb ub) → Gives (typeMoreComplex (n + 1) E t c srcs d td l) true)

set_option hygiene false in
/-- Unfold `type_more_complex` past its trivial cases and the wrapper peeling. -/
macro "tmc_pre" : tactic => `(tactic| (
    unfold typeMoreComplex at h
    obtain ⟨_e, _s₁, _he, h⟩ := bind_ok_inv h
    have := he _ _ _ _he; subst _e
    simp only [hb, hd, Bool.false_eq_true, if_false] at h
    obtain ⟨_f, _s₂, _hf, h⟩ := bind_ok_inv h
    have := hdf _ _ _ _hf; subst _f
    simp only [hvt, hvc, hut, huc, Bool.false_eq_true, if_false] at h))

theorem typeMoreComplexBranches_proven : TypeMoreComplexBranches := by
  intro n E t c srcs d td l he hb hd hdf hvt hvc hut huc
  refine ⟨fun ci cn clb cub hc => ⟨fun hnt hlb s r s' h => ?_, fun hnt hlb x hx s r s' h => ?_,
      fun ti tn tlb tub e x ht hee hx s r s' h => ?_⟩,
    fun ca cb hc => ⟨fun ta tb x y ht hx hy s r s' h => ?_, fun hnt x y hx hy s r s' h => ?_⟩,
    fun ti ci ht hc s r s' h => ?_,
    fun T ht hnu hntv => ⟨fun C x hc hx s r s' h => ?_, fun hty htd s r s' h => ?_,
      fun hty htd x hx s r s' h => ?_⟩,
    fun tn tP cn cP ht hc => ⟨fun hne s r s' h => ?_, fun heq hlt s r s' h => ?_,
      fun heq hle hcase s r s' h => ?_, fun heq hle hcase F hF s r s' h => ?_⟩,
    fun tn tP ht hcd hnu hntv s r s' h => ?_⟩
  -- TypeVar comparison
  · subst hc; tmc_pre
    try (split at h; · exact absurd rfl (hnt _ _ _ _))
    simp only [hlb, if_true] at h; exact (pure_ok_inv h).1
  · subst hc hlb; tmc_pre
    try (split at h; · exact absurd rfl (hnt _ _ _ _))
    try simp only [bne_self_eq_false, Bool.false_eq_true, if_false] at h
    exact hx _ _ _ h
  · subst hc ht; tmc_pre
    obtain ⟨e', s₃, he', h⟩ := bind_ok_inv h
    have := hee _ _ _ he'; subst e'
    show r = _
    cases hq : (tlb == Val.bottom || e)
    · simp only [hq, Bool.not_false, if_true, Bool.true_or] at h ⊢; exact (pure_ok_inv h).1
    · simp only [hq, Bool.not_true, Bool.false_eq_true, if_false, Bool.false_or] at h ⊢
      exact hx _ _ _ h
  -- Union comparison
  · subst hc ht; tmc_pre
    obtain ⟨x', s₃, hx', h⟩ := bind_ok_inv h
    have := hx _ _ _ hx'; subst x'
    cases x
    · simp only [Bool.false_eq_true, if_false, Bool.false_or] at h ⊢; exact hy _ _ _ h
    · simp only [if_true, Bool.true_or] at h ⊢; exact (pure_ok_inv h).1
  · subst hc; tmc_pre
    try (split at h; · exact absurd rfl (hnt _ _))
    obtain ⟨x', s₃, hx', h⟩ := bind_ok_inv h
    have := hx _ _ _ hx'; subst x'
    cases x
    · simp only [Bool.not_false, if_true, Bool.false_and] at h ⊢; exact (pure_ok_inv h).1
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and] at h ⊢
      exact hy _ _ _ h
  -- Int
  · subst hc ht; tmc_pre
    exact (pure_ok_inv h).1
  -- Type{T}
  · subst ht hc; tmc_pre
    have hT : isType (Val.typeeq T) = true := rfl
    have hC : isType (Val.typeeq C) = true := rfl
    have hp : ∀ X, typeParameter (Val.typeeq X) = pure X := fun _ => rfl
    simp only [hT, hC, hp, if_true, pure_bind] at h
    exact hx _ _ _ h
  · subst ht; tmc_pre
    have hT : isType (Val.typeeq T) = true := rfl
    have hp : ∀ X, typeParameter (Val.typeeq X) = pure X := fun _ => rfl
    subst htd
    simp only [hT, hty, hp, if_true, pure_bind, Bool.false_eq_true, if_false, beq_self_eq_true] at h
    exact (pure_ok_inv h).1
  · subst ht; tmc_pre
    have hT : isType (Val.typeeq T) = true := rfl
    have hp : ∀ X, typeParameter (Val.typeeq X) = pure X := fun _ => rfl
    have : (td == 0) = false := by simpa using htd
    simp only [hT, hty, hp, this, if_true, pure_bind, Bool.false_eq_true, if_false] at h
    exact hx _ _ _ h
  -- DataTypes
  all_goals try (subst ht hc; tmc_pre)
  · have : (tn == cn) = false := by simpa using hne
    have hT : isType (Val.datatype tn tP) = false := rfl
    simp only [hT, Bool.false_eq_true, if_false, this] at h
    exact (pure_ok_inv h).1
  · subst heq
    have hT : isType (Val.datatype tn tP) = false := rfl
    simp only [hT, Bool.false_eq_true, if_false, beq_self_eq_true, if_true, hlt] at h
    exact (pure_ok_inv h).1
  · subst heq
    have hnl : ¬ cP.length < tP.length := by omega
    have hne : tP.isEmpty = false := by simpa [Val.isDatatype, Val.params] using hd
    have hT : isType (Val.datatype tn tP) = false := rfl
    simp only [hT, Bool.false_eq_true, if_false, beq_self_eq_true, if_true, hnl, hne, hcase] at h
    exact (pure_ok_inv h).1
  · subst heq
    have hnl : ¬ cP.length < tP.length := by omega
    have hne : tP.isEmpty = false := by simpa [Val.isDatatype, Val.params] using hd
    have hT : isType (Val.datatype tn tP) = false := rfl
    simp only [hT, Bool.false_eq_true, if_false, beq_self_eq_true, if_true, hnl, hne, hcase] at h
    obtain ⟨st, s₃, hst, h⟩ := bind_ok_inv h
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hst
    have hsz : ([1:tP.length + 1]).size = tP.length := by simp [Std.Legacy.Range.size]
    rw [hsz] at hst
    have := forIn_firstTrue (List.range' 1 tP.length) _ F hF _ _ _ hst
    rw [this] at h
    show r = _
    cases hany : (List.range' 1 tP.length).any F <;> simp only [hany, Bool.false_eq_true, if_false, if_true] at h <;>
      exact (pure_ok_inv h).1
  -- DataType against something else
  · subst ht; tmc_pre
    have hT : isType (Val.datatype tn tP) = false := rfl
    simp only [hT, Bool.false_eq_true, if_false] at h
    repeat' (split at h)
    all_goals first
      | exact (pure_ok_inv h).1
      | exact absurd rfl (hntv _ _ _ _)
      | exact absurd rfl (hnu _ _)
      | simp [Val.isDatatype] at hcd

/-! ## `issimplertype` on a `PartialStruct` -/

/-- A `for` loop whose body answers `yield` (keep going) on the elements that pass and
`done (some false)` on the first that fails ends with `none` exactly when every element passes. -/
theorem forIn_firstFalse {α : Type} (l : List α)
    (f : α → Option Bool × Unit → CM (ForInStep (Option Bool × Unit))) (F : α → Bool)
    (hf : ∀ x ∈ l, ∀ s step s', (f x (none, ())).run s = .ok (step, s') →
      step = if F x then .yield (none, ()) else .done (some false, ())) :
    ∀ s st s', (forIn l ((none : Option Bool), ()) f).run s = .ok (st, s') →
      st.1 = if l.all F then none else some false := by
  induction l with
  | nil =>
    intro s st s' h
    simp only [List.forIn_nil] at h
    obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1; rfl
  | cons x xs ih =>
    intro s st s' h
    rw [List.forIn_cons] at h
    obtain ⟨step, s₁, hs, h⟩ := bind_ok_inv h
    have := hf x (List.mem_cons_self ..) _ _ _ hs; subst this
    cases hF : F x
    · simp only [hF, Bool.false_eq_true, if_false] at h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      simp [hF]
    · simp only [hF, if_true] at h
      have := ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) _ _ _ h
      simp [hF, this]

/-- Whether `_typename` found a single type name. -/
def _root_.JuliaLean.Compiler.TypenameT.isConst : TypenameT → Bool | .const _ => true | _ => false

/-- `issimplertype(𝕃, a::PartialStruct, b)` (`Compiler/src/typelimits.jl:345-355`) when `a` and `b`
are not `===`, the widened type of `a` is simpler than that of `b`, and `b` is a `Const` or a
`PartialStruct` with at least as many initialized fields: `a` is simpler than `b` exactly when
every field `aᵢ` of `a` (1-based, `Vararg` unwrapped) is lattice-equal to the declared field type,
or to the wrapper of its own type name, or to `getfield_tfunc(b, i)` ("It is not enough for ai to
be simpler than bi: it must exactly equal"). The `B1`..`E3` are what those queries answer for
field `i`. -/
def IssimplertypePartialStruct : Prop :=
  ∀ n E L atyp us (fs : List LElt) ui fi (b : LElt) (w : Val) (k1 k2 : Nat)
    (B1 : Nat → Val) (E1 : Nat → Bool) (W : Nat → Val) (TN : Nat → TypeName) (E2 : Nat → Bool)
    (G : Nat → LElt) (E3 : Nat → Bool),
    b.isLimited = false → Gives (eltEgal n E (.partialStruct atyp us fs ui fi) b) false →
    Gives (widenconst n E b) w → Gives (issimplertype n E L (.ty atyp) (.ty w)) true →
    (b.isConst || b.isPartialStruct) = true →
    Gives (nInitialized E (.partialStruct atyp us fs ui fi)) k1 → Gives (nInitialized E b) k2 → k1 ≤ k2 →
    (∀ i ∈ List.range' 1 fs.length,
      Gives (fieldtypeIdx E atyp i) (B1 i) ∧
      Gives (isLatticeEqual n E L (unwrapvaElt fs[i - 1]!) (.ty (B1 i))) (E1 i) ∧
      Gives (widenconst n E (unwrapvaElt fs[i - 1]!)) (W i) ∧
      (∀ tname, typenameT (W i) = .const tname → Gives (E.types.typename tname) (TN i) ∧
        Gives (isLatticeEqual n E L (unwrapvaElt fs[i - 1]!) (.ty (TN i).wrapper)) (E2 i)) ∧
      Gives (getfieldTfuncIdx n E L b i) (G i) ∧
      Gives (isLatticeEqual n E L (unwrapvaElt fs[i - 1]!) (G i)) (E3 i)) →
    Gives (issimplertype (n + 1) E L (.partialStruct atyp us fs ui fi) b)
      ((List.range' 1 fs.length).all fun i => E1 i || ((typenameT (W i)).isConst && E2 i) || E3 i)

theorem issimplertypePartialStruct_proven : IssimplertypePartialStruct := by
  intro n E L atyp us fs ui fi b w k1 k2 B1 E1 W TN E2 G E3 hlb he hw hsimp hcp hk1 hk2 hk hfld
    s r s' h
  have hla : (LElt.partialStruct atyp us fs ui fi).isLimited = false := rfl
  unfold issimplertype at h
  simp only [hla, hlb, Bool.or_self, Bool.false_eq_true, if_false] at h
  obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
  have := he _ _ _ hx; subst x
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
  have := hw _ _ _ hx; subst x
  obtain ⟨x, s₃, hx, h⟩ := bind_ok_inv h
  have := hsimp _ _ _ hx; subst x
  simp only [Bool.not_true, Bool.false_eq_true, if_false, hcp, if_true] at h
  obtain ⟨x, s₄, hx, h⟩ := bind_ok_inv h
  have := hk1 _ _ _ hx; subst x
  obtain ⟨x, s₅, hx, h⟩ := bind_ok_inv h
  have := hk2 _ _ _ hx; subst x
  simp only [hk, decide_true, Bool.not_true, Bool.false_eq_true, if_false] at h
  obtain ⟨st, s₆, hst, h⟩ := bind_ok_inv h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hst
  have hsz : ([1:fs.length + 1]).size = fs.length := by simp [Std.Legacy.Range.size]
  rw [hsz] at hst
  have := forIn_firstFalse (List.range' 1 fs.length) _
    (fun i => E1 i || ((typenameT (W i)).isConst && E2 i) || E3 i) (by
      intro i hi s step s' hb
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfld i hi
      try simp only at hb
      obtain ⟨x, t₁, hx, hb⟩ := bind_ok_inv hb
      have := h1 _ _ _ hx; subst x
      obtain ⟨x, t₂, hx, hb⟩ := bind_ok_inv hb
      have := h2 _ _ _ hx; subst x
      cases he1 : E1 i
      · simp only [he1, Bool.false_eq_true, if_false, Bool.false_or] at hb ⊢
        obtain ⟨x, t₃, hx, hb⟩ := bind_ok_inv hb
        have := h3 _ _ _ hx; subst x
        cases htn : typenameT (W i) with
        | const tname =>
          simp only [htn] at hb
          obtain ⟨hh1, hh2⟩ := h4 tname htn
          obtain ⟨x, t₄, hx, hb⟩ := bind_ok_inv hb
          have := hh1 _ _ _ hx; subst x
          obtain ⟨x, t₅, hx, hb⟩ := bind_ok_inv hb
          have := hh2 _ _ _ hx; subst x
          simp only [TypenameT.isConst, Bool.true_and]
          cases he2 : E2 i
          · simp only [he2, Bool.false_eq_true, if_false, Bool.false_or] at hb ⊢
            obtain ⟨x, t₆, hx, hb⟩ := bind_ok_inv hb
            have := h5 _ _ _ hx; subst x
            obtain ⟨x, t₇, hx, hb⟩ := bind_ok_inv hb
            have := h6 _ _ _ hx; subst x
            cases he3 : E3 i <;> simp only [he3, Bool.false_eq_true, if_false, if_true, Bool.or_false, Bool.or_true] at hb ⊢ <;> exact (pure_ok_inv hb).1
          · simp only [he2, if_true, Bool.true_or] at hb ⊢; exact (pure_ok_inv hb).1
        | bottom =>
          simp only [htn] at hb
          obtain ⟨x, t₆, hx, hb⟩ := bind_ok_inv hb
          have := h5 _ _ _ hx; subst x
          obtain ⟨x, t₇, hx, hb⟩ := bind_ok_inv hb
          have := h6 _ _ _ hx; subst x
          simp only [TypenameT.isConst, Bool.false_and, Bool.false_or]
          cases he3 : E3 i <;> simp only [he3, Bool.false_eq_true, if_false, if_true, Bool.or_false, Bool.or_true] at hb ⊢ <;> exact (pure_ok_inv hb).1
        | typeName =>
          simp only [htn] at hb
          obtain ⟨x, t₆, hx, hb⟩ := bind_ok_inv hb
          have := h5 _ _ _ hx; subst x
          obtain ⟨x, t₇, hx, hb⟩ := bind_ok_inv hb
          have := h6 _ _ _ hx; subst x
          simp only [TypenameT.isConst, Bool.false_and, Bool.false_or]
          cases he3 : E3 i <;> simp only [he3, Bool.false_eq_true, if_false, if_true, Bool.or_false, Bool.or_true] at hb ⊢ <;> exact (pure_ok_inv hb).1
      · simp only [he1, if_true, Bool.true_or] at hb ⊢; exact (pure_ok_inv hb).1) _ _ _ hst
  rw [this] at h
  show r = _
  cases hall : (List.range' 1 fs.length).all (fun i => E1 i || ((typenameT (W i)).isConst && E2 i) || E3 i) <;>
    simp only [hall, Bool.false_eq_true, if_false, if_true] at h <;> exact (pure_ok_inv h).1

end JuliaLean.Proofs.Compiler.src.typelimits
