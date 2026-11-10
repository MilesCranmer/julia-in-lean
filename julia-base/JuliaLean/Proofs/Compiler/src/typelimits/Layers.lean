import JuliaLean.Proofs.Compiler.src.typelimits.Spec

/-!
What each `tmerge` layer of `Compiler/src/typelimits.jl` returns beyond `Union{}`: the merges
of its own wrappers, and what it hands to the layer below.
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## `tmerge(::InferenceLattice)` -/

/-- `tmerge(::InferenceLattice, a, b)` (`Compiler/src/typelimits.jl:501-507`) hands two elements
that are not `LimitedAccuracy` to the layer below unchanged, and sends a `LimitedAccuracy` to
`tmerge_limited`: for `LimitedAccuracy(T, causes)` and an element `b` that is not `Union{}`, with
neither of `T` and `b` `⊑` the other, the answer is `LimitedAccuracy(tmerge(T, b), causes)`
(lines 476-498). -/
def TmergeInferenceDispatch : Prop :=
  (∀ p n E (a b : LElt) s, a.isLimited = false → b.isLimited = false →
    (tmerge (n + 1) E (.inference p) a b).run s = (tmerge n E p a b).run s) ∧
  (∀ p n E (T b m : LElt) cs cid, b.isLimited = false → b.isBottom = false → m.isLimited = false →
    Gives (sqsub n E (.inference p) T b) false → Gives (sqsub n E (.inference p) b T) false →
    Gives (tmerge n E p T b) m →
    Gives (tmerge (n + 1) E (.inference p) (.limitedAccuracy T cs cid) b) (.limitedAccuracy m cs cid))

theorem tmergeInferenceDispatch_proven : TmergeInferenceDispatch := by
  refine ⟨fun p n E a b s ha hb => ?_, fun p n E T b m cs cid hl hb hm hs1 hs2 hmg s r s' h => ?_⟩
  · simp only [tmerge, ha, hb, Bool.or_self, Bool.not_false, if_true]
  · have hT : (LElt.limitedAccuracy T cs cid).isLimited = true := rfl
    have hTb : (LElt.limitedAccuracy T cs cid).isBottom = false := rfl
    simp only [tmerge, hT, hTb, hb, hl, Bool.true_or, Bool.not_true, Bool.false_eq_true,
      if_false] at h
    split at h
    · rename_i heq; cases heq; simp [LElt.isLimited] at hl
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := hs1 _ _ _ hx; subst x
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨y, s₂, hy, h⟩ := bind_ok_inv h
    have := hs2 _ _ _ hy; subst y
    simp only [Bool.false_eq_true, if_false, Bool.and_false, Bool.and_self] at h
    obtain ⟨z, s₃, hz, h⟩ := bind_ok_inv h
    have := hmg _ _ _ hz; subst z
    simp only [mkLimitedAccuracy, hm, Bool.false_eq_true, if_false] at h
    exact (pure_ok_inv h).1

/-! ## `tmerge(::ConstsLattice)` -/

/-- `tmerge(::ConstsLattice, a, b)` (`Compiler/src/typelimits.jl:763-773`): unless both are
`Const`/`PartialTypeVar` and `a === b`, each `Const` or `PartialTypeVar` argument is widened to
its type and the pair is handed to `JLTypeLattice`; other arguments are handed on unchanged. So
two different `Const`s are merged as their types. -/
def TmergeConstsDispatch : Prop :=
  ∀ n E (a b wa wb : LElt),
    (((a.isConst || a.isPartialTypeVar) && (b.isConst || b.isPartialTypeVar)) = true →
      Gives (eltEgal n E a b) false) →
    ((a.isConst || a.isPartialTypeVar) = true → Gives (widenlatticeElt n E .jlType a) wa) →
    ((a.isConst || a.isPartialTypeVar) = false → wa = a) →
    ((b.isConst || b.isPartialTypeVar) = true → Gives (widenlatticeElt n E .jlType b) wb) →
    ((b.isConst || b.isPartialTypeVar) = false → wb = b) →
    Via (tmerge (n + 1) E .consts a b) (tmerge n E .jlType wa wb)

theorem tmergeConstsDispatch_proven : TmergeConstsDispatch := by
  intro n E a b wa wb he hwa hwa' hwb hwb' s r s' h
  simp only [tmerge] at h
  generalize hac : (a.isConst || a.isPartialTypeVar) = ac at *
  generalize hbc : (b.isConst || b.isPartialTypeVar) = bc at *
  have tail : ∀ s₀, (do
      let mut typea := a
      let mut typeb := b
      if ac then typea ← widenlatticeElt n E .jlType typea
      if bc then typeb ← widenlatticeElt n E .jlType typeb
      tmerge n E .jlType typea typeb : CM LElt).run s₀ = .ok (r, s') →
      ∃ s₁, (tmerge n E .jlType wa wb).run s₁ = .ok (r, s') := by
    intro s₀ h
    cases ac <;> cases bc <;> simp only [if_true, Bool.false_eq_true, if_false] at h
    · rw [hwa' rfl, hwb' rfl]; exact ⟨_, h⟩
    · obtain ⟨y, s₁, hy, h⟩ := bind_ok_inv h
      have := hwb rfl _ _ _ hy; subst y
      rw [hwa' rfl]; exact ⟨_, h⟩
    · obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
      have := hwa rfl _ _ _ hx; subst x
      rw [hwb' rfl]; exact ⟨_, h⟩
    · obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
      have := hwa rfl _ _ _ hx; subst x
      obtain ⟨y, s₂, hy, h⟩ := bind_ok_inv h
      have := hwb rfl _ _ _ hy; subst y
      exact ⟨_, h⟩
  cases ac <;> cases bc <;> simp only [Bool.and_true, Bool.and_false, Bool.false_eq_true,
    if_false, if_true] at h
  · exact tail _ h
  · exact tail _ h
  · exact tail _ h
  · obtain ⟨e, s₁, he', h⟩ := bind_ok_inv h
    have := he rfl _ _ _ he'; subst e
    simp only [Bool.false_eq_true, if_false] at h
    exact tail _ h

/-! ## `tmerge(::JLTypeLattice)` -/

/-- `tmerge(::JLTypeLattice, a, b)` (`Compiler/src/typelimits.jl:775-789`), given what
`isconcretetype` answers for each type:
* two equal concrete types: `a` itself;
* otherwise, when each is concrete or a `Type{T}`: `Union{a, b}`;
* otherwise, the `tmerge_fast_path` answer when it has one, else `tmerge_types_slow(a, b)`. -/
def TmergeJLTypeExact : Prop :=
  ∀ n E (ta tb : Val) (act bct : Bool), ta.isType = true → tb.isType = true →
    Gives (isconcretetype E ta) act → Gives (isconcretetype E tb) bct →
    ((act && bct && ta == tb) = true → Gives (tmerge (n + 1) E .jlType (.ty ta) (.ty tb)) (.ty ta)) ∧
    ((act && bct && ta == tb) = false → ((act || isType ta) && (bct || isType tb)) = true →
      ∀ u, Gives (jlUnion n E [ta, tb]) u → Gives (tmerge (n + 1) E .jlType (.ty ta) (.ty tb)) (.ty u)) ∧
    (((act || isType ta) && (bct || isType tb)) = false →
      ∀ o, Gives (tmergeFastPath n E .jlType (.ty ta) (.ty tb)) o →
      (∀ u, o = some u → Gives (tmerge (n + 1) E .jlType (.ty ta) (.ty tb)) u) ∧
      (o = none → ∀ v, Gives (tmergeTypesSlow n E ta tb) v →
        Gives (tmerge (n + 1) E .jlType (.ty ta) (.ty tb)) (.ty v)))

theorem tmergeJLTypeExact_proven : TmergeJLTypeExact := by
  intro n E ta tb act bct hta htb hca hcb
  have pre : ∀ s r s', (tmerge (n + 1) E .jlType (.ty ta) (.ty tb)).run s = .ok (r, s') →
      ∃ s₁, (do
        if act && bct then
          if ta == tb then return LElt.ty ta
        if (act || isType ta) && (bct || isType tb) then
          return .ty (← jlUnion n E [ta, tb])
        if let some u ← tmergeFastPath n E .jlType (.ty ta) (.ty tb) then return u
        return .ty (← tmergeTypesSlow n E ta tb) : CM LElt).run s₁ = .ok (r, s') := by
    intro s r s' h
    simp only [tmerge, hta, htb, Bool.not_true, Bool.or_self, Bool.false_eq_true, if_false] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := hca _ _ _ hx; subst x
    obtain ⟨y, s₂, hy, h⟩ := bind_ok_inv h
    have := hcb _ _ _ hy; subst y
    exact ⟨_, h⟩
  refine ⟨fun hc s r s' h => ?_, fun hc hu u hgu s r s' h => ?_, fun hu o ho => ⟨?_, ?_⟩⟩
  · obtain ⟨s₁, h⟩ := pre s r s' h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    simp only [h1, h2, h3, Bool.and_self, if_true] at h
    exact (pure_ok_inv h).1
  · obtain ⟨s₁, h⟩ := pre s r s' h
    have hnc' : (act && bct) = true → (ta == tb) = false := fun hab => by simpa [hab] using hc
    cases hab : (act && bct)
    all_goals try simp only [hab, Bool.false_eq_true, if_false] at h
    all_goals try simp only [hnc' hab, if_true, Bool.false_eq_true, if_false] at h
    all_goals
      simp only [hu, if_true] at h
      obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
      have := hgu _ _ _ hx; subst x
      exact (pure_ok_inv h).1
  · intro u hou s r s' h
    obtain ⟨s₁, h⟩ := pre s r s' h
    have hab : (act && bct) = false := by cases act <;> cases bct <;> simp_all
    simp only [hab, hu, Bool.false_eq_true, if_false] at h
    obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
    have := ho _ _ _ hx; subst x
    subst hou
    exact (pure_ok_inv h).1
  · intro hon v hv s r s' h
    obtain ⟨s₁, h⟩ := pre s r s' h
    have hab : (act && bct) = false := by cases act <;> cases bct <;> simp_all
    simp only [hab, hu, Bool.false_eq_true, if_false] at h
    obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
    have := ho _ _ _ hx; subst x
    subst hon
    obtain ⟨y, s₃, hy, h⟩ := bind_ok_inv h
    have := hv _ _ _ hy; subst y
    exact (pure_ok_inv h).1


/-! ## `tmerge(::InterConditionalsLattice)` -/

/-- `tmerge(::InterConditionalsLattice, a, b)` (`Compiler/src/typelimits.jl:549-587`):
* two `InterConditional`s on the same slot merge their then and else types in the layer below,
  and give `InterConditional(slot, then, else)` when those differ;
* on different slots the answer is `Const(v)` when both are known to be the same `Bool` `v`,
  else `Bool`;
* an `InterConditional` and an element that is neither an `InterConditional`, a `Const` nor
  `Union{}`: the `InterConditional` is widened (`widenconditional`) and the pair handed down;
* two elements that are not `InterConditional`s are handed down unchanged. -/
def TmergeInterConditionalsSpec : Prop :=
  (∀ p n E (a b : LElt) s, a.isInterConditional = false → b.isInterConditional = false →
    (tmerge (n + 1) E (.interConditionals p) a b).run s = (tmerge n E p a b).run s) ∧
  (∀ p n E sl (t1 e1 t2 e2 tt te : LElt), Gives (tmerge n E p t1 t2) tt →
    Gives (tmerge n E p e1 e2) te → Gives (eltEgal n E tt te) false →
    Gives (tmerge (n + 1) E (.interConditionals p) (.interConditional sl t1 e1) (.interConditional sl t2 e2))
      (.interConditional sl tt te)) ∧
  (∀ p n E s1 s2 (t1 e1 t2 e2 : LElt), s1 ≠ s2 →
    Gives (tmerge (n + 1) E (.interConditionals p) (.interConditional s1 t1 e1) (.interConditional s2 t2 e2))
      (match maybeExtractConstBool (.interConditional s1 t1 e1) with
       | some v => if some v == maybeExtractConstBool (.interConditional s2 t2 e2) then .const (boolVal v)
                   else .ty boolTy
       | none => .ty boolTy)) ∧
  (∀ p n E sl (t1 e1 b w : LElt), b.isInterConditional = false → b.isConst = false →
    b.isBottom = false → Gives (widenconditional (.interConditional sl t1 e1)) w →
    Via (tmerge (n + 1) E (.interConditionals p) (.interConditional sl t1 e1) b) (tmerge n E p w b))

theorem tmergeInterConditionalsSpec_proven : TmergeInterConditionalsSpec := by
  refine ⟨fun p n E a b s ha hb => ?_, fun p n E sl t1 e1 t2 e2 tt te ht he hne s r s' h => ?_,
    fun p n E s1 s2 t1 e1 t2 e2 hs s r s' h => ?_, fun p n E sl t1 e1 b w hb hc hbot hw s r s' h => ?_⟩
  · simp only [tmerge, isConditionalT, ha, hb, if_true, Bool.false_eq_true, if_false, Bool.and_false]
  · simp only [tmerge, isConditionalT, LElt.isInterConditional, if_true, Bool.and_self,
      isSameConditionals, beq_self_eq_true, pure_bind] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := ht _ _ _ hx; subst x
    obtain ⟨y, s₂, hy, h⟩ := bind_ok_inv h
    have := he _ _ _ hy; subst y
    obtain ⟨z, s₃, hz, h⟩ := bind_ok_inv h
    have := hne _ _ _ hz; subst z
    simp only [Bool.not_false, if_true] at h
    exact (pure_ok_inv h).1
  · have hne : (s1 == s2) = false := by simpa using hs
    simp only [tmerge, isConditionalT, LElt.isInterConditional, if_true, Bool.and_self,
      isSameConditionals, hne, pure_bind, Bool.false_eq_true, if_false] at h
    show r = _
    cases hm : maybeExtractConstBool (LElt.interConditional s1 t1 e1) with
    | none => simp only [hm] at h; exact (pure_ok_inv h).1
    | some v =>
      simp only [hm] at h ⊢
      by_cases hc : (some v == maybeExtractConstBool (LElt.interConditional s2 t2 e2)) = true
      · simp only [hc, if_true] at h ⊢; exact (pure_ok_inv h).1
      · simp only [hc, if_false, Bool.false_eq_true] at h ⊢; exact (pure_ok_inv h).1
  · have hai : (LElt.interConditional sl t1 e1).isInterConditional = true := rfl
    have hab : (LElt.interConditional sl t1 e1).isBottom = false := rfl
    simp only [tmerge, isConditionalT, hai, hb, hbot, if_true, Bool.false_eq_true,
      if_false, Bool.and_false, Bool.true_and] at h
    split at h
    · simp [LElt.isConst] at hc
    · try simp only [hb, hbot, Bool.and_false, Bool.false_eq_true, if_false, if_true] at h
      obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
      have := hw _ _ _ hx; subst x
      exact ⟨_, h⟩

/-! ## `tmerge(::AnyMustAliasesLattice)` -/

/-- `tmerge(::AnyMustAliasesLattice, a, b)` (`Compiler/src/typelimits.jl:589-607`), on
`MustAliasesLattice`:
* two `MustAlias`es of the same slot and field whose `vartyp`s widen to the same type keep the
  alias, with `vartyp` and `fldtyp` merged in the layer below (`update_mustalias`);
* a `MustAlias` and an element that is neither a `MustAlias` nor `Union{}`: the alias is widened
  to its `fldtyp` and the pair handed down;
* two elements that are not `MustAlias`es are handed down unchanged.
The same holds for `InterMustAlias` on `InterMustAliasesLattice`. -/
def TmergeMustAliasesSpec : Prop :=
  (∀ p n E (a b : LElt) s, a.isMustAlias = false → b.isMustAlias = false →
    (tmerge (n + 1) E (.mustAliases p) a b).run s = (tmerge n E p a b).run s) ∧
  (∀ p n E sl d i (v1 f1 v2 f2 v f : LElt) (w1 w2 : Val), Gives (widenconst n E v1) w1 →
    Gives (widenconst n E v2) w2 → Gives (JuliaLean.Compiler.egal n E w1 w2) true →
    Gives (tmerge n E p v1 v2) v → Gives (tmerge n E p f1 f2) f →
    Via (tmerge (n + 1) E (.mustAliases p) (.mustAlias sl d v1 i f1) (.mustAlias sl d v2 i f2))
      (updateMustalias (.mustAlias sl d v1 i f1) (some v) (some f))) ∧
  (∀ p n E sl d i (v1 f1 b : LElt), b.isMustAlias = false → b.isBottom = false →
    Via (tmerge (n + 1) E (.mustAliases p) (.mustAlias sl d v1 i f1) b) (tmerge n E p f1 b)) ∧
  (∀ p n E (a b : LElt) s, a.isInterMustAlias = false → b.isInterMustAlias = false →
    (tmerge (n + 1) E (.interMustAliases p) a b).run s = (tmerge n E p a b).run s) ∧
  (∀ p n E sl i (v1 f1 v2 f2 v f : LElt) (w1 w2 : Val), Gives (widenconst n E v1) w1 →
    Gives (widenconst n E v2) w2 → Gives (JuliaLean.Compiler.egal n E w1 w2) true →
    Gives (tmerge n E p v1 v2) v → Gives (tmerge n E p f1 f2) f →
    Gives (tmerge (n + 1) E (.interMustAliases p) (.interMustAlias sl v1 i f1) (.interMustAlias sl v2 i f2))
      (.interMustAlias sl v i f))

theorem tmergeMustAliasesSpec_proven : TmergeMustAliasesSpec := by
  refine ⟨fun p n E a b s ha hb => ?_, fun p n E sl d i v1 f1 v2 f2 v f w1 w2 h1 h2 he hv hf s r s' h => ?_,
    fun p n E sl d i v1 f1 b hb hbot s r s' h => ?_, fun p n E a b s ha hb => ?_,
    fun p n E sl i v1 f1 v2 f2 v f w1 w2 h1 h2 he hv hf s r s' h => ?_⟩
  · simp only [tmerge, isValidLatticeNorec, ha, hb, Bool.false_eq_true, if_false]
  · simp only [tmerge, isValidLatticeNorec, LElt.isMustAlias, LElt.isBottom, isSameAlias,
      beq_self_eq_true, Bool.and_self, if_true, Bool.false_eq_true, if_false] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := h1 _ _ _ hx; subst x
    obtain ⟨y, s₂, hy, h⟩ := bind_ok_inv h
    have := h2 _ _ _ hy; subst y
    obtain ⟨z, s₃, hz, h⟩ := bind_ok_inv h
    have := he _ _ _ hz; subst z
    simp only [if_true] at h
    obtain ⟨x, s₄, hx, h⟩ := bind_ok_inv h
    have := hv _ _ _ hx; subst x
    obtain ⟨y, s₅, hy, h⟩ := bind_ok_inv h
    have := hf _ _ _ hy; subst y
    exact ⟨_, h⟩
  · have hA : (LElt.mustAlias sl d v1 i f1).isMustAlias = true := rfl
    simp only [tmerge, isValidLatticeNorec, hA, hb, hbot, if_true, Bool.false_eq_true,
      if_false, Bool.false_and, widenmustalias, pure_bind] at h
    exact ⟨_, h⟩
  · simp only [tmerge, isValidLatticeNorec, ha, hb, Bool.false_eq_true, if_false]
  · simp only [tmerge, isValidLatticeNorec, LElt.isInterMustAlias, LElt.isBottom, isSameAlias,
      beq_self_eq_true, Bool.and_self, if_true, Bool.false_eq_true, if_false] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := h1 _ _ _ hx; subst x
    obtain ⟨y, s₂, hy, h⟩ := bind_ok_inv h
    have := h2 _ _ _ hy; subst y
    obtain ⟨z, s₃, hz, h⟩ := bind_ok_inv h
    have := he _ _ _ hz; subst z
    simp only [if_true] at h
    obtain ⟨x, s₄, hx, h⟩ := bind_ok_inv h
    have := hv _ _ _ hx; subst x
    obtain ⟨y, s₅, hy, h⟩ := bind_ok_inv h
    have := hf _ _ _ hy; subst y
    simp only [updateMustalias, Option.getD_some] at h
    exact (pure_ok_inv h).1

/-! ## `tmerge(::PartialsLattice)` -/

/-- `tmerge(::PartialsLattice, a, b)` (`Compiler/src/typelimits.jl:702-761`) when
`tmerge_fast_path` has no answer:
* two `PartialStruct`s or `Const`s that are not `===`: the `tmerge_partial_struct` answer, when it
  has one;
* two `PartialOpaque`s of the same type: `PartialOpaque(typ, tmerge(env_a, env_b), parent,
  source)` when the sources and parents are the same objects, else the type itself;
* two `PartialTask`s: `PartialTask(tmerge(fetch_a, fetch_b))`, or `Task` when that merge is
  `Any`;
* two elements that are none of `PartialStruct`, `Const`, `PartialOpaque`, `PartialTask`: handed
  to the layer below unchanged. -/
def TmergePartialsSpec : Prop :=
  (∀ wl n E (a b r : LElt), (a.isPartialStruct || a.isConst) = true →
    (b.isPartialStruct || b.isConst) = true → Gives (tmergeFastPath n E (.partials wl) a b) none →
    Gives (eltEgal n E a b) false → Gives (tmergePartialStruct n E (.partials wl) a b) (some r) →
    Gives (tmerge (n + 1) E (.partials wl) a b) r) ∧
  (∀ wl n E t1 t2 e1 e2 p1 p2 r1 r2 (env : LElt),
    Gives (tmergeFastPath n E (.partials wl) (.partialOpaque t1 e1 p1 r1) (.partialOpaque t2 e2 p2 r2)) none →
    Gives (tyEq n E t1 t2) true → Gives (tmerge n E (.partials wl) e1 e2) env →
    Gives (tmerge (n + 1) E (.partials wl) (.partialOpaque t1 e1 p1 r1) (.partialOpaque t2 e2 p2 r2))
      (if r1 == r2 && p1 == p2 then .partialOpaque t1 env p1 r1 else .ty t1)) ∧
  (∀ wl n E (f1 f2 m : LElt),
    Gives (tmergeFastPath n E (.partials wl) (.partialTask f1) (.partialTask f2)) none →
    Gives (tmerge n E (.partials wl) f1 f2) m →
    Gives (tmerge (n + 1) E (.partials wl) (.partialTask f1) (.partialTask f2))
      (if m.isAny then .ty taskType else .partialTask m)) ∧
  (∀ wl n E (a b : LElt), a.isPartialStruct = false → a.isConst = false →
    a.isPartialOpaque = false → a.isPartialTask = false → b.isPartialStruct = false →
    b.isConst = false → b.isPartialOpaque = false → b.isPartialTask = false →
    Gives (tmergeFastPath n E (.partials wl) a b) none →
    Via (tmerge (n + 1) E (.partials wl) a b) (tmerge n E wl a b))

theorem tmergePartialsSpec_proven : TmergePartialsSpec := by
  refine ⟨fun wl n E a b r ha hb hf he hp s r' s' h => ?_,
    fun wl n E t1 t2 e1 e2 p1 p2 r1 r2 env hf ht he s r s' h => ?_,
    fun wl n E f1 f2 m hf hm s r s' h => ?_,
    fun wl n E a b h1 h2 h3 h4 h5 h6 h7 h8 hf s r s' h => ?_⟩
  · simp only [tmerge] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := hf _ _ _ hx; subst x
    simp only [ha, hb, Bool.and_self, if_true] at h
    obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
    have := he _ _ _ hx; subst x
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨x, s₃, hx, h⟩ := bind_ok_inv h
    have := hp _ _ _ hx; subst x
    exact (pure_ok_inv h).1
  · simp only [tmerge] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := hf _ _ _ hx; subst x
    simp only [LElt.isPartialStruct, LElt.isConst, Bool.or_self, Bool.false_and, Bool.false_eq_true,
      if_false] at h
    obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
    have := ht _ _ _ hx; subst x
    simp only [if_true] at h
    show r = _
    by_cases hc : (r1 == r2 && p1 == p2) = true
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false, if_true] at h ⊢
      obtain ⟨x, s₃, hx, h⟩ := bind_ok_inv h
      have := he _ _ _ hx; subst x
      exact (pure_ok_inv h).1
    · simp only [hc, Bool.not_false, Bool.false_eq_true, if_false, if_true] at h ⊢
      exact (pure_ok_inv h).1
  · simp only [tmerge] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := hf _ _ _ hx; subst x
    simp only [LElt.isPartialStruct, LElt.isConst, Bool.or_self, Bool.false_and, Bool.false_eq_true,
      if_false] at h
    obtain ⟨x, s₂, hx, h⟩ := bind_ok_inv h
    have := hm _ _ _ hx; subst x
    show r = _
    by_cases hc : m.isAny = true
    · simp only [hc, if_true] at h ⊢; exact (pure_ok_inv h).1
    · simp only [hc, Bool.false_eq_true, if_false] at h ⊢; exact (pure_ok_inv h).1
  · simp only [tmerge] at h
    obtain ⟨x, s₁, hx, h⟩ := bind_ok_inv h
    have := hf _ _ _ hx; subst x
    simp only [h1, h2, h5, h6, Bool.or_self, Bool.false_and, Bool.false_eq_true, if_false] at h
    repeat' (split at h)
    all_goals first
      | exact ⟨_, h⟩
      | (simp only [LElt.isPartialOpaque, LElt.isPartialTask, Bool.true_eq_false] at h3 h4 h7 h8)

end JuliaLean.Proofs.Compiler.src.typelimits
