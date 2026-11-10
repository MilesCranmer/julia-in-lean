import JuliaLean.Proofs.Compiler.src.typelattice.Common

/-!
Properties of the lattice-element constructors, `LimitedAccuracy` and the slot wrappers of
`Compiler/src/typelattice.jl`.
-/

namespace JuliaLean.Proofs.Compiler.src.typelattice

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## `LimitedAccuracy` -/

/-- `LimitedAccuracy(T, nothing)` is `T` itself; `LimitedAccuracy(T, causes)` never nests a
`LimitedAccuracy` in another (it is an `AssertionError`) and otherwise wraps `T` with exactly the
given causes. -/
def LimitedAccuracyCtorSpec : Prop :=
  (∀ typ s, (mkLimitedAccuracy typ none).run s = .ok (typ, s)) ∧
  (∀ typ cs cid, typ.isLimited = true →
    ThrowsJulia "AssertionError" (mkLimitedAccuracy typ (some (cs, cid)))) ∧
  (∀ typ cs cid s, typ.isLimited = false →
    (mkLimitedAccuracy typ (some (cs, cid))).run s = .ok (.limitedAccuracy typ cs cid, s))

theorem mkLimitedAccuracy_some {typ : LElt} {cs : List ObjId} {cid s : Nat}
    (h : typ.isLimited = false) :
    (mkLimitedAccuracy typ (some (cs, cid))).run s = .ok (.limitedAccuracy typ cs cid, s) := by
  cases typ <;> first | rfl | (simp [LElt.isLimited] at h)

theorem limitedAccuracyCtorSpec_proven : LimitedAccuracyCtorSpec := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ _ _ h => mkLimitedAccuracy_some h⟩
  intro typ cs cid h s
  cases typ <;> first | exact ⟨"found nested LimitedAccuracy", rfl⟩ | (simp [LElt.isLimited] at h)

/-! ## `narrow_limited_typ` -/

/-- The comment at `Compiler/src/typelattice.jl:12-13`: "If `y` is limited, return `x` limited by
the causes of `y` (and of `x`, if any). Otherwise return `x` unchanged." The result is limited
around `x` itself, or around `x.typ` when `x` is already limited (no nesting). Its causes are
exactly those of `x` and of `y`, held in a new `IdSet`: the result's set is the object the
`copy` allocates (the next fresh object id `s`), never `x.causes` or `y.causes` themselves, so
`union!` does not change the set of `x` or `y`. -/
def NarrowLimitedTypSpec : Prop :=
  ∀ x y, (x.isLimited = true → (ignorelimited x).isLimited = false) →
    ∀ s r s', (narrowLimitedTyp x y).run s = .ok (r, s') →
      (y.isLimited = false → r = x ∧ s' = s) ∧
      (y.isLimited = true → s' = s + 1 ∧ ∃ cs, r = .limitedAccuracy (ignorelimited x) cs s ∧
        ∀ c, c ∈ cs ↔ c ∈ limitedCauses x ∨ c ∈ limitedCauses y)

theorem narrowLimitedTypSpec_proven : NarrowLimitedTypSpec := by
  intro x y hx s r s' h
  cases y
  case limitedAccuracy yt yc yid =>
    refine ⟨fun h => (by cases h), fun _ => ?_⟩
    cases x
    case limitedAccuracy xt xc xid =>
      have hxt : xt.isLimited = false := hx rfl
      have e : (narrowLimitedTyp (.limitedAccuracy xt xc xid) (.limitedAccuracy yt yc yid)).run s =
          .ok (.limitedAccuracy xt (idsetUnion xc yc) s, s + 1) := by
        show (do let (c, cid) ← copyIdSet xc
                 mkLimitedAccuracy xt (some (idsetUnion c yc, cid)) : CM LElt).run s = _
        rw [run_bind_ok (rfl : (copyIdSet xc).run s = .ok ((xc, s), s + 1))]
        exact mkLimitedAccuracy_some hxt
      rw [e] at h; cases h
      exact ⟨rfl, _, rfl, fun c => idsetUnion_mem xc yc c⟩
    all_goals (cases h; exact ⟨rfl, _, rfl, fun c => by simp [limitedCauses]⟩)
  all_goals (cases h; exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => (by cases h)⟩)

/-- The limited result of `narrow_limited_typ(f, v)` when either is limited: `f` (or `f.typ`)
limited by exactly the causes of `v` and of `f`. -/
theorem narrow_fv_limited {f v : LElt} {s : Nat} {l : LElt} {s₂ : Nat}
    (hf : f.isLimited = true → (ignorelimited f).isLimited = false)
    (hl : (v.isLimited || f.isLimited) = true)
    (hn : (narrowLimitedTyp f v).run s = .ok (l, s₂)) :
    ∃ cs cid, l = .limitedAccuracy (ignorelimited f) cs cid ∧
      ∀ c, c ∈ cs ↔ c ∈ limitedCauses v ∨ c ∈ limitedCauses f := by
  have spec := narrowLimitedTypSpec_proven f v hf s l s₂ hn
  cases hv : v.isLimited
  · have hfl : f.isLimited = true := by simpa [hv] using hl
    have hlf : l = f := (spec.1 hv).1
    rw [hlf]
    have hv0 : limitedCauses v = [] := by
      cases v <;> simp_all [limitedCauses, LElt.isLimited]
    cases f
    case limitedAccuracy ft fc fid =>
      exact ⟨fc, fid, rfl, fun c => by rw [hv0]; simp [limitedCauses]⟩
    all_goals simp [LElt.isLimited] at hfl
  · obtain ⟨_, cs, hl', hcs⟩ := spec.2 hv
    exact ⟨cs, s, hl', fun c => (hcs c).trans or_comm⟩

/-! ## `assert_nested_slotwrapper` -/

/-- `assert_nested_slotwrapper(t)` returns `t` unchanged when it is not a slot wrapper and is an
`AssertionError` when it is one. -/
def AssertNestedSlotwrapperSpec : Prop :=
  ∀ t, (t.isSlotWrapper = false → ∀ s, (assertNestedSlotwrapper t).run s = .ok (t, s)) ∧
    (t.isSlotWrapper = true → ThrowsJulia "AssertionError" (assertNestedSlotwrapper t))

theorem assertNestedSlotwrapperSpec_proven : AssertNestedSlotwrapperSpec := by
  intro t
  cases t <;> refine ⟨fun h s => ?_, fun h s => ?_⟩ <;>
    first
    | rfl
    | exact ⟨_, rfl⟩
    | (simp [LElt.isSlotWrapper, LElt.isAnyConditional, LElt.isAnyMustAlias, LElt.isConditional,
        LElt.isInterConditional, LElt.isMustAlias, LElt.isInterMustAlias] at h)

/-! ## `Conditional` and `MustAlias` constructors -/

/-- `Conditional(slot, ssadef, thentype, elsetype; isdefined)` never builds a `Conditional` around
a slot wrapper (`AssertionError`) or around a `LimitedAccuracy`: with neither, it is the plain
struct; when either branch type is limited, the result is `LimitedAccuracy(Bool)` with exactly
the causes of the two branch types. -/
def ConditionalCtorSpec : Prop :=
  ∀ slot d t e isdef,
    ((t.isSlotWrapper || e.isSlotWrapper) = true →
      ThrowsJulia "AssertionError" (mkConditional slot d t e isdef)) ∧
    ((t.isSlotWrapper || e.isSlotWrapper) = false → (t.isLimited || e.isLimited) = false →
      ∀ s, (mkConditional slot d t e isdef).run s = .ok (.conditional slot d t e isdef, s)) ∧
    ((t.isSlotWrapper || e.isSlotWrapper) = false → (t.isLimited || e.isLimited) = true →
      Returns (mkConditional slot d t e isdef) fun r => ∃ cs cid,
        r = .limitedAccuracy (.ty boolTy) cs cid ∧
        ∀ c, c ∈ cs ↔ c ∈ limitedCauses t ∨ c ∈ limitedCauses e)

theorem conditionalCtorSpec_proven : ConditionalCtorSpec := by
  intro slot d t e isdef
  refine ⟨?_, ?_, ?_⟩
  · intro h s
    cases t <;> cases e <;>
      first
      | exact ⟨_, rfl⟩
      | (simp [LElt.isSlotWrapper, LElt.isAnyConditional, LElt.isAnyMustAlias,
          LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
          LElt.isInterMustAlias] at h)
  · intro h₁ h₂ s
    cases t <;> cases e <;>
      first
      | rfl
      | (simp [LElt.isSlotWrapper, LElt.isAnyConditional, LElt.isAnyMustAlias,
          LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
          LElt.isInterMustAlias, LElt.isLimited] at h₁ h₂)
  · intro h₁ h₂ s r s' h
    cases t <;> cases e <;>
      first
      | (cases h
         exact ⟨_, _, rfl, fun c => by simp [limitedCauses, idsetUnion_mem, or_comm]⟩)
      | (simp [LElt.isSlotWrapper, LElt.isAnyConditional, LElt.isAnyMustAlias,
          LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
          LElt.isInterMustAlias, LElt.isLimited] at h₁ h₂)

/-- `MustAlias(slot, ssadef, vartyp, fldidx, fldtyp)` never builds an alias around a slot wrapper
(`AssertionError`) or a `LimitedAccuracy`: with neither, it is the plain struct; when either type
is limited, the result is the field type, limited by exactly the causes of the two types. -/
def MustAliasCtorSpec : Prop :=
  ∀ slot d v i f,
    ((v.isSlotWrapper || f.isSlotWrapper) = true →
      ThrowsJulia "AssertionError" (mkMustAlias slot d v i f)) ∧
    ((v.isSlotWrapper || f.isSlotWrapper) = false → (v.isLimited || f.isLimited) = false →
      ∀ s, (mkMustAlias slot d v i f).run s = .ok (.mustAlias slot d v i f, s)) ∧
    ((v.isSlotWrapper || f.isSlotWrapper) = false → (v.isLimited || f.isLimited) = true →
      (f.isLimited = true → (ignorelimited f).isLimited = false) →
      Returns (mkMustAlias slot d v i f) fun r => ∃ cs cid,
        r = .limitedAccuracy (ignorelimited f) cs cid ∧
        ∀ c, c ∈ cs ↔ c ∈ limitedCauses v ∨ c ∈ limitedCauses f)

theorem assert_ok {t : LElt} {s : Nat} (h : t.isSlotWrapper = false) :
    (assertNestedSlotwrapper t).run s = .ok (t, s) :=
  (assertNestedSlotwrapperSpec_proven t).1 h s

theorem mustAliasCtorSpec_proven : MustAliasCtorSpec := by
  intro slot d v i f
  refine ⟨?_, ?_, ?_⟩
  · intro h s
    cases v <;> cases f <;>
      first
      | exact ⟨_, rfl⟩
      | (simp [LElt.isSlotWrapper, LElt.isAnyConditional, LElt.isAnyMustAlias,
          LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
          LElt.isInterMustAlias] at h)
  · intro h₁ h₂ s
    cases v <;> cases f <;>
      first
      | rfl
      | (simp [LElt.isSlotWrapper, LElt.isAnyConditional, LElt.isAnyMustAlias,
          LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
          LElt.isInterMustAlias, LElt.isLimited] at h₁ h₂)
  · intro h₁ h₂ hf s r s' h
    simp only [Bool.or_eq_false_iff] at h₁
    unfold mkMustAlias at h
    rw [run_bind_ok (assert_ok h₁.1), run_bind_ok (assert_ok h₁.2)] at h
    obtain ⟨l, s₂, hn, hk⟩ := run_bind_inv h
    obtain ⟨cs, cid, hlr, hcs⟩ := narrow_fv_limited hf h₂ hn
    subst hlr
    cases hk
    exact ⟨cs, cid, rfl, hcs⟩

/-- `InterConditional(cnd::Conditional)` asserts `ssadef == 0` and keeps the slot and both branch
types, so the conversion preserves what the conditional says about its value. -/
def InterConditionalOfSpec : Prop :=
  ∀ slot d t e isdef,
    (d ≠ 0 → ThrowsJulia "AssertionError" (interConditionalOf (.conditional slot d t e isdef))) ∧
    (d = 0 → ∀ s, (interConditionalOf (.conditional slot d t e isdef)).run s =
        .ok (.interConditional slot t e, s) ∧
      maybeExtractConstBool (.interConditional slot t e) =
        maybeExtractConstBool (.conditional slot d t e isdef) ∧
      (widenconditional (.interConditional slot t e)).run s =
        (widenconditional (.conditional slot d t e isdef)).run s)

theorem interConditionalOfSpec_proven : InterConditionalOfSpec := by
  intro slot d t e isdef
  refine ⟨fun hd s => ⟨"cnd.ssadef == 0", ?_⟩, fun hd s => ⟨?_, rfl, rfl⟩⟩
  · show (if (d != 0) = true then jlThrow "AssertionError" "cnd.ssadef == 0"
          else pure (LElt.interConditional slot t e) : CM LElt).run s = _
    have : (d != 0) = true := by simpa using hd
    rw [if_pos this]; rfl
  · subst hd; rfl

/-- `InterMustAlias(alias::MustAlias)` asserts `ssadef == 0`; it keeps the slot, field index and
both types, unless one of them is limited, in which case it is the limited field type. Without
limits, the field type it widens to is unchanged. When either type is limited, the result is the
field type limited by exactly the causes of the two types, as in the `MustAlias` constructor. -/
def InterMustAliasOfSpec : Prop :=
  ∀ slot d v i f,
    (d ≠ 0 → ThrowsJulia "AssertionError" (interMustAliasOf (.mustAlias slot d v i f))) ∧
    (d = 0 → (v.isLimited || f.isLimited) = false → ∀ s,
      (interMustAliasOf (.mustAlias slot d v i f)).run s = .ok (.interMustAlias slot v i f, s) ∧
      (widenmustalias (.interMustAlias slot v i f)).run s =
        (widenmustalias (.mustAlias slot d v i f)).run s) ∧
    (d = 0 → (v.isLimited || f.isLimited) = true →
      (f.isLimited = true → (ignorelimited f).isLimited = false) →
      Returns (interMustAliasOf (.mustAlias slot d v i f)) fun r => ∃ cs cid,
        r = .limitedAccuracy (ignorelimited f) cs cid ∧
        ∀ c, c ∈ cs ↔ c ∈ limitedCauses v ∨ c ∈ limitedCauses f)

theorem interMustAliasOfSpec_proven : InterMustAliasOfSpec := by
  intro slot d v i f
  refine ⟨fun hd s => ⟨"alias.ssadef == 0", ?_⟩, fun hd hl s => ⟨?_, rfl⟩, ?_⟩
  · show (if (d != 0) = true then jlThrow "AssertionError" "alias.ssadef == 0" else _ : CM LElt).run s = _
    have : (d != 0) = true := by simpa using hd
    rw [if_pos this]; rfl
  · subst hd
    cases v <;> cases f <;> first | rfl | (simp [LElt.isLimited] at hl)
  · intro hd hl hf s r s' h
    subst hd
    have h' : (narrowLimitedTyp f v >>= fun limited =>
        if limited.isLimited = true then pure limited
        else (pure (LElt.interMustAlias slot v i f) : CM LElt)).run s = .ok (r, s') := h
    obtain ⟨l, s₂, hn, hk⟩ := run_bind_inv h'
    obtain ⟨cs, cid, hlr, hcs⟩ := narrow_fv_limited hf hl hn
    subst hlr
    cases hk
    exact ⟨cs, cid, rfl, hcs⟩

/-- `update_mustalias(alias; vartyp, fldtyp)` (comment at `Compiler/src/typelattice.jl:117`):
"Return an alias of the same field as `alias`, with `vartyp` and `fldtyp` replaced." For an
`InterMustAlias`, and for a `MustAlias` whose new types are neither slot wrappers nor limited, the
result is an alias of the same field (`is_same_alias`) holding the new types. For a `MustAlias`,
the new types go through the validating constructor: a new slot-wrapper type is an
`AssertionError`, and a new limited type gives the field type limited by exactly the causes of the
two new types. -/
def UpdateMustaliasSpec : Prop :=
  (∀ slot d v i f v' f',
    ((v'.getD v).isSlotWrapper || (f'.getD f).isSlotWrapper) = true →
    ThrowsJulia "AssertionError" (updateMustalias (.mustAlias slot d v i f) v' f')) ∧
  (∀ slot d v i f v' f',
    ((v'.getD v).isSlotWrapper || (f'.getD f).isSlotWrapper) = false →
    ((v'.getD v).isLimited || (f'.getD f).isLimited) = true →
    ((f'.getD f).isLimited = true → (ignorelimited (f'.getD f)).isLimited = false) →
    Returns (updateMustalias (.mustAlias slot d v i f) v' f') fun r => ∃ cs cid,
      r = .limitedAccuracy (ignorelimited (f'.getD f)) cs cid ∧
      ∀ c, c ∈ cs ↔ c ∈ limitedCauses (v'.getD v) ∨ c ∈ limitedCauses (f'.getD f)) ∧
  (∀ slot v i f v' f' s,
    (updateMustalias (.interMustAlias slot v i f) v' f').run s =
      .ok (.interMustAlias slot (v'.getD v) i (f'.getD f), s) ∧
    isSameAlias (.interMustAlias slot v i f) (.interMustAlias slot (v'.getD v) i (f'.getD f)) = true) ∧
  (∀ slot d v i f v' f' s,
    ((v'.getD v).isSlotWrapper || (f'.getD f).isSlotWrapper) = false →
    ((v'.getD v).isLimited || (f'.getD f).isLimited) = false →
    (updateMustalias (.mustAlias slot d v i f) v' f').run s =
      .ok (.mustAlias slot d (v'.getD v) i (f'.getD f), s) ∧
    isSameAlias (.mustAlias slot d v i f) (.mustAlias slot d (v'.getD v) i (f'.getD f)) = true)

theorem updateMustaliasSpec_proven : UpdateMustaliasSpec := by
  refine ⟨fun slot d v i f v' f' h => (mustAliasCtorSpec_proven slot d _ i _).1 h,
    fun slot d v i f v' f' h₁ h₂ hf => (mustAliasCtorSpec_proven slot d _ i _).2.2 h₁ h₂ hf,
    fun slot v i f v' f' s => ⟨rfl, by simp [isSameAlias]⟩, ?_⟩
  intro slot d v i f v' f' s h₁ h₂
  exact ⟨(mustAliasCtorSpec_proven slot d _ i _).2.1 h₁ h₂ s, by simp [isSameAlias]⟩

/-! ## Widening slot wrappers -/

/-- Widening a slot wrapper does not change the type it widens to:
`widenconst(widenslotwrapper(x)) == widenconst(x)` for every `Conditional`, `InterConditional`,
`MustAlias` and `InterMustAlias` (`widenconst(::AnyConditional) = Bool`,
`widenconst(a::AnyMustAlias) = widenconst(widenmustalias(a))`). The fuel of the left side is one
step more than the right because `widenconst` of an alias recurses once. -/
def WidenslotwrapperKeepsWidenconst : Prop :=
  ∀ n E x s, 1 ≤ n → x.isSlotWrapper = true →
    (widenconst (n + 1) E x).run s = (widenslotwrapper x >>= widenconst n E).run s

theorem widenconditional_bool (c : LElt) (s : Nat) (hc : c.isAnyConditional = true) :
    ∃ w, (widenconditional c).run s = .ok (w, s) ∧
      (w = .const (boolVal false) ∨ w = .const (boolVal true) ∨ w = .ty boolTy) := by
  cases c
  case conditional slot d t e isdef =>
    simp only [widenconditional]
    split <;> exact ⟨_, rfl, by simp⟩
  case interConditional slot t e =>
    simp only [widenconditional]
    split <;> exact ⟨_, rfl, by simp⟩
  all_goals simp [LElt.isAnyConditional, LElt.isConditional, LElt.isInterConditional] at hc

theorem widenslotwrapper_cond (c : LElt) (s : Nat) (hc : c.isAnyConditional = true) :
    (widenslotwrapper c).run s = (widenconditional c).run s := by
  obtain ⟨w, hw, _⟩ := widenconditional_bool c s hc
  unfold widenslotwrapper
  rw [if_pos hc]

theorem widenslotwrapperKeepsWidenconst_proven : WidenslotwrapperKeepsWidenconst := by
  intro n E x s hn hx
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hc : x.isAnyConditional = true
  · obtain ⟨w, hw, hw3⟩ := widenconditional_bool x s hc
    have hs : (widenslotwrapper x).run s = .ok (w, s) := by rw [widenslotwrapper_cond x s hc, hw]
    rw [run_bind_ok hs]
    cases x <;> simp [LElt.isAnyConditional, LElt.isConditional, LElt.isInterConditional] at hc <;>
      rcases hw3 with rfl | rfl | rfl <;> rfl
  · cases x
    case mustAlias => rfl
    case interMustAlias => rfl
    all_goals simp [LElt.isSlotWrapper, LElt.isAnyConditional, LElt.isAnyMustAlias,
      LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias, LElt.isInterMustAlias] at hx hc

/-- `widenslotwrapper` leaves every element that is not a slot wrapper unchanged, and removes the
slot wrapper from every alias whose field type is not itself a slot wrapper (which the `MustAlias`
constructor asserts). -/
def WidenslotwrapperUnwraps : Prop :=
  ∀ x s, (x.isSlotWrapper = false → (widenslotwrapper x).run s = .ok (x, s)) ∧
    ((match x with | .mustAlias _ _ _ _ f | .interMustAlias _ _ _ f => f.isSlotWrapper
                   | _ => false) = false →
      Returns (widenslotwrapper x) fun r => r.isSlotWrapper = false)

theorem widenslotwrapperUnwraps_proven : WidenslotwrapperUnwraps := by
  intro x s
  refine ⟨fun h => ?_, fun h s r s' hr => ?_⟩
  · cases x <;> first | rfl | (simp [LElt.isSlotWrapper, LElt.isAnyConditional,
      LElt.isAnyMustAlias, LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
      LElt.isInterMustAlias] at h)
  · by_cases hc : x.isAnyConditional = true
    · obtain ⟨w, hw, hw3⟩ := widenconditional_bool x s hc
      rw [widenslotwrapper_cond x s hc, hw] at hr
      cases hr
      rcases hw3 with rfl | rfl | rfl <;> rfl
    · cases x
      case mustAlias => cases hr; exact h
      case interMustAlias => cases hr; exact h
      all_goals first | (cases hr; rfl) | (simp [LElt.isAnyConditional, LElt.isConditional,
        LElt.isInterConditional] at hc)

/-- `widenconditional(c)` is `Const(b)` exactly when `maybe_extract_const_bool(c) === b`, and
`Bool` otherwise (both read the same two branch types, `Compiler/src/typelattice.jl:242-255` and
`288-292`). -/
def WidenconditionalAgreesExtract : Prop :=
  ∀ c s, c.isAnyConditional = true →
    (widenconditional c).run s =
      .ok ((match maybeExtractConstBool c with
            | some b => .const (boolVal b)
            | none => .ty boolTy), s)

/-- `Conditional(1, 0, Union{}, Union{})`. -/
def condBotBot : LElt := .conditional 1 0 (.ty .bottom) (.ty .bottom) false

/-- Counterexample: for `Conditional(1, 0, Union{}, Union{})`, `widenconditional` is
`Const(false)` but `maybe_extract_const_bool` is `nothing`. -/
theorem widenconditionalAgreesExtract_refuted : ¬ WidenconditionalAgreesExtract := by
  intro h
  have := h condBotBot 0 rfl
  cases this

/-- The same agreement for every conditional whose branches are not both `Union{}` (a
conditional with two impossible branches is itself unreachable). -/
def WidenconditionalAgreesExtractReachable : Prop :=
  ∀ c s, c.isAnyConditional = true →
    (match c with
     | .conditional _ _ t e _ | .interConditional _ t e => !(t.isBottom && e.isBottom)
     | _ => false) = true →
    (widenconditional c).run s =
      .ok ((match maybeExtractConstBool c with
            | some b => .const (boolVal b)
            | none => .ty boolTy), s)

theorem widenconditionalAgreesExtractReachable_proven : WidenconditionalAgreesExtractReachable := by
  intro c s hc hb
  cases c
  case conditional slot d t e isdef =>
    simp only [widenconditional, maybeExtractConstBool] at hb ⊢
    repeat' split
    all_goals first | rfl | (simp_all [LElt.isBottom]; done) | (simp_all [LElt.isBottom]; rfl)
  case interConditional slot t e =>
    simp only [widenconditional, maybeExtractConstBool] at hb ⊢
    repeat' split
    all_goals first | rfl | (simp_all [LElt.isBottom]; done) | (simp_all [LElt.isBottom]; rfl)
  all_goals simp [LElt.isAnyConditional, LElt.isConditional, LElt.isInterConditional] at hc

/-- `widenwrappedconditional` and `widenwrappedmustalias` widen inside a `LimitedAccuracy` and
keep its causes, and agree with `widenconditional` / `widenmustalias` on everything else. Inside
the `LimitedAccuracy` the wrapped element may itself be a slot wrapper, which is the case these
methods exist for: `LimitedAccuracy(Conditional)` becomes `LimitedAccuracy` of the widened
conditional, and `LimitedAccuracy(MustAlias)` becomes `LimitedAccuracy` of its field type. -/
def WidenwrappedSpec : Prop :=
  (∀ x s, x.isLimited = false →
    (widenwrappedconditional x).run s = (widenconditional x).run s ∧
    (widenwrappedmustalias x).run s = (widenmustalias x).run s) ∧
  (∀ t cs cid s w, t.isLimited = false →
    (widenconditional t).run s = .ok (w, s) → w.isLimited = false →
    (widenwrappedconditional (.limitedAccuracy t cs cid)).run s = .ok (.limitedAccuracy w cs cid, s)) ∧
  (∀ t cs cid s w, t.isLimited = false →
    (widenmustalias t).run s = .ok (w, s) → w.isLimited = false →
    (widenwrappedmustalias (.limitedAccuracy t cs cid)).run s = .ok (.limitedAccuracy w cs cid, s))

theorem widenwrappedSpec_proven : WidenwrappedSpec := by
  refine ⟨fun x s hx => ?_, fun t cs cid s w hl hw hwl => ?_, fun t cs cid s w hl hw hwl => ?_⟩
  · cases x <;> first | (exact ⟨rfl, rfl⟩) | (simp [LElt.isLimited] at hx)
  · unfold widenwrappedconditional
    show (do let w ← widenconditional t; mkLimitedAccuracy w (some (cs, cid)) : CM LElt).run s = _
    rw [run_bind_ok hw]
    exact mkLimitedAccuracy_some hwl
  · unfold widenwrappedmustalias
    show (do let w ← widenmustalias t; mkLimitedAccuracy w (some (cs, cid)) : CM LElt).run s = _
    rw [run_bind_ok hw]
    exact mkLimitedAccuracy_some hwl

/-- `condParts c` is `(thentype, elsetype)` of a `Conditional` or `InterConditional`. -/
def condParts : LElt → Option (LElt × LElt)
  | .conditional _ _ t e _ | .interConditional _ t e => some (t, e)
  | _ => none

theorem isBottom_iff (x : LElt) : x.isBottom = true ↔ x = .ty .bottom := by
  constructor
  · intro h
    cases x
    case ty v => cases v <;> first | rfl | (simp [LElt.isBottom] at h)
    all_goals simp [LElt.isBottom] at h
  · intro h; subst h; rfl

/-- What widening a slot wrapper gives, from the meaning of each wrapper (`Conditional` docstring
at `Compiler/src/typelattice.jl:20-39`: in the true branch the slot has type `thentype`, in the
false branch `elsetype`; `MustAlias` docstring at `:66-89`: it stands for the field of type
`fldtyp`):

* `widenconditional` of a conditional whose `thentype` is `Union{}` (the true branch cannot be
  taken) is `Const(false)`; with only `elsetype` `Union{}` it is `Const(true)`; otherwise `Bool`.
* `widenmustalias` of an alias is its field type `fldtyp` itself (not its widening).
* `widenslotwrapper` widens a conditional with `widenconditional` and an alias with
  `widenmustalias`.
* Both functions return every other element unchanged, and a `LimitedAccuracy` is an
  `ErrorException` ("unhandled LimitedAccuracy"). -/
def WidenWrappersSpec : Prop :=
  (∀ c t e s, condParts c = some (t, e) →
    (t.isBottom = true → (widenconditional c).run s = .ok (.const (boolVal false), s)) ∧
    (t.isBottom = false → e.isBottom = true →
      (widenconditional c).run s = .ok (.const (boolVal true), s)) ∧
    (t.isBottom = false → e.isBottom = false → (widenconditional c).run s = .ok (.ty boolTy, s))) ∧
  (∀ x s, x.isAnyConditional = false → x.isLimited = false →
    (widenconditional x).run s = .ok (x, s)) ∧
  (∀ t cs cid, ThrowsJulia "ErrorException" (widenconditional (.limitedAccuracy t cs cid))) ∧
  (∀ slot d v i f s, (widenmustalias (.mustAlias slot d v i f)).run s = .ok (f, s)) ∧
  (∀ slot v i f s, (widenmustalias (.interMustAlias slot v i f)).run s = .ok (f, s)) ∧
  (∀ x s, x.isAnyMustAlias = false → x.isLimited = false → (widenmustalias x).run s = .ok (x, s)) ∧
  (∀ t cs cid, ThrowsJulia "ErrorException" (widenmustalias (.limitedAccuracy t cs cid))) ∧
  (∀ c s, c.isAnyConditional = true → (widenslotwrapper c).run s = (widenconditional c).run s) ∧
  (∀ slot d v i f s, (widenslotwrapper (.mustAlias slot d v i f)).run s = .ok (f, s)) ∧
  (∀ slot v i f s, (widenslotwrapper (.interMustAlias slot v i f)).run s = .ok (f, s))

theorem wc_then_bottom (c t e : LElt) (s : Nat) (hc : condParts c = some (t, e))
    (ht : t.isBottom = true) : (widenconditional c).run s = .ok (.const (boolVal false), s) := by
  rw [isBottom_iff] at ht
  subst ht
  cases c <;> simp [condParts] at hc <;> (obtain ⟨rfl, rfl⟩ := hc) <;> rfl

theorem wc_else_bottom (c t e : LElt) (s : Nat) (hc : condParts c = some (t, e))
    (ht : t.isBottom = false) (he : e.isBottom = true) :
    (widenconditional c).run s = .ok (.const (boolVal true), s) := by
  rw [isBottom_iff] at he
  subst he
  cases c <;> simp [condParts] at hc <;> (obtain ⟨rfl, rfl⟩ := hc) <;>
    (simp only [widenconditional]
     split <;> first | rfl | (simp_all [LElt.isBottom]; done) | (simp_all [LElt.isBottom]; rfl))

theorem wc_neither_bottom (c t e : LElt) (s : Nat) (hc : condParts c = some (t, e))
    (ht : t.isBottom = false) (he : e.isBottom = false) :
    (widenconditional c).run s = .ok (.ty boolTy, s) := by
  cases c <;> simp [condParts] at hc <;> (obtain ⟨rfl, rfl⟩ := hc) <;>
    (simp only [widenconditional]
     split <;> first | rfl | (simp_all [LElt.isBottom]; done) | (simp_all [LElt.isBottom]; rfl))

theorem widenWrappersSpec_proven : WidenWrappersSpec := by
  refine ⟨fun c t e s hc => ⟨wc_then_bottom c t e s hc, wc_else_bottom c t e s hc,
      wc_neither_bottom c t e s hc⟩, ?_, fun _ _ _ s => ⟨_, rfl⟩, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, ?_, fun _ _ _ s => ⟨_, rfl⟩, fun c s hc => widenslotwrapper_cond c s hc,
    fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · intro x s hc hl
    cases x <;> first | rfl | (simp [LElt.isAnyConditional, LElt.isConditional,
      LElt.isInterConditional, LElt.isLimited] at hc hl)
  · intro x s hc hl
    cases x <;> first | rfl | (simp [LElt.isAnyMustAlias, LElt.isMustAlias,
      LElt.isInterMustAlias, LElt.isLimited] at hc hl)

/-! ## `is_same_conditionals`, `is_same_alias`, `ignorelimited` -/

/-- `is_same_conditionals` is an equivalence relation on `Conditional`s and on
`InterConditional`s, and comparing the two kinds is a `MethodError` ("they will never be
compared", `Compiler/src/typelattice.jl:263-264`). Two `Conditional`s are about the same thing
exactly when they refine the same slot at the same definition (`slot` and `ssadef`), and two
`InterConditional`s when they refine the same argument (`slot`). -/
def IsSameConditionalsEquiv : Prop :=
  (∀ s1 d1 t1 e1 i1 s2 d2 t2 e2 i2 s, ∃ r,
    (isSameConditionals (.conditional s1 d1 t1 e1 i1) (.conditional s2 d2 t2 e2 i2)).run s =
      .ok (r, s) ∧ (r = true ↔ s1 = s2 ∧ d1 = d2)) ∧
  (∀ s1 t1 e1 s2 t2 e2 s, ∃ r,
    (isSameConditionals (.interConditional s1 t1 e1) (.interConditional s2 t2 e2)).run s =
      .ok (r, s) ∧ (r = true ↔ s1 = s2)) ∧
  (∀ c s, c.isAnyConditional = true → (isSameConditionals c c).run s = .ok (true, s)) ∧
  (∀ a b s, (isSameConditionals a b).run s = .ok (true, s) →
    (isSameConditionals b a).run s = .ok (true, s)) ∧
  (∀ a b c s, (isSameConditionals a b).run s = .ok (true, s) →
    (isSameConditionals b c).run s = .ok (true, s) →
    (isSameConditionals a c).run s = .ok (true, s)) ∧
  (∀ s1 d1 t1 e1 i1 s2 t2 e2,
    ThrowsJulia "MethodError" (isSameConditionals (.conditional s1 d1 t1 e1 i1)
      (.interConditional s2 t2 e2)))

theorem isSameConditionalsEquiv_proven : IsSameConditionalsEquiv := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ s => ⟨_, rfl, by simp⟩, fun _ _ _ _ _ _ s => ⟨_, rfl, by simp⟩,
    ?_, ?_, ?_, fun _ _ _ _ _ _ _ _ s => ⟨_, rfl⟩⟩
  · intro c s hc
    cases c <;> first
      | (show Except.ok (_, s) = _; simp)
      | (simp [LElt.isAnyConditional, LElt.isConditional, LElt.isInterConditional] at hc)
  · intro a b s h
    cases a <;> cases b <;> (try cases h) <;>
      (simp only [isSameConditionals, pure_run, Except.ok.injEq, Prod.mk.injEq, and_true,
        beq_iff_eq, Bool.and_eq_true] at h ⊢; omega)
  · intro a b c s h₁ h₂
    cases a <;> cases b <;> (try cases h₁) <;> cases c <;> (try cases h₂) <;>
      (simp only [isSameConditionals, pure_run, Except.ok.injEq, Prod.mk.injEq, and_true,
        beq_iff_eq, Bool.and_eq_true] at h₁ h₂ ⊢; omega)

/-- `is_same_alias` is an equivalence relation on `MustAlias`es and on `InterMustAlias`es, and is
`false` across the two kinds and for anything that is not an alias. Two `MustAlias`es refer to
the same field exactly when they have the same slot, definition and field index, and two
`InterMustAlias`es when they have the same slot and field index. -/
def IsSameAliasEquiv : Prop :=
  (∀ s1 d1 v1 i1 f1 s2 d2 v2 i2 f2,
    isSameAlias (.mustAlias s1 d1 v1 i1 f1) (.mustAlias s2 d2 v2 i2 f2) = true ↔
      s1 = s2 ∧ d1 = d2 ∧ i1 = i2) ∧
  (∀ s1 v1 i1 f1 s2 v2 i2 f2,
    isSameAlias (.interMustAlias s1 v1 i1 f1) (.interMustAlias s2 v2 i2 f2) = true ↔
      s1 = s2 ∧ i1 = i2) ∧
  (∀ a, a.isAnyMustAlias = true → isSameAlias a a = true) ∧
  (∀ a b, isSameAlias a b = true → isSameAlias b a = true) ∧
  (∀ a b c, isSameAlias a b = true → isSameAlias b c = true → isSameAlias a c = true) ∧
  (∀ a b, isSameAlias a b = true → a.isAnyMustAlias = true ∧
    (a.isMustAlias = b.isMustAlias))

theorem isSameAliasEquiv_proven : IsSameAliasEquiv := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ => by simp [isSameAlias, and_assoc],
    fun _ _ _ _ _ _ _ _ => by simp [isSameAlias], ?_, ?_, ?_, ?_⟩
  · intro a h; cases a <;> simp_all [isSameAlias, LElt.isAnyMustAlias, LElt.isMustAlias,
      LElt.isInterMustAlias]
  · intro a b h
    cases a <;> cases b <;>
      simp only [isSameAlias, beq_iff_eq, Bool.and_eq_true, Bool.false_eq_true] at h ⊢ <;> omega
  · intro a b c h₁ h₂
    cases a <;> cases b <;> cases c <;>
      simp only [isSameAlias, beq_iff_eq, Bool.and_eq_true, Bool.false_eq_true] at h₁ h₂ ⊢ <;>
      omega
  · intro a b h; cases a <;> cases b <;> simp_all [isSameAlias, LElt.isAnyMustAlias,
      LElt.isMustAlias, LElt.isInterMustAlias]

/-- `ignorelimited` removes one `LimitedAccuracy`, so on elements that are not nested (the
constructor's assertion) the result is never limited, and applying it twice is the same as once.
For a `LimitedAccuracy(T)` the result is the element `T` it wraps. -/
def IgnorelimitedSpec : Prop :=
  (∀ t cs cid, ignorelimited (.limitedAccuracy t cs cid) = t) ∧
  ∀ x, (x.isLimited = true → (ignorelimited x).isLimited = false) →
    (ignorelimited x).isLimited = false ∧ ignorelimited (ignorelimited x) = ignorelimited x ∧
    (x.isLimited = false → ignorelimited x = x)

theorem ignorelimitedSpec_proven : IgnorelimitedSpec := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro x hx
  cases x
  case limitedAccuracy t cs cid =>
    have ht := hx rfl
    refine ⟨ht, ?_, fun h => by cases h⟩
    cases t <;> first | rfl | (simp [ignorelimited, LElt.isLimited] at ht)
  all_goals exact ⟨rfl, rfl, fun _ => rfl⟩

end JuliaLean.Proofs.Compiler.src.typelattice
