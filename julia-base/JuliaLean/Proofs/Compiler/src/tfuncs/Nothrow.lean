import JuliaLean.Proofs.Compiler.src.tfuncs.Common

/-!
`builtin_nothrow` and the `nothrow` predicates of the core builtins
(`Compiler/src/tfuncs.jl:361-364, 403-419, 954-963, 1000-1003, 1023-1026, 2626-2711, 3236-3253`).
-/

namespace JuliaLean.Proofs.Compiler.Tfuncs

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- The last argument type is a `Vararg` (`hasvarargtype`, `Compiler/src/tfuncs.jl:3236`). -/
def hasVararg (args : List LElt) : Bool := (args.getLast?.map LElt.isVarargElt).getD false

/-- `builtin_nothrow(𝕃, f, argtypes, rt)` on the modelled builtins
(`Compiler/src/tfuncs.jl:3243-3253` and `_builtin_nothrow`, 2626-2711):
* a `Union{}` result is never nothrow;
* `tuple` and `svec` are nothrow whenever the result is not `Union{}`, Vararg or not;
* every other builtin with a trailing `Vararg` argument is not nothrow;
* the other `_PURE_BUILTINS` (`===`, `typeof`, `has_free_typevars`, `nfields`) are nothrow;
* `isa(x, t)` is nothrow when `t ⊑ Type` (`isa_nothrow`), `a <: b` when `a ⊑ Type` and
  `b ⊑ Type` (`subtype_nothrow`), `ifelse(c, x, y)` when `c ⊑ Bool` (`ifelse_nothrow`);
  `typeassert`, `isdefined` and `getfield` defer to their own predicates;
* `isa`, `<:` and `typeassert` with other than two arguments, and `ifelse` with other than
  three, are not nothrow, and neither is `throw`. -/
def BuiltinNothrowSpec : Prop :=
  ∀ n T L s,
    (∀ f args rt, modelledBuiltins.contains f = true → rt.isBottom = true →
      (builtinNothrow n T L f args rt).run s = .ok (false, s)) ∧
    (∀ f args rt, (f = "tuple" ∨ f = "svec") → rt.isBottom = false →
      (builtinNothrow n T L f args rt).run s = .ok (true, s)) ∧
    (∀ f args rt, modelledBuiltins.contains f = true → f ≠ "tuple" → f ≠ "svec" →
      rt.isBottom = false → hasVararg args = true →
      (builtinNothrow n T L f args rt).run s = .ok (false, s)) ∧
    (∀ f args rt, f ∈ ["===", "typeof", "has_free_typevars", "nfields"] →
      rt.isBottom = false → hasVararg args = false →
      (builtinNothrow n T L f args rt).run s = .ok (true, s)) ∧
    (∀ x t rt, rt.isBottom = false → t.isVarargElt = false →
      (builtinNothrow n T L "isa" [x, t] rt).run s = (sqsub n T.E L t (.ty typeTypeVal)).run s) ∧
    (∀ a b rt, rt.isBottom = false → b.isVarargElt = false →
      (builtinNothrow n T L "<:" [a, b] rt).run s =
        (JuliaLean.Compiler.andM (sqsub n T.E L a (.ty typeTypeVal))
          (sqsub n T.E L b (.ty typeTypeVal))).run s) ∧
    (∀ c x y rt, rt.isBottom = false → y.isVarargElt = false →
      (builtinNothrow n T L "ifelse" [c, x, y] rt).run s = (sqsub n T.E L c (.ty boolTy)).run s) ∧
    (∀ v t rt, rt.isBottom = false → t.isVarargElt = false →
      (builtinNothrow n T L "typeassert" [v, t] rt).run s = (typeassertNothrow n T.E L v t).run s) ∧
    (∀ args rt, rt.isBottom = false → hasVararg args = false →
      (builtinNothrow n T L "isdefined" args rt).run s = (isdefinedNothrow n T.E L args).run s) ∧
    (∀ args rt, rt.isBottom = false → hasVararg args = false →
      (builtinNothrow n T L "getfield" args rt).run s = (getfieldNothrow n T L args).run s) ∧
    (∀ f args rt, f ∈ ["isa", "<:", "typeassert"] → args.length ≠ 2 → hasVararg args = false →
      (builtinNothrow n T L f args rt).run s = .ok (false, s)) ∧
    (∀ args rt, args.length ≠ 3 → hasVararg args = false →
      (builtinNothrow n T L "ifelse" args rt).run s = .ok (false, s)) ∧
    (∀ args rt, (builtinNothrow n T L "throw" args rt).run s = .ok (false, s))

theorem builtinNothrowSpec_proven : BuiltinNothrowSpec := by
  intro n T L s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f args rt hf hb
    have hf' : f ∈ modelledBuiltins := by simpa using hf
    simp [builtinNothrow, hf', hb]; rfl
  · intro f args rt hf hb
    rcases hf with rfl | rfl <;> simp [builtinNothrow, modelledBuiltins, hb] <;> rfl
  · intro f args rt hf ht hs hb hv
    simp only [hasVararg] at hv
    have hf' : f ∈ modelledBuiltins := by simpa using hf
    simp [builtinNothrow, hf', hb, ht, hs, hv]; rfl
  · intro f args rt hf hb hv
    simp only [hasVararg] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;>
      simp [builtinNothrow, modelledBuiltins, pureBuiltins, hb, hv] <;> rfl
  · intro x t rt hb ht
    simp [builtinNothrow, modelledBuiltins, pureBuiltins, hb, ht, isaNothrow]
  · intro a b rt hb ht
    simp [builtinNothrow, modelledBuiltins, pureBuiltins, hb, ht, subtypeNothrow]
  · intro c x y rt hb ht
    simp [builtinNothrow, modelledBuiltins, pureBuiltins, hb, ht, ifelseNothrow]
  · intro v t rt hb ht
    simp [builtinNothrow, modelledBuiltins, pureBuiltins, hb, ht]
  · intro args rt hb hv
    simp only [hasVararg] at hv
    simp [builtinNothrow, modelledBuiltins, pureBuiltins, hb, hv]
  · intro args rt hb hv
    simp only [hasVararg] at hv
    simp [builtinNothrow, modelledBuiltins, pureBuiltins, hb, hv]
  · intro f args rt hf hl hv
    simp only [hasVararg] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;>
      simp [builtinNothrow, modelledBuiltins, pureBuiltins, hl, hv] <;>
      first | rfl | (split <;> rfl)
  · intro args rt hl hv
    simp only [hasVararg] at hv
    simp [builtinNothrow, modelledBuiltins, pureBuiltins, hl, hv]
    first | rfl | (split <;> rfl)
  · intro args rt
    simp [builtinNothrow, modelledBuiltins, pureBuiltins]
    first | rfl | (split <;> (try split) <;> rfl)

/-- `isdefined_nothrow` (`Compiler/src/tfuncs.jl:403-419`): only the two-argument form without
`Vararg`s can be nothrow; on an object that may be a `Module` the name must be `⊑ Symbol`, and on
any other object `⊑ Symbol` or `⊑ Int`. -/
def IsdefinedNothrowSpec : Prop :=
  ∀ n E L s,
    (∀ args, args.length ≠ 2 → (isdefinedNothrow n E L args).run s = .ok (false, s)) ∧
    (∀ x nm, x.isVarargElt = true → (isdefinedNothrow n E L [x, nm]).run s = .ok (false, s)) ∧
    (∀ x nm, nm.isVarargElt = true → (isdefinedNothrow n E L [x, nm]).run s = .ok (false, s)) ∧
    (∀ x nm t s₁ s₂, x.isVarargElt = false → nm.isVarargElt = false →
      (widenconst n E x).run s = .ok (t, s₁) → (hasintersect n E t moduleType).run s₁ = .ok (true, s₂) →
      (isdefinedNothrow n E L [x, nm]).run s = (sqsub n E L nm (.ty symbolType)).run s₂) ∧
    (∀ x nm t s₁ s₂, x.isVarargElt = false → nm.isVarargElt = false →
      (widenconst n E x).run s = .ok (t, s₁) → (hasintersect n E t moduleType).run s₁ = .ok (false, s₂) →
      (isdefinedNothrow n E L [x, nm]).run s =
        (JuliaLean.Compiler.orM (sqsub n E L nm (.ty symbolType)) (sqsub n E L nm (.ty longType))).run s₂)

theorem isdefinedNothrowSpec_proven : IsdefinedNothrowSpec := by
  intro n E L s
  refine ⟨fun args hl => ?_, fun x nm hx => ?_, fun x nm hn => ?_,
    fun x nm t s₁ s₂ hx hn hw hi => ?_, fun x nm t s₁ s₂ hx hn hw hi => ?_⟩
  · rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> first | rfl | simp at hl
  · simp [isdefinedNothrow, hx]; rfl
  · simp [isdefinedNothrow, hn]; rfl
  · simp only [isdefinedNothrow, hx, hn, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    refine (stbind_run_ok hi).trans ?_; rfl
  · simp only [isdefinedNothrow, hx, hn, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    refine (stbind_run_ok hi).trans ?_; rfl

/-- `typeassert_nothrow` (`Compiler/src/tfuncs.jl:954-963`): `typeassert(v, t)` is nothrow
exactly when `t` is a closed `Type{P}` (or `TypeEgal{P}`) with `v ⊑ P`, or a constant type `T`
with `v ⊑ T`; any other `t` is not nothrow. -/
def TypeassertNothrowBase : Prop :=
  ∀ n E L v s,
    (∀ P, JuliaLean.Compiler.hasFreeTypevars (.typeeq P) = false →
      (typeassertNothrow n E L v (.ty (.typeeq P))).run s = (sqsub n E L v (.ty P)).run s) ∧
    (∀ P, JuliaLean.Compiler.hasFreeTypevars (.typeegal P) = false →
      (typeassertNothrow n E L v (.ty (.typeegal P))).run s = (sqsub n E L v (.ty P)).run s) ∧
    (∀ u, isType u = false → (typeassertNothrow n E L v (.ty u)).run s = .ok (false, s)) ∧
    (∀ T, T.isType = true →
      (typeassertNothrow n E L v (.const T)).run s = (sqsub n E L v (.ty T)).run s) ∧
    (∀ T, T.isType = false → (typeassertNothrow n E L v (.const T)).run s = .ok (false, s))

theorem typeassertNothrowBase_proven : TypeassertNothrowBase := by
  intro n E L v s
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun u hu => ?_, fun T hT => ?_, fun T hT => ?_⟩
  · simp only [typeassertNothrow, isType, isTypeEq, Val.isTypeeq, hP, Bool.true_or,
      Bool.not_false, Bool.and_self, ite_true, typeParameter]
    show (sqsub n E L v (.ty P) >>= fun b => (if b then pure true else pure false : CM Bool)).run s = _
    rw [StateT.run_bind]
    cases h : (sqsub n E L v (.ty P)).run s with
    | error e => rfl
    | ok p => obtain ⟨b, s'⟩ := p; cases b <;> rfl
  · simp only [typeassertNothrow, isType, isTypeEq, isTypeEgal, Val.isTypeeq, Val.isTypeegal, hP,
      Bool.or_true, Bool.not_false, Bool.and_self, ite_true, typeParameter]
    show (sqsub n E L v (.ty P) >>= fun b => (if b then pure true else pure false : CM Bool)).run s = _
    rw [StateT.run_bind]
    cases h : (sqsub n E L v (.ty P)).run s with
    | error e => rfl
    | ok p => obtain ⟨b, s'⟩ := p; cases b <;> rfl
  · simp [typeassertNothrow, hu]; rfl
  · simp only [typeassertNothrow, hT, ite_true]
    rw [StateT.run_bind]
    cases h : (sqsub n E L v (.ty T)).run s with
    | error e => rfl
    | ok p => obtain ⟨b, s'⟩ := p; cases b <;> rfl
  · simp [typeassertNothrow, hT]; rfl

end JuliaLean.Proofs.Compiler.Tfuncs
