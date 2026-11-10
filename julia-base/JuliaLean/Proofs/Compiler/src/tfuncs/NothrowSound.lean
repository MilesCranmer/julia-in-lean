import JuliaLean.Proofs.Compiler.src.tfuncs.Dispatch

/-!
Soundness of `builtin_nothrow` for `===`, `typeof`, `has_free_typevars`, `isa`, `<:` and
`ifelse`: when it returns `true`, calling the builtin on argument values in the concretization of
the argument types does not throw.

The statements take as hypotheses the facts about the C runtime and the lattice order they need,
each one a property Julia means to have:
* `EgalNoJuliaError`, `IsaNoJuliaError`, `IssubNoJuliaError`: `===`, `isa` and `<:` on valid
  arguments never throw a Julia exception (`jl_egal`, `jl_isa`, `jl_subtype` have no error paths;
  the model's only errors are fuel exhaustion and internal errors);
* `SqsubGammaType`, `SqsubGammaBool`: an element `⊑ Type` stands only for type objects, and an
  element `⊑ Bool` only for `true` and `false` (`⊑` is sound for the concretization).
-/

namespace JuliaLean.Proofs.Compiler.Tfuncs

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

def EgalNoJuliaError : Prop :=
  ∀ n T a b s e, (JuliaLean.C.egal n T a b).run s = .error e → isJuliaError e = false
def IsaNoJuliaError : Prop :=
  ∀ n E x t s e, (isa n E x t).run s = .error e → isJuliaError e = false
def IssubNoJuliaError : Prop :=
  ∀ n E a b s e, (issub n E a b).run s = .error e → isJuliaError e = false
def SqsubGammaType (L : Lattice) : Prop :=
  ∀ n E e v s₁ s₂ s₃ s₄, (sqsub n E L e (.ty typeTypeVal)).run s₁ = .ok (true, s₂) →
    (inGamma n E v e).run s₃ = .ok (true, s₄) → v.isType = true
def SqsubGammaBool (L : Lattice) : Prop :=
  ∀ n E e v s₁ s₂ s₃ s₄, (sqsub n E L e (.ty boolTy)).run s₁ = .ok (true, s₂) →
    (inGamma n E v e).run s₃ = .ok (true, s₄) → (asBool? v).isSome = true

/-- A computation that throws no Julia exception, from any state. -/
def NoJuliaError {α : Type} (m : CM α) : Prop := ∀ s e, m.run s = .error e → isJuliaError e = false

theorem noJuliaError_bind {α β : Type} {m : CM α} {k : α → CM β} (hm : NoJuliaError m)
    (hk : ∀ a, NoJuliaError (k a)) : NoJuliaError (m >>= k) := by
  intro s e h
  rw [StateT.run_bind] at h
  cases hr : m.run s with
  | error e' => rw [hr] at h; cases h; exact hm s _ hr
  | ok p => rw [hr] at h; exact hk p.1 p.2 e h

theorem noJuliaError_pure {α : Type} (a : α) : NoJuliaError (pure a : CM α) := by
  intro s e h; cases h

/-- From `builtin_nothrow = true`: the result is not `Union{}` and there is no trailing
`Vararg`. -/
theorem nothrow_basic (n : Nat) (T : TEnv) (L : Lattice) (f : String) (args : List LElt)
    (rt : LElt) (s s' : Nat) (hm : modelledBuiltins.contains f = true) (ht : f ≠ "tuple")
    (hs : f ≠ "svec") (h : (builtinNothrow n T L f args rt).run s = .ok (true, s')) :
    rt.isBottom = false ∧ hasVararg args = false := by
  have spec := builtinNothrowSpec_proven n T L s
  cases hb : rt.isBottom
  · cases hv : hasVararg args
    · exact ⟨rfl, rfl⟩
    · rw [spec.2.2.1 f args rt hm ht hs hb hv] at h; cases h
  · rw [spec.1 f args rt hm hb] at h; cases h

/-- `builtin_nothrow` for `typeof`, `has_free_typevars` and `===` ignores the argument count
(they are `_PURE_BUILTINS`, `Compiler/src/tfuncs.jl:3249-3250`) and relies on `rt`, the
`builtin_tfunction` result, being `Union{}` for a wrong count. With that `rt`, a nothrow call on
as many values as argument types throws no Julia exception. -/
def PureNothrowSound : Prop :=
  EgalNoJuliaError →
  ∀ n T L f args rt vals s₀ s₁ s₂ s₃, f ∈ ["typeof", "has_free_typevars", "==="] →
    (builtinTfunction n T L f args).run s₀ = .ok (rt, s₁) →
    (builtinNothrow n T L f args rt).run s₂ = .ok (true, s₃) →
    vals.length = args.length →
    NoJuliaError (builtinRT n T.E f vals)

theorem pureNothrowSound_proven : PureNothrowSound := by
  intro hegal n T L f args rt vals s₀ s₁ s₂ s₃ hf htf hnt hlen
  have hfa : f ∈ fixedArityBuiltins := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp [fixedArityBuiltins]
  have hm : modelledBuiltins.contains f = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> rfl
  have ht : f ≠ "tuple" := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> decide
  have hs : f ≠ "svec" := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> decide
  obtain ⟨hb, hv⟩ := nothrow_basic n T L f args rt s₂ s₃ hm ht hs hnt
  cases hk : arityOk f args.length
  · have := builtinArityBottom_proven.1 n T L f args (List.mem_append_left _ hfa) hv hk s₀ rt s₁ htf
    simp [hb] at this
  · rw [← hlen] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · rcases vals with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · simp [arityOk, tfuncArity] at hk
      · intro s e h; cases h
      · simp [arityOk, tfuncArity] at hk
    · rcases vals with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · simp [arityOk, tfuncArity] at hk
      · intro s e h; cases h
      · simp [arityOk, tfuncArity] at hk
    · rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · simp [arityOk, tfuncArity] at hk
      · simp [arityOk, tfuncArity] at hk
      · intro s e h
        have : (builtinRT n T.E "===" [a, b]) =
            (do return boolVal (← JuliaLean.C.egal n T.E.types a b)) := rfl
        rw [this, StateT.run_bind] at h
        cases he : (JuliaLean.C.egal n T.E.types a b).run s with
        | error e' => rw [he] at h; cases h; exact hegal _ _ _ _ _ _ he
        | ok p => rw [he] at h; cases h
      · simp [arityOk, tfuncArity] at hk

/-- `isa(x, t)` with `t ⊑ Type` (`isa_nothrow`) does not throw: the value of `t` is a type, so
`jl_f_isa`'s `JL_TYPECHK` passes. -/
def IsaNothrowSound (L : Lattice) : Prop :=
  SqsubGammaType L → IsaNoJuliaError →
  ∀ n T x t rt vx vt s₁ s₂ s₃ s₄, (builtinNothrow n T L "isa" [x, t] rt).run s₁ = .ok (true, s₂) →
    (inGamma n T.E vt t).run s₃ = .ok (true, s₄) →
    NoJuliaError (builtinRT n T.E "isa" [vx, vt])

theorem isaNothrowSound_proven (L : Lattice) : IsaNothrowSound L := by
  intro hsq hisa n T x t rt vx vt s₁ s₂ s₃ s₄ hnt hg
  obtain ⟨hb, hv⟩ := nothrow_basic n T L "isa" [x, t] rt s₁ s₂ rfl (by decide) (by decide) hnt
  have htv : t.isVarargElt = false := by simpa [hasVararg] using hv
  rw [(builtinNothrowSpec_proven n T L s₁).2.2.2.2.1 x t rt hb htv] at hnt
  have hty := hsq n T.E t vt s₁ s₂ s₃ s₄ hnt hg
  intro s e h
  have : builtinRT n T.E "isa" [vx, vt] = (do
      if !vt.isType then jlThrow "TypeError" "isa"
      return boolVal (← isa n T.E vx vt)) := rfl
  rw [this] at h
  simp only [hty, Bool.not_true, Bool.false_eq_true, ite_false] at h
  rw [StateT.run_bind] at h
  cases hi : (isa n T.E vx vt).run s with
  | error e' => rw [hi] at h; cases h; exact hisa _ _ _ _ _ _ hi
  | ok p => rw [hi] at h; cases h

/-- `a <: b` with `a ⊑ Type` and `b ⊑ Type` (`subtype_nothrow`) does not throw. -/
def SubtypeNothrowSound (L : Lattice) : Prop :=
  SqsubGammaType L → IssubNoJuliaError →
  ∀ n T a b rt va vb s₁ s₂ s₃ s₄ s₅ s₆, (builtinNothrow n T L "<:" [a, b] rt).run s₁ = .ok (true, s₂) →
    (inGamma n T.E va a).run s₃ = .ok (true, s₄) →
    (inGamma n T.E vb b).run s₅ = .ok (true, s₆) →
    NoJuliaError (builtinRT n T.E "<:" [va, vb])

theorem subtypeNothrowSound_proven (L : Lattice) : SubtypeNothrowSound L := by
  intro hsq hsub n T a b rt va vb s₁ s₂ s₃ s₄ s₅ s₆ hnt hga hgb
  obtain ⟨hb, hv⟩ := nothrow_basic n T L "<:" [a, b] rt s₁ s₂ rfl (by decide) (by decide) hnt
  have hbv : b.isVarargElt = false := by simpa [hasVararg] using hv
  rw [(builtinNothrowSpec_proven n T L s₁).2.2.2.2.2.1 a b rt hb hbv] at hnt
  obtain ⟨c, s', hc, hnt⟩ := run_bind_inv hnt
  cases c with
  | false => cases hnt
  | true =>
    have hta := hsq n T.E a va s₁ s' s₃ s₄ hc hga
    have htb := hsq n T.E b vb s' s₂ s₅ s₆ hnt hgb
    intro s e h
    have : builtinRT n T.E "<:" [va, vb] = (do
        if !va.isType || !vb.isType then jlThrow "TypeError" "<:"
        return boolVal (← issub n T.E va vb)) := rfl
    rw [this] at h
    simp only [hta, htb, Bool.not_true, Bool.or_self, Bool.false_eq_true, ite_false] at h
    rw [StateT.run_bind] at h
    cases hi : (issub n T.E va vb).run s with
    | error e' => rw [hi] at h; cases h; exact hsub _ _ _ _ _ _ hi
    | ok p => rw [hi] at h; cases h

/-- `ifelse(c, x, y)` with `c ⊑ Bool` (`ifelse_nothrow`) returns one of its arguments. -/
def IfelseNothrowSound (L : Lattice) : Prop :=
  SqsubGammaBool L →
  ∀ n T c x y rt vc vx vy s₁ s₂ s₃ s₄, (builtinNothrow n T L "ifelse" [c, x, y] rt).run s₁ = .ok (true, s₂) →
    (inGamma n T.E vc c).run s₃ = .ok (true, s₄) →
    ∀ s, (builtinRT n T.E "ifelse" [vc, vx, vy]).run s = .ok (vx, s) ∨
      (builtinRT n T.E "ifelse" [vc, vx, vy]).run s = .ok (vy, s)

theorem ifelseNothrowSound_proven (L : Lattice) : IfelseNothrowSound L := by
  intro hsq n T c x y rt vc vx vy s₁ s₂ s₃ s₄ hnt hg s
  obtain ⟨hb, hv⟩ := nothrow_basic n T L "ifelse" [c, x, y] rt s₁ s₂ rfl (by decide) (by decide) hnt
  have hyv : y.isVarargElt = false := by simpa [hasVararg] using hv
  rw [(builtinNothrowSpec_proven n T L s₁).2.2.2.2.2.2.1 c x y rt hb hyv] at hnt
  have hbool := hsq n T.E c vc s₁ s₂ s₃ s₄ hnt hg
  have : builtinRT n T.E "ifelse" [vc, vx, vy] = (match asBool? vc with
      | some true => return vx
      | some false => return vy
      | none => jlThrow "TypeError" "ifelse") := rfl
  rw [this]
  cases hab : asBool? vc with
  | none => rw [hab] at hbool; cases hbool
  | some b => cases b
              · exact Or.inr rfl
              · exact Or.inl rfl

def IsaNothrowSoundAll : Prop := ∀ L, IsaNothrowSound L
def SubtypeNothrowSoundAll : Prop := ∀ L, SubtypeNothrowSound L
def IfelseNothrowSoundAll : Prop := ∀ L, IfelseNothrowSound L

theorem isaNothrowSoundAll_proven : IsaNothrowSoundAll := isaNothrowSound_proven
theorem subtypeNothrowSoundAll_proven : SubtypeNothrowSoundAll := subtypeNothrowSound_proven
theorem ifelseNothrowSoundAll_proven : IfelseNothrowSoundAll := ifelseNothrowSound_proven

end JuliaLean.Proofs.Compiler.Tfuncs
