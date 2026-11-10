import JuliaLean.Proofs.Compiler.src.tfuncs.Nothrow

/-!
`builtin_tfunction` (`Compiler/src/tfuncs.jl:3255-3334`): constant folding, the argument count
check, and what they give `builtin_nothrow` for the pure builtins.
-/

namespace JuliaLean.Proofs.Compiler.Tfuncs

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- The modelled builtins with a fixed argument count and a modelled runtime. -/
def fixedArityBuiltins : List String :=
  ["===", "typeof", "has_free_typevars", "nfields", "<:", "isa", "typeassert", "throw", "ifelse"]

/-- `tfuncArity f` admits `k` arguments. -/
def arityOk (f : String) (k : Nat) : Bool :=
  match tfuncArity f with
  | some (mn, some mx) => mn ≤ k && k ≤ mx
  | some (mn, none) => mn ≤ k
  | none => false

/-- Calling a fixed-arity builtin with the wrong number of arguments is a Julia exception
(`JL_NARGS`, `src/builtins.c`). -/
theorem builtinRT_wrong_arity (n : Nat) (E : CEnv) (f : String) (vals : List Val) (s : Nat)
    (hf : f ∈ fixedArityBuiltins) (hk : arityOk f vals.length = false) :
    ∃ e, (builtinRT n E f vals).run s = .error e ∧ isJuliaError e = true := by
  simp only [fixedArityBuiltins, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
  first
    | exact ⟨_, rfl, isJuliaError_jl _ _⟩
    | (simp [arityOk, tfuncArity] at hk)

/-- `collect_const_args` returns one value per argument type. -/
theorem collectConstArgs_length (E : CEnv) (args : List LElt) (s : Nat) (vals : List Val)
    (s' : Nat) (h : (collectConstArgs E args).run s = .ok (vals, s')) : vals.length = args.length := by
  induction args generalizing s vals s' with
  | nil =>
    simp [collectConstArgs, List.mapM_nil] at h
    cases h; rfl
  | cons a as ih =>
    simp only [collectConstArgs, List.mapM_cons] at h ih
    obtain ⟨v, s₁, _, h⟩ := run_bind_inv h
    obtain ⟨vs, s₂, hvs, h⟩ := run_bind_inv h
    have := ih s₁ vs s₂ hvs
    cases h
    simp [this]

/-! ## Constant folding -/

/-- The constant-folding prologue of `builtin_tfunction` (`Compiler/src/tfuncs.jl:3259-3277`):
it applies only to the foldable builtins (`_PURE_BUILTINS`, and the builtins that are both
consistent and effect-free) with all-constant arguments; then it returns `Const(f(args...))`
when the call returns, and `Union{}` when the call throws a Julia exception. -/
def BuiltinFoldSpec : Prop :=
  ∀ n E f args s,
    (foldableBuiltins.contains f = false → (builtinFold n E f args).run s = .ok (none, s)) ∧
    (∀ s₁, foldableBuiltins.contains f = true → (isAllConstArg n E args).run s = .ok (false, s₁) →
      (builtinFold n E f args).run s = .ok (none, s₁)) ∧
    (∀ s₁ vals s₂, foldableBuiltins.contains f = true →
      (isAllConstArg n E args).run s = .ok (true, s₁) →
      (collectConstArgs E args).run s₁ = .ok (vals, s₂) →
      (builtinFold n E f args).run s =
        match (builtinRT n E f vals).run s₂ with
        | .ok (r, s₃) => .ok (some (.const r), s₃)
        | .error e => if isJuliaError e then .ok (some (.ty .bottom), s₂) else .error e)

theorem builtinFoldSpec_proven : BuiltinFoldSpec := by
  intro n E f args s
  refine ⟨fun hf => ?_, fun s₁ hf ha => ?_, fun s₁ vals s₂ hf ha hc => ?_⟩
  · have : f ∉ foldableBuiltins := by simpa using hf
    simp [builtinFold, this]; rfl
  · simp only [builtinFold, hf, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, ha]; rfl
  · simp only [builtinFold, hf, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, ha]
    dsimp only [bind, Except.bind]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [stbind_run_ok hc]
    cases hrt : (builtinRT n E f vals).run s₂ with
    | ok p =>
      obtain ⟨r, s₃⟩ := p
      rw [tryCatch_run, stbind_run_ok hrt]; rfl
    | error e =>
      rw [tryCatch_run, stbind_run_error hrt]
      dsimp only
      split <;> rfl

/-! ## Argument count and `Vararg` padding -/

/-- The argument check of `builtin_tfunction` (`Compiler/src/tfuncs.jl:3306-3325`). Without a
trailing `Vararg` the tfunc gets the arguments unchanged when their count is within the
`add_tfunc` bounds, and the call is `Union{}` otherwise. With a trailing `Vararg{T}` after `k`
other arguments: more than `maxarg` fixed arguments is `Union{}`; exactly `maxarg` drops the
`Vararg`; otherwise the fixed arguments are padded with copies of `T` up to `minarg`, and a
`Vararg{T}` is appended when the padded list is still shorter than `maxarg`. -/
def BuiltinArgsSpec : Prop :=
  (∀ mn mx args, hasVararg args = false →
    builtinArgs mn mx args =
      if mn ≤ args.length ∧ (mx.map (fun m => decide (args.length ≤ m))).getD true = true
      then some args else none) ∧
  (∀ mn mx pre vaT N,
    builtinArgs mn mx (pre ++ [.ty (.vararg vaT N)]) =
      if (mx.map (fun m => decide (pre.length > m))).getD false = true then none
      else if mx = some pre.length then some pre
      else
        let padded := pre ++ List.replicate (mn - pre.length) (.ty (vaT.getD anyType))
        if (mx.map (fun m => decide (padded.length < m))).getD true = true then
          some (padded ++ [.ty (.vararg (some (vaT.getD anyType)) none)])
        else some padded)

theorem builtinArgsSpec_proven : BuiltinArgsSpec := by
  refine ⟨fun mn mx args hv => ?_, fun mn mx pre vaT N => ?_⟩
  · simp only [hasVararg] at hv
    unfold builtinArgs
    split
    · rename_i vaT N h
      simp [h, LElt.isVarargElt, Val.isVararg] at hv
    · simp
  · simp [builtinArgs]

/-! ## `builtin_tfunction` -/

/-- `builtin_tfunction` on a modelled builtin: a folded call is the folded result; `tuple`
calls `tuple_tfunc`; any other builtin calls its tfunc with the checked argument list, and a
wrong argument count is `Union{}` (`Compiler/src/tfuncs.jl:3255-3334`). -/
def BuiltinTfunctionSpec : Prop :=
  ∀ n T L f args s s₁, modelledBuiltins.contains f = true →
    (∀ r, (builtinFold n T.E f args).run s = .ok (some r, s₁) →
      (builtinTfunction n T L f args).run s = .ok (r, s₁)) ∧
    ((builtinFold n T.E f args).run s = .ok (none, s₁) → f = "tuple" →
      (builtinTfunction n T L f args).run s = (tupleTfunc n T.E L args).run s₁) ∧
    (∀ e, (builtinFold n T.E f args).run s = .error e →
      (builtinTfunction n T L f args).run s = .error e) ∧
    (∀ mn mx, (builtinFold n T.E f args).run s = .ok (none, s₁) → f ≠ "tuple" →
      tfuncArity f = some (mn, mx) →
      (builtinTfunction n T L f args).run s =
        (match builtinArgs mn mx args with
         | none => pure (LElt.ty .bottom)
         | some a => callTfunc n T L f a).run s₁)

theorem builtinTfunctionSpec_proven : BuiltinTfunctionSpec := by
  intro n T L f args s s₁ hm
  refine ⟨fun r hr => ?_, fun hr ht => ?_, fun e hr => ?_, fun mn mx hr ht ha => ?_⟩
  · simp only [builtinTfunction, hm, Bool.true_or, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, hr]; rfl
  · subst ht
    simp only [builtinTfunction, hm, Bool.true_or, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, hr]; rfl
  · simp only [builtinTfunction, hm, Bool.true_or, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, hr]; rfl
  · have ht' : (f == "tuple") = false := by simpa using ht
    have hc : (f == "current_scope") = false := by
      cases h : f == "current_scope"
      · rfl
      · have := beq_iff_eq.mp h; subst this; simp [modelledBuiltins] at hm
    have hap : (f == "apply_type") = false := by
      cases h : f == "apply_type"
      · rfl
      · have := beq_iff_eq.mp h; subst this; simp [modelledBuiltins] at hm
    simp only [builtinTfunction, hm, Bool.true_or, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, hr]
    dsimp only [bind, Except.bind]
    simp only [ht', hc, hap, Bool.false_eq_true, ite_false, ha]
    cases builtinArgs mn mx args <;> rfl

/-- The `builtin_tfunction` branches for builtins outside the modelled tfuncs
(`Compiler/src/tfuncs.jl:3287-3303`): a builtin without a tfunc (`find_tfunc(f) === nothing`) is
`Any`; `current_scope` with arguments other than none or a single `Vararg` is `Union{}`;
`apply_type` that does not fold goes to `apply_type_tfunc` (not modelled here), not to the `Any`
branch. -/
def BuiltinDispatchSpec : Prop :=
  ∀ n T L args s,
    (∀ f, f ∈ noTfuncBuiltins → (builtinTfunction n T L f args).run s = .ok (.ty anyType, s)) ∧
    (args.length ≠ 0 → (args.length ≠ 1 ∨ args[0]!.isVarargElt = false) →
      (builtinTfunction n T L "current_scope" args).run s = .ok (.ty .bottom, s)) ∧
    (∀ s₁, (builtinFold n T.E "apply_type" args).run s = .ok (none, s₁) →
      (builtinTfunction n T L "apply_type" args).run s = (unmodelled "apply_type_tfunc" : CM LElt).run s₁)

theorem builtinDispatchSpec_proven : BuiltinDispatchSpec := by
  intro n T L args s
  refine ⟨fun f hf => ?_, fun h0 h1 => ?_, fun s₁ hr => ?_⟩
  · simp only [noTfuncBuiltins, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · have hl : (args.length != 0) = true := by simpa using h0
    have hc : (args.length != 1 || !args[0]!.isVarargElt) = true := by
      rcases h1 with h1 | h1
      · simp [h1]
      · rw [h1]; simp
    simp only [builtinTfunction]
    rw [show ((modelledBuiltins.contains "current_scope" ||
      dispatchOnlyBuiltins.contains "current_scope")) = true from rfl]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, show (builtinFold n T.E "current_scope" args).run s = .ok (none, s) from rfl]
    dsimp only [bind, Except.bind]
    simp only [hl, hc, ite_true]
    rfl
  · simp only [builtinTfunction]
    rw [show ((modelledBuiltins.contains "apply_type" ||
      dispatchOnlyBuiltins.contains "apply_type")) = true from rfl]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [StateT.run_bind, hr]
    rfl

/-! ## A wrong argument count -/

theorem builtinRT_getfield_wrong_arity (n : Nat) (E : CEnv) (vals : List Val) (s : Nat)
    (hk : arityOk "getfield" vals.length = false) :
    ∃ e, (builtinRT n E "getfield" vals).run s = .error e ∧ isJuliaError e = true := by
  rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
  · exact ⟨_, rfl, isJuliaError_jl _ _⟩
  · exact ⟨_, rfl, isJuliaError_jl _ _⟩
  all_goals first
    | (simp [arityOk, tfuncArity] at hk)
    | skip
  have : (c :: d :: e :: rest).length > 2 := by simp
  refine ⟨_, ?_, isJuliaError_jl "ArgumentError" "getfield: wrong number of arguments"⟩
  simp [builtinRT, this]; rfl

/-- Folding a fixed-arity builtin called with the wrong number of arguments gives `Union{}`,
if it folds at all. -/
theorem builtinFold_wrong_arity (n : Nat) (E : CEnv) (f : String) (args : List LElt)
    (hf : f ∈ fixedArityBuiltins) (hk : arityOk f args.length = false) :
    Returns (builtinFold n E f args) (fun r => ∀ x, r = some x → x.isBottom = true) := by
  intro s r s' h x hx
  subst hx
  have hfold : foldableBuiltins.contains f = true := by
    simp only [fixedArityBuiltins, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [builtinFold, hfold, Bool.not_true, Bool.false_eq_true, ite_false] at h
  obtain ⟨b, s₁, hb, h⟩ := run_bind_inv h
  cases b with
  | false => cases h
  | true =>
    obtain ⟨vals, s₂, hc, h⟩ := run_bind_inv h
    have hlen := collectConstArgs_length E args s₁ vals s₂ hc
    obtain ⟨e, he, hj⟩ := builtinRT_wrong_arity n E f vals s₂ hf (hlen ▸ hk)
    rw [tryCatch_run, run_bind_error he] at h
    simp only [hj, ite_true] at h
    cases h; rfl

/-- `builtin_tfunction` returns `Union{}` for a builtin called with a number of arguments outside
its `add_tfunc` bounds and no trailing `Vararg` (`Compiler/src/tfuncs.jl:3319-3322`), and the
call does throw: for `getfield` and the fixed-arity builtins, the runtime raises a Julia
exception for every such argument list (`JL_NARGS` in `src/builtins.c`). -/
def BuiltinArityBottom : Prop :=
  (∀ n T L f args, f ∈ fixedArityBuiltins ++ ["getfield", "isdefined"] → hasVararg args = false →
    arityOk f args.length = false →
    Returns (builtinTfunction n T L f args) (fun R => R.isBottom = true)) ∧
  (∀ n E f vals s, f ∈ fixedArityBuiltins ++ ["getfield"] → arityOk f vals.length = false →
    ∃ e, (builtinRT n E f vals).run s = .error e ∧ isJuliaError e = true)

theorem builtinArityBottom_proven : BuiltinArityBottom := by
  refine ⟨fun n T L f args hf hv hk => ?_, fun n E f vals s hf hk => ?_⟩
  · intro s R s' h
    have hm : modelledBuiltins.contains f = true := by
      simp only [fixedArityBuiltins, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have ht : f ≠ "tuple" := by
      simp only [fixedArityBuiltins, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨mn, mx, har⟩ : ∃ mn mx, tfuncArity f = some (mn, mx) := by
      simp only [fixedArityBuiltins, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, _, rfl⟩
    have spec := builtinTfunctionSpec_proven n T L f args s
    cases hfr : (builtinFold n T.E f args).run s with
    | error e => rw [(spec s hm).2.2.1 e hfr] at h; cases h
    | ok p =>
      obtain ⟨o, s₁⟩ := p
      cases o with
      | some x =>
        rw [(spec s₁ hm).1 x hfr] at h
        cases h
        have hfa : f ∈ fixedArityBuiltins := by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with hf | rfl | rfl
          · exact hf
          · have := (builtinFoldSpec_proven n T.E "getfield" args s).1 rfl
            rw [this] at hfr; cases hfr
          · have := (builtinFoldSpec_proven n T.E "isdefined" args s).1 rfl
            rw [this] at hfr; cases hfr
        exact builtinFold_wrong_arity n T.E f args hfa hk s _ _ hfr _ rfl
      | none =>
        rw [(spec s₁ hm).2.2.2 mn mx hfr ht har] at h
        have hargs : builtinArgs mn mx args = none := by
          rw [builtinArgsSpec_proven.1 mn mx args hv]
          simp only [arityOk, har] at hk
          cases mx with
          | none => simp_all
          | some m => simp_all
        rw [hargs] at h
        cases h; rfl
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with hf | rfl
    · exact builtinRT_wrong_arity n E f vals s hf hk
    · exact builtinRT_getfield_wrong_arity n E vals s hk

end JuliaLean.Proofs.Compiler.Tfuncs
