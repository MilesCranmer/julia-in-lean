import JuliaLean.Compiler.src.optimize

/-!
Model of the decision helpers of `Compiler/src/ssair/inlining.jl`: which result
`early_inline_special_case` gives (the decision to replace a call by its constant result, and the
`compilerbarrier`, `Core.ifelse` and `Core.task_result_type` rewrites), the branch
`handle_cases!` takes (single case, union split, or only flags), `inline_const_if_inlineable!`
and `linear_inline_eligible`; and the inline/compile decision of `resolve_todo` and
`semiconcrete_result_item` with the call-site `@inline`/`@noinline` flag bits that
`jl_code_info_set_ir` (src/method.c) sets. The last three are not in the difftest driver.

The parts that transform IR are not modelled; the inventory lists them as `todo`.

Modelling choices:

* The lattice and type questions these functions ask (`isa(type, Const)`,
  `is_inlineable_constant`, membership in `_PURE_BUILTINS` and `_EFFECT_FREE_BUILTINS`,
  `is_pure_intrinsic_infer`, `⊑(optimizer_lattice(...), x, Bool)` and so on) are inputs; the
  model mirrors the order of the questions, the branches and the flag arithmetic, which uses the
  `IR_FLAG_*` constants of `JuliaLean.Compiler.Optimize`.
* Which statement a rewrite produces is a tag (`EarlyResult`), not the new statement.

All sources are at master `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
-/

namespace JuliaLean.Compiler.Inlining

open JuliaLean JuliaLean.Compiler JuliaLean.Compiler.Optimize

/-- The callees `early_inline_special_case` names after the constant case. -/
inductive Special where
  | compilerbarrier | ifelse | taskResultType | none
  deriving Repr, DecidableEq, Inhabited

/-- What `early_inline_special_case` asks about the call `stmt` with signature
`sig = Signature(f, ft, argtypes)` and inferred `type`:

* `inlining`: `OptimizationParams(state.interp).inlining`;
* `typeConst`: `isa(type, Const)`; `valInlineable`: `is_inlineable_constant(type.val)`;
* `fIntrinsic`: `isa(f, IntrinsicFunction)`; `pureIntrinsic`: `is_pure_intrinsic_infer(f)`;
* `inPure`, `inEffectFree`: `contains_is(_PURE_BUILTINS, f)`,
  `contains_is(_EFFECT_FREE_BUILTINS, f)`;
* `special`: whether `f` is `compilerbarrier`, `Core.ifelse` or `Core.task_result_type`;
* `nargtypes`: `length(argtypes)`;
* about `argtypes[2]`: `arg2Const` (`isa(_, Const)`), `arg2Symbol` (its value `isa Symbol`),
  `arg2Conditional` (that value `=== :conditional`), `arg2True`, `arg2False` (the value
  `=== true`, `=== false`), `arg2Bool` (`⊑(𝕃ₒ, _, Bool)`), `arg2Task` (`⊑(𝕃ₒ, _, Task)`);
* `args34Egal`: `stmt.args[3] === stmt.args[4]`. -/
structure EarlyFacts where
  inlining : Bool
  typeConst : Bool
  valInlineable : Bool
  fIntrinsic : Bool
  pureIntrinsic : Bool
  inPure : Bool
  inEffectFree : Bool
  special : Special
  nargtypes : Nat
  arg2Const : Bool
  arg2Symbol : Bool
  arg2Conditional : Bool
  arg2True : Bool
  arg2False : Bool
  arg2Bool : Bool
  arg2Task : Bool
  args34Egal : Bool
  deriving Repr, Inhabited

/-- The result of `early_inline_special_case`: `nothing`, or `SomeCase` of `quoted(type.val)`,
`stmt.args[3]`, `stmt.args[4]` or `quoted(instanceof_tfunc(type)[1])`. -/
inductive EarlyResult where
  | none_ | quotedVal | arg3 | arg4 | instanceof
  deriving Repr, DecidableEq, Inhabited

/-- Julia source: Compiler/src/ssair/inlining.jl:1766-1815
```julia
function early_inline_special_case(ir::IRCode, stmt::Expr, flag::UInt32,
                                   @nospecialize(type), sig::Signature, state::InliningState)
    OptimizationParams(state.interp).inlining || return nothing
    (; f, ft, argtypes) = sig

    if isa(type, Const) # || isconstType(type)
        val = type.val
        is_inlineable_constant(val) || return nothing
        if isa(f, IntrinsicFunction)
            if is_pure_intrinsic_infer(f) && has_flag(flag, IR_FLAG_NOTHROW)
                return SomeCase(quoted(val))
            end
        elseif contains_is(_PURE_BUILTINS, f)
            return SomeCase(quoted(val))
        elseif contains_is(_EFFECT_FREE_BUILTINS, f)
            if has_flag(flag, IR_FLAG_NOTHROW)
                return SomeCase(quoted(val))
            end
        end
    end
    if f === compilerbarrier
        # check if this `compilerbarrier` has already imposed a barrier on abstract interpretation
        # so that it can be eliminated here
        length(argtypes) == 3 || return nothing
        setting = argtypes[2]
        isa(setting, Const) || return nothing
        setting = setting.val
        isa(setting, Symbol) || return nothing
        # setting === :const || setting === :type barrier const evaluation,
        # so they can't be eliminated at IPO time
        setting === :conditional || return nothing
        # barriered successfully already, eliminate it
        return SomeCase(stmt.args[3])
    elseif f === Core.ifelse && length(argtypes) == 4
        cond = argtypes[2]
        if isa(cond, Const)
            if cond.val === true
                return SomeCase(stmt.args[3])
            elseif cond.val === false
                return SomeCase(stmt.args[4])
            end
        elseif ⊑(optimizer_lattice(state.interp), cond, Bool) && stmt.args[3] === stmt.args[4]
            return SomeCase(stmt.args[3])
        end
    elseif (f === Core.task_result_type && length(argtypes) == 2 &&
            ⊑(optimizer_lattice(state.interp), argtypes[2], Task))
        return SomeCase(quoted(instanceof_tfunc(type)[1]))
    end
    return nothing
end
```
-/
def earlyInlineSpecialCase (x : EarlyFacts) (flag : UInt32) : EarlyResult := Id.run do
  if !x.inlining then return .none_
  if x.typeConst then
    if !x.valInlineable then return .none_
    if x.fIntrinsic then
      if x.pureIntrinsic && hasFlag flag IR_FLAG_NOTHROW then return .quotedVal
    else if x.inPure then return .quotedVal
    else if x.inEffectFree then
      if hasFlag flag IR_FLAG_NOTHROW then return .quotedVal
  if x.special == .compilerbarrier then
    if x.nargtypes != 3 then return .none_
    if !x.arg2Const then return .none_
    if !x.arg2Symbol then return .none_
    if !x.arg2Conditional then return .none_
    return .arg3
  else if x.special == .ifelse && x.nargtypes == 4 then
    if x.arg2Const then
      if x.arg2True then return .arg3
      else if x.arg2False then return .arg4
    else if x.arg2Bool && x.args34Egal then return .arg3
  else if x.special == .taskResultType && x.nargtypes == 2 && x.arg2Task then
    return .instanceof
  return .none_

/-- The branch `handle_cases!` takes: `handle_single_case!` on the one case, pushing a
`UnionSplit` with its two flags, giving up, or `add_flag!` with the new statement flag. -/
inductive HandleCasesResult where
  | single
  | unionSplit (handledAllCases fullyCovered : Bool)
  | none_
  | flags (f : UInt32)
  deriving Repr, DecidableEq, Inhabited

/-- `ncases` is `length(cases)`, `atypeDataType` is `isa(atype, DataType)`, `sigsDataType` lists
`isa(case.sig, DataType)` for the cases in order, `flag` is the statement's flag before.

Julia source: Compiler/src/ssair/inlining.jl:1578-1596
```julia
function handle_cases!(todo::Vector{Pair{Int,Any}}, ir::IRCode, idx::Int, stmt::Expr,
    @nospecialize(atype), cases::Vector{InliningCase}, handled_all_cases::Bool, fully_covered::Bool,
    joint_effects::Effects)
    # If we only have one case and that case is fully covered, we may either
    # be able to do the inlining now (for constant cases), or push it directly
    # onto the todo list
    if fully_covered && handled_all_cases && length(cases) == 1
        handle_single_case!(todo, ir, idx, stmt, cases[1].item)
    elseif length(cases) > 0 || handled_all_cases
        isa(atype, DataType) || return nothing
        for case in cases
            isa(case.sig, DataType) || return nothing
        end
        push!(todo, idx=>UnionSplit(handled_all_cases, fully_covered, atype, cases))
    else
        add_flag!(ir[SSAValue(idx)], flags_for_effects(joint_effects))
    end
    return nothing
end
```
`add_flag!(inst, flag)` is `inst[:flag] |= flag` (Compiler/src/ssair/ir.jl). -/
def handleCases (handledAllCases fullyCovered : Bool) (ncases : Nat) (atypeDataType : Bool)
    (sigsDataType : List Bool) (jointEffects : Effects) (flag : UInt32) : HandleCasesResult :=
  if fullyCovered && handledAllCases && ncases == 1 then .single
  else if ncases > 0 || handledAllCases then
    if !atypeDataType then .none_
    else if !sigsDataType.all id then .none_
    else .unionSplit handledAllCases fullyCovered
  else .flags (flag ||| flagsForEffects jointEffects)

/-- The result of `inline_const_if_inlineable!` and the instruction's flag after it.
`rtConst` is `inst[:type] isa Const`, `valInlineable` is `is_inlineable_constant(rt.val)`.

Julia source: Compiler/src/ssair/inlining.jl:1699-1707
```julia
function inline_const_if_inlineable!(inst::Instruction)
    rt = inst[:type]
    if rt isa Const && is_inlineable_constant(rt.val)
        inst[:stmt] = quoted(rt.val)
        return true
    end
    add_flag!(inst, IR_FLAGS_REMOVABLE)
    return false
end
```
-/
def inlineConstIfInlineable (rtConst valInlineable : Bool) (flag : UInt32) : Bool × UInt32 :=
  if rtConst && valInlineable then (true, flag)
  else (false, flag ||| IR_FLAGS_REMOVABLE)

/-- The terminator of the first block: a `ReturnNode` with its `val` defined, a `ReturnNode`
without (`unreachable`), or anything else. -/
inductive Terminator where
  | returnVal | returnUndef | other
  deriving Repr, DecidableEq, Inhabited

/-- `nblocks` is `length(ir.cfg.blocks)`; `term` describes
`ir[SSAValue(last(ir.cfg.blocks[1].stmts))][:stmt]`.

Julia source: Compiler/src/ssair/inlining.jl:1758-1764
```julia
function linear_inline_eligible(ir::IRCode)
    length(ir.cfg.blocks) == 1 || return false
    terminator = ir[SSAValue(last(ir.cfg.blocks[1].stmts))][:stmt]
    isa(terminator, ReturnNode) || return false
    isdefined(terminator, :val) || return false
    return true
end
```
-/
def linearInlineEligible (nblocks : Nat) (term : Terminator) : Bool :=
  if nblocks != 1 then false
  else match term with
    | .returnVal => true
    | .returnUndef => false
    | .other => false

/-! ## Call-site annotations and the decision to inline -/

/-- The `@inline`/`@noinline` bits `jl_code_info_set_ir` gives a statement. `regions` is the stack
`inline_flags` of enclosing call-site regions, outermost first: `true` for `@inline`
(`Expr(:inline, true)` pushes 1), `false` for `@noinline` (`Expr(:noinline, true)` pushes 0).

Julia source: src/method.c:480-483 and 612-615
```c
    // isempty(inline_flags): no user callsite inline annotation
    // last(inline_flags) == 1: callsite inline region
    // last(inline_flags) == 0: callsite noinline region
    arraylist_t *inline_flags = arraylist_new((arraylist_t*)malloc_s(sizeof(arraylist_t)), 0);
    ...
            if (inline_flags->len > 0) {
                void* inline_flag = inline_flags->items[inline_flags->len-1];
                flag |= 1 << (inline_flag ? 1 : 2);
            }
```
-/
def callsiteInlineBits (regions : List Bool) : UInt32 :=
  match regions.getLast? with
  | none => 0
  | some inl => (1 : UInt32) <<< (if inl then 1 else 2)

/-- What the inliner does with one call: replace it by a constant, call a compiled
specialization, or inline the source. -/
inductive Decision where
  | constant | compileable | inline
  deriving Repr, DecidableEq, Inhabited

/-- The decision of `resolve_todo`. `hasResult` is `call_result !== nothing`; `someCase` is
`get_local_code(call_result) isa SomeCase` (the local result is a constant); `inlining` is
`OptimizationParams(state.interp).inlining`; `src` is the source of the local result; `defIsMethod`,
`hasGenerator` and `mayInvokeGenerator` describe `mi` as for `srcInliningPolicyMI`. A
`compileable_specialization` is `compileable` (it may return `nothing`, which is not inlining
either).

Julia source: Compiler/src/ssair/inlining.jl:860-900
```julia
function resolve_todo(mi::MethodInstance, call_result::Union{Nothing,LocalInferenceResult},
    call_edge::Union{Nothing,MethodInstance,CodeInstance},
    @nospecialize(info::CallInfo), flag::UInt32, state::InliningState)
    et = InliningEdgeTracker(state)
    target = call_edge === nothing ? mi : call_edge

    if call_result === nothing
        # there is no cached source available for this, but there might be code for the compilation sig
        item = compileable_specialization(target, Effects(), et, info, state)
        (edge bookkeeping)
        return item
    end

    (edge bookkeeping)
    inferred_result = get_local_code(call_result)
    if inferred_result isa SomeCase
        return ConstantCase(inferred_result.val)
    end
    (; src, effects) = inferred_result

    # the duplicated check might have been done already within `analyze_method!`, but still
    # we need it here too since we may come here directly using a constant-prop' result
    if !OptimizationParams(state.interp).inlining || is_stmt_noinline(flag)
        return compileable_specialization(target, effects, et, info, state)
    end

    src_inlining_policy(state.interp, mi, src, info, flag) ||
        return compileable_specialization(target, effects, et, info, state)

    ir, spec_info, debuginfo = retrieve_ir_for_inlining(mi, src, true)
    return InliningTodo(mi, ir, spec_info, debuginfo, effects)
end
```
-/
def resolveTodoDecision (hasResult someCase inlining : Bool) (flag : UInt32)
    (defIsMethod hasGenerator mayInvokeGenerator : Bool) (src : Src) : Decision :=
  if !hasResult then .compileable
  else if someCase then .constant
  else if !inlining || isStmtNoinline flag then .compileable
  else if srcInliningPolicyMI defIsMethod hasGenerator mayInvokeGenerator src flag then .inline
  else .compileable

/-- The decision of `semiconcrete_result_item`. `declaredNoinline` is
`is_declared_noinline(mi.def::Method)` (the method's source carries `@noinline`); the source is
the `IRCode` of the semi-concrete result.

Julia source: Compiler/src/ssair/inlining.jl:1517-1538
```julia
function semiconcrete_result_item(result::SemiConcreteResult,
        @nospecialize(info::CallInfo), flag::UInt32, state::InliningState)
    code = result.edge
    mi = get_ci_mi(code)
    (edge bookkeeping)

    if (!OptimizationParams(state.interp).inlining || is_stmt_noinline(flag) ||
        # For `NativeInterpreter`, `SemiConcreteResult` may be produced for
        # a `@noinline`-declared method when it's marked as `@constprop :aggressive`.
        # Suppress the inlining here (unless inlining is requested at the callsite).
        (is_declared_noinline(mi.def::Method) && !is_stmt_inline(flag)))
        return compileable_specialization(code, result.effects, et, info, state)
    end
    src_inlining_policy(state.interp, mi, result.ir, info, flag) ||
        return compileable_specialization(code, result.effects, et, info, state)

    preserve_local_sources = OptimizationParams(state.interp).preserve_local_sources
    ir, _, debuginfo = retrieve_ir_for_inlining(mi, result.ir, preserve_local_sources)
    return InliningTodo(mi, ir, result.spec_info, debuginfo, result.effects)
end
```
-/
def semiconcreteDecision (inlining : Bool) (flag : UInt32) (declaredNoinline : Bool)
    (defIsMethod hasGenerator mayInvokeGenerator : Bool) : Decision :=
  if !inlining || isStmtNoinline flag || (declaredNoinline && !isStmtInline flag) then .compileable
  else if srcInliningPolicyMI defIsMethod hasGenerator mayInvokeGenerator .irCode flag then .inline
  else .compileable

end JuliaLean.Compiler.Inlining
