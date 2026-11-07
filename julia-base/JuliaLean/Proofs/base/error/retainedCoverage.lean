import JuliaLean.base.error


namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

def ErrorRuntimeExact : Prop :=
  (∀ parts, errorFromParts parts = String.intercalate "" parts) ∧
  (∀ entries, backtraceFromRuntime entries = reformatBacktrace entries) ∧
  (∀ keywordType argumentTypes,
    keywordMethodError keywordType argumentTypes =
      "MethodError(Core.kwcall," ++ keywordType ++ "," ++ argumentTypes ++ ")") ∧
  (∀ name condition code extra,
    systemError name condition code extra =
      if condition then .raised name code extra else .skipped) ∧
  (∀ entries, reformatBacktrace entries =
    match entries with
    | [] => .ok []
    | .unknownTag tag :: _ => .error s!"Unexpected extended backtrace entry tag {tag}"
    | entry :: rest => reformatBacktrace rest >>= fun tail => .ok (entry :: tail))

theorem errorRuntimeExact : ErrorRuntimeExact := by
  repeat' apply And.intro
  all_goals try (intros; rfl)
  · intro entries
    cases entries with
    | nil => rfl
    | cons head tail => cases head <;> rfl

def RetryExact : Prop :=
  (∀ backoff, makeBackoff backoff =
    if validBackoff backoff then .ok backoff else .error "all inputs must be non-negative") ∧
  (∀ backoff state randomTerm,
    iterateBackoff backoff state randomTerm =
      if state.1 < 1 then none else some (state.2, (state.1 - 1,
        min backoff.maxDelay (state.2 * backoff.factor * randomTerm)))) ∧
  (∀ backoff, backoffLength backoff = backoff.count) ∧
  backoffElementType = "Float64" ∧
  (∀ attempts, retryTrace attempts =
    match attempts with
    | [] => { calls := 1, sleeps := 0, result := false }
    | .success :: _ => { calls := 1, sleeps := 0, result := true }
    | .failure false :: _ => { calls := 1, sleeps := 0, result := false }
    | .failure true :: rest =>
        let tail := retryTrace rest
        { calls := tail.calls + 1, sleeps := tail.sleeps + 1, result := tail.result })

theorem retryExact : RetryExact := by
  repeat' apply And.intro
  all_goals try (intros; rfl)
  · intro attempts
    cases attempts with
    | nil => rfl
    | cons head tail =>
        cases head with
        | success => rfl
        | failure retry => cases retry <;> rfl

end JuliaLean.ErrorShow.Coverage
