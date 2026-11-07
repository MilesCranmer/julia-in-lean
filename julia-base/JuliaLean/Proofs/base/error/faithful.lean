import JuliaLean.Proofs.base.error.retainedCoverage

/-!
Method-specific models for every active definition in `base/error.jl` at Julia
`bbfa0ce4150`. Each proposition is attached only to the method whose body its
model replays.
-/

namespace JuliaLean.ErrorShow.ErrorFaithful

open JuliaLean.ErrorShow.Coverage



def ErrorVarargExact : Prop := ∀ arguments,
  errorVararg arguments = match arguments with
  | [] => .error ""
  | [argument] => if argument.isString then .error argument.text else .error "MethodError(ErrorException)"
  | arguments => .error (String.intercalate "" (arguments.map (·.text)))

theorem errorVarargExact : ErrorVarargExact := by
  unfold ErrorVarargExact
  intro arguments
  cases arguments with
  | nil => rfl
  | cons head tail => cases tail <;> rfl



def RethrowCurrentExact : Prop := ∀ _unit : Unit, rethrowCurrent = .current
theorem rethrowCurrentExact : RethrowCurrentExact := by unfold RethrowCurrentExact; intros; rfl

def RethrowReplacementExact : Prop := ∀ exception,
  rethrowReplacement exception = .replacement exception
theorem rethrowReplacementExact : RethrowReplacementExact := by unfold RethrowReplacementExact; intros; rfl





def ReformatBacktraceExact : Prop := ∀ entries,
  reformatBacktrace entries = match entries with
  | [] => .ok []
  | .native pointer :: rest =>
      reformatBacktrace rest >>= fun tail => .ok (.native pointer :: tail)
  | .extended tag header managedCount _ code moduleId :: rest =>
      if tag = 1 then
        let moduleId := if managedCount = 2 then moduleId else none
        reformatBacktrace rest >>= fun tail =>
          .ok (.interpreter { code, statement := header, moduleId } :: tail)
      else .error s!"Unexpected extended backtrace entry tag {tag}"

theorem reformatBacktraceExact : ReformatBacktraceExact := by
  intro entries
  cases entries with
  | nil => rfl
  | cons head rest => cases head <;> rfl



def BacktraceExact : Prop := ∀ runtimeEntries,
  backtrace runtimeEntries = reformatBacktrace runtimeEntries
theorem backtraceExact : BacktraceExact := by unfold BacktraceExact; intros; rfl

def CatchBacktraceExact : Prop := ∀ runtimeEntries,
  catchBacktrace runtimeEntries = reformatBacktrace runtimeEntries
theorem catchBacktraceExact : CatchBacktraceExact := by unfold CatchBacktraceExact; intros; rfl




def CurrentExceptionsExact : Prop := ∀ withBacktrace rawNewestFirst,
  currentExceptions withBacktrace rawNewestFirst =
    rawNewestFirst.reverse.map fun record =>
      { exception := record.exception
        backtrace := if withBacktrace then some (reformatBacktrace record.rawBacktrace) else none }

theorem currentExceptionsExact : CurrentExceptionsExact := by unfold CurrentExceptionsExact; intros; rfl



def KeywordErrorExact : Prop := ∀ keywordTuple arguments world,
  keywordError keywordTuple arguments world =
    .error s!"MethodError(Core.kwcall,{keywordTuple},{String.intercalate "," arguments},{world})"
theorem keywordErrorExact : KeywordErrorExact := by unfold KeywordErrorExact; intros; rfl




def SystemErrorIfExact : Prop := ∀ functionName condition errno extra,
  systemErrorIf functionName condition errno extra =
    if condition then .error s!"SystemError({functionName},{errno},{extra})" else .ok none
theorem systemErrorIfExact : SystemErrorIfExact := by unfold SystemErrorIfExact; intros; rfl

def SystemErrorNowExact : Prop := ∀ functionName errno extra,
  systemErrorNow functionName errno extra = .error s!"SystemError({functionName},{errno},{extra})"
theorem systemErrorNowExact : SystemErrorNowExact := by unfold SystemErrorNowExact; intros; rfl




def AssertExpansionExact : Prop := ∀ condition message,
  assertExpansion condition message =
    if condition then .ok () else .error ("AssertionError: " ++ assertMessage message)
theorem assertExpansionExact : AssertExpansionExact := by unfold AssertExpansionExact; intros; rfl

def AssertToStringExact : Prop := ∀ compilerBarrierResult,
  assertToString compilerBarrierResult = compilerBarrierResult
theorem assertToStringExact : AssertToStringExact := by unfold AssertToStringExact; intros; rfl


def BootstrapAssertToStringExact : Prop := ∀ baseDefined baseString printed,
  bootstrapAssertToString baseDefined baseString printed =
    if baseDefined then (baseString, [])
    else ("Error during bootstrap. See stdout.", [printed])
theorem bootstrapAssertToStringExact : BootstrapAssertToStringExact := by unfold BootstrapAssertToStringExact; intros; rfl



def BackoffConstructorExact : Prop := ∀ count firstDelay maxDelay factor jitter,
  makeBackoff count firstDelay maxDelay factor jitter =
    if 0 ≤ count && 0 ≤ firstDelay && 0 ≤ maxDelay && 0 ≤ factor && 0 ≤ jitter then
      .ok { count, firstDelay, maxDelay, factor, jitter }
    else .error "all inputs must be non-negative"
theorem backoffConstructorExact : BackoffConstructorExact := by unfold BackoffConstructorExact; intros; rfl


def DefaultBackoffExact : Prop := ∀ count firstDelay maxDelay factor jitter,
  defaultBackoff count firstDelay maxDelay factor jitter =
    makeBackoff count firstDelay maxDelay factor jitter
theorem defaultBackoffExact : DefaultBackoffExact := by unfold DefaultBackoffExact; intros; rfl


def IterateBackoffExact : Prop := ∀ backoff state randomSample,
  iterateBackoff backoff state randomSample =
    if state.1 < 1 then none
    else some (state.2, (state.1 - 1,
      min backoff.maxDelay (state.2 * backoff.factor *
        (1 - backoff.jitter + randomSample * 2 * backoff.jitter))))
theorem iterateBackoffExact : IterateBackoffExact := by unfold IterateBackoffExact; intros; rfl

def BackoffLengthExact : Prop := ∀ backoff, backoffLength backoff = backoff.count
theorem backoffLengthExact : BackoffLengthExact := by unfold BackoffLengthExact; intros; rfl

def BackoffElementTypeExact : Prop := ∀ backoff, backoffElementType backoff = "Float64"
theorem backoffElementTypeExact : BackoffElementTypeExact := by unfold BackoffElementTypeExact; intros; rfl




def RetryExact : Prop :=
  (∀ delays attempts, retry delays attempts =
    match attempts with
    | [] => { result := .error "missing final attempt", calls := 0, sleeps := 0, sleptDelays := [] }
    | _ => retry.loop delays attempts) ∧
  (∀ delays attempts, retry.loop delays attempts =
    match delays, attempts with
    | _, [] => { result := .error "missing final attempt", calls := 0, sleeps := 0, sleptDelays := [] }
    | [], .success value :: _ => { result := .ok value, calls := 1, sleeps := 0, sleptDelays := [] }
    | [], .failure exception _ :: _ => { result := .error exception, calls := 1, sleeps := 0, sleptDelays := [] }
    | _ :: _, [.success value] => { result := .ok value, calls := 1, sleeps := 0, sleptDelays := [] }
    | _ :: _, [.failure exception _] => { result := .error exception, calls := 1, sleeps := 0, sleptDelays := [] }
    | _ :: _, .success value :: _ => { result := .ok value, calls := 1, sleeps := 0, sleptDelays := [] }
    | _ :: _, .failure exception false :: _ => { result := .error exception, calls := 1, sleeps := 0, sleptDelays := [] }
    | delay :: restDelays, .failure _ true :: restAttempts =>
        let tail := retry.loop restDelays restAttempts
        { result := tail.result, calls := tail.calls + 1, sleeps := tail.sleeps + 1,
          sleptDelays := delay :: tail.sleptDelays })

theorem retryExact : RetryExact := by
  constructor
  · intro delays attempts
    cases attempts <;> rfl
  · intro delays attempts
    cases delays with
    | nil =>
        cases attempts with
        | nil => rfl
        | cons attempt rest => cases attempt <;> rfl
    | cons delay restDelays =>
        cases attempts with
        | nil => rfl
        | cons attempt rest =>
            cases rest with
            | nil => cases attempt <;> rfl
            | cons next more => cases attempt with
              | success value => rfl
              | failure exception allowed => cases allowed <;> rfl

end JuliaLean.ErrorShow.ErrorFaithful
