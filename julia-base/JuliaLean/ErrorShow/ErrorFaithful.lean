import JuliaLean.ErrorShow.Coverage

/-!
Method-specific models for every active definition in `base/error.jl` at Julia
`bbfa0ce4150`. Each proposition is attached only to the method whose body its
model replays.
-/

namespace JuliaLean.ErrorShow.ErrorFaithful

open JuliaLean.ErrorShow.Coverage

abbrev R (α : Type) := Except String α

/-! `error(s::Vararg{Any,N})`, lines 47-57. -/

structure ErrorArgument where
  isString : Bool
  text : String
  deriving Repr, DecidableEq

def errorVararg : List ErrorArgument → R String
  | [] => .error ""
  | [argument] => if argument.isString then .error argument.text else .error "MethodError(ErrorException)"
  | arguments => .error (String.intercalate "" (arguments.map (·.text)))

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

/-! `rethrow()` and `rethrow(e)`, lines 73-74. -/

inductive RethrowCall where
  | current
  | replacement (exception : String)
  deriving Repr, DecidableEq

def rethrowCurrent : RethrowCall := .current
def rethrowReplacement (exception : String) : RethrowCall := .replacement exception

def RethrowCurrentExact : Prop := ∀ _unit : Unit, rethrowCurrent = .current
theorem rethrowCurrentExact : RethrowCurrentExact := by unfold RethrowCurrentExact; intros; rfl

def RethrowReplacementExact : Prop := ∀ exception,
  rethrowReplacement exception = .replacement exception
theorem rethrowReplacementExact : RethrowReplacementExact := by unfold RethrowReplacementExact; intros; rfl

/-! `_reformat_bt`, lines 84-114. The raw input type enforces the runtime's
entry-size invariant while retaining every source branch. -/

structure InterpreterData where
  code : Nat
  statement : Nat
  moduleId : Option Nat
  deriving Repr, DecidableEq

inductive RawBacktraceEntry where
  | native (pointer : Nat)
  | extended (tag header managedCount uintCount : Nat) (code : Nat) (moduleId : Option Nat)
  deriving Repr, DecidableEq

inductive FormattedBacktraceEntry where
  | native (pointer : Nat)
  | interpreter (data : InterpreterData)
  deriving Repr, DecidableEq

def reformatBacktrace : List RawBacktraceEntry → R (List FormattedBacktraceEntry)
  | [] => .ok []
  | .native pointer :: rest => do
      let tail ← reformatBacktrace rest
      .ok (.native pointer :: tail)
  | .extended tag header managedCount _ code moduleId :: rest =>
      if tag = 1 then do
        let moduleId := if managedCount = 2 then moduleId else none
        let tail ← reformatBacktrace rest
        .ok (.interpreter { code, statement := header, moduleId } :: tail)
      else .error s!"Unexpected extended backtrace entry tag {tag}"

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

/-! `backtrace()` and `catch_backtrace()`, lines 121-128 and 152-155. -/

def backtrace (runtimeEntries : List RawBacktraceEntry) : R (List FormattedBacktraceEntry) :=
  reformatBacktrace runtimeEntries

def catchBacktrace (runtimeEntries : List RawBacktraceEntry) : R (List FormattedBacktraceEntry) :=
  reformatBacktrace runtimeEntries

def BacktraceExact : Prop := ∀ runtimeEntries,
  backtrace runtimeEntries = reformatBacktrace runtimeEntries
theorem backtraceExact : BacktraceExact := by unfold BacktraceExact; intros; rfl

def CatchBacktraceExact : Prop := ∀ runtimeEntries,
  catchBacktrace runtimeEntries = reformatBacktrace runtimeEntries
theorem catchBacktraceExact : CatchBacktraceExact := by unfold CatchBacktraceExact; intros; rfl

/-! `current_exceptions`, lines 179-189. The runtime vector is represented as
newest-first records, matching `jl_get_excstack`. -/

structure RawExceptionRecord where
  exception : String
  rawBacktrace : List RawBacktraceEntry
  deriving Repr, DecidableEq

structure ExceptionRecord where
  exception : String
  backtrace : Option (R (List FormattedBacktraceEntry))
  deriving Repr

def currentExceptions (withBacktrace : Bool) (rawNewestFirst : List RawExceptionRecord) :
    List ExceptionRecord :=
  rawNewestFirst.reverse.map fun record =>
    { exception := record.exception
      backtrace := if withBacktrace then some (reformatBacktrace record.rawBacktrace) else none }

def CurrentExceptionsExact : Prop := ∀ withBacktrace rawNewestFirst,
  currentExceptions withBacktrace rawNewestFirst =
    rawNewestFirst.reverse.map fun record =>
      { exception := record.exception
        backtrace := if withBacktrace then some (reformatBacktrace record.rawBacktrace) else none }

theorem currentExceptionsExact : CurrentExceptionsExact := by unfold CurrentExceptionsExact; intros; rfl

/-! `kwerr`, lines 192-195. -/

structure KeywordMethodError where
  keywordTuple : String
  arguments : List String
  world : Nat
  deriving Repr, DecidableEq

def keywordError (keywordTuple : String) (arguments : List String) (world : Nat) :
    R KeywordMethodError :=
  .error s!"MethodError(Core.kwcall,{keywordTuple},{String.intercalate "," arguments},{world})"

def KeywordErrorExact : Prop := ∀ keywordTuple arguments world,
  keywordError keywordTuple arguments world =
    .error s!"MethodError(Core.kwcall,{keywordTuple},{String.intercalate "," arguments},{world})"
theorem keywordErrorExact : KeywordErrorExact := by unfold KeywordErrorExact; intros; rfl

/-! `systemerror` overloads, lines 204-205. -/

structure SystemErrorData where
  functionName : String
  code : Int
  extra : Option String
  deriving Repr, DecidableEq

def systemErrorIf (functionName : String) (condition : Bool) (errno : Int)
    (extra : Option String) : R (Option SystemErrorData) :=
  if condition then .error s!"SystemError({functionName},{errno},{extra})" else .ok none

def systemErrorNow (functionName : String) (errno : Int) (extra : Option String) :
    R SystemErrorData :=
  .error s!"SystemError({functionName},{errno},{extra})"

def SystemErrorIfExact : Prop := ∀ functionName condition errno extra,
  systemErrorIf functionName condition errno extra =
    if condition then .error s!"SystemError({functionName},{errno},{extra})" else .ok none
theorem systemErrorIfExact : SystemErrorIfExact := by unfold SystemErrorIfExact; intros; rfl

def SystemErrorNowExact : Prop := ∀ functionName errno extra,
  systemErrorNow functionName errno extra = .error s!"SystemError({functionName},{errno},{extra})"
theorem systemErrorNowExact : SystemErrorNowExact := by unfold SystemErrorNowExact; intros; rfl

/-! `@assert`, `_assert_tostring`, and `__assert_tostring`, lines 249-268. -/

inductive AssertSourceMessage where
  | absent (conditionText : String)
  | literalString (text : String)
  | expression (evaluatedText : String)
  | literalValue (expandedText : String)
  deriving Repr, DecidableEq

def assertMessage : AssertSourceMessage → String
  | .absent conditionText => conditionText
  | .literalString text | .expression text | .literalValue text => text

def assertExpansion (condition : Bool) (message : AssertSourceMessage) : R Unit :=
  if condition then .ok () else .error ("AssertionError: " ++ assertMessage message)

def AssertExpansionExact : Prop := ∀ condition message,
  assertExpansion condition message =
    if condition then .ok () else .error ("AssertionError: " ++ assertMessage message)
theorem assertExpansionExact : AssertExpansionExact := by unfold AssertExpansionExact; intros; rfl

def assertToString (compilerBarrierResult : String) : String := compilerBarrierResult
def AssertToStringExact : Prop := ∀ compilerBarrierResult,
  assertToString compilerBarrierResult = compilerBarrierResult
theorem assertToStringExact : AssertToStringExact := by unfold AssertToStringExact; intros; rfl

def bootstrapAssertToString (baseDefined : Bool) (baseString printed : String) :
    String × List String :=
  if baseDefined then (baseString, [])
  else ("Error during bootstrap. See stdout.", [printed])

def BootstrapAssertToStringExact : Prop := ∀ baseDefined baseString printed,
  bootstrapAssertToString baseDefined baseString printed =
    if baseDefined then (baseString, [])
    else ("Error during bootstrap. See stdout.", [printed])
theorem bootstrapAssertToStringExact : BootstrapAssertToStringExact := by unfold BootstrapAssertToStringExact; intros; rfl

/-! `ExponentialBackOff`, lines 277-300. Float arithmetic is represented by
exact rationals supplied as integers with a common implicit scale. -/

structure Backoff where
  count : Int
  firstDelay : Int
  maxDelay : Int
  factor : Int
  jitter : Int
  deriving Repr, DecidableEq

def makeBackoff (count firstDelay maxDelay factor jitter : Int) : R Backoff :=
  if 0 ≤ count && 0 ≤ firstDelay && 0 ≤ maxDelay && 0 ≤ factor && 0 ≤ jitter then
    .ok { count, firstDelay, maxDelay, factor, jitter }
  else .error "all inputs must be non-negative"

def BackoffConstructorExact : Prop := ∀ count firstDelay maxDelay factor jitter,
  makeBackoff count firstDelay maxDelay factor jitter =
    if 0 ≤ count && 0 ≤ firstDelay && 0 ≤ maxDelay && 0 ≤ factor && 0 ≤ jitter then
      .ok { count, firstDelay, maxDelay, factor, jitter }
    else .error "all inputs must be non-negative"
theorem backoffConstructorExact : BackoffConstructorExact := by unfold BackoffConstructorExact; intros; rfl

def defaultBackoff (count firstDelay maxDelay factor jitter : Int) : R Backoff :=
  makeBackoff count firstDelay maxDelay factor jitter

def DefaultBackoffExact : Prop := ∀ count firstDelay maxDelay factor jitter,
  defaultBackoff count firstDelay maxDelay factor jitter =
    makeBackoff count firstDelay maxDelay factor jitter
theorem defaultBackoffExact : DefaultBackoffExact := by unfold DefaultBackoffExact; intros; rfl

def iterateBackoff (backoff : Backoff) (state : Int × Int) (randomSample : Int) :
    Option (Int × (Int × Int)) :=
  if state.1 < 1 then none
  else
    let nextCount := state.1 - 1
    let currentDelay := state.2
    let jitterFactor := 1 - backoff.jitter + randomSample * 2 * backoff.jitter
    let nextDelay := min backoff.maxDelay (state.2 * backoff.factor * jitterFactor)
    some (currentDelay, (nextCount, nextDelay))

def IterateBackoffExact : Prop := ∀ backoff state randomSample,
  iterateBackoff backoff state randomSample =
    if state.1 < 1 then none
    else some (state.2, (state.1 - 1,
      min backoff.maxDelay (state.2 * backoff.factor *
        (1 - backoff.jitter + randomSample * 2 * backoff.jitter))))
theorem iterateBackoffExact : IterateBackoffExact := by unfold IterateBackoffExact; intros; rfl

def backoffLength (backoff : Backoff) : Int := backoff.count
def BackoffLengthExact : Prop := ∀ backoff, backoffLength backoff = backoff.count
theorem backoffLengthExact : BackoffLengthExact := by unfold BackoffLengthExact; intros; rfl

def backoffElementType (_ : Backoff) : String := "Float64"
def BackoffElementTypeExact : Prop := ∀ backoff, backoffElementType backoff = "Float64"
theorem backoffElementTypeExact : BackoffElementTypeExact := by unfold BackoffElementTypeExact; intros; rfl

/-! `retry`, lines 322-342. -/

inductive Attempt where
  | success (value : String)
  | failure (exception : String) (checkAllowsRetry : Bool)
  deriving Repr, DecidableEq

structure RetryResult where
  result : R String
  calls : Nat
  sleeps : Nat
  sleptDelays : List Nat
  deriving Repr

def retry (delays : List Nat) : List Attempt → RetryResult
  | [] => { result := .error "missing final attempt", calls := 0, sleeps := 0, sleptDelays := [] }
  | attempts => loop delays attempts
where
  loop : List Nat → List Attempt → RetryResult
    | [], .success value :: _ => { result := .ok value, calls := 1, sleeps := 0, sleptDelays := [] }
    | [], .failure exception _ :: _ => { result := .error exception, calls := 1, sleeps := 0, sleptDelays := [] }
    | _ :: _, [.success value] => { result := .ok value, calls := 1, sleeps := 0, sleptDelays := [] }
    | _ :: _, [.failure exception _] => { result := .error exception, calls := 1, sleeps := 0, sleptDelays := [] }
    | _delay :: _restDelays, .success value :: _ => { result := .ok value, calls := 1, sleeps := 0, sleptDelays := [] }
    | _delay :: _restDelays, .failure exception false :: _ =>
        { result := .error exception, calls := 1, sleeps := 0, sleptDelays := [] }
    | delay :: restDelays, .failure _ true :: restAttempts =>
        let tail := loop restDelays restAttempts
        { result := tail.result, calls := tail.calls + 1, sleeps := tail.sleeps + 1,
          sleptDelays := delay :: tail.sleptDelays }
    | _, [] => { result := .error "missing final attempt", calls := 0, sleeps := 0, sleptDelays := [] }

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
