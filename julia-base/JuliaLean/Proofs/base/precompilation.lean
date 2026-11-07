import JuliaLean.base.precompilation
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.precompilation

open JuliaLean JuliaLean.base.precompilation JuliaLean.Registry

/-- Every compilation job has exactly one of the six compilation states. -/
def JobStatusPartition : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf),
    ([is_pending j, is_started j, is_recompiled j, is_soft_error j,
      is_failed j, is_dep_failed j].filter (· == true)).length = 1

def PositivePidOnly : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf), has_pid j = true ↔ 0 < j.pid.val

def HistoricalPidObservation : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf), had_pid j = true ↔ j.had_pid = true

def LockHolderObservation : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf),
    is_locked j = true ↔ ∃ head tail, j.lock_holder = head :: tail

def WaitingObservation : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf), is_waiting j = true ↔ j.waiting_for_bg = true

/-- Terminal counters and process information are independent of compilation status updates. -/
def RuntimeFieldsPreserved {Buf : Type} (before after : PrecompileJob Buf) : Prop :=
  after.started_at = before.started_at ∧ after.output = before.output ∧
  after.pid = before.pid ∧ after.had_pid = before.had_pid ∧
  after.lock_holder = before.lock_holder ∧ after.waiting_for_bg = before.waiting_for_bg ∧
  after.verbose_timing = before.verbose_timing ∧ after.peak_rss_bytes = before.peak_rss_bytes

def RecompiledUpdate : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf),
    let (returned, after) := mark_recompiled_result j
    returned = .JOB_RECOMPILED ∧ is_recompiled after = true ∧
    after.error_msg = j.error_msg ∧ RuntimeFieldsPreserved j after

def SoftErrorUpdate : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf),
    let (returned, after) := mark_soft_error_result j
    returned = .JOB_SOFT_ERROR ∧ is_soft_error after = true ∧
    after.error_msg = j.error_msg ∧ RuntimeFieldsPreserved j after

def FailedUpdate : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf) (message : Bytes),
    let (returned, after) := mark_failed_result j message
    returned = message ∧ is_failed after = true ∧
    after.error_msg = message ∧ RuntimeFieldsPreserved j after

def DependencyFailedUpdate : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf) (root : Bytes),
    let (returned, after) := mark_dep_failed_result j root
    returned = root ∧ is_dep_failed after = true ∧
    after.error_msg = root ∧ RuntimeFieldsPreserved j after

def PidUpdate : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf) (pid : JInt .i32),
    let (returned, after) := set_pid_result j pid
    returned = true ∧ after.pid.val = pid.val ∧ had_pid after = true ∧
    after.status = j.status ∧ after.started_at = j.started_at ∧
    after.error_msg = j.error_msg ∧ after.output = j.output ∧
    after.lock_holder = j.lock_holder ∧ after.waiting_for_bg = j.waiting_for_bg ∧
    after.verbose_timing = j.verbose_timing ∧ after.peak_rss_bytes = j.peak_rss_bytes

def ClearedPidRetainsHistory : Prop :=
  ∀ (Buf : Type) (j : PrecompileJob Buf),
    let (returned, after) := clear_pid_result j
    returned.val = 0 ∧ has_pid after = false ∧ after.had_pid = j.had_pid ∧
    after.status = j.status ∧ after.started_at = j.started_at ∧
    after.error_msg = j.error_msg ∧ after.output = j.output ∧
    after.lock_holder = j.lock_holder ∧ after.waiting_for_bg = j.waiting_for_bg ∧
    after.verbose_timing = j.verbose_timing ∧ after.peak_rss_bytes = j.peak_rss_bytes

/-- The timing header names the total, inclusion, dependency, compilation, method-count,
image-generation, cache-size and peak-memory columns. -/
def TimingHeaderColumns : Prop :=
  format_verbose_timing_header =
    lit "   total │ include   (deps)   (comp) │ methods  img-gen     cache  ~pk-rss"

/-- Formatting does not hide a rounding error or replace it with a padding error. -/
def TimingRoundingFailure : Prop :=
  ∀ (T Rounded Padded Result Error : Type)
    (roundDigits : T → JInt64 → Except Error Rounded)
    (lpad : Rounded → JInt64 → Except Error Padded)
    (string : Padded → Bytes → Except Error Result) (t : T) (error : Error),
    roundDigits t (ji 1) = .error error →
    timing_string_selected roundDigits lpad string t = .error error

/-- Padding failure is propagated after successful rounding, before final string assembly. -/
def TimingPaddingFailure : Prop :=
  ∀ (T Rounded Padded Result Error : Type)
    (roundDigits : T → JInt64 → Except Error Rounded)
    (lpad : Rounded → JInt64 → Except Error Padded)
    (string : Padded → Bytes → Except Error Result) (t : T) (rounded : Rounded) (error : Error),
    roundDigits t (ji 1) = .ok rounded →
    lpad rounded (ji 6) = .error error →
    timing_string_selected roundDigits lpad string t = .error error

def appendMessage {Result : Type} (returned : Result) (_io : Unit) (message : Bytes) :
    StateM Bytes Result := do
  modify (· ++ message)
  pure returned

/-- Error display writes the message verbatim and retains the selected printer's return value. -/
def ErrorMessageOutput : Prop :=
  ∀ (Result : Type) (returned : Result) (err : PkgPrecompileError) (before : Bytes),
    (showerror_PkgPrecompileError (appendMessage returned) () err).run before =
      (returned, before ++ err.msg)

/-- Supplying a backtrace never adds stack frames to this error's displayed message. -/
def ErrorBacktraceHidden : Prop :=
  ∀ (BT Result : Type) (bt : BT) (returned : Result) (err : PkgPrecompileError) (before : Bytes),
    (showerror_PkgPrecompileError_bt (appendMessage returned) () err bt).run before =
      (returned, before ++ err.msg)

/-- Interactive error display includes its type label before the original message. -/
def ErrorShowLabel : Prop :=
  ∀ (Result : Type) (returned : Result) (err : PkgPrecompileError) (before : Bytes),
    (show_PkgPrecompileError_selected
      (fun io label message => appendMessage returned io (label ++ message)) () err).run before =
      (returned, before ++ lit "PkgPrecompileError: " ++ err.msg)

theorem jobStatusPartition_proven : JobStatusPartition := by
  intro Buf j
  cases h : j.status <;>
    simp [is_pending, is_started, is_recompiled, is_soft_error, is_failed, is_dep_failed, h]

theorem positivePidOnly_proven : PositivePidOnly := by
  intro Buf j
  simp [has_pid]

theorem historicalPidObservation_proven : HistoricalPidObservation := by
  intro Buf j
  rfl

theorem lockHolderObservation_proven : LockHolderObservation := by
  intro Buf j
  cases h : j.lock_holder <;> simp [is_locked, h]

theorem waitingObservation_proven : WaitingObservation := by
  intro Buf j
  rfl

theorem recompiledUpdate_proven : RecompiledUpdate := by
  intro Buf j
  simp [mark_recompiled_result, is_recompiled, RuntimeFieldsPreserved]

theorem softErrorUpdate_proven : SoftErrorUpdate := by
  intro Buf j
  simp [mark_soft_error_result, is_soft_error, RuntimeFieldsPreserved]

theorem failedUpdate_proven : FailedUpdate := by
  intro Buf j message
  simp [mark_failed_result, is_failed, RuntimeFieldsPreserved]

theorem dependencyFailedUpdate_proven : DependencyFailedUpdate := by
  intro Buf j root
  simp [mark_dep_failed_result, is_dep_failed, RuntimeFieldsPreserved]

theorem pidUpdate_proven : PidUpdate := by
  intro Buf j pid
  simp [set_pid_result, had_pid]

theorem clearedPidRetainsHistory_proven : ClearedPidRetainsHistory := by
  intro Buf j
  have zero : (JInt.wrap .i32 0).val = 0 := by
    change wrapInt .i32 0 = 0
    exact wrapInt_of_inRange .i32 0 (by
      change -2147483648 ≤ (0 : Int) ∧ (0 : Int) ≤ 2147483647
      omega)
  simp [clear_pid_result, has_pid, zero]

theorem timingHeaderColumns_proven : TimingHeaderColumns := rfl

theorem timingRoundingFailure_proven : TimingRoundingFailure := by
  intro T Rounded Padded Result Error roundDigits lpad string t error failure
  simp [timing_string_selected, failure, bind, Except.bind]

theorem timingPaddingFailure_proven : TimingPaddingFailure := by
  intro T Rounded Padded Result Error roundDigits lpad string t rounded error success failure
  simp [timing_string_selected, success, failure, bind, Except.bind]

theorem errorMessageOutput_proven : ErrorMessageOutput := by
  intro Result returned err before
  rfl

theorem errorBacktraceHidden_proven : ErrorBacktraceHidden := by
  intro BT Result bt returned err before
  rfl

theorem errorShowLabel_proven : ErrorShowLabel := by
  intro Result returned err before
  exact congrArg (fun bytes => (returned, bytes)) (List.append_assoc _ _ _).symm


def entries : List Entry := [
  { id := "precompilation-job-status-partition", juliaFile := "base/precompilation.jl"
    juliaFns := ["is_pending", "is_started", "is_recompiled", "is_soft_error", "is_failed", "is_dep_failed"]
    statement := "Every job is in exactly one of the six compilation states."
    source := "base/precompilation.jl:186-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``JobStatusPartition, thm := some ``jobStatusPartition_proven },
  { id := "precompilation-positive-pid-only", juliaFile := "base/precompilation.jl"
    juliaFns := ["has_pid"]
    statement := "A job has a running process exactly when its signed process id is positive."
    source := "base/precompilation.jl:192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PositivePidOnly, thm := some ``positivePidOnly_proven },
  { id := "precompilation-historical-pid-observation", juliaFile := "base/precompilation.jl"
    juliaFns := ["had_pid"]
    statement := "The process-history query reports the sticky had_pid flag independently of the current process id."
    source := "base/precompilation.jl:193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``HistoricalPidObservation, thm := some ``historicalPidObservation_proven },
  { id := "precompilation-lock-holder-observation", juliaFile := "base/precompilation.jl"
    juliaFns := ["is_locked"]
    statement := "A job is reported locked exactly when its lock-holder name is nonempty."
    source := "base/precompilation.jl:194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``LockHolderObservation, thm := some ``lockHolderObservation_proven },
  { id := "precompilation-waiting-observation", juliaFile := "base/precompilation.jl"
    juliaFns := ["is_waiting"]
    statement := "The waiting query reports the background-precompilation waiting flag."
    source := "base/precompilation.jl:195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``WaitingObservation, thm := some ``waitingObservation_proven },
  { id := "precompilation-recompiled-update", juliaFile := "base/precompilation.jl"
    juliaFns := ["mark_recompiled!"]
    statement := "Marking a job recompiled returns JOB_RECOMPILED, updates its status, and preserves its error message and runtime fields."
    source := "base/precompilation.jl:198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``RecompiledUpdate, thm := some ``recompiledUpdate_proven },
  { id := "precompilation-soft-error-update", juliaFile := "base/precompilation.jl"
    juliaFns := ["mark_soft_error!"]
    statement := "Marking a soft error returns JOB_SOFT_ERROR, updates the status, and preserves its message and runtime fields."
    source := "base/precompilation.jl:199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``SoftErrorUpdate, thm := some ``softErrorUpdate_proven },
  { id := "precompilation-failed-update", juliaFile := "base/precompilation.jl"
    juliaFns := ["mark_failed!"]
    statement := "Marking failure returns and stores the supplied message, sets failure status, and preserves runtime fields."
    source := "base/precompilation.jl:200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``FailedUpdate, thm := some ``failedUpdate_proven },
  { id := "precompilation-dependency-failed-update", juliaFile := "base/precompilation.jl"
    juliaFns := ["mark_dep_failed!"]
    statement := "Marking dependency failure returns and stores the root package name, sets dependency-failure status, and preserves runtime fields."
    source := "base/precompilation.jl:202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``DependencyFailedUpdate, thm := some ``dependencyFailedUpdate_proven },
  { id := "precompilation-pid-update", juliaFile := "base/precompilation.jl"
    juliaFns := ["set_pid!"]
    statement := "Setting a process id returns true, stores that signed id, sets the sticky process-history flag, and preserves unrelated fields."
    source := "base/precompilation.jl:203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PidUpdate, thm := some ``pidUpdate_proven },
  { id := "precompilation-cleared-pid-retains-history", juliaFile := "base/precompilation.jl"
    juliaFns := ["clear_pid!"]
    statement := "Clearing a process id returns Int32 zero, removes the running-process indication, and preserves the sticky history flag and unrelated fields."
    source := "base/precompilation.jl:204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ClearedPidRetainsHistory, thm := some ``clearedPidRetainsHistory_proven },
  { id := "precompilation-timing-header-columns", juliaFile := "base/precompilation.jl"
    juliaFns := ["format_verbose_timing_header"]
    statement := "The verbose timing header labels each displayed timing, method-count, cache-size and peak-memory column."
    source := "base/precompilation.jl:442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TimingHeaderColumns, thm := some ``timingHeaderColumns_proven },
  { id := "precompilation-timing-rounding-failure", juliaFile := "base/precompilation.jl"
    juliaFns := ["timing_string"]
    statement := "Timing formatting propagates the selected rounding operation's error before padding or string assembly, for every input type."
    source := "base/precompilation.jl:382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TimingRoundingFailure, thm := some ``timingRoundingFailure_proven },
  { id := "precompilation-timing-padding-failure", juliaFile := "base/precompilation.jl"
    juliaFns := ["timing_string"]
    statement := "After rounding succeeds, timing formatting propagates padding failure before final string assembly."
    source := "base/precompilation.jl:382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TimingPaddingFailure, thm := some ``timingPaddingFailure_proven },
  { id := "precompilation-error-message-output", juliaFile := "base/precompilation.jl"
    juliaFns := ["Base.showerror(::IO, ::PkgPrecompileError)"]
    statement := "Error display writes the original message verbatim and preserves the selected printer's return value."
    source := "base/precompilation.jl:359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ErrorMessageOutput, thm := some ``errorMessageOutput_proven },
  { id := "precompilation-error-backtrace-hidden", juliaFile := "base/precompilation.jl"
    juliaFns := ["Base.showerror(::IO, ::PkgPrecompileError, bt; kw...)"]
    statement := "Error display with a backtrace writes only the original message, without stack frames."
    source := "base/precompilation.jl:360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ErrorBacktraceHidden, thm := some ``errorBacktraceHidden_proven },
  { id := "precompilation-error-show-label", juliaFile := "base/precompilation.jl"
    juliaFns := ["Base.show(::IO, ::PkgPrecompileError)"]
    statement := "Interactive error display writes the PkgPrecompileError type label before the original message and preserves the printer's return value."
    source := "base/precompilation.jl:363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ErrorShowLabel, thm := some ``errorShowLabel_proven }
]

end JuliaLean.Proofs.base.precompilation

namespace JuliaLean.Proofs.base.precompilation

open JuliaLean JuliaLean.base.precompilation JuliaLean.Registry

/-- Fresh jobs are pending without a process, and each state query reads its
corresponding native status or record field. -/
def JobQueriesBodies : Prop :=
  ∀ (Buf : Type) (buf : Buf),
    (PrecompileJob.new buf).status = .JOB_PENDING ∧
    (PrecompileJob.new buf).pid.val = 0 ∧
    ∀ job : PrecompileJob Buf,
      (is_pending job = true ↔ job.status = .JOB_PENDING) ∧
      (is_started job = true ↔ job.status = .JOB_STARTED) ∧
      (is_recompiled job = true ↔ job.status = .JOB_RECOMPILED) ∧
      (is_soft_error job = true ↔ job.status = .JOB_SOFT_ERROR) ∧
      (is_failed job = true ↔ job.status = .JOB_FAILED) ∧
      (is_dep_failed job = true ↔ job.status = .JOB_DEP_FAILED) ∧
      (has_pid job = true ↔ 0 < job.pid.val) ∧
      had_pid job = job.had_pid ∧
      (is_locked job = true ↔ job.lock_holder ≠ []) ∧
      is_waiting job = job.waiting_for_bg

theorem jobQueriesBodies_proven : JobQueriesBodies := by
  intro Buf buf
  refine ⟨rfl, rfl, ?_⟩
  intro job
  cases status : job.status <;>
    simp [is_pending, is_started, is_recompiled, is_soft_error, is_failed,
      is_dep_failed, has_pid, had_pid, is_locked, is_waiting, status]

/-- A truncation boundary with the ordinary IOBuffer zero-length contract is
sufficient for clear_failure to clear the output as well as status and message.
The other job mutators preserve the requested native values exactly. -/
def JobUpdatesBodies : Prop :=
  (∀ (Buf : Type) (job : PrecompileJob Buf) time,
    (mark_started job time).status = .JOB_STARTED ∧
    (mark_started job time).started_at = time) ∧
  (∀ (Buf : Type) (job : PrecompileJob Buf),
    (mark_recompiled job).status = .JOB_RECOMPILED) ∧
  (∀ (Buf : Type) (job : PrecompileJob Buf),
    (mark_soft_error job).status = .JOB_SOFT_ERROR) ∧
  (∀ (Buf : Type) (job : PrecompileJob Buf) message,
    (mark_failed job message).status = .JOB_FAILED ∧
    (mark_failed job message).error_msg = message) ∧
  (∀ (Buf : Type) (job : PrecompileJob Buf) root,
    (mark_dep_failed job root).status = .JOB_DEP_FAILED ∧
    (mark_dep_failed job root).error_msg = root) ∧
  (∀ (Buf : Type) (job : PrecompileJob Buf) pid,
    (set_pid job pid).pid = pid ∧ (set_pid job pid).had_pid = true) ∧
  (∀ (Buf : Type) (job : PrecompileJob Buf), (clear_pid job).pid.val = 0) ∧
  (∀ (Buf : Type) (truncate0 : Buf → Except PError Buf) (bytes : Buf → Nat),
    (∀ buffer, ∃ empty, truncate0 buffer = .ok empty ∧ bytes empty = 0) →
    ∀ job : PrecompileJob Buf, ∃ cleared,
      clear_failure truncate0 job = .ok cleared ∧
      cleared.status = .JOB_PENDING ∧ cleared.error_msg = [] ∧ bytes cleared.output = 0)

theorem jobUpdatesBodies_proven : JobUpdatesBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Buf job time; exact ⟨rfl, rfl⟩
  · intro Buf job; rfl
  · intro Buf job; rfl
  · intro Buf job message; exact ⟨rfl, rfl⟩
  · intro Buf job root; exact ⟨rfl, rfl⟩
  · intro Buf job pid; exact ⟨rfl, rfl⟩
  · intro Buf job; rfl
  · intro Buf truncate0 bytes contract job
    obtain ⟨empty, run, size⟩ := contract job.output
    refine ⟨{ job with status := .JOB_PENDING, error_msg := [], output := empty }, ?_, rfl, rfl, size⟩
    simp [clear_failure, run, bind, Except.bind, pure, Except.pure]

def entriesRetired : List Entry := [
  { id := "runtimecov-precomp-job-state", juliaFile := "base/precompilation.jl",
    juliaFns := ["PrecompileJob", "is_pending", "is_started", "is_recompiled", "is_soft_error",
      "is_failed", "is_dep_failed", "has_pid", "had_pid", "is_locked", "is_waiting"],
    statement := "A new precompile job is pending with no process, and each query reads exactly its corresponding status or state field.",
    source := "base/precompilation.jl:183-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .proven, prop := ``JobQueriesBodies, thm := some ``jobQueriesBodies_proven },
  { id := "runtimecov-precomp-job-updates", juliaFile := "base/precompilation.jl",
    juliaFns := ["mark_started!", "mark_recompiled!", "mark_soft_error!", "mark_failed!",
      "mark_dep_failed!", "set_pid!", "clear_pid!", "clear_failure!"],
    statement := "Each job-state mutator changes the named fields, and clearing a failure restores pending status and empties the stored error and output.",
    source := "base/precompilation.jl:197-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .proven, prop := ``JobUpdatesBodies, thm := some ``jobUpdatesBodies_proven,
    notes := "The source-native buffer carrier is arbitrary. Clearing composes the explicit IOBuffer truncate-to-zero contract; no private job or buffer carrier is retained." }
]

end JuliaLean.Proofs.base.precompilation

namespace JuliaLean.Proofs.base.precompilation

open JuliaLean JuliaLean.base.precompilation JuliaLean.Registry

/-- Each optional cache contributes its native Int size when present. A failed
filesystem query stops the scan and preserves the previously accumulated size. -/
def CacheBytesBody : Prop :=
  ∀ (file : Bytes → Except PError Bool) (size : Bytes → Except PError (JInt .i64)) (jl : Bytes),
    (∀ error companion, file jl = .error error →
      _precompile_cache_bytes file size jl companion = .ok (JInt.wrap .i64 0)) ∧
    (∀ error companion, file jl = .ok true → size jl = .error error →
      _precompile_cache_bytes file size jl companion = .ok (JInt.wrap .i64 0)) ∧
    (∀ n, file jl = .ok true → size jl = .ok n →
      _precompile_cache_bytes file size jl none = .ok n) ∧
    (file jl = .ok false →
      _precompile_cache_bytes file size jl none = .ok (JInt.wrap .i64 0)) ∧
    (∀ so n m, file jl = .ok true → size jl = .ok n →
      file so = .ok true → size so = .ok m →
      _precompile_cache_bytes file size jl (some so) = .ok (JInt.wrap .i64 (n.val + m.val))) ∧
    (∀ so m, file jl = .ok false → file so = .ok true → size so = .ok m →
      _precompile_cache_bytes file size jl (some so) = .ok m) ∧
    (∀ so n, file jl = .ok true → size jl = .ok n → file so = .ok false →
      _precompile_cache_bytes file size jl (some so) = .ok n) ∧
    (∀ so, file jl = .ok false → file so = .ok false →
      _precompile_cache_bytes file size jl (some so) = .ok (JInt.wrap .i64 0)) ∧
    (∀ so n error, file jl = .ok true → size jl = .ok n →
      (file so = .error error ∨ file so = .ok true ∧ size so = .error error) →
      _precompile_cache_bytes file size jl (some so) = .ok n) ∧
    (∀ so error, file jl = .ok false →
      (file so = .error error ∨ file so = .ok true ∧ size so = .error error) →
      _precompile_cache_bytes file size jl (some so) = .ok (JInt.wrap .i64 0))

attribute [local simp] Except.bind Except.pure Except.tryCatch MonadExceptOf.tryCatch

theorem cacheBytesBody_proven : CacheBytesBody := by
  have wrapIdentity (n : JInt .i64) :
      JInt.wrap .i64 ((JInt.wrap .i64 0).val + n.val) = n := by
    apply Subtype.ext
    change wrapInt .i64 (0 + n.val) = n.val
    simpa only [Int.zero_add] using wrapInt_of_inRange .i64 n.val n.property
  intro file size jl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro error companion failure
    simp [ _precompile_cache_bytes, failure, pure, bind, tryCatch, tryCatchThe]
  · intro error companion present failure
    simp [ _precompile_cache_bytes, present, failure, pure, bind, tryCatch, tryCatchThe]
  · intro n present sized
    simp [ _precompile_cache_bytes, present, sized, pure, bind, tryCatch, tryCatchThe, wrapIdentity]
  · intro absent
    simp [ _precompile_cache_bytes, absent, pure, bind, tryCatch, tryCatchThe]
  · intro so n m present sized presentSo sizedSo
    simp [ _precompile_cache_bytes, present, sized, presentSo, sizedSo,
      pure, bind, tryCatch, tryCatchThe, wrapIdentity]
  · intro so m absent presentSo sizedSo
    simp [ _precompile_cache_bytes, absent, presentSo, sizedSo,
      pure, bind, tryCatch, tryCatchThe, wrapIdentity]
  · intro so n present sized absentSo
    simp [ _precompile_cache_bytes, present, sized, absentSo,
      pure, bind, tryCatch, tryCatchThe, wrapIdentity]
  · intro so absent absentSo
    simp [ _precompile_cache_bytes, absent, absentSo, pure, bind, tryCatch, tryCatchThe]
  · intro so n error present sized failure
    have total := wrapIdentity n
    rcases failure with query | ⟨query, sizedSo⟩ <;>
      simp_all [ _precompile_cache_bytes, pure, bind, tryCatch, tryCatchThe, wrapIdentity]
  · intro so error absent failure
    rcases failure with query | ⟨query, sizedSo⟩ <;>
      simp_all [ _precompile_cache_bytes, pure, bind, tryCatch, tryCatchThe]

/-- The progress boundary helpers emit the specified terminal-control bytes. -/
def ProgressBoundaryBodies : Prop :=
  ∀ (Io : Type) (io : Io) (progress : MiniProgressBar) (initial : Bytes),
    (start_progress (m := StateM Bytes) (fun _ bytes => modify (· ++ bytes)) io progress).run initial =
      ((), initial ++ lit "\x1b[?25l") ∧
    (end_progress (m := StateM Bytes) (fun _ bytes => modify (· ++ bytes)) io progress).run initial =
      ((), initial ++ lit "\x1b[?25h\x1b[2K") ∧
    (print_progress_bottom (m := StateM Bytes) (fun _ bytes => modify (· ++ bytes)) io).run initial =
      ((), initial ++ lit "\x1b[S\x1b[1A\x1b[2K\x1b[1G")

private theorem byteListLoop (bytes : ByteArray) (index : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bytes index acc = acc.reverse ++ bytes.data.toList.drop index := by
  fun_induction ByteArray.toList.loop bytes index acc with
  | case1 i r inside ih =>
    rw [ih, List.reverse_cons, List.append_assoc]
    have listInside : i < bytes.data.toList.length := by simpa using inside
    rw [List.drop_eq_getElem_cons listInside]
    simp only [List.singleton_append]
    congr 2
    simp [ByteArray.get!, inside]
  | case2 i r outside =>
    rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt outside), List.append_nil]

private theorem byteListData (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  unfold ByteArray.toList
  rw [byteListLoop]
  rfl

private theorem litAppend (left right : String) : lit left ++ lit right = lit (left ++ right) := by
  simp only [lit, String.toUTF8_eq_toByteArray, String.toByteArray_append,
    byteListData, ByteArray.toList_data_append]

theorem progressBoundaryBodies_proven : ProgressBoundaryBodies := by
  intro Io io progress initial
  refine ⟨rfl, ?_, ?_⟩
  · change ((), initial ++ (ansi_enablecursor ++ ansi_clearline)) = _
    have bytes : ansi_enablecursor ++ ansi_clearline = lit "\x1b[?25h\x1b[2K" := by
      unfold ansi_enablecursor ansi_clearline
      rw [litAppend]
      congr 1
    rw [bytes]
  have one : (JInt.wrap .i64 1).val = 1 := by
    change wrapInt .i64 1 = 1
    exact wrapInt_of_inRange .i64 1 (by
      change -9223372036854775808 ≤ (1 : Int) ∧ (1 : Int) ≤ 9223372036854775807
      omega)
  unfold print_progress_bottom ansi_moveup
  simp only [one]
  change ((), initial ++ (lit "\x1b[S" ++
    (lit "\x1b[" ++ lit (toString (1 : Int)) ++ lit "A") ++
      ansi_clearline ++ ansi_movecol1)) = _
  simp only [ansi_clearline, ansi_movecol1, litAppend]
  congr 2


def entriesMore : List Entry := [
  { id := "runtimecov-precomp-cache-bytes", juliaFile := "base/precompilation.jl",
    juliaFns := ["_precompile_cache_bytes"],
    statement := "Cache byte counting adds existing cache-file sizes with native Int arithmetic and preserves totals accumulated before a caught filesystem error.",
    source := "base/precompilation.jl:444-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .proven, prop := ``CacheBytesBody, thm := some ``cacheBytesBody_proven,
    notes := "The legacy Nat accumulator is replaced by the installed source method and native wrapping Int arithmetic. Both isfile and filesize exceptions are covered." },
  { id := "runtimecov-precomp-progress-boundaries", juliaFile := "base/precompilation.jl",
    juliaFns := ["start_progress", "end_progress", "print_progress_bottom"],
    statement := "Progress start, end and bottom helpers emit their fixed ANSI control sequences.",
    source := "base/precompilation.jl:486,538-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .proven, prop := ``ProgressBoundaryBodies, thm := some ``progressBoundaryBodies_proven }
]

end JuliaLean.Proofs.base.precompilation
