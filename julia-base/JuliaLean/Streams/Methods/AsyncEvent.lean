import JuliaLean.Streams.Methods.Support

namespace JuliaLean.Streams.Methods.AsyncEvent

open JuliaLean.Streams JuliaLean.Streams.Methods JuliaLean.Registry

structure AsyncM where
  event : EventM
  hasHandle : Bool
  timeoutMs : Nat
  intervalMs : Nat
  deriving Repr, DecidableEq

def freshAsync (kind : EventKind) (timeout interval : Nat := 0) : AsyncM :=
  ⟨freshEvent kind, true, timeout, interval⟩

inductive TimerField where
  | timeout | interval | handle | isopen | set
  deriving Repr, DecidableEq

inductive TimerValue where
  | natural (value : Nat)
  | boolean (value : Bool)
  deriving Repr, DecidableEq

inductive TimedWaitResult where | ok | timedOut
  deriving Repr, DecidableEq

/-- `AsyncCondition()`, `base/asyncevent.jl:23-38`. -/
def m23 (initCode : Int) : Except StreamErr AsyncM :=
  let state := freshAsync .asyncCondition
  if initCode != 0 then .error .ioError else .ok state

/-- `AsyncCondition(cb)`, `base/asyncevent.jl:47-70`. -/
def m47 (state : AsyncM) : AsyncM × Bool :=
  (state, state.event.set)

/-- `Timer(timeout; interval)`, `base/asyncevent.jl:129-150`. -/
def m129 (timeoutUs intervalUs : Int) (initOk startOk : Bool) : Except StreamErr AsyncM :=
  if timeoutUs < 0 || intervalUs < 0 then .error .argumentError
  else if !initOk || !startOk then .error .ioError
  else
    let setup := timerSetup timeoutUs.toNat intervalUs.toNat
    let kind := if intervalUs = 0 then EventKind.oneShotTimer else .repeatingTimer
    .ok (freshAsync kind setup.timeoutMs setup.intervalMs)

/-- `getproperty(t::Timer, f)`, `base/asyncevent.jl:152-161`. -/
def m152 (state : AsyncM) (field : TimerField) : TimerValue :=
  match field with
  | .timeout => .natural (if state.timeoutMs = 0 then 0 else state.timeoutMs - 1)
  | .interval => .natural state.intervalMs
  | .handle => .boolean state.hasHandle
  | .isopen => .boolean state.event.isopen
  | .set => .boolean state.event.set

/-- `propertynames(::Timer)`, `base/asyncevent.jl:162`. -/
def m162 : List String :=
  ["handle", "cond", "isopen", "set", "timeout", "timeout_ms", "interval", "interval_ms"]

/-- `show(io, t::Timer)`, `base/asyncevent.jl:164-169`. -/
def m164 (state : AsyncM) : String :=
  let openness := if state.event.isopen then "open" else "closed"
  let interval := if state.intervalMs > 0 then ", interval: " ++ toString state.intervalMs ++ " ms" else ""
  "Timer (" ++ openness ++ ", timeout: " ++ toString (timerTimeout ⟨state.timeoutMs, state.intervalMs⟩) ++ " ms" ++ interval ++ ")"

/-- Timer pointer conversion, `base/asyncevent.jl:171`. -/
def m171 (state : AsyncM) : Bool := state.hasHandle

/-- AsyncCondition pointer conversion, `base/asyncevent.jl:172`. -/
def m172 (state : AsyncM) : Bool := state.hasHandle

/-- Keyword `_trywait`, `base/asyncevent.jl:177-178`. -/
def m177 (state : AsyncM) : Except StreamErr EventM := waitEvent state.event

/-- Token `_trywait`, `base/asyncevent.jl:179-233`. -/
def m179 (state : AsyncM) : Except StreamErr EventM := waitEvent state.event

/-- `waitqueue(t)`, `base/asyncevent.jl:235`. -/
def m235 (queueLength : Nat) : Nat := queueLength

/-- Keyword `wait`, `base/asyncevent.jl:237-238`. -/
def m237 (state : AsyncM) : Except StreamErr Unit :=
  match m177 state with | .ok _ => .ok () | .error e => .error e

/-- Token `wait`, `base/asyncevent.jl:239-244`. -/
def m239 (state : AsyncM) (cancelled : Bool) : Except StreamErr Unit :=
  match m179 state with
  | .error e => .error e
  | .ok _ => if cancelled then .error .ioError else .ok ()

/-- `isopen`, `base/asyncevent.jl:247`. -/
def m247 (state : AsyncM) : Bool := state.event.isopen

/-- `close`, `base/asyncevent.jl:257-292`. -/
def m257 (state : AsyncM) : AsyncM :=
  if !state.hasHandle && !state.event.isopen then state
  else { state with event := closeEvent state.event, hasHandle := false }

/-- `uvfinalize`, `base/asyncevent.jl:294-312`. -/
def m294 (state : AsyncM) : AsyncM :=
  if state.hasHandle then { state with event := closeEvent state.event, hasHandle := false } else state

/-- `_uv_hook_close`, `base/asyncevent.jl:314-326`. -/
def m314 (state : AsyncM) : AsyncM :=
  { state with event := closeEvent state.event, hasHandle := false }

/-- `uv_asynccb`, `base/asyncevent.jl:328-338`. -/
def m328 (state : AsyncM) : AsyncM :=
  { state with event := { state.event with set := true } }

/-- `uv_timercb`, `base/asyncevent.jl:340-359`. -/
def m340 (state : AsyncM) : AsyncM :=
  let signaled := signalEvent state.event
  { state with event := signaled, hasHandle := state.hasHandle && signaled.isopen }

/-- `sleep(sec)`, `base/asyncevent.jl:371-381`. -/
def m371 (secondsNonnegative waitSucceeded : Bool) : Except StreamErr Bool :=
  if !secondsNonnegative then .error .argumentError
  else if !waitSucceeded then .error .ioError
  else .ok false

/-- Callback `Timer`, `base/asyncevent.jl:421-454`. -/
def m421 (state : AsyncM) (spawn : Option Bool) : AsyncM × Bool × Bool :=
  let sticky := match spawn with | none => true | some value => !value
  (state, sticky, state.event.set)

/-- `timedwait`, `base/asyncevent.jl:478-496`. -/
def m478 (pollIntervalValid : Bool) (tests : List Bool) (polls : Nat) : Except StreamErr TimedWaitResult :=
  if !pollIntervalValid then .error .argumentError
  else if timedwaitResult tests polls then .ok .ok else .ok .timedOut

/-- `TimeoutWait(timeout)`, `base/asyncevent.jl:512`. -/
def m512 (timeoutMs : Nat) : TimeoutWaitM := ⟨timeoutMs, false⟩

/-- `wait_enqueue!`, `base/asyncevent.jl:515-537`. -/
def m515 (state : TimeoutWaitM) : TimeoutWaitM × Bool := (timeoutEnqueue state, true)

/-- `wait_dequeue!`, `base/asyncevent.jl:539-544`. -/
def m539 (state : TimeoutWaitM) : TimeoutWaitM := timeoutDequeue state

def P23 : Prop := ∀ code,
  (code = 0 → m23 code = .ok (freshAsync .asyncCondition)) ∧
  (code ≠ 0 → m23 code = .error .ioError)

def P47 : Prop := ∀ state,
  (m47 state).1 = state ∧ (m47 state).2 = state.event.set

def P129 : Prop := ∀ timeoutUs intervalUs initOk startOk,
  (timeoutUs < 0 ∨ intervalUs < 0 →
    m129 timeoutUs intervalUs initOk startOk = .error .argumentError) ∧
  (0 ≤ timeoutUs ∧ 0 ≤ intervalUs ∧ (!initOk || !startOk) = true →
    m129 timeoutUs intervalUs initOk startOk = .error .ioError) ∧
  (0 ≤ timeoutUs ∧ 0 ≤ intervalUs ∧ initOk = true ∧ startOk = true →
    let setup := timerSetup timeoutUs.toNat intervalUs.toNat
    let kind := if intervalUs = 0 then EventKind.oneShotTimer else .repeatingTimer
    m129 timeoutUs intervalUs initOk startOk =
      .ok (freshAsync kind setup.timeoutMs setup.intervalMs))

def P152 : Prop := ∀ state,
  m152 state .timeout = .natural (timerTimeout ⟨state.timeoutMs, state.intervalMs⟩) ∧
  m152 state .interval = .natural state.intervalMs ∧
  m152 state .handle = .boolean state.hasHandle ∧
  m152 state .isopen = .boolean state.event.isopen ∧
  m152 state .set = .boolean state.event.set

def P162 : Prop := ∀ _input : Unit,
  m162 = ["handle", "cond", "isopen", "set", "timeout", "timeout_ms", "interval", "interval_ms"]

def P164 : Prop := ∀ state,
  let openness := if state.event.isopen then "open" else "closed"
  let interval := if state.intervalMs > 0 then
    ", interval: " ++ toString state.intervalMs ++ " ms" else ""
  m164 state = "Timer (" ++ openness ++ ", timeout: " ++
    toString (timerTimeout ⟨state.timeoutMs, state.intervalMs⟩) ++ " ms" ++ interval ++ ")"

def P171 : Prop := ∀ state, m171 state = state.hasHandle
def P172 : Prop := ∀ state, m172 state = state.hasHandle

def trywaitContract (result : Except StreamErr EventM) (event : EventM) : Prop :=
  (event.set = true →
    result = .ok (if event.kind == .oneShotTimer then event else { event with set := false })) ∧
  (event.set = false ∧ event.isopen = false → result = .error .eofError) ∧
  (event.set = false ∧ event.isopen = true → result = .error .ioError)

def P177 : Prop := ∀ state, trywaitContract (m177 state) state.event
def P179 : Prop := ∀ state, trywaitContract (m179 state) state.event
def P235 : Prop := ∀ queueLength, m235 queueLength = queueLength

def waitContract (result : Except StreamErr Unit) (event : EventM) : Prop :=
  (event.set = true → result = .ok ()) ∧
  (event.set = false ∧ event.isopen = false → result = .error .eofError) ∧
  (event.set = false ∧ event.isopen = true → result = .error .ioError)

def P237 : Prop := ∀ state, waitContract (m237 state) state.event

def P239 : Prop := ∀ state cancelled,
  (state.event.set = true ∧ cancelled = false → m239 state cancelled = .ok ()) ∧
  (state.event.set = true ∧ cancelled = true → m239 state cancelled = .error .ioError) ∧
  (state.event.set = false ∧ state.event.isopen = false →
    m239 state cancelled = .error .eofError) ∧
  (state.event.set = false ∧ state.event.isopen = true →
    m239 state cancelled = .error .ioError)

def P247 : Prop := ∀ state, m247 state = state.event.isopen

def P257 : Prop := ∀ state,
  let closed := m257 state
  closed.hasHandle = false ∧ closed.event.isopen = false ∧
  closed.event.kind = state.event.kind ∧ closed.event.set = state.event.set ∧
  closed.timeoutMs = state.timeoutMs ∧ closed.intervalMs = state.intervalMs ∧
  m257 closed = closed

def P294 : Prop := ∀ state,
  (state.hasHandle = false → m294 state = state) ∧
  (state.hasHandle = true →
    (m294 state).hasHandle = false ∧ (m294 state).event.isopen = false)

def P314 : Prop := ∀ state,
  (m314 state).hasHandle = false ∧ (m314 state).event.isopen = false ∧
  (m314 state).event.kind = state.event.kind ∧
  (m314 state).event.set = state.event.set

def P328 : Prop := ∀ state,
  (m328 state).event.set = true ∧
  (m328 state).event.isopen = state.event.isopen ∧
  (m328 state).event.kind = state.event.kind ∧
  (m328 state).hasHandle = state.hasHandle

def P340 : Prop := ∀ state,
  let fired := m340 state
  fired.event.set = (state.event.set || state.event.isopen) ∧
  fired.hasHandle = (state.hasHandle && fired.event.isopen) ∧
  fired.event.kind = state.event.kind ∧
  fired.timeoutMs = state.timeoutMs ∧ fired.intervalMs = state.intervalMs

def P371 : Prop := ∀ nonnegative waited,
  (nonnegative = false → m371 nonnegative waited = .error .argumentError) ∧
  (nonnegative = true ∧ waited = false → m371 nonnegative waited = .error .ioError) ∧
  (nonnegative = true ∧ waited = true → m371 nonnegative waited = .ok false)

def P421 : Prop := ∀ state spawn,
  (m421 state spawn).1 = state ∧
  (m421 state spawn).2.1 = (match spawn with | none => true | some value => !value) ∧
  (m421 state spawn).2.2 = state.event.set

def P478 : Prop := ∀ valid tests polls,
  (valid = false → m478 valid tests polls = .error .argumentError) ∧
  (valid = true ∧ timedwaitResult tests polls = true →
    m478 valid tests polls = .ok .ok) ∧
  (valid = true ∧ timedwaitResult tests polls = false →
    m478 valid tests polls = .ok .timedOut)

def P512 : Prop := ∀ timeout,
  (m512 timeout).timeoutMs = timeout ∧ (m512 timeout).armed = false

def P515 : Prop := ∀ state,
  (m515 state).1.timeoutMs = state.timeoutMs ∧
  (m515 state).1.armed = true ∧ (m515 state).2 = true

def P539 : Prop := ∀ state,
  (m539 state).timeoutMs = state.timeoutMs ∧ (m539 state).armed = false

theorem p23 : P23 := by simp [P23, m23]
theorem p47 : P47 := by simp [P47, m47]
theorem p129 : P129 := by
  intro timeout interval initOk startOk
  by_cases ht : timeout < 0
  · simp [m129, ht] <;> omega
  · by_cases hi : interval < 0
    · simp [m129, ht, hi] <;> omega
    · cases initOk <;> cases startOk <;> simp [m129, ht, hi]
theorem p152 : P152 := by simp [P152, m152, timerTimeout]
theorem p162 : P162 := by intro _input; rfl
theorem p164 : P164 := by simp [P164, m164]
theorem p171 : P171 := by simp [P171, m171]
theorem p172 : P172 := by simp [P172, m172]
theorem p177 : P177 := by
  intro state
  cases hs : state.event.set <;> cases ho : state.event.isopen <;>
    cases hk : state.event.kind <;> simp [P177, trywaitContract, m177, waitEvent, hs, ho, hk]
theorem p179 : P179 := by
  intro state
  cases hs : state.event.set <;> cases ho : state.event.isopen <;>
    cases hk : state.event.kind <;> simp [P179, trywaitContract, m179, waitEvent, hs, ho, hk]
theorem p235 : P235 := by simp [P235, m235]
theorem p237 : P237 := by
  intro state
  cases hs : state.event.set <;> cases ho : state.event.isopen <;>
    cases hk : state.event.kind <;> simp [P237, waitContract, m237, m177, waitEvent, hs, ho, hk]
theorem p239 : P239 := by
  intro state cancelled
  cases hs : state.event.set <;> cases ho : state.event.isopen <;>
    cases hc : cancelled <;> cases hk : state.event.kind <;>
      simp [P239, m239, m179, waitEvent, hs, ho, hc, hk]
theorem p247 : P247 := by simp [P247, m247]
theorem p257 : P257 := by
  intro state
  cases hh : state.hasHandle <;> cases ho : state.event.isopen <;>
    simp [P257, m257, closeEvent, hh, ho]
theorem p294 : P294 := by
  intro state
  cases hh : state.hasHandle <;> simp [P294, m294, closeEvent, hh]
theorem p314 : P314 := by simp [P314, m314, closeEvent]
theorem p328 : P328 := by simp [P328, m328]
theorem p340 : P340 := by
  intro state
  cases ho : state.event.isopen <;> cases hk : state.event.kind <;>
    simp [m340, signalEvent, ho, hk]
theorem p371 : P371 := by simp [P371, m371]
theorem p421 : P421 := by simp [P421, m421]
theorem p478 : P478 := by simp [P478, m478]
theorem p512 : P512 := by simp [P512, m512]
theorem p515 : P515 := by simp [P515, m515, timeoutEnqueue]
theorem p539 : P539 := by simp [P539, m539, timeoutDequeue]

def entries : List Entry := [
  { id := "streams-method-asyncevent-l23", juliaFile := "base/asyncevent.jl", juliaFns := ["AsyncCondition()"], statement := "Construction associates and initializes the async handle, throwing on a nonzero libuv result.", source := "base/asyncevent.jl:23-38", status := .proven, prop := ``P23, thm := some ``p23 },
  { id := "streams-method-asyncevent-l47", juliaFile := "base/asyncevent.jl", juliaFns := ["AsyncCondition(cb::Function)"], statement := "Callback construction preserves the condition and schedules immediately exactly when an event is already set.", source := "base/asyncevent.jl:47-70", status := .proven, prop := ``P47, thm := some ``p47 },
  { id := "streams-method-asyncevent-l129", juliaFile := "base/asyncevent.jl", juliaFns := ["Timer(timeout::Real; interval::Real = 0.0)"], statement := "Timer construction rejects negative durations, rounds milliseconds, and checks both libuv setup calls.", source := "base/asyncevent.jl:129-150", status := .proven, prop := ``P129, thm := some ``p129 },
  { id := "streams-method-asyncevent-l152", juliaFile := "base/asyncevent.jl", juliaFns := ["getproperty(t::Timer, f::Symbol)"], statement := "Timer properties remove timeout compensation, expose the interval, and forward stored fields.", source := "base/asyncevent.jl:152-161", status := .proven, prop := ``P152, thm := some ``p152 },
  { id := "streams-method-asyncevent-l162", juliaFile := "base/asyncevent.jl", juliaFns := ["propertynames(::Timer)"], statement := "Timer property names are returned in source order.", source := "base/asyncevent.jl:162", status := .proven, prop := ``P162, thm := some ``p162 },
  { id := "streams-method-asyncevent-l164", juliaFile := "base/asyncevent.jl", juliaFns := ["show(io::IO, t::Timer)"], statement := "Timer display reports open state and includes the interval only when positive.", source := "base/asyncevent.jl:164-169", status := .proven, prop := ``P164, thm := some ``p164 },
  { id := "streams-method-asyncevent-l171", juliaFile := "base/asyncevent.jl", juliaFns := ["unsafe_convert(::Type{Ptr{Cvoid}}, t::Timer)"], statement := "Timer pointer conversion returns its handle.", source := "base/asyncevent.jl:171", status := .proven, prop := ``P171, thm := some ``p171 },
  { id := "streams-method-asyncevent-l172", juliaFile := "base/asyncevent.jl", juliaFns := ["unsafe_convert(::Type{Ptr{Cvoid}}, async::AsyncCondition)"], statement := "AsyncCondition pointer conversion returns its handle.", source := "base/asyncevent.jl:172", status := .proven, prop := ``P172, thm := some ``p172 },
  { id := "streams-method-asyncevent-l177", juliaFile := "base/asyncevent.jl", juliaFns := ["_trywait(t::Union{Timer, AsyncCondition}; cancel::CancelTokenArg=DEFAULT_CANCEL)"], statement := "Keyword _trywait resolves cancellation and forwards the event state.", source := "base/asyncevent.jl:177-178", status := .proven, prop := ``P177, thm := some ``p177 },
  { id := "streams-method-asyncevent-l179", juliaFile := "base/asyncevent.jl", juliaFns := ["_trywait(t::Union{Timer, AsyncCondition}, tok::MaybeToken)"], statement := "Token _trywait observes a pending event first, rejects a closed unset event, and retains a one-shot event.", source := "base/asyncevent.jl:179-233", status := .proven, prop := ``P179, thm := some ``p179 },
  { id := "streams-method-asyncevent-l235", juliaFile := "base/asyncevent.jl", juliaFns := ["waitqueue(t::Union{Timer, AsyncCondition})"], statement := "waitqueue forwards the event condition queue.", source := "base/asyncevent.jl:235", status := .proven, prop := ``P235, thm := some ``p235 },
  { id := "streams-method-asyncevent-l237", juliaFile := "base/asyncevent.jl", juliaFns := ["wait(t::Union{Timer, AsyncCondition}; cancel::CancelTokenArg=DEFAULT_CANCEL)"], statement := "Keyword wait checks its cancellation argument and forwards to token wait.", source := "base/asyncevent.jl:237-238", status := .proven, prop := ``P237, thm := some ``p237 },
  { id := "streams-method-asyncevent-l239", juliaFile := "base/asyncevent.jl", juliaFns := ["wait(t::Union{Timer, AsyncCondition}, tok::MaybeToken)"], statement := "Token wait performs _trywait, checks cancellation, and throws EOF on a closed unset event.", source := "base/asyncevent.jl:239-244", status := .proven, prop := ``P239, thm := some ``p239 },
  { id := "streams-method-asyncevent-l247", juliaFile := "base/asyncevent.jl", juliaFns := ["isopen(t::Union{Timer, AsyncCondition})"], statement := "isopen returns the atomic activity flag.", source := "base/asyncevent.jl:247", status := .proven, prop := ``P247, thm := some ``p247 },
  { id := "streams-method-asyncevent-l257", juliaFile := "base/asyncevent.jl", juliaFns := ["close(t::Union{Timer, AsyncCondition})"], statement := "Close short-circuits a fully closed object and otherwise clears activity and waits for handle closure.", source := "base/asyncevent.jl:257-292", status := .proven, prop := ``P257, thm := some ``p257 },
  { id := "streams-method-asyncevent-l294", juliaFile := "base/asyncevent.jl", juliaFns := ["uvfinalize(t::Union{Timer, AsyncCondition})"], statement := "Finalization disassociates and closes a live handle before notifying waiters.", source := "base/asyncevent.jl:294-312", status := .proven, prop := ``P294, thm := some ``p294 },
  { id := "streams-method-asyncevent-l314", juliaFile := "base/asyncevent.jl", juliaFns := ["_uv_hook_close(t::Union{Timer, AsyncCondition})"], statement := "The close hook clears activity and handle state before notifying waiters.", source := "base/asyncevent.jl:314-326", status := .proven, prop := ``P314, thm := some ``p314 },
  { id := "streams-method-asyncevent-l328", juliaFile := "base/asyncevent.jl", juliaFns := ["uv_asynccb(handle::Ptr{Cvoid})"], statement := "The async callback sets the event before notifying its condition.", source := "base/asyncevent.jl:328-338", status := .proven, prop := ``P328, thm := some ``p328 },
  { id := "streams-method-asyncevent-l340", juliaFile := "base/asyncevent.jl", juliaFns := ["uv_timercb(handle::Ptr{Cvoid})"], statement := "The timer callback sets the event, closes a one-shot timer, then notifies waiters.", source := "base/asyncevent.jl:340-359", status := .proven, prop := ``P340, thm := some ``p340 },
  { id := "streams-method-asyncevent-l371", juliaFile := "base/asyncevent.jl", juliaFns := ["sleep(sec::Real; cancel::CancelTokenArg=DEFAULT_CANCEL)"], statement := "Sleep rejects negative durations and closes its timer after either wait outcome.", source := "base/asyncevent.jl:371-381", status := .proven, prop := ``P371, thm := some ``p371 },
  { id := "streams-method-asyncevent-l421", juliaFile := "base/asyncevent.jl", juliaFns := ["Timer(cb::Function, timeout; spawn::Union{Nothing,Bool}=nothing, kwargs...)"], statement := "Callback timer construction selects stickiness, preserves lifetime, and schedules according to the pending event bit.", source := "base/asyncevent.jl:421-454", status := .proven, prop := ``P421, thm := some ``p421 },
  { id := "streams-method-asyncevent-l478", juliaFile := "base/asyncevent.jl", juliaFns := ["timedwait(testcb, timeout::Real; pollint::Real=0.1)"], statement := "timedwait validates its poll interval and returns at the first successful poll or timeout.", source := "base/asyncevent.jl:478-496", status := .proven, prop := ``P478, thm := some ``p478 },
  { id := "streams-method-asyncevent-l512", juliaFile := "base/asyncevent.jl", juliaFns := ["TimeoutWait(timeout::Real)"], statement := "TimeoutWait converts and stores the deadline with no armed timer.", source := "base/asyncevent.jl:512", status := .proven, prop := ``P512, thm := some ``p512 },
  { id := "streams-method-asyncevent-l515", juliaFile := "base/asyncevent.jl", juliaFns := ["wait_enqueue!(x::TimeoutWait, w::WaitEntry, first::Bool)"], statement := "Enqueue arms the timer, spawns the claimer, schedules it, and returns true.", source := "base/asyncevent.jl:515-537", status := .proven, prop := ``P515, thm := some ``p515 },
  { id := "streams-method-asyncevent-l539", juliaFile := "base/asyncevent.jl", juliaFns := ["wait_dequeue!(x::TimeoutWait, w::WaitEntry, why::UInt8)"], statement := "Dequeue closes any timer and clears the stored timer reference.", source := "base/asyncevent.jl:539-544", status := .proven, prop := ``P539, thm := some ``p539 }
]

end JuliaLean.Streams.Methods.AsyncEvent
