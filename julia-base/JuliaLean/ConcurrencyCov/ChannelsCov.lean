import JuliaLean.ConcurrencyCov.Common

/-! Source-body models and properties for uncovered methods in `base/channels.jl`. -/

namespace JuliaLean.ConcurrencyCov.ChannelsCov

open JuliaLean.ConcurrencyCov

def sizeError : String := "Channel size must be either 0, a positive integer or Inf"

/-- Julia integer arguments, distinguishing values that fit the `Int` field. -/
inductive IntegerSize where
  | value (n : Int)
  | positiveOverflow
  deriving DecidableEq, Repr

/-- Float64 classes relevant to `convert(Int, sz)`. -/
inductive FloatSize where
  | positiveInf
  | negativeInf
  | nan
  | integral (n : Int)
  | fractional
  deriving DecidableEq, Repr

structure ChannelState where
  size : Int
  isOpen : Bool := true
  available : Int := 0
  locked : Bool := false
  exception : Option Exn := none
  hooks : Nat := 0
  deriving DecidableEq, Repr

/-- `Channel{T}(sz::Integer)`, lines 43-51, including conversion to the `Int` field. -/
def channelInteger : IntegerSize → R ChannelState
  | .value n => if n < 0 then .error (.argumentError sizeError) else .ok ⟨n, true, 0, false, none, 0⟩
  | .positiveOverflow => .error .inexactError

/-- `Channel{T}(sz::Float64)`, lines 54-57: only positive infinity is handled
before `convert(Int, sz)`. -/
def channelFloat : FloatSize → R ChannelState
  | .positiveInf => channelInteger (.value (2 ^ 63 - 1))
  | .integral n => channelInteger (.value n)
  | .negativeInf | .nan | .fractional => .error .inexactError

inductive SizeArg where
  | integer (size : IntegerSize)
  | float (size : FloatSize)
  deriving DecidableEq, Repr

/-- `Channel(sz=0)` dispatches to `Channel{Any}(sz)` without changing `sz`. -/
def channelDefault : SizeArg → R ChannelState
  | .integer size => channelInteger size
  | .float size => channelFloat size

structure TaskPlan where
  channel : ChannelState
  sticky : Bool
  pool : String
  scheduled : Bool
  taskrefWritten : Bool
  deriving DecidableEq, Repr

/-- `Channel{T}(func, size; ...)`, lines 139-157. -/
def channelFunction (size : IntegerSize) (spawn : Bool) (pool : Option String)
    (taskref : Bool) : R TaskPlan := do
  let ch ← channelInteger size
  let actualPool := pool.getD "default"
  let actualSpawn := spawn || pool.isSome
  return ⟨{ ch with hooks := ch.hooks + 1 }, !actualSpawn, actualPool, actualSpawn, taskref⟩

def channelFunctionAny := channelFunction

/-- Deprecated keyword constructor, lines 165-176. -/
def channelDeprecated (ctypeSet csizeSet spawnSet poolSet : Bool) (size : IntegerSize) : R TaskPlan :=
  if (ctypeSet || csizeSet) && (spawnSet || poolSet) then
    .error (.argumentError "Cannot combine deprecated and scheduling keywords")
  else channelFunction size false none false

def closedException : Exn := .invalidState "Channel is closed." "closed"
def isbuffered (c : ChannelState) : Bool := c.size != 0

def close (c : ChannelState) (e : Exn := closedException) : ChannelState :=
  { c with isOpen := false, exception := some e }

def isopen (c : ChannelState) : Bool := c.isOpen
def bind (c : ChannelState) : ChannelState := { c with hooks := c.hooks + 1 }

inductive TaskStatus where | running | succeeded | failed (task : Nat)
  deriving DecidableEq, Repr

/-- `close_chnl_on_taskdone`, lines 367-381. -/
def closeOnTaskDone (status : TaskStatus) (c : ChannelState) : ChannelState :=
  if !c.isOpen then c else match status with
    | .failed t => close c (.taskFailed t)
    | _ => close c

def channeledTasks (n funcs types sizes : Nat) : R (Nat × Nat) :=
  if sizes != n then .error (.assertionError "length(csizes) != n")
  else if types != n then .error (.assertionError "length(ctypes) != n")
  else .ok (n, funcs)

def showInvalidState (msg : String) : String := "InvalidStateException: " ++ msg
def incrementAvailable (c : ChannelState) (inc : Int) : ChannelState :=
  { c with available := c.available + inc }
def fetchUnbuffered : R Nat := .error (.errorException "`fetch` is not supported on an unbuffered Channel.")
def isempty (c : ChannelState) : Bool := c.available = 0
def isfull (c : ChannelState) : Bool := c.size ≤ c.available

def channelLock (c : ChannelState) : ChannelState := { c with locked := true }
def channelUnlock (c : ChannelState) : ChannelState := { c with locked := false }
def channelTrylock (c : ChannelState) : Bool × ChannelState :=
  if c.locked then (false, c) else (true, channelLock c)
def channelWithLock (body : R Nat) (c : ChannelState) : R Nat × ChannelState :=
  (body, channelUnlock (channelLock c))

def channelEltype (typeName : String) : String := typeName
def channelShow (typeName : String) (c : ChannelState) : String :=
  typeName ++ "(" ++ toString c.size ++ ")"
def channelShowPlain (compact : Bool) (typeName : String) (c : ChannelState) : String :=
  let head := channelShow typeName c
  if compact then head
  else if !c.isOpen then head ++ " (closed)"
  else if c.available = 0 then head ++ " (empty)"
  else head ++ " (" ++ toString c.available ++ " item" ++ (if c.available = 1 then "" else "s") ++ " available)"

inductive IteratorSize where | sizeUnknown
  deriving DecidableEq, Repr
def channelIteratorSize : IteratorSize := .sizeUnknown

def pushWrapper (putResult value : Nat) : Nat × Nat := (putResult, value)
def popfirstWrapper (taken : Nat) : Nat := taken

/-- Constructor wrappers, task binding, state queries, and display traits preserve
the branch and mutation order in `base/channels.jl:10-387,408,535,648-794`. -/
def ChannelBodies : Prop :=
  (∀ p v, pushWrapper p v = (p, v)) ∧
  (∀ v, popfirstWrapper v = v) ∧
  (∀ n, channelDefault (.integer n) = channelInteger n) ∧
  (∀ n, channelDefault (.float n) = channelFloat n) ∧
  (∀ size spawn pool ref, channelFunctionAny size spawn pool ref =
    channelFunction size spawn pool ref) ∧
  (∀ c e, (close c e).isOpen = false ∧ (close c e).exception = some e) ∧
  (∀ c, isopen c = c.isOpen ∧ isbuffered c = (c.size != 0)) ∧
  (∀ c, (bind c).hooks = c.hooks + 1) ∧
  (∀ n funcs, channeledTasks n funcs n n = .ok (n, funcs)) ∧
  (∀ msg, showInvalidState msg = "InvalidStateException: " ++ msg) ∧
  (∀ c inc, (incrementAvailable c inc).available = c.available + inc) ∧
  fetchUnbuffered = .error (.errorException "`fetch` is not supported on an unbuffered Channel.") ∧
  (∀ c, isempty c = decide (c.available = 0) ∧ isfull c = decide (c.size ≤ c.available)) ∧
  (∀ c, (channelLock c).locked = true ∧ (channelUnlock c).locked = false) ∧
  (∀ t, channelEltype t = t) ∧
  channelIteratorSize = .sizeUnknown

theorem channelBodies_proven : ChannelBodies := by
  refine ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_,
    fun _ => rfl, fun _ _ => rfl, rfl, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩, fun _ => rfl, rfl⟩
  intro n funcs
  simp [channeledTasks]

/-- Every size not listed by the constructor documentation should reach its
`ArgumentError` (`base/channels.jl:13-27,43-57`). -/
def FloatSizeArgumentError : Prop :=
  ∀ s, s ∈ [FloatSize.negativeInf, .nan, .fractional] →
    channelFloat s = .error (.argumentError sizeError)

theorem floatSizeArgumentError_refuted : ¬ FloatSizeArgumentError := by
  intro h
  have bad := h .negativeInf (by simp)
  cases bad

/-- The function constructor defaults the pool before setting stickiness, the
deprecated constructor rejects mixed keyword families, task termination closes
once, and lock/display wrappers delegate to the channel state
(`base/channels.jl:139-176,329-381,698-767`). -/
def ChannelWrapperSpec : Prop :=
  (∀ size spawn pool ref plan, channelFunction size spawn pool ref = .ok plan →
    plan.pool = pool.getD "default" ∧ plan.sticky = !(spawn || pool.isSome) ∧
    plan.scheduled = (spawn || pool.isSome) ∧ plan.taskrefWritten = ref) ∧
  (∀ size, channelDeprecated true false true false size =
    .error (.argumentError "Cannot combine deprecated and scheduling keywords")) ∧
  (∀ t c, c.isOpen = true → (closeOnTaskDone (.failed t) c).exception = some (Exn.taskFailed t)) ∧
  (∀ c, channelTrylock c = if c.locked then (false, c) else (true, channelLock c)) ∧
  (∀ body c, channelWithLock body c = (body, channelUnlock (channelLock c))) ∧
  (∀ compact name c, channelShowPlain compact name c =
    let head := channelShow name c
    if compact then head
    else if !c.isOpen then head ++ " (closed)"
    else if c.available = 0 then head ++ " (empty)"
    else head ++ " (" ++ toString c.available ++ " item" ++
      (if c.available = 1 then "" else "s") ++ " available)")

theorem channelWrapperSpec_proven : ChannelWrapperSpec := by
  refine ⟨?_, fun _ => rfl, ?_, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  · intro size spawn pool ref plan h
    unfold channelFunction at h
    obtain ⟨ch, -, h⟩ := bind_ok h
    cases h
    simp
  · intro t c h
    simp [closeOnTaskDone, h, close]

end JuliaLean.ConcurrencyCov.ChannelsCov
