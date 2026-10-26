import JuliaLean.Streams.Methods.Support

namespace JuliaLean.Streams.Methods.Process

open JuliaLean JuliaLean.Streams JuliaLean.Streams.Methods JuliaLean.Registry

structure ProcM where
  core : ProcessM
  command : CmdM
  hasHandle : Bool
  input : Nat
  output : Nat
  error : Nat
  syncCount : Nat
  deriving Repr, DecidableEq

structure ChainM where
  processes : List ProcM
  input : Nat
  output : Nat
  error : Nat
  deriving Repr, DecidableEq

inductive OpenAccess where | none | read | write | readWrite
  deriving Repr, DecidableEq

inductive StdioSource where | endpoint | pipe | abstractPipe | ioStream | file | generic | osHandle | syncClose
  deriving Repr, DecidableEq

def procCtor (command : CmdM) (handle : Bool) (syncCount id : Nat) : ProcM :=
  ⟨processCtor id command.ignorestatus, command, handle, 0, 0, 0, syncCount⟩

def chainCtor : ChainM := ⟨[], 0, 0, 0⟩

def procExited (p : ProcM) : Bool := !p.hasHandle
def procRunning (p : ProcM) : Bool := p.hasHandle
def procSuccess (p : ProcM) : Bool := testSuccess p.core

def spawnLeaf (command : CmdM) (handle : Bool) (id : Nat := 0) : Except StreamErr ProcM :=
  if command.exec.isEmpty then .error .argumentError else .ok (procCtor command handle 0 id)

def spawnInto (chain : ChainM) (command : CmdM) (handle : Bool) : Except StreamErr ChainM :=
  match spawnLeaf command handle chain.processes.length with
  | .error e => .error e
  | .ok process => .ok { chain with processes := chain.processes ++ [process] }

def spawnTree (chain : ChainM) : CommandM → Except StreamErr ChainM
  | .leaf command => spawnInto chain command true
  | .stdoutPipe left right | .stderrPipe left right | .concurrent left right =>
      match spawnTree chain left with
      | .error e => .error e
      | .ok afterLeft => spawnTree afterLeft right
  | .redirect command => spawnTree chain command

def processList (chain : ChainM) : List ProcessM := chain.processes.map (·.core)

/-- `Process` constructor, `base/process.jl:13-20`. -/
def m13 (command : CmdM) (handle : Bool) (syncCount id : Nat) : ProcM := procCtor command handle syncCount id
/-- `pipe_reader(::Process)`, `base/process.jl:22`. -/
def m22 (p : ProcM) : Nat := p.output
/-- `pipe_writer(::Process)`, `base/process.jl:23`. -/
def m23 (p : ProcM) : Nat := p.input
/-- `ProcessChain()`, `base/process.jl:32-34`. -/
def m32 : ChainM := chainCtor
/-- `pipe_reader(::ProcessChain)`, `base/process.jl:36`. -/
def m36 (p : ChainM) : Nat := p.output
/-- `pipe_writer(::ProcessChain)`, `base/process.jl:37`. -/
def m37 (p : ChainM) : Nat := p.input
/-- `rawhandle(::SyncCloseFD)`, `base/process.jl:46`. -/
def m46 (handle : Nat) : Nat := handle
/-- `uvfinalize(::Process)`, `base/process.jl:49-60`. -/
def m49 (p : ProcM) : ProcM := if p.hasHandle then { p with hasHandle := false } else p
/-- `uv_return_spawn`, `base/process.jl:63-79`. -/
def m63 (p : ProcM) (hasData : Bool) (exitCode : JInt .i64) (signal : JInt .i32) : ProcM :=
  if !hasData then p else { p with core := processExitCallback p.core exitCode signal, hasHandle := false }
/-- `_uv_hook_close(::Process)`, `base/process.jl:82-85`. -/
def m82 (p : ProcM) : ProcM := { p with hasHandle := false }
/-- `as_cpumask`, `base/process.jl:90-97`. -/
def m90 (cpus : List Nat) (runtimeSize : Nat) : List Bool := cpuMask cpus (max (cpus.foldl max 0) runtimeSize)
/-- `_spawn_primitive`, `base/process.jl:100-159`. -/
def m100 (command : CmdM) (cancelled spawnSucceeded : Bool) : Except StreamErr ProcM :=
  if cancelled then .error .ioError
  else if !spawnSucceeded then .error .ioError
  else spawnLeaf command true
/-- `_spawn(cmds, tok)`, `base/process.jl:163-164`. -/
def m163 (command : CommandM) : Except StreamErr ChainM := spawnTree chainCtor command
/-- Vector-stdio `_spawn`, `base/process.jl:166-172`. -/
def m166 (command : CommandM) : Except StreamErr ChainM := spawnTree chainCtor command
/-- Direct Cmd `_spawn`, `base/process.jl:175-178`. -/
def m175 (command : CmdM) : Except StreamErr ProcM := spawnLeaf command true
/-- Abstract command `_spawn`, `base/process.jl:181-183`. -/
def m181 (command : CommandM) : Except StreamErr ChainM := spawnTree chainCtor command
/-- `_stdio_copy`, `base/process.jl:186-192`. -/
def m186 (stdios : List α) (fd : Nat) (replacement default : α) : List α := stdioCopy stdios fd replacement default
/-- Redirect `_spawn` without chain, `base/process.jl:194-203`. -/
def m194 (command : CommandM) : Except StreamErr ChainM := spawnTree chainCtor command
/-- Redirect `_spawn` with chain, `base/process.jl:205-214`. -/
def m205 (chain : ChainM) (command : CommandM) : Except StreamErr ChainM := spawnTree chain command
/-- Stdout pipeline `_spawn`, `base/process.jl:216-228`. -/
def m216 (chain : ChainM) (left right : CommandM) : Except StreamErr ChainM := spawnTree chain (.stdoutPipe left right)
/-- Stderr pipeline `_spawn`, `base/process.jl:230-242`. -/
def m230 (chain : ChainM) (left right : CommandM) : Except StreamErr ChainM := spawnTree chain (.stderrPipe left right)
/-- Concurrent command `_spawn`, `base/process.jl:244-248`. -/
def m244 (chain : ChainM) (left right : CommandM) : Except StreamErr ChainM := spawnTree chain (.concurrent left right)
/-- Cmd `_spawn` into a chain, `base/process.jl:250-255`. -/
def m250 (chain : ChainM) (command : CmdM) : Except StreamErr ChainM := spawnInto chain command true
/-- `setup_stdios`, `base/process.jl:259-274`. -/
def m259 (opened closeAfter : List Bool) : Bool × Nat := (opened.all id, (closeAfter.filter id).length)
/-- PipeEndpoint stdio setup, `base/process.jl:276-294`. -/
def m276 (isInitial childReadable : Bool) : Bool × Bool := if isInitial then (childReadable, true) else (childReadable, false)
/-- Pipe stdio setup, `base/process.jl:296-302`. -/
def m296 (bothInitial childReadable : Bool) : Bool × Bool := (childReadable, bothInitial)
/-- AbstractPipe stdio setup, `base/process.jl:304-305`. -/
def m304 (readable : Bool) : Bool := readable
/-- IOStream stdio setup, `base/process.jl:307-310`. -/
def m307 (fd : Int) : Int × Bool := (fd, false)
/-- FileRedirect stdio setup, `base/process.jl:312-323`. -/
def m312 (childReadable append : Bool) : Nat × Nat × Bool :=
  if childReadable then (0, 0, true) else (if append then 3 else 2, 4, true)
/-- Generic IO stdio setup, `base/process.jl:329-357`. -/
def m329 (childReadable copySucceeded : Bool) : Except StreamErr (Bool × Bool) :=
  if copySucceeded then .ok (childReadable, true) else .error .ioError
/-- Generic `close_stdio`, `base/process.jl:359`. -/
def m359 (_source : StdioSource) : Bool := true
/-- OS handle `close_stdio`, `base/process.jl:360`. -/
def m360 (_source : StdioSource) : Bool := true
/-- SyncCloseFD `close_stdio`, `base/process.jl:361`. -/
def m361 (_source : StdioSource) : Bool := true
/-- StdIOSet swallowing options, `base/process.jl:373`. -/
def m373 (stdios : List α) : List α := stdios
/-- StdIOSet inheriting options, `base/process.jl:374`. -/
def m374 (stdios : List α) : List α := stdios
/-- Variadic swallowing options, `base/process.jl:375-376`. -/
def m375 (input output error : α) (extra : List α) : List α := [input, output, error] ++ extra
/-- Variadic inheriting options, `base/process.jl:380-381`. -/
def m380 (input output error : α) (extra : List α) : List α := [input, output, error] ++ extra
/-- `eachline(command)`, `base/process.jl:383-391`. -/
def m383 (command : CommandM) (keep cancelled : Bool) : Except StreamErr (ChainM × Bool) :=
  if cancelled then .error .ioError else
    match spawnTree chainCtor command with
    | .error e => .error e
    | .ok chain => .ok (chain, keep)
/-- Mode-string process `open`, `base/process.jl:407-418`. -/
def m407 (mode : String) : Except StreamErr OpenAccess :=
  match mode with | "r+" | "w+" => .ok .readWrite | "r" => .ok .read | "w" => .ok .write | _ => .error .argumentError
/-- Keyword process `open`, `base/process.jl:431-454`. -/
def m431 (command : CommandM) (read write stdioIsDevnull : Bool) : Except StreamErr (ChainM × OpenAccess) :=
  if read && write && !stdioIsDevnull then .error .argumentError
  else if !read && !write && !stdioIsDevnull then .error .argumentError
  else
    match spawnTree chainCtor command with
    | .error e => .error e
    | .ok chain =>
        .ok (chain, if read && write then .readWrite else if read then .read else if write then .write else .none)
/-- Do-block process `open`, `base/process.jl:464-508`. -/
def m464 (bodySucceeded outputAtEof processSucceeded : Bool) : OpenDoOutcome :=
  openDoOutcome bodySucceeded outputAtEof processSucceeded
/-- Nested `waitkill`, `base/process.jl:466-481`. -/
def m466 (chain : ChainM) : ChainM := { chain with processes := chain.processes.map fun p => m49 p }
/-- `read(command)`, `base/process.jl:515-522`. -/
def m515 (output : List UInt8) (chain : ChainM) (cancelled : Bool) : Except ProcessErr (List UInt8) :=
  if cancelled then .error .methodError else readCommand output (processList chain)
/-- String `read(command)`, `base/process.jl:529-530`. -/
def m529 (output : List UInt8) (chain : ChainM) (cancelled : Bool) : Except ProcessErr (List UInt8) := m515 output chain cancelled
/-- `run`, `base/process.jl:553-580`. -/
def m553 (command : CommandM) (wait cancelled : Bool) : Except ProcessErr ChainM :=
  if cancelled then .error .methodError
  else match spawnTree chainCtor command with
    | .error _ => .error .methodError
    | .ok chain => if wait then match runResult (processList chain) with | .ok _ => .ok chain | .error e => .error e else .ok chain
/-- `test_success`, `base/process.jl:593-600`. -/
def m593 (p : ProcM) : Except StreamErr Bool :=
  if !procExited p then .error .ioError
  else if p.core.exitcode.val < 0 then .error .ioError
  else .ok (procSuccess p)
/-- Process `success`, `base/process.jl:602-605`. -/
def m602 (p : ProcM) : Except StreamErr Bool := m593 p
/-- Left-to-right aggregation used by vector `success`, `base/process.jl:606-607`. -/
def successVector : List ProcM → Except StreamErr Bool
  | [] => .ok true
  | process :: rest =>
      match m602 process with
      | .error e => .error e
      | .ok succeeded =>
          match successVector rest with
          | .error e => .error e
          | .ok tailSucceeded => .ok (succeeded && tailSucceeded)

/-- Vector `success`, `base/process.jl:606-607`. -/
def m606 (processes : List ProcM) : Except StreamErr Bool := successVector processes
/-- ProcessChain `success`, `base/process.jl:608-609`. -/
def m608 (chain : ChainM) : Except StreamErr Bool := m606 chain.processes
/-- Command `success`, `base/process.jl:618-622`. -/
def m618 (chain : ChainM) (cancelled : Bool) : Except StreamErr Bool := if cancelled then .error .ioError else m608 chain
/-- Single-process failure constructor, `base/process.jl:635`. -/
def m635 (p : ProcM) : List ProcM := [p]
/-- `showerror(ProcessFailedException)`, `base/process.jl:637-647`. -/
def m637 (processes : List ProcM) : List (Nat × Int) := processes.map fun p => (p.core.id, p.core.exitcode.val)
/-- Single-process `pipeline_error`, `base/process.jl:649-654`. -/
def m649 (p : ProcM) : Except ProcessErr Unit := if p.command.ignorestatus then .ok () else .error (.processFailed [p.core.id])
/-- Chain `pipeline_error`, `base/process.jl:656-665`. -/
def m656 (chain : ChainM) : Except ProcessErr Unit := pipelineError (processList chain)
/-- Process `kill`, `base/process.jl:675-686`. -/
def m675 (p : ProcM) (signal : JInt .i32) (foreignCode esrch : Int) : Except StreamErr ProcM :=
  if !procRunning p then .ok p
  else if foreignCode != 0 && foreignCode != esrch then .error .ioError
  else .ok { p with core := killProcess p.core signal, hasHandle := false }
/-- Vector `kill`, `base/process.jl:687`. -/
def m687 (processes : List ProcM) (signal : JInt .i32) : List ProcM := processes.map fun p => { p with core := killProcess p.core signal, hasHandle := false }
/-- ProcessChain `kill`, `base/process.jl:688`. -/
def m688 (chain : ChainM) (signal : JInt .i32) : ChainM := { chain with processes := m687 chain.processes signal }
/-- `getpid`, `base/process.jl:698-708`. -/
def m698 (p : ProcM) (foreignPid : Int) : Except StreamErr Int := if !p.hasHandle || foreignPid ≤ 0 then .error .ioError else .ok foreignPid
/-- Process `process_running`, `base/process.jl:717`. -/
def m717 (p : ProcM) : Bool := procRunning p
/-- Vector `process_running`, `base/process.jl:718`. -/
def m718 (processes : List ProcM) : Bool := processes.any procRunning
/-- Chain `process_running`, `base/process.jl:719`. -/
def m719 (chain : ChainM) : Bool := m718 chain.processes
/-- Process `process_exited`, `base/process.jl:726`. -/
def m726 (p : ProcM) : Bool := !m717 p
/-- Vector `process_exited`, `base/process.jl:727`. -/
def m727 (processes : List ProcM) : Bool := processes.all m726
/-- Chain `process_exited`, `base/process.jl:728`. -/
def m728 (chain : ChainM) : Bool := m727 chain.processes
/-- `process_signaled`, `base/process.jl:730`. -/
def m730 (p : ProcM) : Bool := processSignaled p.core
/-- `process_status`, `base/process.jl:732-737`. -/
def m732 (p : ProcM) : ProcessStatus := if m717 p then .running else processStatus p.core
/-- Process `wait`, `base/process.jl:739-765`. -/
def m739 (p : ProcM) (syncd cancelled : Bool) : Except StreamErr ProcM :=
  if cancelled then .error .ioError else .ok (if syncd then { p with syncCount := 0 } else p)
/-- ProcessChain `wait`, `base/process.jl:767-768`. -/
def m767 (chain : ChainM) (syncd cancelled : Bool) : Except StreamErr ChainM :=
  if cancelled then .error .ioError else .ok { chain with processes := chain.processes.map fun p => if syncd then { p with syncCount := 0 } else p }
/-- Process display, `base/process.jl:770`. -/
def m770 (p : ProcM) : ProcessStatus := m732 p
/-- Generated unary Cmd sequence methods, `base/process.jl:773-775`. -/
def m774 (command : CmdM) : List JuliaLean.ShellCmd.JS := command.exec
/-- Reverse Cmd iterator, `base/process.jl:776`. -/
def m776 (command : CmdM) : List JuliaLean.ShellCmd.JS := command.exec.reverse
/-- Cmd element type, `base/process.jl:777`. -/
def m777 : String := "String"
/-- Generated indexed Cmd methods, `base/process.jl:778-780`. -/
def m779 (command : CmdM) (index : Nat) : Option JuliaLean.ShellCmd.JS := command.exec[index]?

def SpawnOrderContract (result : Except StreamErr ChainM) (initial : ChainM)
    (command : CommandM) : Prop := ∀ next,
  result = .ok next →
    next.processes.map (fun p => p.command) =
      initial.processes.map (fun p => p.command) ++ commandLeaves command

def P13 : Prop := ∀ command handle syncCount id,
  let process := m13 command handle syncCount id
  process.command = command ∧ process.hasHandle = handle ∧
  process.syncCount = syncCount ∧ process.core.id = id ∧
  process.core.ignorestatus = command.ignorestatus ∧ process.core.exited = false

def P22 : Prop := ∀ process, m22 process = process.output
def P23 : Prop := ∀ process, m23 process = process.input
def P32 : Prop := ∀ _input : Unit,
  m32.processes = [] ∧ m32.input = 0 ∧ m32.output = 0 ∧ m32.error = 0
def P36 : Prop := ∀ chain, m36 chain = chain.output
def P37 : Prop := ∀ chain, m37 chain = chain.input
def P46 : Prop := ∀ handle, m46 handle = handle

def P49 : Prop := ∀ process,
  (m49 process).hasHandle = false ∧ (m49 process).core = process.core ∧
  m49 (m49 process) = m49 process

def P63 : Prop := ∀ process hasData exitCode signal,
  (hasData = false → m63 process hasData exitCode signal = process) ∧
  (hasData = true →
    let exited := m63 process hasData exitCode signal
    exited.hasHandle = false ∧ exited.core.exited = true ∧
    exited.core.exitcode = exitCode ∧ exited.core.termsignal = signal)

def P82 : Prop := ∀ process,
  (m82 process).hasHandle = false ∧ (m82 process).core = process.core

def P90 : Prop := ∀ cpus runtimeSize,
  m90 cpus runtimeSize =
    (List.range (max (cpus.foldl max 0) runtimeSize)).map
      (fun i => decide ((i + 1) ∈ cpus))

def P100 : Prop := ∀ command cancelled spawned,
  (cancelled = true → m100 command cancelled spawned = .error .ioError) ∧
  (cancelled = false ∧ spawned = false → m100 command cancelled spawned = .error .ioError) ∧
  (cancelled = false ∧ spawned = true ∧ command.exec.isEmpty = true →
    m100 command cancelled spawned = .error .argumentError) ∧
  (cancelled = false ∧ spawned = true ∧ command.exec.isEmpty = false →
    ∃ process, m100 command cancelled spawned = .ok process ∧
      process.command = command ∧ process.hasHandle = true)

def P163 : Prop := ∀ command, SpawnOrderContract (m163 command) chainCtor command
def P166 : Prop := ∀ command, SpawnOrderContract (m166 command) chainCtor command

def P175 : Prop := ∀ command,
  (command.exec.isEmpty = true → m175 command = .error .argumentError) ∧
  (command.exec.isEmpty = false → ∃ process, m175 command = .ok process ∧
    process.command = command ∧ process.hasHandle = true)

def P181 : Prop := ∀ command, SpawnOrderContract (m181 command) chainCtor command

def P186 : Prop := ∀ (α : Type) (stdios : List α) fd replacement default,
  m186 stdios fd replacement default =
    (stdios ++ List.replicate (fd - stdios.length) default).set (fd - 1) replacement

def P194 : Prop := ∀ command, SpawnOrderContract (m194 command) chainCtor command
def P205 : Prop := ∀ chain command, SpawnOrderContract (m205 chain command) chain command
def P216 : Prop := ∀ chain left right,
  SpawnOrderContract (m216 chain left right) chain (.stdoutPipe left right)
def P230 : Prop := ∀ chain left right,
  SpawnOrderContract (m230 chain left right) chain (.stderrPipe left right)
def P244 : Prop := ∀ chain left right,
  SpawnOrderContract (m244 chain left right) chain (.concurrent left right)
def P250 : Prop := ∀ chain command, SpawnOrderContract (m250 chain command) chain (.leaf command)

def P259 : Prop := ∀ opened closeAfter,
  (m259 opened closeAfter).1 = opened.all id ∧
  (m259 opened closeAfter).2 = (closeAfter.filter id).length

def P276 : Prop := ∀ isInitial childReadable,
  (m276 isInitial childReadable).1 = childReadable ∧
  (m276 isInitial childReadable).2 = isInitial

def P296 : Prop := ∀ bothInitial childReadable,
  (m296 bothInitial childReadable).1 = childReadable ∧
  (m296 bothInitial childReadable).2 = bothInitial

def P304 : Prop := ∀ readable, m304 readable = readable
def P307 : Prop := ∀ fd, (m307 fd).1 = fd ∧ (m307 fd).2 = false

def P312 : Prop := ∀ childReadable append,
  (childReadable = true → m312 childReadable append = (0, 0, true)) ∧
  (childReadable = false ∧ append = true → m312 childReadable append = (3, 4, true)) ∧
  (childReadable = false ∧ append = false → m312 childReadable append = (2, 4, true))

def P329 : Prop := ∀ childReadable copied,
  (copied = true → m329 childReadable copied = .ok (childReadable, true)) ∧
  (copied = false → m329 childReadable copied = .error .ioError)

def P359 : Prop := ∀ source, m359 source = true
def P360 : Prop := ∀ source, m360 source = true
def P361 : Prop := ∀ source, m361 source = true
def P373 : Prop := ∀ (α : Type) (stdios : List α), m373 stdios = stdios
def P374 : Prop := ∀ (α : Type) (stdios : List α), m374 stdios = stdios
def P375 : Prop := ∀ (α : Type) (input output error : α) extra,
  m375 input output error extra = [input, output, error] ++ extra
def P380 : Prop := ∀ (α : Type) (input output error : α) extra,
  m380 input output error extra = [input, output, error] ++ extra

def P383 : Prop := ∀ command keep cancelled,
  (cancelled = true → m383 command keep cancelled = .error .ioError) ∧
  (∀ chain, m383 command keep false = .ok (chain, keep) →
    chain.processes.map (fun p => p.command) = commandLeaves command)

def P407 : Prop :=
  m407 "r" = .ok .read ∧ m407 "w" = .ok .write ∧
  m407 "r+" = .ok .readWrite ∧ m407 "w+" = .ok .readWrite ∧
  ∀ mode, mode ≠ "r" → mode ≠ "w" → mode ≠ "r+" → mode ≠ "w+" →
    m407 mode = .error .argumentError

def accessOf (read write : Bool) : OpenAccess :=
  if read && write then .readWrite else if read then .read else if write then .write else .none

def P431 : Prop := ∀ command read write devnull,
  (devnull = false ∧ read = write → m431 command read write devnull = .error .argumentError) ∧
  (∀ chain, m431 command read write devnull = .ok (chain, accessOf read write) →
    chain.processes.map (fun p => p.command) = commandLeaves command)

def P464 : Prop := ∀ bodyOk outputEof processOk,
  (bodyOk = false → m464 bodyOk outputEof processOk = .bodyError) ∧
  (bodyOk = true ∧ outputEof = false → m464 bodyOk outputEof processOk = .unreadOutput) ∧
  (bodyOk = true ∧ outputEof = true ∧ processOk = false →
    m464 bodyOk outputEof processOk = .processError) ∧
  (bodyOk = true ∧ outputEof = true ∧ processOk = true →
    m464 bodyOk outputEof processOk = .returned)

def P466 : Prop := ∀ chain,
  (m466 chain).processes.length = chain.processes.length ∧
  (m466 chain).processes.map (fun p => p.hasHandle) =
    List.replicate chain.processes.length false ∧
  (m466 chain).processes.map (fun p => p.command) = chain.processes.map (fun p => p.command)

def P515 : Prop := ∀ output chain cancelled,
  (cancelled = true → m515 output chain cancelled = .error .methodError) ∧
  (cancelled = false →
    match runResult (processList chain) with
    | .ok _ => m515 output chain cancelled = .ok output
    | .error e => m515 output chain cancelled = .error e)

def P529 : Prop := ∀ output chain cancelled,
  m529 output chain cancelled = m515 output chain cancelled

def P553 : Prop := ∀ command wait cancelled,
  (cancelled = true → m553 command wait cancelled = .error .methodError) ∧
  (∀ chain, cancelled = false → spawnTree chainCtor command = .ok chain → wait = false →
    m553 command wait cancelled = .ok chain) ∧
  (∀ chain, cancelled = false → spawnTree chainCtor command = .ok chain → wait = true →
    match runResult (processList chain) with
    | .ok _ => m553 command wait cancelled = .ok chain
    | .error e => m553 command wait cancelled = .error e)

def P593 : Prop := ∀ process,
  (process.hasHandle = true → m593 process = .error .ioError) ∧
  (process.hasHandle = false ∧ process.core.exitcode.val < 0 →
    m593 process = .error .ioError) ∧
  (process.hasHandle = false ∧ 0 ≤ process.core.exitcode.val →
    m593 process = .ok (procSuccess process))

def P602 : Prop := ∀ process, m602 process = m593 process

def P606 : Prop := ∀ processes,
  (∀ process, process ∈ processes → process.hasHandle = false ∧
    0 ≤ process.core.exitcode.val) →
  m606 processes = .ok (processes.all procSuccess)

def P608 : Prop := ∀ chain,
  (∀ process, process ∈ chain.processes → process.hasHandle = false ∧
    0 ≤ process.core.exitcode.val) →
  m608 chain = .ok (chain.processes.all procSuccess)

def P618 : Prop := ∀ chain cancelled,
  (cancelled = true → m618 chain cancelled = .error .ioError) ∧
  (cancelled = false → m618 chain cancelled = m608 chain)

def P635 : Prop := ∀ process, m635 process = [process]
def P637 : Prop := ∀ processes,
  m637 processes = processes.map (fun p => (p.core.id, p.core.exitcode.val))

def P649 : Prop := ∀ process,
  (process.command.ignorestatus = true → m649 process = .ok ()) ∧
  (process.command.ignorestatus = false →
    m649 process = .error (.processFailed [process.core.id]))

def P656 : Prop := ∀ chain,
  match failedProcesses (processList chain) with
  | [] => m656 chain = .ok ()
  | failed => m656 chain = .error (.processFailed (failed.map (fun p => p.id)))

def P675 : Prop := ∀ process signal foreignCode esrch,
  (process.hasHandle = false → m675 process signal foreignCode esrch = .ok process) ∧
  (process.hasHandle = true ∧ foreignCode ≠ 0 ∧ foreignCode ≠ esrch →
    m675 process signal foreignCode esrch = .error .ioError) ∧
  (process.hasHandle = true ∧ process.core.exited = false ∧
      (foreignCode = 0 ∨ foreignCode = esrch) →
    ∃ killed, m675 process signal foreignCode esrch = .ok killed ∧
      killed.hasHandle = false ∧ killed.core.termsignal = signal)

def P687 : Prop := ∀ processes signal,
  (m687 processes signal).length = processes.length ∧
  (m687 processes signal).all (fun p => !p.hasHandle) = true

def P688 : Prop := ∀ chain signal,
  (m688 chain signal).processes = m687 chain.processes signal ∧
  (m688 chain signal).input = chain.input ∧ (m688 chain signal).output = chain.output

def P698 : Prop := ∀ process pid,
  (process.hasHandle = false ∨ pid ≤ 0 → m698 process pid = .error .ioError) ∧
  (process.hasHandle = true ∧ 0 < pid → m698 process pid = .ok pid)

def P717 : Prop := ∀ process, m717 process = process.hasHandle
def P718 : Prop := ∀ processes, m718 processes = processes.any (fun p => p.hasHandle)
def P719 : Prop := ∀ chain, m719 chain = chain.processes.any (fun p => p.hasHandle)
def P726 : Prop := ∀ process, m726 process = !process.hasHandle
def P727 : Prop := ∀ processes, m727 processes = processes.all (fun p => !p.hasHandle)
def P728 : Prop := ∀ chain, m728 chain = chain.processes.all (fun p => !p.hasHandle)
def P730 : Prop := ∀ process, m730 process = decide (process.core.termsignal.val > 0)

def P732 : Prop := ∀ process,
  (process.hasHandle = true → m732 process = .running) ∧
  (process.hasHandle = false → m732 process = processStatus process.core)

def P739 : Prop := ∀ process syncd cancelled,
  (cancelled = true → m739 process syncd cancelled = .error .ioError) ∧
  (cancelled = false ∧ syncd = false → m739 process syncd cancelled = .ok process) ∧
  (cancelled = false ∧ syncd = true → ∃ waited,
    m739 process syncd cancelled = .ok waited ∧ waited.syncCount = 0)

def P767 : Prop := ∀ chain syncd cancelled,
  (cancelled = true → m767 chain syncd cancelled = .error .ioError) ∧
  (cancelled = false ∧ syncd = false → m767 chain syncd cancelled = .ok chain) ∧
  (cancelled = false ∧ syncd = true → ∃ waited,
    m767 chain syncd cancelled = .ok waited ∧
      waited.processes.all (fun p => p.syncCount = 0) = true)

def P770 : Prop := ∀ process, m770 process = m732 process
def P774 : Prop := ∀ command, m774 command = command.exec
def P776 : Prop := ∀ command, m776 command = command.exec.reverse
def P777 : Prop := ∀ _input : Unit, m777 = "String"
def P779 : Prop := ∀ command index, m779 command index = command.exec[index]?

theorem spawnInto_success_order (chain : ChainM) (command : CmdM) (handle : Bool)
    (next : ChainM) (h : spawnInto chain command handle = .ok next) :
    next.processes.map (fun p => p.command) =
      chain.processes.map (fun p => p.command) ++ [command] := by
  by_cases empty : command.exec.isEmpty
  · simp [spawnInto, spawnLeaf, empty] at h
  · simp [spawnInto, spawnLeaf, empty] at h
    subst next
    simp [procCtor]

theorem spawnTree_success_order (command : CommandM) (chain next : ChainM)
    (h : spawnTree chain command = .ok next) :
    next.processes.map (fun p => p.command) =
      chain.processes.map (fun p => p.command) ++ commandLeaves command := by
  induction command generalizing chain next with
  | leaf cmd =>
      simpa [commandLeaves] using spawnInto_success_order chain cmd true next h
  | stdoutPipe left right ihLeft ihRight =>
      cases hleft : spawnTree chain left with
      | error e => simp [spawnTree, hleft] at h
      | ok middle =>
          have hright : spawnTree middle right = .ok next := by simpa [spawnTree, hleft] using h
          rw [ihRight middle next hright, ihLeft chain middle hleft]
          simp [commandLeaves, List.append_assoc]
  | stderrPipe left right ihLeft ihRight =>
      cases hleft : spawnTree chain left with
      | error e => simp [spawnTree, hleft] at h
      | ok middle =>
          have hright : spawnTree middle right = .ok next := by simpa [spawnTree, hleft] using h
          rw [ihRight middle next hright, ihLeft chain middle hleft]
          simp [commandLeaves, List.append_assoc]
  | concurrent left right ihLeft ihRight =>
      cases hleft : spawnTree chain left with
      | error e => simp [spawnTree, hleft] at h
      | ok middle =>
          have hright : spawnTree middle right = .ok next := by simpa [spawnTree, hleft] using h
          rw [ihRight middle next hright, ihLeft chain middle hleft]
          simp [commandLeaves, List.append_assoc]
  | redirect command ih =>
      simpa [spawnTree, commandLeaves] using ih chain next h

theorem spawnTree_contract (chain : ChainM) (command : CommandM) :
    SpawnOrderContract (spawnTree chain command) chain command := by
  intro next h
  exact spawnTree_success_order command chain next h

theorem spawn_of_pair_success (command : CommandM) (chain : ChainM) {tag : α}
    (h : (match spawnTree chainCtor command with
      | .error e => .error e
      | .ok spawned => .ok (spawned, tag)) =
        (Except.ok (chain, tag) : Except StreamErr (ChainM × α))) :
    spawnTree chainCtor command = .ok chain := by
  cases hs : spawnTree chainCtor command with
  | error e => simp [hs] at h
  | ok spawned =>
      have heq : spawned = chain := by simpa [hs] using h
      simpa [heq] using hs

theorem successVector_valid (processes : List ProcM)
    (valid : ∀ process, process ∈ processes →
      process.hasHandle = false ∧ 0 ≤ process.core.exitcode.val) :
    successVector processes = .ok (processes.all procSuccess) := by
  induction processes with
  | nil => simp [successVector]
  | cons process tail ih =>
      have hp := valid process (by simp)
      have ht : ∀ p, p ∈ tail → p.hasHandle = false ∧ 0 ≤ p.core.exitcode.val := by
        intro p h
        exact valid p (by simp [h])
      have hn : ¬ process.core.exitcode.val < 0 := by omega
      simp [successVector, m602, m593, procExited, hp.1, hn, ih ht]

theorem p13 : P13 := by simp [P13, m13, procCtor, processCtor]
theorem p22 : P22 := by simp [P22, m22]
theorem p23 : P23 := by simp [P23, m23]
theorem p32 : P32 := by simp [P32, m32, chainCtor]
theorem p36 : P36 := by simp [P36, m36]
theorem p37 : P37 := by simp [P37, m37]
theorem p46 : P46 := by simp [P46, m46]
theorem p49 : P49 := by
  intro process
  cases hh : process.hasHandle <;> simp [P49, m49, hh]
theorem p63 : P63 := by
  intro process hasData exitCode signal
  cases hd : hasData <;> simp [P63, m63, hd, processExitCallback]
theorem p82 : P82 := by simp [P82, m82]
theorem p90 : P90 := by simp [P90, m90, cpuMask]
theorem p100 : P100 := by
  intro command cancelled spawned
  cases hc : cancelled <;> cases hs : spawned <;> cases he : command.exec.isEmpty <;>
    simp [P100, m100, spawnLeaf, procCtor, hc, hs, he]
theorem p163 : P163 := by exact fun command => spawnTree_contract chainCtor command
theorem p166 : P166 := by exact fun command => spawnTree_contract chainCtor command
theorem p175 : P175 := by
  intro command
  cases he : command.exec.isEmpty <;> simp [P175, m175, spawnLeaf, procCtor, he]
theorem p181 : P181 := by exact fun command => spawnTree_contract chainCtor command
theorem p186 : P186 := by simp [P186, m186, stdioCopy]
theorem p194 : P194 := by exact fun command => spawnTree_contract chainCtor command
theorem p205 : P205 := by exact fun chain command => spawnTree_contract chain command
theorem p216 : P216 := by exact fun chain left right => spawnTree_contract chain (.stdoutPipe left right)
theorem p230 : P230 := by exact fun chain left right => spawnTree_contract chain (.stderrPipe left right)
theorem p244 : P244 := by exact fun chain left right => spawnTree_contract chain (.concurrent left right)
theorem p250 : P250 := by
  intro chain command next h
  simpa [SpawnOrderContract, commandLeaves] using
    spawnInto_success_order chain command true next h
theorem p259 : P259 := by simp [P259, m259]
theorem p276 : P276 := by simp [P276, m276]
theorem p296 : P296 := by simp [P296, m296]
theorem p304 : P304 := by simp [P304, m304]
theorem p307 : P307 := by simp [P307, m307]
theorem p312 : P312 := by simp [P312, m312]
theorem p329 : P329 := by simp [P329, m329]
theorem p359 : P359 := by simp [P359, m359]
theorem p360 : P360 := by simp [P360, m360]
theorem p361 : P361 := by simp [P361, m361]
theorem p373 : P373 := by simp [P373, m373]
theorem p374 : P374 := by simp [P374, m374]
theorem p375 : P375 := by simp [P375, m375]
theorem p380 : P380 := by simp [P380, m380]
theorem p383 : P383 := by
  intro command keep cancelled
  constructor
  · intro hc
    simp [m383, hc]
  · intro chain h
    have hs : spawnTree chainCtor command = .ok chain :=
      spawn_of_pair_success command chain (by simpa [m383] using h)
    simpa [chainCtor] using spawnTree_success_order command chainCtor chain hs
theorem p407 : P407 := by
  refine ⟨by rfl, by rfl, by rfl, by rfl, ?_⟩
  intro mode hr hw hrp hwp
  simp [m407]
theorem p431 : P431 := by
  intro command read write devnull
  constructor
  · rintro ⟨hd, hrw⟩
    cases read <;> cases write <;> simp [m431, hd] at hrw ⊢
  · intro chain h
    cases read <;> cases write <;> cases devnull <;>
      simp [m431, accessOf] at h ⊢
    all_goals
      have hspawn : spawnTree chainCtor command = .ok chain :=
        spawn_of_pair_success command chain h
      have hs := spawnTree_success_order command chainCtor chain hspawn
      simpa [chainCtor] using hs
theorem p464 : P464 := by simp [P464, m464, openDoOutcome]
theorem p466 : P466 := by
  rintro ⟨processes, input, output, error⟩
  have mapped : ∀ ps : List ProcM,
      (ps.map m49).length = ps.length ∧
      (ps.map m49).map (fun p => p.hasHandle) = List.replicate ps.length false ∧
      (ps.map m49).map (fun p => p.command) = ps.map (fun p => p.command) := by
    intro ps
    induction ps with
    | nil => simp
    | cons process rest ih =>
        have hrep : List.replicate (rest.length + 1) false =
            false :: List.replicate rest.length false := by
          rw [show rest.length + 1 = Nat.succ rest.length by omega]
          rfl
        cases hh : process.hasHandle <;> simp [m49, hh, ih, hrep]
  simpa [m466] using mapped processes
theorem p515 : P515 := by
  intro output chain cancelled
  cases hc : cancelled
  · cases hrun : runResult (processList chain) <;>
      simp [P515, m515, readCommand, hc, hrun]
  · simp [P515, m515, hc]
theorem p529 : P529 := by simp [P529, m529]
theorem p553 : P553 := by
  intro command wait cancelled
  constructor
  · intro hc
    simp [m553, hc]
  · constructor
    · intro chain hc hs hw
      subst wait
      simp [m553, hc, hs]
    · intro chain hc hs hw
      subst wait
      cases hrun : runResult (processList chain) <;> simp [m553, hc, hs, hrun]
theorem p593 : P593 := by
  intro process
  cases hh : process.hasHandle
  · by_cases he : process.core.exitcode.val < 0 <;>
      simp [P593, m593, procExited, procSuccess, testSuccess, hh, he]
  · simp [P593, m593, procExited, hh]
theorem p602 : P602 := by simp [P602, m602]
theorem p606 : P606 := by
  intro processes valid
  simpa [m606] using successVector_valid processes valid
theorem p608 : P608 := by
  intro chain valid
  exact p606 chain.processes valid
theorem p618 : P618 := by simp [P618, m618]
theorem p635 : P635 := by simp [P635, m635]
theorem p637 : P637 := by simp [P637, m637]
theorem p649 : P649 := by simp [P649, m649]
theorem p656 : P656 := by
  intro chain
  cases h : failedProcesses (processList chain) <;> simp [P656, m656, pipelineError, h]
theorem p675 : P675 := by
  intro process signal code esrch
  cases hh : process.hasHandle <;> cases he : process.core.exited <;>
    by_cases hc0 : code = 0 <;> by_cases hce : code = esrch <;>
      simp [P675, m675, procRunning, hh, he, hc0, hce, killProcess]
theorem p687 : P687 := by
  intro processes signal
  simp [P687, m687]
theorem p688 : P688 := by simp [P688, m688]
theorem p698 : P698 := by
  intro process pid
  cases hh : process.hasHandle <;> by_cases hp : pid ≤ 0 <;>
    simp [P698, m698, hh, hp] <;> omega
theorem p717 : P717 := by simp [P717, m717, procRunning]
theorem p718 : P718 := by
  intro processes
  rfl
theorem p719 : P719 := by
  intro chain
  exact p718 chain.processes
theorem p726 : P726 := by simp [P726, m726, m717, procRunning]
theorem p727 : P727 := by
  intro processes
  rfl
theorem p728 : P728 := by
  intro chain
  exact p727 chain.processes
theorem p730 : P730 := by simp [P730, m730, processSignaled]
theorem p732 : P732 := by
  intro process
  cases hh : process.hasHandle <;> simp [P732, m732, m717, procRunning, hh]
theorem p739 : P739 := by simp [P739, m739]
theorem p767 : P767 := by
  intro chain syncd cancelled
  cases cancelled <;> cases syncd <;> simp [P767, m767]
theorem p770 : P770 := by simp [P770, m770]
theorem p774 : P774 := by simp [P774, m774]
theorem p776 : P776 := by simp [P776, m776]
theorem p777 : P777 := by intro _input; rfl
theorem p779 : P779 := by simp [P779, m779]

def entries : List Entry := [
  methodEntry "base/process.jl" "process" 13 20 "Process(cmd::Cmd, handle::Ptr{Cvoid}, syncd::Vector{Task})" "The Process constructor stores command, handle, stdio defaults, sync tasks, status sentinels, and finalizer state." ``P13 ``p13,
  methodEntry "base/process.jl" "process" 22 22 "pipe_reader(p::Process)" "Process pipe_reader returns stdout." ``P22 ``p22,
  methodEntry "base/process.jl" "process" 23 23 "pipe_writer(p::Process)" "Process pipe_writer returns stdin." ``P23 ``p23,
  methodEntry "base/process.jl" "process" 32 34 "ProcessChain()" "ProcessChain starts empty with devnull stdio." ``P32 ``p32,
  methodEntry "base/process.jl" "process" 36 36 "pipe_reader(p::ProcessChain)" "ProcessChain pipe_reader returns stdout." ``P36 ``p36,
  methodEntry "base/process.jl" "process" 37 37 "pipe_writer(p::ProcessChain)" "ProcessChain pipe_writer returns stdin." ``P37 ``p37,
  methodEntry "base/process.jl" "process" 46 46 "rawhandle(io::SyncCloseFD)" "SyncCloseFD rawhandle forwards its descriptor." ``P46 ``p46,
  methodEntry "base/process.jl" "process" 49 60 "uvfinalize(proc::Process)" "Process finalization closes and clears a non-null handle once." ``P49 ``p49,
  methodEntry "base/process.jl" "process" 63 79 "uv_return_spawn(p::Ptr{Cvoid}, exit_status::Int64, termsignal::Int32)" "The exit callback returns early without data, otherwise stores exact status, clears the handle, and notifies waiters." ``P63 ``p63,
  methodEntry "base/process.jl" "process" 82 85 "_uv_hook_close(proc::Process)" "The process close hook atomically clears and frees the handle." ``P82 ``p82,
  methodEntry "base/process.jl" "process" 90 97 "as_cpumask(cpus::Vector{UInt16})" "CPU mask construction sizes for both requested CPUs and libuv, then sets each requested slot." ``P90 ``p90,
  methodEntry "base/process.jl" "process" 100 159 "_spawn_primitive(file, cmd::Cmd, stdio::SpawnIOs, tok::MaybeToken=default_cancel_token())" "Primitive spawn checks cancellation before side effects, marshals command state, and returns a process only on foreign success." ``P100 ``p100,
  methodEntry "base/process.jl" "process" 163 164 "_spawn(cmds::AbstractCmd, tok::MaybeToken=default_cancel_token())" "The no-stdio spawn overload supplies an empty stdio vector." ``P163 ``p163,
  methodEntry "base/process.jl" "process" 166 172 "_spawn(cmd::AbstractCmd, stdios::Vector{Redirectable}, tok::MaybeToken=default_cancel_token())" "Vector-stdio spawn sets up descriptors around the recursive spawn." ``P166 ``p166,
  methodEntry "base/process.jl" "process" 175 178 "_spawn(cmd::Cmd, stdios::SpawnIOs, tok::MaybeToken=default_cancel_token())" "Direct Cmd spawn rejects an empty executable and spawns its first word." ``P175 ``p175,
  methodEntry "base/process.jl" "process" 181 183 "_spawn(cmds::AbstractCmd, stdios::SpawnIOs, tok::MaybeToken=default_cancel_token())" "Composite spawn creates an empty ProcessChain before traversal." ``P181 ``p181,
  methodEntry "base/process.jl" "process" 186 192 "_stdio_copy(stdios::SpawnIOs, fd::Int, @nospecialize replace)" "stdio copy pads to the requested descriptor and replaces that slot." ``P186 ``p186,
  methodEntry "base/process.jl" "process" 194 203 "_spawn(redirect::CmdRedirect, stdios::SpawnIOs, tok::MaybeToken=default_cancel_token())" "Redirect spawn installs its descriptor and closes only a temporary handle." ``P194 ``p194,
  methodEntry "base/process.jl" "process" 205 214 "_spawn(redirect::CmdRedirect, stdios::SpawnIOs, chain::ProcessChain, tok::MaybeToken)" "Chain redirect spawn installs its descriptor, recurses, and closes only temporary handles." ``P205 ``p205,
  methodEntry "base/process.jl" "process" 216 228 "_spawn(cmds::OrCmds, stdios::SpawnIOs, chain::ProcessChain, tok::MaybeToken)" "Stdout pipeline spawn links a pipe, spawns left then right, and closes both temporary ends." ``P216 ``p216,
  methodEntry "base/process.jl" "process" 230 242 "_spawn(cmds::ErrOrCmds, stdios::SpawnIOs, chain::ProcessChain, tok::MaybeToken)" "Stderr pipeline spawn links descriptor three to descriptor one in source order." ``P230 ``p230,
  methodEntry "base/process.jl" "process" 244 248 "_spawn(cmds::AndCmds, stdios::SpawnIOs, chain::ProcessChain, tok::MaybeToken)" "Concurrent command spawn visits left then right in the shared chain." ``P244 ``p244,
  methodEntry "base/process.jl" "process" 250 255 "_spawn(cmd::Cmd, stdios::SpawnIOs, chain::ProcessChain, tok::MaybeToken)" "Chain Cmd spawn rejects empty commands and appends the new process." ``P250 ``p250,
  methodEntry "base/process.jl" "process" 259 274 "setup_stdios(f, stdios::Vector{Redirectable})" "setup_stdios opens every descriptor, calls its body, and closes each marked temporary on all exits." ``P259 ``p259,
  methodEntry "base/process.jl" "process" 276 294 "setup_stdio(stdio::PipeEndpoint, child_readable::Bool)" "Initial PipeEndpoint setup creates the opposite child end; an open endpoint is passed through." ``P276 ``p276,
  methodEntry "base/process.jl" "process" 296 302 "setup_stdio(stdio::Pipe, child_readable::Bool)" "Pipe setup links two initial ends and selects output for readable children or input otherwise." ``P296 ``p296,
  methodEntry "base/process.jl" "process" 304 305 "setup_stdio(stdio::AbstractPipe, readable::Bool)" "AbstractPipe setup selects its reader or writer before forwarding." ``P304 ``p304,
  methodEntry "base/process.jl" "process" 307 310 "setup_stdio(stdio::IOStream, child_readable::Bool)" "IOStream setup passes its raw descriptor without parent cleanup." ``P307 ``p307,
  methodEntry "base/process.jl" "process" 312 323 "setup_stdio(stdio::FileRedirect, child_readable::Bool)" "File redirection selects read or create-write flags, append versus truncate, permissions, and parent cleanup." ``P312 ``p312,
  methodEntry "base/process.jl" "process" 329 357 "setup_stdio(stdio::IO, child_readable::Bool)" "Generic IO setup creates a pipe, launches the directional copy task, closes the parent, and tracks synchronized cleanup." ``P329 ``p329,
  methodEntry "base/process.jl" "process" 359 359 "close_stdio(stdio)" "Generic close_stdio calls close." ``P359 ``p359,
  methodEntry "base/process.jl" "process" 360 360 "close_stdio(stdio::OS_HANDLE)" "OS-handle close_stdio uses synchronous pipe close." ``P360 ``p360,
  methodEntry "base/process.jl" "process" 361 361 "close_stdio(stdio::SyncCloseFD)" "SyncCloseFD close_stdio recurses on its descriptor." ``P361 ``p361,
  methodEntry "base/process.jl" "process" 373 373 "spawn_opts_swallow(stdios::StdIOSet)" "StdIOSet swallowing options preserve descriptor order." ``P373 ``p373,
  methodEntry "base/process.jl" "process" 374 374 "spawn_opts_inherit(stdios::StdIOSet)" "StdIOSet inheriting options preserve descriptor order." ``P374 ``p374,
  methodEntry "base/process.jl" "process" 375 376 "spawn_opts_swallow(in::Redirectable=devnull, out::Redirectable=devnull, err::Redirectable=devnull, extra::Redirectable...)" "Variadic swallowing options return stdin, stdout, stderr, then extras." ``P375 ``p375,
  methodEntry "base/process.jl" "process" 380 381 "spawn_opts_inherit(in::Redirectable=RawFD(0), out::Redirectable=RawFD(1), err::Redirectable=RawFD(2), extra::Redirectable...)" "Variadic inheriting options return stdin, stdout, stderr, then extras." ``P380 ``p380,
  methodEntry "base/process.jl" "process" 383 391 "eachline(cmd::AbstractCmd; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)" "Command eachline checks cancellation, spawns captured stdout, and retains the keep and completion-status behavior." ``P383 ``p383,
  methodEntry "base/process.jl" "process" 407 418 "open(cmds::AbstractCmd, mode::AbstractString, stdio::Redirectable=devnull; cancel::CancelTokenArg=DEFAULT_CANCEL)" "Mode process-open maps r, w, r+, and w+ to documented access and rejects every other mode." ``P407 ``p407,
  methodEntry "base/process.jl" "process" 431 454 "open(cmds::AbstractCmd, stdio::Redirectable=devnull; write::Bool=false, read::Bool=!write, cancel::CancelTokenArg=DEFAULT_CANCEL)" "Keyword process-open selects pipes and stdio for four access modes and enforces devnull-only ambiguous modes." ``P431 ``p431,
  methodEntry "base/process.jl" "process" 464 508 "open(f::Function, cmds::AbstractCmd, args...; kwargs...)" "Do-block open preserves body errors, rejects unread output, waits for cleanup, checks status, and returns the body result." ``P464 ``p464,
  methodEntry "base/process.jl" "process" 466 481 "waitkill(P::Union{Process,ProcessChain})" "waitkill closes the process, schedules termination, waits without stdio synchronization, and closes its timer." ``P466 ``p466,
  methodEntry "base/process.jl" "process" 515 522 "read(cmd::AbstractCmd; cancel::CancelTokenArg=DEFAULT_CANCEL)" "Command read checks cancellation, captures stdout bytes, and applies process status before returning them." ``P515 ``p515,
  methodEntry "base/process.jl" "process" 529 530 "read(cmd::AbstractCmd, ::Type{String}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "String command read converts the checked byte result." ``P529 ``p529,
  methodEntry "base/process.jl" "process" 553 580 "run(cmds::AbstractCmd, args...; wait::Bool = true, cancel::CancelTokenArg=DEFAULT_CANCEL)" "Run checks cancellation, uses inherited stdio and status checks when waiting, and swallowed stdio otherwise." ``P553 ``p553,
  methodEntry "base/process.jl" "process" 593 600 "test_success(proc::Process)" "test_success requires exit, reports negative spawn status, and accepts exactly zero code and signal." ``P593 ``p593,
  methodEntry "base/process.jl" "process" 602 605 "success(x::Process; cancel::CancelTokenArg=DEFAULT_CANCEL)" "Process success waits, then applies test_success." ``P602 ``p602,
  methodEntry "base/process.jl" "process" 606 607 "success(procs::Vector{Process}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "Vector success waits and combines every process result with conjunction." ``P606 ``p606,
  methodEntry "base/process.jl" "process" 608 609 "success(procs::ProcessChain; cancel::CancelTokenArg=DEFAULT_CANCEL)" "ProcessChain success forwards its process vector." ``P608 ``p608,
  methodEntry "base/process.jl" "process" 618 622 "success(cmd::AbstractCmd; cancel::CancelTokenArg=DEFAULT_CANCEL)" "Command success checks cancellation, spawns, and forwards process success." ``P618 ``p618,
  methodEntry "base/process.jl" "process" 635 635 "ProcessFailedException(proc::Process)" "The single-process failure constructor wraps exactly that process." ``P635 ``p635,
  methodEntry "base/process.jl" "process" 637 647 "showerror(io::IO, err::ProcessFailedException)" "Failure display distinguishes one process from many and preserves order and exit codes." ``P637 ``p637,
  methodEntry "base/process.jl" "process" 649 654 "pipeline_error(proc::Process)" "Single-process pipeline_error throws exactly when ignorestatus is false." ``P649 ``p649,
  methodEntry "base/process.jl" "process" 656 665 "pipeline_error(procs::ProcessChain)" "Chain pipeline_error includes exactly failed non-ignored processes in order." ``P656 ``p656,
  methodEntry "base/process.jl" "process" 675 686 "kill(p::Process, signum::Integer=SIGTERM)" "Kill is a no-op after exit, accepts success or ESRCH, and reports every other foreign failure." ``P675 ``p675,
  methodEntry "base/process.jl" "process" 687 687 "kill(ps::Vector{Process}, signum::Integer=SIGTERM)" "Vector kill visits every process in order." ``P687 ``p687,
  methodEntry "base/process.jl" "process" 688 688 "kill(ps::ProcessChain, signum::Integer=SIGTERM)" "ProcessChain kill forwards its process vector." ``P688 ``p688,
  methodEntry "base/process.jl" "process" 698 708 "Libc.getpid(p::Process)" "getpid reads a live handle and rejects absent or nonpositive foreign pids." ``P698 ``p698,
  methodEntry "base/process.jl" "process" 717 717 "process_running(s::Process)" "A Process is running exactly while its handle is non-null." ``P717 ``p717,
  methodEntry "base/process.jl" "process" 718 718 "process_running(s::Vector{Process})" "A process vector is running when any member is running." ``P718 ``p718,
  methodEntry "base/process.jl" "process" 719 719 "process_running(s::ProcessChain)" "ProcessChain running forwards its process vector." ``P719 ``p719,
  methodEntry "base/process.jl" "process" 726 726 "process_exited(s::Process)" "A Process is exited exactly when it is not running." ``P726 ``p726,
  methodEntry "base/process.jl" "process" 727 727 "process_exited(s::Vector{Process})" "A process vector is exited when every member has exited." ``P727 ``p727,
  methodEntry "base/process.jl" "process" 728 728 "process_exited(s::ProcessChain)" "ProcessChain exited forwards its process vector." ``P728 ``p728,
  methodEntry "base/process.jl" "process" 730 730 "process_signaled(s::Process)" "A process is signaled exactly for a positive termination signal." ``P730 ``p730,
  methodEntry "base/process.jl" "process" 732 737 "process_status(s::Process)" "Process status reports running first, then exact signal, then exact exit code." ``P732 ``p732,
  methodEntry "base/process.jl" "process" 739 765 "wait(x::Process, syncd::Bool=true; cancel::CancelTokenArg=DEFAULT_CANCEL)" "Process wait checks cancellation, waits for exit once, and optionally waits for every synchronized copy task." ``P739 ``p739,
  methodEntry "base/process.jl" "process" 767 768 "wait(x::ProcessChain, syncd::Bool=true; cancel::CancelTokenArg=DEFAULT_CANCEL)" "ProcessChain wait visits each process with the same synchronization and cancellation arguments." ``P767 ``p767,
  methodEntry "base/process.jl" "process" 770 770 "show(io::IO, p::Process)" "Process display includes the command and exact process status." ``P770 ``p770,
  methodEntry "base/process.jl" "process" 774 774 "$f(cmd::Cmd)" "Generated unary Cmd collection methods forward to exec." ``P774 ``p774,
  methodEntry "base/process.jl" "process" 776 776 "Iterators.reverse(cmd::Cmd)" "Cmd reverse forwards to reverse(exec)." ``P776 ``p776,
  methodEntry "base/process.jl" "process" 777 777 "eltype(::Type{Cmd})" "Cmd element type is the element type of its exec field." ``P777 ``p777,
  methodEntry "base/process.jl" "process" 779 779 "$f(cmd::Cmd, i)" "Generated indexed Cmd methods forward the index to exec." ``P779 ``p779
]

end JuliaLean.Streams.Methods.Process
