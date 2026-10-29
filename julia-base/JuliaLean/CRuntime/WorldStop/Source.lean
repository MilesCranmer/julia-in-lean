import JuliaLean.CRuntime.Types
import JuliaLean.Registry.Types

/-!
World-stop synchronization model for Julia
`bbfa0ce4150ea33f2532198cabcf319a49399360`.

Atomic accesses, ordinary accesses, mutexes, condition variables, fences,
page-pointer loads and page reads are separate source steps. Atomic loads
accept arbitrary value/read-from choices; the complete candidate is checked
against C11. Stores apply the C field width through `truncate`. Pointer IDs
identify logical allocations.

Faulting page reads block their source continuation. Nondeterministic normal
handler delivery requires installed handlers and retries that page read on
return (`signals-unix.c:588-605`). `PlatformTraceContract` requires successful
page protection and valid delivery actors. Fairness, signal-mask restoration,
cancellation/reset and alternate exception dispatch are outside this model.

The registered controller may remain GC-safe while calling the exported
`JL_NOTSAFEPOINT` resume function (`julia.h:1345`;
`support/analyzer_annotations.h:27-34,49-55`).
-/

namespace JuliaLean.CRuntime.WorldStop

open Memory

inductive TaskField where
  | copyStack | started | next | queue | waitingOn | cachedWaitEntry
  | cachedCancelEntry | tls | state | start | invoked | result | doneNotify
  | isException | scope | eh | gcstack | excstack | tid | sticky | ptls
  | worldAge | reentrantTiming | runningTimeNs | finishedAt | firstEnqueuedAt
  | lastStartedRunningAt | boundCancelDefault | resetCtx | cancelHandlerCtx
  deriving DecidableEq, Repr

/-- GC-relevant fields of `threading.c:284-285,352-424`,
`julia_threads.h:178-213`, `safepoint.c:19-47`, and
`gc-stock.c:3780,3871-3898`, at `bbfa0ce4150`. TLS, task and array pointer
identities are independent natural-number allocation IDs; zero is NULL. -/
inductive Loc where
  | gcRunning | disableCounter | nThreads | allTLS | tlsSize
  | gcNThreads | gcAllTLS | threadedRegion | ioLoopTid
  | tlsSlot (array slot : Nat)
  | gcState (tls : Nat) | safepoint (tls : Nat) | suspendCount (tls : Nat)
  | currentTask (tls : Nat) | rootTask (tls : Nat) | tid (tls : Nat)
  | tlsZeroed (tls : Nat) | heapReady (tls : Nat) | schedulerReady (tls : Nat)
  | rootFieldsReady (tls : Nat) | handlersReady (tls : Nat)
  | pgcstack (tls : Nat) | taskHeader (task : Nat) | taskField (task : Nat) (field : TaskField)
  | abandonTo (tls : Nat) | abandonNotify (tls : Nat)
  | pageCount (page : Nat)
  deriving DecidableEq, Repr, Inhabited

def declaredAccessClass : Loc → Memory.AccessClass
  | .gcNThreads | .gcAllTLS | .tlsSize | .tlsSlot _ _ | .rootTask _ | .tid _
  | .pgcstack _ | .pageCount _ => .ordinary
  | .taskHeader _ => .atomic
  | .taskField _ .waitingOn | .taskField _ .state | .taskField _ .isException
  | .taskField _ .tid | .taskField _ .runningTimeNs | .taskField _ .finishedAt
  | .taskField _ .firstEnqueuedAt | .taskField _ .lastStartedRunningAt
  | .taskField _ .resetCtx | .taskField _ .cancelHandlerCtx => .atomic
  | .taskField _ _ | .abandonTo _ | .abandonNotify _ => .ordinary
  | _ => .atomic

def initRootTaskFieldTypingCandidate : Candidate Loc Nat :=
  ⟨#[
    { thread := 0, action := .init (.taskField 1 .copyStack) 0 },
    { thread := 0, action := .plainStore (.taskField 1 .copyStack) 1 },
    { thread := 0, action := .init (.taskField 1 .waitingOn) 0 },
    { thread := 0, action := .store (.taskField 1 .waitingOn) .relaxed 1 },
    { thread := 0, action := .init (.taskHeader 1) 0 },
    { thread := 0, action := .store (.taskHeader 1) .relaxed 1 },
    { thread := 0, action := .init (.abandonTo 1) 0 },
    { thread := 0, action := .plainStore (.abandonTo 1) 0 }
  ]⟩

theorem initRoot_task_fields_match_declarations :
    initRootTaskFieldTypingCandidate.DeclaredAccessTyped declaredAccessClass := by
  unfold Candidate.DeclaredAccessTyped
  decide

/- `tlsZeroed`, `heapReady`, `schedulerReady`, `rootFieldsReady`, and
`handlersReady` are proof metadata for completed source initialization calls.
`Op.milestone` records completed initialization calls. -/

/-- `src/julia_threads.h:186-198`, `src/threading.h:17`,
`src/gc-stock.c:3780`, `src/safepoint.c:19,34`, `bbfa0ce4150`. The source
uses valid nonnegative thread IDs/counts in the modeled allocation domain. -/
def truncate : Loc → Nat → Nat
  | .gcState _, v => v % 256
  | .suspendCount _, v | .tid _, v | .pageCount _, v => v % 65536
  | .gcRunning, v | .disableCounter, v | .nThreads, v => v % 4294967296
  | _, v => v

/-- Saved C locals for nested helpers, `safepoint.c:283,350`. -/
inductive Reg where
  | ptls | target | tid | state | oldState | collectorOldState | handlerState | resumeState
  | running | disabled | count | array | newArray | size | newSize | i
  | slot | current | suspend | waitstate | result | page | loaded | task
  | gcCount | gcArray | resumeCount | threaded | ioTid | bootstrap | handleSignals
  deriving DecidableEq, Repr, Inhabited

/-- Scalar C expressions used by `safepoint.c`, `threading.c`, and the
collector-entry slice of `gc-stock.c`. Store widths apply at the destination. -/
inductive Expr where
  | nat (value : Nat)
  | reg (name : Reg)
  | add (a b : Expr) | sub (a b : Expr)
  | eq (a b : Expr) | ne (a b : Expr) | lt (a b : Expr) | le (a b : Expr)
  | signedNegative (bits : Nat) (a : Expr)
  | either (a b : Expr) | both (a b : Expr)
  deriving DecidableEq, Repr, Inhabited

private def lit := Expr.nat
private def reg := Expr.reg

def Expr.eval (r : Reg → Nat) : Expr → Nat
  | .nat v => v
  | .reg k => r k
  | .add a b => a.eval r + b.eval r
  | .sub a b => a.eval r - b.eval r
  | .eq a b => if a.eval r = b.eval r then 1 else 0
  | .ne a b => if a.eval r ≠ b.eval r then 1 else 0
  | .lt a b => if a.eval r < b.eval r then 1 else 0
  | .le a b => if a.eval r ≤ b.eval r then 1 else 0
  | .signedNegative bits a => if 2 ^ (bits - 1) ≤ a.eval r % (2 ^ bits) then 1 else 0
  | .either a b => if a.eval r ≠ 0 ∨ b.eval r ≠ 0 then 1 else 0
  | .both a b => if a.eval r ≠ 0 ∧ b.eval r ≠ 0 then 1 else 0

def Expr.sources (r : Reg → List Nat) : Expr → List Nat
  | .nat _ => []
  | .reg k => r k
  | .signedNegative _ a => a.sources r
  | .add a b | .sub a b | .eq a b | .ne a b | .lt a b | .le a b
  | .either a b | .both a b => a.sources r ++ b.sources r

/-- Address calculations for the TLS projection and published pointer
arrays, `safepoint.c:139-148,398-412,445-460`, `threading.c:408-422`. -/
inductive Addr where
  | fixed (loc : Loc)
  | tlsSlot (array slot : Expr)
  | gcState (tls : Expr) | safepoint (tls : Expr) | suspendCount (tls : Expr)
  | currentTask (tls : Expr) | rootTask (tls : Expr) | tid (tls : Expr)
  | tlsZeroed (tls : Expr) | heapReady (tls : Expr) | schedulerReady (tls : Expr)
  | rootFieldsReady (tls : Expr) | handlersReady (tls : Expr)
  | pgcstack (tls : Expr) | taskHeader (task : Expr) | taskField (task : Expr) (field : TaskField)
  | abandonTo (tls : Expr) | abandonNotify (tls : Expr)
  | pageCount (page : Expr)
  deriving DecidableEq, Repr, Inhabited

def Addr.eval (r : Reg → Nat) : Addr → Loc
  | .fixed l => l
  | .tlsSlot a i => .tlsSlot (a.eval r) (i.eval r)
  | .gcState t => .gcState (t.eval r)
  | .safepoint t => .safepoint (t.eval r)
  | .suspendCount t => .suspendCount (t.eval r)
  | .currentTask t => .currentTask (t.eval r)
  | .rootTask t => .rootTask (t.eval r)
  | .tid t => .tid (t.eval r)
  | .tlsZeroed t => .tlsZeroed (t.eval r)
  | .heapReady t => .heapReady (t.eval r)
  | .schedulerReady t => .schedulerReady (t.eval r)
  | .rootFieldsReady t => .rootFieldsReady (t.eval r)
  | .handlersReady t => .handlersReady (t.eval r)
  | .pgcstack t => .pgcstack (t.eval r)
  | .taskHeader t => .taskHeader (t.eval r)
  | .taskField t f => .taskField (t.eval r) f
  | .abandonTo t => .abandonTo (t.eval r)
  | .abandonNotify t => .abandonNotify (t.eval r)
  | .pageCount p => .pageCount (p.eval r)

def Addr.sources (r : Reg → List Nat) : Addr → List Nat
  | .fixed _ => []
  | .tlsSlot a i => a.sources r ++ i.sources r
  | .gcState t | .safepoint t | .suspendCount t | .currentTask t | .rootTask t
  | .tid t | .tlsZeroed t | .heapReady t | .schedulerReady t
  | .rootFieldsReady t | .handlersReady t | .pgcstack t | .taskHeader t
  | .taskField t _ | .abandonTo t | .abandonNotify t | .pageCount t => t.sources r

/-- `safepoint.c:45-47,352`, `threading.c:404`, `bbfa0ce4150`.
Mutex IDs are kept distinct from condition-variable IDs. -/
inductive Mutex where
  | safepoint | tls | sleep (tls : Expr) | profile
  deriving DecidableEq, Repr

def Mutex.eval (r : Reg → Nat) : Mutex → Nat
  | .safepoint => 0
  | .tls => 1
  | .sleep t => 2 + 2 * t.eval r
  | .profile => 3

def Mutex.sources (r : Reg → List Nat) : Mutex → List Nat
  | .sleep t => t.sources r
  | _ => []

inductive Cond where
  | beginGC | endGC | wake (tls : Expr)
  deriving DecidableEq, Repr

def Cond.eval (r : Reg → Nat) : Cond → Nat
  | .beginGC => 0
  | .endGC => 1
  | .wake t => 2 + t.eval r

/-- Any actor can enter a collector, resume, suspend or adoption continuation. -/
inductive Proc where
  | stateSet | saveAndSet | safepointCheck | setGCAndWait | waitGC | waitResume
  | startGC | endGC | worldWait | collect
  | enableNonmutator | disableNonmutator | initTLS | initRoot | adopt | exitThread
  | suspendThread | resumeThread | safeExit
  deriving DecidableEq, Repr, Inhabited

/-- One source primitive. The `external` cases delimit unmodeled bodies
that do not change this synchronization projection. `critical` is a client
heap/stack access, permitted after a completed unsafe-enter call
(`gc-stock.c:96-105`); `gcBody` denotes `_jl_gc_collect` at line 3888. -/
inductive Op where
  | assign (dst : Reg) (value : Expr)
  | load (dst : Reg) (loc : Addr) (order : Order)
  | store (loc : Addr) (order : Order) (value : Expr)
  | plainLoad (dst : Reg) (loc : Addr)
  | plainStore (loc : Addr) (value : Expr)
  | fetchAdd (loc : Addr) (amount : Nat) (subtract : Bool)
  | cas (dst : Reg) (loc : Addr) (expected desired : Expr)
  | fence | signalFence
  | lock (mutex : Mutex) | unlock (mutex : Mutex)
  | condWait (cond : Cond) (mutex : Mutex)
  | broadcast (cond : Cond) | signal (cond : Cond)
  | protect (page : Expr) (enabled : Bool)
  | readPage (dst : Reg) (page : Expr)
  | external (name : String)
  /-- Completed initialization calls. -/
  | milestone (field : Addr) (value : Expr)
  | critical | gcBody | endGCBody | abort
  deriving DecidableEq, Repr

/-- A source location accompanies every operation and control decision.
While-condition preludes contain separate loads for C short circuiting.
`testLoop` selects the continuation of the same C while statement. -/
inductive Command where
  | stmt (file : String) (line : Nat) (op : Op)
  | branch (file : String) (line : Nat) (test : Expr)
      (yes no : List Command)
  | whileDo (file : String) (line : Nat) (prelude : List Command)
      (test : Expr) (body : List Command)
  | testLoop (file : String) (line : Nat) (prelude : List Command)
      (test : Expr) (body : List Command)
  | call (file : String) (line : Nat) (proc : Proc)
  | ret (file : String) (line : Nat)
  deriving Repr

private def sp (line : Nat) (op : Op) := Command.stmt "src/safepoint.c" line op
private def th (line : Nat) (op : Op) := Command.stmt "src/threading.c" line op
private def gh (line : Nat) (op : Op) := Command.stmt "src/julia_threads.h" line op
private def gc (line : Nat) (op : Op) := Command.stmt "src/gc-stock.c" line op
private def task (line : Nat) (op : Op) := Command.stmt "src/task.c" line op
private def spif (line : Nat) (e : Expr) (a b : List Command) :=
  Command.branch "src/safepoint.c" line e a b
private def thif (line : Nat) (e : Expr) (a b : List Command) :=
  Command.branch "src/threading.c" line e a b
private def gcif (line : Nat) (e : Expr) (a b : List Command) :=
  Command.branch "src/gc-stock.c" line e a b
private def callsp (line : Nat) (p : Proc) := Command.call "src/safepoint.c" line p
private def retsp (line : Nat) := Command.ret "src/safepoint.c" line

private def P := reg .ptls
private def T := reg .target
private def zero := lit 0
private def one := lit 1
private def nonzero (e : Expr) := Expr.ne e zero
private def add1 (e : Expr) := Expr.add e one

/-- `safepoint.c:49-69,71-89`: increment/decrement and page protection
are distinct statements. The caller holds `safepoint_lock`. The return value
of mprotect/VirtualProtect is recorded by the OS event; the C code ignores it. -/
def enablePage (page : Expr) : List Command := [
  sp 53 (.plainLoad .loaded (.pageCount page)),
  sp 53 (.plainStore (.pageCount page) (add1 (reg .loaded))),
  spif 53 (.eq (reg .loaded) zero) [sp 66 (.protect page true)] []]

def disablePage (page : Expr) : List Command := [
  sp 75 (.plainLoad .loaded (.pageCount page)),
  sp 75 (.plainStore (.pageCount page) (.sub (reg .loaded) one)),
  spif 75 (.eq (reg .loaded) one) [sp 86 (.protect page false)] []]

/-- `safepoint.c:148,329`: C `a || b` does not execute b when a is
nonzero. The relaxed and acquire observations remain separate transitions. -/
def runningPrelude : List Command := [
  sp 329 (.load .running (.fixed .gcRunning) .relaxed),
  spif 329 (.eq (reg .running) zero)
    [sp 329 (.load .running (.fixed .gcRunning) .acquire)] []]

def statePrelude : List Command := [
  sp 148 (.load .state (.gcState T) .relaxed),
  spif 148 (nonzero (reg .state))
    [sp 148 (.load .state (.gcState T) .acquire)] []]

def suspendWaitCountLoad : Command :=
  sp 428 (.load .suspend (.suspendCount T) .acquire)

def resumeCountDecrement : Command :=
  sp 465 (.store (.suspendCount T) .relaxed (.sub (reg .resumeCount) one))

/-- Synchronization-control slices at the pinned commit. External boundaries
delimit allocator, scheduler, profiler and timing bodies. The straggler-timeout
branch retains its condition wait and diagnostic. Root tasks use the normal
non-copy-stack path and valid root-task exit. -/
def program : Proc → List Command
  | .stateSet => [
      gh 656 (.store (.gcState P) .release (reg .state)),
      .branch "src/julia_threads.h" 657
        (.either (.eq (reg .state) zero) (.eq (reg .oldState) zero))
        [.call "src/julia_threads.h" 658 .safepointCheck] [],
      .ret "src/julia_threads.h" 659]
  | .saveAndSet => [
      gh 664 (.load .oldState (.gcState P) .relaxed),
      .call "src/julia_threads.h" 664 .stateSet,
      .ret "src/julia_threads.h" 665]
  | .safepointCheck => [
      gh 639 .signalFence,
      gh 640 (.load .page (.safepoint P) .relaxed),
      gh 640 (.readPage .loaded (reg .page)),
      gh 641 .signalFence,
      .ret "src/julia_threads.h" 643]
  | .setGCAndWait => [
      sp 277 (.external "save errno/Windows last-error"),
      sp 283 (.load .handlerState (.gcState P) .relaxed),
      sp 284 (.store (.gcState P) .release one),
      sp 285 (.lock .safepoint),
      sp 286 (.broadcast .beginGC),
      sp 287 (.unlock .safepoint),
      callsp 288 .waitGC,
      sp 289 (.external "jl_gc_notify_task_resume"),
      sp 290 (.store (.gcState P) .release (reg .handlerState)),
      callsp 291 .waitResume,
      sp 295 (.external "restore errno/Windows last-error"), retsp 296]
  | .waitGC => [
      .whileDo "src/safepoint.c" 329 runningPrelude (nonzero (reg .running)) [
        sp 333 (.lock .safepoint),
        sp 334 (.load .running (.fixed .gcRunning) .relaxed),
        spif 334 (nonzero (reg .running))
          [sp 335 (.condWait .endGC .safepoint)] [],
        sp 336 (.unlock .safepoint)],
      sp 339 (.external "jl_gc_notify_task_resume when ct != NULL"), retsp 340]
  | .waitResume => [
      sp 350 (.load .resumeState (.gcState P) .relaxed),
      sp 351 (.store (.gcState P) .release one),
      sp 352 (.lock (.sleep P)),
      sp 353 (.load .suspend (.suspendCount P) .relaxed),
      spif 353 (nonzero (reg .suspend)) [
        sp 355 (.unlock (.sleep P)),
        sp 356 (.lock .safepoint),
        sp 357 (.broadcast .beginGC),
        sp 358 (.unlock .safepoint),
        sp 359 (.lock (.sleep P)),
        .whileDo "src/safepoint.c" 360
          [sp 360 (.load .suspend (.suspendCount P) .relaxed)]
          (nonzero (reg .suspend))
          [sp 361 (.condWait (.wake P) (.sleep P))]] [],
      sp 366 (.store (.gcState P) .release (reg .resumeState)),
      sp 367 (.unlock (.sleep P)),
      sp 368 (.external "jl_gc_notify_task_resume"), retsp 369]
  | .startGC => [
      sp 194 (.load .state (.gcState P) .relaxed),
      sp 195 (.lock .safepoint),
      sp 196 (.broadcast .beginGC),
      .whileDo "src/safepoint.c" 198
        [sp 198 (.load .suspend (.suspendCount P) .relaxed)]
        (nonzero (reg .suspend)) [
          sp 199 (.unlock .safepoint), callsp 200 .waitResume,
          sp 201 (.lock .safepoint)],
      sp 207 (.assign .running zero),
      sp 208 (.cas .result (.fixed .gcRunning) zero one),
      spif 208 (.eq (reg .result) zero) [
        sp 209 (.unlock .safepoint), callsp 210 .waitGC,
        sp 211 (.assign .result zero), retsp 211] [],
      sp 216 (.load .disabled (.fixed .disableCounter) .acquire),
      spif 216 (nonzero (reg .disabled)) [
        sp 217 (.store (.fixed .gcRunning) .release zero),
        sp 218 (.unlock .safepoint),
        sp 219 (.assign .result zero), retsp 219] [],
      .stmt "src/safepoint.c" 221 (.external "enable page 1 follows" )] ++
      enablePage one ++ enablePage (lit 2) ++ [
      sp 223 (.unlock .safepoint), sp 224 (.assign .result one), retsp 225]
  | .endGC => [sp 251 (.load .running (.fixed .gcRunning) .relaxed),
      sp 252 (.lock .safepoint)] ++ disablePage (lit 2) ++ disablePage one ++ [
      sp 258 (.store (.fixed .gcRunning) .release zero),
      sp 259 (.unlock .safepoint), sp 260 (.broadcast .endGC), retsp 261]
  | .worldWait => [
      sp 136 (.external "is_mutator = jl_get_pgcstack() != NULL"),
      sp 138 (.external "jl_wake_libuv when gc_n_threads > 1 or nonmutator"),
      sp 139 (.assign .i zero),
      .whileDo "src/safepoint.c" 139 [] (.lt (reg .i) (reg .gcCount)) [
        sp 140 (.plainLoad .target (.tlsSlot (reg .gcArray) (reg .i))),
        spif 141 (nonzero T) [
          .whileDo "src/safepoint.c" 148 statePrelude
            (.eq (reg .state) zero) [
              sp 153 (.lock .safepoint),
              sp 154 (.load .state (.gcState T) .relaxed),
              spif 154 (.eq (reg .state) zero)
                [sp 155 (.condWait .beginGC .safepoint)] [],
              sp 157 (.unlock .safepoint)]] [],
        sp 139 (.assign .i (add1 (reg .i)))], retsp 189]
  | .collect => [
      gc 3827 (.load .disabled (.fixed .disableCounter) .acquire),
      gcif 3827 (nonzero (reg .disabled)) [
        gc 3828 (.external "deferred allocation bookkeeping"),
        .ret "src/gc-stock.c" 3832] [],
      gc 3837 (.load .collectorOldState (.gcState P) .relaxed),
      gc 3838 (.store (.gcState P) .release one),
      gc 3839 (.external "save errno/Windows last-error"),
      .call "src/gc-stock.c" 3845 .startGC,
      gcif 3845 (.eq (reg .result) zero) [
        gc 3847 (.assign .state (reg .collectorOldState)),
        gc 3847 (.assign .oldState one),
        .call "src/gc-stock.c" 3847 .stateSet,
        .call "src/gc-stock.c" 3848 .waitResume,
        gcif 3849 (.eq (reg .collectorOldState) zero)
          [.call "src/gc-stock.c" 3850 .safepointCheck] [],
        .ret "src/gc-stock.c" 3855] [],
      gc 3870 .fence,
      gc 3871 (.load .gcCount (.fixed .nThreads) .acquire),
      gc 3871 (.plainStore (.fixed .gcNThreads) (reg .gcCount)),
      gc 3872 (.load .gcArray (.fixed .allTLS) .relaxed),
      gc 3872 (.plainStore (.fixed .gcAllTLS) (reg .gcArray)),
      .call "src/gc-stock.c" 3873 .worldWait,
      gc 3883 (.external "pre-GC callbacks"),
      gc 3886 (.load .disabled (.fixed .disableCounter) .acquire),
      gcif 3886 (.eq (reg .disabled) zero)
        [gc 3887 (.external "finalizers_lock"), gc 3888 .gcBody,
         gc 3894 (.external "unlock finalizers_lock")] [],
      gc 3897 (.plainStore (.fixed .gcNThreads) zero),
      gc 3898 (.plainStore (.fixed .gcAllTLS) zero),
      gc 3899 .endGCBody,
      .call "src/gc-stock.c" 3899 .endGC,
      gc 3900 (.assign .state (reg .collectorOldState)),
      gc 3900 (.assign .oldState one),
      .call "src/gc-stock.c" 3900 .stateSet,
      .call "src/gc-stock.c" 3902 .waitResume,
      gcif 3903 (.eq (reg .collectorOldState) zero)
        [.call "src/gc-stock.c" 3904 .safepointCheck] [],
      gc 3909 (.external "finalizers and post-GC callbacks"),
      .ret "src/gc-stock.c" 3925]
  | .enableNonmutator => [
      gc 3808 (.fetchAdd (.fixed .disableCounter) 1 true),
      .ret "src/gc-stock.c" 3814]
  | .disableNonmutator => [
      gc 3810 (.fetchAdd (.fixed .disableCounter) 1 false),
      .call "src/gc-stock.c" 3812 .waitGC,
      .ret "src/gc-stock.c" 3814]
  | .initTLS => [
      th 355 (.external "reject duplicate thread TLS / pgcstack"),
      th 366 (.external "allocate aligned TLS; abort on failure"),
      th 369 (.milestone (.tlsZeroed P) one),
      th 372 (.external "pthread_setspecific exit hook"),
      th 374 (.external "system_id = uv_thread_self"),
      th 375 (.external "rngseed = jl_rand"),
      th 385 (.store (.gcState P) .relaxed zero),
      thif 389 (.eq (reg .tid) zero)
        [th 390 (.store (.safepoint P) .relaxed one)]
        [th 393 (.store (.safepoint P) .relaxed (lit 2))],
      th 396 (.external "allocate and zero bt_data"),
      th 400 (.external "small_arraylist_new locks"),
      th 401 (.milestone (.heapReady P) one),
      th 402 (.milestone (.schedulerReady P) one),
      th 404 (.lock .tls),
      th 406 (.load .tid (.fixed .nThreads) .relaxed),
      th 407 (.plainStore (.tid P) (reg .tid)),
      th 408 (.load .array (.fixed .allTLS) .relaxed),
      th 409 (.plainLoad .size (.fixed .tlsSize)),
      thif 409 (.le (reg .size) (reg .tid)) [
        th 410 (.assign .newSize (.add (.add (reg .size) (reg .tid)) (lit 2))),
        th 411 (.external "calloc newArray/newSize; zero unused slots"),
        th 412 (.assign .i zero),
        .whileDo "src/threading.c" 412 [] (.lt (reg .i) (reg .size)) [
          th 413 (.plainLoad .slot (.tlsSlot (reg .array) (reg .i))),
          th 413 (.plainStore (.tlsSlot (reg .newArray) (reg .i)) (reg .slot)),
          th 412 (.assign .i (add1 (reg .i)))],
        th 415 (.store (.fixed .allTLS) .release (reg .newArray)),
        th 416 (.plainStore (.fixed .tlsSize) (reg .newSize)),
        th 417 (.external "jl_gc_add_quiescent old array; no immediate free"),
        th 418 (.assign .array (reg .newArray))] [],
      th 420 (.plainStore (.tlsSlot (reg .array) (reg .tid)) P),
      th 421 (.load .count (.fixed .nThreads) .relaxed),
      thif 421 (.lt (reg .count) (add1 (reg .tid)))
        [th 422 (.store (.fixed .nThreads) .release (add1 (reg .tid)))] [],
      th 423 .fence, th 424 (.unlock .tls),
      th 429 (.external "eager libunwind TLS allocation"),
      .ret "src/threading.c" 435]
  | .initRoot => [
      task 1548 (.external "zero stack bootstrap task"),
      task 1549 (.plainStore (.pgcstack P) (reg .bootstrap)),
      task 1550 (.external "bootstrap_task.ptls = ptls"),
      task 1551 (.external "allocate root Task with GC disabled"),
      task 1552 (.store (.taskHeader (reg .task)) .relaxed one),
      task 1553 (.milestone (.rootFieldsReady P) zero),
      task 1568 (.plainStore (.taskField (reg .task) .copyStack) zero),
      task 1569 (.external "ct->ctx.stkbuf = stack"),
      task 1570 (.external "ct->ctx.bufsz = ssize"),
      task 1578 (.plainStore (.taskField (reg .task) .started) one),
      task 1579 (.plainStore (.taskField (reg .task) .next) one),
      task 1580 (.plainStore (.taskField (reg .task) .queue) one),
      task 1581 (.store (.taskField (reg .task) .waitingOn) .relaxed one),
      task 1582 (.plainStore (.taskField (reg .task) .cachedWaitEntry) one),
      task 1583 (.plainStore (.taskField (reg .task) .cachedCancelEntry) one),
      task 1584 (.plainStore (.taskField (reg .task) .tls) one),
      task 1585 (.store (.taskField (reg .task) .state) .relaxed zero),
      task 1586 (.plainStore (.taskField (reg .task) .start) zero),
      task 1587 (.plainStore (.taskField (reg .task) .invoked) zero),
      task 1588 (.plainStore (.taskField (reg .task) .result) one),
      task 1589 (.plainStore (.taskField (reg .task) .doneNotify) one),
      task 1590 (.store (.taskField (reg .task) .isException) .relaxed zero),
      task 1591 (.plainStore (.taskField (reg .task) .scope) one),
      task 1592 (.plainStore (.taskField (reg .task) .eh) zero),
      task 1593 (.plainStore (.taskField (reg .task) .gcstack) zero),
      task 1594 (.plainStore (.taskField (reg .task) .excstack) zero),
      task 1595 (.store (.taskField (reg .task) .tid) .relaxed (reg .tid)),
      task 1596 (.external "ct->threadpoolid = jl_threadpoolid(ptls->tid)"),
      task 1597 (.plainStore (.taskField (reg .task) .sticky) one),
      task 1598 (.plainStore (.taskField (reg .task) .ptls) P),
      task 1599 (.plainStore (.taskField (reg .task) .worldAge) one),
      task 1600 (.plainStore (.taskField (reg .task) .reentrantTiming) zero),
      task 1601 (.store (.taskField (reg .task) .runningTimeNs) .relaxed zero),
      task 1602 (.store (.taskField (reg .task) .finishedAt) .relaxed zero),
      task 1603 (.external "metrics_enabled and timestamps"),
      task 1614 (.store (.taskField (reg .task) .firstEnqueuedAt) .relaxed zero),
      task 1615 (.store (.taskField (reg .task) .lastStartedRunningAt) .relaxed one),
      task 1616 (.plainStore (.taskField (reg .task) .boundCancelDefault) zero),
      task 1617 (.store (.taskField (reg .task) .resetCtx) .relaxed zero),
      task 1618 (.store (.taskField (reg .task) .cancelHandlerCtx) .relaxed zero),
      task 1619 (.plainStore (.abandonTo P) zero),
      task 1620 (.plainStore (.abandonNotify P) zero),
      task 1620 (.milestone (.rootFieldsReady P) one),
      task 1621 (.plainStore (.rootTask P) (reg .task)),
      task 1622 (.store (.currentTask P) .relaxed (reg .task)),
      task 1624 (.plainStore (.pgcstack P) (reg .task)),
      task 1635 (.external "jl_timing_block_task_enter"),
      .branch "src/task.c" 1658 (nonzero (reg .handleSignals))
        [task 1659 (.milestone (.handlersReady P) one)] [],
      .ret "src/task.c" 1661]
  | .adopt => [
      .call "src/threading.c" 466 .disableNonmutator,
      .call "src/threading.c" 471 .initTLS,
      th 473 (.external "jl_init_stack_limits"),
      .call "src/threading.c" 476 .initRoot,
      th 478 (.external "uv_random root RNG"),
      .call "src/threading.c" 479 .enableNonmutator,
      th 480 (.external "jl_init_task_lock; CANSAFEPOINT"),
      .ret "src/threading.c" 481]
  | .safeExit => [
      sp 268 (.store (.gcState P) .release (lit 2)),
      sp 269 (.lock .safepoint), sp 270 (.broadcast .beginGC),
      sp 271 (.unlock .safepoint), callsp 272 .waitGC, retsp 273]
  | .exitThread => [
      th 530 (.external "pthread_setspecific exit hook NULL"),
      th 535 (.load .oldState (.gcState P) .relaxed),
      th 535 (.assign .state zero),
      .call "src/threading.c" 535 .stateSet,
      th 536 (.external "scheduler_delete_thread"),
      th 538 (.load .current (.currentTask P) .relaxed),
      th 539 (.external "jl_task_frame_noreturn current/root; wrong-task exit aborts"),
      th 555 (.external "previous_exception = NULL"),
      th 557 (.plainStore (.rootTask P) zero),
      th 560 (.external "disable/free signal stack"),
      th 596 (.lock .profile),
      th 598 (.store (.currentTask P) .relaxed zero),
      th 607 (.unlock .profile),
      th 609 (.external "free bt_data and locks list"),
      th 615 (.external "jl_free_thread_gc_state"),
      .call "src/threading.c" 616 .safeExit,
      .ret "src/threading.c" 617]
  | .suspendThread => [
      sp 398 (.load .count (.fixed .nThreads) .acquire),
      spif 398 (.either (.signedNegative 32 (reg .tid)) (.le (reg .count) (reg .tid)))
        [sp 399 (.assign .result zero), retsp 399] [],
      sp 400 (.load .array (.fixed .allTLS) .relaxed),
      sp 400 (.plainLoad .target (.tlsSlot (reg .array) (reg .tid))),
      spif 401 (.eq T zero) [sp 404 (.assign .result zero), retsp 404] [],
      sp 401 (.load .current (.currentTask T) .relaxed),
      spif 402 (.eq (reg .current) zero)
        [sp 404 (.assign .result zero), retsp 404] [],
      sp 406 (.lock .safepoint), sp 407 (.lock (.sleep T)),
      sp 408 (.load .resumeCount (.suspendCount T) .relaxed),
      sp 408 (.assign .resumeCount (add1 (reg .resumeCount))),
      sp 409 (.store (.suspendCount T) .relaxed (reg .resumeCount)),
      spif 410 (.eq (reg .resumeCount) one)
        (enablePage (lit 3) ++ [
          sp 412 (.store (.safepoint T) .relaxed (lit 3)),
          sp 413 (.load .threaded (.fixed .threadedRegion) .seqCst),
          spif 413 (.eq (reg .threaded) zero)
            [sp 413 (.load .ioTid (.fixed .ioLoopTid) .relaxed)] [],
          spif 413 (.either (nonzero (reg .threaded)) (.eq (reg .tid) (reg .ioTid)))
            [sp 414 (.external "jl_wake_libuv")] []]) [],
      sp 416 (.unlock (.sleep T)),
      spif 417 (nonzero (reg .waitstate)) [
        spif 419 (.le (lit 2) (reg .waitstate)) [
          sp 424 (.unlock .safepoint), callsp 425 .setGCAndWait,
          sp 426 (.lock .safepoint)] [],
        .whileDo "src/safepoint.c" 428
          [suspendWaitCountLoad,
           spif 428 (nonzero (reg .suspend))
             [sp 429 (.load .state (.gcState T) .acquire)] []]
          (.both (nonzero (reg .suspend))
            (.either
              (.both (.le (reg .waitstate) (lit 2)) (.eq (reg .state) zero))
              (.both (.eq (reg .waitstate) (lit 3)) (.ne (reg .state) one))))
          [sp 434 (.condWait .beginGC .safepoint)]] [],
      sp 437 (.unlock .safepoint), sp 438 (.assign .result (reg .resumeCount)), retsp 439]
  | .resumeThread => [
      sp 445 (.load .count (.fixed .nThreads) .acquire),
      spif 445 (.either (.signedNegative 32 (reg .tid)) (.le (reg .count) (reg .tid)))
        [sp 446 (.assign .result zero), retsp 446] [],
      sp 447 (.load .array (.fixed .allTLS) .relaxed),
      sp 447 (.plainLoad .target (.tlsSlot (reg .array) (reg .tid))),
      spif 448 (.eq T zero) [sp 451 (.assign .result zero), retsp 451] [],
      sp 448 (.load .current (.currentTask T) .relaxed),
      spif 449 (.eq (reg .current) zero)
        [sp 451 (.assign .result zero), retsp 451] [],
      sp 453 (.lock .safepoint), sp 454 (.lock (.sleep T)),
      sp 455 (.load .resumeCount (.suspendCount T) .relaxed),
      spif 456 (.eq (reg .resumeCount) one) [
        spif 457 (.eq (reg .tid) zero)
          [sp 458 (.store (.safepoint T) .relaxed one)]
          [sp 460 (.store (.safepoint T) .relaxed (lit 2))],
        sp 461 (.signal (.wake T)), sp 462 (.broadcast .beginGC)] [],
      spif 464 (nonzero (reg .resumeCount))
        ([resumeCountDecrement,
          spif 466 (.eq (reg .resumeCount) one) (disablePage (lit 3)) []]) [],
      sp 469 (.unlock (.sleep T)), sp 470 (.unlock .safepoint),
      sp 471 (.assign .result (reg .resumeCount)), retsp 472]

/-- `current` selects the latest write; `chosen` accepts arbitrary read choices.
`src/julia_atomics.h:105-195,199-259`, `bbfa0ce4150`. -/
inductive ReadChoice where
  | current
  | chosen (value : Nat) (source : Option Nat)
  deriving DecidableEq, Repr, Inhabited

structure Choice where
  read : ReadChoice := .current
  protectSucceeds : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- OS events for `mprotect/VirtualProtect`, the volatile page load, and
`signals-unix.c:588-605`. The faulting instruction's continuation is saved. -/
inductive OSEvent where
  | protection (actor page : Nat) (enabled succeeded : Bool)
  | pageRead (actor page : Nat) (faulted : Bool) (pointerDependencies : List Nat)
  | delivery (actor page : Nat)
  | returnFromHandler (actor : Nat)
  deriving DecidableEq, Repr

/-- Source PC, C locals, saved calls, and condition/signal blocking state.
The head of `todo` is the next source statement. -/
structure Thread where
  todo : List Command := []
  calls : List (List Command) := []
  regs : Reg → Nat := fun _ => 0
  regSources : Reg → List Nat := fun _ => []
  controlSources : List Nat := []
  parked : Option (Nat × Nat) := none
  fault : Option Nat := none
  inHandler : Bool := false
  handlerDepth : Option Nat := none
  aborted : Bool := false
  criticalPermit : Bool := false

/-- C local widths: GC states are int8, tid/suspend values int16, and
the array sizes/counts/loop variables are int. Pointer IDs are logical
allocation identities and are not arithmetically truncated.
`julia_threads.h:179,186-199`; `threading.c:352,410,412`;
`safepoint.c:139,148,408,455`. -/
def localWidth : Reg → Option Nat
  | .state | .oldState | .collectorOldState | .handlerState | .resumeState => some 8
  | .suspend | .resumeCount | .ioTid => some 16
  | .tid | .count | .size | .newSize | .i | .gcCount | .threaded | .waitstate => some 32
  | _ => none

/-- Source memory for arbitrary finite actors, with independent allocation
identities, registered TLS pointer/count, and explicit memory choices. -/
structure Machine (n : Nat) where
  memory : Loc → Nat
  threads : Fin n → Thread
  pageProtected : Nat → Bool
  locks : Nat → Option (Fin n)
  conditions : Nat → Nat
  latest : Loc → Option Nat
  moClock : Loc → Nat
  scClock : Nat := 0
  candidate : Memory.Candidate Loc Nat
  os : List OSEvent := []
  sourceTrace : List (Nat × String × Nat) := []
  collectionActive : Bool := false
  criticalDuringGC : Bool := false

def replace [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

def setThread (s : Machine n) (t : Fin n) (thd : Thread) : Machine n :=
  { s with threads := replace s.threads t thd }

def setReg (thd : Thread) (dst : Reg) (value : Nat)
    (sources : List Nat := []) : Thread :=
  let value := match localWidth dst with
    | some bits => value % (2 ^ bits)
    | none => value
  { thd with
    regs := replace thd.regs dst value,
    regSources := replace thd.regSources dst sources }

def readChoice (s : Machine n) (l : Loc) (c : Choice) : Nat × Option Nat :=
  match c.read with
  | .current => (s.memory l, s.latest l)
  | .chosen value source => (value, source)

def emit (s : Machine n) (t : Fin n) (a : Memory.Action Loc Nat)
    (rf : Option Nat := none) (deps : List Nat := []) : Machine n :=
  let writes := a.writeValue.isSome
  let atomicWrite := writes && !a.isPlain
  let mo := if atomicWrite then s.moClock (a.location.getD .gcRunning) + 1 else 0
  let e : Memory.Event Loc Nat :=
    { thread := t.val, action := a, readFrom := rf, mo := mo,
      sc := s.scClock, dependsOn := (s.threads t).controlSources ++ deps }
  let s := { s with
    candidate := s.candidate.append e,
    scClock := s.scClock + if a.isSC then 1 else 0 }
  match a.location, a.writeValue with
  | some l, some v =>
      { s with
        memory := replace s.memory l (truncate l v),
        latest := replace s.latest l (some (s.candidate.events.size - 1)),
        moClock := if atomicWrite then replace s.moClock l mo else s.moClock }
  | _, _ => s

def next (s : Machine n) (t : Fin n) (thd : Thread) (tail : List Command) : Machine n :=
  setThread s t { thd with todo := tail }

def returnThread (s : Machine n) (t : Fin n) (thd : Thread) : Machine n :=
  match thd.calls with
  | [] => setThread s t { thd with todo := [] }
  | todo :: calls =>
      let handlerReturn := thd.inHandler && thd.handlerDepth == some calls.length
      { (setThread s t { thd with
          todo, calls,
          inHandler := if handlerReturn then false else thd.inHandler,
          handlerDepth := if handlerReturn then none else thd.handlerDepth }) with
        os := if handlerReturn then s.os ++ [.returnFromHandler t.val] else s.os }

/-- Heap/stack critical statements in root construction and thread cleanup,
including bootstrap Task allocation and root-field writes. `task.c:1549-1624`;
`threading.c:536-557,598,615`. -/
def sourceTouchesRoots (file : String) (line : Nat) (op : Op) : Bool :=
  if file = "src/task.c" then
    match op with
    | .plainStore (.taskField _ _) _ | .store (.taskField _ _) _ _
    | .plainStore (.rootTask _) _ | .plainStore (.pgcstack _) _
    | .store (.currentTask _) _ _ => true
    | .external _ => decide (line = 1551)
    | _ => false
  else if file = "src/threading.c" then
    decide (line = 536 ∨ line = 539 ∨ line = 557 ∨ line = 598 ∨ line = 615)
  else false

/-- One C statement, branch, or synthetic while-test continuation.
Locks block on contention. Condwait releases its mutex and parks; `wake`
explicitly reacquires it, including possible spurious wakeups. Atomic read
choices are accepted provisionally and checked on the complete candidate.
`julia_threads.h:638-643`, `safepoint.c:49-89,128-472`,
`threading.c:352-424,462-481,527-617`, `gc-stock.c:3805-3904`. -/
def step (s : Machine n) (t : Fin n) (c : Choice := {}) : Machine n :=
  let thd := s.threads t
  if thd.aborted || thd.parked.isSome || thd.fault.isSome then s else
  match thd.todo with
  | [] => returnThread s t thd
  | .ret file line :: _ =>
      returnThread { s with sourceTrace := s.sourceTrace ++ [(t.val, file, line)] } t thd
  | .call file line p :: tail =>
      setThread { s with sourceTrace := s.sourceTrace ++ [(t.val, file, line)] } t
        { thd with todo := program p, calls := tail :: thd.calls }
  | .branch file line test yes no :: tail =>
      next { s with sourceTrace := s.sourceTrace ++ [(t.val, file, line)] } t
        { thd with controlSources := thd.controlSources ++ test.sources thd.regSources }
        ((if test.eval thd.regs ≠ 0 then yes else no) ++ tail)
  | .whileDo file line prelude test body :: tail =>
      next s t thd (prelude ++ [.testLoop file line prelude test body] ++ tail)
  | .testLoop file line prelude test body :: tail =>
      next { s with sourceTrace := s.sourceTrace ++ [(t.val, file, line)] } t
        { thd with controlSources := thd.controlSources ++ test.sources thd.regSources }
        (if test.eval thd.regs ≠ 0 then
          body ++ [.whileDo file line prelude test body] ++ tail else tail)
  | .stmt file line op :: tail =>
      let logged := { s with
        sourceTrace := s.sourceTrace ++ [(t.val, file, line)],
        criticalDuringGC := s.criticalDuringGC ||
          (s.collectionActive && sourceTouchesRoots file line op) }
      let eval := Expr.eval thd.regs
      let addr := Addr.eval thd.regs
      let deps := Expr.sources thd.regSources
      let addrDeps := Addr.sources thd.regSources
      match op with
      | .assign dst value => next logged t (setReg thd dst (eval value) (deps value)) tail
      | .load dst loc order =>
          let (value, rf) := readChoice s (addr loc) c
          let out := emit logged t (.load (addr loc) order value) rf (addrDeps loc)
          next out t (setReg thd dst value [s.candidate.events.size]) tail
      | .store loc order value =>
          let thd := if addr loc = .gcState (thd.regs .ptls) then
              { thd with criticalPermit := false } else thd
          next (emit logged t (.store (addr loc) order (truncate (addr loc) (eval value)))
            none (addrDeps loc ++ deps value)) t thd tail
      | .plainLoad dst loc =>
          let (value, rf) := readChoice s (addr loc) c
          let out := emit logged t (.plainLoad (addr loc) value) rf (addrDeps loc)
          next out t (setReg thd dst value [s.candidate.events.size]) tail
      | .plainStore loc value =>
          next (emit logged t (.plainStore (addr loc) (truncate (addr loc) (eval value)))
            none (addrDeps loc ++ deps value)) t thd tail
      | .fetchAdd loc amount subtract =>
          let (value, rf) := readChoice s (addr loc) c
          let value' := if subtract then (value + 4294967296 - amount) % 4294967296
            else (value + amount) % 4294967296
          next (emit logged t (.rmw (addr loc) .seqCst value value') rf (addrDeps loc)) t thd tail
      | .cas dst loc expected desired =>
          let (value, rf) := readChoice s (addr loc) c
          let out := emit logged t
            (.cas (addr loc) .seqCst .seqCst (eval expected) (eval desired) value) rf
            (addrDeps loc ++ deps expected ++ deps desired)
          next out t (setReg thd dst (if value = eval expected then 1 else 0)
            [s.candidate.events.size]) tail
      | .fence => next (emit logged t (.fence .seqCst)) t thd tail
      | .signalFence => next (emit logged t (.signalFence .seqCst)) t thd tail
      | .lock mutex =>
          let m := mutex.eval thd.regs
          if s.locks m = none then
            next { (emit logged t (.lock m) none (mutex.sources thd.regSources)) with
              locks := replace s.locks m (some t) } t thd tail
          else s
      | .unlock mutex =>
          let m := mutex.eval thd.regs
          if s.locks m = some t then
            next { (emit logged t (.unlock m) none (mutex.sources thd.regSources)) with
              locks := replace s.locks m none } t thd tail
          else s
      | .condWait cond mutex =>
          let m := mutex.eval thd.regs
          if s.locks m = some t then
            setThread { (emit logged t (.unlock m) none (mutex.sources thd.regSources)) with
              locks := replace s.locks m none } t
              { thd with todo := tail, parked := some (cond.eval thd.regs, m) }
          else s
      | .broadcast cond | .signal cond =>
          let k := cond.eval thd.regs
          next { logged with conditions := replace s.conditions k (s.conditions k + 1) } t thd tail
      | .protect page enabled =>
          let p := eval page
          next { logged with
            pageProtected := if c.protectSucceeds then replace s.pageProtected p enabled else s.pageProtected,
            os := s.os ++ [.protection t.val p enabled c.protectSucceeds] } t thd tail
      | .readPage dst page =>
          let p := eval page
          let faulted := s.pageProtected p
          let out := { logged with
            os := s.os ++ [.pageRead t.val p faulted (thd.controlSources ++ deps page)] }
          if faulted then setThread out t { thd with fault := some p }
          else next out t
            { (setReg thd dst 0) with
              criticalPermit := decide (s.memory (.gcState (thd.regs .ptls)) = 0) } tail
      | .external _ => next logged t thd tail
      | .milestone field value =>
          next { logged with memory := replace s.memory (addr field) (eval value) } t thd tail
      | .critical =>
          if thd.criticalPermit then
            next { logged with criticalDuringGC := s.criticalDuringGC || s.collectionActive } t thd tail
          else setThread logged t { thd with aborted := true }
      | .gcBody => next { logged with collectionActive := true } t thd tail
      | .endGCBody => next { logged with collectionActive := false } t thd tail
      | .abort => setThread logged t { thd with aborted := true }

/-- Condwait may wake spuriously, but returning requires its mutex. No
fairness is assumed (`safepoint.c:155,335,361,434`). -/
def wake (s : Machine n) (t : Fin n) : Machine n :=
  let thd := s.threads t
  match thd.parked with
  | none => s
  | some (_, m) =>
      if s.locks m = none then
        setThread { (emit s t (.lock m)) with locks := replace s.locks m (some t) } t
          { thd with parked := none }
      else s

/-- The ordinary safepoint fault path of `signals-unix.c:588-605`.
Delivery is a separate scheduler event. Invalid handler entry aborts; valid
entry preserves the faulting page-load continuation for retry. -/
def deliver (s : Machine n) (t : Fin n) : Machine n :=
  let thd := s.threads t
  match thd.fault with
  | none => s
  | some page =>
      if s.memory (.handlersReady (thd.regs .ptls)) = 1 ∧
          s.memory (.gcState (thd.regs .ptls)) ≠ 1 then
        setThread { s with os := s.os ++ [.delivery t.val page] } t
          { thd with
            todo := program .setGCAndWait,
            calls := thd.todo :: thd.calls, fault := none, inHandler := true,
            handlerDepth := some thd.calls.length }
      else setThread s t { thd with aborted := true }

inductive Scheduled (n : Nat) where
  | source (thread : Fin n) (choice : Choice := {})
  | wake (thread : Fin n)
  | deliver (thread : Fin n)

def advance (s : Machine n) : Scheduled n → Machine n
  | .source t c => step s t c
  | .wake t => wake s t
  | .deliver t => deliver s t

def run (s : Machine n) : List (Scheduled n) → Machine n
  | [] => s
  | event :: events => run (advance s event) events

/-- Source/OS trace assumptions, `safepoint.c:49-89` and
`signals-unix.c:588-605`. Successful page protection is an explicit platform
assumption because the C code does not check mprotect's result. The source
machine enforces fault blocking and retry. -/
def PlatformTraceContract (s : Machine n) : Prop :=
  (∀ actor page enabled ok,
    OSEvent.protection actor page enabled ok ∈ s.os → ok = true) ∧
  (∀ actor page, OSEvent.delivery actor page ∈ s.os → actor < n)

/-- Finite registered TLS entries, initialized live roots, valid TLS IDs,
and initial critical-operation permissions. `threading.c:420-424,611-616`;
`julia_threads.h:185-198`. -/
def WellFormed (s : Machine n) : Prop :=
  n ≤ 32767 ∧ s.memory .nThreads ≤ n ∧
  (∀ i, i < s.memory .nThreads →
    let p := s.memory (.tlsSlot (s.memory .allTLS) i)
    p = 0 ∨ (p ≤ n ∧ s.memory (.tlsZeroed p) = 1 ∧
      (s.memory (.currentTask p) = 0 ∨ s.memory (.rootFieldsReady p) = 1))) ∧
  (∀ t : Fin n, (s.threads t).regs .ptls ≤ n) ∧
  s.criticalDuringGC = false ∧
  (s.collectionActive = true → ∀ t : Fin n, (s.threads t).criticalPermit = false)


/-- Public API client entry points. The controller suspends a different
thread while GC-unsafe, enters GC-safe mode through the actual state helper,
resumes the target, and has a normal unsafe-return continuation.
`julia.h:1342,1345`;
`julia_threads.h:677,679-680`; `gc-stock.c:3821`. -/
inductive EntryPC where
  | collector | safeTarget | controller | idle
  deriving DecidableEq, Repr

def entryCommands : EntryPC → List Command
  | .collector => [.call "src/gc-stock.c" 3821 .collect]
  | .safeTarget => [.call "src/julia_threads.h" 677 .saveAndSet,
      .stmt "src/gc-stock.c" 96 .critical]
  | .controller => [
      .call "src/julia.h" 1342 .suspendThread,
      gh 679 (.assign .state (lit 2)),
      .call "src/julia_threads.h" 679 .saveAndSet,
      .call "src/julia.h" 1345 .resumeThread,
      gh 680 (.assign .state zero),
      gh 680 (.assign .oldState (lit 2)),
      .call "src/julia_threads.h" 680 .stateSet]
  | .idle => []

/-- The recorded source PCs and C arguments at a public client entry.
Registered roots are initialized. Suspension begins at its
public entry with a valid distinct live target and waitstate=1.
`threading.c:420-424`; `safepoint.c:398-409`; `julia_threads.h:677-680`. -/
def ThreadAtPublicEntry (s : Machine n) (role : Fin n → EntryPC) (t : Fin n) : Prop :=
  let thd := s.threads t
  thd.todo = entryCommands (role t) ∧ thd.calls = [] ∧
  thd.parked = none ∧ thd.fault = none ∧ thd.inHandler = false ∧
  thd.handlerDepth = none ∧ thd.aborted = false ∧
  0 < thd.regs .ptls ∧ thd.regs .ptls ≤ n ∧
  s.memory (.heapReady (thd.regs .ptls)) = 1 ∧
  s.memory (.schedulerReady (thd.regs .ptls)) = 1 ∧
  s.memory (.rootFieldsReady (thd.regs .ptls)) = 1 ∧
  s.memory (.currentTask (thd.regs .ptls)) ≠ 0 ∧
  s.memory (.rootTask (thd.regs .ptls)) ≠ 0 ∧
  s.memory (.pgcstack (thd.regs .ptls)) ≠ 0 ∧
  s.memory (.tid (thd.regs .ptls)) = t.val ∧ t.val < s.memory .nThreads ∧
  s.memory (.safepoint (thd.regs .ptls)) = (if t.val = 0 then 1 else 2) ∧
  s.memory (.tlsSlot (s.memory .allTLS) t.val) = thd.regs .ptls ∧
  s.memory (.handlersReady (thd.regs .ptls)) = 1 ∧
  (match role t with
   | .collector => s.memory (.gcState (thd.regs .ptls)) = 0
   | .safeTarget => s.memory (.gcState (thd.regs .ptls)) = 2 ∧ thd.regs .state = 0
   | .controller => s.memory (.gcState (thd.regs .ptls)) = 0 ∧
       thd.regs .waitstate = 1 ∧ thd.regs .tid < s.memory .nThreads ∧
       let target := s.memory (.tlsSlot (s.memory .allTLS) (thd.regs .tid))
       target ≠ 0 ∧ target ≠ thd.regs .ptls ∧ s.memory (.currentTask target) ≠ 0
   | .idle => s.memory (.gcState (thd.regs .ptls)) = 2)

/-- Admissible source starts have public entry PCs, no pending suspension,
GC or protected pages, and initialized registered roots.
`safepoint.c:19,34,91-125`;
`threading.c:352-424,462-481`; `task.c:1621-1659`. -/
def PublicAPIEntry (s : Machine n) (role : Fin n → EntryPC) : Prop :=
  WellFormed s ∧ s.collectionActive = false ∧
  s.memory .gcRunning = 0 ∧ s.memory .disableCounter = 0 ∧
  s.memory .gcNThreads = 0 ∧ s.memory .gcAllTLS = 0 ∧
  (∀ page, s.pageProtected page = false ∧ s.memory (.pageCount page) = 0) ∧
  (∀ mutex, s.locks mutex = none) ∧
  (∀ t : Fin n, s.memory (.suspendCount ((s.threads t).regs .ptls)) = 0 ∧
    ThreadAtPublicEntry s role t)

/-- An interpreter prefix from public API entries, retaining the complete
candidate, read-from, modification-order, dependency, and lock histories. -/
def SourceReachableCheckpoint (s : Machine n) : Prop :=
  ∃ initial : Machine n, ∃ role : Fin n → EntryPC, ∃ front : List (Scheduled n),
    PublicAPIEntry initial role ∧ s = run initial front

/-- Model-scoped GC-critical exclusion from an admitted `PublicAPIEntry`.
`SourceReachableCheckpoint` does not prove Julia startup or adoption reaches
that entry. `criticalDuringGC` records `.critical` and `sourceTouchesRoots`,
and `PlatformTraceContract` requires successful protection events.
Defined checks the global prefix-plus-suffix C11 execution.
`gc-stock.c:96-105`; `safepoint.c:128-224,443-472`;
`julia_threads.h:638-680`. -/
def stoppedWorldExcludesCriticalExecution : Prop :=
  ∀ n (s : Machine n), SourceReachableCheckpoint s →
    ∀ schedule : List (Scheduled n),
      let out := run s schedule
      out.candidate.defined = true → PlatformTraceContract out →
      out.criticalDuringGC = false

instance finiteForall (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∀ i, p i) :=
  decidable_of_iff (∀ i ∈ List.finRange n, p i) (by simp)

instance boolForall (p : Bool → Prop) [DecidablePred p] :
    Decidable (∀ b, p b) :=
  decidable_of_iff (p false ∧ p true) (by
    constructor
    · intro h b
      cases b
      · exact h.1
      · exact h.2
    · intro h
      exact ⟨h false, h true⟩)


end JuliaLean.CRuntime.WorldStop
