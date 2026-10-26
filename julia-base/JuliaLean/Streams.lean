import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Streams.Model
import JuliaLean.Streams.Props
import JuliaLean.Streams.Proofs
import JuliaLean.Streams.Refutations
import JuliaLean.Streams.Coverage
import JuliaLean.Streams.Methods

namespace JuliaLean.Streams

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := Methods.entries ++ [
  { id := "streams-coverage-stream-lifecycle", juliaFile := "base/stream.jl"
    juliaFns := ["LibuvStream/LibuvServer field forwarding", "PipeEndpoint", "TTY", "uv_status_string",
      "isreadable", "iswritable", "isopen", "check_open", "wait_readnb", "closewrite", "close",
      "uvfinalize", "link_pipe!", "start_reading", "stop_reading", "uv_readcb"]
    statement := "Libuv stream construction, status rendering, readability/writability checks, buffered wait transitions, close paths, pipe linking, and read callbacks follow their source branches."
    source := "base/stream.jl:29-1185"
    status := .proven, prop := ``StreamLifecycleCoverage, thm := some ``streamLifecycleCoverage_proven },
  { id := "streams-coverage-stream-requests", juliaFile := "base/stream.jl"
    juliaFns := ["UvReqWait", "_begin_uvreq_wait!", "_end_uvreq_wait!", "_wait_uvreq",
      "_claim_uvreq_waiter", "_uv_write_wait", "_uv_write_cancelled_finish", "_split_complete",
      "_end_split_uvreq_wait!", "uv_write_async", "uv_writecb_task", "uv_shutdowncb_task",
      "_requeue_unwritten!", "flush", "writepartial"]
    statement := "Libuv request waits preserve completion versus detachment ownership, cancellation marking, rooted buffers, split-write counts, first-error selection, and unwritten-byte order."
    source := "base/stream.jl:444-718,1347-1913"
    status := .proven, prop := ``StreamRequestCoverage, thm := some ``streamRequestCoverage_proven },
  { id := "streams-coverage-stream-readwrite", juliaFile := "base/stream.jl"
    juliaFns := ["readbytes!", "read", "unsafe_read", "readavailable", "copyuntil", "uv_write",
      "write", "unsafe_write", "buffer_writes"]
    statement := "Libuv read and write adapters preserve byte order, requested counts, first-delimiter consumption, chunk sizes, and owner-carrying dispatch."
    source := "base/stream.jl:1190-1349,1604-1854"
    status := .proven, prop := ``StreamReadWriteCoverage, thm := some ``streamReadWriteCoverage_proven },
  { id := "streams-coverage-stream-redirect", juliaFile := "base/stream.jl"
    juliaFns := ["_fd", "RedirectStdStream", "redirect_stdio", "resolve", "same_path", "Pipe iteration",
      "mark", "unmark", "reset", "ismarked", "peek"]
    statement := "Standard-stream redirection resolves keep/path/stream inputs in fd order, Pipe exposes its two endpoints in order, and mark/peek methods forward to the receive buffer."
    source := "base/stream.jl:1916-2205"
    status := .proven, prop := ``StreamRedirectCoverage, thm := some ``streamRedirectCoverage_proven },
  { id := "streams-coverage-bufferstream", juliaFile := "base/stream.jl"
    juliaFns := ["BufferStream", "closewrite", "close", "read", "unsafe_read", "bytesavailable",
      "isreadable", "iswritable", "wait_readnb", "readavailable", "readbytes!", "readuntil",
      "wait_close", "write", "unsafe_write", "eof", "flush", "skip", "reseteof"]
    statement := "BufferStream methods use one FIFO buffer, retain buffered reads after close, reject closed writes, preserve exact read/write counts, and reset only EOF state."
    source := "base/stream.jl:2210-2446"
    status := .proven, prop := ``BufferStreamCoverage, thm := some ``bufferStreamCoverage_proven },
  { id := "streams-coverage-iostream-lifecycle", juliaFile := "base/iostream.jl"
    juliaFns := ["IOStream", "_lock_ios", "fd", "stat", "isopen", "close", "closewrite", "flush",
      "iswritable", "isreadable", "truncate", "seek", "seekstart", "seekend", "skip", "position",
      "filesize", "eof", "fdio", "open", "write", "unsafe_write"]
    statement := "IOStream construction, locking, open-mode selection, state queries, seek/truncate arithmetic, close/flush, and writes follow the ios.c wrapper branches and return counts."
    source := "base/iostream.jl:13-426"
    status := .proven, prop := ``IOStreamLifecycleCoverage, thm := some ``ioStreamLifecycleCoverage_proven },
  { id := "streams-coverage-iostream-read", juliaFile := "base/iostream.jl"
    juliaFns := ["bytesavailable", "readavailable", "read", "unsafe_read", "take!", "readuntil",
      "readuntil_string", "readline", "copyuntil", "readbytes_all!", "readbytes_some!", "readbytes!", "peek"]
    statement := "IOStream read adapters consume from the current position in canonical byte order, distinguish exact from partial counts, implement delimiter/line rules, and preserve peek position."
    source := "base/iostream.jl:429-664"
    status := .proven, prop := ``IOStreamReadCoverage, thm := some ``ioStreamReadCoverage_proven },
  { id := "streams-coverage-libuv-handles", juliaFile := "base/libuv.jl"
    juliaFns := ["uv_sizeof_handle", "uv_sizeof_req", "uv_handle_data", "uv_req_data", "uv_req_set_data",
      "handle_as", "associate_julia_struct", "disassociate_julia_struct", "iolock_begin", "iolock_end",
      "preserve_handle", "unpreserve_handle"]
    statement := "Libuv handle wrappers preserve association identity, balanced handle preservation, request data ownership, and iolock nesting around foreign calls."
    source := "base/libuv.jl:8-82"
    status := .proven, prop := ``LibuvHandleCoverage, thm := some ``libuvHandleCoverage_proven },
  { id := "streams-coverage-libuv-errors", juliaFile := "base/libuv.jl"
    juliaFns := ["IOError", "showerror", "_UVError", "struverror", "uverrorname", "uv_error", "eventloop",
      "uv_unref", "uv_ref", "process_events", "callback declarations", "reinit_stdio", "_reinit_stdio"]
    statement := "Libuv error wrappers throw only for negative codes and retain code/name/description text; loop references and stdio reinitialization follow handle-kind branches."
    source := "base/libuv.jl:89-163"
    status := .proven, prop := ``LibuvErrorCoverage, thm := some ``libuvErrorCoverage_proven },
  { id := "streams-coverage-asyncevent-constructors", juliaFile := "base/asyncevent.jl"
    juliaFns := ["AsyncCondition", "Timer", "getproperty", "propertynames", "show", "unsafe_convert"]
    statement := "AsyncCondition and Timer constructors initialize live unset handles, timer durations use the documented millisecond rounding and timeout compensation, and accessors recover the public durations."
    source := "base/asyncevent.jl:17-172"
    status := .proven, prop := ``AsyncConstructionCoverage, thm := some ``asyncConstructionCoverage_proven },
  { id := "streams-coverage-asyncevent-utilities", juliaFile := "base/asyncevent.jl"
    juliaFns := ["sleep", "Timer(::Function,...)", "timedwait", "TimeoutWait", "wait_enqueue!", "wait_dequeue!"]
    statement := "Sleep closes its timer on every exit, callback timers consume pending events until close, timedwait returns on the first successful poll, and TimeoutWait arms then closes its timer."
    source := "base/asyncevent.jl:361-544"
    status := .proven, prop := ``AsyncUtilityCoverage, thm := some ``asyncUtilityCoverage_proven },
  { id := "streams-coverage-process-spawn", juliaFile := "base/process.jl"
    juliaFns := ["Process", "ProcessChain", "uvfinalize", "uv_return_spawn", "_uv_hook_close",
      "as_cpumask", "_spawn_primitive", "_spawn", "_stdio_copy"]
    statement := "Process construction initializes sentinel status fields, spawn rejects empty leaves, composite commands spawn left before right, and exit callbacks store exact code and signal before notification."
    source := "base/process.jl:3-255"
    status := .proven, prop := ``ProcessSpawnCoverage, thm := some ``processSpawnCoverage_proven },
  { id := "streams-coverage-process-stdio", juliaFile := "base/process.jl"
    juliaFns := ["setup_stdios", "setup_stdio", "close_stdio", "spawn_opts_swallow", "spawn_opts_inherit"]
    statement := "Process stdio setup pads descriptor slots, selects the correct pipe endpoint direction, tracks parent-owned handles and copy tasks, and closes only handles it opened."
    source := "base/process.jl:258-381"
    status := .proven, prop := ``ProcessStdioCoverage, thm := some ``processStdioCoverage_proven },
  { id := "streams-coverage-process-open", juliaFile := "base/process.jl"
    juliaFns := ["eachline(::AbstractCmd)", "open(::AbstractCmd,...)", "read(::AbstractCmd)", "run(::AbstractCmd)"]
    statement := "Process open mode parsing selects read/write pipes exactly, do-block open closes and status-checks on every path, and run/read choose inherited versus swallowed stdio before checking status."
    source := "base/process.jl:383-580"
    status := .proven, prop := ``ProcessOpenCoverage, thm := some ``processOpenCoverage_proven },
  { id := "streams-coverage-process-sequence", juliaFile := "base/process.jl"
    juliaFns := ["success", "ProcessFailedException", "showerror", "pipeline_error", "kill", "getpid",
      "process_running", "process_exited", "process_signaled", "process_status", "wait", "show", "Cmd sequence methods"]
    statement := "Process status, wait, error display/filtering, kill/getpid, vector/chain aggregation, and Cmd sequence forwarding preserve source order and exact stored status fields."
    source := "base/process.jl:582-780"
    status := .proven, prop := ``ProcessSequenceCoverage, thm := some ``processSequenceCoverage_proven },
  { id := "streams-write-read-fifo", juliaFile := "base/stream.jl"
    juliaFns := ["write/unsafe_write(::LibuvStream)", "readavailable(::LibuvStream)",
      "write/unsafe_write(::BufferStream)", "readavailable(::BufferStream)",
      "write/unsafe_write(::IOStream)", "readavailable(::IOStream)"]
    statement := "Bytes accepted by a PipeEndpoint peer or BufferStream are returned in order; an IOStream returns them in order after seekstart."
    source := "base/io.jl:267-271 (write); base/iostream.jl:158-185; base/stream.jl:1292-1300,2277-2287; invariant (FIFO stream)"
    status := .proven, prop := ``WriteReadFIFO, thm := some ``writeReadFIFO_proven },
  { id := "streams-unsafe-lengths", juliaFile := "base/stream.jl"
    juliaFns := ["unsafe_read(::LibuvStream, ::Ptr{UInt8}, ::UInt)",
      "unsafe_write(::LibuvStream, ::Ptr{UInt8}, ::UInt)",
      "unsafe_read(::BufferStream, ::Ptr{UInt8}, ::UInt)",
      "unsafe_write(::BufferStream, ::Ptr{UInt8}, ::UInt)",
      "unsafe_read(::IOStream, ::Ptr{UInt8}, ::UInt)",
      "unsafe_write(::IOStream, ::Ptr{UInt8}, ::UInt)"]
    statement := "For a pointer valid for n bytes, unsafe_write accepts exactly n bytes and unsafe_read returns exactly the requested n leading bytes or EOFError."
    source := "base/stream.jl:1240-1275,1736-1739,2249-2255,2404-2413; base/iostream.jl:416-425,477-483"
    status := .proven, prop := ``UnsafeLengthsExact, thm := some ``unsafeLengthsExact_proven },
  { id := "streams-readavailable-buffer", juliaFile := "base/stream.jl"
    juliaFns := ["readavailable(::LibuvStream)", "readavailable(::BufferStream)", "readavailable(::IOStream)"]
    statement := "readavailable returns and consumes every byte currently buffered, in order."
    source := "base/stream.jl:1292-1300,2277-2287; base/iostream.jl:431-442"
    status := .proven, prop := ``ReadAvailableExact, thm := some ``readAvailableExact_proven },
  { id := "streams-delimiter-handling", juliaFile := "base/stream.jl"
    juliaFns := ["readuntil(::LibuvStream, ::UInt8)", "readuntil(::BufferStream, ::UInt8)",
      "readuntil(::IOStream, ::UInt8/AbstractChar)", "readline(::IOStream)", "readline(::IO)"]
    statement := "readuntil returns bytes through the first delimiter iff keep=true and consumes that delimiter; readline additionally removes CRLF when keep=false."
    source := "base/io.jl:636-648,668-687; base/stream.jl:1302-1344,2339-2360; base/iostream.jl:490-508"
    status := .proven, prop := ``DelimiterHandling, thm := some ``delimiterHandling_proven },
  { id := "streams-closed-reads-stay-closed", juliaFile := "base/stream.jl"
    juliaFns := ["unsafe_read", "readavailable", "readuntil", "readline"]
    statement := "Reading buffered data from a closed stream, when permitted, never reopens it."
    source := "invariant; base/iostream.jl:83-84 (closed IOStream may retain readable buffered data)"
    status := .proven, prop := ``ClosedReadsStayClosed, thm := some ``closedReadsStayClosed_proven },
  { id := "streams-close-monotone", juliaFile := "base/stream.jl"
    juliaFns := ["close(::LibuvStream)", "close(::BufferStream)", "close(::IOStream)", "isopen", "eof"]
    statement := "close is idempotent, a closed stream stays closed, and buffered data delays eof without making isopen true."
    source := "base/io.jl:51-55,208-215; base/stream.jl:770-783,2219-2236; base/iostream.jl:78-93"
    status := .proven, prop := ``CloseMonotone, thm := some ``closeMonotone_proven },
  { id := "streams-closed-libuv-write", juliaFile := "base/stream.jl"
    juliaFns := ["unsafe_write(::LibuvStream)", "unsafe_write(::BufferStream)", "check_open"]
    statement := "A write to a closed LibuvStream or BufferStream raises an IOError."
    source := "base/stream.jl:384-388,1736-1739,2404-2413"
    status := .proven, prop := ``ClosedLibuvWritesError, thm := some ``closedLibuvWritesError_proven },
  { id := "streams-iostream-closed-write", juliaFile := "base/iostream.jl"
    juliaFns := ["iswritable(::IOStream)", "write(::IOStream, ::UInt8)", "unsafe_write(::IOStream, ::Ptr{UInt8}, ::UInt)"]
    statement := "A closed IOStream is not writable and a nonempty write raises an error."
    source := "base/iostream.jl:79-84,104,411-425; base/io.jl:186-188,267-271"
    status := .refuted, prop := ``ClosedIOStreamWriteErrors,
    thm := some ``closedIOStreamWriteErrors_refuted
    issue := "#64218"
    notes := "After close, isopen(io) == false but iswritable(io) == true; byte and string writes return 0 on 1.13.2 and master." },
  { id := "streams-event-close-idempotent", juliaFile := "base/asyncevent.jl"
    juliaFns := ["close(::Union{Timer,AsyncCondition})", "isopen", "wait", "uv_asynccb", "uv_timercb"]
    statement := "Closing a Timer or AsyncCondition is idempotent, prevents new events, and wait on a closed object without a pending event throws EOFError."
    source := "base/asyncevent.jl:9-15,74-87,177-292,328-358"
    status := .proven, prop := ``EventCloseIdempotent, thm := some ``eventCloseIdempotent_proven },
  { id := "streams-timer-one-shot-wait", juliaFile := "base/asyncevent.jl"
    juliaFns := ["Timer", "_trywait", "wait", "uv_timercb"]
    statement := "After a one-shot Timer fires, every later wait returns immediately even though the timer is inactive."
    source := "base/asyncevent.jl:77-87,116-118,177-243,340-358"
    status := .proven, prop := ``OneShotWaitPersistent, thm := some ``oneShotWaitPersistent_proven
    notes := "Master behavior; the docstring records that releases before Julia 1.14 threw EOFError after the first wait." },
  { id := "streams-event-pending-close", juliaFile := "base/asyncevent.jl"
    juliaFns := ["Timer(::Function,...)", "AsyncCondition(::Function)", "close", "_trywait"]
    statement := "A Timer or AsyncCondition event already pending at close can be observed one final time without reopening the object."
    source := "base/asyncevent.jl:47-69,177-243,257-292,385-453"
    status := .proven, prop := ``PendingEventSurvivesClose, thm := some ``pendingEventSurvivesClose_proven },
  { id := "streams-pipeline-left-associative", juliaFile := "base/cmd.jl"
    juliaFns := ["pipeline(from, to, ...)"]
    statement := "A multi-stage pipeline is chained from left to right."
    source := "base/cmd.jl:559-576 (pipeline docstring and implementation)"
    status := .proven, prop := ``PipelineLeftAssociative, thm := some ``pipelineLeftAssociative_proven },
  { id := "streams-ignorestatus-stderr-pipeline", juliaFile := "base/cmd.jl"
    juliaFns := ["ignorestatus(::AbstractCmd)", "pipeline(::AbstractCmd; stderr=::AbstractCmd)"]
    statement := "ignorestatus accepts every command object, including a pipeline that redirects stderr to another command."
    source := "base/cmd.jl:297-305,512-540"
    status := .refuted, prop := ``IgnoreStatusAllCommands,
    thm := some ``ignoreStatusAllCommands_refuted
    issue := "#64219"
    notes := "pipeline(cmd; stderr=othercmd) is ErrOrCmds; ignorestatus throws MethodError on 1.13.2 and master because only OrCmds and AndCmds are included." },
  { id := "streams-detach-flag", juliaFile := "base/cmd.jl"
    juliaFns := ["detach(::Cmd)", "Cmd(::Cmd; detach)"]
    statement := "detach sets the detached process flag and preserves the command, environment, and ignorestatus setting."
    source := "base/cmd.jl:27-38,308-312"
    status := .proven, prop := ``DetachSetsFlag, thm := some ``detachSetsFlag_proven },
  { id := "streams-detach-pipeline", juliaFile := "base/cmd.jl"
    juliaFns := ["detach(::AbstractCmd)", "pipeline(::AbstractCmd, ::AbstractCmd)"]
    statement := "detach accepts every command object that run accepts, including pipeline command objects."
    source := "base/cmd.jl:308-312,559-576"
    status := .refuted, prop := ``DetachAllCommands,
    thm := some ``detachAllCommands_refuted
    issue := "none found (queries: detach pipeline; detach OrCmds)"
    notes := "detach(pipeline(`/bin/true`, `/bin/cat`)) throws MethodError on 1.13.2 and master; only detach(::Cmd) is defined." },
  { id := "streams-process-status", juliaFile := "base/process.jl"
    juliaFns := ["uv_return_spawn", "test_success", "success", "process_status"]
    statement := "success is true exactly for exit code zero with no signal, and process_status reports the exact terminating signal."
    source := "base/process.jl:62-78,582-622,730-736"
    status := .proven, prop := ``ProcessStatusExact, thm := some ``processStatusExact_proven },
  { id := "streams-process-failure-contents", juliaFile := "base/process.jl"
    juliaFns := ["ProcessFailedException", "pipeline_error(::ProcessChain)"]
    statement := "ProcessFailedException contains exactly the failed non-ignored processes in pipeline order."
    source := "base/process.jl:625-665"
    status := .proven, prop := ``ProcessFailureContents, thm := some ``processFailureContents_proven },
  { id := "streams-run-read-status", juliaFile := "base/process.jl"
    juliaFns := ["run(::AbstractCmd)", "read(::AbstractCmd)", "success", "pipeline_error"]
    statement := "run and read(command) apply the same exit-status rule, and successful read returns the captured bytes exactly."
    source := "base/process.jl:510-579,593-665"
    status := .proven, prop := ``RunReadStatusHandling, thm := some ``runReadStatusHandling_proven },
  { id := "streams-kill-signal", juliaFile := "base/process.jl"
    juliaFns := ["kill(::Process, ::Integer)", "uv_return_spawn", "process_status"]
    statement := "kill is a successful no-op after exit; otherwise the process reports the exact terminating signal and a zero exit code."
    source := "base/process.jl:62-78,667-688,730-736"
    status := .proven, prop := ``KillReportsSignal, thm := some ``killReportsSignal_proven }
]

end JuliaLean.Streams
