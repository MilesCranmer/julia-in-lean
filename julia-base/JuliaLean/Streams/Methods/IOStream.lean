import JuliaLean.Streams.Methods.Support

namespace JuliaLean.Streams.Methods.IOStream

open JuliaLean.Streams JuliaLean.Streams.Methods JuliaLean.Registry

structure NamedIO where
  name : String
  file : IOFileM
  finalize : Bool
  locking : Bool
  deriving Repr, DecidableEq

structure OpenFlagsM where
  read : Bool
  write : Bool
  create : Bool
  truncate : Bool
  append : Bool
  deriving Repr, DecidableEq

def resolveFlags (read write create truncate append : Option Bool) : OpenFlagsM :=
  let append' := append.getD false
  let provisionalWrite := write.getD (truncate.getD false || append')
  let read' := read.getD (!provisionalWrite)
  let write' := write.getD ((truncate.getD (!read' && provisionalWrite)) || append')
  let truncate' := truncate.getD (!read' && write')
  let create' := create.getD ((!read' && write') || truncate' || append')
  ⟨read', write', create', truncate', append'⟩

/-- Inner `IOStream(name, buf)`, `base/iostream.jl:21`. -/
def m21 (name : String) (buffer : List UInt8) : NamedIO :=
  ⟨name, ⟨buffer, 0, true, true, true⟩, false, true⟩

/-- `IOStream(name, finalize)`, `base/iostream.jl:24-31`. -/
def m24 (name : String) (finalize : Bool) : NamedIO :=
  { m21 name [] with finalize }

/-- `IOStream(name)`, `base/iostream.jl:32`. -/
def m32 (name : String) : NamedIO := m24 name true

/-- Pointer conversion, `base/iostream.jl:34`. -/
def m34 (pointer : Nat) : Nat := pointer

/-- IOStream display, `base/iostream.jl:35`. -/
def m35 (stream : NamedIO) : String := "IOStream(" ++ stream.name ++ ")"

/-- `_lock_ios`, `base/iostream.jl:37-47`. -/
def m37 (_locking : Bool) (value : α) : α := value

/-- `fd(s::IOStream)`, `base/iostream.jl:74`. -/
def m74 (foreignFd : Int) : Int := foreignFd

/-- `stat(s::IOStream)`, `base/iostream.jl:76`. -/
def m76 (fdStat : α) : α := fdStat

/-- `isopen(s::IOStream)`, `base/iostream.jl:88`. -/
def m88 (stream : NamedIO) : Bool := stream.file.isopen

/-- `close(s::IOStream)`, `base/iostream.jl:90-93`. -/
def m90 (stream : NamedIO) (foreignFailed : Bool) : Except StreamErr NamedIO :=
  if foreignFailed then .error .ioError else .ok { stream with file := ioClose stream.file }

/-- `closewrite(s::IOStream)`, `base/iostream.jl:95`. -/
def m95 (_stream : NamedIO) : Unit := ()

/-- `flush(s::IOStream)`, `base/iostream.jl:97-102`. -/
def m97 (stream : NamedIO) : Except StreamErr NamedIO :=
  match ioFlushModel stream.file with
  | .ok file => .ok { stream with file }
  | .error e => .error e

/-- `iswritable(s::IOStream)`, `base/iostream.jl:104`. -/
def m104 (stream : NamedIO) : Bool := stream.file.writable

/-- `isreadable(s::IOStream)`, `base/iostream.jl:106`. -/
def m106 (stream : NamedIO) : Bool := stream.file.readable

/-- `truncate(s, n)`, `base/iostream.jl:137-141`. -/
def m137 (stream : NamedIO) (n : Nat) (foreignFailed : Bool) : Except StreamErr NamedIO :=
  if foreignFailed then .error .ioError else .ok { stream with file := ioTruncate stream.file n }

/-- `seek(s, n)`, `base/iostream.jl:158-163`. -/
def m158 (stream : NamedIO) (n : Nat) (foreignResult : Int) : Except StreamErr NamedIO :=
  if foreignResult = -1 || foreignResult < -1 then .error .ioError
  else .ok { stream with file := ioSeek stream.file n }

/-- `seekstart(s)`, `base/iostream.jl:185`. -/
def m185 (stream : NamedIO) : NamedIO := { stream with file := ioSeek stream.file 0 }

/-- `seekend(s)`, `base/iostream.jl:192-196`. -/
def m192 (stream : NamedIO) (foreignFailed : Bool) : Except StreamErr NamedIO :=
  if foreignFailed then .error .ioError else .ok { stream with file := ioSeekEnd stream.file }

/-- `skip(s, delta)`, `base/iostream.jl:215-220`. -/
def m215 (stream : NamedIO) (delta : Int) (foreignResult : Int) : Except StreamErr NamedIO :=
  if foreignResult = -1 || foreignResult < -1 then .error .ioError
  else .ok { stream with file := ioSkip stream.file delta }

/-- `position(s)`, `base/iostream.jl:247-251`. -/
def m247 (foreignPosition : Int) : Except StreamErr Int :=
  if foreignPosition = -1 then .error .ioError else .ok foreignPosition

/-- `filesize(s)`, `base/iostream.jl:253-260`. -/
def m253 (foreignSize fallbackSize : Int) : Int :=
  if foreignSize = -1 then fallbackSize else foreignSize

/-- `_eof_nolock(s)`, `base/iostream.jl:262`. -/
def m262 (stream : NamedIO) : Bool := ioEof stream.file

/-- `eof(s; cancel)`, `base/iostream.jl:263-268`. -/
def m263 (stream : NamedIO) (cancelled : Bool) : Except StreamErr Bool :=
  if cancelled then .error .ioError else .ok (m262 stream)

/-- `fdio(name, fd, own)`, `base/iostream.jl:281-286`. -/
def m281 (name : String) (fd : Int) (own : Bool) : NamedIO × Int × Bool :=
  (m32 name, fd, own)

/-- `fdio(fd, own)`, `base/iostream.jl:287`. -/
def m287 (fd : Int) (own : Bool) : NamedIO × Int × Bool :=
  m281 ("<fd " ++ toString fd ++ ">") fd own

/-- Keyword `open`, `base/iostream.jl:316-345`. -/
def m316 (name : String) (locking : Bool) (read write create truncate append : Option Bool)
    (openSucceeded appendSeekSucceeded : Bool) : Except StreamErr (NamedIO × OpenFlagsM) :=
  let flags := resolveFlags read write create truncate append
  let stream := { m32 ("<file " ++ name ++ ">") with
    file := ioCtor flags.read flags.write, locking }
  if !openSucceeded then .error .ioError
  else if flags.append && !appendSeekSucceeded then .error .ioError
  else .ok (stream, flags)

/-- AbstractString keyword `open`, `base/iostream.jl:346`. -/
def m346 (convertedName : String) : String := convertedName

/-- Mode-string `open`, `base/iostream.jl:399-407`. -/
def m399 (mode : String) : Except StreamErr OpenMode :=
  match parseOpenMode mode with
  | some value => .ok value
  | none => .error .argumentError

/-- Byte `write`, `base/iostream.jl:411-414`. -/
def m411 (stream : NamedIO) (byte : UInt8) : Except StreamErr (Nat × IOFileM) :=
  ioWrite stream.file [byte]

/-- `unsafe_write`, `base/iostream.jl:416-426`. -/
def m416 (stream : NamedIO) (memory : List UInt8) (n : Nat) (cancelled : Bool) : Except StreamErr (Nat × IOFileM) :=
  if cancelled then .error .ioError
  else ioWrite stream.file (memory.take n)

/-- `bytesavailable`, `base/iostream.jl:429`. -/
def m429 (stream : NamedIO) : Nat := ioBytesAvailable stream.file

/-- `readavailable`, `base/iostream.jl:431-447`. -/
def m431 (stream : NamedIO) (cancelled : Bool) (reportedRead : Nat) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError
  else
    let result := ioReadAvailable stream.file
    if reportedRead != result.1.length then .error .eofError else .ok result

/-- Byte `read`, `base/iostream.jl:449-455`. -/
def m449 (stream : NamedIO) : Except StreamErr (UInt8 × IOFileM) :=
  match stream.file.data[stream.file.position]? with
  | none => .error .eofError
  | some byte => .ok (byte, { stream.file with position := stream.file.position + 1 })

/-- Fixed-width integer `read`, `base/iostream.jl:458-470`. -/
def m458 (stream : NamedIO) (width : Nat) : Except StreamErr (List UInt8 × IOFileM) :=
  ioReadExact stream.file width

/-- Float16 `read`, `base/iostream.jl:472`. -/
def m472 (stream : NamedIO) : Except StreamErr (List UInt8 × IOFileM) := m458 stream 2

/-- Float32 `read`, `base/iostream.jl:473`. -/
def m473 (stream : NamedIO) : Except StreamErr (List UInt8 × IOFileM) := m458 stream 4

/-- Float64 `read`, `base/iostream.jl:474`. -/
def m474 (stream : NamedIO) : Except StreamErr (List UInt8 × IOFileM) := m458 stream 8

/-- `unsafe_read`, `base/iostream.jl:477-483`. -/
def m477 (stream : NamedIO) (n : Nat) : Except StreamErr (List UInt8 × IOFileM) :=
  ioReadExact stream.file n

/-- `take!`, `base/iostream.jl:487-488`. -/
def m487 (stream : NamedIO) : List UInt8 × IOFileM := ioTake stream.file

/-- Byte `readuntil`, `base/iostream.jl:490-493`. -/
def m490 (stream : NamedIO) (delimiter : UInt8) (keep cancelled : Bool) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError else .ok (ioReadUntil stream.file delimiter keep)

/-- `readuntil_string`, `base/iostream.jl:496-498`. -/
def m496 (stream : NamedIO) (delimiter : UInt8) (keep : Bool) : List UInt8 × IOFileM :=
  ioReadUntil stream.file delimiter keep

/-- Character `readuntil`, `base/iostream.jl:499-503`. -/
def m499 (stream : NamedIO) (delimiter : UInt8) (ascii keep cancelled : Bool) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError
  else if ascii then .ok (m496 stream delimiter keep)
  else .ok (ioReadUntil stream.file delimiter keep)

/-- `readline`, `base/iostream.jl:505-508`. -/
def m505 (stream : NamedIO) (keep cancelled : Bool) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError else .ok (ioReadline stream.file keep)

/-- IOBuffer `copyuntil`, `base/iostream.jl:510-533`. -/
def m510 (output : List UInt8) (stream : NamedIO) (delimiter : UInt8) (keep : Bool) : List UInt8 × IOFileM :=
  let read := ioReadUntil stream.file delimiter keep
  (output ++ read.1, read.2)

/-- IOStream `copyuntil`, `base/iostream.jl:535-540`. -/
def m535 (output input : NamedIO) (delimiter : UInt8) (keep : Bool) : Except StreamErr (NamedIO × NamedIO) :=
  let read := ioReadUntil input.file delimiter keep
  match ioWrite output.file read.1 with
  | .error e => .error e
  | .ok written => .ok ({ output with file := written.2 }, { input with file := read.2 })

/-- `readbytes_all!`, `base/iostream.jl:542-568`. -/
def m542 (stream : NamedIO) (buffer : List UInt8) (n : Nat) : Nat × List UInt8 × IOFileM :=
  let read := ioReadN stream.file n
  (read.1.length, buffer ++ read.1, read.2)

/-- `readbytes_some!`, `base/iostream.jl:570-585`. -/
def m570 (stream : NamedIO) (buffer : List UInt8) (n : Nat) : Nat × List UInt8 × IOFileM :=
  let read := ioReadN stream.file n
  (read.1.length, buffer ++ read.1, read.2)

/-- Public `readbytes!`, `base/iostream.jl:599-603`. -/
def m599 (stream : NamedIO) (buffer : List UInt8) (n : Nat) (all cancelled : Bool) : Except StreamErr (Nat × List UInt8 × IOFileM) :=
  if cancelled then .error .ioError
  else .ok (if all then m542 stream buffer n else m570 stream buffer n)

/-- Whole-stream `read`, `base/iostream.jl:605-634`. -/
def m605 (stream : NamedIO) (fillCount sizeHint : Int) : List UInt8 × IOFileM :=
  if fillCount != -1 then ioReadN stream.file fillCount.toNat
  else
    let remaining := if sizeHint < 0 then ioBytesAvailable stream.file else sizeHint.toNat
    ioReadN stream.file remaining

/-- Counted `read`, `base/iostream.jl:646-654`. -/
def m646 (stream : NamedIO) (n : Nat) (all cancelled : Bool) : Except StreamErr (List UInt8 × IOFileM) :=
  if cancelled then .error .ioError
  else
    let read := if all then m542 stream [] n else m570 stream [] n
    .ok (read.2.1, read.2.2)

/-- Byte `peek`, `base/iostream.jl:658-664`. -/
def m658 (stream : NamedIO) : Except StreamErr UInt8 := ioPeek stream.file

def ReadPrefixContract (result : List UInt8 × IOFileM) (file : IOFileM) (n : Nat) : Prop :=
  let bytes := (file.data.drop file.position).take n
  result.1 = bytes ∧ result.2 = { file with position := file.position + bytes.length }

def ExactReadContract (result : Except StreamErr (List UInt8 × IOFileM))
    (file : IOFileM) (n : Nat) : Prop :=
  let unread := file.data.drop file.position
  (n ≤ unread.length →
    result = .ok (unread.take n, { file with position := file.position + n })) ∧
  (unread.length < n → result = .error .eofError)

def ReadUntilContract (result : List UInt8 × IOFileM) (file : IOFileM)
    (delimiter : UInt8) (keep : Bool) : Prop :=
  let split := splitUntil delimiter (file.data.drop file.position)
  let bytes := if split.found && keep then split.before ++ [delimiter] else split.before
  let consumed := split.before.length + if split.found then 1 else 0
  result.1 = bytes ∧ result.2 = { file with position := file.position + consumed }

def ReadBytesContract (result : Nat × List UInt8 × IOFileM) (file : IOFileM)
    (buffer : List UInt8) (n : Nat) : Prop :=
  let bytes := (file.data.drop file.position).take n
  result.1 = bytes.length ∧ result.2.1 = buffer ++ bytes ∧
  result.2.2 = { file with position := file.position + bytes.length }

def P21 : Prop := ∀ name buffer,
  let stream := m21 name buffer
  stream.name = name ∧ stream.file.data = buffer ∧ stream.file.position = 0 ∧
  stream.file.isopen = true ∧ stream.file.readable = true ∧
  stream.file.writable = true ∧ stream.finalize = false ∧ stream.locking = true

def P24 : Prop := ∀ name finalize,
  let stream := m24 name finalize
  stream.name = name ∧ stream.file.data = [] ∧ stream.file.position = 0 ∧
  stream.file.isopen = true ∧ stream.finalize = finalize ∧ stream.locking = true

def P32 : Prop := ∀ name,
  (m32 name).name = name ∧ (m32 name).finalize = true ∧ (m32 name).file.isopen = true

def P34 : Prop := ∀ pointer, m34 pointer = pointer
def P35 : Prop := ∀ stream, m35 stream = "IOStream(" ++ stream.name ++ ")"
def P37 : Prop := ∀ (α : Type) locking (value : α), m37 locking value = value
def P74 : Prop := ∀ foreignFd, m74 foreignFd = foreignFd
def P76 : Prop := ∀ (α : Type) (fdStat : α), m76 fdStat = fdStat
def P88 : Prop := ∀ stream, m88 stream = stream.file.isopen

def P90 : Prop := ∀ stream failed,
  (failed = true → m90 stream failed = .error .ioError) ∧
  (failed = false →
    m90 stream failed = .ok { stream with file := { stream.file with isopen := false } })

def P95 : Prop := ∀ stream, m95 stream = ()

def P97 : Prop := ∀ stream,
  (stream.file.isopen = true → m97 stream = .ok stream) ∧
  (stream.file.isopen = false → m97 stream = .error .ioError)

def P104 : Prop := ∀ stream, m104 stream = stream.file.writable
def P106 : Prop := ∀ stream, m106 stream = stream.file.readable

def P137 : Prop := ∀ stream n failed,
  (failed = true → m137 stream n failed = .error .ioError) ∧
  (failed = false → ∃ next, m137 stream n failed = .ok next ∧
    next.file.data.length = n ∧ next.file.position = min stream.file.position n ∧
    next.file.isopen = stream.file.isopen ∧ next.name = stream.name)

def P158 : Prop := ∀ stream n foreignResult,
  (foreignResult = -1 ∨ foreignResult < -1 →
    m158 stream n foreignResult = .error .ioError) ∧
  (foreignResult ≠ -1 ∧ ¬ foreignResult < -1 →
    ∃ next, m158 stream n foreignResult = .ok next ∧
    next.file.position = n ∧ next.file.data = stream.file.data)

def P185 : Prop := ∀ stream,
  (m185 stream).file.position = 0 ∧ (m185 stream).file.data = stream.file.data

def P192 : Prop := ∀ stream failed,
  (failed = true → m192 stream failed = .error .ioError) ∧
  (failed = false → ∃ next, m192 stream failed = .ok next ∧
    next.file.position = stream.file.data.length ∧ next.file.data = stream.file.data)

def P215 : Prop := ∀ stream delta foreignResult,
  (foreignResult = -1 ∨ foreignResult < -1 →
    m215 stream delta foreignResult = .error .ioError) ∧
  (foreignResult ≠ -1 ∧ ¬ foreignResult < -1 →
    ∃ next, m215 stream delta foreignResult = .ok next ∧
    next.file.position = (max 0 ((stream.file.position : Int) + delta)).toNat ∧
    next.file.data = stream.file.data)

def P247 : Prop := ∀ position,
  (position = -1 → m247 position = .error .ioError) ∧
  (position ≠ -1 → m247 position = .ok position)

def P253 : Prop := ∀ size fallback,
  (size = -1 → m253 size fallback = fallback) ∧
  (size ≠ -1 → m253 size fallback = size)

def P262 : Prop := ∀ stream,
  m262 stream = decide (stream.file.data.length - stream.file.position = 0)

def P263 : Prop := ∀ stream cancelled,
  (cancelled = true → m263 stream cancelled = .error .ioError) ∧
  (cancelled = false → m263 stream cancelled = .ok (m262 stream))

def P281 : Prop := ∀ name fd own,
  (m281 name fd own).1.name = name ∧ (m281 name fd own).2.1 = fd ∧
  (m281 name fd own).2.2 = own

def P287 : Prop := ∀ fd own,
  (m287 fd own).1.name = "<fd " ++ toString fd ++ ">" ∧
  (m287 fd own).2.1 = fd ∧ (m287 fd own).2.2 = own

def P316 : Prop := ∀ name locking read write create truncate append opened sought,
  let flags := resolveFlags read write create truncate append
  (opened = false →
    m316 name locking read write create truncate append opened sought = .error .ioError) ∧
  (opened = true ∧ flags.append = true ∧ sought = false →
    m316 name locking read write create truncate append opened sought = .error .ioError) ∧
  (opened = true ∧ (flags.append = false ∨ sought = true) →
    ∃ stream, m316 name locking read write create truncate append opened sought = .ok (stream, flags) ∧
      stream.name = "<file " ++ name ++ ">" ∧ stream.locking = locking ∧
      stream.file.readable = flags.read ∧ stream.file.writable = flags.write)

def P346 : Prop := ∀ convertedName, m346 convertedName = convertedName

def P399 : Prop := ∀ mode,
  (∀ parsed, parseOpenMode mode = some parsed → m399 mode = .ok parsed) ∧
  (parseOpenMode mode = none → m399 mode = .error .argumentError)

def P411 : Prop := ∀ stream byte,
  (stream.file.writable = false → m411 stream byte = .error .argumentError) ∧
  (stream.file.writable = true ∧ stream.file.isopen = false →
    m411 stream byte = .ok (0, stream.file)) ∧
  (stream.file.writable = true ∧ stream.file.isopen = true →
    ∃ next, m411 stream byte = .ok (1, next) ∧
      next.position = stream.file.position + 1)

def P416 : Prop := ∀ stream memory n cancelled,
  (cancelled = true → m416 stream memory n cancelled = .error .ioError) ∧
  (cancelled = false ∧ stream.file.writable = false →
    m416 stream memory n cancelled = .error .argumentError) ∧
  (cancelled = false ∧ stream.file.writable = true ∧ stream.file.isopen = false →
    m416 stream memory n cancelled = .ok (0, stream.file)) ∧
  (cancelled = false ∧ stream.file.writable = true ∧ stream.file.isopen = true →
    ∃ next, m416 stream memory n cancelled = .ok ((memory.take n).length, next) ∧
      next.position = stream.file.position + (memory.take n).length)

def P429 : Prop := ∀ stream,
  m429 stream = stream.file.data.length - stream.file.position

def P431 : Prop := ∀ stream cancelled reported,
  let unread := stream.file.data.drop stream.file.position
  (cancelled = true → m431 stream cancelled reported = .error .ioError) ∧
  (cancelled = false ∧ reported ≠ unread.length →
    m431 stream cancelled reported = .error .eofError) ∧
  (cancelled = false ∧ reported = unread.length →
    m431 stream cancelled reported =
      .ok (unread, { stream.file with position := stream.file.position + unread.length }))

def P449 : Prop := ∀ stream,
  (∀ byte, stream.file.data[stream.file.position]? = some byte →
    m449 stream = .ok (byte, { stream.file with position := stream.file.position + 1 })) ∧
  (stream.file.data[stream.file.position]? = none → m449 stream = .error .eofError)

def P458 : Prop := ∀ stream width, ExactReadContract (m458 stream width) stream.file width
def P472 : Prop := ∀ stream, ExactReadContract (m472 stream) stream.file 2
def P473 : Prop := ∀ stream, ExactReadContract (m473 stream) stream.file 4
def P474 : Prop := ∀ stream, ExactReadContract (m474 stream) stream.file 8
def P477 : Prop := ∀ stream n, ExactReadContract (m477 stream n) stream.file n

def P487 : Prop := ∀ stream,
  (m487 stream).1 = stream.file.data ∧ (m487 stream).2.data = [] ∧
  (m487 stream).2.position = 0

def P490 : Prop := ∀ stream delimiter keep cancelled,
  (cancelled = true → m490 stream delimiter keep cancelled = .error .ioError) ∧
  (cancelled = false → ∃ result, m490 stream delimiter keep cancelled = .ok result ∧
    ReadUntilContract result stream.file delimiter keep)

def P496 : Prop := ∀ stream delimiter keep,
  ReadUntilContract (m496 stream delimiter keep) stream.file delimiter keep

def P499 : Prop := ∀ stream delimiter ascii keep cancelled,
  (cancelled = true → m499 stream delimiter ascii keep cancelled = .error .ioError) ∧
  (cancelled = false → ∃ result, m499 stream delimiter ascii keep cancelled = .ok result ∧
    ReadUntilContract result stream.file delimiter keep)

def P505 : Prop := ∀ stream keep cancelled,
  (cancelled = true → m505 stream keep cancelled = .error .ioError) ∧
  (cancelled = false → m505 stream keep cancelled = .ok (ioReadline stream.file keep))

def P510 : Prop := ∀ output stream delimiter keep,
  let read := ioReadUntil stream.file delimiter keep
  (m510 output stream delimiter keep).1 = output ++ read.1 ∧
  (m510 output stream delimiter keep).2 = read.2

def P535 : Prop := ∀ output input delimiter keep,
  let read := ioReadUntil input.file delimiter keep
  (output.file.writable = false →
    m535 output input delimiter keep = .error .argumentError) ∧
  (output.file.writable = true → ∃ nextOutput,
    m535 output input delimiter keep =
      .ok (nextOutput, { input with file := read.2 })) ∧
  (output.file.writable = true ∧ output.file.isopen = true → ∃ nextOutput,
    m535 output input delimiter keep =
      .ok (nextOutput, { input with file := read.2 }) ∧
    nextOutput.file.position = output.file.position + read.1.length)

def P542 : Prop := ∀ stream buffer n,
  ReadBytesContract (m542 stream buffer n) stream.file buffer n

def P570 : Prop := ∀ stream buffer n,
  ReadBytesContract (m570 stream buffer n) stream.file buffer n

def P599 : Prop := ∀ stream buffer n all cancelled,
  (cancelled = true → m599 stream buffer n all cancelled = .error .ioError) ∧
  (cancelled = false ∧ all = true →
    m599 stream buffer n all cancelled = .ok (m542 stream buffer n)) ∧
  (cancelled = false ∧ all = false →
    m599 stream buffer n all cancelled = .ok (m570 stream buffer n))

def P605 : Prop := ∀ stream fillCount sizeHint,
  (fillCount ≠ -1 → ReadPrefixContract (m605 stream fillCount sizeHint) stream.file fillCount.toNat) ∧
  (fillCount = -1 ∧ sizeHint < 0 →
    ReadPrefixContract (m605 stream fillCount sizeHint) stream.file (m429 stream)) ∧
  (fillCount = -1 ∧ 0 ≤ sizeHint →
    ReadPrefixContract (m605 stream fillCount sizeHint) stream.file sizeHint.toNat)

def P646 : Prop := ∀ stream n all cancelled,
  (cancelled = true → m646 stream n all cancelled = .error .ioError) ∧
  (cancelled = false → ∃ result, m646 stream n all cancelled = .ok result ∧
    ReadPrefixContract result stream.file n)

def P658 : Prop := ∀ stream,
  (∀ byte, stream.file.data[stream.file.position]? = some byte → m658 stream = .ok byte) ∧
  (stream.file.data[stream.file.position]? = none → m658 stream = .error .eofError)

theorem readPrefixContract_ioReadN (file : IOFileM) (n : Nat) :
    ReadPrefixContract (ioReadN file n) file n := by
  simp [ReadPrefixContract, ioReadN]

theorem exactReadContract_ioReadExact (file : IOFileM) (n : Nat) :
    ExactReadContract (ioReadExact file n) file n := by
  by_cases h : n ≤ (file.data.drop file.position).length
  · rw [List.length_drop] at h
    simp [ExactReadContract, ioReadExact, ioReadN, h]
  · have h' : file.data.length - file.position < n := by
      rw [← List.length_drop]
      omega
    have hmin : min n (file.data.length - file.position) ≠ n := by omega
    simp [ExactReadContract, ioReadExact, ioReadN, h', hmin]

theorem readUntilContract_ioReadUntil (file : IOFileM) (delimiter : UInt8) (keep : Bool) :
    ReadUntilContract (ioReadUntil file delimiter keep) file delimiter keep := by
  simp [ReadUntilContract, ioReadUntil]

theorem readBytesContract_ioReadN (file : IOFileM) (buffer : List UInt8) (n : Nat) :
    ReadBytesContract
      ((ioReadN file n).1.length, buffer ++ (ioReadN file n).1, (ioReadN file n).2)
      file buffer n := by
  simp [ReadBytesContract, ioReadN]

theorem p21 : P21 := by simp [P21, m21]
theorem p24 : P24 := by simp [P24, m24, m21]
theorem p32 : P32 := by simp [P32, m32, m24, m21]
theorem p34 : P34 := by simp [P34, m34]
theorem p35 : P35 := by simp [P35, m35]
theorem p37 : P37 := by simp [P37, m37]
theorem p74 : P74 := by simp [P74, m74]
theorem p76 : P76 := by simp [P76, m76]
theorem p88 : P88 := by simp [P88, m88]
theorem p90 : P90 := by simp [P90, m90, ioClose]
theorem p95 : P95 := by simp [P95, m95]
theorem p97 : P97 := by
  intro stream
  cases ho : stream.file.isopen <;> simp [P97, m97, ioFlushModel, ho]
theorem p104 : P104 := by simp [P104, m104]
theorem p106 : P106 := by simp [P106, m106]
theorem p137 : P137 := by
  intro stream n failed
  cases failed
  · by_cases h : n ≤ stream.file.data.length
    · simp [P137, m137, ioTruncate, h]
    · simp [P137, m137, ioTruncate, h]
      omega
  · simp [P137, m137]
theorem p158 : P158 := by
  intro stream n result
  by_cases heq : result = -1
  · simp [P158, m158, ioSeek, heq]
  · by_cases hlt : result < -1 <;> simp [P158, m158, ioSeek, heq, hlt]
theorem p185 : P185 := by simp [P185, m185, ioSeek]
theorem p192 : P192 := by simp [P192, m192, ioSeekEnd]
theorem p215 : P215 := by
  intro stream delta result
  by_cases heq : result = -1
  · simp [P215, m215, ioSkip, heq]
  · by_cases hlt : result < -1 <;> simp [P215, m215, ioSkip, heq, hlt]
theorem p247 : P247 := by simp [P247, m247]
theorem p253 : P253 := by
  intro size fallback
  by_cases h : size = -1 <;> simp [P253, m253, h]
theorem p262 : P262 := by intro stream; rfl
theorem p263 : P263 := by simp [P263, m263]
theorem p281 : P281 := by simp [P281, m281, m32, m24, m21]
theorem p287 : P287 := by simp [P287, m287, m281, m32, m24, m21]
theorem p316 : P316 := by
  intro name locking read write create truncate append opened sought
  cases opened <;> cases sought <;>
    cases h : (resolveFlags read write create truncate append).append <;>
      simp [m316, h, ioCtor, m32, m24, m21]
theorem p346 : P346 := by simp [P346, m346]
theorem p399 : P399 := by
  intro mode
  cases h : parseOpenMode mode <;> simp [P399, m399, h]
theorem p411 : P411 := by
  intro stream byte
  cases hw : stream.file.writable <;> cases ho : stream.file.isopen <;>
    simp [P411, m411, ioWrite, hw, ho]
theorem p416 : P416 := by
  intro stream memory n cancelled
  cases hc : cancelled <;> cases hw : stream.file.writable <;> cases ho : stream.file.isopen <;>
    simp [P416, m416, ioWrite, hc, hw, ho]
theorem p429 : P429 := by simp [P429, m429, ioBytesAvailable]
theorem p431 : P431 := by
  intro stream cancelled reported
  cases hc : cancelled
  · have hlen : (stream.file.data.drop stream.file.position).length =
        stream.file.data.length - stream.file.position := List.length_drop
    have htake : List.take (stream.file.data.length - stream.file.position)
        (stream.file.data.drop stream.file.position) =
        stream.file.data.drop stream.file.position := by
      rw [← hlen]
      exact List.take_length
    by_cases hr : reported = (stream.file.data.drop stream.file.position).length
    · simp [P431, m431, ioReadAvailable, ioReadN, hc, hr, hlen, htake]
    · simp [P431, m431, ioReadAvailable, ioReadN, hc, hr, hlen, htake]
  · simp [P431, m431, hc]
theorem p449 : P449 := by
  intro stream
  cases h : stream.file.data[stream.file.position]? <;> simp [P449, m449, h]
theorem p458 : P458 := by exact fun stream width => exactReadContract_ioReadExact stream.file width
theorem p472 : P472 := by exact fun stream => exactReadContract_ioReadExact stream.file 2
theorem p473 : P473 := by exact fun stream => exactReadContract_ioReadExact stream.file 4
theorem p474 : P474 := by exact fun stream => exactReadContract_ioReadExact stream.file 8
theorem p477 : P477 := by exact fun stream n => exactReadContract_ioReadExact stream.file n
theorem p487 : P487 := by simp [P487, m487, ioTake]
theorem p490 : P490 := by
  intro stream delimiter keep cancelled
  cases hc : cancelled <;>
    simp [P490, m490, hc, readUntilContract_ioReadUntil]
theorem p496 : P496 := by exact fun stream delimiter keep =>
  readUntilContract_ioReadUntil stream.file delimiter keep
theorem p499 : P499 := by
  intro stream delimiter ascii keep cancelled
  cases hc : cancelled <;> cases ascii <;>
    simp [P499, m499, m496, hc, readUntilContract_ioReadUntil]
theorem p505 : P505 := by simp [P505, m505]
theorem p510 : P510 := by simp [P510, m510]
theorem p535 : P535 := by
  intro output input delimiter keep
  cases keep <;> cases hw : output.file.writable <;> cases ho : output.file.isopen <;>
    simp [P535, m535, ioWrite, hw, ho]
theorem p542 : P542 := by
  intro stream buffer n
  exact readBytesContract_ioReadN stream.file buffer n
theorem p570 : P570 := by
  intro stream buffer n
  exact readBytesContract_ioReadN stream.file buffer n
theorem p599 : P599 := by
  intro stream buffer n all cancelled
  cases cancelled <;> cases all <;> simp [P599, m599]
theorem p605 : P605 := by
  intro stream fillCount sizeHint
  by_cases hf : fillCount = -1
  · by_cases hs : sizeHint < 0
    · simp [P605, m605, hf, hs, m429, ioBytesAvailable, readPrefixContract_ioReadN]
      omega
    · simp [P605, m605, hf, hs, readPrefixContract_ioReadN]
  · simp [P605, m605, hf, readPrefixContract_ioReadN]
theorem p646 : P646 := by
  intro stream n all cancelled
  cases cancelled <;> cases all <;>
    simp [P646, m646, m542, m570, ReadPrefixContract, ioReadN]
theorem p658 : P658 := by
  intro stream
  cases h : stream.file.data[stream.file.position]? <;> simp [P658, m658, ioPeek, h]

def entries : List Entry := [
  methodEntry "base/iostream.jl" "iostream" 21 21 "IOStream(name::AbstractString, buf::Vector{UInt8})" "The inner constructor stores the supplied buffer, name, initial mark, lock, and locking flag." ``P21 ``p21,
  methodEntry "base/iostream.jl" "iostream" 24 31 "IOStream(name::AbstractString, finalize::Bool)" "The outer constructor allocates the backing buffer and installs finalization exactly when requested." ``P24 ``p24,
  methodEntry "base/iostream.jl" "iostream" 32 32 "IOStream(name::AbstractString)" "The one-argument constructor enables finalization." ``P32 ``p32,
  methodEntry "base/iostream.jl" "iostream" 34 34 "unsafe_convert(T::Type{Ptr{Cvoid}}, s::IOStream)" "Pointer conversion returns the backing byte-vector pointer." ``P34 ``p34,
  methodEntry "base/iostream.jl" "iostream" 35 35 "show(io::IO, s::IOStream)" "Display prints IOStream with its stored name." ``P35 ``p35,
  methodEntry "base/iostream.jl" "iostream" 37 47 "_lock_ios(s, expr)" "The lock macro conditionally brackets evaluation and returns the expression value." ``P37 ``p37,
  methodEntry "base/iostream.jl" "iostream" 74 74 "fd(s::IOStream)" "fd returns the descriptor supplied by ios." ``P74 ``p74,
  methodEntry "base/iostream.jl" "iostream" 76 76 "stat(s::IOStream)" "stat forwards the descriptor to stat." ``P76 ``p76,
  methodEntry "base/iostream.jl" "iostream" 88 88 "isopen(s::IOStream)" "isopen reports the ios open flag." ``P88 ``p88,
  methodEntry "base/iostream.jl" "iostream" 90 93 "close(s::IOStream)" "close locks the stream, closes ios, and raises a system error on failure." ``P90 ``p90,
  methodEntry "base/iostream.jl" "iostream" 95 95 "closewrite(s::IOStream)" "closewrite is the documented no-op for IOStream." ``P95 ``p95,
  methodEntry "base/iostream.jl" "iostream" 97 102 "flush(s::IOStream)" "flush brackets the locked ios flush with signal-atomic state and reports failure." ``P97 ``p97,
  methodEntry "base/iostream.jl" "iostream" 104 104 "iswritable(s::IOStream)" "iswritable returns the ios access-mode bit." ``P104 ``p104,
  methodEntry "base/iostream.jl" "iostream" 106 106 "isreadable(s::IOStream)" "isreadable returns the ios access-mode bit." ``P106 ``p106,
  methodEntry "base/iostream.jl" "iostream" 137 141 "truncate(s::IOStream, n::Integer)" "truncate reports foreign failure and otherwise resizes the stream to the requested length." ``P137 ``p137,
  methodEntry "base/iostream.jl" "iostream" 158 163 "seek(s::IOStream, n::Integer)" "seek distinguishes the foreign failure sentinels and updates position on success." ``P158 ``p158,
  methodEntry "base/iostream.jl" "iostream" 185 185 "seekstart(s::IO)" "seekstart forwards position zero to seek." ``P185 ``p185,
  methodEntry "base/iostream.jl" "iostream" 192 196 "seekend(s::IOStream)" "seekend reports foreign failure and moves to the current data end on success." ``P192 ``p192,
  methodEntry "base/iostream.jl" "iostream" 215 220 "skip(s::IOStream, delta::Integer)" "skip distinguishes the foreign failure sentinels and applies the relative offset on success." ``P215 ``p215,
  methodEntry "base/iostream.jl" "iostream" 247 251 "position(s::IOStream)" "position rejects the foreign failure sentinel and returns every other result." ``P247 ``p247,
  methodEntry "base/iostream.jl" "iostream" 253 260 "filesize(s::IOStream)" "filesize falls back to stat exactly when ios reports minus one." ``P253 ``p253,
  methodEntry "base/iostream.jl" "iostream" 262 262 "_eof_nolock(s::IOStream)" "The unlocked EOF helper returns the blocking ios EOF result." ``P262 ``p262,
  methodEntry "base/iostream.jl" "iostream" 263 268 "eof(s::IOStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "eof checks cancellation at entry, then reads EOF under the stream lock." ``P263 ``p263,
  methodEntry "base/iostream.jl" "iostream" 281 286 "fdio(name::AbstractString, fd::Integer, own::Bool=false)" "fdio constructs a stream and forwards the descriptor and ownership bit to ios." ``P281 ``p281,
  methodEntry "base/iostream.jl" "iostream" 287 287 "fdio(fd::Integer, own::Bool=false)" "Unnamed fdio constructs the documented descriptor name and forwards ownership." ``P287 ``p287,
  methodEntry "base/iostream.jl" "iostream" 316 345 "open(fname::String; lock = true, read :: Union{Bool,Nothing} = nothing, write :: Union{Bool,Nothing} = nothing, create :: Union{Bool,Nothing} = nothing, truncate :: Union{Bool,Nothing} = nothing, append :: Union{Bool,Nothing} = nothing, )" "Keyword open resolves flags, configures locking, reports open failure, and seeks for append mode." ``P316 ``p316,
  methodEntry "base/iostream.jl" "iostream" 346 346 "open(fname::AbstractString; kwargs...)" "AbstractString open converts its filename to String before forwarding keywords." ``P346 ``p346,
  methodEntry "base/iostream.jl" "iostream" 399 407 "open(fname::AbstractString, mode::AbstractString; lock = true)" "Mode open recognizes the six documented modes and rejects every other string." ``P399 ``p399,
  methodEntry "base/iostream.jl" "iostream" 411 414 "write(s::IOStream, b::UInt8)" "Byte write checks access mode and returns the ios byte count." ``P411 ``p411,
  methodEntry "base/iostream.jl" "iostream" 416 426 "unsafe_write(s::IOStream, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)" "unsafe_write performs its cancellation precheck, checks access mode, and writes the requested prefix." ``P416 ``p416,
  methodEntry "base/iostream.jl" "iostream" 429 429 "bytesavailable(s::IOStream)" "bytesavailable returns the locked nonblocking byte count." ``P429 ``p429,
  methodEntry "base/iostream.jl" "iostream" 431 447 "readavailable(s::IOStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "readavailable checks cancellation, fills an empty buffer once, reads the reported count, and rejects a short result." ``P431 ``p431,
  methodEntry "base/iostream.jl" "iostream" 449 455 "read(s::IOStream, ::Type{UInt8})" "Byte read returns and consumes one byte or throws EOF." ``P449 ``p449,
  methodEntry "base/iostream.jl" "iostream" 458 470 "read(s::IOStream, T::Union{Type{Int16},Type{UInt16},Type{Int32},Type{UInt32},Type{Int64},Type{UInt64}})" "Fixed-width integer read buffers exactly the type width and throws EOF when short." ``P458 ``p458,
  methodEntry "base/iostream.jl" "iostream" 472 472 "read(s::IOStream, ::Type{Float16})" "Float16 read reinterprets an exact Int16 read." ``P472 ``p472,
  methodEntry "base/iostream.jl" "iostream" 473 473 "read(s::IOStream, ::Type{Float32})" "Float32 read reinterprets an exact Int32 read." ``P473 ``p473,
  methodEntry "base/iostream.jl" "iostream" 474 474 "read(s::IOStream, ::Type{Float64})" "Float64 read reinterprets an exact Int64 read." ``P474 ``p474,
  methodEntry "base/iostream.jl" "iostream" 477 483 "unsafe_read(s::IOStream, p::Ptr{UInt8}, nb::UInt)" "unsafe_read fills exactly the requested count or throws EOF." ``P477 ``p477,
  methodEntry "base/iostream.jl" "iostream" 487 488 "take!(s::IOStream)" "take returns the ios buffer and clears it." ``P487 ``p487,
  methodEntry "base/iostream.jl" "iostream" 490 493 "readuntil(s::IOStream, delim::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)" "Byte readuntil checks cancellation and consumes through the first delimiter with the requested keep rule." ``P490 ``p490,
  methodEntry "base/iostream.jl" "iostream" 496 498 "readuntil_string(s::IOStream, delim::UInt8, keep::Bool)" "String readuntil applies the byte delimiter and keep rule without a copy." ``P496 ``p496,
  methodEntry "base/iostream.jl" "iostream" 499 503 "readuntil(s::IOStream, delim::AbstractChar; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)" "Character readuntil uses the byte-string path for ASCII and copyuntil otherwise." ``P499 ``p499,
  methodEntry "base/iostream.jl" "iostream" 505 508 "readline(s::IOStream; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)" "readline checks cancellation and applies newline and CRLF removal rules." ``P505 ``p505,
  methodEntry "base/iostream.jl" "iostream" 510 533 "copyuntil(out::IOBuffer, s::IOStream, delim::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)" "IOBuffer copyuntil grows output, copies chunks through the first delimiter, and honors keep." ``P510 ``p510,
  methodEntry "base/iostream.jl" "iostream" 535 540 "copyuntil(out::IOStream, s::IOStream, delim::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)" "IOStream copyuntil locks both streams and copies through the first delimiter." ``P535 ``p535,
  methodEntry "base/iostream.jl" "iostream" 542 568 "readbytes_all!(s::IOStream, b::MutableDenseArrayType{UInt8}, nb::Integer)" "readbytes_all grows as needed, loops until count or EOF, and retains all bytes read." ``P542 ``p542,
  methodEntry "base/iostream.jl" "iostream" 570 585 "readbytes_some!(s::IOStream, b::MutableDenseArrayType{UInt8}, nb::Integer)" "readbytes_some grows once, performs one read, and retains every byte returned." ``P570 ``p570,
  methodEntry "base/iostream.jl" "iostream" 599 603 "readbytes!(s::IOStream, b::MutableDenseArrayType{UInt8}, nb=length(b); all::Bool=true, cancel::CancelTokenArg=DEFAULT_CANCEL)" "Public readbytes checks cancellation and dispatches exactly on the all flag." ``P599 ``p599,
  methodEntry "base/iostream.jl" "iostream" 605 634 "read(s::IOStream)" "Whole-stream read uses the fill count when available and otherwise uses the file-size hint before reading to EOF." ``P605 ``p605,
  methodEntry "base/iostream.jl" "iostream" 646 654 "read(s::IOStream, nb::Integer; all::Bool=true, cancel::CancelTokenArg=DEFAULT_CANCEL)" "Counted read allocates according to all, delegates to readbytes, and shrinks to the returned count." ``P646 ``p646,
  methodEntry "base/iostream.jl" "iostream" 658 664 "peek(s::IOStream, ::Type{UInt8})" "Byte peek returns the next byte without moving position or throws EOF." ``P658 ``p658
]

end JuliaLean.Streams.Methods.IOStream
