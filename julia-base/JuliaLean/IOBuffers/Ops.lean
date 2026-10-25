import JuliaLean.IOBuffers.Model

/-!
Constructors and operations of the IOBuffer model as data, with an interpreter that
records the observable result of each step (used for the differential tests and for
properties over operation sequences).
-/

namespace JuliaLean.IOBuffers

open JuliaLean

/-- A constructor call. -/
inductive Ctor where
  /-- `IOBuffer(; read, write, append, truncate, maxsize, sizehint)`. -/
  | empty (read write append truncate : Option Bool) (maxsize : Int) (sizehint : Option Int)
  /-- `IOBuffer(data; read, write, append, truncate, maxsize)`. -/
  | data (d : DataArg) (read write append truncate : Option Bool) (maxsize : Int)
  /-- `IOBuffer(s::String)`. -/
  | str (s : List UInt8)
  /-- `PipeBuffer(data; maxsize)`. -/
  | pipe (d : DataArg) (maxsize : Int)
  /-- `PipeBuffer(maxsize)`. -/
  | pipeN (maxsize : Int)

def Ctor.build : Ctor → Except IOErr IOBuf
  | .empty r w a t m s => iobufferEmpty r w a t m s
  | .data d r w a t m => iobufferData d r w a t m
  | .str s => iobufferString s
  | .pipe d m => pipeBuffer d .i64 m
  | .pipeN m => pipeBufferN .i64 m

/-- An operation on the buffer `io`. -/
inductive Op where
  | writeByte (b : UInt8)
  | writeBytes (bs : List UInt8)
  | readByte
  | peekByte
  | readN (n : Int)
  | readAll
  | readBang (n : Nat)
  | readbytes (nb : Int)
  | peekT (nb : Nat)
  | readT (nb : Nat)
  | peekGeneric
  | skip (n : Int)
  | seek (n : Int)
  | seekstart
  | seekend
  | mark
  | unmark
  | reset
  | truncate (n : Int)
  | take
  | takestring
  | readuntil (d : UInt8) (keep : Bool)
  | readline (keep : Bool)
  | occursin (d : UInt8)
  | copyline (line : List UInt8) (keep : Bool)
  | closewrite
  | close

/-- The value an operation returns. -/
inductive Val where
  | int (x : Int)
  | bytes (bs : List UInt8)
  | bool (b : Bool)
  | count (n : Int) (bs : List UInt8)
  | unit
  deriving DecidableEq

/-- Run one operation. `Int` arguments of other operations are `Int` in Julia; values
outside its range are clamped by the generator. -/
def runOp : Op → M Val
  | .writeByte b => do return .int (← writeByte b).val
  | .writeBytes bs => do return .int (← unsafeWrite bs).val
  | .readByte => do return .bytes [← readByte]
  | .peekByte => do return .bytes [← peekByte]
  | .readN n => do return .bytes (← readN (i n))
  | .readAll => do return .bytes (← readAll)
  | .readBang n => do return .bytes (← readBang n)
  | .readbytes nb => do let (k, bs) ← readbytes (i nb); return .count k.val bs
  | .peekT nb => do return .bytes (← peekT nb)
  | .readT nb => do return .bytes (← readT nb)
  | .peekGeneric => do return .bytes [← peekGeneric]
  | .skip n => do skip n; return .unit
  | .seek n => do seekAny n; return .unit
  | .seekstart => do seekstart; return .unit
  | .seekend => do seekend; return .unit
  | .mark => do return .int (← mark).val
  | .unmark => do return .bool (← unmark)
  | .reset => do return .int (← reset).val
  | .truncate n => do truncate (i n); return .unit
  | .take => do return .bytes (← take)
  | .takestring => do return .bytes (← takestring)
  | .readuntil d k => do return .bytes (← readuntil d k)
  | .readline k => do return .bytes (← readline k)
  | .occursin d => do return .bool (← lift (occursin d (← get)))
  | .copyline l k => do copylineFrom l k; return .unit
  | .closewrite => do closewrite; return .unit
  | .close => do close; return .unit

/-- Run a list of operations, continuing after exceptions as a `try`/`catch` would. -/
def runOps : List Op → IOBuf → List (Except IOErr Val × IOBuf)
  | [], _ => []
  | o :: os, io =>
    match (runOp o).run io with
    | .ok v io' => (.ok v, io') :: runOps os io'
    | .error e io' => (.error e, io') :: runOps os io'

/-- The final state after running `os`. -/
def finalState : List Op → IOBuf → IOBuf
  | [], io => io
  | o :: os, io =>
    match (runOp o).run io with
    | .ok _ io' => finalState os io'
    | .error _ io' => finalState os io'

def hexByte (b : UInt8) : String :=
  let h := "0123456789abcdef".toList
  String.ofList [h.getD (b.toNat / 16) '0', h.getD (b.toNat % 16) '0']

def hexBytes (bs : List UInt8) : String := String.join (bs.map hexByte)

def Val.show : Val → String
  | .int x => s!"I:{x}"
  | .bytes bs => s!"B:{hexBytes bs}"
  | .bool b => if b then "T" else "F"
  | .count n bs => s!"C:{n}:{hexBytes bs}"
  | .unit => "U"

def showStep : Except IOErr Val × IOBuf → String
  | (r, io) =>
    let rs := match r with | .ok v => v.show | .error e => s!"E:{e.name}"
    s!"{rs}|pos={(position io).val}|avail={(bytesavailable io).val}|eof={if eof io then 1 else 0}|marked={if ismarked io then 1 else 0}"

/-- The trace printed by the differential tests. -/
def trace (c : Ctor) (os : List Op) : List String :=
  match c.build with
  | .error e => [s!"CTOR E:{e.name}"]
  | .ok io => "CTOR ok" :: (runOps os io).map showStep

end JuliaLean.IOBuffers
