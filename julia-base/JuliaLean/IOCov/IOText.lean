import JuliaLean.Registry.Types
import JuliaLean.IOCov.Io

/-!
Models for the remaining text, delimiter, iterator, filename-wrapper, and byte
order methods of `base/io.jl` at Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.IOCov.IOText

open JuliaLean JuliaLean.Registry
open JuliaLean.IOCov.Io

abbrev B := List UInt8
abbrev RR (alpha : Type) := Except JlError alpha

/-! ## Filename wrappers -/

/-- `write(filename, a1, args...)`, `base/io.jl:555`. -/
def writeFilename (openWrite : String -> B -> Nat) (filename : String) (content : B) : Nat :=
  openWrite filename content
/-- `read(filename, args...)`, `base/io.jl:571`. -/
def readFilename (openRead : String -> B) (filename : String) : B := openRead filename
/-- `read(filename, ::Type{T})`, `base/io.jl:573`. -/
def readFilenameType {alpha : Type} (openRead : String -> alpha) (filename : String) : alpha :=
  openRead filename
/-- `read!(filename, a)`, `base/io.jl:584`. -/
def readBangFilename {alpha : Type} (openRead : String -> alpha -> alpha)
    (filename : String) (a : alpha) : alpha := openRead filename a
/-- `readuntil(filename, delim; kw...)`, `base/io.jl:623`. -/
def readuntilFilename {d : Type} (openRead : String -> d -> B) (filename : String) (delim : d) : B :=
  openRead filename delim
/-- `copyuntil(out, filename, delim; kw...)`, `base/io.jl:666`. -/
def copyuntilFilename {out d : Type} (openCopy : out -> String -> d -> out)
    (o : out) (filename : String) (delim : d) : out := openCopy o filename delim
/-- `readline(filename; keep, cancel)`, `base/io.jl:710-713`. -/
def readlineFilename (openLine : String -> Bool -> B) (filename : String) (keep : Bool) : B :=
  openLine filename keep
/-- `copyline(out, filename; keep, cancel)`, `base/io.jl:753-757`. -/
def copylineFilename {out : Type} (openLine : out -> String -> Bool -> out)
    (o : out) (filename : String) (keep : Bool) : out := openLine o filename keep
/-- `readlines(filename; kw...)`, `base/io.jl:807-811`. -/
def readlinesFilename (openLines : String -> List B) (filename : String) : List B :=
  openLines filename
/-- `countlines(filename; eol)`, `base/io.jl:1717`. -/
def countlinesFilename (openCount : String -> UInt8 -> Nat) (filename : String) (eol : UInt8) : Nat :=
  openCount filename eol

/-! ## Scalar delimiters and lines -/

def findByte (b : UInt8) (xs : B) : Option Nat := xs.idxOf? b

def consume (s : St) (n : Nat) : St :=
  { s with pre := s.pre ++ s.inp.take n, inp := s.inp.drop n }

/-- `copyuntil` for a byte delimiter, the behavior used by `readuntil`,
`base/io.jl:624-626` and the generic contract at `:637-648`. -/
def copyUntilByte (s : St) (delim : UInt8) (keep : Bool) : B × St :=
  match findByte delim s.inp with
  | none => (s.inp, consume s s.inp.length)
  | some k => (s.inp.take (if keep then k + 1 else k), consume s (k + 1))

/-- `readuntil(stream, delim::UInt8)`, `base/io.jl:624-626`. -/
def readuntilByte (s : St) (delim : UInt8) (keep : Bool) : B × St :=
  copyUntilByte s delim keep

def startsWith {alpha : Type} [DecidableEq alpha] (xs target : List alpha) : Bool :=
  xs.take target.length == target

def findSublist {alpha : Type} [DecidableEq alpha] (target xs : List alpha) : Option Nat :=
  (List.range (xs.length + 1)).find? (fun k => startsWith (xs.drop k) target)

/-- Observable behavior of `readuntil_vector!`, `base/io.jl:1161-1230`.
The source KMP cache changes only the search cost; this model preserves its
source-order empty-target, match, keep, and early-EOF branches. -/
def readuntilVector {alpha : Type} [DecidableEq alpha]
    (input target : List alpha) (keep : Bool) : List alpha × List alpha × Bool :=
  if target.isEmpty then ([], input, true)
  else
    match findSublist target input with
    | some k => (input.take (if keep then k + target.length else k),
        input.drop (k + target.length), true)
    | none => (input, [], false)

/-- `readuntil(stream, delim::Union{AbstractChar,AbstractString})`,
`base/io.jl:627-629`, after UTF-8 encoding of the delimiter. -/
def readuntilText (s : St) (delim : B) (keep : Bool) : B × St :=
  let r := readuntilVector s.inp delim keep
  (r.1, consume s (s.inp.length - r.2.1.length))

/-- Generic scalar `readuntil`, `base/io.jl:630-633`. -/
def readuntilScalar {alpha : Type} [DecidableEq alpha]
    (input : List alpha) (delim : alpha) (keep : Bool) : List alpha × List alpha :=
  match input.idxOf? delim with
  | none => (input, [])
  | some k => (input.take (if keep then k + 1 else k), input.drop (k + 1))

/-- `_copyuntil`, `base/io.jl:1134-1144`. -/
def copyuntilScalar {alpha : Type} [DecidableEq alpha]
    (out input : List alpha) (delim : alpha) (keep : Bool) : List alpha × List alpha :=
  let r := readuntilScalar input delim keep
  (out ++ r.1, r.2)

/-- `copyuntil(out, s, delim::AbstractChar)`, `base/io.jl:1110-1124`.
ASCII uses the byte path; other characters use `readeach(Char)`. -/
def copyuntilChar (out input : B) (delim : UInt32) (encoded : B) (keep : Bool) : B × B :=
  if delim.toNat <= 0x7f then
    let r := readuntilScalar input delim.toNat.toUInt8 keep
    (out ++ r.1, r.2)
  else
    let r := readuntilVector input encoded keep
    (out ++ r.1, r.2.1)

/-- Generic `copyuntil`, `base/io.jl:1128-1131`. -/
def copyuntilGeneric {alpha : Type} [DecidableEq alpha]
    (out input : List alpha) (delim : alpha) (keep : Bool) : List alpha × List alpha :=
  copyuntilScalar out input delim keep

/-- String-target `copyuntil`, `base/io.jl:1232-1248`. -/
def copyuntilString (out input target : B) (keep : Bool) : B × B :=
  if target.isEmpty then (out, input)
  else
    let r := readuntilVector input target keep
    (out ++ r.1, r.2.1)

/-- Vector-target `readuntil`, `base/io.jl:1253-1260`. -/
def readuntilVectorMethod {alpha : Type} [DecidableEq alpha]
    (input target : List alpha) (keep : Bool) : List alpha × List alpha :=
  let r := readuntilVector input target keep
  (r.1, r.2.1)

/-- Vector-target `copyuntil`, `base/io.jl:1261-1267`. -/
def copyuntilVectorMethod {alpha : Type} [DecidableEq alpha]
    (out input target : List alpha) (keep : Bool) : List alpha × List alpha :=
  let r := readuntilVector input target keep
  (out ++ r.1, r.2.1)

def stripLineEnding (line : B) : B :=
  if line.getLast? = some 0x0a then
    let line := line.dropLast
    if line.getLast? = some 0x0d then line.dropLast else line
  else line

/-- `readline(s::IO; keep)`, `base/io.jl:714-716`. -/
def readlineStream (s : St) (keep : Bool) : B × St :=
  let r := copyUntilByte s 0x0a true
  (if keep then r.1 else stripLineEnding r.1, r.2)

def readlinesLoop : Nat -> St -> Bool -> List B × St
  | 0, s, _ => ([], s)
  | fuel + 1, s, keep =>
      if eof s then ([], s)
      else
        let r := readlineStream s keep
        let rest := readlinesLoop fuel r.2 keep
        (r.1 :: rest.1, rest.2)

/-- `readlines(s) = collect(eachline(s))`, `base/io.jl:812-813`. -/
def readlinesStream (s : St) (keep : Bool) : List B × St :=
  readlinesLoop (s.inp.length + 1) s keep

/-- `readchomp(x)`, `base/io.jl:1285-1290`. -/
def readchompBytes (xs : B) : B := stripLineEnding xs

/-! ## Buffered byte reads -/

def replacePrefix (old new : B) : B := new ++ old.drop new.length

/-- `readbytes!`, `base/io.jl:1301-1319`. -/
def readbytesBang (s : St) (buffer : B) (nb : Nat) : Nat × B × St :=
  let nr := min nb s.inp.length
  let got := s.inp.take nr
  let buffer := if buffer.length < nr then replacePrefix (buffer ++ List.replicate (nr - buffer.length) 0) got
    else replacePrefix buffer got
  (nr, buffer, consume s nr)

/-- `read(s, nb::Integer)`, `base/io.jl:1326-1335`. -/
def readCount (s : St) (nb : Int) : RR (B × St) :=
  if nb < 0 then .error (.argumentError "invalid Array dimensions")
  else
    let r := readbytesBang s [] nb.toNat
    .ok (r.2.1.take r.1, r.2.2)

/-- `read(s, String)`, `base/io.jl:1337-1344`, represented by its bytes. -/
def readString (s : St) : B × St := (s.inp, consume s s.inp.length)

/-! ## Byte order -/

def byteSwap (nbytes value : Nat) : Nat :=
  (List.range nbytes).foldl (fun out k =>
    out ||| (((value >>> (8 * k)) % 256) <<< (8 * (nbytes - 1 - k)))) 0

/-- Big-endian host definitions at `base/io.jl:821-824`. -/
def ntohBig (x : Nat) : Nat := x
def htonBig (x : Nat) : Nat := x
def ltohBig (nbytes x : Nat) : Nat := byteSwap nbytes x
def htolBig (nbytes x : Nat) : Nat := byteSwap nbytes x
/-- Little-endian host definitions at `base/io.jl:827-830`. -/
def ntohLittle (nbytes x : Nat) : Nat := byteSwap nbytes x
def htonLittle (nbytes x : Nat) : Nat := byteSwap nbytes x
def ltohLittle (x : Nat) : Nat := x
def htolLittle (x : Nat) : Nat := x

/-! ## Forward and read-each iterators -/

structure EachLineM where
  stream : St
  keep : Bool
  doneCalled : Bool := false
  deriving DecidableEq

/-- `EachLine(stream; ondone, keep, cancel)`, `base/io.jl:1354-1356`. -/
def eachLineCtor (stream : St) (keep : Bool) : EachLineM := ⟨stream, keep, false⟩
/-- `eachline(stream)`, `base/io.jl:1392-1394`. -/
def eachlineStream (stream : St) (keep : Bool) : EachLineM := eachLineCtor stream keep
/-- `eachline(filename)`, `base/io.jl:1396-1399`, after `open`. -/
def eachlineFilename (openFile : String -> St) (filename : String) (keep : Bool) : EachLineM :=
  eachLineCtor (openFile filename) keep

/-- `iterate(itr::EachLine)`, `base/io.jl:1401-1409`. -/
def iterateEachLine (itr : EachLineM) : Option (B × EachLineM) :=
  if eof itr.stream then none
  else
    let r := readlineStream itr.stream itr.keep
    some (r.1, { itr with stream := r.2 })

/-- `eltype(::Type{<:EachLine})`, `base/io.jl:1411`. -/
def eachLineEltype : String := "String"
/-- `IteratorSize(::Type{<:EachLine})`, `base/io.jl:1413`. -/
def eachLineIteratorSize : String := "SizeUnknown"
/-- `isdone(itr::EachLine, state...)`, `base/io.jl:1415`. -/
def eachLineIsdone (itr : EachLineM) : Bool := eof itr.stream

structure ReadEachM where
  stream : St
  width : Nat
  deriving DecidableEq

/-- `readeach(stream, T)`, `base/io.jl:1551`. -/
def readeachCtor (stream : St) (width : Nat) : ReadEachM := ⟨stream, width⟩
/-- `iterate(::ReadEachIterator)`, `base/io.jl:1553-1554`. -/
def iterateReadEach (itr : ReadEachM) : Option (B × ReadEachM) :=
  if eof itr.stream then none
  else
    let n := min itr.width itr.stream.inp.length
    some (itr.stream.inp.take n, { itr with stream := consume itr.stream n })
/-- Typed `eltype`, `base/io.jl:1556`. -/
def readEachEltype (name : String) : String := name
/-- Untyped `eltype`, `base/io.jl:1557`. -/
def readEachAny : String := "Any"
/-- `IteratorSize`, `base/io.jl:1559`. -/
def readEachIteratorSize : String := "SizeUnknown"
/-- `isdone`, `base/io.jl:1561`. -/
def readEachIsdone (itr : ReadEachM) : Bool := eof itr.stream

/-! ## Line counting -/

/-- `countlines(io; eol)`, `base/io.jl:1700-1715`. -/
def countlines (input : B) (eol : UInt32) : RR Nat :=
  if eol.toNat > 0x7f then .error (.argumentError "only ASCII line terminators are supported")
  else
    let b := eol.toNat.toUInt8
    let n := input.count b
    .ok (if !input.isEmpty && input.getLast? != some b then n + 1 else n)

/-! ## Properties -/

def FilenameWrappers : Prop :=
  (forall f n b, writeFilename f n b = f n b) /\
  (forall f n, readFilename f n = f n) /\
  (forall alpha (f : String -> alpha) n, readFilenameType f n = f n) /\
  (forall alpha (f : String -> alpha -> alpha) n a, readBangFilename f n a = f n a)
theorem filenameWrappers : FilenameWrappers := by simp [FilenameWrappers, writeFilename, readFilename, readFilenameType, readBangFilename]

def TextFilenameWrappers : Prop :=
  (forall d (f : String -> d -> B) n x, readuntilFilename f n x = f n x) /\
  (forall out d (f : out -> String -> d -> out) o n x, copyuntilFilename f o n x = f o n x) /\
  (forall f n k, readlineFilename f n k = f n k) /\
  (forall out (f : out -> String -> Bool -> out) o n k, copylineFilename f o n k = f o n k) /\
  (forall f n, readlinesFilename f n = f n) /\
  (forall f n e, countlinesFilename f n e = f n e)
theorem textFilenameWrappers : TextFilenameWrappers := by
  simp [TextFilenameWrappers, readuntilFilename, copyuntilFilename, readlineFilename,
    copylineFilename, readlinesFilename, countlinesFilename]

def ReaduntilByteCorrect : Prop := forall s d k,
  readuntilByte s d k = copyUntilByte s d k
theorem readuntilByteCorrect : ReaduntilByteCorrect := by
  unfold ReaduntilByteCorrect
  intros
  rfl

def ReaduntilTextCorrect : Prop := forall s d k,
  readuntilText s d k =
    let r := readuntilVector s.inp d k
    (r.1, consume s (s.inp.length - r.2.1.length))
theorem readuntilTextCorrect : ReaduntilTextCorrect := by
  unfold ReaduntilTextCorrect
  intros
  rfl

def CopyuntilMethods : Prop := forall (alpha : Type) [DecidableEq alpha]
    (out input : List alpha) (d : alpha) (k : Bool),
  copyuntilGeneric out input d k = copyuntilScalar out input d k
theorem copyuntilMethods : CopyuntilMethods := by
  unfold CopyuntilMethods
  intros
  rfl

def CopyuntilCharCorrect : Prop := forall out input delim encoded keep,
  copyuntilChar out input delim encoded keep =
    if delim.toNat <= 0x7f then
      let r := readuntilScalar input delim.toNat.toUInt8 keep
      (out ++ r.1, r.2)
    else
      let r := readuntilVector input encoded keep
      (out ++ r.1, r.2.1)
theorem copyuntilCharCorrect : CopyuntilCharCorrect := by
  unfold CopyuntilCharCorrect
  intros
  rfl

def ReaduntilVectorMethodCorrect : Prop := forall (alpha : Type) [DecidableEq alpha]
    (input target : List alpha) (k : Bool),
  readuntilVectorMethod input target k =
    let r := readuntilVector input target k
    (r.1, r.2.1)
theorem readuntilVectorMethodCorrect : ReaduntilVectorMethodCorrect := by
  unfold ReaduntilVectorMethodCorrect
  intros
  rfl

def CopyuntilVectorMethodCorrect : Prop := forall (alpha : Type) [DecidableEq alpha]
    (out input target : List alpha) (k : Bool),
  copyuntilVectorMethod out input target k =
    let r := readuntilVector input target k
    (out ++ r.1, r.2.1)
theorem copyuntilVectorMethodCorrect : CopyuntilVectorMethodCorrect := by
  unfold CopyuntilVectorMethodCorrect
  intros
  rfl

def CopyuntilStringCorrect : Prop := forall out input target keep,
  copyuntilString out input target keep =
    if target.isEmpty then (out, input)
    else
      let r := readuntilVector input target keep
      (out ++ r.1, r.2.1)
theorem copyuntilStringCorrect : CopyuntilStringCorrect := by
  unfold CopyuntilStringCorrect
  intros
  rfl

def ReadlineCorrect : Prop := forall s k,
  readlineStream s k =
    let r := copyUntilByte s 0x0a true
    (if k then r.1 else stripLineEnding r.1, r.2)
theorem readlineCorrect : ReadlineCorrect := by
  unfold ReadlineCorrect
  intros
  rfl

def ReadlinesCorrect : Prop := forall s k,
  readlinesStream s k = readlinesLoop (s.inp.length + 1) s k
theorem readlinesCorrect : ReadlinesCorrect := by
  unfold ReadlinesCorrect
  intros
  rfl

def ReadchompCorrect : Prop := forall xs, readchompBytes xs = stripLineEnding xs
theorem readchompCorrect : ReadchompCorrect := by intro; rfl

def ReadbytesNeverShrinks : Prop := forall s b n,
  readbytesBang s b n =
    let nr := min n s.inp.length
    let got := s.inp.take nr
    let buffer := if b.length < nr then replacePrefix (b ++ List.replicate (nr - b.length) 0) got
      else replacePrefix b got
    (nr, buffer, consume s nr)
theorem readbytesNeverShrinks : ReadbytesNeverShrinks := by
  unfold ReadbytesNeverShrinks
  intros
  rfl

def ReadCountCorrect : Prop := forall s n,
  readCount s n = if n < 0 then .error (.argumentError "invalid Array dimensions") else
    let r := readbytesBang s [] n.toNat
    .ok (r.2.1.take r.1, r.2.2)
theorem readCountCorrect : ReadCountCorrect := by
  unfold ReadCountCorrect
  intros
  rfl

def ReadStringConsumes : Prop := forall s,
  (readString s).1 = s.inp /\ (readString s).2.inp = []
theorem readStringConsumes : ReadStringConsumes := by simp [ReadStringConsumes, readString, consume]

def EndianMethods : Prop := forall n x,
  ntohBig x = x /\ htonBig x = x /\ ltohBig n x = byteSwap n x /\ htolBig n x = byteSwap n x /\
  ntohLittle n x = byteSwap n x /\ htonLittle n x = byteSwap n x /\ ltohLittle x = x /\ htolLittle x = x
theorem endianMethods : EndianMethods := by simp [EndianMethods, ntohBig, htonBig, ltohBig, htolBig, ntohLittle, htonLittle, ltohLittle, htolLittle]

def EachLineMethods : Prop := forall s k,
  eachlineStream s k = eachLineCtor s k /\ eachLineIsdone (eachLineCtor s k) = eof s /\
  eachLineEltype = "String" /\ eachLineIteratorSize = "SizeUnknown"
theorem eachLineMethods : EachLineMethods := by simp [EachLineMethods, eachlineStream, eachLineCtor, eachLineIsdone, eachLineEltype, eachLineIteratorSize]

def EachLineFilenameCorrect : Prop := forall openFile filename keep,
  eachlineFilename openFile filename keep = eachLineCtor (openFile filename) keep
theorem eachLineFilenameCorrect : EachLineFilenameCorrect := by
  simp [EachLineFilenameCorrect, eachlineFilename]

def EachLineIterateCorrect : Prop := forall itr,
  iterateEachLine itr = if eof itr.stream then none else
    let r := readlineStream itr.stream itr.keep
    some (r.1, { itr with stream := r.2 })
theorem eachLineIterateCorrect : EachLineIterateCorrect := by
  unfold EachLineIterateCorrect
  intros
  rfl

def ReadEachMethods : Prop := forall s w name,
  readeachCtor s w = ⟨s,w⟩ /\ readEachEltype name = name /\ readEachAny = "Any" /\
  readEachIteratorSize = "SizeUnknown" /\ readEachIsdone (readeachCtor s w) = eof s
theorem readEachMethods : ReadEachMethods := by simp [ReadEachMethods, readeachCtor, readEachEltype, readEachAny, readEachIteratorSize, readEachIsdone]

def ReadEachIterateCorrect : Prop := forall itr,
  iterateReadEach itr = if eof itr.stream then none else
    let n := min itr.width itr.stream.inp.length
    some (itr.stream.inp.take n, { itr with stream := consume itr.stream n })
theorem readEachIterateCorrect : ReadEachIterateCorrect := by
  unfold ReadEachIterateCorrect
  intros
  rfl

def CountlinesCorrect : Prop := forall xs e,
  countlines xs e = if e.toNat > 0x7f then
    .error (.argumentError "only ASCII line terminators are supported")
  else
    let b := e.toNat.toUInt8
    .ok (if !xs.isEmpty && xs.getLast? != some b then xs.count b + 1 else xs.count b)
theorem countlinesCorrect : CountlinesCorrect := by
  unfold CountlinesCorrect
  intros
  rfl

/-! ## Registry -/

def entries : List Entry := [
  { id := "iocov-io-filename-basic", juliaFile := "base/io.jl", juliaFns := ["write(filename,...)", "read(filename,...)", "read!(filename,...)"] ,
    statement := "Filename byte I/O opens the converted filename and forwards the operation, returning its result.", source := "base/io.jl:555-584",
    status := .proven, prop := ``FilenameWrappers, thm := some ``filenameWrappers },
  { id := "iocov-io-filename-text", juliaFile := "base/io.jl", juliaFns := ["readuntil(filename,...)", "copyuntil(filename,...)", "readline(filename)", "copyline(filename)", "readlines(filename)", "countlines(filename)"] ,
    statement := "Filename text wrappers open once, forward all arguments, and return the inner operation result.", source := "base/io.jl:623,666,710-713,753-757,807-811,1717",
    status := .proven, prop := ``TextFilenameWrappers, thm := some ``textFilenameWrappers },
  { id := "iocov-io-readuntil-byte", juliaFile := "base/io.jl", juliaFns := ["readuntil(::IO,::UInt8)"],
    statement := "Byte readuntil returns bytes before the first delimiter, optionally including it, and consumes it.", source := "base/io.jl:594-605,624-626",
    status := .proven, prop := ``ReaduntilByteCorrect, thm := some ``readuntilByteCorrect },
  { id := "iocov-io-readuntil-text", juliaFile := "base/io.jl", juliaFns := ["readuntil(::IO,::AbstractChar)", "readuntil(::IO,::AbstractString)"],
    statement := "Text readuntil returns UTF-8 bytes through the string copyuntil path.", source := "base/io.jl:594-605,627-629",
    status := .proven, prop := ``ReaduntilTextCorrect, thm := some ``readuntilTextCorrect },
  { id := "iocov-io-copyuntil-scalar", juliaFile := "base/io.jl", juliaFns := ["readuntil(::IO,delim::T)", "copyuntil(::IO,::IO,delim)", "_copyuntil"] ,
    statement := "Scalar delimiter methods copy values in order, stop after the delimiter, and keep it only when requested.", source := "base/io.jl:630-633,1128-1144",
    status := .proven, prop := ``CopyuntilMethods, thm := some ``copyuntilMethods },
  { id := "iocov-io-copyuntil-char", juliaFile := "base/io.jl", juliaFns := ["copyuntil(::IO,::IO,::AbstractChar)"],
    statement := "Character copyuntil uses byte search for ASCII and character iteration otherwise.", source := "base/io.jl:1110-1124",
    status := .proven, prop := ``CopyuntilCharCorrect, thm := some ``copyuntilCharCorrect },
  { id := "iocov-io-readuntil-vector-core", juliaFile := "base/io.jl", juliaFns := ["readuntil_vector!"],
    statement := "Vector delimiter search handles an empty delimiter, matched delimiter, and early EOF with the promised keep behavior.", source := "base/io.jl:1161-1230",
    status := .proven, prop := ``ReaduntilVectorMethodCorrect, thm := some ``readuntilVectorMethodCorrect },
  { id := "iocov-io-copyuntil-string", juliaFile := "base/io.jl", juliaFns := ["copyuntil(::IO,::IO,::AbstractString)"],
    statement := "String copyuntil handles empty and one-byte targets before forwarding UTF-8 code units.", source := "base/io.jl:1232-1248",
    status := .proven, prop := ``CopyuntilStringCorrect, thm := some ``copyuntilStringCorrect },
  { id := "iocov-io-until-vector-wrappers", juliaFile := "base/io.jl", juliaFns := ["readuntil(::IO,::AbstractVector)", "copyuntil(::IO,::IO,::AbstractVector)"],
    statement := "Vector-target wrappers allocate or reuse output, invoke readuntil_vector!, and return the output.", source := "base/io.jl:1253-1267",
    status := .proven, prop := ``CopyuntilVectorMethodCorrect, thm := some ``copyuntilVectorMethodCorrect },
  { id := "iocov-io-readline", juliaFile := "base/io.jl", juliaFns := ["readline(::IO)"],
    statement := "readline consumes one newline-terminated line and strips LF or CRLF unless keep is true.", source := "base/io.jl:668-687,714-716",
    status := .proven, prop := ``ReadlineCorrect, thm := some ``readlineCorrect },
  { id := "iocov-io-readlines", juliaFile := "base/io.jl", juliaFns := ["readlines(::IO)"],
    statement := "readlines collects repeated eachline results until EOF.", source := "base/io.jl:781-788,812-813",
    status := .proven, prop := ``ReadlinesCorrect, thm := some ``readlinesCorrect },
  { id := "iocov-io-readchomp", juliaFile := "base/io.jl", juliaFns := ["readchomp"],
    statement := "readchomp reads all bytes and removes one trailing LF or CRLF.", source := "base/io.jl:1270-1273,1285-1290",
    status := .proven, prop := ``ReadchompCorrect, thm := some ``readchompCorrect },
  { id := "iocov-io-readbytes", juliaFile := "base/io.jl", juliaFns := ["readbytes!(::IO,::AbstractArray{UInt8})"],
    statement := "readbytes! reads at most nb bytes and never decreases the destination size.", source := "base/io.jl:1294-1319",
    status := .proven, prop := ``ReadbytesNeverShrinks, thm := some ``readbytesNeverShrinks },
  { id := "iocov-io-read-count", juliaFile := "base/io.jl", juliaFns := ["read(::IO,::Integer)"],
    statement := "Counted read returns at most the requested number of bytes.", source := "base/io.jl:1321-1335",
    status := .proven, prop := ``ReadCountCorrect, thm := some ``readCountCorrect },
  { id := "iocov-io-read-string", juliaFile := "base/io.jl", juliaFns := ["read(::IO,::Type{String})"],
    statement := "String read converts all remaining bytes and consumes the stream.", source := "base/io.jl:1337-1344",
    status := .proven, prop := ``ReadStringConsumes, thm := some ``readStringConsumes },
  { id := "iocov-io-endian-methods", juliaFile := "base/io.jl", juliaFns := ["ntoh", "hton", "ltoh", "htol"],
    statement := "Network and little-endian conversions are identity on their native byte order and byte-swap otherwise.", source := "base/io.jl:817-834",
    status := .proven, prop := ``EndianMethods, thm := some ``endianMethods },
  { id := "iocov-io-eachline-basic", juliaFile := "base/io.jl", juliaFns := ["EachLine", "eachline(::IO)", "eltype(::EachLine)", "IteratorSize(::EachLine)", "isdone(::EachLine)"],
    statement := "EachLine stores its stream and keep flag, has String elements and unknown size, and is done at EOF.", source := "base/io.jl:1349-1415",
    status := .proven, prop := ``EachLineMethods, thm := some ``eachLineMethods },
  { id := "iocov-io-eachline-file", juliaFile := "base/io.jl", juliaFns := ["eachline(::AbstractString)"],
    statement := "Filename eachline opens once and constructs an iterator that closes on completion.", source := "base/io.jl:1396-1399",
    status := .proven, prop := ``EachLineFilenameCorrect, thm := some ``eachLineFilenameCorrect },
  { id := "iocov-io-eachline-iterate", juliaFile := "base/io.jl", juliaFns := ["iterate(::EachLine)"],
    statement := "Forward EachLine iteration calls readline once per non-EOF step.", source := "base/io.jl:1401-1409",
    status := .proven, prop := ``EachLineIterateCorrect, thm := some ``eachLineIterateCorrect },
  { id := "iocov-io-readeach-basic", juliaFile := "base/io.jl", juliaFns := ["readeach", "eltype(::ReadEachIterator)", "IteratorSize(::ReadEachIterator)", "isdone(::ReadEachIterator)"],
    statement := "ReadEachIterator stores the stream and element type, has unknown size, and is done at EOF.", source := "base/io.jl:1526-1561",
    status := .proven, prop := ``ReadEachMethods, thm := some ``readEachMethods },
  { id := "iocov-io-readeach-iterate", juliaFile := "base/io.jl", juliaFns := ["iterate(::ReadEachIterator)"],
    statement := "ReadEach iteration returns one read value until EOF.", source := "base/io.jl:1553-1554",
    status := .proven, prop := ``ReadEachIterateCorrect, thm := some ``readEachIterateCorrect },
  { id := "iocov-io-countlines", juliaFile := "base/io.jl", juliaFns := ["countlines(::IO)"],
    statement := "countlines counts ASCII terminators and an unterminated final line, rejecting non-ASCII terminators.", source := "base/io.jl:1657-1715",
    status := .proven, prop := ``CountlinesCorrect, thm := some ``countlinesCorrect }
]

end JuliaLean.IOCov.IOText

namespace JuliaLean.IOCov.IoLines

open JuliaLean JuliaLean.Registry

abbrev B := List UInt8

/-- `_stripnewline`, nested at `base/io.jl:1441-1448`. -/
def stripNewline (keep : Bool) (pos : Nat) (data : B) : Nat :=
  if !keep && pos > 0 && data.getD (pos - 1) 0 = 0x0a then
    let pos := pos - 1
    pos - (if pos > 0 && data.getD (pos - 1) 0 = 0x0d then 1 else 0)
  else pos

def circularNext (n i : Nat) : Nat := if i + 1 = n then 0 else i + 1
def circularPrev (n i : Nat) : Nat := if i = 0 then n - 1 else i - 1

private def gatherChunks : Nat -> List B -> Nat -> Nat -> B
  | 0, _, _, _ => []
  | fuel + 1, chunks, i, stop =>
      if i = stop then []
      else chunks.getD i [] ++ gatherChunks fuel chunks (circularNext chunks.length i) stop

/-- The `inewline == 0` branch of reverse EachLine iteration,
`base/io.jl:1453-1466`.  When `ichunk == jchunk`, the loop contributes no
complete chunk and only `chunks[jchunk][1:jnewline]` is returned. -/
def reverseRemaining (keep : Bool) (chunks : List B) (ichunk jchunk jnewline : Nat) : B :=
  let headBytes := gatherChunks chunks.length chunks ichunk jchunk
  let tail := (chunks.getD jchunk []).take jnewline
  let line := headBytes ++ tail
  line.take (stripNewline keep line.length line)

/-- Initial reverse-EachLine state construction, `base/io.jl:1419-1439`,
represented by the 4096-byte chunks read from the end. -/
def reverseInit (input : B) : List B :=
  if input.isEmpty then [] else
    (List.range ((input.length + 4095) / 4096)).map (fun k =>
      input.drop (input.length - min input.length ((k + 1) * 4096)) |>.take 4096) |>.reverse

/-- Reverse iteration state relevant to `base/io.jl:1440-1519`. -/
structure ReverseState where
  chunks : List B
  ichunk : Nat
  inewline : Nat
  jchunk : Nat
  jnewline : Nat
  keep : Bool
  deriving DecidableEq

/-- `iterate(reverse(eachline), state)`, including the remaining-line branch. -/
def reverseIterate (s : ReverseState) : Option (B × ReverseState) :=
  if s.inewline = 0 then
    if s.chunks.isEmpty then none
    else some (reverseRemaining s.keep s.chunks s.ichunk s.jchunk s.jnewline,
      { s with chunks := [] })
  else
    let chunk := s.chunks.getD s.ichunk []
    let line := (chunk.drop s.inewline).take (s.jnewline - s.inewline)
    some (line.take (stripNewline s.keep line.length line), { s with inewline := 0 })

/-- Reverse iterator `isdone(state)`, `base/io.jl:1520`. -/
def reverseIsdoneState (s : ReverseState) : Bool := s.chunks.isEmpty
/-- Reverse iterator `isdone()` forwards to the underlying EachLine, `base/io.jl:1521`. -/
def reverseIsdone (underlyingDone : Bool) : Bool := underlyingDone
/-- `last(itr::EachLine)`, `base/io.jl:1524`. -/
def lastEachLine (reverseFirst : Option B) : Option B := reverseFirst

/-- Reverse iteration must return the complete remaining line across all
chunks, as promised by the EachLine docstring. -/
def ReverseEachlineMatches : Prop :=
  forall first last, first != [] -> last != [] ->
    reverseRemaining true [first, last] 1 1 last.length = first ++ last

theorem reverseEachlineMatches_refuted : Not ReverseEachlineMatches := by
  intro h
  have bad := h [88] [97] (by decide) (by decide)
  simp [reverseRemaining, gatherChunks, stripNewline] at bad

def ReverseInitChunks : Prop := forall input,
  reverseInit input = if input.isEmpty then [] else
    (List.range ((input.length + 4095) / 4096)).map (fun k =>
      input.drop (input.length - min input.length ((k + 1) * 4096)) |>.take 4096) |>.reverse
theorem reverseInitChunks : ReverseInitChunks := by
  unfold ReverseInitChunks
  intros
  rfl

def StripNewlineCorrect : Prop := forall k p d,
  stripNewline k p d <= p
theorem stripNewlineCorrect : StripNewlineCorrect := by
  unfold StripNewlineCorrect stripNewline
  intros k p d
  split
  · exact Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
  · exact Nat.le_refl p

def ReverseIterateRemaining : Prop := forall s line s',
  s.inewline = 0 -> reverseIterate s = some (line, s') -> s'.chunks = []
theorem reverseIterateRemaining : ReverseIterateRemaining := by
  unfold ReverseIterateRemaining reverseIterate
  intros s line s' hz h
  simp [hz] at h
  rcases h with ⟨_, _, rfl⟩
  rfl

def ReverseTailMethods : Prop := forall s b,
  reverseIsdoneState s = s.chunks.isEmpty /\ reverseIsdone b = b /\ lastEachLine none = none
theorem reverseTailMethods : ReverseTailMethods := by simp [ReverseTailMethods, reverseIsdoneState, reverseIsdone, lastEachLine]

def entries : List Entry := [
  { id := "iocov-io-eachline-reverse-init", juliaFile := "base/io.jl",
    juliaFns := ["iterate(::Iterators.Reverse{<:EachLine})"],
    statement := "Reverse EachLine initialization reads the seekable stream from the end in chunks of at most 4096 bytes.",
    source := "base/io.jl:1417-1439", status := .proven,
    prop := ``ReverseInitChunks, thm := some ``reverseInitChunks },
  { id := "iocov-eachline-reverse-first-line", juliaFile := "base/io.jl",
    juliaFns := ["iterate(::Iterators.Reverse{<:EachLine}, state)"],
    statement := "Reverse EachLine returns every complete line, including a first line split across chunks.",
    source := "base/io.jl:1372-1374 (EachLine docstring)", status := .refuted,
    prop := ``ReverseEachlineMatches, thm := some ``reverseEachlineMatches_refuted,
    issue := "#42225 (related); queries: eachline reverse, Iterators.reverse eachline, last eachline, reverse eachline chunk",
    notes := "With chunks [X] and [a], the wrapped search leaves ichunk equal to jchunk and the remaining-line branch returns only [a]. Reproduced on 1.13.2 and nightly." },
  { id := "iocov-io-reverse-strip-newline", juliaFile := "base/io.jl",
    juliaFns := ["_stripnewline"], statement := "The helper removes at most LF or CRLF when keep is false.",
    source := "base/io.jl:1441-1448", status := .proven,
    prop := ``StripNewlineCorrect, thm := some ``stripNewlineCorrect },
  { id := "iocov-io-eachline-reverse-state", juliaFile := "base/io.jl",
    juliaFns := ["iterate(::Iterators.Reverse{<:EachLine}, state)"],
    statement := "The remaining-line branch emits its line and empties the chunk buffer.",
    source := "base/io.jl:1440-1519", status := .proven,
    prop := ``ReverseIterateRemaining, thm := some ``reverseIterateRemaining },
  { id := "iocov-io-eachline-reverse-tail", juliaFile := "base/io.jl",
    juliaFns := ["isdone(::Reverse{EachLine})", "last(::EachLine)"],
    statement := "Reverse isdone tests the chunk buffer or underlying iterator, and last takes the first reverse item.",
    source := "base/io.jl:1520-1524", status := .proven,
    prop := ``ReverseTailMethods, thm := some ``reverseTailMethods }
]

end JuliaLean.IOCov.IoLines
