import JuliaLean.StringsCovB.Ann
import JuliaLean.IOBuffers.Model

/-!
# `base/strings/annotated_io.jl`: `AnnotatedIOBuffer`

Models of the `AnnotatedIOBuffer` methods of `base/strings/annotated_io.jl`
(master `bbfa0ce4150`). The wrapped `IOBuffer` is the `IOBuffers` area's
`GenericIOBuffer` model (`IOBuf`, `EStateM` methods); an `AnnotatedIOBuffer`
is that buffer and its vector of `RegionAnnotation`s (`Ann.RA`).

* A method that mutates the buffer returns its result together with the new
  state (`AM`); a mutation made before an exception persists.
* `write(dest, src)` of two buffers takes both states; the buffers are distinct
  objects (`to === from` throws earlier, `base/iobuffer.jl:889-890`).
* A non-`AnnotatedIOBuffer` `IO` is a byte sink: the list of bytes written.
-/

namespace JuliaLean.StringsCovB.AIO

open JuliaLean JuliaLean.Strings JuliaLean.StringsCovB.Ann
open JuliaLean.IOBuffers (IOBuf IOErr)

/-- `AnnotatedIOBuffer`, `base/strings/annotated_io.jl:5-8`. -/
structure AIO where
  io : IOBuf
  anns : List RA

/-- Exceptions: those of the `IOBuffer` methods and those of the String model
(`OutOfMemoryError`, `StringIndexError`, ...). -/
inductive AErr where
  | io (e : IOErr)
  | str (e : SErr)
  deriving DecidableEq, Repr

abbrev AM := EStateM AErr AIO

/-- Run an `IOBuffer` method on `io.io`. -/
def onIO {α : Type} (m : IOBuffers.M α) : AM α := fun a =>
  match m.run a.io with
  | .ok x io' => .ok x { a with io := io' }
  | .error e io' => .error (.io e) { a with io := io' }

def setAnns (l : List RA) : AM Unit := modify fun a => { a with anns := l }

instance : Inhabited RA := ⟨⟨ix 0, ix 0, 0, none⟩⟩

/-! ## Construction and forwarding, `base/strings/annotated_io.jl:10-33` -/

/-- `AnnotatedIOBuffer(io::IOBuffer) = AnnotatedIOBuffer(io, Vector{RegionAnnotation}())`, `:10`. -/
def ofIO (io : IOBuf) : AIO := ⟨io, []⟩

/-- `AnnotatedIOBuffer() = AnnotatedIOBuffer(IOBuffer())`, `:11`. -/
def empty : Except IOErr AIO := do
  let io ← IOBuffers.iobuffer
  pure (ofIO io)

/-- `show(io::IO, aio::AnnotatedIOBuffer)`, `:13-18`: the shown type, then
`(<size> byte[s], <n> annotation[s])` with `size = filesize(aio.io)`. -/
def showAIO (typeName : String) (aio : AIO) : String :=
  let size := (IOBuffers.filesize aio.io).val
  let n := aio.anns.length
  typeName ++ "(" ++ toString size ++ " byte" ++ (if size = 1 then "" else "s") ++ ", " ++
    toString n ++ " annotation" ++ (if n = 1 then "" else "s") ++ ")"

/-- `pipe_reader(io::AnnotatedIOBuffer) = io.io`, `:20`. -/
def pipeReader (a : AIO) : IOBuf := a.io
/-- `pipe_writer(io::AnnotatedIOBuffer) = io.io`, `:21`. -/
def pipeWriter (a : AIO) : IOBuf := a.io

/-- `position(io::AnnotatedIOBuffer) = position(io.io)`, `:24`. -/
def position (a : AIO) : JInt64 := IOBuffers.position a.io
/-- `seek(io::AnnotatedIOBuffer, n::Integer) = (seek(io.io, n); io)`, `:25`. -/
def seek (n : Int) : AM Unit := onIO (IOBuffers.seekAny n)
/-- `seekend(io::AnnotatedIOBuffer) = (seekend(io.io); io)`, `:26`. -/
def seekend : AM Unit := onIO IOBuffers.seekend
/-- `skip(io::AnnotatedIOBuffer, n::Integer) = (skip(io.io, n); io)`, `:27`. -/
def skip (n : Int) : AM Unit := onIO (IOBuffers.skip n)
/-- `copy(io::AnnotatedIOBuffer) = AnnotatedIOBuffer(copy(io.io), copy(io.annotations))`, `:28`;
`copy(::IOBuffer)` is a parameter. -/
def copyAIO (copyBuf : IOBuf → IOBuf) (a : AIO) : AIO := ⟨copyBuf a.io, a.anns⟩

/-- `annotations(io::AnnotatedIOBuffer) = io.annotations`, `:30`. -/
def annotationsIO (a : AIO) : List RA := a.anns

/-- `annotate!(io::AnnotatedIOBuffer, range, label, val)`, `:32-33`. -/
def annotateIO (range : Region) (label : Nat) (val : Val) : AM Unit := do
  let a ← get
  setAnns (annotateBang a.anns range label val)

/-- `eof(io::AnnotatedIOBuffer)`: `eof(pipe_reader(io))` (`base/io.jl:536`). -/
def eofA (a : AIO) : Bool := IOBuffers.eof a.io

/-! ## `_clear_annotations_in_region!` and `_insert_annotations!` -/

/-- The per-annotation step of the `for i in eachindex(annotations)` loop of
`_clear_annotations_in_region!`, `base/strings/annotated_io.jl:122-140`: the
truncated annotation, followed by the extra tail when `span` lies strictly inside
the region. The extras are inserted right after their annotation (`insert!` at
`i + offset`, `:142-145`). -/
def clearOne (span : Region) (annot : RA) : List RA :=
  let region := annot.region
  if (region.1.val ≤ span.1.val ∧ span.1.val ≤ region.2.val) ∨
      (region.1.val ≤ span.2.val ∧ span.2.val ≤ region.2.val) then
    let a' := annot.setR (if region.1.val < span.1.val then urange region.1 (span.1 - ix 1)
      else urange (span.2 + ix 1) region.2)
    if region.1.val < span.1.val ∧ span.2.val < region.2.val then
      [a', annot.setR (urange (span.2 + ix 1) region.2)]
    else [a']
  else [annot]

/-- `_clear_annotations_in_region!(annotations, span)`,
`base/strings/annotated_io.jl:120-149`: first drop the annotations entirely
inside `span` (`filter!`, `:122`), then truncate or split the overlapping ones. -/
def clearRegion (annotations : List RA) (span : Region) : List RA :=
  (annotations.filter fun ann => decide (ann.lo.val < span.1.val) || decide (ann.hi.val > span.2.val)).flatMap
    (clearOne span)

/-- The `all(1:i) do runlen ... end` test of `_insert_annotations!`,
`base/strings/annotated_io.jl:178-184` (`newannots[begin+runlen-1]`,
`annots[end-i+runlen]`). -/
def runOk (annots newannots : List RA) (offset : JInt64) (i : Nat) : Bool :=
  (List.range i).all fun k =>
    let new := newannots.getD k default
    let old := annots.getD (annots.length - i + k) default
    !(old.hi != offset || new.lo != ix 1 || old.label != new.label || old.value != new.value)

/-- The candidate run length `i` of the `for i in reverse(axes(newannots, 1))`
loop, `base/strings/annotated_io.jl:172-186`. -/
def runCand (annots newannots : List RA) (offset : JInt64) (l : RA) (i : Nat) : Bool :=
  let annot := newannots.getD (i - 1) default
  annot.lo == ix 1 && decide (i ≤ annots.length) && annot.label == l.label &&
    annot.value == l.value && runOk annots newannots offset i

/-- The labelled block `run = @label search begin ... end`,
`base/strings/annotated_io.jl:169-189`: the largest `i` passing every test, or 0. -/
def findRun (annots newannots : List RA) (offset : JInt64) : Nat :=
  match annots.getLast? with
  | none => 0
  | some l =>
    if l.hi == offset then
      (((List.range newannots.length).reverse.map (· + 1)).find? (runCand annots newannots offset l)).getD 0
    else 0

/-- `_insert_annotations!(annots, newannots, offset)`,
`base/strings/annotated_io.jl:168-229`: extend the last `run` annotations by the
first `run` new ones, then push the remaining new ones shifted by `offset`. -/
def insertAnns (annots newannots : List RA) (offset : JInt64) : List RA :=
  let run := findRun annots newannots offset
  let merged := (List.range run).foldl (fun acc k =>
    let oldIndex := annots.length - run + k
    let old := acc.getD oldIndex default
    let new := newannots.getD k default
    acc.set oldIndex ⟨old.lo, (urange old.lo (new.hi + offset)).2, old.label, old.value⟩) annots
  merged ++ (newannots.drop run).map fun annot =>
    let r := urange (annot.lo + offset) (annot.hi + offset)
    ⟨r.1, r.2, annot.label, annot.value⟩

/-- `_insert_annotations!(io::AnnotatedIOBuffer, newannots, offset = position(io))`,
`base/strings/annotated_io.jl:231-232`. -/
def insertIO (newannots : List RA) (offset : JInt64) : AM Unit := do
  let a ← get
  setAnns (insertAnns a.anns newannots offset)

/-! ## Writing -/

/-- The argument of `write(io::AnnotatedIOBuffer, astr::Union{AnnotatedString,
SubString{<:AnnotatedString}})`. -/
inductive WArg where
  | str (a : AS)
  | sub (s : ASub)

def liftS {α : Type} (x : SJl α) : AM α :=
  match x with
  | .ok a => pure a
  | .error e => throw (.str e)

/-- `astr = AnnotatedString(astr)`: a copy of an `AnnotatedString`
(`base/strings/annotated.jl:134`) or the conversion of a SubString (`:312`). -/
def toAS : WArg → SJl AS
  | .str a => .ok (ofS (.ann a))
  | .sub s => ofSub s

/-- `write(io::AnnotatedIOBuffer, astr)`, `base/strings/annotated_io.jl:35-41`,
after the conversion: clear `offset+1:offset+ncodeunits(astr)` unless at the
end, insert the annotations at `position(io)`, write the code units
(`write(io.io, String(astr))` is `unsafe_write`). -/
def writeAS (astr : AS) : AM JInt64 := do
  let a ← get
  let offset := position a
  if !eofA a then setAnns (clearRegion a.anns (urange (offset + ix 1) (offset + ncodeunits astr.str)))
  let a ← get
  setAnns (insertAnns a.anns astr.anns (position a))
  onIO (IOBuffers.unsafeWrite astr.str.bytes)

/-- `write(io::AnnotatedIOBuffer, astr::Union{AnnotatedString, SubString{<:AnnotatedString}})`,
`base/strings/annotated_io.jl:35-41`. -/
def writeW (x : WArg) : AM JInt64 := do
  let astr ← liftS (toAS x)
  writeAS astr

/-- `write(io::AnnotatedIOBuffer, c::AnnotatedChar) = write(io, AnnotatedString(string(c),
[(region=1:ncodeunits(c), a...) for a in c.annotations]))`, `:43-44`; `string(c)`
prints the character (`base/strings/annotated_io.jl:356-357,387-388`). -/
def writeC (c : AC) : AM JInt64 := do
  let str ← liftS (stringOfChars [c.char])
  writeAS (ctorVector (.plain str) (c.anns.map fun a => (urange (ix 1) (ix (ncodeunitsC c)), a.label, a.value)))

/-- `write(io::AnnotatedIOBuffer, x::AbstractString) = write(io.io, x)::Int` (`:45`),
`write(io, s::Union{SubString{String}, String})` (`:46`) and
`write(io, s::StringViewAndSub)` (`:47`): the code units go to `io.io`; the
annotations are untouched. -/
def writePlain (bs : List UInt8) : AM JInt64 := onIO (IOBuffers.unsafeWrite bs)

/-- `write(io::AnnotatedIOBuffer, b::UInt8) = write(io.io, b)`, `:48`. -/
def writeByte (b : UInt8) : AM JInt64 := onIO (IOBuffers.writeByte b)

/-- `write(to::IO, from::GenericIOBuffer)`, `base/iobuffer.jl:886-897`, with
`to = dest.io`: the readable bytes `from.data[from.ptr:from.size]` are written and
`from.ptr` becomes `from.size + 1`. -/
def writeBuf (src : IOBuf) : IOBuffers.M JInt64 := do
  if !src.readable then IOBuffers.throwArg "read failed, IOBuffer is not readable"
  IOBuffers.unsafeWrite (IOBuffers.slice src.data src.ptr.val src.size.val)

/-- `write(dest::AnnotatedIOBuffer, src::AnnotatedIOBuffer)`,
`base/strings/annotated_io.jl:50-60`: the number of bytes written and both new states. -/
def writeAIO (dest src : AIO) : Except AErr (JInt64 × AIO × AIO) :=
  let destpos := position dest
  let isappending := eofA dest
  let srcpos := position src
  match (writeBuf src.io).run dest.io with
  | .error e _ => .error (.io e)
  | .ok nb dio =>
    let src' : AIO := { src with io := { src.io with ptr := src.io.size + IOBuffers.i 1 } }
    let anns := if isappending then dest.anns else clearRegion dest.anns (urange destpos (destpos + nb))
    let srcannots := (src.anns.filter fun annot => decide (annot.lo.val ≥ srcpos.val)).map fun annot =>
      annot.setR (urange (imax (ix 1 + srcpos) annot.lo) annot.hi)
    .ok (nb, ⟨dio, insertAnns anns srcannots (destpos - srcpos)⟩, src')

/-- An `AbstractPipe` such as an `IOContext` whose `pipe_writer` is an
`AnnotatedIOBuffer`, or another `IO` (a byte sink). -/
inductive Pipe where
  | aio (a : AIO)
  | other (out : List UInt8)

/-- `write(io::AbstractPipe, s::Union{AnnotatedString, SubString{<:AnnotatedString}})`,
`base/strings/annotated_io.jl:64-70`: to the `AnnotatedIOBuffer` writer, or the
generic `write(::IO, s)`, which without StyledStrings writes the unannotated
code units (`base/strings/annotated_io.jl:356-363`). -/
def writePipe (p : Pipe) (x : WArg) : Except AErr (JInt64 × Pipe) :=
  match p with
  | .aio a =>
    match (writeW x).run a with
    | .ok n a' => .ok (n, .aio a')
    | .error e _ => .error e
  | .other out =>
    let bs := match x with
      | .str s => s.str.bytes
      | .sub s => subBytes s
    .ok (ix bs.length, .other (out ++ bs))

/-- `write(io::AbstractPipe, c::AnnotatedChar)`, `base/strings/annotated_io.jl:73-79`. -/
def writePipeC (p : Pipe) (c : AC) : Except AErr (JInt64 × Pipe) :=
  match p with
  | .aio a =>
    match (writeC c).run a with
    | .ok n a' => .ok (n, .aio a')
    | .error e _ => .error e
  | .other out => .ok (ix (charBytes c.char).length, .other (out ++ charBytes c.char))

/-! ## Reading and truncation -/

/-- `read(io.io, String)`: `String(read(io))`, all available bytes. -/
def readString : AM JStr := do
  let bs ← onIO IOBuffers.readAll
  if h : bs.length < 2 ^ 62 then pure ⟨bs, h⟩ else throw (.str .outOfMemory)

/-- `read(io::AnnotatedIOBuffer, ::Type{AnnotatedString{T}})`,
`base/strings/annotated_io.jl:81-90`, for `T = String`. -/
def readAnns (anns : List RA) (start : JInt64) : List RA :=
  if start.val = 0 then anns
  else (anns.filter fun annot => decide (annot.hi.val > start.val)).map fun annot =>
    annot.setR (urange (imax (ix 1) (annot.lo - start)) (annot.hi - start))

def readAS : AM AS := do
  let a ← get
  let annots := readAnns a.anns (position a)
  let s ← readString
  pure ⟨s, annots⟩

/-- `read(io, ::Type{AnnotatedString{AbstractString}}) = read(io, AnnotatedString{String})` (`:91`)
and `read(io, ::Type{AnnotatedString}) = read(io, AnnotatedString{String})` (`:92`). -/
def readASAny : AM AS := readAS

/-- The continuation loop of `read(io::IO, ::Type{Char})`, `base/io.jl:1098-1103`. -/
def readCharLoop (l : Nat) : Nat → Int → UInt32 → IOBuffers.M UInt32
  | 0, _, c => pure c
  | fuel + 1, s, c => do
    let io ← get
    if !(decide (s ≥ l) && !IOBuffers.eof io) then return c
    let b ← IOBuffers.peekByte
    if (b &&& 0xc0) != 0x80 then return c
    let b ← IOBuffers.readByte
    readCharLoop l fuel (s - 8) (c ||| (b.toUInt32 <<< s.toNat.toUInt32))

/-- `read(io::IO, ::Type{Char})`, `base/io.jl:1091-1106`: the lead byte, then up to
`4 - leading_ones(b0)` continuation bytes (the loop runs at most three times). -/
def readChar : IOBuffers.M UInt32 := do
  let b0 ← IOBuffers.readByte
  let lo := clo32 (b0.toUInt32 <<< 24)
  let c := b0.toUInt32 <<< 24
  if 2 ≤ lo ∧ lo ≤ 4 then readCharLoop (8 * (4 - lo)) 3 16 c else pure c

/-- `read(io::AnnotatedIOBuffer, ::Type{AnnotatedChar{T}})`,
`base/strings/annotated_io.jl:94-99`, for `T = Char`: the annotations whose
region contains `pos + 1`. -/
def charAnns (anns : List RA) (pos : JInt64) : List Ann :=
  (anns.filter fun annot => decide (annot.lo.val ≤ (pos + ix 1).val ∧ (pos + ix 1).val ≤ annot.hi.val)).map RA.toAnn

def readAC : AM AC := do
  let a ← get
  let pos := position a
  let char ← onIO readChar
  pure ⟨char, charAnns a.anns pos⟩

/-- `read(io, ::Type{AnnotatedChar{AbstractChar}})` (`:100`) and
`read(io, ::Type{AnnotatedChar})` (`:101`) read an `AnnotatedChar{Char}`. -/
def readACAny : AM AC := readAC

/-- `truncate(io::AnnotatedIOBuffer, size::Integer)`, `base/strings/annotated_io.jl:103-109`. -/
def truncAnns (anns : List RA) (size : JInt64) : List RA :=
  (anns.filter fun ann => decide (ann.lo.val ≤ size.val)).map fun ann => ann.setR (urange ann.lo (imin size ann.hi))

def truncateAIO (size : JInt64) : AM Unit := do
  onIO (IOBuffers.truncate size)
  let a ← get
  setAnns (truncAnns a.anns size)

/-! ## Display, `base/strings/annotated_io.jl:340-425`

Without StyledStrings these methods write the unannotated text. An `IO` is a
byte sink and `color` its `:color` property. -/

/-- `function printstyled end`, `base/strings/annotated_io.jl:342`: a generic
function without methods; calling it throws `MethodError`. -/
def printstyledDecl : Except JlError Unit := .error (.methodError "printstyled")

/-- The value `ansi_write` receives: an `AnnotatedChar` or an `AnnotatedString`
(SubString). -/
inductive DArg where
  | achar (c : AC)
  | w (x : WArg)

/-- `unannotate(x)` or `x.char`, as the bytes printed. -/
def dBytes : DArg → List UInt8
  | .achar c => charBytes c.char
  | .w (.str s) => s.str.bytes
  | .w (.sub s) => subBytes s

/-- `ansi_write(f, io, x) = f(io, x isa AnnotatedChar ? x.char : unannotate(x))`,
`base/strings/annotated_io.jl:356-357`, for `f = write` on a byte sink. -/
def ansiWrite (out : List UInt8) (x : DArg) : JInt64 × List UInt8 :=
  (ix (dBytes x).length, out ++ dBytes x)

/-- `ansi_write_(f, io, x) = invoke_in_world(tls_world_age(), ansi_write, f, io, x)`,
`:359-360`: the latest-world `ansi_write`, which without StyledStrings is the
fallback above. -/
def ansiWrite_ (out : List UInt8) (x : DArg) : JInt64 × List UInt8 := ansiWrite out x

/-- `Base.write(io::IO, s::Union{AnnotatedString, SubString})` (`:362-363`). -/
def writeIO (out : List UInt8) (x : WArg) : JInt64 × List UInt8 := ansiWrite_ out (.w x)
/-- `Base.write(io::IO, c::AnnotatedChar)` (`:365-366`). -/
def writeIOC (out : List UInt8) (c : AC) : JInt64 × List UInt8 := ansiWrite_ out (.achar c)

/-- `Base.write(io::IO, aio::AnnotatedIOBuffer)`, `:368-380`: with `:color => true`
the `AnnotatedString` read from `aio` goes through `ansi_write_`; otherwise
`write(io, aio.io)` copies the readable bytes. Both consume `aio`. -/
def writeIOAIO (color : Bool) (out : List UInt8) (aio : AIO) :
    Except AErr ((JInt64 × List UInt8) × AIO) :=
  if color then
    match readASAny.run aio with
    | .ok s aio' => .ok (ansiWrite_ out (.w (.str s)), aio')
    | .error e _ => .error e
  else
    let bs := IOBuffers.slice aio.io.data aio.io.ptr.val aio.io.size.val
    if !aio.io.readable then .error (.io (.jl (.argumentError "read failed, IOBuffer is not readable")))
    else .ok ((ix bs.length, out ++ bs), { aio with io := { aio.io with ptr := aio.io.size + IOBuffers.i 1 } })

/-- `Base.print(io::IO, s::Union{AnnotatedString, SubString})` (`:384-385`). -/
def printIO (out : List UInt8) (x : WArg) : List UInt8 := (ansiWrite_ out (.w x)).2
/-- `Base.print(io::IO, s::AnnotatedChar)` (`:387-388`). -/
def printIOC (out : List UInt8) (c : AC) : List UInt8 := (ansiWrite_ out (.achar c)).2
/-- `Base.print(io::AnnotatedIOBuffer, s::Union{AnnotatedString, SubString})` (`:390-391`). -/
def printAIO (x : WArg) : AM Unit := do discard (writeW x)
/-- `Base.print(io::AnnotatedIOBuffer, c::AnnotatedChar)` (`:393-394`). -/
def printAIOC (c : AC) : AM Unit := do discard (writeC c)

/-- An argument of `printstyled(io::AnnotatedIOBuffer, msg...)`. -/
inductive PArg where
  | w (x : WArg)
  | achar (c : AC)
  | other (bs : List UInt8)

/-- `print(io, msg...)` on an `AnnotatedIOBuffer`: each argument in order. -/
def printAll : List PArg → AM Unit
  | [] => pure ()
  | .w x :: rest => do printAIO x; printAll rest
  | .achar c :: rest => do printAIOC c; printAll rest
  | .other bs :: rest => do discard (writePlain bs); printAll rest

/-- `styled_print(io::AnnotatedIOBuffer, msg, kwargs) = print(io, msg...)` (`:396`):
the fallback ignores the keyword arguments. -/
def styledPrint (msg : List PArg) (_kwargs : List (Nat × Val)) : AM Unit := printAll msg
/-- `styled_print_(io, msg, kwargs) = invoke_in_world(tls_world_age(), styled_print, ...)` (`:398-399`). -/
def styledPrint_ (msg : List PArg) (kwargs : List (Nat × Val)) : AM Unit := styledPrint msg kwargs
/-- `Base.printstyled(io::AnnotatedIOBuffer, msg...; kwargs...) = styled_print_(io, msg, kwargs)` (`:401-402`). -/
def printstyledAIO (msg : List PArg) (kwargs : List (Nat × Val)) : AM Unit := styledPrint_ msg kwargs

/-- `Base.escape_string(io::IO, s::Union{AnnotatedString, SubString}, esc; keep, ascii, fullhex)`,
`:406-408`: `ansi_write_` with a writer that calls `escape_string` on the
unannotated string; the `escape_string` of a `String` is a parameter. -/
def escapeStringA (escape : List UInt8 → List UInt8) (out : List UInt8) (x : WArg) : List UInt8 :=
  out ++ escape (dBytes (.w x))

/-- `show_annot(io::IO, ::Any) = nothing` (`:412`): prints nothing. -/
def showAnnot (out : List UInt8) : List UInt8 := out
/-- `show_annot(io::IO, ::MIME, ::Any) = nothing` (`:413`). -/
def showAnnotM (out : List UInt8) : List UInt8 := out
/-- `show_annot_(io, x) = invoke_in_world(tls_world_age(), show_annot, io, x)` (`:415-416`). -/
def showAnnot_ (out : List UInt8) : List UInt8 := showAnnot out
/-- `show_annot_(io, m, x)` (`:418-419`). -/
def showAnnotM_ (out : List UInt8) : List UInt8 := showAnnotM out
/-- `Base.show(io, ::MIME"text/html", s::Union{AnnotatedString, SubString}) = show_annot_(io, m, s)` (`:421-422`). -/
def showHtml (out : List UInt8) (_x : WArg) : List UInt8 := showAnnotM_ out
/-- `Base.show(io, ::MIME"text/html", c::AnnotatedChar) = show_annot_(io, m, c)` (`:424-425`). -/
def showHtmlC (out : List UInt8) (_c : AC) : List UInt8 := showAnnotM_ out

end JuliaLean.StringsCovB.AIO
