import JuliaLean.base.strings.annotated
import JuliaLean.base.io
import JuliaLean.base.iobuffer
import JuliaLean.base.strings.util
import JuliaLean.base.regex

/-!
# Model of `base/strings/annotated_io.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Annotated values, substring offsets, range construction and mutable annotation
stores reuse `base.strings.annotated`. Buffer handles and IO world effects remain
typed. Overwrite clearing, ordered annotation-run merging, replacement drift and
annotation splitting follow the source, including its exact endpoint checks.
Underlying IO, replacement matching, world-age dispatch and rendering are typed
callees. Default unstyled/HTML methods mirror their source behaviour.
-/

namespace JuliaLean.base.strings.annotated_io
open JuliaLean
open JuliaLean.base.io (M Error)
open JuliaLean.base.strings.annotated (I Region Annotation RegionAnnotation AnnotatedString AnnotatedChar
  Store StringOps SubString i region shift emptyRegion)

def getAt {World A : Type} (xs : List A) (index : I) : M World A := do
  if index.val ≤ 0 then throw (.jl .boundsError)
  match xs[(index.val - 1).toNat]? with
  | some value => pure value
  | none => throw (.jl .boundsError)

def setAt {World Ref A : Type} (store : Store World Ref A) (ref : Ref) (index : I) (value : A) : M World Unit := do
  let old ← store.read ref
  if index.val ≤ 0 || index.val > old.length then throw (.jl .boundsError)
  store.write ref (old.set (index.val - 1).toNat value)

def insertAt {World Ref A : Type} (store : Store World Ref A) (ref : Ref) (index : I) (value : A) : M World Unit := do
  let old ← store.read ref
  if index.val ≤ 0 || index.val > old.length + 1 then throw (.jl .boundsError)
  let offset := (index.val - 1).toNat
  store.write ref (old.take offset ++ [value] ++ old.drop offset)

structure BufferOps (World Buffer : Type) where
  newBuffer : M World Buffer
  position : Buffer → M World I
  eof : Buffer → M World Bool
  filesize : Buffer → M World I
  seekend : Buffer → M World Unit
  copy : Buffer → M World Buffer

structure Replacement where
  region : Region
  offset : I

structure ReplacementOps (World Buffer S Args Count Patterns Replacers Spans Replacer : Type) where
  emptyArgs : Args → Bool
  isZero : Count → Bool
  defaultCount : Count
  leCount : I → Count → M World Bool
  init : S → Args → Count → M World (I × Patterns × Replacers × Spans × Bool)
  once : Buffer → S → I → I → Patterns → Replacers → Spans → Count → I → I →
    M World (Spans × I × Region × I × I)
  freePatterns : Patterns → M World Unit
  getReplacer : Replacers → I → M World Replacer
  isAnnotated : Replacer → Bool

/--
Julia source: base/strings/annotated_io.jl:5-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct AnnotatedIOBuffer <: AbstractPipe
    io::IOBuffer
    annotations::Vector{RegionAnnotation}
end
```
-/
structure AnnotatedIOBuffer (Buffer Regions : Type) where
  io : Buffer
  annotations : Regions

/--
Julia source: base/strings/annotated_io.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedIOBuffer(io::IOBuffer) = AnnotatedIOBuffer(io, Vector{RegionAnnotation}())
```
-/
def newAnnotatedIOBuffer {World Buffer Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (io : Buffer) : M World (AnnotatedIOBuffer Buffer Ref) := do pure ⟨io, ← store.new []⟩

/--
Julia source: base/strings/annotated_io.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedIOBuffer() = AnnotatedIOBuffer(IOBuffer())
```
-/
def newAnnotatedIOBufferDefault {World Buffer Ref Value : Type}
    (store : Store World Ref (RegionAnnotation Value)) (newBuffer : M World Buffer)
    : M World (AnnotatedIOBuffer Buffer Ref) := do newAnnotatedIOBuffer store (← newBuffer)

/--
Julia source: base/strings/annotated_io.jl:13-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, aio::AnnotatedIOBuffer)
    show(io, AnnotatedIOBuffer)
    size = filesize(aio.io)
    print(io, '(', size, " byte", ifelse(size == 1, "", "s"), ", ",
          length(aio.annotations), " annotation", ifelse(length(aio.annotations) == 1, "", "s"), ")")
end
```
-/
def showBuffer {World Io Buffer Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : BufferOps World Buffer) (showType : Io → M World Unit)
    (print : Io → String → M World Unit) (io : Io) (aio : AnnotatedIOBuffer Buffer Ref) : M World Unit := do
  showType io
  let size ← ops.filesize aio.io
  let count := (← store.read aio.annotations).length
  print io ("(" ++ toString size.val ++ " byte" ++ (if size.val == 1 then "" else "s") ++ ", " ++
    toString count ++ " annotation" ++ (if count == 1 then "" else "s") ++ ")")

/--
Julia source: base/strings/annotated_io.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_reader(io::AnnotatedIOBuffer) = io.io
```
-/
def pipeReader {Buffer Ref : Type} (io : AnnotatedIOBuffer Buffer Ref) : Buffer := io.io

/--
Julia source: base/strings/annotated_io.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_writer(io::AnnotatedIOBuffer) = io.io
```
-/
def pipeWriter {Buffer Ref : Type} (io : AnnotatedIOBuffer Buffer Ref) : Buffer := io.io

/--
Julia source: base/strings/annotated_io.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
position(io::AnnotatedIOBuffer) = position(io.io)
```
-/
def position {World Buffer Ref : Type} (ops : BufferOps World Buffer)
    (io : AnnotatedIOBuffer Buffer Ref) : M World I := ops.position io.io

/--
Julia source: base/strings/annotated_io.jl:25-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
seek(io::AnnotatedIOBuffer, n::Integer) = (seek(io.io, n); io)
```
-/
def seek {World Buffer Ref Integer : Type} (seek : Buffer → Integer → M World Unit)
    (io : AnnotatedIOBuffer Buffer Ref) (n : Integer) : M World (AnnotatedIOBuffer Buffer Ref) := do
  seek io.io n
  pure io

/--
Julia source: base/strings/annotated_io.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
skip(io::AnnotatedIOBuffer, n::Integer) = (skip(io.io, n); io)
```
-/
def skip {World Buffer Ref Integer : Type} (skip : Buffer → Integer → M World Unit)
    (io : AnnotatedIOBuffer Buffer Ref) (n : Integer) : M World (AnnotatedIOBuffer Buffer Ref) := do
  skip io.io n
  pure io

/--
Julia source: base/strings/annotated_io.jl:26-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
seekend(io::AnnotatedIOBuffer) = (seekend(io.io); io)
```
-/
def seekend {World Buffer Ref : Type} (ops : BufferOps World Buffer)
    (io : AnnotatedIOBuffer Buffer Ref) : M World (AnnotatedIOBuffer Buffer Ref) := do
  ops.seekend io.io
  pure io

/--
Julia source: base/strings/annotated_io.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(io::AnnotatedIOBuffer) = AnnotatedIOBuffer(copy(io.io), copy(io.annotations))
```
-/
def copy {World Buffer Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : BufferOps World Buffer) (io : AnnotatedIOBuffer Buffer Ref) : M World (AnnotatedIOBuffer Buffer Ref) := do
  let buffer ← ops.copy io.io
  pure ⟨buffer, ← store.copy io.annotations⟩

/--
Julia source: base/strings/annotated_io.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotations(io::AnnotatedIOBuffer) = io.annotations
```
-/
def annotations {Buffer Ref : Type} (io : AnnotatedIOBuffer Buffer Ref) : Ref := io.annotations

/--
Julia source: base/strings/annotated_io.jl:32-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotate!(io::AnnotatedIOBuffer, range::UnitRange{Int}, label::Symbol, @nospecialize(val::Any)) =
    (_annotate!(io.annotations, range, label, val); io)
```
-/
def annotate {World Buffer Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (isNothing : Value → Bool) (io : AnnotatedIOBuffer Buffer Ref) (range : Region)
    (label : String) (value : Value) : M World (AnnotatedIOBuffer Buffer Ref) := do
  let _ ← JuliaLean.base.strings.annotated.annotateList store isNothing io.annotations range label value
  pure io

/--
Julia source: base/strings/annotated_io.jl:120-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _clear_annotations_in_region!(annotations::Vector{RegionAnnotation}, span::UnitRange{Int})
    # Clear out any overlapping pre-existing annotations.
    filter!(ann -> first(ann.region) < first(span) || last(ann.region) > last(span), annotations)
    extras = Tuple{Int, RegionAnnotation}[]
    for i in eachindex(annotations)
        annot = annotations[i]
        region = annot.region
        # Test for partial overlap
        if first(region) <= first(span) <= last(region) || first(region) <= last(span) <= last(region)
            annotations[i] =
                @inline(setindex(annot,
                         if first(region) < first(span)
                             first(region):first(span)-1
                         else
                             last(span)+1:last(region)
                         end,
                         :region))
            # If `span` fits exactly within `region`, then we've only copied over
            # the beginning overhang, but also need to conserve the end overhang.
            if first(region) < first(span) && last(span) < last(region)
                push!(extras, (i, @inline(setindex(annot, last(span)+1:last(region), :region))))
            end
        end
    end
    # Insert any extra entries in the appropriate position
    for (offset, (i, entry)) in enumerate(extras)
        insert!(annotations, i + offset, entry)
    end
    annotations
end
```
-/
def clearAnnotationsInRegion {World Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (annotations : Ref) (span : Region) : M World Ref := do
  let old ← store.read annotations
  store.write annotations (old.filter (fun ann => ann.region.start < span.start || ann.region.stop > span.stop))
  let mut extras : List (I × RegionAnnotation Value) := []
  let count := (← store.read annotations).length
  for offset in List.range count do
    let index := i offset + i 1
    let annot ← getAt (← store.read annotations) index
    let r := annot.region
    if (r.start ≤ span.start && span.start ≤ r.stop) || (r.start ≤ span.stop && span.stop ≤ r.stop) then
      let newRegion := if r.start < span.start then region r.start (span.start - i 1)
        else region (span.stop + i 1) r.stop
      setAt store annotations index { annot with region := newRegion }
      if r.start < span.start && span.stop < r.stop then
        extras := extras ++ [(index, { annot with region := region (span.stop + i 1) r.stop })]
  for ((index, entry), offset) in extras.zipIdx do
    insertAt store annotations (index + i offset + i 1) entry
  pure annotations

/--
Julia source: base/strings/annotated_io.jl:168-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _insert_annotations!(annots::Vector{RegionAnnotation}, newannots::Vector{RegionAnnotation}, offset::Int = 0)
    run = @label search begin
        if !isempty(annots) && last(last(annots).region) == offset
            for i in reverse(axes(newannots, 1))
                annot = newannots[i]
                first(annot.region) == 1 || continue
                i <= length(annots) || continue
                annot.label == last(annots).label || continue
                annot.value == last(annots).value || continue
                all(1:i) do runlen
                    new = newannots[begin+runlen-1]
                    old = annots[end-i+runlen]
                    !(last(old.region) != offset ||
                    first(new.region) != 1 ||
                    old.label != new.label ||
                    old.value != new.value)
                end || continue
                break search i
            end
        end
        0
    end
    for runindex in 0:run-1
        old_index = lastindex(annots) - run + 1 + runindex
        old = annots[old_index]
        new = newannots[begin+runindex]
        extannot = (region = first(old.region):last(new.region)+offset,
                    label = old.label,
                    value = old.value)
        annots[old_index] = extannot
    end
    for index in run+1:lastindex(newannots)
        annot = newannots[index]
        start, stop = first(annot.region), last(annot.region)
        # REVIEW: For some reason, construction of `newannot`
        # can be a significant contributor to the overall runtime
        # of this function. For instance, executing:
        #
        #     replace(AnnotatedIOBuffer(), S"apple",
        #             'e' => S"{red:x}", 'p' => S"{green:y}")
        #
        # results in 3 calls to `_insert_annotations!`. It takes
        # ~570ns in total, compared to ~200ns if we push `annot`
        # instead of `newannot`. Commenting out the `_insert_annotations!`
        # line reduces the runtime to ~170ns, from which we can infer
        # that constructing `newannot` is somehow responsible for
        # a ~30ns -> ~400ns (~13x) increase in runtime!!
        # This also comes with a marginal increase in allocations
        # (compared to the commented out version) of 2 -> 14 (250b -> 720b).
        #
        # This seems quite strange, but I haven't dug into the generated
        # LLVM or ASM code. If anybody reading this is interested in checking
        # this out, that would be brilliant 🙏.
        #
        # What I have done is found that "direct tuple reconstruction"
        # (as below) is several times faster than using `setindex`.
        newannot = (region = start+offset:stop+offset,
                    label = annot.label,
                    value = annot.value)
        push!(annots, newannot)
    end
end
```
-/
def insertAnnotations {World Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (equal notEqual : Value → Value → M World Bool) (annots newannots : Ref) (offset : I := i 0) : M World Unit := do
  let mut run := i 0
  let old ← store.read annots
  if let some last := old.getLast? then
    if last.region.stop == offset then
      let count := (← store.read newannots).length
      for candidate in (List.range count).reverse do
        let index := i candidate + i 1
        let annot ← getAt (← store.read newannots) index
        if annot.region.start != i 1 then continue
        if index.val > (← store.read annots).length then continue
        let last ← getAt (← store.read annots) (i (← store.read annots).length)
        if annot.label != last.label then continue
        if !(← equal annot.value last.value) then continue
        let mut valid := true
        for off in List.range index.val.toNat do
          let runlen := i off + i 1
          let new ← getAt (← store.read newannots) runlen
          let old ← getAt (← store.read annots) (i (← store.read annots).length - index + runlen)
          if old.region.stop != offset || new.region.start != i 1 || old.label != new.label then
            valid := false
            break
          if ← notEqual old.value new.value then
            valid := false
            break
        if !valid then continue
        run := index
        break
  for off in List.range run.val.toNat do
    let oldIndex := i (← store.read annots).length - run + i 1 + i off
    let old ← getAt (← store.read annots) oldIndex
    let new ← getAt (← store.read newannots) (i off + i 1)
    setAt store annots oldIndex ⟨region old.region.start (new.region.stop + offset), old.label, old.value⟩
  let lastNew := i (← store.read newannots).length
  for off in List.range (max 0 (lastNew - run).val).toNat do
    let index := run + i 1 + i off
    let annot ← getAt (← store.read newannots) index
    store.push annots ⟨region (annot.region.start + offset) (annot.region.stop + offset), annot.label, annot.value⟩

/--
Julia source: base/strings/annotated_io.jl:231-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_insert_annotations!(io::AnnotatedIOBuffer, newannots::Vector{RegionAnnotation}, offset::Int = position(io)) =
    _insert_annotations!(io.annotations, newannots, offset)
```
-/
def insertBufferAnnotations {World Buffer Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : BufferOps World Buffer) (equal notEqual : Value → Value → M World Bool)
    (io : AnnotatedIOBuffer Buffer Ref) (newannots : Ref) (offset : Option I := none) : M World Unit := do
  let offset ← match offset with | some offset => pure offset | none => position ops io
  insertAnnotations store equal notEqual io.annotations newannots offset

/--
Julia source: base/strings/annotated_io.jl:35-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(io::AnnotatedIOBuffer, astr::Union{AnnotatedString, SubString{<:AnnotatedString}})
    astr = AnnotatedString(astr)
    offset = position(io.io)
    eof(io) || _clear_annotations_in_region!(io.annotations, offset+1:offset+ncodeunits(astr))
    _insert_annotations!(io, astr.annotations)
    write(io.io, String(astr))
end
```
-/
def writeAnnotatedString {World Buffer Ref Value Input S : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : BufferOps World Buffer) (equal notEqual : Value → Value → M World Bool)
    (construct : Input → M World (AnnotatedString S Ref)) (ncodeunits : AnnotatedString S Ref → M World I)
    (toString : AnnotatedString S Ref → M World S) (write : Buffer → S → M World I)
    (io : AnnotatedIOBuffer Buffer Ref) (astr : Input) : M World I := do
  let astr ← construct astr
  let offset ← ops.position io.io
  if !(← ops.eof io.io) then
    let _ ← clearAnnotationsInRegion store io.annotations (region (offset + i 1) (offset + (← ncodeunits astr)))
  insertBufferAnnotations store ops equal notEqual io astr.annotations
  write io.io (← toString astr)

/--
Julia source: base/strings/annotated_io.jl:43-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::AnnotatedIOBuffer, c::AnnotatedChar) =
    write(io, AnnotatedString(string(c), [(region=1:ncodeunits(c), a...) for a in c.annotations]))
```
-/
def writeAnnotatedChar {World Buffer Regions Annots Value C S : Type}
    (regions : Store World Regions (RegionAnnotation Value)) (annots : Store World Annots (Annotation Value))
    (string : AnnotatedChar C Annots → M World S) (ncodeunits : AnnotatedChar C Annots → M World I)
    (write : AnnotatedIOBuffer Buffer Regions → AnnotatedString S Regions → M World I)
    (io : AnnotatedIOBuffer Buffer Regions) (c : AnnotatedChar C Annots) : M World I := do
  let str ← string c
  let mut values := []
  for a in ← annots.read c.annotations do
    values := values ++ [⟨region (i 1) (← ncodeunits c), a.label, a.value⟩]
  write io ⟨str, ← regions.new values⟩

/--
Julia source: base/strings/annotated_io.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::AnnotatedIOBuffer, x::AbstractString) = write(io.io, x)::Int
```
-/
def writeAbstractString {World Buffer Ref S : Type} (write : Buffer → S → M World I)
    (io : AnnotatedIOBuffer Buffer Ref) (value : S) : M World I := write io.io value

/--
Julia source: base/strings/annotated_io.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::AnnotatedIOBuffer, s::Union{SubString{String}, String}) = write(io.io, s)
```
-/
def writePlainString {World Buffer Ref S : Type} (write : Buffer → S → M World I)
    (io : AnnotatedIOBuffer Buffer Ref) (value : S) : M World I := write io.io value

/--
Julia source: base/strings/annotated_io.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::AnnotatedIOBuffer, s::StringViewAndSub) = write(io.io, s)::Int
```
-/
def writeStringView {World Buffer Ref S : Type} (write : Buffer → S → M World I)
    (io : AnnotatedIOBuffer Buffer Ref) (value : S) : M World I := write io.io value

/--
Julia source: base/strings/annotated_io.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::AnnotatedIOBuffer, b::UInt8) = write(io.io, b)
```
-/
def writeByte {World Buffer Ref : Type} (write : Buffer → JInt .u8 → M World I)
    (io : AnnotatedIOBuffer Buffer Ref) (value : JInt .u8) : M World I := write io.io value

/--
Julia source: base/strings/annotated_io.jl:50-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(dest::AnnotatedIOBuffer, src::AnnotatedIOBuffer)
    destpos = position(dest)
    isappending = eof(dest)
    srcpos = position(src)
    nb = write(dest.io, src.io)
    isappending || _clear_annotations_in_region!(dest.annotations, destpos:destpos+nb)
    srcannots = [@inline(setindex(annot, max(1 + srcpos, first(annot.region)):last(annot.region), :region))
                 for annot in src.annotations if first(annot.region) >= srcpos]
    _insert_annotations!(dest, srcannots, destpos - srcpos)
    nb
end
```
-/
def writeBuffer {World Buffer Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : BufferOps World Buffer) (equal notEqual : Value → Value → M World Bool)
    (write : Buffer → Buffer → M World I) (dest src : AnnotatedIOBuffer Buffer Ref) : M World I := do
  let destpos ← position ops dest
  let isappending ← ops.eof dest.io
  let srcpos ← position ops src
  let nb ← write dest.io src.io
  if !isappending then
    let _ ← clearAnnotationsInRegion store dest.annotations (region destpos (destpos + nb))
  let mut srcannots := []
  for annot in ← store.read src.annotations do
    if annot.region.start ≥ srcpos then
      srcannots := srcannots ++ [{ annot with region := region (max (i 1 + srcpos) annot.region.start) annot.region.stop }]
  let srcannotsRef ← store.new srcannots
  insertBufferAnnotations store ops equal notEqual dest srcannotsRef (some (destpos - srcpos))
  pure nb

/--
Julia source: base/strings/annotated_io.jl:64-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(io::AbstractPipe, s::Union{AnnotatedString, SubString{<:AnnotatedString}})
    if pipe_writer(io) isa AnnotatedIOBuffer
        write(pipe_writer(io), s)
    else
        invoke(write, Tuple{IO, typeof(s)}, io, s)
    end::Int
end
```
-/
def writePipeString {World Pipe Writer Input : Type} (pipeWriter : Pipe → M World Writer)
    (isAnnotatedBuffer : Writer → Bool) (writeAnnotated : Writer → Input → M World I)
    (invokeIOWrite : Pipe → Input → M World I) (io : Pipe) (value : Input) : M World I := do
  if isAnnotatedBuffer (← pipeWriter io) then writeAnnotated (← pipeWriter io) value
  else invokeIOWrite io value

/--
Julia source: base/strings/annotated_io.jl:73-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(io::AbstractPipe, c::AnnotatedChar)
    if pipe_writer(io) isa AnnotatedIOBuffer
        write(pipe_writer(io), c)
    else
        invoke(write, Tuple{IO, typeof(c)}, io, c)
    end::Int
end
```
-/
def writePipeChar {World Pipe Writer Input : Type} (pipeWriter : Pipe → M World Writer)
    (isAnnotatedBuffer : Writer → Bool) (writeAnnotated : Writer → Input → M World I)
    (invokeIOWrite : Pipe → Input → M World I) (io : Pipe) (value : Input) : M World I := do
  if isAnnotatedBuffer (← pipeWriter io) then writeAnnotated (← pipeWriter io) value
  else invokeIOWrite io value

/--
Julia source: base/strings/annotated_io.jl:81-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(io::AnnotatedIOBuffer, ::Type{AnnotatedString{T}}) where {T <: AbstractString}
    start = position(io)
    if start == 0
        AnnotatedString(read(io.io, T), copy(io.annotations))
    else
        annots = [@inline(setindex(annot, UnitRange{Int}(max(1, first(annot.region) - start), last(annot.region)-start), :region))
                  for annot in io.annotations if last(annot.region) > start]
        AnnotatedString(read(io.io, T), annots)
    end
end
```
-/
def readAnnotatedString {World Buffer Ref Value S : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : BufferOps World Buffer) (read : Buffer → M World S) (io : AnnotatedIOBuffer Buffer Ref)
    : M World (AnnotatedString S Ref) := do
  let start ← position ops io
  if start.val == 0 then
    let str ← read io.io
    pure ⟨str, ← store.copy io.annotations⟩
  else
    let mut values := []
    for annot in ← store.read io.annotations do
      if annot.region.stop > start then
        values := values ++ [{ annot with region := region (max (i 1) (annot.region.start - start)) (annot.region.stop - start) }]
    let annots ← store.new values
    pure ⟨← read io.io, annots⟩

/--
Julia source: base/strings/annotated_io.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::AnnotatedIOBuffer, ::Type{AnnotatedString{AbstractString}}) = read(io, AnnotatedString{String})
```
-/
def readAbstractAnnotatedString {World Buffer Ref Result : Type} (read : AnnotatedIOBuffer Buffer Ref → M World Result)
    (io : AnnotatedIOBuffer Buffer Ref) : M World Result := read io

/--
Julia source: base/strings/annotated_io.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::AnnotatedIOBuffer, ::Type{AnnotatedString}) = read(io, AnnotatedString{String})
```
-/
def readDefaultAnnotatedString {World Buffer Ref Result : Type} (read : AnnotatedIOBuffer Buffer Ref → M World Result)
    (io : AnnotatedIOBuffer Buffer Ref) : M World Result := read io

/--
Julia source: base/strings/annotated_io.jl:94-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(io::AnnotatedIOBuffer, ::Type{AnnotatedChar{T}}) where {T <: AbstractChar}
    pos = position(io)
    char = read(io.io, T)
    annots = [NamedTuple{(:label, :value)}(annot) for annot in io.annotations if pos+1 in annot.region]
    AnnotatedChar(char, annots)
end
```
-/
def readAnnotatedChar {World Buffer Regions Annots Value C : Type}
    (regions : Store World Regions (RegionAnnotation Value)) (annots : Store World Annots (Annotation Value))
    (ops : BufferOps World Buffer) (read : Buffer → M World C) (io : AnnotatedIOBuffer Buffer Regions)
    : M World (AnnotatedChar C Annots) := do
  let pos ← position ops io
  let char ← read io.io
  let mut values := []
  for annot in ← regions.read io.annotations do
    if annot.region.start ≤ pos + i 1 && pos + i 1 ≤ annot.region.stop then
      values := values ++ [⟨annot.label, annot.value⟩]
  pure ⟨char, ← annots.new values⟩

/--
Julia source: base/strings/annotated_io.jl:100-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::AnnotatedIOBuffer, ::Type{AnnotatedChar{AbstractChar}}) = read(io, AnnotatedChar{Char})
```
-/
def readAbstractAnnotatedChar {World Buffer Ref Result : Type} (read : AnnotatedIOBuffer Buffer Ref → M World Result)
    (io : AnnotatedIOBuffer Buffer Ref) : M World Result := read io

/--
Julia source: base/strings/annotated_io.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::AnnotatedIOBuffer, ::Type{AnnotatedChar}) = read(io, AnnotatedChar{Char})
```
-/
def readDefaultAnnotatedChar {World Buffer Ref Result : Type} (read : AnnotatedIOBuffer Buffer Ref → M World Result)
    (io : AnnotatedIOBuffer Buffer Ref) : M World Result := read io

/--
Julia source: base/strings/annotated_io.jl:103-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function truncate(io::AnnotatedIOBuffer, size::Integer)
    truncate(io.io, size)
    filter!(ann -> first(ann.region) <= size, io.annotations)
    map!(ann -> @inline(setindex(ann, first(ann.region):min(size, last(ann.region)), :region)),
         io.annotations, io.annotations)
    io
end
```
-/
def truncate {World Buffer Ref Value Integer : Type} (store : Store World Ref (RegionAnnotation Value))
    (truncate : Buffer → Integer → M World Unit) (leSize : I → Integer → M World Bool)
    (minSize : Integer → I → M World I) (io : AnnotatedIOBuffer Buffer Ref) (size : Integer)
    : M World (AnnotatedIOBuffer Buffer Ref) := do
  truncate io.io size
  let old ← store.read io.annotations
  let kept ← old.filterM (fun ann => leSize ann.region.start size)
  store.write io.annotations kept
  for (ann, index) in kept.zipIdx do
    let updated := { ann with region := region ann.region.start (← minSize size ann.region.stop) }
    setAt store io.annotations (i index + i 1) updated
  pure io

/--
Julia source: base/strings/annotated_io.jl:240-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace(out::AnnotatedIOBuffer, str::AnnotatedString, pat_f::Pair...; count = typemax(Int))
    if count == 0 || isempty(pat_f)
        write(out, str)
        return out
    end
    e1, patterns, replacers, repspans, notfound = _replace_init(str.string, pat_f, count)
    if notfound
        foreach(_free_pat_replacer, patterns)
        write(out, str)
        return out
    end
    # Modelled after `Base.annotated_chartransform`, but needing
    # to handle a bit more complexity.
    isappending = eof(out)
    newannots = empty(out.annotations)
    bytepos = bytestart = firstindex(str.string)
    replacements = [(region = (bytestart - 1):(bytestart - 1), offset = position(out))]
    nrep = 1
    while nrep <= count
        repspans, ridx, xspan, newbytes, bytepos = @inline _replace_once(
            out.io, str.string, bytestart, e1, patterns, replacers, repspans, count, nrep, bytepos)
        first(xspan) >= e1 && break
        nrep += 1
        # NOTE: When the replaced pattern ends with a multi-codeunit character,
        # `xspan` only covers up to the start of that character. However,
        # for us to correctly account for the changes to the string we need
        # the /entire/ span of codeunits that were replaced.
        if !isempty(xspan) && codeunit(str.string, last(xspan)) > 0x80
            xspan = first(xspan):nextind(str.string, last(xspan))-1
        end
        drift = last(replacements).offset
        thisrep = (region = xspan, offset = drift + newbytes - length(xspan))
        destoff = first(xspan) - 1 + drift
        push!(replacements, thisrep)
        replacement = replacers[ridx]
        _isannotated(replacement) || continue
        annots = annotations(replacement)
        annots′ = if eltype(annots) == Annotation # When it's a char not a string
            region = 1:newbytes
            [@NamedTuple{region::UnitRange{Int}, label::Symbol, value}((region, label, value))
             for (; label, value) in annots]
        else
            annots
        end::Vector{RegionAnnotation}
        _insert_annotations!(newannots, annots′, destoff)
    end
    push!(replacements, (region = e1:(e1-1), offset = last(replacements).offset))
    foreach(_free_pat_replacer, patterns)
    write(out.io, SubString(str.string, bytepos))
    # NOTE: To enable more efficient annotation clearing,
    # we make use of the fact that `_replace_once` picks
    # replacements ordered by their match start position.
    # This means that the start of `.region`s in
    # `replacements` is monotonically increasing.
    isappending || _clear_annotations_in_region!(out.annotations, first(replacements).offset:position(out))
    for (; region, label, value) in str.annotations
        start, stop = first(region), last(region)
        prioridx = searchsortedlast(
            replacements, (region = start:start, offset = 0),
            by = r -> first(r.region))
        postidx = searchsortedfirst(
            replacements, (region = stop:stop, offset = 0),
            by = r -> first(r.region))
        priorrep, postrep = replacements[prioridx], replacements[postidx]
        if prioridx == postidx && start >= first(priorrep.region) && stop <= last(priorrep.region)
            # Region contained within a replacement
            continue
        elseif postidx - prioridx <= 1 && start > last(priorrep.region) && stop < first(postrep.region)
            # Lies between replacements
            shiftregion = (start + priorrep.offset):(stop + priorrep.offset)
            shiftann = (region = shiftregion, label, value)
            push!(out.annotations, shiftann)
        else
            # Split between replacements
            prevrep = replacements[max(begin, prioridx - 1)]
            for rep in @view replacements[max(begin, prioridx - 1):min(end, postidx + 1)]
                gap = max(start, last(prevrep.region)+1):min(stop, first(rep.region)-1)
                if !isempty(gap)
                    shiftregion = (first(gap) + prevrep.offset):(last(gap) + prevrep.offset)
                    shiftann = (; region = shiftregion, label, value)
                    push!(out.annotations, shiftann)
                end
                prevrep = rep
            end
        end
    end
    append!(out.annotations, newannots)
    out
end
```
-/
def replaceInto {World Buffer S C Ref ARef Value Args Count Patterns Replacers Spans Replacer : Type}
    (store : Store World Ref (RegionAnnotation Value)) (charStore : Store World ARef (Annotation Value))
    (ops : BufferOps World Buffer) (strOps : StringOps World S C)
    (repl : ReplacementOps World Buffer S Args Count Patterns Replacers Spans Replacer)
    (equal notEqual : Value → Value → M World Bool)
    (writeAnnotated : AnnotatedIOBuffer Buffer Ref → AnnotatedString S Ref → M World I)
    (codeunit : S → I → M World (JInt .u8)) (writeTail : Buffer → S → I → M World I)
    (replacementAnnotations : Replacer → M World (Sum ARef Ref))
    (out : AnnotatedIOBuffer Buffer Ref) (str : AnnotatedString S Ref) (patf : Args)
    (count : Count := repl.defaultCount) : M World (AnnotatedIOBuffer Buffer Ref) := do
  if repl.isZero count || repl.emptyArgs patf then
    let _ ← writeAnnotated out str
    return out
  let (e1, patterns, replacers, repspans, notfound) ← repl.init str.string patf count
  if notfound then
    repl.freePatterns patterns
    let _ ← writeAnnotated out str
    return out
  let isappending ← ops.eof out.io
  let newannots ← store.new []
  let bytestart ← strOps.firstindex str.string
  let initialReplacement : Replacement := ⟨region (bytestart - i 1) (bytestart - i 1), ← position ops out⟩
  let (bytepos, finalReplacements) ← JuliaLean.base.io.whileLoop
    (fun (nrep, bytepos, repspans, replacements) => do
      if !(← repl.leCount nrep count) then return .inl (bytepos, replacements)
      let (repspans, ridx, xspan, newbytes, bytepos) ← repl.once
        out.io str.string bytestart e1 patterns replacers repspans count nrep bytepos
      if xspan.start ≥ e1 then return .inl (bytepos, replacements)
      let nrep := nrep + i 1
      let mut xspan := xspan
      if !emptyRegion xspan then
        if (← codeunit str.string xspan.stop).val > 128 then
          xspan := region xspan.start ((← strOps.nextind str.string xspan.stop) - i 1)
      let last ← match replacements.getLast? with
        | some last => pure last
        | none => throw (.jl .boundsError)
      let drift := last.offset
      let length := if emptyRegion xspan then i 0 else xspan.stop - xspan.start + i 1
      let thisrep : Replacement := ⟨xspan, drift + newbytes - length⟩
      let destoff := xspan.start - i 1 + drift
      let replacements := replacements ++ [thisrep]
      let replacement ← repl.getReplacer replacers ridx
      if repl.isAnnotated replacement then
        let annots ← replacementAnnotations replacement
        let annots ← match annots with
          | .inl chars => do
            let values := (← charStore.read chars).map
              (fun a => RegionAnnotation.mk (region (i 1) newbytes) a.label a.value)
            store.new values
          | .inr regions => pure regions
        insertAnnotations store equal notEqual newannots annots destoff
      pure (.inr (nrep, bytepos, repspans, replacements)))
    (i 1, bytestart, repspans, [initialReplacement])
  let mut replacements := finalReplacements
  let last ← match replacements.getLast? with
    | some last => pure last
    | none => throw (.jl .boundsError)
  replacements := replacements ++ [⟨region e1 (e1 - i 1), last.offset⟩]
  repl.freePatterns patterns
  let _ ← writeTail out.io str.string bytepos
  if !isappending then
    let first ← match replacements.head? with
      | some first => pure first
      | none => throw (.jl .boundsError)
    let _ ← clearAnnotationsInRegion store out.annotations (region first.offset (← position ops out))
  for annot in ← store.read str.annotations do
    let start := annot.region.start
    let stop := annot.region.stop
    let prioridx := (replacements.takeWhile (fun r => r.region.start ≤ start)).length
    let postidx := (replacements.takeWhile (fun r => r.region.start < stop)).length + 1
    let priorrep ← getAt replacements (i prioridx)
    let postrep ← getAt replacements (i postidx)
    if prioridx == postidx && start ≥ priorrep.region.start && stop ≤ priorrep.region.stop then
      continue
    else if (i postidx - i prioridx).val ≤ 1 && start > priorrep.region.stop && stop < postrep.region.start then
      store.push out.annotations { annot with region := region (start + priorrep.offset) (stop + priorrep.offset) }
    else
      let firstIndex := max 1 (prioridx - 1)
      let lastIndex := min replacements.length (postidx + 1)
      let mut prevrep ← getAt replacements (i firstIndex)
      for off in List.range (lastIndex + 1 - firstIndex) do
        let rep ← getAt replacements (i (firstIndex + off))
        let gap := region (max start (prevrep.region.stop + i 1)) (min stop (rep.region.start - i 1))
        if !emptyRegion gap then
          store.push out.annotations { annot with region := shift gap prevrep.offset }
        prevrep := rep
  for annot in ← store.read newannots do store.push out.annotations annot
  pure out

/--
Julia source: base/strings/annotated_io.jl:330-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace(out::IO, str::AnnotatedString, pat_f::Pair...; count=typemax(Int)) =
    replace(out, str.string, pat_f...; count)
```
-/
def replacePlainIO {World Io S Ref Args Count Result : Type}
    (replace : Io → S → Args → Count → M World Result) (defaultCount : Count)
    (out : Io) (str : AnnotatedString S Ref) (patf : Args) (count : Count := defaultCount) : M World Result :=
  replace out str.string patf count

/--
Julia source: base/strings/annotated_io.jl:333-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace(str::AnnotatedString, pat_f::Pair...; count=typemax(Int))
    isempty(pat_f) || iszero(count) && return str
    out = AnnotatedIOBuffer()
    replace(out, str, pat_f...; count)
    read(seekstart(out), AnnotatedString)
end
```
-/
def replaceString {World Buffer S T Ref Args Count : Type}
    (emptyArgs : Args → Bool) (isZero : Count → Bool) (defaultCount : Count)
    (newBuffer : M World (AnnotatedIOBuffer Buffer Ref))
    (replace : AnnotatedIOBuffer Buffer Ref → AnnotatedString S Ref → Args → Count →
      M World (AnnotatedIOBuffer Buffer Ref))
    (seekstart : AnnotatedIOBuffer Buffer Ref → M World (AnnotatedIOBuffer Buffer Ref))
    (read : AnnotatedIOBuffer Buffer Ref → M World (AnnotatedString T Ref))
    (str : AnnotatedString S Ref) (patf : Args) (count : Count := defaultCount)
    : M World (Sum (AnnotatedString S Ref) (AnnotatedString T Ref)) := do
  if !emptyArgs patf && isZero count then return .inl str
  let out ← newBuffer
  let _ ← replace out str patf count
  pure (.inr (← read (← seekstart out)))

/--
Julia source: base/strings/annotated_io.jl:356-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ansi_write(f::Function, io::IO, x::Any) =
    f(io, x isa AnnotatedChar ? x.char : unannotate(x))
```
-/
def ansiWrite {World Io X C S Result : Type} (isAnnotatedChar : X → Bool)
    (char : X → C) (unannotate : X → M World S)
    (fChar : Io → C → M World Result) (fString : Io → S → M World Result)
    (io : Io) (x : X) : M World Result := do
  if isAnnotatedChar x then fChar io (char x) else fString io (← unannotate x)

/--
Julia source: base/strings/annotated_io.jl:359-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ansi_write_(f::Function, io::IO, @nospecialize(x::Any)) =
    invoke_in_world(tls_world_age(), ansi_write, f, io, x)
```
-/
def ansiWriteWorld {World Age Function Io X Result : Type} (tlsWorldAge : M World Age)
    (invokeInWorld : Age → Function → Io → X → M World Result)
    (f : Function) (io : Io) (x : X) : M World Result := do
  invokeInWorld (← tlsWorldAge) f io x

/--
Julia source: base/strings/annotated_io.jl:362-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.write(io::IO, s::Union{<:AnnotatedString, SubString{<:AnnotatedString}}) =
    ansi_write_(write, io, s)::Int
```
-/
def writeIOString {World Io X Function : Type}
    (ansiWrite : Function → Io → X → M World I) (write : Function) (io : Io) (x : X) : M World I :=
  ansiWrite write io x

/--
Julia source: base/strings/annotated_io.jl:365-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.write(io::IO, c::AnnotatedChar) =
    ansi_write_(write, io, c)::Int
```
-/
def writeIOChar {World Io X Function : Type}
    (ansiWrite : Function → Io → X → M World I) (write : Function) (io : Io) (x : X) : M World I :=
  ansiWrite write io x

/--
Julia source: base/strings/annotated_io.jl:368-380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.write(io::IO, aio::AnnotatedIOBuffer)
    if get(io, :color, false) == true
        # This does introduce an overhead that technically
        # could be avoided, but I'm not sure that it's currently
        # worth the effort to implement an efficient version of
        # writing from an AnnotatedIOBuffer with style.
        # In the meantime, by converting to an `AnnotatedString` we can just
        # reuse all the work done to make that work.
        ansi_write_(write, io, read(aio, AnnotatedString))::Int
    else
        write(io, aio.io)
    end
end
```
-/
def writeIOBuffer {World Io Buffer Ref S Function : Type}
    (getColorIsTrue : Io → M World Bool) (read : AnnotatedIOBuffer Buffer Ref → M World S)
    (ansiWrite : Function → Io → S → M World I) (writeFunction : Function)
    (writeBuffer : Io → Buffer → M World I) (io : Io) (aio : AnnotatedIOBuffer Buffer Ref) : M World I := do
  if ← getColorIsTrue io then ansiWrite writeFunction io (← read aio)
  else writeBuffer io aio.io

/--
Julia source: base/strings/annotated_io.jl:384-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.print(io::IO, s::Union{<:AnnotatedString, SubString{<:AnnotatedString}}) =
    (ansi_write_(write, io, s); nothing)
```
-/
def printIOString {World Io X Function : Type}
    (ansiWrite : Function → Io → X → M World I) (write : Function) (io : Io) (x : X) : M World Unit := do
  let _ ← ansiWrite write io x
  pure ()

/--
Julia source: base/strings/annotated_io.jl:387-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.print(io::IO, s::AnnotatedChar) =
    (ansi_write_(write, io, s); nothing)
```
-/
def printIOChar {World Io X Function : Type}
    (ansiWrite : Function → Io → X → M World I) (write : Function) (io : Io) (x : X) : M World Unit := do
  let _ ← ansiWrite write io x
  pure ()

/--
Julia source: base/strings/annotated_io.jl:390-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.print(io::AnnotatedIOBuffer, s::Union{<:AnnotatedString, SubString{<:AnnotatedString}}) =
    (write(io, s); nothing)
```
-/
def printBufferString {World Buffer Ref X : Type}
    (write : AnnotatedIOBuffer Buffer Ref → X → M World I)
    (io : AnnotatedIOBuffer Buffer Ref) (x : X) : M World Unit := do
  let _ ← write io x
  pure ()

/--
Julia source: base/strings/annotated_io.jl:393-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.print(io::AnnotatedIOBuffer, c::AnnotatedChar) =
    (write(io, c); nothing)
```
-/
def printBufferChar {World Buffer Ref X : Type}
    (write : AnnotatedIOBuffer Buffer Ref → X → M World I)
    (io : AnnotatedIOBuffer Buffer Ref) (x : X) : M World Unit := do
  let _ ← write io x
  pure ()

/--
Julia source: base/strings/annotated_io.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
styled_print(io::AnnotatedIOBuffer, msg::Any, kwargs::Any) = print(io, msg...)
```
-/
def styledPrint {World Buffer Ref Messages Keywords : Type}
    (print : AnnotatedIOBuffer Buffer Ref → Messages → M World Unit)
    (io : AnnotatedIOBuffer Buffer Ref) (msg : Messages) (_kwargs : Keywords) : M World Unit := print io msg

/--
Julia source: base/strings/annotated_io.jl:398-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
styled_print_(io::AnnotatedIOBuffer, @nospecialize(msg), @nospecialize(kwargs)) =
    invoke_in_world(tls_world_age(), styled_print, io, msg, kwargs)::Nothing
```
-/
def styledPrintWorld {World Age Buffer Ref Messages Keywords : Type} (tlsWorldAge : M World Age)
    (invoke : Age → AnnotatedIOBuffer Buffer Ref → Messages → Keywords → M World Unit)
    (io : AnnotatedIOBuffer Buffer Ref) (msg : Messages) (kwargs : Keywords) : M World Unit := do
  invoke (← tlsWorldAge) io msg kwargs

/--
Julia source: base/strings/annotated_io.jl:401-402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.printstyled(io::AnnotatedIOBuffer, msg...; kwargs...) =
    styled_print_(io, msg, kwargs)
```
-/
def printstyled {World Buffer Ref Messages Keywords : Type}
    (styledPrint : AnnotatedIOBuffer Buffer Ref → Messages → Keywords → M World Unit)
    (io : AnnotatedIOBuffer Buffer Ref) (msg : Messages) (kwargs : Keywords) : M World Unit :=
  styledPrint io msg kwargs

/--
Julia source: base/strings/annotated_io.jl:406-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.escape_string(io::IO, s::Union{<:AnnotatedString, SubString{<:AnnotatedString}},
              esc = ""; keep = (), ascii::Bool=false, fullhex::Bool=false) =
    (ansi_write_((io, s) -> escape_string(io, s, esc; keep, ascii, fullhex), io, s); nothing)
```
-/
def escapeString {World Io Input S Esc Keep Result : Type}
    (escape : Io → S → Esc → Keep → Bool → Bool → M World Result)
    (ansiWrite : (Io → S → M World Result) → Io → Input → M World Result)
    (emptyEsc : Esc) (emptyKeep : Keep) (io : Io) (s : Input)
    (esc : Esc := emptyEsc) (keep : Keep := emptyKeep)
    (ascii : Bool := false) (fullhex : Bool := false) : M World Unit := do
  let _ ← ansiWrite (fun io s => escape io s esc keep ascii fullhex) io s
  pure ()

/--
Julia source: base/strings/annotated_io.jl:412-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_annot(io::IO, ::Any) = nothing
```
-/
def showAnnotation {World Io X : Type} (_io : Io) (_x : X) : M World Unit := pure ()

/--
Julia source: base/strings/annotated_io.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_annot(io::IO, ::MIME, ::Any) = nothing
```
-/
def showAnnotationMIME {World Io MIME X : Type} (_io : Io) (_m : MIME) (_x : X) : M World Unit := pure ()

/--
Julia source: base/strings/annotated_io.jl:415-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_annot_(io::IO, @nospecialize(x::Any)) =
    invoke_in_world(tls_world_age(), show_annot, io, x)::Nothing
```
-/
def showAnnotationWorld {World Io X Age : Type} (tlsWorldAge : M World Age)
    (invoke : Age → Io → X → M World Unit) (io : Io) (x : X) : M World Unit := do
  invoke (← tlsWorldAge) io x

/--
Julia source: base/strings/annotated_io.jl:418-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_annot_(io::IO, m::MIME, @nospecialize(x::Any)) =
    invoke_in_world(tls_world_age(), show_annot, io, m, x)::Nothing
```
-/
def showAnnotationMIMEWorld {World Io MIME X Age : Type} (tlsWorldAge : M World Age)
    (invoke : Age → Io → MIME → X → M World Unit) (io : Io) (m : MIME) (x : X) : M World Unit := do
  invoke (← tlsWorldAge) io m x

/--
Julia source: base/strings/annotated_io.jl:421-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.show(io::IO, m::MIME"text/html", s::Union{<:AnnotatedString, SubString{<:AnnotatedString}}) =
    show_annot_(io, m, s)
```
-/
def showHTMLString {World Io MIME X : Type} (showAnnotation : Io → MIME → X → M World Unit)
    (io : Io) (m : MIME) (x : X) : M World Unit := showAnnotation io m x

/--
Julia source: base/strings/annotated_io.jl:424-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.show(io::IO, m::MIME"text/html", c::AnnotatedChar) =
    show_annot_(io, m, c)
```
-/
def showHTMLChar {World Io MIME X : Type} (showAnnotation : Io → MIME → X → M World Unit)
    (io : Io) (m : MIME) (x : X) : M World Unit := showAnnotation io m x


/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/strings/annotated_io.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## AnnotatedIOBuffer
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:9-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:22-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Useful `IOBuffer` methods that we don't get from `AbstractPipe`
-- /Source

-- Source: base/strings/annotated_io.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:61-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # So that read/writes with `IOContext` (and any similar `AbstractPipe` wrappers)
-- # work as expected.
-- /Source

-- Source: base/strings/annotated_io.jl:71-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Can't be part of the `Union` above because it introduces method ambiguities
-- /Source

-- Source: base/strings/annotated_io.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:110-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     _clear_annotations_in_region!(annotations::Vector{$RegionAnnotation}, span::UnitRange{Int})
-- 
-- Erase the presence of `annotations` within a certain `span`.
-- 
-- This operates by removing all elements of `annotations` that are entirely
-- contained in `span`, truncating ranges that partially overlap, and splitting
-- annotations that subsume `span` to just exist either side of `span`.
-- """
-- /Source

-- Source: base/strings/annotated_io.jl:150-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     _insert_annotations!(io::AnnotatedIOBuffer, annotations::Vector{$RegionAnnotation}, offset::Int = position(io))
-- 
-- Register new `annotations` in `io`, applying an `offset` to their regions.
-- 
-- This largely consists of simply shifting the regions of `annotations` by `offset`
-- and pushing them onto `io`'s annotations. However, when it is possible to merge
-- the new annotations with recent annotations in accordance with the semantics
-- outlined in [`AnnotatedString`](@ref), we do so. More specifically, when there
-- is a run of the most recent annotations that are also present as the first
-- `annotations`, with the same value and adjacent regions, the new annotations are
-- merged into the existing recent annotations by simply extending their range.
-- 
-- This is implemented so that one can say write an `AnnotatedString` to an
-- `AnnotatedIOBuffer` one character at a time without needlessly producing a
-- new annotation for each character.
-- """
-- /Source

-- Source: base/strings/annotated_io.jl:230-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:233-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # String replacement
-- 
-- # REVIEW: For some reason the `Core.kwcall` indirection seems to cause a
-- # substantial slowdown here. If we remove `; count` from the signature
-- # and run the sample code above in `_insert_annotations!`, the runtime
-- # drops from ~4400ns to ~580ns (~7x faster). I cannot guess why this is.
-- /Source

-- Source: base/strings/annotated_io.jl:329-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:339-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Printing
-- 
-- function printstyled end
-- 
-- # NOTE: This is an interim solution to the invalidations caused
-- # by the split styled display implementation. This should be
-- # replaced by a more robust solution (such as a consolidation of
-- # the type and method definitions) in the near future.
-- module AnnotatedDisplay
-- 
-- using ..Base: IO, SubString, AnnotatedString, AnnotatedChar, AnnotatedIOBuffer
-- using ..Base: eachregion, invoke_in_world, tls_world_age, unannotate
-- 
-- # Write
-- 
-- # Unstyled fallback for when StyledStrings is not loaded.
-- /Source

-- Source: base/strings/annotated_io.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:367-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:381-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Print
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:386-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:389-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:403-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Escape
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:409-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Show
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:414-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated_io.jl:426-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end
-- /Source


end JuliaLean.base.strings.annotated_io
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
namespace JuliaLean.StringsCovB.AIOR

open JuliaLean JuliaLean.Strings JuliaLean.StringsCovB.Ann JuliaLean.StringsCovB.AIO

/-- A replacement value. -/
inductive Repl where
  | plain (bs : List UInt8)
  | astr (a : AS)
  | achar (c : AC)

/-- The code units `write(io, repl)` writes. -/
def Repl.bytes : Repl → List UInt8
  | .plain bs => bs
  | .astr a => a.str.bytes
  | .achar c => charBytes c.char

/-- A pair `pat => repl`. -/
structure APair where
  find : JInt64 → SJl StringUtil.Found
  repl : Repl

instance : Inhabited APair := ⟨⟨fun _ => .ok .nothing, .plain []⟩⟩

def APair.toPair (p : APair) : StringUtil.Pair := ⟨p.find, p.repl.bytes⟩

/-- `write(io, bytes)` into `out.io`. -/
def wIO (bs : List UInt8) : AM JInt64 := onIO (IOBuffers.unsafeWrite bs)

/-- `_replace_once(io, str, start, e1, patterns, replaces, rs, count, n, i)`,
`base/strings/util.jl:1068-1104`, writing to `out.io`: returns `(rs, x, r, nb, i)`,
with `x` zero-based and `nb` the result of `_replace` (0 when nothing is written). -/
def replaceOnce (s : JStr) (ps : List APair) (start e1 : JInt64) (rs : List StringUtil.Rng)
    (count n i : JInt64) : AM (List StringUtil.Rng × Nat × StringUtil.Rng × JInt64 × JInt64) := do
  let x := StringUtil.argmin (rs.map (·.1))
  let r := rs.getD x (ix 0, ix 0)
  let j := r.1
  let k := r.2
  if j.val > e1.val then return (rs, x, r, ix 0, i)
  let nb ← if i.val = start.val ∨ i.val ≤ k.val then do
      let b ← liftS (StringUtil.copyOut s i (j - i))
      discard (wIO b)
      wIO (ps.getD x default).repl.bytes
    else pure (ix 0)
  if k.val < j.val then
    if j.val = e1.val then return (rs, x, r, nb, j)
    let k ← liftS (nextind s j)
    if n.val = count.val then return (rs, x, r, nb, j)
    let rs ← liftS (StringUtil.refresh e1 k (ps.map APair.toPair) rs)
    return (rs, x, r, nb, j)
  else
    let k ← liftS (nextind s k)
    if n.val = count.val then return (rs, x, r, nb, k)
    let rs ← liftS (StringUtil.refresh e1 k (ps.map APair.toPair) rs)
    return (rs, x, r, nb, k)

/-- An element `(region, offset)` of `replacements`. -/
structure Rep where
  region : Region
  offset : JInt64

instance : Inhabited Rep := ⟨⟨(ix 0, ix 0), ix 0⟩⟩

/-- The annotations of an annotated replacement in the form `_insert_annotations!`
takes, `base/strings/annotated_io.jl:265-272`: an `AnnotatedChar`'s annotations get
the region `1:newbytes`. `none` for an unannotated replacement (`_isannotated`). -/
def replAnnots (repl : Repl) (newbytes : JInt64) : Option (List RA) :=
  match repl with
  | .plain _ => none
  | .astr a => some a.anns
  | .achar c => some (c.anns.map (RA.ofAnn (urange (ix 1) newbytes)))

/-- The `while nrep <= count` loop of `replace(out::AnnotatedIOBuffer, ...)`,
`base/strings/annotated_io.jl:248-273`. The fuel is `count`: the loop starts with
`nrep = 1` and increments it on every pass that continues. Returns `bytepos`,
`replacements` and `newannots`. -/
def replLoop (s : JStr) (ps : List APair) (bytestart e1 count : JInt64) :
    Nat → List StringUtil.Rng → JInt64 → JInt64 → List Rep → List RA →
      AM (JInt64 × List Rep × List RA)
  | 0, _, _, bytepos, reps, newannots => pure (bytepos, reps, newannots)
  | fuel + 1, repspans, nrep, bytepos, reps, newannots => do
    if !decide (nrep.val ≤ count.val) then return (bytepos, reps, newannots)
    let (repspans, ridx, xspan, newbytes, bytepos) ←
      replaceOnce s ps bytestart e1 repspans count nrep bytepos
    if xspan.1.val ≥ e1.val then return (bytepos, reps, newannots)
    let nrep := nrep + ix 1
    let xspan ← if !isemptyR xspan then do
        let cu ← liftS (codeunit s xspan.2)
        if cu > 0x80 then do
          let nx ← liftS (nextind s xspan.2)
          pure (urange xspan.1 (nx - ix 1))
        else pure xspan
      else pure xspan
    let drift := (reps.getLast?.map (·.offset)).getD (ix 0)
    let thisrep : Rep := ⟨xspan, drift + newbytes - IOBuffers.rangeLength xspan.1 xspan.2⟩
    let destoff := xspan.1 - ix 1 + drift
    let reps := reps ++ [thisrep]
    match replAnnots (ps.getD ridx default).repl newbytes with
    | none => replLoop s ps bytestart e1 count fuel repspans nrep bytepos reps newannots
    | some annots' =>
      replLoop s ps bytestart e1 count fuel repspans nrep bytepos reps (insertAnns newannots annots' destoff)

/-- `searchsortedlast(replacements, (region = x:x, offset = 0), by = r -> first(r.region))`:
the number of leading replacements with `first(region) ≤ x` (one-based index). -/
def ssLast (reps : List Rep) (x : JInt64) : Nat := (reps.takeWhile fun r => decide (r.region.1.val ≤ x.val)).length

/-- `searchsortedfirst(replacements, (region = x:x, offset = 0), by = ...)`: one plus
the number of leading replacements with `first(region) < x`. -/
def ssFirst (reps : List Rep) (x : JInt64) : Nat :=
  (reps.takeWhile fun r => decide (r.region.1.val < x.val)).length + 1

/-- Checked `replacements[k]` (one-based). -/
def repAt (reps : List Rep) (k : Nat) : SJl Rep :=
  if 1 ≤ k ∧ k ≤ reps.length then .ok (reps.getD (k - 1) default) else .error boundsErr

/-- The "split between replacements" loop, `base/strings/annotated_io.jl:311-323`. -/
def gapLoop (start stop : JInt64) (label : Nat) (value : Val) : Rep → List Rep → List RA
  | _, [] => []
  | prevrep, rep :: rest =>
    let gap := urange (imax start (prevrep.region.2 + ix 1)) (imin stop (rep.region.1 - ix 1))
    let here := if !isemptyR gap then
        let r := urange (gap.1 + prevrep.offset) (gap.2 + prevrep.offset)
        [⟨r.1, r.2, label, value⟩]
      else []
    here ++ gapLoop start stop label value rep rest

/-- The annotations pushed for one annotation of `str`,
`base/strings/annotated_io.jl:288-325`. -/
def placeAnn (reps : List Rep) (a : RA) : SJl (List RA) := do
  let start := a.lo
  let stop := a.hi
  let prioridx := ssLast reps start
  let postidx := ssFirst reps stop
  let priorrep ← repAt reps prioridx
  let postrep ← repAt reps postidx
  if prioridx = postidx ∧ start.val ≥ priorrep.region.1.val ∧ stop.val ≤ priorrep.region.2.val then
    pure []
  else if (postidx : Int) - prioridx ≤ 1 ∧ start.val > priorrep.region.2.val ∧
      stop.val < postrep.region.1.val then
    let r := urange (start + priorrep.offset) (stop + priorrep.offset)
    pure [⟨r.1, r.2, a.label, a.value⟩]
  else
    let lo := max 1 (prioridx - 1)
    let hi := min reps.length (postidx + 1)
    let prevrep ← repAt reps lo
    pure (gapLoop start stop a.label a.value prevrep ((reps.drop (lo - 1)).take (hi + 1 - lo)))

/-- The `for (; region, label, value) in str.annotations` loop. -/
def placeAll (reps : List Rep) : List RA → SJl (List RA)
  | [] => .ok []
  | a :: rest => do
    let h ← placeAnn reps a
    let t ← placeAll reps rest
    pure (h ++ t)

/-- `replace(out::AnnotatedIOBuffer, str::AnnotatedString, pat_f::Pair...; count)`,
`base/strings/annotated_io.jl:240-328`. -/
def replaceAIO (str : AS) (ps : List APair) (count : JInt64) : AM Unit := do
  if count.val = 0 ∨ ps.isEmpty then
    discard (writeW (.str str))
    return
  let (e1, repspans, notfound) ← liftS (StringUtil.replaceInit str.str (ps.map APair.toPair) count)
  if notfound then
    discard (writeW (.str str))
    return
  let out ← get
  let isappending := eofA out
  let bytestart := firstindex str.str
  let reps0 : List Rep := [⟨urange (bytestart - ix 1) (bytestart - ix 1), position out⟩]
  let (bytepos, reps, newannots) ←
    replLoop str.str ps bytestart e1 count count.val.toNat repspans (ix 1) bytestart reps0 []
  let lastoff := (reps.getLast?.map (·.offset)).getD (ix 0)
  let reps := reps ++ [⟨urange e1 (e1 - ix 1), lastoff⟩]
  let rest ← liftS (substring str.str bytepos (lastindex str.str))
  discard (wIO rest.view.bytes)
  let out ← get
  if !isappending then
    setAnns (clearRegion out.anns (urange (reps.headD default).offset (position out)))
  let placed ← liftS (placeAll reps str.anns)
  let out ← get
  setAnns (out.anns ++ placed ++ newannots)

/-- `replace(out::IO, str::AnnotatedString, pat_f::Pair...; count) =
replace(out, str.string, pat_f...; count)`, `base/strings/annotated_io.jl:330-331`:
the plain `replace` of the underlying `String` written to `out` (a byte sink;
`_replace_(io, ...)` writes what `_replace_(str, ...)` returns,
`base/strings/util.jl:1107-1131`). -/
def replaceIO (out : List UInt8) (str : AS) (ps : List APair) (count : JInt64) : SJl (List UInt8) :=
  (StringUtil.replace str.str (ps.map APair.toPair) count).map (out ++ ·)

/-- `replace(str::AnnotatedString, pat_f::Pair...; count)`,
`base/strings/annotated_io.jl:333-338`. `isempty(pat_f) || iszero(count) && return str`
parses as `isempty(pat_f) || (iszero(count) && return str)`. -/
def replaceAS (str : AS) (ps : List APair) (count : JInt64) : Except AErr AS :=
  if !ps.isEmpty ∧ count.val = 0 then .ok str
  else
    match IOBuffers.iobuffer with
    | .error e => .error (.io e)
    | .ok io =>
      match (do replaceAIO str ps count; AIO.seek 0; readASAny).run (ofIO io) with
      | .ok r _ => .ok r
      | .error e _ => .error e

/-- `typemax(Int)`, the default `count`. -/
def intMax : JInt64 := ix (2 ^ 63 - 1)

/-! ## Finders -/

/-- `findnext(RegexAndMatchData(re), str, k)` with the regex model of
`RegexUnicode.Core` (`_findnext_re`, `base/regex.jl:491-512`): a range or
`nothing`. An `ErrorException` from PCRE (not reached in the examples below) is
reported as an `ArgumentError`. -/
def regexFinder (re : RegexUnicode.Core.Regex) (s : JStr) (k : JInt64) : SJl StringUtil.Found :=
  match RegexUnicode.Core.findnextRe re s k with
  | .ok none => .ok .nothing
  | .ok (some (a, b)) => .ok (.range a b)
  | .error (.str e) => .error e
  | .error (.errorException m) => .error (.jl (.argumentError m))

end JuliaLean.StringsCovB.AIOR
