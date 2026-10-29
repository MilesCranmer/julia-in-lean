import JuliaLean.Registry.Types
import JuliaLean.IOBuffers.Model

/-!
Method-specific coverage models for the remaining methods of `base/iobuffer.jl`
at Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.IOCov.IOBufferRemaining

open JuliaLean JuliaLean.Registry
open JuliaLean.IOBuffers

/-! ## Constructors and accessors -/

/-- `_new_generic_iobuffer`, `base/iobuffer.jl:96-107`. -/
def newGeneric (data : List UInt8) (isMem readable writable seekable append : Bool)
    (maxsize : I) : IOBuf := newBuf data isMem readable writable seekable append maxsize

/-- `GenericIOBuffer{T}(...)`, `base/iobuffer.jl:110-130`. -/
def genericTyped (data : DataArg) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr IOBuf :=
  genericIOBuffer data readable writable seekable append maxsize truncate

/-- Untyped `GenericIOBuffer(...)`, `base/iobuffer.jl:134-137`. -/
def genericUntyped (data : DataArg) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr IOBuf :=
  genericTyped data readable writable seekable append maxsize truncate

/-- `GenericIOBuffer(data::Vector{UInt8}, ...)`, `base/iobuffer.jl:141-161`. -/
def genericVector (v : Vec) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr IOBuf :=
  genericIOBuffer (.vec v) readable writable seekable append maxsize truncate

/-- `get_offset`, `base/iobuffer.jl:163`. -/
def getOffsetMethod (io : IOBuf) : I := getOffset io
/-- `get_compacted`, `base/iobuffer.jl:164`. -/
def getCompactedMethod (io : IOBuf) : I := getCompacted io
/-- `StringMemory`, `base/iobuffer.jl:167`. -/
def stringMemoryMethod (n : Int) : Except IOErr (List UInt8) := toI n >>= stringMemory
/-- `StringVector`, `base/iobuffer.jl:168`. -/
def stringVectorMethod (n : Int) : Except IOErr (List UInt8) := stringMemoryMethod n

/-- `IOBuffer(data; ...)`, `base/iobuffer.jl:230-244`. -/
def ioBufferDataMethod (data : DataArg) (read write append truncate : Option Bool)
    (maxsize : Int) : Except IOErr IOBuf := iobufferData data read write append truncate maxsize

/-- `IOBuffer(; ...)`, `base/iobuffer.jl:246-270`. -/
def ioBufferEmptyMethod (read write append truncate : Option Bool) (maxsize : Int)
    (sizehint : Option Int) : Except IOErr IOBuf :=
  iobufferEmpty read write append truncate maxsize sizehint

/-- `PipeBuffer(data; maxsize::Int)`, `base/iobuffer.jl:284-285`. -/
def pipeBufferMethod (data : DataArg) (maxsize : Int) : Except IOErr IOBuf :=
  pipeBuffer data .i64 maxsize

/-- `_truncated_pipebuffer`, `base/iobuffer.jl:289-294`. -/
def truncatedPipeBuffer (data : DataArg) (maxsize : Int) : Except IOErr IOBuf := do
  let buf <- pipeBuffer data .i64 (2 ^ 63 - 1)
  pure { buf with size := getOffset buf, maxsize := i maxsize }

/-- `_similar_data(b::IOBuffer, len)`, `base/iobuffer.jl:297`. -/
def similarDataMethod (b : IOBuf) (len : I) : Except IOErr (List UInt8) :=
  stringMemory len

/-- `copy(b::GenericIOBuffer)`, `base/iobuffer.jl:302-332`. -/
def copyBuffer (b : IOBuf) : Except IOErr IOBuf := do
  if b.reinit then
    let data <- similarData b (i 0)
    genericIOBuffer (if b.isMem then .mem data else .other data) b.readable b.writable
      b.seekable b.append b.maxsize.val false
  else if b.writable then
    let used <- getUsedSpan b
    let compacted := used.1 - getOffset b - i 1
    let len := rangeLength used.1 used.2
    let data0 <- similarData b len
    let data <- copyto data0 (i 1) b.data used.1 len
    let ret <- genericIOBuffer (if b.isMem then .mem data else .other data) b.readable b.writable
      b.seekable b.append b.maxsize.val false
    pure (IOBuf.mk ret.data ret.isMem ret.reinit ret.readable ret.writable ret.seekable
      ret.append len ret.maxsize (b.ptr - used.1 + i 1) (-(getCompacted b) - compacted) b.mark)
  else
    pure (IOBuf.mk b.data b.isMem false b.readable b.writable b.seekable b.append
      (i b.data.length) b.maxsize b.ptr b.oc b.mark)

/-! ## Reading fixed-width values -/

/-- `_throw_not_readable`, `base/iobuffer.jl:344-347`. -/
def throwNotReadableMethod {alpha : Type} : Except IOErr alpha :=
  .error (.jl (.argumentError "read failed, IOBuffer is not readable"))

/-- `unsafe_read!` for an abstract byte vector, `base/iobuffer.jl:361-365`. -/
def unsafeReadAbstract (src : List UInt8) (so : I) (nbytes : Nat) : Except IOErr (List UInt8) :=
  readAt src so nbytes

/-- Dense `unsafe_read!`, `base/iobuffer.jl:375-378`. -/
def unsafeReadDense (src : List UInt8) (so : I) (nbytes : Nat) : Except IOErr (List UInt8) :=
  readAt src so nbytes

/-- Little-endian value assembled by `load_from_array`, `base/iobuffer.jl:394-404`. -/
def loadFromArray (data : List UInt8) (start nbytes : Nat) : Nat :=
  (List.range nbytes).foldl (fun x k => x ||| ((data.getD (start - 1 + k) 0).toNat <<< (8 * k))) 0

/-- Generic-vector `peek(from, T::MultiByteBitNumberType)`, `base/iobuffer.jl:406-414`. -/
def peekMultiGeneric (src : IOBuf) (nbytes : Nat) : Except IOErr Nat :=
  if !src.readable then throwNotReadableMethod
  else if nbytes > (bytesavailable src).val then .error .eofError
  else .ok (loadFromArray src.data src.ptr.val.toNat nbytes)

/-- Dense-vector `peek(from, T::MultiByteBitNumberType)`, `base/iobuffer.jl:418-430`. -/
def peekMultiDense (src : IOBuf) (nbytes : Nat) : Except IOErr (List UInt8) :=
  match (peekT nbytes).run src with
  | .ok x _ => .ok x
  | .error e _ => .error e

/-- `read(from, T::MultiByteBitNumberType)`, `base/iobuffer.jl:432-436`. -/
def readMulti (src : IOBuf) (nbytes : Nat) : EStateM.Result IOErr IOBuf (List UInt8) :=
  (readT nbytes).run src

/-- `read(from, ::Type{Ptr{T}})`, `base/iobuffer.jl:458`. -/
def readPtrMethod (src : IOBuf) : EStateM.Result IOErr IOBuf (List UInt8) :=
  (readT 8).run src

/-- `isreadable(io::GenericIOBuffer)`, `base/iobuffer.jl:460`. -/
def isreadableMethod (io : IOBuf) : Bool := io.readable
/-- `iswritable(io::GenericIOBuffer)`, `base/iobuffer.jl:461`. -/
def iswritableMethod (io : IOBuf) : Bool := io.writable

/-! ## Seeking and room management -/

/-- `skip(io, n::Int)`, `base/iobuffer.jl:479-494`. -/
def skipIntMethod (io : IOBuf) (n : Int) : EStateM.Result IOErr IOBuf Unit :=
  (skip n).run io
/-- `translate_seek_position`, `base/iobuffer.jl:500-510`. -/
def translateSeekMethod (io : IOBuf) (n : I) : I := translateSeekPosition io n
/-- `seek(io, n::Int)`, `base/iobuffer.jl:512-524`. -/
def seekIntMethod (io : IOBuf) (n : I) : EStateM.Result IOErr IOBuf Unit := (seek n).run io
/-- `seekend`, `base/iobuffer.jl:526-529`. -/
def seekendMethod (io : IOBuf) : EStateM.Result IOErr IOBuf Unit := seekend.run io
/-- `ensureroom(io, nshort::Int)`, `base/iobuffer.jl:597`. -/
def ensureroomInt (io : IOBuf) (nshort : Int) : EStateM.Result IOErr IOBuf Unit :=
  (ensureroom (u nshort)).run io
/-- `ensureroom(io, nshort::UInt)`, `base/iobuffer.jl:599-615`. -/
def ensureroomUInt (io : IOBuf) (nshort : U) : EStateM.Result IOErr IOBuf Unit :=
  (ensureroom nshort).run io
/-- `ensureroom_reallocate`, `base/iobuffer.jl:618-624`. -/
def ensureroomReallocateMethod (io : IOBuf) (nshort : U) : EStateM.Result IOErr IOBuf Unit :=
  (ensureroomReallocate nshort).run io

/-! ## Close and take -/

/-- `close`, `base/iobuffer.jl:698-711`. -/
def closeMethod (io : IOBuf) : EStateM.Result IOErr IOBuf Unit := close.run io
/-- `isopen`, `base/iobuffer.jl:713`. -/
def isopenMethod (io : IOBuf) : Bool :=
  io.readable || io.writable || io.seekable || (bytesavailable io).val > 0
/-- Generic `take!`, `base/iobuffer.jl:731-753`. -/
def takeGeneric (io : IOBuf) : EStateM.Result IOErr IOBuf (List UInt8) := take.run io

/-- `unsafe_takestring!`, `base/iobuffer.jl:795-809`, as returned bytes. -/
def unsafeTakestring (io : IOBuf) : Except IOErr (List UInt8) := do
  let used <- getUsedSpan io
  let nbytes := rangeLength used.1 used.2
  if nbytes.val = 0 then pure []
  else pure (slice io.data used.1.val used.2.val)

/-- Generic `takestring!`, `base/iobuffer.jl:862`. -/
def takestringGeneric (io : IOBuf) : EStateM.Result IOErr IOBuf (List UInt8) := take.run io

/-- `_unsafe_take!`, `base/iobuffer.jl:876-884`. -/
def unsafeTake (io : IOBuf) : List UInt8 :=
  let offset := getOffset io
  slice io.data (offset.val + 1) io.size.val

/-! ## Transfer and byte operations -/

/-- `write(to::IO, from::GenericIOBuffer)`, `base/iobuffer.jl:886-897`. -/
def writeFromBuffer (to src : IOBuf) : Except IOErr (I × IOBuf × IOBuf) := do
  if to = src then .error (.jl (.argumentError "Writing all content fron an IOBuffer into itself in invalid"))
  else if !src.readable then throwNotReadableMethod
  else
    let bytes <- pending src
    match (unsafeWrite bytes).run to with
    | .error e to' => .error e
    | .ok written to' => .ok (written, to', { src with ptr := src.size + i 1 })

/-- Abstract-vector `_unsafe_write`, `base/iobuffer.jl:923-928`. -/
def unsafeWriteAbstract (data : List UInt8) (start : I) (bytes : List UInt8) : Except IOErr (List UInt8) :=
  writeAt false data start bytes
/-- Dense-vector `_unsafe_write`, `base/iobuffer.jl:930-946`. -/
def unsafeWriteDense (data : List UInt8) (start : I) (bytes : List UInt8) : Except IOErr (List UInt8) :=
  writeAt true data start bytes
/-- `write(to::GenericIOBuffer, a::UInt8)`, `base/iobuffer.jl:948-963`. -/
def writeByteMethod (io : IOBuf) (a : UInt8) : EStateM.Result IOErr IOBuf I :=
  (writeByte a).run io
/-- Default-argument `readbytes!`, `base/iobuffer.jl:965`. -/
def readbytesConvert (io : IOBuf) (nb : Int) : EStateM.Result IOErr IOBuf (I × List UInt8) :=
  (readbytes (i nb)).run io
/-- `readbytes!(..., nb::Int)`, `base/iobuffer.jl:967-976`. -/
def readbytesInt (io : IOBuf) (nb : I) : EStateM.Result IOErr IOBuf (I × List UInt8) :=
  (readbytes nb).run io
/-- `readavailable`, `base/iobuffer.jl:980`. -/
def readavailableMethod (io : IOBuf) : EStateM.Result IOErr IOBuf (List UInt8) := readAll.run io
/-- `read(io, nb::Integer)`, `base/iobuffer.jl:982`. -/
def readCountMethod (io : IOBuf) (nb : I) : EStateM.Result IOErr IOBuf (List UInt8) :=
  (readN nb).run io

/-! ## Line and checksum methods -/

/-- `copyline(out::GenericIOBuffer, s::IO)`, `base/iobuffer.jl:1010-1055`.
`line` is the result of the source `copyuntil(..., keep=true)` call. -/
def copylineGenericOut (out : IOBuf) (line : List UInt8) (keep : Bool) :
    EStateM.Result IOErr IOBuf Unit := (copylineFrom line keep).run out

/-- `copyline(out::IO, io::GenericIOBuffer)`, `base/iobuffer.jl:1079`. -/
def copylineGenericIn (io : IOBuf) (keep : Bool) : EStateM.Result IOErr IOBuf (List UInt8) :=
  (readline keep).run io
/-- `copyline(out::GenericIOBuffer, io::GenericIOBuffer)`, `base/iobuffer.jl:1080`. -/
def copylineGenericBoth (out io : IOBuf) (keep : Bool) :
    Except IOErr (IOBuf × IOBuf) :=
  match (readline keep).run io with
  | .error e io' => .error e
  | .ok line io' =>
      match (unsafeWrite line).run out with
      | .error e _ => .error e
      | .ok _ out' => .ok (out', io')

/-- `_crc32c(io, nb, crc)`, `base/iobuffer.jl:1084-1092`. -/
def crc32cCount (crcFn : List UInt8 -> UInt32 -> UInt32) (io : IOBuf)
    (nb : Int) (crc : UInt32) : Except IOErr (UInt32 × IOBuf) := do
  if nb < 0 then .error (.jl (.argumentError "number of bytes to checksum must be >= 0"))
  else if !io.readable then throwNotReadableMethod
  else
    let n := min nb (bytesavailable io).val
    if n = 0 then pure (crc, io)
    else
      let bytes := slice io.data io.ptr.val (io.ptr.val + n - 1)
      pure (crcFn bytes crc, { io with ptr := io.ptr + i n })

/-- `_crc32c(io, crc)`, `base/iobuffer.jl:1093`. -/
def crc32cAll (crcFn : List UInt8 -> UInt32 -> UInt32) (io : IOBuf) (crc : UInt32) :
    Except IOErr (UInt32 × IOBuf) := crc32cCount crcFn io (bytesavailable io).val crc

/-! ## Properties -/

def NewGenericFields : Prop := forall d m r w s a z,
  newGeneric d m r w s a z = newBuf d m r w s a z
theorem newGenericFields : NewGenericFields := by
  unfold NewGenericFields
  intros
  rfl

def GenericConstructors : Prop := forall d r w s a z t,
  genericTyped d r w s a z t = genericIOBuffer d r w s a z t /\
  genericUntyped d r w s a z t = genericTyped d r w s a z t
theorem genericConstructors : GenericConstructors := by simp [GenericConstructors, genericTyped, genericUntyped]

def VectorConstructor : Prop := forall v r w s a z t,
  genericVector v r w s a z t = genericIOBuffer (.vec v) r w s a z t
theorem vectorConstructor : VectorConstructor := by simp [VectorConstructor, genericVector]

def OffsetAccessors : Prop := forall io,
  getOffsetMethod io = imax (i 0) io.oc /\ getCompactedMethod io = imax (i 0) (-io.oc)
theorem offsetAccessors : OffsetAccessors := by simp [OffsetAccessors, getOffsetMethod, getCompactedMethod, getOffset, getCompacted]

def StringAllocators : Prop := forall n,
  stringVectorMethod n = stringMemoryMethod n
theorem stringAllocators : StringAllocators := by intro; rfl

def PublicConstructors : Prop := forall d r w a t z h,
  ioBufferDataMethod d r w a t z = iobufferData d r w a t z /\
  ioBufferEmptyMethod r w a t z h = iobufferEmpty r w a t z h /\
  pipeBufferMethod d z = pipeBuffer d .i64 z
theorem publicConstructors : PublicConstructors := by
  simp [PublicConstructors, ioBufferDataMethod, ioBufferEmptyMethod, pipeBufferMethod]

def TruncatedPipeCorrect : Prop := forall d z,
  truncatedPipeBuffer d z = do
    let buf <- pipeBuffer d .i64 (2 ^ 63 - 1)
    pure { buf with size := getOffset buf, maxsize := i z }
theorem truncatedPipeCorrect : TruncatedPipeCorrect := by
  unfold TruncatedPipeCorrect
  intros
  rfl

def SimilarDataCorrect : Prop := forall b n, similarDataMethod b n = stringMemory n
theorem similarDataCorrect : SimilarDataCorrect := by simp [SimilarDataCorrect, similarDataMethod]

def CopyReadonlyFields : Prop := forall b r,
  b.reinit = false -> b.writable = false -> copyBuffer b = .ok r ->
  r.data = b.data /\ r.ptr = b.ptr /\ r.mark = b.mark /\ r.oc = b.oc
theorem copyReadonlyFields : CopyReadonlyFields := by
  unfold CopyReadonlyFields copyBuffer
  intros b r hr hw h
  simp [hr, hw] at h
  change Except.ok _ = Except.ok r at h
  injection h with h
  subst r
  simp

def ThrowNotReadable : Prop := forall alpha,
  (throwNotReadableMethod : Except IOErr alpha) = .error (.jl (.argumentError "read failed, IOBuffer is not readable"))
theorem throwNotReadable : ThrowNotReadable := by intro; rfl

def UnsafeReadMethods : Prop := forall d k n,
  unsafeReadAbstract d k n = readAt d k n /\ unsafeReadDense d k n = readAt d k n
theorem unsafeReadMethods : UnsafeReadMethods := by
  simp [UnsafeReadMethods, unsafeReadAbstract, unsafeReadDense]

def LoadFromArrayLittleEndian : Prop := forall d start n,
  loadFromArray d start n = (List.range n).foldl
    (fun x k => x ||| ((d.getD (start - 1 + k) 0).toNat <<< (8 * k))) 0
theorem loadFromArrayLittleEndian : LoadFromArrayLittleEndian := by
  simp [LoadFromArrayLittleEndian, loadFromArray]

def PeekMethodsDoNotAdvance : Prop := forall io n,
  peekMultiDense io n = match (peekT n).run io with
    | .ok x _ => .ok x
    | .error e _ => .error e
theorem peekMethodsDoNotAdvance : PeekMethodsDoNotAdvance := by
  unfold PeekMethodsDoNotAdvance
  intros
  rfl

def ReadMultiAdvances : Prop := forall io n,
  readMulti io n = (readT n).run io
theorem readMultiAdvances : ReadMultiAdvances := by
  unfold ReadMultiAdvances
  intros
  rfl

def PtrReadIsUIntRead : Prop := forall io, readPtrMethod io = (readT 8).run io
theorem ptrReadIsUIntRead : PtrReadIsUIntRead := by intro; rfl

def ReadWriteFlags : Prop := forall io,
  isreadableMethod io = io.readable /\ iswritableMethod io = io.writable
theorem readWriteFlags : ReadWriteFlags := by
  simp [ReadWriteFlags, isreadableMethod, iswritableMethod]

def SeekMethodsCorrect : Prop := forall io n,
  skipIntMethod io n = (skip n).run io /\
  translateSeekMethod io (i n) = translateSeekPosition io (i n) /\
  seekIntMethod io (i n) = (seek (i n)).run io /\
  seekendMethod io = seekend.run io
theorem seekMethodsCorrect : SeekMethodsCorrect := by
  simp [SeekMethodsCorrect, skipIntMethod, translateSeekMethod, seekIntMethod, seekendMethod]

def EnsureRoomMethods : Prop := forall io n,
  ensureroomInt io n.val = (ensureroom (u n.val)).run io /\
  ensureroomUInt io n = (ensureroom n).run io /\
  ensureroomReallocateMethod io n = (ensureroomReallocate n).run io
theorem ensureRoomMethods : EnsureRoomMethods := by
  simp [EnsureRoomMethods, ensureroomInt, ensureroomUInt, ensureroomReallocateMethod]

def CloseMethodCorrect : Prop := forall io, closeMethod io = close.run io
theorem closeMethodCorrect : CloseMethodCorrect := by simp [CloseMethodCorrect, closeMethod]

def IsopenCorrect : Prop := forall io,
  isopenMethod io = (io.readable || io.writable || io.seekable || (bytesavailable io).val > 0)
theorem isopenCorrect : IsopenCorrect := by simp [IsopenCorrect, isopenMethod]

def TakeMethodsCorrect : Prop := forall io,
  takeGeneric io = take.run io /\ takestringGeneric io = take.run io
theorem takeMethodsCorrect : TakeMethodsCorrect := by
  simp [TakeMethodsCorrect, takeGeneric, takestringGeneric]

def UnsafeTakeReturnsUsed : Prop := forall io,
  unsafeTake io = slice io.data ((getOffset io).val + 1) io.size.val /\
  unsafeTakestring io = do
    let used <- getUsedSpan io
    let nbytes := rangeLength used.1 used.2
    if nbytes.val = 0 then pure [] else pure (slice io.data used.1.val used.2.val)
theorem unsafeTakeReturnsUsed : UnsafeTakeReturnsUsed := by
  simp [UnsafeTakeReturnsUsed, unsafeTake, unsafeTakestring]

def WriteFromConsumes : Prop := forall to src,
  writeFromBuffer to src = do
    if to = src then .error (.jl (.argumentError "Writing all content fron an IOBuffer into itself in invalid"))
    else if !src.readable then throwNotReadableMethod
    else
      let bytes <- pending src
      match (unsafeWrite bytes).run to with
      | .error e _ => .error e
      | .ok written to' => .ok (written, to', { src with ptr := src.size + i 1 })
theorem writeFromConsumes : WriteFromConsumes := by
  unfold WriteFromConsumes
  intros
  rfl

def UnsafeWriteMethods : Prop := forall d k bs,
  unsafeWriteAbstract d k bs = writeAt false d k bs /\
  unsafeWriteDense d k bs = writeAt true d k bs
theorem unsafeWriteMethods : UnsafeWriteMethods := by
  simp [UnsafeWriteMethods, unsafeWriteAbstract, unsafeWriteDense]

def ByteReadWriteMethods : Prop := forall io a n,
  writeByteMethod io a = (writeByte a).run io /\
  readbytesConvert io n.val = (readbytes (i n.val)).run io /\
  readbytesInt io n = (readbytes n).run io /\
  readavailableMethod io = readAll.run io /\
  readCountMethod io n = (readN n).run io
theorem byteReadWriteMethods : ByteReadWriteMethods := by
  simp [ByteReadWriteMethods, writeByteMethod, readbytesConvert, readbytesInt,
    readavailableMethod, readCountMethod]

def CopylineMethods : Prop := forall out io line keep,
  copylineGenericOut out line keep = (copylineFrom line keep).run out /\
  copylineGenericIn io keep = (readline keep).run io /\
  copylineGenericBoth out io keep =
    match (readline keep).run io with
    | .error e _ => .error e
    | .ok line io' =>
        match (unsafeWrite line).run out with
        | .error e _ => .error e
        | .ok _ out' => .ok (out', io')
theorem copylineMethods : CopylineMethods := by
  simp [CopylineMethods, copylineGenericOut, copylineGenericIn, copylineGenericBoth]

def CrcDefaultUsesAvailable : Prop := forall f io crc,
  crc32cAll f io crc = crc32cCount f io (bytesavailable io).val crc
theorem crcDefaultUsesAvailable : CrcDefaultUsesAvailable := by
  simp [CrcDefaultUsesAvailable, crc32cAll]

/-! ## Registry -/

def entries : List Entry := []

end JuliaLean.IOCov.IOBufferRemaining
