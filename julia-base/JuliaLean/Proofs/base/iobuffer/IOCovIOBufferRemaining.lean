import JuliaLean.Registry.Types
import JuliaLean.base.iobuffer

/-!
Method-specific coverage models for the remaining methods of `base/iobuffer.jl`
at Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.IOCov.IOBufferRemaining

open JuliaLean JuliaLean.Registry
open JuliaLean.IOBuffers

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
  unfold CopylineMethods
  intros
  exact ⟨rfl, rfl, rfl⟩

def CrcDefaultUsesAvailable : Prop := forall f io crc,
  crc32cAll f io crc = crc32cCount f io (bytesavailable io).val crc
theorem crcDefaultUsesAvailable : CrcDefaultUsesAvailable := by
  simp [CrcDefaultUsesAvailable, crc32cAll]

/-! ## Registry -/

def entries : List Entry := []

end JuliaLean.IOCov.IOBufferRemaining
