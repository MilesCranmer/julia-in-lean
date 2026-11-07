import JuliaLean.Proofs.base.filesystem
import JuliaLean.base.stat

namespace JuliaLean.Files.Coverage

open JuliaLean.Files

def FileLifecycleTransferBehavior : Prop :=
  (∀ handle, newFile handle = ⟨true, handle⟩) ∧
  (∀ file, rawHandle file = file.handle) ∧
  (∀ file, setupStdio file = (file, false)) ∧
  (∀ handle, openFile handle =
    if handle < 0 then .error .io ⟨false, -1⟩ else .ok (newFile handle)) ∧
  (∀ file, checkOpen file = if file.isOpen then .ok () else .error .argument ()) ∧
  (∀ file, closeHandle file = ⟨false, -1⟩) ∧
  (∀ file, closeFile file = { file with isOpen := false }) ∧
  (∀ file reply, tryLock file reply =
    if !file.isOpen then .error .closed (false, file)
    else match reply with
      | .acquired => .ok (true, file)
      | .unavailable => .ok (false, file)
      | .failure => .error .io (false, file)) ∧
  (∀ maxChunk offset bytes, sendChunks maxChunk offset bytes =
    if maxChunk == 0 || bytes == 0 then []
    else let count := (bytes + maxChunk - 1) / maxChunk
      (List.range count).map fun index =>
        (offset + index * maxChunk, min maxChunk (bytes - index * maxChunk))) ∧
  (∀ data size, truncateData data size =
    if size ≤ data.length then data.take size
    else data ++ List.replicate (size - data.length) 0)

theorem fileLifecycleTransferBehavior : FileLifecycleTransferBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def FileReadAccessBehavior : Prop :=
  (∀ file, seekEnd file = { file with position := file.data.length }) ∧
  (∀ file returnedPosition, seekResult file returnedPosition =
    if returnedPosition == -1 then .error .io file
    else .ok { file with position := returnedPosition.toNat }) ∧
  (∀ file, bytesavailable file = file.data.length - file.position) ∧
  (∀ file, (bytesavailable file == 0) = (file.data.length - file.position == 0)) ∧
  (∀ first leading rest bytes, charReadBytes first leading rest bytes =
    first :: if 2 ≤ leading ∧ leading ≤ 4 then continuationTail rest bytes else []) ∧
  (∀ code, accessAllowed code = (code == 0))

theorem fileReadAccessBehavior : FileReadAccessBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-! ### Method-specific `base/filesystem.jl` mirrors -/

def FileLifecycleMethods : Prop :=
  (uvFsReqCleanupMethod = [.cleanupRequest]) ∧
  (∀ handle, fileFromHandleMethod handle = ⟨true, handle⟩) ∧
  (∀ converted, fileFromRawFdMethod converted = fileFromHandleMethod converted) ∧
  (∀ file, rawhandleMethod file = file.handle) ∧
  (∀ file, setupStdioMethod file = (file, false)) ∧
  (∀ flags mode code handle, openFsMethod flags mode code handle =
    let events := [.allocateRequest, .openCall flags mode, .cleanupRequest, .freeRequest]
    if code < 0 then (events, .error .io ⟨false, -1⟩)
    else (events, .ok ⟨true, handle⟩)) ∧
  (∀ file, isopenMethod file = file.isOpen) ∧
  (∀ file, checkOpenMethod file = if file.isOpen then .ok () else .error .argument ()) ∧
  (∀ file code, closeFsMethod file code =
    if !file.isOpen then ([], .ok file)
    else let closed : HandleFile := ⟨false, -1⟩
      if code < 0 then ([.closeCall], .error .io closed) else ([.closeCall], .ok closed))

theorem fileLifecycleMethods : FileLifecycleMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def FileLockMethods : Prop :=
  (∀ file shared observation, trylockfileMethod file shared observation =
    if !file.isOpen then ([], .error .argument false)
    else match observation with
      | .success => ([.lockCall shared], .ok true)
      | .unavailable => ([.lockCall shared], .ok false)
      | .failure => ([.lockCall shared], .error .io false)) ∧
  (∀ file observation, unlockfileMethod file observation =
    if !file.isOpen then ([], .error .argument ())
    else match observation with
      | .failure => ([.unlockCall], .error .io ())
      | _ => ([.unlockCall], .ok ())) ∧
  (∀ file, closewriteMethod file = ())

theorem fileLockMethods : FileLockMethods := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def FileWriteMethods : Prop :=
  (∀ dstOpen srcOpen maxChunk offset bytes, sendfileMethod dstOpen srcOpen maxChunk offset bytes =
    if !dstOpen || !srcOpen then .error .argument []
    else .ok ((sendChunks maxChunk offset bytes).map fun pair => .sendfileCall pair.1 pair.2)) ∧
  (∀ file count offset code, unsafeWriteMethod file count offset code =
    if !file.isOpen then ([], .error .closed 0)
    else if code < 0 then ([.writeCall count offset], .error .io 0)
    else ([.writeCall count offset], .ok count)) ∧
  (∀ file byte code, writeByteMethod file byte code = unsafeWriteMethod file 1 (-1) code) ∧
  (∀ file size code, truncateMethod file size code =
    if !file.isOpen then ([], .error .closed file)
    else if code < 0 then ([.allocateRequest, .truncateCall size, .freeRequest], .error .io file)
    else ([.allocateRequest, .truncateCall size, .freeRequest], .ok file)) ∧
  (∀ file code, futimeMethod file code =
    if !file.isOpen then ([], .error .closed file)
    else if code < 0 then ([.allocateRequest, .futimeCall, .freeRequest], .error .io file)
    else ([.allocateRequest, .futimeCall, .freeRequest], .ok file))

theorem fileWriteMethods : FileWriteMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def FileScalarReadMethods : Prop :=
  (∀ file code byte, readUInt8Method file code byte =
    if !file.isOpen then ([], .error .closed 0)
    else if code < 0 then ([.readCall 1], .error .io 0)
    else if code < 1 then ([.readCall 1], .error .eof 0)
    else ([.readCall 1], .ok byte)) ∧
  (∀ file first leading following, readCharMethod file first leading following =
    if !file.isOpen then .error .closed []
    else .ok (charReadBytes first leading (4 - leading) following)) ∧
  (∀ decoded, readAbstractCharMethod decoded = decoded) ∧
  (∀ file requested returned code, unsafeReadMethod file requested returned code =
    if !file.isOpen then ([], .error .closed ())
    else if code < 0 then ([.readCall requested], .error .io ())
    else if returned != requested then ([.readCall requested], .error .eof ())
    else ([.readCall requested], .ok ()))

theorem fileScalarReadMethods : FileScalarReadMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def FileBulkReadMethods : Prop :=
  (∀ file, bytesavailableMethod file = file.data.length - file.position) ∧
  (∀ file, eofMethod file = (bytesavailableMethod file == 0)) ∧
  (∀ file bufferLength requested returned, readbytesMethod file bufferLength requested returned =
    if !file.isOpen then .error .closed (bufferLength, 0)
    else let count := min requested (bytesavailableMethod file)
      let resized := max bufferLength count
      .ok (resized, min returned count)) ∧
  (∀ file, readAllMethod file = bytesavailableMethod file) ∧
  (∀ file, readavailableMethod file = readAllMethod file) ∧
  (∀ file requested, readCountMethod file requested = min requested (bytesavailableMethod file))

theorem fileBulkReadMethods : FileBulkReadMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def statFileMethod (statResult : FullStat) : FullStat := statResult
def FileSeekDescriptorMethods : Prop :=
  (∀ file requested returned, seekMethod file requested returned =
    if returned == -1 then ([.seekSet requested], .error .io file)
    else ([.seekSet requested], .ok { file with position := returned.toNat })) ∧
  (∀ file returned, seekendMethod file returned =
    if returned == -1 then ([.seekEnd], .error .io file)
    else ([.seekEnd], .ok { file with position := returned.toNat })) ∧
  (∀ file amount returned, skipMethod file amount returned =
    if returned == -1 then ([.seekCurrent amount], .error .io file)
    else ([.seekCurrent amount], .ok { file with position := returned.toNat })) ∧
  (∀ file returned, positionMethod file returned =
    if !file.isOpen then .error .closed file.position
    else if returned == -1 then .error .io file.position else .ok returned.toNat) ∧
  (∀ file, fdMethod file = file.handle) ∧
  (∀ statResult, statFileMethod statResult = statResult) ∧
  (∀ file code, touchFileMethod file code =
    if code != 0 then ([.touchCall], .error .io file) else ([.touchCall], .ok file))

theorem fileSeekDescriptorMethods : FileSeekDescriptorMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def FileAccessMethods : Prop :=
  (∀ mode code, accessMethod mode code = ([.accessCall mode], code == 0)) ∧
  (∀ result, accessAbstractStringMethod result = result)

theorem fileAccessMethods : FileAccessMethods := by
  constructor <;> intros <;> rfl

end JuliaLean.Files.Coverage
