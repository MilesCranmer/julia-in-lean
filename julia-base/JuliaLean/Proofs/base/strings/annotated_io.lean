-- No Proofs/base/strings/annotated_io.lean file exists in the supplied tree.
-- Import the source-mirrored subjects directly.
import JuliaLean.base.strings.annotated_io
import JuliaLean.base.iobuffer
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.strings.annotated_io.Round1

/-
Public plumbing with no independent statement (review check 2).

`annotations(::AnnotatedIOBuffer)` at base/strings/annotated_io.jl:30 is the
exact stored-vector projection, mirrored by annotated_io.annotations:190.
A standalone equation saying that it returns `io.annotations` merely unfolds
the definition (check 3c). The shared-vector identity and its consequences for
ordered observations, aliases and later mutation remain in the full retained
`stringscovb-aio-forward` contract and the public transfer/mutation contracts.
No initialized-slot or in-range-region invariant is assumed. This method is
therefore nothing-to-promise on its own; it has no new registry property.

The `function printstyled end` declaration at Julia line 342 supplies no
method and is excluded from the method inventory.
-/

open JuliaLean
open JuliaLean.base

/-- Concrete mutable IOBuffer headers and an arbitrary surrounding heap. The
surrounding heap can contain arbitrary annotation vectors, undefined annotation
slots, and aliases. Neither the subject nor its read-at-end observer reads or
mutates that heap. Each BufferState is the existing IOBuffer model's complete
header and memory-content observation; all permission, append, mark, offset,
reinitialization, and size-limit fields remain present. -/
structure CursorWorld (Metadata : Type) where
  buffers : List iobuffer.BufferState
  metadata : Metadata

def cursorGet {Metadata : Type} (handle : Nat) :
    io.M (CursorWorld Metadata) iobuffer.BufferState := do
  match (← io.getWorld).buffers[handle]? with
  | some buffer => pure buffer
  | none => throw (.jl .boundsError)

def cursorSet {Metadata : Type} (handle : Nat) (buffer : iobuffer.BufferState) :
    io.M (CursorWorld Metadata) Unit := do
  let world ← io.getWorld
  if handle < world.buffers.length then
    io.setWorld { world with buffers := world.buffers.set handle buffer }
  else throw (.jl .boundsError)

/-- The invoked cursor operation is the installed source model of
base/iobuffer.jl:526-529. Error transport retains the complete mutated state. -/
def cursorSeekEnd {Metadata : Type} (handle : Nat) : io.M (CursorWorld Metadata) Unit :=
  iobuffer.liftBufferIO cursorGet cursorSet handle
    (iobuffer.source_seekend iobuffer.bufferAccess ())

/-- The observer calls the installed byte-read source body, with the existing
getUnchecked byte-content primitive. On every extent in the property below,
source_read_uint8 returns from its readability or exhaustion check before this
byte-content callback is reached. It is not an assumed EOF callback and this
adapter does not claim a binding for general memory reads, writes, or allocation.
Readability and exhaustion checks are performed by source_read_uint8 itself. -/
def cursorReadByte {Metadata : Type} (handle : Nat) :
    io.M (CursorWorld Metadata) (JInt .u8) :=
  iobuffer.liftBufferIO cursorGet cursorSet handle
    (iobuffer.source_read_uint8 iobuffer.bufferAccess
      (fun bytes index => do
        let byte ← iobuffer.lift (iobuffer.getUnchecked bytes index)
        pure (JInt.wrap .u8 byte.toNat)) ())

/-- Only newBuffer and copy are structural padding: the property universally
quantifies them without any laws, and neither can be invoked by seekend,
position, or the byte-read observer. Every field actually invoked here calls
the existing source model. This is not a proposed binding for constructors,
copy, or any byte-write/growth operation. -/
def cursorOps {Metadata : Type}
    (newBuffer : io.M (CursorWorld Metadata) Nat)
    (copy : Nat → io.M (CursorWorld Metadata) Nat) :
    strings.annotated_io.BufferOps (CursorWorld Metadata) Nat where
  newBuffer := newBuffer
  position := fun handle => do pure (iobuffer.source_position (← cursorGet handle))
  eof := fun handle => do pure (iobuffer.source_eof (← cursorGet handle))
  filesize := fun handle => do pure (iobuffer.source_filesize (← cursorGet handle))
  seekend := cursorSeekEnd
  copy := copy

/-- A live IOBuffer header's physical byte extent is nonnegative and lies in its
Memory{UInt8} allocation. This is the runtime size/type invariant, not a writable,
readable, seekable, append-mode, zero-offset, or success-only restriction.
Source field invariant: base/iobuffer.jl:55-58. Native address-width memory
bound: source excerpt in JuliaLean/src/genericmemory_c.lean:148-154. -/
def CursorBufferExtent (buffer : iobuffer.BufferState) : Prop :=
  buffer.isMemory = true ∧
  buffer.data.length < 2 ^ 63 - 1 ∧
  0 ≤ buffer.size.val ∧ buffer.size.val ≤ buffer.data.length

/-- Seeking an annotated buffer to its end leaves bytes and every annotation
unchanged, reports no remaining bytes and the final cursor position, and makes
the next byte read report EOF (or the existing permission error if unreadable).
It accepts nonseekable, closed, readonly, append, marked, offset, and reinitialized
IOBuffer states subject only to a live physical extent. The underlying source
read determines its own error; the statement does not assume that result.

Julia source: base/strings/annotated_io.jl:24,26;
base/iobuffer.jl:438-448,467,470-473,526-529,691
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/iostream.jl:187-190; base/io.jl:208-227,237-243;
base/iobuffer.jl:173-180,344-347
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def SeekEndExhaustsAndFrames : Prop :=
  ∀ (Metadata Ref : Type) (before : CursorWorld Metadata)
    (wrapped : strings.annotated_io.AnnotatedIOBuffer Nat Ref)
    (buffer : iobuffer.BufferState)
    (newBuffer : io.M (CursorWorld Metadata) Nat)
    (copy : Nat → io.M (CursorWorld Metadata) Nat),
    before.buffers[wrapped.io]? = some buffer →
    CursorBufferExtent buffer →
    let ops := cursorOps newBuffer copy
    let atEnd := { buffer with ptr := buffer.size + iobuffer.i 1 }
    ∃ after : CursorWorld Metadata,
      strings.annotated_io.seekend ops wrapped before = some (.ok (wrapped, after)) ∧
      after.buffers[wrapped.io]? = some atEnd ∧
      after.metadata = before.metadata ∧
      after.buffers.length = before.buffers.length ∧
      (∀ other, other < before.buffers.length → other ≠ wrapped.io →
        after.buffers[other]? = before.buffers[other]?) ∧
      iobuffer.source_eof atEnd = true ∧
      iobuffer.source_bytesavailable atEnd = iobuffer.i 0 ∧
      strings.annotated_io.position ops wrapped after =
        some (.ok (buffer.size - buffer.offset, after)) ∧
      cursorReadByte wrapped.io after = some (.error
        ((if buffer.readable then io.Error.eofError
          else io.Error.jl (.argumentError "read failed, IOBuffer is not readable")), after))

end JuliaLean.Proofs.base.strings.annotated_io.Round1

namespace JuliaLean.Proofs.base.strings.annotated_io

open JuliaLean.Registry

end JuliaLean.Proofs.base.strings.annotated_io

namespace JuliaLean.ChatGPT.Batch4.Group18
open JuliaLean JuliaLean.base
open JuliaLean.Proofs.base.strings.annotated_io.Round1

theorem aio_i_val_one : (iobuffer.i 1).val = 1 := by decide
theorem aio_i_val_zero : (iobuffer.i 0).val = 0 := by decide

theorem aio_add_val (a b : JInt64) :
    (a + b).val = wrapInt .i64 (a.val + b.val) := rfl

theorem aio_sub_val (a b : JInt64) :
    (a - b).val = wrapInt .i64 (a.val - b.val) := rfl

theorem aio_add_one_sub_one (a : JInt64) :
    a + iobuffer.i 1 - iobuffer.i 1 = a := by
  apply Subtype.ext
  rw [aio_sub_val, aio_add_val, aio_i_val_one]
  have ha := a.property
  simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at ha ⊢
  omega

theorem aio_available_end (a : JInt64) :
    a - (a + iobuffer.i 1) + iobuffer.i 1 = iobuffer.i 0 := by
  apply Subtype.ext
  rw [aio_add_val, aio_sub_val, aio_add_val, aio_i_val_one, aio_i_val_zero]
  have ha := a.property
  simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at ha ⊢
  omega

theorem aio_position_end (a b : JInt64) :
    a + iobuffer.i 1 - b - iobuffer.i 1 = a - b := by
  apply Subtype.ext
  rw [aio_sub_val, aio_sub_val, aio_sub_val, aio_add_val, aio_i_val_one]
  have ha := a.property
  have hb := b.property
  simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at ha hb ⊢
  omega

theorem aio_size_succ (buffer : iobuffer.BufferState)
    (h : CursorBufferExtent buffer) :
    (buffer.size + iobuffer.i 1).val = buffer.size.val + 1 := by
  rcases h with ⟨_, hlen, hsize, hmax⟩
  rw [aio_add_val, aio_i_val_one]
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  omega

theorem aio_wrap_congr64 {a b : Int}
    (h : a % (2 ^ 64) = b % (2 ^ 64)) :
    wrapInt .i64 a = wrapInt .i64 b := by
  simp [wrapInt, IntTy.signed, IntTy.bits] at h ⊢
  omega

theorem aio_to_i64 (z : Int) :
    (C.toJInt .i64 (BitVec.ofInt 64 z)).val = wrapInt .i64 z := by
  change wrapInt .i64 ((BitVec.ofInt 64 z).toInt) = _
  apply aio_wrap_congr64
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_emod

theorem aio_source_add (a b : JInt64) : int.add a b = a + b := by
  apply Subtype.ext
  simp only [int.add, int.add_int, C.jlAddInt, C.fromJInt]
  rw [← BitVec.ofInt_add]
  exact aio_to_i64 _

theorem aio_from_i64 (a : JInt64) : (C.fromJInt a).toInt = a.val := by
  have h := a.property
  simp only [C.fromJInt, BitVec.toInt_ofInt]
  simp [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, Int.bmod_def] at h ⊢
  split <;> omega

theorem aio_widen_i64 (a : JInt64) : int.widenTo .i64 a = a := by
  apply Subtype.ext
  exact wrapInt_of_inRange .i64 a.val a.property

theorem aio_source_lt (a b : JInt64) : int.lt a b = decide (a.val < b.val) := by
  change int.ltSame (int.widenTo .i64 a) (int.widenTo .i64 b) = _
  rw [aio_widen_i64, aio_widen_i64]
  change decide ((C.fromJInt a).toInt < (C.fromJInt b).toInt) = _
  rw [aio_from_i64, aio_from_i64]

theorem aio_cursor_get {Metadata : Type} (world : CursorWorld Metadata)
    (handle : Nat) (buffer : iobuffer.BufferState)
    (h : world.buffers[handle]? = some buffer) :
    cursorGet handle world = some (.ok (buffer, world)) := by
  unfold cursorGet
  simp only [io.getWorld, bind, pure, Option.bind]
  rw [h]

theorem aio_cursor_set {Metadata : Type} (world : CursorWorld Metadata)
    (handle : Nat) (buffer : iobuffer.BufferState) (h : handle < world.buffers.length) :
    cursorSet handle buffer world =
      some (.ok ((), { world with buffers := world.buffers.set handle buffer })) := by
  unfold cursorSet
  simp only [io.getWorld, bind, pure, Option.bind]
  rw [ite_eq_left h]
  rfl

theorem aio_seekend_run (buffer : iobuffer.BufferState) :
    (iobuffer.source_seekend iobuffer.bufferAccess ()).run buffer =
      .ok () { buffer with ptr := buffer.size + iobuffer.i 1 } := by
  simp only [iobuffer.source_seekend, iobuffer.bufferAccess, iobuffer.bufferFields,
    iobuffer.updateBufferFields, EStateM.run, bind, pure, get, modify,
    EStateM.bind, EStateM.pure, aio_source_add]
  rfl

theorem aio_read_end_run (buffer : iobuffer.BufferState)
    (getindex : List UInt8 → JInt64 → iobuffer.M (JInt .u8))
    (hext : CursorBufferExtent buffer) :
    (iobuffer.source_read_uint8 iobuffer.bufferAccess getindex ()).run
      { buffer with ptr := buffer.size + iobuffer.i 1 } =
      .error (if buffer.readable then .eofError else
        .jl (.argumentError "read failed, IOBuffer is not readable"))
        { buffer with ptr := buffer.size + iobuffer.i 1 } := by
  have hgt : int.lt buffer.size (buffer.size + iobuffer.i 1) = true := by
    rw [aio_source_lt, aio_size_succ buffer hext]
    exact decide_eq_true (by omega)
  cases buffer.readable <;>
    simp only [iobuffer.source_read_uint8, iobuffer.bufferAccess, iobuffer.bufferFields,
      EStateM.run, bind, pure, get, getThe, MonadStateOf.get, EStateM.get, EStateM.bind, EStateM.pure,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      iobuffer.source_throw_not_readable, iobuffer.liftIO, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw, hgt]

theorem aio_world_bind {World A B : Type}
    (action : io.M World A) (next : A → io.M World B) (before after : World) (value : A)
    (h : action before = some (.ok (value, after))) :
    (action >>= next) before = next value after := by
  simp only [bind, h, Option.bind]

theorem aio_lift_ok {Metadata A : Type} (before : CursorWorld Metadata) (handle : Nat)
    (buffer afterBuffer : iobuffer.BufferState) (action : iobuffer.M A) (value : A)
    (hget : before.buffers[handle]? = some buffer)
    (hrun : action.run buffer = .ok value afterBuffer) :
    iobuffer.liftBufferIO cursorGet cursorSet handle action before =
      some (.ok (value, { before with buffers := before.buffers.set handle afterBuffer })) := by
  have hlt : handle < before.buffers.length := (List.getElem?_eq_some_iff.mp hget).1
  unfold iobuffer.liftBufferIO
  rw [aio_world_bind _ _ _ _ _ (aio_cursor_get before handle buffer hget)]
  rw [hrun]
  dsimp only
  rw [aio_world_bind _ _ _ _ _ (aio_cursor_set before handle afterBuffer hlt)]
  rfl

theorem aio_lift_error {Metadata A : Type} (before : CursorWorld Metadata) (handle : Nat)
    (buffer afterBuffer : iobuffer.BufferState) (action : iobuffer.M A) (error : iobuffer.IOErr)
    (hget : before.buffers[handle]? = some buffer)
    (hrun : action.run buffer = .error error afterBuffer) :
    iobuffer.liftBufferIO cursorGet cursorSet handle action before =
      some (.error (iobuffer.genericIOError error,
        { before with buffers := before.buffers.set handle afterBuffer })) := by
  have hlt : handle < before.buffers.length := (List.getElem?_eq_some_iff.mp hget).1
  unfold iobuffer.liftBufferIO
  rw [aio_world_bind _ _ _ _ _ (aio_cursor_get before handle buffer hget)]
  rw [hrun]
  dsimp only
  rw [aio_world_bind _ _ _ _ _ (aio_cursor_set before handle afterBuffer hlt)]
  rfl

/-- Seeking the wrapped buffer to its physical end preserves every framed field. -/
theorem AnnotatedIoSeekendReadEof_proven :
    JuliaLean.Proofs.base.strings.annotated_io.Round1.SeekEndExhaustsAndFrames := by
  intro Metadata Ref before wrapped buffer newBuffer copy hget hext
  dsimp only
  let atEnd := { buffer with ptr := buffer.size + iobuffer.i 1 }
  let after : CursorWorld Metadata :=
    { before with buffers := before.buffers.set wrapped.io atEnd }
  have hlt : wrapped.io < before.buffers.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  have hgetAfter : after.buffers[wrapped.io]? = some atEnd :=
    List.getElem?_set_self hlt
  have hseek : cursorSeekEnd wrapped.io before = some (.ok ((), after)) :=
    aio_lift_ok before wrapped.io buffer atEnd _ () hget (aio_seekend_run buffer)
  refine ⟨after, ?_, hgetAfter, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold strings.annotated_io.seekend
    change (cursorSeekEnd wrapped.io >>= fun _ => pure wrapped) before = _
    rw [aio_world_bind _ _ _ _ _ hseek]
    rfl
  · exact List.length_set
  · intro other hother hne
    exact List.getElem?_set_ne (Ne.symm hne)
  · change decide ((buffer.size + iobuffer.i 1 - iobuffer.i 1).val ≥ buffer.size.val) = true
    rw [aio_add_one_sub_one]
    exact decide_eq_true (Int.le_refl _)
  · exact aio_available_end buffer.size
  · unfold strings.annotated_io.position
    change (cursorGet wrapped.io >>= fun current => pure (iobuffer.source_position current)) after = _
    rw [aio_world_bind _ _ _ _ _ (aio_cursor_get after wrapped.io atEnd hgetAfter)]
    simp only [iobuffer.source_position, atEnd, aio_position_end]
    rfl
  · unfold cursorReadByte
    rw [aio_lift_error after wrapped.io atEnd atEnd _ _ hgetAfter
      (aio_read_end_run buffer _ hext)]
    cases buffer.readable <;>
      simp only [Bool.false_eq_true, ↓reduceIte, iobuffer.genericIOError,
        after, List.set_set]

end JuliaLean.ChatGPT.Batch4.Group18

namespace JuliaLean.Proofs.base.strings.annotated_io

open JuliaLean.Registry
def entries : List Entry := [
  { id := "annotated-io-seekend-read-eof",
    juliaFile := "base/strings/annotated_io.jl",
    juliaFns := ["seekend(io::AnnotatedIOBuffer)"],
    statement := "seekend on an AnnotatedIOBuffer returns the same wrapper and leaves the wrapped IOBuffer exhausted: eof is true, bytesavailable is zero, position is size minus offset, the next byte read raises EOFError (or the unreadable-buffer ArgumentError), and bytes, annotations, mode fields and all other buffers are unchanged.",
    source := "base/strings/annotated_io.jl:26; base/iobuffer.jl:438-448,467,470-473,526-529,691",
    status := .proven,
    prop := ``Round1.SeekEndExhaustsAndFrames,
    thm := some ``JuliaLean.ChatGPT.Batch4.Group18.AnnotatedIoSeekendReadEof_proven }
]

end JuliaLean.Proofs.base.strings.annotated_io
