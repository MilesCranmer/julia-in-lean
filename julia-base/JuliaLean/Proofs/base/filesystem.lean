import JuliaLean.base.filesystem

namespace JuliaLean.Files

/-- Current-offset writes advance by the bytes written, explicit-offset writes
leave the position unchanged, reads advance by bytes returned, and seeking may
position beyond end while bytes available stays zero. -/
def FileOffsetSpec : Prop :=
  (∀ file bytes, file.isOpen = true →
    unsafeWrite file bytes none =
      .ok (bytes.length,
        { file with data := writeData file.data file.position bytes,
                    position := file.position + bytes.length })) ∧
  (∀ file bytes offset, file.isOpen = true →
    unsafeWrite file bytes (some offset) =
      .ok (bytes.length,
        { file with data := writeData file.data offset bytes,
                    position := file.position })) ∧
  (∀ file byte, file.isOpen = true → file.data[file.position]? = some byte →
    readByte file = .ok (some byte, { file with position := file.position + 1 })) ∧
  (∀ file count, file.isOpen = true →
    ∃ bytes out,
      readBytes file count = .ok (bytes, out) ∧
      out.position = file.position + bytes.length ∧
      bytes = (file.data.drop file.position).take count) ∧
  (∀ file position, file.isOpen = true →
    seek file position = .ok { file with position } ∧
    bytesavailable { file with position } = file.data.length - position)

theorem fileOffsetSpec_proven : FileOffsetSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro file bytes hopen
    simp [unsafeWrite, hopen]
  · intro file bytes offset hopen
    simp [unsafeWrite, hopen]
  · intro file byte hopen hbyte
    simp [readByte, hopen, hbyte]
  · intro file count hopen
    let bytes := (file.data.drop file.position).take count
    refine ⟨bytes, { file with position := file.position + bytes.length }, ?_⟩
    simp [readBytes, hopen, bytes]
  · intro file position hopen
    constructor
    · simp [seek, hopen]
    · simp [bytesavailable]

end JuliaLean.Files
