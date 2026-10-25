import JuliaLean.Base64Uuid.Props

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-!
Concrete counterexamples. Each matches a reproducer in `repro/base64uuid-*.jl`; the
inputs here are the smallest ones showing the same mechanism.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `"SGVsbG8hSGVs"` decodes to `"Hello!Hel"`; `read(pipe, 6)` pulls the last four
characters into the pipe buffer, `eof(pipe)` is then true and `read(pipe)` returns
nothing. -/
theorem decodeStreamSplit_refuted : ¬ DecodeStreamSplit := by
  intro h
  have hh := h (ascii "SGVsbG8hSGVs") [6] (ascii "Hello!Hel") (by decide)
  revert hh
  decide

/-- After the one byte of `"QQ=="`, only the ignored `'\n'` is left: `eof` is false and
`read(pipe, UInt8)` throws `EOFError`. -/
theorem eofThenReadByte_refuted : ¬ EofThenReadByte := by
  intro h
  have hh := h (ascii "QQ==\n") 1 ⟨ascii "\n", [], []⟩ (by decide) (by decide)
  obtain ⟨b, p, hb⟩ := hh
  have : readByte ⟨ascii "\n", [], []⟩ = some (.error .eof) := by decide
  rw [this] at hb
  cases hb

/-- The pipe after the first iteration of `readbytes!(pipe, UInt8[], 1)` on `"QQ=="`:
the decoded byte waits in `pipe.rest`. -/
def hangPipe : DPipe := ⟨[], [], [b8 0x41]⟩

theorem hang_first : ∀ f, readbytesLoop (f + 1) (DPipe.new (ascii "QQ==")) ⟨0, []⟩ 0 1 =
    readbytesLoop f hangPipe ⟨0, []⟩ 0 1 := by
  intro f
  have h1 : rbStep (DPipe.new (ascii "QQ==")) ⟨0, []⟩ 0 1 =
      some (.ok (.inr (hangPipe, ⟨0, []⟩, 0))) := by decide
  simp only [readbytesLoop, h1]

theorem hang_step : ∀ f, readbytesLoop (f + 1) hangPipe ⟨0, []⟩ 0 1 =
    readbytesLoop f hangPipe ⟨0, []⟩ 0 1 := by
  intro f
  have h1 : rbStep hangPipe ⟨0, []⟩ 0 1 = some (.ok (.inr (hangPipe, ⟨0, []⟩, 0))) := by decide
  simp only [readbytesLoop, h1]

theorem hang_loop : ∀ f, readbytesLoop f hangPipe ⟨0, []⟩ 0 1 = none := by
  intro f
  induction f with
  | zero => rfl
  | succ f ih => rw [hang_step, ih]

/-- `readbytes!(Base64DecodePipe(IOBuffer("QQ==")), UInt8[], 1)` never returns. -/
theorem readbytesTerminates_refuted : ¬ ReadbytesTerminates := by
  intro h
  obtain ⟨fuel, hf⟩ := h (ascii "QQ==") ⟨0, []⟩ 1
  apply hf
  cases fuel with
  | zero => rfl
  | succ f => simp only [readbytesF, hang_first, hang_loop]

/-- `readbytes!(Base64DecodePipe(IOBuffer("QQ==")), data, 4)` with `length(data) == 4`
leaves `length(data) == 1`. -/
theorem readbytesNoShrink_refuted : ¬ ReadbytesNoShrink := by
  intro h
  have hh := h (ascii "QQ==") ⟨4, []⟩ 4 10 ⟨[], [], []⟩ ⟨1, [b8 0x41]⟩ 1 (by decide)
  revert hh
  decide

/-- `base64decode("QQ==QQ==") == [0x41, 0x41]`, no `ArgumentError`. -/
theorem decodeRejectsMidPadding_refuted : ¬ DecodeRejectsMidPadding := by
  intro h
  have hh := h (ascii "QQ==QQ==") (by decide)
  revert hh
  decide

/-- `uuid5` hashes `unescape_string("\\n") == "\n"` instead of the two characters. -/
theorem uuid5HashesName_refuted : ¬ Uuid5HashesName := by
  intro h
  have hh := h ⟨JInt.lit .u128 0⟩ ['\\', 'n']
  revert hh
  decide

/-- A one-byte file whose `stat` size is 0, as `/proc` files have: `crc32c` returns the
seed without reading. -/
theorem crc32cStreamAll_refuted : ¬ Crc32cStreamAll := by
  intro h
  have hh := h ⟨[b8 0x61], 0, 0⟩ (JInt.lit .u32 0) (by decide)
  revert hh
  decide

end JuliaLean.Base64Uuid
