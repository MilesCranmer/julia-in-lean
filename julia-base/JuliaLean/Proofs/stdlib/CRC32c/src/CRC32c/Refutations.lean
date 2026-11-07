import JuliaLean.Proofs.stdlib.CRC32c.src.CRC32c.Props

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- A one-byte file whose `stat` size is 0, as `/proc` files have: `crc32c` returns the
seed without reading. -/
theorem crc32cStreamAll_refuted : ¬ Crc32cStreamAll := by
  intro h
  have hh := h ⟨[b8 0x61], 0, 0⟩ (JInt.lit .u32 0) (by decide)
  revert hh
  decide

end JuliaLean.Base64Uuid
