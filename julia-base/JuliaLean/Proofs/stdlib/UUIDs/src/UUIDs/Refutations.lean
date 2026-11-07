import JuliaLean.Proofs.stdlib.UUIDs.src.UUIDs.Props

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `uuid5` hashes `unescape_string("\\n") == "\n"` instead of the two characters. -/
theorem uuid5HashesName_refuted : ¬ Uuid5HashesName := by
  intro h
  have hh := h ⟨JInt.lit .u128 0⟩ ['\\', 'n']
  revert hh
  decide

end JuliaLean.Base64Uuid
