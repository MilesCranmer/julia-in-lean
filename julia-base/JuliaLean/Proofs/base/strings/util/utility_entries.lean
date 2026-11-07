import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.strings.annotated.regions
import JuliaLean.Proofs.base.strings.util.starts_io
import JuliaLean.Proofs.base.strings.util.starts_io_proofs
import JuliaLean.Proofs.base.strings.util.hex
import JuliaLean.Proofs.base.strings.util.split
import JuliaLean.Proofs.base.strings.util.truncate
import JuliaLean.Proofs.base.strings.util.replacement_entries
import JuliaLean.Proofs.base.strings.util.strip
import JuliaLean.Proofs.base.strings.util.padding

/-!
# String utilities

`base/strings/util.jl`, string helpers of `base/strings/basic.jl` and
`base/strings/annotated.jl` (master `bbfa0ce4150`), on top of the String model of
`JuliaLean/Strings`.
-/

namespace JuliaLean.StringUtil

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry :=
  annotatedEntries ++ startsioEntries ++ startsioProofEntries ++ hexEntries ++ splitEntries ++
    truncateEntries ++ replaceEntries ++ stripEntries ++
    padEntries

end JuliaLean.StringUtil
