import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.StringUtil.Annotated
import JuliaLean.StringUtil.StartsIO
import JuliaLean.StringUtil.StartsIOProofs
import JuliaLean.StringUtil.Hex
import JuliaLean.StringUtil.Split
import JuliaLean.StringUtil.Truncate
import JuliaLean.StringUtil.Replace
import JuliaLean.StringUtil.Strip
import JuliaLean.StringUtil.Pad

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
