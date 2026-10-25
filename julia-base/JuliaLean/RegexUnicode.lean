import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.RegexUnicode.CoreEntries
import JuliaLean.RegexUnicode.SubstEntries
import JuliaLean.RegexUnicode.UniEntries

/-!
# Regex and Unicode

Models of the Julia wrappers in `base/regex.jl`, `base/pcre.jl`, the regex paths of
`base/strings/util.jl` and `base/strings/search.jl`, `base/strings/unicode.jl` and
`stdlib/Unicode/src/Unicode.jl` (master `bbfa0ce4150`). PCRE2 and utf8proc are
primitives described by their documented behaviour.
-/

namespace JuliaLean.RegexUnicode

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := coreEntries ++ substEntries ++ unicodeEntries

end JuliaLean.RegexUnicode
