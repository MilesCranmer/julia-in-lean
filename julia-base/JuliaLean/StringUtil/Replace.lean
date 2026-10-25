import JuliaLean.StringUtil.ReplaceProofs
import JuliaLean.Registry.Types

/-!
# Registry entries for `replace(s, pat => repl, ...)`

Model: `JuliaLean/StringUtil/ReplaceModel.lean`; proofs:
`JuliaLean/StringUtil/ReplaceProofs.lean`.
-/

namespace JuliaLean.StringUtil

open JuliaLean.Registry

def replaceEntries : List Entry := [
  { id := "stringutil-replace-reference"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["replace(::String, ::Pair...; count)", "_replace_init", "_replace_once",
      "_replace_finish", "_replace_(::String, ::NTuple{N,Pair}, ::Int)"]
    statement := "For N pairs pat => repl with nonempty patterns and String/Char replacements, " ++
      "replace(s, pairs...; count) equals the docstring's single left-to-right scan: at each " ++
      "character index the first pattern in argument order that occurs there is replaced and " ++
      "the scan resumes after the match, other bytes are copied, and at most count replacements " ++
      "are made. Hypothesis (finder contract): for every 1 <= k <= ncodeunits(s)+1, " ++
      "findnext(pat, s, k) returns the first occurrence of the pattern's bytes at a character " ++
      "index >= k (an Int j, or a range j:l whose last character starts at l, i.e. " ++
      "nextind(s, l) == j + ncodeunits(pat)), or nothing if there is none."
    source := "docstring base/strings/util.jl:1152-1157"
    status := .proven
    prop := `JuliaLean.StringUtil.ReplaceMatchesReference
    thm := some `JuliaLean.StringUtil.replaceMatchesReference
    notes := "Proven for every byte string s: validity of s is not a hypothesis, all " ++
      "assumptions sit in the finder contract (that Julia's findnext for String and Char " ++
      "patterns meets it on valid UTF-8 is not proven here; a differential check " ++
      "exercises it). Model and reference agree " ++
      "with Julia 1.13.2 and nightly on 9 cases (string and Char patterns, ties in both " ++
      "argument orders, count = 0, 1, 2, 3, -1). The replace code in util.jl is identical " ++
      "in 1.13.2." },
  { id := "stringutil-replace-count-edge"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["replace(::String, ::Pair...; count)", "_replace_init"]
    statement := "replace(s, pairs...; count=0) returns s, and count < 0 throws DomainError."
    source := "docstring base/strings/util.jl:1137 (replace at most count occurrences); invariant"
    status := .proven
    prop := `JuliaLean.StringUtil.ReplaceCountEdge
    thm := some `JuliaLean.StringUtil.replaceCountEdge
    notes := "count == 0 is checked in _replace_ before _replace_init, so it never throws." },
  { id := "stringutil-replace-count-min"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["replace(::String, ::Pair...; count)", "_replace_finish", "_replace_once"]
    statement := "Under the finder contract of stringutil-replace-reference, with count >= 0 " ++
      "the number of replacements (calls of _replace) is min(count, m), where m is the number " ++
      "made with the default count = typemax(Int), which equals the number of matches of the " ++
      "reference scan."
    source := "docstring base/strings/util.jl:1137 (replace at most count occurrences)"
    status := .proven
    prop := `JuliaLean.StringUtil.ReplaceCountMin
    thm := some `JuliaLean.StringUtil.replaceCountMin
    notes := "The replacement count is instrumentation in the model (nrep), not a Julia value." }
]

end JuliaLean.StringUtil
