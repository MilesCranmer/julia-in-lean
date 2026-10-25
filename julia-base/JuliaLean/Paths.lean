import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Paths.Model
import JuliaLean.Paths.Props
import JuliaLean.Paths.Refute
import JuliaLean.Paths.Split
import JuliaLean.Paths.Relpath

namespace JuliaLean.Paths

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "paths-splitext-dotfile-doc", juliaFile := "base/path.jl"
    juliaFns := ["splitext(::AbstractString)"]
    statement := "If the last component of p = q * \".\" * r (r without dots or separators) contains the dot, splitext(p) == (q, \".\" * r)."
    source := "base/path.jl:335-337 (splitext docstring)", status := .refuted
    prop := ``SplitextDoc, thm := some ``splitextDoc_refuted
    issue := "none found (queries: splitext, splitext dotfile, splitext hidden file)"
    notes := "splitext(\".bashrc\") == (\".bashrc\", \"\") but splitext(\"..bashrc\") == (\".\", \".bashrc\"). Likely intended dotfile rule, undocumented. Same on 1.13.2 (regex implementation)." },
  { id := "paths-dirname-basename", juliaFile := "base/path.jl"
    juliaFns := ["dirname", "basename", "splitdir"]
    statement := "splitdir(p) == (dirname(p), basename(p)); basename(p) has no separator and ends p."
    source := "base/path.jl:262-330 (splitdir, dirname, basename docstrings)", status := .proven
    prop := ``DirnameBasename, thm := some ``dirnameBasename_proven },
  { id := "paths-joinpath-splitdir", juliaFile := "base/path.jl"
    juliaFns := ["joinpath", "splitdir"]
    statement := "joinpath(dirname(p), basename(p)) == p for every p without \"//\"."
    source := "invariant (splitdir docstring: split a path into directory and file name)", status := .proven
    prop := ``JoinSplitdir, thm := some ``joinSplitdir_proven },
  { id := "paths-splitpath-joinpath", juliaFile := "base/path.jl"
    juliaFns := ["splitpath", "joinpath"]
    statement := "joinpath(splitpath(p)...) == p for canonical p, and splitpath(joinpath(parts...)) == parts for component lists."
    source := "base/path.jl:376-377 (splitpath docstring: the opposite of joinpath)", status := .proven
    prop := ``SplitpathJoinpath, thm := some ``splitpathJoinpath_proven },
  { id := "paths-splitext-concat", juliaFile := "base/path.jl"
    juliaFns := ["splitext"]
    statement := "a * b == p for (a, b) = splitext(p), and b is empty or a dot followed by neither dots nor separators."
    source := "base/path.jl:335-337 (splitext docstring)", status := .proven
    prop := ``SplitextConcat, thm := some ``splitextConcat_proven
    notes := "1.13.2 differs: its regex implementation (replaced on master by merged PR #60677) lets `$` match before a final newline, so on 1.13.2 splitext(\"a\\n\") == (\"a\", \"\") drops the newline, isdirpath(\"\\n\") and isdirpath(\"a/\\n\") are true, and normpath(\"\\n/\") == \"\\n\". Fixed on master." },
  { id := "paths-normpath-idempotent", juliaFile := "base/path.jl"
    juliaFns := ["normpath"]
    statement := "normpath(normpath(p)) == normpath(p)."
    source := "base/path.jl:543 (normpath docstring: normalize a path)", status := .proven
    prop := ``NormpathIdempotent, thm := some ``normpathIdempotent_proven },
  { id := "paths-normpath-canonical", juliaFile := "base/path.jl"
    juliaFns := ["normpath"]
    statement := "normpath(p) has no \"//\"; for absolute p it is absolute with no \".\" or \"..\" component (never above the root); for relative p, \"..\" only at the start and no \".\" unless the result is \".\"."
    source := "base/path.jl:543 (normpath docstring: removing . and .. entries)", status := .proven
    prop := ``NormpathCanonical, thm := some ``normpathCanonical_proven },
  { id := "paths-normpath-lexical", juliaFile := "base/path.jl"
    juliaFns := ["normpath"]
    statement := "normpath(p) leads where p leads under lexical resolution of . and .., from every starting directory."
    source := "base/path.jl:543 (normpath docstring)", status := .proven
    prop := ``NormpathLexical, thm := some ``normpathLexical_proven },
  { id := "paths-normpath-isdirpath", juliaFile := "base/path.jl"
    juliaFns := ["normpath", "isdirpath"]
    statement := "isdirpath(normpath(p)) == isdirpath(p)."
    source := "invariant (normpath keeps a directory path a directory path)", status := .proven
    prop := ``NormpathIsdirpath, thm := some ``normpathIsdirpath_proven
    notes := "1.13.2 differs: its regex implementation (replaced on master by merged PR #60677) lets `$` match before a final newline, so on 1.13.2 splitext(\"a\\n\") == (\"a\", \"\") drops the newline, isdirpath(\"\\n\") and isdirpath(\"a/\\n\") are true, and normpath(\"\\n/\") == \"\\n\". Fixed on master." },
  { id := "paths-relpath-roundtrip", juliaFile := "base/path.jl"
    juliaFns := ["relpath", "abspath"]
    statement := "With an absolute pwd(), relpath(p, s) is relative and leads from s to p under lexical resolution."
    source := "base/path.jl:914-916 (relpath docstring)", status := .proven
    prop := ``RelpathRoundtrip, thm := some ``relpathRoundtrip_proven },
  { id := "paths-joinpath-laws", juliaFile := "base/path.jl"
    juliaFns := ["joinpath"]
    statement := "joinpath(a, b) == b for absolute b, and joinpath is associative."
    source := "base/path.jl:494-496 (joinpath docstring: prior components dropped)", status := .proven
    prop := ``JoinpathLaws, thm := some ``joinpathLaws_proven },
  { id := "paths-expanduser-doc", juliaFile := "base/path.jl"
    juliaFns := ["expanduser"]
    statement := "expanduser replaces a leading ~ (followed by / or nothing) with homedir() and leaves paths without leading ~, and ~user of unknown users, unchanged."
    source := "base/path.jl:887-893 (expanduser docstring)", status := .proven
    prop := ``ExpanduserDoc, thm := some ``expanduserDoc_proven },
  { id := "paths-abspath-laws", juliaFile := "base/path.jl"
    juliaFns := ["abspath"]
    statement := "With an absolute pwd(), abspath(p) is absolute and abspath(abspath(p)) == abspath(p)."
    source := "base/path.jl:600-601 (abspath docstring)", status := .proven
    prop := ``AbspathLaws, thm := some ``abspathLaws_proven },
  { id := "paths-isdirpath-trailing", juliaFile := "base/path.jl"
    juliaFns := ["isdirpath"]
    statement := "isdirpath(p * \"/\") is true for every p."
    source := "base/path.jl:244 (isdirpath docstring)", status := .proven
    prop := ``IsdirpathTrailing, thm := some ``isdirpathTrailing_proven }
]

end JuliaLean.Paths
