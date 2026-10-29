import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.RegexUnicode.CoreTheory
import JuliaLean.RegexUnicode.CoreProps

namespace JuliaLean.RegexUnicode

open JuliaLean.Registry

def coreEntries : List Entry := [
  { id := "regexunicode-eachmatch-progress", juliaFile := "base/regex.jl"
    juliaFns := ["iterate(::RegexMatchIterator)", "eachmatch(::Regex, ::AbstractString)", "match(::Regex, ::String, ::Integer, ::UInt32)"]
    statement := "Each step of eachmatch(r, s; overlap) from a state (offset, prevempty) returns a match with m.offset >= offset; without overlap the next offset is m.offset + ncodeunits(m.match); the measure 2(ncodeunits(s)+1-offset) + (prevempty ? 0 : 1) strictly decreases, so iteration from any state terminates, for every PCRE primitive whose nonempty matches start at valid indices and every byte string."
    source := "eachmatch docstring (base/regex.jl:779-784): \"Search for all matches of the regular expression r in s and return an iterator over the matches\"; termination invariant of iterate (base/regex.jl:749-777)"
    status := .proven, prop := ``JuliaLean.RegexUnicode.Core.EachmatchProgress
    thm := some ``JuliaLean.RegexUnicode.Core.eachmatchProgress_proven
    notes := "Hypothesis NonemptyAtChar: every nonempty PCRE match starts at a valid Julia index. Without it the statement fails: a nonempty match inside one character gives an empty SubString, so the state (o, true) can repeat (e.g. r\"(?:\\C\\K)?\\C\" on \"€\"). Julia cannot build such a regex: \\C, the only item matching part of a character in UTF mode, is rejected by the JIT (\"PCRE JIT error: feature is not supported by the JIT compiler\" on 1.13.2 and master), and with PCRE2_MATCH_INVALID_UTF nonempty matches consist of whole valid characters." },
  { id := "regexunicode-count-findall", juliaFile := "base/regex.jl"
    juliaFns := ["count(::Regex, ::AbstractString)", "findall(::Regex, ::AbstractString)"]
    statement := "count(r, s; overlap) == length(findall(r, s; overlap)) for every PCRE primitive, string and overlap flag, including which exception is thrown."
    source := "count docstring (base/regex.jl:546-547): \"This is equivalent to calling length(findall(pattern, string)) but more efficient.\""
    status := .proven, prop := ``JuliaLean.RegexUnicode.Core.CountEqLengthFindall
    thm := some ``JuliaLean.RegexUnicode.Core.countEqLengthFindall_proven
    notes := "count (base/regex.jl:573-585) and findall (base/strings/search.jl:651-665) run the same findnext loop." },
  { id := "regexunicode-findnext-range", juliaFile := "base/regex.jl"
    juliaFns := ["findnext(::Regex, ::String, ::Integer)", "_findnext_re"]
    statement := "For valid UTF-8 s and a valid start index i (or ncodeunits(s)+1), findnext(r, s, i) returning a range r has first(r) >= i, first(r) a valid index or ncodeunits(s)+1, and s[r] defined, for every PCRE primitive whose matches started at a character boundary begin and end at character boundaries."
    source := "findnext docstring (base/strings/search.jl:482-492): \"The return value is a range of indices where the matching sequence is found, such that s[findnext(x, s, i)] == x\" and \"i <= start\""
    status := .proven, prop := ``JuliaLean.RegexUnicode.Core.FindnextRange
    thm := some ``JuliaLean.RegexUnicode.Core.findnextRange_proven
    notes := "Hypothesis CharBoundaries matches PCRE2's UTF mode (pcre2unicode: characters are matched; pcre2api: with PCRE2_NO_UTF_CHECK the start offset must be at a character boundary). last(r) = prevind(s, ovector[2] + 1) after UnitRange normalisation (base/range.jl:439-441)." },
  { id := "regexunicode-findnext-start-below", juliaFile := "base/regex.jl"
    juliaFns := ["findnext(::Regex, ::String, ::Integer)", "_findnext_re", "match(::Regex, ::String, ::Integer)"]
    statement := "findnext(r, s, i) throws BoundsError for every start i < 1, like findnext(::AbstractString, ::String, i)."
    source := "consistency with findnext(t::AbstractString, s::String, i), which throws BoundsError for i < 1 (base/strings/search.jl:400-408), and with findnext(r, s, i) for i > ncodeunits(s)+1 (base/regex.jl:492-494)"
    status := .refuted, prop := ``JuliaLean.RegexUnicode.Core.FindnextBelowBoundsError
    thm := some ``JuliaLean.RegexUnicode.Core.findnextBelowBoundsError_refuted
    issue := "none found (queries: findnext regex InexactError; match regex bad offset value; match regex offset bounds)"
    notes := "findnext(r\"a\", \"abc\", 0) and match(r\"a\", \"abc\", 0) throw InexactError: idx-1 = -1 is converted to Csize_t in the pcre2_match ccall (base/pcre.jl:211-213). _findnext_re checks only idx > nextind(s, lastindex(s)). Checked in startBelow_agrees." },
  { id := "regexunicode-match-offset-inside-char", juliaFile := "base/regex.jl"
    juliaFns := ["match(::Regex, ::String, ::Integer)", "findnext(::Regex, ::String, ::Integer)"]
    statement := "For valid UTF-8 s and i in 1:ncodeunits(s)+1, match(r, s, i) returning m has isvalid(s, m.offset) or m.offset == ncodeunits(s)+1."
    source := "RegexMatch docstring (base/regex.jl:177): \"The location of the start of the match is stored in the offset field\" (an index of s)"
    status := .refuted, prop := ``JuliaLean.RegexUnicode.Core.MatchOffsetValid
    thm := some ``JuliaLean.RegexUnicode.Core.matchOffsetValid_refuted
    issue := "none found (queries: match offset inside character; match regex offset bounds)"
    notes := "match(r\"\", \"éa\", 2).offset == 2 and findnext(r\"\", \"éa\", 2) == 2:1 (1.13.2 and master): Julia passes PCRE2_NO_UTF_CHECK, so pcre2_match accepts a start offset inside a character and the empty match is reported there. Checked in emptyEA_agrees." },
  { id := "regexunicode-eachmatch-offset-inside-malformed", juliaFile := "base/regex.jl"
    juliaFns := ["iterate(::RegexMatchIterator)", "eachmatch(::Regex, ::AbstractString)", "findfirst(::Regex, ::AbstractString)"]
    statement := "For any byte string s, every offset <= ncodeunits(s) of a match yielded by eachmatch(r, s) is a valid index of s, for every PCRE primitive satisfying the documented pcre2_match facts."
    source := "RegexMatch docstring (base/regex.jl:177): the offset is the start of the match in s; eachmatch iterates s by valid offsets (base/regex.jl:749-777 uses nextind)"
    status := .refuted, prop := ``JuliaLean.RegexUnicode.Core.EachmatchOffsetsValid
    thm := some ``JuliaLean.RegexUnicode.Core.eachmatchOffsetsValid_refuted
    issue := "none found; related #63805 (PCRE2 10.49 upgrade) (queries: PCRE 10.49; PCRE2 10.49; PCRE invalid UTF-8 empty match)"
    notes := "Nightly only. s = \"a\\xe2\\x82\", r\"(?<!a)(?!a)\": master (PCRE2 10.49) yields offsets [3, 4], findfirst 3:2, replace(s, r => \"-\") == \"a\\xe2-\\x82-\"; index 3 is inside the malformed character at 2:3. 1.13.2 (PCRE2 10.46) yields offsets [4] only. The counterexample primitive emptyAt [2, 3] reports exactly master's empty matches; PCRE2's MATCH_INVALID_UTF documentation does not tie positions inside invalid sequences to Julia's character grouping. Checked in eachLookMal_agrees and lookMal_agrees." }
]

end JuliaLean.RegexUnicode
