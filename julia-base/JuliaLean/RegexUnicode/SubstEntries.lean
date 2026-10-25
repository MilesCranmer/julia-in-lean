import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.RegexUnicode.SubstProofs

namespace JuliaLean.RegexUnicode

open JuliaLean.Registry

/-- Registry entries for regex substitution and the regex builders. -/
def substEntries : List Entry := [
  { id := "regexunicode-replace-capture-append", juliaFile := "base/regex.jl"
    juliaFns := ["replace(::IO, ::AbstractString, ::Pair{Regex,SubstitutionString})",
      "_write_capture(::IO, ::Int, str, r, ::RegexAndMatchData)"]
    statement := "On an append-mode IOBuffer (unbounded maxsize), replace(io, s, r => sub) appends exactly the bytes of replace(s, r => sub) after the existing content and leaves the read position unchanged."
    source := "base/strings/util.jl:1150-1152 (replace docstring: the transformed string is written to io); base/iobuffer.jl:52-53 (append: write new data at size+1)"
    status := .refuted
    prop := ``Subst.ReplaceCaptureAppend, thm := some ``Subst.replaceCaptureAppend_refuted
    issue := "none found (queries: replace io regex capture; replace PipeBuffer; _write_capture)"
    notes := "io = PipeBuffer(); write(io, \"head\"); read(io, UInt8); replace(io, \"abc\", r\"(b)\" => s\"<\\1>\"); read(io, String) == \"\\0da<>c\": the capture and its NUL go to io.ptr, the read position, which then advances." },
  { id := "regexunicode-replace-capture-generic-io", juliaFile := "base/regex.jl"
    juliaFns := ["replace(::IO, ::AbstractString, ::Pair{Regex,SubstitutionString})",
      "_write_capture(::IO, ::Int, str, r, ::RegexAndMatchData)"]
    statement := "For every IO (a fresh IOBuffer or any other IO), replace(io, s, r => sub) succeeds whenever replace(s, r => sub) does."
    source := "base/strings/util.jl:1150-1152 (replace([io::IO], s, pat=>r): the transformed string is written to io)"
    status := .refuted
    prop := ``Subst.ReplaceCaptureGenericIO, thm := some ``Subst.replaceCaptureGenericIO_refuted
    issue := "none found (queries: replace IOContext; replace io regex capture; _write_capture)"
    notes := "replace(devnull, \"abc\", r\"(b)\" => s\"<\\1>\") (also IOContext, IOStream) throws MethodError: no method matching ensureroom; replace(\"abc\", r\"(b)\" => s\"<\\1>\") == \"a<b>c\". Without a capture reference the call works." },
  { id := "regexunicode-subst-empty-group-name", juliaFile := "base/regex.jl"
    juliaFns := ["_replace(io, ::SubstitutionString, str, r, re)"]
    statement := "For every match, a malformed substitution string (a backslash not followed by a backslash, digits, or g<non-empty name>) makes the substitution throw ErrorException(\"Bad replacement string: ...\")."
    source := "base/regex.jl:652 (replace_err) and 686-726 (every malformed form calls replace_err); SubstitutionString docstring base/regex.jl:587-604"
    status := .refuted
    prop := ``Subst.SubstEmptyGroupName, thm := some ``Subst.substEmptyGroupName_refuted
    issue := "none found (queries: SubstitutionString g<; SubstitutionString group name empty)"
    notes := "s\"\\g<>\": all(isdigit, \"\") is true, so parse(Int, \"\") throws ArgumentError (regex.jl:713-714); s\"\\g<\" throws the documented ErrorException." },
  { id := "regexunicode-subst-group-overflow", juliaFile := "base/regex.jl"
    juliaFns := ["_replace(io, ::SubstitutionString, str, r, re)"]
    statement := "For every match, a reference \\N in a substitution string (N the decimal number written) either throws or writes capture group N."
    source := "base/strings/util.jl:1143-1144 (replace docstring: capture group references in r are replaced with the corresponding matched text)"
    status := .refuted
    prop := ``Subst.SubstGroupRef, thm := some ``Subst.substGroupRef_refuted
    issue := "none found (queries: SubstitutionString overflow; substitution string group number overflow)"
    notes := "replace(\"ab\", r\"(a)\" => s\"[\\18446744073709551617]\") == \"[a]b\": group = 10group + d (regex.jl:695) wraps Int to 1. s\"[\\2]\" throws \"PCRE error: unknown substring\"." },
  { id := "regexunicode-subst-literal", juliaFile := "base/regex.jl"
    juliaFns := ["_replace(io, ::SubstitutionString, str, r, re)"]
    statement := "For every match and every io, a substitution string without a backslash writes exactly its characters, one write(io, c) each; on an IO other than IOBuffer the bytes written are those of the string (as for the plain String replacement)."
    source := "base/strings/util.jl:1143-1144 (replace docstring); base/regex.jl:727-730"
    status := .proven
    prop := ``Subst.SubstLiteral, thm := some ``Subst.substLiteral_proven
    notes := "Stated for the text after unescape_string(repl, KEEP_ESC), byte by byte (ASCII level); for valid UTF-8 the byte walk issues the same write(io, ::UInt8) calls as write(io, c::Char) (io.jl:973-980)." },
  { id := "regexunicode-regex-pow-negative", juliaFile := "base/regex.jl"
    juliaFns := ["^(::Regex, ::Integer)"]
    statement := "For every compiling regex r and every n, r^n either throws or produces a pattern that PCRE reads as the pattern of r in a group followed by the repetition quantifier {n}."
    source := "base/regex.jl:910-928 (^ docstring: Repeat a regex n times)"
    status := .refuted
    prop := ``Subst.RegexPowQuant, thm := some ``Subst.regexPowQuant_refuted
    issue := "none found (queries: regex repeat negative; Regex ^ negative; regex multiplication)"
    notes := "r\"a\"^-1 == r\"(?:a){-1}\" (regex.jl:929); PCRE2 reads {-1} as literal text (pcre2pattern, Repetition), so match(r\"a\"^-1, \"a{-1}\") succeeds. \"a\"^-1 throws ArgumentError." },
  { id := "regexunicode-regex-concat-comment", juliaFile := "base/regex.jl"
    juliaFns := ["*(::Regex, ::AbstractString)", "wrap_string(::Regex, ::UInt32)"]
    statement := "For every regex r that compiles and every string s, r * s compiles."
    source := "base/regex.jl:829-855 (* docstring: Concatenate regexes, strings and/or characters, producing a Regex)"
    status := .refuted
    prop := ``Subst.RegexConcatCompiles, thm := some ``Subst.regexConcatCompiles_refuted
    issue := "none found (queries: regex concatenation comment; regex extended mode comment; regex multiplication)"
    notes := "r\"a  # the letter a\"x * \"b\" builds \"(?:a  # the letter a)\\\\Qb\\\\E\" with x set (regex.jl:874, 879): the comment runs to the end and swallows the ')', so PCRE reports missing closing parenthesis. Same for r^2 and r * r\"b\"x." },
  { id := "regexunicode-concat-quote", juliaFile := "base/regex.jl"
    juliaFns := ["wrap_string(::AbstractString, ::UInt32)", "*(::Regex, ::AbstractString)"]
    statement := "For every string s, wrap_string(s) = \"\\\\Q\" * replace(s, raw\"\\E\" => raw\"\\\\E\\QE\") * \"\\\\E\" lexes under PCRE's \\Q...\\E rule to exactly the literal characters of s, and lexing it followed by any text consumes the whole quoted part and returns to the ordinary state."
    source := "base/regex.jl:880-881 (comment: if s contains \\E, split '\\' and 'E' within two distinct \\Q...\\E groups); pcre2pattern, Quoting"
    status := .proven
    prop := ``Subst.ConcatQuote, thm := some ``Subst.concatQuote_proven
    notes := "Holds with and without the x flag: \\Q...\\E is checked before x-mode white space and comments." },
  { id := "regexunicode-dupnames-haskey", juliaFile := "base/regex.jl"
    juliaFns := ["keys(::RegexMatch)", "haskey(::RegexMatch, ::AbstractString)"]
    statement := "For every regex and match m, every key k in keys(m) satisfies haskey(m, k)."
    source := "base/regex.jl:238-259 (keys docstring: a vector of keys for all capture groups; named groups have string keys)"
    status := .refuted
    prop := ``Subst.DupnamesHaskey, thm := some ``Subst.dupnamesHaskey_refuted
    issue := "#51560"
    notes := "m = match(r\"(?J)(?<x>a)|(?<x>b)\", \"b\"): keys(m) == [\"x\", \"x\"], haskey(m, \"x\") == false, since pcre2_substring_number_from_name returns PCRE2_ERROR_NOUNIQUESUBSTRING (-50) for a duplicated name (regex.jl:294-297)." }
]

end JuliaLean.RegexUnicode
