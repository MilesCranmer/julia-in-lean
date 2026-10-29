import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.RegexUnicode.UniBasic
import JuliaLean.RegexUnicode.UniNormalize
import JuliaLean.RegexUnicode.UniNormProof
import JuliaLean.RegexUnicode.UniGraphemes
import JuliaLean.RegexUnicode.UniGraphProof

namespace JuliaLean.RegexUnicode

open JuliaLean.Registry

/-- Registry entries for `base/strings/unicode.jl` and `stdlib/Unicode`. -/
def unicodeEntries : List Entry := [
  { id := "regexunicode-isequal-normalized-stripmark"
    juliaFile := "stdlib/Unicode/src/Unicode.jl"
    juliaFns := ["isequal_normalized(::AbstractString, ::AbstractString)",
      "_isequal_normalized!", "decompose_next_chars!"]
    statement := "For all strings of code points, casefold and stripmark, and any uninitialized buffer contents, isequal_normalized(s1, s2; casefold, stripmark) equals the comparison of the canonical decompositions normalize(s; decompose=true, casefold, stripmark) (per-character utf8proc_decompose_char, then canonical ordering), for every utf8proc table with the documented decomposition behaviour."
    source := "stdlib/Unicode/src/Unicode.jl:230-268 (isequal_normalized docstring: whether s1 and s2 are canonically equivalent; stripmark=true strips diacritical marks and other combining characters)"
    status := .refuted
    prop := ``Uni.IsequalNormalizedSpec
    thm := some ``Uni.isequalNormalizedSpec_refuted
    issue := "none found; related #52408 (queries: isequal_normalized; isequal_normalized stripmark)"
    notes := "Counterexample isequal_normalized(\"a\\u0301\", \"aa\"; stripmark=true): true, decompositions \"a\" and \"aa\". With STRIPMARK, U+0301 decomposes to 0 code points, so decompose_next_chars! returns n = 0 after reading combining_class(d[0]) out of bounds under @inbounds (modelled as the buffer's memory at position 0), and the main loop compares the stale d1[1] = 'a' (Unicode.jl:333-344 never re-checks j1 > n1). Theorem stripmark_observed reproduces the other observed rows: (\"cafe\\u0301\", \"cafe\") false, (\"cafe\\u0301\", \"cafee\") true, (\"\\u0301\", \"\") false. Theorem stripmark_uninit: in the model isequal_normalized(\"\\u0301\", \"\\u0301\"; stripmark=true) compares the never-written d1[1] and d2[1], so it is true or false depending on the uninitialized contents of the two Vector{UInt32}(undef, 4) buffers. When the mark is followed by a character, the d[0] read decides whether the next character joins the chunk (\"noe\\u0308l\" vs \"noel\" printed false, consistent with combining_class(d[0]) == 0). Identical in 1.13.2." },
  { id := "regexunicode-isequal-normalized-reflexive"
    juliaFile := "stdlib/Unicode/src/Unicode.jl"
    juliaFns := ["isequal_normalized(::AbstractString, ::AbstractString)",
      "_isequal_normalized!", "decompose_next_chars!"]
    statement := "Without stripmark, isequal_normalized(s, s; casefold) == true for every string whose characters are code points below 0x110000, every casefold, any uninitialized buffer contents, and every utf8proc table whose decomposition succeeds on code points and is nonempty without STRIPMARK."
    source := "stdlib/Unicode/src/Unicode.jl:230-268 (isequal_normalized docstring: canonical equivalence); invariant"
    status := .proven
    prop := ``Uni.IsequalNormalizedReflexive
    thm := some ``Uni.isequalNormalizedReflexive_proven
    notes := "The proof shows that without STRIPMARK every chunk has n >= 1, decompose_next_chars! reads only buffer positions it wrote in the same call (including the n < 32 insertion sort and the n >= 32 segment sort), and the two buffers agree on 1:n whatever their uninitialized contents; the main loop's bound sum(dlen + 1) + 1 is never exhausted. Full agreement with the NFD specification without stripmark (regexunicode-isequal-normalized-nostrip) was not attempted; an 80000-row differential check against normalize found no mismatch. With stripmark the property fails (regexunicode-isequal-normalized-stripmark, theorem stripmark_uninit)." },
  { id := "regexunicode-graphemes-range"
    juliaFile := "stdlib/Unicode/src/Unicode.jl"
    juliaFns := ["graphemes(::AbstractString, ::AbstractUnitRange)",
      "iterate(::GraphemeIterator, ::Any)", "length(::GraphemeIterator)",
      "isgraphemebreak!(::Ref{Int32}, ::AbstractChar, ::AbstractChar)"]
    statement := "For every String s and 1 <= m <= n: if n <= length(graphemes(s)), graphemes(s, m:n) returns a SubString of s whose bytes are the concatenation of elements m through n of collect(graphemes(s)); if n > length(graphemes(s)) it throws BoundsError. length(graphemes(s)) equals the number of collected graphemes. Holds for every utf8proc_grapheme_break_stateful that breaks after '\\0' from state 0 and leaves the initial state for the next character."
    source := "stdlib/Unicode/src/Unicode.jl:152-185 (graphemes(s, m:n) docstring: the m-th through n-th graphemes of s)"
    status := .proven
    prop := ``Uni.GraphemesRangeProp
    thm := some ``Uni.graphemesRange_proven
    notes := "Covers malformed and overlong encodings on master: isgraphemebreak! never throws there because UInt32(c) succeeds on every well-formed character. The hypothesis GbInit (a precondition of the property, not an axiom) is the documented GB4 rule (break after a control character) plus utf8proc's state encoding (state after a break from 0 at c equals the state initialized from c). 1.13.2 differs only for overlong encodings: its UInt32(::Char) throws InvalidCharError for them, and collect(graphemes(\"\\xc0\\x80\")), length(graphemes(\"\\xc0\\x80\")) and graphemes(\"\\xc0\\x80\", 1:1) all throw InvalidCharError on 1.13.2 while master returns the one grapheme \"\\xc0\\x80\"." }
]

end JuliaLean.RegexUnicode
