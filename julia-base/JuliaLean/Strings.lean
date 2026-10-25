import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Strings.Search
import JuliaLean.Strings.Length

namespace JuliaLean.Strings

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "strings-iterate-valid-indices"
    juliaFile := "base/strings/string.jl"
    juliaFns := ["iterate(::String, ::Int)", "isvalid(::String, ::Int)"]
    statement := "Iterating any byte string, valid UTF-8 or not, from firstindex terminates and yields one character at each index i with isvalid(s, i), in increasing order."
    source := "base/strings/basic.jl:31-47 (AbstractString iteration contract); invariant"
    status := .proven
    prop := ``IterateVisitsValid
    thm := some ``iterateVisitsValid_proven
    notes := "Covers overlong encodings, surrogates, truncated sequences and stray continuation bytes: the model is the byte list with no validity assumption." },
  { id := "strings-length-iterate-steps"
    juliaFile := "base/strings/string.jl"
    juliaFns := ["length(::String)", "iterate(::String, ::Int)"]
    statement := "length(s) equals the number of characters that iterating s yields, for any byte string s."
    source := "base/strings/basic.jl (length docstring: number of characters); invariant"
    status := .proven
    prop := ``LengthIterateSteps
    thm := some ``lengthIterateSteps_proven
    notes := "Proves that the _length_continued loop (base/strings/string.jl:635-658) subtracts exactly the continuation bytes absorbed by lead bytes, the positions where isvalid(s, i) is false." },
  { id := "strings-thisind-idempotent"
    juliaFile := "base/strings/string.jl"
    juliaFns := ["thisind(::String, ::Int)"]
    statement := "thisind(s, thisind(s, i)) == thisind(s, i) whenever thisind(s, i) returns."
    source := "base/strings/basic.jl:435-460 (thisind docstring); invariant"
    status := .proven
    prop := ``ThisindIdempotent
    thm := some ``thisindIdempotent_proven },
  { id := "strings-prevind-after-nextind"
    juliaFile := "base/strings/string.jl"
    juliaFns := ["nextind(::String, ::Int)", "prevind(::AbstractString, ::Int, ::Int)"]
    statement := "prevind(s, nextind(s, i)) == i for every valid index i of any byte string."
    source := "base/strings/basic.jl:477-500,517-540 (prevind/nextind docstrings); invariant"
    status := .proven
    prop := ``PrevindAfterNextind
    thm := some ``previndAfterNextind_proven },
  { id := "strings-nextind-after-prevind"
    juliaFile := "base/strings/string.jl"
    juliaFns := ["nextind(::String, ::Int)", "prevind(::AbstractString, ::Int, ::Int)"]
    statement := "nextind(s, prevind(s, i)) == i for every valid index i >= 2 and for i = ncodeunits(s)+1 of a nonempty string."
    source := "base/strings/basic.jl:477-500,517-540 (prevind/nextind docstrings); invariant"
    status := .proven
    prop := ``NextindAfterPrevind
    thm := some ``nextindAfterPrevind_proven },
  { id := "strings-repeat-size"
    juliaFile := "base/strings/substring.jl"
    juliaFns := ["repeat(::String, ::Integer)"]
    statement := "repeat(s, r) either throws or returns a String of exactly r * ncodeunits(s) code units; it never allocates a wrapped size."
    source := "invariant"
    status := .proven
    prop := ``RepeatSize
    thm := some ``repeatSize_proven
    notes := "Master checks r > typemax(UInt) ÷ n before computing n*r (base/strings/substring.jl:296, from #62797). Julia 1.13.2 has no such check (base/strings/substring.jl:271-287): repeat(\"abcd\", 2^62) computes n*r = 0 and then copies 2^62 times into a zero-length string; that release-only defect is not registered because master fixes it." },
  { id := "strings-first-n-overflow"
    juliaFile := "base/strings/basic.jl"
    juliaFns := ["first(::AbstractString, ::Integer)", "nextind(::AbstractString, ::Int, ::Int)"]
    statement := "first(s, n) with n >= length(s) returns the whole string s."
    source := "base/strings/basic.jl:684-686: \"Get a string consisting of the first `n` characters of `s`.\""
    status := .refuted
    prop := ``FirstNAll
    thm := some ``firstNAll_refuted
    issue := "none found (queries: nextind overflow, nextind typemax, first string typemax, first(s, n) overflow)"
    notes := "first(\"é\", typemax(Int)) == \"\": nextind(s, 0, n) wraps to a negative index, so s[1:min(end, k)] is empty. Any string with ncodeunits(s) > length(s) and n within ncodeunits(s) - length(s) of typemax(Int) is affected." },
  { id := "strings-nextind-n-overflow"
    juliaFile := "base/strings/basic.jl"
    juliaFns := ["nextind(::AbstractString, ::Int, ::Int)"]
    statement := "nextind(s, i, n) with n >= 1 and 0 <= i <= ncodeunits(s) returns an index greater than i."
    source := "base/strings/basic.jl:529-534: \"each remaining iteration increases the returned value by `1`\""
    status := .refuted
    prop := ``NextindNIncreasing
    thm := some ``nextindNIncreasing_refuted
    issue := "none found (queries: nextind overflow, nextind typemax, nextind)"
    notes := "nextind(\"a\", 1, typemax(Int)) == typemin(Int): the final `i + n` (base/strings/basic.jl:573) wraps." },
  { id := "strings-chop-head-overflow"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["chop(::AbstractString)"]
    statement := "chop(s; head, tail) with head, tail >= 0 and head + tail >= length(s) returns an empty string."
    source := "base/strings/util.jl:214-217: \"If it is requested to remove more characters than `length(s)` then an empty string is returned.\""
    status := .refuted
    prop := ``ChopTooMany
    thm := some ``chopTooMany_refuted
    issue := "none found (queries: chop head overflow, chop typemax, chop)"
    notes := "chop(\"ab\", head=typemax(Int), tail=0) throws BoundsError: nextind(s, 1, head) wraps negative and SubString(s, negative, 2) fails its bounds check." },
  { id := "strings-partition-overflow"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["iterate(::Base.Iterators.PartitionIterator{<:AbstractString})"]
    statement := "Iterators.partition(s, n) with n >= length(s) yields the whole nonempty string as its first chunk."
    source := "base/iterators.jl:1424-1426: \"Iterate over a collection `n` elements at a time.\""
    status := .refuted
    prop := ``PartitionWhole
    thm := some ``partitionWhole_refuted
    issue := "none found (queries: partition string typemax)"
    notes := "collect(Iterators.partition(\"é€\", typemax(Int))) throws BoundsError: nextind(s, 1, n-1) wraps negative (base/strings/util.jl:816)." },
  { id := "strings-lpad-typemin"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["lpad(::AbstractString, ::Integer)", "rpad(::AbstractString, ::Integer)"]
    statement := "lpad(s, n) returns s unchanged when n <= textwidth(s)."
    source := "base/strings/util.jl:496-499: \"If `s` is already `n` characters long, an equal string is returned.\""
    status := .refuted
    prop := ``LpadNoPad
    thm := some ``lpadNoPad_refuted
    issue := "none found (queries: lpad typemin, lpad negative OutOfMemoryError, lpad overflow, rpad typemin, lpad)"
    notes := "lpad(\"a\", typemin(Int)) throws OutOfMemoryError while lpad(\"a\", -5) == \"a\": signed(n) - textwidth(s) wraps to typemax(Int). rpad has the same code and behaviour. The model takes textwidth(s) as the parameter tw; the counterexample uses tw = textwidth(\"a\") = 1." },
  { id := "strings-findnext-inside-char"
    juliaFile := "base/strings/search.jl"
    juliaFns := ["findnext(::AbstractString, ::AbstractString, ::Integer)", "findfirst(::AbstractString, ::AbstractString)"]
    statement := "findnext(t, s, i) returns a range r with s[r] == t."
    source := "base/strings/search.jl:489-492: \"a range of indices where the matching sequence is found, such that `s[r] == t`\""
    status := .refuted
    prop := ``FindnextMatches
    thm := some ``findnextMatches_refuted
    issue := "none found (queries: findfirst invalid UTF-8, findnext invalid string index, occursin invalid UTF-8, search middle of character)"
    notes := "findfirst(\"\\xa9x\", \"éx\") == 2:3, a match starting inside 'é'; s[2:3] throws StringIndexError. The one-character needle \"\\xa9\" is searched by character and is not found, so occursin(\"\\xa9x\", s) is true while occursin(\"\\xa9\", s) is false. Only needles that are not valid UTF-8 can match inside a character." },
  { id := "strings-findprev-empty-end"
    juliaFile := "base/strings/search.jl"
    juliaFns := ["findprev(::AbstractString, ::AbstractString, ::Integer)"]
    statement := "findprev(t, s, i) returns the last occurrence start:stop with stop <= i: if findnext(t, s, a) reports an occurrence a:b with b <= i <= ncodeunits(s)+1, findprev(t, s, i) returns an occurrence starting at a or later."
    source := "base/strings/search.jl:799-806: \"`findprev(\\\"substring\\\", string, i)` == `start:stop` such that `string[start:stop] == \\\"substring\\\"` and `stop <= i`, or `nothing` if unmatched.\""
    status := .refuted
    prop := ``FindprevLatest
    thm := some ``findprevLatest_refuted
    issue := "none found (queries: findprev empty string, findlast empty string)"
    notes := "findnext(\"\", \"abc\", 4) == 4:3 and findall(\"\", \"abc\") contains 4:3, but findprev(\"\", \"abc\", 4) == 0:-1: the String method returns index 0 for i > sizeof(s) (base/strings/search.jl:713-714). The generic AbstractString method returns 4:3. For nonempty needles the String method also accepts any i > ncodeunits(s)+1 where findnext throws BoundsError." },
  { id := "strings-reverse-malformed"
    juliaFile := "base/strings/stringview.jl"
    juliaFns := ["reverse(::String)"]
    statement := "collect(reverse(s)) == reverse(collect(s)) for every byte string s."
    source := "base/strings/stringview.jl:34: \"this function reverses the codepoints in a string\""
    status := .refuted
    prop := ``ReverseChars
    thm := some ``reverseChars_refuted
    issue := "none found (queries: reverse invalid UTF-8, reverse malformed char, reverse string invalid)"
    notes := "s = \"\\x82\\xe2\": collect(s) == ['\\x82', '\\xe2'] but reverse(s) has bytes e2 82, which decode as the single character '\\xe2\\x82'. Reversing the bytes of malformed characters can merge them." },
  { id := "strings-raw-substring-iterate"
    juliaFile := "base/strings/substring.jl"
    juliaFns := ["raw_substring(::AbstractString, ::Int, ::Int)", "iterate(::SubString, ::Integer)"]
    statement := "A SubString{String} from raw_substring iterates to the end without error, yielding length(ss) characters."
    source := "base/strings/substring.jl:11-14: \"The presence of truncated characters is safe and well-defined for `String`\""
    status := .refuted
    prop := ``RawSubstringIterates
    thm := some ``rawSubstringIterates_refuted
    issue := "none found (queries: raw_substring, truncated SubString, SubString truncated character, SubString iterate BoundsError); related: #59663 (adds raw_substring), #59610 (replaces Val(:noshift))"
    notes := "ss = Base.raw_substring(\"é\", 1, 1): iterate(ss) == ('é', 3), reading a byte past the SubString, and the next iterate(ss, 3) throws BoundsError, so collect(ss) throws. Julia 1.13.2 has the same behaviour for SubString(\"é\", 0, 1, Val(:noshift))." },
  { id := "strings-cmp-malformed"
    juliaFile := "base/strings/string.jl"
    juliaFns := ["cmp(::String, ::String)", "cmp(::AbstractString, ::AbstractString)"]
    statement := "cmp(a::String, b::String) agrees with the generic AbstractString cmp, which compares characters lexicographically."
    source := "base/strings/basic.jl:280-284 (cmp docstring: lexicographical order by Unicode code points); base/strings/basic.jl:307-318"
    status := .refuted
    prop := ``CmpAgreesGeneric
    thm := some ``cmpAgreesGeneric_refuted
    issue := "none found (queries: cmp invalid UTF-8, isless string invalid UTF-8 codeunit)"
    notes := "cmp(\"\\xe2\\xc0\", \"\\xe2\\x82\") == 1 (byte order) but the generic method gives -1, because '\\xe2' < '\\xe2\\x82' as Chars. The two orders agree on valid UTF-8." }
]

end JuliaLean.Strings
