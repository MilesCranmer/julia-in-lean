import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Strings.Search
import JuliaLean.Strings.Length

namespace JuliaLean.Strings

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "strings-reverse-malformed"
    juliaFile := "base/strings/stringview.jl"
    juliaFns := ["reverse(::String)"]
    statement := "collect(reverse(s)) == reverse(collect(s)) for every byte string s."
    source := "base/strings/stringview.jl:34: \"this function reverses the codepoints in a string\""
    status := .refuted
    prop := ``ReverseChars
    thm := some ``reverseChars_refuted
    issue := "none found (queries: reverse invalid UTF-8, reverse malformed char, reverse string invalid)"
    notes := "s = \"\\x82\\xe2\": collect(s) == ['\\x82', '\\xe2'] but reverse(s) has bytes e2 82, which decode as the single character '\\xe2\\x82'. Reversing the bytes of malformed characters can merge them." }
]

end JuliaLean.Strings
