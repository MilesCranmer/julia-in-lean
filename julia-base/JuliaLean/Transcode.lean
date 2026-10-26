import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Transcode.Props

namespace JuliaLean.Transcode

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "transcode-utf8-utf16-total"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{UInt16}, ::AbstractVector{UInt8})", "transcode(::Type{UInt16}, ::String)"]
    statement := "transcode(UInt16, src) returns for every byte vector, valid UTF-8 or not (overlong forms, surrogates, truncated sequences, stray continuation bytes, bytes F5-FF), and never reads past the end of src."
    source := "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\""
    status := .proven
    prop := ``Utf8ToUtf16Total
    thm := some ``utf8ToUtf16Total_proven
    notes := "Every src[i += 1] (cstring.jl:194,202,209,231) is guarded by i < n; the model reads through nextB, which throws BoundsError past the end. Differential test: 61238 byte vectors (all of length <= 1, all non-ASCII-led pairs, 25000 random UTF-8-like vectors), 0 mismatches against nightly." },
  { id := "transcode-utf16-utf8-complete"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{UInt8}, ::AbstractVector{UInt16})", "transcode(::Type{String}, ::Vector{UInt16})"]
    statement := "transcode(UInt8, src::Vector{UInt16}) returns for every code-unit vector, unpaired surrogates included; its first loop allocates exactly the number of bytes its second loop writes, so no write leaves StringVector(m) and no byte of it stays uninitialized."
    source := "base/strings/cstring.jl:140-142 (always succeeds); cstring.jl:241-246 (sizes are precomputed so that dst is never grown); invariant"
    status := .proven
    prop := ``Utf16ToUtf8Complete
    thm := some ``utf16ToUtf8Complete_proven
    notes := "Vectors shorter than 2^60 elements. Differential test: all 65536 single units and 25000 random surrogate-heavy vectors, 0 mismatches." },
  { id := "transcode-utf32-invalid"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{UInt32}, ::String)", "transcode(::Type{Int32}, ::String)", "cconvert(::Type{Cwstring}, ::AbstractString)"]
    statement := "transcode(UInt32, s) returns for every String s."
    source := "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\""
    status := .refuted
    prop := ``Utf8ToUtf32Total
    thm := some ``utf8ToUtf32Total_refuted
    issue := "none found (queries: transcode, transcode UInt32 invalid, transcode InvalidCharError, transcode UTF-32 invalid UTF-8, transcode Cwchar_t invalid, Cwstring invalid UTF-8, transcode always succeeds; prs: transcode)"
    notes := "transcode(UInt32, \"a\\xffb\") throws InvalidCharError while transcode(UInt16, \"a\\xffb\") == [0x61, 0xff, 0x62]. On Linux/macOS (Cwchar_t = Int32) every Cwstring ccall argument goes through this method. Julia 1.13.2 additionally throws for overlong forms such as \"\\xc0\\x80\" (its codepoint(::Char) rejects them); master returns 0 for that one." },
  { id := "transcode-utf32-out-of-range"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{UInt8}, ::Vector{UInt32})", "transcode(::Type{String}, ::Vector{UInt32})", "unsafe_string(::Ptr{UInt32}, ::Integer)"]
    statement := "transcode(UInt8, v::Vector{UInt32}) returns for every vector v."
    source := "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\""
    status := .refuted
    prop := ``Utf32ToUtf8Total
    thm := some ``utf32ToUtf8Total_refuted
    issue := "none found (queries: transcode, transcode CodePointError, transcode always succeeds; prs: transcode)"
    notes := "transcode(String, UInt32[0x61, 0x200000]) throws CodePointError (Char(::UInt32) rejects values >= 2^21); the Int32 method throws InexactError for negative values. Values 0x110000-0x1fffff are encoded without error. Differential test of both methods: 16000 vectors, 0 mismatches." },
  { id := "transcode-utf16-roundtrip"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{UInt16}, ::String)", "transcode(::Type{String}, ::Vector{UInt16})"]
    statement := "transcode(String, transcode(UInt16, s)) == s for every valid (well-formed UTF-8) string s, and transcode(UInt8, ...) allocates exactly ncodeunits(s) bytes."
    source := "base/strings/cstring.jl:157-158 (doctest transcode(String, transcode(UInt16, str)) == str); invariant"
    status := .proven
    prop := ``RoundTrip16
    thm := some ``roundTrip16_proven
    notes := "Valid = Unicode Table 3-7 (no overlong forms, surrogates or code points above U+10FFFF); strings shorter than 2^60 bytes. Per-character facts are checked exhaustively by the kernel (Transcode/Tables.lean)." },
  { id := "transcode-utf16-wellformed"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{UInt16}, ::String)"]
    statement := "For a valid string s, transcode(UInt16, s) is well-formed UTF-16: every high surrogate is immediately followed by a low surrogate, and every low surrogate immediately follows a high surrogate."
    source := "invariant (UTF-16 output of valid input; Unicode D91)"
    status := .proven
    prop := ``Utf16WellFormed
    thm := some ``utf16WellFormed_proven },
  { id := "transcode-utf16-length"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{UInt16}, ::String)", "length(::String)"]
    statement := "For a valid string s, length(transcode(UInt16, s)) == length(s) + count(>=(0xf0), codeunits(s)): one code unit per character and two for characters outside the BMP."
    source := "invariant"
    status := .proven
    prop := ``Utf16Length
    thm := some ``utf16Length_proven
    notes := "length(s) is the Strings model of length(::String) (base/strings/string.jl:631-658)." },
  { id := "transcode-utf32-length"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{UInt32}, ::String)", "length(::String)"]
    statement := "Whenever transcode(UInt32, s) returns, length(transcode(UInt32, s)) == length(s), for any byte string s."
    source := "invariant (one UTF-32 code unit per character)"
    status := .proven
    prop := ``Utf32Length
    thm := some ``utf32Length_proven },
  { id := "transcode-containsnul-agree"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["containsnul(::String)", "containsnul(::AbstractString)"]
    statement := "containsnul(s::String), a memchr for a zero byte, equals containsnul(s::AbstractString) = '\\0' in s for every byte string s, valid or not."
    source := "base/strings/cstring.jl:78-81; invariant"
    status := .proven
    prop := ``ContainsnulAgree
    thm := some ``containsnulAgree_proven },
  { id := "transcode-cstring-nul-check"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["unsafe_convert(::Type{Cstring}, ::String)", "ccall with Cstring arguments"]
    statement := "unsafe_convert(Cstring, s::String) throws ArgumentError exactly when '\\0' in s; otherwise the C function receives all of s's bytes, none of them NUL."
    source := "base/strings/cstring.jl:83-88; Cstring docstring (cstring.jl:21-22): \"Cstrings are NUL-terminated\""
    status := .proven
    prop := ``CstringNulCheck
    thm := some ``cstringNulCheck_proven
    notes := "Differential test of containsnul (String and SubString) and unsafe_convert(Cstring, ...) on 61238 byte strings, 0 mismatches." },
  { id := "transcode-cwstring-nul-terminated"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["cconvert(::Type{Cwstring}, ::AbstractString)", "cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"]
    statement := "cconvert(Cwstring, s) passes NUL-terminated data without an embedded NUL to C, both on Windows (Cwchar_t = UInt16) and on Linux/macOS (Cwchar_t = Int32)."
    source := "Cwstring docstring (base/strings/cstring.jl:8-9): \"Cwstrings are NUL-terminated\"; cstring.jl:92-100"
    status := .proven
    prop := ``CwstringNulTerminated
    thm := some ``cwstringNulTerminated_proven
    notes := "Because the check runs on the transcoded data, an overlong NUL such as \"a\\xc0\\x80b\" is rejected with ArgumentError on Windows and on master; Julia 1.13.2 on Linux throws InvalidCharError for it instead (transcode-utf32-invalid)." },
  { id := "transcode-cwstring-overlong-nul"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["Base.cwstring(::AbstractString)"]
    statement := "Base.cwstring(s) returns UTF-16 data whose only NUL is the terminator."
    source := "base/strings/cstring.jl:112-113: \"Convert a string s to a NUL-terminated Vector{Cwchar_t}, suitable for passing to C functions\"; the embedded-NUL check at :121"
    status := .refuted
    prop := ``CwstringNoEmbeddedNul
    thm := some ``cwstringNoEmbeddedNul_refuted
    issue := "none found; related #25452 (overlong decoding), #56795 (cwstring NUL check) (queries: cwstring, Cwstring, cwstring overlong, cwstring NUL, overlong NUL transcode, transcode overlong; prs: transcode)"
    notes := "cwstring(\"\\xc0\\x80\") == UInt16[0, 0]: the NUL check looks at the UTF-8 bytes, but transcode(UInt16, ...) decodes the overlong forms c0 80, e0 80 80 and f0 80 80 80 to 0x0000. Windows only (ENV, longpath, homedir lookup, clipboard use cwstring); the reproducer runs cwstring's body on Linux." },
  { id := "transcode-cwstring-empty-vector"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"]
    statement := "cconvert(Cwstring, v::Vector{Cwchar_t}) throws ArgumentError for every v that is not NUL-terminated."
    source := "base/strings/cstring.jl:97-98: v[end] == 0 || throw(ArgumentError(\"C string data must be NUL terminated: ...\"))"
    status := .refuted
    prop := ``CwstringVectorCheck
    thm := some ``cwstringVectorCheck_refuted
    issue := "none found (queries: Cwstring, Cwstring empty vector BoundsError, C string data must be NUL terminated, embedded NULs Cwstring)"
    notes := "Cwchar_t[] throws BoundsError from v[end]." },
  { id := "transcode-unsafe-string-nul"
    juliaFile := "base/strings/cstring.jl"
    juliaFns := ["unsafe_string(::Ptr{UInt16})", "unsafe_string(::Ptr{UInt16}, ::Integer)"]
    statement := "unsafe_string(p::Ptr{UInt16}) reads the code units up to and including the first NUL and nothing after it, and returns transcode(String, ...) of the units before the NUL."
    source := "base/strings/cstring.jl:309-319 (unsafe_string docstring: C-style NUL-terminated data)"
    status := .proven
    prop := ``UnsafeStringNul
    thm := some ``unsafeStringNul_proven
    notes := "Readable memory shorter than 2^60 units; a read outside it is modelled as an error, so the theorem also shows no read past the NUL." },
  { id := "transcode-string-vector-alias"
    juliaFile := "base/strings/string.jl"
    juliaFns := ["String(::Vector{UInt8})", "jl_genericmemory_to_string (src/genericmemory.c)"]
    statement := "Once String(v) has returned a String, no later operation on arrays changes its bytes."
    source := "base/strings/string.jl:85: \"Strings are immutable sequences of Chars\"; string.jl:100-101"
    status := .refuted
    prop := ``StringVectorImmutable
    thm := some ``stringVectorImmutable_refuted
    issue := "none found; related #56435 (closed; a comment there names this hazard) (queries: jl_genericmemory_to_string, String reshape take! mutate, String(v) aliasing reshape, String immutable mutated Vector{UInt8} shared memory, String constructor shares memory wrap, String mutable reshape, immutable String modified; prs: jl_genericmemory_to_string)"
    notes := "For v over string-owned memory (take!, read(io, nb), StringVector), String(v) returns the owning String object without copying; another array over the same memory (reshape, vec) can then write into the String, and a later String(w) on such an array returns the same object with a new length (stringVector_truncate)." }
]

end JuliaLean.Transcode
