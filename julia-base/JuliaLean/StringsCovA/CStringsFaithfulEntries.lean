import JuliaLean.Registry.Types
import JuliaLean.StringsCovA.CStringsFaithful

namespace JuliaLean.StringsCovA.CStringsFaithfulRegistry

open JuliaLean.Registry

def entries : List Entry := [
  { id := "stringscova-cstring-ctor-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["Cstring(::Ptr)"]
    statement := "Cstring bitcasts a supported pointer to Cstring without changing its address."
    source := "base/strings/cstring.jl:31", status := .proven, prop := ``CStringsFaithful.CstringCtorProperty, thm := some ``CStringsFaithful.cstringCtor_proven },
  { id := "stringscova-cwstring-ctor-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["Cwstring(::Ptr)"]
    statement := "Cwstring bitcasts a supported pointer to Cwstring without changing its address."
    source := "base/strings/cstring.jl:32", status := .proven, prop := ``CStringsFaithful.CwstringCtorProperty, thm := some ``CStringsFaithful.cwstringCtor_proven },
  { id := "stringscova-cstring-ptr-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["Ptr{T}(::Cstring)"]
    statement := "Ptr{T}(Cstring) returns the same address with pointer tag T."
    source := "base/strings/cstring.jl:33", status := .proven, prop := ``CStringsFaithful.PtrCstringProperty, thm := some ``CStringsFaithful.ptrCstring_proven },
  { id := "stringscova-cstring-convert-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["convert(::Type{Cstring}, ::Ptr)"]
    statement := "convert(Cstring,p) calls the Cstring pointer constructor."
    source := "base/strings/cstring.jl:36", status := .proven, prop := ``CStringsFaithful.ConvertCstringProperty, thm := some ``CStringsFaithful.convertCstring_proven },
  { id := "stringscova-cwstring-convert-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["convert(::Type{Cwstring}, ::Ptr)"]
    statement := "convert(Cwstring,p) calls the Cwstring pointer constructor."
    source := "base/strings/cstring.jl:37", status := .proven, prop := ``CStringsFaithful.ConvertCwstringProperty, thm := some ``CStringsFaithful.convertCwstring_proven },
  { id := "stringscova-cstring-convert-ptr-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["convert(::Type{Ptr{T}}, ::Cstring)"]
    statement := "convert(Ptr{T},Cstring) calls the corresponding Ptr{T} constructor."
    source := "base/strings/cstring.jl:38", status := .proven, prop := ``CStringsFaithful.ConvertPtrCstringProperty, thm := some ``CStringsFaithful.convertPtrCstring_proven },
  { id := "stringscova-cwstring-convert-ptr-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["convert(::Type{Ptr{T}}, ::Cwstring)"]
    statement := "convert(Ptr{T},Cwstring) delegates to Ptr{T}(Cwstring)."
    source := "base/strings/cstring.jl:39", status := .proven, prop := ``CStringsFaithful.ConvertPtrCwstringProperty, thm := some ``CStringsFaithful.convertPtrCwstring_proven },
  { id := "stringscova-cstring-pointer-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["pointer(::Cstring)"]
    statement := "pointer(Cstring) converts it to Ptr{Cchar}."
    source := "base/strings/cstring.jl:55", status := .proven, prop := ``CStringsFaithful.PointerCstringProperty, thm := some ``CStringsFaithful.pointerCstring_proven },
  { id := "stringscova-cwstring-pointer-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["pointer(::Cwstring)"]
    statement := "pointer(Cwstring) converts it to Ptr{Cwchar_t}."
    source := "base/strings/cstring.jl:56", status := .proven, prop := ``CStringsFaithful.PointerCwstringProperty, thm := some ``CStringsFaithful.pointerCwstring_proven },
  { id := "stringscova-cstring-eq-ptr-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["==(::Union{Cstring,Cwstring}, ::Ptr)"]
    statement := "C-string equality with a pointer compares the converted address."
    source := "base/strings/cstring.jl:59", status := .proven, prop := ``CStringsFaithful.EqCptrProperty, thm := some ``CStringsFaithful.eqCptr_proven },
  { id := "stringscova-ptr-eq-cstring-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["==(::Ptr, ::Union{Cstring,Cwstring})"]
    statement := "Pointer equality with a C string compares against the converted address."
    source := "base/strings/cstring.jl:60", status := .proven, prop := ``CStringsFaithful.EqPtrCProperty, thm := some ``CStringsFaithful.eqPtrC_proven },
  { id := "stringscova-cstring-unsafe-string-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_string(::Cstring)"]
    statement := "unsafe_string(Cstring) converts to Ptr{UInt8} and copies through the first NUL."
    source := "base/strings/cstring.jl:62", status := .proven, prop := ``CStringsFaithful.UnsafeStringCstringProperty, thm := some ``CStringsFaithful.unsafeStringCstring_proven },
  { id := "stringscova-cstring-cconvert-string-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["cconvert(::Type{Cstring}, ::String)"]
    statement := "cconvert(Cstring,String) returns the same String."
    source := "base/strings/cstring.jl:65", status := .proven, prop := ``CStringsFaithful.CconvertStringProperty, thm := some ``CStringsFaithful.cconvertString_proven },
  { id := "stringscova-cstring-cconvert-abstract-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["cconvert(::Type{Cstring}, ::AbstractString)"]
    statement := "cconvert(Cstring,AbstractString) preserves String conversion failures and otherwise returns the converted concrete String."
    source := "base/strings/cstring.jl:66-67", status := .proven, prop := ``CStringsFaithful.CconvertAbstractProperty, thm := some ``CStringsFaithful.cconvertAbstract_proven },
  { id := "stringscova-cwstring-cconvert-abstract-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["cconvert(::Type{Cwstring}, ::AbstractString)"]
    statement := "cconvert(Cwstring,AbstractString) first constructs a String, transcodes to the platform wide type, appends NUL, and applies the wide-vector checks in order."
    source := "base/strings/cstring.jl:69-73", status := .proven, prop := ``CStringsFaithful.CconvertCwstringProperty, thm := some ``CStringsFaithful.cconvertCwstring_proven },
  { id := "stringscova-cstring-eltype-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["eltype(::Type{Cstring})"]
    statement := "eltype(Cstring) is Cchar."
    source := "base/strings/cstring.jl:75", status := .proven, prop := ``CStringsFaithful.EltypeCstringProperty, thm := some ``CStringsFaithful.eltypeCstring_proven },
  { id := "stringscova-cwstring-eltype-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["eltype(::Type{Cwstring})"]
    statement := "eltype(Cwstring) is Cwchar_t."
    source := "base/strings/cstring.jl:76", status := .proven, prop := ``CStringsFaithful.EltypeCwstringProperty, thm := some ``CStringsFaithful.eltypeCwstring_proven },
  { id := "stringscova-containsnul-ptr-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["containsnul(::Ptr, len)"]
    statement := "containsnul calls memchr for zero over exactly len bytes."
    source := "base/strings/cstring.jl:78-79", status := .proven, prop := ``CStringsFaithful.ContainsnulPtrProperty, thm := some ``CStringsFaithful.containsnulPtr_proven },
  { id := "stringscova-containsnul-string-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["containsnul(::String)"]
    statement := "String NUL detection converts the storage pointer and scans exactly sizeof(s) bytes, excluding the trailing terminator."
    source := "base/strings/cstring.jl:80", status := .proven, prop := ``CStringsFaithful.ContainsnulStringProperty, thm := some ``CStringsFaithful.containsnulString_proven },
  { id := "stringscova-containsnul-abstract-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["containsnul(::AbstractString)"]
    statement := "AbstractString NUL detection propagates iteration failures and otherwise reports whether the character sequence contains NUL."
    source := "base/strings/cstring.jl:81", status := .proven, prop := ``CStringsFaithful.ContainsnulAbstractProperty, thm := some ``CStringsFaithful.containsnulAbstract_proven },
  { id := "stringscova-cstring-unsafe-string-convert-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_convert(::Type{Cstring}, ::String)"]
    statement := "String-to-Cstring conversion obtains the storage pointer, scans exactly the String bytes for embedded NUL, throws when one is present, and otherwise preserves the address."
    source := "base/strings/cstring.jl:83-88", status := .proven, prop := ``CStringsFaithful.UnsafeConvertCstringProperty, thm := some ``CStringsFaithful.unsafeConvertCstring_proven },
  { id := "stringscova-cstring-unsafe-memory-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_convert(::Type{Cstring}, ::Memory)"]
    statement := "unsafe_convert(Cstring,Memory) converts the Memory storage to Ptr{Cvoid} and then constructs a Cstring with the same address."
    source := "base/strings/cstring.jl:90", status := .proven, prop := ``CStringsFaithful.UnsafeConvertMemoryProperty, thm := some ``CStringsFaithful.unsafeConvertMemory_proven },
  { id := "stringscova-cwstring-cconvert-vector-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"]
    statement := "Wide-vector conversion rejects embedded NULs before the last element, requires a final NUL, and preserves every accepted vector."
    source := "base/strings/cstring.jl:92-100", status := .proven, prop := ``CStringsFaithful.CconvertCwstringVectorProperty, thm := some ``CStringsFaithful.cconvertCwstringVector_proven },
  { id := "stringscova-cwstring-unsafe-generic-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_convert(::Type{Cwstring}, s)"]
    statement := "unsafe_convert(Cwstring,s) converts s to Ptr{Cwchar_t} and constructs Cwstring."
    source := "base/strings/cstring.jl:101", status := .proven, prop := ``CStringsFaithful.UnsafeConvertWideProperty, thm := some ``CStringsFaithful.unsafeConvertWide_proven },
  { id := "stringscova-cwstring-unsafe-identity-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_convert(::Type{Cwstring}, ::Cwstring)"]
    statement := "unsafe_convert(Cwstring,Cwstring) is the identity."
    source := "base/strings/cstring.jl:102", status := .proven, prop := ``CStringsFaithful.UnsafeConvertWideIdentityProperty, thm := some ``CStringsFaithful.unsafeConvertWideIdentity_proven },
  { id := "stringscova-cstring-cconvert-symbol-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["cconvert(::Type{Cstring}, ::Symbol)"]
    statement := "cconvert(Cstring,Symbol) returns the Symbol."
    source := "base/strings/cstring.jl:105", status := .proven, prop := ``CStringsFaithful.CconvertSymbolProperty, thm := some ``CStringsFaithful.cconvertSymbol_proven },
  { id := "stringscova-cstring-unsafe-symbol-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_convert(::Type{Cstring}, ::Symbol)"]
    statement := "unsafe_convert(Cstring,Symbol) converts that Symbol to Ptr{Cchar} and constructs a Cstring with the resulting address."
    source := "base/strings/cstring.jl:106", status := .proven, prop := ``CStringsFaithful.UnsafeConvertSymbolProperty, thm := some ``CStringsFaithful.unsafeConvertSymbol_proven },
  { id := "stringscova-transcode-identity-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(::Type{T}, ::AbstractVector{T})"]
    statement := "Transcoding a vector to its own code-unit type returns the same vector."
    source := "base/strings/cstring.jl:163", status := .proven, prop := ``CStringsFaithful.TranscodeIdentityProperty, thm := some ``CStringsFaithful.transcodeIdentity_proven },
  { id := "stringscova-transcode-string32-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(::Type{T}, ::String) where T<:Union{Int32,UInt32}"]
    statement := "String-to-32-bit transcode iterates characters, converts each in order to the selected Int32 or UInt32 representation, and preserves the first conversion failure."
    source := "base/strings/cstring.jl:164", status := .proven, prop := ``CStringsFaithful.TranscodeString32Property, thm := some ``CStringsFaithful.transcodeString32_proven },
  { id := "stringscova-transcode-bytes32-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(::Type{T}, ::AbstractVector{UInt8})"]
    statement := "UTF-8 vector to 32-bit transcode copies to a Vector, constructs a String, and invokes the String method."
    source := "base/strings/cstring.jl:165-166", status := .proven, prop := ``CStringsFaithful.TranscodeBytes32Property, thm := some ``CStringsFaithful.transcodeBytes32_proven },
  { id := "stringscova-transcode-codeunits32-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(::Type{T}, ::CodeUnits{UInt8,String})"]
    statement := "UTF-8 String CodeUnits to 32-bit transcode constructs the parent String and invokes the String method."
    source := "base/strings/cstring.jl:167-168", status := .proven, prop := ``CStringsFaithful.TranscodeCodeunits32Property, thm := some ``CStringsFaithful.transcodeCodeunits32_proven },
  { id := "stringscova-transcode-32-to-bytes-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(::Type{UInt8}, ::Vector{<:Union{Int32,UInt32}})"]
    statement := "32-bit-to-UTF-8 transcode converts and prints each source element before advancing, so output order and the first conversion failure match the source loop."
    source := "base/strings/cstring.jl:170-176", status := .proven, prop := ``CStringsFaithful.Transcode8of32Property, thm := some ``CStringsFaithful.transcode8of32_proven },
  { id := "stringscova-transcode-string-identity-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(::Type{String}, ::String)"]
    statement := "transcode(String,String) returns its input."
    source := "base/strings/cstring.jl:177", status := .proven, prop := ``CStringsFaithful.TranscodeStringIdentityProperty, thm := some ``CStringsFaithful.transcodeStringIdentity_proven },
  { id := "stringscova-transcode-string-codeunits-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(T, ::String)"]
    statement := "Generic transcode from String invokes transcode on its codeunits."
    source := "base/strings/cstring.jl:178", status := .proven, prop := ``CStringsFaithful.TranscodeStringCodeunitsProperty, thm := some ``CStringsFaithful.transcodeStringCodeunits_proven },
  { id := "stringscova-transcode-vector-string-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(::Type{String}, ::Vector{UInt8})"]
    statement := "Vector{UInt8} to String transcode copies through a full view, preserves every byte, and leaves the caller's vector unchanged."
    source := "base/strings/cstring.jl:182", status := .proven, prop := ``CStringsFaithful.TranscodeVectorStringProperty, thm := some ``CStringsFaithful.transcodeVectorString_proven },
  { id := "stringscova-transcode-to-string-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["transcode(::Type{String}, src)"]
    statement := "Generic transcode to String first transcodes to UInt8 and constructs a String from those bytes."
    source := "base/strings/cstring.jl:183", status := .proven, prop := ``CStringsFaithful.TranscodeToStringProperty, thm := some ``CStringsFaithful.transcodeToString_proven },
  { id := "stringscova-unsafe-wide-length-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_string(::Ptr{T}, ::Integer)"]
    statement := "For every valid pointer and nonnegative Integer length, wide unsafe_string wraps exactly that many units without ownership and transcodes them to String."
    source := "base/strings/cstring.jl:321-323", status := .proven, prop := ``CStringsFaithful.UnsafeStringWideLengthProperty, thm := some ``CStringsFaithful.unsafeStringWideLength_proven },
  { id := "stringscova-unsafe-wide-nul-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_string(::Ptr{T})"]
    statement := "For every documented valid NUL-terminated pointer, wide unsafe_string loads consecutive units from index one, excludes the first zero, and calls the length-qualified method."
    source := "base/strings/cstring.jl:324-330", status := .proven, prop := ``CStringsFaithful.UnsafeStringWideProperty, thm := some ``CStringsFaithful.unsafeStringWide_proven },
  { id := "stringscova-unsafe-cwstring-faithful", juliaFile := "base/strings/cstring.jl", juliaFns := ["unsafe_string(::Cwstring)"]
    statement := "unsafe_string(Cwstring) converts it to Ptr{Cwchar_t} and calls wide unsafe_string."
    source := "base/strings/cstring.jl:331", status := .proven, prop := ``CStringsFaithful.UnsafeStringCwstringProperty, thm := some ``CStringsFaithful.unsafeStringCwstring_proven }
]

end JuliaLean.StringsCovA.CStringsFaithfulRegistry
