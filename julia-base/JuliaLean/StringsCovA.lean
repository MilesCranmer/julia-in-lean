import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.StringsCovA.Lazy
import JuliaLean.StringsCovA.StringView
import JuliaLean.StringsCovA.CStrings
import JuliaLean.StringsCovA.Basic
import JuliaLean.StringsCovA.Substring
import JuliaLean.StringsCovA.Search
import JuliaLean.StringsCovA.Util
import JuliaLean.StringsCovA.String
import JuliaLean.StringsCovA.LazyFaithfulEntries
import JuliaLean.StringsCovA.CStringsFaithfulEntries
import JuliaLean.StringsCovA.StringViewFaithfulEntries
import JuliaLean.StringsCovA.StringViewRebuiltEntries
import JuliaLean.StringsCovA.SubstringFaithfulCtorEntries
import JuliaLean.StringsCovA.SubstringFaithfulAccessEntries
import JuliaLean.StringsCovA.SubstringFaithfulFinalEntries
import JuliaLean.StringsCovA.SubstringRebuiltEntries
import JuliaLean.StringsCovA.BasicFaithfulEntries
import JuliaLean.StringsCovA.BasicRebuiltEntries
import JuliaLean.StringsCovA.SearchFaithfulEntries
import JuliaLean.StringsCovA.SearchRebuiltEntries
import JuliaLean.StringsCovA.UtilFaithfulEntries
import JuliaLean.StringsCovA.UtilRebuiltEntries
import JuliaLean.StringsCovA.UtilReviewExtras
import JuliaLean.StringsCovA.StringFaithfulEntries
import JuliaLean.StringsCovA.StringRebuiltEntries

namespace JuliaLean.StringsCovA

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "stringscova-stringview-storage", juliaFile := "base/strings/stringview.jl"
    juliaFns := ["StringView(::AbstractVector{UInt8})", "Vector{UInt8}(::StringViewAndSub)",
      "Array{UInt8}(::StringViewAndSub)", "String(::StringViewAndSub)", "copy(::StringView)",
      "Symbol(::DenseStringViewAndSub)", "pointer(::DenseStringView)",
      "pointer(::DenseStringView, ::Integer)", "pointer(::SubString{<:DenseStringView})",
      "pointer(::SubString{<:DenseStringView}, ::Integer)",
      "unsafe_convert(::Type{Ptr{UInt8}}, ::DenseStringViewAndSub)",
      "unsafe_convert(::Type{Ptr{Int8}}, ::DenseStringViewAndSub)",
      "String(::DenseStringViewAndSub)", "cconvert(::Type{Ptr{UInt8}}, ::DenseStringViewAndSub)",
      "cconvert(::Type{Ptr{Int8}}, ::DenseStringViewAndSub)"]
    statement := "StringView construction preserves the byte storage, conversions copy or expose those bytes as specified, and pointer conversions preserve the base address plus the SubString offset."
    source := "base/strings/stringview.jl:8-29", status := .proven
    prop := ``StringView.StorageContract, thm := some ``StringView.storageContract },
  { id := "stringscova-stringview-bytes", juliaFile := "base/strings/stringview.jl"
    juliaFns := ["sizeof(::StringView)", "ncodeunits(::StringView)", "codeunit(::StringView)",
      "codeunit(::StringView, ::Integer)", "codeunits(::StringView)",
      "codeunits(::SubString{<:StringView})", "cmp(::UTF8String, ::UTF8String)",
      "==(::UTF8String, ::UTF8String)"]
    statement := "StringView byte access, comparison, and equality operate on exactly the wrapped byte range, with UInt8 code units and ordinary bounds checking."
    source := "base/strings/stringview.jl:85-95", status := .proven
    prop := ``StringView.ByteContract, thm := some ``StringView.byteContract },
  { id := "stringscova-stringview-empty-constructor", juliaFile := "base/strings/stringview.jl"
    juliaFns := ["typemin(::Type{StringView{V}}) where V"]
    statement := "typemin(StringView{V}) returns an empty StringView for every permitted backing-vector type V."
    source := "base/strings/stringview.jl:97-99 (comment: typemin and one is the empty string)"
    status := .refuted, prop := ``StringViewFaithful.TypeminTypeProperty
    thm := some ``StringViewFaithful.typeminType_refuted
    issue := "none found (queries: StringView typemin; StringView one empty; StringView SubArray MethodError)"
    notes := "A StringView backed by a SubArray makes all three generic operations call SubArray(), which throws MethodError. StringView is absent from Julia 1.13.2; reproduced on master bbfa0ce4150." },
  { id := "stringscova-stringview-behavior", juliaFile := "base/strings/stringview.jl"
    juliaFns := ["isascii(::StringViewAndSub)", "hash(::DenseStringViewAndSub, ::UInt)",
      "write(::IO, ::StringViewAndSub)", "print(::IO, ::StringViewAndSub)",
      "thisind(::StringViewAndSub, ::Integer)", "thisind(::StringViewAndSub, ::Int)",
      "nextind(::StringViewAndSub, ::Integer)", "nextind(::StringViewAndSub, ::Int)",
      "isvalid(::StringViewAndSub, ::Int)"]
    statement := "ASCII checking, hashing, output, and UTF-8 index operations delegate to the wrapped bytes and preserve their documented return conventions."
    source := "base/strings/stringview.jl:105-122", status := .proven
    prop := ``StringView.BehaviorContract, thm := some ``StringView.behaviorContract },
  { id := "stringscova-stringview-slice-chomp-replace", juliaFile := "base/strings/stringview.jl"
    juliaFns := ["getindex(::StringView, ::UnitRange{Int})", "chomp(::StringViewAndSub)",
      "replace(::IO, ::DenseStringViewAndSub, ::Pair...; count)"]
    statement := "StringView range indexing checks endpoints and returns the selected bytes, chomp removes one LF or CRLF suffix, and replace delegates with the requested count."
    source := "base/strings/stringview.jl:124-155", status := .proven
    prop := ``StringView.SliceChompReplaceContract,
    thm := some ``StringView.sliceChompReplaceContract }
] ++ LazyFaithfulRegistry.entries ++ CStringsFaithfulRegistry.entries ++ StringViewFaithfulRegistry.entries ++
  StringViewRebuiltRegistry.entries ++
  SubstringFaithfulCtorRegistry.entries ++ SubstringFaithfulAccessRegistry.entries ++
  SubstringFaithfulFinalRegistry.entries ++ BasicFaithfulRegistry.entries ++
  SubstringRebuiltRegistry.entries ++
  BasicRebuiltRegistry.entries ++
  SearchFaithfulRegistry.entries ++ SearchRebuiltRegistry.entries ++
  UtilFaithfulRegistry.entries ++ UtilRebuiltRegistry.entries ++ UtilReviewExtras.entries ++
  StringFaithfulRegistry.entries ++ StringRebuiltRegistry.entries

end JuliaLean.StringsCovA
