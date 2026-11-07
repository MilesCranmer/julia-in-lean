import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.strings.lazy.coverage
import JuliaLean.Proofs.base.strings.stringview.coverage
import JuliaLean.Proofs.base.strings.cstring.coverage
import JuliaLean.Proofs.base.strings.basic.coverage
import JuliaLean.Proofs.base.strings.substring.coverage
import JuliaLean.Proofs.base.strings.search.coverage
import JuliaLean.Proofs.base.strings.util.coverage
import JuliaLean.Proofs.base.strings.string.coverage
import JuliaLean.Proofs.base.strings.lazy.faithful_entries
import JuliaLean.Proofs.base.strings.cstring.faithful_entries
import JuliaLean.Proofs.base.strings.stringview.faithful_entries
import JuliaLean.Proofs.base.strings.stringview.rebuilt_entries
import JuliaLean.Proofs.base.strings.substring.faithful_ctor_entries
import JuliaLean.Proofs.base.strings.substring.faithful_access_entries
import JuliaLean.Proofs.base.strings.substring.faithful_final_entries
import JuliaLean.Proofs.base.strings.substring.rebuilt_entries
import JuliaLean.Proofs.base.strings.basic.faithful_entries
import JuliaLean.Proofs.base.strings.basic.rebuilt_entries
import JuliaLean.Proofs.base.strings.search.faithful_entries
import JuliaLean.Proofs.base.strings.search.rebuilt_entries
import JuliaLean.Proofs.base.strings.util.faithful_entries
import JuliaLean.Proofs.base.strings.util.rebuilt_entries
import JuliaLean.Proofs.base.strings.util.review_extras
import JuliaLean.Proofs.base.strings.string.faithful_entries
import JuliaLean.Proofs.base.strings.string.rebuilt_entries

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
