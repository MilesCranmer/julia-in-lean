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
import JuliaLean.StringsCovA.UtilFaithfulEntries
import JuliaLean.StringsCovA.StringFaithfulEntries

namespace JuliaLean.StringsCovA

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "stringscova-lazy-construction", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["_LazyString(parts, str)", "LazyString(args...; compact::Bool=false)",
      "lazy_str(text, flags...)"]
    statement := "Both constructors preserve their parts and selected compact/cache state, and @lazy_str builds the corresponding lazy value from its parsed literal and interpolation parts."
    source := "base/strings/lazy.jl:36-43,45-87", status := .proven
    prop := ``Lazy.ConstructionContract, thm := some ``Lazy.constructionContract },
  { id := "stringscova-lazy-materialization", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["String(::LazyString)"]
    statement := "String(l) returns the cached bytes when present and otherwise returns the concatenated printed parts."
    source := "base/strings/lazy.jl:24-34,89-101", status := .proven
    prop := ``Lazy.MaterializationContract, thm := some ``Lazy.materializationContract },
  { id := "stringscova-lazy-forwarders", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["hash(::LazyString, ::UInt64)", "lastindex(::LazyString)",
      "iterate(::LazyString)", "iterate(::LazyString, ::Integer)",
      "isequal(::LazyString, ::LazyString)", "==(::LazyString, ::LazyString)",
      "ncodeunits(::LazyString)", "codeunit(::LazyString)",
      "codeunit(::LazyString, ::Integer)", "codeunits(::LazyString)",
      "isvalid(::LazyString, ::Integer)"]
    statement := "Every AbstractString operation materializes the LazyString and delegates to the corresponding String operation; ncodeunits and codeunits expose the resulting bytes and codeunit type is UInt8."
    source := "base/strings/lazy.jl:103-113", status := .proven
    prop := ``Lazy.ForwardingContract, thm := some ``Lazy.forwardingContract },
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
    thm := some ``StringView.sliceChompReplaceContract },
  { id := "stringscova-cstring-pointer-conversions", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["Cstring(::Ptr)", "Cwstring(::Ptr)", "Ptr{T}(::Cstring)",
      "convert(::Type{Cstring}, ::Ptr)", "convert(::Type{Cwstring}, ::Ptr)",
      "convert(::Type{Ptr{T}}, ::Cstring)"]
    statement := "C string pointer constructors and conversions preserve the address and requested pointer tag."
    source := "base/strings/cstring.jl:30-39", status := .proven
    prop := ``CStrings.PointerConversions, thm := some ``CStrings.pointerConversions },
  { id := "stringscova-cwstring-pointer-type", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["Ptr{T}(::Cwstring)"]
    statement := "Converting a Cwstring to Ptr{T} returns a value of the requested Ptr{T} type."
    source := "constructor and conversion invariant; base/strings/cstring.jl:34,39"
    status := .refuted, prop := ``CStringsFaithful.PtrCwstringProperty
    thm := some ``CStringsFaithful.ptrCwstring_refuted
    issue := "#64224 (open, exact duplicate)"
    notes := "Ptr{Cvoid}(Cwstring(C_NULL)) has runtime type Ptr{Int32} on both tested versions because line 34 ignores T." },
  { id := "stringscova-cstring-pointer-operations", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["pointer(::Cstring)", "pointer(::Cwstring)", "==(::Cstring,::Ptr)",
      "==(::Ptr,::Cstring)", "unsafe_string(::Cstring)"]
    statement := "Pointer access and comparison preserve addresses, and unsafe_string reads bytes through the first NUL."
    source := "base/strings/cstring.jl:55-62", status := .proven
    prop := ``CStrings.PointerOperations, thm := some ``CStrings.pointerOperations },
  { id := "stringscova-cstring-conversion-wrappers", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["cconvert(::Type{Cstring}, ::String)", "cconvert(::Type{Cstring}, ::AbstractString)",
      "eltype(::Type{Cstring})", "eltype(::Type{Cwstring})", "containsnul(::Ptr, len)",
      "unsafe_convert(::Type{Cstring}, ::Memory)", "unsafe_convert(::Type{Cwstring}, ::Any)",
      "unsafe_convert(::Type{Cwstring}, ::Cwstring)", "cconvert(::Type{Cstring}, ::Symbol)",
      "unsafe_convert(::Type{Cstring}, ::Symbol)"]
    statement := "C conversion wrappers preserve their input bytes or address, report native element types, and scan exactly the requested pointer prefix for NUL."
    source := "base/strings/cstring.jl:64-106", status := .proven
    prop := ``CStrings.ConversionOperations, thm := some ``CStrings.conversionOperations },
  { id := "stringscova-transcode-wrappers", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{T}, ::AbstractVector{T})", "transcode(::Type{T}, ::String)",
      "transcode(::Type{T}, ::AbstractVector{UInt8})", "transcode(::Type{T}, ::CodeUnits{UInt8,String})",
      "transcode(::Type{UInt8}, ::Vector{UInt32})", "transcode(::Type{String}, ::String)",
      "transcode(T, ::String)", "transcode(::Type{String}, ::Vector{UInt8})", "transcode(::Type{String}, src)"]
    statement := "The simple transcode overloads are identities, comprehensions, or direct delegations to the UTF conversion routines in source order."
    source := "base/strings/cstring.jl:163-183", status := .proven
    prop := ``CStrings.TranscodeWrappers, thm := some ``CStrings.transcodeWrappers },
  { id := "stringscova-unsafe-wide-strings", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["unsafe_string(::Ptr{T}, ::Integer)", "unsafe_string(::Ptr{T})", "unsafe_string(::Cwstring)"]
    statement := "Wide unsafe_string with a length transcodes exactly that many units, while the NUL-terminated forms transcode exactly the prefix before the first zero."
    source := "base/strings/cstring.jl:308-331", status := .proven
    prop := ``CStrings.UnsafeWideStrings, thm := some ``CStrings.unsafeWideStrings },
  { id := "stringscova-basic-integer-fallbacks", juliaFile := "base/strings/basic.jl"
    juliaFns := ["codeunit(::AbstractString, ::Integer)", "isvalid(::AbstractString, ::Integer)",
      "iterate(::AbstractString, ::Integer)"]
    statement := "Each generic Integer fallback rejects a missing machine-Int implementation and otherwise converts once and dispatches to it."
    source := "base/strings/basic.jl:107-157", status := .proven
    prop := ``Basic.IntegerFallbacks, thm := some ``Basic.integerFallbacks },
  { id := "stringscova-basic-scalars", juliaFile := "base/strings/basic.jl"
    juliaFns := ["eltype(::Type{<:AbstractString})", "sizeof(::AbstractString)", "firstindex(::AbstractString)",
      "lastindex(::AbstractString)", "isempty(::AbstractString)", "first(::AbstractString)",
      "getindex/get/checkbounds(::AbstractString)", "string(::AbstractString)", "Vector/Array(::AbstractString)",
      "Symbol(::AbstractString)", "convert(::Type{<:AbstractString}, ::AbstractString)"]
    statement := "Generic scalar access, bounds checks, construction, and conversion follow the source expressions for every supplied implementation."
    source := "base/strings/basic.jl:159-228", status := .proven
    prop := ``Basic.ScalarBasics, thm := some ``Basic.scalarBasics },
  { id := "stringscova-basic-presentation-comparison", juliaFile := "base/strings/basic.jl"
    juliaFns := ["summary(::IO,::AbstractString)", "*(::AbstractString,...) ", "one(::AbstractString)",
      "_isannotated", "cmp(::AbstractString,::AbstractString)", "==(::AbstractString,::AbstractString)",
      "isless(::AbstractString,::AbstractString)", "cmp(::Symbol,::Symbol)", "isless(::Symbol,::Symbol)"]
    statement := "Summary, concatenation selection, annotation detection, and lexicographic comparison follow their documented character behavior."
    source := "base/strings/basic.jl:230-363", status := .proven
    prop := ``Basic.PresentationComparison, thm := some ``Basic.presentationComparison },
  { id := "stringscova-basic-index-arithmetic", juliaFile := "base/strings/basic.jl"
    juliaFns := ["length(::AbstractString)", "length(::AbstractString,::Integer,::Integer)",
      "thisind(::AbstractString,::Integer)", "prevind(::AbstractString,::Integer,::Integer)",
      "nextind(::AbstractString,::Integer,::Integer)"]
    statement := "Generic length, thisind, prevind, and nextind delegate to the faithful UTF-8 loops and preserve their errors."
    source := "base/strings/basic.jl:365-573", status := .proven
    prop := ``Basic.IndexArithmetic, thm := some ``Basic.indexArithmetic },
  { id := "stringscova-basic-eachindex-ascii", juliaFile := "base/strings/basic.jl"
    juliaFns := ["keys(::AbstractString)", "EachStringIndex methods", "isascii(::Char/AbstractChar/AbstractString)",
      "_isascii", "_isascii_chunks", "isascii(::AbstractVector)"]
    statement := "String index iteration visits the same indices as nextind, and every ASCII method returns true exactly when all represented values are below 0x80."
    source := "base/strings/basic.jl:575-653", status := .proven
    prop := ``Basic.EachIndexAscii, thm := some ``Basic.eachIndexAscii },
  { id := "stringscova-basic-transform-slices", juliaFile := "base/strings/basic.jl"
    juliaFns := ["map(::Any,::AbstractString)", "filter(::Any,::AbstractString)", "last(::AbstractString,::Integer)",
      "reverseind", "repeat(::AbstractString,::Integer)", "^(::AbstractString,::Integer)",
      "iterate(::Iterators.Reverse{<:AbstractString})"]
    statement := "Map and filter transform the character sequence, slice helpers use the faithful index arithmetic, repeat delegates to String, and reverse iteration moves with prevind."
    source := "base/strings/basic.jl:655-776", status := .proven
    prop := ``Basic.TransformSlices, thm := some ``Basic.transformSlices },
  { id := "stringscova-basic-codeunits", juliaFile := "base/strings/basic.jl"
    juliaFns := ["CodeUnits and its array/pointer methods", "codeunits(::AbstractString)", "_split_rest"]
    statement := "CodeUnits exposes the source code units with matching size, bounds, storage identity, output, pointer conversion, and allocation behavior; _split_rest delegates to string index arithmetic."
    source := "base/strings/basic.jl:778-840", status := .proven
    prop := ``Basic.CodeUnitWrappers, thm := some ``Basic.codeUnitWrappers },
  { id := "stringscova-substring-constructors", juliaFile := "base/strings/substring.jl"
    juliaFns := ["SubString/raw_substring constructors", "view/maybeview", "convert(::SubString)",
      "String(::SubString{String})"]
    statement := "Substring constructors preserve the parent byte interval, flatten nested views where specified, check raw bounds, and conversion copies exactly the visible bytes."
    source := "base/strings/substring.jl:71-137", status := .proven
    prop := ``Substring.ConstructorContract, thm := some ``Substring.constructorContract },
  { id := "stringscova-substring-access", juliaFile := "base/strings/substring.jl"
    juliaFns := ["ncodeunits/codeunit/length/getindex/isvalid/thisind/nextind(::SubString)",
      "parent/parentindices", "==/cmp/hash(::SubString{String})", "pointer/cconvert/unsafe_convert", "string/Symbol"]
    statement := "Every SubString access maps its local index through the stored offset and exposes, compares, hashes, or copies exactly the visible parent bytes."
    source := "base/strings/substring.jl:139-213", status := .proven
    prop := ``Substring.AccessContract, thm := some ``Substring.accessContract },
  { id := "stringscova-substring-builders", juliaFile := "base/strings/substring.jl"
    juliaFns := ["__unsafe_string! overloads", "string(::Union...)", "_string"]
    statement := "The string builders size and concatenate the exact bytes of each Char, String, SubString, or Symbol in argument order."
    source := "base/strings/substring.jl:215-283", status := .proven
    prop := ``Substring.BuilderContract, thm := some ``Substring.builderContract },
  { id := "stringscova-substring-final", juliaFile := "base/strings/substring.jl"
    juliaFns := ["repeat(::String/Substring,::Integer)", "filter(::Any,::String/Substring)",
      "getindex(::AbstractString,::AbstractUnitRange)"]
    statement := "Repeat returns the faithful repeated bytes or its documented error, filter keeps exactly accepted characters, and range indexing constructs the corresponding SubString."
    source := "base/strings/substring.jl:285-322", status := .proven
    prop := ``Substring.FinalOperations, thm := some ``Substring.finalOperations },
  { id := "stringscova-search-characters", juliaFile := "base/strings/search.jl"
    juliaFns := ["last_utf8_byte", "is_standalone_byte", "FwCharPosIter/RvCharPosIter methods",
      "findnext/findprev character and byte specializations", "memchr/memrchr", "findall(::Fix2{Char})"]
    statement := "Forward and reverse character search test complete UTF-8 characters at valid indices, while the byte specializations return the first or last matching byte in the requested range."
    source := "base/strings/search.jl:34-284", status := .proven
    prop := ``Search.CharacterSearch, thm := some ``Search.characterSearch },
  { id := "stringscova-search-forward", juliaFile := "base/strings/search.jl"
    juliaFns := ["findfirst(::AbstractChar/AbstractVector)", "findnext(::Function,::AbstractString)",
      "in(::AbstractChar,::AbstractString)", "_searchindex overloads", "_search_bloom_mask", "_nthbyte", "_search"]
    statement := "Forward predicate and substring search follows the source byte-search loop and returns its sentinel or matching start/range."
    source := "base/strings/search.jl:321-479", status := .proven
    prop := ``Search.ForwardSearch, thm := some ``Search.forwardSearch },
  { id := "stringscova-search-wrappers", juliaFile := "base/strings/search.jl"
    juliaFns := ["findnext(::AbstractChar/AbstractVector)", "findlast string/vector/char", "findall(pattern,string; overlap)"]
    statement := "Public forward-search wrappers delegate from the documented starting index, and findall advances from each result according to overlap and empty-match rules."
    source := "base/strings/search.jl:509-665", status := .proven
    prop := ``Search.SearchWrappers, thm := some ``Search.searchWrappers },
  { id := "stringscova-search-reverse", juliaFile := "base/strings/search.jl"
    juliaFns := ["findprev(::Function,::AbstractString)", "_rsearchindex overloads", "_rsearch"]
    statement := "Reverse predicate and substring search follows the source reverse byte-search loop and returns its sentinel or latest matching range."
    source := "base/strings/search.jl:667-796", status := .proven
    prop := ``Search.ReverseSearch, thm := some ``Search.reverseSearch },
  { id := "stringscova-search-final", juliaFile := "base/strings/search.jl"
    juliaFns := ["findprev(::AbstractChar/AbstractVector)", "occursin", "in(::AbstractString,::AbstractString)",
      "in(::UInt8/Int8,::DenseArray)"]
    statement := "Final public wrappers delegate to reverse search or occurrence search, string `in` throws its guidance error, and byte membership is exactly successful byte search."
    source := "base/strings/search.jl:823-916", status := .proven
    prop := ``Search.FinalWrappers, thm := some ``Search.finalWrappers },
  { id := "stringscova-util-prefix-suffix", juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith overloads", "endswith overloads", "contains overloads"]
    statement := "Prefix and suffix predicates compare complete characters or dense bytes at character boundaries, IO prefix checks compare unread bytes, and contains delegates to occursin."
    source := "base/strings/util.jl:14-209", status := .proven
    prop := ``Util.PrefixSuffix, thm := some ``Util.prefixSuffix },
  { id := "stringscova-util-chop-affixes", juliaFile := "base/strings/util.jl"
    juliaFns := ["chopprefix overloads", "chopsuffix overloads"]
    statement := "chopprefix and chopsuffix remove exactly a matching character sequence and otherwise preserve the original characters."
    source := "base/strings/util.jl:246-350", status := .proven
    prop := ``Util.ChopAffixes, thm := some ``Util.chopAffixes },
  { id := "stringscova-util-strip-wrappers", juliaFile := "base/strings/util.jl"
    juliaFns := ["lstrip/rstrip/strip default, Chars, and error overloads"]
    statement := "The strip wrappers select the documented predicate or character membership test, compose right then left stripping, and reject a String as the character-set argument."
    source := "base/strings/util.jl:392-489", status := .proven
    prop := ``Util.StripWrappers, thm := some ``Util.stripWrappers },
  { id := "stringscova-util-pad-truncate-wrappers", juliaFile := "base/strings/util.jl"
    juliaFns := ["lpad/rpad conversion wrappers", "_pad_remainder(::AbstractChar)", "string_truncate_boundaries"]
    statement := "Padding wrappers stringify once, character remainder returns the character, and truncation boundaries use the faithful width-balancing loop."
    source := "base/strings/util.jl:493-735", status := .proven
    prop := ``Util.PadTruncateWrappers, thm := some ``Util.padTruncateWrappers },
  { id := "stringscova-util-split-wrappers", juliaFile := "base/strings/util.jl"
    juliaFns := ["SplitIterator/RSplitIterator methods", "PartitionIterator string specialization",
      "eachsplit/eachrsplit/split/rsplit overloads"]
    statement := "Split iterators and collecting wrappers delegate to the faithful forward and reverse delimiter loops with the documented limit and keepempty values."
    source := "base/strings/util.jl:774-1009", status := .proven
    prop := ``Util.SplitWrappers, thm := some ``Util.splitWrappers },
  { id := "stringscova-util-replace-wrappers", juliaFile := "base/strings/util.jl"
    juliaFns := ["_replace overloads", "_pat_replacer/_free_pat_replacer", "_replace_ overloads", "replace overloads"]
    statement := "Replacement wrappers choose literal, shown, substring, or character replacements and delegate to the faithful single-pass replacement engine with count preserved."
    source := "base/strings/util.jl:1011-1187", status := .proven
    prop := ``Util.ReplaceWrappers, thm := some ``Util.replaceWrappers },
  { id := "stringscova-util-encoding-rest", juliaFile := "base/strings/util.jl"
    juliaFns := ["hex2bytes/hex2bytes! wrappers", "number_from_hex(::AbstractChar)",
      "bytes2hex overloads", "ascii overloads", "Base.rest string overloads"]
    statement := "Hex wrappers use the proven nibble conversion, ASCII accepts exactly byte strings below 0x80, and rest returns the requested suffix or collected remaining characters."
    source := "base/strings/util.jl:1237-1373", status := .proven
    prop := ``Util.EncodingRest, thm := some ``Util.encodingRest },
  { id := "stringscova-string-view-errors", juliaFile := "base/strings/string.jl"
    juliaFns := ["StringView{T} constructor", "string_index_err", "showerror(::StringIndexError)", "between"]
    statement := "StringView requires one-based concrete storage, string_index_err throws at the supplied index, showerror identifies that index, and between is an inclusive test."
    source := "base/strings/string.jl:32-78", status := .proven
    prop := ``String.ViewErrors, thm := some ``String.viewErrors },
  { id := "stringscova-string-storage-conversions", juliaFile := "base/strings/string.jl"
    juliaFns := ["String/unsafe_takestring/takestring!/unsafe_string constructors", "_string_n",
      "String/unsafe_wrap/Vector/Array conversions", "pointer/ncodeunits/codeunit"]
    statement := "String construction and conversion preserve exactly the selected bytes, taking a vector empties it, pointer arithmetic is byte-based, and codeunit performs the documented bounds check."
    source := "base/strings/string.jl:96-217", status := .proven
    prop := ``String.StorageConversions, thm := some ``String.storageConversions },
  { id := "stringscova-string-comparison-indices", juliaFile := "base/strings/string.jl"
    juliaFns := ["_memcmp overloads", "==/typemin(::String)", "_thisind_str/_thisind_continued", "_nextind_str/_nextind_continued"]
    statement := "Byte comparison uses the requested common prefix, String equality compares bytes, typemin is empty, and UTF-8 index helpers use the faithful rewind and advance branches."
    source := "base/strings/string.jl:219-306", status := .proven
    prop := ``String.ComparisonIndices, thm := some ``String.comparisonIndices },
  { id := "stringscova-string-utf8-classification", juliaFile := "base/strings/string.jl"
    juliaFns := ["_utf_dfa_step/_isvalid_utf8_dfa", "_find_nonascii_chunk", "byte_string_classify",
      "_byte_string_classify_nonascii", "isvalid(::Type{String},...)", "is_valid_continuation"]
    statement := "The UTF-8 DFA and chunked classifier use the source tables and return ASCII, valid UTF-8, or invalid consistently for every byte vector."
    source := "base/strings/string.jl:308-504", status := .proven
    prop := ``String.Utf8Classification, thm := some ``String.utf8Classification },
  { id := "stringscova-string-iteration-slices", juliaFile := "base/strings/string.jl"
    juliaFns := ["iterate_continued/getindex/getindex_continued", "getindex range overloads",
      "length String/StringView overloads and helpers", "isascii(::String)", "repeat(::AbstractChar,::Integer)"]
    statement := "Iteration and indexing decode the same UTF-8 unit sequence, range slicing copies the checked byte span, length counts character starts, ASCII scans bytes, and character repetition emits the exact encoded bytes."
    source := "base/strings/string.jl:506-715", status := .proven
    prop := ``String.IterationSlices, thm := some ``String.iterationSlices }
] ++ LazyFaithfulRegistry.entries ++ CStringsFaithfulRegistry.entries ++ StringViewFaithfulRegistry.entries ++
  StringViewRebuiltRegistry.entries ++
  SubstringFaithfulCtorRegistry.entries ++ SubstringFaithfulAccessRegistry.entries ++
  SubstringFaithfulFinalRegistry.entries ++ BasicFaithfulRegistry.entries ++
  SubstringRebuiltRegistry.entries ++
  BasicRebuiltRegistry.entries ++
  SearchFaithfulRegistry.entries ++ UtilFaithfulRegistry.entries ++ StringFaithfulRegistry.entries

end JuliaLean.StringsCovA
