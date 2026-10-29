import JuliaLean.MemSafety.G6.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MemSafety.G6

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-6.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-file-diskstat-pointer"
    juliaFile := "base/file.jl"
    juliaFns := ["diskstat"]
    statement := "diskstat loads one DiskStat only after uv_fs_statfs succeeds and jl_uv_fs_t_ptr returns its documented uv_statfs_t result."
    source := "libuv uv_fs_statfs result contract; base/file.jl:1662-1713"
    status := .proven
    prop := ``DiskstatPointerLoadInBounds
    thm := some ``diskstatPointerLoadInBounds_proven },
  { id := "memsafety-reflection-debug-global"
    juliaFile := "base/reflection.jl"
    juliaFns := ["default_debug_info_kind"]
    statement := "cglobal(:jl_default_debug_info_kind, Cint) denotes one runtime-owned Cint and the function loads that object at offset zero."
    source := "runtime exported-global type invariant; base/reflection.jl:90; src/jl_exported_data.inc"
    status := .proven
    prop := ``ReflectionGlobalLoadInBounds
    thm := some ``reflectionGlobalLoadInBounds_proven },
  { id := "memsafety-mpfr-constructed-storage"
    juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(; precision)", "getproperty/setproperty!(::BigFloat)",
      "BigFloat(::Float64)"]
    statement := "The MPFR header fields and Float64-constructor payload writes fit the ABI-specific allocation computed from the requested precision."
    source := "MPFR custom-allocation contract and BigFloat layout; base/mpfr.jl:124-207,330-370"
    status := .proven
    prop := ``BigFloatStorageAccessesInBounds
    thm := some ``bigFloatStorageAccessesInBounds_proven },
  { id := "memsafety-mpfr-string-buffer"
    juliaFile := "base/mpfr.jl"
    juliaFns := ["string_mpfr"]
    statement := "string_mpfr scans and possibly replaces only the non-NUL bytes counted by a successful mpfr_asprintf result."
    source := "MPFR mpfr_asprintf return contract; base/mpfr.jl:1221-1236"
    status := .proven
    prop := ``StringMpfrAccessesInBounds
    thm := some ``stringMpfrAccessesInBounds_proven },
  { id := "memsafety-parsers-int-accesses"
    juliaFile := "base/parsers/ints.jl"
    juliaFns := ["load8", "overflowfailure", "parseint", "parsevalue"]
    statement := "The sign read, every eight-byte block, and every scalar or overflow scan index computed by integer parsing lies in the input byte vector."
    source := "parseint contract and computed loop bounds; base/parsers/ints.jl:8-21,71-189"
    status := .proven
    prop := ``ParserAccessesInBounds
    thm := some ``parserAccessesInBounds_proven },
  { id := "memsafety-log-table-indices"
    juliaFile := "base/special/log.jl"
    juliaFns := ["_log(::Float64)", "_log(::Float32)", "log1p", "log_proc1", "_log_ext"]
    statement := "Seven-bit rounding of a normalized mantissa computes a log_proc1 table index in 1:129, and the masked _log_ext index is in 1:128."
    source := "computed IEEE fraction and mask arithmetic; base/special/log.jl:151-156,209-214,258-386,555-565"
    status := .proven
    prop := ``LogTableAccessesInBounds
    thm := some ``logTableAccessesInBounds_proven },
  { id := "memsafety-uuid-format-writes"
    juliaFile := "base/uuid.jl"
    juliaFns := ["string(::UUID)"]
    statement := "UUID formatting computes 32 hexadecimal table indices in 1:16 and writes them and four hyphens only in its 36-byte result."
    source := "computed groupings and nibble arithmetic; base/uuid.jl:98-115"
    status := .proven
    prop := ``UuidWritesInBounds
    thm := some ``uuidWritesInBounds_proven },
  { id := "memsafety-regex-ovector"
    juliaFile := "base/regex.jl"
    juliaFns := ["match(::Regex, ::DenseUTF8String, idx)", "_findnext_re"]
    statement := "The capture count computed from PCRE's ovector length makes every whole-match and capture slot load fit the ovector."
    source := "PCRE2 ovector contract and computed capture loop; base/regex.jl:430-451,491-511"
    status := .proven
    prop := ``RegexOvectorAccessesInBounds
    thm := some ``regexOvectorAccessesInBounds_proven },
  { id := "memsafety-regex-subject-spans"
    juliaFile := "base/regex.jl"
    juliaFns := ["match", "_annotatedmatch", "_findnext_re", "count(::AbstractPattern, ::AbstractString)"]
    statement := "PCRE's half-open subject spans convert to in-bounds Julia byte spans, and count calls nextind only for a match endpoint no later than lastindex."
    source := "PCRE2 subject-offset contract and computed caller branches; base/regex.jl:430-461,491-511,573-583"
    status := .proven
    prop := ``RegexSpanAccessesInBounds
    thm := some ``regexSpanAccessesInBounds_proven },
  { id := "memsafety-annotated-string-accesses"
    juliaFile := "base/strings/annotated.jl"
    juliaFns := ["unannotate(::SubString{<:AnnotatedString})", "getindex(::AnnotatedString, i)"]
    statement := "A construction-checked SubString span stays in its annotated parent, and checked AnnotatedString indexing uses an in-bounds underlying String index."
    source := "SubString representation and computed index check; base/strings/annotated.jl:184-199"
    status := .proven
    prop := ``AnnotatedStringAccessesInBounds
    thm := some ``annotatedStringAccessesInBounds_proven }
]

end JuliaLean.MemSafety.G6
