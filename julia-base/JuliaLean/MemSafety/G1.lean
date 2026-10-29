import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.MemSafety.G1.Faithful
import JuliaLean.MemSafety.G1.GrowthBounds

namespace JuliaLean.MemSafety.G1

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-1.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-base-compiler-bootstrap", juliaFile := "base/Base_compiler.jl"
    juliaFns := ["include(::Module, ::String)", "strcat(::String, ::String)"]
    statement := "Bootstrap include either grows its valid offset-one vector through _growend! or advances its size before writing len+1; strcat partitions the exact x+y allocation."
    source := "base/Base_compiler.jl:13-25,194-205; base/array.jl:1171-1227"
    status := .proven, prop := ``BootstrapInBounds, thm := some ``bootstrapInBounds_proven },
  { id := "memsafety-array-checked-cartesian", juliaFile := "base/array.jl"
    juliaFns := ["isassigned(::Array, ::Int...)", "getindex(::Array, ::Int, ::Int, ::Int...)", "_setindex!(::Array, ::Any, ::Int, ::Int, ::Int...)"]
    statement := "After checkbounds normalizes missing and extra singleton dimensions, _sub2ind computes a one-based linear index inside the product storage length."
    source := "base/array.jl:231-236,974-977,1042-1051; base/abstractarray.jl:682-728,3165-3208"
    status := .proven, prop := ``CheckedCartesianInBounds,
    thm := some ``checkedCartesianInBounds_proven },
  { id := "memsafety-array-checked-copies", juliaFile := "base/array.jl"
    juliaFns := ["_copyto_impl!", "copy(::Array)", "getindex(::Array, ::Colon)", "setindex!(::Array, ::Array, ::AbstractUnitRange)", "setindex!(::Array, ::Array, ::Colon)"]
    statement := "Checked copy paths derive both spans from their bounds checks; exact-copy paths allocate or require exactly the copied element count."
    source := "base/array.jl:299-315,391-399,995-1001,1078-1095"
    status := .proven, prop := ``ArrayCheckedCopiesInBounds,
    thm := some ``arrayCheckedCopiesInBounds_proven },
  { id := "memsafety-array-wrap-memory", juliaFile := "base/array.jl"
    juliaFns := ["wrap(::Type{Array}, ::Memory, dims)", "wrap(::Type{Array}, ::Memory, length)", "wrap(::Type{Array}, ::Memory)"]
    statement := "The Memory overloads start at the first cell and expose only the checked dimension product after _wrap compares it with length(memory)."
    source := "base/array.jl:3240-3278"
    status := .proven, prop := ``WrapMemoryInBounds, thm := some ``wrapMemoryInBounds_proven },
  { id := "memsafety-array-growbeg-accesses", juliaFile := "base/array.jl"
    juliaFns := ["_growbeg!", "_growbeg_internal!"]
    statement := "Every unchecked reference, copy span, and clearing index reached from valid public grow-begin calls is in bounds."
    source := "base/array.jl:1116-1168"
    status := .todo, prop := ``GrowthBounds.GrowbegPublicSafety,
    notes := "The public-path access trace and machine-sized arithmetic lemmas are not yet connected by a proof." },
  { id := "memsafety-array-growend-accesses", juliaFile := "base/array.jl"
    juliaFns := ["_growend!", "_growend_internal!"]
    statement := "Every unchecked reference, copy span, and clearing index reached from valid public grow-end calls is in bounds."
    source := "base/array.jl:1171-1222"
    status := .todo, prop := ``GrowthBounds.GrowendPublicSafety,
    notes := "The public-path access trace and machine-sized arithmetic lemmas are not yet connected by a proof." },
  { id := "memsafety-combinatorics-swap-invperm", juliaFile := "base/combinatorics.jl"
    juliaFns := ["swapcols!", "swaprows!", "invperm"]
    statement := "Swaps check both scalar indices before traversing the other matrix axis, and invperm range-checks every value before indexing its length-sized result."
    source := "base/combinatorics.jl:103-123,286-296"
    status := .proven, prop := ``CombinatoricsAccessesInBounds,
    thm := some ``combinatoricsAccessesInBounds_proven },
  { id := "memsafety-gcutils-global", juliaFile := "base/gcutils.jl"
    juliaFns := ["GC.enable_finalizers"]
    statement := "cglobal(:jl_gc_have_pending_finalizers, Cint) computes offset zero in the runtime's one-Cint global object."
    source := "base/gcutils.jl:161-166; src/gc.c runtime global declaration"
    status := .proven, prop := ``RuntimeCellInBounds, thm := some ``runtimeCellInBounds_proven },
  { id := "memsafety-libdl-global", juliaFile := "base/libdl.jl"
    juliaFns := ["Libdl.__init__"]
    statement := "cglobal(:jl_libdl_dlopen_func, Any) computes offset zero in the runtime's one-Any global object."
    source := "base/libdl.jl:515-517; runtime global declaration"
    status := .proven, prop := ``RuntimeCellInBounds, thm := some ``runtimeCellInBounds_proven },
  { id := "memsafety-libc-os-buffers", juliaFile := "base/libc.jl"
    juliaFns := ["Libc.FormatMessage", "Libc.getgrgid"]
    statement := "FormatMessageW's returned count sizes both copy spans, and getgrgid walks the null-terminated member-pointer array returned by libuv."
    source := "base/libc.jl:395-410,581-603; Win32 FormatMessageW and libuv uv_os_get_group contracts"
    status := .proven, prop := ``LibcBuffersInBounds, thm := some ``libcBuffersInBounds_proven },
  { id := "memsafety-deprecated-substring-negative-count", juliaFile := "base/deprecated.jl"
    juliaFns := ["SubString{T}(s, i, j, Val(:noshift))"]
    statement := "Every successful deprecated no-shift constructor call returns a SubString with a nonnegative code-unit count and a span inside its parent."
    source := "base/deprecated.jl:704-724; SubString representation invariant"
    status := .refuted, prop := ``DeprecatedSubstringValid,
    thm := some ``deprecatedSubstringValid_refuted
    issue := "none found (queries: SubString negative ncodeunits, Val noshift negative SubString, raw_substring negative)"
    notes := "With s=\"abc\", i=2, and j=-1, both validated endpoints are valid before the unchecked raw_substring call stores ncodeunits=-1." }
]

end JuliaLean.MemSafety.G1
