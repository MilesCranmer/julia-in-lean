import JuliaLean.Proofs.base.iostream
import JuliaLean.Proofs.base.util
import JuliaLean.Proofs.base.secretbuffer
import JuliaLean.Registry.Types
import JuliaLean.Registry.Generality
import JuliaLean.Proofs.base.float.Registry
import JuliaLean.Proofs.base.int.IntArith
import JuliaLean.Proofs.base.range.integer_entries
import JuliaLean.Proofs.base.sort.entries
import JuliaLean.Proofs.base.range.floating_entries
import JuliaLean.Proofs.base.strings.string.entries
import JuliaLean.base.ryu.Ryu
import JuliaLean.Proofs.base.ryu.shortest.claims
import JuliaLean.base.parse
import JuliaLean.Proofs.base.parse.integer_properties
import JuliaLean.Proofs.base.parse.IntParseBoundary
import JuliaLean.base.intfuncs
import JuliaLean.Proofs.base.intfuncs.integer_printing
import JuliaLean.Proofs.base.parse.IntRoundtrip1
import JuliaLean.Proofs.base.parse.IntRoundtrip2
import JuliaLean.Proofs.base.floatfuncs.round_digits
import JuliaLean.Proofs.base.math.MathFuncs
import JuliaLean.Proofs.base.accumulate.ReductionClaims
import JuliaLean.Proofs.base.io.IOBufferPeek
import JuliaLean.Proofs.base.version
import JuliaLean.Proofs.base.promotion.Registry
import JuliaLean.Proofs.base.toml.parser.Registry
import JuliaLean.Proofs.base.regex.all
import JuliaLean.Proofs.base.show.printingEntries
import JuliaLean.Proofs.base.array.cartesian_search
import JuliaLean.Proofs.base.gmp.big_number_entries
import JuliaLean.Proofs.base.missing.entries
import JuliaLean.Proofs.base.strings.util.utility_entries
import JuliaLean.Proofs.base.shell.ShellCmdRegistry
import JuliaLean.Proofs.base.strings.cstring.registry
import JuliaLean.Proofs.base.floatfuncs.FloatFuncs
import JuliaLean.Proofs.base.channels.channel_entries
import JuliaLean.Proofs.stdlib.Printf.src.Printf
import JuliaLean.Proofs.stdlib.Dates.src.Dates
import JuliaLean.Proofs.stdlib.Base64.src.Base64
import JuliaLean.Proofs.base.broadcast.views
import JuliaLean.Proofs.stdlib.Random
import JuliaLean.Proofs.stdlib.Sockets.src.IPAddr
import JuliaLean.Proofs.stdlib.Serialization.src.Serialization
import JuliaLean.Proofs.stdlib.Markdown.src.Registry
import JuliaLean.Proofs.base.weakdict.Entries
import JuliaLean.Proofs.base.abstractarray.interface_entries
import JuliaLean.Proofs.base.strings.annotated.hash_entries
import JuliaLean.Proofs.stdlib.Artifacts.src.Artifacts
import JuliaLean.Proofs.base.abstractarray.memory_safety_access
import JuliaLean.Proofs.base.array.memory_safety
import JuliaLean.Proofs.base.set.memory_safety
import JuliaLean.Proofs.base.Base_compiler.memory_safety
import JuliaLean.Proofs.base.abstractarraymath.memory_safety
import JuliaLean.Proofs.base.deprecated.memory_safety
import JuliaLean.Proofs.base.strings.string.memory_safety
import JuliaLean.Proofs.base.strings.substring.memory_safety
import JuliaLean.Proofs.base.strings.io.memory_safety
import JuliaLean.Proofs.base.iobuffer.memory_safety
import JuliaLean.Proofs.base.reducedim.memory_safety
import JuliaLean.Proofs.base.combinatorics.memory_safety
import JuliaLean.Proofs.base.gcutils.memory_safety_cells
import JuliaLean.Proofs.base.libc.memory_safety
import JuliaLean.Proofs.base.arraymath.memory_safety_group2
import JuliaLean.Proofs.base.experimental.memory_safety_group2
import JuliaLean.Proofs.base.expr.memory_safety_group2
import JuliaLean.Proofs.base.gmp.memory_safety_group2
import JuliaLean.Proofs.base.hashing.memory_safety_group2
import JuliaLean.Proofs.base.loading.memory_safety_group2
import JuliaLean.Proofs.base.missing.memory_safety_group2
import JuliaLean.Proofs.base.multidimensional.memory_safety_group2
import JuliaLean.Proofs.base.reshapedarray.memory_safety_group2
import JuliaLean.Proofs.base.ryu.shortest.memory_safety
import JuliaLean.Proofs.base.special.rem_pio2.memory_safety_group2
import JuliaLean.Proofs.base.strings.stringview.memory_safety_group2
import JuliaLean.Proofs.base.summarysize.memory_safety_group2
import JuliaLean.Proofs.base.abstractarray.access_bounds
import JuliaLean.Proofs.base.deepcopy.access_bounds
import JuliaLean.Proofs.base.dict.access_bounds
import JuliaLean.Proofs.base.hamt.access_bounds
import JuliaLean.Proofs.base.env.access_bounds
import JuliaLean.Proofs.base.intfuncs.access_bounds
import JuliaLean.Proofs.base.io.access_bounds
import JuliaLean.Proofs.base.module.access_bounds
import JuliaLean.Proofs.base.parse.access_bounds
import JuliaLean.Proofs.base.parsers.floats.access_bounds
import JuliaLean.Proofs.base.path.access_bounds
import JuliaLean.Proofs.base.pcre.access_bounds
import JuliaLean.Proofs.base.reduce.access_bounds
import JuliaLean.Proofs.base.strings.util.access_bounds
import JuliaLean.Proofs.base.strings.unicode.access_bounds
import JuliaLean.Proofs.base.timing.access_bounds
import JuliaLean.Proofs.base.sort.MemoryBounds
import JuliaLean.Proofs.base.bitarray.MemoryBounds
import JuliaLean.Proofs.base.boot.ArrayBounds
import JuliaLean.Proofs.base.broadcast.MemoryBounds
import JuliaLean.Proofs.base.hamt.BitmapBounds
import JuliaLean.Proofs.base.precompilation.ProcessStatsBounds
import JuliaLean.Proofs.base.rational.SplitBounds
import JuliaLean.Proofs.base.reinterpretarray.ReductionBounds
import JuliaLean.Proofs.base.runtime_internals.MetadataBounds
import JuliaLean.Proofs.base.ryu.utils.LookupBounds
import JuliaLean.Proofs.base.simdloop.IndexBounds
import JuliaLean.Proofs.base.strings.search.IndexBounds
import JuliaLean.Proofs.base.sysinfo.CpuInfoBounds
import JuliaLean.Proofs.base.accumulate.access_bounds
import JuliaLean.Proofs.base.bitset.access_bounds
import JuliaLean.Proofs.base.essentials.constructor_access_bounds
import JuliaLean.Proofs.base.options.command_access_bounds
import JuliaLean.Proofs.base.threadingconstructs.access_bounds
import JuliaLean.Proofs.base.rawbigfloats.access_bounds
import JuliaLean.Proofs.base.show.bit_access_bounds
import JuliaLean.Proofs.base.slicearray.access_bounds
import JuliaLean.Proofs.base.stream.redirect_access_bounds
import JuliaLean.Proofs.base.toml.parser.chunk_access_bounds
import JuliaLean.Proofs.base.version.access_bounds
import JuliaLean.Proofs.base.file.access_bounds
import JuliaLean.Proofs.base.reflection.access_bounds
import JuliaLean.Proofs.base.genericmemory.access_bounds
import JuliaLean.Proofs.base.mpfr.access_bounds
import JuliaLean.Proofs.base.parsers.ints.access_bounds
import JuliaLean.Proofs.base.permuteddimsarray.access_bounds
import JuliaLean.Proofs.base.special.log.access_bounds
import JuliaLean.Proofs.base.uuid.access_bounds
import JuliaLean.Proofs.base.strings.string.access_bounds
import JuliaLean.Proofs.base.strings.basic.access_bounds
import JuliaLean.Proofs.base.regex.access_bounds
import JuliaLean.Proofs.base.strings.annotated.access_bounds
import JuliaLean.Proofs.base.gcutils.memory_safety
import JuliaLean.Proofs.base.libdl.memory_safety
import JuliaLean.Proofs.base.module.memory_safety
import JuliaLean.Proofs.base.simdloop.memory_safety
import JuliaLean.Proofs.base.reflection.memory_safety
import JuliaLean.Proofs.base.array.wrap_memory_safety
import JuliaLean.Proofs.base.missing.memory_safety
import JuliaLean.Proofs.base.accumulate
import JuliaLean.Proofs.base.threadingconstructs
import JuliaLean.Proofs.base.ryu.utils
import JuliaLean.Proofs.base.combinatorics.Entries
import JuliaLean.Proofs.base.logging.logging.Registry
import JuliaLean.Proofs.base.loading.retained
import JuliaLean.Proofs.base.stream
import JuliaLean.Proofs.base.file.Entries
import JuliaLean.Proofs.base.expr.Registry
import JuliaLean.Proofs.base.meta.Registry
import JuliaLean.Proofs.base.runtime_internals.Registry
import JuliaLean.Proofs.base.reflection.Registry
import JuliaLean.Proofs.base.Enums.Registry
import JuliaLean.Proofs.base.cartesian.Registry
import JuliaLean.Proofs.base.errorshow.coverage
import JuliaLean.Proofs.base.task.task_entries
import JuliaLean.Proofs.base.parsers.floats.Registry
import JuliaLean.Proofs.base.abstractarray.rows.entries
import JuliaLean.Proofs.base.accumulate.broadcast
import JuliaLean.Proofs.base.simdloop.coverage
import JuliaLean.Proofs.base.show.coverage
import JuliaLean.Proofs.base.range.coverage
import JuliaLean.Proofs.base.array.coverage
import JuliaLean.Proofs.base.rawbigfloats
import JuliaLean.Proofs.base.float.FloatIntCov
import JuliaLean.Proofs.base.boot
import JuliaLean.Proofs.base.essentials
import JuliaLean.base.boot
import JuliaLean.base.essentials
import JuliaLean.base.expr
import JuliaLean.Proofs.base.runtime_internals.RuntimeCov
import JuliaLean.Proofs.base.runtime_internals
import JuliaLean.Proofs.base.Base_compiler
import JuliaLean.Proofs.base.runtime_internals.legacy_runtime
import JuliaLean.Proofs.base.precompilation.legacy_runtime
import JuliaLean.Proofs.base.array.legacy_refutations
import JuliaLean.Proofs.base.array.legacy_cartesian_filter
import JuliaLean.Proofs.base.reshapedarray.legacy_runtime
import JuliaLean.Proofs.base.math.MathCov
import JuliaLean.Proofs.base.io.IOCov
import JuliaLean.Proofs.base.reflection
import JuliaLean.Proofs.base.stacktraces
import JuliaLean.Proofs.base.experimental
import JuliaLean.Proofs.base.number.numberscov
import JuliaLean.Proofs.base.operators.numberscov
import JuliaLean.Proofs.base.promotion.numberscov
import JuliaLean.Proofs.base.rational.numberscov
import JuliaLean.Proofs.base.complex.numberscov
import JuliaLean.Proofs.base.sort.coverage_entries
import JuliaLean.Proofs.base.traits.entries
import JuliaLean.Proofs.base.indices.MethodRows
import JuliaLean.Proofs.base.some.MethodRows
import JuliaLean.Proofs.base.missing.MethodRows
import JuliaLean.Proofs.base.reduce.MethodRows
import JuliaLean.Proofs.base.reducedim.MethodRows
import JuliaLean.Proofs.base.intfuncs.entries
import JuliaLean.Proofs.base.dict.CoverageEntries
import JuliaLean.Proofs.base.strings.entries
import JuliaLean.Proofs.base.strings.annotated_io.registry
import JuliaLean.Proofs.base.threadingconstructs.concurrency_entries
import JuliaLean.Proofs.base.binaryplatforms
import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.docs.basedocs
import JuliaLean.Proofs.base.docs.bindings
import JuliaLean.Proofs.base.docs.core
import JuliaLean.Proofs.base.docs.utils
import JuliaLean.Proofs.base.expr
import JuliaLean.Proofs.base.linking
import JuliaLean.Proofs.base.parse
import JuliaLean.Proofs.base.syntax
import JuliaLean.Proofs.base.toml.parser
import JuliaLean.Proofs.base.toml.printer
import JuliaLean.base.binaryplatforms
import JuliaLean.base.docs.Docs
import JuliaLean.base.docs.basedocs
import JuliaLean.base.docs.bindings
import JuliaLean.base.docs.core
import JuliaLean.base.docs.utils
import JuliaLean.base.io
import JuliaLean.base.linking
import JuliaLean.base.meta
import JuliaLean.base.parse
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.string
import JuliaLean.base.syntax
import JuliaLean.base.toml.parser
import JuliaLean.base.toml.printer
import JuliaLean.Proofs.base.deprecated.misc_coverage
import JuliaLean.Proofs.base.experimental.misc_coverage
import JuliaLean.Proofs.base.experimental.misc_additional
import JuliaLean.Proofs.base.shell.misc_coverage
import JuliaLean.Proofs.base.c.misc_coverage
import JuliaLean.Proofs.base.module.misc_coverage
import JuliaLean.Proofs.base.refvalue.misc_coverage
import JuliaLean.Proofs.base.scope.misc_coverage
import JuliaLean.Proofs.base.baseext.misc_coverage
import JuliaLean.Proofs.base.cmem.misc_coverage
import JuliaLean.Proofs.base.osutils.misc_coverage
import JuliaLean.Proofs.base.flfrontend.misc_coverage
import JuliaLean.Proofs.base.coreir.misc_coverage
import JuliaLean.Proofs.base.opaque_closure.misc_coverage
import JuliaLean.Proofs.base.Base.misc_coverage
import JuliaLean.Proofs.base.download.misc_coverage
import JuliaLean.Proofs.base.parsers.ints.misc_coverage
import JuliaLean.Proofs.base.ryu.utils.basic
import JuliaLean.Proofs.base.ryu.utils.arithmetic
import JuliaLean.Proofs.base.ryu.Ryu.wrappers
import JuliaLean.Proofs.base.abstractarray.specification_entries
import JuliaLean.Proofs.base.abstractarray
import JuliaLean.Proofs.base.abstractarraymath
import JuliaLean.Proofs.base.abstractdict
import JuliaLean.Proofs.base.abstractset
import JuliaLean.Proofs.base.anyall
import JuliaLean.Proofs.base.array
import JuliaLean.Proofs.base.arraymath
import JuliaLean.Proofs.base.bitarray
import JuliaLean.Proofs.base.bitarray.dispatch
import JuliaLean.Proofs.base.bitset
import JuliaLean.Proofs.base.bool
import JuliaLean.Proofs.base.broadcast
import JuliaLean.Proofs.base.channels
import JuliaLean.Proofs.base.char
import JuliaLean.Proofs.base.fastmath
import JuliaLean.Proofs.base.checked
import JuliaLean.Proofs.base.cmem
import JuliaLean.Proofs.base.complex
import JuliaLean.Proofs.base.deprecated
import JuliaLean.Proofs.base.dict
import JuliaLean.Proofs.base.div
import JuliaLean.Proofs.base.error
import JuliaLean.Proofs.base.errorshow
import JuliaLean.Proofs.base.arrayshow
import JuliaLean.Proofs.base.file
import JuliaLean.Proofs.base.float
import JuliaLean.Proofs.base.floatfuncs
import JuliaLean.Proofs.base.generator
import JuliaLean.Proofs.base.genericmemory
import JuliaLean.Proofs.base.gmp
import JuliaLean.Proofs.base.hamt
import JuliaLean.Proofs.base.hashing
import JuliaLean.Proofs.base.iddict
import JuliaLean.Proofs.base.idset
import JuliaLean.Proofs.base.indices
import JuliaLean.Proofs.base.int
import JuliaLean.Proofs.base.intfuncs
import JuliaLean.Proofs.base.iobuffer
import JuliaLean.Proofs.base.iterators
import JuliaLean.Proofs.base.linked_list
import JuliaLean.Proofs.base.logging.logging
import JuliaLean.Proofs.base.loading
import JuliaLean.Proofs.base.math
import JuliaLean.Proofs.base.missing
import JuliaLean.Proofs.base.mpfr
import JuliaLean.Proofs.base.multidimensional
import JuliaLean.Proofs.base.multinverses
import JuliaLean.Proofs.base.namedtuple
import JuliaLean.Proofs.base.ntuple
import JuliaLean.Proofs.base.number
import JuliaLean.Proofs.base.operators
import JuliaLean.Proofs.base.ordering
import JuliaLean.Proofs.base.osinfo
import JuliaLean.Proofs.base.pair
import JuliaLean.Proofs.base.path
import JuliaLean.Proofs.base.permuteddimsarray
import JuliaLean.Proofs.base.pointer
import JuliaLean.Proofs.base.precompilation
import JuliaLean.Proofs.base.cpuid
import JuliaLean.Proofs.base.promotion
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.rational
import JuliaLean.Proofs.base.reduce
import JuliaLean.Proofs.base.reducedim
import JuliaLean.Proofs.base.refpointer
import JuliaLean.Proofs.base.refvalue
import JuliaLean.Proofs.base.reinterpretarray
import JuliaLean.Proofs.base.reshapedarray
import JuliaLean.Proofs.base.rounding
import JuliaLean.Proofs.base.set
import JuliaLean.Proofs.base.show
import JuliaLean.Proofs.base.slicearray
import JuliaLean.Proofs.base.some
import JuliaLean.Proofs.base.sort
import JuliaLean.Proofs.base.stat
import JuliaLean.Proofs.base.strings.annotated
import JuliaLean.Proofs.base.strings.annotated_io
import JuliaLean.Proofs.base.strings.basic
import JuliaLean.Proofs.base.strings.cstring
import JuliaLean.Proofs.base.strings.io
import JuliaLean.Proofs.base.strings.lazy
import JuliaLean.Proofs.base.strings.search
import JuliaLean.Proofs.base.strings.string
import JuliaLean.Proofs.base.strings.substring
import JuliaLean.Proofs.base.strings.unicode
import JuliaLean.Proofs.base.strings.util
import JuliaLean.Proofs.base.subarray
import JuliaLean.Proofs.base.terminfo
import JuliaLean.Proofs.base.tuple
import JuliaLean.Proofs.base.twiceprecision
import JuliaLean.Proofs.base.uuid
import JuliaLean.Proofs.base.views
import JuliaLean.Proofs.base.special.exp
import JuliaLean.Proofs.base.special.cbrt
import JuliaLean.Proofs.base.floatfuncsArchive20261101
import JuliaLean.Proofs.base.floatfuncsInt64Archive20261101
import JuliaLean.Proofs.base.special.trig
import JuliaLean.Proofs.base.special.hyperbolic
import JuliaLean.Proofs.base.special.rem2pi
import JuliaLean.Proofs.base.combinatorics
import JuliaLean.Proofs.base.iterators.zip_shared_stateful_completion
import JuliaLean.Proofs.base.complex.cis_imaginary_axis
import JuliaLean.Proofs.base.indices.heterogeneous_cartesian_promotion
import JuliaLean.Proofs.base.intfuncs.lcm_zero_absorption
import JuliaLean.Proofs.base.parse.complex_imaginary_minimum
import JuliaLean.Proofs.base.permuteddimsarray.copy_linear_length
import JuliaLean.Proofs.base.set.replacement_key_swap

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



  { id := "memsafety-combinatorics-swap-invperm", juliaFile := "base/combinatorics.jl"
    juliaFns := ["swapcols!", "swaprows!", "invperm"]
    statement := "Swaps check both scalar indices before traversing the other matrix axis, and invperm range-checks every value before indexing its length-sized result."
    source := "base/combinatorics.jl:103-123,286-296"
    status := .proven, prop := ``CombinatoricsAccessesInBounds,
    thm := some ``combinatoricsAccessesInBounds_proven },


  { id := "memsafety-libc-os-buffers", juliaFile := "base/libc.jl"
    juliaFns := ["Libc.FormatMessage", "Libc.getgrgid"]
    statement := "FormatMessageW's returned count sizes both copy spans, and getgrgid walks the null-terminated member-pointer array returned by libuv."
    source := "base/libc.jl:395-410,581-603; Win32 FormatMessageW and libuv uv_os_get_group contracts"
    status := .proven, prop := ``LibcBuffersInBounds, thm := some ``libcBuffersInBounds_proven },

]

end JuliaLean.MemSafety.G1

namespace JuliaLean.MemSafety.G2

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-2.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-experimental-const-getindex", juliaFile := "base/experimental.jl"
    juliaFns := ["getindex(::Experimental.Const, ::Int)", "getindex(::Experimental.Const, ::Int...)"]
    statement := "Const's completed scalar or Cartesian bounds check makes its computed memory or linear index valid for the wrapped Array."
    source := "Array representation invariant; base/experimental.jl:25-40"
    status := .proven, prop := ``ConstGetindexInBounds, thm := some ``constGetindexInBounds },
  { id := "memsafety-expr-copy", juliaFile := "base/expr.jl"
    juliaFns := ["copy(::PhiNode)", "copy(::PhiCNode)", "copy_exprargs"]
    statement := "The expression-copy loops read and write only the slots computed from length(values) or eachindex(x)."
    source := "Array iteration invariant; base/expr.jl:45-79"
    status := .proven, prop := ``ExprCopyInBounds, thm := some ``exprCopyInBounds },

  { id := "memsafety-gmp-limb-convert", juliaFile := "base/gmp.jl"
    juliaFns := ["BigInt(::Integer)", "rem(::BigInt, ::Type)", "(::Type{<:IEEEFloat})(::BigInt, ::RoundingMode)"]
    statement := "BigInt construction, fixed-width remainder, and floating conversion derive every limb index from the input value's normalized limb count."
    source := "GMP normalized-limb representation; base/gmp.jl:347-465"
    status := .proven, prop := ``GmpLimbAccessesInBounds, thm := some ``gmpLimbAccessesInBounds },
  { id := "memsafety-gmp-bit-magnitude", juliaFile := "base/gmp.jl"
    juliaFns := ["exponent(::BigInt)", "top_set_bit(::BigInt)", "_bit_magnitude"]
    statement := "The public callers reject zero before _bit_magnitude reads the most-significant normalized limb."
    source := "base/gmp.jl:608-623"
    status := .proven, prop := ``GmpBitMagnitudeInBounds, thm := some ``gmpBitMagnitudeInBounds },
  { id := "memsafety-gmp-string", juliaFile := "base/gmp.jl"
    juliaFns := ["string(::BigInt)"]
    statement := "string allocates the digit and sign count computed from n, base, and pad before writing a negative sign at byte one."
    source := "base/gmp.jl:765-781"
    status := .proven, prop := ``GmpStringSignInBounds, thm := some ``gmpStringSignInBounds },
  { id := "memsafety-gmp-hash", juliaFile := "base/gmp.jl"
    juliaFns := ["UnsafeLimbView.getindex", "iterate(::UnsafeLimbView)", "hash_integer(::BigInt)", "hash(::BigInt)"]
    statement := "The BigInt hash branches and each byte index requested from their computed UnsafeLimbViews select an allocated limb."
    source := "GMP normalized-limb representation; base/gmp.jl:873-955"
    status := .proven, prop := ``GmpHashInBounds, thm := some ``gmpHashInBounds },
  { id := "memsafety-loading-isfile-casesensitive", juliaFile := "base/loading.jl"
    juliaFns := ["isfile_casesensitive"]
    statement := "Every loop iteration reads the four-byte filename-length field from a buffer allocated or resized to include its 12-byte header."
    source := "getattrlist buffer layout; base/loading.jl:33-65"
    status := .proven, prop := ``LoadingHeaderInBounds, thm := some ``loadingHeaderInBounds },


  { id := "memsafety-missing-mapreduce", juliaFile := "base/missing.jl"
    juliaFns := ["_mapreduce(::IndexLinear, ::SkipMissing)", "_mapreduce_impl_skipmissing"]
    statement := "Both preliminary scans and every sequential or pairwise mapreduce block compute indices within LinearIndices(A), including typemax guards."
    source := "base/missing.jl:269-351"
    status := .proven, prop := ``MissingMapreduceInBounds, thm := some ``missingMapreduceInBounds },
  { id := "memsafety-ryu-exponent-table", juliaFile := "base/ryu/shortest.jl"
    juliaFns := ["Ryu.writeshortest(::Float16)", "Ryu.writeshortest(::Float32)", "Ryu.writeshortest(::Float64)"]
    statement := "For every IEEE input type accepted by writeshortest, the exponent computed by reduce_shortest selects one of the 100 DIGIT_TABLE16 entries."
    source := "base/ryu/shortest.jl:7-226,319-447"
    status := .proven, prop := ``RyuExponentTableInBounds, thm := some ``ryuExponentTableInBounds },
  { id := "memsafety-rem-pio2-paynehanek-callers", juliaFile := "base/special/rem_pio2.jl"
    juliaFns := ["rem_pio2_kernel(::Float64)", "rem_pio2_kernel(::Float32)", "paynehanek(::Float64)"]
    statement := "Every public Float64 and Float32 reduction path that reaches paynehanek computes INV_2PI positions 1 through 19."
    source := "base/special/rem_pio2.jl:130-178,222-293"
    status := .proven, prop := ``PayneHanekCallerInBounds, thm := some ``payneHanekCallerInBounds },
  { id := "memsafety-stringview-indexing", juliaFile := "base/strings/stringview.jl"
    juliaFns := ["getindex(::StringView, ::UnitRange{Int})", "chomp(::StringViewAndSub)"]
    statement := "StringView range checks protect both UTF-8 validity probes, and chomp computes a substring length no greater than its code-unit length."
    source := "base/strings/stringview.jl:122-150"
    status := .proven, prop := ``StringViewInBounds, thm := some ``stringViewInBounds },
  { id := "memsafety-summarysize-memory", juliaFile := "base/summarysize.jl"
    juliaFns := ["summarysize"]
    statement := "The frontier transition enumerates length*np inline pointer fields and length direct elements, mapping every field ordinal to an existing GenericMemory element."
    source := "GenericMemory traversal invariant; base/summarysize.jl:45-116,171-190"
    status := .proven, prop := ``SummarySizeInBounds, thm := some ``summarySizeInBounds }
]

end JuliaLean.MemSafety.G2

namespace JuliaLean.MemSafety.G3

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-3.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-deepcopy-memory", juliaFile := "base/deepcopy.jl"
    juliaFns := ["_deepcopy_memory_t"]
    statement := "The non-bits loop stays within the source and destination; for bits elements copy allocates the same extent and its memmove byte count fits both memories without overflow."
    source := "base/deepcopy.jl:108-127; base/genericmemory.jl:197-207,223-225,257-263; src/genericmemory.c:55-71"
    status := .proven, prop := ``DeepcopyMemorySafe, thm := some ``deepcopyMemorySafe_proven },
  { id := "memsafety-environment-buffers", juliaFile := "base/env.jl"
    juliaFns := ["_environ", "iterate(::EnvDict)"]
    statement := "Every environment pointer read and Windows block copy uses an offset computed within the platform-defined null-terminated storage."
    source := "base/env.jl:54-75,193-245; GetEnvironmentStringsW and POSIX environ layout contracts"
    status := .proven, prop := ``EnvironmentBufferSafe, thm := some ``environmentBufferSafe_proven },
  { id := "memsafety-io-internal-buffers", juliaFile := "base/io.jl"
    juliaFns := ["ENDIAN_BOM initialization", "countlines"]
    statement := "The endianness probe reads the first of four allocated bytes, and countlines scans the computed 1:nb indices where readbytes! guarantees nb is at most 8192."
    source := "base/io.jl:817-834,1295-1300,1700-1714"
    status := .proven, prop := ``IOSafe, thm := some ``ioSafe_proven },

  { id := "memsafety-parse-integer", juliaFile := "base/parse.jl"
    juliaFns := ["skipspace", "skipspace_back", "parseint_preamble", "parseint_utf8"]
    statement := "Every unchecked byte index computed by the public integer parser's fast path, whitespace loops, sign and prefix branches, and trailing scan lies in 1:ncodeunits(s)."
    source := "base/parse.jl:68-147; parse and tryparse call parseint_utf8 with 1:ncodeunits(s)"
    status := .proven, prop := ``IntegerParseSafe, thm := some ``integerParseSafe_proven },
  { id := "memsafety-parsers-float", juliaFile := "base/parsers/floats.jl"
    juliaFns := ["eisellemire", "fromdecimal", "cmpmidpoint", "scandigits", "scanexponent", "scanhex", "parsehex", "matchword", "nanpayload", "parsespecial", "parsefloat"]
    statement := "The Eisel-Lemire and Clinger table offsets are computed within their tables, and every byte access across the float parser's guarded scan branches lies in the public 1:length(buf) span."
    source := "base/parsers/floats.jl:92-419; parsevalue supplies 1:length(bytes)"
    status := .proven, prop := ``FloatParseSafe, thm := some ``floatParseSafe_proven },
  { id := "memsafety-pcre-context-names", juliaFile := "base/pcre.jl"
    juliaFns := ["get_local_match_context", "capture_names"]
    statement := "The context-vector growth computed from maxthreadid covers the current thread, and capture_names computes both header-byte indices within every fixed-size PCRE2 name-table entry."
    source := "base/pcre.jl:37-63,265-280; PCRE2 API name table contract"
    status := .proven, prop := ``PcreNameTableSafe, thm := some ``pcreNameTableSafe_proven },
  { id := "memsafety-timing-globals", juliaFile := "base/timing.jl"
    juliaFns := ["gc_page_utilization_data", "full_sweep_reasons"]
    statement := "Both GC timing unsafe_wrap extents equal the matching C global-array extents, and enumerate reads only those wrapped reason elements."
    source := "base/timing.jl:148-184; src/gc-stock.c:75,942; src/gc-stock.h:571-579; src/gc-mmtk/gc-mmtk.c:1433-1434"
    status := .proven, prop := ``TimingGlobalsSafe, thm := some ``timingGlobalsSafe_proven }
]

end JuliaLean.MemSafety.G3

namespace JuliaLean.MemSafety.G4

open JuliaLean.Registry

/-- Registry entries for the sites in `memsafety/sites-4.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-boot-array-getindex", juliaFile := "base/boot.jl"
    juliaFns := ["getindex(::Array, ::Int) during bootstrap"]
    statement := "The bootstrap unsigned range check permits memoryrefget only at an index in 1:length(A)."
    source := "base/boot.jl:879-883"
    status := .proven, prop := ``BootArrayRefInBounds, thm := some ``bootArrayRefInBounds },
  { id := "memsafety-precompilation-process-stats", juliaFile := "base/precompilation.jl"
    juliaFns := ["_get_process_stats"]
    statement := "The UInt64 reads at byte offsets 8, 16 and 24 fit in the allocated 96-byte proc_taskinfo buffer."
    source := "base/precompilation.jl:2102-2111"
    status := .proven, prop := ``ProcessStatsReadsInBounds, thm := some ``processStatsReadsInBounds },
  { id := "memsafety-runtime-fieldname", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["fieldname", "getindex(::DataTypeFieldDesc)"]
    statement := "Both field accessors reject indices outside 1:nfields before their unchecked read."
    source := "base/runtime_internals.jl:391-405,797-812"
    status := .proven, prop := ``RuntimeFieldInBounds, thm := some ``runtimeFieldInBounds },
  { id := "memsafety-runtime-field-bitmaps", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["isconst(::Type, ::Int)", "isfieldatomic(::Type, ::Int)"]
    statement := "A checked field number maps to a word within the runtime field bitmap."
    source := "base/runtime_internals.jl:544-578; DataType field-bitmap representation invariant"
    status := .proven, prop := ``RuntimeBitfieldInBounds, thm := some ``runtimeBitfieldInBounds },
  { id := "memsafety-runtime-metadata", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["DataTypeLayout", "getindex(::DataTypeFieldDesc)", "get_require_world"]
    statement := "Runtime-owned metadata pointers are read only as their complete represented object after null and field checks."
    source := "runtime object representation; base/runtime_internals.jl:625-645,789-812,1662"
    status := .proven, prop := ``RuntimeMetadataAccessesInBounds, thm := some ``runtimeMetadataAccessesInBounds },

  { id := "memsafety-sysinfo-cpu-info", juliaFile := "base/sysinfo.jl"
    juliaFns := ["Sys.cpu_info"]
    statement := "cpu_info reads exactly the count records returned and initialized by libuv."
    source := "libuv uv_cpu_info contract; base/sysinfo.jl:309-323"
    status := .proven, prop := ``CpuInfoInBounds, thm := some ``cpuInfoInBounds }
]

end JuliaLean.MemSafety.G4

namespace JuliaLean.MemSafety.G5

open JuliaLean.Registry

/-- Registry entries for the proved and refuted sites in `memsafety/sites-5.tsv`. -/
def entries : List Entry := [
  { id := "memsafety-accumulate-indexing", juliaFile := "base/accumulate.jl"
    juliaFns := ["_accumulate_pairwise!", "accumulate_pairwise!", "_accumulate1!"]
    statement := "Every unchecked input and output access computed by the pairwise recursion and LinearIndices iterator is within both arrays after their equality checks."
    source := "array-axis invariant; base/accumulate.jl:7-35,436-451"
    status := .proven, prop := ``AccumulateAccessesInBounds
    thm := some ``accumulateAccessesInBounds },

  { id := "memsafety-accumulate-dimensional-initial", juliaFile := "base/accumulate.jl"
    juliaFns := ["_accumulate!", "_accumulaten!"]
    statement := "After the matching-axis and nonempty checks, each dimensional scan's initial unchecked read and write use the first index of the common axis."
    source := "array-axis invariant; base/accumulate.jl:374-390,404-425"
    status := .proven, prop := ``AccumulateDimsInitialAccessesInBounds
    thm := some ``accumulateDimsInitialAccessesInBounds },
  { id := "memsafety-options-commands", juliaFile := "base/options.jl"
    juliaFns := ["JLOptions", "unsafe_load_commands", "show(::IO, ::JLOptions)", "exec_options"]
    statement := "JLOptions loads one runtime object, and every command-table and first-byte load follows the runtime table's terminating null pointer."
    source := "runtime JLOptions layout invariant; base/options.jl:79-85,105-133; base/client.jl:268; base/show.jl:287"
    status := .proven, prop := ``OptionsCommandsAccessesInBounds
    thm := some ``optionsCommandsAccessesInBounds },
  { id := "memsafety-rawbigfloats-get-elem", juliaFile := "base/rawbigfloats.jl"
    juliaFns := ["get_elem(::BigFloatData, ::Int, ::Val{:words}, ::Val{:ascending})", "get_elem(::BigFloatData, ::Int, ::Val{:descending})", "truncated", "BigFloatDataRoundingIncrementHelper", "tail_is_nonzero"]
    statement := "Every unchecked BigFloatData word load computed by truncation, descending indexing, final and round bits, and sticky-bit scanning is within the limb vector."
    source := "base/rawbigfloats.jl:5-142; public BigFloat-to-Float callers at base/mpfr.jl:494-552"
    status := .proven, prop := ``RawBigFloatAccessesInBounds
    thm := some ``rawBigFloatAccessesInBounds },
  { id := "memsafety-show-bits", juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, x)"]
    statement := "The raw-bits display branch reads exactly the descending byte offsets below cld(bitsizeof(typeof(x)), 8)."
    source := "bits object storage invariant; base/show.jl:530-565"
    status := .proven, prop := ``ShowBitsAccessesInBounds
    thm := some ``showBitsAccessesInBounds },
  { id := "memsafety-stream-redirect-global", juliaFile := "base/stream.jl"
    juliaFns := ["_redirect_io_cglobal", "RedirectStdStream"]
    statement := "The redirect helper's nested descriptor branch either performs no store or stores at the implicit first element of one scalar runtime global."
    source := "runtime scalar-global invariant; base/stream.jl:1928-1978"
    status := .proven, prop := ``StreamRedirectAccessesInBounds
    thm := some ``streamRedirectAccessesInBounds },
  { id := "memsafety-thread-runtime-globals", juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["maxthreadid", "_nthreads_in_pool", "nthreadpools", "ngcthreads", "threadpoolsize", "threadpooltids", "multiq_size", "@spawn"]
    statement := "Scalar thread globals use their only cell, and every public caller maps to one of the two entries in jl_n_threads_per_pool."
    source := "runtime thread-pool layout invariant; base/threadingconstructs.jl:38-169,828; base/partr.jl:111,132"
    status := .proven, prop := ``ThreadRuntimeAccessesInBounds
    thm := some ``threadRuntimeAccessesInBounds },
  { id := "memsafety-toml-take-chunks", juliaFile := "base/toml/parser.jl"
    juliaFns := ["parse_string_continue", "take_chunks", "TOML.parse", "TOML.tryparse"]
    statement := "Every take_chunks source span recorded by the parser cursor lies in l.str, and every destination span lies in the string allocated from the sum of chunk lengths."
    source := "Parser cursor and chunk representation invariant; base/toml/parser.jl:75-149,1360-1462"
    status := .proven, prop := ``TomlTakeChunksAccessesInBounds
    thm := some ``tomlTakeChunksAccessesInBounds },
  { id := "memsafety-version-matches", juliaFile := "base/version.jl"
    juliaFns := ["matches_spec_range!"]
    statement := "The exact lower-search and upper-marking loops read versions and write dest only after their i <= n check and the two length assertions."
    source := "base/version.jl:530-560"
    status := .proven, prop := ``VersionMatchesAccessesInBounds
    thm := some ``versionMatchesAccessesInBounds },
  { id := "memsafety-version-intersect", juliaFile := "base/version.jl"
    juliaFns := ["intersect(::VersionSpec, ::VersionSpec)"]
    statement := "The nested range product loop writes one one-based slot for each pair into the allocation with that product length."
    source := "base/version.jl:570-579"
    status := .proven, prop := ``VersionIntersectAccessesInBounds
    thm := some ``versionIntersectAccessesInBounds },

]

end JuliaLean.MemSafety.G5

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

namespace JuliaLean.MemSafety

open JuliaLean.Registry

/-- Registry entries of this area; group `G<n>` covers `memsafety/sites-<n>.tsv`. -/
def entries : List Entry :=
  G1.entries ++ G2.entries ++ G3.entries ++ G4.entries ++ G5.entries ++ G6.entries

end JuliaLean.MemSafety

/-!
Parsing and printing numbers.

* `IntParse`: `parse`/`tryparse` for every `BitInteger` type from UTF-8 bytes
  (`base/parse.jl`, `base/parsers/ints.jl`), including whitespace, signs, `0x`/`0o`/`0b`
  prefixes, bases 2..62 and the decimal fast paths.
* `IntPrint`: `string(n; base, pad)` with the `bin`/`oct`/`dec`/`hex`/`_base` writers,
  `digits`, `digits!` and `bitstring` (`base/intfuncs.jl`), reusing `ndigits` from
  `IntArith.PowersDigits`.
* `Ryu`: `Ryu.writeshortest` on exact binary64 (`base/ryu/shortest.jl`, `utils.jl`),
  including `compact`, `precision`, `hash`, `padexp` and `typed`.
* `RoundDigits`: `round(x; digits)` for negative digit counts (`base/floatfuncs.jl`).

Differential checks against Julia master, all matching: 41,310 `parse`/`tryparse`
rows (all ten types; bases none, 1, 2, 7, 10, 16, 36, 62, 63; edge, random, prefixed,
whitespace and boundary strings), 10,165 `string`/`digits`/`bitstring` rows (all ten
types; bases -63..63 edge set including invalid ones; pads -2, 0, 1, 5, 40), 7,219
Float64 `string`/compact `show` rows (edge bit patterns and random values), 3,564
`round(x, r; digits=-k)` rows (four rounding modes, k from 1 to 308).
`parse(Float64, s)` is pure Julia on master (`base/parsers/floats.jl`,
Clinger/Eisel-Lemire) but is not modelled here; 1.13.2 calls C `jl_try_substrtod`.
-/

namespace JuliaLean.ParsePrint

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "parseprint-tryparse-nothing-iff-parse-throws", juliaFile := "base/parse.jl"
    juliaFns := ["parse(::Type{<:Integer}, ::AbstractString; base)", "tryparse(::Type{<:Integer}, ::AbstractString; base)"]
    statement := "For every BitInteger type, byte string and valid base, tryparse returns nothing exactly when parse throws, and otherwise both return the same value."
    source := "base/parse.jl:241-254", status := .proven
    prop := ``IntParse.TryparseNothingIffParseThrows, thm := some ``IntParse.tryparseNothingIffParseThrows
    notes := "Both call tryparse_internal/parseint_utf8 on the whole string; the proof shows the shared core (fast decimal path, preamble, prefix handling and checked loop) always terminates with a value or a failure record, and parse throws exactly on the failure. Same structure in 1.13.2 (parseint_preamble on Chars)." },
  { id := "parseprint-parse-overflow-detected", juliaFile := "base/parsers/ints.jl"
    juliaFns := ["parse(::Type{<:Integer}, ::AbstractString; base)", "Parsers.parseint"]
    statement := "For every BitInteger type and base 10 or 16, parsing the spelling of any integer within 16 of typemin, typemax, ±2^64 or ±2^128 returns that integer if it fits and throws otherwise; no wrapped value is returned."
    source := "base/parsers/ints.jl:150-173 (invariant: parse returns the value of the string or throws OverflowError)", status := .proven
    prop := ``IntParse.ParseOverflowDetected, thm := some ``IntParse.parseOverflowDetected
    notes := "Exhaustive decide +kernel over 10 types x 2 bases x 6 centres x 33 offsets (7,920 strings, up to 39 digits). The centres cover the type bounds and the wrap points of the UInt64/UInt128 accumulator. Random long strings were also differential-checked." },
  { id := "parseprint-ryu-compact-lost-digit", juliaFile := "base/ryu/shortest.jl"
    juliaFns := ["Ryu.reduce_shortest", "Ryu.writeshortest", "show(::IO, ::Float64) with :compact"]
    statement := "Compact display of a finite nonzero Float64 is within half a unit in the sixth significant digit of the value (plus the first rounding to shortest)."
    source := "base/ryu/Ryu.jl:46 (compact: output will be limited to 6 significant digits), base/ryu/Ryu.jl:128-136", status := .refuted
    prop := ``Ryu.CompactSixDigits, thm := some ``Ryu.compactSixDigits_refuted
    issue := "none found; related #33185 (closed, different compact rounding regression). Searched issues: compact show float digits; compact float printing; compact 1e16; Ryu compact; maxsignif; reduce_shortest; PRs: compact float; Ryu shortest; writeshortest"
    notes := "1.7562091489257724e16 shows as 1.7562e16 (error 9.1e10 > 5e10). The a_allzero loop in reduce_shortest removes a zero sixth digit after already dropping the rounding digit. Same in both versions." },
  { id := "parseprint-ryu-compact-tie-even", juliaFile := "base/ryu/shortest.jl"
    juliaFns := ["Ryu.reduce_shortest", "show(::IO, ::Float64) with :compact"]
    statement := "Compact display rounds an exact seven-digit tie k*10^e (last digit 5) to the even six-digit neighbour, as reduce_shortest does for smaller values."
    source := "base/ryu/shortest.jl:131-133,174,209 (ties-to-even invariant)", status := .refuted
    prop := ``Ryu.CompactTiesToEven, thm := some ``Ryu.compactTiesToEven_refuted
    issue := "none found. Searched issues: compact tie even; round half even compact; compact float printing; Ryu compact; PRs: compact float; Ryu shortest; writeshortest"
    notes := "1.234565e17 shows as 1.23457e17; 1234565.0 shows as 1.23456e6. The mod-5 test at shortest.jl:59 mixes UInt32 and UInt64 and is never zero for v >= 2^32. Could be read as an unspecified tie rule (maybe intended)." },
  { id := "parseprint-ryu-precision-pow10-overflow", juliaFile := "base/ryu/shortest.jl"
    juliaFns := ["Ryu.writeshortest"]
    statement := "writeshortest with precision p uses fixed notation for x = 10^k exactly whenever k < p."
    source := "base/ryu/shortest.jl:337-338 (branch invariant), base/ryu/Ryu.jl:41", status := .refuted
    prop := ``Ryu.PrecisionFixedPowersOfTen, thm := some ``Ryu.precisionFixedPowersOfTen_refuted
    issue := "none found. Searched issues: writeshortest precision; Ryu precision; writeshortest 1e19; Ryu precision exponent form; PRs: writeshortest; writeshortest precision"
    notes := "With precision 30, 1e18 is fixed but 1e19 and 1e20 use exponent form: 10^(pt - olength) overflows Int. Only direct writeshortest callers pass such precisions. Same in both versions." },
  { id := "parseprint-round-digits-overflow-zero", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["round(::Real, ::RoundingMode; digits, sigdigits)", "Base._round_step"]
    statement := "round(x; digits=-k) of a finite x >= 10^k is never zero (the nearest multiple of 10^k is at least 10^k)."
    source := "base/rounding.jl:341-345", status := .refuted
    prop := ``RoundDigits.RoundDigitsNonzero, thm := some ``RoundDigits.roundDigitsNonzero_refuted
    issue := "none found; open #63105 rewrites round with digits but keeps this branch. Searched issues: round sigdigits floatmax; round digits overflow zero; round floatmax; _round_step; PRs: round sigdigits; _round_step; round digits overflow"
    notes := "round(floatmax(); digits=-308) and round(floatmax(); sigdigits=1) return 0.0: the overflow branch of _round_step returns zero. The model takes the step as the correctly rounded 10^k; Julia's 10.0^k is not correctly rounded for some k (first k = 33) but is for k = 308. Same in both versions." }
]

end JuliaLean.ParsePrint

namespace JuliaLean.MiscCov

open JuliaLean.Registry Lean

private def proven (id file : String) (fns : List String) (statement source : String)
    (prop thm : Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement, source, status := .proven,
    prop, thm := some thm }

private def refuted (id file : String) (fns : List String) (statement source issue : String)
    (prop thm : Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement, source, status := .refuted,
    prop, thm := some thm, issue }

/-- Registry entries of this area. -/
def entries : List Entry := [
  proven "misccov-deprecated-internal-change" "base/deprecated.jl" ["__has_internal_change"]
    "The cutoff and named-change branches return their documented Boolean result." "base/deprecated.jl:110-113"
    ``Deprecated.HasInternalChange ``Deprecated.hasInternalChange_proven,
  proven "misccov-deprecated-macro" "base/deprecated.jl" ["@deprecate", "cannot_export_nonsymbol"]
    "@deprecate validates signatures and emits the documented forwarding method and export." "base/deprecated.jl:179-231"
    ``Deprecated.DeprecateContract ``Deprecated.deprecateContract_proven,
  proven "misccov-depwarn" "base/deprecated.jl" ["depwarn", "_depwarn", "firstcaller"]
    "Deprecation levels and caller discovery produce the documented error or warning record." "base/deprecated.jl:253-317"
    ``Deprecated.DepwarnContract ``Deprecated.depwarnContract_proven,
  proven "misccov-deprecated-bindings" "base/deprecated.jl" ["deprecate", "@deprecate_binding", "@deprecate_stdlib", "@deprecate_moved"]
    "Binding deprecations emit the documented aliases, messages, exports and flags." "base/deprecated.jl:319-376"
    ``Deprecated.BindingContract ``Deprecated.bindingContract_proven,

  proven "misccov-experimental-const" "base/experimental.jl" ["IndexStyle", "size", "axes", "getindex"]
    "Const arrays preserve dimensions and return the stored value at every in-bounds index." "base/experimental.jl:19-39"
    ``ExperimentalConstIndexingClosed ``experimentalConstIndexingClosed_proven,
  refuted "misccov-max-methods-default" "base/experimental.jl" ["@max_methods"]
    "Every documented @max_methods setting expands successfully." "base/experimental.jl:55-66"
    "none found (queries: @max_methods default, max_methods default MethodError)"
    ``Experimental.MaxMethodsDoc ``Experimental.maxMethodsDoc_refuted,
  proven "misccov-experimental-options" "base/experimental.jl" ["@aliasscope", "@optlevel", "@max_methods", "@compiler_options", "@force_compile"]
    "Compiler-option macros validate inputs and emit the corresponding meta expressions." "base/experimental.jl:42-139"
    ``Experimental.OptionMacros ``Experimental.optionMacros_proven,
  proven "misccov-experimental-checked" "base/experimental.jl" ["make_all_arithmetic_checked", "+", "-", "*"]
    "Generated checked arithmetic methods return exact results or overflow errors." "base/experimental.jl:142-172"
    ``Experimental.CheckedArithmetic ``Experimental.checkedArithmetic_proven,
  proven "misccov-experimental-sync" "base/experimental.jl" ["sync_end"]
    "sync_end waits for every task and forwards every completion." "base/experimental.jl:180-198"
    ``Experimental.SyncContract ``Experimental.syncContract_proven,
  proven "misccov-experimental-sync-macro" "base/experimental.jl" ["@sync"]
    "@sync creates the channel, rewrites async calls and invokes sync_end." "base/experimental.jl:200-207"
    ``Experimental.SyncMacroShape ``Experimental.syncMacroShape_proven,
  proven "misccov-experimental-hints" "base/experimental.jl" ["register_error_hint", "show_error_hints"]
    "Error-hint handlers retain registration order and run for the exception type chain." "base/experimental.jl:214-257"
    ``Experimental.HintsContract ``Experimental.hintsContract_proven,
  proven "misccov-experimental-overlay" "base/experimental.jl" ["overlay_def!", "overlay", "consistent_overlay"]
    "Overlay helpers accept documented definitions and emit their matching metadata." "base/experimental.jl:265-355"
    ``Experimental.OverlayContract ``Experimental.overlayContract_proven,
  proven "misccov-experimental-methodtable" "base/experimental.jl" ["new_mt", "@MethodTable"]
    "MethodTable construction checks top-level use and preserves its name and module." "base/experimental.jl:363-379"
    ``Experimental.MethodTableContract ``Experimental.methodTableContract_proven,
  proven "misccov-experimental-runtime" "base/experimental.jl" ["make_io_thread", "entrypoint", "disable_new_worlds", "task_metrics", "task_running_time_ns", "task_wall_time_ns"]
    "Runtime helpers propagate errors, set flags and compute wrapped task times." "base/experimental.jl:387-471"
    ``Experimental.RuntimeContract ``Experimental.runtimeContract_proven,
  proven "misccov-experimental-wait" "base/experimental.jl" ["wait_with_timeout"]
    "Timed waits return the waiter, timeout or cancellation result from the first event." "base/experimental.jl:479-525"
    ``Experimental.WaitContract ``Experimental.waitContract_proven,
  proven "misccov-experimental-syntax" "base/experimental.jl" ["set_syntax_version", "@VERSION", "reexport"]
    "Syntax-version and reexport helpers validate and emit the documented module operations." "base/experimental.jl:533-598"
    ``Experimental.SyntaxContract ``Experimental.syntaxContract_proven,
  proven "misccov-experimental-prune-objcache" "base/experimental.jl" ["prune_objcache"]
    "A disabled cache is neither pruned nor copied, a failed prune skips compaction, and successful compaction returns the number removed."
    "base/experimental.jl:853-861" ``Experimental.PruneObjcacheContract ``Experimental.pruneObjcacheContract_proven,

  refuted "misccov-shell-fd-overflow" "base/shell.jl" ["__repl_entry_shell_parse", "shell_parse"]
    "Every unsupported redirect descriptor produces the parser's unsupported-fd error." "base/shell.jl:195-201"
    "none found (queries: shell_parse fd overflow, unsupported fd redirect OverflowError)"
    ``Shell.FdErrorType ``Shell.fdErrorType_refuted,
  refuted "misccov-shell-redirect-before-pipe" "base/shell.jl" ["__repl_entry_shell_parse", "shell_parse"]
    "A redirect operator immediately before a pipe is rejected for lacking a filename." "base/shell.jl:302-303"
    "none found (queries: shell_parse redirect before pipe)"
    ``Shell.RedirectNeedsFilename ``Shell.redirectNeedsFilename_refuted,
  refuted "misccov-shell-empty-word-redirect" "base/shell.jl" ["__repl_entry_shell_parse", "shell_parse"]
    "A quoted empty argument immediately before a redirect remains an argument." "base/shell.jl:129,307"
    "none found (queries: shell_parse empty quoted argument redirect)"
    ``Shell.EmptyWordBeforeRedirect ``Shell.emptyWordBeforeRedirect_refuted,
  proven "misccov-shell-word-helpers" "base/shell.jl" ["push_nonempty!", "consume_upto!", "append_2to1!"]
    "Word helpers preserve nonempty spans and represent a quoted empty word." "base/shell.jl:63-77"
    ``Shell.WordHelpers ``Shell.wordHelpers_proven,
  proven "misccov-shell-dollar" "base/shell.jl" ["parse_dollar_interp"]
    "Dollar interpolation parses the next atom and rejects a terminal dollar sign." "base/shell.jl:86-103"
    ``Shell.DollarInterp ``Shell.dollarInterp_proven,
  proven "misccov-shell-redirect-word" "base/shell.jl" ["redirect_word_expr"]
    "Redirect words remain strings or become interpolation expressions according to their parts." "base/shell.jl:106-114"
    ``Shell.RedirectWord ``Shell.redirectWord_proven,
  proven "misccov-shell-build-segment" "base/shell.jl" ["build_seg_expr"]
    "Command segments and redirect flags produce the corresponding command or pipeline syntax." "base/shell.jl:328-343"
    ``Shell.BuildSegShape ``Shell.buildSegShape_proven,

  proven "misccov-baseext" "base/baseext.jl" ["VecElement", "convert", "Array", "Vector", "Matrix"]
    "VecElement and Array convenience methods preserve conversions, rank, dimensions and fill values." "base/baseext.jl:17-45"
    ``BaseExtContractClosed ``baseExtContractClosed_proven,
  proven "misccov-scope" "base/scope.jl" ["Scope"]
    "Scope constructors preserve existing scopes and extend a parent once per pair." "base/scope.jl:24-47"
    ``ScopeContractClosed ``scopeContractClosed_proven,

  proven "misccov-cfunction" "base/c.jl" ["unsafe_convert", "cfunction"]
    "CFunction conversion and syntax construction preserve pointer and signature arguments." "base/c.jl:32-52"
    ``CInterface.CfunctionContract ``CInterface.cfunctionContract_proven,
  proven "misccov-c-sigint" "base/c.jl" ["sigatomic_begin", "sigatomic_end", "disable_sigint", "reenable_sigint", "exit_on_sigint"]
    "Signal helpers balance the runtime counter and propagate results, errors and mode updates." "base/c.jl:55-107"
    ``CInterface.SigintContract ``CInterface.sigintContract_proven,
  refuted "misccov-ccallable-forward-decl" "base/c.jl" ["@ccallable", "expand_ccallable"]
    "Every non-method definition produces @ccallable's expected-method error." "base/c.jl:119-180"
    "none found (queries: @ccallable forward declaration FieldError)"
    ``CInterface.CcallableErrors ``CInterface.ccallableErrors_refuted,
  proven "misccov-ccallable-expand" "base/c.jl" ["_ccallable", "expand_ccallable", "@ccallable"]
    "@ccallable extracts and emits the registration and escaped definition." "base/c.jl:109-180"
    ``CInterface.CcallableExpand ``CInterface.ccallableExpand_proven,
  refuted "misccov-ccall-macro-parse-doc" "base/c.jl" ["ccall_macro_parse"]
    "ccall_macro_parse returns the four values and bare function described by its docstring." "base/c.jl:185-193"
    "none found (queries: ccall_macro_parse docstring tuple)"
    ``CInterface.CcallMacroParseDoc ``CInterface.ccallMacroParseDoc_refuted,
  proven "misccov-ccall-parse" "base/c.jl" ["pusharg!", "ccall_macro_parse"]
    "ccall parsing separates typed arguments and every call option." "base/c.jl:195-350"
    ``CInterface.CcallMacroParse ``CInterface.ccallMacroParse_proven,
  proven "misccov-ccall-lower" "base/c.jl" ["ccall_macro_lower", "@ccall", "ccall_effects"]
    "ccall lowering emits conversions and the requested convention, effects and safety flags." "base/c.jl:352-424"
    ``CInterface.CcallLower ``CInterface.ccallLower_proven,

  proven "misccov-module-import-path" "base/module.jl" ["check_macro_rename", "eval_import_path", "eval_import_path_all", "_eval_using"]
    "Import-path evaluation validates renames and preserves every path effect." "base/module.jl:3-154"
    ``Module.ImportPathContract ``Module.importPathContract_proven,
  proven "misccov-module-import" "base/module.jl" ["_eval_import"]
    "_eval_import processes paths in order and propagates the first error." "base/module.jl:156-236"
    ``Module.ImportContract ``Module.importContract_proven,

  proven "misccov-osutils-static" "base/osutils.jl" ["@static"]
    "@static evaluates conditional syntax recursively and preserves other expressions." "base/osutils.jl:24-48"
    ``Static.Contract ``Static.contract_proven,
  proven "misccov-flfrontend" "base/flfrontend.jl" ["fl_parse", "fl_lower"]
    "Frontend wrappers normalize inputs and preserve every parse and lowering option." "base/flfrontend.jl:5-29"
    ``FlFrontend.Contract ``FlFrontend.contract_proven,
  proven "misccov-coreir" "base/coreir.jl" ["PhiNode", "PartialStruct", "partialstruct_init_undefs", "==", "getproperty"]
    "Core IR constructors validate fields and expose structural equality and properties." "base/coreir.jl:3-67"
    ``CoreIR.Contract ``CoreIR.contract_proven,
  proven "misccov-opaque-closure" "base/opaque_closure.jl" ["@opaque", "generate_opaque_closure", "OpaqueClosure"]
    "Opaque-closure helpers preserve signature, bounds, arity, environment and options." "base/opaque_closure.jl:3-92"
    ``OpaqueClosure.Contract ``OpaqueClosure.contract_proven,

  proven "misccov-base-pair" "base/Base.jl" ["Pair"]
    "The typed Pair constructor converts each mismatched component exactly once." "base/Base.jl:10-13"
    ``PairContractClosed ``pairContractClosed_proven,
  proven "misccov-base-small" "base/Base.jl" ["array_new_memory", "sizeof", "isdebugbuild", "a_method_to_overwrite_in_test", "include", "IncludeInto", "in_sysimage"]
    "Small Base wrappers preserve ownership, byte size, flags, include arguments and membership." "base/Base.jl:46-57,87,135-137,350-363"
    ``BaseJl.SmallContract ``BaseJl.smallContract_proven,
  proven "misccov-base-sigint" "base/Base.jl" ["sigint_new_episode!", "sigint_close_episode!", "sigint_active_severity", "_sigint_dispatch_pass", "maybe_dispatch_sigint", "sigint_listener"]
    "Interrupt episodes preserve generation matching, monotone cancellation and dispatch claims." "base/Base.jl:445-553"
    ``BaseJl.SigintContract ``BaseJl.sigintContract_proven,
  proven "misccov-base-listeners" "base/Base.jl" ["profile_printing_listener", "start_profile_listener", "start_sigint_listener"]
    "Listener setup creates the required tasks, callbacks and finalizers." "base/Base.jl:370-407,563-589"
    ``BaseJl.ListenerContract ``BaseJl.listenerContract_proven,
  proven "misccov-base-init" "base/Base.jl" ["__init__"]
    "Base initialization performs each state reset and startup action in source order." "base/Base.jl:591-623"
    ``BaseJl.InitContract ``BaseJl.initContract_proven,
  proven "misccov-download" "base/download.jl" ["Downloads", "download", "do_download"]
    "Download wrappers load Downloads, select the path, transfer and return the path." "base/download.jl:3-25"
    ``BaseJl.DownloadContract ``BaseJl.downloadContract_proven,

  proven "misccov-parsers-helpers" "base/parsers/ints.jl" ["load8", "isdigits8", "digits8", "bytesin", "ishexdigits8", "hexdigits8", "digitvalue", "overflowfailure"]
    "Parser byte helpers load, classify and convert digits and distinguish invalid tails." "base/parsers/ints.jl:10-78"
    ``Parsers.HelperContract ``Parsers.helperContract_proven,
  proven "misccov-parsers-parse" "base/parsers/ints.jl" ["parseint", "parsevalue"]
    "Integer parsing follows each source branch and returns values or structured failures." "base/parsers/ints.jl:86-190"
    ``Parsers.ParseContract ``Parsers.parseContract_proven,
  proven "misccov-parsers-show" "base/parsers/Parsers.jl" ["show(::ParseFailure)"]
    "Each ParseFailure prints its qualified constant name." "base/parsers/Parsers.jl:52-53"
    ``Parsers.HelperContract ``Parsers.helperContract_proven,
  refuted "misccov-parsers-parsevalue-bool" "base/parsers/ints.jl" ["parseint", "parsevalue"]
    "parsevalue for every integer type returns a value or ParseFailure without throwing." "base/parsers/Parsers.jl:58-63; base/parsers/ints.jl:161-190"
    "PR #63971 (open, same Bool failure)"
    ``Parsers.ParsevalueNoThrow ``Parsers.parsevalueNoThrow_refuted,

  proven "misccov-ryu-log-range" "base/ryu/utils.jl" ["log10pow2", "log10pow5", "pow5bits"]
    "Fixed-point logarithm helpers are exact on Ryu's algorithmic ranges." "base/ryu/utils.jl:23-43"
    ``RyuUtils.LogApproxRange ``RyuUtils.logApproxRange_proven,
  refuted "misccov-ryu-log10pow-negative" "base/ryu/utils.jl" ["log10pow2", "log10pow5"]
    "The documented bounds make the logarithm helpers valid for negative exponents." "base/ryu/utils.jl:23-35"
    "none found (queries: Ryu log10pow2 negative, log10pow5 negative)"
    ``RyuUtils.LogApproxDoc ``RyuUtils.logApproxDoc_refuted,
  proven "misccov-ryu-mulshift" "base/ryu/utils.jl" ["mulshift", "mulshiftinvsplit", "mulshiftsplit"]
    "Split multiplication returns the exact requested high shifted product." "base/ryu/utils.jl:49-53,132-146"
    ``RyuUtils.MulshiftExact ``RyuUtils.mulshiftExact_proven,
  proven "misccov-ryu-index" "base/ryu/utils.jl" ["indexforexp", "pow10bitsforindex", "lengthforindex"]
    "Ryu index helpers implement their integer formulas." "base/ryu/utils.jl:55-57"
    ``RyuUtils.IndexHelpers ``RyuUtils.indexHelpers_proven,
  proven "misccov-ryu-powers" "base/ryu/utils.jl" ["pow5", "pow2"]
    "Power helpers recognize divisibility by their requested powers." "base/ryu/utils.jl:64-87"
    ``RyuUtils.Pow5Pow2Exact ``RyuUtils.pow5Pow2Exact_proven,
  refuted "misccov-ryu-decimallength-doc" "base/ryu/utils.jl" ["decimallength"]
    "decimallength returns the decimal digit count for every accepted integer." "base/ryu/utils.jl:91-130"
    "none found (queries: Ryu decimallength 18 digits, decimallength UInt32)"
    ``RyuUtils.DecimallengthDoc ``RyuUtils.decimallengthDoc_refuted,
  proven "misccov-ryu-decimallength-range" "base/ryu/utils.jl" ["decimallength"]
    "Each decimallength overload is exact throughout Ryu's used range." "base/ryu/utils.jl:94-130"
    ``RyuUtils.DecimallengthRange ``RyuUtils.decimallengthRange_proven,
  proven "misccov-ryu-umul256" "base/ryu/utils.jl" ["umul256", "umul256_hi"]
    "umul256 returns the exact low and high halves of the 256-bit product." "base/ryu/utils.jl:153-183"
    ``RyuUtils.Umul256Exact ``RyuUtils.umul256Exact_proven,
  proven "misccov-ryu-mod1e9" "base/ryu/utils.jl" ["mod1e9", "mulshiftmod1e9"]
    "Remainder helpers equal the mathematical result modulo one billion." "base/ryu/utils.jl:185-206"
    ``RyuUtils.Mod1e9Exact ``RyuUtils.mod1e9Exact_proven,
  proven "misccov-ryu-output-helpers" "base/ryu/utils.jl" ["append_sign", "append_d_digits"]
    "Output helpers write the requested sign and decimal separator." "base/ryu/utils.jl:208-230"
    ``RyuUtils.AppendSignDigits ``RyuUtils.appendSignDigits_proven,
  proven "misccov-ryu-table-formulas" "base/ryu/utils.jl" ["pow5split", "pow5invsplit"]
    "Power-of-five split values equal their integer formulas." "base/ryu/utils.jl:279-312"
    ``RyuUtils.Pow5SplitFormulas ``RyuUtils.pow5SplitFormulas_proven,
  refuted "misccov-ryu-pow5invsplit-bitcount" "base/ryu/utils.jl" ["pow5invsplit", "pow5_inv_bitcount"]
    "pow5invsplit has exactly the documented significant-bit count." "base/ryu/utils.jl:271-284"
    "none found (queries: Ryu pow5invsplit bitcount)"
    ``RyuUtils.Pow5InvsplitBitcount ``RyuUtils.pow5InvsplitBitcount_refuted,
  proven "misccov-ryu-lookups" "base/ryu/utils.jl" ["pow5invsplit_lookup", "pow5split_lookup"]
    "Generated lookup methods return their matching table entries." "base/ryu/utils.jl:286-325"
    ``RyuUtils.LookupTables ``RyuUtils.lookupTables_proven,
  proven "misccov-ryu-inverse-tables" "base/ryu/utils.jl" ["generateinversetables"]
    "Generated inverse tables preserve limb bounds, growth and entry counts." "base/ryu/utils.jl:242-268"
    ``RyuUtils.InverseTablesShape ``RyuUtils.inverseTablesShape_proven,

  proven "misccov-ryu-digit-counts" "base/ryu/Ryu.jl" ["neededdigits", "neededfloatdigits"]
    "Ryu buffer-size helpers return the source constants for every float width." "base/ryu/Ryu.jl:16-27"
    ``RyuWrap.DigitCounts ``RyuWrap.digitCounts_proven,
  proven "misccov-ryu-wrappers" "base/ryu/Ryu.jl" ["writeshortest", "writefixed", "writeexp", "show", "string", "print"]
    "Allocating format wrappers validate precision, size buffers and forward options." "base/ryu/Ryu.jl:48-145"
    ``RyuWrap.WrapperContract ``RyuWrap.wrapperContract_proven
]

end JuliaLean.MiscCov

namespace JuliaLean.Registry

/-- Every registered Base property. Each area module and each `JuliaLean.Proofs.base` file
contributes its own `entries`. -/
def all : List Entry :=
  JuliaLean.Float.entries
    ++ JuliaLean.IntArith.entries
    ++ JuliaLean.Ranges.entries
    ++ JuliaLean.Sort.entries
    ++ JuliaLean.FloatRanges.entries
    ++ JuliaLean.Strings.entries
    ++ JuliaLean.ParsePrint.entries
    ++ JuliaLean.ArrayOps.entries
    ++ JuliaLean.MathFuncs.entries
    ++ JuliaLean.Reduce.entries
    ++ JuliaLean.IOBuffers.entries
    ++ JuliaLean.VersionNumbers.entries
    ++ JuliaLean.Promotion.entries
    ++ JuliaLean.Toml.entries
    ++ JuliaLean.RegexUnicode.entries
    ++ JuliaLean.Show.entries
    ++ JuliaLean.Multidim.entries
    ++ JuliaLean.BigNums.entries
    ++ JuliaLean.MissingChar.entries
    ++ JuliaLean.StringUtil.entries
    ++ JuliaLean.ShellCmd.entries
    ++ JuliaLean.Transcode.entries
    ++ JuliaLean.FloatFuncs.entries
    ++ JuliaLean.Channels.entries
    ++ JuliaLean.Printf.entries
    ++ JuliaLean.Dates.entries
    ++ JuliaLean.Base64Uuid.entries
    ++ JuliaLean.BroadcastViews.entries
    ++ JuliaLean.RandomSampling.entries
    ++ JuliaLean.Sockets.entries
    ++ JuliaLean.Serialization.entries
    ++ JuliaLean.Markdown.entries
    ++ JuliaLean.IdDicts.entries
    ++ JuliaLean.AbstractArrays.entries
    ++ JuliaLean.HashOps.entries
    ++ JuliaLean.Artifacts.entries
    ++ JuliaLean.MemSafety.entries
    ++ JuliaLean.Proofs.base.gcutils.memory_safety.entries
    ++ JuliaLean.Proofs.base.libdl.memory_safety.entries
    ++ JuliaLean.Proofs.base.module.memory_safety.entries
    ++ JuliaLean.Proofs.base.simdloop.memory_safety.entries
    ++ JuliaLean.Proofs.base.reflection.memory_safety.entries
    ++ JuliaLean.Proofs.base.array.wrap_memory_safety.entries
    ++ JuliaLean.Proofs.base.missing.memory_safety.entries
    ++ JuliaLean.Proofs.base.accumulate.entries
    ++ JuliaLean.Proofs.base.threadingconstructs.entries
    ++ JuliaLean.Proofs.base.array.entries
    ++ JuliaLean.Proofs.base.ryu.utils.entries
    ++ JuliaLean.Combinatorics.entries
    ++ JuliaLean.Logging.entries
    ++ JuliaLean.Loading.entries
    ++ JuliaLean.Streams.entries
    ++ JuliaLean.Files.entries
    ++ JuliaLean.ExprReflect.entriesExpr
    ++ JuliaLean.ExprReflect.entriesMeta
    ++ JuliaLean.ExprReflect.entriesRuntime_internals
    ++ JuliaLean.ExprReflect.entriesReflection
    ++ JuliaLean.ExprReflect.entriesEnums
    ++ JuliaLean.ExprReflect.entriesCartesian
    ++ JuliaLean.ErrorShow.entries
    ++ JuliaLean.Tasks.entries
    ++ JuliaLean.NumMisc.entries
    ++ JuliaLean.AbstractArrayCov.entries
    ++ JuliaLean.BroadcastCov.entries
    ++ JuliaLean.IteratorsCov.entries
    ++ JuliaLean.ShowCov.entries
    ++ JuliaLean.RangesCov.entries
    ++ JuliaLean.Proofs.base.rawbigfloats.entries
    ++ JuliaLean.FloatIntCov.entries

    ++ JuliaLean.RuntimeCov.entries
    ++ JuliaLean.Proofs.base.runtime_internals.entries
    ++ JuliaLean.Proofs.base.Base_compiler.entries
    ++ JuliaLean.Proofs.base.runtime_internals.LegacyRuntime.entries
    ++ JuliaLean.Proofs.base.precompilation.LegacyRuntime.entries
    ++ JuliaLean.Proofs.base.array.LegacyRefutations.entries
    ++ JuliaLean.Proofs.base.array.LegacyCartesianFilter.entries
    ++ JuliaLean.Proofs.base.reshapedarray.LegacyRuntime.entries
    ++ JuliaLean.Proofs.base.osinfo.entriesLegacyRetired
    ++ JuliaLean.MathCov.entries
    ++ JuliaLean.IOCov.entries
    ++ JuliaLean.Proofs.base.reflection.entries
    ++ JuliaLean.Proofs.base.stacktraces.entries
    ++ JuliaLean.Proofs.base.experimental.entries
    ++ JuliaLean.SortTuplesCov.entries
    ++ JuliaLean.ReduceCov.TraitsEntries.entries
    ++ JuliaLean.ReduceCov.IndicesEntries.entries
    ++ JuliaLean.ReduceCov.SomeRows.entries
    ++ JuliaLean.ReduceCov.MissingCov.entries
    ++ JuliaLean.ReduceCov.ReduceRows.entries
    ++ JuliaLean.ReduceCov.ReducedimRows.entries
    ++ JuliaLean.IntFuncsCov.entries
    ++ JuliaLean.DictsCov.entries
    ++ JuliaLean.StringsCovA.entries
    ++ JuliaLean.StringsCovB.entries
    ++ JuliaLean.ConcurrencyCov.entries

    ++ JuliaLean.MiscCov.entries
    ++ JuliaLean.AbstractArraySpecs.entries
    ++ JuliaLean.Proofs.base.abstractarray.entries
    ++ JuliaLean.Proofs.base.abstractarray.LegacyRetired.entriesFill
    ++ JuliaLean.Proofs.base.abstractarray.LegacyRetired.entriesRepair
    ++ JuliaLean.Proofs.base.abstractarray.LegacyRetired.entriesSameRank
    ++ JuliaLean.Proofs.base.abstractarray.LegacyRetired.entries
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entriesBatch6
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entriesBatch7
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entriesZero
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entriesBatch8
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entries
    ++ JuliaLean.Proofs.base.abstractarray.entriesModels2Group6
    ++ JuliaLean.Proofs.base.abstractarray.entriesModels1Group3
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entriesBatch4
    ++ JuliaLean.Proofs.base.abstractarray.entriesModels1Group2
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entriesBatch3
    ++ JuliaLean.Proofs.base.abstractarray.entriesModels1Group1
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entriesBatch2
    ++ JuliaLean.Proofs.base.abstractarray.entriesModels1Group4
    ++ JuliaLean.Proofs.base.abstractarray.Completion20261105.entriesBatch5
    ++ JuliaLean.Proofs.base.abstractarraymath.entries
    ++ JuliaLean.Proofs.base.abstractdict.entries
    ++ JuliaLean.Proofs.base.abstractset.entries
    ++ JuliaLean.Proofs.base.anyall.entries
    
    
    
    ++ JuliaLean.Proofs.base.arraymath.entries
    ++ JuliaLean.Proofs.base.bitarray.entries
    ++ JuliaLean.Proofs.base.bitarray.dispatch.entries
    ++ JuliaLean.Proofs.base.bitset.entries
    ++ JuliaLean.Proofs.base.bool.entries
    ++ JuliaLean.Proofs.base.broadcast.entries
    ++ JuliaLean.Proofs.base.broadcast.entriesModels2Group5
    ++ JuliaLean.Proofs.base.broadcast.entriesModels1Group11
    ++ JuliaLean.Proofs.base.broadcast.entriesModels1Group12
    ++ JuliaLean.Proofs.base.channels.entries
    ++ JuliaLean.Proofs.base.char.entries
    ++ JuliaLean.Proofs.base.fastmath.entries
    ++ JuliaLean.Proofs.base.checked.entries
    ++ JuliaLean.Proofs.base.cmem.entries
    ++ JuliaLean.Proofs.base.complex.entries
    ++ JuliaLean.Proofs.base.complex.entriesModels2Group9
    ++ JuliaLean.Proofs.base.complex.entriesPreparedGroup19
    ++ JuliaLean.Proofs.base.deprecated.entries
    ++ JuliaLean.Proofs.base.dict.entries
    ++ JuliaLean.Proofs.base.div.entries
    ++ JuliaLean.Proofs.base.error.entries
    ++ JuliaLean.Proofs.base.errorshow.entries
    ++ JuliaLean.Proofs.base.arrayshow.entries
    ++ JuliaLean.Proofs.base.errorshow.entriesModels2Group17
    ++ JuliaLean.Proofs.base.essentials.entries
    ++ JuliaLean.Proofs.base.essentials.entriesModels2Group19
    ++ JuliaLean.Proofs.base.essentials.entriesModels1Group18
    ++ JuliaLean.Proofs.base.file.entries
    ++ JuliaLean.Proofs.base.float.entries
    ++ JuliaLean.Proofs.base.floatfuncs.entries
    ++ JuliaLean.Proofs.base.generator.entries
    ++ JuliaLean.Proofs.base.genericmemory.entries
    ++ JuliaLean.Proofs.base.gmp.entries
    ++ JuliaLean.Proofs.base.gmp.entriesLegacyRetired
  ++ JuliaLean.Proofs.base.gmp.entriesModels2Group2
    ++ JuliaLean.Proofs.base.hamt.entries
    ++ JuliaLean.Proofs.base.hashing.entries
    ++ JuliaLean.Proofs.base.iddict.entries
    ++ JuliaLean.Proofs.base.idset.entries
    ++ JuliaLean.Proofs.base.indices.entries
    ++ JuliaLean.Proofs.base.int.entries
    ++ JuliaLean.Proofs.base.intfuncs.entries
    ++ JuliaLean.Proofs.base.intfuncs.entriesModels2Group16
    ++ JuliaLean.Proofs.base.iobuffer.entries
    ++ JuliaLean.Proofs.base.iterators.entries
    ++ JuliaLean.Proofs.base.iterators.ZipSharedStatefulCompletion.entries
    ++ JuliaLean.Proofs.base.complex.CisImaginaryAxis.entries
    ++ JuliaLean.Proofs.base.indices.HeterogeneousCartesianPromotion.entries
    ++ JuliaLean.Proofs.base.intfuncs.lcm_zero_absorption.entries
    ++ JuliaLean.Proofs.base.parse.complex_imaginary_minimum.entries
    ++ JuliaLean.Proofs.base.permuteddimsarray.CopyLinearLength.entries
    ++ JuliaLean.Proofs.base.linked_list.entries
    ++ JuliaLean.Proofs.base.logging.logging.entries
    ++ JuliaLean.Proofs.base.loading.ValueContracts.entries
    ++ JuliaLean.Proofs.base.loading.entries
  ++ JuliaLean.Proofs.base.loading.entriesModels2Group4
    ++ JuliaLean.Proofs.base.loading.entriesModels1Group10
    ++ JuliaLean.Proofs.base.loading.entriesModels1Group10Coverage
    ++ JuliaLean.Proofs.base.loading.entriesModels1Group9
    ++ JuliaLean.Proofs.base.loading.SourceCoverage.entries
    ++ JuliaLean.Proofs.base.math.entries
    ++ JuliaLean.Proofs.base.missing.entries
    ++ JuliaLean.Proofs.base.mpfr.entries
    ++ JuliaLean.Proofs.base.mpfr.entriesLegacyRetired
    ++ JuliaLean.Proofs.base.mpfr.entriesLegacyAggregates
    ++ JuliaLean.Proofs.base.multidimensional.entries
  ++ JuliaLean.Proofs.base.multidimensional.entriesModels2Group3
    ++ JuliaLean.Proofs.base.multidimensional.entriesModels1Group5
    ++ JuliaLean.Proofs.base.multidimensional.entriesModels1Group6
    ++ JuliaLean.Proofs.base.multinverses.entries
    ++ JuliaLean.Proofs.base.namedtuple.entries
    ++ JuliaLean.Proofs.base.ntuple.entries
    ++ JuliaLean.Proofs.base.number.entries
    ++ JuliaLean.Proofs.base.operators.entries
    ++ JuliaLean.Proofs.base.operators.entriesModels2Group15
    ++ JuliaLean.Proofs.base.ordering.entries
    ++ JuliaLean.Proofs.base.osinfo.entries
    ++ JuliaLean.Proofs.base.pair.entries
    ++ JuliaLean.Proofs.base.path.entries
    ++ JuliaLean.Proofs.base.permuteddimsarray.entries
    ++ JuliaLean.Proofs.base.pointer.entries
    ++ JuliaLean.Proofs.base.precompilation.entries
    ++ JuliaLean.Proofs.base.precompilation.entriesRetired
    ++ JuliaLean.Proofs.base.precompilation.entriesMore
    ++ JuliaLean.Proofs.base.cpuid.entries
    ++ JuliaLean.Proofs.base.promotion.entries
    ++ JuliaLean.Proofs.base.range.entries
    ++ JuliaLean.Proofs.base.range.entriesModels2Group20
    ++ JuliaLean.Proofs.base.range.entriesModels1Group7
    ++ JuliaLean.Proofs.base.range.entriesModels1Group8
    ++ JuliaLean.Proofs.base.rational.entries
    ++ JuliaLean.Proofs.base.rational.entriesModels2Group10
    ++ JuliaLean.Proofs.base.rational.entriesModels1Group20
    ++ JuliaLean.Proofs.base.reduce.entries
    ++ JuliaLean.Proofs.base.reduce.entriesModels2Group7
    ++ JuliaLean.Proofs.base.reducedim.entries
    ++ JuliaLean.Proofs.base.refpointer.entries
    ++ JuliaLean.Proofs.base.refvalue.entries
    ++ JuliaLean.Proofs.base.reinterpretarray.entries
    ++ JuliaLean.Proofs.base.reinterpretarray.entriesModels2Group12
    ++ JuliaLean.Proofs.base.reshapedarray.entries
    ++ JuliaLean.Proofs.base.rounding.entries
    ++ JuliaLean.Proofs.base.set.entries
    ++ JuliaLean.Proofs.base.show.entries
    ++ JuliaLean.Proofs.base.slicearray.entries
    ++ JuliaLean.Proofs.base.some.entries
    ++ JuliaLean.Proofs.base.sort.entries
    ++ JuliaLean.Proofs.base.stat.entries
    ++ JuliaLean.Proofs.base.strings.annotated.entries
    ++ JuliaLean.Proofs.base.strings.annotated_io.entries
    ++ JuliaLean.Proofs.base.strings.basic.entries
    ++ JuliaLean.Proofs.base.strings.cstring.entries
    ++ JuliaLean.Proofs.base.strings.io.entries
    ++ JuliaLean.Proofs.base.strings.lazy.entries
    ++ JuliaLean.Proofs.base.strings.search.entries
    ++ JuliaLean.Proofs.base.strings.string.entries
    ++ JuliaLean.Proofs.base.strings.substring.entries
    ++ JuliaLean.Proofs.base.strings.unicode.entries
    ++ JuliaLean.Proofs.base.strings.util.entries
    ++ JuliaLean.Proofs.base.subarray.entries
    ++ JuliaLean.Proofs.base.subarray.LegacyRetired.entries
    ++ JuliaLean.Proofs.base.subarray.entriesModels2Group14
    ++ JuliaLean.Proofs.base.subarray.entriesModels1Group17
    ++ JuliaLean.Proofs.base.toml.parser.entries
    ++ JuliaLean.Proofs.base.terminfo.entries
    ++ JuliaLean.Proofs.base.tuple.entries
    ++ JuliaLean.Proofs.base.twiceprecision.entries
    ++ JuliaLean.Proofs.base.uuid.entries
    ++ JuliaLean.Proofs.base.views.entries
    ++ JuliaLean.Proofs.base.special.exp.entries
    ++ JuliaLean.Proofs.base.special.cbrt.entries
    ++ JuliaLean.Proofs.base.floatfuncsArchive20261101.entries
    ++ JuliaLean.Proofs.base.floatfuncsInt64Archive20261101.entries
    ++ JuliaLean.Proofs.base.secretbuffer.entries
    ++ JuliaLean.Proofs.base.util.entries
    ++ JuliaLean.Proofs.base.special.trig.entries
    ++ JuliaLean.Proofs.base.special.hyperbolic.entries
    ++ JuliaLean.Proofs.base.special.rem2pi.entries
    ++ JuliaLean.Proofs.base.combinatorics.entries
    ++ JuliaLean.Proofs.base.binaryplatforms.entries
    ++ JuliaLean.Proofs.base.boot.entries
    ++ JuliaLean.Proofs.base.boot.entriesModels2Group1
    ++ JuliaLean.Proofs.base.docs.Docs.entries
    ++ JuliaLean.Proofs.base.docs.basedocs.entries
    ++ JuliaLean.Proofs.base.docs.bindings.entries
    ++ JuliaLean.Proofs.base.docs.core.entries
    ++ JuliaLean.Proofs.base.docs.utils.entries
    ++ JuliaLean.Proofs.base.linking.entries
    ++ JuliaLean.Proofs.base.parse.entries
    ++ JuliaLean.Proofs.base.syntax.entries
    ++ JuliaLean.Proofs.base.toml.printer.entries

    ++ JuliaLean.Proofs.base.iostream.entriesModels2Group18
end JuliaLean.Registry
