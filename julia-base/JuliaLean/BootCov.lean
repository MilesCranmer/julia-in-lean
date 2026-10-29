import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.BootCov.IntConvProofs
import JuliaLean.BootCov.ObjectsProofs
import JuliaLean.BootCov.TypesProofs
import JuliaLean.BootCov.ArraysProofs
import JuliaLean.BootCov.MacrosProofs
import JuliaLean.BootCov.MiscProofs
import JuliaLean.BootCov.DefaultCtorsProofs

/-!
Coverage of `base/boot.jl` and `base/essentials.jl` (Julia master `bbfa0ce4150`).
-/

namespace JuliaLean.BootCov

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "bootcov-boot-int-ctors", juliaFile := "base/boot.jl"
    juliaFns := ["toInt8..toUInt128 (110 methods)", "Int8(::BuiltinInts)..UInt128(::BuiltinInts)"]
    statement := "Every Core integer constructor T(x) for a built-in integer or Bool x returns x itself when x is representable in T and otherwise throws InexactError for T."
    source := "convert docstring (base/essentials.jl:428-430); base/boot.jl:1071-1193", status := .proven
    prop := ``IntConv.CtorExact, thm := some ``IntConv.ctorExact },
  { id := "bootcov-boot-int-helpers", juliaFile := "base/boot.jl"
    juliaFns := ["is_top_bit_set", "throw_inexacterror", "check_sign_bit", "checked_trunc_sint", "checked_trunc_uint"]
    statement := "is_top_bit_set tests the signed sign bit; check_sign_bit returns x unless its top bit is set, then throws InexactError for To; the checked truncations succeed exactly when the value survives the round trip through the narrower type."
    source := "base/boot.jl:1037-1069", status := .proven
    prop := ``IntConv.HelperSemantics, thm := some ``IntConv.helperSemantics },
  { id := "bootcov-signbit-func-name", juliaFile := "base/boot.jl"
    juliaFns := ["check_sign_bit", "toUInt16(::Int8)", "toUInt32(::Int8/::Int16)", "toUInt64(::Int8/::Int16/::Int32)", "toUInt128(::Int8..::Int64)"]
    statement := "A failing integer conversion that does not narrow the bit width reports convert, not trunc, as the failing function."
    source := "base/boot.jl:1049-1051 (check_sign_bit comment: if x is signed then bitsizeof(x) === bitsizeof(To))", status := .refuted
    prop := ``IntConv.WideningErrorNamesConvert, thm := some ``IntConv.wideningErrorNamesConvert_refuted
    issue := "none found (queries: InexactError trunc UInt16 Int8, check_sign_bit, InexactError trunc convert widening, InexactError: trunc negative unsigned, InexactError trunc message misleading, InexactError says trunc, bitsizeof check_top_bit, InexactError convert vs trunc)"
    notes := "UInt16(Int8(-1)) throws InexactError(:trunc, UInt16, -1) while UInt16(Int16(-1)) throws InexactError(:convert, ...). Same on 1.13.2." },
  { id := "bootcov-boot-signed-unsigned", juliaFile := "base/boot.jl"
    juliaFns := ["Signed(::UInt8..::UInt128)", "Unsigned(::Int8..::Int128)"]
    statement := "Signed(x) and Unsigned(x) of a fixed-width integer convert exactly to the same-width signed or unsigned type."
    source := "base/boot.jl:1206-1215; convert docstring", status := .proven
    prop := ``IntConv.SignedUnsignedExact, thm := some ``IntConv.signedUnsignedExact },
  { id := "bootcov-boot-ptr-casts", juliaFile := "base/boot.jl"
    juliaFns := ["(::Type{T})(x::T)", "Int(::Ptr)", "UInt(::Ptr)", "Ptr{T}(x)", "AddrSpace(::UInt8)", "Signed(::Float/Bool)", "Unsigned(::Float/Bool)", "Integer(::Integer)", "Integer(::Float)"]
    statement := "Pointer casts are bit casts that round-trip addresses, Ptr{T}() is null, T(x::T) and Integer(x::Integer) return x, and the float/Bool forms of Signed, Unsigned and Integer delegate to Int(x) or UInt(x)."
    source := "base/boot.jl:1195-1221", status := .proven
    prop := ``IntConv.PtrCastsRoundTrip, thm := some ``IntConv.ptrCastsRoundTrip },
  { id := "bootcov-boot-exceptions", juliaFile := "base/boot.jl"
    juliaFns := ["ErrorException", "BoundsError (3 methods)", "DivideError", "OutOfMemoryError", "ReadOnlyMemoryError", "SegmentationFault", "StackOverflowError", "UndefRefError", "UndefVarError (2)", "ConcurrencyViolationError", "MissingCodeError", "InterruptException", "DomainError (2)", "TypeError (2)", "InexactError", "OverflowError", "ArgumentError", "UndefKeywordError", "MethodError (2)", "AssertionError (2)", "FieldError", "LoadError", "InitError", "ABIOverride", "PrecompilableError", "TrimFailure", "PossiblyAmbiguous", "UndefInitializer", "CoreSTDOUT", "CoreSTDERR", "TypeNameError"]
    statement := "Exception and singleton constructors store their arguments in field order, leave omitted fields undefined, convert typed fields (MethodError when impossible) and fill the documented defaults."
    source := "base/boot.jl:470-606, 696, 757, 974-977, 1307", status := .proven
    prop := ``Objects.ExceptionFields, thm := some ``Objects.exceptionFields },
  { id := "bootcov-boot-wrappers", juliaFile := "base/boot.jl"
    juliaFns := ["String(::String)", "Nothing()", "EvalInto", "Box (2)", "WeakRef (2)", "Tuple{}()", "VecElement{T}", "VecElement", "Const", "_PartialStruct", "InterConditional", "InterMustAlias", "PartialOpaque", "PartialTask", "GeneratedFunctionStub", "Pair(a, b)", "MacroSource"]
    statement := "Wrapper and lattice-element constructors store their arguments, Box() leaves its field undefined, WeakRef() refers to nothing, and VecElement(x) is VecElement{typeof(x)}(x)."
    source := "base/boot.jl:611-696, 1012, 1269, 1335", status := .proven
    prop := ``Objects.WrapperFields, thm := some ``Objects.wrapperFields },
  { id := "bootcov-boot-ir-nodes", juliaFile := "base/boot.jl"
    juliaFns := ["GotoNode", "NewvarNode", "QuoteNode", "SSAValue", "Argument", "ReturnNode (2)", "GotoIfNot", "EnterNode (3)", "LineNumberNode (2)", "DebugInfo (2)", "SlotNumber", "PhiNode", "PiNode", "PhiCNode", "UpsilonNode (2)", "MethodMatch", "LineInfoNode"]
    statement := "IR node constructors store their arguments; LineNumberNode(l, f) turns a String file into a Symbol and rejects other non-Symbol files; EnterNode(old, d) keeps old.scope exactly when it is defined."
    source := "base/boot.jl:699-736, 1292-1293", status := .proven
    prop := ``Objects.IRNodeFields, thm := some ``Objects.irNodeFields },
  { id := "bootcov-boot-named-tuples", juliaFile := "base/boot.jl"
    juliaFns := ["NamedTuple()", "NamedTuple{names}(::Tuple)", "NamedTuple{names,T}(::T)"]
    statement := "NamedTuple constructors pair the names with the arguments in order; NamedTuple{names}(args) throws exactly when the counts differ; NamedTuple() is empty."
    source := "base/boot.jl:1022-1030", status := .proven
    prop := ``Objects.NamedTupleCtors, thm := some ``Objects.namedTupleCtors },
  { id := "bootcov-boot-handles", juliaFile := "base/boot.jl"
    juliaFns := ["getptls", "include", "eval", "(::EvalInto)(e)", "CodeInstance", "GlobalRef", "Module"]
    statement := "The runtime-handle constructors and Core.eval/include pass their arguments to the runtime in order; Module() defaults to :anonymous with standard imports and default names."
    source := "base/boot.jl:617-626, 740-751", status := .proven
    prop := ``Objects.HandleCtors, thm := some ``Objects.handleCtors },
  { id := "bootcov-boot-typeof", juliaFile := "base/boot.jl"
    juliaFns := ["(::typeof(Typeof))(x)", "(::typeof(TypeEqOf))(x)", "_typeof_captured_variable"]
    statement := "Typeof(x) is Type{x} for types with free typevars, TypeEgal{x} for other types and typeof(x) otherwise; TypeEqOf(x) is Type{x} for every type; _typeof_captured_variable picks typeof for types with free typevars."
    source := "base/boot.jl:296-319, 387", status := .proven
    prop := ``Types.TypeofKinds, thm := some ``Types.typeofKinds
    notes := "1.13.2 Typeof returns Type{x} for all types and has no TypeEqOf." },
  { id := "bootcov-boot-typevar-unionall", juliaFile := "base/boot.jl"
    juliaFns := ["TypeVar (3 methods)", "UnionAll(v, t)"]
    statement := "TypeVar builds a fresh typevar with default bounds Union{} and Any, rejecting non-Symbol names and non-type bounds; UnionAll(v, t) requires a TypeVar, returns v.ub for t === v, returns t when v does not occur in it, and otherwise wraps t."
    source := "base/boot.jl:370-373; src/jltypes.c:1054-1099, 2216-2229", status := .proven
    prop := ``Types.TypeVarUnionAll, thm := some ``Types.typeVarUnionAll },
  { id := "bootcov-boot-typename", juliaFile := "base/boot.jl"
    juliaFns := ["typename (4 methods)"]
    statement := "typename sees through where, returns the shared name of a Union whose members agree, and throws TypeNameError for other values including Union{}."
    source := "base/boot.jl:1310-1318", status := .proven
    prop := ``Types.TypenameBehaviour, thm := some ``Types.typenameBehaviour },
  { id := "bootcov-boot-typeapp", juliaFile := "base/boot.jl"
    juliaFns := ["TypeApp", "_contains_typeapp", "apply_type_or_typeapp", "resolve_typegroup"]
    statement := "apply_type_or_typeapp builds the left-nested TypeApp chain when the head is a TypeVar or TypeApp or a parameter contains a TypeApp, and calls apply_type otherwise; an empty typegroup resolves to ()."
    source := "base/boot.jl:403-467", status := .proven
    prop := ``Types.TypeAppBehaviour, thm := some ``Types.typeAppBehaviour
    notes := "Master only; absent in 1.13.2." },
  { id := "bootcov-boot-operators", juliaFile := "base/boot.jl"
    juliaFns := [">:", "!=="]
    statement := "(>:)(a, b) is b <: a and (!==)(a, b) is !(a === b)."
    source := "base/boot.jl:1322-1323", status := .proven
    prop := ``Types.BootOperators, thm := some ``Types.bootOperators },
  { id := "bootcov-boot-memory", juliaFile := "base/boot.jl"
    juliaFns := ["GenericMemory{kind,T,addrspace}(undef, m)", "GenericMemory{...}(undef, (m,))", "GenericMemory{...}()"]
    statement := "Memory(undef, m) allocates exactly m undefined slots when 0 <= m <= the runtime limit and throws ArgumentError otherwise; the tuple and empty forms agree."
    source := "base/boot.jl:762-765; src/genericmemory.c:55-73", status := .proven
    prop := ``Arrays.MemoryCtorCorrect, thm := some ``Arrays.memoryCtorCorrect },
  { id := "bootcov-boot-memoryref", juliaFile := "base/boot.jl"
    juliaFns := ["memoryref (3 methods)", "GenericMemoryRef (3 methods)"]
    statement := "memoryref(mem, i) refers to slot i exactly when 1 <= i <= length(mem) and throws BoundsError otherwise; memoryref(ref, i) shifts by i - 1, negative shifts included, throwing BoundsError exactly when the target leaves the memory."
    source := "memoryref docstring (base/genericmemory.jl); base/boot.jl:768-773; src/builtins.c (jl_f_memoryrefnew)", status := .proven
    prop := ``Arrays.MemoryrefCorrect, thm := some ``Arrays.memoryrefCorrect },
  { id := "bootcov-boot-checked-dims", juliaFile := "base/boot.jl"
    juliaFns := ["_checked_mul_dims (4 methods)", "checked_dims (3 methods)"]
    statement := "checked_dims with two or more dimensions throws ArgumentError or returns the exact product of dimensions that are all nonnegative and below typemax(Int); checked_dims() is 1 and checked_dims(m) is m."
    source := "invariant; base/boot.jl:781-818", status := .proven
    prop := ``Arrays.CheckedDimsSound, thm := some ``Arrays.checkedDimsSound
    notes := "Rejecting a typemax(Int) dimension even when the product fits is reported as reinterpretarrays-reshape-typemax-dim." },
  { id := "bootcov-boot-array-ctors", juliaFile := "base/boot.jl"
    juliaFns := ["Array{T,1/2/3/N}(undef, dims...)", "Array{T,N}(undef, ::NTuple)", "Array{T}(undef, ...)", "Vector{T}()", "new_as_memoryref"]
    statement := "Every Array(undef, dims...) constructor throws ArgumentError or builds an array with exactly the requested dimensions whose memory length is the product of the dimensions."
    source := "Array docstring (base/docs/basedocs.jl); base/boot.jl:779-847", status := .proven
    prop := ``Arrays.ArrayCtorShape, thm := some ``Arrays.arrayCtorShape },
  { id := "bootcov-boot-array-conversions", juliaFile := "base/boot.jl"
    juliaFns := ["(Array{T,N} where T)(::AbstractArray)", "Array(::AbstractArray)", "Array{T}(::AbstractArray)", "AbstractArray{T}(::AbstractArray)"]
    statement := "The converting Array constructors call the full constructor with the element type fixed by the signature and the source dimensionality."
    source := "base/boot.jl:849-854", status := .proven
    prop := ``Arrays.ArrayConversions, thm := some ``Arrays.arrayConversions },
  { id := "bootcov-boot-symbol", juliaFile := "base/boot.jl"
    juliaFns := ["_Symbol", "Symbol(::String)", "Symbol(::Vector{UInt8})", "Symbol(::Symbol)"]
    statement := "Symbol(s) builds the symbol with exactly the bytes of s (for a vector, those visible through its reference), throws ArgumentError for a NUL byte, and Symbol(::Symbol) is the identity."
    source := "Symbol docstring; base/boot.jl:858-873; src/symbol.c:114-119", status := .proven
    prop := ``Arrays.SymbolCtors, thm := some ``Arrays.symbolCtors },
  { id := "bootcov-boot-markers", juliaFile := "base/boot.jl"
    juliaFns := ["@nospecialize(x)", "Expr(args...)", "@latestworld", "@inline", "@noinline", "@nospecializeinfer", "@_boundscheck"]
    statement := "The Core marker macros expand to their meta expressions, and Expr(head, args...) requires a Symbol head and at least one argument."
    source := "base/boot.jl:324-367", status := .proven
    prop := ``Macros.CoreMarkerMacros, thm := some ``Macros.coreMarkerMacros },
  { id := "bootcov-boot-effect-metas", juliaFile := "base/boot.jl"
    juliaFns := ["_is_internal", "@_total_meta", "@_foldable_meta"]
    statement := "Core.@_total_meta and Core.@_foldable_meta expand to their purity expression only inside Core and to false elsewhere; the :total form asserts exactly the @assume_effects :total effects."
    source := "base/boot.jl:331-361; base/expr.jl:1019-1030", status := .proven
    prop := ``Macros.CoreEffectMetas, thm := some ``Macros.coreEffectMetas
    notes := "Core.@_foldable_meta also asserts notaskstate and inaccessiblememonly; see bootcov-foldable-meta-effects." },
  { id := "bootcov-boot-doc", juliaFile := "base/boot.jl"
    juliaFns := ["@doc", "@__doc__", "isbasicdoc", "firstarg", "iscallexpr (2)", "ignoredoc", "atdoc!"]
    statement := "The Core doc helpers drop basic and call documentation targets and keep other expressions, @doc passes :escape results through and wraps others in a hygienic scope, and atdoc! installs the hook."
    source := "base/boot.jl:940-960", status := .proven
    prop := ``Macros.DocHelpers, thm := some ``Macros.docHelpers },
  { id := "bootcov-boot-printing", juliaFile := "base/boot.jl"
    juliaFns := ["CoreSTDOUT", "CoreSTDERR", "io_pointer (2)", "unsafe_write (2)", "write (2)", "show (2)", "print (5)", "println (3)"]
    statement := "Core printing appends each argument's bytes in order to the chosen stream (strings and chars verbatim, others via jl_static_show), println adds a newline, write returns the byte count, and the other stream is untouched."
    source := "base/boot.jl:970-1006", status := .proven
    prop := ``Misc.CorePrinting, thm := some ``Misc.corePrinting },
  { id := "bootcov-boot-identity", juliaFile := "base/boot.jl"
    juliaFns := ["convert(::Type{Any}, x)", "convert(::Type{T}, x::T)", "cconvert(::Type{T}, x)", "unsafe_convert(::Type{T}, x::T)", "Union{}(a...)", "kwcall(kw, ::Type{Union{}}, a...)"]
    statement := "The Core identity conversions return their argument, Core.cconvert is convert, and constructing Union{} throws ArgumentError."
    source := "base/boot.jl:377-399", status := .proven
    prop := ``Misc.IdentityConversionsBoot, thm := some ``Misc.identityConversionsBoot },
  { id := "bootcov-boot-hooks", juliaFile := "base/boot.jl"
    juliaFns := ["struct_name_shim", "_setparser!", "_setlowerer!", "_set_toplevel_eval!", "_hasmethod"]
    statement := "struct_name_shim returns the type under construction exactly for x === mod; each _set...! installs and returns its hook only; _hasmethod is true exactly when lookup finds a method."
    source := "base/boot.jl:1227-1281", status := .proven
    prop := ``Misc.CoreHooks, thm := some ``Misc.coreHooks }
]

end JuliaLean.BootCov
