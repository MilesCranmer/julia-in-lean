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
    prop := ``Misc.CoreHooks, thm := some ``Misc.coreHooks },
  { id := "bootcov-foldable-meta-effects", juliaFile := "base/essentials.jl"
    juliaFns := ["@_total_meta", "@_foldable_meta", "@_terminates_locally_meta", "@_terminates_globally_meta", "@_terminates_globally_notaskstate_meta", "@_terminates_globally_noub_meta", "@_effect_free_terminates_locally_meta", "@_nothrow_noub_meta", "@_nothrow_meta", "@_noub_meta", "@_notaskstate_meta", "@_noub_if_noinbounds_meta", "_is_internal", "_nameof", "nameof(::Module)"]
    statement := "Each Base effect macro asserts exactly the effects of the @assume_effects settings its comment names (up to terminates_globally implying terminates_locally), inside Base or Compiler, and expands to false elsewhere."
    source := "base/essentials.jl:195-374 (comments: can be used in place of @assume_effects ...); base/expr.jl:995-1031", status := .refuted
    prop := ``Macros.BaseEffectMetasMatchAssume, thm := some ``Macros.baseEffectMetasMatchAssume_refuted
    issue := "none found (queries: _foldable_meta, foldable_meta notaskstate, _foldable_meta inaccessiblememonly, assume_effects foldable bootstrapping meta)"
    notes := "@_foldable_meta also sets notaskstate and inaccessiblememonly; every other macro matches. Same on 1.13.2." },
  { id := "bootcov-ess-markers", juliaFile := "base/essentials.jl"
    juliaFns := ["@_gc_preserve_begin", "@_gc_preserve_end", "@nospecialize", "@specialize", "@isdefined", "@_propagate_inbounds_meta", "@_nospecializeinfer_meta", "@eval (2)", "esc", "@boundscheck", "@inbounds", "@label (3)", "@goto", "@__LINE__", "@world"]
    statement := "The Base marker macros expand to the documented expressions; @nospecialize x=v uses :kw only for one argument; @label rejects _; labelled loops wrap their body in a name#cont block; @world accepts a symbol, GlobalRef or a.b."
    source := "docstrings of @nospecialize, @boundscheck, @inbounds, @label, @goto, @eval; base/essentials.jl:46-186, 377-382, 488-501, 893-977, 1020-1060, 1568-1570, 1646-1660", status := .proven
    prop := ``Macros.BaseMarkerMacros, thm := some ``Macros.baseMarkerMacros
    notes := "1.13.2 has only @label(name) without the _ check or loop forms." },
  { id := "bootcov-ess-checkbounds", juliaFile := "base/essentials.jl"
    juliaFns := ["checkbounds(::Type{Bool}, ::Union{Array,Memory}, ::Int)"]
    statement := "checkbounds(Bool, A, i) is true exactly when i is in 1:length(A), for every Int index."
    source := "checkbounds docstring; base/essentials.jl:385-388", status := .proven
    prop := ``Arrays.CheckboundsBoolCorrect, thm := some ``Arrays.checkboundsBoolCorrect },
  { id := "bootcov-ess-access", juliaFile := "base/essentials.jl"
    juliaFns := ["checkbounds(A, I...)", "default_access_order (4)", "getindex(::GenericMemory, ::Int)", "getindex(::GenericMemoryRef)", "getindex(::Array, ::Int)", "setindex! (4)", "size(::Array)", "size(::GenericMemory)", "length(::Vector)"]
    statement := "A[i] throws BoundsError outside 1:length(A) and otherwise reads the slot; A[i] = x then A[i] returns x; setindex! returns its array and the MemoryRef{T} method converts first; atomic memory uses :monotonic; size and length read the stored dimensions."
    source := "getindex/setindex! docstrings; base/essentials.jl:12-14, 389-406, 1063-1082, 1286", status := .proven
    prop := ``Arrays.AccessSemantics, thm := some ``Arrays.accessSemantics },
  { id := "bootcov-ess-svec", juliaFile := "base/essentials.jl"
    juliaFns := ["getindex(::SimpleVector, ::Int)", "length", "firstindex", "lastindex", "iterate", "eltype", "keys", "isempty", "axes (2)", "==", "map", "getindex(::SimpleVector, ::AbstractArray)", "unsafe_convert(::Type{Ptr{Any}}, ::SimpleVector)"]
    statement := "SimpleVector indexing throws BoundsError outside 1:length(v); iterate yields every element in order; firstindex, lastindex, keys, axes, isempty and eltype describe 1:length(v); map and v[I] act elementwise; equal svecs compare equal and different lengths compare unequal."
    source := "iteration/indexing interface (manual); base/essentials.jl:1086-1111", status := .proven
    prop := ``Arrays.SvecSemantics, thm := some ``Arrays.svecSemantics },
  { id := "bootcov-svec-isassigned-undef", juliaFile := "base/essentials.jl"
    juliaFns := ["isassigned(::SimpleVector, ::Int)"]
    statement := "isassigned(v, i) is true exactly when i is in bounds and slot i holds a value."
    source := "isassigned docstring, base/essentials.jl:1113-1117", status := .refuted
    prop := ``Arrays.SvecIsassignedCorrect, thm := some ``Arrays.svecIsassignedCorrect_refuted
    issue := "none found (queries: isassigned SimpleVector, isassigned svec undef, jl_alloc_svec isassigned)"
    notes := "A jl_alloc_svec vector with NULL slots reports isassigned(v, 1) == true. Same on 1.13.2." },
  { id := "bootcov-ess-unwrap-rewrap", juliaFile := "base/essentials.jl"
    juliaFns := ["unwrap_unionall", "rewrap_unionall", "rewrap_unionall(::TypeofVararg, u)"]
    statement := "unwrap_unionall strips every where, rewrap_unionall(unwrap_unionall(u), u) rebuilds every UnionAll Julia can construct, and rewrap is the identity for non-UnionAll u."
    source := "invariant; base/essentials.jl:544-571", status := .proven
    prop := ``Types.UnwrapRewrap, thm := some ``Types.unwrapRewrap },
  { id := "bootcov-ess-rename", juliaFile := "base/essentials.jl"
    juliaFns := ["rename_unionall", "widen_diagonal"]
    statement := "rename_unionall returns non-UnionAll types unchanged and renames the variable of D{T} where T to a fresh TypeVar with the same name and bounds; widen_diagonal returns the runtime result."
    source := "base/essentials.jl:574-587", status := .proven
    prop := ``Types.RenameUnionall, thm := some ``Types.renameUnionall_spec },
  { id := "bootcov-ess-vararg", juliaFile := "base/essentials.jl"
    juliaFns := ["isvarargtype", "isvatuple", "unwrapva", "unconstrain_vararg_length"]
    statement := "isvarargtype recognises Vararg, unwrapva returns the element type (Any if absent), unconstrain_vararg_length drops the length, isvatuple holds exactly for DataTypes whose last parameter is a Vararg."
    source := "base/essentials.jl:589-613", status := .proven
    prop := ``Types.VarargHelpers, thm := some ``Types.varargHelpers },
  { id := "bootcov-ess-min-ninit", juliaFile := "base/essentials.jl"
    juliaFns := ["datatype_min_ninitialized"]
    statement := "datatype_min_ninitialized counts the fields every instance defines: 0 for abstract types, tuple length adjusted for a trailing Vararg, the number of NamedTuple names, and field count minus possibly-undefined fields otherwise."
    source := "base/essentials.jl:615-646", status := .proven
    prop := ``Types.MinNinitialized, thm := some ``Types.minNinitialized },
  { id := "bootcov-ess-has-typevar", juliaFile := "base/essentials.jl"
    juliaFns := ["has_typevar"]
    statement := "has_typevar finds a typevar in itself and in type parameters and does not see a variable bound by its own UnionAll."
    source := "base/essentials.jl:1288", status := .proven
    prop := ``Types.HasTypevarBehaviour, thm := some ``Types.hasTypevarBehaviour },
  { id := "bootcov-ess-tuples", juliaFile := "base/essentials.jl"
    juliaFns := ["argtail", "tail (2)", "_tuple_error", "convert(::Type{T}, ::NTuple{N,Any})", "cvt1"]
    statement := "tail drops the first element and throws ArgumentError on (); tuple convert throws MethodError when impossible, returns x when every element already has its field type, keeps the length and converts the others elementwise."
    source := "tail docstring (base/essentials.jl:525-540), convert docstring; base/essentials.jl:521-667", status := .proven
    prop := ``Misc.TupleHelpers, thm := some ``Misc.tupleHelpers },
  { id := "bootcov-ess-identity", juliaFile := "base/essentials.jl"
    juliaFns := ["convert(::Type{Union{}}, _...)", "convert(::Type{Type}, ::Type)", "convert(::Type{String}, ::String)", "convert(::Type{T}, ::T) where T<:Tuple", "cconvert (3)", "unsafe_convert (5)"]
    statement := "The Base identity conversions return their argument, cconvert converts only non-T values and defers pointers, unsafe_convert keeps addresses, and conversion to Union{} throws ArgumentError."
    source := "cconvert/unsafe_convert docstrings; base/essentials.jl:471-480, 652, 737-746", status := .proven
    prop := ``Misc.IdentityConversionsBase, thm := some ``Misc.identityConversionsBase },
  { id := "bootcov-ess-barriers", juliaFile := "base/essentials.jl"
    juliaFns := ["blackbox", "inferencebarrier", "values"]
    statement := "blackbox, inferencebarrier and values return their argument unchanged."
    source := "values docstring (base/essentials.jl:1231-1252); compilerbarrier semantics", status := .proven
    prop := ``Misc.Barriers, thm := some ``Misc.barriers },
  { id := "bootcov-ess-throw-boundserror", juliaFile := "base/essentials.jl"
    juliaFns := ["throw_boundserror(A)", "throw_boundserror(A, I)", "throw_boundserror(A, i1, i2, I...)", "_throw_boundserror_indices(A)", "_throw_boundserror_indices(A, i1, I...)"]
    statement := "Every throw_boundserror form throws BoundsError(A, indices), the splatting forms with the indices as a tuple."
    source := "BoundsError docstring; base/essentials.jl:15-19", status := .proven
    prop := ``Misc.ThrowBoundserrorForms, thm := some ``Misc.throwBoundserrorForms },
  { id := "bootcov-ess-globalref-eq", juliaFile := "base/essentials.jl"
    juliaFns := ["==(::GlobalRef, ::GlobalRef)"]
    statement := "Two GlobalRefs are == exactly when their modules and names are identical."
    source := "invariant (base/essentials.jl:23)", status := .proven
    prop := ``Misc.GlobalRefEq, thm := some ``Misc.globalRefEq_spec },
  { id := "bootcov-ess-oftype", juliaFile := "base/essentials.jl"
    juliaFns := ["oftype"]
    statement := "oftype(x, y) returns y when y isa typeof(x), and otherwise convert(typeof(x), y), which must itself have type typeof(x)."
    source := "oftype docstring (base/essentials.jl:700-717)", status := .proven
    prop := ``Misc.OftypeSpec, thm := some ``Misc.oftypeSpec },
  { id := "bootcov-ess-signed-unsigned", juliaFile := "base/essentials.jl"
    juliaFns := ["unsigned(::Int)", "signed(::UInt)"]
    statement := "unsigned(::Int) and signed(::UInt) reinterpret the bit pattern, invert each other, and unsigned(x) == x mod 2^64."
    source := "signed and unsigned docstrings (base/int.jl); base/essentials.jl:720-721", status := .proven
    prop := ``Misc.SignedUnsignedInt, thm := some ``Misc.signedUnsignedInt },
  { id := "bootcov-ess-reinterpret", juliaFile := "base/essentials.jl"
    juliaFns := ["reinterpret(::Type{Out}, x)"]
    statement := "reinterpret(Out, x) is bitcast(Out, x) for primitive Out and x and _reinterpret(Out, x) otherwise."
    source := "reinterpret docstring (base/essentials.jl:753-786)", status := .proven
    prop := ``Misc.ReinterpretSpec, thm := some ``Misc.reinterpretSpec },
  { id := "bootcov-ess-sizeof", juliaFile := "base/essentials.jl"
    juliaFns := ["sizeof(x)"]
    statement := "sizeof(x) returns Core.sizeof(x)."
    source := "sizeof docstring (base/essentials.jl:796-840)", status := .proven
    prop := ``Misc.SizeofSpec, thm := some ``Misc.sizeofSpec },
  { id := "bootcov-ess-ifelse", juliaFile := "base/essentials.jl"
    juliaFns := ["ifelse"]
    statement := "ifelse(true, x, y) is x and ifelse(false, x, y) is y."
    source := "ifelse docstring (base/essentials.jl:870-883)", status := .proven
    prop := ``Misc.IfelseSpec, thm := some ``Misc.ifelseSpec },
  { id := "bootcov-ess-isempty", juliaFile := "base/essentials.jl"
    juliaFns := ["isempty(itr)"]
    statement := "isempty(itr) is isdone(itr) when that is a Bool and otherwise iterate(itr) === nothing."
    source := "isempty docstring (base/essentials.jl:1203-1224)", status := .proven
    prop := ``Misc.IsemptySpec, thm := some ``Misc.isemptySpec },
  { id := "bootcov-ess-int-add-sub", juliaFile := "base/essentials.jl"
    juliaFns := ["+(::Int, ::Int)", "-(::Int, ::Int)"]
    statement := "The bootstrap Int + and - return the exact result reduced modulo 2^64 into Int."
    source := "integer arithmetic wraps (manual, Integers and Floating-Point Numbers: Overflow behavior)", status := .proven
    prop := ``Misc.IntAddSub, thm := some ``Misc.intAddSub },
  { id := "bootcov-ess-not", juliaFile := "base/essentials.jl"
    juliaFns := ["!(::Bool)"]
    statement := "!x is the Boolean negation of x."
    source := "! docstring (base/essentials.jl:1260-1283)", status := .proven
    prop := ``Misc.NotBool, thm := some ``Misc.notBool_spec },
  { id := "bootcov-ess-ismissing", juliaFile := "base/essentials.jl"
    juliaFns := ["ismissing"]
    statement := "ismissing(x) is true exactly when x is missing."
    source := "ismissing docstring (base/essentials.jl:1525-1531)", status := .proven
    prop := ``Misc.IsmissingSpec, thm := some ``Misc.ismissingSpec },
  { id := "bootcov-ess-isdone", juliaFile := "base/essentials.jl"
    juliaFns := ["isdone(_, _...)"]
    statement := "The fallback isdone returns missing."
    source := "isdone docstring (base/essentials.jl:1573-1590)", status := .proven
    prop := ``Misc.IsdoneDefault, thm := some ``Misc.isdoneDefault_spec },
  { id := "bootcov-ess-isiterable", juliaFile := "base/essentials.jl"
    juliaFns := ["isiterable"]
    statement := "isiterable(T) is true exactly when iterate has a method for Tuple{T}."
    source := "isiterable docstring (base/essentials.jl:1602-1607)", status := .proven
    prop := ``Misc.IsiterableSpec, thm := some ``Misc.isiterableSpec },
  { id := "bootcov-ess-resolve-in-world", juliaFile := "base/essentials.jl"
    juliaFns := ["_resolve_in_world"]
    statement := "_resolve_in_world throws InexactError for a negative world and otherwise reads gr in world UInt(world)."
    source := "invariant (base/essentials.jl:1662-1663)", status := .proven
    prop := ``Misc.ResolveInWorld, thm := some ``Misc.resolveInWorld_spec },
  { id := "bootcov-ess-pairs-colon-val", juliaFile := "base/essentials.jl"
    juliaFns := ["Pairs{K,V,I,A}", "Pairs{K,V}", "Pairs{K}", "Pairs", "pairs(::Type{NamedTuple})", "Colon()", "show(::IO, ::Colon)", "Val{x}()", "Val(x)"]
    statement := "Pairs converts only mistyped arguments and chooses its parameters from the arguments; pairs(NamedTuple) has Symbol keys; Colon() is a singleton printed as Colon(); Val(x) is Val{x}()."
    source := "Colon and Val docstrings; base/essentials.jl:505-513, 1160-1193", status := .proven
    prop := ``Misc.PairsAndColon, thm := some ``Misc.pairsAndColon },
  { id := "bootcov-ess-fieldtypes-constrain", juliaFile := "base/essentials.jl"
    juliaFns := ["_fieldtypes_constrain_typevars"]
    statement := "_fieldtypes_constrain_typevars(tvars, fts) is true exactly when every type variable occurs in some field type or in the upper bound of an inner type variable before one that shadows it."
    source := "comment at base/essentials.jl:1290-1291; lines 1292-1329", status := .proven
    prop := ``DefaultCtors.FieldtypesConstrainSpec, thm := some ``DefaultCtors.fieldtypesConstrainSpec },
  { id := "bootcov-ess-defaultctor-typeinfo", juliaFile := "base/essentials.jl"
    juliaFns := ["_defaultctor_typeinfo"]
    statement := "_defaultctor_typeinfo(ty) returns unwrap_unionall(ty), the UnionAll variables outermost first, and the field types, and throws TypeError when the unwrapped type is not a DataType."
    source := "comment at base/essentials.jl:1331; lines 1332-1350", status := .proven
    prop := ``DefaultCtors.TypeinfoSpec, thm := some ``DefaultCtors.typeinfoSpec },
  { id := "bootcov-ess-defaultctors", juliaFile := "base/essentials.jl"
    juliaFns := ["_defaultctors"]
    statement := "_defaultctors defines the outer constructor T(x::FT1, ...) = new{...}(x, ...) exactly when the type parameters are constrained, skips the inner constructor only for a non-parametric type whose fields are all Any, and otherwise defines the inner constructor taking Any arguments that converts each non-Any field with isa(x, fieldtype(T, i)) ? x : convert(fieldtype(T, i), x); every generated array slot is assigned."
    source := "manual, Constructors (default constructors); comments at base/essentials.jl:1352-1354, 1387-1388, 1428, 1440-1441; lines 1355-1504", status := .proven
    prop := ``DefaultCtors.DefaultctorsSpec, thm := some ``DefaultCtors.defaultctorsSpec },
  { id := "bootcov-ess-length-abstract", juliaFile := "base/essentials.jl"
    juliaFns := ["length(::AbstractArray)"]
    statement := "length(t::AbstractArray) = prod(size(t)) is the product of the dimensions reduced into Int, so it is the number of elements whenever that product is at most typemax(Int)."
    source := "length docstring (base/abstractarray.jl:305-308); base/essentials.jl:13", status := .proven
    prop := ``DefaultCtors.LengthAbstractSpec, thm := some ``DefaultCtors.lengthAbstractSpec }
]

end JuliaLean.BootCov
