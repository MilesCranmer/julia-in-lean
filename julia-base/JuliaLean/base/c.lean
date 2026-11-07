import JuliaLean.Core
import JuliaLean.base.pointer
import JuliaLean.base.expr

/-!
# Model of `base/c.jl`

The `CFunction` model retains its typed pointer and callable payload. Runtime calls use typed
interfaces, platform-selected C ABI aliases are functions of the C runtime probes, and macro
expansion remains visible below.
-/

namespace JuliaLean.base.c

open JuliaLean
open JuliaLean.base.pointer

/--
Julia source: base/c.jl:15-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct CFunction <: Ref{Cvoid}
    ptr::Ptr{Cvoid}
    f::Any
    _1::Ptr{Cvoid}
    _2::Ptr{Cvoid}
    let constructor = false end
end
```
-/
structure CFunction (F : Type) where
  ptr : Ptr Unit
  f : F
  root1 : Ptr Unit
  root2 : Ptr Unit

/--
Julia source: base/c.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Cvoid}}, cf::CFunction) = cf.ptr
```
-/
def unsafeConvertCFunction {F : Type} (cf : CFunction F) : Ptr Unit := cf.ptr

-- UNTRANSLATED: `@cfunction` constructs compiler expression nodes at macro-expansion time.
/-
Julia source: base/c.jl:24-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @cfunction(callable, ReturnType, (ArgumentTypes...,)) -> Ptr{Cvoid}
    @cfunction(\$callable, ReturnType, (ArgumentTypes...,)) -> CFunction

Generate a C-callable function pointer from the Julia function `callable`
for the given type signature.
To pass the return value to a `ccall`, use the argument type `Ptr{Cvoid}` in the signature.

Note that the argument type tuple must be a literal tuple, and not a tuple-valued variable or expression
(although it can include a splat expression). And that these arguments will be evaluated in global scope
during compile-time (not deferred until runtime).
Adding a '\\\$' in front of the function argument changes this to instead create a runtime closure
over the local variable `callable` (this is not supported on all architectures).

See [manual section on ccall and cfunction usage](@ref Calling-C-and-Fortran-Code).

# Examples
```julia-repl
julia> function foo(x::Int, y::Int)
           return x + y
       end

julia> @cfunction(foo, Int, (Int, Int))
Ptr{Cvoid} @0x000000001b82fcd0
```
"""
macro cfunction(f, rt, at)
    if !(isa(at, Expr) && at.head === :tuple)
        throw(ArgumentError("@cfunction argument types must be a literal tuple"))
    end
    at.head = :call
    pushfirst!(at.args, GlobalRef(Core, :svec))
    if isa(f, Expr) && f.head === :$
        fptr = f.args[1]
        typ = CFunction
    else
        fptr = QuoteNode(f)
        typ = Ptr{Cvoid}
    end
    cfun = Expr(:cfunction, typ, fptr, rt, at, QuoteNode(:ccall))
    return esc(cfun)
end
````
-/

/--
Julia source: base/c.jl:67-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if ccall(:jl_is_char_signed, Ref{Bool}, ())
    const Cchar = Int8
else
    const Cchar = UInt8
end
"""
    Cchar

Equivalent to the native `char` c-type.
"""
Cchar
```
-/
def ccharType (charIsSigned : Bool) : IntTy :=
  if charIsSigned then .i8 else .u8

/-- Platform-selected `Clong`, `Culong`, and `Cwchar_t` type aliases. -/
structure CLongTypes where
  clong : IntTy
  culong : IntTy
  cwchar : IntTy
  deriving Repr, DecidableEq

/--
Julia source: base/c.jl:79-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The ccall here is equivalent to Sys.iswindows(), but that's not defined yet
if ccall(:jl_get_UNAME, Any, ()) === :NT
    const Clong = Int32
    const Culong = UInt32
    const Cwchar_t = UInt16
else
    const Clong = Int
    const Culong = UInt
    const Cwchar_t = Int32
end

"""
    Clong

Equivalent to the native `signed long` c-type.
"""
Clong

"""
    Culong

Equivalent to the native `unsigned long` c-type.
"""
Culong

"""
    Cwchar_t

Equivalent to the native `wchar_t` c-type ([`Int32`](@ref)).
"""
Cwchar_t
```
-/
def cLongTypes (isWindows : Bool) : CLongTypes :=
  if isWindows then ⟨.i32, .u32, .u16⟩ else ⟨.i64, .u64, .i32⟩

/--
Julia source: base/c.jl:111-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if ccall(:jl_get_UNAME, Any, ()) !== :NT
    const sizeof_mode_t = ccall(:jl_sizeof_mode_t, Cint, ())
    if sizeof_mode_t == 2
        const Cmode_t = Int16
    elseif sizeof_mode_t == 4
        const Cmode_t = Int32
    elseif sizeof_mode_t == 8
        const Cmode_t = Int64
    else
        error("invalid sizeof mode_t")
    end
end
```
-/
def cModeType {ε : Type} (isWindows : Bool) (sizeofModeT : JInt .i32)
    (raiseError : String → Except ε (Option IntTy)) : Except ε (Option IntTy) :=
  if isWindows then .ok none
  else if sizeofModeT.val == 2 then .ok (some .i16)
  else if sizeofModeT.val == 4 then .ok (some .i32)
  else if sizeofModeT.val == 8 then .ok (some .i64)
  else raiseError "invalid sizeof mode_t"

/--
Julia source: base/c.jl:131-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sigatomic_begin() = ccall(:jl_sigatomic_begin, Cvoid, ())
sigatomic_end() = ccall(:jl_sigatomic_end, Cvoid, ())
```
-/
def sigatomicBegin (runtimeBegin : Unit → Unit) : Unit := runtimeBegin ()
def sigatomicEnd (runtimeEnd : Unit → Unit) : Unit := runtimeEnd ()

/--
Julia source: base/c.jl:134-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    disable_sigint(f::Function)

Disable Ctrl-C handler during execution of a function on the current task,
for calling external code that may call julia code that is not interrupt safe.
Intended to be called using `do` block syntax as follows:

    disable_sigint() do
        # interrupt-unsafe code
        ...
    end

External functions that do not call julia code or julia runtime
automatically disable sigint during their execution.
"""
function disable_sigint(f::Function)
    depwarn("`disable_sigint` no longer defers Ctrl-C: SIGINT is delivered as a " *
            "cancellation of the current ^C scope and observed at cancellation " *
            "points regardless of the sigatomic region this establishes. Shield " *
            "a region from cancellation by scoping " *
            "`Base.CANCEL_TOKEN => nothing` over it instead.", :disable_sigint)
    sigatomic_begin()
    res = f()
    # Exception unwind sigatomic automatically
    sigatomic_end()
    res
end
```
-/
def disableSigint {α ε : Type}
    (depwarn : String → String → Except ε Unit)
    (sigatomicBegin sigatomicEnd : Unit → Except ε Unit)
    (f : Unit → Except ε α) : Except ε α := do
  depwarn
    "`disable_sigint` no longer defers Ctrl-C: SIGINT is delivered as a cancellation of the current ^C scope and observed at cancellation points regardless of the sigatomic region this establishes. Shield a region from cancellation by scoping `Base.CANCEL_TOKEN => nothing` over it instead."
    "disable_sigint"
  sigatomicBegin ()
  let result ← f ()
  sigatomicEnd ()
  pure result

/--
Julia source: base/c.jl:162-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    reenable_sigint(f::Function)

Re-enable Ctrl-C handler during execution of a function.
Temporarily reverses the effect of [`disable_sigint`](@ref).
"""
function reenable_sigint(f::Function)
    sigatomic_end()
    res = f()
    # Exception unwind sigatomic automatically
    sigatomic_begin()
    res
end
```
-/
def reenableSigint {α ε : Type}
    (sigatomicBegin sigatomicEnd : Unit → Except ε Unit)
    (f : Unit → Except ε α) : Except ε α := do
  sigatomicEnd ()
  let result ← f ()
  sigatomicBegin ()
  pure result

/--
Julia source: base/c.jl:176-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    exit_on_sigint(on::Bool)

Set `exit_on_sigint` flag of the julia runtime.  If `false`, Ctrl-C
(SIGINT) cancels the current ^C episode's cancellation scope and is
observed at cancellation points as a [`Base.CancellationRequest`](@ref),
which is capturable in a `try` block.
This is the default behavior in REPL, any code run via `-e` and `-E`
and in Julia script run with `-i` option.

If `true`, Ctrl-C terminates the process directly.  Running code
upon such event requires [`atexit`](@ref).  This is the default
behavior in Julia script run without `-i` option.

!!! compat "Julia 1.5"
    Function `exit_on_sigint` requires at least Julia 1.5.
"""
function exit_on_sigint(on::Bool)
    ccall(:jl_exit_on_sigint, Cvoid, (Cint,), on)
end
```
-/
def exitOnSigint (setExitFlag : Bool → Unit) (on : Bool) : Unit := setExitFlag on

/--
Julia source: base/c.jl:197-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ccallable(name::Union{Nothing, String}, rt::Type, sigt::Type)
    ccall(:jl_extern_c, Cvoid, (Any, Any, Any), name, rt, sigt)
end
```
-/
def registerCcallable {RT ST : Type}
    (jlExternC : Option String → RT → ST → Unit)
    (name : Option String) (returnType : RT) (signatureType : ST) : Unit :=
  jlExternC name returnType signatureType

-- UNTRANSLATED: These macro methods create and lower syntax trees for Julia's compiler.
/-
Julia source: base/c.jl:201-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expand_ccallable(name, rt, def)
    if isa(def,Expr) && (def.head === :(=) || def.head === :function)
        sig = def.args[1]
        if sig.head === :(::)
            if rt === nothing
                rt = sig.args[2]
            end
            sig = sig.args[1]
        end
        if rt === nothing
            error("@ccallable requires a return type")
        end
        if sig.head === :call
            f = sig.args[1]
            if isa(f,Expr) && f.head === :(::)
                f = f.args[end]
            else
                f = :(typeof($f))
            end
            at = Any[let a = sig.args[i]
                    if isa(a,Expr) && a.head === :(::)
                        a.args[end]
                    else
                        :Any
                    end
                end for i in 2:length(sig.args)]
            return quote
                @__doc__ $(esc(def))
                _ccallable($name, $(esc(rt)), $(Expr(:curly, :Tuple, esc(f), map!(esc, at, at)...)))
            end
        end
    end
    error("expected method definition in @ccallable")
end

"""
    @ccallable ["name"] function f(...)::RetType ... end

Make the annotated function be callable from C using its name. This can, for example,
be used to expose functionality as a C API when creating a custom Julia sysimage.

If the first argument is a string, it is used as the external name of the function.
"""
macro ccallable(def)
    expand_ccallable(nothing, nothing, def)
end
macro ccallable(rt, def)
    if rt isa String
        expand_ccallable(rt, nothing, def)
    else
        expand_ccallable(nothing, rt, def)
    end
end

# @ccall implementation
```
-/

-- UNTRANSLATED: `@ccall` argument parsing and lowering construct compiler expression trees.
/-
Julia source: base/c.jl:254-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# @ccall implementation
"""
    ccall_macro_parse(expression)

`ccall_macro_parse` is an implementation detail of `@ccall`.

It takes an expression like `:(printf("%d"::Cstring, value::Cuint)::Cvoid)`
returns: a tuple of `(function_name, return_type, arg_types, args)`

The above input outputs this:

    (:printf, :Cvoid, [:Cstring, :Cuint], ["%d", :value])
"""
function ccall_macro_parse(exprs)
    gc_safe = false
    cancel = nothing
    expr = nothing
    if exprs isa Expr
        expr = exprs
    else
        # leading `name = value` options, then the call expression
        i = 1
        while i < length(exprs) && isexpr(exprs[i], :(=))
            opt = exprs[i]::Expr
            name = opt.args[1]
            value = opt.args[2]
            if name === :gc_safe
                if value === true
                    gc_safe = true
                elseif value === false
                    gc_safe = false
                else
                    throw(ArgumentError("gc_safe must be true or false"))
                end
            elseif name === :cancel_handler
                if !(isexpr(value, :tuple) && length(value.args) == 2)
                    throw(ArgumentError("cancel_handler must be a `(handler, state)` tuple"))
                end
                cancel = (value.args[1], value.args[2])
            else
                throw(ArgumentError("@ccall options are `gc_safe = <bool>` and `cancel_handler = (handler, state)`"))
            end
            i += 1
        end
        if i != length(exprs)
            throw(ArgumentError("@ccall needs a function signature with a return type"))
        end
        expr = exprs[i]
    end

    # setup and check for errors
    if !isexpr(expr, :(::))
        throw(ArgumentError("@ccall needs a function signature with a return type"))
    end
    rettype = expr.args[2]

    call = expr.args[1]
    if !isexpr(call, :call)
        throw(ArgumentError("@ccall has to take a function call"))
    end

    # get the function symbols
    func = let f = call.args[1]
        if isexpr(f, :.)
            Expr(:tuple, f.args[2], f.args[1])
        elseif isexpr(f, :$)
            func = f.args[1]
            if isa(func, String) || (isa(func, QuoteNode) && !isa(func.value, Ptr)) || isa(func, Tuple) || isexpr(func, :tuple)
                throw(ArgumentError("interpolated value should be a variable or expression, not a literal name or tuple"))
            end
            func
        elseif f isa Symbol
            Expr(:tuple, QuoteNode(f))
        else
            throw(ArgumentError("@ccall function name must be a symbol, a `.` node (e.g. `libc.printf`) or an interpolated function pointer (with `\$`)"))
        end
    end

    # detect varargs
    varargs = nothing
    argstart = 2
    callargs = call.args
    if length(callargs) >= 2 && isexpr(callargs[2], :parameters)
        argstart = 3
        varargs = callargs[2].args
    end

    # collect args and types
    args = []
    types = []

    function pusharg!(arg)
        if !isexpr(arg, :(::))
            throw(ArgumentError("args in @ccall need type annotations. '$arg' doesn't have one."))
        end
        push!(args, arg.args[1])
        push!(types, arg.args[2])
    end

    for i in argstart:length(callargs)
        pusharg!(callargs[i])
    end
    # add any varargs if necessary
    nreq = 0
    if varargs !== nothing
        if length(args) == 0
            throw(ArgumentError("C ABI prohibits vararg without one required argument"))
        end
        nreq = length(args)
        for a in varargs
            pusharg!(a)
        end
    end
    return func, rettype, types, args, gc_safe, cancel, nreq
end


function ccall_macro_lower(convention, func, rettype, types, args, gc_safe, cancel, nreq)
    have_cancel = cancel !== nothing
    # `Base.@assume_effects :reset_safe @ccall ...` arrives as the
    # CCALL_EFFECT_RESET_SAFE bit above the standard effects overrides in
    # the `@ccall_effects` word (see `@assume_effects` in expr.jl): split it
    # back out into its dedicated calling-convention slot here.
    reset_safe = false
    if convention isa Tuple
        cc_sym, effects = convention
        reset_safe = (effects & CCALL_EFFECT_RESET_SAFE) != 0x0000
        base_cconv = (cc_sym, effects & ~CCALL_EFFECT_RESET_SAFE, gc_safe)
    else
        base_cconv = (convention, UInt16(0), gc_safe)
    end
    if !have_cancel
        cconv = reset_safe ? Expr(:cconv, (base_cconv..., false, true), nreq) :
                             Expr(:cconv, base_cconv, nreq)
        return Expr(:call, :ccall, esc(func), cconv, esc(rettype),
                     Expr(:tuple, map!(esc, types, types)...), map!(esc, args, args)...)
    end
    # Our internal ABI for cancellation handlers is f(func, state, args...). Codegen
    # inlines the establishment of the handler and the ultimate call to `f` has the
    # ordinary ABI without the extra arguments.
    fex, sex = cancel
    nreq > 0 && (nreq += 2)
    cconv = Expr(:cconv, reset_safe ? (base_cconv..., true, true) : (base_cconv..., true), nreq)
    return Expr(:call, :ccall, esc(func), cconv, esc(rettype),
                Expr(:tuple, :(Ptr{Cvoid}), :(Ptr{Cvoid}), map!(esc, types, types)...),
                esc(fex), esc(sex), map!(esc, args, args)...)
end
```
-/

-- UNTRANSLATED: `@ccall` macros emit compiler-only foreign-call syntax.
/-
Julia source: base/c.jl:403-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @ccall library.function_name(argvalue1::argtype1, ...)::returntype
    @ccall function_name(argvalue1::argtype1, ...)::returntype
    @ccall \$function_pointer(argvalue1::argtype1, ...)::returntype

Call a function in a C-exported shared library, specified by
`library.function_name`, where `library` is a string constant or
literal. The library may be omitted, in which case the `function_name`
is resolved in the current process. Alternatively, `@ccall` may
also be used to call a function pointer `\$function_pointer`, such as
one returned by `dlsym`.

Each `argvalue` to `@ccall` is converted to the corresponding
`argtype`, by automatic insertion of calls to `unsafe_convert(argtype,
cconvert(argtype, argvalue))`. (See also the documentation for
[`unsafe_convert`](@ref Base.unsafe_convert) and [`cconvert`](@ref
Base.cconvert) for further details.) In most cases, this simply
results in a call to `convert(argtype, argvalue)`.


# Examples

    @ccall strlen(s::Cstring)::Csize_t

This calls the C standard library function:

    size_t strlen(char *)

with a Julia variable named `s`. See also `ccall`.

Varargs are supported with the following convention:

    @ccall printf("%s = %d"::Cstring ; "foo"::Cstring, foo::Cint)::Cint

The semicolon is used to separate required arguments (of which there
must be at least one) from variadic arguments.

Example using an external library:

    # C signature of g_uri_escape_string:
    # char *g_uri_escape_string(const char *unescaped, const char *reserved_chars_allowed, gboolean allow_utf8);

    const glib = "libglib-2.0"
    @ccall glib.g_uri_escape_string(my_uri::Cstring, ":/"::Cstring, true::Cint)::Cstring

The string literal could also be used directly before the function
name, if desired `"libglib-2.0".g_uri_escape_string(...`

It's possible to declare the ccall as `gc_safe` by using the `gc_safe = true` option:

    @ccall gc_safe=true strlen(s::Cstring)::Csize_t

This allows the garbage collector to run concurrently with the ccall, which can be useful whenever
the `ccall` may block outside of julia.

!!! warning
    This option should be used with caution, as it can lead to undefined behavior if the ccall
    calls back into the julia runtime. (`@cfunction`/`@ccallable` are safe however)

!!! compat "Julia 1.12"
    The `gc_safe` argument requires Julia 1.12 or higher.

# Extended help

## Cancellation

### Semantics of reset_safe annotation

When annotated `@assume_effects :reset_safe`, e.g.:

    Base.@assume_effects :reset_safe @ccall libgmp.__gmpz_mul(x::mpz_t, a::mpz_t, b::mpz_t)::Cvoid

The compiler has license to extend an earlier reset region through the entire
execution of the called C function. In particular, as a result, the function
may be abandoned at any point (and reset to the appropriate cancellation
point).

This imposes strict requirements on the foreign code. In particular, it is
generally unsafe to call into most C standard library functions (the Julia
runtime will handle properly protecting the symbol lookup itself), modify
memory other than allocated since the most recent cancellation point (or
which the cancellation will explicitly clean up). Additionally, any memory
access to memory that may be read after a reset must be annotated
`volatile`. This list of conditions is meant to be illustrative, not
exhaustive and may be extended with additional warnings in the future.

Co-operating foreign code may use the Julia C API to temporarily protect
regions from reset, although this API is not yet stable and requires source
modifications.

!!! compat "Julia 1.14"
    The `:reset_safe` effect requires Julia 1.14 or higher.

## Cancellation handlers

Because the `:reset_safe` effect imposes such strict requirements, another
option is provided to allow for cancellation of cooperating foreign code.
In particular, a long-running foreign call can be made cancellable with the
`cancel_handler = (handler, state)` option:

    @ccall cancel_handler=(CANCEL_FPTR, ref) lib.solve(ref::Ptr{Cvoid})::Cvoid

`handler` is a C-callable function pointer `void (*)(void *state, uint8_t
sev)` (typically from [`@cfunction`](@ref)). If the cancellation token
source (`Base.CancellationTokenSource`) bound to the calling task is
cancelled while the call runs, the runtime invokes `handler(state, sev)` *on
the thread executing the call*, like a signal handler: at an arbitrary point
of the foreign code, on the same stack, resuming the interrupted call when
the handler returns (`sev` is the request state of the cancelled source).
The handler performs the library-specific work to make the foreign call
return early - typically setting a flag or calling the library's own
cancellation entry point.

Both `CANCEL_FPTR` and `ref` are handled as ordinary ccall arguments (both
of C type `Ptr{Cvoid}`), including for purposes of rooting. Note that since
`CANCEL_FPTR` runs as a signal handler, it must be async-signal-safe in the
ordinary sense, although unlike `:reset_safe`, no requirements are imposed
on the called function itself.

A function may be annotated with both `:reset_safe` and `cancel_handler`,
in which case the cancel_handler takes precedence. However, in such a
situation, the compiler will attempt to preserve the reset region into the
ccall and it may be read by the cancel_handler (which can then perform some
library specific cleanup before performing the reset as usual). However,
this is not required nor assumed. A cancel handler could instead cause the
function to return early with an error code. Note however, that there is no
automatic cancellation point implied by the `cancel_handler` attribute. It
is the responsibility of the user to set an appropriate cancellation point
either before or after (possibly conditional on an appropriate error return
code) the ccall.

!!! compat "Julia 1.14"
    The `cancel_handler` option requires Julia 1.14 or higher.
"""
macro ccall(exprs...)
    return ccall_macro_lower((:ccall), ccall_macro_parse(exprs)...)
end

macro ccall_effects(effects::UInt16, exprs...)
    return ccall_macro_lower((:ccall, effects), ccall_macro_parse(exprs)...)
end
```
-/

end JuliaLean.base.c

namespace JuliaLean.MiscCov.CInterface

open JuliaLean.MiscCov
/-- `ex.args[k]` (one-based) of an `Expr`: `FieldError` for a non-`Expr`, `BoundsError`
past the end. -/
def arg (ex : Ex) (k : Nat) : M Ex :=
  match ex with
  | .expr _ as => match as[k - 1]? with
    | some a => .ok a
    | none => .error .boundsError
  | _ => .error .fieldError

/-- `ex.args` of an `Expr` (`FieldError` otherwise). -/
def argsOf (ex : Ex) : M (List Ex) :=
  match ex with
  | .expr _ as => .ok as
  | _ => .error .fieldError

/-- `ex.head`. -/
def headOf (ex : Ex) : M String :=
  match ex with
  | .expr h _ => .ok h
  | _ => .error .fieldError

/-! ## `CFunction` and `@cfunction`, `base/c.jl:13-65` -/

/-- A `CFunction` object: its `ptr` field and the closure. -/
structure CFunction where
  ptr : Nat
  f : String

/-- `unsafe_convert(::Type{Ptr{Cvoid}}, cf::CFunction) = cf.ptr`, `base/c.jl:22`. -/
def unsafeConvert (cf : CFunction) : Nat := cf.ptr

/-- `@cfunction(f, rt, at)`, `base/c.jl:50-65`. -/
def cfunction (f rt ats : Ex) : M Ex :=
  if !ats.isExpr "tuple" then .error (.argumentError "@cfunction argument types must be a literal tuple")
  else do
    let as ← argsOf ats
    let ats' := Ex.expr "call" (.gref "Core" "svec" :: as)
    let (fptr, typ) ← (if f.isExpr "$" then do pure (← arg f 1, Ex.gref "Base" "CFunction")
      else pure (.qn f, Ex.val "Ptr{Cvoid}") : M (Ex × Ex))
    .ok (Ex.esc (.expr "cfunction" [typ, fptr, rt, ats', .qn (.sym "ccall")]))


/-! ## SIGINT regions, `base/c.jl:131-195` -/

/-- Runtime state: `defer_signal`, whether SIGINT exits, and the warnings written. -/
structure RT where
  defer : Nat
  exitOnSigint : Bool
  warnings : List String
  deriving DecidableEq, Repr

/-- `sigatomic_begin()`, `base/c.jl:131`. -/
def sigatomicBegin (r : RT) : RT := { r with defer := r.defer + 1 }

/-- `sigatomic_end()`, `base/c.jl:132`: an error outside a sigatomic region. -/
def sigatomicEnd (r : RT) : M RT :=
  if r.defer = 0 then .error (.errorException "sigatomic_end called in non-sigatomic region")
  else .ok { r with defer := r.defer - 1 }

/-- A Julia function of no arguments run on the runtime state. -/
abbrev Thunk (α : Type) := RT → M (α × RT)

/-- `depwarn(msg, :disable_sigint)` when deprecation warnings are enabled. -/
def disableSigintMsg : String := "`disable_sigint` no longer defers Ctrl-C"

/-- The state after `depwarn(msg, :disable_sigint)`: the warning is written when
deprecation warnings are enabled (`warn`). -/
def warnState (warn : Bool) (r : RT) : RT :=
  if warn then { r with warnings := r.warnings ++ [disableSigintMsg] } else r

/-- `disable_sigint(f)`, `base/c.jl:149-160`. -/
def disableSigint {α : Type} (warn : Bool) (f : Thunk α) (r : RT) : M (α × RT) := do
  let (res, r) ← f (sigatomicBegin (warnState warn r))
  let r ← sigatomicEnd r
  pure (res, r)

/-- `reenable_sigint(f)`, `base/c.jl:168-174`. -/
def reenableSigint {α : Type} (f : Thunk α) (r : RT) : M (α × RT) := do
  let r ← sigatomicEnd r
  let (res, r) ← f r
  let r := sigatomicBegin r
  pure (res, r)

/-- `exit_on_sigint(on)`, `base/c.jl:193-195`. -/
def exitOnSigint (on : Bool) (r : RT) : RT := { r with exitOnSigint := on }


/-! ## `@ccallable`, `base/c.jl:197-253` -/

/-- `_ccallable(name, rt, sigt)`, `base/c.jl:197-199`: `jl_extern_c` registers the
method; the model records the registration. -/
def ccallableRt (regs : List (Option String × String × String)) (name : Option String) (rt sigt : String) :
    List (Option String × String × String) := regs ++ [(name, rt, sigt)]

/-- The argument type of one signature argument (`base/c.jl:218-224`). -/
def argType (a : Ex) : Ex :=
  match a with
  | .expr "::" as => as.getLast?.getD .nothing
  | _ => .sym "Any"

/-- `name` as the expression interpolated into the quote: a string or `nothing`. -/
def nameEx : Option String → Ex
  | some s => .str s
  | none => .nothing

/-- `expand_ccallable(name, rt, def)`, `base/c.jl:201-234`. `rt = none` is `nothing`. -/
def expandCcallable (name : Option String) (rt : Option Ex) (def_ : Ex) : M Ex := do
  match def_ with
  | .expr h (sig0 :: _) =>
    if h = "=" ∨ h = "function" then do
      let sh ← headOf sig0
      let (rt, sig) ← (if sh = "::" then do
          let rt ← (match rt with | some r => pure (some r) | none => do pure (some (← arg sig0 2)))
          let sig ← arg sig0 1
          pure (rt, sig)
        else pure (rt, sig0) : M (Option Ex × Ex))
      match rt with
      | none => .error (.errorException "@ccallable requires a return type")
      | some rt =>
        let sh ← headOf sig
        if sh = "call" then do
          let sargs ← argsOf sig
          let f0 ← arg sig 1
          let f := match f0 with
            | .expr "::" fs => fs.getLast?.getD .nothing
            | _ => .expr "call" [.sym "typeof", f0]
          let ats := sargs.drop 1 |>.map argType
          pure (.expr "block" [.expr "macrocall" [.sym "@__doc__", .lnn, Ex.esc def_],
            .expr "call" [.sym "_ccallable", nameEx name, Ex.esc rt,
              .expr "curly" (.sym "Tuple" :: Ex.esc f :: ats.map Ex.esc)]])
        else .error (.errorException "expected method definition in @ccallable")
    else .error (.errorException "expected method definition in @ccallable")
  | _ => .error (.errorException "expected method definition in @ccallable")

/-- `@ccallable def`, `base/c.jl:244-246`. -/
def ccallable1 (def_ : Ex) : M Ex := expandCcallable none none def_

/-- `@ccallable rt def`, `base/c.jl:247-253`: a string first argument is the C name. -/
def ccallable2 (rt def_ : Ex) : M Ex :=
  match rt with
  | .str s => expandCcallable (some s) none def_
  | _ => expandCcallable none (some rt) def_

/-! ## `@ccall`, `base/c.jl:268-543` -/

/-- The macro arguments: one `Expr` or the tuple `exprs...`. -/
inductive CArgs where
  | single (e : Ex)
  | many (es : List Ex)

/-- The result `(func, rettype, types, args, gc_safe, cancel, nreq)`. -/
structure Parsed where
  func : Ex
  rettype : Ex
  types : List Ex
  args : List Ex
  gcSafe : Bool
  cancel : Option (Ex × Ex)
  nreq : Nat

/-- `pusharg!(arg)`, `base/c.jl:346-352`. -/
def pusharg (acc : List Ex × List Ex) (a : Ex) : M (List Ex × List Ex) :=
  if !a.isExpr "::" then .error (.argumentError "args in @ccall need type annotations.")
  else do
    let x ← arg a 1
    let t ← arg a 2
    pure (acc.1 ++ [x], acc.2 ++ [t])

def pushargs (acc : List Ex × List Ex) : List Ex → M (List Ex × List Ex)
  | [] => .ok acc
  | a :: as => do pushargs (← pusharg acc a) as

/-- The option loop `while i < length(exprs) && isexpr(exprs[i], :(=))`,
`base/c.jl:276-297`: the remaining expressions, `gc_safe`, `cancel`. -/
def options : List Ex → Bool → Option (Ex × Ex) → M (List Ex × Bool × Option (Ex × Ex))
  | [], g, c => .ok ([], g, c)
  | [e], g, c => .ok ([e], g, c)
  | e :: e' :: es, g, c =>
    match e with
    | .expr "=" oargs => do
      let name ← arg e 1
      let value ← arg e 2
      let _ := oargs
      if name.isSym "gc_safe" then
        match value with
        | .bool true => options (e' :: es) true c
        | .bool false => options (e' :: es) false c
        | _ => .error (.argumentError "gc_safe must be true or false")
      else if name.isSym "cancel_handler" then
        match value with
        | .expr "tuple" [a, b] => options (e' :: es) g (some (a, b))
        | _ => .error (.argumentError "cancel_handler must be a `(handler, state)` tuple")
      else .error (.argumentError "@ccall options are `gc_safe = <bool>` and `cancel_handler = (handler, state)`")
    | _ => .ok (e :: e' :: es, g, c)

/-- `isa(func, String) || (isa(func, QuoteNode) && !isa(func.value, Ptr)) ||
isa(func, Tuple) || isexpr(func, :tuple)`; a `Ptr` or `Tuple` runtime value is
`.val "Ptr"` / `.val "Tuple"`. -/
def literalName (func : Ex) : Bool :=
  match func with
  | .str _ => true
  | .qn v => (match v with | .val "Ptr" => false | _ => true)
  | .val "Tuple" => true
  | .expr "tuple" _ => true
  | _ => false

/-- `ccall_macro_parse(exprs)`, `base/c.jl:268-369`. -/
def ccallMacroParse (exprs : CArgs) : M Parsed := do
  let (expr, gc, cancel) ← (match exprs with
    | .single e => pure (e, false, none)
    | .many es => do
      let (rest, gc, cancel) ← options es false none
      match rest with
      | [e] => pure (e, gc, cancel)
      | _ => .error (.argumentError "@ccall needs a function signature with a return type") : M (Ex × Bool × Option (Ex × Ex)))
  if !expr.isExpr "::" then .error (.argumentError "@ccall needs a function signature with a return type")
  else do
    let rettype ← arg expr 2
    let call ← arg expr 1
    if !call.isExpr "call" then .error (.argumentError "@ccall has to take a function call")
    else do
      let f ← arg call 1
      let func ← (if f.isExpr "." then do pure (Ex.expr "tuple" [← arg f 2, ← arg f 1])
        else if f.isExpr "$" then do
          let func ← arg f 1
          if literalName func then
            .error (.argumentError "interpolated value should be a variable or expression, not a literal name or tuple")
          else pure func
        else match f with
          | .sym _ => pure (Ex.expr "tuple" [.qn f])
          | _ => .error (.argumentError "@ccall function name must be a symbol, a `.` node (e.g. `libc.printf`) or an interpolated function pointer (with `$`)") : M Ex)
      let callargs ← argsOf call
      let (argstart, varargs) ← (if callargs.length ≥ 2 && (callargs.getD 1 .nothing).isExpr "parameters" then do
          pure (3, some (← argsOf (callargs.getD 1 .nothing)))
        else pure (2, none) : M (Nat × Option (List Ex)))
      let (args, types) ← pushargs ([], []) (callargs.drop (argstart - 1))
      match varargs with
      | none => pure ⟨func, rettype, types, args, gc, cancel, 0⟩
      | some vs =>
        if args.length = 0 then .error (.argumentError "C ABI prohibits vararg without one required argument")
        else do
          let nreq := args.length
          let (args, types) ← pushargs (args, types) vs
          pure ⟨func, rettype, types, args, gc, cancel, nreq⟩




/-- The calling convention argument: `:ccall` or `(:ccall, effects)`. -/
inductive Conv where
  | plain
  | effects (bits : Nat)

/-- `ccall_macro_lower(convention, func, rettype, types, args, gc_safe, cancel, nreq)`,
`base/c.jl:372-401`. A `cconv` tuple is `(cc, effects, gc_safe[, cancel[, reset]])`. -/
def ccallMacroLower (conv : Conv) (p : Parsed) : Ex :=
  let (resetSafe, effects) := match conv with
    | .plain => (false, 0)
    | .effects b => (b &&& resetSafeBit != 0, b &&& (0xFFFF ^^^ resetSafeBit))
  let base := [Ex.sym "ccall", .int effects, .bool p.gcSafe]
  match p.cancel with
  | none =>
    let cconv := if resetSafe then Ex.expr "cconv" [.expr "tuple" (base ++ [.bool false, .bool true]), .int p.nreq]
      else Ex.expr "cconv" [.expr "tuple" base, .int p.nreq]
    .expr "call" ([.sym "ccall", Ex.esc p.func, cconv, Ex.esc p.rettype,
      .expr "tuple" (p.types.map Ex.esc)] ++ p.args.map Ex.esc)
  | some (fex, sex) =>
    let nreq := if p.nreq > 0 then p.nreq + 2 else p.nreq
    let cconv := Ex.expr "cconv" [.expr "tuple" (if resetSafe then base ++ [.bool true, .bool true] else base ++ [.bool true]),
      .int nreq]
    .expr "call" ([.sym "ccall", Ex.esc p.func, cconv, Ex.esc p.rettype,
      .expr "tuple" ([.val "Ptr{Cvoid}", .val "Ptr{Cvoid}"] ++ p.types.map Ex.esc), Ex.esc fex, Ex.esc sex] ++
      p.args.map Ex.esc)

/-- `@ccall exprs...`, `base/c.jl:537-539`. -/
def ccallMacro (exprs : List Ex) : M Ex := do
  let p ← ccallMacroParse (.many exprs)
  pure (ccallMacroLower .plain p)

/-- `@ccall_effects effects exprs...`, `base/c.jl:541-543`. -/
def ccallEffects (effects : Nat) (exprs : List Ex) : M Ex := do
  let p ← ccallMacroParse (.many exprs)
  pure (ccallMacroLower (.effects effects) p)

end JuliaLean.MiscCov.CInterface
