import JuliaLean.src.runtime_intrinsics_c

namespace JuliaLean.C

/-- `jl_f_intrinsic_call`: runtime function-pointer selection, compiler-only rejection and arity.

Julia source: src/builtins.c:2903-2938 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_CALLABLE(jl_f_intrinsic_call)
{
    enum intrinsic f = (enum intrinsic)*(uint32_t*)jl_data_ptr(F);
    if (f == cglobal && nargs == 1)
        f = cglobal_auto;
    unsigned fargs = intrinsic_nargs[f];
    if (!fargs)
        jl_errorf("`%s` requires the compiler", jl_intrinsic_name(f));
    JL_NARGS(intrinsic_call, fargs, fargs);

    union {
        void (*fptr)(void);
        jl_value_t *(*call1)(jl_value_t*);
        jl_value_t *(*call2)(jl_value_t*, jl_value_t*);
        jl_value_t *(*call3)(jl_value_t*, jl_value_t*, jl_value_t*);
        jl_value_t *(*call4)(jl_value_t*, jl_value_t*, jl_value_t*, jl_value_t*);
        jl_value_t *(*call5)(jl_value_t*, jl_value_t*, jl_value_t*, jl_value_t*, jl_value_t*);
    } fptr;
    fptr.fptr = runtime_fp[f];
    switch (fargs) {
        case 1:
            return fptr.call1(args[0]);
        case 2:
            return fptr.call2(args[0], args[1]);
        case 3:
            return fptr.call3(args[0], args[1], args[2]);
        case 4:
            return fptr.call4(args[0], args[1], args[2], args[3]);
        case 5:
            return fptr.call5(args[0], args[1], args[2], args[3], args[4]);
        default:
            assert(0 && "unexpected number of arguments to an intrinsic function");
    }
    jl_gc_debug_fprint_critical_error(ios_safe_stderr);
    abort();
}
```
-/
def jlCompilerRequired (name : String) : IntrinsicResult α :=
  .error (.errorException ("`" ++ name ++ "` requires the compiler"))

end JuliaLean.C
