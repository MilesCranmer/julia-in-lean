# builtin_tfunction pads a call whose last argument is a Vararg up to the builtin's maximum
# argument count. For getfield(x, name, a, b...) with b::Vararg{Bool} it calls the 4-argument
# getfield_tfunc, which reads `a` as the memory order and returns Union{} because `a` is a Bool.
# With b empty the call is the 3-argument getfield(x, name, boundscheck), which succeeds.
id = "compiler-tfuncs-vararg-optional-arg-bottom"
gb(x, b::Bool...) = (getfield(x, 1, false, b...); :reached)
rt = only(Base.return_types(gb, (Tuple{Int}, Vararg{Bool})))
r = gb((1,))
println("return_types(gb, (Tuple{Int}, Vararg{Bool})) = ", rt)
println("gb((1,)) = ", repr(r))
const CC = Base.Compiler
println("builtin_tfunction(getfield, [Tuple{Int}, Const(1), Const(false), Vararg{Bool}]) = ",
        CC.builtin_tfunction(CC.NativeInterpreter(), getfield,
                             Any[Tuple{Int}, Core.Const(1), Core.Const(false), Vararg{Bool}], nothing))
# User-visible effect: with an empty Vector{Bool} splatted, the compiled code reaches the
# `unreachable` inference put after the call. Run it in a child process, since it crashes.
code = "f(x, v::Vector{Bool}) = (getfield(x, 1, false, v...); :reached); print(f((1,), Bool[]))"
p = run(pipeline(ignorestatus(`$(Base.julia_cmd()) --startup-file=no -e $code`); stdout = devnull, stderr = devnull))
println("child running f((1,), Bool[]) with f(x, v) = (getfield(x, 1, false, v...); :reached): ",
        success(p) ? "returned" : "died, termsignal $(p.termsignal)")
println(rt === Union{} && r === :reached ? "REPRODUCED $id" : "NOT REPRODUCED $id")
