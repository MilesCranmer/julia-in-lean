# Inference never terminates on a `@goto` loop that assigns a PartialTypeVar in two merge blocks.
# Each block's entry state is Union{Nothing, TypeVar}, and ⊑(PartialTypeVar, Union{Nothing, TypeVar})
# is false (Compiler/src/typelattice.jl:561-562), so `stupdate!` reports a change on every visit.
# Same shape as the Const(::Bool) hang fixed by JuliaLang/julia#64441.
# Inference runs in a child process with a time limit; the control must finish, the PTV case must not.
id = "compiler-tl-sqsub-widenconst-upper-hang"
println("VERSION = ", VERSION, ", commit ", Base.GIT_VERSION_INFO.commit)
code(body) = """
function g(q)
    h = nothing
    q && @goto a
    @label b; h = $body
    @label a; h = $body; @goto b
end
t = @elapsed Base.infer_return_type(g, (Bool,))
println("finished in ", t, " s")
"""
function finishes(body, limit)
    p = run(pipeline(`$(Base.julia_cmd()) --startup-file=no -e $(code(body))`; stdout, stderr=devnull); wait=false)
    t0 = time()
    while process_running(p) && time() - t0 < limit
        sleep(0.2)
    end
    running = process_running(p)
    running && kill(p)
    return !running
end
ctl = finishes("1", 60)
ptv = finishes("TypeVar(:T)", 60)
println("control (h = 1) finishes: ", ctl, ";  PartialTypeVar (h = TypeVar(:T)) finishes within 60 s: ", ptv)
println(ctl && !ptv ? "REPRODUCED $id" : "NOT REPRODUCED $id")
