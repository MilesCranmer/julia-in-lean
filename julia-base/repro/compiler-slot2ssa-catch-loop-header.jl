# A `while` loop at the start of a `catch` block makes the catch block the loop header. For a
# local stored in the `try` and changed in the loop, construct_ssa! places both a PhiC node and
# a phi node in that block, and the renaming then reads the PhiC node in the loop
# (Compiler/src/ssair/slot2ssa.jl:706-715): the phi, which carries the loop value, is dead.
# The loop reads the value from the `try` on every iteration, so the result is wrong. (When the
# local is a pointer such as a `Ref` argument, calling the function segfaulted in our runs.)
const CC = Base.Compiler
id = "compiler-slot2ssa-catch-loop-header"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)

const C = Ref(0)
function loopcatch()
    x = 0
    try
        x = 1
        error("e")
    catch
        while C[] < 3
            C[] += 1
            x += 1
        end
    end
    return x
end

C[] = 0
r = loopcatch()
println("loopcatch() = ", r, " (expected 4)")

# The same function run by the interpreter, without inference or slot2ssa.
src = Base.remove_linenums!(quote
    const C = Ref(0)
    function loopcatch()
        x = 0
        try
            x = 1
            error("e")
        catch
            while C[] < 3
                C[] += 1
                x += 1
            end
        end
        return x
    end
    print(loopcatch())
end)
interp = readchomp(`$(Base.julia_cmd()) --compile=min -e $(string(src))`)
println("loopcatch() with --compile=min = ", interp)

# The IR after slot2ssa: the phi for `x` in the catch block is not used. (Diagnostic only; the
# internal API differs on 1.13.)
try
mi = Base.method_instance(loopcatch, ())
ninterp = CC.NativeInterpreter()
frame = CC.typeinf_frame(ninterp, mi, false)
opt = CC.OptimizationState(frame, ninterp)
ir = isdefined(CC, :convert_to_ircode!) ? CC.convert_to_ircode!(opt.src, opt) : CC.convert_to_ircode(opt.src, opt)
domtree = CC.construct_domtree(ir)
defuse = CC.scan_slot_def_use(Int(opt.src.nargs), opt.src, ir.stmts.stmt)
out = CC.construct_ssa!(opt.src, ir, opt, domtree, defuse, CC.optimizer_lattice(ninterp))
used = falses(length(out.new_nodes))
for s in Iterators.flatten((out.stmts.stmt, out.new_nodes.stmts.stmt)), op in CC.userefs(s)
    v = op[]
    v isa Core.SSAValue && v.id > length(out.stmts) && (used[v.id - length(out.stmts)] = true)
end
local dead = [i for i in 1:length(out.new_nodes) if out.new_nodes.stmts.stmt[i] isa Core.PhiNode &&
        !isempty(out.new_nodes.stmts.stmt[i].edges) && !used[i]]
println("phi nodes construct_ssa! inserted but never used: ", [out.new_nodes.stmts.stmt[i] for i in dead])
catch e
    println("IR inspection skipped: ", sprint(showerror, e))
end

println(r != 4 && interp == "4" ? "REPRODUCED $id" : "NOT REPRODUCED $id")
