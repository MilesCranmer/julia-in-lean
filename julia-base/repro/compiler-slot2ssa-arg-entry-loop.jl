# When block 1 is a loop header and an argument is assigned in the loop, construct_ssa! puts
# no phi node for the argument in block 1, so every iteration reads the argument's entry value.
# compute_live_ins (Compiler/src/ssair/slot2ssa.jl:494-530) counts the argument's def (0) as a
# def at the top of block 1, which hides the use in block 1 that the back edge reaches first.
# Lowering never makes this shape (it copies an assigned argument into a new slot at statement
# 1), but a generator that returns a CodeInfo can: the function below returns 1 instead of 4.
const CC = Base.Compiler
id = "compiler-slot2ssa-arg-entry-loop"
"--interp" in ARGS || println(VERSION, " ", Base.GIT_VERSION_INFO.commit)

const CNT = Ref(0)
cont() = (CNT[] += 1; CNT[] < 4)
tmpl(x) = x

# 1: x = x + 1;  2: %2 = cont();  3: goto 5 if not %2;  4: goto 1;  5: return x
function mkci()
    ci = copy(first(code_lowered(tmpl, (Any,))))
    ci.code = Any[Expr(:(=), Core.SlotNumber(2), Expr(:call, GlobalRef(Base, :+), Core.SlotNumber(2), 1)),
                  Expr(:call, GlobalRef(Main, :cont)),
                  Core.GotoIfNot(Core.SSAValue(2), 5),
                  Core.GotoNode(1),
                  Core.ReturnNode(Core.SlotNumber(2))]
    ci.ssavaluetypes = 5
    ci.ssaflags = fill(UInt32(0), 5)
    ci.slotflags = UInt8[0x00, 0x08 | 0x02]
    ci.debuginfo = Core.DebugInfo(:none)
    ci.method_for_inference_limit_heuristics = nothing
    ci.edges = nothing
    return ci
end
const CI = mkci()

struct LoopGen end
(::LoopGen)(world::UInt, source, args...) = copy(CI)
@eval function argloop(x)
    $(Expr(:meta, :generated, LoopGen()))
    $(Expr(:meta, :generated_only))
end

CNT[] = 0
r = argloop(0)
if "--interp" in ARGS
    print(r)
    exit()
end
println("argloop(0) = ", r, " (expected 4)")

# The same code run by the interpreter, without inference or slot2ssa.
interp = readchomp(`$(Base.julia_cmd()) --compile=min $(@__FILE__) --interp`)
println("argloop(0) with --compile=min = ", interp)

# The IR construct_ssa! returns: no phi node in block 1, and `x + 1` reads the argument.
try
    code_ir = only(Base.code_ircode(argloop, (Int,)))[1]
    println("block 1 of code_ircode: ", [code_ir.stmts.stmt[i] for i in code_ir.cfg.blocks[1].stmts])
catch e
    println("IR inspection skipped: ", sprint(showerror, e))
end

println(r != 4 && interp == "4" ? "REPRODUCED $id" : "NOT REPRODUCED $id")
