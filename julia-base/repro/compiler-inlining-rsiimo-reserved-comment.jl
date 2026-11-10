# The comment at Compiler/src/optimize.jl:44 says "Reserved: one(UInt32) << 15 used for RSIIMO
# below", but IR_FLAG_RSIIMO is one(UInt32) << 20 (optimize.jl:57) and no flag uses bit 15.
const CC = Base.Compiler
id = "compiler-inlining-rsiimo-reserved-comment"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
src = joinpath(Sys.BINDIR, Base.DATAROOTDIR, "julia", "Compiler", "src", "optimize.jl")
line = isfile(src) ? findfirst(l -> occursin("Reserved: one(UInt32) << 15 used for RSIIMO", l), readlines(src)) : nothing
println("comment line: ", line === nothing ? "not found" : "optimize.jl:$line")
if !isdefined(CC, :IR_FLAG_RSIIMO)
    println("IR_FLAG_RSIIMO is not defined")
    println("NOT REPRODUCED $id")
    exit()
end
println("IR_FLAG_RSIIMO = 1 << ", trailing_zeros(CC.IR_FLAG_RSIIMO))
flags = [getfield(CC, n) for n in names(CC; all = true) if startswith(string(n), "IR_FLAG_") && getfield(CC, n) isa UInt32]
println("flags at bit 15: ", count(==(UInt32(1) << 15), flags))
ok = line !== nothing && CC.IR_FLAG_RSIIMO != UInt32(1) << 15
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
