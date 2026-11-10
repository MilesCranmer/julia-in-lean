# max_union_splitting "specifies the maximum number of union-tuples to swap or expand"
# (Compiler/src/types.jl:295-297), but is_union_split_eligible compares it with unionsplitcost,
# which counts the largest union as 2 whatever its size. A call with a 3-member and a 2-member
# union argument costs 4, is allowed with the default limit 4, and splits into 6 signatures; a
# single 20-member union costs 2 and splits into 20.
const C = Base.Compiler
id = "compiler-unionsplit-split-count-exceeds-limit"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
L = C.typeinf_lattice(C.NativeInterpreter())
a = Any[typeof(+), Union{Int8,Int16,Int32}, Union{Int8,Int16}]
n = length(C.switchtupleunion(L, a))
println("unionsplitcost = ", C.unionsplitcost(L, a), ", eligible(4) = ", C.is_union_split_eligible(L, a, 4),
        ", signatures = ", n)
big = Union{(Val{i} for i in 1:20)...}
b = Any[typeof(+), big]
println("20-member union: unionsplitcost = ", C.unionsplitcost(L, b), ", eligible(4) = ",
        C.is_union_split_eligible(L, b, 4), ", signatures = ", length(C.switchtupleunion(L, b)))
println(C.is_union_split_eligible(L, a, 4) && n > 4 ? "REPRODUCED $id" : "NOT REPRODUCED $id")
