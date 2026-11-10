# Narrower argument types can turn union splitting off. unionsplitcost counts union members, not
# types, so `Union{Int8,Int16,Nothing}` (3 members) costs more than the wider
# `Union{Integer,Nothing}` (2 members). With the default max_union_splitting = 4,
# is_union_split_eligible allows splitting the wider call and refuses the narrower one.
const C = Base.Compiler
id = "compiler-unionsplit-cost-subtype-monotone"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
L = C.typeinf_lattice(C.NativeInterpreter())
wide = Any[typeof(+), Union{Integer,Nothing}, Union{Integer,Nothing}]
narrow = Any[typeof(+), Union{Int8,Int16,Nothing}, Union{Int8,Int16,Nothing}]
println("narrow[i] <: wide[i]: ", all(narrow .<: wide))
cw = C.unionsplitcost(L, wide); cn = C.unionsplitcost(L, narrow)
ew = C.is_union_split_eligible(L, wide, 4); en = C.is_union_split_eligible(L, narrow, 4)
println("cost(wide) = ", cw, ", eligible = ", ew, "; cost(narrow) = ", cn, ", eligible = ", en)
println(all(narrow .<: wide) && ew && !en ? "REPRODUCED $id" : "NOT REPRODUCED $id")
