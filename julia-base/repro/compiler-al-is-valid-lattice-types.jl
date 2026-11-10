# is_valid_lattice(𝕃, x) is false for every element of every lattice above JLTypeLattice.
# Compiler/src/abstractlattice.jl:281-283 joins the layer's own test and the parent's with `&&`,
# but each element passes the test of one layer only.
const CC = Base.Compiler
id = "compiler-al-is-valid-lattice-types"
L = CC.typeinf_lattice(CC.NativeInterpreter())
r1 = CC.is_valid_lattice(L, Int)
r2 = CC.is_valid_lattice(CC.ConstsLattice(), Core.Const(1))
r3 = CC.is_valid_lattice(CC.JLTypeLattice(), Int)
println("is_valid_lattice(typeinf_lattice, Int) = ", r1)
println("is_valid_lattice(ConstsLattice(), Const(1)) = ", r2)
println("is_valid_lattice(JLTypeLattice(), Int) = ", r3)
println(r1 === false && r2 === false && r3 === true ? "REPRODUCED $id" : "NOT REPRODUCED $id")
