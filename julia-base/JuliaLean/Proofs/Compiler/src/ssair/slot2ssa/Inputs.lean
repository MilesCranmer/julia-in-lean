import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Spec

/-!
The counterexample inputs of the refuted properties of `Compiler/src/ssair/slot2ssa.jl`: what
`construct_ssa!` gets for two small Julia functions on the pinned Julia (the IR after
`convert_to_ircode!`, the block entry states and `π` tests, the statement handlers). They were
printed from the pinned Julia in the encoding of `difftest/compiler/slot2ssa.jl`, as Lean terms.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair

/-! ## A loop whose header is a catch block -/

/-- The input of `construct_ssa!` for
```julia
function h3(c)
    x = 0
    try
        x = 1
        c[] == 0 && error("e")
    catch
        while c[] < 3
            c[] += 1
            x += 1
        end
    end
    return x
end
```
at `(Base.RefValue{Int},)`. The catch block (block 7, statements 13-16) is also the header of
the `while` loop: its predecessors are the `enter` block 2, the virtual `0` and the loop body 8. -/
def h3Inputs : SSAInputs where
  nargs := 2
  slotnames := #["#self#", "c", "x"]
  bbStates := #[some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨true, true, "Union{}", true⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Core.Const(0)", true⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Core.Const(0)", true⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Core.Const(1)", true⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Core.Const(1)", true⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Core.Const(1)", true⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Int64", false⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Int64", false⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Int64", false⟩], some #[⟨false, false, "Core.Const(Main.h3)", false⟩, ⟨false, false, "Base.RefValue{Int64}", false⟩, ⟨false, false, "Int64", false⟩]]
  handler := #[0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  sp := #[]

/-- The IR of `h3` after `convert_to_ircode!`. -/
def h3IR : SIR where
  stmts := #[(.expr "=" #[(.slot 3), (.lit "Int64:0")]), (.enter 13 none), (.expr "=" #[(.slot 3), (.lit "Int64:1")]), (.glob "Main.=="), (.expr "call" #[(.glob "Base.getindex"), (.slot 2)]), (.expr "call" #[(.ssa 4), (.ssa 5), (.lit "Int64:0")]), (.gotoifnot (.ssa 6) 11), (.glob "Main.error"), (.expr "call" #[(.ssa 8), (.lit "String:\"e\"")]), (.ret none), (.expr "leave" #[(.ssa 2)]), (.goto 26), (.glob "Main.<"), (.expr "call" #[(.glob "Base.getindex"), (.slot 2)]), (.expr "call" #[(.ssa 13), (.ssa 14), (.lit "Int64:3")]), (.gotoifnot (.ssa 15) 25), (.glob "Main.+"), (.expr "call" #[(.glob "Base.getindex"), (.slot 2)]), (.expr "call" #[(.ssa 17), (.ssa 18), (.lit "Int64:1")]), (.expr "call" #[(.glob "Base.setindex!"), (.slot 2), (.ssa 19)]), (.glob "Main.+"), (.slot 3), (.expr "=" #[(.slot 3), (.expr "call" #[(.ssa 21), (.ssa 22), (.lit "Int64:1")])]), (.goto 13), (.expr "pop_exception" #[(.ssa 2)]), (.slot 3), (.ret (some (.ssa 26)))]
  nothrow := #[true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false]
  cfg := ⟨#[⟨1, 1, #[0], #[2]⟩, ⟨2, 2, #[1], #[7, 3]⟩, ⟨3, 7, #[2], #[5, 4]⟩, ⟨8, 10, #[3], #[]⟩, ⟨11, 11, #[3], #[6]⟩, ⟨12, 12, #[5], #[10]⟩, ⟨13, 16, #[2, 0, 8], #[9, 8]⟩, ⟨17, 24, #[7], #[7]⟩, ⟨25, 25, #[7], #[10]⟩, ⟨26, 27, #[6, 9], #[]⟩], #[2, 3, 8, 11, 12, 13, 17, 25, 26, 28]⟩
  newNodes := #[]

/-! ## A `@goto` into a loop body -/

/-- The input of `construct_ssa!` for
```julia
function g2(a)
    @goto L1
    for i = 1:a
        w = 1
        while @isdefined(w)
            @label L1
            y = 1
        end
    end
    return 0
end
```
at `(Int,)`. Lowering keeps the iterator `%5` and the state `%13` of the `for` loop in SSA
values defined in blocks 2 and 3, which the `@goto` skips, and uses them in block 6 (statement
19, `iterate(%5, %13)`). Inference has turned the dead statements of blocks 2, 3, 7 and 8 into
constants; blocks 2 and 7 have no predecessors. -/
def g2Inputs : SSAInputs where
  nargs := 2
  slotnames := #["#self#", "a", "", "i", "w", "y"]
  bbStates := #[some #[⟨false, false, "Core.Const(Main.g2)", false⟩, ⟨false, false, "Int64", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", true⟩], none, none, some #[⟨false, false, "Core.Const(Main.g2)", false⟩, ⟨false, false, "Int64", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", false⟩, ⟨false, false, "Core.Const(1)", true⟩], some #[⟨false, false, "Core.Const(Main.g2)", false⟩, ⟨false, false, "Int64", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", true⟩], some #[⟨false, false, "Core.Const(Main.g2)", false⟩, ⟨false, false, "Int64", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", false⟩, ⟨true, true, "Union{}", false⟩, ⟨false, false, "Core.Const(1)", true⟩], none, none]
  handler := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  sp := #[]

/-- The IR of `g2` after `convert_to_ircode!`. -/
def g2IR : SIR where
  stmts := #[(.newvar 3), .nothing, (.goto 17), (.lit "Core.Const:Core.Const(:(Main.:(:)))"), (.lit "Core.Const:Core.Const(:((%4)(1, _2)))"), (.lit "Core.Const:Core.Const(:(_3 = Base.iterate(%5)))"), (.lit "Core.Const:Core.Const(:(_3))"), (.lit "Core.Const:Core.Const(:(%7 === nothing))"), (.lit "Core.Const:Core.Const(:(Base.not_int(%8)))"), (.lit "Core.Const:Core.Const(:(goto %25 if not %9))"), (.lit "Core.Const:Core.Const(:(_3))"), (.lit "Core.Const:Core.Const(:(_4 = Core.getfield(%11, 1)))"), (.lit "Core.Const:Core.Const(:(Core.getfield(%11, 2)))"), (.lit "Core.Const:Core.Const(:(_5 = 1))"), (.expr "isdefined" #[(.slot 5)]), (.gotoifnot (.ssa 15) 19), (.expr "=" #[(.slot 6), (.lit "Int64:1")]), (.goto 15), (.expr "=" #[(.slot 3), (.expr "call" #[(.glob "Base.iterate"), (.ssa 5), (.ssa 13)])]), (.lit "Core.Const:Core.Const(:(_3))"), (.lit "Core.Const:Core.Const(:(%20 === nothing))"), (.lit "Core.Const:Core.Const(:(Base.not_int(%21)))"), (.ret none), (.lit "Core.Const:Core.Const(:(goto %11))"), (.lit "Core.Const:Core.Const(:(return 0))"), (.ret none)]
  nothrow := #[false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true, false, false, true]
  cfg := ⟨#[⟨1, 3, #[0], #[5]⟩, ⟨4, 10, #[], #[8, 3]⟩, ⟨11, 14, #[2, 7], #[4]⟩, ⟨15, 16, #[3, 5], #[6, 5]⟩, ⟨17, 18, #[1, 4], #[4]⟩, ⟨19, 23, #[4], #[]⟩, ⟨24, 24, #[], #[3]⟩, ⟨25, 26, #[2], #[]⟩], #[4, 11, 15, 17, 19, 24, 25, 27]⟩
  newNodes := #[]

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
