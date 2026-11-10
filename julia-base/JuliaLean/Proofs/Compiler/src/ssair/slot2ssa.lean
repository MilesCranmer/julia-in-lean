import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.ssair.slot2ssa
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.BoundedIdf
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.BoundedPruned
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.BoundedSsa
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.BoundedSem
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Fixup
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.General
import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Refuted

/-!
Properties of `Compiler/src/ssair/slot2ssa.jl` (the slot def/use scan, liveness, the iterated
dominance frontier, `construct_ssa!` and `domsort_ssa!`) and of the heap of
`Compiler/src/ssair/heap.jl` it uses. The model is `JuliaLean/Compiler/src/ssair/slot2ssa.lean`.

Topic files under `slot2ssa/`: `Spec` (dominance frontiers and liveness by definition, the CFGs
with statement ranges), `Checks` and `Props` (the IDF and liveness checks, the statements),
`Ssa` (the end-to-end check of `construct_ssa!` on small lowered-code shapes), `Heap`,
`Inputs` (the counterexample inputs printed from the pinned Julia), `Bounded*`, `Pruned/`,
`SsaChecks/` (exhaustive kernel evaluation), `Sem` (what an IR does, and the end-to-end check
that `construct_ssa!` and `domsort_ssa!` keep it, with `SemChecks/` and `BoundedSem`), `Fixup`
(`fixup_uses!`), `General` (the open general statements and `renumber_ssa`) and `Refuted`.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Registry

private def s2s : String := "Compiler/src/ssair/slot2ssa.jl"
private def heap : String := "Compiler/src/ssair/heap.jl"

private def idfFn : String :=
  "iterated_dominance_frontier(cfg::CFG, liveness::BlockLiveness, domtree::DomTree)"
private def liveFns : List String :=
  ["compute_live_ins(cfg::CFG, slot::SlotInfo)",
   "compute_live_ins(cfg::CFG, defs::Vector{Int}, uses::Vector{Int})"]
private def ssaFns : List String :=
  ["construct_ssa!(ci::CodeInfo, ir::IRCode, sv::OptimizationState, domtree::DomTree, defuses::Vector{SlotInfo}, 𝕃ₒ::AbstractLattice)",
   "domsort_ssa!(ir::IRCode, domtree::DomTree)",
   "rename_incoming_edge(old_edge::Int, old_to::Int, result_order::Vector{Int}, bb_rename::Vector{Int})",
   "rename_outgoing_edge(old_to::Int, old_from::Int, result_order::Vector{Int}, bb_rename::Vector{Int})",
   "rename_phinode_edges(node::PhiNode, bb::Int, result_order::Vector{Int}, bb_rename::Vector{Int})",
   "renumber_ssa!(@nospecialize(stmt), ssanums::Vector{SSAValue}, new_ssa::Bool=false)",
   "new_to_regular(@nospecialize(stmt), new_offset::Int)",
   "make_ssa!(ci::CodeInfo, code::Vector{Any}, idx::Int, @nospecialize(typ))",
   "fixup_slot!(ir::IRCode, ci::CodeInfo, idx::Int, slot::Int, @nospecialize(ssa), @nospecialize(def_ssa))",
   "fixemup!(@specialize(slot_filter), @specialize(rename_slot), ir::IRCode, ci::CodeInfo, idx::Int, @nospecialize(stmt))",
   "rename_uses!(ir::IRCode, ci::CodeInfo, idx::Int, @nospecialize(stmt), renames::Vector{Pair{Any, Any}})",
   "scan_slot_def_use(nargs::Int, ci::CodeInfo, code::Vector{Any})",
   "scan_entry!(result::Vector{SlotInfo}, idx::Int, @nospecialize(stmt))"]
private def fixupFns : List String :=
  ["fixup_uses!(ir::IRCode, ci::CodeInfo, code::Vector{Any}, uses::Vector{Int}, slot::Int, @nospecialize(ssa))",
   "fixemup!(@specialize(slot_filter), @specialize(rename_slot), ir::IRCode, ci::CodeInfo, idx::Int, @nospecialize(stmt))",
   "fixup_slot!(ir::IRCode, ci::CodeInfo, idx::Int, slot::Int, @nospecialize(ssa), @nospecialize(def_ssa))"]
private def heapFns : List String :=
  ["heapleft(i::Integer)", "heapright(i::Integer)", "heapparent(i::Integer)",
   "percolate_down!(xs::Vector, i::Integer, x, o::Ordering, len::Integer=length(xs))",
   "percolate_up!(xs::Vector, i::Integer, x, o::Ordering)",
   "heappop!(xs::Vector, o::Ordering)", "heappush!(xs::Vector, x, o::Ordering)",
   "heapify!(xs::Vector, o::Ordering)"]

/-- Registry entries of `Compiler/src/ssair/slot2ssa.jl` and `Compiler/src/ssair/heap.jl`. -/
def entries : List Entry := [
  -- Bounded, proven by exhaustive kernel evaluation.
  { id := "compiler-slot2ssa-idf-small", juliaFile := s2s, juliaFns := [idfFn],
    statement := "On every CFG of cfgsUpTo3 (564 CFGs of 1 to 3 blocks plus the domtree area's lowering-shaped 3-block CFGs, with self loops, irreducible loops, back edges into block 1, catch blocks with the virtual predecessor and unreachable blocks), for every set of reachable def blocks given in every order, iterated_dominance_frontier without liveness (live_in_bbs === nothing) and with the model of construct_domtree returns exactly the iterated dominance frontier of the defs by definition (least fixed point of DF(defs ∪ X), DF from dominance by definition), with no block twice.",
    source := "docstring Compiler/src/ssair/slot2ssa.jl:186-228 (\"Run iterated dominance frontier\", following [SG95]); definition of the iterated dominance frontier",
    status := .proven, prop := ``IdfSmall, thm := some ``idfSmall_proven,
    notes := "Exhaustive check by kernel evaluation (decide +kernel), in the same slices as the domtree area. The domtree area's branchCFGs (4 to 9 blocks) are not checked here because of cost; see coverage/review/Compiler_src_ssair_slot2ssa.fixes.md. Unreachable def blocks are left out on purpose: for them the function also returns block 1 or unreachable blocks (on [[], [2]] with defs [2] it returns [2], on [[], [1]] it returns [1]), which the definition does not, since an unreachable block dominates nothing. Inference deletes dead code before slot2reg, so construct_ssa! does not pass such defs; this was checked on three functions with dead loops and dead @goto loops, whose code_ircode is valid. The difftest's idf op (about 2700 cases per seed, unreachable defs included) agrees with the pinned Julia. The general statement is compiler-slot2ssa-idf." },
  { id := "compiler-slot2ssa-pruned-small", juliaFile := s2s, juliaFns := idfFn :: liveFns,
    statement := "On every CFG of cfgsUpTo3 (564 CFGs of 1 to 3 blocks plus the domtree area's lowering-shaped 3-block CFGs) with two statements per block, for every def/use pattern of one slot (in each block: nothing, a use, a def then a use, or a use and a def in one statement as in x = x + 1; with and without the argument def 0, which this statement counts, as compute_live_ins does, as a def at the top of block 1) whose defs are in reachable blocks: compute_live_ins returns def_bbs = the blocks with a def and live_in_bbs = the blocks where the slot is live-in by the backward liveness equations, each without a repeated block; and iterated_dominance_frontier with that liveness returns exactly the pruned SSA phi positions (iterated dominance frontier of the def blocks ∩ live-in blocks), with no block twice.",
    source := "comments Compiler/src/ssair/slot2ssa.jl:495-497 (remove blocks where all uses are dominated by a def, to prevent dead phi nodes) and 258-262 (place a phi unless liveness said otherwise); definition of pruned SSA",
    status := .proven, prop := ``PrunedPhisSmall, thm := some ``prunedPhisSmall_proven,
    notes := "Exhaustive check by kernel evaluation: 2 + 50 + 512 + 48 CFGs times up to 128 patterns, split into 71 kernel checks (Pruned/S0 to S7, and six for lower3). The domtree area's branchCFGs (4 to 9 blocks) are not checked here because of cost; see coverage/review/Compiler_src_ssair_slot2ssa.fixes.md. compute_live_ins(cfg, slot::SlotInfo) is the one-line method that passes slot.defs and slot.uses; the model inlines it in idfSlotsLoop. With unreachable def blocks the pruned result can also contain an unreachable live-in block, for which construct_ssa! would hit @assert bbstate !== nothing; inference's dead-code deletion keeps this from happening (see compiler-slot2ssa-idf-small). Counting the argument def as a def at the top of block 1 is right only when block 1 has no predecessor but the virtual 0: when a back edge enters block 1, a use in block 1 is reached from that edge before any def, so block 1 is live-in, but compute_live_ins and this statement both leave it out. That is the miscompile compiler-slot2ssa-arg-entry-loop. The general statement is compiler-slot2ssa-pruned." },
  { id := "compiler-slot2ssa-ssa-small", juliaFile := s2s, juliaFns := ssaFns,
    statement := "For one local or argument x and every lowered-code CFG with 1 to 3 blocks (each block ends in a return, a fall-through, a goto to any block or a goto-if-not to any block; 158 CFGs with self loops, irreducible loops and unreachable blocks), with three statements per block and every def/use pattern of x (as in compiler-slot2ssa-pruned-small, every read having an assignment before it on some path), with inference's view of x computed from the definitions (assigned on every path, on some path; dead blocks without a state and with their code removed): construct_ssa! as slot2reg calls it returns, every phi node has exactly one edge per predecessor of its block and one value slot per edge, every SSA use in a reachable block is dominated by its definition (the value of a phi edge dominating the end of the predecessor), and the result is in dominator order with every statement's use of a statement after it.",
    source := "docstring of domsort_ssa! Compiler/src/ssair/slot2ssa.jl:328-334 (domtree order; any use of an SSA value comes after its definition); the SSA property construct_ssa! is for",
    status := .proven, prop := ``SsaSmall, thm := some ``ssaSmall_proven,
    notes := "Exhaustive check by kernel evaluation: about 15800 inputs (3470 of the 3-block ones get a phi with two or more edges, 2606 an undef check, 214 a split block and 307 a fixup goto in domsort_ssa!), in 443 kernel checks (SsaChecks/: two CFGs per check for the first 40 3-block CFGs, then one CFG in four parts). No try/catch: with a catch block that is also a loop header the renaming is wrong (compiler-slot2ssa-catch-loop-header). A @goto into a loop body makes lowering emit SSA values that do not dominate their uses, and construct_ssa! then throws AssertionError: val.id > 0 (theorem g2_asserts on the input of `function g2(a); @goto L1; for i = 1:a; w = 1; while @isdefined(w); @label L1; y = 1; end; end; return 0; end`). That is the known lowering bug JuliaLang/julia#61132 (also #47346, #60816), so it is not registered here. ssaPropsOK checks only the shape of the result, so a renaming that turns every slot read into a constant would also pass; compiler-slot2ssa-sem-small checks on the same inputs that the result does what the lowered code does. The general statement is compiler-slot2ssa-ssa." },
  { id := "compiler-slot2ssa-sem-small", juliaFile := s2s, juliaFns := ssaFns,
    statement := "For one local or argument x and every input of compiler-slot2ssa-ssa-small (every lowered-code CFG with 1 to 3 blocks, every def/use pattern of x whose reads have an assignment before them on some path), run on symbolic values with every oracle of three outcomes for the branch condition: the IR that construct_ssa! hands to domsort_ssa! and the result of domsort_ssa! make the same calls with the same arguments in the same order and end the same way (the same return value, or UndefVarError for the same local), neither gets stuck, and domsort_ssa! keeps every new node; and, when x is a local or no block jumps back to block 1 (lowering keeps this: it copies an assigned argument into a new slot at statement 1), the lowered code (with slots) and the IR construct_ssa! hands to domsort_ssa! agree in the same way.",
    source := "docstring of domsort_ssa! Compiler/src/ssair/slot2ssa.jl:328-334 (sorting the blocks into domtree order; control flow is kept by the fixup gotos, lines 373-385 and 428-458); construct_ssa! turns slots into SSA values, so the code must do what it did before",
    status := .proven, prop := ``SemSmall, thm := some ``semSmall_proven,
    notes := "Exhaustive check by kernel evaluation over the about 15800 inputs of compiler-slot2ssa-ssa-small, eight oracles each, in 584 kernel checks (8 in SemChecks/C12, then four per file in SemChecks/G000 to G143 with one 3-block CFG each, in four parts). The semantics (Sem.lean, runIR) logs each call as a term built from its arguments, so a result that drops, adds, reorders or changes a call, or ends differently, fails; Core.typeassert(c, Core.Bool), what construct_ssa! makes of a conditional jump to the next block, is not logged. A run is stuck on any node it does not cover, on an SSA value read before its definition ran, on a phi node with no edge for the block control came from, and on a phi node that is not at the start of its block. Runs have a budget of 16 block entries; when one runs out, its log must be a prefix of the other's. A domsort_ssa! that returned `return 0`, or that sent a goto or a fall-through to the wrong block, fails on the inputs whose blocks make different calls. Without the condition on block 1 the second part is false: compiler-slot2ssa-arg-entry-loop." },
  { id := "compiler-slot2ssa-heap-small", juliaFile := heap, juliaFns := heapFns,
    statement := "Under the ordering By(x -> -x[2]) of iterated_dominance_frontier, for every vector of 0 to 5 elements with levels 1 to 3: heapify! returns a permutation of it with the heap property (no element lower ordered than its parent); heappop! on that heap returns an element of the highest level and leaves a heap of the other elements; heappush! of an element of any level 1 to 3 gives a heap of all the elements.",
    source := "docstrings Compiler/src/ssair/heap.jl:33-71 (heappop!, heappush!, heapify!) and the comments \"Binary min-heap percolate down/up\" at lines 11 and 23",
    status := .proven, prop := ``HeapSmall, thm := some ``heapSmall_proven,
    notes := "Exhaustive check by kernel evaluation over 364 vectors. heapleft, heapright and heapparent are inlined in the model as 2i, 2i + 1 and i / 2 (Int division rounds toward zero, as div does, on these positive indices). Only the slot2ssa ordering is modelled. The general statement is compiler-slot2ssa-heap." },
  { id := "compiler-slot2ssa-fixup-uses-small", juliaFile := s2s, juliaFns := fixupFns,
    statement := "For every vector of two statements built from slot 2, slot 3 and a literal (a bare operand, a call on two operands, an assignment of an operand or a call to slot 2 or 3, @isdefined of slot 2 or 3, a conditional jump, a return, a one-edge phi node, a NewvarNode, nothing), both IR_FLAG_NOTHROW flags, and the new values SSAValue(9), Argument(2) and UNDEF_TOKEN, fixup_uses!(ir, ci, code, uses, 2, ssa) with uses the uses of slot 2 by scan_slot_def_use returns and: for a new value other than UNDEF_TOKEN, inserts no node, turns each use statement into the statement with every read of slot 2 replaced by the new value (operands, the right side of an assignment, phi values; @isdefined(slot 2) becomes true) and leaves the other statements unchanged, after which scan_slot_def_use finds no use of slot 2, the same defs of slot 2 and the same defs and uses of slot 3; for UNDEF_TOKEN, leaves the statements that are not uses unchanged, inserts only throw_undef_if_not(:x, false) nodes, and puts one before each use other than @isdefined (for a phi node, before the last statement of the block of its edge).",
    source := "Compiler/src/ssair/slot2ssa.jl:151-155 (fixup_uses! renames the uses of one slot to ssa, with the slot defined) and 82-97 (fixup_slot!: an undef error for UNDEF_TOKEN)",
    status := .proven, prop := ``FixupUsesSmall, thm := some ``fixupUsesSmall_proven,
    notes := "Exhaustive check by kernel evaluation over 16428 inputs, in 37 kernel checks (Fixup.lean). fixup_uses! is called only from the disabled `if false` branch of construct_ssa! (Compiler/src/ssair/slot2ssa.jl:578-599), so it does not run in compiled code today. Static parameters are left out of the statements here; the difftest's fixup op covers them. With UNDEF_TOKEN a use @isdefined(x) becomes true: compiler-slot2ssa-fixup-uses-isdefined." },
  -- General, proven.
  { id := "compiler-slot2ssa-renumber", juliaFile := s2s,
    juliaFns := ["renumber_ssa(stmt::SSAValue, ssanums::Vector{SSAValue}, new_ssa::Bool=false)"],
    statement := "renumber_ssa(SSAValue(id), ssanums) is SSAValue(id) for id > length(ssanums), ssanums[id] when 1 <= id <= length(ssanums) and that entry is positive, an AssertionError when the entry is not positive, and a BoundsError for id < 1.",
    source := "Compiler/src/ssair/slot2ssa.jl:48-56",
    status := .proven, prop := ``RenumberSsaSpec, thm := some ``renumberSsaSpec_proven,
    notes := "The AssertionError branch is the one the @goto-into-a-loop input reaches (see compiler-slot2ssa-ssa-small)." },
  -- General, open.
  { id := "compiler-slot2ssa-idf", juliaFile := s2s, juliaFns := [idfFn],
    statement := "compiler-slot2ssa-idf-small for every CFG of compute_basic_blocks form.",
    source := "docstring Compiler/src/ssair/slot2ssa.jl:186-228",
    status := .todo, prop := ``IdfAll,
    notes := "Needs a proof of the Sreedhar-Gao walk (levels, the visited set across heap pops) over the model, on top of a proof of the dominator tree (compiler-domtree-construct, open)." },
  { id := "compiler-slot2ssa-pruned", juliaFile := s2s, juliaFns := idfFn :: liveFns,
    statement := "compiler-slot2ssa-pruned-small for every CFG of compute_basic_blocks form.",
    source := "comments Compiler/src/ssair/slot2ssa.jl:495-497 and 258-262",
    status := .todo, prop := ``PrunedPhisAll },
  { id := "compiler-slot2ssa-ssa", juliaFile := s2s, juliaFns := ssaFns,
    statement := "compiler-slot2ssa-ssa-small for lowered-code CFGs of any number of blocks.",
    source := "docstring Compiler/src/ssair/slot2ssa.jl:328-334",
    status := .todo, prop := ``SsaAll,
    notes := "The difftest's ssa op (about 7900 generated functions per seed) agrees with the pinned Julia; verify_ir after compact! fails on 20-26 per seed, all inspected ones being the catch-block loop header of compiler-slot2ssa-catch-loop-header or a @goto into a loop." },
  { id := "compiler-slot2ssa-heap", juliaFile := heap, juliaFns := heapFns,
    statement := "compiler-slot2ssa-heap-small for vectors of any length and any levels.",
    source := "docstrings Compiler/src/ssair/heap.jl:33-71",
    status := .todo, prop := ``HeapAll },
  -- Refuted.
  { id := "compiler-slot2ssa-arg-entry-loop", juliaFile := s2s,
    juliaFns := ["construct_ssa!(ci::CodeInfo, ir::IRCode, sv::OptimizationState, domtree::DomTree, defuses::Vector{SlotInfo}, 𝕃ₒ::AbstractLattice)",
                 "compute_live_ins(cfg::CFG, defs::Vector{Int}, uses::Vector{Int})"],
    statement := "construct_ssa! keeps what the code does: for one local or argument x and every input of compiler-slot2ssa-ssa-small, on every oracle of three branch outcomes, the lowered code and the IR construct_ssa! hands to domsort_ssa! make the same calls with the same arguments in the same order and end the same way (compiler-slot2ssa-sem-small without its condition on block 1).",
    source := "construct_ssa! turns slots into SSA values, so the code must do what it did before; comment Compiler/src/ssair/slot2ssa.jl:495-497 (only blocks where all uses are dominated by a def lose their phi)",
    status := .refuted, prop := ``ConstructSemAll, thm := some ``constructSemAll_refuted,
    issue := "none found (queries: slot2ssa argument loop; construct_ssa argument; compute_live_ins; phi entry block; entry block loop header; back edge first block; generated function CodeInfo loop; generated CodeInfo wrong result; goto first statement; missing phi argument; slot2ssa; loop argument wrong result generated; label first statement goto; CodeInfo generator loop argument; phi node missing loop; block 1 predecessor; prs: compute_live_ins, entry block phi, slot2ssa argument)",
    notes := "Counterexample: argLoopSuccs/argLoopPats, x the argument: block 1 runs x = x + 1 and jumps back to itself through block 2 while Main.c holds, block 3 calls f(x). compute_live_ins counts the argument def 0 as a def at the top of block 1 (block_for_inst(cfg, 0) is 1, and 0 sorts before every use), so the use of x in block 1, which the back edge reaches first, counts as covered: block 1 is not live-in, iterated_dominance_frontier drops it, and block 1 gets no phi for x. Every iteration then computes Argument(2) + 1. Lowering does not make this shape for source code (it copies an argument that the body assigns into a new slot at statement 1, as x@_3 = x@_2), but a generator that returns a CodeInfo can: repro/compiler-slot2ssa-arg-entry-loop.jl returns 1 instead of 4 (4 with --compile=min). The same input passes compiler-slot2ssa-ssa-small, whose checks are about the shape of the result." },
  { id := "compiler-slot2ssa-fixup-uses-isdefined", juliaFile := s2s, juliaFns := fixupFns,
    statement := "compiler-slot2ssa-fixup-uses-small, and in addition: with UNDEF_TOKEN as the new value, a use @isdefined(x) of the slot becomes false.",
    source := "Compiler/src/ssair/slot2ssa.jl:151-155; the @isdefined case of fixemup! (lines 119-126) answers with the undef half of the renaming, and UNDEF_TOKEN is the value of a slot that has none",
    status := .refuted, prop := ``FixupIsdefinedUndef, thm := some ``fixupIsdefinedUndef_refuted,
    issue := "none found (queries: fixup_uses; isdefined UNDEF_TOKEN; fixemup; prs: the same)",
    notes := "fixup_uses! passes the renaming ssa => true whatever ssa is, so with UNDEF_TOKEN the @isdefined case returns true (theorem fixupIsdefined_true on [nothing, @isdefined(x)]), while every other read of the slot gets throw_undef_if_not(:x, false). repro/compiler-slot2ssa-fixup-uses-isdefined.jl calls Compiler.fixup_uses! directly. P3: dead code." },
  { id := "compiler-slot2ssa-catch-loop-header", juliaFile := s2s,
    juliaFns := ["construct_ssa!(ci::CodeInfo, ir::IRCode, sv::OptimizationState, domtree::DomTree, defuses::Vector{SlotInfo}, 𝕃ₒ::AbstractLattice)"],
    statement := "Pruned SSA has no dead phi nodes: for every input of construct_ssa! (as slot2reg calls it) where every block has an inference state, every slot is Union{} or surely defined at each block entry, and no statement contains @isdefined, every phi node it inserts with an incoming edge is an operand of some statement or new node of its result.",
    source := "comment Compiler/src/ssair/slot2ssa.jl:495-497 (pruning prevents dead phi nodes); the renaming makes each read at a block entry refer to the block's phi",
    status := .refuted, prop := ``PhisUsed, thm := some ``phisUsed_refuted,
    issue := "none found (queries: catch loop; PhiC; phic; upsilon; catch segfault; catch while; try catch while; catch miscompile; slot2ssa catch; while loop in catch segfault; catch while loop; PhiCNode loop; catch block loop header; phic back edge; while catch wrong result; segfault catch while; upsilon loop catch; prs: catch while loop, PhiC loop catch, catch block loop); related #57393, #28224",
    notes := "Counterexample: the input of `function h3(c); x = 0; try; x = 1; c[] == 0 && error(\"e\"); catch; while c[] < 3; c[] += 1; x += 1; end; end; return x; end`. The catch block is the while loop's header, so it gets a PhiC node and a phi node for x (and for c); the renaming overwrites the phi with the PhiC (Compiler/src/ssair/slot2ssa.jl:709-715), so both phis are dead and the loop reads the value from the try. The model's new nodes equal the pinned Julia's. User-visible: a function of this shape returns 1 instead of 4 on the pinned Julia, nightly 290d5bb5f5, 1.13.3, 1.12.7 and 1.11.9 (4 on 1.10.12, whose catch block starts with a :leave), and segfaults when the local is read through a Ref argument." }
]

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
