import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.cartesian.LegacyProofs
import JuliaLean.Proofs.base.cartesian.Refutations
import JuliaLean.Proofs.base.cartesian.RowEntries

namespace JuliaLean.ExprReflect

open JuliaLean.Registry

def entriesCartesian : List Entry := [
  { id := "exprreflect-nref", juliaFile := "base/cartesian.jl"
    juliaFns := ["Base.Cartesian.@nref"]
    statement := "For every natural dimension count N, @nref produces A[i_1,...,i_N] in increasing dimension order."
    source := "base/cartesian.jl:73-88", status := .proven
    prop := ``NrefExact, thm := some ``nrefExact_proven },
  { id := "exprreflect-ntuple", juliaFile := "base/cartesian.jl"
    juliaFns := ["Base.Cartesian.@ntuple"]
    statement := "For every natural dimension count N, @ntuple produces (i_1,...,i_N) in increasing dimension order."
    source := "base/cartesian.jl:222-231", status := .proven
    prop := ``NtupleExact, thm := some ``ntupleExact_proven },
  { id := "exprreflect-nloops-atomic-body", juliaFile := "base/cartesian.jl"
    juliaFns := ["Base.Cartesian.@nloops", "Base.Cartesian._nloops"]
    statement := "For every natural dimension count and every body expression, @nloops expands to the documented normalized loop nest."
    source := "base/cartesian.jl:9-38", status := .refuted
    prop := ``CartesianLoopsTotal, thm := some ``cartesianLoopsTotal_refuted
    issue := "none found (queries: Cartesian @nloops body MethodError)"
    notes := "An atomic body such as the symbol body dispatches to no _nloops method because args is restricted to Expr..., although symbols and literals are valid macro body expressions." },
  { id := "exprreflect-nloops-compound", juliaFile := "base/cartesian.jl"
    juliaFns := ["Base.Cartesian.@nloops", "Base.Cartesian._nloops"]
    statement := "For every natural dimension count and compound body, @nloops expands to the documented normalized loop nest with dimension N outermost."
    source := "base/cartesian.jl:25-33,38-70", status := .proven
    prop := ``CartesianLoopsCompoundExact, thm := some ``cartesianLoopsCompoundExact_proven },

  -- Whole-Base source-body coverage families.,
  { id := "exprreflect-cartesian-macro-bodies", juliaFile := "base/cartesian.jl"
    juliaFns := ["@nloops", "_nloops", "@nref", "@ncall", "@ncallkw", "@nexprs", "@nextract", "@nall", "@nany", "@ntuple", "@nif"]
    statement := "Cartesian macros generate exactly one ordered dimension contribution per requested dimension, with the documented loop nesting, calls, tuple, extraction, Boolean, and conditional shapes."
    source := "base/cartesian.jl:9-259", status := .proven
    prop := ``CartesianMacroBodies, thm := some ``cartesianMacroBodies_proven },
  { id := "exprreflect-cartesian-substitution-bodies", juliaFile := "base/cartesian.jl"
    juliaFns := ["inlineanonymous", "LReplace", "lreplace", "lreplace!", "lreplace_string!", "poplinenum", "exprresolve_arith", "exprresolve_conditional", "exprresolve"]
    statement := "Cartesian substitution replaces free dimension variables and indexed symbol suffixes across quote/escape boundaries, removes singleton line blocks, and resolves supported arithmetic and conditionals."
    source := "base/cartesian.jl:261-473", status := .proven
    prop := ``CartesianSubstitutionBodies, thm := some ``cartesianSubstitutionBodies_proven },
] ++ cartesianRowEntries

end JuliaLean.ExprReflect
