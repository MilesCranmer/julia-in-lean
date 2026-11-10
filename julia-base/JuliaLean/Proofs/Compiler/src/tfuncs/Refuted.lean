import JuliaLean.Proofs.Compiler.src.tfuncs.Common

/-!
Soundness counterexamples for `builtin_tfunction` and `tuple_tfunc`, each confirmed on the
pinned Julia by a reproducer in `repro/`.

The third soundness bug of this area, `subtype_tfunc` returning `Const(false)` for a left side
that may be `Union{}` (`bugs/compiler-tfuncs-subtype-bottom-lhs.yaml`), has no Lean refutation:
every counterexample needs `jl_subtype` or `jl_isa` on a `Union` or `UnionAll`, and those paths of
the subtyping model run `while` loops, which are `partial` and so opaque to the kernel.
-/

namespace JuliaLean.Proofs.Compiler.Tfuncs

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

set_option maxRecDepth 100000

/-! ## `<:` with a left side that may be `Union{}` -/

/-- Soundness of `builtin_tfunction(<:, ...)` on `typeinf_lattice`. Open in Lean (see the module
comment); refuted on the pinned Julia by `repro/compiler-tfuncs-subtype-bottom-lhs.jl`. -/
def SubtypeTfuncSound : Prop := TfuncSound typeinfLattice "<:"

/-! ## `getfield` with a trailing `Vararg` -/

/-- Soundness of `builtin_tfunction(getfield, ...)` on `typeinf_lattice`. -/
def GetfieldTfuncSound : Prop := TfuncSound typeinfLattice "getfield"

def tupInt : Val := .datatype tupleName [longType]

/-- `[Tuple{Int64}, Const(1), Const(false), Vararg{Bool}]`. -/
def getfieldVaArgs : List LElt :=
  [.ty tupInt, .const (.long 1), .const (boolVal false), .ty (.vararg (some boolTy) none)]

theorem getfield_cx_args :
    (argsIn 20 cxE [.imm tupInt [.long 1], .long 1, boolVal false] getfieldVaArgs).run 0 =
      .ok (true, 0) :=
  andM_ok (by rfl) (andM_ok (inGamma_const_long 18 cxE 1 0)
    (andM_ok (inGamma_const_bool 18 cxE false 0) rfl))

theorem getfield_cx_rt :
    (builtinRT 20 cxE "getfield" [.imm tupInt [.long 1], .long 1, boolVal false]).run 0 =
      .ok (.long 1, 0) := by
  rfl

theorem getfield_cx_tfunc :
    (builtinTfunction 20 cxT typeinfLattice "getfield" getfieldVaArgs).run 0 = .ok (.ty .bottom, 0) := by
  rfl

/-- Counterexample: `getfield(x, 1, false, b...)` with `x::Tuple{Int64}` and `b::Vararg{Bool}`.
`builtin_tfunction` pads the trailing `Vararg` up to the maximum arity 4
(`Compiler/src/tfuncs.jl:3306-3322`), so it calls the 4-argument `getfield_tfunc`, which reads
`false` as the memory order and returns `Union{}` because a `Bool` does not intersect `Symbol`
(`Compiler/src/tfuncs.jl:1176-1177`). With `b` empty the call is the 3-argument
`getfield(x, 1, false)`, which returns `x[1]`. -/
theorem getfieldTfuncSound_refuted : ¬ GetfieldTfuncSound := by
  intro h
  have := h 20 cxT getfieldVaArgs [.imm tupInt [.long 1], .long 1, boolVal false]
    ⟨0, 0, getfield_cx_args⟩ 0 (.long 1) 0 getfield_cx_rt 0 _ 0 getfield_cx_tfunc 0 false 0 rfl
  exact Bool.false_ne_true this

/-! ## `tuple` with a `Vararg{Type{T}}` argument -/

/-- The parameters `tuple_tfunc` builds are types that tuple values can have: no parameter is a
`Type{T}` (or `TypeEgal{T}`), bare or as the element type of a trailing `Vararg`. No value's
type is `Type{T}`, so a tuple type with such a parameter has no instances; the source comment says
these parameters must be turned into valid ones (`Compiler/src/tfuncs.jl:2334-2337`). -/
def TupleParamsHaveInstances : Prop :=
  ∀ n E L argtypes, Returns (tupleTfuncParams n E L argtypes) fun r =>
    ∀ ps anyinfo argtypes', r = some (ps, anyinfo, argtypes') →
      ps.all (fun p => !isType (unwrapva p)) = true

def vaTypeInt : Val := .vararg (some (.typeeq longType)) none

theorem tuple_cx_params :
    (tupleTfuncParams 20 cxE typeinfLattice [.ty vaTypeInt]).run 0 =
      .ok (some ([vaTypeInt], false, [.ty vaTypeInt]), 0) := by
  rfl

/-- Counterexample: `tuple(v...)` with `v::Vector{Type{Int64}}` has the argument types
`[Vararg{Type{Int64}}]`. The loop turns a `Type{T}` argument into `DataType` or `Type`, but passes a
`Vararg` through unchanged: line 2333 keeps a `Vararg` as it is, and the checks at 2338-2360 test
the `Vararg` itself, which is neither a `Type{T}` nor a kind (`Compiler/src/tfuncs.jl`). So the
result is `Tuple{Vararg{Type{Int64}}}`. The value `(Int64, Int64)` is a `Tuple{DataType, DataType}`. -/
theorem tupleParamsHaveInstances_refuted : ¬ TupleParamsHaveInstances := by
  intro h
  have := h 20 cxE typeinfLattice [.ty vaTypeInt] 0 _ 0 tuple_cx_params _ _ _ rfl
  exact Bool.false_ne_true this

end JuliaLean.Proofs.Compiler.Tfuncs
