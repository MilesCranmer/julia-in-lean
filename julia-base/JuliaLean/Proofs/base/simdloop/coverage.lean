import JuliaLean.base.simdloop
import JuliaLean.Proofs.base.generator.iterator_protocol
import JuliaLean.Registry.Types

/-!
# `@simd` syntax processing (`base/simdloop.jl`)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- The parser accepts exactly assignment/in iteration forms with a symbol;
body validation rejects nested break/continue/goto; a valid one-dimensional
loop compiles to the recorded variable, range, body and dependency flag; the
range helpers and both macros follow their source bodies. -/
def SimdLoopSemantics : Prop :=
  (∀ head var range, (head = "=" ∨ head = "in") →
    parseIterationSpace (.expr head [.symbol var, range]) = .ok (var, range)) ∧
  (∀ x, checkSimdBody x = if forbidden x then
    .error (.simdError "invalid control flow inside a @simd loop body") else .ok true) ∧
  (∀ (α : Type) (r : List α) j, simdOuterRange r = [0] ∧
    simdInnerLength r j = r.length) ∧
  (∀ (α : Type) (r : List α) j i value, r[i]? = some value →
    simdIndex r j i = .ok value) ∧
  (∀ var range body ivdep,
    forbidden (.expr "for" [.expr "=" [.symbol var, range], body]) = false →
    compileSimd (.expr "for" [.expr "=" [.symbol var, range], body]) ivdep =
      .ok { varName := var, range := range, body := body, ivdep := ivdep }) ∧
  (∀ loop, simdMacro loop = compileSimd loop none) ∧
  (∀ loop, simdIvdepMacro "ivdep" loop = compileSimd loop (some "julia.ivdep")) ∧
  (∀ tag loop, tag ≠ "ivdep" →
    simdIvdepMacro tag loop =
      .error (.simdError "Only ivdep is valid as the first argument to @simd"))

theorem simdLoopSemantics : SimdLoopSemantics := by
  refine ⟨?_, fun _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, ?_, ?_,
    fun _ => rfl, ?_, ?_⟩
  · intro head var range h
    rcases h with rfl | rfl <;> rfl
  · intro α r j i value h
    simp [simdIndex, h]
  · intro var range body ivdep h
    simp [compileSimd, checkSimdBody, h, parseIterationSpace]
    rfl
  · intro loop
    simp [simdIvdepMacro]
  · intro tag loop h
    simp [simdIvdepMacro, h]

end JuliaLean.IteratorsCov

namespace JuliaLean.IteratorsCov

open JuliaLean.Registry

/-- Registry entries for the four iterator implementation files. -/
def entries : List Entry := [
  { id := "iteratorscov-simdloop-semantics", juliaFile := "base/simdloop.jl"
    juliaFns := ["parse_iteration_space", "check_body!", "simd_outer_range", "simd_inner_length",
      "simd_index", "compile", "@simd"]
    statement := "The SIMD parser validates the loop shape, rejects nested forbidden control flow, constructs the documented indexed loop expansion, and accepts only the ivdep option."
    source := "@simd docstring and invariant; base/simdloop.jl:17-137"
    status := .proven, prop := ``SimdLoopSemantics, thm := some ``simdLoopSemantics }

]

end JuliaLean.IteratorsCov
