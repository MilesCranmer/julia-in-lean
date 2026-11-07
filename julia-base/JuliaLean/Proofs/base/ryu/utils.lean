import JuliaLean.base.ryu.utils
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.ryu.utils

open JuliaLean JuliaLean.Registry JuliaLean.base.ryu.Ryu

def RyuLookupInBounds : Prop :=
  ∀ (T : FT) (i : Int),
    (∃ value, pow5invsplit_lookup T i = some value) ∧
    (∃ value, pow5split_lookup T i = some value)

theorem ryuLookupInBounds_refuted : ¬ RyuLookupInBounds := by
  intro h
  obtain ⟨value, hv⟩ := (h .f64 (-1)).1
  simp [pow5invsplit_lookup] at hv

def entries : List Entry := [
  { id := "memsafety-ryu-lookup-index", juliaFile := "base/ryu/utils.jl"
    juliaFns := ["pow5invsplit_lookup", "pow5split_lookup"]
    statement := "Every index accepted by the documented Ryu lookup helpers selects an element of the generated tuple."
    source := "base/ryu/utils.jl:286-325 (lookup docstrings state no index precondition)"
    status := .refuted, prop := ``RyuLookupInBounds, thm := some ``ryuLookupInBounds_refuted
    issue := "none found (queries: pow5invsplit_lookup bounds; Ryu lookup negative index; PRs same)"
    notes := "i=-1 computes tuple index zero in both helpers; forced bounds checks reproduce on release and nightly." }
]

end JuliaLean.Proofs.base.ryu.utils
