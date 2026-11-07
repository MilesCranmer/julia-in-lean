import JuliaLean.base.cpuid
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.cpuid

open JuliaLean JuliaLean.base.cpuid JuliaLean.Registry

/-- Finite feature sets at the source Set primitive boundary. Membership and
subset use UInt32 feature identities; no legacy ISA values are converted. -/
private def featureSetOps : SetOps (List U32) U32 where
  empty := []
  push := fun values feature => if values.contains feature then values else feature :: values
  contains := List.contains
  subset := fun left right => left.all right.contains
  properSubset := fun left right => left.all right.contains && !(right.all left.contains)
  elements := id

/-- Incomparability must be transitive for a strict weak ordering. -/
def IsaIslessStrictWeak : Prop :=
  ∀ x y z : ISA32 (List U32),
    islessISA featureSetOps x y = false → islessISA featureSetOps y x = false →
    islessISA featureSetOps y z = false → islessISA featureSetOps z y = false →
    islessISA featureSetOps x z = false

theorem isaIslessStrictWeak_refuted : ¬ IsaIslessStrictWeak := by
  intro promised
  have bad := promised ⟨[JInt.lit .u32 1]⟩ ⟨[JInt.lit .u32 3]⟩
    ⟨[JInt.lit .u32 1, JInt.lit .u32 2]⟩
    (by decide) (by decide) (by decide) (by decide)
  revert bad
  decide

def entries : List Entry := [
  { id := "runtimecov-isa-isless-order", juliaFile := "base/cpuid.jl",
    juliaFns := ["isless(::ISA, ::ISA)"],
    statement := "isless on ISA values is a strict weak order (incomparability is transitive).",
    source := "base/cpuid.jl:20-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .refuted, prop := ``IsaIslessStrictWeak, thm := some ``isaIslessStrictWeak_refuted,
    notes := "The real leISA/ltISA/islessISA source operations use finite UInt32 feature-set membership. The counterexample is {1}, {3}, {1,2}; it does not use the legacy unbounded-Nat ISA model.",
    issue := "none found (queries: CPUID ISA isless; ISA partial order isless)" }
]

end JuliaLean.Proofs.base.cpuid
