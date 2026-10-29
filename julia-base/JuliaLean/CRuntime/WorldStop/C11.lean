import JuliaLean.CRuntime.WorldStop.Witness
import JuliaLean.CRuntime.WorldStop.C11Certificate

namespace JuliaLean.CRuntime.WorldStop

open Memory

/-- Initialization, public API entries, suspension, GC, resume and the
cached-pointer suffix share one globally Defined candidate. -/
theorem canonicalOutcome_C11 : canonicalOutcome.candidate.Defined := by
  rw [canonicalCandidate_matchesSource]
  exact chronologicalCertificate_defined canonicalCandidate canonicalCandidate_certificate

theorem canonicalOutcome_defined : canonicalOutcome.candidate.defined = true :=
  candidate_defined_true _ canonicalOutcome_C11

end JuliaLean.CRuntime.WorldStop
