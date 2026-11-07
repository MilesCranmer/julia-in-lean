import JuliaLean.base.terminfo
import JuliaLean.Proofs.base.coreio.showSupport

namespace JuliaLean.ShowCov.TermInfo

open JuliaLean.ShowCov

theorem readExact_short (r : Rd) (nb : Nat) (h : r.rest.length < nb) :
    readExact r nb = .error .eofError := by
  simp [readExact, Nat.not_le_of_gt h]

theorem readExact_length (r : Rd) (nb : Nat) (h : nb ≤ r.rest.length) :
    (readExact r nb).map (fun result => result.1.length) = .ok nb := by
  simp [readExact, h, Except.map, List.length_take, Nat.min_eq_left h]

theorem extendedNamesOffset_no_values (indices : List Int) :
    extendedNamesOffset indices [] = 0 := by
  simp [extendedNamesOffset]

end JuliaLean.ShowCov.TermInfo
