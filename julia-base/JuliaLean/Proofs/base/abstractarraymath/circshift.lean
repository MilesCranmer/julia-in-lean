import JuliaLean.Proofs.base.abstractarraymath.cartesian_contracts
import JuliaLean.Proofs.base.multidimensional.circshift

namespace JuliaLean.Multidim

theorem circshiftFormula : CircshiftFormula := by
  intro sz shifts src hsz hlen
  unfold circshift
  by_cases hz : sz.any (· == 0) = true
  · rw [if_pos hz]
    exact ⟨_, rfl, fun J hJ => (empty_box sz J hz hJ).elim⟩
  · rw [if_neg hz]
    have hpos : ∀ n ∈ sz, 0 < n := by
      intro n hn
      refine Nat.pos_of_ne_zero fun h0 => hz (List.any_eq_true.mpr ⟨n, hn, by simp [h0]⟩)
    have hfill : fillToLength shifts sz.length =
        .ok (shifts ++ List.replicate (sz.length - shifts.length) 0) := by
      unfold fillToLength; rw [if_neg (by omega)]
    rw [hfill]
    have hshlen : (shifts ++ List.replicate (sz.length - shifts.length) 0).length = sz.length := by
      simp; omega
    obtain ⟨d', hrun, hJ⟩ := runBlocks_spec (oneAxes sz) (oneAxes sz) src
      (fun J => some (src (circF sz (shifts ++ List.replicate (sz.length - shifts.length) 0) J)))
      (fun b J => InBlock b.1 J)
      (circBlocks sz (shifts ++ List.replicate (sz.length - shifts.length) 0))
      (fun b hb dest => block_step sz _ b.1 b.2
        (blocks_ok sz _ hshlen hpos b hb) hsz dest src)
      (fun _ => none)
    exact ⟨d', hrun, fun J hJin => (hJ J).2 (cover sz _ J hshlen hpos hJin)⟩

end JuliaLean.Multidim
