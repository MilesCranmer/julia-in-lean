import JuliaLean.ConcurrencyCov.Locks

/-! Properties of the spin-lock methods in `base/locks-mt.jl`. -/

namespace JuliaLean.ConcurrencyCov.Locks

open JuliaLean.ConcurrencyCov

/-- Both constructors start unlocked; `trylock` disables finalizers before the
atomic swap and restores them on failure; `unlock` rejects an unmatched release,
restores finalizers after a successful swap, and `lock` retries while owned
(`base/locks-mt.jl:46-115`). -/
def SpinLockSpec : Prop :=
  spinLock = ⟨0, fun _ => 0⟩ ∧
  paddedSpinLock = ⟨0, fun _ => 0⟩ ∧
  (∀ l, spinIslocked l = decide (l.owned ≠ 0)) ∧
  (∀ l, spinAssertHavelock l = if spinIslocked l then .ok () else .error .concurrencyViolation) ∧
  (∀ t l, spinTrylock t l =
    if l.owned = 0 then (true, ⟨1, upd l.fin t (l.fin t + 1)⟩) else (false, l)) ∧
  (∀ t l, spinLockStep t l =
    match spinTrylock t l with | (true, l') => some l' | (false, _) => none) ∧
  (∀ t l, spinUnlock t l =
    if l.owned = 0 then .error (.errorException "unlock count must match lock count")
    else .ok ⟨0, upd l.fin t (l.fin t - 1)⟩)

theorem spinLockSpec_proven : SpinLockSpec := by
  refine ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, ?_,
    fun _ _ => rfl, fun _ _ => rfl⟩
  intro t l
  by_cases h : l.owned = 0 <;> simp [spinTrylock, h]

end JuliaLean.ConcurrencyCov.Locks
