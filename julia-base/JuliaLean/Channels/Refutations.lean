import JuliaLean.Channels.Props

/-! Reachability helpers and the counterexample for the refuted `Channel`
property; it matches `repro/channels-isready-buffered-stored.jl`. -/

namespace JuliaLean.Channels

theorem Reach.trans {a b c : St} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  induction h2 with
  | refl => exact h1
  | step i _ hs ih => exact Reach.step i ih hs

/-- Every schedule run by `runSched` is an interleaving the scheduler may
choose. -/
theorem reach_runSched (s : St) (l : List Nat) : Reach s (runSched s l) := by
  induction l generalizing s with
  | nil => exact Reach.refl s
  | cons i is ih =>
    cases h : stepTask s i with
    | none =>
      have e : runSched s (i :: is) = runSched s is := by simp [runSched, h]
      rw [e]; exact ih s
    | some s' =>
      have e : runSched s (i :: is) = runSched s' is := by simp [runSched, h]
      rw [e]; exact (Reach.step i (Reach.refl s) h).trans (ih s')

/-- `Channel(1)`: task 0 runs `put!(c, 1)`; task 1 runs `put!(c, 2)` and blocks
on the full buffer; task 2 runs `take!(c)`, which removes 1 and wakes task 1
without running it. Now `n_avail(c) == 1` (so `isready(c)`) but the buffer is
empty. -/
theorem isready_buffered_cex :
    (runSched (init 1 [.put 1, .put 2, .take]) [0, 0, 1, 1, 2]).ch.nAvail = 1 ∧
    (runSched (init 1 [.put 1, .put 2, .take]) [0, 0, 1, 1, 2]).ch.data = [] := by
  decide

theorem isreadyBufferedStored_refuted : ¬ IsreadyBufferedStored := by
  intro h
  have hc := isready_buffered_cex
  have := h 1 _ _ (reach_runSched _ [0, 0, 1, 1, 2]) (by decide) (by rw [hc.1]; decide)
  exact this hc.2

end JuliaLean.Channels
