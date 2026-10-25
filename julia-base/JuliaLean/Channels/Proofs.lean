import JuliaLean.Channels.ProofsResults
import JuliaLean.Channels.ProofsReady
import JuliaLean.Channels.ProofsQueues
import JuliaLean.Channels.ProofsLedger
import JuliaLean.Channels.ProofsFit

namespace JuliaLean.Channels

 theorem inv_init : Inv sz ops (init sz ops) :=
  ⟨fitInv_init, queueInv_init sz ops, ledgerInv_init sz ops⟩

 theorem inv_step (h : Inv sz ops s) (hs : stepTask s i = some s') : Inv sz ops s' :=
  ⟨fitInv_step h.fit hs, queueInv_step h.queues h.fit hs,
    ledgerInv_step h.ledger h.fit h.queues hs⟩

 theorem inv_reach (h : Reach (init sz ops) s) : Inv sz ops s := by
  induction h with
  | refl => exact inv_init
  | step i _ hs ih => exact inv_step ih hs

 theorem putTakeConservation : PutTakeConservation := by
  intro sz ops s hr
  exact ledgerInv_conservation (inv_reach hr).ledger

 theorem bufferBound : BufferBound := by
  intro sz ops s hr
  exact (inv_reach hr).queues.buffer

 theorem fetchKeeps : FetchKeeps := by
  intro sz ops s s' i hr hop hs
  exact fetchKeeps_of_fit (inv_reach hr).fit hop hs

 theorem closeWakesWaiters : CloseWakesWaiters := by
  intro sz ops s hr hc
  exact closeWakesWaiters_of_queue (inv_reach hr).queues hc

 theorem takeClosedEmptyThrows : TakeClosedEmptyThrows := by
  intro sz ops s i _ hc hd ht
  exact takeClosedEmptyThrows_of_state hc hd ht

 theorem iterateEndsDrained : IterateEndsDrained := by
  intro sz ops s s' i hr hop hs hd
  exact iterateEndsDrained_of_inv (inv_reach hr).fit (inv_reach hr).queues hop hs hd

 theorem noLostWakeup : NoLostWakeup := by
  intro sz ops s hr
  exact noLostWakeup_of_queue (inv_reach hr).queues

 theorem isreadyUnbuffered : IsreadyUnbuffered := by
  intro ops s hr
  exact isreadyUnbuffered_of_inv (inv_reach hr).fit (inv_reach hr).queues

end JuliaLean.Channels
