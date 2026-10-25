import JuliaLean.IOBuffers.InvProofsCtor
import JuliaLean.IOBuffers.InvProofsOps

/-!
Every reachable buffer satisfies `Inv` (`reachable_inv`), so the observers agree
(`invariantHolds`), and no operation on it accesses memory outside `data` (`noOutOfBounds`).
-/

namespace JuliaLean.IOBuffers

open JuliaLean

namespace InvP

theorem finalState_sinv : ∀ (ops : List Op) (s : IOBuf) (K : Int), SInv s K →
    (∀ o ∈ ops, Op.ok o) → K + ((ops.map Op.weight).sum : Nat) ≤ 2 ^ 61 →
    SInv (finalState ops s) (K + ((ops.map Op.weight).sum : Nat))
  | [], s, K, h, _, _ => by
    have e : K + ((([] : List Op).map Op.weight).sum : Nat) = K := by
      simp only [List.map_nil, List.sum_nil]; omega
    rw [e]; exact h
  | o :: os, s, K, h, ho, hK => by
    have hsum : ((o :: os).map Op.weight).sum = o.weight + (os.map Op.weight).sum := by
      simp only [List.map_cons, List.sum_cons]
    rw [hsum] at hK ⊢
    have hspec := runOp_spec o (ho o (List.mem_cons_self ..)) h (by omega)
    have key : ∀ s', SInv s' (K + o.weight) →
        SInv (finalState os s') (K + ↑(o.weight + (os.map Op.weight).sum)) := by
      intro s' hs'
      have e : K + ↑(o.weight + (os.map Op.weight).sum) =
          K + ↑o.weight + ↑((os.map Op.weight).sum) := by omega
      rw [e]
      exact finalState_sinv os s' _ hs' (fun o' h' => ho o' (List.mem_cons_of_mem _ h'))
        (by omega)
    rw [finalState.eq_2]
    unfold Spec at hspec
    split
    · next a s' heq =>
      have heq' : runOp o s = .ok a s' := heq
      rw [heq'] at hspec
      exact key s' hspec
    · next e s' heq =>
      have heq' : runOp o s = .error e s' := heq
      rw [heq'] at hspec
      exact key s' hspec.2

theorem reachable_sinv {io : IOBuf} (hr : Reachable io) : SInv io (2 ^ 61) := by
  obtain ⟨c, ops, io0, hc, hb, ho, hw, he⟩ := hr
  subst he
  have hw' : (((ops.map Op.weight).sum : Nat) : Int) ≤ 2 ^ 60 := by
    unfold bound at hw; omega
  exact (finalState_sinv ops io0 _ (ctor_sinv hc hb) ho (by omega)).mono (by omega)

/-- `m` started in `s` never throws `IOErr.outOfBounds`. -/
abbrev Safe {α} (m : M α) (s : IOBuf) : Prop := Spec m s (fun _ _ => True) (fun e _ => NotOOB e)

theorem Safe.then {α} {m : M α} {s : IOBuf} {Q : α → IOBuf → Prop} (hm : Safe m s)
    (hq : ∀ a s', Q a s') : Spec m s Q (fun e _ => NotOOB e) :=
  hm.mono (fun a s' _ => hq a s') (fun _ _ x => x)

theorem compact_safe (s : IOBuf) : Safe compact s := by
  unfold compact
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure]
  refine spec_lift_of (fun ⟨a, b⟩ _ => ?_) (fun _ he => noob_getUsedSpan he)
  dsimp only
  split
  · trivial
  · exact spec_lift_of (fun _ _ => trivial) (fun _ he => noob_copyto he)

theorem resize_safe (s : IOBuf) (n : I) (exact : Bool) : Safe (resize n exact) s := by
  unfold resize
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure]
  generalize (if exact = true then n else imin s.maxsize (overallocation n)) = ns
  refine spec_lift_of (fun ⟨a, b⟩ _ => ?_) (fun _ he => noob_getUsedSpan he)
  dsimp only
  refine spec_lift_of (fun _ _ => ?_) (fun _ he => noob_similarData he)
  split
  · trivial
  · split
    · trivial
    · exact spec_lift_of (fun _ _ => trivial) (fun _ he => noob_copyto he)

theorem truncate_safe (s : IOBuf) (n : I) : Safe (truncate n) s := by
  unfold truncate
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure, spec_discard, throwArg,
    spec_throw]
  have tail : ∀ s1 : IOBuf, Spec (resize (n + getOffset s1) false) s1 (fun _ s2 =>
      Spec (lift (fillZero s2.data (s2.size + i 1) (imin (i ↑s2.data.length) (n + getOffset s2))))
        s2 (fun _ _ => True) (fun e _ => NotOOB e)) (fun e _ => NotOOB e) := fun s1 =>
    (resize_safe s1 _ _).then
      (fun _ _ => spec_lift_of (fun _ _ => trivial) (fun _ he => noob_fillZero he))
  repeat' split
  all_goals first
    | trivial
    | exact noob_jl _
    | exact spec_lift_of (fun _ _ => trivial) (fun _ he => noob_similarData he)
    | exact tail _
    | exact (compact_safe _).then (fun _ s1 => tail s1)

theorem resultOf_ne_oob {α} {m : M α} {s : IOBuf} {Q : α → IOBuf → Prop}
    {E : IOErr → IOBuf → Prop} (h : Spec m s Q E) (hE : ∀ e s', E e s' → NotOOB e) :
    resultOf m s ≠ .error .outOfBounds := by
  unfold resultOf
  unfold Spec at h
  show (match m s with | .ok a _ => (.ok a : Except IOErr α) | .error e _ => .error e) ≠ _
  revert h
  cases m s with
  | ok a s' => intro _ hc; cases hc
  | error e s' => intro he hc; cases hc; exact hE _ _ he rfl

theorem weight_or_truncate (o : Op) (ho : o.ok) :
    o.weight ≤ 2 ^ 60 ∨ ∃ n, o = .truncate n := by
  cases o with
  | writeBytes bs => exact .inl ho
  | truncate n => exact .inr ⟨n, rfl⟩
  | _ => exact .inl (by simp [Op.weight])

end InvP

open InvP

theorem reachable_inv : ∀ io, Reachable io → Inv io :=
  fun _ hr => (reachable_sinv hr).toInv (Int.le_refl _)

theorem invariantHolds : InvariantHolds :=
  fun io hr => consistent_of_inv (reachable_inv io hr)

theorem noOutOfBounds : NoOutOfBounds := by
  intro io hr o ho
  have hs := reachable_sinv hr
  rcases weight_or_truncate o ho with hw | ⟨n, rfl⟩
  · exact resultOf_ne_oob (runOp_spec o ho hs (by omega)) (fun _ _ x => x.1)
  · refine resultOf_ne_oob (Q := fun _ _ => True) (E := fun e _ => NotOOB e) ?_ (fun _ _ x => x)
    simp only [runOp, spec_bind, spec_pure]
    exact (truncate_safe io (i n)).then (fun _ _ => trivial)

end JuliaLean.IOBuffers
