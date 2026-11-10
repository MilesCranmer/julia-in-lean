import JuliaLean.Compiler.src.reinfer

/-!
Proof helpers for the models of `Compiler/src/reinfer.jl` and `Compiler/src/bindinginvalidations.jl`:
reduction lemmas for `Except` and `StateT` over `Except` (scoped simp lemmas), the `for`-loop
lemmas for loops whose steps either continue or stop with an early result, and the specification
of `eachinterference` and `method_in_interferences`. No registry entries.
-/

namespace JuliaLean.Proofs.Compiler.src.reinfer.Monad

open JuliaLean.Compiler.CICache JuliaLean.Compiler.Reinfer
open JuliaLean.C (Val)

@[scoped simp] theorem ok_bind {ε α β} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl
@[scoped simp] theorem error_bind {ε α β} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl
@[scoped simp] theorem ok_bind' {ε α β} (x : α) (f : α → Except ε β) : Except.bind (Except.ok x) f = f x := rfl
@[scoped simp] theorem error_bind' {ε α β} (e : ε) (f : α → Except ε β) : Except.bind (Except.error e) f = .error e := rfl
@[scoped simp] theorem pure_ok {ε α} (x : α) : (pure x : Except ε α) = .ok x := rfl

theorem method_uid (H : Heap) (u : Nat) (x : MethodR) (h : H.method u = .ok x) : x.uid = u := by
  unfold Heap.method at h
  split at h
  · rename_i m hm
    cases h
    have := Array.find?_some hm
    simpa using this
  · cases h

theorem ei_loop (H : Heap) (cutoff : Nat) (f : Nat → MethodR) :
    ∀ (ks : List Nat) (acc : Array MethodR), (∀ k ∈ ks, H.method k = .ok (f k)) →
    forIn (m := Except String) ks acc (fun k r => do
        let im ← H.method k
        if cutoff < im.primaryWorld then Except.ok (ForInStep.done r) else Except.ok (ForInStep.yield (r.push im)))
      = .ok (acc ++ ((ks.map f).takeWhile (fun x => decide (x.primaryWorld ≤ cutoff))).toArray) := by
  intro ks
  induction ks with
  | nil => intro acc _; simp
  | cons k ks ih =>
    intro acc hk
    simp only [List.forIn_cons]
    rw [hk k (by simp)]
    by_cases hc : cutoff < (f k).primaryWorld
    · simp [hc]
    · simp only [ok_bind, ite_eq_right_iff, if_neg hc, pure_ok]
      rw [ih _ (fun k h => hk k (by simp [h]))]
      have : (f k).primaryWorld ≤ cutoff := by omega
      simp [List.takeWhile_cons, this]

theorem ei_spec (H : Heap) (m : MethodR) (cutoff : Nat) (f : Nat → MethodR)
    (hf : ∀ k ∈ m.interferences, H.method k = .ok (f k)) :
    eachinterference H m cutoff =
      .ok ((m.interferences.map f).takeWhile (fun x => decide (x.primaryWorld ≤ cutoff))) := by
  unfold eachinterference
  simp only [pure_ok]
  rw [ei_loop H cutoff f _ _ hf]
  simp

theorem takeWhile_all {α} (p : α → Bool) : ∀ (l : List α), (∀ x ∈ l, p x = true) → l.takeWhile p = l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.takeWhile_cons, h x (by simp), if_true]
    rw [takeWhile_all p xs (fun y hy => h y (by simp [hy]))]

theorem mii_spec (H : Heap) (m2 m1 : MethodR)
    (hf : ∀ k ∈ m1.interferences, ∃ x, H.method k = .ok x ∧ x.primaryWorld ≤ typemaxUInt) :
    methodInInterferences H m2 m1 = .ok (decide (m2.uid ∈ m1.interferences)) := by
  classical
  let f : Nat → MethodR := fun k => match H.method k with | .ok x => x | .error _ => default
  have hf' : ∀ k ∈ m1.interferences, H.method k = .ok (f k) := by
    intro k hk; obtain ⟨x, hx, _⟩ := hf k hk; simp [f, hx]
  unfold methodInInterferences
  rw [ei_spec H m1 typemaxUInt f hf']
  simp only [ok_bind, pure_ok]
  congr 1
  have htw : (m1.interferences.map f).takeWhile (fun x => decide (x.primaryWorld ≤ typemaxUInt)) =
      m1.interferences.map f := by
    apply takeWhile_all
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨x, hx, hp⟩ := hf k hk
    simp [f, hx, hp]
  rw [htw]
  apply Bool.eq_iff_iff.2
  simp only [List.any_map, List.any_eq_true, Function.comp, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, he⟩
    rw [← he, method_uid H k (f k) (hf' k hk)]; exact hk
  · intro hk
    exact ⟨m2.uid, hk, method_uid H _ _ (hf' _ hk)⟩

theorem msr_asymm (H : Heap) (a b : MethodR) :
    methodMorespecificRecorded H a b = .ok true → methodMorespecificRecorded H b a = .ok false ∧ a.uid ≠ b.uid := by
  intro h
  unfold methodMorespecificRecorded at h ⊢
  by_cases hab : a.uid = b.uid
  · simp [hab] at h
  · have hba : ¬ b.uid = a.uid := fun e => hab e.symm
    simp only [hab, hba, beq_iff_eq, if_false] at h ⊢
    refine ⟨?_, hab⟩
    cases h1 : methodInInterferences H a b with
    | error e => simp [h1] at h
    | ok v1 =>
      cases h2 : methodInInterferences H b a with
      | error e => simp [h1, h2] at h; cases v1 <;> simp at h
      | ok v2 =>
        simp [h1, h2] at h
        cases v1 <;> cases v2 <;> simp at h <;> simp


macro "rinf_loopcase" : tactic => `(tactic| ((repeat' split) <;> intro hx <;>
  (try simp only [Except.ok.injEq, ForInStep.done.injEq, ForInStep.yield.injEq, reduceCtorEq] at hx) <;>
  (try cases hx) <;> simp_all))

abbrev St := Option Bool × Unit

/-- A loop whose steps either continue with no early result or stop with one: when it ends with
no early result, every step continued. -/
theorem forIn_none {α} (f : α → St → Except String (ForInStep St))
    (hy : ∀ x s', f x (none, ()) = .ok (.yield s') → s' = (none, ()))
    (hd : ∀ x s', f x (none, ()) = .ok (.done s') → s'.1 ≠ none) :
    ∀ (l : List α) (s : St), forIn l (none, ()) f = .ok s → s.1 = none →
      ∀ x ∈ l, f x (none, ()) = .ok (.yield (none, ()))
  | [], _, _, _ => by simp
  | x :: xs, s, h, hs => by
    simp only [List.forIn_cons] at h
    cases hx : f x (none, ()) with
    | error e => rw [hx] at h; cases h
    | ok r =>
      rw [hx] at h
      cases r with
      | done s' =>
        simp only [ok_bind] at h; cases h
        exact absurd hs (hd x _ hx)
      | yield s' =>
        have := hy x s' hx; subst this
        simp only [ok_bind] at h
        intro y hy'
        simp only [List.mem_cons] at hy'
        rcases hy' with rfl | hy'
        · exact hx
        · exact forIn_none f hy hd xs s h hs y hy'

/-- When such a loop ends with an early result, some step stopped with it. -/
theorem forIn_some {α} (f : α → St → Except String (ForInStep St))
    (hy : ∀ x s', f x (none, ()) = .ok (.yield s') → s' = (none, ())) :
    ∀ (l : List α) (s : St), forIn l (none, ()) f = .ok s → s.1 ≠ none →
      ∃ x ∈ l, f x (none, ()) = .ok (.done s)
  | [], s, h, hs => by simp at h; cases h; simp at hs
  | x :: xs, s, h, hs => by
    simp only [List.forIn_cons] at h
    cases hx : f x (none, ()) with
    | error e => rw [hx] at h; cases h
    | ok r =>
      rw [hx] at h
      cases r with
      | done s' =>
        simp only [ok_bind] at h; cases h
        exact ⟨x, by simp, hx⟩
      | yield s' =>
        have := hy x s' hx; subst this
        simp only [ok_bind] at h
        obtain ⟨y, hy', hf⟩ := forIn_some f hy xs s h hs
        exact ⟨y, by simp [hy'], hf⟩


/-- A loop whose step on each element either continues or stops with the same early result `b`,
by a test `q`: it stops with `b` exactly when some element passes the test. -/
theorem forIn_bool {α} (f : α → St → Except String (ForInStep St)) (q : α → Bool) (b : Bool)
    (hf : ∀ x, f x (none, ()) = .ok (if q x then .done (some b, ()) else .yield (none, ()))) :
    ∀ l : List α, forIn l (none, ()) f = .ok (if l.any q then (some b, ()) else (none, ()))
  | [] => by simp
  | x :: xs => by
    simp only [List.forIn_cons, hf x]
    by_cases hq : q x
    · simp [hq]
    · simp only [hq, Bool.false_eq_true, if_false, ok_bind]
      rw [forIn_bool f q b hf xs]
      simp [hq]

section
variable {σ ε α β : Type}
@[scoped simp] theorem lift_ok_bind (a : α) (f : α → StateT σ (Except ε) β) (s : σ) :
    (StateT.lift (Except.ok a) : StateT σ (Except ε) α).bind f s = f a s := rfl
@[scoped simp] theorem lift_err_bind (e : ε) (f : α → StateT σ (Except ε) β) (s : σ) :
    (StateT.lift (Except.error e) : StateT σ (Except ε) α).bind f s = Except.error e := rfl
@[scoped simp] theorem modifyGet_bind (g : σ → α × σ) (f : α → StateT σ (Except ε) β) (s : σ) :
    (StateT.modifyGet g : StateT σ (Except ε) α).bind f s = f (g s).1 (g s).2 := rfl
@[scoped simp] theorem stpure_app (a : α) (s : σ) : (StateT.pure a : StateT σ (Except ε) α) s = Except.ok (a, s) := rfl
@[scoped simp] theorem stpure_bind (a : α) (f : α → StateT σ (Except ε) β) (s : σ) :
    (StateT.pure a : StateT σ (Except ε) α).bind f s = f a s := rfl
@[scoped simp] theorem lift_throw_bind (e : String) (f : α → StateT σ (Except String) β) (s : σ) :
    (StateT.lift (throwThe String e) : StateT σ (Except String) α).bind f s = .error e := rfl
@[scoped simp] theorem get_bind (f : σ → StateT σ (Except ε) β) (s : σ) :
    (StateT.get : StateT σ (Except ε) σ).bind f s = f s s := rfl
@[scoped simp] theorem get_proj_bind {γ : Type} (p : σ → γ) (g : γ → StateT σ (Except ε) β) (s : σ) :
    ((StateT.get : StateT σ (Except ε) σ).bind (fun x => StateT.pure (p x))).bind g s = g (p s) s := rfl
theorem st_bind_assoc {γ : Type} (x : StateT σ (Except ε) α) (f : α → StateT σ (Except ε) β)
    (g : β → StateT σ (Except ε) γ) : (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  funext s
  simp only [StateT.bind, bind, Except.bind]
  cases x s with
  | error e => rfl
  | ok p => rfl
@[scoped simp] theorem st_throw_bind (e : String) (f : α → StateT σ (Except String) β) (s : σ) :
    (StateT.bind (throw e : StateT σ (Except String) α) f) s = Except.error e := rfl
@[scoped simp] theorem lift_throw (e : String) (s : σ) :
    (StateT.lift (throwThe String e) : StateT σ (Except String) α) s = .error e := rfl
end

macro "rinf_vmsimp2" " at " h:ident : tactic => `(tactic| simp only [Except.pure, ok_bind', StateT.bind, StateT.pure,
  StateT.modifyGet, StateT.lift, Except.bind, bind, pure, pure_ok, jlThrow, throw, throwThe,
  MonadExcept.throw, MonadExceptOf.throw] at $h:ident)

macro "rinf_vmsimp" " at " h:ident : tactic => `(tactic| simp only [getHeap, getWS, liftE, modifyHeap, modifyWS,
  emit, StateT.bind, StateT.lift, StateT.pure, StateT.modifyGet, StateT.get, bind, pure, pure_ok,
  ok_bind', get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet, assert',
  StateT.run] at $h:ident)

end JuliaLean.Proofs.Compiler.src.reinfer.Monad
