import JuliaLean.base.scope

namespace JuliaLean.MiscCov.Scope

variable {V : Type}

/-- The value a list of pairs binds a key to, applied left to right: the last pair
for the key wins; `none` if no pair names the key. -/
def lastFor (k : Nat) : List (Key V × V) → M (Option V)
  | [] => pure none
  | (key, v) :: rest => do
    let w ← key.conv v
    let r ← lastFor k rest
    pure (if r.isSome then r else if key.id == k then some w else none)

/-- A scope built from a parent and pairs looks a key up in the last pair that
binds it, else in the parent; a failed `convert` of any value is thrown; the
other constructors return their argument / `nothing`. -/
def Contract : Prop :=
  (∀ s : Scope V, ofScope s = s) ∧ (@ofNothing V = none) ∧
  (∀ (parent : Option (Scope V)) (key : Key V) (value : V),
    mk parent key value = (key.conv value).map fun w =>
      ⟨(key.id, w) :: (parent.map (·.values)).getD []⟩) ∧
  (∀ (parent : Option (Scope V)) (p1 : Key V × V) (ps : List (Key V × V)) (s : Scope V) (k : Nat),
    mkPairs parent p1 ps = .ok s →
      ∃ last, lastFor k (p1 :: ps) = .ok last ∧
        s.values.get k = (if last.isSome then last else (parent.bind (·.values.get k))))

theorem lastFor_cons (k : Nat) (key : Key V) (v w : V) (rest : List (Key V × V)) (h : key.conv v = .ok w) :
    lastFor k ((key, v) :: rest) = (lastFor k rest).map
      (fun r => if r.isSome then r else if key.id == k then some w else none) := by
  simp only [lastFor, h, bind, Except.bind, pure, Except.pure]
  cases lastFor k rest <;> rfl

theorem mkPairs_spec (k : Nat) : ∀ (ps : List (Key V × V)) (parent : Option (Scope V)) (p1 : Key V × V)
    (s : Scope V), mkPairs parent p1 ps = .ok s →
      ∃ last, lastFor k (p1 :: ps) = .ok last ∧
        s.values.get k = (if last.isSome then last else (parent.bind (·.values.get k))) := by
  intro ps
  induction ps with
  | nil =>
    intro parent p1 s h
    obtain ⟨key, v⟩ := p1
    simp only [mkPairs, mkPair, mk, bind, Except.bind, pure, Except.pure] at h
    cases hc : key.conv v with
    | error e => rw [hc] at h; cases h
    | ok w =>
      rw [hc] at h
      refine ⟨if key.id == k then some w else none, ?_, ?_⟩
      · simp [lastFor, hc, bind, Except.bind, pure, Except.pure]
      · cases parent <;> simp at h <;> subst h <;>
          by_cases hk : key.id = k <;> simp [Storage.get, List.find?, hk]
  | cons p2 ps ih =>
    intro parent p1 s h
    obtain ⟨key, v⟩ := p1
    simp only [mkPairs, mk, bind, Except.bind, pure, Except.pure] at h
    cases hc : key.conv v with
    | error e => rw [hc] at h; cases h
    | ok w =>
      rw [hc] at h
      have h' : mkPairs (some ⟨(key.id, w) :: (parent.map (·.values)).getD []⟩) p2 ps = .ok s := by
        cases parent <;> exact h
      obtain ⟨last, hl, hs⟩ := ih _ _ _ h'
      refine ⟨if last.isSome then last else if key.id == k then some w else none, ?_, ?_⟩
      · rw [lastFor_cons k key v w _ hc, hl]; rfl
      · rw [hs]
        cases last with
        | some x => simp
        | none =>
          cases parent <;> by_cases hk : key.id = k <;> simp [Storage.get, List.find?, hk]

theorem contract_proven : @Contract V := by
  refine ⟨fun _ => rfl, rfl, ?_, fun parent p1 ps s k h => mkPairs_spec k ps parent p1 s h⟩
  intro parent key value
  simp only [mk, bind, Except.bind, pure, Except.pure]
  cases key.conv value <;> cases parent <;> rfl

end JuliaLean.MiscCov.Scope

namespace JuliaLean.MiscCov

def ScopeContractClosed : Prop := @Scope.Contract Unit
theorem scopeContractClosed_proven : ScopeContractClosed := Scope.contract_proven

end JuliaLean.MiscCov
