import JuliaLean.Platforms.Lemmas
import JuliaLean.VersionNumbers.Order

/-!
# Proofs about `platforms_match` and the comparison strategies
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (VersionNumber veq vless tupleCmp tupleCmp_cmp)

/-! ## `Except` helpers -/

theorem bind_ok {α β : Type} {m : Jl α} {f : α → Jl β} {r : β} (h : (m >>= f) = .ok r) :
    ∃ a, m = .ok a ∧ f a = .ok r := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## `platforms_match` as a conjunction over keys -/

theorem platformsMatch_cons (usem : UserSem) (a b : Platform) (k : Str) (rest : List Str) :
    platformsMatch usem (k :: rest) a b =
      (matchKey usem a b k >>= fun r => if r then platformsMatch usem rest a b else pure false) := rfl

theorem platformsMatch_true_iff (usem : UserSem) (a b : Platform) :
    ∀ order, platformsMatch usem order a b = .ok true ↔ ∀ k ∈ order, matchKey usem a b k = .ok true
  | [] => by simp [platformsMatch, pure, Except.pure]
  | k :: rest => by
    rw [platformsMatch_cons, List.forall_mem_cons, ← platformsMatch_true_iff usem a b rest]
    cases h : matchKey usem a b k with
    | error e => simp [bind, Except.bind]
    | ok r => cases r <;> simp [bind, Except.bind, pure, Except.pure]

theorem platformsMatch_false (usem : UserSem) (a b : Platform) :
    ∀ order, platformsMatch usem order a b = .ok false → ∃ k ∈ order, matchKey usem a b k = .ok false
  | [] => by simp [platformsMatch, pure, Except.pure]
  | k :: rest => by
    rw [platformsMatch_cons]
    intro h
    obtain ⟨r, hr, h⟩ := bind_ok h
    cases r with
    | false => exact ⟨k, List.mem_cons_self, hr⟩
    | true =>
      obtain ⟨k', hk', h'⟩ := platformsMatch_false usem a b rest h
      exact ⟨k', List.mem_cons_of_mem _ hk', h'⟩

theorem mem_order_iff {order : List Str} {a b : Platform} (h : IsUnionOrder order a b) (k : Str) :
    k ∈ order ↔ (haskey a.tags k = true ∨ haskey b.tags k = true) := h.2 k

/-- Results of `platforms_match` agree for two key orders with the same members
(whenever both return). -/
theorem platformsMatch_agree (usem : UserSem) (a b : Platform) (order order' : List Str) (x y : Bool)
    (hmem : ∀ k, k ∈ order ↔ k ∈ order')
    (hx : platformsMatch usem order a b = .ok x) (hy : platformsMatch usem order' a b = .ok y) : x = y := by
  cases x <;> cases y
  · rfl
  · obtain ⟨k, hk, hf⟩ := platformsMatch_false usem a b order hx
    rw [(platformsMatch_true_iff usem a b order').1 hy k ((hmem k).1 hk)] at hf
    cases hf
  · obtain ⟨k, hk, hf⟩ := platformsMatch_false usem a b order' hy
    rw [(platformsMatch_true_iff usem a b order).1 hx k ((hmem k).2 hk)] at hf
    cases hf
  · rfl

theorem matchOrderIndependent_proven : MatchOrderIndependent := by
  intro usem a b order order' x y h h' hx hy
  exact platformsMatch_agree usem a b order order' x y (fun k => by rw [h.2 k, h'.2 k]) hx hy

/-! ## Symmetry -/

theorem veq_iff (a b : VersionNumber) : veq a b = true ↔ a = b := by
  constructor
  · intro h
    unfold veq at h
    by_cases h1 : a.major = b.major <;> by_cases h2 : a.minor = b.minor <;>
      by_cases h3 : a.patch = b.patch <;> by_cases h4 : tupleCmp a.pre b.pre = 0 <;>
      by_cases h5 : tupleCmp a.build b.build = 0 <;> simp_all
    have e4 := tupleCmp_cmp.eq0 _ _ h4
    have e5 := tupleCmp_cmp.eq0 _ _ h5
    cases a; cases b; simp_all
  · rintro rfl
    unfold veq
    simp [tupleCmp_cmp.toIsPre.self]

theorem veq_self (a : VersionNumber) : veq a a = true := (veq_iff a a).2 rfl

theorem veq_comm (a b : VersionNumber) : veq a b = veq b a := by
  by_cases h : a = b
  · subst h; rfl
  · have h1 : veq a b = false := by
      cases e : veq a b
      · rfl
      · exact absurd ((veq_iff a b).1 e) h
    have h2 : veq b a = false := by
      cases e : veq b a
      · rfl
      · exact absurd ((veq_iff b a).1 e).symm h
    rw [h1, h2]

theorem beq_swap {α : Type} [BEq α] [LawfulBEq α] (x y : α) : (x == y) = (y == x) := by
  cases hxy : x == y <;> cases hyx : y == x <;> simp_all

theorem strategy_builtin {p : Platform} (hp : BuiltinStrats p) (k : Str) (n : Nat) : strategy p k ≠ .user n := by
  unfold strategy dget
  cases hf : p.strats.find? (·.1 == k) with
  | none => simp
  | some e => simpa using hp e (List.mem_of_find?_eq_some hf) n

theorem compare_dflt_swap (usem : UserSem) (x y : Str) (f g : Bool) :
    compare usem .dflt x y f g = compare usem .dflt y x g f := by
  simp only [compare, beq_swap x y]

theorem compare_juliaMinor_swap (usem : UserSem) (x y : Str) (f g : Bool) (r : Bool)
    (h : compare usem .juliaMinor x y f g = .ok r) : compare usem .juliaMinor y x g f = .ok r := by
  simp only [compare] at h ⊢
  obtain ⟨va, hx, h⟩ := bind_ok h
  obtain ⟨vb, hy, h⟩ := bind_ok h
  rw [hy, hx]
  simpa [bind, Except.bind, pure, Except.pure, beq_swap va.major.val, beq_swap va.minor.val] using h

theorem compare_cap_swap (usem : UserSem) (x y : Str) (f g : Bool) (r : Bool) (hfg : (f || g) = true)
    (h : compare usem .cap x y f g = .ok r) : compare usem .cap y x g f = .ok r := by
  simp only [compare] at h ⊢
  obtain ⟨va, hx, h⟩ := bind_ok h
  obtain ⟨vb, hy, h⟩ := bind_ok h
  rw [hy, hx]
  cases f <;> cases g <;> simp_all [bind, Except.bind, pure, Except.pure, veq_comm]

theorem compare_swap (usem : UserSem) (c : Strat) (hc : ∀ n, c ≠ .user n) (x y : Str) (f g : Bool) (r : Bool)
    (hfg : (f || g) = true) (h : compare usem c x y f g = .ok r) : compare usem c y x g f = .ok r := by
  cases c with
  | dflt => rw [compare_dflt_swap]; exact h
  | cap => exact compare_cap_swap usem x y f g r hfg h
  | juliaMinor => exact compare_juliaMinor_swap usem x y f g r h
  | user n => exact absurd rfl (hc n)

/-- The strategy `platforms_match` selects for a key. -/
def pick (sa sb : Strat) : Strat := if sb != .dflt then sb else sa

theorem pick_mem (sa sb : Strat) : pick sa sb = sa ∨ pick sa sb = sb := by
  unfold pick; split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem pick_symm (sa sb : Strat) (hc : ¬ (sa != .dflt && sb != .dflt && sa != sb) = true) :
    (if sa != .dflt then sa else sb) = pick sa sb := by
  unfold pick
  by_cases h1 : sa = .dflt <;> by_cases h2 : sb = .dflt <;> simp_all

theorem matchKey_swap (usem : UserSem) {a b : Platform} (ha : BuiltinStrats a) (hb : BuiltinStrats b) (k : Str)
    (r : Bool) (h : matchKey usem a b k = .ok r) : matchKey usem b a k = .ok r := by
  unfold matchKey at h ⊢
  cases hta : tget a k <;> cases htb : tget b k <;> simp only [hta, htb] at h ⊢
  · exact h
  · exact h
  · exact h
  · rename_i ak bk
    have hsa := strategy_builtin ha k
    have hsb := strategy_builtin hb k
    generalize strategy a k = sa at hsa h ⊢
    generalize strategy b k = sb at hsb h ⊢
    by_cases hc : (sa != .dflt && sb != .dflt && sa != sb) = true
    · rw [if_pos hc] at h
      cases h
    · rw [if_neg hc] at h
      have hc' : ¬ (sb != .dflt && sa != .dflt && sb != sa) = true := by
        by_cases h1 : sa = .dflt <;> by_cases h2 : sb = .dflt <;> by_cases h3 : sa = sb <;> simp_all
      rw [if_neg hc', pick_symm sa sb hc]
      have hbuiltin : ∀ n, pick sa sb ≠ .user n := by
        intro n; rcases pick_mem sa sb with e | e <;> rw [e]
        · exact hsa n
        · exact hsb n
      refine compare_swap usem (pick sa sb) hbuiltin ak bk _ _ r ?_ h
      rcases pick_mem sa sb with e | e <;> rw [e] <;> simp

theorem matchSymmetric_proven : MatchSymmetric := by
  intro usem a b order order' x y ha hb h h' hx hy
  cases x <;> cases y
  · rfl
  · obtain ⟨k, hk, hf⟩ := platformsMatch_false usem a b order hx
    have hk' : k ∈ order' := (h'.2 k).2 ((h.2 k).1 hk).symm
    have := (platformsMatch_true_iff usem b a order').1 hy k hk'
    rw [matchKey_swap usem ha hb k false hf] at this
    cases this
  · obtain ⟨k, hk, hf⟩ := platformsMatch_false usem b a order' hy
    have hk' : k ∈ order := (h.2 k).2 ((h'.2 k).1 hk).symm
    have := (platformsMatch_true_iff usem a b order).1 hx k hk'
    rw [matchKey_swap usem hb ha k false hf] at this
    cases this
  · rfl

/-! ## Semantics described in the docstring -/

theorem matchKey_one_sided (usem : UserSem) (a b : Platform) (k : Str)
    (h : ¬ (haskey a.tags k = true ∧ haskey b.tags k = true)) :
    matchKey usem a b k = .ok !(strictPresenceTags.contains k) := by
  unfold matchKey
  cases hta : tget a k <;> cases htb : tget b k
  · rfl
  · rfl
  · rfl
  · exfalso; apply h; simp [haskey, tget] at hta htb ⊢; simp [hta, htb]

theorem matchSemantics_proven : MatchSemantics := by
  intro usem a b order h
  rw [platformsMatch_true_iff]
  constructor
  · intro hall
    refine ⟨fun k ha hb => hall k ((h.2 k).2 (Or.inl ha)), ?_⟩
    cases hsa : haskey a.tags (s% "sanitize") <;> cases hsb : haskey b.tags (s% "sanitize")
    · rfl
    · have := hall _ ((h.2 _).2 (Or.inr hsb))
      rw [matchKey_one_sided usem a b _ (by simp [hsa])] at this
      simp [strictPresenceTags] at this
    · have := hall _ ((h.2 _).2 (Or.inl hsa))
      rw [matchKey_one_sided usem a b _ (by simp [hsb])] at this
      simp [strictPresenceTags] at this
    · rfl
  · rintro ⟨hboth, hsan⟩ k hk
    by_cases hab : haskey a.tags k = true ∧ haskey b.tags k = true
    · exact hboth k hab.1 hab.2
    · rw [matchKey_one_sided usem a b k hab]
      by_cases hks : k = s% "sanitize"
      · subst hks
        exfalso
        have := (h.2 _).1 hk
        cases hsa : haskey a.tags (s% "sanitize") <;> cases hsb : haskey b.tags (s% "sanitize") <;> simp_all
      · simp [strictPresenceTags, hks]

theorem matchConflictingStrategies_proven : MatchConflictingStrategies := by
  intro usem a b order k h ha hb hsa hsb hne heq
  have := (platformsMatch_true_iff usem a b order).1 heq k ((h.2 k).2 (Or.inl ha))
  unfold matchKey at this
  have hta : ∃ ak, tget a k = some ak := by
    simp [haskey, tget] at ha; exact Option.isSome_iff_exists.mp ha
  have htb : ∃ bk, tget b k = some bk := by
    simp [haskey, tget] at hb; exact Option.isSome_iff_exists.mp hb
  obtain ⟨ak, hak⟩ := hta
  obtain ⟨bk, hbk⟩ := htb
  rw [hak, hbk] at this
  simp [hsa, hsb, hne, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at this

theorem strategySemantics_proven : StrategySemantics := by
  intro usem a b va vb ha hb
  simp [compare, ha, hb, bind, Except.bind, pure, Except.pure]

end JuliaLean.Platforms
