import JuliaLean.Proofs.Compiler.src.typelimits.Simpler

/-!
Branch-by-branch statements of `Compiler/src/typelimits.jl`: for each method, what it returns on
each of its branches, given what the calls it makes return. They pin the bodies that the
coarser laws in the other files leave open.

`Gives m v` says that every run of `m` that returns, returns `v`. A hypothesis `Gives m v` on a
call the method makes fixes the answer of that call; the conclusion then fixes the method's
answer. `Via m m'` says that every result of `m` is a result of `m'` (from some state), so `m`
hands its arguments on to `m'` unchanged.
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- Every run of `m` that returns, returns `v`. -/
abbrev Gives {α : Type} (m : CM α) (v : α) : Prop := Returns m (· = v)

/-- Every result of `m` is a result of `m'` from some state, with the same final state. -/
def Via {α : Type} (m m' : CM α) : Prop :=
  ∀ s r s', m.run s = .ok (r, s') → ∃ s₁, m'.run s₁ = .ok (r, s')

theorem gives_bind {α β : Type} {m : CM α} {f : α → CM β} {v : α} {s s' : Nat} {r : β}
    (hm : Gives m v) (h : (m >>= f).run s = .ok (r, s')) : ∃ s₁, (f v).run s₁ = .ok (r, s') := by
  obtain ⟨v', s₁, h1, h2⟩ := bind_ok_inv h
  have := hm _ _ _ h1; subst this
  exact ⟨s₁, h2⟩

/-! ## `union_count_abstract` -/

/-- `union_count_abstract(t)` is the number of members of the union `t` that are not dispatch
elements (`Compiler/src/typelimits.jl:315-316`), where `d x` is what `isdispatchelem(x)` answers;
for a non-`Union` `x` it is `0` when `x` is a dispatch element and `1` otherwise. -/
def UnionCountAbstractExact : Prop :=
  (∀ E (t : Val) (d : Val → Bool), (∀ x ∈ uniontypes t, Gives (isdispatchelem E x) (d x)) →
    Gives (unionCountAbstract E t) ((uniontypes t).filter (fun x => !d x)).length) ∧
  (∀ E (x : Val) (b : Bool), (∀ p q, x ≠ .union p q) → Gives (isdispatchelem E x) b →
    Gives (unionCountAbstract E x) (if b then 0 else 1))

theorem unionCountAbstractExact_proven : UnionCountAbstractExact := by
  refine ⟨?_, ?_⟩
  · intro E t d
    induction t using unionCountAbstract.induct with
    | case1 a b iha ihb =>
      intro hall s r s' h
      simp only [unionCountAbstract] at h
      obtain ⟨ra, s₁, ha, h⟩ := bind_ok_inv h
      obtain ⟨rb, s₂, hb, h⟩ := bind_ok_inv h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      have e1 := iha (fun x hx => hall x (by simp [uniontypes, hx])) _ _ _ ha
      have e2 := ihb (fun x hx => hall x (by simp [uniontypes, hx])) _ _ _ hb
      simp only [uniontypes, List.filter_append, List.length_append]; omega
    | case2 x hx =>
      intro hall s r s' h
      rw [unionCountAbstract.eq_2 E x hx] at h
      obtain ⟨b, s₁, hd, h⟩ := bind_ok_inv h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      have := hall x (by rw [uniontypes_nonunion hx]; exact List.mem_singleton.mpr rfl) _ _ _ hd
      subst this
      rw [uniontypes_nonunion hx]
      cases hdx : d x <;> simp [hdx]
  · intro E x b hx hd s r s' h
    rw [unionCountAbstract.eq_2 E x hx] at h
    obtain ⟨b', s₁, hb, h⟩ := bind_ok_inv h
    obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
    rw [hd _ _ _ hb]

/-! ## `union_causes` -/

theorem mem_idsetUnion_inv {s t : List ObjId} {x : ObjId} (h : x ∈ idsetUnion s t) : x ∈ s ∨ x ∈ t := by
  unfold idsetUnion at h
  induction t generalizing s with
  | nil => exact .inl h
  | cons y t ih =>
    simp only [List.foldl_cons] at h
    rcases ih h with h | h
    · split at h
      · exact .inl h
      · rcases List.mem_append.mp h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons.mpr (.inl (List.mem_singleton.mp h)))
    · exact .inr (List.mem_cons_of_mem _ h)

/-- `union_causes(a, b)` (`Compiler/src/typelimits.jl:427-435`) returns the set `b` itself when
`a ⊆ b`, else the set `a` itself when `b ⊆ a`, else a new set (a fresh object) whose members are
exactly those of `a` and `b`. In every case the members of the result are exactly the members of
`a` and `b`. -/
def UnionCausesExact : Prop :=
  ∀ (a b r : List ObjId × ObjId) s s', (unionCauses a b).run s = .ok (r, s') →
    (a.1.all b.1.contains = true → r = b) ∧
    (a.1.all b.1.contains = false → b.1.all a.1.contains = true → r = a) ∧
    (a.1.all b.1.contains = false → b.1.all a.1.contains = false → r.2 = s) ∧
    (∀ x, x ∈ r.1 ↔ x ∈ a.1 ∨ x ∈ b.1)

theorem unionCausesExact_proven : UnionCausesExact := by
  intro a b r s s' h
  have hsup := unionCausesSuperset_proven a b r s s' h
  unfold unionCauses at h
  by_cases hab : a.1.all b.1.contains = true
  · rw [if_pos hab] at h
    obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
    refine ⟨fun _ => rfl, fun h => absurd hab (by simp [h]), fun h => absurd hab (by simp [h]),
      fun x => ⟨fun hx => .inr hx, fun hx => hx.elim (fun hx => ?_) id⟩⟩
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hab x hx)
  rw [if_neg hab] at h
  have hab' : a.1.all b.1.contains = false := by simpa using hab
  by_cases hba : b.1.all a.1.contains = true
  · rw [if_pos hba] at h
    obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
    refine ⟨fun h => absurd h hab, fun _ _ => rfl, fun _ h => absurd hba (by simp [h]),
      fun x => ⟨fun hx => .inl hx, fun hx => hx.elim id (fun hx => ?_)⟩⟩
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hba x hx)
  rw [if_neg hba] at h
  obtain ⟨c, s₁, hc, h⟩ := bind_ok_inv h
  obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
  unfold copyIdSet at hc
  obtain ⟨id, s₂, hid, hc⟩ := bind_ok_inv hc
  obtain ⟨h2, -⟩ := pure_ok_inv hc; subst h2
  have : id = s := by cases hid; rfl
  subst this
  refine ⟨fun h => absurd h hab, fun _ h => absurd h hba, fun _ _ => rfl, fun x => ⟨fun hx => ?_,
    fun hx => hx.elim (hsup.1 x) (hsup.2 x)⟩⟩
  exact mem_idsetUnion_inv hx

/-! ## `issimpleenoughtype` -/

/-- `issimpleenoughtype(t)` (`Compiler/src/typelimits.jl:318-323`), both branches:
* when `unwrap_unionall(t)` is a `DataType` whose type name's wrapper is `== t`, the answer is
  `true` (line 320), whatever the union counts are;
* otherwise the answer is `max(unionlen(t), union_count_abstract(t) + 1) ≤ 3 &&
  unioncomplexity(t) ≤ 3` (lines 321-322), with `c` and `k` what the two counts return. -/
def IssimpleenoughtypeExact : Prop :=
  (∀ n E (t : Val) name ps tn, unwrapUnionall t = .datatype name ps →
    Gives (E.types.typename name) tn → Gives (tyEq n E tn.wrapper t) true →
    Gives (issimpleenoughtype n E t) true) ∧
  (∀ n E (t : Val) c k,
    (∀ name ps, unwrapUnionall t = .datatype name ps → ∀ tn s₁ s₂,
      (E.types.typename name).run s₁ = .ok (tn, s₂) → Gives (tyEq n E tn.wrapper t) false) →
    Gives (unionCountAbstract E t) c → Gives (unioncomplexity n t) k →
    Gives (issimpleenoughtype n E t)
      (decide (max (unionlen t) (c + 1) ≤ MAX_TYPEUNION_LENGTH) && decide (k ≤ MAX_TYPEUNION_COMPLEXITY)))

theorem issimpleenoughtypeExact_proven : IssimpleenoughtypeExact := by
  refine ⟨fun n E t name ps tn hut htn heq s r s' h => ?_, fun n E t c k hw hc hk s r s' h => ?_⟩
  · unfold issimpleenoughtype at h
    simp only [hut] at h
    obtain ⟨tn', s₁, htn', h⟩ := bind_ok_inv h
    have := htn _ _ _ htn'; subst this
    obtain ⟨b, s₂, hb, h⟩ := bind_ok_inv h
    have := heq _ _ _ hb; subst this
    exact (pure_ok_inv h).1
  · unfold issimpleenoughtype at h
    have tail : ∀ s₀, (do
          if !(max (unionlen t) ((← unionCountAbstract E t) + 1) ≤ MAX_TYPEUNION_LENGTH) then
            return false
          return decide ((← unioncomplexity n t) ≤ MAX_TYPEUNION_COMPLEXITY) : CM Bool).run s₀ = .ok (r, s') →
        r = (decide (max (unionlen t) (c + 1) ≤ MAX_TYPEUNION_LENGTH) && decide (k ≤ MAX_TYPEUNION_COMPLEXITY)) := by
      intro s₀ h
      obtain ⟨c', s₁, h₁, h⟩ := bind_ok_inv h
      have := hc _ _ _ h₁; subst this
      by_cases hle : max (unionlen t) (c' + 1) ≤ MAX_TYPEUNION_LENGTH
      · rw [if_neg (by simpa using hle)] at h
        obtain ⟨k', s₂, h₂, h⟩ := bind_ok_inv h
        have := hk _ _ _ h₂; subst this
        obtain ⟨h1, -⟩ := pure_ok_inv h
        subst h1; simp [hle]
      · rw [if_pos (by simpa using hle)] at h
        obtain ⟨h1, -⟩ := pure_ok_inv h
        subst h1; simp [hle]
    simp only at h
    split at h
    · rename_i name ps hut
      obtain ⟨tn, s₁, htn, h⟩ := bind_ok_inv h
      obtain ⟨b, s₂, hb, h⟩ := bind_ok_inv h
      have := hw name ps hut tn _ _ htn _ _ _ hb; subst this
      exact tail _ h
    · exact tail _ h

/-! ## `tmerge_fast_path` -/

/-- `tmerge_fast_path(𝕃, a, b)` (`Compiler/src/typelimits.jl:413-425`) on two elements that are
not `Union{}`, given what `===`, the two `⊑` queries and the two `issimplertype` queries answer:
`a` when `a === b`; else `b` when `a ⊑ b` and `issimplertype(b, a)`; else `a` when `a ⊑ b` and
`b ⊑ a`; else `a` when `b ⊑ a` and `issimplertype(a, b)`; else `nothing`. -/
def TmergeFastPathExact : Prop :=
  ∀ n E L (a b : LElt) (e sa sb ia ib : Bool), a.isBottom = false → b.isBottom = false →
    Gives (eltEgal n E a b) e → Gives (sqsub n E L a b) sa → Gives (sqsub n E L b a) sb →
    Gives (issimplertype n E L b a) ia → Gives (issimplertype n E L a b) ib →
    Gives (tmergeFastPath n E L a b)
      (if e then some a else if sa && ia then some b else if sa && sb then some a
       else if sb && ib then some a else none)

theorem tmergeFastPathExact_proven : TmergeFastPathExact := by
  intro n E L a b e sa sb ia ib ha hb he hsa hsb hia hib s r s' h
  unfold tmergeFastPath at h
  simp only [ha, hb, Bool.false_eq_true, if_false] at h
  obtain ⟨e', s₁, he', h⟩ := bind_ok_inv h
  have := he _ _ _ he'; subst e'
  cases e
  · simp only [Bool.false_eq_true, if_false] at h ⊢
    obtain ⟨sa', s₂, hsa', h⟩ := bind_ok_inv h
    have := hsa _ _ _ hsa'; subst sa'
    cases sa
    · simp only [Bool.false_eq_true, if_false, Bool.false_and] at h ⊢
      obtain ⟨sb', s₃, hsb', h⟩ := bind_ok_inv h
      have := hsb _ _ _ hsb'; subst sb'
      cases sb
      · simp only [Bool.false_eq_true, if_false, Bool.and_false] at h
        exact (pure_ok_inv h).1
      · simp only [if_true, Bool.true_and] at h ⊢
        obtain ⟨ib', s₄, hib', h⟩ := bind_ok_inv h
        have := hib _ _ _ hib'; subst ib'
        cases ib
        · exact (pure_ok_inv h).1
        · exact (pure_ok_inv h).1
    · simp only [if_true, Bool.true_and] at h ⊢
      obtain ⟨ia', s₃, hia', h⟩ := bind_ok_inv h
      have := hia _ _ _ hia'; subst ia'
      cases ia
      · simp only [Bool.false_eq_true, if_false] at h ⊢
        obtain ⟨sb', s₄, hsb', h⟩ := bind_ok_inv h
        have := hsb _ _ _ hsb'; subst sb'
        cases sb
        · simp only [Bool.false_eq_true, if_false, Bool.and_false] at h ⊢
          exact (pure_ok_inv h).1
        · simp only [if_true, Bool.and_self] at h ⊢
          exact (pure_ok_inv h).1
      · simp only [if_true] at h ⊢
        exact (pure_ok_inv h).1
  · simp only [if_true] at h ⊢
    exact (pure_ok_inv h).1

end JuliaLean.Proofs.Compiler.src.typelimits
