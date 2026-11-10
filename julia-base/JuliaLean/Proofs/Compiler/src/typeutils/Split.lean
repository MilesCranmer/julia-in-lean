import JuliaLean.Proofs.Compiler.src.typeutils.Cost

/-!
`_switchtupleunion` and both `switchtupleunion` methods (`Compiler/src/typeutils.jl:318-392`)
without alias groups: the result is the cartesian product `cart` of the members of the `Union`
arguments, in the order the recursion visits them.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- The types `_switchtupleunion` splits an argument into: the members of a `Union`, and none for
any other argument. -/
def partsPure : LElt → Option (List Val)
  | .ty (.union a b) => some (uniontypes (.union a b))
  | _ => none

/-- The argument lists `_switchtupleunion(𝕃, t, i, ...)` emits, in order: the last of the first
`i` positions varies slowest. -/
def cart (t : Array LElt) : Nat → List (Array LElt)
  | 0 => [t]
  | i + 1 =>
    match t[i]? with
    | some a =>
      match partsPure a with
      | some ps => ps.flatMap fun ty => cart (t.set! i (.ty ty)) i
      | none => cart t i
    | none => []

/-- Pointwise relation between two lists. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a b as bs} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

theorem ListRel.append {α β : Type} {R : α → β → Prop} {as bs cs ds} :
    ListRel R as bs → ListRel R cs ds → ListRel R (as ++ cs) (bs ++ ds) := by
  intro h1 h2
  induction h1 with
  | nil => exact h2
  | cons hab _ ih => exact .cons hab ih

theorem ListRel.length_eq {α β : Type} {R : α → β → Prop} {as bs} (h : ListRel R as bs) :
    as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- The first `i` arguments are read without widening (see `PlainArgs`). -/
def PlainBelow (L : Lattice) (t : Array LElt) (i : Nat) : Prop :=
  hasExtendedUnionsplit L = true → ∀ k (hk : k < i) (hks : k < t.size),
    t[k].isTypeElt = true ∨ t[k].isVarargElt = true

theorem PlainBelow.set {L t i k} (h : PlainBelow L t i) (hk : i ≤ k) (x : LElt) :
    PlainBelow L (t.set! k x) i := by
  intro hext j hj hjs
  have hjs' : j < t.size := by simpa [Array.set!_eq_setIfInBounds] using hjs
  have := h hext j hj hjs'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hjs']
  rw [if_neg (by omega)]
  exact this

theorem PlainBelow.mono {L t i j} (h : PlainBelow L t i) (hj : j ≤ i) : PlainBelow L t j :=
  fun hext k hk hks => h hext k (by omega) hks

/-- The result `_switchtupleunion` promises: the arguments emitted so far, then one emitted value
per list of `cart`. -/
def CartResult {α : Type} (R : Array LElt → α → Prop) (t : Array LElt) (i : Nat)
    (tunion res : Array α) : Prop :=
  ∃ rs, res.toList = tunion.toList ++ rs ∧ ListRel R (cart t i) rs

theorem forIn_parts {α : Type} (R : Array LElt → α → Prop) (ps : List Val) (i : Nat)
    (t : Array LElt) (g : Array LElt → Array α → CM (Array α))
    (f : Val → Array LElt × Array α → CM (ForInStep (Array LElt × Array α)))
    (hf : ∀ ty t₀ tu s st s', (f ty (t₀, tu)).run s = .ok (st, s') →
      ∃ tu', st = .yield (t₀.set! i (.ty ty), tu') ∧ (g (t₀.set! i (.ty ty)) tu).run s = .ok (tu', s'))
    (hg : ∀ ty tu, Returns (g (t.set! i (.ty ty)) tu) (CartResult R (t.set! i (.ty ty)) i tu)) :
    ∀ t₀ tu, (∀ y, t₀.set! i y = t.set! i y) →
      Returns (forIn ps (t₀, tu) f) (fun st => ∃ rs, st.2.toList = tu.toList ++ rs ∧
        ListRel R (ps.flatMap fun ty => cart (t.set! i (.ty ty)) i) rs) := by
  induction ps with
  | nil => intro t₀ tu _ s st s' h; cases h; exact ⟨[], by simp, .nil⟩
  | cons ty ps ih =>
    intro t₀ tu ht₀ s st s' h
    obtain ⟨st₁, s₁, h1, h2⟩ := forIn_cons_run h
    obtain ⟨tu', rfl, hgr⟩ := hf ty t₀ tu s st₁ s₁ h1
    rw [ht₀] at hgr
    obtain ⟨rs1, hr1, hrel1⟩ := hg ty tu s tu' s₁ hgr
    have ht₁ : ∀ y, (t₀.set! i (.ty ty)).set! i y = t.set! i y := by
      intro y
      simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
      have := ht₀ y
      simpa only [Array.set!_eq_setIfInBounds] using this
    obtain ⟨rs2, hr2, hrel2⟩ := ih _ tu' ht₁ s₁ st s' h2
    refine ⟨rs1 ++ rs2, by rw [hr2, hr1, List.append_assoc], ?_⟩
    rw [List.flatMap_cons]
    exact hrel1.append hrel2

theorem forIn_empty_array_run {β γ : Type} (b : β) (f : γ → β → CM (ForInStep β)) (s : Nat) :
    (forIn (#[] : Array γ) b f).run s = .ok (b, s) := by
  rw [← Array.forIn_toList]; rfl

theorem forIn_nil_run {β γ : Type} (b : β) (f : γ → β → CM (ForInStep β)) (s : Nat) :
    (forIn ([] : List γ) b f).run s = .ok (b, s) := rfl

theorem widenconst_ty_run (n : Nat) (E : CEnv) (t : Val) (ht : t.isType = true) (s : Nat)
    {r s'} (h : (widenconst n E (.ty t)).run s = .ok (r, s')) : r = t ∧ s' = s := by
  cases n with
  | zero => cases h
  | succ n =>
    simp only [widenconst, ht, if_true] at h
    cases h; exact ⟨rfl, rfl⟩

/-- For an argument that is not a `Union`, `_switchtupleunion` does not split. -/
theorem xbranch_eq (n : Nat) (E : CEnv) (L : Lattice) {β : Type} (a : LElt)
    (hnu : ∀ x y, a ≠ .ty (.union x y))
    (hpl : hasExtendedUnionsplit L = true → a.isTypeElt = true ∨ a.isVarargElt = true)
    (k : Option (List Val) → CM β) (s : Nat) (r : β) (s' : Nat)
    (h : ((if (hasExtendedUnionsplit L && !a.isConst && !a.isVarargElt) = true then do
        let wty ← widenconst n E a
        if wty.isUnion = true then do
          let p ← pure (some (uniontypes wty)); k p
        else do let p ← pure none; k p
      else do let p ← pure none; k p) : CM β).run s = .ok (r, s')) :
    (k none).run s = .ok (r, s') := by
  split at h
  · rename_i hc
    have hext : hasExtendedUnionsplit L = true := by simp_all
    have hnv : a.isVarargElt = false := by simp_all
    rcases hpl hext with ht | ht
    · cases a with
      | ty t =>
        simp only [LElt.isTypeElt] at ht
        obtain ⟨w, s₁, hw, h4⟩ := run_bind_inv h
        obtain ⟨rfl, rfl⟩ := widenconst_ty_run n E t ht s hw
        have hnu' : w.isUnion = false := by
          cases w with
          | union x y => exact absurd rfl (hnu x y)
          | _ => rfl
        split at h4
        · rename_i hc; rw [hnu'] at hc; cases hc
        · exact h4
      | _ => simp [LElt.isTypeElt] at ht
    · rw [hnv] at ht; cases ht
  · exact h

/-- `_switchtupleunion(𝕃, t, i, tunion, origt)` without alias groups appends one emitted value
for each list of `cart t i`, in that order. -/
theorem switchtupleunion_cart (n : Nat) (E : CEnv) (L : Lattice) {α : Type}
    (emit : Array LElt → CM α) (R : Array LElt → α → Prop)
    (hemit : ∀ c s r s', (emit c).run s = .ok (r, s') → R c r) :
    ∀ i (t : Array LElt) (tunion : Array α), i ≤ t.size → PlainBelow L t i →
      Returns (switchtupleunion_ n E L emit t i tunion none) (CartResult R t i tunion) := by
  intro i
  induction i with
  | zero =>
    intro t tunion _ _ s res s' h
    simp only [switchtupleunion_] at h
    obtain ⟨r, s₁, hr, h⟩ := run_bind_inv h
    have hR := hemit t s r s₁ hr
    cases h
    exact ⟨[r], by simp, .cons hR .nil⟩
  | succ i ih =>
    intro t tunion hi hplain s res s' h
    simp only [switchtupleunion_, Nat.add_sub_cancel] at h
    have hit : i < t.size := by omega
    rw [Array.getElem?_eq_getElem hit] at h
    simp only at h
    have hrec : ∀ tu, Returns (switchtupleunion_ n E L emit t i tu none) (CartResult R t i tu) :=
      fun tu => ih t tu (by omega) (hplain.mono (by omega))
    have hcart_none : partsPure t[i] = none → cart t (i + 1) = cart t i := by
      intro hp; simp only [cart, Array.getElem?_eq_getElem hit, hp]
    generalize hai : t[i] = a at h hcart_none
    have hpl : hasExtendedUnionsplit L = true → a.isTypeElt = true ∨ a.isVarargElt = true :=
      fun hext => hai ▸ hplain hext i (by omega) hit
    by_cases hu : ∃ x y, a = .ty (.union x y)
    · obtain ⟨x, y, rfl⟩ := hu
      simp only [pure_bind] at h
      obtain ⟨st, s₁, hst, h⟩ := run_bind_inv h
      obtain ⟨rs, hrs, hrel⟩ := forIn_parts R (uniontypes (.union x y)) i t
        (fun t' tu => switchtupleunion_ n E L emit t' i tu none) _
        (by
          intro ty t₀ tu s₃ st₃ s₃' h3
          obtain ⟨t₁, s₄, ht₁, h3⟩ := run_bind_inv h3
          rw [forIn_empty_array_run] at ht₁
          cases ht₁
          obtain ⟨tu', s₅, htu, h3⟩ := run_bind_inv h3
          cases h3
          exact ⟨tu', rfl, htu⟩)
        (fun ty tu => ih _ tu (by simp [Array.set!_eq_setIfInBounds]; omega)
          ((hplain.mono (by omega)).set (Nat.le_refl i) _))
        t tunion (fun _ => rfl) s st s₁ hst
      obtain ⟨u, s₂, hu2, h⟩ := run_bind_inv h
      rw [List.zip_nil_left, forIn_nil_run] at hu2
      cases hu2
      cases h
      refine ⟨rs, hrs, ?_⟩
      all_goals (simp only [cart, Array.getElem?_eq_getElem hit, hai, partsPure]; try exact hrel)
    · have hnu : ∀ x y, a ≠ .ty (.union x y) := fun x y he => hu ⟨x, y, he⟩
      have hp : partsPure a = none := by
        cases a with
        | ty t' =>
          cases t' with
          | union x y => exact absurd rfl (hnu x y)
          | _ => rfl
        | _ => rfl
      have h2 : (switchtupleunion_ n E L emit t i tunion none).run s = .ok (res, s') := by
        cases a with
        | ty t' =>
          cases t' with
          | union x y => exact absurd rfl (hnu x y)
          | _ => have := xbranch_eq n E L _ hnu hpl _ s res s' h; simpa using this
        | _ => have := xbranch_eq n E L _ hnu hpl _ s res s' h; simpa using this
      have := hrec tunion s res s' h2
      unfold CartResult at this ⊢
      rwa [hcart_none hp]

/-! ## The lists of `cart` -/

/-- How many types an argument splits into: its number of `Union` members, or 1. -/
def partsCount (a : LElt) : Nat := match partsPure a with
  | some ps => ps.length
  | none => 1

/-- The product of `partsCount` over the first `i` arguments. -/
def countBelow (t : Array LElt) : Nat → Nat
  | 0 => 1
  | i + 1 => (match t[i]? with | some a => partsCount a | none => 0) * countBelow t i

theorem countBelow_set (t : Array LElt) (k : Nat) (y : LElt) :
    ∀ i, i ≤ k → countBelow (t.set! k y) i = countBelow t i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    simp only [countBelow, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    rw [if_neg (by omega)]
    rw [← Array.set!_eq_setIfInBounds, ih (by omega)]

theorem length_uniontypes : ∀ v : Val, (uniontypes v).length = unionlen v
  | .union a b => by simp [uniontypes, unionlen, length_uniontypes a, length_uniontypes b]
  | .datatype .. | .intersect .. | .typeeq .. | .typeegal .. | .unionall .. | .typevar ..
  | .vararg .. | .bottom | .typeapp .. | .long .. | .symbol .. | .bits .. | .imm ..
  | .mutableRef .. | .module .. => rfl

theorem not_union_of_mem_uniontypes : ∀ v m : Val, m ∈ uniontypes v → m.isUnion = false
  | .union a b, m, h => by
    simp only [uniontypes, List.mem_append] at h
    rcases h with h | h
    · exact not_union_of_mem_uniontypes a m h
    · exact not_union_of_mem_uniontypes b m h
  | .datatype .., m, h | .intersect .., m, h | .typeeq .., m, h | .typeegal .., m, h
  | .unionall .., m, h | .typevar .., m, h | .vararg .., m, h | .bottom, m, h
  | .typeapp .., m, h | .long .., m, h | .symbol .., m, h | .bits .., m, h | .imm .., m, h
  | .mutableRef .., m, h | .module .., m, h => by
    simp only [uniontypes, List.mem_singleton] at h; subst h; rfl

/-- `cart t i` has `countBelow t i` lists: the product of the members counts. -/
theorem length_cart : ∀ i (t : Array LElt), i ≤ t.size → (cart t i).length = countBelow t i := by
  intro i
  induction i with
  | zero => intro _ _; rfl
  | succ i ih =>
    intro t hi
    have hit : i < t.size := by omega
    simp only [cart, countBelow, Array.getElem?_eq_getElem hit, partsCount]
    cases hp : partsPure t[i] with
    | none => simp only [Nat.one_mul]; exact ih t (by omega)
    | some ps =>
      simp only [List.length_flatMap]
      have : ∀ ty ∈ ps, (cart (t.set! i (.ty ty)) i).length = countBelow t i := by
        intro ty _
        rw [ih _ (by simp [Array.set!_eq_setIfInBounds]; omega), countBelow_set t i _ i (Nat.le_refl i)]
      rw [List.map_congr_left this]
      clear this hp
      induction ps with
      | nil => simp
      | cons y ps ih' => simp only [List.map_cons, List.sum_cons, List.length_cons, ih']; grind

/-- The argument lists that keep every argument from position `i` on and replace each earlier
`Union` argument by one of its members. -/
def Choice (t : Array LElt) (i : Nat) (c : Array LElt) : Prop :=
  c.size = t.size ∧ (∀ k, i ≤ k → c[k]? = t[k]?) ∧
    ∀ k < i, ∀ a, t[k]? = some a →
      (partsPure a = none → c[k]? = some a) ∧ (∀ ps, partsPure a = some ps → ∃ y ∈ ps, c[k]? = some (.ty y))

/-- `cart t i` is exactly the set of `Choice t i` lists. -/
theorem mem_cart : ∀ i (t : Array LElt), i ≤ t.size → ∀ c, c ∈ cart t i ↔ Choice t i c := by
  intro i
  induction i with
  | zero =>
    intro t _ c
    simp only [cart, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    · rintro ⟨hs, hk, -⟩
      exact Array.ext_getElem? (fun k => hk k (Nat.zero_le k))
  | succ i ih =>
    intro t hi c
    have hit : i < t.size := by omega
    have hget : t[i]? = some t[i] := Array.getElem?_eq_getElem hit
    simp only [cart, hget]
    cases hp : partsPure t[i] with
    | none =>
      rw [ih t (by omega)]
      constructor
      · rintro ⟨hs, hk, hb⟩
        refine ⟨hs, fun k hk' => hk k (by omega), fun k hk' a ha => ?_⟩
        by_cases hki : k = i
        · subst hki
          rw [hget] at ha; cases ha
          exact ⟨fun _ => by rw [hk k (Nat.le_refl k), hget], fun ps hps => by rw [hp] at hps; cases hps⟩
        · exact hb k (by omega) a ha
      · rintro ⟨hs, hk, hb⟩
        refine ⟨hs, fun k hk' => ?_, fun k hk' a ha => hb k (by omega) a ha⟩
        by_cases hki : k = i
        · subst hki; rw [(hb k (by omega) _ hget).1 hp, hget]
        · exact hk k (by omega)
    | some ps =>
      simp only [List.mem_flatMap]
      constructor
      · rintro ⟨y, hy, hc⟩
        rw [ih _ (by simp [Array.set!_eq_setIfInBounds]; omega)] at hc
        obtain ⟨hs, hk, hb⟩ := hc
        simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at hs
        refine ⟨hs, fun k hk' => ?_, fun k hk' a ha => ?_⟩
        · have := hk k (by omega)
          simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at this
          rwa [if_neg (by omega)] at this
        · by_cases hki : k = i
          · subst hki
            rw [hget] at ha; cases ha
            refine ⟨fun h => (by rw [hp] at h; cases h), fun ps' hps' => ?_⟩
            rw [hp] at hps'; cases hps'
            refine ⟨y, hy, ?_⟩
            have := hk k (Nat.le_refl k)
            simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_true] at this
            rwa [if_pos hit] at this
          · have ha' : (t.set! i (.ty y))[k]? = some a := by
              simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
              rwa [if_neg (by omega)]
            exact hb k (by omega) a ha'
      · rintro ⟨hs, hk, hb⟩
        obtain ⟨y, hy, hcy⟩ := (hb i (Nat.lt_succ_self i) _ hget).2 ps hp
        refine ⟨y, hy, ?_⟩
        rw [ih _ (by simp [Array.set!_eq_setIfInBounds]; omega)]
        refine ⟨by simp [Array.set!_eq_setIfInBounds, hs], fun k hk' => ?_, fun k hk' a ha => ?_⟩
        · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
          by_cases hki : i = k
          · subst hki; rw [if_pos rfl, if_pos hit]; exact hcy
          · rw [if_neg hki]; exact hk k (by omega)
        · have ha' : t[k]? = some a := by
            simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at ha
            rwa [if_neg (by omega)] at ha
          exact hb k (by omega) a ha'

/-- After splitting every position, no argument is a `Union`. -/
theorem cart_no_union (t : Array LElt) : ∀ c ∈ cart t t.size, ∀ (k : Nat) (e : LElt), c[k]? = some e →
    partsPure e = none := by
  intro c hc k e he
  obtain ⟨hs, -, hb⟩ := (mem_cart t.size t (Nat.le_refl _) c).mp hc
  have hk : k < t.size := by
    have := (Array.getElem?_eq_some_iff.mp he).1; omega
  obtain ⟨a, ha⟩ : ∃ a, t[k]? = some a := ⟨t[k], Array.getElem?_eq_getElem hk⟩
  obtain ⟨h1, h2⟩ := hb k hk a ha
  cases hp : partsPure a with
  | none => rw [h1 hp] at he; cases he; exact hp
  | some ps =>
    obtain ⟨y, hy, hcy⟩ := h2 ps hp
    rw [hcy] at he; cases he
    have : ps = uniontypes (match a with | .ty v => v | _ => .bottom) := by
      cases a with
      | ty v => cases v with
        | union x y => simp only [partsPure] at hp; cases hp; rfl
        | _ => simp [partsPure] at hp
      | _ => simp [partsPure] at hp
    rw [this] at hy
    have := not_union_of_mem_uniontypes _ y hy
    cases y with
    | union => simp [Val.isUnion] at this
    | _ => rfl

theorem listRel_toList {l : List (Array LElt)} {rs : List (List LElt)}
    (h : ListRel (fun c r => r = c.toList) l rs) : rs = l.map Array.toList := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hab, ih]

theorem plainBelow_of_plainArgs (L : Lattice) (argtypes : List LElt) (h : PlainArgs L argtypes)
    (i : Nat) : PlainBelow L argtypes.toArray i :=
  fun hext k _ hks => h hext _ (by simp)

/-- `switchtupleunion(𝕃, argtypes)` without alias groups (no `fargs`, no `MustAlias` argument)
and for arguments it reads unwidened returns the argument lists of `cart`: each list replaces
every `Union` argument by one of its members, every such choice appears once per member, in order,
no `Union` argument is left, and there are as many lists as the product of the members counts
(`Compiler/src/typeutils.jl:318-331`: "return an array such that those Unions are removed and
`Union{return...} == ty`"). -/
def SwitchtupleunionLSpec : Prop :=
  (∀ n E L argtypes, NoMustAlias argtypes → PlainArgs L argtypes →
    Returns (switchtupleunionL n E L argtypes none)
      (· = (cart argtypes.toArray argtypes.length).map Array.toList)) ∧
  (∀ t : Array LElt, (cart t t.size).length = countBelow t t.size) ∧
  (∀ (t : Array LElt) c, c ∈ cart t t.size ↔ Choice t t.size c) ∧
  (∀ t : Array LElt, ∀ c ∈ cart t t.size, ∀ (k : Nat) (e : LElt), c[k]? = some e → partsPure e = none) ∧
  (∀ x y, partsCount (.ty (.union x y)) = unionlen (.union x y))

theorem switchtupleunionLSpec_proven : SwitchtupleunionLSpec := by
  refine ⟨fun n E L argtypes hma hplain s r s' h => ?_, fun t => length_cart _ t (Nat.le_refl _),
    fun t c => mem_cart _ t (Nat.le_refl _) c, cart_no_union,
    fun x y => by simp [partsCount, partsPure, length_uniontypes]⟩
  simp only [switchtupleunionL] at h
  obtain ⟨g, s₁, hg, h⟩ := run_bind_inv h
  have := computeAliasGroups_none argtypes (some argtypes) (.inr rfl) hma s g s₁ hg
  subst this
  obtain ⟨res, s₂, hres, h⟩ := run_bind_inv h
  obtain ⟨rs, hrs, hrel⟩ := switchtupleunion_cart n E L (fun t => pure t.toList)
    (fun c r => r = c.toList) (fun c s r s' h => by cases h; rfl) argtypes.length argtypes.toArray
    #[] (by simp) (plainBelow_of_plainArgs L argtypes hplain _) s₁ res s₂ hres
  cases h
  simp only [List.nil_append] at hrs
  rw [hrs]
  exact listRel_toList hrel

/-- `switchtupleunion(ty)` returns one tuple type per list of `cart` of `ty`'s (unwrapped)
parameters: as many as the product of the members counts of its `Union` parameters. -/
def SwitchtupleunionCount : Prop :=
  ∀ n E (ty : Val) name ps, ty.unwrapUnionall = .datatype name ps →
    Returns (switchtupleunion n E ty)
      (fun r => r.length = countBelow (ps.map LElt.ty).toArray ps.length)

theorem switchtupleunionCount_proven : SwitchtupleunionCount := by
  intro n E ty name ps hty s r s' h
  simp only [switchtupleunion, hty] at h
  obtain ⟨res, s₁, hres, h⟩ := run_bind_inv h
  obtain ⟨rs, hrs, hrel⟩ := switchtupleunion_cart n E .jlType _ (fun _ _ => True)
    (fun _ _ _ _ _ => trivial) ps.length (ps.map LElt.ty).toArray #[] (by simp)
    (fun hext => by simp [hasExtendedUnionsplit] at hext) s res s₁ hres
  cases h
  simp only [List.nil_append] at hrs
  rw [Array.length_toList, ← Array.length_toList, hrs, ← hrel.length_eq,
    length_cart _ _ (by simp)]

end JuliaLean.Proofs.Compiler.src.typeutils
