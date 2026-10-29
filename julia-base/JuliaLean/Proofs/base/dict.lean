import JuliaLean.base.dict
import JuliaLean.Registry.Types

/-!
# Properties of `base/dict.jl`

`Dict` properties compare a table with a finite reference map: `DictRep hash eqKey h m` says
that `h` satisfies the invariant every API call preserves (power-of-two size, slot bytes,
reachable probe chains, pairwise non-`isequal` keys, `count`, `maxprobe`, `idxfloor`) and that
its stored pairs are a permutation of `m`. Callees defined in other Julia files are parameters
constrained only by their documented laws.
-/

namespace JuliaLean.Proofs.base.dict

open JuliaLean JuliaLean.base.dict JuliaLean.Registry

variable {K V : Type}

/-! ## Laws of callees from other files -/

/-- `isequal` is an equivalence relation and `isequal(x, y)` implies `hash(x) == hash(y)`
(`Dict` docstring `base/dict.jl:35`, `hash` docstring `base/hashing.jl`). `eqKey` is the probe
test `key === k || isequal(key, k)`. -/
structure KeyLaws (hash : K → JInt .u64) (eqKey : K → K → Bool) : Prop where
  refl : ∀ a, eqKey a a = true
  symm : ∀ a b, eqKey a b = true → eqKey b a = true
  trans : ∀ a b c, eqKey a b = true → eqKey b c = true → eqKey a c = true
  hash_eq : ∀ a b, eqKey a b = true → hash a = hash b

/-- `_tablesz(x) = x < 16 ? 16 : 1 << top_set_bit(x-1)` (`base/abstractdict.jl:584`) with
`top_set_bit(y) = log2(y) + 1`, on the `Int` arguments that cannot wrap. -/
def tableszSpec (x : Nat) : Nat := if x < 16 then 16 else 2 ^ (Nat.log2 (x - 1) + 1)

def TableszLaw (tablesz : Nat → Nat) : Prop := ∀ x, x ≤ 2 ^ 62 → tablesz x = tableszSpec x

/-- `cld(x, 2)`: the smallest integer at least `x / 2` (`cld` docstring, `base/div.jl`). -/
def CldLaw (cld : JInt .i64 → JInt .i64) : Prop := ∀ x : JInt .i64, (cld x).val = -((-x.val) / 2)

/-- `max_values(K)` bounds the number of pairwise non-`isequal` keys, or is at least `2^62`
(`base/abstractset.jl`). -/
def MaxValuesLaw (eqKey : K → K → Bool) (maxValues : Nat) : Prop :=
  2 ^ 62 ≤ maxValues ∨
  ∀ xs : List K, xs.Pairwise (fun a b => eqKey a b = false) → xs.length ≤ maxValues

/-- `unsetindex!(m, i)` leaves every other index of the memory unchanged. -/
def UnsetLaw {α : Type} (unset : Nat → (Nat → Option α) → Nat → (Nat → Option α)) : Prop :=
  ∀ size f i j, j ≠ i → unset size f i j = f j

/-- `fill!(m, b)` sets every index `1:length(m)` to `b`. -/
def FillLaw (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat) : Prop :=
  ∀ size b slots i, 1 ≤ i → i ≤ size → fillSlots size b slots i = b

/-- `copy(m)` has the entries of `m` at every index `1:length(m)`. -/
def CopyLaw {α : Type} (copy : Nat → (Nat → α) → Nat → α) : Prop :=
  ∀ size f i, 1 ≤ i → i ≤ size → copy size f i = f i

/-- `x isa V ? x : convert(V, x)` returns `x` itself when `x isa V`. -/
def ValueConvLaw {W : Type} (conv : ValueConv W V) : Prop :=
  ∀ w v, conv.isa w = some v → conv.convert w = .ok v

/-- The key conversion of `setindex!`/`get!` (`base/dict.jl:347-357,445-455`): a key that is
already a `K` is used as is, otherwise `convert(K, key0)` must stay `isequal` to `key0`. -/
def convKey {Q : Type} (conv : KeyConv Q K) (q : Q) : DictResult K :=
  match conv.isa q with
  | some k => .ok k
  | none =>
    match conv.convert q with
    | .ok k => if conv.isequal q k then .ok k else .error .keyTypeError
    | .error e => .error e

/-! ## Slot arithmetic -/

/-- Table sizes after the first `rehash!`: powers of two, at least 16. -/
def IsPow (sz : Nat) : Prop := ∃ p, 4 ≤ p ∧ sz = 2 ^ p

theorem IsPow.ge {sz : Nat} (h : IsPow sz) : 16 ≤ sz := by
  obtain ⟨p, hp, rfl⟩ := h
  calc 16 = 2 ^ 4 := rfl
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp

theorem IsPow.land {sz : Nat} (h : IsPow sz) (x : Nat) : Nat.land x (sz - 1) = x % sz := by
  obtain ⟨p, -, rfl⟩ := h
  exact Nat.and_two_pow_sub_one_eq_mod x p

theorem IsPow.dvd64 {sz : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) : ∃ q, 2 ^ 64 = sz * q := by
  obtain ⟨p, -, rfl⟩ := h
  have hp : p ≤ 64 := by
    apply Nat.le_of_not_lt
    intro hc
    have : 2 ^ 65 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hc
    omega
  exact ⟨2 ^ (64 - p), by rw [← Nat.pow_add]; congr 1; omega⟩

theorem IsPow.double {sz : Nat} (h : IsPow sz) : IsPow (sz * 2) := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p + 1, by omega, (Nat.pow_succ 2 p).symm⟩

theorem IsPow.quad {sz : Nat} (h : IsPow sz) : IsPow (sz * 4) := by
  obtain ⟨p, hp, rfl⟩ := h
  refine ⟨p + 2, by omega, ?_⟩
  rw [Nat.pow_add]

theorem sub_mod_pow {sz d : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (hd : 0 < d) (hd' : d ≤ sz) :
    (2 ^ 64 - d) % sz = sz - d := by
  obtain ⟨q, hq⟩ := h.dvd64 hs
  cases q with
  | zero => rw [Nat.mul_zero] at hq; exact absurd hq (by decide)
  | succ q =>
    have hle : sz ≤ sz * (q + 1) := Nat.le_mul_of_pos_right sz (by omega)
    have e : 2 ^ 64 - d = sz * q + (sz - d) := by
      have : sz * (q + 1) = sz * q + sz := Nat.mul_succ sz q
      omega
    rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem nextIndex_spec {sz i : Nat} (h : IsPow sz) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    (i < sz ∧ nextIndex sz i = i + 1) ∨ (i = sz ∧ nextIndex sz i = 1) := by
  unfold nextIndex
  rw [h.land]
  by_cases hi : i < sz
  · left; exact ⟨hi, by rw [Nat.mod_eq_of_lt hi]⟩
  · right
    have e : i = sz := by omega
    refine ⟨e, ?_⟩
    rw [e, Nat.mod_self]

theorem intBits64_of_nonneg {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) : intBits64 x = x.toNat := by
  unfold intBits64
  omega

theorem intBits64_of_neg {x : Int} (h0 : -2 ^ 64 ≤ x) (h1 : x < 0) :
    intBits64 x = (x + 2 ^ 64).toNat := by
  unfold intBits64
  omega

theorem previousIndex_spec {sz i : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i)
    (h2 : i ≤ sz) :
    (i = 1 ∧ previousIndex sz i = sz) ∨ (1 < i ∧ previousIndex sz i = i - 1) := by
  have h16 := h.ge
  unfold previousIndex
  rw [h.land]
  by_cases hi : i = 1
  · left
    refine ⟨hi, ?_⟩
    have hb : intBits64 ((i : Int) - 2) = 2 ^ 64 - 1 := by
      rw [intBits64_of_neg (by omega) (by omega)]
      omega
    rw [hb, sub_mod_pow h hs (by omega) (by omega)]
    omega
  · right
    refine ⟨by omega, ?_⟩
    have hb : intBits64 ((i : Int) - 2) = i - 2 := by
      rw [intBits64_of_nonneg (by omega) (by omega)]
      omega
    rw [hb, Nat.mod_eq_of_lt (by omega)]
    omega

/-- `(index - index0) & (newsz-1)`, the probe length in `rehash!`. -/
def probeDist (newsz index index0 : Nat) : Nat :=
  Nat.land (intBits64 ((index : Int) - (index0 : Int))) (newsz - 1)

theorem probeDist_spec {sz i j : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64)
    (h1 : 1 ≤ i) (h2 : i ≤ sz) (h3 : 1 ≤ j) (h4 : j ≤ sz) :
    (j ≤ i ∧ probeDist sz i j = i - j) ∨ (i < j ∧ probeDist sz i j = i + sz - j) := by
  unfold probeDist
  rw [h.land]
  by_cases hij : j ≤ i
  · left
    refine ⟨hij, ?_⟩
    have hb : intBits64 ((i : Int) - j) = i - j := by
      rw [intBits64_of_nonneg (by omega) (by omega)]
      omega
    rw [hb, Nat.mod_eq_of_lt (by omega)]
  · right
    refine ⟨by omega, ?_⟩
    have hb : intBits64 ((i : Int) - j) = 2 ^ 64 - (j - i) := by
      rw [intBits64_of_neg (by omega) (by omega)]
      omega
    rw [hb, sub_mod_pow h hs (by omega) (by omega)]
    omega

/-- The home slot `hashindex(key, sz)[1]` of a key. -/
def home (hash : K → JInt .u64) (sz : Nat) (k : K) : Nat := (hashindex hash k sz).1

theorem hashindex_fst (hash : K → JInt .u64) (k : K) (sz : Nat) :
    (hashindex hash k sz).1 = Nat.land (hash k).val.toNat (sz - 1) + 1 := rfl

theorem hashindex_snd (hash : K → JInt .u64) (k : K) (sz : Nat) :
    (hashindex hash k sz).2 = shorthash7 (hash k) := rfl

theorem home_eq {sz : Nat} (h : IsPow sz) (hash : K → JInt .u64) (k : K) :
    home hash sz k = (hash k).val.toNat % sz + 1 := by
  unfold home
  rw [hashindex_fst, h.land]

theorem home_range {sz : Nat} (h : IsPow sz) (hash : K → JInt .u64) (k : K) :
    1 ≤ home hash sz k ∧ home hash sz k ≤ sz := by
  rw [home_eq h]
  have := Nat.mod_lt (hash k).val.toNat (show sz > 0 by have := h.ge; omega)
  omega

/-- The slot at probe distance `d` from `home`: `d` steps `(index & (sz-1)) + 1`. -/
def pr (sz home : Nat) : Nat → Nat
  | 0 => home
  | d + 1 => nextIndex sz (pr sz home d)

theorem pr_succ (sz home d : Nat) : pr sz home (d + 1) = nextIndex sz (pr sz home d) := rfl

theorem pr_spec {sz home : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz) :
    ∀ d, d < sz →
      (home + d ≤ sz ∧ pr sz home d = home + d) ∨ (sz < home + d ∧ pr sz home d = home + d - sz)
  | 0, _ => Or.inl ⟨by omega, rfl⟩
  | d + 1, hd => by
    have ih := pr_spec h h1 h2 d (by omega)
    have hr : 1 ≤ pr sz home d ∧ pr sz home d ≤ sz := by omega
    have hn := nextIndex_spec h hr.1 hr.2
    rw [pr_succ]
    omega

theorem pr_range {sz home d : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz) (hd : d < sz) :
    1 ≤ pr sz home d ∧ pr sz home d ≤ sz := by
  have := pr_spec h h1 h2 d hd
  omega

theorem pr_inj {sz home d d' : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz)
    (hd : d < sz) (hd' : d' < sz) (e : pr sz home d = pr sz home d') : d = d' := by
  have := pr_spec h h1 h2 d hd
  have := pr_spec h h1 h2 d' hd'
  omega

theorem pr_surj {sz home j : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz)
    (hj1 : 1 ≤ j) (hj2 : j ≤ sz) : ∃ d, d < sz ∧ pr sz home d = j := by
  by_cases hc : home ≤ j
  · refine ⟨j - home, by omega, ?_⟩
    have := pr_spec h h1 h2 (j - home) (by omega)
    omega
  · refine ⟨j + sz - home, by omega, ?_⟩
    have := pr_spec h h1 h2 (j + sz - home) (by omega)
    omega

theorem probeDist_pr {sz home d : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ home)
    (h2 : home ≤ sz) (hd : d < sz) : probeDist sz (pr sz home d) home = d := by
  have := pr_spec h h1 h2 d hd
  have hr := pr_range h h1 h2 hd
  have := probeDist_spec h hs hr.1 hr.2 h1 h2
  omega

theorem nextIndex_previousIndex {sz i : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i)
    (h2 : i ≤ sz) :
    nextIndex sz (previousIndex sz i) = i ∧ 1 ≤ previousIndex sz i ∧ previousIndex sz i ≤ sz := by
  have hp := previousIndex_spec h hs h1 h2
  have h16 := h.ge
  have hr : 1 ≤ previousIndex sz i ∧ previousIndex sz i ≤ sz := by omega
  have := nextIndex_spec h hr.1 hr.2
  omega

theorem nextIndex_range {sz i : Nat} (h : IsPow sz) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    1 ≤ nextIndex sz i ∧ nextIndex sz i ≤ sz := by
  have := nextIndex_spec h h1 h2
  have := h.ge
  omega

theorem pr_range_all {sz home : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz) :
    ∀ d, 1 ≤ pr sz home d ∧ pr sz home d ≤ sz
  | 0 => ⟨h1, h2⟩
  | d + 1 => by
    have ih := pr_range_all h h1 h2 d
    exact nextIndex_range h ih.1 ih.2

/-! ## Slot bytes -/

/-- `(b & 0x80) != 0`, the byte test of `isslotfilled`. -/
def filledB (b : Nat) : Bool := Nat.land b 0x80 != 0

theorem isslotfilled_eq (h : DictState K V) (i : Nat) : isslotfilled h i = filledB (h.slots i) := rfl

theorem isslotempty_eq (h : DictState K V) (i : Nat) : isslotempty h i = (h.slots i == 0) := rfl

theorem isslotmissing_eq (h : DictState K V) (i : Nat) : isslotmissing h i = (h.slots i == 0x7f) :=
  rfl

theorem lor128_facts : ∀ y, y < 256 →
    filledB (Nat.lor y 128) = true ∧ Nat.lor y 128 ≠ 0 ∧ Nat.lor y 128 ≠ 127 ∧
      128 ≤ Nat.lor y 128 ∧ Nat.lor y 128 < 256 := by
  decide +kernel

theorem shorthash7_facts (h : JInt .u64) :
    filledB (shorthash7 h) = true ∧ shorthash7 h ≠ 0 ∧ shorthash7 h ≠ 127 :=
  have := lor128_facts _ (Nat.mod_lt (h.val.toNat >>> 57) (by decide))
  ⟨this.1, this.2.1, this.2.2.1⟩

theorem shorthash7_filled (h : JInt .u64) : filledB (shorthash7 h) = true := (shorthash7_facts h).1

theorem shorthash7_ne0 (h : JInt .u64) : shorthash7 h ≠ 0 := (shorthash7_facts h).2.1

theorem shorthash7_ne127 (h : JInt .u64) : shorthash7 h ≠ 127 := (shorthash7_facts h).2.2

theorem filledB_zero : filledB 0 = false := by decide

theorem filledB_127 : filledB 127 = false := by decide

/-! ## `_tablesz` -/

theorem tableszSpec_pow (x : Nat) : IsPow (tableszSpec x) := by
  unfold tableszSpec
  split
  · exact ⟨4, by omega, rfl⟩
  · refine ⟨Nat.log2 (x - 1) + 1, ?_, rfl⟩
    have : 2 ^ 3 ≤ x - 1 := by
      have : (8 : Nat) = 2 ^ 3 := rfl
      omega
    have := (Nat.le_log2 (show x - 1 ≠ 0 by omega)).2 this
    omega

theorem tableszSpec_ge (x : Nat) : x ≤ tableszSpec x := by
  unfold tableszSpec
  split
  · omega
  · have := @Nat.lt_log2_self (x - 1)
    omega

theorem tableszSpec_le (x : Nat) : tableszSpec x ≤ 16 + 2 * x := by
  unfold tableszSpec
  split
  · omega
  · have h := Nat.log2_self_le (show x - 1 ≠ 0 by omega)
    rw [Nat.pow_succ]
    omega

theorem tableszSpec_of_pow {x : Nat} (h : IsPow x) : tableszSpec x = x := by
  obtain ⟨p, hp, rfl⟩ := h
  have h16 : 16 ≤ 2 ^ p := IsPow.ge ⟨p, hp, rfl⟩
  unfold tableszSpec
  split
  · omega
  have hlog : Nat.log2 (2 ^ p - 1) = p - 1 := by
    rw [Nat.log2_eq_iff (by omega)]
    have e : 2 ^ p = 2 ^ (p - 1) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    constructor
    · omega
    · rw [show p - 1 + 1 = p by omega]; omega
  rw [hlog, show p - 1 + 1 = p by omega]

theorem tableszSpec_le_pow {x : Nat} (h : x ≤ 2 ^ 62) : tableszSpec x ≤ 2 ^ 62 := by
  unfold tableszSpec
  split
  · omega
  · have hlog : Nat.log2 (x - 1) < 62 := (Nat.log2_lt (by omega)).2 (by omega)
    exact Nat.pow_le_pow_right (by decide) (by omega)

/-! ## `Except` steps and memory updates -/

@[simp] theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

@[simp] theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = Except.error e := rfl

@[simp] theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = Except.ok a := rfl

theorem bind_of_ok {ε α β : Type} {x : Except ε α} {a : α} (h : x = .ok a) (f : α → Except ε β) :
    (x >>= f) = f a := by subst h; rfl

theorem updateAt_same {α : Type} (f : Nat → α) (i : Nat) (x : α) : updateAt f i x i = x := by
  simp [updateAt]

theorem updateAt_ne {α : Type} (f : Nat → α) {i j : Nat} (x : α) (h : j ≠ i) :
    updateAt f i x j = f j := by
  simp [updateAt, h]

theorem updateAt_self {α : Type} (f : Nat → α) (i : Nat) : updateAt f i (f i) = f := by
  funext j
  by_cases h : j = i
  · rw [h, updateAt_same]
  · rw [updateAt_ne _ _ h]


/-! ## Generic list lemmas -/

theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    have ih := filterMap_congr_mem (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases hg : g a with
    | none => rw [List.filterMap_cons_none (ha.trans hg), List.filterMap_cons_none hg, ih]
    | some b => rw [List.filterMap_cons_some (ha.trans hg), List.filterMap_cons_some hg, ih]

theorem filterMap_update_perm {β : Type} {f g : Nat → Option β} {j : Nat} {e : β} :
    ∀ {l : List Nat}, l.Nodup → j ∈ l → (∀ x ∈ l, x ≠ j → g x = f x) → g j = some e →
      List.Perm (l.filterMap g) (e :: l.filterMap (fun x => if x = j then none else f x))
  | [], _, hj, _, _ => absurd hj List.not_mem_nil
  | a :: l, hnd, hj, hgf, hge => by
    rw [List.nodup_cons] at hnd
    by_cases haj : a = j
    · subst haj
      have hc : l.filterMap g = l.filterMap (fun x => if x = a then none else f x) := by
        apply filterMap_congr_mem
        intro x hx
        have hxa : x ≠ a := fun h => hnd.1 (h ▸ hx)
        rw [ite_eq_right hxa]
        exact hgf x (List.mem_cons_of_mem _ hx) hxa
      have e2 : (a :: l).filterMap (fun x => if x = a then none else f x) =
          l.filterMap (fun x => if x = a then none else f x) :=
        List.filterMap_cons_none (f := fun x => if x = a then none else f x) (by simp)
      rw [List.filterMap_cons_some hge, e2, hc]
    · have hjl : j ∈ l := by
        rcases List.mem_cons.1 hj with h | h
        · exact absurd h.symm haj
        · exact h
      have ih := filterMap_update_perm hnd.2 hjl
        (fun x hx hxj => hgf x (List.mem_cons_of_mem _ hx) hxj) hge
      have hga : g a = f a := hgf a List.mem_cons_self haj
      cases hfa : f a with
      | none =>
        have e2 : (a :: l).filterMap (fun x => if x = j then none else f x) =
            l.filterMap (fun x => if x = j then none else f x) :=
          List.filterMap_cons_none (f := fun x => if x = j then none else f x) (by simp [haj, hfa])
        rw [List.filterMap_cons_none (hga.trans hfa), e2]
        exact ih
      | some b =>
        have e2 : (a :: l).filterMap (fun x => if x = j then none else f x) =
            b :: l.filterMap (fun x => if x = j then none else f x) :=
          List.filterMap_cons_some (f := fun x => if x = j then none else f x) (by simp [haj, hfa])
        rw [List.filterMap_cons_some (hga.trans hfa), e2]
        exact (List.Perm.cons b ih).trans (List.Perm.swap e b _)

theorem filterMap_erase_eq_filter {β : Type} {f : Nat → Option β} {j : Nat} {p : β → Bool}
    {l : List Nat} (h : ∀ x ∈ l, ∀ b, f x = some b → (p b = true ↔ x ≠ j)) :
    l.filterMap (fun x => if x = j then none else f x) = (l.filterMap f).filter p := by
  rw [List.filter_filterMap]
  apply filterMap_congr_mem
  intro x hx
  show (if x = j then none else f x) = (f x).filter p
  cases hf : f x with
  | none => split <;> rfl
  | some b =>
    have hb := h x hx b hf
    by_cases hxj : x = j
    · have hp : p b = false := by
        cases hp : p b
        · rfl
        · exact absurd (hb.1 hp) (fun h => h hxj)
      rw [ite_eq_left hxj, Option.filter_some_neg hp]
    · rw [ite_eq_right hxj, Option.filter_some_pos (hb.2 hxj)]

/-! ## The table invariant and its abstraction -/

/-- The pair stored at slot `i`, if the slot is filled. -/
def ent (t : DictState K V) (i : Nat) : Option (K × V) :=
  if filledB (t.slots i) then
    match t.keys i, t.vals i with
    | some k, some v => some (k, v)
    | _, _ => none
  else none

/-- The stored pairs in slot order. -/
def tlist (t : DictState K V) : List (K × V) := (List.range' 1 t.size).filterMap (ent t)

/-- Slot `i` lies on the probe sequence of `k`, within `maxprobe` steps and after non-empty
slots only. -/
def Chain (hash : K → JInt .u64) (t : DictState K V) (k : K) (i : Nat) : Prop :=
  ∃ d, d ≤ t.maxprobe ∧ i = pr t.size (home hash t.size k) d ∧
    ∀ e, e < d → t.slots (pr t.size (home hash t.size k) e) ≠ 0

/-- Slot `i` is empty, deleted, or filled with a reachable key. -/
def SlotOK (hash : K → JInt .u64) (t : DictState K V) (i : Nat) : Prop :=
  t.slots i = 0 ∨ t.slots i = 127 ∨
  ∃ k v, t.keys i = some k ∧ t.vals i = some v ∧ t.slots i = shorthash7 (hash k) ∧ Chain hash t k i

/-- The invariant of every `Dict` built by the API (`base/dict.jl:65-90`): `slots` holds
`0x00` (empty), `0x7f` (deleted) or `0x80 | shorthash` (full), every full slot is reachable
from its key's home slot within `maxprobe` steps over non-empty slots, keys are pairwise
non-`isequal`, `count` is the number of full slots, and `idxfloor` is at most every used
index. -/
structure Inv (hash : K → JInt .u64) (eqKey : K → K → Bool) (t : DictState K V) : Prop where
  size : t.size = 0 ∨ IsPow t.size
  sizeLe : t.size ≤ 2 ^ 62
  slot : ∀ i, 1 ≤ i → i ≤ t.size → SlotOK hash t i
  distinct : ∀ i j a b, 1 ≤ i → i ≤ t.size → 1 ≤ j → j ≤ t.size → i ≠ j →
    ent t i = some a → ent t j = some b → eqKey a.1 b.1 = false
  count : t.count = (tlist t).length
  maxprobe : t.size = 0 ∨ t.maxprobe < t.size
  idxfloor : 1 ≤ t.idxfloor
  floorLe : ∀ i, 1 ≤ i → i ≤ t.size → filledB (t.slots i) = true → t.idxfloor ≤ i
  popcursor : 1 ≤ t.popcursor

/-- `h` is a well-formed `Dict` whose stored pairs are the pairs of `m`. -/
def DictRep (hash : K → JInt .u64) (eqKey : K → K → Bool) (h : DictState K V)
    (m : List (K × V)) : Prop :=
  Inv hash eqKey h ∧ List.Perm (tlist h) m

theorem ent_some {t : DictState K V} {i : Nat} {e : K × V} (h : ent t i = some e) :
    filledB (t.slots i) = true ∧ t.keys i = some e.1 ∧ t.vals i = some e.2 := by
  unfold ent at h
  split at h
  · split at h
    · cases h; exact ⟨‹_›, ‹_›, ‹_›⟩
    · cases h
  · cases h

theorem ent_of_not_filled {t : DictState K V} {i : Nat} (h : filledB (t.slots i) = false) :
    ent t i = none := by
  unfold ent
  simp [h]

theorem ent_of_filled {t : DictState K V} {i : Nat} {k : K} {v : V}
    (h : filledB (t.slots i) = true) (hk : t.keys i = some k) (hv : t.vals i = some v) :
    ent t i = some (k, v) := by
  unfold ent
  rw [ite_eq_left h, hk, hv]

theorem mem_tlist {t : DictState K V} {e : K × V} :
    e ∈ tlist t ↔ ∃ i, 1 ≤ i ∧ i ≤ t.size ∧ ent t i = some e := by
  unfold tlist
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [List.mem_range'_1] at hi
    exact ⟨i, hi.1, by omega, he⟩
  · rintro ⟨i, h1, h2, he⟩
    exact ⟨i, List.mem_range'_1.2 ⟨h1, by omega⟩, he⟩

theorem nodup_range'1 (s n : Nat) : (List.range' s n).Nodup := List.nodup_range'

section Inv
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}

/-- Filled slots of an invariant table. -/
theorem Inv.filled {t : DictState K V} (hi : Inv hash eqKey t) {i : Nat} (h1 : 1 ≤ i)
    (h2 : i ≤ t.size) (hf : filledB (t.slots i) = true) :
    ∃ k v, t.keys i = some k ∧ t.vals i = some v ∧ ent t i = some (k, v) ∧
      t.slots i = shorthash7 (hash k) ∧ Chain hash t k i := by
  rcases hi.slot i h1 h2 with h | h | ⟨k, v, hk, hv, hs, hc⟩
  · rw [h, filledB_zero] at hf; cases hf
  · rw [h, filledB_127] at hf; cases hf
  · exact ⟨k, v, hk, hv, ent_of_filled hf hk hv, hs, hc⟩

theorem tlist_pairwise {t : DictState K V} (hi : Inv hash eqKey t) :
    (tlist t).Pairwise (fun a b => eqKey a.1 b.1 = false) := by
  unfold tlist
  apply List.Pairwise.filterMap (R := fun x y : Nat => x < y ∧ 1 ≤ x ∧ y ≤ t.size)
  · intro x y hxy a ha b hb
    exact hi.distinct x y a b hxy.2.1 (by omega) (by omega) hxy.2.2 (by omega) ha hb
  · have hl := List.pairwise_lt_range' (s := 1) (n := t.size)
    refine hl.imp_of_mem ?_
    intro x y hx hy hxy
    rw [List.mem_range'_1] at hx hy
    exact ⟨hxy, hx.1, by omega⟩

theorem Inv.count_le_size {t : DictState K V} (hi : Inv hash eqKey t) : t.count ≤ t.size := by
  rw [hi.count]
  unfold tlist
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

end Inv

/-- A table with the same slots, keys and filled values. -/
theorem tlist_congr {t t' : DictState K V} (hs : t'.size = t.size)
    (he : ∀ i, 1 ≤ i → i ≤ t.size → ent t' i = ent t i) : tlist t' = tlist t := by
  unfold tlist
  rw [hs]
  apply filterMap_congr_mem
  intro x hx
  rw [List.mem_range'_1] at hx
  exact he x hx.1 (by omega)

/-- Storing `e` at slot `j`. -/
theorem tlist_store {eqKey : K → K → Bool} {t t' : DictState K V} {j : Nat} {e : K × V}
    (hs : t'.size = t.size) (hj1 : 1 ≤ j) (hj2 : j ≤ t.size)
    (he : ∀ i, 1 ≤ i → i ≤ t.size → ent t' i = if i = j then some e else ent t i)
    (hdis : ∀ i b, 1 ≤ i → i ≤ t.size → i ≠ j → ent t i = some b → eqKey e.1 b.1 = false)
    (hsame : ∀ b, ent t j = some b → eqKey e.1 b.1 = true) :
    List.Perm (tlist t') (e :: (tlist t).filter (fun b => !eqKey e.1 b.1)) := by
  unfold tlist
  rw [hs]
  have hmem : j ∈ List.range' 1 t.size := List.mem_range'_1.2 ⟨hj1, by omega⟩
  have h1 := filterMap_update_perm (f := ent t) (g := ent t') (j := j) (e := e)
    (nodup_range'1 1 t.size) hmem
    (fun x hx hxj => by
      rw [List.mem_range'_1] at hx
      rw [he x hx.1 (by omega), ite_eq_right hxj])
    (by rw [he j hj1 hj2, ite_eq_left rfl])
  refine h1.trans (List.Perm.cons e ?_)
  rw [filterMap_erase_eq_filter (p := fun b => !eqKey e.1 b.1)]
  intro x hx b hb
  rw [List.mem_range'_1] at hx
  by_cases hxj : x = j
  · subst hxj
    simp [hsame b hb]
  · simp [hdis x b hx.1 (by omega) hxj hb, hxj]

/-- Clearing slot `j`. -/
theorem tlist_clear {eqKey : K → K → Bool} {t t' : DictState K V} {j : Nat} {k : K}
    (hs : t'.size = t.size)
    (he : ∀ i, 1 ≤ i → i ≤ t.size → ent t' i = if i = j then none else ent t i)
    (hdis : ∀ i b, 1 ≤ i → i ≤ t.size → i ≠ j → ent t i = some b → eqKey k b.1 = false)
    (hsame : ∀ b, ent t j = some b → eqKey k b.1 = true) :
    tlist t' = (tlist t).filter (fun b => !eqKey k b.1) := by
  unfold tlist
  rw [hs]
  rw [filterMap_congr_mem (f := ent t') (g := fun x => if x = j then none else ent t x) (fun x hx => by
    rw [List.mem_range'_1] at hx
    exact he x hx.1 (by omega))]
  rw [filterMap_erase_eq_filter (p := fun b => !eqKey k b.1)]
  intro x hx b hb
  rw [List.mem_range'_1] at hx
  by_cases hxj : x = j
  · subst hxj
    simp [hsame b hb]
  · simp [hdis x b hx.1 (by omega) hxj hb, hxj]

/-- A chain survives a larger `maxprobe` and slots that stay non-empty. -/
theorem Chain.mono {hash : K → JInt .u64} {t t' : DictState K V} {k : K} {i : Nat}
    (hpow : IsPow t.size) (hmp : t.maxprobe < t.size)
    (hs : t'.size = t.size) (hm : t.maxprobe ≤ t'.maxprobe)
    (hne : ∀ p, 1 ≤ p → p ≤ t.size → t.slots p ≠ 0 → t'.slots p ≠ 0)
    (hc : Chain hash t k i) : Chain hash t' k i := by
  obtain ⟨d, hd, hi, hall⟩ := hc
  refine ⟨d, Nat.le_trans hd hm, by rw [hs]; exact hi, fun e he => ?_⟩
  rw [hs]
  have hr := pr_range hpow (home_range hpow hash k).1 (home_range hpow hash k).2
    (show e < t.size by omega)
  exact hne _ hr.1 hr.2 (hall e he)

/-- `isequal` keys have equal homes. -/
theorem home_eq_of_eq {hash : K → JInt .u64} {eqKey : K → K → Bool} (hl : KeyLaws hash eqKey)
    {a b : K} (h : eqKey a b = true) (sz : Nat) : home hash sz a = home hash sz b := by
  unfold home hashindex
  rw [hl.hash_eq a b h]

theorem SlotOK.transfer {hash : K → JInt .u64} {t t' : DictState K V} {i : Nat}
    (h : SlotOK hash t i) (hs : t'.slots i = t.slots i) (hk : t'.keys i = t.keys i)
    (hv : t'.vals i = t.vals i) (hc : ∀ k, Chain hash t k i → Chain hash t' k i) :
    SlotOK hash t' i := by
  rcases h with h | h | ⟨k, v, h1, h2, h3, h4⟩
  · exact Or.inl (hs.trans h)
  · exact Or.inr (Or.inl (hs.trans h))
  · exact Or.inr (Or.inr ⟨k, v, hk.trans h1, hv.trans h2, hs.trans h3, hc k h4⟩)

theorem filled_ne_zero {b : Nat} (h : filledB b = true) : b ≠ 0 := by
  intro h0
  rw [h0, filledB_zero] at h
  cases h

theorem filled_ne_127 {b : Nat} (h : filledB b = true) : b ≠ 127 := by
  intro h0
  rw [h0, filledB_127] at h
  cases h

/-- A slot of an invariant table is empty, deleted, or filled. -/
theorem Inv.byte {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    (hi : Inv hash eqKey t) {i : Nat} (h1 : 1 ≤ i) (h2 : i ≤ t.size) :
    t.slots i = 0 ∨ t.slots i = 127 ∨ filledB (t.slots i) = true := by
  rcases hi.slot i h1 h2 with h | h | ⟨k, -, -, -, hs, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [hs]; exact shorthash7_filled _))

/-- Stored keys of a table are not `isequal` to `q`. -/
def Absent (eqKey : K → K → Bool) (t : DictState K V) (q : K) : Prop :=
  ∀ e ∈ tlist t, eqKey q e.1 = false

/-! ## Reference maps: association lists with pairwise non-`isequal` keys -/

/-- Removing every pair whose key is `isequal` to the query `q`. -/
def rdel {Q : Type} (matchQ : Q → K → Bool) (m : List (K × V)) (q : Q) : List (K × V) :=
  m.filter (fun e => !matchQ q e.1)
/-- Setting a key stores the new key object (`h.keys[index] = key`, `base/dict.jl:365`). -/
def rset (eqKey : K → K → Bool) (m : List (K × V)) (k : K) (v : V) : List (K × V) :=
  (k, v) :: rdel eqKey m k
/-- The stored pair whose key is `isequal` to the query `q` (of any type). -/
def rfind {Q : Type} (matchQ : Q → K → Bool) (m : List (K × V)) (q : Q) : Option (K × V) :=
  m.find? (fun e => matchQ q e.1)
def rlookup {Q : Type} (matchQ : Q → K → Bool) (m : List (K × V)) (q : Q) : Option V :=
  (rfind matchQ m q).map (·.2)

/-- `isequal(q, k)` for a query `q` of type `Q` and stored keys of type `K`: equal queries
hash like the key, the relation respects `isequal` on keys, and a query is `isequal` to at most
one class of keys. -/
structure QueryLaws (hash : K → JInt .u64) (eqKey : K → K → Bool) {Q : Type}
    (hashQ : Q → JInt .u64) (matchQ : Q → K → Bool) : Prop where
  hash_eq : ∀ q k, matchQ q k = true → hashQ q = hash k
  congr : ∀ q a b, matchQ q a = true → eqKey a b = true → matchQ q b = true
  unique : ∀ q a b, matchQ q a = true → matchQ q b = true → eqKey a b = true

/-- Keys pairwise non-`isequal`. -/
abbrev Distinct (eqKey : K → K → Bool) (m : List (K × V)) : Prop :=
  m.Pairwise (fun a b => eqKey a.1 b.1 = false)

section Ref
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}

theorem eq_false_symm (hl : KeyLaws hash eqKey) {a b : K} (h : eqKey a b = false) :
    eqKey b a = false := by
  cases hb : eqKey b a
  · rfl
  · rw [hl.symm b a hb] at h; cases h

theorem eq_trans' (hl : KeyLaws hash eqKey) {q a b : K} (h1 : eqKey q a = true)
    (h2 : eqKey q b = true) : eqKey a b = true :=
  hl.trans a q b (hl.symm q a h1) h2

theorem Distinct.perm (hl : KeyLaws hash eqKey) {m m' : List (K × V)} (h : Distinct eqKey m)
    (hp : List.Perm m m') : Distinct eqKey m' :=
  hp.pairwise h (fun h => eq_false_symm hl h)

theorem KeyLaws.query (hl : KeyLaws hash eqKey) : QueryLaws hash eqKey hash eqKey :=
  ⟨hl.hash_eq, fun q a b h1 h2 => hl.trans q a b h1 h2, fun q a b h1 h2 => eq_trans' hl h1 h2⟩

theorem rfind_of_mem {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {m : List (K × V)} (hd : Distinct eqKey m) {q : Q}
    {e : K × V} (he : e ∈ m) (hm : matchQ q e.1 = true) : rfind matchQ m q = some e := by
  induction m with
  | nil => cases he
  | cons a m ih =>
    replace hd := List.pairwise_cons.1 hd
    unfold rfind
    by_cases ha : matchQ q a.1 = true
    · rw [List.find?_cons_of_pos (p := fun e : K × V => matchQ q e.1) ha]
      rcases List.mem_cons.1 he with h | h
      · rw [h]
      · have h1 := hd.1 e h
        rw [hq.unique q a.1 e.1 ha hm] at h1
        cases h1
    · rw [List.find?_cons_of_neg (p := fun e : K × V => matchQ q e.1) ha]
      rcases List.mem_cons.1 he with h | h
      · subst h; exact absurd hm ha
      · exact ih hd.2 h

end Ref

theorem rfind_none {Q : Type} {matchQ : Q → K → Bool} {m : List (K × V)} {q : Q}
    (h : ∀ e ∈ m, matchQ q e.1 = false) : rfind matchQ m q = none := by
  unfold rfind
  rw [List.find?_eq_none]
  intro x hx
  have := h x hx
  simp [this]

theorem rfind_some {Q : Type} {matchQ : Q → K → Bool} {m : List (K × V)} {q : Q} {e : K × V}
    (h : rfind matchQ m q = some e) : e ∈ m ∧ matchQ q e.1 = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some (p := fun e : K × V => matchQ q e.1) h⟩

theorem rfind_eq_none_iff {Q : Type} {matchQ : Q → K → Bool} {m : List (K × V)} {q : Q} :
    rfind matchQ m q = none ↔ ∀ e ∈ m, matchQ q e.1 = false := by
  unfold rfind
  rw [List.find?_eq_none]
  constructor
  · intro h e he
    cases hq : matchQ q e.1
    · rfl
    · exact absurd hq (h e he)
  · intro h e he
    have := h e he
    simp [this]

/-- Lookups only depend on the elements of a distinct list. -/
theorem rfind_perm {hash : K → JInt .u64} {eqKey : K → K → Bool} (hl : KeyLaws hash eqKey)
    {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ)
    {m m' : List (K × V)} (hd : Distinct eqKey m) (hp : List.Perm m m') (q : Q) :
    rfind matchQ m q = rfind matchQ m' q := by
  have hd' := hd.perm hl hp
  cases h : rfind matchQ m q with
  | none =>
    symm
    rw [rfind_eq_none_iff] at h ⊢
    exact fun e he => h e (hp.mem_iff.2 he)
  | some e =>
    have := rfind_some h
    exact (rfind_of_mem hq hd' (hp.mem_iff.1 this.1) this.2).symm

theorem distinct_filter {eqKey : K → K → Bool} {m : List (K × V)} (h : Distinct eqKey m)
    (p : K × V → Bool) : Distinct eqKey (m.filter p) :=
  List.Pairwise.sublist List.filter_sublist h

theorem distinct_rset {eqKey : K → K → Bool} {m : List (K × V)} (h : Distinct eqKey m) (k : K)
    (v : V) : Distinct eqKey (rset eqKey m k v) := by
  unfold rset rdel
  refine List.pairwise_cons.2 ⟨fun b hb => ?_, distinct_filter h _⟩
  show eqKey k b.1 = false
  rw [List.mem_filter] at hb
  cases hk : eqKey k b.1
  · rfl
  · rw [hk] at hb; exact absurd hb.2 (by decide)

theorem distinct_rdel {eqKey : K → K → Bool} {Q : Type} {matchQ : Q → K → Bool}
    {m : List (K × V)} (h : Distinct eqKey m) (q : Q) :
    Distinct eqKey (rdel matchQ m q) := distinct_filter h _

theorem mem_rdel {Q : Type} {matchQ : Q → K → Bool} {m : List (K × V)} {q : Q} {e : K × V} :
    e ∈ rdel matchQ m q ↔ e ∈ m ∧ matchQ q e.1 = false := by
  unfold rdel
  rw [List.mem_filter]
  cases matchQ q e.1 <;> simp

theorem mem_rset {eqKey : K → K → Bool} {m : List (K × V)} {k : K} {v : V} {e : K × V} :
    e ∈ rset eqKey m k v ↔ e = (k, v) ∨ (e ∈ m ∧ eqKey k e.1 = false) := by
  unfold rset
  rw [List.mem_cons, mem_rdel]

/-! ## `age` arithmetic -/

/-- `age` advanced by `n` increments. -/
def ageAdd (a : JInt .u64) (n : Nat) : JInt .u64 := JInt.wrap .u64 (a.val + n)

theorem u64_val_range (a : JInt .u64) : 0 ≤ a.val ∧ a.val < 2 ^ 64 := by
  have h := a.property
  have h1 : IntTy.min .u64 = 0 := by decide
  have h2 : IntTy.max .u64 = 2 ^ 64 - 1 := by decide
  omega

theorem ageAdd_val (a : JInt .u64) (n : Nat) : (ageAdd a n).val = (a.val + n) % 2 ^ 64 := rfl

theorem ageAdd_zero (a : JInt .u64) : ageAdd a 0 = a := by
  apply Subtype.ext
  rw [ageAdd_val]
  have := u64_val_range a
  omega

theorem ageAdd_add (a : JInt .u64) (n k : Nat) : ageAdd (ageAdd a n) k = ageAdd a (n + k) := by
  apply Subtype.ext
  rw [ageAdd_val, ageAdd_val, ageAdd_val]
  omega

theorem bump_eq (a : JInt .u64) : bumpAge a = ageAdd a 1 := by
  have h1 : (JInt.lit .u64 1).val = 1 := by decide
  show JInt.wrap .u64 (a.val + (JInt.lit .u64 1).val) = JInt.wrap .u64 (a.val + ((1 : Nat) : Int))
  rw [h1] <;> rfl

theorem bump_ageAdd (a : JInt .u64) (n : Nat) : bumpAge (ageAdd a n) = ageAdd a (n + 1) := by
  rw [bump_eq, ageAdd_add]

theorem bump_bump (a : JInt .u64) : bumpAge (bumpAge a) = ageAdd a 2 := by
  rw [bump_eq, bump_eq, ageAdd_add]

theorem ageAdd_ne (a : JInt .u64) {n : Nat} (h1 : 0 < n) (h2 : n < 2 ^ 64) :
    (ageAdd a n).val ≠ a.val := by
  rw [ageAdd_val]
  have := u64_val_range a
  omega

/-- `t'` keeps the slots and keys of `t` and at least its `maxprobe`. -/
def Same (t t' : DictState K V) : Prop :=
  t'.size = t.size ∧ t'.slots = t.slots ∧ t'.keys = t.keys ∧ t.maxprobe ≤ t'.maxprobe

theorem Same.refl (t : DictState K V) : Same t t := ⟨rfl, rfl, rfl, Nat.le_refl _⟩

theorem Same.trans {t1 t2 t3 : DictState K V} (h1 : Same t1 t2) (h2 : Same t2 t3) : Same t1 t3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, Nat.le_trans h1.2.2.2 h2.2.2.2⟩

/-- A table operation advanced the age by `n`, and left slots and keys alone when `n = 0`. -/
def AgeStep (t t' : DictState K V) (n : Nat) : Prop :=
  t'.age = ageAdd t.age n ∧ (n = 0 → Same t t')

theorem AgeStep.refl (t : DictState K V) : AgeStep t t 0 :=
  ⟨(ageAdd_zero _).symm, fun _ => Same.refl t⟩

theorem AgeStep.trans {t1 t2 t3 : DictState K V} {n1 n2 : Nat} (h1 : AgeStep t1 t2 n1)
    (h2 : AgeStep t2 t3 n2) : AgeStep t1 t3 (n1 + n2) :=
  ⟨by rw [h2.1, h1.1, ageAdd_add], fun h => (h1.2 (by omega)).trans (h2.2 (by omega))⟩

theorem AgeStep.of_pos {t t' : DictState K V} {n : Nat} (h : t'.age = ageAdd t.age n)
    (hn : 0 < n) : AgeStep t t' n := ⟨h, fun h0 => absurd h0 (by omega)⟩


/-! ## Lookup: `ht_keyindex` -/

/-- The tag and key test of the probe loops at slot `j`. -/
def hitAt {Q : Type} (t : DictState K V) (sh : Nat) (m : Q → K → Bool) (q : Q) (j : Nat) : Bool :=
  sh == t.slots j && (match t.keys j with | some k => m q k | none => false)

theorem hitAt_true {Q : Type} {t : DictState K V} {sh : Nat} {m : Q → K → Bool} {q : Q} {j : Nat}
    (h : hitAt t sh m q j = true) : t.slots j = sh ∧ ∃ k, t.keys j = some k ∧ m q k = true := by
  unfold hitAt at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1.symm, ?_⟩
  cases hk : t.keys j with
  | none => rw [hk] at h; exact absurd h.2 (by simp)
  | some k => rw [hk] at h; exact ⟨k, rfl, h.2⟩

theorem hitAt_of {Q : Type} {t : DictState K V} {sh : Nat} {m : Q → K → Bool} {q : Q} {j : Nat}
    {k : K} (hs : t.slots j = sh) (hk : t.keys j = some k) (hm : m q k = true) :
    hitAt t sh m q j = true := by
  unfold hitAt
  rw [hk, hs]
  simp [hm]

theorem keyindexLoop_succ {Q : Type} (m : Q → K → Bool) (q : Q) (t : DictState K V)
    (sh left index : Nat) :
    keyindexLoop m q t sh (left + 1) index =
      if isslotempty t index then .ok (-1)
      else if sh == t.slots index then
        (match t.keys index with
         | none => .error .undefRef
         | some k =>
           if m q k then .ok (index : Int) else keyindexLoop m q t sh left (nextIndex t.size index))
      else keyindexLoop m q t sh left (nextIndex t.size index) := rfl

/-- One step of the lookup loop at a slot whose matching tag has a defined key. -/
theorem keyindexLoop_step {Q : Type} (m : Q → K → Bool) (q : Q) (t : DictState K V)
    (sh left index : Nat) (hdef : t.slots index = sh → ∃ k, t.keys index = some k) :
    keyindexLoop m q t sh (left + 1) index =
      if t.slots index = 0 then .ok (-1)
      else if hitAt t sh m q index then .ok (index : Int)
      else keyindexLoop m q t sh left (nextIndex t.size index) := by
  rw [keyindexLoop_succ, isslotempty_eq]
  by_cases h0 : t.slots index = 0
  · rw [ite_eq_left (by simp [h0]), ite_eq_left h0]
  · rw [ite_eq_right (by simp [h0]), ite_eq_right h0]
    by_cases hs : t.slots index = sh
    · obtain ⟨k, hk⟩ := hdef hs
      have hb : (sh == t.slots index) = true := by simp [hs]
      rw [ite_eq_left hb, hk]
      unfold hitAt
      rw [hb, hk, Bool.true_and]
    · have hb : ¬ (sh == t.slots index) = true := by simp [Ne.symm hs]
      rw [ite_eq_right hb]
      unfold hitAt
      rw [ite_eq_right (by simp [Ne.symm hs])]

/-- The loop returns `-1` or a hit on a slot satisfying any predicate stable under the step. -/
theorem keyindexLoop_cases {Q : Type} (m : Q → K → Bool) (q : Q) (t : DictState K V) (sh : Nat)
    (P : Nat → Prop) (hP : ∀ j, P j → P (nextIndex t.size j))
    (hdef : ∀ j, P j → t.slots j = sh → ∃ k, t.keys j = some k) :
    ∀ left index, P index →
      keyindexLoop m q t sh left index = .ok (-1) ∨
      ∃ j, P j ∧ hitAt t sh m q j = true ∧ keyindexLoop m q t sh left index = .ok (j : Int)
  | 0, _, _ => Or.inl rfl
  | left + 1, index, hp => by
    rw [keyindexLoop_step m q t sh left index (hdef index hp)]
    split
    · exact Or.inl rfl
    · split
      · next hh => exact Or.inr ⟨index, hp, hh, rfl⟩
      · exact keyindexLoop_cases m q t sh P hP hdef left _ (hP _ hp)

/-- The loop stops at the first hit on a probe sequence over non-empty slots. -/
theorem keyindexLoop_found {Q : Type} (m : Q → K → Bool) (q : Q) (t : DictState K V) (sh h d : Nat)
    (hdef : ∀ e, t.slots (pr t.size h e) = sh → ∃ k, t.keys (pr t.size h e) = some k) :
    ∀ left a, a ≤ d → d < a + left →
      (∀ e, a ≤ e → e < d → t.slots (pr t.size h e) ≠ 0 ∧ hitAt t sh m q (pr t.size h e) = false) →
      hitAt t sh m q (pr t.size h d) = true → t.slots (pr t.size h d) ≠ 0 →
      keyindexLoop m q t sh left (pr t.size h a) = .ok (pr t.size h d : Int)
  | 0, _, h1, h2, _, _, _ => absurd h2 (by omega)
  | left + 1, a, h1, h2, hbefore, hhit, hne => by
    rw [keyindexLoop_step m q t sh left _ (hdef a)]
    by_cases had : a = d
    · subst had
      rw [ite_eq_right hne, ite_eq_left hhit]
    · have hb := hbefore a (Nat.le_refl _) (by omega)
      rw [ite_eq_right hb.1, ite_eq_right (by rw [hb.2]; decide)]
      exact keyindexLoop_found m q t sh h d hdef left (a + 1) (by omega) (by omega)
        (fun e he1 he2 => hbefore e (by omega) he2) hhit hne

section Lookup
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}

/-- A non-empty invariant table has a power-of-two size and `maxprobe < size`. -/
theorem Inv.pow_of_count {t : DictState K V} (hi : Inv hash eqKey t) (hc : t.count ≠ 0) :
    IsPow t.size ∧ t.maxprobe < t.size := by
  have hs : t.size ≠ 0 := by
    intro h0
    apply hc
    rw [hi.count]
    unfold tlist
    rw [h0]
    rfl
  rcases hi.size with h | h
  · exact absurd h hs
  · rcases hi.maxprobe with h' | h'
    · exact absurd h' hs
    · exact ⟨h, h'⟩

theorem Inv.count_pos {t : DictState K V} (hi : Inv hash eqKey t) {i : Nat} {e : K × V}
    (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some e) : t.count ≠ 0 := by
  rw [hi.count]
  have : e ∈ tlist t := mem_tlist.2 ⟨i, h1, h2, he⟩
  intro h0
  rw [List.length_eq_zero_iff] at h0
  rw [h0] at this
  cases this

/-- A slot holding a filled tag has a defined key. -/
theorem Inv.key_of_tag {t : DictState K V} (hi : Inv hash eqKey t) {j : Nat} (hpow : IsPow t.size)
    (hh : 1 ≤ j ∧ j ≤ t.size) {b : JInt .u64} (hs : t.slots j = shorthash7 b) :
    ∃ k, t.keys j = some k := by
  have hf : filledB (t.slots j) = true := by rw [hs]; exact shorthash7_filled _
  obtain ⟨k, -, hk, -⟩ := hi.filled hh.1 hh.2 hf
  exact ⟨k, hk⟩

/-- `ht_keyindex` on an invariant table, when non-empty. -/
theorem htKeyindex_unfold {Q : Type} {t : DictState K V} (hi : Inv hash eqKey t) (hc : t.count ≠ 0)
    (hashQ : Q → JInt .u64) (m : Q → K → Bool) (q : Q) :
    htKeyindex hashQ m t q =
      keyindexLoop m q t (shorthash7 (hashQ q)) (t.maxprobe + 1) (home hashQ t.size q) := by
  have hp := hi.pow_of_count hc
  have h0 : isempty t = false := by simp [isempty, hc]
  unfold htKeyindex
  rw [h0]
  simp only [Bool.false_eq_true, ite_false]
  rw [ite_eq_right (by simp [hp.2])]
  rfl

theorem htKeyindex_found {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V} (hi : Inv hash eqKey t) {q : Q}
    {i : Nat} {k : K} {v : V} (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some (k, v))
    (hm : matchQ q k = true) : htKeyindex hashQ matchQ t q = .ok (i : Int) := by
  have hc := hi.count_pos h1 h2 he
  have hp := hi.pow_of_count hc
  rw [htKeyindex_unfold hi hc]
  have hfill := (ent_some he).1
  obtain ⟨k', v', hk, hv, -, hs, hch⟩ := hi.filled h1 h2 hfill
  have hkk : k' = k := by rw [(ent_some he).2.1] at hk; cases hk; rfl
  subst hkk
  obtain ⟨d, hd, hid, hall⟩ := hch
  have hhash : hashQ q = hash k' := hq.hash_eq q k' hm
  have hh : home hash t.size k' = home hashQ t.size q := by
    unfold home hashindex; rw [hhash]
  have hhr := home_range hp.1 hash k'
  rw [← hh]
  have hsh : shorthash7 (hashQ q) = shorthash7 (hash k') := by rw [hhash]
  rw [hid]
  apply keyindexLoop_found matchQ q t (shorthash7 (hashQ q)) (home hash t.size k') d
    (fun e hs' => hi.key_of_tag hp.1 (pr_range_all hp.1 hhr.1 hhr.2 e) hs')
    (t.maxprobe + 1) 0 (Nat.zero_le _) (by omega)
  · intro e _ hed
    refine ⟨hall e hed, ?_⟩
    cases hhit : hitAt t (shorthash7 (hashQ q)) matchQ q (pr t.size (home hash t.size k') e)
    · rfl
    · exfalso
      obtain ⟨hs', k2, hk2, hm2⟩ := hitAt_true hhit
      have hr := pr_range hp.1 hhr.1 hhr.2 (show e < t.size by omega)
      have hf2 : filledB (t.slots (pr t.size (home hash t.size k') e)) = true := by
        rw [hs']; exact shorthash7_filled _
      obtain ⟨k3, v3, hk3, -, he3, -, -⟩ := hi.filled hr.1 hr.2 hf2
      rw [hk2] at hk3
      cases hk3
      have hne : pr t.size (home hash t.size k') e ≠ i := by
        intro heq
        rw [hid] at heq
        have := pr_inj hp.1 hhr.1 hhr.2 (show e < t.size by omega) (show d < t.size by omega) heq
        omega
      have hdis := hi.distinct _ i _ _ hr.1 hr.2 h1 h2 hne he3 he
      dsimp only at hdis
      rw [hq.unique q k2 k' hm2 hm] at hdis
      cases hdis
  · exact hitAt_of (by rw [← hid, hs, hsh]) (by rw [← hid]; exact hk) hm
  · rw [← hid, hs]; exact shorthash7_ne0 _

theorem htKeyindex_absent {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    {t : DictState K V} (hi : Inv hash eqKey t) {q : Q}
    (habs : ∀ e ∈ tlist t, matchQ q e.1 = false) : htKeyindex hashQ matchQ t q = .ok (-1) := by
  by_cases hc : t.count = 0
  · have h0 : isempty t = true := by simp [isempty, hc]
    unfold htKeyindex
    rw [h0]
    rfl
  have hp := hi.pow_of_count hc
  rw [htKeyindex_unfold hi hc]
  have hr := home_range hp.1 hashQ q
  rcases keyindexLoop_cases matchQ q t (shorthash7 (hashQ q)) (fun j => 1 ≤ j ∧ j ≤ t.size)
      (fun j hj => nextIndex_range hp.1 hj.1 hj.2) (fun j hj hs => hi.key_of_tag hp.1 hj hs)
      (t.maxprobe + 1) _ hr with h | ⟨j, hj, hhit, _⟩
  · exact h
  · exfalso
    obtain ⟨hs, k2, hk2, hm2⟩ := hitAt_true hhit
    have hf2 : filledB (t.slots j) = true := by rw [hs]; exact shorthash7_filled _
    obtain ⟨k3, v3, hk3, -, he3, -, -⟩ := hi.filled hj.1 hj.2 hf2
    rw [hk2] at hk3
    cases hk3
    have := habs _ (mem_tlist.2 ⟨j, hj.1, hj.2, he3⟩)
    rw [hm2] at this
    cases this

theorem valAt_of_ent {t : DictState K V} {i : Nat} {k : K} {v : V} (he : ent t i = some (k, v)) :
    valAt t i = .ok v := by
  unfold valAt
  rw [(ent_some he).2.2]

theorem keyAt_of_ent {t : DictState K V} {i : Nat} {k : K} {v : V} (he : ent t i = some (k, v)) :
    keyAt t i = .ok k := by
  unfold keyAt
  rw [(ent_some he).2.1]

/-- `ht_keyindex` on a table that represents `m`. -/
theorem DictRep.htKeyindex {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V}
    {m : List (K × V)} (h : DictRep hash eqKey t m) (q : Q) :
    match rfind matchQ m q with
    | some e => ∃ i : Nat, JuliaLean.base.dict.htKeyindex hashQ matchQ t q = .ok (i : Int) ∧
        1 ≤ i ∧ i ≤ t.size ∧ ent t i = some e
    | none => JuliaLean.base.dict.htKeyindex hashQ matchQ t q = .ok (-1) := by
  have hd : Distinct eqKey (tlist t) := tlist_pairwise h.1
  rw [← rfind_perm hl hq hd h.2]
  cases hf : rfind matchQ (tlist t) q with
  | some e =>
    obtain ⟨hem, heq⟩ := rfind_some hf
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
    obtain ⟨k, v⟩ := e
    exact ⟨i, htKeyindex_found hq h.1 h1 h2 hei heq, h1, h2, hei⟩
  | none => exact htKeyindex_absent h.1 (rfind_eq_none_iff.1 hf)

end Lookup


/-! ## `rehash!` -/

/-- Updating slot `j` with a filled byte stores `(k, v)` there. -/
theorem ent_store_eq {t t' : DictState K V} {j : Nat} {k : K} {v : V} {b : Nat}
    (hb : filledB b = true) (hs : t'.slots = updateAt t.slots j b)
    (hk : t'.keys = updateAt t.keys j (some k)) (hv : t'.vals = updateAt t.vals j (some v))
    (i : Nat) : ent t' i = if i = j then some (k, v) else ent t i := by
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl]
    apply ent_of_filled
    · rw [hs, updateAt_same]; exact hb
    · rw [hk, updateAt_same]
    · rw [hv, updateAt_same]
  · rw [ite_eq_right h]
    unfold ent
    rw [hs, hk, hv, updateAt_ne _ _ h, updateAt_ne _ _ h, updateAt_ne _ _ h]

theorem filterMap_ent_nil {t : DictState K V} :
    ∀ n s, (∀ p, s ≤ p → p < s + n → filledB (t.slots p) = false) →
      (List.range' s n).filterMap (ent t) = []
  | 0, _, _ => rfl
  | n + 1, s, h => by
    rw [List.range'_succ,
      List.filterMap_cons_none (ent_of_not_filled (h s (Nat.le_refl _) (by omega)))]
    exact filterMap_ent_nil n (s + 1) (fun p h1 h2 => h p (by omega) (by omega))

theorem length_filterMap_ent_all {t : DictState K V} :
    ∀ n s, (∀ p, s ≤ p → p < s + n → ent t p ≠ none) →
      ((List.range' s n).filterMap (ent t)).length = n
  | 0, _, _ => rfl
  | n + 1, s, h => by
    rw [List.range'_succ]
    cases he : ent t s with
    | none => exact absurd he (h s (Nat.le_refl _) (by omega))
    | some e =>
      rw [List.filterMap_cons_some he, List.length_cons,
        length_filterMap_ent_all n (s + 1) (fun p h1 h2 => h p (by omega) (by omega))]

/-- A table with fewer stored pairs than slots has a slot without a pair. -/
theorem exists_not_ent {t : DictState K V} (h : (tlist t).length < t.size) :
    ∃ j, 1 ≤ j ∧ j ≤ t.size ∧ ent t j = none := by
  apply Classical.byContradiction
  intro hne
  have hall : ∀ p, 1 ≤ p → p < 1 + t.size → ent t p ≠ none := by
    intro p h1 h2 he
    exact hne ⟨p, h1, by omega, he⟩
  have := length_filterMap_ent_all t.size 1 hall
  unfold tlist at h
  omega

/-- The probe loop of `rehash!` stops at the first empty slot. -/
theorem rehashProbe_spec (slots : Nat → Nat) (sz hm : Nat) :
    ∀ left a, (∃ d, a ≤ d ∧ d < a + left ∧ slots (pr sz hm d) = 0) →
      ∃ d, a ≤ d ∧ d < a + left ∧ slots (pr sz hm d) = 0 ∧
        (∀ e, a ≤ e → e < d → slots (pr sz hm e) ≠ 0) ∧
        rehashProbe slots sz left (pr sz hm a) = some (pr sz hm d)
  | 0, a, ⟨d, h1, h2, _⟩ => absurd h2 (by omega)
  | left + 1, a, ⟨d, h1, h2, h3⟩ => by
    have e : rehashProbe slots sz (left + 1) (pr sz hm a) =
        if slots (pr sz hm a) == 0 then some (pr sz hm a)
        else rehashProbe slots sz left (pr sz hm (a + 1)) := rfl
    by_cases ha : slots (pr sz hm a) = 0
    · refine ⟨a, Nat.le_refl _, by omega, ha, fun e he1 he2 => absurd he2 (by omega), ?_⟩
      rw [e, ha] <;> rfl
    · have hd : a < d := by
        rcases Nat.lt_or_ge a d with h | h
        · exact h
        · have : d = a := by omega
          subst this
          exact absurd h3 ha
      obtain ⟨d', h1', h2', h3', h4', h5'⟩ :=
        rehashProbe_spec slots sz hm left (a + 1) ⟨d, by omega, by omega, h3⟩
      refine ⟨d', by omega, by omega, h3', fun e he1 he2 => ?_, ?_⟩
      · by_cases hea : e = a
        · rw [hea]; exact ha
        · exact h4' e (by omega) he2
      · rw [e, ite_eq_right (by simp [ha])]
        exact h5'

/-- The table of the copy-loop locals of `rehash!`. -/
def accT (newsz : Nat) (acc : RehashAcc K V) : DictState K V :=
  ⟨newsz, acc.slots, acc.keys, acc.vals, 0, acc.count, JInt.lit .u64 0, 1, acc.maxprobe, 1⟩

/-- The copy loop after the old slots `1:n`. -/
def AccOK (hash : K → JInt .u64) (eqKey : K → K → Bool) (t : DictState K V) (newsz n : Nat)
    (acc : RehashAcc K V) : Prop :=
  Inv hash eqKey (accT newsz acc) ∧ (∀ j, acc.slots j ≠ 127) ∧
  List.Perm (tlist (accT newsz acc)) ((List.range' 1 n).filterMap (ent t))

abbrev acc0 : RehashAcc K V := RehashAcc.mk (fun _ => 0) (fun _ => none) (fun _ => none) 0 0

theorem accOK_zero {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V} {newsz : Nat}
    (hp : IsPow newsz) (hle : newsz ≤ 2 ^ 62) : AccOK hash eqKey t newsz 0 acc0 := by
  have hnil : tlist (accT newsz (acc0 : RehashAcc K V)) = [] :=
    filterMap_ent_nil (t := accT newsz acc0) newsz 1 (fun _ _ _ => filledB_zero)
  refine ⟨⟨Or.inr hp, hle, fun i _ _ => Or.inl rfl, ?_, ?_, Or.inr ?_, Nat.le_refl _, ?_,
    Nat.le_refl _⟩, fun _ => by show (0 : Nat) ≠ 127; decide, ?_⟩
  · intro i j a b _ _ _ _ _ ha
    have : ent (accT newsz (acc0 : RehashAcc K V)) i = none := ent_of_not_filled filledB_zero
    rw [this] at ha
    cases ha
  · rw [hnil] <;> rfl
  · have := hp.ge
    show 0 < newsz
    omega
  · intro i _ _ hf
    exact absurd hf (by show ¬ (filledB 0 = true); decide)
  · rw [hnil]
    exact List.Perm.nil

/-- The prefix lists of a table. -/
theorem prefix_succ (t : DictState K V) (n : Nat) :
    (List.range' 1 (n + 1)).filterMap (ent t) =
      (List.range' 1 n).filterMap (ent t) ++ (ent t (n + 1)).toList := by
  rw [List.range'_concat, List.filterMap_append]
  congr 1
  rw [show 1 + 1 * n = n + 1 by omega]
  cases h : ent t (n + 1)
  · rw [List.filterMap_cons_none h] <;> rfl
  · rw [List.filterMap_cons_some h] <;> rfl

theorem prefix_length_le (t : DictState K V) {n : Nat} (hn : n ≤ t.size) :
    ((List.range' 1 n).filterMap (ent t)).length ≤ (tlist t).length := by
  unfold tlist
  have h := List.range'_append_1 (s := 1) (m := n) (n := t.size - n)
  rw [show n + (t.size - n) = t.size by omega] at h
  rw [← h, List.filterMap_append, List.length_append]
  omega

theorem prefix_mem {t : DictState K V} {n : Nat} {e : K × V}
    (h : e ∈ (List.range' 1 n).filterMap (ent t)) : ∃ p, 1 ≤ p ∧ p ≤ n ∧ ent t p = some e := by
  rw [List.mem_filterMap] at h
  obtain ⟨p, hp, he⟩ := h
  rw [List.mem_range'_1] at hp
  exact ⟨p, hp.1, by omega, he⟩

/-- The copy-loop locals after storing `(k, v)` with byte `b` at `index`, probe length `d`. -/
def accStore (acc : RehashAcc K V) (index b : Nat) (k : K) (v : V) (d : Nat) : RehashAcc K V :=
  RehashAcc.mk (updateAt acc.slots index b) (updateAt acc.keys index (some k))
    (updateAt acc.vals index (some v)) (acc.count + 1) (max acc.maxprobe d)

theorem rehashCopyLoop_skip {hash : K → JInt .u64} {newsz : Nat} {olds : Nat → Nat}
    {oldk : Nat → Option K} {oldv : Nat → Option V} {acc : RehashAcc K V} {i r : Nat}
    (hf : filledB (olds i) = false) :
    rehashCopyLoop hash newsz olds oldk oldv (r + 1) i acc =
      rehashCopyLoop hash newsz olds oldk oldv r (i + 1) acc := by
  have hf' : (Nat.land (olds i) 0x80 != 0) = false := hf
  simp only [rehashCopyLoop, hf', Bool.false_eq_true, ite_false]

theorem rehashCopyLoop_store {hash : K → JInt .u64} {newsz : Nat} {olds : Nat → Nat}
    {oldk : Nat → Option K} {oldv : Nat → Option V} {acc : RehashAcc K V} {i r : Nat} {k : K}
    {v : V} {index : Nat} (hf : filledB (olds i) = true) (hk : oldk i = some k)
    (hv : oldv i = some v)
    (hp : rehashProbe acc.slots newsz newsz (home hash newsz k) = some index) :
    rehashCopyLoop hash newsz olds oldk oldv (r + 1) i acc =
      rehashCopyLoop hash newsz olds oldk oldv r (i + 1)
        (accStore acc index (olds i) k v (probeDist newsz index (home hash newsz k))) := by
  have hf' : (Nat.land (olds i) 0x80 != 0) = true := hf
  have hp' : rehashProbe acc.slots newsz newsz (hashindex hash k newsz).1 = some index := hp
  simp only [rehashCopyLoop, hf', ite_true, hk, hv]
  rw [hp']
  rfl

/-- One step of the copy loop. -/
theorem rehashStep_ok {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    (hi : Inv hash eqKey t) {newsz : Nat} (hp : IsPow newsz)
    (hle : newsz ≤ 2 ^ 62) (hgt : t.count < newsz) {n : Nat} (hn : n < t.size)
    {acc : RehashAcc K V} (ha : AccOK hash eqKey t newsz n acc) :
    ∃ acc', (∀ r, rehashCopyLoop hash newsz t.slots t.keys t.vals (r + 1) (n + 1) acc =
        rehashCopyLoop hash newsz t.slots t.keys t.vals r (n + 2) acc') ∧
      AccOK hash eqKey t newsz (n + 1) acc' := by
  obtain ⟨hai, ha127, hap⟩ := ha
  cases hf : filledB (t.slots (n + 1)) with
  | false =>
    refine ⟨acc, fun r => rehashCopyLoop_skip hf, hai, ha127, ?_⟩
    rw [prefix_succ, ent_of_not_filled hf]
    simpa using hap
  | true =>
    obtain ⟨k, v, hk, hv, hent, hs, -⟩ := hi.filled (by omega) (by omega) hf
    -- the accumulator has fewer pairs than slots
    have hlen : (tlist (accT newsz acc)).length + 1 ≤ t.count := by
      rw [hap.length_eq, hi.count]
      have h1 := prefix_length_le t (n := n + 1) (by omega)
      rw [prefix_succ, hent, List.length_append] at h1
      simpa using h1
    obtain ⟨j, hj1, hj2, hjn⟩ := exists_not_ent (t := accT newsz acc) (by show _ < newsz; omega)
    have hj0 : acc.slots j = 0 := by
      rcases hai.slot j hj1 hj2 with h | h | ⟨k', v', hk', hv', hs', -⟩
      · exact h
      · exact absurd h (ha127 j)
      · have hf' : filledB ((accT newsz acc).slots j) = true := by
          rw [hs']; exact shorthash7_filled _
        rw [ent_of_filled hf' hk' hv'] at hjn
        cases hjn
    have hhr := home_range hp hash k
    obtain ⟨d0, hd0, hd0e⟩ := pr_surj hp hhr.1 hhr.2 hj1 hj2
    obtain ⟨d, -, hd, hdz, hdbefore, hprobe⟩ := rehashProbe_spec acc.slots newsz (home hash newsz k)
      newsz 0 ⟨d0, Nat.zero_le _, by omega, by rw [hd0e]; exact hj0⟩
    have hprobe' : rehashProbe acc.slots newsz newsz (home hash newsz k) =
        some (pr newsz (home hash newsz k) d) := hprobe
    have hdist := probeDist_pr hp (by omega) hhr.1 hhr.2 (show d < newsz by omega)
    refine ⟨_, fun r => rehashCopyLoop_store hf hk hv hprobe', ?_⟩
    rw [hdist]
    have hir := pr_range hp hhr.1 hhr.2 (show d < newsz by omega)
    have hent' := ent_store_eq (t := accT newsz acc)
      (t' := accT newsz (accStore acc (pr newsz (home hash newsz k) d) (t.slots (n + 1)) k v d))
      hf rfl rfl rfl
    -- keys already copied come from earlier old slots
    have hold : ∀ i b, 1 ≤ i → i ≤ newsz → ent (accT newsz acc) i = some b →
        eqKey k b.1 = false ∧ eqKey b.1 k = false := by
      intro i b h1 h2 hb
      obtain ⟨p, hp1, hp2, hpe⟩ := prefix_mem (hap.mem_iff.1 (mem_tlist.2 ⟨i, h1, h2, hb⟩))
      exact ⟨hi.distinct (n + 1) p (k, v) b (by omega) (by omega) hp1 (by omega) (by omega) hent hpe,
        hi.distinct p (n + 1) b (k, v) hp1 (by omega) (by omega) (by omega) (by omega) hpe hent⟩
    have hmpacc : acc.maxprobe < newsz := by
      rcases hai.maxprobe with h | h
      · exact absurd h (by have := hp.ge; show newsz ≠ 0; omega)
      · exact h
    have hnf : ent (accT newsz acc) (pr newsz (home hash newsz k) d) = none :=
      ent_of_not_filled (by
        show filledB (acc.slots (pr newsz (home hash newsz k) d)) = false
        rw [hdz]; exact filledB_zero)
    have hstore := tlist_store (eqKey := eqKey) (t := accT newsz acc)
      (t' := accT newsz (accStore acc (pr newsz (home hash newsz k) d) (t.slots (n + 1)) k v d))
      (j := pr newsz (home hash newsz k) d) (e := (k, v)) rfl hir.1 hir.2 (fun i _ _ => hent' i)
      (fun i b h1 h2 _ hb => (hold i b h1 h2 hb).1)
      (fun b hb => by rw [hnf] at hb; cases hb)
    have hfilt : (tlist (accT newsz acc)).filter (fun b => !eqKey (k, v).1 b.1) =
        tlist (accT newsz acc) := by
      rw [List.filter_eq_self]
      intro b hb
      obtain ⟨i, h1, h2, hbi⟩ := mem_tlist.1 hb
      simp [(hold i b h1 h2 hbi).1]
    rw [hfilt] at hstore
    refine ⟨⟨Or.inr hp, hle, ?_, ?_, ?_, Or.inr ?_, Nat.le_refl _, fun _ h _ _ => h, Nat.le_refl _⟩,
      ?_, ?_⟩
    · -- slots
      intro i h1 h2
      by_cases hi' : i = pr newsz (home hash newsz k) d
      · subst hi'
        refine Or.inr (Or.inr ⟨k, v, updateAt_same _ _ _, updateAt_same _ _ _,
          (updateAt_same _ _ _).trans hs, d, ?_, rfl, ?_⟩)
        · show d ≤ max acc.maxprobe d
          omega
        · intro e he
          have hne : pr newsz (home hash newsz k) e ≠ pr newsz (home hash newsz k) d := by
            intro heq
            have := pr_inj hp hhr.1 hhr.2 (show e < newsz by omega) (show d < newsz by omega) heq
            omega
          show updateAt acc.slots (pr newsz (home hash newsz k) d) (t.slots (n + 1))
            (pr newsz (home hash newsz k) e) ≠ 0
          rw [updateAt_ne _ _ hne]
          exact hdbefore e (Nat.zero_le _) he
      · rcases hai.slot i h1 h2 with h | h | ⟨k', v', hk', hv', hs', hc'⟩
        · exact Or.inl ((updateAt_ne _ _ hi').trans h)
        · exact Or.inr (Or.inl ((updateAt_ne _ _ hi').trans h))
        · refine Or.inr (Or.inr ⟨k', v', (updateAt_ne _ _ hi').trans hk',
            (updateAt_ne _ _ hi').trans hv', (updateAt_ne _ _ hi').trans hs', ?_⟩)
          refine Chain.mono (t := accT newsz acc) hp hmpacc rfl ?_ ?_ hc'
          · show acc.maxprobe ≤ max acc.maxprobe d
            omega
          · intro p _ _ hne
            show updateAt acc.slots (pr newsz (home hash newsz k) d) (t.slots (n + 1)) p ≠ 0
            by_cases hp' : p = pr newsz (home hash newsz k) d
            · rw [hp', updateAt_same, hs]; exact shorthash7_ne0 _
            · rw [updateAt_ne _ _ hp']; exact hne
    · -- distinct
      intro i i' a b h1 h2 h1' h2' hne ha hb
      rw [hent'] at ha hb
      by_cases hi1 : i = pr newsz (home hash newsz k) d
      · rw [ite_eq_left hi1] at ha
        cases ha
        have hi2 : i' ≠ pr newsz (home hash newsz k) d := fun h => hne (hi1.trans h.symm)
        rw [ite_eq_right hi2] at hb
        exact (hold i' b h1' h2' hb).1
      · rw [ite_eq_right hi1] at ha
        by_cases hi2 : i' = pr newsz (home hash newsz k) d
        · rw [ite_eq_left hi2] at hb
          cases hb
          exact (hold i a h1 h2 ha).2
        · rw [ite_eq_right hi2] at hb
          exact hai.distinct i i' a b h1 h2 h1' h2' hne ha hb
    · -- count
      show acc.count + 1 = _
      rw [hstore.length_eq, List.length_cons,
        ← show acc.count = (tlist (accT newsz acc)).length from hai.count]
    · -- maxprobe
      show max acc.maxprobe d < newsz
      omega
    · -- no deleted bytes
      intro p
      show updateAt acc.slots (pr newsz (home hash newsz k) d) (t.slots (n + 1)) p ≠ 127
      by_cases hp' : p = pr newsz (home hash newsz k) d
      · rw [hp', updateAt_same, hs]; exact shorthash7_ne127 _
      · rw [updateAt_ne _ _ hp']; exact ha127 p
    · -- contents
      rw [prefix_succ, hent]
      exact hstore.trans ((List.Perm.cons _ hap).trans (List.perm_append_singleton _ _).symm)

/-- The whole copy loop. -/
theorem rehash_loop {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    (hi : Inv hash eqKey t) {newsz : Nat} (hp : IsPow newsz) (hle : newsz ≤ 2 ^ 62)
    (hgt : t.count < newsz) :
    ∀ r n (acc : RehashAcc K V), n + r = t.size → AccOK hash eqKey t newsz n acc →
      ∃ acc', rehashCopyLoop hash newsz t.slots t.keys t.vals r (n + 1) acc = .ok acc' ∧
        AccOK hash eqKey t newsz t.size acc'
  | 0, n, acc, hn, ha => ⟨acc, rfl, by rw [show t.size = n by omega]; exact ha⟩
  | r + 1, n, acc, hn, ha => by
    obtain ⟨acc', h1, h2⟩ := rehashStep_ok hi hp hle hgt (n := n) (by omega) ha
    rw [h1 r]
    exact rehash_loop hi hp hle hgt r (n + 1) acc' (by omega) h2

/-- `rehash!(h, newsz0)` keeps the pairs when the new size exceeds the count. -/
theorem rehash_spec {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) {t : DictState K V} (hi : Inv hash eqKey t) (newsz0 : Nat)
    (h62 : newsz0 ≤ 2 ^ 62) (hgt : t.count < tableszSpec newsz0) :
    ∃ t', rehash hash tablesz t newsz0 = .ok t' ∧ Inv hash eqKey t' ∧
      List.Perm (tlist t') (tlist t) ∧ t'.size = tableszSpec newsz0 ∧ t'.count = t.count ∧
      t'.age = (if t.count = 0 then bumpAge t.age else bumpAge (bumpAge t.age)) := by
  have hp := tableszSpec_pow newsz0
  have hle := tableszSpec_le_pow h62
  have htab : tablesz newsz0 = tableszSpec newsz0 := htz newsz0 h62
  by_cases hc : t.count = 0
  · let t' : DictState K V := DictState.mk (tableszSpec newsz0) (fun _ => 0) (fun _ => none)
      (fun _ => none) 0 t.count (bumpAge t.age) 1 0 1
    have hnil : tlist t' = [] :=
      filterMap_ent_nil (tableszSpec newsz0) 1 (fun _ _ _ => filledB_zero)
    refine ⟨t', ?_, ?_, ?_, rfl, rfl, by simp [hc, t']⟩
    · unfold rehash
      rw [htab]
      have h0 : (t.count == 0) = true := by simp [hc]
      simp only [h0, ite_true]
      rfl
    · have h := accOK_zero (hash := hash) (eqKey := eqKey) (t := t) hp hle
      exact ⟨h.1.size, h.1.sizeLe, h.1.slot, h.1.distinct, by rw [hnil]; exact hc,
        h.1.maxprobe, h.1.idxfloor, h.1.floorLe, h.1.popcursor⟩
    · have ht : tlist t = [] := by
        rw [hi.count] at hc
        exact List.length_eq_zero_iff.1 hc
      rw [hnil, ht]
  · obtain ⟨acc, hloop, hacc, -, hperm⟩ :=
      rehash_loop hi hp hle hgt t.size 0 acc0 (by omega) (accOK_zero hp hle)
    have htl : (List.range' 1 t.size).filterMap (ent t) = tlist t := rfl
    rw [htl] at hperm
    refine ⟨DictState.mk (tableszSpec newsz0) acc.slots acc.keys acc.vals 0 acc.count
      (bumpAge (bumpAge t.age)) 1 acc.maxprobe 1, ?_,
      ⟨hacc.size, hacc.sizeLe, hacc.slot, hacc.distinct, hacc.count, hacc.maxprobe, hacc.idxfloor,
        hacc.floorLe, hacc.popcursor⟩, hperm, rfl, ?_, by simp [hc]⟩
    · unfold rehash
      rw [htab]
      have h0 : (t.count == 0) = false := by simp [hc]
      simp only [h0, Bool.false_eq_true, ite_false]
      rw [bind_of_ok hloop]
    · show acc.count = t.count
      rw [show acc.count = (tlist (accT (tableszSpec newsz0) acc)).length from hacc.count,
        hperm.length_eq, hi.count]


/-! ## Insertion: `ht_keyindex2_shorthash!` -/

/-- A free slot on the probe sequence from the home slot `hm`. -/
def InsertSlot (t : DictState K V) (hm j : Nat) : Prop :=
  1 ≤ j ∧ j ≤ t.size ∧ filledB (t.slots j) = false ∧
  ∃ d, d ≤ t.maxprobe ∧ j = pr t.size hm d ∧ ∀ e, e < d → t.slots (pr t.size hm e) ≠ 0

section Insert
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}

/-- Storing a new key at a free slot of its probe sequence. -/
theorem Inv.store (hl : KeyLaws hash eqKey) {t t' : DictState K V} (hi : Inv hash eqKey t)
    {j : Nat} {k : K} {v : V} (hj : InsertSlot t (home hash t.size k) j) (habs : Absent eqKey t k)
    (hs : t'.size = t.size) (hsl : t'.slots = updateAt t.slots j (shorthash7 (hash k)))
    (hk : t'.keys = updateAt t.keys j (some k)) (hv : t'.vals = updateAt t.vals j (some v))
    (hc : t'.count = t.count + 1) (hm : t'.maxprobe = t.maxprobe)
    (hf1 : 1 ≤ t'.idxfloor) (hf2 : t'.idxfloor ≤ t.idxfloor) (hf3 : t'.idxfloor ≤ j)
    (hp : 1 ≤ t'.popcursor) :
    Inv hash eqKey t' ∧ List.Perm (tlist t') ((k, v) :: tlist t) := by
  obtain ⟨hj1, hj2, hjf, hjc⟩ := hj
  have hpow : IsPow t.size := by
    rcases hi.size with h | h
    · omega
    · exact h
  have hmp : t.maxprobe < t.size := by
    rcases hi.maxprobe with h | h
    · omega
    · exact h
  have hent : ∀ i, ent t' i = if i = j then some (k, v) else ent t i :=
    ent_store_eq (shorthash7_filled _) hsl hk hv
  have hnone : ent t j = none := ent_of_not_filled hjf
  have hstore := tlist_store (eqKey := eqKey) hs hj1 hj2 (fun i _ _ => hent i)
    (fun i b h1 h2 _ hb => habs b (mem_tlist.2 ⟨i, h1, h2, hb⟩))
    (fun b hb => by rw [hnone] at hb; cases hb)
  have hfilt : (tlist t).filter (fun b => !eqKey (k, v).1 b.1) = tlist t := by
    rw [List.filter_eq_self]
    intro b hb
    simp [habs b hb]
  rw [hfilt] at hstore
  have hne : ∀ p, 1 ≤ p → p ≤ t.size → t.slots p ≠ 0 → t'.slots p ≠ 0 := by
    intro p _ _ h0
    rw [hsl]
    by_cases hpj : p = j
    · rw [hpj, updateAt_same]; exact shorthash7_ne0 _
    · rw [updateAt_ne _ _ hpj]; exact h0
  refine ⟨⟨by rw [hs]; exact hi.size, by rw [hs]; exact hi.sizeLe, ?_, ?_, ?_, ?_, hf1, ?_, hp⟩,
    hstore⟩
  · intro i h1 h2
    rw [hs] at h2
    by_cases hij : i = j
    · subst hij
      refine Or.inr (Or.inr ⟨k, v, by rw [hk, updateAt_same], by rw [hv, updateAt_same],
        by rw [hsl, updateAt_same], ?_⟩)
      exact Chain.mono hpow hmp hs (by rw [hm]; exact Nat.le_refl _) hne hjc
    · refine SlotOK.transfer (hi.slot i h1 h2) (by rw [hsl, updateAt_ne _ _ hij])
        (by rw [hk, updateAt_ne _ _ hij]) (by rw [hv, updateAt_ne _ _ hij]) ?_
      intro k' hc'
      exact Chain.mono hpow hmp hs (by rw [hm]; exact Nat.le_refl _) hne hc'
  · intro i i' a b h1 h2 h1' h2' hne' ha hb
    rw [hs] at h2 h2'
    rw [hent] at ha hb
    by_cases hi1 : i = j
    · rw [ite_eq_left hi1] at ha
      cases ha
      have hi2 : i' ≠ j := fun h => hne' (hi1.trans h.symm)
      rw [ite_eq_right hi2] at hb
      exact habs b (mem_tlist.2 ⟨i', h1', h2', hb⟩)
    · rw [ite_eq_right hi1] at ha
      by_cases hi2 : i' = j
      · rw [ite_eq_left hi2] at hb
        cases hb
        exact eq_false_symm hl (habs a (mem_tlist.2 ⟨i, h1, h2, ha⟩))
      · rw [ite_eq_right hi2] at hb
        exact hi.distinct i i' a b h1 h2 h1' h2' hne' ha hb
  · rw [hc, hstore.length_eq, List.length_cons, hi.count]
  · right
    rw [hm, hs]
    exact hmp
  · intro i h1 h2 hfi
    rw [hs] at h2
    by_cases hij : i = j
    · rw [hij]; exact hf3
    · have : filledB (t.slots i) = true := by
        rw [hsl, updateAt_ne _ _ hij] at hfi; exact hfi
      exact Nat.le_trans hf2 (hi.floorLe i h1 h2 this)

end Insert

/-! ### The first probe loop -/

/-- The `avail` update of the first loop. -/
def avail1 (t : DictState K V) (index : Nat) (avail : Int) : Int :=
  if (t.slots index == 0x7f && avail == 0) = true then -(index : Int) else avail

theorem keyindex2Loop1_step {Q : Type} (m : Q → K → Bool) (q : Q) (t : DictState K V)
    (sh sz left iter index : Nat) (avail : Int) (hsh : sh ≠ 127)
    (hdef : t.slots index = sh → ∃ k, t.keys index = some k) :
    keyindex2Loop1 m q t sh sz (left + 1) iter index avail =
      if t.slots index = 0 then .ok (.found (if avail < 0 then avail else -(index : Int)))
      else if hitAt t sh m q index = true then .ok (.found (index : Int))
      else if iter + 1 > t.maxprobe then
        .ok (.broken (iter + 1) (nextIndex sz index) (avail1 t index avail))
      else keyindex2Loop1 m q t sh sz left (iter + 1) (nextIndex sz index) (avail1 t index avail) := by
  by_cases h0 : t.slots index = 0
  · simp [keyindex2Loop1, h0]
  · by_cases hs : t.slots index = sh
    · obtain ⟨k, hk⟩ := hdef hs
      have h0' : sh ≠ 0 := hs ▸ h0
      cases hm : m q k <;> simp [keyindex2Loop1, hs, h0', hsh, hk, hitAt, avail1, hm]
    · cases hk : t.keys index <;>
        simp [keyindex2Loop1, h0, hs, Ne.symm hs, hitAt, avail1, hk]

/-- Probe positions before `a` are non-empty and miss. -/
def Before {Q : Type} (t : DictState K V) (sh : Nat) (m : Q → K → Bool) (q : Q) (h a : Nat) : Prop :=
  ∀ e, e < a → t.slots (pr t.size h e) ≠ 0 ∧ hitAt t sh m q (pr t.size h e) = false

/-- `avail` is `0` with no deleted slot before `a`, or a deleted slot before `a`. -/
def AvailOK (t : DictState K V) (h a : Nat) (avail : Int) : Prop :=
  (avail = 0 ∧ ∀ e, e < a → t.slots (pr t.size h e) ≠ 127) ∨
  (∃ e, e < a ∧ avail = -(pr t.size h e : Int) ∧ t.slots (pr t.size h e) = 127)

theorem keyindex2Loop1_spec {Q : Type} (t : DictState K V) (sh : Nat) (m : Q → K → Bool) (q : Q)
    (h : Nat) (hsh : sh ≠ 127) (hpow : IsPow t.size) (hh1 : 1 ≤ h) (hh2 : h ≤ t.size)
    (hmp : t.maxprobe < t.size) (hdef : ∀ e, t.slots (pr t.size h e) = sh →
      ∃ k, t.keys (pr t.size h e) = some k) :
    ∀ left a avail, a + left = t.maxprobe + 1 → Before t sh m q h a → AvailOK t h a avail →
      (∃ d, a ≤ d ∧ d ≤ t.maxprobe ∧ Before t sh m q h d ∧ hitAt t sh m q (pr t.size h d) = true ∧
        keyindex2Loop1 m q t sh t.size left a (pr t.size h a) avail =
          .ok (.found (pr t.size h d : Int))) ∨
      (∃ d av, a ≤ d ∧ d ≤ t.maxprobe ∧ Before t sh m q h d ∧ t.slots (pr t.size h d) = 0 ∧
        AvailOK t h d av ∧
        keyindex2Loop1 m q t sh t.size left a (pr t.size h a) avail =
          .ok (.found (if av < 0 then av else -(pr t.size h d : Int)))) ∨
      (Before t sh m q h (t.maxprobe + 1) ∧ ∃ av, AvailOK t h (t.maxprobe + 1) av ∧
        keyindex2Loop1 m q t sh t.size left a (pr t.size h a) avail =
          .ok (.broken (t.maxprobe + 1) (pr t.size h (t.maxprobe + 1)) av))
  | 0, a, avail, hal, hb, hav => by
    have ha : t.maxprobe + 1 = a := by omega
    right; right
    rw [ha]
    exact ⟨hb, avail, hav, rfl⟩
  | left + 1, a, avail, hal, hb, hav => by
    rw [keyindex2Loop1_step m q t sh t.size left a _ avail hsh (hdef a)]
    by_cases h0 : t.slots (pr t.size h a) = 0
    · right; left
      refine ⟨a, avail, Nat.le_refl _, by omega, hb, h0, hav, ?_⟩
      rw [ite_eq_left h0]
    · rw [ite_eq_right h0]
      by_cases hh : hitAt t sh m q (pr t.size h a) = true
      · left
        exact ⟨a, Nat.le_refl _, by omega, hb, hh, by rw [ite_eq_left hh]⟩
      · have hh' : hitAt t sh m q (pr t.size h a) = false := Bool.eq_false_iff.2 hh
        rw [ite_eq_right hh]
        have hb' : Before t sh m q h (a + 1) := by
          intro e he
          by_cases hea : e < a
          · exact hb e hea
          · have : e = a := by omega
            rw [this]
            exact ⟨h0, hh'⟩
        have hra := pr_range hpow hh1 hh2 (show a < t.size by omega)
        have hav' : AvailOK t h (a + 1) (avail1 t (pr t.size h a) avail) := by
          unfold avail1
          by_cases h127 : t.slots (pr t.size h a) = 127
          · rcases hav with ⟨hz, hall⟩ | ⟨e, he, hea, he127⟩
            · rw [ite_eq_left (by simp [h127, hz])]
              exact Or.inr ⟨a, by omega, rfl, h127⟩
            · have hre := pr_range hpow hh1 hh2 (show e < t.size by omega)
              rw [ite_eq_right (fun hc => by
                simp only [Bool.and_eq_true, beq_iff_eq] at hc
                rw [hea] at hc
                omega)]
              exact Or.inr ⟨e, by omega, hea, he127⟩
          · rw [ite_eq_right (fun hc => h127 (by
              simp only [Bool.and_eq_true, beq_iff_eq] at hc
              exact hc.1))]
            rcases hav with ⟨hz, hall⟩ | ⟨e, he, hea, he127⟩
            · refine Or.inl ⟨hz, fun e he => ?_⟩
              by_cases hea : e < a
              · exact hall e hea
              · have : e = a := by omega
                rw [this]
                exact h127
            · exact Or.inr ⟨e, by omega, hea, he127⟩
        by_cases hmpa : a + 1 > t.maxprobe
        · rw [ite_eq_left hmpa]
          right; right
          have e1 : t.maxprobe + 1 = a + 1 := by omega
          rw [e1]
          exact ⟨hb', _, hav', rfl⟩
        · rw [ite_eq_right hmpa]
          rcases keyindex2Loop1_spec t sh m q h hsh hpow hh1 hh2 hmp hdef left (a + 1) _ (by omega)
              hb' hav' with ⟨d, h2, h3, h4, h5, h6⟩ | ⟨d, av, h2, h3, h4, h5, h6, h7⟩ | h1
          · exact Or.inl ⟨d, by omega, h3, h4, h5, h6⟩
          · exact Or.inr (Or.inl ⟨d, av, by omega, h3, h4, h5, h6, h7⟩)
          · exact Or.inr (Or.inr h1)

/-! ### The second probe loop -/

theorem keyindex2Loop2_spec (t : DictState K V) (h M : Nat) :
    ∀ left a, M ≤ a + left →
      (∃ d, a ≤ d ∧ d < M ∧ filledB (t.slots (pr t.size h d)) = false ∧
        (∀ e, a ≤ e → e < d → filledB (t.slots (pr t.size h e)) = true) ∧
        keyindex2Loop2 t t.size M left a (pr t.size h a) = some (d, pr t.size h d)) ∨
      ((∀ e, a ≤ e → e < M → filledB (t.slots (pr t.size h e)) = true) ∧
        keyindex2Loop2 t t.size M left a (pr t.size h a) = none)
  | 0, a, hM => Or.inr ⟨fun e h1 h2 => absurd h2 (by omega), rfl⟩
  | left + 1, a, hM => by
    have e1 : keyindex2Loop2 t t.size M (left + 1) a (pr t.size h a) =
        if a < M then (if !filledB (t.slots (pr t.size h a)) then some (a, pr t.size h a)
          else keyindex2Loop2 t t.size M left (a + 1) (pr t.size h (a + 1))) else none := rfl
    rw [e1]
    by_cases haM : a < M
    · rw [ite_eq_left haM]
      cases hf : filledB (t.slots (pr t.size h a))
      · left
        refine ⟨a, Nat.le_refl _, haM, hf, fun e h1 h2 => absurd h2 (by omega), ?_⟩
        rw [ite_eq_left (by simp)]
      · rw [ite_eq_right (by simp)]
        rcases keyindex2Loop2_spec t h M left (a + 1) (by omega) with
          ⟨d, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
        · refine Or.inl ⟨d, by omega, h2, h3, fun e he1 he2 => ?_, h5⟩
          by_cases hea : e = a
          · rw [hea]; exact hf
          · exact h4 e (by omega) he2
        · refine Or.inr ⟨fun e he1 he2 => ?_, h2⟩
          by_cases hea : e = a
          · rw [hea]; exact hf
          · exact h1 e (by omega) he2
    · rw [ite_eq_right haM]
      exact Or.inr ⟨fun e h1 h2 => absurd h2 (by omega), rfl⟩

/-! ### Counting a window of filled slots -/

theorem length_filterMap_ent_eq {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {t : DictState K V} (hi : Inv hash eqKey t) :
    ∀ l : List Nat, (∀ p ∈ l, 1 ≤ p ∧ p ≤ t.size) →
      (l.filterMap (ent t)).length = (l.filter (fun p => filledB (t.slots p))).length
  | [], _ => rfl
  | p :: l, hl => by
    have hp := hl p List.mem_cons_self
    have ih := length_filterMap_ent_eq hi l (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    cases hf : filledB (t.slots p)
    · rw [List.filterMap_cons_none (ent_of_not_filled hf), List.filter_cons_of_neg (by simp [hf]),
        ih]
    · obtain ⟨k, v, -, -, he, -, -⟩ := hi.filled hp.1 hp.2 hf
      rw [List.filterMap_cons_some he,
        List.filter_cons_of_pos (p := fun x => filledB (t.slots x)) hf, List.length_cons,
        List.length_cons, ih]

theorem count_ge_window {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    (hi : Inv hash eqKey t) (hpow : IsPow t.size) {h M : Nat} (h1 : 1 ≤ h) (h2 : h ≤ t.size)
    (hM : M ≤ t.size) (hall : ∀ e, e < M → filledB (t.slots (pr t.size h e)) = true) :
    M ≤ t.count := by
  let L := (List.range M).map (pr t.size h)
  have hnd : L.Nodup := by
    show List.Pairwise (fun a b => a ≠ b) ((List.range M).map (pr t.size h))
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun hx hy hxy heq => hxy ?_) List.nodup_range
    rw [List.mem_range] at hx hy
    exact pr_inj hpow h1 h2 (by omega) (by omega) heq
  have hsub : L ⊆ (List.range' 1 t.size).filter (fun p => filledB (t.slots p)) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at he
    have hr := pr_range hpow h1 h2 (show e < t.size by omega)
    rw [List.mem_filter, List.mem_range'_1]
    exact ⟨⟨hr.1, by omega⟩, hall e he⟩
  have hle := hnd.length_le_of_subset hsub
  have hlen : L.length = M := by simp [L]
  rw [hi.count]
  unfold tlist
  rw [length_filterMap_ent_eq hi _ (fun p hp => by rw [List.mem_range'_1] at hp; omega)]
  omega

theorem pow_le_window {sz : Nat} (h : IsPow sz) : sz ≤ 64 * max 16 (sz >>> 6) := by
  obtain ⟨p, hp, rfl⟩ := h
  rw [Nat.shiftRight_eq_div_pow]
  by_cases hp6 : 6 ≤ p
  · have e : 2 ^ p = 2 ^ 6 * 2 ^ (p - 6) := by rw [← Nat.pow_add]; congr 1; omega
    have : 2 ^ p / 2 ^ 6 = 2 ^ (p - 6) := by
      rw [e, Nat.mul_div_cancel_left _ (Nat.two_pow_pos 6)]
    rw [this]
    have : 2 ^ (p - 6) ≤ max 16 (2 ^ (p - 6)) := Nat.le_max_right _ _
    have h64 : (2 : Nat) ^ 6 = 64 := rfl
    omega
  · have : 2 ^ p ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
    have : 16 ≤ max 16 (2 ^ p / 2 ^ 6) := Nat.le_max_left _ _
    have h32 : (2 : Nat) ^ 5 = 32 := rfl
    omega


/-! ### `ht_keyindex2_shorthash!` -/

/-- The part of `ht_keyindex2_shorthash!` after the first loop, for a non-empty size. -/
def k2tail (hashS : K → JInt .u64) {Q : Type} (hashQ : Q → JInt .u64) (matchQ : Q → K → Bool)
    (tablesz : Nat → Nat) (fuel : Nat) (t : DictState K V) (q : Q) (sh : Nat) :
    Probe1 → DictResult (Int × Nat × DictState K V)
  | .found i => .ok (i, sh, t)
  | .broken iter index avail =>
    if avail < 0 then .ok (avail, sh, t) else
    match keyindex2Loop2 t t.size (max maxallowedprobe (t.size >>> maxprobeshift))
        (max maxallowedprobe (t.size >>> maxprobeshift)) iter index with
    | some (iter, index) => .ok (-(index : Int), sh, { t with maxprobe := iter })
    | none =>
      rehash hashS tablesz t (if t.count > 64000 then t.size * 2 else t.size * 4) >>= fun t =>
        htKeyindex2Loop hashS hashQ matchQ tablesz fuel t q

theorem htKeyindex2Loop_eq (hashS : K → JInt .u64) {Q : Type} (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (tablesz : Nat → Nat) (fuel : Nat) (t : DictState K V) (q : Q) :
    htKeyindex2Loop hashS hashQ matchQ tablesz (fuel + 1) t q =
      if (t.size == 0) = true then
        (rehash hashS tablesz t 4 >>= fun t1 =>
          .ok (-((hashindex hashQ q t1.size).1 : Int), (hashindex hashQ q t1.size).2, t1))
      else (keyindex2Loop1 matchQ q t (hashindex hashQ q t.size).2 t.size (t.maxprobe + 1) 0
          (hashindex hashQ q t.size).1 0 >>=
        k2tail hashS hashQ matchQ tablesz fuel t q (hashindex hashQ q t.size).2) := by
  rw [htKeyindex2Loop]
  by_cases h0 : (t.size == 0) = true
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0]
    generalize hashindex hashQ q t.size = hp
    obtain ⟨idx0, sh0⟩ := hp
    show (keyindex2Loop1 matchQ q t sh0 t.size (t.maxprobe + 1) 0 idx0 0 >>= fun r => _) = _
    cases keyindex2Loop1 matchQ q t sh0 t.size (t.maxprobe + 1) 0 idx0 0 with
    | error e => rfl
    | ok p =>
      cases p with
      | found i => rfl
      | broken iter index avail => rfl

/-- Result of the insertion probe for the query `q`. -/
structure K2Out (hash : K → JInt .u64) (eqKey : K → K → Bool) {Q : Type} (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (t : DictState K V) (q : Q) (idx : Int) (t' : DictState K V)
    (n : Nat) : Prop where
  inv : Inv hash eqKey t'
  perm : List.Perm (tlist t') (tlist t)
  count : t'.count = t.count
  age : AgeStep t t' n
  found : ∀ i e, 1 ≤ i → i ≤ t.size → ent t i = some e → matchQ q e.1 = true → idx = i ∧ t' = t
  absent : (∀ e ∈ tlist t, matchQ q e.1 = false) →
    idx < 0 ∧ InsertSlot t' (home hashQ t'.size q) (-idx).toNat

section Probe2
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}

theorem Inv.maxprobe_up {t : DictState K V} (hi : Inv hash eqKey t) (hpow : IsPow t.size)
    {mp : Nat} (h1 : t.maxprobe ≤ mp) (h2 : mp < t.size) :
    Inv hash eqKey { t with maxprobe := mp } := by
  have hmp : t.maxprobe < t.size := by omega
  refine ⟨hi.size, hi.sizeLe, fun i h1' h2' => ?_, hi.distinct, hi.count, Or.inr h2, hi.idxfloor,
    hi.floorLe, hi.popcursor⟩
  exact SlotOK.transfer (hi.slot i h1' h2') rfl rfl rfl
    (fun k hc => Chain.mono (t := t) hpow hmp rfl h1 (fun _ _ _ h => h) hc)

/-- A present key is hit before any empty slot of its probe sequence. -/
theorem present_hit {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V} (hi : Inv hash eqKey t)
    {q : Q} {i : Nat} {e : K × V} (h1 : 1 ≤ i) (h2 : i ≤ t.size)
    (he : ent t i = some e) (hm : matchQ q e.1 = true) :
    ∃ d, d ≤ t.maxprobe ∧ i = pr t.size (home hashQ t.size q) d ∧
      (∀ e', e' < d → t.slots (pr t.size (home hashQ t.size q) e') ≠ 0) ∧
      hitAt t (shorthash7 (hashQ q)) matchQ q i = true := by
  obtain ⟨k, v, hk, -, hek, hs, d, hd, hid, hall⟩ := hi.filled h1 h2 (ent_some he).1
  rw [he] at hek
  cases hek
  have hhash := hq.hash_eq q k hm
  have hh : home hashQ t.size q = home hash t.size k := by unfold home hashindex; rw [hhash]
  refine ⟨d, hd, by rw [hh]; exact hid, by rw [hh]; exact hall, hitAt_of ?_ hk hm⟩
  rw [hs, hhash]

/-- A key missed by every probe before an empty slot, or before `maxprobe`, is absent. -/
theorem absent_of_before {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V} (hi : Inv hash eqKey t)
    {q : Q} {d : Nat}
    (hb : Before t (shorthash7 (hashQ q)) matchQ q (home hashQ t.size q) d)
    (hend : t.slots (pr t.size (home hashQ t.size q) d) = 0 ∨ t.maxprobe < d) :
    ∀ e ∈ tlist t, matchQ q e.1 = false := by
  intro e he
  cases hm : matchQ q e.1
  · rfl
  · exfalso
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 he
    obtain ⟨d', hd', hid', hall', hhit'⟩ := present_hit hq hi h1 h2 hei hm
    rcases Nat.lt_trichotomy d' d with hlt | heq | hgt
    · have := (hb d' hlt).2
      rw [← hid', hhit'] at this
      cases this
    · rcases hend with h0 | hlt
      · have hf := (ent_some hei).1
        rw [hid', heq, h0, filledB_zero] at hf
        cases hf
      · omega
    · rcases hend with h0 | hlt
      · exact hall' d hgt h0
      · omega

theorem k2tail_neg {hashS : K → JInt .u64} {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} {tablesz : Nat → Nat} {fuel : Nat} {t : DictState K V} {q : Q}
    {sh iter index : Nat} {avail : Int} (h : avail < 0) :
    k2tail hashS hashQ matchQ tablesz fuel t q sh (.broken iter index avail) =
      .ok (avail, sh, t) := by
  rw [k2tail, ite_eq_left h]

theorem k2tail_some {hashS : K → JInt .u64} {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} {tablesz : Nat → Nat} {fuel : Nat} {t : DictState K V} {q : Q}
    {sh iter index d j : Nat} {avail : Int} (h : ¬ avail < 0)
    (h2 : keyindex2Loop2 t t.size (max 16 (t.size >>> 6)) (max 16 (t.size >>> 6)) iter index =
      some (d, j)) :
    k2tail hashS hashQ matchQ tablesz fuel t q sh (.broken iter index avail) =
      .ok (-(j : Int), sh, { t with maxprobe := d }) := by
  rw [k2tail, ite_eq_right h]
  show (match keyindex2Loop2 t t.size (max 16 (t.size >>> 6)) (max 16 (t.size >>> 6)) iter index with
    | some (iter, index) => (Except.ok (-(index : Int), sh, { t with maxprobe := iter }) :
        DictResult (Int × Nat × DictState K V))
    | none => rehash hashS tablesz t (if t.count > 64000 then t.size * 2 else t.size * 4) >>=
        fun t => htKeyindex2Loop hashS hashQ matchQ tablesz fuel t q) = _
  rw [h2]

theorem k2tail_none {hashS : K → JInt .u64} {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} {tablesz : Nat → Nat} {fuel : Nat} {t : DictState K V} {q : Q}
    {sh iter index : Nat} {avail : Int} (h : ¬ avail < 0)
    (h2 : keyindex2Loop2 t t.size (max 16 (t.size >>> 6)) (max 16 (t.size >>> 6)) iter index =
      none) :
    k2tail hashS hashQ matchQ tablesz fuel t q sh (.broken iter index avail) =
      (rehash hashS tablesz t (if t.count > 64000 then t.size * 2 else t.size * 4) >>= fun t =>
        htKeyindex2Loop hashS hashQ matchQ tablesz fuel t q) := by
  rw [k2tail, ite_eq_right h]
  show (match keyindex2Loop2 t t.size (max 16 (t.size >>> 6)) (max 16 (t.size >>> 6)) iter index with
    | some (iter, index) => (Except.ok (-(index : Int), sh, { t with maxprobe := iter }) :
        DictResult (Int × Nat × DictState K V))
    | none => rehash hashS tablesz t (if t.count > 64000 then t.size * 2 else t.size * 4) >>=
        fun t => htKeyindex2Loop hashS hashQ matchQ tablesz fuel t q) = _
  rw [h2]

theorem tableszSpec_four : tableszSpec 4 = 16 := by decide

/-- One round of `ht_keyindex2_shorthash!`, given the result for a smaller rehash budget. -/
theorem htKeyindex2_main (hl : KeyLaws hash eqKey) {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ) {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) (q : Q) (f : Nat)
    (IH : ∀ f', f = f' + 1 → ∀ fuel (t : DictState K V), f' < fuel → Inv hash eqKey t →
      t.count < 2 ^ 54 → (t.size = 0 ∨ 64 * t.count < t.size * 2 ^ f') →
      ∃ idx t' n, htKeyindex2Loop hash hashQ matchQ tablesz fuel t q =
          .ok (idx, shorthash7 (hashQ q), t') ∧
        n ≤ 2 * f' + 2 ∧ K2Out hash eqKey hashQ matchQ t q idx t' n)
    (fuel : Nat) (t : DictState K V) (hfuel : f < fuel) (hi : Inv hash eqKey t)
    (hc : t.count < 2 ^ 54) (hf : t.size = 0 ∨ 64 * t.count < t.size * 2 ^ f) :
    ∃ idx t' n, htKeyindex2Loop hash hashQ matchQ tablesz fuel t q =
        .ok (idx, shorthash7 (hashQ q), t') ∧
      n ≤ 2 * f + 2 ∧ K2Out hash eqKey hashQ matchQ t q idx t' n := by
  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
  rw [htKeyindex2Loop_eq]
  by_cases hs0 : t.size = 0
  · -- an empty table gets 16 slots
    have hc0 : t.count = 0 := by have := hi.count_le_size; omega
    rw [ite_eq_left (by simp [hs0])]
    obtain ⟨t1, h1, hi1, hp1, hs1, hc1, ha1⟩ :=
      rehash_spec htz hi 4 (by decide) (by rw [tableszSpec_four]; omega)
    rw [bind_of_ok h1]
    have hpow1 : IsPow t1.size := by rw [hs1]; exact tableszSpec_pow 4
    have hhr := home_range hpow1 hashQ q
    have hnil : tlist t = [] := List.length_eq_zero_iff.1 (by rw [← hi.count]; exact hc0)
    have hnil1 : tlist t1 = [] := List.length_eq_zero_iff.1 (by simp [hp1.length_eq, hnil])
    refine ⟨-((home hashQ t1.size q : Nat) : Int), t1, 1, rfl, by omega,
      ⟨hi1, hp1, hc1, AgeStep.of_pos (by rw [ha1, ite_eq_left hc0, bump_eq]) (by omega),
       fun i e h1 h2 _ _ => absurd h2 (by omega), fun _ => ⟨by omega, ?_⟩⟩⟩
    rw [show (-(-((home hashQ t1.size q : Nat) : Int))).toNat = home hashQ t1.size q by omega]
    refine ⟨hhr.1, hhr.2, ?_, 0, Nat.zero_le _, rfl, fun e he => absurd he (by omega)⟩
    cases hfill : filledB (t1.slots (home hashQ t1.size q))
    · rfl
    · obtain ⟨k, v, -, -, he, -, -⟩ := hi1.filled hhr.1 hhr.2 hfill
      have hm : (k, v) ∈ tlist t1 := mem_tlist.2 ⟨_, hhr.1, hhr.2, he⟩
      rw [hnil1] at hm
      cases hm
  · have hpow : IsPow t.size := by
      rcases hi.size with h | h
      · exact absurd h hs0
      · exact h
    have hmp : t.maxprobe < t.size := by
      rcases hi.maxprobe with h | h
      · exact absurd h hs0
      · exact h
    rw [ite_eq_right (by simp [hs0])]
    have hhr := home_range hpow hashQ q
    have hsh : shorthash7 (hashQ q) ≠ 127 := shorthash7_ne127 _
    have hdef : ∀ e, t.slots (pr t.size (home hashQ t.size q) e) = shorthash7 (hashQ q) →
        ∃ k, t.keys (pr t.size (home hashQ t.size q) e) = some k :=
      fun e hs => hi.key_of_tag hpow (pr_range_all hpow hhr.1 hhr.2 e) hs
    have hshq : (hashindex hashQ q t.size).2 = shorthash7 (hashQ q) := rfl
    have hhome : (hashindex hashQ q t.size).1 = home hashQ t.size q := rfl
    rw [hshq, hhome]
    rcases keyindex2Loop1_spec t (shorthash7 (hashQ q)) matchQ q (home hashQ t.size q) hsh hpow
        hhr.1 hhr.2 hmp hdef (t.maxprobe + 1) 0 0 (by omega) (fun e he => absurd he (by omega))
        (Or.inl ⟨rfl, fun e he => absurd he (by omega)⟩)
      with ⟨d, -, hd, hbd, hhit, hres⟩ | ⟨d, av, -, hd, hbd, hd0, hav, hres⟩ | ⟨hbm, av, hav, hres⟩
    all_goals rw [show pr t.size (home hashQ t.size q) 0 = home hashQ t.size q from rfl] at hres
    · -- the key is present
      rw [hres, except_ok_bind]
      show ∃ idx t' n, Except.ok ((pr t.size (home hashQ t.size q) d : Int), shorthash7 (hashQ q), t) =
        _ ∧ _
      obtain ⟨hs', k', hk', hm'⟩ := hitAt_true hhit
      have hdr := pr_range hpow hhr.1 hhr.2 (show d < t.size by omega)
      have hfill : filledB (t.slots (pr t.size (home hashQ t.size q) d)) = true := by
        rw [hs']; exact shorthash7_filled _
      obtain ⟨k2, v2, hk2, -, he2, -, -⟩ := hi.filled hdr.1 hdr.2 hfill
      rw [hk'] at hk2
      cases hk2
      refine ⟨_, t, 0, rfl, by omega, hi, List.Perm.refl _, rfl, AgeStep.refl t, ?_, ?_⟩
      · intro i e h1 h2 he hm
        refine ⟨?_, rfl⟩
        by_cases hi' : pr t.size (home hashQ t.size q) d = i
        · rw [hi']
        · exfalso
          have := hi.distinct _ i _ _ hdr.1 hdr.2 h1 h2 hi' he2 he
          dsimp only at this
          rw [hq.unique q k' e.1 hm' hm] at this
          cases this
      · intro habs
        exfalso
        have := habs _ (mem_tlist.2 ⟨_, hdr.1, hdr.2, he2⟩)
        dsimp only at this
        rw [hm'] at this
        cases this
    · -- an empty slot ends the probe: the key is absent
      rw [hres, except_ok_bind]
      show ∃ idx t' n, Except.ok ((if av < 0 then av else -(pr t.size (home hashQ t.size q) d : Int)),
        shorthash7 (hashQ q), t) = _ ∧ _
      have habs := absent_of_before hq hi hbd (Or.inl hd0)
      refine ⟨_, t, 0, rfl, by omega, hi, List.Perm.refl _, rfl, AgeStep.refl t,
        fun i e h1 h2 he hm => ?_, fun _ => ?_⟩
      · have := habs e (mem_tlist.2 ⟨i, h1, h2, he⟩)
        rw [hm] at this
        cases this
      · by_cases hav0 : av < 0
        · rw [ite_eq_left hav0]
          rcases hav with ⟨hz, -⟩ | ⟨e, he, hea, he127⟩
          · omega
          · have hre := pr_range hpow hhr.1 hhr.2 (show e < t.size by omega)
            refine ⟨hav0, ?_⟩
            rw [hea, show (-(-((pr t.size (home hashQ t.size q) e : Nat) : Int))).toNat =
              pr t.size (home hashQ t.size q) e by omega]
            exact ⟨hre.1, hre.2, by rw [he127]; exact filledB_127, e, by omega, rfl,
              fun e' he' => (hbd e' (by omega)).1⟩
        · rw [ite_eq_right hav0]
          have hdr := pr_range hpow hhr.1 hhr.2 (show d < t.size by omega)
          refine ⟨by omega, ?_⟩
          rw [show (-(-((pr t.size (home hashQ t.size q) d : Nat) : Int))).toNat =
            pr t.size (home hashQ t.size q) d by omega]
          exact ⟨hdr.1, hdr.2, by rw [hd0]; exact filledB_zero, d, hd, rfl,
            fun e' he' => (hbd e' he').1⟩
    · -- no hit and no empty slot within maxprobe: the key is absent
      rw [hres, except_ok_bind]
      have habs := absent_of_before hq hi hbm (Or.inr (by omega))
      have hnf : ∀ i e, 1 ≤ i → i ≤ t.size → ent t i = some e → matchQ q e.1 = true → False := by
        intro i e h1 h2 he hm
        have := habs e (mem_tlist.2 ⟨i, h1, h2, he⟩)
        rw [hm] at this
        cases this
      by_cases hav0 : av < 0
      · rw [k2tail_neg hav0]
        refine ⟨av, t, 0, rfl, by omega, hi, List.Perm.refl _, rfl, AgeStep.refl t,
          fun i e h1 h2 he hm => (hnf i e h1 h2 he hm).elim, fun _ => ⟨hav0, ?_⟩⟩
        rcases hav with ⟨hz, -⟩ | ⟨e, he, hea, he127⟩
        · omega
        · have hre := pr_range hpow hhr.1 hhr.2 (show e < t.size by omega)
          rw [hea, show (-(-((pr t.size (home hashQ t.size q) e : Nat) : Int))).toNat =
            pr t.size (home hashQ t.size q) e by omega]
          exact ⟨hre.1, hre.2, by rw [he127]; exact filledB_127, e, by omega, rfl,
            fun e' he' => (hbm e' (by omega)).1⟩
      · -- every probe within maxprobe is filled
        have hfilled : ∀ e, e ≤ t.maxprobe →
            filledB (t.slots (pr t.size (home hashQ t.size q) e)) = true := by
          intro e he
          have hre := pr_range hpow hhr.1 hhr.2 (show e < t.size by omega)
          rcases hi.byte hre.1 hre.2 with h | h | h
          · exact absurd h (hbm e (by omega)).1
          · rcases hav with ⟨-, hall⟩ | ⟨e', he', hea, -⟩
            · exact absurd h (hall e (by omega))
            · have hre' := pr_range hpow hhr.1 hhr.2 (show e' < t.size by omega)
              omega
          · exact h
        have h16 := hpow.ge
        have hM : max 16 (t.size >>> 6) ≤ t.size := by
          rw [Nat.shiftRight_eq_div_pow]
          have : t.size / 2 ^ 6 ≤ t.size := Nat.div_le_self _ _
          omega
        rcases keyindex2Loop2_spec t (home hashQ t.size q) (max 16 (t.size >>> 6))
            (max 16 (t.size >>> 6)) (t.maxprobe + 1) (by omega) with
          ⟨d, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
        · -- a free slot beyond maxprobe
          rw [k2tail_some hav0 h5]
          have hdr := pr_range hpow hhr.1 hhr.2 (show d < t.size by omega)
          refine ⟨_, { t with maxprobe := d }, 0, rfl, by omega,
            ⟨hi.maxprobe_up hpow (by omega) (by omega), List.Perm.refl _, rfl,
             ⟨(ageAdd_zero _).symm, fun _ => ⟨rfl, rfl, rfl, by show t.maxprobe ≤ d; omega⟩⟩,
             fun i e h1 h2 he hm => (hnf i e h1 h2 he hm).elim, fun _ => ⟨by omega, ?_⟩⟩⟩
          rw [show (-(-((pr t.size (home hashQ t.size q) d : Nat) : Int))).toNat =
            pr t.size (home hashQ t.size q) d by omega]
          refine ⟨hdr.1, hdr.2, h3, d, Nat.le_refl _, rfl, fun e he => ?_⟩
          show t.slots (pr t.size (home hashQ t.size q) e) ≠ 0
          by_cases hem : e ≤ t.maxprobe
          · exact filled_ne_zero (hfilled e hem)
          · exact filled_ne_zero (h4 e (by omega) he)
        · -- the window is full: rehash and probe again
          have hall : ∀ e, e < max 16 (t.size >>> 6) →
              filledB (t.slots (pr t.size (home hashQ t.size q) e)) = true := by
            intro e he
            by_cases hem : e ≤ t.maxprobe
            · exact hfilled e hem
            · exact h1 e (by omega) he
          have hcM := count_ge_window hi hpow hhr.1 hhr.2 hM hall
          have hwin := pow_le_window hpow
          cases f with
          | zero =>
            exfalso
            rcases hf with h | h
            · exact hs0 h
            · rw [Nat.pow_zero, Nat.mul_one] at h
              omega
          | succ f =>
            rw [k2tail_none hav0 h2]
            have hc0 : t.count ≠ 0 := by omega
            have hpow0 : IsPow (if t.count > 64000 then t.size * 2 else t.size * 4) := by
              split
              · exact hpow.double
              · exact hpow.quad
            have htab := tableszSpec_of_pow hpow0
            have hge : 2 * t.size ≤ (if t.count > 64000 then t.size * 2 else t.size * 4) := by
              split <;> omega
            have hle4 : (if t.count > 64000 then t.size * 2 else t.size * 4) ≤ 4 * t.size := by
              split <;> omega
            have hcs := hi.count_le_size
            obtain ⟨t1, h1', hi1, hp1, hs1, hc1, ha1⟩ := rehash_spec htz hi
              (if t.count > 64000 then t.size * 2 else t.size * 4) (by omega)
              (by rw [htab]; omega)
            rw [bind_of_ok h1']
            have hf1 : t1.size = 0 ∨ 64 * t1.count < t1.size * 2 ^ f := by
              right
              rcases hf with h | h
              · exact absurd h hs0
              · have e1 : t.size * 2 ^ (f + 1) = 2 * t.size * 2 ^ f := by
                  rw [Nat.pow_succ, Nat.mul_comm (2 ^ f) 2, ← Nat.mul_assoc, Nat.mul_comm t.size 2]
                have e2 : 2 * t.size * 2 ^ f ≤ t1.size * 2 ^ f :=
                  Nat.mul_le_mul_right _ (by rw [hs1, htab]; exact hge)
                rw [hc1]
                omega
            obtain ⟨idx, t2, n1, h2', hn1, hout⟩ :=
              IH f rfl fuel' t1 (by omega) hi1 (by rw [hc1]; exact hc) hf1
            refine ⟨idx, t2, 2 + n1, h2', by omega, ⟨hout.inv, hout.perm.trans hp1,
              hout.count.trans hc1, ?_, fun i e h1 h2 he hm => (hnf i e h1 h2 he hm).elim,
              fun _ => hout.absent (fun e he => habs e (hp1.mem_iff.1 he))⟩⟩
            exact (AgeStep.of_pos (by rw [ha1, ite_eq_right hc0, bump_bump]) (by omega)).trans
              hout.age

theorem htKeyindex2_spec (hl : KeyLaws hash eqKey) {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ) {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) (q : Q) :
    ∀ f fuel (t : DictState K V), f < fuel → Inv hash eqKey t → t.count < 2 ^ 54 →
      (t.size = 0 ∨ 64 * t.count < t.size * 2 ^ f) →
      ∃ idx t' n, htKeyindex2Loop hash hashQ matchQ tablesz fuel t q =
          .ok (idx, shorthash7 (hashQ q), t') ∧
        n ≤ 2 * f + 2 ∧ K2Out hash eqKey hashQ matchQ t q idx t' n := by
  intro f
  induction f with
  | zero => exact htKeyindex2_main hl hq htz q 0 (fun f h => absurd h (by omega))
  | succ f ih =>
    exact htKeyindex2_main hl hq htz q (f + 1) (fun f' h => by
      have : f' = f := by omega
      subst this
      exact ih)

/-- The insertion probe of `setindex!`/`get!` (`ht_keyindex2_shorthash!(h, key)`, fuel
`size + 64`): at most `count + 8` rehashes happen. -/
theorem htKeyindex2Query_spec (hl : KeyLaws hash eqKey) {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ) {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) {t : DictState K V} (hi : Inv hash eqKey t)
    (hc : t.count < 2 ^ 54) (q : Q) :
    ∃ idx t' n, htKeyindex2Query hash hashQ matchQ tablesz t q =
        .ok (idx, shorthash7 (hashQ q), t') ∧
      n ≤ 2 * t.count + 18 ∧ K2Out hash eqKey hashQ matchQ t q idx t' n := by
  have hf : t.size = 0 ∨ 64 * t.count < t.size * 2 ^ (t.count + 8) := by
    rcases hi.size with h | h
    · exact Or.inl h
    · right
      have h16 := h.ge
      have h1 : t.count < 2 ^ t.count := Nat.lt_two_pow_self
      have h2 : 2 ^ (t.count + 8) = 2 ^ t.count * 2 ^ 8 := Nat.pow_add 2 t.count 8
      have h3 : 16 * 2 ^ (t.count + 8) ≤ t.size * 2 ^ (t.count + 8) := Nat.mul_le_mul_right _ h16
      omega
  have hcs := hi.count_le_size
  obtain ⟨idx, t', n, h1, h2, h3⟩ :=
    htKeyindex2_spec hl hq htz q (t.count + 8) (t.size + 64) t (by omega) hi hc hf
  exact ⟨idx, t', n, h1, by omega, h3⟩

theorem htKeyindex2_spec' (hl : KeyLaws hash eqKey) {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) {t : DictState K V} (hi : Inv hash eqKey t)
    (hc : t.count < 2 ^ 54) (q : K) :
    ∃ idx t' n, htKeyindex2 hash eqKey tablesz t q = .ok (idx, shorthash7 (hash q), t') ∧
      n ≤ 2 * t.count + 18 ∧ K2Out hash eqKey hash eqKey t q idx t' n :=
  htKeyindex2Query_spec hl hl.query htz hi hc q

end Probe2


/-! ## Storing: `_setindex!` and `setindex!` -/

theorem length_filterMap_isSome {α β γ : Type} {f : α → Option β} {g : α → Option γ} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = (g x).isSome) →
      (l.filterMap f).length = (l.filterMap g).length
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    have ih := length_filterMap_isSome (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases hf : f a with
    | none =>
      cases hg : g a with
      | none => rw [List.filterMap_cons_none hf, List.filterMap_cons_none hg, ih]
      | some c => rw [hf, hg] at ha; cases ha
    | some b =>
      cases hg : g a with
      | none => rw [hf, hg] at ha; cases ha
      | some c =>
        rw [List.filterMap_cons_some hf, List.filterMap_cons_some hg, List.length_cons,
          List.length_cons, ih]

theorem rset_perm {eqKey : K → K → Bool} {m m' : List (K × V)} (h : List.Perm m m') (k : K)
    (v : V) : List.Perm (rset eqKey m k v) (rset eqKey m' k v) :=
  (h.filter _).cons _

theorem rdel_absent {Q : Type} {matchQ : Q → K → Bool} {m : List (K × V)} {q : Q}
    (h : ∀ e ∈ m, matchQ q e.1 = false) : rdel matchQ m q = m := by
  unfold rdel
  rw [List.filter_eq_self]
  intro e he
  simp [h e he]

section Set
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}

/-- Overwriting the pair of a filled slot whose key is `isequal` to `k`
(`h.keys[index] = key; h.vals[index] = v`, `base/dict.jl:364-366`). -/
theorem Inv.overwrite (hl : KeyLaws hash eqKey) {t t' : DictState K V} (hi : Inv hash eqKey t)
    {i : Nat} {k0 : K} {v0 : V} (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some (k0, v0))
    {k : K} {v : V} (hk : eqKey k k0 = true)
    (hs : t'.size = t.size) (hsl : t'.slots = t.slots)
    (hkeys : t'.keys = updateAt t.keys i (some k)) (hv : t'.vals = updateAt t.vals i (some v))
    (hc : t'.count = t.count) (hm : t'.maxprobe = t.maxprobe) (hf : t'.idxfloor = t.idxfloor)
    (hp : t'.popcursor = t.popcursor) :
    Inv hash eqKey t' ∧ List.Perm (tlist t') (rset eqKey (tlist t) k v) := by
  obtain ⟨hfi, -, -⟩ := ent_some he
  obtain ⟨k1, v1, -, -, he1, hs0, hch0⟩ := hi.filled h1 h2 hfi
  rw [he] at he1
  cases he1
  have hpp := hi.pow_of_count (hi.count_pos h1 h2 he)
  have hent : ∀ j, ent t' j = if j = i then some (k, v) else ent t j :=
    ent_store_eq hfi (by rw [hsl, updateAt_self]) hkeys hv
  have hdis : ∀ j b, 1 ≤ j → j ≤ t.size → j ≠ i → ent t j = some b → eqKey k b.1 = false := by
    intro j b hj1 hj2 hji hb
    have h0 := hi.distinct i j (k0, v0) b h1 h2 hj1 hj2 (Ne.symm hji) he hb
    cases hkb : eqKey k b.1
    · rfl
    · have := hl.trans k0 k b.1 (hl.symm k k0 hk) hkb
      dsimp only at h0
      rw [this] at h0
      cases h0
  have hstore := tlist_store (eqKey := eqKey) hs h1 h2 (fun j _ _ => hent j) hdis
    (fun b hb => by rw [he] at hb; cases hb; exact hk)
  have hhash : hash k = hash k0 := hl.hash_eq k k0 hk
  have hch : Chain hash t k i := by
    obtain ⟨d, hd, hid, hall⟩ := hch0
    refine ⟨d, hd, ?_, ?_⟩
    · rw [home_eq_of_eq hl hk]; exact hid
    · rw [home_eq_of_eq hl hk]; exact hall
  have hne : ∀ p, 1 ≤ p → p ≤ t.size → t.slots p ≠ 0 → t'.slots p ≠ 0 :=
    fun p _ _ h => by rw [hsl]; exact h
  refine ⟨⟨by rw [hs]; exact hi.size, by rw [hs]; exact hi.sizeLe, ?_, ?_, ?_, ?_,
    by rw [hf]; exact hi.idxfloor, ?_, by rw [hp]; exact hi.popcursor⟩, hstore⟩
  · intro j hj1 hj2
    rw [hs] at hj2
    by_cases hji : j = i
    · subst hji
      refine Or.inr (Or.inr ⟨k, v, by rw [hkeys, updateAt_same], by rw [hv, updateAt_same],
        by rw [hsl, hs0, hhash], ?_⟩)
      exact Chain.mono hpp.1 hpp.2 hs (by rw [hm]; exact Nat.le_refl _) hne hch
    · exact SlotOK.transfer (hi.slot j hj1 hj2) (by rw [hsl])
        (by rw [hkeys, updateAt_ne _ _ hji]) (by rw [hv, updateAt_ne _ _ hji])
        (fun k' hc' => Chain.mono hpp.1 hpp.2 hs (by rw [hm]; exact Nat.le_refl _) hne hc')
  · intro a b x y ha1 ha2 hb1 hb2 hab hx hy
    rw [hs] at ha2 hb2
    rw [hent] at hx hy
    by_cases hai : a = i
    · rw [ite_eq_left hai] at hx
      cases hx
      have hbi : b ≠ i := fun h => hab (hai.trans h.symm)
      rw [ite_eq_right hbi] at hy
      exact hdis b y hb1 hb2 hbi hy
    · rw [ite_eq_right hai] at hx
      by_cases hbi : b = i
      · rw [ite_eq_left hbi] at hy
        cases hy
        exact eq_false_symm hl (hdis a x ha1 ha2 hai hx)
      · rw [ite_eq_right hbi] at hy
        exact hi.distinct a b x y ha1 ha2 hb1 hb2 hab hx hy
  · rw [hc, hi.count]
    unfold tlist
    rw [hs]
    symm
    apply length_filterMap_isSome
    intro x _
    rw [hent x]
    by_cases hxi : x = i
    · rw [ite_eq_left hxi, hxi, he]; rfl
    · rw [ite_eq_right hxi]
  · rw [hm, hs]; exact Or.inr hpp.2
  · intro j hj1 hj2 hfj
    rw [hs] at hj2
    rw [hsl] at hfj
    rw [hf]
    exact hi.floorLe j hj1 hj2 hfj

/-- The table after the stores of `_setindex!` and before its rehash check. -/
def storeAt (t : DictState K V) (v : V) (k : K) (j sh : Nat) : DictState K V :=
  DictState.mk t.size (updateAt t.slots j sh) (updateAt t.keys j (some k))
    (updateAt t.vals j (some v)) (t.ndel - if isslotmissing t j then 1 else 0) (t.count + 1)
    (bumpAge t.age) (min t.idxfloor j) t.maxprobe t.popcursor

theorem setindexAt_eq (tablesz : Nat → Nat) (t : DictState K V) (v : V) (k : K) (j sh : Nat) :
    setindexAt hash tablesz t v k j sh =
      if ((storeAt t v k j sh).count + (storeAt t v k j sh).ndel) * 3 >
          (storeAt t v k j sh).size * 2 then
        rehash hash tablesz (storeAt t v k j sh)
          (if (storeAt t v k j sh).count > 64000 then (storeAt t v k j sh).count * 2
            else max ((storeAt t v k j sh).count * 4) 4) >>= fun t' => .ok ((), t')
      else .ok ((), storeAt t v k j sh) := rfl

/-- `_setindex!(h, v, key, index, sh)` at a free slot of the probe sequence of an absent key
stores the pair, and its rehash keeps every pair. -/
theorem setindexAt_spec (hl : KeyLaws hash eqKey) {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) {t : DictState K V} (hi : Inv hash eqKey t) (hc : t.count < 2 ^ 54)
    {j : Nat} {k : K} {v : V} (hj : InsertSlot t (home hash t.size k) j)
    (habs : Absent eqKey t k) :
    ∃ t', setindexAt hash tablesz t v k j (shorthash7 (hash k)) = .ok ((), t') ∧
      Inv hash eqKey t' ∧ List.Perm (tlist t') ((k, v) :: tlist t) ∧ t'.count = t.count + 1 ∧
      (t'.age = ageAdd t.age 1 ∨ t'.age = ageAdd t.age 3) := by
  obtain ⟨hi1, hp1⟩ := Inv.store hl hi hj habs (t' := storeAt t v k j (shorthash7 (hash k)))
    rfl rfl rfl rfl rfl rfl
    (by show 1 ≤ min t.idxfloor j; have := hi.idxfloor; have := hj.1; omega)
    (Nat.min_le_left _ _) (Nat.min_le_right _ _) hi.popcursor
  rw [setindexAt_eq]
  have hc1 : (storeAt t v k j (shorthash7 (hash k))).count = t.count + 1 := rfl
  split
  · have hns : (if (storeAt t v k j (shorthash7 (hash k))).count > 64000 then
        (storeAt t v k j (shorthash7 (hash k))).count * 2
        else max ((storeAt t v k j (shorthash7 (hash k))).count * 4) 4) ≤ 4 * t.count + 4 ∧
        2 * (t.count + 1) ≤ (if (storeAt t v k j (shorthash7 (hash k))).count > 64000 then
        (storeAt t v k j (shorthash7 (hash k))).count * 2
        else max ((storeAt t v k j (shorthash7 (hash k))).count * 4) 4) := by
      rw [hc1]
      split <;> omega
    generalize hN : (if (storeAt t v k j (shorthash7 (hash k))).count > 64000 then
      (storeAt t v k j (shorthash7 (hash k))).count * 2
      else max ((storeAt t v k j (shorthash7 (hash k))).count * 4) 4) = N at hns ⊢
    have hge := tableszSpec_ge N
    obtain ⟨t2, h2, hi2, hp2, -, hc2, ha2⟩ := rehash_spec htz hi1 N (by omega) (by omega)
    rw [bind_of_ok h2]
    refine ⟨t2, rfl, hi2, hp2.trans hp1, hc2.trans hc1, Or.inr ?_⟩
    rw [ha2, ite_eq_right (by rw [hc1]; omega)]
    show bumpAge (bumpAge (bumpAge t.age)) = _
    rw [bump_bump, bump_eq t.age, ageAdd_add]
  · exact ⟨_, rfl, hi1, hp1, hc1, Or.inl (bump_eq _)⟩

/-- The stores after the insertion probe of `setindex!`/`get!` (`base/dict.jl:362-369,751-757`). -/
def storeBody (hash : K → JInt .u64) (tablesz : Nat → Nat) (h : DictState K V) (value : V) (key : K)
    (index : Int) (shortHash : Nat) : DictResult (DictState K V) :=
  if index > 0 then
    .ok (DictState.mk h.size h.slots (updateAt h.keys index.toNat (some key))
      (updateAt h.vals index.toNat (some value)) h.ndel h.count (bumpAge h.age)
      h.idxfloor h.maxprobe h.popcursor)
  else do
    let (_, h) ← setindexAt hash tablesz h value key (-index).toNat shortHash
    .ok h

/-- Insertion probe followed by the stores: the table represents `rset (tlist t) k v`. -/
theorem storeBody_spec (hl : KeyLaws hash eqKey) {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) {t t1 : DictState K V} (hi : Inv hash eqKey t)
    (hc : t.count < 2 ^ 54) {k : K} {v : V} {idx : Int} {n : Nat}
    (hout : K2Out hash eqKey hash eqKey t k idx t1 n) :
    ∃ t', storeBody hash tablesz t1 v k idx (shorthash7 (hash k)) = .ok t' ∧
      Inv hash eqKey t' ∧ List.Perm (tlist t') (rset eqKey (tlist t) k v) ∧
      ∃ n', 0 < n' ∧ n' ≤ 3 ∧ t'.age = ageAdd t1.age n' := by
  cases hf : rfind eqKey (tlist t) k with
  | some e =>
    obtain ⟨hem, heq⟩ := rfind_some hf
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
    obtain ⟨hidx, ht1⟩ := hout.found i e h1 h2 hei heq
    obtain ⟨k0, v0⟩ := e
    subst hidx
    rw [ht1]
    unfold storeBody
    rw [ite_eq_left (by omega)]
    have hti : ((i : Int)).toNat = i := by omega
    rw [hti]
    obtain ⟨hi', hp'⟩ := Inv.overwrite hl hi h1 h2 hei heq
      (t' := DictState.mk t.size t.slots (updateAt t.keys i (some k)) (updateAt t.vals i (some v))
        t.ndel t.count (bumpAge t.age) t.idxfloor t.maxprobe t.popcursor)
      rfl rfl rfl rfl rfl rfl rfl rfl
    exact ⟨_, rfl, hi', hp', 1, by omega, by omega, bump_eq _⟩
  | none =>
    have habs := rfind_eq_none_iff.1 hf
    obtain ⟨hneg, hslot⟩ := hout.absent habs
    unfold storeBody
    rw [ite_eq_right (by omega)]
    have habs1 : Absent eqKey t1 k := fun e he => habs e (hout.perm.mem_iff.1 he)
    obtain ⟨t', h', hi', hp', -, ha'⟩ := setindexAt_spec hl htz hout.inv
      (by rw [hout.count]; exact hc) hslot habs1 (v := v)
    rw [bind_of_ok h']
    refine ⟨t', rfl, hi', ?_, ?_⟩
    · refine hp'.trans ((hout.perm.cons _).trans ?_)
      unfold rset
      rw [rdel_absent habs]
    · rcases ha' with h | h
      · exact ⟨1, by omega, by omega, h⟩
      · exact ⟨3, by omega, by omega, h⟩

theorem setindexAny_eq (tablesz : Nat → Nat) (t : DictState K V) (v : V) (k : K) :
    setindexAny hash eqKey tablesz t v k =
      (htKeyindex2 hash eqKey tablesz t k >>= fun r => storeBody hash tablesz r.2.2 v k r.1 r.2.1) := by
  unfold setindexAny storeBody
  cases htKeyindex2 hash eqKey tablesz t k with
  | error e => rfl
  | ok r => obtain ⟨a, b, c⟩ := r; rfl

theorem setindexTyped_eq {W : Type} (tablesz : Nat → Nat) (valueConv : ValueConv W V)
    (t : DictState K V) (w : W) (k : K) :
    setindexTyped hash eqKey tablesz valueConv t w k =
      (convertValue valueConv w >>= fun v =>
        htKeyindex2 hash eqKey tablesz t k >>= fun r => storeBody hash tablesz r.2.2 v k r.1 r.2.1) := by
  unfold setindexTyped storeBody
  cases convertValue valueConv w with
  | error e => rfl
  | ok v =>
    show (htKeyindex2 hash eqKey tablesz t k >>= _) = (htKeyindex2 hash eqKey tablesz t k >>= _)
    cases htKeyindex2 hash eqKey tablesz t k with
    | error e => rfl
    | ok r => obtain ⟨a, b, c⟩ := r; rfl

theorem setindexConv_eq {Q W : Type} (tablesz : Nat → Nat) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (t : DictState K V) (w : W) (q : Q) :
    setindexConv hash eqKey tablesz keyConv valueConv t w q =
      (convKey keyConv q >>= fun k => setindexTyped hash eqKey tablesz valueConv t w k) := by
  unfold setindexConv convKey
  cases keyConv.isa q with
  | some k => rfl
  | none =>
    cases keyConv.convert q with
    | error e => rfl
    | ok k => by_cases he : keyConv.isequal q k = true <;> simp [he]

/-- `setindex!` with an already converted value on a represented table. -/
theorem DictRep.store (hl : KeyLaws hash eqKey) {tablesz : Nat → Nat} (htz : TableszLaw tablesz)
    {t : DictState K V} {m : List (K × V)} (h : DictRep hash eqKey t m) (hc : t.count < 2 ^ 54)
    (k : K) (v : V) :
    ∃ t', (htKeyindex2 hash eqKey tablesz t k >>= fun r =>
        storeBody hash tablesz r.2.2 v k r.1 r.2.1) = .ok t' ∧
      DictRep hash eqKey t' (rset eqKey m k v) := by
  obtain ⟨idx, t1, n, hprobe, -, hout⟩ := htKeyindex2_spec' hl htz h.1 hc k
  obtain ⟨t', hs, hi', hp', -⟩ := storeBody_spec hl htz h.1 hc hout (v := v)
  rw [hprobe, except_ok_bind]
  exact ⟨t', hs, hi', hp'.trans (rset_perm h.2 k v)⟩

end Set


/-! ## `get!` -/

section GetBang
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}

/-- `default` behaves like Julia code that uses the `Dict` API on the table it is given: on a
well-formed table with fewer than `2^54` pairs it returns a well-formed table with fewer than
`2^54` pairs and advances `age` by fewer than `2^64` steps, leaving slots and keys alone when it
does not advance `age`. -/
def DefaultOK {W : Type} (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (default : DictState K V → DictResult (W × DictState K V)) : Prop :=
  ∀ h0 w h2, Inv hash eqKey h0 → h0.count < 2 ^ 54 → default h0 = .ok (w, h2) →
    Inv hash eqKey h2 ∧ h2.count < 2 ^ 54 ∧ ∃ n, n < 2 ^ 64 ∧ AgeStep h0 h2 n

theorem absent_of_same {t t' : DictState K V} (hi : Inv hash eqKey t) (hs : Same t t') {k : K}
    (habs : ∀ e ∈ tlist t, eqKey k e.1 = false) : ∀ e ∈ tlist t', eqKey k e.1 = false := by
  intro e he
  obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 he
  obtain ⟨hf, hk, -⟩ := ent_some hei
  rw [hs.1] at h2
  rw [hs.2.1] at hf
  obtain ⟨k', v', hk', -, he', -, -⟩ := hi.filled h1 h2 hf
  rw [hs.2.2.1, hk'] at hk
  cases hk
  exact habs (e.1, v') (mem_tlist.2 ⟨i, h1, h2, he'⟩)

theorem InsertSlot.same {t t' : DictState K V} (hs : Same t t') {hm j : Nat}
    (h : InsertSlot t hm j) : InsertSlot t' hm j := by
  obtain ⟨h1, h2, hf, d, hd, hj, hall⟩ := h
  refine ⟨h1, by rw [hs.1]; exact h2, by rw [hs.2.1]; exact hf, d, Nat.le_trans hd hs.2.2.2,
    by rw [hs.1]; exact hj, fun e he => ?_⟩
  rw [hs.1, hs.2.1]
  exact hall e he

/-- The stores of `get!` after `default()` (`base/dict.jl:751-758`). -/
def getTail (hash : K → JInt .u64) (tablesz : Nat → Nat) (value : V) (key : K) :
    Int × Nat × DictState K V → DictResult (V × DictState K V)
  | (index, shortHash, h) =>
    if index > 0 then
      .ok (value, DictState.mk h.size h.slots (updateAt h.keys index.toNat (some key))
        (updateAt h.vals index.toNat (some value)) h.ndel h.count (bumpAge h.age)
        h.idxfloor h.maxprobe h.popcursor)
    else do
      let (_, h) ← setindexAt hash tablesz h value key (-index).toNat shortHash
      .ok (value, h)

theorem getTail_eq (tablesz : Nat → Nat) (v : V) (k : K) (idx : Int) (sh : Nat)
    (t : DictState K V) :
    getTail hash tablesz v k (idx, sh, t) =
      (storeBody hash tablesz t v k idx sh >>= fun t' => .ok (v, t')) := by
  unfold getTail storeBody
  dsimp only
  by_cases hp : idx > 0
  · rw [ite_eq_left hp, ite_eq_left hp]; rfl
  · rw [ite_eq_right hp, ite_eq_right hp]
    cases setindexAt hash tablesz t v k (-idx).toNat sh with
    | error e => rfl
    | ok r => obtain ⟨a, b⟩ := r; rfl

theorem getBang_eq {W : Type} (tablesz : Nat → Nat) (valueConv : ValueConv W V)
    (t : DictState K V) (k : K) (default : DictState K V → DictResult (W × DictState K V)) :
    getBang hash eqKey tablesz valueConv t k default =
      (htKeyindex2 hash eqKey tablesz t k >>= fun r =>
        if r.1 > 0 then valAt r.2.2 r.1.toNat >>= fun v => .ok (v, r.2.2)
        else default r.2.2 >>= fun d => convertValue valueConv d.1 >>= fun v =>
          (if d.2.age != r.2.2.age then htKeyindex2 hash eqKey tablesz d.2 k
            else .ok (r.1, r.2.1, d.2)) >>= getTail hash tablesz v k) := by
  unfold getBang
  cases htKeyindex2 hash eqKey tablesz t k with
  | error e => rfl
  | ok r =>
    obtain ⟨idx, sh, t1⟩ := r
    show _ = (if idx > 0 then _ else _)
    by_cases hp : idx > 0
    · rw [ite_eq_left hp]
      show (if idx > 0 then _ else _) = _
      rw [ite_eq_left hp]
    · rw [ite_eq_right hp]
      show (if idx > 0 then _ else _) = _
      rw [ite_eq_right hp]
      cases default t1 with
      | error e => rfl
      | ok d =>
        obtain ⟨w, t2⟩ := d
        show (convertValue valueConv w >>= _) = (convertValue valueConv w >>= _)
        cases convertValue valueConv w with
        | error e => rfl
        | ok v =>
          rw [except_ok_bind, except_ok_bind]
          dsimp only
          by_cases ha : (t2.age != t1.age) = true
          · rw [ite_eq_left ha, ite_eq_left ha]
            cases htKeyindex2 hash eqKey tablesz t2 k with
            | error e => rfl
            | ok r => obtain ⟨a, b, c⟩ := r; rfl
          · rw [ite_eq_right ha, ite_eq_right ha]; rfl

/-- `get!(default, h, key)`: a present key returns its value and leaves the table alone; an
absent key calls `default` on a table with the same pairs and stores the converted result on top
of every change `default` made. -/
theorem getBang_spec (hl : KeyLaws hash eqKey) {tablesz : Nat → Nat} (htz : TableszLaw tablesz)
    {W : Type} (valueConv : ValueConv W V) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (hc : t.count < 2 ^ 54) (k : K)
    (default : DictState K V → DictResult (W × DictState K V)) (hdef : DefaultOK hash eqKey default) :
    match rfind eqKey m k with
    | some e => getBang hash eqKey tablesz valueConv t k default = .ok (e.2, t)
    | none => ∃ t1, DictRep hash eqKey t1 m ∧
        (∀ err, default t1 = .error err →
          getBang hash eqKey tablesz valueConv t k default = .error err) ∧
        (∀ w t2, default t1 = .ok (w, t2) →
          match convertValue valueConv w with
          | .error err => getBang hash eqKey tablesz valueConv t k default = .error err
          | .ok v => ∃ t', getBang hash eqKey tablesz valueConv t k default = .ok (v, t') ∧
              DictRep hash eqKey t' (rset eqKey (tlist t2) k v)) := by
  have hd : Distinct eqKey (tlist t) := tlist_pairwise h.1
  rw [← rfind_perm hl hl.query hd h.2]
  obtain ⟨idx, t1, n, hprobe, -, hout⟩ := htKeyindex2_spec' hl htz h.1 hc k
  rw [getBang_eq, hprobe, except_ok_bind]
  cases hf : rfind eqKey (tlist t) k with
  | some e =>
    obtain ⟨hem, heq⟩ := rfind_some hf
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
    obtain ⟨hidx, ht1⟩ := hout.found i e h1 h2 hei heq
    obtain ⟨k0, v0⟩ := e
    subst hidx
    rw [ht1]
    show (if ((i : Nat) : Int) > 0 then _ else _) = _
    rw [ite_eq_left (by omega), show ((i : Nat) : Int).toNat = i by omega, valAt_of_ent hei]
    rfl
  | none =>
    have habs := rfind_eq_none_iff.1 hf
    obtain ⟨hneg, hslot⟩ := hout.absent habs
    refine ⟨t1, ⟨hout.inv, hout.perm.trans h.2⟩, fun err herr => ?_, fun w t2 hw => ?_⟩
    · show (if idx > 0 then _ else _) = _
      rw [ite_eq_right (by omega)]
      show (default t1 >>= _) = _
      rw [herr]
      rfl
    · obtain ⟨hi2, hc2, n2, hn2, hage2⟩ := hdef t1 w t2 hout.inv (by rw [hout.count]; exact hc) hw
      show (match convertValue valueConv w with
        | .error err => (if idx > 0 then _ else _) = Except.error err
        | .ok v => _)
      cases hv : convertValue valueConv w with
      | error err =>
        show (if idx > 0 then _ else _) = _
        rw [ite_eq_right (by omega)]
        show (default t1 >>= _) = _
        rw [hw]
        show (convertValue valueConv w >>= _) = _
        rw [hv]
        rfl
      | ok v =>
        show ∃ t', (if idx > 0 then _ else _) = _ ∧ _
        rw [ite_eq_right (by omega)]
        show ∃ t', (default t1 >>= _) = _ ∧ _
        rw [hw, except_ok_bind]
        show ∃ t', (convertValue valueConv w >>= _) = _ ∧ _
        rw [hv, except_ok_bind]
        dsimp only
        by_cases hn0 : n2 = 0
        · -- `age` unchanged: the earlier probe result is still valid
          have hsame := hage2.2 hn0
          have hagee : t2.age = t1.age := by rw [hage2.1, hn0, ageAdd_zero]
          rw [ite_eq_right (by simp [hagee]), except_ok_bind, getTail_eq]
          have habs1 : ∀ e ∈ tlist t1, eqKey k e.1 = false :=
            fun e he => habs e (hout.perm.mem_iff.1 he)
          have habs2 := absent_of_same hout.inv hsame habs1
          have hout2 : K2Out hash eqKey hash eqKey t2 k idx t2 0 :=
            ⟨hi2, List.Perm.refl _, rfl, AgeStep.refl t2,
              fun i e h1 h2 he hm => absurd hm (by rw [habs2 e (mem_tlist.2 ⟨i, h1, h2, he⟩)]; simp),
              fun _ => ⟨hneg, by rw [hsame.1]; exact hslot.same hsame⟩⟩
          obtain ⟨t', hs', hi', hp', -⟩ := storeBody_spec hl htz hi2 hc2 hout2 (v := v)
          rw [hout2.inv.size.elim (fun _ => hs') (fun _ => hs')] at *
          exact ⟨t', by rw [hs']; rfl, hi', hp'⟩
        · -- `age` changed: probe again
          have hagen : (t2.age != t1.age) = true := by
            have := ageAdd_ne t1.age (n := n2) (by omega) hn2
            rw [← hage2.1] at this
            simp only [bne_iff_ne, ne_eq]
            intro heq
            exact this (by rw [heq])
          rw [ite_eq_left hagen]
          obtain ⟨idx2, t3, n3, hprobe2, -, hout3⟩ := htKeyindex2_spec' hl htz hi2 hc2 k
          rw [hprobe2, except_ok_bind, getTail_eq]
          obtain ⟨t', hs', hi', hp', -⟩ := storeBody_spec hl htz hi2 hc2 hout3 (v := v)
          exact ⟨t', by rw [hs']; rfl, hi', hp'⟩

end GetBang


/-! ## `_delete!`

`_delete!` empties the slot when the next slot is empty, together with the run of deleted slots
before it (which may wrap from index 1 to `size`), and otherwise leaves a `0x7f` tombstone. A key
whose probe chain crossed a cleared slot would have had to cross the empty slot after the run, so
every chain of a remaining key survives. -/

/-- `r` backward steps from `i`. -/
def bk (sz i : Nat) : Nat → Nat
  | 0 => i
  | r + 1 => previousIndex sz (bk sz i r)

theorem bk_range {sz i : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    ∀ r, 1 ≤ bk sz i r ∧ bk sz i r ≤ sz
  | 0 => ⟨h1, h2⟩
  | r + 1 => by
    have ih := bk_range h hs h1 h2 r
    exact (nextIndex_previousIndex h hs ih.1 ih.2).2

theorem next_bk {sz i : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i) (h2 : i ≤ sz)
    (r : Nat) : nextIndex sz (bk sz i (r + 1)) = bk sz i r := by
  have ih := bk_range h hs h1 h2 r
  exact (nextIndex_previousIndex h hs ih.1 ih.2).1

/-- Slots after emptying `bk 0, ..., bk (r-1)`. -/
def clr (sz i : Nat) (S : Nat → Nat) : Nat → Nat → Nat
  | 0 => S
  | r + 1 => updateAt (clr sz i S r) (bk sz i r) 0

theorem clr_spec (sz i : Nat) (S : Nat → Nat) : ∀ r p,
    (clr sz i S r p = S p ∧ ∀ s, s < r → p ≠ bk sz i s) ∨
      (clr sz i S r p = 0 ∧ ∃ s, s < r ∧ p = bk sz i s)
  | 0, _ => Or.inl ⟨rfl, fun s hs => absurd hs (by omega)⟩
  | r + 1, p => by
    have e : clr sz i S (r + 1) p = updateAt (clr sz i S r) (bk sz i r) 0 p := rfl
    rw [e]
    by_cases hp : p = bk sz i r
    · exact Or.inr ⟨by rw [hp, updateAt_same], r, by omega, hp⟩
    · rw [updateAt_ne _ _ hp]
      rcases clr_spec sz i S r p with ⟨h1, h2⟩ | ⟨h1, s, hs, h2⟩
      · refine Or.inl ⟨h1, fun s hs => ?_⟩
        by_cases hsr : s = r
        · rw [hsr]; exact hp
        · exact h2 s (by omega)
      · exact Or.inr ⟨h1, s, by omega, h2⟩

/-- The tombstone-clearing loop empties `bk 0, ..., bk (R-1)` for some `R ≥ 1`, all of which
except `bk 0` held `0x7f`. -/
theorem clearBackward_spec {sz i : Nat} (S : Nat → Nat) :
    ∀ left r (ndel : Int), 1 ≤ r + left → (∀ s, 1 ≤ s → s ≤ r → S (bk sz i s) = 127) →
      ∃ R nd, 1 ≤ R ∧ (∀ s, 1 ≤ s → s < R → S (bk sz i s) = 127) ∧
        clearBackward sz (clr sz i S r) left (bk sz i r) ndel = (clr sz i S R, nd)
  | 0, r, ndel, hr, hS => ⟨r, ndel, by omega, fun s hs1 hs2 => hS s hs1 (by omega), rfl⟩
  | left + 1, r, ndel, _, hS => by
    have e : clearBackward sz (clr sz i S r) (left + 1) (bk sz i r) ndel =
        if (clr sz i S (r + 1) (bk sz i (r + 1)) == 0x7f) = true then
          clearBackward sz (clr sz i S (r + 1)) left (bk sz i (r + 1)) (ndel - 1)
        else (clr sz i S (r + 1), ndel - 1) := rfl
    rw [e]
    by_cases hm : (clr sz i S (r + 1) (bk sz i (r + 1)) == 0x7f) = true
    · rw [if_pos hm]
      have h127 : clr sz i S (r + 1) (bk sz i (r + 1)) = 127 := by simpa using hm
      have hS' : S (bk sz i (r + 1)) = 127 := by
        rcases clr_spec sz i S (r + 1) (bk sz i (r + 1)) with ⟨ha, -⟩ | ⟨ha, -⟩
        · rw [← ha]; exact h127
        · rw [ha] at h127; cases h127
      exact clearBackward_spec S left (r + 1) (ndel - 1) (by omega) (fun s hs1 hs2 => by
        by_cases hsr : s = r + 1
        · rw [hsr]; exact hS'
        · exact hS s hs1 (by omega))
    · rw [if_neg hm]
      exact ⟨r + 1, ndel - 1, by omega, fun s hs1 hs2 => hS s hs1 (by omega), rfl⟩

/-- The slot bytes and tombstone change computed by `_delete!`. -/
def delD (t : DictState K V) (i : Nat) : (Nat → Nat) × Int :=
  if isslotempty t (nextIndex t.size i) then clearBackward t.size t.slots t.size i 1
  else (updateAt t.slots i 0x7f, 1)

/-- `_delete!` with the computed slot bytes and tombstone count `D`. -/
def delT (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) (t : DictState K V) (i : Nat)
    (D : (Nat → Nat) × Int) : DictState K V :=
  DictState.mk t.size D.1 (unsetKey t.size t.keys i) (unsetVal t.size t.vals i)
    ((t.ndel : Int) + D.2).toNat (t.count - 1) (bumpAge t.age) t.idxfloor t.maxprobe t.popcursor

theorem deleteAt_eq (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) (t : DictState K V) (i : Nat) :
    deleteAt unsetKey unsetVal t i = delT unsetKey unsetVal t i (delD t i) := by
  unfold deleteAt delD delT
  dsimp only
  generalize (if isslotempty t (nextIndex t.size i) = true then
    clearBackward t.size t.slots t.size i 1 else (updateAt t.slots i 0x7f, 1)) = D
  cases D
  rfl

theorem ent_congr {t t' : DictState K V} {p : Nat} (hs : t'.slots p = t.slots p)
    (hk : t'.keys p = t.keys p) (hv : t'.vals p = t.vals p) : ent t' p = ent t p := by
  unfold ent
  rw [hs, hk, hv]

/-- Clearing the entry at `i` with new slot bytes that keep every remaining chain. -/
theorem Inv.clear {hash : K → JInt .u64} {eqKey : K → K → Bool} (hl : KeyLaws hash eqKey)
    {t t' : DictState K V} (hi : Inv hash eqKey t) {i : Nat}
    (h1 : 1 ≤ i) (h2 : i ≤ t.size) {e : K × V} (he : ent t i = some e)
    (hs : t'.size = t.size) (hk : ∀ p, p ≠ i → t'.keys p = t.keys p)
    (hv : ∀ p, p ≠ i → t'.vals p = t.vals p)
    (hc : t'.count = t.count - 1) (hm : t'.maxprobe = t.maxprobe) (hf : t'.idxfloor = t.idxfloor)
    (hp : t'.popcursor = t.popcursor)
    (hA : t'.slots i = 0 ∨ t'.slots i = 127)
    (hB : ∀ p, p ≠ i → t'.slots p = t.slots p ∨ (t.slots p = 127 ∧ t'.slots p = 0))
    (hC : ∀ q hh d, filledB (t.slots q) = true → q ≠ i → q = pr t.size hh d → d < t.size →
      1 ≤ hh → hh ≤ t.size → (∀ e, e < d → t.slots (pr t.size hh e) ≠ 0) →
      ∀ e, e < d → t'.slots (pr t.size hh e) ≠ 0) :
    Inv hash eqKey t' ∧ tlist t' = (tlist t).filter (fun b => !eqKey e.1 b.1) := by
  have hnfi : filledB (t'.slots i) = false := by
    rcases hA with h | h <;> rw [h] <;> decide
  have hent : ∀ p, ent t' p = if p = i then none else ent t p := by
    intro p
    by_cases hpi : p = i
    · rw [if_pos hpi, hpi]
      exact ent_of_not_filled hnfi
    · rw [if_neg hpi]
      rcases hB p hpi with h | ⟨h127, h0⟩
      · exact ent_congr h (hk p hpi) (hv p hpi)
      · rw [ent_of_not_filled (by rw [h0]; decide), ent_of_not_filled (by rw [h127]; decide)]
  have hdis : ∀ p b, 1 ≤ p → p ≤ t.size → p ≠ i → ent t p = some b → eqKey e.1 b.1 = false :=
    fun p b hp1 hp2 hpi hb => hi.distinct i p e b h1 h2 hp1 hp2 (Ne.symm hpi) he hb
  have hsame : ∀ b, ent t i = some b → eqKey e.1 b.1 = true := by
    intro b hb
    rw [he] at hb
    cases hb
    exact hl.refl _
  have htl : tlist t' = (tlist t).filter (fun b => !eqKey e.1 b.1) :=
    tlist_clear hs (fun p _ _ => hent p) hdis hsame
  have hself := tlist_store (t := t) (t' := t) (e := e) rfl h1 h2
    (fun p _ _ => by
      by_cases hp : p = i
      · rw [if_pos hp, hp, he]
      · rw [if_neg hp]) hdis hsame
  have hlen : (tlist t).length = (tlist t').length + 1 := by
    rw [htl, hself.length_eq, List.length_cons]
  have hpow : IsPow t.size := by
    rcases hi.size with h | h
    · omega
    · exact h
  have hmp : t.maxprobe < t.size := by
    rcases hi.maxprobe with h | h
    · omega
    · exact h
  refine ⟨⟨by rw [hs]; exact hi.size, by rw [hs]; exact hi.sizeLe, fun p hp1 hp2 => ?_, ?_, ?_,
    by rw [hm, hs]; exact hi.maxprobe, by rw [hf]; exact hi.idxfloor, fun p hp1 hp2 hfp => ?_,
    by rw [hp]; exact hi.popcursor⟩, htl⟩
  · rw [hs] at hp2
    by_cases hpi : p = i
    · rw [hpi]
      rcases hA with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hi.slot p hp1 hp2 with h0 | h127 | ⟨k, v, hkp, hvp, hsp, d, hd, hid, hall⟩
      · left
        rcases hB p hpi with h | ⟨h, -⟩
        · rw [h, h0]
        · rw [h0] at h; exact absurd h (by decide)
      · rcases hB p hpi with h | ⟨-, h⟩
        · exact Or.inr (Or.inl (by rw [h, h127]))
        · exact Or.inl h
      · have hsp' : t'.slots p = t.slots p := by
          rcases hB p hpi with h | ⟨h, -⟩
          · exact h
          · rw [hsp] at h; exact absurd h (shorthash7_ne127 _)
        have hfp : filledB (t.slots p) = true := by rw [hsp]; exact shorthash7_filled _
        have hhr := home_range hpow hash k
        refine Or.inr (Or.inr ⟨k, v, by rw [hk p hpi]; exact hkp,
          by rw [hv p hpi]; exact hvp, by rw [hsp', hsp], d, by rw [hm]; exact hd,
          by rw [hs]; exact hid, ?_⟩)
        rw [hs]
        exact hC p (home hash t.size k) d hfp hpi hid (by omega) hhr.1 hhr.2 hall
  · intro a b a' b' ha1 ha2 hb1 hb2 hab hea heb
    rw [hs] at ha2 hb2
    rw [hent] at hea heb
    by_cases hai : a = i
    · rw [if_pos hai] at hea; cases hea
    · by_cases hbi : b = i
      · rw [if_pos hbi] at heb; cases heb
      · rw [if_neg hai] at hea
        rw [if_neg hbi] at heb
        exact hi.distinct a b a' b' ha1 ha2 hb1 hb2 hab hea heb
  · have := hi.count
    omega
  · rw [hs] at hp2
    have hpi : p ≠ i := fun h => by rw [h, hnfi] at hfp; cases hfp
    have hfp' : filledB (t.slots p) = true := by
      rcases hB p hpi with h | ⟨-, h⟩
      · rw [← h]; exact hfp
      · rw [h] at hfp; cases hfp
    rw [hf]
    exact hi.floorLe p hp1 hp2 hfp'

/-- Positions `e + s` on a probe sequence through `bk r` walk forward to `bk (r - s)`. -/
theorem pr_bk {sz i hh e r : Nat} (hp : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i) (h2 : i ≤ sz)
    (hpr : pr sz hh e = bk sz i r) : ∀ s, s ≤ r → pr sz hh (e + s) = bk sz i (r - s)
  | 0, _ => hpr
  | s + 1, hsr => by
    rw [← Nat.add_assoc, pr_succ, pr_bk hp hs h1 h2 hpr s (by omega),
      show r - s = r - (s + 1) + 1 by omega, next_bk hp hs h1 h2]

/-- `_delete!(h, index)` on a filled slot removes exactly that pair. -/
theorem deleteAt_spec {hash : K → JInt .u64} {eqKey : K → K → Bool} (hl : KeyLaws hash eqKey)
    {unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K)}
    {unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)}
    (huk : UnsetLaw unsetKey) (huv : UnsetLaw unsetVal)
    {t : DictState K V} (hi : Inv hash eqKey t) {i : Nat}
    (h1 : 1 ≤ i) (h2 : i ≤ t.size) {e : K × V} (he : ent t i = some e) :
    Inv hash eqKey (deleteAt unsetKey unsetVal t i) ∧
      tlist (deleteAt unsetKey unsetVal t i) = (tlist t).filter (fun b => !eqKey e.1 b.1) ∧
      (deleteAt unsetKey unsetVal t i).count = t.count - 1 ∧
      (deleteAt unsetKey unsetVal t i).age = bumpAge t.age ∧
      (deleteAt unsetKey unsetVal t i).size = t.size ∧
      (deleteAt unsetKey unsetVal t i).idxfloor = t.idxfloor ∧
      (deleteAt unsetKey unsetVal t i).popcursor = t.popcursor ∧
      (deleteAt unsetKey unsetVal t i).maxprobe = t.maxprobe ∧
      filledB ((deleteAt unsetKey unsetVal t i).slots i) = false ∧
      ∀ p, p ≠ i → filledB ((deleteAt unsetKey unsetVal t i).slots p) = filledB (t.slots p) ∧
        ent (deleteAt unsetKey unsetVal t i) p = ent t p := by
  have hpow : IsPow t.size := by
    rcases hi.size with h | h
    · omega
    · exact h
  have hs64 : t.size ≤ 2 ^ 64 := by have := hi.sizeLe; omega
  -- the facts about the new slot bytes used by `Inv.clear`
  have key : ((delD t i).1 i = 0 ∨ (delD t i).1 i = 127) ∧
      (∀ p, p ≠ i → (delD t i).1 p = t.slots p ∨ (t.slots p = 127 ∧ (delD t i).1 p = 0)) ∧
      (∀ q hh d, filledB (t.slots q) = true → q ≠ i → q = pr t.size hh d → d < t.size →
        1 ≤ hh → hh ≤ t.size → (∀ e, e < d → t.slots (pr t.size hh e) ≠ 0) →
        ∀ e, e < d → (delD t i).1 (pr t.size hh e) ≠ 0) := by
    unfold delD
    by_cases hE : isslotempty t (nextIndex t.size i) = true
    · rw [if_pos hE]
      have hE0 : t.slots (nextIndex t.size i) = 0 := by
        rw [isslotempty_eq] at hE; simpa using hE
      obtain ⟨R, nd, hR, h127, hdb⟩ := clearBackward_spec (sz := t.size) (i := i) t.slots t.size 0 1
        (by omega) (fun s hs1 hs2 => absurd hs2 (by omega))
      have hdb' : clearBackward t.size t.slots t.size i 1 = (clr t.size i t.slots R, nd) := hdb
      rw [hdb']
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rcases clr_spec t.size i t.slots R i with ⟨-, hne⟩ | ⟨h0, -⟩
        · exact absurd rfl (hne 0 (by omega))
        · exact Or.inl h0
      · intro p hpi
        rcases clr_spec t.size i t.slots R p with ⟨h, -⟩ | ⟨h0, s, hs, hps⟩
        · exact Or.inl h
        · have hs0 : s ≠ 0 := fun h => hpi (by rw [hps, h] <;> rfl)
          exact Or.inr ⟨by rw [hps]; exact h127 s (by omega) hs, h0⟩
      · intro q hh d hqf hqi hq hd hh1 hh2 hall e' he' hS0
        have ht0 := hall e' he'
        rcases clr_spec t.size i t.slots R (pr t.size hh e') with ⟨hc, -⟩ | ⟨-, r, hr, hpr⟩
        · rw [hc] at hS0; exact ht0 hS0
        · have hpos := pr_bk hpow hs64 h1 h2 hpr
          rcases Nat.lt_or_ge (e' + r) d with hlt | hge
          · have hnext : pr t.size hh (e' + r + 1) = nextIndex t.size i := by
              rw [pr_succ, hpos r (Nat.le_refl _), Nat.sub_self]
              rfl
            by_cases hd' : e' + r + 1 = d
            · rw [← hd', hnext] at hq
              rw [hq, hE0, filledB_zero] at hqf
              cases hqf
            · have := hall (e' + r + 1) (by omega)
              rw [hnext] at this
              exact this hE0
          · have hq' := hpos (d - e') (by omega)
            rw [show e' + (d - e') = d by omega, ← hq] at hq'
            by_cases hz : r - (d - e') = 0
            · rw [hz] at hq'
              exact hqi hq'
            · have := h127 (r - (d - e')) (by omega) (by omega)
              rw [← hq'] at this
              rw [this, filledB_127] at hqf
              cases hqf
    · rw [if_neg hE]
      dsimp only
      refine ⟨Or.inr (updateAt_same _ _ _), fun p hpi => Or.inl (updateAt_ne _ _ hpi), ?_⟩
      intro q hh d _ _ _ _ _ _ hall e' he' hS0
      by_cases hpi : pr t.size hh e' = i
      · rw [hpi, updateAt_same] at hS0; cases hS0
      · rw [updateAt_ne _ _ hpi] at hS0; exact hall e' he' hS0
  obtain ⟨hA, hB, hC⟩ := key
  have hk : ∀ p, p ≠ i → (delT unsetKey unsetVal t i (delD t i)).keys p = t.keys p :=
    fun p hp => huk t.size t.keys i p hp
  have hv : ∀ p, p ≠ i → (delT unsetKey unsetVal t i (delD t i)).vals p = t.vals p :=
    fun p hp => huv t.size t.vals i p hp
  obtain ⟨hI, htl⟩ := Inv.clear (t' := delT unsetKey unsetVal t i (delD t i)) hl hi h1 h2 he rfl
    hk hv rfl rfl rfl rfl hA hB hC
  rw [deleteAt_eq]
  have hfill : ∀ p, p ≠ i →
      filledB ((delT unsetKey unsetVal t i (delD t i)).slots p) = filledB (t.slots p) := by
    intro p hpi
    show filledB ((delD t i).1 p) = filledB (t.slots p)
    rcases hB p hpi with h | ⟨h127, h0⟩
    · rw [h]
    · rw [h127, h0]; decide
  refine ⟨hI, htl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun p hpi => ⟨hfill p hpi, ?_⟩⟩
  · show filledB ((delD t i).1 i) = false
    rcases hA with h | h <;> rw [h] <;> decide
  · unfold ent
    rw [hfill p hpi, hk p hpi, hv p hpi]

/-! ## `delete!`, `pop!` -/

section Delete
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}
  {unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K)}
  {unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)}

/-- Keys `isequal` to a stored key `e.1` that the query `q` matches are exactly the keys `q`
matches. -/
theorem filter_match_eq {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {q : Q} {k : K} (hm : matchQ q k = true)
    (m : List (K × V)) :
    m.filter (fun b => !eqKey k b.1) = m.filter (fun b => !matchQ q b.1) := by
  apply List.filter_congr
  intro b _
  cases h1 : matchQ q b.1 <;> cases h2 : eqKey k b.1
  · rfl
  · rw [hq.congr q k b.1 hm h2] at h1; cases h1
  · rw [hq.unique q k b.1 hm h1] at h2; cases h2
  · rfl

/-- The slot of a query on a represented table. -/
theorem DictRep.probe (hl : KeyLaws hash eqKey) {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V}
    {m : List (K × V)} (h : DictRep hash eqKey t m) (q : Q) :
    match rfind matchQ m q with
    | some e => ∃ i : Nat, JuliaLean.base.dict.htKeyindex hashQ matchQ t q = .ok (i : Int) ∧
        1 ≤ i ∧ i ≤ t.size ∧ ent t i = some e ∧ matchQ q e.1 = true
    | none => JuliaLean.base.dict.htKeyindex hashQ matchQ t q = .ok (-1) ∧
        ∀ e ∈ tlist t, matchQ q e.1 = false := by
  have hd : Distinct eqKey (tlist t) := tlist_pairwise h.1
  have hr := h.htKeyindex hl hq q
  cases hf : rfind matchQ m q with
  | some e =>
    rw [hf] at hr
    obtain ⟨i, h1, h2, h3, h4⟩ := hr
    exact ⟨i, h1, h2, h3, h4, (rfind_some hf).2⟩
  | none =>
    rw [hf] at hr
    refine ⟨hr, ?_⟩
    rw [← rfind_perm hl hq hd h.2] at hf
    exact rfind_eq_none_iff.1 hf

theorem DictRep.deleteAt (hl : KeyLaws hash eqKey) (huk : UnsetLaw unsetKey)
    (huv : UnsetLaw unsetVal) {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) {q : Q} {i : Nat} {e : K × V} (h1 : 1 ≤ i) (h2 : i ≤ t.size)
    (he : ent t i = some e) (hm : matchQ q e.1 = true) :
    DictRep hash eqKey (deleteAt unsetKey unsetVal t i) (rdel matchQ m q) ∧
      (deleteAt unsetKey unsetVal t i).count = t.count - 1 := by
  obtain ⟨hI, htl, hc, -⟩ := deleteAt_spec hl huk huv h.1 h1 h2 he
  refine ⟨⟨hI, ?_⟩, hc⟩
  rw [htl, filter_match_eq hq hm]
  exact h.2.filter _

/-- `delete!(h, key)` removes every pair whose key is `isequal` to `key`. -/
theorem DictRep.deleteKey (hl : KeyLaws hash eqKey) (huk : UnsetLaw unsetKey)
    (huv : UnsetLaw unsetVal) {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (q : Q) :
    ∃ t', JuliaLean.base.dict.deleteKey hashQ matchQ unsetKey unsetVal t q = .ok t' ∧
      DictRep hash eqKey t' (rdel matchQ m q) := by
  have hp := h.probe hl hq q
  unfold JuliaLean.base.dict.deleteKey
  cases hf : rfind matchQ m q with
  | some e =>
    rw [hf] at hp
    obtain ⟨i, hidx, h1, h2, he, hm⟩ := hp
    rw [hidx, except_ok_bind, if_pos (by omega), show ((i : Nat) : Int).toNat = i by omega]
    exact ⟨_, rfl, (h.deleteAt hl huk huv hq h1 h2 he hm).1⟩
  | none =>
    rw [hf] at hp
    rw [hp.1, except_ok_bind, if_neg (by omega)]
    refine ⟨t, rfl, ?_⟩
    rw [rdel_absent (fun e he => (rfind_eq_none_iff.1 hf) e he)]
    exact h

/-- `pop!(h, key)` returns the stored value and removes the key, or throws `KeyError`. -/
theorem DictRep.popKey (hl : KeyLaws hash eqKey) (huk : UnsetLaw unsetKey)
    (huv : UnsetLaw unsetVal) {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (q : Q) :
    match rfind matchQ m q with
    | some e => ∃ t', JuliaLean.base.dict.popKey hashQ matchQ unsetKey unsetVal t q = .ok (e.2, t') ∧
        DictRep hash eqKey t' (rdel matchQ m q)
    | none => JuliaLean.base.dict.popKey hashQ matchQ unsetKey unsetVal t q = .error .keyError := by
  have hp := h.probe hl hq q
  unfold JuliaLean.base.dict.popKey
  cases hf : rfind matchQ m q with
  | some e =>
    rw [hf] at hp
    obtain ⟨i, hidx, h1, h2, he, hm⟩ := hp
    rw [hidx, except_ok_bind, if_pos (by omega), show ((i : Nat) : Int).toNat = i by omega]
    obtain ⟨k0, v0⟩ := e
    unfold popAt
    rw [valAt_of_ent he, except_ok_bind]
    exact ⟨_, rfl, (h.deleteAt hl huk huv hq h1 h2 he hm).1⟩
  | none =>
    rw [hf] at hp
    rw [hp.1, except_ok_bind, if_neg (by omega)]

/-- `pop!(h, key, default)` returns the stored value and removes the key, or returns `default`
and leaves the table alone. -/
theorem DictRep.popDefault (hl : KeyLaws hash eqKey) (huk : UnsetLaw unsetKey)
    (huv : UnsetLaw unsetVal) {Q : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (q : Q) (d : V) :
    match rfind matchQ m q with
    | some e => ∃ t', JuliaLean.base.dict.popDefault hashQ matchQ unsetKey unsetVal t q d =
          .ok (e.2, t') ∧ DictRep hash eqKey t' (rdel matchQ m q)
    | none => JuliaLean.base.dict.popDefault hashQ matchQ unsetKey unsetVal t q d = .ok (d, t) := by
  have hp := h.probe hl hq q
  unfold JuliaLean.base.dict.popDefault
  cases hf : rfind matchQ m q with
  | some e =>
    rw [hf] at hp
    obtain ⟨i, hidx, h1, h2, he, hm⟩ := hp
    rw [hidx, except_ok_bind, if_pos (by omega), show ((i : Nat) : Int).toNat = i by omega]
    obtain ⟨k0, v0⟩ := e
    unfold popAt
    rw [valAt_of_ent he, except_ok_bind]
    exact ⟨_, rfl, (h.deleteAt hl huk huv hq h1 h2 he hm).1⟩
  | none =>
    rw [hf] at hp
    rw [hp.1, except_ok_bind, if_neg (by omega)]

end Delete

/-! ## `skip_deleted` and `pop!(h)` -/

theorem skipLoop_succ (t : DictState K V) (n i : Nat) :
    skipDeleted.loop t (n + 1) i = if isslotfilled t i then i else skipDeleted.loop t n (i + 1) :=
  rfl

theorem skipLoop_spec (t : DictState K V) : ∀ n i, 1 ≤ i →
    (skipDeleted.loop t n i = 0 ∧ ∀ j, i ≤ j → j < i + n → filledB (t.slots j) = false) ∨
    (i ≤ skipDeleted.loop t n i ∧ skipDeleted.loop t n i < i + n ∧
      filledB (t.slots (skipDeleted.loop t n i)) = true ∧
      ∀ j, i ≤ j → j < skipDeleted.loop t n i → filledB (t.slots j) = false)
  | 0, i, _ => Or.inl ⟨rfl, fun j h1 h2 => absurd h2 (by omega)⟩
  | n + 1, i, hi => by
    rw [skipLoop_succ, isslotfilled_eq]
    by_cases hf : filledB (t.slots i) = true
    · rw [if_pos hf]
      exact Or.inr ⟨Nat.le_refl _, by omega, hf, fun j h1 h2 => absurd h2 (by omega)⟩
    · rw [if_neg hf]
      have hf' : filledB (t.slots i) = false := by simpa using hf
      rcases skipLoop_spec t n (i + 1) (by omega) with ⟨h0, hall⟩ | ⟨h1, h2, h3, h4⟩
      · refine Or.inl ⟨h0, fun j hj1 hj2 => ?_⟩
        by_cases hji : j = i
        · rw [hji]; exact hf'
        · exact hall j (by omega) (by omega)
      · refine Or.inr ⟨by omega, by omega, h3, fun j hj1 hj2 => ?_⟩
        by_cases hji : j = i
        · rw [hji]; exact hf'
        · exact h4 j (by omega) hj2

/-- `skip_deleted(h, i)` for `i ≥ 1` returns the first filled slot at or after `i`, or `0` when
there is none. -/
theorem skipDeleted_spec (t : DictState K V) {i : Nat} (hi : 1 ≤ i) :
    (skipDeleted t i = 0 ∧ ∀ j, i ≤ j → j ≤ t.size → filledB (t.slots j) = false) ∨
    (i ≤ skipDeleted t i ∧ skipDeleted t i ≤ t.size ∧ filledB (t.slots (skipDeleted t i)) = true ∧
      ∀ j, i ≤ j → j < skipDeleted t i → filledB (t.slots j) = false) := by
  unfold skipDeleted
  by_cases hgt : i > t.size
  · rw [if_pos hgt]
    exact Or.inl ⟨rfl, fun j h1 h2 => absurd h2 (by omega)⟩
  · rw [if_neg hgt]
    rcases skipLoop_spec t (t.size - i + 1) i hi with ⟨h0, hall⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h0, fun j h1 h2 => hall j h1 (by omega)⟩
    · exact Or.inr ⟨h1, by omega, h3, h4⟩

/-- The pop of `pop!(h)` after its emptiness check (`base/dict.jl:1052-1056`). -/
def popTail (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) :
    Nat × DictState K V → DictResult ((K × V) × DictState K V)
  | (index, h) => do
    let h := DictState.mk h.size h.slots h.keys h.vals h.ndel h.count h.age h.idxfloor
      h.maxprobe (index + 1)
    let key ← keyAt h index
    let (value, h) ← popAt unsetKey unsetVal h index
    .ok ((key, value), h)

theorem popAny_eq (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) (t : DictState K V) :
    popAny unsetKey unsetVal t =
      if isempty t then .error .argumentError
      else popTail unsetKey unsetVal
        (if skipDeleted t t.popcursor == 0 then skipDeletedFloor t
          else (skipDeleted t t.popcursor, t)) := by
  unfold popAny
  by_cases he : isempty t = true
  · rw [if_pos he, if_pos he]
  · rw [if_neg he, if_neg he]
    dsimp only
    generalize (if (skipDeleted t t.popcursor == 0) = true then skipDeletedFloor t
      else (skipDeleted t t.popcursor, t)) = sel
    obtain ⟨index, h⟩ := sel
    unfold popTail
    dsimp only

section PopAny
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}
  {unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K)}
  {unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)}

/-- `pop!(h)` throws `ArgumentError` on an empty table and otherwise removes and returns one
stored pair. -/
theorem DictRep.popAny (hl : KeyLaws hash eqKey) (huk : UnsetLaw unsetKey)
    (huv : UnsetLaw unsetVal) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) :
    match m with
    | [] => JuliaLean.base.dict.popAny unsetKey unsetVal t = .error .argumentError
    | _ :: _ => ∃ e t', JuliaLean.base.dict.popAny unsetKey unsetVal t = .ok (e, t') ∧ e ∈ m ∧
        DictRep hash eqKey t' (rdel eqKey m e.1) := by
  have hcount : t.count = m.length := by rw [h.1.count, h.2.length_eq]
  rw [popAny_eq]
  cases m with
  | nil =>
    rw [if_pos (by simp [isempty, hcount])]
  | cons a rest =>
    show ∃ e t', (if isempty t = true then _ else _) = _ ∧ _
    rw [if_neg (by simp [isempty, hcount])]
    -- the selected slot is filled
    have hsel : ∃ index t1, (if skipDeleted t t.popcursor == 0 then skipDeletedFloor t
          else (skipDeleted t t.popcursor, t)) = (index, t1) ∧ 1 ≤ index ∧ index ≤ t.size ∧
        filledB (t.slots index) = true ∧ Inv hash eqKey t1 ∧ t1.size = t.size ∧
        t1.slots = t.slots ∧ t1.keys = t.keys ∧ t1.vals = t.vals ∧ t1.count = t.count := by
      rcases skipDeleted_spec t h.1.popcursor with ⟨h0, -⟩ | ⟨h1, h2, h3, -⟩
      · rw [if_pos (by simp [h0])]
        unfold skipDeletedFloor
        dsimp only
        have ham : a ∈ tlist t := h.2.mem_iff.2 List.mem_cons_self
        obtain ⟨p, hp1, hp2, hpe⟩ := mem_tlist.1 ham
        have hpf := (ent_some hpe).1
        rcases skipDeleted_spec t h.1.idxfloor with ⟨-, hall⟩ | ⟨h1, h2, h3, h4⟩
        · exact absurd (hall p (h.1.floorLe p hp1 hp2 hpf) hp2) (by rw [hpf]; decide)
        · have hne : (skipDeleted t t.idxfloor != 0) = true := by
            have := h.1.idxfloor
            have h0' : skipDeleted t t.idxfloor ≠ 0 := by omega
            simpa using h0'
          rw [if_pos hne]
          refine ⟨_, _, rfl, by have := h.1.idxfloor; omega, h2, h3, ?_, rfl, rfl, rfl, rfl, rfl⟩
          have hi := h.1
          refine ⟨hi.size, hi.sizeLe, fun j hj1 hj2 => SlotOK.transfer (hi.slot j hj1 hj2) rfl rfl rfl
            (fun k hc => hc), hi.distinct, hi.count, hi.maxprobe,
            by show 1 ≤ skipDeleted t t.idxfloor; have := hi.idxfloor; omega,
            fun j hj1 hj2 hjf => ?_, hi.popcursor⟩
          show skipDeleted t t.idxfloor ≤ j
          apply Classical.byContradiction
          intro hlt
          have := h4 j (hi.floorLe j hj1 hj2 hjf) (by omega)
          rw [hjf] at this
          cases this
      · have hne : (skipDeleted t t.popcursor == 0) = false := by
          have := h.1.popcursor
          have h0' : skipDeleted t t.popcursor ≠ 0 := by omega
          simpa using h0'
        rw [if_neg (by simp [hne])]
        exact ⟨_, _, rfl, by have := h.1.popcursor; omega, h2, h3, h.1, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨index, t1, hsel, hx1, hx2, hxf, hi1, hs1, hsl1, hk1, hv1, hc1⟩ := hsel
    rw [hsel]
    unfold popTail
    dsimp only
    let t2 : DictState K V := DictState.mk t1.size t1.slots t1.keys t1.vals t1.ndel t1.count t1.age
      t1.idxfloor t1.maxprobe (index + 1)
    have hi2 : Inv hash eqKey t2 :=
      ⟨hi1.size, hi1.sizeLe, fun j hj1 hj2 => SlotOK.transfer (hi1.slot j hj1 hj2) rfl rfl rfl
        (fun k hc => hc), hi1.distinct, hi1.count, hi1.maxprobe, hi1.idxfloor, hi1.floorLe,
        by show 1 ≤ index + 1; omega⟩
    have htl2 : tlist t2 = tlist t := by
      apply tlist_congr hs1
      intro j _ _
      show ent t2 j = ent t j
      unfold ent
      show (if filledB (t1.slots j) then _ else _) = _
      rw [hsl1, hk1, hv1]
    have hx2' : index ≤ t2.size := by show index ≤ t1.size; omega
    have hxf' : filledB (t2.slots index) = true := by show filledB (t1.slots index) = true; rw [hsl1]; exact hxf
    obtain ⟨k, v, hk, hv, he, -⟩ := hi2.filled hx1 hx2' hxf'
    show ∃ e t', (keyAt t2 index >>= _) = _ ∧ _
    rw [keyAt_of_ent he, except_ok_bind]
    unfold popAt
    rw [valAt_of_ent he, except_ok_bind]
    have hm2 : DictRep hash eqKey t2 (a :: rest) := ⟨hi2, by rw [htl2]; exact h.2⟩
    obtain ⟨hr, -⟩ := hm2.deleteAt hl huk huv hl.query hx1 hx2' he (q := k) (hl.refl k)
    refine ⟨(k, v), _, rfl, ?_, hr⟩
    exact h.2.mem_iff.1 (by rw [← htl2]; exact mem_tlist.2 ⟨index, hx1, hx2', he⟩)

end PopAny


/-! ## Lookups -/

section Lookups
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}

theorem rlookup_of_rfind {Q : Type} {matchQ : Q → K → Bool} {m : List (K × V)} {q : Q} :
    rlookup matchQ m q = (rfind matchQ m q).map (·.2) := rfl

/-- `getindex`, both `get`s, `haskey`, `in(key, keys(d))` and `getkey` on a represented table. -/
theorem DictRep.lookups (hl : KeyLaws hash eqKey) {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V}
    {m : List (K × V)} (h : DictRep hash eqKey t m) (q : Q) (default : V) (defaultKey : K)
    (defaultF : Unit → DictResult V) :
    getindex hashQ matchQ t q =
        (match rlookup matchQ m q with | some v => .ok v | none => .error .keyError) ∧
      JuliaLean.base.dict.get hashQ matchQ t q default = .ok ((rlookup matchQ m q).getD default) ∧
      getF hashQ matchQ t q defaultF =
        (match rlookup matchQ m q with | some v => .ok v | none => defaultF ()) ∧
      haskey hashQ matchQ t q = .ok (rlookup matchQ m q).isSome ∧
      inKeySet hashQ matchQ ⟨t⟩ q = .ok (rlookup matchQ m q).isSome ∧
      getkey hashQ matchQ t q defaultKey = .ok (((rfind matchQ m q).map (·.1)).getD defaultKey) := by
  have hp := h.probe hl hq q
  rw [rlookup_of_rfind]
  unfold getindex JuliaLean.base.dict.get getF haskey inKeySet getkey
  cases hf : rfind matchQ m q with
  | some e =>
    rw [hf] at hp
    obtain ⟨i, hidx, h1, h2, he, -⟩ := hp
    obtain ⟨k, v⟩ := e
    have hti : ((i : Nat) : Int).toNat = i := by omega
    simp only [hidx, except_ok_bind, Option.map_some, Option.getD_some, Option.isSome_some]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hti,
      valAt_of_ent he, keyAt_of_ent he]
    refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩ <;> simp
  | none =>
    rw [hf] at hp
    simp only [hp.1, except_ok_bind, Option.map_none, Option.getD_none, Option.isSome_none]
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩ <;> simp

end Lookups

/-! ## `empty!` -/

theorem emptyBang_fields (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) (t : DictState K V) :
    (emptyBang fillSlots unsetKey unsetVal t).size = t.size ∧
      (emptyBang fillSlots unsetKey unsetVal t).slots = fillSlots t.size 0 t.slots ∧
      (emptyBang fillSlots unsetKey unsetVal t).ndel = 0 ∧
      (emptyBang fillSlots unsetKey unsetVal t).count = 0 ∧
      (emptyBang fillSlots unsetKey unsetVal t).age = bumpAge t.age ∧
      (emptyBang fillSlots unsetKey unsetVal t).idxfloor = max 1 t.size ∧
      (emptyBang fillSlots unsetKey unsetVal t).maxprobe = 0 ∧
      (emptyBang fillSlots unsetKey unsetVal t).popcursor = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `empty!(h)` leaves a well-formed table with no pairs. -/
theorem emptyBang_spec {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat} (hfill : FillLaw fillSlots)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) {t : DictState K V}
    (hi : Inv hash eqKey t) :
    DictRep hash eqKey (emptyBang fillSlots unsetKey unsetVal t) [] ∧
      (emptyBang fillSlots unsetKey unsetVal t).age = bumpAge t.age := by
  obtain ⟨hs, hsl, -, hc, ha, hf, hm, hp⟩ := emptyBang_fields fillSlots unsetKey unsetVal t
  have h0 : ∀ i, 1 ≤ i → i ≤ t.size → (emptyBang fillSlots unsetKey unsetVal t).slots i = 0 := by
    intro i h1 h2
    rw [hsl]
    exact hfill t.size 0 t.slots i h1 h2
  have hnil : tlist (emptyBang fillSlots unsetKey unsetVal t) = [] := by
    unfold tlist
    rw [hs]
    exact filterMap_ent_nil t.size 1 (fun p h1 h2 => by rw [h0 p h1 (by omega)]; exact filledB_zero)
  refine ⟨⟨⟨by rw [hs]; exact hi.size, by rw [hs]; exact hi.sizeLe, fun i h1 h2 => ?_, ?_, ?_, ?_,
    by rw [hf]; omega, fun i h1 h2 hfi => ?_, by rw [hp]; exact Nat.le_refl _⟩, by rw [hnil]⟩, ha⟩
  · rw [hs] at h2
    exact Or.inl (h0 i h1 h2)
  · intro i j a b h1 h2 _ _ _ ha _
    rw [hs] at h2
    rw [ent_of_not_filled (by rw [h0 i h1 h2]; exact filledB_zero)] at ha
    cases ha
  · rw [hc, hnil]; rfl
  · rw [hm, hs]
    rcases hi.size with h | h
    · exact Or.inl h
    · exact Or.inr (by have := h.ge; omega)
  · rw [hs] at h2
    rw [h0 i h1 h2, filledB_zero] at hfi
    cases hfi

/-! ## `filter!` -/

section Filter
variable {hash : K → JInt .u64} {eqKey : K → K → Bool}
  {unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K)}
  {unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)}

/-- The scan of `filter!` from slot `i`: slots before `i` hold the kept pairs of `t`, slots from
`i` on are those of `t`. -/
theorem filterLoop_spec (hl : KeyLaws hash eqKey) (huk : UnsetLaw unsetKey)
    (huv : UnsetLaw unsetVal) (pred : K × V → Bool) {t : DictState K V} :
    ∀ n i (h : DictState K V), Inv hash eqKey h → h.size = t.size → 1 ≤ i →
      i + n = t.size + 1 →
      (∀ p, 1 ≤ p → p < i → ent h p = (ent t p).filter pred) →
      (∀ p, i ≤ p → p ≤ t.size → ent h p = ent t p) →
      ∃ h', filterLoop unsetKey unsetVal pred h n i = .ok h' ∧ Inv hash eqKey h' ∧
        h'.size = t.size ∧ ∀ p, 1 ≤ p → p ≤ t.size → ent h' p = (ent t p).filter pred
  | 0, i, h, hi, hs, _, hn, hlt, _ =>
    ⟨h, rfl, hi, hs, fun p h1 h2 => hlt p h1 (by omega)⟩
  | n + 1, i, h, hi, hs, h1, hn, hlt, hge => by
    have hi2 : i ≤ h.size := by omega
    have hstep : filterLoop unsetKey unsetVal pred h (n + 1) i =
        if isslotfilled h i then
          (keyAt h i >>= fun key => valAt h i >>= fun value =>
            filterLoop unsetKey unsetVal pred
              (if pred (key, value) then h else deleteAt unsetKey unsetVal h i) n (i + 1))
        else filterLoop unsetKey unsetVal pred h n (i + 1) := rfl
    rw [hstep, isslotfilled_eq]
    by_cases hf : filledB (h.slots i) = true
    · rw [if_pos hf]
      obtain ⟨k, v, -, -, he, -, -⟩ := hi.filled h1 hi2 hf
      rw [keyAt_of_ent he, except_ok_bind, valAt_of_ent he, except_ok_bind]
      have het : ent t i = some (k, v) := by rw [← hge i (Nat.le_refl _) (by omega)]; exact he
      by_cases hp : pred (k, v) = true
      · rw [if_pos hp]
        refine filterLoop_spec hl huk huv pred n (i + 1) h hi hs (by omega) (by omega)
          (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => hge p (by omega) hp2)
        by_cases hpi : p = i
        · rw [hpi, he, het]; simp [Option.filter, hp]
        · exact hlt p hp1 (by omega)
      · rw [if_neg hp]
        obtain ⟨hI, -, -, -, hsz, -, -, -, hfi, hrest⟩ := deleteAt_spec hl huk huv hi h1 hi2 he
        refine filterLoop_spec hl huk huv pred n (i + 1) _ hI (by rw [hsz, hs]) (by omega)
          (by omega) (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)
        · by_cases hpi : p = i
          · rw [hpi, ent_of_not_filled hfi, het]; simp [Option.filter, hp]
          · rw [(hrest p hpi).2]; exact hlt p hp1 (by omega)
        · rw [(hrest p (by omega)).2]; exact hge p (by omega) hp2
    · rw [if_neg hf]
      have hf' : filledB (h.slots i) = false := by simpa using hf
      refine filterLoop_spec hl huk huv pred n (i + 1) h hi hs (by omega) (by omega)
        (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => hge p (by omega) hp2)
      by_cases hpi : p = i
      · rw [hpi, ent_of_not_filled hf', ← hge i (Nat.le_refl _) (by omega),
          ent_of_not_filled hf']; rfl
      · exact hlt p hp1 (by omega)

/-- `filter!(pred, h)` keeps exactly the pairs `pred` accepts. -/
theorem DictRep.filterBang (hl : KeyLaws hash eqKey) (huk : UnsetLaw unsetKey)
    (huv : UnsetLaw unsetVal) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (pred : K × V → Bool) :
    ∃ t', JuliaLean.base.dict.filterBang unsetKey unsetVal pred t = .ok t' ∧
      DictRep hash eqKey t' (m.filter pred) := by
  unfold JuliaLean.base.dict.filterBang
  by_cases hc : (t.count == 0) = true
  · rw [if_pos hc]
    have hc0 : t.count = 0 := by simpa using hc
    have hnil : tlist t = [] := List.length_eq_zero_iff.1 (by rw [← h.1.count]; exact hc0)
    have hm : m = [] := List.Perm.eq_nil (h.2.symm.trans (by rw [hnil]))
    refine ⟨t, rfl, h.1, ?_⟩
    rw [hm, hnil]
    rfl
  · rw [if_neg hc]
    obtain ⟨t', h', hi', hs', hent⟩ := filterLoop_spec hl huk huv pred t.size 1 t h.1 rfl
      (Nat.le_refl _) (by omega) (fun p h1 h2 => absurd h2 (by omega)) (fun p _ _ => rfl)
    refine ⟨t', h', hi', ?_⟩
    have htl : tlist t' = (tlist t).filter pred := by
      unfold tlist
      rw [hs', List.filter_filterMap]
      apply filterMap_congr_mem
      intro x hx
      rw [List.mem_range'_1] at hx
      exact hent x hx.1 (by omega)
    rw [htl]
    exact h.2.filter pred

end Filter

/-! ## Iteration -/

/-- Repeated `iterate(t, i)` calls, as in `for pair in t`, with `fuel` calls allowed. -/
def iterCollect (t : DictState K V) : Nat → Nat → DictResult (List (K × V))
  | 0, _ => .ok []
  | fuel + 1, i => do
    match ← iterateNext t i with
    | none => .ok []
    | some (pair, next) => do
      let rest ← iterCollect t fuel next
      .ok (pair :: rest)

theorem filterMap_ent_range_skip {t : DictState K V} :
    ∀ n i, (∀ p, i ≤ p → p < i + n → filledB (t.slots p) = false) →
      (List.range' i n).filterMap (ent t) = []
  | 0, _, _ => rfl
  | n + 1, i, h => by
    rw [List.range'_succ, List.filterMap_cons_none (ent_of_not_filled (h i (Nat.le_refl _) (by omega)))]
    exact filterMap_ent_range_skip n (i + 1) (fun p h1 h2 => h p (by omega) (by omega))

theorem range'_split (i r n : Nat) (h1 : i ≤ r) (h2 : r < i + n) :
    List.range' i n = List.range' i (r - i) ++ r :: List.range' (r + 1) (i + n - (r + 1)) := by
  have e1 : List.range' i n =
      List.range' i (r - i) ++ List.range' (i + (r - i)) (i + n - (r + 1) + 1) := by
    rw [List.range'_append_1]; congr 1; omega
  rw [e1, show i + (r - i) = r by omega, List.range'_succ]

/-- Iterating from slot `i ≥ 1` yields the stored pairs from slot `i` on, in slot order. -/
theorem iterCollect_spec {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    (hi : Inv hash eqKey t) (hbig : t.size < 2 ^ 63 - 1) :
    ∀ fuel i, 1 ≤ i → t.size + 1 - i < fuel →
      iterCollect t fuel i = .ok ((List.range' i (t.size + 1 - i)).filterMap (ent t))
  | 0, _, _, h => absurd h (by omega)
  | fuel + 1, i, h1, hf => by
    have hstep : iterCollect t (fuel + 1) i = (iterateNext t i >>= fun r =>
        match r with
        | none => .ok []
        | some (pair, next) => iterCollect t fuel next >>= fun rest => .ok (pair :: rest)) := rfl
    rw [hstep]
    unfold iterateNext
    rcases skipDeleted_spec t h1 with ⟨h0, hall⟩ | ⟨hr1, hr2, hr3, hr4⟩
    · rw [h0]
      rw [filterMap_ent_range_skip _ _ (fun p hp1 hp2 => hall p hp1 (by omega))]
      rfl
    · obtain ⟨k, v, -, -, he, -, -⟩ := hi.filled (by omega) hr2 hr3
      have hit : iterateDict t (skipDeleted t i) =
          .ok (some ((k, v), skipDeleted t i + 1)) := by
        unfold iterateDict
        rw [if_neg (by simp; omega), keyAt_of_ent he, except_ok_bind, valAt_of_ent he,
          except_ok_bind, if_neg (by simp; omega)]
      rw [hit, except_ok_bind]
      dsimp only
      rw [iterCollect_spec hi hbig fuel (skipDeleted t i + 1) (by omega) (by omega), except_ok_bind]
      rw [range'_split i (skipDeleted t i) (t.size + 1 - i) hr1 (by omega), List.filterMap_append,
        filterMap_ent_range_skip _ _ (fun p hp1 hp2 => hr4 p hp1 (by omega)), List.nil_append,
        List.filterMap_cons_some he,
        show i + (t.size + 1 - i) - (skipDeleted t i + 1) = t.size + 1 - (skipDeleted t i + 1) by omega]

/-- The stored pairs start at `idxfloor`. -/
theorem tlist_from_floor {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    (hi : Inv hash eqKey t) :
    tlist t = (List.range' t.idxfloor (t.size + 1 - t.idxfloor)).filterMap (ent t) := by
  unfold tlist
  have hfl := hi.idxfloor
  have hlow : ∀ p, 1 ≤ p → p < t.idxfloor → p ≤ t.size → filledB (t.slots p) = false := by
    intro p h1 h2 h3
    cases hf : filledB (t.slots p)
    · rfl
    · have := hi.floorLe p h1 h3 hf; omega
  by_cases hle : t.idxfloor ≤ t.size + 1
  · have hsplit : List.range' 1 t.size = List.range' 1 (t.idxfloor - 1) ++
        List.range' (1 + (t.idxfloor - 1)) (t.size + 1 - t.idxfloor) := by
      rw [List.range'_append_1]; congr 1; omega
    rw [hsplit, show 1 + (t.idxfloor - 1) = t.idxfloor by omega, List.filterMap_append,
      filterMap_ent_range_skip _ _ (fun p h1 h2 => hlow p h1 (by omega) (by omega)),
      List.nil_append]
  · rw [show t.size + 1 - t.idxfloor = 0 by omega]
    exact filterMap_ent_range_skip _ _ (fun p h1 h2 => hlow p h1 (by omega) (by omega))

/-- `for pair in d` (`iterate(d)` then `iterate(d, i)`) visits every stored pair once, in slot
order. -/
theorem DictRep.iterate {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    {m : List (K × V)} (h : DictRep hash eqKey t m) (hbig : t.size < 2 ^ 63 - 1) :
    (iterateFirst t >>= fun r =>
        match r with
        | none => .ok []
        | some (pair, next) => iterCollect t (t.size + 1) next >>= fun rest => .ok (pair :: rest)) =
      .ok (tlist t) ∧ List.Perm (tlist t) m := by
  have hfl := h.1.idxfloor
  have hc := iterCollect_spec h.1 hbig (t.size + 2) t.idxfloor hfl (by omega)
  have hstep : iterCollect t (t.size + 2) t.idxfloor = (iterateNext t t.idxfloor >>= fun r =>
      match r with
      | none => .ok []
      | some (pair, next) => iterCollect t (t.size + 1) next >>= fun rest => .ok (pair :: rest)) :=
    rfl
  refine ⟨?_, h.2⟩
  show (iterateNext t t.idxfloor >>= _) = _
  rw [← hstep, hc, ← tlist_from_floor h.1]


/-! ## `sizehint!` -/

theorem wrap_i64_val {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) :
    (JInt.wrap .i64 x).val = x :=
  wrapInt_of_inRange .i64 x (by constructor <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega)

theorem i64_val_range (a : JInt .i64) : -2 ^ 63 ≤ a.val ∧ a.val < 2 ^ 63 := by
  have h := a.property
  have h1 : IntTy.min .i64 = -2 ^ 63 := by decide
  have h2 : IntTy.max .i64 = 2 ^ 63 - 1 := by decide
  omega

/-- The number of pairwise non-`isequal` keys is at most `max_values(K)`. -/
theorem count_le_maxValues {hash : K → JInt .u64} {eqKey : K → K → Bool} {maxValues : Nat}
    (hmv : MaxValuesLaw eqKey maxValues) {t : DictState K V} (hi : Inv hash eqKey t)
    (hc : t.count < 2 ^ 54) : t.count ≤ maxValues := by
  rcases hmv with h | h
  · have : (2 : Nat) ^ 54 ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  · have hp := tlist_pairwise hi
    have := h ((tlist t).map Prod.fst) (List.pairwise_map.2 hp)
    rw [List.length_map, ← hi.count] at this
    exact this

/-- `sizehint!(d, n; shrink)` with a hint that does not overflow keeps every pair. -/
theorem sizehint_spec {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) {maxValues : Nat} (hmv : MaxValuesLaw eqKey maxValues)
    {cld : JInt .i64 → JInt .i64} (hcld : CldLaw cld) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (hc : t.count < 2 ^ 54) (n : JInt .i64) (hn : n.val ≤ 2 ^ 61)
    (shrink : Bool) :
    ∃ t', sizehint hash tablesz maxValues cld t n shrink = .ok t' ∧ DictRep hash eqKey t' m ∧
      t'.count = t.count := by
  have hmax := count_le_maxValues hmv h.1 hc
  have hnr := i64_val_range n
  -- `min(max(newsz, length(d)), max_values(K))`
  have hx0 : (clampSizeHint t.count maxValues n).val = min (max n.val (t.count : Int)) (maxValues : Int) := by
    unfold clampSizeHint
    apply wrap_i64_val <;> omega
  -- `3 * newsz` does not wrap
  have h3 : (JInt.lit .i64 (3 * (clampSizeHint t.count maxValues n).val)).val =
      3 * (clampSizeHint t.count maxValues n).val := by
    unfold JInt.lit
    apply wrap_i64_val <;> omega
  have hy := hcld (JInt.lit .i64 (3 * (clampSizeHint t.count maxValues n).val))
  generalize hY : cld (JInt.lit .i64 (3 * (clampSizeHint t.count maxValues n).val)) = Y at hy
  rw [h3, hx0] at hy
  have hYle : Y.val.toNat ≤ 2 ^ 62 := by omega
  have hN : tablesz Y.val.toNat = tableszSpec Y.val.toNat := htz _ hYle
  have hN62 := tableszSpec_le_pow hYle
  have hNge := tableszSpec_ge Y.val.toNat
  have hN16 := (tableszSpec_pow Y.val.toNat).ge
  have hgt : t.count < tableszSpec (tableszSpec Y.val.toNat) := by
    rw [tableszSpec_of_pow (tableszSpec_pow _)]
    omega
  unfold sizehint
  dsimp only
  rw [hY, hN]
  split
  · exact ⟨t, rfl, h, rfl⟩
  · obtain ⟨t', h', hi', hp', -, hc', -⟩ := rehash_spec htz h.1 _ hN62 hgt
    exact ⟨t', h', ⟨hi', hp'.trans h.2⟩, hc'⟩

/-! ## Constructors -/

/-- One `d[k] = v` of a constructor loop on the reference map, with the key and value
conversions of `setindex!` (`base/dict.jl:347-357,359-360`). -/
def refStep {Q W : Type} (eqKey : K → K → Bool) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (m : List (K × V)) (p : Q × W) : DictResult (List (K × V)) := do
  let k ← convKey keyConv p.1
  let v ← convertValue valueConv p.2
  .ok (rset eqKey m k v)

theorem rset_length_le {eqKey : K → K → Bool} (m : List (K × V)) (k : K) (v : V) :
    (rset eqKey m k v).length ≤ m.length + 1 := by
  unfold rset rdel
  rw [List.length_cons]
  have := List.length_filter_le (fun e : K × V => !eqKey k e.1) m
  omega

section Ctor
variable {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat}

/-- `h[k] = v` for converted pairs, as one step of the reference fold. -/
theorem DictRep.setConv (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (hc : t.count < 2 ^ 54) (p : Q × W) :
    match refStep eqKey keyConv valueConv m p with
    | .ok m' => ∃ t', setindexConv hash eqKey tablesz keyConv valueConv t p.2 p.1 = .ok t' ∧
        DictRep hash eqKey t' m'
    | .error e => setindexConv hash eqKey tablesz keyConv valueConv t p.2 p.1 = .error e := by
  unfold refStep
  rw [setindexConv_eq]
  cases hk : convKey keyConv p.1 with
  | error e => rfl
  | ok k =>
    show (match (convertValue valueConv p.2 >>= fun v => Except.ok (rset eqKey m k v)) with
      | .ok m' => _ | .error e => _)
    rw [except_ok_bind, setindexTyped_eq]
    cases hv : convertValue valueConv p.2 with
    | error e => rfl
    | ok v =>
      rw [except_ok_bind]
      exact h.store hl htz hc k v

/-- The insertion loop of the constructors (`for (k,v) in kv; h[k] = v; end`). -/
theorem insertLoop_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (loop : List (Q × W) → DictState K V → DictResult (DictState K V))
    (hnil : ∀ t, loop [] t = .ok t)
    (hcons : ∀ p rest t, loop (p :: rest) t =
      (setindexConv hash eqKey tablesz keyConv valueConv t p.2 p.1 >>= fun t => loop rest t)) :
    ∀ (pairs : List (Q × W)) (t : DictState K V) (m : List (K × V)), DictRep hash eqKey t m →
      t.count + pairs.length < 2 ^ 54 →
      match pairs.foldlM (refStep eqKey keyConv valueConv) m with
      | .ok m' => ∃ t', loop pairs t = .ok t' ∧ DictRep hash eqKey t' m'
      | .error e => loop pairs t = .error e
  | [], t, m, h, _ => by
    show ∃ t', loop [] t = .ok t' ∧ DictRep hash eqKey t' m
    exact ⟨t, hnil t, h⟩
  | p :: rest, t, m, h, hc => by
    rw [List.foldlM_cons, hcons]
    have hs := h.setConv hl htz keyConv valueConv (by simp at hc; omega) p
    cases hr : refStep eqKey keyConv valueConv m p with
    | error e =>
      rw [hr] at hs
      rw [hs]
      rfl
    | ok m1 =>
      rw [hr] at hs
      obtain ⟨t1, h1, hrep1⟩ := hs
      rw [h1, except_ok_bind, except_ok_bind]
      have hc1 : t1.count ≤ t.count + 1 := by
        rw [hrep1.1.count, hrep1.2.length_eq, h.1.count, h.2.length_eq]
        revert hr
        unfold refStep
        intro hr
        cases hk : convKey keyConv p.1 <;> rw [hk] at hr
        · cases hr
        · cases hv : convertValue valueConv p.2 <;> rw [hv] at hr
          · cases hr
          · cases hr
            exact rset_length_le _ _ _
      exact insertLoop_spec hl htz keyConv valueConv loop hnil hcons rest t1 m1 hrep1
        (by simp at hc; omega)

end Ctor

/-- `Dict{K,V}()` is a well-formed empty table. -/
theorem dictEmpty_rep (hash : K → JInt .u64) (eqKey : K → K → Bool) :
    DictRep hash eqKey (dictEmpty K V) [] := by
  have hnil : tlist (dictEmpty K V) = [] := rfl
  refine ⟨⟨Or.inl rfl, Nat.zero_le _, fun i h1 h2 => absurd h2 (by show ¬ i ≤ 0; omega),
    fun i _ _ _ h1 h2 => absurd h2 (by show ¬ i ≤ 0; omega), by rw [hnil]; rfl, Or.inl rfl,
    Nat.le_refl 1, fun i h1 h2 => absurd h2 (by show ¬ i ≤ 0; omega), Nat.le_refl 1⟩,
    by rw [hnil]⟩


/-! ## Tables with the same slots and keys -/

theorem Inv.of_ent_map {hash : K → JInt .u64} {eqKey : K → K → Bool} {t t' : DictState K V}
    (hi : Inv hash eqKey t) (G : K × V → K × V) (hG : ∀ e, (G e).1 = e.1)
    (hs : t'.size = t.size) (hsl : t'.slots = t.slots) (hk : t'.keys = t.keys)
    (hc : t'.count = t.count) (hm : t'.maxprobe = t.maxprobe) (hf : t'.idxfloor = t.idxfloor)
    (hp : t'.popcursor = t.popcursor)
    (he : ∀ p, 1 ≤ p → p ≤ t.size → ent t' p = (ent t p).map G) :
    Inv hash eqKey t' ∧ tlist t' = (tlist t).map G := by
  have htl : tlist t' = (tlist t).map G := by
    unfold tlist
    rw [hs, List.map_filterMap]
    apply filterMap_congr_mem
    intro x hx
    rw [List.mem_range'_1] at hx
    exact he x hx.1 (by omega)
  refine ⟨⟨by rw [hs]; exact hi.size, by rw [hs]; exact hi.sizeLe, fun i h1 h2 => ?_, ?_, ?_,
    by rw [hm, hs]; exact hi.maxprobe, by rw [hf]; exact hi.idxfloor,
    fun i h1 h2 hfi => ?_, by rw [hp]; exact hi.popcursor⟩, htl⟩
  · rw [hs] at h2
    have hne : ∀ p, 1 ≤ p → p ≤ t.size → t.slots p ≠ 0 → t'.slots p ≠ 0 :=
      fun p _ _ h => by rw [hsl]; exact h
    rcases hi.slot i h1 h2 with h0 | h127 | ⟨k, v, hki, hvi, hsi, hci⟩
    · exact Or.inl (by rw [hsl]; exact h0)
    · exact Or.inr (Or.inl (by rw [hsl]; exact h127))
    · have hfi : filledB (t.slots i) = true := by rw [hsi]; exact shorthash7_filled _
      have he' := he i h1 h2
      rw [ent_of_filled hfi hki hvi, Option.map_some] at he'
      obtain ⟨-, hk', hv'⟩ := ent_some he'
      have hpp : IsPow t.size ∧ t.maxprobe < t.size := by
        rcases hi.size with h | h
        · omega
        · rcases hi.maxprobe with h' | h'
          · omega
          · exact ⟨h, h'⟩
      refine Or.inr (Or.inr ⟨k, (G (k, v)).2, ?_, hv', by rw [hsl]; exact hsi,
        Chain.mono hpp.1 hpp.2 hs (by rw [hm]; exact Nat.le_refl _) hne hci⟩)
      rw [hk']
      rw [hG]
  · intro a b x y ha1 ha2 hb1 hb2 hab hx hy
    rw [hs] at ha2 hb2
    rw [he a ha1 ha2] at hx
    rw [he b hb1 hb2] at hy
    cases hxa : ent t a with
    | none => rw [hxa] at hx; cases hx
    | some x0 =>
      cases hyb : ent t b with
      | none => rw [hyb] at hy; cases hy
      | some y0 =>
        rw [hxa, Option.map_some] at hx
        rw [hyb, Option.map_some] at hy
        cases hx
        cases hy
        rw [hG, hG]
        exact hi.distinct a b x0 y0 ha1 ha2 hb1 hb2 hab hxa hyb
  · rw [hc, hi.count, htl, List.length_map]
  · rw [hs] at h2
    rw [hsl] at hfi
    rw [hf]
    exact hi.floorLe i h1 h2 hfi

/-! ## `map!(f, values(d))` -/

/-- The value loop of `map!` with a function `g` that returns. -/
theorem mapValuesLoop_spec {hash : K → JInt .u64} {eqKey : K → K → Bool} (g : V → V)
    {t : DictState K V} :
    ∀ n i (h : DictState K V), h.size = t.size → h.slots = t.slots → h.keys = t.keys →
      h.count = t.count → h.maxprobe = t.maxprobe → h.idxfloor = t.idxfloor →
      h.popcursor = t.popcursor → Inv hash eqKey t → 1 ≤ i → i + n = t.size + 1 →
      (∀ p, 1 ≤ p → p < i → ent h p = (ent t p).map (fun e => (e.1, g e.2))) →
      (∀ p, i ≤ p → p ≤ t.size → ent h p = ent t p) →
      ∃ h', mapValuesLoop (fun v => .ok (g v)) h n i = .ok h' ∧ h'.size = t.size ∧
        h'.slots = t.slots ∧ h'.keys = t.keys ∧ h'.count = t.count ∧ h'.maxprobe = t.maxprobe ∧
        h'.idxfloor = t.idxfloor ∧ h'.popcursor = t.popcursor ∧
        ∀ p, 1 ≤ p → p ≤ t.size → ent h' p = (ent t p).map (fun e => (e.1, g e.2))
  | 0, i, h, hs, hsl, hk, hc, hm, hf, hp, _, _, hn, hlt, _ =>
    ⟨h, rfl, hs, hsl, hk, hc, hm, hf, hp, fun p h1 h2 => hlt p h1 (by omega)⟩
  | n + 1, i, h, hs, hsl, hk, hc, hm, hf, hp, hi, h1, hn, hlt, hge => by
    have hstep : mapValuesLoop (fun v => .ok (g v)) h (n + 1) i =
        if isslotfilled h i then
          (valAt h i >>= fun value => (Except.ok (g value) : DictResult V) >>= fun value =>
            mapValuesLoop (fun v => .ok (g v))
              (DictState.mk h.size h.slots h.keys (updateAt h.vals i (some value)) h.ndel h.count
                h.age h.idxfloor h.maxprobe h.popcursor) n (i + 1))
        else mapValuesLoop (fun v => .ok (g v)) h n (i + 1) := rfl
    rw [hstep, isslotfilled_eq]
    by_cases hfl : filledB (h.slots i) = true
    · rw [if_pos hfl]
      have hti : filledB (t.slots i) = true := by rw [← hsl]; exact hfl
      obtain ⟨k, v, -, -, he, -, -⟩ := hi.filled h1 (by omega) hti
      have heh : ent h i = some (k, v) := by rw [hge i (Nat.le_refl _) (by omega)]; exact he
      rw [valAt_of_ent heh, except_ok_bind, except_ok_bind]
      refine mapValuesLoop_spec g n (i + 1) _ hs hsl hk hc hm hf hp hi (by omega) (by omega)
        (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)
      · by_cases hpi : p = i
        · subst hpi
          rw [he, Option.map_some]
          exact ent_of_filled (t := DictState.mk h.size h.slots h.keys
            (updateAt h.vals p (some (g v))) h.ndel h.count h.age h.idxfloor h.maxprobe h.popcursor)
            hfl (ent_some heh).2.1 (by show updateAt h.vals p (some (g v)) p = _; rw [updateAt_same])
        · have : ent (DictState.mk h.size h.slots h.keys (updateAt h.vals i (some (g v))) h.ndel
              h.count h.age h.idxfloor h.maxprobe h.popcursor) p = ent h p := by
            unfold ent
            show (if filledB (h.slots p) then match h.keys p, updateAt h.vals i (some (g v)) p with
              | some k, some v => some (k, v) | _, _ => none else none) = _
            rw [updateAt_ne _ _ hpi]
          rw [this]
          exact hlt p hp1 (by omega)
      · have : ent (DictState.mk h.size h.slots h.keys (updateAt h.vals i (some (g v))) h.ndel
            h.count h.age h.idxfloor h.maxprobe h.popcursor) p = ent h p := by
          unfold ent
          show (if filledB (h.slots p) then match h.keys p, updateAt h.vals i (some (g v)) p with
            | some k, some v => some (k, v) | _, _ => none else none) = _
          rw [updateAt_ne _ _ (by omega)]
        rw [this]
        exact hge p (by omega) hp2
    · rw [if_neg hfl]
      have hfl' : filledB (h.slots i) = false := by simpa using hfl
      refine mapValuesLoop_spec g n (i + 1) h hs hsl hk hc hm hf hp hi (by omega) (by omega)
        (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => hge p (by omega) hp2)
      by_cases hpi : p = i
      · subst hpi
        rw [ent_of_not_filled hfl', ← hge p (Nat.le_refl _) (by omega), ent_of_not_filled hfl']
        rfl
      · exact hlt p hp1 (by omega)

/-- `map!(f, values(d))` with a returning `f` replaces every stored value `v` by `f(v)`. -/
theorem DictRep.mapBang {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    {m : List (K × V)} (h : DictRep hash eqKey t m) (g : V → V) :
    ∃ t', JuliaLean.base.dict.mapBang (fun v => .ok (g v)) ⟨t⟩ = .ok ⟨t'⟩ ∧
      DictRep hash eqKey t' (m.map (fun e => (e.1, g e.2))) ∧ t'.keys = t.keys := by
  have hfl := h.1.idxfloor
  have hlow : ∀ p, 1 ≤ p → p < t.idxfloor → p ≤ t.size → ent t p = none := by
    intro p h1 h2 h3
    apply ent_of_not_filled
    cases hf : filledB (t.slots p)
    · rfl
    · have := h.1.floorLe p h1 h3 hf; omega
  have key : ∀ t' : DictState K V, t'.size = t.size → t'.slots = t.slots → t'.keys = t.keys →
      t'.count = t.count → t'.maxprobe = t.maxprobe → t'.idxfloor = t.idxfloor →
      t'.popcursor = t.popcursor →
      (∀ p, 1 ≤ p → p ≤ t.size → ent t' p = (ent t p).map (fun e => (e.1, g e.2))) →
      DictRep hash eqKey t' (m.map (fun e => (e.1, g e.2))) := by
    intro t' hs hsl hk hc hm hf hp he
    obtain ⟨hI, htl⟩ := Inv.of_ent_map h.1 (fun e => (e.1, g e.2)) (fun _ => rfl) hs hsl hk hc hm
      hf hp he
    exact ⟨hI, by rw [htl]; exact h.2.map _⟩
  unfold JuliaLean.base.dict.mapBang
  dsimp only
  split
  · refine ⟨t, rfl, key t rfl rfl rfl rfl rfl rfl rfl
      (fun p h1 h2 => by rw [hlow p h1 (by omega) h2]; rfl), rfl⟩
  · rename_i hgt
    obtain ⟨t', ht', hs, hsl, hk, hc, hm, hf, hp, he⟩ := mapValuesLoop_spec g
      (t.size - t.idxfloor + 1) t.idxfloor t
      rfl rfl rfl rfl rfl rfl rfl h.1 hfl (by omega)
      (fun p h1 h2 => by rw [hlow p h1 h2 (by omega)]; rfl) (fun p _ _ => rfl)
    rw [ht', except_ok_bind]
    exact ⟨t', rfl, key t' hs hsl hk hc hm hf hp he, hk⟩


/-! ## `keys(d)` and `values(d)` iteration -/

/-- The part of a stored pair that `iterate(::KeySet)`/`iterate(::ValueIterator)` returns. -/
def entPart : (part : DictPart) → K × V → part.Elem K V
  | .keys, e => e.1
  | .vals, e => e.2

theorem partAt_of_ent {t : DictState K V} {i : Nat} {k : K} {v : V}
    (he : ent t i = some (k, v)) (part : DictPart) : partAt t part i = .ok (entPart part (k, v)) := by
  cases part with
  | keys => exact keyAt_of_ent he
  | vals => exact valAt_of_ent he

/-- Repeated `iterate(v, i)` calls on `keys(d)` or `values(d)`. -/
def partCollect (t : DictState K V) (part : DictPart) : Nat → Nat → DictResult (List (part.Elem K V))
  | 0, _ => .ok []
  | fuel + 1, i => do
    match ← iteratePart t part i with
    | none => .ok []
    | some (x, next) => do
      let rest ← partCollect t part fuel next
      .ok (x :: rest)

theorem partCollect_spec {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    (hi : Inv hash eqKey t) (hbig : t.size < 2 ^ 63 - 1) (part : DictPart) :
    ∀ fuel i, 1 ≤ i → t.size + 1 - i < fuel →
      partCollect t part fuel i =
        .ok (((List.range' i (t.size + 1 - i)).filterMap (ent t)).map (entPart part))
  | 0, _, _, h => absurd h (by omega)
  | fuel + 1, i, h1, hf => by
    have hstep : partCollect t part (fuel + 1) i = (iteratePart t part i >>= fun r =>
        match r with
        | none => .ok []
        | some (x, next) => partCollect t part fuel next >>= fun rest => .ok (x :: rest)) := rfl
    rw [hstep]
    unfold iteratePart
    rw [if_neg (by simp; omega)]
    rcases skipDeleted_spec t h1 with ⟨h0, hall⟩ | ⟨hr1, hr2, hr3, hr4⟩
    · dsimp only
      rw [h0]
      rw [filterMap_ent_range_skip _ _ (fun p hp1 hp2 => hall p hp1 (by omega))]
      rfl
    · obtain ⟨k, v, -, -, he, -, -⟩ := hi.filled (by omega) hr2 hr3
      dsimp only
      rw [if_neg (by simp; omega), partAt_of_ent he, except_ok_bind, except_ok_bind,
        if_neg (by simp; omega)]
      dsimp only
      rw [partCollect_spec hi hbig part fuel (skipDeleted t i + 1) (by omega) (by omega),
        except_ok_bind]
      rw [range'_split i (skipDeleted t i) (t.size + 1 - i) hr1 (by omega), List.filterMap_append,
        filterMap_ent_range_skip _ _ (fun p hp1 hp2 => hr4 p hp1 (by omega)), List.nil_append,
        List.filterMap_cons_some he,
        show i + (t.size + 1 - i) - (skipDeleted t i + 1) = t.size + 1 - (skipDeleted t i + 1) by omega]
      rfl

/-- `for x in keys(d)` / `for x in values(d)` (`iterate(v, i = v.dict.idxfloor)`) yields the key or
value of every stored pair once, in slot order. -/
theorem DictRep.iteratePart {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    {m : List (K × V)} (h : DictRep hash eqKey t m) (hbig : t.size < 2 ^ 63 - 1)
    (part : DictPart) :
    partCollect t part (t.size + 2) t.idxfloor = .ok ((tlist t).map (entPart part)) := by
  rw [partCollect_spec h.1 hbig part (t.size + 2) t.idxfloor h.1.idxfloor (by omega),
    ← tlist_from_floor h.1]

/-! ## `skip_deleted_floor!` -/

theorem DictRep.skipDeletedFloor {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {t : DictState K V} {m : List (K × V)} (h : DictRep hash eqKey t m) :
    (JuliaLean.base.dict.skipDeletedFloor t).1 = skipDeleted t t.idxfloor ∧
      DictRep hash eqKey (JuliaLean.base.dict.skipDeletedFloor t).2 m ∧
      ((JuliaLean.base.dict.skipDeletedFloor t).1 ≠ 0 →
        (JuliaLean.base.dict.skipDeletedFloor t).2.idxfloor =
          (JuliaLean.base.dict.skipDeletedFloor t).1) := by
  unfold JuliaLean.base.dict.skipDeletedFloor
  dsimp only
  refine ⟨rfl, ?_, ?_⟩
  · split
    · rename_i hne
      have hi := h.1
      have hne' : skipDeleted t t.idxfloor ≠ 0 := by simpa using hne
      rcases skipDeleted_spec t hi.idxfloor with ⟨h0, -⟩ | ⟨h1, h2, h3, h4⟩
      · exact absurd h0 hne'
      · have hent : tlist (DictState.mk t.size t.slots t.keys t.vals t.ndel t.count t.age
            (skipDeleted t t.idxfloor) t.maxprobe t.popcursor) = tlist t := rfl
        refine ⟨⟨hi.size, hi.sizeLe, fun j hj1 hj2 => SlotOK.transfer (hi.slot j hj1 hj2) rfl rfl rfl
          (fun k hc => hc), hi.distinct, hi.count, hi.maxprobe,
          by show 1 ≤ skipDeleted t t.idxfloor; have := hi.idxfloor; omega,
          fun j hj1 hj2 hjf => ?_, hi.popcursor⟩, by rw [hent]; exact h.2⟩
        show skipDeleted t t.idxfloor ≤ j
        apply Classical.byContradiction
        intro hlt
        have := h4 j (hi.floorLe j hj1 hj2 hjf) (by omega)
        rw [hjf] at this
        cases this
    · exact h
  · intro hne
    rw [if_pos (by simpa using hne)]

/-! ## `copy(d)` -/

theorem DictRep.copyDict {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {copySlots : Nat → (Nat → Nat) → Nat → Nat} {copyKeys : Nat → (Nat → Option K) → Nat → Option K}
    {copyVals : Nat → (Nat → Option V) → Nat → Option V} (hcs : CopyLaw copySlots)
    (hck : CopyLaw copyKeys) (hcv : CopyLaw copyVals) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) :
    DictRep hash eqKey (JuliaLean.base.dict.copyDict copySlots copyKeys copyVals t) m := by
  let c := JuliaLean.base.dict.copyDict copySlots copyKeys copyVals t
  have hs : ∀ i, 1 ≤ i → i ≤ t.size → c.slots i = t.slots i := fun i h1 h2 => hcs t.size t.slots i h1 h2
  have hk : ∀ i, 1 ≤ i → i ≤ t.size → c.keys i = t.keys i := fun i h1 h2 => hck t.size t.keys i h1 h2
  have hv : ∀ i, 1 ≤ i → i ≤ t.size → c.vals i = t.vals i := fun i h1 h2 => hcv t.size t.vals i h1 h2
  have hpp : t.size = 0 ∨ (IsPow t.size ∧ t.maxprobe < t.size) := by
    rcases h.1.size with h0 | hp
    · exact Or.inl h0
    · rcases h.1.maxprobe with h0 | hm
      · exact Or.inl h0
      · exact Or.inr ⟨hp, hm⟩
  have hent : ∀ i, 1 ≤ i → i ≤ t.size → ent c i = ent t i :=
    fun i h1 h2 => ent_congr (hs i h1 h2) (hk i h1 h2) (hv i h1 h2)
  have htl : tlist c = tlist t := tlist_congr rfl hent
  have hi := h.1
  refine ⟨⟨hi.size, hi.sizeLe, fun i h1 h2 => ?_, fun a b x y ha1 ha2 hb1 hb2 hab hx hy => ?_,
    by rw [htl]; exact hi.count, hi.maxprobe, hi.idxfloor, fun i h1 h2 hf => ?_, hi.popcursor⟩,
    by rw [htl]; exact h.2⟩
  · rcases hpp with h0 | ⟨hpow, hmp⟩
    · exact absurd h2 (by show ¬ i ≤ t.size; omega)
    · refine SlotOK.transfer (hi.slot i h1 h2) (hs i h1 h2) (hk i h1 h2) (hv i h1 h2) ?_
      intro k hc
      exact Chain.mono hpow hmp rfl (Nat.le_refl _)
        (fun p hp1 hp2 hp0 => by rw [hs p hp1 hp2]; exact hp0) hc
  · rw [hent a ha1 ha2] at hx
    rw [hent b hb1 hb2] at hy
    exact hi.distinct a b x y ha1 ha2 hb1 hb2 hab hx hy
  · rw [hs i h1 h2] at hf
    exact hi.floorLe i h1 h2 hf


/-! # Properties -/

/-- After `d[k] = v`, the table represents `rset m k v`: a key `isequal` to `k` finds `v` and every
other lookup keeps its value. The `Dict{K,Any}` overload stores `v` as is,
`setindex!(h::Dict{K,V}, v0, key::K)` converts the value first, and `setindex!(h, v0, key0)` also
converts the key and throws `KeyTypeError` when the conversion changes its `isequal` identity. -/
def DictSetindexLookup : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → TableszLaw tablesz → DictRep hash eqKey h m → h.count < 2 ^ 54 →
    (∀ (key : K) (value : V), ∃ h', setindexAny hash eqKey tablesz h value key = .ok h' ∧
      DictRep hash eqKey h' (rset eqKey m key value)) ∧
    (∀ (key : K) (w : W), match convertValue valueConv w with
      | .ok v => ∃ h', setindexTyped hash eqKey tablesz valueConv h w key = .ok h' ∧
          DictRep hash eqKey h' (rset eqKey m key v)
      | .error e => setindexTyped hash eqKey tablesz valueConv h w key = .error e) ∧
    (∀ (key0 : Q) (w : W), match refStep eqKey keyConv valueConv m (key0, w) with
      | .ok m' => ∃ h', setindexConv hash eqKey tablesz keyConv valueConv h w key0 = .ok h' ∧
          DictRep hash eqKey h' m'
      | .error e => setindexConv hash eqKey tablesz keyConv valueConv h w key0 = .error e)

theorem DictSetindexLookup_proven : DictSetindexLookup := by
  intro K V Q W hash eqKey tablesz keyConv valueConv h m hl htz hr hc
  refine ⟨fun key value => ?_, fun key w => ?_,
    fun key0 w => hr.setConv hl htz keyConv valueConv hc (key0, w)⟩
  · rw [setindexAny_eq]; exact hr.store hl htz hc key value
  · rw [setindexTyped_eq]
    cases convertValue valueConv w with
    | error e => rfl
    | ok v => rw [except_ok_bind]; exact hr.store hl htz hc key v

/-- `ht_keyindex(h, key)` returns the slot of the stored key `isequal` to `key`, or `-1`;
`ht_keyindex2_shorthash!(h, key)` returns that slot without changing the table, or a negative free
slot on the key's probe sequence of a table (possibly rehashed or with a larger `maxprobe`) holding
the same pairs, with the short hash of `key`; `ht_keyindex2!` returns the same index. -/
def DictProbeSemantics : Prop :=
  ∀ (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (tablesz : Nat → Nat) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → TableszLaw tablesz →
    DictRep hash eqKey h m → h.count < 2 ^ 54 →
    (∀ q : Q,
      (match rfind matchQ m q with
        | some e => ∃ i : Nat, htKeyindex hashQ matchQ h q = .ok (i : Int) ∧ 1 ≤ i ∧ i ≤ h.size ∧
            ent h i = some e
        | none => htKeyindex hashQ matchQ h q = .ok (-1)) ∧
      ∃ idx h', htKeyindex2Query hash hashQ matchQ tablesz h q = .ok (idx, shorthash7 (hashQ q), h') ∧
        DictRep hash eqKey h' m ∧
        (match rfind matchQ m q with
          | some e => ∃ i : Nat, idx = i ∧ h' = h ∧ ent h i = some e
          | none => idx < 0 ∧ InsertSlot h' (home hashQ h'.size q) (-idx).toNat)) ∧
    ∀ k : K, ∃ idx h', htKeyindex2 hash eqKey tablesz h k = .ok (idx, shorthash7 (hash k), h') ∧
      htKeyindex2Bang hash eqKey tablesz h k = .ok (idx, h')

theorem DictProbeSemantics_proven : DictProbeSemantics := by
  intro K V Q hash eqKey hashQ matchQ tablesz h m hl hq htz hr hc
  refine ⟨fun q => ⟨hr.htKeyindex hl hq q, ?_⟩, fun k => ?_⟩
  · obtain ⟨idx, t', n, hprobe, -, hout⟩ := htKeyindex2Query_spec hl hq htz hr.1 hc q
    refine ⟨idx, t', hprobe, ⟨hout.inv, hout.perm.trans hr.2⟩, ?_⟩
    have hd : Distinct eqKey (tlist h) := tlist_pairwise hr.1
    rw [← rfind_perm hl hq hd hr.2]
    cases hf : rfind matchQ (tlist h) q with
    | some e =>
      obtain ⟨hem, heq⟩ := rfind_some hf
      obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
      obtain ⟨hidx, ht1⟩ := hout.found i e h1 h2 hei heq
      exact ⟨i, hidx, ht1, hei⟩
    | none => exact hout.absent (rfind_eq_none_iff.1 hf)
  · obtain ⟨idx, t', n, hprobe, -, -⟩ := htKeyindex2_spec' hl htz hr.1 hc k
    refine ⟨idx, t', hprobe, ?_⟩
    unfold htKeyindex2Bang
    rw [hprobe]
    rfl

/-- `delete!(h, key)` removes every pair whose key is `isequal` to `key` and keeps the others. -/
def DictDeleteLookup : Prop :=
  ∀ (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → UnsetLaw unsetKey →
    UnsetLaw unsetVal → DictRep hash eqKey h m → ∀ q : Q,
    ∃ h', deleteKey hashQ matchQ unsetKey unsetVal h q = .ok h' ∧
      DictRep hash eqKey h' (rdel matchQ m q)

theorem DictDeleteLookup_proven : DictDeleteLookup := by
  intro K V Q hash eqKey hashQ matchQ unsetKey unsetVal h m hl hq huk huv hr q
  exact hr.deleteKey hl huk huv hq q

/-- `pop!(h, key)` returns the stored value and removes the key, or throws `KeyError`;
`pop!(h, key, default)` returns `default` and leaves the table alone when the key is absent. -/
def DictPopKeyContract : Prop :=
  ∀ (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → UnsetLaw unsetKey →
    UnsetLaw unsetVal → DictRep hash eqKey h m → ∀ (q : Q) (default : V),
    (match rfind matchQ m q with
      | some e => ∃ h', popKey hashQ matchQ unsetKey unsetVal h q = .ok (e.2, h') ∧
          DictRep hash eqKey h' (rdel matchQ m q)
      | none => popKey hashQ matchQ unsetKey unsetVal h q = .error .keyError) ∧
    (match rfind matchQ m q with
      | some e => ∃ h', popDefault hashQ matchQ unsetKey unsetVal h q default = .ok (e.2, h') ∧
          DictRep hash eqKey h' (rdel matchQ m q)
      | none => popDefault hashQ matchQ unsetKey unsetVal h q default = .ok (default, h))

theorem DictPopKeyContract_proven : DictPopKeyContract := by
  intro K V Q hash eqKey hashQ matchQ unsetKey unsetVal h m hl hq huk huv hr q default
  exact ⟨hr.popKey hl huk huv hq q, hr.popDefault hl huk huv hq q default⟩

/-- `pop!(h)` throws `ArgumentError` on an empty dictionary and otherwise removes and returns one
stored pair. -/
def DictPopAnyContract : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → UnsetLaw unsetKey → UnsetLaw unsetVal → DictRep hash eqKey h m →
    match m with
    | [] => popAny unsetKey unsetVal h = .error .argumentError
    | _ :: _ => ∃ e h', popAny unsetKey unsetVal h = .ok (e, h') ∧ e ∈ m ∧
        DictRep hash eqKey h' (rdel eqKey m e.1)

theorem DictPopAnyContract_proven : DictPopAnyContract := by
  intro K V hash eqKey unsetKey unsetVal h m hl huk huv hr
  have hp := hr.popAny hl huk huv
  cases m with
  | nil => exact hp
  | cons a rest => exact hp

/-- `empty!(h)` leaves a well-formed dictionary with no pairs; `isempty` and `length` report the
number of stored pairs. -/
def DictEmptyContract : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) (h : DictState K V)
    (m : List (K × V)),
    FillLaw fillSlots → DictRep hash eqKey h m →
    DictRep hash eqKey (emptyBang fillSlots unsetKey unsetVal h) [] ∧
      isempty (emptyBang fillSlots unsetKey unsetVal h) = true ∧
      length (emptyBang fillSlots unsetKey unsetVal h) = 0 ∧
      isempty h = m.isEmpty ∧ length h = m.length

theorem DictEmptyContract_proven : DictEmptyContract := by
  intro K V hash eqKey fillSlots unsetKey unsetVal h m hfill hr
  obtain ⟨hrep, -⟩ := emptyBang_spec hfill unsetKey unsetVal hr.1
  have hc : h.count = m.length := by rw [hr.1.count, hr.2.length_eq]
  refine ⟨hrep, rfl, rfl, ?_, hc⟩
  unfold isempty
  rw [hc]
  cases m <;> rfl

/-- `filter!(pred, h)` keeps exactly the pairs for which `pred` is true. -/
def DictFilterContract : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → UnsetLaw unsetKey → UnsetLaw unsetVal → DictRep hash eqKey h m →
    ∀ pred : K × V → Bool, ∃ h', filterBang unsetKey unsetVal pred h = .ok h' ∧
      DictRep hash eqKey h' (m.filter pred)

theorem DictFilterContract_proven : DictFilterContract := by
  intro K V hash eqKey unsetKey unsetVal h m hl huk huv hr pred
  exact hr.filterBang hl huk huv pred

/-- `sizehint!(d, n; shrink)` with `3n` within `Int` returns and keeps every pair. -/
def DictSizehintSmall : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (h : DictState K V) (m : List (K × V)),
    TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    DictRep hash eqKey h m → h.count < 2 ^ 54 → ∀ (n : JInt .i64) (shrink : Bool), n.val ≤ 2 ^ 61 →
    ∃ h', sizehint hash tablesz maxValues cld h n shrink = .ok h' ∧ DictRep hash eqKey h' m

theorem DictSizehintSmall_proven : DictSizehintSmall := by
  intro K V hash eqKey tablesz maxValues cld h m htz hmv hcld hr hc n shrink hn
  obtain ⟨h', h1, h2, -⟩ := sizehint_spec htz hmv hcld hr hc n hn shrink
  exact ⟨h', h1, h2⟩

/-- Every `Int` size hint returns and keeps every pair. -/
def DictSizehintTotal : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    DictRep hash eqKey h m → h.count < 2 ^ 54 → ∀ (n : JInt .i64) (shrink : Bool),
    ∃ h', sizehint hash tablesz maxValues cld h n shrink = .ok h' ∧ DictRep hash eqKey h' m

/-- `get!(default, h, key)` returns a present key's value without calling `default` and without
changing the table; otherwise it calls `default` once on a table with the same pairs and stores the
converted result on top of every change `default` made (`get!` docstring, `base/dict.jl:416-442`).
`get!(default, h, key0)` first converts the key like `setindex!`. -/
def DictGetBangMutatingDefault : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (h : DictState K V) (m : List (K × V))
    (default : DictState K V → DictResult (W × DictState K V)),
    KeyLaws hash eqKey → TableszLaw tablesz → DictRep hash eqKey h m → h.count < 2 ^ 54 →
    DefaultOK hash eqKey default →
    (∀ key : K, match rfind eqKey m key with
      | some e => getBang hash eqKey tablesz valueConv h key default = .ok (e.2, h)
      | none => ∃ h1, DictRep hash eqKey h1 m ∧
          (∀ err, default h1 = .error err →
            getBang hash eqKey tablesz valueConv h key default = .error err) ∧
          (∀ w h2, default h1 = .ok (w, h2) →
            match convertValue valueConv w with
            | .error err => getBang hash eqKey tablesz valueConv h key default = .error err
            | .ok v => ∃ h', getBang hash eqKey tablesz valueConv h key default = .ok (v, h') ∧
                DictRep hash eqKey h' (rset eqKey (tlist h2) key v))) ∧
    ∀ key0 : Q, match convKey keyConv key0 with
      | .error err => getBangConv hash eqKey tablesz keyConv valueConv h key0 default = .error err
      | .ok key => getBangConv hash eqKey tablesz keyConv valueConv h key0 default =
          getBang hash eqKey tablesz valueConv h key default

theorem DictGetBangMutatingDefault_proven : DictGetBangMutatingDefault := by
  intro K V Q W hash eqKey tablesz keyConv valueConv h m default hl htz hr hc hdef
  refine ⟨fun key => getBang_spec hl htz valueConv hr hc key default hdef, fun key0 => ?_⟩
  unfold getBangConv convKey
  cases keyConv.isa key0 with
  | some k => rfl
  | none =>
    show (match (match keyConv.convert key0 with
      | .ok k => if keyConv.isequal key0 k then Except.ok k else Except.error DictError.keyTypeError
      | .error e => .error e) with
      | .error err => _ | .ok key => _)
    cases keyConv.convert key0 with
    | error e => rfl
    | ok k => by_cases he : keyConv.isequal key0 k = true <;> simp [he]

/-- Every `Dict` lookup agrees with the reference map for queries of any type:
`getindex` throws `KeyError` for an absent key, both `get`s return their defaults (calling the
function only when absent), `haskey` and `in(key, keys(d))` report presence, and `getkey` returns
the stored key. -/
def DictLookupSemantics : Prop :=
  ∀ (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → DictRep hash eqKey h m →
    ∀ (q : Q) (default : V) (defaultKey : K) (defaultF : Unit → DictResult V),
      getindex hashQ matchQ h q =
          (match rlookup matchQ m q with | some v => .ok v | none => .error .keyError) ∧
        JuliaLean.base.dict.get hashQ matchQ h q default = .ok ((rlookup matchQ m q).getD default) ∧
        getF hashQ matchQ h q defaultF =
          (match rlookup matchQ m q with | some v => .ok v | none => defaultF ()) ∧
        haskey hashQ matchQ h q = .ok (rlookup matchQ m q).isSome ∧
        inKeySet hashQ matchQ ⟨h⟩ q = .ok (rlookup matchQ m q).isSome ∧
        getkey hashQ matchQ h q defaultKey = .ok (((rfind matchQ m q).map (·.1)).getD defaultKey)

theorem DictLookupSemantics_proven : DictLookupSemantics := by
  intro K V Q hash eqKey hashQ matchQ h m hl hq hr q default defaultKey defaultF
  exact hr.lookups hl hq q default defaultKey defaultF


/-- The reference map of a constructor loop `for (k, v) in kv; h[k] = v; end`. -/
def refBuild {Q W : Type} (eqKey : K → K → Bool) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (pairs : List (Q × W)) : DictResult (List (K × V)) :=
  pairs.foldlM (refStep eqKey keyConv valueConv) []

section CtorProps
variable {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat}

theorem fromIterator_insert_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pairs : List (Q × W)) (t : DictState K V)
    (ht : DictRep hash eqKey t []) (hc : t.count + pairs.length < 2 ^ 54) :
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m' => ∃ t', dictFromIterator.insert hash eqKey tablesz keyConv valueConv pairs t = .ok t' ∧
        DictRep hash eqKey t' m'
    | .error e => dictFromIterator.insert hash eqKey tablesz keyConv valueConv pairs t = .error e :=
  insertLoop_spec hl htz keyConv valueConv _ (fun _ => rfl)
    (fun p rest t => by obtain ⟨a, b⟩ := p; rfl) pairs t [] ht hc

theorem fromPairs_insert_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pairs : List (Q × W)) (t : DictState K V)
    (ht : DictRep hash eqKey t []) (hc : t.count + pairs.length < 2 ^ 54) :
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m' => ∃ t', dictFromPairs.insert hash eqKey tablesz keyConv valueConv pairs t = .ok t' ∧
        DictRep hash eqKey t' m'
    | .error e => dictFromPairs.insert hash eqKey tablesz keyConv valueConv pairs t = .error e :=
  insertLoop_spec hl htz keyConv valueConv _ (fun _ => rfl) (fun p rest t => rfl) pairs t [] ht hc

/-- `sizehint!(Dict{K,V}(), n)` for a small `n` gives an empty well-formed table. -/
theorem sizehint_empty (htz : TableszLaw tablesz) {maxValues : Nat}
    (hmv : MaxValuesLaw eqKey maxValues) {cld : JInt .i64 → JInt .i64} (hcld : CldLaw cld)
    (n : Nat) (hn : n ≤ 2 ^ 53) :
    ∃ t, sizehint hash tablesz maxValues cld (dictEmpty K V) (JInt.lit .i64 (Int.ofNat n)) true =
      .ok t ∧ DictRep hash eqKey t [] ∧ t.count = 0 := by
  have hv : (JInt.lit .i64 (Int.ofNat n)).val = n := by
    unfold JInt.lit; apply wrap_i64_val <;> simp only [Int.ofNat_eq_coe] <;> omega
  obtain ⟨t, h1, h2, h3⟩ := sizehint_spec htz hmv hcld (dictEmpty_rep (V := V) hash eqKey)
    (by show (0 : Nat) < 2 ^ 54; decide)
    (JInt.lit .i64 (Int.ofNat n)) (by rw [hv]; omega) true
  exact ⟨t, h1, h2, h3⟩

end CtorProps

/-- `Dict{K,V}()`, `empty(a, K, V)`, `Dict()` and `Dict(())` are empty well-formed tables. -/
def DictEmptyConstructorSemantics : Prop :=
  (∀ (K V C : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (a : C),
    DictRep hash eqKey (dictEmpty K V) [] ∧ DictRep hash eqKey (emptyDict K V a) []) ∧
  (∀ (hash : JAny → JInt .u64) (eqKey : JAny → JAny → Bool),
    DictRep hash eqKey dictAny [] ∧ DictRep hash eqKey (dictEmptyTuple ()) [])

theorem DictEmptyConstructorSemantics_proven : DictEmptyConstructorSemantics :=
  ⟨fun _ _ _ hash eqKey _ => ⟨dictEmpty_rep hash eqKey, dictEmpty_rep hash eqKey⟩,
    fun hash eqKey => ⟨dictEmpty_rep hash eqKey, dictEmpty_rep hash eqKey⟩⟩

/-- `Dict{K,V}(kv)` stores the converted pairs in iteration order, a later `isequal` key replacing
an earlier one, and throws the first conversion error (`Dict` docstring, `base/dict.jl:31-64`). -/
def DictIteratorConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (pairs : List (Q × W)) (hasLength : Bool),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    pairs.length ≤ 2 ^ 53 →
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m => ∃ h, dictFromIterator hash eqKey tablesz maxValues cld keyConv valueConv hasLength
        pairs = .ok h ∧ DictRep hash eqKey h m
    | .error e => dictFromIterator hash eqKey tablesz maxValues cld keyConv valueConv hasLength
        pairs = .error e

theorem DictIteratorConstructorSemantics_proven : DictIteratorConstructorSemantics := by
  intro K V Q W hash eqKey tablesz maxValues cld keyConv valueConv pairs hasLength hl htz hmv hcld hn
  unfold dictFromIterator
  dsimp only
  cases hasLength with
  | true =>
    obtain ⟨t, h1, h2, h3⟩ := sizehint_empty (V := V) htz hmv hcld pairs.length hn
    rw [if_pos rfl, h1, except_ok_bind]
    exact fromIterator_insert_spec hl htz keyConv valueConv pairs t h2 (by rw [h3]; omega)
  | false =>
    rw [if_neg (by decide), except_ok_bind]
    exact fromIterator_insert_spec hl htz keyConv valueConv pairs _ (dictEmpty_rep hash eqKey)
      (by show 0 + pairs.length < 2 ^ 54; omega)

/-- `Dict{K,V}(ps::Pair...)` stores the converted pairs in argument order, a later `isequal` key
replacing an earlier one. -/
def DictConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (pairs : List (Q × W)),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    pairs.length ≤ 2 ^ 53 →
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m => ∃ h, dictFromPairs hash eqKey tablesz maxValues cld keyConv valueConv pairs = .ok h ∧
        DictRep hash eqKey h m
    | .error e => dictFromPairs hash eqKey tablesz maxValues cld keyConv valueConv pairs = .error e

theorem DictConstructorSemantics_proven : DictConstructorSemantics := by
  intro K V Q W hash eqKey tablesz maxValues cld keyConv valueConv pairs hl htz hmv hcld hn
  unfold dictFromPairs
  obtain ⟨t, h1, h2, h3⟩ := sizehint_empty (V := V) htz hmv hcld pairs.length hn
  rw [h1, except_ok_bind]
  exact fromPairs_insert_spec hl htz keyConv valueConv pairs t h2 (by rw [h3]; omega)

/-- `Dict{K,V}(p::Pair)` holds the converted pair. -/
def DictSinglePairConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pair : Q × W),
    KeyLaws hash eqKey → TableszLaw tablesz →
    match refStep eqKey keyConv valueConv [] pair with
    | .ok m => ∃ h, dictFromPair hash eqKey tablesz keyConv valueConv pair = .ok h ∧
        DictRep hash eqKey h m
    | .error e => dictFromPair hash eqKey tablesz keyConv valueConv pair = .error e

theorem DictSinglePairConstructorSemantics_proven : DictSinglePairConstructorSemantics := by
  intro K V Q W hash eqKey tablesz keyConv valueConv pair hl htz
  exact (dictEmpty_rep hash eqKey).setConv hl htz keyConv valueConv
    (by show (0 : Nat) < 2 ^ 54; decide) pair

/-- `Dict(ps::Pair{K,V}...)` behaves like `Dict{K,V}(ps)`. -/
def DictTypedPairListConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (pairs : List (Q × W)),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    pairs.length ≤ 2 ^ 53 →
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m => ∃ h, dictTypedPairs hash eqKey tablesz maxValues cld keyConv valueConv pairs = .ok h ∧
        DictRep hash eqKey h m
    | .error e => dictTypedPairs hash eqKey tablesz maxValues cld keyConv valueConv pairs = .error e

theorem DictTypedPairListConstructorSemantics_proven : DictTypedPairListConstructorSemantics := by
  intro K V Q W hash eqKey tablesz maxValues cld keyConv valueConv pairs hl htz hmv hcld hn
  exact DictIteratorConstructorSemantics_proven K V Q W hash eqKey tablesz maxValues cld keyConv
    valueConv pairs true hl htz hmv hcld hn

/-- `Dict(kv)` and `Dict(ps::Pair...)` forward to `dict_with_eltype` (`base/abstractdict.jl`),
which constructs `Dict{K,V}(kv)` for the pair element type: the result holds the converted pairs. -/
def DictGenericConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (pairs : List (Q × W)) (hasLength : Bool)
    (eltype : List (Q × W) → Type)
    (dictWithEltype : List (Q × W) → Type → DictResult (DictState K V)),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    pairs.length ≤ 2 ^ 53 →
    (∀ T, dictWithEltype pairs T =
      dictFromIterator hash eqKey tablesz maxValues cld keyConv valueConv hasLength pairs) →
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m => (∃ h, dictInferred eltype dictWithEltype pairs = .ok h ∧ DictRep hash eqKey h m) ∧
        ∃ h, dictPairsGeneric eltype dictWithEltype pairs = .ok h ∧ DictRep hash eqKey h m
    | .error e => dictInferred eltype dictWithEltype pairs = .error e ∧
        dictPairsGeneric eltype dictWithEltype pairs = .error e

theorem DictGenericConstructorSemantics_proven : DictGenericConstructorSemantics := by
  intro K V Q W hash eqKey tablesz maxValues cld keyConv valueConv pairs hasLength eltype
    dictWithEltype hl htz hmv hcld hn hlaw
  have h := DictIteratorConstructorSemantics_proven K V Q W hash eqKey tablesz maxValues cld
    keyConv valueConv pairs hasLength hl htz hmv hcld hn
  have e1 : dictInferred eltype dictWithEltype pairs =
      dictFromIterator hash eqKey tablesz maxValues cld keyConv valueConv hasLength pairs := hlaw _
  have e2 : dictPairsGeneric eltype dictWithEltype pairs =
      dictFromIterator hash eqKey tablesz maxValues cld keyConv valueConv hasLength pairs := hlaw _
  rw [e1, e2]
  cases hb : refBuild eqKey keyConv valueConv pairs with
  | ok m => rw [hb] at h; exact ⟨h, h⟩
  | error e => rw [hb] at h; exact ⟨h, h⟩

/-- `Dict{K,V}(d::Dict{K,V})` (and `copy(d)`) has the same pairs and counters as `d`. -/
def DictCopySemantics : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (copySlots : Nat → (Nat → Nat) → Nat → Nat)
    (copyKeys : Nat → (Nat → Option K) → Nat → Option K)
    (copyVals : Nat → (Nat → Option V) → Nat → Option V) (h : DictState K V) (m : List (K × V)),
    CopyLaw copySlots → CopyLaw copyKeys → CopyLaw copyVals → DictRep hash eqKey h m →
    DictRep hash eqKey (copyDict copySlots copyKeys copyVals h) m ∧
      (dictCopy copySlots copyKeys copyVals h).count = h.count ∧
      (dictCopy copySlots copyKeys copyVals h).ndel = h.ndel ∧
      (dictCopy copySlots copyKeys copyVals h).age = h.age

theorem DictCopySemantics_proven : DictCopySemantics := by
  intro K V hash eqKey copySlots copyKeys copyVals h m hcs hck hcv hr
  exact ⟨hr.copyDict hcs hck hcv, rfl, rfl, rfl⟩

/-- Every documented `Dict` constructor and copy holds its map contents. -/
def DictConstructionSemantics : Prop :=
  DictEmptyConstructorSemantics ∧ DictIteratorConstructorSemantics ∧
  DictSinglePairConstructorSemantics ∧ DictConstructorSemantics ∧
  DictTypedPairListConstructorSemantics ∧ DictGenericConstructorSemantics ∧ DictCopySemantics

theorem DictConstructionSemantics_proven : DictConstructionSemantics :=
  ⟨DictEmptyConstructorSemantics_proven, DictIteratorConstructorSemantics_proven,
    DictSinglePairConstructorSemantics_proven, DictConstructorSemantics_proven,
    DictTypedPairListConstructorSemantics_proven, DictGenericConstructorSemantics_proven,
    DictCopySemantics_proven⟩

/-- `skip_deleted(h, i)` returns the first filled slot at or after `i` or `0`; iterating a `Dict`,
its `keys` or its `values` visits every stored pair once, in slot order;
`skip_deleted_floor!` advances `idxfloor` to the first filled slot without changing the pairs. -/
def DictIterationSemantics : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (h : DictState K V)
    (m : List (K × V)),
    DictRep hash eqKey h m → h.size < 2 ^ 63 - 1 →
    (∀ start, 1 ≤ start →
      (skipDeleted h start = 0 ∧ ∀ j, start ≤ j → j ≤ h.size → isslotfilled h j = false) ∨
      (start ≤ skipDeleted h start ∧ skipDeleted h start ≤ h.size ∧
        isslotfilled h (skipDeleted h start) = true ∧
        ∀ j, start ≤ j → j < skipDeleted h start → isslotfilled h j = false)) ∧
    (∃ l, (iterateFirst h >>= fun r =>
        match r with
        | none => .ok []
        | some (pair, next) => iterCollect h (h.size + 1) next >>= fun rest => .ok (pair :: rest)) =
      .ok l ∧ List.Perm l m) ∧
    (partCollect h .keys (h.size + 2) h.idxfloor = .ok ((tlist h).map Prod.fst) ∧
      partCollect h .vals (h.size + 2) h.idxfloor = .ok ((tlist h).map Prod.snd) ∧
      List.Perm (tlist h) m) ∧
    (JuliaLean.base.dict.skipDeletedFloor h).1 = skipDeleted h h.idxfloor ∧
      DictRep hash eqKey (JuliaLean.base.dict.skipDeletedFloor h).2 m

theorem DictIterationSemantics_proven : DictIterationSemantics := by
  intro K V hash eqKey h m hr hbig
  obtain ⟨hit, hp⟩ := hr.iterate hbig
  obtain ⟨hf1, hf2, -⟩ := hr.skipDeletedFloor
  refine ⟨fun start hs => skipDeleted_spec h hs, ⟨_, hit, hp⟩,
    ⟨hr.iteratePart hbig .keys, hr.iteratePart hbig .vals, hr.2⟩, hf1, hf2⟩

/-- `Iterators.only(d)` (`Iterators._only(d, first)`, `base/iterators.jl:1673-1678`) returns the
only pair of a one-pair dictionary and throws `ArgumentError` otherwise. `first(d)` returns the
first iterated pair. -/
def DictOnlyContract : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (h : DictState K V)
    (m : List (K × V))
    (only : DictState K V → (DictState K V → DictResult (K × V)) → DictResult (K × V))
    (first : DictState K V → DictResult (K × V)),
    DictRep hash eqKey h m → h.size < 2 ^ 63 - 1 →
    (∀ d f, only d f = if length d != 1 then .error .argumentError else f d) →
    (∀ d, first d = (iterateFirst d >>= fun r =>
      match r with | some (p, _) => .ok p | none => .error .argumentError)) →
    onlyDict only first h = match m with | [e] => .ok e | _ => .error .argumentError

theorem DictOnlyContract_proven : DictOnlyContract := by
  intro K V hash eqKey h m only first hr hbig honly hfirst
  have hc : length h = m.length := by
    show h.count = m.length; rw [hr.1.count, hr.2.length_eq]
  unfold onlyDict
  rw [honly, hc]
  obtain ⟨hit, hp⟩ := hr.iterate hbig
  match m, hp with
  | [], _ => rfl
  | [e], hp =>
    have hl : tlist h = [e] := List.perm_singleton.1 hp
    show (if (1 != 1) = true then _ else _) = _
    rw [if_neg (by decide), hfirst]
    rw [hl] at hit
    revert hit
    cases iterateFirst h with
    | error err => intro hit; cases hit
    | ok r =>
      cases r with
      | none => intro hit; cases hit
      | some pn =>
        obtain ⟨p, n⟩ := pn
        intro hit
        show Except.ok p = _
        change (iterCollect h (h.size + 1) n >>= fun rest => Except.ok (p :: rest)) = _ at hit
        cases hc2 : iterCollect h (h.size + 1) n with
        | error err => rw [hc2] at hit; cases hit
        | ok rest => rw [hc2] at hit; cases hit; rfl
  | a :: b :: rest, _ =>
    show (if ((rest.length + 2) != 1) = true then _ else _) = _
    rw [if_pos (by simp)]

/-- `map!(f, values(d))` replaces every stored value `v` by `f(v)` and keeps the keys. -/
def DictMapReduceSemantics : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (h : DictState K V)
    (m : List (K × V)) (g : V → V),
    DictRep hash eqKey h m →
    ∃ h', mapBang (fun v => .ok (g v)) ⟨h⟩ = .ok ⟨h'⟩ ∧
      DictRep hash eqKey h' (m.map (fun e => (e.1, g e.2)))

theorem DictMapReduceSemantics_proven : DictMapReduceSemantics := by
  intro K V hash eqKey h m g hr
  obtain ⟨h', h1, h2, -⟩ := hr.mapBang g
  exact ⟨h', h1, h2⟩

theorem lor128_add : ∀ y, y < 128 → Nat.lor y 128 = 128 + y := by decide +kernel

theorem filledB_iff : ∀ b, b < 256 → (filledB b = true ↔ 128 ≤ b) := by decide +kernel

/-- The slot bytes: `_shorthash7` stores the top seven hash bits with the high bit set, and the
three byte classes `0x00` (empty), `0x7f` (deleted) and `0x80` and above (full) are disjoint. -/
def DictSlots : Prop :=
  (∀ hash : JInt .u64, shorthash7 hash = 128 + hash.val.toNat / 2 ^ 57 ∧
    128 ≤ shorthash7 hash ∧ shorthash7 hash < 256) ∧
  (∀ b, b < 256 →
    (isslotempty { (dictEmpty Unit Unit) with slots := fun _ => b } 1 = true ↔ b = 0) ∧
    (isslotmissing { (dictEmpty Unit Unit) with slots := fun _ => b } 1 = true ↔ b = 0x7f) ∧
    (isslotfilled { (dictEmpty Unit Unit) with slots := fun _ => b } 1 = true ↔ 128 ≤ b))

theorem DictSlots_proven : DictSlots := by
  refine ⟨fun hash => ?_, fun b hb => ⟨?_, ?_, filledB_iff b hb⟩⟩
  · have hr := u64_val_range hash
    have hlt : hash.val.toNat / 2 ^ 57 < 128 := by omega
    have e : shorthash7 hash = Nat.lor ((hash.val.toNat / 2 ^ 57) % 256) 0x80 := by
      unfold shorthash7; rw [Nat.shiftRight_eq_div_pow]
    rw [e, Nat.mod_eq_of_lt (by omega), lor128_add _ hlt]
    omega
  · show (b == 0) = true ↔ b = 0
    simp
  · show (b == 0x7f) = true ↔ b = 0x7f
    simp

/-- `hashindex(key, sz)` for a power-of-two `sz` returns the one-based slot
`hash(key) mod sz + 1` and the short hash of `key`. -/
def DictHashindexSemantics : Prop :=
  ∀ (K : Type) (hash : K → JInt .u64) (key : K) (p : Nat),
    4 ≤ p → p ≤ 62 →
    (hashindex hash key (2 ^ p)).1 = (hash key).val.toNat % 2 ^ p + 1 ∧
      (hashindex hash key (2 ^ p)).2 = shorthash7 (hash key) ∧
      1 ≤ (hashindex hash key (2 ^ p)).1 ∧ (hashindex hash key (2 ^ p)).1 ≤ 2 ^ p

theorem DictHashindexSemantics_proven : DictHashindexSemantics := by
  intro K hash key p hp1 hp2
  have hpow : IsPow (2 ^ p) := ⟨p, hp1, rfl⟩
  have e : (hashindex hash key (2 ^ p)).1 = (hash key).val.toNat % 2 ^ p + 1 := by
    show Nat.land (hash key).val.toNat (2 ^ p - 1) + 1 = _
    rw [hpow.land]
  have hpos : 0 < 2 ^ p := Nat.two_pow_pos p
  refine ⟨e, rfl, ?_, ?_⟩ <;> rw [e]
  · omega
  · have := Nat.mod_lt (hash key).val.toNat hpos; omega

/-- The slot-byte and hash-index layout. -/
def DictSlotSemantics : Prop := DictSlots ∧ DictHashindexSemantics

theorem DictSlotSemantics_proven : DictSlotSemantics :=
  ⟨DictSlots_proven, DictHashindexSemantics_proven⟩

/-- Linear probing (`(index & (sz-1)) + 1`) stays within the one-based slot memory. -/
def DictProbeSafe : Prop :=
  ∀ size start offset, 0 < size → start < size →
    1 ≤ nextIndex size (start + offset) ∧ nextIndex size (start + offset) ≤ size

theorem DictProbeSafe_proven : DictProbeSafe := by
  intro size start offset h1 _
  unfold nextIndex
  have : Nat.land (start + offset) (size - 1) ≤ size - 1 := Nat.and_le_right
  constructor <;> omega

/-! ## `show` -/

/-- With `:limit => true`, `show(io, d)` prints an ellipsis exactly when it leaves pairs out, that
is when `d` has more than ten pairs; without `:limit` it prints every pair (`IOContext` `:limit`
docstring, `base/show.jl:397-398`). `typeinfo_prefix`, `show_circular`, `show(io, pair)` and
iteration are callees from other files: the hypotheses say that `d` is not circular, `isempty`
agrees with iteration, and no shown part is itself an ellipsis. -/
def DictShowLimitEllipsis : Prop :=
  ∀ (C D K V : Type) (ops : DictShowOps C D K V) (io : C) (d : D),
    ops.isEmpty d = (ops.pairs d).isEmpty → ops.circular io d = false →
    (∀ c p, ops.showPair c p ≠ "…") → (∀ c x, ops.typePrefix c x ≠ "…") →
    ("…" ∈ showDict ops io d ↔ ops.getLimit io = true ∧ 10 < (ops.pairs d).length)

/-! ## `ImmutableDict` -/

/-- The pairs `for pair in d` visits: `iterate(d, t)` until it returns `nothing`, with `fuel`
steps. -/
def immutableCollectFuel : Nat → ImmutableDict K V → List (K × V)
  | 0, _ => []
  | fuel + 1, d =>
    match immutableIterate d with
    | none => []
    | some (pair, rest) => pair :: immutableCollectFuel fuel rest

/-- Every pair iteration visits (the chain of `d` has `d.length` links). -/
def immutableCollect (d : ImmutableDict K V) : List (K × V) := immutableCollectFuel (d.length + 1) d

theorem immutableCollectFuel_eq : ∀ (n : Nat) (d : ImmutableDict K V), d.length < n →
    immutableCollectFuel n d = d
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _ => rfl
  | n + 1, p :: rest, h => by
    simp only [List.length_cons] at h
    simp only [immutableCollectFuel, immutableIterate, immutableCollectFuel_eq n rest (by omega)]

theorem immutableCollect_eq (d : ImmutableDict K V) : immutableCollect d = d :=
  immutableCollectFuel_eq _ d (Nat.lt_succ_self _)

/-- `count(p, itr)` counts the iterated elements for which `p` is true (`count` docstring,
`base/reduce.jl`). -/
def CountLaw (count : (K × V → Bool) → ImmutableDict K V → Nat) : Prop :=
  ∀ p d, count p d = (immutableCollect d).countP p

/-- The pair `new` stores for arguments `key, value`: `convert(K, key) => convert(V, value)`. -/
def newPair {Q W : Type} (keyConv : ValueConv Q K) (valueConv : ValueConv W V) (p : Q × W) :
    DictResult (K × V) := do
  let k ← convertValue keyConv p.1
  let v ← convertValue valueConv p.2
  .ok (k, v)

theorem immutableExtend_eq {Q W : Type} (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (d : ImmutableDict K V) (p : Q × W) :
    immutableExtend keyConv valueConv d p = (newPair keyConv valueConv p).map (· :: d) := by
  unfold immutableExtend immutablePrepend newPair
  cases convertValue keyConv p.1 <;> cases convertValue valueConv p.2 <;> rfl

/-- `ImmutableDict` lookups return the most recent value for a key (`ImmutableDict` docstring,
`base/dict.jl:785-797`): the value of the first iterated pair whose key is `isequal` to the
query. `getindex` throws `KeyError` and both `get` methods return their default only when no
stored key matches. -/
def ImmutableDictLookupSemantics : Prop :=
  ∀ (K V Q : Type) (eqKey : K → Q → Bool) (d : ImmutableDict K V) (q : Q) (default : V)
    (fallback : Unit → V),
    immutableGetindex eqKey d q =
        (match ((immutableCollect d).find? (fun e => eqKey e.1 q)).map (·.2) with
          | some v => .ok v | none => .error .keyError) ∧
      immutableHasKey eqKey d q = ((immutableCollect d).find? (fun e => eqKey e.1 q)).isSome ∧
      immutableGet eqKey d q default =
        (((immutableCollect d).find? (fun e => eqKey e.1 q)).map (·.2)).getD default ∧
      immutableGetF eqKey d q fallback =
        (match ((immutableCollect d).find? (fun e => eqKey e.1 q)).map (·.2) with
          | some v => v | none => fallback ())

theorem ImmutableDictLookupSemantics_proven : ImmutableDictLookupSemantics := by
  intro K V Q eqKey d q default fallback
  simp only [immutableCollect_eq]
  induction d with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    by_cases h : eqKey k q = true
    · simp [immutableGetindex, immutableHasKey, immutableGet, immutableGetF, List.find?, h]
    · simp only [Bool.not_eq_true] at h
      simp only [immutableGetindex, immutableHasKey, immutableGet, immutableGetF, List.find?, h,
        ih1, ih2, ih3, ih4, Bool.false_or]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- `(key => value) in d` is true exactly when some stored pair has a key `isequal` to `key` and
a value for which `valcmp(value, stored)` is true (`ImmutableDict` docstring: "to see if this
particular combination is in the properties set"). -/
def ImmutableDictPairMembershipSemantics : Prop :=
  ∀ (K V Q W : Type) (eqKey : K → Q → Bool) (valcmp : W → V → Bool) (d : ImmutableDict K V)
    (pair : Q × W),
    immutableIn eqKey (fun w v => .ok (some (valcmp w v))) pair d =
      .ok (some ((immutableCollect d).any fun e => eqKey e.1 pair.1 && valcmp pair.2 e.2))

theorem ImmutableDictPairMembershipSemantics_proven : ImmutableDictPairMembershipSemantics := by
  intro K V Q W eqKey valcmp d pair
  rw [immutableCollect_eq]
  induction d with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    by_cases h : eqKey k pair.1 = true
    · by_cases hv : valcmp pair.2 v = true
      · simp [immutableIn, h, hv]
      · simp only [Bool.not_eq_true] at hv
        simp [immutableIn, h, hv, ih]
    · simp only [Bool.not_eq_true] at h
      simp [immutableIn, h, ih]

/-- Iteration shows every pair, duplicates included; `length` (`count(Returns(true), t)`) and
`isempty` agree with it and `empty(d, K, V)` has no pairs. -/
def ImmutableDictCollectionSemantics : Prop :=
  ∀ (K V : Type) (count : (K × V → Bool) → ImmutableDict K V → Nat), CountLaw count →
    ∀ d : ImmutableDict K V,
    immutableLength count d = (immutableCollect d).length ∧
    immutableIsEmpty d = (immutableCollect d).isEmpty ∧
    immutableCollect (immutableEmptyLike K V d) = []

theorem ImmutableDictCollectionSemantics_proven : ImmutableDictCollectionSemantics := by
  intro K V count hc d
  refine ⟨?_, ?_, ?_⟩
  · unfold immutableLength
    rw [hc, immutableCollect_eq]
    simp
  · rw [immutableCollect_eq]; rfl
  · rfl

/-- The constructors iterate from the most recently added pair to the least recently added one
(`ImmutableDict` docstring): `ImmutableDict{K,V}()` is empty, `ImmutableDict(KV)` holds `KV`, and
every added pair is converted to `K => V` by `new`, the first failing conversion propagating. -/
def ImmutableDictConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (d : ImmutableDict K V) (first : K × V) (pair : Q × W) (rest : List (Q × W)),
    immutableCollect (immutableEmpty K V) = [] ∧
    (immutableFromPair first).map immutableCollect = .ok [first] ∧
    (immutableSingleton keyConv valueConv pair.1 pair.2).map immutableCollect =
      (newPair keyConv valueConv pair).map (fun p => [p]) ∧
    (immutablePrepend keyConv valueConv d pair.1 pair.2).map immutableCollect =
      (newPair keyConv valueConv pair).map (fun p => p :: immutableCollect d) ∧
    (immutableExtend keyConv valueConv d pair).map immutableCollect =
      (newPair keyConv valueConv pair).map (fun p => p :: immutableCollect d) ∧
    (immutableExtendMany keyConv valueConv d rest).map immutableCollect =
      (rest.mapM (newPair keyConv valueConv)).map (fun ps => ps.reverse ++ immutableCollect d) ∧
    (immutableFromPairs keyConv valueConv first rest).map immutableCollect =
      (rest.mapM (newPair keyConv valueConv)).map (fun ps => ps.reverse ++ [first])

theorem immutableExtendMany_spec {Q W : Type} (keyConv : ValueConv Q K)
    (valueConv : ValueConv W V) (rest : List (Q × W)) : ∀ d : ImmutableDict K V,
    immutableExtendMany keyConv valueConv d rest =
      (rest.mapM (newPair keyConv valueConv)).map (fun ps => ps.reverse ++ d) := by
  induction rest with
  | nil => intro d; rfl
  | cons p rest ih =>
    intro d
    simp only [immutableExtendMany, immutableExtend_eq, List.mapM_cons]
    cases newPair keyConv valueConv p with
    | error e => rfl
    | ok x =>
      show immutableExtendMany keyConv valueConv (x :: d) rest = _
      rw [ih]
      cases rest.mapM (newPair keyConv valueConv) with
      | error e => rfl
      | ok xs => simp [Except.map, bind, Except.bind, pure, Except.pure]

theorem ImmutableDictConstructorSemantics_proven : ImmutableDictConstructorSemantics := by
  intro K V Q W keyConv valueConv d first pair rest
  have hext := immutableExtend_eq keyConv valueConv d pair
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have := immutableExtend_eq keyConv valueConv (immutableEmpty K V) pair
    unfold immutableSingleton
    unfold immutableExtend at this
    rw [this]
    cases newPair keyConv valueConv pair <;> rfl
  · unfold immutableExtend at hext
    rw [hext]
    cases newPair keyConv valueConv pair <;> simp [Except.map, immutableCollect_eq]
  · rw [hext]
    cases newPair keyConv valueConv pair <;> simp [Except.map, immutableCollect_eq]
  · rw [immutableExtendMany_spec]
    cases rest.mapM (newPair keyConv valueConv) <;> simp [Except.map, immutableCollect_eq]
  · show (immutableExtendMany keyConv valueConv [first] rest).map immutableCollect = _
    rw [immutableExtendMany_spec]
    cases rest.mapM (newPair keyConv valueConv) <;> simp [Except.map, immutableCollect_eq]

/-- After `setindex(d, value, key)` or `ImmutableDict(d, key => value)` returns `d'`, `d'[key]` is
the stored value (`setindex` docstring, `base/dict.jl:871-872`: the most recent value of the key
`key` set to `value`; `ImmutableDict` docstring: `getindex` returns the most recent value). -/
def ImmutableDictSetGet : Prop :=
  ∀ (K V Q W : Type) (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (eqKey : K → Q → Bool) (d d' : ImmutableDict K V) (value : W) (key : Q) (v : V),
    convertValue valueConv value = .ok v →
    (setindexImmutable keyConv valueConv d value key = .ok d' ∨
      immutableExtend keyConv valueConv d (key, value) = .ok d') →
    immutableGetindex eqKey d' key = .ok v

/-- With a value comparison returning `missing` (`none`), `(key => value) in d` for a stored key
`isequal` to `key` returns `missing`, like `in(::Pair, ::AbstractDict)` and three-valued `==`
(`base/operators.jl:126-127`). -/
def ImmutableDictInMissing : Prop :=
  ∀ (K V Q W : Type) (eqKey : K → Q → Bool) (d : ImmutableDict K V) (pair : Q × W),
    ((immutableCollect d).any fun e => eqKey e.1 pair.1) = true →
    immutableIn eqKey (fun _ _ => .ok none) pair d = .ok none

/-- Keys already of type `K`: `key isa K` holds, so no conversion happens. -/
def typedKey (eqKey : K → K → Bool) : KeyConv K K := ⟨some, .ok, eqKey⟩

/-- `Dict{K,V}(d)` of an `ImmutableDict` maps every key to `d[key]`, its most recent value
(`ImmutableDict` docstring; `Dict` docstring: the pairs of the argument). -/
def ImmutableDictToDict : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (d : ImmutableDict K V) (h : DictState K V),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    dictFromIterator hash eqKey tablesz maxValues cld (typedKey eqKey) (fieldConv V) true
      (immutableCollect d) = .ok h →
    ∀ (key : K) (default : V), JuliaLean.base.dict.get hash eqKey h key default =
      .ok (immutableGet eqKey d key default)

/-! ## `PersistentDict` -/

/-- The pairs `HAMT.iterate(t, state)` visits, with `fuel` steps. -/
def trieCollect {Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S) (t : H) :
    Nat → Option S → List (K × V)
  | 0, _ => []
  | fuel + 1, state =>
    match ops.iterate t state with
    | none => []
    | some (pair, next) => pair :: trieCollect ops t fuel (some next)

/-- Laws of the `HAMT` operations of `base/hamt.jl` (not modelled), for keys and values of types
`K` and `V`, in terms of the stored pairs `abs t` of a valid trie `t`. Keys are compared with
`===` (`eqKey`) and hashed with `objectid` (`hash`): `PersistentDict` "behaves like an IdDict"
(`base/dict.jl:946`).
- `HAMT{K,V}()` is empty and `HAMT{K,V}(k => v)` holds `k => v` (`hamt.jl:66-80`);
- `islevel_empty(t)` holds exactly for a trie without pairs;
- `path(t, HashState(k), copy)` ends at a present leaf (`found && present`) exactly when a stored
  key is `===` to `k`, and that leaf holds its value (`hamt.jl:158-187`); the copied `top` holds
  the pairs of `t`;
- `insert!` on the copied path stores `k => v` in `top`, and throws ("Perfect hash collision")
  exactly when a stored key that is not `===` to `k` has the same `objectid` (`hamt.jl:192-240`);
- `deleteat!(trie.data, i)` and `unset!(trie, bi)` at a present leaf remove `k`;
- `iterate` visits every pair once, and `length` and `isempty` count the pairs. -/
structure HamtLaws {H HS S : Type} (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)) : Prop where
  keys : KeyLaws hash eqKey
  distinct : ∀ t, valid t → Distinct eqKey (abs t)
  empty_valid : valid (ops.empty ())
  empty_abs : abs (ops.empty ()) = []
  singleton : ∀ p : K × V, ∃ t, ops.singleton p = .ok t ∧ valid t ∧ abs t = [p]
  levelEmpty : ∀ t, valid t → (ops.isLevelEmpty t = true ↔ abs t = [])
  found : ∀ t (k : K) (copy : Bool), valid t →
    ((ops.path t (ops.hashState k) copy).found && (ops.path t (ops.hashState k) copy).present) =
      (rfind eqKey (abs t) k).isSome
  leaf : ∀ t (k : K), valid t →
    ((ops.path t (ops.hashState k) false).found &&
      (ops.path t (ops.hashState k) false).present) = true →
    ops.leafValue (ops.path t (ops.hashState k) false).trie
      (ops.path t (ops.hashState k) false).index = rlookup eqKey (abs t) k
  copy : ∀ t (k : K), valid t → valid (ops.path t (ops.hashState k) true).top ∧
    List.Perm (abs (ops.path t (ops.hashState k) true).top) (abs t)
  insert : ∀ t (k : K) (v : V) t', valid t →
    ops.insert (ops.path t (ops.hashState k) true).top (ops.path t (ops.hashState k) true).trie
      (ops.path t (ops.hashState k) true).found (ops.path t (ops.hashState k) true).present
      (ops.path t (ops.hashState k) true).index (ops.path t (ops.hashState k) true).bitmapIndex
      (ops.path t (ops.hashState k) true).state v = .ok t' →
    valid t' ∧ List.Perm (abs t') (rset eqKey (abs t) k v)
  insert_ok : ∀ t (k : K) (v : V), valid t →
    ((∃ t', ops.insert (ops.path t (ops.hashState k) true).top
      (ops.path t (ops.hashState k) true).trie (ops.path t (ops.hashState k) true).found
      (ops.path t (ops.hashState k) true).present (ops.path t (ops.hashState k) true).index
      (ops.path t (ops.hashState k) true).bitmapIndex (ops.path t (ops.hashState k) true).state
      v = .ok t') ↔
      ∀ e ∈ abs t, hash e.1 = hash k → eqKey e.1 k = true)
  delete : ∀ t (k : K), valid t →
    ((ops.path t (ops.hashState k) true).found && (ops.path t (ops.hashState k) true).present) =
      true →
    valid (ops.unset (ops.deleteAt (ops.path t (ops.hashState k) true).top
      (ops.path t (ops.hashState k) true).trie (ops.path t (ops.hashState k) true).index)
      (ops.path t (ops.hashState k) true).trie (ops.path t (ops.hashState k) true).bitmapIndex) ∧
    List.Perm (abs (ops.unset (ops.deleteAt (ops.path t (ops.hashState k) true).top
      (ops.path t (ops.hashState k) true).trie (ops.path t (ops.hashState k) true).index)
      (ops.path t (ops.hashState k) true).trie (ops.path t (ops.hashState k) true).bitmapIndex))
      (rdel eqKey (abs t) k)
  iterate : ∀ t, valid t → ∀ fuel, (abs t).length < fuel →
    List.Perm (trieCollect ops t fuel none) (abs t)
  length : ∀ t, valid t → ops.length t = (abs t).length
  isEmpty : ∀ t, valid t → ops.isEmpty t = (abs t).isEmpty

/-- `PersistentDict` lookups (`KeyValue.get`, `haskey`, `getindex`, both `get`s and
`KeyValue.get(default, d, key)`) agree with the stored pairs: a key `===` to a stored key finds its
value, any other key is absent (`KeyError` or the default). -/
def PersistentLookupSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops hash eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K) (default : V) (fallback : Unit → DictResult V),
    valid d.trie →
    persistentKeyGet ops d key = rlookup eqKey (abs d.trie) key ∧
    persistentGetindex ops d key =
      (match rlookup eqKey (abs d.trie) key with | some v => .ok v | none => .error .keyError) ∧
    persistentHasKey ops d key = (rlookup eqKey (abs d.trie) key).isSome ∧
    persistentGet ops d key default = (rlookup eqKey (abs d.trie) key).getD default ∧
    persistentGetDefault ops d key fallback =
      (match rlookup eqKey (abs d.trie) key with | some v => .ok v | none => fallback ()) ∧
    persistentGetTypedDefault ops d key fallback =
      (match rlookup eqKey (abs d.trie) key with | some v => .ok v | none => fallback ())

/-- `KeyValue.get` reads the leaf `trie.data[i]` (`@inbounds`) only at the end of a path that
`HAMT.path` reports found and present, and only for a stored key, whose value it returns. -/
def PersistentPathSafe : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops hash eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K) (value : V), valid d.trie →
    persistentKeyGet ops d key = some value →
    ops.isLevelEmpty d.trie = false ∧ (ops.path d.trie (ops.hashState key) false).found = true ∧
    (ops.path d.trie (ops.hashState key) false).present = true ∧
    ops.leafValue (ops.path d.trie (ops.hashState key) false).trie
      (ops.path d.trie (ops.hashState key) false).index = some value ∧
    rlookup eqKey (abs d.trie) key = some value

/-- A successful `KeyValue.set(d, key, val)` returns a dictionary holding `key => val` and every
other pair of `d` (`PersistentDict` docstring: each operation returns a new dictionary); it
succeeds exactly when no stored key other than `key` has the same `objectid`.
`PersistentDict(d, key, val)` and both `PersistentDict(d, key => val)` first convert the
arguments. -/
def PersistentSetSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops hash eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K) (value : V), valid d.trie →
    (∀ d', (persistentSet ops d key value = .ok d' ∨ persistentSetTyped ops d key value = .ok d') →
      valid d'.trie ∧ List.Perm (abs d'.trie) (rset eqKey (abs d.trie) key value)) ∧
    ((∃ d', persistentSetTyped ops d key value = .ok d') ↔
      ∀ e ∈ abs d.trie, hash e.1 = hash key → eqKey e.1 key = true) ∧
    ∀ (Q W : Type) (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (q : Q) (w : W) d',
      (persistentExtend ops keyConv valueConv d q w = .ok d' ∨
        persistentExtendPair ops keyConv valueConv d (q, w) = .ok d' ∨
        persistentTypedExtendPair ops keyConv valueConv d (q, w) = .ok d') →
      ∃ k v, keyConv.convert q = .ok k ∧ valueConv.convert w = .ok v ∧ valid d'.trie ∧
        List.Perm (abs d'.trie) (rset eqKey (abs d.trie) k v)

/-- `KeyValue.set(d, key::K, val::V)` is annotated `:nothrow` (`base/dict.jl:911-912`): it returns
for every key and value. -/
def PersistentSetNothrow : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops hash eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K) (value : V), valid d.trie →
    ∃ d', persistentSetTyped ops d key value = .ok d'

/-- `(key => val) in d` is `false` for an absent key and otherwise `valcmp(val, stored)`. -/
def PersistentPairMembershipSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops hash eqKey valid abs →
    ∀ (d : PersistentDict K V H) (pair : K × V) (valcmp : V → V → DictResult Bool), valid d.trie →
    persistentIn ops valcmp d pair =
      (match rlookup eqKey (abs d.trie) pair.1 with
        | none => .ok false
        | some stored => valcmp pair.2 stored)

/-- `delete(d, key)` and both `KeyValue.set(d, key)` return a dictionary without `key` that keeps
every other pair of `d` (`PersistentDict` docstring example `Base.delete(dict, :a)`). -/
def PersistentDeleteSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops hash eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K), valid d.trie →
    (valid (persistentDelete ops d key).trie ∧
      List.Perm (abs (persistentDelete ops d key).trie) (rdel eqKey (abs d.trie) key)) ∧
    (valid (persistentSetDelete ops d key).trie ∧
      List.Perm (abs (persistentSetDelete ops d key).trie) (rdel eqKey (abs d.trie) key)) ∧
    (valid (persistentSetTypedDelete ops d key).trie ∧
      List.Perm (abs (persistentSetTypedDelete ops d key).trie) (rdel eqKey (abs d.trie) key))

/-- The pairs `iterate(d, state)` visits from `state`, with `fuel` steps. -/
def persistentCollectFuel {Q W H HS S : Type} (ops : PersistentOps K V Q W H HS S)
    (d : PersistentDict K V H) : Nat → Option S → List (K × V)
  | 0, _ => []
  | fuel + 1, state =>
    match persistentIterate ops d state with
    | none => []
    | some (pair, next) => pair :: persistentCollectFuel ops d fuel (some next)

/-- Iteration visits every stored pair once; `length` and `isempty` count them, `eltype` is the
pair type and `empty(d, K, V)` has no pairs. -/
def PersistentCollectionSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops hash eqKey valid abs →
    ∀ d : PersistentDict K V H, valid d.trie →
    List.Perm (persistentCollectFuel ops d ((abs d.trie).length + 1) none) (abs d.trie) ∧
    persistentLength ops d = (abs d.trie).length ∧
    persistentIsEmpty ops d = (abs d.trie).isEmpty ∧
    persistentEltype K V = (K × V) ∧
    valid (persistentEmptyLike ops d).trie ∧ abs (persistentEmptyLike ops d).trie = []

/-- `PersistentDict{K,V}()` is empty; the one-pair constructors hold their pair; the multi-pair
constructors hold the converted pairs, a later `===` key replacing an earlier one, and succeed
whenever the conversions do and no two keys that are not `===` share an `objectid`.
`HAMT{K,V}(kv::Pair)` converts `kv` to `Pair{K,V}` (`hamt.jl:82`). -/
def PersistentConstructorSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S) (hash : K → JInt .u64)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops hash eqKey valid abs →
    (valid (persistentEmptyConstructor ops).trie ∧ abs (persistentEmptyConstructor ops).trie = []) ∧
    (∀ (key : K) (value : V), ∃ d, persistentSingleton ops key value = .ok d ∧
      persistentTypedPair ops (key, value) = .ok d ∧ persistentPair ops (key, value) = .ok d ∧
      valid d.trie ∧ abs d.trie = [(key, value)]) ∧
    ∀ (Q W HS' S' : Type) (opsPair : PersistentOps K V Q W H HS' S') (keyConv : KeyConv Q K)
      (valueConv : ValueConv W V),
      (∀ q w, opsPair.singleton (q, w) =
        (do let k ← keyConv.convert q; let v ← valueConv.convert w; ops.singleton (k, v))) →
      ∀ (first : K × V) (q : Q) (w : W) (rest : List (Q × W)),
      let conv := fun (p : Q × W) => (do
        let k ← keyConv.convert p.1; let v ← valueConv.convert p.2; .ok (k, v) : DictResult (K × V))
      (∀ d, persistentPairs ops keyConv valueConv first rest = .ok d →
        ∃ ps, rest.mapM conv = .ok ps ∧ valid d.trie ∧
          List.Perm (abs d.trie) (ps.foldl (fun m p => rset eqKey m p.1 p.2) [first])) ∧
      (∀ d, persistentTypedPairs opsPair ops keyConv valueConv q w rest = .ok d →
        ∃ p ps, conv (q, w) = .ok p ∧ rest.mapM conv = .ok ps ∧ valid d.trie ∧
          List.Perm (abs d.trie) (ps.foldl (fun m p => rset eqKey m p.1 p.2) [p])) ∧
      ((∀ a b, hash a = hash b → eqKey a b = true) →
        (∀ ps, rest.mapM conv = .ok ps → ∃ d, persistentPairs ops keyConv valueConv first rest = .ok d) ∧
        (∀ p ps, conv (q, w) = .ok p → rest.mapM conv = .ok ps →
          ∃ d, persistentTypedPairs opsPair ops keyConv valueConv q w rest = .ok d))

section PersistentProofs
variable {H HS S : Type} {ops : PersistentOps K V K V H HS S} {hash : K → JInt .u64}
  {eqKey : K → K → Bool} {valid : H → Prop} {abs : H → List (K × V)}

theorem HamtLaws.keyGet (hl : HamtLaws ops hash eqKey valid abs) (d : PersistentDict K V H)
    (key : K) (hv : valid d.trie) : persistentKeyGet ops d key = rlookup eqKey (abs d.trie) key := by
  have hfound := hl.found d.trie key false hv
  have hleaf := hl.leaf d.trie key hv
  have hle := hl.levelEmpty d.trie hv
  unfold persistentKeyGet
  dsimp only [Id.run]
  split
  · rename_i h1
    rw [hle.1 h1]; rfl
  · split
    · rename_i _ h2; exact hleaf h2
    · rename_i _ h2
      unfold rlookup
      cases hr : rfind eqKey (abs d.trie) key with
      | none => rfl
      | some e => rw [hr] at hfound; exact absurd hfound h2

theorem persistentSetTyped_eq (ops : PersistentOps K V K V H HS S) (d : PersistentDict K V H)
    (key : K) (value : V) :
    persistentSetTyped ops d key value =
      (ops.insert (ops.path d.trie (ops.hashState key) true).top
        (ops.path d.trie (ops.hashState key) true).trie (ops.path d.trie (ops.hashState key) true).found
        (ops.path d.trie (ops.hashState key) true).present
        (ops.path d.trie (ops.hashState key) true).index
        (ops.path d.trie (ops.hashState key) true).bitmapIndex
        (ops.path d.trie (ops.hashState key) true).state value).map PersistentDict.mk := by
  unfold persistentSetTyped persistentInsert
  dsimp only
  cases ops.insert (ops.path d.trie (ops.hashState key) true).top
    (ops.path d.trie (ops.hashState key) true).trie (ops.path d.trie (ops.hashState key) true).found
    (ops.path d.trie (ops.hashState key) true).present
    (ops.path d.trie (ops.hashState key) true).index
    (ops.path d.trie (ops.hashState key) true).bitmapIndex
    (ops.path d.trie (ops.hashState key) true).state value <;> rfl

theorem HamtLaws.setTyped (hl : HamtLaws ops hash eqKey valid abs) (d : PersistentDict K V H)
    (key : K) (value : V) (hv : valid d.trie) :
    (∀ d', persistentSetTyped ops d key value = .ok d' → valid d'.trie ∧
      List.Perm (abs d'.trie) (rset eqKey (abs d.trie) key value)) ∧
    ((∃ d', persistentSetTyped ops d key value = .ok d') ↔
      ∀ e ∈ abs d.trie, hash e.1 = hash key → eqKey e.1 key = true) := by
  rw [persistentSetTyped_eq]
  have hins := hl.insert d.trie key value
  have hok := hl.insert_ok d.trie key value hv
  revert hins hok
  cases ops.insert (ops.path d.trie (ops.hashState key) true).top
    (ops.path d.trie (ops.hashState key) true).trie (ops.path d.trie (ops.hashState key) true).found
    (ops.path d.trie (ops.hashState key) true).present
    (ops.path d.trie (ops.hashState key) true).index
    (ops.path d.trie (ops.hashState key) true).bitmapIndex
    (ops.path d.trie (ops.hashState key) true).state value with
  | error e =>
    intro _ hok
    refine ⟨fun d' hd => (by cases hd), ?_⟩
    rw [← hok]
    exact ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | ok t =>
    intro hins hok
    refine ⟨fun d' hd => ?_, ?_⟩
    · cases hd; exact hins t hv rfl
    · rw [← hok]
      exact ⟨fun _ => ⟨t, rfl⟩, fun _ => ⟨⟨t⟩, rfl⟩⟩

theorem persistentExtend_ok {Q W : Type} {keyConv : KeyConv Q K} {valueConv : ValueConv W V}
    {d d' : PersistentDict K V H} {q : Q} {w : W}
    (hd : persistentExtend ops keyConv valueConv d q w = .ok d') :
    ∃ k v, keyConv.convert q = .ok k ∧ valueConv.convert w = .ok v ∧
      persistentSetTyped ops d k v = .ok d' := by
  unfold persistentExtend at hd
  cases hk : keyConv.convert q with
  | error e => rw [hk] at hd; cases hd
  | ok k =>
    rw [hk] at hd
    cases hw : valueConv.convert w with
    | error e => rw [hw] at hd; cases hd
    | ok v => rw [hw] at hd; exact ⟨k, v, rfl, rfl, hd⟩

theorem PersistentLookupSemantics_proven : PersistentLookupSemantics := by
  intro K V H HS S ops hash eqKey valid abs hl d key default fallback hv
  have hk := hl.keyGet d key hv
  refine ⟨hk, ?_, ?_, ?_, ?_, ?_⟩
  · unfold persistentGetindex; rw [hk] <;> cases rlookup eqKey (abs d.trie) key <;> rfl
  · unfold persistentHasKey; rw [hk]
  · unfold persistentGet; rw [hk]
  · unfold persistentGetDefault; rw [hk]
    cases rlookup eqKey (abs d.trie) key <;> rfl
  · unfold persistentGetTypedDefault; rw [hk]
    cases rlookup eqKey (abs d.trie) key <;> rfl

theorem PersistentPathSafe_proven : PersistentPathSafe := by
  intro K V H HS S ops hash eqKey valid abs hl d key value hv hget
  rw [hl.keyGet d key hv] at hget
  have hfind : (rfind eqKey (abs d.trie) key).isSome = true := by
    unfold rlookup at hget
    cases hr : rfind eqKey (abs d.trie) key with
    | none => rw [hr] at hget; cases hget
    | some e => rfl
  have hf := hl.found d.trie key false hv
  rw [hfind] at hf
  have hle : ops.isLevelEmpty d.trie = false := by
    cases h : ops.isLevelEmpty d.trie with
    | false => rfl
    | true => rw [(hl.levelEmpty d.trie hv).1 h] at hget; cases hget
  have hfp := Bool.and_eq_true_iff.1 hf
  exact ⟨hle, hfp.1, hfp.2, (hl.leaf d.trie key hv hf).trans hget, hget⟩

theorem PersistentSetSemantics_proven : PersistentSetSemantics := by
  intro K V H HS S ops hash eqKey valid abs hl d key value hv
  refine ⟨fun d' hd => ?_, (hl.setTyped d key value hv).2, ?_⟩
  · have e : persistentSet ops d key value = persistentSetTyped ops d key value := rfl
    rcases hd with hd | hd
    · rw [e] at hd; exact (hl.setTyped d key value hv).1 d' hd
    · exact (hl.setTyped d key value hv).1 d' hd
  · intro Q W keyConv valueConv q w d' hd
    have hd' : persistentExtend ops keyConv valueConv d q w = .ok d' := by
      rcases hd with hd | hd | hd <;> exact hd
    obtain ⟨k, v, hk, hw, hs⟩ := persistentExtend_ok hd'
    obtain ⟨h1, h2⟩ := (hl.setTyped d k v hv).1 d' hs
    exact ⟨k, v, hk, hw, h1, h2⟩

theorem PersistentPairMembershipSemantics_proven : PersistentPairMembershipSemantics := by
  intro K V H HS S ops hash eqKey valid abs hl d pair valcmp hv
  unfold persistentIn
  rw [hl.keyGet d pair.1 hv] <;> cases rlookup eqKey (abs d.trie) pair.1 <;> rfl


theorem HamtLaws.deleteKey (hl : HamtLaws ops hash eqKey valid abs) (d : PersistentDict K V H)
    (key : K) (hv : valid d.trie) :
    valid (persistentDeleteKey ops d key).trie ∧
      List.Perm (abs (persistentDeleteKey ops d key).trie) (rdel eqKey (abs d.trie) key) := by
  have e : (persistentDeleteKey ops d key).trie =
      if ((ops.path d.trie (ops.hashState key) true).found &&
        (ops.path d.trie (ops.hashState key) true).present) = true then
        ops.unset (ops.deleteAt (ops.path d.trie (ops.hashState key) true).top
          (ops.path d.trie (ops.hashState key) true).trie
          (ops.path d.trie (ops.hashState key) true).index)
          (ops.path d.trie (ops.hashState key) true).trie
          (ops.path d.trie (ops.hashState key) true).bitmapIndex
      else (ops.path d.trie (ops.hashState key) true).top := rfl
  rw [e]
  split
  · rename_i h; exact hl.delete d.trie key hv h
  · rename_i h
    have hf := hl.found d.trie key true hv
    have hnone : rfind eqKey (abs d.trie) key = none := by
      cases hr : rfind eqKey (abs d.trie) key with
      | none => rfl
      | some e => rw [hr] at hf; exact absurd hf h
    rw [rdel_absent (rfind_eq_none_iff.1 hnone)]
    exact hl.copy d.trie key hv

theorem PersistentDeleteSemantics_proven : PersistentDeleteSemantics := by
  intro K V H HS S ops hash eqKey valid abs hl d key hv
  exact ⟨hl.deleteKey d key hv, hl.deleteKey d key hv, hl.deleteKey d key hv⟩

theorem persistentCollectFuel_eq {Q W : Type} (ops : PersistentOps K V Q W H HS S)
    (d : PersistentDict K V H) : ∀ n s, persistentCollectFuel ops d n s = trieCollect ops d.trie n s
  | 0, _ => rfl
  | n + 1, s => by
    simp only [persistentCollectFuel, trieCollect, persistentIterate]
    cases ops.iterate d.trie s with
    | none => rfl
    | some p => simp only [persistentCollectFuel_eq ops d n]

theorem PersistentCollectionSemantics_proven : PersistentCollectionSemantics := by
  intro K V H HS S ops hash eqKey valid abs hl d hv
  refine ⟨?_, hl.length d.trie hv, hl.isEmpty d.trie hv, rfl, hl.empty_valid, hl.empty_abs⟩
  rw [persistentCollectFuel_eq]
  exact hl.iterate d.trie hv _ (Nat.lt_succ_self _)

/-- One `PersistentDict(d, key, value)` per pair, from a valid dictionary whose pairs are a
permutation of `m0`. -/
theorem HamtLaws.extendMany (hl : HamtLaws ops hash eqKey valid abs) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) :
    ∀ (rest : List (Q × W)) (d0 d : PersistentDict K V H) (m0 : List (K × V)), valid d0.trie →
      List.Perm (abs d0.trie) m0 → persistentExtendMany ops keyConv valueConv d0 rest = .ok d →
      ∃ ps, rest.mapM (fun (p : Q × W) => (do
          let k ← keyConv.convert p.1; let v ← valueConv.convert p.2; .ok (k, v) :
          DictResult (K × V))) = .ok ps ∧ valid d.trie ∧
        List.Perm (abs d.trie) (ps.foldl (fun m p => rset eqKey m p.1 p.2) m0)
  | [], d0, d, m0, hv, hp, hd => by
    cases hd; exact ⟨[], rfl, hv, hp⟩
  | (q, w) :: rest, d0, d, m0, hv, hp, hd => by
    unfold persistentExtendMany at hd
    cases he : persistentExtend ops keyConv valueConv d0 q w with
    | error e => rw [he] at hd; cases hd
    | ok d1 =>
      rw [he] at hd
      obtain ⟨k, v, hk, hw, hs⟩ := persistentExtend_ok he
      obtain ⟨hv1, hp1⟩ := (hl.setTyped d0 k v hv).1 d1 hs
      obtain ⟨ps, hps, hvd, hpd⟩ := hl.extendMany keyConv valueConv rest d1 d (rset eqKey m0 k v)
        hv1 (hp1.trans (rset_perm hp k v)) hd
      refine ⟨(k, v) :: ps, ?_, hvd, hpd⟩
      simp only [List.mapM_cons, hk, hw, hps, except_ok_bind]
      rfl

theorem HamtLaws.extendMany_ok (hl : HamtLaws ops hash eqKey valid abs) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (hinj : ∀ a b, hash a = hash b → eqKey a b = true) :
    ∀ (rest : List (Q × W)) (d0 : PersistentDict K V H) (ps : List (K × V)), valid d0.trie →
      rest.mapM (fun (p : Q × W) => (do
          let k ← keyConv.convert p.1; let v ← valueConv.convert p.2; .ok (k, v) :
          DictResult (K × V))) = .ok ps →
      ∃ d, persistentExtendMany ops keyConv valueConv d0 rest = .ok d
  | [], d0, _, _, _ => ⟨d0, rfl⟩
  | (q, w) :: rest, d0, ps, hv, hps => by
    simp only [List.mapM_cons] at hps
    cases hk : keyConv.convert q with
    | error e => rw [hk] at hps; cases hps
    | ok k =>
      cases hw : valueConv.convert w with
      | error e => rw [hk, hw] at hps; cases hps
      | ok v =>
        rw [hk, hw] at hps
        simp only [except_ok_bind] at hps
        cases hr : rest.mapM (fun (p : Q × W) => (do
            let k ← keyConv.convert p.1; let v ← valueConv.convert p.2; .ok (k, v) :
            DictResult (K × V))) with
        | error e => rw [hr] at hps; cases hps
        | ok ps' =>
          obtain ⟨d1, hd1⟩ := (hl.setTyped d0 k v hv).2.2 (fun e _ he => hinj e.1 k he)
          have hv1 := ((hl.setTyped d0 k v hv).1 d1 hd1).1
          obtain ⟨d, hd⟩ := hl.extendMany_ok keyConv valueConv hinj rest d1 ps' hv1 hr
          refine ⟨d, ?_⟩
          unfold persistentExtendMany
          have he : persistentExtend ops keyConv valueConv d0 q w = .ok d1 := by
            unfold persistentExtend; rw [hk, hw]; exact hd1
          rw [he]
          exact hd

theorem PersistentConstructorSemantics_proven : PersistentConstructorSemantics := by
  intro K V H HS S ops hash eqKey valid abs hl
  refine ⟨⟨hl.empty_valid, hl.empty_abs⟩, fun key value => ?_, ?_⟩
  · obtain ⟨t, ht, hv, ha⟩ := hl.singleton (key, value)
    have e : persistentSingleton ops key value = .ok ⟨t⟩ := by
      unfold persistentSingleton; rw [ht]; rfl
    exact ⟨⟨t⟩, e, e, e, hv, ha⟩
  intro Q W HS' S' opsPair keyConv valueConv hsing first q w rest
  dsimp only
  obtain ⟨t1, ht1, hv1, ha1⟩ := hl.singleton first
  have hpair : persistentPair ops first = .ok ⟨t1⟩ := by
    unfold persistentPair persistentSingleton; rw [ht1]; rfl
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun hinj => ⟨fun ps hps => ?_, fun p ps hp hps => ?_⟩⟩
  · unfold persistentPairs at hd
    rw [hpair] at hd
    exact hl.extendMany keyConv valueConv rest ⟨t1⟩ d [first] hv1 (by rw [ha1]) hd
  · unfold persistentTypedPairs persistentTypedPair persistentSingleton at hd
    rw [hsing] at hd
    cases hk : keyConv.convert q with
    | error e => rw [hk] at hd; cases hd
    | ok k =>
      cases hw : valueConv.convert w with
      | error e => rw [hk, hw] at hd; cases hd
      | ok v =>
        rw [hk, hw] at hd
        obtain ⟨t, ht, hv, ha⟩ := hl.singleton (k, v)
        simp only [except_ok_bind, ht] at hd
        obtain ⟨ps, hps, hvd, hpd⟩ := hl.extendMany keyConv valueConv rest ⟨t⟩ d [(k, v)] hv
          (by rw [ha]) hd
        refine ⟨(k, v), ps, ?_, hps, hvd, hpd⟩
        simp only [hk, hw, except_ok_bind]
  · obtain ⟨d, hd⟩ := hl.extendMany_ok keyConv valueConv hinj rest ⟨t1⟩ ps hv1 hps
    refine ⟨d, ?_⟩
    unfold persistentPairs
    rw [hpair]
    exact hd
  · have hp' := hp

    cases hk : keyConv.convert q with
    | error e => rw [hk] at hp'; cases hp'
    | ok k =>
      cases hw : valueConv.convert w with
      | error e => rw [hk, hw] at hp'; cases hp'
      | ok v =>
        obtain ⟨t, ht, hv, -⟩ := hl.singleton (k, v)
        obtain ⟨d, hd⟩ := hl.extendMany_ok keyConv valueConv hinj rest ⟨t⟩ ps hv hps
        refine ⟨d, ?_⟩
        unfold persistentTypedPairs persistentTypedPair persistentSingleton
        rw [hsing, hk, hw]
        simp only [except_ok_bind, ht]
        exact hd

end PersistentProofs

/-! ## `_similar_for` -/

/-- `_similar_for(c, Pair{K,V}, ...)` returns `empty(c, K, V)`, an empty dictionary of the kind of
`c` (`Dict`, `ImmutableDict` or `PersistentDict`); any other element type throws `ArgumentError`
("similar requires an element type of Pair"). -/
def DictSimilarSemantics : Prop :=
  ∀ (K V C D : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (c : C),
    DictRep hash eqKey (similarForPairs (emptyDict K V) c) [] ∧
    (∀ d : ImmutableDict K V, immutableCollect (similarForPairs (immutableEmptyLike K V) d) = []) ∧
    (∀ (H HS S : Type) (ops : PersistentOps K V K V H HS S) (valid : H → Prop)
      (abs : H → List (K × V)), HamtLaws ops hash eqKey valid abs → ∀ d : PersistentDict K V H,
      valid (similarForPairs (persistentEmptyLike ops) d).trie ∧
        abs (similarForPairs (persistentEmptyLike ops) d).trie = []) ∧
    similarForOther (D := D) c = .error .argumentError

theorem DictSimilarSemantics_proven : DictSimilarSemantics := by
  intro K V C D hash eqKey c
  exact ⟨dictEmpty_rep hash eqKey, fun _ => rfl,
    fun _ _ _ ops valid abs hl _ => ⟨hl.empty_valid, hl.empty_abs⟩, rfl⟩

/-! ## `mergewith!` and `reduce(merge, items)` -/

/-- `mergewith!(combine, d1, d2)` (docstring `base/abstractdict.jl`): for each pair `k => v` of
`d2` in iteration order, a stored key `isequal` to `k` gets `combine(old, v)`; any other `k` is
added like `setindex!` (converted, `KeyTypeError` when the conversion is not `isequal`). -/
def refMergeStep {Q W : Type} (eqKey : K → K → Bool) (matchQ : Q → K → Bool)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (combine : V → W → DictResult V)
    (m : List (K × V)) (p : Q × W) : DictResult (List (K × V)) :=
  match rfind matchQ m p.1 with
  | some e => do
    let v ← combine e.2 p.2
    .ok (rset eqKey m e.1 v)
  | none => refStep eqKey keyConv valueConv m p

/-- `mergewith!(combine, d1, d2)` merges the pairs of `d2` into `d1` in iteration order, combining
values of keys `isequal` to stored ones with `combine(old, new)`, and propagates the first error
(`mergewith!` docstring, `base/abstractdict.jl`). -/
def DictMergewithSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (tablesz : Nat → Nat) (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (combine : V → W → DictResult V)
    (hasLength : Bool) (h : DictState K V) (m : List (K × V)) (d2 : List (Q × W)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → TableszLaw tablesz →
    MaxValuesLaw eqKey maxValues → CldLaw cld →
    (∀ q k, keyConv.convert q = .ok k → keyConv.isequal q k = true → ∀ k', matchQ q k' = eqKey k k') →
    (∀ q k, keyConv.isa q = some k → ∀ k', matchQ q k' = eqKey k k') →
    DictRep hash eqKey h m → m.length + d2.length ≤ 2 ^ 53 →
    match d2.foldlM (refMergeStep eqKey matchQ keyConv valueConv combine) m with
    | .ok m' => ∃ h', mergewithBang hash hashQ matchQ tablesz maxValues cld keyConv valueConv
        combine hasLength h d2 = .ok h' ∧ DictRep hash eqKey h' m'
    | .error e => mergewithBang hash hashQ matchQ tablesz maxValues cld keyConv valueConv
        combine hasLength h d2 = .error e

/-- `reduce(merge, items)` (`merge` docstring, `base/abstractdict.jl`) returns a `Dict` whose key
and value types promote those of `items` and whose pairs are those of the items merged from left to
right, a later `isequal` key replacing an earlier one; no items throws `ArgumentError`
("reducing over an empty collection"). `mapreduce` and `reduce(merge!, items; init)` come from
other files: `mapreduce(f, op, items)` is the left fold of `op` over `f` of the items and throws
for none, and `reduce(merge!, items; init)` applies `merge!(d, item)` (`sizehint!` then
`d[k] = v` for every pair) item by item. -/
def DictReduceMergeSemantics : Prop :=
  ∀ (D : Type) (keytype valtype : D → Type) (promoteType : Type → Type → Type)
    (mapreduce : (D → Type) → (Type → Type → Type) → List D → DictResult Type)
    (mergeItems : {K V : Type} → List D → DictState K V → DictResult (DictState K V)),
    (∀ f op, mapreduce f op [] = .error .argumentError) →
    (∀ f op x xs, mapreduce f op (x :: xs) = .ok (xs.foldl (fun acc y => op acc (f y)) (f x))) →
    reduceMerge keytype valtype promoteType mapreduce mergeItems [] = .error .argumentError ∧
    ∀ (x : D) (xs : List D) (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
      (tablesz : Nat → Nat) (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
      (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pairsOf : D → List (Q × W)),
      xs.foldl (fun acc y => promoteType acc (keytype y)) (keytype x) = K →
      xs.foldl (fun acc y => promoteType acc (valtype y)) (valtype x) = V →
      KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
      ((x :: xs).map (fun y => (pairsOf y).length)).sum ≤ 2 ^ 53 →
      (∀ h0 : DictState K V, mergeItems (x :: xs) h0 = (x :: xs).foldlM (fun h y => do
        let h ← sizehint hash tablesz maxValues cld h
          (JInt.lit .i64 (Int.ofNat (h.count + (pairsOf y).length))) false
        (pairsOf y).foldlM (fun h p => setindexConv hash eqKey tablesz keyConv valueConv h p.2 p.1) h)
        h0) →
      match refBuild eqKey keyConv valueConv ((x :: xs).flatMap pairsOf) with
      | .ok m => ∃ h, reduceMerge keytype valtype promoteType mapreduce mergeItems (x :: xs) =
          .ok ⟨K, V, h⟩ ∧ DictRep hash eqKey h m
      | .error e => reduceMerge keytype valtype promoteType mapreduce mergeItems (x :: xs) =
          .error e

section Merge
variable {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat}

/-- `_setindex!(d1, v, k, -i, sh)` at the free slot the probe of a query `q` returned, for the
converted key `k` that `q` is `isequal` to. -/
theorem mergeAbsent (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {Q : Type}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ)
    {t : DictState K V} (hi : Inv hash eqKey t) (hc : t.count < 2 ^ 54) {q : Q} {j : Nat}
    (hj : InsertSlot t (home hashQ t.size q) j) (habs : ∀ e ∈ tlist t, matchQ q e.1 = false)
    (k : K) (hk : ∀ k', matchQ q k' = eqKey k k') (v : V) :
    ∃ t', setindexAt hash tablesz t v k j (shorthash7 (hashQ q)) = .ok ((), t') ∧
      Inv hash eqKey t' ∧ List.Perm (tlist t') ((k, v) :: tlist t) ∧ t'.count = t.count + 1 := by
  have hh : hashQ q = hash k := hq.hash_eq q k (by rw [hk]; exact hl.refl k)
  have hhome : home hashQ t.size q = home hash t.size k := by
    unfold home hashindex; rw [hh]
  rw [hhome] at hj
  rw [hh]
  obtain ⟨t', h', hi', hp', hc', -⟩ :=
    setindexAt_spec hl htz hi hc hj (fun e he => by rw [← hk]; exact habs e he) (v := v)
  exact ⟨t', h', hi', hp', hc'⟩

theorem mergewithLoop_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {Q W : Type}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (combine : V → W → DictResult V)
    (hc1 : ∀ q k, keyConv.convert q = .ok k → keyConv.isequal q k = true →
      ∀ k', matchQ q k' = eqKey k k')
    (hc2 : ∀ q k, keyConv.isa q = some k → ∀ k', matchQ q k' = eqKey k k') :
    ∀ (d2 : List (Q × W)) (t : DictState K V) (m : List (K × V)), DictRep hash eqKey t m →
      t.count + d2.length < 2 ^ 54 →
      match d2.foldlM (refMergeStep eqKey matchQ keyConv valueConv combine) m with
      | .ok m' => ∃ t', mergewithLoop hash hashQ matchQ tablesz keyConv valueConv combine t d2 =
          .ok t' ∧ DictRep hash eqKey t' m'
      | .error e => mergewithLoop hash hashQ matchQ tablesz keyConv valueConv combine t d2 =
          .error e
  | [], t, _, hr, _ => ⟨t, rfl, hr⟩
  | (q, w) :: rest, t, m, hr, hc => by
    have hc0 : t.count < 2 ^ 54 := by simp only [List.length_cons] at hc; omega
    obtain ⟨idx, t1, n, hprobe, -, hout⟩ := htKeyindex2Query_spec hl hq htz hr.1 hc0 q
    have hd : Distinct eqKey (tlist t) := tlist_pairwise hr.1
    have hfp : rfind matchQ (tlist t) q = rfind matchQ m q := rfind_perm hl hq hd hr.2 q
    simp only [List.foldlM_cons]
    unfold mergewithLoop
    rw [hprobe, except_ok_bind]
    dsimp only
    cases hf : rfind matchQ (tlist t) q with
    | some e =>
      obtain ⟨hem, heq⟩ := rfind_some hf
      obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
      obtain ⟨hidx, ht1⟩ := hout.found i e h1 h2 hei heq
      subst hidx; subst t1
      have hstep : refMergeStep eqKey matchQ keyConv valueConv combine m (q, w) =
          (combine e.2 w >>= fun v => .ok (rset eqKey m e.1 v)) := by
        unfold refMergeStep; rw [← hfp, hf]
      rw [hstep, if_pos (by omega)]
      have hti : ((i : Int)).toNat = i := by omega
      rw [hti]
      obtain ⟨-, hk0, hv0⟩ := ent_some hei
      have hval : valAt t i = .ok e.2 := by unfold valAt; rw [hv0]
      rw [hval, except_ok_bind]
      cases hcomb : combine e.2 w with
      | error err => rfl
      | ok v' =>
        simp only [except_ok_bind]
        obtain ⟨k0, v0⟩ := e
        obtain ⟨hi2, hp2⟩ := Inv.overwrite hl hr.1 h1 h2 hei (hl.refl k0)
          (t' := DictState.mk t.size t.slots t.keys (updateAt t.vals i (some v')) t.ndel t.count
            t.age t.idxfloor t.maxprobe t.popcursor)
          rfl rfl (by show t.keys = _; rw [← hk0, updateAt_self]) rfl rfl rfl rfl rfl
        exact mergewithLoop_spec hl htz hq keyConv valueConv combine hc1 hc2 rest _ _
          ⟨hi2, hp2.trans (rset_perm hr.2 k0 v')⟩
          (by show t.count + rest.length < 2 ^ 54; simp only [List.length_cons] at hc; omega)
    | none =>
      have habs := rfind_eq_none_iff.1 hf
      obtain ⟨hneg, hslot⟩ := hout.absent habs
      have hmnone : rfind matchQ m q = none := by rw [← hfp]; exact hf
      have habs1 : ∀ e ∈ tlist t1, matchQ q e.1 = false :=
        fun e he => habs e (hout.perm.mem_iff.1 he)
      have hstep : refMergeStep eqKey matchQ keyConv valueConv combine m (q, w) =
          refStep eqKey keyConv valueConv m (q, w) := by
        unfold refMergeStep; rw [hmnone]
      rw [hstep, if_neg (by omega)]
      have hc1' : t1.count < 2 ^ 54 := by rw [hout.count]; exact hc0
      -- the stores after a successful conversion of `q` to `k`
      have finish : ∀ k, (∀ k', matchQ q k' = eqKey k k') → ∀ v,
          match rest.foldlM (refMergeStep eqKey matchQ keyConv valueConv combine)
            (rset eqKey m k v) with
          | .ok m' => ∃ t', (setindexAt hash tablesz t1 v k (-idx).toNat (shorthash7 (hashQ q)) >>=
              fun r => mergewithLoop hash hashQ matchQ tablesz keyConv valueConv combine r.2 rest) =
              .ok t' ∧ DictRep hash eqKey t' m'
          | .error e => (setindexAt hash tablesz t1 v k (-idx).toNat (shorthash7 (hashQ q)) >>=
              fun r => mergewithLoop hash hashQ matchQ tablesz keyConv valueConv combine r.2 rest) =
              .error e := by
        intro k hk v
        obtain ⟨t2, hs2, hi2, hp2, hcount2⟩ := mergeAbsent hl htz hq hout.inv hc1' hslot habs1 k hk v
        rw [hs2, except_ok_bind]
        have hmabs : ∀ e ∈ m, eqKey k e.1 = false := fun e he => by
          rw [← hk]; exact rfind_eq_none_iff.1 hmnone e he
        have hrep : DictRep hash eqKey t2 (rset eqKey m k v) := by
          refine ⟨hi2, ?_⟩
          unfold rset
          rw [rdel_absent hmabs]
          exact hp2.trans ((hout.perm.trans hr.2).cons _)
        exact mergewithLoop_spec hl htz hq keyConv valueConv combine hc1 hc2 rest t2 _ hrep
          (by rw [hcount2, hout.count]; simp only [List.length_cons] at hc; omega)
      unfold refStep convKey
      cases hisa : keyConv.isa q with
      | some k =>
        dsimp only
        simp only [except_ok_bind]
        cases hv : convertValue valueConv w with
        | error e => rfl
        | ok v =>
          simp only [except_ok_bind]
          exact finish k (hc2 q k hisa) v
      | none =>
        dsimp only
        cases hconv : keyConv.convert q with
        | error e => rfl
        | ok k =>
          simp only [except_ok_bind]
          by_cases hie : keyConv.isequal q k = true
          · simp only [hie, ↓reduceIte, except_ok_bind]
            cases hv : convertValue valueConv w with
            | error e => rfl
            | ok v =>
              simp only [except_ok_bind]
              exact finish k (hc1 q k hconv hie) v
          · simp only [hie, ↓reduceIte, except_error_bind, Bool.false_eq_true] <;> rfl

theorem DictMergewithSemantics_proven : DictMergewithSemantics := by
  intro K V Q W hash eqKey hashQ matchQ tablesz maxValues cld keyConv valueConv combine hasLength h m
    d2 hl hq htz hmv hcld hc1 hc2 hr hlen
  have hcm : h.count = m.length := by rw [hr.1.count, hr.2.length_eq]
  unfold mergewithBang
  cases hasLength with
  | true =>
    have hn : (JInt.lit .i64 (Int.ofNat (h.count + d2.length))).val = h.count + d2.length := by
      unfold JInt.lit; apply wrap_i64_val <;> simp only [Int.ofNat_eq_coe] <;> omega
    obtain ⟨t1, hs, hr1, hc1'⟩ := sizehint_spec htz hmv hcld hr (by omega)
      (JInt.lit .i64 (Int.ofNat (h.count + d2.length))) (by rw [hn]; omega) false
    rw [if_pos rfl, hs, except_ok_bind]
    exact mergewithLoop_spec hl htz hq keyConv valueConv combine hc1 hc2 d2 t1 m hr1 (by omega)
  | false =>
    rw [if_neg (by decide), except_ok_bind]
    exact mergewithLoop_spec hl htz hq keyConv valueConv combine hc1 hc2 d2 h m hr (by omega)

theorem refBuild_length_le {Q W : Type} (keyConv : KeyConv Q K) (valueConv : ValueConv W V) :
    ∀ (pairs : List (Q × W)) (m m' : List (K × V)),
      pairs.foldlM (refStep eqKey keyConv valueConv) m = .ok m' → m'.length ≤ m.length + pairs.length
  | [], m, m', h => by cases h; simp
  | p :: rest, m, m', h => by
    simp only [List.foldlM_cons] at h
    cases hs : refStep eqKey keyConv valueConv m p with
    | error e => rw [hs] at h; cases h
    | ok m1 =>
      rw [hs, except_ok_bind] at h
      have h1 := refBuild_length_le keyConv valueConv rest m1 m' h
      have h2 : m1.length ≤ m.length + 1 := by
        unfold refStep at hs
        cases hk : convKey keyConv p.1 with
        | error e => rw [hk] at hs; cases hs
        | ok k =>
          rw [hk, except_ok_bind] at hs
          cases hv : convertValue valueConv p.2 with
          | error e => rw [hv] at hs; cases hs
          | ok v =>
            rw [hv, except_ok_bind] at hs
            cases hs
            exact rset_length_le m k v
      simp only [List.length_cons]
      omega

/-- `reduce(merge!, items; init)`: `merge!(d, item)` for each item in turn (`sizehint!` then
`d[k] = v` for every pair of the item). -/
theorem mergeItems_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {maxValues : Nat}
    (hmv : MaxValuesLaw eqKey maxValues) {cld : JInt .i64 → JInt .i64} (hcld : CldLaw cld)
    {D Q W : Type} (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pairsOf : D → List (Q × W)) :
    ∀ (items : List D) (t : DictState K V) (m : List (K × V)), DictRep hash eqKey t m →
      t.count + (items.map fun y => (pairsOf y).length).sum ≤ 2 ^ 53 →
      match (items.flatMap pairsOf).foldlM (refStep eqKey keyConv valueConv) m with
      | .ok m' => ∃ t', items.foldlM (fun h y => do
            let h ← sizehint hash tablesz maxValues cld h
              (JInt.lit .i64 (Int.ofNat (h.count + (pairsOf y).length))) false
            (pairsOf y).foldlM (fun h (p : Q × W) =>
              setindexConv hash eqKey tablesz keyConv valueConv h p.2 p.1) h)
            t = .ok t' ∧ DictRep hash eqKey t' m'
      | .error e => items.foldlM (fun h y => do
            let h ← sizehint hash tablesz maxValues cld h
              (JInt.lit .i64 (Int.ofNat (h.count + (pairsOf y).length))) false
            (pairsOf y).foldlM (fun h (p : Q × W) =>
              setindexConv hash eqKey tablesz keyConv valueConv h p.2 p.1) h)
            t = .error e
  | [], t, m, hr, _ => ⟨t, rfl, hr⟩
  | y :: ys, t, m, hr, hc => by
    simp only [List.map_cons, List.sum_cons] at hc
    have hn : (JInt.lit .i64 (Int.ofNat (t.count + (pairsOf y).length))).val =
        t.count + (pairsOf y).length := by
      unfold JInt.lit; apply wrap_i64_val <;> simp only [Int.ofNat_eq_coe] <;> omega
    obtain ⟨t1, hs, hr1, hc1⟩ := sizehint_spec htz hmv hcld hr (by omega)
      (JInt.lit .i64 (Int.ofNat (t.count + (pairsOf y).length))) (by rw [hn]; omega) false
    have hloop := insertLoop_spec hl htz keyConv valueConv
      (fun ps t => ps.foldlM (fun h (p : Q × W) =>
        setindexConv hash eqKey tablesz keyConv valueConv h p.2 p.1) t)
      (fun _ => rfl) (fun p rest t => rfl) (pairsOf y) t1 m hr1 (by omega)
    simp only [List.flatMap_cons, List.foldlM_append, List.foldlM_cons]
    rw [hs, except_ok_bind]
    cases hb : (pairsOf y).foldlM (refStep eqKey keyConv valueConv) m with
    | error e =>
      rw [hb] at hloop
      simp only [hloop, except_error_bind]
      done
    | ok m1 =>
      rw [hb] at hloop
      obtain ⟨t2, ht2, hr2⟩ := hloop
      simp only [ht2, except_ok_bind]
      have hm1 := refBuild_length_le keyConv valueConv (pairsOf y) m m1 hb
      have hcm : t.count = m.length := by rw [hr.1.count, hr.2.length_eq]
      have hc2 : t2.count = m1.length := by rw [hr2.1.count, hr2.2.length_eq]
      exact mergeItems_spec hl htz hmv hcld keyConv valueConv pairsOf ys t2 m1 hr2 (by omega)

end Merge

theorem DictReduceMergeSemantics_proven : DictReduceMergeSemantics := by
  intro D keytype valtype promoteType mapreduce mergeItems hmr0 hmr1
  refine ⟨?_, ?_⟩
  · unfold reduceMerge; rw [hmr0]
  · intro x xs K V Q W hash eqKey tablesz maxValues cld keyConv valueConv pairsOf hK hV hl htz hmv
      hcld hsum hmerge
    subst hK hV
    have hspec := mergeItems_spec hl htz hmv hcld keyConv valueConv pairsOf (x :: xs)
      (dictEmpty _ _) [] (dictEmpty_rep hash eqKey) (by show 0 + _ ≤ _; omega)
    unfold reduceMerge refBuild
    rw [hmr1 keytype, hmr1 valtype]
    dsimp only
    rw [hmerge]
    revert hspec
    cases ((x :: xs).flatMap pairsOf).foldlM (refStep eqKey keyConv valueConv) [] with
    | error e => intro hspec; rw [hspec]
    | ok m =>
      intro hspec
      obtain ⟨t', ht', hr'⟩ := hspec
      exact ⟨t', by rw [ht'], hr'⟩

/-- `map!(f, values(d))` (`DictMapReduceSemantics`) and `reduce(merge, items)`
(`DictReduceMergeSemantics`). -/
def DictMapReduceMergeSemantics : Prop := DictMapReduceSemantics ∧ DictReduceMergeSemantics

theorem DictMapReduceMergeSemantics_proven : DictMapReduceMergeSemantics :=
  ⟨DictMapReduceSemantics_proven, DictReduceMergeSemantics_proven⟩

/-! ## Refutations

Each counterexample uses lawful callees: `Nat` keys compared with `==` and a constant hash
(every hash is consistent with `isequal`), `_tablesz` (`tableszSpec`), `max_values(Int)` and
`cld(x, 2)` (`cldSpec`). -/

/-- A hash consistent with `==` on `Nat`: all keys collide. -/
def natHash (_ : Nat) : JInt .u64 := JInt.lit .u64 0

def natEq (a b : Nat) : Bool := a == b

theorem natKeyLaws : KeyLaws natHash natEq :=
  ⟨fun a => by simp [natEq], fun a b h => by simp only [natEq, beq_iff_eq] at *; exact h.symm,
    fun a b c h1 h2 => by simp only [natEq, beq_iff_eq] at *; omega, fun _ _ _ => rfl⟩

/-- `cld(x, 2)` on `Int` (`cld` docstring, `base/div.jl`). -/
def cldSpec (x : JInt .i64) : JInt .i64 := JInt.wrap .i64 (-((-x.val) / 2))

theorem cldSpec_law : CldLaw cldSpec := by
  intro x
  have hx := i64_val_range x
  unfold cldSpec
  apply wrap_i64_val <;> omega

theorem rehash_ok_size {hash : K → JInt .u64} {tablesz : Nat → Nat} {h r : DictState K V}
    {n : Nat} (hr : rehash hash tablesz h n = .ok r) : r.size = tablesz n := by
  unfold rehash at hr
  dsimp only at hr
  split at hr
  · cases hr; rfl
  · simp only [bind, Except.bind] at hr
    split at hr
    · cases hr
    · cases hr; rfl

/-- `sizehint!(d, 2^62)` on a well-formed `Dict` with 17 pairs: `3 * 2^62` wraps to `-2^62`, so the
requested table size is `_tablesz(cld(-2^62, 2)) = 16`, too small for 17 pairs; no result
represents the pairs. -/
theorem sizehint_wrap_not_ok {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {tablesz : Nat → Nat} (htz : TableszLaw tablesz) {maxValues : Nat}
    (hmv1 : 2 ^ 62 ≤ maxValues) (hmv2 : maxValues < 2 ^ 63) {cld : JInt .i64 → JInt .i64}
    (hcld : CldLaw cld) {h h' : DictState K V} {m : List (K × V)} (hr : DictRep hash eqKey h m)
    (hm : m.length = 17) (hr' : DictRep hash eqKey h' m) :
    sizehint hash tablesz maxValues cld h (JInt.lit .i64 (2 ^ 62)) true ≠ .ok h' := by
  intro hs
  have hc : h.count = 17 := by rw [hr.1.count, hr.2.length_eq, hm]
  have hsz := hr.1.count_le_size
  have hc' : h'.count = 17 := by rw [hr'.1.count, hr'.2.length_eq, hm]
  have hsz' := hr'.1.count_le_size
  have hn : (JInt.lit .i64 (2 ^ 62)).val = 2 ^ 62 := by
    unfold JInt.lit; apply wrap_i64_val <;> omega
  have hx0 : (clampSizeHint h.count maxValues (JInt.lit .i64 (2 ^ 62))).val = 2 ^ 62 := by
    unfold clampSizeHint
    rw [hn, wrap_i64_val (by omega) (by omega)]
    omega
  have h3 : (JInt.lit .i64 (3 * (clampSizeHint h.count maxValues (JInt.lit .i64 (2 ^ 62))).val)).val
      = -2 ^ 62 := by
    rw [hx0]; decide
  have hy := hcld (JInt.lit .i64 (3 * (clampSizeHint h.count maxValues (JInt.lit .i64 (2 ^ 62))).val))
  generalize hY : cld (JInt.lit .i64
    (3 * (clampSizeHint h.count maxValues (JInt.lit .i64 (2 ^ 62))).val)) = Y at hy
  rw [h3] at hy
  have hY0 : Y.val.toNat = 0 := by rw [hy]; decide
  have hN : tablesz Y.val.toNat = 16 := by rw [hY0, htz 0 (by omega)]; decide
  unfold sizehint at hs
  dsimp only at hs
  rw [hY, hN] at hs
  split at hs
  · rename_i hcond
    simp at hcond
    omega
  · have := rehash_ok_size hs
    rw [htz 16 (by omega)] at this
    have h16 : tableszSpec 16 = 16 := by decide
    omega

/-- Seventeen keys `0, ..., 16` with unit values. -/
def pairs17 : List (Nat × Unit) := (List.range 17).map fun i => (i, ())

theorem DictSizehintTotal_refuted : ¬ DictSizehintTotal := by
  intro hT
  have hb := DictIteratorConstructorSemantics_proven Nat Unit Nat Unit natHash natEq tableszSpec
    (2 ^ 63 - 1) cldSpec (typedKey natEq) (fieldConv Unit) pairs17 true natKeyLaws (fun _ _ => rfl)
    (Or.inl (by decide)) cldSpec_law (by decide)
  rw [show refBuild natEq (typedKey natEq) (fieldConv Unit) pairs17 =
    .ok (pairs17.reverse) from rfl] at hb
  obtain ⟨h, -, hr⟩ := hb
  have hc : h.count < 2 ^ 54 := by rw [hr.1.count, hr.2.length_eq]; decide
  obtain ⟨h', hs, hr'⟩ := hT Nat Unit natHash natEq tableszSpec (2 ^ 63 - 1) cldSpec h
    pairs17.reverse natKeyLaws (fun _ _ => rfl) (Or.inl (by decide)) cldSpec_law hr hc
    (JInt.lit .i64 (2 ^ 62)) true
  exact sizehint_wrap_not_ok (fun _ _ => rfl) (by decide) (by decide) cldSpec_law hr (by decide)
    hr' hs

/-- A `show` context with `:limit => true` for a dictionary given by its list of pairs. -/
def showOps10 : DictShowOps Unit (List (Nat × Nat)) Nat Nat :=
  ⟨fun c _ => c, fun _ => true, fun _ _ => "Dict", List.isEmpty, fun _ _ => false, id,
    fun _ _ => "p"⟩

/-- Ten pairs: all ten are shown, yet the ellipsis is printed. -/
theorem DictShowLimitEllipsis_refuted : ¬ DictShowLimitEllipsis := by
  intro h
  have := h Unit (List (Nat × Nat)) Nat Nat showOps10 () ((List.range 10).map fun i => (i, i)) rfl
    rfl (fun _ _ => show "p" ≠ "…" by decide) (fun _ _ => show "Dict" ≠ "…" by decide)
  have hmem : "…" ∈ showDict showOps10 () ((List.range 10).map fun i => (i, i)) := by decide
  exact absurd (this.1 hmem).2 (by decide)

/-- `convert(Float32, x::Float64)` modelled on naturals: it rounds to an even number, so the
converted key is not `isequal` to the original (`Float32(0.1) != 0.1`). -/
def lossyConv : ValueConv Nat Nat := ⟨fun _ => none, fun q => .ok (q / 2 * 2)⟩

theorem ImmutableDictSetGet_refuted : ¬ ImmutableDictSetGet := by
  intro h
  have := h Nat Unit Nat Unit lossyConv (fieldConv Unit) (fun k q => k == q) [] [(0, ())] () 1 ()
    rfl (Or.inl rfl)
  simp [immutableGetindex] at this

theorem ImmutableDictInMissing_refuted : ¬ ImmutableDictInMissing := by
  intro h
  have := h Nat Nat Nat Nat (fun k q => k == q) [(0, 1)] (0, 0) rfl
  simp [immutableIn] at this

/-- `ImmutableDict(:a => 1, :a => 2)`: `d[:a] == 2`, but `Dict(d)` stores the older value last. -/
theorem ImmutableDictToDict_refuted : ¬ ImmutableDictToDict := by
  intro hT
  have hb := DictIteratorConstructorSemantics_proven Nat Nat Nat Nat natHash natEq tableszSpec
    (2 ^ 63 - 1) cldSpec (typedKey natEq) (fieldConv Nat) [(0, 2), (0, 1)] true natKeyLaws
    (fun _ _ => rfl) (Or.inl (by decide)) cldSpec_law (by decide)
  rw [show refBuild natEq (typedKey natEq) (fieldConv Nat) [(0, 2), (0, 1)] = .ok [(0, 1)]
    from rfl] at hb
  obtain ⟨h, hh, hr⟩ := hb
  have hlook := (DictLookupSemantics_proven Nat Nat Nat natHash natEq natHash natEq h [(0, 1)]
    natKeyLaws natKeyLaws.query hr 0 0 0 (fun _ => .ok 0)).2.1
  have := hT Nat Nat natHash natEq tableszSpec (2 ^ 63 - 1) cldSpec [(0, 2), (0, 1)] h natKeyLaws
    (fun _ _ => rfl) (Or.inl (by decide)) cldSpec_law (by rw [immutableCollect_eq]; exact hh) 0 0
  rw [hlook] at this
  simp [rlookup, rfind, immutableGet, natEq] at this

theorem len_le_one {α : Type} {t : List α} (h : t.length ≤ 1) : t = [] ∨ ∃ a, t = [a] := by
  match t, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr ⟨a, rfl⟩

/-- A `PersistentDict{Bool,Nothing}` whose two keys share an `objectid` (a perfect hash collision,
as in `repro/dicts-persistentdict-objectid-collision.jl`): every key lands in the same slot of the
root level, which holds at most one leaf. -/
def collideOps : PersistentOps Bool Unit Bool Unit (List (Bool × Unit)) Bool Nat where
  empty _ := []
  singleton p := .ok [p]
  hashState k := k
  path t k _ := ⟨t.all (fun e => e.1 == k), !t.isEmpty, t, 0, 0, t, k⟩
  insert top _ found _ _ _ k v := if found then .ok [(k, v)] else .error .thrownDict
  deleteAt _ _ _ := []
  unset top _ _ := top
  isLevelEmpty t := t.isEmpty
  leafValue t _ := t.head?.map (·.2)
  iterate t s := (t[s.getD 0]?).map fun p => (p, s.getD 0 + 1)
  length t := t.length
  isEmpty t := t.isEmpty

def boolHash (_ : Bool) : JInt .u64 := JInt.lit .u64 0

def boolEq (a b : Bool) : Bool := a == b

theorem collideOps_laws :
    HamtLaws collideOps boolHash boolEq (fun t => t.length ≤ 1) (fun t => t) := by
  refine ⟨⟨by decide, by decide, by decide, fun _ _ _ => rfl⟩, ?_, by decide, rfl,
    fun p => ⟨[p], rfl, Nat.le_refl _, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases len_le_one ht with rfl | ⟨a, rfl⟩ <;> simp
  · intro t ht
    rcases len_le_one ht with rfl | ⟨a, rfl⟩ <;> simp [collideOps]
  · intro t k _ ht
    rcases len_le_one ht with rfl | ⟨⟨a, u⟩, rfl⟩
    · rfl
    · cases a <;> cases k <;> rfl
  · intro t k ht
    rcases len_le_one ht with rfl | ⟨⟨a, u⟩, rfl⟩
    · intro h; cases h
    · cases a <;> cases k <;> cases u <;> intro h <;> first | rfl | cases h
  · intro t k ht
    exact ⟨ht, List.Perm.refl _⟩
  · intro t k v t' ht
    rcases len_le_one ht with rfl | ⟨⟨a, u⟩, rfl⟩
    · intro h; cases h; exact ⟨Nat.le_refl _, by cases k <;> cases v <;> decide⟩
    · cases a <;> cases k <;> cases u <;> cases v <;> intro h <;>
        first | (cases h; exact ⟨by decide, by decide⟩) | cases h
  · intro t k v ht
    rcases len_le_one ht with rfl | ⟨⟨a, u⟩, rfl⟩
    · exact ⟨fun _ _ he => absurd he (List.not_mem_nil), fun _ => ⟨[(k, v)], rfl⟩⟩
    · cases a <;> cases k <;> cases u <;> cases v <;> simp [collideOps, boolHash, boolEq]
  · intro t k ht
    rcases len_le_one ht with rfl | ⟨⟨a, u⟩, rfl⟩
    · intro h; cases h
    · cases a <;> cases k <;> cases u <;> intro h <;>
        first | (exact ⟨by decide, by decide⟩) | cases h
  · intro t ht fuel hf
    rcases len_le_one ht with rfl | ⟨⟨a, u⟩, rfl⟩
    · match fuel, hf with
      | n + 1, _ => exact List.Perm.refl _
    · match fuel, hf with
      | n + 2, _ =>
        show List.Perm ((a, u) :: trieCollect collideOps [(a, u)] (n + 1) (some 1)) [(a, u)]
        exact List.Perm.refl _
  · intro t _; rfl
  · intro t _; rfl

/-- `KeyValue.set(d, false, nothing)` on `d = PersistentDict(true => nothing)` whose keys collide
throws "Perfect hash collision". -/
theorem PersistentSetNothrow_refuted : ¬ PersistentSetNothrow := by
  intro h
  obtain ⟨d', hd⟩ := h Bool Unit (List (Bool × Unit)) Bool Nat collideOps boolHash boolEq
    (fun t => t.length ≤ 1) (fun t => t) collideOps_laws ⟨[(true, ())]⟩ false () (by decide)
  cases hd

/-! ## Sequences of operations -/

/-- One `Dict` call with keys of type `K` and values of type `V`: `d[k] = v`, `delete!(d, k)`,
`pop!(d, k)`, `pop!(d, k, default)`, `get!(() -> default, d, k)`, `sizehint!(d, n; shrink)`,
`empty!(d)`, `filter!(pred, d)` and `map!(f, values(d))`. -/
inductive DictCall (K V : Type) where
  | setindex (key : K) (value : V)
  | delete (key : K)
  | pop (key : K)
  | popDefault (key : K) (default : V)
  | getBang (key : K) (default : V)
  | sizehint (n : JInt .i64) (shrink : Bool)
  | empty
  | filter (predicate : K × V → Bool)
  | mapValues (f : V → V)

/-- The reference result of one call on the finite map `m`: the new map and the value the call
returns, if any. -/
def refCall (eqKey : K → K → Bool) (m : List (K × V)) :
    DictCall K V → DictResult (List (K × V) × Option V)
  | .setindex k v => .ok (rset eqKey m k v, none)
  | .delete k => .ok (rdel eqKey m k, none)
  | .pop k =>
    match rfind eqKey m k with
    | some e => .ok (rdel eqKey m k, some e.2)
    | none => .error .keyError
  | .popDefault k d =>
    match rfind eqKey m k with
    | some e => .ok (rdel eqKey m k, some e.2)
    | none => .ok (m, some d)
  | .getBang k d =>
    match rfind eqKey m k with
    | some e => .ok (m, some e.2)
    | none => .ok (rset eqKey m k d, some d)
  | .sizehint _ _ => .ok (m, none)
  | .empty => .ok ([], none)
  | .filter p => .ok (m.filter p, none)
  | .mapValues f => .ok (m.map (fun e => (e.1, f e.2)), none)

/-- One call on the source-mirrored `Dict` model, with the value it returns, if any. -/
def modelCall (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) (h : DictState K V) :
    DictCall K V → DictResult (DictState K V × Option V)
  | .setindex k v => setindexAny hash eqKey tablesz h v k >>= fun h' => .ok (h', none)
  | .delete k => deleteKey hash eqKey unsetKey unsetVal h k >>= fun h' => .ok (h', none)
  | .pop k => popKey hash eqKey unsetKey unsetVal h k >>= fun r => .ok (r.2, some r.1)
  | .popDefault k d =>
    popDefault hash eqKey unsetKey unsetVal h k d >>= fun r => .ok (r.2, some r.1)
  | .getBang k d =>
    getBang hash eqKey tablesz (fieldConv V) h k (fun h => .ok (d, h)) >>=
      fun r => .ok (r.2, some r.1)
  | .sizehint n s => sizehint hash tablesz maxValues cld h n s >>= fun h' => .ok (h', none)
  | .empty => .ok (emptyBang fillSlots unsetKey unsetVal h, none)
  | .filter p => filterBang unsetKey unsetVal p h >>= fun h' => .ok (h', none)
  | .mapValues f => mapBang (fun v => .ok (f v)) ⟨h⟩ >>= fun r => .ok (r.dict, none)

/-- Runs `calls` in order from `s`, collecting the returned values; the first error propagates. -/
def runCalls {S : Type} (step : S → DictCall K V → DictResult (S × Option V)) :
    S → List (DictCall K V) → DictResult (S × List V)
  | s, [] => .ok (s, [])
  | s, c :: cs => step s c >>= fun r =>
    runCalls step r.1 cs >>= fun t => .ok (t.1, r.2.toList ++ t.2)

/-- Every sequence of fewer than `2^54` calls from `Dict()` made of `d[k] = v`, `delete!`, `pop!`
(both), `get!`, `sizehint!` (hints at most `2^61`), `empty!`, `filter!` and `map!` returns the
reference map's values and throws its `KeyError`s, and leaves a table representing the reference
map: its keys are pairwise non-`isequal`, lookups find its values, `length` counts its pairs and
iteration yields each of its pairs exactly once. -/
def DictOperationsAgree : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)) (calls : List (DictCall K V)),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    FillLaw fillSlots → UnsetLaw unsetKey → UnsetLaw unsetVal → calls.length < 2 ^ 54 →
    (∀ n s, DictCall.sizehint n s ∈ calls → n.val ≤ 2 ^ 61) →
    match runCalls (refCall eqKey) [] calls with
    | .ok r => ∃ h,
        runCalls (modelCall hash eqKey tablesz maxValues cld fillSlots unsetKey unsetVal)
          (dictEmpty K V) calls = .ok (h, r.2) ∧
        DictRep hash eqKey h r.1 ∧ Distinct eqKey r.1 ∧ length h = r.1.length ∧
        (∀ (k : K) (default : V),
          getindex hash eqKey h k =
              (match rlookup eqKey r.1 k with | some v => .ok v | none => .error .keyError) ∧
            JuliaLean.base.dict.get hash eqKey h k default =
              .ok ((rlookup eqKey r.1 k).getD default) ∧
            haskey hash eqKey h k = .ok (rlookup eqKey r.1 k).isSome) ∧
        ∃ l, (iterateFirst h >>= fun x =>
            match x with
            | none => .ok []
            | some (pair, next) =>
              iterCollect h (h.size + 1) next >>= fun rest => .ok (pair :: rest)) =
          .ok l ∧ List.Perm l r.1
    | .error e =>
      runCalls (modelCall hash eqKey tablesz maxValues cld fillSlots unsetKey unsetVal)
        (dictEmpty K V) calls = .error e

section Calls
variable {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat} {maxValues : Nat}
  {cld : JInt .i64 → JInt .i64} {fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat}
  {unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K)}
  {unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V)}

theorem modelCall_agrees (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz)
    (hmv : MaxValuesLaw eqKey maxValues) (hcld : CldLaw cld) (hfill : FillLaw fillSlots)
    (huk : UnsetLaw unsetKey) (huv : UnsetLaw unsetVal) {h : DictState K V} {m : List (K × V)}
    (hr : DictRep hash eqKey h m) (hc : m.length < 2 ^ 54) (c : DictCall K V)
    (hs : ∀ n s, c = .sizehint n s → n.val ≤ 2 ^ 61) :
    match refCall eqKey m c with
    | .ok r => ∃ h', modelCall hash eqKey tablesz maxValues cld fillSlots unsetKey unsetVal h c =
        .ok (h', r.2) ∧ DictRep hash eqKey h' r.1 ∧ r.1.length ≤ m.length + 1
    | .error e =>
      modelCall hash eqKey tablesz maxValues cld fillSlots unsetKey unsetVal h c = .error e := by
  have hcount : h.count < 2 ^ 54 := by rw [hr.1.count, hr.2.length_eq]; exact hc
  have hdel : ∀ k, (rdel eqKey m k).length ≤ m.length + 1 := fun k => by
    have := List.length_filter_le (fun e : K × V => !eqKey k e.1) m
    unfold rdel; omega
  cases c with
  | setindex k v =>
    obtain ⟨h', hs', hr'⟩ := (DictSetindexLookup_proven K V K V hash eqKey tablesz
      ⟨some, .ok, fun _ _ => true⟩ (fieldConv V) h m hl htz hr hcount).1 k v
    dsimp only [refCall]
    exact ⟨h', by show (setindexAny hash eqKey tablesz h v k >>= _) = _; rw [hs']; rfl, hr',
      rset_length_le m k v⟩
  | delete k =>
    obtain ⟨h', hd, hr'⟩ := hr.deleteKey hl huk huv hl.query k
    dsimp only [refCall]
    exact ⟨h', by show (deleteKey hash eqKey unsetKey unsetVal h k >>= _) = _; rw [hd]; rfl, hr',
      hdel k⟩
  | pop k =>
    have hp := hr.popKey hl huk huv hl.query k
    rcases hf : rfind eqKey m k with _ | e
    · simp only [hf] at hp
      simp only [refCall, hf]
      show (popKey hash eqKey unsetKey unsetVal h k >>= _) = _
      rw [hp]; rfl
    · simp only [hf] at hp
      obtain ⟨h', hpk, hr'⟩ := hp
      simp only [refCall, hf]
      exact ⟨h', by show (popKey hash eqKey unsetKey unsetVal h k >>= _) = _; rw [hpk]; rfl, hr',
        hdel k⟩
  | popDefault k d =>
    have hp := hr.popDefault hl huk huv hl.query k d
    rcases hf : rfind eqKey m k with _ | e
    · simp only [hf] at hp
      simp only [refCall, hf]
      exact ⟨h, by show (popDefault hash eqKey unsetKey unsetVal h k d >>= _) = _; rw [hp]; rfl,
        hr, Nat.le_succ _⟩
    · simp only [hf] at hp
      obtain ⟨h', hpk, hr'⟩ := hp
      simp only [refCall, hf]
      exact ⟨h', by show (popDefault hash eqKey unsetKey unsetVal h k d >>= _) = _; rw [hpk]; rfl,
        hr', hdel k⟩
  | getBang k d =>
    have hdef : DefaultOK hash eqKey
        (fun t : DictState K V => (.ok (d, t) : DictResult (V × DictState K V))) := by
      intro h0 w h2 hi hc0 he
      cases he
      exact ⟨hi, hc0, 0, Nat.two_pow_pos 64, AgeStep.refl h0⟩
    have hg := getBang_spec hl htz (fieldConv V) hr hcount k _ hdef
    rcases hf : rfind eqKey m k with _ | e
    · simp only [hf] at hg
      obtain ⟨t1, ht1, -, hok⟩ := hg
      obtain ⟨t', hgb, hr'⟩ := hok d t1 rfl
      simp only [refCall, hf]
      exact ⟨t', by
        show (getBang hash eqKey tablesz (fieldConv V) h k (fun h => .ok (d, h)) >>= _) = _
        rw [hgb]; rfl, ⟨hr'.1, hr'.2.trans (rset_perm ht1.2 k d)⟩, rset_length_le m k d⟩
    · simp only [hf] at hg
      simp only [refCall, hf]
      exact ⟨h, by
        show (getBang hash eqKey tablesz (fieldConv V) h k (fun h => .ok (d, h)) >>= _) = _
        rw [hg]; rfl, hr, Nat.le_succ _⟩
  | sizehint n s =>
    obtain ⟨h', hsh, hr'⟩ := DictSizehintSmall_proven K V hash eqKey tablesz maxValues cld h m htz
      hmv hcld hr hcount n s (hs n s rfl)
    dsimp only [refCall]
    exact ⟨h', by show (sizehint hash tablesz maxValues cld h n s >>= _) = _; rw [hsh]; rfl, hr',
      Nat.le_succ _⟩
  | empty =>
    dsimp only [refCall]
    exact ⟨_, rfl,
      (DictEmptyContract_proven K V hash eqKey fillSlots unsetKey unsetVal h m hfill hr).1,
      Nat.zero_le _⟩
  | filter p =>
    obtain ⟨h', hfb, hr'⟩ := hr.filterBang hl huk huv p
    dsimp only [refCall]
    exact ⟨h', by show (filterBang unsetKey unsetVal p h >>= _) = _; rw [hfb]; rfl, hr',
      by have := List.length_filter_le p m; omega⟩
  | mapValues f =>
    obtain ⟨h', hmb, hr'⟩ := DictMapReduceSemantics_proven K V hash eqKey h m f hr
    dsimp only [refCall]
    exact ⟨h', by show (mapBang (fun v => .ok (f v)) ⟨h⟩ >>= _) = _; rw [hmb]; rfl, hr',
      by rw [List.length_map]; omega⟩

theorem runCalls_agrees (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz)
    (hmv : MaxValuesLaw eqKey maxValues) (hcld : CldLaw cld) (hfill : FillLaw fillSlots)
    (huk : UnsetLaw unsetKey) (huv : UnsetLaw unsetVal) :
    ∀ (calls : List (DictCall K V)) (h : DictState K V) (m : List (K × V)),
    DictRep hash eqKey h m → m.length + calls.length < 2 ^ 54 →
    (∀ n s, DictCall.sizehint n s ∈ calls → n.val ≤ 2 ^ 61) →
    match runCalls (refCall eqKey) m calls with
    | .ok r => ∃ h', runCalls (modelCall hash eqKey tablesz maxValues cld fillSlots unsetKey
        unsetVal) h calls = .ok (h', r.2) ∧ DictRep hash eqKey h' r.1
    | .error e => runCalls (modelCall hash eqKey tablesz maxValues cld fillSlots unsetKey unsetVal)
        h calls = .error e
  | [], h, _, hr, _, _ => ⟨h, rfl, hr⟩
  | c :: cs, h, m, hr, hlen, hs => by
    rw [List.length_cons] at hlen
    have hstep := modelCall_agrees hl htz hmv hcld hfill huk huv (tablesz := tablesz)
      (maxValues := maxValues) (cld := cld) hr (by omega) c
      (fun n s he => hs n s (he ▸ List.mem_cons_self))
    simp only [runCalls]
    rcases hrc : refCall eqKey m c with e | ⟨m1, o⟩
    · simp only [hrc] at hstep
      simp only [hstep, except_error_bind]
    · simp only [hrc] at hstep
      obtain ⟨h1, hm1, hr1, hl1⟩ := hstep
      have ih := runCalls_agrees hl htz hmv hcld hfill huk huv cs h1 m1 hr1 (by omega)
        (fun n s hm => hs n s (List.mem_cons_of_mem _ hm))
      simp only [except_ok_bind, hm1]
      rcases hrr : runCalls (refCall eqKey) m1 cs with e | ⟨m2, outs⟩
      · simp only [hrr] at ih
        simp only [ih, except_error_bind]
      · simp only [hrr] at ih
        obtain ⟨h2, hm2, hr2⟩ := ih
        simp only [except_ok_bind]
        exact ⟨h2, by simp only [hm2, except_ok_bind], hr2⟩

end Calls

theorem DictOperationsAgree_proven : DictOperationsAgree := by
  intro K V hash eqKey tablesz maxValues cld fillSlots unsetKey unsetVal calls hl htz hmv hcld
    hfill huk huv hlen hs
  have hrun := runCalls_agrees hl htz hmv hcld hfill huk huv calls (dictEmpty K V) []
    (dictEmpty_rep hash eqKey) (by rw [List.length_nil]; omega) hs
  rcases hrr : runCalls (refCall eqKey) [] calls with e | ⟨m, outs⟩
  · simp only [hrr] at hrun
    exact hrun
  · simp only [hrr] at hrun
    obtain ⟨h, hm, hr⟩ := hrun
    have hsize : h.size < 2 ^ 63 - 1 := by have := hr.1.sizeLe; omega
    obtain ⟨-, hit, -⟩ := DictIterationSemantics_proven K V hash eqKey h m hr hsize
    refine ⟨h, hm, hr, Distinct.perm hl (tlist_pairwise hr.1) hr.2,
      (DictEmptyContract_proven K V hash eqKey fillSlots unsetKey unsetVal h m hfill hr).2.2.2.2,
      fun k default => ?_, hit⟩
    obtain ⟨hgi, hget, -, hhk, -⟩ := hr.lookups hl hl.query k default k (fun _ => .ok default)
    exact ⟨hgi, hget, hhk⟩

/-- Dictionary iteration (`DictIterationSemantics`) and `Iterators.only` (`DictOnlyContract`). -/
def DictIterationOnlySemantics : Prop := DictIterationSemantics ∧ DictOnlyContract

theorem DictIterationOnlySemantics_proven : DictIterationOnlySemantics :=
  ⟨DictIterationSemantics_proven, DictOnlyContract_proven⟩

/-! ## Nothing to promise

Nothing to promise: Dict@87: the internal constructor `Dict{K,V}(slots, keys, vals, ndel, count, age, idxfloor, maxprobe, popcursor)` stores its arguments as the fields; every behaviour of the table built from them is stated for the operations that maintain the fields.
Nothing to promise: Iterators.only@1069: forwards to `Iterators._only(dict, first)` (`base/iterators.jl`), which owns the one-element check; `PersistentCollectionSemantics` states the iteration it consumes.
-/

/-! ## Method → property table

| Julia method (`name@line`) | Property |
|---|---|
| `show@3` | `DictShowLimitEllipsis` |
| `Dict@77`, `Dict@109`, `Dict@110`, `empty@120` | `DictEmptyConstructorSemantics` |
| `Dict@83`, `copy@111` | `DictCopySemantics` |
| `Dict@87` | nothing to promise (stores its arguments) |
| `Dict@91` | `DictIteratorConstructorSemantics` |
| `Dict@99` | `DictSinglePairConstructorSemantics` |
| `Dict@100` | `DictConstructorSemantics` |
| `Dict@115` | `DictTypedPairListConstructorSemantics` |
| `Dict@116`, `Dict@118` | `DictGenericConstructorSemantics` (in `DictConstructionSemantics`) |
| `_shorthash7@123`, `isslotempty@135`, `isslotfilled@136`, `isslotmissing@137` | `DictSlots` |
| `hashindex@128` | `DictHashindexSemantics` |
| `rehash!@139`, `sizehint!@196` | `DictSizehintSmall`, `DictSizehintTotal`, `DictProbeSafe` |
| `empty!@224`, `isempty@712`, `length@713` | `DictEmptyContract` |
| `ht_keyindex@241`, `ht_keyindex2_shorthash!@270`, `ht_keyindex2!@325` | `DictProbeSemantics`, `DictProbeSafe` |
| `_setindex!@327`, `setindex!@347`, `setindex!@359`, `setindex!@374` | `DictSetindexLookup` |
| `get!@445`, `get!@457` | `DictGetBangMutatingDefault` |
| `getindex@480`, `get@507`, `get@529`, `haskey@553`, `in@554`, `getkey@575` | `DictLookupSemantics` |
| `_pop!@580`, `pop!@586`, `pop!@615` | `DictPopKeyContract` |
| `pop!@620` | `DictPopAnyContract` |
| `_delete!@631`, `delete!@681` | `DictDeleteLookup` |
| `skip_deleted@689`, `skip_deleted_floor!@698`, `_iterate_dict@706`, `iterate@707`, `iterate@710`, `iterate@717` | `DictIterationSemantics` |
| `Iterators.only@715` | `DictOnlyContract` |
| `filter!@725` | `DictFilterContract` |
| `reduce@735` | `DictReduceMergeSemantics` |
| `map!@741` | `DictMapReduceSemantics` |
| `mergewith!@753` | `DictMergewithSemantics` |
| `ImmutableDict@780`, `ImmutableDict@781`, `ImmutableDict@782`, `ImmutableDict@811`, `ImmutableDict@812`, `ImmutableDict@813`, `ImmutableDict@815` | `ImmutableDictConstructorSemantics`, `ImmutableDictSetGet` |
| `in@817` | `ImmutableDictPairMembershipSemantics`, `ImmutableDictInMissing` |
| `haskey@828`, `getindex@836`, `get@843`, `get@851` | `ImmutableDictLookupSemantics`, `ImmutableDictToDict` |
| `iterate@860`, `length@864`, `isempty@865`, `empty@866` | `ImmutableDictCollectionSemantics` |
| `setindex@886` | `ImmutableDictSetGet` |
| `_similar_for@890`, `_similar_for@891` | `DictSimilarSemantics` |
| `KeyValue.set@903`, `KeyValue.set@906`, `PersistentDict@969`, `PersistentDict@970`, `PersistentDict@976`, `PersistentDict@992`, `PersistentDict@1000` | `PersistentConstructorSemantics` |
| `KeyValue.set@909`, `KeyValue.set@911`, `_keyvalueset@913`, `PersistentDict@982`, `PersistentDict@983`, `PersistentDict@986` | `PersistentSetSemantics`, `PersistentSetNothrow` |
| `KeyValue.set@920`, `KeyValue.set@922`, `_keyvalueset@924`, `delete@1059` | `PersistentDeleteSemantics` |
| `eltype@1008`, `iterate@1063`, `length@1065`, `isempty@1066`, `empty@1067` | `PersistentCollectionSemantics` |
| `in@1010` | `PersistentPairMembershipSemantics` |
| `haskey@1017`, `getindex@1021`, `get@1027`, `KeyValue.get@1033`, `KeyValue.get@1047`, `get@1053` | `PersistentLookupSemantics`, `PersistentPathSafe` |
| `Iterators.only@1069` | nothing to promise (forwards to `Iterators._only`) |
-/

private def proven (id : String) (juliaFns : List String) (statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/dict.jl", juliaFns := juliaFns, statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

private def refuted (id : String) (juliaFns : List String) (statement source : String)
    (prop thm : Lean.Name) (notes : String) : Entry :=
  { id := id, juliaFile := "base/dict.jl", juliaFns := juliaFns, statement := statement,
    source := source, status := .refuted, prop := prop, thm := some thm,
    issue := "none found (retained reproducer)", notes := notes }

def entries : List Entry := [
  proven "dicts-ops-agree" ["setindex!@374", "delete!@681", "pop!@586", "pop!@615", "get!@457",
    "sizehint!@196", "empty!@224", "filter!@725", "map!@741", "getindex@480", "get@507",
    "haskey@553", "iterate@707", "iterate@710", "length@713"]
    "Every sequence of fewer than 2^54 calls from Dict() made of d[k] = v, delete!, pop! (both), get!, sizehint! (hints at most 2^61), empty!, filter! and map! returns the reference finite map's values and KeyErrors, and leaves a table whose keys are pairwise non-isequal, whose lookups, haskey and length agree with the reference map and whose iteration yields each reference pair exactly once."
    "Dict docstring base/dict.jl:31-64 and the docstrings of each call" ``DictOperationsAgree
    ``DictOperationsAgree_proven,
  proven "dicts-setindex-lookup" ["setindex!@347", "setindex!@359", "setindex!@374", "_setindex!@327"]
    "After d[k] = v, any key isequal to k finds v and every other lookup keeps its value; a converted key that is not isequal to the original throws KeyTypeError."
    "Dict docstring base/dict.jl:31-35; setindex! docstring" ``DictSetindexLookup
    ``DictSetindexLookup_proven,
  proven "dicts-delete-lookup" ["delete!@681", "_delete!@631"]
    "After delete!(d, k), keys isequal to k miss and every other lookup is unchanged."
    "delete! docstring base/dict.jl:658-679" ``DictDeleteLookup ``DictDeleteLookup_proven,
  proven "dicts-pop-key" ["pop!@586", "pop!@615", "_pop!@580"]
    "pop!(d, k) returns and deletes the stored value or throws KeyError; pop!(d, k, default) returns default and leaves d unchanged when k is absent."
    "pop! docstring base/dict.jl:591-612" ``DictPopKeyContract ``DictPopKeyContract_proven,
  proven "dicts-getbang-mutating-default" ["get!@445", "get!@457"]
    "get!(f, d, k) skips f when k is present; otherwise it calls f once and stores convert(V, f()) under k on top of every change f made to d."
    "get! docstring base/dict.jl:416-442; re-probe base/dict.jl:462-468" ``DictGetBangMutatingDefault
    ``DictGetBangMutatingDefault_proven,
  proven "dicts-sizehint-small" ["sizehint!@196", "rehash!@139"]
    "sizehint!(d, n; shrink) with n <= 2^61 (3n within Int) returns and keeps every pair, including shrinking hints."
    "sizehint! docstring base/array.jl:1581-1586; base/dict.jl:196-204" ``DictSizehintSmall
    ``DictSizehintSmall_proven,
  proven "dicts-empty" ["empty!@224", "isempty@712", "length@713"]
    "empty!(d) leaves a well-formed Dict with no pairs; isempty and length report the number of pairs."
    "empty! docstring base/dict.jl:206-223" ``DictEmptyContract ``DictEmptyContract_proven,
  proven "dicts-filter" ["filter!@725"]
    "filter!(pred, d) keeps exactly the pairs satisfying pred, for every hash including full collisions."
    "filter! docstring base/array.jl; base/dict.jl:725-733" ``DictFilterContract
    ``DictFilterContract_proven,
  proven "dicts-pop-any" ["pop!@620"]
    "pop!(d) on a non-empty Dict removes and returns one stored pair; on an empty Dict it throws ArgumentError."
    "pop! docstring base/array.jl; base/dict.jl:620-629" ``DictPopAnyContract
    ``DictPopAnyContract_proven,
  proven "dicts-float-keys-isequal" ["setindex!@359", "getindex@480", "get@507"]
    "Keys compare with isequal for every hash consistent with it: storing y after x overwrites x exactly when isequal(x, y) (so all Float64 NaNs are one key and 0.0 and -0.0 are two)."
    "Dict docstring base/dict.jl:35; Set docstring base/set.jl:30-36" ``DictSetindexLookup
    ``DictSetindexLookup_proven,
  refuted "dicts-immutabledict-lossy-key" ["ImmutableDict@782", "ImmutableDict@812", "setindex@886", "getindex@836"]
    "After d2 = ImmutableDict(d, key => value) or setindex(d, value, key), d2[key] is value."
    "ImmutableDict docstring base/dict.jl:785-797; setindex docstring base/dict.jl:868-885" ``ImmutableDictSetGet
    ``ImmutableDictSetGet_refuted
    "new(parent, key, value) converts the key without an isequal check: setindex(ImmutableDict{Float32,Int}(), 1, 0.1) stores Float32(0.1) and d2[0.1] throws KeyError.",
  refuted "dicts-persistentdict-nothrow" ["KeyValue.set@911", "_keyvalueset@913"]
    "KeyValue.set(dict::PersistentDict{K,V}, key::K, val::V), annotated @assume_effects :nothrow, returns for every key and value."
    "effect annotation base/dict.jl:911-912" ``PersistentSetNothrow ``PersistentSetNothrow_refuted
    "HAMT.insert! throws \"Perfect hash collision\" for a new key whose objectid equals a stored key's; the counterexample is a lawful trie of colliding Bool keys.",
  refuted "dicts-immutabledict-in-missing" ["in@817"]
    "in(key => value, d::ImmutableDict) with a value comparison returning missing returns missing for a stored key (three-valued logic) instead of throwing."
    "comparison docstring base/operators.jl:126-127; in(::Pair, ::AbstractDict) base/abstractdict.jl" ``ImmutableDictInMissing
    ``ImmutableDictInMissing_refuted
    "valcmp(value, dict.value) && return true throws TypeError when valcmp returns missing: (:a => missing) in ImmutableDict(:a => 1).",
  refuted "dicts-immutabledict-to-dict" ["Dict@91", "iterate@860", "get@843"]
    "Dict{K,V}(d) for an ImmutableDict d maps every key to d[key], its most recent value."
    "ImmutableDict docstring base/dict.jl:785-797; Dict docstring base/dict.jl:31-64" ``ImmutableDictToDict
    ``ImmutableDictToDict_refuted
    "Iteration is most recent first, so the constructor stores the oldest value last: Dict(ImmutableDict(:a => 1, :a => 2)) == Dict(:a => 1).",
  refuted "dicts-sizehint-wrap-hang" ["sizehint!@196", "rehash!@139"]
    "sizehint!(d, n; shrink) returns and keeps every pair for every Int n."
    "sizehint! docstring base/array.jl:1581-1586; base/dict.jl:196-204" ``DictSizehintTotal
    ``DictSizehintTotal_refuted
    "3 * 2^62 wraps to -2^62, so sizehint!(d, 2^62) on 17 pairs rehashes into 16 slots; Julia loops forever in rehash!.",
  proven "memsafety-dict-persistent-path" ["KeyValue.get@1033"]
    "KeyValue.get reads the leaf trie.data[i] only at the end of a path HAMT.path reports found and present, for a stored key, and returns its value."
    "base/dict.jl:1033-1045; base/hamt.jl:158-187" ``PersistentPathSafe ``PersistentPathSafe_proven,
  proven "memsafety-dict-probes" ["rehash!@139", "ht_keyindex@241", "ht_keyindex2_shorthash!@270"]
    "Every slot a linear probe computes, (index & (sz-1)) + 1, lies in 1:sz."
    "base/dict.jl:139-322" ``DictProbeSafe ``DictProbeSafe_proven,
  proven "dictscov-dict-construct" ["Dict@77", "Dict@83", "Dict@91", "Dict@99", "Dict@100", "Dict@109",
    "Dict@110", "copy@111", "Dict@115", "Dict@116", "Dict@118", "empty@120"]
    "Each Dict constructor builds a table representing the reference map of its converted pairs (later isequal keys win, first conversion error propagates); copy keeps the pairs and counters."
    "Dict docstring base/dict.jl:31-64" ``DictConstructionSemantics ``DictConstructionSemantics_proven,
  proven "dictscov-dict-slots" ["_shorthash7@123", "hashindex@128", "isslotempty@135", "isslotfilled@136", "isslotmissing@137"]
    "_shorthash7 is a filled slot byte holding the top seven hash bits, hashindex is hash mod sz plus one for power-of-two sizes, and the slot tests classify 0x00, 0x7f and 0x80-0xff."
    "invariant base/dict.jl:66,123-137" ``DictSlotSemantics ``DictSlotSemantics_proven,
  proven "dictscov-dict-keyindex" ["ht_keyindex@241", "ht_keyindex2_shorthash!@270", "ht_keyindex2!@325"]
    "ht_keyindex finds the slot of the stored key isequal to a query of any lawful type or returns -1; ht_keyindex2! returns a present key's slot or a free slot on its probe sequence of a table with the same pairs."
    "invariant base/dict.jl:241-325" ``DictProbeSemantics ``DictProbeSemantics_proven,
  proven "dictscov-dict-setindex" ["setindex!@347", "setindex!@359", "setindex!@374"]
    "setindex! converts the value to V and stores it under the key; the Dict{K,Any} method stores it unconverted; a key of another type is converted and must stay isequal, else KeyTypeError."
    "setindex! docstring; base/dict.jl:347-387" ``DictSetindexLookup ``DictSetindexLookup_proven,
  proven "dictscov-dict-getbang" ["get!@445", "get!@457"]
    "get!(f, h, key) returns a stored value without calling f, or stores and returns convert(V, f()); a foreign key goes through the setindex! key conversion."
    "get! docstring base/dict.jl:416-478" ``DictGetBangMutatingDefault
    ``DictGetBangMutatingDefault_proven,
  proven "dictscov-dict-lookup" ["getindex@480", "get@507", "get@529", "haskey@553", "in@554", "getkey@575"]
    "Dictionary lookups, membership and key retrieval agree with the reference map for queries of every lawful type."
    "docstrings base/dict.jl:485-578" ``DictLookupSemantics ``DictLookupSemantics_proven,
  proven "dictscov-dict-pop" ["_pop!@580", "pop!@586", "pop!@615", "_delete!@631"]
    "pop!(h, key) returns the stored value and removes the key or throws KeyError; pop!(h, key, default) returns default instead; _pop!/_delete! remove exactly the found pair."
    "pop! docstring base/dict.jl:591-687" ``DictPopKeyContract ``DictPopKeyContract_proven,
  proven "dictscov-dict-iterate" ["skip_deleted@689", "skip_deleted_floor!@698", "_iterate_dict@706",
    "iterate@707", "iterate@710", "iterate@717", "Iterators.only@715"]
    "skip_deleted returns the first filled slot at or after i (or 0), iteration of the Dict, its keys and its values yields each stored pair once, and only returns the single pair or throws ArgumentError."
    "keys docstring base/abstractdict.jl:86-91; base/dict.jl:689-723" ``DictIterationOnlySemantics
    ``DictIterationOnlySemantics_proven,
  proven "dictscov-dict-map-reduce" ["map!@741", "reduce@735"]
    "map!(f, values(d)) replaces each value v by f(v); reduce(merge, items) merges the items left to right into a Dict of the promoted types and throws ArgumentError for no items."
    "map! docstring base/abstractdict.jl; base/dict.jl:735-751" ``DictMapReduceMergeSemantics
    ``DictMapReduceMergeSemantics_proven,
  refuted "dictscov-show-limit-ellipsis" ["show@3"]
    "With :limit => true, show prints an ellipsis exactly when some pair is not shown."
    "IOContext :limit docstring base/show.jl:397-398; base/dict.jl:3-23" ``DictShowLimitEllipsis
    ``DictShowLimitEllipsis_refuted
    "The ellipsis is printed after the tenth pair even when the dictionary has exactly ten pairs.",
  proven "dictscov-dict-l83" ["Dict@83", "copy@111"]
    "Copying a Dict keeps every pair and the count, ndel and age fields."
    "base/dict.jl:83-86,111" ``DictCopySemantics ``DictCopySemantics_proven,
  proven "dictscov-dict-l91" ["Dict@91"]
    "Dict{K,V}(kv) stores the converted pairs in iteration order, later isequal keys winning, and throws the first conversion error."
    "Dict docstring; base/dict.jl:91-98" ``DictIteratorConstructorSemantics
    ``DictIteratorConstructorSemantics_proven,
  proven "dictscov-dict-l100" ["Dict@100"]
    "Dict{K,V}(ps::Pair...) stores the converted pairs in argument order, later isequal keys winning."
    "Dict docstring; base/dict.jl:100-107" ``DictConstructorSemantics ``DictConstructorSemantics_proven,
  proven "dictscov-dict-l99" ["Dict@99"]
    "Dict{K,V}(p::Pair) holds the converted pair or throws its conversion error."
    "Dict docstring; base/dict.jl:99" ``DictSinglePairConstructorSemantics
    ``DictSinglePairConstructorSemantics_proven,
  proven "dictscov-dict-l110" ["Dict@77", "Dict@109", "Dict@110", "empty@120"]
    "Dict{K,V}(), Dict(), Dict(()) and empty(a, K, V) are empty well-formed tables."
    "Dict docstring; base/dict.jl:77-82,109-110,120" ``DictEmptyConstructorSemantics
    ``DictEmptyConstructorSemantics_proven,
  proven "dictscov-dict-l374" ["setindex!@374"]
    "The Dict{K,Any} method stores the supplied value under the key without conversion."
    "base/dict.jl:374-387" ``DictSetindexLookup ``DictSetindexLookup_proven,
  proven "dictscov-dict-l135" ["isslotempty@135"] "A slot is empty exactly when its byte is 0x00."
    "base/dict.jl:135" ``DictSlots ``DictSlots_proven,
  proven "dictscov-dict-l136" ["isslotfilled@136"] "A slot is filled exactly when its high bit is set."
    "base/dict.jl:136" ``DictSlots ``DictSlots_proven,
  proven "dictscov-dict-l137" ["isslotmissing@137"] "A slot is deleted exactly when its byte is 0x7f."
    "base/dict.jl:137" ``DictSlots ``DictSlots_proven,
  proven "dictscov-dict-l507" ["get@507"] "get returns the stored value or the supplied default."
    "base/dict.jl:507-510" ``DictLookupSemantics ``DictLookupSemantics_proven,
  proven "dictscov-dict-l480" ["getindex@480"]
    "getindex returns the mapped value and throws KeyError for an absent key."
    "base/dict.jl:480-483" ``DictLookupSemantics ``DictLookupSemantics_proven,
  proven "dictscov-dict-l241" ["ht_keyindex@241"]
    "ht_keyindex returns the equal key's slot or -1 when absent."
    "base/dict.jl:241-263" ``DictProbeSemantics ``DictProbeSemantics_proven,
  proven "dictscov-dict-l128" ["hashindex@128"]
    "hashindex returns the one-based slot hash mod sz plus one and the short hash of the key."
    "base/dict.jl:128-133" ``DictHashindexSemantics ``DictHashindexSemantics_proven,
  proven "dictscov-dict-l115" ["Dict@115"]
    "Dict(ps::Pair{K,V}...) builds the same table as Dict{K,V}(ps)."
    "base/dict.jl:115" ``DictTypedPairListConstructorSemantics
    ``DictTypedPairListConstructorSemantics_proven,
  proven "dictscov-dict-l689" ["skip_deleted@689"]
    "skip_deleted returns the first filled slot at or after i, or zero when none remains."
    "base/dict.jl:689-697" ``DictIterationSemantics ``DictIterationSemantics_proven,
  proven "dictscov-dict-l631" ["_delete!@631"]
    "Deleting a filled slot removes its mapping and repairs tombstones without changing other mappings."
    "base/dict.jl:631-656" ``DictDeleteLookup ``DictDeleteLookup_proven,
  proven "dictscov-dict-l457" ["get!@457"]
    "get! returns an existing value without calling default, or stores and returns the converted default."
    "base/dict.jl:457-478" ``DictGetBangMutatingDefault ``DictGetBangMutatingDefault_proven,
  proven "dictscov-dict-l615" ["pop!@615"]
    "The default pop! removes and returns a found value and otherwise returns default."
    "base/dict.jl:615-618" ``DictPopKeyContract ``DictPopKeyContract_proven,
  proven "dictscov-dict-l575" ["getkey@575"]
    "getkey returns the stored equal key or the supplied default."
    "base/dict.jl:575-578" ``DictLookupSemantics ``DictLookupSemantics_proven,
  proven "dictscov-dict-l445" ["get!@445"]
    "A foreign get! key is converted and rejected with KeyTypeError when conversion changes its isequal identity."
    "base/dict.jl:445-455" ``DictGetBangMutatingDefault ``DictGetBangMutatingDefault_proven,
  proven "dictscov-dict-l123" ["_shorthash7@123"]
    "_shorthash7 stores the high seven bits of the hash with the filled marker set."
    "base/dict.jl:123" ``DictSlots ``DictSlots_proven,
  proven "dictscov-dict-l359" ["setindex!@359"]
    "setindex! stores the converted value under the key and keeps every other mapping."
    "base/dict.jl:359-372" ``DictSetindexLookup ``DictSetindexLookup_proven,
  proven "dictscov-dict-l327" ["_setindex!@327"]
    "Insertion at a free probe slot adds the pair, keeping the table well formed (count, age, idxfloor, rehash above the load threshold)."
    "base/dict.jl:327-345" ``DictSetindexLookup ``DictSetindexLookup_proven,
  proven "dictscov-dict-l586" ["pop!@586"]
    "pop! returns and removes a stored key's value, or throws KeyError when absent."
    "base/dict.jl:586-589" ``DictPopKeyContract ``DictPopKeyContract_proven,
  proven "dictscov-dict-l715" ["Iterators.only@715"]
    "Iterators.only returns the sole dictionary pair and throws ArgumentError unless the dictionary has one pair."
    "base/dict.jl:715" ``DictOnlyContract ``DictOnlyContract_proven,
  proven "dictscov-dict-l580" ["_pop!@580"]
    "_pop! returns the value of the indexed pair and deletes it."
    "base/dict.jl:580-584" ``DictPopKeyContract ``DictPopKeyContract_proven,
  proven "dictscov-dict-l554" ["in@554"]
    "Membership in keys(d) is true exactly when the dictionary holds an isequal key."
    "base/dict.jl:554" ``DictLookupSemantics ``DictLookupSemantics_proven,
  proven "dictscov-dict-l698" ["skip_deleted_floor!@698"]
    "skip_deleted_floor! advances idxfloor to the first filled slot and keeps the pairs."
    "base/dict.jl:698-704" ``DictIterationSemantics ``DictIterationSemantics_proven,
  proven "dictscov-dict-l347" ["setindex!@347"]
    "setindex! converts foreign keys and throws KeyTypeError when the conversion changes isequal identity."
    "base/dict.jl:347-357" ``DictSetindexLookup ``DictSetindexLookup_proven,
  proven "dictscov-dict-l712" ["isempty@712"]
    "A Dict is empty exactly when it holds no pairs."
    "base/dict.jl:712" ``DictEmptyContract ``DictEmptyContract_proven,
  proven "dictscov-dict-l553" ["haskey@553"]
    "haskey is true exactly when the dictionary holds an isequal key."
    "base/dict.jl:553" ``DictLookupSemantics ``DictLookupSemantics_proven,
  proven "dictscov-dict-l529" ["get@529"]
    "get(f, d, key) returns the stored value and calls f only when the key is absent."
    "base/dict.jl:529-532" ``DictLookupSemantics ``DictLookupSemantics_proven,
  proven "dictscov-dict-l735" ["reduce@735"]
    "reduce(merge, items) merges the items left to right into a Dict of the promoted key and value types and throws ArgumentError for no items."
    "merge docstring base/abstractdict.jl; base/dict.jl:735-739" ``DictReduceMergeSemantics
    ``DictReduceMergeSemantics_proven,
  proven "dictscov-dict-l741" ["map!@741"]
    "map!(f, values(d)) replaces each stored value v by f(v) and keeps the keys."
    "map! docstring base/abstractdict.jl; base/dict.jl:741-751" ``DictMapReduceSemantics
    ``DictMapReduceSemantics_proven,
  proven "dictscov-dict-immutable-construct" ["ImmutableDict@780", "ImmutableDict@781",
    "ImmutableDict@782", "ImmutableDict@811", "ImmutableDict@812", "ImmutableDict@813", "ImmutableDict@815"]
    "ImmutableDict constructors iterate the added pairs from most to least recent, followed by the parent's pairs, duplicates included; each added pair is converted to K => V."
    "ImmutableDict docstring base/dict.jl:785-808; base/dict.jl:780-815" ``ImmutableDictConstructorSemantics
    ``ImmutableDictConstructorSemantics_proven,
  proven "dictscov-dict-immutable-lookup" ["haskey@828", "getindex@836", "get@843", "get@851"]
    "ImmutableDict lookups return the most recent value of an isequal key; getindex throws KeyError and the get methods return their defaults only when no key matches."
    "ImmutableDict docstring base/dict.jl:785-797; base/dict.jl:828-857" ``ImmutableDictLookupSemantics
    ``ImmutableDictLookupSemantics_proven,
  proven "dictscov-dict-immutable-membership" ["in@817"]
    "Pair membership is true exactly when some stored pair matches the key (isequal) and the value (valcmp)."
    "ImmutableDict docstring base/dict.jl:794-795; base/dict.jl:817-826" ``ImmutableDictPairMembershipSemantics
    ``ImmutableDictPairMembershipSemantics_proven,
  proven "dictscov-dict-immutable-iteration" ["iterate@860", "length@864", "isempty@865", "empty@866"]
    "ImmutableDict length and isempty agree with iteration, which shows every pair including duplicates; empty has no pairs."
    "ImmutableDict docstring base/dict.jl:785-799; base/dict.jl:860-866" ``ImmutableDictCollectionSemantics
    ``ImmutableDictCollectionSemantics_proven,
  proven "dictscov-dict-immutable-similar" ["_similar_for@890", "_similar_for@891"]
    "A Pair element type gives an empty dictionary of the kind of the source (Dict, ImmutableDict, PersistentDict); other element types throw ArgumentError."
    "base/dict.jl:890-892" ``DictSimilarSemantics ``DictSimilarSemantics_proven,
  proven "dictscov-dict-persistent-construct" ["KeyValue.set@903", "KeyValue.set@906", "PersistentDict@969",
    "PersistentDict@970", "PersistentDict@976", "PersistentDict@992", "PersistentDict@1000"]
    "PersistentDict{K,V}() is empty; one-pair constructors hold their pair; multi-pair constructors hold the converted pairs, later === keys winning, and succeed without objectid collisions."
    "PersistentDict docstring base/dict.jl:936-965; base/dict.jl:903-908,969-1006" ``PersistentConstructorSemantics
    ``PersistentConstructorSemantics_proven,
  proven "dictscov-dict-persistent-set" ["KeyValue.set@909", "KeyValue.set@911", "_keyvalueset@913",
    "PersistentDict@982", "PersistentDict@983", "PersistentDict@986"]
    "A successful persistent insertion returns a dictionary with the new pair and every other pair; it succeeds exactly when no other stored key has the same objectid."
    "PersistentDict docstring base/dict.jl:939-944; base/dict.jl:909-919,982-990" ``PersistentSetSemantics
    ``PersistentSetSemantics_proven,
  proven "dictscov-dict-persistent-lookup" ["KeyValue.get@1033", "KeyValue.get@1047", "haskey@1017",
    "getindex@1021", "get@1027", "get@1053"]
    "PersistentDict lookups return the stored value of a === key, throw KeyError when required, and use defaults only for absent keys."
    "PersistentDict docstring; base/dict.jl:1017-1057" ``PersistentLookupSemantics
    ``PersistentLookupSemantics_proven,
  proven "dictscov-dict-persistent-membership" ["in@1010"]
    "Pair membership is false for an absent key and otherwise compares the stored value with valcmp."
    "base/dict.jl:1010-1015" ``PersistentPairMembershipSemantics
    ``PersistentPairMembershipSemantics_proven,
  proven "dictscov-dict-persistent-delete" ["KeyValue.set@920", "KeyValue.set@922", "_keyvalueset@924", "delete@1059"]
    "Deleting a persistent key returns a dictionary without it that keeps every other pair."
    "PersistentDict docstring base/dict.jl:959-960; base/dict.jl:920-933,1059-1061" ``PersistentDeleteSemantics
    ``PersistentDeleteSemantics_proven,
  proven "dictscov-dict-persistent-collection" ["eltype@1008", "iterate@1063", "length@1065", "isempty@1066", "empty@1067"]
    "PersistentDict iteration visits every pair once, length and isempty count them, eltype is Pair{K,V} and empty has no pairs."
    "PersistentDict docstring; base/dict.jl:1008,1063-1067" ``PersistentCollectionSemantics
    ``PersistentCollectionSemantics_proven,
  proven "dicts-source-mergewith" ["mergewith!@753"]
    "mergewith!(combine, d1, d2) merges the pairs of d2 in iteration order, combining the values of present keys with combine(old, new) and adding the others like setindex!, propagating the first error."
    "mergewith! docstring base/abstractdict.jl; base/dict.jl:753-774" ``DictMergewithSemantics
    ``DictMergewithSemantics_proven
]

end JuliaLean.Proofs.base.dict
