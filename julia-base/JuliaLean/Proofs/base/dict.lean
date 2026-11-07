import JuliaLean.base.dict
import JuliaLean.src.genericmemory_c
import JuliaLean.base.abstractdict
import JuliaLean.base.abstractset
import JuliaLean.base.checked
import JuliaLean.base.div
import JuliaLean.base.genericmemory
import JuliaLean.base.hamt
import JuliaLean.base.hashing
import JuliaLean.base.int
import JuliaLean.base.reduce
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

def TableszLaw (tablesz : Nat → Nat) : Prop := ∀ x, tablesz x = tableszSpec x

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

theorem IsPow.dvd64 {sz : Nat} (_h : IsPow sz) (_hs : True) : ∃ q, 2 ^ 64 * sz = sz * q :=
  ⟨2 ^ 64, Nat.mul_comm _ _⟩
theorem IsPow.double {sz : Nat} (h : IsPow sz) : IsPow (sz * 2) := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p + 1, by omega, (Nat.pow_succ 2 p).symm⟩

theorem IsPow.quad {sz : Nat} (h : IsPow sz) : IsPow (sz * 4) := by
  obtain ⟨p, hp, rfl⟩ := h
  refine ⟨p + 2, by omega, ?_⟩
  rw [Nat.pow_add]

theorem sub_mod_pow {sz d : Nat} (_h : IsPow sz) (_hs : True) (hd : 0 < d) (hd' : d ≤ sz) :
    (sz - d) % sz = sz - d := by
  exact Nat.mod_eq_of_lt (by omega)
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

theorem intBits64_of_nonneg {sz : Nat} {x : Int} (h0 : 0 ≤ x) (_h1 : x < (sz : Int)) :
    intBits64 sz x = x.toNat := by
  unfold intBits64
  omega

theorem intBits64_of_neg {sz : Nat} {x : Int} (h0 : -(sz : Int) ≤ x) (h1 : x < 0) :
    intBits64 sz x = (x + (sz : Int)).toNat := by
  unfold intBits64
  omega

theorem previousIndex_spec {sz i : Nat} (h : IsPow sz) (hs : True) (h1 : 1 ≤ i)
    (h2 : i ≤ sz) :
    (i = 1 ∧ previousIndex sz i = sz) ∨ (1 < i ∧ previousIndex sz i = i - 1) := by
  have h16 := h.ge
  unfold previousIndex
  rw [h.land]
  by_cases hi : i = 1
  · left
    refine ⟨hi, ?_⟩
    have hb : intBits64 sz ((i : Int) - 2) = sz - 1 := by
      rw [intBits64_of_neg (by omega) (by omega)]
      omega
    rw [hb, sub_mod_pow h hs (by omega) (by omega)]
    omega
  · right
    refine ⟨by omega, ?_⟩
    have hb : intBits64 sz ((i : Int) - 2) = i - 2 := by
      rw [intBits64_of_nonneg (by omega) (by omega)]
      omega
    rw [hb, Nat.mod_eq_of_lt (by omega)]
    omega

/-- `(index - index0) & (newsz-1)`, the probe length in `rehash!`. -/
def probeDist (newsz index index0 : Nat) : Nat :=
  Nat.land (intBits64 newsz ((index : Int) - (index0 : Int))) (newsz - 1)

theorem probeDist_spec {sz i j : Nat} (h : IsPow sz) (hs : True)
    (h1 : 1 ≤ i) (h2 : i ≤ sz) (h3 : 1 ≤ j) (h4 : j ≤ sz) :
    (j ≤ i ∧ probeDist sz i j = i - j) ∨ (i < j ∧ probeDist sz i j = i + sz - j) := by
  have h16 := h.ge
  unfold probeDist
  rw [h.land]
  by_cases hij : j ≤ i
  · left
    refine ⟨hij, ?_⟩
    have hb : intBits64 sz ((i : Int) - j) = i - j := by
      rw [intBits64_of_nonneg (by omega) (by omega)]
      omega
    rw [hb, Nat.mod_eq_of_lt (by omega)]
  · right
    refine ⟨by omega, ?_⟩
    have hb : intBits64 sz ((i : Int) - j) = sz - (j - i) := by
      rw [intBits64_of_neg (by omega) (by omega)]
      omega
    rw [hb, sub_mod_pow h hs (by omega) (by omega)]
    omega
/-- The home slot `hashindex(key, sz)[1]` of a key. -/
def home (hash : K → JInt .u64) (sz : Nat) (k : K) : Nat :=
  Nat.land (hash k).val.toNat ((JInt.lit .i64 (Int.ofNat sz)).val - 1).toNat + 1

theorem hashindex_fst (hash : K → JInt .u64) (k : K) (sz : Nat) :
    home hash sz k =
      Nat.land (hash k).val.toNat ((JInt.lit .i64 (Int.ofNat sz)).val - 1).toNat + 1 := rfl

theorem home_range {sz : Nat} (h : IsPow sz) (hash : K → JInt .u64) (k : K) :
    1 ≤ home hash sz k ∧ home hash sz k ≤ sz := by
  unfold home
  have h16 := h.ge
  have hle : Nat.land (hash k).val.toNat ((JInt.lit .i64 (Int.ofNat sz)).val - 1).toNat ≤
      ((JInt.lit .i64 (Int.ofNat sz)).val - 1).toNat := Nat.and_le_right
  have hval : ((JInt.lit .i64 (Int.ofNat sz)).val - 1).toNat ≤ sz - 1 := by
    by_cases hlt : (sz : Int) < 2 ^ 63
    · have hw : (JInt.lit .i64 (Int.ofNat sz)).val = (sz : Int) := by
        unfold JInt.lit JInt.wrap
        exact wrapInt_of_inRange .i64 (sz : Int)
          ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits],
           by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩
      rw [hw]
      omega
    · have hb := (JInt.lit .i64 (Int.ofNat sz)).property
      have hmax : IntTy.max .i64 = 2 ^ 63 - 1 := by decide
      omega
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

theorem probeDist_pr {sz home d : Nat} (h : IsPow sz) (hs : True) (h1 : 1 ≤ home)
    (h2 : home ≤ sz) (hd : d < sz) : probeDist sz (pr sz home d) home = d := by
  have := pr_spec h h1 h2 d hd
  have hr := pr_range h h1 h2 hd
  have := probeDist_spec h hs hr.1 hr.2 h1 h2
  omega

theorem nextIndex_previousIndex {sz i : Nat} (h : IsPow sz) (hs : True) (h1 : 1 ≤ i)
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
  sizeLe : 0 ≤ t.size
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
  unfold home
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
    unfold home; rw [hhash]
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
    (hp : IsPow newsz) (hle : True) : AccOK hash eqKey t newsz 0 acc0 := by
  have hnil : tlist (accT newsz (acc0 : RehashAcc K V)) = [] :=
    filterMap_ent_nil (t := accT newsz acc0) newsz 1 (fun _ _ _ => filledB_zero)
  refine ⟨⟨Or.inr hp, Nat.zero_le _, fun i _ _ => Or.inl rfl, ?_, ?_, Or.inr ?_, Nat.le_refl _, ?_,
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
  have hp' : rehashProbe acc.slots newsz newsz
      (Nat.land (hash k).val.toNat ((JInt.lit .i64 (Int.ofNat newsz)).val - 1).toNat + 1) =
      some index := hp
  simp only [rehashCopyLoop, hashindex, DictInteger.toInt, bind, Except.bind, pure, Except.pure, hf', ite_true, hk, hv]
  rw [hp']
  rfl

theorem rehashCopyLoop_no_undef {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {t : DictState K V} (hi : Inv hash eqKey t) (newsz : Nat) :
    ∀ r i (acc : RehashAcc K V), 1 ≤ i → i + r = t.size + 1 →
      rehashCopyLoop hash newsz t.slots t.keys t.vals r i acc ≠ .error .undefRef
  | 0, _, _, _, _ => nofun
  | r + 1, i, acc, h1, hr => by
    unfold rehashCopyLoop
    by_cases hf : (Nat.land (t.slots i) 0x80 != 0) = true
    · obtain ⟨k, v, hk, hv, -⟩ := hi.filled h1 (by omega) hf
      simp only [hf, ite_true, hk, hv, hashindex, DictInteger.toInt, bind, Except.bind, pure, Except.pure]
      cases rehashProbe acc.slots newsz newsz
          (Nat.land (hash k).val.toNat ((JInt.lit .i64 (Int.ofNat newsz)).val - 1).toNat + 1) with
      | none => nofun
      | some idx => exact rehashCopyLoop_no_undef hi newsz r (i + 1) _ (by omega) (by omega)
    · simp only [hf, Bool.false_eq_true, ite_false]
      exact rehashCopyLoop_no_undef hi newsz r (i + 1) acc (by omega) (by omega)

theorem rehash_no_undef {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {tablesz : Nat → Nat} {t : DictState K V} (hi : Inv hash eqKey t) (newsz0 : Nat) :
    rehash hash tablesz t newsz0 ≠ .error .undefRef := by
  unfold rehash
  dsimp only
  split
  · nofun
  · have hnu := rehashCopyLoop_no_undef hi (tablesz newsz0) t.size 1 acc0 (Nat.le_refl _) (by omega)
    cases hloop : rehashCopyLoop hash (tablesz newsz0) t.slots t.keys t.vals t.size 1 acc0 with
    | error e =>
      intro he
      have : e = .undefRef := by cases he; rfl
      subst this
      exact hnu hloop
    | ok acc =>
      dsimp only [bind, Except.bind]
      split <;> nofun

/-- One step of the copy loop. -/
theorem rehashStep_ok {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    (hi : Inv hash eqKey t) {newsz : Nat} (hp : IsPow newsz)
    (hle : True) (hgt : t.count < newsz) {n : Nat} (hn : n < t.size)
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
    have hdist := probeDist_pr hp trivial hhr.1 hhr.2 (show d < newsz by omega)
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
    refine ⟨⟨Or.inr hp, Nat.zero_le _, ?_, ?_, ?_, Or.inr ?_, Nat.le_refl _, fun _ h _ _ => h, Nat.le_refl _⟩,
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
    (hi : Inv hash eqKey t) {newsz : Nat} (hp : IsPow newsz) (hle : True)
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
    (_h62 : True) (hgt : t.count < tableszSpec newsz0) :
    ∃ t', rehash hash tablesz t newsz0 = .ok t' ∧ Inv hash eqKey t' ∧
      List.Perm (tlist t') (tlist t) ∧ t'.size = tableszSpec newsz0 ∧ t'.count = t.count ∧
      t'.age = (if t.count = 0 then bumpAge t.age else bumpAge (bumpAge t.age)) := by
  have hp := tableszSpec_pow newsz0
  have hle : True := trivial
  have htab : tablesz newsz0 = tableszSpec newsz0 := htz newsz0
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
      simp only [ne_eq, not_true_eq_false, ite_false]
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
          .ok (-((home hashQ t1.size q : Nat) : Int), shorthash7 (hashQ q), t1))
      else (keyindex2Loop1 matchQ q t (shorthash7 (hashQ q)) t.size (t.maxprobe + 1) 0
          (home hashQ t.size q) 0 >>=
        k2tail hashS hashQ matchQ tablesz fuel t q (shorthash7 (hashQ q))) := by
  rw [htKeyindex2Loop]
  by_cases h0 : (t.size == 0) = true
  · rw [ite_eq_left h0, ite_eq_left h0]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    show (keyindex2Loop1 matchQ q t (shorthash7 (hashQ q)) t.size (t.maxprobe + 1) 0
      (home hashQ t.size q) 0 >>= fun r => _) = _
    cases keyindex2Loop1 matchQ q t (shorthash7 (hashQ q)) t.size (t.maxprobe + 1) 0
      (home hashQ t.size q) 0 with
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
  have hh : home hashQ t.size q = home hash t.size k := by unfold home; rw [hhash]
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
      True → (t.size = 0 ∨ 64 * t.count < t.size * 2 ^ f') →
      ∃ idx t' n, htKeyindex2Loop hash hashQ matchQ tablesz fuel t q =
          .ok (idx, shorthash7 (hashQ q), t') ∧
        n ≤ 2 * f' + 2 ∧ K2Out hash eqKey hashQ matchQ t q idx t' n)
    (fuel : Nat) (t : DictState K V) (hfuel : f < fuel) (hi : Inv hash eqKey t)
    (hc : True) (hf : t.size = 0 ∨ 64 * t.count < t.size * 2 ^ f) :
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
      rehash_spec htz hi 4 trivial (by rw [tableszSpec_four]; omega)
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
    have hshq : shorthash7 (hashQ q) = shorthash7 (hashQ q) := rfl
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
              (if t.count > 64000 then t.size * 2 else t.size * 4) trivial
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
              IH f rfl fuel' t1 (by omega) hi1 trivial hf1
            refine ⟨idx, t2, 2 + n1, h2', by omega, ⟨hout.inv, hout.perm.trans hp1,
              hout.count.trans hc1, ?_, fun i e h1 h2 he hm => (hnf i e h1 h2 he hm).elim,
              fun _ => hout.absent (fun e he => habs e (hp1.mem_iff.1 he))⟩⟩
            exact (AgeStep.of_pos (by rw [ha1, ite_eq_right hc0, bump_bump]) (by omega)).trans
              hout.age

theorem htKeyindex2_spec (hl : KeyLaws hash eqKey) {Q : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ) {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) (q : Q) :
    ∀ f fuel (t : DictState K V), f < fuel → Inv hash eqKey t → True →
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
    (hc : True) (q : Q) :
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
    (hc : True) (q : K) :
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
      if (JInt.lit .i64 (Int.ofNat (storeAt t v k j sh).count) +
          JInt.lit .i64 (Int.ofNat (storeAt t v k j sh).ndel)) * JInt.lit .i64 3 >
          JInt.lit .i64 (Int.ofNat (storeAt t v k j sh).size) * JInt.lit .i64 2 then
        rehash hash tablesz (storeAt t v k j sh)
          (if (storeAt t v k j sh).count > 64000 then (storeAt t v k j sh).count * 2
            else max ((storeAt t v k j sh).count * 4) 4) >>= fun t' => .ok ((), t')
      else .ok ((), storeAt t v k j sh) := rfl

/-- `_setindex!(h, v, key, index, sh)` at a free slot of the probe sequence of an absent key
stores the pair, and its rehash keeps every pair. -/
theorem setindexAt_spec (hl : KeyLaws hash eqKey) {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) {t : DictState K V} (hi : Inv hash eqKey t) (_hc : True)
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
    obtain ⟨t2, h2, hi2, hp2, -, hc2, ha2⟩ := rehash_spec htz hi1 N trivial (by omega)
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
    (_hc : True) {k : K} {v : V} {idx : Int} {n : Nat}
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
      trivial hslot habs1 (v := v)
    rw [bind_of_ok h']
    refine ⟨t', rfl, hi', ?_, ?_⟩
    · refine hp'.trans ((hout.perm.cons _).trans ?_)
      unfold rset
      rw [rdel_absent habs]
    · rcases ha' with h | h
      · exact ⟨1, by omega, by omega, h⟩
      · exact ⟨3, by omega, by omega, h⟩

theorem setindexAny_eq {W : Type} [AnyValue W V] (tablesz : Nat → Nat) (t : DictState K V)
    (w : W) (k : K) :
    setindexAny hash eqKey tablesz t w k =
      (htKeyindex2 hash eqKey tablesz t k >>= fun r =>
        storeBody hash tablesz r.2.2 (AnyValue.toAny w) k r.1 r.2.1) := by
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
    {t : DictState K V} {m : List (K × V)} (h : DictRep hash eqKey t m) (hc : True)
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
  ∀ h0 w h2, Inv hash eqKey h0 → True → default h0 = .ok (w, h2) →
    Inv hash eqKey h2 ∧ True ∧ ∃ n, n < 2 ^ 64 ∧ AgeStep h0 h2 n

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
    (h : DictRep hash eqKey t m) (hc : True) (k : K)
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
    · obtain ⟨hi2, hc2, n2, hn2, hage2⟩ := hdef t1 w t2 hout.inv trivial hw
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

theorem bk_range {sz i : Nat} (h : IsPow sz) (hs : True) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    ∀ r, 1 ≤ bk sz i r ∧ bk sz i r ≤ sz
  | 0 => ⟨h1, h2⟩
  | r + 1 => by
    have ih := bk_range h hs h1 h2 r
    exact (nextIndex_previousIndex h hs ih.1 ih.2).2

theorem next_bk {sz i : Nat} (h : IsPow sz) (hs : True) (h1 : 1 ≤ i) (h2 : i ≤ sz)
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
theorem pr_bk {sz i hh e r : Nat} (hp : IsPow sz) (hs : True) (h1 : 1 ≤ i) (h2 : i ≤ sz)
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
  have hs64 : True := trivial
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
    (huv : UnsetLaw unsetVal) {Q D : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (q : Q) (d : D) :
    match rfind matchQ m q with
    | some e => ∃ t', JuliaLean.base.dict.popDefault hashQ matchQ unsetKey unsetVal t q d =
          .ok (.inl e.2, t') ∧ DictRep hash eqKey t' (rdel matchQ m q)
    | none => JuliaLean.base.dict.popDefault hashQ matchQ unsetKey unsetVal t q d = .ok (.inr d, t) := by
  have hp := h.probe hl hq q
  unfold JuliaLean.base.dict.popDefault
  cases hf : rfind matchQ m q with
  | some e =>
    rw [hf] at hp
    obtain ⟨i, hidx, h1, h2, he, hm⟩ := hp
    rw [hidx, except_ok_bind, if_pos (by omega), show ((i : Nat) : Int).toNat = i by omega]
    obtain ⟨k0, v0⟩ := e
    unfold popAt
    rw [valAt_of_ent he, except_ok_bind, except_ok_bind]
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
theorem DictRep.lookups (hl : KeyLaws hash eqKey) {Q D DK DF : Type} {hashQ : Q → JInt .u64}
    {matchQ : Q → K → Bool} (hq : QueryLaws hash eqKey hashQ matchQ) {t : DictState K V}
    {m : List (K × V)} (h : DictRep hash eqKey t m) (q : Q) (default : D) (defaultKey : DK)
    (defaultF : Unit → DictResult DF) :
    getindex hashQ matchQ t q =
        (match rlookup matchQ m q with | some v => .ok v | none => .error .keyError) ∧
      JuliaLean.base.dict.get hashQ matchQ t q default =
        .ok (match rlookup matchQ m q with | some v => .inl v | none => .inr default) ∧
      getF hashQ matchQ t q defaultF =
        (match rlookup matchQ m q with | some v => .ok (.inl v) | none => .inr <$> defaultF ()) ∧
      haskey hashQ matchQ t q = .ok (rlookup matchQ m q).isSome ∧
      inKeySet hashQ matchQ ⟨t⟩ q = .ok (rlookup matchQ m q).isSome ∧
      getkey hashQ matchQ t q defaultKey =
        .ok (match rfind matchQ m q with | some e => .inl e.1 | none => .inr defaultKey) := by
  have hp := h.probe hl hq q
  rw [rlookup_of_rfind]
  unfold getindex JuliaLean.base.dict.get getF haskey inKeySet getkey
  cases hf : rfind matchQ m q with
  | some e =>
    rw [hf] at hp
    obtain ⟨i, hidx, h1, h2, he, -⟩ := hp
    obtain ⟨k, v⟩ := e
    have hti : ((i : Nat) : Int).toNat = i := by omega
    simp only [hidx, except_ok_bind, Option.map_some, Option.isSome_some]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hti,
      valAt_of_ent he, keyAt_of_ent he]
    refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩ <;> simp
  | none =>
    rw [hf] at hp
    simp only [hp.1, except_ok_bind, Option.map_none, Option.isSome_none]
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
    (hc : t.count ≤ 2 ^ 61) : t.count ≤ maxValues := by
  rcases hmv with h | h
  · have : (2 : Nat) ^ 61 ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  · have hp := tlist_pairwise hi
    have := h ((tlist t).map Prod.fst) (List.pairwise_map.2 hp)
    rw [List.length_map, ← hi.count] at this
    exact this

/-- `sizehint!(d, n; shrink)` with a hint that does not overflow keeps every pair. -/
theorem sizehint_spec {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat}
    (htz : TableszLaw tablesz) {maxValues : Nat} (hmv : MaxValuesLaw eqKey maxValues)
    {cld : JInt .i64 → JInt .i64} (hcld : CldLaw cld) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (hc : t.count ≤ 2 ^ 61) (n : JInt .i64) (hn : n.val ≤ 2 ^ 61)
    (shrink : Bool) :
    ∃ t', sizehint hash tablesz maxValues (fun x => .ok (cld x)) t n shrink = .ok t' ∧ DictRep hash eqKey t' m ∧
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
  have hN : tablesz Y.val.toNat = tableszSpec Y.val.toNat := htz _
  have hN62 : True := trivial
  have hNge := tableszSpec_ge Y.val.toNat
  have hN16 := (tableszSpec_pow Y.val.toNat).ge
  have hgt : t.count < tableszSpec (tableszSpec Y.val.toNat) := by
    rw [tableszSpec_of_pow (tableszSpec_pow _)]
    omega
  unfold sizehint
  simp only [DictInteger.toInt, except_ok_bind]
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

/-- The pairs yielded by `iterate(kv)` followed by `iterate(kv, state)` with `fuel` steps. -/
def iterCollectPairs {Q W C S : Type}
    (iterate : C → Option S → DictResult (Option ((Q × W) × S))) (kv : C) :
    Nat → Option S → DictResult (List (Q × W))
  | 0, _ => .ok []
  | fuel + 1, state => do
    match ← iterate kv state with
    | none => .ok []
    | some (pair, nextState) =>
      let rest ← iterCollectPairs iterate kv fuel (some nextState)
      .ok (pair :: rest)

theorem iterCollectPairs_listIterate_aux {Q W : Type} (xs : List (Q × W)) :
    ∀ (rest : List (Q × W)) (fuel : Nat), rest.length < fuel →
      iterCollectPairs listIterate xs fuel (some rest) = .ok rest
  | [], _ + 1, _ => rfl
  | a :: as, n + 1, h => by
    simp only [List.length_cons] at h
    rw [iterCollectPairs]
    change (Except.ok (some (a, as)) >>= fun x => _) = Except.ok (a :: as)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [iterCollectPairs_listIterate_aux xs as n (by omega)]

theorem iterCollectPairs_listIterate {Q W : Type} (xs : List (Q × W)) :
    iterCollectPairs listIterate xs (xs.length + 1) none = .ok xs := by
  cases xs with
  | nil => rfl
  | cons a as =>
    rw [iterCollectPairs]
    change (Except.ok (some (a, as)) >>= fun x => _) = Except.ok (a :: as)
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [iterCollectPairs_listIterate_aux (a :: as) as (a :: as).length (Nat.lt_succ_self _)]

section Ctor
variable {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat}

/-- `h[k] = v` for converted pairs, as one step of the reference fold. -/
theorem DictRep.setConv (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (hc : True) (p : Q × W) :
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
      True →
      match pairs.foldlM (refStep eqKey keyConv valueConv) m with
      | .ok m' => ∃ t', loop pairs t = .ok t' ∧ DictRep hash eqKey t' m'
      | .error e => loop pairs t = .error e
  | [], t, m, h, _ => by
    show ∃ t', loop [] t = .ok t' ∧ DictRep hash eqKey t' m
    exact ⟨t, hnil t, h⟩
  | p :: rest, t, m, h, hc => by
    rw [List.foldlM_cons, hcons]
    have hs := h.setConv hl htz keyConv valueConv trivial p
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
        trivial

theorem dictInsertLoop_of_collect (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz)
    {Q W C S : Type} (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (iterate : C → Option S → DictResult (Option ((Q × W) × S))) (kv : C) :
    ∀ (fuel : Nat) (state : Option S) (pairs : List (Q × W))
      (t : DictState K V) (m : List (K × V)),
      iterCollectPairs iterate kv fuel state = .ok pairs →
      DictRep hash eqKey t m →
      match pairs.foldlM (refStep eqKey keyConv valueConv) m with
      | .ok m' => ∃ t', dictInsertLoop hash eqKey tablesz keyConv valueConv iterate kv fuel state t = .ok t' ∧
          DictRep hash eqKey t' m'
      | .error e => dictInsertLoop hash eqKey tablesz keyConv valueConv iterate kv fuel state t = .error e
  | 0, state, pairs, t, m, hcol, ht => by
    cases hcol
    exact ⟨t, rfl, ht⟩
  | fuel + 1, state, pairs, t, m, hcol, ht => by
    rw [iterCollectPairs] at hcol
    rw [dictInsertLoop]
    cases hit : iterate kv state with
    | error e => rw [hit] at hcol; cases hcol
    | ok step =>
      rw [hit] at hcol
      dsimp only [bind, Except.bind, pure, Except.pure] at hcol ⊢
      cases step with
      | none =>
        cases hcol
        exact ⟨t, rfl, ht⟩
      | some ps =>
        obtain ⟨⟨q, w⟩, nextState⟩ := ps
        dsimp only [bind, Except.bind, pure, Except.pure] at hcol ⊢
        cases hrest : iterCollectPairs iterate kv fuel (some nextState) with
        | error e => rw [hrest] at hcol; cases hcol
        | ok rest =>
          rw [hrest] at hcol
          cases hcol
          rw [List.foldlM_cons]
          have hs := ht.setConv hl htz keyConv valueConv trivial (q, w)
          cases hr : refStep eqKey keyConv valueConv m (q, w) with
          | error e =>
            rw [hr] at hs
            rw [hs]
            rfl
          | ok m1 =>
            rw [hr] at hs
            obtain ⟨t1, h1, hrep1⟩ := hs
            rw [h1]
            dsimp only [bind, Except.bind]
            exact dictInsertLoop_of_collect hl htz keyConv valueConv iterate kv fuel
              (some nextState) rest t1 m1 hrest hrep1
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
theorem mapValuesLoop_spec {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {W : Type} (valueConv : ValueConv W V) (f : V → DictResult W) (g : V → V)
    (hg : ∀ v, (f v >>= convertValue valueConv) = .ok (g v))
    {t : DictState K V} :
    ∀ n i (h : DictState K V), h.size = t.size → h.slots = t.slots → h.keys = t.keys →
      h.count = t.count → h.maxprobe = t.maxprobe → h.idxfloor = t.idxfloor →
      h.popcursor = t.popcursor → Inv hash eqKey t → 1 ≤ i → i + n = t.size + 1 →
      (∀ p, 1 ≤ p → p < i → ent h p = (ent t p).map (fun e => (e.1, g e.2))) →
      (∀ p, i ≤ p → p ≤ t.size → ent h p = ent t p) →
      ∃ h', mapValuesLoop valueConv f h n i = .ok h' ∧ h'.size = t.size ∧
        h'.slots = t.slots ∧ h'.keys = t.keys ∧ h'.count = t.count ∧ h'.maxprobe = t.maxprobe ∧
        h'.idxfloor = t.idxfloor ∧ h'.popcursor = t.popcursor ∧
        ∀ p, 1 ≤ p → p ≤ t.size → ent h' p = (ent t p).map (fun e => (e.1, g e.2))
  | 0, i, h, hs, hsl, hk, hc, hm, hf, hp, _, _, hn, hlt, _ =>
    ⟨h, rfl, hs, hsl, hk, hc, hm, hf, hp, fun p h1 h2 => hlt p h1 (by omega)⟩
  | n + 1, i, h, hs, hsl, hk, hc, hm, hf, hp, hi, h1, hn, hlt, hge => by
    have hstep : mapValuesLoop valueConv f h (n + 1) i =
        if isslotfilled h i then
          (valAt h i >>= fun value => (f value >>= convertValue valueConv) >>= fun value =>
            mapValuesLoop valueConv f
              (DictState.mk h.size h.slots h.keys (updateAt h.vals i (some value)) h.ndel h.count
                h.age h.idxfloor h.maxprobe h.popcursor) n (i + 1))
        else mapValuesLoop valueConv f h n (i + 1) := by
      rw [mapValuesLoop]
      split
      · cases valAt h i with
        | error e => rfl
        | ok v =>
          dsimp only [bind, Except.bind]
          cases f v <;> rfl
      · rfl
    rw [hstep, isslotfilled_eq]
    by_cases hfl : filledB (h.slots i) = true
    · rw [if_pos hfl]
      have hti : filledB (t.slots i) = true := by rw [← hsl]; exact hfl
      obtain ⟨k, v, -, -, he, -, -⟩ := hi.filled h1 (by omega) hti
      have heh : ent h i = some (k, v) := by rw [hge i (Nat.le_refl _) (by omega)]; exact he
      rw [valAt_of_ent heh, except_ok_bind, hg v, except_ok_bind]
      refine mapValuesLoop_spec valueConv f g hg n (i + 1) _ hs hsl hk hc hm hf hp hi (by omega) (by omega)
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
      refine mapValuesLoop_spec valueConv f g hg n (i + 1) h hs hsl hk hc hm hf hp hi (by omega) (by omega)
        (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => hge p (by omega) hp2)
      by_cases hpi : p = i
      · subst hpi
        rw [ent_of_not_filled hfl', ← hge p (Nat.le_refl _) (by omega), ent_of_not_filled hfl']
        rfl
      · exact hlt p hp1 (by omega)

/-- `map!(f, values(d))` with a returning `f` replaces every stored value `v` by the converted `f(v)`. -/
theorem DictRep.mapBang {hash : K → JInt .u64} {eqKey : K → K → Bool} {t : DictState K V}
    {m : List (K × V)} (h : DictRep hash eqKey t m) {W : Type} (valueConv : ValueConv W V)
    (f : V → DictResult W) (g : V → V) (hg : ∀ v, (f v >>= convertValue valueConv) = .ok (g v)) :
    ∃ t', JuliaLean.base.dict.mapBang valueConv f ⟨t⟩ = .ok ⟨t'⟩ ∧
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
    obtain ⟨t', ht', hs, hsl, hk, hc, hm, hf, hp, he⟩ := mapValuesLoop_spec valueConv f g hg
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
theorem rlookup_rset {hash : K → JInt .u64} {eqKey : K → K → Bool} (hl : KeyLaws hash eqKey)
    (m : List (K × V)) (k q : K) (v : V) :
    rlookup eqKey (rset eqKey m k v) q =
      if eqKey q k then some v else rlookup eqKey m q := by
  unfold rlookup rfind rset rdel
  rw [List.find?_cons]
  by_cases hqk : eqKey q k = true
  · rw [hqk]; rfl
  · have hqf : eqKey q k = false := by simpa using hqk
    rw [hqf]
    dsimp only
    congr 1
    induction m with
    | nil => rfl
    | cons e rest ih =>
      by_cases hke : eqKey k e.1 = true
      · have hqe : eqKey q e.1 = false := by
          cases h : eqKey q e.1
          · rfl
          · exact absurd (hl.trans q e.1 k h (hl.symm k e.1 hke)) (by rw [hqf]; decide)
        simp [List.filter, hke, List.find?_cons, hqe, ih]
      · have hkef : eqKey k e.1 = false := by simpa using hke
        simp only [List.filter, hkef, Bool.not_false, List.find?_cons]
        cases eqKey q e.1 <;> simp [ih]

def DictSetindexLookup : Prop :=
  ∀ (K V Q W D : Type) [AnyValue W V] (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (tablesz : Nat → Nat) (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → TableszLaw tablesz → DictRep hash eqKey h m →
    (∀ (key : K) (value : V) (j : Nat),
      InsertSlot h (home hash h.size key) j → Absent eqKey h key →
      ∃ h', setindexAt hash tablesz h value key j = .ok ((), h') ∧
        DictRep hash eqKey h' ((key, value) :: m)) ∧
    (∀ (key : K) (w : W), ∃ h', setindexAny hash eqKey tablesz h w key = .ok h' ∧
      DictRep hash eqKey h' (rset eqKey m key (AnyValue.toAny w))) ∧
    (∀ (key : K) (w : W) (q : K) (default : D), match convertValue valueConv w with
      | .ok v => ∃ h', setindexTyped hash eqKey tablesz valueConv h w key = .ok h' ∧
          DictRep hash eqKey h' (rset eqKey m key v) ∧
          getindex hash eqKey h' q =
            (if eqKey q key then .ok v
             else match rlookup eqKey m q with | some v0 => .ok v0 | none => .error .keyError) ∧
          JuliaLean.base.dict.get hash eqKey h' q default =
            .ok (if eqKey q key then .inl v
                 else match rlookup eqKey m q with | some v0 => .inl v0 | none => .inr default)
      | .error e => setindexTyped hash eqKey tablesz valueConv h w key = .error e) ∧
    (∀ (key0 : Q) (w : W), match refStep eqKey keyConv valueConv m (key0, w) with
      | .ok m' => ∃ h', setindexConv hash eqKey tablesz keyConv valueConv h w key0 = .ok h' ∧
          DictRep hash eqKey h' m'
      | .error e => setindexConv hash eqKey tablesz keyConv valueConv h w key0 = .error e)

theorem DictSetindexLookup_proven : DictSetindexLookup := by
  intro K V Q W D _ hash eqKey tablesz keyConv valueConv h m hl htz hr
  refine ⟨fun key value j hj habs => ?_, fun key w => ?_, fun key w q default => ?_,
    fun key0 w => hr.setConv hl htz keyConv valueConv trivial (key0, w)⟩
  · obtain ⟨h', h1, hi', hp', -⟩ := setindexAt_spec hl htz hr.1 trivial hj habs (v := value)
    exact ⟨h', h1, hi', hp'.trans (hr.2.cons _)⟩
  · rw [setindexAny_eq]; exact hr.store hl htz trivial key (AnyValue.toAny w)
  · rw [setindexTyped_eq]
    cases convertValue valueConv w with
    | error e => rfl
    | ok v =>
      rw [except_ok_bind]
      obtain ⟨h', hs, hr'⟩ := hr.store hl htz trivial key v
      obtain ⟨hgi, hget, -⟩ := hr'.lookups hl hl.query q default q (fun _ => .ok default)
      rw [rlookup_rset hl m key q v] at hgi hget
      refine ⟨h', hs, hr', ?_, ?_⟩
      · rw [hgi]; cases eqKey q key <;> rfl
      · rw [hget]; cases eqKey q key <;> rfl

/-- `ht_keyindex(h, key)` returns the slot of the stored key `isequal` to `key`, or `-1`;
`ht_keyindex2_shorthash!(h, key)` returns that slot without changing the table, or a negative free
slot on the key's probe sequence of a table (possibly rehashed or with a larger `maxprobe`) holding
the same pairs, with the short hash of `key`; `ht_keyindex2!` returns the same index. -/
def DictProbeSemantics : Prop :=
  ∀ (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (tablesz : Nat → Nat) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → TableszLaw tablesz →
    DictRep hash eqKey h m →
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
  intro K V Q hash eqKey hashQ matchQ tablesz h m hl hq htz hr
  refine ⟨fun q => ⟨hr.htKeyindex hl hq q, ?_⟩, fun k => ?_⟩
  · obtain ⟨idx, t', n, hprobe, -, hout⟩ := htKeyindex2Query_spec hl hq htz hr.1 trivial q
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
  · obtain ⟨idx, t', n, hprobe, -, -⟩ := htKeyindex2_spec' hl htz hr.1 trivial k
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
  ∀ (K V Q D : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → UnsetLaw unsetKey →
    UnsetLaw unsetVal → DictRep hash eqKey h m → ∀ (q : Q) (default : D),
    (match rfind matchQ m q with
      | some e => ∃ h', popKey hashQ matchQ unsetKey unsetVal h q = .ok (e.2, h') ∧
          DictRep hash eqKey h' (rdel matchQ m q)
      | none => popKey hashQ matchQ unsetKey unsetVal h q = .error .keyError) ∧
    (match rfind matchQ m q with
      | some e => ∃ h', popDefault hashQ matchQ unsetKey unsetVal h q default = .ok (.inl e.2, h') ∧
          DictRep hash eqKey h' (rdel matchQ m q)
      | none => popDefault hashQ matchQ unsetKey unsetVal h q default = .ok (.inr default, h))

theorem DictPopKeyContract_proven : DictPopKeyContract := by
  intro K V Q D hash eqKey hashQ matchQ unsetKey unsetVal h m hl hq huk huv hr q default
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

/-- `sizehint!(d, n; shrink)` converts any `Integer` `n` to `Int` (propagating `InexactError`),
and when `3 * newsz` fits in `Int` (`h.count ≤ 2^61` and `n ≤ 2^61`) returns and keeps every pair;
`rehash!(d, newsz)` keeps every pair when `d.count < _tablesz(newsz)` and throws a concurrent-write
error if `h.age` changes during the copy loop. -/
def DictSizehintSmall : Prop :=
  ∀ (K V I : Type) [DictInteger I] (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (tablesz : Nat → Nat) (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (h : DictState K V) (m : List (K × V)),
    TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    DictRep hash eqKey h m →
    (∀ (n : I) (shrink : Bool) (err : DictError),
      DictInteger.toInt n = .error err →
      sizehint hash tablesz maxValues (fun x => .ok (cld x)) h n shrink = .error err) ∧
    (h.count ≤ 2 ^ 61 → ∀ (n : I) (nInt : JInt .i64) (shrink : Bool),
      DictInteger.toInt n = .ok nInt → nInt.val ≤ 2 ^ 61 →
      ∃ h', sizehint hash tablesz maxValues (fun x => .ok (cld x)) h n shrink = .ok h' ∧ DictRep hash eqKey h' m) ∧
    (∀ (newsz0 : Nat), h.count < tablesz newsz0 →
      (∃ h', rehash hash tablesz h newsz0 = .ok h' ∧ DictRep hash eqKey h' m) ∧
      (0 < h.count → ∀ (observedAge : JInt .u64), observedAge ≠ bumpAge h.age →
        rehash hash tablesz h newsz0 observedAge = .error .concurrentWrite))

theorem DictSizehintSmall_proven : DictSizehintSmall := by
  intro K V I _ hash eqKey tablesz maxValues cld h m htz hmv hcld hr
  refine ⟨fun n shrink err herr => ?_, fun hc n nInt shrink hn hnle => ?_,
    fun newsz0 hgt => ⟨?_, fun hpos observedAge hne => ?_⟩⟩
  · unfold sizehint
    rw [herr]
    rfl
  · have heq : sizehint hash tablesz maxValues (fun x => .ok (cld x)) h n shrink =
        sizehint hash tablesz maxValues (fun x => .ok (cld x)) h nInt shrink := by
      unfold sizehint
      rw [hn]
      rfl
    rw [heq]
    obtain ⟨h', h1, h2, -⟩ := sizehint_spec htz hmv hcld hr hc nInt hnle shrink
    exact ⟨h', h1, h2⟩
  · rw [htz newsz0] at hgt
    obtain ⟨h', h1, hi', hp', -⟩ := rehash_spec htz hr.1 newsz0 trivial hgt
    exact ⟨h', h1, hi', hp'.trans hr.2⟩
  · rw [htz newsz0] at hgt
    have hp := tableszSpec_pow newsz0
    have htab : tablesz newsz0 = tableszSpec newsz0 := htz newsz0
    have h0 : (h.count == 0) = false := by simp; omega
    obtain ⟨acc, hloop, -⟩ :=
      rehash_loop hr.1 hp trivial hgt h.size 0 acc0 (by omega) (accOK_zero hp trivial)
    unfold rehash
    rw [htab]
    simp only [h0, Bool.false_eq_true, ite_false]
    rw [bind_of_ok hloop]
    simp only [ne_eq, hne, not_false_eq_true, ite_true]
    rfl

/-- Every `Int` size hint returns and keeps every pair. -/
def DictSizehintTotal : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    DictRep hash eqKey h m → ∀ (n : JInt .i64) (shrink : Bool),
    ∃ h', sizehint hash tablesz maxValues (fun x => .ok (cld x)) h n shrink = .ok h' ∧ DictRep hash eqKey h' m

/-- `get!(default, h, key)` returns a present key's value without calling `default` and without
changing the table; otherwise it calls `default` once and stores the converted result on top of
every change `default` made (`get!` docstring, `base/dict.jl:416-442`).
`get!(default, h, key0)` first converts the key like `setindex!`. -/
def DictGetBangMutatingDefault : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → TableszLaw tablesz → FillLaw fillSlots →
    UnsetLaw unsetKey → UnsetLaw unsetVal →
    DictRep hash eqKey h m →
    (∀ (f : Unit → DictResult W) (key : K),
      let default : DictState K V → DictResult (W × DictState K V) :=
        fun t => f () >>= fun w => .ok (w, t)
      match rfind eqKey m key with
      | some e => getBang hash eqKey tablesz valueConv h key default = .ok (e.2, h)
      | none =>
        match f () >>= convertValue valueConv with
        | .error err => getBang hash eqKey tablesz valueConv h key default = .error err
        | .ok v => ∃ h', getBang hash eqKey tablesz valueConv h key default = .ok (v, h') ∧
            DictRep hash eqKey h' (rset eqKey m key v)) ∧
    (∀ (k_in : K) (w : W) (key : K),
      let default : DictState K V → DictResult (W × DictState K V) :=
        fun t => deleteKey hash eqKey unsetKey unsetVal t k_in >>= fun t' => .ok (w, t')
      match rfind eqKey m key with
      | some e => getBang hash eqKey tablesz valueConv h key default = .ok (e.2, h)
      | none =>
        match convertValue valueConv w with
        | .error err => getBang hash eqKey tablesz valueConv h key default = .error err
        | .ok v => ∃ h', getBang hash eqKey tablesz valueConv h key default = .ok (v, h') ∧
            DictRep hash eqKey h' (rset eqKey (rdel eqKey m k_in) key v)) ∧
    (∀ (w : W) (key : K),
      let default : DictState K V → DictResult (W × DictState K V) :=
        fun t => .ok (w, emptyBang fillSlots unsetKey unsetVal t)
      match rfind eqKey m key with
      | some e => getBang hash eqKey tablesz valueConv h key default = .ok (e.2, h)
      | none =>
        match convertValue valueConv w with
        | .error err => getBang hash eqKey tablesz valueConv h key default = .error err
        | .ok v => ∃ h', getBang hash eqKey tablesz valueConv h key default = .ok (v, h') ∧
            DictRep hash eqKey h' [(key, v)]) ∧
    ∀ (key0 : Q) (default : DictState K V → DictResult (W × DictState K V)),
      match convKey keyConv key0 with
      | .error err => getBangConv hash eqKey tablesz keyConv valueConv h key0 default = .error err
      | .ok key => getBangConv hash eqKey tablesz keyConv valueConv h key0 default =
          getBang hash eqKey tablesz valueConv h key default

theorem DictGetBangMutatingDefault_proven : DictGetBangMutatingDefault := by
  intro K V Q W hash eqKey tablesz fillSlots unsetKey unsetVal keyConv valueConv h m
    hl htz hfill huk huv hr
  refine ⟨fun f key => ?_, fun k_in w key => ?_, fun w key => ?_, fun key0 default => ?_⟩
  · have hdef : DefaultOK hash eqKey (fun t : DictState K V => f () >>= fun w => .ok (w, t)) := by
      intro h0 w h2 hi _ he
      dsimp only at he
      cases hf : f () with
      | error err => rw [hf] at he; cases he
      | ok w0 =>
        rw [hf, except_ok_bind] at he
        cases he
        exact ⟨hi, trivial, 0, Nat.two_pow_pos 64, AgeStep.refl h0⟩
    have hg := getBang_spec hl htz valueConv hr trivial key _ hdef
    cases hrfind : rfind eqKey m key with
    | some e => dsimp only; rw [hrfind] at hg; exact hg
    | none =>
      dsimp only
      rw [hrfind] at hg
      obtain ⟨t1, ht1, herr, hok⟩ := hg
      revert herr hok
      cases hf : f () with
      | error err =>
        intro herr _
        exact herr err rfl
      | ok w =>
        intro _ hok
        have h1 := hok w t1 rfl
        dsimp only [except_ok_bind]
        cases hv : convertValue valueConv w with
        | error err => rw [hv] at h1; exact h1
        | ok v =>
          rw [hv] at h1
          obtain ⟨h', hgb, hr'⟩ := h1
          exact ⟨h', hgb, hr'.1, hr'.2.trans (rset_perm ht1.2 key v)⟩
  · have hdelStep : ∀ t0 : DictState K V, Inv hash eqKey t0 →
        ∃ t2, deleteKey hash eqKey unsetKey unsetVal t0 k_in = .ok t2 ∧
          Inv hash eqKey t2 ∧ tlist t2 = rdel eqKey (tlist t0) k_in ∧
          ∃ n, n < 2 ^ 64 ∧ AgeStep t0 t2 n := by
      intro t0 hi0
      have hrep0 : DictRep hash eqKey t0 (tlist t0) := ⟨hi0, List.Perm.refl _⟩
      have hp := hrep0.probe hl hl.query k_in
      unfold JuliaLean.base.dict.deleteKey
      cases hf : rfind eqKey (tlist t0) k_in with
      | some e =>
        rw [hf] at hp
        obtain ⟨i, hidx, h1, h2, he, hm⟩ := hp
        rw [hidx, except_ok_bind, if_pos (by omega), show ((i : Nat) : Int).toNat = i by omega]
        obtain ⟨hI, htl, -, ha, -⟩ := deleteAt_spec hl huk huv hi0 h1 h2 he
        refine ⟨_, rfl, hI, ?_, 1, Nat.one_lt_two_pow (by decide),
          AgeStep.of_pos (by rw [ha, bump_eq]) (by omega)⟩
        rw [htl, filter_match_eq hl.query hm]; rfl
      | none =>
        rw [hf] at hp
        rw [hp.1, except_ok_bind, if_neg (by omega)]
        exact ⟨t0, rfl, hi0, (rdel_absent (rfind_eq_none_iff.1 hf)).symm,
          0, Nat.two_pow_pos 64, AgeStep.refl t0⟩
    let default : DictState K V → DictResult (W × DictState K V) :=
      fun t => deleteKey hash eqKey unsetKey unsetVal t k_in >>= fun t' => .ok (w, t')
    have hdef : DefaultOK hash eqKey default := by
      intro h0 w0 h2 hi0 _ he
      obtain ⟨t2, hd, hi2, -, n, hn, ha⟩ := hdelStep h0 hi0
      dsimp only [default] at he
      rw [hd, except_ok_bind] at he
      cases he
      exact ⟨hi2, trivial, n, hn, ha⟩
    have hg := getBang_spec hl htz valueConv hr trivial key default hdef
    cases hrfind : rfind eqKey m key with
    | some e => rw [hrfind] at hg; exact hg
    | none =>
      rw [hrfind] at hg
      obtain ⟨t1, ht1, -, hok⟩ := hg
      obtain ⟨t2, hd, -, htl2, -⟩ := hdelStep t1 ht1.1
      have h1 := hok w t2 (by show (deleteKey _ _ _ _ t1 k_in >>= _) = _; rw [hd]; rfl)
      cases hv : convertValue valueConv w with
      | error err => rw [hv] at h1; exact h1
      | ok v =>
        rw [hv] at h1
        obtain ⟨h', hgb, hr'⟩ := h1
        refine ⟨h', hgb, hr'.1, hr'.2.trans ?_⟩
        rw [htl2]
        exact rset_perm (ht1.2.filter _) key v
  · have hdef : DefaultOK hash eqKey
        (fun t : DictState K V => .ok (w, emptyBang fillSlots unsetKey unsetVal t)) := by
      intro h0 w0 h2 hi0 _ he
      cases he
      obtain ⟨hrep, ha⟩ := emptyBang_spec hfill unsetKey unsetVal hi0
      exact ⟨hrep.1, trivial, 1, Nat.one_lt_two_pow (by decide),
        AgeStep.of_pos (by rw [ha, bump_eq]) (by omega)⟩
    have hg := getBang_spec hl htz valueConv hr trivial key _ hdef
    cases hrfind : rfind eqKey m key with
    | some e => rw [hrfind] at hg; exact hg
    | none =>
      rw [hrfind] at hg
      obtain ⟨t1, ht1, -, hok⟩ := hg
      obtain ⟨hrep, -⟩ := emptyBang_spec hfill unsetKey unsetVal ht1.1
      have hnil : tlist (emptyBang fillSlots unsetKey unsetVal t1) = [] :=
        List.perm_nil.1 hrep.2
      have h1 := hok w (emptyBang fillSlots unsetKey unsetVal t1) rfl
      cases hv : convertValue valueConv w with
      | error err => rw [hv] at h1; exact h1
      | ok v =>
        rw [hv] at h1
        obtain ⟨h', hgb, hr'⟩ := h1
        rw [hnil] at hr'
        exact ⟨h', hgb, hr'⟩
  · unfold getBangConv convKey
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
  ∀ (K V Q D DK DF : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → DictRep hash eqKey h m →
    ∀ (q : Q) (default : D) (defaultKey : DK) (defaultF : Unit → DictResult DF),
      getindex hashQ matchQ h q =
          (match rlookup matchQ m q with | some v => .ok v | none => .error .keyError) ∧
        JuliaLean.base.dict.get hashQ matchQ h q default =
          .ok (match rlookup matchQ m q with | some v => .inl v | none => .inr default) ∧
        getF hashQ matchQ h q defaultF =
          (match rlookup matchQ m q with | some v => .ok (.inl v) | none => .inr <$> defaultF ()) ∧
        haskey hashQ matchQ h q = .ok (rlookup matchQ m q).isSome ∧
        inKeySet hashQ matchQ ⟨h⟩ q = .ok (rlookup matchQ m q).isSome ∧
        getkey hashQ matchQ h q defaultKey =
          .ok (match rfind matchQ m q with | some e => .inl e.1 | none => .inr defaultKey)

theorem DictLookupSemantics_proven : DictLookupSemantics := by
  intro K V Q D DK DF hash eqKey hashQ matchQ h m hl hq hr q default defaultKey defaultF
  exact hr.lookups hl hq q default defaultKey defaultF


/-- The reference map of a constructor loop `for (k, v) in kv; h[k] = v; end`. -/
def refBuild {Q W : Type} (eqKey : K → K → Bool) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (pairs : List (Q × W)) : DictResult (List (K × V)) :=
  pairs.foldlM (refStep eqKey keyConv valueConv) []

section CtorProps
variable {hash : K → JInt .u64} {eqKey : K → K → Bool} {tablesz : Nat → Nat}

theorem fromIterator_insert_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz)
    {Q W C S : Type} (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (iterate : C → Option S → DictResult (Option ((Q × W) × S))) (bound : C → Nat)
    (kv : C) (pairs : List (Q × W)) (t : DictState K V)
    (hcol : iterCollectPairs iterate kv (bound kv) none = .ok pairs)
    (ht : DictRep hash eqKey t []) :
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m' => ∃ t', dictInsertLoop hash eqKey tablesz keyConv valueConv iterate kv (bound kv) none t = .ok t' ∧
        DictRep hash eqKey t' m'
    | .error e => dictInsertLoop hash eqKey tablesz keyConv valueConv iterate kv (bound kv) none t = .error e :=
  dictInsertLoop_of_collect hl htz keyConv valueConv iterate kv (bound kv) none pairs t [] hcol ht
theorem fromPairs_insert_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pairs : List (Q × W)) (t : DictState K V)
    (ht : DictRep hash eqKey t []) :
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m' => ∃ t', dictFromPairs.insert hash eqKey tablesz keyConv valueConv pairs t = .ok t' ∧
        DictRep hash eqKey t' m'
    | .error e => dictFromPairs.insert hash eqKey tablesz keyConv valueConv pairs t = .error e :=
  insertLoop_spec hl htz keyConv valueConv _ (fun _ => rfl) (fun p rest t => rfl) pairs t [] ht trivial

/-- `sizehint!(Dict{K,V}(), n)` gives an empty well-formed table for every `Int` `n`. -/
theorem sizehint_empty (htz : TableszLaw tablesz) (maxValues : Nat)
    (cld : JInt .i64 → JInt .i64) (nInt : JInt .i64) :
    ∃ t, sizehint hash tablesz maxValues (fun x => .ok (cld x)) (dictEmpty K V) nInt true =
      .ok t ∧ DictRep hash eqKey t [] ∧ t.count = 0 := by
  let x := (cld (JInt.lit .i64 (3 * (clampSizeHint 0 maxValues nInt).val))).val.toNat
  have hN : tablesz x = tableszSpec x := htz x
  have hpow : IsPow (tableszSpec x) := tableszSpec_pow x
  have h16 : 16 ≤ tableszSpec x := hpow.ge
  have hgt : (dictEmpty K V).count < tableszSpec (tableszSpec x) := by
    rw [tableszSpec_of_pow hpow]
    show 0 < tableszSpec x
    omega
  obtain ⟨t, h1, hi, hp, -, hc, -⟩ :=
    rehash_spec htz (dictEmpty_rep (V := V) hash eqKey).1 (tableszSpec x) trivial hgt
  unfold sizehint
  simp only [DictInteger.toInt, except_ok_bind]
  change ∃ t, (if (true && tablesz x == 0) || (!true && tablesz x ≤ 0) then
    Except.ok (dictEmpty K V) else rehash hash tablesz (dictEmpty K V) (tablesz x)) = .ok t ∧ _
  rw [hN, if_neg (by simp; omega)]
  exact ⟨t, h1, ⟨hi, hp.trans (dictEmpty_rep hash eqKey).2⟩, hc⟩

/-- `sizehint!(d, n, shrink=false)` keeps every pair for every `Int` `n`. -/
theorem sizehint_no_shrink (htz : TableszLaw tablesz) (maxValues : Nat)
    (cld : JInt .i64 → JInt .i64) {t : DictState K V} {m : List (K × V)}
    (h : DictRep hash eqKey t m) (nInt : JInt .i64) :
    ∃ t', sizehint hash tablesz maxValues (fun x => .ok (cld x)) t nInt false = .ok t' ∧ DictRep hash eqKey t' m ∧
      t'.count = t.count := by
  let x := (cld (JInt.lit .i64 (3 * (clampSizeHint t.count maxValues nInt).val))).val.toNat
  have hN : tablesz x = tableszSpec x := htz x
  have hpow : IsPow (tableszSpec x) := tableszSpec_pow x
  unfold sizehint
  simp only [DictInteger.toInt, except_ok_bind]
  change ∃ t', (if (false && tablesz x == t.size) || (!false && tablesz x ≤ t.size) then
    Except.ok t else rehash hash tablesz t (tablesz x)) = .ok t' ∧ _
  rw [hN]
  split
  · exact ⟨t, rfl, h, rfl⟩
  · rename_i hle
    have hlt : t.size < tableszSpec x := by simp at hle; exact hle
    have hcs := h.1.count_le_size
    have hgt : t.count < tableszSpec (tableszSpec x) := by
      rw [tableszSpec_of_pow hpow]
      omega
    obtain ⟨t', h', hi', hp', -, hc', -⟩ := rehash_spec htz h.1 (tableszSpec x) trivial hgt
    exact ⟨t', h', ⟨hi', hp'.trans h.2⟩, hc'⟩

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
  ∀ (K V Q W C S I : Type) [DictInteger I] (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (tablesz : Nat → Nat) (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (haslength : C → Bool) (length : C → DictResult I)
    (iterate : C → Option S → DictResult (Option ((Q × W) × S))) (bound : C → Nat)
    (kv : C) (pairs : List (Q × W)),
    KeyLaws hash eqKey → TableszLaw tablesz →
    iterCollectPairs iterate kv (bound kv) none = .ok pairs →
    match (if haslength kv then length kv >>= DictInteger.toInt else .ok (JInt.lit .i64 0)) with
    | .error e => dictFromIterator hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
        haslength length iterate bound kv = .error e
    | .ok _ =>
      match refBuild eqKey keyConv valueConv pairs with
      | .ok m => ∃ h, dictFromIterator hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
          haslength length iterate bound kv = .ok h ∧ DictRep hash eqKey h m
      | .error e => dictFromIterator hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
          haslength length iterate bound kv = .error e

theorem DictIteratorConstructorSemantics_proven : DictIteratorConstructorSemantics := by
  intro K V Q W C S I _ hash eqKey tablesz maxValues cld keyConv valueConv haslength length
    iterate bound kv pairs hl htz hcol
  unfold dictFromIterator
  dsimp only
  cases hhl : haslength kv with
  | true =>
    simp only [ite_true]
    cases hlen : length kv with
    | error e => simp only [except_error_bind]
    | ok len =>
      simp only [except_ok_bind]
      cases hconv : DictInteger.toInt len with
      | error e => simp only [except_error_bind]
      | ok lenInt =>
        simp only [except_ok_bind]
        obtain ⟨t, h1, h2, -⟩ := sizehint_empty (V := V) htz maxValues cld lenInt
        rw [h1, except_ok_bind]
        exact fromIterator_insert_spec hl htz keyConv valueConv iterate bound kv pairs t hcol h2
  | false =>
    simp only [Bool.false_eq_true, ite_false, except_ok_bind]
    exact fromIterator_insert_spec hl htz keyConv valueConv iterate bound kv pairs _ hcol
      (dictEmpty_rep hash eqKey)
/-- `Dict{K,V}(ps::Pair...)` stores the converted pairs in argument order, a later `isequal` key
replacing an earlier one. -/
def DictConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (pairs : List (Q × W)),
    KeyLaws hash eqKey → TableszLaw tablesz →
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m => ∃ h, dictFromPairs hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv pairs = .ok h ∧
        DictRep hash eqKey h m
    | .error e => dictFromPairs hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv pairs = .error e

theorem DictConstructorSemantics_proven : DictConstructorSemantics := by
  intro K V Q W hash eqKey tablesz maxValues cld keyConv valueConv pairs hl htz
  unfold dictFromPairs
  obtain ⟨t, h1, h2, -⟩ :=
    sizehint_empty (V := V) htz maxValues cld (JInt.lit .i64 (Int.ofNat pairs.length))
  rw [h1, except_ok_bind]
  exact fromPairs_insert_spec hl htz keyConv valueConv pairs t h2

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
  exact (dictEmpty_rep hash eqKey).setConv hl htz keyConv valueConv trivial pair

/-- `Dict(ps::Pair{K,V}...)` behaves like `Dict{K,V}(ps)`. -/
def DictTypedPairListConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64) (keyConv : KeyConv Q K)
    (valueConv : ValueConv W V) (pairs : List (Q × W)),
    KeyLaws hash eqKey → TableszLaw tablesz →
    match refBuild eqKey keyConv valueConv pairs with
    | .ok m => ∃ h, dictTypedPairs hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv pairs = .ok h ∧
        DictRep hash eqKey h m
    | .error e => dictTypedPairs hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv pairs = .error e

theorem DictTypedPairListConstructorSemantics_proven : DictTypedPairListConstructorSemantics := by
  intro K V Q W hash eqKey tablesz maxValues cld keyConv valueConv pairs hl htz
  exact DictIteratorConstructorSemantics_proven K V Q W (List (Q × W)) (List (Q × W)) (JInt .i64)
    hash eqKey tablesz maxValues cld keyConv valueConv (fun _ => true)
    (fun xs => .ok (JInt.lit .i64 (Int.ofNat xs.length)))
    listIterate (fun xs => xs.length + 1) pairs pairs hl htz
    (iterCollectPairs_listIterate pairs)

/-- `Dict(kv)` and `Dict(ps::Pair...)` forward to `dict_with_eltype` (`base/abstractdict.jl`),
which constructs `Dict{K,V}(kv)` for the pair element type: the result holds the converted pairs. -/
def DictGenericConstructorSemantics : Prop :=
  ∀ (K V Q W C S I : Type) [DictInteger I] (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (tablesz : Nat → Nat) (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (haslength : C → Bool) (length : C → DictResult I)
    (iterate : C → Option S → DictResult (Option ((Q × W) × S))) (bound : C → Nat)
    (eltypeC : C → Type)
    (dictWithEltypeC : (C → DictResult (DictState K V)) → C → Type → DictResult (DictState K V))
    (kv : C) (iterPairs : List (Q × W))
    (pairs : List (Q × W))
    (eltype : List (Q × W) → Type)
    (dictWithEltype : (List (Q × W) → DictResult (DictState K V)) → List (Q × W) → Type → DictResult (DictState K V)),
    KeyLaws hash eqKey → TableszLaw tablesz →
    (∀ ctor x T, dictWithEltypeC ctor x T = ctor x) →
    (∀ ctor xs T, dictWithEltype ctor xs T = ctor xs) →
    iterCollectPairs iterate kv (bound kv) none = .ok iterPairs →
    (match (if haslength kv then length kv >>= DictInteger.toInt else .ok (JInt.lit .i64 0)) with
      | .error e => dictInferred hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
          haslength length iterate bound eltypeC dictWithEltypeC kv = .error e
      | .ok _ =>
        match refBuild eqKey keyConv valueConv iterPairs with
        | .ok m => ∃ h, dictInferred hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
            haslength length iterate bound eltypeC dictWithEltypeC kv = .ok h ∧ DictRep hash eqKey h m
        | .error e => dictInferred hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
            haslength length iterate bound eltypeC dictWithEltypeC kv = .error e) ∧
    (match refBuild eqKey keyConv valueConv pairs with
      | .ok m => ∃ h, dictPairsGeneric hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
          eltype dictWithEltype pairs = .ok h ∧ DictRep hash eqKey h m
      | .error e => dictPairsGeneric hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
          eltype dictWithEltype pairs = .error e)

theorem DictGenericConstructorSemantics_proven : DictGenericConstructorSemantics := by
  intro K V Q W C S I _ hash eqKey tablesz maxValues cld keyConv valueConv haslength length
    iterate bound eltypeC dictWithEltypeC kv iterPairs pairs eltype dictWithEltype
    hl htz hlawC hlaw hcol
  have h1 := DictIteratorConstructorSemantics_proven K V Q W C S I hash eqKey tablesz maxValues cld
    keyConv valueConv haslength length iterate bound kv iterPairs hl htz hcol
  have h2 := DictTypedPairListConstructorSemantics_proven K V Q W hash eqKey tablesz maxValues cld
    keyConv valueConv pairs hl htz
  have e1 : dictInferred hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
      haslength length iterate bound eltypeC dictWithEltypeC kv =
      dictFromIterator hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
        haslength length iterate bound kv := hlawC _ _ _
  have e2 : dictPairsGeneric hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
      eltype dictWithEltype pairs =
      dictTypedPairs hash eqKey tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv pairs := hlaw _ _ _
  rw [e1, e2]
  exact ⟨h1, h2⟩
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
only pair of a one-pair dictionary and throws `ArgumentError` otherwise. -/
def DictOnlyContract : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (h : DictState K V)
    (m : List (K × V)),
    DictRep hash eqKey h m → h.size < 2 ^ 63 - 1 →
    onlyDict h =
      match m with
      | [e] => .ok e
      | _ => .error (.argumentError "Collection must contain exactly 1 element")

theorem DictOnlyContract_proven : DictOnlyContract := by
  intro K V hash eqKey h m hr hbig
  have hc : length h = m.length := by
    show h.count = m.length; rw [hr.1.count, hr.2.length_eq]
  unfold onlyDict JuliaLean.base.iterators.sourceMethod1673 firstDict
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hc]
  obtain ⟨hit, hp⟩ := hr.iterate hbig
  match m, hp with
  | [], _ => rfl
  | [e], hp =>
    have hl : tlist h = [e] := List.perm_singleton.1 hp
    dsimp only [List.length_cons, List.length_nil]
    rw [if_pos (by decide)]
    rw [if_neg (by simp)]
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
    dsimp only [List.length_cons, List.length_nil]
    rw [if_pos (by decide), if_pos (by simp)]

/-- `map!(f, values(d))` replaces every stored value `v` by the converted `f(v)` and keeps the keys. -/
def DictMapReduceSemantics : Prop :=
  ∀ (K V W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (valueConv : ValueConv W V) (f : V → DictResult W) (g : V → V)
    (h : DictState K V) (m : List (K × V)),
    DictRep hash eqKey h m →
    (∀ v, (f v >>= convertValue valueConv) = .ok (g v)) →
    ∃ h', mapBang valueConv f ⟨h⟩ = .ok ⟨h'⟩ ∧
      DictRep hash eqKey h' (m.map (fun e => (e.1, g e.2)))

theorem DictMapReduceSemantics_proven : DictMapReduceSemantics := by
  intro K V W hash eqKey valueConv f g h m hr hg
  obtain ⟨h', h1, h2, -⟩ := hr.mapBang valueConv f g hg
  exact ⟨h', h1, h2⟩

theorem lor128_add : ∀ y, y < 128 → Nat.lor y 128 = 128 + y := by decide +kernel

theorem filledB_iff : ∀ b, b < 256 → (filledB b = true ↔ 128 ≤ b) := by decide +kernel

/-- The slot bytes: `_shorthash7` stores the top seven hash bits with the high bit set,
`isslotempty`, `isslotmissing` and `isslotfilled` partition the slots of every well-formed `Dict`
into three mutually exclusive states with `isslotfilled h i = (ent h i).isSome`, `empty!` makes
every slot empty, and `_delete!` makes a deleted slot empty when the next slot is empty and
missing (tombstone) otherwise. -/
def DictSlots : Prop :=
  (∀ hash : JInt .u64, shorthash7 hash = 128 + hash.val.toNat / 2 ^ 57 ∧
    128 ≤ shorthash7 hash ∧ shorthash7 hash < 256 ∧
    isslotfilled { (dictEmpty Unit Unit) with slots := fun _ => shorthash7 hash } 1 = true ∧
    isslotempty { (dictEmpty Unit Unit) with slots := fun _ => shorthash7 hash } 1 = false ∧
    isslotmissing { (dictEmpty Unit Unit) with slots := fun _ => shorthash7 hash } 1 = false) ∧
  (∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (h : DictState K V)
    (m : List (K × V)) (i : Nat),
    DictRep hash eqKey h m → 1 ≤ i → i ≤ h.size →
    isslotfilled h i = (ent h i).isSome ∧
    ((isslotempty h i = true ∧ isslotmissing h i = false ∧ isslotfilled h i = false) ∨
     (isslotempty h i = false ∧ isslotmissing h i = true ∧ isslotfilled h i = false) ∨
     (isslotempty h i = false ∧ isslotmissing h i = false ∧ isslotfilled h i = true))) ∧
  (∀ (K V : Type) (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (h : DictState K V) (i : Nat),
    FillLaw fillSlots → 1 ≤ i → i ≤ h.size →
    isslotempty (emptyBang fillSlots unsetKey unsetVal h) i = true ∧
    isslotmissing (emptyBang fillSlots unsetKey unsetVal h) i = false ∧
    isslotfilled (emptyBang fillSlots unsetKey unsetVal h) i = false ∧
    (isslotempty h (nextIndex h.size i) = false →
      isslotmissing (deleteAt unsetKey unsetVal h i) i = true ∧
      isslotempty (deleteAt unsetKey unsetVal h i) i = false ∧
      isslotfilled (deleteAt unsetKey unsetVal h i) i = false))

theorem DictSlots_proven : DictSlots := by
  refine ⟨fun hash => ?_, fun K V hash eqKey h m i hr h1 h2 => ?_,
    fun K V fillSlots unsetKey unsetVal h i hfill h1 h2 => ?_⟩
  · have hr := u64_val_range hash
    have hlt : hash.val.toNat / 2 ^ 57 < 128 := by omega
    have e : shorthash7 hash = Nat.lor ((hash.val.toNat / 2 ^ 57) % 256) 0x80 := by
      unfold shorthash7; rw [Nat.shiftRight_eq_div_pow]
    have hf := shorthash7_facts hash
    have he' : shorthash7 hash = 128 + hash.val.toNat / 2 ^ 57 := by
      rw [e, Nat.mod_eq_of_lt (by omega), lor128_add _ hlt]
    refine ⟨he', by omega, by omega, hf.1, ?_, ?_⟩
    · show (shorthash7 hash == 0) = false
      exact beq_false_of_ne hf.2.1
    · show (shorthash7 hash == 0x7f) = false
      exact beq_false_of_ne hf.2.2
  · rcases hr.1.slot i h1 h2 with h0 | h127 | ⟨k, v, hk, hv, hs, -⟩
    · have hfe : isslotfilled h i = false := by rw [isslotfilled_eq, h0]; exact filledB_zero
      have hee : isslotempty h i = true := by rw [isslotempty_eq, h0]; rfl
      have hme : isslotmissing h i = false := by rw [isslotmissing_eq, h0]; decide
      have hent : ent h i = none := ent_of_not_filled (by rw [h0]; exact filledB_zero)
      exact ⟨by rw [hfe, hent]; rfl, Or.inl ⟨hee, hme, hfe⟩⟩
    · have hfe : isslotfilled h i = false := by rw [isslotfilled_eq, h127]; exact filledB_127
      have hee : isslotempty h i = false := by rw [isslotempty_eq, h127]; decide
      have hme : isslotmissing h i = true := by rw [isslotmissing_eq, h127]; rfl
      have hent : ent h i = none := ent_of_not_filled (by rw [h127]; exact filledB_127)
      exact ⟨by rw [hfe, hent]; rfl, Or.inr (Or.inl ⟨hee, hme, hfe⟩)⟩
    · have hff : filledB (h.slots i) = true := by rw [hs]; exact shorthash7_filled _
      have hfe : isslotfilled h i = true := by rw [isslotfilled_eq]; exact hff
      have hee : isslotempty h i = false := by
        rw [isslotempty_eq, hs]; exact beq_false_of_ne (shorthash7_ne0 _)
      have hme : isslotmissing h i = false := by
        rw [isslotmissing_eq, hs]; exact beq_false_of_ne (shorthash7_ne127 _)
      have hent : ent h i = some (k, v) := ent_of_filled hff hk hv
      exact ⟨by rw [hfe, hent]; rfl, Or.inr (Or.inr ⟨hee, hme, hfe⟩)⟩
  · obtain ⟨-, hsl, -⟩ := emptyBang_fields fillSlots unsetKey unsetVal h
    have h0 : (emptyBang fillSlots unsetKey unsetVal h).slots i = 0 := by
      rw [hsl]; exact hfill h.size 0 h.slots i h1 h2
    refine ⟨by rw [isslotempty_eq, h0]; rfl, by rw [isslotmissing_eq, h0]; decide,
      by rw [isslotfilled_eq, h0]; exact filledB_zero, fun hne => ?_⟩
    have hslDel : (deleteAt unsetKey unsetVal h i).slots i = 0x7f := by
      rw [deleteAt_eq]
      unfold delT delD
      rw [if_neg (by simp [hne])]
      show updateAt h.slots i 0x7f i = 0x7f
      exact updateAt_same _ _ _
    exact ⟨by rw [isslotmissing_eq, hslDel]; rfl, by rw [isslotempty_eq, hslDel]; decide,
      by rw [isslotfilled_eq, hslDel]; exact filledB_127⟩

/-- `hashindex(key, sz)` converts any `Integer` `sz` to `Int` (propagating `InexactError`), and
for a power-of-two `sz` returns the one-based slot `hash(key) mod sz + 1` and the short hash of
`key`. -/
def DictHashindexSemantics : Prop :=
  ∀ (K I : Type) [DictInteger I] (hash : K → JInt .u64) (key : K) (sz : I),
    (∀ (szInt : JInt .i64) (p : Nat), 4 ≤ p → p ≤ 62 →
      DictInteger.toInt sz = .ok szInt → szInt.val = (2 ^ p : Nat) →
      hashindex hash key sz = .ok ((hash key).val.toNat % 2 ^ p + 1, shorthash7 (hash key)) ∧
        1 ≤ (hash key).val.toNat % 2 ^ p + 1 ∧ (hash key).val.toNat % 2 ^ p + 1 ≤ 2 ^ p) ∧
    (∀ err, DictInteger.toInt sz = .error err → hashindex hash key sz = .error err)

theorem DictHashindexSemantics_proven : DictHashindexSemantics := by
  intro K I _ hash key sz
  refine ⟨fun szInt p hp1 _ hsz hval => ?_, fun err herr => ?_⟩
  · have hpow : IsPow (2 ^ p) := ⟨p, hp1, rfl⟩
    have hpos : 0 < 2 ^ p := Nat.two_pow_pos p
    have hlt := Nat.mod_lt (hash key).val.toNat hpos
    unfold hashindex
    rw [hsz, except_ok_bind]
    dsimp only [pure, Except.pure]
    have hsub : (szInt.val - 1).toNat = 2 ^ p - 1 := by omega
    rw [hsub, hpow.land]
    exact ⟨rfl, by omega, by omega⟩
  · unfold hashindex
    rw [herr]
    rfl

/-- The slot-byte and hash-index layout. -/
def DictSlotSemantics : Prop := DictSlots ∧ DictHashindexSemantics

theorem DictSlotSemantics_proven : DictSlotSemantics :=
  ⟨DictSlots_proven, DictHashindexSemantics_proven⟩

/-- Linear probing (`(index & (sz-1)) + 1`), `ht_keyindex`, `ht_keyindex2_shorthash!` and
`rehash!` stay within the one-based slot memory `1:sz` and never read an undefined slot. -/
def DictProbeSafe : Prop :=
  (∀ size start offset, 0 < size → start < size →
    1 ≤ nextIndex size (start + offset) ∧ nextIndex size (start + offset) ≤ size) ∧
  ∀ (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (tablesz : Nat → Nat) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → TableszLaw tablesz →
    DictRep hash eqKey h m →
    (∀ q : Q, (htKeyindex hashQ matchQ h q = .ok (-1)) ∨
      ∃ i : Nat, htKeyindex hashQ matchQ h q = .ok (i : Int) ∧
        1 ≤ i ∧ i ≤ h.size ∧ (h.keys i).isSome = true ∧ (h.vals i).isSome = true) ∧
    (∀ q : Q, ∃ idx h',
      htKeyindex2Query hash hashQ matchQ tablesz h q = .ok (idx, shorthash7 (hashQ q), h') ∧
      DictRep hash eqKey h' m ∧
      ((∃ i : Nat, idx = i ∧ 1 ≤ i ∧ i ≤ h'.size ∧ (h'.keys i).isSome = true ∧ (h'.vals i).isSome = true) ∨
       (idx < 0 ∧ 1 ≤ (-idx).toNat ∧ (-idx).toNat ≤ h'.size))) ∧
    (∀ newsz0 : Nat, rehash hash tablesz h newsz0 ≠ .error .undefRef ∧
      (h.count < tablesz newsz0 →
        ∃ h', rehash hash tablesz h newsz0 = .ok h' ∧ DictRep hash eqKey h' m ∧
          ∀ i, 1 ≤ i → i ≤ h'.size → isslotfilled h' i = true →
            (h'.keys i).isSome = true ∧ (h'.vals i).isSome = true))

theorem DictProbeSafe_proven : DictProbeSafe := by
  refine ⟨fun size start offset h1 _ => ?_,
    fun K V Q hash eqKey hashQ matchQ tablesz h m hl hq htz hr =>
      ⟨fun q => ?_, fun q => ?_, fun newsz0 => ⟨rehash_no_undef hr.1 newsz0, fun hgt => ?_⟩⟩⟩
  · unfold nextIndex
    have : Nat.land (start + offset) (size - 1) ≤ size - 1 := Nat.and_le_right
    constructor <;> omega
  · have hk := hr.htKeyindex hl hq q
    cases hf : rfind matchQ m q with
    | none => rw [hf] at hk; exact Or.inl hk
    | some e =>
      rw [hf] at hk
      obtain ⟨i, hidx, h1, h2, hei⟩ := hk
      obtain ⟨-, hk', hv'⟩ := ent_some hei
      exact Or.inr ⟨i, hidx, h1, h2, by rw [hk']; rfl, by rw [hv']; rfl⟩
  · obtain ⟨idx, h', n, hprobe, -, hout⟩ := htKeyindex2Query_spec hl hq htz hr.1 trivial q
    refine ⟨idx, h', hprobe, ⟨hout.inv, hout.perm.trans hr.2⟩, ?_⟩
    cases hf : rfind matchQ (tlist h) q with
    | some e =>
      obtain ⟨hem, heq⟩ := rfind_some hf
      obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
      obtain ⟨hidx, ht'⟩ := hout.found i e h1 h2 hei heq
      subst ht'
      obtain ⟨-, hk', hv'⟩ := ent_some hei
      exact Or.inl ⟨i, hidx, h1, h2, by rw [hk']; rfl, by rw [hv']; rfl⟩
    | none =>
      obtain ⟨hneg, h1, h2, -⟩ := hout.absent (rfind_eq_none_iff.1 hf)
      exact Or.inr ⟨hneg, h1, h2⟩
  · rw [htz newsz0] at hgt
    obtain ⟨h', h1, hi', hp', -⟩ := rehash_spec htz hr.1 newsz0 trivial hgt
    refine ⟨h', h1, ⟨hi', hp'.trans hr.2⟩, fun i hi1 hi2 hfl => ?_⟩
    rw [isslotfilled_eq] at hfl
    obtain ⟨k, v, hk, hv, -⟩ := hi'.filled hi1 hi2 hfl
    exact ⟨by rw [hk]; rfl, by rw [hv]; rfl⟩
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
  ∀ (K V Q D : Type) (eqKey : K → Q → Bool) (d : ImmutableDict K V) (q : Q) (default : D)
    (fallback : Unit → DictResult D),
    immutableGetindex eqKey d q =
        (match ((immutableCollect d).find? (fun e => eqKey e.1 q)).map (·.2) with
          | some v => .ok v | none => .error .keyError) ∧
      immutableHasKey eqKey d q = ((immutableCollect d).find? (fun e => eqKey e.1 q)).isSome ∧
      immutableGet eqKey d q default =
        (match ((immutableCollect d).find? (fun e => eqKey e.1 q)).map (·.2) with
          | some v => .inl v | none => .inr default) ∧
      immutableGetF eqKey d q fallback =
        (match ((immutableCollect d).find? (fun e => eqKey e.1 q)).map (·.2) with
          | some v => .ok (.inl v) | none => .inr <$> fallback ())

theorem ImmutableDictLookupSemantics_proven : ImmutableDictLookupSemantics := by
  intro K V Q D eqKey d q default fallback
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
/-- Pair membership scans matching keys in iteration order. The first true comparison wins,
the first error propagates, and `missing` in a Boolean test throws `TypeError`. -/
def ImmutableDictPairMembershipSemantics : Prop :=
  ∀ (K V Q W : Type) (eqKey : K → Q → Bool)
    (valcmp : W → V → DictResult (Option Bool)) (d : ImmutableDict K V) (pair : Q × W),
    immutableIn eqKey valcmp pair d =
      match (((immutableCollect d).filter (fun e => eqKey e.1 pair.1)).map
        (fun e => valcmp pair.2 e.2)).find? (fun r =>
          match r with | .ok (some false) => false | _ => true) with
      | none => .ok (some false)
      | some (.ok none) => .error .typeError
      | some r => r

theorem ImmutableDictPairMembershipSemantics_proven : ImmutableDictPairMembershipSemantics := by
  intro K V Q W eqKey valcmp d pair
  rw [immutableCollect_eq]
  induction d with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    cases h : eqKey k pair.1
    · simpa [immutableIn, h] using ih
    · cases hv : valcmp pair.2 v with
      | error e => simp [immutableIn, h, hv]
      | ok b =>
        cases b with
        | none => simp [immutableIn, h, hv]
        | some b => cases b <;> simp [immutableIn, h, hv, ih]

/-- Iteration shows every pair, duplicates included; `length` (`count(Returns(true), t)`) and
`isempty` agree with it and `empty(d, K, V)` has no pairs. -/
def ImmutableDictCollectionSemantics : Prop :=
  ∀ (K V : Type) (count : (K × V → Bool) → ImmutableDict K V → Nat), CountLaw count →
    ∀ d : ImmutableDict K V,
    immutableIterate (immutableEmpty K V) = none ∧
    (∀ p (rest : ImmutableDict K V),
      immutableIterate (p :: rest) = some (p, rest) ∧
      immutableIterate d [] = none ∧
      immutableIterate d (p :: rest) = some (p, rest)) ∧
    immutableLength (fun p x => .ok (count p x)) d = .ok (immutableCollect d).length ∧
    immutableIsEmpty d = (immutableIterate d).isNone ∧
    immutableEmptyLike K V d = immutableEmpty K V ∧
    immutableCollect (immutableEmptyLike K V d) = []

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

/-- Incremental iteration step of `ImmutableDict` (`iterate(d)` and `iterate(d, t)`). -/
def immutableIterStep {K V : Type} (d : ImmutableDict K V)
    (state : Option (ImmutableDict K V)) :
    DictResult (Option ((K × V) × ImmutableDict K V)) :=
  .ok (immutableIterate d (state.getD d))

theorem immutableIterStep_eq :
    @immutableIterStep K V = @listIterate (K × V) := by
  funext d state
  unfold immutableIterStep listIterate immutableIterate
  cases state.getD d <;> rfl

theorem iterCollectPairs_immutableIterStep (d : ImmutableDict K V) :
    iterCollectPairs immutableIterStep d (d.length + 1) none = .ok (immutableCollect d) := by
  rw [immutableCollect_eq, immutableIterStep_eq]
  exact iterCollectPairs_listIterate d
/-- `Dict{K,V}(d)` of an `ImmutableDict` maps every key to `d[key]`, its most recent value
(`ImmutableDict` docstring; `Dict` docstring: the pairs of the argument). -/
def ImmutableDictToDict : Prop :=
  ∀ (K V D : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (count : (K × V → Bool) → ImmutableDict K V → Nat)
    (eltype : ImmutableDict K V → Type)
    (dictWithEltype : (ImmutableDict K V → DictResult (DictState K V)) → ImmutableDict K V → Type → DictResult (DictState K V))
    (d : ImmutableDict K V) (h : DictState K V),
    KeyLaws hash eqKey → TableszLaw tablesz → CountLaw count →
    (∀ ctor kv T, dictWithEltype ctor kv T = ctor kv) →
    (dictInferred hash eqKey tablesz maxValues (fun x => .ok (cld x)) (typedKey eqKey) (fieldConv V)
      (fun _ => true)
      (fun x => do
        let len ← immutableLength (fun p y => .ok (count p y)) x
        .ok (JInt.lit .i64 (Int.ofNat len)))
      immutableIterStep (fun x => x.length + 1) eltype dictWithEltype d = .ok h ∨
     dictFromIterator hash eqKey tablesz maxValues (fun x => .ok (cld x)) (typedKey eqKey) (fieldConv V)
      (fun _ => true)
      (fun x => do
        let len ← immutableLength (fun p y => .ok (count p y)) x
        .ok (JInt.lit .i64 (Int.ofNat len)))
      immutableIterStep (fun x => x.length + 1) d = .ok h) →
    ∀ (key : K) (default : D), JuliaLean.base.dict.get hash eqKey h key default =
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

/-- Documented laws of the `HAMT` operations of `base/hamt.jl` for keys and values of types
`K` and `V`, in terms of the stored pairs `abs t` of a valid trie `t`. Keys are compared with
`===` (`eqKey`); `runtime.objectid` is the typed Julia identity primitive (`base/dict.jl:946`). -/
structure HamtLaws {H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)) : Prop where
  keys : KeyLaws runtime.objectid eqKey
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
  insert : ∀ t (k : K) (v : V), valid t →
    ∃ t', ops.insert (ops.path t (ops.hashState k) true).top
      (ops.path t (ops.hashState k) true).trie (ops.path t (ops.hashState k) true).found
      (ops.path t (ops.hashState k) true).present (ops.path t (ops.hashState k) true).index
      (ops.path t (ops.hashState k) true).bitmapIndex (ops.path t (ops.hashState k) true).state
      v = some (.ok t') ∧ valid t' ∧ List.Perm (abs t') (rset eqKey (abs t) k v)
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
  length : ∀ t, valid t →
    ops.length t = some (.ok (JInt.lit .i64 (Int.ofNat (abs t).length)))
  isEmpty : ∀ t, valid t → ops.isEmpty t = some (.ok (abs t).isEmpty)

/-- `HAMT` laws when `insert!` throws `"Perfect hash collision"` on distinct keys sharing an
`objectid` (`base/hamt.jl:205-208`). -/
structure HamtCollisionLaws {H HS S : Type} (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K) (eqKey : K → K → Bool)
    (valid : H → Prop) (abs : H → List (K × V)) : Prop where
  keys : KeyLaws runtime.objectid eqKey
  distinct : ∀ t, valid t → Distinct eqKey (abs t)
  empty_valid : valid (ops.empty ())
  empty_abs : abs (ops.empty ()) = []
  singleton : ∀ p : K × V, ∃ t, ops.singleton p = .ok t ∧ valid t ∧ abs t = [p]
  insert : ∀ t (k : K) (v : V) t', valid t →
    ops.insert (ops.path t (ops.hashState k) true).top (ops.path t (ops.hashState k) true).trie
      (ops.path t (ops.hashState k) true).found (ops.path t (ops.hashState k) true).present
      (ops.path t (ops.hashState k) true).index (ops.path t (ops.hashState k) true).bitmapIndex
      (ops.path t (ops.hashState k) true).state v = some (.ok t') →
    valid t' ∧ List.Perm (abs t') (rset eqKey (abs t) k v)
  insert_ok : ∀ t (k : K) (v : V), valid t →
    ((∃ t', ops.insert (ops.path t (ops.hashState k) true).top
      (ops.path t (ops.hashState k) true).trie (ops.path t (ops.hashState k) true).found
      (ops.path t (ops.hashState k) true).present (ops.path t (ops.hashState k) true).index
      (ops.path t (ops.hashState k) true).bitmapIndex (ops.path t (ops.hashState k) true).state
      v = some (.ok t')) ↔
      ∀ e ∈ abs t, runtime.objectid e.1 = runtime.objectid k → eqKey e.1 k = true)

/-- `PersistentDict` lookups (`KeyValue.get`, `haskey`, `getindex`, both `get`s and
`KeyValue.get(default, d, key)`) agree with the stored pairs: a key `===` to a stored key finds its
value, any other key is absent (`KeyError` or the default). -/
def PersistentLookupSemantics : Prop :=
  ∀ (K V D H HS S : Type) (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops runtime eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K) (default : D) (fallback : Unit → DictResult D),
    valid d.trie →
    persistentKeyGet ops d key = rlookup eqKey (abs d.trie) key ∧
    persistentGetindex ops d key =
      (match rlookup eqKey (abs d.trie) key with | some v => .ok v | none => .error .keyError) ∧
    persistentHasKey ops d key = (rlookup eqKey (abs d.trie) key).isSome ∧
    persistentGet ops d key default =
      (match rlookup eqKey (abs d.trie) key with | some v => .inl v | none => .inr default) ∧
    persistentGetDefault ops d key fallback =
      (match rlookup eqKey (abs d.trie) key with | some v => .ok (.inl v) | none => .inr <$> fallback ()) ∧
    persistentGetTypedDefault ops d key fallback =
      (match rlookup eqKey (abs d.trie) key with | some v => .ok (.inl v) | none => .inr <$> fallback ())

/-- `KeyValue.get` reads the leaf `trie.data[i]` (`@inbounds`) only at the end of a path that
`HAMT.path` reports found and present, and only for a stored key, whose value it returns. -/
def PersistentPathSafe : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops runtime eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K) (value : V), valid d.trie →
    persistentKeyGet ops d key = some value →
    ops.isLevelEmpty d.trie = false ∧ (ops.path d.trie (ops.hashState key) false).found = true ∧
    (ops.path d.trie (ops.hashState key) false).present = true ∧
    ops.leafValue (ops.path d.trie (ops.hashState key) false).trie
      (ops.path d.trie (ops.hashState key) false).index = some value ∧
    rlookup eqKey (abs d.trie) key = some value

/-- `KeyValue.set(d, key, val)`, `_keyvalueset(d, key, val)`, `PersistentDict(d, key, val)` and
both `PersistentDict(d, key => val)` convert `key` to `K` and `val` to `V` and return a new
dictionary holding the converted pair and every other pair of `d` (`PersistentDict` docstring:
each operation returns a new dictionary; later `===` keys replace earlier ones). -/
def PersistentSetSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops runtime eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K) (value : V), valid d.trie →
    (∃ d', persistentSetTyped ops d key value = some (.ok d') ∧
      persistentSet ops d key value = some (.ok d') ∧
      persistentInsert ops d key value = some (.ok d') ∧
      valid d'.trie ∧ List.Perm (abs d'.trie) (rset eqKey (abs d.trie) key value)) ∧
    ∀ (Q W HS' S' : Type) (opsHet : PersistentOps K V Q W H HS' S')
      (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (q : Q) (w : W),
      (∀ t q w,
        (let p := opsHet.path t (opsHet.hashState q) true
         opsHet.insert p.top p.trie p.found p.present p.index p.bitmapIndex p.state w) =
        (match keyConv.convert q with
        | .error error => some (.error error)
        | .ok k =>
            match valueConv.convert w with
            | .error error => some (.error error)
            | .ok v =>
                let p := ops.path t (ops.hashState k) true
                ops.insert p.top p.trie p.found p.present p.index p.bitmapIndex p.state v)) →
      match (do let k ← keyConv.convert q; let v ← valueConv.convert w; .ok (k, v) : DictResult (K × V)) with
      | .ok (k, v) =>
        ∃ d', persistentSet opsHet d q w = some (.ok d') ∧
          persistentInsert opsHet d q w = some (.ok d') ∧
          persistentExtend ops keyConv valueConv d q w = some (.ok d') ∧
          persistentExtendPair ops keyConv valueConv d (q, w) = some (.ok d') ∧
          persistentTypedExtendPair ops keyConv valueConv d (q, w) = some (.ok d') ∧
          valid d'.trie ∧ List.Perm (abs d'.trie) (rset eqKey (abs d.trie) k v)
      | .error e =>
        persistentSet opsHet d q w = some (.error e) ∧
        persistentInsert opsHet d q w = some (.error e) ∧
        persistentExtend ops keyConv valueConv d q w = some (.error e) ∧
        persistentExtendPair ops keyConv valueConv d (q, w) = some (.error e) ∧
        persistentTypedExtendPair ops keyConv valueConv d (q, w) = some (.error e)

/-- `KeyValue.set(d, key::K, val::V)` is annotated `:nothrow` (`base/dict.jl:911-912`): it returns
for every key and value. -/
def PersistentSetNothrow : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtCollisionLaws ops runtime eqKey valid abs →
    ∀ (d : PersistentDict K V H) (key : K) (value : V), valid d.trie →
    ∃ d', persistentSetTyped ops d key value = some (.ok d')

/-- `(key => val) in d` is `false` for an absent key and otherwise `valcmp(val, stored)`. -/
def PersistentPairMembershipSemantics : Prop :=
  ∀ (K V R H HS S : Type) (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops runtime eqKey valid abs →
    ∀ (d : PersistentDict K V H) (pair : K × V) (valcmp : V → V → DictResult R), valid d.trie →
    persistentIn ops valcmp d pair =
      (match rlookup eqKey (abs d.trie) pair.1 with
        | none => .ok (.inl false)
        | some stored => .inr <$> valcmp pair.2 stored)

/-- `delete(d, key)` and both `KeyValue.set(d, key)` return a dictionary without `key` that keeps
every other pair of `d` (`PersistentDict` docstring example `Base.delete(dict, :a)`). -/
def PersistentDeleteSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops runtime eqKey valid abs →
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
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops runtime eqKey valid abs →
    ∀ d : PersistentDict K V H, valid d.trie →
    List.Perm (persistentCollectFuel ops d ((abs d.trie).length + 1) none) (abs d.trie) ∧
    persistentLength ops d = some (.ok (JInt.lit .i64 (Int.ofNat (abs d.trie).length))) ∧
    persistentIsEmpty ops d = some (.ok (abs d.trie).isEmpty) ∧
    persistentEltype K V = (K × V) ∧
    valid (persistentEmptyLike ops d).trie ∧ abs (persistentEmptyLike ops d).trie = [] ∧
    (persistentOnly ops d = some
      (if (JInt.lit .i64 (Int.ofNat (abs d.trie).length)).val = 1 then
        match (persistentCollectFuel ops d ((abs d.trie).length + 1) none).head? with
        | some e => .ok e
        | none => .error (.inr (.argumentError "PersistentDict must be non-empty"))
      else .error (.inr (.argumentError "Collection must contain exactly 1 element"))))

/-- `PersistentDict{K,V}()` and `KeyValue.set(PersistentDict{K,V})` are empty; the one-pair
constructors hold their converted pair (propagating conversion errors); the multi-pair
constructors hold the converted pairs in argument order, a later `===` key replacing an earlier
one, and propagate the first conversion error. -/
def persistentConvPair {Q W : Type} (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (p : Q × W) : DictResult (K × V) := do
  let k ← keyConv.convert p.1
  let v ← valueConv.convert p.2
  .ok (k, v)

def PersistentConstructorSemantics : Prop :=
  ∀ (K V H HS S : Type) (ops : PersistentOps K V K V H HS S)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (eqKey : K → K → Bool) (valid : H → Prop) (abs : H → List (K × V)),
    HamtLaws ops runtime eqKey valid abs →
    (valid (persistentEmpty ops).trie ∧ abs (persistentEmpty ops).trie = [] ∧
      valid (persistentEmptyConstructor ops).trie ∧ abs (persistentEmptyConstructor ops).trie = []) ∧
    (∀ (key : K) (value : V), ∃ d, persistentSingleton ops key value = .ok d ∧
      persistentTypedPair ops (key, value) = .ok d ∧ persistentPair ops (key, value) = .ok d ∧
      valid d.trie ∧ abs d.trie = [(key, value)]) ∧
    ∀ (Q W HS' S' : Type) (opsPair : PersistentOps K V Q W H HS' S') (keyConv : KeyConv Q K)
      (valueConv : ValueConv W V),
      (∀ q w, opsPair.singleton (q, w) =
        (do let k ← keyConv.convert q; let v ← valueConv.convert w; ops.singleton (k, v))) →
      ∀ (first : K × V) (q : Q) (w : W) (rest : List (Q × W)),
      let conv := persistentConvPair keyConv valueConv
      (match conv (q, w) with
        | .ok p => ∃ d, persistentSingleton opsPair q w = .ok d ∧
            persistentTypedPair opsPair (q, w) = .ok d ∧ valid d.trie ∧ abs d.trie = [p]
        | .error e => persistentSingleton opsPair q w = .error e ∧
            persistentTypedPair opsPair (q, w) = .error e) ∧
      (match rest.mapM conv with
        | .ok ps => ∃ d, persistentPairs ops keyConv valueConv first rest = some (.ok d) ∧
            valid d.trie ∧ List.Perm (abs d.trie) (ps.foldl (fun m p => rset eqKey m p.1 p.2) [first])
        | .error e => persistentPairs ops keyConv valueConv first rest = some (.error e)) ∧
      (match (do let p ← conv (q, w); let ps ← rest.mapM conv; .ok (p, ps)) with
        | .ok (p, ps) => ∃ d, persistentTypedPairs opsPair ops keyConv valueConv q w rest = some (.ok d) ∧
            valid d.trie ∧ List.Perm (abs d.trie) (ps.foldl (fun m p => rset eqKey m p.1 p.2) [p])
        | .error e => persistentTypedPairs opsPair ops keyConv valueConv q w rest = some (.error e))

section PersistentProofs
variable {H HS S : Type} {ops : PersistentOps K V K V H HS S}
  {runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K}
  {eqKey : K → K → Bool} {valid : H → Prop} {abs : H → List (K × V)}

theorem HamtLaws.keyGet (hl : HamtLaws ops runtime eqKey valid abs) (d : PersistentDict K V H)
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
        (ops.path d.trie (ops.hashState key) true).state value).map (Except.map PersistentDict.mk) := by
  rfl

theorem HamtLaws.setTyped (hl : HamtLaws ops runtime eqKey valid abs) (d : PersistentDict K V H)
    (key : K) (value : V) (hv : valid d.trie) :
    ∃ d', persistentSetTyped ops d key value = some (.ok d') ∧
      valid d'.trie ∧ List.Perm (abs d'.trie) (rset eqKey (abs d.trie) key value) := by
  rw [persistentSetTyped_eq]
  obtain ⟨t', ht', hv', hp'⟩ := hl.insert d.trie key value hv
  rw [ht']
  exact ⟨⟨t'⟩, rfl, hv', hp'⟩

theorem PersistentLookupSemantics_proven : PersistentLookupSemantics := by
  intro K V D H HS S ops runtime eqKey valid abs hl d key default fallback hv
  have hk := hl.keyGet d key hv
  refine ⟨hk, ?_, ?_, ?_, ?_, ?_⟩
  · unfold persistentGetindex; rw [hk] <;> cases rlookup eqKey (abs d.trie) key <;> rfl
  · unfold persistentHasKey; rw [hk]
  · unfold persistentGet; rw [hk]; cases rlookup eqKey (abs d.trie) key <;> rfl
  · unfold persistentGetDefault; rw [hk]
    cases rlookup eqKey (abs d.trie) key <;> rfl
  · unfold persistentGetTypedDefault; rw [hk]
    cases rlookup eqKey (abs d.trie) key <;> rfl

theorem PersistentPathSafe_proven : PersistentPathSafe := by
  intro K V H HS S ops runtime eqKey valid abs hl d key value hv hget
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
  intro K V H HS S ops runtime eqKey valid abs hl d key value hv
  obtain ⟨d', hd', hv', hp'⟩ := hl.setTyped d key value hv
  refine ⟨⟨d', hd', hd', hd', hv', hp'⟩, ?_⟩
  intro Q W HS' S' opsHet keyConv valueConv q w hhet
  have hins : persistentInsert opsHet d q w = persistentExtend ops keyConv valueConv d q w := by
    unfold persistentInsert persistentExtend persistentSetTyped
    dsimp only
    rw [hhet d.trie q w]
    cases keyConv.convert q with
    | error e => rfl
    | ok k =>
      cases valueConv.convert w with
      | error e => rfl
      | ok v => rfl
  have hset : persistentSet opsHet d q w = persistentExtend ops keyConv valueConv d q w := hins
  have hexp : persistentExtendPair ops keyConv valueConv d (q, w) =
      persistentExtend ops keyConv valueConv d q w := rfl
  have htexp : persistentTypedExtendPair ops keyConv valueConv d (q, w) =
      persistentExtend ops keyConv valueConv d q w := rfl
  rw [hset, hins, hexp, htexp]
  unfold persistentExtend
  cases hk : keyConv.convert q with
  | error e => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | ok k =>
    cases hw : valueConv.convert w with
    | error e => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | ok v =>
      dsimp only [bind, Except.bind, pure, Except.pure]
      obtain ⟨d1, hd1, hv1, hp1⟩ := hl.setTyped d k v hv
      exact ⟨d1, hd1, hd1, hd1, hd1, hd1, hv1, hp1⟩

theorem PersistentPairMembershipSemantics_proven : PersistentPairMembershipSemantics := by
  intro K V R H HS S ops runtime eqKey valid abs hl d pair valcmp hv
  unfold persistentIn
  rw [hl.keyGet d pair.1 hv] <;> cases rlookup eqKey (abs d.trie) pair.1 <;> rfl

theorem HamtLaws.deleteKey (hl : HamtLaws ops runtime eqKey valid abs) (d : PersistentDict K V H)
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
  intro K V H HS S ops runtime eqKey valid abs hl d key hv
  exact ⟨hl.deleteKey d key hv, hl.deleteKey d key hv, hl.deleteKey d key hv⟩

theorem persistentCollectFuel_eq {Q W : Type} (ops : PersistentOps K V Q W H HS S)
    (d : PersistentDict K V H) : ∀ n s, persistentCollectFuel ops d n s = trieCollect ops d.trie n s
  | 0, _ => rfl
  | n + 1, s => by
    simp only [persistentCollectFuel, trieCollect, persistentIterate]
    cases ops.iterate d.trie s with
    | none => rfl
    | some p => simp only [persistentCollectFuel_eq ops d n]


/-- One `PersistentDict(d, key, value)` per pair, from a valid dictionary whose pairs are a
permutation of `m0`. -/
theorem HamtLaws.extendMany_spec (hl : HamtLaws ops runtime eqKey valid abs) {Q W : Type}
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) :
    ∀ (rest : List (Q × W)) (d0 : PersistentDict K V H) (m0 : List (K × V)), valid d0.trie →
      List.Perm (abs d0.trie) m0 →
      let conv := persistentConvPair keyConv valueConv
      match rest.mapM conv with
      | .ok ps => ∃ d, persistentExtendMany ops keyConv valueConv d0 rest = some (.ok d) ∧
          valid d.trie ∧ List.Perm (abs d.trie) (ps.foldl (fun m p => rset eqKey m p.1 p.2) m0)
      | .error e => persistentExtendMany ops keyConv valueConv d0 rest = some (.error e)
  | [], d0, m0, hv, hp => ⟨d0, rfl, hv, hp⟩
  | (q, w) :: rest, d0, m0, hv, hp => by
    dsimp only
    simp only [List.mapM_cons]
    rw [persistentConvPair]
    unfold persistentExtendMany persistentExtend
    cases hk : keyConv.convert q with
    | error e => rfl
    | ok k =>
      cases hw : valueConv.convert w with
      | error e => rfl
      | ok v =>
        dsimp only [bind, Except.bind, pure, Except.pure]
        obtain ⟨d1, hd1, hv1, hp1⟩ := hl.setTyped d0 k v hv
        rw [hd1]
        dsimp only
        have ih := hl.extendMany_spec keyConv valueConv rest d1 (rset eqKey m0 k v) hv1
          (hp1.trans (rset_perm hp k v))
        dsimp only at ih
        cases hrm : rest.mapM (persistentConvPair keyConv valueConv) with
        | error e =>
          rw [hrm] at ih
          exact ih
        | ok ps =>
          rw [hrm] at ih
          exact ih

theorem PersistentConstructorSemantics_proven : PersistentConstructorSemantics := by
  intro K V H HS S ops runtime eqKey valid abs hl
  refine ⟨⟨hl.empty_valid, hl.empty_abs, hl.empty_valid, hl.empty_abs⟩, fun key value => ?_, ?_⟩
  · obtain ⟨t, ht, hv, ha⟩ := hl.singleton (key, value)
    have e : persistentSingleton ops key value = .ok ⟨t⟩ := by
      unfold persistentSingleton; rw [ht]; rfl
    exact ⟨⟨t⟩, e, e, e, hv, ha⟩
  intro Q W HS' S' opsPair keyConv valueConv hsing first q w rest
  dsimp only
  obtain ⟨t1, ht1, hv1, ha1⟩ := hl.singleton first
  have hpair : persistentPair ops first = .ok ⟨t1⟩ := by
    unfold persistentPair persistentSingleton; rw [ht1]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [persistentConvPair]
    unfold persistentTypedPair persistentSingleton
    rw [hsing]
    cases hk : keyConv.convert q with
    | error e => exact ⟨rfl, rfl⟩
    | ok k =>
      cases hw : valueConv.convert w with
      | error e => exact ⟨rfl, rfl⟩
      | ok v =>
        dsimp only [bind, Except.bind, pure, Except.pure]
        obtain ⟨t, ht, hv, ha⟩ := hl.singleton (k, v)
        rw [ht]
        exact ⟨⟨t⟩, rfl, rfl, hv, ha⟩
  · unfold persistentPairs
    rw [hpair]
    dsimp only [bind, Except.bind]
    exact hl.extendMany_spec keyConv valueConv rest ⟨t1⟩ [first] hv1 (by rw [ha1])
  · rw [persistentConvPair]
    unfold persistentTypedPairs persistentTypedPair persistentSingleton
    rw [hsing]
    cases hk : keyConv.convert q with
    | error e => rfl
    | ok k =>
      cases hw : valueConv.convert w with
      | error e => rfl
      | ok v =>
        dsimp only [bind, Except.bind, pure, Except.pure]
        obtain ⟨t, ht, hv, ha⟩ := hl.singleton (k, v)
        rw [ht]
        dsimp only
        have hex := hl.extendMany_spec keyConv valueConv rest ⟨t⟩ [(k, v)] hv (by rw [ha])
        dsimp only at hex
        cases hrm : rest.mapM (persistentConvPair keyConv valueConv) with
        | error e =>
          rw [hrm] at hex
          exact hex
        | ok ps =>
          rw [hrm] at hex
          exact hex
end PersistentProofs

/-! ## `_similar_for` -/

/-- `_similar_for(c, Pair{K,V}, ...)` returns `empty(c, K, V)`, an empty dictionary of the kind of
`c` (`Dict`, `ImmutableDict` or `PersistentDict`); any other element type throws `ArgumentError`
("similar requires an element type of Pair"). -/
def DictSimilarSemantics : Prop :=
  ∀ (K V C D : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (c : C),
    DictRep hash eqKey (similarForPairs K V c) [] ∧
    (∀ d : ImmutableDict K V, immutableCollect (similarForPairs K V d) = []) ∧
    (∀ (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K) (H HS S : Type)
      (ops : PersistentOps K V K V H HS S) (valid : H → Prop) (abs : H → List (K × V)),
      HamtLaws ops runtime eqKey valid abs → ∀ d : PersistentDict K V H,
      letI : AbstractDictEmpty (PersistentDict K V H) K V (PersistentDict K V H) := persistentEmptyDictInst ops
      valid (similarForPairs K V d).trie ∧
        abs (similarForPairs K V d).trie = []) ∧
    similarForOther (D := D) c = .error .argumentError

theorem DictSimilarSemantics_proven : DictSimilarSemantics := by
  intro K V C D hash eqKey c
  exact ⟨dictEmpty_rep hash eqKey, fun _ => rfl,
    fun runtime _ _ _ ops valid abs hl _ => by
      letI : AbstractDictEmpty (PersistentDict K V _) K V (PersistentDict K V _) := persistentEmptyDictInst ops
      exact ⟨hl.empty_valid, hl.empty_abs⟩, rfl⟩

/-! ## `mergewith!` and `reduce(merge, items)` -/

/-- `mergewith!(combine, d1, d2)` (docstring `base/abstractdict.jl`): for each pair `k => v` of
`d2` in iteration order, a stored key `isequal` to `k` gets `combine(old, v)`; any other `k` is
added like `setindex!` (converted, `KeyTypeError` when the conversion is not `isequal`). -/
def refMergeStep {Q W R : Type} (eqKey : K → K → Bool) (matchQ : Q → K → Bool)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combineConv : ValueConv R V) (combine : V → W → DictResult R)
    (m : List (K × V)) (p : Q × W) : DictResult (List (K × V)) :=
  match rfind matchQ m p.1 with
  | some e => do
    let r ← combine e.2 p.2
    let v ← convertValue combineConv r
    .ok (rset eqKey m e.1 v)
  | none => refStep eqKey keyConv valueConv m p

/-- `mergewith!(combine, d1, d2)` merges the pairs of `d2` into `d1` in iteration order, combining
values of keys `isequal` to stored ones with `combine(old, new)` (converted to `V`), and propagates
the first error (`mergewith!` docstring, `base/abstractdict.jl`). -/
def DictMergewithSemantics : Prop :=
  ∀ (K V Q W R D S I : Type) [DictInteger I] (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (hashQ : Q → JInt .u64) (matchQ : Q → K → Bool) (tablesz : Nat → Nat)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combineConv : ValueConv R V) (combine : V → W → DictResult R)
    (haslength : D → Bool) (lengthD2 : D → DictResult I)
    (iterateD2 : D → Option S → DictResult (Option ((Q × W) × S))) (boundD2 : D → Nat)
    (h : DictState K V) (m : List (K × V)) (d2 : D) (pairsD2 : List (Q × W)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → TableszLaw tablesz →
    (∀ q k, keyConv.convert q = .ok k → keyConv.isequal q k = true → ∀ k', matchQ q k' = eqKey k k') →
    (∀ q k, keyConv.isa q = some k → ∀ k', matchQ q k' = eqKey k k') →
    iterCollectPairs iterateD2 d2 (boundD2 d2) none = .ok pairsD2 →
    DictRep hash eqKey h m →
    match (if haslength d2 then lengthD2 d2 >>= DictInteger.toInt else .ok (JInt.lit .i64 0)) with
    | .error e => mergewithBang hash hashQ matchQ tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
        combineConv combine haslength lengthD2 iterateD2 boundD2 h d2 = .error e
    | .ok _ =>
      match pairsD2.foldlM (refMergeStep eqKey matchQ keyConv valueConv combineConv combine) m with
      | .ok m' => ∃ h', mergewithBang hash hashQ matchQ tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
          combineConv combine haslength lengthD2 iterateD2 boundD2 h d2 = .ok h' ∧ DictRep hash eqKey h' m'
      | .error e => mergewithBang hash hashQ matchQ tablesz maxValues (fun x => .ok (cld x)) keyConv valueConv
          combineConv combine haslength lengthD2 iterateD2 boundD2 h d2 = .error e
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
      KeyLaws hash eqKey → TableszLaw tablesz →
      (∀ h0 : DictState K V, mergeItems (x :: xs) h0 = (x :: xs).foldlM (fun h y => do
        let h ← sizehint hash tablesz maxValues (fun x => .ok (cld x)) h
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
    {t : DictState K V} (hi : Inv hash eqKey t) (hc : True) {q : Q} {j : Nat}
    (hj : InsertSlot t (home hashQ t.size q) j) (habs : ∀ e ∈ tlist t, matchQ q e.1 = false)
    (k : K) (hk : ∀ k', matchQ q k' = eqKey k k') (v : V) :
    ∃ t', setindexAt hash tablesz t v k j (shorthash7 (hashQ q)) = .ok ((), t') ∧
      Inv hash eqKey t' ∧ List.Perm (tlist t') ((k, v) :: tlist t) ∧ t'.count = t.count + 1 := by
  have hh : hashQ q = hash k := hq.hash_eq q k (by rw [hk]; exact hl.refl k)
  have hhome : home hashQ t.size q = home hash t.size k := by
    unfold home; rw [hh]
  rw [hhome] at hj
  rw [hh]
  obtain ⟨t', h', hi', hp', hc', -⟩ :=
    setindexAt_spec hl htz hi hc hj (fun e he => by rw [← hk]; exact habs e he) (v := v)
  exact ⟨t', h', hi', hp', hc'⟩

theorem convertKey_eq {Q : Type} (keyConv : KeyConv Q K) (q : Q) :
    convertKey keyConv q = convKey keyConv q := rfl

theorem mergewithStep_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz)
    {Q W R : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combineConv : ValueConv R V) (combine : V → W → DictResult R)
    (hc1 : ∀ q k, keyConv.convert q = .ok k → keyConv.isequal q k = true →
      ∀ k', matchQ q k' = eqKey k k')
    (hc2 : ∀ q k, keyConv.isa q = some k → ∀ k', matchQ q k' = eqKey k k')
    (q : Q) (w : W) (t : DictState K V) (m : List (K × V)) (hr : DictRep hash eqKey t m) :
    match refMergeStep eqKey matchQ keyConv valueConv combineConv combine m (q, w) with
    | .ok m1 => ∃ t1, mergewithStep hash hashQ matchQ tablesz keyConv valueConv
        combineConv combine t q w = .ok t1 ∧ DictRep hash eqKey t1 m1
    | .error e => mergewithStep hash hashQ matchQ tablesz keyConv valueConv
        combineConv combine t q w = .error e := by
  obtain ⟨idx, t1, n, hprobe, -, hout⟩ := htKeyindex2Query_spec hl hq htz hr.1 trivial q
  have hd : Distinct eqKey (tlist t) := tlist_pairwise hr.1
  have hfp : rfind matchQ (tlist t) q = rfind matchQ m q := rfind_perm hl hq hd hr.2 q
  unfold mergewithStep
  rw [hprobe, except_ok_bind]
  dsimp only
  cases hf : rfind matchQ (tlist t) q with
  | some e =>
    obtain ⟨hem, heq⟩ := rfind_some hf
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 hem
    obtain ⟨hidx, ht1⟩ := hout.found i e h1 h2 hei heq
    subst hidx; subst t1
    have hstep : refMergeStep eqKey matchQ keyConv valueConv combineConv combine m (q, w) =
        (combine e.2 w >>= fun r => convertValue combineConv r >>= fun v =>
          .ok (rset eqKey m e.1 v)) := by
      unfold refMergeStep; rw [← hfp, hf]
    rw [hstep, ite_eq_left (by omega)]
    have hti : ((i : Int)).toNat = i := by omega
    rw [hti]
    obtain ⟨-, hk0, hv0⟩ := ent_some hei
    have hval : valAt t i = .ok e.2 := by unfold valAt; rw [hv0]
    rw [hval, except_ok_bind]
    cases hcomb : combine e.2 w with
    | error err => rfl
    | ok r0 =>
      rw [except_ok_bind, except_ok_bind]
      cases hconvV : convertValue combineConv r0 with
      | error err => rfl
      | ok v' =>
        rw [except_ok_bind, except_ok_bind]
        obtain ⟨k0, v0⟩ := e
        obtain ⟨hi2, hp2⟩ := Inv.overwrite hl hr.1 h1 h2 hei (hl.refl k0)
          (t' := DictState.mk t.size t.slots t.keys (updateAt t.vals i (some v')) t.ndel t.count
            t.age t.idxfloor t.maxprobe t.popcursor)
          rfl rfl (by show t.keys = _; rw [← hk0, updateAt_self]) rfl rfl rfl rfl rfl
        exact ⟨_, rfl, hi2, hp2.trans (rset_perm hr.2 k0 v')⟩
  | none =>
    have habs := rfind_eq_none_iff.1 hf
    obtain ⟨hneg, hslot⟩ := hout.absent habs
    have hmnone : rfind matchQ m q = none := by rw [← hfp]; exact hf
    have habs1 : ∀ e ∈ tlist t1, matchQ q e.1 = false :=
      fun e he => habs e (hout.perm.mem_iff.1 he)
    have hstep : refMergeStep eqKey matchQ keyConv valueConv combineConv combine m (q, w) =
        refStep eqKey keyConv valueConv m (q, w) := by
      unfold refMergeStep; rw [hmnone]
    rw [hstep, ite_eq_right (by omega)]
    have finish : ∀ k, (∀ k', matchQ q k' = eqKey k k') → ∀ v,
        ∃ t2, (setindexAt hash tablesz t1 v k (-idx).toNat (shorthash7 (hashQ q)) >>=
          fun r => Except.ok r.2) = .ok t2 ∧ DictRep hash eqKey t2 (rset eqKey m k v) := by
      intro k hk v
      obtain ⟨t2, hs2, hi2, hp2, -⟩ := mergeAbsent hl htz hq hout.inv trivial hslot habs1 k hk v
      rw [hs2, except_ok_bind]
      have hmabs : ∀ e ∈ m, eqKey k e.1 = false := fun e he => by
        rw [← hk]; exact rfind_eq_none_iff.1 hmnone e he
      refine ⟨t2, rfl, hi2, ?_⟩
      unfold rset
      rw [rdel_absent hmabs]
      exact hp2.trans ((hout.perm.trans hr.2).cons _)
    have hck : ∀ k, convKey keyConv q = .ok k → ∀ k', matchQ q k' = eqKey k k' := by
      intro k hck
      unfold convKey at hck
      cases hisa : keyConv.isa q with
      | some k0 =>
        rw [hisa] at hck
        cases hck
        exact hc2 q k hisa
      | none =>
        rw [hisa] at hck
        cases hconv : keyConv.convert q with
        | error e => rw [hconv] at hck; cases hck
        | ok k0 =>
          rw [hconv] at hck
          dsimp only at hck
          by_cases hie : keyConv.isequal q k0 = true
          · rw [ite_eq_left hie] at hck
            cases hck
            exact hc1 q k hconv hie
          · rw [ite_eq_right hie] at hck
            cases hck
    unfold refStep
    rw [convertKey_eq]
    cases hk : convKey keyConv q with
    | error e => rfl
    | ok k =>
      rw [except_ok_bind, except_ok_bind]
      cases hv : convertValue valueConv w with
      | error e => rfl
      | ok v =>
        rw [except_ok_bind, except_ok_bind]
        exact finish k (hck k hk) v

theorem mergewithLoop_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz)
    {Q W R D S : Type} {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (hq : QueryLaws hash eqKey hashQ matchQ)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V)
    (combineConv : ValueConv R V) (combine : V → W → DictResult R)
    (iterateD2 : D → Option S → DictResult (Option ((Q × W) × S))) (d2 : D)
    (hc1 : ∀ q k, keyConv.convert q = .ok k → keyConv.isequal q k = true →
      ∀ k', matchQ q k' = eqKey k k')
    (hc2 : ∀ q k, keyConv.isa q = some k → ∀ k', matchQ q k' = eqKey k k') :
    ∀ (fuel : Nat) (state : Option S) (pairs : List (Q × W))
      (t : DictState K V) (m : List (K × V)),
      iterCollectPairs iterateD2 d2 fuel state = .ok pairs →
      DictRep hash eqKey t m →
      match pairs.foldlM (refMergeStep eqKey matchQ keyConv valueConv combineConv combine) m with
      | .ok m' => ∃ t', mergewithLoop hash hashQ matchQ tablesz keyConv valueConv
          combineConv combine iterateD2 d2 fuel state t = .ok t' ∧ DictRep hash eqKey t' m'
      | .error e => mergewithLoop hash hashQ matchQ tablesz keyConv valueConv
          combineConv combine iterateD2 d2 fuel state t = .error e
  | 0, state, pairs, t, _, hcol, hr => by
    cases hcol
    exact ⟨t, rfl, hr⟩
  | fuel + 1, state, pairs, t, m, hcol, hr => by
    rw [iterCollectPairs] at hcol
    rw [mergewithLoop]
    cases hit : iterateD2 d2 state with
    | error e => rw [hit] at hcol; cases hcol
    | ok step =>
      rw [hit] at hcol
      dsimp only [bind, Except.bind, pure, Except.pure] at hcol ⊢
      cases step with
      | none =>
        cases hcol
        exact ⟨t, rfl, hr⟩
      | some ps =>
        obtain ⟨⟨q, w⟩, nextState⟩ := ps
        dsimp only [bind, Except.bind, pure, Except.pure] at hcol ⊢
        cases hrest : iterCollectPairs iterateD2 d2 fuel (some nextState) with
        | error e => rw [hrest] at hcol; cases hcol
        | ok rest =>
          rw [hrest] at hcol
          cases hcol
          rw [List.foldlM_cons]
          have hs := mergewithStep_spec hl htz hq keyConv valueConv combineConv combine
            hc1 hc2 q w t m hr
          cases hrm : refMergeStep eqKey matchQ keyConv valueConv combineConv combine m (q, w) with
          | error e =>
            rw [hrm] at hs
            rw [hs]
            rfl
          | ok m1 =>
            rw [hrm] at hs
            obtain ⟨t1, ht1, hr1⟩ := hs
            rw [ht1]
            dsimp only [bind, Except.bind]
            exact mergewithLoop_spec hl htz hq keyConv valueConv combineConv combine
              iterateD2 d2 hc1 hc2 fuel (some nextState) rest t1 m1 hrest hr1
theorem DictMergewithSemantics_proven : DictMergewithSemantics := by
  intro K V Q W R D S I _ hash eqKey hashQ matchQ tablesz maxValues cld keyConv valueConv
    combineConv combine haslength lengthD2 iterateD2 boundD2 h m d2 pairsD2
    hl hq htz hc1 hc2 hcol hr
  unfold mergewithBang
  dsimp only
  cases hhl : haslength d2 with
  | true =>
    simp only [ite_true]
    cases hlen : lengthD2 d2 with
    | error e => simp only [except_error_bind]
    | ok len =>
      simp only [except_ok_bind]
      cases hconv : DictInteger.toInt len with
      | error e => simp only [except_error_bind]
      | ok len2 =>
        simp only [except_ok_bind]
        obtain ⟨t1, hs, hr1, -⟩ :=
          sizehint_no_shrink htz maxValues cld hr (JInt.lit .i64 (Int.ofNat (length h) + len2.val))
        rw [hs, except_ok_bind]
        exact mergewithLoop_spec hl htz hq keyConv valueConv combineConv combine
          iterateD2 d2 hc1 hc2 (boundD2 d2) none pairsD2 t1 m hcol hr1
  | false =>
    simp only [Bool.false_eq_true, ite_false, except_ok_bind]
    exact mergewithLoop_spec hl htz hq keyConv valueConv combineConv combine
      iterateD2 d2 hc1 hc2 (boundD2 d2) none pairsD2 h m hcol hr
/-- `reduce(merge!, items; init)`: `merge!(d, item)` for each item in turn (`sizehint!` then
`d[k] = v` for every pair of the item). -/
theorem mergeItems_spec (hl : KeyLaws hash eqKey) (htz : TableszLaw tablesz)
    (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    {D Q W : Type} (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pairsOf : D → List (Q × W)) :
    ∀ (items : List D) (t : DictState K V) (m : List (K × V)), DictRep hash eqKey t m →
      match (items.flatMap pairsOf).foldlM (refStep eqKey keyConv valueConv) m with
      | .ok m' => ∃ t', items.foldlM (fun h y => do
            let h ← sizehint hash tablesz maxValues (fun x => .ok (cld x)) h
              (JInt.lit .i64 (Int.ofNat (h.count + (pairsOf y).length))) false
            (pairsOf y).foldlM (fun h (p : Q × W) =>
              setindexConv hash eqKey tablesz keyConv valueConv h p.2 p.1) h)
            t = .ok t' ∧ DictRep hash eqKey t' m'
      | .error e => items.foldlM (fun h y => do
            let h ← sizehint hash tablesz maxValues (fun x => .ok (cld x)) h
              (JInt.lit .i64 (Int.ofNat (h.count + (pairsOf y).length))) false
            (pairsOf y).foldlM (fun h (p : Q × W) =>
              setindexConv hash eqKey tablesz keyConv valueConv h p.2 p.1) h)
            t = .error e
  | [], t, m, hr => ⟨t, rfl, hr⟩
  | y :: ys, t, m, hr => by
    obtain ⟨t1, hs, hr1, -⟩ := sizehint_no_shrink htz maxValues cld hr
      (JInt.lit .i64 (Int.ofNat (t.count + (pairsOf y).length)))
    have hloop := insertLoop_spec hl htz keyConv valueConv
      (fun ps t => ps.foldlM (fun h (p : Q × W) =>
        setindexConv hash eqKey tablesz keyConv valueConv h p.2 p.1) t)
      (fun _ => rfl) (fun p rest t => rfl) (pairsOf y) t1 m hr1 trivial
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
      exact mergeItems_spec hl htz maxValues cld keyConv valueConv pairsOf ys t2 m1 hr2

end Merge

theorem DictReduceMergeSemantics_proven : DictReduceMergeSemantics := by
  intro D keytype valtype promoteType mapreduce mergeItems hmr0 hmr1
  refine ⟨?_, ?_⟩
  · unfold reduceMerge; rw [hmr0]
  · intro x xs K V Q W hash eqKey tablesz maxValues cld keyConv valueConv pairsOf hK hV hl htz hmerge
    subst hK hV
    have hspec := mergeItems_spec hl htz maxValues cld keyConv valueConv pairsOf (x :: xs)
      (dictEmpty _ _) [] (dictEmpty_rep hash eqKey)
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
  simp only [ne_eq, not_true_eq_false, ite_false] at hr
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
    sizehint hash tablesz maxValues (fun x => .ok (cld x)) h (JInt.lit .i64 (2 ^ 62)) true ≠ .ok h' := by
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
  have hN : tablesz Y.val.toNat = 16 := by rw [hY0, htz 0]; decide
  unfold sizehint at hs
  simp only [DictInteger.toInt, except_ok_bind] at hs
  rw [hY, hN] at hs
  split at hs
  · rename_i hcond
    simp at hcond
    omega
  · have := rehash_ok_size hs
    rw [htz 16] at this
    have h16 : tableszSpec 16 = 16 := by decide
    omega

/-- Seventeen keys `0, ..., 16` with unit values. -/
def pairs17 : List (Nat × Unit) := (List.range 17).map fun i => (i, ())

theorem DictSizehintTotal_refuted : ¬ DictSizehintTotal := by
  intro hT
  have hb := DictConstructorSemantics_proven Nat Unit Nat Unit natHash natEq tableszSpec
    (2 ^ 63 - 1) cldSpec (typedKey natEq) (fieldConv Unit) pairs17 natKeyLaws (fun _ => rfl)
  rw [show refBuild natEq (typedKey natEq) (fieldConv Unit) pairs17 =
    .ok (pairs17.reverse) from rfl] at hb
  obtain ⟨h, -, hr⟩ := hb
  obtain ⟨h', hs, hr'⟩ := hT Nat Unit natHash natEq tableszSpec (2 ^ 63 - 1) cldSpec h
    pairs17.reverse natKeyLaws (fun _ => rfl) (Or.inl (by decide)) cldSpec_law hr
    (JInt.lit .i64 (2 ^ 62)) true
  exact sizehint_wrap_not_ok (fun _ => rfl) (by decide) (by decide) cldSpec_law hr (by decide)
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
  let count : (Nat × Nat → Bool) → ImmutableDict Nat Nat → Nat :=
    fun p d => (immutableCollect d).countP p
  have hcount : CountLaw count := fun _ _ => rfl
  have hb := DictIteratorConstructorSemantics_proven Nat Nat Nat Nat (ImmutableDict Nat Nat)
    (ImmutableDict Nat Nat) (JInt .i64) natHash natEq tableszSpec (2 ^ 63 - 1) cldSpec
    (typedKey natEq) (fieldConv Nat) (fun _ => true)
    (fun x => do
      let len ← immutableLength (fun p y => .ok (count p y)) x
      .ok (JInt.lit .i64 (Int.ofNat len)))
    immutableIterStep (fun x => x.length + 1) [(0, 2), (0, 1)] [(0, 2), (0, 1)]
    natKeyLaws (fun _ => rfl) (iterCollectPairs_immutableIterStep [(0, 2), (0, 1)])
  dsimp only [bind, Except.bind, DictInteger.toInt] at hb
  rw [show refBuild natEq (typedKey natEq) (fieldConv Nat) [(0, 2), (0, 1)] =
    .ok [(0, 1)] from rfl] at hb
  obtain ⟨h, hh, hr⟩ := hb
  have hlook := (DictLookupSemantics_proven Nat Nat Nat Nat Nat Nat natHash natEq natHash natEq h
    [(0, 1)] natKeyLaws natKeyLaws.query hr 0 0 0 (fun _ => .ok 0)).2.1
  have := hT Nat Nat Nat natHash natEq tableszSpec (2 ^ 63 - 1) cldSpec count
    (fun _ => Nat × Nat) (fun ctor kv _ => ctor kv) [(0, 2), (0, 1)] h natKeyLaws
    (fun _ => rfl) hcount (fun _ _ _ => rfl) (Or.inl hh) 0 0
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
  insert _ _ found _ _ _ k v := some (if found then .ok [(k, v)] else .error .thrownDict)
  deleteAt _ _ _ := []
  unset top _ _ := top
  isLevelEmpty t := t.isEmpty
  leafValue t _ := t.head?.map (·.2)
  iterate t s := (t[s.getD 0]?).map fun p => (p, s.getD 0 + 1)
  length t := some (.ok (JInt.lit .i64 (Int.ofNat t.length)))
  isEmpty t := some (.ok t.isEmpty)

def boolHash (_ : Bool) : JInt .u64 := JInt.lit .u64 0

def boolEq (a b : Bool) : Bool := a == b

theorem collideOps_laws :
    HamtCollisionLaws collideOps (⟨boolHash⟩ : JuliaLean.base.hamt.HamtObjectIdRuntime Bool)
      boolEq (fun t => t.length ≤ 1) (fun t => t) := by
  refine ⟨⟨by decide, by decide, by decide, fun _ _ _ => rfl⟩, ?_, by decide, rfl,
    fun p => ⟨[p], rfl, Nat.le_refl _, rfl⟩, ?_, ?_⟩
  · intro t ht
    rcases len_le_one ht with rfl | ⟨a, rfl⟩ <;> simp
  · intro t k v t' ht
    rcases len_le_one ht with rfl | ⟨⟨a, u⟩, rfl⟩
    · intro h; cases h; exact ⟨Nat.le_refl _, by cases k <;> cases v <;> decide⟩
    · cases a <;> cases k <;> cases u <;> cases v <;> intro h <;>
        first | (cases h; exact ⟨by decide, by decide⟩) | cases h
  · intro t k v ht
    rcases len_le_one ht with rfl | ⟨⟨a, u⟩, rfl⟩
    · exact ⟨fun _ _ he => absurd he (List.not_mem_nil), fun _ => ⟨[(k, v)], rfl⟩⟩
    · cases a <;> cases k <;> cases u <;> cases v <;> simp [collideOps, boolHash, boolEq]

/-- `KeyValue.set(d, false, nothing)` on `d = PersistentDict(true => nothing)` whose keys collide
throws "Perfect hash collision". -/
theorem PersistentSetNothrow_refuted : ¬ PersistentSetNothrow := by
  intro h
  obtain ⟨d', hd⟩ := h Bool Unit (List (Bool × Unit)) Bool Nat collideOps
    (⟨boolHash⟩ : JuliaLean.base.hamt.HamtObjectIdRuntime Bool) boolEq
    (fun t => t.length ≤ 1) (fun t => t) collideOps_laws ⟨[(true, ())]⟩ false () (by decide)
  cases hd

/-- `Dict()` starts empty and every source-mirrored dictionary operation (`setindex!`, `delete!`,
`pop!`, `get!`, `sizehint!`, `empty!`, `filter!`, `map!`, `getindex`, `get`, `haskey`, `length`,
`isempty` and `iterate`) agrees with the reference finite map `m`: keys remain pairwise
non-`isequal`, lookups, `haskey` and `length` match `m`, and iteration yields each pair of `m`
exactly once. -/
def DictOperationsAgree : Prop :=
  ∀ (K V W D : Type) [AnyValue W V] (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (tablesz : Nat → Nat) (maxValues : Nat) (cld : JInt .i64 → JInt .i64)
    (fillSlots : Nat → Nat → (Nat → Nat) → Nat → Nat)
    (unsetKey : Nat → (Nat → Option K) → Nat → (Nat → Option K))
    (unsetVal : Nat → (Nat → Option V) → Nat → (Nat → Option V))
    (valueConv : ValueConv W V)
    (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → TableszLaw tablesz → MaxValuesLaw eqKey maxValues → CldLaw cld →
    FillLaw fillSlots → UnsetLaw unsetKey → UnsetLaw unsetVal →
    DictRep hash eqKey h m →
    DictRep hash eqKey (dictEmpty K V) [] ∧
    Distinct eqKey m ∧ length h = m.length ∧ isempty h = m.isEmpty ∧
    (∀ (k : K) (w : W), ∃ h', setindexAny hash eqKey tablesz h w k = .ok h' ∧
      DictRep hash eqKey h' (rset eqKey m k (AnyValue.toAny w))) ∧
    (∀ (k : K), ∃ h', deleteKey hash eqKey unsetKey unsetVal h k = .ok h' ∧
      DictRep hash eqKey h' (rdel eqKey m k)) ∧
    (∀ (k : K) (default : D) (defaultV : V),
      (match rfind eqKey m k with
        | some e => ∃ h', popKey hash eqKey unsetKey unsetVal h k = .ok (e.2, h') ∧
            DictRep hash eqKey h' (rdel eqKey m k)
        | none => popKey hash eqKey unsetKey unsetVal h k = .error .keyError) ∧
      (match rfind eqKey m k with
        | some e => ∃ h', popDefault hash eqKey unsetKey unsetVal h k default = .ok (.inl e.2, h') ∧
            DictRep hash eqKey h' (rdel eqKey m k)
        | none => popDefault hash eqKey unsetKey unsetVal h k default = .ok (.inr default, h)) ∧
      (match rfind eqKey m k with
        | some e => getBang hash eqKey tablesz (fieldConv V) h k (fun t => .ok (defaultV, t)) =
            .ok (e.2, h)
        | none => ∃ h', getBang hash eqKey tablesz (fieldConv V) h k (fun t => .ok (defaultV, t)) =
            .ok (defaultV, h') ∧ DictRep hash eqKey h' (rset eqKey m k defaultV)) ∧
      getindex hash eqKey h k =
        (match rlookup eqKey m k with | some v => .ok v | none => .error .keyError) ∧
      JuliaLean.base.dict.get hash eqKey h k default =
        .ok (match rlookup eqKey m k with | some v => .inl v | none => .inr default) ∧
      haskey hash eqKey h k = .ok (rlookup eqKey m k).isSome) ∧
    (∀ (n : JInt .i64), ∃ h', sizehint hash tablesz maxValues (fun x => .ok (cld x)) h n false = .ok h' ∧
      DictRep hash eqKey h' m) ∧
    DictRep hash eqKey (emptyBang fillSlots unsetKey unsetVal h) [] ∧
    (∀ pred : K × V → Bool, ∃ h', filterBang unsetKey unsetVal pred h = .ok h' ∧
      DictRep hash eqKey h' (m.filter pred)) ∧
    (∀ (f : V → DictResult W) (g : V → V),
      (∀ v, (f v >>= convertValue valueConv) = .ok (g v)) →
      ∃ h', mapBang valueConv f ⟨h⟩ = .ok ⟨h'⟩ ∧
        DictRep hash eqKey h' (m.map (fun e => (e.1, g e.2)))) ∧
    (h.size < 2 ^ 63 - 1 → ∃ l,
      (iterateFirst h >>= fun x =>
        match x with
        | none => .ok []
        | some (pair, next) =>
          iterCollect h (h.size + 1) next >>= fun rest => .ok (pair :: rest)) =
        .ok l ∧ List.Perm l m)

theorem DictOperationsAgree_proven : DictOperationsAgree := by
  intro K V W D _ hash eqKey tablesz maxValues cld fillSlots unsetKey unsetVal valueConv h m
    hl htz _ _ hfill huk huv hr
  have hset := (DictSetindexLookup_proven K V K W D hash eqKey tablesz (typedKey eqKey) valueConv
    h m hl htz hr).2.1
  have hempty := DictEmptyContract_proven K V hash eqKey fillSlots unsetKey unsetVal h m hfill hr
  refine ⟨dictEmpty_rep hash eqKey, Distinct.perm hl (tlist_pairwise hr.1) hr.2,
    hempty.2.2.2.2, hempty.2.2.2.1, hset, fun k => hr.deleteKey hl huk huv hl.query k,
    fun k default defaultV => ?_, fun n => ?_, hempty.1, fun pred => hr.filterBang hl huk huv pred,
    fun f g hg => DictMapReduceSemantics_proven K V W hash eqKey valueConv f g h m hr hg,
    fun hsize => (DictIterationSemantics_proven K V hash eqKey h m hr hsize).2.1⟩
  · obtain ⟨hgi, hget, -, hhk, -⟩ := hr.lookups hl hl.query k default k (fun _ => .ok default)
    have hgb := (DictGetBangMutatingDefault_proven K V K V hash eqKey tablesz fillSlots unsetKey
      unsetVal (typedKey eqKey) (fieldConv V) h m hl htz hfill huk huv hr).1 (fun _ => .ok defaultV) k
    exact ⟨hr.popKey hl huk huv hl.query k, hr.popDefault hl huk huv hl.query k default,
      hgb, hgi, hget, hhk⟩
  · obtain ⟨h', h1, h2, -⟩ := sizehint_no_shrink htz maxValues cld hr n
    exact ⟨h', h1, h2⟩
/-- Dictionary iteration (`DictIterationSemantics`) and `Iterators.only` (`DictOnlyContract`). -/
def DictIterationOnlySemantics : Prop := DictIterationSemantics ∧ DictOnlyContract

theorem DictIterationOnlySemantics_proven : DictIterationOnlySemantics :=
  ⟨DictIterationSemantics_proven, DictOnlyContract_proven⟩

/-! ## Nothing to promise

Nothing to promise: Dict@87: the internal constructor `Dict{K,V}(slots, keys, vals, ndel, count, age, idxfloor, maxprobe, popcursor)` stores its arguments as the fields; every behaviour of the table built from them is stated for the operations that maintain the fields.
Nothing to promise: Iterators.only@1069: forwards to `Iterators._only(dict, first)` (`base/iterators.jl`), which owns the one-element check; `PersistentCollectionSemantics` states both the iteration and `persistentOnly` on `PersistentDict`.
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
| `eltype@1008`, `iterate@1063`, `length@1065`, `isempty@1066`, `empty@1067`, `Iterators.only@1069` | `PersistentCollectionSemantics` |
| `in@1010` | `PersistentPairMembershipSemantics` |
| `haskey@1017`, `getindex@1021`, `get@1027`, `KeyValue.get@1033`, `KeyValue.get@1047`, `get@1053` | `PersistentLookupSemantics`, `PersistentPathSafe` |
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

namespace round2

open JuliaLean.src.genericmemory_c (DictLayout runtimeAccessOps dictMemoryrefUnset dictUnsetEffects interpretSlots interpretSlotEffect boxedDictLayout)

open JuliaLean JuliaLean.base.dict JuliaLean.Registry JuliaLean.Proofs.base.dict

/-! ## Callee instances and approved second-round statements -/

/-! ## Callee instances -/

/-- `_tablesz(x::Int)` (`base/abstractdict.jl:879`, model `abstractdict.tableSize`): `x < 16 ? 16 :
one(Int) << top_set_bit(x - 1)` with `int.jl`'s `<` (`int.lt`), `-` (`int.sub`), `<<(::Int, ::Int)`
(`int.shl_Int`) and `top_set_bit` (`int.top_set_bit`). The `Dict` model passes sizes as `Nat`; a
size is the `Int` with that value and the result is read back as a `Nat`. -/
def jlTablesz (x : Nat) : Nat :=
  (JuliaLean.base.abstractdict.tableSize (I := JInt .i64)
    (fun a b => JuliaLean.base.int.lt a b) (fun n => JuliaLean.base.int.lit .i64 n)
    (JuliaLean.base.int.lit .i64 1) JuliaLean.base.int.sub JuliaLean.base.int.shl_Int
    JuliaLean.base.int.top_set_bit (JInt.wrap .i64 x)).val.toNat

/-- `cld(x, 2)` on `Int` (`base/div.jl:164`, model `div.cld`) with the `Int` `RoundUp` method
`div(x::T, y::T, ::typeof(RoundUp))` (`base/div.jl:471-474`, `div.divBitIntegerUpDown`). Division by
`2` never throws; the `Dict` model's `cld` interface is total, so the unreachable error branch
returns `x`. -/
def jlCld2 (x : JInt .i64) : JInt .i64 :=
  match JuliaLean.base.div.cld JuliaLean.base.div.divBitIntegerUpDown x
      (JuliaLean.base.int.lit .i64 2) with
  | .ok q => q
  | .error _ => x

/-- `max_values(T)` (`base/abstractset.jl:92-103`, model `abstractset.maxValuesDispatch`) for the
key type tag `T`, with `checked.jl`'s `add_with_overflow` on `Int`. -/
def jlMaxValues (T : JuliaLean.base.abstractset.JuliaType) : Nat :=
  (JuliaLean.base.abstractset.maxValuesDispatch JuliaLean.base.checked.addWithOverflowBits T).val.toNat


def memUnset {α : Type} (layout : DictLayout) (_size : Nat)
    (mem : Nat → Option α) (i : Nat) : Nat → Option α :=
  (Id.run ((JuliaLean.base.genericmemory.unsetindexMemoryInt (runtimeAccessOps layout) true () (JInt.wrap .i64 i)).run mem)).2

/-- C `memset(p, v, n)`: writes the byte `v` to the `n` bytes from address `p`. Slot byte `i` of a
`Memory{UInt8}` is at address `i`. -/
def cMemset (p v n : Nat) : StateM (Nat → Nat) Unit :=
  fun s => ((), fun j => if p ≤ j ∧ j < p + n then v else s j)

/-- `fill!(a::Memory{UInt8}, x::Integer)` (`base/genericmemory.jl:283-291`, model
`genericmemory.fillByteMemory`) of a memory of length `size` with slot bytes `slots`: `x isa UInt8`,
`unsafe_convert(Ptr{Cvoid}, a)` is the address of element `1`, `length(a) % UInt` is `size`, and
the GC-preserve calls do nothing to the contents. The `Dict` model's `fillSlots` interface. -/
def memFill (size b : Nat) (slots : Nat → Nat) : Nat → Nat :=
  (Id.run ((JuliaLean.base.genericmemory.fillByteMemory (m := StateM (Nat → Nat))
    (M := Nat) (P := Nat) (X := Nat) (U := Nat) (USize := Nat) (Token := Unit)
    (fun _ => Nat) (fun _ => True) (fun _ x => some x) (fun _ x => pure x)
    (fun _ => ()) (fun _ => pure ()) (fun _ => pure 1) cMemset (fun a => pure a)
    size b trivial).run slots)).2

/-- Several memories: memory `mem`, element `j`. -/
abbrev CopyHeap (α : Type) := Nat → Nat → Option α

/-- C `memmove` and the runtime `jl_genericmemory_copyto`: copy `n` elements of memory `sm` from
index `soff` onto memory `dm` from index `doff`. -/
def heapCopyRange {α : Type} (dm doff sm soff n : Nat) : StateM (CopyHeap α) Unit :=
  fun h => ((), fun mem j =>
    if mem = dm ∧ doff ≤ j ∧ j < doff + n then h sm (soff + (j - doff)) else h mem j)

/-- The copy runtime of `base/genericmemory.jl` on a `CopyHeap`: a reference is (memory, index), a
pointer is (memory, index), element sizes are `1`, and `isbitstype(T)` is `isBits`. -/
def memCopyOps {α : Type} (isBits : Bool) :
    JuliaLean.base.genericmemory.MemoryCopyOps (StateM (CopyHeap α)) Nat Nat
      (JInt .i64) (JInt .i64) (JInt .i64) (JInt .i64) (Nat × Nat) Unit where
  isZero n := n.val == 0
  toInt n := pure n
  byteCount _ n := pure n
  checkEnd ref _ := pure ref
  memoryrefDest mem i := pure ⟨mem, i.val.toNat⟩
  memoryrefSource mem i := pure ⟨mem, i.val.toNat⟩
  memoryrefoffset ref := JInt.wrap .i64 ref.ptr_or_offset
  isBitsType _ := isBits
  gcPreserveBegin _ := ()
  gcPreserveEnd _ := pure ()
  unsafeConvert ref := pure (ref.mem, ref.ptr_or_offset)
  memmove d s n := heapCopyRange d.1 d.2 s.1 s.2 n.val.toNat
  ccallCopy dm doff sm soff n := heapCopyRange dm doff sm soff n.val.toNat
  pointerDest mem i := pure (mem, i.val.toNat)
  pointerSource mem i := pure (mem, i.val.toNat)
  pointerLess a b := a.1 == b.1 && decide (a.2 < b.2)
  pointerGreater a b := a.1 == b.1 && decide (a.2 > b.2)
  sourceEnd s n := pure (s + n - JInt.lit .i64 1)
  forwardRange n := pure ((List.range n.val.toNat).map fun i : Nat => JInt.wrap .i64 ((i : Int) + 1))
  backwardRange n :=
    pure (((List.range n.val.toNat).reverse).map fun i : Nat => JInt.wrap .i64 ((i : Int) + 1))
  destIndex d i := pure (d + i - JInt.lit .i64 1)
  sourceIndex s i := pure (s + i - JInt.lit .i64 1)

/-- `copy(a::Memory{T})` (`base/genericmemory.jl:257-263`, model `genericmemory.copyMemory`) of a
memory of length `size` with contents `src` (memory `0`); `T(undef, n)` allocates memory `1`, with
no element assigned. The `Dict` model's `copyKeys`/`copyVals` interface. -/
def memCopy {α : Type} (isBits : Bool) (size : Nat) (src : Nat → Option α) : Nat → Option α :=
  let heap0 : CopyHeap α := fun mem j => if mem = 0 then src j else none
  let r := Id.run ((JuliaLean.base.genericmemory.copyMemory (T := α) (memCopyOps isBits)
    (fun _ => pure (JInt.wrap .i64 size)) (fun _ => pure 1) 0).run heap0)
  r.2 r.1

/-- `copy(d.slots)` of a `Memory{UInt8}` (`isbitstype(UInt8)`): the `Dict` model's `copySlots`
interface; slot bytes are always assigned. -/
def memCopySlots (size : Nat) (slots : Nat → Nat) : Nat → Nat :=
  fun j => (memCopy true size (fun i => some (slots i)) j).getD 0

/-- Tables of at most `2^50` slots. -/
def SmallTable {K V : Type} (h : DictState K V) : Prop := h.size ≤ 2 ^ 50

/-- At most `2^48` pairs inserted by one call. -/
def SmallBatch {α : Type} (xs : List α) : Prop := xs.length ≤ 2 ^ 48

/-- The `Julia` key type tag `max_values` dispatches on. -/
abbrev JType := JuliaLean.base.abstractset.JuliaType

/-- `count(Returns(true), t)` (`base/reduce.jl:1096-1098`, model `reduce.count_f` with
`_simple_count`): `sum(_bool(pred), itr; init = 0)` over the pairs `iterate(t)` visits, with
`add_sum(x::Real, y::Real) = x + y` (`base/reduce.jl:19`) of an `Int` and a `Bool` (`int.jl`'s `+`
after `Int(::Bool)`). The `ImmutableDict` model's `count` interface; summing never throws, and the
unreachable error branch returns `0`. -/
def immCount {K V : Type} (p : K × V → Bool) (d : ImmutableDict K V) : Nat :=
  match JuliaLean.base.reduce.count_f
      (JuliaLean.base.reduce._simple_count (fun _ => .hasEltype)
        (JuliaLean.base.reduce.valueReducer
          (JuliaLean.base.reduce.add_sum_small id (JuliaLean.base.int.ofBool .i64)
            JuliaLean.base.int.add)
          (JuliaLean.base.reduce.reduce_first_add_sum
            (JuliaLean.base.reduce.reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64)))
          (JuliaLean.base.reduce.reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0)
            (JInt .i64))))
      p (.values (immutableCollect d)) (.value (JuliaLean.base.int.lit .i64 0)) with
  | .ok n => n.val.toNat
  | .error _ => 0

/-! ## `PersistentDict` on the `HAMT` model -/

/-- A `HAMT{K,V}` value: the heap holding its nodes and vectors with the root node handle, or the
`HAMT` error that a failed operation raised. -/
abbrev PTrie (K V : Type) :=
  Except JuliaLean.base.hamt.HamtError (JuliaLean.base.hamt.HamtHeap K V × Nat)


/-- The exception a `HAMT` error raises: `error("Perfect hash collision")` and the `@assert` are
`ErrorException`s (`thrownDict`), a failed `::Leaf` assertion is a `TypeError`, and an out-of-bounds
or undefined read (which the model reports only for a malformed heap) is `undefRef`. -/
def hamtThrow : JuliaLean.base.hamt.HamtError → DictError
  | .perfectHashCollision => .thrownDict
  | .assertion => .thrownDict
  | .typeError => .typeError
  | .bounds => .undefRef
  | .undefinedReference => .undefRef

/-- Run a `HAMT` action on the root of `t`. -/
def runTrie {K V α : Type} (t : PTrie K V) (act : Nat → JuliaLean.base.hamt.HamtM K V α) :
    Except JuliaLean.base.hamt.HamtError (α × JuliaLean.base.hamt.HamtHeap K V) :=
  match t with
  | .error e => .error e
  | .ok (heap, root) =>
    match JuliaLean.base.hamt.runHamt (act root) heap with
    | (.ok a, heap') => .ok (a, heap')
    | (.error e, _) => .error e

def runPartialTrie {K V α : Type} (t : PTrie K V)
    (act : Nat → JuliaLean.base.hamt.PartialHamtM K V α) :
    Option (Except JuliaLean.base.hamt.HamtError (α × JuliaLean.base.hamt.HamtHeap K V)) :=
  match t with
  | .error error => some (.error error)
  | .ok (heap, root) =>
    (JuliaLean.base.hamt.runPartialHamt (act root) heap).map fun
      | (.ok value, heap') => .ok (value, heap')
      | (.error error, _) => .error error

/-- Run a `HAMT` action that mutates the node `trie` of the tree `top` (`HAMT.insert!`,
`deleteat!(trie.data, i)`, `HAMT.unset!`) and return `top` in the updated heap: `top` carries the
latest heap of the tree, `trie` the node. -/
def runAt {K V α : Type} (top trie : PTrie K V) (act : Nat → JuliaLean.base.hamt.HamtM K V α) :
    Except JuliaLean.base.hamt.HamtError (α × PTrie K V) :=
  match top, trie with
  | .ok (heap, topRoot), .ok (_, trieRoot) =>
    match JuliaLean.base.hamt.runHamt (act trieRoot) heap with
    | (.ok a, heap') => .ok (a, .ok (heap', topRoot))
    | (.error e, _) => .error e
  | .error e, _ => .error e
  | _, .error e => .error e

def runPartialAt {K V α : Type} (top trie : PTrie K V)
    (act : Nat → JuliaLean.base.hamt.PartialHamtM K V α) :
    Option (Except JuliaLean.base.hamt.HamtError (α × PTrie K V)) :=
  match top, trie with
  | .ok (heap, topRoot), .ok (_, trieRoot) =>
      match JuliaLean.base.hamt.runPartialHamt (act trieRoot) heap with
      | none => none
      | some (.ok a, heap') => some (.ok (a, .ok (heap', topRoot)))
      | some (.error error, _) => some (.error error)
  | .error error, _ => some (.error error)
  | _, .error error => some (.error error)

/-- `deleteat!(v::Vector, i::Integer)` (`base/array.jl:1894-1898`: remove the item at index `i`)
on a heap vector of the `HAMT` model. `hamt.lean`'s `heapVectorOps` give the heap vectors'
`insert!`, `copy` and `setindex!` the same way and have no deletion; `array.lean`'s `deleteat!`
works on its own `Vector` representation, not on these heap lists. -/
def heapVectorDeleteAt {K V : Type} (handle i : Nat) : JuliaLean.base.hamt.HamtM K V Unit := do
  let heap ← get
  match heap.vectors[handle]? with
  | none => throw JuliaLean.base.hamt.HamtError.bounds
  | some slots =>
    if i = 0 || i > slots.length then throw JuliaLean.base.hamt.HamtError.bounds
    set { heap with vectors := heap.vectors.set handle (slots.eraseIdx (i - 1)) }

/-- The `HAMT` operations of `base/hamt.jl` a `PersistentDict{K,V}` call makes with `key::K` and
`val::V`, on the `JuliaLean.base.hamt` model: `HAMT.HAMT{K,V}()`, `HAMT.HAMT{K,V}(key => val)`,
`HAMT.HashState(key)`, `HAMT.path`, `HAMT.insert!`, `deleteat!(trie.data, i)`, `HAMT.unset!`,
`HAMT.islevel_empty`, the leaf read `trie.data[i]::Leaf`, `HAMT.iterate`, `length` and `isempty`.
Keys are compared with `===` (`egal`), as `HAMT.path` does. A failed operation yields the error
trie (or, for `insert!` and the one-pair constructor, the thrown exception); reads of an error trie
find nothing. -/
def hamtOps {K V : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K) :
    PersistentOps K V K V (PTrie K V) (JuliaLean.base.hamt.HashState K)
      (JuliaLean.base.hamt.IterState K V) where
  empty _ :=
    match JuliaLean.base.hamt.runHamt
        (JuliaLean.base.hamt.HAMT.emptyConstructor JuliaLean.base.hamt.heapVectorOps)
        JuliaLean.base.hamt.HamtHeap.empty with
    | (.ok root, heap) => .ok (heap, root)
    | (.error e, _) => .error e
  singleton p :=
    match JuliaLean.base.hamt.runHamt
        (JuliaLean.base.hamt.HAMT.typedPairConstructor JuliaLean.base.hamt.heapVectorOps
          runtime p)
        JuliaLean.base.hamt.HamtHeap.empty with
    | (.ok root, heap) => .ok (.ok (heap, root))
    | (.error e, _) => .error (hamtThrow e)
  hashState k := JuliaLean.base.hamt.HashState.fromKey runtime k
  path t hs copy :=
    match runTrie t (fun root => JuliaLean.base.hamt.path JuliaLean.base.hamt.heapVectorOps egal
        runtime root hs copy) with
    | .ok (pr, heap) =>
      ⟨pr.found, pr.present, .ok (heap, pr.trie), pr.index, pr.bi.x, .ok (heap, pr.top), pr.hash⟩
    | .error e => ⟨false, false, .error e, 0, 0, .error e, hs⟩
  insert top trie found present index bi hs value :=
    (runPartialAt top trie (fun node => JuliaLean.base.hamt.insert! JuliaLean.base.hamt.heapVectorOps
      runtime found present node index ⟨bi⟩ hs value)).map fun
      | .ok (_, top') => .ok top'
      | .error error => .error (hamtThrow error)
  deleteAt top trie index :=
    match runAt top trie (fun node => do
        let data ← JuliaLean.base.hamt.nodeData node
        heapVectorDeleteAt data index) with
    | .ok (_, top') => top'
    | .error e => .error e
  unset top trie bi :=
    match runAt top trie (fun node => JuliaLean.base.hamt.unset! node ⟨bi⟩) with
    | .ok (_, top') => top'
    | .error e => .error e
  isLevelEmpty t :=
    match runTrie t JuliaLean.base.hamt.islevel_empty with
    | .ok (b, _) => b
    | .error _ => true
  leafValue t i :=
    match runTrie t (fun root => do
        let node ← JuliaLean.base.hamt.readNode root
        match ← JuliaLean.base.hamt.heapVectorOps.get node.data i with
        | .leaf leaf => pure (some leaf.val)
        | .trie _ => pure none) with
    | .ok (v, _) => v
    | .error _ => none
  iterate t state :=
    match runTrie t (fun root =>
        JuliaLean.base.hamt.iterate JuliaLean.base.hamt.heapVectorOps root state) with
    | .ok (r, _) => r
    | .error _ => none
  length t :=
    (runPartialTrie t (JuliaLean.base.hamt.lengthHAMT JuliaLean.base.hamt.heapVectorOps)).map fun
      | .ok (n, _) => .ok n
      | .error error => .error (hamtThrow error)
  isEmpty t :=
    (runPartialTrie t (JuliaLean.base.hamt.isemptyHAMT JuliaLean.base.hamt.heapVectorOps)).map fun
      | .ok (b, _) => .ok b
      | .error error => .error (hamtThrow error)

/-- The same operations for a call whose key and value arguments have types `Q` and `W`:
`HAMT.HAMT{K,V}(kv::Pair) = HAMT.HAMT{K,V}(convert(Pair{K,V}, kv))` (`base/hamt.jl:82`) converts the
pair before building the one-pair trie; the other operations convert the key before hashing it and
the value before storing it. -/
def hamtOpsConv {K V Q W : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) :
    PersistentOps K V Q W (PTrie K V) (DictResult (JuliaLean.base.hamt.HashState K))
      (JuliaLean.base.hamt.IterState K V) where
  empty u := (hamtOps (V := V) egal runtime).empty u
  singleton p := do
    let k ← keyConv.convert p.1
    let v ← valueConv.convert p.2
    (hamtOps egal runtime).singleton (k, v)
  hashState q := (keyConv.convert q).map (JuliaLean.base.hamt.HashState.fromKey runtime)
  path t hs copy :=
    match hs with
    | .ok h =>
      let p := (hamtOps (V := V) egal runtime).path t h copy
      ⟨p.found, p.present, p.trie, p.index, p.bitmapIndex, p.top, .ok p.state⟩
    | .error e => ⟨false, false, t, 0, 0, t, .error e⟩
  insert top trie found present index bi hs w :=
    match hs with
    | .error error => some (.error error)
    | .ok h =>
        match valueConv.convert w with
        | .error error => some (.error error)
        | .ok v => (hamtOps egal runtime).insert top trie found present index bi h v
  deleteAt := (hamtOps (V := V) egal runtime).deleteAt
  unset := (hamtOps (V := V) egal runtime).unset
  isLevelEmpty := (hamtOps (V := V) egal runtime).isLevelEmpty
  leafValue := (hamtOps (V := V) egal runtime).leafValue
  iterate := (hamtOps (V := V) egal runtime).iterate
  length := (hamtOps (V := V) egal runtime).length
  isEmpty := (hamtOps (V := V) egal runtime).isEmpty

/-- The `PersistentDict` values the API builds and the pairs each holds: the empty dictionary, a
one-pair dictionary, and the results of the typed `KeyValue.set` insertion (a later `===` key
replaces an earlier one) and deletion, which every constructor and update reaches
(`base/dict.jl:903-933,969-1006,1059-1061`). -/
inductive PRep {K V H HS S : Type} (ops : PersistentOps K V K V H HS S) (egal : K → K → Bool) :
    PersistentDict K V H → List (K × V) → Prop
  | empty : PRep ops egal (persistentEmpty ops) []
  | singleton {k : K} {v : V} {d : PersistentDict K V H} :
      persistentSingleton ops k v = .ok d → PRep ops egal d [(k, v)]
  | set {d d' : PersistentDict K V H} {m : List (K × V)} {k : K} {v : V} :
      PRep ops egal d m → persistentSetTyped ops d k v = some (.ok d') →
      PRep ops egal d' (rset egal m k v)
  | delete {d : PersistentDict K V H} {m : List (K × V)} {k : K} :
      PRep ops egal d m → PRep ops egal (persistentDelete ops d k) (rdel egal m k)

/-- Keys that are not `===` have different `objectid`s. `HAMT.insert!` throws
`"Perfect hash collision"` exactly when a new key meets a stored key that is not `===` to it but has
the same `HashState` hash, which `hash(::UInt64, ::UInt)` keeps injective in the `objectid`. -/
def ObjectidDistinct {K : Type} (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (egal : K → K → Bool) (ks : List K) : Prop :=
  ∀ a ∈ ks, ∀ b ∈ ks, egal a b = false → runtime.objectid a ≠ runtime.objectid b

/-- `delete!(h, key)` removes every pair whose key is `isequal` to `key` and keeps the others
(`delete!` docstring, `base/dict.jl:658-679`; `_delete!`, `base/dict.jl:631-656`). -/
def DictDeleteLookup : Prop :=
  ∀ (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (rtK : DictLayout)
    (rtV : DictLayout) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → 
    DictRep hash eqKey h m → h.size < 2 ^ 63 → ∀ q : Q,
    ∃ h', deleteKey hashQ matchQ (memUnset rtK) (memUnset rtV) h q = .ok h' ∧
      DictRep hash eqKey h' (rdel matchQ m q)
/-- `pop!(h, key)` returns the stored value and removes the key, or throws `KeyError`;
`pop!(h, key, default)` returns `default` and leaves the table alone when the key is absent
(`pop!` docstring, `base/dict.jl:591-612`; `_pop!`, `base/dict.jl:580-584`). -/
def DictPopKeyContract : Prop :=
  ∀ (K V Q D : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (rtK : DictLayout)
    (rtV : DictLayout) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → 
    DictRep hash eqKey h m → h.size < 2 ^ 63 → ∀ (q : Q) (default : D),
    (match rfind matchQ m q with
      | some e => ∃ h', popKey hashQ matchQ (memUnset rtK) (memUnset rtV) h q = .ok (e.2, h') ∧
          DictRep hash eqKey h' (rdel matchQ m q)
      | none => popKey hashQ matchQ (memUnset rtK) (memUnset rtV) h q = .error .keyError) ∧
    (match rfind matchQ m q with
      | some e => ∃ h', popDefault hashQ matchQ (memUnset rtK) (memUnset rtV) h q default =
            .ok (.inl e.2, h') ∧ DictRep hash eqKey h' (rdel matchQ m q)
      | none => popDefault hashQ matchQ (memUnset rtK) (memUnset rtV) h q default =
          .ok (.inr default, h))
/-- `pop!(h)` throws `ArgumentError` on an empty dictionary and otherwise removes and returns one
stored pair (`pop!` docstring, `base/array.jl`; `base/dict.jl:620-629`). -/
def DictPopAnyContract : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (rtK : DictLayout)
    (rtV : DictLayout) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → DictRep hash eqKey h m → h.size < 2 ^ 63 →
    match m with
    | [] => popAny (memUnset rtK) (memUnset rtV) h = .error .argumentError
    | _ :: _ => ∃ e h', popAny (memUnset rtK) (memUnset rtV) h = .ok (e, h') ∧ e ∈ m ∧
        DictRep hash eqKey h' (rdel eqKey m e.1)
/-- `filter!(pred, h)` keeps exactly the pairs for which `pred` is true (`filter!` docstring,
`base/array.jl`; `base/dict.jl:725-733`). -/
def DictFilterContract : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (rtK : DictLayout)
    (rtV : DictLayout) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → DictRep hash eqKey h m → h.size < 2 ^ 63 →
    ∀ pred : K × V → Bool, ∃ h', filterBang (memUnset rtK) (memUnset rtV) pred h = .ok h' ∧
      DictRep hash eqKey h' (m.filter pred)
/-- `hashindex(key, sz)` (`base/dict.jl:125-133`, "computes optimal position in the hash table")
converts any `Integer` `sz` to `Int` (propagating `InexactError`); for every table size `sz ≥ 1`
it returns the short hash of `key` and the index `((hash(key) % Int) & (sz-1)) + 1` of `int.jl`'s
`Int` arithmetic, which lies in `1:sz` and is `hash(key) mod sz + 1` for a power-of-two `sz`. -/
def DictHashindexSemantics : Prop :=
  ∀ (K I : Type) [DictInteger I] (hash : K → JInt .u64) (key : K) (sz : I),
    (∀ szInt : JInt .i64, DictInteger.toInt sz = .ok szInt → 1 ≤ szInt.val →
      ∃ idx : Nat, hashindex hash key sz = .ok (idx, shorthash7 (hash key)) ∧
        (idx : Int) = (JuliaLean.base.int.add
          (JuliaLean.base.int.and_int (JuliaLean.base.int.remT .i64 (hash key))
            (JuliaLean.base.int.sub szInt (JuliaLean.base.int.lit .i64 1)))
          (JuliaLean.base.int.lit .i64 1)).val ∧
        1 ≤ idx ∧ (idx : Int) ≤ szInt.val ∧
        ∀ p : Nat, szInt.val = (2 ^ p : Nat) → idx = (hash key).val.toNat % 2 ^ p + 1) ∧
    (∀ err, DictInteger.toInt sz = .error err → hashindex hash key sz = .error err)
/-- `get(f, d, key)` (`get` docstring, `base/dict.jl:512-527`: return the stored value, or `f()` if
no mapping for the key is present): for a present key it returns the stored value whatever `f`
does, so an `f` that throws is not run; for an absent key it returns `f()` and propagates its
exception. -/
def DictGetCallableDefault : Prop :=
  ∀ (K V Q DF : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → QueryLaws hash eqKey hashQ matchQ → DictRep hash eqKey h m →
    ∀ q : Q,
      (∀ v : V, rlookup matchQ m q = some v →
        ∀ f : Unit → DictResult DF, getF hashQ matchQ h q f = .ok (.inl v)) ∧
      (∀ v : V, rlookup matchQ m q = some v →
        ∀ err : DictError, getF hashQ matchQ h q (fun _ => (.error err : DictResult DF)) =
          .ok (.inl v)) ∧
      (rlookup matchQ m q = none →
        ∀ f : Unit → DictResult DF, getF hashQ matchQ h q f = .inr <$> f ())
/-- `Dict{K,V}(p::Pair)` holds the converted pair or throws its conversion error
(`base/dict.jl:99`). -/
def DictSinglePairConstructorSemantics : Prop :=
  ∀ (K V Q W : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pair : Q × W),
    KeyLaws hash eqKey →
    match refStep eqKey keyConv valueConv [] pair with
    | .ok m => ∃ h, dictFromPair hash eqKey jlTablesz keyConv valueConv pair = .ok h ∧
        DictRep hash eqKey h m
    | .error e => dictFromPair hash eqKey jlTablesz keyConv valueConv pair = .error e
/-- `length(t) = count(Returns(true), t)` and `isempty(t)` agree with iteration, which visits every
pair from the most recently added, duplicates included; `empty(d, K, V)` has no pairs
(`ImmutableDict` docstring, `base/dict.jl:785-799`; `base/dict.jl:860-866`). -/
def ImmutableDictCollectionSemantics : Prop :=
  ∀ (K V : Type) (d : ImmutableDict K V), d.length < 2 ^ 63 →
    immutableIterate (immutableEmpty K V) = none ∧
    (∀ (p : K × V) (rest : ImmutableDict K V),
      immutableIterate (p :: rest) = some (p, rest) ∧
      immutableIterate d [] = none ∧
      immutableIterate d (p :: rest) = some (p, rest)) ∧
    immutableLength (fun p x => .ok (immCount p x)) d = .ok (immutableCollect d).length ∧
    immutableIsEmpty d = (immutableIterate d).isNone ∧
    immutableEmptyLike K V d = immutableEmpty K V ∧
    immutableCollect (immutableEmptyLike K V d) = []
/-- `setindex(d, value, key)` and `ImmutableDict(d, key => value)` (`setindex` docstring,
`base/dict.jl:868-885`; `ImmutableDict` docstring, `base/dict.jl:785-808`) return a dictionary in
which the converted pair `convert(K, key) => convert(V, value)` shadows `d`: a query `isequal` to the
stored key finds `value`, any other query finds what it found in `d`; a failing conversion throws.
In particular `d'[key] == value` whenever `convert(K, key)` is `isequal` to `key`. -/
def ImmutableDictSetindexShadows : Prop :=
  ∀ (K V Q W R : Type) (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (eqKey : K → R → Bool) (d : ImmutableDict K V) (value : W) (key : Q),
    match newPair keyConv valueConv (key, value) with
    | .error e => setindexImmutable keyConv valueConv d value key = .error e ∧
        immutableExtend keyConv valueConv d (key, value) = .error e
    | .ok (k, v) => ∃ d', setindexImmutable keyConv valueConv d value key = .ok d' ∧
        immutableExtend keyConv valueConv d (key, value) = .ok d' ∧
        ∀ r : R, immutableGetindex eqKey d' r =
          (if eqKey k r then .ok v else immutableGetindex eqKey d r)
/-- After `d2 = setindex(d, value, key)` or `ImmutableDict(d, key => value)` returns, `d2[key]` is
the stored value: the `setindex` docstring (`base/dict.jl:868-885`) promises "the most recent value
of the key `key` set to `value`" for every `key`, and `ImmutableDict` lookups return the most recent
value (`base/dict.jl:785-797`). `Dict`'s `setindex!` guarantees the same by throwing `KeyTypeError`
when `convert(K, key)` is not `isequal` to `key` (`base/dict.jl:347-357`); `ImmutableDict` makes no
such check. -/
def ImmutableDictSetGet : Prop :=
  ∀ (K V Q W : Type) (keyConv : ValueConv Q K) (valueConv : ValueConv W V)
    (eqKey : K → Q → Bool) (d d' : ImmutableDict K V) (value : W) (key : Q) (v : V),
    convertValue valueConv value = .ok v →
    (setindexImmutable keyConv valueConv d value key = .ok d' ∨
      immutableExtend keyConv valueConv d (key, value) = .ok d') →
    immutableGetindex eqKey d' key = .ok v
/-- `KeyValue.get`, `haskey`, `getindex`, `get(d, key, default)`, `KeyValue.get(default, d, key)`
and `get(default, d, key)` agree with the pairs a `PersistentDict` holds: a key `===` to a stored key
finds its value, any other key is absent (`KeyError` or the default) (`base/dict.jl:1017-1057`). -/
def PersistentLookupSemantics : Prop :=
  ∀ (K V D : Type) (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K),
    KeyLaws runtime.objectid egal →
    ∀ (d : PersistentDict K V (PTrie K V)) (m : List (K × V)),
    PRep (hamtOps egal runtime) egal d m →
    ∀ (key : K) (default : D) (fallback : Unit → DictResult D),
    persistentKeyGet (hamtOps egal runtime) d key = rlookup egal m key ∧
    persistentGetindex (hamtOps egal runtime) d key =
      (match rlookup egal m key with | some v => .ok v | none => .error .keyError) ∧
    persistentHasKey (hamtOps egal runtime) d key = (rlookup egal m key).isSome ∧
    persistentGet (hamtOps egal runtime) d key default =
      (match rlookup egal m key with | some v => .inl v | none => .inr default) ∧
    persistentGetDefault (hamtOps egal runtime) d key fallback =
      (match rlookup egal m key with | some v => .ok (.inl v) | none => .inr <$> fallback ()) ∧
    persistentGetTypedDefault (hamtOps egal runtime) d key fallback =
      (match rlookup egal m key with | some v => .ok (.inl v) | none => .inr <$> fallback ())
/-- `KeyValue.get` reads the leaf `trie.data[i]` (`@inbounds`, `base/dict.jl:1033-1045`) only at the
end of a path `HAMT.path` walks without an out-of-bounds or undefined read; when the path reports
the key found and present, that slot holds a leaf whose key is `===` to the query and whose value
is the stored value. -/
def PersistentPathSafe : Prop :=
  ∀ (K V : Type) (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K),
    KeyLaws runtime.objectid egal →
    ∀ (d : PersistentDict K V (PTrie K V)) (m : List (K × V)),
    PRep (hamtOps egal runtime) egal d m → ∀ key : K,
    ∃ (pr : JuliaLean.base.hamt.PathResult K V) (heap : JuliaLean.base.hamt.HamtHeap K V),
      runTrie d.trie (fun root => JuliaLean.base.hamt.path JuliaLean.base.hamt.heapVectorOps egal
        (runtime) root
        (JuliaLean.base.hamt.HashState.fromKey (runtime) key)
        false) = .ok (pr, heap) ∧
      ((pr.found && pr.present) = true →
        ∃ leaf : JuliaLean.base.hamt.Leaf K V,
          runTrie (.ok (heap, pr.trie)) (fun t => do
            let node ← JuliaLean.base.hamt.readNode t
            JuliaLean.base.hamt.heapVectorOps.get node.data pr.index) = .ok (.leaf leaf, heap) ∧
          egal leaf.key key = true ∧ rlookup egal m key = some leaf.val)
/-- `KeyValue.set(d, key::K, val::V)` is annotated `@assume_effects :nothrow`
(`base/dict.jl:911-912`): it returns for every key and value. -/
def PersistentSetNothrow : Prop :=
  ∀ (K V : Type) (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K),
    KeyLaws runtime.objectid egal →
    ∀ (d : PersistentDict K V (PTrie K V)) (m : List (K × V)),
    PRep (hamtOps egal runtime) egal d m → ∀ (k : K) (v : V),
    ∃ d', persistentSetTyped (hamtOps egal runtime) d k v = some (.ok d')
/-- `(key => val) in d` is `false` for an absent key and otherwise `valcmp(val, stored)`
(`base/dict.jl:1010-1015`). -/
def PersistentPairMembershipSemantics : Prop :=
  ∀ (K V R : Type) (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K),
    KeyLaws runtime.objectid egal →
    ∀ (d : PersistentDict K V (PTrie K V)) (m : List (K × V)),
    PRep (hamtOps egal runtime) egal d m →
    ∀ (pair : K × V) (valcmp : V → V → DictResult R),
    persistentIn (hamtOps egal runtime) valcmp d pair =
      (match rlookup egal m pair.1 with
        | none => .ok (.inl false)
        | some stored => .inr <$> valcmp pair.2 stored)
/-- Iteration (`HAMT.iterate`) visits every stored pair once; `length` and `isempty` count them;
`empty(d, K, V)` has no pairs; `Iterators.only(d)` returns the only pair of a one-pair dictionary
and throws `ArgumentError` otherwise (`base/dict.jl:1063-1069`). -/
def PersistentCollectionSemantics : Prop :=
  ∀ (K V : Type) (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K),
    KeyLaws runtime.objectid egal →
    ∀ (d : PersistentDict K V (PTrie K V)) (m : List (K × V)),
    PRep (hamtOps egal runtime) egal d m →
    List.Perm (persistentCollectFuel (hamtOps egal runtime) d (m.length + 1) none) m ∧
    persistentLength (hamtOps egal runtime) d =
      some (.ok (JInt.lit .i64 (Int.ofNat m.length))) ∧
    persistentIsEmpty (hamtOps egal runtime) d = some (.ok m.isEmpty) ∧
    (∀ q : K, persistentKeyGet (hamtOps egal runtime)
      (persistentEmptyLike (hamtOps egal runtime) d) q = none) ∧
    persistentLength (hamtOps egal runtime) (persistentEmptyLike (hamtOps egal runtime) d) =
      some (.ok (JInt.lit .i64 0)) ∧
    persistentOnly (hamtOps egal runtime) d = some
      (if (JInt.lit .i64 (Int.ofNat m.length)).val = 1 then
        match (persistentCollectFuel (hamtOps egal runtime) d (m.length + 1) none).head? with
        | some e => .ok e
        | none => .error (.inr (.argumentError "PersistentDict must be non-empty"))
      else .error (.inr (.argumentError "Collection must contain exactly 1 element")))

open JuliaLean.C

/-! ## 1. `dictscov-dict-l99`: `DictSinglePairConstructorSemantics` -/

theorem jlTablesz_4 : jlTablesz 4 = 16 := by decide

theorem rehash_empty_4 {K V : Type} (hash : K → JInt .u64) (tz : Nat → Nat) (htz : tz 4 = 16) :
    rehash hash tz (dictEmpty K V) 4 =
      .ok ⟨16, fun _ => 0, fun _ => none, fun _ => none, 0, 0,
        bumpAge (dictEmpty K V).age, 1, 0, 1⟩ := by
  unfold rehash
  rw [htz]
  rfl

theorem htKeyindex2_empty {K V : Type} (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (tz : Nat → Nat) (htz : tz 4 = 16) (key : K) :
    htKeyindex2 hash eqKey tz (dictEmpty K V) key =
      .ok (-(home hash 16 key : Int), shorthash7 (hash key),
        ⟨16, fun _ => 0, fun _ => none, fun _ => none, 0, 0,
          bumpAge (dictEmpty K V).age, 1, 0, 1⟩) := by
  unfold htKeyindex2 htKeyindex2Loop
  change (do
    let h ← rehash hash tz (dictEmpty K V) 4
    let (index, shortHash) ← hashindex hash key (JInt.lit .i64 (Int.ofNat h.size))
    Except.ok (-(index : Int), shortHash, h)) = _
  rw [rehash_empty_4 hash tz htz]
  rfl

theorem setindexAt_eq_of_size16_empty {K V : Type} (hash : K → JInt .u64)
    (tz : Nat → Nat) (t : DictState K V) (hs : t.size = 16) (hc : t.count = 0) (hn : t.ndel = 0)
    (v : V) (k : K) (j sh : Nat) :
    setindexAt hash tz t v k j sh = .ok ((), storeAt t v k j sh) := by
  rw [setindexAt_eq]
  have h1 : (storeAt t v k j sh).count = 1 := by show t.count + 1 = 1; rw [hc]
  have h2 : (storeAt t v k j sh).ndel = 0 := by show t.ndel - _ = 0; rw [hn, Nat.zero_sub]
  have h3 : (storeAt t v k j sh).size = 16 := hs
  rw [h1, h2, h3]
  exact ite_eq_right (by decide)

theorem setindexTyped_empty_eq {K V W : Type} (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (tz1 tz2 : Nat → Nat) (h1 : tz1 4 = 16) (h2 : tz2 4 = 16)
    (valueConv : ValueConv W V) (w : W) (key : K) :
    setindexTyped hash eqKey tz1 valueConv (dictEmpty K V) w key =
      setindexTyped hash eqKey tz2 valueConv (dictEmpty K V) w key := by
  rw [setindexTyped_eq, setindexTyped_eq]
  cases convertValue valueConv w with
  | error e => rw [except_error_bind, except_error_bind]
  | ok v =>
    rw [except_ok_bind, except_ok_bind,
      htKeyindex2_empty hash eqKey tz1 h1 key, htKeyindex2_empty hash eqKey tz2 h2 key,
      except_ok_bind, except_ok_bind]
    unfold storeBody
    have hpos : ¬ (-(home hash 16 key : Int) > 0) := by
      have := (home_range ⟨4, by decide, rfl⟩ hash key).1
      omega
    rw [ite_eq_right hpos, ite_eq_right hpos,
      setindexAt_eq_of_size16_empty hash tz1 _ rfl rfl rfl,
      setindexAt_eq_of_size16_empty hash tz2 _ rfl rfl rfl]

theorem dictFromPair_eq_tableszSpec {K V Q W : Type} (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (keyConv : KeyConv Q K) (valueConv : ValueConv W V) (pair : Q × W) :
    dictFromPair hash eqKey jlTablesz keyConv valueConv pair =
      dictFromPair hash eqKey tableszSpec keyConv valueConv pair := by
  unfold dictFromPair
  rw [setindexConv_eq, setindexConv_eq]
  cases convKey keyConv pair.1 with
  | error e => rw [except_error_bind, except_error_bind]
  | ok k =>
    rw [except_ok_bind, except_ok_bind]
    exact setindexTyped_empty_eq hash eqKey jlTablesz tableszSpec jlTablesz_4 rfl valueConv pair.2 k

theorem DictSinglePairConstructorSemantics_proven : DictSinglePairConstructorSemantics := by
  intro K V Q W hash eqKey keyConv valueConv pair hl
  rw [dictFromPair_eq_tableszSpec]
  exact JuliaLean.Proofs.base.dict.DictSinglePairConstructorSemantics_proven K V Q W hash eqKey
    tableszSpec keyConv valueConv pair hl (fun _ => rfl)

/-! ## 2. `dictscov-dict-l128`: `DictHashindexSemantics` -/

private theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2)
  omega

private theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  unfold wrapInt
  have hp : (2 : Int) ^ t.bits = ((2 ^ t.bits : Nat) : Int) := by simp
  rw [hp]
  have hm : (a + (2 : Int) ^ (t.bits - 1)) % ((2 ^ t.bits : Nat) : Int) =
      (b + (2 : Int) ^ (t.bits - 1)) % ((2 ^ t.bits : Nat) : Int) := by
    rw [Int.add_emod a, h, ← Int.add_emod]
  rw [hm, h]

private theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  unfold wrapInt
  have hp : (2 : Int) ^ t.bits = ((2 ^ t.bits : Nat) : Int) := by simp
  rw [hp]
  split
  · rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod, Int.add_sub_cancel]
  · exact Int.emod_emod z _

private theorem fromJInt_toNat {t : IntTy} (x : JInt t) :
    ((fromJInt x).toNat : Int) = x.val % ((2 ^ t.bits : Nat) : Int) := by
  simp only [fromJInt, BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := two_pow_pos_int t.bits; omega))

private theorem fromJInt_toNat_eq {t : IntTy} (x : JInt t) :
    (fromJInt x).toNat = (x.val % ((2 ^ t.bits : Nat) : Int)).toNat := by
  simp only [fromJInt, BitVec.toNat_ofInt]

private theorem toJInt_val (t : IntTy) (b : BitVec t.bits) :
    (toJInt t b).val = wrapInt t (if t.signed then b.toInt else (b.toNat : Int)) := rfl

private theorem toJInt_ofInt_val (t : IntTy) (z : Int) :
    (toJInt t (BitVec.ofInt t.bits z)).val = wrapInt t z := by
  rw [toJInt_val]
  apply wrapInt_congr
  split
  · rw [BitVec.toInt_ofInt]
    exact Int.bmod_emod
  · rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have := two_pow_pos_int t.bits; omega)), Int.emod_emod]

private theorem toJInt_congr {t : IntTy} (b : BitVec t.bits) (z : Int)
    (h : (b.toNat : Int) = z % ((2 ^ t.bits : Nat) : Int)) : (toJInt t b).val = wrapInt t z := by
  have hb : b = BitVec.ofInt t.bits z := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    omega
  rw [hb, toJInt_ofInt_val]

private theorem add_int_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.add_int x y).val = wrapInt t (x.val + y.val) := by
  simp only [JuliaLean.base.int.add_int, jlAddInt, fromJInt]
  rw [← BitVec.ofInt_add, toJInt_ofInt_val]

private theorem sub_int_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.sub_int x y).val = wrapInt t (x.val - y.val) := by
  simp only [JuliaLean.base.int.sub_int, jlSubInt, fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, toJInt_ofInt_val,
    Int.sub_eq_add_neg]

private theorem and_int_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.and_int x y).val =
      wrapInt t (Nat.land (fromJInt x).toNat (fromJInt y).toNat : Int) := by
  unfold JuliaLean.base.int.and_int
  apply toJInt_congr
  rw [jlAndInt, BitVec.toNat_and]
  have hlt : Nat.land (fromJInt x).toNat (fromJInt y).toNat < 2 ^ t.bits :=
    Nat.lt_of_le_of_lt Nat.and_le_left (fromJInt x).isLt
  have hmod : (Nat.land (fromJInt x).toNat (fromJInt y).toNat : Int) % ((2 ^ t.bits : Nat) : Int) =
      (Nat.land (fromJInt x).toNat (fromJInt y).toNat : Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmod]
  rfl

private theorem bitcast_val (T : IntTy) {t : IntTy} (x : JInt t) (h : t.bits = T.bits) :
    (JuliaLean.base.int.bitcast T x h).val = wrapInt T x.val := by
  unfold JuliaLean.base.int.bitcast
  apply toJInt_congr
  simp only [jlBitcast, BitVec.toNat_cast]
  rw [fromJInt_toNat, h]

private theorem wrapInt_i64_of_bounds {z : Int} (h1 : -(2 ^ (64 - 1) : Int) ≤ z)
    (h2 : z ≤ (2 ^ (64 - 1) : Int) - 1) :
    wrapInt .i64 z = z :=
  wrapInt_of_inRange .i64 z ⟨h1, h2⟩

private theorem wrapInt_i64_of_nat_lt {n : Nat} (h : n < 2 ^ 63) :
    wrapInt .i64 (n : Int) = (n : Int) :=
  wrapInt_i64_of_bounds (by omega) (by omega)

private theorem emod_2pow64_toNat {z : Int} (h1 : 0 ≤ z) (h2 : z < ((2 ^ 64 : Nat) : Int)) :
    (z % ((2 ^ IntTy.i64.bits : Nat) : Int)).toNat = z.toNat := by
  change (z % ((2 ^ 64 : Nat) : Int)).toNat = z.toNat
  rw [Int.emod_eq_of_lt h1 h2]

private theorem fromJInt_remT_u64_toNat (hsh : JInt .u64) :
    (fromJInt (JuliaLean.base.int.remT .i64 hsh)).toNat = hsh.val.toNat := by
  have hhsh := hsh.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Bool.false_eq_true, ite_false] at hhsh
  have hx_val : (JuliaLean.base.int.remT .i64 hsh).val = wrapInt .i64 hsh.val :=
    bitcast_val .i64 hsh rfl
  rw [fromJInt_toNat_eq, hx_val, wrapInt_emod_self]
  exact emod_2pow64_toNat hhsh.1 (by omega)

private theorem fromJInt_sub_one_toNat (szInt : JInt .i64) (h1 : 1 ≤ szInt.val) :
    (fromJInt (JuliaLean.base.int.sub szInt (JuliaLean.base.int.lit .i64 1))).toNat =
      (szInt.val - 1).toNat := by
  have hszb := szInt.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ite_true] at hszb
  have hy_val : (JuliaLean.base.int.sub szInt (JuliaLean.base.int.lit .i64 1)).val =
      szInt.val - 1 := by
    show (JuliaLean.base.int.sub_int szInt (JuliaLean.base.int.lit .i64 1)).val = _
    rw [sub_int_val]
    have h1val : (JuliaLean.base.int.lit .i64 1).val = 1 := rfl
    rw [h1val]
    exact wrapInt_i64_of_bounds (by omega) (by omega)
  rw [fromJInt_toNat_eq, hy_val]
  exact emod_2pow64_toNat (by omega) (by omega)

private theorem hashindex_int_eq (hsh : JInt .u64) (szInt : JInt .i64) (h1 : 1 ≤ szInt.val) :
    ((Nat.land hsh.val.toNat (szInt.val - 1).toNat + 1 : Nat) : Int) =
      (JuliaLean.base.int.add
        (JuliaLean.base.int.and_int (JuliaLean.base.int.remT .i64 hsh)
          (JuliaLean.base.int.sub szInt (JuliaLean.base.int.lit .i64 1)))
        (JuliaLean.base.int.lit .i64 1)).val := by
  have hszb := szInt.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ite_true] at hszb
  have hand_le : Nat.land hsh.val.toNat (szInt.val - 1).toNat ≤ (szInt.val - 1).toNat :=
    Nat.and_le_right
  have hland_lt : Nat.land hsh.val.toNat (szInt.val - 1).toNat < 2 ^ 63 := by omega
  have hidx_lt : Nat.land hsh.val.toNat (szInt.val - 1).toNat + 1 < 2 ^ 63 := by omega
  change ((Nat.land hsh.val.toNat (szInt.val - 1).toNat + 1 : Nat) : Int) =
    (JuliaLean.base.int.add_int
      (JuliaLean.base.int.and_int (JuliaLean.base.int.remT .i64 hsh)
        (JuliaLean.base.int.sub szInt (JuliaLean.base.int.lit .i64 1)))
      (JuliaLean.base.int.lit .i64 1)).val
  rw [add_int_val, and_int_val, fromJInt_remT_u64_toNat hsh, fromJInt_sub_one_toNat szInt h1]
  have h1val : (JuliaLean.base.int.lit .i64 1).val = ((1 : Nat) : Int) := rfl
  rw [h1val, wrapInt_i64_of_nat_lt hland_lt, ← Int.natCast_add, wrapInt_i64_of_nat_lt hidx_lt]

theorem DictHashindexSemantics_proven : DictHashindexSemantics := by
  intro K I _ hash key sz
  refine ⟨fun szInt hsz h1 => ?_, fun err herr => ?_⟩
  · have hand_le : Nat.land (hash key).val.toNat (szInt.val - 1).toNat ≤ (szInt.val - 1).toNat :=
      Nat.and_le_right
    refine ⟨Nat.land (hash key).val.toNat (szInt.val - 1).toNat + 1,
      ?_, hashindex_int_eq (hash key) szInt h1, by omega, by omega, fun p hp => ?_⟩
    · unfold hashindex
      rw [hsz, except_ok_bind]
      rfl
    · have hsub : (szInt.val - 1).toNat = 2 ^ p - 1 := by omega
      rw [hsub]
      exact congrArg (· + 1) (Nat.and_two_pow_sub_one_eq_mod (hash key).val.toNat p)
  · unfold hashindex
    rw [herr]
    rfl

/-! ## 3. `dictscov-dict-l529`: `DictGetCallableDefault` -/

theorem DictGetCallableDefault_proven : DictGetCallableDefault := by
  intro K V Q DF hash eqKey hashQ matchQ h m hl hq hr q
  refine ⟨fun v hv f => ?_, fun v hv err => ?_, fun hnone f => ?_⟩
  · have hgetF := (hr.lookups hl hq q () q f).2.2.1
    rw [hv] at hgetF
    exact hgetF
  · have hgetF := (hr.lookups hl hq q () q (fun _ => (.error err : DictResult DF))).2.2.1
    rw [hv] at hgetF
    exact hgetF
  · have hgetF := (hr.lookups hl hq q () q f).2.2.1
    rw [hnone] at hgetF
    exact hgetF

/-! ## 4. `dictscov-dict-immutable-setindex`: `ImmutableDictSetindexShadows` -/

theorem ImmutableDictSetindexShadows_proven : ImmutableDictSetindexShadows := by
  intro K V Q W R keyConv valueConv eqKey d value key
  have hext := immutableExtend_eq keyConv valueConv d (key, value)
  have hset : setindexImmutable keyConv valueConv d value key =
      immutableExtend keyConv valueConv d (key, value) := rfl
  cases hnp : newPair keyConv valueConv (key, value) with
  | error e =>
    rw [hnp] at hext
    exact ⟨hset.trans hext, hext⟩
  | ok kv =>
    obtain ⟨k, v⟩ := kv
    rw [hnp] at hext
    exact ⟨(k, v) :: d, hset.trans hext, hext, fun r => rfl⟩

/-! ## 5. `dicts-immutabledict-lossy-key`: `ImmutableDictSetGet` (Refuted) -/

theorem ImmutableDictSetGet_refuted : ¬ ImmutableDictSetGet :=
  JuliaLean.Proofs.base.dict.ImmutableDictSetGet_refuted

/-! ## 6. `dictscov-show-limit-ellipsis`: `DictShowLimitEllipsis` (Refuted) -/

def dictIterPairs {K V : Type} (h : DictState K V) : List (K × V) :=
  match (iterateFirst h >>= fun r => match r with
      | none => .ok []
      | some (pair, next) => iterCollect h (h.size + 1) next >>= fun rest => .ok (pair :: rest)) with
  | .ok l => l
  | .error _ => []

def dictShowOps {C K V : Type} (ioContext : C → DictState K V → C) (getLimit : C → Bool)
    (typePrefix : C → DictState K V → String) (circular : C → DictState K V → Bool)
    (showPair : C → K × V → String) : DictShowOps C (DictState K V) K V :=
  ⟨ioContext, getLimit, typePrefix, isempty, circular, dictIterPairs, showPair⟩

def DictShowLimitEllipsis : Prop :=
  ∀ (C K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (ioContext : C → DictState K V → C) (getLimit : C → Bool)
    (typePrefix : C → DictState K V → String) (circular : C → DictState K V → Bool)
    (showPair : C → K × V → String) (io : C) (h : DictState K V) (m : List (K × V)),
    KeyLaws hash eqKey → DictRep hash eqKey h m → SmallTable h → circular io h = false →
    (∀ c p, showPair c p ≠ "…") → (∀ c x, typePrefix c x ≠ "…") →
    ("…" ∈ showDict (dictShowOps ioContext getLimit typePrefix circular showPair) io h ↔
      getLimit io = true ∧ 10 < m.length)

def idHash16 (k : Nat) : JInt .u64 := JInt.lit .u64 (k % 16)

theorem idHash16_laws : KeyLaws idHash16 natEq :=
  ⟨natKeyLaws.refl, natKeyLaws.symm, natKeyLaws.trans,
    fun a b h => by simp only [natEq, beq_iff_eq] at h; rw [h]⟩

def h10 : DictState Nat Unit where
  size := 16
  slots i := if 1 ≤ i ∧ i ≤ 10 then 0x80 else 0
  keys i := if 1 ≤ i ∧ i ≤ 10 then some (i - 1) else none
  vals i := if 1 ≤ i ∧ i ≤ 10 then some () else none
  ndel := 0
  count := 10
  age := JInt.wrap .u64 0
  idxfloor := 1
  maxprobe := 0
  popcursor := 1

theorem h10_inv : Inv idHash16 natEq h10 := by
  refine ⟨Or.inr ⟨4, by decide, rfl⟩, by decide, ?_, ?_, by decide, Or.inr (by decide),
    by decide, fun i hi1 _ _ => hi1, by decide⟩
  · intro i hi1 _
    by_cases hi10 : i ≤ 10
    · rcases (by omega :
          i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
          i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Or.inr (Or.inr ⟨_, (), rfl, rfl, rfl, 0, Nat.le_refl 0, rfl,
        fun e he => absurd he (Nat.not_lt_zero e)⟩)
    · exact Or.inl (by simp [h10, hi1, hi10])
  · intro i j a b hi1 _ hj1 _ hij ha hb
    have ⟨hfi, hki, _⟩ := ent_some ha
    have ⟨hfj, hkj, _⟩ := ent_some hb
    have hi10 : i ≤ 10 := by
      by_cases h : i ≤ 10
      · exact h
      · have hs0 : h10.slots i = 0 := by simp [h10, hi1, h]
        rw [hs0, filledB_zero] at hfi
        cases hfi
    have hj10 : j ≤ 10 := by
      by_cases h : j ≤ 10
      · exact h
      · have hs0 : h10.slots j = 0 := by simp [h10, hj1, h]
        rw [hs0, filledB_zero] at hfj
        cases hfj
    simp only [h10, hi1, hi10, hj1, hj10, and_self, ite_true, Option.some.injEq] at hki hkj
    rw [← hki, ← hkj]
    simp only [natEq, beq_eq_false_iff_ne]
    omega

theorem h10_rep : DictRep idHash16 natEq h10 (tlist h10) := ⟨h10_inv, List.Perm.refl _⟩

theorem DictShowLimitEllipsis_refuted : ¬ DictShowLimitEllipsis := by
  intro h
  have hsm : SmallTable h10 := by show 16 ≤ 2 ^ 50; decide
  have := h Unit Nat Unit idHash16 natEq (fun c _ => c) (fun _ => true) (fun _ _ => "Dict")
    (fun _ _ => false) (fun _ _ => "p") () h10 (tlist h10) idHash16_laws h10_rep hsm rfl
    (fun _ _ => by decide) (fun _ _ => by decide)
  have hmem : "…" ∈ showDict (dictShowOps (fun c _ => c) (fun _ => true) (fun _ _ => "Dict")
      (fun _ _ => false) (fun _ _ => "p")) () h10 := by decide
  exact absurd (this.1 hmem).2 (by decide)

/-! ## 7. `memUnset` helper and `DictDeleteLookup`, `DictPopKeyContract`, `DictPopAnyContract`, `DictFilterContract` -/

theorem memUnset_eq {α : Type} (layout : DictLayout)
    (size : Nat) (mem : Nat → Option α) (i : Nat) :
    memUnset layout size mem i =
      interpretSlots (dictUnsetEffects layout ((JInt.wrap .i64 i).val.toNat - 1))
        (JInt.wrap .i64 i).val.toNat mem := by
  dsimp only [memUnset, JuliaLean.base.genericmemory.unsetindexMemoryInt,
    JuliaLean.base.genericmemory.unsetindexRef, runtimeAccessOps, dictMemoryrefUnset,
    Id.run, StateT.run, bind, StateT.bind, pure, StateT.pure]

private theorem interpretSlotEffect_frame {α : Type} (effect : JuliaLean.src.genericmemory_c.Effect)
    (i : Nat) (slots : Nat → Option α) (j : Nat) (hji : j ≠ i) :
    interpretSlotEffect i slots effect j = slots j := by
  cases effect <;> simp [interpretSlotEffect, hji]

private theorem interpretSlots_frame {α : Type} (effects : List JuliaLean.src.genericmemory_c.Effect)
    (i : Nat) (slots : Nat → Option α) (j : Nat) (hji : j ≠ i) :
    interpretSlots effects i slots j = slots j := by
  induction effects generalizing slots with
  | nil => rfl
  | cons effect effects ih =>
    change interpretSlots effects i (interpretSlotEffect i slots effect) j = slots j
    rw [ih, interpretSlotEffect_frame effect i slots j hji]

theorem memUnset_ne_of_lt {α : Type} (layout : DictLayout)
    (size : Nat) (mem : Nat → Option α) {i j : Nat}
    (hi : i < 2 ^ 63) (hji : j ≠ i) :
    memUnset layout size mem i j = mem j := by
  rw [memUnset_eq]
  have hw : (JInt.wrap .i64 i).val.toNat = i := by
    show (wrapInt .i64 (i : Int)).toNat = i
    rw [wrapInt_of_inRange .i64 (i : Int)
      ⟨by simp only [IntTy.min, IntTy.signed, IntTy.bits, ite_true]; omega,
       by simp only [IntTy.max, IntTy.signed, IntTy.bits, ite_true]; omega⟩]
    exact Int.toNat_natCast i
  rw [hw]
  exact interpretSlots_frame _ i mem j hji

def clampUnset63 {α : Type} (unset : Nat → (Nat → Option α) → Nat → (Nat → Option α))
    (size : Nat) (f : Nat → Option α) (i : Nat) : Nat → Option α :=
  if i < 2 ^ 63 then unset size f i else f

theorem clampUnset63_law {α : Type} (layout : DictLayout) :
    UnsetLaw (clampUnset63 (memUnset (α := α) layout)) := by
  intro size f i j hji
  unfold clampUnset63
  split
  · rename_i hi
    exact memUnset_ne_of_lt layout size f hi hji
  · rfl

theorem deleteAt_clampUnset63 {K V : Type}
    (rtK : DictLayout)
    (rtV : DictLayout)
    (t : DictState K V) (i : Nat) (hi : i < 2 ^ 63) :
    deleteAt (memUnset rtK) (memUnset rtV) t i =
      deleteAt (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV)) t i := by
  unfold deleteAt clampUnset63
  simp only [hi, ite_true]

theorem popAt_clampUnset63 {K V : Type}
    (rtK : DictLayout)
    (rtV : DictLayout)
    (t : DictState K V) (i : Nat) (hi : i < 2 ^ 63) :
    popAt (memUnset rtK) (memUnset rtV) t i =
      popAt (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV)) t i := by
  unfold popAt
  rw [deleteAt_clampUnset63 rtK rtV t i hi]

theorem htKeyindex_le_size {K V Q : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool} {h : DictState K V} {m : List (K × V)}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (q : Q) :
    htKeyindex hashQ matchQ h q = .ok (-1) ∨
      ∃ i : Nat, htKeyindex hashQ matchQ h q = .ok (i : Int) ∧ 1 ≤ i ∧ i ≤ h.size := by
  have hk := hr.htKeyindex hl hq q
  cases hf : rfind matchQ m q with
  | none =>
    rw [hf] at hk
    exact Or.inl hk
  | some e =>
    rw [hf] at hk
    obtain ⟨i, h1, h2, h3, _⟩ := hk
    exact Or.inr ⟨i, h1, h2, h3⟩

theorem deleteKey_clampUnset63 {K V Q : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (rtK : DictLayout)
    (rtV : DictLayout)
    {h : DictState K V} {m : List (K × V)}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (hsz : h.size < 2 ^ 63) (q : Q) :
    deleteKey hashQ matchQ (memUnset rtK) (memUnset rtV) h q =
      deleteKey hashQ matchQ (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV)) h q := by
  unfold deleteKey
  rcases htKeyindex_le_size hl hq hr q with hk | ⟨i, hk, hi1, hi2⟩
  · rw [hk]; rfl
  · rw [hk, except_ok_bind, except_ok_bind, ite_eq_left (by omega), ite_eq_left (by omega)]
    rw [deleteAt_clampUnset63 rtK rtV h ((i : Int).toNat) (by omega)]

theorem popKey_clampUnset63 {K V Q : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (rtK : DictLayout)
    (rtV : DictLayout)
    {h : DictState K V} {m : List (K × V)}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (hsz : h.size < 2 ^ 63) (q : Q) :
    popKey hashQ matchQ (memUnset rtK) (memUnset rtV) h q =
      popKey hashQ matchQ (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV)) h q := by
  unfold popKey
  rcases htKeyindex_le_size hl hq hr q with hk | ⟨i, hk, hi1, hi2⟩
  · rw [hk]; rfl
  · rw [hk, except_ok_bind, except_ok_bind, ite_eq_left (by omega), ite_eq_left (by omega)]
    rw [popAt_clampUnset63 rtK rtV h ((i : Int).toNat) (by omega)]

theorem popDefault_clampUnset63 {K V Q D : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (rtK : DictLayout)
    (rtV : DictLayout)
    {h : DictState K V} {m : List (K × V)}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (hsz : h.size < 2 ^ 63) (q : Q) (default : D) :
    popDefault hashQ matchQ (memUnset rtK) (memUnset rtV) h q default =
      popDefault hashQ matchQ (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV))
        h q default := by
  unfold popDefault
  rcases htKeyindex_le_size hl hq hr q with hk | ⟨i, hk, hi1, hi2⟩
  · rw [hk]; rfl
  · rw [hk, except_ok_bind, except_ok_bind, ite_eq_left (by omega), ite_eq_left (by omega)]
    rw [popAt_clampUnset63 rtK rtV h ((i : Int).toNat) (by omega)]

theorem skipDeleted_le_size {K V : Type} (h : DictState K V) {start : Nat} (hs : 1 ≤ start) :
    skipDeleted h start ≤ h.size := by
  rcases skipDeleted_spec h hs with ⟨h0, _⟩ | ⟨_, hle, _, _⟩ <;> omega

theorem popAny_clampUnset63 {K V : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    (rtK : DictLayout)
    (rtV : DictLayout)
    {h : DictState K V} {m : List (K × V)}
    (hr : DictRep hash eqKey h m) (hsz : h.size < 2 ^ 63) :
    popAny (memUnset rtK) (memUnset rtV) h =
      popAny (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV)) h := by
  unfold popAny
  split
  · rfl
  · have h0 := skipDeleted_le_size h hr.1.popcursor
    have hf := skipDeleted_le_size h hr.1.idxfloor
    have hidx : (if skipDeleted h h.popcursor == 0 then skipDeletedFloor h
        else (skipDeleted h h.popcursor, h)).1 < 2 ^ 63 := by
      unfold skipDeletedFloor
      split <;> dsimp only <;> omega
    dsimp only
    rw [popAt_clampUnset63 rtK rtV _ _ hidx]

theorem filterLoop_clampUnset63 {K V : Type}
    (rtK : DictLayout)
    (rtV : DictLayout)
    (pred : K × V → Bool) :
    ∀ (rem i : Nat) (h : DictState K V),
      i + rem ≤ h.size + 1 → h.size < 2 ^ 63 →
      filterLoop (memUnset rtK) (memUnset rtV) pred h rem i =
        filterLoop (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV)) pred h rem i
  | 0, _, _, _, _ => rfl
  | rem + 1, i, h, hbound, hsz => by
    unfold filterLoop
    split
    · cases keyAt h i with
      | error e => rw [except_error_bind, except_error_bind]
      | ok k =>
        rw [except_ok_bind, except_ok_bind]
        cases valAt h i with
        | error e => rw [except_error_bind, except_error_bind]
        | ok v =>
          rw [except_ok_bind, except_ok_bind]
          have hi : i < 2 ^ 63 := by omega
          rw [deleteAt_clampUnset63 rtK rtV h i hi]
          let h' := if pred (k, v) then h else
            deleteAt (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV)) h i
          have hsz' : h'.size = h.size := by
            dsimp only [h']
            split <;> rfl
          exact filterLoop_clampUnset63 rtK rtV pred rem (i + 1) h' (by omega) (by omega)
    · exact filterLoop_clampUnset63 rtK rtV pred rem (i + 1) h (by omega) hsz

theorem filterBang_clampUnset63 {K V : Type}
    (rtK : DictLayout)
    (rtV : DictLayout)
    (pred : K × V → Bool) (h : DictState K V) (hsz : h.size < 2 ^ 63) :
    filterBang (memUnset rtK) (memUnset rtV) pred h =
      filterBang (clampUnset63 (memUnset rtK)) (clampUnset63 (memUnset rtV)) pred h := by
  unfold filterBang
  split
  · rfl
  · exact filterLoop_clampUnset63 rtK rtV pred h.size 1 h (by omega) hsz

theorem DictDeleteLookup_of_size_lt
    (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (rtK : DictLayout)
    (rtV : DictLayout) (h : DictState K V) (m : List (K × V))
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m)
    (hsz : h.size < 2 ^ 63) (q : Q) :
    ∃ h', deleteKey hashQ matchQ (memUnset rtK) (memUnset rtV) h q = .ok h' ∧
      DictRep hash eqKey h' (rdel matchQ m q) := by
  rw [deleteKey_clampUnset63 rtK rtV hl hq hr hsz q]
  exact hr.deleteKey hl (clampUnset63_law rtK) (clampUnset63_law rtV) hq q

theorem DictPopKeyContract_of_size_lt
    (K V Q D : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool) (hashQ : Q → JInt .u64)
    (matchQ : Q → K → Bool) (rtK : DictLayout)
    (rtV : DictLayout) (h : DictState K V) (m : List (K × V))
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m)
    (hsz : h.size < 2 ^ 63) (q : Q) (default : D) :
    (match rfind matchQ m q with
      | some e => ∃ h', popKey hashQ matchQ (memUnset rtK) (memUnset rtV) h q = .ok (e.2, h') ∧
          DictRep hash eqKey h' (rdel matchQ m q)
      | none => popKey hashQ matchQ (memUnset rtK) (memUnset rtV) h q = .error .keyError) ∧
    (match rfind matchQ m q with
      | some e => ∃ h', popDefault hashQ matchQ (memUnset rtK) (memUnset rtV) h q default =
            .ok (.inl e.2, h') ∧ DictRep hash eqKey h' (rdel matchQ m q)
      | none => popDefault hashQ matchQ (memUnset rtK) (memUnset rtV) h q default =
          .ok (.inr default, h)) := by
  rw [popKey_clampUnset63 rtK rtV hl hq hr hsz q,
    popDefault_clampUnset63 rtK rtV hl hq hr hsz q default]
  exact ⟨hr.popKey hl (clampUnset63_law rtK) (clampUnset63_law rtV) hq q,
    hr.popDefault hl (clampUnset63_law rtK) (clampUnset63_law rtV) hq q default⟩

theorem DictPopAnyContract_of_size_lt
    (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (rtK : DictLayout)
    (rtV : DictLayout) (h : DictState K V) (m : List (K × V))
    (hl : KeyLaws hash eqKey) 
    (hr : DictRep hash eqKey h m) (hsz : h.size < 2 ^ 63) :
    match m with
    | [] => popAny (memUnset rtK) (memUnset rtV) h = .error .argumentError
    | _ :: _ => ∃ e h', popAny (memUnset rtK) (memUnset rtV) h = .ok (e, h') ∧ e ∈ m ∧
        DictRep hash eqKey h' (rdel eqKey m e.1) := by
  have hp := hr.popAny hl (clampUnset63_law rtK) (clampUnset63_law rtV)
  rw [← popAny_clampUnset63 rtK rtV hr hsz] at hp
  cases m <;> exact hp

theorem DictFilterContract_of_size_lt
    (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (rtK : DictLayout)
    (rtV : DictLayout) (h : DictState K V) (m : List (K × V))
    (hl : KeyLaws hash eqKey) 
    (hr : DictRep hash eqKey h m) (hsz : h.size < 2 ^ 63) (pred : K × V → Bool) :
    ∃ h', filterBang (memUnset rtK) (memUnset rtV) pred h = .ok h' ∧
      DictRep hash eqKey h' (m.filter pred) := by
  rw [filterBang_clampUnset63 rtK rtV pred h hsz]
  exact hr.filterBang hl (clampUnset63_law rtK) (clampUnset63_law rtV) pred

theorem memUnset_wraps_at_2pow64_plus_1 :
    memUnset boxedDictLayout (2 ^ 65) (fun _ => some ()) (2 ^ 64 + 1) 1 = none := by
  rw [memUnset_eq]
  decide

/-! ## 8. `dictscov-dict-immutable-iteration`: `immCount` and `ImmutableDictCollectionSemantics` -/

private abbrev immAddOp : JuliaLean.base.reduce.Reducer (JInt .i64) Bool :=
  JuliaLean.base.reduce.valueReducer
    (JuliaLean.base.reduce.add_sum_small id (JuliaLean.base.int.ofBool .i64)
      JuliaLean.base.int.add)
    (JuliaLean.base.reduce.reduce_first_add_sum
      (JuliaLean.base.reduce.reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64)))
    (JuliaLean.base.reduce.reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0)
      (JInt .i64))

private abbrev immMappedOp (K V : Type) : JuliaLean.base.reduce.Reducer (JInt .i64) (K × V) :=
  JuliaLean.base.reduce.mappingRFReducer
    (JuliaLean.base.reduce.mappingRF_constructor
      (JuliaLean.base.reduce._bool (fun _ : K × V => true))
      (JuliaLean.base.reduce.bottomRFReducer immAddOp))

private theorem add_one_i64 (acc : JInt .i64) :
    JuliaLean.base.int.add acc (JuliaLean.base.int.ofBool .i64 true) =
      JInt.wrap .i64 (acc.val + 1) := by
  apply Subtype.ext
  exact add_int_val acc (JuliaLean.base.int.ofBool .i64 true)

private theorem wrap_i64_add_one (n : Nat) :
    JInt.wrap .i64 ((JInt.wrap .i64 n).val + 1) = JInt.wrap .i64 (n + 1 : Nat) := by
  apply Subtype.ext
  show wrapInt .i64 (wrapInt .i64 (n : Int) + 1) = wrapInt .i64 ((n + 1 : Nat) : Int)
  rw [Int.natCast_add]
  change wrapInt .i64 (wrapInt .i64 (n : Int) + 1) = wrapInt .i64 ((n : Int) + 1)
  apply wrapInt_congr
  rw [Int.add_emod, wrapInt_emod_self, ← Int.add_emod]

private theorem immStep_value {K V : Type} (n : Nat) (x : K × V) :
    (immMappedOp K V).step (.value (JInt.wrap .i64 n)) x =
      .value (JInt.wrap .i64 (n + 1 : Nat)) := by
  change JuliaLean.base.reduce.FoldInit.value
    (JuliaLean.base.int.add (JInt.wrap .i64 n) (JuliaLean.base.int.ofBool .i64 true)) = _
  rw [add_one_i64, wrap_i64_add_one]

private theorem immFoldl_true {K V : Type} (xs : List (K × V)) (n : Nat) :
    xs.foldl (immMappedOp K V).step (.value (JInt.wrap .i64 n)) =
      .value (JInt.wrap .i64 (n + xs.length : Nat)) := by
  induction xs generalizing n with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, List.length_cons, immStep_value, ih]
    congr 2
    omega

private theorem xfadjoint_imm (K V : Type) (d : ImmutableDict K V) :
    JuliaLean.base.reduce._xfadjoint (JuliaLean.base.reduce.bottomRFReducer immAddOp)
      (.generator (JuliaLean.base.reduce._bool (fun _ : K × V => true))
        (.values (immutableCollect d))) =
      ⟨K × V, immMappedOp K V, .values (immutableCollect d)⟩ := by
  simp only [JuliaLean.base.reduce._xfadjoint,
    JuliaLean.base.reduce._xfadjoint_unwrap_dispatch,
    JuliaLean.base.reduce._xfadjoint_unwrap_generator,
    JuliaLean.base.reduce._xfadjoint_unwrap_values,
    JuliaLean.base.reduce.MapCallable.isIdentity]
  rfl

theorem immCount_true_eq {K V : Type} (d : ImmutableDict K V) :
    immCount (fun _ => true) d = (JInt.wrap .i64 (immutableCollect d).length).val.toNat := by
  unfold immCount JuliaLean.base.reduce.count_f JuliaLean.base.reduce._simple_count
    JuliaLean.base.reduce.sum_f JuliaLean.base.reduce.mapreduce
    JuliaLean.base.reduce.mapfoldl JuliaLean.base.reduce.mapfoldl_impl
  dsimp only
  rw [xfadjoint_imm]
  unfold JuliaLean.base.reduce.foldl_impl JuliaLean.base.reduce._foldl_impl
    JuliaLean.base.reduce.iteratorValues
  dsimp only
  cases h : immutableCollect d with
  | nil => rfl
  | cons x xs =>
    dsimp only
    have h0 : JuliaLean.base.int.lit .i64 0 = JInt.wrap .i64 (0 : Nat) := rfl
    rw [h0, immStep_value, immFoldl_true]
    simp only [List.length_cons, Nat.zero_add]
    congr 3
    omega

theorem immCount_true_of_lt {K V : Type} (d : ImmutableDict K V) (h : d.length < 2 ^ 63) :
    immCount (fun _ => true) d = (immutableCollect d).length := by
  rw [immCount_true_eq, immutableCollect_eq]
  show (wrapInt .i64 (d.length : Int)).toNat = d.length
  rw [wrapInt_of_inRange .i64 (d.length : Int)
    ⟨by simp only [IntTy.min, IntTy.signed, IntTy.bits, ite_true]; omega,
     by simp only [IntTy.max, IntTy.signed, IntTy.bits, ite_true]; omega⟩]
  exact Int.toNat_natCast d.length

theorem ImmutableDictCollectionSemantics_of_length_lt
    (K V : Type) (d : ImmutableDict K V) (h : d.length < 2 ^ 63) :
    immutableIterate (immutableEmpty K V) = none ∧
    (∀ (p : K × V) (rest : ImmutableDict K V),
      immutableIterate (p :: rest) = some (p, rest) ∧
      immutableIterate d [] = none ∧
      immutableIterate d (p :: rest) = some (p, rest)) ∧
    immutableLength (fun p x => .ok (immCount p x)) d = .ok (immutableCollect d).length ∧
    immutableIsEmpty d = (immutableIterate d).isNone ∧
    immutableEmptyLike K V d = immutableEmpty K V ∧
    immutableCollect (immutableEmptyLike K V d) = [] := by
  refine ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, rfl, rfl⟩
  · unfold immutableLength
    dsimp only
    rw [immCount_true_of_lt d h]
  · cases d <;> rfl

theorem immCount_overflow_at_2pow63 :
    let d : ImmutableDict Unit Unit := List.replicate (2 ^ 63) ((), ())
    immCount (fun _ => true) d = 0 ∧ (immutableCollect d).length = 2 ^ 63 := by
  intro d
  have hlen : (immutableCollect d).length = 2 ^ 63 := by
    rw [immutableCollect_eq]
    exact List.length_replicate
  refine ⟨?_, hlen⟩
  rw [immCount_true_eq, hlen]
  decide

/-! ## 9. `PersistentDict` wrapper reduction lemmas -/

theorem PersistentLookupSemantics_of_keyGet
    {K V D : Type} {egal : K → K → Bool} {runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K}
    {d : PersistentDict K V (PTrie K V)} {m : List (K × V)}
    {key : K} (default : D) (fallback : Unit → DictResult D)
    (hk : persistentKeyGet (hamtOps egal runtime) d key = rlookup egal m key) :
    persistentKeyGet (hamtOps egal runtime) d key = rlookup egal m key ∧
    persistentGetindex (hamtOps egal runtime) d key =
      (match rlookup egal m key with | some v => .ok v | none => .error .keyError) ∧
    persistentHasKey (hamtOps egal runtime) d key = (rlookup egal m key).isSome ∧
    persistentGet (hamtOps egal runtime) d key default =
      (match rlookup egal m key with | some v => .inl v | none => .inr default) ∧
    persistentGetDefault (hamtOps egal runtime) d key fallback =
      (match rlookup egal m key with | some v => .ok (.inl v) | none => .inr <$> fallback ()) ∧
    persistentGetTypedDefault (hamtOps egal runtime) d key fallback =
      (match rlookup egal m key with | some v => .ok (.inl v) | none => .inr <$> fallback ()) := by
  refine ⟨hk, ?_, ?_, ?_, ?_, ?_⟩
  · unfold persistentGetindex; rw [hk]; cases rlookup egal m key <;> rfl
  · unfold persistentHasKey; rw [hk]
  · unfold persistentGet; rw [hk]; cases rlookup egal m key <;> rfl
  · unfold persistentGetDefault; rw [hk]; cases rlookup egal m key <;> rfl
  · unfold persistentGetTypedDefault; rw [hk]; cases rlookup egal m key <;> rfl

theorem PersistentPairMembershipSemantics_of_keyGet
    {K V R : Type} {egal : K → K → Bool} {runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K}
    {d : PersistentDict K V (PTrie K V)} {m : List (K × V)}
    (pair : K × V) (valcmp : V → V → DictResult R)
    (hk : persistentKeyGet (hamtOps egal runtime) d pair.1 = rlookup egal m pair.1) :
    persistentIn (hamtOps egal runtime) valcmp d pair =
      (match rlookup egal m pair.1 with
        | none => .ok (.inl false)
        | some stored => .inr <$> valcmp pair.2 stored) := by
  unfold persistentIn
  rw [hk]
  cases rlookup egal m pair.1 <;> rfl

theorem persistentKeyGet_emptyLike {K V : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (d : PersistentDict K V (PTrie K V)) (q : K) :
    persistentKeyGet (hamtOps egal runtime)
      (persistentEmptyLike (hamtOps egal runtime) d) q = none := rfl


end round2


private def openEntry (id : String) (juliaFns : List String) (statement source : String)
    (prop : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/dict.jl", juliaFns := juliaFns, statement := statement,
    source := source, status := .todo, prop := prop, thm := none }
private def oldEntries : List Entry := [
  proven "dicts-ops-agree" ["Dict@77", "setindex!@374", "delete!@681", "pop!@586", "pop!@615", "get!@457",
    "sizehint!@196", "empty!@224", "filter!@725", "map!@741", "getindex@480", "get@507",
    "haskey@553", "iterate@707", "iterate@710", "isempty@712", "length@713"]
    "Dict() is empty and every source-mirrored Dict operation (setindex!, delete!, pop!, get!, sizehint!, empty!, filter!, map!) preserves the reference finite map, while lookups, haskey, length, isempty and iteration agree with the reference map."
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
    "sizehint!(d, n; shrink) converts any Integer n to Int (propagating InexactError), keeps every pair when 3n fits in Int, and rehash! throws a concurrent-write error if age changes during copying."
    "sizehint! docstring base/array.jl:1581-1586; base/dict.jl:139-204" ``DictSizehintSmall
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
  refuted "dicts-immutabledict-to-dict" ["Dict@91", "Dict@118", "iterate@860", "length@864", "get@843"]
    "Dict(d) and Dict{K,V}(d) for an ImmutableDict d map every key to d[key], its most recent value."
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
    "Every slot accessed by linear probing, ht_keyindex, ht_keyindex2_shorthash! and rehash! lies in 1:sz and filled slots hold defined keys and values."
    "base/dict.jl:139-322" ``DictProbeSafe ``DictProbeSafe_proven,
  proven "dictscov-dict-construct" ["Dict@77", "Dict@83", "Dict@91", "Dict@99", "Dict@100", "Dict@109",
    "Dict@110", "copy@111", "Dict@115", "Dict@116", "Dict@118", "empty@120"]
    "Each Dict constructor builds a table representing the reference map of its converted pairs (later isequal keys win, first conversion error propagates); copy keeps the pairs and counters."
    "Dict docstring base/dict.jl:31-64" ``DictConstructionSemantics ``DictConstructionSemantics_proven,
  proven "dictscov-dict-slots" ["_shorthash7@123", "hashindex@128", "isslotempty@135", "isslotfilled@136", "isslotmissing@137"]
    "_shorthash7 is a filled slot byte holding the top seven hash bits, hashindex is hash mod sz plus one for power-of-two sizes, and the three slot predicates partition well-formed Dict slots and track empty! and _delete! transitions."
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
  proven "dictscov-dict-l135" ["isslotempty@135"]
    "isslotempty, isslotmissing and isslotfilled partition the slots of every well-formed Dict, and empty! makes every slot empty."
    "base/dict.jl:135" ``DictSlots ``DictSlots_proven,
  proven "dictscov-dict-l136" ["isslotfilled@136"]
    "isslotfilled holds exactly at slots with a stored key-value entry, disjoint from isslotempty and isslotmissing, and is set by _shorthash7."
    "base/dict.jl:136" ``DictSlots ``DictSlots_proven,
  proven "dictscov-dict-l137" ["isslotmissing@137"]
    "isslotmissing is disjoint from isslotempty and isslotfilled on every well-formed Dict and marks tombstone slots left by _delete! when the following slot is non-empty."
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
    "hashindex converts any Integer sz to Int and returns the one-based slot hash mod sz plus one and the short hash of the key."
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
    "Pair membership scans matching keys in iteration order: the first true comparison wins, the first error propagates, and missing throws TypeError."
    "ImmutableDict docstring base/dict.jl:794-795; base/dict.jl:817-826" ``ImmutableDictPairMembershipSemantics
    ``ImmutableDictPairMembershipSemantics_proven,
  openEntry "dictscov-dict-immutable-iteration" ["iterate@860", "length@864", "isempty@865", "empty@866"]
    "ImmutableDict length and isempty agree with iteration, which shows every pair including duplicates; empty has no pairs."
    "ImmutableDict docstring base/dict.jl:785-799; base/dict.jl:860-866" ``ImmutableDictCollectionSemantics,
  proven "dictscov-dict-immutable-similar" ["_similar_for@890", "_similar_for@891"]
    "A Pair element type gives an empty dictionary of the kind of the source (Dict, ImmutableDict, PersistentDict); other element types throw ArgumentError."
    "base/dict.jl:890-892" ``DictSimilarSemantics ``DictSimilarSemantics_proven,
  proven "dictscov-dict-persistent-construct" ["KeyValue.set@903", "KeyValue.set@906", "PersistentDict@969",
    "PersistentDict@970", "PersistentDict@976", "PersistentDict@992", "PersistentDict@1000"]
    "PersistentDict{K,V}() and KeyValue.set(PersistentDict{K,V}) are empty; one-pair constructors hold their converted pair; multi-pair constructors hold the converted pairs in argument order, later === keys winning, and propagate the first conversion error."
    "PersistentDict docstring base/dict.jl:936-965; base/dict.jl:903-908,969-1006" ``PersistentConstructorSemantics
    ``PersistentConstructorSemantics_proven,
  proven "dictscov-dict-persistent-set" ["KeyValue.set@909", "KeyValue.set@911", "_keyvalueset@913",
    "PersistentDict@982", "PersistentDict@983", "PersistentDict@986"]
    "Persistent insertions convert key and value to K and V (propagating conversion errors) and return a new dictionary holding the pair and every other pair, with later === keys replacing earlier ones."
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
  openEntry "dictscov-dict-persistent-collection" ["eltype@1008", "iterate@1063", "length@1065", "isempty@1066", "empty@1067", "Iterators.only@1069"]
    "PersistentDict iteration visits every pair once, length returns the wrapping native count, isempty tests whether there are pairs, eltype is Pair{K,V}, empty has no pairs, and Iterators.only checks the native length before returning the first pair."
    "PersistentDict docstring; base/dict.jl:1008,1063-1069" ``PersistentCollectionSemantics,
  proven "dicts-source-mergewith" ["mergewith!@753"]
    "mergewith!(combine, d1, d2) merges the pairs of d2 in iteration order, combining the values of present keys with combine(old, new) and adding the others like setindex!, propagating the first error."
    "mergewith! docstring base/abstractdict.jl; base/dict.jl:753-774" ``DictMergewithSemantics
    ``DictMergewithSemantics_proven
]


private def round2Entries : List Entry := [
  openEntry "dicts-delete-lookup" ["delete!@681", "_delete!@631"]
    "After delete!(d, k), keys isequal to k miss and every other lookup is unchanged."
    "delete! docstring base/dict.jl:658-679" ``JuliaLean.Proofs.base.dict.round2.DictDeleteLookup,
  openEntry "dicts-pop-key" ["pop!@586", "pop!@615", "_pop!@580"]
    "pop!(d, k) returns and deletes the stored value or throws KeyError; pop!(d, k, default) returns default and leaves d unchanged when k is absent."
    "pop! docstring base/dict.jl:591-612" ``JuliaLean.Proofs.base.dict.round2.DictPopKeyContract,
  openEntry "dicts-filter" ["filter!@725"]
    "filter!(pred, d) keeps exactly the pairs satisfying pred, for every hash including full collisions."
    "filter! docstring base/array.jl; base/dict.jl:725-733" ``JuliaLean.Proofs.base.dict.round2.DictFilterContract,
  openEntry "dicts-pop-any" ["pop!@620"]
    "pop!(d) on a non-empty Dict removes and returns one stored pair; on an empty Dict it throws ArgumentError."
    "pop! docstring base/array.jl; base/dict.jl:620-629" ``JuliaLean.Proofs.base.dict.round2.DictPopAnyContract,
  refuted "dicts-immutabledict-lossy-key" ["ImmutableDict@782", "ImmutableDict@812", "setindex@886", "getindex@836"]
    "After d2 = ImmutableDict(d, key => value) or setindex(d, value, key), d2[key] is value."
    "ImmutableDict docstring base/dict.jl:785-797; setindex docstring base/dict.jl:868-885" ``JuliaLean.Proofs.base.dict.round2.ImmutableDictSetGet
    ``JuliaLean.Proofs.base.dict.round2.ImmutableDictSetGet_refuted
    "new(parent, key, value) converts the key without an isequal check: setindex(ImmutableDict{Float32,Int}(), 1, 0.1) stores Float32(0.1) and d2[0.1] throws KeyError.",
  openEntry "dicts-persistentdict-nothrow" ["KeyValue.set@911", "_keyvalueset@913"]
    "KeyValue.set(dict::PersistentDict{K,V}, key::K, val::V), annotated @assume_effects :nothrow, returns for every key and value."
    "effect annotation base/dict.jl:911-912" ``JuliaLean.Proofs.base.dict.round2.PersistentSetNothrow,
  openEntry "memsafety-dict-persistent-path" ["KeyValue.get@1033"]
    "KeyValue.get reads the leaf trie.data[i] only at the end of a path HAMT.path reports found and present, for a stored key, and returns its value."
    "base/dict.jl:1033-1045; base/hamt.jl:158-187" ``JuliaLean.Proofs.base.dict.round2.PersistentPathSafe,
  openEntry "dictscov-dict-pop" ["_pop!@580", "pop!@586", "pop!@615", "_delete!@631"]
    "pop!(h, key) returns the stored value and removes the key or throws KeyError; pop!(h, key, default) returns default instead; _pop!/_delete! remove exactly the found pair."
    "pop! docstring base/dict.jl:591-687" ``JuliaLean.Proofs.base.dict.round2.DictPopKeyContract,
  proven "dictscov-dict-l99" ["Dict@99"]
    "Dict{K,V}(p::Pair) holds the converted pair or throws its conversion error."
    "Dict docstring; base/dict.jl:99" ``JuliaLean.Proofs.base.dict.round2.DictSinglePairConstructorSemantics
    ``JuliaLean.Proofs.base.dict.round2.DictSinglePairConstructorSemantics_proven,
  proven "dictscov-dict-l128" ["hashindex@128"]
    "hashindex propagates Integer-to-Int conversion errors and, for positive Int sizes, returns the short hash and the one-based slot from Julia's Int arithmetic."
    "base/dict.jl:128-133" ``JuliaLean.Proofs.base.dict.round2.DictHashindexSemantics
    ``JuliaLean.Proofs.base.dict.round2.DictHashindexSemantics_proven,
  openEntry "dictscov-dict-l631" ["_delete!@631"]
    "Deleting a filled slot removes its mapping and repairs tombstones without changing other mappings."
    "base/dict.jl:631-656" ``JuliaLean.Proofs.base.dict.round2.DictDeleteLookup,
  openEntry "dictscov-dict-l615" ["pop!@615"]
    "The default pop! removes and returns a found value and otherwise returns default."
    "base/dict.jl:615-618" ``JuliaLean.Proofs.base.dict.round2.DictPopKeyContract,
  openEntry "dictscov-dict-l586" ["pop!@586"]
    "pop! returns and removes a stored key's value, or throws KeyError when absent."
    "base/dict.jl:586-589" ``JuliaLean.Proofs.base.dict.round2.DictPopKeyContract,
  openEntry "dictscov-dict-l580" ["_pop!@580"]
    "_pop! returns the value of the indexed pair and deletes it."
    "base/dict.jl:580-584" ``JuliaLean.Proofs.base.dict.round2.DictPopKeyContract,
  proven "dictscov-dict-l529" ["get@529"]
    "get(f, d, key) returns the stored value without calling f when present, or returns f's result and propagates its error when absent."
    "base/dict.jl:529-532" ``JuliaLean.Proofs.base.dict.round2.DictGetCallableDefault
    ``JuliaLean.Proofs.base.dict.round2.DictGetCallableDefault_proven,
  openEntry "dictscov-dict-immutable-iteration" ["iterate@860", "length@864", "isempty@865", "empty@866"]
    "ImmutableDict length and isempty agree with iteration, which shows every pair including duplicates; empty has no pairs."
    "ImmutableDict docstring base/dict.jl:785-799; base/dict.jl:860-866" ``JuliaLean.Proofs.base.dict.round2.ImmutableDictCollectionSemantics,
  openEntry "dictscov-dict-persistent-lookup" ["KeyValue.get@1033", "KeyValue.get@1047", "haskey@1017", "getindex@1021", "get@1027", "get@1053"]
    "PersistentDict lookups return the stored value of a === key, throw KeyError when required, and use defaults only for absent keys."
    "PersistentDict docstring; base/dict.jl:1017-1057" ``JuliaLean.Proofs.base.dict.round2.PersistentLookupSemantics,
  openEntry "dictscov-dict-persistent-membership" ["in@1010"]
    "Pair membership is false for an absent key and otherwise compares the stored value with valcmp."
    "base/dict.jl:1010-1015" ``JuliaLean.Proofs.base.dict.round2.PersistentPairMembershipSemantics,
  openEntry "dictscov-dict-persistent-collection" ["iterate@1063", "length@1065", "isempty@1066", "empty@1067", "Iterators.only@1069"]
    "PersistentDict iteration visits every pair once, length returns the wrapping native count, isempty tests whether there are pairs, empty has no pairs, and Iterators.only checks the native length before returning the first pair."
    "PersistentDict docstring; base/dict.jl:1063-1069" ``JuliaLean.Proofs.base.dict.round2.PersistentCollectionSemantics,
  proven "dictscov-dict-immutable-setindex" ["ImmutableDict@782", "ImmutableDict@812", "setindex@886"]
    "ImmutableDict constructors and setindex store the converted pair so it shadows equal keys, preserves other lookups, and propagates conversion errors."
    "setindex docstring base/dict.jl:868-885; ImmutableDict docstring base/dict.jl:785-808" ``JuliaLean.Proofs.base.dict.round2.ImmutableDictSetindexShadows
    ``JuliaLean.Proofs.base.dict.round2.ImmutableDictSetindexShadows_proven
]

private def round1ApprovedIds : List String := [
  "dicts-immutabledict-in-missing",
  "dictscov-dict-lookup",
  "dictscov-dict-iterate",
  "dictscov-dict-l110",
  "dictscov-dict-l507",
  "dictscov-dict-l480",
  "dictscov-dict-l689",
  "dictscov-dict-l575",
  "dictscov-dict-l715",
  "dictscov-dict-l554",
  "dictscov-dict-l698",
  "dictscov-dict-l553",
  "dictscov-dict-l741",
  "dictscov-dict-immutable-construct",
  "dictscov-dict-immutable-lookup",
  "dictscov-dict-immutable-membership"
]

end JuliaLean.Proofs.base.dict

namespace JuliaLean.Proofs.base.dict.Round3

open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict

/- Public plumbing dispositions required by review check 2:
* Dict{K,V}@87 merely installs the supplied raw fields, with no documented
  consistency guarantee for arbitrary raw input; no independent Prop is added.
* eltype(::PersistentDict{K,V})@1008 returns Pair{K,V}. Its model persistentEltype
  is the corresponding type identity. A field/type identity would only unfold,
  so this method has nothing independent to promise beyond type plumbing.
These comments are new candidate Proofs text, not edits to frozen input files.
-/

/-- Dict emptiness and length agree with independently executed source iteration.
Julia source: base/dict.jl:706-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/base/collections.md:81,84; base/abstractdict.jl:83-92
  @ f755f49a9e41380d7da126b3c1db9fe7f83dd027

Inv describes slot occupancy, defined key/value cells, stored count and the
iteration floor on the input. It does not assume what iterateFirst/iterateNext
return. iterCollect only repeats actual iterateNext calls, with more steps than
there are slots; the bound prevents the Int cursor from wrapping. No hash or
comparison callback is executed by these read-only subjects.
-/
def DictReadOnlyObservations : Prop :=
  ∀ (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (h : DictState K V),
    Inv hash eqKey h → h.size < 2 ^ 63 - 1 →
    (JuliaLean.base.dict.isempty h = true ↔ iterateFirst h = .ok none) ∧
    ∃ pairs,
      (iterateFirst h >>= fun step =>
        match step with
        | none => .ok []
        | some (pair, next) =>
          iterCollect h (h.size + 1) next >>= fun rest => .ok (pair :: rest)) = .ok pairs ∧
      JuliaLean.base.dict.length h = pairs.length

end JuliaLean.Proofs.base.dict.Round3

section
-- Source section: PersistentWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Every API-generated reference map has distinct keys, independently of the
implementation used for the underlying trie. -/
theorem persistentPRepDistinct {K V H HS S : Type}
    {ops : PersistentOps K V K V H HS S} {egal : K → K → Bool}
    {d : PersistentDict K V H} {m : List (K × V)}
    (h : round2.PRep ops egal d m) : Distinct egal m := by
  induction h with
  | empty => exact List.Pairwise.nil
  | singleton _ => exact List.Pairwise.cons (by intro e he; cases he) List.Pairwise.nil
  | set _ _ ih => exact distinct_rset ih _ _
  | delete _ ih => exact distinct_rdel ih _

/-- Once the concrete key-get theorem is proved, the exact pair-membership
contract follows with no additional HAMT invariant. -/
theorem persistentMembershipOfLookup
    (h : round2.PersistentLookupSemantics) :
    round2.PersistentPairMembershipSemantics := by
  intro K V R egal runtime hl d m hr pair valcmp
  have hk := (h K V Unit egal runtime hl d m hr pair.1 () (fun _ => .ok ())).1
  exact round2.PersistentPairMembershipSemantics_of_keyGet pair valcmp hk

/-- All empty-like dictionaries give the same empty reference lookup. -/
theorem persistentEmptyLikeKeyGet {K V : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (d : PersistentDict K V (round2.PTrie K V)) (key : K) :
    persistentKeyGet (round2.hamtOps egal runtime)
      (persistentEmptyLike (round2.hamtOps egal runtime) d) key =
        rlookup egal ([] : List (K × V)) key := rfl

/-- The first pair of a positive-fuel collection is the initial iterator's pair. -/
theorem persistentCollectHead {K V Q W H HS S : Type}
    (ops : PersistentOps K V Q W H HS S) (d : PersistentDict K V H) (n : Nat) :
    (persistentCollectFuel ops d (n + 1) none).head? =
      (persistentIterate ops d none).map (fun p => p.1) := by
  unfold persistentCollectFuel
  cases persistentIterate ops d none <;> rfl

/-- The `only` wrapper needs just a successful native-length result and the
first iteration result; no additional structural HAMT fact is used here. -/
theorem persistentOnlyOfLength {K V Q W H HS S : Type}
    (ops : PersistentOps K V Q W H HS S) (d : PersistentDict K V H)
    (n : JInt .i64) (fuel : Nat)
    (h : persistentLength ops d = some (.ok n)) :
    persistentOnly ops d = some
      (if n.val = 1 then
        match (persistentCollectFuel ops d (fuel + 1) none).head? with
        | some e => .ok e
        | none => .error (.inr (.argumentError "PersistentDict must be non-empty"))
      else .error (.inr (.argumentError "Collection must contain exactly 1 element"))) := by
  rw [persistentCollectHead]
  unfold persistentOnly
  rw [h]
  by_cases hn : n.val = 1
  · have hnat : n.val.toNat = 1 := by omega
    simp only [Bool.true_eq, ite_true, Option.bind_some, JuliaLean.base.iterators.sourceMethod1673,
      bind, Except.bind, pure, Except.pure, hnat, ne_eq, not_true_eq_false,
      decide_false, Bool.false_eq_true, ite_false, hn, firstPersistent]
    cases persistentIterate ops d none <;> rfl
  · have hnat : n.val.toNat ≠ 1 := by omega
    simp only [Bool.true_eq, ite_true, Option.bind_some, JuliaLean.base.iterators.sourceMethod1673,
      bind, Except.bind, pure, Except.pure, hnat, decide_true, hn, ite_false,
      Except.mapError]
    simp only [decide_eq_true_eq]
    rw [ite_eq_left hnat]

/-- A new persistent dictionary's concrete heap has one empty vector and one
zero-bitmap root node. -/
def persistentEmptyHeap (K V : Type) : JuliaLean.base.hamt.HamtHeap K V :=
  ⟨[[]], [⟨0, 0⟩]⟩

theorem persistentEmptyTrie {K V : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K) :
    (persistentEmpty (round2.hamtOps (V := V) egal runtime)).trie =
      .ok (persistentEmptyHeap K V, 0) := rfl

/-- Empty-state read correctness for all key types, value types and query keys. -/
theorem persistentEmptyKeyGet {K V : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K) (key : K) :
    persistentKeyGet (round2.hamtOps egal runtime)
      (persistentEmpty (round2.hamtOps (V := V) egal runtime)) key = none := rfl

theorem persistentEmptyLength {K V : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K) :
    persistentLength (round2.hamtOps egal runtime)
      (persistentEmpty (round2.hamtOps (V := V) egal runtime)) =
        some (.ok (JInt.lit .i64 0)) := by
  have hcore : JuliaLean.base.hamt.lengthHAMT JuliaLean.base.hamt.heapVectorOps 0
      (persistentEmptyHeap K V) = some (.ok (JInt.lit .i64 0), persistentEmptyHeap K V) := by
    rw [JuliaLean.base.hamt.lengthHAMT]
    change JuliaLean.base.hamt.lengthEntries JuliaLean.base.hamt.heapVectorOps 0 0 1
      (JInt.lit .i64 0) (persistentEmptyHeap K V) = _
    rw [JuliaLean.base.hamt.lengthEntries]
    rfl
  change ((round2.runPartialTrie (.ok (persistentEmptyHeap K V, 0))
    (JuliaLean.base.hamt.lengthHAMT JuliaLean.base.hamt.heapVectorOps)).map fun
      | .ok (n, _) => (Except.ok n : DictResult (JInt .i64))
      | .error e => .error (round2.hamtThrow e)) = _
  unfold round2.runPartialTrie JuliaLean.base.hamt.runPartialHamt
  dsimp only
  rw [hcore]
  rfl

theorem persistentEmptyIsEmpty {K V : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K) :
    persistentIsEmpty (round2.hamtOps egal runtime)
      (persistentEmpty (round2.hamtOps (V := V) egal runtime)) = some (.ok true) := by
  have hcore : JuliaLean.base.hamt.isemptyHAMT JuliaLean.base.hamt.heapVectorOps 0
      (persistentEmptyHeap K V) = some (.ok true, persistentEmptyHeap K V) := by
    rw [JuliaLean.base.hamt.isemptyHAMT]
    rfl
  change ((round2.runPartialTrie (.ok (persistentEmptyHeap K V, 0))
    (JuliaLean.base.hamt.isemptyHAMT JuliaLean.base.hamt.heapVectorOps)).map fun
      | .ok (b, _) => (Except.ok b : DictResult Bool)
      | .error e => .error (round2.hamtThrow e)) = _
  unfold round2.runPartialTrie JuliaLean.base.hamt.runPartialHamt
  dsimp only
  rw [hcore]
  rfl

/-- The exact collection target reduces to the three HAMT facts about iteration,
native length and emptiness; the remaining clauses are discharged uniformly. -/
theorem persistentCollectionOfCore {K V : Type} (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K)
    (d : PersistentDict K V (round2.PTrie K V)) (m : List (K × V))
    (hiter : List.Perm
      (persistentCollectFuel (round2.hamtOps egal runtime) d (m.length + 1) none) m)
    (hlen : persistentLength (round2.hamtOps egal runtime) d =
      some (.ok (JInt.lit .i64 (Int.ofNat m.length))))
    (hempty : persistentIsEmpty (round2.hamtOps egal runtime) d = some (.ok m.isEmpty)) :
    List.Perm (persistentCollectFuel (round2.hamtOps egal runtime) d (m.length + 1) none) m ∧
    persistentLength (round2.hamtOps egal runtime) d =
      some (.ok (JInt.lit .i64 (Int.ofNat m.length))) ∧
    persistentIsEmpty (round2.hamtOps egal runtime) d = some (.ok m.isEmpty) ∧
    (∀ q : K, persistentKeyGet (round2.hamtOps egal runtime)
      (persistentEmptyLike (round2.hamtOps egal runtime) d) q = none) ∧
    persistentLength (round2.hamtOps egal runtime)
      (persistentEmptyLike (round2.hamtOps egal runtime) d) = some (.ok (JInt.lit .i64 0)) ∧
    persistentOnly (round2.hamtOps egal runtime) d = some
      (if (JInt.lit .i64 (Int.ofNat m.length)).val = 1 then
        match (persistentCollectFuel (round2.hamtOps egal runtime) d (m.length + 1) none).head? with
        | some e => .ok e
        | none => .error (.inr (.argumentError "PersistentDict must be non-empty"))
      else .error (.inr (.argumentError "Collection must contain exactly 1 element"))) := by
  exact ⟨hiter, hlen, hempty, fun _ => rfl, persistentEmptyLength egal runtime,
    persistentOnlyOfLength _ d _ m.length hlen⟩

open JuliaLean.base.hamt

/-- State-and-error semantics for composing concrete HAMT actions. -/
theorem persistentHamtBindRun {K V A B : Type} (action : HamtM K V A)
    (cont : A → HamtM K V B) (heap : HamtHeap K V) :
    runHamt (action >>= cont) heap =
      match runHamt action heap with
      | (.error e, heap') => (.error e, heap')
      | (.ok a, heap') => runHamt (cont a) heap' := by
  have hb : (action >>= cont).run heap =
      match action.run heap with
      | (.error e, heap') => (.error e, heap')
      | (.ok a, heap') => (cont a).run heap' := by
    simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
    cases h : action heap with
    | mk result after => cases result <;> rfl
  exact congrArg Id.run hb

/-- A single equation of the concrete HAMT traversal loop. -/
theorem persistentHamtLoopRun {K V B : Type} (state : B)
    (step : Unit → B → HamtM K V (ForInStep B)) (heap : HamtHeap K V) :
    runHamt (Lean.Loop.forIn (m := HamtM K V) (β := B) ({} : Lean.Loop) state step) heap =
      match runHamt (step () state) heap with
      | (.error e, heap') => (.error e, heap')
      | (.ok (.done result), heap') => (.ok result, heap')
      | (.ok (.yield next), heap') =>
          runHamt (Lean.Loop.forIn (m := HamtM K V) (β := B) ({} : Lean.Loop) next step) heap' := by
  cases h : runHamt (step () state) heap with
  | mk out heap' =>
    have hrun : StateT.run (ExceptT.run (step () state)) heap = (out, heap') := by
      simpa only [runHamt] using h
    rw [Lean.Loop.forIn_eq_of_monadTail]
    unfold runHamt
    rw [ExceptT.run_bind, StateT.run_bind, hrun]
    cases out with
    | error e => rfl
    | ok result => cases result <;> rfl

/-- An explicit form of one non-copying path step. It is used only to reason
about the frozen traversal, and does not replace or alter that traversal. -/
def persistentPathReadStep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (top : Nat) :
    Unit → (Nat × HashState K × Option (PathResult K V)) →
      HamtM K V (ForInStep (Nat × HashState K × Option (PathResult K V))) :=
  fun _ state => do
    let current := state.1
    let h := state.2.1
    let result := state.2.2
    if result.isNone then
      let bi := BitmapIndex.fromHash h
      let i ← entry_index current bi
      if ← isset current bi then
        let node ← readNode current
        match ← heapVectorOps.get node.data i with
        | .leaf leaf => pure (.yield
            (current, h, some ⟨same leaf.key h.key, true, current, i, bi, top, h⟩))
        | .trie child => pure (.yield (child, next runtime h, result))
      else pure (.yield (current, h, some ⟨true, false, current, i, bi, top, h⟩))
    else pure (.done (current, h, result))

/-- If the initial path step finds a leaf or an empty slot, the loop returns
that result without any further heap access. -/
theorem persistentPathReadRunOfStep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (root : Nat) (initial : HashState K)
    (heap after : HamtHeap K V) (current : Nat) (hash : HashState K)
    (result : PathResult K V)
    (hstep : runHamt (persistentPathReadStep same runtime root () (root, initial, none)) heap =
      (.ok (.yield (current, hash, some result)), after)) :
    runHamt (path heapVectorOps same runtime root initial false) heap = (.ok result, after) := by
  have hloop : runHamt
      (Lean.Loop.forIn (m := HamtM K V)
        (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
        (root, initial, none) (persistentPathReadStep same runtime root)) heap =
      (.ok (current, hash, some result), after) := by
    rw [persistentHamtLoopRun, hstep]
    dsimp only
    exact persistentHamtLoopRun (current, hash, some result)
      (persistentPathReadStep same runtime root) after
  rw [path.eq_1]
  simp only [Bool.false_eq_true, ite_false, ForIn.forIn]
  change runHamt (do
    let final ← Lean.Loop.forIn (m := HamtM K V)
      (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
      (root, initial, none) (persistentPathReadStep same runtime root)
    match final.2.2 with
    | some r => pure r
    | none => throw HamtError.bounds) heap = _
  rw [persistentHamtBindRun, hloop]
  rfl

/-- The two tags represent the constructible Julia values
`UInt64(13698151559422712335)` and `Int64(8252252557198629082)`.
Both have object identity word zero on both checked Julia versions. -/
inductive PersistentCollisionKey where
  | unsignedWord
  | signedWord
  deriving DecidableEq

def persistentCollisionEq (a b : PersistentCollisionKey) : Bool := decide (a = b)

def persistentCollisionRuntime : HamtObjectIdRuntime PersistentCollisionKey :=
  ⟨fun _ => JInt.lit .u64 0⟩

theorem persistentCollisionKeyLaws :
    KeyLaws persistentCollisionRuntime.objectid persistentCollisionEq := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    exact decide_eq_true (Eq.refl a)
  · intro a b h
    exact decide_eq_true (of_decide_eq_true h).symm
  · intro a b c hab hbc
    exact decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc))
  · intro a b _
    rfl

def persistentCollisionHeap : HamtHeap PersistentCollisionKey Unit :=
  ⟨[[some (.leaf ⟨.unsignedWord, ()⟩)]], [⟨0, 1⟩]⟩

def persistentCollisionDict :
    PersistentDict PersistentCollisionKey Unit (round2.PTrie PersistentCollisionKey Unit) :=
  ⟨.ok (persistentCollisionHeap, 0)⟩

theorem persistentCollisionSingleton :
    persistentSingleton (round2.hamtOps persistentCollisionEq persistentCollisionRuntime)
      .unsignedWord () = .ok persistentCollisionDict := rfl

theorem persistentCollisionRep :
    round2.PRep (round2.hamtOps persistentCollisionEq persistentCollisionRuntime)
      persistentCollisionEq persistentCollisionDict [(.unsignedWord, ())] :=
  round2.PRep.singleton persistentCollisionSingleton

def persistentPathCopyStep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (top : Nat) :
    Unit → (Nat × HashState K × Option (PathResult K V)) →
      HamtM K V (ForInStep (Nat × HashState K × Option (PathResult K V))) :=
  fun _ state => do
    if state.2.2.isNone = true then
      let index ← entry_index state.1 (BitmapIndex.fromHash state.2.1)
      if ← isset state.1 (BitmapIndex.fromHash state.2.1) then
        let node ← readNode state.1
        let entry ← heapVectorOps.get node.data index
        Entry.casesOn entry
          (fun leaf => pure (.yield (state.1, state.2.1,
            some ⟨same leaf.key state.2.1.key, true, state.1, index,
              BitmapIndex.fromHash state.2.1, top, state.2.1⟩)))
          (fun child => do
            let childNode ← readNode child
            let childData ← heapVectorOps.copy childNode.data
            let childCopy ← HAMT.inner childData childNode.bitmap
            let parentData ← nodeData state.1
            heapVectorOps.set parentData index (.trie childCopy)
            let nextTrie ← pure childCopy
            pure (.yield (nextTrie, next runtime state.2.1, state.2.2)))
      else pure (.yield (state.1, state.2.1,
          some ⟨true, false, state.1, index, BitmapIndex.fromHash state.2.1, top, state.2.1⟩))
    else pure (.done (state.1, state.2.1, state.2.2))

def persistentCollisionCopiedHeap : HamtHeap PersistentCollisionKey Unit :=
  ⟨[[some (.leaf ⟨.unsignedWord, ()⟩)], [some (.leaf ⟨.unsignedWord, ()⟩)]],
    [⟨0, 1⟩, ⟨1, 1⟩]⟩

def persistentCollisionQueryHash : HashState PersistentCollisionKey :=
  HashState.fromKey persistentCollisionRuntime .signedWord

def persistentCollisionPathResult : PathResult PersistentCollisionKey Unit :=
  ⟨false, true, 1, 1, ⟨0⟩, 1, persistentCollisionQueryHash⟩

theorem persistentCollisionCopyStep :
    runHamt (persistentPathCopyStep persistentCollisionEq persistentCollisionRuntime 1 ()
      (1, persistentCollisionQueryHash, none)) persistentCollisionCopiedHeap =
    (.ok (.yield (1, persistentCollisionQueryHash, some persistentCollisionPathResult)),
      persistentCollisionCopiedHeap) := rfl

theorem persistentCollisionCopyLoop :
    runHamt (Lean.Loop.forIn (m := HamtM PersistentCollisionKey Unit)
      (β := Nat × HashState PersistentCollisionKey × Option (PathResult PersistentCollisionKey Unit))
      ({} : Lean.Loop) (1, persistentCollisionQueryHash, none)
      (persistentPathCopyStep persistentCollisionEq persistentCollisionRuntime 1))
      persistentCollisionCopiedHeap =
    (.ok (1, persistentCollisionQueryHash, some persistentCollisionPathResult),
      persistentCollisionCopiedHeap) := by
  rw [persistentHamtLoopRun, persistentCollisionCopyStep]
  dsimp only
  exact persistentHamtLoopRun (1, persistentCollisionQueryHash, some persistentCollisionPathResult)
    (persistentPathCopyStep persistentCollisionEq persistentCollisionRuntime 1)
    persistentCollisionCopiedHeap

theorem persistentCollisionCopyPath :
    runHamt (path heapVectorOps persistentCollisionEq persistentCollisionRuntime 0
      persistentCollisionQueryHash true) persistentCollisionHeap =
    (.ok persistentCollisionPathResult, persistentCollisionCopiedHeap) := by
  rw [path.eq_1]
  simp only [ite_true]
  let copied : HamtHeap PersistentCollisionKey Unit :=
    ⟨[[some (.leaf ⟨.unsignedWord, ()⟩)], [some (.leaf ⟨.unsignedWord, ()⟩)]], [⟨0, 1⟩]⟩
  have hread : runHamt (readNode 0) persistentCollisionHeap =
      (.ok ⟨0, 1⟩, persistentCollisionHeap) := rfl
  have hcopy : runHamt (heapVectorOps.copy 0) persistentCollisionHeap = (.ok 1, copied) := rfl
  have hinner : runHamt (HAMT.inner 1 1) copied =
      (.ok 1, persistentCollisionCopiedHeap) := rfl
  rw [persistentHamtBindRun]
  simp only [hread]
  rw [persistentHamtBindRun]
  simp only [hcopy]
  rw [persistentHamtBindRun]
  simp only [hinner]
  simp only [ForIn.forIn]
  have hloop := persistentCollisionCopyLoop
  unfold persistentPathCopyStep at hloop
  unfold path.match_1 path.match_3
  rw [persistentHamtBindRun]
  rw [hloop] <;> rfl

theorem persistentCollisionDepthZero :
    HashState.fromOtherAtDepth persistentCollisionRuntime persistentCollisionQueryHash
      PersistentCollisionKey.unsignedWord =
      HashState.fromKey persistentCollisionRuntime PersistentCollisionKey.unsignedWord := by
  unfold HashState.fromOtherAtDepth
  simp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

theorem persistentCollisionInsertAction :
    insert! heapVectorOps persistentCollisionRuntime false true 1 1 ⟨0⟩
      persistentCollisionQueryHash () persistentCollisionCopiedHeap =
    some (.error .perfectHashCollision, persistentCollisionCopiedHeap) := by
  have hread : runHamt (readNode 1) persistentCollisionCopiedHeap =
      (.ok ⟨1, 1⟩, persistentCollisionCopiedHeap) := rfl
  have hget : runHamt (heapVectorOps.get 1 1) persistentCollisionCopiedHeap =
      (.ok (.leaf ⟨PersistentCollisionKey.unsignedWord, ()⟩), persistentCollisionCopiedHeap) := rfl
  unfold insert!
  simp only [Bool.false_eq_true, ite_false, Bool.not_true]
  rw [persistentHamtBindRun, hread]
  dsimp only
  rw [persistentHamtBindRun, hget]
  dsimp only
  have hpure : runHamt (pure (Leaf.mk PersistentCollisionKey.unsignedWord ()))
      persistentCollisionCopiedHeap =
      (.ok ⟨PersistentCollisionKey.unsignedWord, ()⟩, persistentCollisionCopiedHeap) := rfl
  rw [persistentHamtBindRun, hpure]
  dsimp only
  rw [persistentCollisionDepthZero]
  rfl

theorem persistentCollisionWrappedPath :
    (round2.hamtOps persistentCollisionEq persistentCollisionRuntime).path
      persistentCollisionDict.trie persistentCollisionQueryHash true =
    ⟨false, true, .ok (persistentCollisionCopiedHeap, 1), 1, 0,
      .ok (persistentCollisionCopiedHeap, 1), persistentCollisionQueryHash⟩ := by
  have hrun : round2.runTrie persistentCollisionDict.trie
      (fun root => path heapVectorOps persistentCollisionEq persistentCollisionRuntime root
        persistentCollisionQueryHash true) =
      .ok (persistentCollisionPathResult, persistentCollisionCopiedHeap) := by
    simp only [persistentCollisionDict, round2.runTrie]
    rw [persistentCollisionCopyPath]
  simp only [round2.hamtOps]
  rw [hrun]
  rfl

theorem persistentCollisionWrappedInsert :
    (round2.hamtOps persistentCollisionEq persistentCollisionRuntime).insert
      (.ok (persistentCollisionCopiedHeap, 1)) (.ok (persistentCollisionCopiedHeap, 1))
      false true 1 0 persistentCollisionQueryHash () = some (.error .thrownDict) := by
  simp only [round2.hamtOps, round2.runPartialAt, runPartialHamt]
  rw [persistentCollisionInsertAction]
  rfl

theorem persistentCollisionSetError :
    persistentSetTyped (round2.hamtOps persistentCollisionEq persistentCollisionRuntime)
      persistentCollisionDict .signedWord () = some (.error .thrownDict) := by
  unfold persistentSetTyped JuliaLean.base.dict.persistentInsert
  change ((round2.hamtOps persistentCollisionEq persistentCollisionRuntime).insert
      ((round2.hamtOps persistentCollisionEq persistentCollisionRuntime).path
        persistentCollisionDict.trie persistentCollisionQueryHash true).top
      ((round2.hamtOps persistentCollisionEq persistentCollisionRuntime).path
        persistentCollisionDict.trie persistentCollisionQueryHash true).trie
      ((round2.hamtOps persistentCollisionEq persistentCollisionRuntime).path
        persistentCollisionDict.trie persistentCollisionQueryHash true).found
      ((round2.hamtOps persistentCollisionEq persistentCollisionRuntime).path
        persistentCollisionDict.trie persistentCollisionQueryHash true).present
      ((round2.hamtOps persistentCollisionEq persistentCollisionRuntime).path
        persistentCollisionDict.trie persistentCollisionQueryHash true).index
      ((round2.hamtOps persistentCollisionEq persistentCollisionRuntime).path
        persistentCollisionDict.trie persistentCollisionQueryHash true).bitmapIndex
      ((round2.hamtOps persistentCollisionEq persistentCollisionRuntime).path
        persistentCollisionDict.trie persistentCollisionQueryHash true).state ()).map
        (Except.map PersistentDict.mk) = _
  rw [persistentCollisionWrappedPath]
  dsimp only
  rw [persistentCollisionWrappedInsert]
  rfl

/-- The exact frozen concrete-HAMT target is false on two constructible scalar
keys with the same identity word; the accompanying Julia script checks both. -/
theorem DictsPersistentdictNothrow_refuted :
    ¬ JuliaLean.Proofs.base.dict.round2.PersistentSetNothrow := by
  intro h
  obtain ⟨d', hd⟩ := h PersistentCollisionKey Unit persistentCollisionEq
    persistentCollisionRuntime persistentCollisionKeyLaws persistentCollisionDict
    [(.unsignedWord, ())] persistentCollisionRep .signedWord ()
  rw [persistentCollisionSetError] at hd
  cases hd

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: SharedHamt.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt

/-! An independently specified finite tree in the frozen HAMT heap. The pair
list is obtained structurally from the leaves, including each subtree in vector
order. Bitmap and vector-size agreement support checked slot-rank reasoning.
The relation places no requirement on the result of a subject operation. -/

mutual
  inductive TrieRep {K V : Type} (heap : HamtHeap K V) :
      Nat → List (K × V) → Prop where
    | node {root : Nat} {node : HAMTNode K V}
        {slots : List (Option (Entry K V))} {pairs : List (K × V)}
        (hnode : heap.nodes[root]? = some node)
        (hslots : heap.vectors[node.data]? = some slots)
        (hbitmap : node.bitmap < 2 ^ 32)
        (hcount : countOnes 32 node.bitmap = slots.length)
        (hentries : EntriesRep heap slots pairs) :
        TrieRep heap root pairs

  inductive EntriesRep {K V : Type} (heap : HamtHeap K V) :
      List (Option (Entry K V)) → List (K × V) → Prop where
    | nil : EntriesRep heap [] []
    | leaf {leaf : Leaf K V} {rest : List (Option (Entry K V))}
        {pairs : List (K × V)} (hrest : EntriesRep heap rest pairs) :
        EntriesRep heap (some (.leaf leaf) :: rest) ((leaf.key, leaf.val) :: pairs)
    | trie {child : Nat} {rest : List (Option (Entry K V))}
        {childPairs restPairs : List (K × V)}
        (hchild : TrieRep heap child childPairs)
        (hrest : EntriesRep heap rest restPairs) :
        EntriesRep heap (some (.trie child) :: rest) (childPairs ++ restPairs)
end

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: PathSafetyWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict JuliaLean.base.hamt

theorem pathCountOnesZero : ∀ n, countOnes n 0 = 0
  | 0 => rfl
  | n + 1 => by
      change 0 + countOnes n 0 = 0
      rw [pathCountOnesZero n]

/-- The rank of a present bit is within the number of present bitmap bits. -/
theorem pathCountOnesPrefixLe : ∀ (n x i : Nat),
    i < n → Nat.testBit x i = true →
      countOnes n (x &&& (2 ^ i - 1)) + 1 ≤ countOnes n x := by
  intro n
  induction n with
  | zero => intro x i hi; omega
  | succ n ih =>
    intro x i hi hbit
    cases i with
    | zero =>
      have hx : x % 2 = 1 := by simpa only [Nat.testBit_zero, decide_eq_true_eq] using hbit
      simp only [Nat.pow_zero, Nat.sub_self, Nat.and_zero]
      rw [pathCountOnesZero]
      change 0 + 1 ≤ x % 2 + countOnes n (x / 2)
      rw [hx]
      omega
    | succ i =>
      have hbit' : Nat.testBit (x / 2) i = true := by
        simpa only [Nat.testBit_succ] using hbit
      have hi' : i < n := by omega
      have hmaskOdd : (2 ^ (i + 1) - 1) % 2 = 1 := by
        rw [Nat.two_pow_sub_one_mod_two]
        exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow' i)
      have hlow : (x &&& (2 ^ (i + 1) - 1)) % 2 = x % 2 := by
        rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx1
        · have hnotOne : (x &&& (2 ^ (i + 1) - 1)) % 2 ≠ 1 := by
            intro h
            have hboth := Nat.and_mod_two_eq_one.mp h
            omega
          rcases Nat.mod_two_eq_zero_or_one (x &&& (2 ^ (i + 1) - 1)) with hzero | hone
          · omega
          · exact (hnotOne hone).elim
        · have hland := Nat.and_mod_two_eq_one.mpr ⟨hx1, hmaskOdd⟩
          omega
      have hmaskDiv : (2 ^ (i + 1) - 1) / 2 = 2 ^ i - 1 := by
        rw [Nat.pow_succ]
        omega
      have hquot : (x &&& (2 ^ (i + 1) - 1)) / 2 = (x / 2) &&& (2 ^ i - 1) := by
        rw [Nat.and_div_two, hmaskDiv]
      simp only [countOnes, hlow, hquot]
      have htail := ih (x / 2) i hi' hbit'
      omega

theorem pathBitmapIndex_lt {K : Type} (hash : HashState K) :
    (BitmapIndex.fromHash hash).x < 32 := by
  exact Nat.and_lt_two_pow _ (by decide : LEVEL_MASK < 2 ^ 5)

theorem pathNextKey {K : Type} (runtime : HamtObjectIdRuntime K) (hash : HashState K) :
    (next runtime hash).key = hash.key := by
  unfold next
  dsimp only
  split <;> rfl

def pathReadIndex {K V : Type} (node : HAMTNode K V) (hash : HashState K) : Nat :=
  countOnes 32 (Nat.land node.bitmap
    (shiftLeftNat 1 (BitmapIndex.fromHash hash).x - 1)) + 1

theorem pathReadNodeRun {K V : Type} (heap : HamtHeap K V) (root : Nat)
    (node : HAMTNode K V) (hn : heap.nodes[root]? = some node) :
    runHamt (readNode root) heap = (.ok node, heap) := by
  have hget : runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := rfl
  unfold readNode
  rw [persistentHamtBindRun, hget]
  dsimp only
  rw [hn]
  rfl

theorem pathVectorSlotsRun {K V : Type} (heap : HamtHeap K V) (data : Nat)
    (slots : List (Option (Entry K V))) (hs : heap.vectors[data]? = some slots) :
    runHamt (heapVectorSlots data) heap = (.ok slots, heap) := by
  have hget : runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := rfl
  unfold heapVectorSlots
  rw [persistentHamtBindRun, hget]
  dsimp only
  rw [hs]
  rfl

theorem pathVectorGetRun {K V : Type} (heap : HamtHeap K V) (data : Nat)
    (slots : List (Option (Entry K V))) (index : Nat) (entry : Entry K V)
    (hs : heap.vectors[data]? = some slots) (hi : 1 ≤ index)
    (he : slots[index - 1]? = some (some entry)) :
    runHamt (heapVectorOps.get data index) heap = (.ok entry, heap) := by
  change runHamt (heapVectorGet data index) heap = _
  unfold heapVectorGet
  rw [persistentHamtBindRun, pathVectorSlotsRun heap data slots hs]
  dsimp only
  rw [ite_eq_right (show index ≠ 0 by omega), he]
  rfl

theorem pathReadIndexRun {K V : Type} (heap : HamtHeap K V) (root : Nat)
    (node : HAMTNode K V) (hash : HashState K) (hn : heap.nodes[root]? = some node) :
    runHamt (entry_index root (BitmapIndex.fromHash hash)) heap =
      (.ok (pathReadIndex node hash), heap) := by
  unfold entry_index nodeBitmap
  rw [persistentHamtBindRun, persistentHamtBindRun, pathReadNodeRun heap root node hn]
  rfl

theorem pathIssetRun {K V : Type} (heap : HamtHeap K V) (root : Nat)
    (node : HAMTNode K V) (hash : HashState K) (hn : heap.nodes[root]? = some node) :
    runHamt (isset root (BitmapIndex.fromHash hash)) heap =
      (.ok (Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x), heap) := by
  unfold isset nodeBitmap
  rw [persistentHamtBindRun, persistentHamtBindRun, pathReadNodeRun heap root node hn]
  change (Except.ok ((node.bitmap / 2 ^ (BitmapIndex.fromHash hash).x) % 2 == 1), heap) = _
  rw [Bool.beq_eq_decide_eq, ← Nat.testBit_eq_decide_div_mod_eq]

def PathTerminal {K V : Type} (same : K → K → Bool) (heap : HamtHeap K V)
    (query : K) (pairs : List (K × V)) (result : PathResult K V) : Prop :=
  result.present = true →
    ∃ (leaf : Leaf K V) (node : HAMTNode K V) (slots : List (Option (Entry K V))),
      heap.nodes[result.trie]? = some node ∧ heap.vectors[node.data]? = some slots ∧
      1 ≤ result.index ∧ slots[result.index - 1]? = some (some (.leaf leaf)) ∧
      result.found = same leaf.key query ∧ (leaf.key, leaf.val) ∈ pairs

def PathLoopWitness {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : Nat)
    (hash : HashState K) (pairs : List (K × V)) : Prop :=
  ∃ last finalHash result,
    runHamt (Lean.Loop.forIn (m := HamtM K V)
      (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
      (current, hash, none) (persistentPathReadStep same runtime top)) heap =
      (.ok (last, finalHash, some result), heap) ∧
    PathTerminal same heap hash.key pairs result

theorem pathTerminal_mono {K V : Type} {same : K → K → Bool} {heap : HamtHeap K V}
    {query : K} {pairs more : List (K × V)} {result : PathResult K V}
    (ht : PathTerminal same heap query pairs result)
    (hm : ∀ p, p ∈ pairs → p ∈ more) : PathTerminal same heap query more result := by
  intro hp
  obtain ⟨leaf, node, slots, hn, hs, hi, he, hf, hmem⟩ := ht hp
  exact ⟨leaf, node, slots, hn, hs, hi, he, hf, hm _ hmem⟩

theorem pathLoopWitness_mono {K V : Type} {same : K → K → Bool}
    {runtime : HamtObjectIdRuntime K} {heap : HamtHeap K V} {top current : Nat}
    {hash : HashState K} {pairs more : List (K × V)}
    (hw : PathLoopWitness same runtime heap top current hash pairs)
    (hm : ∀ p, p ∈ pairs → p ∈ more) :
    PathLoopWitness same runtime heap top current hash more := by
  obtain ⟨last, finalHash, result, hr, ht⟩ := hw
  exact ⟨last, finalHash, result, hr, pathTerminal_mono ht hm⟩

def EntryPathProperty {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top : Nat)
    (pairs : List (K × V)) : Entry K V → Prop
  | .leaf leaf => (leaf.key, leaf.val) ∈ pairs
  | .trie child => ∀ hash, PathLoopWitness same runtime heap top child hash pairs

theorem entryPathProperty_mono {K V : Type} {same : K → K → Bool}
    {runtime : HamtObjectIdRuntime K} {heap : HamtHeap K V} {top : Nat}
    {pairs more : List (K × V)} {entry : Entry K V}
    (he : EntryPathProperty same runtime heap top pairs entry)
    (hm : ∀ p, p ∈ pairs → p ∈ more) :
    EntryPathProperty same runtime heap top more entry := by
  cases entry with
  | leaf leaf => exact hm _ he
  | trie child => exact fun hash => pathLoopWitness_mono (he hash) hm

theorem pathReadStep_present {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : Nat)
    (hash : HashState K) (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (entry : Entry K V) (hn : heap.nodes[current]? = some node)
    (hs : heap.vectors[node.data]? = some slots)
    (he : slots[pathReadIndex node hash - 1]? = some (some entry))
    (hb : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true) :
    runHamt (persistentPathReadStep same runtime top () (current, hash, none)) heap =
      (.ok (.yield (match entry with
        | .leaf leaf => (current, hash, some ⟨same leaf.key hash.key, true, current,
            pathReadIndex node hash, BitmapIndex.fromHash hash, top, hash⟩)
        | .trie child => (child, next runtime hash, none))), heap) := by
  simp only [persistentPathReadStep, Option.isNone, ite_true]
  rw [persistentHamtBindRun, pathReadIndexRun heap current node hash hn]
  dsimp only
  rw [persistentHamtBindRun, pathIssetRun heap current node hash hn]
  simp only [hb, ite_true]
  rw [persistentHamtBindRun, pathReadNodeRun heap current node hn]
  dsimp only
  rw [persistentHamtBindRun,
    pathVectorGetRun heap node.data slots (pathReadIndex node hash) entry hs
      (Nat.le_add_left 1 _) he]
  cases entry <;> rfl

theorem pathReadStep_absent {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : Nat)
    (hash : HashState K) (node : HAMTNode K V) (hn : heap.nodes[current]? = some node)
    (hb : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = false) :
    runHamt (persistentPathReadStep same runtime top () (current, hash, none)) heap =
      (.ok (.yield (current, hash, some ⟨true, false, current,
        pathReadIndex node hash, BitmapIndex.fromHash hash, top, hash⟩)), heap) := by
  simp only [persistentPathReadStep, Option.isNone, ite_true]
  rw [persistentHamtBindRun, pathReadIndexRun heap current node hash hn]
  dsimp only
  rw [persistentHamtBindRun, pathIssetRun heap current node hash hn]
  simp only [hb, Bool.false_eq_true, ite_false]
  rfl

theorem pathReadLoop_terminal {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : Nat)
    (hash : HashState K) (result : PathResult K V)
    (hs : runHamt (persistentPathReadStep same runtime top () (current, hash, none)) heap =
      (.ok (.yield (current, hash, some result)), heap)) :
    runHamt (Lean.Loop.forIn (m := HamtM K V)
      (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
      (current, hash, none) (persistentPathReadStep same runtime top)) heap =
      (.ok (current, hash, some result), heap) := by
  rw [persistentHamtLoopRun, hs]
  dsimp only
  exact persistentHamtLoopRun (current, hash, some result)
    (persistentPathReadStep same runtime top) heap

/-- Every non-copying path in an independently described finite heap terminates,
keeps the heap unchanged and can report a present result only at a defined leaf. -/
theorem trieRep_pathLoop {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top : Nat)
    {root : Nat} {pairs : List (K × V)} (hr : TrieRep heap root pairs) :
    ∀ hash, PathLoopWitness same runtime heap top root hash pairs := by
  let motiveNode := fun (root : Nat) (pairs : List (K × V)) (_ : TrieRep heap root pairs) =>
    ∀ hash, PathLoopWitness same runtime heap top root hash pairs
  let motiveEntries := fun (slots : List (Option (Entry K V))) (pairs : List (K × V))
      (_ : EntriesRep heap slots pairs) =>
    ∀ i, i < slots.length → ∃ entry, slots[i]? = some (some entry) ∧
      EntryPathProperty same runtime heap top pairs entry
  have hrec : motiveNode root pairs hr := by
    refine TrieRep.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hr
    · intro root node slots pairs hn hs _hb hc he ih hash
      cases hbit : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x with
      | false =>
        let result : PathResult K V := ⟨true, false, root, pathReadIndex node hash,
          BitmapIndex.fromHash hash, top, hash⟩
        refine ⟨root, hash, result,
          pathReadLoop_terminal same runtime heap top root hash result
            (pathReadStep_absent same runtime heap top root hash node hn hbit), ?_⟩
        intro hp
        cases hp
      | true =>
        have hidx : 1 ≤ pathReadIndex node hash := Nat.le_add_left 1 _
        have hbound : pathReadIndex node hash ≤ slots.length := by
          unfold pathReadIndex shiftLeftNat
          rw [Nat.one_mul, ← hc]
          exact pathCountOnesPrefixLe 32 node.bitmap (BitmapIndex.fromHash hash).x
            (pathBitmapIndex_lt hash) hbit
        obtain ⟨entry, hentry, hproperty⟩ := ih (pathReadIndex node hash - 1) (by omega)
        have hstep := pathReadStep_present same runtime heap top root hash node slots entry
          hn hs hentry hbit
        cases entry with
        | leaf leaf =>
          let result : PathResult K V := ⟨same leaf.key hash.key, true, root,
            pathReadIndex node hash, BitmapIndex.fromHash hash, top, hash⟩
          refine ⟨root, hash, result,
            pathReadLoop_terminal same runtime heap top root hash result hstep, ?_⟩
          intro _
          exact ⟨leaf, node, slots, hn, hs, hidx, hentry, rfl, hproperty⟩
        | trie child =>
          obtain ⟨last, finalHash, result, hloop, ht⟩ := hproperty (next runtime hash)
          refine ⟨last, finalHash, result, ?_, ?_⟩
          · rw [persistentHamtLoopRun, hstep]
            exact hloop
          · simpa only [pathNextKey] using ht
    · intro i hi
      cases hi
    · intro leaf rest pairs hr ih i hi
      cases i with
      | zero => exact ⟨.leaf leaf, rfl, List.mem_cons_self⟩
      | succ i =>
        obtain ⟨entry, he, hp⟩ := ih i (by
          simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)
        exact ⟨entry, he, entryPathProperty_mono hp
          (fun p hp => List.mem_cons_of_mem _ hp)⟩
    · intro child rest childPairs restPairs hc hr ihc ihr i hi
      cases i with
      | zero =>
        refine ⟨.trie child, rfl, fun hash => ?_⟩
        exact pathLoopWitness_mono (ihc hash) (fun p hp => List.mem_append_left _ hp)
      | succ i =>
        obtain ⟨entry, he, hp⟩ := ihr i (by
          simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)
        exact ⟨entry, he, entryPathProperty_mono hp
          (fun p hp => List.mem_append_right _ hp)⟩
  exact hrec

theorem trieRep_pathRun {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V)
    {root : Nat} {pairs : List (K × V)} (hr : TrieRep heap root pairs)
    (hash : HashState K) :
    ∃ result, runHamt (path heapVectorOps same runtime root hash false) heap =
        (.ok result, heap) ∧ PathTerminal same heap hash.key pairs result := by
  obtain ⟨last, finalHash, result, hloop, ht⟩ := trieRep_pathLoop same runtime heap root hr hash
  refine ⟨result, ?_, ht⟩
  rw [path.eq_1]
  simp only [Bool.false_eq_true, ite_false, ForIn.forIn]
  change runHamt (do
    let final ← Lean.Loop.forIn (m := HamtM K V)
      (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
      (root, hash, none) (persistentPathReadStep same runtime root)
    match final.2.2 with
    | some r => pure r
    | none => throw HamtError.bounds) heap = _
  rw [persistentHamtBindRun, hloop]
  rfl

/-- The entire frozen path-safety conclusion follows from a structural finite
heap representation and independently stated uniqueness of the reference map. -/
theorem persistentPathSafe_of_trieRep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (heap : HamtHeap K V) (root : Nat) (pairs reference : List (K × V))
    (hr : TrieRep heap root pairs) (hd : Distinct same reference)
    (hperm : List.Perm pairs reference) (key : K) :
    ∃ (pr : PathResult K V) (after : HamtHeap K V),
      round2.runTrie (.ok (heap, root)) (fun root =>
        path heapVectorOps same runtime root (HashState.fromKey runtime key) false) =
          .ok (pr, after) ∧
      ((pr.found && pr.present) = true →
        ∃ leaf : Leaf K V,
          round2.runTrie (.ok (after, pr.trie)) (fun t => do
            let node ← readNode t
            heapVectorOps.get node.data pr.index) = .ok (.leaf leaf, after) ∧
          same leaf.key key = true ∧ rlookup same reference key = some leaf.val) := by
  obtain ⟨result, hrun, ht⟩ := trieRep_pathRun same runtime heap hr (HashState.fromKey runtime key)
  refine ⟨result, heap, ?_, ?_⟩
  · unfold round2.runTrie
    dsimp only
    rw [hrun]
  · intro hfp
    have hp := Bool.and_eq_true_iff.mp hfp
    obtain ⟨leaf, node, slots, hn, hs, hi, he, hf, hm⟩ := ht hp.2
    have heq : same leaf.key key = true := hf.symm.trans hp.1
    have hfind := rfind_of_mem hl.query hd (hperm.mem_iff.1 hm) (hl.symm leaf.key key heq)
    refine ⟨leaf, ?_, heq, ?_⟩
    · have hread : runHamt (do
          let node ← readNode result.trie
          heapVectorOps.get node.data result.index) heap = (.ok (.leaf leaf), heap) := by
        rw [persistentHamtBindRun, pathReadNodeRun heap result.trie node hn]
        exact pathVectorGetRun heap node.data slots result.index (.leaf leaf) hs hi he
      unfold round2.runTrie
      dsimp only
      rw [hread]
    · unfold rlookup
      rw [hfind]
      rfl

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: SingletonWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict JuliaLean.base.hamt

/-- The first five identity-hash bits select the singleton root slot. -/
def singletonHashSlot {K : Type} (runtime : HamtObjectIdRuntime K) (key : K) : Nat :=
  Nat.land (runtime.objectid key).val.toNat LEVEL_MASK

/-- Exact heap allocated by the one-pair HAMT constructor. -/
def singletonHeap {K V : Type} (runtime : HamtObjectIdRuntime K) (key : K) (value : V) :
    HamtHeap K V :=
  ⟨[[some (.leaf ⟨key, value⟩)]], [⟨0, u32 (2 ^ singletonHashSlot runtime key)⟩]⟩

def singletonDict {K V : Type} (runtime : HamtObjectIdRuntime K) (key : K) (value : V) :
    PersistentDict K V (round2.PTrie K V) :=
  ⟨.ok (singletonHeap runtime key value, 0)⟩

theorem singletonConstructorRun {K V : Type} (runtime : HamtObjectIdRuntime K)
    (key : K) (value : V) :
    runHamt (HAMT.typedPairConstructor heapVectorOps runtime (key, value)) HamtHeap.empty =
      (.ok 0, singletonHeap runtime key value) := by
  simp [singletonHeap, singletonHashSlot, runHamt, HAMT.typedPairConstructor, init_hamt,
    HashState.fromKey, BitmapIndex.fromHash, set!, heapVectorOps, heapVectorAllocate,
    heapVectorSet, readNode, shiftLeftNat, shiftRightNat, HamtHeap.empty,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, StateT.map, Functor.map,
    getThe, liftM, monadLift, MonadLift.monadLift, ExceptT.run, ExceptT.bind, ExceptT.pure,
    ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.run, StateT.bind, StateT.pure,
    StateT.get, StateT.set, Bind.bind, Pure.pure]

theorem singletonConstructor {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V) :
    persistentSingleton (round2.hamtOps same runtime) key value =
      .ok (singletonDict runtime key value) := by
  unfold persistentSingleton
  change ((match runHamt (HAMT.typedPairConstructor heapVectorOps runtime (key, value))
      HamtHeap.empty with
    | (.ok root, heap) => (Except.ok (Except.ok (heap, root)) : DictResult (round2.PTrie K V))
    | (.error e, _) => .error (round2.hamtThrow e)) >>= fun trie =>
      Except.ok (PersistentDict.mk trie)) = _
  rw [singletonConstructorRun]
  rfl

theorem singletonRepresentation {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V) :
    round2.PRep (round2.hamtOps same runtime) same (singletonDict runtime key value)
      [(key, value)] :=
  .singleton (singletonConstructor same runtime key value)

theorem singletonHashSlot_lt {K : Type} (runtime : HamtObjectIdRuntime K) (key : K) :
    singletonHashSlot runtime key < 32 := by
  have hlevel : LEVEL_MASK < 2 ^ 5 := by decide
  exact Nat.and_lt_two_pow _ hlevel

theorem singletonBitmap {K : Type} (runtime : HamtObjectIdRuntime K) (key : K) :
    u32 (2 ^ singletonHashSlot runtime key) = 2 ^ singletonHashSlot runtime key := by
  unfold u32
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (singletonHashSlot_lt runtime key))

theorem singletonBitmap_ne_zero {K : Type} (runtime : HamtObjectIdRuntime K) (key : K) :
    u32 (2 ^ singletonHashSlot runtime key) ≠ 0 := by
  rw [singletonBitmap]
  exact Nat.ne_of_gt (Nat.two_pow_pos _)

theorem singletonLevelNotEmpty {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V) :
    (round2.hamtOps same runtime).isLevelEmpty (singletonDict runtime key value).trie = false := by
  change (u32 (2 ^ singletonHashSlot runtime key) == 0) = false
  exact beq_eq_false_iff_ne.mpr (singletonBitmap_ne_zero runtime key)

theorem singletonCountOnesZero : ∀ n, countOnes n 0 = 0
  | 0 => rfl
  | n + 1 => by
    change 0 + countOnes n 0 = 0
    rw [singletonCountOnesZero n]


theorem singletonBitTest (x y : Nat) :
    ((2 ^ x / 2 ^ y) % 2 == 1) = decide (x = y) := by
  rw [Bool.beq_eq_decide_eq, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_two_pow]

def singletonQueryIndex {K : Type} (runtime : HamtObjectIdRuntime K) (key query : K) : Nat :=
  countOnes 32 (Nat.land (2 ^ singletonHashSlot runtime key)
    (2 ^ singletonHashSlot runtime query - 1)) + 1

theorem singletonQueryIndex_same {K : Type} (runtime : HamtObjectIdRuntime K) (key query : K)
    (hs : singletonHashSlot runtime key = singletonHashSlot runtime query) :
    singletonQueryIndex runtime key query = 1 := by
  unfold singletonQueryIndex
  rw [hs]
  have hmask : Nat.land (2 ^ singletonHashSlot runtime query)
      (2 ^ singletonHashSlot runtime query - 1) = 0 :=
    (Nat.and_two_pow_sub_one_eq_mod _ _).trans (Nat.mod_self _)
  rw [hmask, singletonCountOnesZero]

theorem singletonReadNodeRun {K V : Type} (runtime : HamtObjectIdRuntime K)
    (key : K) (value : V) :
    runHamt (readNode 0) (singletonHeap runtime key value) =
      (.ok ⟨0, u32 (2 ^ singletonHashSlot runtime key)⟩, singletonHeap runtime key value) := rfl

theorem singletonGetRun {K V : Type} (runtime : HamtObjectIdRuntime K)
    (key : K) (value : V) :
    runHamt (heapVectorOps.get 0 1) (singletonHeap runtime key value) =
      (.ok (.leaf ⟨key, value⟩), singletonHeap runtime key value) := rfl

theorem singletonIndexRun {K V : Type} (runtime : HamtObjectIdRuntime K)
    (key : K) (value : V) (query : K) :
    runHamt (entry_index 0 (BitmapIndex.fromHash (HashState.fromKey runtime query)))
      (singletonHeap runtime key value) =
      (.ok (singletonQueryIndex runtime key query), singletonHeap runtime key value) := by
  change ((Except.ok (countOnes 32 (Nat.land (u32 (2 ^ singletonHashSlot runtime key))
    (shiftLeftNat 1 (BitmapIndex.fromHash (HashState.fromKey runtime query)).x - 1)) + 1) :
      Except HamtError Nat),
      singletonHeap runtime key value) = _
  rw [singletonBitmap]
  simp only [BitmapIndex.fromHash, HashState.fromKey, shiftRightNat, Nat.pow_zero,
    Nat.div_one, shiftLeftNat, Nat.one_mul]
  rfl

theorem singletonIssetRun {K V : Type} (runtime : HamtObjectIdRuntime K)
    (key : K) (value : V) (query : K) :
    runHamt (isset 0 (BitmapIndex.fromHash (HashState.fromKey runtime query)))
      (singletonHeap runtime key value) =
      (.ok (decide (singletonHashSlot runtime key = singletonHashSlot runtime query)),
        singletonHeap runtime key value) := by
  change ((Except.ok ((shiftRightNat (u32 (2 ^ singletonHashSlot runtime key))
    (BitmapIndex.fromHash (HashState.fromKey runtime query)).x) % 2 == 1) : Except HamtError Bool),
      singletonHeap runtime key value) = _
  rw [singletonBitmap]
  simp only [BitmapIndex.fromHash, HashState.fromKey, shiftRightNat, Nat.pow_zero, Nat.div_one]
  rw [singletonBitTest]
  rfl

def singletonQueryResult {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key query : K) : PathResult K V :=
  if singletonHashSlot runtime key = singletonHashSlot runtime query then
    ⟨same key query, true, 0, 1, BitmapIndex.fromHash (HashState.fromKey runtime query),
      0, HashState.fromKey runtime query⟩
  else
    ⟨true, false, 0, singletonQueryIndex runtime key query,
      BitmapIndex.fromHash (HashState.fromKey runtime query), 0, HashState.fromKey runtime query⟩


/-- Every singleton read path stops at the root, including a colliding query. -/
theorem singletonPathStep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V) (query : K) :
    runHamt (persistentPathReadStep same runtime 0 ()
      (0, HashState.fromKey runtime query, none)) (singletonHeap runtime key value) =
      (.ok (.yield (0, HashState.fromKey runtime query,
        some (singletonQueryResult same runtime key query))), singletonHeap runtime key value) := by
  simp only [persistentPathReadStep, Option.isNone, ite_true]
  rw [persistentHamtBindRun, singletonIndexRun]
  dsimp only
  rw [persistentHamtBindRun, singletonIssetRun]
  dsimp only
  by_cases hs : singletonHashSlot runtime key = singletonHashSlot runtime query
  · simp only [hs, decide_true, ite_true]
    rw [persistentHamtBindRun, singletonReadNodeRun]
    dsimp only
    rw [persistentHamtBindRun, singletonQueryIndex_same runtime key query hs, singletonGetRun]
    simp only [singletonQueryResult, hs, ite_true]
    rfl
  · simp only [hs, decide_false, Bool.false_eq_true, ite_false, singletonQueryResult]
    rfl

/-- Concrete no-copy traversal of the singleton heap, for an arbitrary query. -/
theorem singletonPathRun {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V) (query : K) :
    runHamt (path heapVectorOps same runtime 0 (HashState.fromKey runtime query) false)
      (singletonHeap runtime key value) =
      (.ok (singletonQueryResult same runtime key query), singletonHeap runtime key value) :=
  persistentPathReadRunOfStep same runtime 0 (HashState.fromKey runtime query)
    (singletonHeap runtime key value) (singletonHeap runtime key value) 0
    (HashState.fromKey runtime query) (singletonQueryResult same runtime key query)
    (singletonPathStep same runtime key value query)


theorem singletonRunTriePath {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V) (query : K) :
    round2.runTrie (singletonDict runtime key value).trie (fun root =>
      path heapVectorOps same runtime root (HashState.fromKey runtime query) false) =
      .ok (singletonQueryResult same runtime key query, singletonHeap runtime key value) := by
  dsimp only [round2.runTrie, singletonDict]
  rw [singletonPathRun]

theorem singletonWrappedPath {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V) (query : K) :
    (round2.hamtOps same runtime).path (singletonDict runtime key value).trie
      (HashState.fromKey runtime query) false =
      let pr := singletonQueryResult (V := V) same runtime key query
      ⟨pr.found, pr.present, .ok (singletonHeap runtime key value, pr.trie), pr.index,
        pr.bi.x, .ok (singletonHeap runtime key value, pr.top), pr.hash⟩ := by
  change (match round2.runTrie (singletonDict runtime key value).trie
      (fun root => path heapVectorOps same runtime root (HashState.fromKey runtime query) false) with
    | .ok (pr, heap) =>
        TriePath.mk (H := round2.PTrie K V) pr.found pr.present (.ok (heap, pr.trie)) pr.index pr.bi.x
          (.ok (heap, pr.top)) pr.hash
    | .error e => TriePath.mk (H := round2.PTrie K V) false false (.error e) 0 0 (.error e)
        (HashState.fromKey runtime query)) = _
  rw [singletonRunTriePath]

theorem singletonKeyGet {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (key : K) (value : V) (query : K) :
    persistentKeyGet (round2.hamtOps same runtime) (singletonDict runtime key value) query =
      rlookup same [(key, value)] query := by
  have hf := singletonLevelNotEmpty same runtime key value
  change (if (round2.hamtOps same runtime).isLevelEmpty (singletonDict runtime key value).trie then
      none
    else if ((round2.hamtOps same runtime).path (singletonDict runtime key value).trie
        (HashState.fromKey runtime query) false).found &&
      ((round2.hamtOps same runtime).path (singletonDict runtime key value).trie
        (HashState.fromKey runtime query) false).present then
      (round2.hamtOps same runtime).leafValue
        ((round2.hamtOps same runtime).path (singletonDict runtime key value).trie
          (HashState.fromKey runtime query) false).trie
        ((round2.hamtOps same runtime).path (singletonDict runtime key value).trie
          (HashState.fromKey runtime query) false).index
    else none) = _
  simp only [hf, Bool.false_eq_true, ite_false, singletonWrappedPath]
  by_cases hs : singletonHashSlot runtime key = singletonHashSlot runtime query
  · simp only [singletonQueryResult, hs, ite_true, Bool.and_true]
    change (if same key query then some value else none) = rlookup same [(key, value)] query
    have he : same key query = same query key := by
      cases h1 : same key query <;> cases h2 : same query key
      · rfl
      · have h3 := hl.symm query key h2
        rw [h1] at h3
        cases h3
      · have h3 := hl.symm key query h1
        rw [h2] at h3
        cases h3
      · rfl
    rw [he]
    cases hc : same query key <;>
      simp only [rlookup, rfind, List.find?_cons, hc, List.find?_nil,
        Option.map_none, Option.map_some, Bool.false_eq_true, ite_false, ite_true]
  · have he : same query key = false := by
      cases h : same query key
      · rfl
      · have hid := hl.hash_eq query key h
        have hslots : singletonHashSlot runtime key = singletonHashSlot runtime query := by
          unfold singletonHashSlot
          rw [hid]
        exact False.elim (hs hslots)
    simp only [singletonQueryResult, hs, ite_false]
    change none = rlookup same [(key, value)] query
    simp only [rlookup, rfind, List.find?_cons, he, Bool.false_eq_true, ite_false,
      List.find?_nil, Option.map_none]


/-- The full frozen path-safety conclusion for an arbitrary one-pair constructor. -/
theorem singletonPathSafety {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (key : K) (value : V) (query : K) :
    ∃ (pr : PathResult K V) (heap : HamtHeap K V),
      round2.runTrie (singletonDict runtime key value).trie (fun root =>
        path heapVectorOps same runtime root (HashState.fromKey runtime query) false) =
        .ok (pr, heap) ∧
      ((pr.found && pr.present) = true →
        ∃ leaf : Leaf K V,
          round2.runTrie (.ok (heap, pr.trie)) (fun t => do
            let node ← readNode t
            heapVectorOps.get node.data pr.index) = .ok (.leaf leaf, heap) ∧
          same leaf.key query = true ∧ rlookup same [(key, value)] query = some leaf.val) := by
  refine ⟨singletonQueryResult same runtime key query, singletonHeap runtime key value,
    singletonRunTriePath same runtime key value query, ?_⟩
  intro hfound
  by_cases hs : singletonHashSlot runtime key = singletonHashSlot runtime query
  · simp only [singletonQueryResult, hs, ite_true, Bool.and_true] at hfound ⊢
    refine ⟨⟨key, value⟩, rfl, hfound, ?_⟩
    have hsym := hl.symm key query hfound
    simp only [rlookup, rfind, List.find?_cons, hsym, ite_true, Option.map_some]
  · simp only [singletonQueryResult, hs, ite_false, Bool.and_false] at hfound
    cases hfound

/-- Pair membership is correct for every singleton and every comparison callback. -/
theorem singletonPairMembership {K V R : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (key : K) (value : V) (pair : K × V) (valcmp : V → V → DictResult R) :
    persistentIn (round2.hamtOps same runtime) valcmp (singletonDict runtime key value) pair =
      (match rlookup same [(key, value)] pair.1 with
        | none => .ok (.inl false)
        | some stored => .inr <$> valcmp pair.2 stored) :=
  round2.PersistentPairMembershipSemantics_of_keyGet pair valcmp
    (singletonKeyGet same runtime hl key value pair.1)

/-- All six lookup operations agree with the singleton reference map. -/
theorem singletonLookupSemantics {K V D : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (key : K) (value : V) (query : K) (default : D) (fallback : Unit → DictResult D) :
    persistentKeyGet (round2.hamtOps same runtime) (singletonDict runtime key value) query =
      rlookup same [(key, value)] query ∧
    persistentGetindex (round2.hamtOps same runtime) (singletonDict runtime key value) query =
      (match rlookup same [(key, value)] query with | some v => .ok v | none => .error .keyError) ∧
    persistentHasKey (round2.hamtOps same runtime) (singletonDict runtime key value) query =
      (rlookup same [(key, value)] query).isSome ∧
    persistentGet (round2.hamtOps same runtime) (singletonDict runtime key value) query default =
      (match rlookup same [(key, value)] query with | some v => .inl v | none => .inr default) ∧
    persistentGetDefault (round2.hamtOps same runtime) (singletonDict runtime key value) query fallback =
      (match rlookup same [(key, value)] query with | some v => .ok (.inl v) | none => .inr <$> fallback ()) ∧
    persistentGetTypedDefault (round2.hamtOps same runtime) (singletonDict runtime key value) query fallback =
      (match rlookup same [(key, value)] query with | some v => .ok (.inl v) | none => .inr <$> fallback ()) :=
  round2.PersistentLookupSemantics_of_keyGet default fallback
    (singletonKeyGet same runtime hl key value query)


/-- A bounded singleton bitmap contains exactly one set bit. -/
theorem singletonCountOnesPow (n p : Nat) (hp : p < n) :
    countOnes n (2 ^ p) = 1 := by
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    cases p with
    | zero =>
      change 1 + countOnes n 0 = 1
      rw [singletonCountOnesZero]
    | succ p =>
      simp only [countOnes, Nat.pow_succ, Nat.mul_mod_left,
        Nat.mul_div_cancel (2 ^ p) (by decide : 0 < 2),
        Nat.zero_add]
      exact ih p (by omega)

/-- The one-pair constructor satisfies the shared finite-tree relation. -/
theorem singletonTrieRep {K V : Type} (runtime : HamtObjectIdRuntime K)
    (key : K) (value : V) :
    TrieRep (singletonHeap runtime key value) 0 [(key, value)] := by
  refine .node (node := ⟨0, u32 (2 ^ singletonHashSlot runtime key)⟩)
    (slots := [some (.leaf ⟨key, value⟩)]) rfl rfl ?_ ?_ (.leaf .nil)
  · rw [singletonBitmap]
    exact Nat.pow_lt_pow_right (by decide) (singletonHashSlot_lt runtime key)
  · rw [singletonBitmap]
    exact singletonCountOnesPow 32 _ (singletonHashSlot_lt runtime key)

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: PersistentBridge.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Older node and vector records are unchanged after an allocation or a
mutation restricted to freshly copied records. -/
def PersistentHeapFrame {K V : Type} (base after : HamtHeap K V) : Prop :=
  (∀ i, i < base.nodes.length → after.nodes[i]? = base.nodes[i]?) ∧
  (∀ i, i < base.vectors.length → after.vectors[i]? = base.vectors[i]?)

theorem persistentHeapFrameRefl {K V : Type} (heap : HamtHeap K V) :
    PersistentHeapFrame heap heap := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem persistentHeapFrameLengths {K V : Type} {base after : HamtHeap K V}
    (h : PersistentHeapFrame base after) :
    base.nodes.length ≤ after.nodes.length ∧ base.vectors.length ≤ after.vectors.length := by
  constructor
  · by_cases hn : base.nodes.length ≤ after.nodes.length
    · exact hn
    have hi : after.nodes.length < base.nodes.length := by omega
    have heq := h.1 after.nodes.length hi
    have hnone : base.nodes[after.nodes.length]? = none := by
      rw [← heq]
      exact List.getElem?_eq_none_iff.mpr (Nat.le_refl _)
    have := List.getElem?_eq_none_iff.mp hnone
    omega
  · by_cases hn : base.vectors.length ≤ after.vectors.length
    · exact hn
    have hi : after.vectors.length < base.vectors.length := by omega
    have heq := h.2 after.vectors.length hi
    have hnone : base.vectors[after.vectors.length]? = none := by
      rw [← heq]
      exact List.getElem?_eq_none_iff.mpr (Nat.le_refl _)
    have := List.getElem?_eq_none_iff.mp hnone
    omega

theorem persistentHeapFrameTrans {K V : Type} {a b c : HamtHeap K V}
    (hab : PersistentHeapFrame a b) (hbc : PersistentHeapFrame b c) :
    PersistentHeapFrame a c := by
  have hlen := persistentHeapFrameLengths hab
  exact ⟨fun i hi => (hbc.1 i (Nat.lt_of_lt_of_le hi hlen.1)).trans (hab.1 i hi),
    fun i hi => (hbc.2 i (Nat.lt_of_lt_of_le hi hlen.2)).trans (hab.2 i hi)⟩

/-- A finite subtree and its independent pair list survive any later heap
whose older records have the same contents. -/
theorem persistentTrieRepFrame {K V : Type} {base after : HamtHeap K V}
    (hframe : PersistentHeapFrame base after) {root : Nat} {pairs : List (K × V)}
    (hr : TrieRep base root pairs) : TrieRep after root pairs := by
  let motiveNode : (root : Nat) → (pairs : List (K × V)) → TrieRep base root pairs → Prop :=
    fun root pairs _ => TrieRep after root pairs
  let motiveEntries : (slots : List (Option (Entry K V))) → (pairs : List (K × V)) →
      EntriesRep base slots pairs → Prop := fun slots pairs _ => EntriesRep after slots pairs
  have hrec : motiveNode root pairs hr := by
    refine TrieRep.rec (motive_1 := motiveNode) (motive_2 := motiveEntries) ?_ ?_ ?_ ?_ hr
    · intro current node slots ps hnode hslots hbitmap hcount _ ih
      have hi := (List.getElem?_eq_some_iff.mp hnode).1
      have hj := (List.getElem?_eq_some_iff.mp hslots).1
      exact .node ((hframe.1 current hi).trans hnode)
        ((hframe.2 node.data hj).trans hslots) hbitmap hcount ih
    · exact .nil
    · intro leaf rest ps _ ih
      exact .leaf ih
    · intro child rest childPairs restPairs _ _ ihChild ihRest
      exact .trie ihChild ihRest
  exact hrec

theorem persistentEntriesRepFrame {K V : Type} {base after : HamtHeap K V}
    (hframe : PersistentHeapFrame base after) {slots : List (Option (Entry K V))}
    {pairs : List (K × V)} (hr : EntriesRep base slots pairs) : EntriesRep after slots pairs := by
  let motiveNode : (root : Nat) → (pairs : List (K × V)) → TrieRep base root pairs → Prop :=
    fun root pairs _ => TrieRep after root pairs
  let motiveEntries : (slots : List (Option (Entry K V))) → (pairs : List (K × V)) →
      EntriesRep base slots pairs → Prop := fun slots pairs _ => EntriesRep after slots pairs
  have hrec : motiveEntries slots pairs hr := by
    refine EntriesRep.rec (motive_1 := motiveNode) (motive_2 := motiveEntries) ?_ ?_ ?_ ?_ hr
    · intro current node sl ps hnode hslots hbitmap hcount _ ih
      have hi := (List.getElem?_eq_some_iff.mp hnode).1
      have hj := (List.getElem?_eq_some_iff.mp hslots).1
      exact .node ((hframe.1 current hi).trans hnode)
        ((hframe.2 node.data hj).trans hslots) hbitmap hcount ih
    · exact .nil
    · intro leaf rest ps _ ih
      exact .leaf ih
    · intro child rest childPairs restPairs _ _ ihChild ihRest
      exact .trie ihChild ihRest
  exact hrec

/-- Replacing a leaf changes precisely its one pair in the independently
flattened list. Child subtrees retain their order and contents. -/
theorem persistentEntriesReplaceLeaf {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) {i : Nat} {old : Leaf K V}
    (hget : slots[i]? = some (some (.leaf old))) (new : Leaf K V) :
    ∃ before after,
      pairs = before ++ (old.key, old.val) :: after ∧
      EntriesRep heap (slots.set i (some (.leaf new)))
        (before ++ (new.key, new.val) :: after) := by
  induction slots generalizing pairs i with
  | nil => cases hget
  | cons slot rest ih =>
    cases hr with
    | leaf hrest =>
      rename_i leaf tailPairs
      cases i with
      | zero =>
        cases hget
        exact ⟨[], _, rfl, .leaf hrest⟩
      | succ i =>
        obtain ⟨before, after, hp, hn⟩ := ih hrest hget
        refine ⟨(leaf.key, leaf.val) :: before, after, ?_, ?_⟩
        · rw [hp]
          rfl
        · exact .leaf hn
    | trie hchild hrest =>
      rename_i child childPairs restPairs
      cases i with
      | zero => cases hget
      | succ i =>
        obtain ⟨before, after, hp, hn⟩ := ih hrest hget
        refine ⟨childPairs ++ before, after, ?_, ?_⟩
        · rw [hp, List.append_assoc]
        · rw [List.append_assoc]
          exact .trie hchild hn

/-- Removing a leaf removes precisely its pair; no assumption about its hash
or equality class is required for this structural statement. -/
theorem persistentEntriesEraseLeaf {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) {i : Nat} {old : Leaf K V}
    (hget : slots[i]? = some (some (.leaf old))) :
    ∃ before after,
      pairs = before ++ (old.key, old.val) :: after ∧
      EntriesRep heap (slots.eraseIdx i) (before ++ after) := by
  induction slots generalizing pairs i with
  | nil => cases hget
  | cons slot rest ih =>
    cases hr with
    | leaf hrest =>
      rename_i leaf tailPairs
      cases i with
      | zero =>
        cases hget
        exact ⟨[], _, rfl, hrest⟩
      | succ i =>
        obtain ⟨before, after, hp, hn⟩ := ih hrest hget
        refine ⟨(leaf.key, leaf.val) :: before, after, ?_, ?_⟩
        · rw [hp]
          rfl
        · exact .leaf hn
    | trie hchild hrest =>
      rename_i child childPairs restPairs
      cases i with
      | zero => cases hget
      | succ i =>
        obtain ⟨before, after, hp, hn⟩ := ih hrest hget
        refine ⟨childPairs ++ before, after, ?_, ?_⟩
        · rw [hp, List.append_assoc]
        · rw [List.append_assoc]
          exact .trie hchild hn

/-- Inserting one leaf adds one pair at the corresponding position in the
independent flattened sequence, after all pairs of preceding child entries. -/
theorem persistentEntriesInsertLeaf {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) (i : Nat) (hi : i ≤ slots.length)
    (new : Leaf K V) :
    ∃ before after, pairs = before ++ after ∧
      EntriesRep heap (slots.insertIdx i (some (.leaf new)))
        (before ++ (new.key, new.val) :: after) := by
  induction slots generalizing pairs i with
  | nil =>
    cases hr
    have heq : i = 0 := by simpa only [List.length_nil, Nat.le_zero_eq] using hi
    subst i
    exact ⟨[], [], rfl, .leaf .nil⟩
  | cons slot rest ih =>
    cases i with
    | zero => exact ⟨[], pairs, rfl, .leaf hr⟩
    | succ i =>
      have hi' : i ≤ rest.length := by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hi
      cases hr with
      | leaf hrest =>
        rename_i leaf tailPairs
        obtain ⟨before, after, hp, hn⟩ := ih hrest i hi'
        refine ⟨(leaf.key, leaf.val) :: before, after, ?_, ?_⟩
        · rw [hp]
          rfl
        · exact .leaf hn
      | trie hchild hrest =>
        rename_i child childPairs restPairs
        obtain ⟨before, after, hp, hn⟩ := ih hrest i hi'
        refine ⟨childPairs ++ before, after, ?_, ?_⟩
        · rw [hp, List.append_assoc]
        · rw [List.append_assoc]
          exact .trie hchild hn

/-- A copied parent can replace one old child with a newly represented child.
The untouched prefix and suffix of its pair sequence are explicit. -/
theorem persistentEntriesReplaceTrie {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap)
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep base slots pairs) {i oldChild newChild : Nat}
    (hget : slots[i]? = some (some (.trie oldChild)))
    {newPairs : List (K × V)} (hnew : TrieRep heap newChild newPairs) :
    ∃ before oldPairs after,
      TrieRep base oldChild oldPairs ∧
      pairs = before ++ oldPairs ++ after ∧
      EntriesRep heap (slots.set i (some (.trie newChild)))
        (before ++ newPairs ++ after) := by
  induction slots generalizing pairs i with
  | nil => cases hget
  | cons slot rest ih =>
    cases hr with
    | leaf hrest =>
      rename_i leaf tailPairs
      cases i with
      | zero => cases hget
      | succ i =>
        obtain ⟨before, oldPairs, after, hc, hp, hn⟩ := ih hrest hget
        refine ⟨(leaf.key, leaf.val) :: before, oldPairs, after, hc, ?_, ?_⟩
        · rw [hp]
          rfl
        · exact .leaf hn
    | trie hchild hrest =>
      rename_i child childPairs restPairs
      cases i with
      | zero =>
        cases hget
        exact ⟨[], _, _, hchild, rfl, .trie hnew (persistentEntriesRepFrame hframe hrest)⟩
      | succ i =>
        obtain ⟨before, oldPairs, after, hc, hp, hn⟩ := ih hrest hget
        refine ⟨childPairs ++ before, oldPairs, after, hc, ?_, ?_⟩
        · simp only [hp, List.append_assoc]
        · have hh := EntriesRep.trie (persistentTrieRepFrame hframe hchild) hn
          simpa only [List.append_assoc, List.set_cons_succ, List.insertIdx_succ_cons] using hh

/-- Replacing a collision leaf by a represented child replaces exactly that
one old pair by the child's independently flattened sequence. -/
theorem persistentEntriesLeafToTrie {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap)
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep base slots pairs) {i child : Nat} {old : Leaf K V}
    (hget : slots[i]? = some (some (.leaf old)))
    {newPairs : List (K × V)} (hnew : TrieRep heap child newPairs) :
    ∃ before after,
      pairs = before ++ (old.key, old.val) :: after ∧
      EntriesRep heap (slots.set i (some (.trie child)))
        (before ++ newPairs ++ after) := by
  induction slots generalizing pairs i with
  | nil => cases hget
  | cons slot rest ih =>
    cases hr with
    | leaf hrest =>
      rename_i leaf restPairs
      cases i with
      | zero =>
        cases hget
        exact ⟨[], restPairs, rfl,
          .trie hnew (persistentEntriesRepFrame hframe hrest)⟩
      | succ i =>
        obtain ⟨before, after, hp, hn⟩ := ih hrest hget
        refine ⟨(leaf.key, leaf.val) :: before, after, ?_, ?_⟩
        · rw [hp]
          rfl
        · exact .leaf hn
    | trie hchild hrest =>
      rename_i oldChild childPairs restPairs
      cases i with
      | zero => cases hget
      | succ i =>
        obtain ⟨before, after, hp, hn⟩ := ih hrest hget
        refine ⟨childPairs ++ before, after, ?_, ?_⟩
        · simp only [hp, List.append_assoc]
        · have hh := EntriesRep.trie (persistentTrieRepFrame hframe hchild) hn
          simpa only [List.append_assoc, List.set_cons_succ, List.insertIdx_succ_cons] using hh

/-- Inserting a new child at a defined vector boundary adds its entire pair
sequence between the existing prefix and suffix. -/
theorem persistentEntriesInsertTrie {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap)
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep base slots pairs) (i : Nat) (hi : i ≤ slots.length)
    (child : Nat) {newPairs : List (K × V)} (hnew : TrieRep heap child newPairs) :
    ∃ before after, pairs = before ++ after ∧
      EntriesRep heap (slots.insertIdx i (some (.trie child)))
        (before ++ newPairs ++ after) := by
  induction slots generalizing pairs i with
  | nil =>
    cases hr
    have heq : i = 0 := by simpa only [List.length_nil, Nat.le_zero_eq] using hi
    subst i
    exact ⟨[], [], rfl, .trie hnew .nil⟩
  | cons slot rest ih =>
    cases i with
    | zero => exact ⟨[], pairs, rfl, .trie hnew (persistentEntriesRepFrame hframe hr)⟩
    | succ i =>
      have hi' : i ≤ rest.length := by
        simpa only [List.length_cons, Nat.succ_le_succ_iff] using hi
      cases hr with
      | leaf hrest =>
        rename_i leaf restPairs
        obtain ⟨before, after, hp, hn⟩ := ih hrest i hi'
        refine ⟨(leaf.key, leaf.val) :: before, after, ?_, ?_⟩
        · rw [hp]
          rfl
        · exact .leaf hn
      | trie hchild hrest =>
        rename_i oldChild childPairs restPairs
        obtain ⟨before, after, hp, hn⟩ := ih hrest i hi'
        refine ⟨childPairs ++ before, after, ?_, ?_⟩
        · simp only [hp, List.append_assoc]
        · have hh := EntriesRep.trie (persistentTrieRepFrame hframe hchild) hn
          simpa only [List.append_assoc, List.set_cons_succ, List.insertIdx_succ_cons] using hh

theorem persistentHeapFrameVectorSet {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap) (data : Nat)
    (slots : List (Option (Entry K V))) (hfresh : base.vectors.length ≤ data) :
    PersistentHeapFrame base {heap with vectors := heap.vectors.set data slots} := by
  constructor
  · exact hframe.1
  · intro i hi
    have hne : data ≠ i := by omega
    simpa only [List.getElem?_set, hne, ite_false] using hframe.2 i hi

theorem persistentHeapFrameNodeSet {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap) (root : Nat)
    (node : HAMTNode K V) (hfresh : base.nodes.length ≤ root) :
    PersistentHeapFrame base {heap with nodes := heap.nodes.set root node} := by
  constructor
  · intro i hi
    have hne : root ≠ i := by omega
    simpa only [List.getElem?_set, hne, ite_false] using hframe.1 i hi
  · exact hframe.2

/-- An update of a fresh copied node and its fresh vector preserves all
original subtrees. Its leaf sequence is the sequence specified by `hentries`. -/
theorem persistentFreshFocusRep {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap) (root data bitmap : Nat)
    (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (hroot : root < heap.nodes.length) (hdata : data < heap.vectors.length)
    (hfreshRoot : base.nodes.length ≤ root) (hfreshData : base.vectors.length ≤ data)
    (hbitmap : bitmap < 2 ^ 32) (hcount : countOnes 32 bitmap = slots.length)
    (hentries : EntriesRep base slots pairs) :
    let after : HamtHeap K V :=
      { vectors := heap.vectors.set data slots,
        nodes := heap.nodes.set root ⟨data, bitmap⟩ }
    PersistentHeapFrame base after ∧ TrieRep after root pairs := by
  dsimp only
  have hf := persistentHeapFrameNodeSet
    (persistentHeapFrameVectorSet hframe data slots hfreshData)
    root ⟨data, bitmap⟩ hfreshRoot
  refine ⟨hf, TrieRep.node (node := (⟨data, bitmap⟩ : HAMTNode K V)) (slots := slots)
    ?_ ?_ hbitmap hcount (persistentEntriesRepFrame hf hentries)⟩
  · exact List.getElem?_set_self hroot
  · exact List.getElem?_set_self hdata

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: CopyContextWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Structural concatenation keeps the vector order of the leaf list. -/
theorem contextEntriesAppend {K V : Type} {heap : HamtHeap K V}
    {left right : List (Option (Entry K V))} {xs ys : List (K × V)}
    (hl : EntriesRep heap left xs) (hr : EntriesRep heap right ys) :
    EntriesRep heap (left ++ right) (xs ++ ys) := by
  induction left generalizing xs with
  | nil => cases hl; exact hr
  | cons entry rest ih =>
    cases hl with
    | leaf hrest => exact .leaf (ih hrest)
    | trie hchild hrest =>
      rw [List.append_assoc]
      exact .trie hchild (ih hrest)

/-- A selected child separates the vector and its leaf list into matching
before/child/after components. -/
theorem contextEntriesSplitChild {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) {index child : Nat}
    (hget : slots[index]? = some (some (.trie child))) :
    ∃ beforeSlots afterSlots beforePairs childPairs afterPairs,
      slots = beforeSlots ++ some (.trie child) :: afterSlots ∧
      index = beforeSlots.length ∧
      pairs = beforePairs ++ childPairs ++ afterPairs ∧
      EntriesRep heap beforeSlots beforePairs ∧
      TrieRep heap child childPairs ∧ EntriesRep heap afterSlots afterPairs := by
  induction slots generalizing pairs index with
  | nil => cases hget
  | cons entry rest ih =>
    cases hr with
    | leaf hrest =>
      rename_i leaf restPairs
      cases index with
      | zero => cases hget
      | succ index =>
        obtain ⟨bs, zs, bp, cp, zp, hs, hi, hp, hb, hc, hz⟩ := ih hrest hget
        refine ⟨some (.leaf leaf) :: bs, zs, (leaf.key, leaf.val) :: bp, cp, zp,
          ?_, ?_, ?_, .leaf hb, hc, hz⟩
        · rw [hs]
          rfl
        · simp only [List.length_cons, hi]
        · rw [hp]
          rfl
    | trie hchild hrest =>
      rename_i oldChild oldPairs restPairs
      cases index with
      | zero =>
        cases hget
        exact ⟨[], _, [], _, _, rfl, rfl, rfl, .nil, hchild, hrest⟩
      | succ index =>
        obtain ⟨bs, zs, bp, cp, zp, hs, hi, hp, hb, hc, hz⟩ := ih hrest hget
        refine ⟨some (.trie oldChild) :: bs, zs, oldPairs ++ bp, cp, zp,
          ?_, ?_, ?_, .trie hchild hb, hc, hz⟩
        · rw [hs]
          rfl
        · simp only [List.length_cons, hi]
        · rw [hp]
          simp only [List.append_assoc]

/-- A finite tree with one subtree left open. The heap records and sibling
subtrees are specified independently of the contents eventually put in the
hole. In particular the hole itself may be a freshly allocated handle. -/
inductive TrieContext {K V : Type} (heap : HamtHeap K V) :
    Nat → Nat → List (K × V) → List (K × V) → Prop where
  | root (focus : Nat) : TrieContext heap focus focus [] []
  | parent {root child focus : Nat} {node : HAMTNode K V}
      {beforeSlots afterSlots : List (Option (Entry K V))}
      {beforePairs afterPairs innerBefore innerAfter : List (K × V)}
      (hnode : heap.nodes[root]? = some node)
      (hslots : heap.vectors[node.data]? =
        some (beforeSlots ++ some (.trie child) :: afterSlots))
      (hbitmap : node.bitmap < 2 ^ 32)
      (hcount : countOnes 32 node.bitmap = beforeSlots.length + 1 + afterSlots.length)
      (hbefore : EntriesRep heap beforeSlots beforePairs)
      (hchild : TrieContext heap child focus innerBefore innerAfter)
      (hafter : EntriesRep heap afterSlots afterPairs) :
      TrieContext heap root focus (beforePairs ++ innerBefore) (innerAfter ++ afterPairs)

/-- Filling the one hole reconstructs the entire tree and its exact pair list. -/
theorem contextFill {K V : Type} {heap : HamtHeap K V}
    {root focus : Nat} {before after pairs : List (K × V)}
    (hc : TrieContext heap root focus before after)
    (hr : TrieRep heap focus pairs) :
    TrieRep heap root (before ++ pairs ++ after) := by
  induction hc with
  | root => simpa only [List.nil_append, List.append_nil] using hr
  | parent hn hs hb hnsize hbefore hchild hafter ih =>
    have he := contextEntriesAppend hbefore (EntriesRep.trie (ih hr) hafter)
    have htree := TrieRep.node hn hs hb (by
      simp only [List.length_append, List.length_cons]
      omega) he
    simpa only [List.append_assoc] using htree

/-- Nested contexts compose without examining any hole contents. -/
theorem contextCompose {K V : Type} {heap : HamtHeap K V}
    {root middle focus : Nat} {outerBefore outerAfter innerBefore innerAfter : List (K × V)}
    (ho : TrieContext heap root middle outerBefore outerAfter)
    (hi : TrieContext heap middle focus innerBefore innerAfter) :
    TrieContext heap root focus (outerBefore ++ innerBefore) (innerAfter ++ outerAfter) := by
  induction ho with
  | root => simpa only [List.nil_append, List.append_nil] using hi
  | parent hn hs hb hcount hbefore hchild hafter ih =>
    have hc := TrieContext.parent hn hs hb hcount hbefore (ih hi) hafter
    simpa only [List.append_assoc] using hc

/-- A context survives any extension preserving its node/vector records and
the existing sibling subtrees. The open handle need not already exist. -/
theorem contextFrame {K V : Type} {base afterHeap : HamtHeap K V}
    (hf : PersistentHeapFrame base afterHeap)
    {root focus : Nat} {before after : List (K × V)}
    (hc : TrieContext base root focus before after) :
    TrieContext afterHeap root focus before after := by
  induction hc with
  | root => exact .root _
  | parent hn hs hb hcount hbefore hchild hafter ih =>
    have hi := (List.getElem?_eq_some_iff.mp hn).1
    have hj := (List.getElem?_eq_some_iff.mp hs).1
    exact .parent ((hf.1 _ hi).trans hn) ((hf.2 _ hj).trans hs) hb hcount
      (persistentEntriesRepFrame hf hbefore) ih (persistentEntriesRepFrame hf hafter)

/-- A local replacement can be lifted through a preserved copied spine. -/
theorem contextReplace {K V : Type} {base afterHeap : HamtHeap K V}
    (hf : PersistentHeapFrame base afterHeap)
    {root focus : Nat} {before after pairs : List (K × V)}
    (hc : TrieContext base root focus before after)
    (hr : TrieRep afterHeap focus pairs) :
    TrieRep afterHeap root (before ++ pairs ++ after) :=
  contextFill (contextFrame hf hc) hr

/-- The exact allocation performed when one node and its vector are copied. -/
def contextCopiedHeap {K V : Type} (heap : HamtHeap K V)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) : HamtHeap K V :=
  ⟨heap.vectors ++ [slots], heap.nodes ++ [⟨heap.vectors.length, node.bitmap⟩]⟩

theorem contextCopiedHeapFrame {K V : Type} (heap : HamtHeap K V)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) :
    PersistentHeapFrame heap (contextCopiedHeap heap node slots) := by
  constructor
  · intro i hi
    simp only [contextCopiedHeap, List.getElem?_append, hi, ite_true]
  · intro i hi
    simp only [contextCopiedHeap, List.getElem?_append, hi, ite_true]

/-- Copying a node preserves its exact structural pair list at the new root. -/
theorem contextCopiedTrieRep {K V : Type} {heap : HamtHeap K V}
    {root : Nat} {pairs : List (K × V)} (hr : TrieRep heap root pairs) :
    ∃ node slots,
      heap.nodes[root]? = some node ∧ heap.vectors[node.data]? = some slots ∧
      TrieRep (contextCopiedHeap heap node slots) heap.nodes.length pairs := by
  cases hr with
  | node hn hs hb hc he =>
    rename_i node slots
    refine ⟨_, _, hn, hs, ?_⟩
    have he' := persistentEntriesRepFrame (contextCopiedHeapFrame heap node slots) he
    refine TrieRep.node (node := ⟨heap.vectors.length, _⟩) (slots := _) ?_ ?_ hb hc he'
    · simp only [contextCopiedHeap, List.getElem?_append, Nat.lt_irrefl, ite_false,
        Nat.sub_self, List.getElem?_cons_zero]
    · simp only [contextCopiedHeap, List.getElem?_append, Nat.lt_irrefl, ite_false,
        Nat.sub_self, List.getElem?_cons_zero]

theorem contextVectorAllocateRun {K V : Type} (heap : HamtHeap K V)
    (slots : List (Option (Entry K V))) :
    runHamt (heapVectorAllocate slots) heap =
      (.ok heap.vectors.length, {heap with vectors := heap.vectors ++ [slots]}) := rfl

theorem contextVectorCopyRun {K V : Type} (heap : HamtHeap K V) (data : Nat)
    (slots : List (Option (Entry K V))) (hs : heap.vectors[data]? = some slots) :
    runHamt (heapVectorOps.copy data) heap =
      (.ok heap.vectors.length, {heap with vectors := heap.vectors ++ [slots]}) := by
  change runHamt (heapVectorCopy data) heap = _
  unfold heapVectorCopy
  rw [persistentHamtBindRun, pathVectorSlotsRun heap data slots hs]
  rfl

theorem contextInnerRun {K V : Type} (heap : HamtHeap K V) (data bitmap : Nat) :
    runHamt (HAMT.inner data bitmap) heap =
      (.ok heap.nodes.length, {heap with nodes := heap.nodes ++ [⟨data, bitmap⟩]}) := rfl

/-- The frozen initial copying action has the structural heap shape above. -/
theorem contextCopyNodeRun {K V : Type} (heap : HamtHeap K V) (root : Nat)
    (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots) :
    runHamt (do
      let old ← readNode root
      let data ← heapVectorOps.copy old.data
      HAMT.inner data old.bitmap) heap =
      (.ok heap.nodes.length, contextCopiedHeap heap node slots) := by
  rw [persistentHamtBindRun, pathReadNodeRun heap root node hn]
  dsimp only
  rw [persistentHamtBindRun, contextVectorCopyRun heap node.data slots hs]
  rfl

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: HashRoutingWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Equality of the hash-state fields that determine the next bitmap slot. -/
def RoutingHashEq {K : Type} (runtime : HamtObjectIdRuntime K)
    (a b : HashState K) : Prop :=
  runtime.objectid a.key = runtime.objectid b.key ∧
    a.hash = b.hash ∧ a.depth = b.depth ∧ a.shift = b.shift

theorem routingHashEq_initial {K : Type} (runtime : HamtObjectIdRuntime K)
    (a b : K) (he : runtime.objectid a = runtime.objectid b) :
    RoutingHashEq runtime (HashState.fromKey runtime a) (HashState.fromKey runtime b) :=
  ⟨he, he, rfl, rfl⟩

theorem routingHashEq_bitmap {K : Type} {runtime : HamtObjectIdRuntime K}
    {a b : HashState K} (he : RoutingHashEq runtime a b) :
    BitmapIndex.fromHash a = BitmapIndex.fromHash b := by
  unfold BitmapIndex.fromHash
  rw [he.2.1, he.2.2.2]

theorem routingHashEq_next {K : Type} {runtime : HamtObjectIdRuntime K}
    {a b : HashState K} (he : RoutingHashEq runtime a b) :
    RoutingHashEq runtime (next runtime a) (next runtime b) := by
  obtain ⟨hi, hh, hd, hs⟩ := he
  unfold next RoutingHashEq
  simp only [hs, hd]
  split
  · exact ⟨hi, by rw [hi], rfl, rfl⟩
  · exact ⟨hi, hh, rfl, rfl⟩

/-- A leaf's finite route is described using heap cells and bitmap ranks,
without referring to the result of any lookup operation. -/
inductive RoutedLeaf {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) : Nat → HashState K → Leaf K V → Prop where
  | leaf {root : Nat} {hash : HashState K} {node : HAMTNode K V}
      {slots : List (Option (Entry K V))} {leaf : Leaf K V}
      (hnode : heap.nodes[root]? = some node)
      (hslots : heap.vectors[node.data]? = some slots)
      (hbit : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true)
      (hentry : slots[pathReadIndex node hash - 1]? = some (some (.leaf leaf))) :
      RoutedLeaf runtime heap root hash leaf
  | child {root child : Nat} {hash : HashState K} {node : HAMTNode K V}
      {slots : List (Option (Entry K V))} {leaf : Leaf K V}
      (hnode : heap.nodes[root]? = some node)
      (hslots : heap.vectors[node.data]? = some slots)
      (hbit : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true)
      (hentry : slots[pathReadIndex node hash - 1]? = some (some (.trie child)))
      (hchild : RoutedLeaf runtime heap child (next runtime hash) leaf) :
      RoutedLeaf runtime heap root hash leaf

/-- Equal identity hashes follow the same concrete route at every depth. -/
theorem routedLeaf_hashEq {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root : Nat} {a b : HashState K} {leaf : Leaf K V}
    (hr : RoutedLeaf runtime heap root a leaf) (he : RoutingHashEq runtime a b) :
    RoutedLeaf runtime heap root b leaf := by
  induction hr generalizing b with
  | leaf hn hs hb hg =>
    have hbi := routingHashEq_bitmap he
    refine .leaf hn hs ?_ ?_
    · simpa only [hbi] using hb
    · simpa only [pathReadIndex, hbi] using hg
  | child hn hs hb hg hc ih =>
    have hbi := routingHashEq_bitmap he
    refine .child hn hs ?_ ?_ (ih (routingHashEq_next he))
    · simpa only [hbi] using hb
    · simpa only [pathReadIndex, hbi] using hg

def RoutingLoopWitness {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V)
    (top root : Nat) (hash : HashState K) (leaf : Leaf K V) : Prop :=
  ∃ last finalHash result,
    runHamt (Lean.Loop.forIn (m := HamtM K V)
      (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
      (root, hash, none) (persistentPathReadStep same runtime top)) heap =
      (.ok (last, finalHash, some result), heap) ∧
    result.found = same leaf.key hash.key ∧ result.present = true ∧
    runHamt (do
      let node ← readNode result.trie
      heapVectorOps.get node.data result.index) heap = (.ok (.leaf leaf), heap)

theorem routedLeaf_loop {K V : Type} (same : K → K → Bool)
    {runtime : HamtObjectIdRuntime K} {heap : HamtHeap K V}
    {root : Nat} {hash : HashState K} {leaf : Leaf K V}
    (hr : RoutedLeaf runtime heap root hash leaf) (top : Nat) :
    RoutingLoopWitness same runtime heap top root hash leaf := by
  induction hr with
  | @leaf root hash node slots leaf hn hs hb hg =>
    let result : PathResult K V := ⟨same leaf.key hash.key, true, root,
      pathReadIndex node hash, BitmapIndex.fromHash hash, top, hash⟩
    have hstep := pathReadStep_present same runtime heap top root hash node slots
      (.leaf leaf) hn hs hg hb
    refine ⟨root, hash, result,
      pathReadLoop_terminal same runtime heap top root hash result hstep, rfl, rfl, ?_⟩
    change runHamt (do
      let n ← readNode root
      heapVectorOps.get n.data (pathReadIndex node hash)) heap = _
    rw [persistentHamtBindRun, pathReadNodeRun heap root node hn]
    exact pathVectorGetRun heap node.data slots (pathReadIndex node hash) (.leaf leaf)
      hs (Nat.le_add_left 1 _) hg
  | @child root child hash node slots leaf hn hs hb hg hc ih =>
    obtain ⟨last, finalHash, result, hloop, hf, hp, hread⟩ := ih
    have hstep := pathReadStep_present same runtime heap top root hash node slots
      (.trie child) hn hs hg hb
    refine ⟨last, finalHash, result, ?_, ?_, hp, hread⟩
    · rw [persistentHamtLoopRun, hstep]
      exact hloop
    · simpa only [pathNextKey] using hf

/-- Following a stored finite route terminates at its exact leaf. -/
theorem routedLeaf_path {K V : Type} (same : K → K → Bool)
    {runtime : HamtObjectIdRuntime K} {heap : HamtHeap K V}
    {root : Nat} {hash : HashState K} {leaf : Leaf K V}
    (hr : RoutedLeaf runtime heap root hash leaf) :
    ∃ result,
      runHamt (path heapVectorOps same runtime root hash false) heap =
        (.ok result, heap) ∧
      result.found = same leaf.key hash.key ∧ result.present = true ∧
      runHamt (do
        let node ← readNode result.trie
        heapVectorOps.get node.data result.index) heap = (.ok (.leaf leaf), heap) := by
  obtain ⟨last, finalHash, result, hloop, hf, hp, hread⟩ := routedLeaf_loop same hr root
  refine ⟨result, ?_, hf, hp, hread⟩
  rw [path.eq_1]
  simp only [Bool.false_eq_true, ite_false, ForIn.forIn]
  change runHamt (do
    let final ← Lean.Loop.forIn (m := HamtM K V)
      (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
      (root, hash, none) (persistentPathReadStep same runtime root)
    match final.2.2 with
    | some r => pure r
    | none => throw HamtError.bounds) heap = _
  rw [persistentHamtBindRun, hloop]
  rfl

/-- Every pair is stored on the route determined by its own identity hash. -/
def StoredRouting {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root : Nat) (pairs : List (K × V)) : Prop :=
  ∀ key value, (key, value) ∈ pairs →
    RoutedLeaf runtime heap root (HashState.fromKey runtime key) ⟨key, value⟩


/-- A finite route must start at a node with an occupied bitmap slot. -/
theorem routedLeaf_rootNonempty {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root : Nat} {hash : HashState K} {leaf : Leaf K V}
    (hr : RoutedLeaf runtime heap root hash leaf) :
    ∃ node : HAMTNode K V, heap.nodes[root]? = some node ∧ node.bitmap ≠ 0 := by
  cases hr with
  | leaf hn _ hb _ =>
    refine ⟨_, hn, ?_⟩
    intro hz
    rw [hz, Nat.zero_testBit] at hb
    cases hb
  | child hn _ hb _ _ =>
    refine ⟨_, hn, ?_⟩
    intro hz
    rw [hz, Nat.zero_testBit] at hb
    cases hb

theorem routingLevelRun {K V : Type} (heap : HamtHeap K V) (root : Nat)
    (node : HAMTNode K V) (hn : heap.nodes[root]? = some node) :
    runHamt (islevel_empty root) heap = (.ok (node.bitmap == 0), heap) := by
  have hb : runHamt (nodeBitmap root) heap = (.ok node.bitmap, heap) := by
    unfold nodeBitmap
    rw [persistentHamtBindRun, pathReadNodeRun heap root node hn]
    rfl
  unfold islevel_empty
  rw [persistentHamtBindRun, hb]
  rfl

theorem routingOpsLevel {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (root : Nat)
    (node : HAMTNode K V) (hn : heap.nodes[root]? = some node) :
    (round2.hamtOps same runtime).isLevelEmpty (.ok (heap, root)) = (node.bitmap == 0) := by
  unfold round2.hamtOps round2.runTrie
  dsimp only
  rw [routingLevelRun heap root node hn]

theorem routedLeaf_opsNonempty {K V : Type} (same : K → K → Bool)
    {runtime : HamtObjectIdRuntime K} {heap : HamtHeap K V}
    {root : Nat} {hash : HashState K} {leaf : Leaf K V}
    (hr : RoutedLeaf runtime heap root hash leaf) :
    (round2.hamtOps same runtime).isLevelEmpty (.ok (heap, root)) = false := by
  obtain ⟨node, hn, hb⟩ := routedLeaf_rootNonempty hr
  rw [routingOpsLevel same runtime heap root node hn]
  exact beq_eq_false_iff_ne.mpr hb

/-- A successful concrete path is packaged faithfully by the public operation record. -/
theorem routingOpsPathGeneral {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap after : HamtHeap K V) (root : Nat)
    (hash : HashState K) (copy : Bool) (result : PathResult K V)
    (hrun : runHamt (path heapVectorOps same runtime root hash copy) heap =
      (.ok result, after)) :
    (round2.hamtOps same runtime).path (.ok (heap, root)) hash copy =
      ⟨result.found, result.present, .ok (after, result.trie), result.index,
        result.bi.x, .ok (after, result.top), result.hash⟩ := by
  unfold round2.hamtOps round2.runTrie
  dsimp only
  rw [hrun]

theorem routingOpsPath {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (root : Nat)
    (hash : HashState K) (result : PathResult K V)
    (hrun : runHamt (path heapVectorOps same runtime root hash false) heap =
      (.ok result, heap)) :
    (round2.hamtOps same runtime).path (.ok (heap, root)) hash false =
      ⟨result.found, result.present, .ok (heap, result.trie), result.index,
        result.bi.x, .ok (heap, result.top), result.hash⟩ :=
  routingOpsPathGeneral same runtime heap heap root hash false result hrun

/-- The public key-get wrapper evaluates a checked concrete path without changing its result. -/
theorem routingKeyGetEquation {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (root : Nat)
    (query : K) (result : PathResult K V)
    (hpath : runHamt (path heapVectorOps same runtime root
      (HashState.fromKey runtime query) false) heap = (.ok result, heap)) :
    persistentKeyGet (round2.hamtOps same runtime)
      (⟨.ok (heap, root)⟩ : PersistentDict K V (round2.PTrie K V)) query =
      (if (round2.hamtOps same runtime).isLevelEmpty (.ok (heap, root)) then none
      else if result.found && result.present then
        (round2.hamtOps same runtime).leafValue (.ok (heap, result.trie)) result.index
      else none) := by
  change (if (round2.hamtOps same runtime).isLevelEmpty (.ok (heap, root)) then none
    else if ((round2.hamtOps same runtime).path (.ok (heap, root))
        (HashState.fromKey runtime query) false).found &&
      ((round2.hamtOps same runtime).path (.ok (heap, root))
        (HashState.fromKey runtime query) false).present then
      (round2.hamtOps same runtime).leafValue
        ((round2.hamtOps same runtime).path (.ok (heap, root))
          (HashState.fromKey runtime query) false).trie
        ((round2.hamtOps same runtime).path (.ok (heap, root))
          (HashState.fromKey runtime query) false).index
    else none) = _
  simp only [routingOpsPath same runtime heap root (HashState.fromKey runtime query) result hpath]

/-- A safe path in a finite tree cannot find a key absent from every structural leaf. -/
theorem routingKeyGetAbsent {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (heap : HamtHeap K V) {root : Nat} {pairs reference : List (K × V)}
    (hr : TrieRep heap root pairs) (hperm : List.Perm pairs reference) (query : K)
    (habsent : rfind same reference query = none) :
    persistentKeyGet (round2.hamtOps same runtime)
      (⟨.ok (heap, root)⟩ : PersistentDict K V (round2.PTrie K V)) query = none := by
  obtain ⟨result, hpath, hterminal⟩ :=
    trieRep_pathRun same runtime heap hr (HashState.fromKey runtime query)
  have hmiss : (result.found && result.present) = false := by
    cases hm : result.found && result.present with
    | false => rfl
    | true =>
      have hp := Bool.and_eq_true_iff.mp hm
      obtain ⟨leaf, node, slots, hn, hs, hi, hg, hf, hmem⟩ := hterminal hp.2
      have heq : same leaf.key query = true := hf.symm.trans hp.1
      have hfalse := (rfind_eq_none_iff.mp habsent) (leaf.key, leaf.val) (hperm.mem_iff.mp hmem)
      have htrue := hl.symm leaf.key query heq
      rw [htrue] at hfalse
      cases hfalse
  rw [routingKeyGetEquation same runtime heap root query result hpath, hmiss]
  cases (round2.hamtOps same runtime).isLevelEmpty (.ok (heap, root)) <;> rfl

/-- A clear selected root bit excludes every leaf route at that hash state. -/
theorem routedLeaf_absentAt {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root : Nat} {hash : HashState K} {leaf : Leaf K V}
    (node : HAMTNode K V) (hn : heap.nodes[root]? = some node)
    (hbit : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = false) :
    ¬ RoutedLeaf runtime heap root hash leaf := by
  intro hr
  cases hr with
  | leaf hn' _ hb _ =>
    cases Option.some.inj (hn'.symm.trans hn)
    rw [hbit] at hb
    cases hb
  | child hn' _ hb _ _ =>
    cases Option.some.inj (hn'.symm.trans hn)
    rw [hbit] at hb
    cases hb

/-- A route ending at a known selected leaf cell identifies that exact stored leaf. -/
theorem routedLeaf_leafAt {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root : Nat} {hash : HashState K} {leaf stored : Leaf K V}
    (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hg : slots[pathReadIndex node hash - 1]? = some (some (.leaf stored)))
    (hr : RoutedLeaf runtime heap root hash leaf) : leaf = stored := by
  cases hr with
  | leaf hn' hs' _ hg' =>
    cases Option.some.inj (hn'.symm.trans hn)
    cases Option.some.inj (hs'.symm.trans hs)
    exact Entry.leaf.inj (Option.some.inj (Option.some.inj (hg'.symm.trans hg)))
  | child hn' hs' _ hg' _ =>
    cases Option.some.inj (hn'.symm.trans hn)
    cases Option.some.inj (hs'.symm.trans hs)
    have he := hg'.symm.trans hg
    cases he

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: CopyRoutingPrelude.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Every finite route from a source root is preserved at a second root. -/
def RouteTransport {K V : Type} (runtime : HamtObjectIdRuntime K)
    (source : HamtHeap K V) (root : Nat) (after : HamtHeap K V) (copy : Nat) : Prop :=
  ∀ hash leaf, RoutedLeaf runtime source root hash leaf → RoutedLeaf runtime after copy hash leaf

theorem copyRouting_frame {K V : Type} {runtime : HamtObjectIdRuntime K}
    {base after : HamtHeap K V} (hf : PersistentHeapFrame base after)
    {root : Nat} {hash : HashState K} {leaf : Leaf K V}
    (hr : RoutedLeaf runtime base root hash leaf) :
    RoutedLeaf runtime after root hash leaf := by
  induction hr with
  | leaf hn hs hb hg =>
    exact .leaf ((hf.1 _ (List.getElem?_eq_some_iff.mp hn).1).trans hn)
      ((hf.2 _ (List.getElem?_eq_some_iff.mp hs).1).trans hs) hb hg
  | child hn hs hb hg hc ih =>
    exact .child ((hf.1 _ (List.getElem?_eq_some_iff.mp hn).1).trans hn)
      ((hf.2 _ (List.getElem?_eq_some_iff.mp hs).1).trans hs) hb hg ih

theorem copyRouting_frameTransport {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base after : HamtHeap K V} (hf : PersistentHeapFrame base after) (root : Nat) :
    RouteTransport runtime base root after root :=
  fun _ _ hr => copyRouting_frame hf hr

theorem copyRouting_transportTrans {K V : Type} {runtime : HamtObjectIdRuntime K}
    {a b c : HamtHeap K V} {ra rb rc : Nat}
    (hab : RouteTransport runtime a ra b rb) (hbc : RouteTransport runtime b rb c rc) :
    RouteTransport runtime a ra c rc := fun hash leaf hr => hbc hash leaf (hab hash leaf hr)

/-- A copied root with the same bitmap and entry references preserves routing.
Every child route is protected by the old-prefix frame. -/
theorem copyRouting_sameSlots {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base after : HamtHeap K V} (hf : PersistentHeapFrame base after)
    (root copy : Nat) (sourceNode node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hn : base.nodes[root]? = some sourceNode) (hs : base.vectors[sourceNode.data]? = some slots)
    (hcn : after.nodes[copy]? = some node) (hcs : after.vectors[node.data]? = some slots)
    (hbitmap : node.bitmap = sourceNode.bitmap) :
    RouteTransport runtime base root after copy := by
  intro hash leaf hr
  cases hr with
  | leaf hn' hs' hb hg =>
    cases Option.some.inj (hn'.symm.trans hn)
    cases Option.some.inj (hs'.symm.trans hs)
    refine .leaf hcn hcs ?_ ?_
    · simpa only [hbitmap] using hb
    · simpa only [pathReadIndex, hbitmap] using hg
  | child hn' hs' hb hg hc =>
    cases Option.some.inj (hn'.symm.trans hn)
    cases Option.some.inj (hs'.symm.trans hs)
    refine .child hcn hcs ?_ ?_ (copyRouting_frame hf hc)
    · simpa only [hbitmap] using hb
    · simpa only [pathReadIndex, hbitmap] using hg

/-- Replacing one child reference by a route-equivalent child preserves all
routes. Other children remain protected by the source-prefix frame. -/
theorem copyRouting_replaceChild {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base after : HamtHeap K V} (hf : PersistentHeapFrame base after)
    (root copy oldChild newChild index : Nat) (sourceNode node : HAMTNode K V)
    (slots : List (Option (Entry K V)))
    (hn : base.nodes[root]? = some sourceNode) (hs : base.vectors[sourceNode.data]? = some slots)
    (hcn : after.nodes[copy]? = some node)
    (hcs : after.vectors[node.data]? = some (slots.set index (some (.trie newChild))))
    (hbitmap : node.bitmap = sourceNode.bitmap)
    (hselected : slots[index]? = some (some (.trie oldChild)))
    (hchild : RouteTransport runtime base oldChild after newChild) :
    RouteTransport runtime base root after copy := by
  intro hash leaf hr
  have hi : index < slots.length := (List.getElem?_eq_some_iff.mp hselected).1
  cases hr with
  | leaf hn' hs' hb hg =>
    cases Option.some.inj (hn'.symm.trans hn)
    cases Option.some.inj (hs'.symm.trans hs)
    have hne : index ≠ pathReadIndex sourceNode hash - 1 := by
      intro heq
      rw [heq, hg] at hselected
      cases hselected
    refine .leaf hcn hcs ?_ ?_
    · simpa only [hbitmap] using hb
    · have hget : (slots.set index (some (.trie newChild)))[pathReadIndex sourceNode hash - 1]? =
          some (some (.leaf leaf)) := by
        rw [List.getElem?_set_ne hne]
        exact hg
      simpa only [pathReadIndex, hbitmap] using hget
  | @child _ child _ _ _ _ hn' hs' hb hg hc =>
    cases Option.some.inj (hn'.symm.trans hn)
    cases Option.some.inj (hs'.symm.trans hs)
    by_cases heq : index = pathReadIndex sourceNode hash - 1
    · have hsame : child = oldChild := by
        rw [heq, hg] at hselected
        exact Entry.trie.inj (Option.some.inj (Option.some.inj hselected))
      subst child
      refine .child hcn hcs ?_ ?_ (hchild _ _ hc)
      · simpa only [hbitmap] using hb
      · have hget : (slots.set index (some (.trie newChild)))[pathReadIndex sourceNode hash - 1]? =
            some (some (.trie newChild)) := by
          rw [← heq, List.getElem?_set_self hi]
        simpa only [pathReadIndex, hbitmap] using hget
    · refine .child hcn hcs ?_ ?_ (copyRouting_frame hf hc)
      · simpa only [hbitmap] using hb
      · have hget : (slots.set index (some (.trie newChild)))[pathReadIndex sourceNode hash - 1]? =
            some (some (.trie child)) := by
          rw [List.getElem?_set_ne heq]
          exact hg
        simpa only [pathReadIndex, hbitmap] using hget

theorem copyRouting_stored {K V : Type} {runtime : HamtObjectIdRuntime K}
    {base after : HamtHeap K V} {root copy : Nat} {pairs : List (K × V)}
    (ht : RouteTransport runtime base root after copy)
    (hr : StoredRouting runtime base root pairs) : StoredRouting runtime after copy pairs :=
  fun key value hmem => ht _ _ (hr key value hmem)

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: CopyRoutingContext.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- A finite selected-hash route prefix ending at a replaceable focus. -/
inductive RoutingContext {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) : Nat → HashState K → Nat → HashState K → Prop where
  | root (root : Nat) (hash : HashState K) : RoutingContext runtime heap root hash root hash
  | child {root child focus : Nat} {hash focusHash : HashState K}
      {node : HAMTNode K V} {slots : List (Option (Entry K V))}
      (hnode : heap.nodes[root]? = some node)
      (hslots : heap.vectors[node.data]? = some slots)
      (hbit : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true)
      (hentry : slots[pathReadIndex node hash - 1]? = some (some (.trie child)))
      (hchild : RoutingContext runtime heap child (next runtime hash) focus focusHash) :
      RoutingContext runtime heap root hash focus focusHash

theorem copyRouting_contextFill {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root focus : Nat} {hash focusHash : HashState K}
    {leaf : Leaf K V} (hc : RoutingContext runtime heap root hash focus focusHash)
    (hr : RoutedLeaf runtime heap focus focusHash leaf) :
    RoutedLeaf runtime heap root hash leaf := by
  induction hc with
  | root => exact hr
  | child hn hs hb hg hc ih => exact .child hn hs hb hg (ih hr)

/-- Any leaf route with the selected query hash must follow the same finite
prefix and therefore reaches the focus with the recorded terminal hash. -/
theorem copyRouting_contextPullback {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root focus : Nat} {hash focusHash : HashState K}
    {leaf : Leaf K V} (hc : RoutingContext runtime heap root hash focus focusHash)
    (hr : RoutedLeaf runtime heap root hash leaf) :
    RoutedLeaf runtime heap focus focusHash leaf := by
  induction hc with
  | root => exact hr
  | @child root child focus hash focusHash node slots hn hs hb hg hc ih =>
    cases hr with
    | leaf hn' hs' _ he =>
      cases Option.some.inj (hn'.symm.trans hn)
      cases Option.some.inj (hs'.symm.trans hs)
      have hbad := hg.symm.trans he
      cases hbad
    | @child _ storedChild _ _ _ _ hn' hs' _ he hroute =>
      cases Option.some.inj (hn'.symm.trans hn)
      cases Option.some.inj (hs'.symm.trans hs)
      have hsame : storedChild = child :=
        Entry.trie.inj (Option.some.inj (Option.some.inj (he.symm.trans hg)))
      subst storedChild
      exact ih hroute

theorem copyRouting_contextFrame {K V : Type} {runtime : HamtObjectIdRuntime K}
    {base after : HamtHeap K V} (hf : PersistentHeapFrame base after)
    {root focus : Nat} {hash focusHash : HashState K}
    (hc : RoutingContext runtime base root hash focus focusHash) :
    RoutingContext runtime after root hash focus focusHash := by
  induction hc with
  | root root hash => exact .root root hash
  | child hn hs hb hg hc ih =>
    exact .child ((hf.1 _ (List.getElem?_eq_some_iff.mp hn).1).trans hn)
      ((hf.2 _ (List.getElem?_eq_some_iff.mp hs).1).trans hs) hb hg ih

theorem copyRouting_contextCompose {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root middle focus : Nat} {hash middleHash focusHash : HashState K}
    (ho : RoutingContext runtime heap root hash middle middleHash)
    (hi : RoutingContext runtime heap middle middleHash focus focusHash) :
    RoutingContext runtime heap root hash focus focusHash := by
  induction ho with
  | root => exact hi
  | child hn hs hb hg hc ih => exact .child hn hs hb hg (ih hi)

/-- A finite represented subtree's routes depend only on its old heap records.
Thus a route found after a prefix-preserving extension already existed before. -/
theorem copyRouting_pullback {K V : Type} {runtime : HamtObjectIdRuntime K}
    {base after : HamtHeap K V} (hf : PersistentHeapFrame base after)
    {root : Nat} {pairs : List (K × V)} (hr : TrieRep base root pairs)
    {hash : HashState K} {leaf : Leaf K V} (hroute : RoutedLeaf runtime after root hash leaf) :
    RoutedLeaf runtime base root hash leaf := by
  let motiveNode := fun (root : Nat) (pairs : List (K × V)) (_ : TrieRep base root pairs) =>
    ∀ hash leaf, RoutedLeaf runtime after root hash leaf → RoutedLeaf runtime base root hash leaf
  let motiveEntries := fun (slots : List (Option (Entry K V))) (pairs : List (K × V))
      (_ : EntriesRep base slots pairs) =>
    ∀ (index child : Nat), slots[index]? = some (some (Entry.trie child)) →
      ∀ hash leaf, RoutedLeaf runtime after child hash leaf → RoutedLeaf runtime base child hash leaf
  have hrec : motiveNode root pairs hr := by
    refine TrieRep.rec (motive_1 := motiveNode) (motive_2 := motiveEntries) ?_ ?_ ?_ ?_ hr
    · intro root node slots pairs hn hs _ _ _ ih hash leaf hroute
      have hnAfter := (hf.1 root (List.getElem?_eq_some_iff.mp hn).1).trans hn
      have hsAfter := (hf.2 node.data (List.getElem?_eq_some_iff.mp hs).1).trans hs
      cases hroute with
      | leaf hn' hs' hb hg =>
        cases Option.some.inj (hn'.symm.trans hnAfter)
        cases Option.some.inj (hs'.symm.trans hsAfter)
        exact .leaf hn hs hb hg
      | child hn' hs' hb hg hc =>
        cases Option.some.inj (hn'.symm.trans hnAfter)
        cases Option.some.inj (hs'.symm.trans hsAfter)
        exact .child hn hs hb hg (ih _ _ hg _ _ hc)
    · intro index child hg
      cases hg
    · intro leaf rest pairs hr ih index child hg
      cases index with
      | zero => cases hg
      | succ index => exact ih index child hg
    · intro storedChild rest cp rp hc hr ihc ihr index child hg
      cases index with
      | zero =>
        cases hg
        exact ihc
      | succ index => exact ihr index child hg
  exact hrec hash leaf hroute

/-- A child different from the open hole belongs to one of its independently
represented sibling lists. -/
theorem copyRouting_siblingRep {K V : Type} {heap : HamtHeap K V}
    {before after : List (Option (Entry K V))} {bp ap : List (K × V)}
    (hb : EntriesRep heap before bp) (ha : EntriesRep heap after ap)
    {hole child index : Nat} (hne : child ≠ hole)
    (hg : (before ++ some (.trie hole) :: after)[index]? = some (some (.trie child))) :
    ∃ pairs, TrieRep heap child pairs := by
  rw [List.getElem?_append] at hg
  by_cases hi : index < before.length
  · rw [if_pos hi] at hg
    obtain ⟨_, _, _, pairs, _, _, _, _, _, hc, _⟩ := contextEntriesSplitChild hb hg
    exact ⟨pairs, hc⟩
  · rw [if_neg hi] at hg
    cases hrem : index - before.length with
    | zero =>
      simp only [hrem, List.getElem?_cons_zero] at hg
      have heq : hole = child := Entry.trie.inj (Option.some.inj (Option.some.inj hg))
      exact (hne heq.symm).elim
    | succ i =>
      simp only [hrem, List.getElem?_cons_succ] at hg
      obtain ⟨_, _, _, pairs, _, _, _, _, _, hc, _⟩ := contextEntriesSplitChild ha hg
      exact ⟨pairs, hc⟩

/-- A per-leaf route update at the hole lifts through all preserved ancestors.
Other branches are justified by their independently represented sibling trees. -/
theorem copyRouting_liftFocus {K V : Type} {runtime : HamtObjectIdRuntime K}
    {base before after : HamtHeap K V} (hb : PersistentHeapFrame base before)
    (ha : PersistentHeapFrame base after) {root focus : Nat} {bp ap : List (K × V)}
    (hc : TrieContext base root focus bp ap) (leaf : Leaf K V)
    (hfocus : ∀ hash, RoutedLeaf runtime before focus hash leaf →
      RoutedLeaf runtime after focus hash leaf) :
    ∀ hash, RoutedLeaf runtime before root hash leaf → RoutedLeaf runtime after root hash leaf := by
  let motive := fun (root focus : Nat) (bp ap : List (K × V))
      (_ : TrieContext base root focus bp ap) =>
    (∀ hash, RoutedLeaf runtime before focus hash leaf → RoutedLeaf runtime after focus hash leaf) →
      ∀ hash, RoutedLeaf runtime before root hash leaf → RoutedLeaf runtime after root hash leaf
  have hrec : motive root focus bp ap hc := by
    refine TrieContext.rec (motive := motive) ?_ ?_ hc
    · intro root hfocus hash hr
      exact hfocus hash hr
    · intro root child focus node bs zs bp zp ib ia hn hs _ _ hbs hchild hzs ih hfocus hash hr
      have hnBefore := (hb.1 root (List.getElem?_eq_some_iff.mp hn).1).trans hn
      have hsBefore := (hb.2 node.data (List.getElem?_eq_some_iff.mp hs).1).trans hs
      have hnAfter := (ha.1 root (List.getElem?_eq_some_iff.mp hn).1).trans hn
      have hsAfter := (ha.2 node.data (List.getElem?_eq_some_iff.mp hs).1).trans hs
      cases hr with
      | leaf hn' hs' hbit hget =>
        cases Option.some.inj (hn'.symm.trans hnBefore)
        cases Option.some.inj (hs'.symm.trans hsBefore)
        exact .leaf hnAfter hsAfter hbit hget
      | @child _ storedChild _ _ _ _ hn' hs' hbit hget hroute =>
        cases Option.some.inj (hn'.symm.trans hnBefore)
        cases Option.some.inj (hs'.symm.trans hsBefore)
        by_cases heq : storedChild = child
        · subst storedChild
          exact .child hnAfter hsAfter hbit hget (ih hfocus _ hroute)
        · obtain ⟨pairs, hrep⟩ := copyRouting_siblingRep hbs hzs heq hget
          exact .child hnAfter hsAfter hbit hget
            (copyRouting_frame ha (copyRouting_pullback hb hrep hroute))
  exact hrec hfocus

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: HashDepthWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Finite advancement is specified independently of the source alignment loop. -/
def hashAdvance {K : Type} (runtime : HamtObjectIdRuntime K) : Nat → HashState K → HashState K
  | 0, hash => hash
  | n + 1, hash => hashAdvance runtime n (next runtime hash)

theorem hashNextDepth {K : Type} (runtime : HamtObjectIdRuntime K) (hash : HashState K) :
    (next runtime hash).depth = hash.depth + 1 := by
  unfold next
  dsimp only
  split <;> rfl

theorem hashAdvanceDepth {K : Type} (runtime : HamtObjectIdRuntime K) (n : Nat)
    (hash : HashState K) : (hashAdvance runtime n hash).depth = hash.depth + n := by
  induction n generalizing hash with
  | zero => rfl
  | succ n ih =>
    rw [hashAdvance, ih, hashNextDepth]
    omega

theorem hashAdvanceKey {K : Type} (runtime : HamtObjectIdRuntime K) (n : Nat)
    (hash : HashState K) : (hashAdvance runtime n hash).key = hash.key := by
  induction n generalizing hash with
  | zero => rfl
  | succ n ih => rw [hashAdvance, ih, pathNextKey]

theorem hashAdvanceNext {K : Type} (runtime : HamtObjectIdRuntime K) (n : Nat)
    (hash : HashState K) :
    hashAdvance runtime n (next runtime hash) = next runtime (hashAdvance runtime n hash) := by
  induction n generalizing hash with
  | zero => rfl
  | succ n ih => exact ih (next runtime hash)

def CanonicalHash {K : Type} (runtime : HamtObjectIdRuntime K) (hash : HashState K) : Prop :=
  hash = hashAdvance runtime hash.depth (HashState.fromKey runtime hash.key)

theorem canonicalHash_initial {K : Type} (runtime : HamtObjectIdRuntime K) (key : K) :
    CanonicalHash runtime (HashState.fromKey runtime key) := rfl

theorem canonicalHash_next {K : Type} {runtime : HamtObjectIdRuntime K} {hash : HashState K}
    (hc : CanonicalHash runtime hash) : CanonicalHash runtime (next runtime hash) := by
  unfold CanonicalHash
  rw [hashNextDepth, pathNextKey, hashAdvance, hashAdvanceNext]
  exact congrArg (next runtime) hc

def hashDepthStep {K : Type} (runtime : HamtObjectIdRuntime K) (target : Nat) :
    Unit → HashState K → Id (ForInStep (HashState K)) :=
  fun _ hash => if hash.depth = target then pure (.done hash)
    else pure (.yield (next runtime hash))

def hashDepthLoop {K : Type} (runtime : HamtObjectIdRuntime K) (target : Nat)
    (hash : HashState K) : HashState K :=
  Lean.Loop.forIn (m := Id) (β := HashState K) ({} : Lean.Loop) hash
    (hashDepthStep runtime target)

theorem hashDepthLoop_eq_advance {K : Type} (runtime : HamtObjectIdRuntime K) (target : Nat) :
    ∀ n (hash : HashState K), target = hash.depth + n →
      hashDepthLoop runtime target hash = hashAdvance runtime n hash := by
  intro n
  induction n with
  | zero =>
    intro hash ht
    have he : hash.depth = target := by omega
    unfold hashDepthLoop
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [hashDepthStep, he, ite_true, hashAdvance] <;> rfl
  | succ n ih =>
    intro hash ht
    have he : hash.depth ≠ target := by omega
    have hloop : hashDepthLoop runtime target hash =
        hashDepthLoop runtime target (next runtime hash) := by
      unfold hashDepthLoop
      rw [Lean.Loop.forIn_eq_of_monadTail]
      simp only [hashDepthStep, he, ite_false] <;> rfl
    rw [hloop, ih (next runtime hash) (by rw [hashNextDepth]; omega)] <;> rfl

/-- The source loop reconstructs exactly the requested finite hash depth. -/
theorem hashFromOther_eq_advance {K Q : Type} (runtime : HamtObjectIdRuntime K)
    (other : HashState Q) (key : K) :
    HashState.fromOtherAtDepth runtime other key =
      hashAdvance runtime other.depth (HashState.fromKey runtime key) := by
  have h := hashDepthLoop_eq_advance runtime other.depth other.depth
    (HashState.fromKey runtime key) (Nat.zero_add other.depth).symm
  simpa [HashState.fromOtherAtDepth, hashDepthLoop, hashDepthStep,
    ForIn.forIn, Lean.Loop.forIn, Id.run] using h

theorem routingContext_canonical {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root focus : Nat} {hash focusHash : HashState K}
    (hr : RoutingContext runtime heap root hash focus focusHash)
    (hc : CanonicalHash runtime hash) : CanonicalHash runtime focusHash := by
  induction hr with
  | root => exact hc
  | child hn hs hb he hr ih => exact ih (canonicalHash_next hc)

theorem routingContext_advance {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root focus : Nat} {hash focusHash : HashState K}
    (hr : RoutingContext runtime heap root hash focus focusHash) :
    ∃ n, focusHash = hashAdvance runtime n hash := by
  induction hr with
  | root => exact ⟨0, rfl⟩
  | child hn hs hb he hr ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n + 1, h⟩

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: CopyPathWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- The frozen copying traversal step, exposed for local state equations. -/
def copyPathStep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (top : Nat) :
    Unit → (Nat × HashState K × Option (PathResult K V)) →
      HamtM K V (ForInStep (Nat × HashState K × Option (PathResult K V))) :=
  fun _ state => do
    let current := state.1
    let hash := state.2.1
    let result := state.2.2
    if result.isNone then
      let bi := BitmapIndex.fromHash hash
      let index ← entry_index current bi
      if ← isset current bi then
        let node ← readNode current
        match ← heapVectorOps.get node.data index with
        | .leaf leaf => pure (.yield (current, hash,
            some ⟨same leaf.key hash.key, true, current, index, bi, top, hash⟩))
        | .trie child =>
          let childNode ← readNode child
          let childData ← heapVectorOps.copy childNode.data
          let childCopy ← HAMT.inner childData childNode.bitmap
          let parentData ← nodeData current
          let _ ← heapVectorOps.set parentData index (.trie childCopy)
          pure (.yield (childCopy, next runtime hash, result))
      else pure (.yield (current, hash,
          some ⟨true, false, current, index, bi, top, hash⟩))
    else pure (.done (current, hash, result))

/-- The generated loop body retains the final pure child-copy binding exactly
as in the frozen source. Its equality to the exposed step uses monad laws. -/
def copyPathForInBody {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (top : Nat) :
    Unit → (Nat × HashState K × Option (PathResult K V)) →
      HamtM K V (ForInStep (Nat × HashState K × Option (PathResult K V))) :=
  fun _ state => do
    if state.2.2.isNone = true then
      let index ← entry_index state.1 (BitmapIndex.fromHash state.2.1)
      if ← isset state.1 (BitmapIndex.fromHash state.2.1) then
        let node ← readNode state.1
        match ← heapVectorOps.get node.data index with
        | .leaf leaf => pure (.yield (state.1, state.2.1,
            some ⟨same leaf.key state.2.1.key, true, state.1, index,
              BitmapIndex.fromHash state.2.1, top, state.2.1⟩))
        | .trie child =>
          let childNode ← readNode child
          let childData ← heapVectorOps.copy childNode.data
          let childCopy ← HAMT.inner childData childNode.bitmap
          let parentData ← nodeData state.1
          heapVectorOps.set parentData index (.trie childCopy)
          let nextTrie ← pure childCopy
          pure (.yield (nextTrie, next runtime state.2.1, state.2.2))
      else pure (.yield (state.1, state.2.1,
          some ⟨true, false, state.1, index, BitmapIndex.fromHash state.2.1, top, state.2.1⟩))
    else pure (.done (state.1, state.2.1, state.2.2))

theorem copyPathForInBody_eq {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (top : Nat) :
    copyPathForInBody (V := V) same runtime top = copyPathStep same runtime top := by
  funext unit state
  cases state with
  | mk current rest =>
    cases rest with
    | mk hash result =>
      simp only [copyPathForInBody, copyPathStep, bind_assoc, pure_bind]

/-- A copied node has a fresh record and a fresh vector with exactly its
source node's bitmap and entry references. -/
def CopyPathNode {K V : Type} (base : HamtHeap K V) (source : Nat)
    (heap : HamtHeap K V) (current : Nat) : Prop :=
  ∃ (sourceNode : HAMTNode K V) (slots : List (Option (Entry K V)))
      (node : HAMTNode K V),
    base.nodes[source]? = some sourceNode ∧
    base.vectors[sourceNode.data]? = some slots ∧
    heap.nodes[current]? = some node ∧ heap.vectors[node.data]? = some slots ∧
    node.bitmap = sourceNode.bitmap ∧
    base.nodes.length ≤ current ∧ base.vectors.length ≤ node.data

/-- All terminal slot facts needed for a subsequent local insertion or deletion
are retained relative to a heap that already contains the copied ancestors. -/
def CopyPathTerminal {K V : Type} (same : K → K → Bool) (query : K)
    (base after : HamtHeap K V) (result : PathResult K V)
    (pairs : List (K × V)) : Prop :=
  ∃ (node : HAMTNode K V) (slots : List (Option (Entry K V))),
    after.nodes[result.trie]? = some node ∧ after.vectors[node.data]? = some slots ∧
    node.bitmap < 2 ^ 32 ∧ countOnes 32 node.bitmap = slots.length ∧
    EntriesRep base slots pairs ∧ base.nodes.length ≤ result.trie ∧
    base.vectors.length ≤ node.data ∧ result.hash.key = query ∧
    result.bi = BitmapIndex.fromHash result.hash ∧
    result.index = pathReadIndex node result.hash ∧
    Nat.testBit node.bitmap result.bi.x = result.present ∧
    (if result.present then
      ∃ leaf : Leaf K V, slots[result.index - 1]? = some (some (.leaf leaf)) ∧
        result.found = same leaf.key query
    else result.found = true)

def CopyPathWitness {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (top : Nat) (sourceBase : HamtHeap K V) (source : Nat)
    (base heap : HamtHeap K V) (current : Nat) (hash : HashState K) (pairs : List (K × V)) : Prop :=
  ∃ last finalHash result after focusBase before focusPairs rest,
    runHamt (Lean.Loop.forIn (m := HamtM K V)
      (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
      (current, hash, none) (copyPathStep same runtime top)) heap =
      (.ok (last, finalHash, some result), after) ∧
    PersistentHeapFrame base focusBase ∧ PersistentHeapFrame focusBase after ∧
    TrieContext focusBase current result.trie before rest ∧
    pairs = before ++ focusPairs ++ rest ∧
    CopyPathTerminal same hash.key focusBase after result focusPairs ∧ result.top = top ∧
    RouteTransport runtime sourceBase source after current ∧
    RoutingContext runtime focusBase current hash result.trie result.hash

def CopyPathProperty {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (top : Nat) (sourceBase : HamtHeap K V)
    (source : Nat) (pairs : List (K × V)) : Prop :=
  ∀ {base heap : HamtHeap K V} {current : Nat},
    PersistentHeapFrame sourceBase base → CopyPathNode base source heap current →
    PersistentHeapFrame base heap → ∀ hash,
      CopyPathWitness same runtime top sourceBase source base heap current hash pairs

theorem copyPathNode_initial {K V : Type} (heap : HamtHeap K V) (source : Nat)
    (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hn : heap.nodes[source]? = some node) (hs : heap.vectors[node.data]? = some slots) :
    CopyPathNode heap source (contextCopiedHeap heap node slots) heap.nodes.length := by
  refine ⟨node, slots, ⟨heap.vectors.length, node.bitmap⟩, hn, hs, ?_, ?_, rfl,
    Nat.le_refl _, Nat.le_refl _⟩
  · simp only [contextCopiedHeap, List.getElem?_append, Nat.lt_irrefl, ite_false,
      Nat.sub_self, List.getElem?_cons_zero]
  · simp only [contextCopiedHeap, List.getElem?_append, Nat.lt_irrefl, ite_false,
      Nat.sub_self, List.getElem?_cons_zero]

theorem copyPathNodeDataRun {K V : Type} (heap : HamtHeap K V) (current : Nat)
    (node : HAMTNode K V) (hn : heap.nodes[current]? = some node) :
    runHamt (nodeData current) heap = (.ok node.data, heap) := by
  unfold nodeData
  rw [persistentHamtBindRun, pathReadNodeRun heap current node hn] <;> rfl

theorem copyPathVectorSetRun {K V : Type} (heap : HamtHeap K V) (data index : Nat)
    (slots : List (Option (Entry K V))) (entry : Entry K V)
    (hs : heap.vectors[data]? = some slots) (hlo : 1 ≤ index) (hhi : index ≤ slots.length) :
    runHamt (heapVectorOps.set data index entry) heap =
      (.ok (), {heap with vectors := heap.vectors.set data (slots.set (index - 1) (some entry))}) := by
  have hget : runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := rfl
  change runHamt (heapVectorSet data index entry) heap = _
  unfold heapVectorSet
  rw [persistentHamtBindRun, hget]
  dsimp only
  rw [hs]
  dsimp only
  have hbad : (index = 0 || index > slots.length) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  rw [hbad] <;> rfl

theorem copyPathStep_leaf {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : Nat)
    (hash : HashState K) (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (leaf : Leaf K V) (hn : heap.nodes[current]? = some node)
    (hs : heap.vectors[node.data]? = some slots)
    (he : slots[pathReadIndex node hash - 1]? = some (some (.leaf leaf)))
    (hb : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true) :
    runHamt (copyPathStep same runtime top () (current, hash, none)) heap =
      (.ok (.yield (current, hash, some ⟨same leaf.key hash.key, true, current,
        pathReadIndex node hash, BitmapIndex.fromHash hash, top, hash⟩)), heap) := by
  simp only [copyPathStep, Option.isNone, ite_true]
  rw [persistentHamtBindRun, pathReadIndexRun heap current node hash hn]
  dsimp only
  rw [persistentHamtBindRun, pathIssetRun heap current node hash hn]
  simp only [hb, ite_true]
  rw [persistentHamtBindRun, pathReadNodeRun heap current node hn]
  dsimp only
  rw [persistentHamtBindRun,
    pathVectorGetRun heap node.data slots (pathReadIndex node hash) (.leaf leaf) hs
      (Nat.le_add_left 1 _) he] <;> rfl

theorem copyPathStep_absent {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : Nat)
    (hash : HashState K) (node : HAMTNode K V) (hn : heap.nodes[current]? = some node)
    (hb : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = false) :
    runHamt (copyPathStep same runtime top () (current, hash, none)) heap =
      (.ok (.yield (current, hash, some ⟨true, false, current,
        pathReadIndex node hash, BitmapIndex.fromHash hash, top, hash⟩)), heap) := by
  simp only [copyPathStep, Option.isNone, ite_true]
  rw [persistentHamtBindRun, pathReadIndexRun heap current node hash hn]
  dsimp only
  rw [persistentHamtBindRun, pathIssetRun heap current node hash hn]
  simp only [hb, Bool.false_eq_true, ite_false] <;> rfl

theorem copyPathLoop_terminal {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current : Nat)
    (hash : HashState K) (result : PathResult K V)
    (hs : runHamt (copyPathStep same runtime top () (current, hash, none)) heap =
      (.ok (.yield (current, hash, some result)), heap)) :
    runHamt (Lean.Loop.forIn (m := HamtM K V)
      (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
      (current, hash, none) (copyPathStep same runtime top)) heap =
      (.ok (current, hash, some result), heap) := by
  rw [persistentHamtLoopRun, hs]
  dsimp only
  exact persistentHamtLoopRun (current, hash, some result) (copyPathStep same runtime top) heap

/-- The parent is linked to a child handle before that child's copied records
are appended; this intermediate heap specifies the preserved open context. -/
def copyPathParentHeap {K V : Type} (heap : HamtHeap K V)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (index : Nat) : HamtHeap K V :=
  {heap with vectors := heap.vectors.set node.data (slots.set (index - 1) (some (.trie heap.nodes.length)))}

theorem copyPathStep_child {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (top current child : Nat)
    (hash : HashState K) (node childNode : HAMTNode K V)
    (slots childSlots : List (Option (Entry K V)))
    (hn : heap.nodes[current]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (he : slots[pathReadIndex node hash - 1]? = some (some (.trie child)))
    (hb : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true)
    (hchild : heap.nodes[child]? = some childNode)
    (hchildSlots : heap.vectors[childNode.data]? = some childSlots) :
    runHamt (copyPathStep same runtime top () (current, hash, none)) heap =
      (.ok (.yield (heap.nodes.length, next runtime hash, none)),
        contextCopiedHeap (copyPathParentHeap heap node slots (pathReadIndex node hash))
          childNode childSlots) := by
  let copied := contextCopiedHeap heap childNode childSlots
  have hcurrentLt := (List.getElem?_eq_some_iff.mp hn).1
  have hdataLt := (List.getElem?_eq_some_iff.mp hs).1
  have hcopiedNode : copied.nodes[current]? = some node :=
    ((contextCopiedHeapFrame heap childNode childSlots).1 current hcurrentLt).trans hn
  have hcopiedSlots : copied.vectors[node.data]? = some slots :=
    ((contextCopiedHeapFrame heap childNode childSlots).2 node.data hdataLt).trans hs
  have hlo : 1 ≤ pathReadIndex node hash := Nat.le_add_left 1 _
  have hhi : pathReadIndex node hash ≤ slots.length := by
    have hi := (List.getElem?_eq_some_iff.mp he).1
    omega
  simp only [copyPathStep, Option.isNone, ite_true]
  rw [persistentHamtBindRun, pathReadIndexRun heap current node hash hn]
  dsimp only
  rw [persistentHamtBindRun, pathIssetRun heap current node hash hn]
  simp only [hb, ite_true]
  rw [persistentHamtBindRun, pathReadNodeRun heap current node hn]
  dsimp only
  rw [persistentHamtBindRun,
    pathVectorGetRun heap node.data slots (pathReadIndex node hash) (.trie child) hs hlo he]
  dsimp only
  rw [persistentHamtBindRun, pathReadNodeRun heap child childNode hchild]
  dsimp only
  rw [persistentHamtBindRun, contextVectorCopyRun heap childNode.data childSlots hchildSlots]
  dsimp only
  rw [persistentHamtBindRun, contextInnerRun]
  dsimp only
  change runHamt (do
      let parentData ← nodeData current
      let _ ← heapVectorOps.set parentData (pathReadIndex node hash) (.trie heap.nodes.length)
      pure (ForInStep.yield (heap.nodes.length, next runtime hash,
        (none : Option (PathResult K V))))) copied = _
  rw [persistentHamtBindRun, copyPathNodeDataRun copied current node hcopiedNode]
  dsimp only
  rw [persistentHamtBindRun,
    copyPathVectorSetRun copied node.data (pathReadIndex node hash) slots
      (.trie heap.nodes.length) hcopiedSlots hlo hhi]
  change ((.ok (.yield (heap.nodes.length, next runtime hash, none)) :
      Except HamtError (ForInStep (Nat × HashState K × Option (PathResult K V)))),
      {copied with vectors := copied.vectors.set node.data (slots.set (pathReadIndex node hash - 1) (some (.trie heap.nodes.length)))}) = _
  simp only [copied, contextCopiedHeap, copyPathParentHeap, List.length_set,
    List.set_append_left node.data _ hdataLt]

/-- The rank-selected slot of a finite structural entry list is defined. -/
theorem copyEntries_get {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) (index : Nat) (hi : index < slots.length) :
    ∃ entry, slots[index]? = some (some entry) := by
  induction slots generalizing pairs index with
  | nil => cases hi
  | cons slot rest ih =>
    cases hr with
    | leaf hrest =>
      cases index with
      | zero => exact ⟨_, rfl⟩
      | succ index => exact ih hrest index (Nat.lt_of_succ_lt_succ hi)
    | trie hchild hrest =>
      cases index with
      | zero => exact ⟨_, rfl⟩
      | succ index => exact ih hrest index (Nat.lt_of_succ_lt_succ hi)

/-- Every copying path through a finite structural tree terminates. Its
returned open context preserves all ancestors independently of a future
replacement at the fresh terminal node. -/
theorem trieRep_copyPathLoop {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (sourceBase : HamtHeap K V) (top : Nat)
    {source : Nat} {pairs : List (K × V)} (hr : TrieRep sourceBase source pairs) :
    CopyPathProperty same runtime top sourceBase source pairs := by
  let motiveNode := fun (source : Nat) (pairs : List (K × V))
      (_ : TrieRep sourceBase source pairs) =>
    CopyPathProperty same runtime top sourceBase source pairs
  let motiveEntries := fun (slots : List (Option (Entry K V))) (pairs : List (K × V))
      (_ : EntriesRep sourceBase slots pairs) =>
    ∀ index child, slots[index]? = some (some (.trie child)) →
      ∃ beforeSlots afterSlots beforePairs childPairs afterPairs,
        slots = beforeSlots ++ some (.trie child) :: afterSlots ∧
        index = beforeSlots.length ∧ pairs = beforePairs ++ childPairs ++ afterPairs ∧
        EntriesRep sourceBase beforeSlots beforePairs ∧ TrieRep sourceBase child childPairs ∧
        EntriesRep sourceBase afterSlots afterPairs ∧
        CopyPathProperty same runtime top sourceBase child childPairs
  have hrec : motiveNode source pairs hr := by
    refine TrieRep.rec (motive_1 := motiveNode) (motive_2 := motiveEntries)
      ?_ ?_ ?_ ?_ hr
    · intro source sourceNode slots pairs hsn hss hsb hsc hse ihEntries
      intro base heap current hbase hcopy hframe hash
      obtain ⟨sourceNode', slots', node, hsn', hss', hn, hs, hbitmap, hfreshN, hfreshD⟩ := hcopy
      have hsrcNode := (hbase.1 source (List.getElem?_eq_some_iff.mp hsn).1).trans hsn
      have hnodeEq : sourceNode' = sourceNode := Option.some.inj (hsn'.symm.trans hsrcNode)
      subst sourceNode'
      have hsrcSlots := (hbase.2 sourceNode.data (List.getElem?_eq_some_iff.mp hss).1).trans hss
      have hslotsEq : slots' = slots := Option.some.inj (hss'.symm.trans hsrcSlots)
      subst slots'
      have hb : node.bitmap < 2 ^ 32 := by rw [hbitmap]; exact hsb
      have hc : countOnes 32 node.bitmap = slots.length := by rw [hbitmap]; exact hsc
      have heBase := persistentEntriesRepFrame hbase hse
      cases hbit : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x with
      | false =>
        let result : PathResult K V := ⟨true, false, current, pathReadIndex node hash,
          BitmapIndex.fromHash hash, top, hash⟩
        refine ⟨current, hash, result, heap, base, [], pairs, [],
          copyPathLoop_terminal same runtime heap top current hash result
            (copyPathStep_absent same runtime heap top current hash node hn hbit),
          persistentHeapFrameRefl base, hframe, .root current, ?_, ?_, rfl, ?_, .root current hash⟩
        · simp only [List.nil_append, List.append_nil]
        · exact ⟨node, slots, hn, hs, hb, hc, heBase, hfreshN, hfreshD,
            rfl, rfl, rfl, hbit, rfl⟩
        · exact copyRouting_sameSlots runtime (persistentHeapFrameTrans hbase hframe)
            source current sourceNode node slots hsn hss hn hs hbitmap
      | true =>
        have hlo : 1 ≤ pathReadIndex node hash := Nat.le_add_left 1 _
        have hhi : pathReadIndex node hash ≤ slots.length := by
          unfold pathReadIndex shiftLeftNat
          rw [Nat.one_mul, ← hc]
          exact pathCountOnesPrefixLe 32 node.bitmap (BitmapIndex.fromHash hash).x
            (pathBitmapIndex_lt hash) hbit
        obtain ⟨entry, hentry⟩ := copyEntries_get hse (pathReadIndex node hash - 1) (by omega)
        cases entry with
        | leaf leaf =>
          let result : PathResult K V := ⟨same leaf.key hash.key, true, current,
            pathReadIndex node hash, BitmapIndex.fromHash hash, top, hash⟩
          refine ⟨current, hash, result, heap, base, [], pairs, [],
            copyPathLoop_terminal same runtime heap top current hash result
              (copyPathStep_leaf same runtime heap top current hash node slots leaf hn hs hentry hbit),
            persistentHeapFrameRefl base, hframe, .root current, ?_, ?_, rfl, ?_, .root current hash⟩
          · simp only [List.nil_append, List.append_nil]
          · exact ⟨node, slots, hn, hs, hb, hc, heBase, hfreshN, hfreshD,
              rfl, rfl, rfl, hbit, leaf, hentry, rfl⟩
          · exact copyRouting_sameSlots runtime (persistentHeapFrameTrans hbase hframe)
              source current sourceNode node slots hsn hss hn hs hbitmap
        | trie child =>
          obtain ⟨bs, zs, bp, cp, zp, hsplit, hindex, hpairs, hbefore, hchild, hafter, ihChild⟩ :=
            ihEntries (pathReadIndex node hash - 1) child hentry
          let parent := copyPathParentHeap heap node slots (pathReadIndex node hash)
          have hparentBase : PersistentHeapFrame base parent :=
            persistentHeapFrameVectorSet hframe node.data
              (slots.set (pathReadIndex node hash - 1) (some (.trie heap.nodes.length))) hfreshD
          have hsourceParent := persistentHeapFrameTrans hbase hparentBase
          have hsourceHeap := persistentHeapFrameTrans hbase hframe
          cases hchild with
          | node hcn hcs hcb hcc hce =>
            rename_i childNode childSlots
            have hchildNHeap :=
              (hsourceHeap.1 child (List.getElem?_eq_some_iff.mp hcn).1).trans hcn
            have hchildSHeap :=
              (hsourceHeap.2 childNode.data (List.getElem?_eq_some_iff.mp hcs).1).trans hcs
            have hchildNParent :=
              (hsourceParent.1 child (List.getElem?_eq_some_iff.mp hcn).1).trans hcn
            have hchildSParent :=
              (hsourceParent.2 childNode.data (List.getElem?_eq_some_iff.mp hcs).1).trans hcs
            have hchildCopy := copyPathNode_initial parent child childNode childSlots
              hchildNParent hchildSParent
            obtain ⟨last, finalHash, result, final, focusBase, before, focusPairs, rest,
                hloop, hfocusBase, hfinal, hcontext, hsubpairs, hterminal, htop, htransport, hrouting⟩ :=
              ihChild hsourceParent hchildCopy (contextCopiedHeapFrame parent childNode childSlots)
                (next runtime hash)
            have hparentSlots : parent.vectors[node.data]? =
                some (bs ++ some (.trie heap.nodes.length) :: zs) := by
              change (heap.vectors.set node.data
                (slots.set (pathReadIndex node hash - 1) (some (.trie heap.nodes.length))))[node.data]? = _
              rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hs).1, hsplit, hindex]
              rw [List.set_append_right _ _ (Nat.le_refl _)]
              simp only [Nat.sub_self, List.set_cons_zero]
            have hparentCount : countOnes 32 node.bitmap = bs.length + 1 + zs.length := by
              rw [hc, hsplit]
              simp only [List.length_append, List.length_cons]
              omega
            have hparentContext : TrieContext parent current heap.nodes.length bp zp := by
              have hctx := TrieContext.parent (heap := parent) (root := current)
                (child := heap.nodes.length) (focus := heap.nodes.length)
                hn hparentSlots hb hparentCount
                (persistentEntriesRepFrame hsourceParent hbefore)
                (.root heap.nodes.length) (persistentEntriesRepFrame hsourceParent hafter)
              simpa only [List.append_nil, List.nil_append] using hctx
            refine ⟨last, finalHash, result, final, focusBase,
              bp ++ before, focusPairs, rest ++ zp, ?_,
              persistentHeapFrameTrans hparentBase hfocusBase, hfinal,
              contextCompose (contextFrame hfocusBase hparentContext) hcontext, ?_, ?_, htop, ?_, ?_⟩
            · rw [persistentHamtLoopRun,
                copyPathStep_child same runtime heap top current child hash node childNode
                  slots childSlots hn hs hentry hbit hchildNHeap hchildSHeap]
              exact hloop
            · rw [hpairs, hsubpairs]
              simp only [List.append_assoc]
            · simpa only [pathNextKey] using hterminal
            · have hparentFinal := persistentHeapFrameTrans hfocusBase hfinal
              have hnodeFinal :=
                (hparentFinal.1 current (List.getElem?_eq_some_iff.mp hn).1).trans hn
              have hrawSlots : parent.vectors[node.data]? =
                  some (slots.set (pathReadIndex node hash - 1) (some (.trie heap.nodes.length))) :=
                List.getElem?_set_self (List.getElem?_eq_some_iff.mp hs).1
              have hslotsFinal :=
                (hparentFinal.2 node.data (by
                  simpa only [parent, copyPathParentHeap, List.length_set] using
                    (List.getElem?_eq_some_iff.mp hs).1)).trans hrawSlots
              exact copyRouting_replaceChild runtime
                (persistentHeapFrameTrans hsourceParent hparentFinal)
                source current child heap.nodes.length (pathReadIndex node hash - 1)
                sourceNode node slots hsn hss hnodeFinal hslotsFinal hbitmap hentry htransport
            · have hparentRouting : RoutingContext runtime parent current hash
                  heap.nodes.length (next runtime hash) := by
                refine RoutingContext.child (node := node)
                  (slots := slots.set (pathReadIndex node hash - 1) (some (.trie heap.nodes.length)))
                  hn ?_ hbit ?_ (.root heap.nodes.length (next runtime hash))
                · exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp hs).1
                · exact List.getElem?_set_self (show pathReadIndex node hash - 1 < slots.length by omega)
              exact copyRouting_contextCompose
                (copyRouting_contextFrame hfocusBase hparentRouting) hrouting
    · intro index child hget
      cases hget
    · intro leaf rest pairs hrest ih index child hget
      cases index with
      | zero => cases hget
      | succ index =>
        obtain ⟨bs, zs, bp, cp, zp, hsplit, hindex, hpairs, hb, hc, hz, hp⟩ :=
          ih index child hget
        refine ⟨some (.leaf leaf) :: bs, zs, (leaf.key, leaf.val) :: bp, cp, zp,
          ?_, ?_, ?_, .leaf (leaf := leaf) hb, hc, hz, @hp⟩
        · rw [hsplit] <;> rfl
        · simp only [List.length_cons, hindex]
        · rw [hpairs] <;> rfl
    · intro storedChild rest childPairs restPairs hchild hrest ihChild ihRest index child hget
      cases index with
      | zero =>
        cases hget
        exact ⟨[], rest, [], childPairs, restPairs, rfl, rfl, rfl,
          .nil, hchild, hrest, ihChild⟩
      | succ index =>
        obtain ⟨bs, zs, bp, cp, zp, hsplit, hindex, hpairs, hb, hc, hz, hp⟩ :=
          ihRest index child hget
        refine ⟨some (.trie storedChild) :: bs, zs, childPairs ++ bp, cp, zp,
          ?_, ?_, ?_, .trie hchild hb, hc, hz, @hp⟩
        · rw [hsplit] <;> rfl
        · simp only [List.length_cons, hindex]
        · rw [hpairs]
          simp only [List.append_assoc]
  exact @hrec

/-- The actual frozen copying path returns a preserved ancestor context and
a fresh terminal focus. The reference leaf list is decomposed independently of
the path implementation. -/
theorem trieRep_copyPathFocus {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V)
    {root : Nat} {pairs : List (K × V)} (hr : TrieRep heap root pairs)
    (hash : HashState K) :
    ∃ result after focusBase before focusPairs rest,
      runHamt (path heapVectorOps same runtime root hash true) heap = (.ok result, after) ∧
      PersistentHeapFrame heap focusBase ∧ PersistentHeapFrame focusBase after ∧
      TrieContext focusBase result.top result.trie before rest ∧
      pairs = before ++ focusPairs ++ rest ∧
      CopyPathTerminal same hash.key focusBase after result focusPairs ∧
      result.top = heap.nodes.length ∧ RouteTransport runtime heap root after result.top ∧
      RoutingContext runtime focusBase result.top hash result.trie result.hash := by
  obtain ⟨node, slots, hn, hs, _⟩ := contextCopiedTrieRep hr
  obtain ⟨last, finalHash, result, after, focusBase, before, focusPairs, rest,
      hloop, hbase, hfinal, hcontext, hpairs, hterminal, htop, htransport, hrouting⟩ :=
    trieRep_copyPathLoop same runtime heap heap.nodes.length hr
      (persistentHeapFrameRefl heap) (copyPathNode_initial heap root node slots hn hs)
      (contextCopiedHeapFrame heap node slots) hash
  refine ⟨result, after, focusBase, before, focusPairs, rest,
    ?_, hbase, hfinal, ?_, hpairs, hterminal, htop, ?_, ?_⟩
  · rw [path.eq_1]
    simp only [ite_true]
    rw [persistentHamtBindRun, pathReadNodeRun heap root node hn]
    dsimp only
    rw [persistentHamtBindRun, contextVectorCopyRun heap node.data slots hs]
    dsimp only
    rw [persistentHamtBindRun, contextInnerRun]
    simp only [ForIn.forIn]
    change runHamt (do
      let final ← Lean.Loop.forIn (m := HamtM K V)
        (β := Nat × HashState K × Option (PathResult K V)) ({} : Lean.Loop)
        (heap.nodes.length, hash, none) (copyPathForInBody same runtime heap.nodes.length)
      match final.2.2 with
      | some r => pure r
      | none => throw HamtError.bounds) (contextCopiedHeap heap node slots) = _
    rw [copyPathForInBody_eq, persistentHamtBindRun, hloop] <;> rfl
  · rw [htop]
    exact hcontext
  · rw [htop]
    exact htransport
  · rw [htop]
    exact hrouting

/-- Copying a path terminates, preserves every older heap record, and preserves
the entire independently specified leaf list at the returned new root. -/
theorem trieRep_copyPathRun {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V)
    {root : Nat} {pairs : List (K × V)} (hr : TrieRep heap root pairs)
    (hash : HashState K) :
    ∃ result after,
      runHamt (path heapVectorOps same runtime root hash true) heap = (.ok result, after) ∧
      PersistentHeapFrame heap after ∧ TrieRep after result.top pairs ∧
      result.top = heap.nodes.length := by
  obtain ⟨result, after, focusBase, before, focusPairs, rest,
      hrun, hbase, hfinal, hcontext, hpairs, hterminal, htop, _, _⟩ :=
    trieRep_copyPathFocus same runtime heap hr hash
  obtain ⟨node, slots, hn, hs, hb, hc, he, _⟩ := hterminal
  have hfocus : TrieRep after result.trie focusPairs :=
    .node hn hs hb hc (persistentEntriesRepFrame hfinal he)
  refine ⟨result, after, hrun, persistentHeapFrameTrans hbase hfinal, ?_, htop⟩
  rw [hpairs]
  exact contextReplace hfinal hcontext hfocus

/-- Copying also preserves every stored key's hash route, so the independent
routing invariant needed for lookup completeness survives the operation. -/
theorem trieRep_copyPathRouted {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V)
    {root : Nat} {pairs : List (K × V)} (hr : TrieRep heap root pairs)
    (hs : StoredRouting runtime heap root pairs) (hash : HashState K) :
    ∃ result after,
      runHamt (path heapVectorOps same runtime root hash true) heap = (.ok result, after) ∧
      PersistentHeapFrame heap after ∧ TrieRep after result.top pairs ∧
      StoredRouting runtime after result.top pairs ∧ result.top = heap.nodes.length := by
  obtain ⟨result, after, focusBase, before, focusPairs, rest,
      hrun, hbase, hfinal, hcontext, hpairs, hterminal, htop, htransport, _⟩ :=
    trieRep_copyPathFocus same runtime heap hr hash
  obtain ⟨node, slots, hn, hslots, hb, hc, he, _⟩ := hterminal
  have hfocus : TrieRep after result.trie focusPairs :=
    .node hn hslots hb hc (persistentEntriesRepFrame hfinal he)
  refine ⟨result, after, hrun, persistentHeapFrameTrans hbase hfinal, ?_,
    copyRouting_stored htransport hs, htop⟩
  rw [hpairs]
  exact contextReplace hfinal hcontext hfocus

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: CopyPathClassification.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

theorem copyEntries_leafMem {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) {index : Nat} {leaf : Leaf K V}
    (hg : slots[index]? = some (some (.leaf leaf))) : (leaf.key, leaf.val) ∈ pairs := by
  induction index generalizing slots pairs with
  | zero =>
    cases hr with
    | nil => cases hg
    | leaf _ => cases hg; exact List.mem_cons_self
    | trie _ _ => cases hg
  | succ index ih =>
    cases hr with
    | nil => cases hg
    | leaf ht => exact List.mem_cons_of_mem _ (ih ht hg)
    | trie _ ht => exact List.mem_append_right _ (ih ht hg)

/-- Any route reaching a certified terminal focus forces an occupied leaf and
identifies the found flag with that leaf's comparison to the original query. -/
theorem copyTerminal_ofRoute {K V : Type} {same : K → K → Bool}
    {runtime : HamtObjectIdRuntime K} {query : K} {base after : HamtHeap K V}
    {result : PathResult K V} {pairs : List (K × V)}
    (ht : CopyPathTerminal same query base after result pairs) {leaf : Leaf K V}
    (hr : RoutedLeaf runtime after result.trie result.hash leaf) :
    result.present = true ∧ result.found = same leaf.key query := by
  obtain ⟨node, slots, hn, hs, _, _, _, _, _, _, hbi, hi, hbit, hslot⟩ := ht
  cases hp : result.present with
  | false =>
    have hclear : Nat.testBit node.bitmap (BitmapIndex.fromHash result.hash).x = false := by
      rw [← hbi, hbit, hp]
    exact (routedLeaf_absentAt node hn hclear hr).elim
  | true =>
    simp only [hp, ite_true] at hslot
    obtain ⟨stored, hg, hf⟩ := hslot
    have hg' : slots[pathReadIndex node result.hash - 1]? = some (some (.leaf stored)) := by
      simpa only [hi] using hg
    have heq := routedLeaf_leafAt node slots hn hs hg' hr
    exact ⟨rfl, by simpa only [heq] using hf⟩

/-- A reference pair equal to the query must be reported found and present by
its copied terminal focus; the proof follows only independent stored routes. -/
theorem copyFocus_matchFlags {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    {query : K} {base after : HamtHeap K V} {result : PathResult K V}
    {focusPairs pairs : List (K × V)}
    (hf : PersistentHeapFrame base after)
    (ht : CopyPathTerminal same query base after result focusPairs)
    (hc : RoutingContext runtime base result.top (HashState.fromKey runtime query)
      result.trie result.hash)
    (hs : StoredRouting runtime after result.top pairs)
    (pair : K × V) (hm : pair ∈ pairs) (he : same query pair.1 = true) :
    result.found = true ∧ result.present = true := by
  have hsame := hl.symm query pair.1 he
  have hr := hs pair.1 pair.2 hm
  have hquery := routedLeaf_hashEq hr
    (routingHashEq_initial runtime pair.1 query (hl.hash_eq pair.1 query hsame))
  have hfocus := copyRouting_contextPullback (copyRouting_contextFrame hf hc) hquery
  obtain ⟨hp, hfound⟩ := copyTerminal_ofRoute ht hfocus
  exact ⟨hfound.trans hsame, hp⟩

/-- A miss at the copied focus excludes the query's entire equality class from
the independent reference pair sequence. -/
theorem copyFocus_missing {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    {query : K} {base after : HamtHeap K V} {result : PathResult K V}
    {focusPairs pairs : List (K × V)}
    (hf : PersistentHeapFrame base after)
    (ht : CopyPathTerminal same query base after result focusPairs)
    (hc : RoutingContext runtime base result.top (HashState.fromKey runtime query)
      result.trie result.hash)
    (hs : StoredRouting runtime after result.top pairs)
    (hmiss : (result.found && result.present) = false) :
    ∀ pair ∈ pairs, same query pair.1 = false := by
  intro pair hm
  cases he : same query pair.1 with
  | false => rfl
  | true =>
    have hflags := copyFocus_matchFlags same runtime hl hf ht hc hs pair hm he
    rw [hflags.1, hflags.2] at hmiss
    cases hmiss

theorem copyFocus_missingReference {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    {query : K} {base after : HamtHeap K V} {result : PathResult K V}
    {focusPairs pairs reference : List (K × V)}
    (hf : PersistentHeapFrame base after)
    (ht : CopyPathTerminal same query base after result focusPairs)
    (hc : RoutingContext runtime base result.top (HashState.fromKey runtime query)
      result.trie result.hash)
    (hs : StoredRouting runtime after result.top pairs) (hp : List.Perm pairs reference)
    (hmiss : (result.found && result.present) = false) :
    rfind same reference query = none := by
  apply rfind_none
  intro pair hm
  exact copyFocus_missing same runtime hl hf ht hc hs hmiss pair (hp.mem_iff.2 hm)

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: PersistentLocalEdits.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Setting a previously clear bit adds one to a finite bitmap population. -/
theorem persistentCountSetBit (n x i : Nat) (hi : i < n)
    (hbit : Nat.testBit x i = false) :
    countOnes n (x ||| 2 ^ i) = countOnes n x + 1 := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      have hx0 : x % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx1
        · exact hx0
        · simp only [Nat.testBit_zero, hx1, decide_true, Bool.true_eq_false] at hbit
      have hlow : (x ||| 1) % 2 = 1 := by
        rw [Nat.or_mod_two_eq_one]
        simp [hx0]
      have hdiv : (x ||| 1) / 2 = x / 2 := by
        rw [Nat.or_div_two]
        simp
      simp only [countOnes]
      rw [hlow, hdiv, hx0]
      omega
    | succ i =>
      have hbit' : Nat.testBit (x / 2) i = false := by
        simpa only [Nat.testBit_succ] using hbit
      have hpowMod : (2 ^ (i + 1)) % 2 = 0 := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
      have hlow : (x ||| 2 ^ (i + 1)) % 2 = x % 2 := by
        change (x ||| 2 ^ (i + 1)) % 2 ^ 1 = x % 2 ^ 1
        rw [Nat.or_mod_two_pow]
        simp only [Nat.pow_one, hpowMod, Nat.or_zero]
      have hpowDiv : (2 ^ (i + 1)) / 2 = 2 ^ i := by
        rw [Nat.pow_succ]
        simp
      have hdiv : (x ||| 2 ^ (i + 1)) / 2 = x / 2 ||| 2 ^ i := by
        rw [Nat.or_div_two, hpowDiv]
      simp only [countOnes, hlow, hdiv]
      have htail := ih (x / 2) i (by omega) hbit'
      omega

theorem persistentBitmapSetExisting (bitmap bit : Nat)
    (hbound : bitmap < 2 ^ 32) (hbit : Nat.testBit bitmap bit = true) :
    u32 (bitmap ||| shiftLeftNat 1 bit) = bitmap := by
  have hor : bitmap ||| 2 ^ bit = bitmap := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or]
    by_cases heq : i = bit
    · subst i
      simp only [hbit, Bool.true_or]
    · have hne : bit ≠ i := fun h => heq h.symm
      simp only [Nat.testBit_two_pow, hne, decide_false, Bool.or_false]
  change (bitmap ||| 1 * 2 ^ bit) % 2 ^ 32 = bitmap
  rw [Nat.one_mul, hor]
  exact Nat.mod_eq_of_lt hbound

theorem persistentBitmapSetNew (bitmap bit : Nat)
    (hbound : bitmap < 2 ^ 32) (hbi : bit < 32)
    (hbit : Nat.testBit bitmap bit = false) :
    u32 (bitmap ||| shiftLeftNat 1 bit) < 2 ^ 32 ∧
      countOnes 32 (u32 (bitmap ||| shiftLeftNat 1 bit)) = countOnes 32 bitmap + 1 := by
  have hpow : 2 ^ bit < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hbi
  have hor : bitmap ||| 2 ^ bit < 2 ^ 32 := Nat.or_lt_two_pow hbound hpow
  have hval : u32 (bitmap ||| shiftLeftNat 1 bit) = bitmap ||| 2 ^ bit := by
    change (bitmap ||| 1 * 2 ^ bit) % 2 ^ 32 = bitmap ||| 2 ^ bit
    rw [Nat.one_mul]
    exact Nat.mod_eq_of_lt hor
  rw [hval]
  exact ⟨hor, persistentCountSetBit 32 bitmap bit hbi hbit⟩

/-- Clearing one occupied position removes one bitmap bit and preserves all
other positions. The statement concerns finite natural-number bitmaps only. -/
theorem persistentBitmapClear (bitmap bit : Nat)
    (hbound : bitmap < 2 ^ 32) (hbi : bit < 32)
    (hbit : Nat.testBit bitmap bit = true) :
    let cleared := bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)
    cleared < 2 ^ 32 ∧
      countOnes 32 bitmap = countOnes 32 cleared + 1 ∧
      (∀ i, i ≠ bit → Nat.testBit cleared i = Nat.testBit bitmap i) := by
  let cleared := bitmap &&& (MASK32 ^^^ 2 ^ bit)
  have hmaskAt : Nat.testBit MASK32 bit = true := by
    change Nat.testBit (2 ^ 32 - 1) bit = true
    simpa only [hbi, decide_true] using Nat.testBit_two_pow_sub_one 32 bit
  have hclearBit : Nat.testBit cleared bit = false := by
    simp only [cleared, Nat.testBit_and, Nat.testBit_xor, hmaskAt, hbit,
      Nat.testBit_two_pow, decide_true, Bool.xor_self, Bool.and_false]
  have hrestore : bitmap = cleared ||| 2 ^ bit := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases heq : i = bit
    · subst i
      simp only [Nat.testBit_or, hbit, hclearBit, Nat.testBit_two_pow,
        decide_true, Bool.or_true]
    · have hpowne : bit ≠ i := fun h => heq h.symm
      by_cases hlow : i < 32
      · have hmask : Nat.testBit MASK32 i = true := by
          change Nat.testBit (2 ^ 32 - 1) i = true
          simpa only [hlow, decide_true] using Nat.testBit_two_pow_sub_one 32 i
        simp only [cleared, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
          Nat.testBit_two_pow, hpowne, decide_false, hmask, Bool.xor_false,
          Bool.and_true, Bool.or_false]
      · have hbitmap : Nat.testBit bitmap i = false :=
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hbound (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
        simp only [cleared, Nat.testBit_or, Nat.testBit_and, hbitmap,
          Nat.testBit_two_pow, hpowne, decide_false, Bool.false_and, Bool.false_or]
  have hclearedBound : cleared < 2 ^ 32 :=
    Nat.lt_of_le_of_lt Nat.and_le_left hbound
  have hcount : countOnes 32 bitmap = countOnes 32 cleared + 1 := by
    rw [hrestore]
    exact persistentCountSetBit 32 cleared bit hbi hclearBit
  have hpreserve : ∀ i, i ≠ bit → Nat.testBit cleared i = Nat.testBit bitmap i := by
    intro i hne
    rw [hrestore, Nat.testBit_or]
    have hpowne : bit ≠ i := fun h => hne h.symm
    simp only [Nat.testBit_two_pow, hpowne, decide_false, Bool.or_false]
  simpa only [shiftLeftNat, Nat.one_mul] using And.intro hclearedBound (And.intro hcount hpreserve)

theorem persistentLengthInsert {A : Type} (xs : List A) (i : Nat) (x : A)
    (hi : i ≤ xs.length) : (xs.insertIdx i x).length = xs.length + 1 := by
  exact List.length_insertIdx_of_le_length hi x

theorem persistentLengthErase {A : Type} (xs : List A) (i : Nat)
    (hi : i < xs.length) : (xs.eraseIdx i).length + 1 = xs.length := by
  induction xs generalizing i with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hi
  | cons first rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < rest.length := by
        simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have hh := ih i hi'
      simp only [List.eraseIdx, List.length_cons]
      omega

/-- Replace one existing leaf in a freshly copied focus, preserving the
entire original heap and giving its exact resulting flattened sequence. -/
theorem persistentFocusReplaceLeaf {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap) (root data bitmap i : Nat)
    (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (old new : Leaf K V)
    (hroot : root < heap.nodes.length) (hdata : data < heap.vectors.length)
    (hfreshRoot : base.nodes.length ≤ root) (hfreshData : base.vectors.length ≤ data)
    (hbitmap : bitmap < 2 ^ 32) (hcount : countOnes 32 bitmap = slots.length)
    (hentries : EntriesRep base slots pairs)
    (hget : slots[i]? = some (some (.leaf old))) :
    ∃ before after,
      pairs = before ++ (old.key, old.val) :: after ∧
      let result : HamtHeap K V :=
        { vectors := heap.vectors.set data (slots.set i (some (.leaf new))),
          nodes := heap.nodes.set root ⟨data, bitmap⟩ }
      PersistentHeapFrame base result ∧
        TrieRep result root (before ++ (new.key, new.val) :: after) := by
  obtain ⟨before, after, hp, he⟩ := persistentEntriesReplaceLeaf hentries hget new
  refine ⟨before, after, hp, ?_⟩
  exact persistentFreshFocusRep hframe root data bitmap _ _ hroot hdata
    hfreshRoot hfreshData hbitmap (by simpa only [List.length_set] using hcount) he

/-- Insert one leaf into a fresh focus at a new occupied bitmap position. -/
theorem persistentFocusInsertLeaf {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap) (root data bitmap bit i : Nat)
    (slots : List (Option (Entry K V))) (pairs : List (K × V)) (new : Leaf K V)
    (hroot : root < heap.nodes.length) (hdata : data < heap.vectors.length)
    (hfreshRoot : base.nodes.length ≤ root) (hfreshData : base.vectors.length ≤ data)
    (hbitmap : bitmap < 2 ^ 32) (hcount : countOnes 32 bitmap = slots.length)
    (hentries : EntriesRep base slots pairs) (hi : i ≤ slots.length)
    (hbi : bit < 32) (hbit : Nat.testBit bitmap bit = false) :
    ∃ before after, pairs = before ++ after ∧
      let newBitmap := u32 (bitmap ||| shiftLeftNat 1 bit)
      let result : HamtHeap K V :=
        { vectors := heap.vectors.set data (slots.insertIdx i (some (.leaf new))),
          nodes := heap.nodes.set root ⟨data, newBitmap⟩ }
      PersistentHeapFrame base result ∧
        TrieRep result root (before ++ (new.key, new.val) :: after) := by
  obtain ⟨before, after, hp, he⟩ := persistentEntriesInsertLeaf hentries i hi new
  obtain ⟨hnewBound, hnewCount⟩ := persistentBitmapSetNew bitmap bit hbitmap hbi hbit
  refine ⟨before, after, hp, ?_⟩
  apply persistentFreshFocusRep hframe root data _ _ _ hroot hdata
    hfreshRoot hfreshData hnewBound _ he
  rw [hnewCount, hcount, persistentLengthInsert slots i _ hi]

/-- Delete one leaf from a fresh focus and clear its occupied bitmap bit. -/
theorem persistentFocusEraseLeaf {K V : Type} {base heap : HamtHeap K V}
    (hframe : PersistentHeapFrame base heap) (root data bitmap bit i : Nat)
    (slots : List (Option (Entry K V))) (pairs : List (K × V)) (old : Leaf K V)
    (hroot : root < heap.nodes.length) (hdata : data < heap.vectors.length)
    (hfreshRoot : base.nodes.length ≤ root) (hfreshData : base.vectors.length ≤ data)
    (hbitmap : bitmap < 2 ^ 32) (hcount : countOnes 32 bitmap = slots.length)
    (hentries : EntriesRep base slots pairs)
    (hget : slots[i]? = some (some (.leaf old)))
    (hbi : bit < 32) (hbit : Nat.testBit bitmap bit = true) :
    ∃ before after, pairs = before ++ (old.key, old.val) :: after ∧
      let newBitmap := bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)
      let result : HamtHeap K V :=
        { vectors := heap.vectors.set data (slots.eraseIdx i),
          nodes := heap.nodes.set root ⟨data, newBitmap⟩ }
      PersistentHeapFrame base result ∧ TrieRep result root (before ++ after) := by
  obtain ⟨before, after, hp, he⟩ := persistentEntriesEraseLeaf hentries hget
  obtain ⟨hnewBound, hnewCount, _⟩ := persistentBitmapClear bitmap bit hbitmap hbi hbit
  have hi : i < slots.length := (List.getElem?_eq_some_iff.mp hget).1
  have hlen := persistentLengthErase slots i hi
  refine ⟨before, after, hp, ?_⟩
  apply persistentFreshFocusRep hframe root data _ _ _ hroot hdata
    hfreshRoot hfreshData hnewBound _ he
  omega

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: PersistentBitmapRanks.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- The zero-based vector position determined by a bitmap prefix. -/
def persistentBitmapRank (bitmap bit : Nat) : Nat :=
  countOnes 32 (bitmap &&& (2 ^ bit - 1))

theorem persistentCountAndLe (n x y : Nat) :
    countOnes n (x &&& y) ≤ countOnes n x := by
  induction n generalizing x y with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hlow : (x &&& y) % 2 ≤ x % 2 := by
      change (x &&& y) % 2 ^ 1 ≤ x % 2 ^ 1
      rw [Nat.and_mod_two_pow]
      exact Nat.and_le_left
    change (x &&& y) % 2 + countOnes n ((x &&& y) / 2) ≤
      x % 2 + countOnes n (x / 2)
    rw [Nat.and_div_two]
    exact Nat.add_le_add hlow (ih _ _)

theorem persistentPrefixMaskNested (small large : Nat) (hle : small ≤ large) :
    (2 ^ large - 1) &&& (2 ^ small - 1) = 2 ^ small - 1 := by
  rw [Nat.and_comm]
  apply Nat.and_two_pow_sub_one_of_lt_two_pow
  have hp := Nat.pow_le_pow_right Nat.zero_lt_two hle
  have hz := Nat.two_pow_pos small
  omega

theorem persistentRankMono (bitmap a b : Nat) (hab : a ≤ b) :
    persistentBitmapRank bitmap a ≤ persistentBitmapRank bitmap b := by
  have hmask : (bitmap &&& (2 ^ b - 1)) &&& (2 ^ a - 1) =
      bitmap &&& (2 ^ a - 1) := by
    rw [Nat.and_assoc, persistentPrefixMaskNested a b hab]
  have h := persistentCountAndLe 32 (bitmap &&& (2 ^ b - 1)) (2 ^ a - 1)
  rw [hmask] at h
  exact h

/-- An occupied earlier bit has a strictly smaller vector position. -/
theorem persistentRankStrict (bitmap a b : Nat) (ha : a < 32) (hab : a < b)
    (hbit : Nat.testBit bitmap a = true) :
    persistentBitmapRank bitmap a < persistentBitmapRank bitmap b := by
  have hmaskBit : Nat.testBit (bitmap &&& (2 ^ b - 1)) a = true := by
    simp only [Nat.testBit_and, hbit, Nat.testBit_two_pow_sub_one, hab,
      decide_true, Bool.and_self]
  have hmask : (bitmap &&& (2 ^ b - 1)) &&& (2 ^ a - 1) =
      bitmap &&& (2 ^ a - 1) := by
    rw [Nat.and_assoc, persistentPrefixMaskNested a b (Nat.le_of_lt hab)]
  have h := pathCountOnesPrefixLe 32 (bitmap &&& (2 ^ b - 1)) a ha hmaskBit
  rw [hmask] at h
  exact h

theorem persistentPowPrefixMask (bit query : Nat) :
    2 ^ bit &&& (2 ^ query - 1) = if bit < query then 2 ^ bit else 0 := by
  by_cases hlt : bit < query
  · rw [if_pos hlt]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow
      (Nat.pow_lt_pow_right (by decide) hlt)
  · rw [if_neg hlt]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases heq : bit = i
    · subst i
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true,
        Nat.testBit_two_pow_sub_one, hlt, decide_false, Bool.and_false,
        Nat.zero_testBit]
    · simp only [Nat.testBit_and, Nat.testBit_two_pow, heq, decide_false,
        Bool.false_and, Nat.zero_testBit]

/-- Adding a fresh bitmap bit shifts precisely the positions after that bit. -/
theorem persistentRankOrNew (bitmap bit query : Nat) (hbi : bit < 32)
    (hbit : Nat.testBit bitmap bit = false) :
    persistentBitmapRank (bitmap ||| 2 ^ bit) query =
      persistentBitmapRank bitmap query + (if bit < query then 1 else 0) := by
  unfold persistentBitmapRank
  rw [Nat.and_or_distrib_right, persistentPowPrefixMask]
  by_cases hlt : bit < query
  · simp only [if_pos hlt]
    apply persistentCountSetBit 32 _ bit hbi
    simp only [Nat.testBit_and, hbit, Bool.false_and]
  · simp only [if_neg hlt, Nat.or_zero, Nat.add_zero]

theorem persistentRankSetNew (bitmap bit query : Nat)
    (hbound : bitmap < 2 ^ 32) (hbi : bit < 32)
    (hbit : Nat.testBit bitmap bit = false) :
    persistentBitmapRank (u32 (bitmap ||| shiftLeftNat 1 bit)) query =
      persistentBitmapRank bitmap query + (if bit < query then 1 else 0) := by
  have hraw : u32 (bitmap ||| shiftLeftNat 1 bit) = bitmap ||| 2 ^ bit := by
    change (bitmap ||| 1 * 2 ^ bit) % 2 ^ 32 = _
    rw [Nat.one_mul]
    exact Nat.mod_eq_of_lt
      (Nat.or_lt_two_pow hbound (Nat.pow_lt_pow_right (by decide) hbi))
  rw [hraw]
  exact persistentRankOrNew bitmap bit query hbi hbit

theorem persistentBitmapSetTestBit (bitmap bit query : Nat)
    (hbound : bitmap < 2 ^ 32) (hbi : bit < 32) :
    Nat.testBit (u32 (bitmap ||| shiftLeftNat 1 bit)) query =
      (Nat.testBit bitmap query || decide (bit = query)) := by
  have hraw : u32 (bitmap ||| shiftLeftNat 1 bit) = bitmap ||| 2 ^ bit := by
    change (bitmap ||| 1 * 2 ^ bit) % 2 ^ 32 = _
    rw [Nat.one_mul]
    exact Nat.mod_eq_of_lt
      (Nat.or_lt_two_pow hbound (Nat.pow_lt_pow_right (by decide) hbi))
  rw [hraw, Nat.testBit_or, Nat.testBit_two_pow]

theorem persistentRankClear (bitmap bit query : Nat)
    (hbound : bitmap < 2 ^ 32) (hbi : bit < 32)
    (hbit : Nat.testBit bitmap bit = true) :
    persistentBitmapRank bitmap query =
      persistentBitmapRank (bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)) query +
        (if bit < query then 1 else 0) := by
  let cleared := bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)
  obtain ⟨_, _, hpreserve⟩ := persistentBitmapClear bitmap bit hbound hbi hbit
  have hmask : Nat.testBit MASK32 bit = true := by
    change Nat.testBit (2 ^ 32 - 1) bit = true
    simpa only [hbi, decide_true] using Nat.testBit_two_pow_sub_one 32 bit
  have hclear : Nat.testBit cleared bit = false := by
    simp only [cleared, shiftLeftNat, Nat.one_mul, Nat.testBit_and,
      Nat.testBit_xor, hbit, hmask, Nat.testBit_two_pow, decide_true,
      Bool.xor_self, Bool.and_false]
  have hrestore : bitmap = cleared ||| 2 ^ bit := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or]
    by_cases heq : i = bit
    · subst i
      simp only [hbit, hclear, Nat.testBit_two_pow, decide_true, Bool.or_true]
    · have hne : bit ≠ i := fun h => heq h.symm
      rw [hpreserve i heq]
      simp only [Nat.testBit_two_pow, hne, decide_false, Bool.or_false]
  change persistentBitmapRank bitmap query = persistentBitmapRank cleared query +
    (if bit < query then 1 else 0)
  rw [hrestore]
  exact persistentRankOrNew cleared bit query hbi hclear

/-- The vector cell of every other occupied bit survives insertion at the
new bit's rank, with its rank adjusted by the bitmap calculation. -/
theorem persistentInsertRankEntry {A : Type} (slots : List A) (entry : A)
    (bitmap bit query : Nat) (hbound : bitmap < 2 ^ 32)
    (hbi : bit < 32) (hq : query < 32)
    (hclear : Nat.testBit bitmap bit = false)
    (hpresent : Nat.testBit bitmap query = true) (hne : bit ≠ query) :
    (slots.insertIdx (persistentBitmapRank bitmap bit) entry)[
      persistentBitmapRank (u32 (bitmap ||| shiftLeftNat 1 bit)) query]? =
      slots[persistentBitmapRank bitmap query]? := by
  rw [persistentRankSetNew bitmap bit query hbound hbi hclear]
  by_cases hlt : bit < query
  · rw [if_pos hlt]
    have hrank := persistentRankMono bitmap bit query (Nat.le_of_lt hlt)
    rw [List.getElem?_insertIdx_of_gt (by omega :
      persistentBitmapRank bitmap bit < persistentBitmapRank bitmap query + 1)]
    rw [Nat.add_sub_cancel]
  · have hbefore : query < bit := by omega
    rw [if_neg hlt, Nat.add_zero]
    exact List.getElem?_insertIdx_of_lt
      (persistentRankStrict bitmap query bit hq hbefore hpresent)

/-- Removing one occupied bitmap position preserves every other occupied
position's vector cell after the corresponding rank shift. -/
theorem persistentEraseRankEntry {A : Type} (slots : List A)
    (bitmap bit query : Nat) (hbound : bitmap < 2 ^ 32)
    (hbi : bit < 32) (hq : query < 32)
    (hbit : Nat.testBit bitmap bit = true)
    (hpresent : Nat.testBit bitmap query = true) (hne : bit ≠ query) :
    (slots.eraseIdx (persistentBitmapRank bitmap bit))[
      persistentBitmapRank (bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)) query]? =
      slots[persistentBitmapRank bitmap query]? := by
  have hrank := persistentRankClear bitmap bit query hbound hbi hbit
  by_cases hlt : bit < query
  · rw [if_pos hlt] at hrank
    have hstrict := persistentRankStrict bitmap bit query hbi hlt hbit
    have hindex : persistentBitmapRank bitmap bit ≤
        persistentBitmapRank (bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)) query := by omega
    rw [List.getElem?_eraseIdx_of_ge hindex, ← hrank]
  · rw [if_neg hlt, Nat.add_zero] at hrank
    have hbefore : query < bit := by omega
    have hstrict := persistentRankStrict bitmap query bit hq hbefore hpresent
    rw [← hrank]
    exact List.getElem?_eraseIdx_of_lt hstrict

theorem persistentReplaceRankEntry {A : Type} (slots : List A) (entry : A)
    (bitmap bit query : Nat) (hbi : bit < 32) (hq : query < 32)
    (hbit : Nat.testBit bitmap bit = true)
    (hpresent : Nat.testBit bitmap query = true) (hne : bit ≠ query) :
    (slots.set (persistentBitmapRank bitmap bit) entry)[persistentBitmapRank bitmap query]? =
      slots[persistentBitmapRank bitmap query]? := by
  have hneq : persistentBitmapRank bitmap bit ≠ persistentBitmapRank bitmap query := by
    by_cases hlt : bit < query
    · have hstrict := persistentRankStrict bitmap bit query hbi hlt hbit
      omega
    · have hstrict := persistentRankStrict bitmap query bit hq (by omega) hpresent
      omega
  exact List.getElem?_set_ne hneq

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: PersistentReferenceEdits.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict

theorem persistentReferenceDeleteAbsent {K V : Type} (same : K → K → Bool)
    (pairs : List (K × V)) (key : K)
    (hmissing : ∀ pair ∈ pairs, same key pair.1 = false) :
    rdel same pairs key = pairs := by
  unfold rdel
  apply List.filter_eq_self.mpr
  intro pair hp
  rw [hmissing pair hp]
  rfl

/-- On a distinct pair list, removing the equality class of a selected pair
removes exactly that one occurrence, wherever it occurs in vector order. -/
theorem persistentReferenceDeleteOne {K V : Type}
    {hash : K → JInt .u64} {same : K → K → Bool} (hl : KeyLaws hash same)
    (before after : List (K × V)) (old : K × V) (key : K)
    (hd : Distinct same (before ++ old :: after)) (heq : same old.1 key = true) :
    rdel same (before ++ old :: after) key = before ++ after := by
  have hperm : List.Perm (before ++ old :: after) (old :: (before ++ after)) :=
    List.perm_middle
  have hhead := (List.pairwise_cons.mp (hd.perm hl hperm)).1
  have hmissing : ∀ pair ∈ before ++ after, same key pair.1 = false := by
    intro pair hp
    cases hs : same key pair.1 with
    | false => rfl
    | true =>
      have hbad := hhead pair hp
      rw [hl.trans old.1 key pair.1 heq hs] at hbad
      cases hbad
  have hb : rdel same before key = before :=
    persistentReferenceDeleteAbsent same before key
      (fun pair hp => hmissing pair (List.mem_append_left _ hp))
  have ha : rdel same after key = after :=
    persistentReferenceDeleteAbsent same after key
      (fun pair hp => hmissing pair (List.mem_append_right _ hp))
  have hreverse := hl.symm old.1 key heq
  unfold rdel
  rw [List.filter_append, List.filter_cons]
  simp only [hreverse, Bool.not_true, Bool.false_eq_true, ite_false]
  change rdel same before key ++ rdel same after key = before ++ after
  rw [hb, ha]

theorem persistentReferenceReplacePerm {K V : Type}
    {hash : K → JInt .u64} {same : K → K → Bool} (hl : KeyLaws hash same)
    (before after : List (K × V)) (old : K × V) (key : K) (value : V)
    (hd : Distinct same (before ++ old :: after)) (heq : same old.1 key = true) :
    List.Perm (before ++ (key, value) :: after)
      (rset same (before ++ old :: after) key value) := by
  unfold rset
  rw [persistentReferenceDeleteOne hl before after old key hd heq]
  exact List.perm_middle

theorem persistentReferenceInsertPerm {K V : Type} (same : K → K → Bool)
    (before after : List (K × V)) (key : K) (value : V)
    (hmissing : ∀ pair ∈ before ++ after, same key pair.1 = false) :
    List.Perm (before ++ (key, value) :: after)
      (rset same (before ++ after) key value) := by
  unfold rset
  rw [persistentReferenceDeleteAbsent same (before ++ after) key hmissing]
  exact List.perm_middle

theorem persistentReferenceDeletePerm {K V Q : Type} (same : Q → K → Bool)
    {pairs reference : List (K × V)} (hp : List.Perm pairs reference) (key : Q) :
    List.Perm (rdel same pairs key) (rdel same reference key) := by
  unfold rdel
  exact hp.filter (fun (pair : K × V) => !(same key pair.1))

theorem persistentReferenceSetPerm {K V : Type} (same : K → K → Bool)
    {pairs reference : List (K × V)} (hp : List.Perm pairs reference)
    (key : K) (value : V) :
    List.Perm (rset same pairs key value) (rset same reference key value) :=
  (persistentReferenceDeletePerm same hp key).cons (key, value)

/-- Growing a collision leaf into any finite child tree that contains the
old pairs and one new pair has the correct reference-map effect. -/
theorem persistentReferenceGrowPerm {K V : Type} (same : K → K → Bool)
    (before after oldPairs newPairs : List (K × V)) (key : K) (value : V)
    (hnew : List.Perm newPairs ((key, value) :: oldPairs))
    (hmissing : ∀ pair ∈ before ++ oldPairs ++ after, same key pair.1 = false) :
    List.Perm (before ++ newPairs ++ after)
      (rset same (before ++ oldPairs ++ after) key value) := by
  unfold rset
  rw [persistentReferenceDeleteAbsent same (before ++ oldPairs ++ after) key hmissing]
  have hinside : List.Perm (before ++ newPairs ++ after)
      (before ++ ((key, value) :: oldPairs) ++ after) := by
    simpa only [List.append_assoc] using (hnew.append_left before).append_right after
  apply hinside.trans
  simpa only [List.append_assoc, List.cons_append] using
    (List.perm_middle (a := (key, value)) (l₁ := before) (l₂ := oldPairs ++ after))

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: LocalRoutingWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- The selected one-based path index has the bitmap rank as its predecessor. -/
theorem localRoutingIndexRank {K V : Type} (node : HAMTNode K V) (hash : HashState K) :
    pathReadIndex node hash - 1 =
      persistentBitmapRank node.bitmap (BitmapIndex.fromHash hash).x := by
  simp only [pathReadIndex, persistentBitmapRank, shiftLeftNat, Nat.one_mul,
    Nat.add_sub_cancel, Nat.land_eq]

/-- Every child referenced by a represented entry list has its own finite representation. -/
theorem localRoutingChildRep {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hrep : EntriesRep heap slots pairs) {index child : Nat}
    (hg : slots[index]? = some (some (.trie child))) :
    ∃ childPairs, TrieRep heap child childPairs := by
  induction index generalizing slots pairs with
  | zero =>
    cases hrep with
    | nil => cases hg
    | leaf _ => cases hg
    | trie hc _ => cases hg; exact ⟨_, hc⟩
  | succ index ih =>
    cases hrep with
    | nil => cases hg
    | leaf ht => exact ih ht hg
    | trie _ ht => exact ih ht hg

/-- Root bitmap/cell preservation lifts to all routed leaves, while child routes
are protected by the independent finite source entry list and two heap frames. -/
theorem localRoutingLiftCells {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base before after : HamtHeap K V}
    (hb : PersistentHeapFrame base before) (ha : PersistentHeapFrame base after)
    (root : Nat) (oldNode newNode : HAMTNode K V)
    (slots newSlots : List (Option (Entry K V))) (pairs : List (K × V))
    (hentries : EntriesRep base slots pairs)
    (hnb : before.nodes[root]? = some oldNode) (hsb : before.vectors[oldNode.data]? = some slots)
    (hna : after.nodes[root]? = some newNode) (hsa : after.vectors[newNode.data]? = some newSlots)
    (hcells : ∀ (hash : HashState K) (entry : Entry K V),
      Nat.testBit oldNode.bitmap (BitmapIndex.fromHash hash).x = true →
      slots[pathReadIndex oldNode hash - 1]? = some (some entry) →
      Nat.testBit newNode.bitmap (BitmapIndex.fromHash hash).x = true ∧
        newSlots[pathReadIndex newNode hash - 1]? = some (some entry)) :
    RouteTransport runtime before root after root := by
  intro hash leaf hr
  cases hr with
  | leaf hn hs hbit hget =>
    cases Option.some.inj (hn.symm.trans hnb)
    cases Option.some.inj (hs.symm.trans hsb)
    obtain ⟨hbit', hget'⟩ := hcells hash (.leaf leaf) hbit hget
    exact .leaf hna hsa hbit' hget'
  | child hn hs hbit hget hchild =>
    cases Option.some.inj (hn.symm.trans hnb)
    cases Option.some.inj (hs.symm.trans hsb)
    obtain ⟨hbit', hget'⟩ := hcells hash _ hbit hget
    obtain ⟨childPairs, hchildRep⟩ := localRoutingChildRep hentries hget
    exact .child hna hsa hbit' hget'
      (copyRouting_frame ha (copyRouting_pullback hb hchildRep hchild))

/-- A local leaf edit preserves every route whose leaf differs from the edited leaf. -/
theorem localRoutingLiftOtherCells {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base before after : HamtHeap K V}
    (hb : PersistentHeapFrame base before) (ha : PersistentHeapFrame base after)
    (root : Nat) (oldNode newNode : HAMTNode K V)
    (slots newSlots : List (Option (Entry K V))) (pairs : List (K × V))
    (removed : Leaf K V) (hentries : EntriesRep base slots pairs)
    (hnb : before.nodes[root]? = some oldNode) (hsb : before.vectors[oldNode.data]? = some slots)
    (hna : after.nodes[root]? = some newNode) (hsa : after.vectors[newNode.data]? = some newSlots)
    (hcells : ∀ (hash : HashState K) (entry : Entry K V), entry ≠ .leaf removed →
      Nat.testBit oldNode.bitmap (BitmapIndex.fromHash hash).x = true →
      slots[pathReadIndex oldNode hash - 1]? = some (some entry) →
      Nat.testBit newNode.bitmap (BitmapIndex.fromHash hash).x = true ∧
        newSlots[pathReadIndex newNode hash - 1]? = some (some entry))
    (hash : HashState K) (leaf : Leaf K V) (hne : leaf ≠ removed)
    (hr : RoutedLeaf runtime before root hash leaf) :
    RoutedLeaf runtime after root hash leaf := by
  cases hr with
  | leaf hn hs hbit hget =>
    cases Option.some.inj (hn.symm.trans hnb)
    cases Option.some.inj (hs.symm.trans hsb)
    have hentry : Entry.leaf leaf ≠ Entry.leaf removed := fun he => hne (Entry.leaf.inj he)
    obtain ⟨hbit', hget'⟩ := hcells hash (.leaf leaf) hentry hbit hget
    exact .leaf hna hsa hbit' hget'
  | child hn hs hbit hget hchild =>
    cases Option.some.inj (hn.symm.trans hnb)
    cases Option.some.inj (hs.symm.trans hsb)
    obtain ⟨hbit', hget'⟩ := hcells hash _ (by intro he; cases he) hbit hget
    obtain ⟨childPairs, hchildRep⟩ := localRoutingChildRep hentries hget
    exact .child hna hsa hbit' hget'
      (copyRouting_frame ha (copyRouting_pullback hb hchildRep hchild))

/-- Inserting at the rank of a previously clear bit preserves all old route cells. -/
theorem localRoutingInsertCells {K V : Type}
    (oldNode : HAMTNode K V) (newData bit : Nat)
    (slots : List (Option (Entry K V))) (inserted : Entry K V)
    (hbound : oldNode.bitmap < 2 ^ 32) (hbi : bit < 32)
    (hclear : Nat.testBit oldNode.bitmap bit = false)
    (hash : HashState K) (entry : Entry K V)
    (hbit : Nat.testBit oldNode.bitmap (BitmapIndex.fromHash hash).x = true)
    (hget : slots[pathReadIndex oldNode hash - 1]? = some (some entry)) :
    let newNode : HAMTNode K V :=
      ⟨newData, u32 (oldNode.bitmap ||| shiftLeftNat 1 bit)⟩
    Nat.testBit newNode.bitmap (BitmapIndex.fromHash hash).x = true ∧
      (slots.insertIdx (persistentBitmapRank oldNode.bitmap bit) (some inserted))[pathReadIndex newNode hash - 1]? = some (some entry) := by
  have hne : bit ≠ (BitmapIndex.fromHash hash).x := by
    intro heq
    rw [← heq, hclear] at hbit
    cases hbit
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [persistentBitmapSetTestBit _ _ _ hbound hbi, hbit]
    rfl
  · rw [localRoutingIndexRank]
    rw [persistentInsertRankEntry slots (some inserted) oldNode.bitmap bit
      (BitmapIndex.fromHash hash).x hbound hbi (pathBitmapIndex_lt hash) hclear hbit hne]
    simpa only [localRoutingIndexRank] using hget

/-- Replacing an occupied leaf leaves all other occupied route cells unchanged. -/
theorem localRoutingReplaceCells {K V : Type}
    (oldNode : HAMTNode K V) (newData bit : Nat)
    (slots : List (Option (Entry K V))) (removed replacement : Leaf K V)
    (hbi : bit < 32) (hselected : Nat.testBit oldNode.bitmap bit = true)
    (hremoved : slots[persistentBitmapRank oldNode.bitmap bit]? = some (some (.leaf removed)))
    (hash : HashState K) (entry : Entry K V) (hne : entry ≠ .leaf removed)
    (hbit : Nat.testBit oldNode.bitmap (BitmapIndex.fromHash hash).x = true)
    (hget : slots[pathReadIndex oldNode hash - 1]? = some (some entry)) :
    let newNode : HAMTNode K V := ⟨newData, oldNode.bitmap⟩
    Nat.testBit newNode.bitmap (BitmapIndex.fromHash hash).x = true ∧
      (slots.set (persistentBitmapRank oldNode.bitmap bit) (some (.leaf replacement)))[pathReadIndex newNode hash - 1]? = some (some entry) := by
  have hneBit : bit ≠ (BitmapIndex.fromHash hash).x := by
    intro heq
    rw [localRoutingIndexRank, ← heq] at hget
    exact hne (Option.some.inj (Option.some.inj (hget.symm.trans hremoved)))
  dsimp only
  refine ⟨hbit, ?_⟩
  rw [localRoutingIndexRank]
  rw [persistentReplaceRankEntry slots (some (.leaf replacement)) oldNode.bitmap bit
    (BitmapIndex.fromHash hash).x hbi (pathBitmapIndex_lt hash) hselected hbit hneBit]
  simpa only [localRoutingIndexRank] using hget

/-- Clearing an occupied leaf preserves every other occupied route cell. -/
theorem localRoutingEraseCells {K V : Type}
    (oldNode : HAMTNode K V) (newData bit : Nat)
    (slots : List (Option (Entry K V))) (removed : Leaf K V)
    (hbound : oldNode.bitmap < 2 ^ 32) (hbi : bit < 32)
    (hselected : Nat.testBit oldNode.bitmap bit = true)
    (hremoved : slots[persistentBitmapRank oldNode.bitmap bit]? = some (some (.leaf removed)))
    (hash : HashState K) (entry : Entry K V) (hne : entry ≠ .leaf removed)
    (hbit : Nat.testBit oldNode.bitmap (BitmapIndex.fromHash hash).x = true)
    (hget : slots[pathReadIndex oldNode hash - 1]? = some (some entry)) :
    let newNode : HAMTNode K V :=
      ⟨newData, oldNode.bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)⟩
    Nat.testBit newNode.bitmap (BitmapIndex.fromHash hash).x = true ∧
      (slots.eraseIdx (persistentBitmapRank oldNode.bitmap bit))[pathReadIndex newNode hash - 1]? = some (some entry) := by
  have hneBit : bit ≠ (BitmapIndex.fromHash hash).x := by
    intro heq
    rw [localRoutingIndexRank, ← heq] at hget
    exact hne (Option.some.inj (Option.some.inj (hget.symm.trans hremoved)))
  dsimp only
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, hbits⟩ := persistentBitmapClear oldNode.bitmap bit hbound hbi hselected
    rw [hbits _ (fun heq => hneBit heq.symm)]
    exact hbit
  · rw [localRoutingIndexRank]
    rw [persistentEraseRankEntry slots oldNode.bitmap bit (BitmapIndex.fromHash hash).x
      hbound hbi (pathBitmapIndex_lt hash) hselected hbit hneBit]
    simpa only [localRoutingIndexRank] using hget

/-- The newly inserted leaf is routed at the new bit, including its adjusted rank. -/
theorem localRoutingInsertedLeaf {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root data bitmap : Nat)
    (slots : List (Option (Entry K V))) (leaf : Leaf K V) (hash : HashState K)
    (hbound : bitmap < 2 ^ 32) (hcount : countOnes 32 bitmap = slots.length)
    (hclear : Nat.testBit bitmap (BitmapIndex.fromHash hash).x = false)
    (hnode : heap.nodes[root]? = some
      ⟨data, u32 (bitmap ||| shiftLeftNat 1 (BitmapIndex.fromHash hash).x)⟩)
    (hslots : heap.vectors[data]? = some
      (slots.insertIdx (persistentBitmapRank bitmap (BitmapIndex.fromHash hash).x)
        (some (.leaf leaf)))) :
    RoutedLeaf runtime heap root hash leaf := by
  have hi : persistentBitmapRank bitmap (BitmapIndex.fromHash hash).x ≤ slots.length := by
    rw [← hcount]
    exact persistentCountAndLe 32 bitmap _
  refine .leaf hnode hslots ?_ ?_
  · rw [persistentBitmapSetTestBit _ _ _ hbound (pathBitmapIndex_lt hash)]
    simp only [decide_true, Bool.or_true]
  · rw [localRoutingIndexRank, persistentRankSetNew _ _ _ hbound (pathBitmapIndex_lt hash) hclear]
    simp only [Nat.lt_irrefl, ite_false, Nat.add_zero, List.getElem?_insertIdx_self, hi, ite_true]

/-- A replacement leaf retains the existing selected bit and rank. -/
theorem localRoutingReplacedLeaf {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root data bitmap : Nat)
    (slots : List (Option (Entry K V))) (leaf : Leaf K V) (hash : HashState K)
    (hbit : Nat.testBit bitmap (BitmapIndex.fromHash hash).x = true)
    (hi : persistentBitmapRank bitmap (BitmapIndex.fromHash hash).x < slots.length)
    (hnode : heap.nodes[root]? = some ⟨data, bitmap⟩)
    (hslots : heap.vectors[data]? = some
      (slots.set (persistentBitmapRank bitmap (BitmapIndex.fromHash hash).x)
        (some (.leaf leaf)))) :
    RoutedLeaf runtime heap root hash leaf := by
  refine .leaf hnode hslots hbit ?_
  rw [localRoutingIndexRank, List.getElem?_set_self hi]


/-- All existing routes survive insertion into a fresh clear-bit focus. -/
theorem localRoutingInsertFocus {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base before after : HamtHeap K V}
    (hb : PersistentHeapFrame base before) (ha : PersistentHeapFrame base after)
    (root : Nat) (oldNode : HAMTNode K V) (newData bit : Nat)
    (slots : List (Option (Entry K V))) (pairs : List (K × V)) (inserted : Leaf K V)
    (hentries : EntriesRep base slots pairs)
    (hnb : before.nodes[root]? = some oldNode) (hsb : before.vectors[oldNode.data]? = some slots)
    (hna : after.nodes[root]? = some ⟨newData, u32 (oldNode.bitmap ||| shiftLeftNat 1 bit)⟩)
    (hsa : after.vectors[newData]? = some
      (slots.insertIdx (persistentBitmapRank oldNode.bitmap bit) (some (.leaf inserted))))
    (hbound : oldNode.bitmap < 2 ^ 32) (hbi : bit < 32)
    (hclear : Nat.testBit oldNode.bitmap bit = false) :
    RouteTransport runtime before root after root :=
  localRoutingLiftCells runtime hb ha root oldNode _ slots _ pairs hentries hnb hsb hna hsa
    (localRoutingInsertCells oldNode newData bit slots (.leaf inserted) hbound hbi hclear)

/-- Every route to a different leaf survives replacement of a focus leaf. -/
theorem localRoutingReplaceFocus {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base before after : HamtHeap K V}
    (hb : PersistentHeapFrame base before) (ha : PersistentHeapFrame base after)
    (root : Nat) (oldNode : HAMTNode K V) (newData bit : Nat)
    (slots : List (Option (Entry K V))) (pairs : List (K × V)) (removed replacement : Leaf K V)
    (hentries : EntriesRep base slots pairs)
    (hnb : before.nodes[root]? = some oldNode) (hsb : before.vectors[oldNode.data]? = some slots)
    (hna : after.nodes[root]? = some ⟨newData, oldNode.bitmap⟩)
    (hsa : after.vectors[newData]? = some
      (slots.set (persistentBitmapRank oldNode.bitmap bit) (some (.leaf replacement))))
    (hbi : bit < 32) (hselected : Nat.testBit oldNode.bitmap bit = true)
    (hremoved : slots[persistentBitmapRank oldNode.bitmap bit]? = some (some (.leaf removed)))
    (hash : HashState K) (leaf : Leaf K V) (hne : leaf ≠ removed)
    (hr : RoutedLeaf runtime before root hash leaf) :
    RoutedLeaf runtime after root hash leaf :=
  localRoutingLiftOtherCells runtime hb ha root oldNode _ slots _ pairs removed hentries
    hnb hsb hna hsa
    (localRoutingReplaceCells oldNode newData bit slots removed replacement hbi hselected hremoved)
    hash leaf hne hr

/-- Every route to a different leaf survives erasure of a focus leaf. -/
theorem localRoutingEraseFocus {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base before after : HamtHeap K V}
    (hb : PersistentHeapFrame base before) (ha : PersistentHeapFrame base after)
    (root : Nat) (oldNode : HAMTNode K V) (newData bit : Nat)
    (slots : List (Option (Entry K V))) (pairs : List (K × V)) (removed : Leaf K V)
    (hentries : EntriesRep base slots pairs)
    (hnb : before.nodes[root]? = some oldNode) (hsb : before.vectors[oldNode.data]? = some slots)
    (hna : after.nodes[root]? = some
      ⟨newData, oldNode.bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)⟩)
    (hsa : after.vectors[newData]? = some
      (slots.eraseIdx (persistentBitmapRank oldNode.bitmap bit)))
    (hbound : oldNode.bitmap < 2 ^ 32) (hbi : bit < 32)
    (hselected : Nat.testBit oldNode.bitmap bit = true)
    (hremoved : slots[persistentBitmapRank oldNode.bitmap bit]? = some (some (.leaf removed)))
    (hash : HashState K) (leaf : Leaf K V) (hne : leaf ≠ removed)
    (hr : RoutedLeaf runtime before root hash leaf) :
    RoutedLeaf runtime after root hash leaf :=
  localRoutingLiftOtherCells runtime hb ha root oldNode _ slots _ pairs removed hentries
    hnb hsb hna hsa
    (localRoutingEraseCells oldNode newData bit slots removed hbound hbi hselected hremoved)
    hash leaf hne hr

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: UpdateActionsWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- The exact successful vector insertion action, with its native one-based
index checked before the finite list is changed. -/
theorem updateVectorInsertRun {K V : Type} (heap : HamtHeap K V) (data index : Nat)
    (slots : List (Option (Entry K V))) (entry : Entry K V)
    (hs : heap.vectors[data]? = some slots) (hlo : 1 ≤ index) (hhi : index ≤ slots.length + 1) :
    runHamt (heapVectorOps.insert data index entry) heap =
      (.ok (), {heap with vectors := heap.vectors.set data (slots.insertIdx (index - 1) (some entry))}) := by
  have hget : runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := rfl
  change runHamt (heapVectorInsert data index entry) heap = _
  unfold heapVectorInsert
  rw [persistentHamtBindRun, hget]
  dsimp only
  rw [hs]
  dsimp only
  have hbad : (index = 0 || index > slots.length + 1) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  rw [hbad] <;> rfl

theorem updateBitmapSetRun {K V : Type} (heap : HamtHeap K V) (root bit : Nat)
    (node : HAMTNode K V) (hn : heap.nodes[root]? = some node) :
    runHamt (set! root ⟨bit⟩) heap =
      let bitmap := u32 (node.bitmap ||| shiftLeftNat 1 bit)
      (.ok bitmap, {heap with nodes := heap.nodes.set root {node with bitmap := bitmap}}) := by
  unfold set!
  rw [persistentHamtBindRun, pathReadNodeRun heap root node hn] <;> rfl

theorem updateBitmapClearRun {K V : Type} (heap : HamtHeap K V) (root bit : Nat)
    (node : HAMTNode K V) (hn : heap.nodes[root]? = some node) :
    runHamt (unset! root ⟨bit⟩) heap =
      let bitmap := node.bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)
      (.ok bitmap, {heap with nodes := heap.nodes.set root {node with bitmap := bitmap}}) := by
  unfold unset!
  rw [persistentHamtBindRun, pathReadNodeRun heap root node hn] <;> rfl

/-- A successful found-slot insertion executes precisely the vector edit and
bitmap update described by the structural focus lemmas. -/
theorem updateFoundInsertRun {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root index bit : Nat) (node : HAMTNode K V)
    (slots : List (Option (Entry K V))) (hash : HashState K) (value : V) (present : Bool)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hlo : 1 ≤ index) (hhi : index ≤ slots.length + if present then 0 else 1) :
    runPartialHamt (insert! heapVectorOps runtime true present root index ⟨bit⟩ hash value) heap =
      let edited := if present then slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩))
        else slots.insertIdx (index - 1) (some (.leaf ⟨hash.key, value⟩))
      let bitmap := u32 (node.bitmap ||| shiftLeftNat 1 bit)
      some (.ok (some bitmap),
        { vectors := heap.vectors.set node.data edited,
          nodes := heap.nodes.set root {node with bitmap := bitmap} }) := by
  unfold runPartialHamt insert!
  simp only [ite_true]
  rw [persistentHamtBindRun, copyPathNodeDataRun heap root node hn]
  dsimp only
  cases present with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hhi ⊢
    rw [persistentHamtBindRun, updateVectorInsertRun heap node.data index slots
      (.leaf ⟨hash.key, value⟩) hs hlo hhi]
    dsimp only
    let middle : HamtHeap K V :=
      {heap with vectors := heap.vectors.set node.data (slots.insertIdx (index - 1) (some (.leaf ⟨hash.key, value⟩)))}
    rw [persistentHamtBindRun, updateBitmapSetRun middle root bit node hn] <;> rfl
  | true =>
    simp only [ite_true, Nat.add_zero] at hhi ⊢
    rw [persistentHamtBindRun, copyPathVectorSetRun heap node.data index slots
      (.leaf ⟨hash.key, value⟩) hs hlo hhi]
    dsimp only
    let middle : HamtHeap K V :=
      {heap with vectors := heap.vectors.set node.data (slots.set (index - 1) (some (.leaf ⟨hash.key, value⟩)))}
    rw [persistentHamtBindRun, updateBitmapSetRun middle root bit node hn] <;> rfl

theorem updateVectorDeleteRun {K V : Type} (heap : HamtHeap K V) (data index : Nat)
    (slots : List (Option (Entry K V)))
    (hs : heap.vectors[data]? = some slots) (hlo : 1 ≤ index) (hhi : index ≤ slots.length) :
    runHamt (round2.heapVectorDeleteAt data index) heap =
      (.ok (), {heap with vectors := heap.vectors.set data (slots.eraseIdx (index - 1))}) := by
  have hget : runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := rfl
  unfold round2.heapVectorDeleteAt
  rw [persistentHamtBindRun, hget]
  dsimp only
  rw [hs]
  dsimp only
  have hbad : (index = 0 || index > slots.length) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  rw [hbad] <;> rfl

theorem updateDeleteAndClearRun {K V : Type} (heap : HamtHeap K V)
    (root index bit : Nat) (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hlo : 1 ≤ index) (hhi : index ≤ slots.length) :
    runHamt (do
      let data ← nodeData root
      round2.heapVectorDeleteAt data index
      unset! root ⟨bit⟩) heap =
      let bitmap := node.bitmap &&& (MASK32 ^^^ shiftLeftNat 1 bit)
      (.ok bitmap,
        { vectors := heap.vectors.set node.data (slots.eraseIdx (index - 1)),
          nodes := heap.nodes.set root {node with bitmap := bitmap} }) := by
  rw [persistentHamtBindRun, copyPathNodeDataRun heap root node hn]
  dsimp only
  rw [persistentHamtBindRun, updateVectorDeleteRun heap node.data index slots hs hlo hhi]
  exact updateBitmapClearRun
    {heap with vectors := heap.vectors.set node.data (slots.eraseIdx (index - 1))}
    root bit node hn

/-- An explicit finite trace for successful returns from a partial loop. -/
inductive SuccessfulLoopTrace {S A E : Type} (step : S → Except E (Sum A S)) :
    S → A → Prop where
  | done {state result} (hstep : step state = .ok (.inl result)) :
      SuccessfulLoopTrace step state result
  | next {state nextState result} (hstep : step state = .ok (.inr nextState))
      (rest : SuccessfulLoopTrace step nextState result) :
      SuccessfulLoopTrace step state result

/-- A successful partial-loop result has a finite execution derivation. This
supports induction over successful insertion histories without totality. -/
theorem successfulLoopFiniteTrace {S A E : Type} (step : S → Except E (Sum A S)) :
    ∀ state result, JuliaLean.base.reduce.whileLoop step state = some (.ok result) →
      SuccessfulLoopTrace step state result := by
  apply JuliaLean.base.reduce.whileLoop.fixpoint_induct step
    (fun loop => ∀ state result, loop state = some (.ok result) →
      SuccessfulLoopTrace step state result)
  · refine Lean.Order.admissible_pi_apply
      (fun (state : S) (output : Option (Except E A)) => ∀ result,
        output = some (.ok result) → SuccessfulLoopTrace step state result) ?_
    intro state
    exact Lean.Order.admissible_pi
      (fun (output : Option (Except E A)) (result : A) =>
        output = some (.ok result) → SuccessfulLoopTrace step state result)
      (fun result => Lean.Order.Option.admissible_eq_some
        (SuccessfulLoopTrace step state result) (Except.ok result : Except E A))
  · intro loop ih state result hrun
    cases hstep : step state with
    | error error => simp [hstep] at hrun
    | ok outcome =>
      cases outcome with
      | inl value =>
        have heq : value = result := by
          simpa [hstep] using hrun
        subst result
        exact .done hstep
      | inr nextState =>
        exact .next hstep (ih nextState result (by simpa [hstep] using hrun))

theorem successfulLoopInvariant {S A E : Type} (step : S → Except E (Sum A S))
    (pending : S → Prop) (finished : A → Prop)
    (hs : ∀ state, pending state →
      ∀ output, step state = .ok output →
        match output with | .inl result => finished result | .inr next => pending next)
    {state : S} {result : A} (ht : SuccessfulLoopTrace step state result)
    (hi : pending state) : finished result := by
  induction ht with
  | done h => exact hs _ hi _ h
  | next h rest ih => exact ih (hs _ hi _ h)

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: GrowthWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

abbrev GrowthState (K : Type) := HashState K × HashState K × Nat × BitmapIndex × Bool × Bool

/-- A named copy of the frozen insertion loop body, used to expose a finite
execution derivation. No operation in the frozen model is replaced. -/
def growthStep {K V : Type} (runtime : HamtObjectIdRuntime K)
    (initialIndex : Nat) (value : V) (leaf : Leaf K V) :
    GrowthState K → HamtM K V (ForInStep (GrowthState K)) :=
  fun (hash, oldHash, current, bi, isPresent, finished) => do
    if finished then
      return .done (hash, oldHash, current, bi, isPresent, finished)
    let newTrie ← HAMT.emptyConstructor heapVectorOps
    let node ← readNode current
    let slot ← if isPresent then pure initialIndex else entry_index current bi
    if isPresent then heapVectorOps.set node.data slot (.trie newTrie)
    else heapVectorOps.insert node.data slot (.trie newTrie)
    let _ ← set! current bi
    let hash := next runtime hash
    let oldHash := next runtime oldHash
    let biNew := BitmapIndex.fromHash hash
    let biOld := BitmapIndex.fromHash oldHash
    if biNew == biOld then
      return .yield (hash, oldHash, newTrie, biNew, false, finished)
    else
      let newData ← nodeData newTrie
      let iNew ← entry_index newTrie biNew
      heapVectorOps.insert newData iNew (.leaf ⟨hash.key, value⟩)
      let _ ← set! newTrie biNew
      let iOld ← entry_index newTrie biOld
      heapVectorOps.insert newData iOld (.leaf leaf)
      let _ ← set! newTrie biOld
      return .yield (hash, oldHash, current, bi, isPresent, true)

def growthStateStep {K V : Type} (runtime : HamtObjectIdRuntime K)
    (initialIndex : Nat) (value : V) (leaf : Leaf K V)
    (input : GrowthState K × HamtHeap K V) :
    Except (HamtError × HamtHeap K V)
      (Sum (GrowthState K × HamtHeap K V) (GrowthState K × HamtHeap K V)) :=
  let (outcome, after) := runHamt (growthStep runtime initialIndex value leaf input.1) input.2
  match outcome with
  | .error error => .error (error, after)
  | .ok (.done state) => .ok (.inl (state, after))
  | .ok (.yield state) => .ok (.inr (state, after))

def growthPrelude {K V : Type} (runtime : HamtObjectIdRuntime K)
    (present : Bool) (root index : Nat) (hash : HashState K) :
    HamtM K V (Leaf K V × HashState K) := do
  if !present then throw .assertion
  let node ← readNode root
  let entry ← heapVectorOps.get node.data index
  let leaf ← match entry with
    | .leaf leaf => pure leaf
    | .trie _ => throw .typeError
  let oldHash := HashState.fromOtherAtDepth runtime hash leaf.key
  if oldHash.hash == hash.hash then throw .perfectHashCollision
  return (leaf, oldHash)

theorem growthPreludeKnownRun {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root index : Nat) (node : HAMTNode K V)
    (slots : List (Option (Entry K V))) (selected : Leaf K V)
    (present : Bool) (hash : HashState K)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hi : 1 ≤ index) (he : slots[index - 1]? = some (some (.leaf selected))) :
    runHamt (growthPrelude runtime present root index hash) heap =
      if present then
        if (HashState.fromOtherAtDepth runtime hash selected.key).hash == hash.hash then
          (.error .perfectHashCollision, heap)
        else (.ok (selected, HashState.fromOtherAtDepth runtime hash selected.key), heap)
      else (.error .assertion, heap) := by
  cases present with
  | false => rfl
  | true =>
    unfold growthPrelude
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, pure_bind]
    rw [persistentHamtBindRun, pathReadNodeRun heap root node hn]
    dsimp only
    rw [persistentHamtBindRun, pathVectorGetRun heap node.data slots index (.leaf selected) hs hi he]
    dsimp only
    cases hcheck : ((HashState.fromOtherAtDepth runtime hash selected.key).hash == hash.hash) <;>
      simp only [hcheck, Bool.false_eq_true, ite_false, ite_true] <;> rfl

/-- A successful growth prelude only reads the selected leaf and reconstructs
its hash at the query's current depth. -/
theorem growthPrelude_success_identifies {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root index : Nat) (node : HAMTNode K V)
    (slots : List (Option (Entry K V))) (selected returned : Leaf K V)
    (present : Bool) (hash oldHash : HashState K) (startHeap : HamtHeap K V)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hi : 1 ≤ index) (he : slots[index - 1]? = some (some (.leaf selected)))
    (hr : runHamt (growthPrelude runtime present root index hash) heap =
      (.ok (returned, oldHash), startHeap)) :
    present = true ∧ returned = selected ∧
      oldHash = HashState.fromOtherAtDepth runtime hash selected.key ∧ startHeap = heap := by
  rw [growthPreludeKnownRun runtime heap root index node slots selected present hash hn hs hi he] at hr
  cases present with
  | false => cases hr
  | true =>
    simp only [ite_true] at hr
    split at hr
    · cases hr
    · have hpair := Except.ok.inj (congrArg Prod.fst hr)
      exact ⟨rfl, (congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm,
        (congrArg Prod.snd hr).symm⟩

theorem growthInsertNormalForm {K V : Type} (runtime : HamtObjectIdRuntime K)
    (present : Bool) (root index : Nat) (bi : BitmapIndex) (hash : HashState K)
    (value : V) (heap : HamtHeap K V) :
    runPartialHamt (insert! heapVectorOps runtime false present root index bi hash value) heap =
      match runHamt (growthPrelude runtime present root index hash) heap with
      | (.error error, after) => some (.error error, after)
      | (.ok (leaf, oldHash), after) =>
        match JuliaLean.base.reduce.whileLoop (growthStateStep runtime index value leaf)
          ((hash, oldHash, root, bi, present, false), after) with
        | none => none
        | some (.error (error, final)) => some (.error error, final)
        | some (.ok (_, final)) => some (.ok none, final) := by
  unfold runPartialHamt insert! growthPrelude growthStateStep growthStep
  simp only [Bool.false_eq_true, ite_false]
  rfl'

/-- Successful insertion in the growth branch supplies a finite loop trace,
with the exact original prelude and final heap retained. -/
theorem growthInsertFiniteTrace {K V : Type} (runtime : HamtObjectIdRuntime K)
    (present : Bool) (root index : Nat) (bi : BitmapIndex) (hash : HashState K)
    (value : V) (heap after : HamtHeap K V) (inserted : Option BITMAP)
    (hr : runPartialHamt (insert! heapVectorOps runtime false present root index bi hash value)
      heap = some (.ok inserted, after)) :
    ∃ (leaf : Leaf K V) (oldHash : HashState K) (startHeap : HamtHeap K V)
      (last : GrowthState K),
      runHamt (growthPrelude runtime present root index hash) heap =
        (.ok (leaf, oldHash), startHeap) ∧
      SuccessfulLoopTrace (growthStateStep runtime index value leaf)
        ((hash, oldHash, root, bi, present, false), startHeap) (last, after) ∧
      inserted = none := by
  rw [growthInsertNormalForm] at hr
  cases hp : runHamt (growthPrelude runtime present root index hash) heap with
  | mk outcome startHeap =>
    rw [hp] at hr
    cases outcome with
    | error error => cases hr
    | ok valuePair =>
      rcases valuePair with ⟨leaf, oldHash⟩
      dsimp only at hr
      cases ht : JuliaLean.base.reduce.whileLoop (growthStateStep runtime index value leaf)
        ((hash, oldHash, root, bi, present, false), startHeap) with
      | none => rw [ht] at hr; cases hr
      | some outcome =>
        rw [ht] at hr
        cases outcome with
        | error errorPair => cases hr
        | ok final =>
          rcases final with ⟨last, finalHeap⟩
          have he := Option.some.inj hr
          have hheap : finalHeap = after := congrArg Prod.snd he
          have hresult : inserted = none := (Except.ok.inj (congrArg Prod.fst he)).symm
          subst finalHeap
          exact ⟨leaf, oldHash, startHeap, last, rfl,
            successfulLoopFiniteTrace _ _ _ ht, hresult⟩

theorem growthStepFinished {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (value : V) (leaf : Leaf K V) (heap : HamtHeap K V)
    (hash oldHash : HashState K) (root : Nat) (bi : BitmapIndex) (present : Bool) :
    runHamt (growthStep runtime index value leaf (hash, oldHash, root, bi, present, true)) heap =
      (.ok (.done (hash, oldHash, root, bi, present, true)), heap) := rfl

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: GrowthStructureWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Selecting an old collision leaf splits its vector and flattened pair list
at corresponding positions. This is independent of any insertion execution. -/
theorem growthEntriesSplitLeaf {K V : Type} {heap : HamtHeap K V}
    {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) {index : Nat} {old : Leaf K V}
    (hget : slots[index]? = some (some (.leaf old))) :
    ∃ beforeSlots afterSlots beforePairs afterPairs,
      slots = beforeSlots ++ some (.leaf old) :: afterSlots ∧
      index = beforeSlots.length ∧
      pairs = beforePairs ++ (old.key, old.val) :: afterPairs ∧
      EntriesRep heap beforeSlots beforePairs ∧ EntriesRep heap afterSlots afterPairs := by
  induction slots generalizing pairs index with
  | nil => cases hget
  | cons entry rest ih =>
    cases hr with
    | leaf hrest =>
      rename_i leaf restPairs
      cases index with
      | zero =>
        cases hget
        exact ⟨[], rest, [], restPairs, rfl, rfl, rfl, .nil, hrest⟩
      | succ index =>
        obtain ⟨bs, zs, bp, zp, hs, hi, hp, hb, hz⟩ := ih hrest hget
        refine ⟨some (.leaf leaf) :: bs, zs, (leaf.key, leaf.val) :: bp, zp,
          ?_, ?_, ?_, .leaf hb, hz⟩
        · rw [hs]
          rfl
        · simp only [List.length_cons, hi]
        · rw [hp]
          rfl
    | trie hchild hrest =>
      rename_i child childPairs restPairs
      cases index with
      | zero => cases hget
      | succ index =>
        obtain ⟨bs, zs, bp, zp, hs, hi, hp, hb, hz⟩ := ih hrest hget
        refine ⟨some (.trie child) :: bs, zs, childPairs ++ bp, zp,
          ?_, ?_, ?_, .trie hchild hb, hz⟩
        · rw [hs]
          rfl
        · simp only [List.length_cons, hi]
        · simp only [hp, List.append_assoc]

/-- A fresh empty node allocated after all context records. -/
def growthEmptyExtension {K V : Type} (heap : HamtHeap K V) : HamtHeap K V :=
  contextCopiedHeap heap (⟨0, 0⟩ : HAMTNode K V) []

theorem growthEmptyExtensionFrame {K V : Type} (heap : HamtHeap K V) :
    PersistentHeapFrame heap (growthEmptyExtension heap) :=
  contextCopiedHeapFrame heap ⟨0, 0⟩ []

theorem growthEmptyExtensionNode {K V : Type} (heap : HamtHeap K V) :
    (growthEmptyExtension heap).nodes[heap.nodes.length]? =
      some ⟨heap.vectors.length, 0⟩ := by
  simp only [growthEmptyExtension, contextCopiedHeap, List.getElem?_append,
    Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero]

theorem growthEmptyExtensionSlots {K V : Type} (heap : HamtHeap K V) :
    (growthEmptyExtension heap).vectors[heap.vectors.length]? = some [] := by
  simp only [growthEmptyExtension, contextCopiedHeap, List.getElem?_append,
    Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero]

theorem growthEmptyExtensionRep {K V : Type} (heap : HamtHeap K V) :
    TrieRep (growthEmptyExtension heap) heap.nodes.length [] := by
  exact TrieRep.node (growthEmptyExtensionNode heap) (growthEmptyExtensionSlots heap)
    (by change 0 < 2 ^ 32; decide) (by change countOnes 32 0 = 0; rfl) .nil

/-- Pending growth has an empty fresh focus, while the copied ancestors and
all original sibling pairs live in a preserved prefix heap. The old collision
pair is held separately until the final two-leaf node is installed. -/
def GrowthOpenFocus {K V : Type} (initial heap : HamtHeap K V)
    (root current : Nat) (original : List (K × V)) (old : Leaf K V) : Prop :=
  ∃ contextBase before after data,
    PersistentHeapFrame initial contextBase ∧ PersistentHeapFrame contextBase heap ∧
    TrieContext contextBase root current before after ∧
    original = before ++ (old.key, old.val) :: after ∧
    heap.nodes[current]? = some (⟨data, 0⟩ : HAMTNode K V) ∧
    heap.vectors[data]? = some [] ∧
    contextBase.nodes.length ≤ current ∧ contextBase.vectors.length ≤ data

/-- The completed collision subtree adds exactly one new pair to the
original flattened list, and leaves every original heap record unchanged. -/
def GrowthFinishedRep {K V : Type} (initial heap : HamtHeap K V)
    (root : Nat) (original : List (K × V)) (new : Leaf K V) : Prop :=
  PersistentHeapFrame initial heap ∧
    ∃ pairs, TrieRep heap root pairs ∧ List.Perm pairs ((new.key, new.val) :: original)

/-- Filling the final hole with the two collision leaves reconstructs the
whole modified subtree, regardless of the order of the final two hash slots. -/
theorem growthOpenFill {K V : Type} {initial heap : HamtHeap K V}
    {root current : Nat} {original : List (K × V)} {old new : Leaf K V}
    (hop : GrowthOpenFocus initial heap root current original old)
    {final : HamtHeap K V}
    (hfill : ∀ contextBase before after data,
      PersistentHeapFrame initial contextBase → PersistentHeapFrame contextBase heap →
      TrieContext contextBase root current before after →
      original = before ++ (old.key, old.val) :: after →
      heap.nodes[current]? = some (⟨data, 0⟩ : HAMTNode K V) →
      heap.vectors[data]? = some [] →
      contextBase.nodes.length ≤ current → contextBase.vectors.length ≤ data →
      PersistentHeapFrame contextBase final ∧
        ∃ pairs, TrieRep final current pairs ∧
          List.Perm pairs [(new.key, new.val), (old.key, old.val)]) :
    GrowthFinishedRep initial final root original new := by
  obtain ⟨base, before, after, data, hi, hf, hc, hp, hn, hs, hfn, hfd⟩ := hop
  obtain ⟨hfinal, pairs, ht, hperm⟩ := hfill base before after data hi hf hc hp hn hs hfn hfd
  refine ⟨persistentHeapFrameTrans hi hfinal, before ++ pairs ++ after,
    contextReplace hfinal hc ht, ?_⟩
  have hwhole : List.Perm (before ++ pairs ++ after)
      (before ++ [(new.key, new.val), (old.key, old.val)] ++ after) := by
    simpa only [List.append_assoc] using (hperm.append_left before).append_right after
  apply hwhole.trans
  rw [hp]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    (List.perm_middle (a := (new.key, new.val)) (l₁ := before)
      (l₂ := (old.key, old.val) :: after))

/-- Replacing the initial collision leaf by a child pointer creates the
first one-hole context; the future child need not be present in the prefix. -/
theorem growthInitialContext {K V : Type} {base heap : HamtHeap K V}
    (hf : PersistentHeapFrame base heap) (root : Nat) (node : HAMTNode K V)
    (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (old : Leaf K V) (index : Nat)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hb : node.bitmap < 2 ^ 32) (hc : countOnes 32 node.bitmap = slots.length)
    (he : EntriesRep base slots pairs) (hslot : slots[index]? = some (some (.leaf old)))
    (hfn : base.nodes.length ≤ root) (hfd : base.vectors.length ≤ node.data) :
    let parent : HamtHeap K V :=
      {heap with vectors := heap.vectors.set node.data (slots.set index (some (.trie heap.nodes.length)))}
    ∃ before after, pairs = before ++ (old.key, old.val) :: after ∧
      PersistentHeapFrame base parent ∧ TrieContext parent root heap.nodes.length before after := by
  obtain ⟨bs, zs, bp, zp, hsplit, hi, hp, hbefore, hafter⟩ := growthEntriesSplitLeaf he hslot
  let parent : HamtHeap K V :=
    {heap with vectors := heap.vectors.set node.data (slots.set index (some (.trie heap.nodes.length)))}
  have hframe : PersistentHeapFrame base parent :=
    persistentHeapFrameVectorSet hf node.data _ hfd
  have hslots : parent.vectors[node.data]? = some (bs ++ some (.trie heap.nodes.length) :: zs) := by
    change (heap.vectors.set node.data
      (slots.set index (some (.trie heap.nodes.length))))[node.data]? = _
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hs).1, hsplit, hi]
    rw [List.set_append_right _ _ (Nat.le_refl _)]
    simp only [Nat.sub_self, List.set_cons_zero]
  have hcount : countOnes 32 node.bitmap = bs.length + 1 + zs.length := by
    rw [hc, hsplit]
    simp only [List.length_append, List.length_cons]
    omega
  refine ⟨bp, zp, hp, hframe, ?_⟩
  have hctx := TrieContext.parent (heap := parent) (root := root)
    (child := heap.nodes.length) (focus := heap.nodes.length)
    hn hslots hb hcount (persistentEntriesRepFrame hframe hbefore)
    (.root heap.nodes.length) (persistentEntriesRepFrame hframe hafter)
  simpa only [List.append_nil, List.nil_append] using hctx

theorem growthInitialOpen {K V : Type} {base heap : HamtHeap K V}
    (hf : PersistentHeapFrame base heap) (root : Nat) (node : HAMTNode K V)
    (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (old : Leaf K V) (index : Nat)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hb : node.bitmap < 2 ^ 32) (hc : countOnes 32 node.bitmap = slots.length)
    (he : EntriesRep base slots pairs) (hslot : slots[index]? = some (some (.leaf old)))
    (hfn : base.nodes.length ≤ root) (hfd : base.vectors.length ≤ node.data) :
    let parent : HamtHeap K V :=
      {heap with vectors := heap.vectors.set node.data (slots.set index (some (.trie heap.nodes.length)))}
    GrowthOpenFocus base (growthEmptyExtension parent) root heap.nodes.length pairs old := by
  let parent : HamtHeap K V :=
    {heap with vectors := heap.vectors.set node.data (slots.set index (some (.trie heap.nodes.length)))}
  obtain ⟨before, after, hp, hframe, hcontext⟩ :=
    growthInitialContext hf root node slots pairs old index hn hs hb hc he hslot hfn hfd
  refine ⟨parent, before, after, parent.vectors.length, hframe,
    growthEmptyExtensionFrame parent, hcontext, hp, ?_, growthEmptyExtensionSlots parent,
    Nat.le_refl _, Nat.le_refl _⟩
  exact growthEmptyExtensionNode parent

/-- A subsequent collision level contains only the pointer to the next
empty focus; its single bit is independent of all original sibling entries. -/
def growthEmptyParent {K V : Type} (heap : HamtHeap K V) (current data bit : Nat) : HamtHeap K V :=
  { vectors := heap.vectors.set data [some (.trie heap.nodes.length)],
    nodes := heap.nodes.set current ⟨data, 2 ^ bit⟩ }

theorem growthEmptyParentContext {K V : Type} {base heap : HamtHeap K V}
    (hf : PersistentHeapFrame base heap) (current data bit : Nat)
    (hn : current < heap.nodes.length) (hs : data < heap.vectors.length)
    (hfn : base.nodes.length ≤ current) (hfd : base.vectors.length ≤ data) (hb : bit < 32) :
    PersistentHeapFrame base (growthEmptyParent heap current data bit) ∧
      TrieContext (growthEmptyParent heap current data bit)
        current heap.nodes.length [] [] := by
  have hframe := persistentHeapFrameNodeSet
    (persistentHeapFrameVectorSet hf data [some (.trie heap.nodes.length)] hfd)
    current (⟨data, 2 ^ bit⟩ : HAMTNode K V) hfn
  refine ⟨hframe, ?_⟩
  have hnode : (growthEmptyParent heap current data bit).nodes[current]? = some ⟨data, 2 ^ bit⟩ :=
    List.getElem?_set_self hn
  have hslots : (growthEmptyParent heap current data bit).vectors[data]? =
      some [some (.trie heap.nodes.length)] := List.getElem?_set_self hs
  have hctx := TrieContext.parent (heap := growthEmptyParent heap current data bit)
    (root := current) (child := heap.nodes.length) (focus := heap.nodes.length)
    (beforeSlots := []) (afterSlots := []) (beforePairs := []) (afterPairs := [])
    hnode hslots (Nat.pow_lt_pow_right (by decide) hb)
    (singletonCountOnesPow 32 bit hb) .nil (.root heap.nodes.length) .nil
  exact hctx

/-- Extending an empty collision focus preserves the old pair's hole and
all existing context records, while allocating a fresh empty next focus. -/
theorem growthOpenExtend {K V : Type} {initial heap : HamtHeap K V}
    {root current : Nat} {original : List (K × V)} {old : Leaf K V}
    (hop : GrowthOpenFocus initial heap root current original old) (bit : Nat) (hb : bit < 32) :
    ∃ data,
      heap.nodes[current]? = some (⟨data, 0⟩ : HAMTNode K V) ∧
      GrowthOpenFocus initial
        (growthEmptyExtension (growthEmptyParent heap current data bit))
        root heap.nodes.length original old := by
  obtain ⟨base, before, after, data, hi, hf, hc, hp, hn, hs, hfn, hfd⟩ := hop
  have hroot := (List.getElem?_eq_some_iff.mp hn).1
  have hdata := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨hparentFrame, hchildContext⟩ :=
    growthEmptyParentContext hf current data bit hroot hdata hfn hfd hb
  let parent := growthEmptyParent heap current data bit
  have hcontext : TrieContext parent root heap.nodes.length before after := by
    simpa only [List.append_nil, List.nil_append] using
      contextCompose (contextFrame hparentFrame hc) hchildContext
  have hnodeLength : parent.nodes.length = heap.nodes.length := by
    simp only [parent, growthEmptyParent, List.length_set]
  refine ⟨data, hn, parent, before, after, parent.vectors.length,
    persistentHeapFrameTrans hi hparentFrame, growthEmptyExtensionFrame parent,
    hcontext, hp, ?_, growthEmptyExtensionSlots parent, ?_, Nat.le_refl _⟩
  · rw [← hnodeLength]
    exact growthEmptyExtensionNode parent
  · simpa only [hnodeLength] using Nat.le_refl heap.nodes.length

/-- Two distinct bounded hash slots give a finite two-leaf focus with exactly
the desired pair multiset. Its concrete vector order is determined by rank. -/
theorem growthTwoLeafFocus {K V : Type} {base heap : HamtHeap K V}
    (hf : PersistentHeapFrame base heap) (root data newBit oldBit : Nat)
    (new old : Leaf K V) (hn : root < heap.nodes.length) (hs : data < heap.vectors.length)
    (hfn : base.nodes.length ≤ root) (hfd : base.vectors.length ≤ data)
    (hnewBit : newBit < 32) (holdBit : oldBit < 32) (hne : newBit ≠ oldBit) :
    let slots : List (Option (Entry K V)) :=
      [some (.leaf new)].insertIdx (persistentBitmapRank (2 ^ newBit) oldBit) (some (.leaf old))
    let bitmap := u32 (2 ^ newBit ||| shiftLeftNat 1 oldBit)
    let final : HamtHeap K V :=
      { vectors := heap.vectors.set data slots, nodes := heap.nodes.set root ⟨data, bitmap⟩ }
    PersistentHeapFrame base final ∧
      ∃ pairs, TrieRep final root pairs ∧ List.Perm pairs [(new.key, new.val), (old.key, old.val)] := by
  have hbound : 2 ^ newBit < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hnewBit
  have hcount : countOnes 32 (2 ^ newBit) = 1 := singletonCountOnesPow 32 newBit hnewBit
  have hclear : Nat.testBit (2 ^ newBit) oldBit = false := by
    simp only [Nat.testBit_two_pow, hne, decide_false]
  have hrank : persistentBitmapRank (2 ^ newBit) oldBit ≤ 1 := by
    have h := persistentCountAndLe 32 (2 ^ newBit) (2 ^ oldBit - 1)
    rw [hcount] at h
    exact h
  have he : EntriesRep base [some (.leaf new)] [(new.key, new.val)] := .leaf .nil
  obtain ⟨before, after, hp, heNew⟩ := persistentEntriesInsertLeaf he
    (persistentBitmapRank (2 ^ newBit) oldBit) hrank old
  obtain ⟨hbNew, hcNew⟩ := persistentBitmapSetNew (2 ^ newBit) oldBit hbound holdBit hclear
  have hlen := persistentLengthInsert ([some (Entry.leaf new)] : List (Option (Entry K V)))
    (persistentBitmapRank (2 ^ newBit) oldBit) (some (Entry.leaf old)) hrank
  have hrep := persistentFreshFocusRep hf root data _ _ _ hn hs hfn hfd hbNew
    (by rw [hcNew, hcount, hlen] <;> rfl) heNew
  refine ⟨hrep.1, before ++ (old.key, old.val) :: after, hrep.2, ?_⟩
  have hmove : List.Perm (before ++ (old.key, old.val) :: after)
      ((old.key, old.val) :: [(new.key, new.val)]) := by
    rw [hp]
    exact List.perm_middle
  exact hmove.trans (List.Perm.swap _ _ _)

/-- Finishing at any later pair of distinct hash chunks fills the accumulated
collision chain and produces the desired whole-subtree pair permutation. -/
theorem growthOpenComplete {K V : Type} {initial heap : HamtHeap K V}
    {root current : Nat} {original : List (K × V)} {old new : Leaf K V}
    (hop : GrowthOpenFocus initial heap root current original old)
    (newBit oldBit : Nat) (hnewBit : newBit < 32) (holdBit : oldBit < 32)
    (hne : newBit ≠ oldBit) :
    ∃ data, heap.nodes[current]? = some (⟨data, 0⟩ : HAMTNode K V) ∧
      let slots : List (Option (Entry K V)) :=
        [some (.leaf new)].insertIdx (persistentBitmapRank (2 ^ newBit) oldBit)
          (some (.leaf old))
      let bitmap := u32 (2 ^ newBit ||| shiftLeftNat 1 oldBit)
      let final : HamtHeap K V :=
        { vectors := heap.vectors.set data slots,
          nodes := heap.nodes.set current ⟨data, bitmap⟩ }
      GrowthFinishedRep initial final root original new := by
  obtain ⟨base, before, after, data, hi, hf, hc, hp, hn, hs, hfn, hfd⟩ := hop
  refine ⟨data, hn, ?_⟩
  apply growthOpenFill ⟨base, before, after, data, hi, hf, hc, hp, hn, hs, hfn, hfd⟩
  intro otherBase otherBefore otherAfter otherData _ hframe _ _ hnode hslots hrootFresh hdataFresh
  have hdataEq : otherData = data :=
    congrArg HAMTNode.data (Option.some.inj (hnode.symm.trans hn))
  subst otherData
  exact growthTwoLeafFocus hframe current data newBit oldBit new old
    (List.getElem?_eq_some_iff.mp hn).1 (List.getElem?_eq_some_iff.mp hslots).1
    hrootFresh hdataFresh hnewBit holdBit hne

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: GrowthStepStructureWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

theorem growthEmptyConstructorRun {K V : Type} (heap : HamtHeap K V) :
    runHamt (HAMT.emptyConstructor heapVectorOps) heap =
      (.ok heap.nodes.length, growthEmptyExtension heap) := rfl

theorem growthIndexRun {K V : Type} (heap : HamtHeap K V) (root bit : Nat)
    (node : HAMTNode K V) (hn : heap.nodes[root]? = some node) :
    runHamt (entry_index root ⟨bit⟩) heap =
      (.ok (persistentBitmapRank node.bitmap bit + 1), heap) := by
  have hbitmap : runHamt (nodeBitmap root) heap = (.ok node.bitmap, heap) := by
    unfold nodeBitmap
    rw [persistentHamtBindRun, pathReadNodeRun heap root node hn]
    rfl
  unfold entry_index
  rw [persistentHamtBindRun, hbitmap]
  simp only [persistentBitmapRank, shiftLeftNat, Nat.one_mul] <;> rfl

theorem growthRankZero (bit : Nat) : persistentBitmapRank 0 bit = 0 := by
  unfold persistentBitmapRank
  rw [Nat.zero_and, pathCountOnesZero]

theorem growthSetZeroValue (bit : Nat) (hb : bit < 32) :
    u32 (0 ||| shiftLeftNat 1 bit) = 2 ^ bit := by
  simp only [u32, Nat.zero_or, shiftLeftNat, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hb)

theorem growthSetExistingRun {K V : Type} (heap : HamtHeap K V)
    (root bit : Nat) (node : HAMTNode K V) (hn : heap.nodes[root]? = some node)
    (hb : node.bitmap < 2 ^ 32) (hbit : Nat.testBit node.bitmap bit = true) :
    runHamt (set! root ⟨bit⟩) heap = (.ok node.bitmap, heap) := by
  rw [updateBitmapSetRun heap root bit node hn, persistentBitmapSetExisting node.bitmap bit hb hbit]
  change ((.ok node.bitmap : Except HamtError Nat),
      {heap with nodes := heap.nodes.set root node}) = (.ok node.bitmap, heap)
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hn
  have hsame : heap.nodes.set root node = heap.nodes := by
    rw [← hv]
    exact List.set_getElem_self hi
  rw [hsame]

/-- The exact heap containing the two leaves at their rank-ordered positions. -/
def growthTwoLeafHeap {K V : Type} (heap : HamtHeap K V) (root data newBit oldBit : Nat)
    (new old : Leaf K V) : HamtHeap K V :=
  { vectors := heap.vectors.set data
      ([some (.leaf new)].insertIdx (persistentBitmapRank (2 ^ newBit) oldBit) (some (.leaf old))),
    nodes := heap.nodes.set root ⟨data, u32 (2 ^ newBit ||| shiftLeftNat 1 oldBit)⟩ }

/-- Filling a fresh empty node executes two checked vector insertions, with
the second index calculated from the bitmap produced by the first. -/
theorem growthFillRun {K V A : Type} (heap : HamtHeap K V)
    (root data newBit oldBit : Nat) (new old : Leaf K V) (result : A)
    (hn : heap.nodes[root]? = some (⟨data, 0⟩ : HAMTNode K V))
    (hs : heap.vectors[data]? = some []) (hb : newBit < 32) :
    runHamt (do
      let newData ← nodeData root
      let first ← entry_index root ⟨newBit⟩
      heapVectorOps.insert newData first (.leaf new)
      let _ ← set! root ⟨newBit⟩
      let second ← entry_index root ⟨oldBit⟩
      heapVectorOps.insert newData second (.leaf old)
      let _ ← set! root ⟨oldBit⟩
      pure result) heap =
      (.ok result, growthTwoLeafHeap heap root data newBit oldBit new old) := by
  have hnlt := (List.getElem?_eq_some_iff.mp hn).1
  have hslt := (List.getElem?_eq_some_iff.mp hs).1
  let once : HamtHeap K V :=
    { vectors := heap.vectors.set data [some (.leaf new)],
      nodes := heap.nodes.set root ⟨data, 2 ^ newBit⟩ }
  have hnodeOnce : once.nodes[root]? = some (⟨data, 2 ^ newBit⟩ : HAMTNode K V) :=
    List.getElem?_set_self hnlt
  have hslotsOnce : once.vectors[data]? = some [some (.leaf new)] :=
    List.getElem?_set_self hslt
  have hrank : persistentBitmapRank (2 ^ newBit) oldBit ≤ 1 := by
    have h := persistentCountAndLe 32 (2 ^ newBit) (2 ^ oldBit - 1)
    rw [singletonCountOnesPow 32 newBit hb] at h
    exact h
  rw [persistentHamtBindRun, copyPathNodeDataRun heap root ⟨data, 0⟩ hn]
  dsimp only
  rw [persistentHamtBindRun, growthIndexRun heap root newBit ⟨data, 0⟩ hn]
  simp only [growthRankZero, Nat.zero_add]
  rw [persistentHamtBindRun,
    updateVectorInsertRun heap data 1 [] (.leaf new) hs (Nat.le_refl 1) (Nat.le_refl 1)]
  dsimp only
  simp only [Nat.sub_self, List.insertIdx_zero]
  rw [persistentHamtBindRun,
    updateBitmapSetRun {heap with vectors := heap.vectors.set data [some (.leaf new)]}
      root newBit ⟨data, 0⟩ hn]
  simp only [growthSetZeroValue newBit hb]
  change runHamt (do
      let second ← entry_index root ⟨oldBit⟩
      heapVectorOps.insert data second (.leaf old)
      let _ ← set! root ⟨oldBit⟩
      pure result) once = _
  rw [persistentHamtBindRun, growthIndexRun once root oldBit ⟨data, 2 ^ newBit⟩ hnodeOnce]
  dsimp only
  rw [persistentHamtBindRun, updateVectorInsertRun once data
    (persistentBitmapRank (2 ^ newBit) oldBit + 1) [some (.leaf new)] (.leaf old)
    hslotsOnce (by omega) (by simp only [List.length_cons, List.length_nil]; omega)]
  dsimp only
  simp only [Nat.add_sub_cancel]
  rw [persistentHamtBindRun,
    updateBitmapSetRun
      {once with vectors := once.vectors.set data ([some (.leaf new)].insertIdx (persistentBitmapRank (2 ^ newBit) oldBit) (some (.leaf old)))}
      root oldBit ⟨data, 2 ^ newBit⟩ hnodeOnce]
  simp only [Nat.add_sub_cancel, once, growthTwoLeafHeap, List.set_set] <;> rfl

/-- The shared remainder of the frozen growth step after linking a new empty
child; the two next hash chunks decide whether that child stays open. -/
def growthTail {K V : Type} (runtime : HamtObjectIdRuntime K)
    (hash oldHash : HashState K) (current : Nat) (bi : BitmapIndex) (present : Bool)
    (child : Nat) (value : V) (old : Leaf K V) : HamtM K V (ForInStep (GrowthState K)) := do
  let hash := next runtime hash
  let oldHash := next runtime oldHash
  let biNew := BitmapIndex.fromHash hash
  let biOld := BitmapIndex.fromHash oldHash
  if biNew == biOld then
    pure (.yield (hash, oldHash, child, biNew, false, false))
  else
    let data ← nodeData child
    let first ← entry_index child biNew
    heapVectorOps.insert data first (.leaf ⟨hash.key, value⟩)
    let _ ← set! child biNew
    let second ← entry_index child biOld
    heapVectorOps.insert data second (.leaf old)
    let _ ← set! child biOld
    pure (.yield (hash, oldHash, current, bi, present, true))

theorem growthTailRun {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (hash oldHash : HashState K)
    (current : Nat) (bi : BitmapIndex) (present : Bool) (child data : Nat)
    (value : V) (old : Leaf K V)
    (hn : heap.nodes[child]? = some (⟨data, 0⟩ : HAMTNode K V))
    (hs : heap.vectors[data]? = some []) :
    runHamt (growthTail runtime hash oldHash current bi present child value old) heap =
      let nextHash := next runtime hash
      let nextOldHash := next runtime oldHash
      let newBi := BitmapIndex.fromHash nextHash
      let oldBi := BitmapIndex.fromHash nextOldHash
      if newBi == oldBi then
        (.ok (.yield (nextHash, nextOldHash, child, newBi, false, false)), heap)
      else
        (.ok (.yield (nextHash, nextOldHash, current, bi, present, true)),
          growthTwoLeafHeap heap child data newBi.x oldBi.x ⟨nextHash.key, value⟩ old) := by
  unfold growthTail
  dsimp only
  cases hchunks : ((BitmapIndex.fromHash (next runtime hash)) ==
      (BitmapIndex.fromHash (next runtime oldHash))) with
  | false =>
    simp only [hchunks, Bool.false_eq_true, ite_false]
    exact growthFillRun heap child data _ _ ⟨(next runtime hash).key, value⟩ old _ hn hs
      (pathBitmapIndex_lt (next runtime hash))
  | true => simp only [hchunks, ite_true] <;> rfl

theorem growthReplaceForkHeap {K V : Type} (heap : HamtHeap K V)
    (data index : Nat) (slots : List (Option (Entry K V)))
    (hd : data < heap.vectors.length) :
    {growthEmptyExtension heap with vectors := (growthEmptyExtension heap).vectors.set data (slots.set index (some (.trie heap.nodes.length)))} =
      growthEmptyExtension {heap with vectors := heap.vectors.set data (slots.set index (some (.trie heap.nodes.length)))} := by
  simp only [growthEmptyExtension, contextCopiedHeap, List.set_append_left _ _ hd, List.length_set]

/-- The first collision step replaces the old leaf by a fresh child pointer;
the occupied parent bitmap bit and all original heap records are retained. -/
theorem growthStepPresentPrefix {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (value : V) (old : Leaf K V) (heap : HamtHeap K V)
    (hash oldHash : HashState K) (root : Nat) (bi : BitmapIndex)
    (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hb : node.bitmap < 2 ^ 32) (hbit : Nat.testBit node.bitmap bi.x = true)
    (hlo : 1 ≤ index) (hhi : index ≤ slots.length) :
    let parent : HamtHeap K V :=
      {heap with vectors := heap.vectors.set node.data (slots.set (index - 1) (some (.trie heap.nodes.length)))}
    runHamt (growthStep runtime index value old (hash, oldHash, root, bi, true, false)) heap =
      runHamt (growthTail runtime hash oldHash root bi true heap.nodes.length value old)
        (growthEmptyExtension parent) := by
  have hframe := growthEmptyExtensionFrame heap
  have hnExt := (hframe.1 root (List.getElem?_eq_some_iff.mp hn).1).trans hn
  have hsExt := (hframe.2 node.data (List.getElem?_eq_some_iff.mp hs).1).trans hs
  unfold growthStep
  simp only [Bool.false_eq_true, ite_false]
  rw [persistentHamtBindRun, growthEmptyConstructorRun]
  dsimp only
  rw [persistentHamtBindRun, pathReadNodeRun _ root node hnExt]
  simp only [ite_true]
  have hpure : runHamt (pure index : HamtM K V Nat) (growthEmptyExtension heap) =
      (.ok index, growthEmptyExtension heap) := rfl
  rw [persistentHamtBindRun, hpure]
  dsimp only
  rw [persistentHamtBindRun, copyPathVectorSetRun _ node.data index slots
    (.trie heap.nodes.length) hsExt hlo hhi]
  dsimp only
  rw [persistentHamtBindRun,
    growthSetExistingRun
      {growthEmptyExtension heap with vectors := (growthEmptyExtension heap).vectors.set node.data (slots.set (index - 1) (some (.trie heap.nodes.length)))}
      root bi.x node hnExt hb hbit]
  dsimp only
  rw [growthReplaceForkHeap heap node.data (index - 1) slots
    (List.getElem?_eq_some_iff.mp hs).1]
  rfl

theorem growthInsertForkHeap {K V : Type} (heap : HamtHeap K V)
    (root data bit : Nat) (hn : root < heap.nodes.length) (hd : data < heap.vectors.length) :
    { vectors := (growthEmptyExtension heap).vectors.set data [some (.trie heap.nodes.length)],
      nodes := (growthEmptyExtension heap).nodes.set root (⟨data, 2 ^ bit⟩ : HAMTNode K V) } =
      growthEmptyExtension (growthEmptyParent heap root data bit) := by
  simp only [growthEmptyExtension, contextCopiedHeap, growthEmptyParent,
    List.set_append_left _ _ hd, List.set_append_left _ _ hn, List.length_set]

/-- Every later collision step starts at an empty node and installs a
one-child bitmap/vector level before examining the next hash chunks. -/
theorem growthStepOpenPrefix {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (value : V) (old : Leaf K V) (heap : HamtHeap K V)
    (hash oldHash : HashState K) (root data : Nat) (bi : BitmapIndex)
    (hn : heap.nodes[root]? = some (⟨data, 0⟩ : HAMTNode K V))
    (hs : heap.vectors[data]? = some []) (hb : bi.x < 32) :
    runHamt (growthStep runtime index value old (hash, oldHash, root, bi, false, false)) heap =
      runHamt (growthTail runtime hash oldHash root bi false heap.nodes.length value old)
        (growthEmptyExtension (growthEmptyParent heap root data bi.x)) := by
  have hframe := growthEmptyExtensionFrame heap
  have hnExt := (hframe.1 root (List.getElem?_eq_some_iff.mp hn).1).trans hn
  have hsExt := (hframe.2 data (List.getElem?_eq_some_iff.mp hs).1).trans hs
  unfold growthStep
  simp only [Bool.false_eq_true, ite_false]
  rw [persistentHamtBindRun, growthEmptyConstructorRun]
  dsimp only
  rw [persistentHamtBindRun, pathReadNodeRun _ root ⟨data, 0⟩ hnExt]
  dsimp only
  rw [persistentHamtBindRun, growthIndexRun _ root bi.x ⟨data, 0⟩ hnExt]
  simp only [growthRankZero, Nat.zero_add]
  rw [persistentHamtBindRun, updateVectorInsertRun _ data 1 []
    (.trie heap.nodes.length) hsExt (Nat.le_refl 1) (Nat.le_refl 1)]
  dsimp only
  simp only [Nat.sub_self, List.insertIdx_zero]
  rw [persistentHamtBindRun,
    updateBitmapSetRun
      {growthEmptyExtension heap with vectors := (growthEmptyExtension heap).vectors.set data [some (.trie heap.nodes.length)]}
      root bi.x ⟨data, 0⟩ hnExt]
  simp only [growthSetZeroValue bi.x hb]
  rw [growthInsertForkHeap heap root data bi.x
    (List.getElem?_eq_some_iff.mp hn).1 (List.getElem?_eq_some_iff.mp hs).1]
  rfl

/-- The structural invariant after the first collision fork. A finished
state already holds the enlarged pair list; every other state has one fresh
empty hole into which a later finite collision level can be installed. -/
def GrowthOpenInvariant {K V : Type} (initial : HamtHeap K V) (root : Nat)
    (original : List (K × V)) (old : Leaf K V) (key : K) (value : V)
    (input : GrowthState K × HamtHeap K V) : Prop :=
  let (hash, _, current, bi, present, finished) := input.1
  hash.key = key ∧
    if finished then GrowthFinishedRep initial input.2 root original ⟨key, value⟩
    else present = false ∧ bi.x < 32 ∧
      GrowthOpenFocus initial input.2 root current original old

theorem growthOpenSlots {K V : Type} {initial heap : HamtHeap K V}
    {root current : Nat} {original : List (K × V)} {old : Leaf K V}
    (hop : GrowthOpenFocus initial heap root current original old) (data : Nat)
    (hn : heap.nodes[current]? = some (⟨data, 0⟩ : HAMTNode K V)) :
    heap.vectors[data]? = some [] := by
  obtain ⟨_, _, _, storedData, _, _, _, _, hstored, hs, _, _⟩ := hop
  have heq : storedData = data := congrArg HAMTNode.data
    (Option.some.inj (hstored.symm.trans hn))
  subst storedData
  exact hs

/-- The tail either retains the empty hole at the next common hash chunk or
fills it with two leaves at distinct chunks. Both outcomes preserve the
independent tree/pair invariant. -/
theorem growthTailInvariant {K V : Type} (runtime : HamtObjectIdRuntime K)
    (initial heap : HamtHeap K V) (root current child : Nat)
    (original : List (K × V)) (old : Leaf K V) (key : K) (value : V)
    (hash oldHash : HashState K) (bi : BitmapIndex) (present : Bool)
    (hkey : hash.key = key)
    (hop : GrowthOpenFocus initial heap root child original old) :
    ∃ nextState after,
      runHamt (growthTail runtime hash oldHash current bi present child value old) heap =
        (.ok (.yield nextState), after) ∧
      GrowthOpenInvariant initial root original old key value (nextState, after) := by
  obtain ⟨base, before, rest, data, hi, hf, hc, hp, hn, hs, hfn, hfd⟩ := hop
  let nextHash := next runtime hash
  let nextOldHash := next runtime oldHash
  let newBi := BitmapIndex.fromHash nextHash
  let oldBi := BitmapIndex.fromHash nextOldHash
  have hnextKey : nextHash.key = key := by
    rw [pathNextKey, hkey]
  have hopen : GrowthOpenFocus initial heap root child original old :=
    ⟨base, before, rest, data, hi, hf, hc, hp, hn, hs, hfn, hfd⟩
  cases hchunks : (newBi == oldBi) with
  | true =>
    refine ⟨(nextHash, nextOldHash, child, newBi, false, false), heap, ?_, ?_⟩
    · rw [growthTailRun runtime heap hash oldHash current bi present child data value old hn hs]
      change (if newBi == oldBi then _ else _) = _
      rw [hchunks]
      rfl
    · exact ⟨hnextKey, rfl, pathBitmapIndex_lt nextHash, hopen⟩
  | false =>
    have hne : newBi.x ≠ oldBi.x := by
      change (newBi.x == oldBi.x) = false at hchunks
      exact beq_eq_false_iff_ne.mp hchunks
    obtain ⟨lastData, hlastNode, hcomplete⟩ := growthOpenComplete
      (new := (⟨nextHash.key, value⟩ : Leaf K V)) hopen newBi.x oldBi.x
      (pathBitmapIndex_lt nextHash) (pathBitmapIndex_lt nextOldHash) hne
    have hdataEq : lastData = data :=
      congrArg HAMTNode.data (Option.some.inj (hlastNode.symm.trans hn))
    subst lastData
    let after := growthTwoLeafHeap heap child data newBi.x oldBi.x ⟨nextHash.key, value⟩ old
    refine ⟨(nextHash, nextOldHash, current, bi, present, true), after, ?_, ?_⟩
    · rw [growthTailRun runtime heap hash oldHash current bi present child data value old hn hs]
      change (if newBi == oldBi then _ else _) = _
      have hfalse : (newBi == oldBi) = false := by
        change (newBi.x == oldBi.x) = false
        exact beq_eq_false_iff_ne.mpr hne
      rw [hfalse]
      rfl
    · refine ⟨hnextKey, ?_⟩
      simpa only [after, growthTwoLeafHeap, hnextKey, ite_true] using hcomplete

theorem growthOpenStepInvariant {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (initial heap : HamtHeap K V) (root current : Nat)
    (original : List (K × V)) (old : Leaf K V) (key : K) (value : V)
    (hash oldHash : HashState K) (bi : BitmapIndex) (hb : bi.x < 32)
    (hkey : hash.key = key)
    (hop : GrowthOpenFocus initial heap root current original old) :
    ∃ nextState after,
      runHamt (growthStep runtime index value old (hash, oldHash, current, bi, false, false)) heap =
        (.ok (.yield nextState), after) ∧
      GrowthOpenInvariant initial root original old key value (nextState, after) := by
  obtain ⟨data, hn, hnext⟩ := growthOpenExtend hop bi.x hb
  have hs := growthOpenSlots hop data hn
  obtain ⟨nextState, after, htail, hinv⟩ := growthTailInvariant runtime initial
    (growthEmptyExtension (growthEmptyParent heap current data bi.x)) root current
    heap.nodes.length original old key value hash oldHash bi false hkey hnext
  refine ⟨nextState, after, ?_, hinv⟩
  rw [growthStepOpenPrefix runtime index value old heap hash oldHash current data bi hn hs hb]
  exact htail

/-- Induction over a successful frozen loop trace: no loop-totality premise
is required, and the final heap contains exactly the old pairs plus the new
pair. Every induction step uses the actual source-mirrored loop action. -/
theorem growthSuccessfulInvariantTrace {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (initial : HamtHeap K V) (root : Nat) (original : List (K × V))
    (old : Leaf K V) (key : K) (value : V)
    {start last : GrowthState K × HamtHeap K V}
    (ht : SuccessfulLoopTrace (growthStateStep runtime index value old) start last)
    (hinv : GrowthOpenInvariant initial root original old key value start) :
    GrowthFinishedRep initial last.2 root original ⟨key, value⟩ := by
  apply successfulLoopInvariant (growthStateStep runtime index value old)
    (GrowthOpenInvariant initial root original old key value)
    (fun result => GrowthFinishedRep initial result.2 root original ⟨key, value⟩)
    ?_ ht hinv
  intro state hstate output hstep
  rcases state with ⟨⟨hash, oldHash, current, bi, present, finished⟩, heap⟩
  cases finished with
  | false =>
    change hash.key = key ∧ present = false ∧ bi.x < 32 ∧
      GrowthOpenFocus initial heap root current original old at hstate
    obtain ⟨hkey, hpresent, hb, hop⟩ := hstate
    subst present
    obtain ⟨nextState, after, hrun, hnext⟩ := growthOpenStepInvariant runtime index initial heap
      root current original old key value hash oldHash bi hb hkey hop
    have hactual : growthStateStep runtime index value old
        ((hash, oldHash, current, bi, false, false), heap) = .ok (.inr (nextState, after)) := by
      unfold growthStateStep
      rw [hrun]
    have heq := Except.ok.inj (hactual.symm.trans hstep)
    rw [← heq]
    exact hnext
  | true =>
    change hash.key = key ∧ GrowthFinishedRep initial heap root original ⟨key, value⟩ at hstate
    have hactual : growthStateStep runtime index value old
        ((hash, oldHash, current, bi, present, true), heap) =
        .ok (.inl ((hash, oldHash, current, bi, present, true), heap)) := by
      unfold growthStateStep
      rw [growthStepFinished]
    have heq := Except.ok.inj (hactual.symm.trans hstep)
    rw [← heq]
    exact hstate.2

theorem growthInitialStepInvariant {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (value : V) (old : Leaf K V) (base heap : HamtHeap K V)
    (hash oldHash : HashState K) (root : Nat) (bi : BitmapIndex)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (hf : PersistentHeapFrame base heap)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hb : node.bitmap < 2 ^ 32) (hc : countOnes 32 node.bitmap = slots.length)
    (he : EntriesRep base slots pairs)
    (hslot : slots[index - 1]? = some (some (.leaf old)))
    (hbit : Nat.testBit node.bitmap bi.x = true) (hlo : 1 ≤ index)
    (hfn : base.nodes.length ≤ root) (hfd : base.vectors.length ≤ node.data) :
    ∃ nextState after,
      runHamt (growthStep runtime index value old (hash, oldHash, root, bi, true, false)) heap =
        (.ok (.yield nextState), after) ∧
      GrowthOpenInvariant base root pairs old hash.key value (nextState, after) := by
  have hhi : index ≤ slots.length := by
    have h := (List.getElem?_eq_some_iff.mp hslot).1
    omega
  let parent : HamtHeap K V :=
    {heap with vectors := heap.vectors.set node.data (slots.set (index - 1) (some (.trie heap.nodes.length)))}
  have hnext := growthInitialOpen hf root node slots pairs old (index - 1)
    hn hs hb hc he hslot hfn hfd
  obtain ⟨nextState, after, htail, hinv⟩ := growthTailInvariant runtime base
    (growthEmptyExtension parent) root root heap.nodes.length pairs old hash.key value
    hash oldHash bi true rfl hnext
  refine ⟨nextState, after, ?_, hinv⟩
  rw [growthStepPresentPrefix runtime index value old heap hash oldHash root bi node slots
    hn hs hb hbit hlo hhi]
  exact htail

/-- Successful growth from a freshly copied collision leaf preserves all
original heap records and produces the exact old-plus-new pair multiset. -/
theorem growthSuccessfulStructure {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (value : V) (old : Leaf K V) (base heap : HamtHeap K V)
    (hash oldHash : HashState K) (root : Nat) (bi : BitmapIndex)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (hf : PersistentHeapFrame base heap)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hb : node.bitmap < 2 ^ 32) (hc : countOnes 32 node.bitmap = slots.length)
    (he : EntriesRep base slots pairs)
    (hslot : slots[index - 1]? = some (some (.leaf old)))
    (hbit : Nat.testBit node.bitmap bi.x = true) (hlo : 1 ≤ index)
    (hfn : base.nodes.length ≤ root) (hfd : base.vectors.length ≤ node.data)
    {last : GrowthState K} {after : HamtHeap K V}
    (ht : SuccessfulLoopTrace (growthStateStep runtime index value old)
      ((hash, oldHash, root, bi, true, false), heap) (last, after)) :
    GrowthFinishedRep base after root pairs ⟨hash.key, value⟩ := by
  obtain ⟨nextState, nextHeap, hrun, hinv⟩ := growthInitialStepInvariant runtime index value old
    base heap hash oldHash root bi node slots pairs hf hn hs hb hc he hslot hbit hlo hfn hfd
  have hactual : growthStateStep runtime index value old
      ((hash, oldHash, root, bi, true, false), heap) = .ok (.inr (nextState, nextHeap)) := by
    unfold growthStateStep
    rw [hrun]
  cases ht with
  | done hdone =>
    rw [hactual] at hdone
    cases hdone
  | next hnext rest =>
    have heq := Sum.inr.inj (Except.ok.inj (hactual.symm.trans hnext))
    cases heq
    exact growthSuccessfulInvariantTrace runtime index base root pairs old hash.key value rest hinv

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: RouteLocationWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- A finite leaf route carries a pair in the independently flattened tree. -/
theorem routeLocation_mem {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root : Nat} {hash : HashState K} {leaf : Leaf K V}
    (hroute : RoutedLeaf runtime heap root hash leaf) :
    ∀ {pairs : List (K × V)}, TrieRep heap root pairs → (leaf.key, leaf.val) ∈ pairs := by
  induction hroute with
  | leaf hn hs hb hg =>
    intro pairs hr
    cases hr with
    | node hn' hs' _ _ he =>
      cases Option.some.inj (hn'.symm.trans hn)
      cases Option.some.inj (hs'.symm.trans hs)
      exact copyEntries_leafMem he hg
  | child hn hs hb hg hc ih =>
    intro pairs hr
    cases hr with
    | node hn' hs' _ _ he =>
      cases Option.some.inj (hn'.symm.trans hn)
      cases Option.some.inj (hs'.symm.trans hs)
      obtain ⟨_, _, bp, cp, ap, _, _, hp, _, hchild, _⟩ := contextEntriesSplitChild he hg
      rw [hp]
      exact List.mem_append_left _ (List.mem_append_right _ (ih hchild))

/-- A selected entry either is the leaf or contains one of its finite routes. -/
def EntryReaches {K V : Type} (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V)
    (leaf : Leaf K V) : Entry K V → Prop
  | .leaf stored => stored = leaf
  | .trie child => ∃ hash, RoutedLeaf runtime heap child hash leaf

theorem routeLocation_entryMem {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) {index : Nat} {entry : Entry K V} {leaf : Leaf K V}
    (hg : slots[index]? = some (some entry)) (he : EntryReaches runtime heap leaf entry) :
    (leaf.key, leaf.val) ∈ pairs := by
  induction index generalizing slots pairs entry leaf with
  | zero =>
    cases hr with
    | nil => cases hg
    | leaf hrest =>
      cases hg
      cases he
      exact List.mem_cons_self
    | trie hchild hrest =>
      cases hg
      obtain ⟨hash, hroute⟩ := he
      exact List.mem_append_left _ (routeLocation_mem hroute hchild)
  | succ index ih =>
    cases hr with
    | nil => cases hg
    | leaf hrest => exact List.mem_cons_of_mem _ (ih hrest hg he)
    | trie hchild hrest => exact List.mem_append_right _ (ih hrest hg he)

theorem routeLocation_disjoint {K V : Type} {hash : K → JInt .u64}
    {same : K → K → Bool} (hl : KeyLaws hash same)
    {before after : List (K × V)} (hd : Distinct same (before ++ after))
    (pair : K × V) (hb : pair ∈ before) (ha : pair ∈ after) : False := by
  have hfalse := (List.pairwise_append.mp hd).2.2 pair hb pair ha
  rw [hl.refl pair.1] at hfalse
  cases hfalse

/-- Two entries that reach the same leaf cannot occupy different positions in
a represented vector whose flattened pairs have distinct keys. -/
theorem routeLocation_selectedUnique {K V : Type} {runtime : HamtObjectIdRuntime K}
    {same : K → K → Bool} (hl : KeyLaws runtime.objectid same)
    {heap : HamtHeap K V} {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) (hd : Distinct same pairs)
    {i j : Nat} {ei ej : Entry K V} {leaf : Leaf K V}
    (hgi : slots[i]? = some (some ei)) (hgj : slots[j]? = some (some ej))
    (hi : EntryReaches runtime heap leaf ei) (hj : EntryReaches runtime heap leaf ej) : i = j := by
  induction slots generalizing pairs i j ei ej leaf with
  | nil => cases hgi
  | cons slot rest ih =>
    cases hr with
    | leaf hrest =>
      cases i with
      | zero =>
        cases hgi
        cases j with
        | zero => rfl
        | succ j =>
          cases hi
          have hmem := routeLocation_entryMem hrest hgj hj
          have hfalse := (List.pairwise_cons.mp hd).1 _ hmem
          rw [hl.refl _] at hfalse
          cases hfalse
      | succ i =>
        cases j with
        | zero =>
          cases hgj
          cases hj
          have hmem := routeLocation_entryMem hrest hgi hi
          have hfalse := (List.pairwise_cons.mp hd).1 _ hmem
          rw [hl.refl _] at hfalse
          cases hfalse
        | succ j =>
          exact congrArg Nat.succ (ih hrest (List.pairwise_cons.mp hd).2 hgi hgj hi hj)
    | trie hchild hrest =>
      cases i with
      | zero =>
        cases hgi
        cases j with
        | zero => rfl
        | succ j =>
          obtain ⟨hash, hroute⟩ := hi
          exact (routeLocation_disjoint hl hd (leaf.key, leaf.val)
            (routeLocation_mem hroute hchild) (routeLocation_entryMem hrest hgj hj)).elim
      | succ i =>
        cases j with
        | zero =>
          cases hgj
          obtain ⟨hash, hroute⟩ := hj
          exact (routeLocation_disjoint hl hd (leaf.key, leaf.val)
            (routeLocation_mem hroute hchild) (routeLocation_entryMem hrest hgi hi)).elim
        | succ j =>
          exact congrArg Nat.succ (ih hrest (List.pairwise_append.mp hd).2.1 hgi hgj hi hj)

/-- Occupied bounded bitmap positions have injective zero-based ranks. -/
theorem routeLocation_rankInjective (bitmap a b : Nat)
    (ha : a < 32) (hb : b < 32) (hseta : Nat.testBit bitmap a = true)
    (hsetb : Nat.testBit bitmap b = true)
    (hrank : persistentBitmapRank bitmap a = persistentBitmapRank bitmap b) : a = b := by
  by_cases hab : a < b
  · have hlt := persistentRankStrict bitmap a b ha hab hseta
    omega
  by_cases hba : b < a
  · have hlt := persistentRankStrict bitmap b a hb hba hsetb
    omega
  omega

/-- A route tagged with its terminal node and hash state. These tags describe
heap accesses and do not assume any operation's result. -/
inductive LocatedRoute {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) : Nat → HashState K → Nat → HashState K → Leaf K V → Prop where
  | leaf {root : Nat} {hash : HashState K} {node : HAMTNode K V}
      {slots : List (Option (Entry K V))} {leaf : Leaf K V}
      (hnode : heap.nodes[root]? = some node) (hslots : heap.vectors[node.data]? = some slots)
      (hbit : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true)
      (hentry : slots[pathReadIndex node hash - 1]? = some (some (.leaf leaf))) :
      LocatedRoute runtime heap root hash root hash leaf
  | child {root child terminal : Nat} {hash terminalHash : HashState K}
      {node : HAMTNode K V} {slots : List (Option (Entry K V))} {leaf : Leaf K V}
      (hnode : heap.nodes[root]? = some node) (hslots : heap.vectors[node.data]? = some slots)
      (hbit : Nat.testBit node.bitmap (BitmapIndex.fromHash hash).x = true)
      (hentry : slots[pathReadIndex node hash - 1]? = some (some (.trie child)))
      (hchild : LocatedRoute runtime heap child (next runtime hash) terminal terminalHash leaf) :
      LocatedRoute runtime heap root hash terminal terminalHash leaf

theorem locatedRoute_forget {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root terminal : Nat} {hash terminalHash : HashState K}
    {leaf : Leaf K V} (hr : LocatedRoute runtime heap root hash terminal terminalHash leaf) :
    RoutedLeaf runtime heap root hash leaf := by
  induction hr with
  | leaf hn hs hb hg => exact .leaf hn hs hb hg
  | child hn hs hb hg hc ih => exact .child hn hs hb hg ih

theorem locatedRoute_context {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root focus terminal : Nat} {hash focusHash terminalHash : HashState K}
    {leaf : Leaf K V} (hc : RoutingContext runtime heap root hash focus focusHash)
    (hr : LocatedRoute runtime heap focus focusHash terminal terminalHash leaf) :
    LocatedRoute runtime heap root hash terminal terminalHash leaf := by
  induction hc with
  | root => exact hr
  | child hn hs hb hg hc ih => exact .child hn hs hb hg (ih hr)

/-- A selected child inherits key distinctness from the flattened parent. -/
theorem routeLocation_childDistinct {K V : Type} {same : K → K → Bool}
    {heap : HamtHeap K V} {slots : List (Option (Entry K V))} {pairs : List (K × V)}
    (hr : EntriesRep heap slots pairs) (hd : Distinct same pairs)
    {index child : Nat} (hg : slots[index]? = some (some (.trie child))) :
    ∃ childPairs, TrieRep heap child childPairs ∧ Distinct same childPairs := by
  obtain ⟨_, _, bp, cp, ap, _, _, hp, _, hc, _⟩ := contextEntriesSplitChild hr hg
  rw [hp] at hd
  exact ⟨cp, hc, (List.pairwise_append.mp (List.pairwise_append.mp hd).1).2.1⟩

/-- Distinct stored keys force two routes to the same leaf to end at the same
node and depth. The second route retains its own canonical hash evolution. -/
theorem locatedRoute_align {K V : Type} {runtime : HamtObjectIdRuntime K}
    {same : K → K → Bool} (hl : KeyLaws runtime.objectid same)
    {heap : HamtHeap K V} {root terminal : Nat} {hash terminalHash : HashState K}
    {leaf : Leaf K V} (hq : LocatedRoute runtime heap root hash terminal terminalHash leaf) :
    ∀ {pairs : List (K × V)}, TrieRep heap root pairs → Distinct same pairs →
      ∀ ownHash : HashState K, CanonicalHash runtime ownHash → ownHash.depth = hash.depth →
      RoutedLeaf runtime heap root ownHash leaf →
      ∃ ownFinal,
        RoutedLeaf runtime heap terminal ownFinal leaf ∧ CanonicalHash runtime ownFinal ∧
        ownFinal.depth = terminalHash.depth ∧ ownFinal.key = ownHash.key ∧
        (BitmapIndex.fromHash ownFinal).x = (BitmapIndex.fromHash terminalHash).x := by
  induction hq with
  | @leaf root hash node slots leaf hn hs hb hg =>
    intro pairs ht hd ownHash hcanon hdepth hown
    cases ht with
    | node hn' hs' _ _ he =>
      cases Option.some.inj (hn'.symm.trans hn)
      cases Option.some.inj (hs'.symm.trans hs)
      cases hown with
      | leaf hno hso hbo hgo =>
        cases Option.some.inj (hno.symm.trans hn)
        cases Option.some.inj (hso.symm.trans hs)
        have hindex := routeLocation_selectedUnique hl he hd hg hgo rfl rfl
        have hrank : persistentBitmapRank node.bitmap (BitmapIndex.fromHash ownHash).x =
            persistentBitmapRank node.bitmap (BitmapIndex.fromHash hash).x := by
          simpa only [localRoutingIndexRank] using hindex.symm
        exact ⟨ownHash, .leaf hn hs hbo hgo, hcanon, hdepth, rfl,
          routeLocation_rankInjective node.bitmap _ _ (pathBitmapIndex_lt ownHash)
            (pathBitmapIndex_lt hash) hbo hb hrank⟩
      | child hno hso hbo hgo hchild =>
        cases Option.some.inj (hno.symm.trans hn)
        cases Option.some.inj (hso.symm.trans hs)
        have hindex := routeLocation_selectedUnique hl he hd hg hgo rfl ⟨_, hchild⟩
        rw [← hindex] at hgo
        have hbad := hg.symm.trans hgo
        cases hbad
  | @child root child terminal hash terminalHash node slots leaf hn hs hb hg hchild ih =>
    intro pairs ht hd ownHash hcanon hdepth hown
    cases ht with
    | node hn' hs' _ _ he =>
      cases Option.some.inj (hn'.symm.trans hn)
      cases Option.some.inj (hs'.symm.trans hs)
      cases hown with
      | leaf hno hso hbo hgo =>
        cases Option.some.inj (hno.symm.trans hn)
        cases Option.some.inj (hso.symm.trans hs)
        have hindex := routeLocation_selectedUnique hl he hd hg hgo
          ⟨_, locatedRoute_forget hchild⟩ rfl
        rw [← hindex] at hgo
        have hbad := hg.symm.trans hgo
        cases hbad
      | @child _ ownChild _ _ _ _ hno hso hbo hgo hownChild =>
        cases Option.some.inj (hno.symm.trans hn)
        cases Option.some.inj (hso.symm.trans hs)
        have hindex := routeLocation_selectedUnique hl he hd hg hgo
          ⟨_, locatedRoute_forget hchild⟩ ⟨_, hownChild⟩
        rw [← hindex] at hgo
        have hsame : ownChild = child :=
          Entry.trie.inj (Option.some.inj (Option.some.inj (hgo.symm.trans hg)))
        subst ownChild
        obtain ⟨childPairs, hchildTree, hchildDistinct⟩ := routeLocation_childDistinct he hd hg
        obtain ⟨ownFinal, hroute, hcanonical, hfinalDepth, hfinalKey, hfinalBit⟩ :=
          ih hchildTree hchildDistinct (next runtime ownHash) (canonicalHash_next hcanon)
            (by rw [hashNextDepth, hashNextDepth, hdepth]) hownChild
        exact ⟨ownFinal, hroute, hcanonical, hfinalDepth,
          by simpa only [pathNextKey] using hfinalKey, hfinalBit⟩

/-- A leaf's own stored route reaches the selected terminal at exactly the state
computed by the frozen HashState-from-other-depth constructor. -/
theorem locatedRoute_oldHash {K V : Type} {runtime : HamtObjectIdRuntime K}
    {same : K → K → Bool} (hl : KeyLaws runtime.objectid same)
    {heap : HamtHeap K V} {root terminal : Nat} {query : K} {terminalHash : HashState K}
    {leaf : Leaf K V}
    (hq : LocatedRoute runtime heap root (HashState.fromKey runtime query) terminal terminalHash leaf)
    {pairs : List (K × V)} (ht : TrieRep heap root pairs) (hd : Distinct same pairs)
    (ho : RoutedLeaf runtime heap root (HashState.fromKey runtime leaf.key) leaf) :
    RoutedLeaf runtime heap terminal (HashState.fromOtherAtDepth runtime terminalHash leaf.key) leaf ∧
      (BitmapIndex.fromHash (HashState.fromOtherAtDepth runtime terminalHash leaf.key)).x =
        (BitmapIndex.fromHash terminalHash).x := by
  obtain ⟨ownFinal, hr, hc, hd, hk, hb⟩ := locatedRoute_align hl hq ht hd
    (HashState.fromKey runtime leaf.key) (canonicalHash_initial runtime leaf.key) rfl ho
  have hkey : ownFinal.key = leaf.key := hk
  have heq : ownFinal = HashState.fromOtherAtDepth runtime terminalHash leaf.key := by
    rw [hashFromOther_eq_advance]
    simpa only [CanonicalHash, hd, hkey] using hc
  rw [heq] at hr hb
  exact ⟨hr, hb⟩

/-- The old leaf encountered by a copied insertion has its own correctly aligned
hash route at the copied focus. This is the alignment premise used by growth. -/
theorem copyFocus_oldHashOfSelected {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    {query : K} {base after : HamtHeap K V} {result : PathResult K V}
    {before focusPairs rest pairs : List (K × V)}
    (hf : PersistentHeapFrame base after) (htree : TrieRep after result.top pairs)
    (hd : Distinct same pairs) (hparts : pairs = before ++ focusPairs ++ rest)
    (ht : CopyPathTerminal same query base after result focusPairs)
    (hp : RoutingContext runtime base result.top (HashState.fromKey runtime query)
      result.trie result.hash)
    (hr : StoredRouting runtime after result.top pairs)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (old : Leaf K V)
    (hn : after.nodes[result.trie]? = some node) (hs : after.vectors[node.data]? = some slots)
    (hg : slots[result.index - 1]? = some (some (.leaf old)))
    (hpresent : result.present = true) :
    RoutedLeaf runtime after result.trie (HashState.fromOtherAtDepth runtime result.hash old.key) old ∧
      (BitmapIndex.fromHash (HashState.fromOtherAtDepth runtime result.hash old.key)).x = result.bi.x := by
  obtain ⟨terminalNode, terminalSlots, htn, hts, _, _, he, _, _, _, hbi, hi, hbit, _⟩ := ht
  have hnodeEq : terminalNode = node := Option.some.inj (htn.symm.trans hn)
  subst terminalNode
  have hslotsEq : terminalSlots = slots := Option.some.inj (hts.symm.trans hs)
  subst terminalSlots
  have hbit' : Nat.testBit node.bitmap (BitmapIndex.fromHash result.hash).x = true := by
    rw [← hbi]
    exact hbit.trans hpresent
  have hget' : slots[pathReadIndex node result.hash - 1]? = some (some (.leaf old)) := by
    simpa only [hi] using hg
  have hlocation : LocatedRoute runtime after result.top (HashState.fromKey runtime query)
      result.trie result.hash old :=
    locatedRoute_context (copyRouting_contextFrame hf hp) (.leaf hn hs hbit' hget')
  have hmem : (old.key, old.val) ∈ pairs := by
    rw [hparts]
    exact List.mem_append_left _ (List.mem_append_right _ (copyEntries_leafMem he hg))
  have hown := hr old.key old.val hmem
  have hresult := locatedRoute_oldHash hl hlocation htree hd hown
  exact ⟨hresult.1, hresult.2.trans (congrArg BitmapIndex.x hbi.symm)⟩

/-- When a distinct represented tree contains the terminal leaf, its own route
must follow every recorded base-heap ancestor of a query route to that leaf.
The returned prefix lives in the preserved base, so a future focus edit may use it. -/
theorem routeContext_align {K V : Type} {runtime : HamtObjectIdRuntime K}
    {same : K → K → Bool} (hl : KeyLaws runtime.objectid same)
    {base after : HamtHeap K V} (hf : PersistentHeapFrame base after)
    {root focus : Nat} {hash focusHash : HashState K}
    (hc : RoutingContext runtime base root hash focus focusHash) :
    ∀ leaf : Leaf K V, RoutedLeaf runtime after focus focusHash leaf →
      ∀ {pairs : List (K × V)}, TrieRep after root pairs → Distinct same pairs →
        ∀ ownHash : HashState K, CanonicalHash runtime ownHash → ownHash.depth = hash.depth →
          RoutedLeaf runtime after root ownHash leaf →
          ∃ ownFinal,
            RoutedLeaf runtime after focus ownFinal leaf ∧ CanonicalHash runtime ownFinal ∧
            ownFinal.depth = focusHash.depth ∧ ownFinal.key = ownHash.key ∧
            RoutingContext runtime base root ownHash focus ownFinal := by
  induction hc with
  | root root hash =>
    intro leaf htail pairs ht hd ownHash hcanon hdepth hown
    exact ⟨ownHash, hown, hcanon, hdepth, rfl, .root root ownHash⟩
  | @child root child focus hash focusHash node slots hn hs hb hg hc ih =>
    intro leaf htail pairs ht hd ownHash hcanon hdepth hown
    have hqChild := copyRouting_contextFill (copyRouting_contextFrame hf hc) htail
    have hnAfter := (hf.1 root (List.getElem?_eq_some_iff.mp hn).1).trans hn
    have hsAfter := (hf.2 node.data (List.getElem?_eq_some_iff.mp hs).1).trans hs
    cases ht with
    | node hn' hs' _ _ he =>
      cases Option.some.inj (hn'.symm.trans hnAfter)
      cases Option.some.inj (hs'.symm.trans hsAfter)
      cases hown with
      | leaf hno hso hbo hgo =>
        cases Option.some.inj (hno.symm.trans hnAfter)
        cases Option.some.inj (hso.symm.trans hsAfter)
        have hindex := routeLocation_selectedUnique hl he hd hg hgo ⟨_, hqChild⟩ rfl
        rw [← hindex] at hgo
        have hbad := hg.symm.trans hgo
        cases hbad
      | @child _ ownChild _ _ _ _ hno hso hbo hgo hownChild =>
        cases Option.some.inj (hno.symm.trans hnAfter)
        cases Option.some.inj (hso.symm.trans hsAfter)
        have hownGet := hgo
        have hindex := routeLocation_selectedUnique hl he hd hg hgo ⟨_, hqChild⟩ ⟨_, hownChild⟩
        rw [← hindex] at hgo
        have hsame : ownChild = child :=
          Entry.trie.inj (Option.some.inj (Option.some.inj (hgo.symm.trans hg)))
        subst ownChild
        obtain ⟨childPairs, hchildTree, hchildDistinct⟩ := routeLocation_childDistinct he hd hg
        obtain ⟨ownFinal, hroute, hcanonical, hfinalDepth, hfinalKey, hprefix⟩ :=
          ih leaf htail hchildTree hchildDistinct (next runtime ownHash) (canonicalHash_next hcanon)
            (by rw [hashNextDepth, hashNextDepth, hdepth]) hownChild
        exact ⟨ownFinal, hroute, hcanonical, hfinalDepth,
          by simpa only [pathNextKey] using hfinalKey, .child hn hs hbo hownGet hprefix⟩

/-- Companion to the local old-leaf alignment: its whole own-key prefix is
stored in the preserved focus base and survives later local growth. -/
theorem copyFocus_oldHashContextOfSelected {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    {query : K} {base after : HamtHeap K V} {result : PathResult K V}
    {before focusPairs rest pairs : List (K × V)}
    (hf : PersistentHeapFrame base after) (htree : TrieRep after result.top pairs)
    (hd : Distinct same pairs) (hparts : pairs = before ++ focusPairs ++ rest)
    (ht : CopyPathTerminal same query base after result focusPairs)
    (hp : RoutingContext runtime base result.top (HashState.fromKey runtime query)
      result.trie result.hash)
    (hr : StoredRouting runtime after result.top pairs)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (old : Leaf K V)
    (hn : after.nodes[result.trie]? = some node) (hs : after.vectors[node.data]? = some slots)
    (hg : slots[result.index - 1]? = some (some (.leaf old)))
    (hpresent : result.present = true) :
    RoutingContext runtime base result.top (HashState.fromKey runtime old.key)
      result.trie (HashState.fromOtherAtDepth runtime result.hash old.key) := by
  obtain ⟨terminalNode, terminalSlots, htn, hts, _, _, he, _, _, _, hbi, hi, hbit, _⟩ := ht
  have hnodeEq : terminalNode = node := Option.some.inj (htn.symm.trans hn)
  subst terminalNode
  have hslotsEq : terminalSlots = slots := Option.some.inj (hts.symm.trans hs)
  subst terminalSlots
  have hbit' : Nat.testBit node.bitmap (BitmapIndex.fromHash result.hash).x = true := by
    rw [← hbi]
    exact hbit.trans hpresent
  have hget' : slots[pathReadIndex node result.hash - 1]? = some (some (.leaf old)) := by
    simpa only [hi] using hg
  have htail : RoutedLeaf runtime after result.trie result.hash old := .leaf hn hs hbit' hget'
  have hmem : (old.key, old.val) ∈ pairs := by
    rw [hparts]
    exact List.mem_append_left _ (List.mem_append_right _ (copyEntries_leafMem he hg))
  obtain ⟨ownFinal, _, hcanon, hdepth, hkey, hprefix⟩ :=
    routeContext_align hl hf hp old htail htree hd (HashState.fromKey runtime old.key)
      (canonicalHash_initial runtime old.key) rfl (hr old.key old.val hmem)
  have hk : ownFinal.key = old.key := hkey
  have heq : ownFinal = HashState.fromOtherAtDepth runtime result.hash old.key := by
    rw [hashFromOther_eq_advance]
    simpa only [CanonicalHash, hdepth, hk] using hcanon
  rw [heq] at hprefix
  exact hprefix

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: GrowthRoutingWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Collision growth preserves every previously stored route except the leaf
whose old slot is temporarily replaced by the open child chain. -/
def GrowthOtherRoutes {K V : Type} (runtime : HamtObjectIdRuntime K)
    (source heap : HamtHeap K V) (root : Nat) (old : Leaf K V) : Prop :=
  ∀ hash leaf, leaf ≠ old → RoutedLeaf runtime source root hash leaf →
    RoutedLeaf runtime heap root hash leaf

/-- The two collision keys have independent route prefixes through the same
fresh empty focus. All prefixes are recorded in the preserved context heap. -/
def GrowthRoutedOpenFocus {K V : Type} (runtime : HamtObjectIdRuntime K)
    (initial source heap : HamtHeap K V) (root current : Nat)
    (original : List (K × V)) (old : Leaf K V)
    (initialHash initialOldHash hash oldHash : HashState K) : Prop :=
  ∃ contextBase before after data,
    PersistentHeapFrame initial contextBase ∧ PersistentHeapFrame contextBase heap ∧
    TrieContext contextBase root current before after ∧
    original = before ++ (old.key, old.val) :: after ∧
    heap.nodes[current]? = some (⟨data, 0⟩ : HAMTNode K V) ∧
    heap.vectors[data]? = some [] ∧
    contextBase.nodes.length ≤ current ∧ contextBase.vectors.length ≤ data ∧
    RoutingContext runtime contextBase root initialHash current hash ∧
    RoutingContext runtime contextBase root initialOldHash current oldHash ∧
    GrowthOtherRoutes runtime source heap root old

/-- At completion both collision leaves have their specified routes, and all
other routes and the exact old-plus-new pair multiset have been preserved. -/
def GrowthRoutedFinished {K V : Type} (runtime : HamtObjectIdRuntime K)
    (initial source heap : HamtHeap K V) (root : Nat) (original : List (K × V))
    (old : Leaf K V) (initialHash initialOldHash : HashState K) (value : V) : Prop :=
  GrowthFinishedRep initial heap root original ⟨initialHash.key, value⟩ ∧
    RoutedLeaf runtime heap root initialHash ⟨initialHash.key, value⟩ ∧
    RoutedLeaf runtime heap root initialOldHash old ∧
    GrowthOtherRoutes runtime source heap root old

theorem growthRoutedOpen_forget {K V : Type} {runtime : HamtObjectIdRuntime K}
    {initial source heap : HamtHeap K V} {root current : Nat}
    {original : List (K × V)} {old : Leaf K V}
    {initialHash initialOldHash hash oldHash : HashState K}
    (hr : GrowthRoutedOpenFocus runtime initial source heap root current original old
      initialHash initialOldHash hash oldHash) :
    GrowthOpenFocus initial heap root current original old := by
  obtain ⟨base, before, after, data, hi, hf, hc, hp, hn, hs, hfn, hfd, _, _, _⟩ := hr
  exact ⟨base, before, after, data, hi, hf, hc, hp, hn, hs, hfn, hfd⟩

theorem growthRoutingContextKey {K V : Type} {runtime : HamtObjectIdRuntime K}
    {heap : HamtHeap K V} {root focus : Nat} {hash focusHash : HashState K}
    (hr : RoutingContext runtime heap root hash focus focusHash) : focusHash.key = hash.key := by
  induction hr with
  | root => rfl
  | child _ _ _ _ _ ih => exact ih.trans (pathNextKey runtime _)

theorem growthRoutingRankSame (bit : Nat) : persistentBitmapRank (2 ^ bit) bit = 0 := by
  unfold persistentBitmapRank
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self, pathCountOnesZero]

/-- A one-child level is a route prefix for every hash selecting its one bit. -/
theorem growthRoutingOneChild {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root child data bit : Nat) (hash : HashState K)
    (hn : heap.nodes[root]? = some (⟨data, 2 ^ bit⟩ : HAMTNode K V))
    (hs : heap.vectors[data]? = some [some (.trie child)])
    (hbit : (BitmapIndex.fromHash hash).x = bit) :
    RoutingContext runtime heap root hash child (next runtime hash) := by
  refine .child hn hs ?_ ?_ (.root child (next runtime hash))
  · rw [hbit, Nat.testBit_two_pow]
    exact decide_eq_true (Eq.refl _)
  · rw [localRoutingIndexRank, hbit, growthRoutingRankSame] <;> rfl

/-- Existing routes cannot enter an empty focus, so any frame-preserving fill
of that focus preserves every route through its represented ancestor context. -/
theorem growthRoutingPreserveEmpty {K V : Type} (runtime : HamtObjectIdRuntime K)
    {base before after : HamtHeap K V} (hb : PersistentHeapFrame base before)
    (ha : PersistentHeapFrame base after) {root focus : Nat} {bp ap : List (K × V)}
    (hc : TrieContext base root focus bp ap) (data : Nat)
    (hn : before.nodes[focus]? = some (⟨data, 0⟩ : HAMTNode K V)) :
    RouteTransport runtime before root after root := by
  intro hash leaf hr
  exact copyRouting_liftFocus hb ha hc leaf
    (fun otherHash hroute =>
      (routedLeaf_absentAt ⟨data, 0⟩ hn (Nat.zero_testBit _) hroute).elim) hash hr

/-- Both leaves in the final rank-ordered two-entry node are on their exact
selected hash routes; the second insertion preserves the first selected cell. -/
theorem growthRoutingTwoLeaves {K V : Type} (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root data : Nat) (new old : Leaf K V)
    (hash oldHash : HashState K)
    (hn : root < heap.nodes.length) (hs : data < heap.vectors.length)
    (hne : (BitmapIndex.fromHash hash).x ≠ (BitmapIndex.fromHash oldHash).x) :
    let final := growthTwoLeafHeap heap root data (BitmapIndex.fromHash hash).x
      (BitmapIndex.fromHash oldHash).x new old
    RoutedLeaf runtime final root hash new ∧ RoutedLeaf runtime final root oldHash old := by
  let newBit := (BitmapIndex.fromHash hash).x
  let oldBit := (BitmapIndex.fromHash oldHash).x
  let final := growthTwoLeafHeap heap root data newBit oldBit new old
  have hnode : final.nodes[root]? = some
      (⟨data, u32 (2 ^ newBit ||| shiftLeftNat 1 oldBit)⟩ : HAMTNode K V) :=
    List.getElem?_set_self hn
  have hslots : final.vectors[data]? = some
      ([some (.leaf new)].insertIdx (persistentBitmapRank (2 ^ newBit) oldBit)
        (some (.leaf old))) := List.getElem?_set_self hs
  have hbound : 2 ^ newBit < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (pathBitmapIndex_lt hash)
  have hclear : Nat.testBit (2 ^ newBit) oldBit = false := by
    rw [Nat.testBit_two_pow]
    exact decide_eq_false_iff_not.mpr hne
  have hfirstBit : Nat.testBit (2 ^ newBit) (BitmapIndex.fromHash hash).x = true := by
    change Nat.testBit (2 ^ newBit) newBit = true
    rw [Nat.testBit_two_pow]
    exact decide_eq_true (Eq.refl _)
  have hfirstGet : ([some (.leaf new)] : List (Option (Entry K V)))[pathReadIndex (⟨data, 2 ^ newBit⟩ : HAMTNode K V) hash - 1]? = some (some (.leaf new)) := by
    rw [localRoutingIndexRank]
    change ([some (.leaf new)] : List (Option (Entry K V)))[persistentBitmapRank (2 ^ newBit) newBit]? = _
    rw [growthRoutingRankSame] <;> rfl
  obtain ⟨hnewBit, hnewGet⟩ := localRoutingInsertCells (⟨data, 2 ^ newBit⟩ : HAMTNode K V)
    data oldBit [some (.leaf new)] (.leaf old) hbound (pathBitmapIndex_lt oldHash)
    hclear hash (.leaf new) hfirstBit hfirstGet
  refine ⟨.leaf hnode hslots hnewBit hnewGet, ?_⟩
  exact localRoutingInsertedLeaf runtime final root data (2 ^ newBit) [some (.leaf new)] old oldHash
    hbound (by simpa only [List.length_cons, List.length_nil] using
      singletonCountOnesPow 32 newBit (pathBitmapIndex_lt hash)) hclear hnode hslots

/-- Filling the common empty focus installs both routes and preserves every
unrelated leaf route, along with the structural old-plus-new pair multiset. -/
theorem growthRoutingComplete {K V : Type} (runtime : HamtObjectIdRuntime K)
    {initial source heap : HamtHeap K V} {root current : Nat}
    {original : List (K × V)} {old : Leaf K V}
    {initialHash initialOldHash hash oldHash : HashState K} (value : V)
    (hop : GrowthRoutedOpenFocus runtime initial source heap root current original old
      initialHash initialOldHash hash oldHash)
    (hne : (BitmapIndex.fromHash hash).x ≠ (BitmapIndex.fromHash oldHash).x) :
    ∃ data, heap.nodes[current]? = some (⟨data, 0⟩ : HAMTNode K V) ∧
      GrowthRoutedFinished runtime initial source
        (growthTwoLeafHeap heap current data (BitmapIndex.fromHash hash).x
          (BitmapIndex.fromHash oldHash).x ⟨hash.key, value⟩ old)
        root original old initialHash initialOldHash value := by
  have hopen := growthRoutedOpen_forget hop
  obtain ⟨base, before, after, data, hi, hf, hc, hp, hn, hs, hfn, hfd, hnew, hold, hother⟩ := hop
  have hkey := growthRoutingContextKey hnew
  have hnlt := (List.getElem?_eq_some_iff.mp hn).1
  have hslt := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨lastData, hlastNode, hfinished⟩ := growthOpenComplete
    (new := (⟨hash.key, value⟩ : Leaf K V)) hopen (BitmapIndex.fromHash hash).x
    (BitmapIndex.fromHash oldHash).x (pathBitmapIndex_lt hash) (pathBitmapIndex_lt oldHash) hne
  have hd : lastData = data := congrArg HAMTNode.data (Option.some.inj (hlastNode.symm.trans hn))
  subst lastData
  obtain ⟨hfinalFrame, _⟩ := growthTwoLeafFocus hf current data (BitmapIndex.fromHash hash).x
    (BitmapIndex.fromHash oldHash).x (⟨hash.key, value⟩ : Leaf K V) old hnlt hslt hfn hfd
    (pathBitmapIndex_lt hash) (pathBitmapIndex_lt oldHash) hne
  let final := growthTwoLeafHeap heap current data (BitmapIndex.fromHash hash).x
    (BitmapIndex.fromHash oldHash).x (⟨hash.key, value⟩ : Leaf K V) old
  change PersistentHeapFrame base final at hfinalFrame
  change GrowthFinishedRep initial final root original ⟨hash.key, value⟩ at hfinished
  obtain ⟨hnewLeaf, holdLeaf⟩ := growthRoutingTwoLeaves runtime heap current data
    (⟨hash.key, value⟩ : Leaf K V) old hash oldHash hnlt hslt hne
  have hnewRoot := copyRouting_contextFill (copyRouting_contextFrame hfinalFrame hnew) hnewLeaf
  have holdRoot := copyRouting_contextFill (copyRouting_contextFrame hfinalFrame hold) holdLeaf
  have hkeep := growthRoutingPreserveEmpty runtime hf hfinalFrame hc data hn
  refine ⟨data, hn, ?_⟩
  change GrowthRoutedFinished runtime initial source final root original old initialHash initialOldHash value
  refine ⟨?_, ?_, holdRoot, ?_⟩
  · simpa only [hkey] using hfinished
  · simpa only [hkey] using hnewRoot
  · intro otherHash leaf hneLeaf hr
    exact hkeep _ _ (hother otherHash leaf hneLeaf hr)


/-- A common next slot extends both independent route prefixes by one level.
The empty focus ensures all unrelated routes survive that local change. -/
theorem growthRoutingExtend {K V : Type} (runtime : HamtObjectIdRuntime K)
    {initial source heap : HamtHeap K V} {root current : Nat}
    {original : List (K × V)} {old : Leaf K V}
    {initialHash initialOldHash hash oldHash : HashState K}
    (hop : GrowthRoutedOpenFocus runtime initial source heap root current original old
      initialHash initialOldHash hash oldHash)
    (bi : BitmapIndex) (hnewBi : bi = BitmapIndex.fromHash hash)
    (holdBi : bi = BitmapIndex.fromHash oldHash) :
    ∃ data, heap.nodes[current]? = some (⟨data, 0⟩ : HAMTNode K V) ∧
      GrowthRoutedOpenFocus runtime initial source
        (growthEmptyExtension (growthEmptyParent heap current data bi.x))
        root heap.nodes.length original old initialHash initialOldHash
        (next runtime hash) (next runtime oldHash) := by
  obtain ⟨base, before, after, data, hi, hf, hc, hp, hn, hs, hfn, hfd, hnew, hold, hother⟩ := hop
  have hroot := (List.getElem?_eq_some_iff.mp hn).1
  have hdata := (List.getElem?_eq_some_iff.mp hs).1
  have hbi : bi.x < 32 := by rw [hnewBi]; exact pathBitmapIndex_lt hash
  obtain ⟨hparentFrame, hchildContext⟩ :=
    growthEmptyParentContext hf current data bi.x hroot hdata hfn hfd hbi
  let parent := growthEmptyParent heap current data bi.x
  have hnodeParent : parent.nodes[current]? = some (⟨data, 2 ^ bi.x⟩ : HAMTNode K V) :=
    List.getElem?_set_self hroot
  have hslotsParent : parent.vectors[data]? = some [some (.trie heap.nodes.length)] :=
    List.getElem?_set_self hdata
  have hnewChild := growthRoutingOneChild runtime parent current heap.nodes.length data bi.x hash
    hnodeParent hslotsParent (by rw [← hnewBi])
  have holdChild := growthRoutingOneChild runtime parent current heap.nodes.length data bi.x oldHash
    hnodeParent hslotsParent (by rw [← holdBi])
  have hcontext : TrieContext parent root heap.nodes.length before after := by
    simpa only [List.append_nil, List.nil_append] using
      contextCompose (contextFrame hparentFrame hc) hchildContext
  have hnewContext := copyRouting_contextCompose (copyRouting_contextFrame hparentFrame hnew) hnewChild
  have holdContext := copyRouting_contextCompose (copyRouting_contextFrame hparentFrame hold) holdChild
  have hnodeLength : parent.nodes.length = heap.nodes.length := by
    simp only [parent, growthEmptyParent, List.length_set]
  have hfinalFrame : PersistentHeapFrame base (growthEmptyExtension parent) :=
    persistentHeapFrameTrans hparentFrame (growthEmptyExtensionFrame parent)
  have hkeep := growthRoutingPreserveEmpty runtime hf hfinalFrame hc data hn
  refine ⟨data, hn, parent, before, after, parent.vectors.length,
    persistentHeapFrameTrans hi hparentFrame, growthEmptyExtensionFrame parent,
    hcontext, hp, ?_, growthEmptyExtensionSlots parent, ?_, Nat.le_refl _,
    hnewContext, holdContext, ?_⟩
  · rw [← hnodeLength]
    exact growthEmptyExtensionNode parent
  · rw [hnodeLength]
    exact Nat.le_refl _
  · intro otherHash leaf hneLeaf hr
    exact hkeep _ _ (hother otherHash leaf hneLeaf hr)

/-- Replacing the original collision leaf by a fresh child preserves all other
routes and creates the two finite prefixes entering that new empty child. -/
theorem growthRoutingInitial {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (old : Leaf K V) (base heap : HamtHeap K V)
    (hash oldHash : HashState K) (root : Nat) (bi : BitmapIndex)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (hf : PersistentHeapFrame base heap)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hb : node.bitmap < 2 ^ 32) (hc : countOnes 32 node.bitmap = slots.length)
    (he : EntriesRep base slots pairs)
    (hslot : slots[index - 1]? = some (some (.leaf old)))
    (hbit : Nat.testBit node.bitmap bi.x = true)
    (hnewBi : bi = BitmapIndex.fromHash hash) (holdBi : bi = BitmapIndex.fromHash oldHash)
    (hindex : index = pathReadIndex node hash)
    (hfn : base.nodes.length ≤ root) (hfd : base.vectors.length ≤ node.data) :
    let parent : HamtHeap K V :=
      {heap with vectors := heap.vectors.set node.data (slots.set (index - 1) (some (.trie heap.nodes.length)))}
    GrowthRoutedOpenFocus runtime base heap (growthEmptyExtension parent)
      root heap.nodes.length pairs old hash oldHash (next runtime hash) (next runtime oldHash) := by
  let parent : HamtHeap K V :=
    {heap with vectors := heap.vectors.set node.data (slots.set (index - 1) (some (.trie heap.nodes.length)))}
  obtain ⟨before, after, hp, hparentFrame, hcontext⟩ :=
    growthInitialContext hf root node slots pairs old (index - 1)
      hn hs hb hc he hslot hfn hfd
  have hroot := (List.getElem?_eq_some_iff.mp hn).1
  have hdata := (List.getElem?_eq_some_iff.mp hs).1
  have hselected := (List.getElem?_eq_some_iff.mp hslot).1
  have hnParent : parent.nodes[root]? = some node := hn
  have hsParent : parent.vectors[node.data]? = some
      (slots.set (index - 1) (some (.trie heap.nodes.length))) := List.getElem?_set_self hdata
  have hnewContext : RoutingContext runtime parent root hash heap.nodes.length (next runtime hash) := by
    refine .child hnParent hsParent ?_ ?_ (.root heap.nodes.length (next runtime hash))
    · simpa only [hnewBi] using hbit
    · rw [← hindex]
      exact List.getElem?_set_self hselected
  have holdIndex : pathReadIndex node oldHash = index := by
    rw [hindex]
    simp only [pathReadIndex, ← hnewBi, ← holdBi]
  have holdContext : RoutingContext runtime parent root oldHash heap.nodes.length
      (next runtime oldHash) := by
    refine .child hnParent hsParent ?_ ?_ (.root heap.nodes.length (next runtime oldHash))
    · simpa only [holdBi] using hbit
    · rw [holdIndex]
      exact List.getElem?_set_self hselected
  have hext := growthEmptyExtensionFrame parent
  have hfinalFrame : PersistentHeapFrame base (growthEmptyExtension parent) :=
    persistentHeapFrameTrans hparentFrame hext
  have hnFinal : (growthEmptyExtension parent).nodes[root]? = some node :=
    (hext.1 root hroot).trans hnParent
  have hsFinal : (growthEmptyExtension parent).vectors[node.data]? = some
      (slots.set (index - 1) (some (.trie heap.nodes.length))) :=
    (hext.2 node.data (by simpa only [parent, List.length_set] using hdata)).trans hsParent
  have hother : GrowthOtherRoutes runtime heap (growthEmptyExtension parent) root old := by
    intro otherHash leaf hneLeaf hr
    apply localRoutingLiftOtherCells runtime hf hfinalFrame root node node slots
      (slots.set (index - 1) (some (.trie heap.nodes.length))) pairs old he hn hs hnFinal hsFinal
      ?_ otherHash leaf hneLeaf hr
    intro selectedHash entry hneEntry hbEntry hgEntry
    refine ⟨hbEntry, ?_⟩
    have hneIndex : index - 1 ≠ pathReadIndex node selectedHash - 1 := by
      intro hi
      rw [hi, hgEntry] at hslot
      exact hneEntry (Option.some.inj (Option.some.inj hslot))
    rw [List.getElem?_set_ne hneIndex]
    exact hgEntry
  refine ⟨parent, before, after, parent.vectors.length, hparentFrame, hext,
    hcontext, hp, growthEmptyExtensionNode parent, growthEmptyExtensionSlots parent,
    Nat.le_refl _, Nat.le_refl _, hnewContext, holdContext, hother⟩


/-- Open states retain both prefixes; completed states retain both leaf routes. -/
def GrowthRoutingInvariant {K V : Type} (runtime : HamtObjectIdRuntime K)
    (initial source : HamtHeap K V) (root : Nat) (original : List (K × V))
    (old : Leaf K V) (initialHash initialOldHash : HashState K) (value : V)
    (input : GrowthState K × HamtHeap K V) : Prop :=
  let (hash, oldHash, current, bi, present, finished) := input.1
  if finished then
    GrowthRoutedFinished runtime initial source input.2 root original old initialHash initialOldHash value
  else present = false ∧ bi = BitmapIndex.fromHash hash ∧ bi = BitmapIndex.fromHash oldHash ∧
    GrowthRoutedOpenFocus runtime initial source input.2 root current original old
      initialHash initialOldHash hash oldHash

/-- The two next hash slots either keep the paired route prefixes open or
complete both exact leaf routes in the rank-ordered two-entry node. -/
theorem growthRoutingTail {K V : Type} (runtime : HamtObjectIdRuntime K)
    (initial source heap : HamtHeap K V) (root current child : Nat)
    (original : List (K × V)) (old : Leaf K V)
    (initialHash initialOldHash hash oldHash : HashState K)
    (bi : BitmapIndex) (present : Bool) (value : V)
    (hop : GrowthRoutedOpenFocus runtime initial source heap root child original old
      initialHash initialOldHash (next runtime hash) (next runtime oldHash)) :
    ∃ nextState after,
      runHamt (growthTail runtime hash oldHash current bi present child value old) heap =
        (.ok (.yield nextState), after) ∧
      GrowthRoutingInvariant runtime initial source root original old initialHash initialOldHash value
        (nextState, after) := by
  have hopen := hop
  obtain ⟨base, before, rest, data, hi, hf, hc, hp, hn, hs, hfn, hfd, hnew, hold, hother⟩ := hop
  let nextHash := next runtime hash
  let nextOldHash := next runtime oldHash
  let newBi := BitmapIndex.fromHash nextHash
  let oldBi := BitmapIndex.fromHash nextOldHash
  cases hchunks : (newBi == oldBi) with
  | true =>
    have hbiEq : newBi = oldBi := by
      have hx : newBi.x = oldBi.x := by
        change (newBi.x == oldBi.x) = true at hchunks
        exact eq_of_beq hchunks
      exact congrArg BitmapIndex.mk hx
    refine ⟨(nextHash, nextOldHash, child, newBi, false, false), heap, ?_, ?_⟩
    · rw [growthTailRun runtime heap hash oldHash current bi present child data value old hn hs]
      change (if newBi == oldBi then _ else _) = _
      rw [hchunks] <;> rfl
    · exact ⟨rfl, rfl, hbiEq, hopen⟩
  | false =>
    have hne : newBi.x ≠ oldBi.x := by
      change (newBi.x == oldBi.x) = false at hchunks
      exact beq_eq_false_iff_ne.mp hchunks
    obtain ⟨lastData, hlastNode, hcomplete⟩ := growthRoutingComplete runtime value hopen hne
    have hd : lastData = data := congrArg HAMTNode.data (Option.some.inj (hlastNode.symm.trans hn))
    subst lastData
    let final := growthTwoLeafHeap heap child data newBi.x oldBi.x ⟨nextHash.key, value⟩ old
    refine ⟨(nextHash, nextOldHash, current, bi, present, true), final, ?_, ?_⟩
    · rw [growthTailRun runtime heap hash oldHash current bi present child data value old hn hs]
      change (if newBi == oldBi then _ else _) = _
      rw [hchunks] <;> rfl
    · exact hcomplete

/-- One unfinished growth step extends both prefixes and then examines the
next pair of slots, following the exact frozen step normal form. -/
theorem growthRoutingOpenStep {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (initial source heap : HamtHeap K V) (root current : Nat)
    (original : List (K × V)) (old : Leaf K V)
    (initialHash initialOldHash hash oldHash : HashState K) (bi : BitmapIndex) (value : V)
    (hnewBi : bi = BitmapIndex.fromHash hash) (holdBi : bi = BitmapIndex.fromHash oldHash)
    (hop : GrowthRoutedOpenFocus runtime initial source heap root current original old
      initialHash initialOldHash hash oldHash) :
    ∃ nextState after,
      runHamt (growthStep runtime index value old (hash, oldHash, current, bi, false, false)) heap =
        (.ok (.yield nextState), after) ∧
      GrowthRoutingInvariant runtime initial source root original old initialHash initialOldHash value
        (nextState, after) := by
  obtain ⟨data, hn, hnext⟩ := growthRoutingExtend runtime hop bi hnewBi holdBi
  have hs := growthOpenSlots (growthRoutedOpen_forget hop) data hn
  have hbi : bi.x < 32 := by rw [hnewBi]; exact pathBitmapIndex_lt hash
  obtain ⟨nextState, after, htail, hinv⟩ := growthRoutingTail runtime initial source
    (growthEmptyExtension (growthEmptyParent heap current data bi.x)) root current heap.nodes.length
    original old initialHash initialOldHash hash oldHash bi false value hnext
  refine ⟨nextState, after, ?_, hinv⟩
  rw [growthStepOpenPrefix runtime index value old heap hash oldHash current data bi hn hs hbi]
  exact htail

/-- Finite successful traces preserve both routes through every common-slot
level and finish with exactly the two prescribed collision leaf routes. -/
theorem growthRoutingSuccessfulTrace {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (initial source : HamtHeap K V) (root : Nat) (original : List (K × V))
    (old : Leaf K V) (initialHash initialOldHash : HashState K) (value : V)
    {start last : GrowthState K × HamtHeap K V}
    (ht : SuccessfulLoopTrace (growthStateStep runtime index value old) start last)
    (hinv : GrowthRoutingInvariant runtime initial source root original old
      initialHash initialOldHash value start) :
    GrowthRoutedFinished runtime initial source last.2 root original old initialHash initialOldHash value := by
  apply successfulLoopInvariant (growthStateStep runtime index value old)
    (GrowthRoutingInvariant runtime initial source root original old initialHash initialOldHash value)
    (fun result => GrowthRoutedFinished runtime initial source result.2 root original old
      initialHash initialOldHash value) ?_ ht hinv
  intro state hstate output hstep
  rcases state with ⟨⟨hash, oldHash, current, bi, present, finished⟩, heap⟩
  cases finished with
  | false =>
    change present = false ∧ bi = BitmapIndex.fromHash hash ∧ bi = BitmapIndex.fromHash oldHash ∧
      GrowthRoutedOpenFocus runtime initial source heap root current original old
        initialHash initialOldHash hash oldHash at hstate
    obtain ⟨hpresent, hnewBi, holdBi, hop⟩ := hstate
    subst present
    obtain ⟨nextState, after, hrun, hnext⟩ := growthRoutingOpenStep runtime index initial source heap
      root current original old initialHash initialOldHash hash oldHash bi value hnewBi holdBi hop
    have hactual : growthStateStep runtime index value old
        ((hash, oldHash, current, bi, false, false), heap) = .ok (.inr (nextState, after)) := by
      unfold growthStateStep
      rw [hrun]
    have heq := Except.ok.inj (hactual.symm.trans hstep)
    rw [← heq]
    exact hnext
  | true =>
    change GrowthRoutedFinished runtime initial source heap root original old
      initialHash initialOldHash value at hstate
    have hactual : growthStateStep runtime index value old
        ((hash, oldHash, current, bi, present, true), heap) =
        .ok (.inl ((hash, oldHash, current, bi, present, true), heap)) := by
      unfold growthStateStep
      rw [growthStepFinished]
    have heq := Except.ok.inj (hactual.symm.trans hstep)
    rw [← heq]
    exact hstate

/-- The first collision fork opens both routes at the same new child; the
following tail either keeps that paired focus open or completes the split. -/
theorem growthRoutingInitialStep {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (value : V) (old : Leaf K V) (base heap : HamtHeap K V)
    (hash oldHash : HashState K) (root : Nat) (bi : BitmapIndex)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (hf : PersistentHeapFrame base heap)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hb : node.bitmap < 2 ^ 32) (hc : countOnes 32 node.bitmap = slots.length)
    (he : EntriesRep base slots pairs)
    (hslot : slots[index - 1]? = some (some (.leaf old)))
    (hbit : Nat.testBit node.bitmap bi.x = true) (hlo : 1 ≤ index)
    (hfn : base.nodes.length ≤ root) (hfd : base.vectors.length ≤ node.data)
    (hnewBi : bi = BitmapIndex.fromHash hash) (holdBi : bi = BitmapIndex.fromHash oldHash)
    (hindex : index = pathReadIndex node hash) :
    ∃ nextState after,
      runHamt (growthStep runtime index value old (hash, oldHash, root, bi, true, false)) heap =
        (.ok (.yield nextState), after) ∧
      GrowthRoutingInvariant runtime base heap root pairs old hash oldHash value (nextState, after) := by
  have hhi : index ≤ slots.length := by
    have hi := (List.getElem?_eq_some_iff.mp hslot).1
    omega
  let parent : HamtHeap K V :=
    {heap with vectors := heap.vectors.set node.data (slots.set (index - 1) (some (.trie heap.nodes.length)))}
  have hopen := growthRoutingInitial runtime index old base heap hash oldHash root bi node slots pairs
    hf hn hs hb hc he hslot hbit hnewBi holdBi hindex hfn hfd
  obtain ⟨nextState, after, htail, hinv⟩ := growthRoutingTail runtime base heap
    (growthEmptyExtension parent) root root heap.nodes.length pairs old hash oldHash hash oldHash bi true value hopen
  refine ⟨nextState, after, ?_, hinv⟩
  rw [growthStepPresentPrefix runtime index value old heap hash oldHash root bi node slots
    hn hs hb hbit hlo hhi]
  exact htail

/-- Local successful growth preserves the new and aligned old hash routes,
and preserves arbitrary hash routes only for leaves different from the old leaf. -/
theorem growthSuccessfulRouting {K V : Type} (runtime : HamtObjectIdRuntime K)
    (index : Nat) (value : V) (old : Leaf K V) (base heap : HamtHeap K V)
    (hash oldHash : HashState K) (root : Nat) (bi : BitmapIndex)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (pairs : List (K × V))
    (hf : PersistentHeapFrame base heap)
    (hn : heap.nodes[root]? = some node) (hs : heap.vectors[node.data]? = some slots)
    (hb : node.bitmap < 2 ^ 32) (hc : countOnes 32 node.bitmap = slots.length)
    (he : EntriesRep base slots pairs)
    (hslot : slots[index - 1]? = some (some (.leaf old)))
    (hbit : Nat.testBit node.bitmap bi.x = true) (hlo : 1 ≤ index)
    (hfn : base.nodes.length ≤ root) (hfd : base.vectors.length ≤ node.data)
    (hnewBi : bi = BitmapIndex.fromHash hash) (holdBi : bi = BitmapIndex.fromHash oldHash)
    (hindex : index = pathReadIndex node hash)
    {last : GrowthState K} {after : HamtHeap K V}
    (ht : SuccessfulLoopTrace (growthStateStep runtime index value old)
      ((hash, oldHash, root, bi, true, false), heap) (last, after)) :
    GrowthRoutedFinished runtime base heap after root pairs old hash oldHash value := by
  obtain ⟨nextState, nextHeap, hrun, hinv⟩ := growthRoutingInitialStep runtime index value old
    base heap hash oldHash root bi node slots pairs hf hn hs hb hc he hslot hbit hlo hfn hfd
    hnewBi holdBi hindex
  have hactual : growthStateStep runtime index value old
      ((hash, oldHash, root, bi, true, false), heap) = .ok (.inr (nextState, nextHeap)) := by
    unfold growthStateStep
    rw [hrun]
  cases ht with
  | done hdone =>
    rw [hactual] at hdone
    cases hdone
  | next hnext rest =>
    have heq := Sum.inr.inj (Except.ok.inj (hactual.symm.trans hnext))
    cases heq
    exact growthRoutingSuccessfulTrace runtime index base heap root pairs old hash oldHash value rest hinv

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: CollectionWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1
open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict
open JuliaLean.Proofs.base.dict.round2
open JuliaLean.base.hamt

variable {K V : Type}

def collectionSingletonHeap (k : K) (v : V) (bitmap : Nat) : HamtHeap K V :=
  ⟨[[some (.leaf ⟨k, v⟩)]], [⟨0, bitmap⟩]⟩

abbrev CollectionIterState (K V : Type) :=
  List (Nat × Nat) × Option ((K × V) × IterState K V)

def collectionIterStep (_ : Unit) (s : CollectionIterState K V) :
    HamtM K V (ForInStep (CollectionIterState K V)) := do
  if s.2.isNone && !s.1.isEmpty then
    match s.1 with
    | [] => pure (.yield s)
    | (data, i) :: parents =>
      if i > (← heapVectorOps.length data) then pure (.yield (parents, s.2))
      else
        let entry ← heapVectorOps.get data i
        let frames := (data, i + 1) :: parents
        match entry with
        | .leaf leaf => pure (.yield (frames, some ((leaf.key, leaf.val), ⟨frames⟩)))
        | .trie child =>
          let childData ← nodeData child
          pure (.yield ((childData, 1) :: frames, s.2))
  else pure (.done s)

theorem collectionRunBind {A B : Type} (action : HamtM K V A)
    (next : A → HamtM K V B) (heap : HamtHeap K V) :
    runHamt (action >>= next) heap =
      match runHamt action heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok value, heap') => runHamt (next value) heap' := by
  cases h : runHamt action heap with
  | mk outcome heap' =>
    have hrun : StateT.run (ExceptT.run action) heap = (outcome, heap') := h
    unfold runHamt
    rw [ExceptT.run_bind, StateT.run_bind, hrun]
    cases outcome <;> rfl

theorem collectionLoopEquation {B : Type} (state : B)
    (step : Unit → B → HamtM K V (ForInStep B)) (heap : HamtHeap K V) :
    runHamt (Lean.Loop.forIn (m := HamtM K V) (β := B) ({} : Lean.Loop) state step) heap =
      match runHamt (step () state) heap with
      | (.error error, heap') => (.error error, heap')
      | (.ok (.done result), heap') => (.ok result, heap')
      | (.ok (.yield next), heap') =>
          runHamt (Lean.Loop.forIn (m := HamtM K V) (β := B) ({} : Lean.Loop) next step) heap' := by
  cases h : runHamt (step () state) heap with
  | mk out heap' =>
    have hrun : StateT.run (ExceptT.run (step () state)) heap = (out, heap') := h
    rw [Lean.Loop.forIn_eq_of_monadTail]
    unfold runHamt
    rw [ExceptT.run_bind, StateT.run_bind, hrun]
    cases out with
    | error error => rfl
    | ok result => cases result <;> rfl

theorem collectionSingletonFirst (k : K) (v : V) (bitmap : Nat) :
    runHamt (iterate heapVectorOps 0 none) (collectionSingletonHeap k v bitmap) =
      (.ok (some ((k, v), ⟨[(0, 2)]⟩)), collectionSingletonHeap k v bitmap) := by
  change runHamt ((Lean.Loop.forIn (m := HamtM K V) ({} : Lean.Loop)
    ([(0, 1)], none) collectionIterStep) >>= fun s => pure s.2)
    (collectionSingletonHeap k v bitmap) = _
  rw [collectionRunBind, collectionLoopEquation]
  have hs : runHamt (collectionIterStep () ([(0, 1)], none))
      (collectionSingletonHeap k v bitmap) =
      (.ok (.yield ([(0, 2)], some ((k, v), ⟨[(0, 2)]⟩))),
        collectionSingletonHeap k v bitmap) := by rfl
  rw [hs]
  dsimp only
  rw [collectionLoopEquation]
  have hd : runHamt (collectionIterStep () ([(0, 2)], some ((k, v), ⟨[(0, 2)]⟩)))
      (collectionSingletonHeap k v bitmap) =
      (.ok (.done ([(0, 2)], some ((k, v), ⟨[(0, 2)]⟩))),
        collectionSingletonHeap k v bitmap) := by rfl
  rw [hd]
  rfl

theorem collectionSingletonEnd (k : K) (v : V) (bitmap : Nat) :
    runHamt (iterate heapVectorOps 0 (some ⟨[(0, 2)]⟩))
      (collectionSingletonHeap k v bitmap) =
      (.ok none, collectionSingletonHeap k v bitmap) := by
  change runHamt ((Lean.Loop.forIn (m := HamtM K V) ({} : Lean.Loop)
    ([(0, 2)], none) collectionIterStep) >>= fun s => pure s.2)
    (collectionSingletonHeap k v bitmap) = _
  rw [collectionRunBind, collectionLoopEquation]
  have hs : runHamt (collectionIterStep () ([(0, 2)], none))
      (collectionSingletonHeap k v bitmap) =
      (.ok (.yield ([], none)), collectionSingletonHeap k v bitmap) := by rfl
  rw [hs]
  dsimp only
  rw [collectionLoopEquation]
  have hd : runHamt (collectionIterStep () ([], none))
      (collectionSingletonHeap k v bitmap) =
      (.ok (.done ([], none)), collectionSingletonHeap k v bitmap) := by rfl
  rw [hd]
  rfl

def collectionEmptyHeap (K V : Type) : HamtHeap K V := ⟨[[]], [⟨0, 0⟩]⟩

theorem collectionEmptyIterate :
    runHamt (iterate heapVectorOps 0 none) (collectionEmptyHeap K V) =
      (.ok none, collectionEmptyHeap K V) := by
  change runHamt ((Lean.Loop.forIn (m := HamtM K V) ({} : Lean.Loop)
    ([(0, 1)], none) collectionIterStep) >>= fun s => pure s.2)
    (collectionEmptyHeap K V) = _
  rw [collectionRunBind, collectionLoopEquation]
  have hs : runHamt (collectionIterStep () ([(0, 1)], none))
      (collectionEmptyHeap K V) =
      (.ok (.yield ([], none)), collectionEmptyHeap K V) := by rfl
  rw [hs]
  dsimp only
  rw [collectionLoopEquation]
  have hd : runHamt (collectionIterStep () ([], none))
      (collectionEmptyHeap K V) =
      (.ok (.done ([], none)), collectionEmptyHeap K V) := by rfl
  rw [hd]
  rfl

theorem collectionSingletonLength (k : K) (v : V) (bitmap : Nat) :
    lengthHAMT heapVectorOps 0 (collectionSingletonHeap k v bitmap) =
      some (.ok (JInt.lit .i64 1), collectionSingletonHeap k v bitmap) := by
  rw [lengthHAMT.eq_def]
  change lengthEntries heapVectorOps 0 1 1 (JInt.lit .i64 0)
    (collectionSingletonHeap k v bitmap) = _
  rw [lengthEntries.eq_def]
  change lengthEntries heapVectorOps 0 1 2
    (JuliaLean.base.int.add (JInt.lit .i64 0) (JInt.lit .i64 1))
    (collectionSingletonHeap k v bitmap) = _
  rw [lengthEntries.eq_def]
  have hadd : JuliaLean.base.int.add (JInt.lit .i64 0) (JInt.lit .i64 1) =
      JInt.lit .i64 1 := by decide
  simp only [show ¬ 2 ≤ 1 from by decide, ite_false, hadd]

theorem collectionSingletonIsEmpty (k : K) (v : V) (bitmap : Nat)
    (hbitmap : bitmap ≠ 0) :
    isemptyHAMT heapVectorOps 0 (collectionSingletonHeap k v bitmap) =
      some (.ok false, collectionSingletonHeap k v bitmap) := by
  rw [isemptyHAMT.eq_def]
  have hlevel : runHamt (islevel_empty 0) (collectionSingletonHeap k v bitmap) =
      (.ok false, collectionSingletonHeap k v bitmap) := by
    have hzero : (bitmap == 0) = false := beq_eq_false_iff_ne.mpr hbitmap
    have hread : runHamt (islevel_empty 0) (collectionSingletonHeap k v bitmap) =
        (.ok (bitmap == 0), collectionSingletonHeap k v bitmap) := rfl
    rw [hzero] at hread
    exact hread
  rw [hlevel]
  change isemptyEntries heapVectorOps 0 1 1 true
    (collectionSingletonHeap k v bitmap) = _
  rw [isemptyEntries.eq_def]
  change isemptyEntries heapVectorOps 0 1 2 false
    (collectionSingletonHeap k v bitmap) = _
  rw [isemptyEntries.eq_def]
  rfl

def collectionSingletonDict (k : K) (v : V) (bitmap : Nat) :
    PersistentDict K V (PTrie K V) := ⟨.ok (collectionSingletonHeap k v bitmap, 0)⟩

theorem collectionSingletonIterate (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (k : K) (v : V) (bitmap : Nat) :
    persistentIterate (hamtOps same runtime) (collectionSingletonDict k v bitmap) =
      some ((k, v), ⟨[(0, 2)]⟩) := by
  unfold persistentIterate hamtOps runTrie collectionSingletonDict
  dsimp only
  rw [collectionSingletonFirst]

theorem collectionSingletonIterateEnd (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (k : K) (v : V) (bitmap : Nat) :
    persistentIterate (hamtOps same runtime) (collectionSingletonDict k v bitmap)
      (some ⟨[(0, 2)]⟩) = none := by
  unfold persistentIterate hamtOps runTrie collectionSingletonDict
  dsimp only
  rw [collectionSingletonEnd]

theorem collectionSingletonCollect (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (k : K) (v : V) (bitmap : Nat) (fuel : Nat) :
    persistentCollectFuel (hamtOps same runtime) (collectionSingletonDict k v bitmap)
      (fuel + 2) none = [(k, v)] := by
  unfold persistentCollectFuel
  rw [collectionSingletonIterate]
  dsimp only
  unfold persistentCollectFuel
  rw [collectionSingletonIterateEnd]

theorem collectionSingletonNativeLength (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (k : K) (v : V) (bitmap : Nat) :
    persistentLength (hamtOps same runtime) (collectionSingletonDict k v bitmap) =
      some (.ok (JInt.lit .i64 1)) := by
  unfold persistentLength hamtOps runPartialTrie runPartialHamt collectionSingletonDict
  dsimp only
  rw [collectionSingletonLength]
  rfl

theorem collectionSingletonNonempty (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (k : K) (v : V) (bitmap : Nat)
    (hbitmap : bitmap ≠ 0) :
    persistentIsEmpty (hamtOps same runtime) (collectionSingletonDict k v bitmap) =
      some (.ok false) := by
  unfold persistentIsEmpty hamtOps runPartialTrie runPartialHamt collectionSingletonDict
  dsimp only
  rw [collectionSingletonIsEmpty k v bitmap hbitmap]
  rfl

theorem collectionEmptyPersistentIterate (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) :
    persistentIterate (hamtOps same runtime) (persistentEmpty (hamtOps (V := V) same runtime)) =
      none := by
  change persistentIterate (hamtOps same runtime)
    (⟨.ok (collectionEmptyHeap K V, 0)⟩ : PersistentDict K V (PTrie K V)) = none
  unfold persistentIterate hamtOps runTrie
  dsimp only
  rw [collectionEmptyIterate]

theorem collectionEmptyCollect (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (fuel : Nat) :
    persistentCollectFuel (hamtOps same runtime) (persistentEmpty (hamtOps (V := V) same runtime))
      (fuel + 1) none = [] := by
  unfold persistentCollectFuel
  rw [collectionEmptyPersistentIterate]

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: CollectionTreeWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1
open JuliaLean JuliaLean.C JuliaLean.base.dict JuliaLean.Proofs.base.dict JuliaLean.base.hamt

variable {K V : Type}

theorem collectionWrapCongr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  unfold wrapInt
  have hp : (2 : Int) ^ t.bits = ((2 ^ t.bits : Nat) : Int) := (Int.natCast_pow 2 t.bits).symm
  rw [hp]
  have hm : (a + (2 : Int) ^ (t.bits - 1)) % ((2 ^ t.bits : Nat) : Int) =
      (b + (2 : Int) ^ (t.bits - 1)) % ((2 ^ t.bits : Nat) : Int) := by
    rw [Int.add_emod a, h, ← Int.add_emod]
  rw [hm, h]

theorem collectionWrapMod (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  unfold wrapInt
  have hp : (2 : Int) ^ t.bits = ((2 ^ t.bits : Nat) : Int) := (Int.natCast_pow 2 t.bits).symm
  rw [hp]
  split
  · rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod, Int.add_sub_cancel]
  · exact Int.emod_emod z _

theorem collectionToJIntOfInt (t : IntTy) (z : Int) :
    (toJInt t (BitVec.ofInt t.bits z)).val = wrapInt t z := by
  change wrapInt t (if t.signed then (BitVec.ofInt t.bits z).toInt
    else ((BitVec.ofInt t.bits z).toNat : Int)) = _
  apply collectionWrapCongr
  split
  · rw [BitVec.toInt_ofInt]
    exact Int.bmod_emod
  · rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have := Nat.pow_pos (n := t.bits) (by decide : 0 < 2)
      omega)), Int.emod_emod]

theorem collectionAddVal {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.add x y).val = wrapInt t (x.val + y.val) := by
  simp only [JuliaLean.base.int.add, JuliaLean.base.int.add_int, jlAddInt, fromJInt]
  rw [← BitVec.ofInt_add, collectionToJIntOfInt]

theorem collectionAddNat (m n : Nat) :
    JuliaLean.base.int.add (JInt.lit .i64 m) (JInt.lit .i64 n) =
      JInt.lit .i64 (m + n : Nat) := by
  apply Subtype.ext
  rw [collectionAddVal]
  change wrapInt .i64 (wrapInt .i64 (m : Int) + wrapInt .i64 (n : Int)) =
    wrapInt .i64 ((m + n : Nat) : Int)
  rw [Int.natCast_add]
  apply collectionWrapCongr
  rw [Int.add_emod, collectionWrapMod, collectionWrapMod, ← Int.add_emod]

theorem collectionReadNodeRun (heap : HamtHeap K V) (root : Nat) (node : HAMTNode K V)
    (hnode : heap.nodes[root]? = some node) :
    runHamt (readNode root) heap = (.ok node, heap) := by
  have hget : runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := rfl
  unfold readNode
  rw [collectionRunBind, hget]
  simp only [hnode] <;> rfl

theorem collectionVectorSlotsRun (heap : HamtHeap K V) (data : Nat)
    (slots : List (Option (JuliaLean.base.hamt.Entry K V)))
    (hslots : heap.vectors[data]? = some slots) :
    runHamt (heapVectorSlots data) heap = (.ok slots, heap) := by
  have hget : runHamt (get : HamtM K V (HamtHeap K V)) heap = (.ok heap, heap) := rfl
  unfold heapVectorSlots
  rw [collectionRunBind, hget]
  simp only [hslots] <;> rfl

theorem collectionVectorLengthRun (heap : HamtHeap K V) (data : Nat)
    (slots : List (Option (JuliaLean.base.hamt.Entry K V)))
    (hslots : heap.vectors[data]? = some slots) :
    runHamt (heapVectorOps.length data) heap = (.ok slots.length, heap) := by
  change runHamt (heapVectorLength data) heap = _
  unfold heapVectorLength
  rw [collectionRunBind, collectionVectorSlotsRun heap data slots hslots]
  rfl

theorem collectionVectorGetRun (heap : HamtHeap K V) (data : Nat)
    (beforeSlots rest : List (Option (JuliaLean.base.hamt.Entry K V)))
    (entry : JuliaLean.base.hamt.Entry K V)
    (hslots : heap.vectors[data]? = some (beforeSlots ++ some entry :: rest)) :
    runHamt (heapVectorOps.get data (beforeSlots.length + 1)) heap = (.ok entry, heap) := by
  change runHamt (heapVectorGet data (beforeSlots.length + 1)) heap = _
  unfold heapVectorGet
  rw [collectionRunBind, collectionVectorSlotsRun heap data (beforeSlots ++ some entry :: rest) hslots]
  have hnotzero : beforeSlots.length + 1 ≠ 0 := by omega
  have hget : (beforeSlots ++ some entry :: rest)[beforeSlots.length]? = some (some entry) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  simp only [hnotzero, ite_false, Nat.add_sub_cancel, hget] <;> rfl

/-- A finite heap tree's native length is its leaf count modulo the Julia Int64 word. -/
theorem collectionTreeLength (heap : HamtHeap K V) {root : Nat} {pairs : List (K × V)}
    (hrep : TrieRep heap root pairs) :
    lengthHAMT heapVectorOps root heap = some (.ok (JInt.lit .i64 pairs.length), heap) := by
  let nodeMotive : (root : Nat) → (pairs : List (K × V)) → TrieRep heap root pairs → Prop :=
    fun root pairs _ =>
      lengthHAMT heapVectorOps root heap = some (.ok (JInt.lit .i64 pairs.length), heap)
  let entriesMotive : (slots : List (Option (JuliaLean.base.hamt.Entry K V))) →
      (pairs : List (K × V)) → EntriesRep heap slots pairs → Prop :=
    fun slots pairs _ => ∀ (data : Nat)
      (beforeSlots : List (Option (JuliaLean.base.hamt.Entry K V))) (acc : Nat),
      heap.vectors[data]? = some (beforeSlots ++ slots) →
      lengthEntries heapVectorOps data (beforeSlots.length + slots.length) (beforeSlots.length + 1)
        (JInt.lit .i64 acc) heap = some (.ok (JInt.lit .i64 (acc + pairs.length : Nat)), heap)
  have hrec : nodeMotive root pairs hrep := by
    refine TrieRep.rec (motive_1 := nodeMotive) (motive_2 := entriesMotive)
      ?_ ?_ ?_ ?_ hrep
    · intro root node slots pairs hnode hslots _ _ hentries ihEntries
      dsimp only [nodeMotive]
      dsimp only [entriesMotive] at ihEntries
      rw [lengthHAMT.eq_def, collectionReadNodeRun heap root node hnode]
      dsimp only
      rw [collectionVectorLengthRun heap node.data slots hslots]
      simpa only [List.length_nil, Nat.zero_add, Int.natCast_zero] using ihEntries node.data [] 0 hslots
    · intro data beforeSlots acc hslots
      rw [lengthEntries.eq_def]
      have hbound : ¬ beforeSlots.length + 1 ≤ beforeSlots.length := by omega
      simp only [List.length_nil, Nat.add_zero, hbound, ite_false]
    · intro leaf rest pairs hrest ihRest data beforeSlots acc hslots
      rw [lengthEntries.eq_def]
      have hbound : beforeSlots.length + 1 ≤ beforeSlots.length + (some (.leaf leaf) :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [ite_eq_left hbound, collectionVectorGetRun heap data beforeSlots rest (.leaf leaf) hslots]
      dsimp only
      change lengthEntries heapVectorOps data (beforeSlots.length + (some (.leaf leaf) :: rest).length)
        (beforeSlots.length + 1 + 1)
        (JuliaLean.base.int.add (JInt.lit .i64 acc) (JInt.lit .i64 1)) heap = _
      have hadd := collectionAddNat acc 1
      simp only [Int.natCast_one] at hadd
      rw [hadd]
      have hslotsNext : heap.vectors[data]? = some ((beforeSlots ++ [some (.leaf leaf)]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using hslots
      have hnext := ihRest data (beforeSlots ++ [some (.leaf leaf)]) (acc + 1) hslotsNext
      simpa only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
    · intro child rest childPairs restPairs hchild hrest ihChild ihRest data beforeSlots acc hslots
      rw [lengthEntries.eq_def]
      have hbound : beforeSlots.length + 1 ≤ beforeSlots.length + (some (.trie child) :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [ite_eq_left hbound, collectionVectorGetRun heap data beforeSlots rest (.trie child) hslots]
      dsimp only
      rw [ihChild]
      change lengthEntries heapVectorOps data (beforeSlots.length + (some (.trie child) :: rest).length)
        (beforeSlots.length + 1 + 1)
        (JuliaLean.base.int.add (JInt.lit .i64 acc) (JInt.lit .i64 childPairs.length)) heap = _
      rw [collectionAddNat acc childPairs.length]
      have hslotsNext : heap.vectors[data]? = some ((beforeSlots ++ [some (.trie child)]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using hslots
      have hnext := ihRest data (beforeSlots ++ [some (.trie child)]) (acc + childPairs.length) hslotsNext
      simpa only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
  exact hrec

theorem collectionIsLevelRun (heap : HamtHeap K V) (root : Nat) (node : HAMTNode K V)
    (hnode : heap.nodes[root]? = some node) :
    runHamt (islevel_empty root) heap = (.ok (node.bitmap == 0), heap) := by
  have hbitmap : runHamt (nodeBitmap root) heap = (.ok node.bitmap, heap) := by
    unfold nodeBitmap
    rw [collectionRunBind, collectionReadNodeRun heap root node hnode]
    rfl
  unfold islevel_empty
  rw [collectionRunBind, hbitmap]
  rfl

/-- A finite heap tree is empty exactly when its structural leaf list is empty. -/
theorem collectionTreeIsEmpty (heap : HamtHeap K V) {root : Nat} {pairs : List (K × V)}
    (hrep : TrieRep heap root pairs) :
    isemptyHAMT heapVectorOps root heap = some (.ok pairs.isEmpty, heap) := by
  let nodeMotive : (root : Nat) → (pairs : List (K × V)) → TrieRep heap root pairs → Prop :=
    fun root pairs _ =>
      isemptyHAMT heapVectorOps root heap = some (.ok pairs.isEmpty, heap)
  let entriesMotive : (slots : List (Option (JuliaLean.base.hamt.Entry K V))) →
      (pairs : List (K × V)) → EntriesRep heap slots pairs → Prop :=
    fun slots pairs _ => ∀ (data : Nat)
      (beforeSlots : List (Option (JuliaLean.base.hamt.Entry K V))),
      heap.vectors[data]? = some (beforeSlots ++ slots) →
      isemptyEntries heapVectorOps data (beforeSlots.length + slots.length) (beforeSlots.length + 1)
        true heap = some (.ok pairs.isEmpty, heap)
  have hrec : nodeMotive root pairs hrep := by
    refine TrieRep.rec (motive_1 := nodeMotive) (motive_2 := entriesMotive)
      ?_ ?_ ?_ ?_ hrep
    · intro root node slots pairs hnode hslots _ hcount hentries ihEntries
      dsimp only [nodeMotive]
      dsimp only [entriesMotive] at ihEntries
      rw [isemptyHAMT.eq_def, collectionIsLevelRun heap root node hnode]
      by_cases hz : node.bitmap = 0
      · have hlen : slots.length = 0 := by
          rw [← hcount, hz]
          decide
        have hnil : slots = [] := List.length_eq_zero_iff.mp hlen
        subst slots
        cases hentries
        simp only [hz, beq_self_eq_true] <;> rfl
      · have hfalse : (node.bitmap == 0) = false := beq_eq_false_iff_ne.mpr hz
        rw [hfalse]
        dsimp only
        rw [collectionReadNodeRun heap root node hnode]
        dsimp only
        rw [collectionVectorLengthRun heap node.data slots hslots]
        simpa only [List.length_nil, Nat.zero_add] using ihEntries node.data [] hslots
    · intro data beforeSlots hslots
      rw [isemptyEntries.eq_def]
      have hbound : ¬ beforeSlots.length + 1 ≤ beforeSlots.length := by omega
      simp only [List.length_nil, Nat.add_zero, hbound, decide_false, Bool.false_and, Bool.false_eq_true, ite_false] <;> rfl
    · intro leaf rest pairs hrest ihRest data beforeSlots hslots
      rw [isemptyEntries.eq_def]
      have hbound : beforeSlots.length + 1 ≤ beforeSlots.length + (some (.leaf leaf) :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [ite_eq_left (by simp only [hbound, decide_true, Bool.true_and])]
      rw [collectionVectorGetRun heap data beforeSlots rest (.leaf leaf) hslots]
      change isemptyEntries heapVectorOps data _ _ false heap = some (.ok false, heap)
      rw [isemptyEntries.eq_def]
      simp only [Bool.and_false, Bool.false_eq_true, ite_false]
    · intro child rest childPairs restPairs hchild hrest ihChild ihRest data beforeSlots hslots
      rw [isemptyEntries.eq_def]
      have hbound : beforeSlots.length + 1 ≤ beforeSlots.length + (some (.trie child) :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [ite_eq_left (by simp only [hbound, decide_true, Bool.true_and])]
      rw [collectionVectorGetRun heap data beforeSlots rest (.trie child) hslots]
      dsimp only
      rw [ihChild]
      change isemptyEntries heapVectorOps data (beforeSlots.length + (some (.trie child) :: rest).length)
        (beforeSlots.length + 1 + 1) childPairs.isEmpty heap = _
      have hemptyAppend : (childPairs ++ restPairs).isEmpty =
          (childPairs.isEmpty && restPairs.isEmpty) := by cases childPairs <;> rfl
      cases hempty : childPairs.isEmpty with
      | false =>
        rw [isemptyEntries.eq_def]
        simp only [Bool.and_false, Bool.false_eq_true, ite_false,
          hemptyAppend, hempty, Bool.false_and]
      | true =>
        have hslotsNext : heap.vectors[data]? = some ((beforeSlots ++ [some (.trie child)]) ++ rest) := by
          simpa only [List.append_assoc, List.singleton_append] using hslots
        have hnext := ihRest data (beforeSlots ++ [some (.trie child)]) hslotsNext
        simpa only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          hemptyAppend, hempty, Bool.true_and] using hnext
  exact hrec

/-- The unvisited suffix of each iterator frame and its independent leaf list. -/
inductive CollectionFramesRep (heap : HamtHeap K V) :
    List (Nat × Nat) → List (K × V) → Prop where
  | nil : CollectionFramesRep heap [] []
  | frame {data : Nat} {beforeSlots slots : List (Option (JuliaLean.base.hamt.Entry K V))}
      {pairs : List (K × V)} {parents : List (Nat × Nat)} {parentPairs : List (K × V)}
      (hslots : heap.vectors[data]? = some (beforeSlots ++ slots))
      (hentries : EntriesRep heap slots pairs)
      (hparents : CollectionFramesRep heap parents parentPairs) :
      CollectionFramesRep heap ((data, beforeSlots.length + 1) :: parents) (pairs ++ parentPairs)

def CollectionScanResult (heap : HamtHeap K V) (pairs : List (K × V))
    (final : CollectionIterState K V) : Prop :=
  (pairs = [] ∧ final = ([], none)) ∨
    ∃ (pair : K × V) (rest : List (K × V)) (frames : List (Nat × Nat)),
      pairs = pair :: rest ∧ final = (frames, some (pair, ⟨frames⟩)) ∧
      CollectionFramesRep heap frames rest

def collectionScan (frames : List (Nat × Nat)) : HamtM K V (CollectionIterState K V) :=
  Lean.Loop.forIn (m := HamtM K V) ({} : Lean.Loop) (frames, none) collectionIterStep

def CollectionScanOK (heap : HamtHeap K V) (frames : List (Nat × Nat))
    (pairs : List (K × V)) : Prop :=
  ∃ final, runHamt (collectionScan frames) heap = (.ok final, heap) ∧
    CollectionScanResult heap pairs final

theorem collectionScanNil (heap : HamtHeap K V) : CollectionScanOK heap [] [] := by
  refine ⟨([], none), ?_, Or.inl ⟨rfl, rfl⟩⟩
  unfold collectionScan
  rw [collectionLoopEquation]
  rfl

theorem collectionScanYield (heap : HamtHeap K V) (frames nextFrames : List (Nat × Nat))
    (pairs : List (K × V))
    (hstep : runHamt (collectionIterStep () (frames, none)) heap =
      (.ok (.yield (nextFrames, none)), heap))
    (hnext : CollectionScanOK heap nextFrames pairs) : CollectionScanOK heap frames pairs := by
  obtain ⟨final, hrun, hresult⟩ := hnext
  refine ⟨final, ?_, hresult⟩
  unfold collectionScan at hrun ⊢
  rw [collectionLoopEquation, hstep]
  exact hrun

theorem collectionScanLeaf (heap : HamtHeap K V) (frames nextFrames : List (Nat × Nat))
    (pair : K × V) (rest : List (K × V))
    (hstep : runHamt (collectionIterStep () (frames, none)) heap =
      (.ok (.yield (nextFrames, some (pair, ⟨nextFrames⟩))), heap))
    (hrest : CollectionFramesRep heap nextFrames rest) :
    CollectionScanOK heap frames (pair :: rest) := by
  refine ⟨(nextFrames, some (pair, ⟨nextFrames⟩)), ?_,
    Or.inr ⟨pair, rest, nextFrames, rfl, rfl, hrest⟩⟩
  unfold collectionScan
  rw [collectionLoopEquation, hstep]
  dsimp only
  rw [collectionLoopEquation]
  rfl

theorem collectionStepDrop (heap : HamtHeap K V) (data : Nat)
    (beforeSlots : List (Option (JuliaLean.base.hamt.Entry K V)))
    (parents : List (Nat × Nat)) (hslots : heap.vectors[data]? = some beforeSlots) :
    runHamt (collectionIterStep () ((data, beforeSlots.length + 1) :: parents, none)) heap =
      (.ok (.yield (parents, none)), heap) := by
  unfold collectionIterStep
  simp only [Option.isNone, List.isEmpty, Bool.not_false, Bool.true_and, ite_true]
  rw [collectionRunBind, collectionVectorLengthRun heap data beforeSlots hslots]
  have hbound : beforeSlots.length + 1 > beforeSlots.length := by omega
  simp only [hbound, ite_true] <;> rfl

theorem collectionStepLeaf (heap : HamtHeap K V) (data : Nat)
    (beforeSlots rest : List (Option (JuliaLean.base.hamt.Entry K V))) (leaf : Leaf K V)
    (parents : List (Nat × Nat))
    (hslots : heap.vectors[data]? = some (beforeSlots ++ some (.leaf leaf) :: rest)) :
    runHamt (collectionIterStep () ((data, beforeSlots.length + 1) :: parents, none)) heap =
      (.ok (.yield ((data, beforeSlots.length + 1 + 1) :: parents,
        some ((leaf.key, leaf.val), ⟨(data, beforeSlots.length + 1 + 1) :: parents⟩))), heap) := by
  unfold collectionIterStep
  simp only [Option.isNone, List.isEmpty, Bool.not_false, Bool.true_and, ite_true]
  rw [collectionRunBind,
    collectionVectorLengthRun heap data (beforeSlots ++ some (.leaf leaf) :: rest) hslots]
  have hbound : ¬ beforeSlots.length + 1 > (beforeSlots ++ some (.leaf leaf) :: rest).length := by
    simp only [List.length_append, List.length_cons]
    omega
  simp only [hbound, ite_false]
  rw [collectionRunBind, collectionVectorGetRun heap data beforeSlots rest (.leaf leaf) hslots]
  rfl

theorem collectionStepChild (heap : HamtHeap K V) (data : Nat)
    (beforeSlots rest : List (Option (JuliaLean.base.hamt.Entry K V))) (child : Nat)
    (childNode : HAMTNode K V) (parents : List (Nat × Nat))
    (hslots : heap.vectors[data]? = some (beforeSlots ++ some (.trie child) :: rest))
    (hchild : heap.nodes[child]? = some childNode) :
    runHamt (collectionIterStep () ((data, beforeSlots.length + 1) :: parents, none)) heap =
      (.ok (.yield ((childNode.data, 1) :: (data, beforeSlots.length + 1 + 1) :: parents, none)), heap) := by
  unfold collectionIterStep
  simp only [Option.isNone, List.isEmpty, Bool.not_false, Bool.true_and, ite_true]
  rw [collectionRunBind,
    collectionVectorLengthRun heap data (beforeSlots ++ some (.trie child) :: rest) hslots]
  have hbound : ¬ beforeSlots.length + 1 > (beforeSlots ++ some (.trie child) :: rest).length := by
    simp only [List.length_append, List.length_cons]
    omega
  simp only [hbound, ite_false]
  rw [collectionRunBind, collectionVectorGetRun heap data beforeSlots rest (.trie child) hslots]
  dsimp only
  have hdata : runHamt (nodeData child) heap = (.ok childNode.data, heap) := by
    unfold nodeData
    rw [collectionRunBind, collectionReadNodeRun heap child childNode hchild]
    rfl
  rw [collectionRunBind, hdata]
  rfl

/-- Scanning finite subtree entries terminates at their next leaf or continuation. -/
theorem collectionEntriesScan (heap : HamtHeap K V)
    {slots : List (Option (JuliaLean.base.hamt.Entry K V))} {pairs : List (K × V)}
    (hrep : EntriesRep heap slots pairs) :
    ∀ (data : Nat) (beforeSlots : List (Option (JuliaLean.base.hamt.Entry K V))),
      heap.vectors[data]? = some (beforeSlots ++ slots) →
      ∀ (parents : List (Nat × Nat)) (parentPairs : List (K × V)),
        CollectionFramesRep heap parents parentPairs → CollectionScanOK heap parents parentPairs →
        CollectionScanOK heap ((data, beforeSlots.length + 1) :: parents) (pairs ++ parentPairs) := by
  let nodeMotive : (root : Nat) → (pairs : List (K × V)) → TrieRep heap root pairs → Prop :=
    fun root pairs _ => ∀ (node : HAMTNode K V), heap.nodes[root]? = some node →
      ∀ (parents : List (Nat × Nat)) (parentPairs : List (K × V)),
        CollectionFramesRep heap parents parentPairs → CollectionScanOK heap parents parentPairs →
        CollectionScanOK heap ((node.data, 1) :: parents) (pairs ++ parentPairs)
  let entriesMotive : (slots : List (Option (JuliaLean.base.hamt.Entry K V))) →
      (pairs : List (K × V)) → EntriesRep heap slots pairs → Prop :=
    fun slots pairs _ => ∀ (data : Nat)
      (beforeSlots : List (Option (JuliaLean.base.hamt.Entry K V))),
      heap.vectors[data]? = some (beforeSlots ++ slots) →
      ∀ (parents : List (Nat × Nat)) (parentPairs : List (K × V)),
        CollectionFramesRep heap parents parentPairs → CollectionScanOK heap parents parentPairs →
        CollectionScanOK heap ((data, beforeSlots.length + 1) :: parents) (pairs ++ parentPairs)
  have hrec : entriesMotive slots pairs hrep := by
    refine EntriesRep.rec (motive_1 := nodeMotive) (motive_2 := entriesMotive)
      ?_ ?_ ?_ ?_ hrep
    · intro root node slots pairs hnode hslots _ _ hentries ihEntries node' hnode' parents parentPairs
        hparents hscan
      have heq : node = node' := Option.some.inj (hnode.symm.trans hnode')
      subst node'
      simpa only [List.length_nil, Nat.zero_add] using
        ihEntries node.data [] hslots parents parentPairs hparents hscan
    · intro data beforeSlots hslots parents parentPairs hparents hscan
      simpa only [List.nil_append] using collectionScanYield heap
        ((data, beforeSlots.length + 1) :: parents) parents parentPairs
        (collectionStepDrop heap data beforeSlots parents (by simpa only [List.append_nil] using hslots)) hscan
    · intro leaf rest pairs hrest ihRest data beforeSlots hslots parents parentPairs hparents hscan
      have hslotsNext : heap.vectors[data]? = some ((beforeSlots ++ [some (.leaf leaf)]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using hslots
      have hframesNext : CollectionFramesRep heap
          ((data, beforeSlots.length + 1 + 1) :: parents) (pairs ++ parentPairs) := by
        simpa only [List.length_append, List.length_singleton] using
          (CollectionFramesRep.frame hslotsNext hrest hparents)
      exact collectionScanLeaf heap ((data, beforeSlots.length + 1) :: parents)
        ((data, beforeSlots.length + 1 + 1) :: parents) (leaf.key, leaf.val) (pairs ++ parentPairs)
        (collectionStepLeaf heap data beforeSlots rest leaf parents hslots) hframesNext
    · intro child rest childPairs restPairs hchild hrest ihChild ihRest data beforeSlots hslots parents parentPairs
        hparents hscan
      have hslotsNext : heap.vectors[data]? = some ((beforeSlots ++ [some (.trie child)]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using hslots
      have hframesNext : CollectionFramesRep heap
          ((data, beforeSlots.length + 1 + 1) :: parents) (restPairs ++ parentPairs) := by
        simpa only [List.length_append, List.length_singleton] using
          (CollectionFramesRep.frame hslotsNext hrest hparents)
      have hscanNext : CollectionScanOK heap ((data, beforeSlots.length + 1 + 1) :: parents)
          (restPairs ++ parentPairs) := by
        have hn := ihRest data (beforeSlots ++ [some (.trie child)]) hslotsNext parents parentPairs hparents hscan
        change CollectionScanOK heap ((data, (beforeSlots ++ [some (JuliaLean.base.hamt.Entry.trie (K := K) (V := V) child)]).length + 1) :: parents)
          (restPairs ++ parentPairs) at hn
        simpa only [List.length_append, List.length_singleton] using hn
      obtain ⟨childNode, hchildNode⟩ : ∃ node, heap.nodes[child]? = some node := by
        cases hchild with
        | node hnode _ _ _ _ => exact ⟨_, hnode⟩
      have hscanChild := ihChild childNode hchildNode
        ((data, beforeSlots.length + 1 + 1) :: parents) (restPairs ++ parentPairs) hframesNext hscanNext
      apply collectionScanYield heap ((data, beforeSlots.length + 1) :: parents)
        ((childNode.data, 1) :: (data, beforeSlots.length + 1 + 1) :: parents)
        ((childPairs ++ restPairs) ++ parentPairs)
        (collectionStepChild heap data beforeSlots rest child childNode parents hslots hchildNode)
      simpa only [List.append_assoc] using hscanChild
  exact hrec

theorem collectionTreeScan (heap : HamtHeap K V) {root : Nat} {pairs : List (K × V)}
    (hrep : TrieRep heap root pairs) (node : HAMTNode K V)
    (hnode : heap.nodes[root]? = some node) (parents : List (Nat × Nat))
    (parentPairs : List (K × V)) (hparents : CollectionFramesRep heap parents parentPairs)
    (hscan : CollectionScanOK heap parents parentPairs) :
    CollectionScanOK heap ((node.data, 1) :: parents) (pairs ++ parentPairs) := by
  cases hrep with
  | node hn hs _ _ he =>
    have heq := Option.some.inj (hn.symm.trans hnode)
    subst node
    simpa only [List.length_nil, Nat.zero_add] using
      collectionEntriesScan heap he _ [] hs parents parentPairs hparents hscan

theorem collectionFramesScan (heap : HamtHeap K V)
    {frames : List (Nat × Nat)} {pairs : List (K × V)}
    (hrep : CollectionFramesRep heap frames pairs) : CollectionScanOK heap frames pairs := by
  induction hrep with
  | nil => exact collectionScanNil heap
  | @frame data beforeSlots slots pairs parents parentPairs hslots hentries hparents ih =>
    exact collectionEntriesScan heap hentries data beforeSlots hslots parents parentPairs hparents ih

def CollectionIterationResult (heap : HamtHeap K V) (pairs : List (K × V))
    (result : Option ((K × V) × IterState K V)) : Prop :=
  (result = none ∧ pairs = []) ∨
    ∃ (pair : K × V) (rest : List (K × V)) (state : IterState K V),
      result = some (pair, state) ∧ pairs = pair :: rest ∧
      CollectionFramesRep heap state.frames rest

theorem collectionNodeDataRun (heap : HamtHeap K V) (root : Nat) (node : HAMTNode K V)
    (hnode : heap.nodes[root]? = some node) :
    runHamt (nodeData root) heap = (.ok node.data, heap) := by
  unfold nodeData
  rw [collectionRunBind, collectionReadNodeRun heap root node hnode]
  rfl

/-- Every valid continuation yields the next structural leaf or terminates. -/
theorem collectionIterateState (heap : HamtHeap K V) (root : Nat) (node : HAMTNode K V)
    (hnode : heap.nodes[root]? = some node) {frames : List (Nat × Nat)} {pairs : List (K × V)}
    (hframes : CollectionFramesRep heap frames pairs) :
    ∃ result, runHamt (iterate heapVectorOps root (some ⟨frames⟩)) heap = (.ok result, heap) ∧
      CollectionIterationResult heap pairs result := by
  obtain ⟨final, hscan, hresult⟩ := collectionFramesScan heap hframes
  refine ⟨final.2, ?_, ?_⟩
  · change runHamt (do
      let _ ← nodeData root
      let final ← collectionScan frames
      pure final.2) heap = _
    rw [collectionRunBind, collectionNodeDataRun heap root node hnode]
    dsimp only
    rw [collectionRunBind, hscan]
    rfl
  · rcases hresult with ⟨hpairs, hfinal⟩ | ⟨pair, rest, frames', hpairs, hfinal, hrest⟩
    · rw [hfinal]
      exact Or.inl ⟨rfl, hpairs⟩
    · rw [hfinal]
      exact Or.inr ⟨pair, rest, ⟨frames'⟩, rfl, hpairs, hrest⟩

theorem collectionInitialFrames (heap : HamtHeap K V) {root : Nat} {pairs : List (K × V)}
    (hrep : TrieRep heap root pairs) (node : HAMTNode K V)
    (hnode : heap.nodes[root]? = some node) :
    CollectionFramesRep heap [(node.data, 1)] pairs := by
  cases hrep with
  | node hn hs _ _ he =>
    have heq := Option.some.inj (hn.symm.trans hnode)
    subst node
    have hframes := CollectionFramesRep.frame (beforeSlots := []) hs he (CollectionFramesRep.nil (heap := heap))
    simpa only [List.length_nil, Nat.zero_add, List.append_nil] using hframes

/-- Initial iteration is safe and follows the independently specified tree order. -/
theorem collectionIterateInitial (heap : HamtHeap K V) {root : Nat} {pairs : List (K × V)}
    (hrep : TrieRep heap root pairs) :
    ∃ result, runHamt (iterate heapVectorOps root none) heap = (.ok result, heap) ∧
      CollectionIterationResult heap pairs result := by
  obtain ⟨node, hnode⟩ : ∃ node, heap.nodes[root]? = some node := by
    cases hrep with
    | node hn _ _ _ _ => exact ⟨_, hn⟩
  obtain ⟨result, hrun, hresult⟩ :=
    collectionIterateState heap root node hnode (collectionInitialFrames heap hrep node hnode)
  refine ⟨result, ?_, hresult⟩
  have heq : runHamt (iterate heapVectorOps root none) heap =
      runHamt (iterate heapVectorOps root (some ⟨[(node.data, 1)]⟩)) heap := by
    change runHamt (do
      let data ← nodeData root
      let final ← collectionScan [(data, 1)]
      pure final.2) heap = runHamt (do
      let _ ← nodeData root
      let final ← collectionScan [(node.data, 1)]
      pure final.2) heap
    rw [collectionRunBind, collectionNodeDataRun heap root node hnode]
    rw [collectionRunBind, collectionNodeDataRun heap root node hnode]
  exact heq.trans hrun

def collectionTreeDict (heap : HamtHeap K V) (root : Nat) :
    PersistentDict K V (round2.PTrie K V) := ⟨.ok (heap, root)⟩

theorem collectionOpsIterateOfRun (same : K → K → Bool) (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root : Nat) (state : Option (IterState K V))
    (result : Option ((K × V) × IterState K V))
    (hrun : runHamt (iterate heapVectorOps root state) heap = (.ok result, heap)) :
    persistentIterate (round2.hamtOps same runtime) (collectionTreeDict heap root) state = result := by
  unfold persistentIterate round2.hamtOps round2.runTrie collectionTreeDict
  dsimp only
  rw [hrun]

/-- Enough calls to a valid continuation visit each remaining leaf exactly once. -/
theorem collectionCollectState (same : K → K → Bool) (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) (root : Nat) (node : HAMTNode K V)
    (hnode : heap.nodes[root]? = some node) {frames : List (Nat × Nat)} {pairs : List (K × V)}
    (hframes : CollectionFramesRep heap frames pairs) (fuel : Nat) (hlen : pairs.length < fuel) :
    persistentCollectFuel (round2.hamtOps same runtime) (collectionTreeDict heap root)
      fuel (some ⟨frames⟩) = pairs := by
  induction fuel generalizing frames pairs with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨result, hrun, hresult⟩ := collectionIterateState heap root node hnode hframes
    unfold persistentCollectFuel
    rw [collectionOpsIterateOfRun same runtime heap root (some ⟨frames⟩) result hrun]
    rcases hresult with ⟨hresult, hpairs⟩ | ⟨pair, rest, state, hresult, hpairs, hrest⟩
    · rw [hresult, hpairs]
    · rw [hresult, hpairs]
      dsimp only
      have hrestlen : rest.length < fuel := by
        rw [hpairs, List.length_cons] at hlen
        omega
      exact congrArg (List.cons pair) (ih hrest hrestlen)

/-- Independent finite-tree traversal agrees exactly with the frozen public collector. -/
theorem collectionTreeCollect (same : K → K → Bool) (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) {root : Nat} {pairs : List (K × V)}
    (hrep : TrieRep heap root pairs) :
    persistentCollectFuel (round2.hamtOps same runtime) (collectionTreeDict heap root)
      (pairs.length + 1) none = pairs := by
  obtain ⟨node, hnode⟩ : ∃ node, heap.nodes[root]? = some node := by
    cases hrep with
    | node hn _ _ _ _ => exact ⟨_, hn⟩
  obtain ⟨result, hrun, hresult⟩ := collectionIterateInitial heap hrep
  unfold persistentCollectFuel
  rw [collectionOpsIterateOfRun same runtime heap root none result hrun]
  rcases hresult with ⟨hresult, hpairs⟩ | ⟨pair, rest, state, hresult, hpairs, hrest⟩
  · rw [hresult, hpairs]
  · rw [hresult, hpairs]
    dsimp only
    exact congrArg (List.cons pair)
      (collectionCollectState same runtime heap root node hnode hrest (rest.length + 1)
        (Nat.lt_succ_self _))

theorem collectionTreeNativeLength (same : K → K → Bool) (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) {root : Nat} {pairs : List (K × V)}
    (hrep : TrieRep heap root pairs) :
    persistentLength (round2.hamtOps same runtime) (collectionTreeDict heap root) =
      some (.ok (JInt.lit .i64 pairs.length)) := by
  unfold persistentLength round2.hamtOps round2.runPartialTrie runPartialHamt collectionTreeDict
  dsimp only
  rw [collectionTreeLength heap hrep]
  rfl

theorem collectionTreeEmptyTest (same : K → K → Bool) (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) {root : Nat} {pairs : List (K × V)}
    (hrep : TrieRep heap root pairs) :
    persistentIsEmpty (round2.hamtOps same runtime) (collectionTreeDict heap root) =
      some (.ok pairs.isEmpty) := by
  unfold persistentIsEmpty round2.hamtOps round2.runPartialTrie runPartialHamt collectionTreeDict
  dsimp only
  rw [collectionTreeIsEmpty heap hrep]
  rfl


/-- A permutation of the structural leaves is enough for all three collection observations. -/
theorem collectionTreeCoreOfPerm (same : K → K → Bool) (runtime : HamtObjectIdRuntime K)
    (heap : HamtHeap K V) {root : Nat} {pairs modelPairs : List (K × V)}
    (hrep : TrieRep heap root pairs) (hperm : pairs.Perm modelPairs) :
    List.Perm (persistentCollectFuel (round2.hamtOps same runtime) (collectionTreeDict heap root)
      (modelPairs.length + 1) none) modelPairs ∧
    persistentLength (round2.hamtOps same runtime) (collectionTreeDict heap root) =
      some (.ok (JInt.lit .i64 modelPairs.length)) ∧
    persistentIsEmpty (round2.hamtOps same runtime) (collectionTreeDict heap root) =
      some (.ok modelPairs.isEmpty) := by
  have hlength := hperm.length_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [← hlength, collectionTreeCollect same runtime heap hrep]
    exact hperm
  · rw [collectionTreeNativeLength same runtime heap hrep, hlength]
  · rw [collectionTreeEmptyTest same runtime heap hrep, hperm.isEmpty_eq]

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: CollectionUniquenessWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1
open JuliaLean JuliaLean.base.hamt

variable {K V : Type}

/-- The stored vector and its finite child trees uniquely determine the flattened pair list. -/
theorem collectionEntriesRepUnique (heap : HamtHeap K V)
    {slots : List (Option (JuliaLean.base.hamt.Entry K V))} {pairs otherPairs : List (K × V)}
    (hrep : EntriesRep heap slots pairs) (hother : EntriesRep heap slots otherPairs) :
    pairs = otherPairs := by
  let nodeMotive : (root : Nat) → (pairs : List (K × V)) → TrieRep heap root pairs → Prop :=
    fun root pairs _ => ∀ otherPairs, TrieRep heap root otherPairs → pairs = otherPairs
  let entriesMotive : (slots : List (Option (JuliaLean.base.hamt.Entry K V))) →
      (pairs : List (K × V)) → EntriesRep heap slots pairs → Prop :=
    fun slots pairs _ => ∀ otherPairs, EntriesRep heap slots otherPairs → pairs = otherPairs
  have hrec : entriesMotive slots pairs hrep := by
    refine EntriesRep.rec (motive_1 := nodeMotive) (motive_2 := entriesMotive)
      ?_ ?_ ?_ ?_ hrep
    · intro root node slots pairs hnode hslots _ _ hentries ihEntries otherPairs hother
      cases hother with
      | node hnode' hslots' _ _ hentries' =>
        have hnodes := Option.some.inj (hnode.symm.trans hnode')
        cases hnodes
        have hvecs := Option.some.inj (hslots.symm.trans hslots')
        cases hvecs
        exact ihEntries _ hentries'
    · intro otherPairs hother
      cases hother
      rfl
    · intro leaf rest pairs hrest ihRest otherPairs hother
      cases hother with
      | leaf hrest' => exact congrArg (List.cons (leaf.key, leaf.val)) (ihRest _ hrest')
    · intro child rest childPairs restPairs hchild hrest ihChild ihRest otherPairs hother
      cases hother with
      | trie hchild' hrest' => rw [ihChild _ hchild', ihRest _ hrest']
  exact hrec otherPairs hother

/-- A finite tree rooted at one concrete node has only one structural traversal list. -/
theorem collectionTrieRepUnique (heap : HamtHeap K V)
    {root : Nat} {pairs otherPairs : List (K × V)}
    (hrep : TrieRep heap root pairs) (hother : TrieRep heap root otherPairs) :
    pairs = otherPairs := by
  cases hrep with
  | node hnode hslots _ _ hentries =>
    cases hother with
    | node hnode' hslots' _ _ hentries' =>
      have hnodes := Option.some.inj (hnode.symm.trans hnode')
      cases hnodes
      have hvecs := Option.some.inj (hslots.symm.trans hslots')
      cases hvecs
      exact collectionEntriesRepUnique heap hentries hentries'

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: ReachabilityWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- A public persistent dictionary has an independently described finite heap
whose structural leaf sequence is a permutation of its reference map. -/
def PersistentTreeRep {K V : Type}
    (dict : PersistentDict K V (round2.PTrie K V)) (reference : List (K × V)) : Prop :=
  ∃ (heap : HamtHeap K V) (root : Nat) (pairs : List (K × V)),
    dict.trie = .ok (heap, root) ∧ TrieRep heap root pairs ∧ List.Perm pairs reference

theorem persistentTreeRep_empty {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) :
    PersistentTreeRep (persistentEmpty (round2.hamtOps (V := V) same runtime)) [] := by
  refine ⟨persistentEmptyHeap K V, 0, [], persistentEmptyTrie same runtime,
    ?_, List.Perm.refl []⟩
  exact .node (node := ⟨0, 0⟩) (slots := []) rfl rfl (Nat.two_pow_pos 32) (pathCountOnesZero 32) .nil

theorem persistentTreeRep_singleton {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V)
    (dict : PersistentDict K V (round2.PTrie K V))
    (hc : persistentSingleton (round2.hamtOps same runtime) key value = .ok dict) :
    PersistentTreeRep dict [(key, value)] := by
  have he : singletonDict runtime key value = dict :=
    Except.ok.inj ((singletonConstructor same runtime key value).symm.trans hc)
  rw [← he]
  exact ⟨singletonHeap runtime key value, 0, [(key, value)], rfl,
    singletonTrieRep runtime key value, List.Perm.refl _⟩

/-- The exact remaining transition obligation for the structural reachability
bridge. It concerns the existing successful-set and delete operations. -/
structure PersistentTreeTransitions {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) : Prop where
  set : ∀ (dict next : PersistentDict K V (round2.PTrie K V)) (m : List (K × V))
    (key : K) (value : V),
    round2.PRep (round2.hamtOps same runtime) same dict m →
    PersistentTreeRep dict m →
    persistentSetTyped (round2.hamtOps same runtime) dict key value = some (.ok next) →
    PersistentTreeRep next (rset same m key value)
  delete : ∀ (dict : PersistentDict K V (round2.PTrie K V)) (m : List (K × V)) (key : K),
    round2.PRep (round2.hamtOps same runtime) same dict m →
    PersistentTreeRep dict m →
    PersistentTreeRep (persistentDelete (round2.hamtOps same runtime) dict key) (rdel same m key)

/-- Empty and singleton constructors are closed; the two transition clauses
are sufficient to finish structural reachability for every API history. -/
theorem persistentTreeRep_of_transitions {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (ht : PersistentTreeTransitions (V := V) same runtime)
    {dict : PersistentDict K V (round2.PTrie K V)} {m : List (K × V)}
    (hr : round2.PRep (round2.hamtOps same runtime) same dict m) :
    PersistentTreeRep dict m := by
  induction hr with
  | empty => exact persistentTreeRep_empty same runtime
  | singleton hc => exact persistentTreeRep_singleton same runtime _ _ _ hc
  | set hr hs ih => exact ht.set _ _ _ _ _ hr ih hs
  | delete hr ih => exact ht.delete _ _ _ hr ih

/-- All of the frozen path-safety conclusion is now available from the
structural reachability bridge; uniqueness already follows from API history. -/
theorem persistentPathSafe_of_treeRep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    {dict : PersistentDict K V (round2.PTrie K V)} {m : List (K × V)}
    (hr : round2.PRep (round2.hamtOps same runtime) same dict m)
    (ht : PersistentTreeRep dict m) (key : K) :
    ∃ (pr : PathResult K V) (heap : HamtHeap K V),
      round2.runTrie dict.trie (fun root =>
        path heapVectorOps same runtime root (HashState.fromKey runtime key) false) =
        .ok (pr, heap) ∧
      ((pr.found && pr.present) = true →
        ∃ leaf : Leaf K V,
          round2.runTrie (.ok (heap, pr.trie)) (fun t => do
            let node ← readNode t
            heapVectorOps.get node.data pr.index) = .ok (.leaf leaf, heap) ∧
          same leaf.key key = true ∧ rlookup same m key = some leaf.val) := by
  obtain ⟨heap, root, pairs, hd, hs, hp⟩ := ht
  rw [hd]
  exact persistentPathSafe_of_trieRep same runtime hl heap root pairs m hs
    (persistentPRepDistinct hr) hp key

/-- Complete frozen collection conclusion, with only the independent
structural representation left as an assumption. -/
theorem persistentCollection_of_treeRep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K)
    (dict : PersistentDict K V (round2.PTrie K V)) (m : List (K × V))
    (ht : PersistentTreeRep dict m) :
    List.Perm (persistentCollectFuel (round2.hamtOps same runtime) dict (m.length + 1) none) m ∧
    persistentLength (round2.hamtOps same runtime) dict =
      some (.ok (JInt.lit .i64 (Int.ofNat m.length))) ∧
    persistentIsEmpty (round2.hamtOps same runtime) dict = some (.ok m.isEmpty) ∧
    (∀ q : K, persistentKeyGet (round2.hamtOps same runtime)
      (persistentEmptyLike (round2.hamtOps same runtime) dict) q = none) ∧
    persistentLength (round2.hamtOps same runtime)
      (persistentEmptyLike (round2.hamtOps same runtime) dict) = some (.ok (JInt.lit .i64 0)) ∧
    persistentOnly (round2.hamtOps same runtime) dict = some
      (if (JInt.lit .i64 (Int.ofNat m.length)).val = 1 then
        match (persistentCollectFuel (round2.hamtOps same runtime) dict (m.length + 1) none).head? with
        | some e => .ok e
        | none => .error (.inr (.argumentError "PersistentDict must be non-empty"))
      else .error (.inr (.argumentError "Collection must contain exactly 1 element"))) := by
  obtain ⟨heap, root, pairs, hd, hs, hp⟩ := ht
  have he : dict = ⟨.ok (heap, root)⟩ := by
    cases dict
    cases hd
    rfl
  subst dict
  obtain ⟨hi, hn, hb⟩ := collectionTreeCoreOfPerm same runtime heap hs hp
  exact persistentCollectionOfCore same runtime _ _ hi hn hb

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: RoutedReachabilityWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Independent finite structure, reference-map permutation, key routing, and
reference-key uniqueness, packaged for simultaneous preservation. -/
def PersistentRoutedRep {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K)
    (dict : PersistentDict K V (round2.PTrie K V)) (reference : List (K × V)) : Prop :=
  ∃ (heap : HamtHeap K V) (root : Nat) (pairs : List (K × V)),
    dict.trie = .ok (heap, root) ∧ TrieRep heap root pairs ∧ List.Perm pairs reference ∧
    StoredRouting runtime heap root pairs ∧ Distinct same reference

/-- The stronger representation retains the independently specified finite tree. -/
theorem persistentRoutedRep_tree {K V : Type} {same : K → K → Bool}
    {runtime : HamtObjectIdRuntime K} {dict : PersistentDict K V (round2.PTrie K V)}
    {reference : List (K × V)} (hr : PersistentRoutedRep same runtime dict reference) :
    PersistentTreeRep dict reference := by
  obtain ⟨heap, root, pairs, hd, ht, hp, _, _⟩ := hr
  exact ⟨heap, root, pairs, hd, ht, hp⟩

theorem persistentRoutedRep_empty {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) :
    PersistentRoutedRep same runtime
      (persistentEmpty (round2.hamtOps (V := V) same runtime)) [] := by
  refine ⟨persistentEmptyHeap K V, 0, [], persistentEmptyTrie same runtime,
    ?_, List.Perm.refl [], ?_, List.Pairwise.nil⟩
  · exact .node (node := ⟨0, 0⟩) (slots := []) rfl rfl (Nat.two_pow_pos 32) (pathCountOnesZero 32) .nil
  · intro key value hmem
    cases hmem

/-- The singleton constructor places its sole leaf at its own identity-hash slot. -/
theorem singletonStoredRouting {K V : Type} (runtime : HamtObjectIdRuntime K)
    (key : K) (value : V) :
    StoredRouting runtime (singletonHeap runtime key value) 0 [(key, value)] := by
  intro storedKey storedValue hmem
  have heq := List.mem_singleton.mp hmem
  have hk := congrArg Prod.fst heq
  have hv := congrArg Prod.snd heq
  dsimp only at hk hv
  subst storedKey
  subst storedValue
  have hslot : (BitmapIndex.fromHash (HashState.fromKey runtime key)).x =
      singletonHashSlot runtime key := by
    simp only [BitmapIndex.fromHash, HashState.fromKey, shiftRightNat, Nat.pow_zero, Nat.div_one]
    rfl
  refine .leaf (node := ⟨0, u32 (2 ^ singletonHashSlot runtime key)⟩)
    (slots := [some (.leaf ⟨key, value⟩)]) rfl rfl ?_ ?_
  · change Nat.testBit (u32 (2 ^ singletonHashSlot runtime key))
      (BitmapIndex.fromHash (HashState.fromKey runtime key)).x = true
    rw [singletonBitmap, hslot, Nat.testBit_two_pow]
    exact decide_eq_true (Eq.refl _)
  · have hi : pathReadIndex (⟨0, u32 (2 ^ singletonHashSlot runtime key)⟩ : HAMTNode K V)
        (HashState.fromKey runtime key) = 1 := by
      unfold pathReadIndex
      rw [singletonBitmap, hslot]
      simp only [shiftLeftNat, Nat.one_mul]
      exact singletonQueryIndex_same runtime key key rfl
    rw [hi]
    rfl

theorem persistentRoutedRep_singleton {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (key : K) (value : V)
    (dict : PersistentDict K V (round2.PTrie K V))
    (hc : persistentSingleton (round2.hamtOps same runtime) key value = .ok dict) :
    PersistentRoutedRep same runtime dict [(key, value)] := by
  have he : singletonDict runtime key value = dict :=
    Except.ok.inj ((singletonConstructor same runtime key value).symm.trans hc)
  rw [← he]
  exact ⟨singletonHeap runtime key value, 0, [(key, value)], rfl,
    singletonTrieRep runtime key value, List.Perm.refl _, singletonStoredRouting runtime key value,
    List.Pairwise.cons (by intro pair hmem; cases hmem) List.Pairwise.nil⟩

/-- The two remaining preservation statements for all finite routed states.
These are mathematical obligations about the frozen operations, not new operations. -/
structure PersistentRoutedTransitions {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) : Prop where
  set : ∀ (dict next : PersistentDict K V (round2.PTrie K V)) (reference : List (K × V))
      (key : K) (value : V),
    PersistentRoutedRep same runtime dict reference →
    persistentSetTyped (round2.hamtOps same runtime) dict key value = some (.ok next) →
    PersistentRoutedRep same runtime next (rset same reference key value)
  delete : ∀ (dict : PersistentDict K V (round2.PTrie K V)) (reference : List (K × V))
      (key : K),
    PersistentRoutedRep same runtime dict reference →
    PersistentRoutedRep same runtime
      (persistentDelete (round2.hamtOps same runtime) dict key) (rdel same reference key)

/-- Simultaneous preservation closes the representation for every API history;
the empty and singleton cases have no remaining obligation. -/
theorem persistentRoutedRep_of_transitions {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (ht : PersistentRoutedTransitions (V := V) same runtime)
    {dict : PersistentDict K V (round2.PTrie K V)} {reference : List (K × V)}
    (hr : round2.PRep (round2.hamtOps same runtime) same dict reference) :
    PersistentRoutedRep same runtime dict reference := by
  induction hr with
  | empty => exact persistentRoutedRep_empty same runtime
  | singleton hc => exact persistentRoutedRep_singleton same runtime _ _ _ hc
  | set _ hs ih => exact ht.set _ _ _ _ _ ih hs
  | delete _ ih => exact ht.delete _ _ _ ih

/-- The exact path-safety target follows from the same simultaneous preservation theorem. -/
theorem persistentPathSafe_of_routedTransitions
    (htrans : ∀ (K V : Type) (same : K → K → Bool) (runtime : HamtObjectIdRuntime K),
      KeyLaws runtime.objectid same → PersistentRoutedTransitions (V := V) same runtime) :
    round2.PersistentPathSafe := by
  intro K V same runtime hl dict reference hrep query
  exact persistentPathSafe_of_treeRep same runtime hl hrep
    (persistentRoutedRep_tree
      (persistentRoutedRep_of_transitions same runtime (htrans K V same runtime hl) hrep)) query

/-- The exact collection target follows from the same simultaneous preservation theorem. -/
theorem persistentCollection_of_routedTransitions
    (htrans : ∀ (K V : Type) (same : K → K → Bool) (runtime : HamtObjectIdRuntime K),
      KeyLaws runtime.objectid same → PersistentRoutedTransitions (V := V) same runtime) :
    round2.PersistentCollectionSemantics := by
  intro K V same runtime hl dict reference hrep
  exact persistentCollection_of_treeRep same runtime dict reference
    (persistentRoutedRep_tree
      (persistentRoutedRep_of_transitions same runtime (htrans K V same runtime hl) hrep))

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: FoundInsertTransitionWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- A local insertion/replacement routing proof lifts to the full independent
reference update through the preserved copied ancestor context. -/
theorem foundInsertRouteLift {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) {base before after : HamtHeap K V}
    (hb : PersistentHeapFrame base before) (ha : PersistentHeapFrame base after)
    {root focus : Nat} {outerBefore outerAfter oldPairs newPairs : List (K × V)}
    (hc : TrieContext base root focus outerBefore outerAfter)
    {key : K} {value : V} {hash : HashState K}
    (hprefix : RoutingContext runtime base root (HashState.fromKey runtime key) focus hash)
    (hnew : RoutedLeaf runtime after focus hash ⟨key, value⟩)
    (hs : StoredRouting runtime before root oldPairs)
    (hp : List.Perm newPairs (rset same oldPairs key value))
    (hfocus : ∀ pair ∈ oldPairs, same key pair.1 = false → ∀ hash,
      RoutedLeaf runtime before focus hash ⟨pair.1, pair.2⟩ →
      RoutedLeaf runtime after focus hash ⟨pair.1, pair.2⟩) :
    StoredRouting runtime after root newPairs := by
  intro storedKey storedValue hm
  have hmem := mem_rset.mp (hp.mem_iff.1 hm)
  rcases hmem with he | ⟨hold, hfalse⟩
  · have hk := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    dsimp only at hk hv
    subst storedKey
    subst storedValue
    exact copyRouting_contextFill (copyRouting_contextFrame ha hprefix) hnew
  · exact copyRouting_liftFocus hb ha hc ⟨storedKey, storedValue⟩
      (hfocus (storedKey, storedValue) hold hfalse) _ (hs storedKey storedValue hold)

/-- The found=true branches of the actual partial insertion action preserve the
complete finite routed representation and perform exactly the reference update. -/
theorem foundInsert_preservesFocus {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (reference pairs : List (K × V)) (key : K) (value : V)
    (base before : HamtHeap K V) (result : PathResult K V)
    (outerBefore focusPairs outerAfter : List (K × V))
    (hf : PersistentHeapFrame base before)
    (hc : TrieContext base result.top result.trie outerBefore outerAfter)
    (hparts : pairs = outerBefore ++ focusPairs ++ outerAfter)
    (ht : CopyPathTerminal same key base before result focusPairs)
    (hr : StoredRouting runtime before result.top pairs)
    (hpref : RoutingContext runtime base result.top (HashState.fromKey runtime key)
      result.trie result.hash)
    (hd : Distinct same reference) (hperm : List.Perm pairs reference)
    (hfound : result.found = true) :
    ∃ bitmap after,
      runPartialHamt (insert! heapVectorOps runtime result.found result.present result.trie
        result.index result.bi result.hash value) before = some (.ok (some bitmap), after) ∧
      PersistentRoutedRep same runtime
        (⟨.ok (after, result.top)⟩ : PersistentDict K V (round2.PTrie K V))
        (rset same reference key value) := by
  have htSaved := ht
  obtain ⟨node, slots, hn, hs, hb, hcount, he, hfreshN, hfreshD, hkey, hbi, hi, hbit, hslot⟩ := ht
  have hroot := (List.getElem?_eq_some_iff.mp hn).1
  have hdata := (List.getElem?_eq_some_iff.mp hs).1
  have hbitBound : result.bi.x < 32 := by rw [hbi]; exact pathBitmapIndex_lt result.hash
  have hirank : result.index - 1 = persistentBitmapRank node.bitmap result.bi.x := by
    rw [hi, localRoutingIndexRank, hbi]
  have hlo : 1 ≤ result.index := by rw [hi]; exact Nat.le_add_left 1 _
  have hdPairs : Distinct same pairs := hd.perm hl hperm.symm
  cases hpresent : result.present with
  | false =>
    have hclear : Nat.testBit node.bitmap result.bi.x = false := hbit.trans hpresent
    have hrank : persistentBitmapRank node.bitmap result.bi.x ≤ slots.length := by
      rw [← hcount]
      exact persistentCountAndLe 32 node.bitmap _
    have hhigh : result.index ≤ slots.length + 1 := by omega
    have hmissing : ∀ pair ∈ pairs, same key pair.1 = false :=
      copyFocus_missing same runtime hl hf htSaved hpref hr (by simp only [hpresent, Bool.and_false])
    obtain ⟨insideBefore, insideAfter, hinside, ha, hfocus⟩ :=
      persistentFocusInsertLeaf hf result.trie node.data node.bitmap result.bi.x
        (persistentBitmapRank node.bitmap result.bi.x) slots focusPairs ⟨key, value⟩
        hroot hdata hfreshN hfreshD hb hcount he hrank hbitBound hclear
    let bitmap := u32 (node.bitmap ||| shiftLeftNat 1 result.bi.x)
    let after : HamtHeap K V :=
      ⟨before.vectors.set node.data
          (slots.insertIdx (persistentBitmapRank node.bitmap result.bi.x) (some (.leaf ⟨key, value⟩))),
        before.nodes.set result.trie ⟨node.data, bitmap⟩⟩
    let left := outerBefore ++ insideBefore
    let right := insideAfter ++ outerAfter
    let newPairs := left ++ (key, value) :: right
    have hfull : pairs = left ++ right := by
      rw [hparts, hinside]
      simp only [left, right, List.append_assoc]
    have hnewPerm : List.Perm newPairs (rset same pairs key value) := by
      rw [hfull]
      exact persistentReferenceInsertPerm same left right key value
        (fun pair hm => hmissing pair (by simpa only [hfull] using hm))
    have htree : TrieRep after result.top newPairs := by
      have h := contextReplace ha hc hfocus
      simpa only [after, bitmap, newPairs, left, right, List.append_assoc, List.cons_append] using h
    have hnAfter : after.nodes[result.trie]? = some ⟨node.data, bitmap⟩ :=
      List.getElem?_set_self hroot
    have hsAfter : after.vectors[node.data]? = some
        (slots.insertIdx (persistentBitmapRank node.bitmap result.bi.x) (some (.leaf ⟨key, value⟩))) :=
      List.getElem?_set_self hdata
    have hnewRoute : RoutedLeaf runtime after result.trie result.hash ⟨key, value⟩ := by
      apply localRoutingInsertedLeaf runtime after result.trie node.data node.bitmap slots
        ⟨key, value⟩ result.hash hb hcount
      · simpa only [← hbi] using hclear
      · simpa only [← hbi, bitmap] using hnAfter
      · simpa only [← hbi] using hsAfter
    have hlocal := localRoutingInsertFocus runtime hf ha result.trie node node.data result.bi.x
      slots focusPairs ⟨key, value⟩ he hn hs hnAfter hsAfter hb hbitBound hclear
    have hrouting : StoredRouting runtime after result.top newPairs :=
      foundInsertRouteLift same runtime hf ha hc hpref hnewRoute hr hnewPerm
        (fun pair _ _ hash route => hlocal hash ⟨pair.1, pair.2⟩ route)
    refine ⟨bitmap, after, ?_, after, result.top, newPairs, rfl, htree,
      hnewPerm.trans (persistentReferenceSetPerm same hperm key value), hrouting,
      distinct_rset hd key value⟩
    rw [hfound]
    have hrun := updateFoundInsertRun runtime before result.trie result.index result.bi.x
      node slots result.hash value false hn hs hlo hhigh
    simpa only [Bool.false_eq_true, ite_false, hkey, hirank, bitmap, after] using hrun
  | true =>
    have hselected : Nat.testBit node.bitmap result.bi.x = true := hbit.trans hpresent
    simp only [hpresent, ite_true] at hslot
    obtain ⟨old, hget, hsame⟩ := hslot
    have hgetRank : slots[persistentBitmapRank node.bitmap result.bi.x]? = some (some (.leaf old)) := by
      simpa only [hirank] using hget
    have hrank : persistentBitmapRank node.bitmap result.bi.x < slots.length :=
      (List.getElem?_eq_some_iff.mp hgetRank).1
    have hhigh : result.index ≤ slots.length := by omega
    have hequal : same old.key key = true := hsame.symm.trans hfound
    obtain ⟨insideBefore, insideAfter, hinside, ha, hfocus⟩ :=
      persistentFocusReplaceLeaf hf result.trie node.data node.bitmap
        (persistentBitmapRank node.bitmap result.bi.x) slots focusPairs old ⟨key, value⟩
        hroot hdata hfreshN hfreshD hb hcount he hgetRank
    let after : HamtHeap K V :=
      ⟨before.vectors.set node.data
          (slots.set (persistentBitmapRank node.bitmap result.bi.x) (some (.leaf ⟨key, value⟩))),
        before.nodes.set result.trie ⟨node.data, node.bitmap⟩⟩
    let left := outerBefore ++ insideBefore
    let right := insideAfter ++ outerAfter
    let newPairs := left ++ (key, value) :: right
    have hfull : pairs = left ++ (old.key, old.val) :: right := by
      rw [hparts, hinside]
      simp only [left, right, List.append_assoc, List.cons_append]
    have hnewPerm : List.Perm newPairs (rset same pairs key value) := by
      rw [hfull]
      exact persistentReferenceReplacePerm hl left right (old.key, old.val) key value
        (by simpa only [hfull] using hdPairs) hequal
    have htree : TrieRep after result.top newPairs := by
      have h := contextReplace ha hc hfocus
      simpa only [after, newPairs, left, right, List.append_assoc, List.cons_append] using h
    have hnAfter : after.nodes[result.trie]? = some ⟨node.data, node.bitmap⟩ :=
      List.getElem?_set_self hroot
    have hsAfter : after.vectors[node.data]? = some
        (slots.set (persistentBitmapRank node.bitmap result.bi.x) (some (.leaf ⟨key, value⟩))) :=
      List.getElem?_set_self hdata
    have hnewRoute : RoutedLeaf runtime after result.trie result.hash ⟨key, value⟩ := by
      apply localRoutingReplacedLeaf runtime after result.trie node.data node.bitmap slots
        ⟨key, value⟩ result.hash
      · simpa only [← hbi] using hselected
      · simpa only [← hbi] using hrank
      · exact hnAfter
      · simpa only [← hbi] using hsAfter
    have hlocal : ∀ pair ∈ pairs, same key pair.1 = false → ∀ hash,
        RoutedLeaf runtime before result.trie hash ⟨pair.1, pair.2⟩ →
        RoutedLeaf runtime after result.trie hash ⟨pair.1, pair.2⟩ := by
      intro pair _ hfalse hash route
      have hne : (⟨pair.1, pair.2⟩ : Leaf K V) ≠ old := by
        intro heq
        have hk : pair.1 = old.key := congrArg Leaf.key heq
        rw [hk, hl.symm old.key key hequal] at hfalse
        cases hfalse
      exact localRoutingReplaceFocus runtime hf ha result.trie node node.data result.bi.x
        slots focusPairs old ⟨key, value⟩ he hn hs hnAfter hsAfter hbitBound hselected hgetRank
        hash ⟨pair.1, pair.2⟩ hne route
    have hrouting : StoredRouting runtime after result.top newPairs :=
      foundInsertRouteLift same runtime hf ha hc hpref hnewRoute hr hnewPerm hlocal
    refine ⟨node.bitmap, after, ?_, after, result.top, newPairs, rfl, htree,
      hnewPerm.trans (persistentReferenceSetPerm same hperm key value), hrouting,
      distinct_rset hd key value⟩
    rw [hfound]
    have hrun := updateFoundInsertRun runtime before result.trie result.index result.bi.x
      node slots result.hash value true hn hs hlo (by simpa only [ite_true, Nat.add_zero] using hhigh)
    have hbitmap := persistentBitmapSetExisting node.bitmap result.bi.x hb hselected
    simpa only [ite_true, hkey, hirank, hbitmap, after] using hrun

theorem foundInsertOpsPath {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (root : Nat)
    (hash : HashState K) (result : PathResult K V) (after : HamtHeap K V)
    (hrun : runHamt (path heapVectorOps same runtime root hash true) heap = (.ok result, after)) :
    (round2.hamtOps same runtime).path (.ok (heap, root)) hash true =
      ⟨result.found, result.present, .ok (after, result.trie), result.index,
        result.bi.x, .ok (after, result.top), result.hash⟩ :=
  routingOpsPathGeneral same runtime heap after root hash true result hrun

/-- The public typed-set wrapper returns the copied top in the insertion action's
updated heap, with no extra semantic assumption. -/
theorem foundInsertTypedRun {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (dict : PersistentDict K V (round2.PTrie K V))
    (heap : HamtHeap K V) (root : Nat) (key : K) (value : V)
    (result : PathResult K V) (copied after : HamtHeap K V) (inserted : Option Nat)
    (hd : dict.trie = .ok (heap, root))
    (hp : runHamt (path heapVectorOps same runtime root (HashState.fromKey runtime key) true)
      heap = (.ok result, copied))
    (hi : runPartialHamt (insert! heapVectorOps runtime result.found result.present result.trie
      result.index result.bi result.hash value) copied = some (.ok inserted, after)) :
    persistentSetTyped (round2.hamtOps same runtime) dict key value =
      some (.ok ⟨.ok (after, result.top)⟩) := by
  have hpath := foundInsertOpsPath same runtime heap root (HashState.fromKey runtime key) result copied hp
  unfold persistentSetTyped JuliaLean.base.dict.persistentInsert
  rw [hd]
  change ((round2.hamtOps same runtime).insert
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).top
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).trie
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).found
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).present
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).index
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).bitmapIndex
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).state value).map
      (Except.map PersistentDict.mk) = _
  rw [hpath]
  unfold round2.hamtOps round2.runPartialAt
  dsimp only
  rw [hi] <;> rfl

/-- Full strong-representation preservation for any successful typed insertion
whose actual copied path reports found=true. Collision-growth is a separate case. -/
theorem persistentSet_foundPreserves {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (dict next : PersistentDict K V (round2.PTrie K V)) (reference : List (K × V))
    (key : K) (value : V) (hr : PersistentRoutedRep same runtime dict reference)
    (hf : ((round2.hamtOps same runtime).path dict.trie
      (HashState.fromKey runtime key) true).found = true)
    (hs : persistentSetTyped (round2.hamtOps same runtime) dict key value = some (.ok next)) :
    PersistentRoutedRep same runtime next (rset same reference key value) := by
  obtain ⟨heap, root, pairs, hd, ht, hperm, hrouting, hdistinct⟩ := hr
  obtain ⟨result, copied, focusBase, before, focusPairs, rest,
      hpath, hbase, hfinal, hcontext, hpairs, hterminal, htop, htransport, hprefix⟩ :=
    trieRep_copyPathFocus same runtime heap ht (HashState.fromKey runtime key)
  have hpathOps := foundInsertOpsPath same runtime heap root (HashState.fromKey runtime key)
    result copied hpath
  have hfound : result.found = true := by
    rw [hd, hpathOps] at hf
    exact hf
  obtain ⟨bitmap, after, haction, hrep⟩ :=
    foundInsert_preservesFocus same runtime hl reference pairs key value focusBase copied result
      before focusPairs rest hfinal hcontext hpairs hterminal
      (copyRouting_stored htransport hrouting) hprefix hdistinct hperm hfound
  have hrun := foundInsertTypedRun same runtime dict heap root key value result copied after
    (some bitmap) hd hpath haction
  have heq : (⟨.ok (after, result.top)⟩ : PersistentDict K V (round2.PTrie K V)) = next :=
    Except.ok.inj (Option.some.inj (hrun.symm.trans hs))
  rw [← heq]
  exact hrep

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: DeleteTransitionWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Removing the unique matching key from a distinct sequence removes exactly
its displayed occurrence, even when the query is a different equal key. -/
theorem deleteReferenceSplit {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (before after : List (K × V)) (stored : K × V) (query : K)
    (hd : Distinct same (before ++ stored :: after))
    (heq : same stored.1 query = true) :
    rdel same (before ++ stored :: after) query = before ++ after := by
  have hparts := List.pairwise_append.mp hd
  have htail := List.pairwise_cons.mp hparts.2.1
  have hb : ∀ pair ∈ before, same query pair.1 = false := by
    intro pair hm
    cases hq : same query pair.1 with
    | false => rfl
    | true =>
      have hfalse := hparts.2.2 pair hm stored (List.mem_cons_self)
      have htrue := hl.trans pair.1 query stored.1 (hl.symm query pair.1 hq)
        (hl.symm stored.1 query heq)
      rw [htrue] at hfalse
      cases hfalse
  have ha : ∀ pair ∈ after, same query pair.1 = false := by
    intro pair hm
    cases hq : same query pair.1 with
    | false => rfl
    | true =>
      have hfalse := htail.1 pair hm
      have htrue := hl.trans stored.1 query pair.1 heq hq
      rw [htrue] at hfalse
      cases hfalse
  have hquery := hl.symm stored.1 query heq
  unfold rdel
  rw [List.filter_append, List.filter_cons]
  simp only [hquery, Bool.not_true, Bool.false_eq_true, ite_false]
  change rdel same before query ++ rdel same after query = before ++ after
  rw [rdel_absent hb, rdel_absent ha]

/-- The public path record faithfully packages a successful concrete copying path. -/
theorem deleteWrappedPath {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap copied : HamtHeap K V) (root : Nat)
    (query : K) (result : PathResult K V)
    (hpath : runHamt (path heapVectorOps same runtime root
      (HashState.fromKey runtime query) true) heap = (.ok result, copied)) :
    (round2.hamtOps same runtime).path (.ok (heap, root))
      (HashState.fromKey runtime query) true =
      ⟨result.found, result.present, .ok (copied, result.trie), result.index,
        result.bi.x, .ok (copied, result.top), result.hash⟩ :=
  routingOpsPathGeneral same runtime heap copied root (HashState.fromKey runtime query) true result hpath

/-- The frozen deletion wrapper chooses the copied top in a miss and edits only
its selected focus when both flags are true. -/
theorem deleteResultEquation {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap copied : HamtHeap K V) (root : Nat)
    (query : K) (result : PathResult K V)
    (hpath : runHamt (path heapVectorOps same runtime root
      (HashState.fromKey runtime query) true) heap = (.ok result, copied)) :
    (persistentDelete (round2.hamtOps same runtime)
      (⟨.ok (heap, root)⟩ : PersistentDict K V (round2.PTrie K V)) query).trie =
      (if result.found && result.present then
        (round2.hamtOps same runtime).unset
          ((round2.hamtOps same runtime).deleteAt (.ok (copied, result.top))
            (.ok (copied, result.trie)) result.index)
          (.ok (copied, result.trie)) result.bi.x
      else .ok (copied, result.top)) := by
  change (let p := (round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime query) true;
    if p.found && p.present then
      (round2.hamtOps same runtime).unset
        ((round2.hamtOps same runtime).deleteAt p.top p.trie p.index) p.trie p.bitmapIndex
    else p.top) = _
  simp only [deleteWrappedPath same runtime heap copied root query result hpath]

/-- The two public edit callbacks compose the existing checked vector-erasure
and bitmap-clear actions into the exact finite focus heap. -/
theorem deleteWrappedEdit {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (copied : HamtHeap K V) (result : PathResult K V)
    (node : HAMTNode K V) (slots : List (Option (Entry K V)))
    (hn : copied.nodes[result.trie]? = some node)
    (hs : copied.vectors[node.data]? = some slots)
    (hlo : 1 ≤ result.index) (hhi : result.index ≤ slots.length) :
    (round2.hamtOps same runtime).unset
      ((round2.hamtOps same runtime).deleteAt (.ok (copied, result.top))
        (.ok (copied, result.trie)) result.index)
      (.ok (copied, result.trie)) result.bi.x =
      .ok ({ vectors := copied.vectors.set node.data (slots.eraseIdx (result.index - 1)), nodes := copied.nodes.set result.trie ⟨node.data, node.bitmap &&& (MASK32 ^^^ shiftLeftNat 1 result.bi.x)⟩ }, result.top) := by
  let middle : HamtHeap K V :=
    {copied with vectors := copied.vectors.set node.data (slots.eraseIdx (result.index - 1))}
  have hdelete : runHamt (do
      let data ← nodeData result.trie
      round2.heapVectorDeleteAt data result.index) copied = (.ok (), middle) := by
    rw [persistentHamtBindRun, copyPathNodeDataRun copied result.trie node hn]
    exact updateVectorDeleteRun copied node.data result.index slots hs hlo hhi
  have hdeleteOps : (round2.hamtOps same runtime).deleteAt (.ok (copied, result.top))
      (.ok (copied, result.trie)) result.index = .ok (middle, result.top) := by
    unfold round2.hamtOps round2.runAt
    dsimp only
    rw [hdelete]
  rw [hdeleteOps]
  unfold round2.hamtOps round2.runAt
  dsimp only
  rw [updateBitmapClearRun middle result.trie result.bi.x node hn] <;> rfl

/-- Deletion preserves finite structure, the filtered reference map, every
remaining key's independent route, and reference-key uniqueness. -/
theorem persistentRoutedRep_delete {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (dict : PersistentDict K V (round2.PTrie K V)) (reference : List (K × V)) (query : K)
    (hr : PersistentRoutedRep same runtime dict reference) :
    PersistentRoutedRep same runtime
      (persistentDelete (round2.hamtOps same runtime) dict query) (rdel same reference query) := by
  obtain ⟨heap, root, pairs, hd, htree, hperm, hrouting, hdistinct⟩ := hr
  have he : dict = ⟨.ok (heap, root)⟩ := by
    cases dict
    cases hd
    rfl
  subst dict
  obtain ⟨result, copied, focusBase, before, focusPairs, rest,
      hpath, hbase, hcopied, hcontext, hpairs, hterminal, htop, htransport, hrouteContext⟩ :=
    trieRep_copyPathFocus same runtime heap htree (HashState.fromKey runtime query)
  have hterminalSaved := hterminal
  obtain ⟨node, slots, hn, hs, hbitmap, hcount, hentries, hfreshRoot, hfreshData,
      hkey, hbi, hindex, hbit, hselected⟩ := hterminal
  have hfocus : TrieRep copied result.trie focusPairs :=
    .node hn hs hbitmap hcount (persistentEntriesRepFrame hcopied hentries)
  have htreeCopied : TrieRep copied result.top pairs := by
    rw [hpairs]
    exact contextReplace hcopied hcontext hfocus
  have hstoredCopied : StoredRouting runtime copied result.top pairs :=
    copyRouting_stored htransport hrouting
  cases hflags : result.found && result.present with
  | false =>
    have hmissing := copyFocus_missingReference same runtime hl hcopied hterminalSaved
      hrouteContext hstoredCopied hperm hflags
    have hreference : rdel same reference query = reference :=
      rdel_absent (rfind_eq_none_iff.mp hmissing)
    rw [hreference]
    refine ⟨copied, result.top, pairs, ?_, htreeCopied, hperm, hstoredCopied, hdistinct⟩
    rw [deleteResultEquation same runtime heap copied root query result hpath, hflags]
    rfl
  | true =>
    have hfp := Bool.and_eq_true_iff.mp hflags
    simp only [hfp.2, ite_true] at hselected
    obtain ⟨stored, hget, hfound⟩ := hselected
    have hequal : same stored.key query = true := hfound.symm.trans hfp.1
    have hselectedBit : Nat.testBit node.bitmap result.bi.x = true := hbit.trans hfp.2
    have hbitBound : result.bi.x < 32 := by rw [hbi]; exact pathBitmapIndex_lt result.hash
    have hindexRank : result.index - 1 = persistentBitmapRank node.bitmap result.bi.x := by
      rw [hindex, localRoutingIndexRank, hbi]
    have hlo : 1 ≤ result.index := by
      rw [hindex]
      exact Nat.le_add_left 1 _
    have hhi : result.index ≤ slots.length := by
      have := (List.getElem?_eq_some_iff.mp hget).1
      omega
    have hrootBound := (List.getElem?_eq_some_iff.mp hn).1
    have hdataBound := (List.getElem?_eq_some_iff.mp hs).1
    let edited : HamtHeap K V :=
      { vectors := copied.vectors.set node.data (slots.eraseIdx (result.index - 1)), nodes := copied.nodes.set result.trie ⟨node.data, node.bitmap &&& (MASK32 ^^^ shiftLeftNat 1 result.bi.x)⟩ }
    obtain ⟨localBefore, localAfter, hfocusPairs, hframeEdited, hfocusEdited⟩ :=
      persistentFocusEraseLeaf hcopied result.trie node.data node.bitmap result.bi.x
        (result.index - 1) slots focusPairs stored hrootBound hdataBound hfreshRoot hfreshData
        hbitmap hcount hentries hget hbitBound hselectedBit
    change PersistentHeapFrame focusBase edited at hframeEdited
    change TrieRep edited result.trie (localBefore ++ localAfter) at hfocusEdited
    let remaining : List (K × V) := before ++ (localBefore ++ localAfter) ++ rest
    have hwhole : pairs = (before ++ localBefore) ++ (stored.key, stored.val) :: (localAfter ++ rest) := by
      rw [hpairs, hfocusPairs]
      simp only [List.append_assoc, List.cons_append]
    have hdistinctPairs : Distinct same pairs := hdistinct.perm hl hperm.symm
    have hfiltered : rdel same pairs query = remaining := by
      rw [hwhole]
      rw [deleteReferenceSplit same runtime hl (before ++ localBefore) (localAfter ++ rest)
        (stored.key, stored.val) query (by simpa only [hwhole] using hdistinctPairs) hequal]
      simp only [remaining, List.append_assoc]
    have hpermRemaining : List.Perm remaining (rdel same reference query) := by
      rw [← hfiltered]
      exact hperm.filter (fun (pair : K × V) => !(same query pair.1))
    have hnEdited : edited.nodes[result.trie]? = some
        ⟨node.data, node.bitmap &&& (MASK32 ^^^ shiftLeftNat 1 result.bi.x)⟩ :=
      List.getElem?_set_self hrootBound
    have hsEdited : edited.vectors[node.data]? = some
        (slots.eraseIdx (persistentBitmapRank node.bitmap result.bi.x)) := by
      change (copied.vectors.set node.data (slots.eraseIdx (result.index - 1)))[node.data]? = _
      rw [List.getElem?_set_self hdataBound, hindexRank]
    have hgetRank : slots[persistentBitmapRank node.bitmap result.bi.x]? =
        some (some (.leaf stored)) := by simpa only [hindexRank] using hget
    have hremainingRoutes : StoredRouting runtime edited result.top remaining := by
      intro key value hmem
      have hmemFiltered := mem_rdel.mp (hpermRemaining.mem_iff.mp hmem)
      have hmemOld : (key, value) ∈ pairs := hperm.mem_iff.mpr hmemFiltered.1
      have hne : (⟨key, value⟩ : Leaf K V) ≠ stored := by
        intro hsame
        have hk := congrArg Leaf.key hsame
        dsimp only at hk
        have htrue := hl.symm stored.key query hequal
        rw [hk, htrue] at hmemFiltered
        cases hmemFiltered.2
      have hfocusTransport : ∀ hash,
          RoutedLeaf runtime copied result.trie hash (⟨key, value⟩ : Leaf K V) →
          RoutedLeaf runtime edited result.trie hash (⟨key, value⟩ : Leaf K V) := by
        intro hash hroute
        exact localRoutingEraseFocus runtime hcopied hframeEdited result.trie node node.data result.bi.x
          slots focusPairs stored hentries hn hs hnEdited hsEdited hbitmap hbitBound hselectedBit
          hgetRank hash ⟨key, value⟩ hne hroute
      exact copyRouting_liftFocus hcopied hframeEdited hcontext ⟨key, value⟩ hfocusTransport
        (HashState.fromKey runtime key) (hstoredCopied key value hmemOld)
    refine ⟨edited, result.top, remaining, ?_, ?_, hpermRemaining, hremainingRoutes,
      distinct_rdel hdistinct query⟩
    · rw [deleteResultEquation same runtime heap copied root query result hpath, hflags]
      exact deleteWrappedEdit same runtime copied result node slots hn hs hlo hhi
    · exact contextReplace hframeEdited hcontext hfocusEdited


/-- With deletion discharged, simultaneous reachability has only the successful
set-preservation obligation left. -/
theorem persistentRoutedTransitions_of_set {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (hset : ∀ (dict next : PersistentDict K V (round2.PTrie K V)) (reference : List (K × V))
        (key : K) (value : V),
      PersistentRoutedRep same runtime dict reference →
      persistentSetTyped (round2.hamtOps same runtime) dict key value = some (.ok next) →
      PersistentRoutedRep same runtime next (rset same reference key value)) :
    PersistentRoutedTransitions (V := V) same runtime :=
  ⟨hset, fun dict reference query hr =>
    persistentRoutedRep_delete same runtime hl dict reference query hr⟩

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: GrowthSetBridgeWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- A successful typed wrapper exposes a successful action on the concrete
copied heap, and returns that heap with the copied top handle. -/
theorem growthTypedSuccessAction {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K)
    (dict next : PersistentDict K V (round2.PTrie K V))
    (heap : HamtHeap K V) (root : Nat) (key : K) (value : V)
    (result : PathResult K V) (copied : HamtHeap K V)
    (hd : dict.trie = .ok (heap, root))
    (hp : runHamt (path heapVectorOps same runtime root (HashState.fromKey runtime key) true)
      heap = (.ok result, copied))
    (hs : persistentSetTyped (round2.hamtOps same runtime) dict key value = some (.ok next)) :
    ∃ inserted after,
      runPartialHamt (insert! heapVectorOps runtime result.found result.present result.trie
        result.index result.bi result.hash value) copied = some (.ok inserted, after) ∧
      next = ⟨.ok (after, result.top)⟩ := by
  have hpath := foundInsertOpsPath same runtime heap root (HashState.fromKey runtime key)
    result copied hp
  unfold persistentSetTyped JuliaLean.base.dict.persistentInsert at hs
  rw [hd] at hs
  change ((round2.hamtOps same runtime).insert
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).top
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).trie
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).found
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).present
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).index
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).bitmapIndex
    ((round2.hamtOps same runtime).path (.ok (heap, root)) (HashState.fromKey runtime key) true).state value).map
      (Except.map PersistentDict.mk) = some (.ok next) at hs
  rw [hpath] at hs
  unfold round2.hamtOps round2.runPartialAt at hs
  dsimp only at hs
  cases ha : runPartialHamt (insert! heapVectorOps runtime result.found result.present
      result.trie result.index result.bi result.hash value) copied with
  | none => rw [ha] at hs; cases hs
  | some output =>
    rcases output with ⟨outcome, after⟩
    rw [ha] at hs
    cases outcome with
    | error error => cases hs
    | ok inserted =>
      exact ⟨inserted, after, rfl, (Except.ok.inj (Option.some.inj hs)).symm⟩

/-- The local routing interface for a successful finite collision-growth trace.
The old leaf is required only at its reconstructed own-key hash. Other leaves
retain arbitrary routes through the edited focus. -/
def LocalGrowthRoutingPreservation {K V : Type} (runtime : HamtObjectIdRuntime K) : Prop :=
  ∀ (index : Nat) (value : V) (old : Leaf K V) (base heap : HamtHeap K V)
    (hash oldHash : HashState K) (root : Nat) (bi : BitmapIndex)
    (node : HAMTNode K V) (slots : List (Option (Entry K V))) (pairs : List (K × V)),
    PersistentHeapFrame base heap →
    heap.nodes[root]? = some node → heap.vectors[node.data]? = some slots →
    node.bitmap < 2 ^ 32 → countOnes 32 node.bitmap = slots.length →
    EntriesRep base slots pairs → slots[index - 1]? = some (some (.leaf old)) →
    Nat.testBit node.bitmap bi.x = true → 1 ≤ index →
    base.nodes.length ≤ root → base.vectors.length ≤ node.data →
    bi = BitmapIndex.fromHash hash → bi = BitmapIndex.fromHash oldHash →
    index = pathReadIndex node hash →
    ∀ (last : GrowthState K) (after : HamtHeap K V),
      SuccessfulLoopTrace (growthStateStep runtime index value old)
        ((hash, oldHash, root, bi, true, false), heap) (last, after) →
      RoutedLeaf runtime after root hash ⟨hash.key, value⟩ ∧
      RoutedLeaf runtime after root oldHash old ∧
      ∀ otherHash leaf, leaf ≠ old → RoutedLeaf runtime heap root otherHash leaf →
        RoutedLeaf runtime after root otherHash leaf

/-- The collision branch changes the focus's finite reference list and preserves
the complete represented map, using the concrete successful loop trace. -/
theorem growthInsert_preservesFocus {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (hlocal : LocalGrowthRoutingPreservation (V := V) runtime)
    (reference pairs : List (K × V)) (key : K) (value : V)
    (base before : HamtHeap K V) (result : PathResult K V)
    (outerBefore focusPairs outerAfter : List (K × V))
    (hf : PersistentHeapFrame base before)
    (hc : TrieContext base result.top result.trie outerBefore outerAfter)
    (hparts : pairs = outerBefore ++ focusPairs ++ outerAfter)
    (ht : CopyPathTerminal same key base before result focusPairs)
    (hr : StoredRouting runtime before result.top pairs)
    (hpref : RoutingContext runtime base result.top (HashState.fromKey runtime key)
      result.trie result.hash)
    (hd : Distinct same reference) (hperm : List.Perm pairs reference)
    (hfound : result.found = false) (inserted : Option BITMAP) (after : HamtHeap K V)
    (haction : runPartialHamt (insert! heapVectorOps runtime result.found result.present
      result.trie result.index result.bi result.hash value) before = some (.ok inserted, after)) :
    PersistentRoutedRep same runtime
      (⟨.ok (after, result.top)⟩ : PersistentDict K V (round2.PTrie K V))
      (rset same reference key value) := by
  have htSaved := ht
  obtain ⟨node, slots, hn, hs, hb, hcount, he, hfreshN, hfreshD, hkey, hbi, hi, hbit, hslot⟩ := ht
  have hpresent : result.present = true := by
    cases hh : result.present with
    | false =>
      simp only [hh, Bool.false_eq_true, ite_false] at hslot
      rw [hfound] at hslot
      cases hslot
    | true => rfl
  simp only [hpresent, ite_true] at hslot
  obtain ⟨old, hget, _⟩ := hslot
  have hlo : 1 ≤ result.index := by rw [hi]; exact Nat.le_add_left 1 _
  have hselected : Nat.testBit node.bitmap result.bi.x = true := hbit.trans hpresent
  have hmissing : ∀ pair ∈ pairs, same key pair.1 = false :=
    copyFocus_missing same runtime hl hf htSaved hpref hr (by simp only [hfound, Bool.false_and])
  have hdPairs : Distinct same pairs := hd.perm hl hperm.symm
  have htree : TrieRep before result.top pairs := by
    rw [hparts]
    exact contextReplace hf hc
      (.node (node := node) (slots := slots) hn hs hb hcount (persistentEntriesRepFrame hf he))
  have hOldPrefix := copyFocus_oldHashContextOfSelected same runtime hl hf htree hdPairs hparts
    htSaved hpref hr node slots old hn hs hget hpresent
  have hOldAlignment := copyFocus_oldHashOfSelected same runtime hl hf htree hdPairs hparts
    htSaved hpref hr node slots old hn hs hget hpresent
  have hOldBi : result.bi = BitmapIndex.fromHash
      (HashState.fromOtherAtDepth runtime result.hash old.key) :=
    congrArg BitmapIndex.mk hOldAlignment.2.symm
  rw [hfound, hpresent] at haction
  obtain ⟨returned, oldHash, startHeap, last, hprelude, htrace, _⟩ :=
    growthInsertFiniteTrace runtime true result.trie result.index result.bi result.hash
      value before after inserted haction
  obtain ⟨_, hreturned, holdHash, hstart⟩ :=
    growthPrelude_success_identifies runtime before result.trie result.index node slots old returned
      true result.hash oldHash startHeap hn hs hlo hget hprelude
  subst returned
  subst oldHash
  subst startHeap
  obtain ⟨hframe, newFocusPairs, hfocus, hfocusPerm⟩ :=
    growthSuccessfulStructure runtime result.index value old base before result.hash
      (HashState.fromOtherAtDepth runtime result.hash old.key) result.trie result.bi node slots
      focusPairs hf hn hs hb hcount he hget hselected hlo hfreshN hfreshD htrace
  have hfocusPerm' : List.Perm newFocusPairs ((key, value) :: focusPairs) := by
    simpa only [hkey] using hfocusPerm
  let newPairs := outerBefore ++ newFocusPairs ++ outerAfter
  have hnewPerm : List.Perm newPairs (rset same pairs key value) := by
    rw [hparts]
    exact persistentReferenceGrowPerm same outerBefore outerAfter focusPairs newFocusPairs key value
      hfocusPerm' (fun pair hm => hmissing pair (by simpa only [hparts] using hm))
  have hnewTree : TrieRep after result.top newPairs := contextReplace hframe hc hfocus
  obtain ⟨hnewRoute, hOldRoute, hOtherRoutes⟩ :=
    hlocal result.index value old base before result.hash
      (HashState.fromOtherAtDepth runtime result.hash old.key) result.trie result.bi node slots
      focusPairs hf hn hs hb hcount he hget hselected hlo hfreshN hfreshD hbi hOldBi hi last after htrace
  have hnewRoute' : RoutedLeaf runtime after result.trie result.hash ⟨key, value⟩ := by
    simpa only [hkey] using hnewRoute
  have hOldMem : (old.key, old.val) ∈ pairs := by
    rw [hparts]
    exact List.mem_append_left _ (List.mem_append_right _ (copyEntries_leafMem he hget))
  have hrouting : StoredRouting runtime after result.top newPairs := by
    intro storedKey storedValue hm
    rcases mem_rset.mp (hnewPerm.mem_iff.1 hm) with heq | ⟨hold, _⟩
    · cases heq
      exact copyRouting_contextFill (copyRouting_contextFrame hframe hpref) hnewRoute'
    · cases heq : same old.key storedKey with
      | false =>
        have hne : (⟨storedKey, storedValue⟩ : Leaf K V) ≠ old := by
          intro hequal
          have hk := congrArg Leaf.key hequal
          change storedKey = old.key at hk
          rw [hk, hl.refl old.key] at heq
          cases heq
        exact copyRouting_liftFocus hf hframe hc ⟨storedKey, storedValue⟩
          (fun hash route => hOtherRoutes hash ⟨storedKey, storedValue⟩ hne route)
          (HashState.fromKey runtime storedKey) (hr storedKey storedValue hold)
      | true =>
        have hOldFind := rfind_of_mem hl.query hdPairs hOldMem (hl.refl old.key)
        have hStoredFind := rfind_of_mem hl.query hdPairs hold heq
        have hp : (storedKey, storedValue) = (old.key, old.val) :=
          Option.some.inj (hStoredFind.symm.trans hOldFind)
        have hk := congrArg Prod.fst hp
        have hv := congrArg Prod.snd hp
        dsimp only at hk hv
        subst storedKey
        subst storedValue
        exact copyRouting_contextFill (copyRouting_contextFrame hframe hOldPrefix) hOldRoute
  exact ⟨after, result.top, newPairs, rfl, hnewTree,
    hnewPerm.trans (persistentReferenceSetPerm same hperm key value), hrouting,
    distinct_rset hd key value⟩

/-- Every successful frozen typed insertion preserves the full independent
representation once the finite collision-growth routing lemma is available. -/
theorem persistentRoutedRep_set_of_localGrowth {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (hlocal : LocalGrowthRoutingPreservation (V := V) runtime)
    (dict next : PersistentDict K V (round2.PTrie K V)) (reference : List (K × V))
    (key : K) (value : V) (hr : PersistentRoutedRep same runtime dict reference)
    (hs : persistentSetTyped (round2.hamtOps same runtime) dict key value = some (.ok next)) :
    PersistentRoutedRep same runtime next (rset same reference key value) := by
  have hrSaved := hr
  obtain ⟨heap, root, pairs, hd, ht, hperm, hrouting, hdistinct⟩ := hr
  obtain ⟨result, copied, focusBase, before, focusPairs, rest,
      hpath, hbase, hfinal, hcontext, hpairs, hterminal, htop, htransport, hprefix⟩ :=
    trieRep_copyPathFocus same runtime heap ht (HashState.fromKey runtime key)
  cases hfound : result.found with
  | false =>
    obtain ⟨inserted, after, haction, hnext⟩ :=
      growthTypedSuccessAction same runtime dict next heap root key value result copied hd hpath hs
    rw [hnext]
    exact growthInsert_preservesFocus same runtime hl hlocal reference pairs key value focusBase copied
      result before focusPairs rest hfinal hcontext hpairs hterminal
      (copyRouting_stored htransport hrouting) hprefix hdistinct hperm hfound inserted after haction
  | true =>
    have hfoundOps : ((round2.hamtOps same runtime).path dict.trie
        (HashState.fromKey runtime key) true).found = true := by
      rw [hd, foundInsertOpsPath same runtime heap root (HashState.fromKey runtime key)
        result copied hpath]
      exact hfound
    exact persistentSet_foundPreserves same runtime hl dict next reference key value hrSaved hfoundOps hs

theorem persistentRoutedTransitions_of_localGrowth {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (hlocal : LocalGrowthRoutingPreservation (V := V) runtime) :
    PersistentRoutedTransitions (V := V) same runtime :=
  persistentRoutedTransitions_of_set same runtime hl
    (persistentRoutedRep_set_of_localGrowth same runtime hl hlocal)

/-- The finite local growth proof discharges the routing interface without an
additional condition on represented histories or hash collision termination. -/
theorem localGrowthRoutingPreservation {K V : Type} (runtime : HamtObjectIdRuntime K) :
    LocalGrowthRoutingPreservation (V := V) runtime := by
  intro index value old base heap hash oldHash root bi node slots pairs hf hn hs hb hc he hslot
    hbit hlo hfn hfd hnewBi holdBi hindex last after ht
  exact (growthSuccessfulRouting runtime index value old base heap hash oldHash root bi node slots pairs
    hf hn hs hb hc he hslot hbit hlo hfn hfd hnewBi holdBi hindex ht).2

theorem persistentRoutedTransitions_constructed {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same) :
    PersistentRoutedTransitions (V := V) same runtime :=
  persistentRoutedTransitions_of_localGrowth same runtime hl (localGrowthRoutingPreservation runtime)


theorem persistentPathSafe_fromConcreteTransitions : round2.PersistentPathSafe :=
  persistentPathSafe_of_routedTransitions
    (fun _ _ same runtime hl => persistentRoutedTransitions_constructed same runtime hl)


theorem persistentCollection_fromConcreteTransitions : round2.PersistentCollectionSemantics :=
  persistentCollection_of_routedTransitions
    (fun _ _ same runtime hl => persistentRoutedTransitions_constructed same runtime hl)

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: ReusedWork.lean

/-! Exact target proofs reusing the supplied, already closed source-level theorems. -/

namespace JuliaLean.ChatGPT.Batch4.Group1

/-- dicts-setindex-lookup. -/
theorem DictsSetindexLookup_proven : JuliaLean.Proofs.base.dict.DictSetindexLookup :=
  JuliaLean.Proofs.base.dict.DictSetindexLookup_proven

/-- dicts-float-keys-isequal. -/
theorem DictsFloatKeysIsequal_proven : JuliaLean.Proofs.base.dict.DictSetindexLookup :=
  JuliaLean.Proofs.base.dict.DictSetindexLookup_proven

/-- dictscov-dict-setindex. -/
theorem DictscovDictSetindex_proven : JuliaLean.Proofs.base.dict.DictSetindexLookup :=
  JuliaLean.Proofs.base.dict.DictSetindexLookup_proven

/-- dictscov-dict-l374. -/
theorem DictscovDictL374_proven : JuliaLean.Proofs.base.dict.DictSetindexLookup :=
  JuliaLean.Proofs.base.dict.DictSetindexLookup_proven

/-- dictscov-dict-l359. -/
theorem DictscovDictL359_proven : JuliaLean.Proofs.base.dict.DictSetindexLookup :=
  JuliaLean.Proofs.base.dict.DictSetindexLookup_proven

/-- dictscov-dict-l327. -/
theorem DictscovDictL327_proven : JuliaLean.Proofs.base.dict.DictSetindexLookup :=
  JuliaLean.Proofs.base.dict.DictSetindexLookup_proven

/-- dictscov-dict-l347. -/
theorem DictscovDictL347_proven : JuliaLean.Proofs.base.dict.DictSetindexLookup :=
  JuliaLean.Proofs.base.dict.DictSetindexLookup_proven

/-- dictscov-dict-keyindex. -/
theorem DictscovDictKeyindex_proven : JuliaLean.Proofs.base.dict.DictProbeSemantics :=
  JuliaLean.Proofs.base.dict.DictProbeSemantics_proven

/-- dictscov-dict-l241. -/
theorem DictscovDictL241_proven : JuliaLean.Proofs.base.dict.DictProbeSemantics :=
  JuliaLean.Proofs.base.dict.DictProbeSemantics_proven

/-- dicts-empty. -/
theorem DictsEmpty_proven : JuliaLean.Proofs.base.dict.DictEmptyContract :=
  JuliaLean.Proofs.base.dict.DictEmptyContract_proven

/-- dictscov-dict-l712. -/
theorem DictscovDictL712_proven : JuliaLean.Proofs.base.dict.DictEmptyContract :=
  JuliaLean.Proofs.base.dict.DictEmptyContract_proven

/-- dicts-sizehint-small. -/
theorem DictsSizehintSmall_proven : JuliaLean.Proofs.base.dict.DictSizehintSmall :=
  JuliaLean.Proofs.base.dict.DictSizehintSmall_proven

/-- dicts-getbang-mutating-default. -/
theorem DictsGetbangMutatingDefault_proven : JuliaLean.Proofs.base.dict.DictGetBangMutatingDefault :=
  JuliaLean.Proofs.base.dict.DictGetBangMutatingDefault_proven

/-- dictscov-dict-getbang. -/
theorem DictscovDictGetbang_proven : JuliaLean.Proofs.base.dict.DictGetBangMutatingDefault :=
  JuliaLean.Proofs.base.dict.DictGetBangMutatingDefault_proven

/-- dictscov-dict-l457. -/
theorem DictscovDictL457_proven : JuliaLean.Proofs.base.dict.DictGetBangMutatingDefault :=
  JuliaLean.Proofs.base.dict.DictGetBangMutatingDefault_proven

/-- dictscov-dict-l445. -/
theorem DictscovDictL445_proven : JuliaLean.Proofs.base.dict.DictGetBangMutatingDefault :=
  JuliaLean.Proofs.base.dict.DictGetBangMutatingDefault_proven

/-- dictscov-dict-l91. -/
theorem DictscovDictL91_proven : JuliaLean.Proofs.base.dict.DictIteratorConstructorSemantics :=
  JuliaLean.Proofs.base.dict.DictIteratorConstructorSemantics_proven

/-- dictscov-dict-l100. -/
theorem DictscovDictL100_proven : JuliaLean.Proofs.base.dict.DictConstructorSemantics :=
  JuliaLean.Proofs.base.dict.DictConstructorSemantics_proven

/-- dictscov-dict-l115. -/
theorem DictscovDictL115_proven : JuliaLean.Proofs.base.dict.DictTypedPairListConstructorSemantics :=
  JuliaLean.Proofs.base.dict.DictTypedPairListConstructorSemantics_proven

/-- dictscov-dict-l83. -/
theorem DictscovDictL83_proven : JuliaLean.Proofs.base.dict.DictCopySemantics :=
  JuliaLean.Proofs.base.dict.DictCopySemantics_proven

/-- dictscov-dict-construct. -/
theorem DictscovDictConstruct_proven : JuliaLean.Proofs.base.dict.DictConstructionSemantics :=
  JuliaLean.Proofs.base.dict.DictConstructionSemantics_proven

/-- dictscov-dict-l135. -/
theorem DictscovDictL135_proven : JuliaLean.Proofs.base.dict.DictSlots :=
  JuliaLean.Proofs.base.dict.DictSlots_proven

/-- dictscov-dict-l136. -/
theorem DictscovDictL136_proven : JuliaLean.Proofs.base.dict.DictSlots :=
  JuliaLean.Proofs.base.dict.DictSlots_proven

/-- dictscov-dict-l137. -/
theorem DictscovDictL137_proven : JuliaLean.Proofs.base.dict.DictSlots :=
  JuliaLean.Proofs.base.dict.DictSlots_proven

/-- dictscov-dict-l123. -/
theorem DictscovDictL123_proven : JuliaLean.Proofs.base.dict.DictSlots :=
  JuliaLean.Proofs.base.dict.DictSlots_proven

/-- dictscov-dict-slots. -/
theorem DictscovDictSlots_proven : JuliaLean.Proofs.base.dict.DictSlotSemantics :=
  JuliaLean.Proofs.base.dict.DictSlotSemantics_proven

/-- memsafety-dict-probes. -/
theorem MemsafetyDictProbes_proven : JuliaLean.Proofs.base.dict.DictProbeSafe :=
  JuliaLean.Proofs.base.dict.DictProbeSafe_proven

/-- dictscov-dict-persistent-set. -/
theorem DictscovDictPersistentSet_proven : JuliaLean.Proofs.base.dict.PersistentSetSemantics :=
  JuliaLean.Proofs.base.dict.PersistentSetSemantics_proven

/-- dictscov-dict-persistent-delete. -/
theorem DictscovDictPersistentDelete_proven : JuliaLean.Proofs.base.dict.PersistentDeleteSemantics :=
  JuliaLean.Proofs.base.dict.PersistentDeleteSemantics_proven

/-- dictscov-dict-persistent-construct. -/
theorem DictscovDictPersistentConstruct_proven : JuliaLean.Proofs.base.dict.PersistentConstructorSemantics :=
  JuliaLean.Proofs.base.dict.PersistentConstructorSemantics_proven

/-- dictscov-dict-immutable-similar. -/
theorem DictscovDictImmutableSimilar_proven : JuliaLean.Proofs.base.dict.DictSimilarSemantics :=
  JuliaLean.Proofs.base.dict.DictSimilarSemantics_proven

/-- dicts-source-mergewith. -/
theorem DictsSourceMergewith_proven : JuliaLean.Proofs.base.dict.DictMergewithSemantics :=
  JuliaLean.Proofs.base.dict.DictMergewithSemantics_proven

/-- dictscov-dict-l735. -/
theorem DictscovDictL735_proven : JuliaLean.Proofs.base.dict.DictReduceMergeSemantics :=
  JuliaLean.Proofs.base.dict.DictReduceMergeSemantics_proven

/-- dictscov-dict-map-reduce. -/
theorem DictscovDictMapReduce_proven : JuliaLean.Proofs.base.dict.DictMapReduceMergeSemantics :=
  JuliaLean.Proofs.base.dict.DictMapReduceMergeSemantics_proven

/-- dicts-ops-agree. -/
theorem DictsOpsAgree_proven : JuliaLean.Proofs.base.dict.DictOperationsAgree :=
  JuliaLean.Proofs.base.dict.DictOperationsAgree_proven

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: ReadOnlyWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict

/-- Initial iteration is empty exactly when the independently enumerated slot list is empty. -/
theorem initialIteration_none_iff {K V : Type} {hash : K → JInt .u64}
    {eqKey : K → K → Bool} {h : DictState K V}
    (hi : Inv hash eqKey h) (hbound : h.size < 2 ^ 63 - 1) :
    iterateFirst h = .ok none ↔ tlist h = [] := by
  have hr : DictRep hash eqKey h (tlist h) := ⟨hi, List.Perm.refl _⟩
  have hit := (hr.iterate hbound).1
  constructor
  · intro hnone
    rw [hnone] at hit
    exact (Except.ok.inj hit).symm
  · intro hnil
    rw [hnil] at hit
    cases hfirst : iterateFirst h with
    | error err =>
      rw [hfirst] at hit
      cases hit
    | ok step =>
      cases step with
      | none => rfl
      | some pairNext =>
        obtain ⟨pair, next⟩ := pairNext
        rw [hfirst] at hit
        change (iterCollect h (h.size + 1) next >>= fun rest =>
          Except.ok (pair :: rest)) = Except.ok [] at hit
        cases hrest : iterCollect h (h.size + 1) next with
        | error err =>
          rw [hrest] at hit
          cases hit
        | ok rest =>
          rw [hrest] at hit
          cases hit

/-- dictscov-dict-l712-v2: exact frozen read-only observation contract. -/
theorem DictscovDictL712V2_proven :
    JuliaLean.Proofs.base.dict.Round3.DictReadOnlyObservations := by
  intro K V hash eqKey h hi hbound
  have hr : DictRep hash eqKey h (tlist h) := ⟨hi, List.Perm.refl _⟩
  refine ⟨?_, tlist h, (hr.iterate hbound).1, hi.count⟩
  rw [initialIteration_none_iff hi hbound]
  change (h.count == 0) = true ↔ tlist h = []
  rw [hi.count]
  exact Iff.trans (beq_iff_eq) List.length_eq_zero_iff

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: MutationWork.lean

/-! Usable partial contracts for the unchanged round-two mutation statements.
The native-index bound is explicit in these helpers; none is presented as an
unconditional target proof. -/

namespace JuliaLean.ChatGPT.Batch4.Group1

open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict
open JuliaLean.src.genericmemory_c (DictLayout)

theorem mutationDeleteLookup_of_sizeBound
    (K V Q : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (hashQ : Q → JInt .u64) (matchQ : Q → K → Bool)
    (rtK rtV : DictLayout) (h : DictState K V) (m : List (K × V))
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (hsz : h.size < 2 ^ 63) (q : Q) :
    ∃ h', deleteKey hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q =
        .ok h' ∧ DictRep hash eqKey h' (rdel matchQ m q) :=
  round2.DictDeleteLookup_of_size_lt K V Q hash eqKey hashQ matchQ rtK rtV h m
    hl hq hr hsz q

theorem mutationPopKey_of_sizeBound
    (K V Q D : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (hashQ : Q → JInt .u64) (matchQ : Q → K → Bool)
    (rtK rtV : DictLayout) (h : DictState K V) (m : List (K × V))
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (hsz : h.size < 2 ^ 63) (q : Q) (default : D) :
    (match rfind matchQ m q with
      | some e => ∃ h',
          popKey hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q =
            .ok (e.2, h') ∧ DictRep hash eqKey h' (rdel matchQ m q)
      | none => popKey hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q =
          .error .keyError) ∧
    (match rfind matchQ m q with
      | some e => ∃ h',
          popDefault hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q default =
            .ok (.inl e.2, h') ∧ DictRep hash eqKey h' (rdel matchQ m q)
      | none => popDefault hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV)
          h q default = .ok (.inr default, h)) :=
  round2.DictPopKeyContract_of_size_lt K V Q D hash eqKey hashQ matchQ rtK rtV h m
    hl hq hr hsz q default

theorem mutationPopAny_of_sizeBound
    (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (rtK rtV : DictLayout) (h : DictState K V) (m : List (K × V))
    (hl : KeyLaws hash eqKey) (hr : DictRep hash eqKey h m)
    (hsz : h.size < 2 ^ 63) :
    match m with
    | [] => popAny (round2.memUnset rtK) (round2.memUnset rtV) h = .error .argumentError
    | _ :: _ => ∃ e h', popAny (round2.memUnset rtK) (round2.memUnset rtV) h =
        .ok (e, h') ∧ e ∈ m ∧ DictRep hash eqKey h' (rdel eqKey m e.1) :=
  round2.DictPopAnyContract_of_size_lt K V hash eqKey rtK rtV h m hl hr hsz

theorem mutationFilter_of_sizeBound
    (K V : Type) (hash : K → JInt .u64) (eqKey : K → K → Bool)
    (rtK rtV : DictLayout) (h : DictState K V) (m : List (K × V))
    (hl : KeyLaws hash eqKey) (hr : DictRep hash eqKey h m)
    (hsz : h.size < 2 ^ 63) (pred : K × V → Bool) :
    ∃ h', filterBang (round2.memUnset rtK) (round2.memUnset rtV) pred h = .ok h' ∧
      DictRep hash eqKey h' (m.filter pred) :=
  round2.DictFilterContract_of_size_lt K V hash eqKey rtK rtV h m hl hr hsz pred

/-- All structural iteration conjuncts hold for arbitrary finite lists. The
count conjunct describes the exact frozen native arithmetic, including wrap. -/
theorem immutableCollection_with_wrappingCount
    (K V : Type) (d : ImmutableDict K V) :
    immutableIterate (immutableEmpty K V) = none ∧
    (∀ (p : K × V) (rest : ImmutableDict K V),
      immutableIterate (p :: rest) = some (p, rest) ∧
      immutableIterate d [] = none ∧
      immutableIterate d (p :: rest) = some (p, rest)) ∧
    immutableLength (fun p x => .ok (round2.immCount p x)) d =
      .ok (JInt.wrap .i64 (immutableCollect d).length).val.toNat ∧
    immutableIsEmpty d = (immutableIterate d).isNone ∧
    immutableEmptyLike K V d = immutableEmpty K V ∧
    immutableCollect (immutableEmptyLike K V d) = [] := by
  refine ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, rfl, rfl⟩
  · change Except.ok (round2.immCount (fun _ => true) d) = _
    rw [round2.immCount_true_eq]
  · cases d <;> rfl

/-- The complete frozen conclusion, restricted only by a native count bound. -/
theorem immutableCollection_of_lengthBound
    (K V : Type) (d : ImmutableDict K V) (h : d.length < 2 ^ 63) :
    immutableIterate (immutableEmpty K V) = none ∧
    (∀ (p : K × V) (rest : ImmutableDict K V),
      immutableIterate (p :: rest) = some (p, rest) ∧
      immutableIterate d [] = none ∧
      immutableIterate d (p :: rest) = some (p, rest)) ∧
    immutableLength (fun p x => .ok (round2.immCount p x)) d =
      .ok (immutableCollect d).length ∧
    immutableIsEmpty d = (immutableIterate d).isNone ∧
    immutableEmptyLike K V d = immutableEmpty K V ∧
    immutableCollect (immutableEmptyLike K V d) = [] :=
  round2.ImmutableDictCollectionSemantics_of_length_lt K V d h

end JuliaLean.ChatGPT.Batch4.Group1

-- Source section: RefutationWork.lean

namespace JuliaLean.ChatGPT.Batch4.Group1

/-- A 17-entry table and the scalar Int64 hint 2^62 reach a 16-slot rehash. -/
theorem DictsSizehintWrapHang_refuted :
    ¬ JuliaLean.Proofs.base.dict.DictSizehintTotal :=
  JuliaLean.Proofs.base.dict.DictSizehintTotal_refuted

/-- Exactly ten pairs are all displayed, followed by an unwarranted ellipsis. -/
theorem DictscovShowLimitEllipsis_refuted :
    ¬ JuliaLean.Proofs.base.dict.DictShowLimitEllipsis :=
  JuliaLean.Proofs.base.dict.DictShowLimitEllipsis_refuted

/-- Iteration of a two-entry ImmutableDict visits newest first; Dict keeps oldest last. -/
theorem DictsImmutabledictToDict_refuted :
    ¬ JuliaLean.Proofs.base.dict.ImmutableDictToDict :=
  JuliaLean.Proofs.base.dict.ImmutableDictToDict_refuted

end JuliaLean.ChatGPT.Batch4.Group1

namespace JuliaLean.ChatGPT.Batch4.Group1


theorem MemsafetyDictPersistentPath_proven : JuliaLean.Proofs.base.dict.round2.PersistentPathSafe :=
  persistentPathSafe_fromConcreteTransitions


theorem DictscovDictPersistentCollection_proven : JuliaLean.Proofs.base.dict.round2.PersistentCollectionSemantics :=
  persistentCollection_fromConcreteTransitions

end JuliaLean.ChatGPT.Batch4.Group1
end

section

namespace JuliaLean.ChatGPT.Batch5.Group5
open JuliaLean JuliaLean.base.dict JuliaLean.Proofs.base.dict
open JuliaLean.src.genericmemory_c (DictLayout)

/-- The native bound is needed only for the slot actually changed by this
operation; the table can be symbolically larger. -/
theorem mutationDeleteAt_of_indexBound
    {K V Q : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (rtK rtV : DictLayout) {h : DictState K V} {m : List (K × V)}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) {q : Q} {i : Nat} {e : K × V}
    (hi1 : 1 ≤ i) (hi2 : i ≤ h.size) (he : ent h i = some e)
    (hm : matchQ q e.1 = true) (hi64 : i < 2 ^ 63) :
    DictRep hash eqKey
        (deleteAt (round2.memUnset rtK) (round2.memUnset rtV) h i)
        (rdel matchQ m q) ∧
      (deleteAt (round2.memUnset rtK) (round2.memUnset rtV) h i).count = h.count - 1 := by
  rw [round2.deleteAt_clampUnset63 rtK rtV h i hi64]
  exact hr.deleteAt hl (round2.clampUnset63_law rtK) (round2.clampUnset63_law rtV)
    hq hi1 hi2 he hm

/-- All three key-based mutation wrappers agree with the law-abiding clamped
callee whenever their returned slot has a representable native index. -/
theorem mutationWrappers_of_probeBound
    {K V Q D : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (rtK rtV : DictLayout) {h : DictState K V} {m : List (K × V)}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (q : Q) (default : D)
    (hslot : ∀ i : Nat, htKeyindex hashQ matchQ h q = .ok (i : Int) → i < 2 ^ 63) :
    deleteKey hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q =
        deleteKey hashQ matchQ (round2.clampUnset63 (round2.memUnset rtK))
          (round2.clampUnset63 (round2.memUnset rtV)) h q ∧
    popKey hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q =
        popKey hashQ matchQ (round2.clampUnset63 (round2.memUnset rtK))
          (round2.clampUnset63 (round2.memUnset rtV)) h q ∧
    popDefault hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q default =
        popDefault hashQ matchQ (round2.clampUnset63 (round2.memUnset rtK))
          (round2.clampUnset63 (round2.memUnset rtV)) h q default := by
  rcases round2.htKeyindex_le_size hl hq hr q with hk | ⟨i, hk, hi1, _⟩
  · unfold deleteKey popKey popDefault
    rw [hk]
    exact ⟨rfl, rfl, rfl⟩
  · have hi64 := hslot i hk
    have hiNat : (i : Int).toNat = i := Int.toNat_natCast i
    refine ⟨?_, ?_, ?_⟩
    · unfold deleteKey
      rw [hk, except_ok_bind, except_ok_bind, ite_eq_left (by omega), ite_eq_left (by omega), hiNat]
      rw [round2.deleteAt_clampUnset63 rtK rtV h i hi64]
    · unfold popKey
      rw [hk, except_ok_bind, except_ok_bind, ite_eq_left (by omega), ite_eq_left (by omega), hiNat]
      exact round2.popAt_clampUnset63 rtK rtV h i hi64
    · unfold popDefault
      rw [hk, except_ok_bind, except_ok_bind, ite_eq_left (by omega), ite_eq_left (by omega), hiNat]
      rw [round2.popAt_clampUnset63 rtK rtV h i hi64]

/-- Full deletion conclusion with an operation-specific native-index premise. -/
theorem mutationDeleteLookup_of_probeBound
    {K V Q : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (rtK rtV : DictLayout) {h : DictState K V} {m : List (K × V)}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (q : Q)
    (hslot : ∀ i : Nat, htKeyindex hashQ matchQ h q = .ok (i : Int) → i < 2 ^ 63) :
    ∃ h', deleteKey hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q =
        .ok h' ∧ DictRep hash eqKey h' (rdel matchQ m q) := by
  rw [(mutationWrappers_of_probeBound rtK rtV hl hq hr q () hslot).1]
  exact hr.deleteKey hl (round2.clampUnset63_law rtK) (round2.clampUnset63_law rtV) hq q

/-- Both key-pop conclusions with an operation-specific native-index premise. -/
theorem mutationPopKey_of_probeBound
    {K V Q D : Type} {hash : K → JInt .u64} {eqKey : K → K → Bool}
    {hashQ : Q → JInt .u64} {matchQ : Q → K → Bool}
    (rtK rtV : DictLayout) {h : DictState K V} {m : List (K × V)}
    (hl : KeyLaws hash eqKey) (hq : QueryLaws hash eqKey hashQ matchQ)
    (hr : DictRep hash eqKey h m) (q : Q) (default : D)
    (hslot : ∀ i : Nat, htKeyindex hashQ matchQ h q = .ok (i : Int) → i < 2 ^ 63) :
    (match rfind matchQ m q with
      | some e => ∃ h',
          popKey hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q =
            .ok (e.2, h') ∧ DictRep hash eqKey h' (rdel matchQ m q)
      | none => popKey hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q =
          .error .keyError) ∧
    (match rfind matchQ m q with
      | some e => ∃ h',
          popDefault hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV) h q default =
            .ok (.inl e.2, h') ∧ DictRep hash eqKey h' (rdel matchQ m q)
      | none => popDefault hashQ matchQ (round2.memUnset rtK) (round2.memUnset rtV)
          h q default = .ok (.inr default, h)) := by
  have hw := mutationWrappers_of_probeBound rtK rtV hl hq hr q default hslot
  rw [hw.2.1, hw.2.2]
  exact ⟨hr.popKey hl (round2.clampUnset63_law rtK) (round2.clampUnset63_law rtV) hq q,
    hr.popDefault hl (round2.clampUnset63_law rtK) (round2.clampUnset63_law rtV) hq q default⟩

/-- Exact admissible domain of the frozen immutable dictionary length clause.
This is a symbolic statement about the model, with no oversized Julia allocation. -/
theorem immutableLength_correct_iff_lengthBound
    (K V : Type) (d : ImmutableDict K V) :
    immutableLength (fun p x => .ok (round2.immCount p x)) d =
        .ok (immutableCollect d).length ↔ d.length < 2 ^ 63 := by
  change Except.ok (round2.immCount (fun _ => true) d) =
    (Except.ok (immutableCollect d).length : DictResult Nat) ↔ d.length < 2 ^ 63
  rw [Except.ok.injEq, round2.immCount_true_eq, immutableCollect_eq]
  constructor
  · intro h
    have hu := (JInt.wrap .i64 (d.length : Int)).property.2
    simp only [IntTy.max, IntTy.signed, IntTy.bits, ite_true] at hu
    omega
  · intro h
    show (wrapInt .i64 (d.length : Int)).toNat = d.length
    rw [wrapInt_of_inRange .i64 (d.length : Int)
      ⟨by simp only [IntTy.min, IntTy.signed, IntTy.bits, ite_true]; omega,
       by simp only [IntTy.max, IntTy.signed, IntTy.bits, ite_true]; omega⟩]
    exact Int.toNat_natCast d.length

/-- Every other immutable collection clause is unconditional, so the same
native-length bound is necessary and sufficient for the whole frozen conclusion. -/
theorem immutableCollection_correct_iff_lengthBound
    (K V : Type) (d : ImmutableDict K V) :
    (immutableIterate (immutableEmpty K V) = none ∧
    (∀ (p : K × V) (rest : ImmutableDict K V),
      immutableIterate (p :: rest) = some (p, rest) ∧
      immutableIterate d [] = none ∧
      immutableIterate d (p :: rest) = some (p, rest)) ∧
    immutableLength (fun p x => .ok (round2.immCount p x)) d =
      .ok (immutableCollect d).length ∧
    immutableIsEmpty d = (immutableIterate d).isNone ∧
    immutableEmptyLike K V d = immutableEmpty K V ∧
    immutableCollect (immutableEmptyLike K V d) = []) ↔ d.length < 2 ^ 63 := by
  constructor
  · intro h
    exact (immutableLength_correct_iff_lengthBound K V d).1 h.2.2.1
  · intro h
    exact round2.ImmutableDictCollectionSemantics_of_length_lt K V d h

end JuliaLean.ChatGPT.Batch5.Group5

namespace JuliaLean.ChatGPT.Batch5.Group5

open JuliaLean JuliaLean.base.hamt JuliaLean.base.dict JuliaLean.Proofs.base.dict
open JuliaLean.ChatGPT.Batch4.Group1

/-- A checked leaf read returns its stored value through the concrete operation record. -/
theorem persistentLeafValueOfRead {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (root index : Nat)
    (leaf : Leaf K V)
    (hread : runHamt (do
      let node ← readNode root
      heapVectorOps.get node.data index) heap = (.ok (.leaf leaf), heap)) :
    (round2.hamtOps same runtime).leafValue (.ok (heap, root)) index = some leaf.val := by
  unfold round2.hamtOps round2.runTrie
  dsimp only
  rw [← bind_assoc, persistentHamtBindRun, hread]
  rfl

/-- A query equal to a routed stored key returns that leaf's exact value. -/
theorem persistentKeyGetPresent {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (heap : HamtHeap K V) (root : Nat)
    (query : K) (leaf : Leaf K V)
    (hr : RoutedLeaf runtime heap root (HashState.fromKey runtime query) leaf)
    (heq : same leaf.key query = true) :
    persistentKeyGet (round2.hamtOps same runtime)
      (⟨.ok (heap, root)⟩ : PersistentDict K V (round2.PTrie K V)) query = some leaf.val := by
  obtain ⟨result, hpath, hf, hp, hread⟩ := routedLeaf_path same hr
  have hlevel := routedLeaf_opsNonempty same hr
  have hfound : result.found = true := hf.trans heq
  rw [routingKeyGetEquation same runtime heap root query result hpath, hlevel]
  simp only [Bool.false_eq_true, ite_false, hfound, hp, Bool.true_and, ite_true]
  exact persistentLeafValueOfRead same runtime heap result.trie result.index leaf hread

/-- Finite structure and independent hash routing give the exact reference lookup. -/
theorem persistentKeyGetOfRoutedTree {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    (heap : HamtHeap K V) {root : Nat} {pairs reference : List (K × V)}
    (hr : TrieRep heap root pairs) (hperm : List.Perm pairs reference)
    (hrouting : StoredRouting runtime heap root pairs) (query : K) :
    persistentKeyGet (round2.hamtOps same runtime)
      (⟨.ok (heap, root)⟩ : PersistentDict K V (round2.PTrie K V)) query =
      rlookup same reference query := by
  cases hf : rfind same reference query with
  | none =>
    rw [rlookup, hf]
    exact routingKeyGetAbsent same runtime hl heap hr hperm query hf
  | some pair =>
    obtain ⟨hmem, heq⟩ := rfind_some hf
    have heq' := hl.symm query pair.1 heq
    have hown := hrouting pair.1 pair.2 (hperm.mem_iff.mpr hmem)
    have hroute := routedLeaf_hashEq hown
      (routingHashEq_initial runtime pair.1 query (hl.hash_eq pair.1 query heq'))
    rw [rlookup, hf]
    exact persistentKeyGetPresent same runtime heap root query ⟨pair.1, pair.2⟩ hroute heq'

/-- The existing preservation proof supplies the routed tree for every API history. -/
theorem persistentKeyGetOfAPIHistory {K V : Type} (same : K → K → Bool)
    (runtime : HamtObjectIdRuntime K) (hl : KeyLaws runtime.objectid same)
    {dict : PersistentDict K V (round2.PTrie K V)} {reference : List (K × V)}
    (hr : round2.PRep (round2.hamtOps same runtime) same dict reference) (query : K) :
    persistentKeyGet (round2.hamtOps same runtime) dict query = rlookup same reference query := by
  have hrouted := persistentRoutedRep_of_transitions same runtime
    (persistentRoutedTransitions_constructed same runtime hl) hr
  obtain ⟨heap, root, pairs, hd, ht, hp, hrouting, _⟩ := hrouted
  have he : dict = ⟨.ok (heap, root)⟩ := by
    cases dict
    cases hd
    rfl
  subst dict
  exact persistentKeyGetOfRoutedTree same runtime hl heap ht hp hrouting query

/-- dictscov-dict-persistent-lookup. -/
theorem DictscovDictPersistentLookup_proven : JuliaLean.Proofs.base.dict.round2.PersistentLookupSemantics := by
  intro K V D same runtime hl dict reference hrep query default fallback
  exact round2.PersistentLookupSemantics_of_keyGet default fallback
    (persistentKeyGetOfAPIHistory same runtime hl hrep query)

/-- dictscov-dict-persistent-membership. -/
theorem DictscovDictPersistentMembership_proven : JuliaLean.Proofs.base.dict.round2.PersistentPairMembershipSemantics := by
  intro K V R same runtime hl dict reference hrep pair valueEq
  exact round2.PersistentPairMembershipSemantics_of_keyGet pair valueEq
    (persistentKeyGetOfAPIHistory same runtime hl hrep pair.1)

end JuliaLean.ChatGPT.Batch5.Group5

end

namespace JuliaLean.Proofs.base.dict

open JuliaLean.Registry

theorem DictDeleteLookup_nativeDomain_proven : round2.DictDeleteLookup :=
  round2.DictDeleteLookup_of_size_lt

theorem DictPopKeyContract_nativeDomain_proven : round2.DictPopKeyContract :=
  round2.DictPopKeyContract_of_size_lt

theorem DictPopAnyContract_nativeDomain_proven : round2.DictPopAnyContract :=
  round2.DictPopAnyContract_of_size_lt

theorem DictFilterContract_nativeDomain_proven : round2.DictFilterContract :=
  round2.DictFilterContract_of_size_lt

theorem ImmutableDictCollectionSemantics_nativeDomain_proven : round2.ImmutableDictCollectionSemantics :=
  round2.ImmutableDictCollectionSemantics_of_length_lt

/-- Every source-constructed PersistentDict update returns a dictionary whose lookup
returns the inserted value. The full success-and-lookup guarantee is retained.
Julia source: base/dict.jl:909-919,982-987,1023-1026; base/hamt.jl:195-213. -/
def PersistentSetGet : Prop :=
  ∀ (K V : Type) (egal : K → K → Bool)
    (runtime : JuliaLean.base.hamt.HamtObjectIdRuntime K),
    KeyLaws runtime.objectid egal →
    ∀ (d : JuliaLean.base.dict.PersistentDict K V (round2.PTrie K V)) (m : List (K × V)),
    round2.PRep (round2.hamtOps egal runtime) egal d m →
    ∀ (key : K) (value : V), ∃ updated,
      JuliaLean.base.dict.persistentSetTyped (round2.hamtOps egal runtime) d key value =
        some (.ok updated) ∧
      JuliaLean.base.dict.persistentGetindex (round2.hamtOps egal runtime) updated key = .ok value

theorem persistentSetGet_refuted : ¬ PersistentSetGet := by
  intro claim
  apply JuliaLean.ChatGPT.Batch4.Group1.DictsPersistentdictNothrow_refuted
  intro K V egal runtime lawful d pairs represented key value
  obtain ⟨updated, inserted, _⟩ := claim K V egal runtime lawful d pairs represented key value
  exact ⟨updated, inserted⟩

def entries : List Entry :=
  let retained := oldEntries.filter fun entry =>
    !(round2Entries.any fun replacement => replacement.id == entry.id)
  let combined := (retained.map fun entry =>
    if round1ApprovedIds.contains entry.id then entry
    else { entry with status := .todo, thm := none }) ++ round2Entries ++ [
  { id := "dicts-persistentdict-objectid-collision", juliaFile := "base/dict.jl",
    juliaFns := ["PersistentDict(::PersistentDict, key, val)", "KeyValue.set", "HAMT.insert!"],
    statement := "Setting a key on any PersistentDict succeeds and the key then maps to the value (it behaves like an IdDict).",
    source := "PersistentDict docstring base/dict.jl:945-946; base/dict.jl:909-919,982-987,1023-1026; base/hamt.jl:195-213",
    status := .refuted, prop := ``PersistentSetGet, thm := some ``persistentSetGet_refuted,
    issue := "#54740 (open, duplicate)",
    notes := "The installed HAMT singleton, path-copy and insertion models reject two distinct scalar keys with equal objectid. The full success-and-stored-lookup promise is preserved; the existing runtime evidence is unchanged." },
  { id := "dictscov-dict-l712-v2", juliaFile := "base/dict.jl",
    juliaFns := ["isempty(::Dict)", "length(::Dict)", "iterate(::Dict)"],
    statement := "On a valid dictionary with a nonwrapping iteration cursor, emptiness agrees with initial iteration and length equals the number of independently iterated pairs.",
    source := "base/dict.jl:706-713; doc/src/base/collections.md:81,84; base/abstractdict.jl:83-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.dict.Round3.DictReadOnlyObservations, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL712V2_proven }
]
  combined.map fun entry =>
    match entry.id with
    | "dicts-setindex-lookup" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsSetindexLookup_proven }
    | "dicts-float-keys-isequal" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsFloatKeysIsequal_proven }
    | "dictscov-dict-setindex" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictSetindex_proven }
    | "dictscov-dict-l374" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL374_proven }
    | "dictscov-dict-l359" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL359_proven }
    | "dictscov-dict-l327" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL327_proven }
    | "dictscov-dict-l347" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL347_proven }
    | "dictscov-dict-keyindex" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictKeyindex_proven }
    | "dictscov-dict-l241" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL241_proven }
    | "dicts-empty" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsEmpty_proven }
    | "dictscov-dict-l712" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL712_proven }
    | "dicts-sizehint-small" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsSizehintSmall_proven }
    | "dicts-sizehint-wrap-hang" => { entry with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsSizehintWrapHang_refuted, issue := "Searched JuliaLang/julia issues and PRs; no duplicate found; see bugs/dicts-sizehint-wrap-hang.yaml" }
    | "dicts-getbang-mutating-default" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsGetbangMutatingDefault_proven }
    | "dictscov-dict-getbang" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictGetbang_proven }
    | "dictscov-dict-l457" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL457_proven }
    | "dictscov-dict-l445" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL445_proven }
    | "dictscov-dict-l91" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL91_proven }
    | "dictscov-dict-l100" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL100_proven }
    | "dictscov-dict-l115" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL115_proven }
    | "dictscov-dict-l83" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL83_proven }
    | "dictscov-dict-construct" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictConstruct_proven }
    | "dictscov-dict-l135" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL135_proven }
    | "dictscov-dict-l136" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL136_proven }
    | "dictscov-dict-l137" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL137_proven }
    | "dictscov-dict-l123" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL123_proven }
    | "dictscov-dict-slots" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictSlots_proven }
    | "memsafety-dict-probes" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.MemsafetyDictProbes_proven }
    | "dictscov-show-limit-ellipsis" => { entry with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovShowLimitEllipsis_refuted, issue := "Searched JuliaLang/julia issues and PRs; no duplicate found; see bugs/dictscov-show-limit-ellipsis.yaml" }
    | "dicts-immutabledict-to-dict" => { entry with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsImmutabledictToDict_refuted, issue := "Searched JuliaLang/julia issues and PRs; matches #64139, #64137, #59957; see bugs/dicts-immutabledict-to-dict.yaml" }
    | "memsafety-dict-persistent-path" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.MemsafetyDictPersistentPath_proven }
    | "dictscov-dict-persistent-set" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictPersistentSet_proven }
    | "dicts-persistentdict-nothrow" => { entry with status := .refuted, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsPersistentdictNothrow_refuted, issue := "Searched JuliaLang/julia issues and PRs; matches #54740; see bugs/dicts-persistentdict-nothrow.yaml" }
    | "dictscov-dict-persistent-delete" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictPersistentDelete_proven }
    | "dictscov-dict-persistent-collection" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictPersistentCollection_proven }
    | "dictscov-dict-persistent-construct" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictPersistentConstruct_proven }
    | "dictscov-dict-immutable-similar" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictImmutableSimilar_proven }
    | "dicts-source-mergewith" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsSourceMergewith_proven }
    | "dictscov-dict-l735" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL735_proven }
    | "dictscov-dict-map-reduce" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictMapReduce_proven }
    | "dicts-ops-agree" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictsOpsAgree_proven }
    | "dictscov-dict-l712-v2" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group1.DictscovDictL712V2_proven }
    | "dictscov-dict-persistent-lookup" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch5.Group5.DictscovDictPersistentLookup_proven }
    | "dictscov-dict-persistent-membership" => { entry with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch5.Group5.DictscovDictPersistentMembership_proven }
    | "dicts-delete-lookup" => { entry with status := .proven, thm := some ``DictDeleteLookup_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dictscov-dict-l631" => { entry with status := .proven, thm := some ``DictDeleteLookup_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dicts-pop-key" => { entry with status := .proven, thm := some ``DictPopKeyContract_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dictscov-dict-pop" => { entry with status := .proven, thm := some ``DictPopKeyContract_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dictscov-dict-l615" => { entry with status := .proven, thm := some ``DictPopKeyContract_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dictscov-dict-l586" => { entry with status := .proven, thm := some ``DictPopKeyContract_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dictscov-dict-l580" => { entry with status := .proven, thm := some ``DictPopKeyContract_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dicts-pop-any" => { entry with status := .proven, thm := some ``DictPopAnyContract_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dicts-filter" => { entry with status := .proven, thm := some ``DictFilterContract_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | "dictscov-dict-immutable-iteration" => { entry with status := .proven, thm := some ``ImmutableDictCollectionSemantics_nativeDomain_proven, notes := "Native table and collection sizes respect the representable Int indexing domain." }
    | _ => entry

end JuliaLean.Proofs.base.dict
