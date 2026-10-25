import JuliaLean.Strings.Theory
import JuliaLean.Registry.Types

/-!
# Registered properties of the String model

Each property is a closed `Prop` that quantifies over strings, indices and
counts, stated as the docstring or an obvious invariant promises. Refutations
evaluate the model on one concrete counterexample; the same input is the
reproducer in `repro/<id>.jl`.
-/

namespace JuliaLean.Strings

/-- `r` succeeded with a value satisfying `p`. -/
def okSat {α : Type} (p : α → Bool) : SJl α → Bool
  | .ok a => p a
  | .error _ => false

theorem ok_ne {α : Type} (r : SJl α) (a : α) (p : α → Bool) (hp : p a = true)
    (hr : okSat p r = false) : r ≠ .ok a := by
  intro h; subst h; simp [okSat, hp] at hr

theorem of_okSat_eq {α : Type} [DecidableEq α] (r : SJl α) (a : α)
    (h : okSat (fun b => b == a) r = true) : r = .ok a := by
  cases r with
  | error e => simp [okSat] at h
  | ok b => simp [okSat] at h; rw [h]

/-- `collect(s::SubString)` by repeated `iterate(s, i)` from `firstindex(s) = 1`
(`base/strings/substring.jl:151-158`), keeping a thrown error. Each successful
step increases the state, so `ncodeunits(s) + 1` steps reach the end. -/
def subCollectFrom (ss : JSub) : Nat → JInt64 → SJl (List (UInt32 × JInt64))
  | 0, _ => .ok []
  | k + 1, i =>
    match subIterate ss i with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (c, j)) => (fun xs => (c, i) :: xs) <$> subCollectFrom ss k j

def subCollect (ss : JSub) : SJl (List (UInt32 × JInt64)) :=
  subCollectFrom ss (ss.ncu.val.toNat + 1) (ix 1)

/-! ## Proven properties -/

/-- Iterating any byte string from `firstindex(s)` terminates and yields exactly
one character at each valid index, in increasing order. -/
def IterateVisitsValid : Prop :=
  ∀ s : JStr, ∃ xs, IterTrace s (ix 1) xs ∧ xs.map (fun x => x.2.val) = validIndices s

theorem iterateVisitsValid_proven : IterateVisitsValid := by
  intro s
  have hs := ncu_small s
  exact trace_from s s.bytes.length (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega)
    (by rw [ix1]; omega) (fun h => by rw [ix1]; exact valid_one s (by rw [ix1] at h; omega))

theorem thisZ_range (s : JStr) (p : Int) (hp : 1 ≤ p) : 1 ≤ thisZ s p ∧ thisZ s p ≤ p := by
  rcases thisZ_cases s p with h | h | h | h <;> omega

theorem ncu1_val (s : JStr) : (ncodeunits s + ix 1).val = s.bytes.length + 1 := by
  have hs := ncu_small s
  rw [add_val _ _ (by rw [ncu_val]; simp; omega) (by rw [ncu_val]; simp; omega), ncu_val]; simp

/-- `thisind(s, thisind(s, i)) == thisind(s, i)` whenever `thisind(s, i)` returns. -/
def ThisindIdempotent : Prop :=
  ∀ (s : JStr) (i j : JInt64), thisind s i = .ok j → thisind s j = .ok j

theorem thisindIdempotent_proven : ThisindIdempotent := by
  intro s i j h
  have hs := ncu_small s
  by_cases h0 : i.val = 0
  · unfold thisind at h; rw [if_pos h0] at h; cases h
    unfold thisind; rw [if_pos ix0]
  by_cases hn : i.val = (ncodeunits s + ix 1).val
  · unfold thisind at h; rw [if_neg h0, if_pos hn] at h; cases h
    unfold thisind; rw [if_neg h0, if_pos hn]
  by_cases hm : 1 ≤ i.val ∧ i.val ≤ s.bytes.length
  · obtain ⟨j', hj', hv⟩ := thisind_mid s i hm.1 hm.2
    rw [hj'] at h; cases h
    have hr := thisZ_range s i.val hm.1
    obtain ⟨j'', hj'', hv''⟩ := thisind_mid s j (by omega) (by omega)
    rw [hv, thisZ_idem, ← hv] at hv''
    rw [hj'', show j'' = j from Subtype.ext hv'']
  · exfalso
    have hb : betweenI i (ix 1) (ncodeunits s) = false := by
      unfold betweenI; rw [ncu_val, ix1]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    unfold thisind at h; rw [if_neg h0, if_neg hn, hb] at h; cases h

/-- `prevind(s, nextind(s, i)) == i` for every valid index `i`. -/
def PrevindAfterNextind : Prop :=
  ∀ (s : JStr) (i : JInt64), isvalidAt s i = true → ∃ j, nextind s i = .ok j ∧ prevind s j = .ok i

theorem previndAfterNextind_proven : PrevindAfterNextind := by
  intro s i hv
  obtain ⟨h1, h2, h3⟩ := (isvalidAt_iff s i).1 hv
  obtain ⟨j, hj, hjv⟩ := nextind_mid s i h1 h2
  have hnv := nextZ_nextValid s i.val h1 h2
  rw [← hjv] at hnv
  obtain ⟨k, hk, hk'⟩ := previndN_one s j (by have := hnv.1; omega) hnv.2.1
  refine ⟨j, hj, ?_⟩
  rcases hk' with ⟨hj1, _⟩ | ⟨_, hpv⟩
  · exfalso; have := hnv.1; omega
  · have hp : PrevValid s j.val i.val := ⟨h1, hnv.1, ⟨h1, h2, h3⟩, fun r a b => hnv.2.2.1 r a b⟩
    have e := prevValid_unique s j.val k.val i.val hpv hp
    unfold prevind; rw [hk, show k = i from Subtype.ext e]

/-- `nextind(s, prevind(s, i)) == i` for every valid index `i ≥ 2` and for
`i = ncodeunits(s) + 1` when `s` is nonempty. -/
def NextindAfterPrevind : Prop :=
  ∀ (s : JStr) (i : JInt64), 2 ≤ i.val → (isvalidAt s i = true ∨ i.val = s.bytes.length + 1) →
    ∃ j, prevind s i = .ok j ∧ nextind s j = .ok i

theorem nextindAfterPrevind_proven : NextindAfterPrevind := by
  intro s i h2 hv
  have hi : i.val ≤ s.bytes.length + 1 := by
    rcases hv with hv | hv
    · have := ((isvalidAt_iff s i).1 hv).2.1; omega
    · omega
  have hiv : i.val ≤ s.bytes.length → validZ s i.val := by
    intro hle
    rcases hv with hv | hv
    · exact (isvalidAt_iff s i).1 hv
    · omega
  obtain ⟨k, hk, hk'⟩ := previndN_one s i (by omega) hi
  rcases hk' with ⟨hi1, _⟩ | ⟨_, hpv⟩
  · omega
  obtain ⟨k1, k2, k3⟩ := hpv.2.2.1
  obtain ⟨j, hj, hjv⟩ := nextind_mid s k k1 k2
  have hnv := nextZ_nextValid s k.val k1 k2
  have hnv' : NextValid s k.val i.val := ⟨hpv.2.1, hi, fun r a b => hpv.2.2.2 r a b, hiv⟩
  have e := nextValid_unique s k.val _ _ hnv hnv'
  refine ⟨k, hk, ?_⟩
  rw [hj, show j = i from Subtype.ext (by rw [hjv]; exact e)]

theorem stringN_ok {n : Nat} {fill : Unit → List UInt8} {out : JStr}
    (h : stringN n fill = .ok out) : out.bytes = fill () := by
  unfold stringN at h
  split at h
  · dsimp only at h
    split at h
    · cases h; rfl
    · cases h
  · cases h

theorem length_flatten_replicate (k : Nat) (l : List UInt8) :
    (List.replicate k l).flatten.length = k * l.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]; omega

/-- `repeat(s, r)` either throws or returns exactly `r * ncodeunits(s)` code units:
it never returns a string of a wrapped size. -/
def RepeatSize : Prop :=
  ∀ (s : JStr) (r : JInt64) (out : JStr), repeatStr s r = .ok out →
    out.bytes.length = r.val.toNat * s.bytes.length

theorem repeatSize_proven : RepeatSize := by
  intro s r out h
  unfold repeatStr at h
  by_cases hr : r.val < 0
  · rw [if_pos hr] at h; cases h
  rw [if_neg hr] at h
  have hu := u64_val r (by omega)
  simp only [] at h
  split at h
  · rename_i h0; cases h; rw [hu] at h0; simp [JStr.empty, h0]
  split at h
  · rename_i h1; cases h; rw [hu] at h1; simp [h1]
  split at h
  · rename_i hn; cases h; simp [JStr.empty, hn]
  split at h
  · cases h
  rw [stringN_ok h, length_flatten_replicate, hu]

/-! ## Refuted properties -/

/-- `"é"`: two code units, one character. -/
def strE : JStr := ⟨[0xc3, 0xa9], by decide⟩
def strA : JStr := ⟨[0x61], by decide⟩
def strAB : JStr := ⟨[0x61, 0x62], by decide⟩
def strABC : JStr := ⟨[0x61, 0x62, 0x63], by decide⟩
/-- `"é€"`. -/
def strEEuro : JStr := ⟨[0xc3, 0xa9, 0xe2, 0x82, 0xac], by decide⟩
abbrev intMax : JInt64 := ix (2 ^ 63 - 1)
abbrev intMin : JInt64 := ix (-2 ^ 63)

/-- `first(s, n)` is the first `n` characters of `s`, so the whole string once
`n ≥ length(s)`. -/
def FirstNAll : Prop :=
  ∀ (s : JStr) (n : JInt64), (length s).val ≤ n.val → firstN s n = .ok s

theorem firstNAll_refuted : ¬ FirstNAll := by
  intro h
  exact ok_ne _ strE (fun t => t.bytes == strE.bytes) (by decide) (by decide)
    (h strE intMax (by decide))

/-- `nextind(s, i, n)` for `n ≥ 1` and an in-bounds `i` returns an index after `i`. -/
def NextindNIncreasing : Prop :=
  ∀ (s : JStr) (i n j : JInt64), 0 ≤ i.val → i.val ≤ s.bytes.length → 1 ≤ n.val →
    nextindN s i n = .ok j → i.val < j.val

theorem nextindNIncreasing_refuted : ¬ NextindNIncreasing := by
  intro h
  have := h strA (ix 1) intMax intMin (by decide) (by decide) (by decide) rfl
  revert this; decide

/-- `chop(s; head, tail)` returns an empty string when asked to remove at least
`length(s)` characters. -/
def ChopTooMany : Prop :=
  ∀ (s : JStr) (h t : JInt64), 0 ≤ h.val → 0 ≤ t.val → (length s).val ≤ h.val + t.val →
    ∃ ss, chop s h t = .ok ss ∧ ss.ncu.val = 0

theorem chopTooMany_refuted : ¬ ChopTooMany := by
  intro h
  obtain ⟨ss, hss, _⟩ := h strAB intMax (ix 0) (by decide) (by decide) (by decide)
  exact ok_ne _ ss (fun _ => true) rfl (by decide) hss

/-- `Iterators.partition(s, n)` with `n ≥ length(s)` yields the whole of a
nonempty `s` as its first chunk. -/
def PartitionWhole : Prop :=
  ∀ (s : JStr) (n : JInt64), 1 ≤ s.bytes.length → (length s).val ≤ n.val →
    ∃ ss j, partitionIterate s n (ix 1) = .ok (some (ss, j)) ∧ ss.ncu.val = s.bytes.length

theorem partitionWhole_refuted : ¬ PartitionWhole := by
  intro h
  obtain ⟨ss, j, hss, _⟩ := h strEEuro intMax (by decide) (by decide)
  exact ok_ne _ (some (ss, j)) (fun _ => true) rfl (by decide) hss

/-- `lpad(s, n)` returns `s` unchanged when `n ≤ textwidth(s)`; `tw` is
`textwidth(s)`. -/
def LpadNoPad : Prop :=
  ∀ (s : JStr) (tw n : JInt64), 0 ≤ tw.val → n.val ≤ tw.val → lpad s tw n = .ok s

theorem lpadNoPad_refuted : ¬ LpadNoPad := by
  intro h
  exact ok_ne _ strA (fun t => t.bytes == strA.bytes) (by decide) (by decide)
    (h strA (ix 1) intMin (by decide) (by decide))

/-- `findnext(t, s, i)` returns a range `r` with `s[r] == t`. -/
def FindnextMatches : Prop :=
  ∀ (t s : JStr) (i : JInt64) (a b : Int), findnextStr t s i = .ok (some (a, b)) →
    getindexRange s (ix a) (ix b) = .ok t

/-- `"\xa9x"` and `"éx"`. -/
def strA9x : JStr := ⟨[0xa9, 0x78], by decide⟩
def strEx : JStr := ⟨[0xc3, 0xa9, 0x78], by decide⟩

theorem findnextMatches_refuted : ¬ FindnextMatches := by
  intro h
  have e : findnextStr strA9x strEx (ix 1) = .ok (some (2, 3)) :=
    of_okSat_eq _ _ (by decide)
  exact ok_ne _ strA9x (fun t => t.bytes == strA9x.bytes) (by decide) (by decide)
    (h strA9x strEx (ix 1) 2 3 e)

/-- `findprev(t, s, i)` returns the last occurrence `start:stop` with `stop ≤ i`
(`base/strings/search.jl:801-806`). So if `findnext(t, s, a)` reports an occurrence
`a:b` with `b ≤ i ≤ ncodeunits(s) + 1`, `findprev(t, s, i)` returns an occurrence
starting at `a` or later. -/
def FindprevLatest : Prop :=
  ∀ (t s : JStr) (i : JInt64) (a b : Int), 1 ≤ a → b ≤ i.val → i.val ≤ s.bytes.length + 1 →
    findnextStr t s (ix a) = .ok (some (a, b)) →
    ∃ a' b', findprevStr t s i = .ok (some (a', b')) ∧ a ≤ a'

theorem findprevLatest_refuted : ¬ FindprevLatest := by
  intro h
  obtain ⟨a', b', hp, hle⟩ := h JStr.empty strABC (ix 4) 4 3 (by decide) (by decide) (by decide) rfl
  have e : findprevStr JStr.empty strABC (ix 4) = .ok (some (0, -1)) := of_okSat_eq _ _ (by decide)
  rw [e] at hp
  cases hp
  omega

/-- `reverse(s)` reverses the characters: `collect(reverse(s)) == reverse(collect(s))`. -/
def ReverseChars : Prop := ∀ s : JStr, chars (reverse s) = (chars s).reverse

/-- `"\x82\xe2"`. -/
def str82E2 : JStr := ⟨[0x82, 0xe2], by decide⟩

theorem reverseChars_refuted : ¬ ReverseChars := by
  intro h
  have := h str82E2
  revert this; decide

/-- A SubString made by `raw_substring` can be iterated to the end without error
("the presence of truncated characters is safe and well-defined for `String`"),
yielding `length(ss)` characters. -/
def RawSubstringIterates : Prop :=
  ∀ (s : JStr) (f m : JInt64) (ss : JSub), rawSubstring s f m = .ok ss →
    ∃ xs, subCollect ss = .ok xs ∧ subLength ss = .ok (ix xs.length)

theorem rawSubstringIterates_refuted : ¬ RawSubstringIterates := by
  intro h
  obtain ⟨xs, hx, _⟩ := h strE (ix 1) (ix 1) ⟨strE, ix 0, ix 1⟩ rfl
  exact ok_ne _ xs (fun _ => true) rfl (by decide) hx

/-- `cmp(a::String, b::String)` agrees with the generic `AbstractString` `cmp`,
which compares the characters lexicographically. -/
def CmpAgreesGeneric : Prop := ∀ a b : JStr, cmp a b = cmpGeneric a b

/-- `"\xe2\xc0"` and `"\xe2\x82"`. -/
def strE2C0 : JStr := ⟨[0xe2, 0xc0], by decide⟩
def strE282 : JStr := ⟨[0xe2, 0x82], by decide⟩

theorem cmpAgreesGeneric_refuted : ¬ CmpAgreesGeneric := by
  intro h
  have := h strE2C0 strE282
  revert this; decide

end JuliaLean.Strings
