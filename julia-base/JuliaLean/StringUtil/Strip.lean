import JuliaLean.Strings.Length
import JuliaLean.Registry.Types

/-!
# `lstrip`, `rstrip`, `strip` and `chomp` on `String`

`base/strings/util.jl:371-489` (master `bbfa0ce4150`) for `s::String` and a character
predicate `f`, with the String model of `JuliaLean/Strings` (a `Char` is its 32-bit bit
pattern; strings are arbitrary byte sequences, valid UTF-8 or not).

`pairs(s::AbstractString)` is `Iterators.IterableStatePairs(s)` (`base/iterators.jl:1725`):
its key is the `iterate` state. So `lstrip` walks the string with `iterate` alone, starting at
`first(keys(s)) = 1` (`base/iterators.jl:1708-1712`, `base/strings/basic.jl:583`), and
`rstrip` walks `Iterators.reverse(s)` with `getindex` and `prevind`
(`base/strings/basic.jl:775`) from `last(keys(s)) = lastindex(s)` (`base/strings/basic.jl:584`,
`base/iterators.jl:1717-1721`); `Strings.rstrip` models the latter.

The loops below take the iteration function as a parameter: whnf of `iterate s i` on a
symbolic string does not terminate in practice (see `JuliaLean/Transcode/Bridge.lean`), so a
loop that matches on `iterate s i` directly has no usable equation lemmas.
-/

namespace JuliaLean.StringUtil.Strip

open JuliaLean JuliaLean.Strings

/-! ## Models -/

/-- The loop of `lstrip(f, s)`, `base/strings/util.jl:416-422`, for `s::String`:
`for (i::Int, c::AbstractChar) in pairs(s); !f(c) && return @inbounds SubString(s, i, e); end;
SubString(s, e+1, e)`, with `next = iterate(s, ·)`. The first argument bounds the remaining
iterations: every step increases the state and `iterate` returns `nothing` once it exceeds
`ncodeunits(s)`. -/
def lstripStrLoop (f : UInt32 → Bool) (s : JStr) (next : JInt64 → Option (UInt32 × JInt64))
    (e : JInt64) : Nat → JInt64 → SJl JSub
  | 0, _ => substring s (e + ix 1) e
  | k + 1, i =>
    match next i with
    | none => substring s (e + ix 1) e
    | some (c, i') => if !f c then substring s i e false else lstripStrLoop f s next e k i'

/-- `lstrip(f, s::String)`, `base/strings/util.jl:416-422`, with `e = lastindex(s)`. -/
def lstripStr (f : UInt32 → Bool) (s : JStr) : SJl JSub :=
  lstripStrLoop f s (iterate s) (lastindex s) (s.bytes.length + 1) (ix 1)

/-- `SubString(s::SubString, i::Int, j::Int)`, `base/strings/substring.jl:112-115`:
`@boundscheck i ≤ j && checkbounds(s, i:j)`, then `SubString(s.string, s.offset+i,
s.offset+j)`. `checked = false` models a call under `@inbounds`, which (through
`@propagate_inbounds`) also skips the bounds checks of the inner constructor. -/
def subSubstring (ss : JSub) (i j : JInt64) (checked : Bool := true) : SJl JSub :=
  if checked && decide (i.val ≤ j.val) && !(decide (1 ≤ i.val) && decide (j.val ≤ ss.ncu.val)) then
    .error boundsErr
  else substring ss.str (ss.offset + i) (ss.offset + j) checked

/-- The loop of `lstrip(f, s)`, `base/strings/util.jl:416-422`, for `s::SubString{String}`,
with `next = iterate(s, ·)` (`base/strings/substring.jl:151-158`). Bound as for
`lstripStrLoop`: each successful step increases the state. -/
def lstripSubLoop (f : UInt32 → Bool) (ss : JSub) (next : JInt64 → SJl (Option (UInt32 × JInt64)))
    (e : JInt64) : Nat → JInt64 → SJl JSub
  | 0, _ => subSubstring ss (e + ix 1) e
  | k + 1, i =>
    match next i with
    | .error err => .error err
    | .ok none => subSubstring ss (e + ix 1) e
    | .ok (some (c, i')) => if !f c then subSubstring ss i e false else lstripSubLoop f ss next e k i'

/-- `lstrip(f, s::SubString{String})`, `base/strings/util.jl:416-422`. `lastindex(s) =
thisind(s, ncodeunits(s))` is `_thisind_str` on the SubString (`base/strings/substring.jl:174,178`),
which reads the SubString's own code units `codeunit(s.string, s.offset + i)`
(`base/strings/substring.jl:146-149`): `JSub.view` for every SubString the constructors build
(`offset + ncodeunits ≤ ncodeunits(string)`). -/
def lstripSub (f : UInt32 → Bool) (ss : JSub) : SJl JSub :=
  lstripSubLoop f ss (subIterate ss) (lastindex ss.view) (ss.ncu.val.toNat + 1) (ix 1)

/-- `strip(f, s) = lstrip(f, rstrip(f, s))`, `base/strings/util.jl:489`, for `s::String`:
`rstrip` returns a `SubString{String}`, which `lstrip` then walks. -/
def strip (f : UInt32 → Bool) (s : JStr) : SJl JSub := do
  let r ← Strings.rstrip f s
  lstripSub f r

/-- `collect(ss)` for a SubString by repeated `next = iterate(ss, ·)` from `1`
(`base/strings/substring.jl:151-158`), keeping a thrown error. Bound: `ncodeunits(ss) + 1`. -/
def subCollectWith (next : JInt64 → SJl (Option (UInt32 × JInt64))) : Nat → JInt64 → SJl (List UInt32)
  | 0, _ => .ok []
  | k + 1, i =>
    match next i with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (c, j)) => (fun cs => c :: cs) <$> subCollectWith next k j

/-- The characters of a SubString, `collect(ss)`. -/
def subChars (ss : JSub) : SJl (List UInt32) :=
  subCollectWith (subIterate ss) (ss.ncu.val.toNat + 1) (ix 1)

/-! ## `collect(s)` without unfolding `iterate` -/

/-- `collectFrom` with the iteration function as a parameter (as `Transcode.collectWith`). -/
def collectIt (g : JInt64 → Option (UInt32 × JInt64)) : Nat → JInt64 → List (UInt32 × JInt64)
  | 0, _ => []
  | k + 1, i =>
    collectFrom.match_1 (motive := fun _ => List (UInt32 × JInt64)) (g i) (fun _ => [])
      (fun c j => (c, i) :: collectIt g k j)

section
attribute [local irreducible] iterate
set_option smartUnfolding false in
theorem collectFrom_eq_collectIt (s : JStr) (k : Nat) (i : JInt64) :
    collectFrom s k i = collectIt (iterate s) k i := rfl
end

/-! ## Iteration traces -/

/-- `i` is a valid index of `s` or `ncodeunits(s) + 1`. -/
def VE (s : JStr) (i : JInt64) : Prop :=
  1 ≤ i.val ∧ i.val ≤ s.bytes.length + 1 ∧ (i.val ≤ s.bytes.length → validZ s i.val)

theorem iter_step {s : JStr} {i j : JInt64} {c : UInt32} (hv : VE s i)
    (h : iterate s i = some (c, j)) : validZ s i.val ∧ NextValid s i.val j.val ∧ VE s j := by
  obtain ⟨h1, h2, h3⟩ := hv
  by_cases hn : i.val = s.bytes.length + 1
  · rw [iterate_end s i hn] at h; cases h
  have hvi := h3 (by omega)
  obtain ⟨c', j', h', hj⟩ := iterate_valid s i hvi
  rw [h'] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  have hjj : j.val = nextZ s i.val := by rw [← h.2, hj]
  have hnv := nextZ_nextValid s i.val h1 (by omega)
  rw [← hjj] at hnv
  exact ⟨hvi, hnv, by have := hnv.1; omega, hnv.2.1, hnv.2.2.2⟩

theorem iter_none {s : JStr} {i : JInt64} (hv : VE s i) (h : iterate s i = none) :
    i.val = s.bytes.length + 1 := by
  obtain ⟨h1, h2, h3⟩ := hv
  by_cases hn : i.val = s.bytes.length + 1
  · exact hn
  · obtain ⟨c, j, h', _⟩ := iterate_valid s i (h3 (by omega))
    rw [h] at h'; cases h'

theorem ve_one (s : JStr) : VE s (ix 1) := by
  have e1 := ix1
  refine ⟨by omega, by omega, fun h => ?_⟩
  rw [e1]; exact valid_one s (by omega)

theorem ve_of_valid {s : JStr} {i : JInt64} (hv : validZ s i.val) : VE s i :=
  ⟨hv.1, by have := hv.2.1; omega, fun _ => hv⟩

theorem collectIt_trace (s : JStr) (g : JInt64 → Option (UInt32 × JInt64))
    (hg : ∀ i, g i = iterate s i) : ∀ (k : Nat) (i : JInt64), VE s i →
    (s.bytes.length : Int) + 2 ≤ k + i.val → IterTrace s i (collectIt g k i) := by
  intro k
  induction k with
  | zero => intro i hv hk; have := hv.2.1; omega
  | succ k ih =>
    intro i hv hk
    cases hit : iterate s i with
    | none =>
      have h' : g i = none := by rw [hg]; exact hit
      simp only [collectIt, h']
      exact .done hit
    | some p =>
      obtain ⟨c, j⟩ := p
      have hs := iter_step hv hit
      have h' : g i = some (c, j) := by rw [hg]; exact hit
      simp only [collectIt, h']
      exact .step hit (ih j hs.2.2 (by have := hs.2.1.1; omega))

theorem collect_trace (s : JStr) : IterTrace s (ix 1) (collectPairs s) := by
  have e1 := ix1
  unfold collectPairs
  rw [collectFrom_eq_collectIt]
  exact collectIt_trace s (iterate s) (fun _ => rfl) _ _ (ve_one s) (by omega)

/-- The `(char, index)` pairs of iterating `s` from state `i` until the state is `stop`. -/
inductive Seg (s : JStr) (stop : JInt64) : JInt64 → List (UInt32 × JInt64) → Prop where
  | nil : Seg s stop stop []
  | cons {i c i' xs} : iterate s i = some (c, i') → Seg s stop i' xs → Seg s stop i ((c, i) :: xs)

theorem trace_cons_inv {s : JStr} {i : JInt64} {x : UInt32 × JInt64} {xs : List (UInt32 × JInt64)}
    (h : IterTrace s i (x :: xs)) : x.2 = i ∧ ∃ j, iterate s i = some (x.1, j) ∧ IterTrace s j xs := by
  cases h with
  | step hit htr => exact ⟨rfl, _, hit, htr⟩

theorem trace_nil_inv {s : JStr} {i : JInt64} (h : IterTrace s i []) : iterate s i = none := by
  cases h with
  | done h => exact h

theorem seg_cons_inv {s : JStr} {b i : JInt64} {x : UInt32 × JInt64} {xs : List (UInt32 × JInt64)}
    (h : Seg s b i (x :: xs)) : x.2 = i ∧ ∃ j, iterate s i = some (x.1, j) ∧ Seg s b j xs := by
  cases h with
  | cons hit hs => exact ⟨rfl, _, hit, hs⟩

theorem seg_nil_inv {s : JStr} {b i : JInt64} (h : Seg s b i []) : i = b := by
  cases h with
  | nil => rfl

theorem trace_split {s : JStr} (A : List (UInt32 × JInt64)) : ∀ {i : JInt64} (B : List (UInt32 × JInt64)),
    IterTrace s i (A ++ B) → ∃ j, Seg s j i A ∧ IterTrace s j B := by
  induction A with
  | nil => intro i B h; exact ⟨i, .nil, h⟩
  | cons x A ih =>
    intro i B h
    rw [List.cons_append] at h
    obtain ⟨hx, j, hit, htr⟩ := trace_cons_inv h
    obtain ⟨k, hs, ht⟩ := ih B htr
    obtain ⟨c, i0⟩ := x
    simp only at hx hit
    subst hx
    exact ⟨k, .cons hit hs, ht⟩

theorem seg_split {s : JStr} {b : JInt64} (A : List (UInt32 × JInt64)) :
    ∀ {i : JInt64} (B : List (UInt32 × JInt64)), Seg s b i (A ++ B) → ∃ m, Seg s m i A ∧ Seg s b m B := by
  induction A with
  | nil => intro i B h; exact ⟨i, .nil, h⟩
  | cons x A ih =>
    intro i B h
    rw [List.cons_append] at h
    obtain ⟨hx, j, hit, hs⟩ := seg_cons_inv h
    obtain ⟨m, h1, h2⟩ := ih B hs
    obtain ⟨c, i0⟩ := x
    simp only at hx hit
    subst hx
    exact ⟨m, .cons hit h1, h2⟩

/-- The last step of a segment. -/
theorem seg_last {s : JStr} {b i : JInt64} {A : List (UInt32 × JInt64)} {c : UInt32} {k : JInt64}
    (h : Seg s b i (A ++ [(c, k)])) : Seg s k i A ∧ iterate s k = some (c, b) := by
  obtain ⟨m, h1, h2⟩ := seg_split A [(c, k)] h
  obtain ⟨hx, j, hit, hnil⟩ := seg_cons_inv h2
  simp only at hx hit
  subst hx
  have hj := seg_nil_inv hnil
  rw [hj] at hit
  exact ⟨h1, hit⟩

theorem seg_ve {s : JStr} {b : JInt64} : ∀ {a : JInt64} {xs : List (UInt32 × JInt64)},
    Seg s b a xs → VE s a →
    VE s b ∧ a.val + xs.length ≤ b.val ∧
      (∀ x ∈ xs, validZ s x.2.val ∧ ∃ j, iterate s x.2 = some (x.1, j)) := by
  intro a xs h
  induction h with
  | nil => intro hv; exact ⟨hv, by simp, by simp⟩
  | @cons i c i' xs hit _ ih =>
    intro hv
    obtain ⟨h1, h2, h3⟩ := iter_step hv hit
    obtain ⟨b1, b2, b3⟩ := ih h3
    refine ⟨b1, by simp only [List.length_cons]; have := h2.1; omega, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨h1, _, hit⟩
    · exact b3 x hx

theorem trace_seg_end {s : JStr} : ∀ {i : JInt64} {xs : List (UInt32 × JInt64)},
    IterTrace s i xs → VE s i → Seg s (ncodeunits s + ix 1) i xs := by
  intro i xs h
  induction h with
  | @done i hn =>
    intro hv
    have e : i = ncodeunits s + ix 1 := Subtype.ext (by rw [ncu1_val]; exact iter_none hv hn)
    rw [e]; exact .nil
  | step hit _ ih => intro hv; exact .cons hit (ih (iter_step hv hit).2.2)

/-- The state after a trace prefix: the index of the rest, or `ncodeunits(s) + 1`. -/
theorem trace_head {s : JStr} {j : JInt64} {B : List (UInt32 × JInt64)} (h : IterTrace s j B)
    (hv : VE s j) : j.val = (B.head?.map (·.2.val)).getD (s.bytes.length + 1) := by
  cases B with
  | nil =>
    show j.val = (s.bytes.length : Int) + 1
    exact iter_none hv (trace_nil_inv h)
  | cons x B =>
    obtain ⟨hx, _⟩ := trace_cons_inv h
    show j.val = x.2.val
    rw [hx]

/-! ## SubString iteration -/

theorem subIterate_end (ss : JSub) (p : JInt64) (hm : 0 ≤ ss.ncu.val) (hm2 : ss.ncu.val < 2 ^ 62)
    (hp : p.val = ss.ncu.val + 1) : subIterate ss p = .ok none := by
  have e1 := ix1
  have c1 : p.val = (ss.ncu + ix 1).val := by rw [add_val _ _ (by omega) (by omega)]; omega
  unfold subIterate
  rw [if_pos c1]

theorem subIterate_step (ss : JSub) (p a a' : JInt64) (c : UInt32) (hm : 0 ≤ ss.ncu.val)
    (hm2 : ss.ncu.val < 2 ^ 62) (hp1 : 1 ≤ p.val) (hpm : p.val ≤ ss.ncu.val)
    (eop : ss.offset + p = a) (hit : iterate ss.str a = some (c, a')) :
    subIterate ss p = .ok (some (c, a' - ss.offset)) := by
  have e1 := ix1
  have c1 : ¬ p.val = (ss.ncu + ix 1).val := by rw [add_val _ _ (by omega) (by omega)]; omega
  have c2 : (!(decide (1 ≤ p.val) && decide (p.val ≤ ss.ncu.val))) = false := by
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]; omega
  unfold subIterate
  rw [if_neg c1, c2, if_neg Bool.false_ne_true, eop, hit]
  all_goals rfl

/-- Iterating a SubString that starts and ends at character boundaries of its parent. -/
theorem subCollectWith_seg (s : JStr) (o m b : JInt64) (next : JInt64 → SJl (Option (UInt32 × JInt64)))
    (hnext : ∀ p, next p = subIterate ⟨s, o, m⟩ p) (ho : 0 ≤ o.val) (hm : 0 ≤ m.val)
    (hb : b.val = o.val + m.val + 1) :
    ∀ {a : JInt64} {xs : List (UInt32 × JInt64)}, Seg s b a xs → VE s a →
      ∀ (k : Nat) (p : JInt64), a.val = o.val + p.val → 1 ≤ p.val → xs.length < k →
        subCollectWith next k p = .ok (xs.map (·.1)) := by
  have hs := ncu_small s
  intro a xs h
  induction h with
  | nil =>
    intro hv k p hp _ hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hbn := hv.2.1
    have hstep : next p = .ok none := by
      rw [hnext]; exact subIterate_end ⟨s, o, m⟩ p hm (by show m.val < 2 ^ 62; omega)
        (by show p.val = m.val + 1; omega)
    simp only [subCollectWith, hstep]
    rfl
  | @cons i c i' xs hit hseg ih =>
    intro hv k p hp hp1 hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨hvi, hnv, hve'⟩ := iter_step hv hit
    have hb2 := (seg_ve hseg hve').2.1
    have hbn := (seg_ve hseg hve').1.2.1
    have hi' := hnv.1
    have hlt : i.val < b.val := by omega
    have eop : o + p = i := Subtype.ext (by rw [add_val _ _ (by omega) (by omega)]; omega)
    have hstep : next p = .ok (some (c, i' - o)) := by
      rw [hnext]
      exact subIterate_step ⟨s, o, m⟩ p i i' c hm (by show m.val < 2 ^ 62; omega) hp1
        (by show p.val ≤ m.val; omega) eop hit
    have e' : i'.val = o.val + (i' - o).val := by
      rw [sub_val _ _ (by omega) (by omega)]; omega
    have hrec := ih hve' k (i' - o) e' (by rw [sub_val _ _ (by omega) (by omega)]; omega)
      (by simp only [List.length_cons] at hk; omega)
    simp only [subCollectWith, hstep, hrec]
    rfl

theorem subChars_seg (s : JStr) (o m b a : JInt64) (xs : List (UInt32 × JInt64))
    (hseg : Seg s b a xs) (hv : VE s a) (ho : 0 ≤ o.val) (hm : 0 ≤ m.val)
    (ha : a.val = o.val + 1) (hb : b.val = o.val + m.val + 1) :
    subChars ⟨s, o, m⟩ = .ok (xs.map (·.1)) := by
  have e1 := ix1
  have hl := (seg_ve hseg hv).2.1
  exact subCollectWith_seg s o m b _ (fun _ => rfl) ho hm hb hseg hv (m.val.toNat + 1) (ix 1)
    (by omega) (by omega) (by omega)

theorem subChars_empty (s : JStr) (o m : JInt64) (ho : o.val = 0) (hm : m.val = 0) :
    subChars ⟨s, o, m⟩ = .ok [] :=
  subChars_seg s o m (ix 1) (ix 1) [] .nil (ve_one s) (by omega) (by omega)
    (by have := ix1; omega) (by have := ix1; omega)

/-! ## Index facts -/

/-- `thisind(s, p)` is the last valid index at or before `p`. -/
theorem thisZ_last (s : JStr) (p : Int) (h1 : 1 ≤ p) (h2 : p ≤ s.bytes.length) :
    validZ s (thisZ s p) ∧ ∀ r, thisZ s p < r → r ≤ p → ¬ validZ s r := by
  have hr := thisZ_range s p h1
  refine ⟨⟨hr.1, by omega, thisZ_idem s p⟩, fun r hr1 hr2 hv => ?_⟩
  have hc := leadZ_covers s p h1 h2 (by omega)
  have := leadZ_inside s (thisZ s p) r hc.2.2.1 ⟨hc.1, hc.2.1⟩ hr1 (by omega)
  have := hv.2.2; omega

/-- `lastindex s` with the `thisind` result as an argument: same height and matcher as
`lastindex`, so the kernel compares the two structurally instead of evaluating `thisind`. -/
def liAt (s : JStr) (t : SJl JInt64) : JInt64 :=
  let _u := thisind s (ncodeunits s)
  isvalidAt.match_1 (fun _ => JInt64) t (fun j => j) (fun _ => ix 0)

theorem lastindex_of (s : JStr) (j : JInt64) (hj : thisind s (ncodeunits s) = .ok j) :
    lastindex s = j := by
  have h1 : liAt s (thisind s (ncodeunits s)) = j := by rw [hj]; rfl
  exact h1

theorem lastindex_spec (s : JStr) (h : 1 ≤ s.bytes.length) :
    validZ s (lastindex s).val ∧ ∀ r, (lastindex s).val < r → r ≤ s.bytes.length → ¬ validZ s r := by
  obtain ⟨j, hj, hjv⟩ := thisind_mid s (ncodeunits s) (by rw [ncu_val]; omega)
    (by rw [ncu_val]; exact Int.le_refl _)
  rw [lastindex_of s j hj, hjv, ncu_val]
  exact thisZ_last s _ (by omega) (Int.le_refl _)

theorem lastindex_zero (s : JStr) (h : s.bytes.length = 0) : (lastindex s).val = 0 := by
  have e : (ncodeunits s).val = 0 := by rw [ncu_val, h]; rfl
  have ht : thisind s (ncodeunits s) = .ok (ix 0) := by unfold thisind; rw [if_pos e]
  rw [lastindex_of s _ ht]
  exact ix0

theorem lastindex_range (s : JStr) : 0 ≤ (lastindex s).val ∧ (lastindex s).val ≤ s.bytes.length := by
  by_cases h : s.bytes.length = 0
  · rw [lastindex_zero s h]; omega
  · have := (lastindex_spec s (by omega)).1; exact ⟨by have := this.1; omega, this.2.1⟩

theorem eq_lastindex (s : JStr) (i : JInt64) (hv : validZ s i.val)
    (hgap : ∀ r, i.val < r → r ≤ s.bytes.length → ¬ validZ s r) : lastindex s = i := by
  have hn : 1 ≤ s.bytes.length := by have := hv.1; have := hv.2.1; omega
  obtain ⟨hl, hlg⟩ := lastindex_spec s hn
  apply Subtype.ext
  rcases Int.lt_trichotomy (lastindex s).val i.val with h | h | h
  · exact absurd hv (hlg _ h hv.2.1)
  · exact h
  · exact absurd hl (hgap _ h hl.2.1)

theorem nextind_to (s : JStr) (i j : JInt64) (hv : validZ s i.val) (hn : NextValid s i.val j.val) :
    nextind s i = .ok j := by
  obtain ⟨j', hj', hv'⟩ := nextind_mid s i hv.1 hv.2.1
  have h1 := nextZ_nextValid s i.val hv.1 hv.2.1
  rw [← hv'] at h1
  have e := nextValid_unique s i.val _ _ h1 hn
  rw [hj', Subtype.ext e]

theorem prevind_to (s : JStr) (i j : JInt64) (hi : i.val ≤ s.bytes.length + 1)
    (hp : PrevValid s i.val j.val) : prevind s i = .ok j := by
  obtain ⟨k, hk, hk'⟩ := previndN_one s i (by have := hp.1; have := hp.2.1; omega) hi
  rcases hk' with ⟨hi1, _⟩ | ⟨_, hpv⟩
  · have := hp.1; have := hp.2.1; omega
  · unfold prevind; rw [hk, Subtype.ext (prevValid_unique s i.val _ _ hpv hp)]

theorem prevind_first (s : JStr) (i : JInt64) (hi : i.val = 1) :
    ∃ p, prevind s i = .ok p ∧ p.val = 0 := by
  obtain ⟨k, hk, hk'⟩ := previndN_one s i (by omega) (by omega)
  rcases hk' with ⟨_, h0⟩ | ⟨h2, _⟩
  · exact ⟨k, hk, h0⟩
  · omega

theorem nextValid_prevValid (s : JStr) (i j : Int) (hv : validZ s i) (hn : NextValid s i j) :
    PrevValid s j i :=
  ⟨hv.1, hn.1, hv, fun r a b => hn.2.2.1 r a b⟩

theorem prevValid_nextValid (s : JStr) (i j : Int) (hp : PrevValid s j i)
    (hj : j ≤ s.bytes.length + 1) (hjv : j ≤ s.bytes.length → validZ s j) : NextValid s i j :=
  ⟨hp.2.1, hj, fun r a b => hp.2.2.2 r a b, hjv⟩

theorem substring_empty (s : JStr) (i j : JInt64) (c : Bool) (h : j.val < i.val) :
    substring s i j c = .ok ⟨s, ix 0, ix 0⟩ := by
  have hd : decide (i.val ≤ j.val) = false := decide_eq_false (by omega)
  unfold substring
  rw [hd]
  rfl

theorem substring_ok (s : JStr) (i j j' : JInt64) (c : Bool) (hi : validZ s i.val)
    (hj : validZ s j.val) (hij : i.val ≤ j.val) (hn : nextind s j = .ok j') :
    substring s i j c = .ok ⟨s, i - ix 1, j' - i⟩ := by
  have c1 : (!decide (i.val ≤ j.val)) = false := by simp only [Bool.not_eq_false', decide_eq_true_eq]; omega
  have c2 : (!(decide (1 ≤ i.val) && decide (j.val ≤ (ncodeunits s).val))) = false := by
    rw [ncu_val]; simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hi.1, hj.2.1⟩
  have hvi : (!isvalidAt s i) = false := by rw [(isvalidAt_iff s i).2 hi]; rfl
  have hvj : (!isvalidAt s j) = false := by rw [(isvalidAt_iff s j).2 hj]; rfl
  unfold substring
  rw [c1, if_neg Bool.false_ne_true]
  cases c
  · simp only [Bool.not_false, ↓reduceIte, hn]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, c2, hvi, hvj, hn]

theorem jsub_ok_mk {s : JStr} {o1 m1 o2 m2 : JInt64} (h2 : o1.val = o2.val) (h3 : m1.val = m2.val) :
    (.ok ⟨s, o1, m1⟩ : SJl JSub) = .ok ⟨s, o2, m2⟩ := by
  rw [Subtype.ext h2, Subtype.ext h3]

theorem subSubstring_unchecked (s : JStr) (o m i j : JInt64) :
    subSubstring ⟨s, o, m⟩ i j false = substring s (o + i) (o + j) false := rfl

theorem subSubstring_gt (s : JStr) (o m i j : JInt64) (h : j.val < i.val) :
    subSubstring ⟨s, o, m⟩ i j = substring s (o + i) (o + j) := by
  have hd : decide (i.val ≤ j.val) = false := decide_eq_false (by omega)
  unfold subSubstring
  rw [hd, Bool.and_false, Bool.false_and, if_neg Bool.false_ne_true]
  all_goals rfl

/-! ## `lstrip` -/

/-- `ss` is `s` without its maximal leading run of characters satisfying `f`: the characters
of `s` split as `pre ++ post`, every character of `pre` satisfies `f`, iterating `ss` yields
exactly the characters of `post`, and `ss` is empty or starts at the first index of `post`
(whose character fails `f`) and ends at the end of `s`. -/
def LstripResult (f : UInt32 → Bool) (s : JStr) (ss : JSub) : Prop :=
  ∃ pre post, ss.str = s ∧ collectPairs s = pre ++ post ∧ (∀ x ∈ pre, f x.1 = true) ∧
    subChars ss = .ok (post.map (·.1)) ∧
    ((post = [] ∧ ss.offset.val = 0 ∧ ss.ncu.val = 0) ∨
     (∃ c i rest, post = (c, i) :: rest ∧ f c = false ∧ ss.offset.val = i.val - 1 ∧
        ss.offset.val + ss.ncu.val = s.bytes.length))

/-- For every byte string `s` and predicate `f`, `lstrip(f, s)` returns the SubString of `s`
from its first character failing `f` to its end. -/
def LstripChars : Prop :=
  ∀ (f : UInt32 → Bool) (s : JStr), ∃ ss, lstripStr f s = .ok ss ∧ LstripResult f s ss

theorem lstripStrLoop_spec (f : UInt32 → Bool) (s : JStr) (next : JInt64 → Option (UInt32 × JInt64))
    (hnext : ∀ i, next i = iterate s i) :
    ∀ (k : Nat) (i : JInt64) (pre post : List (UInt32 × JInt64)),
      Seg s (ncodeunits s + ix 1) i post → VE s i → collectPairs s = pre ++ post →
      (∀ x ∈ pre, f x.1 = true) → post.length < k →
      ∃ ss, lstripStrLoop f s next (lastindex s) k i = .ok ss ∧ LstripResult f s ss := by
  have hs := ncu_small s
  have hE := ncu1_val s
  have hl := lastindex_range s
  have hlspec := lastindex_spec s
  generalize lastindex s = L at hl hlspec ⊢
  have e1 := ix1
  have he1 : (L + ix 1).val = L.val + 1 := add_val _ _ (by omega) (by omega)
  have hempty : substring s (L + ix 1) L = .ok ⟨s, ix 0, ix 0⟩ :=
    substring_empty s _ _ true (by omega)
  intro k
  induction k with
  | zero => intro i pre post _ _ _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    intro i pre post hseg hv hcp hpre hk
    cases post with
    | nil =>
      have hi := seg_nil_inv hseg
      have hit : iterate s i = none := iterate_end s i (by rw [hi, hE])
      have hn : next i = none := by rw [hnext]; exact hit
      have hloop : lstripStrLoop f s next L (k + 1) i = .ok ⟨s, ix 0, ix 0⟩ := by
        simp only [lstripStrLoop, hn]; exact hempty
      refine ⟨_, hloop, pre, [], rfl, by simpa using hcp, hpre, subChars_empty s _ _ rfl rfl,
        Or.inl ⟨rfl, rfl, rfl⟩⟩
    | cons x rest =>
      obtain ⟨hx, i', hit, hseg'⟩ := seg_cons_inv hseg
      obtain ⟨c, i0⟩ := x
      simp only at hx hit
      subst hx
      obtain ⟨hvi, hnv, hve'⟩ := iter_step hv hit
      have hn : next i0 = some (c, i') := by rw [hnext]; exact hit
      by_cases hfc : f c = false
      · have hn1 : 1 ≤ s.bytes.length := by have := hvi.2.1; have := hvi.1; omega
        obtain ⟨hlv, hlg⟩ := hlspec hn1
        have hle : i0.val ≤ L.val := by
          by_cases hc : i0.val ≤ L.val
          · exact hc
          · exact absurd hvi (hlg _ (by omega) hvi.2.1)
        have hnl : nextind s L = .ok (ncodeunits s + ix 1) :=
          nextind_to s _ _ hlv ⟨by omega, by omega, fun r h1 h2 => hlg r h1 (by omega), fun h => by omega⟩
        have hsub := substring_ok s i0 L _ false hvi hlv hle hnl
        have hloop : lstripStrLoop f s next L (k + 1) i0 =
            .ok ⟨s, i0 - ix 1, ncodeunits s + ix 1 - i0⟩ := by
          simp only [lstripStrLoop, hn, hfc, Bool.not_false, ↓reduceIte]; exact hsub
        have hi1 := hvi.1
        have hin := hvi.2.1
        have eo : (i0 - ix 1).val = i0.val - 1 := by rw [sub_val _ _ (by omega) (by omega)]; omega
        obtain ⟨m, hmd⟩ : ∃ m, ncodeunits s + ix 1 - i0 = m := ⟨_, rfl⟩
        have en : m.val = s.bytes.length + 1 - i0.val := by
          rw [← hmd, sub_val _ _ (by omega) (by omega), hE]
        rw [hmd] at hloop
        obtain ⟨E, hEd⟩ : ∃ E, ncodeunits s + ix 1 = E := ⟨_, rfl⟩
        rw [hEd] at hseg hE
        refine ⟨_, hloop, pre, (c, i0) :: rest, rfl, hcp, hpre, ?_,
          Or.inr ⟨c, i0, rest, rfl, hfc, eo, ?_⟩⟩
        · exact subChars_seg s (i0 - ix 1) m E i0 _ hseg hv (by omega) (by omega) (by omega)
            (by omega)
        · show (i0 - ix 1).val + m.val = _
          rw [eo, en]; omega
      · have hft : f c = true := by simpa using hfc
        have hpre' : ∀ x ∈ pre ++ [(c, i0)], f x.1 = true := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hpre x hx
          · rw [List.mem_singleton] at hx; rw [hx]; exact hft
        have hcp' : collectPairs s = (pre ++ [(c, i0)]) ++ rest := by simp [hcp]
        have hk' : rest.length < k := by simp only [List.length_cons] at hk; omega
        obtain ⟨ss, h1, h2⟩ := ih i' (pre ++ [(c, i0)]) rest hseg' hve' hcp' hpre' hk'
        refine ⟨ss, ?_, h2⟩
        simp only [lstripStrLoop, hn, hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact h1

theorem lstripChars_proven : LstripChars := by
  intro f s
  have tr := collect_trace s
  have hseg := trace_seg_end tr (ve_one s)
  have hl := (seg_ve hseg (ve_one s)).2.1
  have e1 := ix1
  have hE := ncu1_val s
  have hk : (collectPairs s).length < s.bytes.length + 1 := by omega
  have hcp : collectPairs s = [] ++ collectPairs s := (List.nil_append _).symm
  have hpre : ∀ x ∈ ([] : List (UInt32 × JInt64)), f x.1 = true := fun x hx => by cases hx
  obtain ⟨ss, h1, h2⟩ := lstripStrLoop_spec f s (iterate s) (fun _ => rfl) (s.bytes.length + 1) (ix 1)
    [] (collectPairs s) hseg (ve_one s) hcp hpre hk
  refine ⟨ss, ?_, h2⟩
  unfold lstripStr
  exact h1

/-! ## `rstrip` -/

theorem getindex_of_iterate (s : JStr) (i j : JInt64) (c : UInt32) (hv : validZ s i.val)
    (h : iterate s i = some (c, j)) : getindex s i = .ok c := by
  obtain ⟨h1, h2, h3⟩ := hv
  rw [iterate_eq s i h1 h2] at h
  have hcu : codeunit s i = .ok (cu s i) := by
    unfold codeunit; rw [if_pos ⟨h1, by rw [ncu_val]; exact h2⟩]
  unfold getindex
  rw [hcu]
  change (if !between (cu s i) 0x80 0xf7 then pure ((cu s i).toUInt32 <<< 24)
    else getindexContinued s i ((cu s i).toUInt32 <<< 24)) = .ok c
  by_cases hb : (!between (cu s i) 0x80 0xf7) = true
  · rw [if_pos hb] at h ⊢
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  · rw [if_neg hb] at h ⊢
    unfold getindexContinued
    by_cases hu : (cu s i).toUInt32 <<< 24 < 0xc0000000
    · rw [if_pos hu, if_pos ((isvalidAt_iff s i).2 ⟨h1, h2, h3⟩)]
      unfold iterateContinued at h
      rw [if_pos hu] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
    · rw [if_neg hu]
      simp only [Option.some.injEq] at h
      rw [h]

/-- `ss` is `s` without its maximal trailing run of characters satisfying `f`: the characters
of `s` split as `pre ++ post`, every character of `post` satisfies `f`, iterating `ss` yields
exactly the characters of `pre`, and `ss` starts at the beginning of `s` and is empty or ends
right before the first index of `post` (or at the end of `s`), the last character of `pre`
failing `f`. -/
def RstripResult (f : UInt32 → Bool) (s : JStr) (ss : JSub) : Prop :=
  ∃ pre post, ss.str = s ∧ collectPairs s = pre ++ post ∧ (∀ x ∈ post, f x.1 = true) ∧
    subChars ss = .ok (pre.map (·.1)) ∧ ss.offset.val = 0 ∧
    ((pre = [] ∧ ss.ncu.val = 0) ∨
     (∃ c i, pre.getLast? = some (c, i) ∧ f c = false ∧
        ss.ncu.val + 1 = (post.head?.map (·.2.val)).getD (s.bytes.length + 1)))

/-- For every byte string `s` and predicate `f`, `rstrip(f, s)` returns the SubString of `s`
from its start to its last character failing `f`. -/
def RstripChars : Prop :=
  ∀ (f : UInt32 → Bool) (s : JStr), ∃ ss, Strings.rstrip f s = .ok ss ∧ RstripResult f s ss

theorem nil_or_snoc {α : Type} (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨L, b, by rw [h, List.concat_eq_append]⟩

theorem rstripLoop_spec (f : UInt32 → Bool) (s : JStr) :
    ∀ (k : Nat) (i j : JInt64) (A B : List (UInt32 × JInt64)),
      Seg s j (ix 1) A → IterTrace s j B → collectPairs s = A ++ B → (∀ x ∈ B, f x.1 = true) →
      A.length ≤ k → ((A = [] ∧ i.val = 0) ∨ (∃ A' c, A = A' ++ [(c, i)])) →
      ∃ ss, Strings.rstripLoop f s k i = .ok ss ∧ RstripResult f s ss := by
  have hs := ncu_small s
  have e1 := ix1
  have hempty : substring s (ix 1) (ix 0) = .ok ⟨s, ix 0, ix 0⟩ := substring_empty s _ _ true (by simp)
  have hres0 : ∀ B : List (UInt32 × JInt64), collectPairs s = [] ++ B → (∀ x ∈ B, f x.1 = true) →
      RstripResult f s ⟨s, ix 0, ix 0⟩ := fun B hcp hB =>
    ⟨[], B, rfl, hcp, hB, subChars_empty s _ _ rfl rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  intro k
  induction k with
  | zero =>
    intro i j A B hseg htr hcp hB hk hi
    rcases hi with ⟨rfl, hi0⟩ | ⟨A', c, rfl⟩
    · refine ⟨_, ?_, hres0 B hcp hB⟩
      simp only [Strings.rstripLoop]; exact hempty
    · simp at hk
  | succ k ih =>
    intro i j A B hseg htr hcp hB hk hi
    rcases hi with ⟨rfl, hi0⟩ | ⟨A', c, rfl⟩
    · refine ⟨_, ?_, hres0 B hcp hB⟩
      have h0 : i.val < 1 := by omega
      simp only [Strings.rstripLoop, h0, ↓reduceIte]; exact hempty
    · obtain ⟨hsA', hit⟩ := seg_last hseg
      have hvi0 : VE s i := (seg_ve hsA' (ve_one s)).1
      obtain ⟨hvi, hnv, hvj⟩ := iter_step hvi0 hit
      have hget := getindex_of_iterate s i j c hvi hit
      have hi1 : ¬ i.val < 1 := by have := hvi.1; omega
      have hnext := nextind_to s i j hvi hnv
      obtain ⟨p, hp, hprel⟩ : ∃ p, prevind s i = .ok p ∧
          ((A' = [] ∧ p.val = 0) ∨ ∃ A'' c', A' = A'' ++ [(c', p)]) := by
        rcases nil_or_snoc A' with rfl | ⟨A'', ⟨c', i''⟩, rfl⟩
        · have hi' := seg_nil_inv hsA'
          obtain ⟨p, hp, hp0⟩ := prevind_first s i (by rw [← hi']; exact e1)
          exact ⟨p, hp, Or.inl ⟨rfl, hp0⟩⟩
        · obtain ⟨hs1, hit'⟩ := seg_last hsA'
          have hv'' : VE s i'' := (seg_ve hs1 (ve_one s)).1
          obtain ⟨hvi'', hnv'', _⟩ := iter_step hv'' hit'
          exact ⟨i'', prevind_to s i i'' (by have := hvi0.2.1; omega)
            (nextValid_prevValid s _ _ hvi'' hnv''), Or.inr ⟨A'', c', rfl⟩⟩
      by_cases hfc : f c = false
      · have hv1 : validZ s (ix 1).val := by rw [e1]; exact valid_one s (by have := hvi.2.1; have := hvi.1; omega)
        have hsub := substring_ok s (ix 1) i j false hv1 hvi (by rw [e1]; exact hvi.1) hnext
        have hloop : Strings.rstripLoop f s (k + 1) i = .ok ⟨s, ix 1 - ix 1, j - ix 1⟩ := by
          simp only [Strings.rstripLoop, hi1, hp, hget, hfc, Bool.not_false, ↓reduceIte]
          exact hsub
        have hj1 : 2 ≤ j.val := by have := hnv.1; have := hvi.1; omega
        have hjn := hvj.2.1
        have ej : (j - ix 1).val = j.val - 1 := by rw [sub_val _ _ (by omega) (by omega)]; omega
        have eo : (ix 1 - ix 1).val = 0 := rfl
        refine ⟨_, hloop, A' ++ [(c, i)], B, rfl, hcp, hB, ?_, eo, Or.inr ⟨c, i, by simp, hfc, ?_⟩⟩
        · exact subChars_seg s _ _ _ _ _ hseg (ve_one s) (by omega) (by omega) (by omega) (by omega)
        · show (j - ix 1).val + 1 = _
          rw [ej, ← trace_head htr hvj]; omega
      · have hft : f c = true := by simpa using hfc
        have htr' : IterTrace s i ((c, i) :: B) := .step hit htr
        have hcp' : collectPairs s = A' ++ (c, i) :: B := by simp [hcp]
        have hB' : ∀ x ∈ (c, i) :: B, f x.1 = true := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hft
          · exact hB x hx
        have hk' : A'.length ≤ k := by simp only [List.length_append, List.length_singleton] at hk; omega
        obtain ⟨ss, h1, h2⟩ := ih p i A' ((c, i) :: B) hsA' htr' hcp' hB' hk' hprel
        refine ⟨ss, ?_, h2⟩
        simp only [Strings.rstripLoop, hi1, hp, hget, hft, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
        exact h1

theorem rstripChars_proven : RstripChars := by
  intro f s
  have hs := ncu_small s
  have e1 := ix1
  have hE := ncu1_val s
  have tr := collect_trace s
  have hseg := trace_seg_end tr (ve_one s)
  have hl := (seg_ve hseg (ve_one s)).2.1
  have hend : IterTrace s (ncodeunits s + ix 1) [] := .done (iterate_end s _ hE)
  have hi : (collectPairs s = [] ∧ (lastindex s).val = 0) ∨
      (∃ A' c, collectPairs s = A' ++ [(c, lastindex s)]) := by
    rcases nil_or_snoc (collectPairs s) with h | ⟨A', ⟨c, i⟩, h⟩
    · left
      refine ⟨h, lastindex_zero s ?_⟩
      rw [h] at hseg
      have := congrArg Subtype.val (seg_nil_inv hseg)
      omega
    · right
      refine ⟨A', c, ?_⟩
      rw [h] at hseg
      obtain ⟨hs1, hit⟩ := seg_last hseg
      have hvm : VE s i := (seg_ve hs1 (ve_one s)).1
      obtain ⟨hvi, hnv, _⟩ := iter_step hvm hit
      rw [eq_lastindex s i hvi (fun r h1 h2 => hnv.2.2.1 r h1 (by omega))]
      exact h
  obtain ⟨ss, h1, h2⟩ := rstripLoop_spec f s (s.bytes.length + 1) (lastindex s)
    (ncodeunits s + ix 1) (collectPairs s) [] hseg hend (by simp) (by simp) (by omega) hi
  refine ⟨ss, ?_, h2⟩
  unfold Strings.rstrip
  exact h1

/-! ## `strip` -/

theorem bv_take (s : JStr) (m : Nat) (r : Int) (hm : 1 ≤ m) (hr : r ≤ m) :
    bv (s.slice 0 m) r = bv s r := by
  have hk : r.toNat - 1 < m := by omega
  unfold bv JStr.slice
  simp only [List.drop_zero, List.getD_eq_getElem?_getD, List.getElem?_take, hk, ↓reduceIte]

theorem thisZ_congr (s t : JStr) (p : Int) (h : ∀ r, r ≤ p → bv t r = bv s r) :
    thisZ t p = thisZ s p := by
  unfold thisZ
  rw [h p (Int.le_refl _), h (p - 1) (by omega), h (p - 2) (by omega), h (p - 3) (by omega)]

theorem slice_length (s : JStr) (m : Nat) (hm : m ≤ s.bytes.length) : (s.slice 0 m).bytes.length = m := by
  unfold JStr.slice
  simp only [List.drop_zero, List.length_take]
  omega

/-- The valid indices of a prefix view `s[1:m]` are those of `s` up to `m`. -/
theorem valid_take (s : JStr) (m : Nat) (hm : m ≤ s.bytes.length) (r : Int) (h1 : 1 ≤ r)
    (h2 : r ≤ m) : validZ (s.slice 0 m) r ↔ validZ s r := by
  have hl := slice_length s m hm
  have ht := thisZ_congr s (s.slice 0 m) r (fun q hq => bv_take s m q (by omega) (by omega))
  unfold validZ
  rw [hl, ht]
  constructor
  · intro h; exact ⟨h.1, by omega, h.2.2⟩
  · intro h; exact ⟨h.1, by omega, h.2.2⟩

/-- `ss` is `s` without its maximal leading and trailing runs of characters satisfying `f`:
the characters of `s` split as `pre ++ mid ++ post` with every character of `pre` and of
`post` satisfying `f`, iterating `ss` yields exactly the characters of `mid`, and `ss` is
empty or spans `mid` exactly, whose first and last characters fail `f`. -/
def StripResult (f : UInt32 → Bool) (s : JStr) (ss : JSub) : Prop :=
  ∃ pre mid post, ss.str = s ∧ collectPairs s = pre ++ mid ++ post ∧ (∀ x ∈ pre, f x.1 = true) ∧
    (∀ x ∈ post, f x.1 = true) ∧ subChars ss = .ok (mid.map (·.1)) ∧
    ((mid = [] ∧ ss.offset.val = 0 ∧ ss.ncu.val = 0) ∨
     (∃ c i d j, mid.head? = some (c, i) ∧ mid.getLast? = some (d, j) ∧ f c = false ∧
        f d = false ∧ ss.offset.val = i.val - 1 ∧
        ss.offset.val + ss.ncu.val + 1 = (post.head?.map (·.2.val)).getD (s.bytes.length + 1)))

/-- For every byte string `s` and predicate `f`, `strip(f, s)` returns the SubString of `s`
spanning its characters from the first to the last one failing `f`. -/
def StripChars : Prop :=
  ∀ (f : UInt32 → Bool) (s : JStr), ∃ ss, strip f s = .ok ss ∧ StripResult f s ss

theorem lstripSubLoop_spec (f : UInt32 → Bool) (s : JStr) (o m e b : JInt64)
    (next : JInt64 → SJl (Option (UInt32 × JInt64))) (hnext : ∀ p, next p = subIterate ⟨s, o, m⟩ p)
    (A : List (UInt32 × JInt64)) (ho : o.val = 0) (hm : 0 ≤ m.val) (hb : b.val = m.val + 1)
    (hbn : b.val ≤ s.bytes.length + 1) (he0 : 0 ≤ e.val) (hem : e.val ≤ m.val)
    (heA : A ≠ [] → validZ s e.val ∧ NextValid s e.val b.val) :
    ∀ (k : Nat) (i : JInt64) (P Q : List (UInt32 × JInt64)),
      Seg s b i Q → VE s i → A = P ++ Q → (∀ x ∈ P, f x.1 = true) → Q.length < k →
      ∃ ss, lstripSubLoop f ⟨s, o, m⟩ next e k i = .ok ss ∧
        ∃ P' M, A = P' ++ M ∧ (∀ x ∈ P', f x.1 = true) ∧ ss.str = s ∧
          subChars ss = .ok (M.map (·.1)) ∧
          ((M = [] ∧ ss.offset.val = 0 ∧ ss.ncu.val = 0) ∨
           (∃ c i rest, M = (c, i) :: rest ∧ f c = false ∧ ss.offset.val = i.val - 1 ∧
              ss.offset.val + ss.ncu.val = m.val)) := by
  have hs := ncu_small s
  have e1 := ix1
  have he1 : (e + ix 1).val = e.val + 1 := add_val _ _ (by omega) (by omega)
  have hoe : ∀ x : JInt64, 0 ≤ x.val → x.val ≤ 2 ^ 62 → o + x = x := fun x h1 h2 =>
    Subtype.ext (by rw [add_val _ _ (by omega) (by omega)]; omega)
  have hxo : ∀ x : JInt64, 0 ≤ x.val → x.val ≤ 2 ^ 62 → x - o = x := fun x h1 h2 =>
    Subtype.ext (by rw [sub_val _ _ (by omega) (by omega)]; omega)
  have hempty : subSubstring ⟨s, o, m⟩ (e + ix 1) e = .ok ⟨s, ix 0, ix 0⟩ := by
    rw [subSubstring_gt s o m (e + ix 1) e (by omega)]
    exact substring_empty s _ _ true
      (by rw [hoe e he0 (by omega), hoe (e + ix 1) (by omega) (by omega)]; omega)
  intro k
  induction k with
  | zero => intro i P Q _ _ _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    intro i P Q hseg hv hA hP hk
    cases Q with
    | nil =>
      have hi := seg_nil_inv hseg
      have hstep : next i = .ok none := by
        rw [hnext]
        exact subIterate_end ⟨s, o, m⟩ i hm (by show m.val < 2 ^ 62; omega)
          (by show i.val = m.val + 1; rw [hi, hb])
      have hloop : lstripSubLoop f ⟨s, o, m⟩ next e (k + 1) i = .ok ⟨s, ix 0, ix 0⟩ := by
        simp only [lstripSubLoop, hstep]; exact hempty
      exact ⟨_, hloop, P, [], by simpa using hA, hP, rfl, subChars_empty s _ _ rfl rfl,
        Or.inl ⟨rfl, rfl, rfl⟩⟩
    | cons x rest =>
      obtain ⟨hx, i', hit, hseg'⟩ := seg_cons_inv hseg
      obtain ⟨c, i0⟩ := x
      simp only at hx hit
      subst hx
      obtain ⟨hvi, hnv, hve'⟩ := iter_step hv hit
      have hb2 := (seg_ve hseg' hve').2.1
      have hi0b : i0.val < b.val := by have := hnv.1; omega
      have hstep : next i0 = .ok (some (c, i')) := by
        rw [hnext]
        have := subIterate_step ⟨s, o, m⟩ i0 i0 i' c hm (by show m.val < 2 ^ 62; omega) hvi.1
          (by show i0.val ≤ m.val; omega) (hoe i0 (by have := hvi.1; omega) (by omega)) hit
        rw [this, show (⟨s, o, m⟩ : JSub).offset = o from rfl,
          hxo i' (by have := hnv.1; have := hvi.1; omega) (by have := hve'.2.1; omega)]
      by_cases hfc : f c = false
      · obtain ⟨hev, henv⟩ := heA (by rw [hA]; simp)
        have hle : i0.val ≤ e.val := by
          by_cases hc : i0.val ≤ e.val
          · exact hc
          · exact absurd hvi (henv.2.2.1 _ (by omega) (by omega))
        have hnl : nextind s e = .ok b := nextind_to s e b hev henv
        have hsub := substring_ok s i0 e b false hvi hev hle hnl
        have hss : subSubstring ⟨s, o, m⟩ i0 e false = .ok ⟨s, i0 - ix 1, b - i0⟩ := by
          rw [subSubstring_unchecked, hoe i0 (by have := hvi.1; omega) (by have := hvi.2.1; omega),
            hoe e he0 (by omega)]
          exact hsub
        have hloop : lstripSubLoop f ⟨s, o, m⟩ next e (k + 1) i0 = .ok ⟨s, i0 - ix 1, b - i0⟩ := by
          simp only [lstripSubLoop, hstep, hfc, Bool.not_false, ↓reduceIte]; exact hss
        have hi1 := hvi.1
        have eo : (i0 - ix 1).val = i0.val - 1 := by rw [sub_val _ _ (by omega) (by omega)]; omega
        have en : (b - i0).val = b.val - i0.val := by rw [sub_val _ _ (by omega) (by omega)]
        refine ⟨_, hloop, P, (c, i0) :: rest, hA, hP, rfl, ?_, Or.inr ⟨c, i0, rest, rfl, hfc, eo, ?_⟩⟩
        · exact subChars_seg s _ _ _ _ _ hseg hv (by omega) (by omega) (by omega) (by omega)
        · show (i0 - ix 1).val + (b - i0).val = m.val
          rw [eo, en]; omega
      · have hft : f c = true := by simpa using hfc
        have hP' : ∀ x ∈ P ++ [(c, i0)], f x.1 = true := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hP x hx
          · rw [List.mem_singleton] at hx; rw [hx]; exact hft
        have hA' : A = (P ++ [(c, i0)]) ++ rest := by simp [hA]
        have hk' : rest.length < k := by simp only [List.length_cons] at hk; omega
        obtain ⟨ss, h1, h2⟩ := ih i' (P ++ [(c, i0)]) rest hseg' hve' hA' hP' hk'
        refine ⟨ss, ?_, h2⟩
        simp only [lstripSubLoop, hstep, hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact h1

/-- `bind` on a success, for an arbitrary continuation `g`. Stated for a variable `g` so that
the kernel checks it without unfolding the continuation. -/
theorem bind_ok_eq {α β : Type} (a : α) (g : α → SJl β) : (bind (Except.ok a) g : SJl β) = g a :=
  rfl

/-- `strip` after a successful `rstrip`. -/
theorem strip_of_rstrip (f : UInt32 → Bool) (s : JStr) (r : JSub) (h : Strings.rstrip f s = .ok r) :
    strip f s = lstripSub f r := by
  unfold strip
  rw [h]
  exact bind_ok_eq r (lstripSub f)

theorem stripChars_proven : StripChars := by
  intro f s
  have hs := ncu_small s
  have e1 := ix1
  obtain ⟨r, hr, pre, post, hstr, hcp, hpost, _, hoff, hcase⟩ := rstripChars_proven f s
  have tr := collect_trace s
  rw [hcp] at tr
  obtain ⟨j, hsegA, htrB⟩ := trace_split pre post tr
  have hvj : VE s j := (seg_ve hsegA (ve_one s)).1
  have hlenA := (seg_ve hsegA (ve_one s)).2.1
  have hjv := trace_head htrB hvj
  obtain ⟨rs, ro, rm⟩ := r
  simp only at hstr hoff
  subst hstr
  have hrm : rm.val + 1 = j.val := by
    rcases hcase with ⟨hpre0, hm0⟩ | ⟨c, i, _, _, hm⟩
    · simp only at hm0
      subst hpre0
      have := congrArg Subtype.val (seg_nil_inv hsegA)
      omega
    · simp only at hm; rw [hm, hjv]
  have hrm0 : 0 ≤ rm.val := by omega
  have hrmn : rm.val ≤ rs.bytes.length := by have := hvj.2.1; omega
  -- the last index of the view `rs[1:rm]`
  have hview : (⟨rs, ro, rm⟩ : JSub).view = rs.slice 0 rm.val.toNat := by
    show rs.slice ro.val.toNat rm.val.toNat = _
    rw [hoff, Int.toNat_zero]
  have hmn : rm.val.toNat ≤ rs.bytes.length := by omega
  have hvl := slice_length rs rm.val.toNat hmn
  have hr0 := lastindex_range (rs.slice 0 rm.val.toNat)
  have hsp := lastindex_spec (rs.slice 0 rm.val.toNat)
  generalize hL : lastindex (rs.slice 0 rm.val.toNat) = L at hr0 hsp
  rw [hvl] at hr0 hsp
  obtain ⟨he0, hem, heA⟩ : 0 ≤ L.val ∧ L.val ≤ rm.val ∧
      (pre ≠ [] → validZ rs L.val ∧ NextValid rs L.val j.val) := by
    refine ⟨hr0.1, by omega, fun hne => ?_⟩
    have hm1 : 1 ≤ rm.val := by
      rcases hcase with ⟨hpre0, _⟩ | ⟨c, i, hlast, _, _⟩
      · exact absurd hpre0 hne
      · obtain ⟨A', hA'⟩ : ∃ A', pre = A' ++ [(c, i)] := by
          rcases nil_or_snoc pre with h | ⟨A', x, h⟩
          · exact absurd h hne
          · rw [h] at hlast; simp at hlast; rw [hlast] at h; exact ⟨A', h⟩
        rw [hA'] at hlenA
        simp only [List.length_append, List.length_singleton] at hlenA
        omega
    obtain ⟨hlv, hlg⟩ := hsp (by omega)
    have hl1 := hlv.1
    have hl2 := hlv.2.1
    have hlv' : validZ rs L.val := (valid_take rs _ hmn _ hl1 (by omega)).1 hlv
    refine ⟨hlv', by omega, hvj.2.1, fun q h1 h2 hq => ?_, fun h => hvj.2.2 h⟩
    exact hlg q h1 (by omega) ((valid_take rs _ hmn q (by omega) (by omega)).2 hq)
  obtain ⟨ss, hloop, P', M, hPM, hP', hss, hch, hres⟩ :=
    lstripSubLoop_spec f rs ro rm _ j (subIterate ⟨rs, ro, rm⟩) (fun _ => rfl) pre hoff hrm0
      (by omega) hvj.2.1 he0 hem heA (rm.val.toNat + 1) (ix 1) [] pre hsegA (ve_one rs)
      (by simp) (by simp) (by omega)
  refine ⟨ss, ?_, P', M, post, hss, by rw [hcp, hPM], hP', hpost, hch, ?_⟩
  · rw [strip_of_rstrip f _ _ hr]
    unfold lstripSub
    rw [hview, hL]
    exact hloop
  · rcases hres with ⟨hM, h0, h1⟩ | ⟨c, i, rest, hM, hfc, hof, hend⟩
    · exact Or.inl ⟨hM, h0, h1⟩
    · right
      rcases hcase with ⟨hpre0, _⟩ | ⟨d, dj, hlast, hfd, _⟩
      · rw [hpre0] at hPM; rw [hM] at hPM; simp at hPM
      · refine ⟨c, i, d, dj, by rw [hM]; rfl, ?_, hfc, hfd, hof, ?_⟩
        · obtain ⟨M', y, hMy⟩ : ∃ M' y, M = M' ++ [y] := by
            rcases nil_or_snoc M with h | ⟨M', y, h⟩
            · rw [hM] at h; cases h
            · exact ⟨M', y, h⟩
          have h1 : pre.getLast? = some y := by rw [hPM, hMy, ← List.append_assoc]; simp
          have h2 : M.getLast? = some y := by rw [hMy]; simp
          rw [hlast] at h1
          rw [h2, ← h1]
        · rw [hend, hrm, hjv]

/-! ## `chomp` -/

theorem iterateContinued_top (s : JStr) (i : JInt64) (u : UInt32) (l : Nat) (h : TopByte u l) :
    TopByte (iterateContinued s i u).1 l := by
  have b16 : ∀ b : UInt8, (b.toUInt32 <<< 16).toNat < 2 ^ 24 := fun b => by
    rw [shl16_toNat]; have := UInt8.toNat_lt b; omega
  have b8 : ∀ b : UInt8, (b.toUInt32 <<< 8).toNat < 2 ^ 24 := fun b => by
    rw [shl8_toNat]; have := UInt8.toNat_lt b; omega
  have b0 : ∀ b : UInt8, b.toUInt32.toNat < 2 ^ 24 := fun b => by
    rw [UInt8.toNat_toUInt32]; have := UInt8.toNat_lt b; omega
  unfold iterateContinued
  dsimp only
  repeat' split
  all_goals first
    | exact h
    | exact topByte_or _ _ _ h (b16 _)
    | exact topByte_or _ _ _ (topByte_or _ _ _ h (b16 _)) (b8 _)
    | exact topByte_or _ _ _ (topByte_or _ _ _ (topByte_or _ _ _ h (b16 _)) (b8 _)) (b0 _)

/-- The first byte of `s[i]` is the code unit at `i`. -/
theorem getindex_top (s : JStr) (i : JInt64) (c : UInt32) (h : getindex s i = .ok c) :
    TopByte c (bv s i.val) := by
  rw [← cu_toNat]
  generalize hu : (cu s i).toUInt32 <<< 24 = u
  have hu' : TopByte u (cu s i).toNat := hu ▸ topByte_init (cu s i)
  by_cases hb : 1 ≤ i.val ∧ i.val ≤ (ncodeunits s).val
  · have hcu : codeunit s i = .ok (cu s i) := by unfold codeunit; exact if_pos hb
    have hg : getindex s i =
        (if !between (cu s i) 0x80 0xf7 then .ok u else getindexContinued s i u) := by
      unfold getindex; rw [hcu, ← hu]; rfl
    rw [hg] at h
    split at h
    · exact (Except.ok.inj h) ▸ hu'
    · unfold getindexContinued at h
      split at h
      · split at h
        · exact (Except.ok.inj h) ▸ hu'
        · exact nomatch h
      · exact (Except.ok.inj h) ▸ iterateContinued_top s i _ _ hu'
  · have hcu : codeunit s i = .error boundsErr := by unfold codeunit; exact if_neg hb
    have hg : getindex s i = .error boundsErr := by unfold getindex; rw [hcu]; rfl
    rw [hg] at h
    exact nomatch h

theorem topByte_unique {u : UInt32} {l l' : Nat} (h : TopByte u l) (h' : TopByte u l') : l = l' := by
  obtain ⟨r, hr, hu⟩ := h
  obtain ⟨r', hr', hu'⟩ := h'
  omega

theorem topByte_lit (x : UInt8) : TopByte (x.toUInt32 <<< 24) x.toNat := topByte_init x

/-- An ASCII byte at a valid index is its own character. -/
theorem getindex_ascii (s : JStr) (i : JInt64) (hv : validZ s i.val) (hb : bv s i.val < 128) :
    getindex s i = .ok ((cu s i).toUInt32 <<< 24) ∧ nextZ s i.val = i.val + 1 := by
  have hlt : ¬ (0x80 ≤ cu s i) := by
    rw [UInt8.le_iff_toNat_le, cu_toNat]; show ¬ (128 ≤ bv s i.val); omega
  have hnb : (!between (cu s i) 0x80 0xf7) = true := by
    simp only [between, hlt, decide_false, Bool.false_and, Bool.not_false]
  have hit : iterate s i = some ((cu s i).toUInt32 <<< 24, i + ix 1) := by
    rw [iterate_eq s i hv.1 hv.2.1, if_pos hnb]
  refine ⟨getindex_of_iterate s i _ _ hv hit, ?_⟩
  have h128 : ¬ (128 ≤ bv s i.val) := by omega
  unfold nextZ
  simp only [h128, decide_false, Bool.false_and, Bool.not_false, ↓reduceIte]

theorem cu_eq_of_bv (s : JStr) (i : JInt64) (x : UInt8) (h : bv s i.val = x.toNat) : cu s i = x :=
  UInt8.toNat.inj (by rw [cu_toNat]; exact h)

/-- The bit pattern `s[i]` is `'\n'` (resp. `'\r'`) exactly when the code unit at `i` is
`0x0a` (resp. `0x0d`). -/
theorem getindex_ne_ascii (s : JStr) (i : JInt64) (c : UInt32) (x : UInt8)
    (h : getindex s i = .ok c) (hx : bv s i.val ≠ x.toNat) : (c != x.toUInt32 <<< 24) = true := by
  have ht := getindex_top s i c h
  simp only [bne_iff_ne, ne_eq]
  intro hc
  rw [hc] at ht
  exact hx (topByte_unique ht (topByte_lit x))

theorem bv_last (s : JStr) (h : 1 ≤ s.bytes.length) :
    s.bytes.getLast? = some (s.bytes.getD (s.bytes.length - 1) 0) ∧
    (s.bytes.getD (s.bytes.length - 1) 0).toNat = bv s s.bytes.length := by
  refine ⟨?_, ?_⟩
  · rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  · unfold bv; congr 2

/-- `chomp(s::String)` (the code-unit fast path) and the generic `chomp(::AbstractString)`
return the same SubString for every byte string. -/
def ChompGeneric : Prop := ∀ s : JStr, Strings.chomp s = Strings.chompGeneric s

theorem u8_beq (b x : UInt8) : (b == x) = decide (b.toNat = x.toNat) := by
  by_cases h : b = x
  · subst h; simp
  · have : b.toNat ≠ x.toNat := fun e => h (UInt8.toNat.inj e)
    simp [h, this]

/-- The fast path, unfolded. -/
theorem chomp_eq (s : JStr) : Strings.chomp s = .ok ⟨s, ix 1 - ix 1,
    if (ncodeunits s).val = 0 then ix 0
    else ncodeunits s - (bInt (s.bytes.getLast? == some 0x0a) +
      bInt ((s.bytes.getLast? == some 0x0a) && decide ((ncodeunits s).val > 1) &&
        (cu s (ncodeunits s - bInt (decide ((ncodeunits s).val > 1))) == 0x0d)))⟩ := rfl

theorem len_val (s : JStr) (a b : Bool) :
    (ncodeunits s - (bInt a + bInt b)).val =
      s.bytes.length - ((if a then 1 else 0) + (if b then 1 else 0)) := by
  have hs := ncu_small s
  have hab : (bInt a + bInt b).val = (if a then 1 else 0) + (if b then 1 else 0) := by
    rw [add_val _ _ (by rw [bInt_val, bInt_val]; split <;> split <;> omega)
      (by rw [bInt_val, bInt_val]; split <;> split <;> omega), bInt_val, bInt_val]
  rw [sub_val _ _ (by rw [hab, ncu_val]; split <;> split <;> omega)
    (by rw [hab, ncu_val]; split <;> split <;> omega), hab, ncu_val]

theorem lf_bits : ((0x0a : UInt8).toUInt32 <<< 24) = 0x0a000000 := by decide
theorem cr_bits : ((0x0d : UInt8).toUInt32 <<< 24) = 0x0d000000 := by decide

/-- `Strings.chompGeneric` (`base/strings/util.jl:371-375`) with the last index `i`,
`getindex(s, ·)`, `prevind(s, ·)` and `SubString(s, ·, ·)` as parameters. It is written with
the matchers of `Strings.chompGeneric` itself, so that both unfold to the same term; the
unused `_u` mentions the functions `chompGeneric` calls, which gives this definition the same
height as `chompGeneric`. The kernel then checks `chompGeneric_eq` by unfolding both at once;
any other unfolding of `chompGeneric` first reduces a matcher, which evaluates `lastindex s`
on a symbolic string. -/
def chompGenericWith (s : JStr) (i : JInt64) (g : JInt64 → SJl UInt32) (pv : JInt64 → SJl JInt64)
    (sub : JInt64 → JInt64 → Bool → SJl JSub) : SJl JSub :=
  let _u := (lastindex s, getindex s, prevind s, @substring s)
  let test : JInt64 → UInt32 → SJl Bool := fun k c =>
    if k.val < 1 then .ok true
    else Strings.chompGeneric.match_1 (fun _ => SJl Bool) (g k) (fun e => Except.error e)
      fun d => Except.ok (d != c)
  Strings.chompGeneric.match_3 (fun _ => SJl JSub) (test i 0x0a000000) (fun e => Except.error e)
    (fun _ => sub (ix 1) i true) fun _ =>
    Strings.substring.match_1 (fun _ => SJl JSub) (pv i) (fun e => Except.error e) fun j =>
      Strings.chompGeneric.match_3 (fun _ => SJl JSub) (test j 0x0d000000) (fun e => Except.error e)
        (fun _ => sub (ix 1) j true) fun _ =>
        Strings.substring.match_1 (fun _ => SJl JSub) (pv j) (fun e => Except.error e)
          fun k => sub (ix 1) k true

theorem chompGeneric_eq (s : JStr) :
    Strings.chompGeneric s = chompGenericWith s (lastindex s) (getindex s) (prevind s) (@substring s) :=
  rfl

/-- No character before index `1`: `SubString(s, 1, i)`. -/
theorem chompWith_short (s : JStr) (i : JInt64) (g : JInt64 → SJl UInt32) (pv : JInt64 → SJl JInt64)
    (sub : JInt64 → JInt64 → Bool → SJl JSub) (hi : i.val < 1) :
    chompGenericWith s i g pv sub = sub (ix 1) i true := by
  unfold chompGenericWith
  simp only [hi, ↓reduceIte]

/-- The last character is not `'\n'`: `SubString(s, 1, i)`. -/
theorem chompWith_nolf (s : JStr) (i : JInt64) (g : JInt64 → SJl UInt32) (pv : JInt64 → SJl JInt64)
    (sub : JInt64 → JInt64 → Bool → SJl JSub) (d : UInt32) (hi : ¬ i.val < 1) (hg : g i = .ok d)
    (hd : (d != 0x0a000000) = true) :
    chompGenericWith s i g pv sub = sub (ix 1) i true := by
  unfold chompGenericWith
  simp only [hi, hg, hd, ↓reduceIte]

/-- `'\n'` is the only character: `SubString(s, 1, prevind(s, i))`. -/
theorem chompWith_lf_short (s : JStr) (i j : JInt64) (g : JInt64 → SJl UInt32)
    (pv : JInt64 → SJl JInt64) (sub : JInt64 → JInt64 → Bool → SJl JSub) (hi : ¬ i.val < 1)
    (hg : g i = .ok 0x0a000000) (hp : pv i = .ok j) (hj : j.val < 1) :
    chompGenericWith s i g pv sub = sub (ix 1) j true := by
  unfold chompGenericWith
  simp only [hi, hg, hp, hj, ↓reduceIte, bne_self_eq_false]

/-- `'\n'` after a character other than `'\r'`: `SubString(s, 1, prevind(s, i))`. -/
theorem chompWith_lf (s : JStr) (i j : JInt64) (g : JInt64 → SJl UInt32)
    (pv : JInt64 → SJl JInt64) (sub : JInt64 → JInt64 → Bool → SJl JSub) (d : UInt32)
    (hi : ¬ i.val < 1) (hg : g i = .ok 0x0a000000) (hp : pv i = .ok j) (hj : ¬ j.val < 1)
    (hgj : g j = .ok d) (hd : (d != 0x0d000000) = true) :
    chompGenericWith s i g pv sub = sub (ix 1) j true := by
  unfold chompGenericWith
  simp only [hi, hg, hp, hj, hgj, hd, ↓reduceIte, bne_self_eq_false]

/-- `"\r\n"` at the end: `SubString(s, 1, prevind(s, prevind(s, i)))`. -/
theorem chompWith_crlf (s : JStr) (i j k : JInt64) (g : JInt64 → SJl UInt32)
    (pv : JInt64 → SJl JInt64) (sub : JInt64 → JInt64 → Bool → SJl JSub)
    (hi : ¬ i.val < 1) (hg : g i = .ok 0x0a000000) (hp : pv i = .ok j) (hj : ¬ j.val < 1)
    (hgj : g j = .ok 0x0d000000) (hpk : pv j = .ok k) :
    chompGenericWith s i g pv sub = sub (ix 1) k true := by
  unfold chompGenericWith
  simp only [hi, hg, hp, hj, hgj, hpk, ↓reduceIte, bne_self_eq_false]

/-- `chomp` agrees with the generic method on the empty string: both return `SubString(s, 1, 0)`. -/
theorem chompGeneric_empty (s : JStr) (hn0 : s.bytes.length = 0) :
    Strings.chomp s = Strings.chompGeneric s := by
  have hs := ncu_small s
  have hN := ncu_val s
  obtain ⟨L, hL⟩ : ∃ L, lastindex s = L := ⟨_, rfl⟩
  rw [chomp_eq]
  have h0 : (ncodeunits s).val = 0 := by omega
  have hL0 : L.val < 1 := by rw [← hL, lastindex_zero s hn0]; omega
  have hG : Strings.chompGeneric s = .ok ⟨s, ix 0, ix 0⟩ := by
    rw [chompGeneric_eq, hL, chompWith_short s L _ _ _ hL0]
    exact substring_empty s _ _ true (by rw [ix1]; exact hL0)
  rw [hG, if_pos h0]
  exact jsub_ok_mk rfl rfl

/-- `chomp` agrees with the generic method when the last character is `'\n'`. -/
theorem chompGeneric_lf (s : JStr) (hn0 : ¬ s.bytes.length = 0) (hlast : bv s s.bytes.length = 10) :
    Strings.chomp s = Strings.chompGeneric s := by
    have hs := ncu_small s
    have e1 := ix1
    have hN := ncu_val s
    have eo : (ix 1 - ix 1).val = 0 := rfl
    have hE := ncu1_val s
    obtain ⟨L, hL⟩ : ∃ L, lastindex s = L := ⟨_, rfl⟩
    rw [chomp_eq]
    have h0 : ¬ (ncodeunits s).val = 0 := by omega
    obtain ⟨hl1, hl2⟩ := bv_last s (by omega)
    have hlf : (s.bytes.getLast? == some 0x0a) = decide (bv s s.bytes.length = 10) := by
      rw [hl1]
      show (s.bytes.getD (s.bytes.length - 1) 0 == 0x0a) = _
      rw [u8_beq, hl2]; rfl
    obtain ⟨hLv, hLg⟩ := lastindex_spec s (by omega)
    rw [hL] at hLv hLg
    have hLn : NextValid s L.val (s.bytes.length + 1) :=
      ⟨by have := hLv.2.1; omega, by omega, fun r h1 h2 => hLg r h1 (by omega), fun h => by omega⟩
    have hL1 : ¬ L.val < 1 := by have := hLv.1; omega
    have hv1 : validZ s (ix 1).val := by rw [e1]; exact valid_one s (by omega)
    have hnv : validZ s s.bytes.length := ⟨by omega, Int.le_refl _, thisZ_noncont s _ (by omega)⟩
    have hLeq : L.val = s.bytes.length := by
      have := eq_lastindex s (ncodeunits s) (by rw [hN]; exact hnv) (fun r h1 h2 => by rw [hN] at h1; omega)
      rw [← hL, this, hN]
    have hbL : bv s L.val = 10 := by rw [hLeq]; exact hlast
    have hgetL' : getindex s L = .ok 0x0a000000 := by
      rw [(getindex_ascii s L hLv (by omega)).1, cu_eq_of_bv s L 0x0a hbL, lf_bits]
    by_cases hn1 : s.bytes.length = 1
    · -- `"\n"`: `prevind(s, 1) = 0`, so `SubString(s, 1, 0)`
      obtain ⟨p, hp, hp0⟩ := prevind_first s L (by omega)
      have hp1 : p.val < 1 := by omega
      have hG : Strings.chompGeneric s = .ok ⟨s, ix 0, ix 0⟩ := by
        rw [chompGeneric_eq, hL, chompWith_lf_short s L p _ _ _ hL1 hgetL' hp hp1]
        exact substring_empty s _ _ true (by omega)
      rw [hG, if_neg h0]
      refine jsub_ok_mk rfl ?_
      have htwo : decide ((ncodeunits s).val > 1) = false := by
        rw [hN]; simp only [decide_eq_false_iff_not]; omega
      rw [hlf, htwo, decide_eq_true hlast, Bool.true_and, Bool.false_and]
      rw [len_val]; simp only [↓reduceIte, Bool.false_eq_true, ix0] <;> omega
    have htwo : decide ((ncodeunits s).val > 1) = true := by
      rw [hN]; simp only [decide_eq_true_eq]; omega
    obtain ⟨M1, hM1⟩ : ∃ M1, ncodeunits s - bInt true = M1 := ⟨_, rfl⟩
    have hm1 : M1.val = s.bytes.length - 1 := by
      have hb1 : (bInt true).val = 1 := rfl
      rw [← hM1, sub_val _ _ (by omega) (by omega), hb1, hN]
    by_cases hcr : bv s (s.bytes.length - 1) = 13
    · -- `"…\r\n"`: the `'\r'` at `n - 1` is a single-byte character
      obtain ⟨P1, hP1⟩ : ∃ P1 : JInt64, P1 = ncodeunits s - ix 1 := ⟨_, rfl⟩
      have hP1v : P1.val = s.bytes.length - 1 := by
        rw [hP1, sub_val _ _ (by omega) (by omega), hN]; omega
      have hvP1 : validZ s P1.val := by
        rw [hP1v]; exact ⟨by omega, by omega, thisZ_noncont s _ (by omega)⟩
      have hpL : prevind s L = .ok P1 := prevind_to s L P1 (by omega)
        ⟨hvP1.1, by omega, hvP1, fun r h1 h2 => by omega⟩
      have hP1lt : ¬ P1.val < 1 := by omega
      have hgetP1 : getindex s P1 = .ok 0x0d000000 := by
        rw [(getindex_ascii s P1 hvP1 (by rw [hP1v]; omega)).1,
          cu_eq_of_bv s P1 0x0d (by rw [hP1v]; exact hcr), cr_bits]
      have hlen : ∃ X : JSub, Strings.chompGeneric s = .ok X ∧ X.str = s ∧ X.offset.val = 0 ∧
          X.ncu.val = s.bytes.length - 2 := by
        by_cases hn2 : s.bytes.length = 2
        · obtain ⟨p2, hp2, hp20⟩ := prevind_first s P1 (by omega)
          have hp2lt : p2.val < 1 := by omega
          refine ⟨⟨s, ix 0, ix 0⟩, ?_, rfl, rfl, by show (ix 0).val = _; rw [ix0]; omega⟩
          rw [chompGeneric_eq, hL, chompWith_crlf s L P1 p2 _ _ _ hL1 hgetL' hpL hP1lt hgetP1 hp2]
          exact substring_empty s _ _ true (by omega)
        · obtain ⟨p2, hp2, hp2'⟩ := previndN_one s P1 (by omega) (by omega)
          have hp2P : prevind s P1 = .ok p2 := hp2
          rcases hp2' with ⟨h, _⟩ | ⟨_, hpv⟩
          · omega
          have hvp2 := hpv.2.2.1
          have hnp2 : nextind s p2 = .ok P1 :=
            nextind_to s p2 P1 hvp2 (prevValid_nextValid s _ _ hpv (by omega) (fun _ => hvP1))
          refine ⟨⟨s, ix 1 - ix 1, P1 - ix 1⟩, ?_, rfl, eo,
            by show (P1 - ix 1).val = _; rw [sub_val _ _ (by omega) (by omega), hP1v]; omega⟩
          rw [chompGeneric_eq, hL, chompWith_crlf s L P1 p2 _ _ _ hL1 hgetL' hpL hP1lt hgetP1 hp2P]
          exact substring_ok s (ix 1) p2 P1 true hv1 hvp2 (by rw [e1]; exact hvp2.1) hnp2
      obtain ⟨⟨Xs, Xo, Xm⟩, hX, hXs, hXo, hXn⟩ := hlen
      simp only at hXs hXo hXn
      rw [hXs] at hX
      rw [hX, if_neg h0]
      refine jsub_ok_mk (by rw [eo, hXo]) ?_
      have hcu : (cu s (ncodeunits s - bInt true) == 0x0d) = true := by
        rw [u8_beq, cu_toNat, hM1, hm1]; simp only [decide_eq_true_eq]; exact hcr
      rw [hlf, htwo, decide_eq_true hlast, hcu, Bool.true_and, Bool.true_and]
      rw [len_val, hXn]; simp only [↓reduceIte] <;> omega
    · -- `"…\n"` with no `'\r'` before: `prevind` lands on a character that is not `'\r'`
      obtain ⟨p, hp, hp'⟩ := previndN_one s L (by omega) (by omega)
      rcases hp' with ⟨h, _⟩ | ⟨_, hpv⟩
      · omega
      have hvp := hpv.2.2.1
      have hpL : prevind s L = .ok p := hp
      have hp1 : ¬ p.val < 1 := by have := hvp.1; omega
      have hnp : nextind s p = .ok L :=
        nextind_to s p L hvp (prevValid_nextValid s _ _ hpv (by omega) (fun _ => hLv))
      obtain ⟨cp, jp, hitp, _⟩ := iterate_valid s p hvp
      have hgetp := getindex_of_iterate s p jp cp hvp hitp
      have hbp : bv s p.val ≠ 13 := by
        intro hb
        have hnz := (getindex_ascii s p hvp (by omega)).2
        have hn1' := nextZ_nextValid s p.val hvp.1 hvp.2.1
        rw [hnz] at hn1'
        have := nextValid_unique s p.val _ _ hn1'
          (prevValid_nextValid s _ _ hpv (by omega) (fun _ => hLv))
        have hpe : p.val = s.bytes.length - 1 := by omega
        rw [hpe] at hb; exact hcr hb
      have hne : (cp != 0x0d000000) = true := by
        rw [← cr_bits]; exact getindex_ne_ascii s p cp 0x0d hgetp hbp
      have hG : Strings.chompGeneric s = .ok ⟨s, ix 1 - ix 1, L - ix 1⟩ := by
        rw [chompGeneric_eq, hL, chompWith_lf s L p _ _ _ cp hL1 hgetL' hpL hp1 hgetp hne]
        exact substring_ok s (ix 1) p L true hv1 hvp (by rw [e1]; exact hvp.1) hnp
      rw [hG, if_neg h0]
      refine jsub_ok_mk rfl ?_
      have hcu : (cu s (ncodeunits s - bInt true) == 0x0d) = false := by
        rw [u8_beq, cu_toNat, hM1, hm1]; simp only [decide_eq_false_iff_not]; exact hcr
      rw [hlf, htwo, decide_eq_true hlast, hcu, Bool.true_and, Bool.true_and]
      rw [len_val, sub_val _ _ (by omega) (by omega), hLeq]
      simp only [↓reduceIte, Bool.false_eq_true, ix1] <;> omega

/-- `chomp` agrees with the generic method when the last character is not `'\n'`. -/
theorem chompGeneric_nolf (s : JStr) (hn0 : ¬ s.bytes.length = 0) (hlast : ¬ bv s s.bytes.length = 10) :
    Strings.chomp s = Strings.chompGeneric s := by
    have hs := ncu_small s
    have e1 := ix1
    have hN := ncu_val s
    have hE := ncu1_val s
    obtain ⟨L, hL⟩ : ∃ L, lastindex s = L := ⟨_, rfl⟩
    rw [chomp_eq]
    have h0 : ¬ (ncodeunits s).val = 0 := by omega
    obtain ⟨hl1, hl2⟩ := bv_last s (by omega)
    have hlf : (s.bytes.getLast? == some 0x0a) = decide (bv s s.bytes.length = 10) := by
      rw [hl1]
      show (s.bytes.getD (s.bytes.length - 1) 0 == 0x0a) = _
      rw [u8_beq, hl2]; rfl
    obtain ⟨hLv, hLg⟩ := lastindex_spec s (by omega)
    rw [hL] at hLv hLg
    have hLn : NextValid s L.val (s.bytes.length + 1) :=
      ⟨by have := hLv.2.1; omega, by omega, fun r h1 h2 => hLg r h1 (by omega), fun h => by omega⟩
    have hnL : nextind s L = .ok (ncodeunits s + ix 1) := nextind_to s L _ hLv (by rw [hE]; exact hLn)
    have hL1 : ¬ L.val < 1 := by have := hLv.1; omega
    have hv1 : validZ s (ix 1).val := by rw [e1]; exact valid_one s (by omega)
    obtain ⟨cL, jL, hitL, _⟩ := iterate_valid s L hLv
    have hgetL := getindex_of_iterate s L jL cL hLv hitL
    have hbL : bv s L.val ≠ 10 := by
      intro hb
      have hnz := (getindex_ascii s L hLv (by omega)).2
      have hn1' := nextZ_nextValid s L.val hLv.1 hLv.2.1
      rw [hnz] at hn1'
      have := nextValid_unique s L.val _ _ hn1' hLn
      have hLe : L.val = s.bytes.length := by omega
      rw [hLe] at hb; exact hlast hb
    have hne : (cL != 0x0a000000) = true := by
      rw [← lf_bits]; exact getindex_ne_ascii s L cL 0x0a hgetL hbL
    have hG : Strings.chompGeneric s = .ok ⟨s, ix 1 - ix 1, ncodeunits s + ix 1 - ix 1⟩ := by
      rw [chompGeneric_eq, hL, chompWith_nolf s L _ _ _ cL hL1 hgetL hne]
      exact substring_ok s (ix 1) L _ true hv1 hLv (by rw [e1]; exact hLv.1) hnL
    rw [hG, if_neg h0]
    refine jsub_ok_mk rfl ?_
    rw [hlf, decide_eq_false hlast, Bool.false_and, Bool.false_and]
    rw [len_val, sub_val _ _ (by omega) (by omega), hE]
    simp only [↓reduceIte, Bool.false_eq_true, ix1] <;> omega

theorem chompGeneric_proven : ChompGeneric := by
  intro s
  by_cases hn0 : s.bytes.length = 0
  · exact chompGeneric_empty s hn0
  by_cases hlast : bv s s.bytes.length = 10
  · exact chompGeneric_lf s hn0 hlast
  · exact chompGeneric_nolf s hn0 hlast

end JuliaLean.StringUtil.Strip

namespace JuliaLean.StringUtil

open JuliaLean.Registry

/-- Registry entries of `lstrip`, `rstrip`, `strip` and `chomp`. -/
def stripEntries : List Entry := [
  { id := "stringutil-lstrip-chars"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["lstrip(::Any, ::AbstractString)", "iterate(::String, ::Int)"]
    statement := "For every byte string s (valid UTF-8 or not) and every predicate f, lstrip(f, s) returns (never throws) a SubString of s that ends at the end of s and whose characters (collect) are exactly the characters of s from the first one failing f: collect(s) splits as pre ++ post with every character of pre satisfying f, and the SubString is empty or starts at the index of the first character of post, which fails f."
    source := "base/strings/util.jl:392-410 (lstrip docstring: remove leading characters satisfying the predicate)"
    status := .proven
    prop := ``Strip.LstripChars
    thm := some ``Strip.lstripChars_proven
    notes := "Characters and indices are those of collectPairs (iterate from 1). Iterating the returned SubString goes through SubString iteration (Strip.subChars), proved equal to the tail of collect(s). Same code in 1.13.2 (docstrings differ only)." },
  { id := "stringutil-rstrip-chars"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["rstrip(::Any, ::AbstractString)", "prevind(::String, ::Int)", "getindex(::String, ::Int)"]
    statement := "For every byte string s and predicate f, rstrip(f, s) returns a SubString of s starting at index 1 whose characters are exactly the characters of s up to the last one failing f: collect(s) splits as pre ++ post with every character of post satisfying f, and the SubString is empty or ends just before the first index of post, its last character failing f."
    source := "base/strings/util.jl:427-449 (rstrip docstring: remove trailing characters satisfying the predicate)"
    status := .proven
    prop := ``Strip.RstripChars
    thm := some ``Strip.rstripChars_proven
    notes := "rstrip walks backwards with prevind/getindex from lastindex(s), lstrip and collect forwards with iterate; the proof shows that for every byte string, including invalid UTF-8, the backward walk visits exactly the (character, index) pairs of collect(s) in reverse. Same code in 1.13.2." },
  { id := "stringutil-strip-chars"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["strip(::Any, ::AbstractString)", "lstrip(::Any, ::SubString{String})", "iterate(::SubString{String}, ::Int)"]
    statement := "For every byte string s and predicate f, strip(f, s) = lstrip(f, rstrip(f, s)) returns a SubString of s whose characters are those of s without the maximal leading and trailing runs satisfying f: collect(s) = pre ++ mid ++ post, every character of pre and post satisfies f, the SubString iterates to mid, and it is empty or spans mid exactly (its first and last characters fail f)."
    source := "base/strings/util.jl:456-489 (strip docstring)"
    status := .proven
    prop := ``Strip.StripChars
    thm := some ``Strip.stripChars_proven
    notes := "The lstrip step iterates the SubString returned by rstrip (Strings.subIterate). That SubString always ends at a character boundary of s, so the raw_substring iteration bug (bugs/strings-raw-substring-iterate.yaml, a truncated character read past the SubString end) cannot occur here, and the statement holds for invalid UTF-8 too. Same code in 1.13.2." },
  { id := "stringutil-chomp-generic"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["chomp(::Union{String, SubString{String}})", "chomp(::AbstractString)"]
    statement := "For every byte string s, the String fast path chomp(s) (code units) and the generic chomp(::AbstractString) (characters, prevind) return the same SubString (same parent, offset and length), hence the same bytes."
    source := "base/strings/util.jl:371-388 (two methods of the same documented function)"
    status := .proven
    prop := ``Strip.ChompGeneric
    thm := some ``Strip.chompGeneric_proven
    notes := "Stronger than byte equality: the SubStrings are equal. Holds for malformed input because '\\n' and '\\r' are ASCII: the last code unit is 0x0a exactly when the last character is '\\n'. 1.13.2 builds the fast-path result with SubString(s, 0, len, Val(:noshift)), the same value." }
]

end JuliaLean.StringUtil
