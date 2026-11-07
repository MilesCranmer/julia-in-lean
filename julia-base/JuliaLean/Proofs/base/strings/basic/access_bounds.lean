import JuliaLean.Proofs.base.array.common
import JuliaLean.Proofs.base.strings.string.access_bounds


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-- A checked code-unit or generic `getindex` call performs one local String access only when
its source check succeeds (`base/strings/basic.jl:185-199`, `base/strings/string.jl:212-217`). -/
def checkedStringAccesses (s : JuliaLean.Strings.JStr) (i : Int) : List Int :=
  getindexStringAccesses s i

/-- The generic length/prevind/nextind/ASCII loops range only over a checked source span. The
byte-value branch changes termination, so the set of possible accesses is the loop range.
`base/strings/basic.jl:396-405,447-573,622-652` and
`base/strings/string.jl:597-658`. -/
def checkedStringScan (len first last : Nat) : List Int :=
  if 1 ≤ first ∧ first ≤ last + 1 ∧ last ≤ len then
    if first ≤ last then span first (last + 1 - first) else []
  else []

/-- Exact indices passed to the unchecked `isvalid` call in the generic `nextind(s,i,n)` loop.
The `n` update uses the same wrapping `JInt64` subtraction as Julia; the index advances only
under `i < ncodeunits(s)`. `base/strings/basic.jl:564-573`. -/
def nextindNLoopCalls (s : JuliaLean.Strings.JStr) : Nat → Int → JInt64 → List Int
  | 0, _, _ => []
  | fuel + 1, i, n =>
      if n.val > 0 ∧ i < s.bytes.length then
        let j := i + 1
        j :: nextindNLoopCalls s fuel j
          (n - JuliaLean.Strings.bInt (JuliaLean.Strings.isvalidAt s (JInt.wrap .i64 j)))
      else []

def nextindNAccesses (s : JuliaLean.Strings.JStr) (i n : JInt64) : List Int :=
  if n.val < 0 ∨ i.val < 0 ∨ s.bytes.length < i.val ∨ n.val = 0 then []
  else nextindNLoopCalls s (s.bytes.length - i.val).toNat i.val n

theorem nextindNLoopCalls_safe (s : JuliaLean.Strings.JStr) :
    ∀ (fuel : Nat) (i : Int) (n : JInt64) (j : Int), 0 ≤ i → i ≤ s.bytes.length →
      j ∈ nextindNLoopCalls s fuel i n → inBounds s.bytes.length j := by
  intro fuel
  induction fuel with
  | zero => intro i n j hi0 hin h; simp [nextindNLoopCalls] at h
  | succ fuel ih =>
      intro i n j hi0 hin h
      simp only [nextindNLoopCalls] at h
      split at h
      · rename_i hc
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · simp [inBounds]
          omega
        · exact ih (i + 1) _ j (by omega) (by omega) h
      · simp_all

theorem nextindNAccesses_safe (s : JuliaLean.Strings.JStr) (i n : JInt64) (j : Int)
    (h : j ∈ nextindNAccesses s i n) : inBounds s.bytes.length j := by
  unfold nextindNAccesses at h
  split at h
  · simp_all
  · exact nextindNLoopCalls_safe s _ i.val n j (by omega) (by omega) h

/-- Exact indices passed to `isvalid` in `prevind(s,i,n)`. The index decrements only under
`1 < i`; `n` uses the same wrapping update as Julia. `base/strings/basic.jl:505-514`. -/
def previndNLoopCalls (s : JuliaLean.Strings.JStr) : Nat → Int → JInt64 → List Int
  | 0, _, _ => []
  | fuel + 1, i, n =>
      if n.val > 0 ∧ 1 < i then
        let j := i - 1
        j :: previndNLoopCalls s fuel j
          (n - JuliaLean.Strings.bInt (JuliaLean.Strings.isvalidAt s (JInt.wrap .i64 j)))
      else []

def previndNAccesses (s : JuliaLean.Strings.JStr) (i n : JInt64) : List Int :=
  if n.val < 0 ∨ i.val ≤ 0 ∨ s.bytes.length + 1 < i.val ∨ n.val = 0 then []
  else previndNLoopCalls s (i.val - 1).toNat i.val n

theorem previndNLoopCalls_safe (s : JuliaLean.Strings.JStr) :
    ∀ (fuel : Nat) (i : Int) (n : JInt64) (j : Int), 1 ≤ i → i ≤ s.bytes.length + 1 →
      j ∈ previndNLoopCalls s fuel i n → inBounds s.bytes.length j := by
  intro fuel
  induction fuel with
  | zero => intro i n j hi1 hin h; simp [previndNLoopCalls] at h
  | succ fuel ih =>
      intro i n j hi1 hin h
      simp only [previndNLoopCalls] at h
      split at h
      · rename_i hc
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · simp [inBounds]
          omega
        · exact ih (i - 1) _ j (by omega) (by omega) h
      · simp_all

theorem previndNAccesses_safe (s : JuliaLean.Strings.JStr) (i n : JInt64) (j : Int)
    (h : j ∈ previndNAccesses s i n) : inBounds s.bytes.length j := by
  unfold previndNAccesses at h
  split at h
  · simp_all
  · exact previndNLoopCalls_safe s _ i.val n j (by omega) (by omega) h

def StringCoreAccessesInBounds : Prop :=
  (∀ s i j, j ∈ thisindAccesses s i → inBounds s.bytes.length j) ∧
  (∀ s i j, j ∈ nextindAccesses s i → inBounds s.bytes.length j) ∧
  (∀ s i j, j ∈ iterateStringAccesses s i → inBounds s.bytes.length j) ∧
  (∀ s i j, j ∈ getindexStringAccesses s i → inBounds s.bytes.length j) ∧
  (∀ s i j, j ∈ checkedStringAccesses s i → inBounds s.bytes.length j) ∧
  (∀ s i n j, j ∈ nextindNAccesses s i n → inBounds s.bytes.length j) ∧
  (∀ s i n j, j ∈ previndNAccesses s i n → inBounds s.bytes.length j) ∧
  (∀ len first last j, j ∈ checkedStringScan len first last → inBounds len j)

theorem stringCoreAccessesInBounds_proven : StringCoreAccessesInBounds := by
  exact ⟨thisindAccesses_safe, nextindAccesses_safe, iterateStringAccesses_safe,
    getindexStringAccesses_safe, getindexStringAccesses_safe,
    nextindNAccesses_safe, previndNAccesses_safe,
    by
      intro len first last j h
      unfold checkedStringScan at h
      split at h
      · rename_i hc
        split at h
        · obtain ⟨k, hk, rfl⟩ := mem_span h
          simp [inBounds]
          omega
        · simp_all
      · simp_all⟩

/-- The unchecked range selected by `first(s,n)`. `nextindN` computes `k`; `min(lastindex,k)`
is the endpoint. A nonpositive endpoint makes Julia's range empty, otherwise the range copy
reads through `nextZ(endpoint)-1`. -/
def firstStringAccesses (s : JuliaLean.Strings.JStr) (n : JInt64) : List Int :=
  match JuliaLean.Strings.nextindN s (JuliaLean.Strings.ix 0) n with
  | .error _ => []
  | .ok k =>
      let stop := min (JuliaLean.Strings.thisZ s s.bytes.length) k.val
      if stop < 1 then []
      else span 1 (JuliaLean.Strings.nextZ s stop - 1).toNat

/-- The unchecked range selected by `last(s,n)`. `previndN` computes `k`; `max(1,k)` is the
start and `lastindex(s)` the endpoint. -/
def lastStringAccesses (s : JuliaLean.Strings.JStr) (n : JInt64) : List Int :=
  match JuliaLean.Strings.previndN s (JuliaLean.Strings.ncodeunits s + JuliaLean.Strings.ix 1) n with
  | .error _ => []
  | .ok k =>
      let first := max 1 k.val
      let stop := JuliaLean.Strings.thisZ s s.bytes.length
      if stop < first then [] else span first.toNat (s.bytes.length + 1 - first.toNat)

def StringFirstLastAccessesInBounds : Prop :=
  (∀ s n i, i ∈ firstStringAccesses s n → inBounds s.bytes.length i) ∧
  (∀ s n i, i ∈ lastStringAccesses s n → inBounds s.bytes.length i)

theorem stringFirstLastAccessesInBounds_proven : StringFirstLastAccessesInBounds := by
  constructor
  · intro s n i hi
    unfold firstStringAccesses at hi
    split at hi
    · simp_all
    · rename_i k hk
      dsimp only at hi
      split at hi
      · simp_all
      · rename_i hstop
        obtain ⟨d, hd, rfl⟩ := mem_span hi
        have hlen : 0 < s.bytes.length := by
          cases Nat.eq_zero_or_pos s.bytes.length with
          | inl hz =>
              have hzthis : JuliaLean.Strings.thisZ s 0 = 0 := by
                simp [JuliaLean.Strings.thisZ, JuliaLean.Strings.cB, JuliaLean.Strings.bv]
              have hcast : (s.bytes.length : Int) = 0 := by omega
              rw [hcast, hzthis] at hstop
              omega
          | inr hp => exact hp
        have hlast := JuliaLean.Strings.thisZ_range s s.bytes.length (by omega)
        have hmin : min (JuliaLean.Strings.thisZ s s.bytes.length) k.val ≤ s.bytes.length := by
          omega
        have hn := JuliaLean.Strings.nextZ_spec s
          (min (JuliaLean.Strings.thisZ s s.bytes.length) k.val) (by omega) hmin
        simp [inBounds]
        omega
  · intro s n i hi
    unfold lastStringAccesses at hi
    split at hi
    · simp_all
    · rename_i k hk
      dsimp only at hi
      split at hi
      · simp_all
      · rename_i hstop
        obtain ⟨d, hd, rfl⟩ := mem_span hi
        simp [inBounds]
        omega
end JuliaLean.MemSafety.G6
end
