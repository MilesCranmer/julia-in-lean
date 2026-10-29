import JuliaLean.MultidimCov.ArrayV2Core

/-!
Growth and deletion primitives of `Vector` (master `base/array.jl:1102-1327`).

Each `mNNNN` mirrors the method starting at `base/array.jl:NNNN`. The
`ConcurrencyViolationError("Vector can not be resized concurrently")` checks
compare `a.ref` read twice in one sequential call; in this single-threaded model
the two reads are the same value, so those checks never fire and are omitted.
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- `Core.Intrinsics.ctlz_int` on an `Int64`. -/
def ctlz64 (x : Int) : Int :=
  if x < 0 then 0 else if x = 0 then 64 else 63 - (Nat.log2 x.toNat : Int)

/-- base/array.jl:1102 `overallocation(maxsize::Int)`. -/
def m1102 (maxsize : Int) : Int :=
  let exp2 := 8 * 8 - ctlz64 maxsize
  let extra := 2 ^ (exp2 * 7 / 8).toNat * 3 + Int.tdiv maxsize 8
  if maxsize > wrap64 (typemaxInt - extra) then typemaxInt else wrap64 (maxsize + extra)

/-- base/array.jl:1114 `array_new_memory(mem, newlen)`: a fresh `undef` memory. -/
def m1114 (_mem : Mem α) (newlen : Int) : Mem α := Mem.undef newlen

/-- base/array.jl:1116 `_growbeg_internal!(a, delta, len)`; returns `a` with its new `ref`. -/
def m1116 (a : Arr α) (delta len : Int) : R (Arr α) := do
  let mem := a.mem
  let offset := a.off
  let newlen ← checkedAdd len delta
  let memlen := mem.len
  if offset < 1 ∨ offset - 1 > memlen ∨ len > memlen - (offset - 1) then .error .concurrency else do
  let twoDelta ← checkedMul 2 delta
  let s ← checkedAdd len twoDelta
  let s ← checkedAdd s 1
  let newmemlen := max (m1102 len) s
  let newoffset := Int.tdiv (newmemlen - newlen) 2 + 1
  if newlen < memlen ∧ newoffset < memlen - newlen then do
    let newoffset := Int.tdiv (memlen - newlen) 2 + 1
    let newmem ← memCopy mem (newoffset + delta) mem offset len
    let newmem := newmem.unsetRange offset (min (newoffset + delta) (offset + len) - 1)
    pure { a with mem := newmem, off := newoffset }
  else do
    let newmem ← memCopy (m1114 mem newmemlen) (newoffset + delta) mem offset len
    pure { a with mem := newmem, off := newoffset }

/-- base/array.jl:1151 `_growbeg!(a, delta)`. -/
def m1151 (a : Arr α) (delta0 : Int) : R (Arr α) := do
  let delta ← toInt delta0
  if delta = 0 then .ok a else
  if ¬ delta ≥ 0 then .error .argument else do
  let len := length a
  let offset := a.off
  let newlen ← checkedAdd len delta
  if delta ≤ offset - 1 then
    pure { a with off := offset + (1 - delta) - 1, dims := [newlen] }
  else do
    let a ← m1116 a delta len
    pure { a with dims := [newlen] }

/-- base/array.jl:1171 `_growend_internal!(a, delta, len)`; returns `a` with its new `ref`. -/
def m1171 (a : Arr α) (delta len : Int) : R (Arr α) := do
  let mem := a.mem
  let memlen := mem.len
  let newlen ← checkedAdd len delta
  let offset := a.off
  if offset < 1 ∨ offset - 1 > memlen ∨ len > memlen - (offset - 1) then .error .concurrency else do
  let newmemlen ← checkedAdd (offset - 1) newlen
  if offset - 1 > newlen ∧ offset - 1 - newlen > Int.tdiv newlen 4 then do
    -- `newmem = mem`, so the stale tail of the old window is cleared afterwards
    let newoffset := Int.tdiv newlen 8 + 1
    let newmem ← refCopy mem newoffset mem offset len
    let newmem := newmem.unsetRange (max offset (newoffset + len)) (offset + len - 1)
    pure { a with mem := newmem, off := newoffset }
  else do
    let newmemlen2 := max (m1102 memlen) newmemlen
    let newmem := m1114 mem newmemlen2
    let newmem ← refCopy newmem offset mem offset len
    pure { a with mem := newmem, off := offset }

/-- base/array.jl:1212 `_growend!(a, delta)`. -/
def m1212 (a : Arr α) (delta0 : Int) : R (Arr α) := do
  let delta ← toInt delta0
  if ¬ delta ≥ 0 then .error .argument else do
  let len := length a
  let available := wrap64 (wrap64 (a.mem.len - wrap64 (a.off - 1)) - len)
  let a ← if available < delta then m1171 a delta len else pure a
  pure { a with dims := [wrap64 (len + delta)] }

/-- `for j in lo:hi; @inbounds unsetindex!(a, j); end` (Array `unsetindex!`, base/array.jl:209). -/
def unsetLoop (a : Arr α) (lo hi : Int) : Arr α :=
  { a with mem := a.mem.unsetRange (a.off + lo - 1) (a.off + hi - 1) }

/-- base/array.jl:1230 `_growat!(a, i, delta)`. -/
def m1230 (a : Arr α) (i0 delta0 : Int) : R (Arr α) := do
  let delta ← toInt delta0
  let i ← toInt i0
  if i = 1 then m1151 a delta else
  let len := length a
  if len < typemaxInt ∧ i = len + 1 then m1212 a delta else
  if ¬ delta ≥ 0 then .error .argument else
  if ¬ (1 < i ∧ i ≤ len) then .error .bounds else do
  let mem := a.mem
  let memlen := mem.len
  let newlen ← checkedAdd len delta
  let offset := a.off
  let newmemlen ← checkedAdd (offset - 1) newlen
  let preferStart := i ≤ Int.tdiv len 2
  if preferStart ∧ delta ≤ offset - 1 then do
    let newmem ← refCopy mem (offset - delta) mem offset i
    pure (unsetLoop { a with mem := newmem, off := offset - delta, dims := [newlen] } i (i + delta - 1))
  else if ¬ preferStart ∧ memlen ≥ newmemlen then do
    let newmem ← memCopy mem (offset - 1 + delta + i) mem (offset - 1 + i) (len - i + 1)
    pure (unsetLoop { a with mem := newmem, dims := [newlen] } i (i + delta - 1))
  else do
    let twoDelta ← checkedMul 2 delta
    let s ← checkedAdd len twoDelta
    let s ← checkedAdd s 1
    let newmemlen := max (m1102 memlen) s
    let newoffset := Int.tdiv (newmemlen - newlen) 2 + 1
    let newmem := m1114 mem newmemlen
    let newmem ← refCopy newmem newoffset mem offset (i - 1)
    let newmem ← memCopy newmem (newoffset + delta + i - 1) mem (offset + i - 1) (len - i + 1)
    pure { a with mem := newmem, off := newoffset, dims := [newlen] }

/-- base/array.jl:1278 `_deletebeg!(a, delta)`. -/
def m1278 (a : Arr α) (delta0 : Int) : R (Arr α) := do
  let delta ← toInt delta0
  let len := length a
  if uns delta > uns len then .error .argument else
  let a := unsetLoop a 1 delta
  let newlen := len - delta
  let a := { a with dims := [newlen] }
  if newlen ≠ 0 then pure { a with off := a.off + (delta + 1) - 1 } else pure a

/-- base/array.jl:1296 `_deleteend!(a, delta)`. -/
def m1296 (a : Arr α) (delta0 : Int) : R (Arr α) := do
  let delta ← toInt delta0
  let len := length a
  if uns delta > uns len then .error .argument else
  let newlen := len - delta
  let a := unsetLoop a (newlen + 1) len
  pure { a with dims := [newlen] }

/-- base/array.jl:276 `unsafe_copyto!(dest::Array, doffs, src::Array, soffs, n)`. -/
def m276 (dest : Arr α) (doffs : Int) (src : Arr α) (soffs n : Int) : R (Arr α) :=
  if n = 0 then .ok dest else do
  let doffs ← toInt doffs
  let soffs ← toInt soffs
  let d ← refIndex dest.mem dest.off doffs
  let s ← refIndex src.mem src.off soffs
  let m ← refCopy dest.mem d src.mem s n
  pure { dest with mem := m }

/-- base/array.jl:1307 `_deleteat!(a, i, delta)`. Arithmetic on Julia `Int`
wraps at each operation, including the bounds-check subtraction. -/
def m1312 (a : Arr α) (i0 delta : Int) : R (Arr α) := do
  let i ← toInt i0
  let len := length a
  if ¬ 0 ≤ delta then .error .argument else
  if ¬ (1 ≤ i ∧ i ≤ len) then .error .bounds else
  if ¬ delta ≤ wrap64 (wrap64 (len + 1) - i) then .error .bounds else
  if wrap64 (2 * i + delta) ≤ len then do
    let a ← m276 a (wrap64 (1 + delta)) a 1 (i - 1)
    m1278 a delta
  else do
    let a ← m276 a i a (wrap64 (i + delta)) (wrap64 (len + 1 - delta - i))
    m1296 a delta

/-! ## Arithmetic and list lemmas -/

theorem toInt_ok' {x : Int} (h0 : -9223372036854775808 ≤ x) (h1 : x ≤ 9223372036854775807) :
    toInt x = .ok x := by
  unfold toInt typeminInt typemaxInt; split
  · rfl
  · omega

theorem wrap64_id {x : Int} (h0 : -9223372036854775808 ≤ x) (h1 : x ≤ 9223372036854775807) :
    wrap64 x = x := by
  unfold wrap64
  rw [Int.emod_eq_of_lt (by omega) (by omega)] <;> omega

theorem uns_id {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 9223372036854775807) : uns x = x := by
  unfold uns; exact Int.emod_eq_of_lt h0 (by omega)

theorem uns_neg {x : Int} (h0 : -9223372036854775808 ≤ x) (h1 : x < 0) : uns x = x + 18446744073709551616 := by
  unfold uns
  have : x % 18446744073709551616 = (x + 18446744073709551616) % 18446744073709551616 := by
    rw [Int.add_emod_right]
  rw [show (2 : Int) ^ 64 = 18446744073709551616 by rfl, this, Int.emod_eq_of_lt (by omega) (by omega)]

theorem slice_eq {a a' : Arr α} (s s' m : Int) (hs : 0 ≤ s) (hs' : 0 ≤ s') (hm : 0 ≤ m)
    (h1 : s + m ≤ length a) (h2 : s' + m ≤ length a')
    (hp : ∀ k, 1 ≤ k → k ≤ m → a'.at (s' + k) = a.at (s + k)) :
    ((contents a').drop s'.toNat).take m.toNat = ((contents a).drop s.toNat).take m.toNat := by
  apply List.ext_getElem
  · simp; omega
  · intro k hk1 hk2
    simp only [List.getElem_take, List.getElem_drop, getElem_contents]
    simp only [List.length_take, List.length_drop, contents_length] at hk1
    have := hp (k + 1) (by omega) (by omega)
    rw [show ((s'.toNat + k : Nat) : Int) + 1 = s' + (k + 1) by omega,
        show ((s.toNat + k : Nat) : Int) + 1 = s + (k + 1) by omega]
    exact this

theorem take_eq_of {a a' : Arr α} (m : Int) (hm : 0 ≤ m) (h1 : m ≤ length a) (h2 : m ≤ length a')
    (hp : ∀ k, 1 ≤ k → k ≤ m → a'.at k = a.at k) :
    (contents a').take m.toNat = (contents a).take m.toNat := by
  have := slice_eq (a := a) (a' := a') 0 0 m (by omega) (by omega) hm (by omega) (by omega)
    (fun k h1 h2 => by simpa using hp k h1 h2)
  simpa using this

theorem prefix_eq_of {a a' : Arr α} (n : Int) (hn : 0 ≤ n) (hl : length a = n) (h2 : n ≤ length a')
    (hp : ∀ k, 1 ≤ k → k ≤ n → a'.at k = a.at k) :
    (contents a').take n.toNat = contents a := by
  rw [take_eq_of n hn (by omega) h2 hp, List.take_of_length_le (by simp <;> omega)]

theorem suffix_eq_of {a a' : Arr α} (n d : Int) (hn : 0 ≤ n) (hd : 0 ≤ d) (hl : length a = n)
    (h2 : length a' = n + d) (hp : ∀ k, 1 ≤ k → k ≤ n → a'.at (d + k) = a.at k) :
    (contents a').drop d.toNat = contents a := by
  have := slice_eq (a := a) (a' := a') 0 d n (by omega) hd hn (by omega) (by omega)
    (fun k h1 h2 => by simpa using hp k h1 h2)
  simp only [Int.toNat_zero, List.drop_zero] at this
  rw [List.take_of_length_le (by simp <;> omega), List.take_of_length_le (by simp <;> omega)] at this
  exact this

theorem m1102_bounds {n : Int} (h0 : 0 ≤ n) (h1 : n ≤ 9223372036854775807) :
    n ≤ m1102 n ∧ m1102 n ≤ 9223372036854775807 ∧ (n < 9223372036854775807 → n < m1102 n) ∧
      m1102 n ≤ n + n / 8 + 216172782113783808 := by
  unfold m1102 ctlz64
  have hlog : n ≠ 0 → (Nat.log2 n.toNat : Int) ≤ 62 := by
    intro hn
    have := (Nat.log2_lt (n := n.toNat) (k := 63) (by omega)).2 (by
      have : n.toNat < 2 ^ 63 := by omega
      exact this)
    omega
  have hk : ∀ e : Int, 0 ≤ e → e ≤ 64 → 1 ≤ (2 : Int) ^ (e * 7 / 8).toNat ∧
      (2 : Int) ^ (e * 7 / 8).toNat ≤ 72057594037927936 := by
    intro e he0 he1
    have hle : (e * 7 / 8).toNat ≤ 56 := by omega
    generalize (e * 7 / 8).toNat = k at hle ⊢
    have q0 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have q1 : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) hle
    have q2 : (2 : Nat) ^ 56 = 72057594037927936 := by rfl
    have q3 : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := Int.natCast_pow 2 k
    omega
  have hd : Int.tdiv n 8 = n / 8 := Int.tdiv_eq_ediv_of_nonneg h0
  simp only [show ¬ n < 0 from by omega, if_false, hd]
  have he : ∀ e : Int, 0 ≤ e → e ≤ 64 → ∀ r, r = (if n > wrap64 (typemaxInt - (2 ^ (e * 7 / 8).toNat * 3 + n / 8)) then typemaxInt
      else wrap64 (n + (2 ^ (e * 7 / 8).toNat * 3 + n / 8))) →
      n ≤ r ∧ r ≤ 9223372036854775807 ∧ (n < 9223372036854775807 → n < r) ∧
      r ≤ n + n / 8 + 216172782113783808 := by
    intro e he0 he1 r hr
    obtain ⟨p0, p1⟩ := hk e he0 he1
    unfold typemaxInt at hr
    rw [wrap64_id (by omega) (by omega)] at hr
    split at hr
    · subst hr; omega
    · rw [wrap64_id (by omega) (by omega)] at hr; subst hr; omega
  by_cases hz : n = 0
  · rw [if_pos hz]; exact he (8 * 8 - 64) (by omega) (by omega) _ rfl
  · rw [if_neg hz]; have := hlog hz; exact he _ (by omega) (by omega) _ rfl

/-- `overallocation` (base/array.jl:1102): for every size `0 ≤ n ≤ typemax(Int)` the
new capacity is at least `n`, saturates at `typemax(Int)`, is strictly larger
whenever that is representable, and adds at most `n/8 + 3·2^56` (the comment's
`3*maxsize^(7/8) + maxsize/8`). -/
def P1102 : Prop := ∀ n : Int, 0 ≤ n → n ≤ typemaxInt →
    n ≤ m1102 n ∧ m1102 n ≤ typemaxInt ∧ (n < typemaxInt → n < m1102 n) ∧
      m1102 n ≤ n + n / 8 + 3 * 2 ^ 56

theorem p1102 : P1102 := by
  intro n h0 h1
  unfold typemaxInt at *
  exact m1102_bounds h0 h1

/-- `array_new_memory(mem, newlen)`: a fresh memory of exactly `newlen` slots, all unset. -/
def P1114 : Prop := ∀ {α : Type} (mem : Mem α) (newlen : Int),
    (m1114 mem newlen).len = newlen ∧ ∀ k, (m1114 mem newlen).get k = none

theorem p1114 : P1114 := fun _ _ => ⟨rfl, fun _ => rfl⟩

/-- A valid `Vector` of length `n` in memory that a real allocation can hold. -/
def VecOK (a : Arr α) (n : Int) : Prop := IsVec a n ∧ Valid a ∧ Small a

/-- Pointwise goals about slots after copies and clears. -/
macro "slot_arith" : tactic => `(tactic| (
  simp only [Arr.at, Mem.unsetRange_get, Mem.copy_get, Mem.set_get, Mem.undef_get, Int.max_def,
    Int.min_def, unsetLoop]
  repeat' split
  all_goals first | rfl | omega | (congr 1; omega)))

theorem vecOK_unpack {a : Arr α} {n : Int} (h : VecOK a n) :
    length a = n ∧ 1 ≤ a.off ∧ 0 ≤ n ∧ a.off - 1 + n ≤ a.mem.len ∧ a.mem.len ≤ 1152921504606846976 ∧
      a.dims = [n] := by
  obtain ⟨hv, ⟨h1, h2, h3⟩, h4⟩ := h
  have hn := length_vec a n hv
  unfold Small at h4
  refine ⟨hn, h1, by omega, by omega, by omega, hv⟩

theorem m1171_spec {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) :
    ∃ a', m1171 a delta n = .ok a' ∧ a'.dims = a.dims ∧ 1 ≤ a'.off ∧
      a'.off - 1 + (n + delta) ≤ a'.mem.len ∧ (∀ k, 1 ≤ k → k ≤ n → a'.at k = a.at k) := by
  obtain ⟨_, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1171
  rw [checkedAdd_ok (by omega) (by omega), bind_ok]
  simp only []
  rw [if_neg (by omega), checkedAdd_ok (by omega) (by omega), bind_ok]
  have hq4 : Int.tdiv (n + delta) 4 = (n + delta) / 4 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hq8 : Int.tdiv (n + delta) 8 = (n + delta) / 8 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  rw [hq4, hq8]
  split
  · rename_i hc
    rw [refCopy_ok (by omega) (by omega) (by omega), bind_ok]
    refine ⟨_, rfl, rfl, by simp <;> omega, by simp <;> omega, ?_⟩
    intro k hk1 hk2
    slot_arith
  · rw [refCopy_ok (by omega) (by simp [m1114, Int.max_def]; split <;> omega) (by omega), bind_ok]
    refine ⟨_, rfl, rfl, by omega, by simp [m1114, Int.max_def]; split <;> omega, ?_⟩
    intro k hk1 hk2
    slot_arith

theorem m1212_spec {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) :
    ∃ a', m1212 a delta = .ok a' ∧ IsVec a' (n + delta) ∧ Valid a' ∧
      (∀ k, 1 ≤ k → k ≤ n → a'.at k = a.at k) := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1212
  rw [toInt_ok (by omega) (by omega), bind_ok, if_neg (by omega)]
  simp only [hn]
  rw [wrap64_id (x := a.off - 1) (by omega) (by omega),
    wrap64_id (x := a.mem.len - (a.off - 1)) (by omega) (by omega),
    wrap64_id (x := a.mem.len - (a.off - 1) - n) (by omega) (by omega),
    wrap64_id (x := n + delta) (by omega) (by omega)]
  split
  · obtain ⟨a', h1, h2, h3, h4, h5⟩ := m1171_spec ha hd0 hd1
    rw [h1, bind_ok]
    refine ⟨_, rfl, rfl, ⟨h3, by simp [length, hv] <;> omega, by simp [length, hv] <;> omega⟩, h5⟩
  · rw [pure_ok, bind_ok]
    refine ⟨_, rfl, rfl, ⟨ho, by simp [length, hv] <;> omega, by simp [length, hv] <;> omega⟩, fun k _ _ => rfl⟩

/-- `_growend!` contract: a negative count is an `ArgumentError`; otherwise the
vector grows to `n + delta` slots, stays valid, and keeps its first `n` slots. -/
def P1212 : Prop := ∀ {α : Type} (a : Arr α) (n delta : Int), VecOK a n →
    (typeminInt ≤ delta → delta < 0 → m1212 a delta = .error .argument) ∧
    (0 ≤ delta → delta ≤ 2 ^ 60 → ∃ a', m1212 a delta = .ok a' ∧ Valid a' ∧
      IsVec a' (n + delta) ∧ (contents a').take n.toNat = contents a)

theorem p1212 : P1212 := by
  intro α a n delta ha
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  refine ⟨fun h0 h1 => ?_, fun h0 h1 => ?_⟩
  · unfold m1212 toInt typeminInt typemaxInt
    unfold typeminInt at h0
    rw [if_pos (by omega), bind_ok, if_pos (by omega)]
  · obtain ⟨a', e, hv, hvl, hp⟩ := m1212_spec ha h0 (by omega)
    refine ⟨a', e, hvl, hv, prefix_eq_of n hn0 hn (by rw [length_vec a' _ hv] <;> omega) hp⟩

/-- `_growend_internal!` contract: on a valid vector it returns a ref whose window
holds `n + delta` slots, the first `n` equal to the old ones; on an invalid
`ref`/`size` pair it throws `ConcurrencyViolationError`. -/
def P1171 : Prop := ∀ {α : Type} (a : Arr α) (n delta : Int), 0 ≤ delta → delta ≤ 2 ^ 60 →
    (VecOK a n → ∃ a', m1171 a delta n = .ok a' ∧
      Valid { a' with dims := [n + delta] } ∧ (contents { a' with dims := [n + delta] }).take n.toNat = contents a) ∧
    (0 ≤ n → n ≤ 2 ^ 60 → ¬ Valid a → length a = n → m1171 a delta n = .error .concurrency)

theorem p1171 : P1171 := by
  intro α a n delta h0 h1
  refine ⟨fun ha => ?_, fun hn0 hn1 hv hl => ?_⟩
  · obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
    obtain ⟨a', e, hd, ho', hw', hp⟩ := m1171_spec ha h0 (by omega)
    refine ⟨a', e, ⟨ho', by simp [length, hv] <;> omega, by simp [length, hv] <;> omega⟩, ?_⟩
    exact prefix_eq_of n hn0 hn (by simp [length, hv] <;> omega) hp
  · unfold m1171
    rw [checkedAdd_ok (by omega) (by omega), bind_ok]
    simp only []
    unfold Valid at hv
    rw [if_pos (by omega)]

/-- `_deleteend!` contract: `delta` outside `0:length(a)` is an `ArgumentError`;
otherwise the result is the first `n - delta` slots. -/
def P1296 : Prop := ∀ {α : Type} (a : Arr α) (n delta : Int), VecOK a n →
    (typeminInt ≤ delta → delta ≤ typemaxInt → (delta < 0 ∨ n < delta) → m1296 a delta = .error .argument) ∧
    (0 ≤ delta → delta ≤ n → ∃ a', m1296 a delta = .ok a' ∧ Valid a' ∧ IsVec a' (n - delta) ∧
      contents a' = (contents a).take (n - delta).toNat)

theorem p1296 : P1296 := by
  intro α a n delta ha
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  refine ⟨fun h0 h1 h2 => ?_, fun h0 h1 => ?_⟩
  · unfold m1296 toInt typeminInt typemaxInt
    unfold typeminInt at h0; unfold typemaxInt at h1
    rw [if_pos (by omega), bind_ok]
    simp only [hn]
    rcases h2 with h2 | h2
    · rw [uns_neg (by omega) h2, uns_id (by omega) (by omega), if_pos (by omega)]
    · rw [uns_id (by omega) (by omega), uns_id (by omega) (by omega), if_pos (by omega)]
  · unfold m1296
    rw [toInt_ok (by omega) (by omega), bind_ok]
    simp only [hn]
    rw [uns_id (by omega) (by omega), uns_id (by omega) (by omega), if_neg (by omega), pure_ok]
    refine ⟨_, rfl, ⟨ho, by simp [length, hv] <;> omega, by simp [length, unsetLoop, hv] <;> omega⟩, rfl, ?_⟩
    have := take_eq_of (a := a) (a' := { unsetLoop a (n - delta + 1) n with dims := [n - delta] })
      (n - delta) (by omega) (by omega) (by simp [length]) (fun k h1 h2 => by slot_arith)
    rw [← this, List.take_of_length_le (by simp [length])]

/-- `_deletebeg!` contract: `delta` outside `0:length(a)` is an `ArgumentError`;
otherwise the result is the last `n - delta` slots. -/
def P1278 : Prop := ∀ {α : Type} (a : Arr α) (n delta : Int), VecOK a n →
    (typeminInt ≤ delta → delta ≤ typemaxInt → (delta < 0 ∨ n < delta) → m1278 a delta = .error .argument) ∧
    (0 ≤ delta → delta ≤ n → ∃ a', m1278 a delta = .ok a' ∧ Valid a' ∧ IsVec a' (n - delta) ∧
      contents a' = (contents a).drop delta.toNat)

theorem p1278 : P1278 := by
  intro α a n delta ha
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  refine ⟨fun h0 h1 h2 => ?_, fun h0 h1 => ?_⟩
  · unfold m1278 toInt typeminInt typemaxInt
    unfold typeminInt at h0; unfold typemaxInt at h1
    rw [if_pos (by omega), bind_ok]
    simp only [hn]
    rcases h2 with h2 | h2
    · rw [uns_neg (by omega) h2, uns_id (by omega) (by omega), if_pos (by omega)]
    · rw [uns_id (by omega) (by omega), uns_id (by omega) (by omega), if_pos (by omega)]
  · unfold m1278
    rw [toInt_ok (by omega) (by omega), bind_ok]
    simp only [hn]
    rw [uns_id (by omega) (by omega), uns_id (by omega) (by omega), if_neg (by omega)]
    split
    · refine ⟨_, rfl, ⟨by simp [unsetLoop] <;> omega, by simp [length, hv] <;> omega,
        by simp [length, unsetLoop, hv] <;> omega⟩, rfl, ?_⟩
      symm
      apply suffix_eq_of (n - delta) delta (by omega) h0 (by simp [length]) (by rw [hn] <;> omega)
      intro k h1 h2
      slot_arith
    · rename_i hz
      have hd : delta = n := by omega
      subst hd
      refine ⟨_, rfl, ⟨by simp [unsetLoop] <;> omega, by simp [length, hv] <;> omega,
        by simp [length, unsetLoop, hv] <;> omega⟩, rfl, ?_⟩
      rw [List.drop_of_length_le (by simp [hn])]
      simp [contents, length]

/-- `unsafe_copyto!(dest::Array, doffs, src::Array, soffs, n)` (docstring at
base/array.jl:266): for in-bounds windows, `dest[doffs+k-1]` becomes the old
`src[soffs+k-1]` for `k ∈ 1:n` (correct even when `src === dest`), and every other
slot and the length are unchanged. -/
def P276 : Prop := ∀ {α : Type} (dest src : Arr α) (doffs soffs n : Int), Valid dest → Valid src →
    0 ≤ n → 1 ≤ doffs → doffs + n - 1 ≤ length dest → 1 ≤ soffs → soffs + n - 1 ≤ length src →
    length dest ≤ 2 ^ 60 → length src ≤ 2 ^ 60 →
    ∃ d', m276 dest doffs src soffs n = .ok d' ∧ d'.dims = dest.dims ∧ d'.off = dest.off ∧
      d'.mem.len = dest.mem.len ∧
      ∀ k, 1 ≤ k → k ≤ length dest →
        d'.at k = if doffs ≤ k ∧ k < doffs + n then src.at (k - doffs + soffs) else dest.at k

theorem p276 : P276 := by
  intro α dest src doffs soffs n hd hs hn h1 h2 h3 h4 h5 h6
  obtain ⟨d1, d2, d3⟩ := hd
  obtain ⟨s1, s2, s3⟩ := hs
  unfold m276
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl]
    refine ⟨_, rfl, rfl, rfl, rfl, fun k _ _ => ?_⟩
    rw [if_neg (by omega)]
  · rw [if_neg h0, toInt_ok (by omega) (by omega), bind_ok, toInt_ok (by omega) (by omega), bind_ok]
    unfold refIndex
    rw [if_pos (by omega), bind_ok, if_pos (by omega), bind_ok,
      refCopy_ok (by omega) (by omega) (by omega), bind_ok]
    refine ⟨_, rfl, rfl, rfl, rfl, fun k _ _ => ?_⟩
    slot_arith

theorem drop_eq_of {a a' : Arr α} (s s' : Int) (hs : 0 ≤ s) (hs' : 0 ≤ s') (h1 : s ≤ length a)
    (h : length a - s = length a' - s')
    (hp : ∀ k, 1 ≤ k → k ≤ length a - s → a'.at (s' + k) = a.at (s + k)) :
    (contents a').drop s'.toNat = (contents a).drop s.toNat := by
  have := slice_eq (a := a) (a' := a') s s' (length a - s) hs hs' (by omega) (by omega) (by omega) hp
  rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)] at this
  exact this

theorem m1116_spec {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) :
    ∃ a', m1116 a delta n = .ok a' ∧ a'.dims = a.dims ∧ 1 ≤ a'.off ∧
      a'.off - 1 + (n + delta) ≤ a'.mem.len ∧ (∀ k, 1 ≤ k → k ≤ n → a'.at (delta + k) = a.at k) := by
  obtain ⟨_, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1116
  rw [checkedAdd_ok (by omega) (by omega), bind_ok]
  simp only []
  rw [if_neg (by omega), checkedMul_ok (by omega) (by omega), bind_ok,
    checkedAdd_ok (by omega) (by omega), bind_ok, checkedAdd_ok (by omega) (by omega), bind_ok]
  have hm := m1102_bounds (n := n) hn0 (by omega)
  split
  · rename_i hc
    have hq : Int.tdiv (a.mem.len - (n + delta)) 2 = (a.mem.len - (n + delta)) / 2 :=
      Int.tdiv_eq_ediv_of_nonneg (by omega)
    rw [hq, memCopy_ok (by omega) (by omega) (by omega), bind_ok]
    refine ⟨_, rfl, rfl, by simp <;> omega, by simp <;> omega, ?_⟩
    intro k hk1 hk2
    slot_arith
  · have hq : Int.tdiv (max (m1102 n) (n + 2 * delta + 1) - (n + delta)) 2 =
        (max (m1102 n) (n + 2 * delta + 1) - (n + delta)) / 2 :=
      Int.tdiv_eq_ediv_of_nonneg (by rw [Int.max_def]; split <;> omega)
    rw [hq, memCopy_ok (by omega) (by simp [m1114, Int.max_def]; split <;> omega) (by omega), bind_ok]
    refine ⟨_, rfl, rfl, by simp [Int.max_def]; split <;> omega,
      by simp [m1114, Int.max_def]; split <;> omega, ?_⟩
    intro k hk1 hk2
    slot_arith

theorem m1151_spec {a : Arr α} {n delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) :
    ∃ a', m1151 a delta = .ok a' ∧ IsVec a' (n + delta) ∧ Valid a' ∧
      (∀ k, 1 ≤ k → k ≤ n → a'.at (delta + k) = a.at k) := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1151
  rw [toInt_ok (by omega) (by omega), bind_ok]
  by_cases hz : delta = 0
  · subst hz
    rw [if_pos rfl]
    refine ⟨a, rfl, by simp [IsVec, hv], ha.2.1, fun k _ _ => by simp⟩
  · rw [if_neg hz, if_neg (by omega)]
    simp only [hn]
    rw [checkedAdd_ok (by omega) (by omega), bind_ok]
    split
    · refine ⟨_, rfl, rfl, ⟨by simp <;> omega, by simp [length] <;> omega, by simp [length] <;> omega⟩, ?_⟩
      intro k _ _
      slot_arith
    · obtain ⟨a', h1, h2, h3, h4, h5⟩ := m1116_spec ha hd0 hd1
      rw [h1, bind_ok, pure_ok]
      exact ⟨_, rfl, rfl, ⟨h3, by simp [length] <;> omega, by simp [length] <;> omega⟩, h5⟩

/-- `_growbeg!` contract: a negative count is an `ArgumentError`; otherwise the
vector grows by `delta` slots at the front, stays valid, and its last `n` slots
are the old ones. -/
def P1151 : Prop := ∀ {α : Type} (a : Arr α) (n delta : Int), VecOK a n →
    (typeminInt ≤ delta → delta < 0 → m1151 a delta = .error .argument) ∧
    (0 ≤ delta → delta ≤ 2 ^ 60 → ∃ a', m1151 a delta = .ok a' ∧ Valid a' ∧
      IsVec a' (n + delta) ∧ (contents a').drop delta.toNat = contents a)

theorem p1151 : P1151 := by
  intro α a n delta ha
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  refine ⟨fun h0 h1 => ?_, fun h0 h1 => ?_⟩
  · unfold m1151 toInt typeminInt typemaxInt
    unfold typeminInt at h0
    rw [if_pos (by omega), bind_ok, if_neg (by omega), if_pos (by omega)]
  · obtain ⟨a', e, hv', hvl, hp⟩ := m1151_spec ha h0 (by omega)
    exact ⟨a', e, hvl, hv', suffix_eq_of n delta hn0 h0 hn (length_vec a' _ hv') hp⟩

/-- `_growbeg_internal!` contract: on a valid vector the new ref's window holds
`n + delta` slots whose last `n` are the old ones; an invalid `ref`/`size` pair is
a `ConcurrencyViolationError`. -/
def P1116 : Prop := ∀ {α : Type} (a : Arr α) (n delta : Int), 0 ≤ delta → delta ≤ 2 ^ 60 →
    (VecOK a n → ∃ a', m1116 a delta n = .ok a' ∧
      Valid { a' with dims := [n + delta] } ∧ (contents { a' with dims := [n + delta] }).drop delta.toNat = contents a) ∧
    (0 ≤ n → n ≤ 2 ^ 60 → ¬ Valid a → length a = n → m1116 a delta n = .error .concurrency)

theorem p1116 : P1116 := by
  intro α a n delta h0 h1
  refine ⟨fun ha => ?_, fun hn0 hn1 hv hl => ?_⟩
  · obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
    obtain ⟨a', e, hd, ho', hw', hp⟩ := m1116_spec ha h0 (by omega)
    refine ⟨a', e, ⟨ho', by simp [length] <;> omega, by simp [length] <;> omega⟩, ?_⟩
    exact suffix_eq_of n delta hn0 h0 hn (by simp [length]) hp
  · unfold m1116
    rw [checkedAdd_ok (by omega) (by omega), bind_ok]
    simp only []
    unfold Valid at hv
    rw [if_pos (by omega)]

theorem m1230_spec {a : Arr α} {n i delta : Int} (ha : VecOK a n) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1152921504606846976) (hi0 : 1 ≤ i) (hi1 : i ≤ n + 1) :
    ∃ a', m1230 a i delta = .ok a' ∧ IsVec a' (n + delta) ∧ Valid a' ∧
      (∀ k, 1 ≤ k → k ≤ i - 1 → a'.at k = a.at k) ∧
      (∀ k, 1 ≤ k → k ≤ n - (i - 1) → a'.at (i - 1 + delta + k) = a.at (i - 1 + k)) := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1230
  rw [toInt_ok (by omega) (by omega), bind_ok, toInt_ok (by omega) (by omega), bind_ok]
  by_cases h1 : i = 1
  · subst h1
    rw [if_pos rfl]
    obtain ⟨a', e, h2, h3, h4⟩ := m1151_spec ha hd0 hd1
    exact ⟨a', e, h2, h3, fun k _ _ => by omega, fun k h5 h6 => by simpa using h4 k h5 (by omega)⟩
  rw [if_neg h1]
  simp only [hn]
  by_cases h2 : i = n + 1
  · subst h2
    rw [if_pos ⟨by unfold typemaxInt; omega, rfl⟩]
    obtain ⟨a', e, h3, h4, h5⟩ := m1212_spec ha hd0 hd1
    exact ⟨a', e, h3, h4, fun k h6 h7 => h5 k h6 (by omega), fun k _ _ => by omega⟩
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    checkedAdd_ok (by omega) (by omega), bind_ok, checkedAdd_ok (by omega) (by omega), bind_ok]
  have hq : Int.tdiv n 2 = n / 2 := Int.tdiv_eq_ediv_of_nonneg hn0
  rw [hq]
  split
  · rename_i hc
    rw [refCopy_ok (by omega) (by omega) (by omega), bind_ok, pure_ok]
    refine ⟨_, rfl, rfl, ⟨by simp [unsetLoop] <;> omega, by simp [length, unsetLoop] <;> omega,
      by simp [length, unsetLoop] <;> omega⟩, fun k _ _ => ?_, fun k _ _ => ?_⟩ <;> slot_arith
  split
  · rename_i hc hc2
    rw [memCopy_ok (by omega) (by omega) (by omega), bind_ok, pure_ok]
    refine ⟨_, rfl, rfl, ⟨by simp [unsetLoop] <;> omega, by simp [length, unsetLoop] <;> omega,
      by simp [length, unsetLoop] <;> omega⟩, fun k _ _ => ?_, fun k _ _ => ?_⟩ <;> slot_arith
  · rename_i hc hc2
    have hm := m1102_bounds (n := a.mem.len) (by omega) (by omega)
    rw [checkedMul_ok (by omega) (by omega), bind_ok, checkedAdd_ok (by omega) (by omega), bind_ok,
      checkedAdd_ok (by omega) (by omega), bind_ok]
    have hq2 : Int.tdiv (max (m1102 a.mem.len) (n + 2 * delta + 1) - (n + delta)) 2 =
        (max (m1102 a.mem.len) (n + 2 * delta + 1) - (n + delta)) / 2 :=
      Int.tdiv_eq_ediv_of_nonneg (by rw [Int.max_def]; split <;> omega)
    rw [hq2, refCopy_ok (by omega) (by simp [m1114, Int.max_def]; split <;> omega) (by omega), bind_ok,
      memCopy_ok (by omega) (by simp [m1114, Int.max_def]; split <;> omega) (by omega), bind_ok, pure_ok]
    refine ⟨_, rfl, rfl, ⟨by simp [Int.max_def]; split <;> omega, by simp [length] <;> omega,
      by simp [length, m1114, Int.max_def]; split <;> omega⟩, fun k _ _ => ?_, fun k _ _ => ?_⟩ <;> slot_arith

/-- `_growat!` contract: a negative count is an `ArgumentError`, an insertion point
outside `1:n+1` a `BoundsError`; otherwise `delta` slots open before position `i`
and every old slot keeps its relative order. -/
def P1230 : Prop := ∀ {α : Type} (a : Arr α) (n i delta : Int), VecOK a n →
    (typeminInt ≤ delta → delta < 0 → typeminInt ≤ i → i ≤ typemaxInt → m1230 a i delta = .error .argument) ∧
    (0 ≤ delta → delta ≤ 2 ^ 60 → typeminInt ≤ i → i ≤ typemaxInt → (i < 1 ∨ n + 1 < i) →
      m1230 a i delta = .error .bounds) ∧
    (0 ≤ delta → delta ≤ 2 ^ 60 → 1 ≤ i → i ≤ n + 1 → ∃ a', m1230 a i delta = .ok a' ∧ Valid a' ∧
      IsVec a' (n + delta) ∧ (contents a').take (i - 1).toNat = (contents a).take (i - 1).toNat ∧
      (contents a').drop (i - 1 + delta).toNat = (contents a).drop (i - 1).toNat)

theorem p1230 : P1230 := by
  intro α a n i delta ha
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  refine ⟨fun h0 h1 h2 h3 => ?_, fun h0 h1 h2 h3 h4 => ?_, fun h0 h1 h2 h3 => ?_⟩
  · unfold typeminInt typemaxInt at *
    unfold m1230
    rw [toInt_ok' (by omega) (by omega), bind_ok, toInt_ok' (by omega) (by omega), bind_ok]
    by_cases e1 : i = 1
    · subst e1; rw [if_pos rfl]
      unfold m1151; rw [toInt_ok' (by omega) (by omega), bind_ok, if_neg (by omega), if_pos (by omega)]
    rw [if_neg e1]
    simp only [hn]
    by_cases e2 : i = n + 1
    · rw [if_pos ⟨by unfold typemaxInt; omega, e2⟩]
      unfold m1212; rw [toInt_ok' (by omega) (by omega), bind_ok, if_pos (by omega)]
    rw [if_neg (by unfold typemaxInt; omega), if_pos (by omega)]
  · unfold typeminInt typemaxInt at *
    unfold m1230
    rw [toInt_ok' (by omega) (by omega), bind_ok, toInt_ok' (by omega) (by omega), bind_ok,
      if_neg (by omega)]
    simp only [hn]
    rw [if_neg (by unfold typemaxInt; omega), if_neg (by omega), if_pos (by omega)]
  · obtain ⟨a', e, hv', hvl, hp1, hp2⟩ := m1230_spec ha h0 (by omega) h2 h3
    have hl' := length_vec a' _ hv'
    refine ⟨a', e, hvl, hv', take_eq_of (i - 1) (by omega) (by omega) (by omega) hp1, ?_⟩
    exact drop_eq_of (i - 1) (i - 1 + delta) (by omega) (by omega) (by omega) (by omega)
      (fun k h5 h6 => hp2 k h5 (by omega))

theorem m1296_spec {a : Arr α} {n delta : Int} (ha : VecOK a n) (h0 : 0 ≤ delta) (h1 : delta ≤ n) :
    ∃ a', m1296 a delta = .ok a' ∧ IsVec a' (n - delta) ∧ Valid a' ∧ a'.mem.len = a.mem.len ∧
      ∀ k, 1 ≤ k → k ≤ n - delta → a'.at k = a.at k := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1296
  rw [toInt_ok (by omega) (by omega), bind_ok]
  simp only [hn]
  rw [uns_id (by omega) (by omega), uns_id (by omega) (by omega), if_neg (by omega), pure_ok]
  refine ⟨_, rfl, rfl, ⟨ho, by simp [length, hv] <;> omega, by simp [length, unsetLoop, hv] <;> omega⟩,
    rfl, fun k _ _ => ?_⟩
  slot_arith

theorem m1278_spec {a : Arr α} {n delta : Int} (ha : VecOK a n) (h0 : 0 ≤ delta) (h1 : delta ≤ n) :
    ∃ a', m1278 a delta = .ok a' ∧ IsVec a' (n - delta) ∧ Valid a' ∧ a'.mem.len = a.mem.len ∧
      ∀ k, 1 ≤ k → k ≤ n - delta → a'.at k = a.at (k + delta) := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1278
  rw [toInt_ok (by omega) (by omega), bind_ok]
  simp only [hn]
  rw [uns_id (by omega) (by omega), uns_id (by omega) (by omega), if_neg (by omega)]
  split
  · refine ⟨_, rfl, rfl, ⟨by simp [unsetLoop] <;> omega, by simp [length, hv] <;> omega,
      by simp [length, unsetLoop, hv] <;> omega⟩, rfl, fun k _ _ => ?_⟩
    slot_arith
  · refine ⟨_, rfl, rfl, ⟨by simp [unsetLoop] <;> omega, by simp [length, hv] <;> omega,
      by simp [length, unsetLoop, hv] <;> omega⟩, rfl, fun k _ _ => by omega⟩

theorem contents_take_append_drop {a a' : Arr α} (n i d : Int) (hn : length a = n) (hi : 1 ≤ i)
    (hd : 0 ≤ d) (hid : i + d ≤ n + 1) (hl : length a' = n - d)
    (hp1 : ∀ k, 1 ≤ k → k ≤ i - 1 → a'.at k = a.at k)
    (hp2 : ∀ k, i ≤ k → k ≤ n - d → a'.at k = a.at (k + d)) :
    contents a' = (contents a).take (i - 1).toNat ++ (contents a).drop (i - 1 + d).toNat := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [contents_length] at h1
    rw [getElem_contents]
    by_cases hj : j < (i - 1).toNat
    · rw [List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_take, getElem_contents]
      exact hp1 _ (by omega) (by omega)
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_drop, getElem_contents, List.length_take, contents_length]
      rw [hp2 _ (by omega) (by omega)]
      congr 1
      omega

theorem m276_vec {a : Arr α} {n : Int} (ha : VecOK a n) {doffs soffs c : Int} (hc : 0 ≤ c)
    (h1 : 1 ≤ doffs) (h2 : doffs + c - 1 ≤ n) (h3 : 1 ≤ soffs) (h4 : soffs + c - 1 ≤ n) :
    ∃ a', m276 a doffs a soffs c = .ok a' ∧ VecOK a' n ∧
      ∀ k, 1 ≤ k → k ≤ n → a'.at k = if doffs ≤ k ∧ k < doffs + c then a.at (k - doffs + soffs) else a.at k := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  obtain ⟨d', e, hd, hoff, hml, hp⟩ := p276 a a doffs soffs c ha.2.1 ha.2.1 hc h1 (by omega) h3 (by omega)
    (by omega) (by omega)
  refine ⟨d', e, ⟨hd.trans hv, ?_, ?_⟩, fun k k1 k2 => hp k k1 (by omega)⟩
  · have := ha.2.1; unfold Valid at *; rw [hoff, hml, show length d' = length a by simp [length, hd]]; exact this
  · unfold Small; rw [hml]; exact ha.2.2

theorem m1312_spec {a : Arr α} {n i delta : Int} (ha : VecOK a n) (hi0 : 1 ≤ i) (hi1 : i ≤ n)
    (hd0 : 0 ≤ delta) (hid : i + delta ≤ n + 1) :
    ∃ a', m1312 a i delta = .ok a' ∧ IsVec a' (n - delta) ∧ Valid a' ∧
      contents a' = (contents a).take (i - 1).toNat ++ (contents a).drop (i - 1 + delta).toNat := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1312
  rw [toInt_ok (by omega) (by omega), bind_ok]
  simp only [hn]
  rw [if_neg (by omega), if_neg (by omega),
    wrap64_id (x := n + 1) (by omega) (by omega),
    wrap64_id (x := n + 1 - i) (by omega) (by omega),
    if_neg (by omega), wrap64_id (by omega) (by omega)]
  split
  · rw [wrap64_id (by omega) (by omega)]
    obtain ⟨a1, e1, ha1, hp1⟩ := m276_vec ha (doffs := 1 + delta) (soffs := 1) (c := i - 1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [e1, bind_ok]
    obtain ⟨a2, e2, hv2, hval2, _, hp2⟩ := m1278_spec ha1 hd0 (by omega)
    refine ⟨a2, e2, hv2, hval2, ?_⟩
    apply contents_take_append_drop n i delta hn hi0 hd0 hid (length_vec a2 _ hv2)
    · intro k k1 k2; rw [hp2 k k1 (by omega), hp1 _ (by omega) (by omega), if_pos (by omega)]
      congr 1; omega
    · intro k k1 k2; rw [hp2 k (by omega) k2, hp1 _ (by omega) (by omega), if_neg (by omega)]
  · rw [wrap64_id (x := i + delta) (by omega) (by omega),
        wrap64_id (x := n + 1 - delta - i) (by omega) (by omega)]
    obtain ⟨a1, e1, ha1, hp1⟩ := m276_vec ha (doffs := i) (soffs := i + delta) (c := n + 1 - delta - i)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [e1, bind_ok]
    obtain ⟨a2, e2, hv2, hval2, _, hp2⟩ := m1296_spec ha1 hd0 (by omega)
    refine ⟨a2, e2, hv2, hval2, ?_⟩
    apply contents_take_append_drop n i delta hn hi0 hd0 hid (length_vec a2 _ hv2)
    · intro k k1 k2; rw [hp2 k k1 (by omega), hp1 _ (by omega) (by omega), if_neg (by omega)]
    · intro k k1 k2; rw [hp2 k (by omega) k2, hp1 _ (by omega) (by omega), if_pos (by omega)]
      congr 1; omega

/-- `_deleteat!(a, i, delta)` contract: a negative count is an `ArgumentError`, a
start outside `1:n` a `BoundsError`; for a window inside the vector the result
is the vector with exactly slots `i:i+delta-1` removed. -/
def P1312 : Prop := ∀ {α : Type} (a : Arr α) (n i delta : Int), VecOK a n →
    (typeminInt ≤ i → i ≤ typemaxInt → delta < 0 → m1312 a i delta = .error .argument) ∧
    (typeminInt ≤ i → i ≤ typemaxInt → 0 ≤ delta → (i < 1 ∨ n < i) → m1312 a i delta = .error .bounds) ∧
    (1 ≤ i → i ≤ n → 0 ≤ delta → i + delta ≤ n + 1 → ∃ a', m1312 a i delta = .ok a' ∧ Valid a' ∧
      IsVec a' (n - delta) ∧
      contents a' = (contents a).take (i - 1).toNat ++ (contents a).drop (i - 1 + delta).toNat)

theorem p1312 : P1312 := by
  intro α a n i delta ha
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  refine ⟨fun h0 h1 h2 => ?_, fun h0 h1 h2 h3 => ?_, fun h0 h1 h2 h3 => ?_⟩
  · unfold typeminInt typemaxInt at *
    unfold m1312; rw [toInt_ok' (by omega) (by omega), bind_ok, if_pos (by omega)]
  · unfold typeminInt typemaxInt at *
    unfold m1312; rw [toInt_ok' (by omega) (by omega), bind_ok]
    simp only [hn]
    rw [if_neg (by omega), if_pos (by omega)]
  · obtain ⟨a', e, hv', hval, hc⟩ := m1312_spec ha h0 h1 h2 h3
    exact ⟨a', e, hval, hv', hc⟩

end JuliaLean.MultidimCov.ArrayV2
