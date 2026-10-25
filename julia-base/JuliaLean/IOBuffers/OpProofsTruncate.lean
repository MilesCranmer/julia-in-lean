import JuliaLean.IOBuffers.OpProofsBase

/-!
`truncate` on a seekable `IOBuffer` satisfying `Inv`: the argument checks, and the
shrinking, no-op, and growing (compact, resize, zero-fill) branches.
-/

namespace JuliaLean.IOBuffers

open JuliaLean

namespace OpP

/-- The zero-filling tail of the growing branch of `truncate`. -/
def fillTail (n : I) : M Unit := do
  let io ← get
  let hi := imin (i io.data.length) (n + getOffset io)
  let data ← lift (fillZero io.data (io.size + i 1) hi)
  set { io with data, size := hi }

theorem run_discard {α} (m : M α) (s : IOBuf) :
    (discard m).run s = match m.run s with
      | .ok _ s => .ok () s
      | .error e s => .error e s := by
  show EStateM.map _ m s = _
  simp only [EStateM.map, EStateM.run]
  cases m s <;> rfl

theorem mul_val {a b : I} (h1 : -2 ^ 63 ≤ a.val * b.val) (h2 : a.val * b.val ≤ 2 ^ 63 - 1) :
    (a * b).val = a.val * b.val := i_val h1 h2

theorem bitLength_le : ∀ fuel n, bitLength fuel n ≤ fuel
  | 0, _ => by simp [bitLength]
  | fuel + 1, n => by
    unfold bitLength
    split
    · omega
    · have := bitLength_le fuel (n / 2)
      omega

theorem overallocation_ge (x : I) (h1 : 0 ≤ x.val) (h2 : x.val ≤ 2 ^ 62 + 2 ^ 61) :
    x.val ≤ (overallocation x).val := by
  have hx : ¬ x.val < 0 := by omega
  unfold overallocation
  simp only [hx, ↓reduceIte]
  obtain ⟨k, hk⟩ : ∃ k, bitLength 64 x.val.toNat * 7 / 8 = k := ⟨_, rfl⟩
  rw [hk]
  have hk56 : k ≤ 56 := by have := bitLength_le 64 x.val.toNat; omega
  have hpn : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hk56
  have hP : (0 : Int) ≤ 2 ^ k ∧ (2 : Int) ^ k ≤ 2 ^ 56 :=
    ⟨by exact_mod_cast Nat.zero_le (2 ^ k), by exact_mod_cast hpn⟩
  clear hk hk56 hpn
  have hx' := I_bounds x
  have hpi : (i (2 ^ k)).val = 2 ^ k := i_val (by omega) (by omega)
  have h3 : (i 3).val = 3 := i_val (by decide) (by decide)
  have hm : (i (2 ^ k) * i 3).val = 2 ^ k * 3 := by
    rw [mul_val (by rw [hpi, h3]; omega) (by rw [hpi, h3]; omega), hpi, h3]
  have htd : (i (x.val.tdiv 8)).val = x.val / 8 := by
    rw [Int.tdiv_eq_ediv_of_nonneg h1]; exact i_val (by omega) (by omega)
  have hex : (i (2 ^ k) * i 3 + i (x.val.tdiv 8)).val = 2 ^ k * 3 + x.val / 8 := by
    rw [add_val (by rw [hm, htd]; omega) (by rw [hm, htd]; omega), hm, htd]
  have himax : imaxval.val = 2 ^ 63 - 1 := i_val (by decide) (by decide)
  clear hpi hm htd
  split
  · rw [himax]; omega
  · rw [add_val (by rw [hex]; omega) (by rw [hex]; omega), hex]; omega

theorem inv_mk {s : IOBuf} (hms : 0 ≤ s.maxsize.val) (hlen : s.data.length ≤ 2 ^ 62) (hoc : s.oc.val = 0)
    (hsz0 : 0 ≤ s.size.val) (hsz : s.size.val ≤ s.data.length) (hp1 : 1 ≤ s.ptr.val)
    (hp2 : s.ptr.val ≤ s.size.val + 1) (hst : s.size.val ≤ s.maxsize.val) (hm1 : -1 ≤ s.mark.val)
    (hm2 : s.mark.val ≤ 2 ^ 62) (hseek : s.seekable = true) (hri : s.reinit = false) : Inv s where
  maxsize_nonneg := hms
  len_le := hlen
  oc_ge := by omega
  oc_seekable := fun _ => by omega
  off_le_size := by rw [getOffset_val]; omega
  size_le_len := hsz
  ptr_ge := by rw [getOffset_val]; omega
  ptr_le := hp2
  stored_le := by rw [getOffset_val]; omega
  mark_ge := hm1
  mark_le := hm2
  mark_pipe := fun h => absurd (h.symm.trans hseek) (by decide)
  reinit_state := fun h => absurd (h.symm.trans hri) (by decide)

theorem getUsedSpan_seek {io : IOBuf} (hm : io.isMem = true) (hs : io.seekable = true) :
    getUsedSpan io = .ok (getOffset io + i 1, io.size) := by
  simp [getUsedSpan, hm, hs]

theorem slice_prefix (A B C : List UInt8) (c : Int) (hA : A = []) (hB : (B.length : Int) = c) :
    slice (A ++ B ++ C) 1 c = B := by
  subst hA
  unfold slice
  rw [List.nil_append, show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero,
    List.take_left' (by omega)]

theorem copyto_one {dest src : List UInt8} {so n : I} (hso : 1 ≤ so.val) (hn : 0 ≤ n.val)
    (h1 : n.val ≤ dest.length) (h2 : so.val + n.val - 1 ≤ src.length) :
    ∃ D, copyto dest (i 1) src so n = .ok D ∧ D.length = dest.length ∧
      slice D 1 n.val = slice src so.val (so.val + n.val - 1) := by
  unfold copyto
  simp only [i1]
  split
  · rename_i h0
    refine ⟨dest, rfl, rfl, ?_⟩
    rw [slice_nil (by omega), slice_nil (by omega)]
  · split
    · omega
    · split
      · refine ⟨_, rfl, ?_, ?_⟩
        · have hl := slice_length (d := src) (a := so.val) (b := so.val + n.val - 1) (by omega) h2 (by omega)
          simp only [List.length_append, List.length_take, List.length_drop]
          omega
        · apply slice_prefix _ _ _ _ (by simp)
          have hl := slice_length (d := src) (a := so.val) (b := so.val + n.val - 1) (by omega) h2 (by omega)
          omega
      · rename_i hb
        exact (hb ⟨by omega, by omega, hso, h2⟩).elim

theorem copyto_noarg (dest src : List UInt8) (d so n : I) (hn : 0 ≤ n.val) :
    ∀ msg, copyto dest d src so n ≠ .error (.jl (.argumentError msg)) := by
  intro msg he
  unfold copyto at he
  split at he
  · cases he
  · split at he
    · omega
    · split at he
      · cases he
      · cases he

theorem fillZero_noarg (d : List UInt8) (a b : I) :
    ∀ msg, fillZero d a b ≠ .error (.jl (.argumentError msg)) := by
  intro msg he
  unfold fillZero at he
  split at he
  · cases he
  · split at he
    · cases he
    · cases he

theorem compact_seek {io : IOBuf} (h : Inv io) (hm : io.isMem = true) (hs : io.seekable = true)
    (hri : io.reinit = false) :
    ∃ d s1, compact.run io = .ok d s1 ∧ Inv s1 ∧ s1.oc.val = 0 ∧ content s1 = content io ∧
      (position s1).val = (position io).val ∧ s1.size.val = io.size.val - (getOffset io).val ∧
      s1.isMem = true ∧ s1.seekable = true ∧ s1.reinit = false ∧ s1.maxsize = io.maxsize := by
  have f := invFacts h
  have hoc := h.oc_seekable hs
  have hgus := getUsedSpan_seek hm hs
  have hpos := position_val h
  have h1 : (getOffset io + i 1).val = (getOffset io).val + 1 := add_one_val (by omega)
  have hdel : (getOffset io + i 1 - i 1).val = (getOffset io).val := by
    rw [sub_one_val (by rw [h1]; omega), h1]; omega
  by_cases h0 : (getOffset io).val = 0
  · refine ⟨i 0, io, ?_, h, by omega, rfl, rfl, by omega, hm, hs, hri, rfl⟩
    simp [compact, hgus, lift, hdel, h0]
  · have hrl : (rangeLength (getOffset io + i 1) io.size).val = io.size.val - (getOffset io).val := by
      rw [rangeLength_val _ _ (by omega) (by omega) (by omega) (by omega), h1]; omega
    have hso : (getOffset io + i 1 - i 1 + i 1).val = (getOffset io).val + 1 := by
      rw [add_one_val (by rw [hdel]; omega), hdel]
    obtain ⟨D, hD, hDlen, hDs⟩ := copyto_one (dest := io.data) (src := io.data)
      (so := getOffset io + i 1 - i 1 + i 1) (n := rangeLength (getOffset io + i 1) io.size)
      (by omega) (by omega) (by omega) (by omega)
    have hcg : (getCompacted io).val = 0 := by
      rw [getCompacted_val io (by omega) (by omega)]; omega
    have hcd : (getOffset io + i 1 - i 1 - getOffset io).val = 0 := by
      rw [sub_val (by rw [hdel]; omega) (by rw [hdel]; omega), hdel]; omega
    have hng : (-getCompacted io).val = 0 := by
      rw [neg_val (by rw [hcg]; omega) (by rw [hcg]; omega), hcg]; omega
    have hoc1 : (-getCompacted io - (getOffset io + i 1 - i 1 - getOffset io)).val = 0 := by
      rw [sub_val (by rw [hng, hcd]; omega) (by rw [hng, hcd]; omega), hng, hcd]; omega
    have hp1 : (io.ptr - (getOffset io + i 1 - i 1)).val = io.ptr.val - (getOffset io).val := by
      rw [sub_val (by rw [hdel]; omega) (by rw [hdel]; omega), hdel]
    have hs1 : (io.size - (getOffset io + i 1 - i 1)).val = io.size.val - (getOffset io).val := by
      rw [sub_val (by rw [hdel]; omega) (by rw [hdel]; omega), hdel]
    obtain ⟨s1, hs1def⟩ : ∃ s1 : IOBuf, s1 =
        { io with
          data := D
          oc := -getCompacted io - (getOffset io + i 1 - i 1 - getOffset io)
          ptr := io.ptr - (getOffset io + i 1 - i 1)
          size := io.size - (getOffset io + i 1 - i 1) } :=
      ⟨_, rfl⟩
    have ed : s1.data = D := by rw [hs1def]
    have eoc : s1.oc.val = 0 := by rw [hs1def]; exact hoc1
    have ep : s1.ptr.val = io.ptr.val - (getOffset io).val := by rw [hs1def]; exact hp1
    have es : s1.size.val = io.size.val - (getOffset io).val := by rw [hs1def]; exact hs1
    have ems : s1.maxsize = io.maxsize := by rw [hs1def]
    have emk : s1.mark = io.mark := by rw [hs1def]
    have eflags : s1.isMem = io.isMem ∧ s1.seekable = io.seekable ∧ s1.reinit = io.reinit := by
      rw [hs1def]; exact ⟨rfl, rfl, rfl⟩
    have hgo1 : (getOffset s1).val = 0 := by rw [getOffset_val, eoc]; rfl
    refine ⟨getOffset io + i 1 - i 1, s1, ?_, ?_, eoc, ?_, ?_, es, eflags.1.trans hm,
      eflags.2.1.trans hs, eflags.2.2.trans hri, ems⟩
    · rw [hs1def]
      simp [compact, hgus, lift, hdel, h0, hD, run_map]
    · refine inv_mk (by rw [ems]; omega) (by rw [ed]; omega) eoc (by omega) (by rw [ed]; omega)
        (by omega) (by omega) (by rw [ems]; omega) (by rw [emk]; omega) (by rw [emk]; omega)
        (eflags.2.1.trans hs) (eflags.2.2.trans hri)
    · unfold content
      rw [hgo1, es, ed, show (0 : Int) + 1 = 1 from rfl]
      rw [hrl, hso] at hDs
      rw [hDs]
      congr 1
      omega
    · rw [position_eq s1 (by omega) (by omega), ep, eoc, hpos]
      omega

theorem resize_seek {s : IOBuf} (h : Inv s) (hm : s.isMem = true) (hs : s.seekable = true)
    (x : I) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 2 ^ 62 + 2 ^ 61)
    (hcx : s.size.val - (getOffset s).val ≤ x.val) (hms : 1 ≤ s.maxsize.val) :
    ∃ s2, (resize x false).run s = .ok () s2 ∧ min s.maxsize.val x.val ≤ s2.data.length ∧
      (s2.data.length : Int) ≤ s.maxsize.val ∧ s2.oc.val = 0 ∧
      s2.ptr.val = s.ptr.val - (getOffset s).val ∧ s2.size.val = s.size.val - (getOffset s).val ∧
      slice s2.data 1 s2.size.val = content s := by
  have f := invFacts h
  have hoc := h.oc_seekable hs
  have hgus := getUsedSpan_seek hm hs
  have hov := overallocation_ge x (by omega) hx2
  have hN := imin_val s.maxsize (overallocation x)
  have hN0 : ¬ (imin s.maxsize (overallocation x)).val < 0 := by omega
  have hN1 : ¬ (imin s.maxsize (overallocation x)).val = 0 := by omega
  have hsim : similarData s (imin s.maxsize (overallocation x)) =
      .ok (List.replicate (imin s.maxsize (overallocation x)).val.toNat 0) := by
    simp [similarData, stringMemory, hm, hN0]
  have h1 : (getOffset s + i 1).val = (getOffset s).val + 1 := add_one_val (by omega)
  have hdel : (getOffset s + i 1 - i 1).val = (getOffset s).val := by
    rw [sub_one_val (by rw [h1]; omega), h1]; omega
  have hrl : (rangeLength (getOffset s + i 1) s.size).val = s.size.val - (getOffset s).val := by
    rw [rangeLength_val _ _ (by omega) (by omega) (by omega) (by omega), h1]; omega
  have hcg : (getCompacted s).val = 0 := by
    rw [getCompacted_val s (by omega) (by omega)]; omega
  have hcd : (getOffset s + i 1 - i 1 - getOffset s).val = 0 := by
    rw [sub_val (by rw [hdel]; omega) (by rw [hdel]; omega), hdel]; omega
  have hng : (-getCompacted s).val = 0 := by
    rw [neg_val (by rw [hcg]; omega) (by rw [hcg]; omega), hcg]; omega
  have hoc1 : (-getCompacted s - (getOffset s + i 1 - i 1 - getOffset s)).val = 0 := by
    rw [sub_val (by rw [hng, hcd]; omega) (by rw [hng, hcd]; omega), hng, hcd]; omega
  have hp1 : (s.ptr - (getOffset s + i 1 - i 1)).val = s.ptr.val - (getOffset s).val := by
    rw [sub_val (by rw [hdel]; omega) (by rw [hdel]; omega), hdel]
  have hRlen : (List.replicate (imin s.maxsize (overallocation x)).val.toNat (0 : UInt8)).length =
      (imin s.maxsize (overallocation x)).val.toNat := List.length_replicate
  obtain ⟨D2, hD2run, hD2len, hD2s⟩ : ∃ D2 : List UInt8,
      (resize x false).run s = .ok ()
        { s with
          data := D2
          oc := -getCompacted s - (getOffset s + i 1 - i 1 - getOffset s)
          ptr := s.ptr - (getOffset s + i 1 - i 1)
          size := rangeLength (getOffset s + i 1) s.size } ∧
      D2.length = (imin s.maxsize (overallocation x)).val.toNat ∧
      slice D2 1 (s.size.val - (getOffset s).val) = content s := by
    by_cases hc0 : (rangeLength (getOffset s + i 1) s.size).val = 0
    · refine ⟨_, ?_, hRlen, ?_⟩
      · simp [resize, hgus, lift, hsim, hN1, hc0]
      · rw [slice_nil (by omega)]
        exact (slice_nil (by omega)).symm
    · obtain ⟨D, hD, hDlen, hDs⟩ := copyto_one
        (dest := List.replicate (imin s.maxsize (overallocation x)).val.toNat 0) (src := s.data)
        (so := getOffset s + i 1) (n := rangeLength (getOffset s + i 1) s.size)
        (by omega) (by omega) (by rw [hRlen]; omega) (by omega)
      refine ⟨D, ?_, by rw [hDlen, hRlen], ?_⟩
      · simp [resize, hgus, lift, hsim, hN1, hc0, hD]
      · rw [hrl, h1] at hDs
        rw [hDs]
        unfold content
        congr 1
        omega
  refine ⟨_, hD2run, ?_, ?_, hoc1, hp1, hrl, ?_⟩
  · show min s.maxsize.val x.val ≤ (D2.length : Int)
    rw [hD2len]; omega
  · show (D2.length : Int) ≤ s.maxsize.val
    rw [hD2len]; omega
  · show slice D2 1 (rangeLength (getOffset s + i 1) s.size).val = content s
    rw [hrl]; exact hD2s

theorem resize_noarg {s : IOBuf} (h : Inv s) (hm : s.isMem = true) (hs : s.seekable = true) (x : I) :
    ∀ msg s', (resize x false).run s ≠ .error (.jl (.argumentError msg)) s' := by
  intro msg s' he
  have f := invFacts h
  have hoc := h.oc_seekable hs
  have hgus := getUsedSpan_seek hm hs
  have h1 : (getOffset s + i 1).val = (getOffset s).val + 1 := add_one_val (by omega)
  have hrl : (rangeLength (getOffset s + i 1) s.size).val = s.size.val - (getOffset s).val := by
    rw [rangeLength_val _ _ (by omega) (by omega) (by omega) (by omega), h1]; omega
  by_cases hN0 : (imin s.maxsize (overallocation x)).val < 0
  · have hsim : similarData s (imin s.maxsize (overallocation x)) =
        .error (.jl (.inexactError "convert")) := by
      simp [similarData, stringMemory, hm, hN0]
    simp [resize, hgus, lift, hsim, run_throw] at he
  · have hsim : similarData s (imin s.maxsize (overallocation x)) =
        .ok (List.replicate (imin s.maxsize (overallocation x)).val.toNat 0) := by
      simp [similarData, stringMemory, hm, hN0]
    by_cases hN1 : (imin s.maxsize (overallocation x)).val = 0
    · simp [resize, hgus, lift, hsim, hN1] at he
    · by_cases hc0 : (rangeLength (getOffset s + i 1) s.size).val = 0
      · simp [resize, hgus, lift, hsim, hN1, hc0] at he
      · cases hcp : copyto (List.replicate (imin s.maxsize (overallocation x)).val.toNat 0) (i 1) s.data
            (getOffset s + i 1) (rangeLength (getOffset s + i 1) s.size) with
        | ok D => simp [resize, hgus, lift, hsim, hN1, hc0, hcp] at he
        | error e =>
          have hne := copyto_noarg (List.replicate (imin s.maxsize (overallocation x)).val.toNat 0)
            s.data (i 1) (getOffset s + i 1) (rangeLength (getOffset s + i 1) s.size) (by omega) msg
          rw [hcp] at hne
          simp [resize, hgus, lift, hsim, hN1, hc0, hcp, run_throw] at he
          exact hne (by rw [he.1])

theorem fillTail_noarg (n : I) (s : IOBuf) :
    ∀ msg s', (fillTail n).run s ≠ .error (.jl (.argumentError msg)) s' := by
  intro msg s' he
  cases hf : fillZero s.data (s.size + i 1) (imin (i s.data.length) (n + getOffset s)) with
  | ok D => simp [fillTail, lift, hf] at he
  | error e =>
    have hne := fillZero_noarg s.data (s.size + i 1) (imin (i s.data.length) (n + getOffset s)) msg
    rw [hf] at hne
    simp [fillTail, lift, hf, run_throw] at he
    exact hne (by rw [he.1])

theorem bind_fill_noarg {s : IOBuf} {x n : I}
    (hr : ∀ msg s', (resize x false).run s ≠ .error (.jl (.argumentError msg)) s') :
    ∀ msg s', (resize x false >>= fun _ => fillTail n).run s ≠ .error (.jl (.argumentError msg)) s' := by
  intro msg s' he
  rw [EStateM.run_bind] at he
  cases hres : (resize x false).run s with
  | ok a s2 =>
    rw [hres] at he
    exact fillTail_noarg n s2 msg s' he
  | error e s2 =>
    rw [hres] at he
    simp at he
    exact hr msg s2 (by rw [hres, he.1])

theorem fillTail_ok (n : I) (s2 : IOBuf) (c : Int) (hsz : s2.size.val = c) (hc0 : 0 ≤ c)
    (hcn : c < n.val) (hnl : n.val ≤ s2.data.length) (hl : (s2.data.length : Int) ≤ 2 ^ 63 - 1)
    (hoc : s2.oc.val = 0) (hn : n.val ≤ 2 ^ 60) :
    (fillTail n).run s2 = .ok ()
      { s2 with
        data := s2.data.take c.toNat ++ List.replicate (n.val - c).toNat 0 ++ s2.data.drop n.val.toNat
        size := n } := by
  have hgo : (getOffset s2).val = 0 := by rw [getOffset_val, hoc]; rfl
  have hil : (i s2.data.length).val = s2.data.length := i_val (by omega) (by omega)
  have hhi : imin (i s2.data.length) (n + getOffset s2) = n := by
    apply Subtype.ext
    rw [imin_val, hil, add_val (by rw [hgo]; omega) (by rw [hgo]; omega), hgo]
    omega
  have hsz1 : (s2.size + i 1).val = c + 1 := by rw [add_one_val (by omega), hsz]
  have hfz : fillZero s2.data (s2.size + i 1) n =
      .ok (s2.data.take c.toNat ++ List.replicate (n.val - c).toNat 0 ++ s2.data.drop n.val.toNat) := by
    unfold fillZero
    rw [hsz1]
    split
    · omega
    · split
      · rw [show (c + 1 - 1).toNat = c.toNat by omega,
          show (n.val - (c + 1) + 1).toNat = (n.val - c).toNat by omega]
      · rename_i hb
        exact (hb ⟨by omega, by omega⟩).elim
  simp [fillTail, lift, hhi, hfz]

theorem slice_one (l : List UInt8) (n : Int) : slice l 1 n = l.take n.toNat := by
  unfold slice
  rw [show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero, show n - 1 + 1 = n by omega]

theorem pad_take (l : List UInt8) (n : Nat) (h : l.length ≤ n) :
    (l ++ List.replicate n 0).take n = l ++ List.replicate (n - l.length) 0 := by
  rw [List.take_append, List.take_of_length_le h, List.take_replicate]
  congr 2
  omega

theorem grow_result {io s : IOBuf} (h : Inv s) (hm : s.isMem = true) (hs : s.seekable = true)
    (n x : I) (hrun : (truncate n).run io = (resize x false >>= fun _ => fillTail n).run s)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 2 ^ 62 + 2 ^ 61) (hnx : n.val ≤ x.val)
    (hnm : n.val ≤ s.maxsize.val) (hcn : s.size.val - (getOffset s).val < n.val) (hn : n.val ≤ 2 ^ 60)
    (hcont : content s = content io) (hpos : (position s).val = (position io).val) :
    ∃ sF, (truncate n).run io = .ok () sF ∧
      content sF = (content io ++ List.replicate n.val.toNat 0).take n.val.toNat ∧
      (position sF).val = min (position io).val n.val := by
  have f := invFacts h
  have hoc := h.oc_seekable hs
  have hps := position_val h
  obtain ⟨s2, hres, hl1, hl2, hoc2, hp2, hsz2, hsl2⟩ :=
    resize_seek h hm hs x hx1 hx2 (by omega) (by omega)
  have hfill := fillTail_ok n s2 (s.size.val - (getOffset s).val) hsz2 (by omega) hcn
    (by omega) (by have := I_bounds s.maxsize; omega) hoc2 hn
  have hclen : ((content s).length : Int) = s.size.val - (getOffset s).val := by
    have := slice_length (d := s.data) (a := (getOffset s).val + 1) (b := s.size.val)
      (by omega) (by omega) (by omega)
    unfold content
    omega
  have hA : s2.data.take (s.size.val - (getOffset s).val).toNat = content io := by
    rw [← hcont, ← hsl2, slice_one, hsz2]
  refine ⟨{ s2 with
      data := s2.data.take (s.size.val - (getOffset s).val).toNat ++
        List.replicate (n.val - (s.size.val - (getOffset s).val)).toNat 0 ++ s2.data.drop n.val.toNat
      size := n }, ?_, ?_, ?_⟩
  · rw [hrun, EStateM.run_bind, hres]
    exact hfill
  · show slice (s2.data.take (s.size.val - (getOffset s).val).toNat ++
        List.replicate (n.val - (s.size.val - (getOffset s).val)).toNat 0 ++ s2.data.drop n.val.toNat)
      ((getOffset s2).val + 1) n.val = _
    rw [getOffset_val s2, hoc2, show max (0 : Int) 0 + 1 = 1 from rfl, slice_one, hA,
      pad_take _ _ (by rw [← hcont]; omega)]
    rw [List.take_left' (by simp only [List.length_append, List.length_replicate]; rw [← hcont]; omega)]
    congr 2
    rw [← hcont]
    omega
  · show (position s2).val = _
    rw [position_eq s2 (by omega) (by omega)]
    omega

theorem truncate_arg_err (io : IOBuf) (n : I)
    (hc : io.writable = false ∨ io.seekable = false ∨ n.val < 0 ∨ n.val > io.maxsize.val) :
    ∃ msg, (truncate n).run io = .error (.jl (.argumentError msg)) io := by
  cases hw : io.writable
  · simp [truncate, hw, throwArg]
  · cases hs : io.seekable
    · simp [truncate, hw, hs, throwArg]
    · by_cases h0 : n.val < 0
      · simp [truncate, hw, hs, h0, throwArg]
      · have h1 : n.val > io.maxsize.val := by
          rcases hc with hc | hc | hc | hc
          · rw [hw] at hc; cases hc
          · rw [hs] at hc; cases hc
          · exact absurd hc h0
          · exact hc
        have h1' : io.maxsize.val < n.val := h1
        simp [truncate, hw, hs, h0, h1, h1', throwArg]

theorem truncate_reinit {io : IOBuf} (hm : io.isMem = true) (hw : io.writable = true)
    (hs : io.seekable = true) (hri : io.reinit = true) (n : I) (hn0 : 0 ≤ n.val)
    (hnm : n.val ≤ io.maxsize.val) :
    (truncate n).run io = .ok () { io with data := List.replicate n.val.toNat 0, reinit := false, size := n } := by
  have h0 : ¬ n.val < 0 := by omega
  have h1 : ¬ n.val > io.maxsize.val := by omega
  have h1' : ¬ io.maxsize.val < n.val := by omega
  simp [truncate, hw, hs, hri, h0, h1, h1', similarData, stringMemory, hm, lift]

theorem truncate_eq {io : IOBuf} (hw : io.writable = true) (hs : io.seekable = true)
    (hri : io.reinit = false) (n : I) (hn0 : 0 ≤ n.val) (hnm : n.val ≤ io.maxsize.val)
    (hlt : ¬ n.val < (io.size - getOffset io).val) (hgt : ¬ n.val > (io.size - getOffset io).val) :
    (truncate n).run io = .ok () io := by
  have h0 : ¬ n.val < 0 := by omega
  have h1 : ¬ n.val > io.maxsize.val := by omega
  have h1' : ¬ io.maxsize.val < n.val := by omega
  have hgt' : ¬ (io.size - getOffset io).val < n.val := hgt
  simp [truncate, hw, hs, hri, h0, h1, h1', hlt, hgt, hgt']

theorem truncate_lt {io : IOBuf} (hw : io.writable = true) (hs : io.seekable = true)
    (hri : io.reinit = false) (n : I) (hn0 : 0 ≤ n.val) (hnm : n.val ≤ io.maxsize.val)
    (hlt : n.val < (io.size - getOffset io).val) :
    ∃ s, (truncate n).run io = .ok () s ∧ s.data = io.data ∧ s.oc = io.oc ∧
      s.size = n + getOffset io ∧ s.ptr = imin io.ptr (n + getOffset io + i 1) := by
  have h0 : ¬ n.val < 0 := by omega
  have h1 : ¬ n.val > io.maxsize.val := by omega
  have h1' : ¬ io.maxsize.val < n.val := by omega
  by_cases hmk : (translateSeekPosition io io.mark).val > (n + getOffset io).val
  · refine ⟨{ io with mark := i (-1), size := n + getOffset io, ptr := imin io.ptr (n + getOffset io + i 1) },
      ?_, rfl, rfl, rfl, rfl⟩
    have hmk' : (n + getOffset io).val < (translateSeekPosition io io.mark).val := hmk
    simp [truncate, hw, hs, hri, h0, h1, h1', hlt, hmk, hmk']
  · refine ⟨{ io with size := n + getOffset io, ptr := imin io.ptr (n + getOffset io + i 1) },
      ?_, rfl, rfl, rfl, rfl⟩
    have hmk' : ¬ (n + getOffset io).val < (translateSeekPosition io io.mark).val := hmk
    simp [truncate, hw, hs, hri, h0, h1, h1', hlt, hmk, hmk']

theorem truncate_gt_c {io s1 : IOBuf} {d : I} (hw : io.writable = true) (hs : io.seekable = true)
    (hri : io.reinit = false) (n : I) (hn0 : 0 ≤ n.val) (hnm : n.val ≤ io.maxsize.val)
    (hgt : n.val > (io.size - getOffset io).val) (hcond : (n + getOffset io).val > io.maxsize.val)
    (hcomp : compact.run io = .ok d s1) :
    (truncate n).run io = (resize (n + getOffset s1) false >>= fun _ => fillTail n).run s1 := by
  have h0 : ¬ n.val < 0 := by omega
  have h1 : ¬ n.val > io.maxsize.val := by omega
  have h1' : ¬ io.maxsize.val < n.val := by omega
  have hlt : ¬ n.val < (io.size - getOffset io).val := by omega
  have hgt' : (io.size - getOffset io).val < n.val := hgt
  have hcond' : io.maxsize.val < (n + getOffset io).val := hcond
  simp [truncate, hw, hs, hri, h0, h1, h1', hlt, hgt, hgt', hcond, hcond', run_discard, hcomp, fillTail]

theorem truncate_gt_nc {io : IOBuf} (hw : io.writable = true) (hs : io.seekable = true)
    (hri : io.reinit = false) (n : I) (hn0 : 0 ≤ n.val) (hnm : n.val ≤ io.maxsize.val)
    (hgt : n.val > (io.size - getOffset io).val) (hcond : ¬ (n + getOffset io).val > io.maxsize.val) :
    (truncate n).run io = (resize (n + getOffset io) false >>= fun _ => fillTail n).run io := by
  have h0 : ¬ n.val < 0 := by omega
  have h1 : ¬ n.val > io.maxsize.val := by omega
  have h1' : ¬ io.maxsize.val < n.val := by omega
  have hlt : ¬ n.val < (io.size - getOffset io).val := by omega
  have hgt' : (io.size - getOffset io).val < n.val := hgt
  have hcond' : ¬ io.maxsize.val < (n + getOffset io).val := hcond
  simp [truncate, hw, hs, hri, h0, h1, h1', hlt, hgt, hgt', hcond, hcond', fillTail]

theorem resultOf_ne {α} {m : M α} {io : IOBuf} {e : IOErr} (h : ∀ s', m.run io ≠ .error e s') :
    resultOf m io ≠ .error e := by
  unfold resultOf
  cases hr : m.run io with
  | ok a s => simp
  | error e' s =>
    intro he
    have : e' = e := Except.error.inj he
    subst this
    exact h s hr

theorem truncate_noarg {io : IOBuf} (h : Inv io) (hm : io.isMem = true) (hw : io.writable = true)
    (hs : io.seekable = true) (n : I) (hn0 : 0 ≤ n.val) (hnm : n.val ≤ io.maxsize.val) :
    ∀ msg, resultOf (truncate n) io ≠ .error (.jl (.argumentError msg)) := by
  intro msg
  cases hri : io.reinit
  · by_cases hlt : n.val < (io.size - getOffset io).val
    · obtain ⟨s, hrun, -⟩ := truncate_lt hw hs hri n hn0 hnm hlt
      rw [resultOf_ok hrun]
      intro he
      cases he
    · by_cases hgt : n.val > (io.size - getOffset io).val
      · by_cases hcond : (n + getOffset io).val > io.maxsize.val
        · obtain ⟨d, s1, hcomp, hinv1, -, -, -, -, hm1, hs1, -, -⟩ := compact_seek h hm hs hri
          apply resultOf_ne
          rw [truncate_gt_c hw hs hri n hn0 hnm hgt hcond hcomp]
          exact bind_fill_noarg (resize_noarg hinv1 hm1 hs1 _) msg
        · apply resultOf_ne
          rw [truncate_gt_nc hw hs hri n hn0 hnm hgt hcond]
          exact bind_fill_noarg (resize_noarg h hm hs _) msg
      · rw [resultOf_ok (truncate_eq hw hs hri n hn0 hnm hlt hgt)]
        intro he
        cases he
  · rw [resultOf_ok (truncate_reinit hm hw hs hri n hn0 hnm)]
    intro he
    cases he

theorem truncate_B {io : IOBuf} (h : Inv io) (hm : io.isMem = true) (hw : io.writable = true)
    (hs : io.seekable = true) (n : I) (hn0 : 0 ≤ n.val) (hnm : n.val ≤ io.maxsize.val)
    (hnb : n.val ≤ 2 ^ 60) :
    ∃ sF, (truncate n).run io = .ok () sF ∧
      content sF = (content io ++ List.replicate n.val.toNat 0).take n.val.toNat ∧
      (position sF).val = min (position io).val n.val := by
  have f := invFacts h
  have hoc := h.oc_seekable hs
  have hpos := position_val h
  have hcs : (io.size - getOffset io).val = io.size.val - (getOffset io).val :=
    sub_val (by omega) (by omega)
  have hclen : ((content io).length : Int) = io.size.val - (getOffset io).val := by
    have := slice_length (d := io.data) (a := (getOffset io).val + 1) (b := io.size.val)
      (by omega) (by omega) (by omega)
    unfold content
    omega
  cases hri : io.reinit
  · by_cases hlt : n.val < (io.size - getOffset io).val
    · obtain ⟨s, hrun, ed, eoc, esz, ep⟩ := truncate_lt hw hs hri n hn0 hnm hlt
      have hno : (n + getOffset io).val = n.val + (getOffset io).val := add_val (by omega) (by omega)
      have hno1 : (n + getOffset io + i 1).val = n.val + (getOffset io).val + 1 := by
        rw [add_one_val (by omega), hno]
      have hp : s.ptr.val = min io.ptr.val (n.val + (getOffset io).val + 1) := by
        rw [ep, imin_val, hno1]
      have hsz : s.size.val = n.val + (getOffset io).val := by rw [esz, hno]
      have hgo : getOffset s = getOffset io := by unfold getOffset; rw [eoc]
      have hoc' : s.oc.val = io.oc.val := by rw [eoc]
      refine ⟨s, hrun, ?_, ?_⟩
      · rw [List.take_append_of_le_length (by omega)]
        unfold content
        rw [hgo, ed, hsz]
        unfold slice
        rw [List.take_take]
        congr 1
        omega
      · rw [position_eq s (by omega) (by omega)]
        omega
    · by_cases hgt : n.val > (io.size - getOffset io).val
      · have hno : (n + getOffset io).val = n.val + (getOffset io).val := add_val (by omega) (by omega)
        by_cases hcond : (n + getOffset io).val > io.maxsize.val
        · obtain ⟨d, s1, hcomp, hinv1, hoc1, hcont1, hpos1, hsz1, hm1, hs1, -, hms1⟩ :=
            compact_seek h hm hs hri
          have hgo1 : (getOffset s1).val = 0 := by rw [getOffset_val, hoc1]; rfl
          have hx : (n + getOffset s1).val = n.val := by
            rw [add_val (by rw [hgo1]; omega) (by rw [hgo1]; omega), hgo1]; omega
          exact grow_result hinv1 hm1 hs1 n (n + getOffset s1)
            (truncate_gt_c hw hs hri n hn0 hnm hgt hcond hcomp)
            (by omega) (by omega) (by omega) (by rw [hms1]; omega) (by omega) hnb hcont1 hpos1
        · exact grow_result h hm hs n (n + getOffset io)
            (truncate_gt_nc hw hs hri n hn0 hnm hgt hcond)
            (by omega) (by omega) (by omega) hnm (by omega) hnb rfl rfl
      · refine ⟨io, truncate_eq hw hs hri n hn0 hnm hlt hgt, ?_, ?_⟩
        · rw [List.take_left' (by omega)]
        · omega
  · have hst := h.reinit_state hri
    refine ⟨_, truncate_reinit hm hw hs hri n hn0 hnm, ?_, ?_⟩
    · have hc0 : content io = [] := slice_nil (by omega)
      rw [hc0, List.nil_append, List.take_replicate, Nat.min_self]
      unfold content
      rw [getOffset_val]
      dsimp only
      rw [hst.2.2, show max (0 : Int) 0 + 1 = 1 from rfl, slice_one, List.take_replicate, Nat.min_self]
    · show (position io).val = _
      omega

end OpP

open OpP

theorem truncateSpec_of_inv (hinv : ∀ io, Reachable io → Inv io) : TruncateSpec := by
  intro io hr hm n hn
  have h := hinv io hr
  have hn1 := hn.1
  have hn2 := hn.2
  have hin : (i n).val = n := i_val (by omega) (by omega)
  have hargs : ¬ (io.writable = false ∨ io.seekable = false ∨ n < 0 ∨ n > io.maxsize.val) →
      io.writable = true ∧ io.seekable = true ∧ 0 ≤ n ∧ n ≤ io.maxsize.val := by
    intro hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases hw' : io.writable
      · exact absurd (Or.inl hw') hc
      · rfl
    · cases hs' : io.seekable
      · exact absurd (Or.inr (Or.inl hs')) hc
      · rfl
    · exact Classical.byContradiction fun h0 => hc (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Classical.byContradiction fun h0 => hc (Or.inr (Or.inr (Or.inr (by omega))))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨msg, hmsg⟩
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨hw, hs, hn0, hnm⟩ := hargs hc
    exact truncate_noarg h hm hw hs (i n) (by omega) (by omega) msg hmsg
  · intro hc
    obtain ⟨msg, hmsg⟩ := truncate_arg_err io (i n) (by rw [hin]; exact hc)
    exact ⟨msg, resultOf_err hmsg⟩
  · intro hnb hok
    have hb : ((bound : Nat) : Int) = 2 ^ 60 := by decide
    have hc : ¬ (io.writable = false ∨ io.seekable = false ∨ n < 0 ∨ n > io.maxsize.val) := by
      intro hc
      obtain ⟨msg, hmsg⟩ := truncate_arg_err io (i n) (by rw [hin]; exact hc)
      rw [resultOf_err hmsg] at hok
      cases hok
    obtain ⟨hw, hs, hn0, hnm⟩ := hargs hc
    obtain ⟨sF, hrun, hcF, hpF⟩ := truncate_B h hm hw hs (i n) (by omega) (by omega) (by omega)
    rw [stateOf_ok hrun]
    rw [hin] at hcF hpF
    exact ⟨hcF, hpF⟩

end JuliaLean.IOBuffers
