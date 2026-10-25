import JuliaLean.IOBuffers.InvProofsBase

/-!
`SInv` is preserved by the buffer-management functions (`compact`, `resize`, `ensureroom`)
and by the writes, which never access memory outside `data`.
-/

namespace JuliaLean.IOBuffers.InvP

open JuliaLean JuliaLean.IOBuffers

attribute [local irreducible] wrapInt

theorem usedSpan_err {s : IOBuf} (hm : s.isMem = false) :
    getUsedSpan s = .error (.jl (.methodError "get_used_span")) := by
  unfold getUsedSpan; rw [hm]; rfl

theorem usedSpan_ok {s : IOBuf} {K : Int} (h : SInv s K) (hm : s.isMem = true) :
    ∃ a : I, getUsedSpan s = .ok (a, s.size) ∧ max 0 s.oc.val + 1 ≤ a.val ∧ a.val ≤ s.ptr.val ∧
      (s.seekable = true → a.val = max 0 s.oc.val + 1) ∧
      (s.seekable = false → 0 ≤ s.mark.val → a.val ≤ s.mark.val + s.oc.val + 1) := by
  facts h
  unfold getUsedSpan
  rw [hm, if_neg (show ¬ ((!true) = true) by decide)]
  cases hs : s.seekable
  · rw [if_neg Bool.false_ne_true]
    by_cases hmk : s.mark.val > -1
    · rw [if_pos hmk]
      have hp := h.pipe hs (by omega)
      refine ⟨_, rfl, ?_, ?_, nofun, fun _ _ => ?_⟩ <;> vo
    · rw [if_neg hmk]
      exact ⟨_, rfl, by omega, by omega, nofun, fun _ hm' => absurd hm' (by omega)⟩
  · rw [if_pos (show true = true from rfl)]
    have := h.seek hs
    exact ⟨_, rfl, by vo, by vo, fun _ => by vo, nofun⟩

theorem compacted_sinv {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) (a : I)
    (h1 : max 0 s.oc.val + 1 ≤ a.val) (h2 : a.val ≤ s.ptr.val)
    (h3 : s.seekable = true → a.val = max 0 s.oc.val + 1)
    (h4 : s.seekable = false → 0 ≤ s.mark.val → a.val ≤ s.mark.val + s.oc.val + 1)
    (d : List UInt8) (z : I) (hz : z.val = s.size.val - (a.val - 1))
    (hd1 : z.val ≤ d.length) (hd2 : (d.length : Int) ≤ 2 ^ 62) :
    SInv { s with data := d, oc := -getCompacted s - (a - i 1 - getOffset s),
                  ptr := s.ptr - (a - i 1), size := z } K ∧
    z.val - (-getCompacted s - (a - i 1 - getOffset s)).val = s.size.val - s.oc.val := by
  facts h
  have hoc : (-getCompacted s - (a - i 1 - getOffset s)).val = s.oc.val - (a.val - 1) := by vo
  have hp : (s.ptr - (a - i 1)).val = s.ptr.val - (a.val - 1) := by vo
  refine ⟨⟨?_, ?_, fun hs => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hs hm => ?_, fun hr => ?_, ?_⟩,
    ?_⟩
  all_goals (try simp only [hoc, hp, hz])
  all_goals first
    | omega
    | (have := h3 hs; have := h.seek hs; omega)
    | (have := h.pipe hs hm; have := h4 hs hm; omega)
    | (have := h.re hr; omega)

theorem compact_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec compact s (fun _ s' => SInv s' K ∧
      (∃ d o p z, s' = { s with data := d, oc := o, ptr := p, size := z }) ∧
      s'.data.length = s.data.length ∧ s'.size.val - s'.oc.val = s.size.val - s.oc.val)
      (Err K) := by
  unfold compact
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure]
  by_cases hm : s.isMem = true
  · obtain ⟨a, ha, h1, h2, h3, h4⟩ := usedSpan_ok h hm
    rw [ha, spec_lift_ok]
    dsimp only
    split
    · refine ⟨h, ⟨_, _, _, _, rfl⟩, ?_, ?_⟩ <;> first | rfl | trivial
    · facts h
      have hL : (rangeLength a s.size).val = s.size.val - a.val + 1 :=
        v_rangeLength _ _ (by omega) (by omega)
      refine spec_copyto (by omega) (by vo) (by vo) (by vo) (by vo) (fun r hr => ?_)
      have hz : (s.size - (a - i 1)).val = s.size.val - (a.val - 1) := by vo
      obtain ⟨hS, hrel⟩ := compacted_sinv h hK a h1 h2 h3 h4 r (s.size - (a - i 1)) hz
        (by rw [hr]; omega) (by rw [hr]; omega)
      exact ⟨hS, ⟨_, _, _, _, rfl⟩, hr, hrel⟩
  · rw [usedSpan_err (by simpa using hm), spec_lift_error]; exact ⟨noob_jl _, h⟩

theorem resize_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60)
    (newSize : I) (exact : Bool) (ns : I)
    (hns : (if exact then newSize else imin s.maxsize (overallocation newSize)) = ns)
    (hpos : 0 < ns.val) (hle : ns.val ≤ 2 ^ 62) (hL : s.size.val - max 0 s.oc.val ≤ ns.val) :
    Spec (resize newSize exact) s (fun _ s' => SInv s' K ∧
      (∃ d o p z, s' = { s with data := d, oc := o, ptr := p, size := z }) ∧
      s'.size.val - s'.oc.val = s.size.val - s.oc.val) (Err K) := by
  unfold resize
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure]
  rw [hns]
  by_cases hm : s.isMem = true
  · obtain ⟨a, ha, h1, h2, h3, h4⟩ := usedSpan_ok h hm
    rw [ha, spec_lift_ok]
    dsimp only
    refine spec_similarData (by omega) (fun _ => ?_) (fun hm' => by rw [hm] at hm'; cases hm')
    rw [if_neg (show ¬ ns.val = 0 by omega)]
    facts h
    have hL' : (rangeLength a s.size).val = s.size.val - a.val + 1 :=
      v_rangeLength _ _ (by omega) (by omega)
    have hlen : ((List.replicate ns.val.toNat (0 : UInt8)).length : Int) = ns.val := by
      simp only [List.length_replicate]; omega
    split
    · obtain ⟨hS, hrel⟩ := compacted_sinv h hK a h1 h2 h3 h4 (List.replicate ns.val.toNat 0)
        (rangeLength a s.size) (by omega) (by omega) (by omega)
      exact ⟨hS, ⟨_, _, _, _, rfl⟩, hrel⟩
    · refine spec_copyto (by omega) (by vo) (by vo) (by omega) (by omega) (fun r hr => ?_)
      obtain ⟨hS, hrel⟩ := compacted_sinv h hK a h1 h2 h3 h4 r (rangeLength a s.size)
        (by omega) (by rw [hr]; omega) (by rw [hr]; omega)
      exact ⟨hS, ⟨_, _, _, _, rfl⟩, hrel⟩
  · rw [usedSpan_err (by simpa using hm), spec_lift_error]; exact ⟨noob_jl _, h⟩

theorem bitLength_le : ∀ (f n : Nat), bitLength f n ≤ f
  | 0, _ => Nat.le_refl 0
  | f + 1, n => by
    unfold bitLength
    split
    · omega
    · have := bitLength_le f (n / 2); omega

theorem overalloc_spec (x : I) (h0 : 0 ≤ x.val) (h1 : x.val ≤ 2 ^ 61 + 2 ^ 60) :
    x.val ≤ (overallocation x).val ∧ (overallocation x).val ≤ 2 ^ 62 := by
  have hb := bitLength_le 64 x.val.toNat
  have hP1 : 2 ^ 0 ≤ 2 ^ (bitLength 64 x.val.toNat * 7 / 8) :=
    Nat.pow_le_pow_right (by decide) (Nat.zero_le _)
  have hP2 : 2 ^ (bitLength 64 x.val.toNat * 7 / 8) ≤ 2 ^ 56 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have e : (2 : Int) ^ (bitLength 64 x.val.toNat * 7 / 8) =
      ((2 ^ (bitLength 64 x.val.toNat * 7 / 8) : Nat) : Int) := by
    rw [Int.natCast_pow]; rfl
  have htd : x.val.tdiv 8 = x.val / 8 := Int.tdiv_eq_ediv_of_nonneg h0
  unfold overallocation
  simp only [show ¬ x.val < 0 by omega, ↓reduceIte, e, htd]
  generalize (2 ^ (bitLength 64 x.val.toNat * 7 / 8) : Nat) = P at hP1 hP2 ⊢
  split
  · next hc => vsimp at hc; omega
  · vo

theorem reallocate_spec {s : IOBuf} {K : Int} {nshort : U} (h : SInv s K)
    (hK : K ≤ 2 ^ 61 + 2 ^ 60) (hre : s.writable = true → s.reinit = true)
    (hn : nshort.val ≤ 2 ^ 60) :
    Spec (ensureroomReallocate nshort) s (fun _ s' => SInv s' K ∧ s'.reinit = false) (Err K) := by
  facts h
  have := U.bounds nshort
  unfold ensureroomReallocate
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure, throwArg, spec_throw]
  cases hw : s.writable
  · rw [if_pos (show (!false) = true from rfl)]
    exact ⟨noob_jl _, h⟩
  · have hre' := h.re (hre hw)
    rw [if_neg (show ¬ ((!true) = true) by decide)]
    refine spec_similarData (by vo) (fun _ => ⟨?_, by first | rfl | trivial⟩)
      (fun _ => ⟨noob_jl _, h⟩)
    sinv_close h

theorem slowpath_spec {s : IOBuf} {K : Int} {nshort : U} {avail : I} (h : SInv s K)
    (hK : K + nshort.val ≤ 2 ^ 61 + 2 ^ 60) (hn : nshort.val ≤ 2 ^ 60)
    (st : Int) (hst1 : max 0 s.oc.val ≤ st) (hst2 : st ≤ s.size.val)
    (hav : avail.val = min (s.data.length - st) (s.maxsize.val - (st - max 0 s.oc.val)))
    (hlt : avail.val < nshort.val) :
    Spec (ensureroomSlowpath nshort avail) s
      (fun _ s' => SInv s' K ∧ s'.reinit = s.reinit) (Err K) := by
  have hnb := U.bounds nshort
  have hK' : K ≤ 2 ^ 61 + 2 ^ 60 := by omega
  facts h
  unfold ensureroomSlowpath
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure, spec_discard]
  by_cases hm : s.isMem = true
  · obtain ⟨a, ha, h1, h2, h3, h4⟩ := usedSpan_ok h hm
    rw [ha, spec_lift_ok]
    dsimp only
    split
    · exact (compact_spec h hK').mono
        (fun _ s' ⟨hs', ⟨_, _, _, _, he⟩, _, _⟩ => ⟨hs', by rw [he]⟩) (fun _ _ x => x)
    · rename_i hnc
      clear hnc
      refine spec_toI (by omega) (by omega) (fun n hnv => ?_)
      have hdes : (i ↑s.data.length + n - avail).val =
          s.data.length + nshort.val - avail.val := by vo
      generalize i ↑s.data.length + n - avail = D at hdes ⊢
      refine (Classical.em (D.val > s.maxsize.val)).elim (fun hgt0 => ?_) (fun hgt0 => ?_)
      · rw [if_pos hgt0]
        have hgt := hgt0
        rw [hdes] at hgt
        have tail : ∀ s1 : IOBuf, SInv s1 K → s1.maxsize = s.maxsize →
            s1.data.length = s.data.length → s1.reinit = s.reinit →
            (s1.data.length : Int) < s1.maxsize.val →
            Spec (resize s1.maxsize true) s1 (fun _ s' => SInv s' K ∧ s'.reinit = s.reinit)
              (Err K) := by
          intro s1 hs1 hms hl hr1 hlt1
          rw [hms, hl] at hlt1
          have := hs1.stored; have := hs1.offsz
          refine (resize_spec hs1 hK' s1.maxsize true s1.maxsize rfl ?_ ?_ ?_).mono
            (fun _ s' ⟨hs', ⟨_, _, _, _, he⟩, _⟩ => ⟨hs', by rw [he]; exact hr1⟩)
            (fun _ _ x => x)
          · rw [hms]; omega
          · rw [hms]; omega
          · omega
        split
        · refine (compact_spec h hK').mono (fun _ s1 ⟨hs1, ⟨_, _, _, _, he⟩, hl, _⟩ => ?_)
            (fun _ _ x => x)
          have hms : s1.maxsize = s.maxsize := by rw [he]
          have hr1 : s1.reinit = s.reinit := by rw [he]
          split
          · next hlt1 => exact tail s1 hs1 hms hl hr1 hlt1
          · exact ⟨hs1, hr1⟩
        · split
          · next hlt1 => exact tail s h rfl rfl rfl hlt1
          · exact ⟨h, by first | rfl | trivial⟩
      · rw [if_neg hgt0]
        have hle := hgt0
        rw [hdes] at hle
        have hdpos : 0 ≤ D.val := by omega
        have hdle : D.val ≤ 2 ^ 61 + 2 ^ 60 := by omega
        obtain ⟨ho1, ho2⟩ := overalloc_spec _ hdpos hdle
        refine (resize_spec h hK' _ false _ (if_neg Bool.false_ne_true) ?_ ?_ ?_).mono
          (fun _ s' ⟨hs', ⟨_, _, _, _, he⟩, _⟩ => ⟨hs', by rw [he]⟩) (fun _ _ x => x)
        all_goals rw [v_imin]; omega
  · rw [usedSpan_err (by simpa using hm), spec_lift_error]; exact ⟨noob_jl _, h⟩

theorem ensureroom_spec {s : IOBuf} {K : Int} {nshort : U} (h : SInv s K)
    (hK : K + nshort.val ≤ 2 ^ 61 + 2 ^ 60) (hn : nshort.val ≤ 2 ^ 60) :
    Spec (ensureroom nshort) s (fun _ s' => SInv s' K ∧ s'.reinit = false) (Err K) := by
  have hnb := U.bounds nshort
  have hK' : K ≤ 2 ^ 61 + 2 ^ 60 := by omega
  facts h
  unfold ensureroom
  simp only [spec_bind, spec_get, spec_ite, spec_pure]
  cases hw : s.writable
  · rw [if_pos (show (!false || s.reinit) = true from rfl)]
    exact reallocate_spec h hK' (fun hw' => by rw [hw] at hw'; cases hw') hn
  · cases hr : s.reinit
    · rw [if_neg (show ¬ ((!true || false) = true) by decide)]
      cases hap : s.append
      · rw [if_neg Bool.false_ne_true]
        split
        · next hlt =>
          vsimp at hlt
          exact (slowpath_spec h hK hn (s.ptr.val - 1) (by omega) (by omega) (by vo)
            (by vsimp; omega)).mono (fun _ s' ⟨h1, h2⟩ => ⟨h1, h2.trans hr⟩) (fun _ _ x => x)
        · exact ⟨h, rfl⟩
      · rw [if_pos (show true = true from rfl)]
        split
        · next hlt =>
          vsimp at hlt
          exact (slowpath_spec h hK hn s.size.val (by omega) (by omega) (by vo)
            (by vsimp; omega)).mono (fun _ s' ⟨h1, h2⟩ => ⟨h1, h2.trans hr⟩) (fun _ _ x => x)
        · exact ⟨h, rfl⟩
    · rw [if_pos (show (!true || true) = true from rfl)]
      exact reallocate_spec h hK' (fun _ => hr) hn

theorem unsafeWrite_spec {s : IOBuf} {K : Int} {src : List UInt8} (h : SInv s K)
    (hK : K + src.length ≤ 2 ^ 61 + 2 ^ 60) (hn : src.length ≤ 2 ^ 60) :
    Spec (unsafeWrite src) s (fun _ s' => SInv s' (K + src.length)) (Err (K + src.length)) := by
  unfold unsafeWrite
  simp only [spec_bind, spec_get, spec_set, spec_pure]
  have hu : (u (src.length : Int)).val = src.length := by vsimp
  refine (ensureroom_spec h (by rw [hu]; omega) (by rw [hu]; omega)).mono
    (fun _ s1 hs1 => ?_) (Err.mono (by omega))
  have h1 := hs1.1
  have hr1 := hs1.2
  facts h1
  cases hap : s1.append
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine spec_writeAt (by vo) (by vo) (fun r hrl => ?_)
    sinv_close h1
  · simp only [eq_self_iff_true, ↓reduceIte]
    refine spec_writeAt (by vo) (by vo) (fun r hrl => ?_)
    sinv_close h1

theorem writeByte_spec {s : IOBuf} {K : Int} {b : UInt8} (h : SInv s K)
    (hK : K + 1 ≤ 2 ^ 61 + 2 ^ 60) :
    Spec (writeByte b) s (fun _ s' => SInv s' (K + 1)) (Err (K + 1)) := by
  unfold writeByte
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure]
  have hu : (u 1).val = 1 := by vsimp
  refine (ensureroom_spec h (by rw [hu]; omega) (by rw [hu]; omega)).mono
    (fun _ s1 ⟨h1, hr1⟩ => ?_) (Err.mono (by omega))
  facts h1
  cases hap : s1.append
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · exact h1.mono (by omega)
    · next hle =>
      vsimp at hle
      refine spec_setChecked (fun r hrl hk1 hk2 => ?_) ⟨noob_jl _, h1.mono (by omega)⟩
      sinv_close h1
  · simp only [eq_self_iff_true, ↓reduceIte]
    split
    · exact h1.mono (by omega)
    · next hle =>
      vsimp at hle
      refine spec_setChecked (fun r hrl hk1 hk2 => ?_) ⟨noob_jl _, h1.mono (by omega)⟩
      vsimp at hk1 hk2
      sinv_close h1

end JuliaLean.IOBuffers.InvP
