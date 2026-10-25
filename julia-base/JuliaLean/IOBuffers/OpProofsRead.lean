import JuliaLean.IOBuffers.OpProofsBase

/-!
`read`, `readbytes!`, `readuntil`, `readline` and `take!` on a buffer satisfying `Inv`.
-/

namespace JuliaLean.IOBuffers

open JuliaLean

namespace OpP

theorem readN_run (io : IOBuf) (nb : I) (h0 : 0 ≤ (imin nb (bytesavailable io)).val) :
    (readN nb).run io = (readBang (imin nb (bytesavailable io)).val.toNat).run io := by
  have hn : ¬ (imin nb (bytesavailable io)).val < 0 := by omega
  simp [readN, stringMemory, hn, lift]

theorem readBang_run (io : IOBuf) (k : Nat) (v : U) (hv : toU k = .ok v) :
    (readBang k).run io = (unsafeRead v).run io := by
  simp [readBang, hv, lift]

theorem readuntil_run {io : IOBuf} (h : Inv io) (d : UInt8) (keep : Bool) :
    (readuntil d keep).run io = .ok ((avail io).take
      (if !keep ∧ findOrLen (avail io) d > 0 ∧ (avail io).getD (findOrLen (avail io) d - 1) 0 = d
        then findOrLen (avail io) d - 1 else findOrLen (avail io) d))
      { io with ptr := io.ptr + i (findOrLen (avail io) d) } := by
  have hp := pending_eq h
  unfold readuntil
  simp only [EStateM.run_bind, EStateM.run_get, hp, lift] <;> rfl

theorem readline_run {io : IOBuf} (h : Inv io) (keep : Bool) :
    (readline keep).run io = .ok ((avail io).take
      (if !keep ∧ findOrLen (avail io) 0x0a > 0 ∧ (avail io).getD (findOrLen (avail io) 0x0a - 1) 0 = 0x0a then
        if findOrLen (avail io) 0x0a - 1 > 0 ∧ (avail io).getD (findOrLen (avail io) 0x0a - 2) 0 = 0x0d
        then findOrLen (avail io) 0x0a - 2 else findOrLen (avail io) 0x0a - 1
      else findOrLen (avail io) 0x0a))
      { io with ptr := io.ptr + i (findOrLen (avail io) 0x0a) } := by
  have hp := pending_eq h
  unfold readline
  simp only [EStateM.run_bind, EStateM.run_get, hp, lift] <;> rfl

theorem take_run {io : IOBuf} (h : Inv io) (hm : io.isMem = true) (hw : io.writable = true) :
    take.run io = .ok (if io.seekable then content io else avail io)
      (resetTaken { io with mark := i (-1) }) := by
  have f := invFacts h
  have hba := ba_val h
  cases hs : io.seekable
  · by_cases hz : (bytesavailable io).val = 0
    · have hnil : avail io = [] := slice_nil (by omega)
      have hz' : (io.size - io.ptr + i 1).val = 0 := hz
      simp [take, bytesavailable, hm, hw, hs, hz', hnil, run_map]
    · have hwb : wrapBytes io.data io.ptr (bytesavailable io) = .ok (avail io) := by
        unfold wrapBytes
        rw [if_pos ⟨by omega, by omega⟩]
        congr 1
        unfold avail
        congr 1
        omega
      have hz' : ¬ (io.size - io.ptr + i 1).val = 0 := hz
      have hwb' : wrapBytes io.data io.ptr (io.size - io.ptr + i 1) = .ok (avail io) := hwb
      simp [take, bytesavailable, hm, hw, hs, hz', hwb', lift, run_map]
  · have hfs := filesize_val h hs
    have hfsd : filesize io = io.size - imax (i 0) io.oc := by simp [filesize, getOffset, hs]
    by_cases hz : (filesize io).val = 0
    · have hnil : content io = [] := slice_nil (by omega)
      have hz' : (io.size - imax (i 0) io.oc).val = 0 := by rw [← hfsd]; exact hz
      simp [take, filesize, getOffset, hm, hw, hs, hz', hnil, run_map]
    · by_cases hri : io.reinit = true
      · have := h.reinit_state hri
        have hnil : content io = [] := slice_nil (by omega)
        simp [take, filesize, getOffset, hm, hw, hs, hri, hnil, run_map]
      · have hri' : io.reinit = false := by simpa using hri
        have h1 : (getOffset io + i 1).val = (getOffset io).val + 1 := add_one_val (by omega)
        have hwb : wrapBytes io.data (getOffset io + i 1) (filesize io) = .ok (content io) := by
          unfold wrapBytes
          rw [if_pos ⟨by omega, by omega⟩, h1]
          congr 1
          unfold content
          congr 1
          omega
        have hz' : ¬ (io.size - imax (i 0) io.oc).val = 0 := by rw [← hfsd]; exact hz
        have hwb' : wrapBytes io.data (imax (i 0) io.oc + i 1) (io.size - imax (i 0) io.oc) =
            .ok (content io) := by rw [← hfsd]; exact hwb
        simp [take, filesize, getOffset, hm, hw, hs, hz', hri', hwb', lift, run_map]

theorem reset_position (io : IOBuf) : (position (resetTaken io)).val = 0 := by
  show (i 1 - i 0 - i 1).val = 0
  decide

theorem reset_ba (io : IOBuf) : (bytesavailable (resetTaken io)).val = 0 := by
  show (i 0 - i 1 + i 1).val = 0
  decide

theorem reset_fs (io : IOBuf) : (filesize (resetTaken io)).val = 0 := by
  unfold filesize
  split
  · show (i 0 - imax (i 0) (i 0)).val = 0
    decide
  · exact reset_ba io

theorem reset_mark (io : IOBuf) : ismarked (resetTaken { io with mark := i (-1) }) = false := by
  show decide ((i (-1)).val ≥ 0) = false
  decide

end OpP

open OpP

theorem readSpec_of_inv (hinv : ∀ io, Reachable io → Inv io) : ReadSpec := by
  intro io hr hrd
  have h := hinv io hr
  have f := invFacts h
  have hal := avail_length h
  have hba := ba_val h
  have hpos := position_val h
  refine ⟨?_, ?_, ?_⟩
  · intro n hn0 hn1
    have hin : (i n).val = n := i_val (by omega) (by omega)
    have hm := imin_val (i n) (bytesavailable io)
    rw [hin] at hm
    obtain ⟨v, hv1, hv2⟩ :=
      toU_ok ((imin (i n) (bytesavailable io)).val.toNat : Int) (by omega) (by omega)
    obtain ⟨p, hp, hrun⟩ := unsafeRead_run h hrd v (by omega)
    have hk : v.val.toNat = min n.toNat (avail io).length := by omega
    have hrunN : (readN (i n)).run io = .ok ((avail io).take v.val.toNat) { io with ptr := p } := by
      rw [readN_run io (i n) (by omega), readBang_run io _ v hv1, hrun]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [resultOf_ok hrunN, hk, take_min_of_le _ _ _ (Nat.le_refl _)]
    · rw [stateOf_ok hrunN, avail_adv h p v.val.toNat (by omega) (by omega), hk,
        drop_min_of_le _ _ _ (Nat.le_refl _)]
    · rw [stateOf_ok hrunN, position_ptr io p (by omega) (by omega), hpos]
      omega
    · obtain ⟨w, hw1, hw2⟩ := toU_ok (imin (i n) (bytesavailable io)).val (by omega) (by omega)
      obtain ⟨p', hp', hrun'⟩ := unsafeRead_run h hrd w (by omega)
      have hrunB : (readbytes (i n)).run io =
          .ok (imin (i n) (bytesavailable io), (avail io).take w.val.toNat) { io with ptr := p' } := by
        simp [readbytes, hrd, hw1, lift, hrun', run_map]
      have he : imin (i n) (bytesavailable io) = i (min n (bytesavailable io).val) := by
        apply Subtype.ext
        rw [hm, i_val (by omega) (by omega)]
      have hk' : w.val.toNat = min n.toNat (avail io).length := by omega
      rw [resultOf_ok hrunB, he, hk', take_min_of_le _ _ _ (Nat.le_refl _)]
  · intro he
    have hl0 : ((avail io).length : Int) = 0 := by rw [he]; rfl
    have hgt : io.ptr.val > io.size.val := by omega
    have h1 : readByte.run io = .error .eofError io := by simp [readByte, hrd, hgt]
    have h2 : peekByte.run io = .error .eofError io := by simp [peekByte, hrd, hgt]
    exact ⟨resultOf_err h1, resultOf_err h2⟩
  · intro b rest he
    have hlen : ((avail io).length : Int) ≥ 1 := by rw [he, List.length_cons]; omega
    have hle : ¬ io.ptr.val > io.size.val := by omega
    have hread : readAt io.data io.ptr 1 = .ok [b] := by
      rw [readAt_avail h 1 (by omega), he]
      rfl
    have hrunR : readByte.run io = .ok b { io with ptr := io.ptr + i 1 } := by
      simp [readByte, hrd, hle, hread, lift, run_map]
    have hadd : (io.ptr + i 1).val = io.ptr.val + 1 := add_one_val (by omega)
    have hget : getChecked io.data io.ptr = .ok b := by
      have ht : (List.drop (io.ptr.val - 1).toNat io.data).take (io.size.val - io.ptr.val + 1).toNat =
          b :: rest := he
      unfold getChecked
      rw [if_pos ⟨by omega, by omega⟩, getD_eq_drop_headD, headD_of_take_eq ht]
    have hrunP : peekByte.run io = .ok b io := by
      simp [peekByte, hrd, hle, hget, lift]
    refine ⟨resultOf_ok hrunR, ?_, resultOf_ok hrunP, stateOf_ok hrunP⟩
    rw [stateOf_ok hrunR, avail_adv h (io.ptr + i 1) 1 (by omega) (by omega), he]
    rfl

theorem readUntilSpec_of_inv (hinv : ∀ io, Reachable io → Inv io) : ReadUntilSpec := by
  intro io hr _ d keep
  have h := hinv io hr
  have f := invFacts h
  have hal := avail_length h
  have hba := ba_val h
  have hle := findOrLen_le (avail io) d
  have hle' := findOrLen_le (avail io) 0x0a
  have hadd : ∀ k : Nat, k ≤ (avail io).length → (io.ptr + i k).val = io.ptr.val + k :=
    fun k hk => ptr_add_val h k (by omega)
  have hru := readuntil_run h d keep
  have hrl := readline_run h keep
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [resultOf_ok hru, readuntil_take]
  · rw [stateOf_ok hru, avail_adv h (io.ptr + i (findOrLen (avail io) d)) (findOrLen (avail io) d)
      (by omega) (hadd _ hle), drop_findOrLen]
  · rw [resultOf_ok hrl, readline_take]
  · rw [stateOf_ok hrl, avail_adv h (io.ptr + i (findOrLen (avail io) 0x0a)) (findOrLen (avail io) 0x0a)
      (by omega) (hadd _ hle'), drop_findOrLen]

theorem takeSpec_of_inv (hinv : ∀ io, Reachable io → Inv io) : TakeSpec := by
  intro io hr hm hw
  have h := hinv io hr
  have hrun := take_run h hm hw
  rw [resultOf_ok hrun, stateOf_ok hrun]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · exact reset_position { io with mark := i (-1) }
  · exact reset_ba { io with mark := i (-1) }
  · exact reset_fs { io with mark := i (-1) }
  · exact reset_mark io

end JuliaLean.IOBuffers
