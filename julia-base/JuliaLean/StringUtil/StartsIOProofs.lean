import JuliaLean.StringUtil.StartsIO
import JuliaLean.IOBuffers.InvProofs
import JuliaLean.IOBuffers.OpProofsRead
import JuliaLean.IOBuffers.OpProofsSeek

/-!
`startswith(io, prefix::String)` on every reachable seekable, readable `IOBuffer` returns
whether `prefix` is a prefix of the unread bytes and leaves the position unchanged.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.IOBuffers JuliaLean.IOBuffers.OpP

theorem run_bind_ok {α β} {x : M α} {f : α → M β} {s s' : IOBuf} {a : α}
    (h : x.run s = .ok a s') : (x >>= f).run s = (f a).run s' := by
  have h' : x s = .ok a s' := h
  simp only [EStateM.run, bind, EStateM.bind, h']

theorem run_discard_ok {α} {x : M α} {s s' : IOBuf} {a : α}
    (h : x.run s = .ok a s') : (discard x).run s = .ok () s' := by
  have h' : x s = .ok a s' := h
  show discard x s = _
  rw [show discard x s = EStateM.map (fun _ => ()) x s from rfl]
  unfold EStateM.map
  rw [h']

theorem run_peek_ok {m : M Bool} {io s : IOBuf} {b : Bool}
    (h : m.run io = .ok b s) (hp : (position s).val = (position io).val) :
    result m io = some b ∧
      ∀ s', (∃ b', m.run io = .ok b' s') → (position s').val = (position io).val := by
  constructor
  · unfold result
    rw [h]
  · rintro s' ⟨b', h'⟩
    rw [h] at h'
    cases h'
    exact hp

theorem mark_run (io : IOBuf) : (mark).run io = .ok (position io) { io with mark := position io } := rfl

theorem inv_mark {io : IOBuf} (h : Inv io) (hs : io.seekable = true) :
    Inv { io with mark := position io } := by
  have f := invFacts h
  have hp := position_val h
  have hoc := h.oc_seekable hs
  exact { maxsize_nonneg := h.maxsize_nonneg, len_le := h.len_le, oc_ge := h.oc_ge,
          oc_seekable := h.oc_seekable, off_le_size := h.off_le_size,
          size_le_len := h.size_le_len, ptr_ge := h.ptr_ge, ptr_le := h.ptr_le,
          stored_le := h.stored_le,
          mark_ge := by show -1 ≤ (position io).val; omega,
          mark_le := by show (position io).val ≤ 2 ^ 62; omega,
          mark_pipe := by intro h'; exact absurd hs (by simp_all),
          reinit_state := h.reinit_state }

theorem inv_ptr {io : IOBuf} (h : Inv io) (hs : io.seekable = true)
    (p : I) (hp1 : io.ptr.val ≤ p.val)
    (hp2 : p.val ≤ io.size.val + 1) : Inv { io with ptr := p } := by
  have f := invFacts h
  exact { maxsize_nonneg := h.maxsize_nonneg, len_le := h.len_le, oc_ge := h.oc_ge,
          oc_seekable := h.oc_seekable, off_le_size := h.off_le_size,
          size_le_len := h.size_le_len,
          ptr_ge := by show (getOffset io).val + 1 ≤ p.val; omega,
          ptr_le := hp2, stored_le := h.stored_le, mark_ge := h.mark_ge, mark_le := h.mark_le,
          mark_pipe := by
            intro hs'
            exact absurd hs (by rw [hs']; decide),
          reinit_state := by
            intro hri
            obtain ⟨a, b, c⟩ := h.reinit_state hri
            exact ⟨by show p.val = 1; omega, b, c⟩ }

/-- `read(io, n)` on a readable buffer satisfying the invariant. -/
theorem readN_inv {io : IOBuf} (h : Inv io) (hr : io.readable = true) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∃ p : I, p.val = io.ptr.val + min (n : Int) (bytesavailable io).val ∧
      (readN (i n)).run io = .ok ((avail io).take (min n (avail io).length)) { io with ptr := p } := by
  have hal := avail_length h
  have hin : (i n).val = n := i_val (by omega) (by omega)
  have hm := imin_val (i n) (bytesavailable io)
  rw [hin] at hm
  let k := min n (avail io).length
  have hk : (imin (i n) (bytesavailable io)).val = (k : Int) := by
    clear h hr hn
    dsimp only [k]
    omega
  have hk0 : 0 ≤ (imin (i n) (bytesavailable io)).val := by
    rw [hk]
    exact Int.natCast_nonneg _
  have hkmax : (k : Int) ≤ 2 ^ 64 - 1 := by
    have hkn : k ≤ n := Nat.min_le_left _ _
    clear h hr hal hin hm hk hk0
    omega
  have hkba : (k : Int) ≤ (bytesavailable io).val := by
    have hkl : k ≤ (avail io).length := Nat.min_le_right _ _
    omega
  obtain ⟨v, hv1, hv2⟩ := toU_ok (k : Int) (Int.natCast_nonneg _) hkmax
  obtain ⟨p, hp, hrun⟩ := unsafeRead_run h hr v (by rw [hv2]; exact hkba)
  have hvnat : v.val.toNat = k := by rw [hv2, Int.toNat_natCast]
  refine ⟨p, by rw [hp, hv2, ← hk, hm], ?_⟩
  · rw [readN_run io (i n) hk0, readBang_run io _ v (by simpa only [hk, Int.toNat_natCast] using hv1),
      hrun, hvnat]

theorem reset_run {io : IOBuf} (hs : io.seekable = true) (hm : ismarked io = true) :
    (reset).run io = .ok io.mark
      { io with ptr := clampI (translateSeekPosition io io.mark) (getOffset io + i 1) (io.size + i 1),
                mark := i (-1) } := by
  simp [reset, hm, seek, hs, run_map] <;> rfl

/-- `startswith(io, prefix::String)` on a buffer satisfying the invariant. -/
theorem startswithStr_run {io : IOBuf} (h : Inv io) (hr : io.readable = true)
    (hs : io.seekable = true) (q : List UInt8) (hq : q.length ≤ 2 ^ 62) :
    ∃ s, (startswithStr q).run io = .ok (decide ((avail io).take q.length = q)) s ∧
      (position s).val = (position io).val ∧ ismarked s = false := by
  have f := invFacts h
  have hba := ba_val h
  have hal := avail_length h
  have hpos := position_val h
  have hoc := h.oc_seekable hs
  have h1 := inv_mark h hs
  obtain ⟨p, hp, hread⟩ := readN_inv h1 hr q.length hq
  have hba1 : (bytesavailable { io with mark := position io }).val = (bytesavailable io).val := rfl
  have hav1 : avail { io with mark := position io } = avail io := rfl
  rw [hav1] at hread
  change p.val = io.ptr.val + min (q.length : Int)
    (bytesavailable { io with mark := position io }).val at hp
  rw [hba1] at hp
  have hp' : io.ptr.val ≤ p.val ∧ p.val ≤ io.size.val + 1 := by
    clear h1 hread hav1 hba1
    omega
  have h2 := inv_ptr h1 hs p hp'.1 hp'.2
  have hm2 : ismarked { io with mark := position io, ptr := p } = true := by
    rw [ismarked_iff]; show 0 ≤ (position io).val; omega
  have hreset := reset_run (io := { io with mark := position io, ptr := p }) hs hm2
  have hsp := seek_pos h2 (position io)
  let mid := { io with mark := position io, ptr := p }
  let final := { mid with
    ptr := clampI (translateSeekPosition mid (position io))
      (getOffset mid + i 1) (mid.size + i 1), mark := i (-1) }
  refine ⟨final, ?_, ?_, ?_⟩
  · unfold startswithStr
    rw [run_bind_ok (run_discard_ok (mark_run io)), run_bind_ok hread,
      run_bind_ok (run_discard_ok hreset)]
    change EStateM.Result.ok ((avail io).take (min q.length (avail io).length) == q) final =
      EStateM.Result.ok (decide ((avail io).take q.length = q)) final
    rw [take_min_of_le _ _ _ (Nat.le_refl _)]
    apply congrArg (fun b : Bool => (EStateM.Result.ok b final : EStateM.Result IOErr IOBuf Bool))
    by_cases he : (avail io).take q.length = q <;> simp [he]
  ·
    have hc : (position { mid with
        ptr := clampI (translateSeekPosition mid (position io))
          (getOffset mid + i 1) (mid.size + i 1),
        mark := i (-1) }).val =
        (position { mid with
          ptr := clampI (translateSeekPosition mid (position io))
            (getOffset mid + i 1) (mid.size + i 1) }).val := rfl
    rw [hc, hsp]
    show max ((getOffset io).val + 1) (min (max (-2 ^ 63) (min ((position io).val + io.oc.val + 1)
      (2 ^ 63 - 1))) (io.size.val + 1)) - io.oc.val - 1 = (position io).val
    omega
  · change decide ((i (-1)).val ≥ 0) = false
    rw [im1]
    decide

/-- `startswith(io, prefix)` only peeks (its docstring points to `peek`): on every reachable
readable and seekable `IOBuffer` it returns whether `prefix` is a prefix of the unread bytes,
and the position afterwards is the position before. -/
def StartswithIoPeek : Prop :=
  ∀ io : IOBuf, Reachable io → io.readable = true → io.seekable = true →
    ∀ q : List UInt8, q.length ≤ 2 ^ 62 →
      result (startswithStr q) io = some (decide ((avail io).take q.length = q)) ∧
      ∀ s, (∃ b, (startswithStr q).run io = .ok b s) → (position s).val = (position io).val

theorem startswithIoPeek_proven : StartswithIoPeek := by
  intro io hr hrd hs q hq
  obtain ⟨s, hrun, hpos, _⟩ := startswithStr_run (reachable_inv io hr) hrd hs q hq
  exact run_peek_ok hrun hpos

/-! ## Registry -/

def startsioProofEntries : List JuliaLean.Registry.Entry := [
  { id := "stringutil-startswith-io-peek"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::IO, ::AbstractString)", "read(::IOBuffer, ::Integer)", "mark", "reset"]
    statement := "On every reachable readable and seekable IOBuffer, startswith(io, prefix::String) returns whether prefix is a prefix of the unread bytes, and the position afterwards equals the position before."
    source := "base/strings/util.jl:87-92 (startswith(io::IO, prefix) docstring, which points to `peek`)"
    status := .proven
    prop := ``StartswithIoPeek
    thm := some ``startswithIoPeek_proven
    notes := "Reachable buffers are those of the IOBuffers area (constructor plus any operations); reachable_inv supplies the invariant. The value compares bytes, so for a prefix that ends inside a character of the stream it is true while startswith(String, prefix) is false (startswith(IOBuffer(\"éx\"), \"\\xc3\") == true, startswith(\"éx\", \"\\xc3\") == false); not registered as a bug because the IO method is documented by bytes read. The caller's mark is not preserved: stringutil-startswith-io-mark." }
]

end JuliaLean.StringUtil
