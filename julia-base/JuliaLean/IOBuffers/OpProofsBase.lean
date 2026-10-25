import JuliaLean.IOBuffers.Inv

/-!
Helper lemmas for the operation specifications in `OpProofs`: wrap removal on `Int`
arithmetic, list slices, and evaluation of the model's monadic steps.
-/

namespace JuliaLean.IOBuffers

open JuliaLean

namespace OpP

/-! ## Integer values -/

theorem i64_min : IntTy.i64.min = -2 ^ 63 := by decide
theorem i64_max : IntTy.i64.max = 2 ^ 63 - 1 := by decide
theorem u64_min : IntTy.u64.min = 0 := by decide
theorem u64_max : IntTy.u64.max = 2 ^ 64 - 1 := by decide

theorem I_bounds (x : I) : -2 ^ 63 ≤ x.val ∧ x.val ≤ 2 ^ 63 - 1 := by
  have h := x.property
  have e1 := i64_min
  have e2 := i64_max
  omega

theorem U_bounds (x : U) : 0 ≤ x.val ∧ x.val ≤ 2 ^ 64 - 1 := by
  have h := x.property
  have e1 := u64_min
  have e2 := u64_max
  omega

theorem i_val {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) : (i x).val = x :=
  wrapInt_of_inRange .i64 x ⟨by have e := i64_min; omega, by have e := i64_max; omega⟩

theorem add_val {a b : I} (h1 : -2 ^ 63 ≤ a.val + b.val) (h2 : a.val + b.val ≤ 2 ^ 63 - 1) :
    (a + b).val = a.val + b.val := i_val h1 h2

theorem sub_val {a b : I} (h1 : -2 ^ 63 ≤ a.val - b.val) (h2 : a.val - b.val ≤ 2 ^ 63 - 1) :
    (a - b).val = a.val - b.val := i_val h1 h2

theorem neg_val {a : I} (h1 : -2 ^ 63 ≤ -a.val) (h2 : -a.val ≤ 2 ^ 63 - 1) :
    (-a).val = -a.val := i_val h1 h2

theorem i0 : (i 0).val = 0 := i_val (by decide) (by decide)
theorem i1 : (i 1).val = 1 := i_val (by decide) (by decide)
theorem im1 : (i (-1)).val = -1 := i_val (by decide) (by decide)

theorem add_one_val {a : I} (h : a.val ≤ 2 ^ 63 - 2) : (a + i 1).val = a.val + 1 := by
  have := I_bounds a
  rw [add_val] <;> rw [i1] <;> omega

theorem sub_one_val {a : I} (h : -2 ^ 63 + 1 ≤ a.val) : (a - i 1).val = a.val - 1 := by
  have := I_bounds a
  rw [sub_val] <;> rw [i1] <;> omega

theorem uadd_val {a b : U} (h : a.val + b.val ≤ 2 ^ 64 - 1) : (a + b).val = a.val + b.val := by
  have ha := U_bounds a
  have hb := U_bounds b
  exact wrapInt_of_inRange .u64 _ ⟨by have e := u64_min; omega, by have e := u64_max; omega⟩

theorem rem_u64_val (x : I) (h : 0 ≤ x.val) : (JInt.rem .u64 x).val = x.val := by
  have hx := I_bounds x
  exact wrapInt_of_inRange .u64 _ ⟨by have e := u64_min; omega, by have e := u64_max; omega⟩

theorem imax_val (a b : I) : (imax a b).val = max a.val b.val := by
  unfold imax; split <;> omega

theorem imin_val (a b : I) : (imin a b).val = min a.val b.val := by
  unfold imin; split <;> omega

theorem uminU_val (a b : U) : (uminU a b).val = min a.val b.val := by
  unfold uminU; split <;> omega

theorem getOffset_val (io : IOBuf) : (getOffset io).val = max 0 io.oc.val := by
  unfold getOffset; rw [imax_val, i0]

theorem getCompacted_val (io : IOBuf) (h1 : -2 ^ 62 ≤ io.oc.val) (h2 : io.oc.val ≤ 2 ^ 62) :
    (getCompacted io).val = max 0 (-io.oc.val) := by
  unfold getCompacted; rw [imax_val, i0, neg_val (by omega) (by omega)]

theorem clampToI_val (x : Int) : (clampToI x).val = max (-2 ^ 63) (min x (2 ^ 63 - 1)) := by
  unfold clampToI imaxval
  split
  · rw [i_val (by decide) (by decide)]; omega
  · split
    · rw [i_val (by decide) (by decide)]; omega
    · rw [i_val (by omega) (by omega)]; omega

theorem clampI_val (x lo hi : I) (h : lo.val ≤ hi.val) :
    (clampI x lo hi).val = max lo.val (min x.val hi.val) := by
  unfold clampI
  split
  · omega
  · split <;> omega

theorem translate_val (io : IOBuf) (n : I) :
    (translateSeekPosition io n).val = max (-2 ^ 63) (min (n.val + io.oc.val + 1) (2 ^ 63 - 1)) :=
  clampToI_val _

theorem rangeLength_val (a b : I) (h1 : -2 ^ 61 ≤ a.val) (h2 : a.val ≤ 2 ^ 62 + 1)
    (h3 : -2 ^ 61 ≤ b.val) (h4 : b.val ≤ 2 ^ 62 + 1) :
    (rangeLength a b).val = max 0 (b.val - a.val + 1) := by
  unfold rangeLength
  split
  · rw [i0]; omega
  · have hs : (b - a).val = b.val - a.val := sub_val (by omega) (by omega)
    rw [add_one_val (by rw [hs]; omega), hs]; omega

theorem toU_ok (x : Int) (h0 : 0 ≤ x) (h1 : x ≤ 2 ^ 64 - 1) :
    ∃ v : U, toU x = .ok v ∧ v.val = x := by
  have hb : IntTy.u64.min ≤ x ∧ x ≤ IntTy.u64.max := by rw [u64_min, u64_max]; exact ⟨h0, h1⟩
  refine ⟨⟨x, hb⟩, ?_, rfl⟩
  unfold toU JInt.convert
  rw [dif_pos hb]

theorem toI_ok (x : Int) (h0 : -2 ^ 63 ≤ x) (h1 : x ≤ 2 ^ 63 - 1) :
    ∃ v : I, toI x = .ok v ∧ v.val = x := by
  have hb : IntTy.i64.min ≤ x ∧ x ≤ IntTy.i64.max := by rw [i64_min, i64_max]; exact ⟨h0, h1⟩
  refine ⟨⟨x, hb⟩, ?_, rfl⟩
  unfold toI JInt.convert
  rw [dif_pos hb]

theorem ismarked_iff (io : IOBuf) : ismarked io = true ↔ 0 ≤ io.mark.val := by
  simp [ismarked]

/-! ## Facts from `Inv` -/

theorem invFacts {io : IOBuf} (h : Inv io) :
    0 ≤ io.maxsize.val ∧ (io.data.length : Int) ≤ 2 ^ 62 ∧ -2 ^ 61 ≤ io.oc.val ∧
    (getOffset io).val = max 0 io.oc.val ∧ (getOffset io).val ≤ io.size.val ∧
    io.size.val ≤ io.data.length ∧ (getOffset io).val + 1 ≤ io.ptr.val ∧
    io.ptr.val ≤ io.size.val + 1 ∧ io.size.val - (getOffset io).val ≤ io.maxsize.val ∧
    -1 ≤ io.mark.val ∧ io.mark.val ≤ 2 ^ 62 ∧ io.maxsize.val ≤ 2 ^ 63 - 1 := by
  have := h.len_le
  have := I_bounds io.maxsize
  exact ⟨h.maxsize_nonneg, by omega, h.oc_ge, getOffset_val io, h.off_le_size, h.size_le_len,
    h.ptr_ge, h.ptr_le, h.stored_le, h.mark_ge, h.mark_le, this.2⟩

theorem position_eq (io : IOBuf) (h1 : -2 ^ 63 + 1 ≤ io.ptr.val - io.oc.val)
    (h2 : io.ptr.val - io.oc.val ≤ 2 ^ 63 - 1) : (position io).val = io.ptr.val - io.oc.val - 1 := by
  have hs : (io.ptr - io.oc).val = io.ptr.val - io.oc.val := sub_val (by omega) (by omega)
  unfold position
  rw [sub_one_val (by rw [hs]; omega), hs]

theorem ba_eq (io : IOBuf) (h1 : -2 ^ 63 ≤ io.size.val - io.ptr.val)
    (h2 : io.size.val - io.ptr.val ≤ 2 ^ 63 - 2) :
    (bytesavailable io).val = io.size.val - io.ptr.val + 1 := by
  have hs : (io.size - io.ptr).val = io.size.val - io.ptr.val := sub_val (by omega) (by omega)
  unfold bytesavailable
  rw [add_one_val (by rw [hs]; omega), hs]

theorem position_val {io : IOBuf} (h : Inv io) : (position io).val = io.ptr.val - io.oc.val - 1 := by
  have f := invFacts h
  exact position_eq io (by omega) (by omega)

theorem ba_val {io : IOBuf} (h : Inv io) : (bytesavailable io).val = io.size.val - io.ptr.val + 1 := by
  have f := invFacts h
  exact ba_eq io (by omega) (by omega)

theorem filesize_val {io : IOBuf} (h : Inv io) (hs : io.seekable = true) :
    (filesize io).val = io.size.val - (getOffset io).val := by
  have f := invFacts h
  unfold filesize
  rw [if_pos hs]
  exact sub_val (by omega) (by omega)

/-! ## Lists -/

theorem slice_nil {d : List UInt8} {a b : Int} (h : b - a + 1 ≤ 0) : slice d a b = [] := by
  unfold slice
  rw [show (b - a + 1).toNat = 0 by omega]
  rfl

theorem slice_length {d : List UInt8} {a b : Int} (h1 : 1 ≤ a) (h2 : b ≤ d.length) (h3 : a ≤ b + 1) :
    ((slice d a b).length : Int) = b - a + 1 := by
  unfold slice
  rw [List.length_take, List.length_drop]
  omega

theorem take_drop_congr {d : List UInt8} {x x' y y' : Nat} (hy : y = y') (hx : y = 0 ∨ x = x') :
    (d.drop x).take y = (d.drop x').take y' := by
  subst hy
  rcases hx with h | h
  · subst h; rfl
  · rw [h]

theorem slice_drop (d : List UInt8) (a b : Int) (k : Nat) :
    (slice d a b).drop k = (d.drop ((a - 1).toNat + k)).take ((b - a + 1).toNat - k) := by
  unfold slice
  rw [List.drop_take, List.drop_drop]

theorem take_min_of_le (l : List UInt8) (a b : Nat) (h : l.length ≤ b) :
    l.take (min a b) = l.take a := by
  rw [← List.take_take, List.take_of_length_le h]

theorem drop_min_of_le (l : List UInt8) (a b : Nat) (h : l.length ≤ b) :
    l.drop (min a b) = l.drop a := by
  rcases Nat.le_total a b with h' | h'
  · rw [Nat.min_eq_left h']
  · rw [Nat.min_eq_right h', List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]

theorem getD_eq_drop_headD (l : List UInt8) (n : Nat) : l.getD n 0 = (l.drop n).headD 0 := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih => cases n <;> simp [ih]

theorem avail_length {io : IOBuf} (h : Inv io) : ((avail io).length : Int) = (bytesavailable io).val := by
  have f := invFacts h
  rw [ba_val h]
  exact slice_length (by omega) (by omega) (by omega)

theorem avail_adv {io : IOBuf} (h : Inv io) (p : I) (k : Nat) (hk : (k : Int) ≤ (bytesavailable io).val)
    (hp : p.val = io.ptr.val + k) : avail { io with ptr := p } = (avail io).drop k := by
  have f := invFacts h
  have hb := ba_val h
  show slice io.data p.val io.size.val = (slice io.data io.ptr.val io.size.val).drop k
  rw [slice_drop]
  unfold slice
  apply take_drop_congr <;> omega

theorem pending_eq {io : IOBuf} (h : Inv io) : pending io = .ok (avail io) := by
  have f := invFacts h
  unfold pending
  split
  · rw [show avail io = [] from slice_nil (by omega)]
  · rw [if_pos ⟨by omega, by omega⟩]; rfl

theorem readAt_avail {io : IOBuf} (h : Inv io) (m : Nat) (hm : (m : Int) ≤ (bytesavailable io).val) :
    readAt io.data io.ptr m = .ok ((avail io).take m) := by
  have f := invFacts h
  have hb := ba_val h
  unfold readAt
  split
  · rename_i h0; subst h0; rfl
  · rw [if_pos ⟨by omega, by omega⟩]
    unfold avail slice
    rw [List.take_take]
    congr 2
    omega

/-! ## Monadic steps -/

theorem resultOf_ok {α} {m : M α} {io s : IOBuf} {a : α} (h : m.run io = .ok a s) :
    resultOf m io = .ok a := by
  simp [resultOf, h]

theorem stateOf_ok {α} {m : M α} {io s : IOBuf} {a : α} (h : m.run io = .ok a s) :
    stateOf m io = s := by
  simp [stateOf, h]

theorem resultOf_err {α} {m : M α} {io s : IOBuf} {e : IOErr} (h : m.run io = .error e s) :
    resultOf m io = .error e := by
  simp [resultOf, h]

theorem stateOf_err {α} {m : M α} {io s : IOBuf} {e : IOErr} (h : m.run io = .error e s) :
    stateOf m io = s := by
  simp [stateOf, h]

theorem unsafeRead_run {io : IOBuf} (h : Inv io) (hr : io.readable = true) (nb : U)
    (hnb : nb.val ≤ (bytesavailable io).val) :
    ∃ p : I, p.val = io.ptr.val + nb.val ∧
      (unsafeRead nb).run io = .ok ((avail io).take nb.val.toNat) { io with ptr := p } := by
  have f := invFacts h
  have hb := ba_val h
  have hnb0 := U_bounds nb
  have hav : (JInt.rem .u64 (bytesavailable io)).val = (bytesavailable io).val :=
    rem_u64_val _ (by omega)
  have hadv : uminU (JInt.rem .u64 (bytesavailable io)) nb = nb := by
    apply Subtype.ext; rw [uminU_val]; omega
  have hread := readAt_avail h nb.val.toNat (by omega)
  have hrp := rem_u64_val io.ptr (by omega)
  have hp : (JInt.rem .u64 io.ptr + nb).val = io.ptr.val + nb.val := by
    rw [uadd_val (by rw [hrp]; omega), hrp]
  obtain ⟨p, hp1, hp2⟩ := toI_ok (JInt.rem .u64 io.ptr + nb).val (by omega) (by omega)
  refine ⟨p, by omega, ?_⟩
  have hn1 : ¬ nb.val > (JInt.rem .u64 (bytesavailable io)).val := by omega
  simp [unsafeRead, hr, hadv, hread, hp1, hn1, lift] <;> rfl

theorem run_throw {α} (e : IOErr) (s : IOBuf) : (throw e : M α).run s = .error e s := rfl

theorem ptr_add_val {io : IOBuf} (h : Inv io) (k : Nat) (hk : (k : Int) ≤ (bytesavailable io).val) :
    (io.ptr + i k).val = io.ptr.val + k := by
  have hb := ba_val h
  have hp := h.ptr_ge
  have hp2 := h.ptr_le
  have hg := getOffset_val io
  have hs := h.size_le_len
  have hl := h.len_le
  have hik : (i k).val = k := i_val (by omega) (by omega)
  have h1 : -2 ^ 63 ≤ io.ptr.val + (i k).val := by rw [hik]; omega
  have h2 : io.ptr.val + (i k).val ≤ 2 ^ 63 - 1 := by rw [hik]; omega
  rw [add_val h1 h2, hik]

theorem run_map {α β} (g : α → β) (m : M α) (s : IOBuf) :
    (g <$> m).run s = match m.run s with
      | .ok a s => .ok (g a) s
      | .error e s => .error e s := by
  show EStateM.map g m s = _
  simp only [EStateM.map, EStateM.run]
  cases m s <;> rfl

theorem position_ptr (io : IOBuf) (p : I) (h1 : -2 ^ 63 + 1 ≤ p.val - io.oc.val)
    (h2 : p.val - io.oc.val ≤ 2 ^ 63 - 1) :
    (position { io with ptr := p }).val = p.val - io.oc.val - 1 :=
  position_eq _ h1 h2

theorem getD_of_lt (l : List UInt8) (k : Nat) (h : k < l.length) : l.getD k 0 = l[k] := by
  simp [h]

theorem headD_of_take_eq {l r : List UInt8} {m : Nat} {b : UInt8} (h : l.take m = b :: r) :
    l.headD 0 = b := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    cases m with
    | zero => simp at h
    | succ m => simp at h; simp [h.1]

theorem findOrLen_le (a : List UInt8) (d : UInt8) : findOrLen a d ≤ a.length := by
  unfold findOrLen
  cases hk : a.idxOf? d with
  | none => exact Nat.le_refl _
  | some k =>
    obtain ⟨hlt, -⟩ := List.idxOf?_eq_some_iff.mp hk
    exact hlt

theorem drop_findOrLen (a : List UInt8) (d : UInt8) : a.drop (findOrLen a d) = afterSpec a d := by
  unfold findOrLen afterSpec
  cases a.idxOf? d with
  | none => exact List.drop_length
  | some k => rfl

theorem last_not_mem {a : List UInt8} {d : UInt8} (hn : d ∉ a) :
    ¬ (a.length > 0 ∧ a.getD (a.length - 1) 0 = d) := by
  rintro ⟨hpos, hg⟩
  apply hn
  rw [← hg, getD_of_lt a _ (by omega)]
  exact List.getElem_mem _

theorem readuntil_take (a : List UInt8) (d : UInt8) (keep : Bool) :
    a.take (if !keep ∧ findOrLen a d > 0 ∧ a.getD (findOrLen a d - 1) 0 = d
      then findOrLen a d - 1 else findOrLen a d) = untilSpec a d keep := by
  unfold findOrLen untilSpec
  cases hk : a.idxOf? d with
  | none =>
    have hc := last_not_mem (List.idxOf?_eq_none_iff.mp hk)
    dsimp only
    split
    · rename_i hh; exact absurd ⟨hh.2.1, hh.2.2⟩ hc
    · exact List.take_length
  | some k =>
    obtain ⟨hlt, hak, -⟩ := List.idxOf?_eq_some_iff.mp hk
    have hg : a.getD k 0 = d := by rw [getD_of_lt a k hlt]; exact hak
    cases keep <;> simp [hg, hlt, hak]

theorem readline_take (a : List UInt8) (keep : Bool) :
    a.take (if !keep ∧ findOrLen a 0x0a > 0 ∧ a.getD (findOrLen a 0x0a - 1) 0 = 0x0a then
        if findOrLen a 0x0a - 1 > 0 ∧ a.getD (findOrLen a 0x0a - 2) 0 = 0x0d
        then findOrLen a 0x0a - 2 else findOrLen a 0x0a - 1
      else findOrLen a 0x0a) = lineSpec a keep := by
  unfold findOrLen lineSpec
  cases hk : a.idxOf? 0x0a with
  | none =>
    have hc := last_not_mem (List.idxOf?_eq_none_iff.mp hk)
    dsimp only
    split
    · rename_i hh; exact absurd ⟨hh.2.1, hh.2.2⟩ hc
    · exact List.take_length
  | some k =>
    obtain ⟨hlt, hak, -⟩ := List.idxOf?_eq_some_iff.mp hk
    have hg : a.getD k 0 = 0x0a := by rw [getD_of_lt a k hlt]; exact hak
    dsimp only
    have e1 : k + 1 - 1 = k := by omega
    have e2 : k + 1 - 2 = k - 1 := by omega
    rw [e1, e2]
    cases keep
    · have hcond : ((!false) = true ∧ k + 1 > 0 ∧ a.getD k 0 = 0x0a) := ⟨rfl, by omega, hg⟩
      rw [if_pos hcond]
      show _ = if 0 < k ∧ a.getD (k - 1) 0 = 0x0d then a.take (k - 1) else a.take k
      by_cases hc : 0 < k ∧ a.getD (k - 1) 0 = 0x0d
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
    · have hcond : ¬ ((!true) = true ∧ k + 1 > 0 ∧ a.getD k 0 = 0x0a) :=
        fun hh => absurd hh.1 (by decide)
      rw [if_neg hcond]
      rfl

end OpP

end JuliaLean.IOBuffers
