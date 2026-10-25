import JuliaLean.IOBuffers.Inv

/-!
Proof infrastructure for `reachable_inv`: the predicate `Spec` describing the outcome of an
`M` computation, value lemmas for the wrapping `Int` arithmetic, success lemmas for the
memory primitives, and the strengthened invariant `SInv`.
-/

namespace JuliaLean.IOBuffers.InvP

open JuliaLean JuliaLean.IOBuffers

/-! ## Outcomes of `M` computations -/

/-- `m` started in `s` returns `a` in a state satisfying `Q a`, or throws `e` in a state
satisfying `E e`. -/
def Spec {α} (m : M α) (s : IOBuf) (Q : α → IOBuf → Prop) (E : IOErr → IOBuf → Prop) : Prop :=
  match m s with
  | .ok a s' => Q a s'
  | .error e s' => E e s'

theorem spec_bind {α β} {x : M α} {f : α → M β} {s Q E} :
    Spec (x >>= f) s Q E ↔ Spec x s (fun a s' => Spec (f a) s' Q E) E := by
  simp only [Spec, bind, EStateM.bind]
  cases x s <;> rfl

theorem spec_pure {α} {a : α} {s Q E} : Spec (pure a : M α) s Q E ↔ Q a s := Iff.rfl
theorem spec_get {s Q E} : Spec (get : M IOBuf) s Q E ↔ Q s s := Iff.rfl
theorem spec_set {s s' Q E} : Spec (set s' : M PUnit) s Q E ↔ Q ⟨⟩ s' := Iff.rfl
theorem spec_modify {f s Q E} : Spec (modify f : M PUnit) s Q E ↔ Q ⟨⟩ (f s) := Iff.rfl
theorem spec_throw {α} {e s Q E} : Spec (throw e : M α) s Q E ↔ E e s := Iff.rfl
theorem spec_ite {α} {c : Prop} [Decidable c] {a b : M α} {s Q E} :
    Spec (if c then a else b) s Q E ↔ (if c then Spec a s Q E else Spec b s Q E) := by
  split <;> rfl
theorem spec_lift_ok {α} {a : α} {s Q E} : Spec (lift (.ok a)) s Q E ↔ Q a s := Iff.rfl
theorem spec_lift_error {α} {e s Q E} : Spec (lift (.error e : Except IOErr α)) s Q E ↔ E e s :=
  Iff.rfl

theorem spec_discard {α} {m : M α} {s Q E} :
    Spec (discard m) s Q E ↔ Spec m s (fun _ => Q ()) E := by
  unfold Spec
  rw [show discard m s = EStateM.map (fun _ => ()) m s from rfl]
  unfold EStateM.map
  cases m s <;> rfl

theorem spec_tryCatch {α} {x : M α} {h : IOErr → M α} {s Q E} :
    Spec (tryCatch x h) s Q E ↔ Spec x s Q (fun e s' => Spec (h e) s' Q E) := by
  unfold Spec
  rw [show (tryCatch x h) s = EStateM.tryCatch x h s from rfl]
  unfold EStateM.tryCatch
  cases x s <;> rfl

theorem Spec.mono {α} {m : M α} {s : IOBuf} {Q Q' : α → IOBuf → Prop} {E E' : IOErr → IOBuf → Prop}
    (h : Spec m s Q E) (hq : ∀ a s', Q a s' → Q' a s') (he : ∀ e s', E e s' → E' e s') :
    Spec m s Q' E' := by
  unfold Spec at *
  revert h
  cases m s with
  | ok a s' => exact hq a s'
  | error e s' => exact he e s'

theorem spec_lift_of {α} {x : Except IOErr α} {s Q E} (hok : ∀ a, x = .ok a → Q a s)
    (herr : ∀ e, x = .error e → E e s) : Spec (lift x) s Q E := by
  cases x with
  | ok a => exact hok a rfl
  | error e => exact herr e rfl

/-! ## Values of the wrapping arithmetic -/

theorem I.bounds (a : I) : -2 ^ 63 ≤ a.val ∧ a.val ≤ 2 ^ 63 - 1 := by
  have := a.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ↓reduceIte] at this
  omega

theorem U.bounds (a : U) : 0 ≤ a.val ∧ a.val ≤ 2 ^ 64 - 1 := by
  have := a.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Bool.false_eq_true,
    ↓reduceIte] at this
  omega

theorem w64 {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) : wrapInt .i64 x = x :=
  wrapInt_of_inRange .i64 x ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits] <;> omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits] <;> omega⟩

theorem wu64 {x : Int} (h1 : 0 ≤ x) (h2 : x ≤ 2 ^ 64 - 1) : wrapInt .u64 x = x :=
  wrapInt_of_inRange .u64 x ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits] <;> omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits] <;> omega⟩

theorem v_add {t} (a b : JInt t) : (a + b).val = wrapInt t (a.val + b.val) := rfl
theorem v_sub {t} (a b : JInt t) : (a - b).val = wrapInt t (a.val - b.val) := rfl
theorem v_neg {t} (a : JInt t) : (-a).val = wrapInt t (-a.val) := rfl
theorem v_mul {t} (a b : JInt t) : (a * b).val = wrapInt t (a.val * b.val) := rfl
theorem v_i (x : Int) : (i x).val = wrapInt .i64 x := rfl
theorem v_u (x : Int) : (u x).val = wrapInt .u64 x := rfl
theorem v_rem {t t'} (a : JInt t) : (JInt.rem t' a).val = wrapInt t' a.val := rfl
theorem v_imin (a b : I) : (imin a b).val = min a.val b.val := by
  unfold imin; split <;> omega
theorem v_imax (a b : I) : (imax a b).val = max a.val b.val := by
  unfold imax; split <;> omega
theorem v_uminU (a b : U) : (uminU a b).val = min a.val b.val := by
  unfold uminU; split <;> omega
theorem v_imaxval : imaxval.val = 2 ^ 63 - 1 := by
  unfold imaxval; simp (disch := omega) only [v_i, w64]
theorem v_clampI (x lo hi : I) (h : lo.val ≤ hi.val) :
    (clampI x lo hi).val = max lo.val (min x.val hi.val) := by
  unfold clampI
  split
  · omega
  · split <;> omega
theorem v_clampToI (x : Int) : (clampToI x).val = max (-2 ^ 63) (min x (2 ^ 63 - 1)) := by
  unfold clampToI
  split
  · rw [v_imaxval]; omega
  · split <;> simp (disch := omega) only [v_i, w64] <;> omega
theorem v_off (s : IOBuf) : (getOffset s).val = max 0 s.oc.val := by
  unfold getOffset; simp (disch := omega) only [v_imax, v_i, w64]
theorem v_comp (s : IOBuf) : (getCompacted s).val = max 0 (wrapInt .i64 (-s.oc.val)) := by
  unfold getCompacted; simp (disch := omega) only [v_imax, v_i, v_neg, w64]
theorem v_pos (s : IOBuf) :
    (position s).val = wrapInt .i64 (wrapInt .i64 (s.ptr.val - s.oc.val) - 1) := by
  unfold position; simp (disch := omega) only [v_sub, v_i, w64]
theorem v_ba (s : IOBuf) :
    (bytesavailable s).val = wrapInt .i64 (wrapInt .i64 (s.size.val - s.ptr.val) + 1) := by
  unfold bytesavailable; simp (disch := omega) only [v_add, v_sub, v_i, w64]
theorem v_tsp (s : IOBuf) (n : I) :
    (translateSeekPosition s n).val = max (-2 ^ 63) (min (n.val + s.oc.val + 1) (2 ^ 63 - 1)) := by
  unfold translateSeekPosition; rw [v_clampToI]
theorem v_rangeLength (a b : I) (h1 : a.val ≤ b.val + 1) (h2 : 1 ≤ a.val) :
    (rangeLength a b).val = b.val - a.val + 1 := by
  have := I.bounds a; have := I.bounds b
  unfold rangeLength
  split
  · simp (disch := omega) only [v_i, w64]; omega
  · simp (disch := omega) only [v_add, v_sub, v_i, w64]

/-- Clean up `Bool` conditions and `if`s on literals. -/
macro "bsimp" : tactic => `(tactic| simp only [Bool.false_eq_true, Bool.true_eq_false,
  Bool.not_true, Bool.not_false, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or,
  Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, eq_self_iff_true, true_implies,
  false_implies, and_true, true_and, ↓reduceIte])

/-- Rewrite `.val` of wrapping arithmetic to exact `Int` arithmetic, discharging the range
conditions with `omega`. -/
syntax "vsimp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| vsimp $[$loc]?) =>
    `(tactic| simp (disch := omega) only [JuliaLean.IOBuffers.InvP.v_add,
      JuliaLean.IOBuffers.InvP.v_sub, JuliaLean.IOBuffers.InvP.v_neg,
      JuliaLean.IOBuffers.InvP.v_mul, JuliaLean.IOBuffers.InvP.v_i,
      JuliaLean.IOBuffers.InvP.v_u, JuliaLean.IOBuffers.InvP.v_rem,
      JuliaLean.IOBuffers.InvP.v_imin, JuliaLean.IOBuffers.InvP.v_imax,
      JuliaLean.IOBuffers.InvP.v_uminU, JuliaLean.IOBuffers.InvP.v_imaxval,
      JuliaLean.IOBuffers.InvP.v_clampToI, JuliaLean.IOBuffers.InvP.v_off,
      JuliaLean.IOBuffers.InvP.v_comp, JuliaLean.IOBuffers.InvP.v_pos,
      JuliaLean.IOBuffers.InvP.v_ba, JuliaLean.IOBuffers.InvP.v_tsp,
      JuliaLean.IOBuffers.InvP.v_rangeLength, JuliaLean.IOBuffers.InvP.w64,
      JuliaLean.IOBuffers.InvP.wu64, List.length_replicate, List.length_take,
      Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, eq_self_iff_true,
      true_implies, false_implies, and_true, true_and, ↓reduceIte] $[$loc]?)

/-- `vsimp`, then `omega`. -/
macro "vo" : tactic => `(tactic| ((try vsimp) <;> omega))

/-! ## Memory primitives -/

theorem slice_length (d : List UInt8) (a b : Int) (h1 : 1 ≤ a) (h2 : a ≤ b + 1)
    (h3 : b ≤ d.length) : (slice d a b).length = (b - a + 1).toNat := by
  unfold slice
  simp only [List.length_take, List.length_drop]
  omega

theorem spec_copyto {dest src : List UInt8} {doffs soffs n : I} {s : IOBuf}
    {Q : List UInt8 → IOBuf → Prop} {E : IOErr → IOBuf → Prop} (h0 : 0 ≤ n.val)
    (h1 : 1 ≤ doffs.val) (h2 : doffs.val + n.val - 1 ≤ dest.length)
    (h3 : 1 ≤ soffs.val) (h4 : soffs.val + n.val - 1 ≤ src.length)
    (hq : ∀ r : List UInt8, r.length = dest.length → Q r s) :
    Spec (lift (copyto dest doffs src soffs n)) s Q E := by
  unfold copyto
  by_cases hn : n.val = 0
  · rw [if_pos hn]; exact spec_lift_ok.mpr (hq _ rfl)
  · rw [if_neg hn, if_neg (show ¬ n.val < 0 by omega), if_pos (And.intro h1 (And.intro h2
      (And.intro h3 h4)))]
    refine spec_lift_ok.mpr (hq _ ?_)
    have := slice_length src soffs.val (soffs.val + n.val - 1) h3 (by omega) h4
    simp only [List.length_append, List.length_take, List.length_drop]
    omega

theorem spec_writeAt {m : Bool} {d : List UInt8} {k : I} {bs : List UInt8} {s : IOBuf}
    {Q : List UInt8 → IOBuf → Prop} {E : IOErr → IOBuf → Prop}
    (h1 : 1 ≤ k.val) (h2 : k.val + bs.length - 1 ≤ d.length)
    (hq : ∀ r : List UInt8, r.length = d.length → Q r s) :
    Spec (lift (writeAt m d k bs)) s Q E := by
  unfold writeAt
  by_cases hb : bs.length = 0
  · rw [if_pos hb]; exact spec_lift_ok.mpr (hq _ rfl)
  · rw [if_neg hb, if_pos (And.intro h1 h2)]
    refine spec_lift_ok.mpr (hq _ ?_)
    simp only [List.length_append, List.length_take, List.length_drop]
    omega

theorem spec_readAt {d : List UInt8} {k : I} {n : Nat} {s : IOBuf}
    {Q : List UInt8 → IOBuf → Prop} {E : IOErr → IOBuf → Prop}
    (h : n = 0 ∨ (1 ≤ k.val ∧ k.val + n - 1 ≤ d.length)) (hq : ∀ r, Q r s) :
    Spec (lift (readAt d k n)) s Q E := by
  unfold readAt
  by_cases hn : n = 0
  · rw [if_pos hn]; exact spec_lift_ok.mpr (hq _)
  · rw [if_neg hn, if_pos (h.resolve_left hn)]; exact spec_lift_ok.mpr (hq _)

theorem spec_fillZero {d : List UInt8} {a b : I} {s : IOBuf}
    {Q : List UInt8 → IOBuf → Prop} {E : IOErr → IOBuf → Prop}
    (h1 : 1 ≤ a.val) (h2 : b.val ≤ d.length)
    (hq : ∀ r : List UInt8, r.length = d.length → Q r s) :
    Spec (lift (fillZero d a b)) s Q E := by
  unfold fillZero
  by_cases hb : b.val < a.val
  · rw [if_pos hb]; exact spec_lift_ok.mpr (hq _ rfl)
  · rw [if_neg hb, if_pos (And.intro h1 h2)]
    refine spec_lift_ok.mpr (hq _ ?_)
    simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate]
    omega

theorem spec_setChecked {d : List UInt8} {k : I} {b : UInt8} {s : IOBuf}
    {Q : List UInt8 → IOBuf → Prop} {E : IOErr → IOBuf → Prop}
    (hq : ∀ r : List UInt8, r.length = d.length → 1 ≤ k.val → k.val ≤ d.length → Q r s)
    (he : E (.jl .boundsError) s) :
    Spec (lift (setChecked d k b)) s Q E := by
  unfold setChecked
  split
  · next hk => exact spec_lift_ok.mpr (hq _ List.length_set hk.1 hk.2)
  · exact spec_lift_error.mpr he

theorem spec_toI {x : Int} {s : IOBuf} {Q : I → IOBuf → Prop} {E : IOErr → IOBuf → Prop}
    (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) (hq : ∀ v : I, v.val = x → Q v s) :
    Spec (lift (toI x)) s Q E := by
  unfold toI JInt.convert
  have hc : IntTy.min .i64 ≤ x ∧ x ≤ IntTy.max .i64 := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ↓reduceIte]; omega
  rw [dif_pos hc]
  exact spec_lift_ok.mpr (hq _ rfl)

theorem spec_toU {x : Int} {s : IOBuf} {Q : U → IOBuf → Prop} {E : IOErr → IOBuf → Prop}
    (h1 : 0 ≤ x) (h2 : x ≤ 2 ^ 64 - 1) (hq : ∀ v : U, v.val = x → Q v s) :
    Spec (lift (toU x)) s Q E := by
  unfold toU JInt.convert
  have hc : IntTy.min .u64 ≤ x ∧ x ≤ IntTy.max .u64 := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Bool.false_eq_true,
      ↓reduceIte]; omega
  rw [dif_pos hc]
  exact spec_lift_ok.mpr (hq _ rfl)

theorem spec_stringMemory {n : I} {s : IOBuf} {Q : List UInt8 → IOBuf → Prop}
    {E : IOErr → IOBuf → Prop} (h : 0 ≤ n.val) (hq : Q (List.replicate n.val.toNat 0) s) :
    Spec (lift (stringMemory n)) s Q E := by
  unfold stringMemory
  rw [if_neg (show ¬ n.val < 0 by omega)]
  exact spec_lift_ok.mpr hq

theorem spec_similarData {n : I} {s s0 : IOBuf} {Q : List UInt8 → IOBuf → Prop}
    {E : IOErr → IOBuf → Prop} (h : 0 ≤ n.val) (hq : s0.isMem = true → Q (List.replicate n.val.toNat 0) s)
    (he : s0.isMem = false → E (.jl (.methodError "convert")) s) :
    Spec (lift (similarData s0 n)) s Q E := by
  unfold similarData
  cases hm : s0.isMem
  · rw [if_neg Bool.false_ne_true]; exact spec_lift_error.mpr (he hm)
  · rw [if_pos (rfl : true = true)]; exact spec_stringMemory h (hq hm)

/-- An exception that is not an unchecked access. -/
abbrev NotOOB (e : IOErr) : Prop := e ≠ .outOfBounds

theorem noob_jl (e : JlError) : NotOOB (.jl e) := nofun

theorem noob_copyto {dest src : List UInt8} {doffs soffs n : I} {e : IOErr}
    (h : copyto dest doffs src soffs n = .error e) : NotOOB e := by
  unfold copyto at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_stringMemory {n : I} {e : IOErr} (h : stringMemory n = .error e) : NotOOB e := by
  unfold stringMemory at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_similarData {s : IOBuf} {n : I} {e : IOErr} (h : similarData s n = .error e) :
    NotOOB e := by
  unfold similarData stringMemory at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_toU {x : Int} {e : IOErr} (h : toU x = .error e) : NotOOB e := by
  unfold toU at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_toI {x : Int} {e : IOErr} (h : toI x = .error e) : NotOOB e := by
  unfold toI at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_wrapBytes {d : List UInt8} {k n : I} {e : IOErr} (h : wrapBytes d k n = .error e) :
    NotOOB e := by
  unfold wrapBytes at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_fillZero {d : List UInt8} {a b : I} {e : IOErr} (h : fillZero d a b = .error e) :
    NotOOB e := by
  unfold fillZero at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_getChecked {d : List UInt8} {k : I} {e : IOErr} (h : getChecked d k = .error e) :
    NotOOB e := by
  unfold getChecked at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_setChecked {d : List UInt8} {k : I} {b : UInt8} {e : IOErr}
    (h : setChecked d k b = .error e) : NotOOB e := by
  unfold setChecked at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_getUsedSpan {s : IOBuf} {e : IOErr} (h : getUsedSpan s = .error e) : NotOOB e := by
  unfold getUsedSpan at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

theorem noob_pending {s : IOBuf} {e : IOErr} (h : pending s = .error e) : NotOOB e := by
  unfold pending at h
  repeat' split at h
  all_goals (cases h <;> exact nofun)

/-! ## The strengthened invariant -/

/-- `Inv` in terms of raw field values, with the budget `K` bounding `size` plus the number of
compacted bytes. -/
structure SInv (s : IOBuf) (K : Int) : Prop where
  ms : 0 ≤ s.maxsize.val
  len : (s.data.length : Int) ≤ 2 ^ 62
  seek : s.seekable = true → 0 ≤ s.oc.val
  offsz : max 0 s.oc.val ≤ s.size.val
  szlen : s.size.val ≤ s.data.length
  ptrl : max 0 s.oc.val + 1 ≤ s.ptr.val
  ptru : s.ptr.val ≤ s.size.val + 1
  stored : s.size.val - max 0 s.oc.val ≤ s.maxsize.val
  mkl : -1 ≤ s.mark.val
  mku : s.mark.val ≤ 2 ^ 62
  pipe : s.seekable = false → 0 ≤ s.mark.val →
    s.mark.val ≤ s.ptr.val - s.oc.val - 1 ∧ max 0 s.oc.val ≤ s.mark.val + s.oc.val
  re : s.reinit = true → s.ptr.val = 1 ∧ s.size.val = 0 ∧ s.oc.val = 0
  phi : s.size.val + max 0 (-s.oc.val) ≤ K

/-- Errors that are not unchecked accesses, in a state satisfying `SInv _ K`. -/
abbrev Err (K : Int) : IOErr → IOBuf → Prop := fun e s => NotOOB e ∧ SInv s K

theorem SInv.msu {s : IOBuf} {K : Int} (_h : SInv s K) : s.maxsize.val ≤ 2 ^ 63 - 1 :=
  (I.bounds _).2

/-- Put the unconditional fields of `SInv` into the context. -/
macro "facts " h:term : tactic => `(tactic| (
  have := ($h).ms; have := ($h).len; have := ($h).offsz; have := ($h).szlen;
  have := ($h).ptrl; have := ($h).ptru; have := ($h).stored; have := ($h).mkl;
  have := ($h).mku; have := ($h).phi; have := ($h).msu))

theorem SInv.mono {s : IOBuf} {K K' : Int} (h : SInv s K) (hk : K ≤ K') : SInv s K' :=
  { h with phi := Int.le_trans h.phi hk }

theorem Err.mono {K K' : Int} (hk : K ≤ K') : ∀ e s, Err K e s → Err K' e s :=
  fun _ _ h => ⟨h.1, h.2.mono hk⟩

theorem SInv.toInv {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61) : Inv s := by
  facts h
  have hpos : (position s).val = s.ptr.val - s.oc.val - 1 := by vsimp
  have h1 : (getOffset s).val ≤ s.size.val := by rw [v_off]; exact h.offsz
  have h2 : (getOffset s).val + 1 ≤ s.ptr.val := by rw [v_off]; exact h.ptrl
  have h3 : s.size.val - (getOffset s).val ≤ s.maxsize.val := by rw [v_off]; exact h.stored
  have h4 : s.seekable = false → 0 ≤ s.mark.val →
      s.mark.val ≤ (position s).val ∧ (getOffset s).val ≤ s.mark.val + s.oc.val := by
    intro hs hm; rw [hpos, v_off]; exact h.pipe hs hm
  exact ⟨h.ms, (by omega), (by omega), h.seek, h1, h.szlen, h2, h.ptru, h3, h.mkl, h.mku, h4,
    h.re⟩

theorem consistent_of_inv {io : IOBuf} (h : Inv io) : Consistent io := by
  have h2 := h.len_le; have h3 := h.oc_ge; have h5 := h.off_le_size
  have h6 := h.size_le_len; have h7 := h.ptr_ge; have h8 := h.ptr_le; have h9 := h.stored_le
  rw [v_off] at h5 h7 h9
  have hba : (bytesavailable io).val = io.size.val - io.ptr.val + 1 := by vsimp
  have hpo : (position io).val = io.ptr.val - io.oc.val - 1 := by vsimp
  have hav : (avail io).length = (io.size.val - io.ptr.val + 1).toNat :=
    slice_length _ _ _ (by omega) (by omega) (by omega)
  refine ⟨by omega, ?_, by omega, fun hs => ?_, by omega, ?_⟩
  · unfold eof
    simp only [decide_eq_true_eq]
    vsimp
    omega
  · have := h.oc_seekable hs
    unfold filesize
    rw [if_pos hs]
    vsimp
    omega
  · vsimp
    omega

/-! ## Proving `SInv` of a new state -/

/-- `SInv` of a state whose `SInv` fields agree with those of the state of `h`. -/
macro "sinv_same " h:term : tactic => `(tactic| exact ⟨($h).1, ($h).2, ($h).3, ($h).4,
  ($h).5, ($h).6, ($h).7, ($h).8, ($h).9, ($h).10, ($h).11, ($h).12, ($h).13⟩)

open Lean in
/-- Prove `SInv` of an explicit state field by field with `vsimp` and `omega`, using the
invariant `h` of the state it was computed from. -/
macro "sinv_close " h:term : tactic => do
  let hs := mkIdent (Name.mkSimple "hs"); let hm := mkIdent (Name.mkSimple "hm")
  let hr := mkIdent (Name.mkSimple "hr")
  `(tactic| (
    facts $h
    refine ⟨?_, ?_, fun $hs => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun $hs $hm => ?_, fun $hr => ?_,
      ?_⟩
    all_goals first
      | ((try vsimp) <;> omega)
      | (have := ($h).seek $hs; (try vsimp) <;> omega)
      | (have := ($h).pipe $hs $hm; (try vsimp at $hm:ident ⊢) <;> omega)
      | (have := ($h).re $hr; (try vsimp) <;> omega)
      | (simp only [Bool.false_eq_true, Bool.true_eq_false] at $hs:ident; done)
      | (simp only [Bool.false_eq_true, Bool.true_eq_false] at $hr:ident; done)
      | (simp only [*, Bool.false_eq_true, Bool.true_eq_false] at $hs:ident; done)
      | (simp only [*, Bool.false_eq_true, Bool.true_eq_false] at $hr:ident; done)
      | ((try vsimp at $hm:ident ⊢) <;> omega)))

open Lean in
/-- `sinv_close` for a state not derived from another one. -/
macro "sinv_auto" : tactic => do
  let hs := mkIdent (Name.mkSimple "hs"); let hm := mkIdent (Name.mkSimple "hm")
  let hr := mkIdent (Name.mkSimple "hr")
  `(tactic| (
    refine ⟨?_, ?_, fun $hs => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun $hs $hm => ?_, fun $hr => ?_,
      ?_⟩
    all_goals first
      | ((try vsimp) <;> omega)
      | (simp only [Bool.false_eq_true, Bool.true_eq_false] at $hs:ident; done)
      | (simp only [Bool.false_eq_true, Bool.true_eq_false] at $hr:ident; done)
      | ((try vsimp at $hm:ident ⊢) <;> omega)))

theorem sinv_ptr {s : IOBuf} {K : Int} (h : SInv s K) (p : I) (h1 : max 0 s.oc.val + 1 ≤ p.val)
    (h2 : p.val ≤ s.size.val + 1)
    (h3 : s.seekable = false → 0 ≤ s.mark.val → s.mark.val ≤ p.val - s.oc.val - 1) :
    SInv { s with ptr := p } K :=
  { ms := h.ms, len := h.len, seek := h.seek, offsz := h.offsz, szlen := h.szlen, ptrl := h1,
    ptru := h2, stored := h.stored, mkl := h.mkl, mku := h.mku,
    pipe := fun hs hm => ⟨h3 hs hm, (h.pipe hs hm).2⟩,
    re := fun hr => by
      have := h.re hr
      show p.val = 1 ∧ s.size.val = 0 ∧ s.oc.val = 0
      omega,
    phi := h.phi }

/-- Moving the read pointer forward within the buffer keeps `SInv`. -/
theorem sinv_ptr_fwd {s : IOBuf} {K : Int} (h : SInv s K) (p : I) (h1 : s.ptr.val ≤ p.val)
    (h2 : p.val ≤ s.size.val + 1) : SInv { s with ptr := p } K :=
  sinv_ptr h p (by have := h.ptrl; omega) h2
    (fun hs hm => by have := h.pipe hs hm; omega)

theorem sinv_mark {s : IOBuf} {K : Int} (h : SInv s K) (m : I) (h1 : -1 ≤ m.val)
    (h2 : m.val ≤ 2 ^ 62)
    (h3 : s.seekable = false → 0 ≤ m.val →
      m.val ≤ s.ptr.val - s.oc.val - 1 ∧ max 0 s.oc.val ≤ m.val + s.oc.val) :
    SInv { s with mark := m } K :=
  { ms := h.ms, len := h.len, seek := h.seek, offsz := h.offsz, szlen := h.szlen,
    ptrl := h.ptrl, ptru := h.ptru, stored := h.stored, mkl := h1, mku := h2, pipe := h3,
    re := h.re, phi := h.phi }

end JuliaLean.IOBuffers.InvP
