import JuliaLean.FloatFuncs.Props
import JuliaLean.MathFuncs.ProofsBits

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs.ProofsBits

namespace ProofNext

local notation "signMask" => (2^63 : Nat)
local notation "infMag" => (0x7ff0000000000000 : Nat)
local notation "wordSize" => (2^64 : Nat)

def u (n : Nat) : JInt .u64 := JInt.wrap .u64 (Int.ofNat n)
def un (x : JInt .u64) : Nat := x.val.toNat

def model (x : F64) (dneg : Bool) (da : Nat) : F64 := Id.run do
  if F64.isnan x then return x
  let mut fneg := F64.signbit x
  let mut fu := u (F64.toBits (F64.abs x))
  let fumax := u infMag
  if da > wordSize - 1 then
    fneg := dneg
    fu := fumax
  else
    let du := u da
    if fneg != dneg then
      if du.val > fu.val then
        fu := if (du - fu).val < fumax.val then du - fu else fumax
        fneg := !fneg
      else
        fu := fu - du
    else
      if (fumax - fu).val < du.val then fu := fumax else fu := fu + du
  return F64.ofBits (un fu + if fneg then signMask else 0)

theorem next_model (x : F64) (n : Int) :
    F64.nextfloat x n = model x (decide (n < 0)) n.natAbs := by rfl

theorem prev_model (x : F64) (n : Int) :
    F64.prevfloat x n = model x (decide (n > 0)) n.natAbs := by rfl

theorem u_val (n : Nat) (h : n < wordSize) : (u n).val = (n : Int) := by
  change wrapInt .u64 (n : Int) = (n : Int)
  apply wrapInt_of_inRange
  change (0 : Int) ≤ (n : Int) ∧ (n : Int) ≤ 2^64 - 1
  omega

theorem un_u (n : Nat) (h : n < wordSize) : un (u n) = n := by
  exact wrapU n h

theorem u_sub {a b : Nat} (ha : a < wordSize) (hb : b < wordSize) (hab : b ≤ a) :
    u a - u b = u (a - b) := by
  apply Subtype.ext
  change wrapInt .u64 ((u a).val - (u b).val) = (u (a - b)).val
  rw [u_val a ha, u_val b hb, ← Int.natCast_sub hab]
  rfl

theorem u_add {a b : Nat} (ha : a < wordSize) (hb : b < wordSize) :
    u a + u b = u (a + b) := by
  apply Subtype.ext
  change wrapInt .u64 ((u a).val + (u b).val) = (u (a + b)).val
  rw [u_val a ha, u_val b hb, ← Int.natCast_add]
  rfl

def encode (s : Bool) (m : Nat) : F64 :=
  F64.ofBits (m + if s then signMask else 0)

def walk (s d : Bool) (m n : Nat) : F64 :=
  if s != d then
    if n > m then encode (!s) (min (n - m) infMag)
    else encode s (m - n)
  else encode s (min (m + n) infMag)

def spec (x : F64) (d : Bool) (n : Nat) : F64 :=
  if F64.isnan x then x
  else walk (F64.signbit x) d (F64.toBits x % signMask) n

theorem not_nan_mag {x : F64} (h : F64.isnan x = false) :
    F64.toBits x % signMask ≤ infMag := by
  have hx := tb_lt x
  have hn := isnan_f x |>.mp h
  omega

theorem tb_encode (s : Bool) {m : Nat} (hm : m < signMask) :
    F64.toBits (encode s m) = m + if s then signMask else 0 := by
  unfold encode
  rw [tb_ofBits]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem mag_encode (s : Bool) {m : Nat} (hm : m < signMask) :
    F64.toBits (encode s m) % signMask = m := by
  rw [tb_encode s hm]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem sign_encode (s : Bool) {m : Nat} (hm : m < signMask) :
    F64.signbit (encode s m) = s := by
  unfold F64.signbit
  rw [tb_encode s hm]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> simp <;> omega

theorem not_nan_encode (s : Bool) {m : Nat} (hm : m ≤ infMag) :
    F64.isnan (encode s m) = false := by
  rw [isnan_f, tb_encode s (by omega)]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem encode_input (x : F64) :
    encode (F64.signbit x) (F64.toBits x % signMask) = x := by
  apply f64_ext
  rw [tb_encode _ (Nat.mod_lt _ (by decide))]
  have hx := tb_lt x
  by_cases hs : F64.toBits x ≥ signMask
  · have hsign : F64.signbit x = true := (signbit_iff x).mpr hs
    simp only [hsign, ↓reduceIte]
    omega
  · have hsign : F64.signbit x = false := (signbit_f x).mpr (by omega)
    simp only [hsign, Bool.false_eq_true, ↓reduceIte]
    omega

theorem walk_large (s d : Bool) {m n : Nat} (hm : m ≤ infMag)
    (hn : wordSize ≤ n) : walk s d m n = encode d infMag := by
  have hmn : m < n := by omega
  have hleft : infMag ≤ n - m := by omega
  have hright : infMag ≤ m + n := by omega
  cases s <;> cases d <;>
    simp [walk, hmn, Nat.min_eq_right hleft, Nat.min_eq_right hright]

theorem model_spec (x : F64) (d : Bool) (n : Nat) : model x d n = spec x d n := by
  by_cases hx : F64.isnan x = true
  · simp [model, spec, hx]
  have hx' : F64.isnan x = false := Bool.eq_false_iff.mpr hx
  let m := F64.toBits x % signMask
  have habs : F64.toBits (F64.abs x) = m := tb_abs x
  have hm : m ≤ infMag := not_nan_mag hx'
  have hmw : m < wordSize := by omega
  have hiw : infMag < wordSize := by decide
  simp only [spec, hx', Bool.false_eq_true, ↓reduceIte]
  change model x d n = walk (F64.signbit x) d m n
  by_cases hlarge : n > wordSize - 1
  · rw [walk_large _ _ hm (by omega)]
    simp [model, hx', hlarge, un_u _ hiw, encode]
  have hnw : n < wordSize := by omega
  by_cases hdir : (F64.signbit x != d) = true
  · by_cases hcross : m < n
    · have hdu : (u n).val > (u m).val := by rw [u_val n hnw, u_val m hmw]; omega
      have hsub := u_sub hnw hmw (Nat.le_of_lt hcross)
      have hdiffw : n - m < wordSize := by omega
      by_cases hsat : n - m < infMag
      · have hc : (u (n - m)).val < (u infMag).val := by
          rw [u_val _ hdiffw, u_val _ hiw]
          omega
        simp [model, hx', hlarge, habs, hdir, hdu, hsub, hc,
          un_u _ hdiffw, walk, hcross, Nat.min_eq_left (Nat.le_of_lt hsat), encode]
      · have hc : ¬ (u (n - m)).val < (u infMag).val := by
          rw [u_val _ hdiffw, u_val _ hiw]
          omega
        simp [model, hx', hlarge, habs, hdir, hdu, hsub, hc,
          un_u _ hiw, walk, hcross, Nat.min_eq_right (by omega : infMag ≤ n - m), encode]
    · have hdu : ¬ (u n).val > (u m).val := by rw [u_val n hnw, u_val m hmw]; omega
      have hsub := u_sub hmw hnw (by omega : n ≤ m)
      have hdiffw : m - n < wordSize := by omega
      simp [model, hx', hlarge, habs, hdir, hdu, hsub,
        un_u _ hdiffw, walk, hcross, encode]
  · have hdir' : (F64.signbit x != d) = false := Bool.eq_false_iff.mpr hdir
    have hsub := u_sub hiw hmw hm
    have hdiffw : infMag - m < wordSize := by omega
    by_cases hsat : infMag - m < n
    · have hc : (u (infMag - m)).val < (u n).val := by
        rw [u_val _ hdiffw, u_val _ hnw]
        omega
      simp [model, hx', hlarge, habs, hdir', hsub, hc, un_u _ hiw,
        walk, Nat.min_eq_right (by omega : infMag ≤ m + n), encode]
    · have hc : ¬ (u (infMag - m)).val < (u n).val := by
        rw [u_val _ hdiffw, u_val _ hnw]
        omega
      have hsumw : m + n < wordSize := by omega
      simp [model, hx', hlarge, habs, hdir', hsub, hc, u_add hmw hnw,
        un_u _ hsumw, walk, Nat.min_eq_left (by omega : m + n ≤ infMag), encode]

theorem spec_encode (s d : Bool) {m : Nat} (n : Nat) (hm : m ≤ infMag) :
    spec (encode s m) d n = walk s d m n := by
  simp only [spec, not_nan_encode s hm, Bool.false_eq_true, ↓reduceIte,
    sign_encode s (by omega : m < signMask), mag_encode s (by omega : m < signMask)]

theorem min_add (m n : Nat) :
    min (min (m + 1) infMag + n) infMag = min (m + (n + 1)) infMag := by
  simp only [Nat.min_def]
  split <;> split <;> split <;> omega

theorem walk_step (s d : Bool) {m : Nat} (n : Nat) (hm : m ≤ infMag) :
    spec (walk s d m 1) d n = walk s d m (n + 1) := by
  by_cases hdir : s = d
  · subst d
    have heq : walk s s m 1 = encode s (min (m + 1) infMag) := by simp [walk]
    rw [heq, spec_encode s s n (Nat.min_le_right _ _)]
    simpa only [walk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] using
      congrArg (encode s) (min_add m n)
  · have hdiff : (s != d) = true := by simp [hdir]
    have hneg : (!s) = d := by cases s <;> cases d <;> simp_all
    by_cases hz : m = 0
    · subst m
      have heq : walk s d 0 1 = encode d 1 := by simp [walk, hdiff, hneg]
      rw [heq, spec_encode d d n (by decide)]
      simp [walk, hdiff, hneg, Nat.add_comm]
    · have heq : walk s d m 1 = encode s (m - 1) := by
        simp [walk, hdiff, show ¬ 1 > m by omega]
      rw [heq, spec_encode s d n (by omega)]
      simp only [walk, hdiff, ↓reduceIte]
      by_cases hc : n > m - 1
      · have hc' : n + 1 > m := by omega
        simp only [hc, hc', ↓reduceIte]
        have he : n - (m - 1) = n + 1 - m := by omega
        rw [he]
      · have hc' : ¬ n + 1 > m := by omega
        simp only [hc, hc', ↓reduceIte]
        have he : m - 1 - n = m - (n + 1) := by omega
        rw [he]

theorem spec_zero (x : F64) (d : Bool) : spec x d 0 = x := by
  by_cases hx : F64.isnan x = true
  · simp [spec, hx]
  have hx' : F64.isnan x = false := Bool.eq_false_iff.mpr hx
  have hm := not_nan_mag hx'
  have hw : walk (F64.signbit x) d (F64.toBits x % signMask) 0 =
      encode (F64.signbit x) (F64.toBits x % signMask) := by
    cases F64.signbit x <;> cases d <;> simp [walk, Nat.min_eq_left hm]
  simp only [spec, hx', Bool.false_eq_true, ↓reduceIte, hw, encode_input]

theorem spec_step (x : F64) (d : Bool) (n : Nat) :
    spec (spec x d 1) d n = spec x d (n + 1) := by
  by_cases hx : F64.isnan x = true
  · simp [spec, hx]
  have hx' : F64.isnan x = false := Bool.eq_false_iff.mpr hx
  simp only [spec, hx', Bool.false_eq_true, ↓reduceIte]
  exact walk_step _ _ n (not_nan_mag hx')

theorem spec_iter (d : Bool) (n : Nat) (x : F64) :
    spec x d n = iter (fun y => spec y d 1) n x := by
  induction n generalizing x with
  | zero => exact spec_zero x d
  | succ n ih =>
    change spec x d (n + 1) = iter (fun y => spec y d 1) n (spec x d 1)
    rw [← ih]
    exact (spec_step x d n).symm

theorem next_pos (x : F64) (n : Nat) :
    F64.nextfloat x (n : Int) = spec x false n := by
  have hs : ¬ (n : Int) < 0 := by omega
  simp [next_model, model_spec, hs]

theorem next_neg (x : F64) (n : Nat) :
    F64.nextfloat x (-(n : Int)) = spec x true n := by
  by_cases hn : n = 0
  · subst n
    simp [next_model, model_spec, spec_zero]
  · have hs : 0 < n := by omega
    simp [next_model, model_spec, hs]

theorem prev_pos (x : F64) (n : Nat) :
    F64.prevfloat x (n : Int) = spec x true n := by
  by_cases hn : n = 0
  · subst n
    simp [prev_model, model_spec, spec_zero]
  · have hs : 0 < n := by omega
    simp [prev_model, model_spec, hs]

theorem prev_neg (x : F64) (n : Nat) :
    F64.prevfloat x (-(n : Int)) = spec x false n := by
  have hs : ¬ (n : Int) < 0 := by omega
  simp [prev_model, model_spec, hs]

end ProofNext

theorem nextfloatIterate_proven : NextfloatIterate := by
  intro x n
  have hp : (fun y => F64.nextfloat y 1) = (fun y => ProofNext.spec y false 1) :=
    funext (fun y => ProofNext.next_pos y 1)
  have hn : (fun y => F64.nextfloat y (-1)) = (fun y => ProofNext.spec y true 1) :=
    funext (fun y => ProofNext.next_neg y 1)
  rw [ProofNext.next_pos, ProofNext.next_neg, ProofNext.prev_pos, ProofNext.prev_neg, hp, hn]
  exact ⟨ProofNext.spec_iter false n x, ProofNext.spec_iter true n x,
    ProofNext.spec_iter true n x, ProofNext.spec_iter false n x⟩

end JuliaLean.FloatFuncs
