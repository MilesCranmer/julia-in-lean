import JuliaLean.base.channels
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.channels.Round1

open JuliaLean JuliaLean.base.channels

/-- Mathematical exact-value relation for the binary64 representation already used
by the installed float model. This is an input denotation, not a replacement callee. -/
def ExactFloat64Integer (size : JuliaLean.base.float.FV .f64) (integer : Int) : Prop :=
  size.expField < 2047 ∧
  size.toRat.1 = integer * (size.toRat.2 : Int)

/-- On the repository's 64-bit Int model, every Float64 constructor argument follows
its exact numeric value: positive infinity selects maximum Int capacity; an exact
in-range integer has precisely the integer constructor's outcome; every other value
raises InexactError before channel allocation. The integer-constructor comparison
preserves all errors and divergence and includes negative sizes and both zero signs.
Julia source: base/channels.jl:43-58; base/float.jl:921-932 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/channels.jl:13-30; base/essentials.jl:423-440; doc/src/manual/conversion-and-promotion.md:42-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ChannelFloat64ExactNumericDispatch : Prop :=
  ∀ (E W C Cond Lock Task Waiter Token T : Type)
    (runtime : Runtime E W C Cond Lock Task Waiter Token T)
    (size : JuliaLean.base.float.FV .f64) (world : W),
    (size.toBits = 0x7ff0000000000000 →
      (constructFloat64 runtime size).run world =
        (construct runtime (i ((2 : Int)^63 - 1))).run world) ∧
    (∀ integer : Int,
      ExactFloat64Integer size integer →
      -((2 : Int)^63) ≤ integer → integer < (2 : Int)^63 →
      (constructFloat64 runtime size).run world =
        (construct runtime (i integer)).run world) ∧
    (size.toBits ≠ 0x7ff0000000000000 →
      (¬ ∃ integer : Int,
        ExactFloat64Integer size integer ∧
        -((2 : Int)^63) ≤ integer ∧ integer < (2 : Int)^63) →
      (constructFloat64 runtime size).run world =
        some (.error (.julia (.inexactError "Int64"), world)))

/-!
Public plumbing dispositions (review check 2):
* push!(::AbstractChannel, v), source10, delegates put! and returns the same
  channel as fluent-interface glue; its put!/blocking/conversion/error behavior
  remains in the complete public put! contracts.
* popfirst!(::AbstractChannel), source11, forwards take! and its result/errors.
* Channel(sz=0), source58, selects Channel{Any}; Channel(func,args...;kwargs...),
  source158, forwards the callable/arguments/keywords to Channel{Any}. The full
  construction and callable lifecycle contracts remain in the TSV.
* close(::Channel), source199, supplies closed_exception() to the full close
  method. Default-error construction and actual close behavior remain retained.
* eltype(::Type{Channel{T}}), source748, exposes type parameter T as metadata.
* IteratorSize(::Type{<:Channel}), source794, supplies SizeUnknown metadata;
  full iteration and channel lifetime behavior is retained separately.
These wrappers and traits have no independent behavioral property beyond their
selected callees or type metadata; body/constant equalities would fail check 3c.
Julia source: base/channels.jl at the method lines above
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/

end JuliaLean.Proofs.base.channels.Round1

namespace JuliaLean.Proofs.base.channels

open JuliaLean.Registry

end JuliaLean.Proofs.base.channels


namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean JuliaLean.base.float JuliaLean.base.channels
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.channels.Round1

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

private theorem channelFinite (x : FV .f64) :
    x.isfinite = true ↔ x.expField < 2047 := by
  have he : x.expField < 2048 := Nat.mod_lt _ (by decide)
  change (x.expField != 2047) = true ↔ x.expField < 2047
  simp only [bne_iff_ne]
  omega

private theorem channelDenPos (x : FV .f64) (h : x.isfinite = true) :
    0 < x.toRat.2 := by
  let e := x.expField
  let m := x.frac + if e == 0 then 0 else 2 ^ FTy.f64.fmt.sb
  let p : Int := if e == 0 then 1 - (FTy.f64.fmt.bias : Int) - FTy.f64.fmt.sb
    else (e : Int) - FTy.f64.fmt.bias - FTy.f64.fmt.sb
  let s : Int := if x.signbit then -(m : Int) else (m : Int)
  unfold Fl.toRat
  rw [h]
  change 0 < (if p ≥ 0 then (s * ((2 ^ p.toNat : Nat) : Int), 1)
    else (s, 2 ^ (-p).toNat)).2
  by_cases hp : p ≥ 0
  · rw [if_pos hp]
    exact Nat.zero_lt_succ _
  · rw [if_neg hp]
    exact Nat.two_pow_pos _

private theorem channelExactTrunc (x : FV .f64) (k : Int)
    (h : ExactFloat64Integer x k) :
    x.isinteger = true ∧ x.truncVal = k := by
  have hf := (channelFinite x).mpr h.1
  have hd : (x.toRat.2 : Int) ≠ 0 := by have := channelDenPos x hf; omega
  constructor
  · simp only [Fl.isinteger, hf, h.2, Int.mul_emod_left, beq_self_eq_true, Bool.and_self]
  · simp only [Fl.truncVal, h.2, Int.mul_tdiv_cancel _ hd]

private theorem channelExactOfInteger (x : FV .f64) (h : x.isinteger = true) :
    ExactFloat64Integer x x.truncVal := by
  have hf : x.isfinite = true := (Bool.and_eq_true_iff.mp h).1
  have hm : x.toRat.1 % (x.toRat.2 : Int) = 0 := by
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
  refine ⟨(channelFinite x).mp hf, ?_⟩
  exact (Int.tdiv_mul_cancel (Int.dvd_of_emod_eq_zero hm)).symm

private theorem channelInfEq (x : FV .f64) :
    eq_IEEEFloat x Inf64 = decide (x.toBits = 0x7ff0000000000000) := by
  have he : Inf64.toBits = 0x7ff0000000000000 := by decide
  have hn : Inf64.isnan = false := by decide
  have hz : Inf64.iszero = false := by decide
  simp only [eq_IEEEFloat, eq_float, JuliaLean.C.jlEqFloat, Fl.eq, he, hn, hz,
    Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false]
  by_cases hb : x.toBits = 0x7ff0000000000000
  · have hx : x.isnan = false := by
      change (x.toBits / 4503599627370496 % 2048 == 2047 &&
        x.toBits % 4503599627370496 != 0) = false
      rw [hb]
      decide
    simp only [hb, hx, Bool.not_false, beq_self_eq_true, Bool.true_and, decide_true]
  · simp only [beq_eq_false_iff_ne.mpr hb, Bool.and_false, decide_eq_false hb]

/-- Positive infinity selects the integer constructor without evaluating a conversion. -/
theorem channelPositiveInfinityDispatch
    (E W C Cond Lock Task Waiter Token T : Type)
    (runtime : Runtime E W C Cond Lock Task Waiter Token T)
    (x : FV .f64) (world : W) (h : x.toBits = 0x7ff0000000000000) :
    (constructFloat64 runtime x).run world =
      (construct runtime (i ((2 : Int)^63 - 1))).run world := by
  unfold constructFloat64
  rw [channelInfEq, if_pos (by simp only [h, decide_true])]
  rfl


private abbrev channelBitRange (x : FV .f64) : Prop :=
  (x.signbit = false ∧ x.expField < 1086) ∨
  (x.signbit = true ∧ (x.expField < 1086 ∨ x.expField = 1086 ∧ x.frac = 0))

private theorem channelRawBounds (x : FV .f64) :
    (le_IEEEFloat (floatOfInt .f64 (JuliaLean.base.int.typemin .i64)) x &&
      lt_IEEEFloat x (floatOfInt .f64 (JuliaLean.base.int.typemax .i64))) =
        decide (channelBitRange x) := by
  have hlo : floatOfInt .f64 (JuliaLean.base.int.typemin .i64) =
      (Fl.ofBits 0xc3e0000000000000 : FV .f64) := by decide
  have hhi : floatOfInt .f64 (JuliaLean.base.int.typemax .i64) =
      (Fl.ofBits 0x43e0000000000000 : FV .f64) := by decide
  have hx : x.toBits < 18446744073709551616 := x.bits.isLt
  have hexp : x.expField = x.toBits / 4503599627370496 % 2048 := rfl
  have hfrac : x.frac = x.toBits % 4503599627370496 := rfl
  have hlob : (Fl.ofBits 0xc3e0000000000000 : FV .f64).toBits = 14114281232179134464 := by decide
  have hhib : (Fl.ofBits 0x43e0000000000000 : FV .f64).toBits = 4890909195324358656 := by decide
  have hlon : (Fl.ofBits 0xc3e0000000000000 : FV .f64).isnan = false := by decide
  have hhin : (Fl.ofBits 0x43e0000000000000 : FV .f64).isnan = false := by decide
  have hloz : (Fl.ofBits 0xc3e0000000000000 : FV .f64).iszero = false := by decide
  have hhiz : (Fl.ofBits 0x43e0000000000000 : FV .f64).iszero = false := by decide
  have hlos : (Fl.ofBits 0xc3e0000000000000 : FV .f64).signbit = true := by decide
  have hhis : (Fl.ofBits 0x43e0000000000000 : FV .f64).signbit = false := by decide
  rw [hlo, hhi]
  apply Bool.eq_iff_iff.mpr
  simp only [le_IEEEFloat, le_float, JuliaLean.C.jlLeFloat,
    lt_IEEEFloat, lt_float, JuliaLean.C.jlLtFloat, Fl.le, Fl.lt, Fl.eq,
    hlob, hhib, hlon, hhin, hloz, hhiz, hlos, hhis]
  simp only [decide_eq_true_eq]
  cases hn : x.isnan <;> cases hs : x.signbit
  all_goals
    have hnBits := hn
    have hsBits := hs
    change (x.expField == 2047 && x.frac != 0) = _ at hnBits
    change decide (x.toBits ≥ 9223372036854775808) = _ at hsBits
    simp only [hexp, hfrac] at hnBits ⊢
    simp at hnBits hsBits
    simp [channelBitRange, hn, hs, hexp, hfrac] <;> omega

private theorem channelToRat (x : FV .f64) (hf : x.isfinite = true) :
    x.toRat =
      if x.expField = 0 then
        ((if x.signbit then -(x.frac : Int) else (x.frac : Int)), 2 ^ 1074)
      else if x.expField < 1075 then
        ((if x.signbit then -((x.frac + 4503599627370496 : Nat) : Int)
            else ((x.frac + 4503599627370496 : Nat) : Int)), 2 ^ (1075 - x.expField))
      else
        ((if x.signbit then -((x.frac + 4503599627370496 : Nat) : Int)
            else ((x.frac + 4503599627370496 : Nat) : Int)) *
            ((2 ^ (x.expField - 1075) : Nat) : Int), 1) := by
  unfold Fl.toRat
  rw [hf]
  change (let e := x.expField
    let m := x.frac + if e == 0 then 0 else 4503599627370496
    let p : Int := if e == 0 then -1074 else (e : Int) - 1023 - 52
    let v : Int := if x.signbit then -(m : Int) else (m : Int)
    if p ≥ 0 then (v * ((2 ^ p.toNat : Nat) : Int), 1) else (v, 2 ^ (-p).toNat)) = _
  by_cases he : x.expField = 0
  · have hp : ¬ ((-1074 : Int) ≥ 0) := by decide
    simp only [he, beq_self_eq_true, ite_true, Int.reduceNeg, hp,
      Int.reduceToNat, ite_false, Nat.add_zero]
  · have hb : (x.expField == 0) = false := beq_eq_false_iff_ne.mpr he
    simp only [hb, Bool.false_eq_true, ite_false, he]
    by_cases hl : x.expField < 1075
    · have hp : ¬ (0 : Int) ≤ (x.expField : Int) - 1023 - 52 := by omega
      have hn : (-((x.expField : Int) - 1023 - 52)).toNat = 1075 - x.expField := by omega
      simp only [hp, ite_false, hl, ite_true, hn]
    · have hp : (0 : Int) ≤ (x.expField : Int) - 1023 - 52 := by omega
      have hn : ((x.expField : Int) - 1023 - 52).toNat = x.expField - 1075 := by omega
      simp only [hp, ite_true, hl, ite_false, hn]

private theorem channelSmallRationalBounds (m d : Nat) (negative : Bool)
    (hm : m < 9223372036854775808) (hd : 0 < d) :
    -9223372036854775808 * (d : Int) ≤ (if negative then -(m : Int) else (m : Int)) ∧
      (if negative then -(m : Int) else (m : Int)) < 9223372036854775808 * (d : Int) := by
  cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem channelRatBounds (x : FV .f64) (hf : x.isfinite = true) :
    (-9223372036854775808 * (x.toRat.2 : Int) ≤ x.toRat.1 ∧
      x.toRat.1 < 9223372036854775808 * (x.toRat.2 : Int)) ↔ channelBitRange x := by
  have hfrac : x.frac < 4503599627370496 := Nat.mod_lt _ (by decide)
  rw [channelToRat x hf]
  by_cases he : x.expField = 0
  · simp only [he, ite_true, Prod.fst, Prod.snd]
    have hr := channelSmallRationalBounds x.frac (2 ^ 1074) x.signbit (by omega)
      (Nat.two_pow_pos _)
    have hb : channelBitRange x := by
      cases hs : x.signbit <;> simp [channelBitRange, hs, he] <;> omega
    exact ⟨fun _ => hb, fun _ => hr⟩
  · simp only [he, ite_false]
    by_cases hl : x.expField < 1075
    · simp only [hl, ite_true, Prod.fst, Prod.snd]
      have hr := channelSmallRationalBounds (x.frac + 4503599627370496)
        (2 ^ (1075 - x.expField)) x.signbit (by omega) (Nat.two_pow_pos _)
      have hb : channelBitRange x := by
        cases hs : x.signbit <;> simp [channelBitRange, hs] <;> omega
      exact ⟨fun _ => hb, fun _ => hr⟩
    · simp only [hl, ite_false, Prod.fst, Prod.snd, Int.natCast_one, Int.mul_one]
      by_cases hsmall : x.expField < 1086
      · have hp : 2 ^ (x.expField - 1075) ≤ 1024 :=
          Nat.pow_le_pow_right (n := 2) (by decide) (show x.expField - 1075 ≤ 10 by omega)
        have hprod : (x.frac + 4503599627370496) * 2 ^ (x.expField - 1075) <
            9223372036854775808 := by
          have h := Nat.mul_le_mul_left (x.frac + 4503599627370496) hp
          omega
        have hr := channelSmallRationalBounds
          ((x.frac + 4503599627370496) * 2 ^ (x.expField - 1075)) 1 x.signbit hprod (by decide)
        have hb : channelBitRange x := by
          cases hs : x.signbit <;> simp [channelBitRange, hs, hsmall] <;> omega
        have hr' : -9223372036854775808 ≤
            (if x.signbit then -((x.frac + 4503599627370496 : Nat) : Int)
              else ((x.frac + 4503599627370496 : Nat) : Int)) *
                ((2 ^ (x.expField - 1075) : Nat) : Int) ∧
            (if x.signbit then -((x.frac + 4503599627370496 : Nat) : Int)
              else ((x.frac + 4503599627370496 : Nat) : Int)) *
                ((2 ^ (x.expField - 1075) : Nat) : Int) < 9223372036854775808 := by
          cases hs : x.signbit <;>
            simpa only [hs, Bool.false_eq_true, ite_false, ite_true,
              Int.natCast_mul, Int.natCast_one, Int.mul_one, Int.neg_mul] using hr
        exact ⟨fun _ => hb, fun _ => hr'⟩
      · by_cases heq : x.expField = 1086
        · simp only [heq, Nat.reduceSub, Nat.reducePow]
          cases hs : x.signbit <;>
            simp [channelBitRange, hs, heq, Int.natCast_add] <;> omega
        · have hp : 4096 ≤ 2 ^ (x.expField - 1075) :=
            Nat.pow_le_pow_right (n := 2) (by decide) (show 12 ≤ x.expField - 1075 by omega)
          have hprod : 18446744073709551616 ≤
              (x.frac + 4503599627370496) * 2 ^ (x.expField - 1075) := by
            exact Nat.mul_le_mul (show 4503599627370496 ≤ x.frac + 4503599627370496 by omega) hp
          cases hs : x.signbit <;>
            simp only [channelBitRange, hs, Bool.false_eq_true, Bool.true_eq_false,
              ite_true, ite_false, Int.neg_mul, ← Int.natCast_mul] <;> omega

private theorem channelExactInRange (x : FV .f64) (k : Int)
    (h : ExactFloat64Integer x k) :
    channelBitRange x ↔ -9223372036854775808 ≤ k ∧ k < 9223372036854775808 := by
  have hf := (channelFinite x).mpr h.1
  have hd : (0 : Int) < x.toRat.2 := by have := channelDenPos x hf; omega
  rw [← channelRatBounds x hf, h.2]
  exact and_congr (Int.mul_le_mul_right hd) (Int.mul_lt_mul_right hd)

private theorem channelIntOfFloatExact (x : FV .f64) (k : Int)
    (h : ExactFloat64Integer x k) (hlo : -9223372036854775808 ≤ k)
    (hhi : k < 9223372036854775808) : intOfFloat .i64 x = .ok (i k) := by
  have hf := (channelFinite x).mpr h.1
  obtain ⟨hi, ht⟩ := channelExactTrunc x k h
  have hb : channelBitRange x := (channelExactInRange x k h).mpr ⟨hlo, hhi⟩
  have hc : (le_IEEEFloat (floatOfInt .f64 (JuliaLean.base.int.typemin .i64)) x &&
      lt_IEEEFloat x (floatOfInt .f64 (JuliaLean.base.int.typemax .i64))) = true := by
    rw [channelRawBounds]
    exact decide_eq_true hb
  change (if ((le_IEEEFloat (floatOfInt .f64 (JuliaLean.base.int.typemin .i64)) x &&
      lt_IEEEFloat x (floatOfInt .f64 (JuliaLean.base.int.typemax .i64))) && x.isinteger) then
        (Except.ok (fptosi .i64 x) : Jl (JInt .i64)) else Except.error (.inexactError "Int64")) = .ok (i k)
  rw [hc, hi]
  simp only [Bool.and_self, ite_true]
  congr 1
  change JuliaLean.C.toJInt .i64 (JuliaLean.C.jlFptosi 64 x) = i k
  unfold JuliaLean.C.jlFptosi
  rw [hf, ht]
  simp only [ite_true, JuliaLean.C.toJInt, IntTy.signed, IntTy.bits, ite_true]
  rw [BitVec.toInt_ofInt_eq_self (by decide) hlo hhi]
  rfl

private theorem channelIntOfFloatInvalid (x : FV .f64)
    (h : ¬ ∃ k : Int, ExactFloat64Integer x k ∧
      -9223372036854775808 ≤ k ∧ k < 9223372036854775808) :
    intOfFloat .i64 x = .error (.inexactError "Int64") := by
  have hc : ¬ ((le_IEEEFloat (floatOfInt .f64 (JuliaLean.base.int.typemin .i64)) x &&
      lt_IEEEFloat x (floatOfInt .f64 (JuliaLean.base.int.typemax .i64))) && x.isinteger) = true := by
    intro hc
    obtain ⟨hb, hi⟩ := Bool.and_eq_true_iff.mp hc
    have he := channelExactOfInteger x hi
    rw [channelRawBounds] at hb
    have hr := (channelExactInRange x x.truncVal he).mp (of_decide_eq_true hb)
    exact h ⟨x.truncVal, he, hr⟩
  change (if ((le_IEEEFloat (floatOfInt .f64 (JuliaLean.base.int.typemin .i64)) x &&
      lt_IEEEFloat x (floatOfInt .f64 (JuliaLean.base.int.typemax .i64))) && x.isinteger) then
        (Except.ok (fptosi .i64 x) : Jl (JInt .i64)) else Except.error (.inexactError "Int64")) =
          .error (.inexactError "Int64")
  exact if_neg hc

private theorem channelExactNotInfinity (x : FV .f64) (k : Int)
    (h : ExactFloat64Integer x k) : x.toBits ≠ 0x7ff0000000000000 := by
  intro hb
  have he := h.1
  change x.toBits / 4503599627370496 % 2048 < 2047 at he
  rw [hb] at he
  simp only [Nat.reduceDiv, Nat.reduceMod] at he
  omega

/-- Full numeric dispatch for the installed Float64 channel constructor. -/
theorem ChannelsFloat64ExactNumericDispatch :
    JuliaLean.Proofs.base.channels.Round1.ChannelFloat64ExactNumericDispatch := by
  intro E W C Cond Lock Task Waiter Token T runtime x world
  refine ⟨channelPositiveInfinityDispatch E W C Cond Lock Task Waiter Token T runtime x world, ?_, ?_⟩
  · intro k hk hlo hhi
    have hn := channelExactNotInfinity x k hk
    unfold constructFloat64
    rw [channelInfEq, if_neg (by simpa only [decide_eq_true_eq] using hn)]
    rw [channelIntOfFloatExact x k hk hlo hhi]
    rfl
  · intro hn hk
    unfold constructFloat64
    rw [channelInfEq, if_neg (by simpa only [decide_eq_true_eq] using hn)]
    rw [channelIntOfFloatInvalid x hk]
    rfl

end JuliaLean.ChatGPT.Batch4.Group24

namespace JuliaLean.Proofs.base.channels

open JuliaLean.Registry
def entries : List Entry := [
  { id := "channels-float64-exact-numeric-dispatch", juliaFile := "base/channels.jl"
    juliaFns := ["Channel{T}(::Float64)"]
    statement := "On the Int64 model, Channel{T}(size::Float64) maps +Inf to typemax(Int), every exactly integral in-range size to the integer constructor's outcome, and every other value (NaN, -Inf, fractions, out-of-range) to InexactError before any allocation."
    source := "base/channels.jl:43-58; base/float.jl:921-932; doc/src/manual/conversion-and-promotion.md:42-54"
    status := .proven
    prop := ``JuliaLean.Proofs.base.channels.Round1.ChannelFloat64ExactNumericDispatch, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.ChannelsFloat64ExactNumericDispatch }
]

end JuliaLean.Proofs.base.channels
