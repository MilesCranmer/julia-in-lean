import JuliaLean.RangesCov.Ops

/-!
Methods of `base/twiceprecision.jl` (master `bbfa0ce4150`) for `Float64`, on top of the
`JuliaLean.FloatRanges` model of `TwicePrecision{Float64}` and
`StepRangeLen{Float64,TwicePrecision{Float64},TwicePrecision{Float64},Int}`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

namespace Twice

/-- The call returns normally. -/
def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-! ### Models -/

/-- `truncmask(x, mask) = x` for non-IEEE types, base/twiceprecision.jl:31. -/
def truncmaskGeneric {α : Type} (x : α) (_ : Nat) : α := x

/-- `truncbits(x, nb) = x` for non-IEEE types, base/twiceprecision.jl:36. -/
def truncbitsGeneric {α : Type} (x : α) (_ : Int) : α := x

/-- `mul12(x::T, y::T) where {T} = (p = x * y; (p, zero(p)))`, base/twiceprecision.jl:118,
for integers. -/
def mul12Int (x y : Int) : Int × Int := let p := x * y; (p, 0)

/-- `*(x::TwicePrecision{<:IEEEFloat}, v::Integer)`, base/twiceprecision.jl:310-315, for
`v::Int`; `abs(v) - 1` wraps for `typemin(Int)`. -/
def mulInt (x : TP) (v : I64) : TP :=
  if v.val = 0 then ⟨Float.F64.mul x.hi (FloatRanges.flt v), Float.F64.mul x.lo (FloatRanges.flt v)⟩
  else
    let nb := FloatRanges.topSetBit (FloatRanges.iabs v - FloatRanges.i64 1)
    let u := FloatRanges.truncbits x.hi nb
    let (h, l) := FloatRanges.canonicalize2 (Float.F64.mul u (FloatRanges.flt v))
      (Float.F64.mul (Float.F64.add (Float.F64.sub x.hi u) x.lo) (FloatRanges.flt v))
    ⟨h, l⟩

/-- `<(x::TwicePrecision{T}, y::TwicePrecision{T})`, base/twiceprecision.jl:787-788. -/
def tpLt (x y : TP) : Bool :=
  Float.F64.lt x.hi y.hi || (Float.F64.eq x.hi y.hi && Float.F64.lt x.lo y.lo)

/-- `sumpair(n) = iseven(n) ? (n+1, n>>1) : (n, (n+1)>>1)`, base/twiceprecision.jl:625;
`>>` is an arithmetic shift (floor division by 2). -/
def sumpair (n : Num) : Num × Num :=
  if n.val % 2 = 0 then (Ranges.Num.add n (Ranges.Num.one n.ty), Ranges.Num.lit n.ty (n.val / 2))
  else (n, Ranges.Num.lit n.ty ((Ranges.Num.add n (Ranges.Num.one n.ty)).val / 2))

/-- `sum(r::StepRangeLen)`, base/twiceprecision.jl:591-605, for an integer `StepRangeLen`
with an `Int` length (`W = widen(Int) = Int128`). -/
def sumInt (r : Ranges.RngLen) : Jl Num := do
  let l := r.len
  let np := Ranges.Num.sub l r.offset
  let nn := Ranges.Num.sub r.offset (Ranges.Num.one r.offset.ty)
  let sp := sumpair np
  let sn := sumpair nn
  let W : NType := .bit .i128
  let a ← Ranges.Num.cast W sp.1
  let b ← Ranges.Num.cast W sp.2
  let c ← Ranges.Num.cast W sn.1
  let d ← Ranges.Num.cast W sn.2
  let Δn := Ranges.Num.sub (Ranges.Num.mul a b) (Ranges.Num.mul c d)
  let s := Ranges.Num.mul r.stride Δn
  let ref := Ranges.Num.mul r.ref l
  Ranges.Num.cast r.elementTy (Ranges.Num.add s ref)

/-- `_linspace(::Type{Float64}, start::Integer, stop::Integer, len::Integer) =
_linspace(Float64, start, stop, len, one(start))`, base/twiceprecision.jl:717, for `Int`. -/
def linspaceInt (a b len : I64) : Jl FloatRanges.SRL :=
  FloatRanges.linspaceRat a b len (FloatRanges.i64 1)

/-- `_linspace(Float64, start_n, stop_n, len, den)`, base/twiceprecision.jl:718-734, for
`Int128` numerators and denominator and an `Int` length (`W = widen(Int) = Int128`). -/
def linspaceRat128 (start_n stop_n den : JInt .i128) (len : I64) : Jl FloatRanges.SRL := do
  if len.val < 2 then
    return ← FloatRanges.linspace1 (Float.F64.div (FloatRanges.flt start_n) (FloatRanges.flt den))
      (Float.F64.div (FloatRanges.flt stop_n) (FloatRanges.flt den)) len
  if start_n.val = stop_n.val then
    return ← FloatRanges.hpRatio start_n den (JInt.wrap .i128 0) den 0 len (FloatRanges.i64 1)
  let tmin := Float.F64.div (FloatRanges.flt (-start_n))
    (Float.F64.sub (FloatRanges.flt stop_n) (FloatRanges.flt start_n))
  let r ← Float.F64.roundInt .i64
    (Float.F64.add (Float.F64.mul tmin (FloatRanges.flt (len - FloatRanges.i64 1))) Float.F64.one)
  let imin := FloatRanges.iclamp r (FloatRanges.i64 1) len
  let w (x : I64) : JInt .i128 := JInt.wrap .i128 x.val
  let ref_num := w (len - imin) * start_n + w (imin - FloatRanges.i64 1) * stop_n
  let ref_denom := w (len - FloatRanges.i64 1) * den
  FloatRanges.hpRatio ref_num ref_denom (stop_n - start_n) ref_denom (FloatRanges.nbitslen len imin)
    len imin

/-- `/(r::StepRangeLen{<:Real,<:TwicePrecision}, x::Real)`, base/twiceprecision.jl:538-539. -/
def divScalar (r : FloatRanges.SRL) (x : F64) : Jl FloatRanges.SRL :=
  FloatRanges.SRL.mk' (r.ref.divF x) ((r.step.divF x).trunc (FloatRanges.nbitslen r.len r.offset))
    r.len r.offset

/-- `*(r::StepRangeLen{<:Real,<:TwicePrecision}, x::Real) = x*r`, base/twiceprecision.jl:537. -/
def mulScalarRight (r : FloatRanges.SRL) (x : F64) : Jl FloatRanges.SRL :=
  FloatRanges.SRL.scalarMul x r

/-- `_getindex_hiprec(r::StepRangeLen{<:Any,<:TwicePrecision,<:TwicePrecision}, i)`,
base/twiceprecision.jl:488-495. -/
def getindexHiprec (r : FloatRanges.SRL) (i : Num) : Jl TP := do
  if i.ty = .bool then throw (.argumentError "invalid index of type Bool")
  let ii ← Ranges.Num.cast (.bit .i64) i
  let u : I64 := JInt.wrap .i64 ii.val - r.offset
  let shift_hi := Float.F64.mul (FloatRanges.flt u) r.step.hi
  let shift_lo := Float.F64.mul (FloatRanges.flt u) r.step.lo
  let (x_hi, x_lo) := FloatRanges.add12 r.ref.hi shift_hi
  let (x_hi, x_lo) := FloatRanges.add12 x_hi (Float.F64.add x_lo (Float.F64.add shift_lo r.ref.lo))
  pure ⟨x_hi, x_lo⟩

/-- `+(r1::StepRangeLen{T,R}, r2::StepRangeLen{T,R}) where R<:TwicePrecision`,
base/twiceprecision.jl:627-642. -/
def addSrl (r1 r2 : FloatRanges.SRL) : JlX FloatRanges.SRL := do
  let len := r1.len
  if len ≠ r2.len then throw (.dimensionMismatch "argument dimensions must match")
  let (imid, ref) ← if r1.offset = r2.offset then pure (r1.offset, FloatRanges.TP.add r1.ref r2.ref)
    else do
      let imid ← lift (Float.F64.roundInt .i64
        (Float.F64.div (FloatRanges.flt (r1.offset + r2.offset)) (FloatRanges.dec 2)))
      let a ← lift (getindexHiprec r1 (mkI .i64 imid))
      let b ← lift (getindexHiprec r2 (mkI .i64 imid))
      pure (imid, FloatRanges.TP.add a b)
  let step := (FloatRanges.TP.add r1.step r2.step).trunc (FloatRanges.nbitslen len imid)
  lift (FloatRanges.SRL.mk' ref step len imid)

/-- `range_start_step_length(a::Real, st::IEEEFloat, len)`, base/twiceprecision.jl:441-442,
for `a::Int`: promote, then the Float64 method. -/
def rsslIntFloat (a : I64) (st : F64) (len : I64) : Jl FloatRanges.SRL :=
  FloatRanges.rangeStartStepLength (FloatRanges.flt a) st len

/-- `range_start_step_length(a::IEEEFloat, st::Real, len)`, base/twiceprecision.jl:444-445. -/
def rsslFloatInt (a : F64) (st : I64) (len : I64) : Jl FloatRanges.SRL :=
  FloatRanges.rangeStartStepLength a (FloatRanges.flt st) len

/-- `range_step_stop_length(step::Real, stop::IEEEFloat, len)`, base/twiceprecision.jl:468-469. -/
def rsslStepIntStop (st : I64) (stop : F64) (len : I64) : Jl FloatRanges.SRL :=
  FloatRanges.rangeStepStopLength (FloatRanges.flt st) stop len

/-- `range_step_stop_length(step::IEEEFloat, stop::Real, len)`, base/twiceprecision.jl:471-472. -/
def rsslStepStopInt (st : F64) (stop : I64) (len : I64) : Jl FloatRanges.SRL :=
  FloatRanges.rangeStepStopLength st (FloatRanges.flt stop) len

/-! ### Elements of an integer `StepRangeLen` -/

/-- The mathematical value of element `k + 1` of an integer `StepRangeLen`. -/
def elemVal (r : Ranges.RngLen) (k : Nat) : Int :=
  r.ref.val + ((k : Int) + 1 - r.offset.val) * r.stride.val

/-- Every element of `r` is representable in its element type. -/
def elemsFit (r : Ranges.RngLen) : Prop :=
  ∀ k : Nat, k < r.len.val.toNat →
    ∃ t, r.elementTy = .bit t ∧ t.min ≤ elemVal r k ∧ elemVal r k ≤ t.max

/-- `sum(collect(r))`: the exact sum of the elements. -/
def elemSum (r : Ranges.RngLen) : Int :=
  ((List.range r.len.val.toNat).map (elemVal r)).sum

/-! ### Properties -/

/-- `truncbits(x, 0)` keeps every bit and `truncmask(x, 0)` clears every bit
(base/twiceprecision.jl:28-35). -/
def TruncbitsIdentity : Prop :=
  (∀ x : F64, FloatRanges.truncbits x 0 = x) ∧ (∀ x : F64, FloatRanges.truncmask x 0 = Float.F64.ofBits 0)

theorem truncbitsIdentity_proven : TruncbitsIdentity := by
  refine ⟨?_, ?_⟩
  · intro x
    apply BitVec.eq_of_toNat_eq
    have hm : FloatRanges.shlMask 0 = 2 ^ 64 - 1 := by decide
    have hl : (2 ^ 64 - 1) &&& x.toNat = x.toNat % 2 ^ 64 := by
      rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod _ _
    show (BitVec.ofNat 64 ((FloatRanges.shlMask 0) &&& x.toNat)).toNat = x.toNat
    rw [hm, hl, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt x.isLt]
  · intro x
    show Float.F64.ofBits (0 &&& Float.F64.toBits x) = Float.F64.ofBits 0
    rw [Nat.zero_and]

/-- The non-IEEE fallbacks `truncmask(x, mask) = x` and `truncbits(x, nb) = x` return
their argument unchanged (base/twiceprecision.jl:31,36). -/
def TruncGenericIdentity : Prop :=
  (∀ (α : Type) (x : α) (m : Nat), truncmaskGeneric x m = x) ∧
  (∀ (α : Type) (x : α) (nb : Int), truncbitsGeneric x nb = x)

theorem truncGenericIdentity_proven : TruncGenericIdentity := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- `hi` of `canonicalize2(big, little)` is the rounded sum `big + little`
(base/twiceprecision.jl:48-51). -/
def Canonicalize2Hi : Prop := ∀ b l : F64, (FloatRanges.canonicalize2 b l).1 = Float.F64.add b l

theorem canonicalize2Hi_proven : Canonicalize2Hi := fun _ _ => rfl

/-- `zhi` of `mul12(x, y)` is the rounded product `x * y`, and a non-finite product is
returned in both components (base/twiceprecision.jl:114-117). -/
def Mul12Hi : Prop :=
  ∀ x y : F64, (FloatRanges.mul12 x y).1 = Float.F64.mul x y ∧
    (Float.F64.isfinite (Float.F64.mul x y) = false →
      FloatRanges.mul12 x y = (Float.F64.mul x y, Float.F64.mul x y))

theorem mul12Hi_proven : Mul12Hi := by
  intro x y
  refine ⟨?_, fun h => ?_⟩
  · simp only [FloatRanges.mul12]; split <;> rfl
  · simp [FloatRanges.mul12, h]

/-- The generic `mul12(x::T, y::T)` for integers returns the exact product with a zero low
part (base/twiceprecision.jl:118). -/
def Mul12IntExact : Prop := ∀ x y : Int, (mul12Int x y).1 + (mul12Int x y).2 = x * y

theorem mul12IntExact_proven : Mul12IntExact := fun x y => by simp [mul12Int]

/-- Negating a `TwicePrecision` twice gives it back (base/twiceprecision.jl:279). -/
def TpNegInvolution : Prop := ∀ x : TP, x.neg.neg = x

theorem tpNegInvolution_proven : TpNegInvolution := FloatRanges.TP.neg_neg

/-- `<` on `TwicePrecision` is irreflexive (base/twiceprecision.jl:787-788). -/
def TpLtIrrefl : Prop := ∀ x : TP, tpLt x x = false

theorem f64_lt_irrefl (x : F64) : Float.F64.lt x x = false := by
  unfold Float.F64.lt; split
  · rfl
  · split
    · simp_all
    · split <;> simp

theorem tpLtIrrefl_proven : TpLtIrrefl := by
  intro x; simp [tpLt, f64_lt_irrefl]

/-- `isbetween(a, x, b)` is symmetric in its bounds (base/twiceprecision.jl:790). -/
def IsbetweenSymmetric : Prop :=
  ∀ a x b : F64, FloatRanges.isbetween a x b = FloatRanges.isbetween b x a

theorem isbetweenSymmetric_proven : IsbetweenSymmetric := by
  intro a x b; unfold FloatRanges.isbetween; cases (Float.F64.le a x && Float.F64.le x b) <;>
    cases (Float.F64.le b x && Float.F64.le x a) <;> rfl

/-- `nbitslen(Float64, len, offset)` never exceeds `cld(precision(Float64), 2) = 27`, and
`nbitslen(len, offset)` is 0 for `len < 2` (base/twiceprecision.jl:252-256). -/
def NbitslenBound : Prop :=
  (∀ len off : I64, FloatRanges.nbitslen len off ≤ 27) ∧
  (∀ len off : I64, len.val < 2 → FloatRanges.nbitslen0 len off = 0)

theorem nbitslenBound_proven : NbitslenBound :=
  ⟨fun _ _ => Int.min_le_left _ _, fun _ _ h => by simp [FloatRanges.nbitslen0, h]⟩

/-- `sumpair(n)` factors `sum(1:n)`: `2 * p[1] * p[2] == n * (n + 1)` for every `Int`
`0 <= n < 2^62` (base/twiceprecision.jl:624-625). -/
def SumpairProduct : Prop :=
  ∀ x : JInt .i64, 0 ≤ x.val → x.val < 2 ^ 62 →
    2 * ((sumpair (mkI .i64 x)).1.val * (sumpair (mkI .i64 x)).2.val) = x.val * (x.val + 1)

theorem sumpairProduct_proven : SumpairProduct := by
  intro x h0 h1
  have hmin : IntTy.i64.min = -(2 ^ 63) := by decide
  have hmax : IntTy.i64.max = 2 ^ 63 - 1 := by decide
  have hb : ∀ v : Int, 0 ≤ v → v < 2 ^ 62 + 1 → wrapInt .i64 v = v := fun v a b =>
    wrapInt_of_inRange .i64 v ⟨by rw [hmin]; omega, by rw [hmax]; omega⟩
  have hadd : (Ranges.Num.add (mkI .i64 x) (Ranges.Num.one (.bit .i64))).val = x.val + 1 := by
    rw [one_mkI, add_mkI, mkI_val, jadd_val, wrap_one_val]; exact hb _ (by omega) (by omega)
  by_cases he : x.val % 2 = 0
  · have hs : sumpair (mkI .i64 x) = (Ranges.Num.add (mkI .i64 x) (Ranges.Num.one (.bit .i64)),
        Ranges.Num.lit (.bit .i64) (x.val / 2)) := by
      unfold sumpair; rw [if_pos (by simpa using he)]; rfl
    rw [hs]
    show 2 * ((Ranges.Num.add (mkI .i64 x) (Ranges.Num.one (.bit .i64))).val * wrapInt .i64 (x.val / 2)) = _
    rw [hadd, hb _ (by omega) (by omega)]
    obtain ⟨q, hq⟩ : ∃ q, x.val = 2 * q := ⟨x.val / 2, by omega⟩
    have hq2 : x.val / 2 = q := by omega
    rw [hq2, hq]; grind
  · have hs : sumpair (mkI .i64 x) = (mkI .i64 x,
        Ranges.Num.lit (.bit .i64) ((Ranges.Num.add (mkI .i64 x) (Ranges.Num.one (.bit .i64))).val / 2)) := by
      unfold sumpair; rw [if_neg (by simpa using he)]; rfl
    rw [hs]
    show 2 * (x.val * wrapInt .i64 ((Ranges.Num.add (mkI .i64 x) (Ranges.Num.one (.bit .i64))).val / 2)) = _
    rw [hadd, hb _ (by omega) (by omega)]
    obtain ⟨q, hq⟩ : ∃ q, x.val = 2 * q + 1 := ⟨x.val / 2, by omega⟩
    have hq2 : (x.val + 1) / 2 = q + 1 := by omega
    rw [hq2, hq]; grind

/-- `sum(r)` of an integer `StepRangeLen` equals `sum(collect(r))` (the `sum` docstring:
small integer types are summed in `Int`), whenever every element is representable and the
exact sum fits in `Int`. -/
def SrlSumMatches : Prop :=
  ∀ r : Ranges.RngLen, r.len.ty = .bit .i64 → r.offset.ty = .bit .i64 → 0 ≤ r.len.val →
    1 ≤ r.offset.val → r.offset.val ≤ max 1 r.len.val → elemsFit r →
    -(2 ^ 62) ≤ elemSum r → elemSum r ≤ 2 ^ 62 →
    ∃ v, sumInt r = .ok v ∧ v.val = elemSum r

/-- `(Int8(1):Int8(100)) .* Int8(1)`, i.e. `StepRangeLen{Int8}(Int8(1), Int8(1), 100)`. -/
def sumR : Ranges.RngLen :=
  ⟨mkI .i8 ⟨1, by decide⟩, mkI .i8 ⟨1, by decide⟩, mkI .i64 ⟨100, by decide⟩,
    mkI .i64 ⟨1, by decide⟩, .bit .i8⟩

theorem srlSumMatches_refuted : ¬ SrlSumMatches := by
  intro h
  have hs : elemSum sumR = 5050 := by decide
  have hfit : elemsFit sumR := by
    intro k hk
    have hk' : k < 100 := by simpa [sumR, mkI, Ranges.Num.val] using hk
    refine ⟨.i8, rfl, ?_, ?_⟩ <;>
      simp [elemVal, sumR, mkI, Ranges.Num.val, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  obtain ⟨v, hv, _⟩ := h sumR rfl rfl (by decide) (by decide) (by decide) hfit
    (by rw [hs]; decide) (by rw [hs]; decide)
  have hbad : isOk (sumInt sumR) = false := by decide
  rw [hv] at hbad
  cases hbad

/-- `range(a, b; length=n)` for distinct `Int` endpoints and `n >= 2` returns a range
(the `range` docstring), through `_linspace(Float64, a, b, n)`. -/
def LinspaceIntSucceeds : Prop :=
  ∀ a b n : I64, a.val ≠ b.val → 2 ≤ n.val → isOk (linspaceInt a b n) = true

theorem linspaceIntSucceeds_refuted : ¬ LinspaceIntSucceeds := by
  intro h
  have hbad : isOk (linspaceInt (FloatRanges.i64 (IntTy.i64.max - 10)) (FloatRanges.i64 IntTy.i64.max)
      (FloatRanges.i64 3)) = false := by decide +kernel
  rw [h _ _ _ (by decide) (by decide)] at hbad
  cases hbad

/-- `range(a, b; length=n)` for integer endpoints has `n` elements whenever it returns
(the `range` docstring), through `_linspace(Float64, a, b, n)`. -/
def LinspaceIntLength : Prop :=
  ∀ a b n : I64, FloatRanges.LenIs n (linspaceInt a b n)

theorem linspaceIntLength_proven : LinspaceIntLength :=
  fun a b n => FloatRanges.linspaceRat_len a b n _

/-- For `Int128` endpoints `0 < a <= b`, the first element of `range(a, b; length=n)` is not
negative (elements lie between the endpoints). -/
def LinspaceIntPositive : Prop :=
  ∀ (a b : JInt .i128) (n : I64) (r : FloatRanges.SRL), 0 < a.val → a.val ≤ b.val → 2 ≤ n.val →
    linspaceRat128 a b (JInt.wrap .i128 1) n = .ok r → Float.F64.lt r.first FloatRanges.fzero = false

/-- `Int128(2)^126`. -/
def bigA : JInt .i128 := ⟨2 ^ 126, by decide⟩
/-- `Int128(2)^126 + Int128(2)^80`. -/
def bigB : JInt .i128 := ⟨2 ^ 126 + 2 ^ 80, by decide⟩

theorem linspaceIntPositive_refuted : ¬ LinspaceIntPositive := by
  intro h
  have hc : (match linspaceRat128 bigA bigB (JInt.wrap .i128 1) (FloatRanges.i64 4) with
      | .ok r => Float.F64.lt r.first FloatRanges.fzero
      | .error _ => false) = true := by decide +kernel
  revert hc
  cases hx : linspaceRat128 bigA bigB (JInt.wrap .i128 1) (FloatRanges.i64 4) with
  | error e => simp
  | ok r =>
    intro hc
    have := h bigA bigB (FloatRanges.i64 4) r (by decide) (by decide) (by decide) hx
    simp only at hc
    rw [this] at hc
    cases hc

/-- `floatrange(Float64, start_n, step_n, len, den)` has length `len`
(base/twiceprecision.jl:380-392). -/
def FloatrangeLength : Prop := ∀ a s len den : I64, FloatRanges.LenIs len (FloatRanges.floatrange a s len den)

theorem floatrangeLength_proven : FloatrangeLength := FloatRanges.floatrange_len

/-- `steprangelen_hp(Float64, ref::Tuple, step::Tuple, nb, len, offset)` has length `len`
(base/twiceprecision.jl:342-347). -/
def HpRatioLength : Prop :=
  ∀ (t : IntTy) (a b c d : JInt t) (nb : Int) (len off : I64),
    FloatRanges.LenIs len (FloatRanges.hpRatio a b c d nb len off)

theorem hpRatioLength_proven : HpRatioLength := fun _ => FloatRanges.hpRatio_len

/-- `steprangelen_hp(Float64, ref::F_or_FF, step::F_or_FF, nb, len, offset)` has length
`len` (base/twiceprecision.jl:360-365). -/
def HpFloatLength : Prop :=
  ∀ (ref step : TP) (nb : Int) (len off : I64), FloatRanges.LenIs len (FloatRanges.hpFloat ref step nb len off)

theorem hpFloatLength_proven : HpFloatLength := FloatRanges.hpFloat_len

/-- `StepRangeLen(ref::TwicePrecision, step::TwicePrecision, len, offset)` stores its
arguments and rejects a negative length (base/twiceprecision.jl:375-377, base/range.jl:533-543). -/
def SrlTpConstructor : Prop :=
  (∀ (ref step : TP) (len off : I64) r, FloatRanges.SRL.mk' ref step len off = .ok r →
    r = ⟨ref, step, len, off⟩) ∧
  (∀ (ref step : TP) (len off : I64), len.val < 0 →
    FloatRanges.SRL.mk' ref step len off = .error (.argumentError "length cannot be negative"))

theorem srlTpConstructor_proven : SrlTpConstructor := by
  refine ⟨?_, ?_⟩
  · intro ref step len off r h
    unfold FloatRanges.SRL.mk' at h
    split at h
    · cases h
    · split at h
      · cases h; rfl
      · cases h
  · intro ref step len off h
    simp [FloatRanges.SRL.mk', h]

/-- `range_start_step_length(a::Float64, st::Float64, len)` has length `len`
(base/twiceprecision.jl:447-466). -/
def RsslLength : Prop :=
  ∀ (a s : F64) (len : I64), FloatRanges.LenIs len (FloatRanges.rangeStartStepLength a s len)

theorem rsslLength_proven : RsslLength := FloatRanges.rangeStartStepLength_len

/-- The promoting `range_start_step_length` methods with an `Int` argument have length `len`
(base/twiceprecision.jl:441-445). -/
def RsslPromoteLength : Prop :=
  (∀ (a : I64) (s : F64) (len : I64), FloatRanges.LenIs len (rsslIntFloat a s len)) ∧
  (∀ (a : F64) (s : I64) (len : I64), FloatRanges.LenIs len (rsslFloatInt a s len))

theorem rsslPromoteLength_proven : RsslPromoteLength :=
  ⟨fun _ _ _ => FloatRanges.rangeStartStepLength_len _ _ _,
    fun _ _ _ => FloatRanges.rangeStartStepLength_len _ _ _⟩

/-- `range_step_stop_length(step::Float64, stop::Float64, len)` has length `len`
(base/twiceprecision.jl:474-477). -/
def RstslLength : Prop :=
  ∀ (s b : F64) (len : I64), FloatRanges.LenIs len (FloatRanges.rangeStepStopLength s b len)

theorem rstslLength_proven : RstslLength := FloatRanges.rangeStepStopLength_len

/-- The promoting `range_step_stop_length` methods with an `Int` argument have length `len`
(base/twiceprecision.jl:468-472). -/
def RstslPromoteLength : Prop :=
  (∀ (s : I64) (b : F64) (len : I64), FloatRanges.LenIs len (rsslStepIntStop s b len)) ∧
  (∀ (s : F64) (b : I64) (len : I64), FloatRanges.LenIs len (rsslStepStopInt s b len))

theorem rstslPromoteLength_proven : RstslPromoteLength :=
  ⟨fun _ _ _ => FloatRanges.rangeStepStopLength_len _ _ _,
    fun _ _ _ => FloatRanges.rangeStepStopLength_len _ _ _⟩

/-- `range(start, stop; length=len)` for Float64 endpoints has length `len`
(base/twiceprecision.jl:647-668). -/
def RangeStartStopLengthLen : Prop :=
  ∀ (a b : F64) (len : I64), FloatRanges.LenIs len (FloatRanges.rangeStartStopLength a b len)

theorem rangeStartStopLengthLen_proven : RangeStartStopLengthLen := FloatRanges.rangeStartStopLength_len

/-- `_linspace(start::Float64, stop::Float64, len)` has length `len` and rejects non-finite
endpoints with ArgumentError (base/twiceprecision.jl:670-713). -/
def LinspaceFloatMethod : Prop :=
  (∀ (a b : F64) (len : I64), FloatRanges.LenIs len (FloatRanges.linspaceFloat a b len)) ∧
  (∀ (a b : F64) (len : I64), Float.F64.isfinite a = false →
    FloatRanges.linspaceFloat a b len = .error (.argumentError "start and stop must be finite"))

theorem linspaceFloatMethod_proven : LinspaceFloatMethod := by
  refine ⟨FloatRanges.linspaceFloat_len, ?_⟩
  intro a b len h
  simp [FloatRanges.linspaceFloat, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- `_linspace1(Float64, start, stop, len)` has length `len`, rejects a negative length and
rejects `len == 1` with different endpoints (base/twiceprecision.jl:737-750). -/
def Linspace1Method : Prop :=
  (∀ (a b : F64) (len : I64), FloatRanges.LenIs len (FloatRanges.linspace1 a b len)) ∧
  (∀ (a b : F64) (len : I64), len.val < 0 →
    FloatRanges.linspace1 a b len = .error (.argumentError "negative length")) ∧
  (∀ (a b : F64) (len : I64), len.val = 1 → Float.F64.eq a b = false →
    FloatRanges.linspace1 a b len = .error (.argumentError "endpoints differ"))

theorem linspace1Method_proven : Linspace1Method := by
  refine ⟨FloatRanges.linspace1_len, ?_, ?_⟩
  · intro a b len h; simp [FloatRanges.linspace1, h]
  · intro a b len h he; simp [FloatRanges.linspace1, h, he]

/-- `x * r` keeps the length and offset of a Float64 `StepRangeLen`
(base/twiceprecision.jl:535-536), and so does `r * x` (base/twiceprecision.jl:537). -/
def ScalarMulLength : Prop :=
  (∀ (x : F64) (r out : FloatRanges.SRL), FloatRanges.SRL.scalarMul x r = .ok out →
    out.len = r.len ∧ out.offset = r.offset) ∧
  (∀ (x : F64) (r out : FloatRanges.SRL), mulScalarRight r x = .ok out →
    out.len = r.len ∧ out.offset = r.offset)

theorem mk'_fields' (ref step : TP) (len off : I64) (out : FloatRanges.SRL)
    (h : FloatRanges.SRL.mk' ref step len off = .ok out) : out.len = len ∧ out.offset = off := by
  rw [srlTpConstructor_proven.1 _ _ _ _ _ h]; exact ⟨rfl, rfl⟩

theorem scalarMulLength_proven : ScalarMulLength :=
  ⟨fun _ _ _ h => mk'_fields' _ _ _ _ _ h, fun _ _ _ h => mk'_fields' _ _ _ _ _ h⟩

/-- `r / x` keeps the length and offset of a Float64 `StepRangeLen`
(base/twiceprecision.jl:538-539). -/
def ScalarDivLength : Prop :=
  ∀ (x : F64) (r out : FloatRanges.SRL), divScalar r x = .ok out → out.len = r.len ∧ out.offset = r.offset

theorem scalarDivLength_proven : ScalarDivLength := fun _ _ _ h => mk'_fields' _ _ _ _ _ h

/-- `_getindex_hiprec(r, i)` rejects Bool indices with ArgumentError
(base/twiceprecision.jl:488-495). -/
def HiprecBool : Prop :=
  ∀ (r : FloatRanges.SRL) (b : Bool),
    getindexHiprec r ⟨.bool, b⟩ = .error (.argumentError "invalid index of type Bool")

theorem hiprecBool_proven : HiprecBool := by
  intro r b; simp [getindexHiprec, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- `r1 + r2` of Float64 `StepRangeLen`s throws DimensionMismatch for different lengths
and otherwise has the common length (base/twiceprecision.jl:627-642). -/
def AddSrlLength : Prop :=
  (∀ r1 r2 : FloatRanges.SRL, r1.len ≠ r2.len →
    addSrl r1 r2 = .error (.dimensionMismatch "argument dimensions must match")) ∧
  (∀ r1 r2 out : FloatRanges.SRL, addSrl r1 r2 = .ok out → out.len = r1.len)

theorem addSrlLength_proven : AddSrlLength := by
  refine ⟨?_, ?_⟩
  · intro r1 r2 h
    simp [addSrl, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · intro r1 r2 out h
    unfold addSrl at h
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first
      | (simp only [reduceCtorEq] at h)
      | (cases h)
      | (rename_i hm; exact (mk'_fields' _ _ _ _ _ (Ops.lift_ok h)).1)
      | skip
    all_goals first
      | exact (mk'_fields' _ _ _ _ _ (Ops.lift_ok h)).1
      | (simp_all [lift, throw, throwThe, MonadExceptOf.throw, pure, Except.pure])

def entries : List Entry := []

end Twice

end JuliaLean.RangesCov
