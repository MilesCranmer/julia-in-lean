import JuliaLean.base.checked
import JuliaLean.Proofs.base.promotion
import JuliaLean.base.floatfuncs
import JuliaLean.Bindings.base.math
import JuliaLean.Proofs.base.floatfuncs

/-!
# `JuliaLean.Bindings.base.floatfuncs`: callee bindings for `base/floatfuncs.jl`

Bindings for the callback-parameterized methods of `base/floatfuncs.jl` (`fma`, `isapprox`, `≉`,
`maxintfloat`; Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`), and the row propositions restated
over them.

Every record below is bound to the installed model of the Julia method it stands for, for the
IEEE formats `Float16`, `Float32`, `Float64`. The FMA callees and `sqrt` are the
`JuliaLean.Bindings.base.math` declarations (`floatFmaOps`, `sqrtFloat`), whose only runtime input is
the machine record `Machine`; this file adds no second binding of them.
The named gaps (G1-G5) are listed at the end.
-/

namespace JuliaLean.Bindings.base.floatfuncs

open JuliaLean
open JuliaLean.base.float (FV FTy)
open JuliaLean.base.floatfuncs

/-! ## 1. `maxintfloat` (floatfuncs.jl:34-49) -/

/-- The `FloatKind` tag of an IEEE format: the type the dispatch of `maxintfloat(::Type{T})`
selects (floatfuncs.jl:34-36). -/
def floatKind : FTy → FloatKind
  | .f16 => .f16
  | .f32 => .f32
  | .f64 => .f64

/-- `maxintfloat` on the IEEE type `T`: the three specialized methods return their literal in
`T` (floatfuncs.jl:34-36), so each `from` field is the installed conversion `T(x)`, the identity on
`T` itself. `maxintfloatOther` is never read for an IEEE kind (`maxintfloatTypeDispatch` matches
the kind first); it holds `T`'s own threshold. -/
def floatTypeOps (T : FTy) : FloatTypeOps (FV T) where
  kind := floatKind T
  fromF16 := JuliaLean.base.float.convertFloat T
  fromF32 := JuliaLean.base.float.convertFloat T
  fromF64 := JuliaLean.base.float.convertFloat T
  maxintfloatOther := maxintfloatType T

/-- `typemax(T)` for a `BitInteger` type `T` (`base/int.jl`). -/
def integerTypeOps (t : IntTy) : IntegerTypeOps (JInt t) where
  typemax := JuliaLean.base.int.typemax t

/-- `maxintfloat(::Type{S}, ::Type{T})` for IEEE `S` and `BitInteger` `T` (floatfuncs.jl:46):
`S(typemax(T))` is the installed `floatOfInt S`, `min(::S, ::S)` is `min_float` (`base/math.jl:838`,
the runtime `jl_min_float`). -/
def maxintfloatIntegerIEEE (S : FTy) (t : IntTy) : FV S :=
  maxintfloat_AbstractFloat_Integer (floatTypeOps S) (integerTypeOps t)
    (JuliaLean.base.float.floatOfInt S) JuliaLean.C.jlMinFloat

/-! ## 2. `isapprox(x::Number, y::Number; atol, rtol, nans, norm)` (floatfuncs.jl:230-237) -/

/-- The callees of `isapprox(x::T, y::T)` for an IEEE type `T` with `norm = abs`: `==`, the
same-type `promote` (the pair itself), `isfinite`, `-`, `abs`, `max(::T, ::T) = max_float`
(`base/math.jl:839`), `*`, `<=` and `isnan`, each the installed `base/float.jl` method. -/
def numberApproxOps (T : FTy) : NumberApproxOps (FV T) (FV T) (FV T) (FV T) where
  equal := JuliaLean.base.float.eq_IEEEFloat
  promote := fun x y => (x, y)
  isfinite := JuliaLean.base.float.isfinite_IEEEFloat
  sub := JuliaLean.base.float.sub_IEEEFloat
  normDifference := JuliaLean.base.float.abs_IEEEFloat
  normValue := JuliaLean.base.float.abs_IEEEFloat
  max := JuliaLean.C.jlMaxFloat
  mul := JuliaLean.base.float.mul_IEEEFloat
  le := JuliaLean.base.float.le_IEEEFloat
  isnan := JuliaLean.base.float.isnan_IEEEFloat

/-- `rtoldefault(::Type{T}) = sqrt(eps(T))` for an IEEE type `T` (floatfuncs.jl:326): `eps(T)` is
the installed `eps_float`, `sqrt` the `JuliaLean.Bindings.base.math` binding of `sqrt(::T)` (`base/math.jl`). -/
def rtolFloatOps (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) : RtolFloatOps (FV T) where
  eps := .ok (JuliaLean.base.float.eps_float T)
  sqrt := JuliaLean.Bindings.base.math.sqrtFloat m

/-- `rtoldefault(x, y, atol)` (floatfuncs.jl:335-338) for `x, y, atol` of the IEEE type `T`:
`real(T) = T`, both defaults are `rtoldefault(T)`, `max` is `max_float`, `zero(atol)` is the
positive zero of `T`, and `atol > zero(atol)` is `<(::T, ::T)` with its arguments swapped. -/
def rtolPairOps (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) : RtolPairOps Unit (FV T) (FV T) where
  realType := id
  default := fun _ => rtoldefault_AbstractFloat (rtolFloatOps m T)
  max := fun a b => .ok (JuliaLean.C.jlMaxFloat a b)
  zeroAtol := fun _ => .ok (JuliaLean.base.float.zero_float T)
  atolGreater := fun atol zero => .ok (JuliaLean.base.float.lt_IEEEFloat zero atol)
  zeroRtol := fun _ => .ok (JuliaLean.base.float.zero_float T)

/-- The keyword arguments of `isapprox` for IEEE `T` arguments: `atol` and `rtol` of type `T`,
`none` when omitted, and `nans`. `norm` is its default `abs` (gap G3). -/
structure IsapproxKw (T : FTy) where
  atol : Option (FV T) := none
  rtol : Option (FV T) := none
  nans : Bool := false

/-- `isapprox(x::T, y::T; kw...)` for an IEEE type `T`: `atol` defaults to `zero(real(x))`, `rtol`
to `rtoldefault(x, y, atol)` evaluated after `atol` (keyword defaults are evaluated left to
right), then the installed method body. -/
def isapproxIEEE (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) (x y : FV T) (kw : IsapproxKw T) : Jl Bool := do
  let atol := kw.atol.getD (JuliaLean.base.float.zero_float T)
  let rtol ← match kw.rtol with
    | some r => pure r
    | none => rtoldefault_Values (rtolPairOps m T) () () atol
  pure (isapprox_Number (numberApproxOps T) JuliaLean.base.float.abs_IEEEFloat
    JuliaLean.base.float.abs_IEEEFloat x y atol rtol kw.nans)

/-- `isapprox(y; kwargs...)` (floatfuncs.jl:315) over the bound two-argument method. -/
def isapproxCurriedIEEE (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) (y : FV T) (kw : IsapproxKw T) :
    FV T → Jl Bool :=
  isapprox_Curried (isapproxIEEE m T) y kw

/-- `x ≉ y` (floatfuncs.jl:323) over the bound two-argument method. -/
def notApproxIEEE (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) (x y : FV T) (kw : IsapproxKw T) : Jl Bool :=
  notApproximately (fun (p : FV T × FV T) k => isapproxIEEE m T p.1 p.2 k) (x, y) kw

/-! ## 3. `fma(x::T, y::T, z::T) where T<:IEEEFloat` (floatfuncs.jl:464-466)

`Bindings.base.math.floatFmaOps m` binds `have_fma` to the runtime `jl_cpu_has_fma` of the
machine `m`, the emulated Float16/Float32 widening to `widen(T)` (Float32, Float64) and the Float64
emulation callees to the installed `base/float.jl` and `base/math.jl` methods. -/

/-! ## 4. Restated row propositions over the bound methods -/

open JuliaLean.Proofs.base.floatfuncs (MaxintfloatIEEEFormats FmaCorrect)

/-- `floatfuncs-maxintfloat-methods`, restated over the IEEE dispatch and `BitInteger` caps. -/
def MaxintfloatMethodsBound : Prop :=
  MaxintfloatIEEEFormats ∧
  (∀ (T : FTy) (x : FV T), maxintfloat_AbstractFloat (floatTypeOps T) x = maxintfloatType T) ∧
  (∀ (S : FTy) (t : IntTy),
    maxintfloatIntegerIEEE S t =
      JuliaLean.C.jlMinFloat (maxintfloatType S)
        (JuliaLean.base.float.floatOfInt S (JuliaLean.base.int.typemax t))) ∧
  maxintfloat_Default.toRat = ((2^53 : Int), 1) ∧
  (∀ {A : Type} (slurp : List A),
    maxintfloat_UnionBottom slurp = .error (.methodError "maxintfloat")) ∧
  (∀ {X A : Type} (x : X) (slurp : List A),
    maxintfloat_ValueUnionBottom x slurp = .error (.methodError "maxintfloat"))

/-- The relative tolerance `isapprox` uses: the given `rtol`, else `0` when `atol > 0` and
`sqrt(eps(T))` otherwise. -/
def effectiveRtol (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) (kw : IsapproxKw T) : Jl (FV T) :=
  match kw.rtol with
  | some r => .ok r
  | none =>
      if JuliaLean.base.float.lt_IEEEFloat (JuliaLean.base.float.zero_float T)
          (kw.atol.getD (JuliaLean.base.float.zero_float T))
      then .ok (JuliaLean.base.float.zero_float T)
      else JuliaLean.Bindings.base.math.sqrtFloat m (JuliaLean.base.float.eps_float T)

/-- `floatfuncs-isapprox-tolerances`, restated as the full formula of the public method: equal
values, or finite values with `abs(x-y) <= max(atol, rtol*max(abs(x), abs(y)))`, or (with
`nans=true`) two NaNs; with the documented defaults `atol = 0` and `effectiveRtol`. -/
def IsapproxFormulaBound : Prop :=
  ∀ (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) (x y : FV T) (kw : IsapproxKw T),
    let abs := @JuliaLean.base.float.abs_IEEEFloat T
    let atol := kw.atol.getD (JuliaLean.base.float.zero_float T)
    isapproxIEEE m T x y kw =
      (effectiveRtol m T kw).map (fun rtol =>
        JuliaLean.base.float.eq_IEEEFloat x y ||
        (JuliaLean.base.float.isfinite_IEEEFloat x && JuliaLean.base.float.isfinite_IEEEFloat y &&
          JuliaLean.base.float.le_IEEEFloat (abs (JuliaLean.base.float.sub_IEEEFloat x y))
            (JuliaLean.C.jlMaxFloat atol
              (JuliaLean.base.float.mul_IEEEFloat rtol (JuliaLean.C.jlMaxFloat (abs x) (abs y))))) ||
        (kw.nans && JuliaLean.base.float.isnan_IEEEFloat x && JuliaLean.base.float.isnan_IEEEFloat y))

/-- `floatfuncs-isapprox-nonfinite`, restated over the public method: unequal values one of which
is not finite are not approximately equal when `nans=false`, for every `atol` and `rtol`. -/
def IsapproxNonfiniteBound : Prop :=
  ∀ (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) (x y : FV T) (kw : IsapproxKw T),
    kw.nans = false → JuliaLean.base.float.eq_IEEEFloat x y = false →
    (JuliaLean.base.float.isfinite_IEEEFloat x && JuliaLean.base.float.isfinite_IEEEFloat y) = false →
    isapproxIEEE m T x y kw = .ok false

/-- The round2 forwarder row, restated over the public method: `isapprox(y; kw...)` compares its
argument to `y`, and `≉` negates `isapprox`. -/
def IsapproxForwardersBound : Prop :=
  ∀ (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) (x y : FV T) (kw : IsapproxKw T),
    isapproxCurriedIEEE m T y kw x = isapproxIEEE m T x y kw ∧
    notApproxIEEE m T x y kw = (isapproxIEEE m T x y kw).map (!·)

/-- `floatfuncs-fma-exact`, restated over the runtime FMA dispatch of every machine. -/
def FmaCorrectBound : Prop :=
  ∀ m : JuliaLean.Bindings.base.math.Machine, FmaCorrect (JuliaLean.Bindings.base.math.floatFmaOps m)

/-! ## 5. Named gaps

* G1: `isapprox` on arguments of two different `Number` types, or on non-IEEE types (`BigFloat`,
  `Rational`, `Complex`, user types): `promote`, `==`, `-` and `abs` across types are not bound here.
  `isapprox(::Integer, ::Integer)` is its own method (`isapprox_Integer`), outside these rows.
* G2: `atol`/`rtol` of a type other than `T` (e.g. `atol=1`): the promotion inside `max` and `*`.
* G3: a user `norm` function (`norm=abs` only).
* G4: `maxintfloat(::Type{S})` and `maxintfloat(x::S)` for a non-IEEE `S <: AbstractFloat`, i.e.
  `BigFloat` and every program-defined `AbstractFloat` type (floatfuncs.jl:37 and the `S` of :46).
  `BigFloat` has its own methods `BigFloat(2)^precision(x)` (`base/mpfr.jl:1078-1079`, installed
  `mpfr.maxintfloatValue`/`maxintfloatType`, in the MPFR context monad); a program's type supplies its
  own `maxintfloat(::Type{S})` method or none (a `MethodError`). The pure
  `FloatTypeOps.maxintfloatOther` field holds neither and is not bound for non-IEEE kinds.
* G5: `maxintfloat(S, T)` for an `Integer` type `T` that is not a fixed-width `BitInteger`: `Bool`,
  `BigInt` (no `typemax`, a `MethodError`) and every program-defined `Integer` type, whose own
  `typemax` method (or its absence) decides the result (floatfuncs.jl:46). `IntTy` has none of them.
-/

/-! ## 6. Evaluated checks

Closed cases checked against Julia results, evaluated on the bound methods: `decide +kernel`. Where an arbitrary
machine `m` appears, `simp only` first unfolds the bound callees (`sqrt`, `ldexp` and the `fma`
record) to their machine-free bodies, which shows the result does not read `m` beyond the explicit
FMA widths, then the kernel evaluates the closed term. -/

section Checks

open JuliaLean.Promotion (Fl)

private def f64 (n : Nat) : FV .f64 := Fl.ofBits n
private def f32 (n : Nat) : FV .f32 := Fl.ofBits n
private def f16 (n : Nat) : FV .f16 := Fl.ofBits n

/-- The machine-free body of `Bindings.base.math.sqrtFloat` (`sqrtIEEE` reads only the `sqrtLlvm` field). -/
private def sqrtClosed (T : FTy) (x : FV T) : Jl (FV T) :=
  if JuliaLean.base.math.flt x (JuliaLean.base.math.fzero T) then
    JuliaLean.base.math.throwComplexDomainError "sqrt" x
  else .ok (JuliaLean.C.jlSqrtLlvm x)

private theorem sqrtFloat_closed (m : JuliaLean.Bindings.base.math.Machine) (T : FTy) :
    @JuliaLean.Bindings.base.math.sqrtFloat m T = sqrtClosed T := by
  funext x; rfl

/-- `Bindings.base.math.ieeeOpsWith m .f64 …` as `ldexp64` builds it, with the two machine fields `ldexp` never
reads (`pi`, `haveFma`) replaced by constants. -/
private def ieeeF64Closed : JuliaLean.base.math.IEEEOps .f64 where
  sqrtLlvm := JuliaLean.C.jlSqrtLlvm
  eps := JuliaLean.base.float.eps_float .f64
  floatmin := JuliaLean.base.float.floatmin_float .f64
  floatmax := JuliaLean.base.float.floatmax_float .f64
  invFloatmin := JuliaLean.base.float.div_float (JuliaLean.base.float.one_float .f64)
    (JuliaLean.base.float.floatmin_float .f64)
  pi := JuliaLean.base.float.zero_float .f64
  fma := JuliaLean.C.jlFmaFloat
  twoMul := fun x y => (JuliaLean.base.float.mul_float x y,
    JuliaLean.C.jlFmaFloat x y (JuliaLean.base.float.neg_float (JuliaLean.base.float.mul_float x y)))
  trunc := JuliaLean.C.jlTruncLlvm
  rem := JuliaLean.base.float.rem_IEEEFloat
  flipsign := JuliaLean.Bindings.base.math.flipsignIEEE .f64
  minFloat := JuliaLean.C.jlMinFloat
  maxFloat := JuliaLean.C.jlMaxFloat
  clampUnsigned := JuliaLean.Bindings.base.math.clampUnsigned
  addFast := JuliaLean.base.float.add_float
  oneunit := fun _ => JuliaLean.base.float.one_float .f64
  inverse := fun x => JuliaLean.base.float.div_float (JuliaLean.base.float.one_float .f64) x
  greater := fun x y => JuliaLean.base.float.lt_float y x
  muladd := JuliaLean.base.float.muladd_IEEEFloat
  abs2 := fun x => JuliaLean.base.float.mul_float x x
  haveFma := false

private theorem ldexp64_closed (m : JuliaLean.Bindings.base.math.Machine) :
    JuliaLean.Bindings.base.math.ldexp64 m = fun x e => JuliaLean.base.math.ldexp ieeeF64Closed x e := by
  funext x e; rfl

private theorem haveFma_widths (m : JuliaLean.Bindings.base.math.Machine) (w : List Nat) :
    JuliaLean.Bindings.base.math.haveFma { m with fmaWidths := w } =
      fun T => JuliaLean.C.jlHaveFma T.fmt w := rfl

-- maxintfloat(Float16, Int8) == Float16(127); (Float32, UInt16) == 65535f0;
-- (Float16, UInt128) == Float16(2048); (Float64, Int64) == 2^53; maxintfloat(1f0) == 16777216f0
example : (maxintfloatIntegerIEEE .f16 .i8).toBits = 0x57f0 := by decide +kernel
example : (maxintfloatIntegerIEEE .f32 .u16).toBits = 0x477fff00 := by decide +kernel
example : (maxintfloatIntegerIEEE .f16 .u128).toBits = 0x6800 := by decide +kernel
example : (maxintfloatIntegerIEEE .f64 .i64).toBits = 0x4340000000000000 := by decide +kernel
example : (maxintfloat_AbstractFloat (floatTypeOps .f32) (f32 0x3f800000)).toBits = 0x4b800000 := by
  decide +kernel

-- isapprox(1.0, 1.0); default rtol: 1.0 ≈ 1.0 + 1e-9, not 1.0 + 1e-7
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (f64 0x3ff0000000000000) (f64 0x3ff0000000000000) {} = .ok true := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (f64 0x3ff0000000000000) (f64 0x3ff000000044b830) {} = .ok true := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (f64 0x3ff0000000000000) (f64 0x3ff000001ad7f29b) {} = .ok false := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
-- Float16(1) ≈ Float16(1.01) (stored as 1.0098), not Float16(1.1)
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f16 (f16 0x3c00) (f16 0x3c0a) {} = .ok true := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
-- isapprox(0.1, 0.15; atol=0.05); an atol > 0 zeroes the default rtol
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (f64 0x3fb999999999999a) (f64 0x3fc3333333333333)
      { atol := some (f64 0x3fa999999999999a) } = .ok true := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (f64 0x3ff0000000000000) (f64 0x3ff000000044b830)
      { atol := some (f64 0x3d719799812dea11) } = .ok false := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
-- rtol = 0.34 accepts 0.1 ≈ 0.15, rtol = 0.33 does not
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (f64 0x3fb999999999999a) (f64 0x3fc3333333333333)
      { rtol := some (f64 0x3fd5c28f5c28f5c3) } = .ok true := by
  simp only [isapproxIEEE]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (f64 0x3fb999999999999a) (f64 0x3fc3333333333333)
      { rtol := some (f64 0x3fd51eb851eb851f) } = .ok false := by
  simp only [isapproxIEEE]
  decide +kernel
-- Inf ≈ Inf, Inf ≉ -Inf, NaN ≉ NaN unless nans=true, -0.0 ≈ 0.0
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (Fl.inf false) (Fl.inf false) {} = .ok true := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (Fl.inf false) (Fl.inf true) {} = .ok false := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 Fl.nan Fl.nan {} = .ok false := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 Fl.nan Fl.nan { nans := true } = .ok true := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxIEEE m .f64 (f64 0x8000000000000000) (f64 0) {} = .ok true := by
  simp only [isapproxIEEE, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
-- isapprox(1.0)(1.0 + 1e-9); ≉(0.1, 0.15; atol=0.05) is false
example (m : JuliaLean.Bindings.base.math.Machine) :
    isapproxCurriedIEEE m .f64 (f64 0x3ff0000000000000) {} (f64 0x3ff000000044b830) = .ok true := by
  simp only [isapproxIEEE, isapproxCurriedIEEE, isapprox_Curried, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    notApproxIEEE m .f64 (f64 0x3fb999999999999a) (f64 0x3fc3333333333333)
      { atol := some (f64 0x3fa999999999999a) } = .ok false := by
  simp only [isapproxIEEE, notApproxIEEE, notApproximately, rtolPairOps, rtolFloatOps,
    sqrtFloat_closed]
  decide +kernel

-- fma(0.1, 10.0, -1.0) == 2^-54, on a machine with and without hardware FMA;
-- fma(Float16(0.1), Float16(10), Float16(-1)) == -2^-12 through the emulated Float16 path
example (m : JuliaLean.Bindings.base.math.Machine) :
    (JuliaLean.Bindings.base.math.fmaIEEE { m with fmaWidths := [] }
      (f64 0x3fb999999999999a) (f64 0x4024000000000000) (f64 0xbff0000000000000)).toBits =
      0x3c90000000000000 := by
  simp only [JuliaLean.Bindings.base.math.fmaIEEE, JuliaLean.Bindings.base.math.floatFmaOps, JuliaLean.Bindings.base.math.fma64Ops, haveFma_widths,
    ldexp64_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    (JuliaLean.Bindings.base.math.fmaIEEE { m with fmaWidths := [16, 32, 64] }
      (f64 0x3fb999999999999a) (f64 0x4024000000000000) (f64 0xbff0000000000000)).toBits =
      0x3c90000000000000 := by
  simp only [JuliaLean.Bindings.base.math.fmaIEEE, JuliaLean.Bindings.base.math.floatFmaOps, JuliaLean.Bindings.base.math.fma64Ops, haveFma_widths,
    ldexp64_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    (JuliaLean.Bindings.base.math.fmaIEEE { m with fmaWidths := [] }
      (f16 0x2e66) (f16 0x4900) (f16 0xbc00)).toBits = 0x8c00 := by
  simp only [JuliaLean.Bindings.base.math.fmaIEEE, JuliaLean.Bindings.base.math.floatFmaOps, JuliaLean.Bindings.base.math.fma64Ops, haveFma_widths,
    ldexp64_closed]
  decide +kernel
example (m : JuliaLean.Bindings.base.math.Machine) :
    (JuliaLean.Bindings.base.math.fmaIEEE { m with fmaWidths := [] }
      (f32 0x3dcccccd) (f32 0x41200000) (f32 0xbf800000)).toBits = 0x32800000 := by
  simp only [JuliaLean.Bindings.base.math.fmaIEEE, JuliaLean.Bindings.base.math.floatFmaOps, JuliaLean.Bindings.base.math.fma64Ops, haveFma_widths,
    ldexp64_closed]
  decide +kernel

end Checks

end JuliaLean.Bindings.base.floatfuncs

namespace JuliaLean.Bindings.base.floatfuncs.Int64Approx

open JuliaLean

abbrev S64 := JInt .i64
abbrev U64 := JInt .u64
abbrev Word := S64 ⊕ U64

/-- Observe the existing primitive promotion type computation. Its existing
table theorem establishes termination for these built-in type tags; it is
used only to construct the Option projection, not as an arithmetic hypothesis.
Julia source: base/promotion.jl:397-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _promote(x::T, y::S) where {T,S}
    @inline
    R = promote_type(T, S)
    return (convert(R, x), convert(R, y))
end
```
-/
def promotedType (s t : IntTy) : JuliaLean.base.promotion.PType :=
  (JuliaLean.base.promotion.primitivePromoteType
    (JuliaLean.base.promotion.primitivePType (.int s))
    (JuliaLean.base.promotion.primitivePType (.int t))).get
      (by rw [JuliaLean.Proofs.base.promotion.promoteTypeTable_proven]; rfl)

/-- Actual heterogeneous promote: determine UInt64, convert left then right,
and call the existing different-tuple-types check. The selected promoted type
is independently verified in validation; converters use that fixed type.
Julia source: base/promotion.jl:397-401,423-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _promote(x::T, y::S) where {T,S}
    @inline
    R = promote_type(T, S)
    return (convert(R, x), convert(R, y))
end
function promote(x, y)
    @inline
    px, py = _promote(x, y)
    not_sametype((x,y), (px,py))
    px, py
end
```
-/
def promoteSignedUnsigned (x : S64) (y : U64) : Jl (U64 × U64) :=
  JuliaLean.base.promotion.promoteTwoValues
    (JuliaLean.base.promotion.promotePairValues
      (fun (_ : S64) (_ : U64) => pure (promotedType .i64 .u64))
      (fun _ value => JuliaLean.base.int.convert .u64 value)
      (fun _ value => JuliaLean.base.int.convert .u64 value))
    JuliaLean.base.promotion.notSameTypeDifferent x y

/-- The reverse heterogeneous argument order retains the source conversion
order, using the same actual promotion methods and existing converters.
Julia source: base/promotion.jl:397-401,423-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _promote(x::T, y::S) where {T,S}
    @inline
    R = promote_type(T, S)
    return (convert(R, x), convert(R, y))
end
function promote(x, y)
    @inline
    px, py = _promote(x, y)
    not_sametype((x,y), (px,py))
    px, py
end
```
-/
def promoteUnsignedSigned (x : U64) (y : S64) : Jl (U64 × U64) :=
  JuliaLean.base.promotion.promoteTwoValues
    (JuliaLean.base.promotion.promotePairValues
      (fun (_ : U64) (_ : S64) => pure (promotedType .u64 .i64))
      (fun _ value => JuliaLean.base.int.convert .u64 value)
      (fun _ value => JuliaLean.base.int.convert .u64 value))
    JuliaLean.base.promotion.notSameTypeDifferent x y

/-- Same-type promotion observes the actual source tuple represented as a
two-element list, with statically valid projections.
Julia source: base/promotion.jl:441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote(x::T, y::T, zs::T...) where {T} = (x, y, zs...)
```
-/
def promoteSamePair {A : Type} (x y : A) : A × A :=
  let values := JuliaLean.base.promotion.promoteSameType x y []
  (values[0]'(by simp [values, JuliaLean.base.promotion.promoteSameType]),
   values[1]'(by simp [values, JuliaLean.base.promotion.promoteSameType]))

/-- Dispatch the actual promote methods over the two represented types.
Julia source: base/promotion.jl:423-428,441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote(x, y)
    @inline
    px, py = _promote(x, y)
    not_sametype((x,y), (px,py))
    px, py
end
promote(x::T, y::T, zs::T...) where {T} = (x, y, zs...)
```
-/
def promoteWords : Word → Word → Jl (Word × Word)
  | .inl x, .inl y => let pair := promoteSamePair x y; pure (.inl pair.1, .inl pair.2)
  | .inr x, .inr y => let pair := promoteSamePair x y; pure (.inr pair.1, .inr pair.2)
  | .inl x, .inr y => do
      let pair ← promoteSignedUnsigned x y
      pure (.inr pair.1, .inr pair.2)
  | .inr x, .inl y => do
      let pair ← promoteUnsignedSigned x y
      pure (.inr pair.1, .inr pair.2)

/-- Concrete checked-multiplication dispatch. Successful source promotion
always supplies equal tags; mixed tags are not a method of pinned Base.
Julia source: base/checked.jl:239-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_with_overflow(x::T, y::T) where {T<:SignedInt}   = checked_smul_int(x, y)
mul_with_overflow(x::T, y::T) where {T<:UnsignedInt} = checked_umul_int(x, y)
```
-/
def mulWithOverflowWords : Word → Word → Jl (Word × Bool)
  | .inl x, .inl y =>
      let result := JuliaLean.base.checked.mulWithOverflowSigned rfl x y
      pure (.inl result.1, result.2)
  | .inr x, .inr y =>
      let result := JuliaLean.base.checked.mulWithOverflowUnsigned rfl x y
      pure (.inr result.1, result.2)
  | .inl _, .inr _ | .inr _, .inl _ => .error (.methodError "mul_with_overflow")

/-- Existing signed/unsigned maximum dispatch, including the source's `% R`
conversion rather than checked promotion of a negative absolute tolerance.
Julia source: base/int.jl:591-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function max(x::S, y::T) where {S <: BitInteger, T <: BitInteger}
    R = promote_type(S, T)
    ifelse(x < y, y % R, x % R)
end
```
-/
def maxWords : Word → Word → Word
  | .inl x, .inl y => .inl (JuliaLean.base.int.jmax x y)
  | .inl x, .inr y => .inr (JuliaLean.base.int.jmax x y)
  | .inr x, .inl y => .inr (JuliaLean.base.int.jmax x y)
  | .inr x, .inr y => .inr (JuliaLean.base.int.jmax x y)

/-- The existing integer operator dispatcher retains unchecked rem conversions
for multiplication. This is distinct from `_scaled_rtol`'s checked promotion.
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def mulWords : Word → Word → Word
  | .inl x, .inl y => .inl (JuliaLean.base.int.binop JuliaLean.base.int.mulSame x y)
  | .inl x, .inr y => .inr (JuliaLean.base.int.binop JuliaLean.base.int.mulSame x y)
  | .inr x, .inl y => .inr (JuliaLean.base.int.binop JuliaLean.base.int.mulSame x y)
  | .inr x, .inr y => .inr (JuliaLean.base.int.binop JuliaLean.base.int.mulSame x y)

/-- Existing abs dispatch on the represented signed or unsigned result.
Julia source: base/int.jl:233-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(x::Unsigned) = x
abs(x::Signed) = flipsign(x,x)
```
-/
def absWord : Word → Word
  | .inl x => .inl (JuliaLean.base.int.abs x)
  | .inr x => .inr (JuliaLean.base.int.abs x)

/-- Existing mixed signed/unsigned comparison, without converting a negative
bound to UInt64. The int dispatcher selects the actual same/mixed methods.
Julia source: base/int.jl:579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::BitSigned, y::BitUnsigned) = !(y < x)
```
-/
def leWords : Word → Word → Bool
  | .inl x, .inl y => JuliaLean.base.int.le x y
  | .inl x, .inr y => JuliaLean.base.int.le x y
  | .inr x, .inl y => JuliaLean.base.int.le x y
  | .inr x, .inr y => JuliaLean.base.int.le x y

/-- Bind the generic difference record's individual operations to the existing
integer methods. The actual Int64 distance call selects the signed method below.
Julia source: base/floatfuncs.jl:244,275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_uabsdiff(x::Integer, y::Integer) = x < y ? y - x : x - y
_uabsdiff_le(x::Integer, y::Integer, b::Real) = _uabsdiff(x, y) <= b
```
-/
def differenceOps : JuliaLean.base.floatfuncs.IntegerDifferenceOps S64 S64 Word Word where
  less := JuliaLean.base.int.lt
  subXY := fun x y => .inl (JuliaLean.base.int.sub x y)
  subYX := fun y x => .inl (JuliaLean.base.int.sub y x)
  leBound := leWords

/-- Actual signed-distance method, including opposite signs and typemin.
Julia source: base/floatfuncs.jl:253-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uabsdiff(x::BitSigned, y::BitSigned)
    lo, hi = minmax(x, y)
    # Unsigned subtraction gives the exact distance even across zero.
    return unsigned(hi) - unsigned(lo)
end
```
-/
def distance (x y : S64) : Word :=
  .inr (JuliaLean.base.floatfuncs.uabsdiff_BitSigned
    { minmax := JuliaLean.base.int.minmax_BitInteger
      unsigned := JuliaLean.base.int.unsigned
      sub := JuliaLean.base.int.sub } x y)

/-- Preserve the signed tolerance until the actual source promote call.
`bitRtol`/`bitScale` are representation injections, not numeric conversions.
Julia source: base/floatfuncs.jl:286-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_scaled_rtol(rtol::Real, scale::Integer) = (rtol * scale, false)
_scaled_rtol(rtol::BitInteger, scale::BitInteger) = mul_with_overflow(promote(rtol, scale)...)
```
-/
def scaledRtolOps : JuliaLean.base.floatfuncs.ScaledRtolOps S64 Word Word where
  bitInteger := true
  mulReal := fun rtol scale => pure (mulWords (.inl rtol) scale)
  bitRtol := fun rtol => pure (.inl rtol)
  bitScale := fun scale => pure scale
  promote := promoteWords
  mulWithOverflow := mulWithOverflowWords

/-- Complete concrete Int64 operations for the installed public integer body
with norm=abs. No field contains an assumed arithmetic or callee-correctness law.
Julia source: base/floatfuncs.jl:289-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isapprox(x::Integer, y::Integer;
                  atol::Real=0, rtol::Real=rtoldefault(x,y,atol),
                  nans::Bool=false, norm::Function=abs)
    if norm === abs
        atol < 1 && rtol == 0 && return x == y
        # Check equality before forming the bound, since Inf * 0 is NaN.
        x == y && return true
        # uabs handles typemin and avoids signed/unsigned promotion.
        b, overflowed = _scaled_rtol(rtol, max(uabs(x), uabs(y)))
        # Overflow implies rtol >= 2, hence rtol * max(|x|, |y|) >= |x - y|.
        return overflowed || _uabsdiff_le(x, y, max(atol, b))
    end
    return x == y ||
        norm(_uabsdiff(x, y)) <= max(atol, rtol*max(norm(uabs(x)), norm(uabs(y))))
end
```
-/
def integerOps : JuliaLean.base.floatfuncs.IntegerApproxOps S64 S64 Word Word S64 Word where
  equal := JuliaLean.base.int.eq
  normIsAbs := true
  atolLessOne := fun atol => JuliaLean.base.int.lt atol (JuliaLean.base.int.lit .i64 1)
  rtolIsZero := fun rtol => JuliaLean.base.int.eq rtol (JuliaLean.base.int.lit .i64 0)
  uabsX := fun x => .inr (JuliaLean.base.float.uabs_BitSigned x)
  uabsY := fun y => .inr (JuliaLean.base.float.uabs_BitSigned y)
  maxMagnitude := maxWords
  scaledRtol := scaledRtolOps
  difference := differenceOps
  uabsdiff := distance
  uabsdiffLe := fun x y bound => pure
    (JuliaLean.base.floatfuncs.uabsdiffLe_Integer differenceOps distance x y bound)
  normDifference := absWord
  normUabsX := fun x => absWord (.inr (JuliaLean.base.float.uabs_BitSigned x))
  normUabsY := fun y => absWord (.inr (JuliaLean.base.float.uabs_BitSigned y))
  maxValues := maxWords
  maxBound := fun atol bound => maxWords (.inl atol) bound
  mulBound := fun rtol bound => mulWords (.inl rtol) bound
  le := leWords

/-- Public integer source call after selecting Int64 arguments/tolerances and
the default abs function. The integer source body never reads its nans keyword.
Julia source: base/floatfuncs.jl:289-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isapprox(x::Integer, y::Integer;
                  atol::Real=0, rtol::Real=rtoldefault(x,y,atol),
                  nans::Bool=false, norm::Function=abs)
    if norm === abs
        atol < 1 && rtol == 0 && return x == y
        # Check equality before forming the bound, since Inf * 0 is NaN.
        x == y && return true
        # uabs handles typemin and avoids signed/unsigned promotion.
        b, overflowed = _scaled_rtol(rtol, max(uabs(x), uabs(y)))
        # Overflow implies rtol >= 2, hence rtol * max(|x|, |y|) >= |x - y|.
        return overflowed || _uabsdiff_le(x, y, max(atol, b))
    end
    return x == y ||
        norm(_uabsdiff(x, y)) <= max(atol, rtol*max(norm(uabs(x)), norm(uabs(y))))
end
```
-/
def isapproxInt64 (x y atol rtol : S64) (_nans : Bool := false) : Jl Bool :=
  JuliaLean.base.floatfuncs.isapprox_Integer integerOps x y atol rtol

end JuliaLean.Bindings.base.floatfuncs.Int64Approx
