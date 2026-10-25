import JuliaLean.Float.Extras

/-!
`Complex{Float64}` from `base/complex.jl` at Julia `bbfa0ce4150`, on the exact
binary64 model `JuliaLean.Float.F64`. `muladd` is the fused interpretation of
`F64.muladd`; `have_fma(Float64)` is true on the x86-64 machines the checks ran on.
-/

namespace JuliaLean.Complex

open JuliaLean JuliaLean.Float

namespace Fl

/-- `0.0`. -/
def pzero : F64 := F64.zero false
/-- `-0.0`. -/
def nzero : F64 := F64.zero true
/-- `2.0`. -/
def two : F64 := F64.ofInt 2
/-- `0.5`. -/
def half : F64 := F64.ofBits 0x3fe0000000000000
/-- `Inf`. -/
def inf : F64 := F64.inf false

/-- `copysign(x::Float64, y::Float64)`; `base/floatfuncs.jl:5`. -/
def copysign (x y : F64) : F64 :=
  F64.ofBits (F64.toBits (F64.abs x) + if F64.signbit y then 2^63 else 0)

/-- `flipsign(x::Float64, y::Float64)`; `base/floatfuncs.jl:10`. -/
def flipsign (x y : F64) : F64 := if F64.signbit y then F64.neg x else x

/-- `sign(x::Real)`; `base/number.jl:212`. -/
def sign (x : F64) : F64 :=
  if F64.lt x pzero then F64.neg F64.one
  else if F64.lt pzero x then F64.one else x

/-- `max(x::Float64, y::Float64) = max_float(x, y)`; `base/math.jl:839`. -/
def max (x y : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isnan y then y
  else if F64.lt x y then y
  else if F64.lt y x then x
  else if F64.signbit x then y else x

/-- `x * y` for `x::Bool`, `y::Float64`; `base/bool.jl:161-164`. -/
def mulBool (b : Bool) (y : F64) : F64 := if b then y else copysign pzero y

/-- `eps(Float64)`; `base/float.jl:981`. -/
def eps : F64 := F64.eps

end Fl

/-- `Complex{Float64}`; `base/complex.jl:13-16,38`. -/
structure CF64 where
  re : F64
  im : F64
  deriving DecidableEq, Repr, Inhabited

namespace CF64

/-- `isfinite(z::Complex)`; `base/complex.jl:151`. -/
def isfinite (z : CF64) : Bool := F64.isfinite z.re && F64.isfinite z.im
/-- `isnan(z::Complex)`; `base/complex.jl:152`. -/
def isnan (z : CF64) : Bool := F64.isnan z.re || F64.isnan z.im
/-- `isinf(z::Complex)`; `base/complex.jl:153`. -/
def isinf (z : CF64) : Bool := F64.isinf z.re || F64.isinf z.im
/-- `iszero(z::Complex)`; `base/complex.jl:154`. -/
def iszero (z : CF64) : Bool := F64.iszero z.re && F64.iszero z.im
/-- `isreal(z::Complex)`; `base/complex.jl:149`. -/
def isreal (z : CF64) : Bool := F64.iszero z.im
/-- `isone(z::Complex)`, with `isone(x) = x == one(x)`; `base/complex.jl:155`. -/
def isone (z : CF64) : Bool := F64.eq z.re F64.one && F64.iszero z.im

/-- `one(Complex{Float64})`. -/
def one : CF64 := ⟨F64.one, Fl.pzero⟩

/-- `conj(z::Complex)`; `base/complex.jl:280`. -/
def conj (z : CF64) : CF64 := ⟨z.re, F64.neg z.im⟩
/-- `-(z::Complex)`; `base/complex.jl:291`. -/
def neg (z : CF64) : CF64 := ⟨F64.neg z.re, F64.neg z.im⟩
/-- `+(z::Complex, w::Complex)`; `base/complex.jl:292`. -/
def add (z w : CF64) : CF64 := ⟨F64.add z.re w.re, F64.add z.im w.im⟩
/-- `-(z::Complex, w::Complex)`; `base/complex.jl:293`. -/
def sub (z w : CF64) : CF64 := ⟨F64.sub z.re w.re, F64.sub z.im w.im⟩
/-- `*(z::Complex, w::Complex)`; `base/complex.jl:294-295`. -/
def mul (z w : CF64) : CF64 :=
  ⟨F64.sub (F64.mul z.re w.re) (F64.mul z.im w.im),
   F64.add (F64.mul z.re w.im) (F64.mul z.im w.re)⟩
/-- `abs2(z::Complex)`; `base/complex.jl:282`. -/
def abs2 (z : CF64) : F64 := F64.add (F64.mul z.re z.re) (F64.mul z.im z.im)

/-- `_mulsub(a, b, c) = muladd(a, b, -c)`; `base/complex.jl:303-304`. -/
def mulsub (a b c : F64) : F64 := F64.muladd a b (F64.neg c)

/-- `muladd(z::Complex, w::Complex, x::Complex)`; `base/complex.jl:305-307`. -/
def muladd (z w x : CF64) : CF64 :=
  ⟨F64.muladd z.re w.re (F64.neg (mulsub z.im w.im x.re)),
   F64.muladd z.re w.im (F64.muladd z.im w.re x.im)⟩

/-- `*(x::Bool, z::Complex)`; `base/complex.jl:322`. -/
def boolMul (b : Bool) (z : CF64) : CF64 := ⟨Fl.mulBool b z.re, Fl.mulBool b z.im⟩

/-- `/(z::Complex, x::Real)`; `base/complex.jl:358`. -/
def divReal (z : CF64) (x : F64) : CF64 := ⟨F64.div z.re x, F64.div z.im x⟩

/-- `==(z::Complex, w::Complex)`; `base/complex.jl:246`. -/
def eq (z w : CF64) : Bool := F64.eq z.re w.re && F64.eq z.im w.im
/-- `==(z::Complex, x::Real)`; `base/complex.jl:247`. -/
def eqReal (z : CF64) (x : F64) : Bool := isreal z && F64.eq z.re x
/-- `isequal(z::Complex, w::Complex)`; `base/complex.jl:250`. -/
def isequal (z w : CF64) : Bool := F64.isequal z.re w.re && F64.isequal z.im w.im
/-- `isequal(z::Complex, w::Real)` with `zero(w) = 0.0`; `base/complex.jl:251`. -/
def isequalReal (z : CF64) (x : F64) : Bool :=
  F64.isequal z.re x && F64.isequal z.im Fl.pzero

/--
`hash(z::Complex, h)`; `base/complex.jl:256-263`. `H` is `hash` on the real
parts; `hash_0_imag = hash(0, h_imag)` equals `hash(0.0, h_imag)` because
`isequal(0, 0.0)`.
-/
def hash (H : F64 → UInt64 → UInt64) (hImag : UInt64) (z : CF64) (h : UInt64) : UInt64 :=
  H z.re (h ^^^ H z.im hImag ^^^ H Fl.pzero hImag)

/-! ### Division, `base/complex.jl:400-474` -/

/-- `robust_cdiv2`; `base/complex.jl:467-474`. -/
def robustCdiv2 (a b c d r t : F64) : F64 :=
  if !F64.eq r Fl.pzero then
    let br := F64.mul b r
    if !F64.eq br Fl.pzero then F64.mul (F64.add a br) t
    else F64.add (F64.mul a t) (F64.mul (F64.mul b t) r)
  else F64.mul (F64.add a (F64.mul d (F64.div b c))) t

/-- `robust_cdiv1`; `base/complex.jl:460-466`. -/
def robustCdiv1 (a b c d : F64) : F64 × F64 :=
  let r := F64.div d c
  let t := F64.div F64.one (F64.add c (F64.mul d r))
  (robustCdiv2 a b c d r t, robustCdiv2 b (F64.neg a) c d r t)

/-- `cdiv`; `base/complex.jl:424-432`. -/
def cdiv (a b c d : F64) : F64 × F64 :=
  if F64.le (F64.abs d) (F64.abs c) then robustCdiv1 a b c d
  else
    let (p, q) := robustCdiv1 b a d c
    (p, F64.neg q)

/-- `0.5*floatmax(Float64)`; `base/complex.jl:410,441`. -/
def halfov : F64 := F64.mul Fl.half F64.floatmax
/-- `floatmin(Float64)*2.0/eps(Float64)`; `base/complex.jl:411,442`. -/
def twounEps : F64 := F64.div (F64.mul F64.floatmin Fl.two) Fl.eps

/-- `scaleargs_cdiv`; `base/complex.jl:439-459`. -/
def scaleargsCdiv (a b c d ab cd : F64) : F64 × F64 × F64 × F64 × F64 :=
  let bs := F64.div Fl.two (F64.mul Fl.eps Fl.eps)
  let (a, b, s) :=
    if F64.le halfov ab then (F64.mul a Fl.half, F64.mul b Fl.half, F64.mul F64.one Fl.two)
    else if F64.le ab twounEps then (F64.mul a bs, F64.mul b bs, F64.div F64.one bs)
    else (a, b, F64.one)
  let (c, d, s) :=
    if F64.le halfov cd then (F64.mul c Fl.half, F64.mul d Fl.half, F64.mul s Fl.half)
    else if F64.le cd twounEps then (F64.mul c bs, F64.mul d bs, F64.mul s bs)
    else (c, d, s)
  (a, b, c, d, s)

/-- `scaling_cdiv`; `base/complex.jl:433-438`. -/
def scalingCdiv (a b c d ab cd : F64) : F64 × F64 :=
  let (a, b, c, d, s) := scaleargsCdiv a b c d ab cd
  let (p, q) := cdiv a b c d
  (F64.mul p s, F64.mul q s)

/-- `/(z::ComplexF64, w::ComplexF64)`; `base/complex.jl:400-421`. -/
def div (z w : CF64) : CF64 :=
  let a := z.re
  let b := z.im
  let c := w.re
  let d := w.im
  let absa := F64.abs a
  let absb := F64.abs b
  let ab := if F64.le absb absa then absa else absb
  let absc := F64.abs c
  let absd := F64.abs d
  let cd := if F64.le absd absc then absc else absd
  if F64.isinf c || F64.isinf d then
    if isfinite z then
      ⟨F64.mul (F64.mul Fl.pzero (Fl.sign a)) (Fl.sign c),
       F64.mul (F64.mul Fl.nzero (Fl.sign b)) (Fl.sign d)⟩
    else ⟨F64.add F64.nan (Fl.mulBool false F64.nan), Fl.mulBool true F64.nan⟩
  else
    let (p, q) :=
      if F64.le halfov ab || F64.le ab twounEps || F64.le halfov cd || F64.le cd twounEps
      then scalingCdiv a b c d ab cd
      else cdiv a b c d
    ⟨p, q⟩

/-! ### Inverse, `base/complex.jl:482-517` -/

/-- `robust_cinv`; `base/complex.jl:511-517`. -/
def robustCinv (c d : F64) : F64 × F64 :=
  let r := F64.div d c
  let z := F64.muladd d r c
  (F64.div F64.one z, F64.div (F64.neg r) z)

/-- `inv(w::ComplexF64)`; `base/complex.jl:482-510`. -/
def inv (w : CF64) : Jl CF64 := do
  let c := w.re
  let d := w.im
  let absc := F64.abs c
  let absd := F64.abs d
  let (cd, dc) := if F64.lt absd absc then (absc, absd) else (absd, absc)
  let lo ← F64.sqrt (F64.div F64.floatmin Fl.two)
  let hi ← F64.sqrt (F64.div F64.floatmax Fl.two)
  if F64.le lo cd && F64.le cd hi then
    return divReal (conj w) (F64.muladd cd cd (F64.mul dc dc))
  if F64.isinf c || F64.isinf d then
    return ⟨Fl.copysign Fl.pzero c, Fl.flipsign Fl.nzero d⟩
  let bs := F64.div Fl.two (F64.mul Fl.eps Fl.eps)
  let (c, d, s) :=
    if F64.le (F64.div F64.floatmax Fl.two) cd then (F64.mul c Fl.half, F64.mul d Fl.half, Fl.half)
    else if F64.le cd (F64.div (F64.mul Fl.two F64.floatmin) Fl.eps) then
      (F64.mul c bs, F64.mul d bs, bs)
    else (c, d, F64.one)
  let (p, q) :=
    if F64.le absd absc then robustCinv c d
    else
      let (q, p) := robustCinv (F64.neg d) (F64.neg c)
      (p, q)
  return ⟨F64.mul p s, F64.mul q s⟩

/-! ### Absolute value, `abs(z) = hypot(real(z), imag(z))`, `base/complex.jl:281` -/

/-- `_hypot(x::Float64, y::Float64)` with the hardware-fma branch; `base/math.jl:732-786`. -/
def hypot (x y : F64) : Jl F64 := do
  let axu := F64.abs x
  let ayu := F64.abs y
  let ax := F64.div axu F64.one
  let ay := F64.div ayu F64.one
  if F64.isinf ax || F64.isinf ay then return Fl.inf
  let (axu, ax, ay) := if F64.lt ax ay then (ayu, ay, ax) else (axu, ax, ay)
  let r ← F64.sqrt (F64.div Fl.eps Fl.two)
  if F64.le ay (F64.mul ax r) then return axu
  let sfm ← F64.sqrt F64.floatmin
  let shm ← F64.sqrt (F64.div F64.floatmax Fl.two)
  let scale := F64.mul Fl.eps sfm
  let (ax, ay, scale) :=
    if F64.lt shm ax then (F64.mul ax scale, F64.mul ay scale, F64.div F64.one scale)
    else if F64.lt ay sfm then (F64.div ax scale, F64.div ay scale, scale)
    else (ax, ay, F64.one)
  let h ← F64.sqrt (F64.muladd ax ax (F64.mul ay ay))
  let hsquared := F64.mul h h
  let axsquared := F64.mul ax ax
  let corr := F64.sub
    (F64.add (F64.fma (F64.neg ay) ay (F64.sub hsquared axsquared)) (F64.fma h h (F64.neg hsquared)))
    (F64.fma ax ax (F64.neg axsquared))
  let h := F64.sub h (F64.div corr (F64.mul Fl.two h))
  return F64.mul (F64.mul h scale) F64.one

/-- `abs(z::Complex)`; `base/complex.jl:281`, `base/math.jl:730`. -/
def abs (z : CF64) : Jl F64 := hypot z.re z.im

/-! ### Square root, `base/complex.jl:519-558` -/

/-- `ssqs(x::Float64, y::Float64)`; `base/complex.jl:519-531`. -/
def ssqs (x y : F64) : Jl (F64 × JInt .i64) := do
  let ρ := F64.add (F64.mul x x) (F64.mul y y)
  if !F64.isfinite ρ && (F64.isinf x || F64.isinf y) then
    return (Fl.inf, JInt.lit .i64 0)
  let tiny := F64.div (F64.nextfloat Fl.pzero) (F64.mul Fl.two (F64.mul Fl.eps Fl.eps))
  if F64.isinf ρ || (F64.eq ρ Fl.pzero && (!F64.eq x Fl.pzero || !F64.eq y Fl.pzero)) ||
      F64.lt ρ tiny then
    let m := Fl.max (F64.abs x) (F64.abs y)
    let k ← if F64.eq m Fl.pzero then pure (JInt.lit .i64 0)
      else do let e ← F64.exponent m; pure (JInt.lit .i64 e)
    let xk := F64.ldexp x (-k).val
    let yk := F64.ldexp y (-k).val
    return (F64.add (F64.mul xk xk) (F64.mul yk yk), k)
  return (ρ, JInt.lit .i64 0)

/-- `sqrt(z::Complex)` for `ComplexF64`; `base/complex.jl:533-558`. -/
def sqrt (z : CF64) : Jl CF64 := do
  let x := z.re
  let y := z.im
  if F64.eq x y && F64.eq y Fl.pzero then return ⟨Fl.pzero, y⟩
  let (ρ, k) ← ssqs x y
  let ρ ← if F64.isfinite x then do
      let s ← F64.sqrt ρ
      pure (F64.add (F64.ldexp (F64.abs x) (-k).val) s)
    else pure ρ
  let (k, ρ) ← if k.val % 2 != 0 then do
      let k' ← JInt.div (k - JInt.lit .i64 1) (JInt.lit .i64 2)
      pure (k', ρ)
    else do
      let k' ← JInt.div k (JInt.lit .i64 2)
      pure (k' - JInt.lit .i64 1, F64.add ρ ρ)
  let s ← F64.sqrt ρ
  let ρ := F64.ldexp s k.val
  if !F64.eq ρ Fl.pzero then
    let η := if F64.isfinite y then F64.div (F64.div y ρ) Fl.two else y
    if F64.lt x Fl.pzero then return ⟨F64.abs η, Fl.copysign ρ y⟩
    return ⟨ρ, η⟩
  return ⟨ρ, y⟩

end CF64

end JuliaLean.Complex
