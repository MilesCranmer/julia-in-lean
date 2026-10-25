import JuliaLean.Promotion.IEEE

/-!
Mixed `IEEEFloat`/`BitInteger` comparison, integer-to-float conversion and float-to-integer
conversion at master `bbfa0ce4150`, for all three float types and all ten integer types.
-/

namespace JuliaLean.Promotion

open JuliaLean.Float

/-- Julia's three `IEEEFloat` types. -/
inductive FTy where
  | f16 | f32 | f64
  deriving DecidableEq, Repr

def FTy.fmt : FTy → Fmt
  | .f16 => half | .f32 => single | .f64 => double

/-- `sizeof(T)`. -/
def FTy.bytes : FTy → Nat
  | .f16 => 2 | .f32 => 4 | .f64 => 8

abbrev FV (T : FTy) := Fl T.fmt

/-- `Float32(x::UInt128)` after `abs`; `base/float.jl:307-319`, with UInt32 arithmetic. -/
def f32MagnitudeBits (x : Nat) : Nat :=
  let n := x.log2 + 1
  let y :=
    if n ≤ 24 then (x % 2 ^ 32) * 2 ^ (24 - n) % 2 ^ 32 % 2 ^ 23
    else
      let y := (x / 2 ^ (n - 25)) % 2 ^ 32 % 2 ^ 24
      let y := (y + 1) / 2
      if x % 2 ^ (n - 25) == 0 && (x / 2 ^ (n - 25)) % 2 == 1 then y - y % 2 else y
  let d := (n + 126) % 2 ^ 32 * 2 ^ 23 % 2 ^ 32
  (d + y) % 2 ^ 32

/-- `Float32(x::UInt128)`; `base/float.jl:307-319`. `trailing_zeros(x) == n-25` holds
exactly when the bits below position `n-25` are zero and bit `n-25` is set. -/
def float32OfUInt128 (x : JInt .u128) : Fl single :=
  if x.val = 0 then Fl.zero else Fl.ofBits (f32MagnitudeBits x.val.toNat)

/-- `Float32(x::Int128)`; `base/float.jl:321-336`. -/
def float32OfInt128 (x : JInt .i128) : Fl single :=
  if x.val = 0 then Fl.zero
  else
    let s := if x.val < 0 then 2 ^ 31 else 0
    Fl.ofBits ((s + f32MagnitudeBits x.val.natAbs) % 2 ^ 32)

/-- `Tf(y)` for a `BitInteger` `y`: `sitofp`/`uitofp` (`base/float.jl:243-256`), the
128-bit methods `base/float.jl:265-336`, and `Float16(x::Int128) = Float16(Float64(x))`
(`base/float.jl:339-340`). -/
def ofJInt {t : IntTy} : (T : FTy) → JInt t → FV T
  | .f64, y => Fl.ofF64 (F64.ofJInt y)
  | .f32, y =>
    match t, y with
    | .u128, y => float32OfUInt128 y
    | .i128, y => float32OfInt128 y
    | _, y => Fl.ofInt y.val
  | .f16, y =>
    match t with
    | .u128 | .i128 => Fl.convert (Fl.ofF64 (F64.ofJInt y))
    | _ => Fl.ofInt y.val

/-- How `op(x::Tf, y::Ti)` dispatches for `op ∈ (==, <, <=)`. -/
inductive Rule where
  /-- The exact methods generated at `base/float.jl:649-676`. -/
  | exact
  /-- `op(Float64(x), Float64(y))`; `base/float.jl:680-684`. -/
  | viaF64
  /-- `op(Float32(x), Float32(y))`; `base/float.jl:686-687`. -/
  | viaF32
  /-- `op(promote(x, y)...)` with `promote_type(Tf, Ti) == Tf`; `base/promotion.jl:516-518`,
  `base/float.jl:243-263`. -/
  | promote
  deriving DecidableEq, Repr

def rule : FTy → IntTy → Rule
  | .f32, .i64 | .f32, .u64 | .f32, .i128 | .f32, .u128 => .exact
  | .f64, .i64 | .f64, .u64 | .f64, .i128 | .f64, .u128 => .exact
  | .f16, .i64 | .f16, .u64 | .f16, .i128 | .f16, .u128 => .viaF64
  | .f16, .i32 | .f16, .u32 | .f32, .i32 | .f32, .u32 => .viaF64
  | .f16, .i16 | .f16, .u16 => .viaF32
  | _, _ => .promote

/-- Comparison operators of `base/float.jl:649-690`. -/
inductive Op where
  | eq | lt | le
  deriving DecidableEq, Repr

def Op.float {f : Fmt} : Op → Fl f → Fl f → Bool
  | .eq => Fl.eq | .lt => Fl.lt | .le => Fl.le

def Op.int : Op → Int → Int → Bool
  | .eq => fun a b => decide (a = b) | .lt => fun a b => decide (a < b) | .le => fun a b => decide (a ≤ b)

/-- `op(x::Tf, y::Ti)`. -/
def cmpFI (op : Op) {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) : Bool :=
  match rule T t with
  | .exact =>
    let fy := ofJInt T y
    let tmax := ofJInt T (JInt.typemax t)
    let ty := (fy.unsafeTrunc t).val
    match op with
    | .eq => Fl.eq x fy && !Fl.eq fy tmax && y.val == ty
    | .lt => Fl.lt x fy || (Fl.eq x fy && Fl.lt fy tmax && decide (ty < y.val))
    | .le => Fl.lt x fy || (Fl.eq x fy && Fl.lt fy tmax && decide (ty ≤ y.val))
  | .viaF64 => op.float (Fl.convert (f := double) x) (ofJInt .f64 y)
  | .viaF32 => op.float (Fl.convert (f := single) x) (ofJInt .f32 y)
  | .promote => op.float x (ofJInt T y)

/-- `op(x::Ti, y::Tf)`; `==(y::Ti, x::Tf) = x==y` at `base/float.jl:656`. -/
def cmpIF (op : Op) {T : FTy} {t : IntTy} (x : JInt t) (y : FV T) : Bool :=
  match rule T t with
  | .exact =>
    let fx := ofJInt T x
    let tmax := ofJInt T (JInt.typemax t)
    let tx := (fx.unsafeTrunc t).val
    match op with
    | .eq => cmpFI .eq y x
    | .lt => Fl.lt fx y || (Fl.eq fx y && (Fl.eq fx tmax || decide (x.val < tx)))
    | .le => Fl.lt fx y || (Fl.eq fx y && (Fl.eq fx tmax || decide (x.val ≤ tx)))
  | .viaF64 => op.float (ofJInt .f64 x) (Fl.convert (f := double) y)
  | .viaF32 => op.float (ofJInt .f32 x) (Fl.convert (f := single) y)
  | .promote => op.float (ofJInt T x) y

/-- `isequal(x::AbstractFloat, y::Real)`; `base/operators.jl:203`. -/
def isequalFI {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) : Bool :=
  (x.signbit == decide (y.val < 0)) && cmpFI .eq x y

/-- `isless(x::AbstractFloat, y::Real)`; `base/operators.jl:242`. -/
def islessFI {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) : Bool :=
  (!x.isnan && (x.signbit && !decide (y.val < 0))) || cmpFI .lt x y

/-- `isless(x::Real, y::AbstractFloat)`; `base/operators.jl:241`. -/
def islessIF {T : FTy} {t : IntTy} (x : JInt t) (y : FV T) : Bool :=
  (y.isnan || (decide (x.val < 0) && !y.signbit)) || cmpIF .lt x y

/-- `cmp(x, y)`; `base/operators.jl:526`. -/
def cmpOrderFI {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) : Int :=
  if islessFI x y then -1 else if islessIF y x then 1 else 0

/-! Float-to-integer conversion, `base/float.jl:881-931`. -/

/-- `Tf(typemin(Ti))` and `Tf(typemax(Ti))`, evaluated when the methods are generated. -/
def lo (T : FTy) (t : IntTy) : FV T := ofJInt T (JInt.typemin t)
def hi (T : FTy) (t : IntTy) : FV T := ofJInt T (JInt.typemax t)
def one (T : FTy) : FV T := Fl.ofInt 1

/-- The first branch (`Ti <: Unsigned || sizeof(Ti) < sizeof(Tf)`); `base/float.jl:883`. -/
def smallBranch (T : FTy) (t : IntTy) : Bool := !t.signed || t.bits / 8 < T.bytes

/-- `round(Ti, x::Tf, RoundToZero)`, i.e. `trunc(Ti, x)`; `base/float.jl:888-894,914-920`. -/
def truncTo (T : FTy) (t : IntTy) (x : FV T) : Jl (JInt t) :=
  let valid :=
    if smallBranch T t then
      Fl.lt (Fl.add (lo T t) (Fl.neg (one T))) x && Fl.lt x (Fl.add (hi T t) (one T))
    else
      let lower := if (lo T t).toBits == (Fl.inf true : FV T).toBits then Fl.lt (lo T t) x
        else Fl.le (lo T t) x
      lower && Fl.lt x (hi T t)
  if valid then .ok (x.unsafeTrunc t) else .error (.inexactError "round")

/-- `Ti(x::Tf)`; `base/float.jl:895-902,921-927`. -/
def toInt (T : FTy) (t : IntTy) (x : FV T) : Jl (JInt t) :=
  let upper := if smallBranch T t then Fl.add (hi T t) (one T) else hi T t
  if Fl.le (lo T t) x && Fl.lt x upper && x.isinteger then .ok (x.unsafeTrunc t)
  else .error (.inexactError t.name)

end JuliaLean.Promotion
