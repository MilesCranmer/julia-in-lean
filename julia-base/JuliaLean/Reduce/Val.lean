import JuliaLean.Reduce.Model
import JuliaLean.Float.Extras

/-!
A small dynamically typed value universe for reductions whose result type is
chosen at run time: `BitInteger` values, `Float64`, `Bool` and `missing`, with
the element types of arrays built from them (`Ty`, including two-member unions
and `Union{}`). Arithmetic promotes as Julia's `promote` does for these types
(integers wrap into the promoted type, `base/int.jl:809-822`; `Bool` promotes
to the other integer type; integers and `Bool` promote to `Float64`).
-/

namespace JuliaLean.Reduce

open JuliaLean.Float

/-- A Julia value. -/
inductive Val where
  | int (t : IntTy) (x : JInt t)
  | f64 (x : F64)
  | bool (b : Bool)
  | missing
  deriving DecidableEq

/-- A Julia element type: concrete types, `Union{a, b}` and `Union{}` (`bottom`). -/
inductive Ty where
  | int (t : IntTy)
  | f64
  | bool
  | missing
  | union (a b : Ty)
  | bottom
  deriving DecidableEq, Repr

namespace Val

instance : Inhabited Val := ⟨.missing⟩

/-- `Int64` literal. -/
def i64 (x : Int) : Val := .int .i64 (JInt.lit .i64 x)

/-- `typeof(v)`. -/
def typeOf : Val → Ty
  | .int t _ => .int t
  | .f64 _ => .f64
  | .bool _ => .bool
  | .missing => .missing

/-- `isnan(v)` for a `Number` (`false` for integers and `Bool`, never called on `missing`). -/
def isnan : Val → Bool
  | .f64 x => F64.isnan x
  | _ => false

/-- `isunordered(v)`, `base/operators.jl:283-285`, `base/missing.jl:71`. -/
def isunordered : Val → Bool
  | .f64 x => F64.isnan x
  | .missing => true
  | _ => false

/-- `Float64(v)` for a real number. -/
def toF64 : Val → F64
  | .int _ x => F64.ofJInt x
  | .f64 x => x
  | .bool b => if b then F64.one else F64.zero
  | .missing => F64.nan

/-- `T(b)` for a `Bool` and an integer type. -/
def boolInt (t : IntTy) (b : Bool) : JInt t := JInt.lit t (if b then 1 else 0)

/-- Binary arithmetic after promotion: `missing` absorbs (`base/missing.jl:116-127`), two
integers meet in `IntTy.promote` with wrapping conversion, a `Bool` meets an integer in the
integer's type, anything meeting a `Float64` becomes `Float64`. -/
def numBin (opI : (t : IntTy) → JInt t → JInt t → Val) (opF : F64 → F64 → Val)
    (opB : Bool → Bool → Val) : Val → Val → Val
  | .missing, _ => .missing
  | _, .missing => .missing
  | .int s x, .int t y =>
    let p := IntTy.promote s t
    opI p (JInt.rem p x) (JInt.rem p y)
  | .bool a, .int t y => opI t (boolInt t a) y
  | .int t x, .bool b => opI t x (boolInt t b)
  | .bool a, .bool b => opB a b
  | x, y => opF (toF64 x) (toF64 y)

/-- `x + y`; `+(::Bool, ::Bool)` is `Int(x) + Int(y)` (`base/bool.jl:145`), and a `Bool`
plus a float is `ifelse(x, oneunit(y) + y, y)` (`base/bool.jl:155-158`). -/
def plus : Val → Val → Val
  | .bool b, .f64 y | .f64 y, .bool b => .f64 (if b then F64.add F64.one y else y)
  | x, y => numBin (fun t x y => .int t (x + y)) (fun x y => .f64 (F64.add x y))
    (fun a b => .int .i64 (boolInt .i64 a + boolInt .i64 b)) x y

/-- `x * y`; `*(::Bool, ::Bool)` is `x & y` (`base/bool.jl:149`), and a `Bool` times a
float is `ifelse(x, y, copysign(zero(y), y))` (`base/bool.jl:161-164`). -/
def times : Val → Val → Val
  | .bool b, .f64 y | .f64 y, .bool b => .f64 (if b then y else F64.zero (F64.signbit y))
  | x, y => numBin (fun t x y => .int t (x * y)) (fun x y => .f64 (F64.mul x y))
    (fun a b => .bool (a && b)) x y

/-- `_isless(x, y)` on floats, `base/math.jl:833`. -/
def fisless (x y : F64) : Bool := F64.lt x y || (F64.signbit x && !F64.signbit y)

/-- `max(x, y)` on `Float64` (`max_float`), semantics of `base/math.jl:835`. -/
def fmax (x y : F64) : F64 := if F64.isnan x || (!F64.isnan y && fisless y x) then x else y

/-- `min(x, y)` on `Float64` (`min_float`), semantics of `base/math.jl:834`. -/
def fmin (x y : F64) : F64 := if F64.isnan x || (!F64.isnan y && fisless x y) then x else y

/-- `max(x, y)`: `max(x::T, y::T) = ifelse(y < x, x, y)` for integers and `Bool`
(`base/promotion.jl`), `base/math.jl:835` for floats, `missing` absorbing
(`base/missing.jl:129-137`). -/
def vmax : Val → Val → Val :=
  numBin (fun t x y => .int t (if y.val < x.val then x else y)) (fun x y => .f64 (fmax x y))
    (fun a b => .bool (if !b && a then a else b))

/-- `min(x, y)`, mirror of `vmax`. -/
def vmin : Val → Val → Val :=
  numBin (fun t x y => .int t (if y.val < x.val then y else x)) (fun x y => .f64 (fmin x y))
    (fun a b => .bool (if !b && a then b else a))

/-- `isless(x, y)`: `missing` is greater than everything (`base/missing.jl:86-88`), numbers
compare after promotion, floats with `F64.isless`. -/
def visless : Val → Val → Bool
  | .missing, _ => false
  | _, .missing => true
  | x, y =>
    match numBin (fun _ a b => .bool (decide (a.val < b.val)))
        (fun a b => .bool (F64.isless a b)) (fun a b => .bool (!a && b)) x y with
    | .bool r => r
    | _ => false

/-- `abs(x)`: wrapping for signed integers (`abs(typemin(T)) == typemin(T)`), identity for
unsigned integers and `Bool`, sign bit cleared for floats, `missing` absorbing. -/
def vabs : Val → Val
  | .int t x => .int t (JInt.wrap t (if x.val < 0 then -x.val else x.val))
  | .f64 x => .f64 (F64.abs x)
  | v => v

/-- Signed `BitInteger` types narrower than `Int` (`BitSignedSmall`). -/
def smallSigned : IntTy → Bool
  | .i8 | .i16 | .i32 => true
  | _ => false

/-- Unsigned `BitInteger` types narrower than `UInt` (`BitUnsignedSmall`). -/
def smallUnsigned : IntTy → Bool
  | .u8 | .u16 | .u32 => true
  | _ => false

/-- `Union{Bool, BitIntegerSmall}` membership. -/
def smallOrBool : Val → Bool
  | .int t _ => smallSigned t || smallUnsigned t
  | .bool _ => true
  | _ => false

/-- Integer value of a `Bool` or integer. -/
def intVal : Val → Int
  | .int _ x => x.val
  | .bool b => if b then 1 else 0
  | _ => 0

/-- `Base.add_sum(x, y)`, `base/reduce.jl:16-19`. -/
def addSum (x y : Val) : Val :=
  match x, y with
  | .int s _, .int t _ =>
    if smallUnsigned s && smallUnsigned t then .int .u64 (JInt.wrap .u64 (intVal x + intVal y))
    else if smallOrBool x && smallOrBool y then .int .i64 (JInt.wrap .i64 (intVal x + intVal y))
    else plus x y
  | _, _ =>
    if smallOrBool x && smallOrBool y then .int .i64 (JInt.wrap .i64 (intVal x + intVal y))
    else plus x y

/-- `Base.mul_prod(x, y)`, `base/reduce.jl:27-30`. -/
def mulProd (x y : Val) : Val :=
  match x, y with
  | .int s _, .int t _ =>
    if smallSigned s && smallSigned t then .int .i64 (JInt.wrap .i64 (intVal x * intVal y))
    else if smallUnsigned s && smallUnsigned t then .int .u64 (JInt.wrap .u64 (intVal x * intVal y))
    else times x y
  | _, _ => times x y

/-- `reduce_first(add_sum, x)`, `base/reduce.jl:410, 413-415`. -/
def firstAddSum : Val → Val
  | .int t x =>
    if smallSigned t then .int .i64 (JInt.wrap .i64 x.val)
    else if smallUnsigned t then .int .u64 (JInt.wrap .u64 x.val)
    else .int t x
  | .bool b => .int .i64 (boolInt .i64 b)
  | v => v

/-- `reduce_first(mul_prod, x)`, `base/reduce.jl:416-418`. -/
def firstMulProd : Val → Val
  | .int t x =>
    if smallSigned t then .int .i64 (JInt.wrap .i64 x.val)
    else if smallUnsigned t then .int .u64 (JInt.wrap .u64 x.val)
    else .int t x
  | v => v

/-- `reduce_first(+, x)`, `base/reduce.jl:409-410`. -/
def firstPlus : Val → Val
  | .bool b => .int .i64 (boolInt .i64 b)
  | v => v

/-- `or_any(x, y)`, `base/reduce.jl:33, 36`: `(x || y)::Bool`, `x | y` on two `Bool`s. -/
def orAny : Val → Val → R Val
  | .bool true, _ => .ok (.bool true)
  | .bool false, .bool b => .ok (.bool b)
  | _, _ => .error .typeError

/-- `and_all(x, y)`, `base/reduce.jl:32, 35`: `(x && y)::Bool`, `x & y` on two `Bool`s. -/
def andAll : Val → Val → R Val
  | .bool false, _ => .ok (.bool false)
  | .bool true, .bool b => .ok (.bool b)
  | _, _ => .error .typeError

/-- `x | y` on `Bool` and `missing`, `base/bool.jl:15`, `base/missing.jl:162-164`. -/
def bor : Val → Val → R Val
  | .bool a, .bool b => .ok (.bool (a || b))
  | .missing, .bool b | .bool b, .missing => .ok (if b then .bool true else .missing)
  | .missing, .missing => .ok .missing
  | _, _ => .error .methodError

end Val

namespace Ty

/-- `v isa T`. -/
def isa (v : Val) : Ty → Bool
  | .union a b => isa v a || isa v b
  | .bottom => false
  | t => decide (v.typeOf = t)

/-- `promote_type(a, b)` on the modelled types (`base/promotion.jl`, `base/int.jl:809-822`,
`base/missing.jl:48`). -/
def promote : Ty → Ty → Ty
  | .int s, .int t => .int (IntTy.promote s t)
  | .int t, .bool | .bool, .int t => .int t
  | .int _, .f64 | .f64, .int _ | .bool, .f64 | .f64, .bool | .f64, .f64 => .f64
  | .bool, .bool => .bool
  | .missing, .missing => .missing
  | .missing, s | s, .missing => .union s .missing
  | .bottom, s | s, .bottom => s
  | a, b => .union a b

/-- `promote_union(T)`, `base/reducedim.jl:59-60`. -/
def promoteUnion : Ty → Ty
  | .union a b => promote (promoteUnion a) (promoteUnion b)
  | t => t

/-- `nonmissingtype(T)`, `base/missing.jl:39`; `Missing` gives `Union{}`. -/
def nonmissing : Ty → Ty
  | .missing => .bottom
  | .union a b =>
    match nonmissing a, nonmissing b with
    | .bottom, y => y
    | x, .bottom => x
    | x, y => .union x y
  | t => t

/-- `T <: Union{BitInteger, IEEEFloat, BigFloat}`; `Union{}` is a subtype of every type. -/
def bitIntFloat : Ty → Bool
  | .int _ | .f64 | .bottom => true
  | .union a b => bitIntFloat a && bitIntFloat b
  | _ => false

/-- `typemax(T)` (`Inf` for `Float64`); no method for `Union{}` or unions. -/
def typemax : Ty → R Val
  | .int t => .ok (.int t (JInt.typemax t))
  | .f64 => .ok (.f64 (F64.inf false))
  | _ => .error .methodError

/-- `typemin(T)` (`-Inf` for `Float64`). -/
def typemin : Ty → R Val
  | .int t => .ok (.int t (JInt.typemin t))
  | .f64 => .ok (.f64 (F64.inf true))
  | _ => .error .methodError

/-- `zero(T)`, with `zero(Union{T, Missing}) = zero(T)` (`base/missing.jl:105-108`) and, for
a union of numbers, `zero(T) = convert(T, 0)` (`base/number.jl`), which is the `Int` `0`
when `Int` is a member; `none` when no method applies. -/
def zero : Ty → Option Val
  | .int t => some (.int t (JInt.lit t 0))
  | .f64 => some (.f64 F64.zero)
  | .bool => some (.bool false)
  | .missing => some .missing
  | .union a b =>
    if a = .missing then zero b else if b = .missing then zero a
    else if isa (Val.i64 0) (.union a b) then some (Val.i64 0) else none
  | .bottom => none

/-- `one(T)`, the analogue of `zero`. -/
def one : Ty → Option Val
  | .int t => some (.int t (JInt.lit t 1))
  | .f64 => some (.f64 F64.one)
  | .bool => some (.bool true)
  | .missing => some .missing
  | .union a b =>
    if a = .missing then one b else if b = .missing then one a
    else if isa (Val.i64 1) (.union a b) then some (Val.i64 1) else none
  | .bottom => none

/-- `convert(T, v)` as performed by `setindex!` on an array with element type `T`. -/
def convert (ty : Ty) (v : Val) : R Val :=
  if isa v ty then .ok v
  else
    match ty, v with
    | .int t, .int _ x =>
      match JInt.convert t x.val with
      | .ok y => .ok (.int t y)
      | .error _ => .error .inexactError
    | .int t, .f64 x =>
      match F64.int t x with
      | .ok y => .ok (.int t y)
      | .error _ => .error .inexactError
    | .int t, .bool b => .ok (.int t (Val.boolInt t b))
    | .f64, .int _ x => .ok (.f64 (F64.ofJInt x))
    | .f64, .bool b => .ok (.f64 (Val.toF64 (.bool b)))
    | .bool, .int _ x =>
      if x.val = 0 then .ok (.bool false) else if x.val = 1 then .ok (.bool true)
      else .error .inexactError
    | .union a b, v =>
      if a = .missing then convertNonmissing b v
      else if b = .missing then convertNonmissing a v
      else .error .methodError
    | _, _ => .error .methodError
where
  /-- `convert(T, v)` for the non-missing member of `Union{T, Missing}`. -/
  convertNonmissing (t : Ty) (v : Val) : R Val :=
    match t, v with
    | .int t, .int _ x =>
      match JInt.convert t x.val with
      | .ok y => .ok (.int t y)
      | .error _ => .error .inexactError
    | .int t, .f64 x =>
      match F64.int t x with
      | .ok y => .ok (.int t y)
      | .error _ => .error .inexactError
    | .f64, .int _ x => .ok (.f64 (F64.ofJInt x))
    | _, _ => .error .methodError

end Ty

end JuliaLean.Reduce
