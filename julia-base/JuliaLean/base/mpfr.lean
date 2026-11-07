import JuliaLean.Core
import JuliaLean.base.gmp
import JuliaLean.base.float
import JuliaLean.base.rational
import JuliaLean.base.show

/-!
# Model of `base/mpfr.jl`

Julia f755f49a9e41380d7da126b3c1db9fe7f83dd027, 64-bit Unix ABI.
Finite values retain the exact dyadic value and the MPFR precision/sign/exponent
and little-endian limb layout. MPFR operations are mathematical primitives,
with rounding to the output precision and the current exponent limits.
The state monad retains MPFR flags, global defaults and scoped overrides even
when Julia raises an exception. Faithful rounding has an explicit lower/upper
choice, as permitted by MPFR. Analytic C calls without an exact kernel use explicit
typed interfaces; their outputs are not assumed by this model.
-/
namespace JuliaLean.base.mpfr
open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
abbrev BigInt := JuliaLean.base.gmp.BigInt
abbrev Limb := JuliaLean.base.gmp.Limb
abbrev Clong := JInt .i64
abbrev Culong := JInt .u64
abbrev Cint := JInt .i32


/--
MPFR manual §4.4 Rounding: https://www.mpfr.org/mpfr-current/mpfr.html#Rounding

Julia source: base/mpfr.jl:66-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
    MPFRRoundNearest
    MPFRRoundToZero
    MPFRRoundUp
    MPFRRoundDown
    MPFRRoundFromZero
    MPFRRoundFaithful
end
```
-/
inductive Mode where
  | nearest | toZero | up | down | fromZero | faithful
  deriving DecidableEq, Repr, Inhabited

/--
Base `Enums.jl:17, 19-23, 30-75, 91, 93`; macro expansion `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeBaseType : IntTy := .i32

/--
Base `Enums.jl:221-224`; `membershiptest` is `Enums.jl:79-87`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeFromInteger {I : Type}
    (atLeastZero : JInt .i32 → I → Bool) (atMostFive : I → JInt .i32 → Bool)
    (convert : I → Jl (JInt .i32)) (showInteger : I → String) (x : I) : Jl Mode :=
  if !atLeastZero (JInt.lit .i32 0) x then
    .error (.argumentError ("invalid value for Enum MPFRRoundingMode: " ++ showInteger x))
  else if !atMostFive x (JInt.lit .i32 5) then
    .error (.argumentError ("invalid value for Enum MPFRRoundingMode: " ++ showInteger x))
  else do
    let code ← convert x
    match code.val with
    | 0 => pure .nearest
    | 1 => pure .toZero
    | 2 => pure .up
    | 3 => pure .down
    | 4 => pure .fromZero
    | 5 => pure .faithful
    | _ => .error (.argumentError "invalid MPFRRoundingMode bit pattern")

/--
Base `Enums.jl:19`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeInteger : Mode → JInt .i32
  | .nearest => JInt.lit .i32 0
  | .toZero => JInt.lit .i32 1
  | .up => JInt.lit .i32 2
  | .down => JInt.lit .i32 3
  | .fromZero => JInt.lit .i32 4
  | .faithful => JInt.lit .i32 5

/--
Base `Enums.jl:20`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeCconvert {M : Type → Type} {A : Type} (convert : JInt .i32 → M A) (x : Mode) : M A :=
  convert (modeInteger x)

/--
Base `Enums.jl:21`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeWrite {Io R : Type} {M : Type → Type} (writeInteger : Io → JInt .i32 → M R) (io : Io) (x : Mode) : M R :=
  writeInteger io (modeInteger x)

/--
Base `Enums.jl:22`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeRead {Io : Type} {M : Type → Type} [Monad M] (readInteger : Io → M (JInt .i32))
    (construct : JInt .i32 → M Mode) (io : Io) : M Mode := do
  let code ← readInteger io
  construct code

/--
Base `Enums.jl:32`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeIsless (x y : Mode) : Bool :=
  JuliaLean.base.int.ltSame (modeInteger x) (modeInteger y)

/--
Base `Enums.jl:30, 233`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeEnumHash (typeHash : JInt .u64)
    (hashInteger : JInt .i32 → JInt .u64 → JInt .u64)
    (hashUInt : JInt .u64 → JInt .u64 → JInt .u64)
    (x : Mode) (h : JInt .u64) : JInt .u64 :=
  hashUInt typeHash (hashInteger (modeInteger x) h)

/--
Base `Enums.jl:225`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeNameMap : List (JInt .i32 × String) :=
  [(JInt.lit .i32 0, "MPFRRoundNearest"), (JInt.lit .i32 1, "MPFRRoundToZero"),
   (JInt.lit .i32 2, "MPFRRoundUp"), (JInt.lit .i32 3, "MPFRRoundDown"),
   (JInt.lit .i32 4, "MPFRRoundFromZero"), (JInt.lit .i32 5, "MPFRRoundFaithful")]

/--
Base `Enums.jl:226`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeTypemin : Mode := .nearest

/--
Base `Enums.jl:227`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeTypemax : Mode := .faithful

/--
Base `Enums.jl:235-237`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeInstances : List Mode := [.nearest, .toZero, .up, .down, .fromZero, .faithful]

/--
Base `Enums.jl:34`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeSymbol (x : Mode) : String :=
  match x with
  | .nearest => "MPFRRoundNearest"
  | .toZero => "MPFRRoundToZero"
  | .up => "MPFRRoundUp"
  | .down => "MPFRRoundDown"
  | .fromZero => "MPFRRoundFromZero"
  | .faithful => "MPFRRoundFaithful"

/--
Base `Enums.jl:36-40`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeInternalSymbol (code : JInt .i32) : String :=
  match modeNameMap.find? (fun (value, _) => value.val == code.val) with
  | some (_, name) => name
  | none => "<invalid #" ++ toString code.val ++ ">"

/--
Base `Enums.jl:42`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modePrint {m : Type → Type} [Monad m] {Io V : Type} (p : JuliaLean.base.show.IOPrims m Io V)
    (io : JuliaLean.base.show.JIO Io V) (x : Mode) : m Unit :=
  JuliaLean.base.show.print_Symbol p io (modeSymbol x)

/--
Base `Enums.jl:44-55`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeShow {m : Type → Type} {Io V Ty Mod : Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m]
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (moduleOfValue : V → Except JuliaLean.base.show.ShowError (Option Mod))
    (main parent : Mod) (isvisible : String → Mod → Mod → m Bool)
    (showModule : JuliaLean.base.show.JIO Io V → Mod → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (x : Mode) : m Unit := do
  if !(← JuliaLean.base.show.assertBool a (JuliaLean.base.show.getIO p io "compact" false)) then
    let origin ← match JuliaLean.base.show.getIO p io "module" main with
      | .inl value =>
          match moduleOfValue value with
          | .ok module => pure module
          | .error error => JuliaLean.base.show.throwShow error
      | .inr fallback => pure (some fallback)
    let qualify ← match origin with
      | none => pure true
      | some originModule => do
          let visible ← isvisible (modeSymbol x) parent originModule
          pure !visible
    if qualify then
      showModule io parent
      JuliaLean.base.show.printStr p io "."
  JuliaLean.base.show.print_Symbol p io (modeSymbol x)

/--
Base `Enums.jl:57-62`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeShowTextPlain {m : Type → Type} {Io V Ty : Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m]
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (showType : JuliaLean.base.show.JIO Io V → m Unit)
    (showInteger : JuliaLean.base.show.JIO Io V → JInt .i32 → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (x : Mode) : m Unit := do
  modePrint p io x
  JuliaLean.base.show.printStr p io "::"
  let compactIO ← JuliaLean.base.show.withBool p a io "compact" true
  showType compactIO
  JuliaLean.base.show.printStr p io " = "
  showInteger io (modeInteger x)

/--
Base `Enums.jl:64-75`; macro expansion is `Enums.jl:218-237`.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeShowTypeTextPlain {m : Type → Type} {Io V : Type} [Monad m]
    (p : JuliaLean.base.show.IOPrims m Io V)
    (showDatatype : JuliaLean.base.show.JIO Io V → m Unit)
    (showInteger : JuliaLean.base.show.JIO Io V → JInt .i32 → m Unit)
    (io : JuliaLean.base.show.JIO Io V) : m Unit := do
  JuliaLean.base.show.printStr p io "Enum "
  showDatatype io
  JuliaLean.base.show.printStr p io ":"
  for x in modeInstances do
    JuliaLean.base.show.printStr p io "\n"
    JuliaLean.base.show.print_Symbol p io (modeSymbol x)
    JuliaLean.base.show.printStr p io " = "
    showInteger io (modeInteger x)

/--
Base `Enums.jl:91`; `Ref` uses the installed `base/refvalue.jl` constructor.
Julia source: base/mpfr.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum MPFRRoundingMode begin
```
-/
def modeBroadcastable {R : Type} (makeRef : Mode → R) (x : Mode) : R := makeRef x


/--
Julia source: base/mpfr.jl:75-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Nearest})  = MPFRRoundNearest
convert(::Type{MPFRRoundingMode}, ::RoundingMode{:ToZero})   = MPFRRoundToZero
convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Up})       = MPFRRoundUp
convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Down})     = MPFRRoundDown
convert(::Type{MPFRRoundingMode}, ::RoundingMode{:FromZero}) = MPFRRoundFromZero

function convert(::Type{RoundingMode}, r::MPFRRoundingMode)
    if r == MPFRRoundNearest
        return RoundNearest
    elseif r == MPFRRoundToZero
        return RoundToZero
    elseif r == MPFRRoundUp
        return RoundUp
    elseif r == MPFRRoundDown
        return RoundDown
    elseif r == MPFRRoundFromZero
        return RoundFromZero
    else
        throw(ArgumentError("invalid MPFR rounding mode code: $r"))
    end
end
```
-/
def toMPFR : RoundingMode → Jl Mode
  | .Nearest => pure .nearest
  | .ToZero => pure .toZero
  | .Up => pure .up
  | .Down => pure .down
  | .FromZero => pure .fromZero
  | _ => .error (.methodError "convert")
def toPublic : Mode → Jl RoundingMode
  | .nearest => pure .Nearest
  | .toZero => pure .ToZero
  | .up => pure .Up
  | .down => pure .Down
  | .fromZero => pure .FromZero
  | .faithful => .error (.argumentError "invalid MPFR rounding mode code")

/--
Julia source: base/mpfr.jl:97-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounds_to_nearest(m::MPFRRoundingMode) = m == MPFRRoundNearest
function rounds_away_from_zero(m::MPFRRoundingMode, sign_bit::Bool)
    if m == MPFRRoundToZero
        false
    elseif m == MPFRRoundUp
        !sign_bit
    elseif m == MPFRRoundDown
        sign_bit
    else
        # Assuming `m == MPFRRoundFromZero`
        true
    end
end
tie_breaker_is_to_even(::MPFRRoundingMode) = true
```
-/
def roundsToNearest (r : Mode) : Bool := r == .nearest
def roundsAway (r : Mode) (negative : Bool) : Bool :=
  if r = .toZero then false else if r = .up then !negative
  else if r = .down then negative else true
def tieBreakerEven (_r : Mode) : Bool := true

inductive FP where
  | nan (negative : Bool)
  | inf (negative : Bool)
  | zero (negative : Bool)
  | finite (mantissa : Int) (scale : Int)
  deriving DecidableEq, Repr

def FP.signbit : FP → Bool
  | .nan s | .inf s | .zero s => s
  | .finite m _ => decide (m < 0)
def FP.isnan : FP → Bool | .nan _ => true | _ => false
def FP.isinf : FP → Bool | .inf _ => true | _ => false
def FP.iszero : FP → Bool | .zero _ => true | .finite m _ => decide (m = 0) | _ => false

def FP.toRat : FP → Int × Nat
  | .finite m e => if e ≥ 0 then (m*2^e.toNat,1) else (m,2^(-e).toNat)
  | _ => (0,1)

def FP.neg : FP → FP
  | .nan s => .nan (!s)
  | .inf s => .inf (!s)
  | .zero s => .zero (!s)
  | .finite m e => .finite (-m) e

def specialZeroExp : Clong := JInt.typemin .i64 + JInt.wrap .i64 1
def specialNanExp : Clong := specialZeroExp + JInt.wrap .i64 1
def specialInfExp : Clong := specialNanExp + JInt.wrap .i64 1


/--
Julia source: base/mpfr.jl:124-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct BigFloatLayout
    prec::Clong
    sign::Cint
    exp::Clong
    d::Ptr{Limb}
    # possible padding
    p::Limb # Tuple{Vararg{Limb}}
end
const offset_prec = fieldoffset(BigFloatLayout, 1) % Int
const offset_sign = fieldoffset(BigFloatLayout, 2) % Int
const offset_exp = fieldoffset(BigFloatLayout, 3) % Int
const offset_d = fieldoffset(BigFloatLayout, 4) % Int
const offset_p_limbs = ((fieldoffset(BigFloatLayout, 5) % Int + sizeof(Limb) - 1) ÷ sizeof(Limb))
const offset_p = offset_p_limbs * sizeof(Limb)

"""
    BigFloat <: AbstractFloat

Arbitrary precision floating point number type.
"""
struct BigFloat <: AbstractFloat
    d::Memory{Limb}

    # Not recommended for general use:
    # used internally by, e.g. deepcopy
    global function _BigFloat(d::Memory{Limb})
        Base.unsafe_convert(Ref{BigFloat}, BigFloatData(d)) # force early initialization of pointer field of z.d
        return new(d)
    end

    function BigFloat(; precision::Integer=_precision_with_base_2(BigFloat))
        precision < 1 && throw(DomainError(precision, "`precision` cannot be less than 1."))
        nb = ccall((:mpfr_custom_get_size,libmpfr), Csize_t, (Clong,), precision)
        nl = (nb + offset_p + sizeof(Limb) - 1) ÷ Core.sizeof(Limb) # align to number of Limb allocations required for this
        d = Memory{Limb}(undef, nl % Int)
        # ccall-based version, inlined below
        #ccall((:mpfr_custom_init,libmpfr), Cvoid, (Ptr{Limb}, Clong), BigFloatData(d), prec) # currently seems to be a no-op in mpfr
        #NAN_KIND = Cint(0)
        #ccall((:mpfr_custom_init_set,libmpfr), Cvoid, (Ref{BigFloat}, Cint, Clong, Ptr{Limb}), z, NAN_KIND, prec, BigFloatData(d))
        p = Base.unsafe_convert(Ptr{Limb}, d)
        GC.@preserve d begin # initialize to +NAN
            unsafe_store!(Ptr{Clong}(p) + offset_prec, Clong(precision))
            unsafe_store!(Ptr{Cint}(p) + offset_sign, one(Cint))
            unsafe_store!(Ptr{Clong}(p) + offset_exp, mpfr_special_exponent_nan)
            unsafe_store!(Ptr{Ptr{Limb}}(p) + offset_d, p + offset_p)
        end
        return new(d)
    end
end
```
-/
structure BigFloat where
  value : FP
  prec : Clong
  sign : Cint
  exp : Clong
  d : List Limb
  deriving DecidableEq, Repr

/-- MPFR manual §5.16 `mpfr_custom_get_size`, 64-bit limbs.
https://www.mpfr.org/mpfr-current/mpfr.html#Custom-Interface -/
def customGetSize (precision : Clong) : Culong :=
  JInt.wrap .u64 (8*((precision.val+63).tdiv 64))

def pack (precision : Clong) (value : FP) : BigFloat :=
  let nlimbs := (precision.val.toNat+63)/64
  let negative := value.signbit
  let sign := JInt.wrap .i32 (if negative then -1 else 1)
  let (exponent,limbs) := match value with
    | .nan _ => (specialNanExp, List.replicate nlimbs (JInt.wrap .u64 0))
    | .inf _ => (specialInfExp, List.replicate nlimbs (JInt.wrap .u64 0))
    | .zero _ => (specialZeroExp,List.replicate nlimbs (JInt.wrap .u64 0))
    | .finite m e =>
      let used := m.natAbs.log2+1
      let shifted := if used > nlimbs*64 then m.natAbs / 2^(used-nlimbs*64)
        else m.natAbs*2^(nlimbs*64-used)
      let limbs := JuliaLean.base.gmp.limbsOfNat shifted
      (JInt.wrap .i64 ((used : Int)+e),limbs ++ List.replicate (nlimbs-limbs.length) (JInt.wrap .u64 0))
  ⟨value,precision,sign,exponent,limbs⟩



structure Flags where
  underflow : Bool := false
  overflow : Bool := false
  divbyzero : Bool := false
  nan : Bool := false
  inexact : Bool := false
  range : Bool := false
  deriving DecidableEq, Repr, Inhabited

def Flags.merge (a b : Flags) : Flags :=
  ⟨a.underflow || b.underflow, a.overflow || b.overflow,
   a.divbyzero || b.divbyzero, a.nan || b.nan,
   a.inexact || b.inexact, a.range || b.range⟩

structure ExponentLimits where
  eminMin : Clong
  eminMax : Clong
  emaxMin : Clong
  emaxMax : Clong
  deriving DecidableEq, Repr

structure Context where
  defaultPrecision : Clong := JInt.wrap .i64 256
  defaultRounding : Mode := .nearest
  scopedPrecision : Option Clong := none
  scopedRounding : Option Mode := none
  emin : Clong
  emax : Clong
  limits : ExponentLimits
  flags : Flags := {}
  faithfulUp : Bool := false
  deriving Repr

structure M (A : Type) where
  run : Context → Jl A × Context

instance : Monad M where
  pure a := ⟨fun state => (.ok a,state)⟩
  bind first next := ⟨fun state =>
    let (result,state) := first.run state
    match result with
    | .error e => (.error e,state)
    | .ok value => (next value).run state⟩

instance : MonadExceptOf JlError M where
  throw e := ⟨fun state => (.error e,state)⟩
  tryCatch action handler := ⟨fun state =>
    let (result,state) := action.run state
    match result with
    | .ok a => (.ok a,state)
    | .error e => (handler e).run state⟩

def readContext : M Context := ⟨fun state => (.ok state,state)⟩
def writeContext (state : Context) : M Unit := ⟨fun _ => (.ok (),state)⟩
def liftJl (result : Jl A) : M A := ⟨fun state => (result,state)⟩

/-- Selected Julia methods for an Integer precision. The ccall argument
conversion and explicit Clong(precision) are distinct user-extensible calls. -/
structure IntegerPrecision (I : Type) where
  lessOne : I → M Bool
  ccallClong : I → M Clong
  clong : I → M Clong

def bitsPrecision (t : IntTy) : IntegerPrecision (JInt t) :=
  { lessOne := fun p => pure (JuliaLean.base.int.lt p (JInt.lit .i64 1))
    ccallClong := fun p => liftJl (JuliaLean.base.int.convert .i64 p)
    clong := fun p => liftJl (JuliaLean.base.int.convert .i64 p) }

/-- Adapter for the existing MPFR callees' mathematical Int precision interfaces. -/
def valuePrecision : IntegerPrecision Int :=
  { lessOne := fun p => pure (decide (p < 1))
    ccallClong := fun p => liftJl (JInt.convert "Int64" .i64 p)
    clong := fun p => liftJl (JInt.convert "Int64" .i64 p) }

def boolPrecision : IntegerPrecision Bool :=
  { lessOne := fun p => pure (JuliaLean.base.int.lt (JuliaLean.base.int.ofBool .i64 p) (JInt.lit .i64 1))
    ccallClong := fun p => pure (JuliaLean.base.int.ofBool .i64 p)
    clong := fun p => pure (JuliaLean.base.int.ofBool .i64 p) }

def bigIntPrecision : IntegerPrecision JuliaLean.base.gmp.BigInt :=
  { lessOne := fun p => pure (JuliaLean.base.int.lt
      (JuliaLean.base.gmp.cmpSigned p (JInt.lit .i64 1)) (JInt.lit .i64 0))
    ccallClong := fun p => liftJl (JuliaLean.base.gmp.convertBits .i64 p)
    clong := fun p => liftJl (JuliaLean.base.gmp.convertBits .i64 p) }

/-- Julia dispatch supplies the selected Integer methods or the rejected
keyword's actual type. No numeric projection of an arbitrary Integer is used. -/
inductive PrecisionKeyword where
  | integer {I : Type} (ops : IntegerPrecision I) (value : I)
  | nonInteger (actualType : String)

inductive PrecisionError where
  | julia (error : JlError)
  | typeError (keyword expected actual : String)
  deriving DecidableEq, Repr

abbrev KeywordM := EStateM PrecisionError Context

def liftMPFR (action : M A) : KeywordM A := fun state =>
  match action.run state with
  | (.ok value,after) => .ok value after
  | (.error error,after) => .error (.julia error) after

/--
Julia source: base/mpfr.jl:154-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function BigFloat(; precision::Integer=_precision_with_base_2(BigFloat))
        precision < 1 && throw(DomainError(precision, "`precision` cannot be less than 1."))
        nb = ccall((:mpfr_custom_get_size,libmpfr), Csize_t, (Clong,), precision)
        nl = (nb + offset_p + sizeof(Limb) - 1) ÷ Core.sizeof(Limb) # align to number of Limb allocations required for this
        d = Memory{Limb}(undef, nl % Int)
        # ccall-based version, inlined below
        #ccall((:mpfr_custom_init,libmpfr), Cvoid, (Ptr{Limb}, Clong), BigFloatData(d), prec) # currently seems to be a no-op in mpfr
        #NAN_KIND = Cint(0)
        #ccall((:mpfr_custom_init_set,libmpfr), Cvoid, (Ref{BigFloat}, Cint, Clong, Ptr{Limb}), z, NAN_KIND, prec, BigFloatData(d))
        p = Base.unsafe_convert(Ptr{Limb}, d)
        GC.@preserve d begin # initialize to +NAN
            unsafe_store!(Ptr{Clong}(p) + offset_prec, Clong(precision))
            unsafe_store!(Ptr{Cint}(p) + offset_sign, one(Cint))
            unsafe_store!(Ptr{Clong}(p) + offset_exp, mpfr_special_exponent_nan)
            unsafe_store!(Ptr{Ptr{Limb}}(p) + offset_d, p + offset_p)
        end
        return new(d)
```
-/
def constructInteger {I : Type} (ops : IntegerPrecision I) (precision : I) : M BigFloat := do
  if ← ops.lessOne precision then throw (.domainError "`precision` cannot be less than 1.")
  let cPrecision ← ops.ccallClong precision
  let _nb := customGetSize cPrecision
  let allocated := pack cPrecision (.nan false)
  let precision ← ops.clong precision
  pure { allocated with prec := precision }




/--
Julia source: base/mpfr.jl:246-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rounding_raw(::Type{BigFloat}) = @something(Base.ScopedValues.get(CURRENT_ROUNDING_MODE), ROUNDING_MODE[])
setrounding_raw(::Type{BigFloat}, r::MPFRRoundingMode) = ROUNDING_MODE[]=r
function setrounding_raw(f::Function, ::Type{BigFloat}, r::MPFRRoundingMode)
    Base.ScopedValues.@with(CURRENT_ROUNDING_MODE => r, f())
end

rounding(::Type{BigFloat}) = convert(RoundingMode, rounding_raw(BigFloat))
setrounding(::Type{BigFloat}, r::RoundingMode) = setrounding_raw(BigFloat, convert(MPFRRoundingMode, r))
setrounding(f::Function, ::Type{BigFloat}, r::RoundingMode) =
    setrounding_raw(f, BigFloat, convert(MPFRRoundingMode, r))
```
-/
def roundingRaw (state : Context) : Mode := state.scopedRounding.getD state.defaultRounding
def setroundingRaw (r : Mode) : M Mode := do
  let state ← readContext
  writeContext { state with defaultRounding := r }
  pure r

def withRoundingRaw (action : M A) (r : Mode) : M A := ⟨fun state =>
  let previous := state.scopedRounding
  let (result,after) := action.run { state with scopedRounding := some r }
  (result,{ after with scopedRounding := previous })⟩

def rounding : M RoundingMode := do liftJl (toPublic (roundingRaw (← readContext)))
def setrounding (r : RoundingMode) : M Mode := do setroundingRaw (← liftJl (toMPFR r))
def withRounding (action : M A) (r : RoundingMode) : M A := do
  withRoundingRaw action (← liftJl (toMPFR r))

/--
Julia source: base/mpfr.jl:1050-1051 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_precision_with_base_2(::Type{BigFloat}) =
    Int(@something(Base.ScopedValues.get(CURRENT_PRECISION), DEFAULT_PRECISION[])) # default precision of the type BigFloat itself
```
-/
def precisionType (state : Context) : Clong := state.scopedPrecision.getD state.defaultPrecision

def defaultPrecisionKeyword (state : Context) : PrecisionKeyword :=
  .integer (bitsPrecision .i64) (precisionType state)

def fresh : M BigFloat := do constructInteger (bitsPrecision .i64) (precisionType (← readContext))

structure PrimitiveResult where
  value : BigFloat
  ternary : Cint
  flags : Flags
  deriving Repr

def cmpRat (a : FP) (n : Int) (d : Nat) : Int :=
  match a with
  | .nan _ => 0
  | .inf s => if s then -1 else 1
  | _ =>
    let (m,e) := a.toRat
    JuliaLean.base.gmp.sgn (m*(d : Int)-n*(e : Int))

def effectiveMode (state : Context) (mode : Mode) : Mode :=
  if mode = .faithful then (if state.faithfulUp then .up else .down) else mode

def increment (mode : Mode) (negative : Bool) (q remainder denominator : Nat) : Bool :=
  match mode with
  | .nearest => decide (2*remainder > denominator) ||
      (decide (2*remainder = denominator) && decide (q%2 = 1))
  | .toZero => false
  | .up => decide (remainder ≠ 0) && !negative
  | .down => decide (remainder ≠ 0) && negative
  | .fromZero => decide (remainder ≠ 0)
  | .faithful => false

/-- MPFR manual §§4.4, 4.6: correctly rounded rational, including exponent
range, underflow after rounding, halfway underflow to zero and sticky flags.
https://www.mpfr.org/mpfr-current/mpfr.html#Rounding -/
def roundRat (state : Context) (precision : Clong) (mode : Mode)
    (n : Int) (d : Nat) (zeroSign : Bool := false) : PrimitiveResult :=
  let p := precision.val.toNat
  let mode := effectiveMode state mode
  if n = 0 then ⟨pack precision (.zero zeroSign),JInt.wrap .i32 0,{}⟩ else
    let negative := decide (n < 0)
    let a := n.natAbs
    let exponent := Fl.floorLog2Rat a d + 1
    let scale := exponent-(p : Int)
    let numerator := if scale ≥ 0 then a else a*2^(-scale).toNat
    let denominator := if scale ≥ 0 then d*2^scale.toNat else d
    let q := numerator / denominator
    let remainder := numerator % denominator
    let up := increment mode negative q remainder denominator
    let q := q + if up then 1 else 0
    let roundedExp := scale+(q.log2+1 : Nat)
    let regular := FP.finite (if negative then -(q : Int) else q) scale
    let (value,underflow,overflow) :=
      if roundedExp > state.emax.val then
        let toInf := mode = .nearest || roundsAway mode negative
        (if toInf then FP.inf negative else
          FP.finite (if negative then -((2^p-1 : Nat) : Int) else (2^p-1 : Nat))
            (state.emax.val-(p : Int)),false,true)
      else if roundedExp < state.emin.val then
        let halfScale := state.emin.val-2
        let aboveHalf := if halfScale ≥ 0 then a > d*2^halfScale.toNat
          else a*2^(-halfScale).toNat > d
        let away := if mode = .nearest then aboveHalf else roundsAway mode negative
        (if away then FP.finite (if negative then -1 else 1) (state.emin.val-1)
          else FP.zero negative,true,false)
      else (regular,false,false)
    let ternary := cmpRat value n d
    ⟨pack precision value,JInt.wrap .i32 ternary,
     { underflow := underflow, overflow := overflow, inexact := decide (ternary ≠ 0) }⟩

def specialResult (precision : Clong) (value : FP) (flags : Flags := {}) : PrimitiveResult :=
  ⟨pack precision value,JInt.wrap .i32 0,flags⟩

def applyPrimitive (result : PrimitiveResult) : M BigFloat := do
  let state ← readContext
  writeContext { state with flags := state.flags.merge result.flags }
  pure result.value

/-- MPFR manual §5.2 `mpfr_set`, `mpfr_set_si/ui/z/d`: correct rounding
of the exact input at the destination precision. NaNs raise the NaN flag.
https://www.mpfr.org/mpfr-current/mpfr.html#Assignment-Functions -/
def setPrimitive (state : Context) (precision : Clong) (value : FP) (mode : Mode) : PrimitiveResult :=
  match value with
  | .nan _ => specialResult precision value { nan := true }
  | .inf _ | .zero _ => specialResult precision value
  | .finite _ _ => let (n,d) := value.toRat; roundRat state precision mode n d

def ieeeValue {T : FTy} (x : FV T) : FP :=
  if x.isnan then .nan x.signbit else if x.isinf then .inf x.signbit
  else if x.iszero then .zero x.signbit else
    let (m,e,s) := decompose x
    .finite (m.val*s.val) e.val

def intValue (n : Int) : FP := if n = 0 then .zero false else .finite n 0


/--
Julia source: base/mpfr.jl:302-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BigFloat(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))
    if precision == _precision_with_base_2(x)
        return x
    else
        z = BigFloat(;precision=precision)
        ccall((:mpfr_set, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode),
              z, x, r)
        return z
    end
end

function _duplicate(x::BigFloat)
    z = BigFloat(;precision=_precision_with_base_2(x))
    ccall((:mpfr_set, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Int32), z, x, 0)
    return z
end
```
-/
def fromBigFloat (x : BigFloat) (r : Mode) (precision : Int) : M BigFloat := do
  if precision = x.prec.val then return x
  let z ← constructInteger valuePrecision precision
  applyPrimitive (setPrimitive (← readContext) z.prec x.value r)

def duplicate (x : BigFloat) : M BigFloat := do
  let z ← constructInteger (bitsPrecision .i64) x.prec
  applyPrimitive (setPrimitive (← readContext) z.prec x.value .nearest)

/--
Julia source: base/mpfr.jl:320-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (fJ, fC) in ((:si,:Clong), (:ui,:Culong))
    @eval begin
        function BigFloat(x::($fC), r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))
            z = BigFloat(;precision=precision)
            ccall(($(string(:mpfr_set_,fJ)), libmpfr), Int32, (Ref{BigFloat}, $fC, MPFRRoundingMode), z, x, r)
            return z
        end
    end
end
```
-/
def fromLong {t : IntTy} (x : JInt t) (r : Mode) (precision : Int) : M BigFloat := do
  let z ← constructInteger valuePrecision precision
  applyPrimitive (setPrimitive (← readContext) z.prec (intValue x.val) r)

/--
Julia source: base/mpfr.jl:374-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BigFloat(x::BigInt, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))
    z = BigFloat(;precision=precision)
    ccall((:mpfr_set_z, libmpfr), Int32, (Ref{BigFloat}, Ref{BigInt}, MPFRRoundingMode), z, x, r)
    return z
end

BigFloat(x::Integer; precision::Integer=_precision_with_base_2(BigFloat)) =
    BigFloat(BigInt(x)::BigInt, rounding_raw(BigFloat); precision=precision)
BigFloat(x::Integer, r::MPFRRoundingMode; precision::Integer=_precision_with_base_2(BigFloat)) =
    BigFloat(BigInt(x)::BigInt, r; precision=precision)

BigFloat(x::Union{Bool,Int8,Int16,Int32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat)) =
    BigFloat(convert(Clong, x), r; precision=precision)
BigFloat(x::Union{UInt8,UInt16,UInt32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat)) =
    BigFloat(convert(Culong, x), r; precision=precision)

BigFloat(x::Union{Float16,Float32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat)) =
    BigFloat(Float64(x), r; precision=precision)
```
-/
def fromBigInt (x : BigInt) (r : Mode) (precision : Int) : M BigFloat := do
  let z ← constructInteger valuePrecision precision
  applyPrimitive (setPrimitive (← readContext) z.prec (intValue x.val) r)

def fromInteger {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : I) (r : Mode) (precision : Int) : M BigFloat :=
  fromBigInt (JuliaLean.base.gmp.fromInteger ops x) r precision

def fromSmallSigned {t : IntTy} (x : JInt t) (r : Mode) (precision : Int) : M BigFloat := do
  let x ← liftJl (JInt.convert "Int64" .i64 x.val)
  fromLong x r precision

def fromSmallUnsigned {t : IntTy} (x : JInt t) (r : Mode) (precision : Int) : M BigFloat := do
  let x ← liftJl (JInt.convert "UInt64" .u64 x.val)
  fromLong x r precision

inductive Exact where
  | nan (negative : Bool)
  | inf (negative : Bool)
  | finite (num : Int) (den : Nat) (zeroSign : Bool)
  deriving Repr, DecidableEq

structure Operand where
  value : FP
  unsignedZero : Bool := false
  deriving Repr

def Operand.ofInt (n : Int) : Operand := ⟨intValue n,true⟩
def Operand.exact (x : Operand) : Exact :=
  match x.value with
  | .nan s => .nan s
  | .inf s => .inf s
  | .zero s => .finite 0 1 s
  | .finite _ _ => let (n,d) := x.value.toRat; .finite n d false

def Exact.signbit : Exact → Bool
  | .nan s | .inf s => s
  | .finite n _ zeroSign => if n = 0 then zeroSign else decide (n < 0)

def Exact.neg : Exact → Exact
  | .nan s => .nan (!s)
  | .inf s => .inf (!s)
  | .finite n d s => .finite (-n) d (!s)

inductive BinaryOp where | add | sub | mul | div
  deriving DecidableEq, Repr

/-- MPFR manual §§4.5, 5.5: exact arithmetic and signed-zero rules before
rounding. `unsignedZero` distinguishes integer zero in mixed-operand calls.
https://www.mpfr.org/mpfr-current/mpfr.html#Arithmetic-Functions -/
def exactArithmetic (mode : Mode) (op : BinaryOp) (x y : Exact)
    (unsignedX unsignedY : Bool := false) : Exact :=
  let y := if op = .sub then y.neg else y
  match x,y with
  | .nan s, _ => .nan s
  | _, .nan s => .nan s
  | .inf sx, .inf sy =>
    if op = .mul then .inf (sx != sy)
    else if op = .div ∨ sx ≠ sy then .nan false else .inf sx
  | .inf sx, .finite n _ sy =>
    if op = .add ∨ op = .sub then .inf sx
    else if op = .mul ∧ n = 0 then .nan false
    else .inf (sx != (if n = 0 then sy else decide (n < 0)))
  | .finite n _ sx, .inf sy =>
    if op = .add ∨ op = .sub then .inf sy
    else if op = .mul then
      if n = 0 then .nan false else .inf (decide (n < 0) != sy)
    else .finite 0 1 ((if n = 0 then sx else decide (n < 0)) != sy)
  | .finite a b sa, .finite c d sc =>
    let sa := if a = 0 then sa else decide (a < 0)
    let sc := if c = 0 then sc else decide (c < 0)
    match op with
    | .add | .sub =>
      let n := a*(d : Int)+c*(b : Int)
      let zeroSign := if a = 0 ∧ c = 0 then
        if unsignedX then sc else if unsignedY then sa else if sa == sc then sa else mode == .down
        else mode == .down
      .finite n (b*d) zeroSign
    | .mul => .finite (a*c) (b*d) (sa != sc)
    | .div =>
      if c = 0 then (if a = 0 then .nan false else .inf (sa != sc))
      else .finite (a*(d : Int)*JuliaLean.base.gmp.sgn c) (b*c.natAbs) (sa != sc)

def roundExact (state : Context) (precision : Clong) (mode : Mode)
    (exact : Exact) (divbyzero : Bool := false) : PrimitiveResult :=
  let result := match exact with
    | .nan s => specialResult precision (.nan s) { nan := true }
    | .inf s => specialResult precision (.inf s)
    | .finite n d sign => roundRat state precision mode n d sign
  { result with flags := { result.flags with divbyzero := divbyzero } }

/-- MPFR manual §5.5: `mpfr_add/sub/mul/div` and their `_si`, `_ui`, `_z`,
`_d` variants share exact inputs and one final rounding.
https://www.mpfr.org/mpfr-current/mpfr.html#Arithmetic-Functions -/
def binaryPrimitive (state : Context) (precision : Clong) (mode : Mode)
    (op : BinaryOp) (x y : Operand) : PrimitiveResult :=
  let exact := exactArithmetic (effectiveMode state mode) op x.exact y.exact x.unsignedZero y.unsignedZero
  let divbyzero := op == .div && y.value.iszero && !x.value.isinf &&
    !x.value.isnan && !x.value.iszero
  roundExact state precision mode exact divbyzero

def binaryCall (op : BinaryOp) (x y : Operand) (mode : Mode) : M BigFloat := do
  let z ← fresh
  applyPrimitive (binaryPrimitive (← readContext) z.prec mode op x y)


/--
Julia source: base/mpfr.jl:574-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (fJ, fC) in ((:+,:add), (:*,:mul))
    @eval begin
        # BigFloat
        function ($fJ)(x::BigFloat, y::BigFloat)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC)),libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
            return z
        end

        # Unsigned Integer
        function ($fJ)(x::BigFloat, c::CulongMax)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC,:_ui)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Culong, MPFRRoundingMode), z, x, c, rounding_raw(BigFloat))
            return z
        end
        ($fJ)(c::CulongMax, x::BigFloat) = ($fJ)(x,c)

        # Signed Integer
        function ($fJ)(x::BigFloat, c::ClongMax)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC,:_si)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Clong, MPFRRoundingMode), z, x, c, rounding_raw(BigFloat))
            return z
        end
        ($fJ)(c::ClongMax, x::BigFloat) = ($fJ)(x,c)

        # Float32/Float64
        function ($fJ)(x::BigFloat, c::CdoubleMax)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC,:_d)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Cdouble, MPFRRoundingMode), z, x, c, rounding_raw(BigFloat))
            return z
        end
        ($fJ)(c::CdoubleMax, x::BigFloat) = ($fJ)(x,c)

        # BigInt
        function ($fJ)(x::BigFloat, c::BigInt)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC,:_z)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigInt}, MPFRRoundingMode), z, x, c, rounding_raw(BigFloat))
            return z
        end
        ($fJ)(c::BigInt, x::BigFloat) = ($fJ)(x,c)
    end
end

for (fJ, fC) in ((:-,:sub), (:/,:div))
    @eval begin
        # BigFloat
        function ($fJ)(x::BigFloat, y::BigFloat)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC)),libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
            return z
        end

        # Unsigned Int
        function ($fJ)(x::BigFloat, c::CulongMax)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC,:_ui)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Culong, MPFRRoundingMode), z, x, c, rounding_raw(BigFloat))
            return z
        end
        function ($fJ)(c::CulongMax, x::BigFloat)
            z = BigFloat()
            ccall(($(string(:mpfr_,:ui_,fC)), libmpfr), Int32, (Ref{BigFloat}, Culong, Ref{BigFloat}, MPFRRoundingMode), z, c, x, rounding_raw(BigFloat))
            return z
        end

        # Signed Integer
        function ($fJ)(x::BigFloat, c::ClongMax)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC,:_si)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Clong, MPFRRoundingMode), z, x, c, rounding_raw(BigFloat))
            return z
        end
        function ($fJ)(c::ClongMax, x::BigFloat)
            z = BigFloat()
            ccall(($(string(:mpfr_,:si_,fC)), libmpfr), Int32, (Ref{BigFloat}, Clong, Ref{BigFloat}, MPFRRoundingMode), z, c, x, rounding_raw(BigFloat))
            return z
        end

        # Float32/Float64
        function ($fJ)(x::BigFloat, c::CdoubleMax)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC,:_d)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Cdouble, MPFRRoundingMode), z, x, c, rounding_raw(BigFloat))
            return z
        end
        function ($fJ)(c::CdoubleMax, x::BigFloat)
            z = BigFloat()
            ccall(($(string(:mpfr_,:d_,fC)), libmpfr), Int32, (Ref{BigFloat}, Cdouble, Ref{BigFloat}, MPFRRoundingMode), z, c, x, rounding_raw(BigFloat))
            return z
        end

        # BigInt
        function ($fJ)(x::BigFloat, c::BigInt)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC,:_z)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigInt}, MPFRRoundingMode), z, x, c, rounding_raw(BigFloat))
            return z
        end
        # no :mpfr_z_div function
    end
end
```
-/
def arithmetic (op : BinaryOp) (x y : BigFloat) : M BigFloat := do
  binaryCall op ⟨x.value,false⟩ ⟨y.value,false⟩ (roundingRaw (← readContext))

def arithmeticInteger {t : IntTy} (op : BinaryOp) (x : BigFloat) (c : JInt t) : M BigFloat := do
  binaryCall op ⟨x.value,false⟩ (.ofInt c.val) (roundingRaw (← readContext))
def integerArithmetic {t : IntTy} (op : BinaryOp) (c : JInt t) (x : BigFloat) : M BigFloat := do
  if op = .add ∨ op = .mul then arithmeticInteger op x c
  else binaryCall op (.ofInt c.val) ⟨x.value,false⟩ (roundingRaw (← readContext))

def arithmeticIEEE {T : FTy} (op : BinaryOp) (x : BigFloat) (c : FV T) : M BigFloat := do
  binaryCall op ⟨x.value,false⟩ ⟨ieeeValue (convertFloat .f64 c),false⟩ (roundingRaw (← readContext))
def ieeeArithmetic {T : FTy} (op : BinaryOp) (c : FV T) (x : BigFloat) : M BigFloat := do
  if op = .add ∨ op = .mul then arithmeticIEEE op x c
  else binaryCall op ⟨ieeeValue (convertFloat .f64 c),false⟩ ⟨x.value,false⟩ (roundingRaw (← readContext))

def arithmeticBigInt (op : BinaryOp) (x : BigFloat) (c : BigInt) : M BigFloat := do
  binaryCall op ⟨x.value,false⟩ (.ofInt c.val) (roundingRaw (← readContext))
def bigIntCommutative (op : BinaryOp) (c : BigInt) (x : BigFloat) : M BigFloat :=
  arithmeticBigInt op x c

/--
Julia source: base/mpfr.jl:672-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -(c::BigInt, x::BigFloat)
    z = BigFloat()
    ccall((:mpfr_z_sub, libmpfr), Int32, (Ref{BigFloat}, Ref{BigInt}, Ref{BigFloat}, MPFRRoundingMode), z, c, x, rounding_raw(BigFloat))
    return z
end

inv(x::BigFloat) = one(Clong) / x # faster than fallback one(x)/x

function fma(x::BigFloat, y::BigFloat, z::BigFloat)
    r = BigFloat()
    ccall(("mpfr_fma",libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), r, x, y, z, rounding_raw(BigFloat))
    return r
end

muladd(x::BigFloat, y::BigFloat, z::BigFloat) = fma(x, y, z)
```
-/
def bigIntSub (c : BigInt) (x : BigFloat) : M BigFloat := do
  binaryCall .sub (.ofInt c.val) ⟨x.value,false⟩ (roundingRaw (← readContext))
def inv (x : BigFloat) : M BigFloat := integerArithmetic .div (JInt.wrap .i64 1) x

/-- MPFR manual §5.5 `mpfr_fma`: exact product plus addend, rounded once.
https://www.mpfr.org/mpfr-current/mpfr.html#Arithmetic-Functions -/
def fmaPrimitive (state : Context) (precision : Clong) (mode : Mode)
    (x y z : BigFloat) : PrimitiveResult :=
  let effective := effectiveMode state mode
  let product := exactArithmetic effective .mul (Operand.exact ⟨x.value,false⟩) (Operand.exact ⟨y.value,false⟩)
  let result := exactArithmetic effective .add product (Operand.exact ⟨z.value,false⟩)
  roundExact state precision mode result

def fma (x y z : BigFloat) : M BigFloat := do
  let output ← fresh
  let state ← readContext
  applyPrimitive (fmaPrimitive state output.prec (roundingRaw state) x y z)
def muladd (x y z : BigFloat) := fma x y z

/-- MPFR manual §5.10 `mpfr_roundeven/ceil/floor/trunc/round` use no
intermediate integer rounding at a precision coarser than the integer grid.
https://www.mpfr.org/mpfr-current/mpfr.html#Integer-and-Remainder-Related-Functions -/
def integerRoundPrimitive (state : Context) (precision : Clong) (mode : Mode)
    (tiesAway : Bool) (x : BigFloat) : PrimitiveResult :=
  match x.value with
  | .nan s => specialResult precision (.nan s) { nan := true }
  | .inf s => specialResult precision (.inf s)
  | .zero s => specialResult precision (.zero s)
  | .finite _ _ =>
    let (n,d) := x.value.toRat
    let exponent := Fl.floorLog2Rat n.natAbs d + 1
    let step := max 0 (exponent-precision.val)
    let denominator := d*2^step.toNat
    let q := n.natAbs / denominator
    let remainder := n.natAbs % denominator
    let negative := decide (n < 0)
    let up := if tiesAway && mode == .nearest then decide (2*remainder ≥ denominator)
      else increment (effectiveMode state mode) negative q remainder denominator
    let magnitude := (q + if up then 1 else 0)*2^step.toNat
    let result := roundRat state precision .nearest
      (if negative then -(magnitude : Int) else magnitude) 1 negative
    let comparison := cmpRat result.value.value n d
    { result with
      ternary := JInt.wrap .i32 (comparison * if n % (d : Int) = 0 then 1 else 2)
      flags := { result.flags with inexact := decide (comparison ≠ 0) } }

def truncateOutput (x : BigFloat) : M BigFloat := do
  applyPrimitive (integerRoundPrimitive (← readContext) x.prec .toZero false x)


/--
Julia source: base/mpfr.jl:690-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::BigFloat, y::BigFloat)
    z = BigFloat()
    ccall((:mpfr_div,libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, y, RoundToZero)
    ccall((:mpfr_trunc, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, z)
    return z
end

# Unsigned Int
function div(x::BigFloat, c::CulongMax)
    z = BigFloat()
    ccall((:mpfr_div_ui, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Culong, MPFRRoundingMode), z, x, c, RoundToZero)
    ccall((:mpfr_trunc, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, z)
    return z
end
function div(c::CulongMax, x::BigFloat)
    z = BigFloat()
    ccall((:mpfr_ui_div, libmpfr), Int32, (Ref{BigFloat}, Culong, Ref{BigFloat}, MPFRRoundingMode), z, c, x, RoundToZero)
    ccall((:mpfr_trunc, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, z)
    return z
end

# Signed Integer
function div(x::BigFloat, c::ClongMax)
    z = BigFloat()
    ccall((:mpfr_div_si, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Clong, MPFRRoundingMode), z, x, c, RoundToZero)
    ccall((:mpfr_trunc, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, z)
    return z
end
function div(c::ClongMax, x::BigFloat)
    z = BigFloat()
    ccall((:mpfr_si_div, libmpfr), Int32, (Ref{BigFloat}, Clong, Ref{BigFloat}, MPFRRoundingMode), z, c, x, RoundToZero)
    ccall((:mpfr_trunc, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, z)
    return z
end

# Float32/Float64
function div(x::BigFloat, c::CdoubleMax)
    z = BigFloat()
    ccall((:mpfr_div_d, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Cdouble, MPFRRoundingMode), z, x, c, RoundToZero)
    ccall((:mpfr_trunc, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, z)
    return z
end
function div(c::CdoubleMax, x::BigFloat)
    z = BigFloat()
    ccall((:mpfr_d_div, libmpfr), Int32, (Ref{BigFloat}, Cdouble, Ref{BigFloat}, MPFRRoundingMode), z, c, x, RoundToZero)
    ccall((:mpfr_trunc, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, z)
    return z
end

# BigInt
function div(x::BigFloat, c::BigInt)
    z = BigFloat()
    ccall((:mpfr_div_z, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigInt}, MPFRRoundingMode), z, x, c, RoundToZero)
    ccall((:mpfr_trunc, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, z)
    return z
end
```
-/
def div (x y : BigFloat) : M BigFloat := do
  let z ← binaryCall .div ⟨x.value,false⟩ ⟨y.value,false⟩ .toZero
  truncateOutput z

def divInteger {t : IntTy} (x : BigFloat) (c : JInt t) : M BigFloat := do
  let z ← binaryCall .div ⟨x.value,false⟩ (.ofInt c.val) .toZero
  truncateOutput z
def integerDiv {t : IntTy} (c : JInt t) (x : BigFloat) : M BigFloat := do
  let z ← binaryCall .div (.ofInt c.val) ⟨x.value,false⟩ .toZero
  truncateOutput z

def divIEEE {T : FTy} (x : BigFloat) (c : FV T) : M BigFloat := do
  let z ← binaryCall .div ⟨x.value,false⟩ ⟨ieeeValue (convertFloat .f64 c),false⟩ .toZero
  truncateOutput z
def ieeeDiv {T : FTy} (c : FV T) (x : BigFloat) : M BigFloat := do
  let z ← binaryCall .div ⟨ieeeValue (convertFloat .f64 c),false⟩ ⟨x.value,false⟩ .toZero
  truncateOutput z

def divBigInt (x : BigFloat) (c : BigInt) : M BigFloat := do
  let z ← binaryCall .div ⟨x.value,false⟩ (.ofInt c.val) .toZero
  truncateOutput z

/--
Julia source: base/mpfr.jl:749-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (fJ, fC) in ((:+, :add), (:*, :mul))
    @eval begin
        function ($fJ)(a::BigFloat, b::BigFloat, c::BigFloat)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, a, b, rounding_raw(BigFloat))
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, z, c, rounding_raw(BigFloat))
            return z
        end
        function ($fJ)(a::BigFloat, b::BigFloat, c::BigFloat, d::BigFloat)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, a, b, rounding_raw(BigFloat))
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, z, c, rounding_raw(BigFloat))
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, z, d, rounding_raw(BigFloat))
            return z
        end
        function ($fJ)(a::BigFloat, b::BigFloat, c::BigFloat, d::BigFloat, e::BigFloat)
            z = BigFloat()
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, a, b, rounding_raw(BigFloat))
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, z, c, rounding_raw(BigFloat))
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, z, d, rounding_raw(BigFloat))
            ccall(($(string(:mpfr_,fC)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, z, e, rounding_raw(BigFloat))
            return z
        end
    end
end
```
-/
def commutative3 (op : BinaryOp) (a b c : BigFloat) : M BigFloat := do
  let z ← arithmetic op a b
  let state ← readContext
  applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) op ⟨z.value,false⟩ ⟨c.value,false⟩)
def commutative4 (op : BinaryOp) (a b c d : BigFloat) : M BigFloat := do
  let z ← commutative3 op a b c
  let state ← readContext
  applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) op ⟨z.value,false⟩ ⟨d.value,false⟩)
def commutative5 (op : BinaryOp) (a b c d e : BigFloat) : M BigFloat := do
  let z ← commutative4 op a b c d
  let state ← readContext
  applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) op ⟨z.value,false⟩ ⟨e.value,false⟩)

/--
Julia source: base/mpfr.jl:775-779 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -(x::BigFloat)
    z = BigFloat()
    ccall((:mpfr_neg, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, rounding_raw(BigFloat))
    return z
end
```
-/
def neg (x : BigFloat) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive (setPrimitive state z.prec x.value.neg (roundingRaw state))

/--
Julia source: base/mpfr.jl:1129-1146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isinf(x::BigFloat)
    return x.exp == mpfr_special_exponent_inf
end

function isnan(x::BigFloat)
    return x.exp == mpfr_special_exponent_nan
end

issubnormal(x::BigFloat) = false

isfinite(x::BigFloat) = !isinf(x) && !isnan(x)

iszero(x::BigFloat) = x.exp == mpfr_special_exponent_zero
isone(x::BigFloat) = x == Clong(1)

# In theory, `!iszero(x) && !isnan(x)` should be the same as `x.exp > mpfr_special_exponent_nan`, but this is safer.
ispositive(x::BigFloat) = !signbit(x) && !iszero(x) && !isnan(x)
isnegative(x::BigFloat) = signbit(x) && !iszero(x) && !isnan(x)
```
-/
def isinf (x : BigFloat) : Bool := x.exp == specialInfExp
def isnan (x : BigFloat) : Bool := x.exp == specialNanExp
def issubnormal (_x : BigFloat) : Bool := false
def isfinite (x : BigFloat) : Bool := !isinf x && !isnan x
def iszero (x : BigFloat) : Bool := x.exp == specialZeroExp
def ispositive (x : BigFloat) : Bool := decide (x.sign.val ≥ 0) && !iszero x && !isnan x
def isnegative (x : BigFloat) : Bool := decide (x.sign.val < 0) && !iszero x && !isnan x

/--
Julia source: base/mpfr.jl:1033-1033 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::BigFloat) = signbit(x.sign)
```
-/
def signbit (x : BigFloat) : Bool := decide (x.sign.val < 0)

/--
MPFR manual §5.10 `mpfr_integer_p`: https://www.mpfr.org/mpfr-current/mpfr.html#Integer-and-Remainder-Related-Functions

Julia source: base/mpfr.jl:1111-1113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isinteger(x::BigFloat)
    return ccall((:mpfr_integer_p, libmpfr), Int32, (Ref{BigFloat},), x) != 0
end
```
-/
def isinteger (x : BigFloat) : Bool :=
  if !isfinite x then false else
    let (n,d) := x.value.toRat
    decide (n % (d : Int) = 0)

/--
MPFR manual §5.12 `mpfr_get_prec`: returns the stored precision: https://www.mpfr.org/mpfr-current/mpfr.html#Miscellaneous-Functions

Julia source: base/mpfr.jl:1041-1044 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _precision_with_base_2(x::BigFloat)  # precision of an object of type BigFloat
    return ccall((:mpfr_get_prec, libmpfr), Clong, (Ref{BigFloat},), x)
end
precision(x::BigFloat; base::Integer=2) = _precision(x, base)
```
-/
def precisionValue (x : BigFloat) : Clong := x.prec
def precision {B : Type} (precision : BigFloat → B → Jl Clong) (x : BigFloat) (base : B) :=
  precision x base

/--
Julia source: base/mpfr.jl:330-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BigFloat(x::Float64, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))
    z = BigFloat(;precision)
    # punt on the hard case where we might have to deal with rounding
    # we could use this path in all cases, but mpfr_set_d has a lot of overhead.
    if precision <= Base.significand_bits(Float64)
        ccall((:mpfr_set_d, libmpfr), Int32, (Ref{BigFloat}, Float64, MPFRRoundingMode), z, x, r)
        if isnan(x) && signbit(x) != signbit(z)
            z.sign = -z.sign
        end
        return z
    end
    z.sign = 1-2*signbit(x)
    if iszero(x) || !isfinite(x)
        if isinf(x)
            z.exp = mpfr_special_exponent_inf
        elseif isnan(x)
            z.exp = mpfr_special_exponent_nan
        else
            z.exp = mpfr_special_exponent_zero
        end
        return z
    end
    z.exp = 1 + exponent(x)
    # BigFloat doesn't have an implicit bit
    val = reinterpret(UInt64, significand(x))<<11 | typemin(Int64)
    nlimbs = (precision + 8*Core.sizeof(Limb) - 1) ÷ (8*Core.sizeof(Limb))

    # Limb is a CLong which is a UInt32 on windows (thank M$) which makes this more complicated and slower.
    zd = z.d
    if Limb === UInt64
        for i in 1:nlimbs-1
            @inbounds setindex!(zd, 0x0, i)
        end
        @inbounds setindex!(zd, val, nlimbs)
    else
        for i in 1:nlimbs-2
            @inbounds setindex!(zd, 0x0, i)
        end
        @inbounds setindex!(zd, val % UInt32, nlimbs-1)
        @inbounds setindex!(zd, (val >> 32) % UInt32, nlimbs)
    end
    z
end
```
-/
def fromFloat64 (x : FV .f64) (r : Mode) (precision : Int) : M BigFloat := do
  let z ← constructInteger valuePrecision precision
  if precision ≤ 52 then
    let z ← applyPrimitive (setPrimitive (← readContext) z.prec (ieeeValue x) r)
    if x.isnan && (x.signbit != z.value.signbit) then
      return pack z.prec (.nan x.signbit)
    return z
  return pack z.prec (ieeeValue x)

/--
Julia source: base/mpfr.jl:390-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BigFloat(x::Union{Float16,Float32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat)) =
    BigFloat(Float64(x), r; precision=precision)
```
-/
def fromSmallFloat {T : FTy} (x : FV T) (r : Mode) (precision : Int) : M BigFloat :=
  fromFloat64 (convertFloat .f64 x) r precision

/--
Julia source: base/mpfr.jl:401-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _opposite_round(r::MPFRRoundingMode)
    r == MPFRRoundUp && return MPFRRoundDown
    r == MPFRRoundDown && return MPFRRoundUp
    return r
end
```
-/
def oppositeRound (r : Mode) : Mode :=
  if r = .up then .down else if r = .down then .up else r

/--
Julia source: base/mpfr.jl:393-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BigFloat(x::Rational, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))
    r_den = _opposite_round(r)
    setprecision(BigFloat, precision) do
        setrounding_raw(BigFloat, r) do
            BigFloat(numerator(x))::BigFloat / BigFloat(denominator(x), r_den)::BigFloat
        end
    end
end
```
-/
def fromRational {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : JuliaLean.base.rational.Rational I) (r : Mode) (precision : Int) : M BigFloat := do
  let rden := oppositeRound r
  let previous := (← readContext).scopedPrecision
  let p ← liftJl (JInt.convert "Int64" .i64 precision)
  let state ← readContext
  writeContext { state with scopedPrecision := some p }
  let action : M BigFloat := withRoundingRaw (do
    let n ← fromInteger ops x.num r precision
    let d ← fromInteger ops x.den rden precision
    arithmetic .div n d) r
  let result ← tryCatch (do let value ← action; pure (.ok value)) (fun error => pure (.error error))
  let after ← readContext
  writeContext { after with scopedPrecision := previous }
  liftJl result

def roundIntegerRat (mode : Mode) (n : Int) (d : Nat) (tiesAway : Bool := false) : Int :=
  let q := n.natAbs / d
  let remainder := n.natAbs % d
  let negative := decide (n < 0)
  let up := if tiesAway && mode == .nearest then decide (2*remainder ≥ d)
    else increment mode negative q remainder d
  let q := q + if up then 1 else 0
  if negative then -(q : Int) else q

structure IntegerResult where
  value : Int
  flags : Flags
  deriving Repr

/-- MPFR manual §5.4 `mpfr_get_z`: nonfinite inputs produce zero and raise
range error; finite inputs round to an unbounded integer and raise inexact
when changed. https://www.mpfr.org/mpfr-current/mpfr.html#Conversion-Functions -/
def getZPrimitive (state : Context) (x : BigFloat) (mode : Mode) : IntegerResult :=
  if x.value.isnan || x.value.isinf then ⟨0,{ range := true }⟩ else
    let (n,d) := x.value.toRat
    let value := roundIntegerRat (effectiveMode state mode) n d
    ⟨value,{ inexact := decide (value*(d : Int) ≠ n) }⟩

/-- MPFR manual §5.4 `mpfr_get_sj/uj`: saturation on overflow, zero on NaN,
and range error in either case.
https://www.mpfr.org/mpfr-current/mpfr.html#Conversion-Functions -/
def getCIntegerPrimitive (state : Context) (t : IntTy) (x : BigFloat) (mode : Mode) : IntegerResult :=
  if x.value.isnan then ⟨0,{ range := true }⟩
  else if x.value.isinf then
    ⟨if x.value.signbit then t.min else t.max,{ range := true }⟩
  else
    let result := getZPrimitive state x mode
    if result.value < t.min then ⟨t.min,{ range := true }⟩
    else if result.value > t.max then ⟨t.max,{ range := true }⟩
    else result

def applyIntegerPrimitive (result : IntegerResult) : M Int := do
  let state ← readContext
  writeContext { state with flags := state.flags.merge result.flags }
  pure result.value


/--
Julia source: base/mpfr.jl:430-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _unchecked_cast(::Type{Int64}, x::BigFloat, r::MPFRRoundingMode)
    ccall((:__gmpfr_mpfr_get_sj,libmpfr), Cintmax_t, (Ref{BigFloat}, MPFRRoundingMode), x, r)
end

function _unchecked_cast(::Type{UInt64}, x::BigFloat, r::MPFRRoundingMode)
    ccall((:__gmpfr_mpfr_get_uj,libmpfr), Cuintmax_t, (Ref{BigFloat}, MPFRRoundingMode), x, r)
end

function _unchecked_cast(::Type{BigInt}, x::BigFloat, r::MPFRRoundingMode)
    z = BigInt()
    ccall((:mpfr_get_z, libmpfr), Int32, (Ref{BigInt}, Ref{BigFloat}, MPFRRoundingMode), z, x, r)
    return z
end

function _unchecked_cast(::Type{T}, x::BigFloat, r::MPFRRoundingMode) where T<:Union{Signed, Unsigned}
    CT = T <: Signed ? Int64 : UInt64
    typemax(T) < typemax(CT) ? _unchecked_cast(CT, x, r) : _unchecked_cast(BigInt, x, r)
end
```
-/
def uncheckedCastBits (t : IntTy) (x : BigFloat) (r : Mode) : M Int := do
  let state ← readContext
  if t = .i64 ∨ t = .u64 then
    applyIntegerPrimitive (getCIntegerPrimitive state t x r)
  else
    let ct := if t.signed then IntTy.i64 else IntTy.u64
    if t.max < ct.max then applyIntegerPrimitive (getCIntegerPrimitive state ct x r)
    else applyIntegerPrimitive (getZPrimitive state x r)

def uncheckedCastBigInt (x : BigFloat) (r : Mode) : M BigInt := do
  let state ← readContext
  let value ← applyIntegerPrimitive (getZPrimitive state x r)
  return JuliaLean.base.gmp.ofInt value

/--
MPFR manual §5.13 Exception Related Functions: https://www.mpfr.org/mpfr-current/mpfr.html#Exception-Related-Functions

Julia source: base/mpfr.jl:1326-1332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
clear_flags() = ccall((:mpfr_clear_flags, libmpfr), Cvoid, ())
had_underflow() = ccall((:mpfr_underflow_p, libmpfr), Cint, ()) != 0
had_overflow() = ccall((:mpfr_overflow_p, libmpfr), Cint, ()) != 0
had_divbyzero() = ccall((:mpfr_divby0_p, libmpfr), Cint, ()) != 0
had_nan() = ccall((:mpfr_nanflag_p, libmpfr), Cint, ()) != 0
had_inexact_exception() = ccall((:mpfr_inexflag_p, libmpfr), Cint, ()) != 0
had_range_exception() = ccall((:mpfr_erangeflag_p, libmpfr), Cint, ()) != 0
```
-/
def clearFlags : M Unit := do
  let state ← readContext
  writeContext { state with flags := {} }
def hadUnderflow (state : Context) : Bool := state.flags.underflow
def hadOverflow (state : Context) : Bool := state.flags.overflow
def hadDivbyzero (state : Context) : Bool := state.flags.divbyzero
def hadNan (state : Context) : Bool := state.flags.nan
def hadInexact (state : Context) : Bool := state.flags.inexact
def hadRange (state : Context) : Bool := state.flags.range

/--
Julia source: base/mpfr.jl:449-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function round(::Type{T}, x::BigFloat, r::Union{RoundingMode, MPFRRoundingMode}) where T<:Union{Signed, Unsigned}
    clear_flags()
    res = _unchecked_cast(T, x, r)
    if had_range_exception() || !(typemin(T) <= res <= typemax(T))
        throw(InexactError(:round, T, x))
    end
    return unsafe_trunc(T, res)
end

function round(::Type{BigInt}, x::BigFloat, r::Union{RoundingMode, MPFRRoundingMode})
    clear_flags()
    res = _unchecked_cast(BigInt, x, r)
    had_range_exception() && throw(InexactError(:round, BigInt, x))
    return res
end

round(::Type{T}, x::BigFloat, r::RoundingMode) where T<:Union{Signed, Unsigned} =
    invoke(round, Tuple{Type{<:Union{Signed, Unsigned}}, BigFloat, Union{RoundingMode, MPFRRoundingMode}}, T, x, r)
round(::Type{BigInt}, x::BigFloat, r::RoundingMode) =
    invoke(round, Tuple{Type{BigInt}, BigFloat, Union{RoundingMode, MPFRRoundingMode}}, BigInt, x, r)


unsafe_trunc(::Type{T}, x::BigFloat) where {T<:Integer} = unsafe_trunc(T, _unchecked_cast(T, x, RoundToZero))
unsafe_trunc(::Type{BigInt}, x::BigFloat) = _unchecked_cast(BigInt, x, RoundToZero)

round(::Type{T}, x::BigFloat) where T<:Integer = round(T, x, rounding_raw(BigFloat))
# these two methods are split to increase their precedence in disambiguation:
round(::Type{Integer}, x::BigFloat, r::RoundingMode) = round(BigInt, x, r)
round(::Type{Integer}, x::BigFloat, r::MPFRRoundingMode) = round(BigInt, x, r)
```
-/
def roundBits (t : IntTy) (x : BigFloat) (r : Mode) : M (JInt t) := do
  clearFlags
  let result ← uncheckedCastBits t x r
  if hadRange (← readContext) || !(t.min ≤ result ∧ result ≤ t.max) then
    throw (.inexactError "round")
  return JInt.wrap t result

def roundBigInt (x : BigFloat) (r : Mode) : M BigInt := do
  clearFlags
  let result ← uncheckedCastBigInt x r
  if hadRange (← readContext) then throw (.inexactError "round")
  return result

def roundBitsPublic (t : IntTy) (x : BigFloat) (r : RoundingMode) : M (JInt t) := do
  roundBits t x (← liftJl (toMPFR r))
def roundBigIntPublic (x : BigFloat) (r : RoundingMode) : M BigInt := do
  roundBigInt x (← liftJl (toMPFR r))

def unsafeTruncBits (t : IntTy) (x : BigFloat) : M (JInt t) := do
  return JInt.wrap t (← uncheckedCastBits t x .toZero)
def unsafeTruncBigInt (x : BigFloat) := uncheckedCastBigInt x .toZero

def roundBitsDefault (t : IntTy) (x : BigFloat) : M (JInt t) := do
  roundBits t x (roundingRaw (← readContext))
def roundInteger (x : BigFloat) (r : Mode) : M BigInt := roundBigInt x r

/--
Julia source: base/mpfr.jl:479-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Bool(x::BigFloat)
    iszero(x) && return false
    isone(x) && return true
    throw(InexactError(:Bool, Bool, x))
end
function BigInt(x::BigFloat)
    isinteger(x) || throw(InexactError(:BigInt, BigInt, x))
    trunc(BigInt, x)
end

function (::Type{T})(x::BigFloat) where T<:Integer
    isinteger(x) || throw(InexactError(nameof(T), T, x))
    trunc(T,x)
end
```
-/
def toBool (x : BigFloat) : M Bool := do
  if iszero x then return false
  let (n,d) := x.value.toRat
  if isfinite x && decide (n = (d : Int)) then return true
  throw (.inexactError "Bool")
def toBigInt (x : BigFloat) : M BigInt := do
  if !isinteger x then throw (.inexactError "BigInt")
  roundBigInt x .toZero
def toBits (t : IntTy) (x : BigFloat) : M (JInt t) := do
  if !isinteger x then throw (.inexactError t.name)
  roundBits t x .toZero

/-- MPFR manual §5.6: ordered numeric comparison, undefined on NaN.
https://www.mpfr.org/mpfr-current/mpfr.html#Comparison-Functions -/
def compareFP (x y : FP) : Int :=
  match x,y with
  | .nan _, _ | _, .nan _ => 0
  | .inf sx, .inf sy => if sx == sy then 0 else if sx then -1 else 1
  | .inf sx, _ => if sx then -1 else 1
  | _, .inf sy => if sy then 1 else -1
  | _, _ => let (n,d) := x.toRat; let (m,e) := y.toRat
            JuliaLean.base.gmp.sgn (n*(e : Int)-m*(d : Int))


/--
MPFR manual §5.6 `mpfr_equal_p`, `mpfr_lessequal_p`, `mpfr_less_p`, `mpfr_cmp_z/si/ui/d`: https://www.mpfr.org/mpfr-current/mpfr.html#Comparison-Functions

Julia source: base/mpfr.jl:990-1014 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::BigFloat, y::BigFloat) = ccall((:mpfr_equal_p, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), x, y) != 0
<=(x::BigFloat, y::BigFloat) = ccall((:mpfr_lessequal_p, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), x, y) != 0
<(x::BigFloat, y::BigFloat) = ccall((:mpfr_less_p, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), x, y) != 0

function cmp(x::BigFloat, y::BigInt)
    isnan(x) && return 1
    ccall((:mpfr_cmp_z, libmpfr), Int32, (Ref{BigFloat}, Ref{BigInt}), x, y)
end
function cmp(x::BigFloat, y::ClongMax)
    isnan(x) && return 1
    ccall((:mpfr_cmp_si, libmpfr), Int32, (Ref{BigFloat}, Clong), x, y)
end
function cmp(x::BigFloat, y::CulongMax)
    isnan(x) && return 1
    ccall((:mpfr_cmp_ui, libmpfr), Int32, (Ref{BigFloat}, Culong), x, y)
end
cmp(x::BigFloat, y::Integer) = cmp(x,big(y))
cmp(x::Integer, y::BigFloat) = -cmp(y,x)

function cmp(x::BigFloat, y::CdoubleMax)
    isnan(x) && return isnan(y) ? 0 : 1
    isnan(y) && return -1
    ccall((:mpfr_cmp_d, libmpfr), Int32, (Ref{BigFloat}, Cdouble), x, y)
end
cmp(x::CdoubleMax, y::BigFloat) = -cmp(y,x)
```
-/
def equal (x y : BigFloat) : Bool :=
  !isnan x && !isnan y && decide (compareFP x.value y.value = 0)
def lessEqual (x y : BigFloat) : Bool :=
  !isnan x && !isnan y && decide (compareFP x.value y.value ≤ 0)
def less (x y : BigFloat) : Bool :=
  !isnan x && !isnan y && decide (compareFP x.value y.value < 0)

def cmpBigInt (x : BigFloat) (y : BigInt) : Cint :=
  if isnan x then JInt.wrap .i32 1 else JInt.wrap .i32 (compareFP x.value (intValue y.val))
def cmpSigned {t : IntTy} (x : BigFloat) (y : JInt t) : Cint :=
  if isnan x then JInt.wrap .i32 1 else JInt.wrap .i32 (compareFP x.value (intValue y.val))
def cmpUnsigned {t : IntTy} (x : BigFloat) (y : JInt t) : Cint :=
  if isnan x then JInt.wrap .i32 1 else JInt.wrap .i32 (compareFP x.value (intValue y.val))
def cmpInteger {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : BigFloat) (y : I) := cmpBigInt x (JuliaLean.base.gmp.fromInteger ops y)
def integerCmp {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : I) (y : BigFloat) := -(cmpInteger ops y x)
def cmpIEEE {T : FTy} (x : BigFloat) (y : FV T) : Cint :=
  if isnan x then JInt.wrap .i32 (if y.isnan then 0 else 1)
  else if y.isnan then JInt.wrap .i32 (-1)
  else JInt.wrap .i32 (compareFP x.value (ieeeValue (convertFloat .f64 y)))
def ieeeCmp {T : FTy} (x : FV T) (y : BigFloat) := -(cmpIEEE y x)

/--
Julia source: base/mpfr.jl:1016-1029 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::BigFloat, y::Integer)    = !isnan(x) && cmp(x,y) == 0
==(x::Integer, y::BigFloat)    = y == x
==(x::BigFloat, y::CdoubleMax) = !isnan(x) && !isnan(y) && cmp(x,y) == 0
==(x::CdoubleMax, y::BigFloat) = y == x

<(x::BigFloat, y::Integer)    = !isnan(x) && cmp(x,y) < 0
<(x::Integer, y::BigFloat)    = !isnan(y) && cmp(y,x) > 0
<(x::BigFloat, y::CdoubleMax) = !isnan(x) && !isnan(y) && cmp(x,y) < 0
<(x::CdoubleMax, y::BigFloat) = !isnan(x) && !isnan(y) && cmp(y,x) > 0

<=(x::BigFloat, y::Integer)    = !isnan(x) && cmp(x,y) <= 0
<=(x::Integer, y::BigFloat)    = !isnan(y) && cmp(y,x) >= 0
<=(x::BigFloat, y::CdoubleMax) = !isnan(x) && !isnan(y) && cmp(x,y) <= 0
<=(x::CdoubleMax, y::BigFloat) = !isnan(x) && !isnan(y) && cmp(y,x) >= 0
```
-/
def equalInteger {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : BigFloat) (y : I) : Bool := !isnan x && decide ((cmpInteger ops x y).val = 0)
def integerEqual {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : I) (y : BigFloat) : Bool := equalInteger ops y x

def equalIEEE {T : FTy} (x : BigFloat) (y : FV T) : Bool :=
  !isnan x && !y.isnan && decide ((cmpIEEE x y).val = 0)
def ieeeEqual {T : FTy} (x : FV T) (y : BigFloat) := equalIEEE y x

def lessInteger {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : BigFloat) (y : I) : Bool := !isnan x && decide ((cmpInteger ops x y).val < 0)
def integerLess {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : I) (y : BigFloat) : Bool := !isnan y && decide ((cmpInteger ops y x).val > 0)
def lessIEEE {T : FTy} (x : BigFloat) (y : FV T) : Bool :=
  !isnan x && !y.isnan && decide ((cmpIEEE x y).val < 0)
def ieeeLess {T : FTy} (x : FV T) (y : BigFloat) : Bool :=
  !isnan y && !x.isnan && decide ((cmpIEEE y x).val > 0)

def lessEqualInteger {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : BigFloat) (y : I) : Bool := !isnan x && decide ((cmpInteger ops x y).val ≤ 0)
def integerLessEqual {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : I) (y : BigFloat) : Bool := !isnan y && decide ((cmpInteger ops y x).val ≥ 0)
def lessEqualIEEE {T : FTy} (x : BigFloat) (y : FV T) : Bool :=
  !isnan x && !y.isnan && decide ((cmpIEEE x y).val ≤ 0)
def ieeeLessEqual {T : FTy} (x : FV T) (y : BigFloat) : Bool :=
  !isnan y && !x.isnan && decide ((cmpIEEE y x).val ≥ 0)

/--
Julia source: base/mpfr.jl:1035-1039 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sign(x::BigFloat)
    c = cmp(x, 0)
    (c == 0 || isnan(x)) && return x
    return c < 0 ? -one(x) : one(x)
end
```
-/
def sign (x : BigFloat) : M BigFloat := do
  let c := cmpSigned x (JInt.wrap .i64 0)
  if c.val = 0 || isnan x then return x
  let one ← fromLong (JInt.wrap .i64 1) (roundingRaw (← readContext))
    (precisionType (← readContext)).val
  if c.val < 0 then neg one else pure one

/--
Julia source: base/mpfr.jl:1142-1142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isone(x::BigFloat) = x == Clong(1)
```
-/
def isone (x : BigFloat) : Bool := !isnan x && decide ((cmpSigned x (JInt.wrap .i64 1)).val = 0)

/--
Julia source: base/mpfr.jl:897-910 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function minmax(x::BigFloat, y::BigFloat)
    isnan(x) && return x, x
    isnan(y) && return y, y
    Base.Math._isless(x, y) ? (x, y) : (y, x)
end

function Base._extrema_rf(x::NTuple{2,BigFloat}, y::NTuple{2,BigFloat})
    (x1, x2), (y1, y2) = x, y
    isnan(x1) && return x
    isnan(y1) && return y
    z1 = Base.Math._isless(x1, y1) ? x1 : y1
    z2 = Base.Math._isless(x2, y2) ? y2 : x2
    z1, z2
end
```
-/
def isless (x y : BigFloat) : Bool :=
  if x.value.iszero && y.value.iszero then signbit x && !signbit y
  else less x y

def minmax (x y : BigFloat) : BigFloat × BigFloat :=
  if isnan x then (x,x) else if isnan y then (y,y)
  else if isless x y then (x,y) else (y,x)
def extremaRf (x y : BigFloat × BigFloat) : BigFloat × BigFloat :=
  let (x1,x2) := x
  let (y1,y2) := y
  if isnan x1 then x else if isnan y1 then y
  else (if isless x1 y1 then x1 else y1, if isless x2 y2 then y2 else x2)

/--
MPFR manual §5.13 Exception Related Functions, implementation limits are explicit context data: https://www.mpfr.org/mpfr-current/mpfr.html#Exception-Related-Functions

Julia source: base/mpfr.jl:1286-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_emax() = ccall((:mpfr_get_emax, libmpfr), Clong, ())
get_emax_min() = ccall((:mpfr_get_emax_min, libmpfr), Clong, ())
get_emax_max() = ccall((:mpfr_get_emax_max, libmpfr), Clong, ())

get_emin() = ccall((:mpfr_get_emin, libmpfr), Clong, ())
get_emin_min() = ccall((:mpfr_get_emin_min, libmpfr), Clong, ())
get_emin_max() = ccall((:mpfr_get_emin_max, libmpfr), Clong, ())

check_exponent_err(ret) = ret == 0 || throw(ArgumentError("Invalid MPFR exponent range"))
set_emax!(x) = check_exponent_err(ccall((:mpfr_set_emax, libmpfr), Cint, (Clong,), x))
set_emin!(x) = check_exponent_err(ccall((:mpfr_set_emin, libmpfr), Cint, (Clong,), x))
```
-/
def getEmax (state : Context) : Clong := state.emax
def getEmaxMin (state : Context) : Clong := state.limits.emaxMin
def getEmaxMax (state : Context) : Clong := state.limits.emaxMax
def getEmin (state : Context) : Clong := state.emin
def getEminMin (state : Context) : Clong := state.limits.eminMin
def getEminMax (state : Context) : Clong := state.limits.eminMax

def checkExponentErr (ret : Cint) : Jl Unit :=
  if ret.val = 0 then pure () else .error (.argumentError "Invalid MPFR exponent range")
def setEmax (x : Clong) : M Unit := do
  let state ← readContext
  if state.limits.emaxMin.val ≤ x.val ∧ x.val ≤ state.limits.emaxMax.val then
    writeContext { state with emax := x }
  else liftJl (checkExponentErr (JInt.wrap .i32 1))
def setEmin (x : Clong) : M Unit := do
  let state ← readContext
  if state.limits.eminMin.val ≤ x.val ∧ x.val ≤ state.limits.eminMax.val then
    writeContext { state with emin := x }
  else liftJl (checkExponentErr (JInt.wrap .i32 1))

/--
Julia source: base/mpfr.jl:47-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __init__()
    try
        # set exponent to full range by default
        set_emin!(get_emin_min())
        set_emax!(get_emax_max())
    catch ex
        Base.showerror_nostdio(ex, "WARNING: Error during initialization of module MPFR")
    end
    nothing
end
```
-/
def initModule (showError : JlError → M Unit) : M Unit := do
  tryCatch (do
    setEmin (getEminMin (← readContext))
    setEmax (getEmaxMax (← readContext))) showError

/--
Julia source: base/mpfr.jl:1047-1048 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_convert_precision_from_base(precision::Integer, base::Integer) =
    base == 2 ? precision : ceil(Int, precision * log2(base))
```
-/
def convertPrecisionFromBase {P B R : Type}
    (baseIsTwo : B → Bool) (log2 : B → R) (multiply : P → R → Jl R)
    (ceilInt : R → Jl Clong) (asClong : P → Jl Clong) (precision : P) (base : B) : Jl Clong :=
  if baseIsTwo base then asClong precision else do ceilInt (← multiply precision (log2 base))

/--
Julia source: base/mpfr.jl:1069-1076 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setprecision(::Type{BigFloat}, precision::Integer; base::Integer=2)
    base > 1 || throw(DomainError(base, "`base` cannot be less than 2."))
    precision > 0 || throw(DomainError(precision, "`precision` cannot be less than 1."))
    DEFAULT_PRECISION[] = _convert_precision_from_base(precision, base)
    return precision
end

setprecision(precision::Integer; base::Integer=2) = setprecision(BigFloat, precision; base)
```
-/
def setprecision {P B : Type} (valueP : P → Int) (valueB : B → Int)
    (convertPrecision : P → B → Jl Clong) (precision : P) (base : B) : M P := do
  if valueB base ≤ 1 then throw (.domainError "`base` cannot be less than 2.")
  if valueP precision ≤ 0 then throw (.domainError "`precision` cannot be less than 1.")
  let converted ← liftJl (convertPrecision precision base)
  let state ← readContext
  writeContext { state with defaultPrecision := converted }
  pure precision

def setprecisionDefault {P B : Type} (valueP : P → Int) (valueB : B → Int)
    (convertPrecision : P → B → Jl Clong) (precision : P) (base : B) :=
  setprecision valueP valueB convertPrecision precision base

/--
Julia source: base/mpfr.jl:1214-1219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setprecision(f::Function, ::Type{BigFloat}, prec::Integer; base::Integer=2)
    Base.ScopedValues.@with(CURRENT_PRECISION => _convert_precision_from_base(prec, base), f())
end
setprecision(f, ::Type{Union{}}, slurp...; kwargs...) = throw(MethodError(setprecision, (f, Union{}, slurp...)))

setprecision(f::Function, prec::Integer; base::Integer=2) = setprecision(f, BigFloat, prec; base)
```
-/
def withPrecision {P B : Type} (convertPrecision : P → B → Jl Clong)
    (action : M A) (prec : P) (base : B) : M A := do
  let converted ← liftJl (convertPrecision prec base)
  let body : M A := ⟨fun state =>
    let previous := state.scopedPrecision
    let (result,after) := action.run { state with scopedPrecision := some converted }
    (result,{ after with scopedPrecision := previous })⟩
  body

def setprecisionBottom {A : Type} : M A := throw (.methodError "setprecision")
def withPrecisionDefault {P B : Type} (convertPrecision : P → B → Jl Clong)
    (action : M A) (prec : P) (base : B) := withPrecision convertPrecision action prec base

/--
Julia source: base/mpfr.jl:1200-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setprecision(f::Function, ::Type{T}, prec::Integer; kws...) where T
    Base.depwarn("""
                 The fallback `setprecision(::Function, ...)` method is deprecated. Packages overloading this method should
                 implement their own specialization using `ScopedValue` instead.
                 """, :setprecision)
    old_prec = precision(T)
    setprecision(T, prec; kws...)
    try
        return f()
    finally
        setprecision(T, old_prec)
    end
end
```
-/
def withPrecisionFallback {P : Type} (warn : M Unit) (precision : M P)
    (setPrecision : P → M Unit) (prec : P) (action : M A) : M A := do
  warn
  let old ← precision
  setPrecision prec
  let result ← tryCatch (do let value ← action; pure (.ok value)) (fun error => pure (.error error))
  setPrecision old
  liftJl result

/--
MPFR manual §5.12 `mpfr_copysign`, `mpfr_get_exp`: https://www.mpfr.org/mpfr-current/mpfr.html#Miscellaneous-Functions

Julia source: base/mpfr.jl:1081-1093 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copysign(x::BigFloat, y::BigFloat)
    z = BigFloat()
    ccall((:mpfr_copysign, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
    return z
end

function exponent(x::BigFloat)
    if iszero(x) || !isfinite(x)
        throw(DomainError(x, "`x` must be non-zero and finite."))
    end
    # The '- 1' is to make it work as Base.exponent
    return ccall((:mpfr_get_exp, libmpfr), Clong, (Ref{BigFloat},), x) - 1
end
```
-/
def copysign (x y : BigFloat) : M BigFloat := do
  let z ← fresh
  let value := if x.value.signbit == y.value.signbit then x.value else x.value.neg
  let state ← readContext
  applyPrimitive (setPrimitive state z.prec value (roundingRaw state))

def exponent (x : BigFloat) : Jl Clong :=
  if iszero x || !isfinite x then .error (.domainError "`x` must be non-zero and finite.")
  else pure (x.exp-JInt.wrap .i64 1)

/--
Julia source: base/mpfr.jl:1115-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (f,R) in ((:roundeven, :Nearest),
              (:ceil, :Up),
              (:floor, :Down),
              (:trunc, :ToZero),
              (:round, :NearestTiesAway))
    @eval begin
        function round(x::BigFloat, ::RoundingMode{$(QuoteNode(R))})
            z = BigFloat()
            ccall(($(string(:mpfr_,f)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}), z, x)
            return z
        end
    end
end
```
-/
def roundValue (x : BigFloat) (r : RoundingMode) : M BigFloat := do
  let z ← fresh
  let mode ← liftJl (if r = .NearestTiesAway then pure Mode.nearest else toMPFR r)
  applyPrimitive (integerRoundPrimitive (← readContext) z.prec mode (r == .NearestTiesAway) x)

/-- MPFR manual §5.5 `mpfr_sqrt`: exact integer-square comparisons determine
all rounding bits, including ties and exponent underflow.
https://www.mpfr.org/mpfr-current/mpfr.html#Arithmetic-Functions -/
def sqrtRatPrimitive (state : Context) (precision : Clong) (mode : Mode)
    (n d : Nat) : PrimitiveResult :=
  if n = 0 then specialResult precision (.zero false) else
    let mode := effectiveMode state mode
    let exponent := (Fl.floorLog2Rat n d).fdiv 2 + 1
    let scale := exponent-precision.val
    let numerator := if scale ≥ 0 then n else n*2^(-2*scale).toNat
    let denominator := if scale ≥ 0 then d*2^(2*scale).toNat else d
    let q := Nat.sqrt (numerator/denominator)
    let exact := q*q*denominator = numerator
    let midpoint := (2*q+1)^2*denominator
    let up := if mode = .nearest then
      decide (4*numerator > midpoint) || (decide (4*numerator = midpoint) && decide (q%2 = 1))
      else roundsAway mode false && !decide exact
    let q := q + if up then 1 else 0
    let roundedExp := scale+(q.log2+1 : Nat)
    let (value,underflow,overflow) := if roundedExp > state.emax.val then
      (if mode == .nearest || roundsAway mode false then FP.inf false
        else FP.finite ((2^precision.val.toNat-1 : Nat) : Int) (state.emax.val-precision.val),false,true)
      else if roundedExp < state.emin.val then
        let twiceHalfScale := 2*(state.emin.val-2)
        let aboveHalf := if twiceHalfScale ≥ 0 then n > d*2^twiceHalfScale.toNat
          else n*2^(-twiceHalfScale).toNat > d
        let away := if mode = .nearest then aboveHalf else roundsAway mode false
        (if away then FP.finite 1 (state.emin.val-1) else FP.zero false,true,false)
      else (FP.finite (q : Int) scale,false,false)
    let comparison := match value with
      | .inf _ => 1
      | _ =>
        let (v,w) := value.toRat
        JuliaLean.base.gmp.sgn (v*v*(d : Int)-(n : Int)*(w*w : Nat))
    ⟨pack precision value,JInt.wrap .i32 comparison,
      { underflow := underflow,overflow := overflow,inexact := decide (comparison ≠ 0) }⟩

def sqrtPrimitive (state : Context) (precision : Clong) (mode : Mode) (x : BigFloat) : PrimitiveResult :=
  match x.value with
  | .nan s => specialResult precision (.nan s) { nan := true }
  | .zero s => specialResult precision (.zero s)
  | .inf false => specialResult precision (.inf false)
  | .inf true => specialResult precision (.nan false) { nan := true }
  | .finite m _ =>
    if m < 0 then specialResult precision (.nan false) { nan := true }
    else let (n,d) := x.value.toRat; sqrtRatPrimitive state precision mode n.toNat d


/--
Julia source: base/mpfr.jl:781-789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sqrt(x::BigFloat)
    isnan(x) && return x
    z = BigFloat()
    ccall((:mpfr_sqrt, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, rounding_raw(BigFloat))
    isnan(z) && throw(DomainError(x, "NaN result for non-NaN input."))
    return z
end

sqrt(x::BigInt) = sqrt(BigFloat(x))
```
-/
def sqrt (x : BigFloat) : M BigFloat := do
  if isnan x then return x
  let z ← fresh
  let state ← readContext
  let z ← applyPrimitive (sqrtPrimitive state z.prec (roundingRaw state) x)
  if isnan z then throw (.domainError "NaN result for non-NaN input")
  return z

def sqrtBigInt (x : BigInt) : M BigFloat := do
  let state ← readContext
  sqrt (← fromBigInt x (roundingRaw state) (precisionType state).val)

/-- MPFR manual §5.7 `mpfr_pow_si/ui/z`: exact integer powers and one
rounding, including reciprocal powers and signed zero/infinity.
https://www.mpfr.org/mpfr-current/mpfr.html#Transcendental-Functions -/
def powIntegerPrimitive (state : Context) (precision : Clong) (mode : Mode)
    (x : BigFloat) (exponent : Int) : PrimitiveResult :=
  if exponent = 0 then roundRat state precision mode 1 1 else
    let negative := x.value.signbit && decide (exponent%2 = 1)
    match x.value with
    | .nan s => specialResult precision (.nan s) { nan := true }
    | .inf _ => specialResult precision (if exponent < 0 then .zero negative else .inf negative)
    | .zero _ => specialResult precision (if exponent < 0 then .inf negative else .zero negative)
        { divbyzero := decide (exponent < 0) }
    | .finite _ _ =>
      let (n,d) := x.value.toRat
      if exponent < 0 then
        roundRat state precision mode
          ((if negative then -1 else 1)*(d^exponent.natAbs : Nat)) (n.natAbs^exponent.natAbs)
      else roundRat state precision mode (n^exponent.toNat) (d^exponent.toNat)


/--
Julia source: base/mpfr.jl:797-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ^(x::BigFloat, y::CulongMax)
    z = BigFloat()
    ccall((:mpfr_pow_ui, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Culong, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
    return z
end

function ^(x::BigFloat, y::ClongMax)
    z = BigFloat()
    ccall((:mpfr_pow_si, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Clong, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
    return z
end

function ^(x::BigFloat, y::BigInt)
    z = BigFloat()
    ccall((:mpfr_pow_z, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigInt}, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
    return z
end

^(x::BigFloat, y::Integer)  = typemin(Clong)  <= y <= typemax(Clong)  ? x^Clong(y)  : x^BigInt(y)
^(x::BigFloat, y::Unsigned) = typemin(Culong) <= y <= typemax(Culong) ? x^Culong(y) : x^BigInt(y)
```
-/
def powLong {t : IntTy} (x : BigFloat) (y : JInt t) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive (powIntegerPrimitive state z.prec (roundingRaw state) x y.val)
def powBigInt (x : BigFloat) (y : BigInt) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive (powIntegerPrimitive state z.prec (roundingRaw state) x y.val)
def powInteger {I U : Type} (value : I → Int) (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : BigFloat) (y : I) : M BigFloat :=
  if IntTy.min .i64 ≤ value y ∧ value y ≤ IntTy.max .i64 then
    powLong x (JInt.wrap .i64 (value y))
  else powBigInt x (JuliaLean.base.gmp.fromInteger ops y)
def powUnsigned {I U : Type} (value : I → Int) (ops : JuliaLean.base.gmp.IntegerInput I U)
    (x : BigFloat) (y : I) : M BigFloat :=
  if 0 ≤ value y ∧ value y ≤ IntTy.max .u64 then powLong x (JInt.wrap .u64 (value y))
  else powBigInt x (JuliaLean.base.gmp.fromInteger ops y)

/--
MPFR manual §5.5 `mpfr_mul_2si/ui`: exact scaling followed by destination rounding: https://www.mpfr.org/mpfr-current/mpfr.html#Arithmetic-Functions

Julia source: base/mpfr.jl:841-853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ldexp(x::BigFloat, n::Clong)
    z = BigFloat()
    ccall((:mpfr_mul_2si, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Clong, MPFRRoundingMode), z, x, n, rounding_raw(BigFloat))
    return z
end
function ldexp(x::BigFloat, n::Culong)
    z = BigFloat()
    ccall((:mpfr_mul_2ui, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Culong, MPFRRoundingMode), z, x, n, rounding_raw(BigFloat))
    return z
end
ldexp(x::BigFloat, n::ClongMax) = ldexp(x, convert(Clong, n))
ldexp(x::BigFloat, n::CulongMax) = ldexp(x, convert(Culong, n))
ldexp(x::BigFloat, n::Integer) = x * exp2(BigFloat(n))
```
-/
def ldexpLong {t : IntTy} (x : BigFloat) (n : JInt t) : M BigFloat := do
  let z ← fresh
  let value := match x.value with
    | .finite m e => FP.finite m (e+n.val)
    | v => v
  let state ← readContext
  applyPrimitive (setPrimitive state z.prec value (roundingRaw state))
def ldexpSignedMax {t : IntTy} (x : BigFloat) (n : JInt t) :=
  ldexpLong x (JInt.wrap .i64 n.val)
def ldexpUnsignedMax {t : IntTy} (x : BigFloat) (n : JInt t) :=
  ldexpLong x (JInt.wrap .u64 n.val)

/--
MPFR manual §5.5 `mpfr_fac_ui`, `mpfr_hypot`: factorial and norm rounded only at destination precision: https://www.mpfr.org/mpfr-current/mpfr.html#Arithmetic-Functions

Julia source: base/mpfr.jl:855-869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function factorial(x::BigFloat)
    if x < 0 || !isinteger(x)
        throw(DomainError(x, "Must be a non-negative integer."))
    end
    ui = convert(Culong, x)
    z = BigFloat()
    ccall((:mpfr_fac_ui, libmpfr), Int32, (Ref{BigFloat}, Culong, MPFRRoundingMode), z, ui, rounding_raw(BigFloat))
    return z
end

function hypot(x::BigFloat, y::BigFloat)
    z = BigFloat()
    ccall((:mpfr_hypot, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
    return z
end
```
-/
def factorial (x : BigFloat) : M BigFloat := do
  if decide (compareFP x.value (intValue 0) < 0) && !isnan x || !isinteger x then
    throw (.domainError "Must be a non-negative integer")
  let ui ← toBits .u64 x
  let z ← fresh
  let state ← readContext
  applyPrimitive (roundRat state z.prec (roundingRaw state)
    (JuliaLean.base.gmp.factorialNat ui.val.toNat) 1)

def hypot (x y : BigFloat) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  if isinf x || isinf y then return ← applyPrimitive (specialResult z.prec (.inf false))
  if isnan x || isnan y then
    return ← applyPrimitive (specialResult z.prec (.nan false) { nan := true })
  let (a,b) := x.value.toRat
  let (c,d) := y.value.toRat
  applyPrimitive (sqrtRatPrimitive state z.prec (roundingRaw state)
    (a.natAbs^2*d^2+c.natAbs^2*b^2) (b^2*d^2))

/-- MPFR manual §5.10 `mpfr_fmod`, `mpfr_remainder`: exact quotient
rounded toward zero or to nearest-even, followed by one remainder rounding.
https://www.mpfr.org/mpfr-current/mpfr.html#Integer-and-Remainder-Related-Functions -/
def remainderPrimitive (state : Context) (precision : Clong) (mode : Mode)
    (nearestQuotient : Bool) (x y : BigFloat) : PrimitiveResult :=
  if isnan x || isnan y || isinf x || iszero y then
    specialResult precision (.nan false) { nan := true }
  else if isinf y then setPrimitive state precision x.value mode
  else
    let (a,b) := x.value.toRat
    let (c,d) := y.value.toRat
    let quotient := roundIntegerRat (if nearestQuotient then .nearest else .toZero)
      (a*(d : Int)*JuliaLean.base.gmp.sgn c) (b*c.natAbs)
    roundRat state precision mode (a*(d : Int)-quotient*c*(b : Int)) (b*d) (signbit x)


/--
Julia source: base/mpfr.jl:919-929 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem(x::BigFloat, y::BigFloat)
    z = BigFloat()
    ccall((:mpfr_fmod, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
    return z
end

function rem(x::BigFloat, y::BigFloat, ::RoundingMode{:Nearest})
    z = BigFloat()
    ccall((:mpfr_remainder, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
    return z
end
```
-/
def rem (x y : BigFloat) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive (remainderPrimitive state z.prec (roundingRaw state) false x y)
def remNearest (x y : BigFloat) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive (remainderPrimitive state z.prec (roundingRaw state) true x y)

/--
MPFR manual §5.10 `mpfr_modf`: separately rounded integral and fractional parts: https://www.mpfr.org/mpfr-current/mpfr.html#Integer-and-Remainder-Related-Functions

Julia source: base/mpfr.jl:912-917 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function modf(x::BigFloat)
    zint = BigFloat()
    zfloat = BigFloat()
    ccall((:mpfr_modf, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), zint, zfloat, x, rounding_raw(BigFloat))
    return (zfloat, zint)
end
```
-/
def modf (x : BigFloat) : M (BigFloat × BigFloat) := do
  let zint ← fresh
  let zfloat ← fresh
  let state ← readContext
  let integral := match x.value with
    | .nan s => specialResult zint.prec (.nan s) { nan := true }
    | .inf s => specialResult zint.prec (.inf s)
    | .zero s => specialResult zint.prec (.zero s)
    | .finite _ _ =>
      let (n,d) := x.value.toRat
      roundRat state zint.prec (roundingRaw state) (n.tdiv (d : Int)) 1 (signbit x)
  let zint ← applyPrimitive integral
  let result := match x.value with
    | .nan s => specialResult zfloat.prec (.nan s) { nan := true }
    | .inf s | .zero s => specialResult zfloat.prec (.zero s)
    | .finite _ _ =>
      let (n,d) := x.value.toRat
      let integer := n.tdiv (d : Int)
      roundRat state zfloat.prec (roundingRaw state) (n-integer*(d : Int)) d (signbit x)
  let zfloat ← applyPrimitive result
  return (zfloat,zint)

/--
Julia source: base/mpfr.jl:934-941 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sum(arr::AbstractArray{BigFloat})
    z = BigFloat(0)
    for i in arr
        ccall((:mpfr_add, libmpfr), Int32,
            (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, z, i, rounding_raw(BigFloat))
    end
    return z
end
```
-/
def sum (arr : List BigFloat) : M BigFloat := do
  let state ← readContext
  let init ← fromLong (JInt.wrap .i64 0) (roundingRaw state) (precisionType state).val
  arr.foldlM (fun z i => do
    let state ← readContext
    applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) .add ⟨z.value,false⟩ ⟨i.value,false⟩)) init

/--
MPFR manual §5.4 `mpfr_frexp`; exponent output is unspecified for NaN/Inf and retains input exponent here: https://www.mpfr.org/mpfr-current/mpfr.html#Conversion-Functions

Julia source: base/mpfr.jl:1095-1109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function frexp(x::BigFloat)
    z = BigFloat()
    c = Ref{Clong}()
    ccall((:mpfr_frexp, libmpfr), Int32, (Ptr{Clong}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), c, z, x, rounding_raw(BigFloat))
    return (z, c[])
end

function significand(x::BigFloat)
    z = BigFloat()
    c = Ref{Clong}()
    ccall((:mpfr_frexp, libmpfr), Int32, (Ptr{Clong}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), c, z, x, rounding_raw(BigFloat))
    # Double the significand to make it work as Base.significand
    ccall((:mpfr_mul_si, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Clong, MPFRRoundingMode), z, z, 2, rounding_raw(BigFloat))
    return z
end
```
-/
def frexp (x : BigFloat) : M (BigFloat × Clong) := do
  let z ← fresh
  let state ← readContext
  let e := if iszero x then JInt.wrap .i64 0 else x.exp
  let scaled := match x.value with
    | .finite m scale => FP.finite m (scale-e.val)
    | v => v
  let z ← applyPrimitive (setPrimitive state z.prec scaled (roundingRaw state))
  return (z,e)

def significand (x : BigFloat) : M BigFloat := do
  let (z,_) ← frexp x
  let state ← readContext
  applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) .mul ⟨z.value,false⟩ (.ofInt 2))

/--
Julia source: base/mpfr.jl:1307-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function decompose(x::BigFloat)::Tuple{BigInt, Int, Int}
    isnan(x) && return 0, 0, 0
    isinf(x) && return x.sign, 0, 0
    x == 0 && return 0, 0, x.sign
    s = BigInt()
    s.size = cld(x.prec, 8*sizeof(Limb)) # limbs
    b = s.size * sizeof(Limb)            # bytes
    ccall((:__gmpz_realloc2, libgmp), Cvoid, (Ref{BigInt}, Culong), s, 8b) # bits
    xd = x.d
    GC.@preserve xd memcpy(s.d, Base.unsafe_convert(Ptr{Limb}, xd), b)
    s, x.exp - 8b, x.sign
end
```
-/
def decompose (x : BigFloat) : BigInt × Clong × Clong :=
  if isnan x then (JuliaLean.base.gmp.ofInt 0,JInt.wrap .i64 0,JInt.wrap .i64 0)
  else if isinf x then (JuliaLean.base.gmp.ofInt x.sign.val,JInt.wrap .i64 0,JInt.wrap .i64 0)
  else if x.value.iszero then (JuliaLean.base.gmp.ofInt 0,JInt.wrap .i64 0,JInt.wrap .i64 x.sign.val)
  else
    let nlimbs := (x.prec.val+63).tdiv 64
    let bytes := JInt.wrap .i64 (nlimbs*8)
    let s := JuliaLean.base.gmp.ofInt (JuliaLean.base.gmp.limbMagnitude (x.d.take nlimbs.toNat))
    (s,x.exp-JInt.wrap .i64 (8*bytes.val),JInt.wrap .i64 x.sign.val)

/--
Julia source: base/mpfr.jl:1320-1323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lerpi(j::Integer, d::Integer, a::BigFloat, b::BigFloat)
    t = BigFloat(j)/d
    fma(t, b, fma(-t, a, a))
end
```
-/
def lerpi {J D : Type} (convertJ : J → M BigFloat) (divideD : BigFloat → D → M BigFloat)
    (j : J) (d : D) (a b : BigFloat) : M BigFloat := do
  let t ← divideD (← convertJ j) d
  let inside ← fma (← neg t) a a
  fma t b inside

/--
Julia source: base/mpfr.jl:1298-1305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.deepcopy_internal(x::BigFloat, stackdict::IdDict)
    get!(stackdict, x) do
        d′ = copy(getfield(x, :d))
        y = _BigFloat(d′)
        #ccall((:mpfr_custom_move,libmpfr), Cvoid, (Ref{BigFloat}, Ptr{Limb}), y, d) # unnecessary
        return y
    end::BigFloat
end
```
-/
def deepcopyInternal {D : Type}
    (getOrInsert : D → BigFloat → (Unit → M BigFloat) → M (BigFloat × D))
    (x : BigFloat) (stackdict : D) : M (BigFloat × D) :=
  getOrInsert stackdict x (fun _ => pure { x with d := x.d.map id })

inductive FieldValue where
  | precision (value : Clong)
  | sign (value : Cint)
  | exponent (value : Clong)
  | data (limbs : List Limb)
  deriving Repr
inductive StorageError where
  | fieldError (field : String)
  | boundsError
  | incompatibleRef
  | julia (error : JlError)
  deriving DecidableEq, Repr


/--
Julia source: base/mpfr.jl:178-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct BigFloatData{Limb}
    d::Memory{Limb}
end

# BigFloat interface
@inline function Base.getproperty(x::BigFloat, s::Symbol)
    d = getfield(x, :d)
    p = Base.unsafe_convert(Ptr{Limb}, d)
    if s === :prec
        return GC.@preserve d unsafe_load(Ptr{Clong}(p) + offset_prec)
    elseif s === :sign
        return GC.@preserve d unsafe_load(Ptr{Cint}(p) + offset_sign)
    elseif s === :exp
        return GC.@preserve d unsafe_load(Ptr{Clong}(p) + offset_exp)
    elseif s === :d
        return BigFloatData(d)
    else
        return throw(FieldError(typeof(x), s))
    end
end
```
-/
def getproperty (x : BigFloat) (field : String) : Except StorageError FieldValue :=
  if field = "prec" then pure (.precision x.prec)
  else if field = "sign" then pure (.sign x.sign)
  else if field = "exp" then pure (.exponent x.exp)
  else if field = "d" then pure (.data x.d)
  else .error (.fieldError field)

/--
Julia source: base/mpfr.jl:201-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function Base.setproperty!(x::BigFloat, s::Symbol, v)
    d = getfield(x, :d)
    p = Base.unsafe_convert(Ptr{Limb}, d)
    if s === :sign
        return GC.@preserve d unsafe_store!(Ptr{Cint}(p) + offset_sign, v)
    elseif s === :exp
        return GC.@preserve d unsafe_store!(Ptr{Clong}(p) + offset_exp, v)
    else
        throw(FieldError(BigFloat, s))
    end
end
```
-/
def setpropertySign (x : BigFloat) (sign : Cint) : BigFloat :=
  let value := if decide (sign.val < 0) == x.value.signbit then x.value else x.value.neg
  { x with sign := sign, value := value }
def setpropertyExp (x : BigFloat) (exponent : Clong) : BigFloat :=
  let negative := x.value.signbit
  let value := if exponent == specialNanExp then FP.nan negative
    else if exponent == specialInfExp then FP.inf negative
    else if exponent == specialZeroExp then FP.zero negative
    else
      let magnitude := JuliaLean.base.gmp.limbMagnitude x.d
      FP.finite (if negative then -(magnitude : Int) else magnitude)
        (exponent.val-(x.d.length*64 : Nat))
  { x with exp := exponent,value := value }
def setproperty (x : BigFloat) (field : String) (v : Int) : Except StorageError BigFloat :=
  if field = "sign" then do
    let v ← (JInt.convert "Int32" .i32 v).mapError StorageError.julia
    pure (setpropertySign x v)
  else if field = "exp" then do
    let v ← (JInt.convert "Int64" .i64 v).mapError StorageError.julia
    pure (setpropertyExp x v)
  else .error (.fieldError field)

/--
Julia source: base/mpfr.jl:230-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.setindex!(fd::BigFloatData, v, i)
    d = getfield(fd, :d)
    @boundscheck 1 <= i <= length(d) - offset_p_limbs || throw(BoundsError(fd, i))
    @inbounds d[i + offset_p_limbs] = v
    return fd
end
function Base.getindex(fd::BigFloatData, i)
    d = getfield(fd, :d)
    @boundscheck 1 <= i <= length(d) - offset_p_limbs || throw(BoundsError(fd, i))
    @inbounds d[i + offset_p_limbs]
end
Base.length(fd::BigFloatData) = length(getfield(fd, :d)) - offset_p_limbs
Base.copyto!(fd::BigFloatData, limbs) = copyto!(getfield(fd, :d), offset_p_limbs + 1, limbs) # for Random
```
-/
def dataSetindex (limbs : List Limb) (v : Limb) (i : Clong) : Jl (List Limb) :=
  if i.val < 1 ∨ i.val > (limbs.length : Nat) then .error .boundsError
  else pure (limbs.set (i.val-1).toNat v)
def dataGetindex (limbs : List Limb) (i : Clong) : Jl Limb :=
  if i.val < 1 ∨ i.val > (limbs.length : Nat) then .error .boundsError
  else match limbs[(i.val-1).toNat]? with
    | some l => pure l
    | none => .error .boundsError
def dataLength (limbs : List Limb) : Clong := JInt.wrap .i64 (limbs.length : Int)
def dataCopyto (limbs source : List Limb) : Jl (List Limb) :=
  if source.length > limbs.length then .error .boundsError
  else pure (source ++ limbs.drop source.length)

def ieeeMode (r : Mode) : RoundingMode :=
  match r with
  | .nearest => .Nearest | .toZero => .ToZero | .up => .Up | .down => .Down
  | .fromZero | .faithful => .FromZero

def ieeeIncrement (r : RoundingMode) (negative : Bool) (kept lost total : Nat) : Bool :=
  if total = 0 then false else
  if JuliaLean.base.gmp.roundsNearest r then
    let tieUp := if r = .Nearest then decide (kept%2 = 1)
      else if r = .NearestTiesAway then true else !negative
    decide (2*lost > total) || (decide (2*lost = total) && tieUp)
  else JuliaLean.base.gmp.roundsAway r negative && decide (lost ≠ 0)


/--
Julia source: base/mpfr.jl:494-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function to_ieee754(::Type{T}, x::BigFloat, rm) where {T<:AbstractFloat}
    sb = signbit(x)
    is_zero = iszero(x)
    is_inf = isinf(x)
    is_nan = isnan(x)
    is_regular = !is_zero & !is_inf & !is_nan
    ieee_exp = Int(x.exp) - 1
    ieee_precision = precision(T)
    ieee_exp_max = exponent_max(T)
    ieee_exp_min = exponent_min(T)
    exp_diff = ieee_exp - ieee_exp_min
    is_normal = 0 ≤ exp_diff
    (rm_is_to_zero, rm_is_from_zero) = if rounds_to_nearest(rm)
        (false, false)
    else
        let from = rounds_away_from_zero(rm, sb)
            (!from, from)
        end
    end::NTuple{2,Bool}
    exp_is_huge_p = ieee_exp_max < ieee_exp
    exp_is_huge_n = signbit(exp_diff + ieee_precision)
    rounds_to_inf = is_regular & exp_is_huge_p & !rm_is_to_zero
    rounds_to_zero = is_regular & exp_is_huge_n & !rm_is_from_zero
    U = uinttype(T)

    ret_u = if is_regular & !rounds_to_inf & !rounds_to_zero
        if !exp_is_huge_p
            # significand
            v = x.d::BigFloatData
            len = max(ieee_precision + min(exp_diff, 0), 0)::Int
            signif = truncated(U, v, len) & significand_mask(T)

            # round up if necessary
            rh = BigFloatDataRoundingIncrementHelper(v, len)
            incr = correct_rounding_requires_increment(rh, rm, sb)

            # exponent
            exp_field = max(exp_diff, 0) + is_normal

            ieee754_representation(T, sb, exp_field, signif) + incr
        else
            ieee754_representation(T, sb, Val(:omega))
        end
    else
        if is_zero | rounds_to_zero
            ieee754_representation(T, sb, Val(:zero))
        elseif is_inf | rounds_to_inf
            ieee754_representation(T, sb, Val(:inf))
        else
            ieee754_representation(T, sb, Val(:nan))
        end
    end::U

    reinterpret(T, ret_u)
end

Float16(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat)) = to_ieee754(Float16, x, r)
Float32(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat)) = to_ieee754(Float32, x, r)
Float64(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat)) = to_ieee754(Float64, x, r)
Float16(x::BigFloat, r::RoundingMode) = to_ieee754(Float16, x, r)
Float32(x::BigFloat, r::RoundingMode) = to_ieee754(Float32, x, r)
Float64(x::BigFloat, r::RoundingMode) = to_ieee754(Float64, x, r)
```
-/
def toIEEE (T : FTy) (x : BigFloat) (rm : RoundingMode) : FV T :=
  let sb := signbit x
  let isZero := iszero x
  let isInf := isinf x
  let isNan := isnan x
  let regular := !isZero && !isInf && !isNan
  let ieeeExp := x.exp-JInt.wrap .i64 1
  let ieeePrecision := precision_Type_default T
  let ieeeExpMax := exponent_max T
  let ieeeExpMin := exponent_min T
  let expDiff := ieeeExp-ieeeExpMin
  let normal := decide (expDiff.val ≥ 0)
  let (rmToZero,rmFromZero) := if JuliaLean.base.gmp.roundsNearest rm then (false,false)
    else let away := JuliaLean.base.gmp.roundsAway rm sb; (!away,away)
  let hugePositive := decide (ieeeExpMax.val < ieeeExp.val)
  let hugeNegative := decide ((expDiff+ieeePrecision).val < 0)
  let roundsToInf := regular && hugePositive && !rmToZero
  let roundsToZero := regular && hugeNegative && !rmFromZero
  let result := if regular && !roundsToInf && !roundsToZero then
    if !hugePositive then
      let len := max (ieeePrecision+JInt.wrap .i64 (min expDiff.val 0)).val 0
      let width := x.d.length*64
      let value := JuliaLean.base.gmp.limbMagnitude x.d
      let discarded := width-len.toNat
      let truncated := if len.toNat ≥ width then value*2^(len.toNat-width)
        else value / 2^discarded
      let signif := JInt.wrap T.uintTy ((truncated % 2^T.fmt.sb : Nat) : Int)
      let lost := value % 2^discarded
      let incr := ieeeIncrement rm sb truncated lost (if discarded = 0 then 0 else 2^discarded)
      let exponentField := JInt.wrap .i64 (max expDiff.val 0 + if normal then 1 else 0)
      let u := ieee754_representation T sb exponentField signif
      u + JInt.wrap T.uintTy (if incr then 1 else 0)
    else ieee754_representation_omega T sb
  else if isZero || roundsToZero then ieee754_representation_zero T sb
    else if isInf || roundsToInf then ieee754_representation_inf T sb
    else ieee754_representation_nan T sb
  Fl.ofBits result.val.toNat

def toIEEERaw (T : FTy) (x : BigFloat) (rm : Mode) : FV T := toIEEE T x (ieeeMode rm)
def toFloat16 (x : BigFloat) (rm : Mode) : FV .f16 := toIEEERaw .f16 x rm
def toFloat32 (x : BigFloat) (rm : Mode) : FV .f32 := toIEEERaw .f32 x rm
def toFloat64 (x : BigFloat) (rm : Mode) : FV .f64 := toIEEERaw .f64 x rm
def toFloat16Public (x : BigFloat) (rm : RoundingMode) : FV .f16 := toIEEE .f16 x rm
def toFloat32Public (x : BigFloat) (rm : RoundingMode) : FV .f32 := toIEEE .f32 x rm
def toFloat64Public (x : BigFloat) (rm : RoundingMode) : FV .f64 := toIEEE .f64 x rm

/--
Julia source: base/mpfr.jl:299-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Float64}) = BigFloat
widen(::Type{BigFloat}) = BigFloat
```
-/
inductive BigFloatType where | type
  deriving DecidableEq, Repr
def widenFloat64 : BigFloatType := .type
def widenBigFloat : BigFloatType := .type

/--
Julia source: base/mpfr.jl:557-563 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{BigFloat}, ::Type{<:Real}) = BigFloat
promote_rule(::Type{BigInt}, ::Type{<:AbstractFloat}) = BigFloat
promote_rule(::Type{BigFloat}, ::Type{<:AbstractFloat}) = BigFloat

big(::Type{<:AbstractFloat}) = BigFloat

big(x::AbstractFloat) = convert(BigFloat, x)
```
-/
def promoteBigFloatReal : BigFloatType := .type
def promoteBigIntAbstractFloat : BigFloatType := .type
def promoteBigFloatAbstractFloat : BigFloatType := .type
def bigAbstractFloatType : BigFloatType := .type
def bigAbstractFloat {F : Type} (convert : F → Jl BigFloat) (x : F) := convert x

/--
Julia source: base/mpfr.jl:414-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BigFloat(x::AbstractString, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat)) =
    parse(BigFloat, x; precision=precision, rounding=r)

Rational(x::BigFloat) = convert(Rational{BigInt}, x)
AbstractFloat(x::BigInt) = BigFloat(x)

float(::Type{BigInt}) = BigFloat

BigFloat(x::Real, r::RoundingMode; precision::Integer=_precision_with_base_2(BigFloat)) =
    BigFloat(x, convert(MPFRRoundingMode, r); precision=precision)::BigFloat
BigFloat(x::AbstractString, r::RoundingMode; precision::Integer=_precision_with_base_2(BigFloat)) =
    BigFloat(x, convert(MPFRRoundingMode, r); precision=precision)
```
-/
def fromString {S : Type} (parse : S → Int → Mode → M BigFloat)
    (x : S) (r : Mode) (precision : Int) := parse x precision r
def rationalBigFloat {R : Type} (convert : BigFloat → Jl R) (x : BigFloat) := convert x
def abstractFloatBigInt (x : BigInt) : M BigFloat := do
  let state ← readContext
  fromBigInt x (roundingRaw state) (precisionType state).val
def floatBigIntType : BigFloatType := .type
def fromRealPublic {R : Type} (construct : R → Mode → Int → M BigFloat)
    (x : R) (r : RoundingMode) (precision : Int) : M BigFloat := do
  construct x (← liftJl (toMPFR r)) precision
def fromStringPublic {S : Type} (construct : S → Mode → Int → M BigFloat)
    (x : S) (r : RoundingMode) (precision : Int) : M BigFloat := do
  construct x (← liftJl (toMPFR r)) precision

/--
Julia source: base/mpfr.jl:565-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Rational{BigInt}(x::AbstractFloat)
    isnan(x) && return zero(BigInt) // zero(BigInt)
    isinf(x) && return copysign(one(BigInt),x) // zero(BigInt)
    iszero(x) && return zero(BigInt) // one(BigInt)
    s = max(precision(x) - exponent(x), 0)
    BigInt(ldexp(x,s)) // (BigInt(1) << s)
end
```
-/
def rationalAbstractFloat {F R : Type}
    (isnan isinf iszero : F → Bool) (precision exponent : F → M Clong)
    (copysignOne : F → M BigInt) (ldexp : F → Clong → M F)
    (toBigInt : F → M BigInt) (rational : BigInt → BigInt → M R) (x : F) : M R := do
  if isnan x then return ← rational (JuliaLean.base.gmp.ofInt 0) (JuliaLean.base.gmp.ofInt 0)
  if isinf x then return ← rational (← copysignOne x) (JuliaLean.base.gmp.ofInt 0)
  if iszero x then return ← rational (JuliaLean.base.gmp.ofInt 0) (JuliaLean.base.gmp.ofInt 1)
  let s := JInt.wrap .i64 (max ((← precision x)-(← exponent x)).val 0)
  let num ← toBigInt (← ldexp x s)
  let den := JuliaLean.base.gmp.shiftLeft (JuliaLean.base.gmp.ofInt 1) (JInt.wrap .u64 s.val)
  rational num den

/--
Julia source: base/mpfr.jl:1078-1079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxintfloat(x::BigFloat) = BigFloat(2)^precision(x)
maxintfloat(::Type{BigFloat}) = BigFloat(2)^precision(BigFloat)
```
-/
def maxintfloatValue (x : BigFloat) : M BigFloat := do
  let state ← readContext
  let two ← fromLong (JInt.wrap .i64 2) (roundingRaw state) (precisionType state).val
  powLong two x.prec
def maxintfloatType : M BigFloat := do
  let state ← readContext
  let two ← fromLong (JInt.wrap .i64 2) (roundingRaw state) (precisionType state).val
  powLong two (precisionType (← readContext))

/--
Julia source: base/mpfr.jl:1148-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval typemax(::Type{BigFloat}) = $(BigFloat(Inf))
@eval typemin(::Type{BigFloat}) = $(BigFloat(-Inf))
```
-/
def typemax (precision : Clong) : BigFloat := pack precision (.inf false)
def typemin (precision : Clong) : BigFloat := pack precision (.inf true)

/--
MPFR manual §5.12 `mpfr_get_version`, `mpfr_get_patches`: library metadata: https://www.mpfr.org/mpfr-current/mpfr.html#Miscellaneous-Functions

Julia source: base/mpfr.jl:44-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
version() = VersionNumber(unsafe_string(ccall((:mpfr_get_version,libmpfr), Ptr{Cchar}, ())))
patches() = split(unsafe_string(ccall((:mpfr_get_patches,libmpfr), Ptr{Cchar}, ())),' ')
```
-/
structure LibraryVersion where
  versionString : String
  patchesString : String

def version {V : Type} (versionNumber : String → Jl V) (globals : LibraryVersion) : Jl V :=
  versionNumber globals.versionString
def patches (globals : LibraryVersion) : List String := globals.patchesString.splitOn " "

/-- MPFR manual §5.12 `mpfr_nextabove/nextbelow`: adjacency at the
object's stored precision; only NaN can raise a flag.
https://www.mpfr.org/mpfr-current/mpfr.html#Miscellaneous-Functions -/
def nextPrimitive (state : Context) (up : Bool) (x : BigFloat) : PrimitiveResult :=
  let p := x.prec.val.toNat
  let negative := signbit x
  let maxFinite := FP.finite (if negative then -((2^p-1 : Nat) : Int) else (2^p-1 : Nat))
    (state.emax.val-x.prec.val)
  match x.value with
  | .nan s => specialResult x.prec (.nan s) { nan := true }
  | .inf s => specialResult x.prec (if up != s then .inf s else maxFinite)
  | .zero _ => specialResult x.prec (.finite (if up then 1 else -1) (state.emin.val-1))
  | .finite _ _ =>
    let exponent := x.exp.val
    let q := JuliaLean.base.gmp.limbMagnitude x.d / 2^(x.d.length*64-p)
    let grow := up != negative
    let value := if grow then
      if exponent = state.emax.val ∧ q = 2^p-1 then FP.inf negative
      else FP.finite (if negative then -((q+1 : Nat) : Int) else q+1) (exponent-x.prec.val)
    else if q = 2^(p-1) then
      if exponent = state.emin.val then FP.zero negative
      else FP.finite (if negative then -((2^p-1 : Nat) : Int) else (2^p-1 : Nat))
        (exponent-x.prec.val-1)
    else FP.finite (if negative then -((q-1 : Nat) : Int) else (q-1 : Nat))
      (exponent-x.prec.val)
    specialResult x.prec value

def repeatNext : Nat → Bool → BigFloat → M BigFloat
  | 0, _, x => pure x
  | count+1, up, x => do
    let x ← applyPrimitive (nextPrimitive (← readContext) up x)
    repeatNext count up x

def directionAndCount {I : Type} (negative : I → Bool) (abs : I → I)
    (value : I → Int) (up : Bool) (n : I) : Option (Jl (Bool × Nat)) :=
  JuliaLean.base.reduce.whileLoop (fun (up,n) =>
    pure (if negative n then .inr (!up,abs n) else .inl (up,(value n).toNat))) (up,n)


/--
Julia source: base/mpfr.jl:1151-1168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nextfloat!(x::BigFloat, n::Integer=1)
    signbit(n) && return prevfloat!(x, abs(n))
    for _ = 1:n
        ccall((:mpfr_nextabove, libmpfr), Int32, (Ref{BigFloat},), x)
    end
    return x
end

function prevfloat!(x::BigFloat, n::Integer=1)
    signbit(n) && return nextfloat!(x, abs(n))
    for _ = 1:n
        ccall((:mpfr_nextbelow, libmpfr), Int32, (Ref{BigFloat},), x)
    end
    return x
end

nextfloat(x::BigFloat, n::Integer=1) = n == 0 ? x : nextfloat!(_duplicate(x), n)
prevfloat(x::BigFloat, n::Integer=1) = n == 0 ? x : prevfloat!(_duplicate(x), n)
```
-/
def nextfloatBang {I : Type} (negative : I → Bool) (abs : I → I) (value : I → Int)
    (x : BigFloat) (n : I) (state : Context) : Option (Jl BigFloat × Context) :=
  match directionAndCount negative abs value true n with
  | none => none
  | some (.error e) => some (.error e,state)
  | some (.ok (up,count)) => some ((repeatNext count up x).run state)
def prevfloatBang {I : Type} (negative : I → Bool) (abs : I → I) (value : I → Int)
    (x : BigFloat) (n : I) (state : Context) : Option (Jl BigFloat × Context) :=
  match directionAndCount negative abs value false n with
  | none => none
  | some (.error e) => some (.error e,state)
  | some (.ok (up,count)) => some ((repeatNext count up x).run state)

def nextfloat {I : Type} (negative : I → Bool) (abs : I → I) (value : I → Int)
    (x : BigFloat) (n : I) (state : Context) : Option (Jl BigFloat × Context) :=
  if value n = 0 then some (.ok x,state) else
    let (copy,state) := (duplicate x).run state
    match copy with
    | .error e => some (.error e,state)
    | .ok x => nextfloatBang negative abs value x n state

def prevfloat {I : Type} (negative : I → Bool) (abs : I → I) (value : I → Int)
    (x : BigFloat) (n : I) (state : Context) : Option (Jl BigFloat × Context) :=
  if value n = 0 then some (.ok x,state) else
    let (copy,state) := (duplicate x).run state
    match copy with
    | .error e => some (.error e,state)
    | .ok x => prevfloatBang negative abs value x n state

/--
Julia source: base/mpfr.jl:1170-1173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eps(::Type{BigFloat}) = nextfloat(BigFloat(1)) - BigFloat(1)

floatmin(::Type{BigFloat}) = nextfloat(zero(BigFloat))
floatmax(::Type{BigFloat}) = prevfloat(BigFloat(Inf))
```
-/
def nextfloatOne (x : BigFloat) : M BigFloat := do
  let x ← duplicate x
  applyPrimitive (nextPrimitive (← readContext) true x)
def prevfloatOne (x : BigFloat) : M BigFloat := do
  let x ← duplicate x
  applyPrimitive (nextPrimitive (← readContext) false x)
def epsType : M BigFloat := do
  let state ← readContext
  let one ← fromLong (JInt.wrap .i64 1) (roundingRaw state) (precisionType state).val
  let next ← nextfloatOne one
  let state ← readContext
  let one ← fromLong (JInt.wrap .i64 1) (roundingRaw state) (precisionType state).val
  arithmetic .sub next one

def floatmin : M BigFloat := do
  let state ← readContext
  let zero ← fromLong (JInt.wrap .i64 0) (roundingRaw state) (precisionType state).val
  nextfloatOne zero
def floatmax : M BigFloat := do
  let state ← readContext
  let infinity := pack (precisionType state) (.inf false)
  prevfloatOne infinity

def parseSignedDecimal (chars : List Char) : Option Int :=
  let (negative,chars) := match chars with
    | '-' :: tail => (true,tail)
    | '+' :: tail => (false,tail)
    | _ => (false,chars)
  if chars.isEmpty then none else do
    let magnitude ← chars.foldlM (fun n c => do
      let digit ← JuliaLean.base.gmp.MPZ.parseDigit 10 c
      pure (n*10+digit)) 0
    pure (if negative then -(magnitude : Int) else magnitude)

def nanPayload (chars : List Char) : Bool :=
  match chars with
  | '(' :: rest =>
    rest.getLast? == some ')' && (rest.dropLast.all (fun c =>
      c.isAlphanum || c == '_'))
  | [] => true
  | _ => false

def parseSpecial (base : Nat) (negative : Bool) (chars : List Char) : Option Exact :=
  let chars := chars.map Char.toLower
  if chars = "@inf@".toList || (base ≤ 16 && (chars = "inf".toList || chars = "infinity".toList)) then
    some (.inf negative)
  else if chars.take 5 = "@nan@".toList && nanPayload (chars.drop 5) then some (.nan negative)
  else if base ≤ 16 && chars.take 3 = "nan".toList && nanPayload (chars.drop 3) then some (.nan negative)
  else none

/-- MPFR manual §5.2 `mpfr_set_str`/`mpfr_strtofr`: exact significand and
radix or binary exponent, automatic base detection, locale point, and special
values. No whitespace is accepted inside numeric data.
https://www.mpfr.org/mpfr-current/mpfr.html#Assignment-Functions -/
def parseExact (text : String) (base : Nat) (localePoint : Char := '.') : Option Exact :=
  let chars := (text.toUTF8.toList.map (fun byte => Char.ofNat byte.toNat)).dropWhile
    JuliaLean.base.gmp.MPZ.cWhitespace
  let (negative,chars) := match chars with
    | '-' :: tail => (true,tail)
    | '+' :: tail => (false,tail)
    | _ => (false,chars)
  match parseSpecial (if base = 0 then 10 else base) negative chars with
  | some special => some special
  | none => do
    let (base,chars) := if base = 0 then
      match chars with
      | '0' :: 'x' :: tail | '0' :: 'X' :: tail => (16,tail)
      | '0' :: 'b' :: tail | '0' :: 'B' :: tail => (2,tail)
      | _ => (10,chars)
      else (base,chars)
    let isExponent := fun c => c == '@' || (base ≤ 10 && (c == 'e' || c == 'E')) ||
      ((base = 2 || base = 16) && (c == 'p' || c == 'P'))
    let significand := chars.takeWhile (fun c => !isExponent c)
    let exponentPart := chars.drop significand.length
    let (exponentBase,exponent) ← match exponentPart with
      | [] => some (base,0)
      | exponentPrefix :: exponentChars => do
        let exponent ← parseSignedDecimal exponentChars
        pure (if exponentPrefix == 'p' || exponentPrefix == 'P' then 2 else base,exponent)
    let (digits,afterPoint,points) ← significand.foldlM
      (fun (m,after,points) c =>
        if c == '.' || c == localePoint then
          if points > 0 then none else some (m,after,points+1)
        else do
          let digit ← JuliaLean.base.gmp.MPZ.parseDigit base c
          pure (m*base+digit,after + if points > 0 then 1 else 0,points)) (0,0,0)
    if significand.length ≤ points then none else
      let n := digits * if exponent ≥ 0 then exponentBase^exponent.toNat else 1
      let d := base^afterPoint * if exponent < 0 then exponentBase^(-exponent).toNat else 1
      some (.finite (if negative then -(n : Int) else n) d negative)

inductive ParseAbort where
  | invalidBase
  deriving DecidableEq, Repr


/--
Julia source: base/mpfr.jl:407-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tryparse(::Type{BigFloat}, s::AbstractString; base::Integer=0, precision::Integer=_precision_with_base_2(BigFloat), rounding::MPFRRoundingMode=rounding_raw(BigFloat))
    !isempty(s) && isspace(s[end]) && return tryparse(BigFloat, rstrip(s); base, precision, rounding)
    z = BigFloat(precision=precision)
    err = ccall((:mpfr_set_str, libmpfr), Int32, (Ref{BigFloat}, Cstring, Int32, MPFRRoundingMode), z, s, base, rounding)
    err == 0 ? z : nothing
end
```
-/
def tryparse (space : Char → Bool) (s : String) (base precision : Int) (rounding : Mode)
    (localePoint : Char := '.') (state : Context) :
    Except ParseAbort (Jl (Option BigFloat) × Context) :=
  let chars := s.toList
  let s := if chars.getLast?.any space then String.ofList ((chars.reverse.dropWhile space).reverse) else s
  let (constructed, state) := (constructInteger valuePrecision precision).run state
  match constructed with
  | .error error => pure (.error error,state)
  | .ok z =>
    if s.toList.contains (Char.ofNat 0) then
      pure (.error (.argumentError "embedded NULs are not allowed in C strings"),state)
    else if base ≠ 0 ∧ !(2 ≤ base ∧ base ≤ 62) then .error .invalidBase
    else match parseExact s base.toNat localePoint with
      | none => pure (.ok none,state)
      | some exact =>
        let result := roundExact state z.prec rounding exact
        pure (.ok (some result.value),{ state with flags := state.flags.merge result.flags })

structure ScientificFormat where
  fractionalDigits : Option Nat := none
  deriving Repr

def floorLog10Rat (n d : Nat) : Int :=
  let k := ((JuliaLean.base.gmp.radixDigits n 10).length : Int)-
    ((JuliaLean.base.gmp.radixDigits d 10).length : Int)
  if k ≥ 0 then (if n < d*10^k.toNat then k-1 else k)
  else if n*10^(-k).toNat < d then k-1 else k

def decimalExponentString (exponent : Int) : String :=
  let digits := JuliaLean.base.gmp.renderMagnitude exponent.natAbs 10
  (if exponent < 0 then "-" else "+") ++
    (if digits.length < 2 then "0" else "") ++ digits

/-- MPFR manual §5.9 `mpfr_asprintf`, the `%Re` and `%.kRe` formats used by
Julia's public BigFloat printers. Missing precision is ceil(p log10(2));
rounding is nearest-even and the decimal point is the current locale point.
The arbitrary printf-format entry point remains untranslated.
https://www.mpfr.org/mpfr-current/mpfr.html#Formatted-Output-Functions -/
def scientificPrimitive (x : BigFloat) (format : ScientificFormat) (localePoint : Char := '.') : String :=
  if isnan x then (if signbit x then "-" else "") ++ "nan"
  else if isinf x then (if signbit x then "-" else "") ++ "inf"
  else
    let digits := format.fractionalDigits.getD
      ((JuliaLean.base.gmp.radixDigits (2^x.prec.val.toNat-1) 10).length)
    let (n,d) := x.value.toRat
    let exponent := if n = 0 then 0 else floorLog10Rat n.natAbs d
    let scale := exponent-(digits : Int)
    let numerator := if scale ≥ 0 then n.natAbs else n.natAbs*10^(-scale).toNat
    let denominator := if scale ≥ 0 then d*10^scale.toNat else d
    let q := numerator/denominator
    let remainder := numerator%denominator
    let q := q + if 2*remainder > denominator ∨ (2*remainder = denominator ∧ q%2=1) then 1 else 0
    let (q,exponent) := if q ≥ 10^(digits+1) then (q/10,exponent+1) else (q,exponent)
    let rendered := JuliaLean.base.gmp.renderMagnitude q 10
    let rendered := String.ofList (List.replicate (digits+1-rendered.length) '0') ++ rendered
    let chars := rendered.toList
    (if signbit x then "-" else "") ++ String.ofList (chars.take 1) ++
      (if digits = 0 then "" else String.singleton localePoint ++ String.ofList (chars.drop 1)) ++
      "e" ++ decimalExponentString exponent

def replaceFirstComma : List Char → List Char
  | [] => []
  | ',' :: rest => '.' :: rest
  | c :: rest => c :: replaceFirstComma rest

structure MPFRStringOps (World Ref Ptr : Type) where
  newPointerRef : World → World × Ref
  asprintf : World → Ref → String → BigFloat → World × Cint
  readPointerRef : World → Ref → World × Ptr
  loadByte : World → Ptr → Nat → World × JInt .u8
  storeByte : World → Ptr → JInt .u8 → Nat → World
  unsafeString : World → Ptr → World × String
  freeString : World → Ptr → World

def replaceNativeComma {World Ref Ptr : Type} (ops : MPFRStringOps World Ref Ptr)
    (world : World) (pointer : Ptr) (index remaining : Nat) : World :=
  match remaining with
  | 0 => world
  | Nat.succ remaining =>
      let (world, byte) := ops.loadByte world pointer index
      if byte == JInt.wrap .u8 44 then
        ops.storeByte world pointer (JInt.wrap .u8 46) index
      else
        replaceNativeComma ops world pointer (index + 1) remaining

/-- MPFR 4.2.2 public C unary entry points declared in `src/mpfr.h`. -/
inductive MPFRUnaryKernel where
  | log1p
  | exp | exp2 | exp10 | expm1 | cosh | sinh | tanh | sech | csch | coth | cbrt
  | log | log2 | log10
  | sin | cos | tan | sec | csc | acos | asin | atan | acosh | asinh | atanh
  | sinpi | cospi | tanpi
  deriving DecidableEq, Repr

inductive MPFRBinaryKernel where
  | pow
  | atan2
  deriving DecidableEq, Repr

inductive MPFRDegreeKernel where
  | atan2u
  deriving DecidableEq, Repr

/-- MPFR 4.2.2 `mpfr_*_u` C entry points declared in `src/mpfr.h`. -/
inductive MPFRDegreeUnaryKernel where
  | sin | cos | tan | asin | acos | atan
  deriving DecidableEq, Repr

/-- MPFR 4.2.2 C constant functions `mpfr_const_log2`, `mpfr_const_pi`,
`mpfr_const_euler`, and `mpfr_const_catalan`, declared in `src/mpfr.h`. -/
inductive MPFRConstantKernel where
  | log2 | pi | euler | catalan
  deriving DecidableEq, Repr

/-- Typed bindings to MPFR 4.2.2 C calls from `src/mpfr.h`. -/
structure AnalyticOps where
  unary : MPFRUnaryKernel → Context → Clong → Mode → BigFloat → PrimitiveResult
  binary : MPFRBinaryKernel → Context → Clong → Mode → BigFloat → BigFloat → PrimitiveResult
  degreeBinary : MPFRDegreeKernel → Context → Clong → Mode → Culong →
    BigFloat → BigFloat → PrimitiveResult
  degreeUnary : MPFRDegreeUnaryKernel → Context → Clong → Mode → Culong →
    BigFloat → PrimitiveResult
  sincos : Context → Clong → Clong → Mode → BigFloat →
    PrimitiveResult × PrimitiveResult
  constant : MPFRConstantKernel → Context → Clong → Mode → PrimitiveResult


inductive FormattingError where
  | julia (error : JlError)
  | assertionError
  deriving Repr, DecidableEq
abbrev FormatResult (A : Type) := Except FormattingError A

/--
Julia source: base/mpfr.jl:1239-1265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prettify_bigfloat(s::String)::String
    mantissa, exponent = eachsplit(s, 'e')
    if !occursin('.', mantissa)
        mantissa = string(mantissa, '.')
    end
    mantissa = rstrip(mantissa, '0')
    if endswith(mantissa, '.')
        mantissa = string(mantissa, '0')
    end
    expo = parse(Int, exponent)
    if -5 < expo < 6
        expo == 0 && return mantissa
        int, frac = eachsplit(mantissa, '.')
        if expo > 0
            expo < length(frac) ?
                string(int, frac[1:expo], '.', frac[expo+1:end]) :
                string(int, frac, '0'^(expo-length(frac)), '.', '0')
        else
            neg = startswith(int, '-')
            neg == true && (int = lstrip(int, '-'))
            @assert length(int) == 1 "length(int) != 1"
            string(neg ? '-' : "", '0', '.', '0'^(-expo-1), int, frac == "0" ? "" : frac)
        end
    else
        string(mantissa, 'e', expo)
    end
end
```
-/
def prettifyBigFloat (s : String) : FormatResult String := do
  let fields := s.splitOn "e"
  let mantissa ← match fields[0]? with | some s => pure s | none => throw (.julia .boundsError)
  let expstr ← match fields[1]? with | some s => pure s | none => throw (.julia .boundsError)
  let mantissa := if mantissa.toList.contains '.' then mantissa else mantissa ++ "."
  let mantissa := String.ofList ((mantissa.toList.reverse.dropWhile (· == '0')).reverse)
  let mantissa := if mantissa.toList.getLast? == some '.' then mantissa ++ "0" else mantissa
  let expo ← match parseSignedDecimal expstr.toList with
    | none => throw (.julia (.argumentError "invalid exponent"))
    | some n =>
      if IntTy.min .i64 ≤ n ∧ n ≤ IntTy.max .i64 then pure n
      else throw (.julia (.argumentError "invalid exponent"))
  if -5 < expo ∧ expo < 6 then
    if expo = 0 then return mantissa
    let fields := mantissa.splitOn "."
    let intPart ← match fields[0]? with | some s => pure s | none => throw (.julia .boundsError)
    let frac ← match fields[1]? with | some s => pure s | none => throw (.julia .boundsError)
    if expo > 0 then
      if expo.toNat < frac.length then
        return intPart ++ String.ofList (frac.toList.take expo.toNat) ++ "." ++
          String.ofList (frac.toList.drop expo.toNat)
      else return intPart ++ frac ++ String.ofList (List.replicate (expo.toNat-frac.length) '0') ++ ".0"
    else
      let negative := intPart.toList.head? == some '-'
      let intPart := if negative then String.ofList (intPart.toList.dropWhile (· == '-')) else intPart
      if intPart.length ≠ 1 then throw .assertionError
      return (if negative then "-" else "") ++ "0." ++
        String.ofList (List.replicate (-expo-1).toNat '0') ++ intPart ++
        (if frac = "0" then "" else frac)
  return mantissa ++ "e" ++ toString expo

/-- Exact rendering for the public scientific formats supported by MPFR. -/
def stringScientific (nonfiniteString : FV .f64 → Jl String) (x : BigFloat)
    (format : ScientificFormat := {}) (localePoint : Char := '.') : FormatResult String := do
  if !isfinite x then return ← (nonfiniteString (toFloat64 x .nearest)).mapError FormattingError.julia
  let text := scientificPrimitive x format localePoint
  let text := String.ofList (replaceFirstComma text.toList)
  prettifyBigFloat text

def stringValue (nonfiniteString : FV .f64 → Jl String) (b : BigFloat) := stringScientific nonfiniteString b

/--
Julia source: base/mpfr.jl:1276-1276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, b::BigFloat) = print(io, string(b))
```
-/
def printBigFloat {IO : Type} (nonfiniteString : FV .f64 → Jl String)
    (print : IO → String → Jl IO) (io : IO) (b : BigFloat) : FormatResult IO := do
  (print io (← stringValue nonfiniteString b)).mapError FormattingError.julia

/--
Julia source: base/mpfr.jl:1277-1283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, b::BigFloat)
    if get(io, :compact, false)::Bool
        print(io, _string(b, 5))
    else
        print(io, _string(b))
    end
end
```
-/
def showBigFloat {IO : Type} (nonfiniteString : FV .f64 → Jl String)
    (compact : IO → Jl Bool) (print : IO → String → Jl IO) (io : IO) (b : BigFloat) : FormatResult IO := do
  if ← (compact io).mapError FormattingError.julia then
    (print io (← stringScientific nonfiniteString b ⟨some 5⟩)).mapError FormattingError.julia
  else (print io (← stringValue nonfiniteString b)).mapError FormattingError.julia

/--
Julia source: base/mpfr.jl:214-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.unsafe_convert(::Type{Ref{BigFloat}}, x::Ptr{BigFloat}) = error("not compatible with mpfr")
Base.unsafe_convert(::Type{Ref{BigFloat}}, x::Ref{BigFloat}) = error("not compatible with mpfr")
Base.cconvert(::Type{Ref{BigFloat}}, x::BigFloat) = x.d # BigFloatData is the Ref type for BigFloat
Base.cconvert(::Type{Ref{BigFloat}}, x::Number) = convert(BigFloat, x).d # avoid default conversion to Ref(BigFloat(x))
Base.cconvert(::Type{Ref{BigFloat}}, x::Ref{BigFloat}) = x[].d
```
-/
def incompatiblePointerRef : Except StorageError BigFloat := .error .incompatibleRef
def incompatibleValueRef : Except StorageError BigFloat := .error .incompatibleRef
def cconvertBigFloat (x : BigFloat) : List Limb := x.d
def cconvertNumber {N : Type} (convert : N → Jl BigFloat) (x : N) : Jl (List Limb) := do
  return (← convert x).d
def cconvertRef (x : BigFloat) : List Limb := x.d

/--
Julia source: base/mpfr.jl:931-932 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# TODO: use a higher-precision BigFloat(pi) here?
rem2pi(x::BigFloat, r::RoundingMode) = rem(x, 2*BigFloat(pi), r)
```
-/
def rem2pi (bigPi : M BigFloat) (remRound : BigFloat → BigFloat → RoundingMode → M BigFloat)
    (x : BigFloat) (r : RoundingMode) : M BigFloat := do
  let twicePi ← integerArithmetic .mul (JInt.wrap .i64 2) (← bigPi)
  remRound x twicePi r

/--
Julia source: base/mpfr.jl:791-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ^(x::BigFloat, y::BigFloat)
    z = BigFloat()
    ccall((:mpfr_pow, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, y, rounding_raw(BigFloat))
    return z
end
```
-/
def powReal (ops : AnalyticOps) (x y : BigFloat) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive (ops.binary .pow state z.prec (roundingRaw state) x y)

def unaryKernel (ops : AnalyticOps) (kernel : MPFRUnaryKernel) (x : BigFloat) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive (ops.unary kernel state z.prec (roundingRaw state) x)

def logarithmKernel (ops : AnalyticOps) (name : String) (kernel : MPFRUnaryKernel)
    (x : BigFloat) : M BigFloat := do
  if !isnan x && compareFP x.value (intValue 0) < 0 then
    throw (.domainError (name ++ " was called with a negative real argument but " ++
      "will only return a complex result if called with a complex argument. Try " ++
      name ++ "(complex(x))."))
  unaryKernel ops kernel x

def trigonometricKernel (ops : AnalyticOps) (kernel : MPFRUnaryKernel)
    (x : BigFloat) : M BigFloat := do
  if isnan x then return x
  let value ← unaryKernel ops kernel x
  if isnan value then throw (.domainError "NaN result for non-NaN input.")
  pure value

def degreeUnaryKernel (ops : AnalyticOps) (kernel : MPFRDegreeUnaryKernel)
    (x : BigFloat) : M BigFloat := do
  if isnan x then return x
  let z ← fresh
  let state ← readContext
  let value ← applyPrimitive (ops.degreeUnary kernel state z.prec (roundingRaw state)
    (JInt.wrap .u64 360) x)
  if isnan value then throw (.domainError "NaN result for non-NaN input.")
  pure value

/--
Julia source: base/mpfr.jl:818-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:exp, :exp2, :exp10, :expm1, :cosh, :sinh, :tanh, :sech, :csch, :coth, :cbrt)
    @eval function $f(x::BigFloat)
        z = BigFloat()
        ccall(($(string(:mpfr_,f)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, rounding_raw(BigFloat))
        return z
    end
end
```
-/

-- f = :exp
def expBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .exp x
-- f = :exp2
def exp2BigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .exp2 x
-- f = :exp10
def exp10BigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .exp10 x
-- f = :expm1
def expm1BigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .expm1 x
-- f = :cosh
def coshBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .cosh x
-- f = :sinh
def sinhBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .sinh x
-- f = :tanh
def tanhBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .tanh x
-- f = :sech
def sechBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .sech x
-- f = :csch
def cschBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .csch x
-- f = :coth
def cothBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .coth x
-- f = :cbrt
def cbrtBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := unaryKernel ops .cbrt x


/--
Julia source: base/mpfr.jl:826-831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sincos_fast(v::BigFloat)
    s = BigFloat()
    c = BigFloat()
    ccall((:mpfr_sin_cos, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), s, c, v, rounding_raw(BigFloat))
    return (s, c)
end
```
-/
def sincosFast (ops : AnalyticOps) (v : BigFloat) : M (BigFloat × BigFloat) := do
  let s ← fresh
  let c ← fresh
  let state ← readContext
  let (sineResult, cosineResult) :=
    ops.sincos state s.prec c.prec (roundingRaw state) v
  let s ← applyPrimitive sineResult
  let c ← applyPrimitive cosineResult
  pure (s, c)

/--
Julia source: base/mpfr.jl:832-832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincos(v::BigFloat) = sincos_fast(v)
```
-/
def sincos (ops : AnalyticOps) (v : BigFloat) : M (BigFloat × BigFloat) :=
  sincosFast ops v

def constantWithPrecision (ops : AnalyticOps) (kernel : MPFRConstantKernel)
    (precision : Int) (mode : Mode) : M BigFloat := do
  let output ← constructInteger valuePrecision precision
  let state ← readContext
  applyPrimitive (ops.constant kernel state output.prec mode)

/--
Julia source: base/mpfr.jl:834-839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# return log(2)
function big_ln2()
    c = BigFloat()
    ccall((:mpfr_const_log2, libmpfr), Cint, (Ref{BigFloat}, MPFRRoundingMode), c, MPFR.rounding_raw(BigFloat))
    return c
end
```
-/
def bigLn2 (ops : AnalyticOps) : M BigFloat := do
  let state ← readContext
  constantWithPrecision ops .log2 (precisionType state).val (roundingRaw state)

/--
Julia source: base/mpfr.jl:853-853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ldexp(x::BigFloat, n::Integer) = x * exp2(BigFloat(n))
```
-/
def ldexpInteger {I U : Type} (ops : JuliaLean.base.gmp.IntegerInput I U)
    (exp2 : BigFloat → M BigFloat) (x : BigFloat) (n : I) : M BigFloat := do
  let state ← readContext
  let exponent ← fromInteger ops n (roundingRaw state) (precisionType state).val
  let power ← exp2 exponent
  arithmetic .mul x power

/--
Julia source: base/mpfr.jl:871-882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:log, :log2, :log10)
    @eval function $f(x::BigFloat)
        if x < 0
            throw(DomainError(x, string($f, " was called with a negative real argument but ",
                              "will only return a complex result if called ",
                              "with a complex argument. Try ", $f, "(complex(x)).")))
        end
        z = BigFloat()
        ccall(($(string(:mpfr_,f)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, rounding_raw(BigFloat))
        return z
    end
end
```
-/

-- f = :log
def logBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  logarithmKernel ops "log" .log x
-- f = :log2
def log2BigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  logarithmKernel ops "log2" .log2 x
-- f = :log10
def log10BigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  logarithmKernel ops "log10" .log10 x

/--
Julia source: base/mpfr.jl:884-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function log1p(x::BigFloat)
    if x < -1
        throw(DomainError(x, string("log1p was called with a real argument < -1 but ",
                          "will only return a complex result if called ",
                          "with a complex argument. Try log1p(complex(x)).")))
    end
    z = BigFloat()
    ccall((:mpfr_log1p, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, rounding_raw(BigFloat))
    return z
end
```
-/
def log1p (ops : AnalyticOps) (x : BigFloat) : M BigFloat := do
  if !isnan x && compareFP x.value (intValue (-1)) < 0 then
    throw (.domainError "log1p was called with a real argument < -1 but will only return a complex result if called with a complex argument. Try log1p(complex(x)).")
  let z ← fresh
  let state ← readContext
  applyPrimitive (ops.unary .log1p state z.prec (roundingRaw state) x)

/--
Julia source: base/mpfr.jl:943-954 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Functions for which NaN results are converted to DomainError, following Base
for f in (:sin, :cos, :tan, :sec, :csc, :acos, :asin, :atan, :acosh, :asinh, :atanh, :sinpi, :cospi, :tanpi)
    @eval begin
        function ($f)(x::BigFloat)
            isnan(x) && return x
            z = BigFloat()
            ccall(($(string(:mpfr_,f)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, x, rounding_raw(BigFloat))
            isnan(z) && throw(DomainError(x, "NaN result for non-NaN input."))
            return z
        end
    end
end
```
-/

-- f = :sin
def sinBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .sin x
-- f = :cos
def cosBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .cos x
-- f = :tan
def tanBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .tan x
-- f = :sec
def secBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .sec x
-- f = :csc
def cscBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .csc x
-- f = :acos
def acosBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .acos x
-- f = :asin
def asinBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .asin x
-- f = :atan
def atanBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .atan x
-- f = :acosh
def acoshBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .acosh x
-- f = :asinh
def asinhBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .asinh x
-- f = :atanh
def atanhBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .atanh x
-- f = :sinpi
def sinpiBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .sinpi x
-- f = :cospi
def cospiBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .cospi x
-- f = :tanpi
def tanpiBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat := trigonometricKernel ops .tanpi x



/--
Julia source: base/mpfr.jl:957-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function atan(y::BigFloat, x::BigFloat)
    z = BigFloat()
    ccall((:mpfr_atan2, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, MPFRRoundingMode), z, y, x, rounding_raw(BigFloat))
    return z
end
```
-/
def atan (ops : AnalyticOps) (y x : BigFloat) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive (ops.binary .atan2 state z.prec (roundingRaw state) y x)

/--
Julia source: base/mpfr.jl:963-981 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# degree functions
for f in (:sin, :cos, :tan)
    @eval begin
        function ($(Symbol(f,:d)))(x::BigFloat)
            isnan(x) && return x
            z = BigFloat()
            ccall(($(string(:mpfr_,f,:u)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Culong, MPFRRoundingMode), z, x, 360, rounding_raw(BigFloat))
            isnan(z) && throw(DomainError(x, "NaN result for non-NaN input."))
            return z
        end
        function ($(Symbol(:a,f,:d)))(x::BigFloat)
            isnan(x) && return x
            z = BigFloat()
            ccall(($(string(:mpfr_a,f,:u)), libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Culong, MPFRRoundingMode), z, x, 360, rounding_raw(BigFloat))
            isnan(z) && throw(DomainError(x, "NaN result for non-NaN input."))
            return z
        end
    end
end
```
-/

-- f = :sin
def sindBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  degreeUnaryKernel ops .sin x
-- f = :cos
def cosdBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  degreeUnaryKernel ops .cos x
-- f = :tan
def tandBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  degreeUnaryKernel ops .tan x
-- f = :sin
def asindBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  degreeUnaryKernel ops .asin x
-- f = :cos
def acosdBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  degreeUnaryKernel ops .acos x
-- f = :tan
def atandBigFloat (ops : AnalyticOps) (x : BigFloat) : M BigFloat :=
  degreeUnaryKernel ops .atan x

/--
Julia source: base/mpfr.jl:982-986 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function atand(y::BigFloat, x::BigFloat)
    z = BigFloat()
    ccall((:mpfr_atan2u, libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Ref{BigFloat}, Culong, MPFRRoundingMode), z, y, x, 360, rounding_raw(BigFloat))
    return z
end
```
-/
def atand (ops : AnalyticOps) (y x : BigFloat) : M BigFloat := do
  let z ← fresh
  let state ← readContext
  applyPrimitive
    (ops.degreeBinary .atan2u state z.prec (roundingRaw state) (JInt.wrap .u64 360) y x)

/--
Julia source: base/mpfr.jl:1221-1237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function string_mpfr(x::BigFloat, fmt::String)
    pc = Ref{Ptr{UInt8}}()
    n = ccall((:mpfr_asprintf,libmpfr), Cint,
              (Ptr{Ptr{UInt8}}, Ptr{UInt8}, Ref{BigFloat}...),
              pc, fmt, x)
    p = pc[]
    # convert comma decimal separator to dot
    for i = 1:n
        if unsafe_load(p, i) == UInt8(',')
            unsafe_store!(p, '.', i)
            break
        end
    end
    str = unsafe_string(p)
    ccall((:mpfr_free_str, libmpfr), Cvoid, (Ptr{UInt8},), p)
    return str
end
```
-/
def stringMpfr {World Ref Ptr : Type} (ops : MPFRStringOps World Ref Ptr)
    (world : World) (x : BigFloat) (format : String) : World × String :=
  let (world, pc) := ops.newPointerRef world
  let (world, n) := ops.asprintf world pc format x
  let (world, pointer) := ops.readPointerRef world pc
  let world := replaceNativeComma ops world pointer 1 n.val.toNat
  let (world, text) := ops.unsafeString world pointer
  let world := ops.freeString world pointer
  (world, text)

-- Untranslated: raw Memory construction includes a self-relative native pointer and initialization side effect.
-- UNTRANSLATED
-- Source: base/mpfr.jl:149-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     global function _BigFloat(d::Memory{Limb})
--         Base.unsafe_convert(Ref{BigFloat}, BigFloatData(d)) # force early initialization of pointer field of z.d
--         return new(d)
--     end
-- /Source

/-- The `BigFloatData{Limb}` wrapper around the memory allocation backing a `BigFloat`. -/
structure BigFloatData (Memory : Type) where
  d : Memory

/-- Typed runtime operations for MPFR pointer conversion and repair of the embedded limb pointer.
The preservation callback keeps the allocation live while the pointer is loaded or stored. -/
structure BigFloatPointerOps (Memory LimbPointer PointerPointer BigFloatRef Order : Type) where
  memoryToLimbPointer : Memory → LimbPointer
  toPointerPointer : LimbPointer → PointerPointer
  addLimbOffset : LimbPointer → Int → LimbPointer
  addPointerOffset : PointerPointer → Int → PointerPointer
  pointerEqual : LimbPointer → LimbPointer → Bool
  unsafeLoadPointer : PointerPointer → Order → Jl LimbPointer
  unsafeStorePointer : PointerPointer → LimbPointer → Order → Jl Unit
  bigFloatRef : LimbPointer → BigFloatRef
  preserve : {A : Type} → Memory → (Unit → Jl A) → Jl A
  offsetD : Int
  offsetP : Int
  monotonic : Order

/--
Julia source: base/mpfr.jl:219-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.unsafe_convert(::Type{Ref{BigFloat}}, x::BigFloatData)
    d = getfield(x, :d)
    p = Base.unsafe_convert(Ptr{Limb}, d)
    dptrptr = Ptr{Ptr{Limb}}(p) + offset_d
    dptr = p + offset_p
    GC.@preserve d if unsafe_load(dptrptr, :monotonic) != dptr # make sure this pointer value was recomputed after any deserialization or copying
        unsafe_store!(dptrptr, dptr, :monotonic) # :monotonic ensure that TSAN knows that this isn't a data race
    end
    return Ptr{BigFloat}(p)
end
```
-/

def unsafeConvertBigFloatRef
    {Memory LimbPointer PointerPointer BigFloatRef Order : Type}
    (ops : BigFloatPointerOps Memory LimbPointer PointerPointer BigFloatRef Order)
    (x : BigFloatData Memory) : Jl BigFloatRef := do
  let d := x.d
  let p := ops.memoryToLimbPointer d
  let dptrptr := ops.addPointerOffset (ops.toPointerPointer p) ops.offsetD
  let dptr := ops.addLimbOffset p ops.offsetP
  let _ ← ops.preserve d (fun _ => do
    let current ← ops.unsafeLoadPointer dptrptr ops.monotonic
    if !ops.pointerEqual current dptr then
      ops.unsafeStorePointer dptrptr dptr ops.monotonic
    else pure ())
  pure (ops.bigFloatRef p)


/--
Julia source: base/mpfr.jl:229-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.unsafe_convert(::Type{Ptr{Limb}}, fd::BigFloatData) = Base.unsafe_convert(Ptr{Limb}, getfield(fd, :d)) + offset_p
```
-/

def unsafeConvertBigFloatLimbPtr
    {Memory LimbPointer PointerPointer BigFloatRef Order : Type}
    (ops : BigFloatPointerOps Memory LimbPointer PointerPointer BigFloatRef Order)
    (fd : BigFloatData Memory) : Jl LimbPointer := do
  let p := ops.memoryToLimbPointer fd.d
  pure (ops.addLimbOffset p ops.offsetP)

/--
Julia source: base/mpfr.jl:428-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unchecked_cast(T, x::BigFloat, r::RoundingMode) = _unchecked_cast(T, x, convert(MPFRRoundingMode, r))
```
-/
def uncheckedCastBitsPublic (t : IntTy) (x : BigFloat) (r : RoundingMode) : M Int := do
  uncheckedCastBits t x (← liftJl (toMPFR r))
def uncheckedCastBigIntPublic (x : BigFloat) (r : RoundingMode) : M BigInt := do
  uncheckedCastBigInt x (← liftJl (toMPFR r))

/--
Julia source: base/mpfr.jl:1267-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _string(x::BigFloat, fmt::String)::String
    isfinite(x) || return string(Float64(x))
    _prettify_bigfloat(string_mpfr(x, fmt))
end
```
-/
def stringWithFormat {World Ref Ptr : Type} (ops : MPFRStringOps World Ref Ptr)
    (nonfiniteString : FV .f64 → Jl String) (mode : Mode) (world : World)
    (x : BigFloat) (format : String) : World × FormatResult String :=
  if !isfinite x then
    (world, (nonfiniteString (toFloat64 x mode)).mapError FormattingError.julia)
  else
    let (world, text) := stringMpfr ops world x format
    (world, prettifyBigFloat text)

/--
Julia source: base/mpfr.jl:1272-1272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_string(x::BigFloat, k::Integer) = _string(x, "%.$(k)Re")
```
-/
def stringWithPrecision {I World Ref Ptr : Type} (integerString : I → String)
    (ops : MPFRStringOps World Ref Ptr) (nonfiniteString : FV .f64 → Jl String)
    (mode : Mode) (world : World) (x : BigFloat) (precision : I) : World × FormatResult String :=
  stringWithFormat ops nonfiniteString mode world x
    ("%." ++ integerString precision ++ "Re")
/--
Julia source: base/mpfr.jl:1271-1271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_string(x::BigFloat) = _string(x, "%Re")
```
-/
def stringWithDefaultFormat {World Ref Ptr : Type} (ops : MPFRStringOps World Ref Ptr)
    (nonfiniteString : FV .f64 → Jl String) (mode : Mode) (world : World)
    (x : BigFloat) : World × FormatResult String :=
  stringWithFormat ops nonfiniteString mode world x "%Re"

/--
Julia source: base/mpfr.jl:1274-1274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(b::BigFloat) = _string(b)
```
-/
def stringBigFloat {World Ref Ptr : Type} (ops : MPFRStringOps World Ref Ptr)
    (nonfiniteString : FV .f64 → Jl String) (mode : Mode) (world : World)
    (b : BigFloat) : World × FormatResult String :=
  stringWithDefaultFormat ops nonfiniteString mode world b

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module MPFR
-- 
-- export
--     BigFloat,
--     setprecision
-- 
-- import
--     .Base: *, +, -, /, <, <=, ==, >, >=, ^, ceil, cmp, convert, copysign, div,
--         inv, exp, exp2, exponent, factorial, floor, fma, muladd, hypot, isinteger,
--         isfinite, isinf, isnan, issubnormal, ldexp, log, log2, log10, max, min, modf,
--         nextfloat, prevfloat, promote_rule, rem, rem2pi, round, show, float,
--         sum, sqrt, string, print, trunc, precision, _precision, exp10, expm1, log1p,
--         eps, signbit, sign, sin, cos, sincos, tan, sec, csc, acos, asin, atan,
--         cosh, sinh, tanh, sech, csch, coth, acosh, asinh, atanh, lerpi,
--         cbrt, typemax, typemin, unsafe_trunc, floatmin, floatmax, rounding,
--         setrounding, maxintfloat, widen, significand, frexp, tryparse, iszero,
--         isone, big, decompose, minmax, _precision_with_base_2,
--         sinpi, cospi, sincospi, tanpi, sind, cosd, tand, asind, acosd, atand,
--         uinttype, exponent_max, exponent_min, ieee754_representation, significand_mask,
--         ispositive, isnegative
-- 
-- import .Core: AbstractFloat
-- import .Base: Rational, Float16, Float32, Float64, Bool
-- 
-- using .Base.Libc
-- import ..Rounding: Rounding,
--     rounding_raw, setrounding_raw, rounds_to_nearest, rounds_away_from_zero,
--     tie_breaker_is_to_even, correct_rounding_requires_increment
-- 
-- import ..GMP: ClongMax, CulongMax, CdoubleMax, Limb, libgmp, BigInt
-- 
-- import ..FastMath.sincos_fast
-- 
-- if Sys.iswindows()
--     const libmpfr = "libmpfr-6.dll"
-- elseif Sys.isapple()
--     const libmpfr = "@rpath/libmpfr.6.dylib"
-- else
--     const libmpfr = "libmpfr.so.6"
-- end
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:57-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     MPFR.MPFRRoundingMode
-- 
-- Matches the `mpfr_rnd_t` enum provided by MPFR, see
-- https://www.mpfr.org/mpfr-current/mpfr.html#Rounding-Modes
-- 
-- This is for internal use, and ensures that `ROUNDING_MODE[]` is type-stable.
-- """
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:111-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const ROUNDING_MODE = Ref{MPFRRoundingMode}(MPFRRoundNearest)
-- const CURRENT_ROUNDING_MODE = Base.ScopedValues.ScopedValue{MPFRRoundingMode}()
-- const DEFAULT_PRECISION = Ref{Clong}(256)
-- const CURRENT_PRECISION = Base.ScopedValues.ScopedValue{Clong}()
-- # Basic type and initialization definitions
-- 
-- # Warning: the constants are MPFR implementation details from
-- # `src/mpfr-impl.h`, search for `MPFR_EXP_ZERO`.
-- const mpfr_special_exponent_zero = typemin(Clong) + true
-- const mpfr_special_exponent_nan = mpfr_special_exponent_zero + true
-- const mpfr_special_exponent_inf = mpfr_special_exponent_nan + true
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:173-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
-- Segment of raw words of bits interpreted as a big integer. Less
-- significant words come first. Each word is in machine-native bit-order.
-- """
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:198-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # While BigFloat (like all Numbers) is considered immutable, for practical reasons
-- # of writing the algorithms on it we allow mutating sign and exp
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:212-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Ref interface: make sure the conversion to C is done properly
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:243-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- include("rawbigfloats.jl")
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:256-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     BigFloat(x::Union{Real, AbstractString} [, rounding::RoundingMode=rounding(BigFloat)]; [precision::Integer=precision(BigFloat)])
-- 
-- Create an arbitrary precision floating point number from `x`, with precision
-- `precision`. The `rounding` argument specifies the direction in which the result should be
-- rounded if the conversion cannot be done exactly. If not provided, these are set by the current global values.
-- 
-- `BigFloat(x::Real)` is the same as `convert(BigFloat,x)`, except if `x` itself is already
-- `BigFloat`, in which case it will return a value with the precision set to the current
-- global precision; `convert` will always return `x`.
-- 
-- `BigFloat(x::AbstractString)` is identical to [`parse`](@ref). This is provided for
-- convenience since decimal literals are converted to `Float64` when parsed, so
-- `BigFloat(2.1)` may not yield what you expect.
-- 
-- See also:
-- - [`@big_str`](@ref)
-- - [`rounding`](@ref) and [`setrounding`](@ref)
-- - [`precision`](@ref) and [`setprecision`](@ref)
-- 
-- !!! compat "Julia 1.1"
--     `precision` as a keyword argument requires at least Julia 1.1.
--     In Julia 1.0 `precision` is the second positional argument (`BigFloat(x, precision)`).
-- 
-- # Examples
-- ```jldoctest
-- julia> BigFloat(2.1) # 2.1 here is a Float64
-- 2.100000000000000088817841970012523233890533447265625
-- 
-- julia> BigFloat("2.1") # the closest BigFloat to 2.1
-- 2.099999999999999999999999999999999999999999999999999999999999999999999999999986
-- 
-- julia> BigFloat("2.1", RoundUp)
-- 2.100000000000000000000000000000000000000000000000000000000000000000000000000021
-- 
-- julia> BigFloat("2.1", RoundUp, precision=128)
-- 2.100000000000000000000000000000000000007
-- ```
-- """
-- BigFloat(x, r::RoundingMode)
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:318-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # convert to BigFloat
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:329-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:373-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:426-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## BigFloat -> Integer
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:448-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:478-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:493-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:556-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:564-564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:572-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Basic arithmetic without promotion
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:671-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:687-689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # div
-- # BigFloat
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:746-748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # More efficient commutative operations
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:774-774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:780-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:790-790 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:796-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:817-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:840-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:854-854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:870-870 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:894-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # For `min`/`max`, general fallback for `AbstractFloat` is good enough.
-- # Only implement `minmax` and `_extrema_rf` to avoid repeated calls.
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:911-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:918-918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:930-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:933-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:942-942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:987-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # Utility functions
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1015-1015 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1030-1032 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Note: this inlines the implementation of `mpfr_signbit` to avoid a
-- # `ccall`.
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1034-1034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1040-1040 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1045-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1049-1049 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1052-1068 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     setprecision([T=BigFloat,] precision::Int; base=2)
-- 
-- Set the precision (in bits, by default) to be used for `T` arithmetic.
-- If `base` is specified, then the precision is the minimum required to give
-- at least `precision` digits in the given `base`.
-- 
-- !!! warning
-- 
--     This function is not thread-safe. It will affect code running on all threads, but
--     its behavior is undefined if called concurrently with computations that use the
--     setting.
-- 
-- !!! compat "Julia 1.8"
--     The `base` keyword requires at least Julia 1.8.
-- """
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1077-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1080-1080 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1094-1094 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1110-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1128-1128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1147-1147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1150-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1169-1169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1174-1199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     setprecision(f::Function, [T=BigFloat,] precision::Integer; base=2)
-- 
-- Change the `T` arithmetic precision (in the given `base`) for the duration of `f`.
-- It is logically equivalent to:
-- 
--     old = precision(BigFloat)
--     setprecision(BigFloat, precision)
--     f()
--     setprecision(BigFloat, old)
-- 
-- Often used as `setprecision(T, precision) do ... end`
-- 
-- Note: `nextfloat()`, `prevfloat()` do not use the precision mentioned by
-- `setprecision`.
-- 
-- !!! warning
--     There is a fallback implementation of this method that calls `precision`
--     and `setprecision`, but it should no longer be relied on. Instead, you
--     should define the 3-argument form directly in a way that uses `ScopedValue`,
--     or recommend that callers use `ScopedValue` and `@with` themselves.
-- 
-- !!! compat "Julia 1.8"
--     The `base` keyword requires at least Julia 1.8.
-- """
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1213-1213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1220-1220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1238-1238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1266-1266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1284-1285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # get/set exponent min/max
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1297-1297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1306-1306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1319-1319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1324-1325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # flags
-- /Source

-- Untranslated: exact analytic/string primitive, runtime pointer operation, or source scaffolding.
-- UNTRANSLATED
-- Source: base/mpfr.jl:1333-1334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end #module
-- /Source

end JuliaLean.base.mpfr

namespace JuliaLean.base.gmp

-- placed here to break an import cycle with gmp
-- Source: base/gmp.jl:565-565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(x::BigInt, y::Union{ClongMax,CulongMax}) = float(x)/y
-- /Source
def divideMixedRightMPFR {t : IntTy} (_dispatch : IsClongMax t ∨ IsCulongMax t)
    (x : BigInt) (y : JInt t) : mpfr.M mpfr.BigFloat :=
  divideMixedRightM mpfr.abstractFloatBigInt (mpfr.arithmeticInteger .div) x y

-- placed here to break an import cycle with gmp
-- Source: base/gmp.jl:566-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(x::Union{ClongMax,CulongMax}, y::BigInt) = x/float(y)
-- /Source
def divideMixedLeftMPFR {t : IntTy} (_dispatch : IsClongMax t ∨ IsCulongMax t)
    (x : JInt t) (y : BigInt) : mpfr.M mpfr.BigFloat :=
  divideMixedLeftM mpfr.abstractFloatBigInt (mpfr.integerArithmetic .div) x y

end JuliaLean.base.gmp
namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-- Julia's rounding modes, `base/rounding.jl:37-109`. -/
inductive RMode where
  | nearest | toZero | up | down | fromZero | nearestTiesAway | nearestTiesUp
  deriving DecidableEq, Repr

/-- `MPFRRoundingMode`, `base/mpfr.jl:66-73` (`MPFRRoundFaithful` is never produced). -/
inductive MPFRMode where
  | rndN | rndZ | rndU | rndD | rndA
  deriving DecidableEq, Repr

/-- `convert(MPFRRoundingMode, r)`, `base/mpfr.jl:75-79`: only five modes have a method. -/
def toMPFR : RMode → Jl MPFRMode
  | .nearest => .ok .rndN
  | .toZero => .ok .rndZ
  | .up => .ok .rndU
  | .down => .ok .rndD
  | .fromZero => .ok .rndA
  | _ => .error (.methodError "convert")

/-- `_opposite_round`, `base/mpfr.jl:401-405`. -/
def opposite : MPFRMode → MPFRMode
  | .rndU => .rndD
  | .rndD => .rndU
  | m => m

/-- A BigFloat value (its precision is carried separately). -/
inductive BF where
  | nan
  | inf (neg : Bool)
  | zero (neg : Bool)
  | fin (m : Int) (e : Int)
  deriving DecidableEq, Repr

/-- The canonical finite value `m * 2^e`: factors of two move from `m` into `e`. -/
def mkFin (m : Int) (e : Int) : BF :=
  if m = 0 then .zero false else go m e (m.natAbs.log2 + 1)
where
  go (m : Int) (e : Int) : Nat → BF
    | 0 => .fin m e
    | k + 1 => if m % 2 = 0 then go (m / 2) (e + 1) k else .fin m e

/-- The exact value `n / d` of a finite value (`d > 0`, a power of two). -/
def BF.toRat : BF → Int × Nat
  | .fin m e => if 0 ≤ e then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  | _ => (0, 1)

def BF.signbit : BF → Bool
  | .nan => false
  | .inf s => s
  | .zero s => s
  | .fin m _ => decide (m < 0)

def BF.isnan : BF → Bool
  | .nan => true
  | _ => false

/-- `n / d` (`n ≠ 0`, `d > 0`) correctly rounded to `p` significant bits in mode `r`, ties to
even for `rndN` (MPFR manual §4.4). -/
def roundP (p : Nat) (r : MPFRMode) (n : Int) (d : Nat) : BF :=
  if n = 0 then .zero false
  else
    let neg := decide (n < 0)
    let a := n.natAbs
    let e := Fl.floorLog2Rat a d
    let k : Int := e + 1 - p
    let num := if 0 ≤ k then a else a * 2 ^ (-k).toNat
    let den := if 0 ≤ k then d * 2 ^ k.toNat else d
    let q := num / den
    let rm := num % den
    let up := match r with
      | .rndN => decide (2 * rm > den) || (decide (2 * rm = den) && q % 2 == 1)
      | .rndZ => false
      | .rndA => rm != 0
      | .rndU => rm != 0 && !neg
      | .rndD => rm != 0 && neg
    let q := if up then q + 1 else q
    mkFin (if neg then -(q : Int) else q) k

/-- `mpfr_div` at precision `p` in mode `r` (MPFR manual §5.5), for the operand kinds that
arise from `BigFloat(::Rational)`. -/
def divBF (p : Nat) (r : MPFRMode) : BF → BF → BF
  | .fin m1 e1, .fin m2 e2 =>
    let (n1, d1) := (BF.fin m1 e1).toRat
    let (n2, d2) := (BF.fin m2 e2).toRat
    roundP p r (n1 * d2 * n2.sign) (d1 * n2.natAbs)
  | .zero s, .fin m _ => .zero (s != decide (m < 0))
  | .fin m _, .zero s => .inf (decide (m < 0) != s)
  | .zero _, .zero _ => .nan
  | _, _ => .nan

/-- `BigFloat(x::Integer, r; precision = p)` (`mpfr_set_z`/`mpfr_set_si`, `base/mpfr.jl:320-386`). -/
def ofInt (p : Nat) (r : MPFRMode) (n : Int) : BF := roundP p r n 1

/-- `BigFloat(x::Rational, r; precision = p)`, `base/mpfr.jl:393-400`: the numerator is
converted in mode `r`, the denominator in `_opposite_round(r)`, both at precision `p`, and
their quotient is rounded in mode `r`. -/
def ofRational (p : Nat) (r : MPFRMode) (num : Int) (den : Nat) : BF :=
  divBF p r (ofInt p r num) (ofInt p (opposite r) den)
/-! ## Comparison with Float64 (`base/mpfr.jl:1009-1024`, `base/operators.jl:199,240`) -/

/-- `BigFloat(y::Float64)` (exact for every precision ≥ 53). -/
def ofF64 (y : Fl double) : BF :=
  if y.isnan then .nan
  else if y.isinf then .inf y.signbit
  else if y.iszero then .zero y.signbit
  else
    let (n, d) := y.toRat
    mkFin n (-(d.log2 : Int))

/-- Numeric three-way comparison of two non-NaN values; zeros of either sign are equal. -/
def numCmp (a b : BF) : Int :=
  let key : BF → Int × Int × Nat := fun
    | .inf s => if s then (-1, 0, 1) else (1, 0, 1)
    | v => (0, v.toRat.1, v.toRat.2)
  let (ka, na, da) := key a
  let (kb, nb, db) := key b
  if ka ≠ kb then (if ka < kb then -1 else 1)
  else if ka ≠ 0 then 0
  else
    let l := na * db
    let r := nb * da
    if l < r then -1 else if l = r then 0 else 1

/-- `cmp(x::BigFloat, y::CdoubleMax)`, `base/mpfr.jl:1009-1013`. `mpfr_cmp_d` compares
numerically and returns ±1 or 0 (MPFR manual §5.6). -/
def cmpF64 (x : BF) (y : Fl double) : Int :=
  if x.isnan then (if y.isnan then 0 else 1)
  else if y.isnan then -1
  else numCmp x (ofF64 y)

/-- `isless(x::AbstractFloat, y::AbstractFloat)`, `base/operators.jl:240`, with `x < y` the
numeric `<(::BigFloat, ::CdoubleMax)` (`base/mpfr.jl:1023`) and `signless`,
`base/operators.jl:199`. -/
def islessBF (x y : BF) : Bool :=
  (!x.isnan && (y.isnan || (x.signbit && !y.signbit))) ||
    (!x.isnan && !y.isnan && numCmp x y < 0)
/-! ## Rounding to integers (`base/mpfr.jl:428-468`) -/

/-- `n / d` (`d > 0`) rounded to an integer in mode `r`, as documented for each
`RoundingMode` (`base/rounding.jl:37-109`). -/
def roundIntSpec (r : RMode) (n : Int) (d : Nat) : Int :=
  let fl := n.fdiv d
  let rm := n - fl * d
  let tie := 2 * rm = (d : Int)
  let above := 2 * rm > (d : Int)
  match r with
  | .down => fl
  | .up => if rm = 0 then fl else fl + 1
  | .toZero => if rm = 0 ∨ 0 ≤ n then fl else fl + 1
  | .fromZero => if rm = 0 ∨ n < 0 then fl else fl + 1
  | .nearest => if above ∨ (tie ∧ fl % 2 ≠ 0) then fl + 1 else fl
  | .nearestTiesAway => if above ∨ (tie ∧ 0 ≤ n) then fl + 1 else fl
  | .nearestTiesUp => if above ∨ tie then fl + 1 else fl

/-- The `RoundingMode` an MPFR mode stands for. -/
def MPFRMode.toR : MPFRMode → RMode
  | .rndN => .nearest
  | .rndZ => .toZero
  | .rndU => .up
  | .rndD => .down
  | .rndA => .fromZero

/-- `round(T, x::BigFloat, r)` for `T = Int64`, `base/mpfr.jl:449-456,465-466`:
`_unchecked_cast` converts `r` to an MPFR mode, rounds with `mpfr_get_z` (MPFR manual §5.4),
and the range check throws `InexactError`. -/
def roundToInt (t : IntTy) (x : BF) (r : RMode) : Jl (JInt t) := do
  let mr ← toMPFR r
  match x with
  | .nan | .inf _ => .error (.inexactError "round")
  | .zero _ => JInt.convert (t.name) t 0
  | .fin m e =>
    let (n, d) := (BF.fin m e).toRat
    match JInt.convert (t.name) t (roundIntSpec mr.toR n d) with
    | .ok v => .ok v
    | .error _ => .error (.inexactError "round")

/-- `Rational{BigInt}(x::AbstractFloat)` for `x = Float64`, `base/mpfr.jl:565-571`. NaN builds
`zero(BigInt)//zero(BigInt)`, which `Rational{BigInt}(num, den)` rejects with
`ArgumentError` (`base/gmp.jl:1004-1006`). -/
def rationalBigOfF64 (x : Fl double) : Jl QBig :=
  if x.isnan then .error (.argumentError "invalid rational: zero(BigInt)//zero(BigInt)")
  else if x.isinf then .ok ⟨if x.signbit then -1 else 1, 0⟩
  else if x.iszero then .ok ⟨0, 1⟩
  else
    let (n, d) := x.toRat
    let g := Nat.gcd n.natAbs d
    .ok ⟨n / g, d / g⟩
/-! ## `tryparse(BigFloat, s; base)` (`base/mpfr.jl:407-412`) -/

/-- A call's outcome: a value, a thrown exception, or a process abort. -/
inductive Outcome (α : Type) where
  | ok (a : α)
  | throw (e : JlError)
  | abort
  deriving DecidableEq, Repr

/-- `tryparse(BigFloat, s; base)`, `base/mpfr.jl:407-412`. Trailing whitespace is stripped first;
the `Cstring` conversion of the argument throws `ArgumentError` for embedded NULs
(`base/strings/cstring.jl:85`); `mpfr_set_str` asserts `base == 0 || 2 <= base <= 62`
(MPFR `strtofr.c`, `MPFR_ASSERTN`, active in release builds), aborting the process otherwise.
For a valid base, `setStr` is MPFR's documented parser (MPFR manual §5.2 `mpfr_strtofr`); its
numeric grammar does not matter for the properties below, so it is a parameter. -/
def tryparseBF (setStr : List Char → Nat → Option BF) (s : List Char) (base : Int) :
    Outcome (Option BF) :=
  let s := (s.reverse.dropWhile isSpace).reverse
  if s.contains (Char.ofNat 0) then .throw (.argumentError "embedded NULs are not allowed in C strings")
  else if ¬ (base = 0 ∨ (2 ≤ base ∧ base ≤ 62)) then .abort
  else .ok (setStr s base.toNat)
end JuliaLean.BigNums
