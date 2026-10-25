import JuliaLean.Float.Extras

/-!
Deterministic differential corpus for the exact binary64 model. The Julia oracle uses
identical bit words, pairings, rounding modes, scales, steps, and integer types.
All results are printed as decimal UInt64 bit patterns; NaNs are normalized.
-/
namespace JuliaLean.Float.Validation

private def mask : Nat := 2^64-1
private def initialWords : Array Nat := #[
  0,1,2,0x000ffffffffffffe,0x000fffffffffffff,0x0010000000000000,
  0x0010000000000001,0x3fdfffffffffffff,0x3fe0000000000000,
  0x3fe0000000000001,0x3ff0000000000000,0x3ff0000000000001,
  0x3ff7ffffffffffff,0x3ff8000000000000,0x4004000000000000,
  0x433fffffffffffff,0x4340000000000000,0x7feffffffffffffe,
  0x7fefffffffffffff,0x7ff0000000000000,0x7ff0000000000001,
  0x7ff8000000000000,0x7fffffffffffffff]

/-- 2,194 inputs: signed edge values, integer boundaries, and reproducible random words. -/
def words : Array Nat := Id.run do
  let mut ws := initialWords ++ initialWords.map (· + 2^63)
  for k in #[7,8,15,16,31,32,63,64,127,128] do
    let b := (k+1023)*2^52
    for j in #[-2,-1,0,1,2] do
      let w := (Int.ofNat b + j).toNat
      ws := ws.push w |>.push (w+2^63)
  let mut state := 0x243f6a8885a308d3
  for _ in [:2048] do
    state := (state*6364136223846793005+1442695040888963407) % (mask+1)
    ws := ws.push state
  return ws

private def out (x : F64) : String :=
  if F64.isnan x then "nan" else toString (F64.toBits x)
private def outBool (b : Bool) : String := if b then "true" else "false"
private def outError : JlError → String
  | .inexactError _ => "inexact"
  | .domainError _ => "domain"
  | .methodError _ => "method"
  | e => s!"unexpected:{repr e}"
private def outJl (f : α → String) : Jl α → String
  | .ok x => f x
  | .error e => outError e
private def modes : Array Rounding :=
  #[.RoundNearest,.RoundNearestTiesAway,.RoundUp,.RoundDown,.RoundToZero]
private def types : Array IntTy := #[.i8,.i16,.i32,.i64,.i128,.u8,.u16,.u32,.u64,.u128]
private def scales : Array Int := #[-2200,-1075,-1074,-1022,-53,-1,0,1,52,1023,1074,2200]
private def steps : Array Int := #[-10000,-2,-1,0,1,2,10000]
private def emit (i : Nat) (op value : String) : IO Unit :=
  IO.println s!"{i} {op} {value}"

/-- Print every operation on each corpus input for comparison with Julia. -/
def differential (release : Bool := false) (start : Nat := 0) (count : Nat := 2194) : IO Unit := do
  let ws := words
  emit 0 "floatmin" (out F64.floatmin)
  emit 0 "floatmax" (out F64.floatmax)
  for j in [start:min ws.size (start+count)] do
    let i := j+1
    let b := ws[j]!
    let x := F64.ofBits b
    let y := F64.ofBits ws[(17*j+7)%ws.size]!
    let z := F64.ofBits ws[(31*j+11)%ws.size]!
    emit i "neg" (out (F64.neg x))
    emit i "abs" (out (F64.abs x))
    emit i "sqrt" (outJl out (F64.sqrt x))
    emit i "signbit" (outBool (F64.signbit x))
    emit i "isnan" (outBool (F64.isnan x))
    emit i "isinf" (outBool (F64.isinf x))
    emit i "isfinite" (outBool (F64.isfinite x))
    emit i "next" (out (F64.nextfloat x))
    emit i "prev" (out (F64.prevfloat x))
    emit i "eps" (out (F64.eps x))
    emit i "exponent" (outJl toString (F64.exponent x))
    emit i "significand" (out (F64.significand x))
    let (f,e) := F64.frexp x
    emit i "frexp" s!"{out f},{e}"
    emit i "int" (outJl (fun n => toString n.val) (F64.int .i64 x))
    emit i "ldexp" (out (F64.ldexp x scales[j%scales.size]!))
    emit i "nextn" (out (F64.nextfloat x steps[j%steps.size]!))
    emit i "prevn" (out (F64.prevfloat x steps[j%steps.size]!))
    for (op,v) in #[("add",F64.add x y),("sub",F64.sub x y),
      ("mul",F64.mul x y),("divide",F64.div x y),("fma",F64.fma x y z),
      ("muladd",F64.muladd x y z)] do
      emit i op (out v)
    for (op,v) in #[("eq",F64.eq x y),("lt",F64.lt x y),("le",F64.le x y),
      ("isequal",F64.isequal x y),("isless",F64.isless x y)] do
      emit i op (outBool v)
    for (op,v) in #[("rem",F64.rem x y),("mod",F64.mod x y)] do
      emit i op (out v)
    for (op,mode) in #[("div",Rounding.RoundToZero),("fld",Rounding.RoundDown),
      ("cld",Rounding.RoundUp)] do
      emit i op (if release then outJl out (F64.divIntegerRelease x y mode)
        else out (F64.divInteger x y mode))
    for m in [:modes.size] do
      let r := modes[m]!
      emit i s!"round{m+1}" (out (F64.round x r))
      emit i s!"remmode{m+1}" (if release then outJl out (F64.remModeRelease x y r)
        else out (F64.remMode x y r))
      emit i s!"divmode{m+1}" (if release then outJl out (F64.divIntegerRelease x y r)
        else out (F64.divInteger x y r))
      for t in [:types.size] do
        emit i s!"roundint{m+1}-{t+1}"
          (outJl (fun n => toString n.val) (F64.roundInt types[t]! x r))
    let n := b*2^64 + ws[i%ws.size]!
    for t in [:types.size] do
      emit i s!"ofint{t+1}" (out (F64.ofJInt (JInt.wrap types[t]! (Int.ofNat n))))
  IO.println s!"COUNT {ws.size}"

end JuliaLean.Float.Validation
