import JuliaLean.Runtime.Float
import JuliaLean.base.operators
import JuliaLean.base.ryu.fixed
import JuliaLean.base.ryu.utils
/-!
# Model of `base/ryu/exp.jl`

Each input is converted to Float64 as in Julia; exact decimal rounding reuses
the `Printf` model.
-/

namespace JuliaLean.Printf

open JuliaLean JuliaLean.Float
/-- The exponent part after the exponent character, `base/ryu/exp.jl:160-180`. -/
def expPart (e : Int) : Bytes := (if e < 0 then [45] else [43]) ++ padDigits 2 e.natAbs

/-- `Ryu.writeexp(buf, pos, x, precision, plus, space, hash, expchar, '.', trim)`. -/
def writeexp (x : F64) (prec : Int) (plus space hash : Bool) (expchar : Nat) (trim : Bool) :
    Result Bytes :=
  if prec < 0 then .error (.julia (.argumentError "precision must be non-negative")) else
  let sign := ParsePrint.Ryu.appendSign x plus space
  if F64.iszero x then
    .ok (sign ++ [48] ++ (if prec > 0 && !trim then 46 :: zeros prec.toNat else if hash then [46] else []) ++
      [expchar, 43, 48, 48])
  else if F64.isnan x then .ok (sign ++ [78, 97, 78])
  else if !F64.isfinite x then .ok (sign ++ [73, 110, 102])
  else
    let (num, den) := F64.toRat x
    let (m, e) := sci num.natAbs den prec.toNat
    let ds := digits 10 false m
    let mant := ds.take 1 ++ (if prec > 0 then 46 :: ds.drop 1 else if hash then [46] else [])
    .ok (sign ++ (if trim then trimZeros hash mant else mant) ++ [expchar] ++ expPart e)
end JuliaLean.Printf

namespace JuliaLean.base.ryu.Ryu

open JuliaLean JuliaLean.Promotion

def writeexp64 (x : JuliaLean.Float.F64) (precision : Int)
    (plus space hash : Bool) (expchar decchar : Nat) (trimtrailingzeros : Bool) :
    JuliaLean.Printf.Result (List Nat) :=
  if precision < 0 then .error (.julia (.argumentError "precision must be non-negative")) else
  let sign := JuliaLean.ParsePrint.Ryu.appendSign x plus space
  if JuliaLean.Float.F64.iszero x then
    .ok (sign ++ [48] ++
      (if precision > 0 && !trimtrailingzeros then
        decchar :: JuliaLean.ParsePrint.Ryu.zeros precision.toNat
       else if hash then [decchar] else []) ++ [expchar, 43, 48, 48])
  else if JuliaLean.Float.F64.isnan x then .ok (sign ++ [78, 97, 78])
  else if !JuliaLean.Float.F64.isfinite x then .ok (sign ++ [73, 110, 102])
  else
    (JuliaLean.Printf.writeexp x precision plus space hash expchar trimtrailingzeros).map
      (fun bytes => bytes.map (fun byte => if byte == 46 then decchar else byte))

def writeexp16 (x : Fl half) (precision : Int)
    (plus space hash : Bool) (expchar decchar : Nat) (trimtrailingzeros : Bool) :
    JuliaLean.Printf.Result (List Nat) :=
  writeexp64 (Fl.toF64 (Fl.convert x)) precision plus space hash expchar decchar trimtrailingzeros

def writeexp32 (x : Fl single) (precision : Int)
    (plus space hash : Bool) (expchar decchar : Nat) (trimtrailingzeros : Bool) :
    JuliaLean.Printf.Result (List Nat) :=
  writeexp64 (Fl.toF64 (Fl.convert x)) precision plus space hash expchar decchar trimtrailingzeros

structure ExpBufferOps (Buffer : Type) where
  length : Buffer → Nat
  /-- Writes at a one-based Julia vector index. -/
  writeByte : Buffer → Nat → JInt .u8 → Buffer

inductive ExpWriteError where
  | formatter (error : JuliaLean.Printf.Error)
  | assertionError (message : String)

def liftExpResult {A : Type} (result : JuliaLean.Printf.Result A) : Except ExpWriteError A :=
  match result with
  | .ok value => .ok value
  | .error error => .error (.formatter error)

def writeExpBytes {Buffer : Type} (ops : ExpBufferOps Buffer)
    (buffer : Buffer) (position : Nat) : List Nat → Buffer
  | [] => buffer
  | byte :: bytes =>
    writeExpBytes ops (ops.writeByte buffer position (JInt.wrap .u8 (Int.ofNat byte)))
      (position + 1) bytes

/-!
Julia source: base/ryu/exp.jl:1-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writeexp(buf, pos, v::T,
    precision, plus=false, space=false, hash=false,
    expchar=UInt8('e'), decchar=UInt8('.'), trimtrailingzeros=false) where {T <: Base.IEEEFloat}
    pos = Int(pos)
    precision = Int(precision)
    precision >= 0 || throw(ArgumentError("precision must be non-negative"))
    @assert 0 < pos <= length(buf) "invalid pos"
    startpos = pos
    x = Float64(v)
    pos = append_sign(x, plus, space, buf, pos)

    # special cases
    if iszero(x)
        @inbounds buf[pos] = UInt8('0')
        pos += 1
        if precision > 0 && !trimtrailingzeros
            @inbounds buf[pos] = decchar
            pos += 1
            for _ = 1:precision
                @inbounds buf[pos] = UInt8('0')
                pos += 1
            end
        elseif hash
            @inbounds buf[pos] = decchar
            pos += 1
        end
        @inbounds buf[pos] = expchar
        @inbounds buf[pos + 1] = UInt8('+')
        @inbounds buf[pos + 2] = UInt8('0')
        @inbounds buf[pos + 3] = UInt8('0')
        return pos + 4
    elseif isnan(x)
        @inbounds buf[pos] = UInt8('N')
        @inbounds buf[pos + 1] = UInt8('a')
        @inbounds buf[pos + 2] = UInt8('N')
        return pos + 3
    elseif !isfinite(x)
        @inbounds buf[pos] = UInt8('I')
        @inbounds buf[pos + 1] = UInt8('n')
        @inbounds buf[pos + 2] = UInt8('f')
        return pos + 3
    end

    bits = reinterpret(UInt64, x)
    mant = bits & MANTISSA_MASK
    exp = Int((bits >> 52) & EXP_MASK)

    if iszero(exp)
        e2 = 1 - 1023 - 52
        m2 = mant
    else
        e2 = exp - 1023 - 52
        m2 = (Int64(1) << 52) | mant
    end
    precision += 1
    digits = zero(UInt32)
    printedDigits = 0
    availableDigits = 0
    e = 0
    if e2 >= -52
        idx = e2 < 0 ? 0 : indexforexp(e2)
        p10bits = pow10bitsforindex(idx)
        len = lengthforindex(idx)
        i = len - 1
        while i >= 0
            j = p10bits - e2
            #=@inbounds=# mula, mulb, mulc = POW10_SPLIT[POW10_OFFSET[idx + 1] + i + 1]
            digits = mulshiftmod1e9(m2 << 8, mula, mulb, mulc, j + 8)
            if !iszero(printedDigits)
                if printedDigits + 9 > precision
                    availableDigits = 9
                    break
                end
                pos = append_nine_digits(digits, buf, pos)
                printedDigits += 9
            elseif !iszero(digits)
                availableDigits = decimallength(digits)
                e = i * 9 + availableDigits - 1
                if availableDigits > precision
                    break
                end
                if precision > 1
                    pos = append_d_digits(availableDigits, digits, buf, pos, decchar)
                else
                    @inbounds buf[pos] = UInt8('0') + digits
                    pos += 1
                    if hash
                        @inbounds buf[pos] = decchar
                        pos += 1
                    end
                end
                printedDigits = availableDigits
                availableDigits = 0
            end
            i -= 1
        end
    end
    if e2 < 0 && iszero(availableDigits)
        idx = div(-e2, 16)
        i = Int(MIN_BLOCK_2[idx + 1])
        while i < 200
            j = 120 + (-e2 - 16 * idx)
            p = POW10_OFFSET_2[idx + 1] + i - MIN_BLOCK_2[idx + 1]
            if p >= POW10_OFFSET_2[idx + 2]
                digits = zero(UInt32)
            else
                #=@inbounds=# mula, mulb, mulc = POW10_SPLIT_2[p + 1]
                digits = mulshiftmod1e9(m2 << 8, mula, mulb, mulc, j + 8)
            end
            if !iszero(printedDigits)
                if printedDigits + 9 > precision
                    availableDigits = 9
                    break
                end
                pos = append_nine_digits(digits, buf, pos)
                printedDigits += 9
            elseif !iszero(digits)
                availableDigits = decimallength(digits)
                e = -(i + 1) * 9 + availableDigits - 1
                if availableDigits > precision
                    break
                end
                if precision > 1
                    pos = append_d_digits(availableDigits, digits, buf, pos, decchar)
                else
                    @inbounds buf[pos] = UInt8('0') + digits
                    pos += 1
                    if hash
                        @inbounds buf[pos] = decchar
                        pos += 1
                    end
                end
                printedDigits = availableDigits
                availableDigits = 0
            end
            i += 1
        end
    end
    maximum = precision - printedDigits
    if iszero(availableDigits)
        digits = zero(UInt32)
    end
    lastDigit = zero(UInt32)
    if availableDigits > maximum
        for _ = 0:(availableDigits - maximum - 1)
            lastDigit = digits % UInt32(10)
            digits = div(digits, UInt32(10))
        end
    end
    if lastDigit != 5
        roundUp = lastDigit > 5 ? 1 : 0
    else
        rexp = precision - e
        requiredTwos = -e2 - rexp
        trailingZeros = requiredTwos <= 0 ||
            (requiredTwos < 60 && pow2(m2, requiredTwos))
        if rexp < 0
            requiredFives = -rexp
            trailingZeros = trailingZeros & pow5(m2, requiredFives)
        end
        roundUp = trailingZeros ? 2 : 1
    end
    if !iszero(printedDigits)
        if iszero(digits)
            for _ = 1:maximum
                @inbounds buf[pos] = UInt8('0')
                pos += 1
            end
        else
            pos = append_c_digits(maximum, digits, buf, pos)
        end
    else
        if precision > 1
            pos = append_d_digits(maximum, digits, buf, pos, decchar)
        else
            @inbounds buf[pos] = UInt8('0') + digits
            pos += 1
            if hash
                @inbounds buf[pos] = decchar
                pos += 1
            end
        end
    end
    if !iszero(roundUp)
        roundPos = pos
        while true
            roundPos -= 1
            if roundPos == (startpos - 1) || (@inbounds buf[roundPos]) == UInt8('-') || (plus && (@inbounds buf[roundPos]) == UInt8('+')) || (space && (@inbounds buf[roundPos]) == UInt8(' '))
                @inbounds buf[roundPos + 1] = UInt8('1')
                e += 1
                break
            end
            c = roundPos > 0 ? (@inbounds buf[roundPos]) : 0x00
            if c == decchar
                continue
            elseif c == UInt8('9')
                @inbounds buf[roundPos] = UInt8('0')
                roundUp = 1
                continue
            else
                if roundUp == 2 && iseven(c)
                    break
                end
                @inbounds buf[roundPos] = c + 1
                break
            end
        end
    end
    if trimtrailingzeros
        while @inbounds buf[pos - 1] == UInt8('0')
            pos -= 1
        end
        if @inbounds buf[pos - 1] == decchar && !hash
            pos -= 1
        end
    end
    buf[pos] = expchar
    pos += 1
    if e < 0
        @inbounds buf[pos] = UInt8('-')
        pos += 1
        e = -e
    else
        @inbounds buf[pos] = UInt8('+')
        pos += 1
    end
    if e >= 100
        c = (e % 10) % UInt8
        @inbounds d100 = DIGIT_TABLE16[div(e, 10) + 1]
        @inbounds buf[pos] = d100 % UInt8
        @inbounds buf[pos + 1] = (d100 >> 0x8) % UInt8
        @inbounds buf[pos + 2] = UInt8('0') + c
        pos += 3
    else
        @inbounds d100 = DIGIT_TABLE16[e + 1]
        @inbounds buf[pos] = d100 % UInt8
        @inbounds buf[pos + 1] = (d100 >> 0x8) % UInt8
        pos += 2
    end
    return pos
end
```
-/
def writeexpBuffer {T : FTy} {Buffer : Type} (ops : ExpBufferOps Buffer)
    (toF64 : JuliaLean.Promotion.FV T → JuliaLean.Float.F64)
    (buffer : Buffer) (pos : Int) (value : JuliaLean.Promotion.FV T) (precision : Int)
    (plus : Bool := false) (space : Bool := false) (hash : Bool := false)
    (expchar : Nat := 101) (decchar : Nat := 46) (trimtrailingzeros : Bool := false) :
    Except ExpWriteError (Buffer × Int) := do
  if precision < 0 then
    throw (.formatter (.julia (.argumentError "precision must be non-negative")))
  if !decide (0 < pos ∧ pos ≤ Int.ofNat (ops.length buffer)) then
    throw (.assertionError "invalid pos")
  let bytes ← liftExpResult
    (writeexp64 (toF64 value) precision plus space hash expchar decchar trimtrailingzeros)
  let updated := writeExpBytes ops buffer pos.toNat bytes
  pure (updated, pos + Int.ofNat bytes.length)
end JuliaLean.base.ryu.Ryu
