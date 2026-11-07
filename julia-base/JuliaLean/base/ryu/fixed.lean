import JuliaLean.Runtime.Float
import JuliaLean.base.operators
import JuliaLean.base.ryu.utils
/-!
# Model of `base/ryu/fixed.jl`

Each input is converted to Float64 as in Julia; exact decimal rounding reuses
the `Printf` model.
-/

namespace JuliaLean.Printf

open JuliaLean JuliaLean.Float
/-- The trailing-zero loop of `base/ryu/fixed.jl:176-183` / `exp.jl:150-157`. -/
def trimZeros (hash : Bool) (bs : Bytes) : Bytes :=
  let r := bs.reverse.dropWhile (· == 48)
  (if r.head? == some 46 && !hash then r.tail else r).reverse

/-- `Ryu.writefixed(buf, pos, x, precision, plus, space, hash, '.', trim)`. -/
def writefixed (x : F64) (prec : Int) (plus space hash trim : Bool) : Result Bytes :=
  if prec < 0 then .error (.julia (.argumentError "precision must be non-negative")) else
  let sign := ParsePrint.Ryu.appendSign x plus space
  if F64.iszero x then
    .ok (sign ++ [48] ++ (if prec > 0 && !trim then 46 :: zeros prec.toNat else if hash then [46] else []))
  else if F64.isnan x then .ok (sign ++ [78, 97, 78])
  else if !F64.isfinite x then .ok (sign ++ [73, 110, 102])
  else
    let (num, den) := F64.toRat x
    let p := prec.toNat
    let m := rheScaled num.natAbs den prec
    let frac := prec > 0 || hash
    let body := sign ++ digits 10 false (m / 10 ^ p) ++
      (if frac then 46 :: (if p = 0 then [] else padDigits p (m % 10 ^ p)) else [])
    .ok (if trim && frac then trimZeros hash body else body)
end JuliaLean.Printf

namespace JuliaLean.base.ryu.Ryu

open JuliaLean JuliaLean.Promotion

def writefixed64 (x : JuliaLean.Float.F64) (precision : Int)
    (plus space hash : Bool) (decchar : Nat) (trimtrailingzeros : Bool) :
    JuliaLean.Printf.Result (List Nat) :=
  if precision < 0 then .error (.julia (.argumentError "precision must be non-negative")) else
  let sign := JuliaLean.ParsePrint.Ryu.appendSign x plus space
  if JuliaLean.Float.F64.iszero x then
    .ok (sign ++ [48] ++
      (if precision > 0 && !trimtrailingzeros then
        decchar :: JuliaLean.ParsePrint.Ryu.zeros precision.toNat
       else if hash then [decchar] else []))
  else if JuliaLean.Float.F64.isnan x then .ok (sign ++ [78, 97, 78])
  else if !JuliaLean.Float.F64.isfinite x then .ok (sign ++ [73, 110, 102])
  else
    (JuliaLean.Printf.writefixed x precision plus space hash trimtrailingzeros).map
      (fun bytes => bytes.map (fun byte => if byte == 46 then decchar else byte))

def writefixed16 (x : Fl half) (precision : Int)
    (plus space hash : Bool) (decchar : Nat) (trimtrailingzeros : Bool) :
    JuliaLean.Printf.Result (List Nat) :=
  writefixed64 (Fl.toF64 (Fl.convert x)) precision plus space hash decchar trimtrailingzeros

def writefixed32 (x : Fl single) (precision : Int)
    (plus space hash : Bool) (decchar : Nat) (trimtrailingzeros : Bool) :
    JuliaLean.Printf.Result (List Nat) :=
  writefixed64 (Fl.toF64 (Fl.convert x)) precision plus space hash decchar trimtrailingzeros

structure FixedBufferOps (Buffer : Type) where
  length : Buffer → Nat
  /-- Writes at a one-based Julia vector index. -/
  writeByte : Buffer → Nat → JInt .u8 → Buffer

inductive FixedWriteError where
  | formatter (error : JuliaLean.Printf.Error)
  | assertionError (message : String)

def liftFixedResult {A : Type} (result : JuliaLean.Printf.Result A) : Except FixedWriteError A :=
  match result with
  | .ok value => .ok value
  | .error error => .error (.formatter error)

def writeFixedBytes {Buffer : Type} (ops : FixedBufferOps Buffer)
    (buffer : Buffer) (position : Nat) : List Nat → Buffer
  | [] => buffer
  | byte :: bytes =>
    writeFixedBytes ops (ops.writeByte buffer position (JInt.wrap .u8 (Int.ofNat byte)))
      (position + 1) bytes

/-!
Julia source: base/ryu/fixed.jl:1-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writefixed(buf, pos, v::T,
    precision, plus=false, space=false, hash=false,
    decchar=UInt8('.'), trimtrailingzeros=false) where {T <: Base.IEEEFloat}
    pos = Int(pos)
    precision = Int(precision)
    precision >= 0 || throw(ArgumentError("precision must be non-negative"))
    @assert 0 < pos <= length(buf) "invalid pos"
    startpos = pos
    x = Float64(v)
    pos = append_sign(x, plus, space, buf, pos)

    # special cases
    if x == 0
        buf[pos] = UInt8('0')
        pos += 1
        if precision > 0 && !trimtrailingzeros
            buf[pos] = decchar
            pos += 1
            for _ = 1:precision
                buf[pos] = UInt8('0')
                pos += 1
            end
        elseif hash
            buf[pos] = decchar
            pos += 1
        end
        return pos
    elseif isnan(x)
        buf[pos] = UInt8('N')
        buf[pos + 1] = UInt8('a')
        buf[pos + 2] = UInt8('N')
        return pos + 3
    elseif !isfinite(x)
        buf[pos] = UInt8('I')
        buf[pos + 1] = UInt8('n')
        buf[pos + 2] = UInt8('f')
        return pos + 3
    end

    bits = reinterpret(UInt64, x)
    mant = bits & MANTISSA_MASK
    exp = Int((bits >> 52) & EXP_MASK)

    if exp == 0 # subnormal
        e2 = 1 - 1023 - 52
        m2 = mant
    else
        e2 = exp - 1023 - 52
        m2 = (Int64(1) << 52) | mant
    end
    nonzero = false
    if e2 >= -52
        idx = e2 < 0 ? 0 : indexforexp(e2)
        p10bits = pow10bitsforindex(idx)
        len = lengthforindex(idx)
        i = len - 1
        while i >= 0
            j = p10bits - e2
            mula, mulb, mulc = POW10_SPLIT[POW10_OFFSET[idx + 1] + i + 1]
            digits = mulshiftmod1e9(m2 << 8, mula, mulb, mulc, j + 8)
            if nonzero
                pos = append_nine_digits(digits, buf, pos)
            elseif digits != 0
                olength = decimallength(digits)
                pos = append_c_digits(olength, digits, buf, pos)
                nonzero = true
            end
            i -= 1
        end
    end
    if !nonzero
        buf[pos] = UInt8('0')
        pos += 1
    end
    hasfractional = false
    if precision > 0 || hash
        buf[pos] = decchar
        pos += 1
        hasfractional = true
    end
    if e2 < 0
        idx = div(-e2, 16)
        blocks = div(precision, 9) + 1
        roundUp = 0
        i = 0
        if blocks <= MIN_BLOCK_2[idx + 1]
            i = blocks
            for _ = 1:precision
                buf[pos] = UInt8('0')
                pos += 1
            end
        elseif i < MIN_BLOCK_2[idx + 1]
            i = MIN_BLOCK_2[idx + 1]
            for _ = 1:(9 * i)
                buf[pos] = UInt8('0')
                pos += 1
            end
        end
        while i < blocks
            j = 120 + (-e2 - 16 * idx)
            p = POW10_OFFSET_2[idx + 1] + UInt32(i) - MIN_BLOCK_2[idx + 1]
            if p >= POW10_OFFSET_2[idx + 2]
                for _ = 1:(precision - 9 * i)
                    buf[pos] = UInt8('0')
                    pos += 1
                end
                break
            end
            mula, mulb, mulc = POW10_SPLIT_2[p + 1]
            digits = mulshiftmod1e9(m2 << 8, mula, mulb, mulc, j + 8)
            if i < blocks - 1
                pos = append_nine_digits(digits, buf, pos)
            else
                maximum = precision - 9 * i
                lastDigit = 0
                k = 0
                while k < 9 - maximum
                    # global digits, lastDigit, k
                    lastDigit = digits % 10
                    digits = div(digits, 10)
                    k += 1
                end
                if lastDigit != 5
                    roundUp = lastDigit > 5 ? 1 : 0
                else
                    requiredTwos = -e2 - precision - 1
                    trailingZeros = requiredTwos <= 0 || (requiredTwos < 60 && pow2(m2, requiredTwos))
                    roundUp = trailingZeros ? 2 : 1 # 2 means round only if odd
                end
                if maximum > 0
                    pos = append_c_digits(maximum, digits, buf, pos)
                end
                break
            end
            i += 1
        end
        if roundUp != 0
            roundPos = pos
            dotPos = 1
            while true
                roundPos -= 1
                if roundPos == (startpos - 1) || (buf[roundPos] == UInt8('-')) || (plus && buf[roundPos] == UInt8('+')) || (space && buf[roundPos] == UInt8(' '))
                    buf[pos] = UInt8('0')
                    buf[roundPos + 1] = UInt8('1')
                    if dotPos > 1
                        buf[dotPos] = UInt8('0')
                        buf[dotPos + 1] = decchar
                        hasfractional = true
                    end
                    pos += 1
                    break
                end
                c = roundPos > 0 ? buf[roundPos] : 0x00
                if c == decchar
                    dotPos = roundPos
                    continue
                elseif c == UInt8('9')
                    buf[roundPos] = UInt8('0')
                    roundUp = 1
                    continue
                else
                    if roundUp == 2 && UInt8(c) % 2 == 0
                        break
                    end
                    buf[roundPos] = c + 1
                    break
                end
            end
        end
    else
        for _ = 1:precision
            buf[pos] = UInt8('0')
            pos += 1
        end
    end
    if trimtrailingzeros && hasfractional
        while buf[pos - 1] == UInt8('0')
            pos -= 1
        end
        if buf[pos - 1] == decchar && !hash
            pos -= 1
        end
    end
    return pos
end
```
-/
def writefixedBuffer {T : FTy} {Buffer : Type} (ops : FixedBufferOps Buffer)
    (toF64 : JuliaLean.Promotion.FV T → JuliaLean.Float.F64)
    (buffer : Buffer) (pos : Int) (value : JuliaLean.Promotion.FV T) (precision : Int)
    (plus : Bool := false) (space : Bool := false) (hash : Bool := false)
    (decchar : Nat := 46) (trimtrailingzeros : Bool := false) :
    Except FixedWriteError (Buffer × Int) := do
  if precision < 0 then
    throw (.formatter (.julia (.argumentError "precision must be non-negative")))
  if !decide (0 < pos ∧ pos ≤ Int.ofNat (ops.length buffer)) then
    throw (.assertionError "invalid pos")
  let bytes ← liftFixedResult
    (writefixed64 (toF64 value) precision plus space hash decchar trimtrailingzeros)
  let updated := writeFixedBytes ops buffer pos.toNat bytes
  pure (updated, pos + Int.ofNat bytes.length)
end JuliaLean.base.ryu.Ryu
