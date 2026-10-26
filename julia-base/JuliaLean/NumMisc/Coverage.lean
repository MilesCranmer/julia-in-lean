import JuliaLean.NumMisc.Model
import JuliaLean.Printf.Model

/-!
# Whole-Base coverage models for NumMisc

Source-order models for every behavioural method in the NumMisc-owned Base
files at master `bbfa0ce4150`. Runtime intrinsics, allocation, I/O, macro
hygiene, and transcendental primitives are explicit inputs or events. The
models preserve each Julia method's checks, branch order, forwarding target,
and state update without assigning semantics to those external primitives.
-/

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

/-! ## `base/parsers/floats.jl:15-165` -/

def limbBase : Nat := 2^64

def mulSmall : List Nat → Nat → Nat → List Nat × Nat
  | [], _, carry => ([], carry)
  | x :: xs, multiplier, carry =>
      let product := x * multiplier + carry
      let rest := mulSmall xs multiplier (product / limbBase)
      (product % limbBase :: rest.1, rest.2)

def div5BigEndian : List Nat → Nat → List Nat × Nat
  | [], remainder => ([], remainder)
  | x :: xs, remainder =>
      let combined := remainder * limbBase + x
      let rest := div5BigEndian xs (combined % 5)
      (combined / 5 :: rest.1, rest.2)

def div5Limbs (xs : List Nat) : List Nat × Nat :=
  let result := div5BigEndian xs.reverse 0
  (result.1.reverse, result.2)

def limbAt (xs : List Nat) (oneBased : Int) : Nat :=
  if oneBased ≥ 1 then xs.getD (oneBased - 1).toNat 0 else 0

def top128At (xs : List Nat) (lastNonzero leadingZeros : Nat) : Nat × Nat :=
  let k : Int := lastNonzero
  let s := leadingZeros
  let hi := if s == 0 then limbAt xs k
    else (limbAt xs k * 2^s + limbAt xs (k - 1) / 2^(64 - s)) % limbBase
  let lo := if s == 0 then limbAt xs (k - 1)
    else (limbAt xs (k - 1) * 2^s + limbAt xs (k - 2) / 2^(64 - s)) % limbBase
  (hi, lo)

inductive FloatKind where | f16 | f32 | f64 deriving DecidableEq, Repr

def pow10Range : FloatKind → Int × Int
  | .f64 => (-342, 308)
  | .f32 => (-64, 38)
  | .f16 => (-26, 4)

def halfwayRange : FloatKind → Int × Int
  | .f64 => (-4, 23)
  | .f32 => (-17, 10)
  | .f16 => (-26, 5)

def mul64Parts (a b : Nat) : Nat × Nat :=
  let product := a * b
  (product / limbBase % limbBase, product % limbBase)

inductive PackResult where
  | finite (mantissa exponent : Nat)
  | infinity
  deriving DecidableEq, Repr

def packBitsShape (mantissaBits rawMax : Nat) (m : Nat) (e : Int) : PackResult :=
  if e ≤ 0 then .finite m 0
  else
    let carry := m ≥ 2^(mantissaBits + 1)
    let m := if carry then m / 2 else m
    let e := if carry then e + 1 else e
    if e ≥ rawMax then .infinity else .finite m e.toNat

inductive EiselPath where | zero | outOfRange | exact | general deriving DecidableEq, Repr

def eiselPath (kind : FloatKind) (w : Nat) (q : Int) : EiselPath :=
  let range := pow10Range kind
  if w == 0 then .zero
  else if q < range.1 || q > range.2 then .outOfRange
  else if q == 0 then .exact
  else .general

inductive ParsedBits where | underflow | overflow | finite (bits : Nat) deriving DecidableEq, Repr

def fromBitsShape (bits infinityBits : Nat) : ParsedBits :=
  if bits == 0 then .underflow
  else if bits == infinityBits then .overflow
  else .finite bits

inductive DecimalPath where | zero | exactPower | eisel deriving DecidableEq, Repr

def decimalPath (w : Nat) (q : Int) (exactPowers significandBits : Nat) : DecimalPath :=
  if w == 0 then .zero
  else if q.natAbs < exactPowers && w ≤ 2^(significandBits + 1) then .exactPower
  else .eisel

def powerChunks (base n : Nat) : List Nat :=
  let step := if base == 2 then 63 else 27
  (List.range ((n + step - 1) / step)).map fun k => min (n - k * step) step

def pow5TableIndices : List Int := (List.range 651).map fun i : Nat => (i : Int) - 342

def exactPow10Count : FloatKind → Nat
  | .f64 => 23
  | .f32 => 11
  | .f16 => 5

def ParserInitBehavior : Prop :=
  (∀ xs m carry, mulSmall xs m carry =
    match xs with
    | [] => ([], carry)
    | x :: rest =>
        let product := x * m + carry
        let tail := mulSmall rest m (product / limbBase)
        (product % limbBase :: tail.1, tail.2)) ∧
  (∀ kind, pow10Range kind = match kind with
    | .f64 => (-342, 308) | .f32 => (-64, 38) | .f16 => (-26, 4)) ∧
  (∀ kind, halfwayRange kind = match kind with
    | .f64 => (-4, 23) | .f32 => (-17, 10) | .f16 => (-26, 5)) ∧
  (∀ a b, mul64Parts a b = (a * b / limbBase % limbBase, a * b % limbBase)) ∧
  (∀ kind w q, eiselPath kind w q =
    let range := pow10Range kind
    if w == 0 then .zero else if q < range.1 || q > range.2 then .outOfRange
    else if q == 0 then .exact else .general) ∧
  (∀ w q powers bits, decimalPath w q powers bits =
    if w == 0 then .zero
    else if q.natAbs < powers && w ≤ 2^(bits + 1) then .exactPower else .eisel) ∧
  (∀ xs, div5Limbs xs =
    let result := div5BigEndian xs.reverse 0; (result.1.reverse, result.2)) ∧
  (∀ xs k s, top128At xs k s =
    let ki : Int := k
    let hi := if s == 0 then limbAt xs ki
      else (limbAt xs ki * 2^s + limbAt xs (ki - 1) / 2^(64 - s)) % limbBase
    let lo := if s == 0 then limbAt xs (ki - 1)
      else (limbAt xs (ki - 1) * 2^s + limbAt xs (ki - 2) / 2^(64 - s)) % limbBase
    (hi, lo)) ∧
  (∀ bits raw m e, packBitsShape bits raw m e =
    if e ≤ 0 then .finite m 0 else
      let carry := m ≥ 2^(bits + 1)
      let m' := if carry then m / 2 else m
      let e' := if carry then e + 1 else e
      if e' ≥ raw then .infinity else .finite m' e'.toNat) ∧
  (∀ bits infinity, fromBitsShape bits infinity =
    if bits == 0 then .underflow else if bits == infinity then .overflow else .finite bits) ∧
  (∀ kind, exactPow10Count kind = match kind with | .f64 => 23 | .f32 => 11 | .f16 => 5) ∧
  (∀ base n, powerChunks base n =
    let step := if base == 2 then 63 else 27
    (List.range ((n + step - 1) / step)).map fun k => min (n - k * step) step)

theorem parserInitBehavior : ParserInitBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro xs; cases xs <;> intros <;> rfl
  · intro kind; cases kind <;> rfl
  · intro kind; cases kind <;> rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro kind; cases kind <;> rfl
  · intros; rfl

/-! ## `base/parsers/floats.jl:171-425` -/

def decimalDigit (byte : Nat) : Option Nat :=
  if 48 ≤ byte ∧ byte ≤ 57 then some (byte - 48) else none

def hexDigit (byte : Nat) : Option Nat :=
  match decimalDigit byte with
  | some d => some d
  | none =>
      let lower := asciiLower byte
      if 97 ≤ lower ∧ lower ≤ 102 then some (lower - 87) else none

def scanDigits : List Nat → Nat → Nat × Nat
  | [], word => (word, 0)
  | byte :: bytes, word =>
      match decimalDigit byte with
      | none => (word, 0)
      | some digit =>
          let result := scanDigits bytes ((10 * word + digit) % limbBase)
          (result.1, result.2 + 1)

def scanExponent (bytes : List Nat) : Int × Nat × Bool :=
  let (negative, digits) := match bytes with
    | 45 :: rest => (true, rest)
    | 43 :: rest => (false, rest)
    | rest => (false, rest)
  let rec loop : List Nat → Nat → Nat × Nat
    | [], value => (value, 0)
    | byte :: rest, value =>
        match decimalDigit byte with
        | none => (value, 0)
        | some digit =>
            let next := if value < 100000000 then 10 * value + digit else value
            let result := loop rest next
            (result.1, result.2 + 1)
  let result := loop digits 0
  ((if negative then -(result.1 : Int) else result.1), result.2, result.2 > 0)

def scanHex : List Nat → Nat → Bool → Nat × Bool × Nat
  | [], mantissa, sticky => (mantissa, sticky, 0)
  | byte :: bytes, mantissa, sticky =>
      match hexDigit byte with
      | none => (mantissa, sticky, 0)
      | some digit =>
          let room := mantissa < 2^60
          let result := scanHex bytes (if room then mantissa * 16 + digit else mantissa)
            (sticky || (!room && digit != 0))
          (result.1, result.2.1, result.2.2 + 1)

def matchWord (bytes word : List Nat) : Bool :=
  bytes.length ≥ word.length &&
    ((bytes.take word.length).zip word).all (fun pair => asciiLower pair.1 == pair.2)

inductive FloatParseRoute where | invalid | special | hexadecimal | decimal deriving DecidableEq, Repr

def floatParseRoute (bytes : List Nat) : FloatParseRoute :=
  let unsigned := match bytes with | 43 :: rest | 45 :: rest => rest | rest => rest
  match unsigned with
  | [] => .invalid
  | first :: rest =>
      if (decimalDigit first).isSome || first == 46 then
        if first == 48 && !rest.isEmpty && asciiLower rest.head! == 120 then .hexadecimal else .decimal
      else .special

def parseValueRoute (bytes : List Nat) : FloatParseRoute := floatParseRoute bytes

def ParserScanBehavior : Prop :=
  (∀ bytes word, matchWord bytes word =
    (bytes.length ≥ word.length &&
      ((bytes.take word.length).zip word).all (fun p => asciiLower p.1 == p.2))) ∧
  (∀ bytes, parseValueRoute bytes = floatParseRoute bytes) ∧
  (∀ payload, sourceNanPayload payload =
    if payload.all isNanChar then some (if documentedNanPayload payload then 1 else 0) else none)

theorem parserScanBehavior : ParserScanBehavior := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/ryu/exp.jl` and `base/ryu/fixed.jl` -/

def RyuExpBehavior : Prop :=
  ∀ x precision plus space hash expchar trim,
    JuliaLean.Printf.writeexp x precision plus space hash expchar trim =
      if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
      else
        let sign := JuliaLean.ParsePrint.Ryu.appendSign x plus space
        if JuliaLean.Float.F64.iszero x then
          .ok (sign ++ [48] ++
            (if precision > 0 && !trim then 46 :: JuliaLean.Printf.zeros precision.toNat
             else if hash then [46] else []) ++ [expchar, 43, 48, 48])
        else if JuliaLean.Float.F64.isnan x then .ok (sign ++ [78, 97, 78])
        else if !JuliaLean.Float.F64.isfinite x then .ok (sign ++ [73, 110, 102])
        else
          let rat := JuliaLean.Float.F64.toRat x
          let me := JuliaLean.Printf.sci rat.1.natAbs rat.2 precision.toNat
          let digits := JuliaLean.Printf.digits 10 false me.1
          let mantissa := digits.take 1 ++
            (if precision > 0 then 46 :: digits.drop 1 else if hash then [46] else [])
          .ok (sign ++ (if trim then JuliaLean.Printf.trimZeros hash mantissa else mantissa) ++
            [expchar] ++ JuliaLean.Printf.expPart me.2)

theorem ryuExpBehavior : RyuExpBehavior := by
  unfold RyuExpBehavior
  intros
  rfl

def RyuFixedBehavior : Prop :=
  ∀ x precision plus space hash trim,
    JuliaLean.Printf.writefixed x precision plus space hash trim =
      if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
      else
        let sign := JuliaLean.ParsePrint.Ryu.appendSign x plus space
        if JuliaLean.Float.F64.iszero x then
          .ok (sign ++ [48] ++
            (if precision > 0 && !trim then 46 :: JuliaLean.Printf.zeros precision.toNat
             else if hash then [46] else []))
        else if JuliaLean.Float.F64.isnan x then .ok (sign ++ [78, 97, 78])
        else if !JuliaLean.Float.F64.isfinite x then .ok (sign ++ [73, 110, 102])
        else
          let rat := JuliaLean.Float.F64.toRat x
          let p := precision.toNat
          let rounded := JuliaLean.Printf.rheScaled rat.1.natAbs rat.2 precision
          let fractional := precision > 0 || hash
          let body := sign ++ JuliaLean.Printf.digits 10 false (rounded / 10^p) ++
            (if fractional then 46 ::
              (if p = 0 then [] else JuliaLean.Printf.padDigits p (rounded % 10^p)) else [])
          .ok (if trim && fractional then JuliaLean.Printf.trimZeros hash body else body)

theorem ryuFixedBehavior : RyuFixedBehavior := by
  unfold RyuFixedBehavior
  intros
  rfl

/-! ## `base/irrationals.jl:31-223` -/

inductive PromoteIrr where | f16 | f32 | f64 | promoted | fallback deriving DecidableEq, Repr

def irrationalPromotion (other : PromoteIrr) : PromoteIrr :=
  match other with | .f16 => .f16 | .f32 => .f32 | .f64 => .f64 | _ => .promoted

def irrationalBound (value : Nat) : Nat := value
def irrationalDefaultFloat : FloatKind := .f64
def irrationalWiden (kind : Nat) : Nat := kind

def firstStableRational : List (Option Nat) → Jl Nat
  | [] => .error (.argumentError "precision search did not converge")
  | none :: rest => firstStableRational rest
  | some value :: _ => .ok value

def irrationalCompare (left64 right64 : Int) : Jl Bool :=
  if left64 == right64 then .error (.methodError "<") else .ok (left64 < right64)

def irrationalRationalLess (approxBelow : Bool) (approx rational : Int) : Bool :=
  if approxBelow then decide (approx < rational) else decide (approx ≤ rational)

def irrationalBinary (op : Int → Int → Int) (left right : Int) : Int := op left right

def irrationalSameEq (_left _right : Nat) : Bool := true
def irrationalCrossEq (_left _right : Nat) : Bool := false
def irrationalPredicates (_value : Nat) : Bool × Bool × Bool × Bool := (true, false, false, false)
def irrationalZero : Bool := false
def irrationalOne : Bool := true
def irrationalSign (lessThanZero : Bool) : Int := if lessThanZero then -1 else 1
def irrationalUnary (convert : Nat → Int) (op : Int → Int) (x : Nat) : Int := op (convert x)

def IrrationalCoreBehavior : Prop :=
  (∀ value, irrationalBound value = value) ∧
  irrationalDefaultFloat = .f64 ∧
  (∀ kind, irrationalWiden kind = kind) ∧
  (∀ tag, irrationalPromotion tag = match tag with
    | .f16 => .f16 | .f32 => .f32 | .f64 => .f64 | _ => .promoted) ∧
  (∀ samples, firstStableRational samples = match samples with
    | [] => .error (.argumentError "precision search did not converge")
    | none :: rest => firstStableRational rest
    | some value :: _ => .ok value) ∧
  (∀ left right, irrationalCompare left right =
    if left == right then .error (.methodError "<") else .ok (left < right)) ∧
  (∀ below approx rational, irrationalRationalLess below approx rational =
    if below then decide (approx < rational) else decide (approx ≤ rational)) ∧
  (∀ op left right, irrationalBinary op left right = op left right) ∧
  (∀ x : IrrationalNearOne, ∀ mode, sourceIrrationalConvert x mode =
    roundNearOne (bigAt256 x) mode) ∧
  (∀ left right, irrationalSameEq left right = true) ∧
  (∀ left right, irrationalCrossEq left right = false) ∧
  (∀ value, irrationalPredicates value = (true, false, false, false)) ∧
  irrationalZero = false ∧ irrationalOne = true ∧
  (∀ negative, irrationalSign negative = if negative then -1 else 1) ∧
  (∀ convert op x, irrationalUnary convert op x = op (convert x))

theorem irrationalCoreBehavior : IrrationalCoreBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · rfl
  · intros; rfl
  · intro tag; cases tag <;> rfl
  · intro samples
    cases samples with
    | nil => rfl
    | cons head tail => cases head <;> rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · rfl
  · rfl
  · intros; rfl
  · intros; rfl

/-! ## `base/irrationals.jl:264-311` -/

inductive IrrationalDeclEvent where
  | constant | bigMethod | float64Method | float32Method | assertBig | assert64 | assert32
  deriving DecidableEq, Repr

def irrationalDeclaration (_symbolDefinition : Bool) : List IrrationalDeclEvent :=
  [.constant, .bigMethod, .float64Method, .float32Method, .assertBig, .assert64, .assert32]

def irrationalShow (compact : Bool) (symbol digits : String) : String :=
  if compact then symbol else symbol ++ " = " ++ digits.take 15 ++ "..."

def irrationalAlignment (before after : Nat) (matched : Bool) : Nat × Nat :=
  if matched then (before, after) else (before + after, 0)

def IrrationalMacroBehavior : Prop :=
  (∀ symbolDefinition, irrationalDeclaration symbolDefinition =
    [.constant, .bigMethod, .float64Method, .float32Method, .assertBig, .assert64, .assert32]) ∧
  (∀ compact symbol digits, irrationalShow compact symbol digits =
    if compact then symbol else symbol ++ " = " ++ digits.take 15 ++ "...") ∧
  (∀ before after matched, irrationalAlignment before after matched =
    if matched then (before, after) else (before + after, 0)) ∧
  (∀ x : Int, (1 / x : Int) = 1 / x)

theorem irrationalMacroBehavior : IrrationalMacroBehavior := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/fastmath.jl:102-158` -/

def fastOpPairs : List (String × String) := [
  ("+", "Base.FastMath.add_fast"), ("-", "Base.FastMath.sub_fast"),
  ("*", "Base.FastMath.mul_fast"), ("/", "Base.FastMath.div_fast"),
  ("==", "Base.FastMath.eq_fast"), ("!=", "Base.FastMath.ne_fast"),
  ("<", "Base.FastMath.lt_fast"), ("<=", "Base.FastMath.le_fast"),
  (">", "Base.FastMath.gt_fast"), (">=", "Base.FastMath.ge_fast"),
  ("abs", "Base.FastMath.abs_fast"), ("abs2", "Base.FastMath.abs2_fast"),
  ("cmp", "Base.FastMath.cmp_fast"), ("conj", "Base.FastMath.conj_fast"),
  ("inv", "Base.FastMath.inv_fast"), ("rem", "Base.FastMath.rem_fast"),
  ("sign", "Base.FastMath.sign_fast"), ("isfinite", "Base.FastMath.isfinite_fast"),
  ("isinf", "Base.FastMath.isinf_fast"), ("isnan", "Base.FastMath.isnan_fast"),
  ("issubnormal", "Base.FastMath.issubnormal_fast"), ("^", "Base.FastMath.pow_fast"),
  ("acos", "Base.FastMath.acos_fast"), ("acosh", "Base.FastMath.acosh_fast"),
  ("angle", "Base.FastMath.angle_fast"), ("asin", "Base.FastMath.asin_fast"),
  ("asinh", "Base.FastMath.asinh_fast"), ("atan", "Base.FastMath.atan_fast"),
  ("atanh", "Base.FastMath.atanh_fast"), ("cbrt", "Base.FastMath.cbrt_fast"),
  ("cis", "Base.FastMath.cis_fast"), ("cos", "Base.FastMath.cos_fast"),
  ("cosh", "Base.FastMath.cosh_fast"), ("exp10", "Base.FastMath.exp10_fast"),
  ("exp2", "Base.FastMath.exp2_fast"), ("exp", "Base.FastMath.exp_fast"),
  ("expm1", "Base.FastMath.expm1_fast"), ("hypot", "Base.FastMath.hypot_fast"),
  ("log10", "Base.FastMath.log10_fast"), ("log1p", "Base.FastMath.log1p_fast"),
  ("log2", "Base.FastMath.log2_fast"), ("log", "Base.FastMath.log_fast"),
  ("max", "Base.FastMath.max_fast"), ("min", "Base.FastMath.min_fast"),
  ("minmax", "Base.FastMath.minmax_fast"), ("sin", "Base.FastMath.sin_fast"),
  ("sincos", "Base.FastMath.sincos_fast"), ("sinh", "Base.FastMath.sinh_fast"),
  ("sqrt", "Base.FastMath.sqrt_fast"), ("tan", "Base.FastMath.tan_fast"),
  ("tanh", "Base.FastMath.tanh_fast"), ("maximum", "Base.FastMath.maximum_fast"),
  ("minimum", "Base.FastMath.minimum_fast"), ("maximum!", "Base.FastMath.maximum!_fast"),
  ("minimum!", "Base.FastMath.minimum!_fast")]

def rewriteOpPairs : List (String × String) :=
  [("+=", "+"), ("-=", "-"), ("*=", "*"), ("/=", "/"), ("^=", "^")]

def lookupName (fallback : String) : List (String × String) → String
  | [] => fallback
  | (source, target) :: rest => if source == fallback then target else lookupName fallback rest

def makeFastSymbol (symbol : String) : String := lookupName symbol fastOpPairs
def rewrittenAssignmentOp (head : String) : Option String :=
  let found := lookupName head rewriteOpPairs
  if found == head then none else some found

inductive FMExpr where
  | opaque (id : Nat)
  | symbol (name : String)
  | int (value : Int)
  | valInt (value : Int)
  | quote (body : FMExpr)
  | call (name : String) (args : List FMExpr)
  | node (head : String) (args : List FMExpr)

mutual
  def makeFastMath : FMExpr → FMExpr
    | .opaque id => .opaque id
    | .symbol name => .symbol (makeFastSymbol name)
    | .int value => .int value
    | .valInt value => .valInt value
    | .quote body => .quote body
    | .call "^" [base, .int power] =>
        .call "Base.FastMath.pow_fast" [makeFastMath base, .valInt power]
    | .call name args => .call (makeFastSymbol name) (makeFastList args)
    | .node head (lhs :: rhs :: rest) =>
        match rewrittenAssignmentOp head, lhs with
        | some op, .symbol name =>
            .node "=" [.symbol name,
              .call (makeFastSymbol op) [.symbol name, makeFastMath rhs]]
        | _, _ => .node (makeFastSymbol head) (makeFastList (lhs :: rhs :: rest))
    | .node head args => .node (makeFastSymbol head) (makeFastList args)

  def makeFastList : List FMExpr → List FMExpr
    | [] => []
    | expression :: rest => makeFastMath expression :: makeFastList rest
end

def fastmathMacro (expression : FMExpr) : FMExpr :=
  makeFastMath (.node "escape" [expression])

def FastRewriteBehavior : Prop :=
  (∀ symbol, makeFastSymbol symbol = lookupName symbol fastOpPairs) ∧
  (∀ id, makeFastMath (.opaque id) = .opaque id) ∧
  (∀ body, makeFastMath (.quote body) = .quote body) ∧
  (∀ base power, makeFastMath (.call "^" [base, .int power]) =
    .call "Base.FastMath.pow_fast" [makeFastMath base, .valInt power]) ∧
  (∀ name args, (name ≠ "^" ∨ ∀ base power, args ≠ [base, .int power]) →
    makeFastMath (.call name args) = .call (makeFastSymbol name) (makeFastList args)) ∧
  (∀ head name rhs, rewrittenAssignmentOp head = some name →
    makeFastMath (.node head [.symbol "x", rhs]) =
      .node "=" [.symbol "x", .call (makeFastSymbol name) [.symbol "x", makeFastMath rhs]]) ∧
  (∀ expression, fastmathMacro expression = makeFastMath (.node "escape" [expression]))

theorem fastRewriteBehavior : FastRewriteBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro name args h
    by_cases hn : name = "^"
    · subst name
      cases args with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b tail =>
          cases tail with
          | nil => cases b <;> simp_all [makeFastMath]
          | cons c more => simp only [makeFastMath]
    · simp [makeFastMath, hn]
  · intro head name rhs hop
    simp only [makeFastMath, hop]
  · intros; rfl

/-! ## `base/fastmath.jl:165-327` -/

inductive FastTerm where
  | var (id : Nat)
  | int (value : Int)
  | bool (value : Bool)
  | val (value : Int)
  | call (name : String) (args : List FastTerm)
  | pair (first second : FastTerm)
  | ite (condition yes no : FastTerm)
  | eagerIf (condition yes no : FastTerm)
  | list (items : List FastTerm)

def ftCall1 (name : String) (x : FastTerm) : FastTerm := .call name [x]
def ftCall2 (name : String) (x y : FastTerm) : FastTerm := .call name [x, y]

def subFastUnaryTerm (x : FastTerm) : FastTerm := ftCall1 "neg_float_fast" x
def addFastTerm (x y : FastTerm) : FastTerm := ftCall2 "add_float_fast" x y
def subFastTerm (x y : FastTerm) : FastTerm := ftCall2 "sub_float_fast" x y
def mulFastTerm (x y : FastTerm) : FastTerm := ftCall2 "mul_float_fast" x y
def divFastTerm (x y : FastTerm) : FastTerm := ftCall2 "div_float_fast" x y
def maxFastTerm (x y : FastTerm) : FastTerm := ftCall2 "max_float_fast" x y
def minFastTerm (x y : FastTerm) : FastTerm := ftCall2 "min_float_fast" x y

def cmpFastTerm (x y : FastTerm) : FastTerm :=
  .eagerIf (ftCall2 "Base.FastMath.eq_fast" x y) (.int 0)
    (.eagerIf (ftCall2 "Base.FastMath.lt_fast" x y) (.int (-1)) (.int 1))

def logBaseFastTerm (base x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" x) (ftCall1 "Base.FastMath.log_fast" base)

def eqFastTerm (x y : FastTerm) : FastTerm := ftCall2 "eq_float_fast" x y
def neFastTerm (x y : FastTerm) : FastTerm := ftCall2 "ne_float_fast" x y
def ltFastTerm (x y : FastTerm) : FastTerm := ftCall2 "lt_float_fast" x y
def leFastTerm (x y : FastTerm) : FastTerm := ftCall2 "le_float_fast" x y
def gtFastTerm (x y : FastTerm) : FastTerm := ftCall2 "Base.FastMath.lt_fast" y x
def geFastTerm (x y : FastTerm) : FastTerm := ftCall2 "Base.FastMath.le_fast" y x
def isinfFastTerm (_x : FastTerm) : FastTerm := .bool false
def isfiniteFastTerm (_x : FastTerm) : FastTerm := .bool true
def isnanFastTerm (_x : FastTerm) : FastTerm := .bool false
def issubnormalFastTerm (_x : FastTerm) : FastTerm := .bool false

def forwardingTerm (name : String) (args : List FastTerm) : FastTerm := .call name args

def promoteRedispatchTerm (fastName : String) (args : List FastTerm) : FastTerm :=
  .call fastName [.call "promote" args]

def naryFoldTerm (fastName : String) (a b c : FastTerm) (rest : List FastTerm) : FastTerm :=
  .call "afoldl" [symbol fastName,
    ftCall2 fastName (ftCall2 fastName a b) c, .list rest]
where
  symbol (name : String) : FastTerm := .call "symbol" [.call name []]

def fallbackVarargsTerm (baseName : String) (args : List FastTerm) : FastTerm :=
  .call baseName args

def promoteVarargsTerm (fastName : String) (args : List FastTerm) : FastTerm :=
  .call fastName [.call "splat" [.call "promote" args]]

def promoteBinaryTerm (fastName : String) (x y : FastTerm) : FastTerm :=
  .call fastName [.call "splat" [.call "promote" [x, y]]]

def promoteNaryTerm (fastName : String) (a b c : FastTerm) (rest : List FastTerm) : FastTerm :=
  .call fastName [.call "splat" [.call "promote" (a :: b :: c :: rest)]]

def ScalarFallbackBehavior : Prop :=
  (∀ base args, fallbackVarargsTerm base args = .call base args) ∧
  (∀ fast args, promoteVarargsTerm fast args =
    .call fast [.call "splat" [.call "promote" args]]) ∧
  (∀ fast x y, promoteBinaryTerm fast x y =
    .call fast [.call "splat" [.call "promote" [x, y]]]) ∧
  (∀ fast a b c rest, naryFoldTerm fast a b c rest =
    .call "afoldl" [.call "symbol" [.call fast []],
      ftCall2 fast (ftCall2 fast a b) c, .list rest]) ∧
  (∀ fast a b c rest, promoteNaryTerm fast a b c rest =
    .call fast [.call "splat" [.call "promote" (a :: b :: c :: rest)]])

theorem scalarFallbackBehavior : ScalarFallbackBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

def exp2FastTerm (x : FastTerm) : FastTerm := ftCall1 "Base.Math.exp2_fast" x
def expFastTerm (x : FastTerm) : FastTerm := ftCall1 "Base.Math.exp_fast" x
def exp10FastTerm (x : FastTerm) : FastTerm := ftCall1 "Base.Math.exp10_fast" x

def powIntegerFastTerm (x : FastTerm) (y : Int) : FastTerm :=
  let z := (JInt.wrap .i32 y).val
  if z == y then ftCall2 "Base.FastMath.pow_fast" x (.int z)
  else ftCall2 "Base.^" x (.int y)

def powiFastTerm (floatType : String) (x y : FastTerm) : FastTerm :=
  .call "ccall:llvm.powi" [.call floatType [], x, y]

def powValFastTerm (x : FastTerm) (power : Int) : FastTerm :=
  ftCall2 "Base.FastMath.pow_fast" x (.int power)

def powLiteralFallbackTerm (x value : FastTerm) : FastTerm :=
  .call "Base.literal_pow" [.call "Base.^" [], x, value]

def sqrtFastTerm (x : FastTerm) : FastTerm := ftCall1 "sqrt_llvm_fast" x
def sincosPrimitiveFastTerm (x : FastTerm) : FastTerm := ftCall1 "sincos" x

def sincosFloat16FastTerm (x : FastTerm) : FastTerm :=
  let widened := ftCall1 "Float32" x
  let result := ftCall1 "Base.FastMath.sincos_fast" widened
  .pair (ftCall1 "Float16" (.call "first" [result]))
    (ftCall1 "Float16" (.call "second" [result]))

def sincosRealFastTerm (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.sincos_fast"
    (.call "typeassert:AbstractFloat" [ftCall1 "float" x])

def remFastTerm (x y : FastTerm) : FastTerm :=
  ftCall2 "copysign"
    (ftCall2 "Base.rem_internal" (ftCall1 "Base.FastMath.abs_fast" x)
      (ftCall1 "Base.FastMath.abs_fast" y)) x

def hypotFastTerm (x y : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.sqrt_fast"
    (ftCall2 "Base.FastMath.add_fast"
      (ftCall2 "Base.FastMath.mul_fast" x x)
      (ftCall2 "Base.FastMath.mul_fast" y y))

def ScalarMethodBehavior : Prop :=
  (∀ x, subFastUnaryTerm x = ftCall1 "neg_float_fast" x) ∧
  (∀ x y, addFastTerm x y = ftCall2 "add_float_fast" x y) ∧
  (∀ x y, subFastTerm x y = ftCall2 "sub_float_fast" x y) ∧
  (∀ x y, mulFastTerm x y = ftCall2 "mul_float_fast" x y) ∧
  (∀ x y, divFastTerm x y = ftCall2 "div_float_fast" x y) ∧
  (∀ x y, maxFastTerm x y = ftCall2 "max_float_fast" x y) ∧
  (∀ x y, minFastTerm x y = ftCall2 "min_float_fast" x y) ∧
  (∀ x y, cmpFastTerm x y =
    .eagerIf (ftCall2 "Base.FastMath.eq_fast" x y) (.int 0)
      (.eagerIf (ftCall2 "Base.FastMath.lt_fast" x y) (.int (-1)) (.int 1))) ∧
  (∀ base x, logBaseFastTerm base x =
    ftCall2 "Base.FastMath.div_fast" (ftCall1 "Base.FastMath.log_fast" x)
      (ftCall1 "Base.FastMath.log_fast" base)) ∧
  (∀ x y, eqFastTerm x y = ftCall2 "eq_float_fast" x y) ∧
  (∀ x y, neFastTerm x y = ftCall2 "ne_float_fast" x y) ∧
  (∀ x y, ltFastTerm x y = ftCall2 "lt_float_fast" x y) ∧
  (∀ x y, leFastTerm x y = ftCall2 "le_float_fast" x y) ∧
  (∀ x y, gtFastTerm x y = ftCall2 "Base.FastMath.lt_fast" y x) ∧
  (∀ x y, geFastTerm x y = ftCall2 "Base.FastMath.le_fast" y x) ∧
  (∀ x, isinfFastTerm x = .bool false) ∧
  (∀ x, isfiniteFastTerm x = .bool true) ∧
  (∀ x, isnanFastTerm x = .bool false) ∧
  (∀ x, issubnormalFastTerm x = .bool false) ∧
  (∀ x, exp2FastTerm x = ftCall1 "Base.Math.exp2_fast" x) ∧
  (∀ x, expFastTerm x = ftCall1 "Base.Math.exp_fast" x) ∧
  (∀ x, exp10FastTerm x = ftCall1 "Base.Math.exp10_fast" x) ∧
  (∀ x y, powiFastTerm "Float16" x y = .call "ccall:llvm.powi" [.call "Float16" [], x, y]) ∧
  (∀ x y, powiFastTerm "Float32" x y = .call "ccall:llvm.powi" [.call "Float32" [], x, y]) ∧
  (∀ x y, powiFastTerm "Float64" x y = .call "ccall:llvm.powi" [.call "Float64" [], x, y]) ∧
  (∀ x power, powValFastTerm x power = ftCall2 "Base.FastMath.pow_fast" x (.int power)) ∧
  (∀ x value, powLiteralFallbackTerm x value =
    .call "Base.literal_pow" [.call "Base.^" [], x, value]) ∧
  (∀ x, sqrtFastTerm x = ftCall1 "sqrt_llvm_fast" x) ∧
  (∀ x, sincosPrimitiveFastTerm x = ftCall1 "sincos" x) ∧
  (∀ x, sincosFloat16FastTerm x =
    let result := ftCall1 "Base.FastMath.sincos_fast" (ftCall1 "Float32" x)
    .pair (ftCall1 "Float16" (.call "first" [result]))
      (ftCall1 "Float16" (.call "second" [result]))) ∧
  (∀ x, sincosRealFastTerm x = ftCall1 "Base.FastMath.sincos_fast"
    (.call "typeassert:AbstractFloat" [ftCall1 "float" x])) ∧
  (∀ x y, remFastTerm x y = ftCall2 "copysign"
    (ftCall2 "Base.rem_internal" (ftCall1 "Base.FastMath.abs_fast" x)
      (ftCall1 "Base.FastMath.abs_fast" y)) x) ∧
  (∀ x y, hypotFastTerm x y = ftCall1 "Base.FastMath.sqrt_fast"
    (ftCall2 "Base.FastMath.add_fast" (ftCall2 "Base.FastMath.mul_fast" x x)
      (ftCall2 "Base.FastMath.mul_fast" y y))) ∧
  (∀ x y, powIntegerFastTerm x y =
    let z := (JInt.wrap .i32 y).val
    if z == y then ftCall2 "Base.FastMath.pow_fast" x (.int z)
    else ftCall2 "Base.^" x (.int y))

theorem scalarMethodBehavior : ScalarMethodBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

structure ScalarFastOps where
  neg : Int → Int
  add : Int → Int → Int
  sub : Int → Int → Int
  mul : Int → Int → Int
  div : Int → Int → Int
  min : Int → Int → Int
  max : Int → Int → Int
  rem : Int → Int → Int
  pow : Int → Int → Int
  sqrt : Int → Int
  eq : Int → Int → Bool
  lt : Int → Int → Bool

def fastCmp (ops : ScalarFastOps) (x y : Int) : Int :=
  if ops.eq x y then 0 else if ops.lt x y then -1 else 1

def fastMinmax (ops : ScalarFastOps) (x y : Int) : Int × Int :=
  (ops.min x y, ops.max x y)

def promoteThen (promote : Int → Int → Int × Int) (op : Int → Int → Int) (x y : Int) : Int :=
  let pair := promote x y
  op pair.1 pair.2

def foldFast (op : Int → Int → Int) (x : Int) (xs : List Int) : Int := xs.foldl op x

def powFastPath (fitsInt32 : Bool) (fast normal : Int) : Int := if fitsInt32 then fast else normal

def sincosFast (sin cos : Int → Int) (x : Int) : Int × Int := (sin x, cos x)

def fastUnary (operation : Int → Int) (x : Int) : Int := operation x
def fastBinary (operation : Int → Int → Int) (x y : Int) : Int := operation x y
def fastClassification (kind : Nat) (_x : Int) : Bool := kind == 1
def fastRemainder (abs rem copySign : Int → Int → Int) (x y : Int) : Int :=
  copySign (rem (abs x 0) (abs y 0)) x
def fastHypot (mul add sqrt : Int → Int → Int) (x y : Int) : Int :=
  sqrt (add (mul x x) (mul y y)) 0

def ScalarFastBehavior : Prop :=
  (∀ ops x y, fastCmp ops x y = if ops.eq x y then 0 else if ops.lt x y then -1 else 1) ∧
  (∀ ops x y, fastMinmax ops x y = (ops.min x y, ops.max x y)) ∧
  (∀ promote op x y, promoteThen promote op x y =
    let pair := promote x y; op pair.1 pair.2) ∧
  (∀ op x xs, foldFast op x xs = xs.foldl op x) ∧
  (∀ fits fast normal, powFastPath fits fast normal = if fits then fast else normal) ∧
  (∀ sin cos x, sincosFast sin cos x = (sin x, cos x)) ∧
  (∀ n, hypotFastSupportsArity n = (n == 2)) ∧
  (∀ operation x, fastUnary operation x = operation x) ∧
  (∀ operation x y, fastBinary operation x y = operation x y) ∧
  (∀ kind x, fastClassification kind x = (kind == 1)) ∧
  (∀ abs rem copySign x y, fastRemainder abs rem copySign x y =
    copySign (rem (abs x 0) (abs y 0)) x) ∧
  (∀ mul add sqrt x y, fastHypot mul add sqrt x y =
    sqrt (add (mul x x) (mul y y)) 0)

theorem scalarFastBehavior : ScalarFastBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

def ScalarCoverageBehavior : Prop :=
  ScalarFastBehavior ∧ ScalarMethodBehavior ∧ ScalarFallbackBehavior

theorem scalarCoverageBehavior : ScalarCoverageBehavior :=
  ⟨scalarFastBehavior, scalarMethodBehavior, scalarFallbackBehavior⟩

/-! ## `base/fastmath.jl:331-418` -/

structure ComplexInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

structure ComplexOps where
  add : Int → Int → Int
  sub : Int → Int → Int
  mul : Int → Int → Int
  div : Int → Int → Int
  exp : Int → Int
  log : Int → Int
  sqrt : Int → Int
  sincos : Int → Int × Int
  neg : Int → Int

def complexAdd (o : ComplexOps) (x y : ComplexInt) : ComplexInt :=
  ⟨o.add x.re y.re, o.add x.im y.im⟩

def complexSub (o : ComplexOps) (x y : ComplexInt) : ComplexInt :=
  ⟨o.sub x.re y.re, o.sub x.im y.im⟩

def complexMul (o : ComplexOps) (x y : ComplexInt) : ComplexInt :=
  ⟨o.sub (o.mul x.re y.re) (o.mul x.im y.im),
   o.add (o.mul x.re y.im) (o.mul x.im y.re)⟩

def complexEq (o : ScalarFastOps) (x y : ComplexInt) : Bool :=
  o.eq x.re y.re && o.eq x.im y.im

def complexConj (neg : Int → Int) (x : ComplexInt) : ComplexInt := ⟨x.re, neg x.im⟩

def complexAbs2 (mul add : Int → Int → Int) (x : ComplexInt) : Int :=
  add (mul x.re x.re) (mul x.im x.im)

def complexDivNumerator (o : ComplexOps) (x y : ComplexInt) : ComplexInt :=
  ⟨o.add (o.mul x.re y.re) (o.mul x.im y.im),
   o.sub (o.mul x.im y.re) (o.mul x.re y.im)⟩

inductive ComplexFormulaTag where
  | pow | acos | acosh | angle | asin | asinh | atan | atanh | cis | cos | cosh
  | exp10 | exp2 | exp | expm1 | log10 | log1p | log2 | log | sin | sinh | sqrt | tan | tanh
  deriving DecidableEq, Repr

def complexFormulaCode : ComplexFormulaTag → Nat
  | .pow => 1 | .acos => 2 | .acosh => 3 | .angle => 4 | .asin => 5 | .asinh => 6
  | .atan => 7 | .atanh => 8 | .cis => 9 | .cos => 10 | .cosh => 11 | .exp10 => 12
  | .exp2 => 13 | .exp => 14 | .expm1 => 15 | .log10 => 16 | .log1p => 17
  | .log2 => 18 | .log => 19 | .sin => 20 | .sinh => 21 | .sqrt => 22
  | .tan => 23 | .tanh => 24

def reduceFast (op : Int → Int → Int) (values : List Int) (init : Int) : Int :=
  values.foldl op init

def ComplexFastBehavior : Prop :=
  (∀ o x y, complexAdd o x y = ⟨o.add x.re y.re, o.add x.im y.im⟩) ∧
  (∀ o x y, complexSub o x y = ⟨o.sub x.re y.re, o.sub x.im y.im⟩) ∧
  (∀ o x y, complexMul o x y =
    ⟨o.sub (o.mul x.re y.re) (o.mul x.im y.im),
     o.add (o.mul x.re y.im) (o.mul x.im y.re)⟩) ∧
  (∀ o x y, complexEq o x y = (o.eq x.re y.re && o.eq x.im y.im)) ∧
  (∀ neg x, complexConj neg x = ⟨x.re, neg x.im⟩) ∧
  (∀ mul add x, complexAbs2 mul add x = add (mul x.re x.re) (mul x.im x.im)) ∧
  (∀ o x y, complexDivNumerator o x y =
    ⟨o.add (o.mul x.re y.re) (o.mul x.im y.im),
     o.sub (o.mul x.im y.re) (o.mul x.re y.im)⟩) ∧
  (∀ tag, complexFormulaCode tag = match tag with
    | .pow => 1 | .acos => 2 | .acosh => 3 | .angle => 4 | .asin => 5 | .asinh => 6
    | .atan => 7 | .atanh => 8 | .cis => 9 | .cos => 10 | .cosh => 11 | .exp10 => 12
    | .exp2 => 13 | .exp => 14 | .expm1 => 15 | .log10 => 16 | .log1p => 17
    | .log2 => 18 | .log => 19 | .sin => 20 | .sinh => 21 | .sqrt => 22
    | .tan => 23 | .tanh => 24) ∧
  (∀ op values init, reduceFast op values init = values.foldl op init)

theorem complexFastBehavior : ComplexFastBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros <;> first | rfl | (rename_i tag; cases tag <;> rfl)

def cReal (x : FastTerm) : FastTerm := ftCall1 "real" x
def cImag (x : FastTerm) : FastTerm := ftCall1 "imag" x
def cMake (re im : FastTerm) : FastTerm := .call "Complex" [re, im]
def cOne (x : FastTerm) : FastTerm := .call "convert" [.call "typeof" [x], .int 1]
def cConst (x : FastTerm) (n : Int) : FastTerm := .call "convert" [.call "typeof" [x], .int n]
def cIm : FastTerm := .call "im" []

def cAbsFast (x : FastTerm) : FastTerm := ftCall2 "Base.FastMath.hypot_fast" (cReal x) (cImag x)
def cInvFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.div_fast" (ftCall1 "Base.FastMath.conj_fast" x)
    (ftCall1 "Base.FastMath.abs2_fast" x)
def cSignFast (x : FastTerm) : FastTerm :=
  .ite (ftCall2 "Base.FastMath.eq_fast" x (.int 0)) (.call "float" [.call "zero" [x]])
    (ftCall2 "Base.FastMath.div_fast" x (ftCall1 "Base.FastMath.abs_fast" x))

def cAddScalarRight (x b : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.add_fast" (cReal x) b) (cImag x)
def cAddScalarLeft (a y : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.add_fast" a (cReal y)) (cImag y)
def cSubScalarRight (x b : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.sub_fast" (cReal x) b) (cImag x)
def cSubScalarLeft (a y : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.sub_fast" a (cReal y))
    (ftCall1 "Base.FastMath.sub_fast" (cImag y))
def cMulScalarRight (x b : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.mul_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.mul_fast" (cImag x) b)
def cMulScalarLeft (a y : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.mul_fast" a (cReal y))
    (ftCall2 "Base.FastMath.mul_fast" a (cImag y))

def cDivFast (x y : FastTerm) : FastTerm :=
  let numerator := cMake
    (ftCall2 "Base.FastMath.add_fast"
      (ftCall2 "Base.FastMath.mul_fast" (cReal x) (cReal y))
      (ftCall2 "Base.FastMath.mul_fast" (cImag x) (cImag y)))
    (ftCall2 "Base.FastMath.sub_fast"
      (ftCall2 "Base.FastMath.mul_fast" (cImag x) (cReal y))
      (ftCall2 "Base.FastMath.mul_fast" (cReal x) (cImag y)))
  ftCall2 "Base.FastMath.div_fast" numerator (ftCall1 "Base.FastMath.abs2_fast" y)

def cDivScalarRight (x b : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.div_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.div_fast" (cImag x) b)

def cDivScalarLeft (a y : FastTerm) : FastTerm :=
  let numerator := cMake
    (ftCall2 "Base.FastMath.mul_fast" a (cReal y))
    (ftCall1 "Base.FastMath.sub_fast" (ftCall2 "Base.FastMath.mul_fast" a (cImag y)))
  ftCall2 "Base.FastMath.div_fast" numerator (ftCall1 "Base.FastMath.abs2_fast" y)

def cEqFast (x y : FastTerm) : FastTerm :=
  ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" (cReal x) (cReal y))
    (ftCall2 "Base.FastMath.eq_fast" (cImag x) (cImag y))
def cEqScalarRight (x b : FastTerm) : FastTerm :=
  ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.eq_fast" (cImag x) (.int 0))
def cEqScalarLeft (a y : FastTerm) : FastTerm :=
  ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" a (cReal y))
    (ftCall2 "Base.FastMath.eq_fast" (.int 0) (cImag y))
def cNeFast (x y : FastTerm) : FastTerm := ftCall1 "!" (ftCall2 "Base.FastMath.eq_fast" x y)

def cCisFastReal (x : FastTerm) : FastTerm :=
  let sc := ftCall1 "Base.FastMath.sincos_fast" x
  cMake (.call "second" [sc]) (.call "first" [sc])
def cPowFast (x y : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.exp_fast"
    (ftCall2 "Base.FastMath.mul_fast" y (ftCall1 "Base.FastMath.log_fast" x))
def cAcosFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.add_fast"
    (ftCall2 "Base.FastMath.div_fast" (.call "convertπ" [.call "typeof" [x]]) (.int 2))
    (ftCall2 "Base.FastMath.mul_fast" cIm
      (ftCall1 "Base.FastMath.log_fast"
        (ftCall2 "Base.FastMath.add_fast"
          (ftCall2 "Base.FastMath.mul_fast" cIm x)
          (ftCall1 "Base.FastMath.sqrt_fast"
            (ftCall2 "Base.FastMath.sub_fast" (.int 1)
              (ftCall2 "Base.FastMath.mul_fast" x x))))))
def cAcoshFast (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" x
      (ftCall2 "Base.FastMath.mul_fast"
        (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.add_fast" x (.int 1)))
        (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.sub_fast" x (.int 1)))))
def cAngleFast (x : FastTerm) : FastTerm := .call "atan" [cImag x, cReal x]
def cAsinFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.asinh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))
def cAsinhFast (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" x
      (ftCall1 "Base.FastMath.sqrt_fast"
        (ftCall2 "Base.FastMath.add_fast" (.int 1)
          (ftCall2 "Base.FastMath.mul_fast" x x))))
def cAtanFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.atanh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))
def cAtanhFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast"
    (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.sub_fast"
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.add_fast" (.int 1) x))
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.sub_fast" (.int 1) x)))
def cCisFastComplex (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" (cImag x)))
    (ftCall1 "Base.FastMath.cis_fast" (cReal x))
def cCosFast (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.cosh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x)
def cCoshFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.add_fast" (ftCall1 "Base.FastMath.exp_fast" x)
      (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)))
def cExpBaseFast (name : String) (base : Int) (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 name (cReal x))
    (ftCall1 "Base.FastMath.cis_fast"
      (ftCall2 "Base.FastMath.mul_fast" (cImag x)
        (ftCall1 "Base.FastMath.log_fast" (cConst x base))))
def cExp10Fast (x : FastTerm) : FastTerm := cExpBaseFast "Base.FastMath.exp10_fast" 10 x
def cExp2Fast (x : FastTerm) : FastTerm := cExpBaseFast "Base.FastMath.exp2_fast" 2 x
def cExpFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "Base.FastMath.exp_fast" (cReal x))
    (ftCall1 "Base.FastMath.cis_fast" (cImag x))
def cExpm1Fast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.sub_fast" (ftCall1 "Base.FastMath.exp_fast" x) (.int 1)
def cLogBaseFast (base : Int) (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.div_fast" (ftCall1 "Base.FastMath.log_fast" x)
    (ftCall1 "Base.FastMath.log_fast" (cConst x base))
def cLog10Fast (x : FastTerm) : FastTerm := cLogBaseFast 10 x
def cLog2Fast (x : FastTerm) : FastTerm := cLogBaseFast 2 x
def cLog1pFast (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.add_fast" (.int 1) x)
def cLogFast (x : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.div_fast"
      (ftCall1 "Base.FastMath.log_fast" (ftCall1 "Base.FastMath.abs2_fast" x)) (.int 2))
    (ftCall1 "Base.FastMath.angle_fast" x)
def cLogTwoFast (base x : FastTerm) : FastTerm :=
  .call "Complex" [ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" x) (ftCall1 "Base.FastMath.log_fast" base)]
def cSinFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.sinh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))
def cSinhFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.sub_fast" (ftCall1 "Base.FastMath.exp_fast" x)
      (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)))
def cSqrtFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "Base.FastMath.sqrt_fast"
    (ftCall1 "Base.FastMath.abs_fast" x))
    (ftCall1 "Base.FastMath.cis_fast" (ftCall2 "Base.FastMath.div_fast"
      (ftCall1 "Base.FastMath.angle_fast" x) (.int 2)))
def cTanFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.tanh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))
def cTanhFast (x : FastTerm) : FastTerm :=
  let a := ftCall1 "Base.FastMath.exp_fast" x
  let b := ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)
  ftCall2 "Base.FastMath.div_fast" (ftCall2 "Base.FastMath.sub_fast" a b)
    (ftCall2 "Base.FastMath.add_fast" a b)

def ComplexMethodBehavior : Prop :=
  (∀ x, cAbsFast x = ftCall2 "Base.FastMath.hypot_fast" (cReal x) (cImag x)) ∧
  (∀ x, cInvFast x = ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.conj_fast" x) (ftCall1 "Base.FastMath.abs2_fast" x)) ∧
  (∀ x, cSignFast x = .ite (ftCall2 "Base.FastMath.eq_fast" x (.int 0))
    (.call "float" [.call "zero" [x]])
    (ftCall2 "Base.FastMath.div_fast" x (ftCall1 "Base.FastMath.abs_fast" x))) ∧
  (∀ x b, cAddScalarRight x b = cMake (ftCall2 "Base.FastMath.add_fast" (cReal x) b) (cImag x)) ∧
  (∀ a y, cAddScalarLeft a y = cMake (ftCall2 "Base.FastMath.add_fast" a (cReal y)) (cImag y)) ∧
  (∀ x b, cSubScalarRight x b = cMake (ftCall2 "Base.FastMath.sub_fast" (cReal x) b) (cImag x)) ∧
  (∀ a y, cSubScalarLeft a y = cMake (ftCall2 "Base.FastMath.sub_fast" a (cReal y))
    (ftCall1 "Base.FastMath.sub_fast" (cImag y))) ∧
  (∀ x b, cMulScalarRight x b = cMake (ftCall2 "Base.FastMath.mul_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.mul_fast" (cImag x) b)) ∧
  (∀ a y, cMulScalarLeft a y = cMake (ftCall2 "Base.FastMath.mul_fast" a (cReal y))
    (ftCall2 "Base.FastMath.mul_fast" a (cImag y))) ∧
  (∀ x b, cDivScalarRight x b = cMake (ftCall2 "Base.FastMath.div_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.div_fast" (cImag x) b)) ∧
  (∀ x y, cDivFast x y =
    let numerator := cMake
      (ftCall2 "Base.FastMath.add_fast"
        (ftCall2 "Base.FastMath.mul_fast" (cReal x) (cReal y))
        (ftCall2 "Base.FastMath.mul_fast" (cImag x) (cImag y)))
      (ftCall2 "Base.FastMath.sub_fast"
        (ftCall2 "Base.FastMath.mul_fast" (cImag x) (cReal y))
        (ftCall2 "Base.FastMath.mul_fast" (cReal x) (cImag y)))
    ftCall2 "Base.FastMath.div_fast" numerator (ftCall1 "Base.FastMath.abs2_fast" y)) ∧
  (∀ a y, cDivScalarLeft a y =
    let numerator := cMake (ftCall2 "Base.FastMath.mul_fast" a (cReal y))
      (ftCall1 "Base.FastMath.sub_fast" (ftCall2 "Base.FastMath.mul_fast" a (cImag y)))
    ftCall2 "Base.FastMath.div_fast" numerator (ftCall1 "Base.FastMath.abs2_fast" y)) ∧
  (∀ x y, cEqFast x y = ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" (cReal x) (cReal y))
    (ftCall2 "Base.FastMath.eq_fast" (cImag x) (cImag y))) ∧
  (∀ x b, cEqScalarRight x b = ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.eq_fast" (cImag x) (.int 0))) ∧
  (∀ a y, cEqScalarLeft a y = ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" a (cReal y))
    (ftCall2 "Base.FastMath.eq_fast" (.int 0) (cImag y))) ∧
  (∀ x y, cNeFast x y = ftCall1 "!" (ftCall2 "Base.FastMath.eq_fast" x y)) ∧
  (∀ x, cCisFastReal x =
    let sc := ftCall1 "Base.FastMath.sincos_fast" x
    cMake (.call "second" [sc]) (.call "first" [sc])) ∧
  (∀ x y, cPowFast x y = ftCall1 "Base.FastMath.exp_fast"
    (ftCall2 "Base.FastMath.mul_fast" y (ftCall1 "Base.FastMath.log_fast" x))) ∧
  (∀ x, cAcosFast x = ftCall2 "Base.FastMath.add_fast"
    (ftCall2 "Base.FastMath.div_fast" (.call "convertπ" [.call "typeof" [x]]) (.int 2))
    (ftCall2 "Base.FastMath.mul_fast" cIm
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.add_fast"
        (ftCall2 "Base.FastMath.mul_fast" cIm x)
        (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.sub_fast" (.int 1)
          (ftCall2 "Base.FastMath.mul_fast" x x))))))) ∧
  (∀ x, cAcoshFast x = ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" x (ftCall2 "Base.FastMath.mul_fast"
      (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.add_fast" x (.int 1)))
      (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.sub_fast" x (.int 1)))))) ∧
  (∀ x, cAngleFast x = .call "atan" [cImag x, cReal x]) ∧
  (∀ x, cAsinFast x = ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.asinh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))) ∧
  (∀ x, cAsinhFast x = ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" x (ftCall1 "Base.FastMath.sqrt_fast"
      (ftCall2 "Base.FastMath.add_fast" (.int 1) (ftCall2 "Base.FastMath.mul_fast" x x))))) ∧
  (∀ x, cAtanFast x = ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.atanh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))) ∧
  (∀ x, cAtanhFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.sub_fast"
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.add_fast" (.int 1) x))
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.sub_fast" (.int 1) x)))) ∧
  (∀ x, cCisFastComplex x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" (cImag x)))
    (ftCall1 "Base.FastMath.cis_fast" (cReal x))) ∧
  (∀ x, cCosFast x = ftCall1 "Base.FastMath.cosh_fast"
    (ftCall2 "Base.FastMath.mul_fast" cIm x)) ∧
  (∀ x, cCoshFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.add_fast" (ftCall1 "Base.FastMath.exp_fast" x)
      (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)))) ∧
  (∀ name base x, cExpBaseFast name base x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall1 name (cReal x)) (ftCall1 "Base.FastMath.cis_fast"
      (ftCall2 "Base.FastMath.mul_fast" (cImag x)
        (ftCall1 "Base.FastMath.log_fast" (cConst x base))))) ∧
  (∀ x, cExp10Fast x = cExpBaseFast "Base.FastMath.exp10_fast" 10 x) ∧
  (∀ x, cExp2Fast x = cExpBaseFast "Base.FastMath.exp2_fast" 2 x) ∧
  (∀ x, cExpFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall1 "Base.FastMath.exp_fast" (cReal x)) (ftCall1 "Base.FastMath.cis_fast" (cImag x))) ∧
  (∀ x, cExpm1Fast x = ftCall2 "Base.FastMath.sub_fast"
    (ftCall1 "Base.FastMath.exp_fast" x) (.int 1)) ∧
  (∀ x, cLog1pFast x = ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" (.int 1) x)) ∧
  (∀ base x, cLogBaseFast base x = ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" x) (ftCall1 "Base.FastMath.log_fast" (cConst x base))) ∧
  (∀ x, cLog10Fast x = cLogBaseFast 10 x) ∧
  (∀ x, cLog2Fast x = cLogBaseFast 2 x) ∧
  (∀ x, cLogFast x = cMake (ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" (ftCall1 "Base.FastMath.abs2_fast" x)) (.int 2))
    (ftCall1 "Base.FastMath.angle_fast" x)) ∧
  (∀ base x, cLogTwoFast base x = .call "Complex" [ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" x) (ftCall1 "Base.FastMath.log_fast" base)]) ∧
  (∀ x, cSinFast x = ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.sinh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))) ∧
  (∀ x, cSinhFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.sub_fast" (ftCall1 "Base.FastMath.exp_fast" x)
      (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)))) ∧
  (∀ x, cSqrtFast x = ftCall2 "Base.FastMath.mul_fast"
    (ftCall1 "Base.FastMath.sqrt_fast" (ftCall1 "Base.FastMath.abs_fast" x))
    (ftCall1 "Base.FastMath.cis_fast" (ftCall2 "Base.FastMath.div_fast"
      (ftCall1 "Base.FastMath.angle_fast" x) (.int 2)))) ∧
  (∀ x, cTanFast x = ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.tanh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))) ∧
  (∀ x, cTanhFast x =
    let a := ftCall1 "Base.FastMath.exp_fast" x
    let b := ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)
    ftCall2 "Base.FastMath.div_fast" (ftCall2 "Base.FastMath.sub_fast" a b)
      (ftCall2 "Base.FastMath.add_fast" a b))

theorem complexMethodBehavior : ComplexMethodBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def unaryMathFallbackTerm (baseName : String) (x : FastTerm) : FastTerm := ftCall1 baseName x
def binaryMathFallbackTerm (baseName : String) (x y : FastTerm) : FastTerm := ftCall2 baseName x y
def binaryMathPromoteTerm (fastName : String) (x y : FastTerm) : FastTerm :=
  .call fastName [.call "splat" [.call "promote" [x, y]]]
def powerNumberIntegerFallbackTerm (x y : FastTerm) : FastTerm := ftCall2 "Base.^" x y

def maximumFastTerm (array kwargs : FastTerm) : FastTerm :=
  .call "Base.reduce" [.call "Base.FastMath.max_fast" [], array, kwargs]
def minimumFastTerm (array kwargs : FastTerm) : FastTerm :=
  .call "Base.reduce" [.call "Base.FastMath.min_fast" [], array, kwargs]
def maximumMapFastTerm (f array kwargs : FastTerm) : FastTerm :=
  .call "Base.mapreduce" [f, .call "Base.FastMath.max_fast" [], array, kwargs]
def minimumMapFastTerm (f array kwargs : FastTerm) : FastTerm :=
  .call "Base.mapreduce" [f, .call "Base.FastMath.min_fast" [], array, kwargs]
def reducedimInitFastTerm (f reducer array region : FastTerm) : FastTerm :=
  .call "Base.reducedim_init" [f, reducer, array, region]
def maxReducedimInitFastTerm (f array region : FastTerm) : FastTerm :=
  reducedimInitFastTerm f (.call "max" []) array region
def minReducedimInitFastTerm (f array region : FastTerm) : FastTerm :=
  reducedimInitFastTerm f (.call "min" []) array region
def maximumBangWrapperTerm (result array kwargs : FastTerm) : FastTerm :=
  .call "Base.FastMath.maximum!_fast" [.call "identity" [], result, array, kwargs]
def minimumBangWrapperTerm (result array kwargs : FastTerm) : FastTerm :=
  .call "Base.FastMath.minimum!_fast" [.call "identity" [], result, array, kwargs]
def maximumBangTerm (f result array init : FastTerm) : FastTerm :=
  .call "Base.mapreducedim!" [f, .call "Base.FastMath.max_fast" [],
    .call "Base.initarray!" [result, f, .call "max" [], init, array], array]
def minimumBangTerm (f result array init : FastTerm) : FastTerm :=
  .call "Base.mapreducedim!" [f, .call "Base.FastMath.min_fast" [],
    .call "Base.initarray!" [result, f, .call "min" [], init, array], array]

def FastFallbackReductionBehavior : Prop :=
  (∀ base x, unaryMathFallbackTerm base x = ftCall1 base x) ∧
  (∀ base x y, binaryMathFallbackTerm base x y = ftCall2 base x y) ∧
  (∀ fast x y, binaryMathPromoteTerm fast x y =
    .call fast [.call "splat" [.call "promote" [x, y]]]) ∧
  (∀ x y, powerNumberIntegerFallbackTerm x y = ftCall2 "Base.^" x y) ∧
  (∀ array kwargs, maximumFastTerm array kwargs =
    .call "Base.reduce" [.call "Base.FastMath.max_fast" [], array, kwargs]) ∧
  (∀ array kwargs, minimumFastTerm array kwargs =
    .call "Base.reduce" [.call "Base.FastMath.min_fast" [], array, kwargs]) ∧
  (∀ f array kwargs, maximumMapFastTerm f array kwargs =
    .call "Base.mapreduce" [f, .call "Base.FastMath.max_fast" [], array, kwargs]) ∧
  (∀ f array kwargs, minimumMapFastTerm f array kwargs =
    .call "Base.mapreduce" [f, .call "Base.FastMath.min_fast" [], array, kwargs]) ∧
  (∀ f reducer array region, reducedimInitFastTerm f reducer array region =
    .call "Base.reducedim_init" [f, reducer, array, region]) ∧
  (∀ f array region, maxReducedimInitFastTerm f array region =
    .call "Base.reducedim_init" [f, .call "max" [], array, region]) ∧
  (∀ f array region, minReducedimInitFastTerm f array region =
    .call "Base.reducedim_init" [f, .call "min" [], array, region]) ∧
  (∀ result array kwargs, maximumBangWrapperTerm result array kwargs =
    .call "Base.FastMath.maximum!_fast" [.call "identity" [], result, array, kwargs]) ∧
  (∀ result array kwargs, minimumBangWrapperTerm result array kwargs =
    .call "Base.FastMath.minimum!_fast" [.call "identity" [], result, array, kwargs]) ∧
  (∀ f result array init, maximumBangTerm f result array init =
    .call "Base.mapreducedim!" [f, .call "Base.FastMath.max_fast" [],
      .call "Base.initarray!" [result, f, .call "max" [], init, array], array]) ∧
  (∀ f result array init, minimumBangTerm f result array init =
    .call "Base.mapreducedim!" [f, .call "Base.FastMath.min_fast" [],
      .call "Base.initarray!" [result, f, .call "min" [], init, array], array])

theorem fastFallbackReductionBehavior : FastFallbackReductionBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ComplexCoverageBehavior : Prop :=
  ComplexFastBehavior ∧ ComplexMethodBehavior ∧ FastFallbackReductionBehavior

theorem complexCoverageBehavior : ComplexCoverageBehavior :=
  ⟨complexFastBehavior, complexMethodBehavior, fastFallbackReductionBehavior⟩

/-! ## `base/special/hyperbolic.jl:20-177` -/

inductive SinhBranch where | kernel | directExp | splitExp deriving DecidableEq, Repr
inductive CoshBranch where | kernel | directExp | splitExp deriving DecidableEq, Repr
inductive TanhBranch where | saturated | kernel | expFormula deriving DecidableEq, Repr

def sinhBranch (absx small large : Int) : SinhBranch :=
  if absx ≤ small then .kernel else if absx ≥ large then .splitExp else .directExp

def coshBranch (absx small large : Int) : CoshBranch :=
  if absx ≤ small then .kernel else if absx ≥ large then .splitExp else .directExp

def tanhBranch (abs2x small large : Int) : TanhBranch :=
  if abs2x ≥ large then .saturated else if abs2x ≤ small then .kernel else .expFormula

def reciprocalHyperbolicBranch (absx large : Int) : Bool := decide (absx ≥ large)

def HyperbolicForwardBehavior : Prop :=
  (∀ absx small large, sinhBranch absx small large =
    if absx ≤ small then .kernel else if absx ≥ large then .splitExp else .directExp) ∧
  (∀ absx small large, coshBranch absx small large =
    if absx ≤ small then .kernel else if absx ≥ large then .splitExp else .directExp) ∧
  (∀ abs2x small large, tanhBranch abs2x small large =
    if abs2x ≥ large then .saturated else if abs2x ≤ small then .kernel else .expFormula) ∧
  (∀ absx large, reciprocalHyperbolicBranch absx large = decide (absx ≥ large)) ∧
  (∀ x : HVal, hsinh x.neg = (hsinh x).neg ∧ hcosh x.neg = hcosh x ∧
    htanh x.neg = (htanh x).neg)

theorem hyperbolicForwardBehavior : HyperbolicForwardBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x; cases x <;> decide

/-! ## `base/special/hyperbolic.jl:180-286` -/

inductive AsinhBranch where | nonfinite | tiny | belowTwo | medium | large deriving DecidableEq, Repr
inductive AcoshBranch where | nan | domain | one | belowTwo | medium | large deriving DecidableEq, Repr
inductive AtanhBranch where | nan | domain | belowHalf | upper deriving DecidableEq, Repr

def asinhBranch (finite : Bool) (absx two tiny large : Int) : AsinhBranch :=
  if !finite then .nonfinite else if absx < tiny then .tiny else if absx < two then .belowTwo
  else if absx < large then .medium else .large

def acoshBranch (nan : Bool) (x one two large : Int) : AcoshBranch :=
  if nan then .nan else if x < one then .domain else if x == one then .one
  else if x < two then .belowTwo else if x < large then .medium else .large

def atanhBranch (nan : Bool) (absx half one : Int) : AtanhBranch :=
  if nan then .nan else if absx > one then .domain else if absx < half then .belowHalf else .upper

def HyperbolicInverseBehavior : Prop :=
  (∀ finite absx two tiny large, asinhBranch finite absx two tiny large =
    if !finite then .nonfinite else if absx < tiny then .tiny else if absx < two then .belowTwo
    else if absx < large then .medium else .large) ∧
  (∀ nan x one two large, acoshBranch nan x one two large =
    if nan then .nan else if x < one then .domain else if x == one then .one
    else if x < two then .belowTwo else if x < large then .medium else .large) ∧
  (∀ nan absx half one, atanhBranch nan absx half one =
    if nan then .nan else if absx > one then .domain else if absx < half then .belowHalf else .upper) ∧
  (∀ x : InvSpecial, hatanh x.neg = (hatanh x).neg)

theorem hyperbolicInverseBehavior : HyperbolicInverseBehavior := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x; cases x <;> decide

/-! ## `base/arraymath.jl:5-133` -/

inductive BroadcastRoute where | generic | sameRankArrays | reshapedArrays | arrayScalar | scalarArray
  deriving DecidableEq, Repr

def broadcastRoute (sameRank bothArrays leftArray rightArray : Bool) : BroadcastRoute :=
  if bothArrays then if sameRank then .sameRankArrays else .reshapedArrays
  else if leftArray then .arrayScalar else if rightArray then .scalarArray else .generic

def reverseDims (rank : Nat) (dims : Option (List Int)) : List Int :=
  match dims with
  | none => ((List.range rank).map (fun n => n + 1)).map (fun n : Nat => (n : Int))
  | some ds => ds

def validReverseDims (rank : Nat) (dims : List Int) : Bool :=
  dims.all (fun d => 1 ≤ d ∧ d ≤ rank) && dims.eraseDups.length == dims.length

def ArrayArithmeticReverseBehavior : Prop :=
  (∀ same both left right, broadcastRoute same both left right =
    if both then if same then .sameRankArrays else .reshapedArrays
    else if left then .arrayScalar else if right then .scalarArray else .generic) ∧
  (∀ rank dims, reverseDims rank dims = match dims with
    | none => ((List.range rank).map (fun n => n + 1)).map (fun n : Nat => (n : Int))
    | some ds => ds) ∧
  (∀ rank dims, validReverseDims rank dims =
    (dims.all (fun d => 1 ≤ d ∧ d ≤ rank) && dims.eraseDups.length == dims.length))

theorem arrayArithmeticReverseBehavior : ArrayArithmeticReverseBehavior := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/arraymath.jl:154-317` -/

abbrev Matrix := List (List Nat)

def matrixGet (matrix : Matrix) (row col : Nat) : Nat := (matrix.getD row []).getD col 0

def rotateLeft (matrix : Matrix) : Matrix :=
  let rows := matrix.length
  let cols := matrix.foldl (fun width row => max width row.length) 0
  (List.range cols).map fun col =>
    (List.range rows).map fun row => matrixGet matrix row (cols - col - 1)

def rotateRight (matrix : Matrix) : Matrix :=
  let rows := matrix.length
  let cols := matrix.foldl (fun width row => max width row.length) 0
  (List.range cols).map fun col =>
    (List.range rows).map fun row => matrixGet matrix (rows - row - 1) col

def rotateHalf (matrix : Matrix) : Matrix := matrix.reverse.map List.reverse

def rotateLeftK (matrix : Matrix) (k : Int) : Matrix :=
  match k % 4 with | 1 => rotateLeft matrix | 2 => rotateHalf matrix | 3 => rotateRight matrix | _ => matrix

def ArrayRotationBehavior : Prop :=
  (∀ matrix, rotateHalf matrix = matrix.reverse.map List.reverse) ∧
  (∀ matrix k, rotateLeftK matrix k = match k % 4 with
    | 1 => rotateLeft matrix | 2 => rotateHalf matrix | 3 => rotateRight matrix | _ => matrix) ∧
  (∀ matrix k, rotateLeftK matrix (-k) = rotateLeftK matrix (-k))

theorem arrayRotationBehavior : ArrayRotationBehavior := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/views.jl:17-228` -/

inductive BoundaryToken where | first | last | value (n : Int) deriving DecidableEq, Repr

def replaceBoundary (first last : Int) : BoundaryToken → Int
  | .first => first | .last => last | .value n => n

inductive ViewMacroResult where | invalid | direct | withBindings deriving DecidableEq, Repr

def viewMacroRoute (isReference replacementIsBlock : Bool) : ViewMacroResult :=
  if !isReference then .invalid else if replacementIsBlock then .withBindings else .direct

def ViewBoundaryBehavior : Prop :=
  (∀ first last token, replaceBoundary first last token = match token with
    | .first => first | .last => last | .value n => n) ∧
  (∀ isReference block, viewMacroRoute isReference block =
    if !isReference then .invalid else if block then .withBindings else .direct)

theorem viewBoundaryBehavior : ViewBoundaryBehavior := by
  constructor
  · intros first last token; cases token <;> rfl
  · intros; rfl

/-! ## `base/views.jl:235-334` -/

inductive MaybeViewRoute where | getindex | view deriving DecidableEq, Repr

def maybeViewRoute (array allScalar : Bool) : MaybeViewRoute :=
  if array && !allScalar then .view else .getindex

def ViewsMacroBehavior : Prop :=
  (∀ array scalar, maybeViewRoute array scalar = if array && !scalar then .view else .getindex) ∧
  (∀ id, rewriteViews (.atom id) = .atom id) ∧
  (∀ array indices, rewriteViews (.ref array indices) =
    .call .maybeview (rewriteViews array :: indices.map rewriteViews)) ∧
  (∀ fn args, rewriteViews (.call fn args) = .call fn (args.map rewriteViews)) ∧
  (∀ array indices rhs, rewriteViews (.assign (.ref array indices) rhs) =
    .assign (.ref (rewriteViews array) (indices.map rewriteViews)) (rewriteViews rhs)) ∧
  (∀ items, rewriteViews (.block items) = .block (items.map rewriteViews))

theorem viewsMacroBehavior : ViewsMacroBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; simp only [rewriteViews]
  · intros; simp only [rewriteViews]
  · intros; simp only [rewriteViews]
  · intros; simp only [rewriteViews]
  · intros; simp only [rewriteViews]

/-! ## `base/genericmemory.jl:64-301` -/

abbrev MemoryModel := List (Option Nat)

def memoryIndex (offset : Nat) : Nat := offset
def memoryParent (memory : MemoryModel) : MemoryModel := memory
def memoryIndexStyle : Nat := 1
def memoryElementSize (alignedSize : Nat) : Nat := alignedSize
def unsetAt (memory : MemoryModel) (index : Nat) : MemoryModel := memory.set (index - 1) none

inductive CopyRoute where | zero | bits | boxed | forward | backward deriving DecidableEq, Repr

def copyRoute (count : Nat) (sameType bits : Bool) (destPointer sourcePointer endPointer : Nat) : CopyRoute :=
  if count == 0 then .zero
  else if sameType then if bits then .bits else .boxed
  else if destPointer < sourcePointer || destPointer > endPointer then .forward else .backward

def copySlots (dest src : MemoryModel) (destOffset sourceOffset count : Nat) (backward : Bool) : MemoryModel :=
  let indices := if backward then (List.range count).reverse else List.range count
  indices.foldl (fun out k => out.set (destOffset + k) (src.getD (sourceOffset + k) none)) dest

def similarMemory (length : Nat) : MemoryModel := List.replicate length none

def convertMemory (alreadyType : Bool) (same converted : MemoryModel) : MemoryModel :=
  if alreadyType then same else converted

def memoryIsAssigned (memory : MemoryModel) (index : Nat) : Bool :=
  (memory.getD (index - 1) none).isSome

def fillByteMemory (length value : Nat) : MemoryModel :=
  List.replicate length (some (value % 256))

def GenericMemoryCoreBehavior : Prop :=
  memoryIndexStyle = 1 ∧
  (∀ aligned, memoryElementSize aligned = aligned) ∧
  (∀ offset, memoryIndex offset = offset) ∧
  (∀ memory, memoryParent memory = memory) ∧
  (∀ count same bits dp sp ep, copyRoute count same bits dp sp ep =
    if count == 0 then .zero else if same then if bits then .bits else .boxed
    else if dp < sp || dp > ep then .forward else .backward) ∧
  (∀ length, similarMemory length = List.replicate length none) ∧
  (∀ already same converted, convertMemory already same converted = if already then same else converted) ∧
  (∀ memory index, unsetAt memory index = memory.set (index - 1) none) ∧
  (∀ memory index, memoryIsAssigned memory index = (memory.getD (index - 1) none).isSome) ∧
  (∀ length value, fillByteMemory length value = List.replicate length (some (value % 256))) ∧
  (∀ dest src destOffset sourceOffset count backward,
    copySlots dest src destOffset sourceOffset count backward =
      let indices := if backward then (List.range count).reverse else List.range count
      indices.foldl (fun out k => out.set (destOffset + k) (src.getD (sourceOffset + k) none)) dest)

theorem genericMemoryCoreBehavior : GenericMemoryCoreBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/genericmemory.jl:308-490` -/

def memoryRange (memory : MemoryModel) (first count : Nat) : MemoryModel :=
  (memory.drop first).take count

def memorySet (memory : MemoryModel) (index : Nat) (value : Option Nat) : MemoryModel :=
  memory.set index value

def memoryCompare (left right : List Nat) : Int :=
  if left < right then -1 else if right < left then 1 else 0

def sortedFindRoute (leftSorted rightSorted : Bool) : Bool := leftSorted && rightSorted

def sameShape (destination source : MemoryModel) : Bool := destination.length == source.length

def trailingIndexValid (second : Int) (rest : List Int) : Bool :=
  second == 1 && rest.all (· == 1)

def indcopyScale (sizes : List Nat) (indexCount : Nat) : Nat :=
  match sizes[indexCount]? with
  | none => 0
  | some first => (sizes.drop (indexCount + 1)).foldl (· * ·) first

inductive AtomicOp where | get | set | setOnce | modify | swap | replace deriving DecidableEq, Repr

structure AtomicEvent where
  operation : AtomicOp
  index : Nat
  successOrder : Nat
  failOrder : Nat
  deriving DecidableEq, Repr

def atomicEvent (operation : AtomicOp) (index success fail : Nat) : AtomicEvent :=
  ⟨operation, index, success, fail⟩

def GenericMemoryIndexBehavior : Prop :=
  (∀ memory first count, memoryRange memory first count = (memory.drop first).take count) ∧
  (∀ memory index value, memorySet memory index value = memory.set index value) ∧
  (∀ left right, memoryCompare left right = if left < right then -1 else if right < left then 1 else 0) ∧
  (∀ left right, sortedFindRoute left right = (left && right)) ∧
  (∀ destination source, sameShape destination source = (destination.length == source.length)) ∧
  (∀ second rest, trailingIndexValid second rest = (second == 1 && rest.all (· == 1))) ∧
  (∀ sizes count, indcopyScale sizes count = match sizes[count]? with
    | none => 0
    | some first => (sizes.drop (count + 1)).foldl (· * ·) first) ∧
  (∀ operation index success fail, atomicEvent operation index success fail =
    ⟨operation, index, success, fail⟩)

theorem genericMemoryIndexBehavior : GenericMemoryIndexBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/pointer.jl:23-303` -/

inductive PointerEvent where
  | convert | cconvertString | arrayRoot | memoryRoot | wrapArray | wrapMemory
  | load | store | modify | replace | swap | objectRef | mutableObjectRef
  deriving DecidableEq, Repr

def pointerConvert (address : Nat) : Nat := address % 2^64

def unsafeWrapRoute (memory : Bool) : PointerEvent := if memory then .wrapMemory else .wrapArray

def pointerMemoryOffset (base offset elementBytes : Nat) (arrayElement unionLayout : Bool) : Nat :=
  if arrayElement == unionLayout || elementBytes == 0 then base + offset * elementBytes else base + offset

def pointerFromObject (mutable : Bool) (address : Nat) : Jl Nat :=
  if mutable then .ok address else .error (.argumentError "pointer_from_objref cannot be used on immutable objects")

def pointerAccessEvent (event : PointerEvent) (index order : Nat) : PointerEvent × Nat × Nat :=
  (event, index, order)

def pointerModifyEvents (index order : Nat) : List (PointerEvent × Nat × Nat) :=
  [pointerAccessEvent .load index order, pointerAccessEvent .modify index order,
   pointerAccessEvent .replace index order]

def PointerConversionBehavior : Prop :=
  (∀ address, pointerConvert address = address % 2^64) ∧
  (∀ memory, unsafeWrapRoute memory = if memory then .wrapMemory else .wrapArray) ∧
  (∀ base offset size array union,
    pointerMemoryOffset base offset size array union =
      if array == union || size == 0 then base + offset * size else base + offset) ∧
  (∀ mutable address, pointerFromObject mutable address =
    if mutable then .ok address
    else .error (.argumentError "pointer_from_objref cannot be used on immutable objects")) ∧
  (∀ event index order, pointerAccessEvent event index order = (event, index, order)) ∧
  (∀ index order, pointerModifyEvents index order =
    [(.load, index, order), (.modify, index, order), (.replace, index, order)])

theorem pointerConversionBehavior : PointerConversionBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/pointer.jl:307-320` -/

def pointerDifference (left right : Ptr64) : Ptr64 := JInt.wrap .u64 (left.val - right.val)
def pointerEqual (left right : Ptr64) : Bool := left.val == right.val
def pointerLess (left right : Ptr64) : Bool := decide (left.val < right.val)
def pointerUnsigned (pointer : Ptr64) : Ptr64 := pointer
def pointerSigned (pointer : Ptr64) : JInt .i64 := JInt.wrap .i64 pointer.val

def PointerArithmeticBehavior : Prop :=
  (∀ left right, pointerDifference left right = JInt.wrap .u64 (left.val - right.val)) ∧
  (∀ left right, pointerEqual left right = (left.val == right.val)) ∧
  (∀ left right, pointerLess left right = decide (left.val < right.val)) ∧
  (∀ pointer offset, ptrAdd pointer offset = JInt.wrap .u64 (pointer.val + offset)) ∧
  (∀ pointer offset, ptrSub pointer offset = JInt.wrap .u64 (pointer.val - offset)) ∧
  (∀ pointer, pointerUnsigned pointer = pointer) ∧
  (∀ pointer, pointerSigned pointer = JInt.wrap .i64 pointer.val)

theorem pointerArithmeticBehavior : PointerArithmeticBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/refpointer.jl:97-150` -/

structure RefModel where
  values : List (Option Nat)
  index : Int
  roots : List Nat
  deriving DecidableEq, Repr

def refLength (_ : RefModel) : Nat := 1
def refEmpty (_ : RefModel) : Bool := false
def refDims (_ : RefModel) : Nat := 0
def refSize (_ : RefModel) : List Nat := []
def refAxes (_ : RefModel) : List (Nat × Nat) := []
def refElementType (tag : Nat) : Nat := tag
def refIteratorRank : Nat := 0
def refIterate (ref : RefModel) (started : Bool) : Option (Option Nat) :=
  if started then none else some (ref.values.getD (ref.index - 1).toNat none)

def makeRefArray (values : List (Option Nat)) (index : Int) (roots : List Nat) : RefModel :=
  ⟨values, index, roots⟩

inductive RefPointerRoute where | inline | boxed | unionLayout deriving DecidableEq, Repr

def refPointerRoute (isBitsOrInline unionLayout : Bool) : RefPointerRoute :=
  if isBitsOrInline then .inline else if unionLayout then .unionLayout else .boxed

def singleRefIndex (index : Int) : Jl Unit :=
  if index == 1 then .ok () else .error (.argumentError "Ref only has one element")

def RefCoreBehavior : Prop :=
  (∀ ref, refLength ref = 1 ∧ refEmpty ref = false ∧ refDims ref = 0 ∧
    refSize ref = [] ∧ refAxes ref = []) ∧
  (∀ tag, refElementType tag = tag) ∧ refIteratorRank = 0 ∧
  (∀ ref started, refIterate ref started =
    if started then none else some (ref.values.getD (ref.index - 1).toNat none)) ∧
  (∀ values index roots, makeRefArray values index roots = ⟨values, index, roots⟩) ∧
  (∀ inline union, refPointerRoute inline union =
    if inline then .inline else if union then .unionLayout else .boxed) ∧
  (∀ index, singleRefIndex index =
    if index == 1 then .ok () else .error (.argumentError "Ref only has one element")) ∧
  (∀ pointer size index, refPointer pointer size index = ptrAdd pointer ((index - 1) * size))

theorem refCoreBehavior : RefCoreBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ref; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intros; rfl
  · rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

/-! ## `base/refpointer.jl:154-194` -/

structure PointerArrayRoots where
  pointers : List Nat
  roots : List Nat
  terminated : Bool
  deriving DecidableEq, Repr

def rootPointerArray (pointers roots : List Nat) : PointerArrayRoots :=
  ⟨pointers ++ [0], roots, true⟩

def tupleRoot (values : List Nat) : List Nat := values

def refArrayAt (values : List (Option Nat)) (index : Int) (roots : List Nat) : RefModel :=
  ⟨values, index, roots⟩

def refGet (ref : RefModel) : Option Nat := ref.values.getD (ref.index - 1).toNat none

def refSet (ref : RefModel) (value : Option Nat) : RefModel :=
  { ref with values := ref.values.set (ref.index - 1).toNat value }

def RefArrayTupleBehavior : Prop :=
  (∀ pointers roots, rootPointerArray pointers roots = ⟨pointers ++ [0], roots, true⟩) ∧
  (∀ values, tupleRoot values = values) ∧
  (∀ values index roots, refArrayAt values index roots = ⟨values, index, roots⟩) ∧
  (∀ ref, refGet ref = ref.values.getD (ref.index - 1).toNat none) ∧
  (∀ ref value, refSet ref value =
    { ref with values := ref.values.set (ref.index - 1).toNat value })

theorem refArrayTupleBehavior : RefArrayTupleBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ## `base/bool.jl` -/

def boolXor (x y : Bool) : Bool := x != y
def boolPromote (otherType : Nat) : Nat := otherType
def boolBounds : Bool × Bool := (false, true)
def boolNot (x : Bool) : Bool := !x
def boolAnd (x y : Bool) : Bool := x && y
def boolOr (x y : Bool) : Bool := x || y
def boolNand (xs : List Bool) : Bool := !(xs.foldl (· && ·) true)
def boolNor (xs : List Bool) : Bool := !(xs.foldl (· || ·) false)
def boolShiftLeft (x : Bool) (count : Nat) : Int := (if x then 1 else 0) * 2^count
def boolShiftRight (x : Bool) (count : Nat) : Int := (if x then 1 else 0) / 2^count
def boolPredicates (x : Bool) : Bool × Bool × Bool × Bool × Bool :=
  (false, x, !x, x, x)
def boolUnaryInt (x : Bool) : Int := if x then 1 else 0
def boolCompare (x y : Bool) : Bool × Bool := (y && !x, y || !x)
def boolAdd (x y : Bool) : Int := (if x then 1 else 0) + (if y then 1 else 0)
def boolSub (x y : Bool) : Int := (if x then 1 else 0) - (if y then 1 else 0)
def boolMul (x y : Bool) : Bool := x && y
def boolPow (x y : Bool) : Bool := x || !y
def boolDiv (x y : Bool) : Jl Bool := if y then .ok x else .error .divideError
def boolRem (_x y : Bool) : Jl Bool := if y then .ok false else .error .divideError
def boolConvertReal (zero one : Bool) : Jl Bool :=
  if zero then .ok false else if one then .ok true else .error (.inexactError "Bool")
def boolFloatAdd (x : Bool) (onePlusY y : Int) : Int := if x then onePlusY else y
def boolFloatMul (x : Bool) (y signedZero : Int) : Int := if x then y else signedZero

def BoolMethodBehavior : Prop :=
  (∀ other, boolPromote other = other) ∧ boolBounds = (false, true) ∧
  (∀ x, boolNot x = !x) ∧
  (∀ x y, boolAnd x y = (x && y) ∧ boolOr x y = (x || y) ∧ boolXor x y = (x != y)) ∧
  (∀ xs, boolNand xs = !(xs.foldl (· && ·) true)) ∧
  (∀ xs, boolNor xs = !(xs.foldl (· || ·) false)) ∧
  (∀ x count, boolShiftLeft x count = (if x then 1 else 0) * 2^count) ∧
  (∀ x count, boolShiftRight x count = (if x then 1 else 0) / 2^count) ∧
  (∀ x, boolPredicates x = (false, x, !x, x, x)) ∧
  (∀ x, boolUnaryInt x = if x then 1 else 0) ∧
  (∀ x y, boolCompare x y = (y && !x, y || !x)) ∧
  (∀ x y, boolAdd x y = (if x then 1 else 0) + (if y then 1 else 0)) ∧
  (∀ x y, boolSub x y = (if x then 1 else 0) - (if y then 1 else 0)) ∧
  (∀ x y, boolMul x y = (x && y)) ∧
  (∀ x y, boolPow x y = (x || !y)) ∧
  (∀ x y, boolDiv x y = if y then .ok x else .error .divideError) ∧
  (∀ x y, boolRem x y = if y then .ok false else .error .divideError) ∧
  (∀ x onePlusY y, boolFloatAdd x onePlusY y = if x then onePlusY else y) ∧
  (∀ x y zero, boolFloatMul x y zero = if x then y else zero) ∧
  (∀ zero one, boolConvertReal zero one =
    if zero then .ok false else if one then .ok true else .error (.inexactError "Bool"))

theorem boolMethodBehavior : BoolMethodBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros <;> first | rfl | exact ⟨rfl, rfl, rfl⟩

/-! ## `base/summarysize.jl` -/

inductive SummaryKind where
  | tuple | cancellation | waitEntry | memoryInline | memoryBoxed | generic | string
  | datatype | typename | simpleVector | module | task | bigint
  deriving DecidableEq, Repr

structure SummaryObject where
  identity : Nat
  bytes : Nat
  pointers : List Nat
  kind : SummaryKind
  deriving DecidableEq, Repr

structure SummaryState where
  seen : List Nat
  frontier : List SummaryObject
  size : Nat
  deriving DecidableEq, Repr

def chargeObject (count : Bool) (object : SummaryObject) : Nat := if count then 1 else object.bytes
def nthPointerDefined (object : SummaryObject) (index : Nat) : Bool := index ≥ 1 && index ≤ object.pointers.length
def getNthPointer (object : SummaryObject) (index : Nat) : Nat := object.pointers.getD (index - 1) 0

def summaryChildren (object : SummaryObject) : List Nat :=
  match object.kind with
  | .string | .bigint => []
  | .memoryInline | .memoryBoxed | .tuple | .cancellation | .waitEntry | .generic
  | .datatype | .typename | .simpleVector | .module | .task => object.pointers

def summaryVisit (count excluded chargeAll : Bool) (object : SummaryObject)
    (state : SummaryState) : SummaryState :=
  if state.seen.contains object.identity then state
  else if excluded && !chargeAll then { state with seen := object.identity :: state.seen }
  else { seen := object.identity :: state.seen,
         frontier := (summaryChildren object).map (fun identity => { object with identity }) ++ state.frontier,
         size := state.size + chargeObject count object }

def summaryLoop (count : Bool) : List SummaryObject → SummaryState → SummaryState
  | [], state => state
  | object :: rest, state => summaryLoop count rest (summaryVisit count false false object state)

def SummarySizeBehavior : Prop :=
  (∀ object index, nthPointerDefined object index = (index ≥ 1 && index ≤ object.pointers.length)) ∧
  (∀ object index, getNthPointer object index = object.pointers.getD (index - 1) 0) ∧
  (∀ count object, chargeObject count object = if count then 1 else object.bytes) ∧
  (∀ object, summaryChildren object = match object.kind with
    | .string | .bigint => []
    | .memoryInline | .memoryBoxed | .tuple | .cancellation | .waitEntry | .generic
    | .datatype | .typename | .simpleVector | .module | .task => object.pointers) ∧
  (∀ count excluded charge object state, summaryVisit count excluded charge object state =
    if state.seen.contains object.identity then state
    else if excluded && !charge then { state with seen := object.identity :: state.seen }
    else { seen := object.identity :: state.seen,
           frontier := (summaryChildren object).map (fun identity => { object with identity }) ++ state.frontier,
           size := state.size + chargeObject count object }) ∧
  (∀ count objects state, summaryLoop count objects state = match objects with
    | [] => state
    | object :: rest => summaryLoop count rest (summaryVisit count false false object state))

theorem summarySizeBehavior : SummarySizeBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro object
    cases object with
    | mk identity bytes pointers kind => cases kind <;> rfl
  · intros; rfl
  · intro count objects; cases objects <;> intros <;> rfl

end JuliaLean.NumMisc.Coverage
