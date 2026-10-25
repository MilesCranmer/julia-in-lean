import JuliaLean.Toml.Parser

/-!
# Canonical rendering of a parse outcome

A printable, canonical form of what `tryparse` returns, used to compare the
model with Julia (a Julia script printed the same form from Julia's
result) and to state properties about parsed values:

* a string is its bytes in hex between quotes;
* an integer is `i64:`/`i128:`/`big:`/`u64:`/`u128:` and its decimal value;
* a `Float64` is `F±m:e` with value `±m * 2^e` and `m` odd (or `0`), `Finf±`, `Fnan`;
* dates and times are `D(y,m,d)`, `T(h,mi,s,ms)`, `DT(y,m,d,h,mi,s,ms)`;
* a table is `{k=v,...}` with keys sorted, an array is `[eltype|v,...]`;
* a `ParserError` is `PE:` and its type, a thrown exception `EX:` and its type.
-/

namespace JuliaLean.Toml

/-- Round the positive rational `num / den` to the nearest `Float64` (ties to
even), as `(m, e)` with value `m * 2^e`. Overflow and underflow are excluded by
`classifyDec`/`classifyBin` before a `Val` is built. -/
def roundF64 (num den : Nat) : Nat × Int :=
  -- the exponent of the leading bit, up to one
  let k : Int := (Nat.log2 num : Int) - (Nat.log2 den : Int)
  let e0 : Int := max (k - 53) (-1074)
  let scaled (e : Int) : Nat × Nat :=
    if e ≤ 0 then (num * 2 ^ (-e).toNat, den) else (num, den * 2 ^ e.toNat)
  -- make the integer part `q` have at most 53 bits
  let e1 := if (scaled e0).1 / (scaled e0).2 ≥ 2 ^ 53 then e0 + 1 else e0
  let e1 := if (scaled e1).1 / (scaled e1).2 ≥ 2 ^ 53 then e1 + 1 else e1
  let (n, d) := scaled e1
  let q := n / d
  let r := n % d
  let q := if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q
  if q == 2 ^ 53 then (2 ^ 52, e1 + 1) else (q, e1)

/-- Strip trailing zero bits: `m` odd or zero. -/
def normBin : Nat → Nat × Int → Nat × Int
  | 0, p => p
  | fuel + 1, (m, e) => if m != 0 && m % 2 == 0 then normBin fuel (m / 2, e + 1) else (m, e)

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '?'

def hexStr (s : Str) : List Char :=
  '"' :: (s.flatMap fun b => [hexDigit (b / 16), hexDigit (b % 16)]) ++ ['"']

def natChars (n : Nat) : List Char := Nat.toDigits 10 n

def intChars (i : Int) : List Char :=
  if i < 0 then '-' :: natChars i.natAbs else natChars i.natAbs

def renderFloat : FloatV → List Char
  | .inf neg => "Finf".toList ++ [if neg then '-' else '+']
  | .nan => "Fnan".toList
  | .finite neg num den =>
    let (m, e) := if num == 0 then (0, 0) else normBin 2200 (roundF64 num den)
    ['F', if neg then '-' else '+'] ++ natChars m ++ [':'] ++ intChars e

def kindChars : IntKind → List Char
  | .i64 => "i64".toList | .i128 => "i128".toList | .big => "big".toList
  | .u64 => "u64".toList | .u128 => "u128".toList

def elChars : ElTy → List Char
  | .any => "any".toList | .string => "string".toList | .bool => "bool".toList
  | .i64 => "i64".toList | .u64 => "u64".toList | .f64 => "f64".toList

def tuple (xs : List Int) : List Char :=
  '(' :: (List.intercalate [','] (xs.map intChars)) ++ [')']

/-- Lexicographic order on byte strings. -/
def strLe : Str → Str → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && strLe as bs)

def insertSorted (kv : Str × List Char) : List (Str × List Char) → List (Str × List Char)
  | [] => [kv]
  | x :: xs => if strLe kv.1 x.1 then kv :: x :: xs else x :: insertSorted kv xs

/-- Render a value of the final heap. -/
def renderVal (heap : List Obj) : Nat → Val → List Char
  | 0, _ => "?".toList
  | fuel + 1, v =>
    match v with
    | .str s => hexStr s
    | .int k i => kindChars k ++ [':'] ++ intChars i
    | .float f => renderFloat f
    | .bool b => if b then "true".toList else "false".toList
    | .date y m d => 'D' :: tuple [y, m, d]
    | .time h mi s ms => 'T' :: tuple [h, mi, s, ms]
    | .datetime y m d h mi s ms => 'D' :: 'T' :: tuple [y, m, d, h, mi, s, ms]
    | .ref k =>
      match heap.getD k (.table []) with
      | .table kvs =>
        let items := kvs.foldl (fun acc (key, x) =>
          insertSorted (key, hexStr key ++ ['='] ++ renderVal heap fuel x) acc) []
        '{' :: List.intercalate [','] (items.map (·.2)) ++ ['}']
      | .array el xs =>
        '[' :: elChars el ++ ['|'] ++ List.intercalate [','] (xs.map (renderVal heap fuel)) ++ [']']

def errName (e : ErrType) : List Char :=
  ((toString (repr e)).splitOn ".").getLastD "" |>.toList

/-- The canonical form of `tryparse` on `s`. -/
def outcome (s : Str) (dates : Bool := true) : List Char :=
  match tryparseState s dates with
  | .ok l => renderVal l.heap (l.heap.length + 1) (.ref 0)
  | .error (.parserError e) => "PE:".toList ++ errName e
  | .error .typeError => "EX:TypeError".toList
  | .error (.jl (.argumentError _)) => "EX:ArgumentError".toList
  | .error (.jl (.overflowError _)) => "EX:OverflowError".toList
  | .error (.jl _) => "EX:Other".toList
  | .error (.errorException _) => "EX:ErrorException".toList
  | .error .outOfFuel => "EX:OutOfFuel".toList

end JuliaLean.Toml
