import JuliaLean.Dates.Model
import JuliaLean.ParsePrint.IntPrint

namespace JuliaLean.Dates
open JuliaLean
abbrev Bytes := List Nat

/-- stdlib/Dates/src/io.jl:193-195 delegates numeric formatting to the integer
printer at base/intfuncs.jl:1101-1119. The existing byte-buffer model is reused. -/
def decimal (x : I) (width : Nat) : Jl Bytes :=
  JuliaLean.ParsePrint.IntPrint.string x (i 10) width

/-- stdlib/Dates/src/io.jl:215-229: lowercase y retains the final width bytes,
including dropping a sign; uppercase Y uses the minimum-width printer. -/
def yearText (y : I) (width : Nat) (capital : Bool) : Jl Bytes := do
  let s ← decimal y width
  pure (if capital ∨ s.length = width then s else s.drop (s.length-width))

/-- ASCII locale names used by the English/default and custom-locale corpus.
stdlib/Dates/src/query.jl:16-27, 55-79. Case lookup tries exact then lowercase. -/
structure Locale where
  months : List Bytes
  abbr : List Bytes
  deriving DecidableEq

def bytes (s : String) : Bytes := s.toList.map Char.toNat
def english : Locale := ⟨
  ["January","February","March","April","May","June","July","August","September","October","November","December"].map bytes,
  ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"].map bytes⟩
def lowerAscii (s : Bytes) : Bytes := s.map (fun c => if 65 ≤ c ∧ c ≤ 90 then c+32 else c)
def isDigit (c : Nat) : Bool := 48 ≤ c ∧ c ≤ 57

def monthNameValue (locale : Locale) (full : Bool) (s : Bytes) : Option I :=
  let names := if full then locale.months else locale.abbr
  let k := names.findIdx? (fun n => n = s || lowerAscii n = lowerAscii s)
  k.map (fun k => i (k+1))

/-- DatePart.width and DatePart.fixed from stdlib/Dates/src/io.jl:92-98.
fixed controls parsing of adjacent fields, independently of y versus Y printing. -/
inductive Token where
  | year (width : Nat) (fixed : Bool) (capital : Bool)
  | month (width : Nat) (fixed : Bool)
  | day (width : Nat) (fixed : Bool)
  | monthName (full : Bool) (width : Nat) (fixed : Bool)
  | delim (text : Bytes)
  deriving DecidableEq

/-- stdlib/Dates/src/io.jl:193-201, 215-229, 292-294. -/
def formatToken (c : Civil) (loc : Locale) : Token → Jl Bytes
  | .year n _ cap => yearText c.y n cap
  | .month n _ => decimal c.m n
  | .day n _ => decimal c.d n
  | .monthName full _ _ =>
    let ns := if full then loc.months else loc.abbr
    if c.m.val < 1 ∨ c.m.val > ns.length then .error .boundsError
    else .ok ns[(c.m.val-1).toNat]!
  | .delim s => .ok s

def formatParts (c : Civil) (loc : Locale) : List Token → Jl Bytes
  | [] => .ok []
  | t::ts => do pure ((← formatToken c loc t) ++ (← formatParts c loc ts))

def formatDate (d : I) (tokens : List Token) (loc : Locale := english) : Jl Bytes :=
  formatParts (yearmonthday d) loc tokens

/-- stdlib/Dates/src/parse.jl:195-216: decimal accumulation rejects Int64
magnitude overflow before multiplying. It returns the untouched suffix. -/
def scanDigits : Bytes → I → Nat → Option (I × Nat × Bytes)
  | [], acc, count => some (acc,count,[])
  | c::cs, acc, count =>
    if !isDigit c then some (acc,count,c::cs)
    else if acc.val > (9223372036854775807 - ((c : Int)-48)).tdiv 10 then none
    else scanDigits cs (acc*i 10 + i ((c : Int)-48)) (count+1)

def parseNumber (s : Bytes) (width : Nat) (fixed : Bool) : Option (I × Bytes) := do
  let part := if fixed then s.take width else s
  let (n,count,rest) ← scanDigits part (i 0) 0
  if count < (if fixed then width else 1) then none
  else some (n,if fixed then rest ++ s.drop width else rest)

/-- stdlib/Dates/src/io.jl:114-129 and parse.jl:181-193: sign does not count
against the digit width. -/
def parseYear (s : Bytes) (width : Nat) (fixed : Bool) : Option (I × Bytes) := do
  let (negative,s) := match s with
    | 45::ss => (true,ss)
    | 43::ss => (false,ss)
    | ss => (false,ss)
  let (n,rest) ← parseNumber s width fixed
  pure (if negative then -n else n,rest)

/-- stdlib/Dates/src/parse.jl:219-233, restricted to ASCII letter locale names. -/
def parseMonthName (s : Bytes) (loc : Locale) (full : Bool) (width : Nat) (fixed : Bool) : Option (I × Bytes) := do
  let part := if fixed then s.take width else s
  let word := part.takeWhile (fun c => (65 ≤ c ∧ c ≤ 90) || (97 ≤ c ∧ c ≤ 122))
  if word = [] then none
  else
    let n ← monthNameValue loc full word
    pure (n,s.drop word.length)

/-- stdlib/Dates/src/parse.jl:38-109: defaults survive missing suffix fields;
an unused input suffix fails. Day-of-week annotations are outside this slice. -/
def parseParts (loc : Locale) : List Token → Bytes → Civil → Option Civil
  | [], s, c => if s = [] then some c else none
  | _::_, [], c => some c
  | t::ts, s, c => do
    match t with
    | .year n fixed _ =>
      let (v,s) ← parseYear s n fixed
      parseParts loc ts s { c with y := v }
    | .month n fixed =>
      let (v,s) ← parseNumber s n fixed
      parseParts loc ts s { c with m := v }
    | .day n fixed =>
      let (v,s) ← parseNumber s n fixed
      parseParts loc ts s { c with d := v }
    | .monthName full width fixed =>
      let (v,s) ← parseMonthName s loc full width fixed
      parseParts loc ts s { c with m := v }
    | .delim text =>
      if s.take text.length = text then parseParts loc ts (s.drop text.length) c else none

def parseDate (s : Bytes) (tokens : List Token) (loc : Locale := english) : Jl I :=
  match parseParts loc tokens s ⟨i 1,i 1,i 1⟩ with
  | none => .error (.argumentError "parse")
  | some c => date c

/-- stdlib/Dates/src/io.jl:561. -/
def isoFormat : List Token := [.year 4 false false,.delim [45],.month 2 false,.delim [45],.day 2 false]
def minimumFormat : List Token := [.year 4 false true,.delim [45],.month 2 false,.delim [45],.day 2 false]
def fixedFormat : List Token := [.year 4 true false,.month 2 true,.day 2 false]
def namedFormat : List Token := [.year 4 false true,.delim [45],.monthName true 1 false,.delim [45],.day 2 false]

/-- lpad(x,width,\"0\") pads the whole signed string, unlike decimal's digit
padding. This distinction matters if overflowing accessors produce negative fields. -/
def lpadNumber (n : I) (width : Nat) : Jl Bytes := do
  let s ← decimal n 1
  pure (List.replicate (width-s.length) 48 ++ s)

/-- stdlib/Dates/src/io.jl:836-844. The negative %05i path pads four digits
plus the sign. Month/day use lpad on the complete signed string. -/
def stringDate (d : I) : Jl Bytes := do
  let c := yearmonthday d
  let yy ← yearText c.y 4 true
  let mm ← lpadNumber c.m 2
  let dd ← lpadNumber c.d 2
  pure (yy ++ [45] ++ mm ++ [45] ++ dd)

end JuliaLean.Dates
