import JuliaLean.stdlib.Dates.src.types
import JuliaLean.stdlib.Dates.src.accessors
import JuliaLean.stdlib.Dates.src.query
import JuliaLean.base.intfuncs

namespace JuliaLean.Dates
open JuliaLean

/-- stdlib/Dates/src/io.jl:193-195 delegates numeric formatting to the integer
printer at base/intfuncs.jl:1101-1119. The existing byte-buffer model is reused. -/
def decimal (x : I) (width : Nat) : Jl Bytes :=
  JuliaLean.ParsePrint.IntPrint.string x (i 10) width

/-- stdlib/Dates/src/io.jl:215-229: lowercase y retains the final width bytes,
including dropping a sign; uppercase Y uses the minimum-width printer. -/
def yearText (y : I) (width : Nat) (capital : Bool) : Jl Bytes := do
  let s ← decimal y width
  pure (if capital ∨ s.length = width then s else s.drop (s.length-width))

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
