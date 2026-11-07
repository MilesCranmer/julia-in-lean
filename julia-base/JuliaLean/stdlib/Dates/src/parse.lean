import JuliaLean.stdlib.Dates.src.io

namespace JuliaLean.Dates
open JuliaLean

def isDigit (c : Nat) : Bool := 48 ≤ c ∧ c ≤ 57

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

end JuliaLean.Dates
