import JuliaLean.base.strings.io


namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-- The hex digit loop of `unescape_julia_string`,
`JuliaSyntax/src/julia/literal_parsing.jl:258-264`: `while (k += 1) <= m && i+1 < endind`,
reading `txtbuf[i+1]`. Returns `(k, n, rest)`. -/
def jlHex (m : Nat) : Nat → Nat → Nat → List UInt8 → Nat × Nat × List UInt8
  | 0, k, n, a => (k, n, a)
  | f + 1, k, n, a =>
    if k + 1 ≤ m then
      match a with
      | [] => (k + 1, n, a)
      | nc :: a' =>
        if decide (0x30 ≤ nc) && decide (nc ≤ 0x39) then jlHex m f (k + 1) (n * 16 + (nc - 0x30).toNat) a'
        else if decide (0x61 ≤ nc) && decide (nc ≤ 0x66) then
          jlHex m f (k + 1) (n * 16 + (nc - 0x61 + 10).toNat) a'
        else if decide (0x41 ≤ nc) && decide (nc ≤ 0x46) then
          jlHex m f (k + 1) (n * 16 + (nc - 0x41 + 10).toNat) a'
        else (k + 1, n, a)
    else (k + 1, n, a)

/-- The octal digit loop, `literal_parsing.jl:280-285`. -/
def jlOct : Nat → Nat → Nat → List UInt8 → Nat × List UInt8
  | 0, _, n, a => (n, a)
  | f + 1, k, n, a =>
    if k + 1 ≤ 3 then
      match a with
      | [] => (n, a)
      | c :: a' =>
        if decide (0x30 ≤ c) && decide (c ≤ 0x37) then jlOct f (k + 1) (n * 8 + (c - 0x30).toNat) a'
        else (n, a)
    else (n, a)

/-- The C and literal escapes, `literal_parsing.jl:294-308`. -/
def jlSimple (c : UInt8) : Option UInt8 :=
  if c = 0x6e then some 0x0a
  else if c = 0x74 then some 0x09
  else if c = 0x72 then some 0x0d
  else if c = 0x65 then some 0x1b
  else if c = 0x62 then some 0x08
  else if c = 0x66 then some 0x0c
  else if c = 0x76 then some 0x0b
  else if c = 0x61 then some 0x07
  else if c = 0x5c || c = 0x27 || c = 0x22 || c = 0x24 || c = 0x60 then some c
  else none

/-- Mark the result of the rest of the loop as having seen an error. -/
def jlErr (r : List UInt8 × Bool) : List UInt8 × Bool := (r.1, true)

/-- Prepend output bytes to the result of the rest of the loop. -/
def jlOut (bs : List UInt8) (r : List UInt8 × Bool) : List UInt8 × Bool := (bs ++ r.1, r.2)

/-- The loop of `unescape_julia_string(io, txtbuf, firstind, endind, diagnostics)`,
`JuliaSyntax/src/julia/literal_parsing.jl:229-318`, over the bytes from `i` to
`endind - 1`; returns the bytes written and `had_error`. -/
def jlUnescLoop : Nat → List UInt8 → List UInt8 × Bool
  | 0, _ => ([], false)
  | _ + 1, [] => ([], false)
  | f + 1, c :: r =>
    if c ≠ 0x5c then
      if c = 0x0d then
        match r with
        | 0x0a :: r' => jlOut [0x0a] (jlUnescLoop f r')
        | _ => jlOut [0x0a] (jlUnescLoop f r)
      else jlOut [c] (jlUnescLoop f r)
    else
      match r with
      | [] => ([], true)
      | c :: r =>
        if c = 0x78 || c = 0x75 || c = 0x55 then
          let m := if c = 0x78 then 2 else if c = 0x75 then 4 else 8
          match jlHex m (m + 1) 0 0 r with
          | (k, n, r) =>
            if k = 1 || decide (n > 0x10ffff) then jlErr (jlUnescLoop f r)
            else if m = 2 then jlOut [n.toUInt8] (jlUnescLoop f r)
            else jlOut (writeChar (charOfCp n)) (jlUnescLoop f r)
        else if decide (0x30 ≤ c) && decide (c ≤ 0x37) then
          match jlOct 3 1 (c - 0x30).toNat r with
          | (n, r) =>
            if n > 255 then jlErr (jlUnescLoop f r)
            else jlOut [n.toUInt8] (jlUnescLoop f r)
        else
          match jlSimple c with
          | some u => jlOut [u] (jlUnescLoop f r)
          | none => jlErr (jlUnescLoop f r)

/-- The bytes JuliaSyntax decodes from the body of a non-raw string or char
literal, or `none` when `unescape_julia_string` reports `had_error`. -/
def juliaUnescape (body : List UInt8) : Option (List UInt8) :=
  match jlUnescLoop (body.length + 1) body with
  | (out, false) => some out
  | (_, true) => none

/-! ## `show(io, ::AbstractChar)` -/

end JuliaLean.Show
