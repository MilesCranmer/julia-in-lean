import JuliaLean.RegexUnicode.SubstModel

/-!
# Regex pattern builders and a PCRE2 pattern lexer

* `^(r::Regex, i::Integer)`, `base/regex.jl:929`, and `*(r1, rs...)` with `wrap_string`,
  `base/regex.jl:856-882`, as string builders over `Regex` values (master `bbfa0ce4150`).
* A lexer for the part of PCRE2 pattern syntax these builders rely on (`pcre2pattern(3)`):
  - `\Q...\E` quoting ("Quoting"): inside, only `\E` is special; an isolated `\E` is
    ignored.
  - `PCRE2_EXTENDED` (`x`): white space is ignored and `#` starts a comment that runs to
    the next newline (Julia builds PCRE2 with the default newline, LF); neither applies
    inside `\Q...\E`.
  - `(?:`, `(?imsx-imsx:`, `(?imsx-imsx)` (option changes last to the end of the
    enclosing group), capturing, named and lookaround groups; parentheses must balance
    ("missing closing parenthesis", "unmatched closing parenthesis").
  - `{` starts a repetition quantifier `{n}`, `{n,}`, `{n,m}` only when followed by that
    syntax with decimal digits ("Repetition"); otherwise it is a literal `{`. Counts
    above 65535 are a compile error.
  Constructs outside this fragment (character classes, `\x`-style escapes, verbs,
  quantifier forms that differ between PCRE2 versions, a quantifier after an item that
  cannot be repeated) give `LexErr.unsupported`, which is never treated as a PCRE2
  compile error.
* The PCRE2 name table behind `keys(::RegexMatch)` and `haskey(::RegexMatch, name)`,
  `base/regex.jl:238-286`, `PCRE.capture_names` (`base/pcre.jl:265-282`).
-/

namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

/-! ## Lexer -/

/-- A pattern token. -/
inductive Tok where
  /-- A literal character. -/
  | lit (c : Char)
  /-- A backslash escape such as `\d` or `\.`. -/
  | esc (c : Char)
  /-- `.`, `^`, `$`, `|`, or a lazy/possessive suffix `?`/`+` after a quantifier. -/
  | sym (c : Char)
  /-- `(`: capturing, named or lookaround group. -/
  | openG
  /-- `(?:` or `(?imsx-imsx:`. -/
  | openNC
  | close
  /-- A repetition quantifier `{lo,hi}` (`*`, `+`, `?` included). -/
  | quant (lo : Nat) (hi : Option Nat)
  deriving DecidableEq, Repr

/-- Pattern compile errors of the fragment. -/
inductive LexErr where
  | missingClose
  | unmatchedClose
  | trailingBackslash
  | quantTooBig
  | quantOrder
  /-- Outside the modelled fragment. -/
  | unsupported
  deriving DecidableEq, Repr

def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- White space ignored under `PCRE2_EXTENDED` in UTF mode (Pattern_White_Space). -/
def isXSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\x0b' || c = '\x0c' || c = '\r' ||
  c = '\u0085' || c = '\u200e' || c = '\u200f' || c = '\u2028' || c = '\u2029'

/-- Escapes whose argument syntax is not modelled (`\x{..}`, `\p{..}`, `\g{..}`,
back references and octal digits, ...). -/
def unsupportedEsc (c : Char) : Bool := isDigitC c || "xoNpPgkcuU".toList.contains c

/-- Escapes that are assertions (cannot be repeated). -/
def assertionEsc (c : Char) : Bool := "bBAzZGK".toList.contains c

/-- The rest of an `x`-mode comment: everything after the next newline. -/
def skipComment (t : List Char) : List Char := (t.dropWhile (· ≠ '\n')).drop 1

def digitsNat (ds : List Char) : Nat := ds.foldl (fun acc d => 10 * acc + (d.toNat - 48)) 0

/-- Result of reading a `{`. -/
inductive QRes where
  | quant (lo : Nat) (hi : Option Nat) (rest : List Char)
  | literal
  | unsupported

/-- Quantifier syntax after `{`. Text up to the next `}` made only of digits, commas and
spaces that is not `n`, `n,` or `n,m` is a quantifier in some PCRE2 versions only
(`{,m}`, spaces), so it is `unsupported`; anything else makes `{` literal. -/
def parseQuant (t : List Char) : QRes :=
  let d1 := t.takeWhile isDigitC
  let r1 := t.dropWhile isDigitC
  let fallback : QRes :=
    let inner := t.takeWhile (· ≠ '}')
    if (t.dropWhile (· ≠ '}')).isEmpty then .literal
    else if inner.all (fun c => isDigitC c || c = ',' || c = ' ') then .unsupported
    else .literal
  if d1.isEmpty then fallback
  else
    match r1 with
    | '}' :: r => .quant (digitsNat d1) (some (digitsNat d1)) r
    | ',' :: '}' :: r => .quant (digitsNat d1) none r
    | ',' :: r2 =>
      let d2 := r2.takeWhile isDigitC
      match r2.dropWhile isDigitC with
      | '}' :: r => if d2.isEmpty then fallback else .quant (digitsNat d1) (some (digitsNat d2)) r
      | _ => fallback
    | _ => fallback

/-- Whether the last token can take a quantifier. -/
def repeatable : List Tok → Bool
  | .lit _ :: _ | .close :: _ | .sym '.' :: _ => true
  | .esc c :: _ => !assertionEsc c
  | _ => false

def afterQuant : List Tok → Bool
  | .quant _ _ :: _ => true
  | _ => false

/-- Option letters `[imsx]*(-[imsx]*)?` after `(?`: the new `x` setting and the rest. -/
def optLetters (ext : Bool) : Bool → List Char → Option (Bool × List Char)
  | _, [] => none
  | neg, c :: t =>
    if c = 'x' then optLetters (!neg) neg t
    else if c = 'i' ∨ c = 'm' ∨ c = 's' then optLetters ext neg t
    else if c = '-' ∧ !neg then optLetters ext true t
    else if c = ':' ∨ c = ')' then some (ext, c :: t)
    else none

def isNameChar (c : Char) : Bool := c.isAlphanum || c = '_'

/-- What follows `(`: the group token (`none` for an option setting `(?x)`), the `x`
setting inside, and the rest. -/
def openGroup (ext : Bool) (t : List Char) : Except LexErr (Option Tok × Bool × List Char) :=
  match t with
  | '?' :: ':' :: r => .ok (some .openNC, ext, r)
  | '?' :: '=' :: r | '?' :: '!' :: r | '?' :: '<' :: '=' :: r | '?' :: '<' :: '!' :: r =>
    .ok (some .openG, ext, r)
  | '?' :: '<' :: r | '?' :: 'P' :: '<' :: r =>
    let name := r.takeWhile isNameChar
    match r.dropWhile isNameChar with
    | '>' :: r' => if name.isEmpty then .error .unsupported else .ok (some .openG, ext, r')
    | _ => .error .unsupported
  | '?' :: r =>
    match optLetters ext false r with
    | some (ext', ':' :: r') => .ok (some .openNC, ext', r')
    | some (ext', ')' :: r') => .ok (none, ext', r')
    | _ => .error .unsupported
  | '*' :: _ => .error .unsupported
  | r => .ok (some .openG, ext, r)

/-- A quantifier token after checking PCRE2's limits. -/
def quantTok (lo : Nat) (hi : Option Nat) : Except LexErr Tok :=
  if 65535 < lo then .error .quantTooBig
  else match hi with
    | some h => if 65535 < h then .error .quantTooBig else if h < lo then .error .quantOrder
      else .ok (.quant lo hi)
    | none => .ok (.quant lo hi)

/-- The lexer: remaining text, inside `\Q...\E`, `x` setting, the `x` settings to restore
at each enclosing `)`, tokens so far (reversed). -/
def lexAux : Nat → List Char → Bool → Bool → List Bool → List Tok → Except LexErr (List Tok)
  | 0, _, _, _, _, _ => .error .unsupported
  | _ + 1, [], _, _, stk, acc => if stk.isEmpty then .ok acc.reverse else .error .missingClose
  | f + 1, c :: t, true, ext, stk, acc =>
    if c = '\\' ∧ t.head? = some 'E' then lexAux f t.tail false ext stk acc
    else lexAux f t true ext stk (.lit c :: acc)
  | f + 1, c :: t, false, ext, stk, acc =>
    if c = '\\' then
      match t with
      | [] => .error .trailingBackslash
      | d :: t' =>
        if d = 'Q' then lexAux f t' true ext stk acc
        else if d = 'E' then lexAux f t' false ext stk acc
        else if unsupportedEsc d then .error .unsupported
        else lexAux f t' false ext stk (.esc d :: acc)
    else if ext ∧ isXSpace c then lexAux f t false ext stk acc
    else if ext ∧ c = '#' then lexAux f (skipComment t) false ext stk acc
    else if c = '(' then
      match openGroup ext t with
      | .error e => .error e
      | .ok (some tok, ext', t') => lexAux f t' false ext' (ext :: stk) (tok :: acc)
      | .ok (none, ext', t') => lexAux f t' false ext' stk acc
    else if c = ')' then
      match stk with
      | [] => .error .unmatchedClose
      | e :: stk' => lexAux f t false e stk' (.close :: acc)
    else if c = '[' then .error .unsupported
    else if c = '{' then
      match parseQuant t with
      | .literal => lexAux f t false ext stk (.lit '{' :: acc)
      | .unsupported => .error .unsupported
      | .quant lo hi t' =>
        if repeatable acc then
          match quantTok lo hi with
          | .ok tok => lexAux f t' false ext stk (tok :: acc)
          | .error e => .error e
        else .error .unsupported
    else if c = '*' ∨ c = '+' ∨ c = '?' then
      if repeatable acc then
        lexAux f t false ext stk
          (.quant (if c = '+' then 1 else 0) (if c = '?' then some 1 else none) :: acc)
      else if afterQuant acc ∧ (c = '?' ∨ c = '+') then lexAux f t false ext stk (.sym c :: acc)
      else .error .unsupported
    else if c = '.' ∨ c = '^' ∨ c = '$' ∨ c = '|' then lexAux f t false ext stk (.sym c :: acc)
    else lexAux f t false ext stk (.lit c :: acc)

/-- Lex a pattern compiled with or without `PCRE2_EXTENDED`. -/
def lex (p : List Char) (ext : Bool) : Except LexErr (List Tok) :=
  lexAux (p.length + 1) p false ext [] []

/-! ## `Regex` values and the builders -/

/-- The `CASELESS`, `MULTILINE`, `DOTALL`, `EXTENDED` bits (`imsx`) of `compile_options`. -/
structure Flags where
  i : Bool
  m : Bool
  s : Bool
  x : Bool
  deriving DecidableEq, Repr

def Flags.and (a b : Flags) : Flags := ⟨a.i && b.i, a.m && b.m, a.s && b.s, a.x && b.x⟩
def Flags.andNot (a b : Flags) : Flags := ⟨a.i && !b.i, a.m && !b.m, a.s && !b.s, a.x && !b.x⟩
/-- `mask = CASELESS | MULTILINE | DOTALL | EXTENDED`, `base/regex.jl:857`. -/
def maskAll : Flags := ⟨true, true, true, true⟩
def noFlags : Flags := ⟨false, false, false, false⟩

/-- A `Regex`: `pattern`, `compile_options` (the `imsx` bits and the other bits),
`match_options`. -/
structure Regex where
  pattern : List Char
  flags : Flags
  other : Nat
  mopts : Nat
  deriving DecidableEq

/-- Exceptions of the builders. -/
inductive RErr where
  /-- `ArgumentError("cannot multiply regexes: incompatible options")`. -/
  | argumentError
  /-- `ErrorException("PCRE compilation error: ...")`. -/
  | compile (e : LexErr)
  /-- Outside the modelled fragment. -/
  | unsupported
  /-- No `Regex` argument: `*` is the `String` method instead. -/
  | noMethod
  deriving DecidableEq

/-- Whether a pattern compiles. -/
def compiles (r : Regex) : Bool :=
  match lex r.pattern r.flags.x with
  | .ok _ => true
  | .error _ => false

/-- `Regex(pattern, compile_options, match_options)`, `base/regex.jl:29-45`: it compiles the
pattern. -/
def mkRegex (pattern : List Char) (flags : Flags) (other mopts : Nat) : Except RErr Regex :=
  match lex pattern flags.x with
  | .ok _ => .ok ⟨pattern, flags, other, mopts⟩
  | .error .unsupported => .error .unsupported
  | .error e => .error (.compile e)

/-- `string(i)` for an integer `i`. -/
def intDigits (n : Int) : List Char :=
  if n < 0 then '-' :: Nat.toDigits 10 n.natAbs else Nat.toDigits 10 n.toNat

/-- `^(r::Regex, i::Integer)`, `base/regex.jl:929`:
`Regex(string("(?:", r.pattern, "){$i}"), r.compile_options, r.match_options)`. -/
def pow (r : Regex) (n : Int) : Except RErr Regex :=
  mkRegex (['(', '?', ':'] ++ r.pattern ++ [')', '{'] ++ intDigits n ++ ['}']) r.flags r.other r.mopts

/-- `replace(s, raw"\E" => raw"\\E\QE")` (`base/regex.jl:881`): each `\E`, searched left
to right without overlap, becomes `\\E\QE`. -/
def replaceE : List Char → List Char
  | [] => []
  | [c] => [c]
  | c :: d :: t =>
    if c = '\\' ∧ d = 'E' then ['\\', '\\', 'E', '\\', 'Q', 'E'] ++ replaceE t else c :: replaceE (d :: t)

/-- `wrap_string(s::AbstractString, ::UInt32)`, `base/regex.jl:881`. -/
def wrapString (s : List Char) : List Char := ['\\', 'Q'] ++ replaceE s ++ ['\\', 'E']

/-- `regex_opts_str(opts)`, `base/regex.jl:884-907`: the letters `imsx` that are set. -/
def optsStr (f : Flags) : List Char :=
  (if f.i then ['i'] else []) ++ (if f.m then ['m'] else []) ++ (if f.s then ['s'] else []) ++
    (if f.x then ['x'] else [])

/-- An argument of `*`. -/
inductive Arg where
  | rx (r : Regex)
  | str (s : List Char)
  | chr (c : Char)

/-- `wrap_string`, `base/regex.jl:879-882`. -/
def wrapArg (unshared : Flags) : Arg → List Char
  | .rx r => ['(', '?'] ++ optsStr (r.flags.and unshared) ++ [':'] ++ r.pattern ++ [')']
  | .str s => wrapString s
  | .chr c => ['\\', 'Q', c, '\\', 'E']

/-- The option loop of `*`, `base/regex.jl:861-872`: `(match_opts, compile_opts)` of the
first `Regex`, and `shared`. -/
def mulOpts : List Arg → Option (Nat × Nat) → Flags → Except RErr (Option (Nat × Nat) × Flags)
  | [], o, sh => .ok (o, sh)
  | .rx r :: t, none, sh => mulOpts t (some (r.mopts, r.other)) (sh.and r.flags)
  | .rx r :: t, some (mo, co), sh =>
    if r.mopts = mo ∧ r.other = co then mulOpts t (some (mo, co)) (sh.and r.flags)
    else .error .argumentError
  | _ :: t, o, sh => mulOpts t o sh

/-- `*(r1::Union{Regex,AbstractString,AbstractChar}, rs...)`, `base/regex.jl:856-875`. -/
def mul (args : List Arg) : Except RErr Regex := do
  let (o, shared) ← mulOpts args none maskAll
  match o with
  | none => .error .noMethod
  | some (mo, co) =>
    let unshared := maskAll.andNot shared
    mkRegex (args.flatMap (wrapArg unshared)) shared co mo

/-! ## Capture names -/

/-- A key of `keys(m::RegexMatch)`. -/
inductive Key where
  | num (n : Nat)
  | name (s : List UInt8)
  deriving DecidableEq

/-- `PCRE.capture_names(re)`, `base/pcre.jl:265-282`: a `Dict` from group number to name
filled from the name table in order. -/
def captureName (tbl : NameTable) (idx : Nat) : Option (List UInt8) :=
  tbl.foldl (fun acc e => if e.1 = idx then some e.2 else acc) none

/-- `keys(m::RegexMatch)`, `base/regex.jl:260-266`, for a regex with `ncap` groups. -/
def keys (ncap : Nat) (tbl : NameTable) : List Key :=
  (List.range ncap).map fun j =>
    match captureName tbl (j + 1) with
    | some s => .name s
    | none => .num (j + 1)

/-- `haskey(m::RegexMatch, idx::Integer)` and `haskey(m::RegexMatch, name)`,
`base/regex.jl:293-297`. -/
def haskey (ncap : Nat) (tbl : NameTable) : Key → Except IOErr Bool
  | .num n => .ok (1 ≤ n && n ≤ ncap)
  | .name s => do
    let g ← substringNumberFromName tbl s
    pure (decide (0 < g.val))

end JuliaLean.RegexUnicode.Subst
