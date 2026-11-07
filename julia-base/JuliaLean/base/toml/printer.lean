import JuliaLean.base.toml.parser
import JuliaLean.base.expr
import JuliaLean.base.syntax
import JuliaLean.Core
import JuliaLean.Runtime.Float
import JuliaLean.base.show

/-!
# Canonical rendering of a parse outcome

A printable, canonical form of what `tryparse` returns, used to compare the
model with Julia and to state properties about parsed values:

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



section

/-!
# `base/toml/printer.jl`: `TOML.print`

Model of the TOML printer at master `bbfa0ce4150`. Julia strings are their code
points (`List Nat`, which can hold invalid characters such as surrogates); the
output is the UTF-8 bytes written to the stream (`Toml.Str`), so it can be fed to
the parser model `JuliaLean.Toml`.

Values are the types `TOML.print` handles. Dictionaries carry an identity (`id`)
because `inline_tables` is an `IdSet`; their entries are listed in `keys(d)`
iteration order. `other tag` is a value of a type that is not a `BaseTOMLValue`;
`toToml` is the user's conversion function (`f`; `none` is `identity`) and `extValid`
the user's `is_valid_toml_value` methods. Floats are printed by `Base.print`
(Ryu, another area), passed in as `showFloat`.
-/

namespace JuliaLean.DocsSyntaxCov.TomlPrint

open JuliaLean JuliaLean.DocsSyntaxCov

abbrev CP := List Nat
abbrev Out := List Nat

/-- A value given to `TOML.print`. -/
inductive TV where
  | dict (id : Nat) (entries : List (CP × TV))
  | arr (elems : List TV)
  | bool (b : Bool)
  /-- A `Signed` integer. -/
  | sint (n : Int)
  /-- An `Unsigned` integer. -/
  | uint (n : Nat)
  /-- An `AbstractFloat`, after `Float64(value)`: NaN, ±Inf or a finite value `x`. -/
  | nan
  | inf (pos : Bool)
  | float (x : Nat)
  | str (s : CP)
  | date (y m d : Int)
  | time (h mi s ms : Int)
  | datetime (y m d h mi s ms : Int)
  | other (tag : String)
  deriving Inhabited

/-- Comment blocks keyed by item path (`Base.TOML.CommentBlock`, `Comments`). -/
structure CommentBlock where
  above : List CP
  inline : Option CP

structure Comments where
  items : List (List CP × CommentBlock)
  floating : List (List CP × List CP)

def lookup {α : Type} (d : List (List CP × α)) (k : List CP) : Option α :=
  (d.find? (·.1 == k)).map (·.2)

/-- The context every printing function shares. -/
structure Env where
  /-- The conversion function `f`; `none` is `identity`. -/
  toToml : Option (String → TV)
  /-- User methods of `is_valid_toml_value` for non-base types. -/
  extValid : String → Bool
  /-- `Base.print(io, x::Float64)` for a finite `x`. -/
  showFloat : Nat → Out
  /-- The `by` keyword argument: `sort!(...; by)` compares `by(key)`. -/
  byFn : CP → CP
  /-- Ids of the tables in `inline_tables`. -/
  inline : List Nat
  sorted : Bool
  comments : Option Comments

/-- UTF-8 bytes of one code point. -/
def enc (c : Nat) : Out := Toml.utf8 c

/-- `isvalid(c::Char)` for a code point. -/
def isvalidChar (c : Nat) : Bool := c < 0xD800 || (0xE000 ≤ c && c < 0x110000)

/-- `Base.iscntrl(c)`: general category Cc. -/
def iscntrl (c : Nat) : Bool := c ≤ 0x1f || (0x7f ≤ c && c ≤ 0x9f)

def hexDigit (n : Nat) : Nat := if n < 10 then 48 + n else 87 + n

/-- `string(n, base=16, pad=p)`: lowercase hexadecimal, left-padded with zeros. -/
def hexPad (n p : Nat) : Out :=
  let ds := (Nat.toDigits 16 n).map fun c => c.toNat
  List.replicate (p - ds.length) 48 ++ ds

/-- `string(n, pad=p)` for a decimal `n`. -/
def decPad (n : Int) (p : Nat) : Out :=
  let ds := (Nat.toDigits 10 n.natAbs).map fun c => c.toNat
  (if n < 0 then [45] else []) ++ List.replicate (p - ds.length) 48 ++ ds

/-- `show(io, n)` of a `Signed` integer. -/
def showInt (n : Int) : Out := decPad n 0

/-- One character of `print_toml_escaped`, `base/toml/printer.jl:8-31`. -/
def escapeChar (c : Nat) : DJ Out :=
  if !isvalidChar c then .error (.errorException "TOML print: invalid character")
  else if c == 8 then pure [92, 98]
  else if c == 9 then pure [92, 116]
  else if c == 10 then pure [92, 110]
  else if c == 12 then pure [92, 102]
  else if c == 13 then pure [92, 114]
  else if c == 34 then pure [92, 34]
  else if c == 92 then pure [92, 92]
  else if iscntrl c then pure ([92, 117] ++ hexPad c 4)
  else pure (enc c)

/-- `print_toml_escaped(io, s)`, `base/toml/printer.jl:7-33`. -/
def printTomlEscaped : CP → DJ Out
  | [] => pure []
  | c :: cs => do
    let a ← escapeChar c
    let b ← printTomlEscaped cs
    pure (a ++ b)

/-- `is_valid_toml_value(::Any)` / `is_valid_toml_value(::BaseTOMLValue)`,
`base/toml/printer.jl:38-39`, with user methods for non-base types. -/
def isValidTomlValue (extValid : String → Bool) : TV → Bool
  | .other tag => extValid tag
  | _ => true

/-- `_is_valid_toml_value(x) = x isa BaseTOMLValue || is_valid_toml_value(x)`,
`base/toml/printer.jl:42-43`. -/
def isValid (env : Env) (v : TV) : Bool :=
  (match v with | .other _ => false | _ => true) || isValidTomlValue env.extValid v

/-- `isvalid_barekey_char` of the parser, on a code point. -/
def bareChar (c : Nat) : Bool := Toml.isvalid_barekey_char (Toml.rawOf c)

/-- One key of `printkey`. -/
def printOneKey (k : CP) : DJ Out :=
  if k.length == 0 then pure [34, 34]
  else if k.any (fun c => !bareChar c) then do
    let e ← printTomlEscaped k
    pure ([34] ++ e ++ [34])
  else pure (k.flatMap enc)

/-- `printkey(io, keys)`, `base/toml/printer.jl:49-64`. -/
def printkey : List CP → DJ Out
  | [] => pure []
  | [k] => printOneKey k
  | k :: ks => do
    let a ← printOneKey k
    let b ← printkey ks
    pure (a ++ [46] ++ b)

/-- `to_toml_value(f, value)`, `base/toml/printer.jl:66-75`. -/
def toTomlValue (env : Env) (v : TV) : DJ TV :=
  match v with
  | .other tag =>
    match env.toToml with
    | none => .error (.errorException "is not a valid TOML type, pass a conversion function")
    | some f =>
      let tv := f tag
      if !isValid env tv then .error (.errorException "did not return a valid TOML type") else pure tv
  | _ =>
    match env.toToml with
    | none => .error (.errorException "is not a valid TOML type, pass a conversion function")
    | some _ => pure v

/-- Insertion of `x` into a list sorted by `lt` (stable). -/
def insertBy {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBy lt x ys

/-- `sort!(xs; lt)`: a stable sort. -/
def sortBy {α : Type} (lt : α → α → Bool) (xs : List α) : List α := xs.foldr (insertBy lt) []

/-- `isless` on strings: lexicographic on code points (byte order for UTF-8). -/
def strLt : CP → CP → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && strLt as bs)

/-- `sort!(vkeys)` (no `by`). -/
def sortKeys {α : Type} (kvs : List (CP × α)) : List (CP × α) := sortBy (fun a b => strLt a.1 b.1) kvs

/-- `sort!(collect(akeys); by)`. -/
def sortKeysBy {α : Type} (byFn : CP → CP) (kvs : List (CP × α)) : List (CP × α) :=
  sortBy (fun a b => strLt (byFn a.1) (byFn b.1)) kvs

/-! ## Values, `base/toml/printer.jl:81-173` -/

/-- `printvalue(f, io, value::Base.TOML.Time, sorted)`, lines 103-113. -/
def printTime (h mi s ms : Int) : Out :=
  decPad h 2 ++ [58] ++ decPad mi 2 ++ [58] ++ decPad s 2 ++ (if ms != 0 then [46] ++ decPad ms 3 else [])

/-- `printvalue(f, io, value::Base.TOML.Date, sorted)`, lines 115-121. -/
def printDate (y m d : Int) : Out := decPad y 4 ++ [45] ++ decPad m 2 ++ [45] ++ decPad d 2

/-- `printvalue(f, io, value::Integer, sorted)`, lines 127-133: signed values are shown in
decimal; unsigned ones in hexadecimal with `2 * ndigits(value, base=256)` digits. -/
def printInteger : TV → Out
  | .sint n => showInt n
  | .uint n => (bytes% "0x") ++ hexPad n (2 * (Nat.toDigits 256 n).length)
  | _ => []

/-- `printvalue(f, io, value::AbstractFloat, sorted)`, lines 135-146. -/
def printFloat (env : Env) : TV → Out
  | .nan => (bytes% "nan")
  | .inf pos => if pos then (bytes% "+inf") else (bytes% "-inf")
  | .float x => env.showFloat x
  | _ => []

/-- `printvalue(f, io, value::AbstractString, sorted)`, lines 148-153. -/
def printString (s : CP) : DJ Out := do
  let q := if s.contains 10 then (bytes% "\"\"\"") else (bytes% "\"")
  let e ← printTomlEscaped s
  pure (q ++ e ++ q)

mutual
/-- `printvalue(f, io, value, sorted)`, all methods, lines 81-157. -/
def printvalue (env : Env) : Nat → TV → DJ Out
  | 0, _ => .error (.errorException "out of fuel")
  | n + 1, v =>
    match v with
    | .other _ => do
      let tv ← toTomlValue env v
      printvalue env n tv
    | .arr xs => do
      let body ← printItems env n xs
      pure ([91] ++ body ++ [93])
    | .datetime y m d h mi s ms =>
      pure (printDate y m d ++ [84] ++ printTime h mi s ms ++ [90])
    | .time h mi s ms => pure (printTime h mi s ms)
    | .date y m d => pure (printDate y m d)
    | .bool b => pure (if b then (bytes% "true") else (bytes% "false"))
    | .sint _ | .uint _ => pure (printInteger v)
    | .nan | .inf _ | .float _ => pure (printFloat env v)
    | .str s => printString s
    | .dict _ kvs => printInlineTable env n kvs

/-- The elements of an array, separated by `", "` (lines 88-92). -/
def printItems (env : Env) : Nat → List TV → DJ Out
  | 0, _ => .error (.errorException "out of fuel")
  | _ + 1, [] => pure []
  | n + 1, [x] => printvalue env n x
  | n + 1, x :: xs => do
    let a ← printvalue env n x
    let b ← printItems env n xs
    pure (a ++ (bytes% ", ") ++ b)

/-- `print_inline_table(f, io, value, sorted)`, lines 159-173. -/
def printInlineTable (env : Env) : Nat → List (CP × TV) → DJ Out
  | 0, _ => .error (.errorException "out of fuel")
  | n + 1, kvs => do
    let vkeys := if env.sorted then sortKeys kvs else kvs
    let body ← printInlineEntries env n vkeys
    pure ([123] ++ body ++ [125])

def printInlineEntries (env : Env) : Nat → List (CP × TV) → DJ Out
  | 0, _ => .error (.errorException "out of fuel")
  | _ + 1, [] => pure []
  | n + 1, (k, v) :: rest => do
    let key ← printkey [k]
    let val ← printvalue env n v
    let tail ← printInlineEntries env n rest
    pure (key ++ (bytes% " = ") ++ val ++ (if rest.isEmpty then [] else (bytes% ", ")) ++ tail)
end

/-! ## Comments, lines 182-259 -/

/-- `print_comment_line(io, indentstr, text)`, lines 182-196. -/
def printCommentLine (indentstr : Out) (text : CP) : Out :=
  let lead := match text with
    | [] => []
    | c :: _ => if c == 32 || c == 9 then [] else [32]
  indentstr ++ [35] ++ lead ++
    text.flatMap (fun c =>
      if c == 10 then [10] ++ indentstr ++ [35, 32]
      else if c == 9 || !iscntrl c then enc c else []) ++ [10]

/-- `print_comments_above(io, comments, path, indentstr)`, lines 198-204. -/
def printCommentsAbove (c : Comments) (path : List CP) (indentstr : Out) : Out :=
  match lookup c.items path with
  | none => []
  | some b => b.above.flatMap (printCommentLine indentstr)

/-- `print_comment_inline(io, comments, path)`, lines 206-222. -/
def printCommentInline (c : Comments) (path : List CP) : Out :=
  match lookup c.items path with
  | none => []
  | some b =>
    match b.inline with
    | none => []
    | some text =>
      let lead := match text with
        | [] => []
        | c :: _ => if c == 32 || c == 9 then [] else [32]
      [32, 35] ++ lead ++
        text.flatMap (fun c => if c == 9 || (c != 10 && !iscntrl c) then enc c else [32])

/-- `has_comments(comments, path)`, lines 224-225. -/
def hasComments (c : Comments) (path : List CP) : Bool :=
  (lookup c.items path).isSome || (lookup c.floating path).isSome

/-- `print_hoisted_inline_comments(io, comments, a, path, indentstr, sorted)`, lines 228-250. -/
def printHoisted (c : Comments) (indentstr : Out) (sorted : Bool) :
    Nat → List (CP × TV) → List CP → Out
  | 0, _, _ => []
  | n + 1, kvs, path =>
    let fl := match lookup c.floating path with
      | none => []
      | some lines => lines.flatMap (printCommentLine indentstr)
    let vkeys := if sorted then sortKeys kvs else kvs
    fl ++ vkeys.flatMap (fun (k, v) =>
      let kpath := path ++ [k]
      let blk := match lookup c.items kpath with
        | none => []
        | some b => b.above.flatMap (printCommentLine indentstr) ++
            (match b.inline with | none => [] | some t => printCommentLine indentstr t)
      blk ++ (match v with
        | .dict _ kvs' => printHoisted c indentstr sorted n kvs' kpath
        | _ => []))

/-- `print_comments_floating(io, comments, path, indentstr)`, lines 252-259: the output and
whether any line was printed. -/
def printCommentsFloating (c : Comments) (path : List CP) (indentstr : Out) : Out × Bool :=
  match lookup c.floating path with
  | none => ([], false)
  | some lines => (lines.flatMap (printCommentLine indentstr), !lines.isEmpty)

/-! ## Tables, lines 265-379 -/

/-- `is_table(value)`, line 265. -/
def isTable : TV → Bool
  | .dict _ _ => true
  | _ => false

/-- `is_array_of_tables(value)`, lines 266-269. -/
def isArrayOfTables : TV → Bool
  | .arr xs => xs.length > 0 && xs.all isTable
  | _ => false

/-- `is_tabular(value)`, line 270. -/
def isTabular (v : TV) : Bool := isTable v || isArrayOfTables v

def dictId : TV → Option Nat
  | .dict id _ => some id
  | _ => none

/-- `value in inline_tables` for an `IdSet` of dictionaries. -/
def inInline (env : Env) (v : TV) : Bool :=
  match dictId v with
  | some id => env.inline.contains id
  | none => false

def spaces (n : Nat) : Out := List.replicate n 32

/-- The value after `_is_valid_toml_value(value) || (value = to_toml_value(f, value))`. -/
def checkedValue (env : Env) (v : TV) : DJ TV := if isValid env v then pure v else toTomlValue env v

/-- The first loop of `print_table`: non-tabular entries (lines 299-325). Returns the output
and the new `first_block`. -/
def printEntries (env : Env) (fuel : Nat) (ks : List CP) (indentstr : Out) :
    List (CP × TV) → Bool → DJ (Out × Bool)
  | [], fb => pure ([], fb)
  | (key, value) :: rest, fb => do
    let value ← checkedValue env value
    if isTabular value && !inInline env value then printEntries env fuel ks indentstr rest fb
    else
      let entryPath := ks ++ [key]
      let pre := match env.comments with
        | none => []
        | some c => printCommentsAbove c entryPath indentstr ++
            (match value with
              | .dict _ kvs => if inInline env value then printHoisted c indentstr env.sorted fuel kvs entryPath else []
              | _ => [])
      let k ← printkey [key]
      let v ← printvalue env fuel value
      let post := match env.comments with
        | none => []
        | some c => printCommentInline c entryPath
      let (o, fb') ← printEntries env fuel ks indentstr rest false
      pure (pre ++ indentstr ++ k ++ (bytes% " = ") ++ v ++ post ++ [10] ++ o, fb')

mutual
/-- `print_table(f, io, a, ks; indent, first_block, sorted, inline_tables, by, comments)`,
lines 272-379. `id` is the identity of `a`. -/
def printTable (env : Env) : Nat → Nat → List (CP × TV) → List CP → Nat → Bool → DJ Out
  | 0, _, _, _, _, _ => .error (.errorException "out of fuel")
  | n + 1, id, a, ks, indent, firstBlock => do
    if env.inline.contains id then
      return (← printInlineTable env n a)
    let entryIndent := spaces (4 * (indent - 1))
    let floatOut := match env.comments with
      | none => []
      | some c => let (o, b) := printCommentsFloating c ks entryIndent; o ++ (if b then [10] else [])
    let akeys := if env.sorted then sortKeysBy env.byFn a else a
    let (o1, fb) ← printEntries env n ks entryIndent akeys firstBlock
    let o2 ← printSubtables env n ks indent akeys fb
    pure (floatOut ++ o1 ++ o2)

/-- The second loop of `print_table` (lines 327-378). -/
def printSubtables (env : Env) : Nat → List CP → Nat → List (CP × TV) → Bool → DJ Out
  | 0, _, _, _, _ => .error (.errorException "out of fuel")
  | _ + 1, _, _, [], _ => pure []
  | n + 1, ks, indent, (key, value) :: rest, fb => do
    let value ← checkedValue env value
    match value with
    | .dict id kvs =>
      if !inInline env value then
        let ks' := ks ++ [key]
        let vals := kvs.map (·.2)
        let header0 := kvs.isEmpty || !vals.all isTabular || vals.any (inInline env)
        let header := if !header0 then
            (match env.comments with | none => header0 | some c => hasComments c ks')
          else header0
        let hdr ← if header then do
            let k ← printkey ks'
            pure ((if fb then [] else [10]) ++
              (match env.comments with | none => [] | some c => printCommentsAbove c ks' (spaces (4 * indent))) ++
              spaces (4 * indent) ++ [91] ++ k ++ [93] ++
              (match env.comments with | none => [] | some c => printCommentInline c ks') ++ [10])
          else pure []
        let fb := if header then false else fb
        let sub ← printTable env n id kvs ks' (indent + (if header then 1 else 0)) header
        let o ← printSubtables env n ks indent rest fb
        pure (hdr ++ sub ++ o)
      else printSubtables env n ks indent rest fb
    | .arr xs =>
      if isArrayOfTables value then
        let ks' := ks ++ [key]
        let lead := (if fb then [] else [10]) ++
          (match env.comments with | none => [] | some c => printCommentsAbove c ks' (spaces (4 * indent)))
        let body ← printArrayTables env n ks' indent xs
        let o ← printSubtables env n ks indent rest false
        pure (lead ++ body ++ o)
      else printSubtables env n ks indent rest fb
    | _ => printSubtables env n ks indent rest fb

/-- The `for v in value` loop printing an array of tables (lines 367-375). -/
def printArrayTables (env : Env) : Nat → List CP → Nat → List TV → DJ Out
  | 0, _, _, _ => .error (.errorException "out of fuel")
  | _ + 1, _, _, [] => pure []
  | n + 1, ks, indent, v :: vs => do
    let k ← printkey ks
    let hdr := spaces (4 * indent) ++ (bytes% "[[") ++ k ++ (bytes% "]]\n")
    match v with
    | .dict id kvs =>
      let body ← printTable env n id kvs ks (indent + 1) true
      let rest ← printArrayTables env n ks indent vs
      pure (hdr ++ body ++ rest)
    | _ => .error (.errorException "array should contain only tables")
end

/-- The fuel the printing functions need for a value: its size. -/
def TV.size : TV → Nat
  | .dict _ kvs => sizeKV kvs + 1
  | .arr xs => sizeL xs + 1
  | _ => 1
where
  sizeKV : List (CP × TV) → Nat
  | [] => 0
  | (_, v) :: r => v.size + sizeKV r + 1
  sizeL : List TV → Nat
  | [] => 0
  | v :: r => v.size + sizeL r + 1

/-! ## API, lines 386-393 -/

/-- `print(f, io, a; sorted, by, inline_tables, comments) = print_table(f, io, a; ...)`,
line 386-387 (with `ks = String[]`, `indent = 0`, `first_block = true`). The root table
has identity `id`. -/
def printToml (env : Env) (id : Nat) (a : List (CP × TV)) : DJ Out :=
  printTable env ((TV.dict id a).size * 4 + 8) id a [] 0 true

/-- `print(f, a; ...)`, lines 388-389: the same bytes, written to `stdout`. -/
def printTomlStdout (env : Env) (id : Nat) (a : List (CP × TV)) : DJ Out := printToml env id a

/-- `print(io, a; ...)`, lines 390-391: `f = identity`. -/
def printTomlIdentity (env : Env) (id : Nat) (a : List (CP × TV)) : DJ Out :=
  printToml { env with toToml := none } id a

/-- `print(a; ...)`, lines 392-393: `identity`, to `stdout`. -/
def printTomlIdentityStdout (env : Env) (id : Nat) (a : List (CP × TV)) : DJ Out :=
  printTomlIdentity env id a

end JuliaLean.DocsSyntaxCov.TomlPrint

end


/-!
# Model of `base/toml/printer.jl`

The printer's control flow is typed over Julia-dispatched value, array, dictionary, and string
operations. Its stream output uses `base/show.jl`'s `IOPrims`, lifted from the mutable `base/io.jl`
world. A `BaseTOMLValue` tag represents the members of Julia's union type; user conversion and
`is_valid_toml_value` extensions remain explicit operations.
-/

namespace JuliaLean.base.toml.printer

open JuliaLean
open JuliaLean.base.syntax
open JuliaLean.base.toml.parser

abbrev Bytes := List UInt8
abbrev JInt64 := JInt .i64
abbrev JChar := JuliaLean.base.char.JChar
abbrev Float64 := JuliaLean.Float.F64

def i64 (n : Int) : JInt64 := JInt.wrap .i64 n

def addI64 (x y : JInt64) : JInt64 := i64 (x.val + y.val)
def subI64 (x y : JInt64) : JInt64 := i64 (x.val - y.val)
def mulI64 (x y : JInt64) : JInt64 := i64 (x.val * y.val)

/--
Julia source: base/toml/printer.jl:35-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const BaseTOMLValue = Union{AbstractVector, AbstractDict, Bool, Integer, AbstractFloat, AbstractString,
                            Base.TOML.DateTime, Base.TOML.Time, Base.TOML.Date}
```
-/
inductive BaseTOMLValue where
  | abstractVector
  | abstractDict
  | bool
  | integer
  | abstractFloat
  | abstractString
  | dateTime
  | time
  | date
  deriving DecidableEq

inductive ValueClass where
  | base (kind : BaseTOMLValue)
  | other
  deriving DecidableEq

inductive PrinterError where
  | io (error : JuliaLean.base.io.Error)
  | show (error : JuliaLean.base.show.ShowError)
  | runtimeError (message : String)

abbrev M (World : Type) (A : Type) :=
  World → Option (Except (PrinterError × World) (A × World))

instance {World : Type} : Monad (M World) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world => do
    match ← action world with
    | .error error => pure (.error error)
    | .ok (value, world) => next value world


instance {World : Type} : Lean.Order.MonoBind (M World) where
  bind_mono_left h := by
    intro world
    exact Lean.Order.MonoBind.bind_mono_left (m := Option) (h world)
  bind_mono_right h := by
    intro world
    apply Lean.Order.MonoBind.bind_mono_right (m := Option)
    intro result
    rcases result with error | ⟨value, world⟩
    · exact Lean.Order.PartialOrder.rel_refl
    · exact h value world
instance {World : Type} : MonadExceptOf PrinterError (M World) where
  throw error := fun world => some (.error (error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (error, world)) => handler error world

instance {World : Type} : MonadExceptOf JuliaLean.base.show.ShowError (M World) where
  throw error := fun world => some (.error (.show error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (.show error, world)) => handler error world
    | some (.error (error, world)) => some (.error (error, world))

def liftIO {World A : Type} (action : JuliaLean.base.io.M World A) : M World A := fun world =>
  match action world with
  | none => none
  | some (.ok (value, world)) => some (.ok (value, world))
  | some (.error (error, world)) => some (.error (.io error, world))

/-- Julia's `BaseTOMLValue` union members, selected by trusted Julia dispatch. -/
structure PrinterOps
    (World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type) where
  io : JuliaLean.base.show.IOPrims (M World) Io Unit
  /-- `@invokelatest` uses the runtime's selected method. -/
  invokeLatest : {A : Type} → M World A → M World A
  classify : V → ValueClass
  typeName : V → String
  isValidExtension : V → M World Bool
  isIdentity : Conv → Bool
  convertValue : Conv → V → M World V
  asArray : V → Arr
  arrayLength : Arr → M World JInt64
  arrayValues : Arr → M World (List V)
  arrayHasDictElementType : Arr → Bool
  asDict : V → Dict
  dictKeys : Dict → M World (List Key)
  dictGet : Dict → Key → M World V
  dictValues : Dict → M World (List V)
  dictIsEmpty : Dict → M World Bool
  keyString : Key → M World Bytes
  sortKeys : List Key → M World (List Key)
  sortKeysBy : By → List Key → M World (List Key)
  identityConv : Conv
  identityBy : By
  emptyInlineTables : Inline
  inlineMember : Inline → V → Bool
  inlineDictMember : Inline → Dict → Bool
  stringValue : V → Text
  stringFromBytes : Bytes → Text
  stringBytes : Text → Bytes
  stringLength : Text → M World JInt64
  stringChars : Text → M World (List JChar)
  stringFirst : Text → M World JChar
  stringContains : Text → Bytes → M World Bool
  validChar : JChar → M World Bool
  controlChar : JChar → M World Bool
  charBytes : JChar → Bytes
  reprChar : JChar → String
  uint32Hex : JChar → JInt64 → M World Bytes
  asBool : V → Bool
  asInteger : V → Integer
  integerIsSigned : Integer → Bool
  integerNdigits : Integer → JInt64 → M World JInt64
  integerShow : Io → Integer → M World Unit
  integerHex : Integer → JInt64 → M World Bytes
  asFloat : V → Float
  float64 : Float → M World Float64
  floatIsNan : Float64 → Bool
  floatIsInf : Float64 → Bool
  floatGreaterZero : Float64 → Bool
  floatPrint : Io → Float64 → M World Unit
  intStringPad : JInt64 → JInt64 → M World Bytes
  asDateTime : V → DateTime
  asTime : V → Time
  asDate : V → Date
  repeatChar : JChar → JInt64 → M World Bytes
  stdout : Io

/-- Stream output through the `IOPrims` adapter from `base/show.jl`. -/
def writeBytes {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (bytes : Bytes) : M World Unit :=
  JuliaLean.base.show.write ops.io (.plain io) bytes

def writeLiteral {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (text : String) : M World Unit :=
  writeBytes ops io text.toUTF8.toList

def writeChar {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (c : JChar) : M World Unit :=
  writeBytes ops io (ops.charBytes c)

def runPrintActions {World : Type} (actions : List (M World Unit)) : M World Unit := do
  for action in actions do action

def printMany {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (actions : List (M World Unit)) : M World Unit := do
  JuliaLean.base.show.lockIO ops.io (.plain io)
  let result ← tryCatch (do
    runPrintActions actions
    pure (Except.ok ())) (fun error => pure (Except.error error))
  JuliaLean.base.show.unlockIO ops.io (.plain io)
  match result with
  | .ok () => pure ()
  | .error error => throw error

def printCharList {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (chars : List JChar) : M World Unit := do
  for c in chars do writeChar ops io c

def allM {World A : Type} (f : A → M World Bool) : List A → M World Bool
  | [] => pure true
  | x :: xs => do
      if ← f x then allM f xs else pure false

def anyM {World A : Type} (f : A → M World Bool) : List A → M World Bool
  | [] => pure false
  | x :: xs => do
      if ← f x then pure true else anyM f xs

-- UNTRANSLATED
-- Source: base/toml/printer.jl:1-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- import Base: @invokelatest
-- import ..isvalid_barekey_char # from Parser
-- import ..Comments, ..CommentBlock, ..CommentPath # from Parser
-- 
-- /Source
-- Reason: imports and file-level metadata have no method body.


/--
Julia source: base/toml/printer.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_valid_toml_value(@nospecialize(::Any)) = false
```
-/
def is_valid_toml_value_any (_value : V) : Bool := false

/--
Julia source: base/toml/printer.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_valid_toml_value(@nospecialize(::BaseTOMLValue)) = true
```
-/
def is_valid_toml_value_base (_value : BaseTOMLValue) : Bool := true

/--
Julia source: base/toml/printer.jl:7-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_toml_escaped(io::IO, s::AbstractString)
    for c::AbstractChar in s
        if !isvalid(c)
            error("TOML print: invalid character $(repr(c)) encountered when printing string")
        end
        if c == '\b'
            Base.print(io, '\\', 'b')
        elseif c == '\t'
            Base.print(io, '\\', 't')
        elseif c == '\n'
            Base.print(io, '\\', 'n')
        elseif c == '\f'
            Base.print(io, '\\', 'f')
        elseif c == '\r'
            Base.print(io, '\\', 'r')
        elseif c == '"'
            Base.print(io, '\\', '"')
        elseif c == '\\'
            Base.print(io, "\\", '\\')
        elseif Base.iscntrl(c)
            Base.print(io, "\\u")
            Base.print(io, string(UInt32(c), base=16, pad=4))
        else
            Base.print(io, c)
        end
    end
end
```
-/
def print_toml_escaped {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (s : Text) : M World Unit := do
  for c in (← ops.stringChars s) do
    if !(← ops.validChar c) then
      throw (.runtimeError ("TOML print: invalid character " ++ ops.reprChar c ++ " encountered when printing string"))
    else if c == 0x08 then
      printMany ops io [writeChar ops io 0x5c, writeChar ops io 0x62]
    else if c == 0x09 then
      printMany ops io [writeChar ops io 0x5c, writeChar ops io 0x74]
    else if c == 0x0a then
      printMany ops io [writeChar ops io 0x5c, writeChar ops io 0x6e]
    else if c == 0x0c then
      printMany ops io [writeChar ops io 0x5c, writeChar ops io 0x66]
    else if c == 0x0d then
      printMany ops io [writeChar ops io 0x5c, writeChar ops io 0x72]
    else if c == 0x22 then
      printMany ops io [writeChar ops io 0x5c, writeChar ops io 0x22]
    else if c == 0x5c then
      printMany ops io [writeLiteral ops io "\\", writeChar ops io 0x5c]
    else if ← ops.controlChar c then
      writeLiteral ops io "\\u"
      writeBytes ops io (← ops.uint32Hex c (i64 4))
    else
      writeChar ops io c

/-- Runtime `isa` classification for the Julia `BaseTOMLValue` union. -/
def is_base_toml_value {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (value : V) : Bool :=
  match ops.classify value with
  | .base _ => true
  | .other => false

/-- Julia's `is_valid_toml_value(::Any)` fallback and extensible dispatch. -/
def is_valid_toml_value {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (value : V) : M World Bool := do
  match ops.classify value with
  | .base kind => pure (is_valid_toml_value_base kind)
  | .other => ops.invokeLatest (ops.isValidExtension value)

/--
Julia source: base/toml/printer.jl:40-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Packages (e.g. Dates) extend `is_valid_toml_value`. Call it dynamically, so that doing
# so does not invalidate the printer, which also runs while loading packages.
_is_valid_toml_value(@nospecialize(x)) =
    x isa BaseTOMLValue || (@invokelatest is_valid_toml_value(x))::Bool
```
-/
def _is_valid_toml_value {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (value : V) : M World Bool := do
  if is_base_toml_value ops value then pure true
  else ops.invokeLatest (is_valid_toml_value ops value)

/--
Julia source: base/toml/printer.jl:49-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printkey(io::IO, keys::Vector{String})
    for (i, k) in enumerate(keys)
        i != 1 && Base.print(io, ".")
        if length(k) == 0
            # empty key
            Base.print(io, "\"\"")
        elseif any(!isvalid_barekey_char, k)
            # quoted key
            Base.print(io, "\"")
            print_toml_escaped(io, k)
            Base.print(io, "\"")
        else
            Base.print(io, k)
        end
    end
end
```
-/
def printkeyLoop {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) : JInt64 → List Bytes → M World Unit
  | _, [] => pure ()
  | i, key :: rest => do
      if i.val != 1 then writeLiteral ops io "."
      if key.isEmpty then
        writeLiteral ops io "\"\""
      else if ← anyM (fun c => pure (!JuliaLean.base.toml.parser.isvalid_barekey_char c)) (← ops.stringChars (ops.stringFromBytes key)) then
        writeLiteral ops io "\""
        print_toml_escaped ops io (ops.stringFromBytes key)
        writeLiteral ops io "\""
      else
        writeBytes ops io key
      printkeyLoop ops io (addI64 i (i64 1)) rest

def printkey {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (keys : List Bytes) : M World Unit :=
  printkeyLoop ops io (i64 1) keys

/--
Julia source: base/toml/printer.jl:66-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function to_toml_value(@nospecialize(f::Function), value)
    if f === identity
        error(lazy"type `$(typeof(value))` is not a valid TOML type, pass a conversion function to `TOML.print`")
    end
    toml_value = f(value)
    if !_is_valid_toml_value(toml_value)
        error(lazy"TOML syntax function for type `$(typeof(value))` did not return a valid TOML type but a `$(typeof(toml_value))`")
    end
    return toml_value
end
```
-/
def to_toml_value {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (f : Conv) (value : V) : M World V := do
  if ops.isIdentity f then
    throw (.runtimeError ("type `" ++ ops.typeName value ++ "` is not a valid TOML type, pass a conversion function to `TOML.print`"))
  let tomlValue ← ops.convertValue f value
  if !(← _is_valid_toml_value ops tomlValue) then
    throw (.runtimeError ("TOML syntax function for type `" ++ ops.typeName value ++ "` did not return a valid TOML type but a `" ++ ops.typeName tomlValue ++ "`"))
  pure tomlValue

/--
Julia source: base/toml/printer.jl:81-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Fallback
function printvalue(f::Function, io::IO, value, sorted::Bool)
    toml_value = to_toml_value(f, value)
    @invokelatest printvalue(f, io, toml_value, sorted)
end
```
-/
def printvalueFallback {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (renderValue : V → Bool → M World Unit) (f : Conv) (_io : Io)
    (value : V) (sorted : Bool) : M World Unit := do
  let tomlValue ← to_toml_value ops f value
  renderValue tomlValue sorted

@[partial_fixpoint_monotone]
theorem monotone_printvalueFallback
    {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF γ : Type}
    [Lean.Order.PartialOrder γ]
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (renderValue : γ → V → Bool → M World Unit)
    (hRender : ∀ value sorted, Lean.Order.monotone (fun x => renderValue x value sorted))
    (f : Conv) (io : Io) (value : V) (sorted : Bool) :
    Lean.Order.monotone (fun x =>
      printvalueFallback ops (fun value sorted => renderValue x value sorted) f io value sorted) := by
  unfold printvalueFallback
  apply Lean.Order.monotone_bind
  · exact Lean.Order.monotone_const _
  · apply Lean.Order.monotone_of_monotone_apply
    intro tomlValue
    exact hRender tomlValue sorted

/--
Julia source: base/toml/printer.jl:87-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::AbstractVector, sorted::Bool)
    Base.print(io, "[")
    for (i, x) in enumerate(value)
        i != 1 && Base.print(io, ", ")
        printvalue(f, io, x, sorted)
    end
    Base.print(io, "]")
end
```
-/
def printvalueVectorLoop {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (renderValue : V → M World Unit) (io : Io) : Bool → List V → M World Unit
  | _, [] => pure ()
  | first, value :: rest => do
      if !first then writeLiteral ops io ", "
      renderValue value
      printvalueVectorLoop ops renderValue io false rest

@[partial_fixpoint_monotone]
theorem monotone_printvalueVectorLoop
    {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF γ : Type}
    [Lean.Order.PartialOrder γ]
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (renderValue : γ → V → M World Unit)
    (hRender : ∀ value, Lean.Order.monotone (fun x => renderValue x value))
    (io : Io) (first : Bool) (values : List V) :
    Lean.Order.monotone (fun x =>
      printvalueVectorLoop ops (fun value => renderValue x value) io first values) := by
  induction values generalizing first with
  | nil => exact Lean.Order.monotone_const _
  | cons value rest ih =>
      cases first with
      | false =>
          simp [printvalueVectorLoop]
          apply Lean.Order.monotone_bind
          · exact Lean.Order.monotone_const _
          · apply Lean.Order.monotone_of_monotone_apply
            intro _
            apply Lean.Order.monotone_bind
            · exact hRender value
            · apply Lean.Order.monotone_of_monotone_apply
              intro _
              exact ih false
      | true =>
          simp [printvalueVectorLoop]
          apply Lean.Order.monotone_bind
          · exact hRender value
          · apply Lean.Order.monotone_of_monotone_apply
            intro _
            exact ih false

/--
Julia source: base/toml/printer.jl:96-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::Base.TOML.DateTime, sorted::Bool)
    printvalue(f, io, value.date, sorted)
    Base.print(io, "T")
    printvalue(f, io, value.time, sorted)
    Base.print(io, "Z")
end
```
-/
def printvalueDateTime {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (renderDate : Date → Bool → M World Unit) (renderTime : Time → Bool → M World Unit)
    (_f : Conv) (io : Io) (value : DateTime) (sorted : Bool) : M World Unit := do
  renderDate value.date sorted
  writeLiteral ops io "T"
  renderTime value.time sorted
  writeLiteral ops io "Z"

/--
Julia source: base/toml/printer.jl:103-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::Base.TOML.Time, sorted::Bool)
    Base.print(io, string(value.hour, pad=2))
    Base.print(io, ":")
    Base.print(io, string(value.minute, pad=2))
    Base.print(io, ":")
    Base.print(io, string(value.second, pad=2))
    if value.ms != 0
        Base.print(io, ".")
        Base.print(io, string(value.ms, pad=3))
    end
end
```
-/
def printvalueTime {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (_f : Conv) (io : Io) (value : Time) (_sorted : Bool) : M World Unit := do
  writeBytes ops io (← ops.intStringPad value.hour (i64 2))
  writeLiteral ops io ":"
  writeBytes ops io (← ops.intStringPad value.minute (i64 2))
  writeLiteral ops io ":"
  writeBytes ops io (← ops.intStringPad value.second (i64 2))
  if value.ms.val != 0 then
    writeLiteral ops io "."
    writeBytes ops io (← ops.intStringPad value.ms (i64 3))

/--
Julia source: base/toml/printer.jl:115-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::Base.TOML.Date, sorted::Bool)
    Base.print(io, string(value.year, pad=4))
    Base.print(io, "-")
    Base.print(io, string(value.month, pad=2))
    Base.print(io, "-")
    Base.print(io, string(value.day, pad=2))
end
```
-/
def printvalueDate {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (_f : Conv) (io : Io) (value : Date) (_sorted : Bool) : M World Unit := do
  writeBytes ops io (← ops.intStringPad value.year (i64 4))
  writeLiteral ops io "-"
  writeBytes ops io (← ops.intStringPad value.month (i64 2))
  writeLiteral ops io "-"
  writeBytes ops io (← ops.intStringPad value.day (i64 2))

/--
Julia source: base/toml/printer.jl:123-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::Bool, sorted::Bool)
    Base.print(io, value ? "true" : "false")
end
```
-/
def printvalueBool {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (_f : Conv) (io : Io) (value : Bool) (_sorted : Bool) : M World Unit :=
  writeLiteral ops io (if value then "true" else "false")

/--
Julia source: base/toml/printer.jl:127-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::Integer, sorted::Bool)
    value isa Signed && return Base.show(io, value)
    # unsigned integers are printed as hex
    n = 2 * ndigits(value, base=256)
    Base.print(io, "0x", string(value, base=16, pad=n))
    return
end
```
-/
def printvalueInteger {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (_f : Conv) (io : Io) (value : Integer) (_sorted : Bool) : M World Unit := do
  if ops.integerIsSigned value then
    ops.integerShow io value
  else
    let digits ← ops.integerNdigits value (i64 256)
    let pad := mulI64 (i64 2) digits
    printMany ops io [writeLiteral ops io "0x", do writeBytes ops io (← ops.integerHex value pad)]

/--
Julia source: base/toml/printer.jl:135-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::AbstractFloat, sorted::Bool)
    # The early conversion here avoids invalidations from isnan/isinf
    value = Float64(value)

    if isnan(value)
        Base.print(io, "nan")
    elseif isinf(value)
        Base.print(io, value > 0 ? "+inf" : "-inf")
    else
        Base.print(io, value) # TOML specifies IEEE 754 binary64 for float
    end
end
```
-/
def printvalueFloat {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (_f : Conv) (io : Io) (value : Float) (_sorted : Bool) : M World Unit := do
  let value ← ops.float64 value
  if JuliaLean.Float.F64.isnan value then
    writeLiteral ops io "nan"
  else if JuliaLean.Float.F64.isinf value then
    writeLiteral ops io (if ops.floatGreaterZero value then "+inf" else "-inf")
  else
    ops.floatPrint io value

/--
Julia source: base/toml/printer.jl:148-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::AbstractString, sorted::Bool)
    qmark = Base.contains(value, "\n") ? "\"\"\"" : "\""
    Base.print(io, qmark)
    print_toml_escaped(io, value)
    Base.print(io, qmark)
end
```
-/
def printvalueString {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (_f : Conv) (io : Io) (value : Text) (_sorted : Bool) : M World Unit := do
  let qmark := if ← ops.stringContains value [0x0a] then [0x22, 0x22, 0x22] else [0x22]
  writeBytes ops io qmark
  print_toml_escaped ops io value
  writeBytes ops io qmark

/--
Julia source: base/toml/printer.jl:155-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function printvalue(f::Function, io::IO, value::AbstractDict, sorted::Bool)
    print_inline_table(f, io, value, sorted)
end
```
-/
def printvalueDict {World Io V Dict Conv : Type}
    (renderInline : (Io → V → Bool → M World Unit) → Conv → Io → Dict → Bool → M World Unit)
    (printValue : Io → V → Bool → M World Unit) (f : Conv) (io : Io)
    (value : Dict) (sorted : Bool) : M World Unit :=
  renderInline printValue f io value sorted

def printInlineKeyPrefix {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (value : Dict) (index : JInt64) (key : Key) : M World V := do
  let item ← ops.dictGet value key
  if index.val != 1 then writeLiteral ops io ", "
  let keyText ← ops.keyString key
  printkey ops io [keyText]
  writeLiteral ops io " = "
  pure item

/--
Julia source: base/toml/printer.jl:159-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_inline_table(f::Function, io::IO, value::AbstractDict, sorted::Bool)
    vkeys = collect(keys(value))::AbstractArray
    if sorted
        sort!(vkeys)
    end
    Base.print(io, "{")
    for (i, k) in enumerate(vkeys)
        v = value[k]
        i != 1 && Base.print(io, ", ")
        printkey(io, [String(k)])
        Base.print(io, " = ")
        printvalue(f, io, v, sorted)
    end
    Base.print(io, "}")
end
```
-/
def printInlineKeyLoop {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (printValue : Io → V → Bool → M World Unit) (io : Io) (value : Dict)
    (sorted : Bool) : JInt64 → List Key → M World Unit
  | _, [] => pure ()
  | index, key :: rest => do
      let item ← printInlineKeyPrefix ops io value index key
      printValue io item sorted
      printInlineKeyLoop ops printValue io value sorted (addI64 index (i64 1)) rest

@[partial_fixpoint_monotone]
theorem monotone_printInlineKeyLoop
    {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF γ : Type}
    [Lean.Order.PartialOrder γ]
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (printValue : γ → Io → V → Bool → M World Unit)
    (hRender : ∀ io value sorted, Lean.Order.monotone (fun x => printValue x io value sorted))
    (io : Io) (value : Dict) (sorted : Bool) (index : JInt64) (keys : List Key) :
    Lean.Order.monotone (fun x =>
      printInlineKeyLoop ops (fun io value sorted => printValue x io value sorted)
        io value sorted index keys) := by
  induction keys generalizing index with
  | nil => exact Lean.Order.monotone_const _
  | cons key rest ih =>
      simp [printInlineKeyLoop]
      apply Lean.Order.monotone_bind
      · exact Lean.Order.monotone_const _
      · apply Lean.Order.monotone_of_monotone_apply
        intro item
        apply Lean.Order.monotone_bind
        · exact hRender io item sorted
        · apply Lean.Order.monotone_of_monotone_apply
          intro _
          exact ih (addI64 index (i64 1))

def print_inline_table {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (printValue : Io → V → Bool → M World Unit) (_f : Conv) (io : Io)
    (value : Dict) (sorted : Bool) : M World Unit := do
  let unsortedKeys ← ops.dictKeys value
  let vkeys ← if sorted then ops.sortKeys unsortedKeys else pure unsortedKeys
  writeLiteral ops io "{"
  printInlineKeyLoop ops printValue io value sorted (i64 1) vkeys
  writeLiteral ops io "}"

@[partial_fixpoint_monotone]
theorem monotone_print_inline_table
    {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF γ : Type}
    [Lean.Order.PartialOrder γ]
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (printValue : γ → Io → V → Bool → M World Unit)
    (hRender : ∀ io value sorted, Lean.Order.monotone (fun x => printValue x io value sorted))
    (f : Conv) (io : Io) (value : Dict) (sorted : Bool) :
    Lean.Order.monotone (fun x =>
      print_inline_table ops (fun io value sorted => printValue x io value sorted) f io value sorted) := by
  cases sorted with
  | false =>
      simp [print_inline_table]
      apply Lean.Order.monotone_bind
      · exact Lean.Order.monotone_const _
      · apply Lean.Order.monotone_of_monotone_apply
        intro unsortedKeys
        apply Lean.Order.monotone_bind
        · exact Lean.Order.monotone_const _
        · apply Lean.Order.monotone_of_monotone_apply
          intro keys
          apply Lean.Order.monotone_bind
          · exact Lean.Order.monotone_const _
          · apply Lean.Order.monotone_of_monotone_apply
            intro _
            apply Lean.Order.monotone_bind
            · exact monotone_printInlineKeyLoop ops printValue hRender io value false (i64 1) _
            · exact Lean.Order.monotone_const _
  | true =>
      simp [print_inline_table]
      apply Lean.Order.monotone_bind
      · exact Lean.Order.monotone_const _
      · apply Lean.Order.monotone_of_monotone_apply
        intro unsortedKeys
        apply Lean.Order.monotone_bind
        · exact Lean.Order.monotone_const _
        · apply Lean.Order.monotone_of_monotone_apply
          intro keys
          apply Lean.Order.monotone_bind
          · exact Lean.Order.monotone_const _
          · apply Lean.Order.monotone_of_monotone_apply
            intro _
            apply Lean.Order.monotone_bind
            · exact monotone_printInlineKeyLoop ops printValue hRender io value true (i64 1) keys
            · exact Lean.Order.monotone_const _

/--
Julia source: base/toml/printer.jl:180-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Sanitize comment text so it cannot introduce TOML syntax.

function print_comment_line(io::IO, indentstr::String, text::AbstractString)
    Base.print(io, indentstr, '#')
    # Preserve captured whitespace, but format programmatic comments as `# text`.
    if !(isempty(text) || first(text) == ' ' || first(text) == '\t')
        Base.print(io, ' ')
    end
    for c::AbstractChar in text
        if c == '\n'
            Base.print(io, '\n', indentstr, "# ")
        elseif c == '\t' || !Base.iscntrl(c)
            Base.print(io, c)
        end
    end
    Base.print(io, '\n')
end
```
-/
def print_comment_line {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (indentstr : Bytes) (text : Text) : M World Unit := do
  printMany ops io [writeBytes ops io indentstr, writeLiteral ops io "#"]
  let chars ← ops.stringChars text
  let isEmpty ← ops.stringLength text
  if isEmpty.val == 0 then pure ()
  else
    let first ← ops.stringFirst text
    if first != 0x20 && first != 0x09 then writeLiteral ops io " "
  for c in chars do
    if c == 0x0a then
      printMany ops io [writeChar ops io 0x0a, writeBytes ops io indentstr, writeLiteral ops io "# "]
    else if c == 0x09 || !(← ops.controlChar c) then
      writeChar ops io c
  writeChar ops io 0x0a

/--
Julia source: base/toml/printer.jl:198-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_comments_above(io::IO, comments::Comments, path::CommentPath, indentstr::String)
    block = get(comments.items, path, nothing)
    block === nothing && return
    for line in block.above
        print_comment_line(io, indentstr, line)
    end
end
```
-/
def print_comments_above {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (commentItems : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (io : Io) (comments : Comments CI CF) (path : CommentPath) (indentstr : Bytes) : M World Unit := do
  match commentItems.get comments.items path with
  | none => pure ()
  | some block =>
      for line in block.above do
        print_comment_line ops io indentstr (ops.stringFromBytes line)

/--
Julia source: base/toml/printer.jl:206-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_comment_inline(io::IO, comments::Comments, path::CommentPath)
    block = get(comments.items, path, nothing)
    block === nothing && return
    text = block.inline
    text === nothing && return
    Base.print(io, " #")
    if !(isempty(text) || first(text) == ' ' || first(text) == '\t')
        Base.print(io, ' ')
    end
    for c::AbstractChar in text
        if c == '\t' || (c != '\n' && !Base.iscntrl(c))
            Base.print(io, c)
        else
            Base.print(io, ' ')
        end
    end
end
```
-/
def print_comment_inline {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (commentItems : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (io : Io) (comments : Comments CI CF) (path : CommentPath) : M World Unit := do
  match commentItems.get comments.items path with
  | none => pure ()
  | some block =>
      match block.inline with
      | none => pure ()
      | some bytes => do
          let text := ops.stringFromBytes bytes
          writeLiteral ops io " #"
          let chars ← ops.stringChars text
          let isEmpty ← ops.stringLength text
          if isEmpty.val == 0 then pure ()
          else
            let first ← ops.stringFirst text
            if first != 0x20 && first != 0x09 then writeLiteral ops io " "
          for c in chars do
            if c == 0x09 || (c != 0x0a && !(← ops.controlChar c)) then writeChar ops io c
            else writeLiteral ops io " "

/--
Julia source: base/toml/printer.jl:224-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_comments(comments::Comments, path::CommentPath) =
    haskey(comments.items, path) || haskey(comments.floating, path)
```
-/
def has_comments {CI CF : Type}
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (comments : Comments CI CF) (path : CommentPath) : Bool :=
  (itemOps.get comments.items path).isSome || (floatingOps.get comments.floating path).isSome

inductive HoistedTask (Dict Key : Type) where
  | enter (dict : Dict) (path : CommentPath)
  | entries (dict : Dict) (path : CommentPath) (keys : List Key)

def printerWhileLoop {World State Result : Type}
    (step : State → M World (Sum Result State)) (state : State) : M World Result :=
  fun world =>
    match step state world with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (.inl result, world)) => some (.ok (result, world))
    | some (.ok (.inr next, world)) => printerWhileLoop step next world
partial_fixpoint

def printHoistedStep {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (io : Io) (comments : Comments CI CF) (indentstr : Bytes) (sorted : Bool)
    (tasks : List (HoistedTask Dict Key)) :
    M World (Sum Unit (List (HoistedTask Dict Key))) := do
  match tasks with
  | [] => pure (.inl ())
  | .enter dict path :: rest => do
      match floatingOps.get comments.floating path with
      | none => pure ()
      | some lines =>
          for line in lines do
            print_comment_line ops io indentstr (ops.stringFromBytes line)
      let unsortedKeys ← ops.dictKeys dict
      let keys ← if sorted then ops.sortKeys unsortedKeys else pure unsortedKeys
      pure (.inr (.entries dict path keys :: rest))
  | .entries dict path [] :: rest => pure (.inr rest)
  | .entries dict path (key :: keys) :: rest => do
      let keyText ← ops.keyString key
      let keyPath := path ++ [keyText]
      match itemOps.get comments.items keyPath with
      | none => pure ()
      | some block =>
          for line in block.above do
            print_comment_line ops io indentstr (ops.stringFromBytes line)
          match block.inline with
          | none => pure ()
          | some line => print_comment_line ops io indentstr (ops.stringFromBytes line)
      let value ← ops.dictGet dict key
      let remaining := HoistedTask.entries dict path keys :: rest
      match ops.classify value with
      | .base .abstractDict => pure (.inr (.enter (ops.asDict value) keyPath :: remaining))
      | _ => pure (.inr remaining)

/--
Julia source: base/toml/printer.jl:227-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Hoist nested comments to an inline table's owning entry.
function print_hoisted_inline_comments(io::IO, comments::Comments, a::AbstractDict,
                                       path::CommentPath, indentstr::String, sorted::Bool)
    floating = get(comments.floating, path, nothing)
    if floating !== nothing
        for line in floating
            print_comment_line(io, indentstr, line)
        end
    end
    vkeys = collect(keys(a))
    sorted && sort!(vkeys)
    for k in vkeys
        kpath = [path; String(k)]
        block = get(comments.items, kpath, nothing)
        if block !== nothing
            for line in block.above
                print_comment_line(io, indentstr, line)
            end
            block.inline === nothing || print_comment_line(io, indentstr, block.inline)
        end
        v = a[k]
        v isa AbstractDict && print_hoisted_inline_comments(io, comments, v, kpath, indentstr, sorted)
    end
end
```
-/
def print_hoisted_inline_comments {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (io : Io) (comments : Comments CI CF) (dict : Dict) (path : CommentPath)
    (indentstr : Bytes) (sorted : Bool) : M World Unit :=
  printerWhileLoop (printHoistedStep ops itemOps floatingOps io comments indentstr sorted)
    [.enter dict path]

/--
Julia source: base/toml/printer.jl:252-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_comments_floating(io::IO, comments::Comments, path::CommentPath, indentstr::String)
    lines = get(comments.floating, path, nothing)
    lines === nothing && return false
    for line in lines
        print_comment_line(io, indentstr, line)
    end
    return !isempty(lines)
end
```
-/
def print_comments_floating {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (io : Io) (comments : Comments CI CF) (path : CommentPath) (indentstr : Bytes) : M World Bool := do
  match floatingOps.get comments.floating path with
  | none => pure false
  | some lines =>
      for line in lines do
        print_comment_line ops io indentstr (ops.stringFromBytes line)
      pure (!lines.isEmpty)

/--
Julia source: base/toml/printer.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_table(@nospecialize(value)) = isa(value, AbstractDict)
```
-/
def is_table {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (value : V) : Bool :=
  match ops.classify value with
  | .base .abstractDict => true
  | _ => false


/--
Julia source: base/toml/printer.jl:266-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_array_of_tables(@nospecialize(value)) =
    isa(value, AbstractArray) &&
    length(value) > 0 && (isa(value, AbstractArray{<:AbstractDict}) ||
                          all(v -> isa(v, AbstractDict), value))
```
-/
def is_array_of_tables {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (value : V) : M World Bool := do
  match ops.classify value with
  | .base .abstractVector => do
      let array := ops.asArray value
      if (← ops.arrayLength array).val <= 0 then pure false
      else if ops.arrayHasDictElementType array then pure true
      else allM (fun item => pure (is_table ops item)) (← ops.arrayValues array)
  | _ => pure false

/--
Julia source: base/toml/printer.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_tabular(@nospecialize(value)) = is_table(value) || @invokelatest(is_array_of_tables(value))
```
-/
def is_tabular {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (value : V) : M World Bool := do
  if is_table ops value then pure true else ops.invokeLatest (is_array_of_tables ops value)

/-- The first pass of `print_table`, which emits only non-tabular entries. -/
def printTableEntries {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (f : Conv) (renderValue : V → Bool → M World Unit)
    (io : Io) (dict : Dict) (keys : List Bytes) (indentText : Bytes)
    (sorted : Bool) (inlineTables : Inline) (comments : Option (Comments CI CF))
    : Bool → List Key → M World Bool
  | firstBlock, [] => pure firstBlock
  | firstBlock, key :: rest => do
      let original ← ops.dictGet dict key
      let value ← if ← _is_valid_toml_value ops original then pure original else to_toml_value ops f original
      let tableLike ← is_tabular ops value
      let isInline := ops.inlineMember inlineTables value
      if tableLike && !isInline then
        printTableEntries ops itemOps floatingOps f renderValue io dict keys indentText sorted inlineTables comments firstBlock rest
      else do
        match comments with
        | none => pure ()
        | some commentData => do
            let entryKey ← ops.keyString key
            let entryPath := keys ++ [entryKey]
            print_comments_above ops itemOps io commentData entryPath indentText
            if is_table ops value && isInline then
              print_hoisted_inline_comments ops itemOps floatingOps io commentData (ops.asDict value)
                entryPath indentText sorted
        let keyText ← ops.keyString key
        writeBytes ops io indentText
        printkey ops io [keyText]
        writeLiteral ops io " = "
        renderValue value sorted
        match comments with
        | none => pure ()
        | some commentData => do
            let entryKey ← ops.keyString key
            print_comment_inline ops itemOps io commentData (keys ++ [entryKey])
        writeChar ops io 0x0a
        printTableEntries ops itemOps floatingOps f renderValue io dict keys indentText sorted inlineTables comments false rest
/--
Julia source: base/toml/printer.jl:367-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            for v in value
                Base.print(io, ' '^4indent)
                Base.print(io,"[[")
                printkey(io, ks)
                Base.print(io,"]]\n")
                # TODO, nicer error here
                !isa(v, AbstractDict) && error("array should contain only tables")
                @invokelatest print_table(f, io, v, ks; indent = indent + 1, sorted, by, inline_tables, comments)
```
-/
def printArrayOfTablesLoop {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (io : Io) (childKeys : List Bytes) (indent : JInt64)
    (recurseTable : Dict → List Bytes → JInt64 → Bool → M World Unit) :
    List V → M World Unit
  | [] => pure ()
  | item :: rest => do
      let spaces ← ops.repeatChar 0x20 (mulI64 (i64 4) indent)
      writeBytes ops io spaces
      writeLiteral ops io "[["
      printkey ops io childKeys
      writeLiteral ops io "]]\n"
      if !is_table ops item then throw (.runtimeError "array should contain only tables")
      recurseTable (ops.asDict item) childKeys (addI64 indent (i64 1)) true
      printArrayOfTablesLoop ops io childKeys indent recurseTable rest

theorem monotone_printArrayOfTablesLoop
    {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF γ : Type}
    [Lean.Order.PartialOrder γ]
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (recurseTable : γ → Dict → List Bytes → JInt64 → Bool → M World Unit)
    (hrec : ∀ child childKeys childIndent childFirst,
      Lean.Order.monotone (fun x => recurseTable x child childKeys childIndent childFirst))
    (io : Io) (childKeys : List Bytes) (indent : JInt64) (items : List V) :
    Lean.Order.monotone (fun x => printArrayOfTablesLoop ops io childKeys indent
      (fun child childKeys childIndent childFirst =>
        recurseTable x child childKeys childIndent childFirst) items) := by
  induction items with
  | nil => exact Lean.Order.monotone_const _
  | cons item rest ih =>
      simp only [printArrayOfTablesLoop]
      core_mono (first | exact ih | exact hrec _ _ _ _)


/-- The second pass of `print_table`, which emits nested tables and arrays of tables. -/
def printNestedTables {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (f : Conv) (io : Io) (dict : Dict) (keys : List Bytes) (indent : JInt64)
    (sorted : Bool) (inlineTables : Inline) (byFn : By) (comments : Option (Comments CI CF))
    (recurseTable : Dict → List Bytes → JInt64 → Bool → M World Unit)
    : Bool → List Key → M World Unit
  | _, [] => pure ()
  | firstBlock, key :: rest => do
      let original ← ops.dictGet dict key
      let value ← if ← _is_valid_toml_value ops original then pure original else to_toml_value ops f original
      let isDict := is_table ops value
      let isInline := ops.inlineMember inlineTables value
      if isDict && !isInline then
        let keyText ← ops.keyString key
        let childKeys := keys ++ [keyText]
        let values ← ops.dictValues (ops.asDict value)
        let empty ← ops.dictIsEmpty (ops.asDict value)
        let header ← if empty then pure true else do
          let allTabular ← allM (fun v => is_tabular ops v) values
          if !allTabular then pure true
          else anyM (fun v => pure (ops.inlineMember inlineTables v)) values
        let header ← if header then pure true else
          match comments with
          | none => pure false
          | some commentData => pure (has_comments itemOps floatingOps commentData childKeys)
        let nextFirstBlock ← if header then do
          if !firstBlock then writeChar ops io 0x0a
          match comments with
          | none => pure ()
          | some commentData => do
              let _ ← print_comments_above ops itemOps io commentData childKeys
                (← ops.repeatChar 0x20 (mulI64 (i64 4) indent))
              pure ()
          writeBytes ops io (← ops.repeatChar 0x20 (mulI64 (i64 4) indent))
          writeLiteral ops io "["
          printkey ops io childKeys
          writeLiteral ops io "]"
          match comments with
          | none => pure ()
          | some commentData => print_comment_inline ops itemOps io commentData childKeys
          writeChar ops io 0x0a
          pure false
        else pure firstBlock
        recurseTable (ops.asDict value) childKeys
          (addI64 indent (if header then i64 1 else i64 0)) header
        printNestedTables ops itemOps floatingOps f io dict keys indent sorted inlineTables byFn comments
          recurseTable nextFirstBlock rest
      else do
        let isArrayOfTables ← is_array_of_tables ops value
        if !isArrayOfTables then
          printNestedTables ops itemOps floatingOps f io dict keys indent sorted inlineTables byFn comments
            recurseTable firstBlock rest
        else do
          if !firstBlock then writeChar ops io 0x0a
          let keyText ← ops.keyString key
          let childKeys := keys ++ [keyText]
          match comments with
          | none => pure ()
          | some commentData => do
              let _ ← print_comments_above ops itemOps io commentData childKeys
                (← ops.repeatChar 0x20 (mulI64 (i64 4) indent))
              pure ()
          let items ← ops.arrayValues (ops.asArray value)
          printArrayOfTablesLoop ops io childKeys indent recurseTable items
          printNestedTables ops itemOps floatingOps f io dict keys indent sorted inlineTables byFn comments
            recurseTable false rest


set_option maxHeartbeats 1600000 in
@[partial_fixpoint_monotone]
theorem monotone_printNestedTables
    {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF γ : Type}
    [Lean.Order.PartialOrder γ]
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (f : Conv) (io : Io) (dict : Dict) (keys : List Bytes) (indent : JInt64)
    (sorted : Bool) (inlineTables : Inline) (byFn : By) (comments : Option (Comments CI CF))
    (recurseTable : γ → Dict → List Bytes → JInt64 → Bool → M World Unit)
    (hrec : ∀ child childKeys childIndent childFirst,
      Lean.Order.monotone (fun x => recurseTable x child childKeys childIndent childFirst))
    (firstBlock : Bool) (remaining : List Key) :
    Lean.Order.monotone (fun x =>
      printNestedTables ops itemOps floatingOps f io dict keys indent sorted inlineTables byFn comments
        (fun child childKeys childIndent childFirst =>
          recurseTable x child childKeys childIndent childFirst) firstBlock remaining) := by
  cases comments <;> induction remaining generalizing firstBlock with
  | nil => exact Lean.Order.monotone_const _
  | cons key rest ih =>
      simp only [printNestedTables]
      core_mono (first | exact ih _ | exact hrec _ _ _ _ |
        exact monotone_printArrayOfTablesLoop ops recurseTable hrec _ _ _ _)

/-- Julia's dynamic `printvalue` dispatcher; its method choice is trusted Julia dispatch. -/
def printvalueLoop {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (f : Conv) (io : Io) (value : V) (sorted : Bool) : M World Unit := do
  match ops.classify value with
  | .base .abstractVector => do
      let items ← ops.arrayValues (ops.asArray value)
      writeLiteral ops io "["
      printvalueVectorLoop ops (fun item => printvalueLoop ops f io item sorted) io true items
      writeLiteral ops io "]"
  | .base .dateTime =>
      printvalueDateTime ops (printvalueDate ops f io) (printvalueTime ops f io) f io (ops.asDateTime value) sorted
  | .base .time => printvalueTime ops f io (ops.asTime value) sorted
  | .base .date => printvalueDate ops f io (ops.asDate value) sorted
  | .base .bool => printvalueBool ops f io (ops.asBool value) sorted
  | .base .integer => printvalueInteger ops f io (ops.asInteger value) sorted
  | .base .abstractFloat => printvalueFloat ops f io (ops.asFloat value) sorted
  | .base .abstractString => printvalueString ops f io (ops.stringValue value) sorted
  | .base .abstractDict =>
      print_inline_table ops
        (fun stream item itemSorted => printvalueLoop ops f stream item itemSorted)
        f io (ops.asDict value) sorted
  | .other =>
      printvalueFallback ops (fun item itemSorted => printvalueLoop ops f io item itemSorted)
        f io value sorted
partial_fixpoint

/--
Julia source: base/toml/printer.jl:272-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_table(f::Function, io::IO, a::AbstractDict,
    ks::Vector{String} = String[];
    indent::Int = 0,
    first_block::Bool = true,
    sorted::Bool = false,
    inline_tables::IdSet,
    by::Function = identity,
    comments::Union{Comments, Nothing} = nothing,
)

    if a in inline_tables
        @invokelatest print_inline_table(f, io, a, sorted)
        return
    end

    entry_indentstr = ' '^4max(0, indent-1)
    if comments !== nothing
        if print_comments_floating(io, comments, ks, entry_indentstr)
            println(io)
        end
    end

    akeys = keys(a)
    if sorted
        akeys = sort!(collect(akeys); by)
    end

    # First print non-tabular entries
    for key in akeys
        value = a[key]
        if !_is_valid_toml_value(value)
            value = to_toml_value(f, value)
        end
        if is_tabular(value) && !(value in inline_tables)
            continue
        end

        if comments !== nothing
            entry_path = [ks; String(key)]
            print_comments_above(io, comments, entry_path, entry_indentstr)
            if value isa AbstractDict && value in inline_tables
                print_hoisted_inline_comments(io, comments, value, entry_path, entry_indentstr, sorted)
            end
        end
        Base.print(io, entry_indentstr)
        printkey(io, [String(key)])
        Base.print(io, " = ") # print separator
        printvalue(f, io, value, sorted)
        if comments !== nothing
            print_comment_inline(io, comments, [ks; String(key)])
        end
        Base.print(io, "\n")  # new line?
        first_block = false
    end

    for key in akeys
        value = a[key]
        if !_is_valid_toml_value(value)
            value = to_toml_value(f, value)
        end
        if is_table(value) && !(value in inline_tables)
            push!(ks, String(key))
            _values = @invokelatest values(value)
            header = isempty(value) || !all(is_tabular(v) for v in _values)::Bool || any(v in inline_tables for v in _values)::Bool
            if !header && comments !== nothing
                # Preserve headers that anchor comments.
                header = has_comments(comments, ks)
            end
            if header
                # print table
                first_block || println(io)
                first_block = false
                if comments !== nothing
                    print_comments_above(io, comments, ks, ' '^4indent)
                end
                Base.print(io, ' '^4indent)
                Base.print(io,"[")
                printkey(io, ks)
                Base.print(io,"]")
                if comments !== nothing
                    print_comment_inline(io, comments, ks)
                end
                Base.print(io,"\n")
            end
            # Use runtime dispatch here since the type of value seems not to be enforced other than as AbstractDict
            @invokelatest print_table(f, io, value, ks; indent = indent + header, first_block = header, sorted, by, inline_tables, comments)
            pop!(ks)
        elseif @invokelatest(is_array_of_tables(value))
            # print array of tables
            first_block || println(io)
            first_block = false
            push!(ks, String(key))
            if comments !== nothing
                print_comments_above(io, comments, ks, ' '^4indent)
            end
            for v in value
                Base.print(io, ' '^4indent)
                Base.print(io,"[[")
                printkey(io, ks)
                Base.print(io,"]]\n")
                # TODO, nicer error here
                !isa(v, AbstractDict) && error("array should contain only tables")
                @invokelatest print_table(f, io, v, ks; indent = indent + 1, sorted, by, inline_tables, comments)
            end
            pop!(ks)
        end
    end
end
```
-/
def printTableLoop {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (f : Conv) (io : Io) (dict : Dict) (keys : List Bytes) (indent : JInt64)
    (firstBlock sorted : Bool) (inlineTables : Inline) (byFn : By)
    (comments : Option (Comments CI CF)) : M World Unit := do
  if ops.inlineDictMember inlineTables dict then
    print_inline_table ops (fun stream item itemSorted => printvalueLoop ops f stream item itemSorted)
      f io dict sorted
  else
    let previousIndent := subI64 indent (i64 1)
    let entryIndent ← ops.repeatChar 0x20
      (mulI64 (i64 4) (if previousIndent.val > 0 then previousIndent else i64 0))
    match comments with
    | none => pure ()
    | some commentData =>
        if ← print_comments_floating ops floatingOps io commentData keys entryIndent then
          writeChar ops io 0x0a
    let unsortedKeys ← ops.dictKeys dict
    let sortedKeys ← if sorted then ops.sortKeysBy byFn unsortedKeys else pure unsortedKeys
    let renderValue := fun value sorted => printvalueLoop ops f io value sorted
    let afterEntries ← printTableEntries ops itemOps floatingOps f renderValue io dict keys entryIndent sorted inlineTables comments firstBlock sortedKeys
    let recurseTable := fun child childKeys childIndent childFirst =>
      printTableLoop ops itemOps floatingOps f io child childKeys childIndent childFirst sorted inlineTables byFn comments
    printNestedTables ops itemOps floatingOps f io dict keys indent sorted inlineTables byFn comments recurseTable afterEntries sortedKeys
partial_fixpoint

/--
Julia source: base/toml/printer.jl:386-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(f::Function, io::IO, a::AbstractDict; sorted::Bool=false, by=identity, inline_tables::IdSet{<:AbstractDict}=IdSet{Dict{String}}(), comments::Union{Comments, Nothing}=nothing) =
    print_table(f, io, a; sorted, by, inline_tables, comments)
```
-/
def print_f_io {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (f : Conv) (io : Io) (dict : Dict) (sorted : Bool) (byFn : By)
    (inlineTables : Inline) (comments : Option (Comments CI CF)) : M World Unit :=
  printTableLoop ops itemOps floatingOps f io dict [] (i64 0) true sorted inlineTables byFn comments

/--
Julia source: base/toml/printer.jl:388-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(f::Function, a::AbstractDict; sorted::Bool=false, by=identity, inline_tables::IdSet{<:AbstractDict}=IdSet{Dict{String}}(), comments::Union{Comments, Nothing}=nothing) =
    print(f, stdout, a; sorted, by, inline_tables, comments)
```
-/
def print_f {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (f : Conv) (dict : Dict) (sorted : Bool) (byFn : By)
    (inlineTables : Inline) (comments : Option (Comments CI CF)) : M World Unit :=
  print_f_io ops itemOps floatingOps f ops.stdout dict sorted byFn inlineTables comments

/--
Julia source: base/toml/printer.jl:390-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, a::AbstractDict; sorted::Bool=false, by=identity, inline_tables::IdSet{<:AbstractDict}=IdSet{Dict{String}}(), comments::Union{Comments, Nothing}=nothing) =
    print_table(identity, io, a; sorted, by, inline_tables, comments)
```
-/
def print_io {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (io : Io) (dict : Dict) (sorted : Bool) (byFn : By)
    (inlineTables : Inline) (comments : Option (Comments CI CF)) : M World Unit :=
  print_f_io ops itemOps floatingOps ops.identityConv io dict sorted byFn inlineTables comments

/--
Julia source: base/toml/printer.jl:392-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(a::AbstractDict; sorted::Bool=false, by=identity, inline_tables::IdSet{<:AbstractDict}=IdSet{Dict{String}}(), comments::Union{Comments, Nothing}=nothing) =
    print(identity, stdout, a; sorted, by, inline_tables, comments)
```
-/
def print_dict {World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF : Type}
    (ops : PrinterOps World Io V Arr Dict Key Inline Conv By Integer Float Text CI CF)
    (itemOps : JuliaLean.base.toml.parser.DictOps CommentPath CommentBlock CI)
    (floatingOps : JuliaLean.base.toml.parser.DictOps CommentPath (List Bytes) CF)
    (dict : Dict) (sorted : Bool) (byFn : By) (inlineTables : Inline)
    (comments : Option (Comments CI CF)) : M World Unit :=
  print_f ops itemOps floatingOps ops.identityConv dict sorted byFn inlineTables comments

end JuliaLean.base.toml.printer
