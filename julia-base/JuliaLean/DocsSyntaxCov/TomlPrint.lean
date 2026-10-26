import JuliaLean.Toml.Props
import JuliaLean.DocsSyntaxCov.Ast

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
