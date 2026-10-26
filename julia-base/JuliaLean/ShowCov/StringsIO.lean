import JuliaLean.ShowCov.Basic
import JuliaLean.Show.Escape

/-!
# `base/strings/io.jl`

`print`/`write` calls are recorded as `Ev` events so that `lock`/`unlock`
pairing is visible. A value's `show`/`print` output is given as its events
(or text), and may end in an exception (`Shown`). `IOContext` properties are
association lists `Props` (latest binding first).
-/

namespace JuliaLean.ShowCov.StringsIO

open JuliaLean.ShowCov

/-- Effects on a stream. -/
inductive Ev where
  | lock
  | unlock
  | write (s : String)
  deriving DecidableEq, Repr

/-- The text written by a list of events. -/
def evText : List Ev → String
  | [] => ""
  | .write s :: es => s ++ evText es
  | _ :: es => evText es

/-- Net lock depth after a list of events. -/
def lockDepth : List Ev → Int
  | [] => 0
  | .lock :: es => 1 + lockDepth es
  | .unlock :: es => lockDepth es - 1
  | _ :: es => lockDepth es

/-- What a `show`/`print` call does: events, then normal return or an exception. -/
structure Shown where
  evs : List Ev
  err : Option Err

/-- `print(io::IO, x)`, `base/strings/io.jl:32-40`:
`lock(io); try show(io, x) finally unlock(io) end; return nothing`. -/
def printAny (shown : Shown) : Shown :=
  ⟨[.lock] ++ shown.evs ++ [.unlock], shown.err⟩

/-- `print(io::IO, xs...)`, `base/strings/io.jl:42-54`: under one lock, `print(io, xs[i])`
for each argument until one throws. -/
def printMany (items : List Shown) : Shown :=
  let rec go : List Shown → List Ev × Option Err
    | [] => ([], none)
    | x :: xs =>
      let p := printAny x
      match p.err with
      | some e => (p.evs, some e)
      | none => let (r, e) := go xs; (p.evs ++ r, e)
  let (evs, e) := go items
  ⟨[.lock] ++ evs ++ [.unlock], e⟩

/-- A plain string argument: one write. -/
def strArg (s : String) : Shown := ⟨[.write s], none⟩

/-- `println(io::IO, xs...) = print(io, xs..., "\n")`, `base/strings/io.jl:77`. -/
def printlnMany (items : List Shown) : Shown := printMany (items ++ [strArg "\n"])

/-! ## `sprint`, `repr`, `string` -/

/-- `IOContext` properties, latest binding first (`ImmutableDict` lookup order). -/
abbrev Props := List (String × String)

/-- The `context` keyword of `sprint`/`repr`: `nothing`, one pair, a tuple of
pairs, or an `IO` whose properties are inherited. -/
inductive Ctx where
  | none
  | pair (kv : String × String)
  | tuple (kvs : List (String × String))
  | io (props : Props)

/-- The properties of the stream `f` receives: `IOContext(s, context...)`
adds the pairs in order (each new binding shadows earlier ones), and
`IOContext(s, io)` copies `io`'s properties, `base/strings/io.jl:106-112`. -/
def ctxProps : Ctx → Props
  | .none => []
  | .pair kv => [kv]
  | .tuple kvs => kvs.reverse
  | .io p => p

/-- `sprint(f, args...; context, sizehint)`, `base/strings/io.jl:104-114`. `f`
is what the called function writes given the stream properties; the result
is `takestring!(s)`. The `sizehint` does not affect the text. -/
def sprint (f : Props → Shown) (context : Ctx) (_sizehint : Nat := 0) : R String :=
  let shown := f (ctxProps context)
  match shown.err with
  | some e => .error e
  | none => .ok (evText shown.evs)

/-- `repr(x; context=nothing) = sprint(show, x; context=context)`, `base/strings/io.jl:284`. -/
def repr (shw : Props → Shown) (context : Ctx) : R String := sprint shw context

/-- `limitrepr(x) = repr(x, context = :limit=>true)`, `base/strings/io.jl:286`. -/
def limitrepr (shw : Props → Shown) : R String := repr shw (.pair ("limit", "true"))

/-- Kinds of values `_str_sizehint` distinguishes. -/
inductive Arg where
  | float64 | float32
  | str (s : List Char)
  | char (c : Char)
  | u64 (n : Nat) | u32 (n : Nat)
  | i64 (n : Int) | i32 (n : Int)
  | other

/-- `ndigits(x)` in base 10 for integer `x` (`ndigits(0) == 1`). -/
def ndigits10 (n : Int) : Nat := (Nat.toDigits 10 n.natAbs).length

/-- `_str_sizehint(x)`, `base/strings/io.jl:116-132`. String sizes are UTF-8 byte
counts. -/
def strSizehint : Arg → Nat
  | .float64 => 20
  | .float32 => 12
  | .str s => (s.map Char.utf8Size).sum
  | .char c => c.utf8Size
  | .u64 n => ndigits10 n
  | .u32 n => ndigits10 n
  | .i64 n => ndigits10 n + (if n < 0 then 1 else 0)
  | .i32 n => ndigits10 n + (if n < 0 then 1 else 0)
  | .other => 8

/-- `print_to_string(xs...)`, `base/strings/io.jl:134-148`: `""` for no arguments,
else every argument printed into one buffer (sized by the sum of hints). -/
def printToString (xs : List (Arg × Shown)) : R String :=
  if xs.isEmpty then .ok "" else
  let _siz := (xs.map (fun x => strSizehint x.1)).sum
  let p := printMany (xs.map (·.2))
  match p.err with
  | some e => .error e
  | none => .ok (evText p.evs)

/-- `string_with_env(env, xs...)`, `base/strings/io.jl:150-165`: as
`print_to_string`, printing to `IOContext(s, env)`; `pr env x` is what `x` prints
under the properties `env`. -/
def stringWithEnv (env : Props) (xs : List (Arg × (Props → Shown))) : R String :=
  if xs.isEmpty then .ok "" else
  let p := printMany (xs.map (fun x => x.2 env))
  match p.err with
  | some e => .error e
  | none => .ok (evText p.evs)

/-- `string(xs...) = print_to_string(xs...)`, `base/strings/io.jl:186`. -/
def string (xs : List (Arg × Shown)) : R String := printToString xs

/-- `string(a::Symbol) = String(a)`, `base/strings/io.jl:188`: the symbol's name. -/
def stringSym (name : String) : String := name

/-- `print(io::IO, s::AbstractString) = for c in s; print(io, c); end`,
`base/strings/io.jl:192`: one write per character. -/
def printAbstractString (s : List Char) : List Ev := s.map (fun c => .write (String.singleton c))

/-- `write(io::IO, s::AbstractString)`, `base/strings/io.jl:193`: writes each
character and returns the total byte count (`write(io, c)` returns `ncodeunits(c)`). -/
def writeAbstractString (s : List Char) : List Ev × Nat :=
  (s.map (fun c => .write (String.singleton c)), (s.map Char.utf8Size).sum)

/-- `write(io, s::Union{String,SubString{String}})`, `base/strings/io.jl:242-245`:
one `unsafe_write` of `sizeof(s)` bytes; the return value is `sizeof(s)`.
`print(io, s::String)` (`:246`) is that write, returning `nothing`. -/
def writeString (s : String) : List Ev × Nat := ([.write s], s.utf8ByteSize)
def printString (s : String) : List Ev := (writeString s).1

/-- `show(io, s::AbstractString) = print_quoted(io, s)`,
`base/strings/io.jl:194`; `quoted` is the output of the separately modelled
`print_quoted` body. -/
def showAbstractString (quoted : String) : String := quoted

/-! ## `join` -/

/-- `join(io, iterator, delim, last)`, `base/strings/io.jl:330-345`, on the
printed forms of the items; returns what is written. -/
def joinLast (items : List String) (delim last : String) : List String :=
  let rec go (first : Bool) (prev : Option String) : List String → List String
    | [] => match prev with
      | some p => (if first then [] else [last]) ++ [p]
      | none => []
    | x :: xs => match prev with
      | some p => (if first then [] else [delim]) ++ [p] ++ go false (some x) xs
      | none => go first (some x) xs
  go true none items

/-- `join(io, iterator, delim="")`, `base/strings/io.jl:346-354`. -/
def join2 (items : List String) (delim : String := "") : List String :=
  let rec go (first : Bool) : List String → List String
    | [] => []
    | x :: xs => (if first then [] else [delim]) ++ [x] ++ go false xs
  go true items

/-- Element kinds `_join_preserve_annotations` distinguishes. -/
structure JoinInfo where
  /-- `isconcretetype(@default_eltype(iterator))` (generic method). -/
  concrete : Bool
  /-- `_isannotated` of the element type, or of any tuple element (tuple method). -/
  eltAnnotated : Bool
  argsAnnotated : Bool
  /-- `!isempty(io.annotations)` after joining into the `AnnotatedIOBuffer`. -/
  gotAnnotations : Bool

/-- The result kind of `_join_preserve_annotations`: a plain `String` (via
`sprint(join, ...)` or `String(take!(io.io))`) or an `AnnotatedString`. -/
inductive JoinKind where
  | plain | annotated
  deriving DecidableEq, Repr

/-- `_join_preserve_annotations(iterator, args...)`, `base/strings/io.jl:356-374`. -/
def joinKindGeneric (j : JoinInfo) : JoinKind :=
  if j.concrete && !j.eltAnnotated && !j.argsAnnotated then .plain
  else if j.concrete || j.gotAnnotations then .annotated else .plain

/-- `_join_preserve_annotations(iterator::Tuple, args...)`, `base/strings/io.jl:378-387`. -/
def joinKindTuple (j : JoinInfo) : JoinKind :=
  if !j.eltAnnotated && !j.argsAnnotated then .plain else .annotated

/-- `join(iterator)`, `join(iterator, delim)`, `join(iterator, delim, last)`,
`base/strings/io.jl:389-391`: the text (both result kinds hold the joined text). -/
def joinText (items : List String) (delim : Option String) (last : Option String) : String :=
  match delim, last with
  | none, _ => String.join (join2 items)
  | some d, none => String.join (join2 items d)
  | some d, some l => String.join (joinLast items d l)

/-! ## Escaping -/

/-- `escape_raw_string(io, str, delim)`, `base/strings/io.jl:663-693`: the
characters written and the returned `total` (backslashes added). -/
def escRaw (delim : Char) : List Char → Nat → Nat → List Char × Nat
  | [], escapes, total => (List.replicate escapes '\\', total + escapes)
  | c :: cs, escapes, total =>
    if c = '\\' then
      let (o, t) := escRaw delim cs (escapes + 1) total
      ('\\' :: o, t)
    else if c = delim then
      let (o, t) := escRaw delim cs 0 (total + (escapes + 1))
      (List.replicate (escapes + 1) '\\' ++ c :: o, t)
    else
      let (o, t) := escRaw delim cs 0 total
      (c :: o, t)

def escapeRawStringIO (str : List Char) (delim : Char := '"') : List Char × Nat := escRaw delim str 0 0

/-- `escape_raw_string(str, delim)`, `base/strings/io.jl:694-697`: `str` itself when
nothing needs escaping, else the escaped copy. -/
def escapeRawString (str : List Char) (delim : Char := '"') : List Char :=
  let total := (escapeRawStringIO str delim).2
  if total = 0 then str else (escapeRawStringIO str delim).1

/-- `@raw_str s` returns `s`, `base/strings/io.jl:643`. -/
def rawStr (s : List Char) : List Char := s

/-- `@b_str s = QuoteNode(codeunits(unescape_string(s)))`, `base/strings/io.jl:613-616`. -/
def bStr (s : JuliaLean.Strings.JStr) : JuliaLean.Strings.SJl (List UInt8) :=
  (fun t => t.bytes) <$> JuliaLean.Show.unescapeString s

/-! ## Multiline strings -/

/-- `div(count + tabwidth, tabwidth) * tabwidth`: the next tab stop. -/
def nextTab (count tabwidth : Nat) : Nat := (count + tabwidth) / tabwidth * tabwidth

/-- `indentation(str; tabwidth=8)`, `base/strings/io.jl:719-731`. -/
def indentation (tabwidth : Nat) : List Char → Nat → Nat × Bool
  | [], count => (count, true)
  | c :: cs, count =>
    if c = ' ' then indentation tabwidth cs (count + 1)
    else if c = '\t' then indentation tabwidth cs (nextTab count tabwidth)
    else (count, false)

/-- `for _ = 1:col-indent; print(buf, ' '); end`. -/
def spaces (col indent : Int) : List Char := List.replicate (col - indent).toNat ' '

/-- The loop of `unindent(str, indent; tabwidth=8)`, `base/strings/io.jl:755-801`,
with state `cutting` and `col`. -/
def unindentLoop (indent : Int) (tabwidth : Nat) : Bool → Nat → List Char → List Char
  | cutting, col, [] => if cutting then spaces col indent else []
  | true, col, ch :: cs =>
    if ch = ' ' then unindentLoop indent tabwidth true (col + 1) cs
    else if ch = '\t' then unindentLoop indent tabwidth true (nextTab col tabwidth) cs
    else if ch = '\n' then spaces col indent ++ '\n' :: unindentLoop indent tabwidth true 0 cs
    else spaces col indent ++ ch :: unindentLoop indent tabwidth false (col + 1) cs
  | false, col, ch :: cs =>
    if ch = '\t' then
      let upd := nextTab col tabwidth
      List.replicate (upd - col) ' ' ++ unindentLoop indent tabwidth false upd cs
    else if ch = '\n' then '\n' :: unindentLoop indent tabwidth true 0 cs
    else ch :: unindentLoop indent tabwidth false (col + 1) cs

/-- `unindent(str, indent; tabwidth=8)`, `base/strings/io.jl:749-803`. -/
def unindent (str : List Char) (indent : Int) (tabwidth : Nat := 8) : List Char :=
  if indent = 0 then str else unindentLoop indent tabwidth true 0 str

/-! ## Strings from characters -/

/-- `String(a::AbstractVector{Char})`, `base/strings/io.jl:805-816`: the
characters' encodings written one after another into a string of the summed
length. -/
def stringOfChars (a : List Char) : List Char × Nat := (a, (a.map Char.utf8Size).sum)

/-- `String(chars::AbstractVector{<:AbstractChar})`, `base/strings/io.jl:818-824`:
`print(io, c)` for each; `pr c` is the text `c` prints. -/
def stringOfAbstractChars {C} (pr : C → List Char) (chars : List C) : List Char :=
  chars.flatMap pr

/-- An `AnnotatedChar`: the character and its annotations. -/
structure AChar where
  char : Char
  annotations : List (String × String)

/-- `AnnotatedString(chars)`, `base/strings/io.jl:826-847`: the text and the
annotation regions `point:point` at each annotated character's first byte. -/
def annotatedStringOfChars (chars : List AChar) : List Char × List ((Nat × Nat) × (String × String)) :=
  let rec go (point : Nat) : List AChar → List ((Nat × Nat) × (String × String))
    | [] => []
    | c :: cs => c.annotations.map (fun a => ((point, point), a)) ++ go (point + c.char.utf8Size) cs
  (chars.map (·.char), go 1 chars)

/-! ## `show(io, ::MIME"text/plain", str; limit)` -/

/-- `skip_text(skip) = " ⋯ $skip $units ⋯ "`, `base/strings/io.jl:217`. -/
def skipText (units : String) (skip : Int) : String := " ⋯ " ++ toString skip ++ " " ++ units ++ " ⋯ "

/-- The inputs `show(io, MIME"text/plain"(), str; limit)` takes from the stream,
the string, and helpers in other files. -/
structure LimitIn where
  ioLimit : Bool
  displayCols : Int
  typeinfoNothing : Bool
  /-- `check_textwidth(str, limit)`. -/
  fits : Int → Bool
  /-- `ncodeunits(str)`; `codeunit(str) == UInt8`. -/
  ncu : Nat
  bytes : Bool
  /-- `string_truncate_boundaries(str, limit, max_replacement, Val(:center))`. -/
  boundaries : Int → String → Nat × Nat
  /-- `nextind(str, head)`. -/
  nextind : Nat → Nat
  /-- `textwidth(str[afterhead:prevind(str,tail)])`. -/
  midWidth : Nat → Nat → Nat

/-- The pieces printed: either `show(io, str)` in full, or the head, the styled
replacement, and the tail (as code-unit ranges). -/
inductive LimitOut where
  | full
  | elided (headEnd : Nat) (replacement : String) (tailStart : Nat)
  deriving DecidableEq, Repr

/-- `units` of `show(io, MIME"text/plain", str; limit)`, `base/strings/io.jl:216`. -/
def limitedUnits (x : LimitIn) : String := if x.bytes then "bytes" else "code units"

/-- `n = tail - afterhead`, the skipped code units, `base/strings/io.jl:226-227`. -/
def elidedCount (x : LimitIn) (head tail : Nat) : Int := (tail : Int) - x.nextind head

/-- `replacement = skip_text(n)`, `base/strings/io.jl:228`. -/
def elidedReplacement (x : LimitIn) (head tail : Nat) : String :=
  skipText (limitedUnits x) (elidedCount x head tail)

/-- The elision decision once the boundaries are known, `base/strings/io.jl:225-235`. -/
def limitedElide (x : LimitIn) (head tail : Nat) : LimitOut :=
  if 4 * ((elidedReplacement x head tail).utf8ByteSize : Int) ≤ elidedCount x head tail ∨
      (((elidedReplacement x head tail).utf8ByteSize : Int) ≤ elidedCount x head tail ∧
        ((elidedReplacement x head tail).utf8ByteSize : Int) ≤ x.midWidth (x.nextind head) tail) then
    .elided head (elidedReplacement x head tail) tail
  else .full

/-- The body of `show(io, ::MIME"text/plain", str; limit)` once a limit `l`
applies, `base/strings/io.jl:209-236`. -/
def limitedAt (x : LimitIn) (l : Int) : LimitOut :=
  if x.fits (max 0 (l - 2)) then .full else
  let bounds := x.boundaries (max 0 (l - 2)) (skipText (limitedUnits x) (x.ncu * 100 : Nat))
  limitedElide x bounds.1 bounds.2

/-- The limit in effect, `base/strings/io.jl:198-202`: the `limit` keyword, else
`max(20, displaysize(io)[2])` (times 7 without a `:typeinfo`) on a `:limit` stream. -/
def effectiveLimit (x : LimitIn) (limit : Option Int) : Option Int :=
  match limit with
  | some l => some l
  | none => if !x.ioLimit then none else
      let l := max 20 x.displayCols
      some (if x.typeinfoNothing then l * 7 else l)

/-- `show(io, ::MIME"text/plain", str; limit)`, `base/strings/io.jl:197-236`. -/
def showLimited (x : LimitIn) (limit : Option Int) : LimitOut :=
  match effectiveLimit x limit with
  | none => .full
  | some l => limitedAt x l

end JuliaLean.ShowCov.StringsIO
