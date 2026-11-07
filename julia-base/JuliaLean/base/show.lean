import JuliaLean.base.meta
import JuliaLean.base.strings.unicode
import JuliaLean.base.coreio
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.div
import JuliaLean.base.intfuncs
import JuliaLean.base.pair
import JuliaLean.base.abstractdict
import JuliaLean.base.dict
import JuliaLean.base.expr
import JuliaLean.base.io
import JuliaLean.base.runtime_internals
import JuliaLean.base.iterators
import JuliaLean.base.sort

/-!
# Model of `base/show.jl`

Typed model of the methods of `base/show.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform (`Int === Int64`). Each modelled method is a Lean definition whose
docstring carries the method's verbatim source; its body follows the Julia body call by call.
Methods without a model are kept as `UNTRANSLATED` source blocks with the reason.

* Output happens in an arbitrary monad `m` whose exceptions include `ShowError`. A stream
  argument is either a plain stream of type `Io` or an `IOContext` (`JIO`). The stream methods
  that show.jl calls (`write`, `lock`, `unlock`, a stream type's own `get` and `displaysize`) are
  selected by the stream's type and are the fields of `IOPrims`. `IOPrims.ofIO` builds them for a
  stream type that uses the `base/io.jl` fallbacks `lock(::IO)`/`unlock(::IO)` (model
  `JuliaLean.base.io`).
* Values of type `Any` stored in an `IOContext` have the abstract type `V`, Julia types the
  abstract type `Ty`. Type assertions (`x::Bool`, `x::Type`) and type-level operations are the
  fields of `AnyOps` and `TypeOps`.
* `show`, `print` and `isdelimited` of values of a user-extensible type are function parameters
  (Julia's dispatch is trusted). So are calls into files loaded after show.jl (`printstyled`,
  `nonmissingtype`, `stdout`), calls whose existing model uses another representation
  (`textwidth`, `sprint`, `match`), and calls into this file's untranslated methods
  (`show` of a type, `_show_default`).
* BitInteger arguments use the `base/intfuncs.jl` model of `string(n; base, pad)` and the
  `base/div.jl` model of `cld`.
* Loops whose termination depends on a user iterator are `partial_fixpoint` definitions; they
  require the monad to carry a `Lean.Order.CCPO` and `Lean.Order.MonoBind` structure, so a
  non-terminating Julia loop is the least element.
-/

/-!
Models for the remaining method bodies in `base/show.jl`.  Runtime reflection,
printing of an already-rendered Julia value, and calls into the parser are
explicit inputs.  The surrounding branch order and output construction mirror
the pinned Julia source.
-/


namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-- `show_sym(io, sym; allow_macroname = false)`, `base/show.jl:1867-1878`;
`print(io, sym)` writes the name's bytes. -/
def showSym (escapeRaw : JStr → List UInt8) (d : UData) (o : OpData) (s : JStr) : SJl (List UInt8) := do
  if ← isValidIdentifier d o s then pure s.bytes
  else pure (asc ['v', 'a', 'r', '"'] ++ escapeRaw s ++ [0x22])

/-- `quoted_syms`, `base/show.jl:1676`. -/
def quotedSyms : List (List UInt8) :=
  [[':'], [':', ':'], [':', '='], ['='], ['=', '='], ['=', '=', '='], ['=', '>']].map asc

/-- `show(io, s::Symbol) = show_unquoted_quote_expr(io, s, 0, 0)`, `base/show.jl:1628`,
symbol branch `:1937-1949`; `repr(String(sym))` is `print_quoted` (`base/strings/io.jl:194`). -/
def showSymbol (quoteString : UData → JStr → List UInt8) (d : UData) (o : OpData) (s : JStr) : SJl (List UInt8) :=
  if s.bytes ∈ quotedSyms then .ok (asc [':', '('] ++ s.bytes ++ asc [')'])
  else do
    let isid ← isidentifier d s
    if isid || (isOperatorSym o s && s.bytes ≠ asc ['\'']) then pure (asc [':'] ++ s.bytes)
    else pure (asc ['S', 'y', 'm', 'b', 'o', 'l', '('] ++ quoteString d s ++ asc [')'])

/-! ## Reading `var"..."` back -/

end JuliaLean.Show


/-!
# Printing Julia expressions: `print(io, ex::Expr)`

`printE quoteString escapeRaw d o e` models `string(e)` = `print(io, e)`
(`base/show.jl:1666`), which calls
`show_unquoted(IOContext(io, :unquote_fallback => false), e, 0, -1)` on `JE` values.

Modelling conventions:

* The `IOContext` flags are explicit Bool parameters: `uf` is
  `get(io, :unquote_fallback, true)` and `beg` is `get(io, beginsym, false)`.
  `quote_level` is threaded through as in Julia; it never reaches the output
  in the modelled branches.
* The result is `Except PErr (List UInt8)`: `.ok bytes` is the printed text,
  `.error (.jl e)` a Julia exception, and `.error .unknown` an input outside the
  modelled fragment. The unmodelled `show_unquoted` branches (comprehensions,
  `if`/`for`/`function` blocks, `quote`, `string`, `where`, `...`, `import`,
  `ncat`, macro calls other than `Core.@cmd`, ...) return `.unknown`, as do the
  encoding-only heads `globalref` and `nothing`.
* `Meta.parse("`x`")` is `Expr(:macrocall, GlobalRef(Core, Symbol("@cmd")),
  LineNumberNode, "x")`; `JE` encodes it as
  `node "macrocall" [node "globalref" [sym "Core", sym "@cmd"], node "nothing" [], str "x"]`
  (the encoding `JuliaLean.Show.Syntax` uses).
* Every function takes a fuel argument that decreases on each call, so the
  definitions reduce in the kernel; `printE` passes `16 * e.size + 16`, more
  than any modelled path uses (at most 8 calls per tree level).
-/

namespace JuliaLean.Show

open JuliaLean.Strings

/-- Why the printer model produced no text: a Julia exception, or an input
outside the modelled fragment. -/
inductive PErr where
  | jl (e : SErr)
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- Printer results. -/
abbrev PO := Except PErr (List UInt8)

instance instDecidableEqExceptPErr {α} [DecidableEq α] : DecidableEq (Except PErr α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

/-- UTF-8 encoding of a Unicode scalar value. -/
def utf8Encode (c : Char) : List UInt8 :=
  let n := c.val.toNat
  if n < 0x80 then [n.toUInt8]
  else if n < 0x800 then [(0xC0 + n / 64).toUInt8, (0x80 + n % 64).toUInt8]
  else if n < 0x10000 then
    [(0xE0 + n / 4096).toUInt8, (0x80 + n / 64 % 64).toUInt8, (0x80 + n % 64).toUInt8]
  else
    [(0xF0 + n / 262144).toUInt8, (0x80 + n / 4096 % 64).toUInt8, (0x80 + n / 64 % 64).toUInt8,
     (0x80 + n % 64).toUInt8]

/-- The UTF-8 bytes of a Lean string (a Julia `Symbol` name or `String`). -/
def u8 (s : String) : List UInt8 := s.toList.flatMap utf8Encode

/-- The Julia `String` holding the bytes of `s`; Julia cannot allocate `2^62`
bytes, so longer names leave the model. -/
def jstrOf (s : String) : Except PErr JStr :=
  let b := u8 s
  if h : b.length < 2 ^ 62 then .ok ⟨b, h⟩ else .error .unknown

/-- Lift a string-model result. -/
def liftS {α} (x : SJl α) : Except PErr α :=
  match x with
  | .ok a => .ok a
  | .error e => .error (.jl e)

/-- `Meta.isidentifier(s::Symbol)`, `base/meta.jl:48-56`. -/
def isidentS (d : UData) (s : String) : Except PErr Bool := do
  liftS (isidentifier d (← jstrOf s))

/-- `Meta.is_valid_identifier(sym)`, `base/meta.jl:128-134`. -/
def isValidIdentS (d : UData) (o : OpData) (s : String) : Except PErr Bool := do
  liftS (isValidIdentifier d o (← jstrOf s))

/-- `show_sym(io, sym; allow_macroname=false)`, `base/show.jl:1867-1876`. -/
def showSymS (escapeRaw : JStr → List UInt8) (d : UData) (o : OpData) (s : String) : PO := do
  liftS (showSym escapeRaw d o (← jstrOf s))

/-- `show(io, s::String)` = `print_quoted(io, s)`, `base/strings/io.jl:194`. -/
def showStrS (quoteString : UData → JStr → List UInt8) (d : UData) (s : String) : PO := do
  pure (quoteString d (← jstrOf s))

/-- `Meta.ispostfixoperator(s)`, `base/meta.jl:117-120`: `s` starts with `'`
and every later character is an operator suffix character. -/
def ispostfixoperator (o : OpData) (s : String) : Bool :=
  match s.toList with
  | '\'' :: rest => rest.all (fun c => o.opSuffix c.val)
  | _ => false

/-- `Meta.isoperator(s) = _isoperator(s) || ispostfixoperator(s)`, `base/meta.jl:73`. -/
def isoperator (o : OpData) (s : String) : Bool := o.isOp s || ispostfixoperator o s

/-- `quoted_syms`, `base/show.jl:1676`. -/
def quotedSymNames : List String := [":", "::", ":=", "=", "==", "===", "=>"]

/-- `uni_syms`, `base/show.jl:1677`. -/
def uniSyms : List String := ["::", "<:", ">:"]

/-- `uni_ops`, `base/show.jl:1678`. -/
def uniOps : List String := ["+", "-", "!", "¬", "~", "<:", ">:", "√", "∛", "∜", "∓", "±"]

/-- `expr_infix_wide`, `base/show.jl:1679-1683`. -/
def exprInfixWide : List String :=
  ["=", "+=", "-=", "*=", "/=", "\\=", "^=", "&=", "|=", "÷=", "%=", ">>>=", ">>=", "<<=",
   ".=", ".+=", ".-=", ".*=", "./=", ".\\=", ".^=", ".&=", ".|=", ".÷=", ".%=", ".>>>=", ".>>=", ".<<=",
   "&&", "||", "<:", "$=", "⊻=", ">:", "-->",
   ":=", "≔", "⩴", "≕"]

/-- `expr_infix`, `base/show.jl:1684`. -/
def exprInfix : List String := [":", "->", "::"]

/-- `expr_infix_any = union(expr_infix, expr_infix_wide)`, `base/show.jl:1685`. -/
def exprInfixAny : List String := exprInfix ++ exprInfixWide

/-- `expr_calls`, `base/show.jl:1686-1687`. -/
def exprCalls : String → Option (String × String)
  | "call" => some ("(", ")")
  | "calldecl" => some ("(", ")")
  | "ref" => some ("[", "]")
  | "curly" => some ("{", "}")
  | "." => some ("(", ")")
  | _ => none

/-- `expr_parens`, `base/show.jl:1688-1691`. -/
def exprParens : String → Option (String × String)
  | "tuple" => some ("(", ")")
  | "vcat" => some ("[", "]")
  | "hcat" => some ("[", "]")
  | "row" => some ("[", "]")
  | "vect" => some ("[", "]")
  | "ncat" => some ("[", "]")
  | "nrow" => some ("[", "]")
  | "braces" => some ("{", "}")
  | "bracescat" => some ("{", "}")
  | _ => none

/-- `is_expr(ex, head)`. -/
def isExpr (e : JE) (h : String) : Bool :=
  match e with
  | .node h' _ => h' == h
  | _ => false

/-- `is_quoted(ex)`, `base/show.jl:1750-1752`. -/
def isQuoted : JE → Bool
  | .qn _ => true
  | .node "quote" [_] => true
  | .node "inert" [_] => true
  | _ => false

/-- `unquoted(ex)`, `base/show.jl:1754-1755` (only applied to quoted values). -/
def unquoted : JE → JE
  | .qn v => v
  | .node _ (a :: _) => a
  | e => e

/-- `show(io, n::Int64)` = `string(n)`, `base/show.jl:1425`. -/
def showInt (v : Int) : List UInt8 :=
  let digits (n : Nat) : List UInt8 := (Nat.toDigits 10 n).map (fun c => c.toNat.toUInt8)
  if v < 0 then 45 :: digits v.natAbs else digits v.natAbs

/-- `show(io, x::Float64)` for a literal whose shortest representation is
`±ip.fp` (`JE.flt`, `base/ryu/Ryu.jl`). -/
def showFlt (neg : Bool) (ip : Nat) (fp : List Nat) : List UInt8 :=
  (if neg then [45] else []) ++ (Nat.toDigits 10 ip).map (fun c => c.toNat.toUInt8) ++
    46 :: fp.map (fun k => (48 + k).toUInt8)

/-- `item isa Real && item < 0` for literals (`base/show.jl:1811`); `-0.0 < 0` is false. -/
def isNegReal : JE → Bool
  | .int v => decide (v < 0)
  | .flt neg ip fp => neg && !(ip == 0 && fp.all (· == 0))
  | _ => false

/-- `is_core_macro(arg, :var"@cmd")`, `base/show.jl:2035`, in the `JE` encoding of
`GlobalRef(Core, Symbol("@cmd"))`. -/
def isCoreCmd : JE → Bool
  | .node "globalref" [.sym "Core", .sym "@cmd"] => true
  | _ => false

/-- Heads whose `show_unquoted` branch (`base/show.jl:2233-2600`) the model does
not mirror, plus the encoding-only heads `globalref` and `nothing`. -/
def unmodelledHeads : List String :=
  ["new", "splatnew", "typed_comprehension", "comprehension", "generator", "flatten", "filter",
   "comparison", "function", "macro", "do", "for", "while", "if", "elseif", "let", "module",
   "struct", "primitive", "abstract", "return", "...", "break", "continue", "const", "local",
   "global", "export", "public", "macroname", "line", "try", "quote", "gotoifnot", "string",
   "null", "where", "import", "using", "as", "meta", "toplevel", "globalref", "nothing"]

/-- `" "^n`. -/
def spaces (n : Nat) : List UInt8 := List.replicate n 32

mutual
/-- Number of constructors in a tree; bounds the printer's recursion depth. -/
def JE.size : JE → Nat
  | .qn v => v.size + 1
  | .node _ args => JE.sizeList args + 1
  | _ => 1
/-- Sum of `JE.size` over a list. -/
def JE.sizeList : List JE → Nat
  | [] => 0
  | a :: as => a.size + JE.sizeList as
end

section
variable (quoteString : UData → JStr → List UInt8) (escapeRaw : JStr → List UInt8)
variable (d : UData) (o : OpData)

mutual

/-- `show_unquoted(io, ex, indent, prec, quote_level)` on the leaf types and
dispatch to the `Expr` method: `Symbol` (`base/show.jl:1895`, `show_sym`),
`Int64`/`Float64`/`String` (`base/show.jl:1670-1671` = `show(io, ex)`),
`QuoteNode` (`base/show.jl:1924-1935`) and `Expr` (`base/show.jl:2054`). -/
def showUnquoted : Nat → (uf beg : Bool) → JE → (indent : Nat) → (prec ql : Int) → PO
  | 0, _, _, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, e, indent, prec, ql =>
    match e with
    | .sym s => showSymS escapeRaw d o s
    | .int v => .ok (showInt v)
    | .flt ng ip fp => .ok (showFlt ng ip fp)
    | .str s => showStrS quoteString d s
    | .qn v =>
      match v with
      | .sym _ => showQuoteExpr n uf beg v indent 0
      | _ => do
        let x ← showVal n uf beg v
        pure (u8 "$(QuoteNode(" ++ x ++ u8 "))")
    | .node h args => showExpr n uf beg h args indent prec ql

/-- `show(io, x)` (`base/show.jl:1628`, `:1667`, `:1425`, `base/strings/io.jl:194`):
`Symbol` -> `show_unquoted_quote_expr(io, s, 0, 0)`; `Expr`/`QuoteNode` ->
`show_unquoted_quote_expr(IOContext(io, :unquote_fallback => true), ex, 0, -1)`. -/
def showVal : Nat → (uf beg : Bool) → JE → PO
  | 0, _, _, _ => .error .unknown
  | n + 1, uf, beg, e =>
    match e with
    | .sym _ => showQuoteExpr n uf beg e 0 0
    | .int v => .ok (showInt v)
    | .flt ng ip fp => .ok (showFlt ng ip fp)
    | .str s => showStrS quoteString d s
    | .qn _ => showQuoteExpr n true beg e 0 (-1)
    | .node _ _ => showQuoteExpr n true beg e 0 (-1)

/-- `show_unquoted_quote_expr(io, value, indent, quote_level)`, `base/show.jl:1937-1960`. -/
def showQuoteExpr : Nat → (uf beg : Bool) → JE → (indent : Nat) → (ql : Int) → PO
  | 0, _, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, value, indent, ql =>
    match value with
    | .sym s =>
      if quotedSymNames.contains s then .ok (u8 ":(" ++ u8 s ++ u8 ")")
      else do
        let idf ← isidentS d s
        if idf || (o.isOp s && s != "'") then pure (u8 ":" ++ u8 s)
        else pure (u8 "Symbol(" ++ (← showStrS quoteString d s) ++ u8 ")")
    | .node "block" args => do
      let b ← showBlock n uf false "quote" [] (.node "block" args) indent ql
      pure (b ++ u8 "end")
    | _ => do
      let x ← showUnquoted n uf beg value (indent + 2) (-1) ql
      pure (u8 ":(" ++ x ++ u8 ")")

/-- `show_block(io, head, args::Vector, body, indent, quote_level)`,
`base/show.jl:1771-1789`. -/
def showBlock : Nat → (uf beg : Bool) → (head : String) → (args : List JE) → (body : JE) →
    (indent : Nat) → (ql : Int) → PO
  | 0, _, _, _, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, head, args, body, indent, ql => do
    let a ← if args.isEmpty then pure []
      else do
        let l ← showList n uf beg args (if head == "elseif" then u8 " " else u8 ", ") indent 0 ql false false
        pure (32 :: l)
    let ind := if head == "module" || head == "baremodule" then indent else indent + 4
    let exs := match body with
      | .node "block" bargs => bargs
      | .node "quote" bargs => bargs
      | _ => [body]
    let parts ← exs.mapM (fun ex => do
      let x ← showUnquoted n uf beg ex ind (-1) ql
      pure (10 :: spaces ind ++ x))
    pure (u8 head ++ a ++ parts.flatten ++ 10 :: spaces indent)

/-- `show_list(io, items, sep, indent, prec, quote_level, enclose_operators, kw)`,
`base/show.jl:1800-1826`. -/
def showList : Nat → (uf beg : Bool) → (items : List JE) → (sep : List UInt8) → (indent : Nat) →
    (prec ql : Int) → (encl kw : Bool) → PO
  | 0, _, _, _, _, _, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, items, sep, indent0, prec, ql, encl, kw =>
    if items.isEmpty then .ok [] else do
    let indent := indent0 + 4
    let parts ← items.zipIdx.mapM (fun (item, i) => do
      let first := i == 0
      let pre := if first then [] else sep
      let p1 ← if !isQuoted item && first && decide (prec ≥ (o.prec "^" : Int)) then
          match item with
          | .node "call" [] => .error (.jl (.jl .boundsError))
          | .node "call" (.sym c :: _) =>
            pure (uniOps.contains c || isNegReal item)
          | _ => pure (isNegReal item)
        else pure false
      let p2 ← match item with
        | .sym s => if encl && isoperator o s then isValidIdentS d o s else pure false
        | _ => pure false
      let parens := p1 || p2
      let iprec : Int := if parens then 0 else prec
      let body ← match kw, item with
        | true, .node "kw" [a, b] => showUnquoted n uf beg (.node "=" [a, b]) indent iprec ql
        | true, .node "=" [a, b] => fallback n uf beg "=" [a, b]
        | _, _ => showUnquoted n uf beg item indent iprec ql
      pure (pre ++ (if parens then [40] else []) ++ body ++ (if parens then [41] else [])))
    pure parts.flatten

/-- `show_enclosed_list(io, op, items, sep, cl, indent, prec, quote_level, encl_ops, kw)`,
`base/show.jl:1828-1832`. -/
def showEnclosedList : Nat → (uf beg : Bool) → (op : String) → (items : List JE) →
    (sep : List UInt8) → (cl : String) → (indent : Nat) → (prec ql : Int) → (encl kw : Bool) → PO
  | 0, _, _, _, _, _, _, _, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, op, items, sep, cl, indent, prec, ql, encl, kw => do
    let l ← showList n uf beg items sep indent prec ql encl kw
    pure (u8 op ++ l ++ u8 cl)

/-- `show_call(io, head, func, func_args, indent, quote_level, kw)`, `base/show.jl:1837-1862`. -/
def showCall : Nat → (uf beg : Bool) → (head : String) → (func : JE) → (fargs : List JE) →
    (indent : Nat) → (ql : Int) → (kw : Bool) → PO
  | 0, _, _, _, _, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, head, func, fargs, indent, ql, kw => do
    let (op, cl) := (exprCalls head).getD ("(", ")")
    let bare ← match func with
      | .sym s =>
        if s != ":" && !(head == "." && isoperator o s) then pure true
        else do pure !(← isValidIdentS d o s)
      | .node fh _ => pure (fh == "." || fh == "curly" || fh == "macroname")
      | _ => pure false
    let f ← showUnquoted n uf beg func indent 0 ql
    let fs := if bare then f else [40] ++ f ++ [41]
    let dot := if head == "." then u8 "." else []
    match fargs with
    | .node "parameters" pargs :: rest => do
      let a ← showList n uf beg rest (u8 ", ") indent 0 ql false kw
      let p ← showList n uf beg pargs (u8 ", ") indent 0 ql false kw
      pure (fs ++ dot ++ u8 op ++ a ++ u8 "; " ++ p ++ u8 cl)
    | _ => do
      let l ← showEnclosedList n uf beg op fargs (u8 ", ") cl indent 0 ql false kw
      pure (fs ++ dot ++ l)

/-- `show_unquoted_expr_fallback(io, ex)`, `base/show.jl:2043-2051`. -/
def fallback : Nat → (uf beg : Bool) → (head : String) → (args : List JE) → PO
  | 0, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, head, args => do
    let h ← showVal n uf beg (.sym head)
    let parts ← args.mapM (fun a => do
      let x ← showVal n uf beg a
      pure (u8 ", " ++ x))
    pure (u8 "$(Expr(" ++ h ++ parts.flatten ++ u8 "))")

/-- `show_unquoted(io, ex::Expr, indent, prec, quote_level)`, `base/show.jl:2054-2606`,
for the modelled branches (module docstring). -/
def showExpr : Nat → (uf beg : Bool) → (head : String) → (args : List JE) → (indent : Nat) →
    (prec ql : Int) → PO
  | 0, _, _, _, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, head, args, indent, prec, ql =>
    let nargs := args.length
    -- dot (i.e. "x.y"), but not compact broadcast exps (:2058-2085)
    if head == "." && (nargs != 2 || !isExpr (args.getD 1 default) "tuple") then
      match args with
      | [.sym s] =>
        if isoperator o s then .ok (u8 "(." ++ u8 s ++ u8 ")") else fallback n uf beg head args
      | [item, q] =>
        if isQuoted q then do
          let field := unquoted q
          let idf ← match item with
            | .sym s => isidentS d s
            | _ => pure false
          let parens := !isQuoted item && !idf && !isExpr item "."
          let x ← showUnquoted n uf beg item indent 0 ql
          let (fparens, quoted) := match field with
            | .sym f => (quotedSymNames.contains f, quotedSymNames.contains f || isoperator o f)
            | _ => (true, true)
          let y ← showUnquoted n uf beg field indent 0 ql
          pure ((if parens then [40] else []) ++ x ++ (if parens then [41] else []) ++ [46] ++
            (if quoted then [58] else []) ++ (if fparens then [40] else []) ++ y ++
            (if fparens then [41] else []))
        else fallback n uf beg head args
      | _ => fallback n uf beg head args
    -- infix (i.e. "x <: y" or "x = y") (:2088-2098)
    else if exprInfixAny.contains head && nargs == 2 then
      let funcPrec : Int := o.prec head
      let sep := if exprInfixWide.contains head then u8 " " ++ u8 head ++ u8 " " else u8 head
      let args := match head, args with
        | "->", [.node "..." a, b] => [.node "tuple" [.node "..." a], b]
        | _, _ => args
      if funcPrec ≤ prec then showEnclosedList n uf beg "(" args sep ")" indent funcPrec ql true false
      else showList n uf beg args sep indent funcPrec ql true false
    -- tuple (:2100-2115)
    else if head == "tuple" then
      match args with
      | .node "parameters" pargs :: rest => do
        let a ← showList n uf beg rest (u8 ", ") indent 0 ql false false
        let p ← showList n uf beg pargs (u8 ", ") indent 0 ql false true
        pure (u8 "(" ++ a ++ (if nargs == 2 then u8 "," else []) ++ u8 ";" ++
          (if pargs.isEmpty then [] else u8 " ") ++ p ++ u8 ")")
      | _ => do
        let a ← showList n uf beg args (u8 ", ") indent 0 ql false false
        pure (u8 "(" ++ a ++ (if nargs == 1 then u8 "," else []) ++ u8 ")")
    -- list-like forms, e.g. "[1, 2, 3]" (:2118-2150)
    else if (exprParens head).isSome || head == "typed_vcat" || head == "typed_hcat" ||
        head == "typed_ncat" then
      if head == "ncat" || head == "nrow" || head == "typed_ncat" then .error .unknown
      else do
        let typed := head == "typed_vcat" || head == "typed_hcat"
        let t ← if typed then
            match args with
            | [] => .error (.jl (.jl .boundsError))
            | a :: _ => showUnquoted n uf beg a indent prec ql
          else pure []
        let head := if head == "typed_vcat" then "vcat" else if head == "typed_hcat" then "hcat" else head
        let args := if typed then args.drop 1 else args
        let nargs := args.length
        let (op, cl) := (exprParens head).getD ("[", "]")
        let sep := if head == "vcat" || head == "bracescat" then u8 "; "
          else if head == "hcat" || head == "row" then u8 " " else u8 ", "
        let l ← showList n uf beg args sep indent 0 ql false false
        pure (t ++ (if head != "row" then u8 op else []) ++ l ++
          (if nargs ≤ 1 && head == "vcat" then u8 ";" else []) ++
          (if head != "row" then u8 cl else []))
    -- transpose (:2153-2164)
    else if (head == "'" && nargs == 1) ||
        (head == "call" && nargs == 2 &&
          (match args with
           | .sym s :: _ => ispostfixoperator o s && s != "'"
           | _ => false)) then
      let (op, arg1) := if head == "'" then ("'", args.getD 0 default)
        else (match args.getD 0 default with | .sym s => s | _ => "", args.getD 1 default)
      let encl := match arg1 with
        | .node _ _ => true
        | .sym s => isoperator o s
        | _ => false
      if encl then do
        let x ← showEnclosedList n uf beg "(" [arg1] (u8 ", ") ")" indent 0 0 false false
        pure (x ++ u8 op)
      else do
        let x ← showUnquoted n uf beg arg1 indent 0 ql
        pure (x ++ u8 op)
    -- function call (:2167-2230)
    else if head == "call" && nargs ≥ 1 then
      let func := args.getD 0 default
      let funcPrec : Int := match func with
        | .sym s => o.prec s
        | _ => 0
      let fargs := args.drop 1
      let hasKw := fargs.any (isExpr · "kw") ||
        (match fargs with | a :: _ => isExpr a "parameters" | [] => false)
      if hasKw then showCall n uf beg head func fargs indent ql true
      else
      -- scalar multiplication (i.e. "100x"), :2181-2186
      let scalar : Except PErr Bool := match func, fargs with
        | .sym "*", [x, .sym s] =>
          match x with
          | .int _ | .flt _ _ _ =>
            match s.toList with
            | [] => .error (.jl (.jl .boundsError))
            | c :: _ =>
              let excl := ['e', 'E', 'f'] ++ (if x == .int 0 then ['b', 'o', 'x'] else [])
              .ok !(excl.contains c)
          | _ => .ok false
        | _, _ => .ok false
      match scalar with
      | .error e => .error e
      | .ok true =>
        if funcPrec ≤ prec then showEnclosedList n uf beg "(" fargs [] ")" indent funcPrec ql false false
        else showList n uf beg fargs [] indent funcPrec ql false false
      | .ok false =>
      -- unary operator (i.e. "!z"), :2194-2201
      match func, fargs with
      | .sym f, [arg1] =>
        if uniOps.contains f then do
          let fs ← showUnquoted n uf beg func indent 0 ql
          let encl ← match arg1 with
            | .node _ _ => pure true
            | .sym a => if isoperator o a then isValidIdentS d o a else pure false
            | _ => pure false
          let x ← if encl then showEnclosedList n uf beg "(" fargs (u8 ", ") ")" indent funcPrec 0 false false
            else showUnquoted n uf beg arg1 indent funcPrec ql
          pure (fs ++ x)
        else showBinaryOrCall n uf beg head func funcPrec fargs indent prec ql
      | _, _ => showBinaryOrCall n uf beg head func funcPrec fargs indent prec ql
    -- type annotation (i.e. "::Int"), :2354-2356
    else if uniSyms.contains head && nargs == 1 then do
      let x ← showUnquoted n uf beg (args.getD 0 default) indent 0 ql
      pure (u8 head ++ x)
    else if unmodelledHeads.contains head then .error .unknown
    -- other call-like expressions ("A[1,2]", "T{X,Y}", "f.(X,Y)"), :2237-2239
    else if (exprCalls head).isSome && nargs ≥ 1 then
      let funcargslike := if head == "." then
          (match args.getD 1 default with | .node _ a => a | _ => [])
        else args.drop 1
      showCall n uf (if head == "ref" then true else beg) head (args.getD 0 default) funcargslike
        indent ql (head != "curly")
    -- `a b c`, :2380-2384
    else if head == "macrocall" && nargs ≥ 2 then
      if isCoreCmd (args.getD 0 default) then
        match (args[2]? : Option JE) with
        | none => .error (.jl (.jl .boundsError))
        | some (.str s) => .ok (u8 "`" ++ u8 s ++ u8 "`")
        | some _ => .error .unknown
      else .error .unknown
    -- block, :2469-2489
    else if head == "block" then
      if beg then do
        -- every `JE` argument is an expression (no LineNumberNode), so `seen_expr`
        -- is true after the first argument and `printed_semi` iff `nargs ≥ 2`
        let ind := indent + 4
        let parts ← args.zipIdx.mapM (fun (arg, i) => do
          let x ← showUnquoted n uf beg arg ind (-1) ql
          pure ((if i > 0 then u8 ";" ++ 10 :: spaces ind else []) ++ x))
        pure (u8 "(" ++ parts.flatten ++
          (if nargs ≥ 2 then u8 ")" else if nargs == 1 then u8 ";)" else u8 ";;)"))
      else do
        let b ← showBlock n uf beg "begin" [] (.node head args) indent ql
        pure (b ++ u8 "end")
    -- :2536-2550
    else if (head == "&" || head == "$") && nargs == 1 then
      let ql := if head == "$" then ql - 1 else ql
      if head == "$" && uf then fallback n uf beg head args
      else do
        let a1 := args.getD 0 default
        let parens := match a1 with
          | .node ah _ => !(["tuple", "$", "vect", "braces"].contains ah)
          | .sym s => isoperator o s
          | _ => false
        let x ← showUnquoted n uf beg a1 0 0 ql
        pure (u8 head ++ (if parens then u8 "(" else []) ++ x ++ (if parens then u8 ")" else []))
    else fallback n uf beg head args

/-- The binary-operator and normal-call cases of the `call` branch,
`base/show.jl:2204-2229`. -/
def showBinaryOrCall : Nat → (uf beg : Bool) → (head : String) → (func : JE) → (funcPrec : Int) →
    (fargs : List JE) → (indent : Nat) → (prec ql : Int) → PO
  | 0, _, _, _, _, _, _, _, _, _ => .error .unknown
  | n + 1, uf, beg, head, func, funcPrec, fargs, indent, prec, ql =>
    match func with
    | .sym f =>
      if funcPrec > 0 then
        let na := fargs.length
        if (na == 2 || (na > 2 && ["+", "++", "*"].contains f) || (na == 3 && f == ":")) &&
            fargs.all (fun a => !isExpr a "...") then
          let sep := if f == ":" then u8 f else u8 " " ++ u8 f ++ u8 " "
          if funcPrec ≤ prec then showEnclosedList n uf beg "(" fargs sep ")" indent funcPrec ql true false
          else showList n uf beg fargs sep indent funcPrec ql true false
        else if na == 1 then do
          let fs ← showUnquoted n uf beg func indent 0 ql
          let l ← showEnclosedList n uf beg "(" fargs (u8 ", ") ")" indent 0 ql false false
          pure (u8 "(" ++ fs ++ u8 ")" ++ l)
        else showCall n uf beg head func fargs indent ql true
      else showCall n uf beg head func fargs indent ql true
    | _ => showCall n uf beg head func fargs indent ql true

end

end

/-- `string(ex)` = `print(io, ex)`: for `Expr`/`QuoteNode`,
`show_unquoted(IOContext(io, :unquote_fallback => false), ex, 0, -1)`
(`base/show.jl:1666`); a `Symbol` prints its name, an `Int64`/`Float64` its
`string`, and a `String` its bytes. -/
def printE (quoteString : UData → JStr → List UInt8) (escapeRaw : JStr → List UInt8) (d : UData) (o : OpData) (e : JE) : PO :=
  match e with
  | .sym s => .ok (u8 s)
  | .int v => .ok (showInt v)
  | .flt ng ip fp => .ok (showFlt ng ip fp)
  | .str s => .ok (u8 s)
  | _ => showUnquoted quoteString escapeRaw d o (16 * e.size + 16) false false e 0 (-1) 0

end JuliaLean.Show

namespace JuliaLean.ShowCov.Remaining

open JuliaLean.Show

abbrev Trace := List String

def traceText (xs : Trace) : String := String.join xs

/-! ## Function and container display -/

structure SelfInput where
  typeNameIsSingleton : Bool
  backdatedConstant : Bool
  restrictionTypeIsSelf : Bool
  globalDefined : Bool
  globalTypeIsSelf : Bool
  deriving Repr, DecidableEq

/-- Mirrors `_isself` at `base/show.jl:41-53`. -/
def isSelf (x : SelfInput) : Bool :=
  if x.typeNameIsSingleton then false
  else if x.backdatedConstant then x.restrictionTypeIsSelf
  else x.globalDefined && x.globalTypeIsSelf

inductive FunctionKind where
  | intrinsic (id : Int)
  | builtin
  | generic
  deriving Repr, DecidableEq

structure FunctionView where
  kind : FunctionKind
  name : String
  typeText : String
  methodCount : Nat
  self : SelfInput
  deriving Repr, DecidableEq

/-- Mirrors `show(::MIME"text/plain", ::Function)` at `base/show.jl:55-73`.
`compactText` is the result of the compact `show(io, f)` call. -/
def showFunctionPlain (compact : Bool) (compactText : String) (f : FunctionView) : String :=
  if compact then compactText
  else match f.kind with
    | .intrinsic id => f.name ++ " (intrinsic function #" ++ toString id ++ ")"
    | .builtin => f.name ++ " (built-in function)"
    | .generic =>
      let n := f.methodCount
      let methodWord := if n = 1 then "method" else "methods"
      let shownName := if isSelf f.self || f.name.contains '#' then f.name else "(::" ++ f.typeText ++ ")"
      let what := if shownName.startsWith "@" then "macro" else "generic function"
      shownName ++ " (" ++ what ++ " with " ++ toString n ++ " " ++ methodWord ++ ")"

structure IterEntry where
  full : String
  limited : String
  deriving Repr, DecidableEq

/-- Body-level model of the KeySet/ValueIterator text display at
`base/show.jl:137-166`. -/
def showKeyValueIter (summary forward label : String) (entries : List IterEntry)
    (compact limit : Bool) (rows : Nat) : String :=
  if entries.isEmpty && compact then forward
  else if entries.isEmpty then summary
  else if limit && rows < 2 then summary ++ ". " ++ label ++ ": …"
  else
    let room := if limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map (fun e => "\n  " ++ if limit then e.limited else e.full)
    let ellipsis := if limit && room < entries.length then ["\n  ⋮"] else []
    summary ++ ". " ++ label ++ ":" ++ String.join (lines ++ ellipsis)

structure DictEntry where
  key : String
  value : String
  alignedLimitedKey : String
  limitedValue : String
  deriving Repr, DecidableEq

/-- Body-level model of `show(::MIME"text/plain", ::AbstractDict)` at
`base/show.jl:168-233`.  The four strings are the results of the source's
`sprint` and truncation calls. -/
def showDictPlain (summary forward : String) (entries : List DictEntry)
    (hasLength circular limit : Bool) (rows : Nat) (ellipsisKey : String := "⋮") : String :=
  if entries.isEmpty || !hasLength then forward
  else if circular then summary ++ ":"
  else if limit && rows < 2 then summary ++ ": …"
  else
    let room := if limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map fun e =>
      "\n  " ++ (if limit then e.alignedLimitedKey else e.key) ++ " => " ++
        (if limit then e.limitedValue else e.value)
    let ellipsis := if limit && room < entries.length then ["\n  " ++ ellipsisKey ++ " => ⋮"] else []
    summary ++ ":" ++ String.join (lines ++ ellipsis)

/-- Body-level model of `show(::MIME"text/plain", ::AbstractSet)` at
`base/show.jl:241-276`. -/
def showSetPlain (summary forward : String) (entries : List IterEntry)
    (circular limit : Bool) (rows : Nat) : String :=
  if entries.isEmpty then forward
  else if circular then summary ++ ":"
  else if limit && rows < 2 then summary ++ ": …"
  else
    let room := if limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map (fun e => "\n  " ++ if limit then e.limited else e.full)
    let ellipsis := if limit && room < entries.length then ["\n  ⋮ "] else []
    summary ++ ":" ++ String.join (lines ++ ellipsis)

inductive ActiveRepl where
  | absent
  | present (moduleName : String)
  deriving Repr, DecidableEq

/-- Mirrors `active_module()` at `base/show.jl:570-578`. -/
def activeModule (pure : Bool) (active : ActiveRepl) : R String :=
  if pure then .error (.errorException "active_module() should not be called from a pure context")
  else match active with
    | .absent => .ok "Main"
    | .present m => .ok m

structure FunctionNameView where
  nameIsSingleton : Bool
  singletonName : String
  moduleName : String
  compact : Bool
  globallyBound : Bool
  visible : Bool
  sameModule : Bool
  deriving Repr, DecidableEq

/-- Mirrors `show_function` at `base/show.jl:583-601`; `fallback` is the
rendered result of the chosen fallback function. -/
def showFunction (f : FunctionNameView) (fallback : String) : String :=
  if f.nameIsSingleton then fallback
  else if f.compact then f.singletonName
  else if f.globallyBound then
    (if f.visible || f.sameModule then "" else f.moduleName ++ ".") ++ f.singletonName
  else fallback

/-- Mirrors `show(::Core.IntrinsicFunction)` at `base/show.jl:606-611`. -/
def showIntrinsic (compact : Bool) (name : String) : String :=
  (if compact then "" else "Core.Intrinsics.") ++ name

/-- Mirrors `print(::Core.IntrinsicFunction)` at `base/show.jl:613`. -/
def printIntrinsic (name : String) : String := name

/-! ## Type analysis and printing -/

/-- Mirrors `print_without_params` at `base/show.jl:617-620`. -/
def printWithoutParams (unwrappedIsData wrapperIsOriginal : Bool) : Bool :=
  unwrappedIsData && wrapperIsOriginal

structure TVarBinding where
  unionallKey : Bool
  isTypeVar : Bool
  name : String
  occurs : Bool
  deriving Repr, DecidableEq

/-- Mirrors the IOContext overload of `io_has_tvar_name` at
`base/show.jl:622-629`. -/
def ioHasTvarName (bindings : List TVarBinding) (name : String) : Bool :=
  bindings.any fun b => b.unionallKey && b.isTypeVar && b.name == name && b.occurs

/-- Mirrors the plain-IO overload at `base/show.jl:630`. -/
def ioHasTvarNamePlain (_name : String) : Bool := false

inductive TypeShape where
  | data (moduleName : String)
  | typeVar (upper : TypeShape)
  | typeEq (parameter : Option TypeShape)
  | typeEgal (parameter : TypeShape)
  | union (left right : TypeShape)
  | other
  deriving Repr

/-- Mirrors the four `modulesof!` methods at `base/show.jl:632-652`. -/
def modulesOf : TypeShape → List String
  | .data m => [m]
  | .typeVar ub => modulesOf ub
  | .typeEq (some p) => modulesOf p
  | .typeEq none => []
  | .typeEgal p => modulesOf p
  | .union a b => (modulesOf a ++ modulesOf b).eraseDups
  | .other => []

/-- Mirrors `has_other_free_typevars` at `base/show.jl:654-667`. -/
def hasOtherFreeTypevars (free before : List Nat) : Bool :=
  free.any fun v => !before.contains v

inductive AliasShape where
  | atom (text : String)
  | unionall (name : String) (unbounded : Bool) (body : AliasShape)
  deriving Repr

/-- Mirrors the recursive binder walk in `unbounded_typealias` at
`base/show.jl:674-684`. -/
def unboundedTypealias : AliasShape → AliasShape
  | a@(.atom _) => a
  | .unionall name true body => .unionall name true (unboundedTypealias body)
  | .unionall name false body => .unionall name true (unboundedTypealias body)

/-- Mirrors `reapply_unionall_env` at `base/show.jl:692-701`. -/
def reapplyUnionallEnv (isContext : Bool) (bindings : List (Bool × String)) (x : String) : String :=
  if isContext then bindings.foldl (fun acc b => if b.1 then "(" ++ acc ++ " where " ++ b.2 ++ ")" else acc) x
  else x

structure AliasCandidate where
  name : String
  env : List String
  defined : Bool
  deprecated : Bool
  constant : Bool
  isType : Bool
  hasFree : Bool
  printsWithoutParams : Bool
  properSubtype : Bool
  unionall : Bool
  applicationSucceeded : Bool
  hasOtherFree : Bool
  appliedEqualsInput : Bool
  exactInput : Bool
  strictSubtypes : List String
  deriving Repr, DecidableEq

def validTypeAliasCandidate (c : AliasCandidate) : Bool :=
  c.defined && !c.deprecated && c.constant && c.isType && !c.hasFree &&
    !c.printsWithoutParams && c.properSubtype &&
    (if c.unionall then c.applicationSucceeded && !c.hasOtherFree && c.appliedEqualsInput else c.exactInput)

/-- Mirrors candidate collection, strict-subtype filtering, and the unique
result rule in `make_typealias` at `base/show.jl:703-767`. -/
def makeTypealias (isAny isTuple : Bool) (candidates : List AliasCandidate) : Option (String × List String) :=
  if isAny || isTuple then none
  else
    let valid := candidates.filter validTypeAliasCandidate
    let names := valid.map (·.name)
    let best := if valid.length > 1 then
      valid.filter fun c => !(c.strictSubtypes.any fun n => names.contains n)
    else valid
    match best with
    | [c] => some (c.name, c.env)
    | _ => none

/-- Mirrors `isgensym` at `base/show.jl:769`. -/
def isGensym (name : String) : Bool := name.contains '#'

/-- Mirrors `show_can_elide` at `base/show.jl:771-784`.  The two lists contain
the later where-binders and the other environment slots that refer to `p`. -/
def showCanElide (isSelected : Bool) (elide : Nat) (laterRefs otherEnvRefs : List Bool) : Bool :=
  elide != 0 && isSelected && !(laterRefs.any id) && !(otherEnvRefs.any id)

/-- Mirrors the nested `egal_var` method at `base/show.jl:789-793`. -/
def egalVar (otherIsTypeVar upperEquivalent lowerEquivalent : Bool) : Bool :=
  otherIsTypeVar && upperEquivalent && lowerEquivalent

inductive ParamRender where
  | plain (text : String)
  | typevar (text lower upper : String) (lowerBottom upperAny : Bool)
      (whereIndex : Nat)
  deriving Repr, DecidableEq

def renderParam (p : ParamRender) (elide : Nat) : String := match p with
  | .plain text => text
  | .typevar text lower upper lowerBottom upperAny whereIndex =>
    if lowerBottom && whereIndex > elide then "<:" ++ upper
    else if upperAny && whereIndex > elide then ">:" ++ lower
    else text

/-- Mirrors the final rendering and where-vector resize performed by
`show_typeparams` at `base/show.jl:786-830`; the source loop's decisions are
represented by `keep` and `elide`. -/
def showTypeparams (params : List ParamRender) (keep elide : Nat) : String × Nat :=
  let visible := (params.take keep).map fun p => renderParam p elide
  (if visible.isEmpty then "" else "{" ++ ", ".intercalate visible ++ "}", elide)

/-- Mirrors `show_typealias_name` at `base/show.jl:832-845`. -/
def showTypealiasName (compact visible : Bool) (moduleName name : String) : String :=
  (if !compact && !visible then moduleName ++ "." else "") ++ name

/-- Mirrors `show_typealias(::GlobalRef, env, wheres)` at
`base/show.jl:847-862`. -/
def showTypealias (name renderedParams : String) (envEmpty : Bool) : String :=
  name ++ if envEmpty then "" else renderedParams

/-- Mirrors `make_wheres` at `base/show.jl:864-892`. -/
def makeWheres (context outer env : List Nat) : List Nat :=
  let seen := context.eraseDups
  let outerNew := outer.filter fun x => !seen.contains x
  let seen' := (seen ++ outerNew).eraseDups
  let inner := env.reverse.filter fun x => !seen'.contains x
  inner.reverse ++ outerNew

/-- Mirrors `show_wheres` at `base/show.jl:894-906`. -/
def showWheres (wheres : List String) : String := match wheres with
  | [] => ""
  | [w] => " where " ++ w
  | ws => " where {" ++ ", ".intercalate ws ++ "}"

/-- Mirrors the boolean wrapper `show_typealias(io, x)` at
`base/show.jl:908-915`. -/
def showTypealiasLookup (alias : Option String) : Bool × String := match alias with
  | none => (false, "")
  | some text => (true, text)

structure UnionAliasCandidate where
  text : String
  score : Nat × Int
  subsumedByEarlier : Bool
  deriving Repr, DecidableEq

/-- Mirrors the empty handling, score ordering, and subsumption keep pass in
`make_typealiases` at `base/show.jl:917-1000`. -/
def makeTypealiases (isAny isTuple : Bool) (candidates : List UnionAliasCandidate) : List String :=
  if isAny || isTuple then []
  else
    (candidates.mergeSort fun a b => a.score.1 > b.score.1 ||
      (a.score.1 = b.score.1 && a.score.2 > b.score.2)).filterMap fun c =>
        if c.subsumedByEarlier then none else some c.text

structure UnionPiece where
  text : String
  isTypeVar : Bool
  covered : Bool
  deriving Repr, DecidableEq

/-- Mirrors `show_unionaliases` at `base/show.jl:1002-1044`. -/
def showUnionaliases (pieces : List UnionPiece) (aliases : List String) : Bool × String :=
  if aliases.isEmpty then (false, "")
  else
    let ordinary := pieces.filter fun p => !p.isTypeVar && !p.covered
    let tvars := pieces.filter fun p => p.isTypeVar
    if ordinary.isEmpty && tvars.isEmpty && aliases.length = 1 then (true, aliases.head!)
    else (true, "Union{" ++ ", ".intercalate ((ordinary.map (·.text)) ++ aliases ++ (tvars.map (·.text))) ++ "}")

/-- Mirrors the alias annotation and singleton-function hint in
`show(::MIME"text/plain", ::Type)` at `base/show.jl:1046-1069`. -/
def showTypePlain (normal : String) (printNoParams hasAlias compact globalFunction : Bool)
    (symbol : String) : String :=
  if !printNoParams && hasAlias then
    normal ++ if compact then "" else " (alias for " ++ normal ++ ")"
  else normal ++ if !compact && globalFunction then
    " (singleton type of function " ++ symbol ++ ", subtype of Function)" else ""

/-- Mirrors `show_typeegal` at `base/show.jl:1071-1075`. -/
def showTypeEgal (parameter : String) : String := "Core.TypeEgal{" ++ parameter ++ "}"

inductive AnyTypeView where
  | bottom
  | typeEgal (parameter : String)
  | typeEq (parameter : String)
  | other (rendered : String)
  deriving Repr, DecidableEq

/-- Mirrors `show(::Core.AnyType)` at `base/show.jl:1076-1086`. -/
def showAnyType : AnyTypeView → String
  | .bottom => "Union{}"
  | .typeEgal p => showTypeEgal p
  | .typeEq p => "Type{" ++ p ++ "}"
  | .other s => s

/-- Mirrors `show_typeeq` at `base/show.jl:1091-1095`. -/
def showTypeEq (compact : Bool) (parameter : String) : String :=
  (if compact then "Type{" else "TypeEq{") ++ parameter ++ "}"

inductive ShowTypeBranch where
  | typeEgal (parameter : String)
  | withoutParams (name : String)
  | alias (text : String)
  | typeEq (parameter : String)
  | datatype (text : String)
  | union (aliasesWorked : Bool) (text : String)
  | bottom
  | unionall (body : String) (wheres : List String)
  deriving Repr, DecidableEq

/-- Mirrors the dispatch order of `_show_type` at `base/show.jl:1096-1152`. -/
def showType (compact : Bool) : ShowTypeBranch → String
  | .typeEgal p => showTypeEgal p
  | .withoutParams n => n
  | .alias s => if compact then s else s
  | .typeEq p => showTypeEq compact p
  | .datatype s => s
  | .union worked s => if compact && worked then s else "Union" ++ s
  | .bottom => "Union{}"
  | .unionall body wheres => body ++ showWheres wheres

structure VisibilityView where
  deprecated : Bool
  fromDefined : Bool
  parentDefined : Bool
  sameBinding : Bool
  importedChainReachesParent : Bool
  bothDefinedConst : Bool
  sameRestriction : Bool
  deriving Repr, DecidableEq

/-- Mirrors `isvisible` at `base/show.jl:1159-1177`. -/
def isVisible (v : VisibilityView) : Bool :=
  if v.deprecated || !v.fromDefined || !v.parentDefined then false
  else if v.sameBinding || v.importedChainReachesParent then true
  else v.bothDefinedConst && v.sameRestriction

structure GlobalFunctionView where
  hasName : Bool
  concreteWrapper : Bool
  isDataTypeName : Bool
  containsHash : Bool
  containsAt : Bool
  hasModule : Bool
  defined : Bool
  constant : Bool
  valueHasWrapperType : Bool
  deriving Repr, DecidableEq

/-- Mirrors `is_global_function` at `base/show.jl:1179-1189`. -/
def isGlobalFunction (v : GlobalFunctionView) : Bool :=
  v.hasName && v.concreteWrapper && !v.isDataTypeName && !v.containsHash && !v.containsAt &&
    v.hasModule && v.defined && v.constant && v.valueHasWrapperType

structure WorldPartition where
  definedConst : Bool
  valueIsSubtype : Bool
  minWorld : Int
  maxWorld : Option Int
  deriving Repr, DecidableEq

/-- Mirrors the partition walk in `check_world_bounded` at
`base/show.jl:1191-1209`; `none` for `maxWorld` represents `typemax(UInt)`. -/
def checkWorldBounded : List WorldPartition → Option (Int × Int)
  | [] => none
  | p :: ps => if p.definedConst && p.valueIsSubtype then
      match p.maxWorld with | none => none | some m => some (p.minWorld, m)
    else checkWorldBounded ps

structure TypeNameView where
  unionAllName : Bool
  globalFunction : Bool
  compact : Bool
  prefixModule : Bool
  moduleText : String
  symbolText : String
  symbolStartsIdentifier : Bool
  quotedSymbol : Bool
  world : Option (Int × Int)
  deriving Repr, DecidableEq

/-- Mirrors `show_type_name` at `base/show.jl:1211-1246`. -/
def showTypeName (v : TypeNameView) : String :=
  if v.unionAllName then "UnionAll"
  else
    let prefixText := if v.globalFunction then "typeof(" else ""
    let worldOpen := if v.world.isSome then "@world(" else ""
    let modulePrefix := if !v.compact && v.prefixModule then
      v.moduleText ++ "." ++ if v.globalFunction && !v.symbolStartsIdentifier then
        if v.quotedSymbol then ":(" else ":" else "" else ""
    let worldClose := match v.world with | none => "" | some w => ", " ++ toString w.1 ++ ":" ++ toString w.2 ++ ")"
    let quoteClose := if !v.compact && v.prefixModule && v.globalFunction &&
      !v.symbolStartsIdentifier && v.quotedSymbol then ")" else ""
    prefixText ++ worldOpen ++ modulePrefix ++ v.symbolText ++ worldClose ++ quoteClose ++
      (if v.globalFunction then ")" else "")

structure KwargsView where
  pairsName : Bool
  fourParameters : Bool
  firstSymbol : Bool
  fourthNamedTuple : Bool
  fourthHasTwoParameters : Bool
  typesDataType : Bool
  secondMatchesEltype : Bool
  symbolsTuple : Bool
  thirdNothing : Bool
  result : String
  deriving Repr, DecidableEq

/-- Mirrors `maybe_kws_nt` at `base/show.jl:1248-1264`. -/
def maybeKwsNt (v : KwargsView) : Option String :=
  if v.pairsName && v.fourParameters && v.firstSymbol && v.fourthNamedTuple &&
      v.fourthHasTwoParameters && v.typesDataType && v.secondMatchesEltype &&
      v.symbolsTuple && v.thirdNothing then some v.result else none

inductive VarargKind where | none | fixed (n : Nat) | bound (n : String) | unbound
  deriving Repr, DecidableEq

structure DatatypeView where
  tuple : Bool
  namedTuple : Bool
  tupleParams : List String
  homogeneousTail : Nat
  varargKind : VarargKind
  namedTupleValid : Bool
  namedTupleText : String
  backtrace : Bool
  kwargsText : Option String
  ordinaryText : String
  deriving Repr, DecidableEq

def renderTupleType (params : List String) (tail : Nat) (kind : VarargKind) : String :=
  if params.isEmpty then "Tuple{}"
  else
    let fulln := match kind with | .fixed n => params.length + n - 1 | _ => params.length
    let last := params.getLast!
    let useNTuple := match kind with
      | .bound _ => params.length = 1 && tail = 1
      | .fixed _ => tail = fulln && 3 < tail
      | .none => tail = fulln && 3 < tail
      | .unbound => false
    if useNTuple then
      let ntext := match kind with | .bound n => n | _ => toString fulln
      "NTuple{" ++ ntext ++ ", " ++ last ++ "}"
    else
      let headlen := if 3 < tail then fulln - tail else fulln
      let shownHead := (List.range headlen).map fun i =>
        if let .fixed _ := kind then if params.length ≤ i then last else params[i]!
        else params[i]!
      let tailText := if headlen < fulln then
        (if headlen > 0 then ["Vararg{" ++ last ++ ", " ++ toString (fulln - headlen) ++ "}"]
         else ["Vararg{" ++ last ++ ", " ++ toString fulln ++ "}"])
        else []
      "Tuple{" ++ ", ".intercalate (shownHead ++ tailText) ++ "}"

/-- Mirrors `show_datatype` at `base/show.jl:1266-1360`. -/
def showDatatype (v : DatatypeView) : String :=
  if v.tuple then renderTupleType v.tupleParams v.homogeneousTail v.varargKind
  else if v.namedTuple && v.namedTupleValid then "@NamedTuple{" ++ v.namedTupleText ++ "}"
  else if v.backtrace && v.kwargsText.isSome then "@Kwargs{" ++ v.kwargsText.get! ++ "}"
  else v.ordinaryText

/-- Mirrors both `show_supertypes` methods at `base/show.jl:1378-1386`. -/
def showSupertypes (types : List String) : String := " <: ".intercalate types

/-- Models the expansion produced by `@show` at `base/show.jl:1406-1414`.
Each pair is the source expression text and its evaluated `repr`. -/
def showMacro (expressions : List (String × String)) : List String × Option String :=
  (expressions.map fun e => e.1 ++ " = " ++ e.2, expressions.getLast?.map (·.2))

/-- Mirrors `show(::Core.TypeName)` at `base/show.jl:1416-1420`. -/
def showTypeNameObject (name : String) : String := "typename(" ++ name ++ ")"

/-! ## Source information and AST helpers -/

def duplicateCounts (names : List String) : List (String × Nat) :=
  names.foldl (fun counts name =>
    let n := (counts.find? (·.1 == name)).map (·.2) |>.getD 0
    (name, n + 1) :: counts.filter (·.1 != name)) []

/-- Mirrors `sourceinfo_slotnames` at `base/show.jl:1495-1516`. -/
def sourceinfoSlotnames (slotnames : List String) : List String :=
  let counts := duplicateCounts slotnames
  slotnames.mapIdx fun i name =>
    if name == "#unused#" then "_"
    else if name.isEmpty || (counts.find? (·.1 == name)).any (fun p => p.2 > 1) then
      name ++ "@_" ++ toString (i + 1)
    else name

inductive MethodInstanceView where
  | generator (methodText : String)
  | method (callText : String)
  | thunk (detail : Option (String × String))
  deriving Repr, DecidableEq

/-- Mirrors `show_mi` at `base/show.jl:1533-1560`. -/
def showMethodInstance (fromStackframe : Bool) : MethodInstanceView → String
  | .generator m => "MethodInstance generator for " ++ m
  | .method c => "MethodInstance for " ++ c
  | .thunk detail => "Toplevel MethodInstance thunk" ++ match detail with
      | some (definition, line) =>
        if fromStackframe then "" else " from " ++ definition ++ " starting at " ++ line
      | none => ""

/-- Mirrors `show(::CodeInstance)` at `base/show.jl:1519-1531`. -/
def showCodeInstance (mi : String) (abiOverridden foreign : Bool) : String :=
  "CodeInstance for " ++ mi ++ (if abiOverridden then " (ABI Overridden)" else "") ++
    (if foreign then " (foreign)" else "")

/-- Mirrors the simple `ExprNode` and `show_unquoted` forwarding methods at
`base/show.jl:1666-1671`. -/
def printExprNode (quoteString : UData → JuliaLean.Strings.JStr → List UInt8)
    (escapeRaw : JuliaLean.Strings.JStr → List UInt8) (d : UData) (o : OpData) (ex : JE) : PO :=
  showUnquoted quoteString escapeRaw d o (16 * ex.size + 16) false false ex 0 (-1) 0
def showExprNode (quoteString : UData → JuliaLean.Strings.JStr → List UInt8)
    (escapeRaw : JuliaLean.Strings.JStr → List UInt8) (d : UData) (o : OpData) (ex : JE) : PO :=
  showQuoteExpr quoteString escapeRaw d o (16 * ex.size + 16) true false ex 0 (-1)
def showUnquoted0 (quoteString : UData → JuliaLean.Strings.JStr → List UInt8)
    (escapeRaw : JuliaLean.Strings.JStr → List UInt8) (d : UData) (o : OpData) (ex : JE) : PO :=
  showUnquoted quoteString escapeRaw d o (16 * ex.size + 16) false false ex 0 0 0
def showUnquotedIndent (quoteString : UData → JuliaLean.Strings.JStr → List UInt8)
    (escapeRaw : JuliaLean.Strings.JStr → List UInt8) (d : UData) (o : OpData) (ex : JE) (indent : Nat) : PO :=
  showUnquoted quoteString escapeRaw d o (16 * ex.size + 16) false false ex indent 0 0
def showUnquotedFallback (rendered : String) : String := rendered
def showUnquotedQuoteLevel (quoteString : UData → JuliaLean.Strings.JStr → List UInt8)
    (escapeRaw : JuliaLean.Strings.JStr → List UInt8) (d : UData) (o : OpData) (ex : JE)
    (indent : Nat) (prec : Int) : PO :=
  showUnquoted quoteString escapeRaw d o (16 * ex.size + 16) false false ex indent prec 0

/-- Mirrors the two `operator_precedence` methods at `base/show.jl:1713-1714`. -/
def operatorPrecedenceSymbol (runtime : String → Int) (symbol : String) : Int := runtime symbol
def operatorPrecedenceAny : Int := 0

inductive Associativity where | left | right | none
  deriving Repr, DecidableEq

/-- Mirrors `operator_associativity` at `base/show.jl:1739-1748`. -/
def operatorAssociativity (precedence arrow assignment control pair power comparison : Int)
    (unaryOnly rightSpelling neutralSpelling : Bool) : Associativity :=
  if precedence ∈ [arrow, assignment, control, pair, power] || unaryOnly || rightSpelling then .right
  else if precedence ∈ [0, comparison] || neutralSpelling then .none
  else .left

/-- Mirrors the three `is_quoted` methods at `base/show.jl:1750-1752`. -/
def isQuotedOther : Bool := false
def isQuotedQuoteNode : Bool := true
def isQuotedExpr (head : String) (nargs : Nat) : Bool := (head == "quote" || head == "inert") && nargs = 1

/-- Mirrors the `unquoted` methods at `base/show.jl:1754-1755`. -/
def unquotedValue (value : String) : String := value
def unquotedExpr (args : List String) : Option String := args.head?

/-- Mirrors `emphasize` at `base/show.jl:1762-1764`; the result records the
selected printer, text, color, and bold flag. -/
def emphasize (colorEnabled : Bool) (text color : String) : String × String × Bool :=
  if colorEnabled then ("styled", text ++ ":" ++ color, true)
  else ("plain", text.toUpper, false)

/-- Mirrors the three `show_linenumber` methods at `base/show.jl:1766-1768`. -/
def showLineNumber (line : Int) (file : Option String := none) : String := match file with
  | none => "#= line " ++ toString line ++ " =#"
  | some f => "#= " ++ f ++ ":" ++ toString line ++ " =#"

/-- Mirrors the three `show_block` methods at `base/show.jl:1771-1797` at the
level of already-rendered arguments and body statements. -/
def showBlockText (head : String) (args body : List String) (indent : Nat) (moduleHead : Bool) : String :=
  let argsText := if args.isEmpty then "" else " " ++ (if head == "elseif" then " " else ", ").intercalate args
  let bodyIndent := if moduleHead then indent else indent + 4
  head ++ argsText ++ String.join (body.map fun ex => "\n" ++ String.ofList (List.replicate bodyIndent ' ') ++ ex) ++
    "\n" ++ String.ofList (List.replicate indent ' ')

/-- Mirrors `show_enclosed_list` at `base/show.jl:1828-1832`. -/
def showEnclosedListText (op cl sep : String) (items : List String) : String :=
  op ++ sep.intercalate items ++ cl

inductive WarnClass where | invalid | strong | mild | normal
  deriving Repr, DecidableEq

/-- Mirrors `show_unquoted(::SSAValue)` at `base/show.jl:1880-1894`. -/
def showSSAValue (id : Int) (cls : WarnClass) : String × String × Bool :=
  let text := "%" ++ toString id
  match cls with
  | .invalid => (text, "red", false)
  | .strong => (text, "light_red", true)
  | .mild => (text, "warn", true)
  | .normal => (text, "plain", false)

/-- Mirrors the one-line IR-node methods at `base/show.jl:1895-1900`. -/
def showSymbolNode (shown : String) : String := shown
def showLineNode (line : Int) (file : Option String) : String := showLineNumber line file
def showGotoNode (label : Int) : String := "goto %" ++ toString label
def showGlobalRefNode (shown : String) : String := shown
def showBindingPartitionNode (ownerGlobalRef : String) : String := ownerGlobalRef

/-- Mirrors `show_globalref` at `base/show.jl:1902-1912`. -/
def showGlobalRef (moduleName symbolShown : String) (identifier startsAt operator quoted : Bool) : String :=
  let needsQuote := !identifier && !startsAt
  let parens := needsQuote && (!operator || quoted)
  moduleName ++ "." ++ (if needsQuote then ":" else "") ++
    (if parens then "(" else "") ++ symbolShown ++ (if parens then ")" else "")

/-- Mirrors `show_unquoted(::SlotNumber)` at `base/show.jl:1914-1922`. -/
def showSlotNumber (id : Nat) (slotnames : Option (List String)) : String := match slotnames with
  | some names => if id > 0 && id ≤ names.length then names[id - 1]! else "_" ++ toString id
  | none => "_" ++ toString id

/-- Mirrors `show_unquoted(::QuoteNode)` at `base/show.jl:1924-1935`. -/
def showQuoteNode (symbol : Option String) (shownValue : String) : String := match symbol with
  | some s => s
  | none => "$(QuoteNode(" ++ shownValue ++ "))"

/-- Mirrors the loop structure of `show_generator` at `base/show.jl:1962-1981`.
`ranges` is in the order collected from nested `:flatten` nodes. -/
def showGenerator (body : String) (ranges : List (List String)) : String :=
  body ++ String.join (ranges.map fun r => " for " ++ ", ".intercalate r)

inductive ImportExpr where
  | symbol (name : String)
  | path (parts : List String)
  | colon (base : ImportExpr) (names : List ImportExpr)
  | as (path alias : ImportExpr)
  | other (shown : String)
  deriving Repr

/-- Mirrors `valid_import_path` at `base/show.jl:1983-1988`. -/
def validImportPath : ImportExpr → Bool → Bool
  | .as path _, true => validImportPath path false
  | .path parts, _ => !parts.isEmpty
  | _, _ => false

/-- Mirrors `show_import_path` at `base/show.jl:1990-2020`. -/
def showImportPath : ImportExpr → String
  | .symbol name => name
  | .path parts => ".".intercalate (parts.map fun p => if p == ".." then "(..)" else p)
  | .colon base names => showImportPath base ++ ": " ++ ", ".intercalate (names.map showImportPath)
  | .as path alias => showImportPath path ++ " as " ++ showImportPath alias
  | .other shown => shown

/-- Mirrors `allow_macroname` at `base/show.jl:2023-2032`. -/
def allowMacroname (symbolStartsAt globalRef quotedDot : Bool) (shown : String) : String :=
  if symbolStartsAt || globalRef || quotedDot then "macroname(" ++ shown ++ ")" else shown

/-- Mirrors the four `is_core_macro` methods at `base/show.jl:2034-2037`. -/
def isCoreMacroGlobal (isCore : Bool) (name macroName : String) : Bool := isCore && name == macroName
def isCoreMacroOther (_macroName : String) : Bool := false

/-- Mirrors `show_unquoted_expr_fallback` at `base/show.jl:2043-2051`. -/
def showExprFallback (head : String) (args : List String) : String :=
  "$(Expr(" ++ head ++ String.join (args.map (", " ++ ·)) ++ "))"

/-! ## Stacktrace and IR display -/

/-- Mirrors both `demangle_function_name` methods at `base/show.jl:2608-2616`. -/
def demangleFunctionName (name : String) : String :=
  match name.splitOn "#" with
  | first :: _ :: _ => if first.isEmpty then name else first
  | _ => name

inductive SignatureFunctionView where
  | globalFunction (qualified needsModule : Bool) (moduleName name : String)
  | typeObject (needsParens : Bool) (text : String)
  | other (typeText argName : String) (html : Bool)
  deriving Repr, DecidableEq

/-- Mirrors `show_signature_function` at `base/show.jl:2620-2643`. -/
def showSignatureFunction : SignatureFunctionView → String
  | .globalFunction qualified needsModule mod name =>
      (if qualified && needsModule then mod ++ "." else "") ++ name
  | .typeObject parens text => (if parens then "(" else "") ++ text ++ (if parens then ")" else "")
  | .other typ arg html => if html then "(" ++ arg ++ "::<b>" ++ typ ++ "</b>)"
      else "(" ++ arg ++ "::" ++ typ ++ ")"

/-- Mirrors `print_within_stacktrace` at `base/show.jl:2645-2651`. -/
def printWithinStacktrace (backtrace : Bool) (text color : String) (bold : Bool) : String × String × Bool :=
  if backtrace then (text, color, bold) else (text, "plain", false)

structure CallArg where
  name : Option String
  typeText : String
  deriving Repr, DecidableEq

structure KwArg where
  name : String
  typeText : String
  splat : Bool
  deriving Repr, DecidableEq

/-- Mirrors the output construction in `show_tuple_as_call` at
`base/show.jl:2653-2710`. -/
def showTupleAsCall (functionText : String) (args : List CallArg) (kwargs : Option (List KwArg))
    (whereText : String) : String :=
  let positional := args.map fun a => a.name.getD "" ++ "::" ++ a.typeText
  let kwtext := match kwargs with
    | none => ""
    | some ks => "; " ++ ", ".intercalate (ks.map fun k => k.name ++ if k.splat then "..." else "::" ++ k.typeText)
  functionText ++ "(" ++ ", ".intercalate positional ++ kwtext ++ ")" ++ whereText

/-- Mirrors `type_limited_string_from_context` at `base/show.jl:2712-2723`.
`limited` is the result of the separately modelled `type_depth_limit` call. -/
def typeLimitedStringFromContext (flagPresent : Bool) (original limited : String) : String × Bool :=
  if flagPresent then (limited, limited.utf8ByteSize < original.utf8ByteSize) else (original, false)

/-- Mirrors the two `print_type_bicolor` methods at `base/show.jl:2818-2838`.
The tuple records the outer, inner, and final ellipsis pieces. -/
def printTypeBicolor (str : String) (braceIndex : Option Nat) (endsEllipsis useColor : Bool) : List (String × String) :=
  if !useColor then [(str, "plain")]
  else match braceIndex with
    | none => [(str, "outer")]
    | some i =>
      let outer := str.toList.take i
      let inner := str.toList.drop i
      if endsEllipsis && inner.length ≥ 3 then
        [(String.ofList outer, "outer"), (String.ofList (inner.dropLast.dropLast.dropLast), "inner"), ("...", "outer")]
      else [(String.ofList outer, "outer"), (String.ofList inner, "inner")]

inductive BindingExpr where
  | value (text : String)
  | quote (value : String)
  | symbol (name : String)
  | dot (parent : BindingExpr) (name : String)
  | global (defined constant isModule : Bool) (moduleName name : String)
  deriving Repr, DecidableEq

/-- Mirrors the five `resolvebinding` methods at `base/show.jl:2840-2858`. -/
def resolveBinding : BindingExpr → Option String
  | .value text => some text
  | .quote value => some value
  | .symbol name => some name
  | .dot parent name => (resolveBinding parent).map (· ++ "." ++ name)
  | .global defined constant isModule mod name =>
      if defined && constant && isModule then some (mod ++ "." ++ name) else none

/-- Mirrors `ismodulecall` at `base/show.jl:2860-2864`. -/
def isModuleCall (callHead getfieldFunction resolvedModule : Bool) : Bool :=
  callHead && getfieldFunction && resolvedModule

/-- Mirrors `show(::TypeVar)` and its nested `show_bound` at
`base/show.jl:2866-2899`. -/
def showTypeVar (name lower upper : String) (inEnv lowerBottom upperAny lowerParens upperParens : Bool) : String :=
  let lb := (if lowerParens then "(" else "") ++ lower ++ (if lowerParens then ")" else "")
  let ub := (if upperParens then "(" else "") ++ upper ++ (if upperParens then ")" else "")
  let first := if !inEnv && !lowerBottom then
    if upperAny then name ++ ">:" ++ lb else lb ++ "<:" ++ name
    else name
  first ++ if !inEnv && !upperAny then "<:" ++ ub else ""

/-- Mirrors `show(::Core.TypeofVararg)` at `base/show.jl:2901-2912`. -/
def showVararg (typeText : Option String) (lengthText : Option String) : String := match typeText with
  | none => "Vararg"
  | some t => "Vararg{" ++ t ++ (lengthText.map (", " ++ ·)).getD "" ++ "}"

/-- Mirrors `show(::CodeInfo)` at `base/show.jl:2916-2929`. -/
def showCodeInfo (ir : String) : String := "CodeInfo(\n" ++ ir ++ ")"

/-- Mirrors the Argument wrapper at `base/show.jl:2931`. -/
def showArgument (slot : Nat) (names : Option (List String)) : String := showSlotNumber slot names

/-- Mirrors `show_unquoted_phinode` at `base/show.jl:2933-2947`. -/
def showPhiNode (edges : List Int) (values : List (Option String)) (prefixText : String := "%") : String :=
  let pairs := List.zipWith (fun e v => prefixText ++ toString e ++ " => " ++ v.getD "#undef") edges values
  "φ (" ++ ", ".intercalate pairs ++ ")"

/-- Mirrors `show_unquoted(::PhiCNode)` at `base/show.jl:2949-2957`. -/
def showPhiCNode (values : List String) : String := "φᶜ (" ++ ", ".intercalate values ++ ")"

/-- Mirrors `show_unquoted(::PiNode)` at `base/show.jl:2959-2965`. -/
def showPiNode (value typeText : String) : String := "π (" ++ value ++ ", " ++ typeText ++ ")"

/-- Mirrors `show_unquoted(::UpsilonNode)` at `base/show.jl:2967-2973`. -/
def showUpsilonNode (value : Option String) : String := "ϒ (" ++ value.getD "#undef" ++ ")"

/-- Mirrors `show_unquoted(::ReturnNode)` at `base/show.jl:2975-2982`. -/
def showReturnNode (value : Option String) : String := match value with
  | none => "unreachable"
  | some v => "return " ++ v

/-- Mirrors both GotoIfNot methods at `base/show.jl:2984-2988`. -/
def showGotoIfNot (dest : Int) (condition : String) (prefixText : String := "%") : String :=
  "goto " ++ prefixText ++ toString dest ++ " if not " ++ condition

/-! ## Opaque closures, bindings, and partitions -/

/-- Mirrors both OpaqueClosure show methods at `base/show.jl:3443-3452`. -/
def showOpaqueClosure (arguments result : String) : String := arguments ++ "->◌::" ++ result

inductive PartitionKind where
  | backdatedConst | const | constImport | undefConst | guard | failed | declared
  | implicitGlobal (target : String) | implicitConst | explicitUsing (target : String)
  | imported (target : String) | globalVar (typeText : String)
  deriving Repr, DecidableEq

structure PartitionView where
  minWorld : Nat
  maxWorld : Option Nat
  flags : List String
  kind : PartitionKind
  deriving Repr, DecidableEq

def partitionKindText : PartitionKind → String
  | .backdatedConst => "backdated constant binding"
  | .const => "constant binding"
  | .constImport => "constant binding (declared with `import`)"
  | .undefConst => "undefined const binding"
  | .guard => "undefined binding - guard entry"
  | .failed => "ambiguous binding - guard entry"
  | .declared => "weak global binding declared using `global` (implicit type Any)"
  | .implicitGlobal target => "implicit `using` resolved to global " ++ target
  | .implicitConst => "implicit `using` resolved to constant"
  | .explicitUsing target => "explicit `using` from " ++ target
  | .imported target => "explicit `import` from " ++ target
  | .globalVar typ => "global variable with type " ++ typ

/-- Mirrors `print_partition` at `base/show.jl:3455-3505`. -/
def printPartition (p : PartitionView) : String :=
  toString p.minWorld ++ ":" ++ (p.maxWorld.map toString).getD "∞" ++
    (if p.flags.isEmpty then "" else " [" ++ ",".intercalate p.flags ++ "]") ++
    " - " ++ partitionKindText p.kind

/-- Mirrors the two BindingPartition show methods at `base/show.jl:3507-3517`. -/
def showPartition (owner : String) (p : PartitionView) (plain : Bool) : String :=
  if plain then "BindingPartition for " ++ owner ++ "\n   " ++ printPartition p
  else "BindingPartition(for " ++ owner ++ ": " ++ printPartition p ++ ")"

/-- Mirrors `show(::MIME"text/plain", ::Binding)` at
`base/show.jl:3519-3536`. -/
def showBinding (globalRef : String) (partitions : Option (List PartitionView)) : String := match partitions with
  | none => "Binding " ++ globalRef ++ " - No partitions"
  | some ps => "Binding " ++ globalRef ++ String.join (ps.map fun p => "\n   " ++ printPartition p)

end JuliaLean.ShowCov.Remaining



/-!
# ANSI-aware truncation: `ANSIIterator`, `_truncate_at_width_or_chars`,
# `type_depth_limit` (`base/show.jl:79-135, 2726-2816`)

Strings are valid UTF-8 `String`s, modelled as their `Char` lists; a
character's string index is its 1-based byte offset (`Char.utf8Size` bytes
per character). `tw` is `textwidth(::Char)` (a Unicode table, so a
parameter).
-/

namespace JuliaLean.ShowCov.Truncate

open JuliaLean.ShowCov

/-- An element produced by `ANSIIterator`: a character or an `ANSIDelimiter`
holding the matched escape sequence. -/
inductive Tok where
  | ch (c : Char)
  | ansi (del : List Char)
  deriving DecidableEq, Repr

/-- `ncodeunits` of a token (`ncodeunits(c::ANSIDelimiter) = ncodeunits(c.del)`,
`base/show.jl:85`). -/
def Tok.ncu : Tok → Nat
  | .ch c => c.utf8Size
  | .ansi d => (d.map Char.utf8Size).sum

/-- `textwidth(::ANSIDelimiter) = 0`, `base/show.jl:86`. -/
def Tok.width (tw : Char → Nat) : Tok → Nat
  | .ch c => tw c
  | .ansi _ => 0

def inRange (c : Char) (lo hi : Nat) : Bool := lo ≤ c.toNat && c.toNat ≤ hi

/-- Longest run of characters in `[lo, hi]` at the front. -/
def spanRange (lo hi : Nat) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if inRange c lo hi then
      let (a, b) := spanRange lo hi cs
      (c :: a, b)
    else ([], c :: cs)

/-- One match of `ansi_regex` (`base/show.jl:79`) at the front of a nonempty
string: ESC followed by one of `@`..`Z` or `\`..`_`; or ESC `[`, parameter bytes
0x30-0x3F, intermediate bytes 0x20-0x2F and a final byte 0x40-0x7E; otherwise
any single character (`(?s).`). Returns the matched token and the rest. -/
def ansiMatch : List Char → Option (Tok × List Char)
  | [] => none
  | c :: cs =>
    let single := some (Tok.ch c, cs)
    if c.toNat = 0x1B then
      match cs with
      | d :: ds =>
        if inRange d 0x40 0x5A || inRange d 0x5C 0x5F then some (.ansi [c, d], ds)
        else if d = '[' then
          let (p, r1) := spanRange 0x30 0x3F ds
          let (q, r2) := spanRange 0x20 0x2F r1
          match r2 with
          | f :: r3 => if inRange f 0x40 0x7E then some (.ansi ([c, d] ++ p ++ q ++ [f]), r3) else single
          | [] => single
        else single
      | [] => single
    else single

/-- `ANSIIterator(s)` (`base/show.jl:92-101`): the regex matches of `s` in
order; every character belongs to exactly one match. Each match consumes at
least one character, so `length(s)` rounds suffice. -/
def ansiTokensF : Nat → List Char → List Tok
  | 0, _ => []
  | fuel + 1, s =>
    match ansiMatch s with
    | some (t, r) => t :: ansiTokensF fuel r
    | none => []

def ansiTokens (s : List Char) : List Tok := ansiTokensF s.length s

/-- `IteratorSize(::Type{<:ANSIIterator}) = SizeUnknown()` and
`eltype(::Type{<:ANSIIterator}) = Pair{Int, Union{Char,ANSIDelimiter}}`,
`base/show.jl:94-95`. -/
def iteratorSizeANSI : String := "SizeUnknown"
def eltypeANSI : String := "Pair{Int, Union{Char,ANSIDelimiter}}"

/-- Pair each token with its 1-based starting byte index (`i => c`). -/
def indexed : Nat → List Tok → List (Nat × Tok)
  | _, [] => []
  | i, t :: ts => (i, t) :: indexed (i + t.ncu) ts

/-- `pairs(str)` as tokens: every character on its own. -/
def charTokens (s : List Char) : List Tok := s.map Tok.ch

/-- `textwidth(I::ANSIIterator) = mapreduce(textwidth∘last, +, I; init=0)`,
`base/show.jl:102`. -/
def ansiWidth (tw : Char → Nat) (s : List Char) : Nat :=
  ((ansiTokens s).map (Tok.width tw)).sum

/-- `textwidth(s)` of a plain string. -/
def textwidth (tw : Char → Nat) (s : List Char) : Nat := (s.map tw).sum

/-- The characters of `str` whose start index is at most `idx`
(`SubString(str, 1, idx)` when `idx` is a character start or `0`). -/
def prefixUpTo (str : List Char) (idx : Nat) : List Char :=
  let rec go : Nat → List Char → List Char
    | _, [] => []
    | i, c :: cs => if i ≤ idx then c :: go (i + c.utf8Size) cs else []
  go 1 str

/-- The character starting at byte index `idx`, if any. -/
def charAt (str : List Char) (idx : Nat) : Option Char :=
  let rec go : Nat → List Char → Option Char
    | _, [] => none
    | i, c :: cs => if i = idx then some c else go (i + c.utf8Size) cs
  go 1 str

/-- `prevind(str, idx)`: the start of the character before the one at `idx`
(0 if none). -/
def prevind (str : List Char) (idx : Nat) : Nat :=
  let rec go : Nat → Nat → List Char → Nat
    | _, prev, [] => prev
    | i, prev, c :: cs => if i ≥ idx then prev else go (i + c.utf8Size) i cs
  go 1 0 str

/-- `lastindex(str)`: start of the last character (0 for `""`). -/
def lastindex (str : List Char) : Nat :=
  let rec go : Nat → Nat → List Char → Nat
    | _, last, [] => last
    | i, _, c :: cs => go (i + c.utf8Size) i cs
  go 1 0 str

/-- The reset sequence `"\033[0m"`. -/
def resetSeq : List Char := ['\x1b', '[', '0', 'm']

/-- Loop state of `_truncate_at_width_or_chars`. -/
structure TState where
  wid : Nat
  truncidx : Nat
  lastidx : Nat
  stop : Bool
  needANSIend : Bool
  deriving DecidableEq, Repr

/-- `c != "\033[0m"` for an `ANSIDelimiter` `c` (`base/show.jl:114`):
`ANSIDelimiter` is not an `AbstractString` and has no `==` method with
`String`, so `==` falls back to `===`, which is `false`. -/
def ansiDelimNeString (_del : List Char) : Bool := true

/-- The `for (i, c) in I` loop of `_truncate_at_width_or_chars`,
`base/show.jl:112-124`. -/
def truncLoop (tw : Char → Nat) (width truncwidth : Int) (chars : List Char) :
    TState → List (Nat × Tok) → TState
  | st, [] => st
  | st, (i, t) :: rest =>
    match t with
    | .ansi del =>
      let st := { st with
        needANSIend := if st.truncidx = 0 then ansiDelimNeString del else st.needANSIend
        lastidx := i + t.ncu - 1 }
      truncLoop tw width truncwidth chars st rest
    | .ch c =>
      if st.stop then st else
      let wid := st.wid + tw c
      let truncidx := if st.truncidx = 0 ∧ (wid : Int) > width - truncwidth then st.lastidx else st.truncidx
      let st := { st with wid := wid, truncidx := truncidx, lastidx := i }
      if c ∈ chars then st else
      truncLoop tw width truncwidth chars { st with stop := decide ((wid : Int) ≥ width) } rest

/-- `_truncate_at_width_or_chars(ignore_ANSI, str, width, rpad, chars, truncmark)`,
`base/show.jl:104-135`. -/
def truncateAt (tw : Char → Nat) (ignoreANSI : Bool) (str : List Char) (width : Int)
    (rpad : Bool := false) (chars : List Char := ['\r', '\n']) (truncmark : List Char := ['…']) :
    List Char :=
  let truncwidth : Int := textwidth tw truncmark
  if width ≤ 0 ∨ width < truncwidth then [] else
  let toks := if ignoreANSI then ansiTokens str else charTokens str
  let st := truncLoop tw width truncwidth chars ⟨0, 0, 0, false, false⟩ (indexed 1 toks)
  if st.lastidx = 0 then (if rpad then List.replicate width.toNat ' ' else []) else
  let lastidx := match charAt str st.lastidx with
    | some c => if c ∈ chars then prevind str st.lastidx else st.lastidx
    | none => st.lastidx
  let ansiEnd := if st.needANSIend then resetSeq else []
  let pad := if rpad then List.replicate (width - st.wid).toNat ' ' else []
  let truncidx := if st.truncidx = 0 then lastidx else st.truncidx
  if lastidx < lastindex str then prefixUpTo str truncidx ++ ansiEnd ++ truncmark ++ pad
  else str ++ ansiEnd ++ pad

/-! ## `type_depth_limit` -/

/-- Quote state bits: `st_backslash = 1`, `st_squote = 2`, `st_dquote = 4`
(`base/show.jl:2732`), with `stateis`, `quoted`, `enter`, `leave`
(`base/show.jl:2734-2737`). -/
structure QState where
  backslash : Bool
  squote : Bool
  dquote : Bool
  deriving DecidableEq, Repr

def QState.quoted (q : QState) : Bool := q.squote || q.dquote

/-- First pass: depth at each token (in order), per-level widths and counts,
and the total width, `base/show.jl:2738-2783`. `widthAt` and `levelcount` are
indexed from depth 1. Depths are `Int` (Julia stores them as `Int16`). A
`levelcount[depth]` update at depth `< 1` is a `BoundsError`. -/
structure Pass1 where
  depth : Int
  widthAt : List Nat
  levelcount : List Nat
  strwid : Nat
  q : QState
  depths : List Int
  deriving DecidableEq, Repr

def bumpAt (l : List Nat) (k : Nat) (d : Nat) : List Nat :=
  l.modify k (· + d)

def pass1Step (tw : Char → Nat) (s : Pass1) : Tok → R Pass1
  | .ansi _ => .ok { s with depths := s.depths ++ [s.depth] }
  | .ch c => do
    let q := s.q
    let q :=
      if c = '\\' ∧ q.quoted then { q with backslash := true }
      else if c = '\'' then
        (if q.backslash || q.dquote then q
         else if q.squote then { q with squote := false }
         else { q with squote := true })
      else if c = '"' then
        (if q.backslash || q.squote then q
         else if q.dquote then { q with dquote := false }
         else { q with dquote := true })
      else q
    let depth := if c = '}' ∧ !q.quoted then s.depth - 1 else s.depth
    let wid := tw c
    let strwid := s.strwid + wid
    let widthAt := if depth > 0 then bumpAt s.widthAt (depth.toNat - 1) wid else s.widthAt
    let depths := s.depths ++ [depth]
    let (depth, widthAt, levelcount) ←
      if c = '{' ∧ !q.quoted then do
        let depth := depth + 1
        let (widthAt, levelcount) :=
          if depth > (widthAt.length : Int) then (widthAt ++ [0], s.levelcount ++ [0]) else (widthAt, s.levelcount)
        if depth < 1 then .error .boundsError else
        pure (depth, widthAt, bumpAt levelcount (depth.toNat - 1) 1)
      else pure (depth, widthAt, s.levelcount)
    let q := if c ≠ '\\' ∧ q.backslash then { q with backslash := false } else q
    pure ⟨depth, widthAt, levelcount, strwid, q, depths⟩

def pass1 (tw : Char → Nat) (toks : List Tok) : R Pass1 :=
  toks.foldlM (pass1Step tw) ⟨0, [], [], 0, ⟨false, false, false⟩, []⟩

/-- The `while strwid > n` search for `limit_at`, `base/show.jl:2784-2795`, with
fuel `length(width_at) + 1` (each iteration lowers `limit_at`). -/
def limitSearch (widthAt levelcount : List Nat) (n : Int) : Nat → Int → Int → Int
  | 0, limitAt, _ => limitAt
  | fuel + 1, limitAt, strwid =>
    if strwid > n then
      let limitAt := limitAt - 1
      if limitAt ≤ 1 then limitAt else
      let strwid := strwid - widthAt.getD (limitAt.toNat - 1) 0 + levelcount.getD (limitAt.toNat - 1) 0
      let strwid := if limitAt < widthAt.length then strwid - levelcount.getD limitAt.toNat 0 else strwid
      limitSearch widthAt levelcount n fuel limitAt strwid
    else limitAt

/-- Second pass: keep tokens shallower than `limit_at`, writing `…` on entering
`limit_at`, `base/show.jl:2799-2815`. -/
def pass2 (limitAt : Int) : Int → List (Tok × Int) → List Char
  | _, [] => []
  | prev, (t, di) :: rest =>
    let kept := if di < limitAt then (match t with | .ansi d => d | .ch c => [c]) else []
    let mark := if di > prev ∧ di = limitAt then ['…'] else []
    kept ++ mark ++ pass2 limitAt di rest

/-- `type_depth_limit(str, n; maxdepth)`, `base/show.jl:2726-2816`. -/
def typeDepthLimit (tw : Char → Nat) (str : List Char) (n : Int) (maxdepth : Option Int := none) :
    R (List Char) := do
  let toks := ansiTokens str
  let p ← pass1 tw toks
  let limitAt := match maxdepth with
    | none => limitSearch p.widthAt p.levelcount n (p.widthAt.length + 1) (p.widthAt.length + 1) p.strwid
    | some d => d
  pure (pass2 limitAt 0 (toks.zip p.depths))

end JuliaLean.ShowCov.Truncate

/-!
# `IOContext` (`base/show.jl:332-491`)

A property value is compared with `===`; `PV` is a value with decidable
identity. An `IOContext` stores an underlying (non-`IOContext`) stream and an
`ImmutableDict`, a binding list with the newest binding first; iteration,
`in` and `keys` visit every binding, including shadowed ones.
-/

namespace JuliaLean.ShowCov.IOCtx

open JuliaLean.ShowCov

/-- Property values (compared by identity). -/
inductive PV where
  | bool (b : Bool)
  | int (n : Int)
  | dims (rows cols : Int)
  | obj (id : Nat)
  deriving DecidableEq, Repr

/-- A stream that is not an `IOContext`: its identity, what `get(io, :color, false)`
returns for it (`true` only for a colour `TTY`/`TTYTerminal`), and its
`displaysize`. -/
structure BaseIO where
  id : Nat
  color : Bool
  displaysize : Int × Int
  deriving DecidableEq, Repr

/-- `ImmutableDict{Symbol,Any}`: newest binding first. -/
abbrev IDict := List (String × PV)

/-- An `IO`: a plain stream or `IOContext(io, dict)` over a plain stream. -/
inductive JIO where
  | plain (b : BaseIO)
  | ctx (b : BaseIO) (dict : IDict)
  deriving DecidableEq, Repr

/-- `get(dict, key, default)`: the newest binding. -/
def dget (d : IDict) (k : String) (default : PV) : PV :=
  match d.find? (·.1 == k) with
  | some (_, v) => v
  | none => default

def dhas (d : IDict) (k : String) : Bool := d.any (·.1 == k)

/-- Julia `===` on the modeled property values. Object identity is the stored
object id; immutable scalar values are identical exactly when their payloads
and types agree. -/
def sameIdentity (a b : PV) : Bool := a == b

/-- `ImmutableDict(d, k, v)`: push a binding. -/
def dpush (d : IDict) (k : String) (v : PV) : IDict := (k, v) :: d

/-- The inner constructor `IOContext{IO_t}(io, dict)`, `base/show.jl:336-339`:
an `IOContext` argument is unwrapped to its stream. -/
def mkCtx (io : JIO) (dict : IDict) : JIO :=
  match io with
  | .plain b => .ctx b dict
  | .ctx b _ => .ctx b dict

/-- `ioproperties(io::IO)` and `ioproperties(io::IOContext)`, `base/show.jl:343-344`. -/
def ioproperties : JIO → IDict
  | .plain b => if b.color then [("color", .bool true)] else []
  | .ctx _ d => d

/-- `unwrapcontext(io::IO) = (io,)`, `unwrapcontext(io::IOContext) = (io.io,)`,
`base/show.jl:346-347`. -/
def unwrapcontext : JIO → JIO
  | .plain b => .plain b
  | .ctx b _ => .plain b

/-- `IOContext(io::IO, dict)` and `IOContext(io::IOContext, dict)`,
`base/show.jl:349-355`. -/
def ioContextDict (io : JIO) (dict : IDict) : JIO :=
  match io with
  | .plain b => mkCtx (.plain b) dict
  | .ctx b _ => mkCtx (.plain b) dict

/-- The `convert` methods, `base/show.jl:358-361`: an `IOContext` is returned
as is; another stream is wrapped with its `ioproperties`. -/
def convertCtx (io : JIO) : JIO :=
  match io with
  | .ctx b d => .ctx b d
  | .plain b => ioContextDict (.plain b) (ioproperties (.plain b))

/-- `IOContext(io::IO) = convert(IOContext, io)` and `IOContext{IO_t}(io)`,
`base/show.jl:363-364`. -/
def ioContext1 (io : JIO) : JIO := convertCtx io

/-- `IOContext(io::IO, KV::Pair)`, `base/show.jl:366-369`. -/
def ioContextPair (io : JIO) (kv : String × PV) : JIO :=
  ioContextDict io (dpush (ioproperties io) kv.1 kv.2)

/-- `IOContext(io::IO, context::IO) = IOContext(io, ioproperties(context))`,
`base/show.jl:381`. -/
def ioContextIO (io context : JIO) : JIO := ioContextDict io (ioproperties context)

/-- `IOContext(io::IO, KV::Pair, KVs::Pair...)`, `base/show.jl:456`. -/
def ioContextPairs (io : JIO) : List (String × PV) → JIO
  | [] => io
  | kv :: kvs => ioContextPairs (ioContextPair io kv) kvs

/-- `show(io, ctx::IOContext)`, `base/show.jl:458`; `shownInner` is `show(io, ctx.io)`. -/
def showCtx (shownInner : String) : Out := ["IOContext(", shownInner, ")"]

/-- `pipe_reader(io::IOContext) = io.io`, `pipe_writer`, and `lock`/`unlock`
forwarding, `base/show.jl:460-463`: all act on the wrapped stream. -/
def pipeReader : JIO → JIO := unwrapcontext
def pipeWriter : JIO → JIO := unwrapcontext
def lockTarget : JIO → JIO := unwrapcontext

/-- `in(key_value::Pair, io::IOContext) = in(key_value, io.dict, ===)` and
`in(key_value, io::IO) = false`, `base/show.jl:465-466`: any binding matches. -/
def inWith (identity : PV → PV → Bool) (kv : String × PV) : JIO → Bool
  | .plain _ => false
  | .ctx _ d => d.any (fun e => e.1 == kv.1 && identity e.2 kv.2)

def inCtx (kv : String × PV) (io : JIO) : Bool := inWith sameIdentity kv io

/-- `haskey`, `getindex`, `get`, `keys` on `IOContext` and plain `IO`,
`base/show.jl:467-474`. -/
def haskeyCtx (k : String) : JIO → Bool
  | .plain _ => false
  | .ctx _ d => dhas d k
def getindexCtx (k : String) : JIO → R PV
  | .plain _ => .error (.keyError k)
  | .ctx _ d => match d.find? (·.1 == k) with
    | some (_, v) => .ok v
    | none => .error (.keyError k)
def getCtx (k : String) (default : PV) : JIO → PV
  | .plain _ => default
  | .ctx _ d => dget d k default
def keysCtx : JIO → List String
  | .plain _ => []
  | .ctx _ d => d.map (·.1)

/-- `displaysize(io::IOContext)`, `base/show.jl:476`: the `:displaysize`
property if set (a non-tuple value fails the type assertion), else the stream's. -/
def displaysizeCtx : JIO → R (Int × Int)
  | .plain b => .ok b.displaysize
  | .ctx b d =>
    if dhas d "displaysize" then
      match dget d "displaysize" (.int 0) with
      | .dims r c => .ok (r, c)
      | _ => .error .typeError
    else .ok b.displaysize

/-- The loop of `show_circular(io::IOContext, x)`, `base/show.jl:481-489`:
`d` counts the `:SHOWN_SET` bindings seen, starting at 1. -/
def circularScan (x : PV) : Nat → IDict → Option Out
  | _, [] => none
  | d, (k, v) :: rest =>
    if k = "SHOWN_SET" then
      if v = x then some ["#= circular reference @-" ++ toString d ++ " =#"]
      else circularScan x (d + 1) rest
    else circularScan x d rest

/-- `show_circular(io::IO, x) = false` and `show_circular(io::IOContext, x)`,
`base/show.jl:478-491`: scanning the bindings newest first, the `d`-th
`:SHOWN_SET` binding that is `x` prints `#= circular reference @-d =#`. -/
def showCircular (x : PV) : JIO → Option Out
  | .plain _ => none
  | .ctx _ dict => circularScan x 1 dict

end JuliaLean.ShowCov.IOCtx

/-!
# `show` for scalars, pairs, modules, and small wrappers (`base/show.jl`)

Values printed by methods in other files enter as the text those methods
print. Type names enter as their printed form.
-/

namespace JuliaLean.ShowCov.Values

open JuliaLean.ShowCov

/-! ## `Bool`, `Nothing`, integers -/

/-- `show(io, b::Bool)`, `base/show.jl:1423`; `tiIsBool` is
`nonnothing_nonmissing_typeinfo(io) === Bool` (`base/show.jl:1422`). -/
def showBool (tiIsBool : Bool) (b : Bool) : String :=
  if tiIsBool then (if b then "1" else "0") else (if b then "true" else "false")

/-- `nonnothing_nonmissing_typeinfo(io) = nonmissingtype(nonnothingtype(get(io, :typeinfo, Any)))`,
`base/show.jl:1422`, on a type given as its union components: `Nothing` and
`Missing` are dropped; an empty remainder is `Union{}`. -/
def nonnothingNonmissing (components : List String) : List String :=
  components.filter (fun c => c ≠ "Nothing" ∧ c ≠ "Missing")

/-- `show(io, ::Nothing) = print(io, "nothing")`, `base/show.jl:1424`. -/
def showNothing : String := "nothing"

/-- `show(io, n::Signed) = (write(io, string(n)); nothing)`, `base/show.jl:1425`. -/
def showSigned (n : Int) : String := toString n

/-- Hexadecimal digits of `n`, at least `pad` of them (`string(n, base=16, pad=pad)`). -/
def hexPad (n pad : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (pad - ds.length) '0' ++ ds)

/-- The unsigned integer types by bit size. -/
def uintName (bits : Nat) : String := "UInt" ++ toString bits

/-- `show(io, n::Unsigned)`, `base/show.jl:1426-1436`. `hex` is
`get(io, :hexunsigned, true)`; `tiSame` is `get(io, :typeinfo, Nothing) == typeof(n)`. -/
def showUnsigned (hex tiSame : Bool) (bits n : Nat) : String :=
  if hex then "0x" ++ hexPad n ((bits + 3) / 4)
  else if tiSame then toString n
  else uintName bits ++ "(" ++ toString n ++ ")"

/-- `print(io, n::Unsigned) = print(io, string(n))`, `base/show.jl:1437`. -/
def printUnsigned (n : Nat) : String := toString n

/-- Julia's type for an unsigned hexadecimal literal with `k` digits: the
smallest of `UInt8`..`UInt128` with at least `4k` bits (`BigInt` beyond 32 digits). -/
def hexLiteralBits (k : Nat) : Nat :=
  if k ≤ 2 then 8 else if k ≤ 4 then 16 else if k ≤ 8 then 32 else if k ≤ 16 then 64
  else if k ≤ 32 then 128 else 0

/-- Value of one lowercase hexadecimal digit. -/
def hexDigitVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

/-- Value of a hexadecimal digit string. -/
def hexValue (s : List Char) : Nat :=
  s.foldl (fun acc c => 16 * acc + hexDigitVal c) 0

/-! ## `Pair` -/

/-- What `show(io, p::Pair)` needs about a pair: whether its type is tight
(`has_tight_type`), whether `get(io, :typeinfo, Any) == typeof(p)`, whether
`:compact` is set, and, for each element under its typeinfo, whether it is
delimited and its printed text. -/
structure PairInfo where
  firstTight : Bool
  secondTight : Bool
  tiIsPairType : Bool
  compact : Bool
  firstDelimited : Bool
  secondDelimited : Bool
  firstText : String
  secondText : String
  /-- `show(io, typeof(p))` and `show(io, (p.first, p.second))`. -/
  typeText : String
  tupleText : String

/-- `has_tight_type(p)`, `base/show.jl:1439-1441`. -/
def hasTightType (p : PairInfo) : Bool := p.firstTight && p.secondTight

/-- `isdelimited(io, x) = true`, `isdelimited(io, x::Function) = !isoperator(Symbol(x))`,
`isdelimited(io, p::Pair) = !(has_tight_type(p) || get(io, :typeinfo, Any) == typeof(p))`,
`base/show.jl:1443-1448`. -/
def isdelimitedAny : Bool := true
def isdelimitedFunction (isOperator : Bool) : Bool := !isOperator
def isdelimitedPair (p : PairInfo) : Bool := !(hasTightType p || p.tiIsPairType)

/-- `gettypeinfos(io, p)`, `base/show.jl:1450-1455`: the field types of the
`:typeinfo` when `p isa typeinfo <: Pair`, else `Any => Any`. -/
def gettypeinfos (pIsaTi tiSubPair : Bool) (fieldTypes : String × String) : String × String :=
  if pIsaTi && tiSubPair then fieldTypes else ("Any", "Any")

/-- `show_pairtyped(io, p)`, `base/show.jl:1469-1472`. -/
def showPairtyped (p : PairInfo) : Out := [p.typeText, p.tupleText]

/-- `show(io, p::Pair)`, `base/show.jl:1457-1467`. -/
def showPair (p : PairInfo) : Out :=
  if isdelimitedPair p then showPairtyped p else
  let elt (delim : Bool) (t : String) : Out := (if delim then [] else ["("]) ++ [t] ++ (if delim then [] else [")"])
  elt p.firstDelimited p.firstText ++ [if p.compact then "=>" else " => "] ++ elt p.secondDelimited p.secondText

/-! ## Modules -/

/-- A module: its name, whether its name is a valid identifier (`show_sym`
prints it bare) and its parent; `none` marks `Main`, `Base`, `Core` or a
module that is its own parent. -/
inductive Mod where
  | top (name : String)
  | sub (name : String) (parent : Mod)
  deriving DecidableEq, Repr

/-- `show_sym(io, nameof(m))` for a module name; `symText` renders names. -/
def printFullname (symText : String → String) : Mod → Out
  | .top n => [symText n]
  | .sub n p => printFullname symText p ++ [".", symText n]

/-- `show(io, m::Module)`, `base/show.jl:1474-1480`: a root module prints its
name, others their full dotted path (`print_fullname`, `base/show.jl:1484-1493`). -/
def showModule (symText : String → String) (isRoot : Bool) (m : Mod) : Out :=
  if isRoot then [match m with | .top n => n | .sub n _ => n] else printFullname symText m

/-- `fullname(m)`, joined with `"."`. -/
def fullnameJoin : Mod → String
  | .top n => n
  | .sub n p => fullnameJoin p ++ "." ++ n

/-! ## Small wrappers -/

/-- `show(io, ::UndefInitializer) = print(io, "UndefInitializer()")`, `base/show.jl:3228`. -/
def showUndef : String := "UndefInitializer()"

/-- `show(io, ::MIME"text/plain", u::UndefInitializer)`, `base/show.jl:6-10`. -/
def showUndefPlain (compact : Bool) : Out :=
  [showUndef] ++ (if compact then [] else [": array initializer with undefined values"])

/-- `show(io, ::MIME"text/plain", r::AbstractRange) = show(io, r)`, and the
`UnitRange` method that appends `" (empty range)"`, `base/show.jl:14-21`. -/
def showRangePlain (shown : String) : Out := [shown]
def showUnitRangePlain (shown : String) (compact isEmpty : Bool) : Out :=
  [shown] ++ (if !compact && isEmpty then [" (empty range)"] else [])

/-- `show(io, ::MIME"text/plain", r::LinRange)` and `LogRange`, `base/show.jl:23-39`:
an empty range shows compactly; otherwise the summary, `":\n"`, and the
`print_range` output. -/
def showLinLogPlain (isEmpty : Bool) (shown summary printed : String) : Out :=
  if isEmpty then [shown] else [summary, ":", "\n", printed]

/-- `show(io, ::MIME"text/plain", c::ComposedFunction) = show(io, c)`, also for
`Returns`, `Splat`, `OpaqueClosure` (`base/show.jl:75-77, 3450-3452`). -/
def showPlainForward (shown : String) : Out := [shown]

/-- `show(io, ::MIME"text/plain", t::Task)`, `base/show.jl:294-300`. -/
def showTaskPlain (shown : String) (failed : Bool) (exceptionText : String) : Out :=
  [shown] ++ (if failed then ["\n", exceptionText] else [])

/-- `show(io, src::Core.CancellationTokenSource)`, `base/show.jl:304-319`;
`sev` is `cancel_severity(src)` (`none` for `nothing`), `reprR` is `repr(r)`. -/
def showCTS (sev : Option UInt8) (reprR : String) (nparents : Int) : Out :=
  ["CancellationTokenSource("] ++
  [match sev with
   | none => "active"
   | some r => if r = 1 then "cancelled" else if r = 3 then "cancelled, abandon external"
       else if r = 4 then "cancelled, abandon all" else "cancelled, severity " ++ reprR] ++
  (if nparents > 0 then [", ", toString nparents, if nparents = 1 then " parent" else " parents"] else []) ++
  [")"]

/-- `print(io::IO, s::Symbol) = (write(io,s); nothing)`, `base/show.jl:322`: the
name's bytes. -/
def printSymbol (name : String) : String := name

/-- `show(io, ::MIME"text/plain", ::Core.TypeofBottom) = print(io, "Union{}")`,
`base/show.jl:615`. -/
def showBottomPlain : String := "Union{}"

/-- `show(io, ii::IncludeInto)` and `show(io, ei::Core.EvalInto)`,
`base/show.jl:3539-3555`: `M.include` / `M.eval` when the object is the
module's own binding, else `show_default`. -/
def showInto (isOwn : Bool) (modText field defaultText : String) : Out :=
  if isOwn then [modText, "." ++ field] else [defaultText]

/-- `show(io, ::MIME"text/plain", opt::JLOptions)`, `base/show.jl:278-292`: one
line per field, `repr(value)` after `" = "`, commas between. Pointer fields
are shown as their strings (`""` for `C_NULL`). -/
def showJLOptions (fields : List (String × String)) : Out :=
  let n := fields.length
  ["JLOptions(", "\n"] ++
  ((fields.zipIdx).flatMap (fun ((f, v), i) =>
    ["  ", f, " = ", v, if i + 1 < n then "," else "", "\n"])) ++ [")"]

/-- `show(io, ::MIME"text/plain", ti::TermInfo)` lives in `TermInfo`; the
`summary(io, t::AbstractSet)` header, `base/show.jl:235-239`. -/
def summarySet (typeArg : String) (n : Nat) : Out :=
  [typeArg, " with ", toString n, if n = 1 then " element" else " elements"]

/-- `show(io, x) = show_default(io, x)`, `show(x) = show(stdout, x)`,
`show_default(io, x) = _show_default(io, inferencebarrier(x))`,
`base/show.jl:520-525`: all print what `_show_default` prints. -/
def showFallback (defaultText : String) : String := defaultText

/-- A field of a struct shown by `_show_default`: undefined, or its shown text. -/
inductive Field where
  | undef
  | val (shown : String)

/-- `_show_default(io, x)`, `base/show.jl:527-568`. `fields` are the fields
when `nf != 0 || nb == 0`; `bits` is `none` in that case, else the object's
bytes (little-endian) and `Core.bitsizeof`. `circular` is what `show_circular(io, x)`
printed (`some marker` when it returned `true`). -/
def showDefault (typeText : String) (circular : Option String) (fields : List Field)
    (bits : Option (List UInt8 × Nat)) : Out :=
  [typeText, "("] ++
  (match bits with
   | none =>
     if let some marker := circular then [marker] else
     let shown := fields.map (fun f => match f with | .undef => "#undef" | .val s => s)
     (shown.zipIdx.flatMap (fun (s, i) => [s] ++ (if i + 1 < fields.length then [", "] else [])))
   | some (bytes, nbits) =>
     let nbytes := (nbits + 7) / 8
     ["0x"] ++ ((List.range nbytes).reverse.map (fun i =>
       let byte := (bytes.getD i 0).toNat
       if i = nbytes - 1 ∧ nbits % 8 ≠ 0 then
         hexPad (byte % 2 ^ (nbits % 8)) ((nbits % 8 + 3) / 4)
       else hexPad byte 2))) ++ [")"]

end JuliaLean.ShowCov.Values

/-!
# Delimited lists, summaries, `showarg`, bit chunks, `dump`, `alignment`
(`base/show.jl:1562-1626, 2990-3440`)

Elements are given as their shown text (`none` for an unassigned slot).
-/

namespace JuliaLean.ShowCov.Containers

open JuliaLean.ShowCov

/-! ## `show_delim_array` -/

/-- The `while true` loop of `show_delim_array(io, itr::Union{AbstractArray,SimpleVector}, ...)`,
`base/show.jl:1570-1585`, from index `i` to `l` (fuel `l - i + 1`). -/
def delimArrayLoop (elt : Int → Option String) (delim : String) (delimOne : Bool) (l : Int) :
    Nat → Int → Bool → Out
  | 0, _, _ => []
  | fuel + 1, i, first =>
    let shown := match elt i with | some s => s | none => "#undef"
    if i = l then [shown] ++ (if delimOne && first then [delim] else [])
    else [shown, delim, " "] ++ delimArrayLoop elt delim delimOne l fuel (i + 1) false

/-- `show_delim_array(io, itr::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one, i1, l)`,
`base/show.jl:1562-1589`. `circular` is what `show_circular(io, itr)` printed. -/
def showDelimArray (elt : Int → Option String) (op delim cl : String) (delimOne : Bool)
    (circular : Option String) (i1 l : Int) : Out :=
  [op] ++
  (match circular with
   | some m => [m]
   | none => if l ≥ i1 then delimArrayLoop elt delim delimOne l (l - i1 + 1).toNat i1 true else []) ++
  [cl]

/-- The element loop of `show_delim_array(io, itr, ...)`, `base/show.jl:1604-1620`:
`count` is `i1 - 1` (after the skipping loop leaves `i1` at `min(i1, 1)`); the
loop stops after the last element or once `i1 > n`. -/
def delimIterLoop (delim : String) (delimOne : Bool) (n : Int) : Int → Bool → List String → Out
  | _, _, [] => []
  | count, first, x :: rest =>
    let count := count + 1
    if rest.isEmpty ∨ count > n then [x] ++ (if delimOne && first then [delim] else [])
    else [x, delim, " "] ++ delimIterLoop delim delimOne n count false rest

/-- `show_delim_array(io, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int))`,
`base/show.jl:1591-1623`, for an iterator producing `xs`: skips `i1 - 1`
elements, then shows elements until the iterator ends or `n` have been shown. -/
def showDelimIter (xs : List String) (op delim cl : String) (delimOne : Bool)
    (circular : Option String) (i1 : Int) (n : Int) : Out :=
  [op] ++
  (match circular with
   | some m => [m]
   | none => delimIterLoop delim delimOne n (min i1 1 - 1) true (xs.drop (i1 - 1).toNat)) ++
  [cl]

/-- `show(io, t::Tuple)`, `show(io, v::SimpleVector)`, `show(io, z::Iterators.Zip)`,
`base/show.jl:1625-1626, 3396`. -/
def showTuple (xs : List String) (circular : Option String) : Out :=
  showDelimIter xs "(" "," ")" true circular 1 (2 ^ 63 - 1)
def showSvec (xs : List String) (circular : Option String) : Out :=
  showDelimArray (fun i => if 1 ≤ i then xs[(i - 1).toNat]? else none) "svec(" "," ")" false circular 1 xs.length
def showZip (xs : List String) (circular : Option String) : Out :=
  showDelimIter xs "zip(" "," ")" false circular 1 (2 ^ 63 - 1)

/-- `show(io, e::Iterators.Enumerate)`, `base/show.jl:3391-3395`. -/
def showEnumerate (itr : String) : Out := ["enumerate(", itr, ")"]

/-! ## Summaries -/

/-- `summary(io, x) = print(io, typeof(x))` and `summary(x)` (the string),
`base/show.jl:3249-3254`. -/
def summaryAny (typeText : String) : String := typeText

/-- `dims2string(d)`, `base/show.jl:3258-3260`. -/
def dims2string (d : List Int) : String :=
  match d with
  | [] => "0-dimensional"
  | [n] => toString n ++ "-element"
  | _ => "×".intercalate (d.map toString)

/-- An axis: `Base.OneTo(n)`, an `IdentityUnitRange`/`Slice` over `indices`
(printed as `string(i.indices)`), or another range printed as `text`. -/
inductive Axis where
  | oneTo (n : Int)
  | wrapped (indicesText : String) (len : Int)
  | other (text : String) (len : Int)

def Axis.len : Axis → Int
  | .oneTo n => n
  | .wrapped _ l => l
  | .other _ l => l

/-- `_indsstring(i) = string(i)` and the `IdentityUnitRange`/`Slice` method,
`base/show.jl:3263-3264`; `Base.OneTo(n)` prints `Base.OneTo(n)`. -/
def indsstring : Axis → String
  | .oneTo n => "Base.OneTo(" ++ toString n ++ ")"
  | .wrapped t _ => t
  | .other t _ => t

/-- `inds2string(inds) = join(map(_indsstring,inds), '×')`, `base/show.jl:3262`. -/
def inds2string (inds : List Axis) : String := "×".intercalate (inds.map indsstring)

def isOneTo : Axis → Bool
  | .oneTo _ => true
  | _ => false

/-- `summary(io, a::AbstractArray) = array_summary(io, a, axes(a))` and both
`array_summary` methods, `base/show.jl:3267-3276`. -/
def arraySummary (inds : List Axis) (showargText : String) : Out :=
  [dims2string (inds.map Axis.len), " ", showargText] ++
  (if inds.all isOneTo then [] else [" with indices ", inds2string inds])

/-- `summary(io, mref::GenericMemoryRef)`, `base/show.jl:3279-3284`;
`offset = Core.memoryrefoffset(mref)` (1-based). -/
def summaryMemoryRef (memLength offset : Int) (showargText : String) : Out :=
  [toString (memLength - offset + 1), "-element ", showargText]

/-- `summary(io, f::Function) = show(io, MIME"text/plain"(), f)`, `base/show.jl:3287`. -/
def summaryFunction (plainText : String) : String := plainText

/-! ## `showarg` -/

/-- `showarg(io, x, toplevel)` fallback and the `Array{Union{}}` method,
`base/show.jl:3335-3347`. -/
def showargAny (typeText : String) (toplevel : Bool) : Out :=
  (if toplevel then [] else ["::"]) ++ [typeText]
/-- `showarg(io, T::Type, toplevel)`, `base/show.jl:3339-3342`. -/
def showargType (typeText : String) (toplevel : Bool) : Out :=
  (if toplevel then [] else ["::"]) ++ ["Type{", typeText, "}"]

/-- An index of a `SubArray`: a `Slice` or another index printed as `text`. -/
inductive Ind where
  | slice
  | other (text : String)

/-- `showindices(io, inds...)`, `base/show.jl:3358-3362`. -/
def showindices : List Ind → Out
  | [] => []
  | .slice :: rest => [", :"] ++ showindices rest
  | .other t :: rest => [", ", t] ++ showindices rest

/-- `showarg(io, v::SubArray, toplevel)`, `base/show.jl:3350-3357`; `parentArg`
is `showarg(io, parent(v), false)`. -/
def showargSubArray (parentArg : Out) (inds : List Ind) (eltype : String) (toplevel : Bool) : Out :=
  ["view("] ++ parentArg ++ showindices inds ++ [")"] ++
  (if toplevel then [" with eltype ", eltype] else [])

/-- `showarg(io, r::ReshapedArray, toplevel)`, `base/show.jl:3364-3373`. -/
def showargReshaped (parentArg : Out) (dims : List Int) (eltype : String) (toplevel : Bool) : Out :=
  ["reshape("] ++ parentArg ++
  (if dims.isEmpty then [] else [", ", ", ".intercalate (dims.map toString)]) ++ [")"] ++
  (if toplevel then [" with eltype ", eltype] else [])

/-- `showarg` for `NonReshapedReinterpretArray` and `ReshapedReinterpretArray`,
`base/show.jl:3375-3387`. -/
def showargReinterpret (T : String) (parentArg : Out) : Out :=
  ["reinterpret(", T, ", "] ++ parentArg ++ [")"]
def showargReinterpretReshape (T : String) (parentArg : Out) (eltype : String) (toplevel : Bool) : Out :=
  ["reinterpret(reshape, ", T, ", "] ++ parentArg ++ [")"] ++
  (if toplevel then [" with eltype ", eltype] else [])

/-- The three `showarg` methods for `Iterators.Pairs`, `base/show.jl:3399-3409`. -/
def showargPairsArray (T : String) : Out := ["pairs(IndexLinear(), ::", T, ")"]
def showargPairsNamedTuple : Out := ["pairs(::NamedTuple)"]
def showargPairsGeneric (D I : String) : Out := ["Iterators.Pairs(::", D, ", ::", I, ")"]

/-! ## Bit chunks -/

/-- `print_bit_chunk(io, c::UInt64, l = 64)`, `base/show.jl:3415-3423`, and the
`stdout` forms (`:3425-3426`). -/
def printBitChunk (c : Nat) (l : Nat := 64) : List Char :=
  (List.range l).flatMap (fun s =>
    [if (c / 2 ^ s) % 2 = 1 then '1' else '0'] ++ (if (s + 1) % 8 = 0 then [' '] else []))

/-- `bitshow(io, B::BitArray)` and `bitstring(B) = sprint(bitshow, B)`,
`base/show.jl:3428-3440`: chunks are the 64-bit words of `B.chunks`, `len`
is `length(B)`. -/
def bitshow (chunks : List Nat) (len : Nat) : List Char :=
  if len = 0 then [] else
  let l := (len - 1) % 64 + 1
  (chunks.dropLast.flatMap (fun c => printBitChunk c ++ [':', ' '])) ++ printBitChunk (chunks.getLastD 0) l

/-- The bits of a chunk list in index order, with `l` bits from the last chunk. -/
def bitsOf (chunks : List Nat) (len : Nat) : List Char :=
  (List.range len).map (fun i => if (chunks.getD (i / 64) 0 / 2 ^ (i % 64)) % 2 = 1 then '1' else '0')

/-! ## `dump` -/

/-- What `dump` sees in a value: a leaf printed in one line, a structure with
named fields (`none` for an undefined field), or a `Function` (printed
with its type and no fields). -/
inductive DV where
  | leaf (line : String)
  | node (header : String) (fields : List (String × Option DV))
  | func (line : String)

/-- `dump(io::IOContext, x, n, indent)` for a field structure and leaves,
`base/show.jl:3010-3047`: lines with their nesting depth (the header line has
depth 0, a field of a depth-`k` node has depth `k + 1`). Fields are printed
only while `n > 0`. -/
def dumpLines : Nat → Nat → DV → List (Nat × String)
  | _, d, .leaf s => [(d, s)]
  | _, d, .func s => [(d, s)]
  | 0, d, .node h _ => [(d, h)]
  | n + 1, d, .node h fs =>
    (d, h) :: fs.attach.flatMap (fun ⟨(name, v), _⟩ =>
      match v with
      | none => [(d + 1, name ++ ": #undef")]
      | some v => dumpLines n (d + 1) v)

/-- `dump(io, x; maxdepth = 8)`, `base/show.jl:3130-3133`, and `dump(arg; maxdepth)`
(`:3163-3167`, to `stdout` with `:limit => true`). -/
def dumpTop (maxdepth : Nat) (x : DV) : List (Nat × String) := dumpLines maxdepth 0 x

/-- `dump_elts(io, x::Array, n, indent, i0, i1)` (`base/show.jl:3049-3059`) and
the `:limit` choice of `dump(io, x::Array, ...)` (`:3061-3084`): the element
indices shown. -/
def dumpArrayIndices (limit : Bool) (lx : Nat) : List Nat :=
  if limit then
    (List.range (if lx ≤ 10 then lx else 5)).map (· + 1) ++
    (if lx > 10 then (List.range 5).map (· + (lx - 4)) else [])
  else (List.range lx).map (· + 1)

/-- One-line `dump` methods, `base/show.jl:3043-3047`. -/
def dumpModule (m : String) : String := "Module " ++ m
def dumpString (shown : String) : String := "String " ++ shown
def dumpSymbol (name : String) : String := "Symbol " ++ name
def dumpUnion (printed : String) : String := printed
def dumpPtr (printed : String) : String := printed

/-- `dump(io::IOContext, x::SimpleVector, n, indent)` header, `base/show.jl:2990-3008`. -/
def dumpSvecHeader (isEmpty : Bool) : String := if isEmpty then "empty SimpleVector" else "SimpleVector"

/-- The header of `dump(io::IOContext, x::DataType, n, indent)`, `base/show.jl:3087-3098`. -/
def dumpTypeHeader (isStruct isMutable isTuple isPrimitive isAbstract isAny : Bool)
    (typeText supertypeText : String) : String :=
  let isStruct := isStruct && !isTuple
  let isMut := isStruct && isMutable
  (if isMut then "mutable " else "") ++ (if isStruct then "struct " else "") ++
  (if isPrimitive then "primitive type " else "") ++ (if isAbstract then "abstract type " else "") ++
  typeText ++ (if isAny then "" else " <: " ++ supertypeText)

/-! ## `alignment` -/

/-- `alignment(io, x::Any) = (0, alignment_from_show(io, x))`, and the
`Number`/`Integer` methods `(alignment_from_show(io, x), 0)`, `base/show.jl:3191-3193`;
`w` is `textwidth(sprint(show, x, context=nocolor(io)))` (`alignment_from_show`,
`base/show.jl:3170-3173`). -/
def alignmentAny (w : Nat) : Int × Int := (0, w)
def alignmentNumber (w : Nat) : Int × Int := (w, 0)

/-- The captures of `match(r"^(.*?)((?:[\.eEfF].*)?)$", s)`: the lazy first
group stops at the first `.`, `e`, `E`, `f` or `F` (or takes everything). -/
def splitRealAt (s : List Char) : List Char × List Char :=
  (s.takeWhile (fun c => c ∉ ['.', 'e', 'E', 'f', 'F']), s.dropWhile (fun c => c ∉ ['.', 'e', 'E', 'f', 'F']))

/-- `alignment(io, x::Real)`, `base/show.jl:3194-3199`; `tw` is `textwidth`. -/
def alignmentReal (tw : Char → Nat) (s : List Char) : Int × Int :=
  let (a, b) := splitRealAt s
  ((a.map tw).sum, (b.map tw).sum)

/-- The captures of `match(r"^(.*?/)(/.*)$", s)`: split after the first `/`
that is followed by another `/`; `none` if there is no `//`. -/
def splitRational : List Char → Option (List Char × List Char)
  | [] => none
  | [_] => none
  | c :: d :: rest =>
    if c = '/' ∧ d = '/' then some (['/'], '/' :: rest)
    else (splitRational (d :: rest)).map (fun (a, b) => (c :: a, b))

/-- `alignment(io, x::Rational)`, `base/show.jl:3206-3211`. -/
def alignmentRational (tw : Char → Nat) (s : List Char) : Int × Int :=
  match splitRational s with
  | none => ((s.map tw).sum, 0)
  | some (a, b) => ((a.map tw).sum, (b.map tw).sum)

/-- The captures of `match(r"^(.*[^ef][\+\-])(.*)$", s)`: the greedy first
group ends at the last `+`/`-` that has a preceding character other than
`e`/`f`; `none` if there is none. -/
def splitComplex (s : List Char) : Option (List Char × List Char) :=
  let n := s.length
  let ok (k : Nat) : Bool :=
    1 ≤ k && k < n && (s.getD k ' ' = '+' || s.getD k ' ' = '-') &&
      s.getD (k - 1) ' ' ≠ 'e' && s.getD (k - 1) ' ' ≠ 'f'
  match ((List.range n).filter ok).getLast? with
  | some k => some (s.take (k + 1), s.drop (k + 1))
  | none => none

/-- `alignment(io, x::Complex)`, `base/show.jl:3200-3205`. -/
def alignmentComplex (tw : Char → Nat) (s : List Char) : Int × Int :=
  match splitComplex s with
  | none => ((s.map tw).sum, 0)
  | some (a, b) => ((a.map tw).sum, (b.map tw).sum)

/-- `alignment(io, x::Pair)`, `base/show.jl:3213-3224`. -/
def alignmentPair (fullwidth : Int) (delimited : Bool) (firstWidth : Int) (firstDelimited compact : Bool) :
    Int × Int :=
  if !delimited then
    let left := firstWidth + (if firstDelimited then 0 else 2) + (if compact then 0 else 1)
    (left + 1, fullwidth - left - 1)
  else (0, fullwidth)

/-- `nocolor(io) = IOContext(io, :color => false)`, `base/show.jl:3169`: the
property list with `:color => false` pushed. -/
def nocolor (props : List (String × String)) : List (String × String) := ("color", "false") :: props

end JuliaLean.ShowCov.Containers

namespace JuliaLean.base.show

open JuliaLean
open JuliaLean.base.dict (ImmutableDict ValueConv DictResult DictError)
open JuliaLean.base.pair (Pair)
open JuliaLean.base.expr (Value LeafOps egal isNothing isFalse is_expr is_expr_n)

/-- A Julia `Symbol`, by its name. -/
abbrev Sym := String
/-- The bytes of a Julia `String`. -/
abbrev Bytes := List UInt8
/-- The UTF-8 bytes of a string or character literal. -/
def lit (s : String) : Bytes := s.toUTF8.toList
/-- An `Int` literal. -/
def i64 (z : Int) : JInt64 := JInt.wrap .i64 z

/-- Exceptions thrown by the modelled methods. -/
inductive ShowError where
  | jl (e : JlError)
  | errorException (message : String)
  | assertionError (message : String)
  /-- `KeyError` and failed `convert` calls of the `base/dict.jl` `ImmutableDict` model. -/
  | dict (e : DictError)
  | sort (e : JuliaLean.base.sort.SortException)
  /-- A failed type assertion `x::T`, a non-`Bool` condition, or `isa(x, T)` with a non-type `T`. -/
  | typeError
  /-- `StringIndexError` of indexing a string at an invalid index. -/
  | stringIndexError
  /-- `UndefRefError` of reading an unassigned array element. -/
  | undefRefError

/-- `Any` values stored in an `IOContext` (`V`), in terms of Julia types `Ty`. -/
structure AnyOps (V Ty : Type) where
  ofBool : Bool → V
  /-- `v::Bool`; `none` when `v` is not a `Bool`. -/
  asBool : V → Option Bool
  ofType : Ty → V
  /-- `v::Type`; `none` when `v` is not a type. -/
  asType : V → Option Ty
  /-- `v::Tuple{Int,Int}`. -/
  asDims : V → Option (JInt64 × JInt64)
  /-- `===`. -/
  egal : V → V → Bool

/-- Julia types and the type-level operations show.jl uses. -/
structure TypeOps (m : Type → Type) (Ty : Type) where
  any : Ty
  nothing : Ty
  bool : Ty
  /-- The `UnionAll` type `Pair`. -/
  pair : Ty
  /-- The type `Tuple`. -/
  tuple : Ty
  /-- The BitInteger types. -/
  bitInteger : IntTy → Ty
  /-- `==` on types. -/
  eq : Ty → Ty → m Bool
  /-- `===` on types. -/
  egal : Ty → Ty → Bool
  /-- `<:`. -/
  subtype : Ty → Ty → m Bool
  /-- `fieldtype(T, i)`; `none` when it throws (`BoundsError`). -/
  fieldtype : Ty → JInt64 → Option Ty
  /-- `T.parameters[i]` of a `DataType`. -/
  parameter : Ty → Nat → Ty
  /-- `nonnothingtype(T)` of `base/some.jl` (no model). -/
  nonnothingtype : Ty → m Ty
  /-- `nonmissingtype(T)` of `base/missing.jl`, loaded after show.jl. -/
  nonmissingtype : Ty → m Ty

/-- The `base/io.jl` stream methods called on an underlying stream `Io`. -/
structure IOPrims (m : Type → Type) (Io V : Type) where
  /-- `write(io, s)` of a `String`, `Symbol` or `Char`: appends the bytes. -/
  write : Io → Bytes → m Unit
  lock : Io → m Unit
  unlock : Io → m Unit
  /-- The stream type's own `get(io, key, default)` method: `some v` when it returns `v` rather
  than `default`. Every stream type without its own method uses show.jl's fallback
  `get(io::IO, key, default) = default`, i.e. `fun _ _ => none`. -/
  get : Io → Sym → Option V
  /-- `displaysize(io)::Tuple{Int,Int}` of the stream. -/
  displaysize : Io → m (JInt64 × JInt64)

/-- Stream methods for a stream type without `lock`/`unlock` methods of its own: the
`base/io.jl` fallbacks `lock(::IO) = nothing` and `unlock(::IO) = nothing`, run in `m` through
`liftIO`. -/
def IOPrims.ofIO {m : Type → Type} {Io V World : Type} (liftIO : {α : Type} → JuliaLean.base.io.M World α → m α)
    (write : Io → Bytes → m Unit) (get : Io → Sym → Option V) (displaysize : Io → m (JInt64 × JInt64)) :
    IOPrims m Io V where
  write := write
  lock io := liftIO (JuliaLean.base.io.lock io)
  unlock io := liftIO (JuliaLean.base.io.unlock io)
  get := get
  displaysize := displaysize

/-- An `IOContext{IO_t}`; the inner constructor guarantees `io` is not itself an `IOContext`. -/
structure IOContext (Io V : Type) where
  io : Io
  dict : ImmutableDict Sym V

/-- A stream argument `io::IO`: a plain stream or an `IOContext`. -/
inductive JIO (Io V : Type) where
  | plain (io : Io)
  | context (c : IOContext Io V)

/-- `printstyled(io, xs...; color, bold)` (`base/util.jl`, loaded after show.jl); each argument is
given as its `print` call on the stream `printstyled` passes. -/
abbrev PrintStyled (m : Type → Type) (Io V : Type) := JIO Io V → List (JIO Io V → m Unit) → Sym → Bool → m Unit

/-- `String` operations of `base/strings` on the bytes of a `String`. -/
structure BytesOps (m : Type → Type) where
  /-- `findfirst(c, str)`. -/
  findfirst : Char → Bytes → Option JInt64
  /-- `prevind(str, i, n)`. -/
  prevind : Bytes → JInt64 → JInt64 → JInt64
  lastindex : Bytes → JInt64
  /-- `str[i:j]`; throws on invalid indices. -/
  slice : Bytes → JInt64 → JInt64 → m Bytes
  endswith : Bytes → Bytes → Bool

section
variable {m : Type → Type} [Monad m] [MonadExceptOf ShowError m] {Io V Ty : Type}

def throwShow {α : Type} (e : ShowError) : m α := throwThe ShowError e

def ofJl {α : Type} : Jl α → m α
  | .ok a => pure a
  | .error e => throwShow (.jl e)

def ofDict {α : Type} : DictResult α → m α
  | .ok a => pure a
  | .error e => throwShow (.dict e)

/-- `x::Bool` of a `get(io, key, default::Bool)` result. -/
def assertBool (a : AnyOps V Ty) : V ⊕ Bool → m Bool
  | .inl v => match a.asBool v with
    | some b => pure b
    | none => throwShow .typeError
  | .inr b => pure b

/-- `x::Type` of a `get(io, key, default::Type)` result. -/
def assertType (a : AnyOps V Ty) : V ⊕ Ty → m Ty
  | .inl v => match a.asType v with
    | some t => pure t
    | none => throwShow .typeError
  | .inr t => pure t

/-- `isequal` on `Symbol` keys (`===`). -/
def symEq (k q : Sym) : Bool := k == q

/-- `convert(Any, x)` of a `Bool` stored in an `ImmutableDict{Symbol,Any}`. -/
def boolConv (a : AnyOps V Ty) : ValueConv Bool V := ⟨fun b => some (a.ofBool b), fun b => .ok (a.ofBool b)⟩
/-- `convert(Any, T)` of a type stored in an `ImmutableDict{Symbol,Any}`. -/
def typeConv (a : AnyOps V Ty) : ValueConv Ty V := ⟨fun t => some (a.ofType t), fun t => .ok (a.ofType t)⟩

/--
Julia source: base/show.jl:3226-3227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const undef_ref_str = "#undef"

```
-/
def undef_ref_str : String := "#undef"

/--
Julia source: base/show.jl:460-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_reader(io::IOContext) = io.io
pipe_writer(io::IOContext) = io.io
lock(io::IOContext) = lock(io.io)
unlock(io::IOContext) = unlock(io.io)

```
-/
def pipe_reader (io : IOContext Io V) : Io := io.io
def pipe_writer (io : IOContext Io V) : Io := io.io
def lock_IOContext (p : IOPrims m Io V) (io : IOContext Io V) : m Unit := p.lock io.io
def unlock_IOContext (p : IOPrims m Io V) (io : IOContext Io V) : m Unit := p.unlock io.io

/-! ## Callees in earlier files

`IOContext <: AbstractPipe`, so `base/io.jl` forwards `write` on an `IOContext` to
`pipe_writer(io)`. `base/strings/io.jl` defines `print(io, s::String) = (write(io, s); nothing)`,
`print(io, c::Char) = (write(io, c); nothing)` and
`print(io, xs...) = (lock(io); try for x in xs print(io, x) end finally unlock(io) end; nothing)`. -/

/-- `write(io, s)`. -/
def write (p : IOPrims m Io V) : JIO Io V → Bytes → m Unit
  | .plain io, s => p.write io s
  | .context c, s => p.write (pipe_writer c) s

/-- `print(io, s)` of a `String` or `Char` literal. -/
def printStr (p : IOPrims m Io V) (io : JIO Io V) (s : String) : m Unit := write p io (lit s)

/-- `print(io, s::String)`. -/
def printBytes (p : IOPrims m Io V) (io : JIO Io V) (s : Bytes) : m Unit := write p io s

/-- `lock(io)`. -/
def lockIO (p : IOPrims m Io V) : JIO Io V → m Unit
  | .plain io => p.lock io
  | .context c => lock_IOContext p c

/-- `unlock(io)`. -/
def unlockIO (p : IOPrims m Io V) : JIO Io V → m Unit
  | .plain io => p.unlock io
  | .context c => unlock_IOContext p c

/-- `print(io, xs...)`; each element is given as its `print(io, x)` call. -/
def printAll (p : IOPrims m Io V) (io : JIO Io V) (xs : List (m Unit)) : m Unit := do
  lockIO p io
  tryCatchThe ShowError (do for x in xs do x) (fun e => do unlockIO p io; throwThe ShowError e)
  unlockIO p io

/--
Julia source: base/show.jl:465-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(key_value::Pair, io::IOContext) = in(key_value, io.dict, ===)
in(key_value::Pair, io::IO) = false
haskey(io::IOContext, key) = haskey(io.dict, key)
haskey(io::IO, key) = false
getindex(io::IOContext, key) = getindex(io.dict, key)
getindex(io::IO, key) = throw(KeyError(key))
get(io::IOContext, key, default) = get(io.dict, key, default)
get(io::IO, key, default) = default
keys(io::IOContext) = keys(io.dict)
keys(io::IO) = keys(ImmutableDict{Symbol,Any}())

```
-/
def in_IOContext {Q W : Type} (eqKey : Sym → Q → Bool) (egal : W → V → Bool) (key_value : Q × W)
    (io : IOContext Io V) : m Bool := do
  match ← ofDict (JuliaLean.base.dict.immutableIn eqKey (fun w v => .ok (some (egal w v))) key_value io.dict) with
  | some b => pure b
  | none => throwShow .typeError
def in_IO {Q W : Type} (_key_value : Q × W) (_io : Io) : Bool := false
def haskey_IOContext {Q : Type} (eqKey : Sym → Q → Bool) (io : IOContext Io V) (key : Q) : Bool :=
  JuliaLean.base.dict.immutableHasKey eqKey io.dict key
def haskey_IO {Q : Type} (_io : Io) (_key : Q) : Bool := false
def getindex_IOContext {Q : Type} (eqKey : Sym → Q → Bool) (io : IOContext Io V) (key : Q) : m V :=
  ofDict (JuliaLean.base.dict.immutableGetindex eqKey io.dict key)
def getindex_IO {Q : Type} (_io : Io) (_key : Q) : m V := throwShow (.dict .keyError)
def get_IOContext {Q D : Type} (eqKey : Sym → Q → Bool) (io : IOContext Io V) (key : Q) (default : D) :
    V ⊕ D :=
  JuliaLean.base.dict.immutableGet eqKey io.dict key default
def get_IO {Q D : Type} (_io : Io) (_key : Q) (default : D) : D := default
def keys_IOContext (io : IOContext Io V) : JuliaLean.base.abstractdict.KeySet Sym (ImmutableDict Sym V) :=
  JuliaLean.base.abstractdict.keysAD io.dict
def keys_IO (_io : Io) : JuliaLean.base.abstractdict.KeySet Sym (ImmutableDict Sym V) :=
  JuliaLean.base.abstractdict.keysAD (JuliaLean.base.dict.immutableEmpty Sym V)

/-- *dispatch*: `get(io, key::Symbol, default)`. -/
def getIO {D : Type} (p : IOPrims m Io V) : JIO Io V → Sym → D → V ⊕ D
  | .context c, key, default => get_IOContext symEq c key default
  | .plain io, key, default => match p.get io key with
    | some v => .inl v
    | none => .inr (get_IO io key default)

/-- *dispatch*: `haskey(io, key::Symbol)`. -/
def haskey : JIO Io V → Sym → Bool
  | .context c, key => haskey_IOContext symEq c key
  | .plain io, key => haskey_IO io key

/-- *dispatch*: `io[key::Symbol]`. -/
def getindex : JIO Io V → Sym → m V
  | .context c, key => getindex_IOContext symEq c key
  | .plain io, key => getindex_IO io key

/-- *dispatch*: `(key => value) in io` for a `Symbol` key. -/
def inIO {W : Type} (egal : W → V → Bool) (key_value : Sym × W) : JIO Io V → m Bool
  | .context c => in_IOContext symEq egal key_value c
  | .plain io => pure (in_IO key_value io)

/-- *dispatch*: `keys(io)`. -/
def keys : JIO Io V → JuliaLean.base.abstractdict.KeySet Sym (ImmutableDict Sym V)
  | .context c => keys_IOContext c
  | .plain io => keys_IO io

/--
Julia source: base/show.jl:322-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, s::Symbol) = (write(io,s); nothing)

```
-/
def print_Symbol (p : IOPrims m Io V) (io : JIO Io V) (s : Sym) : m Unit := do
  write p io (lit s)
  pure ()

/--
Julia source: base/show.jl:324-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    IOContext

`IOContext` provides a mechanism for passing output configuration settings among [`show`](@ref) methods.

In short, it is an immutable dictionary that is a subclass of `IO`. It supports standard
dictionary operations such as [`getindex`](@ref), and can also be used as an I/O stream.
"""
struct IOContext{IO_t <: IO} <: AbstractPipe
    io::IO_t
    dict::ImmutableDict{Symbol, Any}

    function IOContext{IO_t}(io::IO_t, dict::ImmutableDict{Symbol, Any}) where IO_t<:IO
        io isa IOContext && (io = io.io) # implicitly unwrap, since the io.dict field is not useful anymore, and could confuse pipe_reader consumers
        return new(io, dict)
    end
end

```
-/
def IOContext.new (io : JIO Io V) (dict : ImmutableDict Sym V) : IOContext Io V :=
  let io := match io with
    | .context c => c.io
    | .plain io => io
  { io := io, dict := dict }

/--
Julia source: base/show.jl:342-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# (Note that TTY and TTYTerminal io types have an implied :color property.)
ioproperties(io::IO) = get(io, :color, false) ? ImmutableDict{Symbol,Any}(:color, true) : ImmutableDict{Symbol,Any}()
ioproperties(io::IOContext) = io.dict
```
-/
def ioproperties_IO (p : IOPrims m Io V) (a : AnyOps V Ty) (io : Io) : m (ImmutableDict Sym V) := do
  if ← assertBool a (getIO p (.plain io) "color" false) then
    ofDict (JuliaLean.base.dict.immutableSingleton (JuliaLean.base.dict.fieldConv Sym) (boolConv a) "color" true)
  else
    pure (JuliaLean.base.dict.immutableEmpty Sym V)
def ioproperties_IOContext (io : IOContext Io V) : ImmutableDict Sym V := io.dict

/-- *dispatch*: `ioproperties(io)`. -/
def ioproperties (p : IOPrims m Io V) (a : AnyOps V Ty) : JIO Io V → m (ImmutableDict Sym V)
  | .plain io => ioproperties_IO p a io
  | .context c => pure (ioproperties_IOContext c)

/--
Julia source: base/show.jl:345-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# these can probably be deprecated, but there is a use in the ecosystem for them
unwrapcontext(io::IO) = (io,)
unwrapcontext(io::IOContext) = (io.io,)

```
-/
def unwrapcontext_IO (io : JIO Io V) : JIO Io V := io
def unwrapcontext_IOContext (io : IOContext Io V) : JIO Io V := .plain io.io

/--
Julia source: base/show.jl:349-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IOContext(io::IO, dict::ImmutableDict{Symbol, Any})
    return IOContext{typeof(io)}(io, dict)
end

```
-/
def IOContext_IO_dict (io : Io) (dict : ImmutableDict Sym V) : IOContext Io V :=
  IOContext.new (.plain io) dict

/--
Julia source: base/show.jl:353-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IOContext(io::IOContext, dict::ImmutableDict{Symbol, Any})
    return typeof(io)(io.io, dict)
end


```
-/
def IOContext_IOContext_dict (io : IOContext Io V) (dict : ImmutableDict Sym V) : IOContext Io V :=
  IOContext.new (.plain io.io) dict

/-- *dispatch*: `IOContext(io, dict::ImmutableDict{Symbol,Any})`. -/
def mkIOContext : JIO Io V → ImmutableDict Sym V → IOContext Io V
  | .plain io, dict => IOContext_IO_dict io dict
  | .context c, dict => IOContext_IOContext_dict c dict

/--
Julia source: base/show.jl:358-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{IOContext}, io::IOContext) = io
convert(::Type{IOContext}, io::IO) = IOContext(io, ioproperties(io))::IOContext
convert(::Type{IOContext{IO_t}}, io::IOContext{IO_t}) where {IO_t} = io
convert(::Type{IOContext{IO_t}}, io::IO) where {IO_t} = IOContext{IO_t}(io, ioproperties(io))::IOContext{IO_t}

```
-/
def convert_IOContext_IOContext (io : IOContext Io V) : IOContext Io V := io
def convert_IOContext_IO (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V) : m (IOContext Io V) := do
  pure (mkIOContext io (← ioproperties p a io))
/-- `convert(IOContext{IO_t}, io)`: the stream type `IO_t` is the model's `Io`, so an
`IOContext` argument is an `IOContext{IO_t}` and is returned unchanged. -/
def convert_IOContextT_IOContextT (io : IOContext Io V) : IOContext Io V := io
def convert_IOContextT_IO (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V) : m (IOContext Io V) := do
  pure (IOContext.new io (← ioproperties p a io))

/-- *dispatch*: `convert(IOContext, io)`. -/
def convertIOContext (p : IOPrims m Io V) (a : AnyOps V Ty) : JIO Io V → m (IOContext Io V)
  | .context c => pure (convert_IOContext_IOContext c)
  | io => convert_IOContext_IO p a io

/--
Julia source: base/show.jl:363-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IOContext(io::IO) = convert(IOContext, io)
IOContext{IO_t}(io::IO) where {IO_t} = convert(IOContext{IO_t}, io)

```
-/
def IOContext_IO (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V) : m (IOContext Io V) :=
  convertIOContext p a io
def IOContextT_IO (p : IOPrims m Io V) (a : AnyOps V Ty) : JIO Io V → m (IOContext Io V)
  | .context c => pure (convert_IOContextT_IOContextT c)
  | io => convert_IOContextT_IO p a io

/--
Julia source: base/show.jl:366-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IOContext(io::IO, KV::Pair)
    d = ioproperties(io)
    return IOContext(io, ImmutableDict{Symbol,Any}(d, KV[1], KV[2]))
end

```
-/
def IOContext_pair {Q W : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (keyConv : ValueConv Q Sym)
    (valueConv : ValueConv W V) (io : JIO Io V) (KV : Q × W) : m (IOContext Io V) := do
  let d ← ioproperties p a io
  return mkIOContext io (← ofDict (JuliaLean.base.dict.immutablePrepend keyConv valueConv d KV.1 KV.2))

/-- `IOContext(io, :typeinfo => T)`. -/
def withTypeinfo (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V) (T : Ty) : m (JIO Io V) := do
  return .context (← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (typeConv a) io ("typeinfo", T))

/--
Julia source: base/show.jl:371-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    IOContext(io::IO, context::IOContext)

Create an `IOContext` that wraps an alternate `IO` but inherits the properties of `context`.

!!! note
    Unless explicitly set in the wrapped `io` the `displaysize` of `io` will not be inherited.
    This is because by default `displaysize` is not a property of IO objects themselves, but lazily inferred,
    as the size of the terminal window can change during the lifetime of the IO object.
"""
IOContext(io::IO, context::IO) = IOContext(io, ioproperties(context))

```
-/
def IOContext_IO_IO {Parent : Type} (p : IOPrims m Parent V) (a : AnyOps V Ty)
    (io : JIO Io V) (context : JIO Parent V) : m (IOContext Io V) := do
  return mkIOContext io (← ioproperties p a context)

/--
Julia source: base/show.jl:383-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    IOContext(io::IO, KV::Pair...)

Create an `IOContext` that wraps a given stream, adding the specified `key=>value` pairs to
the properties of that stream (note that `io` can itself be an `IOContext`).

 - use `(key => value) in io` to see if this particular combination is in the properties set
 - use `get(io, key, default)` to retrieve the most recent value for a particular key

The following properties are in common use:

 - `:compact`: Boolean specifying that values should be printed more compactly, e.g.
   that numbers should be printed with fewer digits. This is set when printing array
   elements. `:compact` output should not contain line breaks.
 - `:limit`: Boolean specifying that containers should be truncated, e.g. showing `…` in
   place of most elements.
 - `:displaysize`: A `Tuple{Int,Int}` giving the size in rows and columns to use for text
   output. This can be used to override the display size for called functions, but to
   get the size of the screen use the `displaysize` function.
 - `:typeinfo`: a `Type` characterizing the information already printed
   concerning the type of the object about to be displayed. This is mainly useful when
   displaying a collection of objects of the same type, so that redundant type information
   can be avoided (e.g. `[Float16(0)]` can be shown as "Float16[0.0]" instead
   of "Float16[Float16(0.0)]" : while displaying the elements of the array, the `:typeinfo`
   property will be set to `Float16`).
 - `:color`: Boolean specifying whether ANSI color/escape codes are supported/expected.
   By default, this is determined by whether `io` is a compatible terminal and by any
   `--color` command-line flag when `julia` was launched.
 - `:hexunsigned`: Boolean specifying whether to print unsigned integers in
   hexadecimal. Defaults to `true`, otherwise they will be printed in decimal.

!!! compat "Julia 1.14"
    The `:hexunsigned` option requires Julia 1.14 or later.

# Examples

```jldoctest
julia> io = IOBuffer();

julia> printstyled(IOContext(io, :color => true), "string", color=:red)

julia> takestring!(io)
"\\e[31mstring\\e[39m"

julia> printstyled(io, "string", color=:red)

julia> takestring!(io)
"string"
```

```jldoctest
julia> print(IOContext(stdout, :compact => false), 1.12341234)
1.12341234
julia> print(IOContext(stdout, :compact => true), 1.12341234)
1.12341
```

```jldoctest
julia> function f(io::IO)
           if get(io, :short, false)
               print(io, "short")
           else
               print(io, "loooooong")
           end
       end
f (generic function with 1 method)

julia> f(stdout)
loooooong
julia> f(IOContext(stdout, :short => true))
short
```
"""
IOContext(io::IO, KV::Pair, KVs::Pair...) = IOContext(IOContext(io, KV), KVs...)

````
-/
def IOContext_pairs {Q W : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (keyConv : ValueConv Q Sym)
    (valueConv : ValueConv W V) (io : JIO Io V) (KV : Q × W) (KVs : List (Q × W)) : m (IOContext Io V) :=
  match KVs with
  -- Julia selects `IOContext(io::IO, KV::Pair)` when `KVs` is empty.
  | [] => IOContext_pair p a keyConv valueConv io KV
  | KV₂ :: rest => do
    IOContext_pairs p a keyConv valueConv (.context (← IOContext_pair p a keyConv valueConv io KV)) KV₂ rest

/--
Julia source: base/show.jl:458-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ctx::IOContext) = (print(io, "IOContext("); show(io, ctx.io); print(io, ")"))

```
-/
def show_IOContext (p : IOPrims m Io V) (showX : JIO Io V → Io → m Unit) (io : JIO Io V)
    (ctx : IOContext Io V) : m Unit := do
  printStr p io "IOContext("
  showX io ctx.io
  printStr p io ")"

/--
Julia source: base/show.jl:476-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
displaysize(io::IOContext) = haskey(io, :displaysize) ? io[:displaysize]::Tuple{Int,Int} : displaysize(io.io)::Tuple{Int,Int}

```
-/
def displaysize_IOContext (p : IOPrims m Io V) (a : AnyOps V Ty) (io : IOContext Io V) :
    m (JInt64 × JInt64) := do
  if haskey (.context io) "displaysize" then
    match a.asDims (← getindex (.context io) "displaysize") with
    | some d => pure d
    | none => throwShow .typeError
  else
    p.displaysize io.io

/--
Julia source: base/show.jl:478-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_circular(io::IO, @nospecialize(x)) = false
function show_circular(io::IOContext, @nospecialize(x))
    d = 1
    for (k, v) in io.dict
        if k === :SHOWN_SET
            if v === x
                printstyled(io, "#= circular reference @-$d =#"; color = :yellow)
                return true
            end
            d += 1
        end
    end
    return false
end

```
-/
def show_circular_IO {X : Type} (_io : Io) (_x : X) : Bool := false
def show_circular_IOContext {X : Type} (p : IOPrims m Io V) (printstyled : PrintStyled m Io V)
    (stringInt : JInt64 → m Bytes) (egal : V → X → Bool) (io : IOContext Io V) (x : X) : m Bool := do
  let mut d := i64 1
  for (k, v) in io.dict do
    if k == "SHOWN_SET" then
      if egal v x then
        -- `"#= circular reference @-$d =#"` is `string("#= circular reference @-", d, " =#")`.
        let msg := lit "#= circular reference @-" ++ (← stringInt d) ++ lit " =#"
        printstyled (.context io) [fun io => printBytes p io msg] "yellow" false
        return true
      d := i64 (d.val + 1)
  return false

/-- *dispatch*: `show_circular(io, x)`. -/
def show_circular {X : Type} (p : IOPrims m Io V) (printstyled : PrintStyled m Io V)
    (stringInt : JInt64 → m Bytes) (egal : V → X → Bool) : JIO Io V → X → m Bool
  | .plain io, x => pure (show_circular_IO io x)
  | .context c, x => show_circular_IOContext p printstyled stringInt egal c x

/--
Julia source: base/show.jl:493-521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    show([io::IO = stdout], x)

Write a text representation of a value `x` to the output stream `io`. New types `T`
should overload `show(io::IO, x::T)`. The representation used by `show` generally
includes Julia-specific formatting and type information, and should be parseable
Julia code when possible.

[`repr`](@ref) returns the output of `show` as a string.

For a more verbose human-readable text output for objects of type `T`, define
`show(io::IO, ::MIME"text/plain", ::T)` in addition. Checking the `:compact`
[`IOContext`](@ref) key (often checked as `get(io, :compact, false)::Bool`)
of `io` in such methods is recommended,
since some containers show their elements by calling this method with
`:compact => true`.

See also [`print`](@ref), which writes un-decorated representations.

# Examples
```jldoctest
julia> show("Hello World!")
"Hello World!"
julia> print("Hello World!")
Hello World!
```
"""
show(io::IO, @nospecialize(x)) = show_default(io, x)

````
-/
def show_Any {X : Type} (show_default : JIO Io V → X → m Unit) (io : JIO Io V) (x : X) : m Unit :=
  show_default io x

/--
Julia source: base/show.jl:522-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(x) = show(stdout, x)

```
-/
def show_stdout {X : Type} (showX : JIO Io V → X → m Unit) (stdout : JIO Io V) (x : X) : m Unit :=
  showX stdout x

/--
Julia source: base/show.jl:524-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# avoid inferring show_default on the type of `x`
show_default(io::IO, @nospecialize(x)) = _show_default(io, inferencebarrier(x))

```
-/
def show_default {X : Type} (_show_default : JIO Io V → X → m Unit) (io : JIO Io V) (x : X) : m Unit :=
  _show_default io x


/--
Julia source: base/show.jl:1422-1422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nonnothing_nonmissing_typeinfo(io::IO) = nonmissingtype(nonnothingtype(get(io, :typeinfo, Any)))
```
-/
def nonnothing_nonmissing_typeinfo (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty)
    (io : JIO Io V) : m Ty := do
  -- `nonnothingtype(T::Type)` has no method for a non-type argument.
  let T ← match getIO p io "typeinfo" t.any with
    | .inl v => match a.asType v with
      | some T => pure T
      | none => throwShow (.jl (.methodError "nonnothingtype"))
    | .inr T => pure T
  t.nonmissingtype (← t.nonnothingtype T)

/--
Julia source: base/show.jl:1423-1423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, b::Bool) = print(io, nonnothing_nonmissing_typeinfo(io) === Bool ? (b ? "1" : "0") : (b ? "true" : "false"))
```
-/
def show_Bool (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty) (io : JIO Io V) (b : Bool) :
    m Unit := do
  printStr p io (if t.egal (← nonnothing_nonmissing_typeinfo p a t io) t.bool then
    (if b then "1" else "0") else (if b then "true" else "false"))

/--
Julia source: base/show.jl:1424-1424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::Nothing) = print(io, "nothing")
```
-/
def show_Nothing (p : IOPrims m Io V) (io : JIO Io V) : m Unit := printStr p io "nothing"

/--
Julia source: base/show.jl:1425-1425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, n::Signed) = (write(io, string(n)); nothing)
```
-/
def show_Signed {N : Type} (p : IOPrims m Io V) (string : N → m Bytes) (io : JIO Io V) (n : N) :
    m Unit := do
  write p io (← string n)
  pure ()

/--
Julia source: base/show.jl:1437-1438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, n::Unsigned) = print(io, string(n))

```
-/
def print_Unsigned {N : Type} (p : IOPrims m Io V) (string : N → m Bytes) (io : JIO Io V) (n : N) :
    m Unit := do
  printBytes p io (← string n)

/--
Julia source: base/show.jl:1426-1436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, n::Unsigned)
    if get(io, :hexunsigned, true)::Bool
        print(io, "0x", string(n, pad = cld(Core.bitsizeof(n), 4), base = 16))
    else
        if get(io, :typeinfo, Nothing)::Type == typeof(n)
            print(io, n)
        else
            print(io, typeof(n), "($(n))")
        end
    end
end
```
-/
def show_Unsigned {N : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty)
    (string : N → m Bytes) (stringBasePad : N → JInt64 → JInt64 → m Bytes) (bitsizeof : N → JInt64)
    (typeOf : N → Ty) (printType : JIO Io V → Ty → m Unit) (io : JIO Io V) (n : N) : m Unit := do
  if ← assertBool a (getIO p io "hexunsigned" true) then
    let pad ← ofJl (JuliaLean.base.div.cldBitInteger (bitsizeof n) (i64 4))
    let s ← stringBasePad n (i64 16) pad
    printAll p io [printStr p io "0x", printBytes p io s]
  else
    if ← t.eq (← assertType a (getIO p io "typeinfo" t.nothing)) (typeOf n) then
      print_Unsigned p string io n
    else
      -- `"($(n))"` is `string("(", n, ")")`, which prints `n` with `print(io, n::Unsigned)`.
      let s := lit "(" ++ (← string n) ++ lit ")"
      printAll p io [printType io (typeOf n), printBytes p io s]

/-- `string(n; base, pad)` of a BitInteger (`base/intfuncs.jl`). -/
def stringBits (c : JuliaLean.base.intfuncs.DigitCallees) {u : IntTy} (n : JInt u) (base pad : JInt64) :
    m Bytes := do
  let b ← ofJl (JuliaLean.base.intfuncs.stringBits c n base pad)
  pure (b.bytes.map UInt8.ofNat)

/-- *dispatch*: `show(io, n)` of a BitInteger: `show(io, n::Signed)` or `show(io, n::Unsigned)`.
`string(n)` is `string(n; base = 10, pad = 1)`. -/
def show_BitInteger (c : JuliaLean.base.intfuncs.DigitCallees) (p : IOPrims m Io V) (a : AnyOps V Ty)
    (t : TypeOps m Ty) (printType : JIO Io V → Ty → m Unit) (io : JIO Io V) {u : IntTy} (n : JInt u) :
    m Unit :=
  if u.signed then
    show_Signed p (fun n => stringBits c n (i64 10) (i64 1)) io n
  else
    show_Unsigned p a t (fun n => stringBits c n (i64 10) (i64 1)) (stringBits c)
      (fun _ => i64 u.bits) (fun _ => t.bitInteger u) printType io n

/-- *dispatch*: `print(io, n)` of a BitInteger. Signed integers have no `print` method of their
own: `print(io, x) = show(io, x)` (`base/strings/io.jl`) under `lock(io)`. -/
def print_BitInteger (c : JuliaLean.base.intfuncs.DigitCallees) (p : IOPrims m Io V) (a : AnyOps V Ty)
    (t : TypeOps m Ty) (printType : JIO Io V → Ty → m Unit) (io : JIO Io V) {u : IntTy} (n : JInt u) :
    m Unit :=
  if u.signed then
    printAll p io [show_BitInteger c p a t printType io n]
  else
    print_Unsigned p (fun n => stringBits c n (i64 10) (i64 1)) io n

/--
Julia source: base/show.jl:1439-1442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_tight_type(p::Pair) =
    typeof(p.first)  == typeof(p).parameters[1] &&
    typeof(p.second) == typeof(p).parameters[2]

```
-/
def has_tight_type {A B : Type} (t : TypeOps m Ty) (typeOfA : A → Ty) (typeOfB : B → Ty)
    (typeOfP : Pair A B → Ty) (p : Pair A B) : m Bool := do
  if ← t.eq (typeOfA p.first) (t.parameter (typeOfP p) 1) then
    t.eq (typeOfB p.second) (t.parameter (typeOfP p) 2)
  else pure false

/--
Julia source: base/show.jl:1443-1443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdelimited(io::IO, x) = true
```
-/
def isdelimited_Any {X : Type} (_io : JIO Io V) (_x : X) : Bool := true

/--
Julia source: base/show.jl:1444-1445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdelimited(io::IO, x::Function) = !isoperator(Symbol(x))

```
-/
def isdelimited_Function {F : Type} (isoperator : Sym → Bool) (symbol : F → Sym) (_io : JIO Io V)
    (x : F) : Bool :=
  !isoperator (symbol x)

/-- `==(x, T)` of an `IOContext` value and a type: a non-type value is never `==` to a type. -/
def eqType (a : AnyOps V Ty) (t : TypeOps m Ty) : V ⊕ Ty → Ty → m Bool
  | .inl v, T => match a.asType v with
    | some S => t.eq S T
    | none => pure false
  | .inr S, T => t.eq S T

/--
Julia source: base/show.jl:1446-1449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# !isdelimited means that the Pair is printed with "=>" (like in "1 => 2"),
# without its explicit type (like in "Pair{Integer,Integer}(1, 2)")
isdelimited(io::IO, p::Pair) = !(has_tight_type(p) || get(io, :typeinfo, Any) == typeof(p))

```
-/
def isdelimited_Pair {A B : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty)
    (typeOfA : A → Ty) (typeOfB : B → Ty) (typeOfP : Pair A B → Ty) (io : JIO Io V) (x : Pair A B) :
    m Bool := do
  if ← has_tight_type t typeOfA typeOfB typeOfP x then return false
  return !(← eqType a t (getIO p io "typeinfo" t.any) (typeOfP x))

/-- `fieldtype(T, i)`. -/
def fieldtype (t : TypeOps m Ty) (T : Ty) (i : JInt64) : m Ty :=
  match t.fieldtype T i with
  | some F => pure F
  | none => throwShow (.jl .boundsError)

/--
Julia source: base/show.jl:1450-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gettypeinfos(io::IO, p::Pair)
    typeinfo = get(io, :typeinfo, Any)
    p isa typeinfo <: Pair ?
        fieldtype(typeinfo, 1) => fieldtype(typeinfo, 2) :
        Any => Any
end

```
-/
def gettypeinfos {A B : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty)
    (typeOfP : Pair A B → Ty) (io : JIO Io V) (x : Pair A B) : m (Ty × Ty) := do
  let typeinfo := getIO p io "typeinfo" t.any
  -- `p isa typeinfo <: Pair` is `(p isa typeinfo) && (typeinfo <: Pair)`; `isa` throws a
  -- `TypeError` when `typeinfo` is not a type.
  let T ← assertType a typeinfo
  if ← (do if ← t.subtype (typeOfP x) T then t.subtype T t.pair else pure false) then
    return (← fieldtype t T (i64 1), ← fieldtype t T (i64 2))
  else
    return (t.any, t.any)

/--
Julia source: base/show.jl:1469-1473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_pairtyped(io::IO, p::Pair{K,V}) where {K,V}
    show(io, typeof(p))
    show(io, (p.first, p.second))
end

```
-/
def show_pairtyped {A B : Type} (showType : JIO Io V → Ty → m Unit)
    (showTuple : JIO Io V → A → B → m Unit) (typeOfP : Pair A B → Ty) (io : JIO Io V) (p : Pair A B) :
    m Unit := do
  showType io (typeOfP p)
  showTuple io p.first p.second

/--
Julia source: base/show.jl:1457-1468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, p::Pair)
    isdelimited(io, p) && return show_pairtyped(io, p)
    typeinfos = gettypeinfos(io, p)
    for i = (1, 2)
        io_i = IOContext(io, :typeinfo => typeinfos[i])
        isdelimited(io_i, p[i]) || print(io, "(")
        show(io_i, p[i])
        isdelimited(io_i, p[i]) || print(io, ")")
        i == 1 && print(io, get(io, :compact, false)::Bool ? "=>" : " => ")
    end
end

```
-/
def show_Pair {A B : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty)
    (typeOfA : A → Ty) (typeOfB : B → Ty) (typeOfP : Pair A B → Ty)
    (isdelimitedA : JIO Io V → A → Bool) (isdelimitedB : JIO Io V → B → Bool)
    (showA : JIO Io V → A → m Unit) (showB : JIO Io V → B → m Unit)
    (showType : JIO Io V → Ty → m Unit) (showTuple : JIO Io V → A → B → m Unit)
    (io : JIO Io V) (x : Pair A B) : m Unit := do
  if ← isdelimited_Pair p a t typeOfA typeOfB typeOfP io x then
    return ← show_pairtyped showType showTuple typeOfP io x
  let typeinfos ← gettypeinfos p a t typeOfP io x
  -- `for i = (1, 2)`, unrolled: `p[1]` and `p[2]` have different types.
  let io_1 ← withTypeinfo p a io typeinfos.1
  if !isdelimitedA io_1 x.first then printStr p io "("
  showA io_1 x.first
  if !isdelimitedA io_1 x.first then printStr p io ")"
  printStr p io (if ← assertBool a (getIO p io "compact" false) then "=>" else " => ")
  let io_2 ← withTypeinfo p a io typeinfos.2
  if !isdelimitedB io_2 x.second then printStr p io "("
  showB io_2 x.second
  if !isdelimitedB io_2 x.second then printStr p io ")"

/-- `IOContext(io, :SHOWN_SET => itr)`. -/
def withShownSet {I : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (ofAny : I → V) (io : JIO Io V)
    (itr : I) : m (JIO Io V) := do
  return .context (← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym)
    ⟨fun x => some (ofAny x), fun x => .ok (ofAny x)⟩ io ("SHOWN_SET", itr))

/-- Linear indexing of an `AbstractArray` or `SimpleVector`. -/
structure IndexOps (I X : Type) where
  isassigned : I → JInt64 → Bool
  getindex : I → JInt64 → Option X

/-- The `while true` loop of `show_delim_array` over an array, from index `i` to `l` (`i ≤ l`). -/
def show_delim_array_loop {I X : Type} (p : IOPrims m Io V) (ix : IndexOps I X)
    (showX : JIO Io V → X → m Unit) (io recur_io : JIO Io V) (itr : I) (delim : String) (delim_one : Bool)
    (l : JInt64) (first : Bool) (i : JInt64) (h : i.val ≤ l.val) : m Unit := do
  if !ix.isassigned itr i then
    printStr p io undef_ref_str
  else
    let x ← match ix.getindex itr i with
      | some x => pure x
      | none => throwShow (.jl .boundsError)
    showX recur_io x
  if hi : i.val = l.val then
    if delim_one && first then printStr p io delim
  else
    -- `i += 1` does not wrap: `i < l`.
    let i' : JInt64 := ⟨i.val + 1, by have := i.2.1; have := l.2.2; constructor <;> omega⟩
    printStr p io delim
    printStr p io " "
    show_delim_array_loop p ix showX io recur_io itr delim delim_one l false i' (by show i.val + 1 ≤ l.val; omega)
termination_by (l.val - i.val).toNat
decreasing_by omega

/--
Julia source: base/show.jl:1562-1590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_delim_array(io::IO, itr::Union{AbstractArray,SimpleVector}, op, delim, cl,
                          delim_one, i1=first(LinearIndices(itr)), l=last(LinearIndices(itr)))
    print(io, op)
    if !show_circular(io, itr)
        recur_io = IOContext(io, :SHOWN_SET => itr)
        first = true
        i = i1
        if l >= i1
            while true
                if !isassigned(itr, i)
                    print(io, undef_ref_str)
                else
                    x = itr[i]
                    show(recur_io, x)
                end
                if i == l
                    delim_one && first && print(io, delim)
                    break
                end
                i += 1
                first = false
                print(io, delim)
                print(io, ' ')
            end
        end
    end
    print(io, cl)
end

```
-/
def show_delim_array_Array {I X : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (ix : IndexOps I X)
    (printstyled : PrintStyled m Io V) (stringInt : JInt64 → m Bytes) (egal : V → I → Bool) (ofAny : I → V)
    (showX : JIO Io V → X → m Unit) (io : JIO Io V) (itr : I) (op delim cl : String) (delim_one : Bool)
    (i1 l : JInt64) : m Unit := do
  printStr p io op
  if !(← show_circular p printstyled stringInt egal io itr) then
    let recur_io ← withShownSet p a ofAny io itr
    let first := true
    let i := i1
    if h : l.val ≥ i1.val then
      show_delim_array_loop p ix showX io recur_io itr delim delim_one l first i h
  printStr p io cl

/-- The iteration protocol of an iterable `itr`. -/
structure IterOps (I X S : Type) where
  iterate : I → Option (X × S)
  iterateFrom : I → S → Option (X × S)

/-- The first `while` loop of the iterable `show_delim_array`: skip to element `i1`. -/
def show_delim_array_skip {I X S : Type} (it : IterOps I X S) (itr : I) (y : Option (X × S))
    (i1 : JInt64) : Option (X × S) × JInt64 :=
  match y with
  | some (_, st) =>
    if h : i1.val > 1 then
      -- `i1 -= 1` does not wrap: `i1 > 1`.
      show_delim_array_skip it itr (it.iterateFrom itr st)
        ⟨i1.val - 1, by have := i1.2.2; have : IntTy.min .i64 ≤ 0 := (by decide); constructor <;> omega⟩
    else (y, i1)
  | none => (y, i1)
termination_by i1.val.toNat
decreasing_by simp_wf; omega

/-- The `while true` loop of the iterable `show_delim_array`. Its termination depends on the
iterator, so it is a `partial_fixpoint`. -/
def show_delim_array_iter_loop {I X S : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty) (it : IterOps I X S) (typeOfI : I → Ty)
    (showX : JIO Io V → X → m Unit) (io recur_io : JIO Io V) (itr : I) (delim : String)
    (delim_one : Bool) (n i0 : JInt64) (typeinfo : V ⊕ Ty) (first : Bool) (x : X) (y : Option (X × S))
    (i1 : JInt64) : m Unit := do
  -- `itr isa typeinfo <: Tuple` is `(itr isa typeinfo) && (typeinfo <: Tuple)`.
  let T ← assertType a typeinfo
  let tight ← do if ← t.subtype (typeOfI itr) T then t.subtype T t.tuple else pure false
  let ti ← if tight then
      fieldtype t T (i64 (i1.val + i0.val))
    else pure T
  showX (← withTypeinfo p a recur_io ti) x
  let i1 := i64 (i1.val + 1)
  match y with
  | none =>
    if delim_one && first then printStr p io delim
  | some (x, st) =>
    if i1.val > n.val then
      if delim_one && first then printStr p io delim
    else
      printStr p io delim
      printStr p io " "
      show_delim_array_iter_loop p a t it typeOfI showX io recur_io itr delim delim_one n i0 typeinfo
        false x (it.iterateFrom itr st) i1
partial_fixpoint

/--
Julia source: base/show.jl:1591-1624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_delim_array(io::IO, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int))
    print(io, op)
    if !show_circular(io, itr)
        recur_io = IOContext(io, :SHOWN_SET => itr)
        y = iterate(itr)
        first = true
        i0 = i1-1
        while i1 > 1 && y !== nothing
            y = iterate(itr, y[2])
            i1 -= 1
        end
        if y !== nothing
            typeinfo = get(io, :typeinfo, Any)
            while true
                x = y[1]
                y = iterate(itr, y[2])
                show(IOContext(recur_io, :typeinfo => itr isa typeinfo <: Tuple ?
                                             fieldtype(typeinfo, i1+i0) :
                                             typeinfo),
                     x)
                i1 += 1
                if y === nothing || i1 > n
                    delim_one && first && print(io, delim)
                    break
                end
                first = false
                print(io, delim)
                print(io, ' ')
            end
        end
    end
    print(io, cl)
end

```
-/
def show_delim_array_iter {I X S : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty) (it : IterOps I X S) (typeOfI : I → Ty)
    (printstyled : PrintStyled m Io V) (stringInt : JInt64 → m Bytes) (egal : V → I → Bool) (ofAny : I → V)
    (showX : JIO Io V → X → m Unit) (io : JIO Io V) (itr : I) (op delim cl : String) (delim_one : Bool)
    (i1 : JInt64 := i64 1) (n : JInt64 := i64 (IntTy.max .i64)) : m Unit := do
  printStr p io op
  if !(← show_circular p printstyled stringInt egal io itr) then
    let recur_io ← withShownSet p a ofAny io itr
    let y := it.iterate itr
    let first := true
    let i0 := i64 (i1.val - 1)
    let (y, i1) := show_delim_array_skip it itr y i1
    match y with
    | some (x, st) =>
      let typeinfo := getIO p io "typeinfo" t.any
      show_delim_array_iter_loop p a t it typeOfI showX io recur_io itr delim delim_one n i0 typeinfo
        first x (it.iterateFrom itr st) i1
    | none => pure ()
  printStr p io cl

/--
Julia source: base/show.jl:1625-1627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, t::Tuple) = show_delim_array(io, t, '(', ',', ')', true)
show(io::IO, v::SimpleVector) = show_delim_array(io, v, "svec(", ',', ')', false)

```
-/
def show_Tuple {I X S : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty) (it : IterOps I X S) (typeOfI : I → Ty)
    (printstyled : PrintStyled m Io V) (stringInt : JInt64 → m Bytes) (egal : V → I → Bool) (ofAny : I → V)
    (showX : JIO Io V → X → m Unit) (io : JIO Io V) (tup : I) : m Unit :=
  show_delim_array_iter p a t it typeOfI printstyled stringInt egal ofAny showX io tup "(" "," ")" true
/-- `show(io::IO, v::SimpleVector)`; Julia selects the `AbstractArray`/`SimpleVector` method of
`show_delim_array`, whose default index range is `1:length(v)`. -/
def show_SimpleVector {I X : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (ix : IndexOps I X)
    (length : I → JInt64) (printstyled : PrintStyled m Io V) (stringInt : JInt64 → m Bytes) (egal : V → I → Bool)
    (ofAny : I → V) (showX : JIO Io V → X → m Unit) (io : JIO Io V) (v : I) : m Unit :=
  show_delim_array_Array p a ix printstyled stringInt egal ofAny showX io v "svec(" "," ")" false (i64 1) (length v)

/--
Julia source: base/show.jl:3228-3229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::UndefInitializer) = print(io, "UndefInitializer()")

```
-/
def show_UndefInitializer (p : IOPrims m Io V) (io : JIO Io V) : m Unit :=
  printStr p io "UndefInitializer()"

-- UNTRANSLATED
-- `using .Meta: …` import statement; no method
-- Source: base/show.jl:1-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- using .Meta: _isoperator, is_id_start_char, is_unary_and_binary_operator,
--     is_valid_identifier
-- 
-- /Source

/--
Julia source: base/show.jl:6-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", u::UndefInitializer)
    show(io, u)
    get(io, :compact, false)::Bool && return
    print(io, ": array initializer with undefined values")
end

```
-/
def show_textplain_UndefInitializer (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V) : m Unit := do
  show_UndefInitializer p io
  if ← assertBool a (getIO p io "compact" false) then return
  printStr p io ": array initializer with undefined values"

/--
Julia source: base/show.jl:12-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# first a few multiline show functions for types defined before the MIME type:

show(io::IO, ::MIME"text/plain", r::AbstractRange) = show(io, r) # always use the compact form for printing ranges

```
-/
def show_textplain_AbstractRange {R : Type} (showR : JIO Io V → R → m Unit) (io : JIO Io V) (r : R) :
    m Unit :=
  showR io r

/--
Julia source: base/show.jl:16-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", r::UnitRange)
    show(io, r)
    if !(get(io, :compact, false)::Bool) && isempty(r)
        print(io, " (empty range)")
    end
end

```
-/
def show_textplain_UnitRange {R : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (isempty : R → Bool)
    (showR : JIO Io V → R → m Unit) (io : JIO Io V) (r : R) : m Unit := do
  showR io r
  if !(← assertBool a (getIO p io "compact" false)) && isempty r then
    printStr p io " (empty range)"

/-- `println(io, xs...) = print(io, xs..., '\n')` (`base/strings/io.jl`). -/
def println (p : IOPrims m Io V) (io : JIO Io V) (xs : List (m Unit)) : m Unit :=
  printAll p io (xs ++ [printStr p io "\n"])

/--
Julia source: base/show.jl:23-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", r::LinRange)
    isempty(r) && return show(io, r)
    # show for LinRange, e.g.
    # range(1, stop=3, length=7)
    # 7-element LinRange{Float64}:
    #   1.0,1.33333,1.66667,2.0,2.33333,2.66667,3.0
    summary(io, r)
    println(io, ":")
    print_range(io, r)
end

```
-/
def show_textplain_LinRange {R : Type} (p : IOPrims m Io V) (isempty : R → Bool)
    (showR : JIO Io V → R → m Unit) (summary : JIO Io V → R → m Unit)
    (print_range : JIO Io V → R → m Unit) (io : JIO Io V) (r : R) : m Unit := do
  if isempty r then return ← showR io r
  summary io r
  println p io [printStr p io ":"]
  print_range io r

/--
Julia source: base/show.jl:34-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", r::LogRange)  # display LogRange like LinRange
    isempty(r) && return show(io, r)
    summary(io, r)
    println(io, ":")
    print_range(io, r, " ", ", ", "", " \u2026 ")
end

```
-/
def show_textplain_LogRange {R : Type} (p : IOPrims m Io V) (isempty : R → Bool)
    (showR : JIO Io V → R → m Unit) (summary : JIO Io V → R → m Unit)
    (print_range : JIO Io V → R → String → String → String → String → m Unit) (io : JIO Io V) (r : R) :
    m Unit := do
  if isempty r then return ← showR io r
  summary io r
  println p io [printStr p io ":"]
  print_range io r " " ", " "" " \u2026 "



/--
Julia source: base/show.jl:75-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::MIME"text/plain", c::ComposedFunction) = show(io, c)
show(io::IO, ::MIME"text/plain", c::Returns) = show(io, c)
show(io::IO, ::MIME"text/plain", s::Splat) = show(io, s)

```
-/
def show_textplain_ComposedFunction {F : Type} (showF : JIO Io V → F → m Unit) (io : JIO Io V) (c : F) :
    m Unit :=
  showF io c
def show_textplain_Returns {F : Type} (showF : JIO Io V → F → m Unit) (io : JIO Io V) (c : F) : m Unit :=
  showF io c
def show_textplain_Splat {F : Type} (showF : JIO Io V → F → m Unit) (io : JIO Io V) (s : F) : m Unit :=
  showF io s


/--
Julia source: base/show.jl:81-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Pseudo-character representing an ANSI delimiter
struct ANSIDelimiter
    del::SubString{String}
end
```
-/
structure ANSIDelimiter where
  /-- The bytes of the `SubString{String}`. -/
  del : Bytes

/-- An element of an `ANSIIterator`: a `Char` or an `ANSIDelimiter`. -/
inductive ANSIChar (C : Type) where
  | char (c : C)
  | delim (d : ANSIDelimiter)

/--
Julia source: base/show.jl:85-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ncodeunits(c::ANSIDelimiter) = ncodeunits(c.del)
textwidth(::ANSIDelimiter) = 0

```
-/
def ncodeunits_ANSIDelimiter (c : ANSIDelimiter) : JInt64 := i64 c.del.length
def textwidth_ANSIDelimiter (_c : ANSIDelimiter) : JInt64 := i64 0


/--
Julia source: base/show.jl:79-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const ansi_regex = r"(?s)(?:\x1B(?:[@-Z\\-_]|\[[0-?]*[ -\/]*[@-~]))|."
```
-/
def ansi_regex {Regex : Type} (compile : Bytes → m Regex) : m Regex :=
  compile (lit "(?s)(?:\\x1B(?:[@-Z\\\\-_]|\\[[0-?]*[ -/]*[@-~]))|.")

/--
Julia source: base/show.jl:88-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# An iterator similar to `pairs(::String)` but whose values are Char or ANSIDelimiter
struct ANSIIterator{S}
    captures::RegexMatchIterator{S}
end
```
-/
structure ANSIIterator (Captures : Type) where
  captures : Captures

/--
Julia source: base/show.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ANSIIterator(s::AbstractString) = ANSIIterator(eachmatch(ansi_regex, s))
```
-/
def ANSIIterator_new {S Regex Captures : Type} (regex : Regex) (eachmatch : Regex → S → m Captures)
    (s : S) : m (ANSIIterator Captures) := do return ⟨← eachmatch regex s⟩

/--
Julia source: base/show.jl:94-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:ANSIIterator}) = SizeUnknown()
```
-/
def IteratorSize_ANSIIterator : JuliaLean.base.iterators.IteratorSizeTag := .sizeUnknown

/--
Julia source: base/show.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:ANSIIterator}) = Pair{Int, Union{Char,ANSIDelimiter}}
```
-/
def eltype_ANSIIterator (C : Type) : Type := JInt64 × ANSIChar C

/--
Julia source: base/show.jl:96-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(I::ANSIIterator, (i, m_st)=(1, iterate(I.captures)))
    m_st === nothing && return nothing
    m, (j, new_m_st) = m_st
    c = lastindex(m.match) == 1 ? only(m.match) : ANSIDelimiter(m.match)
    return (i => c, (j, iterate(I.captures, (j, new_m_st))))
end
```
-/
def iterate_ANSIIterator {R Mt Q C : Type} (iterateCaptures : R → JInt64 × Q → Option (Mt × (JInt64 × Q)))
    (lastindex : Mt → JInt64) (only : Mt → m C) (matchBytes : Mt → Bytes) (I : R)
    (state : JInt64 × Option (Mt × (JInt64 × Q))) :
    m (Option ((JInt64 × ANSIChar C) × (JInt64 × Option (Mt × (JInt64 × Q))))) := do
  let (i, m_st) := state
  match m_st with
  | none => return none
  | some (mt, (j, new_m_st)) =>
    let c ← if (lastindex mt).val == 1 then ANSIChar.char <$> only mt
      else pure (ANSIChar.delim ⟨matchBytes mt⟩)
    return some ((i, c), (j, iterateCaptures I (j, new_m_st)))

/-- `iterate(I::ANSIIterator)`: the default state `(1, iterate(I.captures))`. -/
def iterate_ANSIIterator_start {R Mt Q C : Type} (iterateCaptures : R → JInt64 × Q → Option (Mt × (JInt64 × Q)))
    (iterateCaptures₀ : R → Option (Mt × (JInt64 × Q))) (lastindex : Mt → JInt64) (only : Mt → m C)
    (matchBytes : Mt → Bytes) (I : R) :
    m (Option ((JInt64 × ANSIChar C) × (JInt64 × Option (Mt × (JInt64 × Q))))) :=
  iterate_ANSIIterator iterateCaptures lastindex only matchBytes I (i64 1, iterateCaptures₀ I)

/--
Julia source: base/show.jl:102-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
textwidth(I::ANSIIterator) = mapreduce(textwidth∘last, +, I; init=0)

```
-/
def textwidth_ANSIIterator {C : Type} (textwidthChar : C → JInt64) (I : List (JInt64 × ANSIChar C)) :
    JInt64 :=
  -- `mapreduce` with `init` over an iterator of unknown size is `mapfoldl`.
  I.foldl (fun acc (_, c) => i64 (acc.val + (match c with
    | .char c => textwidthChar c
    | .delim d => textwidth_ANSIDelimiter d).val)) (i64 0)

/-- `AbstractString` operations of `base/strings` used on a string `S` with characters `C`. -/
structure StrOps (S C : Type) where
  textwidthChar : C → JInt64
  /-- `pairs(str)`: index–character pairs. -/
  pairs : S → List (JInt64 × C)
  /-- The elements of `ANSIIterator(str)` (regex matching, untranslated). -/
  ansiPairs : S → List (JInt64 × ANSIChar C)
  /-- `str[i]`; `none` when it throws `StringIndexError`/`BoundsError`. -/
  getindex : S → JInt64 → Option C
  prevind : S → JInt64 → JInt64
  lastindex : S → JInt64
  /-- `SubString(str, 1, i)` as bytes; `none` when it throws. -/
  prefixBytes : S → JInt64 → Option Bytes
  /-- The bytes `print` writes for `str`. -/
  bytes : S → Bytes
  charBytes : C → Bytes
  charEq : C → C → Bool
  ofChar : Char → C

/-- `textwidth(s::AbstractString) = mapreduce(textwidth, +, s; init=0)` of a string given by its
characters. -/
def textwidthChars {S C : Type} (s : StrOps S C) (cs : List C) : JInt64 :=
  cs.foldl (fun acc c => i64 (acc.val + (s.textwidthChar c).val)) (i64 0)

/-- `textwidth(str)`. -/
def textwidthStr {S C : Type} (s : StrOps S C) (str : S) : JInt64 :=
  textwidthChars s ((s.pairs str).map Prod.snd)

/-- `repeat(' ', n)` for `n ≥ 0`. -/
def spaces (n : JInt64) : Bytes := List.replicate n.val.toNat 32

/--
Julia source: base/show.jl:104-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _truncate_at_width_or_chars(ignore_ANSI::Bool, str::AbstractString, width::Int, rpad::Bool=false, chars="\r\n", truncmark="…")
    truncwidth = textwidth(truncmark)
    (width <= 0 || width < truncwidth) && return ""
    wid = truncidx = lastidx = 0
    # if str needs to be truncated, truncidx is the index of truncation.
    stop = false # once set, only ANSI delimiters will be kept as new characters.
    needANSIend = false # set if the last ANSI delimiter before truncidx is not "\033[0m".
    I = ignore_ANSI ? ANSIIterator(str) : pairs(str)
    for (i, c) in I
        if c isa ANSIDelimiter
            truncidx == 0 && (needANSIend = c != "\033[0m")
            lastidx = i + ncodeunits(c) - 1
        else
            stop && break
            wid += textwidth(c)
            truncidx == 0 && wid > (width - truncwidth) && (truncidx = lastidx)
            lastidx = i
            c in chars && break
            stop = wid >= width
        end
    end
    lastidx == 0 && return rpad ? ' '^width : ""
    str[lastidx] in chars && (lastidx = prevind(str, lastidx))
    ANSIend = needANSIend ? "\033[0m" : ""
    pad = rpad ? repeat(' ', max(0, width-wid)) : ""
    truncidx == 0 && (truncidx = lastidx)
    if lastidx < lastindex(str)
        return string(SubString(str, 1, truncidx), ANSIend, truncmark, pad)
    else
        return string(str, ANSIend, pad)
    end
end

```
-/
def _truncate_at_width_or_chars {S C : Type} (s : StrOps S C) (ignore_ANSI : Bool) (str : S) (width : JInt64)
    (rpad : Bool := false) (chars : List C := [s.ofChar '\r', s.ofChar '\n'])
    (truncmark : List C := [s.ofChar '…']) : m Bytes := do
  let truncwidth := textwidthChars s truncmark
  if width.val ≤ 0 || width.val < truncwidth.val then return []
  let mut wid := i64 0
  let mut truncidx := i64 0
  let mut lastidx := i64 0
  let mut stop := false
  let mut needANSIend := false
  let I : List (JInt64 × ANSIChar C) :=
    if ignore_ANSI then s.ansiPairs str else (s.pairs str).map fun (i, c) => (i, .char c)
  for (i, c) in I do
    match c with
    | .delim d =>
      -- `c != "\033[0m"` compares an `ANSIDelimiter` with a `String`: `==` falls back to `===`,
      -- which is `false`.
      if truncidx.val == 0 then needANSIend := true
      lastidx := i64 (i.val + (ncodeunits_ANSIDelimiter d).val - 1)
    | .char c =>
      if stop then break
      wid := i64 (wid.val + (s.textwidthChar c).val)
      if truncidx.val == 0 && wid.val > (i64 (width.val - truncwidth.val)).val then truncidx := lastidx
      lastidx := i
      if chars.any (s.charEq c) then break
      stop := wid.val ≥ width.val
  if lastidx.val == 0 then return (if rpad then spaces width else [])
  let last ← match s.getindex str lastidx with
    | some c => pure c
    | none => throwShow .stringIndexError
  if chars.any (s.charEq last) then lastidx := s.prevind str lastidx
  let ANSIend := if needANSIend then lit "\x1b[0m" else []
  let pad := if rpad then spaces (i64 (max 0 (i64 (width.val - wid.val)).val)) else []
  if truncidx.val == 0 then truncidx := lastidx
  if lastidx.val < (s.lastindex str).val then
    let pre ← match s.prefixBytes str truncidx with
      | some b => pure b
      | none => throwShow .stringIndexError
    return pre ++ ANSIend ++ (truncmark.map s.charBytes).flatten ++ pad
  else
    return s.bytes str ++ ANSIend ++ pad

/-- *dispatch*: `displaysize(io)`. -/
def displaysize (p : IOPrims m Io V) (a : AnyOps V Ty) : JIO Io V → m (JInt64 × JInt64)
  | .context c => displaysize_IOContext p a c
  | .plain io => p.displaysize io

/-- `typemax(Int)`. -/
def typemaxInt : JInt64 := i64 (IntTy.max .i64)

/--
Julia source: base/show.jl:137-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", iter::Union{KeySet,ValueIterator})
    isempty(iter) && get(io, :compact, false)::Bool && return show(io, iter)
    summary(io, iter)
    isempty(iter) && return
    print(io, ". ", isa(iter,KeySet) ? "Keys" : "Values", ":")
    limit = get(io, :limit, false)::Bool
    if limit
        sz = displaysize(io)
        rows, cols = sz[1] - 3, sz[2]
        rows < 2 && (print(io, " …"); return)
        cols < 4 && (cols = 4)
        cols -= 2 # For prefix "  "
        rows -= 1 # For summary
    else
        rows = cols = typemax(Int)
    end

    for (i, v) in enumerate(iter)
        print(io, "\n  ")
        i == rows < length(iter) && (print(io, "⋮"); break)

        if limit
            str = sprint(show, v, context=io, sizehint=0)
            str = _truncate_at_width_or_chars(get(io, :color, false)::Bool, str, cols)
            print(io, str)
        else
            show(io, v)
        end
    end
end

```
-/
def show_textplain_KeySetValues {I X S C : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (s : StrOps S C)
    (isempty : I → Bool) (isKeySet : Bool) (items : I → List X) (length : I → JInt64)
    (showIter : JIO Io V → I → m Unit) (summary : JIO Io V → I → m Unit)
    (sprintShow : JIO Io V → X → m S) (showX : JIO Io V → X → m Unit) (io : JIO Io V) (iter : I) :
    m Unit := do
  if isempty iter then
    if ← assertBool a (getIO p io "compact" false) then return ← showIter io iter
  summary io iter
  if isempty iter then return
  printAll p io [printStr p io ". ", printStr p io (if isKeySet then "Keys" else "Values"), printStr p io ":"]
  let limit ← assertBool a (getIO p io "limit" false)
  let mut rows := typemaxInt
  let mut cols := typemaxInt
  if limit then
    let sz ← displaysize p a io
    rows := i64 (sz.1.val - 3)
    cols := sz.2
    if rows.val < 2 then
      printStr p io " …"
      return
    if cols.val < 4 then cols := i64 4
    cols := i64 (cols.val - 2)
    rows := i64 (rows.val - 1)
  else
    rows := typemaxInt
    cols := typemaxInt
  let mut i := i64 1
  for v in items iter do
    printStr p io "\n  "
    if i.val == rows.val && rows.val < (length iter).val then
      printStr p io "⋮"
      break
    if limit then
      let str ← sprintShow io v
      let str ← _truncate_at_width_or_chars s (← assertBool a (getIO p io "color" false)) str cols
      printBytes p io str
    else
      showX io v
    i := i64 (i.val + 1)

/-- `clamp(x, lo, hi)` of `Int`s (`base/intfuncs.jl`). -/
def clampInt (x lo hi : JInt64) : m JInt64 :=
  ofJl (JuliaLean.base.intfuncs.clamp (fun x hi => decide (x.val > hi.val)) (fun x lo => decide (x.val < lo.val))
    pure pure pure x lo hi)

/-- `cond ? a : b` with a `get(io, key, default)` result that is not asserted `::Bool`. -/
def condBool (a : AnyOps V Ty) (c : V ⊕ Bool) : m Bool := assertBool a c

/-- A `Bool` argument passed to a method declared `ignore_ANSI::Bool`: a non-`Bool` value has no
method. -/
def argBool (a : AnyOps V Ty) (fn : String) : V ⊕ Bool → m Bool
  | .inr b => pure b
  | .inl v => match a.asBool v with
    | some b => pure b
    | none => throwShow (.jl (.methodError fn))

/-- `Vector{String}(undef, n)` entries: `none` is an undefined reference. -/
def readEntry {S : Type} (xs : List (Option S)) (i : JInt64) : m S :=
  if h : 1 ≤ i.val ∧ i.val ≤ xs.length then
    match xs[(i.val - 1).toNat]'(by omega) with
    | some x => pure x
    | none => throwShow .undefRefError
  else throwShow (.jl .boundsError)

def writeEntry {S : Type} (xs : List (Option S)) (i : JInt64) (x : S) : m (List (Option S)) :=
  if 1 ≤ i.val ∧ i.val ≤ xs.length then pure (xs.set (i.val - 1).toNat (some x))
  else throwShow (.jl .boundsError)

/--
Julia source: base/show.jl:168-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", t::AbstractDict{K,V}) where {K,V}
    (isempty(t) || !haslength(t)) && return show(io, t)
    # show more descriptively, with one line per key/value pair
    recur_io = IOContext(io, :SHOWN_SET => t)
    limit = get(io, :limit, false)::Bool
    if !haskey(io, :compact)
        recur_io = IOContext(recur_io, :compact => true)
    end
    recur_io_k = IOContext(recur_io, :typeinfo=>keytype(t))
    recur_io_v = IOContext(recur_io, :typeinfo=>valtype(t))

    summary(io, t)
    isempty(t) && return
    print(io, ":")
    show_circular(io, t) && return
    keywidth = 0
    if limit
        sz = displaysize(io)
        rows, cols = sz[1] - 3, sz[2]
        rows < 2   && (print(io, " …"); return)
        cols < 12  && (cols = 12) # Minimum widths of 2 for key, 4 for value
        cols -= 6 # Subtract the widths of prefix "  " separator " => "
        rows -= 1 # Subtract the summary

        # determine max key width to align the output, caching the strings
        hascolor = get(recur_io, :color, false)
        ks = Vector{String}(undef, min(rows, length(t)))
        vs = Vector{String}(undef, min(rows, length(t)))
        valwidth = 0
        for (i, (k, v)) in enumerate(t)
            i > rows && break
            ks[i] = sprint(show, k, context=recur_io_k, sizehint=0)
            vs[i] = sprint(show, v, context=recur_io_v, sizehint=0)
            keywidth = clamp(hascolor ? textwidth(ANSIIterator(ks[i])) : textwidth(ks[i]), keywidth, cols)
            valwidth = clamp(hascolor ? textwidth(ANSIIterator(vs[i])) : textwidth(vs[i]), valwidth, cols)
        end
        if keywidth > max(div(cols, 2), cols - valwidth)
            keywidth = max(cld(cols, 3), cols - valwidth)
        end
    else
        rows = cols = typemax(Int)
    end

    for (i, (k, v)) in enumerate(t)
        print(io, "\n  ")
        if i == rows < length(t)
            print(io, rpad("⋮", keywidth), " => ⋮")
            break
        end

        if limit
            key = _truncate_at_width_or_chars(hascolor, ks[i], keywidth, true)
        else
            key = sprint(show, k, context=recur_io_k, sizehint=0)
        end
        print(recur_io, key)
        print(io, " => ")

        if limit
            val = _truncate_at_width_or_chars(hascolor, vs[i], cols - keywidth)
            print(io, val)
        else
            show(recur_io_v, v)
        end
    end
end

```
-/
def show_textplain_AbstractDict {D K W S C : Type} (p : IOPrims m Io V) (a : AnyOps V Ty)
    (s : StrOps S C) (isempty : D → Bool) (haslength : D → Bool) (length : D → JInt64)
    (pairs : D → List (K × W)) (keytype valtype : D → Ty) (ofAny : D → V)
    (printstyled : PrintStyled m Io V) (stringInt : JInt64 → m Bytes) (egal : V → D → Bool)
    (showD : JIO Io V → D → m Unit) (summary : JIO Io V → D → m Unit)
    (sprintK : JIO Io V → K → m S) (sprintW : JIO Io V → W → m S) (showW : JIO Io V → W → m Unit)
    (rpad : String → JInt64 → m Bytes) (io : JIO Io V) (d : D) : m Unit := do
  if isempty d || !haslength d then return ← showD io d
  let mut recur_io ← withShownSet p a ofAny io d
  let limit ← assertBool a (getIO p io "limit" false)
  if !haskey io "compact" then
    recur_io := .context (← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (boolConv a) recur_io
      ("compact", true))
  let recur_io_k ← withTypeinfo p a recur_io (keytype d)
  let recur_io_v ← withTypeinfo p a recur_io (valtype d)
  summary io d
  if isempty d then return
  printStr p io ":"
  if ← show_circular p printstyled stringInt egal io d then return
  let mut keywidth := i64 0
  let mut rows := typemaxInt
  let mut cols := typemaxInt
  -- `hascolor`, `ks` and `vs` are assigned only when `limit` holds.
  let mut hascolor : V ⊕ Bool := .inr false
  let mut ks : List (Option S) := []
  let mut vs : List (Option S) := []
  if limit then
    let sz ← displaysize p a io
    rows := i64 (sz.1.val - 3)
    cols := sz.2
    if rows.val < 2 then
      printStr p io " …"
      return
    if cols.val < 12 then cols := i64 12
    cols := i64 (cols.val - 6)
    rows := i64 (rows.val - 1)
    hascolor := getIO p recur_io "color" false
    let n := min rows.val (length d).val
    if n < 0 then throwShow (.jl (.argumentError "invalid Array dimensions"))
    ks := List.replicate n.toNat none
    vs := List.replicate n.toNat none
    let mut valwidth := i64 0
    let mut i := i64 1
    for (k, v) in pairs d do
      if i.val > rows.val then break
      ks ← writeEntry ks i (← sprintK recur_io_k k)
      vs ← writeEntry vs i (← sprintW recur_io_v v)
      let kw ← readEntry ks i
      keywidth ← clampInt (if ← condBool a hascolor then textwidth_ANSIIterator s.textwidthChar (s.ansiPairs kw)
        else textwidthStr s kw) keywidth cols
      let vw ← readEntry vs i
      valwidth ← clampInt (if ← condBool a hascolor then textwidth_ANSIIterator s.textwidthChar (s.ansiPairs vw)
        else textwidthStr s vw) valwidth cols
      i := i64 (i.val + 1)
    if keywidth.val > max (← ofJl (JInt.div cols (i64 2))).val (i64 (cols.val - valwidth.val)).val then
      keywidth := i64 (max (← ofJl (JuliaLean.base.div.cldBitInteger cols (i64 3))).val
        (i64 (cols.val - valwidth.val)).val)
  else
    rows := typemaxInt
    cols := typemaxInt
  let mut i := i64 1
  for (k, v) in pairs d do
    printStr p io "\n  "
    if i.val == rows.val && rows.val < (length d).val then
      let r ← rpad "⋮" keywidth
      printAll p io [printBytes p io r, printStr p io " => ⋮"]
      break
    let key ← if limit then
        _truncate_at_width_or_chars s (← argBool a "_truncate_at_width_or_chars" hascolor) (← readEntry ks i)
          keywidth true
      else s.bytes <$> sprintK recur_io_k k
    printBytes p recur_io key
    printStr p io " => "
    if limit then
      let val ← _truncate_at_width_or_chars s (← argBool a "_truncate_at_width_or_chars" hascolor)
        (← readEntry vs i) (i64 (cols.val - keywidth.val))
      printBytes p io val
    else
      showW recur_io_v v
    i := i64 (i.val + 1)

/--
Julia source: base/show.jl:235-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function summary(io::IO, t::AbstractSet)
    n = length(t)
    showarg(io, t, true)
    print(io, " with ", n, (n==1 ? " element" : " elements"))
end

```
-/
def summary_AbstractSet {T : Type} (p : IOPrims m Io V) (length : T → JInt64)
    (showarg : JIO Io V → T → Bool → m Unit) (printInt : JIO Io V → JInt64 → m Unit) (io : JIO Io V) (t : T) :
    m Unit := do
  let n := length t
  showarg io t true
  printAll p io [printStr p io " with ", printInt io n,
    printStr p io (if n.val == 1 then " element" else " elements")]

/--
Julia source: base/show.jl:241-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", t::AbstractSet{T}) where T
    isempty(t) && return show(io, t)
    # show more descriptively, with one line per value
    recur_io = IOContext(io, :SHOWN_SET => t)
    limit = get(io, :limit, false)::Bool

    summary(io, t)
    isempty(t) && return
    print(io, ":")
    show_circular(io, t) && return
    if limit
        sz = displaysize(io)
        rows, cols = sz[1] - 3, sz[2]
        rows < 2   && (print(io, " …"); return)
        cols -= 2 # Subtract the width of prefix "  "
        cols < 4  && (cols = 4) # Minimum widths of 4 for value
        rows -= 1 # Subtract the summary
    else
        rows = cols = typemax(Int)
    end

    for (i, v) in enumerate(t)
        print(io, "\n  ")
        if i == rows < length(t)
            print(io, rpad("⋮", 2))
            break
        end

        if limit
            str = sprint(show, v, context=recur_io, sizehint=0)
            print(io, _truncate_at_width_or_chars(get(io, :color, false)::Bool, str, cols))
        else
            show(recur_io, v)
        end
    end
end

```
-/
def show_textplain_AbstractSet {T X S C : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (s : StrOps S C)
    (isempty : T → Bool) (length : T → JInt64) (items : T → List X) (ofAny : T → V)
    (printstyled : PrintStyled m Io V) (stringInt : JInt64 → m Bytes) (egal : V → T → Bool)
    (showT : JIO Io V → T → m Unit) (summary : JIO Io V → T → m Unit)
    (sprintShow : JIO Io V → X → m S) (showX : JIO Io V → X → m Unit) (rpad : String → JInt64 → m Bytes)
    (io : JIO Io V) (t : T) : m Unit := do
  if isempty t then return ← showT io t
  let recur_io ← withShownSet p a ofAny io t
  let limit ← assertBool a (getIO p io "limit" false)
  summary io t
  if isempty t then return
  printStr p io ":"
  if ← show_circular p printstyled stringInt egal io t then return
  let mut rows := typemaxInt
  let mut cols := typemaxInt
  if limit then
    let sz ← displaysize p a io
    rows := i64 (sz.1.val - 3)
    cols := sz.2
    if rows.val < 2 then
      printStr p io " …"
      return
    cols := i64 (cols.val - 2)
    if cols.val < 4 then cols := i64 4
    rows := i64 (rows.val - 1)
  else
    rows := typemaxInt
    cols := typemaxInt
  let mut i := i64 1
  for v in items t do
    printStr p io "\n  "
    if i.val == rows.val && rows.val < (length t).val then
      printBytes p io (← rpad "⋮" (i64 2))
      break
    if limit then
      let str ← sprintShow recur_io v
      printBytes p io (← _truncate_at_width_or_chars s (← assertBool a (getIO p io "color" false)) str cols)
    else
      showX recur_io v
    i := i64 (i.val + 1)


/--
Julia source: base/show.jl:294-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", t::Task)
    show(io, t)
    if istaskfailed(t)
        println(io)
        show_task_exception(io, t, indent = false)
    end
end

```
-/
def show_textplain_Task {T : Type} (p : IOPrims m Io V) (showT : JIO Io V → T → m Unit)
    (istaskfailed : T → m Bool) (show_task_exception : JIO Io V → T → Bool → m Unit) (io : JIO Io V)
    (t : T) : m Unit := do
  showT io t
  if ← istaskfailed t then
    println p io []
    show_task_exception io t false

/-- `cancel_severity(src).request` (`base/cancellation.jl`, no model): `none` for `nothing`. -/
structure CancelOps (m : Type → Type) (Src : Type) where
  severityRequest : Src → m (Option (JInt .u8))
  /-- `Int(src.nparents)`. -/
  nparents : Src → m JInt64

/--
Julia source: base/show.jl:302-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Compact summary: the default field-recursive show would descend the
# intrusive child list (unbounded, possibly very deep) via `child_head`.
function show(io::IO, src::Core.CancellationTokenSource)
    print(io, "CancellationTokenSource(")
    sev = cancel_severity(src)
    if sev === nothing
        print(io, "active")
    else
        r = sev.request
        print(io, r == 0x1 ? "cancelled" :
                  r == 0x3 ? "cancelled, abandon external" :
                  r == 0x4 ? "cancelled, abandon all" :
                  "cancelled, severity $(repr(r))")
    end
    np = Int(src.nparents)
    np > 0 && print(io, ", ", np, np == 1 ? " parent" : " parents")
    print(io, ")")
end


```
-/
def show_CancellationTokenSource {Src : Type} (p : IOPrims m Io V) (c : CancelOps m Src)
    (reprU8 : JInt .u8 → m Bytes) (printInt : JIO Io V → JInt64 → m Unit) (io : JIO Io V) (src : Src) :
    m Unit := do
  printStr p io "CancellationTokenSource("
  let sev ← c.severityRequest src
  match sev with
  | none => printStr p io "active"
  | some r =>
    let msg ← if r.val == 1 then pure (lit "cancelled")
      else if r.val == 3 then pure (lit "cancelled, abandon external")
      else if r.val == 4 then pure (lit "cancelled, abandon all")
      else do pure (lit "cancelled, severity " ++ (← reprU8 r))
    printBytes p io msg
  let np ← c.nparents src
  if np.val > 0 then
    printAll p io [printStr p io ", ", printInt io np, printStr p io (if np.val == 1 then " parent" else " parents")]
  printStr p io ")"


-- UNTRANSLATED
-- module definition; no method
-- Source: base/show.jl:580-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- module UsesBaseOnly
-- end
-- 
-- /Source


/--
Julia source: base/show.jl:603-605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, f::Function) = show_function(io, f, get(io, :compact, false)::Bool, show_default)
print(io::IO, f::Function) = show_function(io, f, true, show)

```
-/
def show_Function {F : Type} (p : IOPrims m Io V) (a : AnyOps V Ty)
    (show_function : JIO Io V → F → Bool → (JIO Io V → F → m Unit) → m Unit)
    (show_default : JIO Io V → F → m Unit) (io : JIO Io V) (f : F) : m Unit := do
  show_function io f (← assertBool a (getIO p io "compact" false)) show_default
def print_Function {F : Type} (show_function : JIO Io V → F → Bool → (JIO Io V → F → m Unit) → m Unit)
    (showF : JIO Io V → F → m Unit) (io : JIO Io V) (f : F) : m Unit :=
  show_function io f true showF

/--
Julia source: base/show.jl:606-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, f::Core.IntrinsicFunction)
    if !(get(io, :compact, false)::Bool)
        print(io, "Core.Intrinsics.")
    end
    print(io, nameof(f))
end

```
-/
def show_IntrinsicFunction {F : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (nameof : F → Sym)
    (io : JIO Io V) (f : F) : m Unit := do
  if !(← assertBool a (getIO p io "compact" false)) then
    printStr p io "Core.Intrinsics."
  print_Symbol p io (nameof f)

/--
Julia source: base/show.jl:613-614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, f::Core.IntrinsicFunction) = print(io, nameof(f))

```
-/
def print_IntrinsicFunction {F : Type} (p : IOPrims m Io V) (nameof : F → Sym) (io : JIO Io V) (f : F) :
    m Unit :=
  print_Symbol p io (nameof f)

/--
Julia source: base/show.jl:615-616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::MIME"text/plain", ::Core.TypeofBottom) = print(io, "Union{}")

```
-/
def show_textplain_TypeofBottom (p : IOPrims m Io V) (io : JIO Io V) : m Unit :=
  printStr p io "Union{}"


/--
Julia source: base/show.jl:622-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function io_has_tvar_name(io::IOContext, name::Symbol, @nospecialize(x))
    for (key, val) in io.dict
        if key === :unionall_env && val isa TypeVar && val.name === name && has_typevar(x, val)
            return true
        end
    end
    return false
end
io_has_tvar_name(io::IO, name::Symbol, @nospecialize(x)) = false

```
-/
def io_has_tvar_name_IOContext {X TV : Type} (asTypeVar : V → Option TV) (tvName : TV → Sym)
    (has_typevar : X → TV → Bool) (io : IOContext Io V) (name : Sym) (x : X) : Bool := Id.run do
  for (key, val) in io.dict do
    match asTypeVar val with
    | some tv =>
      if key == "unionall_env" && tvName tv == name && has_typevar x tv then
        return true
    | none => pure ()
  return false
def io_has_tvar_name_IO {X : Type} (_io : Io) (_name : Sym) (_x : X) : Bool := false


/--
Julia source: base/show.jl:769-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isgensym(s::Symbol) = '#' in string(s)

```
-/
def isgensym (s : Sym) : Bool := s.toList.contains '#'



/--
Julia source: base/show.jl:1378-1385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_supertypes(io::IO, typ::DataType)
    print(io, typ)
    while typ != Any
        typ = supertype(typ)
        print(io, " <: ", typ)
    end
end

```
-/
def show_supertypes_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V)
    (t : TypeOps m Ty) (supertype : Ty → m Ty) (printType : JIO Io V → Ty → m Unit) (io : JIO Io V)
    (typ : Ty) : m Unit := do
  if !(← t.eq typ t.any) then
    let typ ← supertype typ
    printAll p io [printStr p io " <: ", printType io typ]
    show_supertypes_loop p t supertype printType io typ
partial_fixpoint
def show_supertypes [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V)
    (t : TypeOps m Ty) (supertype : Ty → m Ty) (printType : JIO Io V → Ty → m Unit) (io : JIO Io V)
    (typ : Ty) : m Unit := do
  printType io typ
  show_supertypes_loop p t supertype printType io typ

/--
Julia source: base/show.jl:1386-1387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_supertypes(typ::DataType) = show_supertypes(stdout, typ)

```
-/
def show_supertypes_stdout [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V)
    (t : TypeOps m Ty) (supertype : Ty → m Ty) (printType : JIO Io V → Ty → m Unit) (stdout : JIO Io V)
    (typ : Ty) : m Unit :=
  show_supertypes p t supertype printType stdout typ

-- UNTRANSLATED
-- the `@show` macro builds an `Expr` at macro-expansion time
-- Source: base/show.jl:1388-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     @show exs...
-- 
-- Prints one or more expressions, and their results, to `stdout`, and returns the last result.
-- 
-- See also [`show`](@ref), [`@info`](@ref man-logging), [`println`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> x = @show 1+2
-- 1 + 2 = 3
-- 3
-- 
-- julia> @show x^2 x/2;
-- x ^ 2 = 9
-- x / 2 = 1.5
-- ```
-- """
-- macro show(exs...)
--     blk = Expr(:block)
--     for ex in exs
--         push!(blk.args, :(println($(sprint(show_unquoted,ex)*" = "),
--                                   repr(begin local value = $(esc(ex)) end))))
--     end
--     isempty(exs) || push!(blk.args, :value)
--     return blk
-- end
-- 
-- /Source

/--
Julia source: base/show.jl:1416-1421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, tn::Core.TypeName)
    print(io, "typename(")
    show_type_name(io, tn)
    print(io, ")")
end

```
-/
def show_TypeName {TN : Type} (p : IOPrims m Io V) (show_type_name : JIO Io V → TN → m Unit)
    (io : JIO Io V) (tn : TN) : m Unit := do
  printStr p io "typename("
  show_type_name io tn
  printStr p io ")"

/-- Modules: `parentmodule`, `nameof`, and identity with `Main`, `Base` and `Core`. -/
structure ModuleOps (Mod : Type) where
  parentmodule : Mod → Mod
  nameof : Mod → Sym
  /-- `===`. -/
  egal : Mod → Mod → Bool
  isMainBaseCore : Mod → Bool
  is_root_module : Mod → Bool

/--
Julia source: base/show.jl:1481-1494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The call to print_fullname above was originally `print(io, join(fullname(m),"."))`,
# which allocates. The method below provides the same behavior without allocating.
# See https://github.com/JuliaLang/julia/pull/42773 for perf information.
function print_fullname(io::IO, m::Module)
    mp = parentmodule(m)
    if m === Main || m === Base || m === Core || mp === m
        show_sym(io, nameof(m))
    else
        print_fullname(io, mp)
        print(io, '.')
        show_sym(io, nameof(m))
    end
end

```
-/
def print_fullname {Mod : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V)
    (md : ModuleOps Mod) (show_sym : JIO Io V → Sym → m Unit) (io : JIO Io V) (mod : Mod) : m Unit := do
  let mp := md.parentmodule mod
  if md.isMainBaseCore mod || md.egal mp mod then
    show_sym io (md.nameof mod)
  else
    print_fullname p md show_sym io mp
    printStr p io "."
    show_sym io (md.nameof mod)
partial_fixpoint

/--
Julia source: base/show.jl:1474-1480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, m::Module)
    if is_root_module(m)
        print(io, nameof(m))
    else
        print_fullname(io, m)
    end
end
```
-/
def show_Module {Mod : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (p : IOPrims m Io V)
    (md : ModuleOps Mod) (show_sym : JIO Io V → Sym → m Unit) (io : JIO Io V) (mod : Mod) : m Unit :=
  if md.is_root_module mod then
    print_Symbol p io (md.nameof mod)
  else
    print_fullname p md show_sym io mod

/-- `get!(names, name, i)` on a `Dict{String,Int}` given as its key–value association list. -/
def getBang (names : List (Bytes × JInt64)) (name : Bytes) (i : JInt64) : JInt64 × List (Bytes × JInt64) :=
  match names.lookup name with
  | some idx => (idx, names)
  | none => (i, names ++ [(name, i)])

/-- `names[name] = v`. -/
def setDict (names : List (Bytes × JInt64)) (name : Bytes) (v : JInt64) : List (Bytes × JInt64) :=
  if names.any (·.1 == name) then names.map fun (k, w) => if k == name then (k, v) else (k, w)
  else names ++ [(name, v)]

/--
Julia source: base/show.jl:1495-1517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sourceinfo_slotnames(src::CodeInfo) = sourceinfo_slotnames(src.slotnames)
function sourceinfo_slotnames(slotnames::Vector{Symbol})
    names = Dict{String,Int}()
    printnames = Vector{String}(undef, length(slotnames))
    for i in eachindex(slotnames)
        if slotnames[i] === :var"#unused#"
            printnames[i] = "_"
            continue
        end
        name = string(slotnames[i])
        idx = get!(names, name, i)
        if idx != i || isempty(name)
            printname = "$name@_$i"
            idx > 0 && (printnames[idx] = "$name@_$idx")
            names[name] = 0
        else
            printname = name
        end
        printnames[i] = printname
    end
    return printnames
end

```
-/
def sourceinfo_slotnames_CodeInfo {Src : Type} (slotnamesOf : Src → List Sym)
    (sourceinfo_slotnames : List Sym → m (List Bytes)) (src : Src) : m (List Bytes) :=
  sourceinfo_slotnames (slotnamesOf src)
def sourceinfo_slotnames (stringInt : JInt64 → m Bytes) (slotnames : List Sym) : m (List Bytes) := do
  let mut names : List (Bytes × JInt64) := []
  -- `Vector{String}(undef, length(slotnames))`
  let mut printnames : List (Option Bytes) := List.replicate slotnames.length none
  let mut i := i64 1
  for slot in slotnames do
    if slot == "#unused#" then
      printnames ← writeEntry printnames i (lit "_")
      i := i64 (i.val + 1)
      continue
    let name := lit slot
    let (idx, names') := getBang names name i
    names := names'
    let mut printname : Bytes := []
    if idx.val != i.val || name.isEmpty then
      printname := name ++ lit "@_" ++ (← stringInt i)
      if idx.val > 0 then
        printnames ← writeEntry printnames idx (name ++ lit "@_" ++ (← stringInt idx))
      names := setDict names name (i64 0)
    else
      printname := name
    printnames ← writeEntry printnames i printname
    i := i64 (i.val + 1)
  let mut out : List Bytes := []
  for k in List.range printnames.length do
    out := out ++ [← readEntry printnames (i64 (k + 1))]
  return out

universe w

/-- `xs[i]` on a `Vector`. -/
def atIdx {α : Type} (xs : List α) (i : JInt64) : m α :=
  if h : 1 ≤ i.val ∧ i.val ≤ xs.length then pure (xs[(i.val - 1).toNat]'(by omega))
  else throwShow (.jl .boundsError)

/--
Julia source: base/show.jl:1630-1665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## Abstract Syntax Tree (AST) printing ##

# Summary:
#   print(io, ex) defers to show_unquoted(io, ex)
#   show(io, ex) defers to show_unquoted(io, QuoteNode(ex))
#   show_unquoted(io, ex) does the heavy lifting
#
# AST printing should follow two rules:
#   1. Meta.parse(string(ex)) == ex
#   2. eval(Meta.parse(repr(ex))) == ex
#
# Rule 1 means that printing an expression should generate Julia code which
# could be reparsed to obtain the original expression. This code should be
# unambiguous and as readable as possible.
#
# Rule 2 means that showing an expression should generate a quoted version of
# print’s output. Parsing and then evaling this output should return the
# original expression.
#
# This is consistent with many other show methods, i.e.:
#   show(Set([1,2,3]))                     # ==> "Set{Int64}([2,3,1])"
#   eval(Meta.parse("Set{Int64}([2,3,1])")) # ==> An actual set
# While this isn’t true of ALL show methods, it is of all ASTs.

const ExprNode = Union{Expr, QuoteNode, SlotNumber, LineNumberNode, SSAValue,
                       GotoNode, GotoIfNot, GlobalRef, PhiNode, PhiCNode, UpsilonNode,
                       ReturnNode}
# Operators have precedence levels from 1-N, and show_unquoted defaults to a
# precedence level of 0 (the fourth argument). The top-level print and show
# methods use a precedence of -1 to specially allow space-separated macro syntax.
# IOContext(io, :unquote_fallback => false) tells show_unquoted to treat any
# Expr whose head is :$ as if it is inside a quote, preventing fallback to the
# "unhandled" case: this is used by print/string to be lawful to Rule 1 above.
# On the contrary, show/repr have to follow Rule 2, requiring any Expr whose
# head is :$ and which is not inside a quote to fallback to the "unhandled" case:
# this is behavior is triggered by IOContext(io, :unquote_fallback => true)
```
-/
-- `x isa ExprNode`.
def isExprNode {L : Type} : Value L → Bool
  | .expr .. | .quoteNode _ | .slotNumber _ | .lineNumberNode .. | .ssaValue _ | .gotoNode _ | .gotoIfNot ..
  | .globalRef .. | .phiNode .. | .phiCNode _ | .upsilonNode _ | .returnNode _ => true
  | _ => false

/--
Julia source: base/show.jl:1673-1692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## AST printing constants ##

const indent_width = 4
const quoted_syms = Set{Symbol}([:(:),:(::),:(:=),:(=),:(==),:(===),:(=>)])
const uni_syms = Set{Symbol}([:(::), :(<:), :(>:)])
const uni_ops = Set{Symbol}([:(+), :(-), :(!), :(¬), :(~), :(<:), :(>:), :(√), :(∛), :(∜), :(∓), :(±)])
const expr_infix_wide = Set{Symbol}([
    :(=), :(+=), :(-=), :(*=), :(/=), :(\=), :(^=), :(&=), :(|=), :(÷=), :(%=), :(>>>=), :(>>=), :(<<=),
    :(.=), :(.+=), :(.-=), :(.*=), :(./=), :(.\=), :(.^=), :(.&=), :(.|=), :(.÷=), :(.%=), :(.>>>=), :(.>>=), :(.<<=),
    :(&&), :(||), :(<:), :($=), :(⊻=), :(>:), :(-->),
    :(:=), :(≔), :(⩴), :(≕)])
const expr_infix = Set{Symbol}([:(:), :(->), :(::)])
const expr_infix_any = union(expr_infix, expr_infix_wide)
const expr_calls  = Dict(:call => ('(',')'), :calldecl => ('(',')'),
                         :ref => ('[',']'), :curly => ('{','}'), :(.) => ('(',')'))
const expr_parens = Dict(:tuple=>('(',')'), :vcat=>('[',']'),
                         :hcat =>('[',']'), :row =>('[',']'), :vect=>('[',']'),
                         :ncat =>('[',']'), :nrow =>('[',']'),
                         :braces=>('{','}'), :bracescat=>('{','}'))

```
-/
def indent_width : JInt64 := i64 4
def quoted_syms : List Sym := [":", "::", ":=", "=", "==", "===", "=>"]
def uni_syms : List Sym := ["::", "<:", ">:"]
def uni_ops : List Sym := ["+", "-", "!", "¬", "~", "<:", ">:", "√", "∛", "∜", "∓", "±"]
def expr_infix_wide : List Sym := [
  "=", "+=", "-=", "*=", "/=", "\\=", "^=", "&=", "|=", "÷=", "%=", ">>>=", ">>=", "<<=",
  ".=", ".+=", ".-=", ".*=", "./=", ".\\=", ".^=", ".&=", ".|=", ".÷=", ".%=", ".>>>=", ".>>=", ".<<=",
  "&&", "||", "<:", "$=", "⊻=", ">:", "-->",
  ":=", "≔", "⩴", "≕"]
def expr_infix : List Sym := [":", "->", "::"]
def expr_infix_any : List Sym := expr_infix ++ expr_infix_wide
def expr_calls : List (Sym × (String × String)) :=
  [("call", ("(", ")")), ("calldecl", ("(", ")")), ("ref", ("[", "]")), ("curly", ("{", "}")), (".", ("(", ")"))]
def expr_parens : List (Sym × (String × String)) :=
  [("tuple", ("(", ")")), ("vcat", ("[", "]")), ("hcat", ("[", "]")), ("row", ("[", "]")), ("vect", ("[", "]")),
    ("ncat", ("[", "]")), ("nrow", ("[", "]")), ("braces", ("{", "}")), ("bracescat", ("{", "}"))]

/-- `d[key]` of a constant `Dict`; `KeyError` when absent. -/
def dictGet {α : Type} (d : List (Sym × α)) (key : Sym) : m α :=
  match d.lookup key with
  | some v => pure v
  | none => throwShow (.dict .keyError)

/--
Julia source: base/show.jl:1750-1756 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_quoted(ex)            = false
is_quoted(ex::QuoteNode) = true
is_quoted(ex::Expr)      = is_expr(ex, :quote, 1) || is_expr(ex, :inert, 1)

unquoted(ex::QuoteNode)  = ex.value
unquoted(ex::Expr)       = ex.args[1]

```
-/
def is_quoted {L : Type} : Value L → Bool
  | .quoteNode _ => true
  | ex@(.expr ..) => is_expr_n ex "quote" (i64 1) || is_expr_n ex "inert" (i64 1)
  | _ => false
def unquoted_QuoteNode {L : Type} (value : Value L) : Value L := value
def unquoted_Expr {L : Type} (args : List (Value L)) : m (Value L) :=
  match args with
  | a :: _ => pure a
  | [] => throwShow (.jl .boundsError)

/-- `unquoted(ex)` for a `QuoteNode` or `Expr` (other values have no method). -/
def unquoted {L : Type} : Value L → m (Value L)
  | .quoteNode v => pure (unquoted_QuoteNode v)
  | .expr _ args => unquoted_Expr args
  | _ => throwShow (.jl (.methodError "unquoted"))

/-- `IRShow.ssa_warn_type_class` results. -/
inductive SSAWarn where
  | strong | mild | none

/-- Callees of the AST printer. -/
structure AstOps (m : Type → Type) (Io V L : Type) where
  lo : LeafOps L
  /-- `print(io, x)` and `show(io, x)` of a non-AST value. -/
  printLeaf : JIO Io V → L → m Unit
  showLeaf : JIO Io V → L → m Unit
  /-- `show(io, x)` of `Argument`, `NewvarNode`, `EnterNode`, `PiNode`, `CodeInfo` and
  `BindingPartition` values outside `show_unquoted` (untranslated `show` methods). -/
  showNode : JIO Io V → Value L → m Unit
  /-- The module `Core`. -/
  core : L
  /-- `x::Int`. -/
  asInt : L → Option JInt64
  /-- `isa(x, Union{Int, Int64, Float32, Float64})`, with whether `x == 0 && x isa Integer`. -/
  scalarCoef : L → Option Bool
  /-- `x isa Real && x < 0`. -/
  isNegativeReal : L → Bool
  isVersionNumber : L → Bool
  /-- `isa(x, String)`. -/
  asString : L → Option Bytes
  /-- `isa(x, AbstractString)`, with `String(x)`. -/
  asAbstractString : L → Option Bytes
  /-- `isa(x, Vector)`, with its elements. -/
  asVector : L → Option (List (Value L))
  isModule : L → Bool
  /-- `partition_owner(bpart).globalref`. -/
  partitionOwner : L → L × Sym
  /-- Module bindings: `isdefined(mod, name)`, `isconst(mod, name)`, `getfield(mod, name)`. -/
  isdefinedBinding : L → Sym → Bool
  isconstBinding : L → Sym → Bool
  getfieldBinding : L → Sym → m L
  /-- The module `Main`. -/
  main : L
  /-- `operator_precedence(s)` (`ccall(:jl_operator_precedence)`). -/
  operator_precedence : Sym → JInt64
  /-- `base/meta.jl` predicates. -/
  isoperator : Sym → Bool
  _isoperator : Sym → Bool
  ispostfixoperator : Sym → Bool
  isidentifier : Sym → Bool
  is_valid_identifier : Sym → Bool
  /-- `escape_raw_string(str)` and `escape_raw_string(io, str)`, `escape_string(io, str, esc)`
  (`base/strings/io.jl`). -/
  escape_raw_string : Bytes → Bytes
  escape_raw_string_io : JIO Io V → Bytes → m Unit
  escape_string_io : JIO Io V → Bytes → Bytes → m Unit
  /-- `repr(s::String)`. -/
  reprString : Bytes → m Bytes
  /-- `Base.Compiler.IRShow.ssa_warn_type_class(io, id)` and `warn_color()`. -/
  ssa_warn_type_class : JIO Io V → JInt64 → m SSAWarn
  warn_color : Sym
  /-- `v isa Vector{String}`, `v::Int` of `IOContext` values. -/
  asStringVector : V → Option (List Bytes)
  asIntV : V → Option JInt64
  /-- The name of the gensym'd symbol `beginsym`. -/
  beginsym : Sym
  /-- `string(n::Int)`. -/
  stringInt : JInt64 → m Bytes
  /-- `IOBuffer()` and `takestring!(buf)`. -/
  newBuffer : m Io
  takestring : Io → m Bytes
  /-- The tail of `with_output_color` (`base/util.jl`): `iscolor && (str = output_color_string(…));
  print(io, str)`, given `str`, `color`, `bold` and `iscolor`. -/
  styled : JIO Io V → Bytes → Sym → Bool → Bool → m Unit

/-- Monads in which `tryCatchThe ShowError` is monotone in both arguments; required, with
`Lean.Order.CCPO` and `MonoBind`, by the mutually recursive AST printer. -/
class MonoTryCatch (m : Type → Type) [Monad m] [MonadExceptOf ShowError m] [∀ α, Lean.Order.CCPO (m α)] : Prop where
  tryCatch_mono_left {α : Type} {a₁ a₂ : m α} {h : ShowError → m α} :
    Lean.Order.PartialOrder.rel a₁ a₂ →
      Lean.Order.PartialOrder.rel (tryCatchThe ShowError a₁ h) (tryCatchThe ShowError a₂ h)
  tryCatch_mono_right {α : Type} {a : m α} {h₁ h₂ : ShowError → m α} :
    (∀ e, Lean.Order.PartialOrder.rel (h₁ e) (h₂ e)) →
      Lean.Order.PartialOrder.rel (tryCatchThe ShowError a h₁) (tryCatchThe ShowError a h₂)

@[partial_fixpoint_monotone]
theorem monotone_tryCatchThe [∀ α, Lean.Order.CCPO (m α)] [MonoTryCatch m] {α : Type} {γ : Sort w}
    [Lean.Order.PartialOrder γ] (f : γ → m α) (h : γ → ShowError → m α) (hf : Lean.Order.monotone f)
    (hh : Lean.Order.monotone h) : Lean.Order.monotone (fun x => tryCatchThe ShowError (f x) (h x)) := by
  intro x₁ x₂ hx
  apply Lean.Order.PartialOrder.rel_trans
  · exact MonoTryCatch.tryCatch_mono_left (hf _ _ hx)
  · exact MonoTryCatch.tryCatch_mono_right (fun e => Lean.Order.monotone_apply e _ hh _ _ hx)

/-- A `print(io, xs...)` call (`base/strings/io.jl`): `lock(io)`, the prints, then `unlock(io)`,
also on an exception. -/
def locked (p : IOPrims m Io V) (io : JIO Io V) (body : m Unit) : m Unit := do
  lockIO p io
  tryCatchThe ShowError body (fun e => do unlockIO p io; throwThe ShowError e)
  unlockIO p io

@[partial_fixpoint_monotone]
theorem monotone_locked [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] {γ : Sort w}
    [Lean.Order.PartialOrder γ] (p : IOPrims m Io V) (io : JIO Io V) (f : γ → m Unit)
    (hf : Lean.Order.monotone f) : Lean.Order.monotone (fun x => locked p io (f x)) := by
  unfold locked
  apply Lean.Order.monotone_bind
  · exact Lean.Order.monotone_const _
  · apply Lean.Order.monotone_of_monotone_apply
    intro _
    apply Lean.Order.monotone_bind
    · exact monotone_tryCatchThe _ _ hf (Lean.Order.monotone_const _)
    · exact Lean.Order.monotone_const _

/-- `" "^n` / `' '^n`: `repeat`, which throws `ArgumentError` for `n < 0`. -/
def spacesRep (n : JInt64) : m Bytes :=
  if n.val < 0 then throwShow (.jl (.argumentError "can't repeat a string a negative number of times"))
  else pure (spaces n)

/-- `IOContext(io, key => b)` for a `Bool` value. -/
def withBool (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V) (key : Sym) (b : Bool) : m (JIO Io V) := do
  return .context (← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (boolConv a) io (key, b))

/-- `print(io, n::Int)`: `print(io, x) = (lock(io); show(io, x); unlock(io))` and
`show(io, n::Signed) = write(io, string(n))`. -/
def printInt {L : Type} (p : IOPrims m Io V) (c : AstOps m Io V L) (io : JIO Io V) (n : JInt64) : m Unit :=
  locked p io (do write p io (← c.stringInt n))

/-- The head of `show_block`: a `Symbol` or a `String`. -/
inductive BlockHead where
  | sym (s : Sym)
  | str (s : String)

def BlockHead.isSym : BlockHead → Sym → Bool
  | .sym s, t => s == t
  | .str _, _ => false

/-- `print(io, head)`. -/
def printHead (p : IOPrims m Io V) (io : JIO Io V) : BlockHead → m Unit
  | .sym s => print_Symbol p io s
  | .str s => printStr p io s

/-- The `args` argument of `show_block`: a `Vector` or another value. -/
inductive BlockArgs (L : Type) where
  | vec (args : List (Value L))
  | arg (x : Value L)

/-- `operator_precedence(x)`: `0` for a non-`Symbol` (`show.jl:1714`). -/
def operator_precedence_any {L : Type} (c : AstOps m Io V L) : Value L → JInt64
  | .symbol s => c.operator_precedence s
  | _ => i64 0

/-- The `x in quoted_syms` etc. tests. -/
def symIn (s : Sym) (set : List Sym) : Bool := set.contains s

/--
Julia source: base/show.jl:1983-1989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function valid_import_path(@nospecialize(ex), allow_as = true)
    if allow_as && is_expr(ex, :as) && length((ex::Expr).args) == 2
        ex = (ex::Expr).args[1]
    end
    return is_expr(ex, :(.)) && length((ex::Expr).args) > 0 && all(a->isa(a,Symbol), (ex::Expr).args)
end

```
-/
def valid_import_path {L : Type} (ex : Value L) (allow_as : Bool := true) : Bool :=
  let ex := if allow_as && is_expr ex "as" && (match ex with | .expr _ a => a.length == 2 | _ => false) then
      (match ex with
        | .expr _ (a :: _) => a
        | _ => ex)
    else ex
  is_expr ex "." && (match ex with
    | .expr _ args => args.length > 0 && args.all (fun a => match a with | .symbol _ => true | _ => false)
    | _ => false)

/--
Julia source: base/show.jl:2022-2033 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Wrap symbols for macro names to allow them to be printed literally
function allow_macroname(ex)
    if (ex isa Symbol && first(string(ex)) == '@') ||
       ex isa GlobalRef ||
       (is_expr(ex, :(.)) && length(ex.args) == 2 &&
        (is_expr(ex.args[2], :quote) || ex.args[2] isa QuoteNode))
       return Expr(:macroname, ex)
    else
        ex
    end
end

```
-/
def allow_macroname {L : Type} (ex : Value L) : m (Value L) := do
  let isMacroSym ← match ex with
    | .symbol s => match s.toList with
      | c :: _ => pure (c == '@')
      | [] => throwShow (.jl (.argumentError "collection must be non-empty"))
    | _ => pure false
  if isMacroSym || (match ex with | .globalRef .. => true | _ => false) ||
      (is_expr ex "." && (match ex with
        | .expr _ [_, a2] => is_expr a2 "quote" || (match a2 with | .quoteNode _ => true | _ => false)
        | _ => false)) then
    return .expr "macroname" [ex]
  else
    return ex

/--
Julia source: base/show.jl:2034-2038 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_core_macro(arg::GlobalRef, macro_name::AbstractString) = is_core_macro(arg, Symbol(macro_name))
is_core_macro(arg::GlobalRef, macro_name::Symbol) = arg == GlobalRef(Core, macro_name)
is_core_macro(@nospecialize(arg), macro_name::AbstractString) = false
is_core_macro(@nospecialize(arg), macro_name::Symbol) = false

```
-/
def is_core_macro_GlobalRef_String {L : Type} (lo : LeafOps L) (core : L) (arg : Value L) (macro_name : String) : Bool :=
  is_core_macro_GlobalRef lo core arg macro_name
where
  is_core_macro_GlobalRef (lo : LeafOps L) (core : L) (arg : Value L) (macro_name : Sym) : Bool :=
    -- `GlobalRef` has no `==` method: `==` is `===`.
    egal lo arg (.globalRef core macro_name)
/-- *dispatch*: `is_core_macro(arg, macro_name::Symbol)`; non-`GlobalRef` arguments give `false`. -/
def is_core_macro {L : Type} (lo : LeafOps L) (core : L) (arg : Value L) (macro_name : Sym) : Bool :=
  match arg with
  | .globalRef .. => is_core_macro_GlobalRef_String.is_core_macro_GlobalRef lo core arg macro_name
  | _ => false

/--
Julia source: base/show.jl:2840-2859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
resolvebinding(@nospecialize(ex)) = ex
resolvebinding(ex::QuoteNode) = ex.value
resolvebinding(ex::Symbol) = resolvebinding(GlobalRef(Main, ex))
function resolvebinding(ex::Expr)
    if ex.head === :. && isa(ex.args[2], Symbol)
        parent = resolvebinding(ex.args[1])
        if isa(parent, Module)
            return resolvebinding(GlobalRef(parent, ex.args[2]))
        end
    end
    return nothing
end
function resolvebinding(ex::GlobalRef)
    isdefined(ex.mod, ex.name) || return nothing
    isconst(ex.mod, ex.name) || return nothing
    m = getfield(ex.mod, ex.name)
    isa(m, Module) || return nothing
    return m
end

```
-/
def resolvebinding {L : Type} (c : AstOps m Io V L) : Value L → m (Value L)
  | .quoteNode v => pure v
  | .symbol s => resolvebinding_GlobalRef c c.main s
  | .expr head args => do
    if head == "." then
      match args with
      | a1 :: .symbol name :: _ =>
        let parent ← resolvebinding c a1
        match parent with
        | .leaf pm => if c.isModule pm then return ← resolvebinding_GlobalRef c pm name
        | _ => pure ()
      | _ :: _ :: _ => pure ()
      | _ => throwShow (.jl .boundsError)
    return .leaf c.lo.nothing
  | .globalRef mod name => resolvebinding_GlobalRef c mod name
  | ex => pure ex
where
  resolvebinding_GlobalRef (c : AstOps m Io V L) (mod : L) (name : Sym) : m (Value L) := do
    if !c.isdefinedBinding mod name then return .leaf c.lo.nothing
    if !c.isconstBinding mod name then return .leaf c.lo.nothing
    let mv ← c.getfieldBinding mod name
    if !c.isModule mv then return .leaf c.lo.nothing
    return .leaf mv

/--
Julia source: base/show.jl:2860-2865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ismodulecall(ex::Expr)
    return ex.head === :call && (ex.args[1] === GlobalRef(Base,:getfield) ||
                                ex.args[1] === GlobalRef(Core,:getfield)) &&
           isa(resolvebinding(ex.args[2]), Module)
end

```
-/
def ismodulecall {L : Type} (c : AstOps m Io V L) (head : Sym) (args : List (Value L)) : m Bool := do
  if head != "call" then return false
  let a1 ← match args[0]? with
    | some a => pure a
    | none => throwShow (.jl .boundsError)
  if !(egal c.lo a1 (.globalRef c.lo.base "getfield") || egal c.lo a1 (.globalRef c.core "getfield")) then
    return false
  let a2 ← match args[1]? with
    | some a => pure a
    | none => throwShow (.jl .boundsError)
  match ← resolvebinding c a2 with
  | .leaf x => return c.isModule x
  | _ => return false

/-- `args[i]` of an `Expr`'s `args`. -/
def argAt' {L : Type} (args : List (Value L)) (i : Nat) : m (Value L) :=
  match args[i - 1]? with
  | some x => if i = 0 then throwShow (.jl .boundsError) else pure x
  | none => throwShow (.jl .boundsError)

/-- `x::Expr`. -/
def asExpr' {L : Type} : Value L → m (Sym × List (Value L))
  | .expr h a => pure (h, a)
  | _ => throwShow .typeError

/-- The line argument of `show_linenumber`: an `Int` field of a `LineNumberNode` or an `Expr`
argument. -/
inductive LineArg (L : Type) where
  | int (n : JInt64)
  | val (x : Value L)

/-- `printstyled(io, xs...; color, bold)` (`base/util.jl`, `with_output_color`): `xs` are printed
into `IOContext(buf, io)`, then the buffer is styled and printed to `io`, also on an exception. -/
def printstyledStr {L : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (body : JIO Io V → m Unit) (color : Sym) (bold : Bool) : m Unit := do
  let buf ← c.newBuffer
  let iscolor ← assertBool a (getIO p io "color" false)
  let ctx := JIO.context (← IOContext_IO_IO p a (.plain buf) io)
  tryCatchThe ShowError (body ctx)
    (fun e => do c.styled io (← c.takestring buf) color bold iscolor; throwThe ShowError e)
  c.styled io (← c.takestring buf) color bold iscolor

/-- The `while isa(fg, Expr) && fg.head === :flatten` loop of `show_generator`, from `fg.args`:
the collected `ranges` (with the final `fg.args[2:end]`) and the final `fg.args`. -/
def generator_ranges {L : Type} : List (Value L) → m (List (List (Value L)) × List (Value L))
  | .expr _ (.expr h nargs :: gargs) :: _ => do
    if h == "flatten" then
      let (rs, fa) ← generator_ranges nargs
      return (gargs :: rs, fa)
    else
      return ([gargs, nargs.drop 1], nargs)
  | .expr _ (_ :: _) :: _ => throwShow .typeError
  | .expr _ [] :: _ => throwShow (.jl .boundsError)
  | _ :: _ => throwShow .typeError
  | [] => throwShow (.jl .boundsError)


/-- `x::Int` of an `Expr` argument. -/
def argInt {L : Type} (c : AstOps m Io V L) : Value L → m JInt64
  | .leaf x => match c.asInt x with
    | some n => pure n
    | none => throwShow .typeError
  | _ => throwShow .typeError

/-- `x::Bool`, or `x` used as an `if` condition, of an `Expr` argument. -/
def exprArgBool {L : Type} (c : AstOps m Io V L) : Value L → m Bool
  | .leaf x => match c.lo.asBool x with
    | some b => pure b
    | none => throwShow .typeError
  | _ => throwShow .typeError

/-- A `get(io, key, default::Bool)` result that is a `Bool`. -/
def getBoolPure (a : AnyOps V Ty) : V ⊕ Bool → Option Bool
  | .inl v => a.asBool v
  | .inr b => some b

/-- `s^n` (`repeat`), which throws `ArgumentError` for `n < 0`. -/
def repeatBytes (s : Bytes) (n : JInt64) : m Bytes :=
  if n.val < 0 then throwShow (.jl (.argumentError "can't repeat a string a negative number of times"))
  else pure (List.flatten (List.replicate n.val.toNat s))

/-- `args[2:2:end]`. -/
def everySecond {α : Type} : List α → List α
  | _ :: x :: rest => x :: everySecond rest
  | _ => []

/-- `minimum(operator_precedence, args[2:2:end]; init=typemax(Int))`. -/
def comp_prec_min {L : Type} (c : AstOps m Io V L) (args : List (Value L)) : JInt64 :=
  (everySecond args).foldl (fun acc x =>
    let q := operator_precedence_any c x
    if q.val < acc.val then q else acc) typemaxInt

/-- The 4-argument `:module` form: `isa(args[1], VersionNumber) && isa(args[2], Bool)`, with the flag,
name and body. -/
def module4 {L : Type} (c : AstOps m Io V L) : List (Value L) → Option (Bool × Value L × Value L)
  | [.leaf v, .leaf b, name, body] =>
    if c.isVersionNumber v then (c.lo.asBool b).map (fun f => (f, name, body)) else none
  | _ => none

/-- The `x"y"` macro test: `isa(args[1], Symbol) && nargs >= 3 && isa(args[3], String) &&
startswith(string(args[1]), "@") && endswith(string(args[1]), "_str")`. -/
def strMacro {L : Type} (c : AstOps m Io V L) : List (Value L) → Option (Sym × Bytes)
  | .symbol s :: _ :: .leaf x :: _ =>
    match c.asString x with
    | some str => if s.startsWith "@" && s.endsWith "_str" then some (s, str) else none
    | none => none
  | _ => none

/-- `join(io, args, ", ")` of `String`s. -/
def join_bytes (p : IOPrims m Io V) (io : JIO Io V) : List Bytes → m Unit
  | [] => pure ()
  | [x] => printBytes p io x
  | x :: xs => do printBytes p io x; printStr p io ", "; join_bytes p io xs

/-- `mname` of the `:macroname` branch: `(a2::Expr).args[1]` of a `:quote` expression, otherwise
`(a2::QuoteNode).value`. -/
def macroname_of {L : Type} (a2 : Value L) : m (Value L) :=
  if is_expr a2 "quote" then do
    let (_, qargs) ← asExpr' a2
    argAt' qargs 1
  else match a2 with
    | .quoteNode v => pure v
    | _ => throwShow .typeError

/--
Julia source: base/show.jl:1878-1894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## AST printing ##

function show_unquoted(io::IO, val::SSAValue, ::Int, ::Int)
    if get(io, :maxssaid, typemax(Int))::Int < val.id
        # invalid SSAValue, print this in red for better recognition
        printstyled(io, "%", val.id; color=:red)
    else
        cls = Base.Compiler.IRShow.ssa_warn_type_class(io, val.id)
        if cls === Base.Compiler.IRShow.SSA_WARN_TYPE_STRONG
            printstyled(io, "%", val.id; color=:light_red, bold=true)
        elseif cls === Base.Compiler.IRShow.SSA_WARN_TYPE_MILD
            printstyled(io, "%", val.id; color=warn_color(), bold=true)
        else
            print(io, "%", val.id)
        end
    end
end
```
-/
def show_unquoted_SSAValue {L : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (id : JInt64) : m Unit := do
  let maxssaid ← match getIO p io "maxssaid" typemaxInt with
    | .inl v => match c.asIntV v with
      | some n => pure n
      | none => throwShow .typeError
    | .inr n => pure n
  -- `print(io, "%", id)`
  let pct : JIO Io V → m Unit := fun io' => locked p io' (do printStr p io' "%"; printInt p c io' id)
  if maxssaid.val < id.val then
    -- invalid SSAValue, print this in red for better recognition
    printstyledStr p a c io pct "red" false
  else
    match ← c.ssa_warn_type_class io id with
    | .strong => printstyledStr p a c io pct "light_red" true
    | .mild => printstyledStr p a c io pct c.warn_color true
    | .none => pct io

/--
Julia source: base/show.jl:1914-1923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted(io::IO, ex::SlotNumber, ::Int, ::Int)
    slotid = ex.id
    slotnames = get(io, :SOURCE_SLOTNAMES, false)
    if isa(slotnames, Vector{String}) && slotid ≤ length(slotnames)
        print(io, slotnames[slotid])
    else
        print(io, "_", slotid)
    end
end

```
-/
def show_unquoted_SlotNumber {L : Type} (p : IOPrims m Io V) (c : AstOps m Io V L) (io : JIO Io V)
    (slotid : JInt64) : m Unit := do
  let slotnames := getIO p io "SOURCE_SLOTNAMES" false
  match slotnames with
  | .inl v =>
    match c.asStringVector v with
    | some names =>
      if slotid.val ≤ names.length then
        printBytes p io (← atIdx names slotid)
        return
    | none => pure ()
  | .inr _ => pure ()
  locked p io (do printStr p io "_"; printInt p c io slotid)

set_option maxHeartbeats 1600000 in
mutual

/--
Julia source: base/show.jl:1666-1667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(        io::IO, ex::ExprNode)    = (show_unquoted(IOContext(io, :unquote_fallback => false), ex, 0, -1); nothing)
show(         io::IO, ex::ExprNode)    = show_unquoted_quote_expr(IOContext(io, :unquote_fallback => true), ex, 0, -1)
```
-/
-- `print(io, x)` of an AST value: `ExprNode`s, `Symbol`s, non-AST values and the other node types.
def printValue {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ex : Value L) : m Unit := do
  if isExprNode ex then
    let ctx ← withBool p a io "unquote_fallback" false
    show_unquoted_4 p a c ctx ex (i64 0) (i64 (-1))
  else match ex with
    | .symbol s => print_Symbol p io s
    | .leaf x => c.printLeaf io x
    -- `print(io, x) = (lock(io); show(io, x); unlock(io))`
    | _ => locked p io (showValue p a c io ex)
partial_fixpoint

-- `show(io, x)` of an AST value; `show(io, s::Symbol)` is `show.jl:1628`.
def showValue {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ex : Value L) : m Unit := do
  if isExprNode ex then
    let ctx ← withBool p a io "unquote_fallback" true
    show_unquoted_quote_expr p a c ctx ex (i64 0) (i64 (-1))
  else match ex with
    | .symbol s => show_Symbol p a c io s
    | .leaf x => c.showLeaf io x
    | _ => c.showNode io ex
partial_fixpoint

/--
Julia source: base/show.jl:1628-1629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, s::Symbol) = show_unquoted_quote_expr(io, s, 0, 0)

```
-/
def show_Symbol {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (s : Sym) : m Unit :=
  show_unquoted_quote_expr p a c io (.symbol s) (i64 0) (i64 0)
partial_fixpoint

/--
Julia source: base/show.jl:1668-1672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_unquoted(io::IO, ex)              = show_unquoted(io, ex, 0, 0)
show_unquoted(io::IO, ex, indent::Int) = show_unquoted(io, ex, indent, 0)
show_unquoted(io::IO, ex, ::Int,::Int) = show(io, ex)
show_unquoted(io::IO, ex, indent::Int, prec::Int, ::Int) = show_unquoted(io, ex, indent, prec)

```
-/
def show_unquoted_2 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ex : Value L) : m Unit :=
  show_unquoted_4 p a c io ex (i64 0) (i64 0)
partial_fixpoint
def show_unquoted_3 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ex : Value L) (indent : JInt64) : m Unit :=
  show_unquoted_4 p a c io ex indent (i64 0)
partial_fixpoint
-- *dispatch*: `show_unquoted(io, ex, indent, prec)`; values without a method use
-- `show_unquoted(io, ex, ::Int, ::Int) = show(io, ex)`.
def show_unquoted_4 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ex : Value L) (indent prec : JInt64) : m Unit :=
  match ex with
  | .expr head args => show_unquoted_Expr p a c io head args indent prec (i64 0)
  | .ssaValue id => show_unquoted_SSAValue p a c io id
  | .symbol s => show_sym p c io s false
  | .lineNumberNode line file => show_linenumber p a c io (.int line) (some file)
  | .gotoNode label => locked p io (do printStr p io "goto %"; printInt p c io label)
  | .globalRef mod name => show_globalref p a c io mod name false
  | .bindingPartition b =>
    let (mod, name) := c.partitionOwner b
    show_globalref p a c io mod name false
  | .slotNumber id => show_unquoted_SlotNumber p c io id
  | .quoteNode v => show_unquoted_QuoteNode p a c io v indent
  | .argument n => show_unquoted_Argument p a c io n indent prec
  | .phiNode edges values => show_unquoted_PhiNode p a c io edges values indent
  | .phiCNode values => show_unquoted_PhiCNode p a c io values indent
  | .piNode val typ => show_unquoted_PiNode p a c io val typ indent
  | .upsilonNode val => show_unquoted_UpsilonNode p a c io val indent
  | .returnNode val => show_unquoted_ReturnNode p a c io val indent
  | .gotoIfNot cond dest => show_unquoted_GotoIfNot p a c io cond dest indent
  | _ => showValue p a c io ex
partial_fixpoint
-- *dispatch*: `show_unquoted(io, ex, indent, prec, quote_level)`.
def show_unquoted_5 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ex : Value L) (indent prec quote_level : JInt64) : m Unit :=
  match ex with
  | .expr head args => show_unquoted_Expr p a c io head args indent prec quote_level
  | _ => show_unquoted_4 p a c io ex indent prec
partial_fixpoint

/--
Julia source: base/show.jl:1766-1769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_linenumber(io::IO, line)       = printstyled(io, "#= line ", line, " =#", color=:light_black)
show_linenumber(io::IO, line, file) = printstyled(io, "#= ", file, ":", line, " =#", color=:light_black)
show_linenumber(io::IO, line, file::Nothing) = show_linenumber(io, line)

```
-/
-- `show_linenumber(io, line)`, `show_linenumber(io, line, file)` and `show_linenumber(io, line,
-- file::Nothing)`; `file = none` is the 2-argument call. `printstyled(io, xs...; color)` prints `xs`
-- into `IOContext(buf, io)` and then styles the buffer (`with_output_color`, `base/util.jl`).
def show_linenumber {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (line : LineArg L) (file : Option (Value L)) : m Unit := do
  let buf ← c.newBuffer
  let iscolor ← assertBool a (getIO p io "color" false)
  let ctx := JIO.context (← IOContext_IO_IO p a (.plain buf) io)
  tryCatchThe ShowError (locked p ctx (show_linenumber_body p a c ctx line file))
    (fun e => do c.styled io (← c.takestring buf) "light_black" false iscolor; throwThe ShowError e)
  c.styled io (← c.takestring buf) "light_black" false iscolor
partial_fixpoint

-- The printed arguments of `show_linenumber`; a `nothing` file is the 2-argument method.
def show_linenumber_body {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (line : LineArg L) : Option (Value L) → m Unit
  | none => do
    printStr p io "#= line "
    printLineArg p a c io line
    printStr p io " =#"
  | some f => do
    if isNothing c.lo f then
      show_linenumber_body p a c io line none
    else
      printStr p io "#= "
      printValue p a c io f
      printStr p io ":"
      printLineArg p a c io line
      printStr p io " =#"
partial_fixpoint

def printLineArg {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V) :
    LineArg L → m Unit
  | .int n => printInt p c io n
  | .val x => printValue p a c io x
partial_fixpoint

/--
Julia source: base/show.jl:1770-1789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# show a block, e g if/for/etc
function show_block(io::IO, head, args::Vector, body, indent::Int, quote_level::Int)
    print(io, head)
    if !isempty(args)
        print(io, ' ')
        if head === :elseif
            show_list(io, args, " ", indent, 0, quote_level)
        else
            show_list(io, args, ", ", indent, 0, quote_level)
        end
    end

    ind = head === :module || head === :baremodule ? indent : indent + indent_width
    exs = (is_expr(body, :block) || is_expr(body, :quote)) ? body.args : Any[body]
    for ex in exs
        print(io, '\n', " "^ind)
        show_unquoted(io, ex, ind, -1, quote_level)
    end
    print(io, '\n', " "^indent)
end
```
-/
def show_block_vec {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (head : BlockHead) (args : List (Value L)) (body : Value L) (indent quote_level : JInt64) : m Unit := do
  printHead p io head
  if !args.isEmpty then
    printStr p io " "
    if head.isSym "elseif" then
      show_list p a c io args (lit " ") indent (i64 0) quote_level false false
    else
      show_list p a c io args (lit ", ") indent (i64 0) quote_level false false
  let ind := if head.isSym "module" || head.isSym "baremodule" then indent else i64 (indent.val + indent_width.val)
  let exs := if is_expr body "block" || is_expr body "quote" then
      (match body with | .expr _ bargs => bargs | _ => [])
    else [body]
  show_block_loop p a c io ind quote_level exs
  let sp ← spacesRep indent
  locked p io (do printStr p io "\n"; printBytes p io sp)
partial_fixpoint

def show_block_loop {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ind quote_level : JInt64) : List (Value L) → m Unit
  | [] => pure ()
  | ex :: exs => do
    let sp ← spacesRep ind
    locked p io (do printStr p io "\n"; printBytes p io sp)
    show_unquoted_5 p a c io ex ind (i64 (-1)) quote_level
    show_block_loop p a c io ind quote_level exs
partial_fixpoint

/--
Julia source: base/show.jl:1790-1798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_block(io::IO,head,    block,i::Int, quote_level::Int) = show_block(io,head, [], block,i, quote_level)
function show_block(io::IO, head, arg, block, i::Int, quote_level::Int)
    if is_expr(arg, :block) || is_expr(arg, :quote)
        show_block(io, head, arg.args, block, i, quote_level)
    else
        show_block(io, head, Any[arg], block, i, quote_level)
    end
end

```
-/
def show_block_5 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (head : BlockHead) (block : Value L) (i quote_level : JInt64) : m Unit :=
  show_block_vec p a c io head [] block i quote_level
partial_fixpoint
-- *dispatch*: `show_block(io, head, args::Vector, …)` or `show_block(io, head, arg, block, …)`.
def show_block {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (head : BlockHead) (arg : BlockArgs L) (block : Value L) (i quote_level : JInt64) : m Unit :=
  match arg with
  | .vec args => show_block_vec p a c io head args block i quote_level
  | .arg x =>
    match x with
    | .leaf v =>
      match c.asVector v with
      | some args => show_block_vec p a c io head args block i quote_level
      | none => show_block_vec p a c io head [x] block i quote_level
    | _ =>
      if is_expr x "block" || is_expr x "quote" then
        show_block_vec p a c io head (match x with | .expr _ xa => xa | _ => []) block i quote_level
      else
        show_block_vec p a c io head [x] block i quote_level
partial_fixpoint

/--
Julia source: base/show.jl:1799-1826 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# show an indented list
function show_list(io::IO, items, sep, indent::Int, prec::Int=0, quote_level::Int=0, enclose_operators::Bool=false,
                   kw::Bool=false)
    n = length(items)
    n == 0 && return
    indent += indent_width
    first = true
    for item in items
        !first && print(io, sep)
        parens = !is_quoted(item) &&
            (first && prec >= prec_power &&
             ((item isa Expr && item.head === :call && (callee = item.args[1]; isa(callee, Symbol) && callee in uni_ops)) ||
              (item isa Real && item < 0))) ||
            (enclose_operators && item isa Symbol && isoperator(item) && is_valid_identifier(item))
        parens && print(io, '(')
        if kw && is_expr(item, :kw, 2)
            item = item::Expr
            show_unquoted(io, Expr(:(=), item.args[1], item.args[2]), indent, parens ? 0 : prec, quote_level)
        elseif kw && is_expr(item, :(=), 2)
            item = item::Expr
            show_unquoted_expr_fallback(io, item)
        else
            show_unquoted(io, item, indent, parens ? 0 : prec, quote_level)
        end
        parens && print(io, ')')
        first = false
    end
end
```
-/
def show_list {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (items : List (Value L)) (sep : Bytes) (indent : JInt64) (prec : JInt64 := i64 0)
    (quote_level : JInt64 := i64 0) (enclose_operators : Bool := false) (kw : Bool := false) : m Unit := do
  let n := items.length
  if n == 0 then return
  let indent := i64 (indent.val + indent_width.val)
  show_list_loop p a c io sep indent prec quote_level enclose_operators kw true items
partial_fixpoint

def show_list_loop {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (sep : Bytes) (indent prec quote_level : JInt64) (enclose_operators kw first : Bool) :
    List (Value L) → m Unit
  | [] => pure ()
  | item :: items => do
    if !first then printBytes p io sep
    -- `(callee = item.args[1]; …)` throws `BoundsError` for an `Expr(:call)` without arguments
    let unaryCall ← match item with
      | .expr "call" iargs => match iargs with
        | .symbol callee :: _ => pure (symIn callee uni_ops)
        | _ :: _ => pure false
        | [] => throwShow (.jl .boundsError)
      | _ => pure false
    let parens := (!is_quoted item &&
        (first && prec.val ≥ (c.operator_precedence "^").val &&
          (unaryCall || (match item with | .leaf x => c.isNegativeReal x | _ => false)))) ||
      (enclose_operators && (match item with
        | .symbol s => c.isoperator s && c.is_valid_identifier s
        | _ => false))
    if parens then printStr p io "("
    if kw && is_expr_n item "kw" (i64 2) then
      match item with
      | .expr _ [x1, x2] =>
        show_unquoted_5 p a c io (.expr "=" [x1, x2]) indent (if parens then i64 0 else prec) quote_level
      | _ => pure ()
    else if kw && is_expr_n item "=" (i64 2) then
      match item with
      | .expr head iargs => show_unquoted_expr_fallback p a c io head iargs
      | _ => pure ()
    else
      show_unquoted_5 p a c io item indent (if parens then i64 0 else prec) quote_level
    if parens then printStr p io ")"
    show_list_loop p a c io sep indent prec quote_level enclose_operators kw false items
partial_fixpoint

/--
Julia source: base/show.jl:1827-1833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# show an indented list inside the parens (op, cl)
function show_enclosed_list(io::IO, op, items, sep, cl, indent, prec=0, quote_level=0, encl_ops=false, kw::Bool=false)
    print(io, op)
    show_list(io, items, sep, indent, prec, quote_level, encl_ops, kw)
    print(io, cl)
end

```
-/
def show_enclosed_list {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (op : String) (items : List (Value L)) (sep : Bytes) (cl : String) (indent : JInt64) (prec : JInt64 := i64 0)
    (quote_level : JInt64 := i64 0) (encl_ops : Bool := false) (kw : Bool := false) : m Unit := do
  printStr p io op
  show_list p a c io items sep indent prec quote_level encl_ops kw
  printStr p io cl
partial_fixpoint

/--
Julia source: base/show.jl:1834-1863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# show a normal (non-operator) function call, e.g. f(x, y) or A[z]
# kw: `=` expressions are parsed with head `kw` in this context
function show_call(io::IO, head, func, func_args, indent, quote_level, kw::Bool)
    op, cl = expr_calls[head]
    if (isa(func, Symbol) && func !== :(:) && !(head === :. && isoperator(func))) ||
            (isa(func, Symbol) && !is_valid_identifier(func)) ||
            (isa(func, Expr) && (func.head === :. || func.head === :curly || func.head === :macroname)) ||
            isa(func, GlobalRef) ||
            isa(func, Core.BindingPartition)
        show_unquoted(io, func, indent, 0, quote_level)
    else
        print(io, '(')
        show_unquoted(io, func, indent, 0, quote_level)
        print(io, ')')
    end
    if head === :(.)
        print(io, '.')
    end
    if !isempty(func_args) && isa(func_args[1], Expr) && (func_args[1]::Expr).head === :parameters
        print(io, op)
        show_list(io, func_args[2:end], ", ", indent, 0, quote_level, false, kw)
        print(io, "; ")
        show_list(io, (func_args[1]::Expr).args, ", ", indent, 0, quote_level, false, kw)
        print(io, cl)
    else
        show_enclosed_list(io, op, func_args, ", ", cl, indent, 0, quote_level, false, kw)
    end
end

```
-/
def show_call {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (head : Sym) (func : Value L) (func_args : List (Value L)) (indent quote_level : JInt64) (kw : Bool) :
    m Unit := do
  let (op, cl) ← dictGet expr_calls head
  let direct := (match func with
      | .symbol f => (f != ":" && !(head == "." && c.isoperator f)) || !c.is_valid_identifier f
      | .expr fh _ => fh == "." || fh == "curly" || fh == "macroname"
      | .globalRef .. | .bindingPartition _ => true
      | _ => false)
  if direct then
    show_unquoted_5 p a c io func indent (i64 0) quote_level
  else
    printStr p io "("
    show_unquoted_5 p a c io func indent (i64 0) quote_level
    printStr p io ")"
  if head == "." then
    printStr p io "."
  match func_args with
  | .expr "parameters" pargs :: rest =>
    printStr p io op
    show_list p a c io rest (lit ", ") indent (i64 0) quote_level false kw
    printStr p io "; "
    show_list p a c io pargs (lit ", ") indent (i64 0) quote_level false kw
    printStr p io cl
  | _ =>
    show_enclosed_list p a c io op func_args (lit ", ") cl indent (i64 0) quote_level false kw
partial_fixpoint

/--
Julia source: base/show.jl:1864-1877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Print `sym` as it would appear as an identifier name in code
# * Print valid identifiers & operators literally; also macros names if allow_macroname=true
# * Escape invalid identifiers with var"" syntax
function show_sym(io::IO, sym::Symbol; allow_macroname=false)
    if is_valid_identifier(sym)
        print(io, sym)
    elseif allow_macroname && (sym_str = string(sym); startswith(sym_str, '@'))
        print(io, '@')
        show_sym(io, Symbol(sym_str[2:end]))
    else
        print(io, "var\"", escape_raw_string(string(sym)), '"')
    end
end

```
-/
def show_sym {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (c : AstOps m Io V L) (io : JIO Io V) (sym : Sym)
    (allow_macroname : Bool := false) : m Unit := do
  if c.is_valid_identifier sym then
    print_Symbol p io sym
  else if allow_macroname && sym.startsWith "@" then
    printStr p io "@"
    show_sym p c io (String.ofList (sym.toList.drop 1)) false
  else
    let esc := c.escape_raw_string (lit sym)
    locked p io (do printStr p io "var\""; printBytes p io esc; printStr p io "\"")
partial_fixpoint

/--
Julia source: base/show.jl:1895-1913 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_unquoted(io::IO, sym::Symbol, ::Int, ::Int)        = show_sym(io, sym, allow_macroname=false)
show_unquoted(io::IO, ex::LineNumberNode, ::Int, ::Int) = show_linenumber(io, ex.line, ex.file)
show_unquoted(io::IO, ex::GotoNode, ::Int, ::Int)       = print(io, "goto %", ex.label)
show_unquoted(io::IO, ex::GlobalRef, ::Int, ::Int)      = show_globalref(io, ex)
show_unquoted(io::IO, bpart::Core.BindingPartition, ::Int, ::Int) =
    show_globalref(io, partition_owner(bpart).globalref)

function show_globalref(io::IO, ex::GlobalRef; allow_macroname=false)
    print(io, ex.mod)
    print(io, '.')
    quoted = !isidentifier(ex.name) && !startswith(string(ex.name), "@")
    parens = quoted && (!isoperator(ex.name) || (ex.name in quoted_syms))
    quoted && print(io, ':')
    parens && print(io, '(')
    show_sym(io, ex.name, allow_macroname=allow_macroname)
    parens && print(io, ')')
    nothing
end

```
-/
def show_globalref {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (mod : L) (name : Sym) (allow_macroname : Bool := false) : m Unit := do
  c.printLeaf io mod
  printStr p io "."
  let quoted := !c.isidentifier name && !name.startsWith "@"
  let parens := quoted && (!c.isoperator name || symIn name quoted_syms)
  if quoted then printStr p io ":"
  if parens then printStr p io "("
  show_sym p c io name allow_macroname
  if parens then printStr p io ")"
partial_fixpoint

/--
Julia source: base/show.jl:1924-1936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted(io::IO, ex::QuoteNode, indent::Int, _prec::Int)
    if isa(ex.value, Symbol)
        show_unquoted_quote_expr(io, ex.value, indent, 0)
    else
        print(io, "\$(QuoteNode(")
        # QuoteNode does not allows for interpolation, so if ex.value is an
        # Expr it should be shown with quote_level equal to zero.
        # Calling show(io, ex.value) like this implicitly enforce that.
        show(io, ex.value)
        print(io, "))")
    end
end

```
-/
def show_unquoted_QuoteNode {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (value : Value L) (indent : JInt64) : m Unit := do
  match value with
  | .symbol _ => show_unquoted_quote_expr p a c io value indent (i64 0)
  | _ =>
    printStr p io "$(QuoteNode("
    -- QuoteNode does not allows for interpolation, so if ex.value is an
    -- Expr it should be shown with quote_level equal to zero.
    showValue p a c io value
    printStr p io "))"
partial_fixpoint

/--
Julia source: base/show.jl:1937-1961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted_quote_expr(io::IO, @nospecialize(value), indent::Int, quote_level::Int)
    if isa(value, Symbol)
        sym = value::Symbol
        if value in quoted_syms
            print(io, ":(", sym, ")")
        else
            if isidentifier(sym) || (_isoperator(sym) && sym !== Symbol("'"))
                print(io, ":", sym)
            else
                print(io, "Symbol(", repr(String(sym)), ")")
            end
        end
    else
        if isa(value,Expr) && value.head === :block
            value = value::Expr
            show_block(IOContext(io, beginsym=>false), "quote", value, indent, quote_level)
            print(io, "end")
        else
            print(io, ":(")
            show_unquoted(io, value, indent+2, -1, quote_level)  # +2 for `:(`
            print(io, ")")
        end
    end
end

```
-/
def show_unquoted_quote_expr {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (value : Value L) (indent quote_level : JInt64) : m Unit := do
  match value with
  | .symbol sym =>
    if symIn sym quoted_syms then
      locked p io (do printStr p io ":("; print_Symbol p io sym; printStr p io ")")
    else if c.isidentifier sym || (c._isoperator sym && sym != "'") then
      locked p io (do printStr p io ":"; print_Symbol p io sym)
    else
      let r ← c.reprString (lit sym)
      locked p io (do printStr p io "Symbol("; printBytes p io r; printStr p io ")")
  | .expr "block" _ =>
    let ctx ← withBool p a io c.beginsym false
    show_block_5 p a c ctx (.str "quote") value indent quote_level
    printStr p io "end"
  | _ =>
    printStr p io ":("
    show_unquoted_5 p a c io value (i64 (indent.val + 2)) (i64 (-1)) quote_level -- +2 for `:(`
    printStr p io ")"
partial_fixpoint

/--
Julia source: base/show.jl:1962-1982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_generator(io, ex::Expr, indent, quote_level)
    if ex.head === :flatten
        fg::Expr = ex
        ranges = Any[]
        while isa(fg, Expr) && fg.head === :flatten
            push!(ranges, (fg.args[1]::Expr).args[2:end])
            fg = (fg.args[1]::Expr).args[1]::Expr
        end
        push!(ranges, fg.args[2:end])
        show_unquoted(io, fg.args[1], indent, 0, quote_level)
        for r in ranges
            print(io, " for ")
            show_list(io, r, ", ", indent, 0, quote_level)
        end
    else
        show_unquoted(io, ex.args[1], indent, 0, quote_level)
        print(io, " for ")
        show_list(io, ex.args[2:end], ", ", indent, 0, quote_level)
    end
end

```
-/
def show_generator {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (head : Sym) (args : List (Value L)) (indent quote_level : JInt64) : m Unit := do
  if head == "flatten" then
    let (ranges, fgargs) ← generator_ranges args
    show_unquoted_5 p a c io (← argAt' fgargs 1) indent (i64 0) quote_level
    show_generator_ranges p a c io indent quote_level ranges
  else
    show_unquoted_5 p a c io (← argAt' args 1) indent (i64 0) quote_level
    printStr p io " for "
    show_list p a c io (args.drop 1) (lit ", ") indent (i64 0) quote_level false false
partial_fixpoint

def show_generator_ranges {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (indent quote_level : JInt64) : List (List (Value L)) → m Unit
  | [] => pure ()
  | r :: rs => do
    printStr p io " for "
    show_list p a c io r (lit ", ") indent (i64 0) quote_level false false
    show_generator_ranges p a c io indent quote_level rs
partial_fixpoint

/--
Julia source: base/show.jl:1990-2021 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_import_path(io::IO, ex, quote_level)
    if !isa(ex, Expr)
        show_unquoted(io, ex)
    elseif ex.head === :(:)
        show_import_path(io, ex.args[1], quote_level)
        print(io, ": ")
        for i = 2:length(ex.args)
            if i > 2
                print(io, ", ")
            end
            show_import_path(io, ex.args[i], quote_level)
        end
    elseif ex.head === :(.)
        for i = 1:length(ex.args)
            sym = ex.args[i]::Symbol
            if sym === :(.)
                print(io, '.')
            else
                if sym === :(..)
                    # special case for https://github.com/JuliaLang/julia/issues/49168
                    print(io, "(..)")
                else
                    show_sym(io, sym, allow_macroname=(i==length(ex.args)))
                end
                i < length(ex.args) && print(io, '.')
            end
        end
    else
        show_unquoted(io, ex, 0, 0, quote_level)
    end
end

```
-/
def show_import_path {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ex : Value L) (quote_level : JInt64) : m Unit := do
  match ex with
  | .expr ":" args =>
    show_import_path p a c io (← argAt' args 1) quote_level
    printStr p io ": "
    show_import_path_rest p a c io quote_level true (args.drop 1)
  | .expr "." args =>
    show_import_path_dots p a c io args.length 1 args
  | .expr .. => show_unquoted_5 p a c io ex (i64 0) (i64 0) quote_level
  | _ => show_unquoted_2 p a c io ex
partial_fixpoint

def show_import_path_rest {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (quote_level : JInt64) (first : Bool) : List (Value L) → m Unit
  | [] => pure ()
  | x :: xs => do
    if !first then printStr p io ", "
    show_import_path p a c io x quote_level
    show_import_path_rest p a c io quote_level false xs
partial_fixpoint

def show_import_path_dots {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (n i : Nat) : List (Value L) → m Unit
  | [] => pure ()
  | x :: xs => do
    let sym ← match x with
      | .symbol s => pure s
      | _ => throwShow .typeError
    if sym == "." then
      printStr p io "."
    else
      if sym == ".." then
        -- special case for https://github.com/JuliaLang/julia/issues/49168
        printStr p io "(..)"
      else
        show_sym p c io sym (i == n)
      if i < n then printStr p io "."
    show_import_path_dots p a c io n (i + 1) xs
partial_fixpoint

/--
Julia source: base/show.jl:2039-2052 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# symbol for IOContext flag signaling whether "begin" is treated
# as an ordinary symbol, which is true in indexing expressions.
const beginsym = gensym(:beginsym)

function show_unquoted_expr_fallback(io::IO, ex::Expr)
    print(io, "\$(Expr(")
    show(io, ex.head)
    for arg in ex.args
        print(io, ", ")
        show(io, arg)
    end
    print(io, "))")
end

```
-/
def show_unquoted_expr_fallback {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (head : Sym) (args : List (Value L)) : m Unit := do
  printStr p io "$(Expr("
  show_Symbol p a c io head
  show_fallback_args p a c io args
  printStr p io "))"
partial_fixpoint

def show_fallback_args {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) : List (Value L) → m Unit
  | [] => pure ()
  | arg :: rest => do
    printStr p io ", "
    showValue p a c io arg
    show_fallback_args p a c io rest
partial_fixpoint

/--
Julia source: base/show.jl:2053-2607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# TODO: implement interpolated strings
function show_unquoted(io::IO, ex::Expr, indent::Int, prec::Int, quote_level::Int = 0)
    head, args, nargs = ex.head, ex.args, length(ex.args)
    unhandled = false
    # dot (i.e. "x.y"), but not compact broadcast exps
    if head === :(.) && (nargs != 2 || !is_expr(args[2], :tuple))
        # standalone .op
        if nargs == 1 && args[1] isa Symbol && isoperator(args[1]::Symbol)
            print(io, "(.", args[1], ")")
        elseif nargs == 2 && is_quoted(args[2])
            item = args[1]
            # field
            field = unquoted(args[2])
            parens = !is_quoted(item) && !(item isa Symbol && isidentifier(item)) && !is_expr(item, :(.))
            parens && print(io, '(')
            show_unquoted(io, item, indent, 0, quote_level)
            parens && print(io, ')')
            # .
            print(io, '.')
            # item
            if isa(field, Symbol)
                parens = field in quoted_syms
                quoted = parens || isoperator(field)
            else
                parens = quoted = true
            end
            quoted && print(io, ':')
            parens && print(io, '(')
            show_unquoted(io, field, indent, 0, quote_level)
            parens && print(io, ')')
        else
            unhandled = true
        end

    # infix (i.e. "x <: y" or "x = y")
    elseif (head in expr_infix_any && nargs==2)
        func_prec = operator_precedence(head)
        head_ = head in expr_infix_wide ? " $head " : head
        if head == :-> && is_expr(args[1], :...)
            args = Any[Expr(:tuple, args[1]), args[2]]
        end
        if func_prec <= prec
            show_enclosed_list(io, '(', args, head_, ')', indent, func_prec, quote_level, true)
        else
            show_list(io, args, head_, indent, func_prec, quote_level, true)
        end

    elseif head === :tuple
        print(io, "(")
        if nargs > 0 && is_expr(args[1], :parameters)
            arg1 = args[1]::Expr
            show_list(io, args[2:end], ", ", indent, 0, quote_level)
            nargs == 2 && print(io, ',')
            print(io, ";")
            if !isempty(arg1.args)
                print(io, " ")
            end
            show_list(io, arg1.args, ", ", indent, 0, quote_level, false, true)
        else
            show_list(io, args, ", ", indent, 0, quote_level)
            nargs == 1 && print(io, ',')
        end
        print(io, ")")

    # list-like forms, e.g. "[1, 2, 3]"
    elseif haskey(expr_parens, head) ||                          # :vcat etc.
        head === :typed_vcat || head === :typed_hcat || head === :typed_ncat
        # print the type and defer to the untyped case
        if head === :typed_vcat || head === :typed_hcat || head === :typed_ncat
            show_unquoted(io, args[1], indent, prec, quote_level)
            if head === :typed_vcat
                head = :vcat
            elseif head === :typed_hcat
                head = :hcat
            else
                head = :ncat
            end
            args = args[2:end]
            nargs = nargs - 1
        end
        op, cl = expr_parens[head]
        if head === :vcat || head === :bracescat
            sep = "; "
        elseif head === :hcat || head === :row
            sep = " "
        elseif head === :ncat || head === :nrow
            sep = ";"^args[1]::Int * " "
            args = args[2:end]
            nargs = nargs - 1
        else
            sep = ", "
        end
        head !== :row && head !== :nrow && print(io, op)
        show_list(io, args, sep, indent, 0, quote_level)
        if nargs <= 1 && (head === :vcat || head === :ncat)
            print(io, sep[1:end-1])
        end
        head !== :row && head !== :nrow && print(io, cl)

    # transpose
    elseif (head === Symbol("'") && nargs == 1) || (
        # ' with unicode suffix is a call expression
        head === :call && nargs == 2 && args[1] isa Symbol &&
        ispostfixoperator(args[1]::Symbol) && args[1]::Symbol !== Symbol("'")
    )
        op, arg1 = head === Symbol("'") ? (head, args[1]) : (args[1], args[2])
        if isa(arg1, Expr) || (isa(arg1, Symbol) && isoperator(arg1::Symbol))
            show_enclosed_list(io, '(', [arg1::Union{Expr, Symbol}], ", ", ')', indent, 0)
        else
            show_unquoted(io, arg1, indent, 0, quote_level)
        end
        print(io, op)

    # function call
    elseif head === :call && nargs >= 1
        func = args[1]
        fname = isa(func, GlobalRef) ? func.name : func
        func_prec = operator_precedence(fname)
        if func_prec > 0 || (isa(fname, Symbol) && fname in uni_ops)
            func = fname
        end
        func_args = args[2:end]

        # :kw exprs are only parsed inside parenthesized calls
        if any(a->is_expr(a, :kw), func_args) || (!isempty(func_args) && is_expr(func_args[1], :parameters))
            show_call(io, head, func, func_args, indent, quote_level, true)

        # scalar multiplication (i.e. "100x")
        elseif (func === :* &&
            length(func_args) == 2 && isa(func_args[1], Union{Int, Int64, Float32, Float64}) &&
            isa(func_args[2], Symbol) &&
            !in(string(func_args[2]::Symbol)[1], ('e', 'E', 'f', (func_args[1] == 0 && func_args[1] isa Integer ?
                                                                  # don't juxtapose 0 with b, o, x
                                                                  ('b', 'o', 'x') : ())...)))
            if func_prec <= prec
                show_enclosed_list(io, '(', func_args, "", ')', indent, func_prec, quote_level)
            else
                show_list(io, func_args, "", indent, func_prec, quote_level)
            end

        # unary operator (i.e. "!z")
        elseif isa(func,Symbol) && length(func_args) == 1 && func in uni_ops
            show_unquoted(io, func, indent, 0, quote_level)
            arg1 = func_args[1]
            if isa(arg1, Expr) || (isa(arg1, Symbol) && isoperator(arg1) && is_valid_identifier(arg1))
                show_enclosed_list(io, '(', func_args, ", ", ')', indent, func_prec)
            else
                show_unquoted(io, arg1, indent, func_prec, quote_level)
            end

        # binary operator (i.e. "x + y")
        elseif func_prec > 0 # is a binary operator
            func = func::Symbol    # operator_precedence returns func_prec == 0 for non-Symbol
            na = length(func_args)
            if (na == 2 || (na > 2 && func in (:+, :++, :*)) || (na == 3 && func === :(:))) &&
                    all(a -> !isa(a, Expr) || a.head !== :..., func_args)
                sep = func === :(:) ? "$func" : " $func "

                if func_prec <= prec
                    show_enclosed_list(io, '(', func_args, sep, ')', indent, func_prec, quote_level, true)
                else
                    show_list(io, func_args, sep, indent, func_prec, quote_level, true)
                end
            elseif na == 1
                # 1-argument call to normally-binary operator
                op, cl = expr_calls[head]
                print(io, "(")
                show_unquoted(io, func, indent, 0, quote_level)
                print(io, ")")
                show_enclosed_list(io, op, func_args, ", ", cl, indent, 0, quote_level)
            else
                show_call(io, head, func, func_args, indent, quote_level, true)
            end

        # normal function (i.e. "f(x,y)")
        else
            show_call(io, head, func, func_args, indent, quote_level, true)
        end

    # new expr
    elseif head === :new || head === :splatnew
        show_enclosed_list(io, "%$head(", args, ", ", ")", indent, 0, quote_level)

    # other call-like expressions ("A[1,2]", "T{X,Y}", "f.(X,Y)")
    elseif haskey(expr_calls, head) && nargs >= 1  # :ref/:curly/:calldecl/:(.)
        funcargslike = head === :(.) ? (args[2]::Expr).args : args[2:end]
        show_call(head === :ref ? IOContext(io, beginsym=>true) : io, head, args[1], funcargslike, indent, quote_level, head !== :curly)

    # comprehensions
    elseif head === :typed_comprehension && nargs == 2
        show_unquoted(io, args[1], indent, 0, quote_level)
        print(io, '[')
        show_generator(io, args[2], indent, quote_level)
        print(io, ']')

    elseif head === :comprehension && nargs == 1
        print(io, '[')
        show_generator(io, args[1], indent, quote_level)
        print(io, ']')

    elseif (head === :generator && nargs >= 2) || (head === :flatten && nargs == 1)
        print(io, '(')
        show_generator(io, ex, indent, quote_level)
        print(io, ')')

    elseif head === :filter && nargs == 2
        show_unquoted(io, args[2], indent, 0, quote_level)
        print(io, " if ")
        show_unquoted(io, args[1], indent, 0, quote_level)

    # comparison (i.e. "x < y < z")
    elseif head === :comparison && nargs >= 3 && (nargs&1==1)
        comp_prec = minimum(operator_precedence, args[2:2:end]; init=typemax(Int))
        if comp_prec <= prec
            show_enclosed_list(io, '(', args, " ", ')', indent, comp_prec, quote_level)
        else
            show_list(io, args, " ", indent, comp_prec, quote_level)
        end

    # function calls need to transform the function from :call to :calldecl
    # so that operators are printed correctly
    elseif head === :function && nargs==2 && is_expr(args[1], :call)
        show_block(IOContext(io, beginsym=>false), head, Expr(:calldecl, (args[1]::Expr).args...), args[2], indent, quote_level)
        print(io, "end")

    elseif (head === :function || head === :macro) && nargs == 1
        print(io, head, ' ')
        show_unquoted(IOContext(io, beginsym=>false), args[1])
        print(io, " end")

    elseif head === :do && nargs == 2
        iob = IOContext(io, beginsym=>false)
        show_unquoted(iob, args[1], indent, -1, quote_level)
        print(io, " do")
        do_args = (((args[2]::Expr).args[1])::Expr).args
        if !isempty(do_args)
            print(io, ' ')
            show_list(iob, do_args, ", ", 0, 0, quote_level)
        end
        for stmt in (((args[2]::Expr).args[2])::Expr).args
            print(io, '\n', " "^(indent + indent_width))
            show_unquoted(iob, stmt, indent + indent_width, -1, quote_level)
        end
        print(io, '\n', " "^indent)
        print(io, "end")

    # block with argument
    elseif head in (:for,:while,:function,:macro,:if,:elseif,:let) && nargs==2
        if head === :function && is_expr(args[1], :...)
            # fix printing of "function (x...) x end"
            block_args = Expr(:tuple, args[1])
        else
            block_args = args[1]
        end
        if is_expr(args[2], :block)
            show_block(IOContext(io, beginsym=>false), head, block_args, args[2], indent, quote_level)
        else
            show_block(IOContext(io, beginsym=>false), head, block_args, Expr(:block, args[2]), indent, quote_level)
        end
        print(io, "end")

    elseif (head === :if || head === :elseif) && nargs == 3
        iob = IOContext(io, beginsym=>false)
        show_block(iob, head, args[1], args[2], indent, quote_level)
        arg3 = args[3]
        if isa(arg3, Expr) && arg3.head === :elseif
            show_unquoted(iob, arg3::Expr, indent, prec, quote_level)
        else
            show_block(iob, "else", arg3, indent, quote_level)
            print(io, "end")
        end

    elseif head === :module && nargs==4 && isa(args[1],VersionNumber) && isa(args[2],Bool)
        # New 4-argument form: (version, baremodule_flag, name, body)
        show_block(IOContext(io, beginsym=>false), args[2] ? :module : :baremodule, args[3], args[4], indent, quote_level)
        print(io, "end")
    elseif head === :module && nargs==3 && isa(args[1],Bool)
        # Old 3-argument form: (baremodule_flag, name, body)
        show_block(IOContext(io, beginsym=>false), args[1] ? :module : :baremodule, args[2], args[3], indent, quote_level)
        print(io, "end")

    # type declaration
    elseif head === :struct && nargs==3
        show_block(IOContext(io, beginsym=>false), args[1] ? Symbol("mutable struct") : Symbol("struct"), args[2], args[3], indent, quote_level)
        print(io, "end")

    elseif head === :primitive && nargs == 2
        print(io, "primitive type ")
        show_list(io, args, ' ', indent, 0, quote_level)
        print(io, " end")

    elseif head === :abstract && nargs == 1
        print(io, "abstract type ")
        show_list(IOContext(io, beginsym=>false), args, ' ', indent, 0, quote_level)
        print(io, " end")

    # empty return (i.e. "function f() return end")
    elseif head === :return && nargs == 1 && args[1] === nothing
        print(io, head)

    # type annotation (i.e. "::Int")
    elseif head in uni_syms && nargs == 1
        print(io, head)
        show_unquoted(io, args[1], indent, 0, quote_level)

    # var-arg declaration or expansion
    # (i.e. "function f(L...) end" or "f(B...)")
    elseif head === :(...) && nargs == 1
        dotsprec = operator_precedence(:(:)) - 1
        parens = dotsprec <= prec
        parens && print(io, "(")
        show_unquoted(io, args[1], indent, dotsprec, quote_level)
        print(io, "...")
        parens && print(io, ")")

    elseif (nargs == 0 && head in (:break, :continue))
        print(io, head)

    elseif (nargs == 1 && head in (:return, :const)) ||
                          head in (:local,  :global)
        print(io, head, ' ')
        show_list(io, args, ", ", indent, 0, quote_level)

    elseif head in (:export, :public)
        print(io, head, ' ')
        show_list(io, mapany(allow_macroname, args), ", ", indent)

    elseif head === :macrocall && nargs >= 2
        # handle some special syntaxes
        # `a b c`
        if is_core_macro(args[1], :var"@cmd")
            print(io, "`", args[3], "`")
        # 11111111111111111111, 0xfffffffffffffffff, 1111...many digits...
        elseif is_core_macro(args[1], :var"@int128_str") ||
               is_core_macro(args[1], :var"@uint128_str") ||
               is_core_macro(args[1], :var"@big_str")
            print(io, args[3])
        # x"y" and x"y"z
        elseif isa(args[1], Symbol) && nargs >= 3 && isa(args[3], String) &&
               startswith(string(args[1]::Symbol), "@") &&
               endswith(string(args[1]::Symbol), "_str")
            s = string(args[1]::Symbol)
            print(io, s[2:prevind(s,end,4)], "\"")
            escape_raw_string(io, args[3])
            print(io, "\"")
            if nargs == 4
                print(io, args[4])
            end
        # general case
        else
            # first show the line number argument as a comment
            if isa(args[2], LineNumberNode) || is_expr(args[2], :line)
                a2 = args[2]
                a2 isa LineNumberNode ? print(io, a2, ' ') : print(io, a2::Expr, ' ')
            end
            # Use the functional syntax unless specifically designated with
            # prec=-1 and hide the line number argument from the argument list
            mname = allow_macroname(args[1])
            if prec >= 0
                show_call(io, :call, mname, args[3:end], indent, quote_level, false)
            else
                show_args = Vector{Any}(undef, nargs - 1)
                show_args[1] = mname
                show_args[2:end] = args[3:end]
                show_list(io, show_args, ' ', indent, 0, quote_level)
            end
        end

    elseif head === :macroname && nargs == 1
        arg1 = args[1]
        if arg1 isa Symbol
            show_sym(io, arg1, allow_macroname=true)
        elseif arg1 isa GlobalRef
            show_globalref(io, arg1, allow_macroname=true)
        elseif is_expr(arg1, :(.)) && length((arg1::Expr).args) == 2
            arg1 = arg1::Expr
            m = arg1.args[1]
            if m isa Symbol || m isa GlobalRef || is_expr(m, :(.), 2)
                show_unquoted(io, m)
            else
                print(io, "(")
                show_unquoted(io, m)
                print(io, ")")
            end
            print(io, '.')
            if is_expr(arg1.args[2], :quote)
                mname = (arg1.args[2]::Expr).args[1]
            else
                mname = (arg1.args[2]::QuoteNode).value
            end
            if mname isa Symbol
                show_sym(io, mname, allow_macroname=true)
            else
                show_unquoted(io, mname)
            end
        else
            show_unquoted(io, arg1)
        end

    elseif head === :line && 1 <= nargs <= 2
        show_linenumber(io, args...)

    elseif head === :try && 3 <= nargs <= 5
        iob = IOContext(io, beginsym=>false)
        show_block(iob, "try", args[1], indent, quote_level)
        if is_expr(args[3], :block)
            show_block(iob, "catch", args[2] === false ? Any[] : args[2], args[3]::Expr, indent, quote_level)
        end
        if nargs >= 5 && is_expr(args[5], :block)
            show_block(iob, "else", Any[], args[5]::Expr, indent, quote_level)
        end
        if nargs >= 4 && is_expr(args[4], :block)
            show_block(iob, "finally", Any[], args[4]::Expr, indent, quote_level)
        end
        print(io, "end")

    elseif head === :block
        # print as (...; ...; ...;) inside indexing expression
        if get(io, beginsym, false)
            print(io, '(')
            ind = indent + indent_width
            # A `;` with only comments before it would parse as a NamedTuple,
            # and a block needs at least one semicolon: `(x;)` `(;;)`
            seen_expr = printed_semi = false
            for (i, arg) in enumerate(ex.args)
                if i > 1
                    seen_expr && (print(io, ';'); printed_semi = true)
                    print(io, "\n", ' '^ind)
                end
                show_unquoted(io, arg, ind, -1, quote_level)
                seen_expr |= !(arg isa LineNumberNode)
            end
            print(io, printed_semi ? ")" : seen_expr ? ";)" : ";;)")
        else
            show_block(io, "begin", ex, indent, quote_level)
            print(io, "end")
        end

    elseif head === :quote && nargs == 1 && isa(args[1], Symbol)
        show_unquoted_quote_expr(IOContext(io, beginsym=>false), args[1]::Symbol, indent, quote_level+1)
    elseif head === :quote && !(get(io, :unquote_fallback, true)::Bool)
        if nargs == 1 && is_expr(args[1], :block)
            show_block(IOContext(io, beginsym=>false), "quote", Expr(:quote, (args[1]::Expr).args...), indent,
                       quote_level+1)
            print(io, "end")
        elseif nargs == 1
            print(io, ":(")
            show_unquoted(IOContext(io, beginsym=>false), args[1], indent+2, 0, quote_level+1)
            print(io, ")")
        else
            show_block(IOContext(io, beginsym=>false), "quote", ex, indent, quote_level+1)
            print(io, "end")
        end

    elseif head === :gotoifnot && nargs == 2 && isa(args[2], Int)
        print(io, "unless ")
        show_unquoted(io, args[1], indent, 0, quote_level)
        print(io, " goto %")
        print(io, args[2]::Int)

    elseif head === :string && nargs == 1 && isa(args[1], AbstractString)
        show(io, args[1])

    elseif head === :null
        print(io, "nothing")

    elseif head === :string
        print(io, '"')
        for x in args
            if !isa(x,AbstractString)
                print(io, "\$(")
                if isa(x,Symbol) && !(x in quoted_syms)
                    show_sym(io, x)
                else
                    show_unquoted(io, x, 0, 0, quote_level)
                end
                print(io, ")")
            else
                escape_string(io, String(x)::String, "\"\$")
            end
        end
        print(io, '"')

    elseif (head === :& || head === :$) && nargs == 1
        if head === :$
            quote_level -= 1
        end
        if head === :$ && get(io, :unquote_fallback, true)
            unhandled = true
        else
            print(io, head)
            a1 = args[1]
            parens = (isa(a1,Expr) && !in(a1.head, (:tuple, :$, :vect, :braces))) ||
                     (isa(a1,Symbol) && isoperator(a1))
            parens && print(io, "(")
            show_unquoted(io, a1, 0, 0, quote_level)
            parens && print(io, ")")
        end

    # `where` syntax
    elseif head === :where && nargs > 1
        parens = 1 <= prec
        parens && print(io, "(")
        show_unquoted(io, args[1], indent, operator_precedence(:(::)), quote_level)
        print(io, " where ")
        if nargs == 2
            show_unquoted(io, args[2], indent, 1, quote_level)
        else
            print(io, "{")
            show_list(io, args[2:end], ", ", indent, 0, quote_level)
            print(io, "}")
        end
        parens && print(io, ")")

    elseif (head === :import || head === :using) &&
           ((nargs == 1 && (valid_import_path(args[1]) ||
                           (is_expr(args[1], :(:)) &&
                            length((args[1]::Expr).args) > 1 &&
                            all(valid_import_path, (args[1]::Expr).args)))) ||
             all(valid_import_path, args))
        print(io, head)
        print(io, ' ')
        first = true
        for a in args
            if !first
                print(io, ", ")
            end
            first = false
            show_import_path(io, a, quote_level)
        end
    elseif head === :as && nargs == 2 && valid_import_path(args[1], false)
        show_import_path(io, args[1], quote_level)
        print(io, " as ")
        show_unquoted(io, args[2], indent, 0, quote_level)
    elseif head === :meta && nargs >= 2 && args[1] === :push_loc
        print(io, "# meta: location ", join(args[2:end], " "))
    elseif head === :meta && nargs == 1 && args[1] === :pop_loc
        print(io, "# meta: pop location")
    elseif head === :meta && nargs == 2 && args[1] === :pop_loc
        print(io, "# meta: pop locations ($(args[2]::Int))")
    # print anything else as "Expr(head, args...)"
    elseif head === :toplevel
        # Reset SOURCE_SLOTNAMES. Raw SlotNumbers are not valid in Expr(:toplevel), but
        # we want to show bad ASTs reasonably to make errors understandable.
        lambda_io = IOContext(io, :SOURCE_SLOTNAMES => false)
        show_unquoted_expr_fallback(lambda_io, ex)
    else
        unhandled = true
    end
    if unhandled
        show_unquoted_expr_fallback(io, ex)
    end
    nothing
end

```
-/
-- `ex` is the original `Expr`; `head`, `args`, `nargs` and `quote_level` are the mutable locals of
-- the Julia method.
def show_unquoted_Expr {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (head₀ : Sym) (args₀ : List (Value L)) (indent prec quote_level₀ : JInt64) : m Unit := do
  let ex : Value L := .expr head₀ args₀
  let unhandled ← show_unquoted_Expr_1 p a c io ex head₀ args₀ indent prec quote_level₀
  if unhandled then
    show_unquoted_expr_fallback p a c io head₀ args₀

partial_fixpoint

-- The `:macroname` branch of `show_unquoted(io, ex::Expr, …)`, on `arg1 = args[1]`.
def show_macroname {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) : Value L → m Unit
  | .symbol s => show_sym p c io s true
  | .globalRef mod name => show_globalref p a c io mod name true
  | .expr h xs => do
    match xs with
    | [mm, a2] =>
      if h == "." then
        if (match mm with | .symbol _ => true | .globalRef .. => true | _ => is_expr_n mm "." (i64 2)) then
          show_unquoted_2 p a c io mm
        else
          printStr p io "("
          show_unquoted_2 p a c io mm
          printStr p io ")"
        printStr p io "."
        let mname ← macroname_of a2
        show_macroname_sym p a c io mname
      else
        show_unquoted_2 p a c io (.expr h xs)
    | _ => show_unquoted_2 p a c io (.expr h xs)
  | arg1 => show_unquoted_2 p a c io arg1
partial_fixpoint

-- `show_sym(io, mname, allow_macroname=true)` for a `Symbol`, otherwise `show_unquoted(io, mname)`.
def show_macroname_sym {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) : Value L → m Unit
  | .symbol s => show_sym p c io s true
  | mname => show_unquoted_2 p a c io mname
partial_fixpoint

-- Branches 1/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_1 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  -- dot (i.e. "x.y"), but not compact broadcast exps
  if head == "." && (nargs != 2 || !(match args with | [_, a2] => is_expr a2 "tuple" | _ => false)) then
    -- standalone .op
    let standaloneOp : Option Sym ← pure <| match args with
      | [.symbol s] => if c.isoperator s then some s else none
      | _ => none
    match standaloneOp with
    | some s => locked p io (do printStr p io "(."; print_Symbol p io s; printStr p io ")")
    | none =>
      if nargs == 2 && (match args with | [_, a2] => is_quoted a2 | _ => false) then
        let item ← argAt' args 1
        -- field
        let field ← unquoted (← argAt' args 2)
        let parens := !is_quoted item && !(match item with | .symbol s => c.isidentifier s | _ => false) &&
          !is_expr item "."
        if parens then printStr p io "("
        show_unquoted_5 p a c io item indent (i64 0) quote_level
        if parens then printStr p io ")"
        -- .
        printStr p io "."
        -- item
        let (parens, quoted) := match field with
          | .symbol f => let parens := symIn f quoted_syms; (parens, parens || c.isoperator f)
          | _ => (true, true)
        if quoted then printStr p io ":"
        if parens then printStr p io "("
        show_unquoted_5 p a c io field indent (i64 0) quote_level
        if parens then printStr p io ")"
      else
        unhandled := true
  -- infix (i.e. "x <: y" or "x = y")
  else if symIn head expr_infix_any && nargs == 2 then
    let func_prec := c.operator_precedence head
    let head_ : Bytes := if symIn head expr_infix_wide then lit (" " ++ head ++ " ") else lit head
    if head == "->" && (match args with | a1 :: _ => is_expr a1 "..." | [] => false) then
      args := match args with
        | [a1, a2] => [.expr "tuple" [a1], a2]
        | _ => args
    if func_prec.val ≤ prec.val then
      show_enclosed_list p a c io "(" args head_ ")" indent func_prec quote_level true
    else
      show_list p a c io args head_ indent func_prec quote_level true
  else if head == "tuple" then
    printStr p io "("
    match args with
    | .expr "parameters" pargs :: rest =>
      show_list p a c io rest (lit ", ") indent (i64 0) quote_level
      if nargs == 2 then printStr p io ","
      printStr p io ";"
      if !pargs.isEmpty then
        printStr p io " "
      show_list p a c io pargs (lit ", ") indent (i64 0) quote_level false true
    | _ =>
      show_list p a c io args (lit ", ") indent (i64 0) quote_level
      if nargs == 1 then printStr p io ","
    printStr p io ")"
  else
    unhandled ← show_unquoted_Expr_2 p a c io ex head₀ args₀ indent prec quote_level₀
  return unhandled
partial_fixpoint

-- Branches 2/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_2 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  -- list-like forms, e.g. "[1, 2, 3]"
  if (expr_parens.lookup head).isSome ||
      head == "typed_vcat" || head == "typed_hcat" || head == "typed_ncat" then
    -- print the type and defer to the untyped case
    if head == "typed_vcat" || head == "typed_hcat" || head == "typed_ncat" then
      show_unquoted_5 p a c io (← argAt' args 1) indent prec quote_level
      if head == "typed_vcat" then
        head := "vcat"
      else if head == "typed_hcat" then
        head := "hcat"
      else
        head := "ncat"
      args := args.drop 1
      nargs := nargs - 1
    let (op, cl) ← dictGet expr_parens head
    let mut sep : Bytes := lit ", "
    if head == "vcat" || head == "bracescat" then
      sep := lit "; "
    else if head == "hcat" || head == "row" then
      sep := lit " "
    else if head == "ncat" || head == "nrow" then
      let k ← argInt c (← argAt' args 1)
      sep := (← repeatBytes (lit ";") k) ++ lit " "
      args := args.drop 1
      nargs := nargs - 1
    else
      sep := lit ", "
    if head != "row" && head != "nrow" then printStr p io op
    show_list p a c io args sep indent (i64 0) quote_level
    if nargs ≤ 1 && (head == "vcat" || head == "ncat") then
      printBytes p io sep.dropLast
    if head != "row" && head != "nrow" then printStr p io cl
  -- transpose
  else if (head == "'" && nargs == 1) || (
      -- ' with unicode suffix is a call expression
      head == "call" && nargs == 2 && (match args with
        | .symbol f :: _ => c.ispostfixoperator f && f != "'"
        | _ => false)) then
    let (op, arg1) ← if head == "'" then do pure (head, ← argAt' args 1) else
      match args with
      | [.symbol f, x] => pure (f, x)
      | _ => throwShow .typeError
    if (match arg1 with | .expr .. => true | .symbol s => c.isoperator s | _ => false) then
      show_enclosed_list p a c io "(" [arg1] (lit ", ") ")" indent (i64 0)
    else
      show_unquoted_5 p a c io arg1 indent (i64 0) quote_level
    print_Symbol p io op
  else
    unhandled ← show_unquoted_Expr_3 p a c io ex head₀ args₀ indent prec quote_level₀
  return unhandled
partial_fixpoint

-- Branches 3/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_3 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  -- function call
  if head == "call" && nargs ≥ 1 then
    let func₀ ← argAt' args 1
    let fname : Value L ← pure <| match func₀ with
      | .globalRef _ name => .symbol name
      | f => f
    let func_prec := operator_precedence_any c fname
    let func ← pure <| if func_prec.val > 0 || (match fname with | .symbol s => symIn s uni_ops | _ => false) then fname
      else func₀
    let func_args ← pure (args.drop 1)
    -- :kw exprs are only parsed inside parenthesized calls
    if func_args.any (fun x => is_expr x "kw") ||
        (match func_args with | x :: _ => is_expr x "parameters" | [] => false) then
      show_call p a c io head func func_args indent quote_level true
    else
      -- scalar multiplication (i.e. "100x"); `string(func_args[2])[1]` throws `BoundsError` for the
      -- empty symbol
      let scalar ← match func, func_args with
        | .symbol "*", [.leaf x, .symbol s] =>
          match c.scalarCoef x with
          | some zeroInteger =>
            match s.toList with
            | ch :: _ => pure !(ch == 'e' || ch == 'E' || ch == 'f' ||
                -- don't juxtapose 0 with b, o, x
                (zeroInteger && (ch == 'b' || ch == 'o' || ch == 'x')))
            | [] => throwShow (.jl .boundsError)
          | none => pure false
        | _, _ => pure false
      if scalar then
        if func_prec.val ≤ prec.val then
          show_enclosed_list p a c io "(" func_args [] ")" indent func_prec quote_level
        else
          show_list p a c io func_args [] indent func_prec quote_level
      -- unary operator (i.e. "!z")
      else if (match func with | .symbol f => symIn f uni_ops | _ => false) && func_args.length == 1 then
        show_unquoted_5 p a c io func indent (i64 0) quote_level
        let arg1 ← argAt' func_args 1
        if (match arg1 with
            | .expr .. => true
            | .symbol s => c.isoperator s && c.is_valid_identifier s
            | _ => false) then
          show_enclosed_list p a c io "(" func_args (lit ", ") ")" indent func_prec
        else
          show_unquoted_5 p a c io arg1 indent func_prec quote_level
      -- binary operator (i.e. "x + y")
      else if func_prec.val > 0 then -- is a binary operator
        let f ← match func with
          | .symbol f => pure f
          | _ => throwShow .typeError
        let na := func_args.length
        if (na == 2 || (na > 2 && (f == "+" || f == "++" || f == "*")) || (na == 3 && f == ":")) &&
            func_args.all (fun x => match x with | .expr h _ => h != "..." | _ => true) then
          let sep := if f == ":" then lit f else lit (" " ++ f ++ " ")
          if func_prec.val ≤ prec.val then
            show_enclosed_list p a c io "(" func_args sep ")" indent func_prec quote_level true
          else
            show_list p a c io func_args sep indent func_prec quote_level true
        else if na == 1 then
          -- 1-argument call to normally-binary operator
          let (op, cl) ← dictGet expr_calls head
          printStr p io "("
          show_unquoted_5 p a c io func indent (i64 0) quote_level
          printStr p io ")"
          show_enclosed_list p a c io op func_args (lit ", ") cl indent (i64 0) quote_level
        else
          show_call p a c io head func func_args indent quote_level true
      -- normal function (i.e. "f(x,y)")
      else
        show_call p a c io head func func_args indent quote_level true
  else
    unhandled ← show_unquoted_Expr_4 p a c io ex head₀ args₀ indent prec quote_level₀
  return unhandled
partial_fixpoint

-- Branches 4/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_4 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  -- new expr
  if head == "new" || head == "splatnew" then
    show_enclosed_list p a c io ("%" ++ head ++ "(") args (lit ", ") ")" indent (i64 0) quote_level
  -- other call-like expressions ("A[1,2]", "T{X,Y}", "f.(X,Y)")
  else if (expr_calls.lookup head).isSome && nargs ≥ 1 then -- :ref/:curly/:calldecl/:(.)
    let funcargslike ← if head == "." then do
        let (_, a2args) ← asExpr' (← argAt' args 2)
        pure a2args
      else pure (args.drop 1)
    let io' ← if head == "ref" then withBool p a io c.beginsym true else pure io
    show_call p a c io' head (← argAt' args 1) funcargslike indent quote_level (head != "curly")
  -- comprehensions
  else if head == "typed_comprehension" && nargs == 2 then
    show_unquoted_5 p a c io (← argAt' args 1) indent (i64 0) quote_level
    printStr p io "["
    show_generator_v p a c io (← argAt' args 2) indent quote_level
    printStr p io "]"
  else if head == "comprehension" && nargs == 1 then
    printStr p io "["
    show_generator_v p a c io (← argAt' args 1) indent quote_level
    printStr p io "]"
  else if (head == "generator" && nargs ≥ 2) || (head == "flatten" && nargs == 1) then
    printStr p io "("
    show_generator p a c io head args indent quote_level
    printStr p io ")"
  else if head == "filter" && nargs == 2 then
    show_unquoted_5 p a c io (← argAt' args 2) indent (i64 0) quote_level
    printStr p io " if "
    show_unquoted_5 p a c io (← argAt' args 1) indent (i64 0) quote_level
  -- comparison (i.e. "x < y < z")
  else if head == "comparison" && nargs ≥ 3 && nargs % 2 == 1 then
    let comp_prec := comp_prec_min c args
    if comp_prec.val ≤ prec.val then
      show_enclosed_list p a c io "(" args (lit " ") ")" indent comp_prec quote_level
    else
      show_list p a c io args (lit " ") indent comp_prec quote_level
  -- function calls need to transform the function from :call to :calldecl
  -- so that operators are printed correctly
  else if head == "function" && nargs == 2 && (match args with | a1 :: _ => is_expr a1 "call" | [] => false) then
    let ctx ← withBool p a io c.beginsym false
    let (_, cargs) ← asExpr' (← argAt' args 1)
    show_block p a c ctx (.sym head) (.arg (.expr "calldecl" cargs)) (← argAt' args 2) indent quote_level
    printStr p io "end"
  else if (head == "function" || head == "macro") && nargs == 1 then
    locked p io (do print_Symbol p io head; printStr p io " ")
    let ctx ← withBool p a io c.beginsym false
    show_unquoted_2 p a c ctx (← argAt' args 1)
    printStr p io " end"
  else if head == "do" && nargs == 2 then
    let iob ← withBool p a io c.beginsym false
    show_unquoted_5 p a c iob (← argAt' args 1) indent (i64 (-1)) quote_level
    printStr p io " do"
    let (_, a2args) ← asExpr' (← argAt' args 2)
    let (_, do_args) ← asExpr' (← argAt' a2args 1)
    if !do_args.isEmpty then
      printStr p io " "
      show_list p a c iob do_args (lit ", ") (i64 0) (i64 0) quote_level
    let (_, stmts) ← asExpr' (← argAt' a2args 2)
    show_do_stmts p a c io iob indent quote_level stmts
    let sp ← spacesRep indent
    locked p io (do printStr p io "\n"; printBytes p io sp)
    printStr p io "end"
  else
    unhandled ← show_unquoted_Expr_5 p a c io ex head₀ args₀ indent prec quote_level₀
  return unhandled
partial_fixpoint

-- Branches 5/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_5 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  -- block with argument
  if ["for", "while", "function", "macro", "if", "elseif", "let"].contains head && nargs == 2 then
    let a1 ← argAt' args 1
    let block_args : Value L := if head == "function" && is_expr a1 "..." then
        -- fix printing of "function (x...) x end"
        .expr "tuple" [a1]
      else a1
    let a2 ← argAt' args 2
    if is_expr a2 "block" then
      let ctx ← withBool p a io c.beginsym false
      show_block p a c ctx (.sym head) (.arg block_args) a2 indent quote_level
    else
      let ctx ← withBool p a io c.beginsym false
      show_block p a c ctx (.sym head) (.arg block_args) (.expr "block" [a2]) indent quote_level
    printStr p io "end"
  else if (head == "if" || head == "elseif") && nargs == 3 then
    let iob ← withBool p a io c.beginsym false
    show_block p a c iob (.sym head) (.arg (← argAt' args 1)) (← argAt' args 2) indent quote_level
    let arg3 ← argAt' args 3
    match arg3 with
    | .expr "elseif" a3 => show_unquoted_Expr p a c iob "elseif" a3 indent prec quote_level
    | _ =>
      show_block_5 p a c iob (.str "else") arg3 indent quote_level
      printStr p io "end"
  else if head == "module" && nargs == 4 && (module4 c args).isSome then
    -- New 4-argument form: (version, baremodule_flag, name, body)
    let ctx ← withBool p a io c.beginsym false
    match module4 c args with
    | some (flag, name, body) =>
      show_block p a c ctx (.sym (if flag then "module" else "baremodule")) (.arg name) body indent quote_level
    | none => pure ()
    printStr p io "end"
  else if head == "module" && nargs == 3 &&
      (match args with | .leaf b :: _ => (c.lo.asBool b).isSome | _ => false) then
    -- Old 3-argument form: (baremodule_flag, name, body)
    let ctx ← withBool p a io c.beginsym false
    let flag ← exprArgBool c (← argAt' args 1)
    show_block p a c ctx (.sym (if flag then "module" else "baremodule")) (.arg (← argAt' args 2))
      (← argAt' args 3) indent quote_level
    printStr p io "end"
  -- type declaration
  else if head == "struct" && nargs == 3 then
    let ctx ← withBool p a io c.beginsym false
    let mut_ ← exprArgBool c (← argAt' args 1)
    show_block p a c ctx (.sym (if mut_ then "mutable struct" else "struct")) (.arg (← argAt' args 2))
      (← argAt' args 3) indent quote_level
    printStr p io "end"
  else if head == "primitive" && nargs == 2 then
    printStr p io "primitive type "
    show_list p a c io args (lit " ") indent (i64 0) quote_level
    printStr p io " end"
  else if head == "abstract" && nargs == 1 then
    printStr p io "abstract type "
    let ctx ← withBool p a io c.beginsym false
    show_list p a c ctx args (lit " ") indent (i64 0) quote_level
    printStr p io " end"
  -- empty return (i.e. "function f() return end")
  else if head == "return" && nargs == 1 && (match args with | [x] => isNothing c.lo x | _ => false) then
    print_Symbol p io head
  -- type annotation (i.e. "::Int")
  else if symIn head uni_syms && nargs == 1 then
    print_Symbol p io head
    show_unquoted_5 p a c io (← argAt' args 1) indent (i64 0) quote_level
  else
    unhandled ← show_unquoted_Expr_6 p a c io ex head₀ args₀ indent prec quote_level₀
  return unhandled
partial_fixpoint

-- Branches 6/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_6 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  -- var-arg declaration or expansion
  -- (i.e. "function f(L...) end" or "f(B...)")
  if head == "..." && nargs == 1 then
    let dotsprec := i64 ((c.operator_precedence ":").val - 1)
    let parens := dotsprec.val ≤ prec.val
    if parens then printStr p io "("
    show_unquoted_5 p a c io (← argAt' args 1) indent dotsprec quote_level
    printStr p io "..."
    if parens then printStr p io ")"
  else if nargs == 0 && (head == "break" || head == "continue") then
    print_Symbol p io head
  else if (nargs == 1 && (head == "return" || head == "const")) || head == "local" || head == "global" then
    locked p io (do print_Symbol p io head; printStr p io " ")
    show_list p a c io args (lit ", ") indent (i64 0) quote_level
  else if head == "export" || head == "public" then
    locked p io (do print_Symbol p io head; printStr p io " ")
    show_list p a c io (← args.mapM allow_macroname) (lit ", ") indent
  else if head == "macrocall" && nargs ≥ 2 then
    let a1 ← argAt' args 1
    -- handle some special syntaxes
    -- `a b c`
    if is_core_macro c.lo c.core a1 "@cmd" then
      let a3 ← argAt' args 3
      locked p io (do printStr p io "`"; printValue p a c io a3; printStr p io "`")
    -- 11111111111111111111, 0xfffffffffffffffff, 1111...many digits...
    else if is_core_macro c.lo c.core a1 "@int128_str" ||
        is_core_macro c.lo c.core a1 "@uint128_str" ||
        is_core_macro c.lo c.core a1 "@big_str" then
      printValue p a c io (← argAt' args 3)
    -- x"y" and x"y"z
    else if (strMacro c args).isSome then
      match strMacro c args with
      | some (s, str) =>
        -- `s[2:prevind(s,end,4)]`: `s` without the leading `@` and the trailing `_str`
        let inner := String.ofList ((s.toList.drop 1).take (s.length - 5))
        locked p io (do printStr p io inner; printStr p io "\"")
        c.escape_raw_string_io io str
        printStr p io "\""
        if nargs == 4 then
          printValue p a c io (← argAt' args 4)
      | none => pure ()
    -- general case
    else
      -- first show the line number argument as a comment
      let a2 ← argAt' args 2
      if (match a2 with | .lineNumberNode .. => true | _ => false) || is_expr a2 "line" then
        locked p io (do printValue p a c io a2; printStr p io " ")
      -- Use the functional syntax unless specifically designated with
      -- prec=-1 and hide the line number argument from the argument list
      let mname ← allow_macroname a1
      if prec.val ≥ 0 then
        show_call p a c io "call" mname (args.drop 2) indent quote_level false
      else
        show_list p a c io (mname :: args.drop 2) (lit " ") indent (i64 0) quote_level
  else
    unhandled ← show_unquoted_Expr_7 p a c io ex head₀ args₀ indent prec quote_level₀
  return unhandled
partial_fixpoint

-- Branches 7/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_7 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  if head == "macroname" && nargs == 1 then
    show_macroname p a c io (← argAt' args 1)
  else if head == "line" && 1 ≤ nargs && nargs ≤ 2 then
    match args with
    | [line] => show_linenumber p a c io (.val line) none
    | [line, file] => show_linenumber p a c io (.val line) (some file)
    | _ => pure ()
  else if head == "try" && 3 ≤ nargs && nargs ≤ 5 then
    let iob ← withBool p a io c.beginsym false
    show_block_5 p a c iob (.str "try") (← argAt' args 1) indent quote_level
    let a3 ← argAt' args 3
    if is_expr a3 "block" then
      let a2 ← argAt' args 2
      show_block p a c iob (.str "catch") (if isFalse c.lo a2 then .vec [] else .arg a2) a3 indent quote_level
    if nargs ≥ 5 then
      let a5 ← argAt' args 5
      if is_expr a5 "block" then
        show_block p a c iob (.str "else") (.vec []) a5 indent quote_level
    if nargs ≥ 4 then
      let a4 ← argAt' args 4
      if is_expr a4 "block" then
        show_block p a c iob (.str "finally") (.vec []) a4 indent quote_level
    printStr p io "end"
  else if head == "block" then
    -- print as (...; ...; ...;) inside indexing expression
    if ← assertBool a (getIO p io c.beginsym false) then
      printStr p io "("
      let ind := i64 (indent.val + indent_width.val)
      -- A `;` with only comments before it would parse as a NamedTuple,
      -- and a block needs at least one semicolon: `(x;)` `(;;)`
      let (seen_expr, printed_semi) ← show_block_semis p a c io ind quote_level true false false args
      printStr p io (if printed_semi then ")" else if seen_expr then ";)" else ";;)")
    else
      show_block_5 p a c io (.str "begin") ex indent quote_level
      printStr p io "end"
  else if head == "quote" && nargs == 1 && (match args with | [.symbol _] => true | _ => false) then
    let ctx ← withBool p a io c.beginsym false
    show_unquoted_quote_expr p a c ctx (← argAt' args 1) indent (i64 (quote_level.val + 1))
  else
    unhandled ← show_unquoted_Expr_8 p a c io ex head₀ args₀ indent prec quote_level₀
  return unhandled
partial_fixpoint

-- Branches 8/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_8 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  -- `!(get(io, :unquote_fallback, true)::Bool)`: a non-`Bool` value takes the branch and fails the
  -- assertion at its start
  if head == "quote" && (match getBoolPure a (getIO p io "unquote_fallback" true) with
      | some b => !b
      | none => true) then
    let _ ← assertBool a (getIO p io "unquote_fallback" true)
    if nargs == 1 && (match args with | [a1] => is_expr a1 "block" | _ => false) then
      let ctx ← withBool p a io c.beginsym false
      let (_, bargs) ← asExpr' (← argAt' args 1)
      show_block_5 p a c ctx (.str "quote") (.expr "quote" bargs) indent (i64 (quote_level.val + 1))
      printStr p io "end"
    else if nargs == 1 then
      printStr p io ":("
      let ctx ← withBool p a io c.beginsym false
      show_unquoted_5 p a c ctx (← argAt' args 1) (i64 (indent.val + 2)) (i64 0) (i64 (quote_level.val + 1))
      printStr p io ")"
    else
      let ctx ← withBool p a io c.beginsym false
      show_block_5 p a c ctx (.str "quote") ex indent (i64 (quote_level.val + 1))
      printStr p io "end"
  else if head == "gotoifnot" && nargs == 2 &&
      (match args with | [_, .leaf x] => (c.asInt x).isSome | _ => false) then
    printStr p io "unless "
    show_unquoted_5 p a c io (← argAt' args 1) indent (i64 0) quote_level
    printStr p io " goto %"
    printInt p c io (← argInt c (← argAt' args 2))
  else if head == "string" && nargs == 1 &&
      (match args with | [.leaf x] => (c.asAbstractString x).isSome | _ => false) then
    showValue p a c io (← argAt' args 1)
  else if head == "null" then
    printStr p io "nothing"
  else if head == "string" then
    printStr p io "\""
    show_string_parts p a c io quote_level args
    printStr p io "\""
  else if (head == "&" || head == "$") && nargs == 1 then
    if head == "$" then
      quote_level := i64 (quote_level.val - 1)
    let fallback ← if head == "$" then assertBool a (getIO p io "unquote_fallback" true) else pure false
    if fallback then
      unhandled := true
    else
      print_Symbol p io head
      let a1 ← argAt' args 1
      let parens := match a1 with
        | .expr h _ => !(["tuple", "$", "vect", "braces"].contains h)
        | .symbol s => c.isoperator s
        | _ => false
      if parens then printStr p io "("
      show_unquoted_5 p a c io a1 (i64 0) (i64 0) quote_level
      if parens then printStr p io ")"
  -- `where` syntax
  else if head == "where" && nargs > 1 then
    let parens := 1 ≤ prec.val
    if parens then printStr p io "("
    show_unquoted_5 p a c io (← argAt' args 1) indent (c.operator_precedence "::") quote_level
    printStr p io " where "
    if nargs == 2 then
      show_unquoted_5 p a c io (← argAt' args 2) indent (i64 1) quote_level
    else
      printStr p io "{"
      show_list p a c io (args.drop 1) (lit ", ") indent (i64 0) quote_level
      printStr p io "}"
    if parens then printStr p io ")"
  else
    unhandled ← show_unquoted_Expr_9 p a c io ex head₀ args₀ indent prec quote_level₀
  return unhandled
partial_fixpoint

-- Branches 9/9 of the `if` chain of `show_unquoted(io, ex::Expr, …)`; returns `unhandled`.
def show_unquoted_Expr_9 {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty)
    (c : AstOps m Io V L) (io : JIO Io V) (ex : Value L) (head₀ : Sym) (args₀ : List (Value L))
    (indent prec quote_level₀ : JInt64) : m Bool := do
  -- (`← pure` binds the locals as values the monotonicity proof can case-split on)
  let mut head ← pure head₀
  let mut args ← pure args₀
  let mut nargs ← pure args₀.length
  let mut quote_level ← pure quote_level₀
  let mut unhandled ← pure false
  if (head == "import" || head == "using") &&
      ((nargs == 1 && (match args with
          | [a1] => valid_import_path a1 ||
            (is_expr a1 ":" && (match a1 with
              | .expr _ xs => xs.length > 1 && xs.all (fun x => valid_import_path x)
              | _ => false))
          | _ => false)) ||
        args.all (fun x => valid_import_path x)) then
    print_Symbol p io head
    printStr p io " "
    -- the `for a in args` loop: `", "` before every path but the first
    show_import_path_rest p a c io quote_level true args
  else if head == "as" && nargs == 2 && (match args with | [a1, _] => valid_import_path a1 false | _ => false) then
    show_import_path p a c io (← argAt' args 1) quote_level
    printStr p io " as "
    show_unquoted_5 p a c io (← argAt' args 2) indent (i64 0) quote_level
  else if head == "meta" && nargs ≥ 2 && (match args with | .symbol "push_loc" :: _ => true | _ => false) then
    -- `join(args[2:end], " ")` is `sprint(join, args[2:end], " ")`: a fresh `IOBuffer`
    let buf ← c.newBuffer
    join_values p a c (.plain buf) true (args.drop 1)
    let str ← c.takestring buf
    locked p io (do printStr p io "# meta: location "; printBytes p io str)
  else if head == "meta" && nargs == 1 && (match args with | [.symbol "pop_loc"] => true | _ => false) then
    printStr p io "# meta: pop location"
  else if head == "meta" && nargs == 2 && (match args with | [.symbol "pop_loc", _] => true | _ => false) then
    let n ← c.stringInt (← argInt c (← argAt' args 2))
    printBytes p io (lit "# meta: pop locations (" ++ n ++ lit ")")
  -- print anything else as "Expr(head, args...)"
  else if head == "toplevel" then
    -- Reset SOURCE_SLOTNAMES. Raw SlotNumbers are not valid in Expr(:toplevel), but
    -- we want to show bad ASTs reasonably to make errors understandable.
    let lambda_io ← withBool p a io "SOURCE_SLOTNAMES" false
    show_unquoted_expr_fallback p a c lambda_io head₀ args₀
  else
    unhandled := true
  return unhandled
partial_fixpoint

-- `show_generator(io, ex, …)` of an argument; it has only an `Expr` method.
def show_generator_v {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ex : Value L) (indent quote_level : JInt64) : m Unit :=
  match ex with
  | .expr h xs => show_generator p a c io h xs indent quote_level
  | _ => throwShow (.jl (.methodError "show_generator"))
partial_fixpoint

-- The `for stmt in …` loop of the `:do` branch.
def show_do_stmts {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io iob : JIO Io V)
    (indent quote_level : JInt64) : List (Value L) → m Unit
  | [] => pure ()
  | stmt :: rest => do
    let sp ← spacesRep (i64 (indent.val + indent_width.val))
    locked p io (do printStr p io "\n"; printBytes p io sp)
    show_unquoted_5 p a c iob stmt (i64 (indent.val + indent_width.val)) (i64 (-1)) quote_level
    show_do_stmts p a c io iob indent quote_level rest
partial_fixpoint

-- The `for (i, arg) in enumerate(ex.args)` loop of the `:block` branch; returns
-- `(seen_expr, printed_semi)`.
def show_block_semis {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (ind quote_level : JInt64) (first seen_expr printed_semi : Bool) : List (Value L) → m (Bool × Bool)
  | [] => pure (seen_expr, printed_semi)
  | arg :: rest => do
    let mut printed_semi := printed_semi
    if !first then
      if seen_expr then
        printStr p io ";"
        printed_semi := true
      let sp ← spacesRep ind
      locked p io (do printStr p io "\n"; printBytes p io sp)
    show_unquoted_5 p a c io arg ind (i64 (-1)) quote_level
    let seen_expr := seen_expr || !(match arg with | .lineNumberNode .. => true | _ => false)
    show_block_semis p a c io ind quote_level false seen_expr printed_semi rest
partial_fixpoint

-- The `for x in args` loop of the `:string` branch.
def show_string_parts {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (quote_level : JInt64) : List (Value L) → m Unit
  | [] => pure ()
  | x :: xs => do
    match (match x with | .leaf v => c.asAbstractString v | _ => none) with
    | some s => c.escape_string_io io s (lit "\"$")
    | none =>
      printStr p io "$("
      match x with
      | .symbol s =>
        if !symIn s quoted_syms then show_sym p c io s false
        else show_unquoted_5 p a c io x (i64 0) (i64 0) quote_level
      | _ => show_unquoted_5 p a c io x (i64 0) (i64 0) quote_level
      printStr p io ")"
    show_string_parts p a c io quote_level xs
partial_fixpoint

-- `join(io, xs, " ")` (`base/strings/io.jl`): `print(io, x)` of each element, `" "` between them.
def join_values {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (first : Bool) : List (Value L) → m Unit
  | [] => pure ()
  | x :: xs => do
    if !first then printStr p io " "
    printValue p a c io x
    join_values p a c io false xs
partial_fixpoint

/--
Julia source: base/show.jl:2931-2932 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_unquoted(io::IO, val::Argument, indent::Int, prec::Int) = show_unquoted(io, Core.SlotNumber(val.n), indent, prec)

```
-/
def show_unquoted_Argument {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (n indent prec : JInt64) : m Unit :=
  show_unquoted_4 p a c io (.slotNumber n) indent prec
partial_fixpoint

/--
Julia source: base/show.jl:2933-2933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_unquoted(io::IO, stmt::PhiNode, indent::Int, ::Int) = show_unquoted_phinode(io, stmt, indent, "%")
```
-/
def show_unquoted_PhiNode {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (edges : List (JInt .i32)) (values : List (Option (Value L))) (indent : JInt64) : m Unit :=
  show_unquoted_phinode p a c io edges values indent "%"
partial_fixpoint

/--
Julia source: base/show.jl:2934-2948 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted_phinode(io::IO, stmt::PhiNode, indent::Int, prefix::String)
    args = String[let
        e = stmt.edges[i]
        v = !isassigned(stmt.values, i) ? "#undef" :
            sprint(; context=io) do io′
                show_unquoted(io′, stmt.values[i], indent)
            end
        "$prefix$e => $v"
        end for i in 1:length(stmt.edges)
    ]
    print(io, "φ ", '(')
    join(io, args, ", ")
    print(io, ')')
end

```
-/
def show_unquoted_phinode {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (edges : List (JInt .i32)) (values : List (Option (Value L))) (indent : JInt64)
    (pfx : String) : m Unit := do
  let args ← phinode_args p a c io indent pfx values 0 edges
  locked p io (do printStr p io "φ "; printStr p io "(")
  join_bytes p io args
  printStr p io ")"
partial_fixpoint

-- The comprehension of `show_unquoted_phinode` from edge index `i` (0-based). `isassigned` is false
-- outside `values`, so a missing element prints `#undef`. `"$e"` of an `Int32` edge has the digits
-- of `string(e)`.
def phinode_args {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (indent : JInt64) (pfx : String) (values : List (Option (Value L))) (i : Nat) :
    List (JInt .i32) → m (List Bytes)
  | [] => pure []
  | e :: es => do
    let v ← match values[i]? with
      | some (some x) => do
        -- `sprint(; context=io) do io' … end`
        let buf ← c.newBuffer
        let ctx := JIO.context (← IOContext_IO_IO p a (.plain buf) io)
        show_unquoted_3 p a c ctx x indent
        c.takestring buf
      | _ => pure (lit "#undef")
    let es' ← c.stringInt (i64 e.val)
    let rest ← phinode_args p a c io indent pfx values (i + 1) es
    pure ((lit pfx ++ es' ++ lit " => " ++ v) :: rest)
partial_fixpoint

/--
Julia source: base/show.jl:2949-2958 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted(io::IO, stmt::PhiCNode, indent::Int, ::Int)
    print(io, "φᶜ (")
    first = true
    for v in stmt.values
        first ? (first = false) : print(io, ", ")
        show_unquoted(io, v, indent)
    end
    print(io, ")")
end

```
-/
def show_unquoted_PhiCNode {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (values : List (Option (Value L))) (indent : JInt64) : m Unit := do
  printStr p io "φc ("
  phic_loop p a c io indent true values
  printStr p io ")"
partial_fixpoint

-- `for v in stmt.values`: iterating an unassigned element throws `UndefRefError`.
def phic_loop {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L) (io : JIO Io V)
    (indent : JInt64) (first : Bool) : List (Option (Value L)) → m Unit
  | [] => pure ()
  | v :: vs => do
    let v ← match v with
      | some x => pure x
      | none => throwShow .undefRefError
    if !first then printStr p io ", "
    show_unquoted_3 p a c io v indent
    phic_loop p a c io indent false vs
partial_fixpoint

/--
Julia source: base/show.jl:2959-2966 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted(io::IO, stmt::PiNode, indent::Int, ::Int)
    print(io, "π (")
    show_unquoted(io, stmt.val, indent)
    print(io, ", ")
    printstyled(io, stmt.typ, color=:cyan)
    print(io, ")")
end

```
-/
def show_unquoted_PiNode {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (val : Value L) (typ : L) (indent : JInt64) : m Unit := do
  printStr p io "π ("
  show_unquoted_3 p a c io val indent
  printStr p io ", "
  printstyledStr p a c io (fun io' => c.printLeaf io' typ) "cyan" false
  printStr p io ")"
partial_fixpoint

/--
Julia source: base/show.jl:2967-2974 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted(io::IO, stmt::UpsilonNode, indent::Int, ::Int)
    print(io, "ϒ (")
    isdefined(stmt, :val) ?
        show_unquoted(io, stmt.val, indent) :
        print(io, "#undef")
    print(io, ")")
end

```
-/
def show_unquoted_UpsilonNode {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (val : Option (Value L)) (indent : JInt64) : m Unit := do
  printStr p io "ϒ ("
  match val with
  | some v => show_unquoted_3 p a c io v indent
  | none => printStr p io "#undef"
  printStr p io ")"
partial_fixpoint

/--
Julia source: base/show.jl:2975-2983 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted(io::IO, stmt::ReturnNode, indent::Int, ::Int)
    if !isdefined(stmt, :val)
        print(io, "unreachable")
    else
        print(io, "return ")
        show_unquoted(io, stmt.val, indent)
    end
end

```
-/
def show_unquoted_ReturnNode {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (val : Option (Value L)) (indent : JInt64) : m Unit := do
  match val with
  | none => printStr p io "unreachable"
  | some v =>
    printStr p io "return "
    show_unquoted_3 p a c io v indent
partial_fixpoint

/--
Julia source: base/show.jl:2984-2984 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_unquoted(io::IO, stmt::GotoIfNot, indent::Int, ::Int) = show_unquoted_gotoifnot(io, stmt, indent, "%")
```
-/
def show_unquoted_GotoIfNot {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (cond : Value L) (dest indent : JInt64) : m Unit :=
  show_unquoted_gotoifnot p a c io cond dest indent "%"
partial_fixpoint

/--
Julia source: base/show.jl:2985-2989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unquoted_gotoifnot(io::IO, stmt::GotoIfNot, indent::Int, prefix::String)
    print(io, "goto ", prefix, stmt.dest, " if not ")
    show_unquoted(io, stmt.cond, indent)
end

```
-/
def show_unquoted_gotoifnot {L : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m] (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (io : JIO Io V) (cond : Value L) (dest indent : JInt64) (pfx : String) : m Unit := do
  locked p io (do printStr p io "goto "; printStr p io pfx; printInt p c io dest; printStr p io " if not ")
  show_unquoted_3 p a c io cond indent
partial_fixpoint

end

/-- The parser's operator tables (`base/meta.jl` and the `jl_operator_precedence` `ccall`). -/
structure OperatorOps where
  /-- `ccall(:jl_operator_precedence, Cint, (Cstring,), s)`. -/
  jl_operator_precedence : Sym → JInt .i32
  isunaryoperator : Sym → Bool
  is_unary_and_binary_operator : Sym → Bool

/-- Julia's associativity result symbols. -/
inductive Associativity where
  | left | none | right
  deriving DecidableEq, Repr

/--
Julia source: base/show.jl:1693-1722 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    operator_precedence(s::Symbol)

Return an integer representing the precedence of a binary operator `s`, relative to
other operators. Higher-numbered operators take precedence over lower-numbered
operators. Return `0` if `s` is not a valid binary operator.

(The precedence of *unary* operators is handled differently, including cases like `+`
where an operator can be either unary or binary.)

# Examples
```jldoctest
julia> Base.operator_precedence(:+), Base.operator_precedence(:*), Base.operator_precedence(:.)
(11, 12, 17)

julia> Base.operator_precedence(:sin), Base.operator_precedence(:+=), Base.operator_precedence(:(=))  # (Note the necessary parens on `:(=)`)
(0, 1, 1)
```
"""
operator_precedence(s::Symbol) = Int(ccall(:jl_operator_precedence, Cint, (Cstring,), s))
operator_precedence(x::Any) = 0 # fallback for generic expression nodes
const prec_assignment = operator_precedence(:(=))
const prec_pair = operator_precedence(:(=>))
const prec_control_flow = operator_precedence(:(&&))
const prec_arrow = operator_precedence(:(-->))
const prec_comparison = operator_precedence(:(>))
const prec_power = operator_precedence(:(^))
const prec_decl = operator_precedence(:(::))

````
-/
-- `Int(::Cint)` sign-extends the `ccall` result.
def operator_precedence (o : OperatorOps) (s : Sym) : JInt64 := i64 (o.jl_operator_precedence s).val
-- `operator_precedence(x::Any)`: `0` for a non-`Symbol`.
def operator_precedence_Any {X : Type} (_x : X) : JInt64 := i64 0
def prec_assignment (o : OperatorOps) : JInt64 := operator_precedence o "="
def prec_pair (o : OperatorOps) : JInt64 := operator_precedence o "=>"
def prec_control_flow (o : OperatorOps) : JInt64 := operator_precedence o "&&"
def prec_arrow (o : OperatorOps) : JInt64 := operator_precedence o "-->"
def prec_comparison (o : OperatorOps) : JInt64 := operator_precedence o ">"
def prec_power (o : OperatorOps) : JInt64 := operator_precedence o "^"
def prec_decl (o : OperatorOps) : JInt64 := operator_precedence o "::"

/--
Julia source: base/show.jl:1723-1749 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    operator_associativity(s::Symbol)

Return a symbol representing the associativity of operator `s`. Left- and right-associative
operators return `:left` and `:right`, respectively. Return `:none` if `s` is non-associative
or an invalid operator.

# Examples
```jldoctest
julia> Base.operator_associativity(:-), Base.operator_associativity(:+), Base.operator_associativity(:^)
(:left, :none, :right)

julia> Base.operator_associativity(:⊗), Base.operator_associativity(:sin), Base.operator_associativity(:→)
(:left, :none, :right)
```
"""
function operator_associativity(s::Symbol)
    if operator_precedence(s) in (prec_arrow, prec_assignment, prec_control_flow, prec_pair, prec_power) ||
        (isunaryoperator(s) && !is_unary_and_binary_operator(s)) ||
        (s === :<| || s === :|| || s == :?)
        return :right
    elseif operator_precedence(s) in (0, prec_comparison) || s in (:+, :++, :*)
        return :none
    end
    return :left
end

````
-/
def operator_associativity (o : OperatorOps) (s : Sym) : Associativity :=
  let prec := operator_precedence o s
  if [prec_arrow o, prec_assignment o, prec_control_flow o, prec_pair o, prec_power o].any (·.val == prec.val) ||
      (o.isunaryoperator s && !o.is_unary_and_binary_operator s) ||
      (s == "<|" || s == "||" || s == "?") then
    .right
  else if [i64 0, prec_comparison o].any (·.val == (operator_precedence o s).val) || ["+", "++", "*"].contains s then
    .none
  else
    .left

-- UNTRANSLATED
-- declarations of the generic functions `printstyled` and `with_output_color` without methods
-- Source: base/show.jl:1757-1761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ## AST printing helpers ##
-- 
-- function printstyled end
-- function with_output_color end
-- 
-- /Source

/--
Julia source: base/show.jl:1762-1765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
emphasize(io, str::AbstractString, col = Base.error_color()) = get(io, :color, false)::Bool ?
    printstyled(io, str; color=col, bold=true) :
    print(io, uppercase(str))

```
-/
def emphasize {S : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (printstyled : PrintStyled m Io V)
    (printS : JIO Io V → S → m Unit) (uppercase : S → m Bytes) (error_color : Sym) (io : JIO Io V) (str : S)
    (col : Sym := error_color) : m Unit := do
  if ← assertBool a (getIO p io "color" false) then
    printstyled io [fun io => printS io str] col true
  else
    printBytes p io (← uppercase str)

/--
Julia source: base/show.jl:2608-2617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
demangle_function_name(name::Symbol) = Symbol(demangle_function_name(string(name)))
function demangle_function_name(name::AbstractString)
    demangle = split(name, '#')
    # kw sorters and impl methods use the name scheme `f#...`
    if length(demangle) >= 2 && demangle[1] != ""
        return demangle[1]
    end
    return name
end

```
-/
def demangle_function_name_AbstractString {S : Type} (split : S → Char → List S) (isEmpty : S → Bool)
    (name : S) : S :=
  let demangle := split name '#'
  -- kw sorters and impl methods use the name scheme `f#...`
  match demangle with
  | d :: _ :: _ => if !isEmpty d then d else name
  | _ => name
def demangle_function_name_Symbol {S : Type} (split : S → Char → List S) (isEmpty : S → Bool)
    (string : Sym → S) (symbol : S → m Sym) (name : Sym) : m Sym :=
  symbol (demangle_function_name_AbstractString split isEmpty (string name))


/--
Julia source: base/show.jl:2645-2652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_within_stacktrace(io, s...; color=:normal, bold=false)
    if get(io, :backtrace, false)::Bool
        printstyled(io, s...; color, bold)
    else
        print(io, s...)
    end
end

```
-/
def print_within_stacktrace (p : IOPrims m Io V) (a : AnyOps V Ty) (printstyled : PrintStyled m Io V)
    (io : JIO Io V) (s : List (JIO Io V → m Unit)) (color : Sym := "normal") (bold : Bool := false) :
    m Unit := do
  if ← assertBool a (getIO p io "backtrace" false) then
    printstyled io s color bold
  else
    printAll p io (s.map fun x => x io)


/--
Julia source: base/show.jl:2712-2724 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function type_limited_string_from_context(out::IO, str::String)
    typelimitflag = get(out, :stacktrace_types_limited, nothing)
    if typelimitflag isa RefValue{Bool}
        sz = get(out, :displaysize, Base.displaysize_(out))::Tuple{Int, Int}
        str_lim = type_depth_limit(str, max(sz[2], 120))
        if sizeof(str_lim) < sizeof(str)
            typelimitflag[] = true
        end
        str = str_lim
    end
    return str
end

```
-/
def type_limited_string_from_context {R : Type} (p : IOPrims m Io V) (a : AnyOps V Ty)
    (asBoolRef : V → Option R) (setRef : R → Bool → m Unit) (displaysize_ : JIO Io V → m (JInt64 × JInt64))
    (type_depth_limit : Bytes → JInt64 → m Bytes) (out : JIO Io V) (str : Bytes) : m Bytes := do
  let typelimitflag := getIO p out "stacktrace_types_limited" ()
  let mut str := str
  -- `typelimitflag isa RefValue{Bool}`; the default `nothing` is not.
  match typelimitflag with
  | .inl v =>
    match asBoolRef v with
    | some r =>
      let dflt ← displaysize_ out
      let sz ← match getIO p out "displaysize" dflt with
        | .inl v => match a.asDims v with
          | some d => pure d
          | none => throwShow .typeError
        | .inr d => pure d
      let str_lim ← type_depth_limit str (i64 (max sz.2.val 120))
      if str_lim.length < str.length then
        setRef r true
      str := str_lim
    | none => pure ()
  | .inr () => pure ()
  return str

/-- `x & s != 0` on the `Int` state of `type_depth_limit`. -/
def stateis (state s : JInt64) : Bool := (JuliaLean.base.int.band state s).val != 0

/-- `xs[i] += w` on a `Vector{Int}`. -/
def addAt (xs : List JInt64) (i : JInt64) (w : JInt64) : m (List JInt64) :=
  if h : 1 ≤ i.val ∧ i.val ≤ xs.length then
    pure (xs.set (i.val - 1).toNat (i64 ((xs[(i.val - 1).toNat]'(by omega)).val + w.val)))
  else throwShow (.jl .boundsError)

/-- `depths[i] = depth` on a `Vector{Int16}`: converts to `Int16`. -/
def setDepth (xs : List (JInt .i16)) (i depth : JInt64) : m (List (JInt .i16)) := do
  let d ← ofJl (JuliaLean.base.int.convert .i16 depth)
  if 1 ≤ i.val ∧ i.val ≤ xs.length then pure (xs.set (i.val - 1).toNat d)
  else throwShow (.jl .boundsError)

/-- The `while strwid > n` loop of `type_depth_limit`. -/
def type_depth_limit_while [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (width_at levelcount : List JInt64) (n : JInt64) (strwid limit_at : JInt64) :
    m JInt64 := do
  if strwid.val > n.val then
    let limit_at' := i64 (limit_at.val - 1)
    if limit_at'.val ≤ 1 then return limit_at'
    -- add levelcount[] to include space taken by `…`
    let mut strwid := i64 (strwid.val - (← atIdx width_at limit_at').val + (← atIdx levelcount limit_at').val)
    if limit_at'.val < width_at.length then
      -- take away the `…` from the previous considered level
      strwid := i64 (strwid.val - (← atIdx levelcount (i64 (limit_at'.val + 1))).val)
    type_depth_limit_while width_at levelcount n strwid limit_at'
  else return limit_at
partial_fixpoint

/--
Julia source: base/show.jl:2725-2817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# limit nesting depth of `{ }` until string textwidth is less than `n`
function type_depth_limit(str::String, n::Int; maxdepth = nothing)
    depth = 0
    width_at = Int[]                       # total textwidth at each nesting depth
    depths = zeros(Int16, lastindex(str))  # depth at each character index
    levelcount = Int[]                     # number of nodes at each level
    strwid = 0
    st_0, st_backslash, st_squote, st_dquote = 0,1,2,4
    state = Ref(st_0)
    stateis(s) = (state[] & s) != 0
    quoted() = stateis(st_squote) || stateis(st_dquote)
    enter(s) = (state[] |= s)
    leave(s) = (state[] &= ~s)
    for (i, c) in ANSIIterator(str)
        if c isa ANSIDelimiter
            depths[i] = depth
            continue
        end

        if c == '\\' && quoted()
            enter(st_backslash)
        elseif c == '\''
            if stateis(st_backslash) || stateis(st_dquote)
            elseif stateis(st_squote)
                leave(st_squote)
            else
                enter(st_squote)
            end
        elseif c == '"'
            if stateis(st_backslash) || stateis(st_squote)
            elseif stateis(st_dquote)
                leave(st_dquote)
            else
                enter(st_dquote)
            end
        end
        if c == '}' && !quoted()
            depth -= 1
        end

        wid = textwidth(c)
        strwid += wid
        if depth > 0
            width_at[depth] += wid
        end
        depths[i] = depth

        if c == '{' && !quoted()
            depth += 1
            if depth > length(width_at)
                push!(width_at, 0)
                push!(levelcount, 0)
            end
            levelcount[depth] += 1
        end
        if c != '\\' && stateis(st_backslash)
            leave(st_backslash)
        end
    end
    if maxdepth === nothing
        limit_at = length(width_at) + 1
        while strwid > n
            limit_at -= 1
            limit_at <= 1 && break
            # add levelcount[] to include space taken by `…`
            strwid = strwid - width_at[limit_at] + levelcount[limit_at]
            if limit_at < length(width_at)
                # take away the `…` from the previous considered level
                strwid -= levelcount[limit_at+1]
            end
        end
    else
        limit_at = maxdepth
    end
    output = IOBuffer()
    prev = 0
    for (i, c) in ANSIIterator(str)
        di = depths[i]
        if di < limit_at
            if c isa ANSIDelimiter
                write(output, c.del)
            else
                write(output, c)
            end
        end
        if di > prev && di == limit_at
            write(output, "…")
        end
        prev = di
    end
    return unsafe_takestring!(output)
end

```
-/
def type_depth_limit {S C : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (s : StrOps S C) (str : S) (n : JInt64) (maxdepth : Option JInt64 := none) :
    m Bytes := do
  let mut depth := i64 0
  let mut width_at : List JInt64 := []
  let lastindex := s.lastindex str
  if lastindex.val < 0 then throwShow (.jl (.argumentError "invalid Array dimensions"))
  let mut depths : List (JInt .i16) := List.replicate lastindex.val.toNat (JInt.wrap .i16 0)
  let mut levelcount : List JInt64 := []
  let mut strwid := i64 0
  let st_backslash := i64 1
  let st_squote := i64 2
  let st_dquote := i64 4
  let mut state := i64 0
  for (i, c) in s.ansiPairs str do
    match c with
    | .delim _ =>
      depths ← setDepth depths i depth
      continue
    | .char c =>
      let quoted := stateis state st_squote || stateis state st_dquote
      if s.charEq c (s.ofChar '\\') && quoted then
        state := JuliaLean.base.int.bor state st_backslash
      else if s.charEq c (s.ofChar '\'') then
        if stateis state st_backslash || stateis state st_dquote then
          pure ()
        else if stateis state st_squote then
          state := JuliaLean.base.int.band state (JuliaLean.base.int.bnot st_squote)
        else
          state := JuliaLean.base.int.bor state st_squote
      else if s.charEq c (s.ofChar '"') then
        if stateis state st_backslash || stateis state st_squote then
          pure ()
        else if stateis state st_dquote then
          state := JuliaLean.base.int.band state (JuliaLean.base.int.bnot st_dquote)
        else
          state := JuliaLean.base.int.bor state st_dquote
      if s.charEq c (s.ofChar '}') && !(stateis state st_squote || stateis state st_dquote) then
        depth := i64 (depth.val - 1)
      let wid := s.textwidthChar c
      strwid := i64 (strwid.val + wid.val)
      if depth.val > 0 then
        width_at ← addAt width_at depth wid
      depths ← setDepth depths i depth
      if s.charEq c (s.ofChar '{') && !(stateis state st_squote || stateis state st_dquote) then
        depth := i64 (depth.val + 1)
        if depth.val > width_at.length then
          width_at := width_at ++ [i64 0]
          levelcount := levelcount ++ [i64 0]
        levelcount ← addAt levelcount depth (i64 1)
      if !s.charEq c (s.ofChar '\\') && stateis state st_backslash then
        state := JuliaLean.base.int.band state (JuliaLean.base.int.bnot st_backslash)
  let limit_at ← match maxdepth with
    | none => type_depth_limit_while width_at levelcount n strwid (i64 (width_at.length + 1))
    | some md => pure md
  let mut output : Bytes := []
  let mut prev := i64 0
  for (i, c) in s.ansiPairs str do
    let di := (← atIdx depths i).val
    if di < limit_at.val then
      match c with
      | .delim d => output := output ++ d.del
      | .char c => output := output ++ s.charBytes c
    if di > prev.val && di == limit_at.val then
      output := output ++ lit "…"
    prev := i64 di
  return output

/--
Julia source: base/show.jl:2818-2839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_type_bicolor(io, type; kwargs...)
    str = sprint(show, type, context=io)
    print_type_bicolor(io, str; kwargs...)
end

function print_type_bicolor(io, str::String; color=:normal, inner_color=:light_black, use_color::Bool=true)
    i = findfirst('{', str)
    if !use_color # fix #41928
        print(io, str)
    elseif i === nothing
        printstyled(io, str; color=color)
    else
        printstyled(io, str[1:prevind(str,i)]; color=color)
        if endswith(str, "...")
            printstyled(io, str[i:prevind(str,end,3)]; color=inner_color)
            printstyled(io, "..."; color=color)
        else
            printstyled(io, str[i:end]; color=inner_color)
        end
    end
end

```
-/
def print_type_bicolor_String (p : IOPrims m Io V) (printstyled : PrintStyled m Io V) (b : BytesOps m) (io : JIO Io V)
    (str : Bytes) (color : Sym := "normal") (inner_color : Sym := "light_black") (use_color : Bool := true) :
    m Unit := do
  let i := b.findfirst '{' str
  if !use_color then -- fix #41928
    printBytes p io str
  else
    match i with
    | none => printstyled io [fun io => printBytes p io str] color false
    | some i =>
      let head ← b.slice str (i64 1) (b.prevind str i (i64 1))
      printstyled io [fun io => printBytes p io head] color false
      if b.endswith str (lit "...") then
        let inner ← b.slice str i (b.prevind str (b.lastindex str) (i64 3))
        printstyled io [fun io => printBytes p io inner] inner_color false
        printstyled io [fun io => printStr p io "..."] color false
      else
        let inner ← b.slice str i (b.lastindex str)
        printstyled io [fun io => printBytes p io inner] inner_color false
def print_type_bicolor_Any {X : Type} (p : IOPrims m Io V) (printstyled : PrintStyled m Io V) (b : BytesOps m)
    (sprintShow : JIO Io V → X → m Bytes) (io : JIO Io V) (type : X) (color : Sym := "normal")
    (inner_color : Sym := "light_black") (use_color : Bool := true) : m Unit := do
  let str ← sprintShow io type
  print_type_bicolor_String p printstyled b io str color inner_color use_color


-- UNTRANSLATED
-- top-level call `Compiler.load_irshow!()` that loads the compiler's IR printer
-- Source: base/show.jl:2914-2915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Compiler.load_irshow!()
-- 
-- /Source

/--
Julia source: base/show.jl:3169-3169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nocolor(io::IO) = IOContext(io, :color => false)
```
-/
def nocolor (p : IOPrims m Io V) (a : AnyOps V Ty) (io : JIO Io V) : m (IOContext Io V) :=
  IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (boolConv a) io ("color", false)

/--
Julia source: base/show.jl:3170-3174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
alignment_from_show(io::IO, x::Any) =
    textwidth(sprint(show, x, context=nocolor(io), sizehint=0))
alignment_from_show(io::IO, x::AbstractString) =
    textwidth(sprint(show, MIME"text/plain"(), x, context=nocolor(io), sizehint=0))

```
-/
def alignment_from_show_Any {X : Type} (p : IOPrims m Io V) (a : AnyOps V Ty)
    (sprintShow : JIO Io V → X → m Bytes) (textwidth : Bytes → JInt64) (io : JIO Io V) (x : X) : m JInt64 := do
  return textwidth (← sprintShow (.context (← nocolor p a io)) x)
def alignment_from_show_AbstractString {X : Type} (p : IOPrims m Io V) (a : AnyOps V Ty)
    (sprintShowTextPlain : JIO Io V → X → m Bytes) (textwidth : Bytes → JInt64) (io : JIO Io V) (x : X) :
    m JInt64 := do
  return textwidth (← sprintShowTextPlain (.context (← nocolor p a io)) x)

/--
Julia source: base/show.jl:3175-3193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
`alignment(io, X)` returns a tuple (left,right) showing how many characters are
needed on either side of an alignment feature such as a decimal point.

# Examples
```jldoctest
julia> Base.alignment(stdout, 42)
(2, 0)

julia> Base.alignment(stdout, 4.23)
(1, 3)

julia> Base.alignment(stdout, 1 + 10im)
(3, 5)
```
"""
alignment(io::IO, x::Any) = (0, alignment_from_show(io, x))
alignment(io::IO, x::Number) = (alignment_from_show(io, x), 0)
alignment(io::IO, x::Integer) = (alignment_from_show(io, x), 0)
````
-/
def alignment_Any {X : Type} (alignment_from_show : JIO Io V → X → m JInt64) (io : JIO Io V) (x : X) :
    m (JInt64 × JInt64) := do
  return (i64 0, ← alignment_from_show io x)
def alignment_Number {X : Type} (alignment_from_show : JIO Io V → X → m JInt64) (io : JIO Io V) (x : X) :
    m (JInt64 × JInt64) := do
  return (← alignment_from_show io x, i64 0)
def alignment_Integer {X : Type} (alignment_from_show : JIO Io V → X → m JInt64) (io : JIO Io V) (x : X) :
    m (JInt64 × JInt64) := do
  return (← alignment_from_show io x, i64 0)

/-- `alignment(io, x)` for `Real`, `Complex` and `Rational`: `match(regex, s)` (PCRE, not
modelled) returns its two captures or `nothing`. -/
def alignment_regex {X : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (sprintShow : JIO Io V → X → m Bytes)
    (matchRegex : Bytes → Option (Bytes × Bytes)) (textwidth : Bytes → JInt64) (io : JIO Io V) (x : X) :
    m (JInt64 × JInt64) := do
  let s ← sprintShow (.context (← nocolor p a io)) x
  match matchRegex s with
  | none => return (textwidth s, i64 0)
  | some (c1, c2) => return (textwidth c1, textwidth c2)

/--
Julia source: base/show.jl:3194-3199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function alignment(io::IO, x::Real)
    s = sprint(show, x, context=nocolor(io), sizehint=0)
    m = match(r"^(.*?)((?:[\.eEfF].*)?)$", s)
    m === nothing ? (textwidth(s), 0) :
                    (textwidth(m.captures[1]), textwidth(m.captures[2]))
end
```
-/
def alignment_Real {X : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (sprintShow : JIO Io V → X → m Bytes)
    (match_real : Bytes → Option (Bytes × Bytes)) (textwidth : Bytes → JInt64) (io : JIO Io V) (x : X) :
    m (JInt64 × JInt64) :=
  alignment_regex p a sprintShow match_real textwidth io x

/--
Julia source: base/show.jl:3200-3205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function alignment(io::IO, x::Complex)
    s = sprint(show, x, context=nocolor(io), sizehint=0)
    m = match(r"^(.*[^ef][\+\-])(.*)$", s)
    m === nothing ? (textwidth(s), 0) :
                    (textwidth(m.captures[1]), textwidth(m.captures[2]))
end
```
-/
def alignment_Complex {X : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (sprintShow : JIO Io V → X → m Bytes)
    (match_complex : Bytes → Option (Bytes × Bytes)) (textwidth : Bytes → JInt64) (io : JIO Io V) (x : X) :
    m (JInt64 × JInt64) :=
  alignment_regex p a sprintShow match_complex textwidth io x

/--
Julia source: base/show.jl:3206-3212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function alignment(io::IO, x::Rational)
    s = sprint(show, x, context=nocolor(io), sizehint=0)
    m = match(r"^(.*?/)(/.*)$", s)
    m === nothing ? (textwidth(s), 0) :
                    (textwidth(m.captures[1]), textwidth(m.captures[2]))
end

```
-/
def alignment_Rational {X : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (sprintShow : JIO Io V → X → m Bytes)
    (match_rational : Bytes → Option (Bytes × Bytes)) (textwidth : Bytes → JInt64) (io : JIO Io V) (x : X) :
    m (JInt64 × JInt64) :=
  alignment_regex p a sprintShow match_rational textwidth io x

/--
Julia source: base/show.jl:3213-3225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function alignment(io::IO, x::Pair)
    fullwidth = alignment_from_show(io, x)
    if !isdelimited(io, x) # i.e. use "=>" for display
        ctx = IOContext(io, :typeinfo => gettypeinfos(io, x)[1])
        left = alignment_from_show(ctx, x.first)
        left += 2 * !isdelimited(ctx, x.first) # for parens around p.first
        left += !(get(io, :compact, false)::Bool) # spaces are added around "=>"
        (left+1, fullwidth-left-1) # +1 for the "=" part of "=>"
    else
        (0, fullwidth) # as for x::Any
    end
end

```
-/
def alignment_Pair {A B : Type} (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty)
    (typeOfA : A → Ty) (typeOfB : B → Ty) (typeOfP : Pair A B → Ty) (isdelimitedA : JIO Io V → A → Bool)
    (alignment_from_show_P : JIO Io V → Pair A B → m JInt64) (alignment_from_show_A : JIO Io V → A → m JInt64)
    (io : JIO Io V) (x : Pair A B) : m (JInt64 × JInt64) := do
  let fullwidth ← alignment_from_show_P io x
  if !(← isdelimited_Pair p a t typeOfA typeOfB typeOfP io x) then -- i.e. use "=>" for display
    let ctx ← withTypeinfo p a io (← gettypeinfos p a t typeOfP io x).1
    let mut left ← alignment_from_show_A ctx x.first
    left := i64 (left.val + 2 * (if !isdelimitedA ctx x.first then 1 else 0)) -- for parens around p.first
    left := i64 (left.val + (if !(← assertBool a (getIO p io "compact" false)) then 1 else 0))
    return (i64 (left.val + 1), i64 (fullwidth.val - left.val - 1)) -- +1 for the "=" part of "=>"
  else
    return (i64 0, fullwidth) -- as for x::Any

/--
Julia source: base/show.jl:3230-3255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    summary(io::IO, x)
    str = summary(x)

Print to a stream `io`, or return a string `str`, giving a brief description of
a value. By default returns `string(typeof(x))`, e.g. [`Int64`](@ref).

For arrays, returns a string of size and type info,
e.g. `10-element Vector{Int64}` or `9×4×5 Array{Float64, 3}`.

# Examples
```jldoctest
julia> summary(1)
"Int64"

julia> summary(zeros(2))
"2-element Vector{Float64}"
```
"""
summary(io::IO, x) = print(io, typeof(x))
function summary(x)
    io = IOBuffer()
    summary(io, x)
    takestring!(io)
end

````
-/
def summary_IO {X : Type} (printType : JIO Io V → Ty → m Unit) (typeOf : X → Ty) (io : JIO Io V) (x : X) :
    m Unit :=
  printType io (typeOf x)
def summary_1 {X : Type} (newBuffer : m Io) (takestring : Io → m Bytes) (summary : JIO Io V → X → m Unit)
    (x : X) : m Bytes := do
  let io ← newBuffer
  summary (.plain io) x
  takestring io

/--
Julia source: base/show.jl:3256-3261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## `summary` for AbstractArrays
# sizes such as 0-dimensional, 4-dimensional, 2x3
dims2string(d) = isempty(d) ? "0-dimensional" :
                 length(d) == 1 ? "$(d[1])-element" :
                 join(map(string,d), '×')

```
-/
def dims2string (stringInt : JInt64 → m Bytes) (join : List Bytes → String → m Bytes) (d : List JInt64) :
    m Bytes := do
  if d.isEmpty then return lit "0-dimensional"
  else match d with
    | [d1] => return (← stringInt d1) ++ lit "-element"
    | _ => join (← d.mapM stringInt) "×"

/-- An index of an array's axes: an `IdentityUnitRange` or `Slice` (with its `indices`) or another index. -/
inductive AxisIndex (X : Type) where
  | wrapped (indices : X)
  | other (i : X)

/--
Julia source: base/show.jl:3262-3265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inds2string(inds) = join(map(_indsstring,inds), '×')
_indsstring(i) = string(i)
_indsstring(i::Union{IdentityUnitRange, Slice}) = string(i.indices)

```
-/
def _indsstring {X : Type} (string : X → m Bytes) : AxisIndex X → m Bytes
  | .other i => string i
  | .wrapped indices => string indices
def inds2string {X : Type} (string : X → m Bytes) (join : List Bytes → String → m Bytes) (inds : List (AxisIndex X)) :
    m Bytes := do
  join (← inds.mapM (_indsstring string)) "×"

/--
Julia source: base/show.jl:3266-3277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# anything array-like gets summarized e.g. 10-element Array{Int64,1}
summary(io::IO, a::AbstractArray) = array_summary(io, a, axes(a))
function array_summary(io::IO, a, inds::Tuple{Vararg{OneTo}})
    print(io, dims2string(length.(inds)), " ")
    showarg(io, a, true)
end
function array_summary(io::IO, a, inds)
    print(io, dims2string(length.(inds)), " ")
    showarg(io, a, true)
    print(io, " with indices ", inds2string(inds))
end

```
-/
def summary_AbstractArray {A Ax : Type} (axes : A → Ax) (array_summary : JIO Io V → A → Ax → m Unit)
    (io : JIO Io V) (x : A) : m Unit :=
  array_summary io x (axes x)
def array_summary_OneTo {A Ax : Type} (p : IOPrims m Io V) (lengths : Ax → List JInt64)
    (dims2string : List JInt64 → m Bytes) (showarg : JIO Io V → A → Bool → m Unit) (io : JIO Io V) (x : A)
    (inds : Ax) : m Unit := do
  let d ← dims2string (lengths inds)
  printAll p io [printBytes p io d, printStr p io " "]
  showarg io x true
def array_summary {A Ax : Type} (p : IOPrims m Io V) (lengths : Ax → List JInt64)
    (dims2string : List JInt64 → m Bytes) (inds2string : Ax → m Bytes) (showarg : JIO Io V → A → Bool → m Unit)
    (io : JIO Io V) (x : A) (inds : Ax) : m Unit := do
  let d ← dims2string (lengths inds)
  printAll p io [printBytes p io d, printStr p io " "]
  showarg io x true
  let s ← inds2string inds
  printAll p io [printStr p io " with indices ", printBytes p io s]

/--
Julia source: base/show.jl:3278-3285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## `summary` for GenericMemoryRef
function summary(io::IO, mref::GenericMemoryRef)
    offset = Core.memoryrefoffset(mref)
    len_after_offset = length(mref.mem) - offset + 1
    print(io, len_after_offset, "-element ")
    showarg(io, mref, true)
end

```
-/
def summary_GenericMemoryRef {R : Type} (p : IOPrims m Io V) (memoryrefoffset : R → JInt64)
    (memLength : R → JInt64) (printInt : JIO Io V → JInt64 → m Unit) (showarg : JIO Io V → R → Bool → m Unit)
    (io : JIO Io V) (mref : R) : m Unit := do
  let offset := memoryrefoffset mref
  let len_after_offset := i64 ((memLength mref).val - offset.val + 1)
  printAll p io [printInt io len_after_offset, printStr p io "-element "]
  showarg io mref true

/--
Julia source: base/show.jl:3286-3288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## `summary` for Function
summary(io::IO, f::Function) = show(io, MIME"text/plain"(), f)

```
-/
def summary_Function {F : Type} (show_textplain : JIO Io V → F → m Unit) (io : JIO Io V) (f : F) : m Unit :=
  show_textplain io f

/--
Julia source: base/show.jl:3289-3338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.showarg(io::IO, x, toplevel)

Show the quasi-type of `x` where quasi-type is the type of `x` or an expression (possibly
containing quasi-types) that would generate an object of the same type as `x`. The shorter
of these two options is typically used.

This function is used by `summary` to display type information in terms of sequences of
function calls on objects.

Show a leading `::` if `toplevel` is `false` and showing a type. `toplevel` is `true` if
this is the direct call from `summary` and `false` for nested (recursive) calls.

The fallback definition is to print `x` as "::\\\$(typeof(x))" or "\\\$(typeof(x))",
representing argument `x` in terms of its type. However, you can specialize
this function for specific types to customize printing. This customization is useful for
types that have simple, public constructors and verbose and/or internal types and type
parameters such as `reinterpret`ed arrays or `SubArray`s.

# Examples

A SubArray created as `view(a, :, 3, 2:5)`, where `a` is a
3-dimensional Float64 array, has type

    SubArray{Float64, 2, Array{Float64, 3}, Tuple{Colon, Int64, UnitRange{Int64}}, false}

The default `show` printing would display this full type.
However, the summary for SubArrays actually prints as

    2×4 view(::Array{Float64, 3}, :, 3, 2:5) with eltype Float64

because of a definition similar to

    function Base.showarg(io::IO, v::SubArray, toplevel)
        print(io, "view(")
        showarg(io, parent(v), false)
        print(io, ", ", join(v.indices, ", "))
        print(io, ')')
        toplevel && print(io, " with eltype ", eltype(v))
    end

Note that we're calling `showarg` recursively for the parent array
type, indicating that any recursed calls are not at the top level.
Printing the parent as `::Array{Float64,3}` is the fallback (non-toplevel)
behavior, because no specialized method for `Array` has been defined.
"""
function showarg(io::IO, @nospecialize(x), toplevel)
    toplevel || print(io, "::")
    print(io, typeof(x))
end
```
-/
def showarg_Any {X : Type} (p : IOPrims m Io V) (printType : JIO Io V → Ty → m Unit) (typeOf : X → Ty)
    (io : JIO Io V) (x : X) (toplevel : Bool) : m Unit := do
  if !toplevel then printStr p io "::"
  printType io (typeOf x)

/--
Julia source: base/show.jl:3339-3342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showarg(io::IO, T::Type, toplevel)
    toplevel || print(io, "::")
    print(io, "Type{", T, "}")
end
```
-/
def showarg_Type (p : IOPrims m Io V) (printType : JIO Io V → Ty → m Unit) (io : JIO Io V) (T : Ty)
    (toplevel : Bool) : m Unit := do
  if !toplevel then printStr p io "::"
  printAll p io [printStr p io "Type{", printType io T, printStr p io "}"]

/--
Julia source: base/show.jl:3343-3348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This method resolves an ambiguity for packages that specialize on eltype
function showarg(io::IO, a::Array{Union{}}, toplevel)
    toplevel || print(io, "::")
    print(io, typeof(a))
end

```
-/
def showarg_ArrayUnion {X : Type} (p : IOPrims m Io V) (printType : JIO Io V → Ty → m Unit) (typeOf : X → Ty)
    (io : JIO Io V) (x : X) (toplevel : Bool) : m Unit := do
  if !toplevel then printStr p io "::"
  printType io (typeOf x)

/-- An index of a `SubArray`: a `Slice` or another index. -/
inductive SubIndex (X : Type) where
  | slice
  | other (i : X)

/--
Julia source: base/show.jl:3358-3363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showindices(io, ::Slice, inds...) =
    (print(io, ", :"); showindices(io, inds...))
showindices(io, ind1, inds...) =
    (print(io, ", ", ind1); showindices(io, inds...))
showindices(io) = nothing

```
-/
def showindices {X : Type} (p : IOPrims m Io V) (printX : JIO Io V → X → m Unit) (io : JIO Io V) :
    List (SubIndex X) → m Unit
  | [] => pure ()
  | .slice :: inds => do
    printStr p io ", :"
    showindices p printX io inds
  | .other ind1 :: inds => do
    printAll p io [printStr p io ", ", printX io ind1]
    showindices p printX io inds

/--
Julia source: base/show.jl:3349-3357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Container specializations
function showarg(io::IO, v::SubArray, toplevel)
    print(io, "view(")
    showarg(io, parent(v), false)
    showindices(io, v.indices...)
    print(io, ')')
    toplevel && print(io, " with eltype ", eltype(v))
    return nothing
end
```
-/
def showarg_SubArray {Sv P X : Type} (p : IOPrims m Io V) (parent : Sv → P) (showargP : JIO Io V → P → Bool → m Unit)
    (indices : Sv → List (SubIndex X)) (printX : JIO Io V → X → m Unit) (printType : JIO Io V → Ty → m Unit)
    (eltype : Sv → Ty) (io : JIO Io V) (v : Sv) (toplevel : Bool) : m Unit := do
  printStr p io "view("
  showargP io (parent v) false
  showindices p printX io (indices v)
  printStr p io ")"
  if toplevel then printAll p io [printStr p io " with eltype ", printType io (eltype v)]
  return ()

/--
Julia source: base/show.jl:3364-3374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showarg(io::IO, r::ReshapedArray, toplevel)
    print(io, "reshape(")
    showarg(io, parent(r), false)
    if !isempty(r.dims)
        print(io, ", ", join(r.dims, ", "))
    end
    print(io, ')')
    toplevel && print(io, " with eltype ", eltype(r))
    return nothing
end

```
-/
def showarg_ReshapedArray {R P : Type} (p : IOPrims m Io V) (parent : R → P) (showargP : JIO Io V → P → Bool → m Unit)
    (dimsEmpty : R → Bool) (joinDims : R → m Bytes) (printType : JIO Io V → Ty → m Unit) (eltype : R → Ty)
    (io : JIO Io V) (r : R) (toplevel : Bool) : m Unit := do
  printStr p io "reshape("
  showargP io (parent r) false
  if !dimsEmpty r then
    let j ← joinDims r
    printAll p io [printStr p io ", ", printBytes p io j]
  printStr p io ")"
  if toplevel then printAll p io [printStr p io " with eltype ", printType io (eltype r)]
  return ()

/--
Julia source: base/show.jl:3375-3380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showarg(io::IO, r::NonReshapedReinterpretArray{T}, toplevel) where {T}
    print(io, "reinterpret(", T, ", ")
    showarg(io, parent(r), false)
    print(io, ')')
end

```
-/
def showarg_NonReshapedReinterpretArray {R P : Type} (p : IOPrims m Io V) (T : R → Ty) (parent : R → P)
    (showargP : JIO Io V → P → Bool → m Unit) (printType : JIO Io V → Ty → m Unit) (io : JIO Io V) (r : R)
    (_toplevel : Bool) : m Unit := do
  printAll p io [printStr p io "reinterpret(", printType io (T r), printStr p io ", "]
  showargP io (parent r) false
  printStr p io ")"

/--
Julia source: base/show.jl:3381-3388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showarg(io::IO, r::ReshapedReinterpretArray{T}, toplevel) where {T}
    print(io, "reinterpret(reshape, ", T, ", ")
    showarg(io, parent(r), false)
    print(io, ')')
    toplevel && print(io, " with eltype ", eltype(r))
    return nothing
end

```
-/
def showarg_ReshapedReinterpretArray {R P : Type} (p : IOPrims m Io V) (T : R → Ty) (parent : R → P)
    (showargP : JIO Io V → P → Bool → m Unit) (printType : JIO Io V → Ty → m Unit) (eltype : R → Ty)
    (io : JIO Io V) (r : R) (toplevel : Bool) : m Unit := do
  printAll p io [printStr p io "reinterpret(reshape, ", printType io (T r), printStr p io ", "]
  showargP io (parent r) false
  printStr p io ")"
  if toplevel then printAll p io [printStr p io " with eltype ", printType io (eltype r)]
  return ()

/--
Julia source: base/show.jl:3389-3395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# printing iterators from Base.Iterators

function show(io::IO, e::Iterators.Enumerate)
    print(io, "enumerate(")
    show(io, e.itr)
    print(io, ')')
end
```
-/
def show_Enumerate {E X : Type} (p : IOPrims m Io V) (itr : E → X) (showX : JIO Io V → X → m Unit) (io : JIO Io V)
    (e : E) : m Unit := do
  printStr p io "enumerate("
  showX io (itr e)
  printStr p io ")"

/--
Julia source: base/show.jl:3396-3397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, z::Iterators.Zip) = show_delim_array(io, z.is, "zip(", ',', ')', false)

```
-/
def show_Zip {Z I X S : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty) (it : IterOps I X S) (typeOfI : I → Ty)
    (printstyled : PrintStyled m Io V) (stringInt : JInt64 → m Bytes) (egal : V → I → Bool) (ofAny : I → V)
    (showX : JIO Io V → X → m Unit) (is : Z → I) (io : JIO Io V) (z : Z) : m Unit :=
  show_delim_array_iter p a t it typeOfI printstyled stringInt egal ofAny showX io (is z) "zip(" "," ")" false

/--
Julia source: base/show.jl:3398-3402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# pretty printing for Iterators.Pairs
function Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T<:AbstractArray
    print(io, "pairs(IndexLinear(), ::", T, ")")
end

```
-/
def showarg_Pairs_IndexLinear {R : Type} (p : IOPrims m Io V) (printType : JIO Io V → Ty → m Unit) (T : R → Ty)
    (io : JIO Io V) (r : R) (_toplevel : Bool) : m Unit :=
  printAll p io [printStr p io "pairs(IndexLinear(), ::", printType io (T r), printStr p io ")"]

/--
Julia source: base/show.jl:3403-3406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.showarg(io::IO, r::Iterators.Pairs{Symbol, <:Any, Nothing, T}, toplevel) where {T <: NamedTuple}
    print(io, "pairs(::NamedTuple)")
end

```
-/
def showarg_Pairs_NamedTuple {R : Type} (p : IOPrims m Io V) (io : JIO Io V) (_r : R) (_toplevel : Bool) :
    m Unit :=
  printStr p io "pairs(::NamedTuple)"

/--
Julia source: base/show.jl:3407-3410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.showarg(io::IO, r::Iterators.Pairs{<:Any, <:Any, I, D}, toplevel) where {D, I}
    print(io, "Iterators.Pairs(::", D, ", ::", I, ")")
end

```
-/
def showarg_Pairs {R : Type} (p : IOPrims m Io V) (printType : JIO Io V → Ty → m Unit) (D I : R → Ty)
    (io : JIO Io V) (r : R) (_toplevel : Bool) : m Unit :=
  printAll p io [printStr p io "Iterators.Pairs(::", printType io (D r), printStr p io ", ::", printType io (I r),
    printStr p io ")"]

/--
Julia source: base/show.jl:3411-3424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# printing BitArrays

# (following functions not exported - mainly intended for debug)

function print_bit_chunk(io::IO, c::UInt64, l::Integer = 64)
    for s = 0:l-1
        d = (c >>> s) & 1
        print(io, "01"[d + 1])
        if (s + 1) & 7 == 0
            print(io, " ")
        end
    end
end

```
-/
def print_bit_chunk (p : IOPrims m Io V) (io : JIO Io V) (c : JInt .u64) (l : JInt64 := i64 64) : m Unit := do
  for s in List.range (l.val.toNat) do
    let d := JuliaLean.base.int.band (JuliaLean.base.int.lshr_Int c (i64 s)) (JInt.wrap .u64 1)
    -- `"01"[d + 1]`
    printStr p io (if d.val + 1 == 1 then "0" else "1")
    if (JuliaLean.base.int.band (i64 (s + 1)) (i64 7)).val == 0 then
      printStr p io " "

/--
Julia source: base/show.jl:3425-3427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print_bit_chunk(c::UInt64, l::Integer) = print_bit_chunk(stdout, c, l)
print_bit_chunk(c::UInt64) = print_bit_chunk(stdout, c)

```
-/
def print_bit_chunk_stdout (p : IOPrims m Io V) (stdout : JIO Io V) (c : JInt .u64) (l : JInt64 := i64 64) :
    m Unit :=
  print_bit_chunk p stdout c l

/--
Julia source: base/show.jl:3428-3437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bitshow(io::IO, B::BitArray)
    isempty(B) && return
    Bc = B.chunks
    for i = 1:length(Bc)-1
        print_bit_chunk(io, Bc[i])
        print(io, ": ")
    end
    l = _mod64(length(B)-1) + 1
    print_bit_chunk(io, Bc[end], l)
end
```
-/
def bitshow {B : Type} (p : IOPrims m Io V) (chunks : B → List (JInt .u64)) (length : B → JInt64)
    (io : JIO Io V) (b : B) : m Unit := do
  if (length b).val == 0 then return
  let Bc := chunks b
  for i in List.range (Bc.length - 1) do
    print_bit_chunk p io (← atIdx Bc (i64 (i + 1)))
    printStr p io ": "
  -- `_mod64(l) = l & 63` (`base/bitarray.jl`)
  let l := i64 ((JuliaLean.base.int.band (i64 ((length b).val - 1)) (i64 63)).val + 1)
  print_bit_chunk p io (← atIdx Bc (i64 Bc.length)) l

/--
Julia source: base/show.jl:3438-3439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bitshow(B::BitArray) = bitshow(stdout, B)

```
-/
def bitshow_stdout {B : Type} (p : IOPrims m Io V) (chunks : B → List (JInt .u64)) (length : B → JInt64)
    (stdout : JIO Io V) (b : B) : m Unit :=
  bitshow p chunks length stdout b

/--
Julia source: base/show.jl:3440-3441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bitstring(B::BitArray) = sprint(bitshow, B)

```
-/
def bitstring_BitArray {B : Type} (p : IOPrims m Io V) (chunks : B → List (JInt .u64)) (length : B → JInt64)
    (sprint : (JIO Io V → m Unit) → m Bytes) (b : B) : m Bytes :=
  sprint fun io => bitshow p chunks length io b

/--
Julia source: base/show.jl:3538-3547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Special pretty printing for EvalInto/IncludeInto
function show(io::IO, ii::IncludeInto)
    if getglobal(ii.m, :include) === ii
        print(io, ii.m)
        print(io, ".include")
    else
        show_default(io, ii)
    end
end

```
-/
def show_IncludeInto {II Mod : Type} (p : IOPrims m Io V) (isSelf : II → m Bool) (modOf : II → Mod)
    (printMod : JIO Io V → Mod → m Unit) (show_default : JIO Io V → II → m Unit) (io : JIO Io V) (ii : II) :
    m Unit := do
  if ← isSelf ii then
    printMod io (modOf ii)
    printStr p io ".include"
  else
    show_default io ii

/--
Julia source: base/show.jl:3548-3555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ei::Core.EvalInto)
    if getglobal(ei.m, :eval) === ei
        print(io, ei.m)
        print(io, ".eval")
    else
        show_default(io, ei)
    end
end
```
-/
def show_EvalInto {EI Mod : Type} (p : IOPrims m Io V) (isSelf : EI → m Bool) (modOf : EI → Mod)
    (printMod : JIO Io V → Mod → m Unit) (show_default : JIO Io V → EI → m Unit) (io : JIO Io V) (ei : EI) :
    m Unit := do
  if ← isSelf ei then
    printMod io (modOf ei)
    printStr p io ".eval"
  else
    show_default io ei

structure DisplayReflection (World D Name Mod Ptr GlobalRef Binding Partition Method Repl : Type) where
  runtime : JuliaLean.base.runtime_internals.TypeOps World Ty D Name Mod Ptr Sym
  bindings : JuliaLean.base.runtime_internals.BindingOps World Mod Sym GlobalRef Binding Partition Ty
  liftRuntime : {A : Type} → JuliaLean.base.io.M World A → m A
  singletonName : Name → Sym
  nameModuleDefined : Name → Bool
  isDefinedGlobal : Mod → Sym → m Bool
  getGlobal : Mod → Sym → m Ty
  isConst : Mod → Sym → m Bool
  isDeprecated : Mod → Sym → m Bool
  moduleOps : ModuleOps Mod
  mainModule : Mod
  baseModule : Mod
  coreModule : Mod
  usesBaseOnly : Mod
  contextModule : V → m Mod
  methods : Ty → m (List Method)
  isIntrinsic : Ty → Bool
  isBuiltin : Ty → Bool
  intrinsicId : Ty → JInt .i32
  stringInt32 : JInt .i32 → m String
  stringInt : JInt64 → m String
  stringValue : Ty → m String
  showValue : JIO Io V → Ty → m Unit
  printValue : JIO Io V → Ty → m Unit
  printModule : JIO Io V → Mod → m Unit
  pureContext : m Bool
  activeRepl : m (Option Repl)
  activeReplModuleLatest : Repl → m Mod

def displayDatatype {World D Name Mod Ptr GlobalRef Binding Partition Method Repl : Type}
    (o : DisplayReflection (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl)
    (value : Ty) : m D :=
  match o.runtime.asDatatype value with
  | none => throwShow .typeError
  | some value => pure value

/--
Julia source: base/show.jl:41-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _isself(ft::DataType)
    ftname = ft.name
    name = ftname.singletonname
    ftname.name === name && return false
    mod = parentmodule(ft)
    bpart = lookup_binding_partition(tls_world_age(), GlobalRef(mod, name))
    if binding_kind(bpart) == PARTITION_KIND_BACKDATED_CONST
        # Read the constant directly, since `getglobal` would warn about (or with
        # `--depwarn=error`, refuse) accessing it from a world prior to its definition
        return ft === typeof(partition_restriction(bpart))
    end
    return isdefinedglobal(mod, name) && ft === typeof(getglobal(mod, name))
end
```
-/
def _isself {World D Name Mod Ptr GlobalRef Binding Partition Method Repl : Type}
    (o : DisplayReflection (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl)
    (ft : D) : m Bool := do
  let r := o.runtime
  let name := r.nameOf ft
  let singleton := o.singletonName name
  if r.name name == singleton then return false
  let module := r.module name
  let world ← o.liftRuntime o.bindings.tlsWorldAge
  let gr ← o.liftRuntime (o.bindings.globalRef module singleton)
  let partition ← o.liftRuntime (JuliaLean.base.runtime_internals.lookupBindingPartitionGlobalRef o.bindings world gr)
  let kind := JuliaLean.base.runtime_internals.bindingKindPartition o.bindings partition
  if kind.val == 11 then
    let value ← o.liftRuntime (JuliaLean.base.runtime_internals.partitionRestriction o.bindings partition)
    return r.egal (r.datatypeValue ft) (r.datatypeValue (r.typeof value))
  if !(← o.isDefinedGlobal module singleton) then return false
  let value ← o.getGlobal module singleton
  return r.egal (r.datatypeValue ft) (r.datatypeValue (r.typeof value))

/--
Julia source: base/show.jl:55-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", f::Function)
    get(io, :compact, false)::Bool && return show(io, f)
    ft = typeof(f)
    name = ft.name.singletonname
    if isa(f, Core.IntrinsicFunction)
        print(io, f)
        id = Core.Intrinsics.bitcast(Int32, f)
        print(io, " (intrinsic function #$id)")
    elseif isa(f, Core.Builtin)
        print(io, name, " (built-in function)")
    else
        n = length(methods(f))
        m = n==1 ? "method" : "methods"
        sname = string(name)
        ns = (_isself(ft) || '#' in sname) ? sname : string("(::", ft, ")")
        what = startswith(ns, '@') ? "macro" : "generic function"
        print(io, ns, " (", what, " with $n $m)")
    end
end
```
-/
def show_textplain_Function {World D Name Mod Ptr GlobalRef Binding Partition Method Repl : Type}
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : DisplayReflection (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl)
    (io : JIO Io V) (f : Ty) : m Unit := do
  if ← assertBool a (getIO p io "compact" false) then return ← o.showValue io f
  let ft := o.runtime.typeof f
  let name := o.singletonName (o.runtime.nameOf ft)
  if o.isIntrinsic f then
    o.printValue io f
    printStr p io (" (intrinsic function #" ++ (← o.stringInt32 (o.intrinsicId f)) ++ ")")
  else if o.isBuiltin f then
    printStr p io name
    printStr p io " (built-in function)"
  else
    let methods ← o.methods f
    let n := i64 methods.length
    let method := if n.val == 1 then "method" else "methods"
    let simple ← if ← _isself o ft then pure true else pure (name.contains '#')
    let display ← if simple then pure name
      else pure ("(::" ++ (← o.stringValue (o.runtime.datatypeValue ft)) ++ ")")
    let what := if display.startsWith "@" then "macro" else "generic function"
    printStr p io display
    printStr p io " ("
    printStr p io what
    printStr p io (" with " ++ (← o.stringInt n) ++ " " ++ method ++ ")")

/--
Julia source: base/show.jl:570-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function active_module()
    if ccall(:jl_is_in_pure_context, Bool, ())
        error("active_module() should not be called from a pure context")
    end
    if !@isdefined(active_repl) || active_repl === nothing
        return Main
    end
    return invokelatest(active_module, active_repl)::Module
end
```
-/
def active_module {World D Name Mod Ptr GlobalRef Binding Partition Method Repl : Type}
    (o : DisplayReflection (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl) : m Mod := do
  if ← o.pureContext then
    throwShow (.errorException "active_module() should not be called from a pure context")
  match ← o.activeRepl with
  | none => return o.mainModule
  | some repl => return ← o.activeReplModuleLatest repl

/--
Julia source: base/show.jl:617-620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_without_params(@nospecialize(x))
    b = unwrap_unionall(x)
    return isa(b, DataType) && b.name.wrapper === x
end
```
-/
def print_without_params {World D Name Mod Ptr GlobalRef Binding Partition Method Repl : Type}
    (o : DisplayReflection (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl)
    (x : Ty) : Bool :=
  match o.runtime.asDatatype (o.runtime.unwrap x) with
  | none => false
  | some dt => o.runtime.egal (o.runtime.wrapper (o.runtime.nameOf dt)) x

structure OptionsDisplayOps (Options Value BytePtr CommandsPtr : Type) where
  fields : m (List Sym)
  get : Options → JInt64 → m Value
  bytePointer : Value → Option BytePtr
  commandsPointer : Value → Option CommandsPtr
  nullBytePointer : BytePtr → Bool
  unsafeString : BytePtr → m Bytes
  unsafeLoadCommands : CommandsPtr → m Value
  stringValue : Bytes → Value
  repr : Value → m String

/--
Julia source: base/show.jl:278-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", opt::JLOptions)
    println(io, "JLOptions(")
    fields = fieldnames(JLOptions)
    nfields = length(fields)
    for (i, f) in enumerate(fields)
        v = getfield(opt, i)
        if isa(v, Ptr{UInt8})
            v = (v != C_NULL) ? unsafe_string(v) : ""
        elseif isa(v, Ptr{Ptr{UInt8}})
            v = unsafe_load_commands(v)
        end
        println(io, "  ", f, " = ", repr(v), i < nfields ? "," : "")
    end
    print(io, ")")
end
```
-/
def show_textplain_JLOptions {Options Value BytePtr CommandsPtr : Type}
    (p : IOPrims m Io V) (o : OptionsDisplayOps (m := m) Options Value BytePtr CommandsPtr)
    (io : JIO Io V) (options : Options) : m Unit := do
  printStr p io "JLOptions("
  printStr p io "\n"
  let fields ← o.fields
  for (field, index) in fields.zipIdx do
    let value ← o.get options (i64 (index + 1))
    let value ← match o.bytePointer value with
      | some pointer =>
        if o.nullBytePointer pointer then pure (o.stringValue [])
        else do pure (o.stringValue (← o.unsafeString pointer))
      | none => match o.commandsPointer value with
        | some pointer => o.unsafeLoadCommands pointer
        | none => pure value
    printStr p io "  "
    printStr p io field
    printStr p io " = "
    printStr p io (← o.repr value)
    printStr p io (if index + 1 < fields.length then "," else "")
    printStr p io "\n"
  printStr p io ")"


inductive AliasEnvEntry (T : Type) where
  | value (value : T)
  | vector (values : List T)

structure TypeDisplayOps (World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type) where
  reflection : DisplayReflection (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl
  types : TypeOps m Ty
  unionall : Ty → Option (Ty × Ty)
  variableName : Ty → Sym
  variableLower : Ty → Ty
  variableUpper : Ty → Ty
  typevarContext : V → Option Ty
  ofValue : Ty → V
  hasTypevar : Ty → Ty → Bool
  hasFreeTypevars : Ty → Bool
  freeTypevars : Ty → m (List Ty)
  rewrapFreeTypevars : Ty → List Ty → m Ty
  rewrapUnionall : Ty → Ty → m Ty
  makeVariable : Sym → Ty → Ty → m Ty
  makeUnionall : Ty → Ty → m Ty
  applyType : Ty → List Ty → m Ty
  intersectEnv : Ty → Ty → m (Ty × Option (List (AliasEnvEntry Ty)))
  structsEquivalent : Ty → Ty → m (JInt .i32)
  unsortedNames : Mod → m (List Sym)
  globalRefModule : GlobalRef → Mod
  globalRefName : GlobalRef → Sym
  newModuleSet : m ModuleSet
  insertModule : ModuleSet → Mod → m Unit
  replaceModule : ModuleSet → Mod → Mod → m Unit
  moduleMembers : ModuleSet → m (List Mod)
  moduleContains : ModuleSet → Mod → m Bool
  bindingSame : Binding → Binding → Bool
  restrictionBinding : Ty → m Binding
  rawRestriction : Partition → Ty
  bindingPartitions : Binding → m (Option Partition)
  atomicNextPartition : Partition → m (Sum Partition Binding)
  minWorld : Partition → JInt .u64
  atomicMaxWorld : Partition → m (JInt .u64)
  concreteType : Ty → m Bool
  isa : Ty → Ty → m Bool
  datatypeName : Name
  unionallName : Name
  unionallType : Ty
  pairsName : Name
  symbolType : Ty
  nothingType : Ty
  elementType : Ty → m Ty
  unionTypes : Ty → m (List Ty)
  unionLength : Ty → m JInt64
  makeUnion : Ty → Ty → m Ty
  varargLength : Ty → Option Ty
  intValue : Ty → Option JInt64
  intOfValue : JInt64 → Ty
  appendCounter : Sym → JInt64 → m Sym
  moduleArgument : V → m (Option Mod)
  quotedSymbols : List Sym
  identifierStart : Char → Bool
  printSymbol : JIO Io V → Sym → m Unit
  printInt : JIO Io V → JInt64 → m Unit
  printWorldRange : JIO Io V → JInt64 × JInt64 → m Unit
  showModule : JIO Io V → Mod → m Unit
  styled : PrintStyled m Io V

def displayAt {A : Type} (values : List A) (index : Nat) : m A :=
  match values[index]? with
  | none => throwShow (.jl .boundsError)
  | some value => pure value

def displayIsvisibleLoop {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (parent origin : Binding) : m Bool := do
  if o.bindingSame origin parent then return true
  let r := o.reflection
  let world ← r.liftRuntime r.bindings.tlsWorldAge
  let partition ← r.liftRuntime (JuliaLean.base.runtime_internals.lookupBindingPartition r.bindings world origin)
  let kind := JuliaLean.base.runtime_internals.bindingKindPartition r.bindings partition
  if JuliaLean.base.runtime_internals.isSomeExplicitImported kind then
    let value ← r.liftRuntime (JuliaLean.base.runtime_internals.partitionRestriction r.bindings partition)
    let origin ← o.restrictionBinding value
    displayIsvisibleLoop o parent origin
  else
    let pw ← r.liftRuntime r.bindings.tlsWorldAge
    let pp ← r.liftRuntime (JuliaLean.base.runtime_internals.lookupBindingPartition r.bindings pw parent)
    let fw ← r.liftRuntime r.bindings.tlsWorldAge
    let fp ← r.liftRuntime (JuliaLean.base.runtime_internals.lookupBindingPartition r.bindings fw origin)
    if JuliaLean.base.runtime_internals.isDefinedConstBinding (JuliaLean.base.runtime_internals.bindingKindPartition r.bindings pp) &&
        JuliaLean.base.runtime_internals.isDefinedConstBinding (JuliaLean.base.runtime_internals.bindingKindPartition r.bindings fp) then
      return r.runtime.egal (o.rawRestriction pp) (o.rawRestriction fp)
    return false
partial_fixpoint

/--
Julia source: base/show.jl:1154-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Check whether 'sym' (defined in module 'parent') is visible from module 'from'
# If an object with this name exists in 'from', we need to check that it's the same binding
# and that it's not deprecated.
# `@constprop :none` so concrete-eval doesn't bake binding edges (often on `Main.sym`)
# into the show machinery, where any rebinding of the name would invalidate it (#61667)
@constprop :none function isvisible(sym::Symbol, parent::Module, from::Module)
    isdeprecated(parent, sym) && return false
    isdefinedglobal(from, sym) || return false
    isdefinedglobal(parent, sym) || return false
    parent_binding = convert(Core.Binding, GlobalRef(parent, sym))
    from_binding = convert(Core.Binding, GlobalRef(from, sym))
    while true
        from_binding === parent_binding && return true
        partition = lookup_binding_partition(tls_world_age(), from_binding)
        is_some_explicit_imported(binding_kind(partition)) || break
        from_binding = partition_restriction(partition)::Core.Binding
    end
    parent_partition = lookup_binding_partition(tls_world_age(), parent_binding)
    from_partition = lookup_binding_partition(tls_world_age(), from_binding)
    if is_defined_const_binding(binding_kind(parent_partition)) && is_defined_const_binding(binding_kind(from_partition))
        return parent_partition.restriction === from_partition.restriction
    end
    return false
end
```
-/
def isvisible {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (symbol : Sym) (parent origin : Mod) : m Bool := do
  let r := o.reflection
  if ← r.isDeprecated parent symbol then return false
  if !(← r.isDefinedGlobal origin symbol) then return false
  if !(← r.isDefinedGlobal parent symbol) then return false
  let pg ← r.liftRuntime (r.bindings.globalRef parent symbol)
  let pb ← r.liftRuntime (JuliaLean.base.runtime_internals.convertBinding r.bindings pg)
  let fg ← r.liftRuntime (r.bindings.globalRef origin symbol)
  let fb ← r.liftRuntime (JuliaLean.base.runtime_internals.convertBinding r.bindings fg)
  displayIsvisibleLoop o pb fb

/--
Julia source: base/show.jl:1179-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_global_function(tn::Core.TypeName, globname::Union{Symbol,Nothing})
    if globname !== nothing && isconcretetype(tn.wrapper) && tn !== DataType.name # ignore that typeof(DataType)===DataType, since it is valid but not useful
        globname_str = string(globname::Symbol)
        if '#' ∉ globname_str && '@' ∉ globname_str && isdefined(tn, :module) &&
                isdefinedglobal(tn.module, globname) && isconst(tn.module, globname) &&
                isa(getglobal(tn.module, globname), tn.wrapper)
            return true
        end
    end
    return false
end
```
-/
def is_global_function {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (name : Name) (globalName : Option Sym) : m Bool := do
  let r := o.reflection
  let some globalName := globalName | return false
  if !(← o.concreteType (r.runtime.wrapper name)) then return false
  if r.runtime.egalName name o.datatypeName then return false
  if globalName.contains '#' || globalName.contains '@' then return false
  if !r.nameModuleDefined name then return false
  let module := r.runtime.module name
  if !(← r.isDefinedGlobal module globalName) then return false
  if !(← r.isConst module globalName) then return false
  o.isa (← r.getGlobal module globalName) (r.runtime.wrapper name)

def checkWorldPartition {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (name : Name) (partition : Partition) : m (Option (JInt64 × JInt64)) := do
  let r := o.reflection
  if JuliaLean.base.runtime_internals.isDefinedConstBinding (JuliaLean.base.runtime_internals.bindingKindPartition r.bindings partition) then
    let value ← r.liftRuntime (JuliaLean.base.runtime_internals.partitionRestriction r.bindings partition)
    if r.runtime.isAType value then
      if ← o.types.subtype value (r.runtime.wrapper name) then
        let maxWorld ← o.atomicMaxWorld partition
        if maxWorld.val == 18446744073709551615 then return none
        let minWorld := o.minWorld partition
        let low ← ofJl (JuliaLean.base.int.convert .i64 minWorld)
        let high ← ofJl (JuliaLean.base.int.convert .i64 maxWorld)
        return some (low, high)
  match ← o.atomicNextPartition partition with
  | .inr _ => return none
  | .inl next => checkWorldPartition o name next
partial_fixpoint

/--
Julia source: base/show.jl:1191-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_world_bounded(tn::Core.TypeName)
    bnd = ccall(:jl_get_module_binding, Ref{Core.Binding}, (Any, Any, Cint), tn.module, tn.name, true)
    isdefined(bnd, :partitions) || return nothing
    partition = @atomic bnd.partitions
    while true
        if is_defined_const_binding(binding_kind(partition))
            cval = partition_restriction(partition)
            if isa(cval, Type) && cval <: tn.wrapper
                max_world = @atomic partition.max_world
                max_world == typemax(UInt) && return nothing
                return Int(partition.min_world):Int(max_world)
            end
        end
        next = @atomic partition.next
        # The last partition's `next` is a backreference to the owning Binding.
        next isa Core.BindingPartition || return nothing
        partition = next
    end
end
```
-/
def check_world_bounded {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (name : Name) : m (Option (JInt64 × JInt64)) := do
  let r := o.reflection
  let binding ← r.liftRuntime (r.bindings.getBinding (r.runtime.module name) (r.runtime.name name) (JInt.wrap .i32 1))
  let some partition ← o.bindingPartitions binding | return none
  checkWorldPartition o name partition

/--
Julia source: base/show.jl:1211-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_type_name(io::IO, tn::Core.TypeName)
    if tn === UnionAll.name
        # by coincidence, `typeof(Type)` is a valid representation of the UnionAll type.
        # intercept this case and print `UnionAll` instead.
        return print(io, "UnionAll")
    end
    globname = tn.singletonname
    globfunc = is_global_function(tn, globname)
    sym = (globfunc ? globname : tn.name)::Symbol
    globfunc && print(io, "typeof(")
    quo = false
    world = check_world_bounded(tn)
    world !== nothing && print(io, "@world(")
    if !(get(io, :compact, false)::Bool)
        # Print module prefix unless type is visible from module passed to
        # IOContext If :module is not set, default to Main.
        # nothing can be used to force printing prefix
        from = get(io, :module, Main)
        if isdefined(tn, :module) && (from === nothing || !isvisible(sym, tn.module, from::Module))
            show(io, tn.module)
            print(io, ".")
            if globfunc && !is_id_start_char(first(string(sym)))
                print(io, ':')
                if sym in quoted_syms
                    print(io, '(')
                    quo = true
                end
            end
        end
    end
    show_sym(io, sym)
    world !== nothing && print(io, ", ", world, ")")
    quo      && print(io, ")")
    globfunc && print(io, ")")
    nothing
end
```
-/
def show_type_name {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : JIO Io V) (name : Name) : m Unit := do
  let r := o.reflection
  if r.runtime.egalName name o.unionallName then return ← printStr p io "UnionAll"
  let globalName := r.singletonName name
  let globalFunction ← is_global_function o name (some globalName)
  let symbol := if globalFunction then globalName else r.runtime.name name
  if globalFunction then printStr p io "typeof("
  let mut quote := false
  let world ← check_world_bounded o name
  if world.isSome then printStr p io "@world("
  if !(← assertBool a (getIO p io "compact" false)) then
    let origin := getIO p io "module" r.mainModule
    if r.nameModuleDefined name then
      let qualify ← match origin with
        | .inr origin => do pure (!(← isvisible o symbol (r.runtime.module name) origin))
        | .inl value => do
          let origin ← o.moduleArgument value
          match origin with
          | none => pure true
          | some origin => do pure (!(← isvisible o symbol (r.runtime.module name) origin))
      if qualify then
        o.showModule io (r.runtime.module name)
        printStr p io "."
        if globalFunction then
          let first ← match symbol.toList.head? with
            | none => throwShow (.jl .boundsError)
            | some first => pure first
          if !o.identifierStart first then
            printStr p io ":"
            if o.quotedSymbols.contains symbol then
              printStr p io "("
              quote := true
  o.printSymbol io symbol
  if let some world := world then
    printStr p io ", "
    o.printWorldRange io world
    printStr p io ")"
  if quote then printStr p io ")"
  if globalFunction then printStr p io ")"

def modulesofValue {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (modules : ModuleSet) (value : Ty) : m ModuleSet := do
  let r := o.reflection
  if r.runtime.isTypeVar value then
    return ← modulesofValue o modules (o.variableUpper value)
  let value := r.runtime.unwrap value
  if let some dt := r.runtime.asDatatype value then
    o.insertModule modules (r.runtime.module (r.runtime.nameOf dt))
  else if r.runtime.isTypeEq value then
    let parameter ← r.liftRuntime (r.runtime.typeParameter value)
    if r.runtime.isAType parameter || r.runtime.isTypeVar parameter then
      let _ ← modulesofValue o modules parameter
  else if r.runtime.isTypeEgal value then
    let parameter ← r.liftRuntime (r.runtime.typeParameter value)
    let _ ← modulesofValue o modules parameter
  else if let some (left, right) := r.runtime.asUnion value then
    let _ ← modulesofValue o modules left
    let _ ← modulesofValue o modules right
  return modules
partial_fixpoint

/--
Julia source: base/show.jl:632-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
modulesof!(s::Set{Module}, x::TypeVar) = modulesof!(s, x.ub)
```
-/
def modulesof_TypeVar {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (modules : ModuleSet) (value : Ty) : m ModuleSet := modulesofValue o modules (o.variableUpper value)

/--
Julia source: base/show.jl:633-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function modulesof!(s::Set{Module}, x::TypeEq)
    p = type_parameter(x)
    # the parameter may be a non-type value, e.g. `Type{1}` (#62897)
    p isa Union{Core.AnyType,TypeVar} ? modulesof!(s, p) : s
end
```
-/
def modulesof_TypeEq {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (modules : ModuleSet) (value : Ty) : m ModuleSet := do
  let r := o.reflection
  let parameter ← r.liftRuntime (r.runtime.typeParameter value)
  if r.runtime.isAType parameter || r.runtime.isTypeVar parameter then modulesofValue o modules parameter
  else pure modules

/--
Julia source: base/show.jl:638-638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
modulesof!(s::Set{Module}, x::Core.TypeEgal) = modulesof!(s, type_parameter(x))
```
-/
def modulesof_TypeEgal {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (modules : ModuleSet) (value : Ty) : m ModuleSet := do
  let parameter ← o.reflection.liftRuntime (o.reflection.runtime.typeParameter value)
  modulesofValue o modules parameter

/--
Julia source: base/show.jl:639-652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function modulesof!(s::Set{Module}, x::Type)
    x = unwrap_unionall(x)
    if x isa DataType
        push!(s, parentmodule(x))
    elseif x isa TypeEq
        modulesof!(s, x)
    elseif x isa Core.TypeEgal
        modulesof!(s, x)
    elseif x isa Union
        modulesof!(s, x.a)
        modulesof!(s, x.b)
    end
    s
end
```
-/
def modulesof_Type {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (modules : ModuleSet) (value : Ty) : m ModuleSet := modulesofValue o modules value

/--
Julia source: base/show.jl:654-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function has_other_free_typevars(@nospecialize(x), free_before)
    has_free_typevars(x) || return false
    for v in find_free_typevars(x)
        seen = false
        for p in free_before
            if p === v
                seen = true
                break
            end
        end
        seen || return true
    end
    return false
end
```
-/
def has_other_free_typevars {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (x : Ty) (before : List Ty) : m Bool := do
  if !o.hasFreeTypevars x then return false
  for binder in ← o.freeTypevars x do
    let mut seen := false
    for previous in before do
      if o.reflection.runtime.egal previous binder then
        seen := true
        break
    if !seen then return true
  return false

/--
Julia source: base/show.jl:669-684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return a copy of the type alias `alias` with every bounded binder replaced by
# an unbounded one, so that `typeintersect_env` can match an open `x` (whose free
# typevars are not yet known to satisfy the alias' bounds) against the alias.
# The binders are rewritten from the innermost outward, so that a bound that
# references an outer binder is rewritten consistently with that binder.
function unbounded_typealias(@nospecialize(alias))
    alias isa UnionAll || return alias
    body = unbounded_typealias(alias.body)
    var = alias.var
    if var.lb === Union{} && var.ub === Any
        body === alias.body && return alias
        return UnionAll(var, body)
    end
    newvar = TypeVar(var.name)
    return UnionAll(newvar, UnionAll(var, body){newvar})
end
```
-/
def unbounded_typealias {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (alias : Ty) : m Ty := do
  let some (binder, oldBody) := o.unionall alias | return alias
  let body ← unbounded_typealias o oldBody
  let r := o.reflection.runtime
  if r.egal (o.variableLower binder) r.bottom && r.egal (o.variableUpper binder) r.any then
    if r.egal body oldBody then return alias
    return ← o.makeUnionall binder body
  let newVariable ← o.makeVariable (o.variableName binder) r.bottom r.any
  let quantified ← o.makeUnionall binder body
  let applied ← o.applyType quantified [newVariable]
  o.makeUnionall newVariable applied
partial_fixpoint

/--
Julia source: base/show.jl:686-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Reconstruct the closed type that the (possibly open) `x` is a piece of, by
# re-wrapping it in the typevars bound by the surrounding printing context (the
# `:unionall_env` entries of `io`). Subtype tests use this so that the
# context-bound typevars are quantified rather than treated as rigid free
# variables, while the rest of the alias machinery keeps operating on the open
# `x` whose free typevars must be matched against the alias' parameters.
function reapply_unionall_env(io::Union{IO,Nothing}, @nospecialize(x))
    if io isa IOContext
        for (key, val) in io.dict
            if key === :unionall_env && val isa TypeVar
                x = UnionAll(val, x)
            end
        end
    end
    return x
end
```
-/
def reapply_unionall_env {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : Option (JIO Io V)) (x : Ty) : m Ty := do
  let mut x := x
  if let some (.context context) := io then
    for (key, value) in context.dict do
      if key == "unionall_env" then
        if let some binder := o.typevarContext value then
          x ← o.makeUnionall binder x
  return x

def aliasEnvironmentValues (entries : List (AliasEnvEntry Ty)) : m (List Ty) := do
  entries.mapM fun entry => match entry with
    | .value value => pure value
    | .vector values => displayAt values 0

/--
Julia source: base/show.jl:703-767 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_typealias(@nospecialize(x::Type), io::Union{IO,Nothing}=nothing)
    Any === x && return nothing
    x <: Tuple && return nothing
    mods = modulesof!(Set{Module}(), x)
    replace!(mods, Core=>Base)
    properx = reapply_unionall_env(io, x)
    aliases = Tuple{GlobalRef,SimpleVector}[]
    for mod in mods
        for name in unsorted_names(mod)
            if isdefinedglobal(mod, name) && !isdeprecated(mod, name) && isconst(mod, name)
                alias = getglobal(mod, name)
                if alias isa Type && !has_free_typevars(alias) && !print_without_params(alias) && properx <: alias
                    if alias isa UnionAll
                        free_before = find_free_typevars(x)
                        (_ti, env) = typeintersect_env(x, unbounded_typealias(alias))
                        # ti === Union{} && continue # impossible, since we already checked that x <: alias
                        env = env::SimpleVector
                        # unwrap `svec(tvar, constrained)` env markers down to the TypeVar
                        env = Core.svec(Any[e isa SimpleVector ? e[1] : e for e in env]...)
                        # TODO: In some cases (such as the following), the `env` is over-approximated.
                        #       We'd like to disable `fix_inferred_var_bound` since we'll already do that fix-up here.
                        #       (or detect and reverse the computation of it here).
                        #   T = Array{Array{T,1}, 1} where T
                        #   (ti, env) = ccall(:jl_type_intersection_with_env, Any, (Any, Any), T, Vector)
                        #   env[1].ub.var == T.var
                        applied = try
                                # this can fail if `x` contains a covariant
                                # union, and the non-matching branch of the
                                # union has additional restrictions on the
                                # bounds of the environment that are not met by
                                # the instantiation found above
                                alias{env...}
                            catch ex
                                ex isa TypeError || rethrow()
                                continue
                            end
                        applied = rewrap_free_typevars(applied, free_before)
                        has_other_free_typevars(applied, free_before) && continue
                        applied == x || continue # it couldn't figure out the parameter matching
                    elseif alias === x
                        env = Core.svec()
                    else
                        continue # not a complete match
                    end
                    push!(aliases, (GlobalRef(mod, name), env))
                end
            end
        end
    end
    if length(aliases) > 1
        # Compare the original aliases, before applying their parameters.
        # Equivalent or incomparable aliases remain ambiguous.
        candidates = aliases
        aliases = filter(candidates) do (name, _)
            alias = getglobal(name.mod, name.name)
            !any(candidates) do (other_name, _)
                other = getglobal(other_name.mod, other_name.name)
                other <: alias && !(alias <: other)
            end
        end
    end
    if length(aliases) == 1
        return aliases[1]
    end
end
```
-/
def make_typealias {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (x : Ty) (io : Option (JIO Io V) := none) : m (Option (GlobalRef × List Ty)) := do
  let r := o.reflection
  if r.runtime.egal r.runtime.any x then return none
  if ← o.types.subtype x o.types.tuple then return none
  let modules ← modulesof_Type o (← o.newModuleSet) x
  o.replaceModule modules r.coreModule r.baseModule
  let proper ← reapply_unionall_env o io x
  let mut aliases : List (GlobalRef × List Ty) := []
  for module in ← o.moduleMembers modules do
    for name in ← o.unsortedNames module do
      if ← r.isDefinedGlobal module name then
        if !(← r.isDeprecated module name) then
          if ← r.isConst module name then
            let alias ← r.getGlobal module name
            if ← (if r.runtime.isAType alias && !o.hasFreeTypevars alias && !print_without_params r alias then
                o.types.subtype proper alias else pure false) then
              let environment ← match o.unionall alias with
                | some _ => do
                  let before ← o.freeTypevars x
                  let (_, environment) ← o.intersectEnv x (← unbounded_typealias o alias)
                  let some environment := environment | throwShow .typeError
                  let environment ← aliasEnvironmentValues environment
                  let applied ← tryCatchThe ShowError (do pure (some (← o.applyType alias environment))) fun error =>
                    match error with
                    | .typeError => pure none
                    | other => throwShow other
                  match applied with
                  | none => pure none
                  | some applied => do
                    let applied ← o.rewrapFreeTypevars applied before
                    if ← has_other_free_typevars o applied before then return none
                    if !(← o.types.eq applied x) then return none
                    pure (some environment)
                | none => pure (if r.runtime.egal alias x then some [] else none)
              if let some environment := environment then
                let name ← r.liftRuntime (r.bindings.globalRef module name)
                aliases := aliases ++ [(name, environment)]
  if aliases.length > 1 then
    let candidates := aliases
    aliases ← candidates.filterM fun (name, _) => do
      let alias ← r.getGlobal (o.globalRefModule name) (o.globalRefName name)
      let mut dominated := false
      for (otherName, _) in candidates do
        let other ← r.getGlobal (o.globalRefModule otherName) (o.globalRefName otherName)
        if ← (do if ← o.types.subtype other alias then return !(← o.types.subtype alias other) else pure false) then
          dominated := true
          break
      pure (!dominated)
  match aliases with
  | [alias] => pure (some alias)
  | _ => pure none


structure BinderVectorOps (m : Type → Type) (Ty Binders : Type) where
  new : List Ty → m Binders
  length : Binders → m Nat
  get : Binders → Nat → m Ty
  push : Binders → Ty → m Unit
  pushfirst : Binders → Ty → m Unit
  resize : Binders → Nat → m Unit

def displayBinderContext {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : JIO Io V) (binder : Ty) : m (JIO Io V) := do
  return .context (← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (JuliaLean.base.dict.fieldConv V) io ("unionall_env", o.ofValue binder))

/--
Julia source: base/show.jl:771-784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_can_elide(p::TypeVar, wheres::Vector, elide::Int, env::SimpleVector, skip::Int)
    elide == 0 && return false
    wheres[elide] === p || return false
    for i = (elide + 1):length(wheres)
        v = wheres[i]::TypeVar
        has_typevar(v.lb, p) && return false
        has_typevar(v.ub, p) && return false
    end
    for i = eachindex(env)
        i == skip && continue
        has_typevar(env[i], p) && return false
    end
    return true
end
```
-/
def show_can_elide {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (binder : Ty) (wheres : Binders) (elide : Nat) (environment : List Ty) (skip : Nat) : m Bool := do
  if elide == 0 then return false
  if !o.reflection.runtime.egal (← b.get wheres (elide - 1)) binder then return false
  let count ← b.length wheres
  for index in List.range (count - elide) do
    let other ← b.get wheres (elide + index)
    if !o.reflection.runtime.isTypeVar other then throwShow .typeError
    if o.hasTypevar (o.variableLower other) binder then return false
    if o.hasTypevar (o.variableUpper other) binder then return false
  for (value, index) in environment.zipIdx do
    if index == skip then continue
    if o.hasTypevar value binder then return false
  return true

def findDisplayBinder {Binders : Type} (b : BinderVectorOps m Ty Binders)
    (same : Ty → Ty → Bool) (wheres : Binders) (value : Ty) : m Nat := do
  for index in List.range (← b.length wheres) do
    if same (← b.get wheres index) value then return index + 1
  return 0

/--
Julia source: base/show.jl:786-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_typeparams(io::IO, env::SimpleVector, orig::SimpleVector, wheres::Vector)
    n = length(env)
    elide = length(wheres)
    function egal_var(p::TypeVar, @nospecialize o)
        return o isa TypeVar &&
            ccall(:jl_types_struct_equiv, Cint, (Any, Any), p.ub, o.ub) != 0 &&
            ccall(:jl_types_struct_equiv, Cint, (Any, Any), p.lb, o.lb) != 0
    end
    for i = n:-1:1
        p = env[i]
        if p isa TypeVar
            if i == n && egal_var(p, orig[i]) && show_can_elide(p, wheres, elide, env, i)
                n -= 1
                elide -= 1
            elseif p.lb === Union{} && isgensym(p.name) && show_can_elide(p, wheres, elide, env, i)
                elide -= 1
            elseif p.ub === Any && isgensym(p.name) && show_can_elide(p, wheres, elide, env, i)
                elide -= 1
            end
        end
    end
    if n > 0
        print(io, "{")
        for i = 1:n
            p = env[i]
            if p isa TypeVar
                if p.lb === Union{} && something(findfirst(@nospecialize(w) -> w === p, wheres), 0) > elide
                    print(io, "<:")
                    show(io, p.ub)
                elseif p.ub === Any && something(findfirst(@nospecialize(w) -> w === p, wheres), 0) > elide
                    print(io, ">:")
                    show(io, p.lb)
                else
                    show(io, p)
                end
            else
                show(io, p)
            end
            i < n && print(io, ", ")
        end
        print(io, "}")
    end
    resize!(wheres, elide)
    nothing
end
```
-/
def show_typeparams {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (showValue : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (environment original : List Ty) (wheres : Binders) : m Unit := do
  let r := o.reflection.runtime
  let mut n := environment.length
  let mut elide ← b.length wheres
  for index in (List.range environment.length).reverse do
    let value ← displayAt environment index
    if r.isTypeVar value then
      let trailing ← if index + 1 == n then do
        let origin ← displayAt original index
        if ← (do
            if !r.isTypeVar origin then return false
            if (← o.structsEquivalent (o.variableUpper value) (o.variableUpper origin)).val == 0 then return false
            return (← o.structsEquivalent (o.variableLower value) (o.variableLower origin)).val != 0) then
          show_can_elide o b value wheres elide environment index
        else pure false
        else pure false
      if trailing then
        n := n - 1
        elide := elide - 1
      else
        let lower ← if r.egal (o.variableLower value) r.bottom && isgensym (o.variableName value) then
          show_can_elide o b value wheres elide environment index
          else pure false
        if lower then elide := elide - 1
        else
          let upper ← if r.egal (o.variableUpper value) r.any && isgensym (o.variableName value) then
            show_can_elide o b value wheres elide environment index
            else pure false
          if upper then elide := elide - 1
  if n > 0 then
    printStr p io "{"
    for index in List.range n do
      let value ← displayAt environment index
      if r.isTypeVar value then
        let lower ← if r.egal (o.variableLower value) r.bottom then do
          pure (decide ((← findDisplayBinder b r.egal wheres value) > elide))
          else pure false
        if lower then
          printStr p io "<:"
          showValue io (o.variableUpper value)
        else
          let upper ← if r.egal (o.variableUpper value) r.any then do
            pure (decide ((← findDisplayBinder b r.egal wheres value) > elide))
            else pure false
          if upper then
            printStr p io ">:"
            showValue io (o.variableLower value)
          else showValue io value
      else showValue io value
      if index + 1 < n then printStr p io ", "
    printStr p io "}"
  b.resize wheres elide

/--
Julia source: base/show.jl:832-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_typealias_name(io::IO, name::GlobalRef)
    if !(get(io, :compact, false)::Bool)
        # Print module prefix unless alias is visible from module passed to
        # IOContext. If :module is not set, default to Main.
        # nothing can be used to force printing prefix.
        from = get(io, :module, Main)
        if (from === nothing || !isvisible(name.name, name.mod, from))
            show(io, name.mod)
            print(io, ".")
        end
    end
    print(io, name.name)
    return nothing
end
```
-/
def show_typealias_name {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : JIO Io V) (name : GlobalRef) : m Unit := do
  let r := o.reflection
  if !(← assertBool a (getIO p io "compact" false)) then
    let origin := getIO p io "module" r.mainModule
    let qualify ← match origin with
      | .inr origin => do pure (!(← isvisible o (o.globalRefName name) (o.globalRefModule name) origin))
      | .inl value => do
        let origin ← o.moduleArgument value
        match origin with
        | none => pure true
        | some origin => do pure (!(← isvisible o (o.globalRefName name) (o.globalRefModule name) origin))
    if qualify then
      o.showModule io (o.globalRefModule name)
      printStr p io "."
  printStr p io (o.globalRefName name)

def displayAliasBinders {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (wheres : Binders) (value : Ty) : m Unit := do
  match o.unionall value with
  | none => pure ()
  | some (binder, body) =>
    b.push wheres binder
    displayAliasBinders o b wheres body
partial_fixpoint

/--
Julia source: base/show.jl:847-862 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_typealias(io::IO, name::GlobalRef, env::SimpleVector, wheres::Vector)
    show_typealias_name(io, name)
    isempty(env) && return
    io = IOContext(io)
    for p in wheres
        io = IOContext(io, :unionall_env => p)
    end
    orig = getfield(name.mod, name.name)
    vars = TypeVar[]
    while orig isa UnionAll
        push!(vars, orig.var)
        orig = orig.body
    end
    show_typeparams(io, env, Core.svec(vars...), wheres)
    nothing
end
```
-/
def show_typealias_named {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (showValue : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (name : GlobalRef) (environment : List Ty) (wheres : Binders) : m Unit := do
  show_typealias_name p a o io name
  if environment.isEmpty then return
  let mut io := JIO.context (← IOContext_IO p a io)
  for index in List.range (← b.length wheres) do
    io ← displayBinderContext p a o io (← b.get wheres index)
  let original ← o.reflection.getGlobal (o.globalRefModule name) (o.globalRefName name)
  let binders ← b.new []
  displayAliasBinders o b binders original
  let mut original := []
  for index in List.range (← b.length binders) do
    original := original ++ [← b.get binders index]
  show_typeparams p o b showValue io environment original wheres

def makeWheresOuter {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (wheres : Binders) (seen : List Ty) (value : Ty) : m (List Ty) := do
  match o.unionall value with
  | none => pure seen
  | some (binder, body) =>
    let seen ← if seen.any (o.reflection.runtime.egal binder) then pure seen else do
      b.push wheres binder
      pure (seen ++ [binder])
    makeWheresOuter o b wheres seen body
partial_fixpoint

/--
Julia source: base/show.jl:864-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_wheres(io::IO, env::SimpleVector, @nospecialize(x::Type))
    seen = IdSet()
    wheres = TypeVar[]
    # record things printed by the context
    if io isa IOContext
        for (key, val) in io.dict
            if key === :unionall_env && val isa TypeVar && has_typevar(x, val)
                push!(seen, val)
            end
        end
    end
    # record things in x to print outermost
    while x isa UnionAll
        if !(x.var in seen)
            push!(seen, x.var)
            push!(wheres, x.var)
        end
        x = x.body
    end
    # record remaining things in env to print innermost
    for i = length(env):-1:1
        p = env[i]
        if p isa TypeVar && !(p in seen)
            push!(seen, p)
            pushfirst!(wheres, p)
        end
    end
    return wheres
end
```
-/
def make_wheres {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (io : JIO Io V) (environment : List Ty) (x : Ty) : m Binders := do
  let r := o.reflection.runtime
  let mut seen := []
  let wheres ← b.new []
  if let .context context := io then
    for (key, value) in context.dict do
      if key == "unionall_env" then
        if let some binder := o.typevarContext value then
          if o.hasTypevar x binder then seen := seen ++ [binder]
  seen ← makeWheresOuter o b wheres seen x
  for binder in environment.reverse do
    if r.isTypeVar binder && !seen.any (r.egal binder) then
      seen := seen ++ [binder]
      b.pushfirst wheres binder
  return wheres

/--
Julia source: base/show.jl:894-906 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_wheres(io::IO, wheres::Vector{TypeVar})
    isempty(wheres) && return
    io = IOContext(io)
    n = length(wheres)
    for i = 1:n
        p = wheres[i]
        print(io, n == 1 ? " where " : i == 1 ? " where {" : ", ")
        show(io, p)
        io = IOContext(io, :unionall_env => p)
    end
    n > 1 && print(io, "}")
    nothing
end
```
-/
def show_wheres {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (showValue : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (wheres : Binders) : m Unit := do
  if (← b.length wheres) == 0 then return
  let mut io := JIO.context (← IOContext_IO p a io)
  let n ← b.length wheres
  for index in List.range n do
    let binder ← b.get wheres index
    printStr p io (if n == 1 then " where " else if index == 0 then " where {" else ", ")
    showValue io binder
    io ← displayBinderContext p a o io binder
  if n > 1 then printStr p io "}"

/--
Julia source: base/show.jl:908-915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_typealias(io::IO, @nospecialize(x::Type))
    alias = make_typealias(x, io)
    alias === nothing && return false
    wheres = make_wheres(io, alias[2], x)
    show_typealias(io, alias[1], alias[2], wheres)
    show_wheres(io, wheres)
    return true
end
```
-/
def show_typealias {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (showValue : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (value : Ty) : m Bool := do
  let some (name, environment) ← make_typealias o value (some io) | return false
  let wheres ← make_wheres o b io environment value
  show_typealias_named p a o b showValue io name environment wheres
  show_wheres p a o b showValue io wheres
  return true


structure UnionTypeAlias (GlobalRef Ty : Type) where
  name : GlobalRef
  environment : List Ty
  applied : Ty
  unionLength : JInt64
  negativeEnvironmentLength : JInt64

def unionAliasLess {GlobalRef Ty : Type} (left right : UnionTypeAlias GlobalRef Ty) : Bool :=
  left.unionLength.val < right.unionLength.val ||
    (left.unionLength.val == right.unionLength.val && left.negativeEnvironmentLength.val < right.negativeEnvironmentLength.val)

def sortUnionAliases {GlobalRef Ty : Type} (numeric : JuliaLean.base.sort.BracketNumerics)
    (first : UnionTypeAlias GlobalRef Ty) (rest : List (UnionTypeAlias GlobalRef Ty)) : m (List (UnionTypeAlias GlobalRef Ty)) :=
  letI : Inhabited (UnionTypeAlias GlobalRef Ty) := ⟨first⟩
  do
    let values := (first :: rest).toArray
    let sorted ← match JuliaLean.base.sort.sortVectorBang
      (JuliaLean.base.sort.sourceVectorSortOps JuliaLean.base.sort.arrayStorage numeric JuliaLean.base.sort.juliaPivot)
      values .defaultStable (fun a b => .ok (unionAliasLess a b)) () (some true)
        (fun a b => .ok (unionAliasLess a b)) none with
      | .ok sorted => pure sorted
      | .error error => throwShow (.sort error)
    pure sorted.toList

/--
Julia source: base/show.jl:917-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_typealiases(@nospecialize(x::Type))
    aliases = SimpleVector[]
    Any === x && return aliases, Union{}
    x <: Tuple && return aliases, Union{}
    mods = modulesof!(Set{Module}(), x)
    replace!(mods, Core=>Base)
    free_before = find_free_typevars(x)
    xenv = UnionAll[]
    each = Any[]
    for p in uniontypes(unwrap_unionall(x))
        p isa UnionAll && push!(xenv, p)
        push!(each, rewrap_unionall(p, x))
    end
    x isa UnionAll && push!(xenv, x)
    for mod in mods
        for name in unsorted_names(mod)
            if isdefinedglobal(mod, name) && !isdeprecated(mod, name) && isconst(mod, name)
                alias = getglobal(mod, name)
                if alias isa Type && !has_free_typevars(alias) && !print_without_params(alias) && !(alias <: Tuple)
                    (ti, env) = typeintersect_env(x, unbounded_typealias(alias))
                    ti === Union{} && continue
                    # make sure this alias wasn't from an unrelated part of the Union
                    mod2 = modulesof!(Set{Module}(), alias)
                    mod in mod2 || (mod === Base && Core in mod2) || continue
                    env = env::SimpleVector
                    # unwrap `svec(tvar, constrained)` env markers down to the TypeVar
                    env = Core.svec(Any[e isa SimpleVector ? e[1] : e for e in env]...)
                    applied = alias
                    if !isempty(env)
                        applied = try
                                # this can fail if `x` contains a covariant
                                # union, and the non-matching branch of the
                                # union has additional restrictions on the
                                # bounds of the environment that are not met by
                                # the instantiation found above
                                alias{env...}
                            catch ex
                                ex isa TypeError || rethrow()
                                continue
                            end
                    end
                    ul = unionlen(applied)
                    for p in xenv
                        applied = rewrap_unionall(applied, p)
                    end
                    applied = rewrap_free_typevars(applied, free_before)
                    has_other_free_typevars(applied, free_before) && continue
                    applied <: x || continue # parameter matching didn't make a subtype
                    print_without_params(x) && (env = Core.svec())
                    for typ in each # check that the alias also fully subsumes at least component of the input
                        typ isa TypeVar && continue
                        if typ <: applied
                            push!(aliases, Core.svec(GlobalRef(mod, name), env, applied, (ul, -length(env))))
                            break
                        end
                    end
                end
            end
        end
    end
    if isempty(aliases)
        return aliases, Union{}
    end
    sort!(aliases, by = x -> x[4]::Tuple{Int,Int}, rev = true) # heuristic sort by "best" environment
    let applied = Union{}
        applied1 = Union{}
        keep = SimpleVector[]
        prev = (0, 0)
        for alias in aliases
            alias4 = alias[4]::Tuple{Int,Int}
            if alias4[1] < 2
                if !(alias[3] <: applied)
                    applied1 = Union{applied1, alias[3]}
                    push!(keep, alias)
                end
            elseif alias4 == prev || !(alias[3] <: applied)
                applied = applied1 = Union{applied1, alias[3]}
                push!(keep, alias)
                prev = alias4
            end
        end
        return keep, applied1
    end
end
```
-/
def make_typealiases {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (numeric : JuliaLean.base.sort.BracketNumerics) (x : Ty) : m (List (UnionTypeAlias GlobalRef Ty) × Ty) := do
  let r := o.reflection
  if r.runtime.egal r.runtime.any x then return ([], r.runtime.bottom)
  if ← o.types.subtype x o.types.tuple then return ([], r.runtime.bottom)
  let modules ← modulesof_Type o (← o.newModuleSet) x
  o.replaceModule modules r.coreModule r.baseModule
  let before ← o.freeTypevars x
  let mut xenv := []
  let mut each := []
  for part in ← o.unionTypes (r.runtime.unwrap x) do
    if (o.unionall part).isSome then xenv := xenv ++ [part]
    each := each ++ [← o.rewrapUnionall part x]
  if (o.unionall x).isSome then xenv := xenv ++ [x]
  let mut aliases : List (UnionTypeAlias GlobalRef Ty) := []
  for module in ← o.moduleMembers modules do
    for name in ← o.unsortedNames module do
      if ← r.isDefinedGlobal module name then
        if !(← r.isDeprecated module name) then
          if ← r.isConst module name then
            let alias ← r.getGlobal module name
            if ← (if r.runtime.isAType alias && !o.hasFreeTypevars alias && !print_without_params r alias then
                (do return !(← o.types.subtype alias o.types.tuple)) else pure false) then
              let (intersection, environment) ← o.intersectEnv x (← unbounded_typealias o alias)
              if r.runtime.egal intersection r.runtime.bottom then continue
              let related ← modulesof_Type o (← o.newModuleSet) alias
              let inModule ← o.moduleContains related module
              let related ← if inModule then pure true else do
                if r.moduleOps.egal module r.baseModule then o.moduleContains related r.coreModule
                else pure false
              if !related then continue
              let some environment := environment | throwShow .typeError
              let mut environment ← aliasEnvironmentValues environment
              let applied ← if environment.isEmpty then pure (some alias) else
                tryCatchThe ShowError (do pure (some (← o.applyType alias environment))) fun error =>
                  match error with
                  | .typeError => pure none
                  | other => throwShow other
              let some applied := applied | continue
              let length ← o.unionLength applied
              let mut applied := applied
              for part in xenv do applied ← o.rewrapUnionall applied part
              applied ← o.rewrapFreeTypevars applied before
              if ← has_other_free_typevars o applied before then continue
              if !(← o.types.subtype applied x) then continue
              if print_without_params r x then environment := []
              for part in each do
                if r.runtime.isTypeVar part then continue
                if ← o.types.subtype part applied then
                  let name ← r.liftRuntime (r.bindings.globalRef module name)
                  aliases := aliases ++ [⟨name, environment, applied, length, i64 (-(environment.length : Int))⟩]
                  break
  let first :: rest := aliases | return ([], r.runtime.bottom)
  aliases ← sortUnionAliases numeric first rest
  let mut applied := r.runtime.bottom
  let mut appliedOne := r.runtime.bottom
  let mut keep := []
  let mut previous : JInt64 × JInt64 := (i64 0, i64 0)
  for alias in aliases do
    let rank := (alias.unionLength, alias.negativeEnvironmentLength)
    if alias.unionLength.val < 2 then
      if !(← o.types.subtype alias.applied applied) then
        appliedOne ← o.makeUnion appliedOne alias.applied
        keep := keep ++ [alias]
    else if ← (if rank.1.val == previous.1.val && rank.2.val == previous.2.val then pure true
        else do return !(← o.types.subtype alias.applied applied)) then
      appliedOne ← o.makeUnion appliedOne alias.applied
      applied := appliedOne
      keep := keep ++ [alias]
      previous := rank
  return (keep, appliedOne)

/--
Julia source: base/show.jl:1002-1044 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_unionaliases(io::IO, x::Union)
    aliases, applied = make_typealiases(x)
    isempty(aliases) && return false
    first = true
    tvar = false
    for typ in uniontypes(x)
        if isa(typ, TypeVar)
            tvar = true # sort bare TypeVars to the end
            continue
        elseif typ <: applied
            continue
        end
        print(io, first ? "Union{" : ", ")
        first = false
        show(io, typ)
    end
    if first && !tvar && length(aliases) == 1
        alias = aliases[1]
        env = alias[2]::SimpleVector
        wheres = make_wheres(io, env, alias[3])
        show_typealias(io, alias[1], env, wheres)
        show_wheres(io, wheres)
    else
        for alias in aliases
            print(io, first ? "Union{" : ", ")
            first = false
            env = alias[2]::SimpleVector
            wheres = make_wheres(io, env, alias[3])
            show_typealias(io, alias[1], env, wheres)
            show_wheres(io, wheres)
        end
        if tvar
            for typ in uniontypes(x)
                if isa(typ, TypeVar)
                    print(io, ", ")
                    show(io, typ)
                end
            end
        end
        print(io, "}")
    end
    return true
end
```
-/
def show_unionaliases {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (numeric : JuliaLean.base.sort.BracketNumerics)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (x : Ty) : m Bool := do
  let (aliases, applied) ← make_typealiases o numeric x
  if aliases.isEmpty then return false
  let mut first := true
  let mut typevar := false
  for part in ← o.unionTypes x do
    if o.reflection.runtime.isTypeVar part then
      typevar := true
      continue
    if ← o.types.subtype part applied then continue
    printStr p io (if first then "Union{" else ", ")
    first := false
    showValue io part
  if first && !typevar && aliases.length == 1 then
    let alias ← displayAt aliases 0
    let wheres ← make_wheres o b io alias.environment alias.applied
    show_typealias_named p a o b showValue io alias.name alias.environment wheres
    show_wheres p a o b showValue io wheres
  else
    for alias in aliases do
      printStr p io (if first then "Union{" else ", ")
      first := false
      let wheres ← make_wheres o b io alias.environment alias.applied
      show_typealias_named p a o b showValue io alias.name alias.environment wheres
      show_wheres p a o b showValue io wheres
    if typevar then
      for part in ← o.unionTypes x do
        if o.reflection.runtime.isTypeVar part then
          printStr p io ", "
          showValue io part
    printStr p io "}"
  return true

/--
Julia source: base/show.jl:1248-1264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function maybe_kws_nt(x::DataType)
    # manually-written version of
    # x <: (Pairs{Symbol, eltype(NT), Nothing, NT} where NT <: NamedTuple)
    x.name === typename(Pairs) || return nothing
    length(x.parameters) == 4 || return nothing
    x.parameters[1] === Symbol || return nothing
    p4 = x.parameters[4]
    if (isa(p4, DataType) && p4.name === typename(NamedTuple) && length(p4.parameters) == 2)
        syms, types = p4.parameters
        types isa DataType || return nothing
        x.parameters[2] === eltype(p4) || return nothing
        isa(syms, Tuple) || return nothing
        x.parameters[3] === Nothing || return nothing
        return p4
    end
    return nothing
end
```
-/
def maybe_kws_nt {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (x : D) : m (Option D) := do
  let r := o.reflection
  if !r.runtime.egalName (r.runtime.nameOf x) o.pairsName then return none
  let parameters ← r.liftRuntime (r.runtime.parameters x)
  if parameters.length != 4 then return none
  if !r.runtime.egal (← displayAt parameters 0) o.symbolType then return none
  let fourth ← displayAt parameters 3
  let some dt := r.runtime.asDatatype fourth | return none
  if !r.runtime.egalName (r.runtime.nameOf dt) r.runtime.namedTupleName then return none
  let namedParameters ← r.liftRuntime (r.runtime.parameters dt)
  if namedParameters.length != 2 then return none
  let symbols ← displayAt namedParameters 0
  let types ← displayAt namedParameters 1
  if (r.runtime.asDatatype types).isNone then return none
  if !r.runtime.egal (← displayAt parameters 1) (← o.elementType fourth) then return none
  if (r.runtime.symbolTuple symbols).isNone then return none
  if !r.runtime.egal (← displayAt parameters 2) o.nothingType then return none
  return some dt

/--
Julia source: base/show.jl:1362-1376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_at_namedtuple(io::IO, syms::Tuple, types::DataType)
    first = true
    for i in eachindex(syms)
        if !first
            print(io, ", ")
        end
        show_sym(io, syms[i])
        typ = types.parameters[i]
        if typ !== Any
            print(io, "::")
            show(io, typ)
        end
        first = false
    end
end
```
-/
def show_at_namedtuple {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (symbols : List Sym) (types : D) : m Unit := do
  let r := o.reflection
  let mut first := true
  for (symbol, index) in symbols.zipIdx do
    if !first then printStr p io ", "
    o.printSymbol io symbol
    let typ ← r.liftRuntime (r.runtime.parameter types (i64 (index + 1)))
    if !r.runtime.egal typ r.runtime.any then
      printStr p io "::"
      showValue io typ
    first := false

inductive DisplayVarargKind where
  | none
  | fixed
  | bound
  | unbound
  deriving BEq

/--
Julia source: base/show.jl:1266-1360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_datatype(io::IO, x::DataType, wheres::Vector{TypeVar}=TypeVar[])
    parameters = x.parameters::SimpleVector
    istuple = x.name === Tuple.name
    isnamedtuple = x.name === typename(NamedTuple)
    kwsnt = maybe_kws_nt(x)
    n = length(parameters)

    # Print tuple types with homogeneous tails longer than max_n compactly using `NTuple` or `Vararg`
    if istuple
        if n == 0
            print(io, "Tuple{}")
            return
        end

        # find the length of the homogeneous tail
        max_n = 3
        taillen = 1
        pn = parameters[n]
        fulln = n
        vakind = :none
        vaN = 0
        if pn isa Core.TypeofVararg
            if isdefined(pn, :N)
                vaN = pn.N
                if vaN isa Int
                    taillen = vaN
                    fulln += taillen - 1
                    vakind = :fixed
                else
                    vakind = :bound
                end
            else
                vakind = :unbound
            end
            pn = unwrapva(pn)
        end
        if !(pn isa TypeVar || pn isa Type)
            # prefer Tuple over NTuple if it contains something other than types
            # (e.g. if the user has switched the N and T accidentally)
            taillen = 0
        elseif vakind === :none || vakind === :fixed
            for i in (n-1):-1:1
                if parameters[i] === pn
                    taillen += 1
                else
                    break
                end
            end
        end

        # prefer NTuple over Tuple if it is a Vararg without a fixed length
        # and prefer Tuple for short lists of elements
        if (vakind == :bound && n == 1 == taillen) || (vakind === :fixed && taillen == fulln > max_n) ||
           (vakind === :none && taillen == fulln > max_n)
            print(io, "NTuple{")
            vakind === :bound ? show(io, vaN) : print(io, fulln)
            print(io, ", ")
            show(io, pn)
            print(io, "}")
        else
            print(io, "Tuple{")
            headlen = (taillen > max_n ? fulln - taillen : fulln)
            for i = 1:headlen
                i > 1 && print(io, ", ")
                show(io, vakind === :fixed && i >= n ? pn : parameters[i])
            end
            if headlen < fulln
                headlen > 0 && print(io, ", ")
                print(io, "Vararg{")
                show(io, pn)
                print(io, ", ", fulln - headlen, "}")
            end
            print(io, "}")
        end
        return
    elseif isnamedtuple
        syms, types = parameters
        if syms isa Tuple && types isa DataType && length(types.parameters) == length(syms) && !isvatuple(types)
            print(io, "@NamedTuple{")
            show_at_namedtuple(io, syms, types)
            print(io, "}")
            return
        end
    elseif get(io, :backtrace, false)::Bool && kwsnt !== nothing
        # simplify the type representation of keyword arguments
        # when printing signature of keyword method in the stack trace
        print(io, "@Kwargs{")
        show_at_namedtuple(io, kwsnt.parameters[1]::Tuple, kwsnt.parameters[2]::DataType)
        print(io, "}")
        return
    end

    show_type_name(io, x.name)
    show_typeparams(io, parameters, (unwrap_unionall(x.name.wrapper)::DataType).parameters, wheres)
end
```
-/
def show_datatype {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (showValue : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (x : D) (wheres : Binders) : m Unit := do
  let r := o.reflection
  let parameters ← r.liftRuntime (r.runtime.parameters x)
  let name := r.runtime.nameOf x
  let isTuple := r.runtime.egalName name r.runtime.tupleName
  let isNamedTuple := r.runtime.egalName name r.runtime.namedTupleName
  let keywords ← maybe_kws_nt o x
  let n := parameters.length
  if isTuple then
    if n == 0 then return ← printStr p io "Tuple{}"
    let mut tailLength := i64 1
    let mut last ← displayAt parameters (n - 1)
    let mut fullLength := i64 n
    let mut kind := DisplayVarargKind.none
    let mut variableCount := o.intOfValue (i64 0)
    if r.runtime.isVararg last then
      match o.varargLength last with
      | some length =>
        variableCount := length
        match o.intValue variableCount with
        | some length =>
          tailLength := length
          fullLength := i64 (fullLength.val + tailLength.val - 1)
          kind := .fixed
        | none => kind := .bound
      | none => kind := .unbound
      last := r.runtime.unwrapVararg last
    if !(r.runtime.isTypeVar last || r.runtime.isAType last) then
      tailLength := i64 0
    else if kind == .none || kind == .fixed then
      for index in (List.range (n - 1)).reverse do
        if r.runtime.egal (← displayAt parameters index) last then
          tailLength := i64 (tailLength.val + 1)
        else break
    if (kind == .bound && n == 1 && tailLength.val == 1) ||
        ((kind == .fixed || kind == .none) && tailLength.val == fullLength.val && fullLength.val > 3) then
      printStr p io "NTuple{"
      if kind == .bound then showValue io variableCount else o.printInt io fullLength
      printStr p io ", "
      showValue io last
      printStr p io "}"
    else
      printStr p io "Tuple{"
      let headLength := if tailLength.val > 3 then i64 (fullLength.val - tailLength.val) else fullLength
      for index in List.range headLength.val.toNat do
        if index > 0 then printStr p io ", "
        let value ← if kind == .fixed && index + 1 >= n then pure last else displayAt parameters index
        showValue io value
      if headLength.val < fullLength.val then
        if headLength.val > 0 then printStr p io ", "
        printStr p io "Vararg{"
        showValue io last
        printStr p io ", "
        o.printInt io (i64 (fullLength.val - headLength.val))
        printStr p io "}"
      printStr p io "}"
    return
  else if isNamedTuple then
    let symbols ← displayAt parameters 0
    let types ← displayAt parameters 1
    if let some symbols := r.runtime.symbolTuple symbols then
      if let some types := r.runtime.asDatatype types then
        let typesParameters ← r.liftRuntime (r.runtime.parameters types)
        if typesParameters.length == symbols.length && !r.runtime.isVaTuple types then
          printStr p io "@NamedTuple{"
          show_at_namedtuple p o showValue io symbols types
          printStr p io "}"
          return
  else if ← assertBool a (getIO p io "backtrace" false) then
    if let some keywords := keywords then
      printStr p io "@Kwargs{"
      let parameters ← r.liftRuntime (r.runtime.parameters keywords)
      let symbols ← displayAt parameters 0
      let some symbols := r.runtime.symbolTuple symbols | throwShow .typeError
      let types ← displayDatatype r (← displayAt parameters 1)
      show_at_namedtuple p o showValue io symbols types
      printStr p io "}"
      return
  show_type_name p a o io name
  let wrapper ← displayDatatype r (r.runtime.unwrap (r.runtime.wrapper name))
  let original ← r.liftRuntime (r.runtime.parameters wrapper)
  show_typeparams p o b showValue io parameters original wheres

def show_datatype_default {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (showValue : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (x : D) : m Unit := do
  show_datatype p a o b showValue io x (← b.new [])

structure TypeListDisplayOps (V Ty : Type) where
  value : List Ty → V
  egal : V → List Ty → Bool

def typeListIndexOps : IndexOps (List Ty) Ty where
  isassigned := fun values index => 1 ≤ index.val && index.val ≤ values.length
  getindex := fun values index => if 1 ≤ index.val then values[(index.val - 1).toNat]? else none

/--
Julia source: base/show.jl:1071-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_typeegal(io::IO, @nospecialize(x::Core.TypeEgal))
    print(io, "Core.TypeEgal{")
    show(io, type_parameter(x))
    print(io, "}")
end
```
-/
def show_typeegal {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (x : Ty) : m Unit := do
  printStr p io "Core.TypeEgal{"
  showValue io (← o.reflection.liftRuntime (o.reflection.runtime.typeParameter x))
  printStr p io "}"

/--
Julia source: base/show.jl:1087-1095 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `Type{T}` is the familiar user-facing spelling and is used for all normal
# (compact) printing. In non-compact contexts (e.g. the REPL's `text/plain`
# display) the canonical kind name `TypeEq{T}` is shown instead, so that a
# concrete `Type{T}` renders as `Type{T} (alias for TypeEq{T})`.
function show_typeeq(io::IO, @nospecialize(x::TypeEq))
    print(io, get(io, :compact, true)::Bool ? "Type{" : "TypeEq{")
    show(io, type_parameter(x))
    print(io, "}")
end
```
-/
def show_typeeq {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (x : Ty) : m Unit := do
  printStr p io (if ← assertBool a (getIO p io "compact" true) then "Type{" else "TypeEq{")
  showValue io (← o.reflection.liftRuntime (o.reflection.runtime.typeParameter x))
  printStr p io "}"

def displayRenameBinder {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : IOContext Io V) (x binder : Ty) (counter : JInt64) : m (Ty × Ty) := do
  let name ← o.appendCounter (o.variableName binder) counter
  if io_has_tvar_name_IOContext o.typevarContext o.variableName o.hasTypevar io name x then
    displayRenameBinder o io x binder (i64 (counter.val + 1))
  else
    let binder ← o.makeVariable name (o.variableLower binder) (o.variableUpper binder)
    let applied ← o.applyType x [binder]
    return (binder, applied)
partial_fixpoint

def displayQuantifiedBody {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (io : IOContext Io V) (x : Ty) (wheres : Binders) : m (Ty × IOContext Io V) := do
  match o.unionall x with
  | none => pure (x, io)
  | some (binder, body) =>
    let (binder, x) ← if o.variableName binder == "_" ||
        io_has_tvar_name_IOContext o.typevarContext o.variableName o.hasTypevar io (o.variableName binder) x then
        displayRenameBinder o io x binder (i64 1)
      else pure (binder, body)
    b.push wheres binder
    let io ← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (JuliaLean.base.dict.fieldConv V)
      (.context io) ("unionall_env", o.ofValue binder)
    displayQuantifiedBody p a o b io x wheres
partial_fixpoint

/--
Julia source: base/show.jl:1096-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_type(io::IO, @nospecialize(x::Type))
    if x isa Core.TypeEgal
        show_typeegal(io, x)
        return
    elseif print_without_params(x)
        show_type_name(io, (unwrap_unionall(x)::DataType).name)
        return
    elseif get(io, :compact, true)::Bool && show_typealias(io, x)
        return
    elseif x isa TypeEq
        show_typeeq(io, x)
        return
    elseif x isa DataType
        show_datatype(io, x)
        return
    elseif x isa Union
        if get(io, :compact, true)::Bool && show_unionaliases(io, x)
            return
        end
        print(io, "Union")
        show_delim_array(io, uniontypes(x), '{', ',', '}', false)
        return
    elseif x === Union{}
        print(io, "Union{}")
        return
    end

    x = x::UnionAll
    wheres = TypeVar[]
    let io = IOContext(io)
        while x isa UnionAll
            var = x.var
            if var.name === :_ || io_has_tvar_name(io, var.name, x)
                counter = 1
                while true
                    newname = Symbol(var.name, counter)
                    if !io_has_tvar_name(io, newname, x)
                        var = TypeVar(newname, var.lb, var.ub)
                        x = x{var}
                        break
                    end
                    counter += 1
                end
            else
                x = x.body
            end
            push!(wheres, var)
            io = IOContext(io, :unionall_env => var)
        end
        if x isa DataType
            show_datatype(io, x, wheres)
        else
            show(io, x)
        end
    end
    show_wheres(io, wheres)
end
```
-/
def _show_type {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (numeric : JuliaLean.base.sort.BracketNumerics)
    (lists : TypeListDisplayOps V Ty) (showValue : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (x : Ty) : m Unit := do
  let r := o.reflection
  if r.runtime.isTypeEgal x then
    show_typeegal p o showValue io x
    return
  if print_without_params r x then
    let dt ← displayDatatype r (r.runtime.unwrap x)
    show_type_name p a o io (r.runtime.nameOf dt)
    return
  if ← assertBool a (getIO p io "compact" true) then
    if ← show_typealias p a o b showValue io x then return
  if r.runtime.isTypeEq x then
    show_typeeq p a o showValue io x
    return
  if let some dt := r.runtime.asDatatype x then
    show_datatype_default p a o b showValue io dt
    return
  if (r.runtime.asUnion x).isSome then
    if ← assertBool a (getIO p io "compact" true) then
      if ← show_unionaliases p a o b numeric showValue io x then return
    printStr p io "Union"
    let parts ← o.unionTypes x
    show_delim_array_Array p a typeListIndexOps o.styled (fun n => do pure (lit (← r.stringInt n)))
      lists.egal lists.value showValue io parts "{" "," "}" false (i64 1) (i64 parts.length)
    return
  if r.runtime.egal x r.runtime.bottom then
    printStr p io "Union{}"
    return
  if (o.unionall x).isNone then throwShow .typeError
  let wheres ← b.new []
  let context ← IOContext_IO p a io
  let (body, context) ← displayQuantifiedBody p a o b context x wheres
  if let some dt := r.runtime.asDatatype body then
    show_datatype p a o b showValue (.context context) dt wheres
  else showValue (.context context) body
  show_wheres p a o b showValue io wheres

/--
Julia source: base/show.jl:1076-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, @nospecialize(x::Core.AnyType))
    if x isa Core.TypeofBottom
        print(io, "Union{}")
    elseif x isa Core.TypeEgal
        show_typeegal(io, x)
    elseif x isa TypeEq
        show_typeeq(io, x)
    else
        _show_type(io, inferencebarrier(x))
    end
end
```
-/
def show_AnyType {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (numeric : JuliaLean.base.sort.BracketNumerics)
    (lists : TypeListDisplayOps V Ty) (showValue : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (x : Ty) : m Unit := do
  let r := o.reflection.runtime
  if r.egal x r.bottom then printStr p io "Union{}"
  else if r.isTypeEgal x then show_typeegal p o showValue io x
  else if r.isTypeEq x then show_typeeq p a o showValue io x
  else _show_type p a o b numeric lists showValue io x

/--
Julia source: base/show.jl:1046-1069 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", @nospecialize(x::Type))
    if !print_without_params(x)
        if make_typealias(x, io) !== nothing || (unwrap_unionall(x) isa Union && x <: make_typealiases(x)[2])
            show(IOContext(io, :compact => true), x)
            if !(get(io, :compact, false)::Bool)
                printstyled(io, " (alias for "; color = :light_black)
                printstyled(IOContext(io, :compact => false), x, color = :light_black)
                printstyled(io, ")"; color = :light_black)
            end
            return
        end
    end
    show(io, x)
    # give a helpful hint for function types
    if x isa DataType && x !== UnionAll && !(get(io, :compact, false)::Bool)
        tn = x.name::Core.TypeName
        globname = tn.singletonname
        if is_global_function(tn, globname)
            print(io, " (singleton type of function ")
            show_sym(io, globname)
            print(io, ", subtype of Function)")
        end
    end
end
```
-/
def show_textplain_Type {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (numeric : JuliaLean.base.sort.BracketNumerics)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (x : Ty) : m Unit := do
  let r := o.reflection
  if !print_without_params r x then
    let direct ← make_typealias o x (some io)
    let aliased ← if direct.isSome then pure true else do
      if (r.runtime.asUnion (r.runtime.unwrap x)).isSome then
        let (_, applied) ← make_typealiases o numeric x
        o.types.subtype x applied
      else pure false
    if aliased then
      let compact ← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (boolConv a) io ("compact", true)
      showValue (.context compact) x
      if !(← assertBool a (getIO p io "compact" false)) then
        o.styled io [fun target => printStr p target " (alias for "] "light_black" false
        let full ← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (boolConv a) io ("compact", false)
        o.styled (.context full) [fun target => r.printValue target x] "light_black" false
        o.styled io [fun target => printStr p target ")"] "light_black" false
      return
  showValue io x
  if let some dt := r.runtime.asDatatype x then
    if !r.runtime.egal x o.unionallType then
      if !(← assertBool a (getIO p io "compact" false)) then
        let name := r.runtime.nameOf dt
        let globalName := r.singletonName name
        if ← is_global_function o name (some globalName) then
          printStr p io " (singleton type of function "
          o.printSymbol io globalName
          printStr p io ", subtype of Function)"


def show_typevar_bound {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (bound : Ty) : m Unit := do
  let parens := (o.unionall bound).isSome && !print_without_params o.reflection bound
  if parens then printStr p io "("
  if !(o.reflection.runtime.isTypeVar bound || o.reflection.runtime.isAType bound) then throwShow .typeError
  showValue io bound
  if parens then printStr p io ")"

/--
Julia source: base/show.jl:2866-2899 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, tv::TypeVar)
    # If we are in the `unionall_env`, the type-variable is bound
    # and the type constraints are already printed.
    # We don't need to print it again.
    # Otherwise, the lower bound should be printed if it is not `Bottom`
    # and the upper bound should be printed if it is not `Any`.
    in_env = (:unionall_env => tv) in io
    function show_bound(io::IO, @nospecialize(b)) # b::Union{Core.AnyType,TypeVar}
        parens = isa(b,UnionAll) && !print_without_params(b)
        parens && print(io, "(")
        b isa TypeVar ? show(io, b) : show(io, b::Core.AnyType)
        parens && print(io, ")")
        nothing
    end
    lb, ub = tv.lb, tv.ub
    if !in_env && lb !== Bottom
        if ub === Any
            show_unquoted(io, tv.name)
            print(io, ">:")
            show_bound(io, lb)
        else
            show_bound(io, lb)
            print(io, "<:")
            show_unquoted(io, tv.name)
        end
    else
        show_unquoted(io, tv.name)
    end
    if !in_env && ub !== Any
        print(io, "<:")
        show_bound(io, ub)
    end
    nothing
end
```
-/
def show_TypeVar {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet L : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] [MonoTryCatch m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (c : AstOps m Io V L)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (binder : Ty) : m Unit := do
  let r := o.reflection.runtime
  let inEnvironment ← match io with
    | .plain _ => pure false
    | .context context => in_IOContext symEq a.egal ("unionall_env", o.ofValue binder) context
  let lower := o.variableLower binder
  let upper := o.variableUpper binder
  if !inEnvironment && !r.egal lower r.bottom then
    if r.egal upper r.any then
      show_unquoted_2 p a c io (.symbol (o.variableName binder))
      printStr p io ">:"
      show_typevar_bound p o showValue io lower
    else
      show_typevar_bound p o showValue io lower
      printStr p io "<:"
      show_unquoted_2 p a c io (.symbol (o.variableName binder))
  else show_unquoted_2 p a c io (.symbol (o.variableName binder))
  if !inEnvironment && !r.egal upper r.any then
    printStr p io "<:"
    show_typevar_bound p o showValue io upper

/--
Julia source: base/show.jl:2901-2913 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, vm::Core.TypeofVararg)
    print(io, "Vararg")
    if isdefined(vm, :T)
        print(io, "{")
        show(io, vm.T)
        if isdefined(vm, :N)
            print(io, ", ")
            show(io, vm.N)
        end
        print(io, "}")
    end
end

```
-/
def show_TypeofVararg {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (value : Ty) : m Unit := do
  printStr p io "Vararg"
  if ← o.reflection.liftRuntime (o.reflection.runtime.isdefined value "T") then
    printStr p io "{"
    showValue io (o.reflection.runtime.unwrapVararg value)
    if let some length := o.varargLength value then
      printStr p io ", "
      showValue io length
    printStr p io "}"


structure SignatureDisplayOps (m : Type → Type) (Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments : Type) where
  functionType : Ty
  isExported : Mod → Sym → m Bool
  sprintSymbol : JIO Io V → Sym → m Bytes
  sprintValue : JIO Io V → Ty → m Bytes
  newBuffer : m Io
  takeString : Io → m Bytes
  newVariables : m Binders
  showMethodParams : JIO Io V → Binders → m Unit
  bytes : BytesOps m
  string : StrOps Bytes C
  asBoolRef : V → Option BoolRef
  setBoolRef : BoolRef → Bool → m Unit
  displaysize : JIO Io V → m (JInt64 × JInt64)
  pairsNamedTuple : Ty
  keywordFirst : Keywords → m (Option ((Ty × Ty) × KeywordState))
  keywordNext : Keywords → KeywordState → m (Option ((Ty × Ty) × KeywordState))
  argumentLength : Arguments → m JInt64
  argumentGet : Arguments → JInt64 → m Ty
  emptyArgumentName : Ty

def displayDemangleName (name : Sym) : m Sym :=
  demangle_function_name_Symbol (fun (value : String) char => value.splitOn (String.singleton char))
    String.isEmpty id pure name

/--
Julia source: base/show.jl:2618-2644 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# show the called object in a signature, given its type `ft`
# `io` should contain the UnionAll env of the signature
function show_signature_function(io::IO, @nospecialize(ft), demangle=false, fargname="", html=false, qualified=false)
    uw = unwrap_unionall(ft)
    if ft <: Function && isa(uw, DataType) && isempty(uw.parameters) && _isself(uw)
        uwmod = parentmodule(uw)
        if qualified && !isexported(uwmod, uw.name.singletonname) && uwmod !== Main
            print_within_stacktrace(io, uwmod, '.', bold=true)
        end
        s = sprint(show_sym, (demangle ? demangle_function_name : identity)(uw.name.singletonname), context=io)
        print_within_stacktrace(io, s, bold=true)
    elseif isType(ft) && (f = type_parameter(ft); !isa(f, TypeVar))
        uwf = unwrap_unionall(f)
        parens = isa(f, UnionAll) && !(isa(uwf, DataType) && f === uwf.name.wrapper)
        parens && print(io, "(")
        print_within_stacktrace(io, f, bold=true)
        parens && print(io, ")")
    else
        if html
            print(io, "($fargname::<b>", ft, "</b>)")
        else
            print_within_stacktrace(io, "($fargname::", ft, ")", bold=true)
        end
    end
    nothing
end

```
-/
def show_signature_function {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders BoolRef C Keywords KeywordState Arguments : Type}
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (s : SignatureDisplayOps m Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments)
    (io : JIO Io V) (ft : Ty) (demangle : Bool := false) (fargname : Ty := s.emptyArgumentName)
    (html : Bool := false) (qualified : Bool := false) : m Unit := do
  let r := o.reflection
  let unwrapped := r.runtime.unwrap ft
  let isFunction ← o.types.subtype ft s.functionType
  let direct ← if isFunction then do
    match r.runtime.asDatatype unwrapped with
    | none => pure false
    | some dt => do
      let parameters ← r.liftRuntime (r.runtime.parameters dt)
      if parameters.isEmpty then _isself r dt else pure false
    else pure false
  if direct then
    let dt ← displayDatatype r unwrapped
    let name := r.runtime.nameOf dt
    let module := r.runtime.module name
    if qualified then
      if !(← s.isExported module (r.singletonName name)) then
        if !r.moduleOps.egal module r.mainModule then
          print_within_stacktrace p a o.styled io [fun target => r.printModule target module, fun target => printStr p target "."] "normal" true
    let name ← if demangle then displayDemangleName (r.singletonName name) else pure (r.singletonName name)
    let rendered ← s.sprintSymbol io name
    print_within_stacktrace p a o.styled io [fun target => printBytes p target rendered] "normal" true
  else
    let typeValue ← if JuliaLean.base.runtime_internals.isType r.runtime ft then do
      let value ← r.liftRuntime (r.runtime.typeParameter ft)
      pure (if r.runtime.isTypeVar value then none else some value)
      else pure none
    match typeValue with
    | some value =>
      let unwrapped := r.runtime.unwrap value
      let bare := match r.runtime.asDatatype unwrapped with
        | none => false
        | some dt => r.runtime.egal value (r.runtime.wrapper (r.runtime.nameOf dt))
      let parens := (o.unionall value).isSome && !bare
      if parens then printStr p io "("
      print_within_stacktrace p a o.styled io [fun target => r.printValue target value] "normal" true
      if parens then printStr p io ")"
    | none =>
      let argumentName ← r.stringValue fargname
      if html then
        printAll p io [printStr p io ("(" ++ argumentName ++ "::<b>"), r.printValue io ft, printStr p io "</b>)"]
      else
        print_within_stacktrace p a o.styled io [fun target => printStr p target ("(" ++ argumentName ++ "::"),
          fun target => r.printValue target ft, fun target => printStr p target ")"] "normal" true

def signatureUnionallEnv {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders) (variables : Binders) (io : JIO Io V) (signature : Ty) : m (JIO Io V × Ty) := do
  match o.unionall signature with
  | none => pure (io, signature)
  | some (binder, body) =>
    b.push variables binder
    let io ← displayBinderContext p a o io binder
    signatureUnionallEnv p a o b variables io body
partial_fixpoint

def showSignatureKeywords {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders BoolRef C Keywords KeywordState Arguments : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (s : SignatureDisplayOps m Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments)
    (io : JIO Io V) (keywords : Keywords) (first : Bool)
    (current : Option ((Ty × Ty) × KeywordState)) : m Unit := do
  match current with
  | none => pure ()
  | some ((name, type), state) =>
    if !first then printStr p io ", "
    print_within_stacktrace p a o.styled io [fun target => o.reflection.printValue target name] "light_black" false
    if ← o.types.eq type s.pairsNamedTuple then printStr p io "..."
    else
      printStr p io "::"
      print_type_bicolor_Any p o.styled s.bytes s.sprintValue io type "normal" "light_black"
        (← assertBool a (getIO p io "backtrace" false))
    showSignatureKeywords p a o s io keywords false (← s.keywordNext keywords state)
partial_fixpoint

/--
Julia source: base/show.jl:2653-2711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_tuple_as_call(out::IO, name::Symbol, sig::Type;
                            demangle=false, kwargs=nothing, argnames=nothing,
                            qualified=false, hasfirst=true)
    # print a method signature tuple for a lambda definition
    if sig === Tuple
        print(out, demangle ? demangle_function_name(name) : name, "(...)")
        return
    end
    tv = Any[]
    buf = IOBuffer()
    io = IOContext(buf, out)
    env_io = io
    while isa(sig, UnionAll)
        push!(tv, sig.var)
        env_io = IOContext(env_io, :unionall_env => sig.var)
        sig = sig.body
    end
    n = 1
    sig = (sig::DataType).parameters
    if hasfirst
        show_signature_function(env_io, sig[1], demangle, "", false, qualified)
        n += 1
    end
    first = true
    print_within_stacktrace(io, "(", bold=true)
    show_argnames = argnames !== nothing && length(argnames) == length(sig)
    for i = n:length(sig)  # fixme (iter): `eachindex` with offset?
        first || print(io, ", ")
        first = false
        if show_argnames
            print_within_stacktrace(io, argnames[i]; color=:light_black)
        end
        print(io, "::")
        print_type_bicolor(env_io, sig[i]; use_color = get(io, :backtrace, false)::Bool)
    end
    if kwargs !== nothing
        print(io, "; ")
        first = true
        for (k, t) in kwargs
            first || print(io, ", ")
            first = false
            print_within_stacktrace(io, k; color=:light_black)
            if t == pairs(NamedTuple)
                # omit type annotation for splat keyword argument
                print(io, "...")
            else
                print(io, "::")
                print_type_bicolor(io, t; use_color = get(io, :backtrace, false)::Bool)
            end
        end
    end
    print_within_stacktrace(io, ")", bold=true)
    show_method_params(io, tv)
    str = takestring!(buf)
    str = type_limited_string_from_context(out, str)
    print(out, str)
    nothing
end

```
-/
def show_tuple_as_call {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders BoolRef C Keywords KeywordState Arguments : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders)
    (s : SignatureDisplayOps m Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments)
    (out : JIO Io V) (name : Sym) (signature : Ty) (demangle : Bool := false)
    (kwargs : Option Keywords := none) (argnames : Option Arguments := none)
    (qualified : Bool := false) (hasfirst : Bool := true) : m Unit := do
  let r := o.reflection
  if r.runtime.egal signature o.types.tuple then
    let name ← if demangle then displayDemangleName name else pure name
    printAll p out [printStr p out name, printStr p out "(...)"]
    return
  let variables ← s.newVariables
  let buffer ← s.newBuffer
  let io := JIO.context (← IOContext_IO_IO p a (.plain buffer) out)
  let (environment, signature) ← signatureUnionallEnv p a o b variables io signature
  let mut start := 0
  let dt ← displayDatatype r signature
  let parameters ← r.liftRuntime (r.runtime.parameters dt)
  if hasfirst then
    show_signature_function p a o s environment (← displayAt parameters 0) demangle s.emptyArgumentName false qualified
    start := 1
  let mut first := true
  print_within_stacktrace p a o.styled io [fun target => printStr p target "("] "normal" true
  let showNames ← match argnames with
    | none => pure false
    | some arguments => do pure ((← s.argumentLength arguments).val == (parameters.length : Int))
  for index in List.range (parameters.length - start) do
    let index := start + index
    if !first then printStr p io ", "
    first := false
    if showNames then
      if let some arguments := argnames then
        let name ← s.argumentGet arguments (i64 (index + 1))
        print_within_stacktrace p a o.styled io [fun target => r.printValue target name] "light_black" false
    printStr p io "::"
    let type ← displayAt parameters index
    print_type_bicolor_Any p o.styled s.bytes s.sprintValue environment type "normal" "light_black"
      (← assertBool a (getIO p io "backtrace" false))
  if let some keywords := kwargs then
    printStr p io "; "
    showSignatureKeywords p a o s io keywords true (← s.keywordFirst keywords)
  print_within_stacktrace p a o.styled io [fun target => printStr p target ")"] "normal" true
  s.showMethodParams io variables
  let rendered ← s.takeString buffer
  let rendered ← type_limited_string_from_context p a s.asBoolRef s.setBoolRef s.displaysize
    (fun value limit => type_depth_limit s.string value limit) out rendered
  printBytes p out rendered


structure ObjectDisplayOps (m : Type → Type) (Ty D Ref VoidPtr BytePtr : Type) where
  getIndex : Ty → JInt64 → m Ty
  isDefined : Ty → Sum Sym JInt64 → m Bool
  newReference : Ty → m Ref
  bitSize : D → m JInt64
  preserve : {A : Type} → Ref → m A → m A
  referencePointer : Ref → m VoidPtr
  addPointer : VoidPtr → JInt64 → VoidPtr
  bytePointer : VoidPtr → BytePtr
  loadByte : BytePtr → m UInt8

def displayFieldName {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (type : D) (index : JInt64) : m (Sum Sym JInt64) := do
  let r := o.reflection
  let value := r.runtime.datatypeValue type
  if r.runtime.egalName (r.runtime.nameOf type) r.runtime.tupleName then
    let name ← r.liftRuntime (JuliaLean.base.runtime_internals.fieldnameTuple
      (fun (i : JInt64) => pure (decide (i.val < 1))) (JuliaLean.base.runtime_internals.fieldcount r.runtime)
      (fun (i n : JInt64) => pure (decide (i.val > n.val))) (fun (i : JInt64) => pure i) value index)
    return .inr name
  else
    let name ← r.liftRuntime (JuliaLean.base.runtime_internals.fieldnameDataType r.runtime
      (fun (i n : JInt64) => pure (decide (i.val > n.val))) (fun (i : JInt64) => pure (decide (i.val < 1)))
      (fun names (i : JInt64) => match names[(i.val - 1).toNat]? with
        | none => throw (.jl .boundsError)
        | some name => pure name) type index)
    return .inl name

/--
Julia source: base/show.jl:527-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_default(io::IO, @nospecialize(x))
    t = typeof(x)
    show(io, inferencebarrier(t)::DataType)
    print(io, '(')
    nf = nfields(x)
    nb = sizeof(x)::Int
    if nf != 0 || nb == 0
        if !show_circular(io, x)
            recur_io = IOContext(io, Pair{Symbol,Any}(:SHOWN_SET, x),
                                 Pair{Symbol,Any}(:typeinfo, Any))
            for i in 1:nf
                f = fieldname(t, i)
                if !isdefined(x, f)
                    print(io, undef_ref_str)
                else
                    show(recur_io, getfield(x, i))
                end
                if i < nf
                    print(io, ", ")
                end
            end
        end
    else
        print(io, "0x")
        r = Ref{Any}(x)
        nbits = Core.bitsizeof(t)
        nbytes = cld(nbits, 8)
        GC.@preserve r begin
            p = unsafe_convert(Ptr{Cvoid}, r)
            for i in (nbytes - 1):-1:0
                byte = unsafe_load(convert(Ptr{UInt8}, p + i))
                if i == nbytes - 1 && nbits % 8 != 0
                    byte &= (UInt8(1) << (nbits % 8)) - UInt8(1)
                    print(io, string(byte, base = 16, pad = cld(nbits % 8, 4)))
                else
                    print(io, string(byte, base = 16, pad = 2))
                end
            end
        end
    end
    print(io,')')
end
```
-/
def _show_default {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Ref VoidPtr BytePtr : Type}
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (objects : ObjectDisplayOps m Ty D Ref VoidPtr BytePtr) (digits : JuliaLean.base.intfuncs.DigitCallees)
    (showValue : JIO Io V → Ty → m Unit) (io : JIO Io V) (x : Ty) : m Unit := do
  let r := o.reflection
  let type := r.runtime.typeof x
  showValue io (r.runtime.datatypeValue type)
  printStr p io "("
  let fields ← r.liftRuntime (r.runtime.nfields x)
  let bytes ← r.liftRuntime (r.runtime.coreSizeof x)
  if fields.val != 0 || bytes.val == 0 then
    let circular ← show_circular p o.styled (fun n => do pure (lit (← r.stringInt n)))
      (fun value x => a.egal value (o.ofValue x)) io x
    if !circular then
      let context ← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (JuliaLean.base.dict.fieldConv V)
        io ("SHOWN_SET", o.ofValue x)
      let context ← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (typeConv a)
        (.context context) ("typeinfo", o.types.any)
      for index in List.range fields.val.toNat do
        let index := i64 (index + 1)
        let name ← displayFieldName o type index
        if !(← objects.isDefined x name) then
          printStr p io undef_ref_str
        else showValue (.context context) (← objects.getIndex x index)
        if index.val < fields.val then printStr p io ", "
  else
    printStr p io "0x"
    let reference ← objects.newReference x
    let bits ← objects.bitSize type
    let byteCount ← ofJl (JuliaLean.base.div.cldBitInteger bits (i64 8))
    objects.preserve reference (do
      let pointer ← objects.referencePointer reference
      for offset in (List.range byteCount.val.toNat).reverse do
        let mut byte ← objects.loadByte (objects.bytePointer (objects.addPointer pointer (i64 offset)))
        let remainder := bits.val.tmod 8
        if offset + 1 == byteCount.val.toNat && remainder != 0 then
          byte := byte &&& UInt8.ofNat (2 ^ remainder.toNat - 1)
          let pad ← ofJl (JuliaLean.base.div.cldBitInteger (i64 remainder) (i64 4))
          printBytes p io (← stringBits digits (JInt.wrap .u8 byte.toNat) (i64 16) pad)
        else printBytes p io (← stringBits digits (JInt.wrap .u8 byte.toNat) (i64 16) (i64 2)))
  printStr p io ")"

/--
Julia source: base/show.jl:583-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_function(io::IO, f::Function, compact::Bool, fallback::Function)
    fname = typeof(f).name
    if fname.name === fname.singletonname
        fallback(io, f)
    elseif compact
        print(io, fname.singletonname)
    elseif isdefined(fname, :module) && isdefinedglobal(fname.module, fname.singletonname) && isconst(fname.module, fname.singletonname) &&
            getglobal(fname.module, fname.singletonname) === f
        # this used to call the removed internal function `is_exported_from_stdlib`, which effectively
        # just checked for exports from Base.
        mod = get(io, :module, UsesBaseOnly)
        if !(isvisible(fname.singletonname, fname.module, mod) || fname.module === mod)
            print(io, fname.module, ".")
        end
        show_sym(io, fname.singletonname)
    else
        fallback(io, f)
    end
end
```
-/
def show_function {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : JIO Io V) (f : Ty) (compact : Bool) (fallback : JIO Io V → Ty → m Unit) : m Unit := do
  let r := o.reflection
  let name := r.runtime.nameOf (r.runtime.typeof f)
  let singleton := r.singletonName name
  if r.runtime.name name == singleton then fallback io f
  else if compact then printStr p io singleton
  else
    let global ← if r.nameModuleDefined name then do
      let module := r.runtime.module name
      if ← r.isDefinedGlobal module singleton then
        if ← r.isConst module singleton then
          pure (r.runtime.egal (← r.getGlobal module singleton) f)
        else pure false
      else pure false
      else pure false
    if global then
      let module := r.runtime.module name
      let origin ← match getIO p io "module" r.usesBaseOnly with
        | .inr origin => pure origin
        | .inl value => r.contextModule value
      let visible ← isvisible o singleton module origin
      if !(visible || r.moduleOps.egal module origin) then
        printAll p io [r.printModule io module, printStr p io "."]
      o.printSymbol io singleton
    else fallback io f

structure PartitionDisplayOps (m : Type → Type) (Ty GlobalRef Binding : Type) where
  bindingRef : Binding → GlobalRef
  valueRef : Ty → m GlobalRef
  printRef : JIO Io V → GlobalRef → m Unit

/--
Julia source: base/show.jl:3455-3505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_partition(io::IO, partition::Core.BindingPartition)
    print(io, partition.min_world)
    print(io, ":")
    max_world = @atomic partition.max_world
    if max_world == typemax(UInt)
        print(io, '∞')
    else
        print(io, max_world)
    end
    if (partition.kind & PARTITION_MASK_FLAG) != 0
        flags = String[]
        (partition.kind & PARTITION_FLAG_EXPORTED)            != 0 && push!(flags, "exported")
        (partition.kind & PARTITION_FLAG_IMPLICITLY_EXPORTED) != 0 && push!(flags, "re-exported")
        (partition.kind & PARTITION_FLAG_DEPRECATED)          != 0 && push!(flags, "deprecated")
        (partition.kind & PARTITION_FLAG_DEPWARN)             != 0 && push!(flags, "depwarn")
        (partition.kind & PARTITION_FLAG_IMPLICITLY_DEPRECATED) != 0 && push!(flags, "implicitly-deprecated")
        print(io, " [", join(flags, ","), "]")
    end
    print(io, " - ")
    kind = binding_kind(partition)
    if kind == PARTITION_KIND_BACKDATED_CONST
        print(io, "backdated constant binding")
    elseif kind == PARTITION_KIND_CONST
        print(io, "constant binding")
    elseif kind == PARTITION_KIND_CONST_IMPORT
        print(io, "constant binding (declared with `import`)")
    elseif kind == PARTITION_KIND_UNDEF_CONST
        print(io, "undefined const binding")
    elseif kind == PARTITION_KIND_GUARD
        print(io, "undefined binding - guard entry")
    elseif kind == PARTITION_KIND_FAILED
        print(io, "ambiguous binding - guard entry")
    elseif kind == PARTITION_KIND_DECLARED
        print(io, "weak global binding declared using `global` (implicit type Any)")
    elseif kind == PARTITION_KIND_IMPLICIT_GLOBAL
        print(io, "implicit `using` resolved to global ")
        print(io, partition_restriction(partition).globalref)
    elseif kind == PARTITION_KIND_IMPLICIT_CONST
        print(io, "implicit `using` resolved to constant")
    elseif kind == PARTITION_KIND_EXPLICIT
        print(io, "explicit `using` from ")
        print(io, partition_restriction(partition).globalref)
    elseif kind == PARTITION_KIND_IMPORTED
        print(io, "explicit `import` from ")
        print(io, partition_restriction(partition).globalref)
    else
        @assert kind == PARTITION_KIND_GLOBAL "unexpected partition kind"
        print(io, "global variable with type ")
        print(io, partition_restriction(partition))
    end
end
```
-/
def print_partition {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (parts : PartitionDisplayOps (Io := Io) (V := V) m Ty GlobalRef Binding)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V) (partition : Partition) : m Unit := do
  let r := o.reflection
  let printUInt := fun value => print_Unsigned p (fun value => stringBits digits value (i64 10) (i64 1)) io value
  printUInt (o.minWorld partition)
  printStr p io ":"
  let maxWorld ← o.atomicMaxWorld partition
  if maxWorld.val == 18446744073709551615 then printStr p io "∞"
  else printUInt maxWorld
  let rawKind := r.bindings.kind partition
  if rawKind.val.toNat &&& 496 != 0 then
    let mut flags := []
    for (mask, name) in [(16, "exported"), (128, "re-exported"), (32, "deprecated"), (64, "depwarn"), (256, "implicitly-deprecated")] do
      if rawKind.val.toNat &&& mask != 0 then flags := flags ++ [name]
    printAll p io [printStr p io " [", printStr p io (String.intercalate "," flags), printStr p io "]"]
  printStr p io " - "
  let kind := JuliaLean.base.runtime_internals.bindingKindPartition r.bindings partition
  if kind.val == 11 then printStr p io "backdated constant binding"
  else if kind.val == 0 then printStr p io "constant binding"
  else if kind.val == 1 then printStr p io "constant binding (declared with `import`)"
  else if kind.val == 10 then printStr p io "undefined const binding"
  else if kind.val == 9 then printStr p io "undefined binding - guard entry"
  else if kind.val == 7 then printStr p io "ambiguous binding - guard entry"
  else if kind.val == 8 then printStr p io "weak global binding declared using `global` (implicit type Any)"
  else if kind.val == 3 then
    let reference ← parts.valueRef (← r.liftRuntime (JuliaLean.base.runtime_internals.partitionRestriction r.bindings partition))
    printAll p io [printStr p io "implicit `using` resolved to global ", parts.printRef io reference]
  else if kind.val == 4 then printStr p io "implicit `using` resolved to constant"
  else if kind.val == 5 then
    let reference ← parts.valueRef (← r.liftRuntime (JuliaLean.base.runtime_internals.partitionRestriction r.bindings partition))
    printAll p io [printStr p io "explicit `using` from ", parts.printRef io reference]
  else if kind.val == 6 then
    let reference ← parts.valueRef (← r.liftRuntime (JuliaLean.base.runtime_internals.partitionRestriction r.bindings partition))
    printAll p io [printStr p io "explicit `import` from ", parts.printRef io reference]
  else
    if kind.val != 2 then throwShow (.assertionError "unexpected partition kind")
    let value ← r.liftRuntime (JuliaLean.base.runtime_internals.partitionRestriction r.bindings partition)
    printAll p io [printStr p io "global variable with type ", r.printValue io value]

/--
Julia source: base/show.jl:3507-3511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, partition::Core.BindingPartition)
    print(io, "BindingPartition(for ", partition_owner(partition).globalref, ": ")
    print_partition(io, partition)
    print(io, ")")
end
```
-/
def show_BindingPartition {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (parts : PartitionDisplayOps (Io := Io) (V := V) m Ty GlobalRef Binding)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V) (partition : Partition) : m Unit := do
  let owner ← o.reflection.liftRuntime (JuliaLean.base.runtime_internals.partitionOwner o.reflection.bindings partition)
  printAll p io [printStr p io "BindingPartition(for ", parts.printRef io (parts.bindingRef owner), printStr p io ": "]
  print_partition p o parts digits io partition
  printStr p io ")"

/--
Julia source: base/show.jl:3513-3517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", partition::Core.BindingPartition)
    print(io, "BindingPartition ")
    print(io, "for ", partition_owner(partition).globalref, "\n   ")
    print_partition(io, partition)
end
```
-/
def show_textplain_BindingPartition {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (parts : PartitionDisplayOps (Io := Io) (V := V) m Ty GlobalRef Binding)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V) (partition : Partition) : m Unit := do
  printStr p io "BindingPartition "
  let owner ← o.reflection.liftRuntime (JuliaLean.base.runtime_internals.partitionOwner o.reflection.bindings partition)
  printAll p io [printStr p io "for ", parts.printRef io (parts.bindingRef owner), printStr p io "\n   "]
  print_partition p o parts digits io partition

def showBindingPartitions {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (parts : PartitionDisplayOps (Io := Io) (V := V) m Ty GlobalRef Binding)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V) (partition : Partition) : m Unit := do
  printStr p io "\n"
  printStr p io "   "
  print_partition p o parts digits io partition
  match ← o.atomicNextPartition partition with
  | .inr _ => pure ()
  | .inl next => showBindingPartitions p o parts digits io next
partial_fixpoint

/--
Julia source: base/show.jl:3519-3536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", bnd::Core.Binding)
    print(io, "Binding ")
    print(io, bnd.globalref)
    if !isdefined(bnd, :partitions)
        print(io, " - No partitions")
    else
        partition = @atomic bnd.partitions
        while true
            println(io)
            print(io, "   ")
            print_partition(io, partition)
            next = @atomic partition.next
            # The last partition's `next` is a backreference to the owning Binding.
            next isa Core.BindingPartition || break
            partition = next
        end
    end
end
```
-/
def show_textplain_Binding {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (parts : PartitionDisplayOps (Io := Io) (V := V) m Ty GlobalRef Binding)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V) (binding : Binding) : m Unit := do
  printStr p io "Binding "
  parts.printRef io (parts.bindingRef binding)
  match ← o.bindingPartitions binding with
  | none => printStr p io " - No partitions"
  | some partition => showBindingPartitions p o parts digits io partition

/-- The `def` of a `Core.CodeInstance`: a `Core.ABIOverride` (with its `def`), a
`MethodInstance`, or another object (which fails the `def::MethodInstance` assertion). -/
inductive CodeInstanceDef (MI : Type) where
  | abiOverride (mi : MI)
  | methodInstance (mi : MI)
  | other

/-- Reflection over `MethodInstance`, `CodeInstance` and `CodeInfo` objects (`src/julia.h` fields),
and the callees of their display that live outside `base/show.jl`. `MI`, `CI`, `CInfo`, `DI` and
`Method` are object identities. -/
structure MethodInstanceDisplayOps (m : Type → Type) (Io V Ty Mod MI CI CInfo DI Method : Type) where
  /-- `mi.def`: a `Method`, or a `Module` for a top-level thunk. -/
  miDef : MI → Sum Method Mod
  /-- `isdefined(def, :generator) ? def.generator : nothing`, and `===` on `MethodInstance`s. -/
  generator : Method → Option MI
  egalMI : MI → MI → Bool
  methodName : Method → Sym
  specTypes : MI → Ty
  /-- `show(io, ::Method)` (`base/methodshow.jl`, loaded after show.jl). -/
  showMethod : JIO Io V → Method → m Unit
  /-- `isdefined(mi, :cache) ? mi.cache : nothing`. -/
  cache : MI → Option CI
  /-- `ci.owner === :uninferred`, `ci.owner !== nothing`, `ci.def`. -/
  ownerIsUninferred : CI → Bool
  ownerIsNothing : CI → Bool
  ciDef : CI → CodeInstanceDef MI
  /-- `ci.inferred.debuginfo`: a `FieldError`/`TypeError` when `inferred` is not a `CodeInfo`. -/
  inferredDebuginfo : CI → m DI
  /-- `Compiler.IRShow.debuginfo_firstline(di)` (the `Compiler` package, not a `base/*.jl` file). -/
  debuginfoFirstline : DI → m (Sym × JInt64)
  /-- `src.slotnames` (`nothing` is `none`). -/
  slotnames : CInfo → Option (List Sym)
  /-- The `Vector{String}` `sourceinfo_slotnames` returns: a new vector object holding new `String`
  objects with these bytes, as the `IOContext` value it is stored as. -/
  ofStrings : List Bytes → m V
  /-- `IRShow.show_ir(io, src, IRShow.IRShowConfig(IRShow.__debuginfo[debuginfo](src)))`: the
  `Compiler` package's IR printer; `debuginfo` is the keyword symbol (a `KeyError` from the
  `__debuginfo` dictionary for an unsupported one is the printer's). -/
  showIR : JIO Io V → CInfo → Sym → m Unit

/--
Julia source: base/show.jl:1533-1561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_mi(io::IO, mi::Core.MethodInstance, from_stackframe::Bool=false)
    def = mi.def
    if isa(def, Method)
        if isdefined(def, :generator) && mi === def.generator
            print(io, "MethodInstance generator for ")
            show(io, def)
        else
            print(io, "MethodInstance for ")
            show_tuple_as_call(io, def.name, mi.specTypes; qualified=true)
        end
    else
        print(io, "Toplevel MethodInstance thunk")
        # `thunk` is not very much information to go on. If this
        # MethodInstance is part of a stacktrace, it gets location info
        # added by other means.  But if it isn't, then we should try
        # to print a little more identifying information.
        if !from_stackframe && isdefined(mi, :cache)
            ci = mi.cache
            if ci.owner === :uninferred
                di = ci.inferred.debuginfo
                file, line = IRShow.debuginfo_firstline(di)
                file = string(file)
                line = isempty(file) || line < 0 ? "<unknown>" : "$file:$line"
                print(io, " from ", def, " starting at ", line)
            end
        end
    end
end

```
-/
def show_mi {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders BoolRef C Keywords KeywordState Arguments MI CI CInfo DI : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders)
    (s : SignatureDisplayOps m Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments)
    (x : MethodInstanceDisplayOps m Io V Ty Mod MI CI CInfo DI Method)
    (io : JIO Io V) (mi : MI) (from_stackframe : Bool := false) : m Unit := do
  match x.miDef mi with
  | .inl def_ =>
    if (match x.generator def_ with | some g => x.egalMI mi g | none => false) then
      printStr p io "MethodInstance generator for "
      x.showMethod io def_
    else
      printStr p io "MethodInstance for "
      show_tuple_as_call p a o b s io (x.methodName def_) (x.specTypes mi) (qualified := true)
  | .inr def_ =>
    printStr p io "Toplevel MethodInstance thunk"
    -- `thunk` is not very much information to go on. If this MethodInstance is part of a
    -- stacktrace, it gets location info added by other means. But if it isn't, then we should
    -- try to print a little more identifying information.
    if !from_stackframe then
      if let some ci := x.cache mi then
        if x.ownerIsUninferred ci then
          let di ← x.inferredDebuginfo ci
          let (file, line) ← x.debuginfoFirstline di
          -- `file = string(file)`
          let line : String ← if file.isEmpty || line.val < 0 then pure "<unknown>"
            else do pure (file ++ ":" ++ (← o.reflection.stringInt line))
          printAll p io [printStr p io " from ", o.reflection.printModule io def_,
            printStr p io " starting at ", printStr p io line]

/--
Julia source: base/show.jl:1518-1518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, mi::Core.MethodInstance) = show_mi(io, mi)
```
-/
def show_MethodInstance {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders BoolRef C Keywords KeywordState Arguments MI CI CInfo DI : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders)
    (s : SignatureDisplayOps m Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments)
    (x : MethodInstanceDisplayOps m Io V Ty Mod MI CI CInfo DI Method)
    (io : JIO Io V) (mi : MI) : m Unit :=
  show_mi p a o b s x io mi

/--
Julia source: base/show.jl:1519-1531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, codeinst::Core.CodeInstance)
    print(io, "CodeInstance for ")
    def = codeinst.def
    if isa(def, Core.ABIOverride)
        show_mi(io, def.def)
        print(io, " (ABI Overridden)")
    else
        show_mi(io, def::MethodInstance)
    end
    if codeinst.owner !== nothing
        print(io, " (foreign)")
    end
end
```
-/
def show_CodeInstance {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders BoolRef C Keywords KeywordState Arguments MI CI CInfo DI : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders)
    (s : SignatureDisplayOps m Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments)
    (x : MethodInstanceDisplayOps m Io V Ty Mod MI CI CInfo DI Method)
    (io : JIO Io V) (codeinst : CI) : m Unit := do
  printStr p io "CodeInstance for "
  match x.ciDef codeinst with
  | .abiOverride mi =>
    show_mi p a o b s x io mi
    printStr p io " (ABI Overridden)"
  | .methodInstance mi => show_mi p a o b s x io mi
  | .other => throwShow .typeError
  if !x.ownerIsNothing codeinst then
    printStr p io " (foreign)"

/--
Julia source: base/show.jl:2916-2929 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, src::CodeInfo; debuginfo::Symbol=:source)
    # Fix slot names and types in function body
    print(io, "CodeInfo(")
    lambda_io::IOContext = io
    if src.slotnames !== nothing
        lambda_io = IOContext(lambda_io, :SOURCE_SLOTNAMES => sourceinfo_slotnames(src))
    end
    println(io)
    # TODO: static parameter values?
    # only accepts :source or :none, we can't have a fallback for default since
    # that would break code_typed(, debuginfo=:source) iff IRShow.default_debuginfo[] = :none
    IRShow.show_ir(lambda_io, src, IRShow.IRShowConfig(IRShow.__debuginfo[debuginfo](src)))
    print(io, ")")
end
```
-/
def show_CodeInfo {MI CI CInfo DI Method Mod : Type}
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (x : MethodInstanceDisplayOps m Io V Ty Mod MI CI CInfo DI Method)
    (stringInt : JInt64 → m Bytes)
    (io : JIO Io V) (src : CInfo) (debuginfo : Sym := "source") : m Unit := do
  -- Fix slot names and types in function body
  printStr p io "CodeInfo("
  let mut lambda_io : JIO Io V := .context (← convertIOContext p a io)
  if let some names := x.slotnames src then
    let printnames ← x.ofStrings (← sourceinfo_slotnames stringInt names)
    lambda_io := .context (← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym)
      (JuliaLean.base.dict.fieldConv V) lambda_io ("SOURCE_SLOTNAMES", printnames))
  println p io []
  -- TODO: static parameter values?
  -- only accepts :source or :none, we can't have a fallback for default since
  -- that would break code_typed(, debuginfo=:source) iff IRShow.default_debuginfo[] = :none
  x.showIR lambda_io src debuginfo
  printStr p io ")"

/--
Julia source: base/show.jl:3442-3448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# printing OpaqueClosure
function show(io::IO, oc::Core.OpaqueClosure)
    A, R = typeof(oc).parameters
    show_tuple_as_call(io, Symbol(""), A; hasfirst=false)
    print(io, "->◌")
    print(io, "::", R)
end
```
-/
def show_OpaqueClosure {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders BoolRef C Keywords KeywordState Arguments : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders)
    (s : SignatureDisplayOps m Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments)
    (io : JIO Io V) (oc : Ty) : m Unit := do
  let r := o.reflection
  let params ← r.liftRuntime (r.runtime.parameters (r.runtime.typeof oc))
  -- `A, R = ...` indexes the parameter `svec`: a `BoundsError` when it is shorter than 2
  let (A, R) ← match params with
    | A :: R :: _ => pure (A, R)
    | _ => throwShow (.jl .boundsError)
  show_tuple_as_call p a o b s io "" A (hasfirst := false)
  printStr p io "->◌"
  printAll p io [printStr p io "::", r.printValue io R]

/--
Julia source: base/show.jl:3450-3452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", oc::Core.OpaqueClosure{A, R}) where {A, R}
    show(io, oc)
end
```
-/
def show_textplain_OpaqueClosure {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Binders BoolRef C Keywords KeywordState Arguments : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (b : BinderVectorOps m Ty Binders)
    (s : SignatureDisplayOps m Io V Ty Mod Binders BoolRef C Keywords KeywordState Arguments)
    (io : JIO Io V) (oc : Ty) : m Unit :=
  show_OpaqueClosure p a o b s io oc

/-- The `dump` method Julia's dispatch selects for a value (`dump(io, x, n, indent)`): a
`SimpleVector`, `Module`, `String`, `Symbol`, `Union`, `Ptr`, `Array`, `DataType`, or any other
value (the `@nospecialize(x)` method). -/
inductive DumpKind (Mod : Type) where
  | simpleVector
  | module (md : Mod)
  | string
  | symbol
  | union
  | ptr
  | array
  | datatype
  | other

/-- Runtime queries of `dump` beyond `TypeDisplayOps` and `ObjectDisplayOps`. Element reads of a
`SimpleVector` or `Array` (`isassigned(x, i)`, `x[i]`), the array's `eltype`, `size` (the `Dims`
tuple value), `length`, and `eltype(x) <: Number`; of a `DataType`: `x <: Tuple`, its `super` field,
its field types with unassigned slots (`datatype_fieldtypes`); `isa(p, Tuple)` of a value; the
global `stdout`; a `Module` stored in an `IOContext`. -/
structure DumpOps (m : Type → Type) (Io V Ty D Mod : Type) where
  kind : Ty → DumpKind Mod
  isFunction : Ty → Bool
  length : Ty → m JInt64
  isassigned : Ty → JInt64 → m Bool
  getindex : Ty → JInt64 → m Ty
  eltype : Ty → Ty
  size : Ty → m Ty
  eltypeIsNumber : Ty → Bool
  isTupleType : D → Bool
  supertype : D → Ty
  fieldtypes : D → m (List (Option Ty))
  isTupleValue : Ty → Bool
  stdout : JIO Io V
  ofModule : Mod → V

/--
Julia source: base/show.jl:3043-3043 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dump(io::IOContext, x::Module, n::Int, indent) = print(io, "Module ", x)
```
-/
def dump_Module {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : IOContext Io V) (x : Mod) : m Unit :=
  printAll p (.context io) [printStr p (.context io) "Module ", o.reflection.printModule (.context io) x]

/--
Julia source: base/show.jl:3044-3044 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dump(io::IOContext, x::String, n::Int, indent) = (print(io, "String "); show(io, x))
```
-/
def dump_String {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : IOContext Io V) (x : Ty) : m Unit := do
  printStr p (.context io) "String "
  o.reflection.showValue (.context io) x

/--
Julia source: base/show.jl:3045-3045 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dump(io::IOContext, x::Symbol, n::Int, indent) = print(io, typeof(x), " ", x)
```
-/
def dump_Symbol {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : IOContext Io V) (x : Ty) : m Unit :=
  let r := o.reflection
  printAll p (.context io) [r.printValue (.context io) (r.runtime.datatypeValue (r.runtime.typeof x)),
    printStr p (.context io) " ", r.printValue (.context io) x]

/--
Julia source: base/show.jl:3046-3046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dump(io::IOContext, x::Union,  n::Int, indent) = print(io, x)
```
-/
def dump_Union {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (_p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : IOContext Io V) (x : Ty) : m Unit :=
  o.reflection.printValue (.context io) x

/--
Julia source: base/show.jl:3047-3047 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dump(io::IOContext, x::Ptr,    n::Int, indent) = print(io, x)
```
-/
def dump_Ptr {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (_p : IOPrims m Io V)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (io : IOContext Io V) (x : Ty) : m Unit :=
  o.reflection.printValue (.context io) x

/--
Julia source: base/show.jl:3086-3126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Types
function dump(io::IOContext, x::DataType, n::Int, indent)
    # For some reason, tuples are structs
    is_struct = isstructtype(x) && !(x <: Tuple)
    is_mut = is_struct && ismutabletype(x)
    is_mut && print(io, "mutable ")
    is_struct && print(io, "struct ")
    isprimitivetype(x) && print(io, "primitive type ")
    isabstracttype(x) && print(io, "abstract type ")
    print(io, x)
    if x !== Any
        print(io, " <: ", supertype(x))
    end
    if n > 0 && !(x <: Tuple) && !isabstracttype(x)
        tvar_io::IOContext = io
        for tparam in x.parameters
            # approximately recapture the list of tvar parameterization
            # that may be used by the internal fields
            if isa(tparam, TypeVar)
                tvar_io = IOContext(tvar_io, :unionall_env => tparam)
            end
        end
        if x.name === _NAMEDTUPLE_NAME && !(x.parameters[1] isa Tuple)
            # named tuple type with unknown field names
            return
        end
        fields = fieldnames(x)
        fieldtypes = datatype_fieldtypes(x)
        for idx in eachindex(fields)
            println(io)
            print(io, indent, "  ")
            is_mut && isconst(x, idx) && print(io, "const ")
            print(io, fields[idx])
            if isassigned(fieldtypes, idx)
                print(io, "::")
                print(tvar_io, fieldtypes[idx])
            end
        end
    end
    nothing
end
```
-/
def dump_DataType {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet : Type}
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (d : DumpOps m Io V Ty D Mod)
    (io : IOContext Io V) (x : Ty) (n : JInt64) (indent : Bytes) : m Unit := do
  let r := o.reflection
  let jio : JIO Io V := .context io
  let dt ← displayDatatype r x
  -- For some reason, tuples are structs
  let is_struct := JuliaLean.base.runtime_internals.isstructtype r.runtime x && !d.isTupleType dt
  let is_mut := is_struct && JuliaLean.base.runtime_internals.ismutabletype r.runtime x
  if is_mut then printStr p jio "mutable "
  if is_struct then printStr p jio "struct "
  if JuliaLean.base.runtime_internals.isprimitivetype r.runtime x then printStr p jio "primitive type "
  if JuliaLean.base.runtime_internals.isabstracttype r.runtime x then printStr p jio "abstract type "
  r.printValue jio x
  if !r.runtime.egal x r.runtime.any then
    printAll p jio [printStr p jio " <: ", r.printValue jio (d.supertype dt)]
  if n.val > 0 && !d.isTupleType dt && !JuliaLean.base.runtime_internals.isabstracttype r.runtime x then
    let mut tvar_io : IOContext Io V := io
    for tparam in ← r.liftRuntime (r.runtime.parameters dt) do
      -- approximately recapture the list of tvar parameterization
      -- that may be used by the internal fields
      if r.runtime.isTypeVar tparam then
        tvar_io ← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (JuliaLean.base.dict.fieldConv V)
          (.context tvar_io) ("unionall_env", o.ofValue tparam)
    if r.runtime.egalName (r.runtime.nameOf dt) r.runtime.namedTupleName then
      let first ← match ← r.liftRuntime (r.runtime.parameters dt) with
        | first :: _ => pure first
        | [] => throwShow (.jl .boundsError)
      -- named tuple type with unknown field names
      if !d.isTupleValue first then return
    let fields ← r.liftRuntime (JuliaLean.base.runtime_internals.fieldnamesDataType r.runtime dt)
    let fieldtypes ← d.fieldtypes dt
    for (k, fname) in (List.range fields.length).zip fields do
      let idx := i64 (k + 1)
      println p jio []
      printAll p jio [printBytes p jio indent, printStr p jio "  "]
      if is_mut then
        if ← r.liftRuntime (JuliaLean.base.runtime_internals.isconstIndex r.runtime x idx) then
          printStr p jio "const "
      printStr p jio fname
      if let some (some ft) := fieldtypes[k]? then
        printStr p jio "::"
        r.printValue (.context tvar_io) ft

mutual

/-- `dump(io, x, n, indent)`: Julia's dispatch on the value (`DumpOps.kind`). -/
def dump {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Ref VoidPtr BytePtr : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (objects : ObjectDisplayOps m Ty D Ref VoidPtr BytePtr) (d : DumpOps m Io V Ty D Mod)
    (io : IOContext Io V) (x : Ty) (n : JInt64) (indent : Bytes) : m Unit :=
  match d.kind x with
  | .simpleVector => dump_SimpleVector p a o objects d io x n indent
  | .module md => dump_Module p o io md
  | .string => dump_String p o io x
  | .symbol => dump_Symbol p o io x
  | .union => dump_Union p o io x
  | .ptr => dump_Ptr p o io x
  | .array => dump_Array p a o objects d io x n indent
  | .datatype => dump_DataType p a o d io x n indent
  | .other => dump_Any p a o objects d io x n indent
partial_fixpoint

/--
Julia source: base/show.jl:2990-3008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dump(io::IOContext, x::SimpleVector, n::Int, indent)
    if isempty(x)
        print(io, "empty SimpleVector")
        return
    end
    print(io, "SimpleVector")
    if n > 0
        for i in eachindex(x)
            println(io)
            print(io, indent, "  ", i, ": ")
            if isassigned(x,i)
                dump(io, x[i], n - 1, string(indent, "  "))
            else
                print(io, undef_ref_str)
            end
        end
    end
    nothing
end
```
-/
def dump_SimpleVector {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Ref VoidPtr BytePtr : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (objects : ObjectDisplayOps m Ty D Ref VoidPtr BytePtr) (d : DumpOps m Io V Ty D Mod)
    (io : IOContext Io V) (x : Ty) (n : JInt64) (indent : Bytes) : m Unit := do
  let len ← d.length x
  if len.val == 0 then
    printStr p (.context io) "empty SimpleVector"
    return
  printStr p (.context io) "SimpleVector"
  if n.val > 0 then
    for k in List.range len.val.toNat do
      let i := i64 (k + 1)
      println p (.context io) []
      printAll p (.context io) [printBytes p (.context io) indent, printStr p (.context io) "  ",
        do printStr p (.context io) (← o.reflection.stringInt i), printStr p (.context io) ": "]
      if ← d.isassigned x i then
        dump p a o objects d io (← d.getindex x i) (JInt.wrap .i64 (n.val - 1)) (indent ++ lit "  ")
      else
        printStr p (.context io) undef_ref_str
partial_fixpoint

/--
Julia source: base/show.jl:3010-3041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dump(io::IOContext, @nospecialize(x), n::Int, indent)
    if x === Union{}
        show(io, x)
        return
    end
    T = typeof(x)
    if isa(x, Function)
        print(io, x, " (function of type ", T, ")")
    else
        print(io, T)
    end
    nf = nfields(x)
    if nf > 0
        if n > 0 && !show_circular(io, x)
            recur_io = IOContext(io, Pair{Symbol,Any}(:SHOWN_SET, x))
            for field in 1:nf
                println(io)
                fname = string(fieldname(T, field))
                print(io, indent, "  ", fname, ": ")
                if isdefined(x,field)
                    dump(recur_io, getfield(x, field), n - 1, string(indent, "  "))
                else
                    print(io, undef_ref_str)
                end
            end
        end
    elseif !isa(x, Function)
        print(io, " ")
        show(io, x)
    end
    nothing
end
```
-/
def dump_Any {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Ref VoidPtr BytePtr : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (objects : ObjectDisplayOps m Ty D Ref VoidPtr BytePtr) (d : DumpOps m Io V Ty D Mod)
    (io : IOContext Io V) (x : Ty) (n : JInt64) (indent : Bytes) : m Unit := do
  let r := o.reflection
  let jio : JIO Io V := .context io
  if r.runtime.egal x r.runtime.bottom then
    r.showValue jio x
    return
  let T := r.runtime.typeof x
  if d.isFunction x then
    printAll p jio [r.printValue jio x, printStr p jio " (function of type ",
      r.printValue jio (r.runtime.datatypeValue T), printStr p jio ")"]
  else
    r.printValue jio (r.runtime.datatypeValue T)
  let nf ← r.liftRuntime (r.runtime.nfields x)
  if nf.val > 0 then
    if n.val > 0 then
      if !(← show_circular p o.styled (fun k => do pure (lit (← r.stringInt k)))
          (fun value x => a.egal value (o.ofValue x)) jio x) then
        let recur_io ← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (JuliaLean.base.dict.fieldConv V)
          jio ("SHOWN_SET", o.ofValue x)
        for k in List.range nf.val.toNat do
          let field := i64 (k + 1)
          println p jio []
          let fname ← match ← displayFieldName o T field with
            | .inl s => pure s
            | .inr i => r.stringInt i
          printAll p jio [printBytes p jio indent, printStr p jio "  ", printStr p jio fname,
            printStr p jio ": "]
          if ← objects.isDefined x (.inr field) then
            dump p a o objects d recur_io (← objects.getIndex x field) (JInt.wrap .i64 (n.val - 1))
              (indent ++ lit "  ")
          else
            printStr p jio undef_ref_str
  else if !d.isFunction x then
    printStr p jio " "
    r.showValue jio x
partial_fixpoint

/--
Julia source: base/show.jl:3049-3059 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dump_elts(io::IOContext, x::Array, n::Int, indent, i0, i1)
    for i in i0:i1
        print(io, indent, "  ", i, ": ")
        if !isassigned(x,i)
            print(io, undef_ref_str)
        else
            dump(io, x[i], n - 1, string(indent, "  "))
        end
        i < i1 && println(io)
    end
end
```
-/
def dump_elts {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Ref VoidPtr BytePtr : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (objects : ObjectDisplayOps m Ty D Ref VoidPtr BytePtr) (d : DumpOps m Io V Ty D Mod)
    (io : IOContext Io V) (x : Ty) (n : JInt64) (indent : Bytes) (i0 i1 : JInt64) : m Unit := do
  let jio : JIO Io V := .context io
  for k in List.range (i1.val - i0.val + 1).toNat do
    let i := JInt.wrap .i64 (i0.val + k)
    printAll p jio [printBytes p jio indent, printStr p jio "  ",
      do printStr p jio (← o.reflection.stringInt i), printStr p jio ": "]
    if !(← d.isassigned x i) then
      printStr p jio undef_ref_str
    else
      dump p a o objects d io (← d.getindex x i) (JInt.wrap .i64 (n.val - 1)) (indent ++ lit "  ")
    if i.val < i1.val then println p jio []
partial_fixpoint

/--
Julia source: base/show.jl:3061-3084 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dump(io::IOContext, x::Array, n::Int, indent)
    print(io, "Array{", eltype(x), "}(", size(x), ")")
    if eltype(x) <: Number
        print(io, " ")
        show(io, x)
    else
        if n > 0 && !isempty(x) && !show_circular(io, x)
            println(io)
            recur_io = IOContext(io, :SHOWN_SET => x)
            lx = length(x)
            if get(io, :limit, false)::Bool
                dump_elts(recur_io, x, n, indent, 1, (lx <= 10 ? lx : 5))
                if lx > 10
                    println(io)
                    println(io, indent, "  ...")
                    dump_elts(recur_io, x, n, indent, lx - 4, lx)
                end
            else
                dump_elts(recur_io, x, n, indent, 1, lx)
            end
        end
    end
    nothing
end
```
-/
def dump_Array {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Ref VoidPtr BytePtr : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (objects : ObjectDisplayOps m Ty D Ref VoidPtr BytePtr) (d : DumpOps m Io V Ty D Mod)
    (io : IOContext Io V) (x : Ty) (n : JInt64) (indent : Bytes) : m Unit := do
  let r := o.reflection
  let jio : JIO Io V := .context io
  let sz ← d.size x
  printAll p jio [printStr p jio "Array{", r.printValue jio (d.eltype x), printStr p jio "}(",
    r.printValue jio sz, printStr p jio ")"]
  if d.eltypeIsNumber x then
    printStr p jio " "
    r.showValue jio x
  else
    let lx ← d.length x
    if n.val > 0 && lx.val != 0 then
      if !(← show_circular p o.styled (fun k => do pure (lit (← r.stringInt k)))
          (fun value x => a.egal value (o.ofValue x)) jio x) then
        println p jio []
        let recur_io ← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym) (JuliaLean.base.dict.fieldConv V)
          jio ("SHOWN_SET", o.ofValue x)
        if ← assertBool a (getIO p jio "limit" false) then
          dump_elts p a o objects d recur_io x n indent (i64 1) (if lx.val ≤ 10 then lx else i64 5)
          if lx.val > 10 then
            println p jio []
            println p jio [printBytes p jio indent, printStr p jio "  ..."]
            dump_elts p a o objects d recur_io x n indent (JInt.wrap .i64 (lx.val - 4)) lx
        else
          dump_elts p a o objects d recur_io x n indent (i64 1) lx
partial_fixpoint

end

/--
Julia source: base/show.jl:3128-3128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const DUMP_DEFAULT_MAXDEPTH = 8
```
-/
def DUMP_DEFAULT_MAXDEPTH : JInt64 := i64 8

/--
Julia source: base/show.jl:3130-3133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dump(io::IO, @nospecialize(x); maxdepth=DUMP_DEFAULT_MAXDEPTH)
    dump(IOContext(io), x, maxdepth, "")
    println(io)
end
```
-/
def dump_IO {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Ref VoidPtr BytePtr : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (objects : ObjectDisplayOps m Ty D Ref VoidPtr BytePtr) (d : DumpOps m Io V Ty D Mod)
    (io : JIO Io V) (x : Ty) (maxdepth : JInt64 := DUMP_DEFAULT_MAXDEPTH) : m Unit := do
  dump p a o objects d (← IOContext_IO p a io) x maxdepth []
  println p io []

/--
Julia source: base/show.jl:3135-3167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    dump(x; maxdepth=$DUMP_DEFAULT_MAXDEPTH)

Show every part of the representation of a value.
The depth of the output is truncated at `maxdepth`.

# Examples
```jldoctest
julia> struct MyStruct
           x
           y
       end

julia> x = MyStruct(1, (2,3));

julia> dump(x)
MyStruct
  x: Int64 1
  y: Tuple{Int64, Int64}
    1: Int64 2
    2: Int64 3

julia> dump(x; maxdepth = 1)
MyStruct
  x: Int64 1
  y: Tuple{Int64, Int64}
```
"""
function dump(arg; maxdepth=DUMP_DEFAULT_MAXDEPTH)
    # this is typically used interactively, so default to being in Main (or current active module)
    mod = get(stdout, :module, active_module())
    dump(IOContext(stdout::IO, :limit => true, :module => mod), arg; maxdepth=maxdepth)
end
````
-/
def dump_default {World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet Ref VoidPtr BytePtr : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : TypeDisplayOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr GlobalRef Binding Partition Method Repl ModuleSet)
    (objects : ObjectDisplayOps m Ty D Ref VoidPtr BytePtr) (d : DumpOps m Io V Ty D Mod)
    (arg : Ty) (maxdepth : JInt64 := DUMP_DEFAULT_MAXDEPTH) : m Unit := do
  -- this is typically used interactively, so default to being in Main (or current active module)
  -- `active_module()` is an argument of `get`, evaluated before the lookup
  let dflt := d.ofModule (← active_module o.reflection)
  let mod := match getIO p d.stdout "module" () with
    | .inl v => v
    | .inr () => dflt
  let ctx ← IOContext_pairs p a (JuliaLean.base.dict.fieldConv Sym) (JuliaLean.base.dict.fieldConv V) d.stdout
    ("limit", a.ofBool true) [("module", mod)]
  dump_IO p a o objects d (.context ctx) arg maxdepth

end

end JuliaLean.base.show

namespace JuliaLean.ShowCov.Methods.ShowFile

set_option linter.unusedVariables false

open JuliaLean.ShowCov
open JuliaLean.Show
open JuliaLean.Strings

structure Capture where
  matchText : List Char
  nextIndex : Nat
  deriving DecidableEq, Repr

def captureIter : List Capture → Option (Capture × (Nat × List Capture))
  | [] => none
  | capture :: rest => some (capture, (capture.nextIndex, rest))

def ansiIterStep (captures : List Capture) (i : Nat) :
    Option ((Nat × Truncate.Tok) ×
      (Nat × Option (Capture × (Nat × List Capture)))) :=
  match captureIter captures with
  | none => none
  | some (capture, (j, newState)) =>
    let token := if (capture.matchText.map Char.utf8Size).sum = 1 then
      match capture.matchText with
      | [c] => Truncate.Tok.ch c
      | _ => Truncate.Tok.ansi capture.matchText
    else Truncate.Tok.ansi capture.matchText
    some ((i, token), (j, captureIter newState))

structure RangeValue where
  id : Nat
  deriving DecidableEq, Repr

structure RangeRuntime where
  render : RangeValue → String
  summary : RangeValue → String
  printLinRange : RangeValue → String
  printLogRange : RangeValue → String
  isempty : RangeValue → Bool

structure WrapperValue where
  id : Nat
  deriving DecidableEq, Repr

structure WrapperRuntime where
  render : WrapperValue → String

structure TypeNameValue where
  id : Nat
  name : String
  singletonName : String
  moduleName : String
  moduleFieldDefined : Bool
  moduleGlobalDefined : Bool
  moduleBindingConst : Bool
  globalValueId : Nat
  deriving DecidableEq, Repr

structure DataTypeValue where
  id : Nat
  typeName : TypeNameValue
  deriving DecidableEq, Repr

structure BindingPartitionValue where
  kind : Nat
  restriction : Nat
  deriving DecidableEq, Repr

structure SelfRuntime where
  worldAge : Nat
  parentModule : DataTypeValue → String
  lookupBindingPartition : Nat → String → String → BindingPartitionValue
  bindingKind : BindingPartitionValue → Nat
  backdatedConstKind : Nat
  typeOf : Nat → Nat
  isDefinedGlobal : String → String → Bool
  getGlobal : String → String → Nat

def isSelfBody (runtime : SelfRuntime) (ft : DataTypeValue) : Bool :=
  let ftname := ft.typeName
  let name := ftname.singletonName
  if ftname.name == name then false
  else
    let mod := runtime.parentModule ft
    let bpart := runtime.lookupBindingPartition runtime.worldAge mod name
    if runtime.bindingKind bpart = runtime.backdatedConstKind then
      ft.id = runtime.typeOf bpart.restriction
    else runtime.isDefinedGlobal mod name &&
      ft.id = runtime.typeOf (runtime.getGlobal mod name)

inductive DisplayFunctionKind where
  | intrinsic
  | builtin
  | generic
  deriving DecidableEq, Repr

structure FunctionValue where
  id : Nat
  datatype : DataTypeValue
  kind : DisplayFunctionKind
  methods : List Nat
  deriving DecidableEq, Repr

structure FunctionRuntime where
  selfRuntime : SelfRuntime
  render : FunctionValue → String
  renderType : DataTypeValue → String
  bitcastInt32 : FunctionValue → Int
  visibleFrom : String → String → String → Bool
  fallbackDefault : FunctionValue → String
  fallbackShow : FunctionValue → String

def showFunctionBody (runtime : FunctionRuntime) (compact : Bool)
    (f : FunctionValue) : String :=
  if compact then runtime.render f
  else
    let ft := f.datatype
    let name := ft.typeName.singletonName
    match f.kind with
    | .intrinsic =>
      runtime.render f ++ " (intrinsic function #" ++
        toString (runtime.bitcastInt32 f) ++ ")"
    | .builtin => name ++ " (built-in function)"
    | .generic =>
      let n := f.methods.length
      let methodWord := if n = 1 then "method" else "methods"
      let stringName := name
      let shownName := if isSelfBody runtime.selfRuntime ft || stringName.contains '#' then
        stringName else "(::" ++ runtime.renderType ft ++ ")"
      let what := if shownName.startsWith "@" then "macro" else "generic function"
      shownName ++ " (" ++ what ++ " with " ++ toString n ++ " " ++ methodWord ++ ")"

inductive FunctionFallback where
  | showDefault
  | show
  deriving DecidableEq, Repr

structure FunctionIO where
  moduleName : String
  compact : Bool
  deriving DecidableEq, Repr

def functionFallback (runtime : FunctionRuntime) : FunctionFallback → FunctionValue → String
  | .showDefault, function => runtime.fallbackDefault function
  | .show, function => runtime.fallbackShow function

def showFunctionCore (runtime : FunctionRuntime) (io : FunctionIO)
    (function : FunctionValue) (compact : Bool) (fallback : FunctionFallback) : String :=
  let fname := function.datatype.typeName
  if fname.name == fname.singletonName then functionFallback runtime fallback function
  else if compact then fname.singletonName
  else if fname.moduleFieldDefined && fname.moduleGlobalDefined &&
      fname.moduleBindingConst && fname.globalValueId = function.id then
    let qualifier := if runtime.visibleFrom fname.singletonName fname.moduleName io.moduleName ||
        fname.moduleName = io.moduleName then "" else fname.moduleName ++ "."
    qualifier ++ fname.singletonName
  else functionFallback runtime fallback function

structure ActiveReplValue where
  id : Nat
  deriving DecidableEq, Repr

structure ActiveModuleRuntime where
  isPureContext : Unit → Bool
  activeReplDefined : Unit → Bool
  activeRepl : Option ActiveReplValue
  invokeLatest : ActiveReplValue → String

def activeModuleBody (runtime : ActiveModuleRuntime) : R String :=
  if runtime.isPureContext () then
    .error (.errorException "active_module() should not be called from a pure context")
  else match runtime.activeReplDefined (), runtime.activeRepl with
    | false, _ => .ok "Main"
    | true, none => .ok "Main"
    | true, some repl => .ok (runtime.invokeLatest repl)

structure TypeObject where
  id : Nat
  deriving DecidableEq, Repr

inductive UnwrappedType where
  | dataType (wrapperId : Nat)
  | other
  deriving DecidableEq, Repr

structure TypeRuntime where
  unwrapUnionall : TypeObject → UnwrappedType

def printWithoutParamsBody (runtime : TypeRuntime) (value : TypeObject) : Bool :=
  match runtime.unwrapUnionall value with
  | .dataType wrapperId => wrapperId = value.id
  | .other => false

structure TypeVarValue where
  id : Nat
  name : String
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

inductive TypeBindingValue where
  | typeVar (value : TypeVarValue)
  | other (id : Nat)
  deriving DecidableEq, Repr

structure TypeVarContext where
  dict : List (String × TypeBindingValue)
  deriving DecidableEq, Repr

structure TypeVarRuntime where
  hasTypevar : TypeObject → TypeVarValue → Bool

def ioHasTypevarBody (runtime : TypeVarRuntime) (io : TypeVarContext)
    (name : String) (value : TypeObject) : Bool :=
  io.dict.any fun binding =>
    binding.1 == "unionall_env" && match binding.2 with
    | .typeVar typevar => typevar.name == name && runtime.hasTypevar value typevar
    | .other _ => false

inductive TypeParameterValue where
  | anyType (shape : Remaining.TypeShape)
  | typeVar (shape : Remaining.TypeShape)
  | nonType (id : Nat)

structure ParameterizedTypeValue where
  id : Nat
  deriving DecidableEq, Repr

structure ParameterRuntime where
  typeParameter : ParameterizedTypeValue → TypeParameterValue

def modulesTypeEqBody (runtime : ParameterRuntime) (value : ParameterizedTypeValue) : List String :=
  match runtime.typeParameter value with
  | .anyType shape | .typeVar shape => Remaining.modulesOf shape
  | .nonType _ => []

structure FreeTypevarRuntime where
  hasFreeTypevars : TypeObject → Bool
  findFreeTypevars : TypeObject → List TypeVarValue

def hasOtherFreeTypevarsBody (runtime : FreeTypevarRuntime) (value : TypeObject)
    (freeBefore : List TypeVarValue) : Bool :=
  if !runtime.hasFreeTypevars value then false
  else (runtime.findFreeTypevars value).any fun freeVar =>
    !(freeBefore.any fun previous => previous.id == freeVar.id)

inductive TypeExpr where
  | atom (id : Nat)
  | unionAll (freeVar : TypeVarValue) (body : TypeExpr)
  deriving DecidableEq, Repr

def reapplyUnionallBody (context : Option TypeVarContext) (value : TypeExpr) : TypeExpr :=
  match context with
  | none => value
  | some io => io.dict.foldl (fun result binding =>
      if binding.1 == "unionall_env" then match binding.2 with
        | .typeVar freeVar => .unionAll freeVar result
        | .other _ => result
      else result) value

structure SymbolValue where
  id : Nat
  deriving DecidableEq, Repr

structure SymbolRuntime where
  string : SymbolValue → String

inductive TypeSlot where
  | typeVar (value : TypeVarValue)
  | other (value : TypeObject)
  deriving DecidableEq, Repr

structure TypeRelationRuntime where
  hasTypevar : Nat → TypeVarValue → Bool
  structurallyEquivalent : Nat → Nat → Bool

def showCanElideBody (runtime : TypeRelationRuntime) (parameter : TypeVarValue)
    (wheres : List TypeVarValue) (elide : Nat) (env : List TypeSlot) (skip : Nat) : Bool :=
  if elide = 0 then false
  else match wheres[elide - 1]? with
  | none => false
  | some selected =>
    if selected.id != parameter.id then false
    else
      let laterOk := (wheres.drop elide).all fun value =>
        !runtime.hasTypevar value.lower parameter && !runtime.hasTypevar value.upper parameter
      let envOk := env.zipIdx.all fun (value, index) =>
        index + 1 = skip || match value with
        | .typeVar typevar =>
          !runtime.hasTypevar typevar.lower parameter &&
            !runtime.hasTypevar typevar.upper parameter
        | .other other => !runtime.hasTypevar other.id parameter
      laterOk && envOk

def egalVarBody (runtime : TypeRelationRuntime) (parameter : TypeVarValue) : TypeSlot → Bool
  | .other _ => false
  | .typeVar other =>
    runtime.structurallyEquivalent parameter.upper other.upper &&
      runtime.structurallyEquivalent parameter.lower other.lower

structure GlobalRefValue where
  moduleName : String
  name : String
  deriving DecidableEq, Repr

structure AliasNameRuntime where
  compact : Bool
  fromModule : Option String
  visible : String → String → String → Bool
  renderModule : String → String

def showAliasNameBody (runtime : AliasNameRuntime) (reference : GlobalRefValue) : Out :=
  let qualifier := if runtime.compact then [] else match runtime.fromModule with
    | none => [runtime.renderModule reference.moduleName, "."]
    | some origin => if runtime.visible reference.name reference.moduleName origin then []
      else [runtime.renderModule reference.moduleName, "."]
  qualifier ++ [reference.name]

structure WheresRuntime where
  render : List TypeVarValue → TypeVarValue → String

def showWheresLoop (runtime : WheresRuntime) (all : List TypeVarValue) :
    List TypeVarValue → Nat → Out
  | [], _ => []
  | parameter :: rest, index =>
    [if all.length = 1 then " where " else if index = 1 then " where {" else ", ",
      runtime.render (all.take (index - 1)) parameter] ++
    showWheresLoop runtime all rest (index + 1)

def showWheresBody (runtime : WheresRuntime) (wheres : List TypeVarValue) : Out :=
  showWheresLoop runtime wheres wheres 1 ++ if wheres.length > 1 then ["}"] else []

structure TypeParamsRuntime where
  relation : TypeRelationRuntime
  bottomId : Nat
  anyId : Nat
  render : List TypeVarValue → TypeSlot → String

def elideParamStep (runtime : TypeParamsRuntime) (env orig : List TypeSlot)
    (wheres : List TypeVarValue) (state : Nat × Nat) (index : Nat) : Nat × Nat :=
  let (n, elide) := state
  match env[index]? with
  | none | some (.other _) => state
  | some (.typeVar parameter) =>
    let can := showCanElideBody runtime.relation parameter wheres elide env (index + 1)
    let sameOrig := match orig[index]? with
      | some other => egalVarBody runtime.relation parameter other
      | none => false
    if index + 1 = n && sameOrig && can then (n - 1, elide - 1)
    else if parameter.lower = runtime.bottomId && parameter.name.contains '#' && can then
      (n, elide - 1)
    else if parameter.upper = runtime.anyId && parameter.name.contains '#' && can then
      (n, elide - 1)
    else state

def wherePosition (wheres : List TypeVarValue) (parameter : TypeVarValue) : Nat :=
  match wheres.findIdx? (fun value => value.id == parameter.id) with
  | none => 0
  | some index => index + 1

def renderTypeParam (runtime : TypeParamsRuntime) (wheres : List TypeVarValue)
    (elide : Nat) : TypeSlot → String
  | slot@(.other _) => runtime.render wheres slot
  | slot@(.typeVar parameter) =>
    if parameter.lower = runtime.bottomId && wherePosition wheres parameter > elide then
      "<:" ++ runtime.render wheres (.other ⟨parameter.upper⟩)
    else if parameter.upper = runtime.anyId && wherePosition wheres parameter > elide then
      ">:" ++ runtime.render wheres (.other ⟨parameter.lower⟩)
    else runtime.render wheres slot

def showTypeparamsBody (runtime : TypeParamsRuntime) (env orig : List TypeSlot)
    (wheres : List TypeVarValue) : Out × List TypeVarValue :=
  let initial := (env.length, wheres.length)
  let (n, elide) := (List.range env.length).reverse.foldl
    (elideParamStep runtime env orig wheres) initial
  let params := env.take n
  let output := if n = 0 then [] else ["{"] ++
    params.zipIdx.flatMap (fun (parameter, index) =>
      [renderTypeParam runtime wheres elide parameter] ++
        if index + 1 < n then [", "] else []) ++ ["}"]
  (output, wheres.take elide)

structure TypeAliasValue where
  reference : GlobalRefValue
  binders : List TypeVarValue
  deriving DecidableEq, Repr

structure TypeAliasRuntime where
  nameRuntime : AliasNameRuntime
  paramsRuntime : TypeParamsRuntime

def showTypealiasBody (runtime : TypeAliasRuntime) (alias : TypeAliasValue)
    (env : List TypeSlot) (wheres : List TypeVarValue) : Out × List TypeVarValue :=
  let name := showAliasNameBody runtime.nameRuntime alias.reference
  if env.isEmpty then (name, wheres)
  else
    let params := showTypeparamsBody runtime.paramsRuntime env
      (alias.binders.map TypeSlot.typeVar) wheres
    (name ++ params.1, params.2)

structure MakeWheresRuntime where
  hasTypevar : TypeExpr → TypeVarValue → Bool

def addSeen (seen : List Nat) (typevar : TypeVarValue) : List Nat :=
  if seen.contains typevar.id then seen else typevar.id :: seen

def outerWheres : TypeExpr → List Nat → List TypeVarValue →
    List Nat × List TypeVarValue
  | .atom _, seen, wheres => (seen, wheres)
  | .unionAll typevar body, seen, wheres =>
    if seen.contains typevar.id then outerWheres body seen wheres
    else outerWheres body (typevar.id :: seen) (wheres ++ [typevar])

def makeWheresBody (runtime : MakeWheresRuntime) (context : Option TypeVarContext)
    (env : List TypeSlot) (value : TypeExpr) : List TypeVarValue :=
  let contextVars := match context with
    | none => []
    | some io => io.dict.filterMap fun (binding : String × TypeBindingValue) =>
      if binding.1 == "unionall_env" then match binding.2 with
        | TypeBindingValue.typeVar typevar =>
          if runtime.hasTypevar value typevar then some typevar else none
        | TypeBindingValue.other _ => none
      else none
  let seen := contextVars.foldl addSeen []
  let (seen, wheres) := outerWheres value seen []
  (env.reverse.foldl (fun (seen, wheres) slot => match slot with
    | .other _ => (seen, wheres)
    | .typeVar typevar => if seen.contains typevar.id then (seen, wheres)
      else (typevar.id :: seen, typevar :: wheres)) (seen, wheres)).2

structure AliasDispatchRuntime where
  makeAlias : TypeExpr → Option (TypeAliasValue × List TypeSlot)
  makeWheres : List TypeSlot → TypeExpr → List TypeVarValue
  showAlias : TypeAliasValue → List TypeSlot → List TypeVarValue → Out
  showWheres : List TypeVarValue → Out

def showTypealiasDispatchBody (runtime : AliasDispatchRuntime) (value : TypeExpr) : Bool × Out :=
  match runtime.makeAlias value with
  | none => (false, [])
  | some (alias, env) =>
    let wheres := runtime.makeWheres env value
    (true, runtime.showAlias alias env wheres ++ runtime.showWheres wheres)

structure AliasObject where
  id : Nat
  isUnionAll : Bool
  deriving DecidableEq, Repr

structure FoundAlias where
  reference : GlobalRefValue
  object : AliasObject
  env : List TypeSlot
  deriving DecidableEq, Repr

structure MakeAliasRuntime where
  anyId : Nat
  isTupleSubtype : TypeObject → Bool
  modulesOf : TypeObject → List String
  normalizeModule : String → String
  names : String → List String
  isDefinedGlobal : String → String → Bool
  isDeprecated : String → String → Bool
  isConst : String → String → Bool
  getGlobal : String → String → AliasObject
  isType : AliasObject → Bool
  hasFreeTypevars : AliasObject → Bool
  printWithoutParams : AliasObject → Bool
  isSubtype : TypeObject → AliasObject → Bool
  reapplyContext : Option TypeVarContext → TypeObject → TypeObject
  findFreeTypevars : TypeObject → List TypeVarValue
  unbounded : AliasObject → AliasObject
  intersectEnv : TypeObject → AliasObject → List TypeSlot
  applyAlias : AliasObject → List TypeSlot → Option TypeObject
  rewrapFree : TypeObject → List TypeVarValue → TypeObject
  hasOtherFree : TypeObject → List TypeVarValue → Bool
  sameType : TypeObject → TypeObject → Bool
  aliasSubtype : AliasObject → AliasObject → Bool

def aliasMatch (runtime : MakeAliasRuntime) (input proper : TypeObject)
    (reference : GlobalRefValue) (alias : AliasObject) : Option FoundAlias :=
  if !runtime.isType alias || runtime.hasFreeTypevars alias ||
      runtime.printWithoutParams alias || !runtime.isSubtype proper alias then none
  else if alias.isUnionAll then
    let freeBefore := runtime.findFreeTypevars input
    let env := runtime.intersectEnv input (runtime.unbounded alias)
    match runtime.applyAlias alias env with
    | none => none
    | some applied =>
      let applied := runtime.rewrapFree applied freeBefore
      if runtime.hasOtherFree applied freeBefore || !runtime.sameType applied input then none
      else some ⟨reference, alias, env⟩
  else if alias.id = input.id then some ⟨reference, alias, []⟩ else none

def collectAliases (runtime : MakeAliasRuntime) (input proper : TypeObject) : List FoundAlias :=
  (runtime.modulesOf input).map runtime.normalizeModule |>.flatMap fun moduleName =>
    (runtime.names moduleName).filterMap fun name =>
      if runtime.isDefinedGlobal moduleName name && !runtime.isDeprecated moduleName name &&
          runtime.isConst moduleName name then
        let alias := runtime.getGlobal moduleName name
        aliasMatch runtime input proper ⟨moduleName, name⟩ alias
      else none

def chooseAlias (runtime : MakeAliasRuntime) (aliases : List FoundAlias) : Option FoundAlias :=
  let best := if aliases.length > 1 then aliases.filter fun candidate =>
    !(aliases.any fun other =>
      runtime.aliasSubtype other.object candidate.object &&
        !runtime.aliasSubtype candidate.object other.object)
  else aliases
  match best with | [candidate] => some candidate | _ => none

def makeTypealiasBody (runtime : MakeAliasRuntime) (context : Option TypeVarContext)
    (input : TypeObject) : Option FoundAlias :=
  if input.id = runtime.anyId || runtime.isTupleSubtype input then none
  else chooseAlias runtime (collectAliases runtime input (runtime.reapplyContext context input))

structure TypeId where
  id : Nat
  deriving DecidableEq, Repr

structure ScalarIO where
  typeinfo : TypeId
  hexUnsigned : Bool
  deriving DecidableEq, Repr

structure SignedValue where
  value : Int
  deriving DecidableEq, Repr

structure UnsignedValue where
  value : Nat
  typeId : TypeId
  deriving DecidableEq, Repr

structure ScalarRuntime where
  anyType : TypeId
  nothingType : TypeId
  boolType : TypeId
  nonnothingType : TypeId → TypeId
  nonmissingType : TypeId → TypeId
  stringSigned : SignedValue → String
  stringUnsignedDecimal : UnsignedValue → String
  stringUnsignedHex : UnsignedValue → Nat → String
  bitSize : UnsignedValue → Nat
  typeOfUnsigned : UnsignedValue → TypeId
  renderType : TypeId → String

def nonnothingNonmissingBody (runtime : ScalarRuntime) (io : ScalarIO) : TypeId :=
  runtime.nonmissingType (runtime.nonnothingType io.typeinfo)

def showBoolBody (runtime : ScalarRuntime) (io : ScalarIO) (value : Bool) : Out :=
  [if nonnothingNonmissingBody runtime io = runtime.boolType then
    if value then "1" else "0"
   else if value then "true" else "false"]

def showUnsignedBody (runtime : ScalarRuntime) (io : ScalarIO)
    (value : UnsignedValue) : Out :=
  if io.hexUnsigned then
    ["0x", runtime.stringUnsignedHex value ((runtime.bitSize value + 3) / 4)]
  else if io.typeinfo = runtime.typeOfUnsigned value then
    [runtime.stringUnsignedDecimal value]
  else [runtime.renderType (runtime.typeOfUnsigned value), "(",
    runtime.stringUnsignedDecimal value, ")"]

structure PairElement where
  id : Nat
  deriving DecidableEq, Repr

structure PairValue where
  first : PairElement
  second : PairElement
  pairType : TypeId
  firstParameter : TypeId
  secondParameter : TypeId
  deriving DecidableEq, Repr

structure PairIO where
  typeinfo : TypeId
  compact : Bool
  deriving DecidableEq, Repr

structure PairRuntime where
  anyType : TypeId
  pairSupertype : TypeId
  typeOfValue : PairElement → TypeId
  typeOfPair : PairValue → TypeId
  pairIsa : PairValue → TypeId → Bool
  subtype : TypeId → TypeId → Bool
  fieldType : TypeId → Nat → TypeId
  isDelimited : PairIO → PairElement → Bool
  renderValue : PairIO → PairElement → String
  renderType : TypeId → String
  renderTuple : PairElement → PairElement → String
  symbolOfFunction : FunctionValue → SymbolValue
  isOperator : SymbolValue → Bool

def hasTightTypeBody (runtime : PairRuntime) (pair : PairValue) : Bool :=
  runtime.typeOfValue pair.first = pair.firstParameter &&
    runtime.typeOfValue pair.second = pair.secondParameter

def pairDelimitedBody (runtime : PairRuntime) (io : PairIO) (pair : PairValue) : Bool :=
  !(hasTightTypeBody runtime pair || io.typeinfo = runtime.typeOfPair pair)

def pairTypeinfosBody (runtime : PairRuntime) (io : PairIO) (pair : PairValue) : TypeId × TypeId :=
  if runtime.pairIsa pair io.typeinfo && runtime.subtype io.typeinfo runtime.pairSupertype then
    (runtime.fieldType io.typeinfo 1, runtime.fieldType io.typeinfo 2)
  else (runtime.anyType, runtime.anyType)

def showPairBody (runtime : PairRuntime) (io : PairIO) (pair : PairValue) : Out :=
  if pairDelimitedBody runtime io pair then
    [runtime.renderType (runtime.typeOfPair pair), runtime.renderTuple pair.first pair.second]
  else
    let typeinfos := pairTypeinfosBody runtime io pair
    let io1 : PairIO := ⟨typeinfos.1, io.compact⟩
    let io2 : PairIO := ⟨typeinfos.2, io.compact⟩
    let firstDelimited := runtime.isDelimited io1 pair.first
    let secondDelimited := runtime.isDelimited io2 pair.second
    (if firstDelimited then [] else ["("]) ++ [runtime.renderValue io1 pair.first] ++
    (if firstDelimited then [] else [")"]) ++ [if io.compact then "=>" else " => "] ++
    (if secondDelimited then [] else ["("]) ++ [runtime.renderValue io2 pair.second] ++
    (if secondDelimited then [] else [")"])

structure ModuleValue where
  id : Nat
  name : String
  parentId : Nat
  deriving DecidableEq, Repr

structure ModuleRuntime where
  moduleCount : Nat
  lookup : Nat → ModuleValue
  lookupSelf : ∀ module, lookup module.id = module
  isRootModule : ModuleValue → Bool
  showSymbol : String → String

def printFullnameBody (runtime : ModuleRuntime) : Nat → ModuleValue → Out
  | 0, module => [runtime.showSymbol module.name]
  | fuel + 1, module =>
    let parent := runtime.lookup module.parentId
    if parent.id = module.id then [runtime.showSymbol module.name]
    else printFullnameBody runtime fuel parent ++ [".", runtime.showSymbol module.name]

def showModuleBody (runtime : ModuleRuntime) (module : ModuleValue) : Out :=
  if runtime.isRootModule module then [module.name]
  else printFullnameBody runtime runtime.moduleCount module

structure CodeInfoValue where
  slotnames : List SymbolValue
  deriving DecidableEq, Repr

structure SlotRuntime where
  symbolRuntime : SymbolRuntime
  unusedSymbol : SymbolValue

def slotStrings (runtime : SlotRuntime) (slotnames : List SymbolValue) : List String :=
  slotnames.map fun symbol =>
    if symbol.id = runtime.unusedSymbol.id then "#unused#"
    else runtime.symbolRuntime.string symbol

def sourceSlotnamesBody (runtime : SlotRuntime) (slotnames : List SymbolValue) : List String :=
  Remaining.sourceinfoSlotnames (slotStrings runtime slotnames)

structure MethodValue where
  id : Nat
  name : String
  generatorId : Option Nat
  deriving DecidableEq, Repr

structure DebugInfoValue where
  file : String
  line : Int
  deriving DecidableEq, Repr

structure MethodCacheValue where
  ownerUninferred : Bool
  debugInfo : DebugInfoValue
  deriving DecidableEq, Repr

inductive MethodDefValue where
  | method (value : MethodValue)
  | toplevel (id : Nat)
  deriving DecidableEq, Repr

structure MethodInstanceValue where
  id : Nat
  definition : MethodDefValue
  specTypes : TypeExpr
  cache : Option MethodCacheValue
  deriving DecidableEq, Repr

inductive CodeInstanceDef where
  | methodInstance (value : MethodInstanceValue)
  | abiOverride (value : MethodInstanceValue)
  deriving DecidableEq, Repr

structure CodeInstanceValue where
  definition : CodeInstanceDef
  owner : Option Nat
  deriving DecidableEq, Repr

structure MethodRuntime where
  renderMethod : MethodValue → String
  showTupleAsCall : String → TypeExpr → Bool → String
  renderToplevelDef : Nat → String

def showMethodInstanceBody (runtime : MethodRuntime) (miValue : MethodInstanceValue)
    (fromStackframe : Bool) : String :=
  match miValue.definition with
  | .method method =>
    if method.generatorId = some miValue.id then
      "MethodInstance generator for " ++ runtime.renderMethod method
    else "MethodInstance for " ++ runtime.showTupleAsCall method.name miValue.specTypes true
  | .toplevel definition =>
    let base := "Toplevel MethodInstance thunk"
    if fromStackframe then base else match miValue.cache with
    | some cache => if cache.ownerUninferred then
        let location := if cache.debugInfo.file.isEmpty || cache.debugInfo.line < 0 then
          "<unknown>" else cache.debugInfo.file ++ ":" ++ toString cache.debugInfo.line
        base ++ " from " ++ runtime.renderToplevelDef definition ++ " starting at " ++ location
      else base
    | none => base

def showCodeInstanceBody (runtime : MethodRuntime) (codeValue : CodeInstanceValue) : String :=
  let (methodInstance, abi) := match codeValue.definition with
    | .methodInstance value => (value, false)
    | .abiOverride value => (value, true)
  "CodeInstance for " ++ showMethodInstanceBody runtime methodInstance false ++
    (if abi then " (ABI Overridden)" else "") ++
    (if codeValue.owner.isSome then " (foreign)" else "")

structure DelimElement where
  id : Nat
  deriving DecidableEq, Repr

structure DelimArrayValue where
  id : Nat
  slots : List (Option DelimElement)
  deriving DecidableEq, Repr

structure DelimArrayRuntime where
  showCircular : DelimArrayValue → Option String
  render : DelimElement → String

def delimArrayElement (runtime : DelimArrayRuntime) (array : DelimArrayValue)
    (index : Int) : Option String :=
  if index < 1 then none else match array.slots[index.toNat - 1]? with
  | none | some none => none
  | some (some value) => some (runtime.render value)

structure IteratorValue where
  id : Nat
  fuel : Nat
  deriving DecidableEq, Repr

structure IteratorState where
  value : DelimElement
  stateId : Nat
  deriving DecidableEq, Repr

structure DelimIteratorRuntime where
  showCircular : IteratorValue → Option String
  iterateStart : IteratorValue → Option IteratorState
  iterateNext : IteratorValue → Nat → Option IteratorState
  render : DelimElement → String

def skipIterator (runtime : DelimIteratorRuntime) (iterator : IteratorValue) :
    Nat → Nat → Option IteratorState → Option IteratorState
  | 0, _, state => state
  | fuel + 1, count, state =>
    if count ≤ 1 then state else match state with
    | none => none
    | some current => skipIterator runtime iterator fuel (count - 1)
      (runtime.iterateNext iterator current.stateId)

def delimIteratorLoop (runtime : DelimIteratorRuntime) (iterator : IteratorValue)
    (delim : String) (delimOne : Bool) (n : Int) :
    Nat → Int → Bool → Option IteratorState → Out
  | 0, _, _, _ => []
  | _, _, _, none => []
  | fuel + 1, count, first, some current =>
    let shown := runtime.render current.value
    let next := runtime.iterateNext iterator current.stateId
    let count := count + 1
    if next.isNone || count > n then [shown] ++ (if delimOne && first then [delim] else [])
    else [shown, delim, " "] ++
      delimIteratorLoop runtime iterator delim delimOne n fuel count false next

def showDelimIteratorBody (runtime : DelimIteratorRuntime) (iterator : IteratorValue)
    (op delim close : String) (delimOne : Bool) (first : Nat) (n : Int) : Out :=
  [op] ++ (match runtime.showCircular iterator with
  | some marker => [marker]
  | none =>
    let state := skipIterator runtime iterator iterator.fuel first
      (runtime.iterateStart iterator)
    delimIteratorLoop runtime iterator delim delimOne n iterator.fuel
      (Int.ofNat (min first 1) - 1) true state) ++ [close]

structure OperatorRuntime where
  precedence : SymbolValue → Int
  isUnary : SymbolValue → Bool
  isUnaryAndBinary : SymbolValue → Bool
  arrow : Int
  assignment : Int
  controlFlow : Int
  pair : Int
  power : Int
  comparison : Int
  leftPipeId : Nat
  shortCircuitOrId : Nat
  questionId : Nat
  plusId : Nat
  plusPlusId : Nat
  multiplyId : Nat

inductive AssociativityValue where
  | left | right | none
  deriving DecidableEq, Repr

def operatorAssociativityBody (runtime : OperatorRuntime) (symbol : SymbolValue) : AssociativityValue :=
  let precedence := runtime.precedence symbol
  if precedence ∈ [runtime.arrow, runtime.assignment, runtime.controlFlow,
      runtime.pair, runtime.power] ||
      (runtime.isUnary symbol && !runtime.isUnaryAndBinary symbol) ||
      symbol.id = runtime.leftPipeId || symbol.id = runtime.shortCircuitOrId ||
      symbol.id = runtime.questionId then .right
  else if precedence ∈ [0, runtime.comparison] || symbol.id = runtime.plusId ||
      symbol.id = runtime.plusPlusId || symbol.id = runtime.multiplyId then .none
  else .left

structure QuoteNodeValue where
  value : DelimElement
  deriving DecidableEq, Repr

structure ExprValue where
  head : String
  args : List DelimElement
  deriving DecidableEq, Repr

structure ExprContext where
  unquoteFallback : Bool
  deriving DecidableEq, Repr

structure ExprRuntime where
  showQuoteSymbol : ExprContext → JStr → Int → Int → PO
  showQuoteExpr : ExprContext → JE → Int → Int → PO
  showUnquoted : ExprContext → JE → Int → Int → PO
  showFallback : ExprContext → DelimElement → String

structure StyledIO where
  id : Nat
  deriving DecidableEq, Repr

inductive WriteEvent where
  | plain (text : String)
  | styled (text color : String) (bold : Bool)
  deriving DecidableEq, Repr

structure StyleRuntime where
  colorEnabled : StyledIO → Bool
  uppercase : String → String
  renderLine : DelimElement → String
  renderFile : DelimElement → String

structure SymbolPrintRuntime where
  string : SymbolValue → String
  symbolFromString : String → SymbolValue
  isValidIdentifier : SymbolValue → Bool
  isIdentifier : SymbolValue → Bool
  isOperator : SymbolValue → Bool
  escapeRaw : String → String
  quotedSymbolIds : List Nat

def showSymPlain (runtime : SymbolPrintRuntime) (symbol : SymbolValue) : String :=
  if runtime.isValidIdentifier symbol then runtime.string symbol
  else "var\"" ++ runtime.escapeRaw (runtime.string symbol) ++ "\""

def showSymBody (runtime : SymbolPrintRuntime) (symbol : SymbolValue)
    (allowMacroname : Bool) : String :=
  if runtime.isValidIdentifier symbol then runtime.string symbol
  else
    let name := runtime.string symbol
    if allowMacroname && name.startsWith "@" then
      "@" ++ showSymPlain runtime (runtime.symbolFromString (name.drop 1).toString)
    else "var\"" ++ runtime.escapeRaw name ++ "\""

structure SSAValueModel where
  id : Int
  deriving DecidableEq, Repr

inductive SSAWarnClass where
  | strong | mild | none
  deriving DecidableEq, Repr

structure SSARuntime where
  maxId : StyledIO → Int
  warnClass : StyledIO → Int → SSAWarnClass
  warnColor : Unit → String

def showSSABody (runtime : SSARuntime) (io : StyledIO)
    (value : SSAValueModel) : List WriteEvent :=
  let text := "%" ++ toString value.id
  if runtime.maxId io < value.id then [.styled text "red" false]
  else match runtime.warnClass io value.id with
  | .strong => [.styled text "light_red" true]
  | .mild => [.styled text (runtime.warnColor ()) true]
  | .none => [.plain text]

structure GlobalRefModel where
  moduleValue : ModuleValue
  name : SymbolValue
  deriving DecidableEq, Repr

structure GlobalRefRuntime where
  symbolRuntime : SymbolPrintRuntime
  renderModule : ModuleValue → String

def showGlobalRefBody (runtime : GlobalRefRuntime) (reference : GlobalRefModel)
    (allowMacroname : Bool) : String :=
  let name := runtime.symbolRuntime.string reference.name
  let quoted := !runtime.symbolRuntime.isIdentifier reference.name && !name.startsWith "@"
  let parens := quoted && (!runtime.symbolRuntime.isOperator reference.name ||
    runtime.symbolRuntime.quotedSymbolIds.contains reference.name.id)
  runtime.renderModule reference.moduleValue ++ "." ++
    (if quoted then ":" else "") ++ (if parens then "(" else "") ++
    showSymBody runtime.symbolRuntime reference.name allowMacroname ++
    (if parens then ")" else "")

structure BindingPartitionModel where
  owner : GlobalRefModel
  deriving DecidableEq, Repr

structure SlotNumberModel where
  id : Nat
  deriving DecidableEq, Repr

structure SlotIO where
  sourceSlotnames : Option (List String)
  deriving DecidableEq, Repr

def showSlotBody (io : SlotIO) (slot : SlotNumberModel) : R String :=
  match io.sourceSlotnames with
  | some names => if slot.id ≤ names.length then
      if slot.id = 0 then .error .boundsError else match names[slot.id - 1]? with
      | some name => .ok name
      | none => .error .boundsError
    else .ok ("_" ++ toString slot.id)
  | none => .ok ("_" ++ toString slot.id)

structure LineNodeModel where
  line : DelimElement
  file : Option DelimElement
  deriving DecidableEq, Repr

inductive QuoteContent where
  | symbol (value : SymbolValue)
  | block (value : ExprValue)
  | other (value : DelimElement)
  deriving DecidableEq, Repr

structure QuoteNodeModel where
  value : QuoteContent
  deriving DecidableEq, Repr

structure QuoteRuntime where
  symbols : SymbolPrintRuntime
  quotedIds : List Nat
  renderStringRepr : String → String
  showBlock : ExprContext → String → ExprValue → Int → Int → String
  showUnquotedOther : ExprContext → DelimElement → Int → Int → String
  showOther : ExprContext → DelimElement → String
  showExpr : ExprContext → ExprValue → String

def showQuotedBody (runtime : QuoteRuntime) (io : ExprContext) (value : QuoteContent)
    (indent quoteLevel : Int) : String :=
  match value with
  | .symbol symbol =>
    let name := runtime.symbols.string symbol
    if runtime.quotedIds.contains symbol.id then ":(" ++ name ++ ")"
    else if runtime.symbols.isIdentifier symbol ||
        (runtime.symbols.isOperator symbol && name ≠ "'") then ":" ++ name
    else "Symbol(" ++ runtime.renderStringRepr name ++ ")"
  | .block expression =>
    runtime.showBlock ⟨false⟩ "quote" expression indent quoteLevel ++ "end"
  | .other other => ":(" ++ runtime.showUnquotedOther io other (indent + 2) (-1) ++ ")"

def showQuoteNodeBody (runtime : QuoteRuntime) (io : ExprContext)
    (node : QuoteNodeModel) (indent : Int) : String :=
  match node.value with
  | .symbol symbol => showQuotedBody runtime io (.symbol symbol) indent 0
  | .block expression => "$(QuoteNode(" ++
      runtime.showExpr io expression ++ "))"
  | .other other => "$(QuoteNode(" ++ runtime.showOther io other ++ "))"

inductive ImportNode where
  | symbol (value : SymbolValue)
  | globalRef (value : GlobalRefModel)
  | expr (head : String) (args : List ImportNode)
  | other (id : Nat)
  deriving Repr

def validImportPathBody (node : ImportNode) (allowAs : Bool) : Bool :=
  let node := match node with
    | .expr "as" [path, _] => if allowAs then path else node
    | _ => node
  match node with
  | .expr "." args => !args.isEmpty && args.all fun arg => match arg with
    | .symbol _ => true
    | _ => false
  | _ => false

structure ImportRuntime where
  symbols : SymbolPrintRuntime
  renderUnquoted : ImportNode → Int → Int → Int → String

def showImportPathBody (runtime : ImportRuntime) : ImportNode → Int → R String
  | node@(.symbol _), _ => .ok (runtime.renderUnquoted node 0 0 0)
  | node@(.globalRef _), _ => .ok (runtime.renderUnquoted node 0 0 0)
  | node@(.other _), _ => .ok (runtime.renderUnquoted node 0 0 0)
  | .expr ":" [], quoteLevel => .ok (runtime.renderUnquoted (.expr ":" []) 0 0 quoteLevel)
  | .expr ":" (first :: rest), quoteLevel => do
    let firstText ← showImportPathBody runtime first quoteLevel
    let restText ← rest.mapM (showImportPathBody runtime · quoteLevel)
    .ok (firstText ++ ": " ++ ", ".intercalate restText)
  | .expr "." args, _ => do
    let pieces ← args.zipIdx.mapM fun (arg, index) => match arg with
      | .symbol symbol =>
        let name := runtime.symbols.string symbol
        let shown := if name = "." then "." else if name = ".." then "(..)"
          else showSymBody runtime.symbols symbol (index + 1 = args.length)
        .ok (shown ++ if index + 1 < args.length && name ≠ "." then "." else "")
      | _ => .error .typeError
    .ok (String.join pieces)
  | node@(.expr _ _), quoteLevel => .ok (runtime.renderUnquoted node 0 0 quoteLevel)

def allowMacronameBody (runtime : SymbolPrintRuntime) (node : ImportNode) : ImportNode :=
  let shouldWrap := match node with
    | .symbol symbol => (runtime.string symbol).startsWith "@"
    | .globalRef _ => true
    | .expr "." [_, .expr "quote" _] => true
    | .expr "." [_, _] => false
    | _ => false
  if shouldWrap then .expr "macroname" [node] else node

def isCoreMacroBody (reference : GlobalRefModel) (macroName : SymbolValue) : Bool :=
  reference.moduleValue.name = "Core" && reference.name.id = macroName.id

structure ExprFallbackValue where
  head : DelimElement
  args : List DelimElement
  deriving DecidableEq, Repr

structure ExprFallbackRuntime where
  render : DelimElement → String

def showExprFallbackBody (runtime : ExprFallbackRuntime) (expression : ExprFallbackValue) : String :=
  "$(Expr(" ++ runtime.render expression.head ++
    String.join (expression.args.map fun arg => ", " ++ runtime.render arg) ++ "))"

inductive GeneratorExpr where
  | base (body : DelimElement) (ranges : List DelimElement)
  | flatten (inner : GeneratorExpr) (ranges : List DelimElement)
  deriving Repr

structure GeneratorRuntime where
  showUnquoted : DelimElement → Int → Int → Int → String
  showList : List DelimElement → String → Int → Int → Int → String

def collectGenerator : GeneratorExpr → DelimElement × List (List DelimElement)
  | .base body ranges => (body, [ranges])
  | .flatten inner ranges =>
    let result := collectGenerator inner
    (result.1, ranges :: result.2)

def showGeneratorBody (runtime : GeneratorRuntime) (expression : GeneratorExpr)
    (indent quoteLevel : Int) : String :=
  let (body, ranges) := collectGenerator expression
  runtime.showUnquoted body indent 0 quoteLevel ++
    String.join (ranges.map fun range => " for " ++
      runtime.showList range ", " indent 0 quoteLevel)

inductive AstValue where
  | symbol (value : SymbolValue)
  | real (value : Int)
  | string (value : String)
  | bool (value : Bool)
  | expr (head : String) (args : List AstValue)
  | globalRef (value : GlobalRefModel)
  | binding (value : BindingPartitionModel)
  | quoteNode (value : DelimElement)
  | other (id : Nat)
  deriving Repr

structure AstRuntime where
  renderUnquoted : AstValue → Int → Int → Int → String
  renderFallback : AstValue → String
  isOperator : SymbolValue → Bool
  isValidIdentifier : SymbolValue → Bool
  unaryOperatorIds : List Nat
  callDelimiters : String → String × String

def astIsQuoted : AstValue → Bool
  | .quoteNode _ => true
  | .expr head args => (head = "quote" || head = "inert") && args.length = 1
  | _ => false

def astListItem (runtime : AstRuntime) (item : AstValue) (first : Bool)
    (indent prec quoteLevel : Int) (encloseOperators keyword : Bool) : String :=
  let unaryCall := match item with
    | .expr "call" (.symbol callee :: _) => runtime.unaryOperatorIds.contains callee.id
    | _ => false
  let negativeReal := match item with | .real value => value < 0 | _ => false
  let operatorSymbol := match item with
    | .symbol symbol => runtime.isOperator symbol && runtime.isValidIdentifier symbol
    | _ => false
  let parens := !astIsQuoted item &&
    ((first && prec ≥ 14 && (unaryCall || negativeReal)) ||
      (encloseOperators && operatorSymbol))
  let shown := match item with
    | .expr "kw" [lhs, rhs] => if keyword then
        runtime.renderUnquoted (.expr "=" [lhs, rhs]) indent (if parens then 0 else prec) quoteLevel
      else runtime.renderUnquoted item indent (if parens then 0 else prec) quoteLevel
    | .expr "=" [_, _] => if keyword then runtime.renderFallback item
      else runtime.renderUnquoted item indent (if parens then 0 else prec) quoteLevel
    | _ => runtime.renderUnquoted item indent (if parens then 0 else prec) quoteLevel
  (if parens then "(" else "") ++ shown ++ if parens then ")" else ""

def showAstListBody (runtime : AstRuntime) (items : List AstValue) (separator : String)
    (indent prec quoteLevel : Int) (encloseOperators keyword : Bool) : String :=
  String.join (items.zipIdx.map fun (item, index) =>
    (if index = 0 then "" else separator) ++
      astListItem runtime item (index = 0) (indent + 4) prec quoteLevel encloseOperators keyword)

def showAstBlockBody (runtime : AstRuntime) (head : String) (arguments : List AstValue)
    (body : AstValue) (indent quoteLevel : Int) : String :=
  let argsText := if arguments.isEmpty then "" else " " ++
    showAstListBody runtime arguments (if head = "elseif" then " " else ", ") indent 0 quoteLevel false false
  let bodyIndent := if head = "module" || head = "baremodule" then indent else indent + 4
  let expressions := match body with
    | .expr "block" args | .expr "quote" args => args
    | _ => [body]
  head ++ argsText ++ String.join (expressions.map fun expression =>
    "\n" ++ String.ofList (List.replicate bodyIndent.toNat ' ') ++
      runtime.renderUnquoted expression bodyIndent (-1) quoteLevel) ++
    "\n" ++ String.ofList (List.replicate indent.toNat ' ')

def showAstCallBody (runtime : AstRuntime) (head : String) (function : AstValue)
    (arguments : List AstValue) (indent quoteLevel : Int) (keyword : Bool) : String :=
  let (openToken, closeToken) := runtime.callDelimiters head
  let direct := match function with
    | .symbol symbol =>
      (symbol.id ≠ 0 && !(head = "." && runtime.isOperator symbol)) ||
        !runtime.isValidIdentifier symbol
    | .expr exprHead _ => exprHead = "." || exprHead = "curly" || exprHead = "macroname"
    | .globalRef _ | .binding _ => true
    | _ => false
  let functionText := runtime.renderUnquoted function indent 0 quoteLevel
  let functionText := if direct then functionText else "(" ++ functionText ++ ")"
  let functionText := functionText ++ if head = "." then "." else ""
  match arguments with
  | .expr "parameters" parameters :: positional =>
    functionText ++ openToken ++
      showAstListBody runtime positional ", " indent 0 quoteLevel false keyword ++ "; " ++
      showAstListBody runtime parameters ", " indent 0 quoteLevel false keyword ++ closeToken
  | _ => functionText ++ openToken ++
      showAstListBody runtime arguments ", " indent 0 quoteLevel false keyword ++ closeToken

def astIsExpr (value : AstValue) (head : String) : Bool := match value with
  | .expr actual _ => actual = head
  | _ => false

def astSymbol? : AstValue → Option SymbolValue
  | .symbol symbol => some symbol
  | .globalRef reference => some reference.name
  | _ => none

structure FullExprRuntime where
  ast : AstRuntime
  operators : OperatorRuntime
  symbols : SymbolPrintRuntime
  infixHeads : List String
  wideInfixHeads : List String
  parenHeads : List (String × (String × String))
  callHeads : List String
  isPostfix : SymbolValue → Bool
  showGenerator : AstValue → Int → Int → String
  showImport : AstValue → Int → String
  validImport : AstValue → Bool → Bool
  allowMacroname : AstValue → AstValue
  isCoreMacro : AstValue → String → Bool
  showQuoted : AstValue → Int → Int → String
  showLine : List AstValue → String
  escapeString : String → String
  fallback : AstValue → String

def showExprFullBody (runtime : FullExprRuntime) (unquoteFallback beginsym : Bool)
    (expression : AstValue) (indent prec quoteLevel : Int) : String :=
  match expression with
  | nonexpr@(.symbol _) | nonexpr@(.real _) | nonexpr@(.string _) |
      nonexpr@(.bool _) | nonexpr@(.globalRef _) | nonexpr@(.binding _) |
      nonexpr@(.quoteNode _) | nonexpr@(.other _) =>
    runtime.ast.renderUnquoted nonexpr indent prec quoteLevel
  | expr@(.expr head args) =>
    let nargs := args.length
    let render (value : AstValue) (p : Int := 0) :=
      runtime.ast.renderUnquoted value indent p quoteLevel
    let list (values : List AstValue) (separator : String) (p : Int := 0)
        (enclose : Bool := false) (keyword : Bool := false) :=
      showAstListBody runtime.ast values separator indent p quoteLevel enclose keyword
    if head = "." && (nargs ≠ 2 || !astIsExpr (args.getD 1 (.other 0)) "tuple") then
      match args with
      | [.symbol symbol] => if runtime.symbols.isOperator symbol then
          "(." ++ runtime.symbols.string symbol ++ ")" else runtime.fallback expr
      | [item, field] => if astIsQuoted field then
          let itemText := render item
          let itemParens := !astIsQuoted item && match item with
            | .symbol symbol => !runtime.symbols.isIdentifier symbol
            | .expr "." _ => false
            | _ => true
          let fieldText := render field
          (if itemParens then "(" else "") ++ itemText ++ (if itemParens then ")" else "") ++
            "." ++ fieldText
        else runtime.fallback expr
      | _ => runtime.fallback expr
    else if runtime.infixHeads.contains head && nargs = 2 then
      let precedence := runtime.operators.precedence (runtime.symbols.symbolFromString head)
      let separator := if runtime.wideInfixHeads.contains head then " " ++ head ++ " " else head
      let shown := list args separator precedence true
      if precedence ≤ prec then "(" ++ shown ++ ")" else shown
    else if head = "tuple" then
      match args with
      | .expr "parameters" parameters :: positional =>
        "(" ++ list positional ", " ++ (if positional.length = 1 then "," else "") ++ ";" ++
          (if parameters.isEmpty then "" else " " ++ list parameters ", " 0 false true) ++ ")"
      | _ => "(" ++ list args ", " ++ (if nargs = 1 then "," else "") ++ ")"
    else if runtime.parenHeads.any (fun pair => pair.1 = head) ||
        ["typed_vcat", "typed_hcat", "typed_ncat"].contains head then
      let typed := head.startsWith "typed_"
      let normalized := if head = "typed_vcat" then "vcat" else if head = "typed_hcat" then "hcat"
        else if head = "typed_ncat" then "ncat" else head
      let values := if typed then args.drop 1 else args
      let typePrefix := if typed then match args with | first :: _ => render first | _ => "" else ""
      let delimiters := (runtime.parenHeads.find? (fun pair => pair.1 = normalized)).map (·.2) |>.getD ("[", "]")
      let separator := if ["vcat", "bracescat"].contains normalized then "; "
        else if ["hcat", "row"].contains normalized then " " else ", "
      typePrefix ++ delimiters.1 ++ list values separator ++ delimiters.2
    else if (head = "'" && nargs = 1) || (head = "call" && nargs = 2 &&
        match args[0]? with
        | some (AstValue.symbol symbol) => runtime.isPostfix symbol && runtime.symbols.string symbol != "'"
        | _ => false) then
      let (operatorText, operand) := if head = "'" then ("'", args.getD 0 (.other 0)) else
        match args with
        | .symbol symbol :: operand :: _ => (runtime.symbols.string symbol, operand)
        | _ => ("", .other 0)
      let enclosed := match operand with
        | .expr _ _ => true
        | .symbol symbol => runtime.symbols.isOperator symbol
        | _ => false
      (if enclosed then "(" else "") ++ render operand ++
        (if enclosed then ")" else "") ++ operatorText
    else if head = "call" && nargs ≥ 1 then
      match args with
      | function :: arguments =>
        let symbol := astSymbol? function
        let precedence := match symbol with | some value => runtime.operators.precedence value | none => 0
        let keyword := arguments.any (astIsExpr · "kw") ||
          match arguments with | first :: _ => astIsExpr first "parameters" | [] => false
        if keyword then showAstCallBody runtime.ast head function arguments indent quoteLevel true
        else if match symbol with | some value => runtime.symbols.string value == "*" | none => false then
          match arguments with
          | [.real coefficient, .symbol symbolValue] =>
            let first := (runtime.symbols.string symbolValue).toList.headD 'a'
            let forbidden := ['e', 'E', 'f'] ++ if coefficient = 0 then ['b', 'o', 'x'] else []
            if !forbidden.contains first then toString coefficient ++ runtime.symbols.string symbolValue
            else showAstCallBody runtime.ast head function arguments indent quoteLevel true
          | _ => showAstCallBody runtime.ast head function arguments indent quoteLevel true
        else if match symbol with
          | some value => arguments.length = 1 && runtime.operators.isUnary value
          | none => false then
          render function ++ render (arguments.headD (.other 0)) precedence
        else if precedence > 0 && arguments.length = 2 then
          let separator := match symbol with | some value => " " ++ runtime.symbols.string value ++ " " | none => " "
          let shown := list arguments separator precedence true
          if precedence ≤ prec then "(" ++ shown ++ ")" else shown
        else showAstCallBody runtime.ast head function arguments indent quoteLevel true
      | [] => runtime.fallback expr
    else if ["new", "splatnew"].contains head then
      "%" ++ head ++ "(" ++ list args ", " ++ ")"
    else if runtime.callHeads.contains head && nargs ≥ 1 then
      let function := args.getD 0 (.other 0)
      let callArguments := if head = "." then match args[1]? with
        | some (AstValue.expr _ values) => values
        | _ => []
        else args.drop 1
      showAstCallBody runtime.ast head function callArguments indent quoteLevel (head != "curly")
    else if head = "typed_comprehension" && nargs = 2 then
      render (args.getD 0 (.other 0)) ++ "[" ++
        runtime.showGenerator (args.getD 1 (.other 0)) indent quoteLevel ++ "]"
    else if head = "comprehension" && nargs = 1 then
      "[" ++ runtime.showGenerator (args.getD 0 (.other 0)) indent quoteLevel ++ "]"
    else if (head = "generator" && nargs ≥ 2) || (head = "flatten" && nargs = 1) then
      "(" ++ runtime.showGenerator expr indent quoteLevel ++ ")"
    else if head = "filter" && nargs = 2 then
      render (args.getD 1 (.other 0)) ++ " if " ++ render (args.getD 0 (.other 0))
    else if head = "comparison" && nargs ≥ 3 && nargs % 2 = 1 then
      list args " "
    else if ["for", "while", "function", "macro", "if", "elseif", "let"].contains head &&
        (nargs = 1 || nargs = 2 || ((head = "if" || head = "elseif") && nargs = 3)) then
      let arguments := if nargs ≥ 2 then [args.getD 0 (.other 0)] else []
      let body := args.getD (nargs - 1) (.expr "block" [])
      showAstBlockBody runtime.ast head arguments body indent quoteLevel ++ "end"
    else if head = "do" && nargs = 2 then
      render (args.getD 0 (.other 0)) (-1) ++ " do" ++
        render (args.getD 1 (.other 0)) ++ "\n" ++
        String.ofList (List.replicate indent.toNat ' ') ++ "end"
    else if head = "module" && (nargs = 3 || nargs = 4) then
      let bare := match args with
        | _ :: .bool flag :: _ => !flag
        | .bool flag :: _ => !flag
        | _ => false
      let name := args.getD (nargs - 2) (.other 0)
      let body := args.getD (nargs - 1) (.expr "block" [])
      showAstBlockBody runtime.ast (if bare then "baremodule" else "module") [name]
        body indent quoteLevel ++ "end"
    else if head = "struct" && nargs = 3 then
      let mutable := match args[0]? with | some (.bool value) => value | _ => false
      showAstBlockBody runtime.ast (if mutable then "mutable struct" else "struct")
        [args.getD 1 (.other 0)] (args.getD 2 (.expr "block" [])) indent quoteLevel ++ "end"
    else if head = "primitive" && nargs = 2 then "primitive type " ++ list args " " ++ " end"
    else if head = "abstract" && nargs = 1 then "abstract type " ++ list args " " ++ " end"
    else if head = "return" && nargs = 1 && match args[0]? with
      | some (AstValue.other 0) => true
      | _ => false then
      "return"
    else if ["::", "<:", ">:"].contains head && nargs = 1 then head ++ render (args.getD 0 (.other 0))
    else if head = "..." && nargs = 1 then render (args.getD 0 (.other 0)) ++ "..."
    else if nargs = 0 && ["break", "continue"].contains head then head
    else if (nargs = 1 && ["return", "const"].contains head) || ["local", "global"].contains head then
      head ++ " " ++ list args ", "
    else if ["export", "public"].contains head then
      head ++ " " ++ list (args.map runtime.allowMacroname) ", "
    else if head = "macrocall" && nargs ≥ 2 then
      if runtime.isCoreMacro (args.getD 0 (.other 0)) "@cmd" then
        "`" ++ render (args.getD 2 (.other 0)) ++ "`"
      else if ["@int128_str", "@uint128_str", "@big_str"].any
          (runtime.isCoreMacro (args.getD 0 (.other 0))) then render (args.getD 2 (.other 0))
      else match args with
        | .symbol macroName :: _ :: .string text :: suffix =>
          let name := runtime.symbols.string macroName
          if name.startsWith "@" && name.endsWith "_str" then
            let literalName := String.ofList (name.toList.drop 1 |>.dropLast.dropLast.dropLast.dropLast)
            literalName ++ "\"" ++ runtime.escapeString text ++ "\"" ++
              match suffix with | [value] => render value | _ => ""
          else showAstCallBody runtime.ast "call" (runtime.allowMacroname (args.getD 0 (.other 0)))
            (args.drop 2) indent quoteLevel false
        | _ => showAstCallBody runtime.ast "call" (runtime.allowMacroname (args.getD 0 (.other 0)))
          (args.drop 2) indent quoteLevel false
    else if head = "macroname" && nargs = 1 then render (args.getD 0 (.other 0))
    else if head = "line" && 1 ≤ nargs && nargs ≤ 2 then runtime.showLine args
    else if head = "try" && 3 ≤ nargs && nargs ≤ 5 then
      showAstBlockBody runtime.ast "try" [] (args.getD 0 (.other 0)) indent quoteLevel ++ "end"
    else if head = "block" then
      if beginsym then "(" ++ list args ";\n" ++ (if args.isEmpty then ";;)" else ";)")
      else showAstBlockBody runtime.ast "begin" [] expr indent quoteLevel ++ "end"
    else if head = "quote" && nargs = 1 then runtime.showQuoted (args.getD 0 (.other 0)) indent (quoteLevel + 1)
    else if head = "gotoifnot" && nargs = 2 then
      "unless " ++ render (args.getD 0 (.other 0)) ++ " goto %" ++ render (args.getD 1 (.other 0))
    else if head = "string" && nargs = 1 then match args[0]? with
      | some (AstValue.string text) => "\"" ++ runtime.escapeString text ++ "\""
      | _ => runtime.fallback expr
    else if head = "null" then "nothing"
    else if head = "string" then "\"" ++ String.join (args.map fun value => match value with
      | .string text => runtime.escapeString text
      | _ => "$(" ++ render value ++ ")") ++ "\""
    else if (head = "&" || head = "$") && nargs = 1 then
      if head = "$" && unquoteFallback then runtime.fallback expr
      else head ++ render (args.getD 0 (.other 0))
    else if head = "where" && nargs > 1 then
      let tail := if nargs = 2 then render (args.getD 1 (.other 0))
        else "{" ++ list (args.drop 1) ", " ++ "}"
      (if prec ≥ 1 then "(" else "") ++ render (args.getD 0 (.other 0)) ++
        " where " ++ tail ++ if prec ≥ 1 then ")" else ""
    else if (head = "import" || head = "using") && args.all (runtime.validImport · true) then
      head ++ " " ++ ", ".intercalate (args.map (runtime.showImport · quoteLevel))
    else if head = "as" && nargs = 2 && runtime.validImport (args.getD 0 (.other 0)) false then
      runtime.showImport (args.getD 0 (.other 0)) quoteLevel ++ " as " ++ render (args.getD 1 (.other 0))
    else if head = "meta" && nargs ≥ 1 then "# meta: " ++ list args " "
    else runtime.fallback expr

def demangleFunctionBody (name : String) : String :=
  let pieces := name.splitOn "#"
  match pieces with
  | first :: _ :: _ => if first.isEmpty then name else first
  | _ => name

structure StacktraceIO where
  backtrace : Bool
  displaysize : Int × Int
  deriving DecidableEq, Repr

def printWithinStacktraceBody (io : StacktraceIO) (pieces : List String)
    (color : String) (bold : Bool) : List WriteEvent :=
  let text := String.join pieces
  if io.backtrace then [.styled text color bold] else [.plain text]

structure TypeLimitContext where
  limitedFlag : Option Bool
  displaysize : Int × Int
  deriving DecidableEq, Repr

structure TypeLimitRuntime where
  depthLimit : String → Int → String
  byteSize : String → Nat

def typeLimitedBody (runtime : TypeLimitRuntime) (context : TypeLimitContext)
    (text : String) : String × Option Bool :=
  match context.limitedFlag with
  | none => (text, none)
  | some current =>
    let limited := runtime.depthLimit text (max context.displaysize.2 120)
    (limited, some (current || runtime.byteSize limited < runtime.byteSize text))

structure SignatureRuntime where
  unwrapUnionall : TypeObject → TypeObject
  subtypeFunction : TypeObject → Bool
  asDataType : TypeObject → Option DataTypeValue
  parametersEmpty : DataTypeValue → Bool
  isSelf : DataTypeValue → Bool
  parentModule : DataTypeValue → String
  isExported : String → String → Bool
  mainModule : String
  renderModule : String → String
  renderSymbol : String → String
  isType : TypeObject → Bool
  typeParameter : TypeObject → Option TypeObject
  isTypeVar : TypeObject → Bool
  isUnionAll : TypeObject → Bool
  wrapperIsSelf : TypeObject → Bool
  renderType : TypeObject → String

def showSignatureFunctionBody (runtime : SignatureRuntime) (input : TypeObject)
    (demangle : Bool) (argumentName : String) (html qualified : Bool) : String :=
  let unwrapped := runtime.unwrapUnionall input
  match runtime.asDataType unwrapped with
  | some datatype =>
    if runtime.subtypeFunction input && runtime.parametersEmpty datatype && runtime.isSelf datatype then
      let moduleName := runtime.parentModule datatype
      let qualifier := if qualified && !runtime.isExported moduleName datatype.typeName.singletonName &&
          moduleName ≠ runtime.mainModule then runtime.renderModule moduleName ++ "." else ""
      let name := if demangle then demangleFunctionBody datatype.typeName.singletonName
        else datatype.typeName.singletonName
      qualifier ++ runtime.renderSymbol name
    else if runtime.isType input then match runtime.typeParameter input with
      | some parameter => if runtime.isTypeVar parameter then
          if html then "(" ++ argumentName ++ "::<b>" ++ runtime.renderType input ++ "</b>)"
          else "(" ++ argumentName ++ "::" ++ runtime.renderType input ++ ")"
        else
          let parens := runtime.isUnionAll parameter && !runtime.wrapperIsSelf parameter
          (if parens then "(" else "") ++ runtime.renderType parameter ++
            (if parens then ")" else "")
      | none => runtime.renderType input
    else if html then "(" ++ argumentName ++ "::<b>" ++ runtime.renderType input ++ "</b>)"
    else "(" ++ argumentName ++ "::" ++ runtime.renderType input ++ ")"
  | none => if runtime.isType input then match runtime.typeParameter input with
      | some parameter => runtime.renderType parameter
      | none => runtime.renderType input
    else if html then "(" ++ argumentName ++ "::<b>" ++ runtime.renderType input ++ "</b>)"
    else "(" ++ argumentName ++ "::" ++ runtime.renderType input ++ ")"

inductive SignatureType where
  | tupleRoot
  | datatype (parameters : List TypeObject)
  | unionAll (binder : TypeVarValue) (body : SignatureType)
  deriving Repr

structure TupleCallRuntime where
  symbols : SymbolPrintRuntime
  signature : SignatureRuntime
  renderType : TypeObject → Bool → String
  isSplatKeyword : TypeObject → Bool
  renderMethodParams : List TypeVarValue → String
  limit : String → String

def unwrapSignature : SignatureType → List TypeVarValue × List TypeObject
  | .tupleRoot => ([], [])
  | .datatype parameters => ([], parameters)
  | .unionAll binder body =>
    let result := unwrapSignature body
    (binder :: result.1, result.2)

def showTupleCallBody (runtime : TupleCallRuntime) (name : SymbolValue)
    (signature : SignatureType) (demangle : Bool)
    (kwargs : Option (List (SymbolValue × TypeObject)))
    (argumentNames : Option (List SymbolValue)) (qualified hasFirst : Bool) : String :=
  match signature with
  | .tupleRoot => runtime.symbols.string
      (if demangle then runtime.symbols.symbolFromString
        (demangleFunctionBody (runtime.symbols.string name)) else name) ++ "(...)"
  | _ =>
    let (binders, parameters) := unwrapSignature signature
    let start := if hasFirst then 1 else 0
    let functionText := if hasFirst then match parameters with
      | first :: _ => showSignatureFunctionBody runtime.signature first demangle "" false qualified
      | [] => ""
      else ""
    let showNames := match argumentNames with
      | some names => names.length == parameters.length
      | none => false
    let arguments := (parameters.drop start).zipIdx.map fun (parameter, offset) =>
      let index := offset + start
      let argName := if showNames then match argumentNames with
        | some names => match names[index]? with | some symbol => runtime.symbols.string symbol | none => ""
        | none => "" else ""
      (if argName.isEmpty then "" else argName) ++ "::" ++ runtime.renderType parameter true
    let keywords := match kwargs with
      | none => ""
      | some pairs => "; " ++ ", ".intercalate (pairs.map fun pair =>
        runtime.symbols.string pair.1 ++ if runtime.isSplatKeyword pair.2 then "..."
          else "::" ++ runtime.renderType pair.2 true)
    runtime.limit (functionText ++ "(" ++ ", ".intercalate arguments ++ keywords ++ ")" ++
      runtime.renderMethodParams binders)

structure TypeColorRuntime where
  renderType : TypeObject → StacktraceIO → String

def firstBrace (text : String) : Option Nat := text.toList.findIdx? (fun char => char = '{')

def printTypeBicolorText (text color innerColor : String) (useColor : Bool) : List WriteEvent :=
  if !useColor then [.plain text]
  else match firstBrace text with
  | none => [.styled text color false]
  | some index =>
    let chars := text.toList
    let outer := String.ofList (chars.take index)
    if text.endsWith "..." then
      let inner := String.ofList ((chars.drop index).dropLast.dropLast.dropLast)
      [.styled outer color false, .styled inner innerColor false, .styled "..." color false]
    else [.styled outer color false, .styled (String.ofList (chars.drop index)) innerColor false]

inductive BindingNode where
  | other (id : Nat)
  | quote (value : BindingNode)
  | symbol (value : SymbolValue)
  | globalRef (value : GlobalRefModel)
  | expr (head : String) (args : List BindingNode)
  deriving Repr

inductive BindingResult where
  | value (node : BindingNode)
  | module (value : ModuleValue)
  | nothing
  deriving Repr

structure BindingRuntime where
  mainModule : ModuleValue
  baseModuleId : Nat
  coreModuleId : Nat
  getfieldSymbolId : Nat
  isDefined : GlobalRefModel → Bool
  isConst : GlobalRefModel → Bool
  getModule : GlobalRefModel → Option ModuleValue

def resolveGlobalBody (runtime : BindingRuntime) (reference : GlobalRefModel) : BindingResult :=
  if !runtime.isDefined reference || !runtime.isConst reference then .nothing
  else match runtime.getModule reference with
  | some module => .module module
  | none => .nothing

def resolveBindingBody (runtime : BindingRuntime) : Nat → BindingNode → BindingResult
  | 0, node => .value node
  | _, .other id => .value (.other id)
  | _, .quote value => .value value
  | fuel + 1, .symbol symbol =>
    resolveGlobalBody runtime ⟨runtime.mainModule, symbol⟩
  | _, .globalRef reference => resolveGlobalBody runtime reference
  | fuel + 1, .expr "." [parent, .symbol name] =>
    match resolveBindingBody runtime fuel parent with
    | .module module => resolveGlobalBody runtime ⟨module, name⟩
    | _ => .nothing
  | _, .expr _ _ => .nothing

def isModuleCallBody (runtime : BindingRuntime) (expression : BindingNode) : Bool :=
  match expression with
  | .expr "call" (BindingNode.globalRef callee :: target :: _) =>
    let getfield := callee.name.id = runtime.getfieldSymbolId &&
      (callee.moduleValue.id = runtime.baseModuleId || callee.moduleValue.id = runtime.coreModuleId)
    getfield && match resolveBindingBody runtime 32 target with
      | .module _ => true
      | _ => false
  | _ => false

structure TypeVarShowRuntime where
  bottomId : Nat
  anyId : Nat
  renderName : String → String
  isUnionAll : TypeObject → Bool
  printWithoutParams : TypeObject → Bool
  renderBound : TypeObject → String

def typevarInEnv (context : TypeVarContext) (typevar : TypeVarValue) : Bool :=
  context.dict.any fun binding => binding.1 == "unionall_env" && match binding.2 with
    | .typeVar value => value.id == typevar.id
    | .other _ => false

def showBoundBody (runtime : TypeVarShowRuntime) (bound : TypeObject) : String :=
  let parens := runtime.isUnionAll bound && !runtime.printWithoutParams bound
  (if parens then "(" else "") ++ runtime.renderBound bound ++ if parens then ")" else ""

def showTypevarBody (runtime : TypeVarShowRuntime) (context : TypeVarContext)
    (typevar : TypeVarValue) : String :=
  let inEnv := typevarInEnv context typevar
  let lower : TypeObject := ⟨typevar.lower⟩
  let upper : TypeObject := ⟨typevar.upper⟩
  let name := runtime.renderName typevar.name
  let lowerText := if !inEnv && typevar.lower ≠ runtime.bottomId then
    if typevar.upper = runtime.anyId then name ++ ">:" ++ showBoundBody runtime lower
    else showBoundBody runtime lower ++ "<:" ++ name
    else name
  lowerText ++ if !inEnv && typevar.upper ≠ runtime.anyId then
    "<:" ++ showBoundBody runtime upper else ""

structure VarargValue where
  typeField : Option TypeObject
  lengthField : Option DelimElement
  deriving Repr

structure VarargRuntime where
  renderType : TypeObject → String
  renderLength : DelimElement → String

def showVarargBody (runtime : VarargRuntime) (value : VarargValue) : String :=
  "Vararg" ++ match value.typeField with
  | none => ""
  | some type => "{" ++ runtime.renderType type ++ match value.lengthField with
    | none => "}"
    | some length => ", " ++ runtime.renderLength length ++ "}"

structure CodeInfoModel where
  id : Nat
  slotnames : Option (List SymbolValue)
  deriving DecidableEq, Repr

structure CodeInfoRuntime where
  slotRuntime : SlotRuntime
  debugInfoConfig : String → CodeInfoModel → String
  showIR : CodeInfoModel → Option (List String) → String → String

def showCodeInfoBody (runtime : CodeInfoRuntime) (source : CodeInfoModel)
    (debugInfo : String) : String :=
  let normalized := source.slotnames.map (sourceSlotnamesBody runtime.slotRuntime)
  let config := runtime.debugInfoConfig debugInfo source
  "CodeInfo(\n" ++ runtime.showIR source normalized config ++ ")"

structure IRNodeRuntime where
  renderUnquoted : DelimElement → Int → String
  renderType : TypeObject → String

structure ArgumentNode where
  n : Nat
  deriving DecidableEq, Repr

structure PhiNodeValue where
  edges : List Int
  values : List (Option DelimElement)
  deriving DecidableEq, Repr

structure PhiCNodeValue where
  values : List DelimElement
  deriving DecidableEq, Repr

structure PiNodeValue where
  value : DelimElement
  type : TypeObject
  deriving DecidableEq, Repr

structure OptionalNodeValue where
  value : Option DelimElement
  deriving DecidableEq, Repr

structure GotoIfNotValue where
  destination : Int
  condition : DelimElement
  deriving DecidableEq, Repr

def showPhiBody (runtime : IRNodeRuntime) (node : PhiNodeValue)
    (indent : Int) (labelPrefix : String) : String :=
  let arguments := node.edges.zipIdx.map fun (edge, index) =>
    let value := match node.values[index]? with
      | some (some assigned) => runtime.renderUnquoted assigned indent
      | _ => "#undef"
    labelPrefix ++ toString edge ++ " => " ++ value
  "φ (" ++ ", ".intercalate arguments ++ ")"

def showPhiCBody (runtime : IRNodeRuntime) (node : PhiCNodeValue) (indent : Int) : String :=
  "φᶜ (" ++ ", ".intercalate (node.values.map (runtime.renderUnquoted · indent)) ++ ")"

def showGotoIfNotBody (runtime : IRNodeRuntime) (node : GotoIfNotValue)
    (indent : Int) (labelPrefix : String) : String :=
  "goto " ++ labelPrefix ++ toString node.destination ++ " if not " ++
    runtime.renderUnquoted node.condition indent

structure AlignmentIO where
  color : Bool
  compact : Bool
  deriving DecidableEq, Repr

structure AlignmentValue where
  id : Nat
  deriving DecidableEq, Repr

structure AlignmentRuntime where
  render : AlignmentIO → AlignmentValue → String
  renderPlainString : AlignmentIO → AlignmentValue → String
  charWidth : Char → Nat

def noColorIO (io : AlignmentIO) : AlignmentIO := {io with color := false}

def alignmentFromShowBody (runtime : AlignmentRuntime) (io : AlignmentIO)
    (value : AlignmentValue) : Nat :=
  Truncate.textwidth runtime.charWidth (runtime.render (noColorIO io) value).toList

def alignmentFromPlainStringBody (runtime : AlignmentRuntime) (io : AlignmentIO)
    (value : AlignmentValue) : Nat :=
  Truncate.textwidth runtime.charWidth (runtime.renderPlainString (noColorIO io) value).toList

structure PairAlignmentRuntime where
  pairRuntime : PairRuntime
  renderPair : PairIO → PairValue → String
  renderElement : PairIO → PairElement → String
  charWidth : Char → Nat

def stringWidth (charWidth : Char → Nat) (text : String) : Int :=
  Int.ofNat (Truncate.textwidth charWidth text.toList)

def alignmentPairBody (runtime : PairAlignmentRuntime) (io : PairIO)
    (pair : PairValue) : Int × Int :=
  let fullWidth := stringWidth runtime.charWidth (runtime.renderPair io pair)
  if !pairDelimitedBody runtime.pairRuntime io pair then
    let typeinfos := pairTypeinfosBody runtime.pairRuntime io pair
    let context : PairIO := ⟨typeinfos.1, io.compact⟩
    let baseLeft := stringWidth runtime.charWidth (runtime.renderElement context pair.first)
    let parenWidth := if runtime.pairRuntime.isDelimited context pair.first then 0 else 2
    let spaceWidth := if io.compact then 0 else 1
    let left := baseLeft + parenWidth + spaceWidth
    (left + 1, fullWidth - left - 1)
  else (0, fullWidth)

structure BitIO where
  id : Nat
  deriving DecidableEq, Repr

structure BitWrite where
  io : BitIO
  text : String
  deriving DecidableEq, Repr

structure BitArrayValue where
  chunks : List Nat
  length : Nat
  deriving DecidableEq, Repr

def printBitChunkBody (io : BitIO) (chunk length : Nat) : List BitWrite :=
  (Containers.printBitChunk chunk length).map fun char => ⟨io, String.singleton char⟩

def bitshowBody (io : BitIO) (array : BitArrayValue) : List BitWrite :=
  if array.length = 0 then [] else
  let preceding := array.chunks.dropLast.flatMap fun chunk =>
    printBitChunkBody io chunk 64 ++ [⟨io, ": "⟩]
  let lastLength := (array.length - 1) % 64 + 1
  preceding ++ printBitChunkBody io (array.chunks.getLastD 0) lastLength

structure OpaqueClosureValue where
  argumentType : SignatureType
  resultType : TypeObject
  deriving Repr

structure OpaqueRuntime where
  tupleRuntime : TupleCallRuntime
  renderResultType : TypeObject → String

def showOpaqueBody (runtime : OpaqueRuntime) (closure : OpaqueClosureValue) : String :=
  showTupleCallBody runtime.tupleRuntime ⟨0⟩ closure.argumentType false none none false false ++
    "->◌::" ++ runtime.renderResultType closure.resultType

structure PartitionValue where
  id : Nat
  minWorld : Nat
  maxWorld : Nat
  kindBits : Nat
  restriction : BindingNode
  deriving Repr

structure PartitionRuntime where
  maxWorldValue : Nat
  flagMask : Nat
  exportedFlag : Nat
  implicitlyExportedFlag : Nat
  deprecatedFlag : Nat
  depwarnFlag : Nat
  implicitlyDeprecatedFlag : Nat
  bindingKind : PartitionValue → Nat
  backdatedConstKind : Nat
  constKind : Nat
  constImportKind : Nat
  undefConstKind : Nat
  guardKind : Nat
  failedKind : Nat
  declaredKind : Nat
  implicitGlobalKind : Nat
  implicitConstKind : Nat
  explicitKind : Nat
  importedKind : Nat
  globalKind : Nat
  renderRestriction : BindingNode → String
  restrictionGlobalRef : BindingNode → GlobalRefModel
  renderGlobalRef : GlobalRefModel → String
  owner : PartitionValue → GlobalRefModel
  lookupPartition : Nat → PartitionValue
  nextPartition : PartitionValue → Option Nat

def partitionFlags (runtime : PartitionRuntime) (partition : PartitionValue) : List String :=
  [(runtime.exportedFlag, "exported"),
   (runtime.implicitlyExportedFlag, "re-exported"),
   (runtime.deprecatedFlag, "deprecated"),
   (runtime.depwarnFlag, "depwarn"),
   (runtime.implicitlyDeprecatedFlag, "implicitly-deprecated")].filterMap fun pair =>
    if (partition.kindBits &&& pair.1) != 0 then some pair.2 else none

def partitionKindText (runtime : PartitionRuntime) (partition : PartitionValue) : String :=
  let kind := runtime.bindingKind partition
  if kind = runtime.backdatedConstKind then "backdated constant binding"
  else if kind = runtime.constKind then "constant binding"
  else if kind = runtime.constImportKind then "constant binding (declared with `import`)"
  else if kind = runtime.undefConstKind then "undefined const binding"
  else if kind = runtime.guardKind then "undefined binding - guard entry"
  else if kind = runtime.failedKind then "ambiguous binding - guard entry"
  else if kind = runtime.declaredKind then "weak global binding declared using `global` (implicit type Any)"
  else if kind = runtime.implicitGlobalKind then "implicit `using` resolved to global " ++
    runtime.renderGlobalRef (runtime.restrictionGlobalRef partition.restriction)
  else if kind = runtime.implicitConstKind then "implicit `using` resolved to constant"
  else if kind = runtime.explicitKind then "explicit `using` from " ++
    runtime.renderGlobalRef (runtime.restrictionGlobalRef partition.restriction)
  else if kind = runtime.importedKind then "explicit `import` from " ++
    runtime.renderGlobalRef (runtime.restrictionGlobalRef partition.restriction)
  else "global variable with type " ++ runtime.renderRestriction partition.restriction

def printPartitionBody (runtime : PartitionRuntime) (partition : PartitionValue) : String :=
  toString partition.minWorld ++ ":" ++
    (if partition.maxWorld = runtime.maxWorldValue then "∞" else toString partition.maxWorld) ++
    (if (partition.kindBits &&& runtime.flagMask) != 0 then
      " [" ++ ",".intercalate (partitionFlags runtime partition) ++ "]" else "") ++
    " - " ++ partitionKindText runtime partition

def bindingPartitionsBody (runtime : PartitionRuntime) : Nat → Option Nat → List String
  | 0, _ => []
  | _, none => []
  | fuel + 1, some id =>
    let partition := runtime.lookupPartition id
    ("\n   " ++ printPartitionBody runtime partition) ::
      bindingPartitionsBody runtime fuel (runtime.nextPartition partition)

structure BindingValue where
  globalRef : GlobalRefModel
  partitionsDefined : Bool
  firstPartition : Option Nat
  fuel : Nat
  deriving Repr

structure IntoValue where
  id : Nat
  moduleValue : ModuleValue
  deriving DecidableEq, Repr

structure IntoRuntime where
  getGlobal : ModuleValue → String → Nat
  renderModule : ModuleValue → String
  showDefault : IntoValue → String

def showIntoBody (runtime : IntoRuntime) (value : IntoValue) (field : String) : String :=
  if runtime.getGlobal value.moduleValue field = value.id then
    runtime.renderModule value.moduleValue ++ "." ++ field
  else runtime.showDefault value

structure AxisModel where
  value : DelimElement
  indices : Option DelimElement
  length : Nat
  oneTo : Bool
  deriving DecidableEq, Repr

structure SummaryValue where
  id : Nat
  typeId : TypeObject
  axes : List AxisModel
  eltype : TypeObject
  deriving Repr

structure MemoryRefValue where
  id : Nat
  memoryLength : Int
  offset : Int
  typeId : TypeObject
  deriving Repr

structure SummaryRuntime where
  renderType : TypeObject → String
  renderValue : DelimElement → String
  showarg : SummaryValue → Bool → String
  showargMemory : MemoryRefValue → Bool → String
  axes : SummaryValue → List AxisModel
  showPlainFunction : SummaryValue → String

def dimsText (dimensions : List Nat) : String :=
  if dimensions.isEmpty then "0-dimensional"
  else if dimensions.length = 1 then toString (dimensions.headD 0) ++ "-element"
  else "×".intercalate (dimensions.map toString)

def axisText (runtime : SummaryRuntime) (axis : AxisModel) : String :=
  runtime.renderValue (axis.indices.getD axis.value)

def axesText (runtime : SummaryRuntime) (axes : List AxisModel) : String :=
  "×".intercalate (axes.map (axisText runtime))

def arraySummaryBody (runtime : SummaryRuntime) (array : SummaryValue)
    (axes : List AxisModel) (includeIndices : Bool) : String :=
  dimsText (axes.map (·.length)) ++ " " ++ runtime.showarg array true ++
    if includeIndices then " with indices " ++ axesText runtime axes else ""

structure SubArrayValue where
  parent : SummaryValue
  indices : List AxisModel
  eltype : TypeObject
  deriving Repr

structure ReshapedValue where
  parent : SummaryValue
  dimensions : List Int
  eltype : TypeObject
  deriving Repr

structure ReinterpretValue where
  parent : SummaryValue
  targetType : TypeObject
  eltype : TypeObject
  deriving Repr

structure IteratorWrapperValue where
  iterator : DelimElement
  deriving DecidableEq, Repr

structure ContainerRuntime where
  summary : SummaryRuntime
  showParent : SummaryValue → Bool → String
  showIterator : DelimElement → String

def showIndicesBody (runtime : SummaryRuntime) : List AxisModel → String
  | [] => ""
  | axis :: rest => (if axis.indices.isSome then ", :" else ", " ++ axisText runtime axis) ++
    showIndicesBody runtime rest

inductive AnyTypeKind where
  | bottom | typeEgal | typeEq | other
  deriving DecidableEq, Repr

structure AnyTypeValueModel where
  object : TypeObject
  kind : AnyTypeKind
  deriving DecidableEq, Repr

structure AnyTypeRuntime where
  compact : Bool
  typeParameter : AnyTypeValueModel → TypeObject
  renderType : TypeObject → String
  showOtherType : AnyTypeValueModel → String

def showTypeEgalBody (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) : String :=
  "Core.TypeEgal{" ++ runtime.renderType (runtime.typeParameter value) ++ "}"

def showTypeEqBody (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) : String :=
  (if runtime.compact then "Type{" else "TypeEq{") ++
    runtime.renderType (runtime.typeParameter value) ++ "}"

def showAnyTypeBody (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) : String :=
  match value.kind with
  | .bottom => "Union{}"
  | .typeEgal => showTypeEgalBody runtime value
  | .typeEq => showTypeEqBody runtime value
  | .other => runtime.showOtherType value

structure TypeDispatchRuntime where
  compact : Bool
  isTypeEgal : TypeObject → Bool
  showTypeEgal : TypeObject → String
  printWithoutParams : TypeObject → Bool
  showTypeName : TypeObject → String
  showAlias : TypeObject → Option String
  isTypeEq : TypeObject → Bool
  showTypeEq : TypeObject → String
  asDataType : TypeObject → Bool
  showDatatype : TypeObject → List TypeVarValue → String
  unionTypes : TypeObject → Option (List TypeObject)
  showUnionAliases : TypeObject → Option String
  bottomId : Nat
  unwrapUnionAll : TypeObject → List TypeVarValue × TypeObject
  ioHasTypevarName : String → TypeObject → Bool
  freshTypevar : TypeVarValue → Nat → TypeVarValue
  instantiate : TypeObject → TypeVarValue → TypeVarValue → TypeObject
  renderType : TypeObject → String
  showWheres : List TypeVarValue → String

def uniqueBinder (runtime : TypeDispatchRuntime) (whole : TypeObject)
    (body : TypeObject) (binder : TypeVarValue) : TypeVarValue × TypeObject :=
  if binder.name = "_" || runtime.ioHasTypevarName binder.name whole then
    let rec find : Nat → TypeVarValue × TypeObject
      | 0 => (binder, body)
      | fuel + 1 =>
        let fresh := runtime.freshTypevar binder (fuel + 1)
        if runtime.ioHasTypevarName fresh.name whole then find fuel
        else (fresh, runtime.instantiate body binder fresh)
    find 64
  else (binder, body)

def showTypeDispatchBody (runtime : TypeDispatchRuntime) (input : TypeObject) : String :=
  if runtime.isTypeEgal input then runtime.showTypeEgal input
  else if runtime.printWithoutParams input then runtime.showTypeName input
  else if runtime.compact then match runtime.showAlias input with
    | some alias => alias
    | none =>
      if runtime.isTypeEq input then runtime.showTypeEq input
      else if runtime.asDataType input then runtime.showDatatype input []
      else match runtime.unionTypes input with
        | some types => match runtime.showUnionAliases input with
          | some aliases => aliases
          | none => "Union{" ++ ",".intercalate (types.map runtime.renderType) ++ "}"
        | none => if input.id = runtime.bottomId then "Union{}" else
          let (binders, initialBody) := runtime.unwrapUnionAll input
          let (wheres, body) := binders.foldl (fun (wheres, body) binder =>
            let result := uniqueBinder runtime input body binder
            (wheres ++ [result.1], result.2)) ([], initialBody)
          (if runtime.asDataType body then runtime.showDatatype body wheres
           else runtime.renderType body) ++ runtime.showWheres wheres
  else if runtime.isTypeEq input then runtime.showTypeEq input
  else if runtime.asDataType input then runtime.showDatatype input []
  else match runtime.unionTypes input with
    | some types => "Union{" ++ ",".intercalate (types.map runtime.renderType) ++ "}"
    | none => if input.id = runtime.bottomId then "Union{}" else
      let (binders, initialBody) := runtime.unwrapUnionAll input
      let (wheres, body) := binders.foldl (fun (wheres, body) binder =>
        let result := uniqueBinder runtime input body binder
        (wheres ++ [result.1], result.2)) ([], initialBody)
      (if runtime.asDataType body then runtime.showDatatype body wheres
       else runtime.renderType body) ++ runtime.showWheres wheres

structure VisibilityBinding where
  id : Nat
  deriving DecidableEq, Repr

structure VisibilityPartition where
  kind : Nat
  restrictionId : Nat
  deriving DecidableEq, Repr

structure VisibilityRuntime where
  isDeprecated : ModuleValue → SymbolValue → Bool
  isDefinedGlobal : ModuleValue → SymbolValue → Bool
  binding : ModuleValue → SymbolValue → VisibilityBinding
  worldAge : Nat
  lookupPartition : Nat → VisibilityBinding → VisibilityPartition
  explicitlyImported : Nat → Bool
  restrictionBinding : VisibilityPartition → VisibilityBinding
  definedConst : Nat → Bool

def followImports (runtime : VisibilityRuntime) (parent : VisibilityBinding) :
    Nat → VisibilityBinding → VisibilityBinding × Bool
  | 0, current => (current, current.id = parent.id)
  | fuel + 1, current =>
    if current.id = parent.id then (current, true)
    else
      let partition := runtime.lookupPartition runtime.worldAge current
      if runtime.explicitlyImported partition.kind then
        followImports runtime parent fuel (runtime.restrictionBinding partition)
      else (current, false)

def isVisibleBody (runtime : VisibilityRuntime) (symbol : SymbolValue)
    (parent origin : ModuleValue) : Bool :=
  if runtime.isDeprecated parent symbol || !runtime.isDefinedGlobal origin symbol ||
      !runtime.isDefinedGlobal parent symbol then false
  else
    let parentBinding := runtime.binding parent symbol
    let originBinding := runtime.binding origin symbol
    let followed := followImports runtime parentBinding 64 originBinding
    if followed.2 then true else
    let parentPartition := runtime.lookupPartition runtime.worldAge parentBinding
    let originPartition := runtime.lookupPartition runtime.worldAge followed.1
    runtime.definedConst parentPartition.kind && runtime.definedConst originPartition.kind &&
      parentPartition.restrictionId = originPartition.restrictionId

structure GlobalFunctionRuntime where
  dataTypeNameId : Nat
  concrete : TypeNameValue → Bool
  moduleDefined : TypeNameValue → Bool
  isDefinedGlobal : String → String → Bool
  isConst : String → String → Bool
  globalIsaWrapper : String → String → TypeNameValue → Bool

def isGlobalFunctionBody (runtime : GlobalFunctionRuntime) (typeName : TypeNameValue)
    (globalName : Option String) : Bool :=
  match globalName with
  | none => false
  | some name => runtime.concrete typeName && typeName.id ≠ runtime.dataTypeNameId &&
    !name.contains '#' && !name.contains '@' && runtime.moduleDefined typeName &&
    runtime.isDefinedGlobal typeName.moduleName name && runtime.isConst typeName.moduleName name &&
    runtime.globalIsaWrapper typeName.moduleName name typeName

structure WorldRuntime where
  bindingDefined : TypeNameValue → Bool
  firstPartition : TypeNameValue → Option Nat
  lookup : Nat → PartitionValue
  next : PartitionValue → Option Nat
  definedConst : Nat → Bool
  restrictionIsTypeSubtype : BindingNode → TypeNameValue → Bool
  maxWorld : Nat

def checkWorldBody (runtime : WorldRuntime) (typeName : TypeNameValue) : Option (Int × Int) :=
  if !runtime.bindingDefined typeName then none else
  let rec search : Nat → Option Nat → Option (Int × Int)
    | 0, _ => none
    | _, none => none
    | fuel + 1, some id =>
      let partition := runtime.lookup id
      if runtime.definedConst partition.kindBits &&
          runtime.restrictionIsTypeSubtype partition.restriction typeName then
        if partition.maxWorld = runtime.maxWorld then none
        else some (Int.ofNat partition.minWorld, Int.ofNat partition.maxWorld)
      else search fuel (runtime.next partition)
  search 64 (runtime.firstPartition typeName)

structure ShowTypeNameRuntime where
  unionAllNameId : Nat
  compact : Bool
  originModule : Option ModuleValue
  globalFunctionRuntime : GlobalFunctionRuntime
  visibilityRuntime : VisibilityRuntime
  worldRuntime : WorldRuntime
  symbolFromName : String → SymbolValue
  moduleFromName : String → ModuleValue
  renderModule : ModuleValue → String
  showSymbol : SymbolValue → String
  idStart : Char → Bool
  quotedSymbolIds : List Nat

def showTypeNameBody (runtime : ShowTypeNameRuntime) (typeName : TypeNameValue) : String :=
  if typeName.id = runtime.unionAllNameId then "UnionAll" else
  let globalName := typeName.singletonName
  let globalFunction := isGlobalFunctionBody runtime.globalFunctionRuntime typeName (some globalName)
  let symbol := runtime.symbolFromName (if globalFunction then globalName else typeName.name)
  let world := checkWorldBody runtime.worldRuntime typeName
  let module := runtime.moduleFromName typeName.moduleName
  let qualify := !runtime.compact && typeName.moduleFieldDefined && match runtime.originModule with
    | none => true
    | some origin => !isVisibleBody runtime.visibilityRuntime symbol module origin
  let symbolText := runtime.showSymbol symbol
  let firstChar := symbolText.toList.headD 'a'
  let needsQuote := globalFunction && !runtime.idStart firstChar
  let parens := needsQuote && runtime.quotedSymbolIds.contains symbol.id
  (if globalFunction then "typeof(" else "") ++
    (if world.isSome then "@world(" else "") ++
    (if qualify then runtime.renderModule module ++ "." else "") ++
    (if qualify && needsQuote then ":" else "") ++
    (if qualify && parens then "(" else "") ++ symbolText ++
    (match world with | some (lo, hi) => ", " ++ toString lo ++ ":" ++ toString hi ++ ")" | none => "") ++
    (if qualify && parens then ")" else "") ++ (if globalFunction then ")" else "")

inductive NestedParameter where
  | type (value : TypeObject)
  | symbols (values : List SymbolValue)
  | other (id : Nat)
  deriving Repr

structure NestedDatatype where
  id : Nat
  name : TypeNameValue
  parameters : List NestedParameter
  deriving Repr

inductive DatatypeParameter where
  | type (value : TypeObject)
  | typevar (value : TypeVarValue)
  | vararg (type : TypeObject) (length : Option Nat)
  | symbols (values : List SymbolValue)
  | datatype (value : NestedDatatype)
  | other (id : Nat)
  deriving Repr

structure DatatypeModel where
  id : Nat
  name : TypeNameValue
  parameters : List DatatypeParameter
  deriving Repr

structure KwargsRuntime where
  pairsTypeNameId : Nat
  namedTupleTypeNameId : Nat
  isSymbolType : DatatypeParameter → Bool
  isNothingType : DatatypeParameter → Bool
  eltype : NestedDatatype → DatatypeParameter
  sameParameter : DatatypeParameter → DatatypeParameter → Bool

def maybeKwargsBody (runtime : KwargsRuntime) (datatype : DatatypeModel) : Option NestedDatatype :=
  if datatype.name.id ≠ runtime.pairsTypeNameId || datatype.parameters.length ≠ 4 then none
  else match datatype.parameters with
  | first :: second :: third :: .datatype fourth :: [] =>
    if !runtime.isSymbolType first || fourth.name.id ≠ runtime.namedTupleTypeNameId ||
        fourth.parameters.length ≠ 2 || !runtime.sameParameter second (runtime.eltype fourth) ||
        !runtime.isNothingType third then none
    else match fourth.parameters with
      | .symbols _ :: .type _ :: [] => some fourth
      | _ => none
  | _ => none

structure DatatypeRuntime where
  tupleNameId : Nat
  namedTupleNameId : Nat
  anyTypeId : Nat
  backtrace : Bool
  kwargsRuntime : KwargsRuntime
  sameParameter : DatatypeParameter → DatatypeParameter → Bool
  renderParameter : DatatypeParameter → String
  renderSymbol : SymbolValue → String
  renderTypeName : TypeNameValue → String
  showTypeparams : List DatatypeParameter → List TypeVarValue → String

def nestedTypes (datatype : NestedDatatype) : List TypeObject :=
  datatype.parameters.filterMap fun parameter => match parameter with
  | .type value => some value
  | _ => none

def showNamedTupleFields (runtime : DatatypeRuntime) (symbols : List SymbolValue)
    (types : List TypeObject) : String :=
  ", ".intercalate (symbols.zipIdx.map fun (symbol, index) =>
    let typeText := match types[index]? with
      | some type => if type.id = runtime.anyTypeId then "" else "::" ++
        runtime.renderParameter (.type type)
      | none => ""
    runtime.renderSymbol symbol ++ typeText)

def showDatatypeBody (runtime : DatatypeRuntime) (datatype : DatatypeModel)
    (wheres : List TypeVarValue) : String :=
  let parameters := datatype.parameters
  if datatype.name.id = runtime.tupleNameId then
    if parameters.isEmpty then "Tuple{}" else
    let last := parameters.getLastD (.other 0)
    let (element, varargLength, varargKind) := match last with
      | .vararg type (some length) => (.type type, length, 1)
      | .vararg type none => (.type type, 0, 2)
      | other => (other, 1, 0)
    let fullLength := if varargKind = 1 then parameters.length + varargLength - 1
      else parameters.length
    let tailLength := if varargKind = 2 then 1 else
      (parameters.dropLast.reverse.takeWhile (runtime.sameParameter · element)).length + 1
    if (varargKind = 2 && parameters.length = 1) ||
        ((varargKind = 0 || varargKind = 1) && tailLength = fullLength && fullLength > 3) then
      "NTuple{" ++ (if varargKind = 2 then "N" else toString fullLength) ++ ", " ++
        runtime.renderParameter element ++ "}"
    else
      let headLength := if tailLength > 3 then fullLength - tailLength else fullLength
      let heads := (List.range headLength).map fun index =>
        runtime.renderParameter (if varargKind = 1 && index ≥ parameters.length - 1 then
          element else parameters.getD index element)
      let tail := if headLength < fullLength then
        (if heads.isEmpty then "" else ", ") ++ "Vararg{" ++ runtime.renderParameter element ++
          ", " ++ toString (fullLength - headLength) ++ "}" else ""
      "Tuple{" ++ ", ".intercalate heads ++ tail ++ "}"
  else if datatype.name.id = runtime.namedTupleNameId then
    match parameters with
    | .symbols symbols :: .datatype types :: [] =>
      let typeValues := nestedTypes types
      if typeValues.length = symbols.length then
        "@NamedTuple{" ++ showNamedTupleFields runtime symbols typeValues ++ "}"
      else runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres
    | _ => runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres
  else if runtime.backtrace then match maybeKwargsBody runtime.kwargsRuntime datatype with
    | some kwargs => match kwargs.parameters with
      | .symbols symbols :: .type _ :: [] =>
        "@Kwargs{" ++ showNamedTupleFields runtime symbols (nestedTypes kwargs) ++ "}"
      | _ => runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres
    | none => runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres
  else runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres

structure SupertypeRuntime where
  anyTypeId : Nat
  supertype : TypeObject → TypeObject
  render : TypeObject → String

def showSupertypesBody (runtime : SupertypeRuntime) : Nat → TypeObject → String
  | 0, type => runtime.render type
  | fuel + 1, type =>
    if type.id = runtime.anyTypeId then runtime.render type else
    let parent := runtime.supertype type
    runtime.render type ++ " <: " ++ showSupertypesBody runtime fuel parent

structure ShowMacroRuntime where
  showUnquoted : AstValue → String
  escape : AstValue → AstValue
  evaluate : AstValue → DelimElement
  repr : DelimElement → String

structure ShowMacroExpansion where
  lines : List String
  returnValue : Option DelimElement
  deriving DecidableEq, Repr

def showMacroBody (runtime : ShowMacroRuntime) (expressions : List AstValue) : ShowMacroExpansion :=
  let lines := expressions.map fun expression =>
    runtime.showUnquoted expression ++ " = " ++ runtime.repr (runtime.evaluate (runtime.escape expression))
  ⟨lines, (expressions.getLast?).map (runtime.evaluate ∘ runtime.escape)⟩

structure ModulesRuntime where
  unwrapUnionall : TypeObject → TypeObject
  dataModule : TypeObject → Option String
  typeEqParameter : TypeObject → Option TypeObject
  typeEgalParameter : TypeObject → Option TypeObject
  unionParts : TypeObject → Option (TypeObject × TypeObject)

def modulesOfTypeBody (runtime : ModulesRuntime) : Nat → TypeObject → List String
  | 0, _ => []
  | fuel + 1, input =>
    let value := runtime.unwrapUnionall input
    match runtime.dataModule value with
    | some moduleName => [moduleName]
    | none => match runtime.typeEqParameter value with
      | some parameter => modulesOfTypeBody runtime fuel parameter
      | none => match runtime.typeEgalParameter value with
        | some parameter => modulesOfTypeBody runtime fuel parameter
        | none => match runtime.unionParts value with
          | some (left, right) =>
            (modulesOfTypeBody runtime fuel left ++ modulesOfTypeBody runtime fuel right).eraseDups
          | none => []

structure UnionAliasValue where
  found : FoundAlias
  applied : TypeObject
  unionLength : Nat
  scoreEnv : Int
  deriving Repr

structure UnionAliasRuntime where
  base : MakeAliasRuntime
  emptyUnion : TypeObject
  unionTypes : TypeObject → List TypeObject
  rewrapUnionall : TypeObject → TypeObject → TypeObject
  unionLength : TypeObject → Nat
  subtype : TypeObject → TypeObject → Bool
  union : TypeObject → TypeObject → TypeObject
  printWithoutParams : TypeObject → Bool

def unionAliasCandidate (runtime : UnionAliasRuntime) (input : TypeObject)
    (components : List TypeObject) (reference : GlobalRefValue)
    (alias : AliasObject) : Option UnionAliasValue :=
  if !runtime.base.isType alias || runtime.base.hasFreeTypevars alias ||
      runtime.base.printWithoutParams alias || runtime.base.isTupleSubtype ⟨alias.id⟩ then none
  else
    let env := runtime.base.intersectEnv input (runtime.base.unbounded alias)
    match runtime.base.applyAlias alias env with
    | none => none
    | some applied0 =>
      let applied := runtime.base.rewrapFree applied0 (runtime.base.findFreeTypevars input)
      if runtime.base.hasOtherFree applied (runtime.base.findFreeTypevars input) ||
          !runtime.subtype applied input then none
      else if !(components.any fun component => runtime.subtype component applied) then none
      else some ⟨⟨reference, alias, if runtime.printWithoutParams input then [] else env⟩,
        applied, runtime.unionLength applied, -Int.ofNat env.length⟩

def insertUnionAlias (value : UnionAliasValue) : List UnionAliasValue → List UnionAliasValue
  | [] => [value]
  | head :: tail =>
    if value.unionLength > head.unionLength ||
        (value.unionLength = head.unionLength && value.scoreEnv > head.scoreEnv) then
      value :: head :: tail else head :: insertUnionAlias value tail

def sortUnionAliases (values : List UnionAliasValue) : List UnionAliasValue :=
  values.foldr insertUnionAlias []

def makeTypealiasesBody (runtime : UnionAliasRuntime) (input : TypeObject) :
    List UnionAliasValue × TypeObject :=
  if input.id = runtime.base.anyId || runtime.base.isTupleSubtype input then ([], runtime.emptyUnion)
  else
    let components := runtime.unionTypes input |>.map (runtime.rewrapUnionall · input)
    let aliases := (runtime.base.modulesOf input).map runtime.base.normalizeModule |>.flatMap fun moduleName =>
      (runtime.base.names moduleName).filterMap fun name =>
        if runtime.base.isDefinedGlobal moduleName name && !runtime.base.isDeprecated moduleName name &&
            runtime.base.isConst moduleName name then
          let alias := runtime.base.getGlobal moduleName name
          unionAliasCandidate runtime input components ⟨moduleName, name⟩ alias
        else none
    let sorted := sortUnionAliases aliases
    let (_, applied, kept) := sorted.foldl (fun (previous, applied, kept) alias =>
      let score := (alias.unionLength, alias.scoreEnv)
      if alias.unionLength < 2 then
        if runtime.subtype alias.applied applied then (previous, applied, kept)
        else (previous, runtime.union applied alias.applied, kept ++ [alias])
      else if score = previous || !runtime.subtype alias.applied applied then
        (score, runtime.union applied alias.applied, kept ++ [alias])
      else (previous, applied, kept)) ((0, 0), runtime.emptyUnion, [])
    (kept, applied)

structure ShowUnionRuntime where
  aliases : UnionAliasRuntime
  renderType : TypeObject → String
  makeWheres : FoundAlias → TypeObject → List TypeVarValue
  renderAlias : FoundAlias → List TypeVarValue → String
  renderWheres : List TypeVarValue → String
  isTypeVar : TypeObject → Bool

def showUnionAliasesBody (runtime : ShowUnionRuntime) (input : TypeObject) : Bool × String :=
  let (aliases, applied) := makeTypealiasesBody runtime.aliases input
  if aliases.isEmpty then (false, "") else
  let components := runtime.aliases.unionTypes input
  let remaining := components.filter fun type =>
    !runtime.isTypeVar type && !runtime.aliases.subtype type applied
  let typevars := components.filter runtime.isTypeVar
  let aliasTexts := aliases.map fun alias =>
    let wheres := runtime.makeWheres alias.found alias.applied
    runtime.renderAlias alias.found wheres ++ runtime.renderWheres wheres
  let pieces := remaining.map runtime.renderType ++ aliasTexts ++ typevars.map runtime.renderType
  (true, if remaining.isEmpty && typevars.isEmpty && aliases.length = 1 then
    aliasTexts.headD "" else "Union{" ++ ", ".intercalate pieces ++ "}")

structure TypePlainRuntime where
  printWithoutParams : TypeObject → Bool
  makeAlias : TypeObject → Option FoundAlias
  unwrapIsUnion : TypeObject → Bool
  unionAliasesApplied : TypeObject → TypeObject
  subtype : TypeObject → TypeObject → Bool
  renderCompact : TypeObject → String
  renderNormal : TypeObject → String
  compactContext : Bool
  asDataTypeName : TypeObject → Option TypeNameValue
  unionAllTypeId : Nat
  isGlobalFunction : TypeNameValue → String → Bool
  renderSymbol : String → String

def showTypePlainBody (runtime : TypePlainRuntime) (input : TypeObject) : List WriteEvent :=
  let aliasWorks := (runtime.makeAlias input).isSome ||
    (runtime.unwrapIsUnion input && runtime.subtype input (runtime.unionAliasesApplied input))
  if !runtime.printWithoutParams input && aliasWorks then
    [.plain (runtime.renderCompact input)] ++
    (if runtime.compactContext then [] else
      [.styled " (alias for " "light_black" false,
       .styled (runtime.renderNormal input) "light_black" false,
       .styled ")" "light_black" false])
  else
    let normal := [.plain (runtime.renderNormal input)]
    if runtime.compactContext || input.id = runtime.unionAllTypeId then normal
    else match runtime.asDataTypeName input with
    | some typeName => if runtime.isGlobalFunction typeName typeName.singletonName then
        normal ++ [.plain (" (singleton type of function " ++
          runtime.renderSymbol typeName.singletonName ++ ", subtype of Function)")]
      else normal
    | none => normal

structure DumpDatatype where
  typeId : TypeObject
  isStruct : Bool
  isMutable : Bool
  isTuple : Bool
  isPrimitive : Bool
  isAbstract : Bool
  isAny : Bool
  supertype : TypeObject
  unknownNamedTuple : Bool
  fields : List (String × Bool × Option TypeObject)
  deriving Repr

inductive DumpValue where
  | bottom
  | module (value : ModuleValue)
  | string (value : String)
  | symbol (value : SymbolValue)
  | unionType (value : TypeObject)
  | pointer (address : Nat)
  | function (value : FunctionValue)
  | simpleVector (slots : List (Option DumpValue))
  | array (elementType : TypeObject) (shape : String) (numeric : Bool)
      (slots : List (Option DumpValue))
  | datatype (value : DumpDatatype)
  | object (typeId : TypeObject) (fields : List (String × Option DumpValue))
  | leaf (typeId : TypeObject) (id : Nat)
  deriving Repr

structure DumpRuntime where
  renderBottom : String
  renderModule : ModuleValue → String
  renderString : String → String
  renderSymbol : SymbolValue → String
  renderType : TypeObject → String
  renderPointer : Nat → String
  renderFunction : FunctionValue → String
  renderLeaf : Nat → String
  renderValue : DumpValue → String
  circular : DumpValue → Bool

def dumpIndent (indent : String) := indent ++ "  "

def dumpBody (runtime : DumpRuntime) (limit : Bool) : Nat → String → DumpValue → String
  | _, _, .bottom => runtime.renderBottom
  | _, _, .module value => "Module " ++ runtime.renderModule value
  | _, _, .string value => "String " ++ runtime.renderString value
  | _, _, .symbol value => "Symbol " ++ runtime.renderSymbol value
  | _, _, .unionType value => runtime.renderType value
  | _, _, .pointer address => runtime.renderPointer address
  | _, _, .function value => runtime.renderFunction value ++ " (function of type " ++
      runtime.renderType ⟨value.datatype.id⟩ ++ ")"
  | _, _, .simpleVector [] => "empty SimpleVector"
  | 0, _, .simpleVector _ => "SimpleVector"
  | depth + 1, indent, .simpleVector slots =>
    "SimpleVector" ++ String.join (slots.zipIdx.map fun (slot, index) =>
      "\n" ++ indent ++ "  " ++ toString (index + 1) ++ ": " ++ match slot with
      | none => "#undef"
      | some value => dumpBody runtime limit depth (dumpIndent indent) value)
  | _, _, .array elementType shape true slots =>
    "Array{" ++ runtime.renderType elementType ++ "}(" ++ shape ++ ") " ++
      runtime.renderValue (.array elementType shape true slots)
  | 0, _, .array elementType shape false _ =>
    "Array{" ++ runtime.renderType elementType ++ "}(" ++ shape ++ ")"
  | depth + 1, indent, value@(.array elementType shape false slots) =>
    let header := "Array{" ++ runtime.renderType elementType ++ "}(" ++ shape ++ ")"
    if slots.isEmpty || runtime.circular value then header else
    let indices := if limit && slots.length > 10 then
      [0, 1, 2, 3, 4] ++ [slots.length - 5, slots.length - 4,
        slots.length - 3, slots.length - 2, slots.length - 1]
      else List.range slots.length
    header ++ "\n" ++ String.join (indices.zipIdx.map fun (index, shownIndex) =>
      (if limit && slots.length > 10 && shownIndex = 5 then indent ++ "  ...\n" else "") ++
      indent ++ "  " ++ toString (index + 1) ++ ": " ++ match slots[index]? with
      | some (some child) => dumpBody runtime limit depth (dumpIndent indent) child
      | _ => "#undef" ++ if shownIndex + 1 < indices.length then "\n" else "")
  | depth, indent, .datatype datatype =>
    let header := (if datatype.isMutable && datatype.isStruct then "mutable " else "") ++
      (if datatype.isStruct && !datatype.isTuple then "struct " else "") ++
      (if datatype.isPrimitive then "primitive type " else "") ++
      (if datatype.isAbstract then "abstract type " else "") ++ runtime.renderType datatype.typeId ++
      (if datatype.isAny then "" else " <: " ++ runtime.renderType datatype.supertype)
    if depth = 0 || datatype.isTuple || datatype.isAbstract || datatype.unknownNamedTuple then header else
      header ++ String.join (datatype.fields.map fun (name, constant, fieldType) =>
        "\n" ++ indent ++ "  " ++ (if datatype.isMutable && constant then "const " else "") ++
        name ++ match fieldType with | none => "" | some type => "::" ++ runtime.renderType type)
  | 0, _, .object typeId _ => runtime.renderType typeId
  | depth + 1, indent, value@(.object typeId fields) =>
    let header := runtime.renderType typeId
    if fields.isEmpty then header ++ " " ++ runtime.renderValue value
    else if runtime.circular value then header else header ++ String.join (fields.map fun (name, field) =>
      "\n" ++ indent ++ "  " ++ name ++ ": " ++ match field with
      | none => "#undef"
      | some child => dumpBody runtime limit depth (dumpIndent indent) child)
  | _, _, .leaf typeId id => runtime.renderType typeId ++ " " ++ runtime.renderLeaf id

def dumpElementsBody (runtime : DumpRuntime) (depth : Nat) (indent : String)
    (slots : List (Option DumpValue)) (first last : Nat) : String :=
  String.join ((List.range (last + 1 - first)).map fun offset =>
    let index := first + offset
    indent ++ "  " ++ toString index ++ ": " ++
      (match slots[index - 1]? with
       | some (some value) => dumpBody runtime false (depth - 1) (dumpIndent indent) value
       | _ => "#undef") ++ if index < last then "\n" else "")

def emphasizeBody (runtime : StyleRuntime) (io : StyledIO) (text color : String) : List WriteEvent :=
  if runtime.colorEnabled io then [.styled text color true]
  else [.plain (runtime.uppercase text)]

def showLineBody (runtime : StyleRuntime) (line : DelimElement)
    (file : Option DelimElement) : List WriteEvent :=
  let text := match file with
    | none => "#= line " ++ runtime.renderLine line ++ " =#"
    | some path => "#= " ++ runtime.renderFile path ++ ":" ++ runtime.renderLine line ++ " =#"
  [.styled text "light_black" false]

structure AliasVarValue where
  id : Nat
  name : String
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

inductive AliasExpr where
  | atom (id : Nat)
  | unionAll (binder : AliasVarValue) (body : AliasExpr)
  deriving DecidableEq, Repr

structure AliasRuntime where
  bottomId : Nat
  anyId : Nat
  newTypeVar : String → AliasVarValue
  newTypeVarLower : ∀ name, (newTypeVar name).lower = bottomId
  newTypeVarUpper : ∀ name, (newTypeVar name).upper = anyId
  instantiate : AliasVarValue → AliasExpr → AliasVarValue → AliasExpr

def unboundedAlias (runtime : AliasRuntime) : AliasExpr → AliasExpr
  | .atom id => .atom id
  | .unionAll binder body =>
    let rewritten := unboundedAlias runtime body
    if binder.lower = runtime.bottomId ∧ binder.upper = runtime.anyId then
      if rewritten = body then .unionAll binder body else .unionAll binder rewritten
    else
      let fresh := runtime.newTypeVar binder.name
      .unionAll fresh (runtime.instantiate binder rewritten fresh)

def outerBinderUnbounded (runtime : AliasRuntime) : AliasExpr → Bool
  | .atom _ => true
  | .unionAll binder _ =>
    binder.lower == runtime.bottomId && binder.upper == runtime.anyId

structure IterValue where
  elements : List Nat
  isKeySet : Bool
  deriving DecidableEq, Repr

structure IterRuntime where
  compact : Bool
  limit : Bool
  color : Bool
  displaysize : Int × Int
  renderIter : IterValue → String
  summary : IterValue → String
  renderValue : Nat → String
  sprintShow : Nat → String
  truncate : Bool → String → Nat → String

def showKeyValueBody (runtime : IterRuntime) (iter : IterValue) : String :=
  let entries := iter.elements.map fun value =>
    { full := runtime.renderValue value
      limited := runtime.truncate runtime.color (runtime.sprintShow value)
        (max 4 (runtime.displaysize.2 - 2)).toNat : Remaining.IterEntry }
  let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else entries.length
  Remaining.showKeyValueIter (runtime.summary iter) (runtime.renderIter iter)
    (if iter.isKeySet then "Keys" else "Values") entries runtime.compact runtime.limit rows

structure SetValue where
  elements : List Nat
  deriving DecidableEq, Repr

structure SetRuntime where
  limit : Bool
  color : Bool
  displaysize : Int × Int
  renderSet : SetValue → String
  summary : SetValue → String
  circular : SetValue → Bool
  renderValue : Nat → String
  sprintShow : Nat → String
  truncate : Bool → String → Nat → String
  showarg : SetValue → Bool → String

def showSetBody (runtime : SetRuntime) (set : SetValue) : String :=
  let cols := max 4 (runtime.displaysize.2 - 2)
  let entries := set.elements.map fun value =>
    { full := runtime.renderValue value
      limited := runtime.truncate runtime.color (runtime.sprintShow value) cols.toNat :
        Remaining.IterEntry }
  let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else entries.length
  Remaining.showSetPlain (runtime.summary set) (runtime.renderSet set) entries
    (runtime.circular set) runtime.limit rows

structure DictValue where
  pairs : List (Nat × Nat)
  hasLength : Bool
  deriving DecidableEq, Repr

structure DictRuntime where
  limit : Bool
  color : Bool
  hasCompactKey : Bool
  displaysize : Int × Int
  renderDict : DictValue → String
  summary : DictValue → String
  circular : DictValue → Bool
  sprintKey : Nat → String
  sprintValue : Nat → String
  renderValue : Nat → String
  textWidth : Bool → String → Nat
  truncate : Bool → String → Nat → Bool → String

def widthStep (runtime : DictRuntime) (cols : Nat) (current : Nat)
    (text : String) : Nat := min cols (max current (runtime.textWidth runtime.color text))

def showDictBody (runtime : DictRuntime) (dict : DictValue) : String :=
  if dict.pairs.isEmpty || !dict.hasLength then runtime.renderDict dict
  else
    let summary := runtime.summary dict
    if runtime.circular dict then summary ++ ":"
    else if runtime.limit && runtime.displaysize.1 - 3 < 2 then summary ++ ": …"
    else
      let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else dict.pairs.length
      let cols := if runtime.limit then (max 12 runtime.displaysize.2 - 6).toNat else 0
      let shownPairs := dict.pairs.take rows
      let keyStrings := shownPairs.map (runtime.sprintKey ·.1)
      let valueStrings := shownPairs.map (runtime.sprintValue ·.2)
      let initialKeyWidth := keyStrings.foldl (widthStep runtime cols) 0
      let valueWidth := valueStrings.foldl (widthStep runtime cols) 0
      let keyWidth := if runtime.limit &&
          initialKeyWidth > max (cols / 2) (cols - valueWidth) then
        max ((cols + 2) / 3) (cols - valueWidth) else initialKeyWidth
      let entries := dict.pairs.map fun pair =>
        { key := runtime.sprintKey pair.1
          value := runtime.renderValue pair.2
          alignedLimitedKey := runtime.truncate runtime.color
            (runtime.sprintKey pair.1) keyWidth true
          limitedValue := runtime.truncate runtime.color
            (runtime.sprintValue pair.2) (cols - keyWidth) false : Remaining.DictEntry }
      Remaining.showDictPlain summary (runtime.renderDict dict) entries dict.hasLength
        false runtime.limit rows

inductive OptionValue where
  | ordinary (id : Nat)
  | ptrUInt8 (address : Option Nat)
  | ptrPtrUInt8 (address : Nat)
  | string (text : String)
  deriving DecidableEq, Repr

structure JLOptionsValue where
  fields : List (String × OptionValue)
  deriving DecidableEq, Repr

structure JLOptionsRuntime where
  unsafeString : Nat → String
  unsafeLoadCommands : Nat → OptionValue
  repr : OptionValue → String

def normalizeOptionValue (runtime : JLOptionsRuntime) : OptionValue → OptionValue
  | .ptrUInt8 none => .string ""
  | .ptrUInt8 (some address) => .string (runtime.unsafeString address)
  | .ptrPtrUInt8 address => runtime.unsafeLoadCommands address
  | value => value

def showJLOptionsBody (runtime : JLOptionsRuntime) (opt : JLOptionsValue) : Out :=
  let nfields := opt.fields.length
  ["JLOptions(", "\n"] ++ (opt.fields.zipIdx.flatMap fun ((field, value), index) =>
    let value := normalizeOptionValue runtime value
    ["  ", field, " = ", runtime.repr value,
      if index + 1 < nfields then "," else "", "\n"]) ++ [")"]

structure TaskValue where
  id : Nat
  deriving DecidableEq, Repr

structure TaskRuntime where
  render : TaskValue → String
  isFailed : TaskValue → Bool
  showException : TaskValue → Bool → String

def showTaskBody (runtime : TaskRuntime) (task : TaskValue) : Out :=
  [runtime.render task] ++
    if runtime.isFailed task then ["\n", runtime.showException task false] else []

structure CancellationValue where
  id : Nat
  nparents : Nat
  deriving DecidableEq, Repr

structure SeverityValue where
  request : UInt8
  deriving DecidableEq, Repr

structure CancellationRuntime where
  cancelSeverity : CancellationValue → Option SeverityValue
  repr : UInt8 → String

def showCancellationBody (runtime : CancellationRuntime)
    (source : CancellationValue) : Out :=
  ["CancellationTokenSource("] ++
  [match runtime.cancelSeverity source with
   | none => "active"
   | some severity =>
     let request := severity.request
     if request = 0x1 then "cancelled"
     else if request = 0x3 then "cancelled, abandon external"
     else if request = 0x4 then "cancelled, abandon all"
     else "cancelled, severity " ++ runtime.repr request] ++
  (if source.nparents > 0 then
    [", ", toString source.nparents,
      if source.nparents = 1 then " parent" else " parents"] else []) ++ [")"]

structure IOContextRuntime where
  getColor : IOCtx.BaseIO → Bool
  renderBase : IOCtx.BaseIO → String

inductive LockEffect where
  | lock
  | unlock
  deriving DecidableEq, Repr

def lockEffect (effect : LockEffect) (io : IOCtx.JIO) : IOCtx.BaseIO × LockEffect :=
  match IOCtx.unwrapcontext io with
  | .plain base => (base, effect)
  | .ctx base _ => (base, effect)

structure GenericValue where
  id : Nat
  deriving DecidableEq, Repr

structure GenericShowRuntime where
  stdout : IOCtx.BaseIO
  showDefault : IOCtx.BaseIO → GenericValue → Out
  showOn : IOCtx.BaseIO → GenericValue → Out
  inferenceBarrier : GenericValue → GenericValue
  showDefaultInner : IOCtx.BaseIO → GenericValue → Out

structure DefaultValue where
  typeId : Nat
  fields : List (Option GenericValue)
  bytes : List UInt8
  byteSize : Nat
  bitSize : Nat
  deriving DecidableEq, Repr

structure DefaultRuntime where
  renderType : Nat → String
  showCircular : IOCtx.BaseIO → DefaultValue → Option String
  showField : IOCtx.BaseIO → GenericValue → String

def defaultFields (runtime : DefaultRuntime) (io : IOCtx.BaseIO)
    (x : DefaultValue) : List Values.Field :=
  x.fields.map fun field => match field with
  | none => .undef
  | some value => .val (runtime.showField io value)

def showDefaultBody (runtime : DefaultRuntime) (io : IOCtx.BaseIO)
    (x : DefaultValue) : Out :=
  let fields := defaultFields runtime io x
  let bits := if !x.fields.isEmpty || x.byteSize = 0 then none
    else some (x.bytes, x.bitSize)
  Values.showDefault (runtime.renderType x.typeId)
    (runtime.showCircular io x) fields bits

def showAtNamedTuple (fields : List (String × Option String)) : Out :=
  fields.zipIdx.flatMap fun ((name, typ), i) =>
    (if i = 0 then [] else [", "]) ++ [name] ++ match typ with | none => [] | some t => ["::", t]

def stateIs (q : Truncate.QState) (bit : Nat) : Bool :=
  if bit = 1 then q.backslash else if bit = 2 then q.squote else if bit = 4 then q.dquote else false
def stateEnter (q : Truncate.QState) (bit : Nat) : Truncate.QState :=
  if bit = 1 then {q with backslash := true} else if bit = 2 then {q with squote := true}
  else if bit = 4 then {q with dquote := true} else q
def stateLeave (q : Truncate.QState) (bit : Nat) : Truncate.QState :=
  if bit = 1 then {q with backslash := false} else if bit = 2 then {q with squote := false}
  else if bit = 4 then {q with dquote := false} else q

def showBound (text : String) (parens : Bool) : String := if parens then "(" ++ text ++ ")" else text

/-- `show(io::IO, ::MIME"text/plain", u::UndefInitializer)`, `base/show.jl:6-10`. -/
def m6 (compact : Bool) := Values.showUndefPlain compact
/-- `show(io::IO, ::MIME"text/plain", r::AbstractRange)`, `base/show.jl:14-14`. -/
def m14 (runtime : RangeRuntime) (r : RangeValue) : Out := [runtime.render r]
/-- `show(io::IO, ::MIME"text/plain", r::UnitRange)`, `base/show.jl:16-21`. -/
def m16 (runtime : RangeRuntime) (compact : Bool) (r : RangeValue) : Out :=
  [runtime.render r] ++
    (if !compact && runtime.isempty r then [" (empty range)"] else [])
/-- `show(io::IO, ::MIME"text/plain", r::LinRange)`, `base/show.jl:23-32`. -/
def m23 (runtime : RangeRuntime) (r : RangeValue) : Out :=
  if runtime.isempty r then [runtime.render r]
  else [runtime.summary r, ":", "\n", runtime.printLinRange r]
/-- `show(io::IO, ::MIME"text/plain", r::LogRange)`, `base/show.jl:34-39`. -/
def m34 (runtime : RangeRuntime) (r : RangeValue) : Out :=
  if runtime.isempty r then [runtime.render r]
  else [runtime.summary r, ":", "\n", runtime.printLogRange r]
/-- `_isself(ft::DataType)`, `base/show.jl:41-53`. -/
def m41 (runtime : SelfRuntime) (ft : DataTypeValue) := isSelfBody runtime ft
/-- `show(io::IO, ::MIME"text/plain", f::Function)`, `base/show.jl:55-73`. -/
def m55 (runtime : FunctionRuntime) (compact : Bool) (f : FunctionValue) :=
  showFunctionBody runtime compact f
/-- `show(io::IO, ::MIME"text/plain", c::ComposedFunction)`, `base/show.jl:75-75`. -/
def m75 (runtime : WrapperRuntime) (c : WrapperValue) : Out := [runtime.render c]
/-- `show(io::IO, ::MIME"text/plain", c::Returns)`, `base/show.jl:76-76`. -/
def m76 (runtime : WrapperRuntime) (c : WrapperValue) : Out := [runtime.render c]
/-- `show(io::IO, ::MIME"text/plain", s::Splat)`, `base/show.jl:77-77`. -/
def m77 (runtime : WrapperRuntime) (s : WrapperValue) : Out := [runtime.render s]
/-- `ncodeunits(c::ANSIDelimiter)`, `base/show.jl:85-85`. -/
def m85 (tok : Truncate.Tok) := Truncate.Tok.ncu tok
/-- `textwidth(::ANSIDelimiter)`, `base/show.jl:86-86`. -/
def m86 (tw : Char → Nat) (tok : Truncate.Tok) := Truncate.Tok.width tw tok
/-- `ANSIIterator(s::AbstractString)`, `base/show.jl:92-92`. -/
def m92 (s : List Char) := Truncate.ansiTokens s
/-- `IteratorSize(::Type{<:ANSIIterator})`, `base/show.jl:94-94`. -/
def m94 (_iteratorType : String) := Truncate.iteratorSizeANSI
/-- `eltype(::Type{<:ANSIIterator})`, `base/show.jl:95-95`. -/
def m95 (_iteratorType : String) := Truncate.eltypeANSI
/-- `iterate(I::ANSIIterator, (i, m_st)=(1, iterate(I.captures)))`, `base/show.jl:96-101`. -/
def m96 (captures : List Capture) (i : Nat) := ansiIterStep captures i
/-- `textwidth(I::ANSIIterator)`, `base/show.jl:102-102`. -/
def m102 (tw : Char → Nat) (s : List Char) := Truncate.ansiWidth tw s
/-- `_truncate_at_width_or_chars(ignore_ANSI::Bool, str::AbstractString, width::Int, rpad::Bool=false, chars="\r\n", truncmark="…")`, `base/show.jl:104-135`. -/
def m104 (tw : Char → Nat) (ignore : Bool) (s : List Char) (width : Int) (rpad : Bool) (chars mark : List Char) := Truncate.truncateAt tw ignore s width rpad chars mark
/-- `show(io::IO, ::MIME"text/plain", iter::Union{KeySet,ValueIterator})`, `base/show.jl:137-166`. -/
def m137 (runtime : IterRuntime) (iter : IterValue) := showKeyValueBody runtime iter
/-- `show(io::IO, ::MIME"text/plain", t::AbstractDict{K,V}) where {K,V}`, `base/show.jl:168-233`. -/
def m168 (runtime : DictRuntime) (dict : DictValue) := showDictBody runtime dict
/-- `summary(io::IO, t::AbstractSet)`, `base/show.jl:235-239`. -/
def m235 (runtime : SetRuntime) (set : SetValue) : Out :=
  [runtime.showarg set true, " with ", toString set.elements.length,
    if set.elements.length = 1 then " element" else " elements"]
/-- `show(io::IO, ::MIME"text/plain", t::AbstractSet{T}) where T`, `base/show.jl:241-276`. -/
def m241 (runtime : SetRuntime) (set : SetValue) := showSetBody runtime set
/-- `show(io::IO, ::MIME"text/plain", opt::JLOptions)`, `base/show.jl:278-292`. -/
def m278 (runtime : JLOptionsRuntime) (opt : JLOptionsValue) :=
  showJLOptionsBody runtime opt
/-- `show(io::IO, ::MIME"text/plain", t::Task)`, `base/show.jl:294-300`. -/
def m294 (runtime : TaskRuntime) (task : TaskValue) := showTaskBody runtime task
/-- `show(io::IO, src::Core.CancellationTokenSource)`, `base/show.jl:304-319`. -/
def m304 (runtime : CancellationRuntime) (source : CancellationValue) :=
  showCancellationBody runtime source
/-- `print(io::IO, s::Symbol)`, `base/show.jl:322-322`. -/
def m322 (name : String) := Values.printSymbol name
/-- `IOContext{IO_t}(io::IO_t, dict::ImmutableDict{Symbol, Any}) where IO_t<:IO`, `base/show.jl:336-339`. -/
def m336 (io : IOCtx.JIO) (dict : IOCtx.IDict) := IOCtx.mkCtx io dict
/-- `ioproperties(io::IO)`, `base/show.jl:343-343`. -/
def m343 (runtime : IOContextRuntime) (io : IOCtx.BaseIO) : IOCtx.IDict :=
  if runtime.getColor io then [("color", .bool true)] else []
/-- `ioproperties(io::IOContext)`, `base/show.jl:344-344`. -/
def m344 (io : IOCtx.JIO) := IOCtx.ioproperties io
/-- `unwrapcontext(io::IO)`, `base/show.jl:346-346`. -/
def m346 (io : IOCtx.JIO) := IOCtx.unwrapcontext io
/-- `unwrapcontext(io::IOContext)`, `base/show.jl:347-347`. -/
def m347 (io : IOCtx.JIO) := IOCtx.unwrapcontext io
/-- `IOContext(io::IO, dict::ImmutableDict{Symbol, Any})`, `base/show.jl:349-351`. -/
def m349 (io : IOCtx.JIO) (dict : IOCtx.IDict) := IOCtx.ioContextDict io dict
/-- `IOContext(io::IOContext, dict::ImmutableDict{Symbol, Any})`, `base/show.jl:353-355`. -/
def m353 (io : IOCtx.JIO) (dict : IOCtx.IDict) := IOCtx.ioContextDict io dict
/-- `convert(::Type{IOContext}, io::IOContext)`, `base/show.jl:358-358`. -/
def m358 (io : IOCtx.JIO) := IOCtx.convertCtx io
/-- `convert(::Type{IOContext}, io::IO)`, `base/show.jl:359-359`. -/
def m359 (io : IOCtx.JIO) := IOCtx.convertCtx io
/-- `convert(::Type{IOContext{IO_t}}, io::IOContext{IO_t}) where {IO_t}`, `base/show.jl:360-360`. -/
def m360 (io : IOCtx.JIO) := IOCtx.convertCtx io
/-- `convert(::Type{IOContext{IO_t}}, io::IO) where {IO_t}`, `base/show.jl:361-361`. -/
def m361 (io : IOCtx.JIO) := IOCtx.convertCtx io
/-- `IOContext(io::IO)`, `base/show.jl:363-363`. -/
def m363 (io : IOCtx.JIO) := IOCtx.ioContext1 io
/-- `IOContext{IO_t}(io::IO) where {IO_t}`, `base/show.jl:364-364`. -/
def m364 (io : IOCtx.JIO) := IOCtx.ioContext1 io
/-- `IOContext(io::IO, KV::Pair)`, `base/show.jl:366-369`. -/
def m366 (io : IOCtx.JIO) (kv : String × IOCtx.PV) := IOCtx.ioContextPair io kv
/-- `IOContext(io::IO, context::IO)`, `base/show.jl:381-381`. -/
def m381 (io context : IOCtx.JIO) := IOCtx.ioContextIO io context
/-- `IOContext(io::IO, KV::Pair, KVs::Pair...)`, `base/show.jl:456-456`. -/
def m456 (io : IOCtx.JIO) (kvs : List (String × IOCtx.PV)) := IOCtx.ioContextPairs io kvs
/-- `show(io::IO, ctx::IOContext)`, `base/show.jl:458-458`. -/
def m458 (runtime : IOContextRuntime) (ctx : IOCtx.JIO) : Out :=
  match IOCtx.unwrapcontext ctx with
  | .plain base => ["IOContext(", runtime.renderBase base, ")"]
  | .ctx base _ => ["IOContext(", runtime.renderBase base, ")"]
/-- `pipe_reader(io::IOContext)`, `base/show.jl:460-460`. -/
def m460 (io : IOCtx.JIO) := IOCtx.pipeReader io
/-- `pipe_writer(io::IOContext)`, `base/show.jl:461-461`. -/
def m461 (io : IOCtx.JIO) := IOCtx.pipeWriter io
/-- `lock(io::IOContext)`, `base/show.jl:462-462`. -/
def m462 (io : IOCtx.JIO) := lockEffect .lock io
/-- `unlock(io::IOContext)`, `base/show.jl:463-463`. -/
def m463 (io : IOCtx.JIO) := lockEffect .unlock io
/-- `in(key_value::Pair, io::IOContext)`, `base/show.jl:465-465`. -/
def m465 (kv : String × IOCtx.PV) (io : IOCtx.JIO) := IOCtx.inCtx kv io
/-- `in(key_value::Pair, io::IO)`, `base/show.jl:466-466`. -/
def m466 (kv : String × IOCtx.PV) (base : IOCtx.BaseIO) := IOCtx.inCtx kv (.plain base)
/-- `haskey(io::IOContext, key)`, `base/show.jl:467-467`. -/
def m467 (io : IOCtx.JIO) (key : String) := IOCtx.haskeyCtx key io
/-- `haskey(io::IO, key)`, `base/show.jl:468-468`. -/
def m468 (base : IOCtx.BaseIO) (key : String) := IOCtx.haskeyCtx key (.plain base)
/-- `getindex(io::IOContext, key)`, `base/show.jl:469-469`. -/
def m469 (io : IOCtx.JIO) (key : String) := IOCtx.getindexCtx key io
/-- `getindex(io::IO, key)`, `base/show.jl:470-470`. -/
def m470 (base : IOCtx.BaseIO) (key : String) := IOCtx.getindexCtx key (.plain base)
/-- `get(io::IOContext, key, default)`, `base/show.jl:471-471`. -/
def m471 (io : IOCtx.JIO) (key : String) (default : IOCtx.PV) := IOCtx.getCtx key default io
/-- `get(io::IO, key, default)`, `base/show.jl:472-472`. -/
def m472 (base : IOCtx.BaseIO) (key : String) (default : IOCtx.PV) := IOCtx.getCtx key default (.plain base)
/-- `keys(io::IOContext)`, `base/show.jl:473-473`. -/
def m473 (io : IOCtx.JIO) := IOCtx.keysCtx io
/-- `keys(io::IO)`, `base/show.jl:474-474`. -/
def m474 (base : IOCtx.BaseIO) := IOCtx.keysCtx (.plain base)
/-- `displaysize(io::IOContext)`, `base/show.jl:476-476`. -/
def m476 (io : IOCtx.JIO) := IOCtx.displaysizeCtx io
/-- `show_circular(io::IO, @nospecialize(x))`, `base/show.jl:478-478`. -/
def m478 (x : IOCtx.PV) (base : IOCtx.BaseIO) := IOCtx.showCircular x (.plain base)
/-- `show_circular(io::IOContext, @nospecialize(x))`, `base/show.jl:479-491`. -/
def m479 (x : IOCtx.PV) (io : IOCtx.JIO) := IOCtx.showCircular x io
/-- `show(io::IO, @nospecialize(x))`, `base/show.jl:520-520`. -/
def m520 (runtime : GenericShowRuntime) (io : IOCtx.BaseIO) (x : GenericValue) :=
  runtime.showDefault io x
/-- `show(x)`, `base/show.jl:522-522`. -/
def m522 (runtime : GenericShowRuntime) (x : GenericValue) :=
  runtime.showOn runtime.stdout x
/-- `show_default(io::IO, @nospecialize(x))`, `base/show.jl:525-525`. -/
def m525 (runtime : GenericShowRuntime) (io : IOCtx.BaseIO) (x : GenericValue) :=
  runtime.showDefaultInner io (runtime.inferenceBarrier x)
/-- `_show_default(io::IO, @nospecialize(x))`, `base/show.jl:527-568`. -/
def m527 (runtime : DefaultRuntime) (io : IOCtx.BaseIO) (x : DefaultValue) :=
  showDefaultBody runtime io x
/-- `active_module()`, `base/show.jl:570-578`. -/
def m570 (runtime : ActiveModuleRuntime) := activeModuleBody runtime
/-- `show_function(io::IO, f::Function, compact::Bool, fallback::Function)`, `base/show.jl:583-601`. -/
def m583 (runtime : FunctionRuntime) (io : FunctionIO) (function : FunctionValue)
    (compact : Bool) (fallback : FunctionFallback) :=
  showFunctionCore runtime io function compact fallback
/-- `show(io::IO, f::Function)`, `base/show.jl:603-603`. -/
def m603 (runtime : FunctionRuntime) (io : FunctionIO) (function : FunctionValue) :=
  showFunctionCore runtime io function io.compact .showDefault
/-- `print(io::IO, f::Function)`, `base/show.jl:604-604`. -/
def m604 (runtime : FunctionRuntime) (io : FunctionIO) (function : FunctionValue) :=
  showFunctionCore runtime io function true .show
/-- `show(io::IO, f::Core.IntrinsicFunction)`, `base/show.jl:606-611`. -/
def m606 (io : FunctionIO) (function : FunctionValue) : String :=
  (if io.compact then "" else "Core.Intrinsics.") ++ function.datatype.typeName.singletonName
/-- `print(io::IO, f::Core.IntrinsicFunction)`, `base/show.jl:613-613`. -/
def m613 (function : FunctionValue) : String := function.datatype.typeName.singletonName
/-- `show(io::IO, ::MIME"text/plain", ::Core.TypeofBottom)`, `base/show.jl:615-615`. -/
def m615 (_io : AlignmentIO) : Out := ["Union{}"]
/-- `print_without_params(@nospecialize(x))`, `base/show.jl:617-620`. -/
def m617 (runtime : TypeRuntime) (value : TypeObject) :=
  printWithoutParamsBody runtime value
/-- `io_has_tvar_name(io::IOContext, name::Symbol, @nospecialize(x))`, `base/show.jl:622-629`. -/
def m622 (runtime : TypeVarRuntime) (io : TypeVarContext) (name : String)
    (value : TypeObject) := ioHasTypevarBody runtime io name value
/-- `io_has_tvar_name(io::IO, name::Symbol, @nospecialize(x))`, `base/show.jl:630-630`. -/
def m630 (name : String) := Remaining.ioHasTvarNamePlain name
/-- `modulesof!(s::Set{Module}, x::TypeVar)`, `base/show.jl:632-632`. -/
def m632 (upper : Remaining.TypeShape) := Remaining.modulesOf (.typeVar upper)
/-- `modulesof!(s::Set{Module}, x::TypeEq)`, `base/show.jl:633-637`. -/
def m633 (runtime : ParameterRuntime) (value : ParameterizedTypeValue) :=
  modulesTypeEqBody runtime value
/-- `modulesof!(s::Set{Module}, x::Core.TypeEgal)`, `base/show.jl:638-638`. -/
def m638 (runtime : ParameterRuntime) (value : ParameterizedTypeValue) :=
  match runtime.typeParameter value with
  | .anyType shape | .typeVar shape => Remaining.modulesOf shape
  | .nonType _ => []
/-- `modulesof!(s::Set{Module}, x::Type)`, `base/show.jl:639-652`. -/
def m639 (runtime : ModulesRuntime) (input : TypeObject) :=
  modulesOfTypeBody runtime 64 input
/-- `has_other_free_typevars(@nospecialize(x), free_before)`, `base/show.jl:654-667`. -/
def m654 (runtime : FreeTypevarRuntime) (value : TypeObject)
    (freeBefore : List TypeVarValue) := hasOtherFreeTypevarsBody runtime value freeBefore
/-- `unbounded_typealias(@nospecialize(alias))`, `base/show.jl:674-684`. -/
def m674 (runtime : AliasRuntime) (alias : AliasExpr) := unboundedAlias runtime alias
/-- `reapply_unionall_env(io::Union{IO,Nothing}, @nospecialize(x))`, `base/show.jl:692-701`. -/
def m692 (context : Option TypeVarContext) (value : TypeExpr) :=
  reapplyUnionallBody context value
/-- `make_typealias(@nospecialize(x::Type), io::Union{IO,Nothing}=nothing)`, `base/show.jl:703-767`. -/
def m703 (runtime : MakeAliasRuntime) (context : Option TypeVarContext)
    (input : TypeObject) := makeTypealiasBody runtime context input
/-- `isgensym(s::Symbol)`, `base/show.jl:769-769`. -/
def m769 (runtime : SymbolRuntime) (symbol : SymbolValue) :=
  (runtime.string symbol).contains '#'
/-- `show_can_elide(p::TypeVar, wheres::Vector, elide::Int, env::SimpleVector, skip::Int)`, `base/show.jl:771-784`. -/
def m771 (runtime : TypeRelationRuntime) (parameter : TypeVarValue)
    (wheres : List TypeVarValue) (elide : Nat) (env : List TypeSlot) (skip : Nat) :=
  showCanElideBody runtime parameter wheres elide env skip
/-- `show_typeparams(io::IO, env::SimpleVector, orig::SimpleVector, wheres::Vector)`, `base/show.jl:786-830`. -/
def m786 (runtime : TypeParamsRuntime) (env orig : List TypeSlot)
    (wheres : List TypeVarValue) := showTypeparamsBody runtime env orig wheres
/-- `egal_var(p::TypeVar, @nospecialize o)`, `base/show.jl:789-793`. -/
def m789 (runtime : TypeRelationRuntime) (parameter : TypeVarValue) (other : TypeSlot) :=
  egalVarBody runtime parameter other
/-- `show_typealias_name(io::IO, name::GlobalRef)`, `base/show.jl:832-845`. -/
def m832 (runtime : AliasNameRuntime) (reference : GlobalRefValue) :=
  showAliasNameBody runtime reference
/-- `show_typealias(io::IO, name::GlobalRef, env::SimpleVector, wheres::Vector)`, `base/show.jl:847-862`. -/
def m847 (runtime : TypeAliasRuntime) (alias : TypeAliasValue)
    (env : List TypeSlot) (wheres : List TypeVarValue) :=
  showTypealiasBody runtime alias env wheres
/-- `make_wheres(io::IO, env::SimpleVector, @nospecialize(x::Type))`, `base/show.jl:864-892`. -/
def m864 (runtime : MakeWheresRuntime) (context : Option TypeVarContext)
    (env : List TypeSlot) (value : TypeExpr) := makeWheresBody runtime context env value
/-- `show_wheres(io::IO, wheres::Vector{TypeVar})`, `base/show.jl:894-906`. -/
def m894 (runtime : WheresRuntime) (wheres : List TypeVarValue) :=
  showWheresBody runtime wheres
/-- `show_typealias(io::IO, @nospecialize(x::Type))`, `base/show.jl:908-915`. -/
def m908 (runtime : AliasDispatchRuntime) (value : TypeExpr) :=
  showTypealiasDispatchBody runtime value
/-- `make_typealiases(@nospecialize(x::Type))`, `base/show.jl:917-1000`. -/
def m917 (runtime : UnionAliasRuntime) (input : TypeObject) :=
  makeTypealiasesBody runtime input
/-- `show_unionaliases(io::IO, x::Union)`, `base/show.jl:1002-1044`. -/
def m1002 (runtime : ShowUnionRuntime) (input : TypeObject) :=
  showUnionAliasesBody runtime input
/-- `show(io::IO, ::MIME"text/plain", @nospecialize(x::Type))`, `base/show.jl:1046-1069`. -/
def m1046 (runtime : TypePlainRuntime) (input : TypeObject) :=
  showTypePlainBody runtime input
/-- `show_typeegal(io::IO, @nospecialize(x::Core.TypeEgal))`, `base/show.jl:1071-1075`. -/
def m1071 (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) :=
  showTypeEgalBody runtime value
/-- `show(io::IO, @nospecialize(x::Core.AnyType))`, `base/show.jl:1076-1086`. -/
def m1076 (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) :=
  showAnyTypeBody runtime value
/-- `show_typeeq(io::IO, @nospecialize(x::TypeEq))`, `base/show.jl:1091-1095`. -/
def m1091 (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) :=
  showTypeEqBody runtime value
/-- `_show_type(io::IO, @nospecialize(x::Type))`, `base/show.jl:1096-1152`. -/
def m1096 (runtime : TypeDispatchRuntime) (input : TypeObject) :=
  showTypeDispatchBody runtime input
/-- `isvisible(sym::Symbol, parent::Module, from::Module)`, `base/show.jl:1159-1177`. -/
def m1159 (runtime : VisibilityRuntime) (symbol : SymbolValue)
    (parent origin : ModuleValue) := isVisibleBody runtime symbol parent origin
/-- `is_global_function(tn::Core.TypeName, globname::Union{Symbol,Nothing})`, `base/show.jl:1179-1189`. -/
def m1179 (runtime : GlobalFunctionRuntime) (typeName : TypeNameValue)
    (globalName : Option String) := isGlobalFunctionBody runtime typeName globalName
/-- `check_world_bounded(tn::Core.TypeName)`, `base/show.jl:1191-1209`. -/
def m1191 (runtime : WorldRuntime) (typeName : TypeNameValue) :=
  checkWorldBody runtime typeName
/-- `show_type_name(io::IO, tn::Core.TypeName)`, `base/show.jl:1211-1246`. -/
def m1211 (runtime : ShowTypeNameRuntime) (typeName : TypeNameValue) :=
  showTypeNameBody runtime typeName
/-- `maybe_kws_nt(x::DataType)`, `base/show.jl:1248-1264`. -/
def m1248 (runtime : KwargsRuntime) (datatype : DatatypeModel) :=
  maybeKwargsBody runtime datatype
/-- `show_datatype(io::IO, x::DataType, wheres::Vector{TypeVar}=TypeVar[])`, `base/show.jl:1266-1360`. -/
def m1266 (runtime : DatatypeRuntime) (datatype : DatatypeModel)
    (wheres : List TypeVarValue) := showDatatypeBody runtime datatype wheres
/-- `show_at_namedtuple(io::IO, syms::Tuple, types::DataType)`, `base/show.jl:1362-1376`. -/
def m1362 (runtime : DatatypeRuntime) (symbols : List SymbolValue)
    (types : List TypeObject) := showNamedTupleFields runtime symbols types
/-- `show_supertypes(io::IO, typ::DataType)`, `base/show.jl:1378-1384`. -/
def m1378 (runtime : SupertypeRuntime) (type : TypeObject) :=
  showSupertypesBody runtime 64 type
/-- `show_supertypes(typ::DataType)`, `base/show.jl:1386-1386`. -/
def m1386 (runtime : SupertypeRuntime) (type : TypeObject) := m1378 runtime type
/-- `show(exs...)`, `base/show.jl:1406-1414`. -/
def m1406 (runtime : ShowMacroRuntime) (expressions : List AstValue) :=
  showMacroBody runtime expressions
/-- `show(io::IO, tn::Core.TypeName)`, `base/show.jl:1416-1420`. -/
def m1416 (runtime : ShowTypeNameRuntime) (name : TypeNameValue) :=
  "typename(" ++ m1211 runtime name ++ ")"
/-- `nonnothing_nonmissing_typeinfo(io::IO)`, `base/show.jl:1422-1422`. -/
def m1422 (runtime : ScalarRuntime) (io : ScalarIO) :=
  nonnothingNonmissingBody runtime io
/-- `show(io::IO, b::Bool)`, `base/show.jl:1423-1423`. -/
def m1423 (runtime : ScalarRuntime) (io : ScalarIO) (value : Bool) :=
  showBoolBody runtime io value
/-- `show(io::IO, ::Nothing)`, `base/show.jl:1424-1424`. -/
def m1424 (_io : ScalarIO) : Out := ["nothing"]
/-- `show(io::IO, n::Signed)`, `base/show.jl:1425-1425`. -/
def m1425 (runtime : ScalarRuntime) (value : SignedValue) : Out :=
  [runtime.stringSigned value]
/-- `show(io::IO, n::Unsigned)`, `base/show.jl:1426-1436`. -/
def m1426 (runtime : ScalarRuntime) (io : ScalarIO) (value : UnsignedValue) :=
  showUnsignedBody runtime io value
/-- `print(io::IO, n::Unsigned)`, `base/show.jl:1437-1437`. -/
def m1437 (runtime : ScalarRuntime) (value : UnsignedValue) : Out :=
  [runtime.stringUnsignedDecimal value]
/-- `has_tight_type(p::Pair)`, `base/show.jl:1439-1441`. -/
def m1439 (runtime : PairRuntime) (pair : PairValue) := hasTightTypeBody runtime pair
/-- `isdelimited(io::IO, x)`, `base/show.jl:1443-1443`. -/
def m1443 (_io x : String) := Values.isdelimitedAny
/-- `isdelimited(io::IO, x::Function)`, `base/show.jl:1444-1444`. -/
def m1444 (runtime : PairRuntime) (function : FunctionValue) :=
  !runtime.isOperator (runtime.symbolOfFunction function)
/-- `isdelimited(io::IO, p::Pair)`, `base/show.jl:1448-1448`. -/
def m1448 (runtime : PairRuntime) (io : PairIO) (pair : PairValue) :=
  pairDelimitedBody runtime io pair
/-- `gettypeinfos(io::IO, p::Pair)`, `base/show.jl:1450-1455`. -/
def m1450 (runtime : PairRuntime) (io : PairIO) (pair : PairValue) :=
  pairTypeinfosBody runtime io pair
/-- `show(io::IO, p::Pair)`, `base/show.jl:1457-1467`. -/
def m1457 (runtime : PairRuntime) (io : PairIO) (pair : PairValue) :=
  showPairBody runtime io pair
/-- `show_pairtyped(io::IO, p::Pair{K,V}) where {K,V}`, `base/show.jl:1469-1472`. -/
def m1469 (runtime : PairRuntime) (pair : PairValue) : Out :=
  [runtime.renderType (runtime.typeOfPair pair), runtime.renderTuple pair.first pair.second]
/-- `show(io::IO, m::Module)`, `base/show.jl:1474-1480`. -/
def m1474 (runtime : ModuleRuntime) (module : ModuleValue) := showModuleBody runtime module
/-- `print_fullname(io::IO, m::Module)`, `base/show.jl:1484-1493`. -/
def m1484 (runtime : ModuleRuntime) (module : ModuleValue) :=
  printFullnameBody runtime runtime.moduleCount module
/-- `sourceinfo_slotnames(src::CodeInfo)`, `base/show.jl:1495-1495`. -/
def m1495 (runtime : SlotRuntime) (source : CodeInfoValue) :=
  sourceSlotnamesBody runtime source.slotnames
/-- `sourceinfo_slotnames(slotnames::Vector{Symbol})`, `base/show.jl:1496-1516`. -/
def m1496 (runtime : SlotRuntime) (slotnames : List SymbolValue) :=
  sourceSlotnamesBody runtime slotnames
/-- `show(io::IO, mi::Core.MethodInstance)`, `base/show.jl:1518-1518`. -/
def m1518 (runtime : MethodRuntime) (miValue : MethodInstanceValue) :=
  showMethodInstanceBody runtime miValue false
/-- `show(io::IO, codeinst::Core.CodeInstance)`, `base/show.jl:1519-1531`. -/
def m1519 (runtime : MethodRuntime) (codeValue : CodeInstanceValue) :=
  showCodeInstanceBody runtime codeValue
/-- `show_mi(io::IO, mi::Core.MethodInstance, from_stackframe::Bool=false)`, `base/show.jl:1533-1560`. -/
def m1533 (runtime : MethodRuntime) (miValue : MethodInstanceValue)
    (fromStackframe : Bool) := showMethodInstanceBody runtime miValue fromStackframe
/-- `show_delim_array(io::IO, itr::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one, i1=first(LinearIndices(itr)), l=last(LinearIndices(itr)))`, `base/show.jl:1562-1589`. -/
def m1562 (runtime : DelimArrayRuntime) (array : DelimArrayValue)
    (op delim close : String) (delimOne : Bool) (first last : Int) :=
  Containers.showDelimArray (delimArrayElement runtime array) op delim close delimOne
    (runtime.showCircular array) first last
/-- `show_delim_array(io::IO, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int))`, `base/show.jl:1591-1623`. -/
def m1591 (runtime : DelimIteratorRuntime) (iterator : IteratorValue)
    (op delim close : String) (delimOne : Bool) (first : Nat) (count : Int) :=
  showDelimIteratorBody runtime iterator op delim close delimOne first count
/-- `show(io::IO, t::Tuple)`, `base/show.jl:1625-1625`. -/
def m1625 (runtime : DelimArrayRuntime) (tuple : DelimArrayValue) :=
  m1562 runtime tuple "(" "," ")" true 1 tuple.slots.length
/-- `show(io::IO, v::SimpleVector)`, `base/show.jl:1626-1626`. -/
def m1626 (runtime : DelimArrayRuntime) (vector : DelimArrayValue) :=
  m1562 runtime vector "svec(" "," ")" false 1 vector.slots.length
/-- `show(io::IO, s::Symbol)`, `base/show.jl:1628-1628`. -/
def m1628 (runtime : ExprRuntime) (io : ExprContext) (symbol : JStr) :=
  runtime.showQuoteSymbol io symbol 0 0
/-- `print( io::IO, ex::ExprNode)`, `base/show.jl:1666-1666`. -/
def m1666 (runtime : ExprRuntime) (io : ExprContext) (expression : JE) :=
  runtime.showUnquoted ⟨false⟩ expression 0 (-1)
/-- `show( io::IO, ex::ExprNode)`, `base/show.jl:1667-1667`. -/
def m1667 (runtime : ExprRuntime) (io : ExprContext) (expression : JE) :=
  runtime.showQuoteExpr ⟨true⟩ expression 0 (-1)
/-- `show_unquoted(io::IO, ex)`, `base/show.jl:1668-1668`. -/
def m1668 (runtime : ExprRuntime) (io : ExprContext) (expression : JE) :=
  runtime.showUnquoted io expression 0 0
/-- `show_unquoted(io::IO, ex, indent::Int)`, `base/show.jl:1669-1669`. -/
def m1669 (runtime : ExprRuntime) (io : ExprContext) (expression : JE) (indent : Int) :=
  runtime.showUnquoted io expression indent 0
/-- `show_unquoted(io::IO, ex, ::Int,::Int)`, `base/show.jl:1670-1670`. -/
def m1670 (runtime : ExprRuntime) (io : ExprContext) (value : DelimElement) :=
  runtime.showFallback io value
/-- `show_unquoted(io::IO, ex, indent::Int, prec::Int, ::Int)`, `base/show.jl:1671-1671`. -/
def m1671 (runtime : ExprRuntime) (io : ExprContext) (expression : JE)
    (indent prec _quoteLevel : Int) := runtime.showUnquoted io expression indent prec
/-- `operator_precedence(s::Symbol)`, `base/show.jl:1713-1713`. -/
def m1713 (runtime : OperatorRuntime) (symbol : SymbolValue) := runtime.precedence symbol
/-- `operator_precedence(x::Any)`, `base/show.jl:1714-1714`. -/
def m1714 (_x : String) := Remaining.operatorPrecedenceAny
/-- `operator_associativity(s::Symbol)`, `base/show.jl:1739-1748`. -/
def m1739 (runtime : OperatorRuntime) (symbol : SymbolValue) :=
  operatorAssociativityBody runtime symbol
/-- `is_quoted(ex)`, `base/show.jl:1750-1750`. -/
def m1750 (_ex : DelimElement) := false
/-- `is_quoted(ex::QuoteNode)`, `base/show.jl:1751-1751`. -/
def m1751 (_node : QuoteNodeValue) := true
/-- `is_quoted(ex::Expr)`, `base/show.jl:1752-1752`. -/
def m1752 (expression : ExprValue) :=
  (expression.head = "quote" || expression.head = "inert") && expression.args.length = 1
/-- `unquoted(ex::QuoteNode)`, `base/show.jl:1754-1754`. -/
def m1754 (node : QuoteNodeValue) := node.value
/-- `unquoted(ex::Expr)`, `base/show.jl:1755-1755`. -/
def m1755 (expression : ExprValue) : R DelimElement :=
  match expression.args with | value :: _ => .ok value | [] => .error .boundsError
/-- `emphasize(io, str::AbstractString, col = Base.error_color())`, `base/show.jl:1762-1764`. -/
def m1762 (runtime : StyleRuntime) (io : StyledIO) (text color : String) :=
  emphasizeBody runtime io text color
/-- `show_linenumber(io::IO, line)`, `base/show.jl:1766-1766`. -/
def m1766 (runtime : StyleRuntime) (line : DelimElement) := showLineBody runtime line none
/-- `show_linenumber(io::IO, line, file)`, `base/show.jl:1767-1767`. -/
def m1767 (runtime : StyleRuntime) (line file : DelimElement) :=
  showLineBody runtime line (some file)
/-- `show_linenumber(io::IO, line, file::Nothing)`, `base/show.jl:1768-1768`. -/
def m1768 (runtime : StyleRuntime) (line : DelimElement) := m1766 runtime line
/-- `show_block(io::IO, head, args::Vector, body, indent::Int, quote_level::Int)`, `base/show.jl:1771-1789`. -/
def m1771 (runtime : AstRuntime) (head : String) (arguments : List AstValue)
    (body : AstValue) (indent quoteLevel : Int) :=
  showAstBlockBody runtime head arguments body indent quoteLevel
/-- `show_block(io::IO,head, block,i::Int, quote_level::Int)`, `base/show.jl:1790-1790`. -/
def m1790 (runtime : AstRuntime) (head : String) (body : AstValue)
    (indent quoteLevel : Int) := m1771 runtime head [] body indent quoteLevel
/-- `show_block(io::IO, head, arg, block, i::Int, quote_level::Int)`, `base/show.jl:1791-1797`. -/
def m1791 (runtime : AstRuntime) (head : String) (argument body : AstValue)
    (indent quoteLevel : Int) :=
  let arguments := match argument with
    | .expr "block" args | .expr "quote" args => args
    | _ => [argument]
  m1771 runtime head arguments body indent quoteLevel
/-- `show_list(io::IO, items, sep, indent::Int, prec::Int=0, quote_level::Int=0, enclose_operators::Bool=false, kw::Bool=false)`, `base/show.jl:1800-1826`. -/
def m1800 (runtime : AstRuntime) (items : List AstValue) (separator : String)
    (indent prec quoteLevel : Int) (encloseOperators keyword : Bool) :=
  showAstListBody runtime items separator indent prec quoteLevel encloseOperators keyword
/-- `show_enclosed_list(io::IO, op, items, sep, cl, indent, prec=0, quote_level=0, encl_ops=false, kw::Bool=false)`, `base/show.jl:1828-1832`. -/
def m1828 (runtime : AstRuntime) (openToken : String) (items : List AstValue)
    (separator closeToken : String) (indent prec quoteLevel : Int)
    (encloseOperators keyword : Bool) := openToken ++
  m1800 runtime items separator indent prec quoteLevel encloseOperators keyword ++ closeToken
/-- `show_call(io::IO, head, func, func_args, indent, quote_level, kw::Bool)`, `base/show.jl:1837-1862`. -/
def m1837 (runtime : AstRuntime) (head : String) (function : AstValue)
    (arguments : List AstValue) (indent quoteLevel : Int) (keyword : Bool) :=
  showAstCallBody runtime head function arguments indent quoteLevel keyword
/-- `show_sym(io::IO, sym::Symbol; allow_macroname=false)`, `base/show.jl:1867-1876`. -/
def m1867 (runtime : SymbolPrintRuntime) (symbol : SymbolValue) (allowMacroname : Bool) :=
  showSymBody runtime symbol allowMacroname
/-- `show_unquoted(io::IO, val::SSAValue, ::Int, ::Int)`, `base/show.jl:1880-1894`. -/
def m1880 (runtime : SSARuntime) (io : StyledIO) (value : SSAValueModel) :=
  showSSABody runtime io value
/-- `show_unquoted(io::IO, sym::Symbol, ::Int, ::Int)`, `base/show.jl:1895-1895`. -/
def m1895 (runtime : SymbolPrintRuntime) (symbol : SymbolValue) :=
  showSymBody runtime symbol false
/-- `show_unquoted(io::IO, ex::LineNumberNode, ::Int, ::Int)`, `base/show.jl:1896-1896`. -/
def m1896 (runtime : StyleRuntime) (node : LineNodeModel) :=
  showLineBody runtime node.line node.file
/-- `show_unquoted(io::IO, ex::GotoNode, ::Int, ::Int)`, `base/show.jl:1897-1897`. -/
def m1897 (label : Int) := Remaining.showGotoNode label
/-- `show_unquoted(io::IO, ex::GlobalRef, ::Int, ::Int)`, `base/show.jl:1898-1898`. -/
def m1898 (runtime : GlobalRefRuntime) (reference : GlobalRefModel) :=
  showGlobalRefBody runtime reference false
/-- `show_unquoted(io::IO, bpart::Core.BindingPartition, ::Int, ::Int)`, `base/show.jl:1899-1900`. -/
def m1899 (runtime : GlobalRefRuntime) (partition : BindingPartitionModel) :=
  showGlobalRefBody runtime partition.owner false
/-- `show_globalref(io::IO, ex::GlobalRef; allow_macroname=false)`, `base/show.jl:1902-1912`. -/
def m1902 (runtime : GlobalRefRuntime) (reference : GlobalRefModel)
    (allowMacroname : Bool) := showGlobalRefBody runtime reference allowMacroname
/-- `show_unquoted(io::IO, ex::SlotNumber, ::Int, ::Int)`, `base/show.jl:1914-1922`. -/
def m1914 (io : SlotIO) (slot : SlotNumberModel) := showSlotBody io slot
/-- `show_unquoted(io::IO, ex::QuoteNode, indent::Int, _prec::Int)`, `base/show.jl:1924-1935`. -/
def m1924 (runtime : QuoteRuntime) (io : ExprContext) (node : QuoteNodeModel)
    (indent : Int) := showQuoteNodeBody runtime io node indent
/-- `show_unquoted_quote_expr(io::IO, @nospecialize(value), indent::Int, quote_level::Int)`, `base/show.jl:1937-1960`. -/
def m1937 (runtime : QuoteRuntime) (io : ExprContext) (value : QuoteContent)
    (indent quoteLevel : Int) := showQuotedBody runtime io value indent quoteLevel
/-- `show_generator(io, ex::Expr, indent, quote_level)`, `base/show.jl:1962-1981`. -/
def m1962 (runtime : GeneratorRuntime) (expression : GeneratorExpr)
    (indent quoteLevel : Int) := showGeneratorBody runtime expression indent quoteLevel
/-- `valid_import_path(@nospecialize(ex), allow_as = true)`, `base/show.jl:1983-1988`. -/
def m1983 (node : ImportNode) (allowAs : Bool) := validImportPathBody node allowAs
/-- `show_import_path(io::IO, ex, quote_level)`, `base/show.jl:1990-2020`. -/
def m1990 (runtime : ImportRuntime) (node : ImportNode) (quoteLevel : Int) :=
  showImportPathBody runtime node quoteLevel
/-- `allow_macroname(ex)`, `base/show.jl:2023-2032`. -/
def m2023 (runtime : SymbolPrintRuntime) (node : ImportNode) := allowMacronameBody runtime node
/-- `is_core_macro(arg::GlobalRef, macro_name::AbstractString)`, `base/show.jl:2034-2034`. -/
def m2034 (runtime : SymbolPrintRuntime) (reference : GlobalRefModel) (macroName : String) :=
  isCoreMacroBody reference (runtime.symbolFromString macroName)
/-- `is_core_macro(arg::GlobalRef, macro_name::Symbol)`, `base/show.jl:2035-2035`. -/
def m2035 (reference : GlobalRefModel) (macroName : SymbolValue) :=
  isCoreMacroBody reference macroName
/-- `is_core_macro(@nospecialize(arg), macro_name::AbstractString)`, `base/show.jl:2036-2036`. -/
def m2036 (_arg : DelimElement) (_macroName : String) := false
/-- `is_core_macro(@nospecialize(arg), macro_name::Symbol)`, `base/show.jl:2037-2037`. -/
def m2037 (_arg : DelimElement) (_macroName : SymbolValue) := false
/-- `show_unquoted_expr_fallback(io::IO, ex::Expr)`, `base/show.jl:2043-2051`. -/
def m2043 (runtime : ExprFallbackRuntime) (expression : ExprFallbackValue) :=
  showExprFallbackBody runtime expression
/-- `show_unquoted(io::IO, ex::Expr, indent::Int, prec::Int, quote_level::Int = 0)`, `base/show.jl:2054-2606`. -/
def m2054 (runtime : FullExprRuntime) (unquoteFallback beginsym : Bool)
    (expression : AstValue) (indent prec quoteLevel : Int) :=
  showExprFullBody runtime unquoteFallback beginsym expression indent prec quoteLevel
/-- `demangle_function_name(name::Symbol)`, `base/show.jl:2608-2608`. -/
def m2608 (runtime : SymbolPrintRuntime) (name : SymbolValue) :=
  runtime.symbolFromString (demangleFunctionBody (runtime.string name))
/-- `demangle_function_name(name::AbstractString)`, `base/show.jl:2609-2616`. -/
def m2609 (name : String) := demangleFunctionBody name
/-- `show_signature_function(io::IO, @nospecialize(ft), demangle=false, fargname="", html=false, qualified=false)`, `base/show.jl:2620-2643`. -/
def m2620 (runtime : SignatureRuntime) (input : TypeObject) (demangle : Bool)
    (argumentName : String) (html qualified : Bool) :=
  showSignatureFunctionBody runtime input demangle argumentName html qualified
/-- `print_within_stacktrace(io, s...; color=:normal, bold=false)`, `base/show.jl:2645-2651`. -/
def m2645 (io : StacktraceIO) (pieces : List String) (color : String) (bold : Bool) :=
  printWithinStacktraceBody io pieces color bold
/-- `show_tuple_as_call(out::IO, name::Symbol, sig::Type; demangle=false, kwargs=nothing, argnames=nothing, qualified=false, hasfirst=true)`, `base/show.jl:2653-2710`. -/
def m2653 (runtime : TupleCallRuntime) (name : SymbolValue) (signature : SignatureType)
    (demangle : Bool) (kwargs : Option (List (SymbolValue × TypeObject)))
    (argumentNames : Option (List SymbolValue)) (qualified hasFirst : Bool) :=
  showTupleCallBody runtime name signature demangle kwargs argumentNames qualified hasFirst
/-- `type_limited_string_from_context(out::IO, str::String)`, `base/show.jl:2712-2723`. -/
def m2712 (runtime : TypeLimitRuntime) (context : TypeLimitContext) (text : String) :=
  typeLimitedBody runtime context text
/-- `type_depth_limit(str::String, n::Int; maxdepth = nothing)`, `base/show.jl:2726-2816`. -/
def m2726 (tw : Char → Nat) (s : List Char) (width : Int) (maxDepth : Option Int) := Truncate.typeDepthLimit tw s width maxDepth
/-- `stateis(s)`, `base/show.jl:2734-2734`. -/
def m2734 (state bit : Nat) := (state &&& bit) != 0
/-- `quoted()`, `base/show.jl:2735-2735`. -/
def m2735 (state : Nat) := m2734 state 2 || m2734 state 4
/-- `enter(s)`, `base/show.jl:2736-2736`. -/
def m2736 (state bit : Nat) := state ||| bit
/-- `leave(s)`, `base/show.jl:2737-2737`. -/
def m2737 (state bit : Nat) := state - (state &&& bit)
/-- `print_type_bicolor(io, type; kwargs...)`, `base/show.jl:2818-2821`. -/
def m2818 (runtime : TypeColorRuntime) (io : StacktraceIO) (type : TypeObject)
    (color innerColor : String) (useColor : Bool) :=
  printTypeBicolorText (runtime.renderType type io) color innerColor useColor
/-- `print_type_bicolor(io, str::String; color=:normal, inner_color=:light_black, use_color::Bool=true)`, `base/show.jl:2823-2838`. -/
def m2823 (text color innerColor : String) (useColor : Bool) :=
  printTypeBicolorText text color innerColor useColor
/-- `resolvebinding(@nospecialize(ex))`, `base/show.jl:2840-2840`. -/
def m2840 (node : BindingNode) := BindingResult.value node
/-- `resolvebinding(ex::QuoteNode)`, `base/show.jl:2841-2841`. -/
def m2841 (value : BindingNode) := BindingResult.value value
/-- `resolvebinding(ex::Symbol)`, `base/show.jl:2842-2842`. -/
def m2842 (runtime : BindingRuntime) (symbol : SymbolValue) :=
  resolveGlobalBody runtime ⟨runtime.mainModule, symbol⟩
/-- `resolvebinding(ex::Expr)`, `base/show.jl:2843-2851`. -/
def m2843 (runtime : BindingRuntime) (expression : BindingNode) :=
  resolveBindingBody runtime 32 expression
/-- `resolvebinding(ex::GlobalRef)`, `base/show.jl:2852-2858`. -/
def m2852 (runtime : BindingRuntime) (reference : GlobalRefModel) :=
  resolveGlobalBody runtime reference
/-- `ismodulecall(ex::Expr)`, `base/show.jl:2860-2864`. -/
def m2860 (runtime : BindingRuntime) (expression : BindingNode) :=
  isModuleCallBody runtime expression
/-- `show(io::IO, tv::TypeVar)`, `base/show.jl:2866-2899`. -/
def m2866 (runtime : TypeVarShowRuntime) (context : TypeVarContext)
    (typevar : TypeVarValue) := showTypevarBody runtime context typevar
/-- `show_bound(io::IO, @nospecialize(b))`, `base/show.jl:2873-2879`. -/
def m2873 (runtime : TypeVarShowRuntime) (bound : TypeObject) := showBoundBody runtime bound
/-- `show(io::IO, vm::Core.TypeofVararg)`, `base/show.jl:2901-2912`. -/
def m2901 (runtime : VarargRuntime) (value : VarargValue) := showVarargBody runtime value
/-- `show(io::IO, src::CodeInfo; debuginfo::Symbol=:source)`, `base/show.jl:2916-2929`. -/
def m2916 (runtime : CodeInfoRuntime) (source : CodeInfoModel) (debugInfo : String) :=
  showCodeInfoBody runtime source debugInfo
/-- `show_unquoted(io::IO, val::Argument, indent::Int, prec::Int)`, `base/show.jl:2931-2931`. -/
def m2931 (io : SlotIO) (argument : ArgumentNode) := m1914 io ⟨argument.n⟩
/-- `show_unquoted(io::IO, stmt::PhiNode, indent::Int, ::Int)`, `base/show.jl:2933-2933`. -/
def m2933 (runtime : IRNodeRuntime) (node : PhiNodeValue) (indent : Int) :=
  showPhiBody runtime node indent "%"
/-- `show_unquoted_phinode(io::IO, stmt::PhiNode, indent::Int, prefix::String)`, `base/show.jl:2934-2947`. -/
def m2934 (runtime : IRNodeRuntime) (node : PhiNodeValue) (indent : Int)
    (labelPrefix : String) := showPhiBody runtime node indent labelPrefix
/-- `show_unquoted(io::IO, stmt::PhiCNode, indent::Int, ::Int)`, `base/show.jl:2949-2957`. -/
def m2949 (runtime : IRNodeRuntime) (node : PhiCNodeValue) (indent : Int) :=
  showPhiCBody runtime node indent
/-- `show_unquoted(io::IO, stmt::PiNode, indent::Int, ::Int)`, `base/show.jl:2959-2965`. -/
def m2959 (runtime : IRNodeRuntime) (node : PiNodeValue) (indent : Int) : List WriteEvent :=
  [.plain ("π (" ++ runtime.renderUnquoted node.value indent ++ ", "),
    .styled (runtime.renderType node.type) "cyan" false, .plain ")"]
/-- `show_unquoted(io::IO, stmt::UpsilonNode, indent::Int, ::Int)`, `base/show.jl:2967-2973`. -/
def m2967 (runtime : IRNodeRuntime) (node : OptionalNodeValue) (indent : Int) :=
  "ϒ (" ++ (match node.value with
    | some value => runtime.renderUnquoted value indent
    | none => "#undef") ++ ")"
/-- `show_unquoted(io::IO, stmt::ReturnNode, indent::Int, ::Int)`, `base/show.jl:2975-2982`. -/
def m2975 (runtime : IRNodeRuntime) (node : OptionalNodeValue) (indent : Int) :=
  match node.value with
  | none => "unreachable"
  | some value => "return " ++ runtime.renderUnquoted value indent
/-- `show_unquoted(io::IO, stmt::GotoIfNot, indent::Int, ::Int)`, `base/show.jl:2984-2984`. -/
def m2984 (runtime : IRNodeRuntime) (node : GotoIfNotValue) (indent : Int) :=
  showGotoIfNotBody runtime node indent "%"
/-- `show_unquoted_gotoifnot(io::IO, stmt::GotoIfNot, indent::Int, prefix::String)`, `base/show.jl:2985-2988`. -/
def m2985 (runtime : IRNodeRuntime) (node : GotoIfNotValue) (indent : Int)
    (labelPrefix : String) := showGotoIfNotBody runtime node indent labelPrefix
/-- `dump(io::IOContext, x::SimpleVector, n::Int, indent)`, `base/show.jl:2990-3008`. -/
def m2990 (runtime : DumpRuntime) (limit : Bool) (depth : Nat)
    (indent : String) (value : DumpValue) := dumpBody runtime limit depth indent value
/-- `dump(io::IOContext, @nospecialize(x), n::Int, indent)`, `base/show.jl:3010-3041`. -/
def m3010 (runtime : DumpRuntime) (limit : Bool) (depth : Nat)
    (indent : String) (value : DumpValue) := dumpBody runtime limit depth indent value
/-- `dump(io::IOContext, x::Module, n::Int, indent)`, `base/show.jl:3043-3043`. -/
def m3043 (runtime : DumpRuntime) (module : ModuleValue) :=
  dumpBody runtime false 0 "" (.module module)
/-- `dump(io::IOContext, x::String, n::Int, indent)`, `base/show.jl:3044-3044`. -/
def m3044 (runtime : DumpRuntime) (value : String) :=
  dumpBody runtime false 0 "" (.string value)
/-- `dump(io::IOContext, x::Symbol, n::Int, indent)`, `base/show.jl:3045-3045`. -/
def m3045 (runtime : DumpRuntime) (symbol : SymbolValue) :=
  dumpBody runtime false 0 "" (.symbol symbol)
/-- `dump(io::IOContext, x::Union, n::Int, indent)`, `base/show.jl:3046-3046`. -/
def m3046 (runtime : DumpRuntime) (type : TypeObject) :=
  dumpBody runtime false 0 "" (.unionType type)
/-- `dump(io::IOContext, x::Ptr, n::Int, indent)`, `base/show.jl:3047-3047`. -/
def m3047 (runtime : DumpRuntime) (address : Nat) :=
  dumpBody runtime false 0 "" (.pointer address)
/-- `dump_elts(io::IOContext, x::Array, n::Int, indent, i0, i1)`, `base/show.jl:3049-3059`. -/
def m3049 (runtime : DumpRuntime) (depth : Nat) (indent : String)
    (slots : List (Option DumpValue)) (first last : Nat) :=
  dumpElementsBody runtime depth indent slots first last
/-- `dump(io::IOContext, x::Array, n::Int, indent)`, `base/show.jl:3061-3084`. -/
def m3061 (runtime : DumpRuntime) (limit : Bool) (depth : Nat) (indent : String)
    (array : DumpValue) := dumpBody runtime limit depth indent array
/-- `dump(io::IOContext, x::DataType, n::Int, indent)`, `base/show.jl:3087-3126`. -/
def m3087 (runtime : DumpRuntime) (depth : Nat) (indent : String)
    (datatype : DumpDatatype) := dumpBody runtime false depth indent (.datatype datatype)
/-- `dump(io::IO, @nospecialize(x); maxdepth=DUMP_DEFAULT_MAXDEPTH)`, `base/show.jl:3130-3133`. -/
def m3130 (runtime : DumpRuntime) (limit : Bool) (maxDepth : Nat) (value : DumpValue) :=
  dumpBody runtime limit maxDepth "" value ++ "\n"
/-- `dump(arg; maxdepth=DUMP_DEFAULT_MAXDEPTH)`, `base/show.jl:3163-3167`. -/
def m3163 (runtime : DumpRuntime) (maxDepth : Nat) (value : DumpValue) :=
  m3130 runtime true maxDepth value
/-- `nocolor(io::IO)`, `base/show.jl:3169-3169`. -/
def m3169 (io : AlignmentIO) := noColorIO io
/-- `alignment_from_show(io::IO, x::Any)`, `base/show.jl:3170-3171`. -/
def m3170 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  alignmentFromShowBody runtime io value
/-- `alignment_from_show(io::IO, x::AbstractString)`, `base/show.jl:3172-3173`. -/
def m3172 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  alignmentFromPlainStringBody runtime io value
/-- `alignment(io::IO, x::Any)`, `base/show.jl:3191-3191`. -/
def m3191 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  (0, m3170 runtime io value)
/-- `alignment(io::IO, x::Number)`, `base/show.jl:3192-3192`. -/
def m3192 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  (m3170 runtime io value, 0)
/-- `alignment(io::IO, x::Integer)`, `base/show.jl:3193-3193`. -/
def m3193 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  (m3170 runtime io value, 0)
/-- `alignment(io::IO, x::Real)`, `base/show.jl:3194-3199`. -/
def m3194 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  Containers.alignmentReal runtime.charWidth (runtime.render (noColorIO io) value).toList
/-- `alignment(io::IO, x::Complex)`, `base/show.jl:3200-3205`. -/
def m3200 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  Containers.alignmentComplex runtime.charWidth (runtime.render (noColorIO io) value).toList
/-- `alignment(io::IO, x::Rational)`, `base/show.jl:3206-3211`. -/
def m3206 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  Containers.alignmentRational runtime.charWidth (runtime.render (noColorIO io) value).toList
/-- `alignment(io::IO, x::Pair)`, `base/show.jl:3213-3224`. -/
def m3213 (runtime : PairAlignmentRuntime) (io : PairIO) (pair : PairValue) :=
  alignmentPairBody runtime io pair
/-- `show(io::IO, ::UndefInitializer)`, `base/show.jl:3228-3228`. -/
def m3228 (_io : AlignmentIO) : Out := ["UndefInitializer()"]
/-- `summary(io::IO, x)`, `base/show.jl:3249-3249`. -/
def m3249 (runtime : SummaryRuntime) (value : SummaryValue) :=
  runtime.renderType value.typeId
/-- `summary(x)`, `base/show.jl:3250-3254`. -/
def m3250 (runtime : SummaryRuntime) (value : SummaryValue) := m3249 runtime value
/-- `dims2string(d)`, `base/show.jl:3258-3260`. -/
def m3258 (dimensions : List Nat) := dimsText dimensions
/-- `inds2string(inds)`, `base/show.jl:3262-3262`. -/
def m3262 (runtime : SummaryRuntime) (axes : List AxisModel) := axesText runtime axes
/-- `_indsstring(i)`, `base/show.jl:3263-3263`. -/
def m3263 (runtime : SummaryRuntime) (axis : AxisModel) := runtime.renderValue axis.value
/-- `_indsstring(i::Union{IdentityUnitRange, Slice})`, `base/show.jl:3264-3264`. -/
def m3264 (runtime : SummaryRuntime) (axis : AxisModel) :=
  runtime.renderValue (axis.indices.getD axis.value)
/-- `summary(io::IO, a::AbstractArray)`, `base/show.jl:3267-3267`. -/
def m3267 (runtime : SummaryRuntime) (array : SummaryValue) :=
  let axes := runtime.axes array
  arraySummaryBody runtime array axes (!(axes.all (·.oneTo)))
/-- `array_summary(io::IO, a, inds::Tuple{Vararg{OneTo}})`, `base/show.jl:3268-3271`. -/
def m3268 (runtime : SummaryRuntime) (array : SummaryValue) (axes : List AxisModel) :=
  arraySummaryBody runtime array axes false
/-- `array_summary(io::IO, a, inds)`, `base/show.jl:3272-3276`. -/
def m3272 (runtime : SummaryRuntime) (array : SummaryValue) (axes : List AxisModel) :=
  arraySummaryBody runtime array axes true
/-- `summary(io::IO, mref::GenericMemoryRef)`, `base/show.jl:3279-3284`. -/
def m3279 (runtime : SummaryRuntime) (reference : MemoryRefValue) :=
  toString (reference.memoryLength - reference.offset + 1) ++ "-element " ++
    runtime.showargMemory reference true
/-- `summary(io::IO, f::Function)`, `base/show.jl:3287-3287`. -/
def m3287 (runtime : SummaryRuntime) (function : SummaryValue) :=
  runtime.showPlainFunction function
/-- `showarg(io::IO, @nospecialize(x), toplevel)`, `base/show.jl:3335-3338`. -/
def m3335 (runtime : SummaryRuntime) (value : SummaryValue) (top : Bool) :=
  (if top then "" else "::") ++ runtime.renderType value.typeId
/-- `showarg(io::IO, T::Type, toplevel)`, `base/show.jl:3339-3342`. -/
def m3339 (runtime : SummaryRuntime) (type : TypeObject) (top : Bool) :=
  (if top then "" else "::") ++ "Type{" ++ runtime.renderType type ++ "}"
/-- `showarg(io::IO, a::Array{Union{}}, toplevel)`, `base/show.jl:3344-3347`. -/
def m3344 (runtime : SummaryRuntime) (array : SummaryValue) (top : Bool) :=
  m3335 runtime array top
/-- `showarg(io::IO, v::SubArray, toplevel)`, `base/show.jl:3350-3357`. -/
def m3350 (runtime : ContainerRuntime) (view : SubArrayValue) (top : Bool) :=
  "view(" ++ runtime.showParent view.parent false ++
    showIndicesBody runtime.summary view.indices ++ ")" ++
    (if top then " with eltype " ++ runtime.summary.renderType view.eltype else "")
/-- `showindices(io, ::Slice, inds...)`, `base/show.jl:3358-3359`. -/
def m3358 (runtime : SummaryRuntime) (rest : List AxisModel) :=
  ", :" ++ showIndicesBody runtime rest
/-- `showindices(io, ind1, inds...)`, `base/show.jl:3360-3361`. -/
def m3360 (runtime : SummaryRuntime) (first : AxisModel) (rest : List AxisModel) :=
  ", " ++ axisText runtime first ++ showIndicesBody runtime rest
/-- `showindices(io)`, `base/show.jl:3362-3362`. -/
def m3362 (_io : SummaryRuntime) := ""
/-- `showarg(io::IO, r::ReshapedArray, toplevel)`, `base/show.jl:3364-3373`. -/
def m3364 (runtime : ContainerRuntime) (array : ReshapedValue) (top : Bool) :=
  "reshape(" ++ runtime.showParent array.parent false ++
    (if array.dimensions.isEmpty then "" else ", " ++ ", ".intercalate (array.dimensions.map toString)) ++
    ")" ++ if top then " with eltype " ++ runtime.summary.renderType array.eltype else ""
/-- `showarg(io::IO, r::NonReshapedReinterpretArray{T}, toplevel) where {T}`, `base/show.jl:3375-3379`. -/
def m3375 (runtime : ContainerRuntime) (array : ReinterpretValue) :=
  "reinterpret(" ++ runtime.summary.renderType array.targetType ++ ", " ++
    runtime.showParent array.parent false ++ ")"
/-- `showarg(io::IO, r::ReshapedReinterpretArray{T}, toplevel) where {T}`, `base/show.jl:3381-3387`. -/
def m3381 (runtime : ContainerRuntime) (array : ReinterpretValue) (top : Bool) :=
  "reinterpret(reshape, " ++ runtime.summary.renderType array.targetType ++ ", " ++
    runtime.showParent array.parent false ++ ")" ++
    if top then " with eltype " ++ runtime.summary.renderType array.eltype else ""
/-- `show(io::IO, e::Iterators.Enumerate)`, `base/show.jl:3391-3395`. -/
def m3391 (runtime : ContainerRuntime) (wrapper : IteratorWrapperValue) :=
  "enumerate(" ++ runtime.showIterator wrapper.iterator ++ ")"
/-- `show(io::IO, z::Iterators.Zip)`, `base/show.jl:3396-3396`. -/
def m3396 (runtime : DelimArrayRuntime) (items : DelimArrayValue) :=
  m1562 runtime items "zip(" "," ")" false 1 items.slots.length
/-- `Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T<:AbstractArray`, `base/show.jl:3399-3401`. -/
def m3399 (runtime : SummaryRuntime) (arrayType : TypeObject) :=
  "pairs(IndexLinear(), ::" ++ runtime.renderType arrayType ++ ")"
/-- `Base.showarg(io::IO, r::Iterators.Pairs{Symbol, <:Any, Nothing, T}, toplevel) where {T <: NamedTuple}`, `base/show.jl:3403-3405`. -/
def m3403 (_values : List DelimElement) (_toplevel : Bool) := "pairs(::NamedTuple)"
/-- `Base.showarg(io::IO, r::Iterators.Pairs{<:Any, <:Any, I, D}, toplevel) where {D, I}`, `base/show.jl:3407-3409`. -/
def m3407 (runtime : SummaryRuntime) (dictType indexType : TypeObject) :=
  "Iterators.Pairs(::" ++ runtime.renderType dictType ++ ", ::" ++
    runtime.renderType indexType ++ ")"
/-- `print_bit_chunk(io::IO, c::UInt64, l::Integer = 64)`, `base/show.jl:3415-3423`. -/
def m3415 (io : BitIO) (chunk length : Nat) := printBitChunkBody io chunk length
/-- `print_bit_chunk(c::UInt64, l::Integer)`, `base/show.jl:3425-3425`. -/
def m3425 (stdout : BitIO) (chunk length : Nat) := m3415 stdout chunk length
/-- `print_bit_chunk(c::UInt64)`, `base/show.jl:3426-3426`. -/
def m3426 (stdout : BitIO) (chunk : Nat) := m3415 stdout chunk 64
/-- `bitshow(io::IO, B::BitArray)`, `base/show.jl:3428-3437`. -/
def m3428 (io : BitIO) (array : BitArrayValue) := bitshowBody io array
/-- `bitshow(B::BitArray)`, `base/show.jl:3438-3438`. -/
def m3438 (stdout : BitIO) (array : BitArrayValue) := m3428 stdout array
/-- `bitstring(B::BitArray)`, `base/show.jl:3440-3440`. -/
def m3440 (array : BitArrayValue) :=
  String.join ((bitshowBody ⟨0⟩ array).map (·.text))
/-- `show(io::IO, oc::Core.OpaqueClosure)`, `base/show.jl:3443-3448`. -/
def m3443 (runtime : OpaqueRuntime) (closure : OpaqueClosureValue) :=
  showOpaqueBody runtime closure
/-- `show(io::IO, ::MIME"text/plain", oc::Core.OpaqueClosure{A, R}) where {A, R}`, `base/show.jl:3450-3452`. -/
def m3450 (runtime : OpaqueRuntime) (closure : OpaqueClosureValue) :=
  m3443 runtime closure
/-- `print_partition(io::IO, partition::Core.BindingPartition)`, `base/show.jl:3455-3505`. -/
def m3455 (runtime : PartitionRuntime) (partition : PartitionValue) :=
  printPartitionBody runtime partition
/-- `show(io::IO, partition::Core.BindingPartition)`, `base/show.jl:3507-3511`. -/
def m3507 (runtime : PartitionRuntime) (partition : PartitionValue) :=
  "BindingPartition(for " ++ runtime.renderGlobalRef (runtime.owner partition) ++ ": " ++
    printPartitionBody runtime partition ++ ")"
/-- `show(io::IO, ::MIME"text/plain", partition::Core.BindingPartition)`, `base/show.jl:3513-3517`. -/
def m3513 (runtime : PartitionRuntime) (partition : PartitionValue) :=
  "BindingPartition for " ++ runtime.renderGlobalRef (runtime.owner partition) ++
    "\n   " ++ printPartitionBody runtime partition
/-- `show(io::IO, ::MIME"text/plain", bnd::Core.Binding)`, `base/show.jl:3519-3536`. -/
def m3519 (runtime : PartitionRuntime) (binding : BindingValue) :=
  "Binding " ++ runtime.renderGlobalRef binding.globalRef ++
    if !binding.partitionsDefined then " - No partitions"
    else String.join (bindingPartitionsBody runtime binding.fuel binding.firstPartition)
/-- `show(io::IO, ii::IncludeInto)`, `base/show.jl:3539-3546`. -/
def m3539 (runtime : IntoRuntime) (value : IntoValue) :=
  showIntoBody runtime value "include"
/-- `show(io::IO, ei::Core.EvalInto)`, `base/show.jl:3548-3555`. -/
def m3548 (runtime : IntoRuntime) (value : IntoValue) :=
  showIntoBody runtime value "eval"
end JuliaLean.ShowCov.Methods.ShowFile

namespace JuliaLean.ReduceCov.Indices

/-- `dims2string(d)` (`base/show.jl`): `"0-dimensional"`, `"n-element"`, or the sizes
joined by `×`. -/
def dims2string : List Int → String
  | [] => "0-dimensional"
  | [n] => s!"{n}-element"
  | ds => "×".intercalate (ds.map toString)

end JuliaLean.ReduceCov.Indices
