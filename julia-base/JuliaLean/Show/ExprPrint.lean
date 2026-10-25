import JuliaLean.Show.Ast
import JuliaLean.Show.Ops
import JuliaLean.Show.Unicode
import JuliaLean.Show.Symbol
import JuliaLean.Show.Escape

/-!
# Printing Julia expressions: `print(io, ex::Expr)`

`printE d o e` models `string(e)` = `print(io, e)` (`base/show.jl:1666`), which
calls `show_unquoted(IOContext(io, :unquote_fallback => false), e, 0, -1)`, on
the `JE` trees of `JuliaLean.Show.Ast`.

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
def showSymS (d : UData) (o : OpData) (s : String) : PO := do
  liftS (showSym d o (← jstrOf s))

/-- `show(io, s::String)` = `print_quoted(io, s)`, `base/strings/io.jl:194`. -/
def showStrS (d : UData) (s : String) : PO := do
  pure (printQuoted d (← jstrOf s))

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
    | .sym s => showSymS d o s
    | .int v => .ok (showInt v)
    | .flt ng ip fp => .ok (showFlt ng ip fp)
    | .str s => showStrS d s
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
    | .str s => showStrS d s
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
        else pure (u8 "Symbol(" ++ (← showStrS d s) ++ u8 ")")
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
def printE (d : UData) (o : OpData) (e : JE) : PO :=
  match e with
  | .sym s => .ok (u8 s)
  | .int v => .ok (showInt v)
  | .flt ng ip fp => .ok (showFlt ng ip fp)
  | .str s => .ok (u8 s)
  | _ => showUnquoted d o (16 * e.size + 16) false false e 0 (-1) 0

end JuliaLean.Show
