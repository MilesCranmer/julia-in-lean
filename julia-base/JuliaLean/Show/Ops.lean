/-!
# Operator tables consulted by the printers

`Base.isoperator`, `Base.operator_precedence` and friends call into the
parser's operator tables (`src/ast.c:862-905`, which consult the flisp tables
in `src/julia-parser.scm`). The tables are large; the model takes them as a
parameter `OpData`, and `OpData.Faithful` records the entries the modelled
properties rely on. Every fact in `Faithful` was printed by Julia 1.13.2 and
master:

```
prec + 11   prec - 11   prec * 12   prec / 12   prec ^ 15   prec :: 16
prec = 1    prec // 13  prec : 10   prec => 2   prec == 7   prec < 7
prec && 6   prec || 5   prec . 17   prec .&& 6  prec .|| 5  prec ' 0
prec ! 0    prec <: 7   prec .+ 11  prec √ 0    prec ~ 1
_isoperator: true for + - * / ^ :: = ' ! ~ && || .&& . .. ... ? $ -> --> <: >:
  % & | \ << >> >>> == != < > <= >= === !== => |> <| : += .+ .= √ ∈;
  false for x, end, "a b"
isunaryoperator: true for + - ! ~ <: >: .+ √; false for the other symbols above
is_syntactic_operator: true for = && || .&& . ... -> += .=; false for the others
```

On 1.13.2 and master, the observed output for each of
`a b f k T y Symbol Core @cmd`: `_isoperator` false, `isunaryoperator` false,
`is_syntactic_operator` false, `operator_precedence` 0; and for `.-`:
`_isoperator` true, `isunaryoperator` true, `is_syntactic_operator` false,
`operator_precedence` 11.
-/

namespace JuliaLean.Show

/-- The parser's operator tables, keyed by symbol name. -/
structure OpData where
  /-- `Base.Meta._isoperator(s)` = `jl_is_operator`, `base/meta.jl:60`. -/
  isOp : String → Bool
  /-- `Base.Meta.isunaryoperator(s)` = `jl_is_unary_operator`, `base/meta.jl:86`. -/
  isUnaryOp : String → Bool
  /-- `Base.Meta.is_unary_and_binary_operator(s)`, `base/meta.jl:87`. -/
  isUnaryAndBinaryOp : String → Bool
  /-- `Base.Meta.is_syntactic_operator(s)`, `base/meta.jl:88`. -/
  isSyntacticOp : String → Bool
  /-- `Base.operator_precedence(s)` = `jl_operator_precedence`, `base/show.jl:1713`. -/
  prec : String → Nat
  /-- `Base.Meta.is_op_suffix_char(c)` on code points, `base/meta.jl:58`. -/
  opSuffix : UInt32 → Bool

/-- The table entries confirmed on Julia 1.13.2 and master (module docstring). -/
def OpData.Faithful (o : OpData) : Prop :=
  o.prec "+" = 11 ∧ o.prec "-" = 11 ∧ o.prec "*" = 12 ∧ o.prec "/" = 12 ∧
  o.prec "^" = 15 ∧ o.prec "::" = 16 ∧ o.prec "=" = 1 ∧ o.prec "//" = 13 ∧
  o.prec ":" = 10 ∧ o.prec "=>" = 2 ∧ o.prec "==" = 7 ∧ o.prec "<" = 7 ∧
  o.prec "&&" = 6 ∧ o.prec "||" = 5 ∧ o.prec "." = 17 ∧ o.prec ".&&" = 6 ∧
  o.prec ".||" = 5 ∧ o.prec "'" = 0 ∧ o.prec "!" = 0 ∧ o.prec "<:" = 7 ∧
  o.prec ".+" = 11 ∧ o.prec "√" = 0 ∧ o.prec "~" = 1 ∧
  (∀ s ∈ ["+", "-", "*", "/", "^", "::", "=", "'", "!", "~", "&&", "||", ".&&", ".", "..",
      "...", "?", "$", "->", "-->", "<:", ">:", "%", "&", "|", "\\", "<<", ">>", ">>>", "==",
      "!=", "<", ">", "<=", ">=", "===", "!==", "=>", "|>", "<|", ":", "+=", ".+", ".=", "√", "∈"],
    o.isOp s = true) ∧
  (∀ s ∈ ["x", "end", "a b"], o.isOp s = false) ∧
  (∀ s ∈ ["+", "-", "!", "~", "<:", ">:", ".+", "√"], o.isUnaryOp s = true) ∧
  (∀ s ∈ ["*", "/", "^", "::", "=", "'", "&&", "||", ".&&", ".", "..", "...", "?", "$", "->",
      "-->", "%", "&", "|", "\\", "<<", ">>", ">>>", "==", "!=", "<", ">", "<=", ">=", "===",
      "!==", "=>", "|>", "<|", ":", "+=", ".=", "∈", "x", "end", "a b"],
    o.isUnaryOp s = false) ∧
  (∀ s ∈ ["=", "&&", "||", ".&&", ".", "...", "->", "+=", ".="], o.isSyntacticOp s = true) ∧
  (∀ s ∈ ["+", "-", "*", "/", "^", "::", "'", "!", "~", "..", "?", "$", "-->", "<:", ">:",
      "%", "&", "|", "\\", "<<", ">>", ">>>", "==", "!=", "<", ">", "<=", ">=", "===", "!==",
      "=>", "|>", "<|", ":", ".+", "√", "∈", "x", "end", "a b"],
    o.isSyntacticOp s = false) ∧
  (∀ s ∈ ["a", "b", "f", "k", "T", "y", "Symbol", "Core", "@cmd"],
    o.isOp s = false ∧ o.isUnaryOp s = false ∧ o.isSyntacticOp s = false ∧ o.prec s = 0) ∧
  o.isOp ".-" = true ∧ o.isUnaryOp ".-" = true ∧ o.isSyntacticOp ".-" = false ∧ o.prec ".-" = 11

end JuliaLean.Show
