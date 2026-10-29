import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Show.EscapeProofs
import JuliaLean.Show.SymbolProofs
import JuliaLean.Show.ExprProps
import JuliaLean.Show.RangeShow
import JuliaLean.Show.EscapeRoundTrip

/-!
# Printing: `repr`/`show`/`print` and `escape_string`

Models of `base/show.jl`, `base/strings/io.jl`, `base/char.jl` and
`base/meta.jl` (master `bbfa0ce4150`), with a model of the JuliaSyntax parser
on the fragment the printed text uses (`JuliaLean/Show/Syntax.lean`). The
Unicode tables (`UData`) and the parser's operator tables (`OpData`) are
parameters; every property quantifies over them.
-/

namespace JuliaLean.Show

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "show-symbol-invalid-utf8"
    juliaFile := "base/show.jl"
    juliaFns := ["show(::IO, ::Symbol)", "Base.isidentifier(::Symbol)"]
    statement := "show(io, sym) returns normally for every Symbol, i.e. every byte string without NUL."
    source := "base/meta.jl:28-46 (isidentifier docstring, :35: a Symbol may contain any characters except \\0)"
    status := .refuted
    prop := ``SymbolReprTotal
    thm := some ``symbolReprTotal_refuted
    issue := "none found (queries: isidentifier; show Symbol invalid UTF-8; InvalidCharError Symbol; Symbol invalid UTF-8 show; isidentifier malformed; issues and PRs)"
    notes := "repr(Symbol(\"\\x80\")) throws InvalidCharError from the UInt32 conversion feeding the is_id_start_char ccall." },
  { id := "show-namedtuple-type-operator"
    juliaFile := "base/show.jl"
    juliaFns := ["Base.show_sym", "Base.show_at_namedtuple"]
    statement := "show_sym(sym) prints an identifier or a var\"...\" literal, so it can name a @NamedTuple field."
    source := "base/show.jl:1362-1376; base/namedtuple.jl:514-523 (@NamedTuple fields are name or name::type)"
    status := .refuted
    prop := ``NamedTupleFieldName
    thm := some ``namedTupleFieldName_refuted
    issue := "none found (queries: NamedTuple show operator; @NamedTuple show var; NamedTuple type printing field name; @NamedTuple operator; NamedTuple show_sym)"
    notes := "repr(typeof((; var\"+\" = 1))) == \"@NamedTuple{+::Int64}\", which does not evaluate." },
  { id := "show-sym-var-roundtrip"
    juliaFile := "base/show.jl"
    juliaFns := ["Base.show_sym"]
    statement := "show_sym(sym) prints either the name itself or var\"e\" where the parser's raw-string reading of e gives back the name's bytes."
    source := "base/show.jl:1864-1866 (escape invalid identifiers with var\"\" syntax); base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``ShowSymVarRoundTrip
    thm := some ``showSymVarRoundTrip_refuted
    issue := "related #57887, #61085"
    notes := "Symbol(\"a\\rb\") prints var\"a\\rb\" with a raw CR, which the parser reads as \"a\\nb\"; names with invalid UTF-8 or unbalanced bidi controls print var\"...\" text that is a ParseError." },
  { id := "show-sym-var-roundtrip-no-cr"
    juliaFile := "base/show.jl"
    juliaFns := ["Base.show_sym", "Base.escape_raw_string"]
    statement := "For names without a CR byte, show_sym prints the name itself or var\"e\" where unescaping e as a raw string body (escape layer only) gives back the name's bytes."
    source := "base/show.jl:1864-1878; base/strings/io.jl:618-643 (@raw_str docstring escaping rule)"
    status := .proven
    prop := ``ShowSymVarRoundTripNoCR
    thm := some ``showSymVarRoundTripNoCR_proven
    notes := "Covers the escape_raw_string / unescape_raw_string layer; tokenizer UTF-8 and bidi checks are outside this statement." },
  { id := "show-expr-unary-literal"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For every parser-produced x, print(Expr(:call, op, x)) for op in (-, +) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1: Meta.parse(string(ex)) == ex)"
    status := .refuted
    prop := ``UnaryCallReparses
    thm := some ``unaryCallReparses_refuted
    issue := "related #49494"
    notes := "-(1) prints -1 (the literal); -(-1) prints --1, a ParseError." },
  { id := "show-expr-neg-zero-base"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)", "Base.show_list"]
    statement := "For numeric literals x, y, print(Expr(:call, :^, x, y)) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``PowerBaseReparses
    thm := some ``powerBaseReparses_refuted
    issue := "none found (queries: show Expr negative zero; show_unquoted -0.0; negative zero Expr; -0.0 print expression; -0.0 ^; signbit show expression)"
    notes := "(-0.0)^2 prints -0.0 ^ 2, which is -(0.0 ^ 2) and evaluates to -0.0 instead of 0.0." },
  { id := "show-expr-typed-concat-parens"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For parser-produced T, a, b, print(Expr(:typed_hcat, T, a, b)) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``TypedConcatReparses
    thm := some ``typedConcatReparses_refuted
    issue := "related #49494"
    notes := "(a + b)[1 2] prints a + b[1 2]." },
  { id := "show-expr-transpose-literal"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For every parser-produced x, print(Expr(Symbol(\"'\"), x)) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``TransposeReparses
    thm := some ``transposeReparses_refuted
    issue := "none found (queries: show Expr transpose negative; show adjoint expression; print transpose expression; adjoint printing Expr; -1' parse)"
    notes := "(-1)' prints -1', a ParseError." },
  { id := "show-expr-decl-unary-rhs"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)", "Base.show_list"]
    statement := "For parser-produced a, b, print(Expr(:(::), a, b)) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``DeclReparses
    thm := some ``declReparses_refuted
    issue := "related #49494"
    notes := "x::(-T) prints x::-T, a ParseError." },
  { id := "show-expr-operator-call-kwargs"
    juliaFile := "base/show.jl"
    juliaFns := ["Base.show_call"]
    statement := "For op in (+, -, !) and parser-produced k, v, b, print(Expr(:call, op, Expr(:parameters, Expr(:kw, k, v)), b)) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``OperatorKwCallReparses
    thm := some ``operatorKwCallReparses_refuted
    issue := "related #19260"
    notes := "(+)(b; a = 1) prints +(b; a = 1), which parses as + applied to the block (b; a = 1)." },
  { id := "show-expr-dotted-shortcircuit"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For parser-produced a, b, print(Expr(h, a, b)) for h in (.&&, .||) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``DottedShortCircuitReparses
    thm := some ``dottedShortCircuitReparses_refuted
    issue := "related #25121"
    notes := "a .&& b prints $(Expr(:.&&, :a, :b)), the unhandled fallback." },
  { id := "show-expr-quoted-symbol"
    juliaFile := "base/show.jl"
    juliaFns := ["Base.show_unquoted_quote_expr"]
    statement := "For every symbol name, print(Expr(:call, :f, QuoteNode(Symbol(name)))) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``QuotedSymbolReparses
    thm := some ``quotedSymbolReparses_refuted
    issue := "related #57412"
    notes := "f(:var\"a b\") prints f(Symbol(\"a b\")), a call instead of a QuoteNode." },
  { id := "show-expr-cmd-backtick"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For every parser-produced command literal, its printed form lexes as a single command token."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``CmdLiteralLexes
    thm := some ``cmdLiteralLexes_refuted
    issue := "none found (queries: show cmd backtick escape; show cmd backtick; print command literal expression; Cmd literal printing backtick; @cmd show escape)"
    notes := "A command whose text is echo `x` prints `echo `x``; the first token ends after `echo `." },
  { id := "show-expr-dotted-unary"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For every parser-produced x, print(Expr(:call, op, x)) for op in (.-, .+) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``DottedUnaryReparses
    thm := some ``dottedUnaryReparses_refuted
    issue := "none found (queries: dotted unary operator printing; (.-); broadcast unary minus show; dotted operator show Expr)"
    notes := ".-x prints (.-)(x), which parses as Expr(:call, Expr(:., :-), :x)." },
  { id := "show-expr-range-quoted"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For parser-produced a and quoted b, print(Expr(:call, :(:), a, QuoteNode(b))) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``RangeQuotedReparses
    thm := some ``rangeQuotedReparses_refuted
    issue := "none found (queries: range quoted symbol print; colon operator printing)"
    notes := "a : :b prints a::b, a type assertion." },
  { id := "show-expr-prefix-syntactic-operand"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For h in (::, $, &) and parser-produced x, print(Expr(h, x)) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .refuted
    prop := ``PrefixSyntacticReparses
    thm := some ``prefixSyntacticReparses_refuted
    issue := "none found (queries: show type annotation unary; print :: expression parse; show_unquoted ::)"
    notes := "::(-1) prints ::-1, a ParseError (also ::!a, $-1, &-1)." },
  { id := "show-expr-unary-ident"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For op in (-, +, !) and every ASCII identifier name that is not an operator, print(Expr(:call, op, name)) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .proven
    prop := ``UnaryIdentReparses
    thm := some ``unaryIdentReparses_proven },
  { id := "show-expr-binary-ident"
    juliaFile := "base/show.jl"
    juliaFns := ["show_unquoted(::IO, ::Expr, ::Int, ::Int)"]
    statement := "For op in (+, -, *, /, ^) and ASCII identifier names a, b that are not operators, print(Expr(:call, op, a, b)) reparses to the same Expr."
    source := "base/show.jl:1636-1640 (Rule 1)"
    status := .proven
    prop := ``BinaryIdentReparses
    thm := some ``binaryIdentReparses_proven }
]

end JuliaLean.Show
