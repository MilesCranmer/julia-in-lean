import JuliaLean.Show.ExprPrint
import JuliaLean.Show.Syntax
import JuliaLean.Show.SymbolProofs

/-!
# Printing then parsing a Julia expression

`base/show.jl:1636-1643` states the rule the expression printer follows:

> 1. `ex == Meta.parse(string(ex))` ... printing an expression should generate
>    Julia code which could be reparsed to obtain the original expression.

`Reparses d o e` says that whenever `string(e)` (`printE`) succeeds, `Meta.parse`
(`parse`) of the text gives back `e`. The properties below quantify over the
Unicode tables `d`, the faithful operator tables `o` and over the
subexpressions; subexpressions range over the trees the parser produces
(`Parsed e`: some source text parses to `e`), so every counterexample is an
expression Julia's own parser builds. Each refutation instantiates
`UData.empty` and the confirmed table `opsFaithful`, and a `_witness` theorem
records the exact printed text and what it parses to (both checked on Julia
1.13.2 and master).
-/

namespace JuliaLean.Show

/-- `e` is produced by `Meta.parse` on some source text. -/
def Parsed (e : JE) : Prop := ∃ src, parse src = .ok e

/-- Rule 1 of `base/show.jl:1636-1643` for one expression. -/
def Reparses (d : UData) (o : OpData) (e : JE) : Prop :=
  ∀ out, printE d o e = .ok out → parse out = .ok e

/-- The command literal `` `text` `` as `Meta.parse` builds it (encoding of
`JuliaLean.Show.Syntax`). -/
def cmdNode (text : String) : JE :=
  .node "macrocall" [.node "globalref" [.sym "Core", .sym "@cmd"], .node "nothing" [], .str text]

/-! ## Properties -/

/-- `-x` and `+x` calls reparse as calls. -/
def UnaryCallReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ op ∈ ["-", "+"], ∀ x, Parsed x →
    Reparses d o (.node "call" [.sym op, x])

/-- `x ^ y` of two numeric literals reparses. -/
def PowerBaseReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ x y,
    (x matches .int _ | .flt _ _ _) → (y matches .int _ | .flt _ _ _) → Parsed x → Parsed y →
    Reparses d o (.node "call" [.sym "^", x, y])

/-- Typed horizontal concatenation `T[a b]` reparses. -/
def TypedConcatReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ T a b, Parsed T → Parsed a → Parsed b →
    Reparses d o (.node "typed_hcat" [T, a, b])

/-- The adjoint `x'` reparses. -/
def TransposeReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ x, Parsed x → Reparses d o (.node "'" [x])

/-- The type declaration `a::b` reparses. -/
def DeclReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ a b, Parsed a → Parsed b →
    Reparses d o (.node "::" [a, b])

/-- A call of an operator with a keyword argument, `op(b; k = v)`, reparses. -/
def OperatorKwCallReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ op ∈ ["+", "-", "!"], ∀ k v b,
    Parsed k → Parsed v → Parsed b →
    Reparses d o (.node "call" [.sym op, .node "parameters" [.node "kw" [k, v]], b])

/-- The dotted short-circuit operators `a .&& b`, `a .|| b` reparse. -/
def DottedShortCircuitReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ h ∈ [".&&", ".||"], ∀ a b, Parsed a → Parsed b →
    Reparses d o (.node h [a, b])

/-- `f(:name)` with a quoted symbol reparses, for every symbol name (a `Symbol`
cannot contain a NUL byte; `:var"name"` quotes any other name). -/
def QuotedSymbolReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ name : String, '\x00' ∉ name.toList →
    Reparses d o (.node "call" [.sym "f", .qn (.sym name)])

/-- A printed command literal lexes as a single command token. -/
def CmdLiteralLexes : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ text, Parsed (cmdNode text) →
    ∀ out, printE d o (cmdNode text) = .ok out → lexCmdEnd out = some out.length

/-- Calls of the dotted unary operators `.-x`, `.+x` reparse. -/
def DottedUnaryReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ op ∈ [".-", ".+"], ∀ x, Parsed x →
    Reparses d o (.node "call" [.sym op, x])

/-- A range `a:b` whose end is a quoted symbol reparses. -/
def RangeQuotedReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ a b, Parsed a → Parsed (.qn b) →
    Reparses d o (.node "call" [.sym ":", a, .qn b])

/-- The prefix forms `::x`, `$x`, `&x` reparse. -/
def PrefixSyntacticReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ h ∈ ["::", "$", "&"], ∀ x, Parsed x →
    Reparses d o (.node h [x])

/-! ## Refutations -/

/-- `-(1)`: `string` gives `-1`, the literal `-1`. -/
theorem unaryCallReparses_witness :
    printE UData.empty opsFaithful (.node "call" [.sym "-", .int 1]) = .ok (u8 "-1") ∧
    parse (u8 "-1") = .ok (.int (-1)) ∧
    printE UData.empty opsFaithful (.node "call" [.sym "-", .int (-1)]) = .ok (u8 "--1") ∧
    parse (u8 "--1") = .error := by
  decide +kernel

theorem unaryCallReparses_refuted : ¬ UnaryCallReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful "-" (by decide +kernel) (.int 1)
    ⟨u8 "1", by decide +kernel⟩ (u8 "-1") (by decide +kernel)
  revert this; decide +kernel

/-- `(-0.0)^2`: `string` gives `-0.0 ^ 2`, which is `-(0.0 ^ 2)`. -/
theorem powerBaseReparses_witness :
    printE UData.empty opsFaithful (.node "call" [.sym "^", .flt true 0 [0], .int 2]) =
      .ok (u8 "-0.0 ^ 2") ∧
    parse (u8 "-0.0 ^ 2") = .ok (.node "call" [.sym "-", .node "call" [.sym "^", .flt false 0 [0], .int 2]]) := by
  decide +kernel

theorem powerBaseReparses_refuted : ¬ PowerBaseReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful (.flt true 0 [0]) (.int 2) rfl rfl
    ⟨u8 "-0.0", by decide +kernel⟩ ⟨u8 "2", by decide +kernel⟩ (u8 "-0.0 ^ 2") (by decide +kernel)
  revert this; decide +kernel

/-- `(a + b)[a b]`: `string` gives `a + b[a b]`, which is `a + (b[a b])`. -/
theorem typedConcatReparses_witness :
    printE UData.empty opsFaithful
        (.node "typed_hcat" [.node "call" [.sym "+", .sym "a", .sym "b"], .sym "a", .sym "b"]) =
      .ok (u8 "a + b[a b]") ∧
    parse (u8 "a + b[a b]") =
      .ok (.node "call" [.sym "+", .sym "a", .node "typed_hcat" [.sym "b", .sym "a", .sym "b"]]) := by
  decide +kernel

theorem typedConcatReparses_refuted : ¬ TypedConcatReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful (.node "call" [.sym "+", .sym "a", .sym "b"])
    (.sym "a") (.sym "b") ⟨u8 "a + b", by decide +kernel⟩ ⟨u8 "a", by decide +kernel⟩ ⟨u8 "b", by decide +kernel⟩
    (u8 "a + b[a b]") (by decide +kernel)
  revert this; decide +kernel

/-- `(-1)'`: `string` gives `-1'`, a `ParseError`. -/
theorem transposeReparses_witness :
    printE UData.empty opsFaithful (.node "'" [.int (-1)]) = .ok (u8 "-1'") ∧
    parse (u8 "-1'") = .error := by
  decide +kernel

theorem transposeReparses_refuted : ¬ TransposeReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful (.int (-1)) ⟨u8 "-1", by decide +kernel⟩
    (u8 "-1'") (by decide +kernel)
  revert this; decide +kernel

/-- `a::(-T)`: `string` gives `a::-T`, a `ParseError`. -/
theorem declReparses_witness :
    printE UData.empty opsFaithful (.node "::" [.sym "a", .node "call" [.sym "-", .sym "T"]]) =
      .ok (u8 "a::-T") ∧
    parse (u8 "a::-T") = .error := by
  decide +kernel

theorem declReparses_refuted : ¬ DeclReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful (.sym "a") (.node "call" [.sym "-", .sym "T"])
    ⟨u8 "a", by decide +kernel⟩ ⟨u8 "-T", by decide +kernel⟩ (u8 "a::-T") (by decide +kernel)
  revert this; decide +kernel

/-- `(+)(b; a = b)`: `string` gives `+(b; a = b)`, which is `+` applied to the
block `(b; a = b)`. -/
theorem operatorKwCallReparses_witness :
    printE UData.empty opsFaithful
        (.node "call" [.sym "+", .node "parameters" [.node "kw" [.sym "a", .sym "b"]], .sym "b"]) =
      .ok (u8 "+(b; a = b)") ∧
    parse (u8 "+(b; a = b)") =
      .ok (.node "call" [.sym "+", .node "block" [.sym "b", .node "=" [.sym "a", .sym "b"]]]) := by
  decide +kernel

theorem operatorKwCallReparses_refuted : ¬ OperatorKwCallReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful "+" (by decide +kernel) (.sym "a") (.sym "b")
    (.sym "b") ⟨u8 "a", by decide +kernel⟩ ⟨u8 "b", by decide +kernel⟩ ⟨u8 "b", by decide +kernel⟩
    (u8 "+(b; a = b)") (by decide +kernel)
  revert this; decide +kernel

/-- `a .&& b`: `string` gives `$(Expr(:.&&, :a, :b))`, an interpolation. -/
theorem dottedShortCircuitReparses_witness :
    printE UData.empty opsFaithful (.node ".&&" [.sym "a", .sym "b"]) =
      .ok (u8 "$(Expr(:.&&, :a, :b))") ∧
    parse (u8 "$(Expr(:.&&, :a, :b))") =
      .ok (.node "$" [.node "call" [.sym "Expr", .qn (.sym ".&&"), .qn (.sym "a"), .qn (.sym "b")]]) := by
  decide +kernel

theorem dottedShortCircuitReparses_refuted : ¬ DottedShortCircuitReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful ".&&" (by decide +kernel) (.sym "a") (.sym "b")
    ⟨u8 "a", by decide +kernel⟩ ⟨u8 "b", by decide +kernel⟩ (u8 "$(Expr(:.&&, :a, :b))") (by decide +kernel)
  revert this; decide +kernel

/-- `f(:var"a b")`: `string` gives `f(Symbol("a b"))`, a call of `Symbol`. -/
theorem quotedSymbolReparses_witness :
    printE UData.empty opsFaithful (.node "call" [.sym "f", .qn (.sym "a b")]) =
      .ok (u8 "f(Symbol(\"a b\"))") ∧
    parse (u8 "f(Symbol(\"a b\"))") =
      .ok (.node "call" [.sym "f", .node "call" [.sym "Symbol", .str "a b"]]) := by
  decide +kernel

theorem quotedSymbolReparses_refuted : ¬ QuotedSymbolReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful "a b" (by decide +kernel)
    (u8 "f(Symbol(\"a b\"))") (by decide +kernel)
  revert this; decide +kernel

/-- `` `echo \`x\`` ``: `string` gives `` `echo `x`` ``, whose command token ends
after `` `echo ` ``. -/
theorem cmdLiteralLexes_witness :
    printE UData.empty opsFaithful (cmdNode "echo `x`") = .ok (u8 "`echo `x``") ∧
    lexCmdEnd (u8 "`echo `x``") = some 7 := by
  decide +kernel

theorem cmdLiteralLexes_refuted : ¬ CmdLiteralLexes := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful "echo `x`" ⟨u8 "`echo \\`x\\``", by decide +kernel⟩
    (u8 "`echo `x``") (by decide +kernel)
  revert this; decide +kernel

/-- `.-x`: `string` gives `(.-)(x)`, a call of the expression `(.-)`. -/
theorem dottedUnaryReparses_witness :
    printE UData.empty opsFaithful (.node "call" [.sym ".-", .sym "x"]) = .ok (u8 "(.-)(x)") ∧
    parse (u8 "(.-)(x)") = .ok (.node "call" [.node "." [.sym "-"], .sym "x"]) := by
  decide +kernel

theorem dottedUnaryReparses_refuted : ¬ DottedUnaryReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful ".-" (by decide +kernel) (.sym "x")
    ⟨u8 "x", by decide +kernel⟩ (u8 "(.-)(x)") (by decide +kernel)
  revert this; decide +kernel

/-- `a:(:b)`: `string` gives `a::b`, a type declaration. -/
theorem rangeQuotedReparses_witness :
    printE UData.empty opsFaithful (.node "call" [.sym ":", .sym "a", .qn (.sym "b")]) =
      .ok (u8 "a::b") ∧
    parse (u8 "a::b") = .ok (.node "::" [.sym "a", .sym "b"]) := by
  decide +kernel

theorem rangeQuotedReparses_refuted : ¬ RangeQuotedReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful (.sym "a") (.sym "b")
    ⟨u8 "a", by decide +kernel⟩ ⟨u8 ":b", by decide +kernel⟩ (u8 "a::b") (by decide +kernel)
  revert this; decide +kernel

/-- `::(-1)`: `string` gives `::-1`, a `ParseError`. -/
theorem prefixSyntacticReparses_witness :
    printE UData.empty opsFaithful (.node "::" [.int (-1)]) = .ok (u8 "::-1") ∧
    parse (u8 "::-1") = .error := by
  decide +kernel

theorem prefixSyntacticReparses_refuted : ¬ PrefixSyntacticReparses := by
  intro h
  have := h UData.empty opsFaithful opsFaithful_faithful "::" (by decide +kernel) (.int (-1))
    ⟨u8 "-1", by decide +kernel⟩ (u8 "::-1") (by decide +kernel)
  revert this; decide +kernel

/-! ## Proven: operators applied to identifiers

The printer side unfolds `printE` (`printUnary`, `printBinary`) given the
symbol printer's results; `showSymS_op` prints the operator names under
`o.Faithful`, and `showSymS_ident` prints an ASCII identifier as itself
(`showSym_ascii_ident`). The parser side is `Syntax.parse_unary_ident` and
`Syntax.parse_binary_ident`. -/

theorem jstrOf_ok (s : String) (h : (u8 s).length < 2 ^ 62) : jstrOf s = .ok ⟨u8 s, h⟩ := dite_eq_left h

theorem showSymS_eq (d : UData) (o : OpData) (s : String) (h : (u8 s).length < 2 ^ 62) :
    showSymS d o s = liftS (showSym d o ⟨u8 s, h⟩) := by
  simp only [showSymS, jstrOf_ok s h, bind, Except.bind]

theorem showSymS_long (d : UData) (o : OpData) (s : String) (h : ¬ (u8 s).length < 2 ^ 62) :
    showSymS d o s = .error .unknown := by
  have hj : jstrOf s = .error .unknown := dite_eq_right_iff.mpr (fun h' => absurd h' h)
  simp only [showSymS, hj, bind, Except.bind]

theorem faithful_op (o : OpData) (hf : o.Faithful) :
    ∀ s ∈ ["+", "-", "!", "*", "/", "^"], o.isOp s = true ∧ o.isSyntacticOp s = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hIsOp, _, _, _, _, hSynF, _⟩ := hf
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨hIsOp _ (by simp), hSynF _ (by simp)⟩

theorem faithful_prec (o : OpData) (hf : o.Faithful) :
    ∀ s ∈ ["+", "-", "*", "/", "^"], 0 < o.prec s := by
  obtain ⟨p1, p2, p3, p4, p5, _⟩ := hf
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> omega

theorem showSymS_opname (d : UData) (o : OpData) (s : String) (hlen : (u8 s).length < 2 ^ 62)
    (e1 : isidentifier d ⟨u8 s, hlen⟩ = .ok false) (h1 : isOperatorSym o ⟨u8 s, hlen⟩ = true)
    (h2 : isSyntacticSym o ⟨u8 s, hlen⟩ = false)
    (h3 : decide (u8 s ∈ [asc ['\''], asc [':', ':'], asc ['?']]) = false) :
    showSymS d o s = .ok (u8 s) := by
  rw [showSymS_eq _ _ _ hlen]
  simp only [showSym, isValidIdentifier, e1, h1, h2]
  simp only [h3]
  rfl

set_option maxRecDepth 100000 in
theorem isidentifier_plus (d : UData) : isidentifier d ⟨u8 "+", by decide⟩ = .ok false := rfl
set_option maxRecDepth 100000 in
theorem isOperatorSym_plus (o : OpData) : isOperatorSym o ⟨u8 "+", by decide⟩ = o.isOp "+" := rfl
set_option maxRecDepth 100000 in
theorem isSyntacticSym_plus (o : OpData) : isSyntacticSym o ⟨u8 "+", by decide⟩ = o.isSyntacticOp "+" := rfl

set_option maxRecDepth 100000 in
theorem isidentifier_minus (d : UData) : isidentifier d ⟨u8 "-", by decide⟩ = .ok false := rfl
set_option maxRecDepth 100000 in
theorem isOperatorSym_minus (o : OpData) : isOperatorSym o ⟨u8 "-", by decide⟩ = o.isOp "-" := rfl
set_option maxRecDepth 100000 in
theorem isSyntacticSym_minus (o : OpData) : isSyntacticSym o ⟨u8 "-", by decide⟩ = o.isSyntacticOp "-" := rfl

set_option maxRecDepth 100000 in
theorem isidentifier_bang (d : UData) : isidentifier d ⟨u8 "!", by decide⟩ = .ok false := rfl
set_option maxRecDepth 100000 in
theorem isOperatorSym_bang (o : OpData) : isOperatorSym o ⟨u8 "!", by decide⟩ = o.isOp "!" := rfl
set_option maxRecDepth 100000 in
theorem isSyntacticSym_bang (o : OpData) : isSyntacticSym o ⟨u8 "!", by decide⟩ = o.isSyntacticOp "!" := rfl

set_option maxRecDepth 100000 in
theorem isidentifier_star (d : UData) : isidentifier d ⟨u8 "*", by decide⟩ = .ok false := rfl
set_option maxRecDepth 100000 in
theorem isOperatorSym_star (o : OpData) : isOperatorSym o ⟨u8 "*", by decide⟩ = o.isOp "*" := rfl
set_option maxRecDepth 100000 in
theorem isSyntacticSym_star (o : OpData) : isSyntacticSym o ⟨u8 "*", by decide⟩ = o.isSyntacticOp "*" := rfl

set_option maxRecDepth 100000 in
theorem isidentifier_slash (d : UData) : isidentifier d ⟨u8 "/", by decide⟩ = .ok false := rfl
set_option maxRecDepth 100000 in
theorem isOperatorSym_slash (o : OpData) : isOperatorSym o ⟨u8 "/", by decide⟩ = o.isOp "/" := rfl
set_option maxRecDepth 100000 in
theorem isSyntacticSym_slash (o : OpData) : isSyntacticSym o ⟨u8 "/", by decide⟩ = o.isSyntacticOp "/" := rfl

set_option maxRecDepth 100000 in
theorem isidentifier_caret (d : UData) : isidentifier d ⟨u8 "^", by decide⟩ = .ok false := rfl
set_option maxRecDepth 100000 in
theorem isOperatorSym_caret (o : OpData) : isOperatorSym o ⟨u8 "^", by decide⟩ = o.isOp "^" := rfl
set_option maxRecDepth 100000 in
theorem isSyntacticSym_caret (o : OpData) : isSyntacticSym o ⟨u8 "^", by decide⟩ = o.isSyntacticOp "^" := rfl

theorem showSymS_op (d : UData) (o : OpData) (hf : o.Faithful) :
    ∀ op ∈ ["+", "-", "!", "*", "/", "^"], showSymS d o op = .ok (u8 op) := by
  intro op hop
  obtain ⟨h1, h2⟩ := faithful_op o hf op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  · exact showSymS_opname d o "+" (by decide) (isidentifier_plus d) ((isOperatorSym_plus o).trans h1)
      ((isSyntacticSym_plus o).trans h2) (by decide +kernel)
  · exact showSymS_opname d o "-" (by decide) (isidentifier_minus d) ((isOperatorSym_minus o).trans h1)
      ((isSyntacticSym_minus o).trans h2) (by decide +kernel)
  · exact showSymS_opname d o "!" (by decide) (isidentifier_bang d) ((isOperatorSym_bang o).trans h1)
      ((isSyntacticSym_bang o).trans h2) (by decide +kernel)
  · exact showSymS_opname d o "*" (by decide) (isidentifier_star d) ((isOperatorSym_star o).trans h1)
      ((isSyntacticSym_star o).trans h2) (by decide +kernel)
  · exact showSymS_opname d o "/" (by decide) (isidentifier_slash d) ((isOperatorSym_slash o).trans h1)
      ((isSyntacticSym_slash o).trans h2) (by decide +kernel)
  · exact showSymS_opname d o "^" (by decide) (isidentifier_caret d) ((isOperatorSym_caret o).trans h1)
      ((isSyntacticSym_caret o).trans h2) (by decide +kernel)

theorem flatMap_ascii : ∀ l : List Char, l.all (fun c => decide (c.toNat < 128)) = true →
    l.flatMap utf8Encode = l.map (fun c => c.toNat.toUInt8)
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have hc : c.val.toNat < 0x80 := h.1
    simp only [List.flatMap_cons, List.map_cons, flatMap_ascii cs h.2]
    simp only [utf8Encode, hc, ite_true]
    rfl

theorem u8_ascii (s : String) (h : s.toList.all (fun c => decide (c.toNat < 128)) = true) :
    u8 s = Syntax.asciiBytes s := flatMap_ascii _ h

theorem u8_append (s t : String) : u8 (s ++ t) = u8 s ++ u8 t := by
  simp [u8, String.toList_append, List.flatMap_append]

theorem isoperator_ident (o : OpData) (n : String) (hn : Syntax.IdentName n) (ho : o.isOp n = false) :
    isoperator o n = false := by
  obtain ⟨_, hid⟩ := hn
  unfold isoperator ispostfixoperator
  rw [ho, Bool.false_or]
  unfold Syntax.asciiBytes at hid
  split
  · next rest h =>
    rw [h] at hid
    simp [Syntax.identOk, Syntax.isIdStartB, Syntax.isLetterB] at hid
  · rfl

theorem keyword_reserved :
    ∀ k ∈ keywordSyms, Syntax.reservedNames.contains (Syntax.asciiStr k) = true := by
  decide +kernel

theorem showSymS_ident (d : UData) (o : OpData) (n : String)
    (hn : Syntax.IdentName n) (hlen : (u8 n).length < 2 ^ 62) : showSymS d o n = .ok (u8 n) := by
  obtain ⟨hasc, hid⟩ := hn
  have hu : u8 n = Syntax.asciiBytes n := u8_ascii n hasc
  rw [showSymS_eq _ _ _ hlen]
  have hk : u8 n ∉ keywordSyms := by
    intro hm
    have h1 := keyword_reserved _ hm
    rw [hu, Syntax.asciiStr_asciiBytes n hasc] at h1
    rw [← Syntax.asciiStr_asciiBytes n hasc] at h1
    cases hb : Syntax.asciiBytes n with
    | nil => rw [hb] at hid; simp [Syntax.identOk] at hid
    | cons b bs =>
      rw [hb] at hid h1
      simp only [Syntax.identOk, Bool.and_eq_true, Bool.not_eq_true'] at hid
      rw [hid.2] at h1
      cases h1
  cases hb : Syntax.asciiBytes n with
  | nil => rw [hb] at hid; simp [Syntax.identOk] at hid
  | cons b bs =>
    rw [hb] at hid
    simp only [Syntax.identOk, Bool.and_eq_true] at hid
    obtain ⟨⟨hs, hr⟩, -⟩ := hid
    have e := showSym_ascii_ident d o ⟨u8 n, hlen⟩ b bs (by show u8 n = b :: bs; rw [hu, hb])
      (by
        simp only [Syntax.isIdStartB, Syntax.isLetterB, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq, ge_iff_le] at hs
        rcases hs with (h | h) | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h))
      (by
        intro x hx
        have h := List.all_eq_true.mp hr x hx
        simp only [Syntax.isIdCharB, Syntax.isIdStartB, Syntax.isLetterB, Syntax.isDigitB, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le] at h
        rcases h with (((h | h) | h) | h) | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inr h))))
      hk
    rw [e]; rfl

theorem printUnary (d : UData) (o : OpData) (op name : String) (r : Except PErr (List UInt8))
    (hsop : showSymS d o op = .ok (u8 op)) (hop : op ∈ ["-", "+", "!"])
    (hs : showSymS d o name = r) (hiso : isoperator o name = false) :
    printE d o (.node "call" [.sym op, .sym name]) = (do let x ← r; pure (u8 op ++ x)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> cases r <;>
  simp [printE, JE.size, JE.sizeList, showUnquoted, showExpr, isExpr, hsop, hs, hiso, exprInfixAny, exprInfix,
    exprInfixWide, exprParens, ispostfixoperator, uniOps] <;> rfl

theorem printBinary (d : UData) (o : OpData) (op a b : String) (ra rb : Except PErr (List UInt8))
    (hsop : showSymS d o op = .ok (u8 op)) (hop : op ∈ ["+", "-", "*", "/", "^"]) (hp : 0 < o.prec op)
    (ha : showSymS d o a = ra) (hisa : isoperator o a = false)
    (hb : showSymS d o b = rb) (hisb : isoperator o b = false) :
    printE d o (.node "call" [.sym op, .sym a, .sym b]) =
      (do let x ← ra; let y ← rb; pure (x ++ (u8 " " ++ (u8 op ++ (u8 " " ++ y))))) := by
  have hp' : ¬ ((o.prec op : Int) ≤ -1) := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> cases ra <;> cases rb <;>
  simp [printE, JE.size, JE.sizeList, showUnquoted, showExpr, showBinaryOrCall, showList, isExpr, ha, hb, hisa,
    hisb, exprInfixAny, exprInfix, exprInfixWide, exprParens, ispostfixoperator, uniOps, isQuoted, isNegReal, hp,
    hp'] <;> rfl

/-- Unary `-`, `+`, `!` applied to an identifier reparses. -/
def UnaryIdentReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ op ∈ ["-", "+", "!"], ∀ name, Syntax.IdentName name →
    o.isOp name = false → Reparses d o (.node "call" [.sym op, .sym name])

/-- Binary `+ - * / ^` of two identifiers reparses. -/
def BinaryIdentReparses : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ op ∈ ["+", "-", "*", "/", "^"], ∀ a b,
    Syntax.IdentName a → Syntax.IdentName b → o.isOp a = false → o.isOp b = false →
    Reparses d o (.node "call" [.sym op, .sym a, .sym b])

theorem ascii_append_op (op n : String) (hop : op ∈ ["+", "-", "!", "*", "/", "^"])
    (hn : n.toList.all (fun c => decide (c.toNat < 128)) = true) :
    (op ++ n).toList.all (fun c => decide (c.toNat < 128)) = true := by
  simp only [String.toList_append, List.all_append, hn, Bool.and_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem unaryIdentReparses_proven : UnaryIdentReparses := by
  intro d o hf op hop name hn ho out hout
  have hop6 : op ∈ ["+", "-", "!", "*", "/", "^"] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with h | h | h <;> simp [h]
  rw [printUnary d o op name _ (showSymS_op d o hf op hop6) hop rfl (isoperator_ident o name hn ho)] at hout
  by_cases hlen : (u8 name).length < 2 ^ 62
  · rw [showSymS_ident d o name hn hlen] at hout
    injection hout with hout
    subst hout
    rw [← u8_append, u8_ascii _ (ascii_append_op op name hop6 hn.1)]
    exact Syntax.parse_unary_ident op hop name hn
  · rw [showSymS_long d o name hlen] at hout
    cases hout

theorem binaryIdentReparses_proven : BinaryIdentReparses := by
  intro d o hf op hop a b ha hb hoa hob out hout
  have hop6 : op ∈ ["+", "-", "!", "*", "/", "^"] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with h | h | h | h | h <;> simp [h]
  rw [printBinary d o op a b _ _ (showSymS_op d o hf op hop6) hop (faithful_prec o hf op hop) rfl
    (isoperator_ident o a ha hoa) rfl (isoperator_ident o b hb hob)] at hout
  by_cases hla : (u8 a).length < 2 ^ 62
  · by_cases hlb : (u8 b).length < 2 ^ 62
    · rw [showSymS_ident d o a ha hla, showSymS_ident d o b hb hlb] at hout
      injection hout with hout
      subst hout
      have hasc : (a ++ " " ++ op ++ " " ++ b).toList.all (fun c => decide (c.toNat < 128)) = true := by
        simp only [String.toList_append, List.all_append, ha.1, hb.1, Bool.and_true, Bool.true_and]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [show u8 a ++ (u8 " " ++ (u8 op ++ (u8 " " ++ u8 b))) = u8 (a ++ " " ++ op ++ " " ++ b) by
        simp only [u8_append, List.append_assoc], u8_ascii _ hasc]
      exact Syntax.parse_binary_ident op hop a b ha hb
    · rw [showSymS_ident d o a ha hla, showSymS_long d o b hlb] at hout
      cases hout
  · rw [showSymS_long d o a hla] at hout
    cases hout


end JuliaLean.Show
