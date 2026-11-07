import JuliaLean.base.meta
import JuliaLean.Proofs.base.meta.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

def MetaRow25Property : Prop := ∀ table character, metaRow25 table character = table character

theorem metaRow25_proven : MetaRow25Property := by unfold MetaRow25Property; intros; rfl

/-- Runtime Unicode identifier-continuation query; `base/meta.jl:26`. -/

def MetaRow26Property : Prop := ∀ table character, metaRow26 table character = table character

theorem metaRow26_proven : MetaRow26Property := by unfold MetaRow26Property; intros; rfl

/-- `isidentifier(::AbstractString)`; `base/meta.jl:48-55`. -/

def MetaRow48Property : Prop :=
  (∀ start rest, metaRow48 start rest [] = false) ∧
  (∀ start rest first tail, metaRow48 start rest (first :: tail) =
    (String.ofList (first :: tail) != "true" && String.ofList (first :: tail) != "false" &&
      start first && tail.all rest))

theorem metaRow48_proven : MetaRow48Property := by exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- `isidentifier(::Symbol)`; `base/meta.jl:56`. -/

def MetaRow56Property : Prop := ∀ symbol start rest,
  metaRow56 symbol start rest = metaRow48 start rest symbol.toList

theorem metaRow56_proven : MetaRow56Property := by unfold MetaRow56Property; intros; rfl

/-- Runtime operator-suffix query; `base/meta.jl:58`. -/

def MetaRow58Property : Prop := ∀ table character, metaRow58 table character = table character

theorem metaRow58_proven : MetaRow58Property := by unfold MetaRow58Property; intros; rfl

/-- Runtime operator query; `base/meta.jl:60`. -/

def MetaRow60Property : Prop := ∀ table symbol, metaRow60 table symbol = table symbol

theorem metaRow60_proven : MetaRow60Property := by unfold MetaRow60Property; intros; rfl

/-- `ispostfixoperator`; used by `isoperator`; `base/meta.jl:117-120`. -/

def MetaRow73Property : Prop := ∀ operators suffixes symbol,
  metaRow73 operators suffixes symbol = (operators symbol || metaPostfix suffixes symbol)

theorem metaRow73_proven : MetaRow73Property := by unfold MetaRow73Property; intros; rfl

/-- Runtime unary-operator query; `base/meta.jl:86`. -/

def MetaRow86Property : Prop := ∀ table symbol, metaRow86 table symbol = table symbol

theorem metaRow86_proven : MetaRow86Property := by unfold MetaRow86Property; intros; rfl

/-- Runtime unary-and-binary query; `base/meta.jl:87`. -/

def MetaRow87Property : Prop := ∀ table symbol, metaRow87 table symbol = table symbol

theorem metaRow87_proven : MetaRow87Property := by unfold MetaRow87Property; intros; rfl

/-- Runtime syntactic-operator query; `base/meta.jl:88`. -/

def MetaRow88Property : Prop := ∀ table symbol, metaRow88 table symbol = table symbol

theorem metaRow88_proven : MetaRow88Property := by unfold MetaRow88Property; intros; rfl

/-- `isbinaryoperator`; `base/meta.jl:101-104`. -/

def MetaRow101Property : Prop := ∀ op unary both symbol,
  metaRow101 op unary both symbol = (op symbol && (!unary symbol || both symbol) && symbol != "'")

theorem metaRow101_proven : MetaRow101Property := by unfold MetaRow101Property; intros; rfl

/-- `ispostfixoperator`; `base/meta.jl:117-120`. -/

def MetaRow117Property : Prop := ∀ suffix symbol,
  metaRow117 suffix symbol = match symbol.toList with | '\'' :: tail => tail.all suffix | _ => false

theorem metaRow117_proven : MetaRow117Property := by
  unfold MetaRow117Property
  intros
  rfl

/-- `is_valid_identifier`; `base/meta.jl:128-134`. -/

def MetaRow128Property : Prop := ∀ start rest operator syntactic keywords excluded symbol,
  metaRow128 start rest operator syntactic keywords excluded symbol =
    ((metaRow48 start rest symbol.toList && !keywords.contains symbol) ||
      (operator symbol && !excluded.contains symbol && !syntactic symbol))

theorem metaRow128_proven : MetaRow128Property := by unfold MetaRow128Property; intros; rfl

/-- `quot`; `base/meta.jl:158`. -/

def MetaRow158Property : Prop := ∀ expression, metaRow158 expression = .expr "quote" [expression]

theorem metaRow158_proven : MetaRow158Property := by unfold MetaRow158Property; intro; rfl

/-- `replace_sourceloc!`; `base/meta.jl:209-217`. -/

def MetaRow209Property : Prop := ∀ location expression,
  metaRow209 location expression = replaceSourceLoc location expression

theorem metaRow209_proven : MetaRow209Property := by unfold MetaRow209Property; intros; rfl

def MetaRow231Property : Prop := ∀ showAtom expression,
  metaRow231 showAtom expression = metaShowSexpr showAtom expression 0

theorem metaRow231_proven : MetaRow231Property := by unfold MetaRow231Property; intros; rfl

/-- `show_sexpr(io, ex)`; `base/meta.jl:232`. -/

def MetaRow232Property : Prop := ∀ showAtom expression,
  metaRow232 showAtom expression = metaShowSexpr showAtom expression 0

theorem metaRow232_proven : MetaRow232Property := by unfold MetaRow232Property; intros; rfl

/-- Generic `show_sexpr(io, ex, indent)` fallback; `base/meta.jl:233`. -/

def MetaRow233Property : Prop := ∀ showAtom expression indent,
  metaRow233 showAtom expression indent = showAtom expression

theorem metaRow233_proven : MetaRow233Property := by unfold MetaRow233Property; intros; rfl

/-- QuoteNode `show_sexpr`; `base/meta.jl:237-242`. -/

def MetaRow237Property : Prop := ∀ showAtom value indent,
  metaRow237 showAtom value indent = metaShowSexpr showAtom (.quoteNode value) indent

theorem metaRow237_proven : MetaRow237Property := by unfold MetaRow237Property; intros; rfl

/-- Expr `show_sexpr`; `base/meta.jl:243-256`. -/

def MetaRow243Property : Prop := ∀ showAtom head arguments indent,
  metaRow243 showAtom head arguments indent = metaShowSexpr showAtom (.expr head arguments) indent

theorem metaRow243_proven : MetaRow243Property := by unfold MetaRow243Property; intros; rfl

/-- `@dump`; `base/meta.jl:264-266`. -/

def MetaRow264Property : Prop := ∀ expression, metaRow264 expression = .expr "dump" [.quoteNode expression]

theorem metaRow264_proven : MetaRow264Property := by unfold MetaRow264Property; intro; rfl

def MetaRow275Property : Prop := ∀ moduleName expression,
  metaRow275 moduleName expression = lowerCall moduleName expression

theorem metaRow275_proven : MetaRow275Property := by unfold MetaRow275Property; intros; rfl

/-- One-argument `@lower`; `base/meta.jl:284-286`. -/

def MetaRow284Property : Prop := ∀ moduleName expression,
  metaRow284 moduleName expression = lowerCall moduleName expression

theorem metaRow284_proven : MetaRow284Property := by unfold MetaRow284Property; intros; rfl

/-- Two-argument `@lower`; `base/meta.jl:287-289`. -/

def MetaRow287Property : Prop := ∀ moduleName expression,
  metaRow287 moduleName expression = lowerCall moduleName expression

theorem metaRow287_proven : MetaRow287Property := by unfold MetaRow287Property; intros; rfl

/-- `ParseError(msg::AbstractString)`; `base/meta.jl:305`. -/

def MetaRow305Property : Prop := ∀ message, metaRow305 message = (message,none)

theorem metaRow305_proven : MetaRow305Property := by unfold MetaRow305Property; intro; rfl

/-- `parser_for_module`; `base/meta.jl:307-313`. -/

def MetaRow307Property : Prop := ∀ isModule hasOverride,
  metaRow307 isModule hasOverride =
    if isModule && hasOverride then "invokelatest(module.#_internal_julia_parse)" else "Base.VersionedParse"

theorem metaRow307_proven : MetaRow307Property := by unfold MetaRow307Property; intros; rfl

def MetaRow315Property : Prop := ∀ length filename line index options wantSyntax parser,
  (index < 1 ∨ length + 1 < index) →
  metaRow315 length filename line index options wantSyntax parser = .error .boundsError

theorem metaRow315_proven : MetaRow315Property := by
  unfold MetaRow315Property
  intros; simp [metaRow315]; omega

/-- `_is_parse_error`; `base/meta.jl:328-329`. -/

def MetaRow328Property : Prop := ∀ result, metaRow328 result = true ↔ ∃ message, result = .error message

theorem metaRow328_proven : MetaRow328Property := by
  intro result; cases result <;> simp [metaRow328]

/-- Position-taking `parse`; `base/meta.jl:363-377`. -/

def MetaRow363Property : Prop := ∀ length position greedy raise wantSyntax filename parser reply message,
  metaRow315 length filename 1 position (if greedy then "statement" else "atom") wantSyntax parser =
    .ok (.error message, reply) → raise = true →
  metaRow363 length position greedy raise wantSyntax filename parser = .error (.argumentError message)

theorem metaRow363_proven : MetaRow363Property := by
  unfold MetaRow363Property
  intros; simp [metaRow363, *]

/-- Whole-string `parse`; `base/meta.jl:406-421`. -/

def MetaRow406Property : Prop := ∀ length position raise result,
  metaRow406 length position raise result = match result with
    | .error _ | .incomplete _ => .ok result
    | _ => if position ≤ length then
        if raise then .error (.argumentError "extra token after end of expression") else .ok (.error "extra token after end of expression")
      else .ok result

theorem metaRow406_proven : MetaRow406Property := by unfold MetaRow406Property; intros; rfl

/-- `parseatom`; `base/meta.jl:423-427`. -/

def MetaRow423Property : Prop := ∀ length position wantSyntax parser,
  metaRow423 length position wantSyntax parser =
    metaRow315 length "none" 1 position "atom" wantSyntax (fun _ _ index _ => parser index)

theorem metaRow423_proven : MetaRow423Property := by unfold MetaRow423Property; intros; rfl

/-- `parseall`; `base/meta.jl:429-434`. -/

def MetaRow429Property : Prop := ∀ length wantSyntax parser,
  metaRow429 length wantSyntax parser =
    metaRow315 length "none" 1 1 "all" wantSyntax (fun _ _ index _ => parser index)

theorem metaRow429_proven : MetaRow429Property := by unfold MetaRow429Property; intros; rfl

/-- Vector driver `partially_inline!`; `base/meta.jl:463-475`. -/

def MetaRow463Property : Prop := ∀ code slotCount slotOffset statementOffset off,
  (metaRow463 code slotCount slotOffset statementOffset off).length = code.length

theorem metaRow463_proven : MetaRow463Property := by
  unfold MetaRow463Property
  intros; simp [metaRow463]

/-- Node dispatcher `_partially_inline!`; `base/meta.jl:477-621`. -/

def MetaRow477Property : Prop := ∀ node slotCount slotOffset statementOffset off,
  metaRow477 node slotCount slotOffset statementOffset off =
    partiallyInlineNode node slotCount slotOffset statementOffset off

theorem metaRow477_proven : MetaRow477Property := by unfold MetaRow477Property; intros; rfl

/-- `_instantiate_type_in_env`; `base/meta.jl:623`. -/

def MetaRow623Property : Prop := ∀ instantiate value signature parameters,
  metaRow623 instantiate value signature parameters = instantiate value signature parameters

theorem metaRow623_proven : MetaRow623Property := by unfold MetaRow623Property; intros; rfl

def MetaRow634Property : Prop := ∀ value, metaRow634 value = metaUnblock value

theorem metaRow634_proven : MetaRow634Property := by unfold MetaRow634Property; intro; rfl

def MetaRow651Property : Prop := ∀ value, metaRow651 value = metaUnescape value

theorem metaRow651_proven : MetaRow651Property := by unfold MetaRow651Property; intro; rfl

def MetaRow666Property : Prop := ∀ unescaped original,
  metaRow666 unescaped original = metaReescape unescaped original

theorem metaRow666_proven : MetaRow666Property := by unfold MetaRow666Property; intros; rfl

/-- `uncurly`; `base/meta.jl:682`. -/

def MetaRow682Property : Prop := ∀ value,
  metaRow682 value = match value with | .curly head _ => head | other => other

theorem metaRow682_proven : MetaRow682Property := by intro value; cases value <;> rfl

end JuliaLean.ExprReflect
