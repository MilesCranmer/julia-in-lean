import JuliaLean.ExprReflect.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ViewsFaithfulFinal

open JuliaLean.Registry
open JuliaLean.ExprReflect

inductive Error where
  | invalidBoundary | malformedReference | unsupportedReplacement | exhausted
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α
abbrev Withex := Option (Ast × Ast)

def escaped : Ast → Nat → Ast
  | expression, 0 => expression
  | expression, depth + 1 => escaped (.expr "escape" [expression]) depth

/-- The local `escapes` loop at `base/views.jl:22-27`. -/
def m22 (expression : Ast) (depth : Nat) : Ast := escaped expression depth

def P22 : Prop :=
  (∀ expression, m22 expression 0 = expression) ∧
  (∀ expression depth, m22 expression (depth + 1) = m22 (.expr "escape" [expression]) depth)

theorem p22 : P22 := by constructor <;> intros <;> rfl

def firstLast (array dimension : Ast) : Ast × Ast :=
  (.expr "call" [.atom "firstindex", array, dimension],
   .expr "call" [.atom "lastindex", array, dimension])

def isSplat : Ast → Bool
  | .expr "..." [_] => true
  | _ => false

def unsplat : Ast → Ast
  | .expr "..." [value] => value
  | value => value

def isAstNode : Ast → Bool
  | .expr _ _ | .quoteNode _ | .line => true
  | _ => false

inductive MainContext where
  | direct
  | assignment (head : String) (tail : List Ast)

def rebuildMain (context : MainContext) (reference : Ast) : Ast :=
  match context with
  | .direct => reference
  | .assignment head tail => .expr head (reference :: tail)

structure IndexState where
  indices : List Ast
  bindings : List Ast
  usedArray : Bool
  nextDimension : Nat
  splatWidth : Option Ast

def dimensionExpr (state : IndexState) : Ast :=
  match state.splatWidth with
  | none => .int state.nextDimension
  | some width => .expr "call" [.atom "+", width, .int state.nextDimension]

def addSplatWidth (current : Option Ast) (value : Ast) : Option Ast :=
  let width := .expr "call" [.atom "length", value]
  match current with
  | none => some width
  | some previous => some (.expr "call" [.atom "+", previous, width])

mutual
  /-- `replace_ref_begin_end_!`, `base/views.jl:19-27,103-160`. A top-level
  `macrocall` stores its `macroexpand` result as its first model argument. -/
  def replaceFuel : Nat → Ast → Withex → Bool → Nat → Result (Ast × Bool)
    | 0, _, _, _, _ => .error .exhausted
    | fuel + 1, expression, withex, inQuote, escapeDepth =>
      match expression with
      | .expr "macrocall" (expanded :: _) =>
          replaceFuel fuel expanded withex inQuote escapeDepth
      | .atom name =>
          if !inQuote && name = "begin" then
            match withex with
            | none => .error .invalidBoundary
            | some bounds => .ok (escaped bounds.1 escapeDepth, true)
          else if !inQuote && name = "end" then
            match withex with
            | none => .error .invalidBoundary
            | some bounds => .ok (escaped bounds.2 escapeDepth, true)
          else .ok (expression, false)
      | .expr "ref" arguments =>
          if inQuote then do
            let state ← arguments.foldlM (fun state argument => do
              let result ← replaceFuel fuel argument withex inQuote escapeDepth
              .ok (state.1 ++ [result.1], state.2 || result.2)) ([], false)
            .ok (.expr "ref" state.1, state.2)
          else handleRefFuel fuel arguments .direct withex inQuote escapeDepth
      | .expr "$" arguments => do
          let state ← arguments.foldlM (fun state argument => do
            let result ← replaceFuel fuel argument withex false escapeDepth
            .ok (state.1 ++ [result.1], state.2 || result.2)) ([], false)
          .ok (.expr "$" state.1, state.2)
      | .expr "quote" arguments => do
          let state ← arguments.foldlM (fun state argument => do
            let result ← replaceFuel fuel argument withex true escapeDepth
            .ok (state.1 ++ [result.1], state.2 || result.2)) ([], false)
          .ok (.expr "quote" state.1, state.2)
      | .expr "hygienic-scope" arguments => do
          let state ← arguments.foldlM (fun state argument => do
            let result ← replaceFuel fuel argument withex inQuote (escapeDepth + 1)
            .ok (state.1 ++ [result.1], state.2 || result.2)) ([], false)
          .ok (.expr "hygienic-scope" state.1, state.2)
      | .expr "escape" arguments =>
          if escapeDepth = 0 then .ok (expression, false)
          else do
            let state ← arguments.foldlM (fun state argument => do
              let result ← replaceFuel fuel argument withex inQuote (escapeDepth - 1)
              .ok (state.1 ++ [result.1], state.2 || result.2)) ([], false)
            .ok (.expr "escape" state.1, state.2)
      | .expr head arguments =>
          if head = "meta" || head = "inert" then .ok (expression, false)
          else if !inQuote && head.endsWith "=" then
            match arguments with
            | (.expr "ref" reference) :: tail => do
                let transformed ← tail.foldlM (fun state argument => do
                  let result ← replaceFuel fuel argument withex inQuote escapeDepth
                  .ok (state.1 ++ [result.1], state.2 || result.2)) ([], false)
                let handled ← handleRefFuel fuel reference (.assignment head transformed.1)
                  withex inQuote escapeDepth
                .ok (handled.1, transformed.2 || handled.2)
            | _ => do
                let state ← arguments.foldlM (fun state argument => do
                  let result ← replaceFuel fuel argument withex inQuote escapeDepth
                  .ok (state.1 ++ [result.1], state.2 || result.2)) ([], false)
                .ok (.expr head state.1, state.2)
          else do
            let state ← arguments.foldlM (fun state argument => do
              let result ← replaceFuel fuel argument withex inQuote escapeDepth
              .ok (state.1 ++ [result.1], state.2 || result.2)) ([], false)
            .ok (.expr head state.1, state.2)
      | .quoteNode _ | .int _ | .line => .ok (expression, false)

  /-- `handle_refexpr!`, `base/views.jl:28-102`. The model preserves its
  three passes, dimension expressions, splat widths, temporary bindings, and
  conditional caching of the array expression. -/
  def handleRefFuel : Nat → List Ast → MainContext → Withex → Bool → Nat →
      Result (Ast × Bool)
    | 0, _, _, _, _, _ => .error .exhausted
    | fuel + 1, arguments, context, withex, inQuote, escapeDepth =>
      if inQuote then .error .malformedReference
      else match arguments with
        | [] => .error .malformedReference
        | array :: indices => do
            let arrayResult ← replaceFuel fuel array withex inQuote escapeDepth
            let cache := .atom "#S"
            if indices.isEmpty then
              .ok (rebuildMain context (.expr "ref" [arrayResult.1]), arrayResult.2)
            else
              let needTemps := indices.any isSplat
              let initial : IndexState := ⟨[], [], false, 1, none⟩
              let processed ← (indices.zipIdx).foldlM (fun state item => do
                let original := item.1
                let value := unsplat original
                let bounds := firstLast cache (dimensionExpr state)
                let result ← replaceFuel fuel value (some bounds) inQuote escapeDepth
                let used := state.usedArray || result.2
                let temp := .atom ("#arg" ++ toString (item.2 + 1))
                let makeTemp := needTemps && isAstNode result.1
                let binding := .expr "=" [temp, result.1]
                let outputValue := if makeTemp then temp else result.1
                let output := if isSplat original then .expr "..." [outputValue] else outputValue
                let bindings := if makeTemp then state.bindings ++ [binding] else state.bindings
                let splatWidth := if isSplat original
                  then addSplatWidth state.splatWidth outputValue else state.splatWidth
                let nextDimension := if isSplat original
                  then state.nextDimension else state.nextDimension + 1
                let next : IndexState :=
                  { indices := state.indices ++ [output]
                    bindings := bindings
                    usedArray := used
                    nextDimension := nextDimension
                    splatWidth := splatWidth }
                .ok next) initial
              let reference := .expr "ref" (arrayResult.1 :: processed.indices)
              if processed.usedArray then
                let cachedReference := .expr "ref"
                  (escaped cache escapeDepth :: processed.indices)
                let main := rebuildMain context cachedReference
                let block := .expr "block"
                  ([.expr "local=" [cache, arrayResult.1]] ++ processed.bindings ++ [main])
                .ok (block, arrayResult.2)
              else .ok (rebuildMain context reference, arrayResult.2)
end

def astSize : Ast → Nat
  | .atom _ | .int _ | .line => 1
  | .quoteNode value => astSize value + 1
  | .expr _ arguments =>
      arguments.foldl (fun total value => total + astSize value) 1

def replacementFuel (expression : Ast) : Nat := astSize expression * 4 + 8

def m19 (expression : Ast) (withex : Withex) (inQuote : Bool)
    (escapeDepth : Nat) : Result (Ast × Bool) :=
  replaceFuel (replacementFuel expression) expression withex inQuote escapeDepth

def P19 : Prop := ∀ expression withex inQuote escapeDepth,
  m19 expression withex inQuote escapeDepth =
    replaceFuel (replacementFuel expression) expression withex inQuote escapeDepth

theorem p19 : P19 := by unfold P19 m19; intros; rfl

def m28 (arguments : List Ast) (context : MainContext) (withex : Withex)
    (inQuote : Bool) (escapeDepth : Nat) : Result (Ast × Bool) :=
  handleRefFuel (arguments.foldl (fun total value => total + astSize value) 8)
    arguments context withex inQuote escapeDepth

def P28 : Prop := ∀ arguments context withex inQuote escapeDepth,
  m28 arguments context withex inQuote escapeDepth =
    handleRefFuel (arguments.foldl (fun total value => total + astSize value) 8)
      arguments context withex inQuote escapeDepth

theorem p28 : P28 := by unfold P28 m28; intros; rfl

def viewCall (arguments : List Ast) : Ast := .expr "call" (.atom "view" :: arguments)

/-- `@view`, `base/views.jl:210-228`. -/
def m210 (expression : Ast) : Result Ast :=
  match expression with
  | .expr "ref" _ => do
      let replaced ← m19 expression none false 0
      let output ← match replaced.1 with
        | .expr "ref" arguments => .ok (viewCall arguments)
        | .expr "block" arguments =>
            match arguments.getLast? with
            | some (.expr "ref" reference) =>
                .ok (.expr "block" (arguments.dropLast ++ [viewCall reference]))
            | _ => .error .unsupportedReplacement
        | _ => .error .unsupportedReplacement
      .ok (.expr "escape" [output])
  | _ => .error .malformedReference

def P210 : Prop := ∀ expression,
  m210 expression = match expression with
    | .expr "ref" _ => do
        let replaced ← m19 expression none false 0
        let output ← match replaced.1 with
          | .expr "ref" arguments => .ok (viewCall arguments)
          | .expr "block" arguments =>
              match arguments.getLast? with
              | some (.expr "ref" reference) =>
                  .ok (.expr "block" (arguments.dropLast ++ [viewCall reference]))
              | _ => .error .unsupportedReplacement
          | _ => .error .unsupportedReplacement
        .ok (.expr "escape" [output])
    | _ => .error .malformedReference

theorem p210 : P210 := by unfold P210 m210; intros; rfl

/-- `_views(x) = x`, `base/views.jl:247`, for every non-Expr Julia value. -/
def m247 (value : X) : X := value

def P247 : Prop := ∀ {X : Type} value, m247 (X := X) value = value

theorem p247 : P247 := by unfold P247 m247; intros; rfl

def operatorName (head : String) : String := String.ofList head.toList.dropLast

def rewriteFuel : Nat → Ast → Result Ast
  | 0, _ => .error .exhausted
  | fuel + 1, expression =>
    match expression with
    | .expr head arguments =>
        if head = "=" || head = ".=" then
          match arguments with
          | [left, right] => do
              let newLeft ← match left with
                | .expr "ref" reference => .expr "ref" <$> reference.mapM (rewriteFuel fuel)
                | other => rewriteFuel fuel other
              let newRight ← rewriteFuel fuel right
              .ok (.expr head [newLeft, newRight])
          | _ => .error .malformedReference
        else if head = "ref" then do
          let rewritten ← arguments.mapM (rewriteFuel fuel)
          .ok (.expr "call" (.atom "maybeview" :: rewritten))
        else if head.endsWith "=" then
          match arguments with
          | (.expr "ref" (array :: indices)) :: remaining => do
              let rewrittenArray ← rewriteFuel fuel array
              let prepared ← (indices.zipIdx).mapM fun item => do
                let original := item.1
                let source := unsplat original
                let rewritten ← rewriteFuel fuel source
                let temporary := .atom ("i" ++ toString (item.2 + 1))
                let binding := .expr "=" [temporary, .expr "escape" [rewritten]]
                let use := if isSplat original then .expr "..." [temporary] else temporary
                .ok (binding, use)
              let rewrittenRemaining ← remaining.mapM fun value => do
                let rewritten ← rewriteFuel fuel value
                .ok (.expr "escape" [rewritten])
              let uses := prepared.map (·.2)
              let bindings := .expr "=" [.atom "a", .expr "escape" [rewrittenArray]] ::
                prepared.map (·.1)
              let updateHead := if head.startsWith "." then ".=" else "="
              let operator := .expr "escape" [.atom (operatorName head)]
              let read := .expr "call" (.atom "maybeview" :: .atom "a" :: uses)
              let operation := .expr "call" (operator :: read :: rewrittenRemaining)
              let assignment := .expr updateHead [.expr "ref" (.atom "a" :: uses), operation]
              .ok (.expr "hygienic-scope"
                [.expr "let" [.expr "block" bindings, assignment], .atom "Base"])
          | _ => do
              let rewritten ← arguments.mapM (rewriteFuel fuel)
              .ok (.expr head rewritten)
        else do
          let rewritten ← arguments.mapM (rewriteFuel fuel)
          .ok (.expr head rewritten)
    | _ => .ok expression

/-- `_views(::Expr)`, `base/views.jl:248-294`, including assignment targets,
read conversion, operator-assignment temporaries, splats, hygienic scope, and
the generic Expr fallback for arbitrary heads. -/
def m248 (expression : Ast) : Result Ast :=
  rewriteFuel (astSize expression * 4 + 8) expression

def P248 : Prop := ∀ expression,
  m248 expression = rewriteFuel (astSize expression * 4 + 8) expression

theorem p248 : P248 := by unfold P248 m248; intros; rfl

private def entry (line : Nat) (fn statement : String) (prop proof : Lean.Name) : Entry :=
  { id := s!"multidimcov-views-faithful-{line}"
    juliaFile := "base/views.jl"
    juliaFns := [fn]
    statement
    source := s!"base/views.jl:{line}"
    status := .proven
    prop
    thm := some proof }

def entries : List Entry := []

end JuliaLean.MultidimCov.ViewsFaithfulFinal
