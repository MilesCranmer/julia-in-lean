import JuliaLean.NumMisc.Model
import JuliaLean.NumMisc.Proofs
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry
open JuliaLean.NumMisc

abbrev ViewResult (α : Type) := Except Unit α

def views17 [Inhabited W] (replace : M → E → W → Bool → Int → E × Bool)
    (module : M) (expr : E) : E := (replace module expr default false 0).1

def Views17Property : Prop := ∀ (M E W : Type) [Inhabited W] replace module expr,
  views17 (replace : M → E → W → Bool → Int → E × Bool) module expr =
    (replace module expr default false 0).1
theorem views17Property : Views17Property := by unfold Views17Property; intros; rfl

def viewsEscapes (escape : E → E) : E → Nat → E
  | expr, 0 => expr
  | expr, n + 1 => viewsEscapes escape (escape expr) n

def ViewsEscapesProperty : Prop :=
  (∀ (E : Type) (escape : E → E) expr, viewsEscapes escape expr 0 = expr) ∧
  (∀ (E : Type) (escape : E → E) expr n,
    viewsEscapes escape expr (n + 1) = viewsEscapes escape (escape expr) n)
theorem viewsEscapesProperty : ViewsEscapesProperty := by
  unfold ViewsEscapesProperty
  constructor <;> intros <;> rfl

inductive BoundaryExpr where
  | beginToken | endToken | atom (id : Nat)
  | ref (array : BoundaryExpr) (indices : List BoundaryExpr)
  | quote (body : BoundaryExpr) | dollar (body : BoundaryExpr)
  | hygienic (body : BoundaryExpr) | escape (body : BoundaryExpr)
  | inert (body : BoundaryExpr) | metadata (body : BoundaryExpr)
  | other (head : Nat) (args : List BoundaryExpr)
  deriving Repr

def boundaryReplace (first last : BoundaryExpr) : BoundaryExpr → Bool → Int → BoundaryExpr × Bool
  | .beginToken, false, _ => (first, true)
  | .endToken, false, _ => (last, true)
  | expr@(.ref _ _), false, _ => (expr, false)
  | .quote body, _, escapes =>
      (.quote body, false)
  | .dollar body, _, escapes =>
      (.dollar body, false)
  | .hygienic body, quoted, escapes =>
      (.hygienic body, false)
  | .escape body, quoted, escapes =>
      if escapes = 0 then (.escape body, false)
      else
        (.escape body, false)
  | expr@(.inert _), _, _ => (expr, false)
  | expr@(.metadata _), _, _ => (expr, false)
  | expr@(.other _ _), _, _ => (expr, false)
  | expr, _, _ => (expr, false)

def Views19Property : Prop :=
  (boundaryReplace (.atom 1) (.atom 2) .beginToken false 0 = (.atom 1, true)) ∧
  (boundaryReplace (.atom 1) (.atom 2) .endToken false 0 = (.atom 2, true)) ∧
  (∀ first last body, boundaryReplace first last (.quote body) false 0 =
    (.quote body, false)) ∧
  (∀ first last expr, boundaryReplace first last (.inert expr) false 0 = (.inert expr, false))
theorem views19Property : Views19Property := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intros <;> rfl

def viewsHandleRef (replaceArray : E → E × Bool)
    (replaceIndices : List E → List E × Bool) (cache : E → List E → E → E)
    (main array : E) (indices : List E) : E × Bool :=
  let arrayResult := replaceArray array
  if indices.isEmpty then (main, arrayResult.2)
  else
    let indexResult := replaceIndices indices
    let used := arrayResult.2 || indexResult.2
    (if used then cache arrayResult.1 indexResult.1 main else main, used)

def Views28Property : Prop := ∀ (E : Type) replaceArray replaceIndices cache main array indices,
  viewsHandleRef (replaceArray : E → E × Bool)
      (replaceIndices : List E → List E × Bool) (cache : E → List E → E → E)
      main array indices =
    let arrayResult := replaceArray array
    if indices.isEmpty then (main, arrayResult.2)
    else
      let indexResult := replaceIndices indices
      let used := arrayResult.2 || indexResult.2
      (if used then cache arrayResult.1 indexResult.1 main else main, used)
theorem views28Property : Views28Property := by unfold Views28Property; intros; rfl

inductive ViewMacroOutput (E : Type) where
  | invalid | direct (expr : E) | block (expr : E)

def views210 (isRef isBlock : E → Bool) (replace : E → E)
    (direct block : E → E) (expr : E) : ViewMacroOutput E :=
  if !isRef expr then .invalid
  else
    let replaced := replace expr
    if isRef replaced then .direct (direct replaced)
    else if isBlock replaced then .block (block replaced)
    else .invalid

def Views210Property : Prop := ∀ (E : Type) isRef isBlock replace direct block expr,
  views210 (isRef : E → Bool) (isBlock : E → Bool) (replace : E → E)
      (direct : E → E) (block : E → E) expr =
    if !isRef expr then .invalid
    else let replaced := replace expr
      if isRef replaced then .direct (direct replaced)
      else if isBlock replaced then .block (block replaced) else .invalid
theorem views210Property : Views210Property := by unfold Views210Property; intros; rfl

def views235 (getindex : A → List I → R) (a : A) (indices : List I) : R :=
  getindex a indices
def views236 (view : A → List I → R) (a : A) (indices : List I) : R := view a indices
def views237 (getindex : A → List I → R) (a : A) (indices : List I) : R :=
  getindex a indices
def views238 (getindex : A → R) (a : A) : R := getindex a
def views239 (getindex : A → R) (a : A) : R := getindex a

def ViewsMaybeProperty : Prop :=
  (∀ (A I R : Type) (get : A → List I → R) a indices,
    views235 get a indices = get a indices) ∧
  (∀ (A I R : Type) (view : A → List I → R) a indices,
    views236 view a indices = view a indices) ∧
  (∀ (A I R : Type) (get : A → List I → R) a indices,
    views237 get a indices = get a indices) ∧
  (∀ (A R : Type) (get : A → R) a, views238 get a = get a) ∧
  (∀ (A R : Type) (get : A → R) a, views239 get a = get a)
theorem viewsMaybeProperty : ViewsMaybeProperty := by
  simp [ViewsMaybeProperty, views235, views236, views237, views238, views239]

def Views247Property : Prop := ∀ expression : ViewExpr,
  (match expression with | .atom id => rewriteViews (.atom id) | other => rewriteViews other) =
    rewriteViews expression
theorem views247Property : Views247Property := by
  intro expression
  cases expression <;> rfl

def Views248Property : Prop := ViewsDocumentedRewrite
theorem views248Property : Views248Property := JuliaLean.NumMisc.viewsDocumentedRewrite_proven

def views332 (replace : M → E → E) (rewrite escape : E → E) (module : M) (expr : E) : E :=
  escape (rewrite (replace module expr))
def Views332Property : Prop := ∀ (M E : Type) replace rewrite escape module expr,
  views332 (replace : M → E → E) (rewrite : E → E) (escape : E → E) module expr =
    escape (rewrite (replace module expr))
theorem views332Property : Views332Property := by unfold Views332Property; intros; rfl

private def viewsEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/views.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def viewsReviewEntries : List Entry := []

end JuliaLean.MultidimCov
