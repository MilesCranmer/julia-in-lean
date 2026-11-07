import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.expr
import JuliaLean.Registry.Types
import JuliaLean.base.docs.basedocs
import JuliaLean.base.docs.bindings
import JuliaLean.base.docs.core
import JuliaLean.base.docs.utils
import JuliaLean.base.expr


section

/-!
# Properties of `base/docs/core.jl`, `utils.jl`, `bindings.jl` and `basedocs.jl`
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-! ## `Core.CoreDocs` -/

/-- `DocLinkedList()` has no record; `DocLinkedList(doc, next)` holds `doc` before `next`;
`CoreDocs.doc!` puts the new record `(mod, ex, str, file, line)` in front of `DOCS` and
returns `nothing`. -/
def CoreDocsRecords : Prop :=
  docLinkedList0.hasDoc = false ∧
  (∀ d n, docLinkedList2 d n = .cons d n ∧ (docLinkedList2 d n).hasDoc = true) ∧
  ∀ (docs : DocLinkedList) (line : Int) (file mod : String) (str ex : JV),
    coreDocBang docs line file mod str ex = (.cons ⟨mod, ex, str, file, line⟩ docs, .nothing)

theorem coreDocsRecords : CoreDocsRecords := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ _ _ => rfl⟩

/-- `isexpr(x, h)` holds exactly for an `Expr` with head `h`; `lazy_iterpolate` turns a string
literal or a `:string` interpolation into a `Core.svec` call of its parts and leaves other
values alone. -/
def CoreExprHelpers : Prop :=
  (∀ h args h', coreIsexpr (.expr h args) h' = (h == h')) ∧
  (∀ x h', (∀ h args, x ≠ .expr h args) → coreIsexpr x h' = false) ∧
  (∀ s, lazyIterpolate (.str s) = .expr "call" [svecFn, .str s]) ∧
  (∀ args, lazyIterpolate (.expr "string" args) = .expr "call" (svecFn :: args)) ∧
  (∀ x, (∀ s, x ≠ .str s) → coreIsexpr x "string" = false → lazyIterpolate x = x)

theorem coreExprHelpers : CoreExprHelpers := by
  refine ⟨fun _ _ _ => rfl, fun x h' hx => ?_, fun _ => rfl, fun _ => rfl, fun x hs hx => ?_⟩
  · cases x <;> simp [coreIsexpr] <;> exact (hx _ _ rfl).elim
  · cases x <;> simp_all [lazyIterpolate]

/-- The bootstrap `@doc` expansion stores the docstring with `CoreDocs.doc!` and evaluates
the documented expression: after it for most forms, around it for a `module` (`:toplevel`),
and not at all for a bare call signature. `@doc` with one argument requires `str -> ex`. -/
def CoreDocmExpansion : Prop :=
  ∀ (source : JV) (mod : String) (str x : JV),
    let out := JV.expr "call" [coreDocFn, .qn source, .val mod, lazyIterpolate str, .qn x]
    (coreIsexpr x "module" = true → coreDocm4 source mod str x = .expr "escape" [.expr "toplevel" [out, x]]) ∧
    (coreIsexpr x "call" = true → coreDocm4 source mod str x = .expr "escape" [out]) ∧
    (coreIsexpr x "module" = false → coreIsexpr x "call" = false →
      coreDocm4 source mod str x = .expr "escape" [.expr "block" [x, out]]) ∧
    (∀ l rest, coreDocm3 source mod (.expr "->" [str, .expr "block" (l :: x :: rest)]) =
      .ok (coreDocm4 source mod str x)) ∧
    (∀ (y : JV), (∀ a b rest, y ≠ .expr "->" (a :: b :: rest)) →
      coreDocm3 source mod y = .error (.errorException "invalid '@doc'."))

theorem coreDocmExpansion : CoreDocmExpansion := by
  intro source mod str x
  refine ⟨fun h => by simp [coreDocm4, h], fun h => ?_, fun h1 h2 => by simp [coreDocm4, h1, h2], fun _ _ => rfl, ?_⟩
  · have : coreIsexpr x "module" = false := by
      cases x <;> simp_all [coreIsexpr]
    simp [coreDocm4, this, h]
  · intro y hy
    unfold coreDocm3
    split
    · rename_i a b rest; exact (hy a b rest rfl).elim
    · rfl

end JuliaLean.DocsSyntaxCov

end

namespace JuliaLean.Proofs.base.docs.core

open JuliaLean.Registry

open JuliaLean.DocsSyntaxCov in
open JuliaLean.Registry in
def entries : List Entry := [
  proven "docssyntaxcov-core-records" "base/docs/core.jl" ["DocLinkedList", "doc!"]
    "CoreDocs constructors and doc! prepend the exact record."
    "base/docs/core.jl:10-19" ``CoreDocsRecords ``coreDocsRecords,
  proven "docssyntaxcov-core-expr" "base/docs/core.jl" ["isexpr", "lazy_iterpolate"]
    "Core expression tests and lazy interpolation follow their expression branches."
    "base/docs/core.jl:21-24" ``CoreExprHelpers ``coreExprHelpers,
  proven "docssyntaxcov-core-docm" "base/docs/core.jl" ["docm"]
    "Bootstrap @doc expansion orders definition and registration correctly."
    "base/docs/core.jl:26-37" ``CoreDocmExpansion ``coreDocmExpansion,
]

end JuliaLean.Proofs.base.docs.core
