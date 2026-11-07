import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.expr
import JuliaLean.Registry.Types
import JuliaLean.base.docs.basedocs
import JuliaLean.base.docs.bindings
import JuliaLean.base.docs.core
import JuliaLean.base.docs.utils


section

/-!
# Properties of `base/docs/core.jl`, `utils.jl`, `bindings.jl` and `basedocs.jl`
-/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

/-! ## `HTML` and `Text` -/

/-- `HTML(xs...)` shows as the concatenation of `print`ed arguments, `html"s"` as `s`, the
`catdoc` of several `HTML`s as the concatenation of their `text/html` shows; `Text` prints and
shows its content, and `catdoc` of `Text`s concatenates them. -/
def HtmlTextRendering : Prop :=
  ∀ {C : Type} (printC : C → String),
    (∀ xs, showHtml printC (htmlVarargs printC xs) = String.join (xs.map printC)) ∧
    (∀ c, showHtml printC (.value c) = printC c) ∧
    (∀ s, showHtml id (htmlStr s) = s) ∧
    (∀ hs, showHtml printC (catdocHtml printC hs) = String.join (hs.map (showHtml printC))) ∧
    (∀ t, showText printC t = printText printC t) ∧
    (∀ c, printText printC (.value c) = printC c) ∧
    (∀ out, printText printC (.fn out) = String.join out) ∧
    (∀ s, printText id (textStr s) = s) ∧
    (∀ ts, printText printC (catdocText printC ts) = String.join (ts.map (printText printC)))

theorem htmlTextRendering : HtmlTextRendering := by
  intro C printC
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- `isequal(x, y)` implies `hash(x) == hash(y)` (the `hash` contract), for `HTML` and `Text`
whose content type obeys it. -/
def TextHashIsequal : Prop :=
  ∀ {C : Type} (ops : ContentOps C), (∀ a b, ops.isequal a b = true → ops.hash a = ops.hash b) →
    ∀ a b h, wrapperIsequal ops a b = true → wrapperHash ops a h = wrapperHash ops b h

/-- `Float64` contents `-0.0` (`true`) and `0.0` (`false`): equal under `==`, not under
`isequal`, with different hashes. -/
def signedZeroOps : ContentOps Bool :=
  { eq := fun _ _ => true, isequal := fun a b => a == b,
    hash := fun a h => if a then h + 1 else h, hashType := id }

theorem textHashIsequal_refuted : ¬ TextHashIsequal := by
  intro h
  have := h signedZeroOps (by intro a b hab; simp [signedZeroOps] at hab; subst hab; rfl) true false 0 rfl
  simp [wrapperHash, signedZeroOps] at this

/-- `==` of two `HTML`/`Text` of the same type compares their contents with `==`. -/
def WrapperEqContent : Prop :=
  ∀ {C : Type} (ops : ContentOps C) (a b : C), wrapperEq ops a b = ops.eq a b ∧
    wrapperHash ops a 0 = ops.hashType (ops.hash a 0)

theorem wrapperEqContent : WrapperEqContent := fun _ _ _ => ⟨rfl, rfl⟩

end JuliaLean.DocsSyntaxCov

end

namespace JuliaLean.Proofs.base.docs.utils

open JuliaLean.Registry

open JuliaLean.DocsSyntaxCov in
open JuliaLean.Registry in
def entries : List Entry := [
  proven "docssyntaxcov-utils-render" "base/docs/utils.jl" ["HTML", "show", "html_str", "catdoc", "print", "text_str"]
    "HTML and Text construction, rendering and concatenation preserve their content."
    "base/docs/utils.jl:33-93,109-119" ``HtmlTextRendering ``htmlTextRendering,
  proven "docssyntaxcov-utils-equality" "base/docs/utils.jl" ["==", "hash"]
    "Wrapper equality and hashing call the corresponding content operations."
    "base/docs/utils.jl:95-96" ``WrapperEqContent ``wrapperEqContent,
  refuted "docssyntaxcov-text-hash-isequal" "base/docs/utils.jl" ["==", "hash"]
    "isequal wrappers must have equal hashes."
    "base/hashing.jl hash contract"
    "none found (queries: HTML hash isequal, Text hash, Docs.Text hash)"
    "Text(-0.0) and Text(0.0) are isequal but have different hashes."
    ``TextHashIsequal ``textHashIsequal_refuted,
]

end JuliaLean.Proofs.base.docs.utils
