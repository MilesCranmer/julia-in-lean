import JuliaLean.Registry.Types
import JuliaLean.Proofs.Compiler.src.typelattice.Common

/-!
Properties of `Compiler/src/abstractlattice.jl`.

The generic `⊏`, `⋤`, `is_lattice_equal`, the `fallback_lattice` methods and `widenlattice(𝕃, t)`
are modelled in `JuliaLean/Compiler/src/typelattice.lean` (they call the layered `⊑`), and their
properties are stated here, under this file's name.
-/

namespace JuliaLean.Proofs.Compiler.src.abstractlattice

open JuliaLean.Registry JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## Layer stacks -/

/-- The layers of a lattice, from the outermost down to `JLTypeLattice`: each layer struct holds
its parent layer (`Compiler/src/abstractlattice.jl:24-95`), and `ConstsLattice` sits directly on
`JLTypeLattice` (`:15-19`). -/
def layers : Lattice → List Lattice
  | .jlType => [.jlType]
  | .consts => [.consts, .jlType]
  | L@(.partials p) | L@(.conditionals p) | L@(.interConditionals p) | L@(.mustAliases p)
  | L@(.interMustAliases p) | L@(.inference p) => L :: layers p

/-! ## `widenlattice(𝕃)` -/

/-- `widenlattice(JLTypeLattice())` throws an `ErrorException` ("Type lattice is the
least-precise lattice available"), and every other layer widens, without touching the state, to
the next layer of its stack (the layer below it, not some other coarser layer), which is one step
closer to `JLTypeLattice`, so repeated widening reaches `JLTypeLattice`. -/
def WidenlatticeTerminates : Prop :=
  ThrowsJulia "ErrorException" (widenlattice .jlType) ∧
  ∀ L, L ≠ .jlType → ∀ s, ∃ L', (widenlattice L).run s = .ok (L', s) ∧
    layerDepth L' < layerDepth L ∧ layers L = L :: layers L'

theorem widenlatticeTerminates_proven : WidenlatticeTerminates := by
  refine ⟨fun s => ⟨"Type lattice is the least-precise lattice available", rfl⟩, ?_⟩
  intro L hL s
  cases L with
  | jlType => exact absurd rfl hL
  | consts => exact ⟨.jlType, rfl, by decide, rfl⟩
  | partials p => exact ⟨p, rfl, by simp [layerDepth], rfl⟩
  | conditionals p => exact ⟨p, rfl, by simp [layerDepth], rfl⟩
  | interConditionals p => exact ⟨p, rfl, by simp [layerDepth], rfl⟩
  | mustAliases p => exact ⟨p, rfl, by simp [layerDepth], rfl⟩
  | interMustAliases p => exact ⟨p, rfl, by simp [layerDepth], rfl⟩
  | inference p => exact ⟨p, rfl, by simp [layerDepth], rfl⟩

/-! ## `is_valid_lattice_norec` -/

/-- The kind of layer that adjoins each kind of element, from the layer docstrings at
`Compiler/src/abstractlattice.jl:6-91`: types belong to `JLTypeLattice`; `Const` and
`PartialTypeVar` to `ConstsLattice`; `PartialStruct`, `PartialOpaque` and `PartialTask` to
`PartialsLattice`; `Conditional`, `InterConditional`, `MustAlias` and `InterMustAlias` to their own
layers; `LimitedAccuracy` to `InferenceLattice`. An object that is not a type (a `TypeVar`, a
`Vararg`) belongs to none. Kinds are numbered as in `layerKind`. -/
def eltOwner : LElt → Option Nat
  | .ty t => if t.isType then some 0 else none
  | .const _ | .partialTypeVar .. => some 1
  | .partialStruct .. | .partialOpaque .. | .partialTask _ => some 2
  | .conditional .. => some 3
  | .interConditional .. => some 4
  | .mustAlias .. => some 5
  | .interMustAlias .. => some 6
  | .limitedAccuracy .. => some 7

/-- `is_valid_lattice_norec(𝕃, x)` holds exactly when `𝕃` is the kind of layer that adjoins `x`
(its docstring). -/
def NorecOwner : Prop :=
  ∀ L e, isValidLatticeNorec L e = true ↔ eltOwner e = some (layerKind L)

theorem norecOwner_proven : NorecOwner := by
  intro L e
  cases L <;> cases e <;>
    simp [isValidLatticeNorec, eltOwner, layerKind, LElt.isConst, LElt.isPartialStruct,
      LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias, LElt.isInterMustAlias,
      LElt.isPartialTypeVar, LElt.isLimited, LElt.isPartialOpaque, LElt.isPartialTask,
      LElt.isTypeElt] <;>
    (try split) <;> simp_all

/-- Each lattice element is owned by at most one kind of layer: no element passes
`is_valid_lattice_norec` for two layers of different kinds. `widenlattice(𝕃, t)` and the
layered `tmeet` rely on this to hand an element to the one layer that understands it. -/
def NorecDisjoint : Prop :=
  ∀ (L₁ L₂ : Lattice) (e : LElt), isValidLatticeNorec L₁ e = true →
    isValidLatticeNorec L₂ e = true → layerKind L₁ = layerKind L₂

theorem norecDisjoint_proven : NorecDisjoint := by
  intro L₁ L₂ e h₁ h₂
  cases e <;> cases L₁ <;> cases L₂ <;>
    simp_all [isValidLatticeNorec, LElt.isConst, LElt.isPartialStruct, LElt.isConditional,
      LElt.isInterConditional, LElt.isMustAlias, LElt.isInterMustAlias, LElt.isPartialTypeVar,
      LElt.isLimited, LElt.isPartialOpaque, LElt.isPartialTask, LElt.isTypeElt, layerKind]

theorem norec_and_false {L₁ L₂ : Lattice} (e : LElt) (h : layerKind L₁ ≠ layerKind L₂) :
    (isValidLatticeNorec L₁ e && isValidLatticeNorec L₂ e) = false := by
  cases h₁ : isValidLatticeNorec L₁ e <;> cases h₂ : isValidLatticeNorec L₂ e <;> simp
  exact h (norecDisjoint_proven _ _ _ h₁ h₂)

/-! ## `is_valid_lattice` -/

/-- A native type is a valid element of every lattice: `is_valid_lattice(𝕃, T)` holds for every
type `T`. (Every layer defers native types to `JLTypeLattice`, and `widenlattice(𝕃, t)` returns
types as elements of every lattice.) -/
def IsValidLatticeTypes : Prop :=
  ∀ (L : Lattice) (t : Val), t.isType = true → isValidLattice L (.ty t) = true

/-- Counterexample: `is_valid_lattice(typeinf_lattice, Int) === false`. -/
theorem isValidLatticeTypes_refuted : ¬ IsValidLatticeTypes := fun h =>
  absurd (h typeinfLattice longType (by decide)) (by decide)

/-- What `is_valid_lattice` computes: on `JLTypeLattice`, `true` for every type and `false` for
every other element (`JLTypeLattice` is "the lattice of Julia types",
`Compiler/src/abstractlattice.jl:6-10`); `false` for every element on
every other lattice. The generic method joins its layer's test and the parent's with `&&`, and no
element passes the tests of two layers (`NorecDisjoint`). -/
def IsValidLatticeOnlyJLType : Prop :=
  (∀ t, t.isType = true → isValidLattice .jlType (.ty t) = true) ∧
  (∀ e, e.isTypeElt = false → isValidLattice .jlType e = false) ∧
  ∀ (L : Lattice) (e : LElt), L ≠ .jlType → isValidLattice L e = false

theorem isValidLatticeOnlyJLType_proven : IsValidLatticeOnlyJLType := by
  refine ⟨fun t ht => ht, fun e he => he, ?_⟩
  intro L e hL
  induction L with
  | jlType => exact absurd rfl hL
  | consts => exact norec_and_false e (by decide)
  | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
  | interMustAliases p ih | inference p ih =>
    by_cases hp : p = .jlType
    · subst hp; exact norec_and_false e (by decide)
    · simp only [isValidLattice, ih hp, Bool.and_false]

/-! ## `tmerge_field` -/

/-- No layer of the default lattices provides a field merge: `tmerge_field` returns `nothing`
on every layer, for all fields, without changing the state, so `tmerge(::PartialsLattice, ...)`
always uses its own field merge (the docstring at `Compiler/src/abstractlattice.jl:127-136`). -/
def TmergeFieldNothing : Prop :=
  ∀ (L : Lattice) (a b : LElt) (s : Nat), (tmergeField L a b).run s = .ok (none, s)

theorem tmergeFieldNothing_proven : TmergeFieldNothing := by
  intro L
  induction L with
  | jlType => intro a b s; rfl
  | consts => intro a b s; rfl
  | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
  | interMustAliases p ih | inference p ih =>
    intro a b s; simp only [tmergeField]; exact ih a b s

/-! ## `⊑(::JLTypeLattice, ...)` -/

theorem sqsubJLType_ok {n : Nat} {E : CEnv} {a b : LElt} {s r s'}
    (h : (sqsubJLType n E a b).run s = .ok (r, s')) :
    ∃ x y, a = .ty x ∧ b = .ty y ∧ x.isType = true ∧ y.isType = true ∧
      (issub n E x y).run s = .ok (r, s') := by
  unfold sqsubJLType at h
  split at h
  · rename_i x y
    split at h
    · rename_i hxy
      simp only [Bool.and_eq_true] at hxy
      exact ⟨x, y, rfl, rfl, hxy.1, hxy.2, h⟩
    · rw [jlThrow_run] at h; cases h
  · rw [jlThrow_run] at h; cases h

/-- On `JLTypeLattice`, `⊑` is subtyping (docstring of `⊑`, `Compiler/src/abstractlattice.jl:149`:
"If `𝕃` is `JLTypeLattice`, this is equivalent to subtyping"): on two types it is the same
computation as `a <: b` (`jl_subtype`), so it is a preorder on types whenever subtyping is; an
argument that is not a type is a `MethodError` (the method is declared on `AnyType`). -/
def SqsubJLTypePreorder : Prop :=
  (∀ n E x y, x.isType = true → y.isType = true →
    sqsubJLType n E (.ty x) (.ty y) = issub n E x y) ∧
  (SubReflexive → SubTransitive →
    (∀ n E t, t.isType = true → Returns (sqsubJLType n E (.ty t) (.ty t)) (· = true)) ∧
    (∀ n₁ n₂ n₃ E a b c s₁ s₁' s₂ s₂',
      (sqsubJLType n₁ E a b).run s₁ = .ok (true, s₁') →
      (sqsubJLType n₂ E b c).run s₂ = .ok (true, s₂') →
      Returns (sqsubJLType n₃ E a c) (· = true)) ∧
    (∀ n E a b, a.isTypeElt = false → ThrowsJulia "MethodError" (sqsubJLType n E a b)))

theorem sqsubJLTypePreorder_proven : SqsubJLTypePreorder := by
  refine ⟨fun n E x y hx hy => by simp [sqsubJLType, hx, hy], ?_⟩
  intro hrefl htrans
  refine ⟨?_, ?_, ?_⟩
  · intro n E t ht s r s' h
    obtain ⟨x, y, hx, hy, _, _, h⟩ := sqsubJLType_ok h
    cases hx; cases hy
    exact hrefl n E t s r s' ht h
  · intro n₁ n₂ n₃ E a b c s₁ s₁' s₂ s₂' h₁ h₂ s₃ r s₃' h₃
    obtain ⟨x, y, hx, hy, _, _, k₁⟩ := sqsubJLType_ok h₁
    obtain ⟨y', z, hy', hz, _, _, k₂⟩ := sqsubJLType_ok h₂
    obtain ⟨x', z', hx', hz', _, _, k₃⟩ := sqsubJLType_ok h₃
    subst hx hy hz
    cases hy'; cases hx'; cases hz'
    exact htrans _ _ _ E x y z _ _ _ _ _ _ _ k₁ k₂ k₃
  · intro n E a b ha s
    refine ⟨"⊑(::JLTypeLattice, ...)", ?_⟩
    unfold sqsubJLType
    match a, b with
    | .ty x, .ty y =>
      simp only [LElt.isTypeElt] at ha
      simp only [ha, Bool.false_and, Bool.false_eq_true, ite_false]
      rfl
    | .ty x, .const _ => rfl
    | .ty x, .partialStruct .. => rfl
    | .ty x, .conditional .. => rfl
    | .ty x, .interConditional .. => rfl
    | .ty x, .mustAlias .. => rfl
    | .ty x, .interMustAlias .. => rfl
    | .ty x, .partialTypeVar .. => rfl
    | .ty x, .limitedAccuracy .. => rfl
    | .ty x, .partialOpaque .. => rfl
    | .ty x, .partialTask .. => rfl
    | .const _, _ => rfl
    | .partialStruct .., _ => rfl
    | .conditional .., _ => rfl
    | .interConditional .., _ => rfl
    | .mustAlias .., _ => rfl
    | .interMustAlias .., _ => rfl
    | .partialTypeVar .., _ => rfl
    | .limitedAccuracy .., _ => rfl
    | .partialOpaque .., _ => rfl
    | .partialTask .., _ => rfl


/-- A `Conditional`, an `InterConditional`, a `MustAlias` and an `InterMustAlias`. -/
def sampleCond : LElt := .conditional 0 0 (.ty .bottom) (.ty .bottom) false
def sampleInterCond : LElt := .interConditional 0 (.ty .bottom) (.ty .bottom)
def sampleAlias : LElt := .mustAlias 0 0 (.ty .bottom) 0 (.ty .bottom)
def sampleInterAlias : LElt := .interMustAlias 0 (.ty .bottom) 0 (.ty .bottom)

/-- `has_conditional(𝕃)` holds exactly when a layer of `𝕃` holds conditionals (its
`is_valid_lattice_norec` accepts a `Conditional` or an `InterConditional`), `has_mustalias(𝕃)`
exactly when a layer holds must-aliases, and `has_extended_unionsplit(𝕃)` agrees with
`has_mustalias(𝕃)` (union splitting through aliases needs an alias layer). On the native
interpreter, the inference and IPO lattices have both and the optimizer lattice has neither. -/
def HasLayerQueries : Prop :=
  (∀ L, hasConditional L = (layers L).any fun l =>
    isValidLatticeNorec l sampleCond || isValidLatticeNorec l sampleInterCond) ∧
  (∀ L, hasMustalias L = (layers L).any fun l =>
    isValidLatticeNorec l sampleAlias || isValidLatticeNorec l sampleInterAlias) ∧
  (∀ L, hasExtendedUnionsplit L = hasMustalias L) ∧
  hasConditional typeinfLattice = true ∧ hasConditional ipoLattice = true ∧
  hasConditional optimizerLattice = false ∧ hasMustalias typeinfLattice = true ∧
  hasMustalias ipoLattice = true ∧ hasMustalias optimizerLattice = false

theorem hasLayerQueries_proven : HasLayerQueries := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · intro L
    induction L <;> simp_all [hasConditional, layers, isValidLatticeNorec, sampleCond,
      sampleInterCond, LElt.isConst, LElt.isPartialTypeVar, LElt.isPartialStruct,
      LElt.isPartialOpaque, LElt.isPartialTask, LElt.isConditional, LElt.isInterConditional,
      LElt.isMustAlias, LElt.isInterMustAlias, LElt.isLimited, LElt.isTypeElt]
  · intro L
    induction L <;> simp_all [hasMustalias, layers, isValidLatticeNorec, sampleAlias,
      sampleInterAlias, LElt.isConst, LElt.isPartialTypeVar, LElt.isPartialStruct,
      LElt.isPartialOpaque, LElt.isPartialTask, LElt.isConditional, LElt.isInterConditional,
      LElt.isMustAlias, LElt.isInterMustAlias, LElt.isLimited, LElt.isTypeElt]
  · intro L
    induction L <;> simp_all [hasExtendedUnionsplit, hasMustalias]

/-! ## `has_nontrivial_extended_info`, `is_const_prop_profitable_arg`, `is_forwardable_argtype` -/

/-- `L` has a layer of kind `k`. -/
def hasKind (L : Lattice) (k : Nat) : Bool := (layers L).any (layerKind · == k)

/-- `has_nontrivial_extended_info(𝕃, t)` (docstring at `Compiler/src/abstractlattice.jl:183-188`:
"non-trivial extended lattice information that would not be available from the type itself"):
a native type has none, on every lattice; a `PartialStruct`, `PartialOpaque` or `PartialTask` has
some on every lattice with a partials layer; a `PartialTypeVar` on every lattice with a constants
layer; and a `Const(v)` has some exactly when `typeof(v)` is not a singleton type (a singleton
type already pins its value). The generic method only passes an element to the next layer, and
no layer of this query recognizes a slot wrapper (`Conditional`, `InterConditional`, `MustAlias`,
`InterMustAlias`) or a `LimitedAccuracy`, so for those the answer is `false` on every lattice.
The const-prop heuristic widens slot wrappers before asking
(`Compiler/src/abstractinterpretation.jl:1263`); the other callers use the answer to decide
whether to keep an element as a `PartialStruct` field (`Compiler/src/tfuncs.jl:2322`,
`Compiler/src/typelimits.jl:693`, `Compiler/src/abstractinterpretation.jl:3507`). -/
def HasNontrivialExtendedInfoSpec : Prop :=
  (∀ n E L t, Returns (hasNontrivialExtendedInfo n E L (.ty t)) (· = false)) ∧
  (∀ n E L x s, hasKind L 2 = true →
    (x.isPartialStruct || x.isPartialOpaque || x.isPartialTask) = true →
    (hasNontrivialExtendedInfo n E L x).run s = .ok (true, s)) ∧
  (∀ n E L tv l u s, hasKind L 1 = true →
    (hasNontrivialExtendedInfo n E L (.partialTypeVar tv l u)).run s = .ok (true, s)) ∧
  (∀ n E L v s, hasKind L 1 = true →
    (hasNontrivialExtendedInfo n E L (.const v)).run s =
      (do return !(← issingletontype n E (typeOf v)) : CM Bool).run s) ∧
  (∀ n E L x s, (x.isSlotWrapper || x.isLimited) = true →
    (hasNontrivialExtendedInfo n E L x).run s = .ok (false, s))

theorem hasNontrivialExtendedInfoSpec_proven : HasNontrivialExtendedInfoSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left 4
  · intro n E L x s hx
    induction L with
    | jlType => rfl
    | consts =>
      cases x <;> first | rfl | (simp [LElt.isSlotWrapper, LElt.isAnyConditional,
        LElt.isAnyMustAlias, LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
        LElt.isInterMustAlias, LElt.isLimited] at hx)
    | partials p ih =>
      cases x <;> first | exact ih | (simp [LElt.isSlotWrapper, LElt.isAnyConditional,
        LElt.isAnyMustAlias, LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
        LElt.isInterMustAlias, LElt.isLimited] at hx)
    | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih => exact ih
  · intro n E L t
    induction L with
    | jlType => intro s r s' h; cases h; rfl
    | consts => intro s r s' h; cases h; rfl
    | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih => exact ih
  · intro n E L x s hk hx
    induction L with
    | jlType => simp [hasKind, layers, layerKind] at hk
    | consts => simp [hasKind, layers, layerKind] at hk
    | partials p ih =>
      cases x <;> first | rfl | (simp [LElt.isPartialStruct, LElt.isPartialOpaque,
        LElt.isPartialTask] at hx)
    | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih =>
      exact ih (by simpa [hasKind, layers, layerKind] using hk)
  · intro n E L tv l u s hk
    induction L with
    | jlType => simp [hasKind, layers, layerKind] at hk
    | consts => rfl
    | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih =>
      exact ih (by simpa [hasKind, layers, layerKind] using hk)
  · intro n E L v s hk
    induction L with
    | jlType => simp [hasKind, layers, layerKind] at hk
    | consts => rfl
    | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih =>
      exact ih (by simpa [hasKind, layers, layerKind] using hk)

/-- `is_const_prop_profitable_arg(𝕃, t)`: a native type and a `PartialTypeVar` ("this isn't
forwardable") are never profitable; a `PartialStruct`, `PartialOpaque` or `PartialTask` is on
every lattice with a partials layer; and, on a lattice with a constants layer, a `Const` of a
mutable value that is not a `Symbol`, a type, a `Method` or a `CodeInstance` is profitable exactly
when its type has const fields ("don't consider mutable values useful constants unless they have
const fields", `Compiler/src/abstractlattice.jl:234`), while a `Const` of a `Symbol`, a type, a
`Method`, a `CodeInstance` or an immutable value always is. As for
`has_nontrivial_extended_info`, no layer of this query recognizes a slot wrapper or a
`LimitedAccuracy`, so for those it is `false` on every lattice. -/
def alwaysProfitableConst (v : Val) : Bool :=
  v.isSymbol || v.isType || typeOf v == methodType || typeOf v == codeInstanceType

def IsConstPropProfitableArgSpec : Prop :=
  (∀ E L t s, (isConstPropProfitableArg E L (.ty t)).run s = .ok (false, s)) ∧
  (∀ E L tv l u s, (isConstPropProfitableArg E L (.partialTypeVar tv l u)).run s = .ok (false, s)) ∧
  (∀ E L x s, hasKind L 2 = true →
    (x.isPartialStruct || x.isPartialOpaque || x.isPartialTask) = true →
    (isConstPropProfitableArg E L x).run s = .ok (true, s)) ∧
  (∀ E L v s, hasKind L 1 = true → alwaysProfitableConst v = false →
    (ismutable E v).run s = .ok (true, s) →
    (isConstPropProfitableArg E L (.const v)).run s = .ok (hasConstfields E v, s)) ∧
  (∀ E L v s, hasKind L 1 = true → alwaysProfitableConst v = false →
    (ismutable E v).run s = .ok (false, s) →
    (isConstPropProfitableArg E L (.const v)).run s = .ok (true, s)) ∧
  (∀ E L v s, hasKind L 1 = true → alwaysProfitableConst v = true →
    (isConstPropProfitableArg E L (.const v)).run s = .ok (true, s)) ∧
  (∀ E L x s, (x.isSlotWrapper || x.isLimited) = true →
    (isConstPropProfitableArg E L x).run s = .ok (false, s))

theorem icp_consts_run (E : CEnv) (v : Val) (s : Nat) :
    (isConstPropProfitableArg E .consts (.const v)).run s =
      (if alwaysProfitableConst v = true then pure true else do
        if !(← ismutable E v) then return true
        return hasConstfields E v : CM Bool).run s := rfl

theorem icp_lift {E : CEnv} {L : Lattice} {x : LElt} {s : Nat} {r : Bool}
    (hk : hasKind L 1 = true) (hx : x.isPartialStruct = false ∧ x.isPartialOpaque = false ∧
      x.isPartialTask = false)
    (h : (isConstPropProfitableArg E .consts x).run s = .ok (r, s)) :
    (isConstPropProfitableArg E L x).run s = .ok (r, s) := by
  induction L with
  | jlType => simp [hasKind, layers, layerKind] at hk
  | consts => exact h
  | partials p ih =>
    obtain ⟨h1, h2, h3⟩ := hx
    show (if x.isPartialStruct = true then pure true else if x.isPartialOpaque = true then pure true
      else if x.isPartialTask = true then pure true else isConstPropProfitableArg E p x : CM Bool).run s = _
    rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h3])]
    exact ih (by simpa [hasKind, layers, layerKind] using hk)
  | conditionals p ih | interConditionals p ih | mustAliases p ih
  | interMustAliases p ih | inference p ih =>
    exact ih (by simpa [hasKind, layers, layerKind] using hk)

theorem isConstPropProfitableArgSpec_proven : IsConstPropProfitableArgSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 6
  · intro E L x s hx
    induction L with
    | jlType => rfl
    | consts =>
      cases x <;> first | rfl | (simp [LElt.isSlotWrapper, LElt.isAnyConditional,
        LElt.isAnyMustAlias, LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
        LElt.isInterMustAlias, LElt.isLimited] at hx)
    | partials p ih =>
      cases x <;> first | exact ih | (simp [LElt.isSlotWrapper, LElt.isAnyConditional,
        LElt.isAnyMustAlias, LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias,
        LElt.isInterMustAlias, LElt.isLimited] at hx)
    | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih => exact ih
  · intro E L t s
    induction L with
    | jlType => rfl
    | consts => rfl
    | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih => exact ih
  · intro E L tv l u s
    induction L with
    | jlType => rfl
    | consts => rfl
    | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih => exact ih
  · intro E L x s hk hx
    induction L with
    | jlType => simp [hasKind, layers, layerKind] at hk
    | consts => simp [hasKind, layers, layerKind] at hk
    | partials p ih =>
      cases x <;> first | rfl | (simp [LElt.isPartialStruct, LElt.isPartialOpaque,
        LElt.isPartialTask] at hx)
    | conditionals p ih | interConditionals p ih | mustAliases p ih
    | interMustAliases p ih | inference p ih =>
      exact ih (by simpa [hasKind, layers, layerKind] using hk)
  · intro E L v s hk hv hm
    refine icp_lift hk ⟨rfl, rfl, rfl⟩ ?_
    rw [icp_consts_run, if_neg (by simp [hv]), run_bind_ok hm]
    rfl
  · intro E L v s hk hv hm
    refine icp_lift hk ⟨rfl, rfl, rfl⟩ ?_
    rw [icp_consts_run, if_neg (by simp [hv]), run_bind_ok hm]
    rfl
  · intro E L v s hk hv
    refine icp_lift hk ⟨rfl, rfl, rfl⟩ ?_
    rw [icp_consts_run, if_pos hv]
    rfl

/-- The layers whose own wrappers local inference forwards to a callee as given argument types
(`ConstsLattice`, `PartialsLattice`, `ConditionalsLattice`, `MustAliasesLattice`). -/
def forwardsOwn (l : Lattice) : Bool :=
  layerKind l == 1 || layerKind l == 2 || layerKind l == 3 || layerKind l == 5

/-- `is_forwardable_argtype(𝕃, x)` holds exactly when one of the forwarding layers of `𝕃` owns
`x` (`is_valid_lattice_norec`), except that a `PartialTypeVar` is never forwardable: native types,
`LimitedAccuracy`, `InterConditional` and `InterMustAlias` never are. -/
def IsForwardableArgtypeSpec : Prop :=
  ∀ L x, isForwardableArgtype L x =
    ((layers L).any (fun l => forwardsOwn l && isValidLatticeNorec l x) && !x.isPartialTypeVar)

theorem isForwardableArgtypeSpec_proven : IsForwardableArgtypeSpec := by
  intro L x
  induction L with
  | jlType => cases x <;> rfl
  | consts => cases x <;> rfl
  | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
  | interMustAliases p ih | inference p ih =>
    simp only [isForwardableArgtype, layers, List.any_cons, ih]
    cases x <;> simp [forwardsOwn, layerKind, isValidLatticeNorec, LElt.isConst,
      LElt.isPartialTypeVar, LElt.isPartialStruct, LElt.isPartialOpaque, LElt.isPartialTask,
      LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias, LElt.isInterMustAlias,
      LElt.isLimited, LElt.isTypeElt]

/-! ## `⊏` and `⋤` -/

/-- `⊏` "is defined as the irreflexive kernel of `⊑`" (docstring at
`Compiler/src/abstractlattice.jl:155-160`): whenever `a ⊑ a`, `a ⊏ a` is false. -/
def SqsubStrictIrreflexive : Prop :=
  ∀ n E L a, Returns (sqsub n E L a a) (· = true) → Returns (sqsubStrict n E L a a) (· = false)

theorem sqsubStrictIrreflexive_proven : SqsubStrictIrreflexive := by
  intro n E L a hr s r s' h
  unfold sqsubStrict at h
  obtain ⟨c, s₁, hc, h⟩ := run_bind_inv h
  have := hr _ _ _ hc
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
  obtain ⟨d, s₂, hd, h⟩ := run_bind_inv h
  have := hr _ _ _ hd
  subst this
  cases h; rfl

/-- `⊏` is the strict order of `⊑` (docstring at `Compiler/src/abstractlattice.jl:155-160`, "the
strict partial order over the type inference lattice"): `a ⊏ b` holds exactly when `a ⊑ b` and not
`b ⊑ a`. When `a ⋢ b`, `a ⊏ b` is `false` without asking `b ⊑ a`; when `a ⊑ b`, it is the negation
of `b ⊑ a`, asked from the state `a ⊑ b` left. -/
def SqsubStrictPart : Prop :=
  ∀ n E L a b s s₁,
    ((sqsub n E L a b).run s = .ok (false, s₁) →
      (sqsubStrict n E L a b).run s = .ok (false, s₁)) ∧
    ((sqsub n E L a b).run s = .ok (true, s₁) → ∀ r s₂, (sqsub n E L b a).run s₁ = .ok (r, s₂) →
      (sqsubStrict n E L a b).run s = .ok (!r, s₂))

theorem sqsubStrictPart_proven : SqsubStrictPart := by
  intro n E L a b s s₁
  refine ⟨fun h => ?_, fun h r s₂ h₂ => ?_⟩
  · unfold sqsubStrict
    rw [run_bind_ok h]
    rfl
  · unfold sqsubStrict
    rw [run_bind_ok h]
    refine (run_bind_ok h₂).trans ?_
    rfl

/-- `⋤` "could be used as a slightly more efficient version of the strict order `⊏`, where we
can safely assume `a ⊑ b` holds" (`Compiler/src/abstractlattice.jl:163-168`): when `a ⊑ b`
returned `true`, `a ⋤ b` returns what `a ⊏ b` returns, from the state `⊑` left. -/
def SqsubStrictNeAgrees : Prop :=
  ∀ n E L a b s s₁, (sqsub n E L a b).run s = .ok (true, s₁) →
    (sqsubStrict n E L a b).run s = (sqsubStrictNe n E L a b).run s₁

theorem sqsubStrictNeAgrees_proven : SqsubStrictNeAgrees := by
  intro n E L a b s s₁ h
  unfold sqsubStrict
  rw [run_bind_ok h]
  rfl

/-! ## The `fallback_lattice` methods -/

/-- The lattice-free `⊑`, `⊏`, `⋤` and `is_lattice_equal` use `fallback_lattice`, which is the
lattice a `NativeInterpreter` infers with (`typeinf_lattice`, `Compiler/src/types.jl:649`), so
external code calling them gets the native interpreter's answers. -/
def FallbackIsTypeinf : Prop :=
  fallbackLattice = typeinfLattice ∧
  ∀ n E a b, sqsubFallback n E a b = sqsub n E typeinfLattice a b ∧
    sqsubStrictFallback n E a b = sqsubStrict n E typeinfLattice a b ∧
    sqsubStrictNeFallback n E a b = sqsubStrictNe n E typeinfLattice a b ∧
    isLatticeEqualFallback n E a b = isLatticeEqual n E typeinfLattice a b

theorem fallbackIsTypeinf_proven : FallbackIsTypeinf :=
  ⟨rfl, fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ## `widenlattice(𝕃, t)` -/

/-- `widenlattice(𝕃, t)` widens `t` into `𝕃`: it returns `t` itself when some layer of `𝕃`
owns it, and the native type `widenconst(t)` otherwise. -/
def WidenlatticeEltSpec : Prop :=
  ∀ n E L t s, 1 ≤ n →
    ((layers L).any (isValidLatticeNorec · t) = true →
      (widenlatticeElt n E L t).run s = .ok (t, s)) ∧
    ((layers L).any (isValidLatticeNorec · t) = false →
      (widenlatticeElt n E L t).run s = (do return .ty (← widenconst n E t) : CM LElt).run s)

theorem widenconst_type {n : Nat} {E : CEnv} {T : Val} {s : Nat} (h : T.isType = true) (hn : 1 ≤ n) :
    (widenconst n E (.ty T)).run s = .ok (T, s) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show (if T.isType = true then pure T else _ : CM Val).run s = _
  rw [if_pos h]; rfl

theorem widenlatticeEltSpec_proven : WidenlatticeEltSpec := by
  intro n E L t s hn
  induction L with
  | jlType =>
    refine ⟨fun h => ?_, fun _ => rfl⟩
    simp [layers] at h
    cases t <;> simp [isValidLatticeNorec, LElt.isTypeElt] at h
    rename_i T
    show (do return LElt.ty (← widenconst n E (.ty T)) : CM LElt).run s = _
    rw [run_bind_ok (widenconst_type h hn)]; rfl
  | consts =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp [layers] at h
      rcases h with h | h
      · show (if isValidLatticeNorec .consts t = true then pure t else _ : CM LElt).run s = _
        rw [if_pos h]; rfl
      · have hc : isValidLatticeNorec .consts t = false := by
          cases hh : isValidLatticeNorec .consts t
          · rfl
          · exact absurd (norecDisjoint_proven _ _ _ hh h) (by decide)
        show (if isValidLatticeNorec .consts t = true then pure t else _ : CM LElt).run s = _
        rw [if_neg (by simp [hc])]
        cases t <;> simp [isValidLatticeNorec, LElt.isTypeElt] at h
        rename_i T
        show (do return LElt.ty (← widenconst n E (.ty T)) : CM LElt).run s = _
        rw [run_bind_ok (widenconst_type h hn)]; rfl
    · simp [layers] at h
      show (if isValidLatticeNorec .consts t = true then pure t else _ : CM LElt).run s = _
      rw [if_neg (by simp [h.1])]
  | partials p ih | conditionals p ih | interConditionals p ih | mustAliases p ih
  | interMustAliases p ih | inference p ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [layers, List.any_cons, Bool.or_eq_true] at h
      unfold widenlatticeElt
      split
      · rfl
      · rcases h with h | h
        · contradiction
        · exact ih.1 h
    · simp only [layers, List.any_cons, Bool.or_eq_false_iff] at h
      unfold widenlatticeElt
      rw [if_neg (by simp [h.1])]
      exact ih.2 h.2

/-! ## Registry -/

/-- Registry entries of `Compiler/src/abstractlattice.jl`. -/
def entries : List Entry := [
  { id := "compiler-al-widenlattice-terminates", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["widenlattice(::JLTypeLattice)", "widenlattice(::ConstsLattice)", "widenlattice(𝕃::PartialsLattice)", "widenlattice(𝕃::ConditionalsLattice)", "widenlattice(𝕃::InterConditionalsLattice)", "widenlattice(𝕃::MustAliasesLattice)", "widenlattice(𝕃::InterMustAliasesLattice)", "widenlattice(𝕃::InferenceLattice)"],
    statement := "widenlattice(JLTypeLattice()) throws an ErrorException and every other layer widens, without side effects, to the next layer of its own stack (its parent), one step closer to JLTypeLattice, so repeated widening terminates.",
    source := "Compiler/src/abstractlattice.jl:12 (error message: the type lattice is the least precise)",
    status := .proven, prop := ``WidenlatticeTerminates, thm := some ``widenlatticeTerminates_proven },
  { id := "compiler-al-norec-disjoint", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["is_valid_lattice_norec(::JLTypeLattice, elem)", "is_valid_lattice_norec(::ConstsLattice, elem)", "is_valid_lattice_norec(::PartialsLattice, elem)", "is_valid_lattice_norec(::ConditionalsLattice, elem)", "is_valid_lattice_norec(::InterConditionalsLattice, elem)", "is_valid_lattice_norec(::MustAliasesLattice, elem)", "is_valid_lattice_norec(::InterMustAliasesLattice, elem)", "is_valid_lattice_norec(::InferenceLattice, elem)"],
    statement := "No lattice element passes is_valid_lattice_norec for two layers of different kinds: each element is owned by at most one layer.",
    source := "invariant: widenlattice(𝕃, t) and the layered tmeet hand an element to the one layer that owns it",
    status := .proven, prop := ``NorecDisjoint, thm := some ``norecDisjoint_proven },
  { id := "compiler-al-norec-owner", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["is_valid_lattice_norec(::JLTypeLattice, elem)", "is_valid_lattice_norec(::ConstsLattice, elem)", "is_valid_lattice_norec(::PartialsLattice, elem)", "is_valid_lattice_norec(::ConditionalsLattice, elem)", "is_valid_lattice_norec(::InterConditionalsLattice, elem)", "is_valid_lattice_norec(::MustAliasesLattice, elem)", "is_valid_lattice_norec(::InterMustAliasesLattice, elem)", "is_valid_lattice_norec(::InferenceLattice, elem)"],
    statement := "is_valid_lattice_norec(𝕃, x) holds exactly when 𝕃 is the kind of layer whose docstring adjoins x: types for JLTypeLattice, Const and PartialTypeVar for ConstsLattice, PartialStruct/PartialOpaque/PartialTask for PartialsLattice, each slot wrapper for its own layer, LimitedAccuracy for InferenceLattice.",
    source := "layer docstrings Compiler/src/abstractlattice.jl:6-91",
    status := .proven, prop := ``NorecOwner, thm := some ``norecOwner_proven },
  { id := "compiler-al-is-valid-lattice-types", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["is_valid_lattice(𝕃::AbstractLattice, elem)", "is_valid_lattice(𝕃::JLTypeLattice, elem)"],
    statement := "A native type is a valid element of every lattice: is_valid_lattice(𝕃, T) holds for every type T.",
    source := "invariant: every layer defers native types to JLTypeLattice; widenlattice(𝕃, t) treats an element owned by any layer as an element of 𝕃",
    status := .refuted, prop := ``IsValidLatticeTypes, thm := some ``isValidLatticeTypes_refuted,
    issue := "none found (queries: is_valid_lattice, is_valid_lattice_norec; issues and prs)",
    notes := "Counterexample: is_valid_lattice(typeinf_lattice, Int) === false (the method uses && where || is needed). Same on Julia 1.13.3 and nightly 290d5bb5f5. No caller in Compiler/src." },
  { id := "compiler-al-is-valid-lattice-only-jltype", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["is_valid_lattice(𝕃::AbstractLattice, elem)", "is_valid_lattice(𝕃::JLTypeLattice, elem)"],
    statement := "is_valid_lattice(JLTypeLattice(), x) is true for every type and false for every other element; is_valid_lattice(𝕃, x) is false for every element x on every lattice 𝕃 other than JLTypeLattice (the scope of the refuted compiler-al-is-valid-lattice-types).",
    source := "Compiler/src/abstractlattice.jl:281-283 (what the method computes)",
    status := .proven, prop := ``IsValidLatticeOnlyJLType, thm := some ``isValidLatticeOnlyJLType_proven },
  { id := "compiler-al-tmerge-field-nothing", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["tmerge_field(𝕃::AbstractLattice, a, b)", "tmerge_field(::JLTypeLattice, a, b)"],
    statement := "tmerge_field returns nothing on every layer of the default lattices, for all fields and without side effects, so tmerge(::PartialsLattice) always uses its default field merge.",
    source := "docstring Compiler/src/abstractlattice.jl:127-136",
    status := .proven, prop := ``TmergeFieldNothing, thm := some ``tmergeFieldNothing_proven },
  { id := "compiler-al-sqsub-jltype-preorder", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["⊑(::JLTypeLattice, a::AnyType, b::AnyType)"],
    statement := "On JLTypeLattice, ⊑ on two types is the same computation as a <: b (jl_subtype); it is reflexive and transitive on types whenever jl_subtype is, and a MethodError for an argument that is not a type.",
    source := "docstring Compiler/src/abstractlattice.jl:144-150 (\"If 𝕃 is JLTypeLattice, this is equivalent to subtyping\")",
    status := .proven, prop := ``SqsubJLTypePreorder, thm := some ``sqsubJLTypePreorder_proven,
    notes := "The equivalence with jl_subtype holds unconditionally. The preorder part is generic over subtyping: it assumes SubReflexive and SubTransitive (partial-correctness laws of the model's jl_subtype; known corner cases of Julia subtyping break transitivity)." },
  { id := "compiler-al-has-layer-queries", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["has_conditional(𝕃::AbstractLattice)", "has_conditional(::AnyConditionalsLattice)", "has_conditional(::JLTypeLattice)", "has_mustalias(𝕃::AbstractLattice)", "has_mustalias(::AnyMustAliasesLattice)", "has_mustalias(::JLTypeLattice)", "has_extended_unionsplit(𝕃::AbstractLattice)", "has_extended_unionsplit(::AnyMustAliasesLattice)", "has_extended_unionsplit(::JLTypeLattice)"],
    statement := "has_conditional(𝕃) holds exactly when a layer of 𝕃 accepts a Conditional or InterConditional, has_mustalias(𝕃) exactly when a layer accepts a MustAlias or InterMustAlias, and has_extended_unionsplit agrees with has_mustalias; the native inference and IPO lattices have both, the optimizer lattice neither.",
    source := "invariant (the queries ask whether 𝕃 can hold these wrappers)",
    status := .proven, prop := ``HasLayerQueries, thm := some ``hasLayerQueries_proven },
  { id := "compiler-al-nontrivial-extended-info", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["has_nontrivial_extended_info(𝕃::AbstractLattice, t)", "has_nontrivial_extended_info(𝕃::PartialsLattice, t)", "has_nontrivial_extended_info(𝕃::ConstsLattice, t)", "has_nontrivial_extended_info(::JLTypeLattice, t)"],
    statement := "Native types carry no extended information on any lattice; PartialStruct/PartialOpaque/PartialTask do on lattices with a partials layer, PartialTypeVar on lattices with a constants layer, and Const(v) exactly when typeof(v) is not a singleton type; slot wrappers and LimitedAccuracy, which no layer of this query recognizes, get false on every lattice.",
    source := "docstring Compiler/src/abstractlattice.jl:183-188",
    status := .proven, prop := ``HasNontrivialExtendedInfoSpec, thm := some ``hasNontrivialExtendedInfoSpec_proven,
    notes := "The false answer for slot wrappers is stated as what the generic method's delegation gives; the const-prop caller widens slot wrappers first (Compiler/src/abstractinterpretation.jl:1263), the others use the answer to decide whether to keep a PartialStruct field (tfuncs.jl:2322, typelimits.jl:693, abstractinterpretation.jl:3507)." },
  { id := "compiler-al-const-prop-profitable", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["is_const_prop_profitable_arg(𝕃::AbstractLattice, t)", "is_const_prop_profitable_arg(𝕃::PartialsLattice, t)", "is_const_prop_profitable_arg(𝕃::ConstsLattice, t)", "is_const_prop_profitable_arg(::JLTypeLattice, t)"],
    statement := "Native types and PartialTypeVar are never profitable for constant propagation; partial wrappers are on lattices with a partials layer; a Const of a mutable value that is not a Symbol, type, Method or CodeInstance is profitable exactly when its type has const fields, and a Const of a Symbol, type, Method, CodeInstance or immutable value always is; slot wrappers and LimitedAccuracy are never.",
    source := "comments Compiler/src/abstractlattice.jl:234,239",
    status := .proven, prop := ``IsConstPropProfitableArgSpec, thm := some ``isConstPropProfitableArgSpec_proven,
    notes := "Method and CodeInstance objects are mutable references (Val.mutableRef) of the concrete types Core.Method and Core.CodeInstance; the difftest generator includes a Const of each." },
  { id := "compiler-al-forwardable-argtype", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["is_forwardable_argtype(𝕃::AbstractLattice, x)", "is_forwardable_argtype(𝕃::ConditionalsLattice, x)", "is_forwardable_argtype(𝕃::PartialsLattice, x)", "is_forwardable_argtype(𝕃::ConstsLattice, x)", "is_forwardable_argtype(𝕃::MustAliasesLattice, x)", "is_forwardable_argtype(::JLTypeLattice, x)"],
    statement := "is_forwardable_argtype(𝕃, x) holds exactly when one of the local-inference layers of 𝕃 (constants, partials, conditionals, must-aliases) owns x, except PartialTypeVar; native types, LimitedAccuracy, InterConditional and InterMustAlias never are.",
    source := "invariant (Compiler/src/inferenceresult.jl:104 forwards exactly these argument types)",
    status := .proven, prop := ``IsForwardableArgtypeSpec, thm := some ``isForwardableArgtypeSpec_proven },
  { id := "compiler-al-strict-irreflexive", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["⊏(𝕃::AbstractLattice, a, b)"],
    statement := "⊏ is the irreflexive kernel of ⊑: whenever a ⊑ a, a ⊏ a is false.",
    source := "docstring Compiler/src/abstractlattice.jl:155-160",
    status := .proven, prop := ``SqsubStrictIrreflexive, thm := some ``sqsubStrictIrreflexive_proven },
  { id := "compiler-al-strict-part", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["⊏(𝕃::AbstractLattice, a, b)"],
    statement := "a ⊏ b holds exactly when a ⊑ b and not b ⊑ a: false without asking b ⊑ a when a ⋢ b, and the negation of b ⊑ a otherwise.",
    source := "docstring Compiler/src/abstractlattice.jl:155-160 (the strict partial order over the lattice)",
    status := .proven, prop := ``SqsubStrictPart, thm := some ``sqsubStrictPart_proven },
  { id := "compiler-al-strictne-agrees", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["⋤(𝕃::AbstractLattice, a, b)"],
    statement := "When a ⊑ b returned true, a ⋤ b returns what a ⊏ b returns (from the state ⊑ left).",
    source := "docstring Compiler/src/abstractlattice.jl:163-168",
    status := .proven, prop := ``SqsubStrictNeAgrees, thm := some ``sqsubStrictNeAgrees_proven },
  { id := "compiler-al-fallback-is-typeinf", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["⊑(a, b)", "⊏(a, b)", "⋤(a, b)", "is_lattice_equal(a, b)"],
    statement := "The lattice-free ⊑, ⊏, ⋤ and is_lattice_equal use fallback_lattice, which equals the NativeInterpreter typeinf_lattice.",
    source := "comment Compiler/src/abstractlattice.jl:309 (fallbacks for external packages) and Compiler/src/types.jl:649",
    status := .proven, prop := ``FallbackIsTypeinf, thm := some ``fallbackIsTypeinf_proven },
  { id := "compiler-al-widenlattice-elt", juliaFile := "Compiler/src/abstractlattice.jl",
    juliaFns := ["widenlattice(::JLTypeLattice, t)", "widenlattice(𝕃::AbstractLattice, t)"],
    statement := "widenlattice(𝕃, t) returns t itself when some layer of 𝕃 owns it and the native type widenconst(t) otherwise.",
    source := "comment Compiler/src/abstractlattice.jl:320 and invariant",
    status := .proven, prop := ``WidenlatticeEltSpec, thm := some ``widenlatticeEltSpec_proven }
]

end JuliaLean.Proofs.Compiler.src.abstractlattice
