import JuliaLean.base.generator
import JuliaLean.Proofs.base.iterators.coverage_zip
import JuliaLean.Proofs.base.iterators.coverage_reverse

/-!
# `Generator` and iterator traits (`base/generator.jl`)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

theorem generatorStep_yields (f : V → V) (nx : V → Step) {y : Step} {xs : List V}
    (h : YF nx y xs) : YF (fun s => generatorStep f (nx s)) (generatorStep f y) (xs.map f) := by
  induction xs generalizing y with
  | nil => cases h; exact .nil
  | cons x xs ih =>
      cases h with
      | cons htail => exact .cons (ih htail)

/-- Generator maps every yielded value and delegates length, shape, axes-like
size, dimensionality, keys, emptiness and isdone to its wrapped iterator;
the type-trait methods implement their documented defaults and special cases. -/
def GeneratorSemantics : Prop :=
  (∀ f it xs, it.Yields xs → (generatorIt f it).Yields (xs.map f)) ∧
  (∀ f its, generatorMany zipIt f its =
    generatorIt (fun | .tup xs => f xs | x => f [x]) (zipIt its)) ∧
  (∀ f it, (generatorIt f it).len = it.len ∧
    (generatorIt f it).size = it.size ∧
    (generatorIt f it).isz = it.isz ∧
    (generatorIt f it).done0 = it.done0 ∧
    (generatorIt f it).doneS = it.doneS ∧
    (generatorIt f it).lastv = it.lastv.map f) ∧
  (∀ (l : R JInt64) (s a : R (List JInt64)) (n : R JInt64) (k : R (List V))
      (e : R Bool) (d : R (Option Bool)) f (v : R V),
    generatorLength l = l ∧ generatorSize s = s ∧ generatorAxes a = a ∧
    generatorNdims n = n ∧ generatorKeys k = k ∧ generatorIsempty e = e ∧
    generatorIsdone d = d ∧ generatorLast f v = v.map f) ∧
  (∀ b, generatorTypeTag b = if b then .freeType else .egalType) ∧
  (∀ (α : Type) (typeOf : α → IteratorType) x,
    iteratorSizeValue typeOf x = iteratorSizeType (typeOf x)) ∧
  (∀ t, iteratorSizeType t = match t with
    | .bottom => jthrow (.argumentError "Union{} does not have elements")
    | .any => .ok .sizeUnknown | .tuple => .ok .hasLength
    | .array n => .ok (.hasShape n) | .generator none => .ok .sizeUnknown
    | .generator (some s) => .ok s | .other => .ok .hasLength) ∧
  (∀ (α : Type) (typeOf : α → EltypeIteratorType) x,
    iteratorEltypeValue typeOf x = iteratorEltypeType (typeOf x)) ∧
  (∀ t, iteratorEltypeType t = match t with
    | .bottom => jthrow (.argumentError "Union{} does not have elements")
    | .any | .generator => .ok false | .other => .ok true) ∧
  (∀ s, hasLengthTrait (.ok s) = decide (s.finite = true))

theorem generatorSemantics : GeneratorSemantics := by
  refine ⟨?_, fun _ _ => rfl, ?_, ?_, fun _ => rfl, fun _ _ _ => rfl,
    fun t => by cases t <;> rfl, fun _ _ _ => rfl,
    fun t => by cases t <;> rfl, ?_⟩
  · intro f it xs h
    exact generatorStep_yields f it.next h
  · intro f it
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l s a n k e d f v
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s
    cases s <;> rfl

end JuliaLean.IteratorsCov
