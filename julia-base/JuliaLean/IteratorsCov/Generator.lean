import JuliaLean.IteratorsCov.Zip
import JuliaLean.IteratorsCov.Reverse

/-!
# `Generator` and iterator traits (`base/generator.jl`)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- The body of `iterate(g::Generator, s...)`, `base/generator.jl:44-50`. -/
def generatorStep (f : V → V) : Step → Step
  | .ok (some (x, s)) => .ok (some (f x, s))
  | y => y

/-- `Generator(f, iter)` together with all one-line delegating methods at
`base/generator.jl:52-59`. -/
def generatorIt (f : V → V) (it : It) : It where
  first := generatorStep f it.first
  next := fun s => generatorStep f (it.next s)
  isz := it.isz
  iel := false
  elt := .any
  len := it.len
  size := it.size
  done0 := it.done0
  doneS := it.doneS
  lastv := it.lastv.map f

/-- `Generator(f, I1, I2, Is...) = Generator(splat(f), zip(...))`, line 37.
The dynamic model receives the splatted function on the tuple value. -/
def generatorMany (f : List V → V) (its : List It) : It :=
  generatorIt (fun | .tup xs => f xs | x => f [x]) (zipIt its)

/-- The one-line delegation methods at lines 52-59. Their arguments are the
results of calling the corresponding method on `g.iter`. -/
def generatorLength (inner : R JInt64) : R JInt64 := inner
def generatorSize (inner : R (List JInt64)) : R (List JInt64) := inner
def generatorAxes (inner : R (List JInt64)) : R (List JInt64) := inner
def generatorNdims (inner : R JInt64) : R JInt64 := inner
def generatorKeys (inner : R (List V)) : R (List V) := inner
def generatorLast (f : V → V) (inner : R V) : R V := inner.map f
def generatorIsempty (inner : R Bool) : R Bool := inner
def generatorIsdone (inner : R (Option Bool)) : R (Option Bool) := inner

/-- The constructor's function-field representation at lines 39-42. -/
inductive GeneratorFunctionTag where
  | value | freeType | egalType
  deriving Repr, DecidableEq

def generatorTypeTag (hasFreeTypevars : Bool) : GeneratorFunctionTag :=
  if hasFreeTypevars then .freeType else .egalType

/-- Type shapes dispatched on by `IteratorSize`, lines 95-104. -/
inductive IteratorType where
  | bottom | any | tuple | array (rank : Nat) | generator (inner : Option Isz) | other
  deriving Repr, DecidableEq

/-- `IteratorSize(x)` calls the type method; `IteratorSize(::Type)` defaults
to HasLength; Bottom throws; Any is SizeUnknown; tuples, arrays and generators
take their source branches (`base/generator.jl:95-104`). -/
def iteratorSizeType : IteratorType → R Isz
  | .bottom => jthrow (.argumentError "Union{} does not have elements")
  | .any => .ok .sizeUnknown
  | .tuple => .ok .hasLength
  | .array rank => .ok (.hasShape rank)
  | .generator none => .ok .sizeUnknown
  | .generator (some inner) => .ok inner
  | .other => .ok .hasLength

def iteratorSizeValue (typeOf : α → IteratorType) (x : α) : R Isz :=
  iteratorSizeType (typeOf x)

/-- `haslength(iter)`, line 104. -/
def hasLengthTrait (size : R Isz) : Bool :=
  match size with
  | .ok .hasLength | .ok (.hasShape _) => true
  | _ => false

/-- Type shapes dispatched on by `IteratorEltype`, lines 129-134. -/
inductive EltypeIteratorType where
  | bottom | any | generator | other
  deriving Repr, DecidableEq

def iteratorEltypeType : EltypeIteratorType → R Bool
  | .bottom => jthrow (.argumentError "Union{} does not have elements")
  | .any | .generator => .ok false
  | .other => .ok true

def iteratorEltypeValue (typeOf : α → EltypeIteratorType) (x : α) : R Bool :=
  iteratorEltypeType (typeOf x)

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
  (∀ f its, generatorMany f its =
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
