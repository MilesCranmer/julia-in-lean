import JuliaLean.base.generator
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.generator

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.generator

/-!
# Properties of `base/generator.jl`

Specifications of generator iteration, finite-length and shape traits, and
known element types, stated from the source docstrings and iterator invariants.
Iterator steps and callees from other files remain typed interface parameters.
-/

/-! Nothing to promise (metadata and trait forwarding)
- `size@53`: forwards the underlying iterator's size; no independent size rule is stated for a
  Generator here.
- `axes@54`: forwards the underlying iterator's axes; it has no separate Generator axes rule here.
- `ndims@55`: forwards the underlying iterator's dimension count; no independent Generator
  dimension rule is stated here.
- `keys@56`: forwards the underlying iterator's keys; no independent Generator key rule is stated
  here.
- `isempty@58`: forwards the underlying iterator's emptiness; no separate emptiness behavior is
  stated in the Generator docstring.
- `isdone@59`: forwards the underlying iterator's state test; no independent Generator state rule
  is stated here.
- `IteratorSize@95`: dispatches to the trait of `typeof(x)`.
- `IteratorSize@102`: forwards a Generator's size trait from its underlying iterator; finite-length
  consequences are stated by `IteratorSizeBehavior`.
- `IteratorEltype@129`: dispatches to the trait of `typeof(x)`.
- `IteratorEltype@132`: `Any` has no known element type, so no concrete yielded type is promised.
- `IteratorEltype@134`: Generator's element type is unknown, so this trait makes no concrete yielded
  type promise.
-/

def collectIteratorPrefix {I Args A : Type}
    (iterate : I → Args → Jl (IteratorStep A Args)) :
    Nat → I → Args → Except GeneratorError (List A)
  | 0, _, _ => .ok []
  | n + 1, iter, state =>
      match iterate iter state with
      | .error error => .error (.iterator error)
      | .ok .done => .ok []
      | .ok .malformed => .error .tupleTypeAssertion
      | .ok (.yielded value next) =>
          match collectIteratorPrefix iterate n iter next with
          | .error error => .error error
          | .ok rest => .ok (value :: rest)

def collectGeneratorPrefix {I F Args A B : Type}
    (apply : F → A → B)
    (iterate : I → Args → Jl (IteratorStep A Args))
    (g : Generator I F) : Nat → Args → Except GeneratorError (List B)
  | 0, _ => .ok []
  | n + 1, state =>
      match iterateGenerator apply iterate g state with
      | .error error => .error error
      | .ok none => .ok []
      | .ok (some (value, next)) =>
          match collectGeneratorPrefix apply iterate g n next with
          | .error error => .error error
          | .ok rest => .ok (value :: rest)

def GeneratorMapsFinitePrefixes : Prop :=
  ∀ {I F A B Args : Type} (g : Generator I F)
    (apply : F → A → B)
    (iterate : I → Args → Jl (IteratorStep A Args))
    (fuel : Nat) (state : Args) (values : List A),
    collectIteratorPrefix iterate fuel g.iter state = .ok values →
      collectGeneratorPrefix apply iterate g fuel state =
        .ok (values.map (apply g.f))

def GeneratorRejectsMalformedStep : Prop :=
  ∀ {I F A B Args : Type} (g : Generator I F)
    (apply : F → A → B)
    (iterate : I → Args → Jl (IteratorStep A Args)) (state : Args),
    iterate g.iter state = .ok .malformed →
      iterateGenerator apply iterate g state = .error .tupleTypeAssertion

def GeneratorIterationSemantics : Prop :=
  GeneratorMapsFinitePrefixes ∧ GeneratorRejectsMalformedStep

def GeneratorTypeMapsFinitePrefixes : Prop :=
  ∀ {I T A B Args : Type} (hasFreeTypevars : T → Bool)
    (typeValue : T) (iter : I)
    (apply : GeneratorTypeFunction T → A → B)
    (iterate : I → Args → Jl (IteratorStep A Args))
    (fuel : Nat) (state : Args) (values : List A),
    collectIteratorPrefix iterate fuel iter state = .ok values →
      collectGeneratorPrefix apply iterate
        (generatorFromType hasFreeTypevars typeValue iter) fuel state =
          .ok (values.map (apply (if hasFreeTypevars typeValue then
            .typeValue typeValue else .typeEgal typeValue)) )

def GeneratorManyMapsFinitePrefixes : Prop :=
  ∀ {F G I1 I2 Rest It A B Args : Type}
    (splat : F → G) (zip : I1 → I2 → Rest → It)
    (apply : G → A → B)
    (iterate : It → Args → Jl (IteratorStep A Args))
    (f : F) (i1 : I1) (i2 : I2) (rest : Rest)
    (fuel : Nat) (state : Args) (values : List A),
    collectIteratorPrefix iterate fuel (zip i1 i2 rest) state = .ok values →
      collectGeneratorPrefix apply iterate
        (generatorMany splat zip f i1 i2 rest) fuel state =
          .ok (values.map (apply (splat f)))

def GeneratorTypeManyMapsFinitePrefixes : Prop :=
  ∀ {T G I1 I2 Rest It A B Args : Type}
    (splat : T → G) (zip : I1 → I2 → Rest → It)
    (apply : G → A → B)
    (iterate : It → Args → Jl (IteratorStep A Args))
    (typeValue : T) (i1 : I1) (i2 : I2) (rest : Rest)
    (fuel : Nat) (state : Args) (values : List A),
    collectIteratorPrefix iterate fuel (zip i1 i2 rest) state = .ok values →
      collectGeneratorPrefix apply iterate
        (generatorTypeMany splat zip typeValue i1 i2 rest) fuel state =
          .ok (values.map (apply (splat typeValue)))

def GeneratorLastMatchesFiniteIteration : Prop :=
  ∀ {I F Args A B : Type} (g : Generator I F)
    (apply : F → A → B)
    (iterate : I → Args → Jl (IteratorStep A Args))
    (last : I → Jl A) (state : Args),
    (∀ (preceding : List A) (lastValue : A),
      collectIteratorPrefix iterate (preceding.length + 2) g.iter state =
        .ok (preceding ++ [lastValue]) →
      last g.iter = .ok lastValue →
      generatorLast last apply g = .ok (apply g.f lastValue) ∧
      collectGeneratorPrefix apply iterate g (preceding.length + 2) state =
        .ok (preceding.map (apply g.f) ++ [apply g.f lastValue])) ∧
    (∀ error,
      collectIteratorPrefix iterate 1 g.iter state = .ok [] →
      last g.iter = .error error →
      generatorLast last apply g = .error error ∧
      collectGeneratorPrefix apply iterate g 1 state = .ok [])

def IteratorSizeBehavior : Prop :=
  (∀ {I F Args A B : Type} (g : Generator I F)
    (typeof : Generator I F → IteratorType)
    (length : I → Jl Nat) (apply : F → A → B)
    (iterate : I → Args → Jl (IteratorStep A Args))
    (fuel : Nat) (state : Args) (sourceValues : List A) (values : List B),
    (iteratorSizeValue typeof g = .ok .hasLength ∨
      ∃ dimensions, iteratorSizeValue typeof g = .ok (.hasShape dimensions)) →
    collectIteratorPrefix iterate fuel g.iter state = .ok sourceValues →
    sourceValues.length < fuel →
    length g.iter = .ok sourceValues.length →
    collectGeneratorPrefix apply iterate g fuel state = .ok values →
      generatorLength length g = .ok values.length ∧
      haslength (iteratorSizeValue typeof) g = .ok true) ∧
  (haslength (iteratorSizeValue id) .any = .ok false) ∧
  (haslength (iteratorSizeValue id) .tuple = .ok true) ∧
  (haslength (iteratorSizeValue id) .other = .ok true) ∧
  (∀ dimensions,
    haslength (iteratorSizeValue id) (.abstractArray dimensions) = .ok true ∧
    iteratorSizeValue id (.abstractArray dimensions) = .ok (.hasShape dimensions)) ∧
  (∀ inner,
    haslength (iteratorSizeValue id) (.generator inner) =
      match inner with
      | none => .ok false
      | some innerType => haslength (iteratorSizeValue id) innerType) ∧
  (∀ {I : Type} (iteratorSize : I → Jl IteratorSize) (iter : I),
    iteratorSize iter = .ok .sizeUnknown → haslength iteratorSize iter = .ok false) ∧
  (∀ {I : Type} (iteratorSize : I → Jl IteratorSize) (iter : I),
    iteratorSize iter = .ok .isInfinite → haslength iteratorSize iter = .ok false) ∧
  iteratorSizeValue id .unionBottom =
    .error (.argumentError "Union{} does not have elements")

def IteratorEltypeMatchesYieldType : Prop :=
  ∀ {I Args A : Type} (iter : I)
    (typeof : I → IteratorType) (eltype : I → A → Prop)
    (iterate : I → Args → Jl (IteratorStep A Args))
    (fuel : Nat) (state : Args) (values : List A),
    iteratorEltypeValue typeof iter = .ok .hasEltype →
    (∀ state value next, iterate iter state = .ok (.yielded value next) →
      eltype iter value) →
    collectIteratorPrefix iterate fuel iter state = .ok values →
    ∀ value, value ∈ values → eltype iter value

def IteratorEltypeBehavior : Prop :=
  IteratorEltypeMatchesYieldType ∧
  iteratorEltypeValue id .other = .ok .hasEltype ∧
  iteratorEltypeValue id .unionBottom =
    .error (.argumentError "Union{} does not have elements")

theorem generatorMapsFinitePrefixes_proven : GeneratorMapsFinitePrefixes := by
  intro I F A B Args g apply iterate fuel
  induction fuel with
  | zero =>
    intro state values h
    simp [collectIteratorPrefix] at h
    subst values
    rfl
  | succ n ih =>
    intro state values h
    cases step : iterate g.iter state with
    | error e => simp [collectIteratorPrefix, step] at h
    | ok result =>
      cases result with
      | done =>
        simp [collectIteratorPrefix, step] at h
        subst values
        simp [collectGeneratorPrefix, iterateGenerator, step]
      | malformed => simp [collectIteratorPrefix, step] at h
      | yielded value next =>
        cases rest : collectIteratorPrefix iterate n g.iter next with
        | error e => simp [collectIteratorPrefix, step, rest] at h
        | ok xs =>
          simp [collectIteratorPrefix, step, rest] at h
          subst values
          simp [collectGeneratorPrefix, iterateGenerator, step, ih next xs rest]

theorem generatorIterationSemantics_proven : GeneratorIterationSemantics := by
  refine ⟨generatorMapsFinitePrefixes_proven, ?_⟩
  intro I F A B Args g apply iterate state h
  simp [iterateGenerator, h]

theorem generatorTypeMapsFinitePrefixes_proven : GeneratorTypeMapsFinitePrefixes := by
  intro I T A B Args hasFree typeValue iter apply iterate fuel state values h
  exact generatorMapsFinitePrefixes_proven
    (generatorFromType hasFree typeValue iter) apply iterate fuel state values h

theorem generatorManyMapsFinitePrefixes_proven : GeneratorManyMapsFinitePrefixes := by
  intro F G I1 I2 Rest It A B Args splat zip apply iterate f i1 i2 rest fuel state values h
  exact generatorMapsFinitePrefixes_proven
    (generatorMany splat zip f i1 i2 rest) apply iterate fuel state values h

theorem generatorTypeManyMapsFinitePrefixes_proven : GeneratorTypeManyMapsFinitePrefixes := by
  intro T G I1 I2 Rest It A B Args splat zip apply iterate typeValue i1 i2 rest fuel state values h
  exact generatorMapsFinitePrefixes_proven
    (generatorTypeMany splat zip typeValue i1 i2 rest) apply iterate fuel state values h

theorem generatorLastMatchesFiniteIteration_proven : GeneratorLastMatchesFiniteIteration := by
  intro I F Args A B g apply iterate last state
  constructor
  · intro preceding lastValue collected h
    constructor
    · simp [generatorLast, h]; rfl
    · simpa using generatorMapsFinitePrefixes_proven g apply iterate
        (preceding.length + 2) state (preceding ++ [lastValue]) collected
  · intro error collected h
    constructor
    · simp [generatorLast, h]; rfl
    · exact generatorMapsFinitePrefixes_proven g apply iterate 1 state [] collected

theorem iteratorSizeBehavior_proven : IteratorSizeBehavior := by
  refine ⟨?_, by rfl, by rfl, by rfl, ?_, ?_, ?_, ?_, by rfl⟩
  · intro I F Args A B g typeof length apply iterate fuel state sourceValues values trait collected _ len mapped
    have mapped : values = sourceValues.map (apply g.f) :=
      Except.ok.inj (mapped.symm.trans
        (generatorMapsFinitePrefixes_proven g apply iterate fuel state sourceValues collected))
    constructor
    · rw [mapped, List.length_map]
      exact len
    · rcases trait with trait | ⟨dimensions, trait⟩ <;> simp [haslength, trait] <;> rfl
  · intro dimensions
    exact ⟨rfl, rfl⟩
  · intro inner
    cases inner <;> rfl
  · intro I iteratorSize iter h
    simp [haslength, h]; rfl
  · intro I iteratorSize iter h
    simp [haslength, h]; rfl

theorem iteratorEltypeBehavior_proven : IteratorEltypeBehavior := by
  refine ⟨?_, rfl, rfl⟩
  intro I Args A iter typeof eltype iterate fuel state values _ law collected
  induction fuel generalizing state values with
  | zero =>
    simp [collectIteratorPrefix] at collected
    subst values
    simp
  | succ n ih =>
    cases step : iterate iter state with
    | error e => simp [collectIteratorPrefix, step] at collected
    | ok result =>
      cases result with
      | done =>
        simp [collectIteratorPrefix, step] at collected
        subst values
        simp
      | malformed => simp [collectIteratorPrefix, step] at collected
      | yielded value next =>
        cases rest : collectIteratorPrefix iterate n iter next with
        | error e => simp [collectIteratorPrefix, step, rest] at collected
        | ok xs =>
          simp [collectIteratorPrefix, step, rest] at collected
          subst values
          intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · subst x; exact law state _ next step
          · exact ih next xs rest x hx

/-- Registry entries for `base/generator.jl`. -/
def entries : List Entry := [
  { id := "generator-maps-finite-prefixes", juliaFile := "base/generator.jl",
    juliaFns := ["iterate(::Generator)"],
    statement := "Generator iteration maps every finite sequence of yielded values, preserves each state, and throws TypeError when a non-tuple result reaches the source assertion.",
    source := "Generator docstring and iterate body, base/generator.jl:3-10,44-50",
    status := .proven, prop := ``GeneratorIterationSemantics, thm := some ``generatorIterationSemantics_proven },
  { id := "generator-type-constructor-maps", juliaFile := "base/generator.jl",
    juliaFns := ["Generator(::Type{T}, iter::I)"],
    statement := "A Generator constructed from a type object applies that type to every yielded value, preserving iterator states and selecting the free-type-variable wrapper.",
    source := "Generator docstring and constructor, base/generator.jl:3-10,39-40",
    status := .proven, prop := ``GeneratorTypeMapsFinitePrefixes, thm := some ``generatorTypeMapsFinitePrefixes_proven },
  { id := "generator-multi-input-maps", juliaFile := "base/generator.jl",
    juliaFns := ["Generator(f, I1, I2, Is...)"],
    statement := "A multi-input Generator zips its iterators, splats the function over each zipped value, and yields the resulting values in order.",
    source := "Generator docstring and constructor, base/generator.jl:3-10,37",
    status := .proven, prop := ``GeneratorManyMapsFinitePrefixes, thm := some ``generatorManyMapsFinitePrefixes_proven },
  { id := "generator-type-multi-input-maps", juliaFile := "base/generator.jl",
    juliaFns := ["Generator(::Type{T}, I1, I2, Is...)"],
    statement := "A type-valued multi-input Generator applies the splatted type constructor to every tuple from zip, preserving the input order.",
    source := "Generator docstring and constructor, base/generator.jl:3-10,42",
    status := .proven, prop := ``GeneratorTypeManyMapsFinitePrefixes, thm := some ``generatorTypeManyMapsFinitePrefixes_proven },
  { id := "generator-last-matches-iteration", juliaFile := "base/generator.jl",
    juliaFns := ["last(::Generator)"],
    statement := "For a finite nonempty iterator, last(Generator) is the final value emitted by Generator iteration; when the iterator is empty, it preserves the underlying last error.",
    source := "Generator docstring and last method, base/generator.jl:3-10,57",
    status := .proven, prop := ``GeneratorLastMatchesFiniteIteration, thm := some ``generatorLastMatchesFiniteIteration_proven },
  { id := "generator-iterator-size-behavior", juliaFile := "base/generator.jl",
    juliaFns := ["IteratorSize(::Type)", "IteratorSize(::Type{Union{}}, slurp...)", "IteratorSize(::Type{Any})", "IteratorSize(::Type{<:Tuple})", "IteratorSize(::Type{<:AbstractArray{<:Any,N}})", "haslength(iter)", "length(::Generator)"],
    statement := "When a Generator has HasLength or HasShape, its length equals the number of values emitted; haslength accepts finite-length and shaped traits and rejects unknown and infinite traits.",
    source := "IteratorSize docstring and methods; Generator iteration and length, base/generator.jl:44-104",
    status := .proven, prop := ``IteratorSizeBehavior, thm := some ``iteratorSizeBehavior_proven },
  { id := "generator-iterator-eltype-behavior", juliaFile := "base/generator.jl",
    juliaFns := ["IteratorEltype(::Type)", "IteratorEltype(::Type{Union{}}, slurp...)"],
    statement := "For an iterator whose yielded values belong to its declared element type, every collected prefix preserves that membership; Union{} trait queries raise ArgumentError.",
    source := "IteratorEltype docstring and methods, base/generator.jl:110-131",
    status := .proven, prop := ``IteratorEltypeBehavior, thm := some ``iteratorEltypeBehavior_proven }
]

end JuliaLean.Proofs.base.generator
