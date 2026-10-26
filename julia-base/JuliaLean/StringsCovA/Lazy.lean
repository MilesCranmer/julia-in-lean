import JuliaLean.Core

/-!
Models for `base/strings/lazy.jl` at Julia `bbfa0ce4150`.  Printed parts are
represented by their resulting byte strings; this keeps the model focused on
the lazy cache and the `AbstractString` forwarding methods.
-/

namespace JuliaLean.StringsCovA.Lazy

structure LazyString where
  parts : List (List UInt8)
  compact : Bool
  cached : Option (List UInt8)

/-- `_LazyString(parts, str)`; `base/strings/lazy.jl:41`. -/
def privateCtor (parts : List (List UInt8)) (str : Option (List UInt8)) : LazyString :=
  ⟨parts, false, str⟩

/-- `LazyString(args...; compact)`; `base/strings/lazy.jl:42`. -/
def ctor (parts : List (List UInt8)) (compact : Bool := false) : LazyString :=
  ⟨parts, compact, none⟩

/-- The parts assembled by `@lazy_str`; `base/strings/lazy.jl:73-87`. -/
def lazyMacro (literalAndInterpolatedParts : List (List UInt8)) (compactFlag : Bool) : LazyString :=
  ctor literalAndInterpolatedParts compactFlag

/-- The bytes printed by the delayed interpolation. -/
def render (parts : List (List UInt8)) : List UInt8 := parts.flatten

/-- `String(l::LazyString)`; `base/strings/lazy.jl:89-101`. -/
def materialize (l : LazyString) : List UInt8 :=
  l.cached.getD (render l.parts)

/-- `hash(s::LazyString, h)`; `base/strings/lazy.jl:103`. -/
def hash (H : List UInt8 → UInt64 → UInt64) (s : LazyString) (h : UInt64) : UInt64 :=
  H (materialize s) h

/-- `lastindex(s::LazyString)`; `base/strings/lazy.jl:104`. -/
def lastindex (stringLastindex : List UInt8 → Int) (s : LazyString) :=
  stringLastindex (materialize s)

/-- `iterate(s::LazyString)`; `base/strings/lazy.jl:105`. -/
def iterate0 {α : Type} (stringIterate : List UInt8 → Option α) (s : LazyString) :=
  stringIterate (materialize s)

/-- `iterate(s::LazyString, i)`; `base/strings/lazy.jl:106`. -/
def iterateAt {α : Type} (stringIterate : List UInt8 → Int → Option α)
    (s : LazyString) (i : Int) := stringIterate (materialize s) i

/-- `isequal(a::LazyString, b::LazyString)`; `base/strings/lazy.jl:107`. -/
def isequal (a b : LazyString) : Bool := materialize a == materialize b

/-- `==(a::LazyString, b::LazyString)`; `base/strings/lazy.jl:108`. -/
def eq (a b : LazyString) : Bool := materialize a == materialize b

/-- `ncodeunits(s::LazyString)`; `base/strings/lazy.jl:109`. -/
def ncodeunits (s : LazyString) : Nat := (materialize s).length

/-- `codeunit(s::LazyString)`; `base/strings/lazy.jl:110`. -/
def codeunitType (_s : LazyString) : Nat := 8

/-- `codeunit(s::LazyString, i)`; `base/strings/lazy.jl:111`. -/
def codeunitAt (s : LazyString) (i : Int) : Jl UInt8 :=
  if 1 ≤ i ∧ i ≤ (materialize s).length then
    .ok ((materialize s).getD (i.toNat - 1) 0)
  else .error .boundsError

/-- `codeunits(s::LazyString)`; `base/strings/lazy.jl:112`. -/
def codeunits (s : LazyString) : List UInt8 := materialize s

/-- `isvalid(s::LazyString, i)`; `base/strings/lazy.jl:113`. -/
def isvalid (stringIsvalid : List UInt8 → Int → Bool) (s : LazyString) (i : Int) : Bool :=
  stringIsvalid (materialize s) i

def ConstructionContract : Prop :=
  (∀ parts str, privateCtor parts str = ⟨parts, false, str⟩) ∧
  (∀ parts compact, ctor parts compact = ⟨parts, compact, none⟩) ∧
  (∀ parts compact, lazyMacro parts compact = ctor parts compact)

theorem constructionContract : ConstructionContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def MaterializationContract : Prop :=
  (∀ parts compact, materialize (ctor parts compact) = render parts) ∧
  (∀ parts compact cached, materialize ⟨parts, compact, some cached⟩ = cached)

theorem materializationContract : MaterializationContract := by
  constructor <;> intros <;> rfl

def ForwardingContract : Prop :=
  (∀ H s h, hash H s h = H (materialize s) h) ∧
  (∀ stringLastindex s, lastindex stringLastindex s = stringLastindex (materialize s)) ∧
  (∀ (α : Type) (stringIterate : List UInt8 → Option α) s,
    iterate0 stringIterate s = stringIterate (materialize s)) ∧
  (∀ (α : Type) (stringIterate : List UInt8 → Int → Option α) s i,
    iterateAt stringIterate s i = stringIterate (materialize s) i) ∧
  (∀ a b, isequal a b = (materialize a == materialize b)) ∧
  (∀ a b, eq a b = (materialize a == materialize b)) ∧
  (∀ s, ncodeunits s = (materialize s).length) ∧
  (∀ s, codeunitType s = 8) ∧
  (∀ s i, codeunitAt s i =
    if 1 ≤ i ∧ i ≤ (materialize s).length then
      .ok ((materialize s).getD (i.toNat - 1) 0)
    else .error .boundsError) ∧
  (∀ s, codeunits s = materialize s) ∧
  (∀ stringIsvalid s i, isvalid stringIsvalid s i = stringIsvalid (materialize s) i)

theorem forwardingContract : ForwardingContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.Lazy
