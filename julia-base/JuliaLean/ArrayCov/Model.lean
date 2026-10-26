import JuliaLean.Core

namespace JuliaLean.ArrayCov

inductive IntegerKind where
  | int | other
  deriving Repr, DecidableEq

/-- `wrap(Array, m::Memory, l::Integer)`, `base/array.jl:3270-3274`.
The source converts `l` to `dims`, calls `_wrap(memoryref(m), (l,))` with the
original integer type, and constructs the array only if that call returns. -/
def wrapMemory (kind : IntegerKind) (length capacity : Nat) : Jl Nat :=
  let _dims := length
  match kind with
  | .other => .error (.methodError "_wrap")
  | .int =>
      if length > capacity then .error .boundsError
      else .ok length

def WrapMemoryIntegerSpec : Prop :=
  ∀ (kind : IntegerKind) (length capacity : Nat), length ≤ capacity →
    wrapMemory kind length capacity = .ok length

theorem wrapMemoryIntegerSpec_refuted : ¬ WrapMemoryIntegerSpec := by
  intro h
  have bad := h .other 2 3 (by decide)
  simp [wrapMemory] at bad

/-- `iterate(R::ReshapedArrayIterator, i...)`, `base/reshapedarray.jl:31-34`.
The body calls the parent iterator and destructures its result immediately;
destructuring `nothing` raises the modelled `MethodError`. -/
def reshapedIteratorStep
    (parentIterate : Nat → Option (Nat × Nat)) (state : Nat) :
    Jl (Option (Nat × Nat)) :=
  match parentIterate state with
  | some (item, nextState) => .ok (some (item, nextState))
  | none => .error (.methodError "iterate")

def ReshapedIteratorProtocol : Prop :=
  ∀ (parentIterate : Nat → Option (Nat × Nat)) (state : Nat),
    parentIterate state = none → reshapedIteratorStep parentIterate state = .ok none

theorem reshapedIteratorProtocol_refuted : ¬ ReshapedIteratorProtocol := by
  intro h
  let exhausted : Nat → Option (Nat × Nat) := fun _ => none
  have bad := h exhausted 0 rfl
  simp [reshapedIteratorStep, exhausted] at bad

inductive FloatKey where
  | negZero | posZero | nan | finite (value : Int)
  deriving Repr, DecidableEq

/-- Julia `==` on the distinguished floating-point cases used by the property. -/
def memberEq : FloatKey → FloatKey → Bool
  | .negZero, .posZero | .posZero, .negZero => true
  | .nan, _ | _, .nan => false
  | x, y => x == y

/-- Julia `isequal`, which is the equality used by Dict keys. -/
def keyEqual : FloatKey → FloatKey → Bool
  | .negZero, .negZero | .posZero, .posZero | .nan, .nan => true
  | .finite x, .finite y => x == y
  | _, _ => false

def firstIndexBy (eq : FloatKey → FloatKey → Bool) (needle : FloatKey) :
    List FloatKey → Nat → Option Nat
  | [], _ => none
  | value :: rest, index =>
      if eq needle value then some index else firstIndexBy eq needle rest (index + 1)

/-- `indexin(a, b::AbstractArray)`, `base/array.jl:2892-2901`.
The first loop inserts each `b` value with `get!`, retaining its first index;
the comprehension then performs Dict lookups for the values from `a`. -/
def indexinModel (a b : List FloatKey) : List (Option Nat) :=
  a.map fun value => firstIndexBy keyEqual value b 1

def membershipIndex (a b : List FloatKey) : List (Option Nat) :=
  a.map fun value => firstIndexBy memberEq value b 1

def IndexinMembershipSpec : Prop :=
  ∀ (a b : List FloatKey), indexinModel a b = membershipIndex a b

theorem indexinMembershipSpec_refuted : ¬ IndexinMembershipSpec := by
  intro h
  have bad := h [.negZero] [.posZero]
  simp [indexinModel, membershipIndex, firstIndexBy, keyEqual, memberEq] at bad

end JuliaLean.ArrayCov
