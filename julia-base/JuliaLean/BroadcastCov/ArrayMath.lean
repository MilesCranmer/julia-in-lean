import JuliaLean.Core
import JuliaLean.Multidim.Model

/-!
Executable models for the methods in `base/abstractarraymath.jl` that are not
already represented by the Multidim and ArrayOps areas. Arrays are represented
by their shape and column-major payload. The dimension-changing methods only
change the shape and retain the payload, matching Julia's `reshape` calls.
-/

namespace JuliaLean.BroadcastCov.ArrayMath

inductive ArrayError where
  | argumentError
  deriving Repr, DecidableEq

abbrev R (α : Type) := Except ArrayError α

abbrev I64 := JInt .i64
def i64 (x : Int) : I64 := JInt.lit .i64 x

structure ArrayModel where
  shape : List Nat
  data : List (I64 × I64)
  deriving Repr, DecidableEq

/-- `isreal(x::AbstractArray)`, line 5. -/
def isrealArray (x : ArrayModel) : Bool := x.data.all (fun z => z.2 == i64 0)

/-- `iszero(x::AbstractArray)`, line 6. -/
def iszeroArray (x : ArrayModel) : Bool := x.data.all (fun z => z == (i64 0, i64 0))

/-- `isreal(x::AbstractArray{<:Real})`, line 7. -/
def isrealRealArray (_ : List Int) : Bool := true

/-- `vec(a::AbstractArray) = reshape(a, length(a))`, line 41. -/
def vecArray (x : ArrayModel) : ArrayModel := { x with shape := [x.data.length] }

/-- `vec(a::AbstractVector) = a`, line 42. -/
def vecVector (x : ArrayModel) : ArrayModel := x

/-- `_sub`, lines 44-46: remove one head from `t` for every head of `s`. -/
def subTuple : List Nat → List Nat → List Nat
  | t, [] => t
  | [], _ :: _ => []
  | _ :: t, _ :: s => subTuple t s

def noDuplicates : List Nat → Bool
  | [] => true
  | d :: ds => !ds.contains d && noDuplicates ds

def eraseDims : List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | n :: ns, dims, d =>
      if dims.contains d then eraseDims ns dims (d + 1)
      else n :: eraseDims ns dims (d + 1)

/-- `_dropdims`, lines 86-103, including range, singleton and uniqueness checks. -/
def dropDims (x : ArrayModel) (dims : List Nat) : R ArrayModel :=
  if dims.all (fun d => decide (1 ≤ d ∧ d ≤ x.shape.length)) &&
      dims.all (fun d => x.shape.getD (d - 1) 0 == 1) && noDuplicates dims then
    .ok { x with shape := eraseDims x.shape dims 1 }
  else .error .argumentError

/-- The scalar-dimension `_dropdims` wrapper at line 104. -/
def dropDim (x : ArrayModel) (dim : Nat) : R ArrayModel := dropDims x [dim]

def buildInserted (shape dims : List Nat) (total source : Nat) : List Nat :=
  match total with
  | 0 => []
  | total + 1 =>
      let d := shape.length + dims.length - total
      if dims.contains d then 1 :: buildInserted shape dims total source
      else shape.getD source 1 :: buildInserted shape dims total (source + 1)

/-- `_insertdims`, lines 147-165, including both bounds and the uniqueness check. -/
def insertDims (x : ArrayModel) (dims : List Nat) : R ArrayModel :=
  let total := x.shape.length + dims.length
  if dims.all (fun d => decide (1 ≤ d ∧ d ≤ total)) && noDuplicates dims then
    .ok { x with shape := buildInserted x.shape dims total 0 }
  else .error .argumentError

/-- The scalar-dimension `_insertdims` wrapper at line 166. -/
def insertDim (x : ArrayModel) (dim : Nat) : R ArrayModel := insertDims x [dim]

/-- `conj!` for numeric arrays and `conj` for general arrays, lines 194 and 220. -/
def conjugate (x : ArrayModel) : ArrayModel :=
  { x with data := x.data.map (fun z => (z.1, -z.2)) }

/-- The real-array identity overloads of `conj!`, `conj`, `real`, unary `+` and
unary `*`, lines 195, 221, 246, 295 and 296. -/
def identityArray (x : ArrayModel) : ArrayModel := x

/-- Recursive `conj!` at line 196, represented after recursion has reached the
numeric leaves. -/
def conjugateNested (xs : List ArrayModel) : List ArrayModel := xs.map conjugate

/-- `real(A)`, line 245. -/
def realArray (x : ArrayModel) : ArrayModel :=
  { x with data := x.data.map (fun z => (z.1, i64 0)) }

/-- `imag(A)`, lines 269-270. -/
def imagArray (x : ArrayModel) : ArrayModel :=
  { x with data := x.data.map (fun z => (z.2, i64 0)) }

/-- Unary array negation at line 293. -/
def negateArray (x : ArrayModel) : ArrayModel :=
  { x with data := x.data.map (fun z => (-z.1, -z.2)) }

/-- The `shiftamt::Real` wrapper at lines 335-337 after `Integer(shiftamt)` has
succeeded. -/
def circshiftReal (shape : List Nat) (data : List Int → Int) (shift : Int) :=
  JuliaLean.Multidim.circshift shape data [shift]

/-- The `DimsInteger` and general tuple wrappers at lines 338 and 411-413. -/
def circshiftDims (shape : List Nat) (data : List Int → Int) (shifts : List Int) :=
  JuliaLean.Multidim.circshift shape data shifts

/-- `to_tuple`, lines 494-496. The iterable overload receives its collected values. -/
def toTuple (xs : List Int) : List Int := xs
def toTupleInteger (x : Int) : List Int := [x]

/-- Both `pad` overloads, lines 498-505. -/
def pad2 (a b : List Int) : List Int × List Int :=
  let n := max a.length b.length
  (JuliaLean.Multidim.padOnes a n, JuliaLean.Multidim.padOnes b n)

def pad3 (a b c : List Int) : List Int × List Int × List Int :=
  let n := max a.length (max b.length c.length)
  (JuliaLean.Multidim.padOnes a n, JuliaLean.Multidim.padOnes b n,
    JuliaLean.Multidim.padOnes c n)

/-- `repeat_inner_outer`, lines 554-557, at the shape level. -/
def repeatInnerOuter (shape : List Int) (inner outer : Option (List Int)) :=
  JuliaLean.Multidim.repeatSize shape inner outer

def BasicArrayMethods : Prop :=
  (∀ x, isrealArray x = x.data.all (fun z => z.2 == i64 0)) ∧
  (∀ x, iszeroArray x = x.data.all (fun z => z == (i64 0, i64 0))) ∧
  (∀ xs, isrealRealArray xs = true) ∧
  (∀ x, (vecArray x).shape = [x.data.length] ∧ (vecArray x).data = x.data) ∧
  (∀ x, vecVector x = x) ∧
  (∀ t s, subTuple t s = t.drop s.length) ∧
  (∀ x, (conjugate x).data = x.data.map (fun z => (z.1, -z.2))) ∧
  (∀ x, identityArray x = x) ∧
  (∀ xs, conjugateNested xs = xs.map conjugate) ∧
  (∀ x, (realArray x).data = x.data.map (fun z => (z.1, i64 0))) ∧
  (∀ x, (imagArray x).data = x.data.map (fun z => (z.2, i64 0))) ∧
  (∀ x, (negateArray x).data = x.data.map (fun z => (-z.1, -z.2)))

theorem basicArrayMethods : BasicArrayMethods := by
  constructor
  · intro x; rfl
  constructor
  · intro x; rfl
  constructor
  · intro xs; rfl
  constructor
  · intro x; exact ⟨rfl, rfl⟩
  constructor
  · intro x; rfl
  constructor
  · intro t s
    induction s generalizing t with
    | nil => simp [subTuple]
    | cons _ s ih =>
      cases t <;> simp [subTuple, ih]
  constructor
  · intro x; rfl
  constructor
  · intro x; rfl
  constructor
  · intro xs; rfl
  constructor
  · intro x; rfl
  constructor
  · intro x; rfl
  · intro x; rfl

def DimensionMethods : Prop :=
  (∀ x dims,
    dropDims x dims =
      if dims.all (fun d => decide (1 ≤ d ∧ d ≤ x.shape.length)) &&
          dims.all (fun d => x.shape.getD (d - 1) 0 == 1) && noDuplicates dims then
        .ok { x with shape := eraseDims x.shape dims 1 }
      else .error .argumentError) ∧
  (∀ x dim, dropDim x dim = dropDims x [dim]) ∧
  (∀ x dims,
    insertDims x dims =
      let total := x.shape.length + dims.length
      if dims.all (fun d => decide (1 ≤ d ∧ d ≤ total)) && noDuplicates dims then
        .ok { x with shape := buildInserted x.shape dims total 0 }
      else .error .argumentError) ∧
  (∀ x dim, insertDim x dim = insertDims x [dim])

theorem dimensionMethods : DimensionMethods := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def WrapperMethods : Prop :=
  (∀ shape data shift,
    circshiftReal shape data shift = JuliaLean.Multidim.circshift shape data [shift]) ∧
  (∀ shape data shifts,
    circshiftDims shape data shifts = JuliaLean.Multidim.circshift shape data shifts) ∧
  (∀ xs, toTuple xs = xs) ∧
  (∀ x, toTupleInteger x = [x]) ∧
  (∀ shape inner outer,
    repeatInnerOuter shape inner outer = JuliaLean.Multidim.repeatSize shape inner outer)

theorem wrapperMethods : WrapperMethods := by
  exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl⟩

end JuliaLean.BroadcastCov.ArrayMath
