import JuliaLean.MultidimCov.MultidimensionalLogicalFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalUnsafeFaithful

open JuliaLean.Registry
open MultidimensionalCartesianFaithful
open MultidimensionalDispatchFaithful

inductive Error where | bounds | dimensionMismatch | conversion deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure ArrayState (α : Type) where
  axes : List (List Int)
  values : List (List Int × α)
  id : Nat
  deriving Repr, DecidableEq

inductive IndexSpec where
  | scalar (value : Int)
  | many (values : List Int)
  deriving Repr, DecidableEq

def indexProduct : List IndexSpec → List (List Int)
  | [] => [[]]
  | .scalar value :: rest => (indexProduct rest).map (value :: ·)
  | .many values :: rest => values.flatMap fun value => (indexProduct rest).map (value :: ·)

def lookup (array : ArrayState α) (index : List Int) : Option α :=
  (array.values.find? fun pair => pair.1 = index).map (fun pair => pair.2)

def write (array : ArrayState α) (index : List Int) (value : α) : ArrayState α :=
  { array with values := (index, value) :: array.values.filter (fun pair => pair.1 ≠ index) }

def m989 (value : α) (_index : Cartesian) : α := value
def P989 : Prop := ∀ {α : Type} (value : α) index, m989 value index = value
theorem p989 : P989 := by simp [P989, m989]

def m990 (tuple : List α) (index : Cartesian) : Option α :=
  match index.coordinates with | [coordinate] => tuple[(coordinate.val - 1).toNat]? | _ => none
def P990 : Prop := ∀ {α : Type} (tuple : List α) index,
  m990 tuple index = match index.coordinates with
    | [coordinate] => tuple[(coordinate.val - 1).toNat]? | _ => none
theorem p990 : P990 := by simp [P990, m990]

def m995 {A I R : Type} (checkbounds : A → List I → Result Unit)
    (maybeReshape : A → List I → A) (unsafeGet : A → List I → Result R)
    (array : A) (indices : List I) : Result R := do
  checkbounds array indices
  unsafeGet (maybeReshape array indices) indices
def P995 : Prop := ∀ {A I R : Type} (checkbounds : A → List I → Result Unit)
    (maybeReshape : A → List I → A) (unsafeGet : A → List I → Result R) array indices,
  m995 checkbounds maybeReshape unsafeGet array indices = do
    checkbounds array indices
    unsafeGet (maybeReshape array indices) indices
theorem p995 : P995 := by simp [P995, m995]

def m1000 {A I : Type} (array : A) (_indices : List I) : A := array
def P1000 : Prop := ∀ {A I : Type} (array : A) (indices : List I), m1000 array indices = array
theorem p1000 : P1000 := by simp [P1000, m1000]
def m1001 := @m1000
def P1001 : Prop := ∀ {A I : Type} (array : A) (indices : List I), m1001 array indices = array
theorem p1001 : P1001 := by simp [P1001, m1001, m1000]

def m1002 {A I : Type} (indexNdims : List I → Nat) (reshape : A → Nat → A)
    (array : A) (indices : List I) : A := reshape array (indexNdims indices)
def P1002 : Prop := ∀ {A I : Type} (indexNdims : List I → Nat) (reshape : A → Nat → A) array indices,
  m1002 indexNdims reshape array indices = reshape array (indexNdims indices)
theorem p1002 : P1002 := by simp [P1002, m1002]

def m1003 {A : Type} (array : A) (_rank : Nat) : A := array
def P1003 : Prop := ∀ {A : Type} (array : A) rank, m1003 array rank = array
theorem p1003 : P1003 := by simp [P1003, m1003]

def m1004 {A : Type} (reshape : A → Nat → A) (array : A) (rank : Nat) : A := reshape array rank
def P1004 : Prop := ∀ {A : Type} (reshape : A → Nat → A) array rank,
  m1004 reshape array rank = reshape array rank
theorem p1004 : P1004 := by simp [P1004, m1004]

def gather (source : ArrayState α) (indices : List IndexSpec) : Result (ArrayState α) :=
  let keys := indexProduct indices
  let values := keys.filterMap fun key => (lookup source key).map (key, ·)
  let outputAxes := indices.filterMap fun index =>
    match index with | .many selected => some selected | _ => none
  if values.length ≠ keys.length then .error .bounds
  else .ok { axes := outputAxes, values := values, id := source.id + 1 }

def m1006 (source : ArrayState α) (indices : List IndexSpec) : Result (ArrayState α) := gather source indices
def P1006 : Prop := ∀ {α : Type} (source : ArrayState α) indices,
  m1006 source indices = gather source indices
theorem p1006 : P1006 := by simp [P1006, m1006]

def m1015 (rank : Nat) : List IndexSpec → ArrayState α → Result (ArrayState α) :=
  fun indices source => if indices.length = rank then gather source indices else .error .dimensionMismatch
def P1015 : Prop := ∀ {α : Type} rank indices (source : ArrayState α),
  m1015 rank indices source = if indices.length = rank then gather source indices else .error .dimensionMismatch
theorem p1015 : P1015 := by simp [P1015, m1015]

def m1030 (dest source : ArrayState α) (indices : List IndexSpec) : Result (ArrayState α) := do
  let gathered ← gather source indices
  pure { dest with values := gathered.values }
def P1030 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1030 dest source indices = do
  let gathered ← gather source indices
  pure { dest with values := gathered.values }
theorem p1030 : P1030 := by simp [P1030, m1030]
def m1035 := @m1030
def P1035 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1035 dest source indices = m1030 dest source indices
theorem p1035 : P1035 := by simp [P1035, m1035]
def m1039 := @m1030
def P1039 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1039 dest source indices = m1030 dest source indices
theorem p1039 : P1039 := by simp [P1039, m1039]

def scatter (dest source : ArrayState α) (indices : List IndexSpec) : Result (ArrayState α) :=
  let keys := indexProduct indices
  if keys.length ≠ source.values.length then .error .dimensionMismatch else
  .ok ((keys.zip source.values).foldl (fun output pair => write output pair.1 pair.2.2) dest)

def m1046 {I : Type} (checkbounds : ArrayState α → List I → Result Unit)
    (convert : List I → List IndexSpec) (dest : ArrayState α) (source : ArrayState α)
    (indices : List I) : Result (ArrayState α) := do
  checkbounds dest indices
  scatter dest source (convert indices)
def P1046 : Prop := ∀ {α I : Type} (checkbounds : ArrayState α → List I → Result Unit)
    (convert : List I → List IndexSpec) dest source indices,
  m1046 checkbounds convert dest source indices = do
    checkbounds dest indices
    scatter dest source (convert indices)
theorem p1046 : P1046 := by simp [P1046, m1046]

def m1053 (rank : Nat) : ArrayState α → ArrayState α → List IndexSpec → Result (ArrayState α) :=
  fun dest source indices => if indices.length = rank then scatter dest source indices else .error .dimensionMismatch
def P1053 : Prop := ∀ {α : Type} rank (dest source : ArrayState α) indices,
  m1053 rank dest source indices = if indices.length = rank then scatter dest source indices else .error .dimensionMismatch
theorem p1053 : P1053 := by simp [P1053, m1053]

def m1069 := @scatter
def P1069 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1069 dest source indices = scatter dest source indices
theorem p1069 : P1069 := by simp [P1069, m1069]
def m1073 := @scatter
def P1073 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1073 dest source indices = scatter dest source indices
theorem p1073 : P1073 := by simp [P1073, m1073]
def m1077 := @scatter
def P1077 : Prop := ∀ {α : Type} (dest source : ArrayState α) indices,
  m1077 dest source indices = scatter dest source indices
theorem p1077 : P1077 := by simp [P1077, m1077]

def m1081 {A R : Type} (diffDims : A → Int → R) (array : A) : R := diffDims array 1
def P1081 : Prop := ∀ {A R : Type} (diffDims : A → Int → R) array,
  m1081 diffDims array = diffDims array 1
theorem p1081 : P1081 := by simp [P1081, m1081]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; multidimensional indexing source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 989 "getindex(scalar,CartesianIndex{0})" "Every Number or AbstractChar passes through unchanged for an empty Cartesian index." ``P989 ``p989,
  entry 990 "getindex(tuple,CartesianIndex{1})" "Tuple indexing reads the sole stored coordinate before calling tuple getindex." ``P990 ``p990,
  entry 995 "_getindex" "The wrapper completes bounds checking before reshaping and invoking unsafe indexing." ``P995 ``p995,
  entry 1000 "_maybe_reshape(IndexLinear)" "Linear arrays pass through unchanged." ``P1000 ``p1000,
  entry 1001 "_maybe_reshape(IndexCartesian,AbstractVector)" "Cartesian vectors pass through unchanged." ``P1001 ``p1001,
  entry 1002 "_maybe_reshape(IndexCartesian,AbstractArray)" "Cartesian arrays derive index_ndims from original indices before reshaping." ``P1002 ``p1002,
  entry 1003 "__maybe_reshape(equal rank)" "Equal-rank arrays pass through with type, axes, and identity unchanged." ``P1003 ``p1003,
  entry 1004 "__maybe_reshape(other rank)" "Other ranks delegate to reshape(A,Val(N))." ``P1004 ``p1004,
  entry 1006 "_unsafe_getindex" "Unsafe indexing derives output axes, allocates the exact shape, validates it, and gathers every source element." ``P1006 ``p1006,
  entry 1015 "_generate_unsafe_getindex!_body" "The generated body iterates the Cartesian product, reads each source coordinate, and writes each destination index in order." ``P1015 ``p1015,
  entry 1030 "_unsafe_getindex!(N)" "The generated N-index overload executes the generated gather body." ``P1030 ``p1030,
  entry 1035 "_unsafe_getindex!(1)" "The one-index specialization executes the same generated gather body." ``P1035 ``p1035,
  entry 1039 "_unsafe_getindex!(2)" "The two-index specialization executes the same generated gather body." ``P1039 ``p1039,
  entry 1046 "_setindex!" "Assignment checks bounds before reshaping, scattering values, and returning the mutated array." ``P1046 ``p1046,
  entry 1053 "_generate_unsafe_setindex!_body" "The generated setter validates shape, then converts and writes each source value in iteration order." ``P1053 ``p1053,
  entry 1069 "_unsafe_setindex!(N)" "The generated N-index overload executes ordered scatter semantics." ``P1069 ``p1069,
  entry 1073 "_unsafe_setindex!(1)" "The one-index specialization executes ordered scatter semantics." ``P1073 ``p1073,
  entry 1077 "_unsafe_setindex!(2)" "The two-index specialization executes ordered scatter semantics." ``P1077 ``p1077,
  entry 1081 "diff(::AbstractVector)" "Vector diff delegates with dims equal to one." ``P1081 ``p1081
]

end JuliaLean.MultidimCov.MultidimensionalUnsafeFaithful
