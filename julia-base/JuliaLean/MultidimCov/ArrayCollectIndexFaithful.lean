import JuliaLean.MultidimCov.ArrayBasicsFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ArrayCollectIndexFaithful

open JuliaLean.Registry
open ArrayFaithfulCore
open ArrayBasicsFaithful

def m771 {I R : Type} (iteratorEltype : I → String) (iteratorSize : I → IteratorSize)
    (collectTyped : String → I → IteratorSize → R) (iterator : I) : R :=
  collectTyped (iteratorEltype iterator) iterator (iteratorSize iterator)
def P771 : Prop := ∀ {I R : Type} (iteratorEltype : I → String) (iteratorSize : I → IteratorSize)
    (collectTyped : String → I → IteratorSize → R) iterator,
  m771 iteratorEltype iteratorSize collectTyped iterator =
    collectTyped (iteratorEltype iterator) iterator (iteratorSize iterator)
theorem p771 : P771 := by simp [P771, m771]

def m773 (array : ArrayState α) : Result (ArrayState α) := m391 array
def P773 : Prop := ∀ {α : Type} (array : ArrayState α), m773 array = m391 array
theorem p773 : P773 := by simp [P773, m773]

def m775 {C I R : Type} (iteratorEltype : I → String) (iteratorSize : I → IteratorSize)
    (collectInto : C → I → String → IteratorSize → R) (container : C) (iterator : I) : R :=
  collectInto container iterator (iteratorEltype iterator) (iteratorSize iterator)
def P775 : Prop := ∀ {C I R : Type} (iteratorEltype : I → String) (iteratorSize : I → IteratorSize)
    (collectInto : C → I → String → IteratorSize → R) container iterator,
  m775 iteratorEltype iteratorSize collectInto container iterator =
    collectInto container iterator (iteratorEltype iterator) (iteratorSize iterator)
theorem p775 : P775 := by simp [P775, m775]

def m777 {C : Type} (convert : α → Result β) (similar : C → String → IteratorSize → ArrayState β)
    (container : C) (type : String) (values : List α) (size : IteratorSize) : Result (ArrayState β) := do
  let converted ← convertAll convert values
  pure { similar container type size with values := converted.map some }
def P777 : Prop := ∀ {C α β : Type} (convert : α → Result β)
    (similar : C → String → IteratorSize → ArrayState β) container type values size,
  m777 convert similar container type values size = do
    let converted ← convertAll convert values
    pure { similar container type size with values := converted.map some }
theorem p777 : P777 := by simp [P777, m777]

def m780 {C : Type} (convert : α → Result β) (similar : C → String → ArrayState β)
    (container : C) (type : String) (values : List α) : Result (ArrayState β) := do
  let converted ← convertAll convert values
  pure { similar container type with axes := oneToAxes [converted.length], values := converted.map some }
def P780 : Prop := ∀ {C α β : Type} (convert : α → Result β)
    (similar : C → String → ArrayState β) container type values,
  m780 convert similar container type values = do
    let converted ← convertAll convert values
    pure { similar container type with axes := oneToAxes [converted.length], values := converted.map some }
theorem p780 : P780 := by simp [P780, m780]

def m788 (array : ArrayState α) : Result (ArrayState α) := m391 array
def P788 : Prop := ∀ {α : Type} (array : ArrayState α), m788 array = m391 array
theorem p788 : P788 := by simp [P788, m788]
def m793 (axes : List (List Int)) (array : ArrayState α) : Result (ArrayState α) := do
  let copied ← m391 array
  pure { copied with axes }
def P793 : Prop := ∀ {α : Type} axes (array : ArrayState α), m793 axes array = do
  let copied ← m391 array
  pure { copied with axes }
theorem p793 : P793 := by simp [P793, m793]
def m798 := @m793
def P798 : Prop := ∀ {α : Type} axes (array : ArrayState α), m798 axes array = m793 axes array
theorem p798 : P798 := by simp [P798, m798]

def m805 {I S : Type} (iterate : I → Option (α × S)) (barrier : α → Bool)
    (iterator : I) : Result α :=
  match iterate iterator with
  | none => .error .argument
  | some (value, _) => if barrier value then .ok value else .error .argument
def P805 : Prop := ∀ {I S α : Type} (iterate : I → Option (α × S)) barrier iterator,
  m805 iterate barrier iterator = match iterate iterator with
    | none => .error .argument
    | some (value, _) => if barrier value then .ok value else .error .argument
theorem p805 : P805 := by
  unfold P805
  intro I S α iterate barrier iterator
  cases h : iterate iterator with
  | none => simp [m805, h]
  | some pair => cases pair; simp [m805, h]

inductive EltypeInfo where | known (name : String) | bottom | unknown deriving Repr, DecidableEq
def m821 (promote : String → String → String) (values : List EltypeInfo) : EltypeInfo :=
  values.foldl (fun current value => match current, value with
    | .bottom, other => other
    | other, .bottom => other
    | .known left, .known right => .known (promote left right)
    | _, _ => .unknown) .bottom
def P821 : Prop := ∀ promote values, m821 promote values =
  values.foldl (fun current value => match current, value with
    | .bottom, other => other
    | other, .bottom => other
    | .known left, .known right => .known (promote left right)
    | _, _ => .unknown) .bottom
theorem p821 : P821 := by simp [P821, m821]

def m833 (map : α → Result β) (values : List α) (size : IteratorSize)
    (defaultType : String) (typeOf : β → String) : Result (ArrayState β) :=
  match values with
  | [] => allocateFor defaultType size
  | first :: rest => do
      let firstMapped ← map first
      let restMapped ← convertAll map rest
      let output : ArrayState β := allocate (typeOf firstMapped) (oneToAxes [values.length])
      pure { output with
        values := (firstMapped :: restMapped).map some }
def P833 : Prop := ∀ {α β : Type} (map : α → Result β) values size defaultType typeOf,
  m833 map values size defaultType typeOf = match values with
    | [] => allocateFor defaultType size
    | first :: rest => do
        let firstMapped ← map first
        let restMapped ← convertAll map rest
        let output : ArrayState β := allocate (typeOf firstMapped) (oneToAxes [values.length])
        pure { output with
          values := (firstMapped :: restMapped).map some }
theorem p833 : P833 := by
  unfold P833
  intro α β map values size defaultType typeOf
  cases values <;> rfl

def m855 := @m833
def P855 : Prop := ∀ {α β : Type} (map : α → Result β) values size defaultType typeOf,
  m855 map values size defaultType typeOf = m833 map values size defaultType typeOf
theorem p855 : P855 := by simp [P855, m855]
def m858 := @m833
def P858 : Prop := ∀ {α β : Type} (map : α → Result β) values size defaultType typeOf,
  m858 map values size defaultType typeOf = m833 map values size defaultType typeOf
theorem p858 : P858 := by simp [P858, m858]

def m875 (dest : ArrayState α) (first : α) (rest : List α) : Result (ArrayState α) :=
  if dest.values.isEmpty then .error .bounds
  else .ok { dest with values := (first :: rest).map some }
def P875 : Prop := ∀ {α : Type} (dest : ArrayState α) first rest,
  m875 dest first rest = if dest.values.isEmpty then .error .bounds
    else .ok { dest with values := (first :: rest).map some }
theorem p875 : P875 := by simp [P875, m875]
def m881 := @m875
def P881 : Prop := ∀ {α : Type} (dest : ArrayState α) first rest, m881 dest first rest = m875 dest first rest
theorem p881 : P881 := by simp [P881, m881]

def m886 (convert : α → Result β) (dest : ArrayState β) (value : α) (index : Int) : Result (ArrayState β) := do
  setLinear dest index (← convert value)
def P886 : Prop := ∀ {α β : Type} (convert : α → Result β) dest value index,
  m886 convert dest value index = do setLinear dest index (← convert value)
theorem p886 : P886 := by simp [P886, m886]

def collectTo (convert : α → Result β) : ArrayState β → Nat → List α → Result (ArrayState β)
  | output, _, [] => .ok output
  | output, index, head :: tail => do
      let value ← convert head
      let written ← setLinear output (Int.ofNat index + 1) value
      collectTo convert written (index + 1) tail

def m895 := @collectTo
def P895 : Prop :=
  (∀ {α β : Type} (convert : α → Result β) (dest : ArrayState β) offset,
    m895 convert dest offset [] = .ok dest) ∧
  (∀ {α β : Type} (convert : α → Result β) (dest : ArrayState β) offset head tail,
    m895 convert dest offset (head :: tail) = do
      let value ← convert head
      let written ← setLinear dest (Int.ofNat offset + 1) value
      m895 convert written (offset + 1) tail)
theorem p895 : P895 := by simp [P895, m895, collectTo]

def m914 (dest : ArrayState α) (values : List α) : ArrayState α :=
  { dest with axes := oneToAxes [dest.values.length + values.length], values := dest.values ++ values.map some }
def P914 : Prop := ∀ {α : Type} (dest : ArrayState α) (values : List α),
  (m914 dest values).values = dest.values ++ values.map some
theorem p914 : P914 := by simp [P914, m914]

def m922 (typeOf : α → String) (dest : ArrayState α) (value : α) : ArrayState α :=
  { elementType := typeOf value, axes := oneToAxes [dest.values.length + 1],
    values := dest.values ++ [some value], id := dest.id + 1 }
def P922 : Prop := ∀ {α : Type} (typeOf : α → String) (dest : ArrayState α) (value : α),
  (m922 typeOf dest value).values = dest.values ++ [some value] ∧
  (m922 typeOf dest value).elementType = typeOf value
theorem p922 : P922 := by simp [P922, m922]

def m935 := @m914
def P935 : Prop := ∀ {α : Type} (dest : ArrayState α) (values : List α),
  (m935 dest values).values = dest.values ++ values.map some
theorem p935 : P935 := by simp [P935, m935, m914]

def cartesianLinear (dims : List Nat) (indices : List Int) : Result Int :=
  if indices.length ≠ dims.length || (List.zip indices dims).any (fun pair => pair.1 < 1 || pair.2 < pair.1)
  then .error .bounds
  else .ok (1 + (List.zip indices dims).foldr (fun pair state => (pair.1 - 1) + Int.ofNat pair.2 * state) 0)

def m974 (array : ArrayState α) (indices : List Int) : Result α := do
  getLinear array (← cartesianLinear (dimensions array) indices)
def P974 : Prop := ∀ {α : Type} (array : ArrayState α) indices, m974 array indices = do
  getLinear array (← cartesianLinear (dimensions array) indices)
theorem p974 : P974 := by simp [P974, m974]

def m981 (array : ArrayState α) (indices : List Int) : Result (ArrayState α) := do
  let values ← indices.mapM (getLinear array)
  pure (typedLiteral array.elementType values)
def P981 : Prop := ∀ {α : Type} (array : ArrayState α) indices, m981 array indices = do
  let values ← indices.mapM (getLinear array)
  pure (typedLiteral array.elementType values)
theorem p981 : P981 := by simp [P981, m981]

def m993 (array : ArrayState α) (mask : List Bool) : Result (ArrayState α) :=
  if mask.length ≠ array.values.length then .error .bounds
  else
    let selected := (array.values.zip mask).filterMap fun pair => if pair.2 then some pair.1 else none
    .ok { array with axes := oneToAxes [mask.count true], values := selected }
def P993 : Prop := ∀ {α : Type} (array : ArrayState α) mask, m993 array mask =
  if mask.length ≠ array.values.length then .error .bounds
  else
    let selected := (array.values.zip mask).filterMap fun pair => if pair.2 then some pair.1 else none
    .ok { array with axes := oneToAxes [mask.count true], values := selected }
theorem p993 : P993 := by simp [P993, m993]

def m995 (array : ArrayState α) : Result (ArrayState α) := m391 array
def P995 : Prop := ∀ {α : Type} (array : ArrayState α), m995 array = m391 array
theorem p995 : P995 := by simp [P995, m995]

def m1005 (array : ArrayState α) (indices : List Int) : Result (ArrayState α) := m981 array indices
def P1005 : Prop := ∀ {α : Type} (array : ArrayState α) indices, m1005 array indices = m981 array indices
theorem p1005 : P1005 := by simp [P1005, m1005]

def m1031 (convert : α → Result β) (array : ArrayState β) (value : α) (index : Int) : Result (ArrayState β) := do
  setLinear array index (← convert value)
def P1031 : Prop := ∀ {α β : Type} (convert : α → Result β)
    (array : ArrayState β) (value : α) index,
  m1031 convert array value index = do setLinear array index (← convert value)
theorem p1031 : P1031 := by simp [P1031, m1031]
def m1036 := @setLinear
def P1036 : Prop := ∀ {α : Type} (array : ArrayState α) index (value : α),
  m1036 array index value = setLinear array index value
theorem p1036 : P1036 := by simp [P1036, m1036]

def m1042 (convert : α → Result β) (array : ArrayState β) (value : α)
    (indices : List Int) : Result (ArrayState β) := do
  setLinear array (← cartesianLinear (dimensions array) indices) (← convert value)
def P1042 : Prop := ∀ {α β : Type} (convert : α → Result β)
    (array : ArrayState β) (value : α) indices,
  m1042 convert array value indices = do
    setLinear array (← cartesianLinear (dimensions array) indices) (← convert value)
theorem p1042 : P1042 := by simp [P1042, m1042]

def m1047 (array : ArrayState α) (value : α) (indices : List Int) : Result (ArrayState α) := do
  setLinear array (← cartesianLinear (dimensions array) indices) value
def P1047 : Prop := ∀ {α : Type} (array : ArrayState α) (value : α) indices,
  m1047 array value indices = do setLinear array (← cartesianLinear (dimensions array) indices) value
theorem p1047 : P1047 := by simp [P1047, m1047]

def m1055 := @setLinear
def P1055 : Prop := ∀ {α : Type} (array : ArrayState α) index (value : α),
  m1055 array index value = setLinear array index value
theorem p1055 : P1055 := by simp [P1055, m1055]
def m1057 := @setLinear
def P1057 : Prop := ∀ {α : Type} (array : ArrayState α) index (value : α),
  m1057 array index value = setLinear array index value
theorem p1057 : P1057 := by simp [P1057, m1057]
def m1059 := @m1031
def P1059 : Prop := ∀ {α β : Type} (convert : α → Result β)
    (array : ArrayState β) (value : α) index,
  m1059 convert array value index = m1031 convert array value index
theorem p1059 : P1059 := by simp [P1059, m1059]

def scatterAt (convert : α → Result β) (array : ArrayState β)
    (source : List α) (indices : List Int) : Result (ArrayState β) :=
  if source.length ≠ indices.length then .error .dimensionMismatch else
  let rec go : ArrayState β → List (α × Int) → Result (ArrayState β)
    | output, [] => .ok output
    | output, pair :: rest => do go (← setLinear output pair.2 (← convert pair.1)) rest
  go array (source.zip indices)
def m1063 := @scatterAt
def P1063 : Prop := ∀ {α β : Type} (convert : α → Result β)
    (array : ArrayState β) (source : List α) indices,
  m1063 convert array source indices = scatterAt convert array source indices
theorem p1063 : P1063 := by simp [P1063, m1063]
def m1078 (array source : ArrayState α) (indices : List Int) : Result (ArrayState α) := do
  scatterAt (fun value => .ok value) array (← assignedValues source) indices
def P1078 : Prop := ∀ {α : Type} (array source : ArrayState α) indices,
  m1078 array source indices = do scatterAt (fun value => .ok value) array (← assignedValues source) indices
theorem p1078 : P1078 := by simp [P1078, m1078]
def m1088 (array source : ArrayState α) : Result (ArrayState α) :=
  m1078 array source (List.range source.values.length |>.map (fun n => Int.ofNat n + 1))
def P1088 : Prop := ∀ {α : Type} (array source : ArrayState α),
  m1088 array source = m1078 array source ((List.range source.values.length).map fun n => Int.ofNat n + 1)
theorem p1088 : P1088 := by simp [P1088, m1088]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-array-faithful-{line}", juliaFile := "base/array.jl", juliaFns := [name],
    statement, source := s!"base/array.jl:{line}; collection and dense indexing source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 771 "collect(itr)" "Collection obtains iterator eltype and size before typed collection." ``P771 ``p771,
  entry 773 "collect(AbstractArray)" "Array collection returns a distinct copy with identical axes and values." ``P773 ``p773,
  entry 775 "collect_similar" "Similar collection preserves container, iterator, inferred type, and iterator size." ``P775 ``p775,
  entry 777 "_collect(HasEltype,sized)" "Sized collection allocates requested type and shape then converts every iterator value." ``P777 ``p777,
  entry 780 "_collect(HasEltype,unknown)" "Unknown-size collection grows a typed vector and preserves iteration order." ``P780 ``p780,
  entry 788 "_collect_indices(())" "Zero-dimensional index collection copies every assigned value." ``P788 ``p788,
  entry 793 "_collect_indices(OneTo axes)" "OneTo collection allocates matching axes and copies every source value." ``P793 ``p793,
  entry 798 "_collect_indices(offset axes)" "General-axis collection allocates exact axes and copies by Cartesian iteration." ``P798 ``p798,
  entry 805 "_iterator_upper_bound" "Upper-bound probing performs iteration and barrier checks on the actual iterator outcome." ``P805 ``p805,
  entry 821 "default_eltype" "Default eltype folds every inferred iterator type with bottom and unknown handling." ``P821 ``p821,
  entry 833 "collect(::Generator)" "Generator collection handles empty input or maps the first value before all remaining values." ``P833 ``p833,
  entry 855 "_collect(EltypeUnknown,unknown)" "Unknown generator collection maps and grows every value in order." ``P855 ``p855,
  entry 858 "_collect(EltypeUnknown,sized)" "Sized unknown-eltype collection seeds from the first mapped value and widens as needed." ``P858 ``p858,
  entry 875 "collect_to_with_first!(AbstractArray)" "The first mapped value and every remaining value fill the destination in iterator order." ``P875 ``p875,
  entry 881 "collect_to_with_first!(generic)" "The generic route preserves the first value and every iterator value in order." ``P881 ``p881,
  entry 886 "setindex_widen_up_to" "Widening converts the element and writes it at the requested destination index." ``P886 ``p886,
  entry 895 "collect_to!" "Collection threads iterator order, destination offset, conversion failures, and each write." ``P895 ``p895,
  entry 914 "grow_to!(dest,itr)" "Growth appends every iterator value and updates the vector length." ``P914 ``p914,
  entry 922 "push_widen" "Widening allocates the promoted element type, copies existing values, and appends the new value." ``P922 ``p922,
  entry 935 "grow_to!(dest,itr,state)" "Stateful growth appends every remaining value in order." ``P935 ``p935,
  entry 974 "getindex(Array,Int...)" "Cartesian dense indexing checks and linearizes every coordinate before reading storage." ``P974 ``p974,
  entry 981 "getindex(Array,unit range)" "Range indexing checks every requested index and returns a typed vector in range order." ``P981 ``p981,
  entry 993 "getindex(Array,Bool range)" "Logical range indexing validates mask length and returns selected values." ``P993 ``p993,
  entry 995 "getindex(Array,Colon)" "Colon indexing returns a distinct typed copy of all assigned values." ``P995 ``p995,
  entry 1005 "getindex(Array,AbstractRange{Int})" "Integer range indexing preserves the requested range order and source element type." ``P1005 ``p1005,
  entry 1031 "setindex!(Array,x,Int)" "Scalar assignment converts before checked storage mutation." ``P1031 ``p1031,
  entry 1036 "_setindex!(Array,x,Int)" "Typed scalar assignment performs checked storage mutation and returns the array." ``P1036 ``p1036,
  entry 1042 "setindex!(Array,x,Int...)" "Cartesian assignment converts, checks and linearizes coordinates, then mutates storage." ``P1042 ``p1042,
  entry 1047 "_setindex!(Array,x,Int...)" "Typed Cartesian assignment linearizes checked coordinates and writes storage." ``P1047 ``p1047,
  entry 1055 "__safe_setindex!(Vector{Any})" "The Any specialization writes the exact polymorphic value at the requested slot." ``P1055 ``p1055,
  entry 1057 "__safe_setindex!(Vector{T},x::T)" "The typed specialization writes the value without conversion." ``P1057 ``p1057,
  entry 1059 "__safe_setindex!(Vector{T},x)" "The fallback converts before delegating to typed storage." ``P1059 ``p1059,
  entry 1063 "setindex!(Array,X,index vector)" "Indexed assignment checks equal lengths then converts and writes each value in order." ``P1063 ``p1063,
  entry 1078 "setindex!(Array,Array,unit range)" "Same-type range assignment copies every assigned source value to its selected destination." ``P1078 ``p1078,
  entry 1088 "setindex!(Array,Array,Colon)" "Colon assignment copies every assigned source value across the full destination." ``P1088 ``p1088
]

end JuliaLean.MultidimCov.ArrayCollectIndexFaithful
