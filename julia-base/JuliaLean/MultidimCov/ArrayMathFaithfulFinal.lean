import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ArrayMathFaithfulFinal

open JuliaLean.Registry

inductive Error where
  | argument | bounds | operation
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

def longerShape (left right : List Nat) : List Nat :=
  if left.length > right.length then left else right

def highestRankShape : List (List Nat) → List Nat
  | [] => []
  | shape :: shapes => shapes.foldl longerShape shape

/-- `base/arraymath.jl:16-25`. Every `size` call used by mapreduce precedes
shape selection; the later pass uses `ndims`, reshapes only rank mismatches,
and finally calls `map`. -/
def m16 (size : A → List Nat) (ndims : A → Nat)
    (reshape : A → List Nat → Result A) (mapArrays : F → List A → Result R)
    (function : F) (first second : A) (rest : List A) : Result R := do
  let arrays := first :: second :: rest
  let shapes := arrays.map size
  let shape := highestRankShape shapes
  let sameShape ← arrays.mapM fun array =>
    if shape.length = ndims array then .ok array else reshape array shape
  mapArrays function sameShape

def P16 : Prop := ∀ {A F R : Type} size ndims reshape mapArrays function first second rest,
  m16 (A := A) (F := F) (R := R) size ndims reshape mapArrays function first second rest = do
    let arrays := first :: second :: rest
    let shapes := arrays.map size
    let shape := highestRankShape shapes
    let sameShape ← arrays.mapM fun array =>
      if shape.length = ndims array then .ok array else reshape array shape
    mapArrays function sameShape

theorem p16 : P16 := by unfold P16 m16; intros; rfl

structure ReverseOps (A V : Type) where
  size : A → Int → Result Int
  firstIndex : A → Int → Result Int
  lastIndex : A → Int → Result Int
  getindex : A → List Int → Result V
  setindex : A → List Int → V → Result Unit
  view : A → List (List Int) → Result A

def oneTo (rank : Nat) : List Int :=
  (List.range rank).map fun index => ((index + 1 : Nat) : Int)

def cartesianPoints : List (List Int) → List (List Int)
  | [] => [[]]
  | axis :: axes =>
      (cartesianPoints axes).flatMap fun tail => axis.map fun value => value :: tail

def reflectedIndex (reversed : List Bool) (offsets index : List Int) : List Int :=
  ((reversed.zip offsets).zip index).map fun item =>
    if item.1.1 then item.1.2 - item.2 else item.2

def reverseCore (ops : ReverseOps A V) (rank : Nat) (array : A) : List Int → Result A
  | [] => .ok array
  | dimensions@(leading :: remaining) => do
      let reversed := oneTo rank |>.map fun dimension => dimensions.contains dimension
      if rank < dimensions.length || dimensions.length != reversed.count true then
        .error .argument
      else
        let halfSizes ← oneTo rank |>.mapM fun dimension => do
          let extent ← ops.size array dimension
          .ok (if dimension = leading then extent / 2 else extent)
        let offsets ← oneTo rank |>.mapM fun dimension => do
          let last ← ops.lastIndex array dimension
          let first ← ops.firstIndex array dimension
          .ok (last + first)
        let halfAxes ← (oneTo rank).zip halfSizes |>.mapM fun item => do
          let first ← ops.firstIndex array item.1
          let _ ← ops.firstIndex array item.1
          .ok ((List.range item.2.toNat).map fun offset => first + Int.ofNat offset)
        let _ ← (cartesianPoints halfAxes).foldlM (fun _ index => do
          let reflected := reflectedIndex reversed offsets index
          let value ← ops.getindex array index
          let reflectedValue ← ops.getindex array reflected
          ops.setindex array reflected value
          ops.setindex array index reflectedValue) ()
        if !remaining.isEmpty then
          let extent ← ops.size array leading
          if extent % 2 != 0 then
            let first ← ops.firstIndex array leading
            let extentAgain ← ops.size array leading
            let middle := first + extentAgain / 2
            let middleAxes ← oneTo rank |>.mapM fun dimension =>
              if dimension = leading then .ok [middle]
              else do
                let lower ← ops.firstIndex array dimension
                let upper ← ops.lastIndex array dimension
                .ok ((List.range (upper - lower + 1).toNat).map fun offset => lower + Int.ofNat offset)
            let slice ← ops.view array middleAxes
            let _ ← reverseCore ops rank slice remaining
            .ok array
          else .ok array
        else .ok array

/-- `base/arraymath.jl:107-130`. The model accepts every signed `Int` tuple,
checks dimensions, builds both ntuples, performs the Cartesian swap loop, then
constructs and recursively reverses an odd middle slice. -/
def m107 (ops : ReverseOps A V) (rank : Nat) (array : A)
    (dimensions : List Int) : Result A :=
  reverseCore ops rank array dimensions

def P107 : Prop := ∀ {A V : Type} ops rank array dimensions,
  m107 (A := A) (V := V) ops rank array dimensions = reverseCore ops rank array dimensions

theorem p107 : P107 := by unfold P107 m107; intros; rfl

/-- `base/arraymath.jl:154-162`. The second `axes(A,1)` call controls the
outer loop after swapped-axis allocation. -/
def m154 (axes : A → Result (List Int × List Int))
    (similar : A → List Int → List Int → Result B) (axis : A → Int → Result (List Int))
    (getindex : A → Int → Int → Result V) (setindex : B → Int → Int → V → Result Unit)
    (array : A) : Result B := do
  let indices ← axes array
  let output ← similar array indices.2 indices.1
  let reflected := indices.2.headD 0 + indices.2.getLastD 0
  let outer ← axis array 1
  let _ ← outer.foldlM (fun _ i =>
    indices.2.foldlM (fun _ j => do
      let value ← getindex array i j
      setindex output (reflected - j) i value) ()) ()
  .ok output

def P154 : Prop := ∀ {A B V : Type} axes similar axis getindex setindex array,
  m154 (A := A) (B := B) (V := V) axes similar axis getindex setindex array = do
    let indices ← axes array
    let output ← similar array indices.2 indices.1
    let reflected := indices.2.headD 0 + indices.2.getLastD 0
    let outer ← axis array 1
    let _ ← outer.foldlM (fun _ i =>
      indices.2.foldlM (fun _ j => do
        let value ← getindex array i j
        setindex output (reflected - j) i value) ()) ()
    .ok output

theorem p154 : P154 := by unfold P154 m154; intros; rfl

/-- `base/arraymath.jl:182-190`. `axes(A,2)` is evaluated for each outer
iteration, matching the nested `for i=ind1, j=axes(A,2)` source loop. -/
def m182 (axes : A → Result (List Int × List Int))
    (similar : A → List Int → List Int → Result B) (axis : A → Int → Result (List Int))
    (getindex : A → Int → Int → Result V) (setindex : B → Int → Int → V → Result Unit)
    (array : A) : Result B := do
  let indices ← axes array
  let output ← similar array indices.2 indices.1
  let reflected := indices.1.headD 0 + indices.1.getLastD 0
  let _ ← indices.1.foldlM (fun _ i => do
    let inner ← axis array 2
    inner.foldlM (fun _ j => do
      let value ← getindex array i j
      setindex output j (reflected - i) value) ()) ()
  .ok output

def P182 : Prop := ∀ {A B V : Type} axes similar axis getindex setindex array,
  m182 (A := A) (B := B) (V := V) axes similar axis getindex setindex array = do
    let indices ← axes array
    let output ← similar array indices.2 indices.1
    let reflected := indices.1.headD 0 + indices.1.getLastD 0
    let _ ← indices.1.foldlM (fun _ i => do
      let inner ← axis array 2
      inner.foldlM (fun _ j => do
        let value ← getindex array i j
        setindex output j (reflected - i) value) ()) ()
    .ok output

theorem p182 : P182 := by unfold P182 m182; intros; rfl

/-- `base/arraymath.jl:209-217`. Allocation precedes the separate dimension-one
and dimension-two axis calls, followed by the `j`, `i` loop nest. -/
def m209 (similar : A → Result B) (axis : A → Int → Result (List Int))
    (getindex : A → Int → Int → Result V) (setindex : B → Int → Int → V → Result Unit)
    (array : A) : Result B := do
  let output ← similar array
  let firstAxis ← axis array 1
  let secondAxis ← axis array 2
  let reflectedFirst := firstAxis.headD 0 + firstAxis.getLastD 0
  let reflectedSecond := secondAxis.headD 0 + secondAxis.getLastD 0
  let _ ← secondAxis.foldlM (fun _ j =>
    firstAxis.foldlM (fun _ i => do
      let value ← getindex array i j
      setindex output (reflectedFirst - i) (reflectedSecond - j) value) ()) ()
  .ok output

def P209 : Prop := ∀ {A B V : Type} similar axis getindex setindex array,
  m209 (A := A) (B := B) (V := V) similar axis getindex setindex array = do
    let output ← similar array
    let firstAxis ← axis array 1
    let secondAxis ← axis array 2
    let reflectedFirst := firstAxis.headD 0 + firstAxis.getLastD 0
    let reflectedSecond := secondAxis.headD 0 + secondAxis.getLastD 0
    let _ ← secondAxis.foldlM (fun _ j =>
      firstAxis.foldlM (fun _ i => do
        let value ← getindex array i j
        setindex output (reflectedFirst - i) (reflectedSecond - j) value) ()) ()
    .ok output

theorem p209 : P209 := by unfold P209 m209; intros; rfl

/-- `base/arraymath.jl:252-257`. Generic `mod` and equality dispatch remain
explicit, so BigInt and custom Integer behavior is covered without coercion. -/
def m252 (modFour : I → Result K) (equals : K → Nat → Result Bool)
    (left half right copy : A → Result R) (array : A) (turns : I) : Result R := do
  let reduced ← modFour turns
  if ← equals reduced 1 then left array
  else if ← equals reduced 2 then half array
  else if ← equals reduced 3 then right array
  else copy array

def P252 : Prop := ∀ {I K A R : Type} modFour equals left half right copy array turns,
  m252 (I := I) (K := K) (A := A) (R := R)
      modFour equals left half right copy array turns = do
    let reduced ← modFour turns
    if ← equals reduced 1 then left array
    else if ← equals reduced 2 then half array
    else if ← equals reduced 3 then right array
    else copy array

theorem p252 : P252 := by unfold P252 m252; intros; rfl

/-- `base/arraymath.jl:292`. Unary negation uses the input Integer's Julia
dispatch and its exact result is passed to counted `rotl90`. -/
def m292 (negate : I → Result J) (rotateLeft : A → J → Result R)
    (array : A) (turns : I) : Result R := do
  let opposite ← negate turns
  rotateLeft array opposite

def P292 : Prop := ∀ {I J A R : Type} negate rotateLeft array turns,
  m292 (I := I) (J := J) (A := A) (R := R) negate rotateLeft array turns = do
    let opposite ← negate turns
    rotateLeft array opposite

theorem p292 : P292 := by unfold P292 m292; intros; rfl

/-- `base/arraymath.jl:317`. Generic modulo and equality dispatch select
rotation for odd counts and copying otherwise. -/
def m317 (modTwo : I → Result K) (equals : K → Nat → Result Bool)
    (half copy : A → Result R) (array : A) (turns : I) : Result R := do
  let reduced ← modTwo turns
  if ← equals reduced 1 then half array else copy array

def P317 : Prop := ∀ {I K A R : Type} modTwo equals half copy array turns,
  m317 (I := I) (K := K) (A := A) (R := R)
      modTwo equals half copy array turns = do
    let reduced ← modTwo turns
    if ← equals reduced 1 then half array else copy array

theorem p317 : P317 := by unfold P317 m317; intros; rfl

private def entry (line : Nat) (fn statement : String) (prop proof : Lean.Name) : Entry :=
  { id := s!"multidimcov-arraymath-faithful-{line}"
    juliaFile := "base/arraymath.jl"
    juliaFns := [fn]
    statement
    source := s!"base/arraymath.jl:{line}"
    status := .proven
    prop
    thm := some proof }

def entries : List Entry := [
  entry 16 "_broadcast_preserving_zero_d(f,::Array,...)" "The mixed-rank overload maps size, selects the first longest shape, checks ndims separately, reshapes only rank mismatches, and maps in source order." ``P16 ``p16,
  entry 107 "_reverse!(::AbstractArray,::NTuple{M,Int})" "The reversal core covers every signed dimension tuple, validates it, builds half and reflected indices, swaps the Cartesian half, and recursively reverses the odd middle slice." ``P107 ``p107,
  entry 154 "rotl90(::AbstractMatrix)" "Left rotation reads axes, allocates swapped axes, calls axes(A,1), and performs every reflected assignment in loop order." ``P154 ``p154,
  entry 182 "rotr90(::AbstractMatrix)" "Right rotation reads axes, allocates swapped axes, and evaluates axes(A,2) for each outer iteration before reflected assignment." ``P182 ``p182,
  entry 209 "rot180(::AbstractMatrix)" "Half rotation allocates first, reads both axes separately, and performs the j then i reflected assignment loop." ``P209 ``p209,
  entry 252 "rotl90(::AbstractMatrix,::Integer)" "Counted left rotation preserves generic Integer modulo and equality dispatch before selecting left, half, right, or copy." ``P252 ``p252,
  entry 292 "rotr90(::AbstractMatrix,::Integer)" "Counted right rotation preserves generic unary negation and passes its exact result to counted left rotation." ``P292 ``p292,
  entry 317 "rot180(::AbstractMatrix,::Integer)" "Counted half rotation preserves generic modulo and equality dispatch before selecting rotation or copy." ``P317 ``p317
]

end JuliaLean.MultidimCov.ArrayMathFaithfulFinal
