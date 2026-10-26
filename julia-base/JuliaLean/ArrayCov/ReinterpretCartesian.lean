import JuliaLean.Core
import JuliaLean.ArrayCov.ReinterpretSimple

namespace JuliaLean.ArrayCov

inductive CartesianRouteError where
  | bounds
  | mismatch
  deriving Repr, DecidableEq

abbrev CartesianJl (α : Type) := Except CartesianRouteError α

def reinterpret288EachIndex (eachIndex : Int → ReinterpretValue → List SCartesianIndexModel)
    (axes : ReinterpretValue → List Int)
    (mismatch : List Int → List (List Int) → CartesianJl (List SCartesianIndexModel))
    (style : Int) (first : ReinterpretValue) (rest : List ReinterpretValue) :
    CartesianJl (List SCartesianIndexModel) :=
  let iter := eachIndex style first
  let otherIters := rest.map (eachIndex style)
  if otherIters.all (· == iter) then .ok iter
  else mismatch (axes first) (rest.map axes)

def reinterpret301GetIndex (checkbounds : SCartesianIndicesModel → JInt64 → JInt64 → Bool)
    (get : List JInt64 → JInt64 → CartesianJl JInt64)
    (iter : SCartesianIndicesModel) (i j : JInt64) : CartesianJl SCartesianIndexModel := do
  if checkbounds iter i j then pure () else throw .bounds
  let item ← get iter.indices2 j
  pure ⟨i, item⟩

def reinterpret306Iterate (iterate : List JInt64 → Option (JInt64 × JInt64))
    (iter : SCartesianIndicesModel) :
    Option (SCartesianIndexModel × (JInt64 × JInt64 × JInt64)) :=
  match iterate iter.indices2 with
  | none => none
  | some (item, state) =>
      some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))

def reinterpret313IterateState
    (iterate : List JInt64 → JInt64 → Option (JInt64 × JInt64))
    (iter : SCartesianIndicesModel)
    (state1 item2 state2 : JInt64) :
    Option (SCartesianIndexModel × (JInt64 × JInt64 × JInt64)) :=
  if state1 < iter.k then
    let item1 := state1 + JInt.lit .i64 1
    some (⟨item1, item2⟩, (item1, item2, state2))
  else
    match iterate iter.indices2 state2 with
    | none => none
    | some (item, state) =>
        some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))

def reinterpret334GetFallback
    (getCartesian : ReinterpretValue → List Int → Jl Int)
    (array : ReinterpretValue) (indices : List Int) : Jl Int :=
  getCartesian array indices

def reinterpret338SetFallback
    (setCartesian : ReinterpretValue → Int → List Int → Jl ReinterpretValue)
    (array : ReinterpretValue) (value : Int) (indices : List Int) : Jl ReinterpretValue :=
  setCartesian array value indices

def reinterpret344GetCartesian
    (firstAxis : ReinterpretValue → JInt64)
    (trailing : Int → ReinterpretValue → SCartesianIndexModel → List JInt64)
    (getindex : ReinterpretValue → List JInt64 → Jl Int)
    (style : Int) (array : ReinterpretValue) (index : SCartesianIndexModel) : Jl Int :=
  let first := firstAxis array + index.i - JInt.lit .i64 1
  getindex array (first :: trailing style array index)

def reinterpret349SetCartesian
    (firstAxis : ReinterpretValue → JInt64)
    (trailing : Int → ReinterpretValue → SCartesianIndexModel → List JInt64)
    (setindex : ReinterpretValue → Int → List JInt64 → Jl ReinterpretValue)
    (style : Int) (array : ReinterpretValue) (value : Int)
    (index : SCartesianIndexModel) : Jl ReinterpretValue :=
  let first := firstAxis array + index.i - JInt.lit .i64 1
  setindex array value (first :: trailing style array index)

def reinterpret356Trailing
    (eachIndices2 : Int → ReinterpretValue → List JInt64)
    (axes : ReinterpretValue → List (List JInt64))
    (first : List JInt64 → JInt64)
    (cartesianAt : List (List JInt64) → JInt64 → List JInt64)
    (style : Int) (array : ReinterpretValue) (index : SCartesianIndexModel) : List JInt64 :=
  let k := index.j - first (eachIndices2 style array)
  let tailAxes := (axes array).tail
  match tailAxes with
  | [axis] => [first axis + k]
  | _ => cartesianAt tailAxes (k + JInt.lit .i64 1)

def ReinterpretCartesianIterationCorrect : Prop :=
  (∀ each axes mismatch style first rest,
      reinterpret288EachIndex each axes mismatch style first rest =
        let iter := each style first
        let other := rest.map (each style)
        if other.all (· == iter) then .ok iter else mismatch (axes first) (rest.map axes)) ∧
  (∀ bounds get iter i j, reinterpret301GetIndex bounds get iter i j = do
      if bounds iter i j then pure () else throw .bounds
      let item ← get iter.indices2 j
      pure ⟨i, item⟩) ∧
  (∀ iterate iter, reinterpret306Iterate iterate iter =
      match iterate iter.indices2 with
      | none => none
      | some (item, state) =>
          some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))) ∧
  (∀ iterate iter state1 item2 state2,
      reinterpret313IterateState iterate iter state1 item2 state2 =
      if state1 < iter.k then
        let item1 := state1 + JInt.lit .i64 1
        some (⟨item1, item2⟩, (item1, item2, state2))
      else match iterate iter.indices2 state2 with
        | none => none
        | some (item, state) =>
            some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))) ∧
  (∀ get array indices, reinterpret334GetFallback get array indices = get array indices) ∧
  (∀ set array value indices, reinterpret338SetFallback set array value indices =
      set array value indices) ∧
  (∀ first trailing get style array index,
      reinterpret344GetCartesian first trailing get style array index =
      get array ((first array + index.i - JInt.lit .i64 1) :: trailing style array index)) ∧
  (∀ first trailing set style array value index,
      reinterpret349SetCartesian first trailing set style array value index =
      set array value
        ((first array + index.i - JInt.lit .i64 1) :: trailing style array index)) ∧
  (∀ each axes first cart style array index,
      reinterpret356Trailing each axes first cart style array index =
      let k := index.j - first (each style array)
      let tailAxes := (axes array).tail
      match tailAxes with
      | [axis] => [first axis + k]
      | _ => cart tailAxes (k + JInt.lit .i64 1))

theorem reinterpretCartesianIterationCorrect : ReinterpretCartesianIterationCorrect := by
  simp [ReinterpretCartesianIterationCorrect, reinterpret288EachIndex,
    reinterpret301GetIndex, reinterpret306Iterate, reinterpret313IterateState,
    reinterpret334GetFallback, reinterpret338SetFallback, reinterpret344GetCartesian,
    reinterpret349SetCartesian, reinterpret356Trailing]

end JuliaLean.ArrayCov
