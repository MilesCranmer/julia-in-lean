import JuliaLean.base.reinterpretarray
import JuliaLean.Core
import JuliaLean.base.reinterpretarray

namespace JuliaLean.ArrayCov

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
  (repeat' (apply And.intro)) <;> intros <;> rfl

end JuliaLean.ArrayCov
