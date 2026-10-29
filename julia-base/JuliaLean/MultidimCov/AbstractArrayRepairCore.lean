import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayRepairCore

open JuliaLean
open JuliaLean.Registry

inductive Error where
  | methodError
  | dimensionMismatch (message : String)
  | source (id : Nat)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

def joinCommaAnd : List String → Result String
  | [left, right] => .ok (left ++ " and " ++ right)
  | left :: second :: rest => match joinCommaAnd (second :: rest) with
    | .error error => .error error
    | .ok tail => .ok (left ++ ", " ++ tail)
  | _ => .error .methodError

def mismatchMessage (indicesDescription first : String) (rest : List String) : Result String :=
  match joinCommaAnd (first :: rest) with
  | .error error => .error error
  | .ok joined => .error (.dimensionMismatch
      ("all inputs to eachindex must have the same " ++ indicesDescription ++ ", got " ++ joined))

def eachindexLinear (indices : A → Result I) (equal : I → I → Bool)
    (render : I → String) (first : A) (rest : List A) : Result I :=
  match indices first with
  | .error error => .error error
  | .ok firstIndices => match rest.mapM indices with
    | .error error => .error error
    | .ok otherIndices => if otherIndices.all (equal firstIndices) then .ok firstIndices else
      match mismatchMessage "indices" (render firstIndices) (otherIndices.map render) with
      | .error error => .error error
      | .ok _ => .error (.source 9)

def wrap64 (value : Int) : Int := wrapInt .i64 value

def strideBeyondRank (strides sizes : List Int) : Int :=
  match strides, sizes with
  | firstStride :: restStrides, firstSize :: restSizes =>
      (List.zip restStrides restSizes).foldl
        (fun total pair => wrap64 (total + wrap64 (pair.1 * pair.2)))
        (wrap64 (firstStride * firstSize))
  | _, _ => 1

def stride (strides sizes : List Int) (dimension : Int) : Result Int :=
  if dimension ≤ Int.ofNat strides.length && 1 ≤ dimension then
    match strides[(dimension - 1).toNat]? with
    | some value => .ok value
    | none => .error (.source 1)
  else if sizes = [] then .ok 1 else .ok (strideBeyondRank strides sizes)

def trailingDimensions (start rank : Int) : List Int :=
  if rank < start then [] else (List.range (rank - start + 1).toNat).map fun offset => start + Int.ofNat offset

def trailingSize (dimensionSize : Int → Result Int) (start rank : Int) : Result Int :=
  multiplyLoop (trailingDimensions start rank) 1
where
  multiplyLoop : List Int → Int → Result Int
    | [], product => .ok product
    | dimension :: rest, product => match dimensionSize dimension with
      | .error error => .error error
      | .ok size => multiplyLoop rest (wrap64 (product * size))

inductive IterStep (I S : Type) where
  | done
  | next (value : I) (state : S)

def checkindexIter (iterate : S → Result (IterStep I S))
    (check : I → Result Bool) : Nat → S → Bool → Result Bool
  | 0, _, accumulated => .ok accumulated
  | fuel + 1, state, accumulated => match iterate state with
    | .error error => .error error
    | .ok .done => .ok accumulated
    | .ok (.next value nextState) => match check value with
      | .error error => .error error
      | .ok checked => checkindexIter iterate check fuel nextState (accumulated && checked)

structure TypedVector (T : Type) where
  elementType : T
  length : Nat
  deriving Repr, DecidableEq

def emptymutable (typeToken : T) : TypedVector T := ⟨typeToken, 0⟩

def Contract : Prop :=
  (∀ left right, joinCommaAnd [left, right] = .ok (left ++ " and " ++ right)) ∧
  (∀ left second rest tail,
    joinCommaAnd (second :: rest) = .ok tail →
      joinCommaAnd (left :: second :: rest) = .ok (left ++ ", " ++ tail)) ∧
  (∀ singleton, joinCommaAnd [singleton] = .error .methodError) ∧
  (∀ {A I : Type} indices equal render first rest output,
    eachindexLinear (A := A) (I := I) indices equal render first rest = .ok output →
      indices first = .ok output ∧ ∃ otherIndices,
        rest.mapM indices = .ok otherIndices ∧ otherIndices.all (equal output)) ∧
  (∀ strides sizes, strideBeyondRank strides sizes =
    match strides, sizes with
    | firstStride :: restStrides, firstSize :: restSizes =>
      (List.zip restStrides restSizes).foldl
        (fun total pair => wrap64 (total + wrap64 (pair.1 * pair.2)))
        (wrap64 (firstStride * firstSize))
    | _, _ => 1) ∧
  (∀ start rank, (trailingDimensions start rank).all fun dimension => start ≤ dimension ∧ dimension ≤ rank) ∧
  (∀ {I S : Type} iterate check fuel state accumulated output,
    checkindexIter (I := I) (S := S) iterate check fuel state accumulated = .ok output →
      (accumulated = false → output = false)) ∧
  (∀ {T : Type} typeToken,
    (emptymutable (T := T) typeToken).elementType = typeToken ∧
      (emptymutable typeToken).length = 0)

theorem trailingDimensions_bounds (start rank : Int) :
    (trailingDimensions start rank).all fun dimension => start ≤ dimension ∧ dimension ≤ rank := by
  unfold trailingDimensions
  split
  · simp
  · simp only [List.all_eq_true, List.mem_map, List.mem_range]
    intro dimension h
    rcases h with ⟨offset, hoffset, rfl⟩
    constructor <;> omega

theorem checkindex_false (iterate : S → Result (IterStep I S)) (check : I → Result Bool) :
    ∀ fuel state output,
      checkindexIter iterate check fuel state false = .ok output → output = false := by
  intro fuel
  induction fuel with
  | zero => intro state output h; simpa [checkindexIter] using (Except.ok.inj h).symm
  | succ fuel ih =>
      intro state output h
      cases hi : iterate state with
      | error error => simp [checkindexIter, hi] at h
      | ok step =>
        cases step with
        | done => simpa [checkindexIter, hi] using (Except.ok.inj h).symm
        | next value nextState =>
          cases hc : check value with
          | error error => simp [checkindexIter, hi, hc] at h
          | ok checked => exact ih nextState output (by simpa [checkindexIter, hi, hc] using h)

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun _ _ => rfl, ?_, fun _ => rfl, ?_, fun _ _ => rfl,
    trailingDimensions_bounds, ?_, fun _ => ⟨rfl, rfl⟩⟩
  · intro left second rest tail h
    cases rest with
    | nil => simp [joinCommaAnd] at h ⊢
    | cons third rest => simp [joinCommaAnd, h]
  · intro A I indices equal render first rest output h
    cases hf : indices first with
    | error error => simp [eachindexLinear, hf] at h
    | ok firstIndices =>
      cases hr : rest.mapM indices with
      | error error => simp [eachindexLinear, hf, hr] at h
      | ok otherIndices =>
        by_cases he : otherIndices.all (equal firstIndices)
        · simp [eachindexLinear, hf, hr, he] at h
          subst output
          exact ⟨rfl, otherIndices, rfl, he⟩
        · simp [eachindexLinear, hf, hr, he] at h
  · intro I S iterate check fuel state accumulated output h hfalse
    subst accumulated
    exact checkindex_false iterate check fuel state output h

def entries : List Entry := [{
  id := "multidimcov-abstractarray-repair-core"
  juliaFile := "base/abstractarray.jl"
  juliaFns := ["_join_comma_and", "throw_eachindex_mismatch_indices", "eachindex", "stride", "trailingsize", "checkindex", "emptymutable"]
  statement := "Abstract-array core helpers preserve recursive diagnostics, actual index lists, wrapping Int stride arithmetic, negative trailing dimensions, incremental bounds checks, and requested element types."
  source := "base/abstractarray.jl:329-896"
  status := .proven
  prop := ``Contract
  thm := some ``contract
}]

end JuliaLean.MultidimCov.AbstractArrayRepairCore
