import JuliaLean.Core
import JuliaLean.ReinterpretArrays.Views

/-! Matrix-axis helpers from `base/combinatorics.jl:103-182`. A matrix is
represented by its ordered columns; row helpers have the same scalar-index
control flow and are covered by the shared bounds model. -/

namespace JuliaLean.Combinatorics

open JuliaLean

private instance {t : IntTy} : Inhabited (JInt t) := ⟨JInt.lit t 0⟩

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

def swapAxis (axisLength i j : Int) : Jl Unit :=
  if i = j then .ok ()
  else if 1 ≤ i ∧ i ≤ axisLength ∧ 1 ≤ j ∧ j ≤ axisLength then .ok ()
  else .error .boundsError

def SwapBoundsChecked : Prop := ∀ (axisLength i j : Int),
  0 ≤ axisLength → (i < 1 ∨ axisLength < i ∨ j < 1 ∨ axisLength < j) →
  swapAxis axisLength i j = .error .boundsError

theorem swapBoundsChecked_refuted : ¬ SwapBoundsChecked := by
  intro h
  have bad := h 2 3 3 (by omega) (by omega)
  simp [swapAxis] at bad

private def get1 {α : Type} [Inhabited α] (xs : List α) (i : Int) : α :=
  xs.getD (i - 1).toNat default

private def set1 {α : Type} (xs : List α) (i : Int) (x : α) : List α :=
  xs.set (i - 1).toNat x

private def swap1 {α : Type} [Inhabited α] (xs : List α) (i j : Int) : List α :=
  let xi := get1 xs i
  let xj := get1 xs j
  set1 (set1 xs i xj) j xi

private def cycleStep {t : IntTy} : Nat → List Int × List (JInt t) × Int × Int →
    Jl (List Int × List (JInt t) × Int × Int)
  | 0, _ => .error (.argumentError "cycle did not terminate")
  | fuel + 1, (cols, p, j, incoming) =>
      if (get1 p incoming).val < 0 then
        let cols' := swap1 cols incoming j
        let next := -(get1 p incoming)
        let p' := set1 p incoming next
        cycleStep fuel (cols', p', incoming, next.val)
      else .ok (cols, p, j, incoming)

private def permuteFor {t : IntTy} (n : Nat) : List Nat → List Int × List (JInt t) →
    Jl (List Int × List (JInt t))
  | [], state => .ok state
  | z :: rest, (cols, p) =>
      let i : Int := z + 1
      if (get1 p i).val > 0 then permuteFor n rest (cols, p)
      else do
        let incoming := -(get1 p i)
        let p' := set1 p i incoming
        let (cols', p'', _, _) ← cycleStep n (cols, p', i, incoming.val)
        permuteFor n rest (cols', p'')

/-- `_permute!`, `base/combinatorics.jl:151-165`, with columns represented by
their labels and the permutation vector mutated as the source mutates it. -/
def permuteCols {t : IntTy} (cols : List Int) (p : List (JInt t)) :
    Jl (List Int × List (JInt t)) :=
  let negated := p.map (fun x => -x)
  permuteFor p.length (List.range p.length) (cols, negated)

private def invCycle {t : IntTy} (i : Int) : Nat →
    List Int × List (JInt t) × Int → Jl (List Int × List (JInt t) × Int)
  | 0, _ => .error (.argumentError "inverse cycle did not terminate")
  | fuel + 1, (cols, p, j) =>
      if j = i then .ok (cols, p, j)
      else
        let cols' := swap1 cols j i
        let next := -(get1 p j)
        let p' := set1 p j next
        invCycle i fuel (cols', p', next.val)

private def invPermuteFor {t : IntTy} (n : Nat) : List Nat →
    List Int × List (JInt t) → Jl (List Int × List (JInt t))
  | [], state => .ok state
  | z :: rest, (cols, p) =>
      let i : Int := z + 1
      if (get1 p i).val > 0 then invPermuteFor n rest (cols, p)
      else do
        let j := -(get1 p i)
        let p' := set1 p i j
        let (cols', p'', _) ← invCycle i n (cols, p', j.val)
        invPermuteFor n rest (cols', p'')

/-- `_invpermute!`, `base/combinatorics.jl:170-182`. -/
def invPermuteCols {t : IntTy} (cols : List Int) (p : List (JInt t)) :
    Jl (List Int × List (JInt t)) :=
  let negated := p.map (fun x => -x)
  invPermuteFor p.length (List.range p.length) (cols, negated)

private def findNextNonzero {t : IntTy} : List (JInt t) → Nat → Option Nat
  | [], _ => none
  | x :: xs, 0 => if x.val ≠ 0 then some 0 else (findNextNonzero xs 0).map (· + 1)
  | _ :: xs, start + 1 => (findNextNonzero xs start).map (· + 1)

private def bangCycle {t : IntTy} (zero : JInt t) (start : Int) : Nat →
    List Int × List (JInt t) × Int × Int × Nat →
    Jl (List Int × List (JInt t) × Nat)
  | 0, _ => .error (.argumentError "destructive cycle did not terminate")
  | fuel + 1, (cols, p, ptr, next, count) =>
      if next = start then .ok (cols, set1 p ptr zero, count)
      else
        let cols' := swap1 cols ptr next
        let p' := set1 p ptr zero
        bangCycle zero start fuel (cols', p', next, (get1 p' next).val, count + 1)

private def bangOuter {t : IntTy} (zero : JInt t) (n : Nat) : Nat →
    List Int × List (JInt t) × Nat × Nat → Jl (List Int × List (JInt t))
  | 0, _ => .error (.argumentError "destructive permutation did not terminate")
  | fuel + 1, (cols, p, count, cursor) =>
      if count < n then
        match findNextNonzero p cursor with
        | none => .error (.argumentError "invalid permutation")
        | some z => do
            let start : Int := z + 1
            let next := (get1 p start).val
            let (cols', p', count') ← bangCycle zero start (n + 1)
              (cols, p, start, next, count + 1)
            bangOuter zero n fuel (cols', p', count', start.toNat)
      else .ok (cols, p)

/-- `permutecols!!`, `base/combinatorics.jl:125-144`. -/
def permuteColsBangBang {t : IntTy} (cols : List Int) (p : List (JInt t)) :
    Jl (List Int × List (JInt t)) :=
  bangOuter (JInt.lit t 0) p.length (p.length + 1) (cols, p, 0, 0)

def typedIsperm {t : IntTy} (p : List (JInt t)) : Bool :=
  JuliaLean.ReinterpretArrays.isperm (p.map (·.val))

def gatherCols {t : IntTy} (cols : List Int) (p : List (JInt t)) : List Int :=
  p.map (fun i => get1 cols i.val)

/-- The signed-marker matrix algorithm works for every integer permutation
admitted by its `AbstractVector{<:Integer}` signature. -/
def PermuteColsCorrect : Prop := ∀ (t : IntTy) (cols : List Int) (p : List (JInt t)),
  cols.length = p.length → typedIsperm p = true →
  permuteCols cols p = .ok (gatherCols cols p, p) ∧
  (∀ ip, JuliaLean.ReinterpretArrays.invperm (p.map (·.val)) = .ok ip →
    invPermuteCols cols p = .ok (ip.map (fun i => get1 cols i), p)) ∧
  permuteColsBangBang cols p = .ok (gatherCols cols p, List.replicate p.length (JInt.lit t 0))

theorem permuteColsCorrect_refuted : ¬ PermuteColsCorrect := by
  intro h
  have bad := (h .u8 [1, 2, 3] [JInt.lit .u8 3, JInt.lit .u8 1, JInt.lit .u8 2] rfl rfl).1
  revert bad
  decide +kernel

end JuliaLean.Combinatorics
