import JuliaLean.Sort.Algorithms

/-!
`partialsort!`/`partialsort` and `partialsortperm!`/`partialsortperm`,
`base/sort.jl:97-177, 1853-1915` (master `bbfa0ce4150`), for element types
that are not `Bool` (so `BoolOptimization` passes through).
-/

namespace JuliaLean.Sort

open JuliaLean

/-- `k::Union{Integer,OrdinalRange}`. A range is stored as Julia stores it:
`first`, `step`, `last` and its length; its elements are `first + i*step`, `i < len`. -/
inductive KSel where
  | int (k : Int)
  | range (first step last : Int) (len : Nat)

/-- The indices `k` selects (`maybeview`, sort.jl:110-111). -/
def KSel.indices : KSel → List Int
  | .int k => [k]
  | .range f s _ n => (List.range n).map fun (i : Nat) => f + (i : Int) * s

/-- `ScratchQuickSort(k)`, sort.jl:1081-1082: `(k, k)` or `(first(k), last(k))`. -/
def KSel.target : KSel → Target
  | .int k => ⟨some k, some k⟩
  | .range f _ l _ => ⟨some f, some l⟩

def KSel.isEmpty : KSel → Bool
  | .int _ => false
  | .range _ _ _ n => n == 0

/-- Result of `partialsort!` in the model. `sampling` marks inputs that reach the
randomized sampling phase of `BracketedSort` (sort.jl:1287 onward: `length(v) ≥ 260`
and a nonempty target), which is outside this model. -/
inductive PartialOutcome (α : Type) where
  | done (v : Array α) (result : List α)
  | thrown (e : JlError)
  | sampling

section
variable {α : Type} [Inhabited α]

/-- `maybeview(v, k)` with the bounds check of `getindex`/`view`. -/
def maybeview (v : Array α) (k : KSel) : Jl (List α) :=
  if k.indices.all (fun i => decide (1 ≤ i ∧ i ≤ v.size)) then .ok (k.indices.map (rd v))
  else .error .boundsError

/-- `partialsort!(v, k, o)`, sort.jl:97-108:
`BoolOptimization(Small{12}(BracketedSort(k)))`. `BracketedSort` (sort.jl:1264-1286)
returns at once for `lo ≥ hi`, delegates to `InitialOptimizations(ScratchQuickSort(k))`
when `ln < 260`, and otherwise evaluates `minimum(target)` (sort.jl:1286), which
throws `ArgumentError` for an empty range. -/
def partialsort (piv : Int → Int → Int) (lt : α → α → Bool) (v : Array α) (k : KSel) :
    PartialOutcome α :=
  let n : Int := v.size
  let finish (w : Array α) : PartialOutcome α :=
    match maybeview w k with
    | .ok r => .done w r
    | .error e => .thrown e
  if n - 1 < 12 then finish (insertionSort lt v 1 n)                       -- sort.jl:797
  else if n < 260 then                                                    -- sort.jl:1277
    finish (initialOptimizations lt (fun w => scratchQuickSort piv lt k.target w 1 n) v 1 n)
  else if k.isEmpty then .thrown (.argumentError "range must be non-empty") -- sort.jl:1286
  else .sampling

/-- Stable insertion of `x` after every element it is not less than. -/
def insertStable (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertStable lt x ys

/-- Reference stable sort (specification only, not Julia code): insert the
elements left to right. -/
def sortRef (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertStable lt x acc) []

/-- The docstring answer of `partialsort(v, k)`: the values at the indices `k`
of the fully sorted vector. -/
def partialRef (lt : α → α → Bool) (v : Array α) (k : KSel) : List α :=
  k.indices.map fun i => (sortRef lt v.toList).getD (i - 1).toNat default

end

/-- `isless` on `Int`. -/
def intLt (a b : Int) : Bool := decide (a < b)

/-- `partialsort(v, k)` returns `sort(v)[k]` (docstring, sort.jl:116-120) for
every integer vector and every range `k` of valid indices, whenever the run
stays inside the model. -/
def PartialsortRangeCorrect : Prop :=
  ∀ (v : Array Int) (f s l : Int) (n : Nat),
    (∀ i ∈ (KSel.range f s l n).indices, 1 ≤ i ∧ i ≤ v.size) →
    (n ≥ 1 → l = f + (n - 1) * s) →
    ∀ w r, partialsort juliaPivot intLt v (.range f s l n) = .done w r →
      r = partialRef intLt v (.range f s l n)

/-- Found by random testing on Julia; see `repro/sort-partialsort-reversed-range.jl`. -/
def reversedRangeInput : Array Int :=
  #[4, 5, 2, 1, 1, 4, 4, 4, 2, 4, 5, 5, 3, 3, 2, 2, 4, 5, 2, 2, 5, 5]

/-- The returned values, if `partialsort!` returned. -/
def PartialOutcome.result? {α : Type} : PartialOutcome α → Option (List α)
  | .done _ r => some r
  | _ => none

/-- The exception, if `partialsort!` threw. -/
def PartialOutcome.thrown? {α : Type} : PartialOutcome α → Option JlError
  | .thrown e => some e
  | _ => none

theorem reversedRangeOutcome :
    (partialsort juliaPivot intLt reversedRangeInput (.range 5 (-1) 3 3)).result? = some [2, 2, 1] := by
  decide +kernel

theorem reversedRangeExpected :
    partialRef intLt reversedRangeInput (.range 5 (-1) 3 3) = [2, 2, 2] := by
  decide +kernel

theorem partialsortRangeCorrect_refuted : ¬ PartialsortRangeCorrect := by
  intro h
  have hb : ∀ i ∈ (KSel.range 5 (-1) 3 3).indices, 1 ≤ i ∧ i ≤ reversedRangeInput.size := by
    decide +kernel
  have hw := reversedRangeOutcome
  revert hw
  cases hp : partialsort juliaPivot intLt reversedRangeInput (.range 5 (-1) 3 3) with
  | done w r =>
    intro hw
    have := h reversedRangeInput 5 (-1) 3 3 hb (by decide) w r hp
    rw [reversedRangeExpected] at this
    simp only [PartialOutcome.result?, Option.some.injEq] at hw
    rw [this] at hw
    exact absurd hw (by decide)
  | thrown e => intro hw; simp [PartialOutcome.result?] at hw
  | sampling => intro hw; simp [PartialOutcome.result?] at hw

/-- `partialsort(v, k)` with an empty range `k` returns an empty vector, for every
vector `v` (it does for every `length(v) < 260`). -/
def PartialsortEmptyRange : Prop :=
  ∀ (v : Array Int) (f s l : Int),
    ∃ w, partialsort juliaPivot intLt v (.range f s l 0) = .done w []

theorem partialsortEmptyRangeThrows :
    (partialsort juliaPivot intLt (Array.replicate 260 0) (.range 4 1 3 0)).thrown? =
      some (.argumentError "range must be non-empty") := by
  decide +kernel

theorem partialsortEmptyRange_refuted : ¬ PartialsortEmptyRange := by
  intro h
  obtain ⟨w, hw⟩ := h (Array.replicate 260 0) 4 1 3
  have e := partialsortEmptyRangeThrows
  rw [hw] at e
  simp [PartialOutcome.thrown?] at e

/-! ### `partialsortperm` -/

instance sortInhabitedJInt {t : IntTy} : Inhabited (JInt t) := ⟨JInt.lit t 0⟩

/-- `partialsortperm(v, k)` for `k` of integer type `t` (sort.jl:1853-1854) and
`partialsortperm!` (sort.jl:1896-1915): `ix = similar(Vector{eltype(k)}, axes(v,1))`,
`ix[i] = i` converts each index to `t` (`InexactError` when it does not fit),
then `InitialOptimizations(ScratchQuickSort(k))` sorts `ix` under
`Perm(ord(lt, by, rev, order), v)` (`base/ordering.jl:123-127`). -/
def partialsortperm (t : IntTy) (piv : Int → Int → Int) (lt : Int → Int → Bool)
    (v : Array Int) (k : KSel) : Jl (List (JInt t)) := do
  let ix ← (List.range v.size).mapM fun (i : Nat) => JInt.convert t ((i : Int) + 1)
  let ix := ix.toArray
  let n : Int := v.size
  let plt (a b : JInt t) : Bool :=
    lt (rd v a.val) (rd v b.val) || (!(lt (rd v b.val) (rd v a.val)) && decide (a.val < b.val))
  let ix := initialOptimizations plt (fun w => scratchQuickSort piv plt k.target w 1 n) ix 1 n
  maybeview ix k

/-- Reference stable sorting permutation (specification only): the indices
`1:n` sorted stably by their values. -/
def sortpermRef (lt : Int → Int → Bool) (v : Array Int) : List Int :=
  sortRef (fun a b => lt (rd v a) (rd v b)) ((List.range v.size).map fun (i : Nat) => (i : Int) + 1)

/-- `partialsortperm(v, k)` returns `sortperm(v)[k]` (docstring, sort.jl:1825-1831)
for every valid index `k`, whatever its integer type. -/
def PartialsortpermIndexType : Prop :=
  ∀ (t : IntTy) (v : Array Int) (k : JInt t), 1 ≤ k.val → k.val ≤ v.size →
    ∃ r, partialsortperm t juliaPivot intLt v (.int k.val) = .ok r ∧
      r.map (·.val) = [(sortpermRef intLt v).getD (k.val - 1).toNat 0]

theorem partialsortpermInt8Throws :
    (partialsortperm .i8 juliaPivot intLt (Array.replicate 128 0) (.int 3)).toOption.isNone = true := by
  decide +kernel

theorem partialsortpermIndexType_refuted : ¬ PartialsortpermIndexType := by
  intro h
  obtain ⟨r, hr, -⟩ := h .i8 (Array.replicate 128 0) (JInt.lit .i8 3) (by decide) (by decide +kernel)
  have e := partialsortpermInt8Throws
  rw [show JInt.lit IntTy.i8 3 = ⟨3, by decide⟩ from rfl] at hr
  rw [hr] at e
  simp [Except.toOption] at e

end JuliaLean.Sort
