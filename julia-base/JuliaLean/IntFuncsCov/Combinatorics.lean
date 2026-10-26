import JuliaLean.Combinatorics.Integer
import JuliaLean.Combinatorics.Permutation
import JuliaLean.IntFuncsCov.Common

/-!
Coverage of the remaining methods of `base/combinatorics.jl` (master `bbfa0ce4150`): the
per-type `factorial` methods, `_foldoneto`, the `isperm` dispatch methods and the tuple
`invperm` methods.

Permutation elements are Julia reals of three kinds: machine integers, `Float64` and
`Bool`. An element is stored exactly as twice its value (`half`), which represents every
integer and every half-integer such as `1.5`; numeric comparisons (`0 < a <= n`,
`P[j] == i`) act on that value, while array indexing (`used[a]`, `b[j]`) follows
`to_index`, which rejects `Bool` and non-`Integer` reals with `ArgumentError`
(`base/indices.jl`). The tuple methods specialised to `Tuple{Int}` and `Tuple{Int,Int}` are
selected when every element is an integer.
-/

namespace JuliaLean.IntFuncsCov.Combinatorics

open JuliaLean JuliaLean.IntFuncsCov

/-! ### `factorial` methods -/

/-- `factorial_lookup(n, table, lim)`, `base/combinatorics.jl:21-30`: `Int(n)`, the sign and
limit checks, `one(n)` for zero, and `oftype(n, table[idx])`; the tables hold `idx!`. -/
def factorialLookup {t : IntTy} (n : JInt t) (lim : Int) : Jl (JInt t) := do
  let idx ← JInt.convert .i64 n.val
  if idx.val < 0 then .error (.domainError "n must not be negative")
  else if idx.val > lim then .error (.overflowError "too large for factorial table")
  else if idx.val = 0 then .ok (JInt.lit t 1)
  else JInt.convert t (JuliaLean.Combinatorics.factorialNat idx.val.toNat)

/-- The fixed-width `factorial` methods, `base/combinatorics.jl:32-40` on a 64-bit
platform: `Int128` (limit 33), `UInt128` (34), `Int64`/`UInt64` (20), and the narrower
types, which convert to `Int64` first. -/
def factorialMethod (t : IntTy) (n : JInt t) : Jl ((s : IntTy) × JInt s) :=
  match t with
  | .i128 => (⟨.i128, ·⟩) <$> factorialLookup n 33
  | .u128 => (⟨.u128, ·⟩) <$> factorialLookup n 34
  | .i64 => (⟨.i64, ·⟩) <$> factorialLookup n 20
  | .u64 => (⟨.u64, ·⟩) <$> factorialLookup n 20
  | _ => do
    let m ← JInt.convert .i64 n.val
    (⟨.i64, ·⟩) <$> factorialLookup m 20

/-- Value form of a `factorial` result. -/
def factorialOut (r : Jl ((s : IntTy) × JInt s)) : Jl (IntTy × Int) :=
  r.map fun p => (p.1, p.2.val)

/-- Every fixed-width `factorial` method returns `n!` in the documented result type when
`n!` is in the table, `DomainError` for negative `n`, and `OverflowError` beyond the table,
for every input that fits in `Int` (larger 64- and 128-bit inputs are the
`combinatorics-factorial-wide-error` refutation). -/
def FactorialMethods : Prop := ∀ (t : IntTy) (n : JInt t),
  IntTy.min .i64 ≤ n.val → n.val ≤ IntTy.max .i64 →
  factorialOut (factorialMethod t n) =
    (JuliaLean.Combinatorics.factorialSpec t n).map fun f => (f.ty, f.val)

private theorem fact_fits : ∀ k, k < 35 →
    ((JuliaLean.Combinatorics.factorialNat k : Int) ≤ IntTy.max .u128) ∧
    (k ≤ 33 → (JuliaLean.Combinatorics.factorialNat k : Int) ≤ IntTy.max .i128) ∧
    (k ≤ 20 → (JuliaLean.Combinatorics.factorialNat k : Int) ≤ IntTy.max .i64) ∧
    (k ≤ 20 → (JuliaLean.Combinatorics.factorialNat k : Int) ≤ IntTy.max .u64) := by
  decide +kernel

private theorem fact_pos (k : Nat) : 0 < JuliaLean.Combinatorics.factorialNat k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [JuliaLean.Combinatorics.factorialNat]; exact Nat.mul_pos (by omega) ih

private theorem lookup_eq {t : IntTy} (n : JInt t) (lim : Int) (hlo : IntTy.min .i64 ≤ n.val)
    (hhi : n.val ≤ IntTy.max .i64)
    (hfit : ∀ k : Nat, (k : Int) ≤ lim → (JuliaLean.Combinatorics.factorialNat k : Int) ≤ t.max)
    (hone : (1 : Int) ≤ t.max) :
    (factorialLookup n lim).map Subtype.val =
      (if n.val < 0 then .error (.domainError "n must not be negative")
       else if n.val > lim then .error (.overflowError "too large for factorial table")
       else .ok (JuliaLean.Combinatorics.factorialNat n.val.toNat : Int)) := by
  have hmin : t.min ≤ 0 := by cases t <;> decide
  unfold factorialLookup
  simp only [JInt.convert, dif_pos (And.intro hlo hhi)]
  by_cases hneg : n.val < 0
  · simp [hneg, Except.map, bind, Except.bind]
  · by_cases hlim : n.val > lim
    · simp [hneg, hlim, Except.map, bind, Except.bind]
    · by_cases hz : n.val = 0
      · have hw : (JInt.lit t 1).val = 1 := by
          show wrapInt t 1 = 1
          exact wrapInt_of_inRange t 1 ⟨by omega, hone⟩
        have hl : ¬ lim < 0 := by omega
        simp [hz, hl, Except.map, bind, Except.bind, hw, JuliaLean.Combinatorics.factorialNat]
      · have hk := hfit n.val.toNat (by omega)
        have hp := fact_pos n.val.toNat
        have hr : t.min ≤ (JuliaLean.Combinatorics.factorialNat n.val.toNat : Int) ∧
            (JuliaLean.Combinatorics.factorialNat n.val.toNat : Int) ≤ t.max := ⟨by omega, hk⟩
        simp [hneg, hlim, hz, Except.map, bind, Except.bind, JInt.convert, hr]

private theorem out_map (s : IntTy) (L : Jl (JInt s)) :
    factorialOut ((fun x => (⟨s, x⟩ : (r : IntTy) × JInt r)) <$> L) =
      (L.map Subtype.val).map (fun v => (s, v)) := by
  cases L <;> rfl

private theorem spec_eq (t : IntTy) (n : JInt t) :
    (JuliaLean.Combinatorics.factorialSpec t n).map (fun f => (f.ty, f.val)) =
      (if n.val < 0 then (Except.error (.domainError "n must not be negative") : Jl Int)
       else if n.val > JuliaLean.Combinatorics.factorialLimit t then
         Except.error (.overflowError "too large for factorial table")
       else Except.ok (JuliaLean.Combinatorics.factorialNat n.val.toNat : Int)).map
        (fun v => (JuliaLean.Combinatorics.factorialResultType t, v)) := by
  unfold JuliaLean.Combinatorics.factorialSpec
  split
  · rfl
  · split <;> rfl

theorem factorialMethods : FactorialMethods := by
  intro t n hlo hhi
  have hfit : ∀ (s : IntTy) (lim : Int), (lim = 33 ∧ s = .i128) ∨ (lim = 34 ∧ s = .u128) ∨
      (lim = 20 ∧ (s = .i64 ∨ s = .u64)) →
      ∀ k : Nat, (k : Int) ≤ lim → (JuliaLean.Combinatorics.factorialNat k : Int) ≤ s.max := by
    intro s lim hs k hk
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · exact (fact_fits k (by omega)).2.1 (by omega)
    · exact (fact_fits k (by omega)).1
    · exact (fact_fits k (by omega)).2.2.1 (by omega)
    · exact (fact_fits k (by omega)).2.2.2 (by omega)
  rw [spec_eq]
  cases t
  case i128 =>
    show factorialOut ((⟨.i128, ·⟩) <$> factorialLookup n 33) = _
    rw [out_map, lookup_eq n 33 hlo hhi (hfit .i128 33 (Or.inl ⟨rfl, rfl⟩)) (by decide)]; rfl
  case u128 =>
    show factorialOut ((⟨.u128, ·⟩) <$> factorialLookup n 34) = _
    rw [out_map, lookup_eq n 34 hlo hhi (hfit .u128 34 (Or.inr (Or.inl ⟨rfl, rfl⟩))) (by decide)]
    rfl
  case i64 =>
    show factorialOut ((⟨.i64, ·⟩) <$> factorialLookup n 20) = _
    rw [out_map, lookup_eq n 20 hlo hhi (hfit .i64 20 (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)))
      (by decide)]; rfl
  case u64 =>
    show factorialOut ((⟨.u64, ·⟩) <$> factorialLookup n 20) = _
    rw [out_map, lookup_eq n 20 hlo hhi (hfit .u64 20 (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)))
      (by decide)]; rfl
  all_goals
    have hr : IntTy.min .i64 ≤ n.val ∧ n.val ≤ IntTy.max .i64 := ⟨hlo, hhi⟩
    have hc : JInt.convert .i64 n.val = .ok ⟨n.val, hr⟩ := by simp [JInt.convert, hr]
    simp only [factorialMethod, hc]
    show factorialOut ((⟨.i64, ·⟩) <$> factorialLookup (⟨n.val, hr⟩ : JInt .i64) 20) = _
    rw [out_map, lookup_eq (⟨n.val, hr⟩ : JInt .i64) 20 hlo hhi
      (hfit .i64 20 (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))) (by decide)]
    rfl

/-! ### `_foldoneto` -/

/-- `_foldoneto(op, acc, Val(N))`, `base/combinatorics.jl:46-60`: the `@assert N > 0`
followed by `for i in 1:N; acc = op(acc, i); end` (the `@generated` branch unrolls the same
loop). `op` may itself throw. -/
def foldoneto {α : Type} (op : α → Nat → Jl α) (acc : α) (N : Nat) : Jl α :=
  if N > 0 then (List.range' 1 N).foldlM op acc
  else .error (.argumentError "AssertionError: N must be positive")

/-- `_foldoneto` applies `op` to `1, ..., N` in order for positive `N` and throws for zero. -/
def FoldonetoOrder : Prop :=
  (∀ (N : Nat) (xs : List Nat), 0 < N →
    foldoneto (fun acc i => (.ok (acc ++ [i]) : Jl (List Nat))) xs N = .ok (xs ++ List.range' 1 N)) ∧
  (∀ (op : Nat → Nat → Jl Nat) (acc : Nat), foldoneto op acc 0 =
    .error (.argumentError "AssertionError: N must be positive"))

private theorem foldlM_append (xs : List Nat) (ys : List Nat) :
    ys.foldlM (m := Except JlError) (fun acc i => .ok (acc ++ [i])) xs = .ok (xs ++ ys) := by
  induction ys generalizing xs with
  | nil => simp [List.foldlM]; rfl
  | cons y ys ih =>
    simp only [List.foldlM]
    show (ys.foldlM _ (xs ++ [y])) = _
    rw [ih]; simp

theorem foldonetoOrder : FoldonetoOrder := by
  refine ⟨fun N xs hN => ?_, fun op acc => rfl⟩
  simp only [foldoneto, if_pos hN]
  exact foldlM_append xs _

/-! ### `isperm` and `invperm` -/

inductive Kind where
  | int | float | bool
  deriving DecidableEq, Repr

/-- A permutation element: its kind and twice its numeric value. -/
structure Elem where
  kind : Kind
  half : Int
  deriving DecidableEq, Repr

def Elem.ofInt (v : Int) : Elem := ⟨.int, 2 * v⟩

/-- `to_index(a)` for a scalar index (`base/indices.jl`): an `Integer` indexes, a `Bool` or
a non-integer real throws `ArgumentError("invalid index ...")`. -/
def toIndex (a : Elem) : Jl Int :=
  match a.kind with
  | .int => .ok (a.half / 2)
  | _ => .error (.argumentError "invalid index")

/-- The loop of `_isperm(A)`, `base/combinatorics.jl:78-85`:
`(0 < a <= n) && (used[a] ⊻= true) || return false`. -/
def ispermLoop (n : Nat) : List Bool → List Elem → Jl Bool
  | _, [] => .ok true
  | used, a :: as =>
    if 0 < a.half ∧ a.half ≤ 2 * n then do
      let k ← toIndex a
      let i := k.toNat - 1
      let new := xor (used.getD i false) true
      if new then ispermLoop n (used.set i new) as else .ok false
    else .ok false

/-- `_isperm(A)`: `used = falses(length(A))` and the loop. -/
def ispermVec (A : List Elem) : Jl Bool := ispermLoop A.length (List.replicate A.length false) A

/-- `isperm(A)`, `base/combinatorics.jl:76`, for an array argument. -/
def ispermArray (A : List Elem) : Jl Bool := ispermVec A

/-- `isperm(p::Tuple{}) = true`, `:87`. -/
def ispermEmpty : Bool := true

/-- `isperm(p::Tuple{Int}) = p[1] == 1`, `:88`. -/
def isperm1 (a : Elem) : Bool := a.half == 2

/-- `isperm(p::Tuple{Int,Int})`, `:89`. -/
def isperm2 (a b : Elem) : Bool :=
  (a.half == 2 && b.half == 4) || (a.half == 4 && b.half == 2)

/-- `isperm(P::Tuple)`, `:91-99`: for each `i`, an inner `_foldoneto` ors `P[j] == i` over
`j`, and the outer one ands the results. -/
def ispermTuple (P : List Elem) : Jl Bool :=
  let n := P.length
  foldoneto (fun b i => do
    let s ← foldoneto (fun s j => .ok (s || (P.getD (j - 1) ⟨.int, 0⟩).half == 2 * (i : Int))) false n
    .ok (b && s)) true n

/-- `isperm(P::Any32) = _isperm(P)`, `:101`, for tuples of length at least 32. -/
def ispermAny32 (P : List Elem) : Jl Bool := ispermVec P

/-- Method selection for a tuple argument. -/
def ispermTupleDispatch : List Elem → Jl Bool
  | [] => .ok ispermEmpty
  | [a] => if a.kind = .int then .ok (isperm1 a) else ispermTuple [a]
  | [a, b] => if a.kind = .int ∧ b.kind = .int then .ok (isperm2 a b) else ispermTuple [a, b]
  | P => if 32 ≤ P.length then ispermAny32 P else ispermTuple P

/-- `invperm(a::AbstractVector)`, `base/combinatorics.jl:286-296`, on the element model:
`((1 <= j <= n) && b[j] == 0) || throw(ArgumentError)`, then `b[j] = i`. -/
def invpermVecLoop (n : Nat) : Nat → List Int → List Elem → Jl (List Int)
  | _, b, [] => .ok b
  | i, b, j :: js =>
    if 2 ≤ j.half ∧ j.half ≤ 2 * n then do
      let k ← toIndex j
      if b.getD (k.toNat - 1) 0 = 0 then invpermVecLoop n (i + 1) (b.set (k.toNat - 1) i) js
      else .error (.argumentError "argument is not a permutation")
    else .error (.argumentError "argument is not a permutation")

def invpermVec (A : List Elem) : Jl (List Int) :=
  invpermVecLoop A.length 1 (List.replicate A.length 0) A

/-- `invperm(p::Union{Tuple{},Tuple{Int},Tuple{Int,Int}})`, `:298-301`: check, then return
`p` itself. -/
def invpermSmall (p : List Elem) : Jl (List Int) := do
  let ok ← ispermTupleDispatch p
  if ok then .ok (p.map (·.half / 2)) else .error (.argumentError "argument is not a permutation")

/-- `invperm(P::Tuple)`, `:303-314`: entry `i` is the first `j` with `P[j] == i`, found by a
`_foldoneto` over `j`; a missing `i` throws. -/
def invpermTuple (P : List Elem) : Jl (List Int) :=
  let n := P.length
  (List.range' 1 n).mapM fun (i : Nat) => do
    let s ← foldoneto (fun (s : Option Nat) j => .ok (if s.isSome then s
      else if (P.getD (j - 1) ⟨.int, 0⟩).half == 2 * (i : Int) then some j else none)) none n
    match s with
    | none => .error (.argumentError "argument is not a permutation")
    | some j => .ok (j : Int)

/-- `invperm(P::Any32) = Tuple(invperm(collect(P)))`, `:316`. -/
def invpermAny32 (P : List Elem) : Jl (List Int) := invpermVec P

/-- Method selection for a tuple argument of `invperm`. -/
def invpermTupleDispatch : List Elem → Jl (List Int)
  | [] => invpermSmall []
  | [a] => if a.kind = .int then invpermSmall [a] else invpermTuple [a]
  | [a, b] => if a.kind = .int ∧ b.kind = .int then invpermSmall [a, b] else invpermTuple [a, b]
  | P => if 32 ≤ P.length then invpermAny32 P else invpermTuple P

/-- The mathematical definition: every `1..n` occurs exactly once (`combinatorics-isperm-definition`). -/
def isPermutation (P : List Int) : Bool := JuliaLean.Combinatorics.permutationDefinition P

/-- All integer lists of length at most `n` with entries in `-1..5`. -/
def intLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [[]] ++ ((intLists n).filter (·.length = n)).flatMap fun l =>
      ([-1, 0, 1, 2, 3, 4, 5] : List Int).map (· :: l)

/-- The inverse of a permutation `P` composes to the identity: `q[P[k]] = k`. -/
def invertsPerm (P q : List Int) : Bool :=
  q.length == P.length &&
  (List.range P.length).all fun k => q.getD ((P.getD k 0).toNat - 1) 0 == (k : Int) + 1

/-- For integer permutations, the array and every tuple `isperm` method return the
mathematical definition, and the array and tuple `invperm` methods agree on the inverse
permutation or both throw `ArgumentError`; checked for every integer tuple and vector of
length at most four with entries in `-1:5`. The 32-element methods delegate to the array
method. -/
def IspermInvpermIntegers : Prop :=
  (∀ P ∈ intLists 4,
    ispermArray (P.map Elem.ofInt) = .ok (isPermutation P) ∧
    ispermTupleDispatch (P.map Elem.ofInt) = .ok (isPermutation P) ∧
    ispermTuple (P.map Elem.ofInt) = (if P = [] then .error (.argumentError
      "AssertionError: N must be positive") else .ok (isPermutation P)) ∧
    (if isPermutation P then
      (match invpermTupleDispatch (P.map Elem.ofInt) with
        | .ok q => invertsPerm P q | .error _ => false) = true ∧
      invpermVec (P.map Elem.ofInt) = invpermTupleDispatch (P.map Elem.ofInt)
    else invpermTupleDispatch (P.map Elem.ofInt) = .error (.argumentError "argument is not a permutation") ∧
      invpermVec (P.map Elem.ofInt) = .error (.argumentError "argument is not a permutation"))) ∧
  (∀ P : List Elem, 32 ≤ P.length →
    ispermTupleDispatch P = ispermArray P ∧ invpermTupleDispatch P = invpermVec P)

set_option maxRecDepth 100000 in
theorem ispermInvpermIntegers : IspermInvpermIntegers := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · intro P hP
    rcases P with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at hP
    · simp at hP
    · simp at hP
    · constructor <;> simp only [ispermTupleDispatch, invpermTupleDispatch, if_pos hP,
        ispermAny32, invpermAny32, ispermArray] <;> rfl

/-- `isperm` documents a `Bool` result for every argument, and the array and tuple methods
agree on the same elements. -/
def IspermTotal : Prop := ∀ P : List Elem,
  (∃ b, ispermArray P = .ok b) ∧ ispermArray P = ispermTupleDispatch P

/-- `isperm([2.0, 1.0])` throws `ArgumentError` from `used[2.0]`, while
`isperm((2.0, 1.0))` returns `true`. -/
theorem ispermTotal_refuted : ¬ IspermTotal := by
  intro h
  have h2 := (h [⟨.float, 4⟩, ⟨.float, 2⟩]).2
  revert h2
  decide

/-! ### Empty vectors with abstract element type -/

inductive EmptyEltype where
  | integer
  | any
  | bottom
  deriving DecidableEq

/-- The entry of `invperm(a::AbstractVector)` at `base/combinatorics.jl:286-296` before
the empty loop: `fill!(similar(a), zero(eltype(a)))`. `zero(Any)` and `zero(Union{})`
throw, while a concrete integer element type supplies zero. -/
def invpermEmpty : EmptyEltype → Jl (List Int)
  | .integer => .ok []
  | .any => .error (.methodError "zero")
  | .bottom => .error (.methodError "zero")

/-- `invperm` returns the inverse of every vector that `isperm` accepts, including an
empty vector of any declared element type. -/
def InvpermEmptyTotal : Prop := ∀ t : EmptyEltype, ∃ r, invpermEmpty t = .ok r

theorem invpermEmptyTotal_refuted : ¬ InvpermEmptyTotal := by
  intro h
  obtain ⟨r, hr⟩ := h .any
  cases hr

end JuliaLean.IntFuncsCov.Combinatorics
