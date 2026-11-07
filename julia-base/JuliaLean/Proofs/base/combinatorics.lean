import JuliaLean.Registry.Types
import JuliaLean.base.combinatorics

namespace JuliaLean.Proofs.base.combinatorics

open JuliaLean

/-- Encoding of the three concrete cases in Tuple{} ∪ Tuple{Int} ∪ Tuple{Int,Int}.
Every value is a realizable native tuple of length at most two. -/
def NativeSmallTuple : Type := Unit ⊕ (JInt .i64 ⊕ (JInt .i64 × JInt .i64))

def nativeSmallValues : NativeSmallTuple → List Int
  | .inl _ => []
  | .inr (.inl a) => [a.val]
  | .inr (.inr ab) => [ab.1.val, ab.2.val]

/-- Bind each source isperm overload; this supplies no expected answer or correctness law.
Julia source: base/combinatorics.jl:87-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def nativeSmallIsperm : NativeSmallTuple → Bool
  | .inl _ => JuliaLean.base.combinatorics.isperm_Tuple0
  | .inr (.inl a) => JuliaLean.base.combinatorics.isperm_Tuple1 a
  | .inr (.inr ab) => JuliaLean.base.combinatorics.isperm_Tuple2 ab.1 ab.2

/-- Independent mathematical inverse relation, expressed by transposed positions. -/
def InversePositions (input output : List Int) : Prop :=
  output.length = input.length ∧
  List.Perm output ((List.range input.length).map (fun (i : Nat) => (i : Int) + 1)) ∧
  ∀ (i j : Nat), i < input.length → j < output.length →
    (input[i]? = some ((j : Int) + 1) ↔ output[j]? = some ((i : Int) + 1))

end JuliaLean.Proofs.base.combinatorics

namespace JuliaLean.Proofs.base.combinatorics.Round1

open JuliaLean.Proofs.base.combinatorics
open JuliaLean

/-- A pair of native Int values is a permutation precisely when it permutes [1,2].
Julia source: base/combinatorics.jl:89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/combinatorics.jl:62-75 and doc/src/base/arrays.md:209
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TupleTwoPermutation : Prop :=
  ∀ (a b : JInt .i64),
    JuliaLean.base.combinatorics.isperm_Tuple2 a b = true ↔
      List.Perm [a.val, b.val] [1, 2]

/-- The singleton native-Int overload recognizes exactly the mathematical permutation [1].
Julia source: base/combinatorics.jl:88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/combinatorics.jl:62-75; doc/src/base/arrays.md:209
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TupleOnePermutation : Prop :=
  ∀ (a : JInt .i64),
    JuliaLean.base.combinatorics.isperm_Tuple1 a = true ↔ List.Perm [a.val] [1]

/-- The complete native small-tuple invperm overload accepts exactly permutations and returns
their inverse; invalid tuples raise the source ArgumentError.
Julia source: base/combinatorics.jl:298-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/combinatorics.jl:245-284; doc/src/base/arrays.md:208
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def NativeSmallTupleInverse : Prop :=
  ∀ (p : NativeSmallTuple),
    if List.Perm (nativeSmallValues p)
        ((List.range (nativeSmallValues p).length).map (fun (i : Nat) => (i : Int) + 1)) then
      ∃ q,
        JuliaLean.base.combinatorics.invperm_small nativeSmallIsperm p = .ok q ∧
        InversePositions (nativeSmallValues p) (nativeSmallValues q)
    else
      JuliaLean.base.combinatorics.invperm_small nativeSmallIsperm p =
        .error (.argumentError "argument is not a permutation")

end JuliaLean.Proofs.base.combinatorics.Round1

namespace JuliaLean.Proofs.base.combinatorics

open JuliaLean.Registry

end JuliaLean.Proofs.base.combinatorics

namespace JuliaLean.ChatGPT.Batch4.Group22
open JuliaLean JuliaLean.Proofs.base.combinatorics

theorem tuplePairPermutationCases (a b : Int) :
    List.Perm [a, b] [1, 2] ↔ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
  constructor
  · intro h
    have ha : a = 1 ∨ a = 2 := by
      have hm : a ∈ ([1, 2] : List Int) := h.subset (List.mem_cons_self ..)
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hm
    rcases ha with ha | ha
    · left
      refine ⟨ha, ?_⟩
      have hp : List.Perm [1, b] [1, 2] := by simpa only [ha] using h
      exact List.singleton_perm_singleton.mp hp.cons_inv
    · right
      refine ⟨ha, ?_⟩
      have hp : List.Perm [2, b] [1, 2] := by simpa only [ha] using h
      have hs : List.Perm ([1, 2] : List Int) [2, 1] := .swap ..
      exact List.singleton_perm_singleton.mp (hp.trans hs).cons_inv
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .refl _
    · exact .swap ..

/-- combinatorics-two-tuple-permutation -/
theorem CombinatoricsTwoTuplePermutation_proven : JuliaLean.Proofs.base.combinatorics.Round1.TupleTwoPermutation := by
  intro a b
  rw [tuplePairPermutationCases]
  simp only [JuliaLean.base.combinatorics.isperm_Tuple2, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]

/-- combinatorics-one-tuple-permutation -/
theorem CombinatoricsOneTuplePermutation_proven : JuliaLean.Proofs.base.combinatorics.Round1.TupleOnePermutation := by
  intro a
  simp only [JuliaLean.base.combinatorics.isperm_Tuple1, beq_iff_eq,
    List.singleton_perm_singleton]

theorem tupleEmptyInversePositions : InversePositions [] [] := by
  refine ⟨rfl, .refl _, ?_⟩
  intro i j hi _
  change i < 0 at hi
  omega

theorem tupleOneInversePositions : InversePositions [1] [1] := by
  refine ⟨rfl, .refl _, ?_⟩
  intro i j hi hj
  change i < 1 at hi
  change j < 1 at hj
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst i
  subst j
  rfl

theorem tupleTwoForwardInversePositions : InversePositions [1, 2] [1, 2] := by
  refine ⟨rfl, .refl _, ?_⟩
  intro i j hi hj
  change i < 2 at hi
  change j < 2 at hj
  have hi01 : i = 0 ∨ i = 1 := by omega
  have hj01 : j = 0 ∨ j = 1 := by omega
  rcases hi01 with rfl | rfl <;> rcases hj01 with rfl | rfl <;> decide

theorem tupleTwoReverseInversePositions : InversePositions [2, 1] [2, 1] := by
  refine ⟨rfl, ?_, ?_⟩
  · change List.Perm ([2, 1] : List Int) [1, 2]
    exact .swap ..
  · intro i j hi hj
    change i < 2 at hi
    change j < 2 at hj
    have hi01 : i = 0 ∨ i = 1 := by omega
    have hj01 : j = 0 ∨ j = 1 := by omega
    rcases hi01 with rfl | rfl <;> rcases hj01 with rfl | rfl <;> decide

theorem tupleSmallPermutation (p : NativeSmallTuple) :
    nativeSmallIsperm p = true ↔
      List.Perm (nativeSmallValues p)
        ((List.range (nativeSmallValues p).length).map (fun (i : Nat) => (i : Int) + 1)) := by
  rcases p with u | a | ⟨a, b⟩
  · change true = true ↔ List.Perm ([] : List Int) []
    exact ⟨fun _ => .refl _, fun _ => rfl⟩
  · change JuliaLean.base.combinatorics.isperm_Tuple1 a = true ↔ List.Perm [a.val] [1]
    exact CombinatoricsOneTuplePermutation_proven a
  · change JuliaLean.base.combinatorics.isperm_Tuple2 a b = true ↔ List.Perm [a.val, b.val] [1, 2]
    exact CombinatoricsTwoTuplePermutation_proven a b

theorem tupleSmallInversePositions (p : NativeSmallTuple)
    (hp : List.Perm (nativeSmallValues p)
      ((List.range (nativeSmallValues p).length).map (fun (i : Nat) => (i : Int) + 1))) :
    InversePositions (nativeSmallValues p) (nativeSmallValues p) := by
  rcases p with u | a | ⟨a, b⟩
  · exact tupleEmptyInversePositions
  · change List.Perm [a.val] [1] at hp
    have ha : a.val = 1 := List.singleton_perm_singleton.mp hp
    change InversePositions [a.val] [a.val]
    rw [ha]
    exact tupleOneInversePositions
  · change List.Perm [a.val, b.val] [1, 2] at hp
    rcases (tuplePairPermutationCases a.val b.val).mp hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · change InversePositions [a.val, b.val] [a.val, b.val]
      rw [ha, hb]
      exact tupleTwoForwardInversePositions
    · change InversePositions [a.val, b.val] [a.val, b.val]
      rw [ha, hb]
      exact tupleTwoReverseInversePositions

/-- combinatorics-native-small-tuple-inverse -/
theorem CombinatoricsNativeSmallTupleInverse_proven : JuliaLean.Proofs.base.combinatorics.Round1.NativeSmallTupleInverse := by
  intro p
  split
  · rename_i hp
    have hb := (tupleSmallPermutation p).mpr hp
    refine ⟨p, ?_, tupleSmallInversePositions p hp⟩
    simp only [JuliaLean.base.combinatorics.invperm_small, hb, ite_true]
  · rename_i hp
    have hb : nativeSmallIsperm p = false := by
      cases he : nativeSmallIsperm p with
      | false => rfl
      | true => exact False.elim (hp ((tupleSmallPermutation p).mp he))
    simp only [JuliaLean.base.combinatorics.invperm_small, hb, Bool.false_eq_true, ite_false]

end JuliaLean.ChatGPT.Batch4.Group22

namespace JuliaLean.Proofs.base.combinatorics

open JuliaLean.Registry
def entries : List Entry := [
  { id := "combinatorics-two-tuple-permutation", juliaFile := "base/combinatorics.jl",
    juliaFns := ["isperm(::Tuple{Int,Int})"],
    statement := "A pair of native integers passes isperm exactly when its values permute [1, 2].",
    source := "base/combinatorics.jl:62-89; doc/src/base/arrays.md:209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.combinatorics.Round1.TupleTwoPermutation, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.CombinatoricsTwoTuplePermutation_proven },
  { id := "combinatorics-one-tuple-permutation", juliaFile := "base/combinatorics.jl",
    juliaFns := ["isperm(::Tuple{Int})"],
    statement := "A singleton native integer tuple passes isperm exactly when its value permutes [1].",
    source := "base/combinatorics.jl:62-88; doc/src/base/arrays.md:209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.combinatorics.Round1.TupleOnePermutation, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.CombinatoricsOneTuplePermutation_proven },
  { id := "combinatorics-native-small-tuple-inverse", juliaFile := "base/combinatorics.jl",
    juliaFns := ["invperm(::Union{Tuple{},Tuple{Int},Tuple{Int,Int}})"],
    statement := "Native tuples of length at most two are accepted exactly when they are permutations and return their mathematical inverse; invalid tuples raise ArgumentError.",
    source := "base/combinatorics.jl:245-301; doc/src/base/arrays.md:208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.combinatorics.Round1.NativeSmallTupleInverse, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.CombinatoricsNativeSmallTupleInverse_proven }
]

end JuliaLean.Proofs.base.combinatorics
