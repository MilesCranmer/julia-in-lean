import JuliaLean.base.namedtuple
import JuliaLean.Proofs.base.namedtuple.sort_namedtuple_correct
import JuliaLean.Proofs.base.tuple.sort_tuple_coverage
import JuliaLean.Proofs.base.tuple.compare
/-! Faithful models for the remaining methods and macros in
`base/namedtuple.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (NT ntNames ntValues lookup)

def NamedTupleShowCorrect : Prop :=
  (∀ (V : Type) (fs : List (ShowField V)),
    (fs.any fun f => !f.concrete) = true → showNamedTuple fs = .fullType) ∧
  (∀ (V : Type), showNamedTuple ([] : List (ShowField V)) = .empty) ∧
  (∀ (V : Type) (f : ShowField V), f.concrete = true →
    showNamedTuple [f] = .fields [f.name] true)

theorem namedTupleShowCorrect : NamedTupleShowCorrect := by
  refine ⟨?_, by simp [showNamedTuple], ?_⟩
  · intro V fs h
    simp [showNamedTuple, h]
  · intro V f h
    simp [showNamedTuple, h]

def NamedTupleTypeMethodsCorrect : Prop :=
  (∀ t, ntEltypeFallback t = .any) ∧
  (∀ join t, ntEltypeNamed join t = computeTupleEltype join (fun _ => false) t) ∧
  (∀ (V : Type) (nt : NT V), namedTupleKeytypeValue nt = .atom "Symbol") ∧
  (∀ names, namedTupleKeytypeType names = .atom "Symbol") ∧
  (∀ join tys, namedTupleValtypeType join tys =
    computeTupleEltype join (fun _ => false) (.tuple (tys.map .type))) ∧
  (∀ names, ntNamesType names = names)

theorem namedTupleTypeMethodsCorrect : NamedTupleTypeMethodsCorrect := by
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ => rfl⟩

def NamedTupleTypeHelpersCorrect : Prop :=
  (∀ names a b, mergeTypes names a b =
    names.filterMap fun n => (fieldType b n).or (fieldType a n)) ∧
  (∀ a names, diffTypes a names = names.filterMap (fieldType a)) ∧
  (∀ (V : Type) (a : NT V) bn,
    diffFallback a bn = a.filter fun p => !bn.contains p.1)

theorem namedTupleTypeHelpersCorrect : NamedTupleTypeHelpersCorrect := by
  refine ⟨by simp [mergeTypes], by simp [diffTypes], ?_⟩
  · intro V a bn
    rfl

def NamedTupleMacrosCorrect : Prop :=
  (∀ ds, namedTupleMacro (.braces ds) = expandDeclarations ds) ∧
  (∀ ds, namedTupleMacro (.block ds) = expandDeclarations ds) ∧
  namedTupleMacro .invalid =
    .error (.argumentError "@NamedTuple expects {...} or begin...end") ∧
  (∀ ex nt, namedTupleMacro ex = .ok nt →
    ∃ r, kwargsMacro ex = .ok r ∧ r.keyType = .atom "Symbol" ∧ r.namedTuple = nt)

theorem namedTupleMacrosCorrect : NamedTupleMacrosCorrect := by
  refine ⟨by simp [namedTupleMacro], by simp [namedTupleMacro], by simp [namedTupleMacro], ?_⟩
  intro ex nt h
  refine ⟨⟨.atom "Symbol", tupleEltype (fun _ _ => .any) (fun _ => false)
    (fun _ => false) (.tuple (nt.types.map .type)), nt⟩, ?_, rfl, rfl⟩
  unfold kwargsMacro
  rw [h]
  rfl

/-! ### Same-file coverage for hash and split_rest -/

/-- NamedTuple hashing uses the names' identity hash combined with tuple value
hashing, `base/namedtuple.jl:250`. -/
def NamedTupleHashCorrect : Prop := JuliaLean.Tuples.HashIsequal

theorem namedTupleHashCorrect : NamedTupleHashCorrect := JuliaLean.Tuples.hashIsequal

def NamedTupleSplitRestDelegates : Prop :=
  ∀ (V : Type) (t : NT V) n st, namedTupleSplitRest t n st = do
    JuliaLean.Tuples.checkLengthSplitRest t.length n
    let names ← JuliaLean.Tuples.splitRestTuple (ntNames t) n st
    pure ((← JuliaLean.Tuples.selectNames t names.1),
      (← JuliaLean.Tuples.selectNames t names.2))

theorem namedTupleSplitRestDelegates : NamedTupleSplitRestDelegates := by
  unfold NamedTupleSplitRestDelegates
  intros
  rfl

end JuliaLean.SortTuplesCov
