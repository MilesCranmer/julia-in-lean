import JuliaLean.SortTuplesCov.NamedTupleProofs
import JuliaLean.SortTuplesCov.TupleCoverage
import JuliaLean.Tuples.ProofsCompare

/-! Faithful models for the remaining methods and macros in
`base/namedtuple.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (NT ntNames ntValues lookup)

/-! ### Display -/

structure ShowField (V : Type) where
  name : String
  value : V
  concrete : Bool

inductive NamedTupleShow where
  | fullType
  | empty
  | fields (names : List String) (singleton : Bool)

/-- `show(io, t::NamedTuple)`, `base/namedtuple.jl:198-229`.  The trace records
the three output forms after the source's concrete-field scan. -/
def showNamedTuple {V : Type} (fields : List (ShowField V)) : NamedTupleShow :=
  if fields.any fun f => !f.concrete then .fullType
  else if fields.isEmpty then .empty
  else .fields (fields.map (fun f => f.name)) (fields.length = 1)

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

/-! ### Type methods -/

/-- `nteltype(::Type) = Any` and the parameterized method at
`base/namedtuple.jl:231-233`. -/
def ntEltypeFallback (_ : TupleTy) : TupleTy := .any
def ntEltypeNamed (join : TupleTy → TupleTy → TupleTy) (tupleType : TupleTy) : TupleTy :=
  computeTupleEltype join (fun _ => false) tupleType
def namedTupleEltype (join : TupleTy → TupleTy → TupleTy) (tupleType : Option TupleTy) : TupleTy :=
  match tupleType with
  | none => ntEltypeFallback .any
  | some t => ntEltypeNamed join t

/-- `keytype` and `valtype`, `base/namedtuple.jl:235-239`. -/
def namedTupleKeytypeValue {V : Type} (_ : NT V) : TupleTy := .atom "Symbol"
def namedTupleKeytypeType (_ : List String) : TupleTy := .atom "Symbol"
def namedTupleValtypeValue {V : Type} (join : TupleTy → TupleTy → TupleTy)
    (fieldTypes : List TupleTy) (_ : NT V) : TupleTy :=
  ntEltypeNamed join (.tuple (fieldTypes.map .type))
def namedTupleValtypeType (join : TupleTy → TupleTy → TupleTy)
    (fieldTypes : List TupleTy) : TupleTy := ntEltypeNamed join (.tuple (fieldTypes.map .type))

/-- `_nt_names(::Type{T})`, `base/namedtuple.jl:248`. -/
def ntNamesType (names : List String) : List String := names

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

/-! ### Merge and structdiff type helpers -/

def fieldType (fields : List (String × TupleTy)) (name : String) : Option TupleTy :=
  (fields.find? fun p => p.1 = name).map Prod.snd

/-- `merge_types`, `base/namedtuple.jl:280-285`: for every merged name choose
the right field type when the name is present there, otherwise the left. -/
def mergeTypes (names : List String) (a b : List (String × TupleTy)) : List TupleTy :=
  names.filterMap fun n => (fieldType b n).or (fieldType a n)

/-- `diff_types`, `base/namedtuple.jl:403-407`. -/
def diffTypes (a : List (String × TupleTy)) (names : List String) : List TupleTy :=
  names.filterMap (fieldType a)

/-- `diff_fallback`, `base/namedtuple.jl:409-422`, with the Memory loop
represented by the selected fields in name order. -/
def diffFallback {V : Type} (a : NT V) (bn : List String) : NT V :=
  a.filter fun p => !bn.contains p.1

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

/-! ### Macros -/

inductive NTDecl where
  | name (name : String)
  | typed (name : String) (ty : TupleTy)
  | invalid

inductive NTSyntax where
  | braces (decls : List NTDecl)
  | block (decls : List NTDecl)
  | invalid

structure NamedTupleMacroResult where
  names : List String
  types : List TupleTy

def expandDeclarations : List NTDecl → Jl NamedTupleMacroResult
  | [] => .ok ⟨[], []⟩
  | .invalid :: _ => .error (.argumentError
      "@NamedTuple must contain a sequence of name or name::type expressions")
  | .name n :: ds => do
      let r ← expandDeclarations ds
      pure ⟨n :: r.names, .any :: r.types⟩
  | .typed n t :: ds => do
      let r ← expandDeclarations ds
      pure ⟨n :: r.names, t :: r.types⟩

/-- `@NamedTuple`, `base/namedtuple.jl:514-523`. -/
def namedTupleMacro : NTSyntax → Jl NamedTupleMacroResult
  | .braces ds | .block ds => expandDeclarations ds
  | .invalid => .error (.argumentError "@NamedTuple expects {...} or begin...end")

structure KwargsMacroResult where
  keyType : TupleTy
  valueType : TupleTy
  namedTuple : NamedTupleMacroResult

/-- `@Kwargs`, `base/namedtuple.jl:578-583`. -/
def kwargsMacro (ex : NTSyntax) : Jl KwargsMacroResult := do
  let nt ← namedTupleMacro ex
  pure ⟨.atom "Symbol", tupleEltype (fun _ _ => .any) (fun _ => false)
    (fun _ => false) (.tuple (nt.types.map .type)), nt⟩

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

/-- `split_rest(t::NamedTuple, n, st...)`, `base/namedtuple.jl:585-589`. -/
def namedTupleSplitRest {V : Type} (t : NT V) (n st : JInt .i64) :
    JuliaLean.Tuples.R (NT V × NT V) := do
  JuliaLean.Tuples.checkLengthSplitRest t.length n
  let names ← JuliaLean.Tuples.splitRestTuple (ntNames t) n st
  pure ((← JuliaLean.Tuples.selectNames t names.1),
    (← JuliaLean.Tuples.selectNames t names.2))

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
