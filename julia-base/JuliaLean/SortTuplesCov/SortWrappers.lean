import JuliaLean.SortTuplesCov.SortBugs

/-! Keyword wrappers and scratch-space methods from `base/sort.jl`
(master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

inductive RevChoice where
  | nothing | false_ | true_
  deriving DecidableEq

def reverseRequested : RevChoice → Bool
  | .true_ => true
  | _ => false

/-- Keyword `issorted`, `base/sort.jl:86-95`. -/
def issortedKeyword {I O R : Type} (ord : Bool → O) (core : I → O → R)
    (itr : I) (rev : RevChoice) : R :=
  if reverseRequested rev then core itr (ord true) else core itr (ord false)

/-- Keyword `partialsort!`, `base/sort.jl:166-168`. -/
def partialsortKeyword {V K O R : Type} (ord : RevChoice → O)
    (core : V → K → O → R) (v : V) (k : K) (rev : RevChoice) : R :=
  core v k (ord rev)

/-- Generated positional search wrappers, `base/sort.jl:304-310`. -/
def searchOrderWrapper {V X O R : Type} (first last : V → Int)
    (core : V → X → Int → Int → O → R) (v : V) (x : X) (o : O) : R :=
  core v x (first v) (last v) o

/-- Generated keyword search wrappers, `base/sort.jl:304-310`. -/
def searchKeywordWrapper {V X O R : Type} (ord : RevChoice → O)
    (core : V → X → O → R) (v : V) (x : X) (rev : RevChoice) : R :=
  core v x (ord rev)

def SortKeywordWrappersCorrect : Prop :=
  (∀ (I O R : Type) (ord : Bool → O) (core : I → O → R) (itr : I),
    issortedKeyword (R := R) ord core itr .true_ = core itr (ord true)) ∧
  (∀ (I O R : Type) (ord : Bool → O) (core : I → O → R) (itr : I) rev,
    rev ≠ .true_ →
    issortedKeyword (R := R) ord core itr rev = core itr (ord false)) ∧
  (∀ (V K O R : Type) (ord : RevChoice → O) (core : V → K → O → R)
      (v : V) (k : K) rev,
    partialsortKeyword (R := R) ord core v k rev = core v k (ord rev)) ∧
  (∀ (V X O R : Type) (first last : V → Int)
      (core : V → X → Int → Int → O → R) (v : V) (x : X) (o : O),
    searchOrderWrapper (R := R) first last core v x o = core v x (first v) (last v) o) ∧
  (∀ (V X O R : Type) (ord : RevChoice → O) (core : V → X → O → R)
      (v : V) (x : X) rev,
    searchKeywordWrapper (R := R) ord core v x rev = core v x (ord rev))

theorem sortKeywordWrappersCorrect : SortKeywordWrappersCorrect := by
  refine ⟨by simp [issortedKeyword, reverseRequested], ?_, by simp [partialsortKeyword],
    by simp [searchOrderWrapper], by simp [searchKeywordWrapper]⟩
  intro I O R ord core itr rev h
  cases rev <;> simp_all [issortedKeyword, reverseRequested]

/-! ### Alternative keyword management -/

inductive KwValue where
  | missing
  | nothing
  | value (n : Int)
  deriving DecidableEq

abbrev KwState := List (String × KwValue)

def kwLookup (kw : KwState) (name : String) : Option KwValue :=
  (kw.find? fun p => p.1 = name).map Prod.snd

/-- The body generated for `_lo`, `_hi`, `_mn`, `_mx`, `_scratch`, and
`_legacy_dispatch_entry`, `base/sort.jl:475-489`. -/
def generatedKeywordGetter (kw : KwState) (name : String) (default : KwValue) : KwState × KwValue :=
  match kwLookup kw name with
  | some v => if v = .missing then (kw ++ [(name, default)], default) else (kw, v)
  | none => (kw ++ [(name, default)], default)

/-- `@getkw syms...`, `base/sort.jl:470-473`, expands each symbol to its
generated getter name in the same order. -/
def getkwExpansion (syms : List String) : List String := syms.map ("_" ++ ·)

def GeneratedKeywordCorrect : Prop :=
  (∀ syms, getkwExpansion syms = syms.map ("_" ++ ·)) ∧
  (∀ kw name v default, kwLookup kw name = some v → v ≠ .missing →
    generatedKeywordGetter kw name default = (kw, v)) ∧
  (∀ kw name default, kwLookup kw name = none →
    generatedKeywordGetter kw name default = (kw ++ [(name, default)], default)) ∧
  (∀ kw name default, kwLookup kw name = some .missing →
    generatedKeywordGetter kw name default = (kw ++ [(name, default)], default))

theorem generatedKeywordCorrect : GeneratedKeywordCorrect := by
  refine ⟨by simp [getkwExpansion], ?_, ?_, ?_⟩
  · intro kw name v default h hv
    simp [generatedKeywordGetter, h, hv]
  · intro kw name default h
    simp [generatedKeywordGetter, h]
  · intro kw name default h
    simp [generatedKeywordGetter, h]

/-! ### Scratch space -/

structure ScratchType where
  name : String
  bytes : Nat
  bits : Bool

structure ScratchVector where
  type : ScratchType
  length : Nat

structure ScratchResult where
  backing : ScratchVector
  viewType : ScratchType
  viewLength : Nat

/-- `make_scratch(nothing, T, len)`, `base/sort.jl:503-506`. -/
def makeScratchNothing (target : ScratchType) (length : Nat) : ScratchResult :=
  let v := ⟨target, length⟩
  ⟨v, target, length⟩

/-- `make_scratch(scratch::Vector{T}, T, len)`, `base/sort.jl:507-510`. -/
def makeScratchSame (scratch : ScratchVector) (length : Nat) : ScratchResult :=
  let backing := { scratch with length := max scratch.length length }
  ⟨backing, scratch.type, backing.length⟩

/-- `make_scratch(scratch::Vector, T, len)`, `base/sort.jl:511-516`: compute
the backing length in bytes, resize, then reinterpret. -/
def makeScratchOther (scratch : ScratchVector) (target : ScratchType) (length : Nat) : Jl ScratchResult :=
  let bytesNeeded := length * target.bytes
  let backingLength := bytesNeeded / scratch.type.bytes
  let backing := { scratch with length := max scratch.length backingLength }
  if scratch.type.bits && target.bits && target.bytes > 0 &&
      (backing.length * scratch.type.bytes) % target.bytes = 0 then
    .ok ⟨backing, target, backing.length * scratch.type.bytes / target.bytes⟩
  else .error (.argumentError "cannot reinterpret")

def MakeScratchCorrect : Prop :=
  (∀ t n, (makeScratchNothing t n).backing.length = n ∧
    (makeScratchNothing t n).viewLength = n) ∧
  (∀ s n, (makeScratchSame s n).backing.length = max s.length n ∧
    (makeScratchSame s n).viewLength = max s.length n) ∧
  (∀ s t n r, makeScratchOther s t n = .ok r →
    r.backing.length ≥ s.length ∧ r.viewType = t)

theorem makeScratchCorrect : MakeScratchCorrect := by
  refine ⟨by simp [makeScratchNothing], by simp [makeScratchSame], ?_⟩
  intro s t n r h
  simp only [makeScratchOther] at h
  split at h
  · cases h
    exact ⟨Nat.le_max_left _ _, rfl⟩
  · contradiction

end JuliaLean.SortTuplesCov
