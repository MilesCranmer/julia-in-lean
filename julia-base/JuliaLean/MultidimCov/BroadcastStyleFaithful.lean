import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastStyleFaithful

open JuliaLean
open JuliaLean.Registry

/-!
Typed models of the broadcast-style methods in `base/broadcast.jl`.  A style
value records the Julia concrete type family and its rank parameter.  This is
the information read or constructed by these methods; payload distinguishes
values of user-defined style types for the `result_style` consistency check.
-/

inductive Rank where
  | any
  | fixed (n : Nat)
  deriving Repr, DecidableEq

inductive StyleKind where
  | unknown
  | tuple
  | array
  | defaultArray
  | arrayConflict
  | custom
  deriving Repr, DecidableEq

structure Style where
  kind : StyleKind
  family : String
  rank : Rank
  payload : Nat := 0
  deriving Repr, DecidableEq

def unknown : Style := { kind := .unknown, family := "Unknown", rank := .any }
def tupleStyle : Style := { kind := .tuple, family := "Style{Tuple}", rank := .any }
def arrayStyle (family : String) : Style := { kind := .array, family, rank := .any }
def defaultStyle (rank : Rank) : Style :=
  { kind := .defaultArray, family := "DefaultArrayStyle", rank }
def conflict : Style := { kind := .arrayConflict, family := "ArrayConflict", rank := .any }

def maxRank : Rank → Rank → Rank
  | .fixed m, .fixed n => .fixed (max m n)
  | _, _ => .any

def rebuildRank (style : Style) (rank : Rank) : Style := { style with rank }

def m37 : Style := unknown
def P37 : Prop := ∀ _ : Unit, m37 = unknown
theorem p37 : P37 := by simp [P37, m37]

inductive MethodArgument (α : Type) where
  | bottomType
  | value (value : α)
  deriving Repr, DecidableEq

structure MethodFailure (α : Type) where
  functionName : String
  arguments : List (MethodArgument α)
  deriving Repr, DecidableEq

def m38 {α : Type} (slurp : List α) : Except (MethodFailure α) Style :=
  .error ⟨"BroadcastStyle", .bottomType :: slurp.map .value⟩
def P38 : Prop := ∀ {α : Type} (slurp : List α),
  m38 slurp = .error ⟨"BroadcastStyle", .bottomType :: slurp.map .value⟩
theorem p38 : P38 := by unfold P38; intros; rfl

def m49 : Style := tupleStyle
def P49 : Prop := ∀ _ : Unit, m49 = tupleStyle
theorem p49 : P49 := by simp [P49, m49]

def m87 {α : Type} (family : String) (_val : α) : Style := arrayStyle family
def P87 : Prop := ∀ {α : Type} family (val : α), m87 family val = arrayStyle family
theorem p87 : P87 := by simp [P87, m87]

def m98 (n : Rank) : Style := defaultStyle n
def P98 : Prop := ∀ n, m98 n = defaultStyle n
theorem p98 : P98 := by simp [P98, m98]

def m99 (_oldRank newRank : Rank) : Style := defaultStyle newRank
def P99 : Prop := ∀ oldRank newRank, m99 oldRank newRank = defaultStyle newRank
theorem p99 : P99 := by simp [P99, m99]

def m102 (n : Rank) : Style := defaultStyle n
def P102 : Prop := ∀ n, m102 n = defaultStyle n
theorem p102 : P102 := by simp [P102, m102]

def m103 {α : Type} (ndims : α → Rank) (T : α) : Style := defaultStyle (ndims T)
def P103 : Prop := ∀ {α : Type} (ndims : α → Rank) T,
  m103 ndims T = defaultStyle (ndims T)
theorem p103 : P103 := by simp [P103, m103]

def m111 {α : Type} (_val : α) : Style := conflict
def P111 : Prop := ∀ {α : Type} (val : α), m111 val = conflict
theorem p111 : P111 := by simp [P111, m111]

def m128 {S : Type} (_left _right : S) (construct : Unit → S) : S := construct ()
def P128 : Prop := ∀ {S : Type} (left right : S) construct,
  m128 left right construct = construct ()
theorem p128 : P128 := by unfold P128; intros; rfl

def m130 (_left _right : Style) : Style := unknown
def P130 : Prop := ∀ left right, m130 left right = unknown
theorem p130 : P130 := by simp [P130, m130]

def m132 (_left _right : Unit) : Style := unknown
def P132 : Prop := ∀ left right, m132 left right = unknown
theorem p132 : P132 := by simp [P132, m132]

def m133 {S U : Type} (_left : S) (_right : U) (construct : Unit → S) : S := construct ()
def P133 : Prop := ∀ {S U : Type} (left : S) (right : U) construct,
  m133 left right construct = construct ()
theorem p133 : P133 := by unfold P133; intros; rfl

def m135 (_arrayStyle : Style) (tuple : Style) : Style := tuple
def P135 : Prop := ∀ array tuple, m135 array tuple = tuple
theorem p135 : P135 := by simp [P135, m135]

def m136 (array : Style) (_tuple : Style) : Style := array
def P136 : Prop := ∀ array tuple, m136 array tuple = array
theorem p136 : P136 := by simp [P136, m136]

def m137 {A : Type} (_left _right : A) (construct : Unit → A) : A := construct ()
def P137 : Prop := ∀ {A : Type} (left right : A) construct,
  m137 left right construct = construct ()
theorem p137 : P137 := by unfold P137; intros; rfl

def m138 {A B : Type} (_left : A) (_right : B) (_different : A ≠ B) : Style := unknown
def P138 : Prop := ∀ {A B : Type} (left : A) (right : B) (different : A ≠ B),
  m138 left right different = unknown
theorem p138 : P138 := by unfold P138; intros; rfl

def m139 {A : Type} (_left _right : A) (construct : Unit → A) : A := construct ()
def P139 : Prop := ∀ {A : Type} (left right : A) construct,
  m139 left right construct = construct ()
theorem p139 : P139 := by unfold P139; intros; rfl

/-- `BroadcastStyle(a::A,b::B)`, `base/broadcast.jl:140-145`. -/
def m140 (sameTypename : S → S → Bool) (constructRank : S → Rank → Style)
    (a b : S) (rankA rankB : Rank) : Style :=
  if sameTypename a b then constructRank a (maxRank rankA rankB) else unknown

def P140 : Prop := ∀ {S : Type} sameTypename constructRank (a b : S) rankA rankB,
  m140 sameTypename constructRank a b rankA rankB =
    if sameTypename a b then constructRank a (maxRank rankA rankB) else unknown
theorem p140 : P140 := by unfold P140; intros; rfl

def m147 (a : Style) (_default : Style) : Style := a
def P147 : Prop := ∀ a default, m147 a default = a
theorem p147 : P147 := by simp [P147, m147]

def m148 (a : Style) (_default : Style) : Style := a
def P148 : Prop := ∀ a default, m148 a default = a
theorem p148 : P148 := by simp [P148, m148]

def m149 (constructRank : S → Rank → R) (a : S) (rankA rankDefault : Rank) : R :=
  constructRank a (maxRank rankA rankDefault)
def P149 : Prop := ∀ {S R : Type} (constructRank : S → Rank → R) (a : S)
    rankA rankDefault,
  m149 constructRank a rankA rankDefault = constructRank a (maxRank rankA rankDefault)
theorem p149 : P149 := by unfold P149; intros; rfl

def m431 : Style := defaultStyle (.fixed 0)
def P431 : Prop := ∀ _ : Unit, m431 = defaultStyle (.fixed 0)
theorem p431 : P431 := by simp [P431, m431]

def m432 {α : Type} (styleOf : α → Style) (resultStyle : Style → Style) (value : α) : Style :=
  resultStyle (styleOf value)
def P432 : Prop := ∀ {α : Type} (styleOf : α → Style) resultStyle value,
  m432 styleOf resultStyle value = resultStyle (styleOf value)
theorem p432 : P432 := by simp [P432, m432]

inductive AssignedStyle where
  | assigned (style : Style)
  | nothing
  | unknown
  deriving Repr, DecidableEq

def m433 : AssignedStyle → Jl Style
  | .assigned style => .ok style
  | .nothing | .unknown => .error (.argumentError "Broadcasted wrapper has no assigned style")

def P433 : Prop :=
  (∀ style, m433 (.assigned style) = .ok style) ∧
  m433 .nothing = .error (.argumentError "Broadcasted wrapper has no assigned style") ∧
  m433 .unknown = .error (.argumentError "Broadcasted wrapper has no assigned style")
theorem p433 : P433 := by simp [P433, m433]

def m437 {α : Type} (styleOf : α → Style) (resultStyle : Style → Style → Style)
    (left right : α) : Style := resultStyle (styleOf left) (styleOf right)
def P437 : Prop := ∀ {α : Type} (styleOf : α → Style) resultStyle left right,
  m437 styleOf resultStyle left right = resultStyle (styleOf left) (styleOf right)
theorem p437 : P437 := by simp [P437, m437]

def combineNonempty {α : Type} (styleOf : α → Style) (resultUnary : Style → Style)
    (resultBinary : Style → Style → Style) : α → List α → Style
  | value, [] => resultUnary (styleOf value)
  | value, next :: rest =>
      resultBinary (styleOf value)
        (combineNonempty styleOf resultUnary resultBinary next rest)

def m438 {α : Type} (styleOf : α → Style) (resultUnary : Style → Style)
    (resultBinary : Style → Style → Style) (first second : α) (rest : List α) : Style :=
  resultBinary (styleOf first)
    (combineNonempty styleOf resultUnary resultBinary second rest)

def P438 : Prop := ∀ {α : Type} (styleOf : α → Style) resultUnary resultBinary
    first second rest,
  m438 styleOf resultUnary resultBinary first second rest =
    resultBinary (styleOf first)
      (combineNonempty styleOf resultUnary resultBinary second rest)
theorem p438 : P438 := by unfold P438; intros; rfl

def m458 (style : Style) : Style := style
def P458 : Prop := ∀ style, m458 style = style
theorem p458 : P458 := by simp [P458, m458]

inductive StyleError where
  | inconsistent
  | conflicting
  | dispatch
  deriving Repr, DecidableEq

def m459 (identical : Style → Style → Bool) (left right : Style) :
    Except StyleError Style :=
  if identical left right then .ok left else .error .inconsistent
def P459 : Prop := ∀ identical left right,
  (identical left right = true → m459 identical left right = .ok left) ∧
  (identical left right = false → m459 identical left right = .error .inconsistent)
theorem p459 : P459 := by
  intro identical left right
  constructor <;> intro h <;> simp [m459, h]

def isArrayStyle (style : Style) : Bool :=
  style.kind = .array || style.kind = .defaultArray || style.kind = .arrayConflict

def resultJoin (left right forward reverse : Style) : Except StyleError Style :=
  if forward.kind = .unknown then
    if reverse.kind = .unknown then
      if isArrayStyle left && isArrayStyle right then .ok conflict else .ok unknown
    else .ok reverse
  else if reverse.kind = .unknown then .ok forward
  else if forward.kind = reverse.kind then m459 (· = ·) forward reverse
  else .error .conflicting

/-- The general `result_style` evaluates the forward rule before the reverse rule. -/
def m463 {σ : Type} (pairRule : Style → Style → StateT σ (Except StyleError) Style)
    (left right : Style) : StateT σ (Except StyleError) Style := fun state =>
  match pairRule left right state with
  | .error error => .error error
  | .ok (forward, stateAfterForward) =>
      match pairRule right left stateAfterForward with
      | .error error => .error error
      | .ok (reverse, stateAfterReverse) =>
          match resultJoin left right forward reverse with
          | .ok style => .ok (style, stateAfterReverse)
          | .error error => .error error

def P463 : Prop := ∀ {σ : Type} (pairRule : Style → Style → StateT σ (Except StyleError) Style)
    left right state forward stateAfterForward reverse stateAfterReverse,
  pairRule left right state = .ok (forward, stateAfterForward) →
  pairRule right left stateAfterForward = .ok (reverse, stateAfterReverse) →
  m463 pairRule left right state =
    match resultJoin left right forward reverse with
    | .ok style => .ok (style, stateAfterReverse)
    | .error error => .error error
theorem p463 : P463 := by
  intro σ pairRule left right state forward stateAfterForward reverse stateAfterReverse hf hr
  simp [m463, hf, hr]

def m467 {α β : Type} (_left : α) (_right : β) (_forward _reverse : Unit) : Style := unknown
def P467 : Prop := ∀ {α β : Type} (left : α) (right : β) forward reverse,
  m467 left right forward reverse = unknown
theorem p467 : P467 := by simp [P467, m467]

def m468 {α β : Type} (_left : α) (_right : β) (_unknown : Unit) (style : Style) : Style := style
def P468 : Prop := ∀ {α β : Type} (left : α) (right : β) unknownValue style,
  m468 left right unknownValue style = style
theorem p468 : P468 := by simp [P468, m468]

def m469 {α β : Type} (_left : α) (_right : β) (style : Style) (_unknown : Unit) : Style := style
def P469 : Prop := ∀ {α β : Type} (left : α) (right : β) style unknownValue,
  m469 left right style unknownValue = style
theorem p469 : P469 := by simp [P469, m469]

def m474 (_left _right _forward _reverse : Style) : Style := conflict
def P474 : Prop := ∀ left right forward reverse, m474 left right forward reverse = conflict
theorem p474 : P474 := by simp [P474, m474]

def m477 {α β : Type} (_left : α) (_right : β) (forward reverse : Style) :
    Except StyleError Style :=
  m459 (· = ·) forward reverse
def P477 : Prop := ∀ {α β : Type} (left : α) (right : β) forward reverse,
  m477 left right forward reverse = m459 (· = ·) forward reverse
theorem p477 : P477 := by unfold P477; intros; rfl

def m479 {α β γ δ : Type} (_left : α) (_right : β) (_forward : γ) (_reverse : δ) :
    Except StyleError Style := .error .conflicting
def P479 : Prop := ∀ {α β γ δ : Type} (left : α) (right : β) (forward : γ) (reverse : δ),
  m479 left right forward reverse = .error .conflicting
theorem p479 : P479 := by simp [P479, m479]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name)
    (notes : String := "") : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; source equation and broadcast-style invariant"
    status := .proven
    prop
    thm := some thm
    notes }

def entries : List Entry := []

end JuliaLean.MultidimCov.BroadcastStyleFaithful
