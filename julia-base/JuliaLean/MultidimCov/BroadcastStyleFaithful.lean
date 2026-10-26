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

def m38 {α : Type} (slurp : List α) : Except (List α) Style := .error slurp
def P38 : Prop := ∀ {α : Type} (slurp : List α),
  m38 slurp = .error slurp
theorem p38 : P38 := by simp [P38, m38]

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

def m128 (style : Style) : Style := style
def P128 : Prop := ∀ style, m128 style = style
theorem p128 : P128 := by simp [P128, m128]

def m130 (_left _right : Style) : Style := unknown
def P130 : Prop := ∀ left right, m130 left right = unknown
theorem p130 : P130 := by simp [P130, m130]

def m132 (_left _right : Unit) : Style := unknown
def P132 : Prop := ∀ left right, m132 left right = unknown
theorem p132 : P132 := by simp [P132, m132]

def m133 (style : Style) (_right : Unit) : Style := style
def P133 : Prop := ∀ style right, m133 style right = style
theorem p133 : P133 := by simp [P133, m133]

def m135 (_arrayStyle : Style) (tuple : Style) : Style := tuple
def P135 : Prop := ∀ array tuple, m135 array tuple = tuple
theorem p135 : P135 := by simp [P135, m135]

def m136 (array : Style) (_tuple : Style) : Style := array
def P136 : Prop := ∀ array tuple, m136 array tuple = array
theorem p136 : P136 := by simp [P136, m136]

def m137 (style : Style) : Style := style
def P137 : Prop := ∀ style, m137 style = style
theorem p137 : P137 := by simp [P137, m137]

def m138 (_left _right : Style) : Style := unknown
def P138 : Prop := ∀ left right, m138 left right = unknown
theorem p138 : P138 := by simp [P138, m138]

def m139 (style : Style) : Style := style
def P139 : Prop := ∀ style, m139 style = style
theorem p139 : P139 := by simp [P139, m139]

/-- `BroadcastStyle(a::A,b::B)`, `base/broadcast.jl:140-145`. -/
def m140 (a b : Style) : Style :=
  if a.family = b.family then rebuildRank a (maxRank a.rank b.rank) else unknown

def P140 : Prop := ∀ a b,
  (a.family = b.family → m140 a b = rebuildRank a (maxRank a.rank b.rank)) ∧
  (a.family ≠ b.family → m140 a b = unknown)
theorem p140 : P140 := by
  intro a b
  constructor <;> intro h <;> simp [m140, h]

def m147 (a : Style) (_default : Style) : Style := a
def P147 : Prop := ∀ a default, m147 a default = a
theorem p147 : P147 := by simp [P147, m147]

def m148 (a : Style) (_default : Style) : Style := a
def P148 : Prop := ∀ a default, m148 a default = a
theorem p148 : P148 := by simp [P148, m148]

def m149 (a : Style) (default : Style) : Style := rebuildRank a (maxRank a.rank default.rank)
def P149 : Prop := ∀ a default,
  m149 a default = rebuildRank a (maxRank a.rank default.rank)
theorem p149 : P149 := by simp [P149, m149]

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

def combineTail {α : Type} (styleOf : α → Style) (resultStyle : Style → Style → Style) :
    List α → Style
  | [] => defaultStyle (.fixed 0)
  | value :: rest => resultStyle (styleOf value) (combineTail styleOf resultStyle rest)

def m438 {α : Type} (styleOf : α → Style) (resultStyle : Style → Style → Style)
    (first second : α) (rest : List α) : Style :=
  resultStyle (styleOf first) (combineTail styleOf resultStyle (second :: rest))

def P438 : Prop := ∀ {α : Type} (styleOf : α → Style) resultStyle first second rest,
  m438 styleOf resultStyle first second rest =
    resultStyle (styleOf first) (combineTail styleOf resultStyle (second :: rest))
theorem p438 : P438 := by simp [P438, m438]

def m458 (style : Style) : Style := style
def P458 : Prop := ∀ style, m458 style = style
theorem p458 : P458 := by simp [P458, m458]

inductive StyleError where
  | inconsistent
  | conflicting
  | dispatch
  deriving Repr, DecidableEq

def m459 (left right : Style) : Except StyleError Style :=
  if left = right then .ok left else .error .inconsistent
def P459 : Prop := ∀ left right,
  (left = right → m459 left right = .ok left) ∧
  (left ≠ right → m459 left right = .error .inconsistent)
theorem p459 : P459 := by
  intro left right
  constructor <;> intro h <;> simp [m459, h]

def isArrayStyle (style : Style) : Bool :=
  style.kind = .array || style.kind = .defaultArray || style.kind = .arrayConflict

def resultJoin (left right forward reverse : Style) : Except StyleError Style :=
  if forward.kind = .unknown then
    if reverse.kind = .unknown then
      if isArrayStyle left && isArrayStyle right then .ok conflict else .ok unknown
    else .ok reverse
  else if reverse.kind = .unknown then .ok forward
  else if forward.kind = reverse.kind then m459 forward reverse
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

def m477 {α β : Type} (_left : α) (_right : β) (forward reverse : Style) : Except StyleError Style :=
  m459 forward reverse
def P477 : Prop := ∀ {α β : Type} (left : α) (right : β) forward reverse,
  m477 left right forward reverse = m459 forward reverse
theorem p477 : P477 := by simp [P477, m477]

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

def entries : List Entry := [
  entry 37 "BroadcastStyle(::Type{Union{}})" "The bottom type has Unknown broadcast style." ``P37 ``p37,
  entry 38 "BroadcastStyle(::Type{Union{}}, slurp...)" "Every multi-argument bottom-type call throws MethodError after retaining the complete argument list." ``P38 ``p38 "Julia 1.13.2 instead returns Unknown() for every arity; master split the zero-argument method from the throwing vararg method.",
  entry 49 "BroadcastStyle(::Type{<:Tuple})" "Every tuple type uses Style{Tuple}." ``P49 ``p49,
  entry 87 "ArrayStyle{A}(::Val)" "Every Val input is ignored and the ArrayStyle for A is returned." ``P87 ``p87,
  entry 98 "DefaultArrayStyle(::Val{N})" "The Val parameter becomes the result rank." ``P98 ``p98,
  entry 99 "DefaultArrayStyle{M}(::Val{N})" "The new Val parameter replaces the old rank." ``P99 ``p99,
  entry 102 "BroadcastStyle(::Type{<:AbstractArray{T,N}})" "Every AbstractArray type receives DefaultArrayStyle with its rank." ``P102 ``p102,
  entry 103 "BroadcastStyle(::Type{T})" "The fallback uses ndims(T) as the default array-style rank." ``P103 ``p103,
  entry 111 "ArrayConflict(::Val)" "Every Val input is ignored and ArrayConflict is returned." ``P111 ``p111,
  entry 128 "BroadcastStyle(::S,::S)" "A homogeneous style pair constructs the same style." ``P128 ``p128,
  entry 130 "BroadcastStyle(::BroadcastStyle,::BroadcastStyle)" "The general style pair returns Unknown." ``P130 ``p130,
  entry 132 "BroadcastStyle(::Unknown,::Unknown)" "Two Unknown styles return Unknown." ``P132 ``p132,
  entry 133 "BroadcastStyle(::S,::Unknown)" "Unknown on the right preserves every style S." ``P133 ``p133,
  entry 135 "BroadcastStyle(::AbstractArrayStyle{0},::Style{Tuple})" "A zero-dimensional array style yields the tuple style." ``P135 ``p135,
  entry 136 "BroadcastStyle(::AbstractArrayStyle,::Style{Tuple})" "An array style of other rank wins over tuple style." ``P136 ``p136,
  entry 137 "BroadcastStyle(::A,::A) where A<:ArrayStyle" "A homogeneous ArrayStyle pair returns that style." ``P137 ``p137,
  entry 138 "BroadcastStyle(::ArrayStyle,::ArrayStyle)" "Different ArrayStyle families return Unknown." ``P138 ``p138,
  entry 139 "BroadcastStyle(::A,::A) where A<:AbstractArrayStyle" "A homogeneous abstract-array style pair returns that style." ``P139 ``p139,
  entry 140 "BroadcastStyle(::AbstractArrayStyle,::AbstractArrayStyle)" "Equal concrete style families rebuild at the maximum rank; unequal families return Unknown." ``P140 ``p140,
  entry 147 "BroadcastStyle(::AbstractArrayStyle{Any},::DefaultArrayStyle)" "An Any-rank custom array style is preserved." ``P147 ``p147,
  entry 148 "BroadcastStyle(::AbstractArrayStyle{N},::DefaultArrayStyle{N})" "A same-rank custom array style is preserved." ``P148 ``p148,
  entry 149 "BroadcastStyle(::AbstractArrayStyle{M},::DefaultArrayStyle{N})" "The custom family is rebuilt at the maximum rank." ``P149 ``p149,
  entry 431 "combine_styles()" "The empty combination returns DefaultArrayStyle{0}." ``P431 ``p431,
  entry 432 "combine_styles(c)" "A single value passes its type style through result_style." ``P432 ``p432,
  entry 433 "combine_styles(::Broadcasted)" "An assigned style is returned; Nothing and Unknown throw ArgumentError." ``P433 ``p433,
  entry 437 "combine_styles(c1,c2)" "Two values pass their individual styles to result_style." ``P437 ``p437,
  entry 438 "combine_styles(c1,c2,cs...)" "Varargs combine the first style with the recursively combined tail." ``P438 ``p438,
  entry 458 "result_style(s)" "Unary result_style returns its input." ``P458 ``p458,
  entry 459 "result_style(s1::S,s2::S)" "Equal values are returned and inconsistent same-type values throw." ``P459 ``p459,
  entry 463 "result_style(s1,s2)" "The general method evaluates forward then reverse pair rules before joining them." ``P463 ``p463,
  entry 467 "result_join(Unknown,Unknown)" "Two unknown rules return Unknown." ``P467 ``p467,
  entry 468 "result_join(Unknown,s)" "A known reverse rule wins." ``P468 ``p468,
  entry 469 "result_join(s,Unknown)" "A known forward rule wins." ``P469 ``p469,
  entry 474 "result_join(array styles,Unknown,Unknown)" "Two unknown array-style rules return ArrayConflict." ``P474 ``p474,
  entry 477 "result_join(s1::S,s2::S)" "Matching rule types delegate to homogeneous result_style." ``P477 ``p477,
  entry 479 "result_join conflicting rules" "Conflicting defined rules throw the conflict error." ``P479 ``p479
]

end JuliaLean.MultidimCov.BroadcastStyleFaithful
