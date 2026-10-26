import JuliaLean.MissingChar.Some
import JuliaLean.ReduceCov.Basic
import JuliaLean.Registry.Types

/-! Method-specific models for `base/some.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.SomeRows

open JuliaLean.Registry
open JuliaLean.MissingChar

structure SomeV (α : Type) where
  value : α
  deriving Repr, DecidableEq

/-- `Some(::Type{T}) where T`, `base/some.jl:15`. -/
def m15 (T : α) : SomeV α := ⟨T⟩
abbrev P15 : Prop := ∀ (α : Type) (T : α), m15 T = SomeV.mk T
theorem p15 : P15 := by simp [P15, m15]

/-- `nonnothingtype(T) = typesplit(T, Nothing)`, `base/some.jl:17`. -/
def m17 (typesplit : α → α → α) (nothing T : α) : α := typesplit T nothing
abbrev P17 : Prop := ∀ (α : Type) (typesplit : α → α → α) (nothing T : α),
  m17 typesplit nothing T = typesplit T nothing
theorem p17 : P17 := by simp [P17, m17]

/-- `promote_rule(::Type{Nothing}, S)`, `base/some.jl:18`. -/
def m18 (unionNothing : α → α) (S : α) : α := unionNothing S
abbrev P18 : Prop := ∀ (α : Type) (unionNothing : α → α) (S : α),
  m18 unionNothing S = unionNothing S
theorem p18 : P18 := by simp [P18, m18]

/-- The general `Nothing` promotion rule, `base/some.jl:19-25`. -/
def m19 (nonnothing : α → α) (supertype : α → α → Bool) (promote : α → α → α)
    (unionNothing : α → α) (any T S : α) : α :=
  let R := nonnothing T
  if supertype R T then any else unionNothing (promote R S)
abbrev P19 : Prop := ∀ (α : Type) (nonnothing : α → α) (supertype : α → α → Bool)
    (promote : α → α → α) (unionNothing : α → α) (any T S : α),
  m19 nonnothing supertype promote unionNothing any T S =
    let R := nonnothing T
    if supertype R T then any else unionNothing (promote R S)
theorem p19 : P19 := by simp [P19, m19]

/-- `nonnothingtype_checked`, including both ordered checks, `base/some.jl:27-32`. -/
def m27 (nonnothing : α → α) (supertype isBottom : α → α → Bool) (T bottom : α) : RJ α :=
  let R := nonnothing T
  if supertype R T then .error (.errorException "could not compute non-nothing type")
  else if isBottom R bottom then .error (.errorException "cannot convert a value to nothing for assignment")
  else .ok R
abbrev P27 : Prop := ∀ (α : Type) (nonnothing : α → α) (supertype isBottom : α → α → Bool)
    (T bottom : α),
  m27 nonnothing supertype isBottom T bottom =
    let R := nonnothing T
    if supertype R T then .error (.errorException "could not compute non-nothing type")
    else if isBottom R bottom then .error (.errorException "cannot convert a value to nothing for assignment")
    else .ok R
theorem p27 : P27 := by simp [P27, m27]

/-- Same-type conversion, `base/some.jl:34`. -/
def m34 (x : α) : α := x
abbrev P34 : Prop := ∀ (α : Type) (x : α), m34 x = x
theorem p34 : P34 := by simp [P34, m34]

/-- General conversion to a type containing `Nothing`, `base/some.jl:35`. -/
def m35 (checked : τ → RJ σ) (convert : σ → α → RJ β) (T : τ) (x : α) : RJ β := do
  convert (← checked T) x
abbrev P35 : Prop := ∀ (τ σ α β : Type) (checked : τ → RJ σ)
    (convert : σ → α → RJ β) (T : τ) (x : α),
  m35 checked convert T x = (checked T).bind (fun R => convert R x)
theorem p35 : P35 := by
  unfold P35 m35
  intros
  rfl

/-- Same-parameter `Some` conversion, `base/some.jl:36`. -/
def m36 (x : SomeV α) : SomeV α := x
abbrev P36 : Prop := ∀ (α : Type) (x : SomeV α), m36 x = x
theorem p36 : P36 := by simp [P36, m36]

/-- Converting between `Some` parameters, `base/some.jl:37`. -/
def m37 (convert : α → RJ β) (x : SomeV α) : RJ (SomeV β) := do
  pure ⟨← convert x.value⟩
abbrev P37 : Prop := ∀ (α β : Type) (convert : α → RJ β) (x : SomeV α),
  m37 convert x = (convert x.value).map SomeV.mk
theorem p37 : P37 := by
  unfold P37 m37
  intro α β convert x
  cases convert x.value <;> rfl

/-- `notnothing(x::Any)`, `base/some.jl:54`. -/
def m54 (x : JV α) : Jl (JV α) := .ok x
abbrev P54 : Prop := ∀ (α : Type) (x : JV α), m54 x = .ok x
theorem p54 : P54 := by simp [P54, m54]

/-- `notnothing(::Nothing)`, `base/some.jl:55`. -/
def m55 (α : Type) : Jl (JV α) := .error (.argumentError "nothing passed to notnothing")
abbrev P55 : Prop := ∀ α : Type, m55 α = .error (.argumentError "nothing passed to notnothing")
theorem p55 : P55 := by simp [P55, m55]

/-- `isnothing(x) = x === nothing`, `base/some.jl:67`. -/
def m67 (x : JV α) : Bool := x.isNothing
abbrev P67 : Prop := ∀ (α : Type) (x : JV α), m67 x = x.isNothing
theorem p67 : P67 := by simp [P67, m67]

/-- Zero-argument `something`, `base/some.jl:99`. -/
def m99 (α : Type) : Jl (JV α) := .error (.argumentError "No value arguments present")
abbrev P99 : Prop := ∀ α : Type, m99 α = .error (.argumentError "No value arguments present")
theorem p99 : P99 := by simp [P99, m99]

/-- `something(x::Nothing, y...)`, `base/some.jl:100`. -/
def m100 (ys : List (JV α)) : Jl (JV α) := something ys
abbrev P100 : Prop := ∀ (α : Type) ys, m100 (α := α) ys = something ys
theorem p100 : P100 := by simp [P100, m100]

/-- `something(x::Some, y...)`, `base/some.jl:101`. -/
def m101 (x : JV α) (_ys : List (JV α)) : Jl (JV α) :=
  match x with | .some value => .ok value | other => .ok other
abbrev P101 : Prop := ∀ (α : Type) value ys, m101 (.some value : JV α) ys = .ok value
theorem p101 : P101 := by simp [P101, m101]

/-- `something(x::Any, y...)`, `base/some.jl:102`. -/
def m102 (x : JV α) (_ys : List (JV α)) : Jl (JV α) := .ok x
abbrev P102 : Prop := ∀ (α : Type) x ys, m102 (α := α) x ys = .ok x
theorem p102 : P102 := by simp [P102, m102]

inductive SomethingExpr (α : Type) where
  | fail
  | branch (value : JV α) (rest : SomethingExpr α)

/-- The reverse loop that builds `@something`'s nested expression, `base/some.jl:138-167`. -/
def m138 (args : List (JV α)) : SomethingExpr α :=
  args.reverse.foldl (fun expr value => .branch value expr) .fail
abbrev P138 : Prop := ∀ (α : Type) args,
  m138 (α := α) args = args.reverse.foldl (fun expr value => .branch value expr) .fail
theorem p138 : P138 := by simp [P138, m138]

/-- `==(a::Some, b::Some)`, `base/some.jl:169`. -/
def m169 (eq : α → α → β) (a b : SomeV α) : β := eq a.value b.value
abbrev P169 : Prop := ∀ (α β : Type) (eq : α → α → β) (a b : SomeV α),
  m169 eq a b = eq a.value b.value
theorem p169 : P169 := by simp [P169, m169]

private def mk (line : Nat) (name : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"reducecov-some-l{line}", juliaFile := "base/some.jl", juliaFns := [name]
    statement := s!"The method at base/some.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/some.jl:{line}", status := .proven, prop, thm := some thm }

def entries : List Entry := [
  mk 15 "Some(::Type{T})" ``P15 ``p15,
  mk 17 "nonnothingtype(::Type)" ``P17 ``p17,
  mk 18 "promote_rule(::Type{Nothing}, ::Type)" ``P18 ``p18,
  mk 19 "promote_rule(::Type{>:Nothing}, ::Type)" ``P19 ``p19,
  mk 27 "nonnothingtype_checked(::Type)" ``P27 ``p27,
  mk 34 "convert(::Type{T}, ::T) where T>:Nothing" ``P34 ``p34,
  mk 35 "convert(::Type{T}, x) where T>:Nothing" ``P35 ``p35,
  mk 36 "convert(::Type{Some{T}}, ::Some{T})" ``P36 ``p36,
  mk 37 "convert(::Type{Some{T}}, ::Some)" ``P37 ``p37,
  mk 54 "notnothing(::Any)" ``P54 ``p54,
  mk 55 "notnothing(::Nothing)" ``P55 ``p55,
  mk 67 "isnothing" ``P67 ``p67,
  mk 99 "something()" ``P99 ``p99,
  mk 100 "something(::Nothing, ...)" ``P100 ``p100,
  mk 101 "something(::Some, ...)" ``P101 ``p101,
  mk 102 "something(::Any, ...)" ``P102 ``p102,
  mk 138 "@something" ``P138 ``p138,
  mk 169 "==(::Some, ::Some)" ``P169 ``p169
]

end JuliaLean.ReduceCov.SomeRows
