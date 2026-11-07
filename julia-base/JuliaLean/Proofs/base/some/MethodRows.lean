import JuliaLean.base.some
import JuliaLean.Registry.Types

/-! Method-specific properties for `base/some.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.SomeRows

open JuliaLean.Registry
open JuliaLean.MissingChar

abbrev P15 : Prop := ∀ (α : Type) (T : α), m15 T = SomeV.mk T
theorem p15 : P15 := by simp [P15, m15]

abbrev P17 : Prop := ∀ (α : Type) (typesplit : α → α → α) (nothing T : α),
  m17 typesplit nothing T = typesplit T nothing
theorem p17 : P17 := by simp [P17, m17]

abbrev P18 : Prop := ∀ (α : Type) (unionNothing : α → α) (S : α),
  m18 unionNothing S = unionNothing S
theorem p18 : P18 := by simp [P18, m18]

abbrev P19 : Prop := ∀ (α : Type) (nonnothing : α → α) (supertype : α → α → Bool)
    (promote : α → α → α) (unionNothing : α → α) (any T S : α),
  m19 nonnothing supertype promote unionNothing any T S =
    let R := nonnothing T
    if supertype R T then any else unionNothing (promote R S)
theorem p19 : P19 := by simp [P19, m19]

abbrev P27 : Prop := ∀ (α : Type) (nonnothing : α → α) (supertype isBottom : α → α → Bool)
    (T bottom : α),
  m27 nonnothing supertype isBottom T bottom =
    let R := nonnothing T
    if supertype R T then .error (.errorException "could not compute non-nothing type")
    else if isBottom R bottom then .error (.errorException "cannot convert a value to nothing for assignment")
    else .ok R
theorem p27 : P27 := by simp [P27, m27]

abbrev P34 : Prop := ∀ (α : Type) (x : α), m34 x = x
theorem p34 : P34 := by simp [P34, m34]

abbrev P35 : Prop := ∀ (τ σ α β : Type) (checked : τ → RJ σ)
    (convert : σ → α → RJ β) (T : τ) (x : α),
  m35 checked convert T x = (checked T).bind (fun R => convert R x)
theorem p35 : P35 := by
  unfold P35 m35
  intros
  rfl

abbrev P36 : Prop := ∀ (α : Type) (x : SomeV α), m36 x = x
theorem p36 : P36 := by simp [P36, m36]

abbrev P37 : Prop := ∀ (α β : Type) (convert : α → RJ β) (x : SomeV α),
  m37 convert x = (convert x.value).map SomeV.mk
theorem p37 : P37 := by
  unfold P37 m37
  intro α β convert x
  cases convert x.value <;> rfl

abbrev P54 : Prop := ∀ (α : Type) (x : JV α), m54 x = .ok x
theorem p54 : P54 := by simp [P54, m54]

abbrev P55 : Prop := ∀ α : Type, m55 α = .error (.argumentError "nothing passed to notnothing")
theorem p55 : P55 := by simp [P55, m55]

abbrev P67 : Prop := ∀ (α : Type) (x : JV α), m67 x = x.isNothing
theorem p67 : P67 := by simp [P67, m67]

abbrev P99 : Prop := ∀ α : Type, m99 α = .error (.argumentError "No value arguments present")
theorem p99 : P99 := by simp [P99, m99]

abbrev P100 : Prop := ∀ (α : Type) ys, m100 (α := α) ys = something ys
theorem p100 : P100 := by simp [P100, m100]

abbrev P101 : Prop := ∀ (α : Type) value ys, m101 (.some value : JV α) ys = .ok value
theorem p101 : P101 := by simp [P101, m101]

abbrev P102 : Prop := ∀ (α : Type) x ys, m102 (α := α) x ys = .ok x
theorem p102 : P102 := by simp [P102, m102]

abbrev P138 : Prop := ∀ (α : Type) args,
  m138 (α := α) args = args.reverse.foldl (fun expr value => .branch value expr) .fail
theorem p138 : P138 := by simp [P138, m138]

abbrev P169 : Prop := ∀ (α β : Type) (eq : α → α → β) (a b : SomeV α),
  m169 eq a b = eq a.value b.value
theorem p169 : P169 := by simp [P169, m169]

private def mk (line : Nat) (name : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"reducecov-some-l{line}", juliaFile := "base/some.jl", juliaFns := [name]
    statement := s!"The method at base/some.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/some.jl:{line}", status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.ReduceCov.SomeRows
