import JuliaLean.base.missing
import JuliaLean.base.missing
import JuliaLean.base.some
import JuliaLean.Core
import JuliaLean.Registry.Types

/-! Method-specific models for `base/missing.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.MissingCov

open JuliaLean.Registry
open JuliaLean.MissingChar
abbrev P5 : Prop := ∀ u, m5 u = "missing"
theorem p5 : P5 := by simp [P5, m5]
abbrev P18 : Prop := ∀ msg, m18 msg = "MissingException: " ++ msg
theorem p18 : P18 := by simp [P18, m18]
abbrev P39 : Prop := ∀ (α : Type) (typesplit : α → α → α) (missing T : α),
  m39 typesplit missing T = typesplit T missing
theorem p39 : P39 := by simp [P39, m39]
abbrev P41 : Prop := ∀ (α : Type) (nonmissing : α → α) (supertype isBottom : α → α → Bool)
    (T bottom : α),
  m41 nonmissing supertype isBottom T bottom =
    let R := nonmissing T
    if supertype R T then .error (.errorException "could not compute non-missing type")
    else if isBottom R bottom then .error (.errorException "cannot convert a value to missing for assignment")
    else .ok R
theorem p41 : P41 := by simp [P41, m41]
abbrev P48 : Prop := ∀ (α : Type) (unionMissing : α → α) (S : α),
  m48 unionMissing S = unionMissing S
theorem p48 : P48 := by simp [P48, m48]
abbrev P49 : Prop := ∀ (α : Type) (unionNothingMissing : α → α) (S : α),
  m49 unionNothingMissing S = unionNothingMissing S
theorem p49 : P49 := by simp [P49, m49]
abbrev P50 : Prop := ∀ (α : Type) (nonnothing nonmissing : α → α)
    (supertype : α → α → Bool) (promote : α → α → α) (unionBoth : α → α)
    (any T S : α),
  m50 nonnothing nonmissing supertype promote unionBoth any T S =
    let Rn := nonnothing T
    if supertype Rn T then any
    else let Rm := nonmissing Rn; if supertype Rm Rn then any else unionBoth (promote Rm S)
theorem p50 : P50 := by simp [P50, m50]
abbrev P60 : Prop := ∀ (α : Type) (nonmissing : α → α) (supertype : α → α → Bool)
    (promote : α → α → α) (unionMissing : α → α) (any T S : α),
  m60 nonmissing supertype promote unionMissing any T S =
    let R := nonmissing T; if supertype R T then any else unionMissing (promote R S)
theorem p60 : P60 := by simp [P60, m60]
abbrev P68 : Prop := ∀ (α : Type) (x : α), m68 x = x
theorem p68 : P68 := by simp [P68, m68]
abbrev P69 : Prop := ∀ (α : Type) (x : α), m69 x = x
theorem p69 : P69 := by simp [P69, m69]
abbrev P70 : Prop := ∀ (τ σ α β : Type) (checked : τ → RJ σ)
    (convert : σ → α → RJ β) (T : τ) (x : α),
  m70 checked convert T x = (checked T).bind (fun R => convert R x)
theorem p70 : P70 := by simp [P70, m70]
abbrev P71 : Prop := ∀ (τ σ ρ α β : Type) (nonnothing : τ → RJ σ)
    (nonmissing : σ → RJ ρ) (convert : ρ → α → RJ β) (T : τ) (x : α),
  m71 nonnothing nonmissing convert T x =
    (nonnothing T).bind (fun R => (nonmissing R).bind (fun U => convert U x))
theorem p71 : P71 := by simp [P71, m71]
abbrev P74 : Prop := ∀ _ : Unit, m74 = none
theorem p74 : P74 := by intro; rfl
abbrev P76 : Prop := ∀ (α : Type) (x : α), m76 α x = none
theorem p76 : P76 := by simp [P76, m76]
abbrev P78 : Prop := ∀ (α : Type) (x : α), m78 α x = none
theorem p78 : P78 := by simp [P78, m78]
abbrev P79 : Prop := ∀ (α : Type) (x : α), m79 α x = none
theorem p79 : P79 := by simp [P79, m79]
abbrev P82 : Prop := ∀ (α : Type) (x : α), m82 α x = false
theorem p82 : P82 := by simp [P82, m82]
abbrev P83 : Prop := ∀ _ : Unit, m83 = none
theorem p83 : P83 := by intro; rfl
abbrev P85 : Prop := ∀ (α : Type) (x : α), m85 α x = none
theorem p85 : P85 := by simp [P85, m85]
abbrev P86 : Prop := ∀ _ : Unit, m86 = false
theorem p86 : P86 := by intro; rfl
abbrev P89 : Prop := ∀ _ : Unit, m89 = none
theorem p89 : P89 := by intro; rfl
abbrev P90 : Prop := ∀ _ : Unit, m90 = none
theorem p90 : P90 := by intro; rfl
abbrev P91 : Prop := ∀ _ : Unit, m91 = none
theorem p91 : P91 := by intro; rfl
abbrev P92 : Prop := ∀ (α : Type) (x : α), m92 α x = none
theorem p92 : P92 := by simp [P92, m92]
abbrev P93 : Prop := ∀ (α : Type) (x : α), m93 α x = none
theorem p93 : P93 := by simp [P93, m93]
abbrev P103 : Prop := ∀ (α : Type) (f : String), m103 α f = none
theorem p103 : P103 := by simp [P103, m103]
abbrev P106 : Prop := ∀ (α : Type) (f : String), m106 α f = .error (.methodError f)
theorem p106 : P106 := by simp [P106, m106]
abbrev P107 : Prop := ∀ (α : Type) (f : String), m107 α f = none
theorem p107 : P107 := by simp [P107, m107]
abbrev P108 : Prop := ∀ (τ σ α : Type) (checked : τ → RJ σ) (f : σ → RJ α) (T : τ),
  m108 checked f T = (checked T).bind f
theorem p108 : P108 := by simp [P108, m108]
abbrev P111 : Prop := ∀ (α : Type) (f : String), m111 α f = .error (.methodError f)
theorem p111 : P111 := by simp [P111, m111]
abbrev P112 : Prop := ∀ (τ σ ρ α : Type) (nonmissing : τ → σ) (f : σ → ρ)
    (unionMissing : ρ → α) (T : τ),
  m112 nonmissing f unionMissing T = unionMissing (f (nonmissing T))
theorem p112 : P112 := by simp [P112, m112]
abbrev P119 : Prop := ∀ (α : Type) (f : String), m119 α f = none
theorem p119 : P119 := by simp [P119, m119]
abbrev P120 : Prop := ∀ (α β : Type) (f : String) (x : β), m120 α β f x = none
theorem p120 : P120 := by simp [P120, m120]
abbrev P121 : Prop := ∀ (α β : Type) (f : String) (x : β), m121 α β f x = none
theorem p121 : P121 := by simp [P121, m121]
abbrev P125 : Prop := ∀ (α : Type) (r : α), m125 α r = none
theorem p125 : P125 := by simp [P125, m125]
abbrev P126 : Prop := ∀ (α β : Type) (x : α) (r : β), m126 α β x r = none
theorem p126 : P126 := by simp [P126, m126]
abbrev P127 : Prop := ∀ (α β : Type) (x : α) (r : β), m127 α β x r = none
theorem p127 : P127 := by simp [P127, m127]
abbrev P131 : Prop := ∀ (α : Type) (result : α), m131 result = result
theorem p131 : P131 := by simp [P131, m131]
abbrev P132 : Prop := ∀ (α β : Type) (result : α) (x : β), m132 result x = result
theorem p132 : P132 := by simp [P132, m132]
abbrev P133 : Prop := ∀ (α β : Type) (result : α) (x : β), m133 result x = result
theorem p133 : P133 := by simp [P133, m133]
abbrev P134 : Prop := ∀ (α : Type) (result : α), m134 result = result
theorem p134 : P134 := by simp [P134, m134]
abbrev P137 : Prop := ∀ (α β γ : Type) (lo : β) (hi : γ), m137 α β γ lo hi = none
theorem p137 : P137 := by simp [P137, m137]
abbrev P139 : Prop := ∀ T, m139 T =
  "cannot convert a missing value to type " ++ T ++ ": use Union{" ++ T ++ ", Missing} instead"
theorem p139 : P139 := by simp [P139, m139]
abbrev P143 : Prop := ∀ (α : Type) (s d b : Int), m143 α s d b = none
theorem p143 : P143 := by simp [P143, m143]
abbrev P144 : Prop := ∀ (α : Type) (r : α), m144 α r = none
theorem p144 : P144 := by simp [P144, m144]
abbrev P145 : Prop := ∀ T, m145 T = .error (.missingException (m139 T))
theorem p145 : P145 := by simp [P145, m145]
abbrev P147 : Prop := ∀ (τ σ α ρ β : Type) (checked : τ → RJ σ)
    (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ),
  m147 checked round T x r = (checked T).bind (fun U => round U x r)
theorem p147 : P147 := by simp [P147, m147]
abbrev P149 : Prop := ∀ (τ σ α ρ β : Type) (checked : τ → RJ σ)
    (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ),
  m149 (τ := τ) (σ := σ) (α := α) (ρ := ρ) (β := β) checked round T x r =
    (checked T).bind (fun U => round U x r)
theorem p149 : P149 := by simp [P149, m149, m147]
abbrev P150 : Prop := ∀ (τ σ α ρ β : Type) (checked : τ → RJ σ)
    (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ),
  m150 (τ := τ) (σ := σ) (α := α) (ρ := ρ) (β := β) checked round T x r =
    (checked T).bind (fun U => round U x r)
theorem p150 : P150 := by simp [P150, m150, m147]
abbrev P151 : Prop := ∀ (τ σ α ρ β : Type) (checked : τ → RJ σ)
    (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ),
  m151 (τ := τ) (σ := σ) (α := α) (ρ := ρ) (β := β) checked round T x r =
    (checked T).bind (fun U => round U x r)
theorem p151 : P151 := by simp [P151, m151, m147]
abbrev P154 : Prop := ∀ (α : Type) (p : Int), m154 α p = none
theorem p154 : P154 := by simp [P154, m154]
abbrev P157 : Prop := ∀ _ : Unit, m157 = none
theorem p157 : P157 := by intro; rfl
abbrev P159 : Prop := ∀ b, m159 b = if b then none else some false
theorem p159 : P159 := by simp [P159, m159]
abbrev P160 : Prop := ∀ (α : Type) (x : α), m160 α x = none
theorem p160 : P160 := by simp [P160, m160]
abbrev P161 : Prop := ∀ (α : Type) (x : α), m161 α x = none
theorem p161 : P161 := by simp [P161, m161]
abbrev P162 : Prop := ∀ _ : Unit, m162 = none
theorem p162 : P162 := by intro; rfl
abbrev P164 : Prop := ∀ b, m164 b = if b then some true else none
theorem p164 : P164 := by simp [P164, m164]
abbrev P165 : Prop := ∀ (α : Type) (x : α), m165 α x = none
theorem p165 : P165 := by simp [P165, m165]
abbrev P166 : Prop := ∀ (α : Type) (x : α), m166 α x = none
theorem p166 : P166 := by simp [P166, m166]
abbrev P167 : Prop := ∀ _ : Unit, m167 = none
theorem p167 : P167 := by intro; rfl
abbrev P169 : Prop := ∀ b, m169 b = none
theorem p169 : P169 := by simp [P169, m169]
abbrev P170 : Prop := ∀ (α : Type) (x : α), m170 α x = none
theorem p170 : P170 := by simp [P170, m170]
abbrev P171 : Prop := ∀ (α : Type) (x : α), m171 α x = none
theorem p171 : P171 := by simp [P171, m171]
abbrev P173 : Prop := ∀ (α : Type) (x : α), m173 α x = none
theorem p173 : P173 := by simp [P173, m173]
abbrev P174 : Prop := ∀ (α : Type) (x : α), m174 α x = none
theorem p174 : P174 := by simp [P174, m174]

def FloatArrayExact : Prop :=
  ∀ T A, m176 T A = A.map fun x => match x with | .missing => .missing | value => value

theorem floatArrayExact_refuted : ¬ FloatArrayExact := by
  intro h
  have counterexample := h .abstractReal [.exactBig]
  simp [m176] at counterexample
abbrev P180 : Prop := ∀ A : List FloatValue, m180 A = A
theorem p180 : P180 := by simp [P180, m180]
abbrev P231 : Prop := ∀ (α : Type) (x : List (Option α)), m231 x = Skip.mk x
theorem p231 : P231 := by simp [P231, m231]
abbrev P236 : Prop := ∀ _ : Unit, m236 = .sizeUnknown
theorem p236 : P236 := by intro; rfl
abbrev P237 : Prop := ∀ (α β : Type) (parentStyle : α → β) (T : α),
  m237 parentStyle T = parentStyle T
theorem p237 : P237 := by simp [P237, m237]
abbrev P238 : Prop := ∀ (α β γ : Type) (eltype : α → β) (nonmissing : β → γ) (T : α),
  m238 eltype nonmissing T = nonmissing (eltype T)
theorem p238 : P238 := by simp [P238, m238]
abbrev P252 : Prop := ∀ (α β : Type) (indexStyle : α → β) (T : α),
  m252 indexStyle T = indexStyle T
theorem p252 : P252 := by simp [P252, m252]
abbrev P263 : Prop := ∀ (α : Type) (showParent : List (Option α) → String) (s : Skip α),
  m263 showParent s = "skipmissing(" ++ showParent s.x ++ ")"
theorem p263 : P263 := by simp [P263, m263]
abbrev P275 : Prop := ∀ (α β : Type) (f : α → β) (op : β → β → β)
    (empty : Jl β) (blk : Nat) (s : Skip α),
  m275 f op empty blk s = mrSkip f op empty blk s.x
theorem p275 : P275 := by simp [P275, m275]
abbrev P299 : Prop := ∀ (α β γ : Type)
    (mapfoldl : (α → β) → (β → β → β) → Skip α → γ)
    (f : α → β) (op : β → β → β) (s : Skip α),
  m299 mapfoldl f op s = mapfoldl f op s
theorem p299 : P299 := by simp [P299, m299]
abbrev P303 : Prop := ∀ (α β : Type) (pairwise : (α → β) → (β → β → β) → Nat)
    (f : α → β) (op : β → β → β) (s : Skip α) (first last : Nat),
  m303 pairwise f op s first last = mrImpl f op s.x (pairwise f op) first last
theorem p303 : P303 := by simp [P303, m303]
abbrev P306 : Prop := ∀ (α β : Type) (f : α → β) (op : β → β → β)
    (s : Skip α) (first last blk : Nat),
  m306 f op s first last blk = mrImpl f op s.x blk first last
theorem p306 : P306 := by simp [P306, m306]
abbrev P420 : Prop := ∀ α : Type, m420 α = .missing
theorem p420 : P420 := by simp [P420, m420]
abbrev P421 : Prop := ∀ (α : Type) (ys : List (JV α)), m421 ys = coalesce ys
theorem p421 : P421 := by simp [P421, m421]
abbrev P422 : Prop := ∀ (α : Type) (x : JV α) (ys : List (JV α)), m422 x ys = x
theorem p422 : P422 := by simp [P422, m422]
abbrev P451 : Prop := ∀ (α : Type) (args : List (JV α)),
  m451 (α := α) args = args.reverse.foldl (fun expr value => .branch value expr) .missing
theorem p451 : P451 := by simp [P451, m451]

private def mk (line : Nat) (name : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"reducecov-missing-l{line}", juliaFile := "base/missing.jl", juliaFns := [name]
    statement := s!"The method at base/missing.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/missing.jl:{line}", status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.ReduceCov.MissingCov
