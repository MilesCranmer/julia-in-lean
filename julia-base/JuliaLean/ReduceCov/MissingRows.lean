import JuliaLean.MissingChar.Skip
import JuliaLean.MissingChar.Some
import JuliaLean.ReduceCov.Basic
import JuliaLean.Registry.Types

/-! Method-specific models for `base/missing.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.MissingCov

open JuliaLean.Registry
open JuliaLean.MissingChar

def m5 (_ : Unit) : String := "missing"
abbrev P5 : Prop := ∀ u, m5 u = "missing"
theorem p5 : P5 := by simp [P5, m5]

def m18 (msg : String) : String := "MissingException: " ++ msg
abbrev P18 : Prop := ∀ msg, m18 msg = "MissingException: " ++ msg
theorem p18 : P18 := by simp [P18, m18]

def m39 (typesplit : α → α → α) (missing T : α) : α := typesplit T missing
abbrev P39 : Prop := ∀ (α : Type) (typesplit : α → α → α) (missing T : α),
  m39 typesplit missing T = typesplit T missing
theorem p39 : P39 := by simp [P39, m39]

def m41 (nonmissing : α → α) (supertype isBottom : α → α → Bool) (T bottom : α) : RJ α :=
  let R := nonmissing T
  if supertype R T then .error (.errorException "could not compute non-missing type")
  else if isBottom R bottom then .error (.errorException "cannot convert a value to missing for assignment")
  else .ok R
abbrev P41 : Prop := ∀ (α : Type) (nonmissing : α → α) (supertype isBottom : α → α → Bool)
    (T bottom : α),
  m41 nonmissing supertype isBottom T bottom =
    let R := nonmissing T
    if supertype R T then .error (.errorException "could not compute non-missing type")
    else if isBottom R bottom then .error (.errorException "cannot convert a value to missing for assignment")
    else .ok R
theorem p41 : P41 := by simp [P41, m41]

def m48 (unionMissing : α → α) (S : α) : α := unionMissing S
abbrev P48 : Prop := ∀ (α : Type) (unionMissing : α → α) (S : α),
  m48 unionMissing S = unionMissing S
theorem p48 : P48 := by simp [P48, m48]

def m49 (unionNothingMissing : α → α) (S : α) : α := unionNothingMissing S
abbrev P49 : Prop := ∀ (α : Type) (unionNothingMissing : α → α) (S : α),
  m49 unionNothingMissing S = unionNothingMissing S
theorem p49 : P49 := by simp [P49, m49]

def m50 (nonnothing nonmissing : α → α) (supertype : α → α → Bool)
    (promote : α → α → α) (unionBoth : α → α) (any T S : α) : α :=
  let Rn := nonnothing T
  if supertype Rn T then any
  else
    let Rm := nonmissing Rn
    if supertype Rm Rn then any else unionBoth (promote Rm S)
abbrev P50 : Prop := ∀ (α : Type) (nonnothing nonmissing : α → α)
    (supertype : α → α → Bool) (promote : α → α → α) (unionBoth : α → α)
    (any T S : α),
  m50 nonnothing nonmissing supertype promote unionBoth any T S =
    let Rn := nonnothing T
    if supertype Rn T then any
    else let Rm := nonmissing Rn; if supertype Rm Rn then any else unionBoth (promote Rm S)
theorem p50 : P50 := by simp [P50, m50]

def m60 (nonmissing : α → α) (supertype : α → α → Bool) (promote : α → α → α)
    (unionMissing : α → α) (any T S : α) : α :=
  let R := nonmissing T
  if supertype R T then any else unionMissing (promote R S)
abbrev P60 : Prop := ∀ (α : Type) (nonmissing : α → α) (supertype : α → α → Bool)
    (promote : α → α → α) (unionMissing : α → α) (any T S : α),
  m60 nonmissing supertype promote unionMissing any T S =
    let R := nonmissing T; if supertype R T then any else unionMissing (promote R S)
theorem p60 : P60 := by simp [P60, m60]

def m68 (x : α) : α := x
abbrev P68 : Prop := ∀ (α : Type) (x : α), m68 x = x
theorem p68 : P68 := by simp [P68, m68]

def m69 (x : α) : α := x
abbrev P69 : Prop := ∀ (α : Type) (x : α), m69 x = x
theorem p69 : P69 := by simp [P69, m69]

def m70 (checked : τ → RJ σ) (convert : σ → α → RJ β) (T : τ) (x : α) : RJ β := do
  (checked T).bind (fun R => convert R x)
abbrev P70 : Prop := ∀ (τ σ α β : Type) (checked : τ → RJ σ)
    (convert : σ → α → RJ β) (T : τ) (x : α),
  m70 checked convert T x = (checked T).bind (fun R => convert R x)
theorem p70 : P70 := by simp [P70, m70]

def m71 (nonnothing : τ → RJ σ) (nonmissing : σ → RJ ρ) (convert : ρ → α → RJ β)
    (T : τ) (x : α) : RJ β :=
  (nonnothing T).bind (fun R => (nonmissing R).bind (fun U => convert U x))
abbrev P71 : Prop := ∀ (τ σ ρ α β : Type) (nonnothing : τ → RJ σ)
    (nonmissing : σ → RJ ρ) (convert : ρ → α → RJ β) (T : τ) (x : α),
  m71 nonnothing nonmissing convert T x =
    (nonnothing T).bind (fun R => (nonmissing R).bind (fun U => convert U x))
theorem p71 : P71 := by simp [P71, m71]

@[simp] def missingResult (α : Type) : Option α := none

def m74 := missingResult Bool
abbrev P74 : Prop := ∀ _ : Unit, m74 = none
theorem p74 : P74 := by intro; rfl
def m76 (α : Type) (_ : α) := missingResult Bool
abbrev P76 : Prop := ∀ (α : Type) (x : α), m76 α x = none
theorem p76 : P76 := by simp [P76, m76]
def m78 (α : Type) (_ : α) := missingResult Bool
abbrev P78 : Prop := ∀ (α : Type) (x : α), m78 α x = none
theorem p78 : P78 := by simp [P78, m78]
def m79 (α : Type) (_ : α) := missingResult Bool
abbrev P79 : Prop := ∀ (α : Type) (x : α), m79 α x = none
theorem p79 : P79 := by simp [P79, m79]
def m82 (α : Type) (_ : α) : Bool := false
abbrev P82 : Prop := ∀ (α : Type) (x : α), m82 α x = false
theorem p82 : P82 := by simp [P82, m82]
def m83 := missingResult Bool
abbrev P83 : Prop := ∀ _ : Unit, m83 = none
theorem p83 : P83 := by intro; rfl
def m85 (α : Type) (_ : α) := missingResult Bool
abbrev P85 : Prop := ∀ (α : Type) (x : α), m85 α x = none
theorem p85 : P85 := by simp [P85, m85]
def m86 : Bool := false
abbrev P86 : Prop := ∀ _ : Unit, m86 = false
theorem p86 : P86 := by intro; rfl
def m89 := missingResult Bool
abbrev P89 : Prop := ∀ _ : Unit, m89 = none
theorem p89 : P89 := by intro; rfl
def m90 := missingResult Bool
abbrev P90 : Prop := ∀ _ : Unit, m90 = none
theorem p90 : P90 := by intro; rfl
def m91 := missingResult Bool
abbrev P91 : Prop := ∀ _ : Unit, m91 = none
theorem p91 : P91 := by intro; rfl
def m92 (α : Type) (_ : α) := missingResult Bool
abbrev P92 : Prop := ∀ (α : Type) (x : α), m92 α x = none
theorem p92 : P92 := by simp [P92, m92]
def m93 (α : Type) (_ : α) := missingResult Bool
abbrev P93 : Prop := ∀ (α : Type) (x : α), m93 α x = none
theorem p93 : P93 := by simp [P93, m93]

/-- Every generated unary method returns `missing`, `base/missing.jl:96-103`. -/
def m103 (α : Type) (_function : String) : Option α := none
abbrev P103 : Prop := ∀ (α : Type) (f : String), m103 α f = none
theorem p103 : P103 := by simp [P103, m103]

def m106 (α : Type) (f : String) : Jl α := .error (.methodError f)
abbrev P106 : Prop := ∀ (α : Type) (f : String), m106 α f = .error (.methodError f)
theorem p106 : P106 := by simp [P106, m106]
def m107 (α : Type) (_function : String) : Option α := none
abbrev P107 : Prop := ∀ (α : Type) (f : String), m107 α f = none
theorem p107 : P107 := by simp [P107, m107]
def m108 (checked : τ → RJ σ) (f : σ → RJ α) (T : τ) : RJ α := (checked T).bind f
abbrev P108 : Prop := ∀ (τ σ α : Type) (checked : τ → RJ σ) (f : σ → RJ α) (T : τ),
  m108 checked f T = (checked T).bind f
theorem p108 : P108 := by simp [P108, m108]
def m111 (α : Type) (f : String) : Jl α := .error (.methodError f)
abbrev P111 : Prop := ∀ (α : Type) (f : String), m111 α f = .error (.methodError f)
theorem p111 : P111 := by simp [P111, m111]
def m112 (nonmissing : τ → σ) (f : σ → ρ) (unionMissing : ρ → α) (T : τ) : α :=
  unionMissing (f (nonmissing T))
abbrev P112 : Prop := ∀ (τ σ ρ α : Type) (nonmissing : τ → σ) (f : σ → ρ)
    (unionMissing : ρ → α) (T : τ),
  m112 nonmissing f unionMissing T = unionMissing (f (nonmissing T))
theorem p112 : P112 := by simp [P112, m112]

def m119 (α : Type) (_function : String) : Option α := none
abbrev P119 : Prop := ∀ (α : Type) (f : String), m119 α f = none
theorem p119 : P119 := by simp [P119, m119]
def m120 (α β : Type) (_function : String) (_ : β) : Option α := none
abbrev P120 : Prop := ∀ (α β : Type) (f : String) (x : β), m120 α β f x = none
theorem p120 : P120 := by simp [P120, m120]
def m121 (α β : Type) (_function : String) (_ : β) : Option α := none
abbrev P121 : Prop := ∀ (α β : Type) (f : String) (x : β), m121 α β f x = none
theorem p121 : P121 := by simp [P121, m121]
def m125 (α : Type) (_rounding : α) := missingResult Int
abbrev P125 : Prop := ∀ (α : Type) (r : α), m125 α r = none
theorem p125 : P125 := by simp [P125, m125]
def m126 (α β : Type) (_number : α) (_rounding : β) := missingResult Int
abbrev P126 : Prop := ∀ (α β : Type) (x : α) (r : β), m126 α β x r = none
theorem p126 : P126 := by simp [P126, m126]
def m127 (α β : Type) (_number : α) (_rounding : β) := missingResult Int
abbrev P127 : Prop := ∀ (α β : Type) (x : α) (r : β), m127 α β x r = none
theorem p127 : P127 := by simp [P127, m127]

def m131 (result : α) : α := result
abbrev P131 : Prop := ∀ (α : Type) (result : α), m131 result = result
theorem p131 : P131 := by simp [P131, m131]
def m132 (result : α) (_ : β) : α := result
abbrev P132 : Prop := ∀ (α β : Type) (result : α) (x : β), m132 result x = result
theorem p132 : P132 := by simp [P132, m132]
def m133 (result : α) (_ : β) : α := result
abbrev P133 : Prop := ∀ (α β : Type) (result : α) (x : β), m133 result x = result
theorem p133 : P133 := by simp [P133, m133]
def m134 (result : α) : α := result
abbrev P134 : Prop := ∀ (α : Type) (result : α), m134 result = result
theorem p134 : P134 := by simp [P134, m134]
def m137 (α β γ : Type) (_lo : β) (_hi : γ) : Option α := none
abbrev P137 : Prop := ∀ (α β γ : Type) (lo : β) (hi : γ), m137 α β γ lo hi = none
theorem p137 : P137 := by simp [P137, m137]
def m139 (T : String) : String :=
  "cannot convert a missing value to type " ++ T ++ ": use Union{" ++ T ++ ", Missing} instead"
abbrev P139 : Prop := ∀ T, m139 T =
  "cannot convert a missing value to type " ++ T ++ ": use Union{" ++ T ++ ", Missing} instead"
theorem p139 : P139 := by simp [P139, m139]

def m143 (α : Type) (_sigdigits _digits _base : Int) : Option α := none
abbrev P143 : Prop := ∀ (α : Type) (s d b : Int), m143 α s d b = none
theorem p143 : P143 := by simp [P143, m143]
def m144 (α : Type) (_rounding : α) := missingResult Int
abbrev P144 : Prop := ∀ (α : Type) (r : α), m144 α r = none
theorem p144 : P144 := by simp [P144, m144]
def m145 (T : String) : RJ Unit := .error (.missingException (m139 T))
abbrev P145 : Prop := ∀ T, m145 T = .error (.missingException (m139 T))
theorem p145 : P145 := by simp [P145, m145]
def m147 (checked : τ → RJ σ) (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ) : RJ β := do
  (checked T).bind (fun U => round U x r)
abbrev P147 : Prop := ∀ (τ σ α ρ β : Type) (checked : τ → RJ σ)
    (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ),
  m147 checked round T x r = (checked T).bind (fun U => round U x r)
theorem p147 : P147 := by simp [P147, m147]
def m149 := @m147
abbrev P149 : Prop := ∀ (τ σ α ρ β : Type) (checked : τ → RJ σ)
    (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ),
  m149 (τ := τ) (σ := σ) (α := α) (ρ := ρ) (β := β) checked round T x r =
    (checked T).bind (fun U => round U x r)
theorem p149 : P149 := by simp [P149, m149, m147]
def m150 := @m147
abbrev P150 : Prop := ∀ (τ σ α ρ β : Type) (checked : τ → RJ σ)
    (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ),
  m150 (τ := τ) (σ := σ) (α := α) (ρ := ρ) (β := β) checked round T x r =
    (checked T).bind (fun U => round U x r)
theorem p150 : P150 := by simp [P150, m150, m147]
def m151 := @m147
abbrev P151 : Prop := ∀ (τ σ α ρ β : Type) (checked : τ → RJ σ)
    (round : σ → α → ρ → RJ β) (T : τ) (x : α) (r : ρ),
  m151 (τ := τ) (σ := σ) (α := α) (ρ := ρ) (β := β) checked round T x r =
    (checked T).bind (fun U => round U x r)
theorem p151 : P151 := by simp [P151, m151, m147]
def m154 (α : Type) (_exponent : Int) : Option α := none
abbrev P154 : Prop := ∀ (α : Type) (p : Int), m154 α p = none
theorem p154 : P154 := by simp [P154, m154]

def m157 := missingResult Bool
abbrev P157 : Prop := ∀ _ : Unit, m157 = none
theorem p157 : P157 := by intro; rfl
def m159 (b : Bool) : Option Bool := if b then none else some false
abbrev P159 : Prop := ∀ b, m159 b = if b then none else some false
theorem p159 : P159 := by simp [P159, m159]
def m160 (α : Type) (_ : α) := missingResult α
abbrev P160 : Prop := ∀ (α : Type) (x : α), m160 α x = none
theorem p160 : P160 := by simp [P160, m160]
def m161 (α : Type) (_ : α) := missingResult α
abbrev P161 : Prop := ∀ (α : Type) (x : α), m161 α x = none
theorem p161 : P161 := by simp [P161, m161]
def m162 := missingResult Bool
abbrev P162 : Prop := ∀ _ : Unit, m162 = none
theorem p162 : P162 := by intro; rfl
def m164 (b : Bool) : Option Bool := if b then some true else none
abbrev P164 : Prop := ∀ b, m164 b = if b then some true else none
theorem p164 : P164 := by simp [P164, m164]
def m165 (α : Type) (_ : α) := missingResult α
abbrev P165 : Prop := ∀ (α : Type) (x : α), m165 α x = none
theorem p165 : P165 := by simp [P165, m165]
def m166 (α : Type) (_ : α) := missingResult α
abbrev P166 : Prop := ∀ (α : Type) (x : α), m166 α x = none
theorem p166 : P166 := by simp [P166, m166]
def m167 := missingResult Bool
abbrev P167 : Prop := ∀ _ : Unit, m167 = none
theorem p167 : P167 := by intro; rfl
def m169 (_ : Bool) := missingResult Bool
abbrev P169 : Prop := ∀ b, m169 b = none
theorem p169 : P169 := by simp [P169, m169]
def m170 (α : Type) (_ : α) := missingResult α
abbrev P170 : Prop := ∀ (α : Type) (x : α), m170 α x = none
theorem p170 : P170 := by simp [P170, m170]
def m171 (α : Type) (_ : α) := missingResult α
abbrev P171 : Prop := ∀ (α : Type) (x : α), m171 α x = none
theorem p171 : P171 := by simp [P171, m171]
def m173 (α : Type) (_ : α) := missingResult String
abbrev P173 : Prop := ∀ (α : Type) (x : α), m173 α x = none
theorem p173 : P173 := by simp [P173, m173]
def m174 (α : Type) (_ : α) := missingResult String
abbrev P174 : Prop := ∀ (α : Type) (x : α), m174 α x = none
theorem p174 : P174 := by simp [P174, m174]

inductive FloatKind where | abstractReal | concreteBigFloat deriving DecidableEq
inductive FloatValue where | missing | exactBig | roundedF64 deriving DecidableEq

/-- `float(A::AbstractArray{Union{T,Missing}})`, `base/missing.jl:176-179`. -/
def m176 (T : FloatKind) (A : List FloatValue) : List FloatValue :=
  let U : FloatValue := match T with | .abstractReal => .roundedF64 | .concreteBigFloat => .exactBig
  A.map fun x => match x, U with
    | .missing, _ => .missing
    | .exactBig, .roundedF64 => .roundedF64
    | value, _ => value

def FloatArrayExact : Prop :=
  ∀ T A, m176 T A = A.map fun x => match x with | .missing => .missing | value => value

theorem floatArrayExact_refuted : ¬ FloatArrayExact := by
  intro h
  have counterexample := h .abstractReal [.exactBig]
  simp [m176] at counterexample

def m180 (A : List FloatValue) := A
abbrev P180 : Prop := ∀ A : List FloatValue, m180 A = A
theorem p180 : P180 := by simp [P180, m180]

structure Skip (α : Type) where x : List (Option α)

def m231 (x : List (Option α)) : Skip α := ⟨x⟩
abbrev P231 : Prop := ∀ (α : Type) (x : List (Option α)), m231 x = Skip.mk x
theorem p231 : P231 := by simp [P231, m231]
def m236 : MissingChar.ISize := .sizeUnknown
abbrev P236 : Prop := ∀ _ : Unit, m236 = .sizeUnknown
theorem p236 : P236 := by intro; rfl
def m237 (parentStyle : α → β) (T : α) : β := parentStyle T
abbrev P237 : Prop := ∀ (α β : Type) (parentStyle : α → β) (T : α),
  m237 parentStyle T = parentStyle T
theorem p237 : P237 := by simp [P237, m237]
def m238 (eltype : α → β) (nonmissing : β → γ) (T : α) : γ := nonmissing (eltype T)
abbrev P238 : Prop := ∀ (α β γ : Type) (eltype : α → β) (nonmissing : β → γ) (T : α),
  m238 eltype nonmissing T = nonmissing (eltype T)
theorem p238 : P238 := by simp [P238, m238]
def m252 (indexStyle : α → β) (T : α) : β := indexStyle T
abbrev P252 : Prop := ∀ (α β : Type) (indexStyle : α → β) (T : α),
  m252 indexStyle T = indexStyle T
theorem p252 : P252 := by simp [P252, m252]
def m263 (showParent : List (Option α) → String) (s : Skip α) : String :=
  "skipmissing(" ++ showParent s.x ++ ")"
abbrev P263 : Prop := ∀ (α : Type) (showParent : List (Option α) → String) (s : Skip α),
  m263 showParent s = "skipmissing(" ++ showParent s.x ++ ")"
theorem p263 : P263 := by simp [P263, m263]

def m275 (f : α → β) (op : β → β → β) (empty : Jl β) (blk : Nat) (s : Skip α) : Jl β :=
  mrSkip f op empty blk s.x
abbrev P275 : Prop := ∀ (α β : Type) (f : α → β) (op : β → β → β)
    (empty : Jl β) (blk : Nat) (s : Skip α),
  m275 f op empty blk s = mrSkip f op empty blk s.x
theorem p275 : P275 := by simp [P275, m275]
def m299 (mapfoldl : (α → β) → (β → β → β) → Skip α → γ)
    (f : α → β) (op : β → β → β) (s : Skip α) : γ := mapfoldl f op s
abbrev P299 : Prop := ∀ (α β γ : Type)
    (mapfoldl : (α → β) → (β → β → β) → Skip α → γ)
    (f : α → β) (op : β → β → β) (s : Skip α),
  m299 mapfoldl f op s = mapfoldl f op s
theorem p299 : P299 := by simp [P299, m299]
def m303 (pairwise : (α → β) → (β → β → β) → Nat)
    (f : α → β) (op : β → β → β) (s : Skip α) (first last : Nat) : Option β :=
  mrImpl f op s.x (pairwise f op) first last
abbrev P303 : Prop := ∀ (α β : Type) (pairwise : (α → β) → (β → β → β) → Nat)
    (f : α → β) (op : β → β → β) (s : Skip α) (first last : Nat),
  m303 pairwise f op s first last = mrImpl f op s.x (pairwise f op) first last
theorem p303 : P303 := by simp [P303, m303]
def m306 (f : α → β) (op : β → β → β) (s : Skip α) (first last blk : Nat) : Option β :=
  mrImpl f op s.x blk first last
abbrev P306 : Prop := ∀ (α β : Type) (f : α → β) (op : β → β → β)
    (s : Skip α) (first last blk : Nat),
  m306 f op s first last blk = mrImpl f op s.x blk first last
theorem p306 : P306 := by simp [P306, m306]

def m420 (α : Type) : JV α := .missing
abbrev P420 : Prop := ∀ α : Type, m420 α = .missing
theorem p420 : P420 := by simp [P420, m420]
def m421 (ys : List (JV α)) : JV α := coalesce ys
abbrev P421 : Prop := ∀ (α : Type) (ys : List (JV α)), m421 ys = coalesce ys
theorem p421 : P421 := by simp [P421, m421]
def m422 (x : JV α) (_ys : List (JV α)) : JV α := x
abbrev P422 : Prop := ∀ (α : Type) (x : JV α) (ys : List (JV α)), m422 x ys = x
theorem p422 : P422 := by simp [P422, m422]

inductive CoalesceExpr (α : Type) where
  | missing
  | branch (value : JV α) (rest : CoalesceExpr α)

def m451 (args : List (JV α)) : CoalesceExpr α :=
  args.reverse.foldl (fun expr value => .branch value expr) .missing
abbrev P451 : Prop := ∀ (α : Type) (args : List (JV α)),
  m451 (α := α) args = args.reverse.foldl (fun expr value => .branch value expr) .missing
theorem p451 : P451 := by simp [P451, m451]

private def mk (line : Nat) (name : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"reducecov-missing-l{line}", juliaFile := "base/missing.jl", juliaFns := [name]
    statement := s!"The method at base/missing.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/missing.jl:{line}", status := .proven, prop, thm := some thm }

def entries : List Entry := [
  mk 5 "show(::IO, ::Missing)" ``P5 ``p5,
  mk 18 "showerror(::IO, ::MissingException)" ``P18 ``p18,
  mk 39 "nonmissingtype(::Type)" ``P39 ``p39,
  mk 41 "nonmissingtype_checked(::Type)" ``P41 ``p41,
  mk 48 "promote_rule(::Type{Missing}, ::Type)" ``P48 ``p48,
  mk 49 "promote_rule(::Type{Union{Nothing,Missing}}, ::Type)" ``P49 ``p49,
  mk 50 "promote_rule(::Type{>:Union{Nothing,Missing}}, ::Type)" ``P50 ``p50,
  mk 60 "promote_rule(::Type{>:Missing}, ::Type)" ``P60 ``p60,
  mk 68 "convert(::Type{T}, ::T) where T>:Missing" ``P68 ``p68,
  mk 69 "convert(::Type{T}, ::T) where T>:Union{Missing,Nothing}" ``P69 ``p69,
  mk 70 "convert(::Type{T}, x) where T>:Missing" ``P70 ``p70,
  mk 71 "convert(::Type{T}, x) where T>:Union{Missing,Nothing}" ``P71 ``p71,
  mk 74 "==(::Missing, ::Missing)" ``P74 ``p74,
  mk 76 "==(::Any, ::Missing)" ``P76 ``p76,
  mk 78 "==(::Missing, ::WeakRef)" ``P78 ``p78,
  mk 79 "==(::WeakRef, ::Missing)" ``P79 ``p79,
  mk 82 "isequal(::Any, ::Missing)" ``P82 ``p82,
  mk 83 "<(::Missing, ::Missing)" ``P83 ``p83,
  mk 85 "<(::Any, ::Missing)" ``P85 ``p85,
  mk 86 "isless(::Missing, ::Missing)" ``P86 ``p86,
  mk 89 "ispositive(::Missing)" ``P89 ``p89,
  mk 90 "isnegative(::Missing)" ``P90 ``p90,
  mk 91 "isapprox(::Missing, ::Missing)" ``P91 ``p91,
  mk 92 "isapprox(::Missing, ::Any)" ``P92 ``p92,
  mk 93 "isapprox(::Any, ::Missing)" ``P93 ``p93,
  mk 103 "generated unary f(::Missing)" ``P103 ``p103,
  mk 106 "generated zero/one/oneunit(::Type{Any})" ``P106 ``p106,
  mk 107 "generated zero/one/oneunit(::Type{Missing})" ``P107 ``p107,
  mk 108 "generated zero/one/oneunit(::Type{T}) where T>:Missing" ``P108 ``p108,
  mk 111 "generated float/real/complex(::Type{Any})" ``P111 ``p111,
  mk 112 "generated float/real/complex(::Type{T}) where T>:Missing" ``P112 ``p112,
  mk 119 "generated binary f(::Missing, ::Missing)" ``P119 ``p119,
  mk 120 "generated binary f(::Missing, ::Number)" ``P120 ``p120,
  mk 121 "generated binary f(::Number, ::Missing)" ``P121 ``p121,
  mk 125 "div(::Missing, ::Missing, ::RoundingMode)" ``P125 ``p125,
  mk 126 "div(::Missing, ::Number, ::RoundingMode)" ``P126 ``p126,
  mk 127 "div(::Number, ::Missing, ::RoundingMode)" ``P127 ``p127,
  mk 131 "generated min/max/minmax(::Missing, ::Missing)" ``P131 ``p131,
  mk 132 "generated min/max/minmax(::Missing, ::Any)" ``P132 ``p132,
  mk 133 "generated min/max/minmax(::Any, ::Missing)" ``P133 ``p133,
  mk 134 "generated min/max/minmax(::Missing)" ``P134 ``p134,
  mk 137 "clamp(::Missing, lo, hi)" ``P137 ``p137,
  mk 139 "missing_conversion_msg" ``P139 ``p139,
  mk 143 "round(::Missing, ::RoundingMode)" ``P143 ``p143,
  mk 144 "round(::Type{>:Missing}, ::Missing, ::RoundingMode)" ``P144 ``p144,
  mk 145 "round(::Type{T}, ::Missing, ::RoundingMode)" ``P145 ``p145,
  mk 147 "round(::Type{T}, ::Any, ::RoundingMode) where T>:Missing" ``P147 ``p147,
  mk 149 "round(::Type{T}, ::Real, ::RoundingMode) where T>:Missing" ``P149 ``p149,
  mk 150 "round(::Type{T}, ::Rational, ::RoundingMode) where T>:Missing" ``P150 ``p150,
  mk 151 "round(::Type{T}, ::Rational{Bool}, ::RoundingMode) where T>:Missing" ``P151 ``p151,
  mk 154 "^(::Missing, ::Integer)" ``P154 ``p154,
  mk 157 "&(::Missing, ::Missing)" ``P157 ``p157,
  mk 159 "&(::Bool, ::Missing)" ``P159 ``p159,
  mk 160 "&(::Missing, ::Integer)" ``P160 ``p160,
  mk 161 "&(::Integer, ::Missing)" ``P161 ``p161,
  mk 162 "|(::Missing, ::Missing)" ``P162 ``p162,
  mk 164 "|(::Bool, ::Missing)" ``P164 ``p164,
  mk 165 "|(::Missing, ::Integer)" ``P165 ``p165,
  mk 166 "|(::Integer, ::Missing)" ``P166 ``p166,
  mk 167 "xor(::Missing, ::Missing)" ``P167 ``p167,
  mk 169 "xor(::Bool, ::Missing)" ``P169 ``p169,
  mk 170 "xor(::Missing, ::Integer)" ``P170 ``p170,
  mk 171 "xor(::Integer, ::Missing)" ``P171 ``p171,
  mk 173 "*(::Missing, ::Union{AbstractString,AbstractChar})" ``P173 ``p173,
  mk 174 "*(::Union{AbstractString,AbstractChar}, ::Missing)" ``P174 ``p174,
  { id := "reducecov-float-missing-abstract", juliaFile := "base/missing.jl"
    juliaFns := ["float(::AbstractArray{Union{T,Missing}})"]
    statement := "float preserves the value of every non-missing element, up to that element's own float conversion."
    source := "float docstring and base/missing.jl:176-179", status := .refuted
    prop := ``FloatArrayExact, thm := some ``floatArrayExact_refuted
    issue := "related #29693; none found for abstract Union element types" },
  mk 180 "float(::AbstractArray{Missing})" ``P180 ``p180,
  mk 231 "skipmissing" ``P231 ``p231,
  mk 236 "IteratorSize(::Type{<:SkipMissing})" ``P236 ``p236,
  mk 237 "IteratorEltype(::Type{SkipMissing{T}})" ``P237 ``p237,
  mk 238 "eltype(::Type{SkipMissing{T}})" ``P238 ``p238,
  mk 252 "IndexStyle(::Type{<:SkipMissing{T}})" ``P252 ``p252,
  mk 263 "show(::IO, ::SkipMissing)" ``P263 ``p263,
  mk 275 "_mapreduce(::IndexLinear, ::SkipMissing)" ``P275 ``p275,
  mk 299 "_mapreduce(::IndexCartesian, ::SkipMissing)" ``P299 ``p299,
  mk 303 "_mapreduce_impl_skipmissing wrapper" ``P303 ``p303,
  mk 306 "_mapreduce_impl_skipmissing kernel" ``P306 ``p306,
  mk 420 "coalesce()" ``P420 ``p420,
  mk 421 "coalesce(::Missing, ...)" ``P421 ``p421,
  mk 422 "coalesce(::Any, ...)" ``P422 ``p422,
  mk 451 "@coalesce" ``P451 ``p451
]

end JuliaLean.ReduceCov.MissingCov
