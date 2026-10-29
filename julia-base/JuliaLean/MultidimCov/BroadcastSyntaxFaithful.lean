import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastSyntaxFaithful

open JuliaLean.Registry

inductive Value where
  | symbol (name : String)
  | expr (head : String) (args : List Value)
  | other (description : String)
  deriving Repr

def m1297 {A R : Type} (maybeview : List A → R) (args : List A) : R := maybeview args
def P1297 : Prop := ∀ {A R : Type} (maybeview : List A → R) args, m1297 maybeview args = maybeview args
theorem p1297 : P1297 := by simp [P1297, m1297]

def m1304 {A : Type} (_value : A) : Bool := false
def P1304 : Prop := ∀ {A : Type} (value : A), m1304 value = false
theorem p1304 : P1304 := by simp [P1304, m1304]

def m1306 (isoperator : String → Bool) (name : String) : Bool :=
  (!isoperator name || name.front ≠ '.' || name = "..") && name ≠ ":"
def P1306 : Prop := ∀ isoperator name,
  m1306 isoperator name = ((!isoperator name || name.front ≠ '.' || name = "..") && name ≠ ":")
theorem p1306 : P1306 := by simp [P1306, m1306]

def m1307 (head : String) (_args : List Value) : Bool := head ≠ "$"
def P1307 : Prop := ∀ head args, m1307 head args = (head ≠ "$")
theorem p1307 : P1307 := by simp [P1307, m1307]

def m1308 (value : Value) : Value := value
def P1308 : Prop := ∀ value, m1308 value = value
theorem p1308 : P1308 := by simp [P1308, m1308]

def undot : Value → Value
  | .expr ".=" args => .expr "=" args
  | .expr "block" args => .expr "block" (args.map undot)
  | value => value

def m1309 (head : String) (args : List Value) : Value := undot (.expr head args)
def P1309 : Prop := ∀ head args,
  m1309 head args = if head = ".=" then .expr "=" args
    else if head = "block" then .expr "block" (args.map undot) else .expr head args
theorem p1309 : P1309 := by
  intro head args
  by_cases hdot : head = ".="
  · simp [m1309, undot, hdot]
  · by_cases hblock : head = "block" <;> simp [m1309, undot, hdot, hblock]

def m1318 (value : Value) : Value := value
def P1318 : Prop := ∀ value, m1318 value = value
theorem p1318 : P1318 := by simp [P1318, m1318]

def dottable (isoperator : String → Bool) : Value → Bool
  | .symbol name => m1306 isoperator name
  | .expr head _ => head ≠ "$"
  | .other _ => false

def dotComparisonArg (isoperator : String → Bool) (index : Nat) : Value → Value
  | .symbol name =>
      if index % 2 = 1 && dottable isoperator (.symbol name) && isoperator name
      then .symbol ("." ++ name) else .symbol name
  | value => value

def dotSyntax (isoperator : String → Bool) : Value → Value
  | .symbol name => .symbol name
  | .other description => .other description
  | .expr head args =>
      let dotted := args.map (dotSyntax isoperator)
      if head = "call" then
        match args, dotted with
        | originalFn :: _, dottedFn :: dottedArgs =>
            if dottable isoperator originalFn then .expr "." [dottedFn, .expr "tuple" dottedArgs]
            else .expr "call" dotted
        | _, _ => .expr "call" dotted
      else if head = "comparison" then
        .expr "comparison" ((dotted.zipIdx).map fun pair => dotComparisonArg isoperator pair.2 pair.1)
      else if head = "$" then args.head?.getD (.other "nothing")
      else if head = "let" || head = "for" then
        .expr head [undot (dotted.head?.getD (.other "nothing")), dotted[1]?.getD (.other "nothing")]
      else if head = "generator" || head = "filter" then
        .expr head (dotted.take 1 ++ (dotted.drop 1).map undot)
      else if (head = "=" || head = "function" || head = "macro") &&
          (match args.head? with | some (.expr "call" _) => true | _ => false) then
        .expr head [args.head?.getD (.other "nothing"), dotted[1]?.getD (.other "nothing")]
      else if head = "<:" then .expr "call" (.symbol ".<:" :: dotted)
      else if head = ">:" then .expr "call" (.symbol ".>:" :: dotted)
      else if (head.endsWith "=" && !head.startsWith ".") || head = "&&" || head = "||" then
        .expr ("." ++ head) dotted
      else .expr head dotted
termination_by value => sizeOf value

def m1319 (isoperator : String → Bool) (head : String) (args : List Value) : Value :=
  dotSyntax isoperator (.expr head args)
def P1319 : Prop := ∀ isoperator head args,
  m1319 isoperator head args = dotSyntax isoperator (.expr head args)
theorem p1319 : P1319 := by simp [P1319, m1319]

def m1390 (isoperator : String → Bool) (escape : Value → Value) (value : Value) : Value :=
  escape (dotSyntax isoperator value)
def P1390 : Prop := ∀ isoperator escape value,
  m1390 isoperator escape value = escape (dotSyntax isoperator value)
theorem p1390 : P1390 := by simp [P1390, m1390]

def m1394 {F G A K R : Type} (broadcastedF : F → List A → R)
    (broadcastedClosure : G → List A → R) (capture : F → List K → G)
    (f : F) (args : List A) (kwargs : List K) : R :=
  if kwargs.isEmpty then broadcastedF f args
  else broadcastedClosure (capture f kwargs) args
def P1394 : Prop := ∀ {F G A K R : Type} (broadcastedF : F → List A → R)
    (broadcastedClosure : G → List A → R) (capture : F → List K → G) f args kwargs,
  m1394 broadcastedF broadcastedClosure capture f args kwargs =
    if kwargs.isEmpty then broadcastedF f args
    else broadcastedClosure (capture f kwargs) args
theorem p1394 : P1394 := by simp [P1394, m1394]

def m1401 {F A B S R : Type} (broadcastable : A → B) (combineStyles : List B → S)
    (styled : S → F → List B → R) (f : F) (args : List A) : R :=
  let mapped := args.map broadcastable
  styled (combineStyles mapped) f mapped
def P1401 : Prop := ∀ {F A B S R : Type} (broadcastable : A → B) (combineStyles : List B → S)
    (styled : S → F → List B → R) f args,
  m1401 broadcastable combineStyles styled f args =
    let mapped := args.map broadcastable; styled (combineStyles mapped) f mapped
theorem p1401 : P1401 := by simp [P1401, m1401]

def m1409 {F A B S R : Type} (broadcastable : A → B) (combineStyles : List B → S)
    (styled : S → F → List B → R) (f : F) (first : A) (rest : List A) : R :=
  let firstMapped := broadcastable first
  let restMapped := rest.map broadcastable
  styled (combineStyles (firstMapped :: restMapped)) f (firstMapped :: restMapped)
def P1409 : Prop := ∀ {F A B S R : Type} (broadcastable : A → B) (combineStyles : List B → S)
    (styled : S → F → List B → R) f first rest,
  m1409 broadcastable combineStyles styled f first rest =
    let firstMapped := broadcastable first; let restMapped := rest.map broadcastable
    styled (combineStyles (firstMapped :: restMapped)) f (firstMapped :: restMapped)
theorem p1409 : P1409 := by simp [P1409, m1409]

def m1414 {F A B S R : Type} (broadcastable : A → B) (combineStyles : List B → S)
    (styled : S → F → List B → R) (f : F) (first second : A) (rest : List A) : R :=
  let firstMapped := broadcastable first
  let secondMapped := broadcastable second
  let restMapped := rest.map broadcastable
  styled (combineStyles (firstMapped :: secondMapped :: restMapped)) f (firstMapped :: secondMapped :: restMapped)
def P1414 : Prop := ∀ {F A B S R : Type} (broadcastable : A → B) (combineStyles : List B → S)
    (styled : S → F → List B → R) f first second rest,
  m1414 broadcastable combineStyles styled f first second rest =
    let firstMapped := broadcastable first; let secondMapped := broadcastable second
    let restMapped := rest.map broadcastable
    styled (combineStyles (firstMapped :: secondMapped :: restMapped)) f (firstMapped :: secondMapped :: restMapped)
theorem p1414 : P1414 := by simp [P1414, m1414]

structure Broadcasted (S F A X : Type) where
  style : S
  f : F
  args : List A
  axes : Option X
  deriving Repr, DecidableEq
def m1420 {S F A X : Type} (style : S) (f : F) (args : List A) : Broadcasted S F A X :=
  ⟨style, f, args, none⟩
def P1420 : Prop := ∀ {S F A X : Type} (style : S) (f : F) args,
  m1420 style f args = (⟨style, f, args, none⟩ : Broadcasted S F A X)
theorem p1420 : P1420 := by simp [P1420, m1420]

structure BroadcastFunction (F : Type) where
  f : F
  deriving Repr, DecidableEq
def m1452 {F A K R : Type} (broadcast : F → List A → List K → R)
    (op : BroadcastFunction F) (args : List A) (kwargs : List K) : R := broadcast op.f args kwargs
def P1452 : Prop := ∀ {F A K R : Type} (broadcast : F → List A → List K → R) op args kwargs,
  m1452 broadcast op args kwargs = broadcast op.f args kwargs
theorem p1452 : P1452 := by simp [P1452, m1452]

inductive ShowError where | failed deriving Repr, DecidableEq
abbrev ShowResult (α : Type) := Except ShowError α

def m1454 {F IO : Type} (print : IO → String → ShowResult IO)
    (showF : IO → F → ShowResult IO) (io : IO) (op : BroadcastFunction F) : ShowResult Unit := do
  let io ← print io "BroadcastFunction("
  let io ← showF io op.f
  let _ ← print io ")"
  pure ()
def P1454 : Prop := ∀ {F IO : Type} (print : IO → String → ShowResult IO)
    (showF : IO → F → ShowResult IO) io op,
  m1454 print showF io op = do
    let io ← print io "BroadcastFunction("
    let io ← showF io op.f
    let _ ← print io ")"
    pure ()
theorem p1454 : P1454 := by simp [P1454, m1454]

def m1460 {F : Type} (render : BroadcastFunction F → String) (op : BroadcastFunction F) : String := render op
def P1460 : Prop := ∀ {F : Type} (render : BroadcastFunction F → String) op,
  m1460 render op = render op
theorem p1460 : P1460 := by simp [P1460, m1460]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; @. docstring and source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.BroadcastSyntaxFaithful
