import JuliaLean.Core
import JuliaLean.MultidimCov.BroadcastStyleFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastLazyFaithful

open JuliaLean
open JuliaLean.Registry
open BroadcastStyleFaithful

inductive Error where
  | tupleNotCallable
  | typeError
  | argumentError
  | boundsError
  | dimensionMismatch
  deriving Repr, DecidableEq

structure Broadcasted (S F A X : Type) where
  style : S
  f : F
  args : A
  axes : X
  deriving Repr, DecidableEq

inductive Candidate (S : Type) where
  | style (value : S)
  | wrongType
  deriving Repr, DecidableEq

def requireStyle : Candidate S → Except Error S
  | .style style => .ok style
  | .wrongType => .error .typeError

def m175 {α β : Type} (_tupleFunction : α) (_args : β) : Except Error Unit :=
  .error .tupleNotCallable
def P175 : Prop := ∀ {α β : Type} (f : α) (args : β),
  m175 f args = .error .tupleNotCallable
theorem p175 : P175 := by simp [P175, m175]

def m176 (style : S) (f : F) (args : A) (axes : X) : Broadcasted S F A X :=
  ⟨style, f, args, axes⟩
def P176 : Prop := ∀ {S F A X : Type} (style : S) (f : F) (args : A) (axes : X),
  m176 style f args axes = (⟨style, f, args, axes⟩ : Broadcasted S F A X)
theorem p176 : P176 := by simp [P176, m176]

def m181 {F A X : Type} (combineStyles : A → Candidate Style) (f : F) (args : A) (axes : X) :
    Except Error (Broadcasted Style F A X) :=
  match combineStyles args with
  | .style style => .ok ⟨style, f, args, axes⟩
  | .wrongType => .error .typeError

def P181 : Prop := ∀ {F A X : Type} (combineStyles : A → Candidate Style)
    (f : F) (args : A) (axes : X),
  m181 combineStyles f args axes =
    match combineStyles args with
    | .style style => .ok ⟨style, f, args, axes⟩
    | .wrongType => .error .typeError
theorem p181 : P181 := by
  intro F A X combineStyles f args axes
  cases h : combineStyles args <;> simp [m181, h]

def m185 {F A X : Type} (constructStyle : Candidate Style) (f : F) (args : A) (axes : X) :
    Except Error (Broadcasted Style F A X) := do
  let style ← requireStyle constructStyle
  .ok ⟨style, f, args, axes⟩
def P185 : Prop := ∀ {F A X : Type} (constructStyle : Candidate Style)
    (f : F) (args : A) (axes : X),
  m185 constructStyle f args axes =
    match constructStyle with
    | .style style => .ok ⟨style, f, args, axes⟩
    | .wrongType => .error .typeError
theorem p185 : P185 := by
  intro F A X constructStyle f args axes
  cases constructStyle <;> rfl

def m189 {S F A X : Type} (constructStyle : Candidate S)
    (function : Candidate F) (arguments : Candidate A) (axisValue : Candidate X) :
    Except Error (Broadcasted S F A X) := do
  let style ← requireStyle constructStyle
  let f ← requireStyle function
  let args ← requireStyle arguments
  let axes ← requireStyle axisValue
  .ok ⟨style, f, args, axes⟩
def P189 : Prop := ∀ {S F A X : Type} (constructStyle : Candidate S)
    (function : Candidate F) (arguments : Candidate A) (axisValue : Candidate X),
  m189 constructStyle function arguments axisValue = do
    let style ← requireStyle constructStyle
    let f ← requireStyle function
    let args ← requireStyle arguments
    let axes ← requireStyle axisValue
    .ok ⟨style, f, args, axes⟩
theorem p189 : P189 := by unfold P189; intros; rfl

def m196 {A B R : Type} (broadcasted : (Bool → Bool → Bool) → A → B → R)
    (a : A) (b : B) : R := broadcasted (fun x y => x && y) a b
def P196 : Prop := ∀ {A B R : Type}
    (broadcasted : (Bool → Bool → Bool) → A → B → R) a b,
  m196 broadcasted a b = broadcasted (fun x y => x && y) a b
theorem p196 : P196 := by simp [P196, m196]

structure FlatBoolBroadcasted (A : Type) where
  f : List Bool → Bool
  args : A

def m199 {A B R : Type} (flatten : B → FlatBoolBroadcasted A)
    (broadcasted : (Bool → List Bool → Bool) → B → A → R) (a : B) (bc : B) : R :=
  let bcf := flatten bc
  broadcasted (fun first rest => first && bcf.f rest) a bcf.args
def P199 : Prop := ∀ {A B R : Type} (flatten : B → FlatBoolBroadcasted A)
    (broadcasted : (Bool → List Bool → Bool) → B → A → R) a bc,
  m199 flatten broadcasted a bc =
    let bcf := flatten bc
    broadcasted (fun first rest => first && bcf.f rest) a bcf.args
theorem p199 : P199 := by simp [P199, m199]

def m207 {A B R : Type} (broadcasted : (Bool → Bool → Bool) → A → B → R)
    (a : A) (b : B) : R := broadcasted (fun x y => x || y) a b
def P207 : Prop := ∀ {A B R : Type}
    (broadcasted : (Bool → Bool → Bool) → A → B → R) a b,
  m207 broadcasted a b = broadcasted (fun x y => x || y) a b
theorem p207 : P207 := by simp [P207, m207]

def m208 {A B R : Type} (flatten : B → FlatBoolBroadcasted A)
    (broadcasted : (Bool → List Bool → Bool) → B → A → R) (a : B) (bc : B) : R :=
  let bcf := flatten bc
  broadcasted (fun first rest => first || bcf.f rest) a bcf.args
def P208 : Prop := ∀ {A B R : Type} (flatten : B → FlatBoolBroadcasted A)
    (broadcasted : (Bool → List Bool → Bool) → B → A → R) a bc,
  m208 flatten broadcasted a bc =
    let bcf := flatten bc
    broadcasted (fun first rest => first || bcf.f rest) a bcf.args
theorem p208 : P208 := by simp [P208, m208]

def m215 (constructStyle : Unit → S2) (bc : Broadcasted S1 F A X) :
    Broadcasted S2 F A X :=
  ⟨constructStyle (), bc.f, bc.args, bc.axes⟩
def P215 : Prop := ∀ {S1 S2 F A X : Type} (constructStyle : Unit → S2)
    (bc : Broadcasted S1 F A X),
  m215 constructStyle bc = ⟨constructStyle (), bc.f, bc.args, bc.axes⟩
theorem p215 : P215 := by unfold P215; intros; rfl

def m218 (printHead : O → Except Error O)
    (printStyle : O → StyleParam → Except Error O)
    (printBody : O → F → A → Except Error O) (styleType : Unit → StyleParam)
    (isTupleAxes : X → Bool) (io : O) (bc : Broadcasted S F A X) :
    Except Error (O × Unit) := do
  let io ← printHead io
  let io ← if isTupleAxes bc.axes then printStyle io (styleType ()) else .ok io
  let io ← printBody io bc.f bc.args
  .ok (io, ())
def P218 : Prop := ∀ {O StyleParam S F A X : Type}
    (printHead : O → Except Error O)
    (printStyle : O → StyleParam → Except Error O)
    (printBody : O → F → A → Except Error O) (styleType : Unit → StyleParam)
    (isTupleAxes : X → Bool) (io : O) (bc : Broadcasted S F A X),
  m218 printHead printStyle printBody styleType isTupleAxes io bc = do
    let io ← printHead io
    let io ← if isTupleAxes bc.axes then printStyle io (styleType ()) else .ok io
    let io ← printBody io bc.f bc.args
    .ok (io, ())
theorem p218 : P218 := by unfold P218; intros; rfl

def m229 {S F A X T R : Type} (axes : Broadcasted S F A X → R)
    (similar : Broadcasted S F A X → T → R → R) (bc : Broadcasted S F A X) (Tval : T) : R :=
  similar bc Tval (axes bc)
def P229 : Prop := ∀ {S F A X T R : Type} (axes : Broadcasted S F A X → R)
    (similar : Broadcasted S F A X → T → R → R) bc Tval,
  m229 axes similar bc Tval = similar bc Tval (axes bc)
theorem p229 : P229 := by simp [P229, m229]

def m230 {T D R : Type} (similarArray : T → Nat → List D → R) (elementType : T) (dims : List D) : R :=
  similarArray elementType dims.length dims
def P230 : Prop := ∀ {T D R : Type} (similarArray : T → Nat → List D → R) elementType dims,
  m230 similarArray elementType dims = similarArray elementType dims.length dims
theorem p230 : P230 := by simp [P230, m230]

def m232 {D R : Type} (similarBitArray : List D → R) (dims : List D) : R := similarBitArray dims
def P232 : Prop := ∀ {D R : Type} (similarBitArray : List D → R) dims,
  m232 similarBitArray dims = similarBitArray dims
theorem p232 : P232 := by simp [P232, m232]

def m235 {T D R : Type} (similarArray : T → Nat → List D → R) (elementType : T) (dims : List D) : R :=
  similarArray elementType dims.length dims
def P235 : Prop := ∀ {T D R : Type} (similarArray : T → Nat → List D → R) elementType dims,
  m235 similarArray elementType dims = similarArray elementType dims.length dims
theorem p235 : P235 := by simp [P235, m235]

def m237 {D R : Type} (similarBitArray : List D → R) (dims : List D) : R := similarBitArray dims
def P237 : Prop := ∀ {D R : Type} (similarBitArray : List D → R) dims,
  m237 similarBitArray dims = similarBitArray dims
theorem p237 : P237 := by simp [P237, m237]

def m240 {S F A Axis : Type} (combineAxes : A → List Axis)
    (bc : Broadcasted S F A (Option (List Axis))) : List Axis :=
  match bc.axes with | some axes => axes | none => combineAxes bc.args
def P240 : Prop := ∀ {S F A Axis : Type} (combineAxes : A → List Axis)
    (bc : Broadcasted S F A (Option (List Axis))),
  m240 combineAxes bc = match bc.axes with | some axes => axes | none => combineAxes bc.args
theorem p240 : P240 := by simp [P240, m240]

def m241 {Axis : Type} (axes : List Axis) : List Axis := axes
def P241 : Prop := ∀ {Axis : Type} (axes : List Axis), m241 axes = axes
theorem p241 : P241 := by simp [P241, m241]

def m242 {A Axis : Type} (combineAxes : A → List Axis) (args : A) : List Axis := combineAxes args
def P242 : Prop := ∀ {A Axis : Type} (combineAxes : A → List Axis) args,
  m242 combineAxes args = combineAxes args
theorem p242 : P242 := by simp [P242, m242]

def m243 {A : Type} (_args : A) : List Unit := []
def P243 : Prop := ∀ {A : Type} (args : A), m243 args = []
theorem p243 : P243 := by simp [P243, m243]

def m245 (axes : B → Except Error (List Axis))
    (getindex : List Axis → Int → Except Error Axis) (oneToOne : Axis)
    (bc : B) (rank d : Int) : Except Error Axis :=
  if d ≤ rank then do getindex (← axes bc) d else .ok oneToOne
def P245 : Prop := ∀ {B Axis : Type}
    (axes : B → Except Error (List Axis))
    (getindex : List Axis → Int → Except Error Axis) (oneToOne : Axis)
    (bc : B) rank d,
  m245 axes getindex oneToOne bc rank d =
    if d ≤ rank then do getindex (← axes bc) d else .ok oneToOne
theorem p245 : P245 := by unfold P245; intros; rfl

def m248 {S : Type} (constructStyle : Unit → S) : S := constructStyle ()
def P248 : Prop := ∀ {S : Type} (constructStyle : Unit → S),
  m248 constructStyle = constructStyle ()
theorem p248 : P248 := by unfold P248; intros; rfl

def m249 (_style : AssignedStyle) : Except Error Style := .error .argumentError
def P249 : Prop := ∀ style, m249 style = .error .argumentError
theorem p249 : P249 := by simp [P249, m249]

structure BroadcastedType (ArgsType : Type) where
  argsType : ArgsType
  axesRank : Option Nat
  styleRank : Rank

def m252 (bcType : BroadcastedType A) : A := bcType.argsType
def P252 : Prop := ∀ {A : Type} (bcType : BroadcastedType A), m252 bcType = bcType.argsType
theorem p252 : P252 := by simp [P252, m252]

def m253 {S F A X : Type} (typeof : Broadcasted S F A X → BroadcastedType A)
    (bc : Broadcasted S F A X) : A := m252 (typeof bc)
def P253 : Prop := ∀ {S F A X : Type} (typeof : Broadcasted S F A X → BroadcastedType A) bc,
  m253 typeof bc = (typeof bc).argsType
theorem p253 : P253 := by simp [P253, m253, m252]

inductive IndexStyle where | linear | cartesian deriving Repr, DecidableEq
inductive IndexSet (Axis : Type) where
  | cartesian (axes : List Axis)
  | linear (axes : List Axis)
  | sole (axis : Axis)
  deriving Repr, DecidableEq

def m255 {B I : Type} (indexStyle : B → IndexStyle) (eachindex : IndexStyle → B → I) (bc : B) : I :=
  eachindex (indexStyle bc) bc
def P255 : Prop := ∀ {B I : Type} (indexStyle : B → IndexStyle)
    (eachindex : IndexStyle → B → I) bc,
  m255 indexStyle eachindex bc = eachindex (indexStyle bc) bc
theorem p255 : P255 := by simp [P255, m255]

def m256 {B Axis I : Type} (axes : B → List Axis)
    (route : IndexStyle → List Axis → I) (style : IndexStyle) (bc : B) : I :=
  route style (axes bc)
def P256 : Prop := ∀ {B Axis I : Type} (axes : B → List Axis)
    (route : IndexStyle → List Axis → I) style bc,
  m256 axes route style bc = route style (axes bc)
theorem p256 : P256 := by simp [P256, m256]

def m257 {Axis : Type} (axes : List Axis) : IndexSet Axis := .cartesian axes
def P257 : Prop := ∀ {Axis : Type} (axes : List Axis), m257 axes = .cartesian axes
theorem p257 : P257 := by simp [P257, m257]

def m258 (linearIndices : T → Except Error L)
    (eachindex : IndexStyle → L → Except Error I) (style : IndexStyle) (axes : T) :
    Except Error I := do
  eachindex style (← linearIndices axes)
def P258 : Prop := ∀ {T L I : Type} (linearIndices : T → Except Error L)
    (eachindex : IndexStyle → L → Except Error I) style (axes : T),
  m258 linearIndices eachindex style axes = do eachindex style (← linearIndices axes)
theorem p258 : P258 := by unfold P258; intros; rfl

def m259 {Axis : Type} (axis : Axis) : Axis := axis
def P259 : Prop := ∀ {Axis : Type} (axis : Axis), m259 axis = axis
theorem p259 : P259 := by simp [P259, m259]

def m261 {B T : Type} (typeof : B → T) (indexStyle : T → IndexStyle) (bc : B) : IndexStyle :=
  indexStyle (typeof bc)
def P261 : Prop := ∀ {B T : Type} (typeof : B → T) (indexStyle : T → IndexStyle) bc,
  m261 typeof indexStyle bc = indexStyle (typeof bc)
theorem p261 : P261 := by simp [P261, m261]

def m262 : IndexStyle := .linear
def P262 : Prop := ∀ _ : Unit, m262 = .linear
theorem p262 : P262 := by simp [P262, m262]

def m263 : IndexStyle := .cartesian
def P263 : Prop := ∀ _ : Unit, m263 = .cartesian
theorem p263 : P263 := by simp [P263, m263]

def m265 {Axis : Type} (axes : List Axis) : IndexSet Axis := .linear axes
def P265 : Prop := ∀ {Axis : Type} (axes : List Axis), m265 axes = .linear axes
theorem p265 : P265 := by simp [P265, m265]

def m267 {B T : Type} (typeof : B → T) (ndims : T → Nat) (bc : B) : Nat := ndims (typeof bc)
def P267 : Prop := ∀ {B T : Type} (typeof : B → T) (ndims : T → Nat) bc,
  m267 typeof ndims bc = ndims (typeof bc)
theorem p267 : P267 := by simp [P267, m267]

def m268 (rank : Nat) : Nat := rank
def P268 : Prop := ∀ rank, m268 rank = rank
theorem p268 : P268 := by simp [P268, m268]

inductive ArgRank where | tuple | other (rank : Nat) deriving Repr, DecidableEq
def argRank : ArgRank → Nat | .tuple => 1 | .other rank => rank
def maxNdim : List ArgRank → Nat
  | [] => 0
  | head :: tail => max (argRank head) (maxNdim tail)

def m269 (argtype : BC → Except Error A) (maxndims : A → Except Error Nat)
    (bcType : BC) : Except Error Nat := do
  maxndims (← argtype bcType)
def P269 : Prop := ∀ {BC A : Type} (argtype : BC → Except Error A)
    (maxndims : A → Except Error Nat) (bcType : BC),
  m269 argtype maxndims bcType = do maxndims (← argtype bcType)
theorem p269 : P269 := by unfold P269; intros; rfl

def m270 (styleRank : Rank) (args : List ArgRank) : Nat :=
  match styleRank with | .fixed n => n | .any => maxNdim args
def P270 : Prop := ∀ styleRank args,
  m270 styleRank args = match styleRank with | .fixed n => n | .any => maxNdim args
theorem p270 : P270 := by intro styleRank args; cases styleRank <;> rfl

def m273 : Nat := 0
def P273 : Prop := ∀ _ : Unit, m273 = 0
theorem p273 : P273 := by simp [P273, m273]

def m274 (head : ArgRank) : Nat := argRank head
def P274 : Prop := ∀ head, m274 head = argRank head
theorem p274 : P274 := by simp [P274, m274]

def m275 (head : ArgRank) (tail : List ArgRank) : Nat := max (argRank head) (maxNdim tail)
def P275 : Prop := ∀ head tail, m275 head tail = max (argRank head) (maxNdim tail)
theorem p275 : P275 := by simp [P275, m275]

abbrev I64 := JInt .i64
def axisLength {Axis : Type} (length : Axis → I64) (axes : List Axis) : List I64 := axes.map length
def m281 {Axis : Type} (length : Axis → I64) (axes : List Axis) : List I64 := axisLength length axes
def P281 : Prop := ∀ {Axis : Type} (length : Axis → I64) axes,
  m281 length axes = axes.map length
theorem p281 : P281 := by simp [P281, m281, axisLength]

def productI64 : List I64 → I64
  | [] => JInt.lit .i64 1
  | x :: xs => x * productI64 xs
def m282 (size : List I64) : I64 := productI64 size
def P282 : Prop := ∀ size, m282 size = productI64 size
theorem p282 : P282 := by simp [P282, m282]

def m288 {I V : Type} (iterate : List I → Nat → Option (I × Nat))
    (getindex : I → V) (iter : List I) (state : Nat) : Option (V × (List I × Nat)) :=
  match iterate iter state with
  | none => none
  | some (index, nextState) => some (getindex index, (iter, nextState))

def m284 {I V : Type} (eachindex : List I)
    (iterate : List I → Nat → Option (I × Nat)) (getindex : I → V) :
    Option (V × (List I × Nat)) := m288 iterate getindex eachindex 0

def P284 : Prop := ∀ {I V : Type} (iter : List I)
    (iterate : List I → Nat → Option (I × Nat)) (getindex : I → V),
  m284 iter iterate getindex = m288 iterate getindex iter 0
theorem p284 : P284 := by simp [P284, m284]

def P288 : Prop := ∀ {I V : Type} (iterate : List I → Nat → Option (I × Nat))
    (getindex : I → V) iter state,
  m288 iterate getindex iter state =
    match iterate iter state with
    | none => none
    | some (index, nextState) => some (getindex index, (iter, nextState))
theorem p288 : P288 := by
  intro I V iterate getindex iter state
  simp [m288]

def m295 (ndims : T → Except Error Nat) (hasShape : Nat → R) (broadcastedType : T) :
    Except Error R := do
  .ok (hasShape (← ndims broadcastedType))
def P295 : Prop := ∀ {T R : Type} (ndims : T → Except Error Nat)
    (hasShape : Nat → R) (broadcastedType : T),
  m295 ndims hasShape broadcastedType = do .ok (hasShape (← ndims broadcastedType))
theorem p295 : P295 := by unfold P295; intros; rfl

inductive IteratorEltype where | unknown deriving Repr, DecidableEq

def m296 : IteratorEltype := .unknown
def P296 : Prop := ∀ _ : Unit, m296 = .unknown
theorem p296 : P296 := by simp [P296, m296]

def m299 {T : Type} (x : T) : T := x
def P299 : Prop := ∀ {T : Type} (x : T), m299 x = x
theorem p299 : P299 := by simp [P299, m299]

def m310 {S F A Axis : Type} (combineAxes : A → Except Error (List Axis))
    (checkAxes : List Axis → A → Except Error Unit)
    (bc : Broadcasted S F A (Option (List Axis))) : Except Error (Broadcasted S F A (Option (List Axis))) := do
  let axes ← match bc.axes with
    | none => combineAxes bc.args
    | some axes => do checkAxes axes bc.args; pure axes
  pure ⟨bc.style, bc.f, bc.args, some axes⟩

def P310 : Prop := ∀ {S F A Axis : Type} (combineAxes : A → Except Error (List Axis))
    (checkAxes : List Axis → A → Except Error Unit)
    (bc : Broadcasted S F A (Option (List Axis))),
  m310 combineAxes checkAxes bc = do
    let axes ← match bc.axes with
      | none => combineAxes bc.args
      | some axes => do checkAxes axes bc.args; pure axes
    pure ⟨bc.style, bc.f, bc.args, some axes⟩
theorem p310 : P310 := by simp [P310, m310]

def m319 {B : Type} (bc : B) : B := bc
def P319 : Prop := ∀ {B : Type} (bc : B), m319 bc = bc
theorem p319 : P319 := by simp [P319, m319]

def m321 {B : Type} (bc : B) : B := bc
def P321 : Prop := ∀ {B : Type} (bc : B), m321 bc = bc
theorem p321 : P321 := by simp [P321, m321]

def m322 {S F A Axis : Type} (checkAxes : List Axis → A → Except Error Unit)
    (bc : Broadcasted S F A (List Axis)) : Except Error (Broadcasted S F A (List Axis)) := do
  checkAxes bc.axes bc.args
  pure bc
def P322 : Prop := ∀ {S F A Axis : Type} (checkAxes : List Axis → A → Except Error Unit)
    (bc : Broadcasted S F A (List Axis)),
  m322 checkAxes bc = do checkAxes bc.axes bc.args; pure bc
theorem p322 : P322 := by simp [P322, m322]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; source equation and lazy-broadcast invariant"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.BroadcastLazyFaithful
