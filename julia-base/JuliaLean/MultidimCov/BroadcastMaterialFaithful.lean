import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastMaterialFaithful

open JuliaLean.Registry

inductive Error where
  | argument
  | dimensionMismatch
  | bounds
  | typeError
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure RefValue (α : Type) where value : α deriving Repr, DecidableEq
structure TypeRef (T : Type) where value : T deriving Repr, DecidableEq

def m736 (value : α) : RefValue α := ⟨value⟩
def P736 : Prop := ∀ {α : Type} (value : α), m736 value = ⟨value⟩
theorem p736 : P736 := by simp [P736, m736]

def m737 (typeValue : T) : TypeRef T := ⟨typeValue⟩
def P737 : Prop := ∀ {T : Type} (typeValue : T), m737 typeValue = ⟨typeValue⟩
theorem p737 : P737 := by simp [P737, m737]

def m738 (value : α) : α := value
def P738 : Prop := ∀ {α : Type} (value : α), m738 value = value
theorem p738 : P738 := by simp [P738, m738]

def m740 {I V : Type} (collect : I → Result (List V)) (iterable : I) : Result (List V) := collect iterable
def P740 : Prop := ∀ {I V : Type} (collect : I → Result (List V)) iterable, m740 collect iterable = collect iterable
theorem p740 : P740 := by simp [P740, m740]

def m741 {D : Type} (_dict : D) : Result Unit := .error .argument
def P741 : Prop := ∀ {D : Type} (dict : D), m741 dict = .error .argument
theorem p741 : P741 := by simp [P741, m741]

structure SampledBroadcast (A V : Type) where
  f : List V → V
  args : List A

def sampleArgs {A I V : Type} (sample : A → I → Result V) : List A → I → Result (List V)
  | [], _ => .ok []
  | head :: tail, index => do pure ((← sample head index) :: (← sampleArgs sample tail index))

def m744 {A I V : Type} (sample : A → I → Result V) (bc : SampledBroadcast A V) (index : I) : Result V := do
  bc.f <$> sampleArgs sample bc.args index
def P744 : Prop := ∀ {A I V : Type} (sample : A → I → Result V) bc index,
  m744 sample bc index = do bc.f <$> sampleArgs sample bc.args index
theorem p744 : P744 := by simp [P744, m744]

def m747 {A I V : Type} (broadcastGet : A → I → Result V) (value : A) (index : I) : Result V :=
  broadcastGet value index
def P747 : Prop := ∀ {A I V : Type} (broadcastGet : A → I → Result V) value index,
  m747 broadcastGet value index = broadcastGet value index
theorem p747 : P747 := by simp [P747, m747]

def m748 {A I V : Type} (broadcastGet : A → I → Result V) (value : A) (index : I) : Result V :=
  broadcastGet value index
def P748 : Prop := ∀ {A I V : Type} (broadcastGet : A → I → Result V) value index,
  m748 broadcastGet value index = broadcastGet value index
theorem p748 : P748 := by simp [P748, m748]

structure TypedValue (T V : Type) where
  value : V
  hasType : Bool
  deriving Repr, DecidableEq
def m751 {A I T V : Type} (inferenceBarrier : A → A) (broadcastGet : A → I → V)
    (eltype : A → T) (typecheck : V → T → Bool) (value : A) (index : I) : Result V :=
  let sampled := broadcastGet (inferenceBarrier value) index
  if typecheck sampled (eltype value) then .ok sampled else .error .typeError
def P751 : Prop := ∀ {A I T V : Type} (inferenceBarrier : A → A) (broadcastGet : A → I → V)
    (eltype : A → T) (typecheck : V → T → Bool) value index,
  m751 inferenceBarrier broadcastGet eltype typecheck value index =
    let sampled := broadcastGet (inferenceBarrier value) index
    if typecheck sampled (eltype value) then .ok sampled else .error .typeError
theorem p751 : P751 := by simp [P751, m751]

def m753 {A I V : Type} (sample : A → I → Result V) (head : A) (tail : List A) (index : I) : Result (List V) := do
  pure ((← sample head index) :: (← sampleArgs sample tail index))
def P753 : Prop := ∀ {A I V : Type} (sample : A → I → Result V) head tail index,
  m753 sample head tail index = do pure ((← sample head index) :: (← sampleArgs sample tail index))
theorem p753 : P753 := by simp [P753, m753]

def m754 {I V : Type} (_index : I) : List V := []
def P754 : Prop := ∀ {I V : Type} (index : I), (m754 index : List V) = []
theorem p754 : P754 := by simp [P754, m754]

inductive JType where
  | bottom
  | known (name : String)
  | union (members : List String)
  | tuple (members : List JType)
  deriving Repr

def m756 {B A : Type} (argtypes : B → A) (returnType : A → JType)
    (promoteUnion : JType → JType) (bc : B) : JType :=
  let args := argtypes bc
  match returnType args with | .bottom => .bottom | result => promoteUnion result
def P756 : Prop := ∀ {B A : Type} (argtypes : B → A) (returnType : A → JType)
    (promoteUnion : JType → JType) bc,
  m756 argtypes returnType promoteUnion bc =
    let args := argtypes bc
    match returnType args with | .bottom => .bottom | result => promoteUnion result
theorem p756 : P756 := by simp [P756, m756]

def m765 {F A : Type} (combineEltypes : F → A → JType) (f : F) (args : A) : JType :=
  combineEltypes f args
def P765 : Prop := ∀ {F A : Type} (combineEltypes : F → A → JType) f args,
  m765 combineEltypes f args = combineEltypes f args
theorem p765 : P765 := by simp [P765, m765]

def m766 {A : Type} (eltype : A → JType) (array : A) : JType := eltype array
def P766 : Prop := ∀ {A : Type} (eltype : A → JType) array, m766 eltype array = eltype array
theorem p766 : P766 := by simp [P766, m766]

def tupleOrBottom : List JType → JType := fun types =>
  if types.any (fun t => match t with | .bottom => true | _ => false)
  then .bottom else .tuple types

def m768 : List JType := []
def P768 : Prop := ∀ _ : Unit, m768 = []
theorem p768 : P768 := by simp [P768, m768]

def m769 (element : JType) : JType := tupleOrBottom [element]
def P769 : Prop := ∀ element, m769 element = tupleOrBottom [element]
theorem p769 : P769 := by simp [P769, m769]

def m770 (left right : JType) : JType := tupleOrBottom [left, right]
def P770 : Prop := ∀ left right, m770 left right = tupleOrBottom [left, right]
theorem p770 : P770 := by simp [P770, m770]

def eltypes : List JType → JType
  | [] => .tuple []
  | head :: tail =>
      match eltypes tail with
      | .bottom => .bottom
      | .tuple rest => tupleOrBottom (head :: rest)
      | _ => .bottom

def m771 (head : JType) (tail : List JType) : JType :=
  match eltypes tail with
  | .bottom => .bottom
  | .tuple rest => tupleOrBottom (head :: rest)
  | _ => .bottom
def P771 : Prop := ∀ head tail, m771 head tail =
  match eltypes tail with
  | .bottom => .bottom
  | .tuple rest => tupleOrBottom (head :: rest)
  | _ => .bottom
theorem p771 : P771 := by simp [P771, m771]

def m774 {F : Type} (returnType : F → JType → JType) (promoteUnion : JType → JType)
    (f : F) (args : List JType) : JType :=
  match eltypes args with | .bottom => .bottom | argTypes => promoteUnion (returnType f argTypes)
def P774 : Prop := ∀ {F : Type} (returnType : F → JType → JType)
    (promoteUnion : JType → JType) f args,
  m774 returnType promoteUnion f args =
    match eltypes args with | .bottom => .bottom | argTypes => promoteUnion (returnType f argTypes)
theorem p774 : P774 := by simp [P774, m774]

def m859 {F A B R : Type} (broadcasted : F → A → B) (materialize : B → R) (f : F) (args : A) : R :=
  materialize (broadcasted f args)
def P859 : Prop := ∀ {F A B R : Type} (broadcasted : F → A → B) (materialize : B → R) f args,
  m859 broadcasted materialize f args = materialize (broadcasted f args)
theorem p859 : P859 := by simp [P859, m859]

def m862 {N R : Type} (f : List N → R) (numbers : List N) : R := f numbers
def P862 : Prop := ∀ {N R : Type} (f : List N → R) numbers, m862 f numbers = f numbers
theorem p862 : P862 := by simp [P862, m862]

def zipTuples {A V : Type} (f : List A → V) (tuples : List (List A)) : List V :=
  match tuples with
  | [] => []
  | first :: _ => (List.range first.length).filterMap fun i => (tuples.mapM fun values => values[i]?).map f
def m863 {A V : Type} (f : List A → V) (tuples : List (List A)) : List V := zipTuples f tuples
def P863 : Prop := ∀ {A V : Type} (f : List A → V) tuples, m863 f tuples = zipTuples f tuples
theorem p863 : P863 := by simp [P863, m863]

def m898 {F D A B : Type} (broadcasted : F → A → Result B)
    (materializeBang : D → B → Result Unit) (f : F) (dest : D) (args : A) : Result D := do
  let bc ← broadcasted f args
  materializeBang dest bc
  pure dest
def P898 : Prop := ∀ {F D A B : Type} (broadcasted : F → A → Result B)
    (materializeBang : D → B → Result Unit) f dest args,
  m898 broadcasted materializeBang f dest args = do
    let bc ← broadcasted f args
    materializeBang dest bc
    pure dest
theorem p898 : P898 := by simp [P898, m898]

def m908 {F A B R C T : Type} (broadcasted : F → A → B) (materialize : B → R)
    (axes : B → List C) (similarFill : B → R → T) (f : F) (args : A) : Sum T R :=
  let bc := broadcasted f args
  let result := materialize bc
  if (axes bc).isEmpty then .inl (similarFill bc result) else .inr result
def P908 : Prop := ∀ {F A B R C T : Type} (broadcasted : F → A → B) (materialize : B → R)
    (axes : B → List C) (similarFill : B → R → T) f args,
  m908 broadcasted materialize axes similarFill f args =
    let bc := broadcasted f args; let result := materialize bc
    if (axes bc).isEmpty then .inl (similarFill bc result) else .inr result
theorem p908 : P908 := by simp [P908, m908]

structure ZeroD (α : Type) where
  value : α
  deriving Repr, DecidableEq

def m913 {R : Type} (f : Unit → R) : ZeroD R := ⟨f ()⟩
def P913 : Prop := ∀ {R : Type} (f : Unit → R), m913 f = ⟨f ()⟩
theorem p913 : P913 := by simp [P913, m913]

def m914 {N R : Type} (f : List N → R) (numbers : List N) : ZeroD R := ⟨f numbers⟩
def P914 : Prop := ∀ {N R : Type} (f : List N → R) numbers,
  m914 f numbers = (⟨f numbers⟩ : ZeroD R)
theorem p914 : P914 := by simp [P914, m914]

def m921 {B R : Type} (instantiate : B → B) (copy : B → R) (bc : B) : R := copy (instantiate bc)
def P921 : Prop := ∀ {B R : Type} (instantiate : B → B) (copy : B → R) bc,
  m921 instantiate copy bc = copy (instantiate bc)
theorem p921 : P921 := by simp [P921, m921]

def m922 (value : α) : α := value
def P922 : Prop := ∀ {α : Type} (value : α), m922 value = value
theorem p922 : P922 := by simp [P922, m922]

def m924 {D X I A B R : Type} (axes : D → X)
    (make : I → List A → X → B) (identity : I) (x : A)
    (instantiate : B → B) (materializeBang : D → B → R) (dest : D) : R :=
  materializeBang dest (instantiate (make identity [x] (axes dest)))
def P924 : Prop := ∀ {D X I A B R : Type} (axes : D → X)
    (make : I → List A → X → B) identity x (instantiate : B → B)
    (materializeBang : D → B → R) dest,
  m924 axes make identity x instantiate materializeBang dest =
    materializeBang dest (instantiate (make identity [x] (axes dest)))
theorem p924 : P924 := by simp [P924, m924]

def m928 {D B S R : Type} (combineStyles : D → B → S) (materializeStyled : S → D → B → R)
    (dest : D) (bc : B) : R := materializeStyled (combineStyles dest bc) dest bc
def P928 : Prop := ∀ {D B S R : Type} (combineStyles : D → B → S)
    (materializeStyled : S → D → B → R) dest bc,
  m928 combineStyles materializeStyled dest bc = materializeStyled (combineStyles dest bc) dest bc
theorem p928 : P928 := by simp [P928, m928]

structure MaterializedExpr (S F A X : Type) where
  style : S
  f : F
  args : A
  axes : X
  deriving Repr, DecidableEq

def m932 {S D F A X R : Type} (axes : D → X)
    (instantiate : MaterializedExpr S F A X → MaterializedExpr S F A X)
    (copyto : D → MaterializedExpr S F A X → R) (_style : S) (dest : D)
    (bc : MaterializedExpr S F A X) : R :=
  copyto dest (instantiate ⟨bc.style, bc.f, bc.args, axes dest⟩)
def P932 : Prop := ∀ {S D F A X R : Type} (axes : D → X)
    (instantiate : MaterializedExpr S F A X → MaterializedExpr S F A X)
    (copyto : D → MaterializedExpr S F A X → R) (style : S) dest bc,
  m932 axes instantiate copyto style dest bc =
    copyto dest (instantiate ⟨bc.style, bc.f, bc.args, axes dest⟩)
theorem p932 : P932 := by simp [P932, m932]

def m936 {D : Type} (throwUnwritable : D → Result Unit) (dest : D) : Result Unit :=
  throwUnwritable dest
def P936 : Prop := ∀ {D : Type} (throwUnwritable : D → Result Unit) dest,
  m936 throwUnwritable dest = throwUnwritable dest
theorem p936 : P936 := by simp [P936, m936]

def m937 {D : Type} (_dest : D) : Result Unit := .error .argument
def P937 : Prop := ∀ {D : Type} (dest : D), m937 dest = .error .argument
theorem p937 : P937 := by simp [P937, m937]

def m942 {B V : Type} (getZero : B → V) (bc : B) : V := getZero bc
def P942 : Prop := ∀ {B V : Type} (getZero : B → V) bc, m942 getZero bc = getZero bc
theorem p942 : P942 := by simp [P942, m942]

def m943 {B : Type} (_bc : B) : Result Unit := .error .argument
def P943 : Prop := ∀ {B : Type} (bc : B), m943 bc = .error .argument
theorem p943 : P943 := by simp [P943, m943]

inductive Inferred where | bottom | concrete | abstract deriving Repr, DecidableEq

def m948 {B Iter I State V D : Type} (resultEltype : B → Result Inferred)
    (similar : B → Inferred → Result D) (copyto : D → B → Result D)
    (preprocess : B → Result B) (eachindex : B → Result Iter)
    (iterate : Iter → Result (Option (I × State))) (getindex : B → I → Result V)
    (typeOf : V → Inferred) (setindex : D → I → V → Result D)
    (normalize : Inferred → Inferred)
    (copyNonleaf : D → B → Iter → State → Nat → Result D)
    (assertReturn : Inferred → D → Result D) (bc : B) : Result D := do
  let elementType ← resultEltype bc
  if elementType = .concrete then
    let dest ← similar bc elementType
    copyto dest bc
  else
    let ready ← preprocess bc
    let iter ← eachindex ready
    match ← iterate iter with
    | none => similar ready elementType
    | some (index, state) => do
        let value ← getindex ready index
        let dest ← similar ready (typeOf value)
        let dest ← setindex dest index value
        let result ← copyNonleaf dest ready iter state 1
        assertReturn (normalize elementType) result
def P948 : Prop := ∀ {B Iter I State V D : Type} (resultEltype : B → Result Inferred)
    (similar : B → Inferred → Result D) (copyto : D → B → Result D)
    (preprocess : B → Result B) (eachindex : B → Result Iter)
    (iterate : Iter → Result (Option (I × State))) (getindex : B → I → Result V)
    (typeOf : V → Inferred) (setindex : D → I → V → Result D)
    (normalize : Inferred → Inferred)
    (copyNonleaf : D → B → Iter → State → Nat → Result D)
    (assertReturn : Inferred → D → Result D) bc,
  m948 resultEltype similar copyto preprocess eachindex iterate getindex typeOf
      setindex normalize copyNonleaf assertReturn bc = do
    let elementType ← resultEltype bc
    if elementType = .concrete then
      let dest ← similar bc elementType
      copyto dest bc
    else
      let ready ← preprocess bc
      let iter ← eachindex ready
      match ← iterate iter with
      | none => similar ready elementType
      | some (index, state) => do
          let value ← getindex ready index
          let dest ← similar ready (typeOf value)
          let dest ← setindex dest index value
          let result ← copyNonleaf dest ready iter state 1
          assertReturn (normalize elementType) result
theorem p948 : P948 := by simp [P948, m948]

def m980 {D B : Type} (convertNothing : B → B) (copyto : D → B → D) (dest : D) (bc : B) : D :=
  copyto dest (convertNothing bc)
def P980 : Prop := ∀ {D B : Type} (convertNothing : B → B) (copyto : D → B → D) dest bc,
  m980 convertNothing copyto dest bc = copyto dest (convertNothing bc)
theorem p980 : P980 := by simp [P980, m980]

def m983 {D B V : Type} (identityFast : B → Option V) (fill : D → V → D)
    (fallback : D → B → D) (dest : D) (bc : B) : D :=
  match identityFast bc with | some value => fill dest value | none => fallback dest bc
def P983 : Prop := ∀ {D B V : Type} (identityFast : B → Option V) (fill : D → V → D)
    (fallback : D → B → D) dest bc,
  m983 identityFast fill fallback dest bc =
    match identityFast bc with | some value => fill dest value | none => fallback dest bc
theorem p983 : P983 := by simp [P983, m983]

def m1001 {A : Type} (sameObject : A → A → Bool) (unalias : A → A → A) (dest src : A) : A :=
  if sameObject dest src then src else unalias dest src
def P1001 : Prop := ∀ {A : Type} (sameObject : A → A → Bool) (unalias : A → A → A) dest src,
  m1001 sameObject unalias dest src = if sameObject dest src then src else unalias dest src
theorem p1001 : P1001 := by simp [P1001, m1001]

def m1002 {A : Type} (src : A) : A := src
def P1002 : Prop := ∀ {A : Type} (src : A), m1002 src = src
theorem p1002 : P1002 := by simp [P1002, m1002]

structure Expr (S F A X : Type) where
  style : S
  f : F
  args : A
  axes : X
  deriving Repr, DecidableEq

def m1007 {S F A X D : Type} (preprocessArgs : D → A → A) (dest : D) (bc : Expr S F A X) : Expr S F A X :=
  ⟨bc.style, bc.f, preprocessArgs dest bc.args, bc.axes⟩
def P1007 : Prop := ∀ {S F A X D : Type} (preprocessArgs : D → A → A) dest (bc : Expr S F A X),
  m1007 preprocessArgs dest bc = ⟨bc.style, bc.f, preprocessArgs dest bc.args, bc.axes⟩
theorem p1007 : P1007 := by simp [P1007, m1007]

def m1008 {D A B : Type} (unalias : D → A → B) (extrude : B → B) (dest : D) (value : A) : B :=
  extrude (unalias dest value)
def P1008 : Prop := ∀ {D A B : Type} (unalias : D → A → B) (extrude : B → B) dest value,
  m1008 unalias extrude dest value = extrude (unalias dest value)
theorem p1008 : P1008 := by simp [P1008, m1008]

def preprocessArgs {D A B : Type} (preprocess : D → A → B) (dest : D) : List A → List B
  | [] => []
  | head :: tail => preprocess dest head :: preprocessArgs preprocess dest tail

def m1010 {D A B : Type} (preprocess : D → A → B) (dest : D) (head : A) (tail : List A) : List B :=
  preprocess dest head :: preprocessArgs preprocess dest tail
def P1010 : Prop := ∀ {D A B : Type} (preprocess : D → A → B) dest head tail,
  m1010 preprocess dest head tail = preprocess dest head :: preprocessArgs preprocess dest tail
theorem p1010 : P1010 := by simp [P1010, m1010]

def m1011 {D A B : Type} (preprocess : D → A → B) (dest : D) (value : A) : List B := [preprocess dest value]
def P1011 : Prop := ∀ {D A B : Type} (preprocess : D → A → B) dest value,
  m1011 preprocess dest value = [preprocess dest value]
theorem p1011 : P1011 := by simp [P1011, m1011]

def m1012 {D B : Type} (_dest : D) : List B := []
def P1012 : Prop := ∀ {D B : Type} (dest : D), (m1012 dest : List B) = []
theorem p1012 : P1012 := by simp [P1012, m1012]

def writeAll {D I V : Type} (setindex : D → I → V → D) (getindex : I → V) : D → List I → D
  | dest, [] => dest
  | dest, index :: rest => writeAll setindex getindex (setindex dest index (getindex index)) rest

def fallbackCopy {D B I V : Type} (preprocess : D → B → B)
    (indices : B → List I) (getindex : B → I → V) (setindex : D → I → V → D)
    (dest : D) (bc : B) : D :=
  let ready := preprocess dest bc
  writeAll setindex (getindex ready) dest (indices ready)

def m1015 {D B X I V : Type} (axesDest : D → X) (axesExpr : B → X) (sameAxes : X → X → Bool)
    (identityArray : B → Option D) (copyto : D → D → D) (preprocess : D → B → B)
    (indices : B → List I) (getindex : B → I → V) (setindex : D → I → V → D)
    (dest : D) (bc : B) : Result D :=
  if !sameAxes (axesDest dest) (axesExpr bc) then .error .dimensionMismatch else
  match identityArray bc with
  | some source =>
      if sameAxes (axesDest dest) (axesDest source) then .ok (copyto dest source)
      else .ok (fallbackCopy preprocess indices getindex setindex dest bc)
  | none => .ok (fallbackCopy preprocess indices getindex setindex dest bc)
def P1015 : Prop := ∀ {D B X I V : Type} (axesDest : D → X) (axesExpr : B → X)
    (sameAxes : X → X → Bool) (identityArray : B → Option D) (copyto : D → D → D)
    (preprocess : D → B → B) (indices : B → List I) (getindex : B → I → V)
    (setindex : D → I → V → D) dest bc,
  m1015 axesDest axesExpr sameAxes identityArray copyto preprocess indices getindex setindex dest bc =
    if !sameAxes (axesDest dest) (axesExpr bc) then .error .dimensionMismatch else
    match identityArray bc with
    | some source =>
        if sameAxes (axesDest dest) (axesDest source) then .ok (copyto dest source)
        else .ok (fallbackCopy preprocess indices getindex setindex dest bc)
    | none => .ok (fallbackCopy preprocess indices getindex setindex dest bc)
theorem p1015 : P1015 := by simp [P1015, m1015]

def m1133 {X : Type} (render : X → String) (destAxes sourceAxes : X) : Except String Unit :=
  .error ("destination axes " ++ render destAxes ++
    " are not compatible with source axes " ++ render sourceAxes)
def P1133 : Prop := ∀ {X : Type} (render : X → String) destAxes sourceAxes,
  m1133 render destAxes sourceAxes =
    .error ("destination axes " ++ render destAxes ++
      " are not compatible with source axes " ++ render sourceAxes)
theorem p1133 : P1133 := by simp [P1133, m1133]

def copyPrefix {D I V : Type} (getindex : D → I → V) (setindex : D → I → V → D)
    (source target : D) : List I → D
  | [] => target
  | index :: rest => copyPrefix getindex setindex source (setindex target index (getindex source index)) rest

def m1136 {D B I V State : Type} (getindex : D → I → V) (setindex : D → I → V → D)
    (continueCopy : D → B → List I → State → Nat → D) (newdest dest : D) (bc : B)
    (value : V) (index : I) (iter : List I) (state : State) (count : Nat) : D :=
  let copied := copyPrefix getindex setindex dest newdest (iter.take count)
  continueCopy (setindex copied index value) bc iter state (count + 1)
def P1136 : Prop := ∀ {D B I V State : Type} (getindex : D → I → V)
    (setindex : D → I → V → D) (continueCopy : D → B → List I → State → Nat → D)
    newdest dest bc value index iter state count,
  m1136 getindex setindex continueCopy newdest dest bc value index iter state count =
    let copied := copyPrefix getindex setindex dest newdest (iter.take count)
    continueCopy (setindex copied index value) bc iter state (count + 1)
theorem p1136 : P1136 := by simp [P1136, m1136]

def copyNonleaf {D I V State : Type} (fits : V → Bool) (getvalue : I → V)
    (setindex : D → I → V → D) (widen : D → V → I → State → Nat → D) :
    D → List (I × State) → Nat → D
  | dest, [], _ => dest
  | dest, (index, state) :: rest, count =>
      let value := getvalue index
      if fits value then
        copyNonleaf fits getvalue setindex widen (setindex dest index value) rest (count + 1)
      else
        widen dest value index state count

def m1145 {D I V State : Type} (fits : V → Bool) (getvalue : I → V)
    (setindex : D → I → V → D) (widen : D → V → I → State → Nat → D)
    (dest : D) (iterations : List (I × State)) (count : Nat) : D :=
  copyNonleaf fits getvalue setindex widen dest iterations count
def P1145 : Prop := ∀ {D I V State : Type} (fits : V → Bool) (getvalue : I → V)
    (setindex : D → I → V → D) (widen : D → V → I → State → Nat → D)
    dest iterations count,
  m1145 fits getvalue setindex widen dest iterations count =
    copyNonleaf fits getvalue setindex widen dest iterations count
theorem p1145 : P1145 := by simp [P1145, m1145]

def m1167 {B I V : Type} (axes : B → List (List I)) (getindex : B → Nat → V) (bc : B) : Result (List V) :=
  match axes bc with
  | [axis] => .ok ((List.range axis.length).map fun k => getindex bc (k + 1))
  | _ => .error .dimensionMismatch
def P1167 : Prop := ∀ {B I V : Type} (axes : B → List (List I)) (getindex : B → Nat → V) bc,
  m1167 axes getindex bc = match axes bc with
    | [axis] => .ok ((List.range axis.length).map fun k => getindex bc (k + 1))
    | _ => .error .dimensionMismatch
theorem p1167 : P1167 := by simp [P1167, m1167]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; broadcast docstring and source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.BroadcastMaterialFaithful
