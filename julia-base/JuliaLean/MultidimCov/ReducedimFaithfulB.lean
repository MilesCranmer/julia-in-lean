import JuliaLean.MultidimCov.ReducedimFaithfulA
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimFaithfulB

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful
open ReducedimFaithfulA

/-- Generated `_fname(a, ::Colon; kw...)`, line 1000. -/
def m1000 (underlying : IdentityT → A → Colon → K → JResult R)
    (identity : IdentityT) (colon : Colon) (array : A) (keywords : K) : JResult R :=
  underlying identity array colon keywords
def P1000 : Prop := ∀ {IdentityT A Colon K R : Type} underlying identity colon array keywords,
  m1000 (IdentityT := IdentityT) (A := A) (Colon := Colon) (K := K) (R := R)
    underlying identity colon array keywords = underlying identity array colon keywords
theorem p1000 : P1000 := by unfold P1000 m1000; intros; rfl

/-- Generated ReshapedArray Colon fast path, line 1003. -/
def m1003 (parent : A → JResult P) (reduction : P → JResult R) (array : A) : JResult R := do
  let source ← parent array
  reduction source
def P1003 : Prop := ∀ {A P R : Type} parent reduction array,
  m1003 (A := A) (P := P) (R := R) parent reduction array = do
    let source ← parent array
    reduction source
theorem p1003 : P1003 := by unfold P1003; intros; rfl

/-- `any(a;kw...)`, line 1007. -/
def m1007 (anyFn : IdentityT → A → K → JResult R) (identity : IdentityT)
    (array : A) (keywords : K) : JResult R := anyFn identity array keywords
def P1007 : Prop := ∀ {IdentityT A K R : Type} anyFn identity array keywords,
  m1007 (IdentityT := IdentityT) (A := A) (K := K) (R := R) anyFn identity array keywords =
    anyFn identity array keywords
theorem p1007 : P1007 := by unfold P1007 m1007; intros; rfl

/-- `all(a;kw...)`, line 1009. -/
def m1009 (allFn : IdentityT → A → K → JResult R) (identity : IdentityT)
    (array : A) (keywords : K) : JResult R := allFn identity array keywords
def P1009 : Prop := ∀ {IdentityT A K R : Type} allFn identity array keywords,
  m1009 (IdentityT := IdentityT) (A := A) (K := K) (R := R) allFn identity array keywords =
    allFn identity array keywords
theorem p1009 : P1009 := by unfold P1009 m1009; intros; rfl

/-- Generated in-place reduction, lines 1020-1021. -/
def m1020 (mapFunction : F → JResult MF)
    (initarray : R → MF → Op → Bool → A → JResult R)
    (mapreducedim : MF → Op → R → A → JResult R)
    (operator : Op) (f : F) (result : R) (array : A) (init : Bool) : JResult R := do
  let mapped ← mapFunction f
  let initialized ← initarray result mapped operator init array
  mapreducedim mapped operator initialized array
def P1020 : Prop := ∀ {F MF R Op A : Type} mapFunction initarray mapreducedim operator f result array init,
  m1020 (F := F) (MF := MF) (R := R) (Op := Op) (A := A)
    mapFunction initarray mapreducedim operator f result array init = do
      let mapped ← mapFunction f
      let initialized ← initarray result mapped operator init array
      mapreducedim mapped operator initialized array
theorem p1020 : P1020 := by unfold P1020; intros; rfl

/-- Generated no-function in-place wrapper, line 1022. -/
def m1022 (reduction : IdentityT → R → A → Bool → JResult R)
    (identity : IdentityT) (result : R) (array : A) (init : Bool) : JResult R :=
  reduction identity result array init
def P1022 : Prop := ∀ {IdentityT R A : Type} reduction identity result array init,
  m1022 (IdentityT := IdentityT) (R := R) (A := A) reduction identity result array init =
    reduction identity result array init
theorem p1022 : P1022 := by unfold P1022 m1022; intros; rfl

/-- Generated `_fname(A,dims;kw...)`, line 1024. -/
def m1024 (underlying : IdentityT → A → D → K → JResult R)
    (identity : IdentityT) (array : A) (dims : D) (keywords : K) : JResult R :=
  underlying identity array dims keywords
def P1024 : Prop := ∀ {IdentityT A D K R : Type} underlying identity array dims keywords,
  m1024 (IdentityT := IdentityT) (A := A) (D := D) (K := K) (R := R)
    underlying identity array dims keywords = underlying identity array dims keywords
theorem p1024 : P1024 := by unfold P1024 m1024; intros; rfl

/-- Generated mapped `_fname`, line 1025. -/
def m1025 (mapFunction : F → JResult MF)
    (mapreduce : MF → Op → A → D → K → JResult R)
    (operator : Op) (f : F) (array : A) (dims : D) (keywords : K) : JResult R := do
  let mapped ← mapFunction f
  mapreduce mapped operator array dims keywords
def P1025 : Prop := ∀ {F MF Op A D K R : Type} mapFunction mapreduce operator f array dims keywords,
  m1025 (F := F) (MF := MF) (Op := Op) (A := A) (D := D) (K := K) (R := R)
    mapFunction mapreduce operator f array dims keywords = do
      let mapped ← mapFunction f
      mapreduce mapped operator array dims keywords
theorem p1025 : P1025 := by unfold P1025; intros; rfl

def checkOutputAxes (axesEqual : Rv → Ri → Nat → JResult Bool)
    (values : Rv) (indices : Ri) : Nat → Nat → JResult Unit
  | _, 0 => .ok ()
  | i, n + 1 => do
      let same ← axesEqual values indices i
      if ¬same then .error (.dimensionMismatch (.literal "Find-reduction: outputs must have the same indices"))
      else checkOutputAxes axesEqual values indices (i + 1) n

def tempInnerLoop (readA : A → Ix → JResult X) (map : F → X → JResult V)
    (compare : Op → V → V → JResult Bool) (isZeroKey : K → JResult Bool)
    (combine : Ix → Ix → JResult Ix) (f : F) (op : Op) (array : A) (outer : Ix) :
    V → K → List K → List Ix → JResult (V × K × List K)
  | value, index, keys, [] => .ok (value, index, keys)
  | value, index, [], _ :: _ => .error .typeError
  | value, index, key :: keys, i :: rest => do
      let ai ← combine i outer
      let source ← readA array ai
      let mapped ← map f source
      let unset ← isZeroKey index
      let better ← if unset then .ok true else compare op value mapped
      let next := if better then (mapped, key) else (value, index)
      tempInnerLoop readA map compare isZeroKey combine f op array outer next.1 next.2 keys rest

def directInnerLoop (readA : A → Ix → JResult X) (map : F → X → JResult V)
    (readValue : Rv → Ix → JResult V) (readIndex : Ri → Ix → JResult K)
    (writeValue : Rv → Ix → V → JResult Rv) (writeIndex : Ri → Ix → K → JResult Ri)
    (compare : Op → V → V → JResult Bool) (isZeroKey : K → JResult Bool)
    (combine : Ix → Ix → JResult Ix) (f : F) (op : Op) (array : A) (outer resultIndex : Ix) :
    Rv → Ri → List K → List Ix → JResult (Rv × Ri × List K)
  | values, indices, keys, [] => .ok (values, indices, keys)
  | values, indices, [], _ :: _ => .error .typeError
  | values, indices, key :: keys, i :: rest => do
      let ai ← combine i outer
      let ri ← combine i resultIndex
      let source ← readA array ai
      let mapped ← map f source
      let oldValue ← readValue values ri
      let oldIndex ← readIndex indices ri
      let unset ← isZeroKey oldIndex
      let better ← if unset then .ok true else compare op oldValue mapped
      let nextValues ← if better then writeValue values ri mapped else .ok values
      let nextIndices ← if better then writeIndex indices ri key else .ok indices
      directInnerLoop readA map readValue readIndex writeValue writeIndex compare isZeroKey combine
        f op array outer resultIndex nextValues nextIndices keys rest

def findOuterLoop (readA : A → Ix → JResult X) (map : F → X → JResult V)
    (readValue : Rv → Ix → JResult V) (readIndex : Ri → Ix → JResult K)
    (writeValue : Rv → Ix → V → JResult Rv) (writeIndex : Ri → Ix → K → JResult Ri)
    (compare : Op → V → V → JResult Bool) (isZeroKey : K → JResult Bool)
    (newIndex : Ix → Shape → JResult Ix) (combine : Ix → Ix → JResult Ix)
    (inner : List Ix) (firstResult : Ix) (shape : Shape) (reduceFirst : Bool)
    (f : F) (op : Op) (array : A) : Rv → Ri → List K → List Ix → JResult (Rv × Ri)
  | values, indices, _, [] => .ok (values, indices)
  | values, indices, keys, outer :: rest => do
      let resultIndex ← newIndex outer shape
      let location ← combine firstResult resultIndex
      if reduceFirst then do
        let initialValue ← readValue values location
        let initialIndex ← readIndex indices location
        let state ← tempInnerLoop readA map compare isZeroKey combine f op array outer
          initialValue initialIndex keys inner
        let nextValues ← writeValue values location state.1
        let nextIndices ← writeIndex indices location state.2.1
        findOuterLoop readA map readValue readIndex writeValue writeIndex compare isZeroKey newIndex combine
          inner firstResult shape reduceFirst f op array nextValues nextIndices state.2.2 rest
      else do
        let state ← directInnerLoop readA map readValue readIndex writeValue writeIndex compare isZeroKey combine
          f op array outer resultIndex values indices keys inner
        findOuterLoop readA map readValue readIndex writeValue writeIndex compare isZeroKey newIndex combine
          inner firstResult shape reduceFirst f op array state.1 state.2.1 state.2.2 rest

/-- `findminmax!`, lines 1032-1080. -/
def m1032 (isEmptyValues : Rv → JResult Bool) (isEmptyArray : A → JResult Bool)
    (checkReducedims : Rv → A → JResult Nat) (ndims : A → JResult Nat)
    (axesEqual : Rv → Ri → Nat → JResult Bool) (axesArray : A → JResult AX)
    (axesValues : Rv → JResult AX) (safeTail : AX → JResult Tail)
    (shapeIndexer : Tail → JResult Shape) (cartesian : Tail → JResult (List Ix))
    (keys : A → JResult (List K)) (zeroKey : A → JResult K) (keyEqual : K → K → JResult Bool)
    (reducedim1 : Rv → JResult Bool) (firstResult : Rv → JResult Ix)
    (axis1 : A → JResult (List Ix)) (newIndex : Ix → Shape → JResult Ix)
    (combine : Ix → Ix → JResult Ix) (readA : A → Ix → JResult X)
    (map : F → X → JResult V) (readValue : Rv → Ix → JResult V)
    (readIndex : Ri → Ix → JResult K) (writeValue : Rv → Ix → V → JResult Rv)
    (writeIndex : Ri → Ix → K → JResult Ri) (compare : Op → V → V → JResult Bool)
    (f : F) (op : Op) (values : Rv) (indices : Ri) (array : A) : JResult (Rv × Ri) := do
  let emptyValues ← isEmptyValues values
  let emptyArray ← isEmptyArray array
  if emptyValues || emptyArray then .ok (values, indices)
  else do
    let _ ← checkReducedims values array
    let rank ← ndims array
    checkOutputAxes axesEqual values indices 1 rank
    let aa ← axesArray array
    let rr ← axesValues values
    let aTail ← safeTail aa
    let rTail ← safeTail rr
    let shape ← shapeIndexer rTail
    let outer ← cartesian aTail
    let allKeys ← keys array
    let zero ← zeroKey array
    let reduceFirst ← reducedim1 values
    let first ← firstResult values
    let inner ← axis1 array
    findOuterLoop readA map readValue readIndex writeValue writeIndex compare (fun key => keyEqual key zero) newIndex combine
      inner first shape reduceFirst f op array values indices allKeys outer
def P1032 : Prop := ∀ {Rv Ri A AX Tail Shape Ix K X F V Op : Type} isEmptyValues isEmptyArray
    checkReducedims ndims axesEqual axesArray axesValues safeTail shapeIndexer cartesian keys zeroKey keyEqual
    reducedim1 firstResult axis1 newIndex combine readA map readValue readIndex writeValue writeIndex compare
    f op values indices array,
  m1032 (Rv := Rv) (Ri := Ri) (A := A) (AX := AX) (Tail := Tail) (Shape := Shape)
    (Ix := Ix) (K := K) (X := X) (F := F) (V := V) (Op := Op)
    isEmptyValues isEmptyArray checkReducedims ndims axesEqual axesArray axesValues safeTail shapeIndexer
    cartesian keys zeroKey keyEqual reducedim1 firstResult axis1 newIndex combine readA map readValue readIndex
    writeValue writeIndex compare f op values indices array = do
      let emptyValues ← isEmptyValues values
      let emptyArray ← isEmptyArray array
      if emptyValues || emptyArray then .ok (values, indices)
      else do
        let _ ← checkReducedims values array
        let rank ← ndims array
        checkOutputAxes axesEqual values indices 1 rank
        let aa ← axesArray array
        let rr ← axesValues values
        let aTail ← safeTail aa
        let rTail ← safeTail rr
        let shape ← shapeIndexer rTail
        let outer ← cartesian aTail
        let allKeys ← keys array
        let zero ← zeroKey array
        let reduceFirst ← reducedim1 values
        let first ← firstResult values
        let inner ← axis1 array
        findOuterLoop readA map readValue readIndex writeValue writeIndex compare (fun key => keyEqual key zero) newIndex combine
          inner first shape reduceFirst f op array values indices allKeys outer
theorem p1032 : P1032 := by unfold P1032; intros; rfl

/-- `findmin!`, lines 1091-1094. -/
def m1091 (isEmpty : A → JResult Bool) (first : A → JResult V)
    (fillValues : Rv → V → JResult Rv) (keyType : A → JResult KT)
    (zero : KT → JResult K) (fillIndices : Ri → K → JResult Ri)
    (findminmax : IdentityT → Cmp → Rv → Ri → A → JResult (Rv × Ri))
    (identity : IdentityT) (isgreater : Cmp) (values : Rv) (indices : Ri) (array : A)
    (init : Bool) : JResult (Rv × Ri) := do
  let empty ← isEmpty array
  let initializedValues ← if init && !empty then do let value ← first array; fillValues values value else .ok values
  let kt ← keyType array
  let z ← zero kt
  let initializedIndices ← fillIndices indices z
  findminmax identity isgreater initializedValues initializedIndices array
def P1091 : Prop := ∀ {A V Rv KT K Ri IdentityT Cmp : Type} isEmpty first fillValues keyType zero fillIndices
    findminmax identity isgreater values indices array init,
  m1091 (A := A) (V := V) (Rv := Rv) (KT := KT) (K := K) (Ri := Ri) (IdentityT := IdentityT) (Cmp := Cmp)
    isEmpty first fillValues keyType zero fillIndices findminmax identity isgreater values indices array init = do
      let empty ← isEmpty array
      let initializedValues ← if init && !empty then do let value ← first array; fillValues values value else .ok values
      let kt ← keyType array
      let z ← zero kt
      let initializedIndices ← fillIndices indices z
      findminmax identity isgreater initializedValues initializedIndices array
theorem p1091 : P1091 := by unfold P1091; intros; rfl

/-- `_findmin(A,dims)`, line 1117. -/
def m1117 (findmin : IdentityT → A → D → JResult R) (identity : IdentityT)
    (array : A) (dims : D) : JResult R := findmin identity array dims
def P1117 : Prop := ∀ {IdentityT A D R : Type} findmin identity array dims,
  m1117 (IdentityT := IdentityT) (A := A) (D := D) (R := R) findmin identity array dims =
    findmin identity array dims
theorem p1117 : P1117 := by unfold P1117 m1117; intros; rfl

def findDim (reducedIndices0 reducedIndices : A → D → JResult RI)
    (isEmpty : A → JResult Bool) (sliceLengthProduct : RI → JResult Nat)
    (eltype : A → JResult T) (promoteOp : F → T → JResult RT)
    (similar : A → RT → RI → JResult RV) (keyType : A → JResult KT)
    (zeros : KT → RI → JResult RIx) (first : A → JResult X)
    (map : F → X → JResult V) (initType : F → A → JResult RT)
    (fillSimilar : A → RT → RI → V → JResult RV)
    (findminmax : F → Cmp → RV → RIx → A → JResult (RV × RIx))
    (compare : Cmp) (f : F) (array : A) (region : D) : JResult (RV × RIx) := do
  let ri ← reducedIndices0 array region
  let empty ← isEmpty array
  if empty then do
    let reduced ← reducedIndices array region
    let product ← sliceLengthProduct reduced
    if product != 0 then .error (.argument (.literal "collection slices must be non-empty"))
    let ty ← eltype array
    let resultType ← promoteOp f ty
    let values ← similar array resultType ri
    let kt ← keyType array
    let indices ← zeros kt ri
    .ok (values, indices)
  else do
    let x ← first array
    let fx ← map f x
    let resultType ← initType f array
    let values ← fillSimilar array resultType ri fx
    let kt ← keyType array
    let indices ← zeros kt ri
    findminmax f compare values indices array

def P1141 : Prop := ∀ {A D RI T F RT RV KT RIx X V Cmp : Type} reducedIndices0 reducedIndices
    isEmpty sliceLengthProduct eltype promoteOp similar keyType zeros first map initType fillSimilar
    findminmax compare f array region,
  findDim (A := A) (D := D) (RI := RI) (T := T) (F := F) (RT := RT) (RV := RV)
    (KT := KT) (RIx := RIx) (X := X) (V := V) (Cmp := Cmp)
    reducedIndices0 reducedIndices isEmpty sliceLengthProduct eltype promoteOp similar keyType zeros
    first map initType fillSimilar findminmax compare f array region = do
      let ri ← reducedIndices0 array region
      let empty ← isEmpty array
      if empty then do
        let reduced ← reducedIndices array region
        let product ← sliceLengthProduct reduced
        if product != 0 then .error (.argument (.literal "collection slices must be non-empty"))
        let ty ← eltype array
        let resultType ← promoteOp f ty
        let values ← similar array resultType ri
        let kt ← keyType array
        let indices ← zeros kt ri
        .ok (values, indices)
      else do
        let x ← first array
        let fx ← map f x
        let resultType ← initType f array
        let values ← fillSimilar array resultType ri fx
        let kt ← keyType array
        let indices ← zeros kt ri
        findminmax f compare values indices array
theorem p1141 : P1141 := by unfold P1141; intros; rfl

/-- `findmax!`, lines 1164-1167, with the same initialization chain as findmin!. -/
def P1164 : Prop := ∀ {A V Rv KT K Ri IdentityT Cmp : Type} isEmpty first fillValues keyType zero fillIndices
    findminmax identity isless values indices array init,
  m1091 (A := A) (V := V) (Rv := Rv) (KT := KT) (K := K) (Ri := Ri) (IdentityT := IdentityT) (Cmp := Cmp)
    isEmpty first fillValues keyType zero fillIndices findminmax identity isless values indices array init = do
      let empty ← isEmpty array
      let initializedValues ← if init && !empty then do let value ← first array; fillValues values value else .ok values
      let kt ← keyType array
      let z ← zero kt
      let initializedIndices ← fillIndices indices z
      findminmax identity isless initializedValues initializedIndices array
theorem p1164 : P1164 := by unfold P1164; intros; rfl

/-- `_findmax(A,dims)`, line 1190. -/
def m1190 (findmax : IdentityT → A → D → JResult R) (identity : IdentityT)
    (array : A) (dims : D) : JResult R := findmax identity array dims
def P1190 : Prop := ∀ {IdentityT A D R : Type} findmax identity array dims,
  m1190 (IdentityT := IdentityT) (A := A) (D := D) (R := R) findmax identity array dims =
    findmax identity array dims
theorem p1190 : P1190 := by unfold P1190 m1190; intros; rfl

/-- `_findmax(f,A,region)`, lines 1214-1226. -/
def P1214 : Prop := P1141
theorem p1214 : P1214 := p1141

/-- `_findminmax_inittype`, lines 1228-1236. -/
def m1228 (eltype : A → JResult TypeTree) (promoteType : Nat → Nat → JResult Nat)
    (realtype : F → Nat → JResult TypeToken) (first : A → JResult X)
    (map : F → X → JResult V) (isInstance : V → TypeToken → JResult Bool)
    (containsMissing : TypeTree → JResult Bool) (typeOf : V → JResult TypeToken)
    (unionMissing : TypeToken → JResult TypeToken) (f : F) (array : A) : JResult TypeToken := do
  let tree ← eltype array
  let promoted ← promoteUnion promoteType tree
  let target ← realtype f promoted
  let x ← first array
  let initial ← map f x
  let same ← isInstance initial target
  if same then .ok target
  else do
    let missing ← containsMissing tree
    let actual ← typeOf initial
    if missing then unionMissing actual else .ok actual
def P1228 : Prop := ∀ {A F X V : Type} eltype promoteType realtype first map isInstance
    containsMissing typeOf unionMissing f array,
  m1228 (A := A) (F := F) (X := X) (V := V) eltype promoteType realtype first map
    isInstance containsMissing typeOf unionMissing f array = do
      let tree ← eltype array
      let promoted ← promoteUnion promoteType tree
      let target ← realtype f promoted
      let x ← first array
      let initial ← map f x
      let same ← isInstance initial target
      if same then .ok target
      else do
        let missing ← containsMissing tree
        let actual ← typeOf initial
        if missing then unionMissing actual else .ok actual
theorem p1228 : P1228 := by unfold P1228; intros; rfl

/-- `argmin(A;dims)`, line 1263. -/
def m1263 (findmin : A → D → JResult (V × I)) (array : A) (dims : D) : JResult I := do
  let result ← findmin array dims
  .ok result.2
def P1263 : Prop := ∀ {A D V I : Type} findmin array dims,
  m1263 (A := A) (D := D) (V := V) (I := I) findmin array dims = do
    let result ← findmin array dims
    .ok result.2
theorem p1263 : P1263 := by unfold P1263; intros; rfl

/-- `argmax(A;dims)`, line 1288. -/
def m1288 (findmax : A → D → JResult (V × I)) (array : A) (dims : D) : JResult I := do
  let result ← findmax array dims
  .ok result.2
def P1288 : Prop := ∀ {A D V I : Type} findmax array dims,
  m1288 (A := A) (D := D) (V := V) (I := I) findmax array dims = do
    let result ← findmax array dims
    .ok result.2
theorem p1288 : P1288 := by unfold P1288; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-reducedim-faithful-{line}", juliaFile := "base/reducedim.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.ReducedimFaithfulB
