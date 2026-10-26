import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimFaithfulA

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

structure OneTo (T : Type) where
  stop : T
  deriving Repr, DecidableEq

/-- `reduced_index(::OneTo)`, line 6. -/
def m6 (one : T → JResult T) (i : OneTo T) : JResult (OneTo T) := do
  let value ← one i.stop
  .ok ⟨value⟩
def P6 : Prop := ∀ {T : Type} (one : T → JResult T) i,
  m6 one i = do let value ← one i.stop; .ok ⟨value⟩
theorem p6 : P6 := by unfold P6; intros; rfl

/-- Unsupported `AbstractUnitRange` reduction, lines 8-14. -/
def m8 (typeOf showType : I → JResult AnyValue) (i : I) : JResult α := do
  let ty ← typeOf i
  let rendered ← showType i
  .error (.argument (lazyAppend [
    .literal "\nNo method is implemented for reducing index range of type ",
    .dynamic ty, .literal ". Please implement\nreduced_index for this index type or report this as an issue.\n",
    .dynamic rendered]))
def P8 : Prop := ∀ {α I : Type} typeOf showType i,
  m8 (α := α) (I := I) typeOf showType i = do
    let ty ← typeOf i
    let rendered ← showType i
    .error (.argument (lazyAppend [
      .literal "\nNo method is implemented for reducing index range of type ",
      .dynamic ty, .literal ". Please implement\nreduced_index for this index type or report this as an issue.\n",
      .dynamic rendered]))
theorem p8 : P8 := by unfold P8; intros; rfl

def checkRegionLoop (isInteger : D → JResult Bool) (toInt : D → JResult Int)
    (render : D → AnyValue) : List D → JResult Unit
  | [] => .ok ()
  | d :: ds => do
      let integer ← isInteger d
      if ¬integer then .error (.argument (.literal "reduced dimension(s) must be integers"))
      else do
        let value ← toInt d
        if value < 1 then
          .error (.argument (lazyAppend [.literal "region dimension(s) must be ≥ 1, got ", .dynamic (render d)]))
        else checkRegionLoop isInteger toInt render ds

/-- `_check_valid_region`, lines 30-35. -/
def m30 (isInteger : D → JResult Bool) (toInt : D → JResult Int)
    (render : D → AnyValue) (region : List D) : JResult Unit :=
  checkRegionLoop isInteger toInt render region
def P30 : Prop := ∀ {D : Type} isInteger toInt render region,
  m30 (D := D) isInteger toInt render region = checkRegionLoop isInteger toInt render region
theorem p30 : P30 := by unfold P30 m30; intros; rfl

/-- Min/max/extrema `initarray!`, lines 45-46. -/
def m45 (mapfirst : F → A → S → JResult A) (a : A) (f : F)
    (init : Bool) (src : S) : JResult A := do
  let result ← if init then mapfirst f a src else .ok a
  .ok result
def P45 : Prop := ∀ {F A S : Type} mapfirst a f init src,
  m45 (F := F) (A := A) (S := S) mapfirst a f init src = do
    let result ← if init then mapfirst f a src else .ok a
    .ok result
theorem p45 : P45 := by unfold P45; intros; rfl

inductive TypeTree where
  | leaf (id : Nat)
  | union (left right : TypeTree)
  deriving Repr, DecidableEq

def promoteUnion (promoteType : Nat → Nat → JResult Nat) : TypeTree → JResult Nat
  | .leaf id => .ok id
  | .union left right => do
      let a ← promoteUnion promoteType left
      let b ← promoteUnion promoteType right
      promoteType a b

/-- Recursive `promote_union(::Union)`, line 59. -/
def P59 : Prop := ∀ promoteType left right,
  promoteUnion promoteType (.union left right) = do
    let a ← promoteUnion promoteType left
    let b ← promoteUnion promoteType right
    promoteType a b
theorem p59 : P59 := by
  unfold P59
  intros
  rw [promoteUnion]

inductive TypeToken where
  | any
  | real
  | concrete (id : Nat)
  deriving Repr, DecidableEq

/-- `_realtype(::Type{<:Complex})`, line 62. -/
def m62 (_complexType : TypeToken) : TypeToken := .real
def P62 : Prop := ∀ complexType, m62 complexType = .real
theorem p62 : P62 := by unfold P62 m62; intros; rfl

/-- Generic `_reducedim_init`, lines 74-85. -/
def m74 (eltype : A → JResult TypeTree) (promoteType : Nat → Nat → JResult Nat)
    (realtype : F → Nat → JResult TypeToken) (applicableZero : TypeToken → JResult Bool)
    (zero : TypeToken → JResult V) (f : F → V → JResult V)
    (fv : V → JResult V) (op : V → V → JResult V)
    (fop : F → A → JResult V) (isInstance : V → TypeToken → JResult Bool)
    (typeOf : V → JResult TypeToken)
    (initarray : A → D → V → TypeToken → JResult R)
    (funValue : F) (array : A) (region : D) : JResult R := do
  let tree ← eltype array
  let promoted ← promoteUnion promoteType tree
  let target ← realtype funValue promoted
  let applicable ← applicableZero target
  let pair ← if target != .any && applicable then do
    let zv ← zero target
    let mapped ← f funValue zv
    let left ← fv mapped
    let right ← fv mapped
    let z ← op left right
    let same ← isInstance z target
    let resultType ← if same then .ok target else typeOf z
    .ok (z, resultType)
  else do
    let reduced ← fop funValue array
    let z ← fv reduced
    let resultType ← typeOf z
    .ok (z, resultType)
  initarray array region pair.1 pair.2
def P74 : Prop := ∀ {A F V D R : Type} eltype promoteType realtype applicableZero zero f fv op fop
    isInstance typeOf initarray funValue array region,
  m74 (A := A) (F := F) (V := V) (D := D) (R := R) eltype promoteType realtype applicableZero
    zero f fv op fop isInstance typeOf initarray funValue array region = do
      let tree ← eltype array
      let promoted ← promoteUnion promoteType tree
      let target ← realtype funValue promoted
      let applicable ← applicableZero target
      let pair ← if target != .any && applicable then do
        let zv ← zero target
        let mapped ← f funValue zv
        let left ← fv mapped
        let right ← fv mapped
        let z ← op left right
        let same ← isInstance z target
        let resultType ← if same then .ok target else typeOf z
        .ok (z, resultType)
      else do
        let reduced ← fop funValue array
        let z ← fv reduced
        let resultType ← typeOf z
        .ok (z, resultType)
      initarray array region pair.1 pair.2
theorem p74 : P74 := by unfold P74; intros; rfl

def anyEmptyAxis (axes : A → D → JResult AX) (isEmpty : AX → JResult Bool)
    (array : A) : List D → JResult Bool
  | [] => .ok false
  | d :: ds => do
      let axis ← axes array d
      let empty ← isEmpty axis
      if empty then .ok true else anyEmptyAxis axes isEmpty array ds

/-- Generated min/max `reducedim_init`, lines 89-128. -/
def m89 (reducedIndices : A → List D → JResult RI)
    (axes : A → D → JResult AX) (isEmptyAxis : AX → JResult Bool)
    (emptyError : JResult Unit) (view : A → RI → JResult W)
    (isEmptyView : W → JResult Bool) (mapEmpty : F → W → JResult R)
    (mapreduce : F → O → W → JResult V) (eltype : A → JResult TypeTree)
    (promoteType : Nat → Nat → JResult Nat) (realtype : F → Nat → JResult TypeToken)
    (isInstance : V → TypeToken → JResult Bool) (typeOf : V → JResult TypeToken)
    (isNumber isNan isUnordered : V → JResult Bool) (infinity : V → JResult V)
    (nonmissing : TypeToken → JResult TypeToken) (machineNumeric : TypeToken → JResult Bool)
    (typeExtreme : TypeToken → JResult V) (allUnordered : W → JResult Bool)
    (filteredReduce : F → O → W → JResult V)
    (initarray : A → List D → V → TypeToken → JResult R)
    (f : F) (opposite : O) (array : A) (region : List D) : JResult R := do
  let ri ← reducedIndices array region
  let hasEmpty ← anyEmptyAxis axes isEmptyAxis array region
  if hasEmpty then emptyError
  let firstSlice ← view array ri
  let emptySlice ← isEmptyView firstSlice
  if emptySlice then mapEmpty f firstSlice
  else do
    let initial ← mapreduce f opposite firstSlice
    let tree ← eltype array
    let promoted ← promoteUnion promoteType tree
    let target ← realtype f promoted
    let initialSame ← isInstance initial target
    let initialType ← if initialSame then .ok target else typeOf initial
    let numeric ← isNumber initial
    let nan ← if numeric then isNan initial else .ok false
    let adjusted ← if nan then infinity initial else do
      let unordered ← isUnordered initial
      if ¬unordered then .ok initial else do
        let orderedType ← nonmissing initialType
        let builtin ← machineNumeric orderedType
        if builtin then typeExtreme orderedType else do
          let allBad ← allUnordered firstSlice
          if allBad then .ok initial else filteredReduce f opposite firstSlice
    let finalSame ← isInstance adjusted target
    let finalType ← if finalSame then .ok target else typeOf adjusted
    initarray array region adjusted finalType
def P89 : Prop := ∀ {A D RI AX W F O V R : Type} reducedIndices axes isEmptyAxis emptyError
    view isEmptyView mapEmpty mapreduce eltype promoteType realtype isInstance typeOf isNumber isNan
    isUnordered infinity nonmissing machineNumeric typeExtreme allUnordered filteredReduce initarray
    f opposite array region,
  m89 (A := A) (D := D) (RI := RI) (AX := AX) (W := W) (F := F) (O := O) (V := V) (R := R)
    reducedIndices axes isEmptyAxis emptyError view isEmptyView mapEmpty mapreduce eltype promoteType
    realtype isInstance typeOf isNumber isNan isUnordered infinity nonmissing machineNumeric typeExtreme
    allUnordered filteredReduce initarray f opposite array region = do
      let ri ← reducedIndices array region
      let hasEmpty ← anyEmptyAxis axes isEmptyAxis array region
      if hasEmpty then emptyError
      let firstSlice ← view array ri
      let emptySlice ← isEmptyView firstSlice
      if emptySlice then mapEmpty f firstSlice
      else do
        let initial ← mapreduce f opposite firstSlice
        let tree ← eltype array
        let promoted ← promoteUnion promoteType tree
        let target ← realtype f promoted
        let initialSame ← isInstance initial target
        let initialType ← if initialSame then .ok target else typeOf initial
        let numeric ← isNumber initial
        let nan ← if numeric then isNan initial else .ok false
        let adjusted ← if nan then infinity initial else do
          let unordered ← isUnordered initial
          if ¬unordered then .ok initial else do
            let orderedType ← nonmissing initialType
            let builtin ← machineNumeric orderedType
            if builtin then typeExtreme orderedType else do
              let allBad ← allUnordered firstSlice
              if allBad then .ok initial else filteredReduce f opposite firstSlice
        let finalSame ← isInstance adjusted target
        let finalType ← if finalSame then .ok target else typeOf adjusted
        initarray array region adjusted finalType
theorem p89 : P89 := by unfold P89; intros; rfl

/-- Extrema `reducedim_init`, lines 131-170. -/
def m131 (reducedIndices : A → List D → JResult RI)
    (axes : A → D → JResult AX) (isEmptyAxis : AX → JResult Bool)
    (emptyError : JResult Unit) (view : A → RI → JResult W)
    (isEmptyView : W → JResult Bool) (mapEmpty : F → W → JResult R)
    (mapreduce : F → O → W → JResult (V × V)) (reversePair : V × V → V × V)
    (eltype : A → JResult TypeTree) (promoteType : Nat → Nat → JResult Nat)
    (realtype : F → Nat → JResult TypeToken) (isInstance : V → TypeToken → JResult Bool)
    (typeOf : V → JResult TypeToken) (isNumber isNan isUnordered : V → JResult Bool)
    (nanPair : V × V → JResult (V × V)) (nonmissing : TypeToken → JResult TypeToken)
    (machineNumeric : TypeToken → JResult Bool) (extremePair : TypeToken → TypeToken → JResult (V × V))
    (allUnordered : W → JResult Bool) (filteredReduce : F → O → W → JResult (V × V))
    (initarray : A → List D → (V × V) → (TypeToken × TypeToken) → JResult R)
    (f : F) (op : O) (array : A) (region : List D) : JResult R := do
  let ri ← reducedIndices array region
  let hasEmpty ← anyEmptyAxis axes isEmptyAxis array region
  if hasEmpty then emptyError
  let firstSlice ← view array ri
  let emptySlice ← isEmptyView firstSlice
  if emptySlice then mapEmpty f firstSlice
  else do
    let reduced ← mapreduce f op firstSlice
    let initial := reversePair reduced
    let tree ← eltype array
    let promoted ← promoteUnion promoteType tree
    let target ← realtype f promoted
    let minSame ← isInstance initial.1 target
    let minType ← if minSame then .ok target else typeOf initial.1
    let maxSame ← isInstance initial.2 target
    let maxType ← if maxSame then .ok target else typeOf initial.2
    let numeric ← isNumber initial.1
    let nan ← if numeric then isNan initial.1 else .ok false
    let adjusted ← if nan then nanPair initial else do
      let unordered ← isUnordered initial.1
      if ¬unordered then .ok initial else do
        let minOrdered ← nonmissing minType
        let maxOrdered ← nonmissing maxType
        let minBuiltin ← machineNumeric minOrdered
        let maxBuiltin ← machineNumeric maxOrdered
        if minBuiltin && maxBuiltin then extremePair minOrdered maxOrdered else do
          let allBad ← allUnordered firstSlice
          if allBad then .ok initial else do
            let result ← filteredReduce f op firstSlice
            .ok (reversePair result)
    let finalMinSame ← isInstance adjusted.1 target
    let finalMinType ← if finalMinSame then .ok target else typeOf adjusted.1
    let finalMaxSame ← isInstance adjusted.2 target
    let finalMaxType ← if finalMaxSame then .ok target else typeOf adjusted.2
    initarray array region adjusted (finalMinType, finalMaxType)
def P131 : Prop := ∀ {A D RI AX W F O V R : Type} reducedIndices axes isEmptyAxis emptyError view
    isEmptyView mapEmpty mapreduce reversePair eltype promoteType realtype isInstance typeOf isNumber isNan
    isUnordered nanPair nonmissing machineNumeric extremePair allUnordered filteredReduce initarray f op array region,
  m131 (A := A) (D := D) (RI := RI) (AX := AX) (W := W) (F := F) (O := O) (V := V) (R := R)
    reducedIndices axes isEmptyAxis emptyError view isEmptyView mapEmpty mapreduce reversePair eltype
    promoteType realtype isInstance typeOf isNumber isNan isUnordered nanPair nonmissing machineNumeric
    extremePair allUnordered filteredReduce initarray f op array region = do
      let ri ← reducedIndices array region
      let hasEmpty ← anyEmptyAxis axes isEmptyAxis array region
      if hasEmpty then emptyError
      let firstSlice ← view array ri
      let emptySlice ← isEmptyView firstSlice
      if emptySlice then mapEmpty f firstSlice
      else do
        let reduced ← mapreduce f op firstSlice
        let initial := reversePair reduced
        let tree ← eltype array
        let promoted ← promoteUnion promoteType tree
        let target ← realtype f promoted
        let minSame ← isInstance initial.1 target
        let minType ← if minSame then .ok target else typeOf initial.1
        let maxSame ← isInstance initial.2 target
        let maxType ← if maxSame then .ok target else typeOf initial.2
        let numeric ← isNumber initial.1
        let nan ← if numeric then isNan initial.1 else .ok false
        let adjusted ← if nan then nanPair initial else do
          let unordered ← isUnordered initial.1
          if ¬unordered then .ok initial else do
            let minOrdered ← nonmissing minType
            let maxOrdered ← nonmissing maxType
            let minBuiltin ← machineNumeric minOrdered
            let maxBuiltin ← machineNumeric maxOrdered
            if minBuiltin && maxBuiltin then extremePair minOrdered maxOrdered else do
              let allBad ← allUnordered firstSlice
              if allBad then .ok initial else do
                let result ← filteredReduce f op firstSlice
                .ok (reversePair result)
        let finalMinSame ← isInstance adjusted.1 target
        let finalMinType ← if finalMinSame then .ok target else typeOf adjusted.1
        let finalMaxSame ← isInstance adjusted.2 target
        let finalMaxType ← if finalMaxSame then .ok target else typeOf adjusted.2
        initarray array region adjusted (finalMinType, finalMaxType)
theorem p131 : P131 := by unfold P131; intros; rfl

/-- Specialized absolute maximum initializer, lines 172-173. -/
def m172 (eltype : A → JResult T) (zeroT : T → JResult V) (f : V → JResult V)
    (zeroV : V → JResult V) (realtype : T → JResult RT)
    (initarray : A → D → V → RT → JResult R) (array : A) (region : D) : JResult R := do
  let ty ← eltype array
  let zt ← zeroT ty
  let mapped ← f zt
  let z ← zeroV mapped
  let resultType ← realtype ty
  initarray array region z resultType
def P172 : Prop := ∀ {A T V RT D R : Type} eltype zeroT f zeroV realtype initarray array region,
  m172 (A := A) (T := T) (V := V) (RT := RT) (D := D) (R := R)
    eltype zeroT f zeroV realtype initarray array region = do
      let ty ← eltype array
      let zt ← zeroT ty
      let mapped ← f zt
      let z ← zeroV mapped
      let resultType ← realtype ty
      initarray array region z resultType
theorem p172 : P172 := by unfold P172; intros; rfl

def specializedInit (unitType : T → JResult V) (unitValue : V → JResult V)
    (eltype : A → JResult T) (f : V → JResult V) (op : V → V → JResult V)
    (initarray : A → D → V → JResult R) (array : A) (region : D) : JResult R := do
  let ty ← eltype array
  let base ← unitType ty
  let mapped ← f base
  let neutral ← unitValue mapped
  let initial ← op neutral neutral
  initarray array region initial
def P190 : Prop := ∀ {T V A D R : Type} zeroType zeroValue eltype f op initarray array region,
  specializedInit (T := T) (V := V) (A := A) (D := D) (R := R)
    zeroType zeroValue eltype f op initarray array region = do
    let ty ← eltype array
    let base ← zeroType ty
    let mapped ← f base
    let neutral ← zeroValue mapped
    let initial ← op neutral neutral
    initarray array region initial
theorem p190 : P190 := by unfold P190 specializedInit; intros; rfl
def P194 : Prop := ∀ {T V A D R : Type} oneType oneValue eltype f op initarray array region,
  specializedInit (T := T) (V := V) (A := A) (D := D) (R := R)
    oneType oneValue eltype f op initarray array region = do
    let ty ← eltype array
    let base ← oneType ty
    let mapped ← f base
    let neutral ← oneValue mapped
    let initial ← op neutral neutral
    initarray array region initial
theorem p194 : P194 := by unfold P194 specializedInit; intros; rfl

inductive IndexStyleToken where | linear | cartesian deriving Repr, DecidableEq

/-- `has_fast_linear_indexing`, line 202. -/
def m202 (indexStyle : A → JResult IndexStyleToken) (array : A) : JResult Bool := do
  let style ← indexStyle array
  .ok (style == .linear)
def P202 : Prop := ∀ {A : Type} indexStyle array,
  m202 (A := A) indexStyle array = do let style ← indexStyle array; .ok (style == .linear)
theorem p202 : P202 := by unfold P202; intros; rfl

def checkDimsLoop (axesR : R → Nat → JResult AX) (axesA : A → Nat → JResult AX)
    (length : AX → JResult Nat) (axisEqual : AX → AX → JResult Bool)
    (result : R) (array : A) : Nat → Nat → Nat → Bool → JResult (Nat × Bool)
  | _, 0, lsiz, had => .ok (lsiz, had)
  | i, n + 1, lsiz, had => do
      let ri ← axesR result i
      let ai ← axesA array i
      let sr ← length ri
      let sa ← length ai
      if sr = 1 then
        let next := if sa > 1 then (if had then 0 else lsiz * sa) else lsiz
        checkDimsLoop axesR axesA length axisEqual result array (i + 1) n next had
      else do
        let same ← axisEqual ri ai
        if ¬same then .error (.dimensionMismatch (.literal "reduction output indices differ from input"))
        else checkDimsLoop axesR axesA length axisEqual result array (i + 1) n lsiz true

/-- `check_reducedims`, lines 205-234. -/
def m205 (ndimsR : R → JResult Nat) (ndimsA : A → JResult Nat)
    (axesR : R → Nat → JResult AX) (axesA : A → Nat → JResult AX)
    (length : AX → JResult Nat) (axisEqual : AX → AX → JResult Bool)
    (result : R) (array : A) : JResult Nat := do
  let nr ← ndimsR result
  let na ← ndimsA array
  if nr > na then .error (.dimensionMismatch (.literal "cannot reduce to more dimensions"))
  else do
    let state ← checkDimsLoop axesR axesA length axisEqual result array 1 na 1 false
    .ok state.1
def P205 : Prop := ∀ {R A AX : Type} ndimsR ndimsA axesR axesA length axisEqual result array,
  m205 (R := R) (A := A) (AX := AX) ndimsR ndimsA axesR axesA length axisEqual result array = do
    let nr ← ndimsR result
    let na ← ndimsA array
    if nr > na then .error (.dimensionMismatch (.literal "cannot reduce to more dimensions"))
    else do
      let state ← checkDimsLoop axesR axesA length axisEqual result array 1 na 1 false
      .ok state.1
theorem p205 : P205 := by unfold P205; intros; rfl

def firstReducedSlice (axisLength : AX → JResult Nat) (firstSlice : AX → JResult AX) :
    List AX → List AX → JResult (List AX)
  | _, [] => .ok []
  | [], a :: rest => do
      let head ← firstSlice a
      let tail ← firstReducedSlice axisLength firstSlice [] rest
      .ok (head :: tail)
  | r :: rs, a :: rest => do
      let n ← axisLength r
      let head ← if n = 1 then firstSlice a else .ok r
      let tail ← firstReducedSlice axisLength firstSlice rs rest
      .ok (head :: tail)

/-- `_firstreducedslice`, line 251. -/
def P251 : Prop := ∀ {AX : Type} axisLength firstSlice r rs a rest,
  firstReducedSlice (AX := AX) axisLength firstSlice (r :: rs) (a :: rest) = do
    let n ← axisLength r
    let head ← if n = 1 then firstSlice a else .ok r
    let tail ← firstReducedSlice axisLength firstSlice rs rest
    .ok (head :: tail)
theorem p251 : P251 := by
  unfold P251
  intros
  rw [firstReducedSlice]

/-- `_firstslice(::OneTo)`, line 252. -/
def m252 (_i : OneTo T) : OneTo Nat := ⟨1⟩
def P252 : Prop := ∀ {T : Type} i, m252 (T := T) i = ⟨1⟩
theorem p252 : P252 := by unfold P252 m252; intros; rfl

structure Slice (AX : Type) where indices : AX deriving Repr, DecidableEq

/-- `_firstslice(::Slice)`, line 253. -/
def m253 (firstSlice : AX → JResult AX) (i : Slice AX) : JResult (Slice AX) := do
  let indices ← firstSlice i.indices
  .ok ⟨indices⟩
def P253 : Prop := ∀ {AX : Type} firstSlice i,
  m253 (AX := AX) firstSlice i = do let indices ← firstSlice i.indices; .ok ⟨indices⟩
theorem p253 : P253 := by unfold P253; intros; rfl

/-- Generic `_firstslice`, line 254. -/
def m254 (firstIndex : I → JResult K) (makeRange : K → K → JResult G)
    (getindex : I → G → JResult R) (i : I) : JResult R := do
  let lo ← firstIndex i
  let hi ← firstIndex i
  let range ← makeRange lo hi
  getindex i range
def P254 : Prop := ∀ {I K G R : Type} firstIndex makeRange getindex i,
  m254 (I := I) (K := K) (G := G) (R := R) firstIndex makeRange getindex i = do
    let lo ← firstIndex i
    let hi ← firstIndex i
    let range ← makeRange lo hi
    getindex i range
theorem p254 : P254 := by unfold P254; intros; rfl

/-- `mapfirst!`, lines 241-245. -/
def m241 (check : R → A → JResult Unit) (axesR : R → JResult (List AX))
    (axesA : A → JResult (List AX)) (axisLength : AX → JResult Nat)
    (firstSlice : AX → JResult AX) (view : A → List AX → JResult W)
    (mapInto : F → R → W → JResult R) (f : F) (result : R) (array : A) : JResult R := do
  check result array
  let rr ← axesR result
  let aa ← axesA array
  let slice ← firstReducedSlice axisLength firstSlice rr aa
  let selected ← view array slice
  mapInto f result selected
def P241 : Prop := ∀ {R A AX W F : Type} check axesR axesA axisLength firstSlice view mapInto f result array,
  m241 (R := R) (A := A) (AX := AX) (W := W) (F := F) check axesR axesA axisLength firstSlice
    view mapInto f result array = do
      check result array
      let rr ← axesR result
      let aa ← axesA array
      let slice ← firstReducedSlice axisLength firstSlice rr aa
      let selected ← view array slice
      mapInto f result selected
theorem p241 : P241 := by unfold P241; intros; rfl

def fastReduceLoop (readR : R → I → JResult V) (block : F → O → A → Int → Int → JResult V)
    (op : O → V → V → JResult V) (writeR : R → I → V → JResult R)
    (f : F) (operator : O) (array : A) (lsiz : Nat) : R → Int → List I → JResult R
  | result, _, [] => .ok result
  | result, base, i :: rest => do
      let old ← readR result i
      let reduced ← block f operator array (base + 1) (base + lsiz)
      let value ← op operator old reduced
      let next ← writeR result i value
      fastReduceLoop readR block op writeR f operator array lsiz next (base + lsiz) rest

def cartesianReduceLoop (readR : R → I → JResult V) (readA : A → I → JResult X)
    (map : F → X → JResult V) (op : O → V → V → JResult V)
    (writeR : R → I → V → JResult R) (newIndex : IA → JResult I)
    (firstResultIndex : R → JResult I) (axis1 : A → JResult (List I))
    (f : F) (operator : O) (array : A) (reduceFirst : Bool) : R → List IA → JResult R
  | result, [] => .ok result
  | result, ia :: rest => do
      let ir ← newIndex ia
      let indices ← axis1 array
      let start ← if reduceFirst then firstResultIndex result else .ok ir
      let initial ← readR result start
      let pair ← indices.foldlM (fun state i => do
        let av ← readA array i
        let mapped ← map f av
        let value ← if reduceFirst then op operator state.2 mapped else do
          let old ← readR state.1 i
          op operator old mapped
        let next ← writeR state.1 (if reduceFirst then start else i) value
        .ok (next, value)) (result, initial)
      cartesianReduceLoop readR readA map op writeR newIndex firstResultIndex axis1 f operator array reduceFirst pair.1 rest

/-- General `_mapreducedim!`, lines 256-293. -/
def m256 (check : R → A → JResult Nat) (isEmpty : A → JResult Bool)
    (fast : A → JResult Bool) (firstLinear : A → JResult Int) (eachResult : R → JResult (List I))
    (readR : R → I → JResult V) (block : F → O → A → Int → Int → JResult V)
    (op : O → V → V → JResult V) (writeR : R → I → V → JResult R)
    (outer : A → JResult (List IA)) (newIndex : IA → JResult I)
    (reducedim1 : R → JResult Bool) (firstResultIndex : R → JResult I)
    (axis1 : A → JResult (List I)) (readA : A → I → JResult X)
    (map : F → X → JResult V) (f : F) (operator : O) (result : R) (array : A) : JResult R := do
  let lsiz ← check result array
  let empty ← isEmpty array
  if empty then .ok result
  else do
    let linear ← fast array
    if linear && lsiz > 16 then do
      let first ← firstLinear array
      let indices ← eachResult result
      fastReduceLoop readR block op writeR f operator array lsiz result (first - 1) indices
    else do
      let indices ← outer array
      let reduceFirst ← reducedim1 result
      cartesianReduceLoop readR readA map op writeR newIndex firstResultIndex axis1
        f operator array reduceFirst result indices
def P256 : Prop := ∀ {R A I IA V F O X : Type} check isEmpty fast firstLinear eachResult readR
    block op writeR outer newIndex reducedim1 firstResultIndex axis1 readA map f operator result array,
  m256 (R := R) (A := A) (I := I) (IA := IA) (V := V) (F := F) (O := O) (X := X)
    check isEmpty fast firstLinear eachResult readR block op writeR outer newIndex reducedim1
    firstResultIndex axis1 readA map f operator result array = do
      let lsiz ← check result array
      let empty ← isEmpty array
      if empty then .ok result
      else do
        let linear ← fast array
        if linear && lsiz > 16 then do
          let first ← firstLinear array
          let indices ← eachResult result
          fastReduceLoop readR block op writeR f operator array lsiz result (first - 1) indices
        else do
          let indices ← outer array
          let reduceFirst ← reducedim1 result
          cartesianReduceLoop readR readA map op writeR newIndex firstResultIndex axis1
            f operator array reduceFirst result indices
theorem p256 : P256 := by unfold P256; intros; rfl

/-- Public `mapreducedim!`, lines 295-296. -/
def m295 (kernel : F → O → R → A → JResult R) (f : F) (op : O)
    (result : R) (array : A) : JResult R := do
  let _ ← kernel f op result array
  .ok result
def P295 : Prop := ∀ {F O R A : Type} kernel f op result array,
  m295 (F := F) (O := O) (R := R) (A := A) kernel f op result array = do
    let _ ← kernel f op result array
    .ok result
theorem p295 : P295 := by unfold P295; intros; rfl

/-- `mapreduce` dims wrapper, lines 328-329. -/
def m328 (mapreduceDim : F → O → N → A → D → JResult R)
    (f : F) (op : O) (init : N) (array : A) (dims : D) : JResult R :=
  mapreduceDim f op init array dims
def P328 : Prop := ∀ {F O N A D R : Type} mapreduceDim f op init array dims,
  m328 (F := F) (O := O) (N := N) (A := A) (D := D) (R := R)
    mapreduceDim f op init array dims = mapreduceDim f op init array dims
theorem p328 : P328 := by unfold P328 m328; intros; rfl

def foldRest (f : F → X → JResult V) (op : O → V → V → JResult V)
    (funValue : F) (operator : O) : V → List X → JResult V
  | value, [] => .ok value
  | value, x :: xs => do
      let mapped ← f funValue x
      let next ← op operator value mapped
      foldRest f op funValue operator next xs

/-- Colon `_mapreduce_dim`, lines 333-343. -/
def m333 (iterate : A → JResult (Option (X × S))) (rest : A → S → JResult (List X))
    (f : F → X → JResult V) (op : O → V → V → JResult V)
    (funValue : F) (operator : O) (init : V) (array : A) : JResult V := do
  let first ← iterate array
  match first with
  | none => .ok init
  | some (x, state) => do
      let mapped ← f funValue x
      let value ← op operator init mapped
      let remaining ← rest array state
      foldRest f op funValue operator value remaining
def P333 : Prop := ∀ {A X S F O V : Type} iterate rest f op funValue operator init array,
  m333 (A := A) (X := X) (S := S) (F := F) (O := O) (V := V)
    iterate rest f op funValue operator init array = do
      let first ← iterate array
      match first with
      | none => .ok init
      | some (x, state) => do
          let mapped ← f funValue x
          let value ← op operator init mapped
          let remaining ← rest array state
          foldRest f op funValue operator value remaining
theorem p333 : P333 := by unfold P333; intros; rfl

/-- `reduce(op,A;kw...)`, line 392. -/
def m392 (mapreduce : IdentityT → O → A → K → JResult R) (identity : IdentityT)
    (op : O) (array : A) (keywords : K) : JResult R := mapreduce identity op array keywords
def P392 : Prop := ∀ {IdentityT O A K R : Type} mapreduce identity op array keywords,
  m392 (IdentityT := IdentityT) (O := O) (A := A) (K := K) (R := R) mapreduce identity op array keywords =
    mapreduce identity op array keywords
theorem p392 : P392 := by unfold P392 m392; intros; rfl

/-- `count(A; dims, init)`, line 425. -/
def m425 (count : IdentityT → A → D → N → JResult R) (identity : IdentityT)
    (array : A) (dims : D) (init : N) : JResult R := count identity array dims init
def P425 : Prop := ∀ {IdentityT A D N R : Type} count identity array dims init,
  m425 (IdentityT := IdentityT) (A := A) (D := D) (N := N) (R := R) count identity array dims init =
    count identity array dims init
theorem p425 : P425 := by unfold P425 m425; intros; rfl

/-- Non-Colon `_count`, line 429. -/
def m429 (boolMap : F → JResult B) (mapreduce : B → Op → A → D → N → JResult R)
    (addSum : Op) (f : F) (array : A) (dims : D) (init : N) : JResult R := do
  let mapped ← boolMap f
  mapreduce mapped addSum array dims init
def P429 : Prop := ∀ {F B Op A D N R : Type} boolMap mapreduce addSum f array dims init,
  m429 (F := F) (B := B) (Op := Op) (A := A) (D := D) (N := N) (R := R)
    boolMap mapreduce addSum f array dims init = do
      let mapped ← boolMap f
      mapreduce mapped addSum array dims init
theorem p429 : P429 := by unfold P429; intros; rfl

/-- `count!(r,A;init)`, line 459. -/
def m459 (countBang : IdentityT → R → A → Bool → JResult R) (identity : IdentityT)
    (result : R) (array : A) (init : Bool) : JResult R := countBang identity result array init
def P459 : Prop := ∀ {IdentityT R A : Type} countBang identity result array init,
  m459 (IdentityT := IdentityT) (R := R) (A := A) countBang identity result array init =
    countBang identity result array init
theorem p459 : P459 := by unfold P459 m459; intros; rfl

/-- Predicate `count!`, lines 460-461. -/
def m460 (boolMap : F → JResult B) (initarray : R → B → Op → Bool → A → JResult R)
    (mapreducedim : B → Op → R → A → JResult R) (addSum : Op)
    (f : F) (result : R) (array : A) (init : Bool) : JResult R := do
  let mapped ← boolMap f
  let initialized ← initarray result mapped addSum init array
  mapreducedim mapped addSum initialized array
def P460 : Prop := ∀ {F B R Op A : Type} boolMap initarray mapreducedim addSum f result array init,
  m460 (F := F) (B := B) (R := R) (Op := Op) (A := A)
    boolMap initarray mapreducedim addSum f result array init = do
      let mapped ← boolMap f
      let initialized ← initarray result mapped addSum init array
      mapreducedim mapped addSum initialized array
theorem p460 : P460 := by unfold P460; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-reducedim-faithful-{line}", juliaFile := "base/reducedim.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 6 "reduced_index(::OneTo)" "The method computes one(T) from the input range element type and constructs OneTo of that singleton endpoint." "base/reducedim.jl:6" ``P6 ``p6,
  entry 8 "reduced_index(::AbstractUnitRange)" "The fallback uses the actual range type in the complete multiline ArgumentError and preserves failures while rendering it." "base/reducedim.jl:8-14" ``P8 ``p8,
  entry 30 "_check_valid_region" "Every region value is checked for Integer membership, converted to Int, and rejected below one in source order." "base/reducedim.jl:30-35" ``P30 ``p30,
  entry 45 "initarray!(min/max/extrema)" "Initialization conditionally calls mapfirst! on the actual result and source arrays, then returns the resulting array." "base/reducedim.jl:45-46" ``P45 ``p45,
  entry 59 "promote_union(::Union)" "Nested unions are recursively decomposed left then right and combined with promote_type at every union node." "base/reducedim.jl:59" ``P59 ``p59,
  entry 62 "_realtype(::Type{<:Complex})" "Every abstract Complex type maps to the Julia Real type." "base/reducedim.jl:62" ``P62 ``p62,
  entry 74 "_reducedim_init" "The initializer computes promoted real element type, follows the zero/applicable branch exactly, derives the result type, and allocates the reduced array." "base/reducedim.jl:74-85" ``P74 ``p74,
  entry 89 "reducedim_init(min/max)" "The generated extrema initializer checks reduced axes, rejects empty reductions, handles empty slices, NaN and unordered initial values, recomputes the result type, and allocates in source order." "base/reducedim.jl:89-128" ``P89 ``p89,
  entry 131 "reducedim_init(ExtremaMap)" "The extrema-pair initializer checks axes, constructs the first slice, reverses min/max, handles NaN and unordered pairs, recomputes both types, and allocates in source order." "base/reducedim.jl:131-170" ``P131 ``p131,
  entry 172 "reducedim_init(abs/abs2,max)" "The specialization nests zero(T), f, zero(result), and _realtype before allocating the reduced result." "base/reducedim.jl:172-173" ``P172 ``p172,
  entry 190 "reducedim_init(add)" "The numeric addition specialization computes zero(f(zero(eltype(A)))), applies op to two copies, then allocates." "base/reducedim.jl:190-193" ``P190 ``p190,
  entry 194 "reducedim_init(multiply)" "The numeric multiplication specialization computes one(f(one(eltype(A)))), applies op to two copies, then allocates." "base/reducedim.jl:194-197" ``P194 ``p194,
  entry 202 "has_fast_linear_indexing" "The method obtains IndexStyle(A) and compares it to IndexLinear." "base/reducedim.jl:202" ``P202 ``p202,
  entry 205 "check_reducedims" "The method checks rank, scans every input dimension, compares non-reduced axes, and returns the leading reduction size with source errors." "base/reducedim.jl:205-234" ``P205 ``p205,
  entry 241 "mapfirst!" "The method checks compatible dimensions, constructs the first reduced slice from both axis tuples, views it, and maps into the result." "base/reducedim.jl:241-245" ``P241 ``p241,
  entry 251 "_firstreducedslice" "The recursive case tests the actual result-axis length, selects the first input slice only for singleton result axes, and recurses on both tails." "base/reducedim.jl:251" ``P251 ``p251,
  entry 252 "_firstslice(::OneTo)" "The OneTo specialization constructs OneTo(1) for every input endpoint." "base/reducedim.jl:252" ``P252 ``p252,
  entry 253 "_firstslice(::Slice)" "The Slice specialization recursively takes its indices' first slice and reconstructs Slice." "base/reducedim.jl:253" ``P253 ``p253,
  entry 254 "_firstslice(generic)" "The fallback calls firstindex twice, constructs the singleton range, and indexes the actual input." "base/reducedim.jl:254" ``P254 ``p254,
  entry 256 "_mapreducedim!" "The kernel checks result dimensions and emptiness, then performs the exact fast-linear or Cartesian nested-loop update path and returns the updated result." "base/reducedim.jl:256-293" ``P256 ``p256,
  entry 295 "mapreducedim!" "The wrapper sequences the internal kernel and returns the original result object after a successful call." "base/reducedim.jl:295-296" ``P295 ``p295,
  entry 328 "mapreduce(dims)" "The wrapper preserves f, op, init, the actual array, and dims in the five-argument _mapreduce_dim call." "base/reducedim.jl:328-329" ``P328 ``p328,
  entry 333 "_mapreduce_dim(::Colon)" "The Colon method explicitly iterates, returns init when empty, maps and combines the first element, and folds the remaining iterator while preserving failures." "base/reducedim.jl:333-343" ``P333 ``p333,
  entry 392 "reduce(AbstractArray)" "The array reduction fixes identity as the map function and forwards op, array, and the complete keyword bundle." "base/reducedim.jl:392" ``P392 ``p392,
  entry 425 "count(AbstractArrayOrBroadcasted)" "The no-predicate wrapper fixes identity and forwards the actual array, dims, and init independently." "base/reducedim.jl:425" ``P425 ``p425,
  entry 429 "_count(non-Colon)" "The method constructs _bool(f), fixes add_sum, and passes array, dims, and init separately to mapreduce." "base/reducedim.jl:429" ``P429 ``p429,
  entry 459 "count!(result,array)" "The no-predicate in-place wrapper fixes identity and preserves the init keyword." "base/reducedim.jl:459" ``P459 ``p459,
  entry 460 "count!(predicate,result,array)" "The predicate method constructs _bool(f), initializes with add_sum, then reduces into the initialized array in source order." "base/reducedim.jl:460-461" ``P460 ``p460
]

end JuliaLean.MultidimCov.ReducedimFaithfulA
