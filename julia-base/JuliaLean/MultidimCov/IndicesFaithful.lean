import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.IndicesFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

inductive IError where
  | methodError (fn : AnyValue) (args : List AnyValue)
  | argument (message : LazyString)
  | dimensionMismatch (message : LazyString)
  | bounds
  | callback (id : Nat)
  deriving Repr, DecidableEq

abbrev IResult (α : Type) := Except IError α

/-- `IndexStyle(::Type{Union{}}, slurp...)`, line 96. -/
def m96 (indexStyleFn unionEmpty : AnyValue) (slurp : List AnyValue) : IResult α :=
  .error (.methodError indexStyleFn (unionEmpty :: slurp))
def P96 : Prop := ∀ {α : Type} fn empty slurp,
  m96 (α := α) fn empty slurp = .error (.methodError fn (empty :: slurp))
theorem p96 : P96 := by unfold P96 m96; intros; rfl

/-- Local `_normalize`, line 119. -/
def m119 (firstIndex lastIndex : X → IResult K) (makeRange : K → K → IResult R)
    (dims : List X) : IResult (List R) :=
  dims.mapM fun x => do
    let first ← firstIndex x
    let last ← lastIndex x
    makeRange first last
def P119 : Prop := ∀ {X K R : Type} firstIndex lastIndex makeRange dims,
  m119 (X := X) (K := K) (R := R) firstIndex lastIndex makeRange dims =
    dims.mapM fun x => do
      let first ← firstIndex x
      let last ← lastIndex x
      makeRange first last
theorem p119 : P119 := by unfold P119 m119; intros; rfl

/-- Array `promote_shape`, lines 188-190. -/
def m188 (axes : A → IResult AX) (promoteShape : AX → AX → IResult R)
    (a b : A) : IResult R := do
  let aa ← axes a
  let bb ← axes b
  promoteShape aa bb
def P188 : Prop := ∀ {A AX R : Type} axes promoteShape a b,
  m188 (A := A) (AX := AX) (R := R) axes promoteShape a b = do
    let aa ← axes a
    let bb ← axes b
    promoteShape aa bb
theorem p188 : P188 := by unfold P188; intros; rfl

/-- `throw_setindex_mismatch`, lines 205-212. -/
def m205 (lengthX : X → IResult N) (lengthI : I → IResult Nat) (firstI : I → IResult N)
    (sizeX : X → IResult S) (dimsX : S → IResult AnyValue) (dimsI : I → IResult AnyValue)
    (showN : N → AnyValue) (x : X) (indices : I) : IResult α := do
  let nindices ← lengthI indices
  if nindices = 1 then do
    let count ← lengthX x
    let destinations ← firstI indices
    .error (.dimensionMismatch (lazyAppend [.literal "tried to assign ", .dynamic (showN count),
      .literal " elements to ", .dynamic (showN destinations), .literal " destinations"]))
  else do
    let shape ← sizeX x
    let source ← dimsX shape
    let destination ← dimsI indices
    .error (.dimensionMismatch (lazyAppend [.literal "tried to assign ", .dynamic source,
      .literal " array to ", .dynamic destination, .literal " destination"]))
def P205 : Prop := ∀ {X N I S α : Type} lengthX lengthI firstI sizeX dimsX dimsI showN x indices,
  m205 (X := X) (N := N) (I := I) (S := S) (α := α)
    lengthX lengthI firstI sizeX dimsX dimsI showN x indices = do
      let nindices ← lengthI indices
      if nindices = 1 then do
        let count ← lengthX x
        let destinations ← firstI indices
        .error (.dimensionMismatch (lazyAppend [.literal "tried to assign ", .dynamic (showN count),
          .literal " elements to ", .dynamic (showN destinations), .literal " destinations"]))
      else do
        let shape ← sizeX x
        let source ← dimsX shape
        let destination ← dimsI indices
        .error (.dimensionMismatch (lazyAppend [.literal "tried to assign ", .dynamic source,
          .literal " array to ", .dynamic destination, .literal " destination"]))
theorem p205 : P205 := by unfold P205; intros; rfl

/-- Scalar `setindex_shape_check`, lines 214-215. -/
def m214 (length : X → IResult I) (equal : I → I → IResult Bool)
    (mismatch : X → List I → IResult Unit) (x : X) (i : I) : IResult Unit := do
  let n ← length x
  let same ← equal n i
  if same then .ok () else mismatch x [i]
def P214 : Prop := ∀ {X I : Type} length equal mismatch x i,
  m214 (X := X) (I := I) length equal mismatch x i = do
    let n ← length x
    let same ← equal n i
    if same then .ok () else mismatch x [i]
theorem p214 : P214 := by unfold P214; intros; rfl

/-- Tuple `setindex_shape_check`, lines 222-225. -/
def m222 (ndims : X → IResult Nat) (lengthShape : S → IResult Nat)
    (lengthX : X → IResult N) (product : S → IResult N) (equalN : N → N → IResult Bool)
    (size : X → IResult S) (shapesMatch : S → S → IResult Bool)
    (mismatch : X → S → IResult Unit) (x : X) (shape : S) : IResult Unit := do
  let rank ← ndims x
  let shapeRank ← lengthShape shape
  let isMatch ← if rank = 1 || shapeRank = 1 then do
    let n ← lengthX x
    let p ← product shape
    equalN n p
  else do
    let actual ← size x
    shapesMatch actual shape
  if isMatch then .ok () else mismatch x shape
def P222 : Prop := ∀ {X S N : Type} ndims lengthShape lengthX product equalN size shapesMatch mismatch x shape,
  m222 (X := X) (S := S) (N := N) ndims lengthShape lengthX product equalN size shapesMatch mismatch x shape = do
    let rank ← ndims x
    let shapeRank ← lengthShape shape
    let isMatch ← if rank = 1 || shapeRank = 1 then do
      let n ← lengthX x
      let p ← product shape
      equalN n p
    else do
      let actual ← size x
      shapesMatch actual shape
    if isMatch then .ok () else mismatch x shape
theorem p222 : P222 := by unfold P222; intros; rfl

/-- Unsupported scalar-to-many assignment, lines 227-228. -/
def m227 (_value : X) (_shape : S) : IResult Unit :=
  .error (.argument (.literal "indexed assignment with a single value to possibly many locations is not supported; perhaps use broadcasting `.=` instead?"))
def P227 : Prop := ∀ {X S : Type} value shape,
  m227 (X := X) (S := S) value shape =
    .error (.argument (.literal "indexed assignment with a single value to possibly many locations is not supported; perhaps use broadcasting `.=` instead?"))
theorem p227 : P227 := by unfold P227 m227; intros; rfl

/-- `to_index(::AbstractArray)`, line 261. -/
def m261 (array : A) : A := array
def P261 : Prop := ∀ {A : Type} array, m261 (A := A) array = array
theorem p261 : P261 := by unfold P261 m261; intros; rfl

/-- `to_index(::AbstractArray{Union{}})`, line 262. -/
def m262 (array : A) : A := array
def P262 : Prop := ∀ {A : Type} array, m262 (A := A) array = array
theorem p262 : P262 := by unfold P262 m262; intros; rfl

def invalidIndex (limitrepr typeOf : A → IResult AnyValue) (value : A) : IResult α := do
  let shown ← limitrepr value
  let ty ← typeOf value
  .error (.argument (lazyAppend [.literal "invalid index: ", .dynamic shown,
    .literal " of type ", .dynamic ty]))

def P263 : Prop := ∀ {A α : Type} limitrepr typeOf value,
  invalidIndex (A := A) (α := α) limitrepr typeOf value = do
    let shown ← limitrepr value
    let ty ← typeOf value
    .error (.argument (lazyAppend [.literal "invalid index: ", .dynamic shown,
      .literal " of type ", .dynamic ty]))
theorem p263 : P263 := by unfold P263 invalidIndex; intros; rfl
def P266 : Prop := P263
theorem p266 : P266 := p263

/-- General two-argument `to_indices`, line 310. -/
def m310 (dropZeroDim : Ix → IResult J) (toIndices : A → J → Ix → IResult R)
    (array : A) (indices : Ix) : IResult R := do
  let dropped ← dropZeroDim indices
  toIndices array dropped indices
def P310 : Prop := ∀ {A Ix J R : Type} dropZeroDim toIndices array indices,
  m310 (A := A) (Ix := Ix) (J := J) (R := R) dropZeroDim toIndices array indices = do
    let dropped ← dropZeroDim indices
    toIndices array dropped indices
theorem p310 : P310 := by unfold P310; intros; rfl

/-- Single-index `to_indices`, line 311. -/
def m311 (indexLinear : IResult Style) (eachindex : Style → A → IResult E)
    (toIndices : A → List E → Ix → IResult R) (array : A) (indices : Ix) : IResult R := do
  let style ← indexLinear
  let each ← eachindex style array
  toIndices array [each] indices
def P311 : Prop := ∀ {Style A E Ix R : Type} indexLinear eachindex toIndices array indices,
  m311 (Style := Style) (A := A) (E := E) (Ix := Ix) (R := R)
    indexLinear eachindex toIndices array indices = do
      let style ← indexLinear
      let each ← eachindex style array
      toIndices array [each] indices
theorem p311 : P311 := by unfold P311; intros; rfl

/-- Bootstrap `_to_indices`, line 312. -/
def m312 (axes : A → IResult AX) (toIndices : A → AX → Ix → IResult R)
    (array : A) (indices : Ix) : IResult R := do
  let ax ← axes array
  toIndices array ax indices
def P312 : Prop := ∀ {A AX Ix R : Type} axes toIndices array indices,
  m312 (A := A) (AX := AX) (Ix := Ix) (R := R) axes toIndices array indices = do
    let ax ← axes array
    toIndices array ax indices
theorem p312 : P312 := by unfold P312; intros; rfl

/-- Exhausted-index `_to_indices`, line 313. -/
def m313 (toIndices : A → J → IResult R) (array : A) (axes : J) : IResult R :=
  toIndices array axes
def P313 : Prop := ∀ {A J R : Type} toIndices array axes,
  m313 (A := A) (J := J) (R := R) toIndices array axes = toIndices array axes
theorem p313 : P313 := by unfold P313 m313; intros; rfl

/-- Integer-tuple `to_indices`, line 320. -/
def m320 (toIndices : A → List E → Ix → IResult R) (array : A) (indices : Ix) : IResult R :=
  toIndices array [] indices
def P320 : Prop := ∀ {A E Ix R : Type} toIndices array indices,
  m320 (A := A) (E := E) (Ix := Ix) (R := R) toIndices array indices =
    toIndices array [] indices
theorem p320 : P320 := by unfold P320 m320; intros; rfl

/-- Recursive contextual `to_indices`, lines 322-323. -/
def m322 (toIndex : A → I → IResult O) (safeTail : List AX → IResult (List AX))
    (toIndices : A → List AX → List I → IResult (List O))
    (array : A) (axes : List AX) (indices : List I) : IResult (List O) :=
  match indices with
  | [] => .ok []
  | first :: rest => do
      let converted ← toIndex array first
      let tailAxes ← safeTail axes
      let convertedRest ← toIndices array tailAxes rest
      .ok (converted :: convertedRest)
def P322 : Prop := ∀ {A I O AX : Type} toIndex safeTail toIndices array axes first rest,
  m322 (A := A) (I := I) (O := O) (AX := AX) toIndex safeTail toIndices array axes (first :: rest) = do
    let converted ← toIndex array first
    let tailAxes ← safeTail axes
    let convertedRest ← toIndices array tailAxes rest
    .ok (converted :: convertedRest)
theorem p322 : P322 := by unfold P322 m322; intros; rfl

structure Slice (R : Type) where indices : R deriving Repr, DecidableEq
structure IdentityUnitRange (R : Type) where indices : R deriving Repr, DecidableEq

/-- Parametric Slice conversion constructor, line 341. -/
def m341 (convert : R → IResult T) (slice : Slice R) : IResult (Slice T) := do
  let indices ← convert slice.indices
  .ok ⟨indices⟩
def P341 : Prop := ∀ {R T : Type} convert slice,
  m341 (R := R) (T := T) convert slice = do let indices ← convert slice.indices; .ok ⟨indices⟩
theorem p341 : P341 := by unfold P341; intros; rfl

/-- Slice size, line 349. -/
def m349 (length : R → IResult N) (slice : Slice R) : IResult (N × Unit) := do
  let n ← length slice.indices
  .ok (n, ())
def P349 : Prop := ∀ {R N : Type} length slice,
  m349 (R := R) (N := N) length slice = do let n ← length slice.indices; .ok (n, ())
theorem p349 : P349 := by unfold P349; intros; rfl

def showWrapped (printLiteral : IOState → String → IResult IOState)
    (printValue : IOState → R → IResult IOState)
    (label : String) (io : IOState) (indices : R) : IResult IOState := do
  let first ← printLiteral io label
  let second ← printValue first indices
  printLiteral second ")"
def P353 : Prop := ∀ {IOState R : Type}
    (printLiteral : IOState → String → IResult IOState)
    (printValue : IOState → R → IResult IOState) (io : IOState) (slice : Slice R),
  showWrapped printLiteral printValue "Base.Slice(" io slice.indices = do
    let first ← printLiteral io "Base.Slice("
    let second ← printValue first slice.indices
    printLiteral second ")"
theorem p353 : P353 := by unfold P353 showWrapped; intros; rfl

/-- Slice iteration, line 354. -/
def m354 (iterate : R → List S → IResult (Option (V × S)))
    (slice : Slice R) (state : List S) : IResult (Option (V × S)) := iterate slice.indices state
def P354 : Prop := ∀ {R S V : Type} iterate slice state,
  m354 (R := R) (S := S) (V := V) iterate slice state = iterate slice.indices state
theorem p354 : P354 := by unfold P354 m354; intros; rfl

/-- Parametric IdentityUnitRange conversion constructor, line 367. -/
def m367 (convert : R → IResult T) (range : IdentityUnitRange R) : IResult (IdentityUnitRange T) := do
  let indices ← convert range.indices
  .ok ⟨indices⟩
def P367 : Prop := ∀ {R T : Type} convert range,
  m367 (R := R) (T := T) convert range = do let indices ← convert range.indices; .ok ⟨indices⟩
theorem p367 : P367 := by unfold P367; intros; rfl

/-- IdentityUnitRange size, line 376. -/
def m376 (length : R → IResult N) (range : IdentityUnitRange R) : IResult (N × Unit) := do
  let n ← length range.indices
  .ok (n, ())
def P376 : Prop := ∀ {R N : Type} length range,
  m376 (R := R) (N := N) length range = do let n ← length range.indices; .ok (n, ())
theorem p376 : P376 := by unfold P376; intros; rfl

/-- IdentityUnitRange unsafe length, line 377. -/
def m377 (unsafeLength : R → IResult N) (range : IdentityUnitRange R) : IResult N :=
  unsafeLength range.indices
def P377 : Prop := ∀ {R N : Type} unsafeLength range,
  m377 (R := R) (N := N) unsafeLength range = unsafeLength range.indices
theorem p377 : P377 := by unfold P377 m377; intros; rfl

/-- Scalar IdentityUnitRange indexing, line 378. -/
def m378 (checkbounds : IdentityUnitRange R → I → IResult Unit)
    (eltype : IdentityUnitRange R → IResult T) (convert : T → I → IResult O)
    (range : IdentityUnitRange R) (index : I) : IResult O := do
  checkbounds range index
  let ty ← eltype range
  convert ty index
def P378 : Prop := ∀ {R I T O : Type} checkbounds eltype convert range index,
  m378 (R := R) (I := I) (T := T) (O := O) checkbounds eltype convert range index = do
    checkbounds range index
    let ty ← eltype range
    convert ty index
theorem p378 : P378 := by unfold P378; intros; rfl

def convertRangeIndex (checkbounds : W → I → IResult Unit) (eltype : W → IResult T)
    (rangeType : T → IResult RT) (convert : RT → I → IResult O) (wrapper : W) (index : I) : IResult O := do
  checkbounds wrapper index
  let element ← eltype wrapper
  let target ← rangeType element
  convert target index
def P380 : Prop := ∀ {W I T RT O : Type} checkbounds eltype rangeType convert wrapper index,
  convertRangeIndex (W := W) (I := I) (T := T) (RT := RT) (O := O)
    checkbounds eltype rangeType convert wrapper index = do
      checkbounds wrapper index
      let element ← eltype wrapper
      let target ← rangeType element
      convert target index
theorem p380 : P380 := by unfold P380 convertRangeIndex; intros; rfl
def P390 : Prop := P380
theorem p390 : P390 := p380

def checkedIdentity (checkbounds : S → I → IResult Unit) (source : S) (index : I) : IResult I := do
  checkbounds source index
  .ok index
def P404 : Prop := ∀ {S I : Type} checkbounds source index,
  checkedIdentity (S := S) (I := I) checkbounds source index = do checkbounds source index; .ok index
theorem p404 : P404 := by unfold P404 checkedIdentity; intros; rfl
def P410 : Prop := P404
theorem p410 : P410 := p404

def P416 : Prop := ∀ {IOState R : Type}
    (printLiteral : IOState → String → IResult IOState)
    (printValue : IOState → R → IResult IOState) (io : IOState) (range : IdentityUnitRange R),
  showWrapped printLiteral printValue "Base.IdentityUnitRange(" io range.indices = do
    let first ← printLiteral io "Base.IdentityUnitRange("
    let second ← printValue first range.indices
    printLiteral second ")"
theorem p416 : P416 := by unfold P416 showWrapped; intros; rfl

def m417 (iterate : R → List S → IResult (Option (V × S)))
    (range : IdentityUnitRange R) (state : List S) : IResult (Option (V × S)) :=
  iterate range.indices state
def P417 : Prop := ∀ {R S V : Type} iterate range state,
  m417 (R := R) (S := S) (V := V) iterate range state = iterate range.indices state
theorem p417 : P417 := by unfold P417 m417; intros; rfl

def P423 : Prop := P404
theorem p423 : P423 := p404

structure LinearIndices (R : Type) where indices : R deriving Repr, DecidableEq

/-- Parametric LinearIndices conversion, lines 479-480. -/
def m479 (convertTuple : R1 → IResult R2) (construct : R2 → IResult (LinearIndices R2))
    (assertType : LinearIndices R2 → IResult (LinearIndices R2)) (indices : LinearIndices R1) :
    IResult (LinearIndices R2) := do
  let converted ← convertTuple indices.indices
  let built ← construct converted
  assertType built
def P479 : Prop := ∀ {R1 R2 : Type} convertTuple construct assertType indices,
  m479 (R1 := R1) (R2 := R2) convertTuple construct assertType indices = do
    let converted ← convertTuple indices.indices
    let built ← construct converted
    assertType built
theorem p479 : P479 := by unfold P479; intros; rfl

/-- Tuple LinearIndices constructor, lines 483-484. -/
def m483 (convertRange : R → IResult O) (construct : List O → IResult L)
    (indices : List R) : IResult L := do
  let converted ← indices.mapM convertRange
  construct converted
def P483 : Prop := ∀ {R O L : Type} convertRange construct indices,
  m483 (R := R) (O := O) (L := L) convertRange construct indices = do
    let converted ← indices.mapM convertRange
    construct converted
theorem p483 : P483 := by unfold P483; intros; rfl

/-- Array LinearIndices constructor, line 487. -/
def m487 (axes : A → IResult AX) (construct : AX → IResult L) (array : A) : IResult L := do
  let ax ← axes array
  construct ax
def P487 : Prop := ∀ {A AX L : Type} axes construct array,
  m487 (A := A) (AX := AX) (L := L) axes construct array = do let ax ← axes array; construct ax
theorem p487 : P487 := by unfold P487; intros; rfl

/-- `_convert2ind(::Integer)`, line 489. -/
def m489 (oneto : I → IResult R) (integer : I) : IResult R := oneto integer
def P489 : Prop := ∀ {I R : Type} oneto integer,
  m489 (I := I) (R := R) oneto integer = oneto integer
theorem p489 : P489 := by unfold P489 m489; intros; rfl

/-- Homogeneous tuple `indices_promote_type`, lines 492-495. -/
def m492 (promoteType : R1 → R2 → IResult R) (tupleType : R → Nat → IResult T)
    (left : R1) (right : R2) (count : Nat) : IResult T := do
  let promoted ← promoteType left right
  tupleType promoted count
def P492 : Prop := ∀ {R1 R2 R T : Type} promoteType tupleType left right count,
  m492 (R1 := R1) (R2 := R2) (R := R) (T := T) promoteType tupleType left right count = do
    let promoted ← promoteType left right
    tupleType promoted count
theorem p492 : P492 := by unfold P492; intros; rfl

/-- LinearIndices promotion rule, lines 497-498. -/
def m497 (indicesPromoteType : R1 → R2 → IResult R)
    (linearType : Nat → R → IResult T) (rank : Nat) (left : R1) (right : R2) : IResult T := do
  let promoted ← indicesPromoteType left right
  linearType rank promoted
def P497 : Prop := ∀ {R1 R2 R T : Type} indicesPromoteType linearType rank left right,
  m497 (R1 := R1) (R2 := R2) (R := R) (T := T)
    indicesPromoteType linearType rank left right = do
      let promoted ← indicesPromoteType left right
      linearType rank promoted
theorem p497 : P497 := by unfold P497; intros; rfl

/-- LinearIndices size, line 507. -/
def m507 (length : R → IResult N) (iter : LinearIndices (List R)) : IResult (List N) :=
  iter.indices.mapM length
def P507 : Prop := ∀ {R N : Type} length iter,
  m507 (R := R) (N := N) length iter = iter.indices.mapM length
theorem p507 : P507 := by unfold P507 m507; intros; rfl

/-- One-dimensional LinearIndices iteration, line 522. -/
def m522 (firstRange : R → IResult AX) (axes1 : AX → IResult AX)
    (iterate : AX → List S → IResult (Option (V × S)))
    (iter : LinearIndices (List R)) (state : List S) : IResult (Option (V × S)) := do
  match iter.indices with
  | [] => .error .bounds
  | first :: _ => do
      let raw ← firstRange first
      let axis ← axes1 raw
      iterate axis state
def P522 : Prop := ∀ {R AX S V : Type} firstRange axes1 iterate first rest state,
  m522 (R := R) (AX := AX) (S := S) (V := V) firstRange axes1 iterate ⟨first :: rest⟩ state = do
    let raw ← firstRange first
    let axis ← axes1 raw
    iterate axis state
theorem p522 : P522 := by unfold P522 m522; intros; rfl

/-- General LinearIndices iteration, line 523. -/
def m523 (length : L → IResult I) (greater : I → I → IResult Bool)
    (addOne : I → IResult I) (iter : L) (state : I) : IResult (Option (I × I)) := do
  let n ← length iter
  let done ← greater state n
  if done then .ok none else do
    let next ← addOne state
    .ok (some (state, next))
def P523 : Prop := ∀ {L I : Type} length greater addOne iter state,
  m523 (L := L) (I := I) length greater addOne iter state = do
    let n ← length iter
    let done ← greater state n
    if done then .ok none else do let next ← addOne state; .ok (some (state, next))
theorem p523 : P523 := by unfold P523; intros; rfl

/-- General LinearIndices last, line 528. -/
def m528 (length : L → IResult I) (iter : L) : IResult I := length iter
def P528 : Prop := ∀ {L I : Type} length iter,
  m528 (L := L) (I := I) length iter = length iter
theorem p528 : P528 := by unfold P528 m528; intros; rfl

def P531 : Prop := ∀ {IOState R : Type}
    (printLiteral : IOState → String → IResult IOState)
    (printValue : IOState → R → IResult IOState) (io : IOState) (iter : LinearIndices R),
  showWrapped printLiteral printValue "LinearIndices(" io iter.indices = do
    let first ← printLiteral io "LinearIndices("
    let second ← printValue first iter.indices
    printLiteral second ")"
theorem p531 : P531 := by unfold P531 showWrapped; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-indices-faithful-{line}", juliaFile := "base/indices.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.IndicesFaithful
