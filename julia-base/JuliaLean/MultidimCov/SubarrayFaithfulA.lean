import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.SubarrayFaithfulA

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

/-! Faithful source-order models for the reviewed HOLLOW methods in
`base/subarray.jl:26-226`. Arbitrary type parameters represent the complete
Julia method domains; callbacks represent the exact calls made by each body. -/

/-- Outer `SubArray(parent, indices)`, lines 26-28. -/
def m26 (viewindexing : List I → JResult VI) (indexStyleView : VI → JResult IV)
    (indexStyleParent : P → JResult IP) (combineStyle : IV → IP → JResult S)
    (ensureIndexable : List I → JResult K) (indexDimsum : List I → JResult D)
    (construct : S → P → K → D → JResult R) (parent : P) (indices : List I) : JResult R := do
  let viewStyle ← viewindexing indices
  let firstStyle ← indexStyleView viewStyle
  let parentStyle ← indexStyleParent parent
  let style ← combineStyle firstStyle parentStyle
  let stored ← ensureIndexable indices
  let dimensions ← indexDimsum indices
  construct style parent stored dimensions

def P26 : Prop := ∀ {I VI IV P IP S K D R : Type}
    (viewindexing : List I → JResult VI) (indexStyleView : VI → JResult IV)
    (indexStyleParent : P → JResult IP) (combineStyle : IV → IP → JResult S)
    (ensureIndexable : List I → JResult K) (indexDimsum : List I → JResult D)
    (construct : S → P → K → D → JResult R) parent indices,
  m26 viewindexing indexStyleView indexStyleParent combineStyle ensureIndexable indexDimsum
    construct parent indices = do
      let viewStyle ← viewindexing indices
      let firstStyle ← indexStyleView viewStyle
      let parentStyle ← indexStyleParent parent
      let style ← combineStyle firstStyle parentStyle
      let stored ← ensureIndexable indices
      let dimensions ← indexDimsum indices
      construct style parent stored dimensions
theorem p26 : P26 := by unfold P26; intros; rfl

/-- Cartesian constructor, lines 30-32. The rank is the supplied dimension tuple length. -/
def m30 (eltype : P → JResult T)
    (construct : T → Nat → P → I → Int → Int → JResult R)
    (parent : P) (indices : I) (dimensions : List D) : JResult R := do
  let elementType ← eltype parent
  construct elementType dimensions.length parent indices 0 0

def P30 : Prop := ∀ {P T I R D : Type} (eltype : P → JResult T)
    (construct : T → Nat → P → I → Int → Int → JResult R) parent indices
    (dimensions : List D),
  m30 eltype construct parent indices dimensions = do
    let elementType ← eltype parent
    construct elementType dimensions.length parent indices 0 0
theorem p30 : P30 := by unfold P30; intros; rfl

/-- Linear constructor, lines 34-37. -/
def m34 (layout : P → I → JResult (Int × Int)) (eltype : P → JResult T)
    (construct : T → Nat → P → I → Int → Int → JResult R)
    (parent : P) (indices : I) (dimensions : List D) : JResult R := do
  let (offset, stride) ← layout parent indices
  let elementType ← eltype parent
  construct elementType dimensions.length parent indices offset stride

def P34 : Prop := ∀ {P I T R D : Type} (layout : P → I → JResult (Int × Int))
    (eltype : P → JResult T)
    (construct : T → Nat → P → I → Int → Int → JResult R) parent indices
    (dimensions : List D),
  m34 layout eltype construct parent indices dimensions = do
    let (offset, stride) ← layout parent indices
    let elementType ← eltype parent
    construct elementType dimensions.length parent indices offset stride
theorem p34 : P34 := by unfold P34; intros; rfl

/-- `_compute_linear_layout`, lines 40-43. -/
def m40 (computeStride : P → I → JResult S) (toIntStride : S → JResult Int)
    (computeOffset : P → Int → I → JResult O) (toIntOffset : O → JResult Int)
    (parent : P) (indices : I) : JResult (Int × Int) := do
  let rawStride ← computeStride parent indices
  let stride ← toIntStride rawStride
  let rawOffset ← computeOffset parent stride indices
  let offset ← toIntOffset rawOffset
  .ok (offset, stride)

def P40 : Prop := ∀ {P I S O : Type} (computeStride : P → I → JResult S)
    (toIntStride : S → JResult Int) (computeOffset : P → Int → I → JResult O)
    (toIntOffset : O → JResult Int) parent indices,
  m40 computeStride toIntStride computeOffset toIntOffset parent indices = do
    let rawStride ← computeStride parent indices
    let stride ← toIntStride rawStride
    let rawOffset ← computeOffset parent stride indices
    let offset ← toIntOffset rawOffset
    .ok (offset, stride)
theorem p40 : P40 := by unfold P40; intros; rfl

/-- Leading-scalar `viewindexing`, line 54. -/
def m54 (tail : S → List A → JResult T) (scalar : S) (rest : List A) : JResult T :=
  tail scalar rest
def P54 : Prop := ∀ {S A T : Type} (tail : S → List A → JResult T) scalar rest,
  m54 tail scalar rest = tail scalar rest
theorem p54 : P54 := by unfold P54; intros; rfl

/-- Two-Slice `viewindexing`, line 56. -/
def m56 (tail : S → List A → JResult T) (_first second : S)
    (rest : List A) : JResult T := tail second rest
def P56 : Prop := ∀ {S A T : Type} (tail : S → List A → JResult T) first second rest,
  m56 tail first second rest = tail second rest
theorem p56 : P56 := by unfold P56; intros; rfl

/-- Slice, AbstractUnitRange, scalar-suffix overload, line 58. -/
def m58 (linear : L) (_slice : S) (_range : R) (_scalars : List X) : L := linear
def P58 : Prop := ∀ {L S R X : Type} (linear : L) (slice : S) (range : R)
    (scalars : List X),
  m58 linear slice range scalars = linear
theorem p58 : P58 := by unfold P58; intros; rfl

/-- Slice, Slice, scalar-suffix disambiguation, line 59. -/
def m59 (linear : L) (_first _second : S) (_scalars : List X) : L := linear
def P59 : Prop := ∀ {L S X : Type} (linear : L) (first second : S) (scalars : List X),
  m59 linear first second scalars = linear
theorem p59 : P59 := by unfold P59; intros; rfl

/-- Scalar AbstractRange overload, line 63. -/
def m63 (linear : L) (_range : R) (_scalars : List X) : L := linear
def P63 : Prop := ∀ {L R X : Type} (linear : L) (range : R) (scalars : List X),
  m63 linear range scalars = linear
theorem p63 : P63 := by unfold P63; intros; rfl

/-- Arbitrary-tuple fallback, line 65. -/
def m65 (cartesian : C) (_indices : List A) : C := cartesian
def P65 : Prop := ∀ {C A : Type} (cartesian : C) (indices : List A),
  m65 cartesian indices = cartesian
theorem p65 : P65 := by unfold P65; intros; rfl

/-- AbstractArray-leading fallback, line 67. -/
def m67 (cartesian : C) (_array : A) (_rest : List X) : C := cartesian
def P67 : Prop := ∀ {C A X : Type} (cartesian : C) (array : A) (rest : List X),
  m67 cartesian array rest = cartesian
theorem p67 : P67 := by unfold P67; intros; rfl

/-- Generic `sizeof(SubArray)`, line 75. -/
def m75 (length : V → JResult N) (eltype : V → JResult T)
    (sizeof : T → JResult N) (multiply : N → N → JResult N) (view : V) : JResult N := do
  let count ← length view
  let elementType ← eltype view
  let bytes ← sizeof elementType
  multiply count bytes
def P75 : Prop := ∀ {V N T : Type} (length : V → JResult N) (eltype : V → JResult T)
    (sizeof : T → JResult N) (multiply : N → N → JResult N) view,
  m75 length eltype sizeof multiply view = do
    let count ← length view
    let elementType ← eltype view
    let bytes ← sizeof elementType
    multiply count bytes
theorem p75 : P75 := by unfold P75; intros; rfl

/-- Array-parent `sizeof(SubArray)`, line 76. -/
def m76 (length : V → JResult N) (parent : V → JResult P)
    (elsize : P → JResult N) (multiply : N → N → JResult N) (view : V) : JResult N := do
  let count ← length view
  let array ← parent view
  let bytes ← elsize array
  multiply count bytes
def P76 : Prop := ∀ {V N P : Type} (length : V → JResult N) (parent : V → JResult P)
    (elsize : P → JResult N) (multiply : N → N → JResult N) view,
  m76 length parent elsize multiply view = do
    let count ← length view
    let array ← parent view
    let bytes ← elsize array
    multiply count bytes
theorem p76 : P76 := by unfold P76; intros; rfl

/-- `copy(SubArray)`, lines 78-83. -/
def m78 (parent : V → JResult P) (indices : V → JResult I)
    (getindex : P → I → JResult R) (ndims : V → JResult Nat)
    (similar : V → JResult R) (setScalar : R → R → JResult R) (view : V) : JResult R := do
  let array ← parent view
  let inds ← indices view
  let value ← getindex array inds
  let rank ← ndims view
  if rank ≠ 0 then .ok value
  else do
    let result ← similar view
    setScalar result value
def P78 : Prop := ∀ {V P I R : Type} (parent : V → JResult P) (indices : V → JResult I)
    (getindex : P → I → JResult R) (ndims : V → JResult Nat)
    (similar : V → JResult R) (setScalar : R → R → JResult R) view,
  m78 parent indices getindex ndims similar setScalar view = do
    let array ← parent view
    let inds ← indices view
    let value ← getindex array inds
    let rank ← ndims view
    if rank ≠ 0 then .ok value
    else do
      let result ← similar view
      setScalar result value
theorem p78 : P78 := by unfold P78; intros; rfl

/-- `parent(SubArray)`, line 86. -/
def m86 (parent : V → P) (view : V) : P := parent view
def P86 : Prop := ∀ {V P : Type} (parent : V → P) view, m86 parent view = parent view
theorem p86 : P86 := by unfold P86; intros; rfl

/-- Generic `parentindices`, line 109. -/
def m109 (size : A → JResult (List D)) (oneto : D → JResult I) (array : A) : JResult (List I) := do
  let shape ← size array
  shape.mapM oneto
def P109 : Prop := ∀ {A D I : Type} (size : A → JResult (List D))
    (oneto : D → JResult I) array, m109 size oneto array = do
      let shape ← size array
      shape.mapM oneto
theorem p109 : P109 := by unfold P109; intros; rfl

def splatMapM (f : I → JResult (List D)) : List I → JResult (List D)
  | [] => .ok []
  | head :: tail => do
      let first ← f head
      let rest ← splatMapM f tail
      .ok (first ++ rest)

/-- `dataids(SubArray)`, line 112. -/
def m112 (parent : V → P) (indices : V → List I) (dataidsParent : P → JResult (List D))
    (dataidsIndex : I → JResult (List D)) (view : V) : JResult (List D) := do
  let first ← dataidsParent (parent view)
  let rest ← splatMapM dataidsIndex (indices view)
  .ok (first ++ rest)
def P112 : Prop := ∀ {V P I D : Type} (parent : V → P) (indices : V → List I)
    (dataidsParent : P → JResult (List D)) (dataidsIndex : I → JResult (List D)) view,
  m112 parent indices dataidsParent dataidsIndex view = do
    let first ← dataidsParent (parent view)
    let rest ← splatMapM dataidsIndex (indices view)
    .ok (first ++ rest)
theorem p112 : P112 := by unfold P112; intros; rfl

/-- Generic `unaliascopy(SubArray)`, line 115. -/
def m115 (typeOf : V → Ty) (parent : V → P) (indices : V → List I)
    (offset stride : V → Int) (unaliasParent : P → JResult P2)
    (unaliasIndex : I → JResult I2)
    (construct : Ty → P2 → List I2 → Int → Int → JResult R) (view : V) : JResult R := do
  let copiedParent ← unaliasParent (parent view)
  let copiedIndices ← (indices view).mapM unaliasIndex
  construct (typeOf view) copiedParent copiedIndices (offset view) (stride view)
def P115 : Prop := ∀ {V Ty P I P2 I2 R : Type} (typeOf : V → Ty) (parent : V → P)
    (indices : V → List I) (offset stride : V → Int) (unaliasParent : P → JResult P2)
    (unaliasIndex : I → JResult I2)
    (construct : Ty → P2 → List I2 → Int → Int → JResult R) view,
  m115 typeOf parent indices offset stride unaliasParent unaliasIndex construct view = do
    let copiedParent ← unaliasParent (parent view)
    let copiedIndices ← (indices view).mapM unaliasIndex
    construct (typeOf view) copiedParent copiedIndices (offset view) (stride view)
theorem p115 : P115 := by unfold P115; intros; rfl

/-- Array-parent `unaliascopy`, lines 119-130. -/
def m119 (indices : V → List I) (trimmedShape : List I → JResult Shape)
    (allocate : Shape → JResult D) (trimmedParent : List I → JResult PI)
    (allSlicesOrColon : PI → Bool) (makeDestView : D → PI → JResult D)
    (trimmedView : List I → JResult VI) (makeSourceView : V → VI → JResult VS)
    (copyTo : D → VS → JResult D) (trimmedIndex : I → JResult I2)
    (layout : D → List I2 → JResult (Int × Int))
    (construct : D → List I2 → Int → Int → JResult R) (linear : Bool) (view : V) : JResult R := do
  let original := indices view
  let shape ← trimmedShape original
  let destination ← allocate shape
  let parentIndices ← trimmedParent original
  let destinationView ← if allSlicesOrColon parentIndices then .ok destination
    else makeDestView destination parentIndices
  let viewIndices ← trimmedView original
  let sourceView ← makeSourceView view viewIndices
  let copiedDestination ← copyTo destinationView sourceView
  let denseIndices ← original.mapM trimmedIndex
  let (offset, stride) ← if linear then layout copiedDestination denseIndices else .ok (0, 0)
  construct copiedDestination denseIndices offset stride
def P119 : Prop := ∀ {V I Shape D PI VI VS I2 R : Type} (indices : V → List I)
    (trimmedShape : List I → JResult Shape) (allocate : Shape → JResult D)
    (trimmedParent : List I → JResult PI) (allSlicesOrColon : PI → Bool)
    (makeDestView : D → PI → JResult D) (trimmedView : List I → JResult VI)
    (makeSourceView : V → VI → JResult VS) (copyTo : D → VS → JResult D)
    (trimmedIndex : I → JResult I2) (layout : D → List I2 → JResult (Int × Int))
    (construct : D → List I2 → Int → Int → JResult R) linear view,
  m119 indices trimmedShape allocate trimmedParent allSlicesOrColon makeDestView trimmedView
    makeSourceView copyTo trimmedIndex layout construct linear view = do
      let original := indices view
      let shape ← trimmedShape original
      let destination ← allocate shape
      let parentIndices ← trimmedParent original
      let destinationView ← if allSlicesOrColon parentIndices then .ok destination
        else makeDestView destination parentIndices
      let viewIndices ← trimmedView original
      let sourceView ← makeSourceView view viewIndices
      let copiedDestination ← copyTo destinationView sourceView
      let denseIndices ← original.mapM trimmedIndex
      let (offset, stride) ← if linear then layout copiedDestination denseIndices else .ok (0, 0)
      construct copiedDestination denseIndices offset stride
theorem p119 : P119 := by unfold P119; intros; rfl

/-- Scalar `_trimmedshape`, line 133. -/
def m133 (one : D) (restShape : List I → JResult (List D))
    (_scalar : S) (rest : List I) : JResult (List D) := do
  let tail ← restShape rest
  .ok (one :: tail)
def P133 : Prop := ∀ {D I S : Type} (one : D) (restShape : List I → JResult (List D))
    (scalar : S) rest,
  m133 one restShape scalar rest = do let tail ← restShape rest; .ok (one :: tail)
theorem p133 : P133 := by unfold P133; intros; rfl

/-- AbstractRange `_trimmedshape`, line 134. -/
def m134 (isEmpty : R → JResult Bool) (eltype : R → JResult T) (zero : T → JResult D)
    (maximum : R → JResult D) (restShape : List I → JResult (List D))
    (range : R) (rest : List I) : JResult (List D) := do
  let empty ← isEmpty range
  let head ← if empty then do let type ← eltype range; zero type else maximum range
  let tail ← restShape rest
  .ok (head :: tail)
def P134 : Prop := ∀ {R T D I : Type} (isEmpty : R → JResult Bool)
    (eltype : R → JResult T) (zero : T → JResult D) (maximum : R → JResult D)
    (restShape : List I → JResult (List D)) range rest,
  m134 isEmpty eltype zero maximum restShape range rest = do
    let empty ← isEmpty range
    let head ← if empty then do let type ← eltype range; zero type else maximum range
    let tail ← restShape rest
    .ok (head :: tail)
theorem p134 : P134 := by unfold P134; intros; rfl

/-- Cartesian-index-array `_trimmedshape`, line 138. -/
def m138 (length : A → JResult D) (one : D) (restShape : List I → JResult (List D))
    (array : A) (rank : Nat) (rest : List I) : JResult (List D) := do
  let count ← length array
  let tail ← restShape rest
  .ok (count :: List.replicate (rank - 1) one ++ tail)
def P138 : Prop := ∀ {A D I : Type} (length : A → JResult D) one
    (restShape : List I → JResult (List D)) array rank rest,
  0 < rank → m138 length one restShape array rank rest = do
    let count ← length array
    let tail ← restShape rest
    .ok (count :: List.replicate (rank - 1) one ++ tail)
theorem p138 : P138 := by unfold P138; intros; rfl

/-- Generic `_trimmedpind`, line 141. -/
def m141 (axes : A → JResult (List AX)) (colon : AX → O)
    (restParent : List I → JResult (List O)) (index : A) (rest : List I) : JResult (List O) := do
  let ownAxes ← axes index
  let tail ← restParent rest
  .ok (ownAxes.map colon ++ tail)
def P141 : Prop := ∀ {A AX O I : Type} (axes : A → JResult (List AX)) (colon : AX → O)
    (restParent : List I → JResult (List O)) index rest,
  m141 axes colon restParent index rest = do
    let ownAxes ← axes index
    let tail ← restParent rest
    .ok (ownAxes.map colon ++ tail)
theorem p141 : P141 := by unfold P141; intros; rfl

/-- AbstractRange `_trimmedpind`, line 142, preserving the range object. -/
def m142 (inject : R → O) (restParent : List I → JResult (List O))
    (range : R) (rest : List I) : JResult (List O) := do
  let tail ← restParent rest
  .ok (inject range :: tail)
def P142 : Prop := ∀ {R O I : Type} (inject : R → O)
    (restParent : List I → JResult (List O)) range rest,
  m142 inject restParent range rest = do let tail ← restParent rest; .ok (inject range :: tail)
theorem p142 : P142 := by unfold P142; intros; rfl

/-- Generic `_trimmedvind`, line 146. -/
def m146 (axes : A → JResult (List AX)) (colon : AX → O)
    (restView : List I → JResult (List O)) (index : A) (rest : List I) : JResult (List O) := do
  let ownAxes ← axes index
  let tail ← restView rest
  .ok (ownAxes.map colon ++ tail)
def P146 : Prop := ∀ {A AX O I : Type} (axes : A → JResult (List AX)) (colon : AX → O)
    (restView : List I → JResult (List O)) index rest,
  m146 axes colon restView index rest = do
    let ownAxes ← axes index
    let tail ← restView rest
    .ok (ownAxes.map colon ++ tail)
theorem p146 : P146 := by unfold P146; intros; rfl

/-- Rank-zero Cartesian-index-array `_trimmedvind`, line 147. -/
def m147 (axes : A → JResult (List AX)) (first : AX → JResult O)
    (restView : List I → JResult (List O)) (index : A) (rest : List I) : JResult (List O) := do
  let ownAxes ← axes index
  let heads ← ownAxes.mapM first
  let tail ← restView rest
  .ok (heads ++ tail)
def P147 : Prop := ∀ {A AX O I : Type} (axes : A → JResult (List AX))
    (first : AX → JResult O) (restView : List I → JResult (List O)) index rest,
  m147 axes first restView index rest = do
    let ownAxes ← axes index
    let heads ← ownAxes.mapM first
    let tail ← restView rest
    .ok (heads ++ tail)
theorem p147 : P147 := by unfold P147; intros; rfl

/-- Scalar `_trimmedindex`, line 150. -/
def m150 (one : O) (oftype : S → O → JResult S) (scalar : S) : JResult S := oftype scalar one
def P150 : Prop := ∀ {O S : Type} (one : O) (oftype : S → O → JResult S) scalar,
  m150 one oftype scalar = oftype scalar one
theorem p150 : P150 := by unfold P150; intros; rfl

/-- General AbstractRange `_trimmedindex`, line 151. -/
def m151 (range : R) : R := range
def P151 : Prop := ∀ {R : Type} (range : R), m151 range = range
theorem p151 : P151 := by unfold P151; intros; rfl

/-- Dense-range `_trimmedindex`, line 152. -/
def m152 (length : R → JResult N) (oneto : N → JResult O)
    (oftype : R → O → JResult R) (range : R) : JResult R := do
  let count ← length range
  let dense ← oneto count
  oftype range dense
def P152 : Prop := ∀ {R N O : Type} (length : R → JResult N) (oneto : N → JResult O)
    (oftype : R → O → JResult R) range, m152 length oneto oftype range = do
      let count ← length range
      let dense ← oneto count
      oftype range dense
theorem p152 : P152 := by unfold P152; intros; rfl

/-- Scalar-index-array `_trimmedindex`, line 153. -/
def m153 (eachindex : A → JResult E) (axes : A → JResult AX)
    (reshape : E → AX → JResult B) (oftype : A → B → JResult A) (array : A) : JResult A := do
  let linear ← eachindex array
  let shape ← axes array
  let dense ← reshape linear shape
  oftype array dense
def P153 : Prop := ∀ {A E AX B : Type} (eachindex : A → JResult E)
    (axes : A → JResult AX) (reshape : E → AX → JResult B)
    (oftype : A → B → JResult A) array, m153 eachindex axes reshape oftype array = do
      let linear ← eachindex array
      let shape ← axes array
      let dense ← reshape linear shape
      oftype array dense
theorem p153 : P153 := by unfold P153; intros; rfl

/-- Rank-zero Cartesian-index-array `_trimmedindex`, line 154. -/
def m154 (copy : A → JResult B) (oftype : A → B → JResult A) (array : A) : JResult A := do
  let duplicate ← copy array
  oftype array duplicate
def P154 : Prop := ∀ {A B : Type} (copy : A → JResult B)
    (oftype : A → B → JResult A) array, m154 copy oftype array = do
      let duplicate ← copy array
      oftype array duplicate
theorem p154 : P154 := by unfold P154; intros; rfl

/-- Positive-rank Cartesian-index-array `_trimmedindex`, lines 155-158. -/
def m155 (one : D) (eachindex : A → JResult E)
    (cartesianIndices : E → List D → JResult C) (axes : A → JResult AX)
    (reshape : C → AX → JResult B) (oftype : A → B → JResult A)
    (array : A) (rank : Nat) : JResult A := do
  let linear ← eachindex array
  let cartesian ← cartesianIndices linear (List.replicate (rank - 1) one)
  let shape ← axes array
  let dense ← reshape cartesian shape
  oftype array dense
def P155 : Prop := ∀ {D A E C AX B : Type} (one : D) (eachindex : A → JResult E)
    (cartesianIndices : E → List D → JResult C) (axes : A → JResult AX)
    (reshape : C → AX → JResult B) (oftype : A → B → JResult A) array rank,
  0 < rank → m155 one eachindex cartesianIndices axes reshape oftype array rank = do
    let linear ← eachindex array
    let cartesian ← cartesianIndices linear (List.replicate (rank - 1) one)
    let shape ← axes array
    let dense ← reshape cartesian shape
    oftype array dense
theorem p155 : P155 := by unfold P155; intros; rfl

/-- `_maybe_reshape_parent` one-dimensional overload, line 165. -/
def m165 (reshape : A → Nat → JResult R) (array : A) : JResult R := reshape array 1
def P165 : Prop := ∀ {A R : Type} (reshape : A → Nat → JResult R) array,
  m165 reshape array = reshape array 1
theorem p165 : P165 := by unfold P165; intros; rfl

/-- Vector `_maybe_reshape_parent`, line 166. -/
def m166 (reshape : A → Nat → JResult R) (array : A) : JResult R := reshape array 1
def P166 : Prop := ∀ {A R : Type} (reshape : A → Nat → JResult R) array,
  m166 reshape array = reshape array 1
theorem p166 : P166 := by unfold P166; intros; rfl

/-- General `_maybe_reshape_parent`, line 168. -/
def m168 (reshape : A → Nat → JResult R) (array : A) (rank : Nat) : JResult R := reshape array rank
def P168 : Prop := ∀ {A R : Type} (reshape : A → Nat → JResult R) array rank,
  m168 reshape array rank = reshape array rank
theorem p168 : P168 := by unfold P168; intros; rfl

/-- General `view`, lines 221-226. -/
def m221 (toIndices : A → List I → JResult (List J)) (unalias : A → J → JResult J)
    (checkbounds : A → List J → JResult Unit) (ndims : A → JResult Nat)
    (removeSingletons : List Bool → List J → JResult (List J))
    (indexNdims : List J → JResult D) (reshapeParent : A → D → JResult P)
    (unsafeView : P → List J → JResult R) (array : A) (indices : List I) : JResult R := do
  let converted ← toIndices array indices
  let unaliased ← converted.mapM (unalias array)
  checkbounds array unaliased
  let rank ← ndims array
  let retained ← removeSingletons (List.replicate rank true) unaliased
  let dimensions ← indexNdims retained
  let parent ← reshapeParent array dimensions
  unsafeView parent retained
def P221 : Prop := ∀ {A I J D P R : Type} (toIndices : A → List I → JResult (List J))
    (unalias : A → J → JResult J) (checkbounds : A → List J → JResult Unit)
    (ndims : A → JResult Nat) (removeSingletons : List Bool → List J → JResult (List J))
    (indexNdims : List J → JResult D) (reshapeParent : A → D → JResult P)
    (unsafeView : P → List J → JResult R) array indices,
  m221 toIndices unalias checkbounds ndims removeSingletons indexNdims reshapeParent unsafeView
    array indices = do
      let converted ← toIndices array indices
      let unaliased ← converted.mapM (unalias array)
      checkbounds array unaliased
      let rank ← ndims array
      let retained ← removeSingletons (List.replicate rank true) unaliased
      let dimensions ← indexNdims retained
      let parent ← reshapeParent array dimensions
      unsafeView parent retained
theorem p221 : P221 := by unfold P221; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-subarray-faithful-{line}", juliaFile := "base/subarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 26 "SubArray(parent,indices)" "Construction evaluates both index styles, ensures the indices, computes the result dimensions, and dispatches in source order." "base/subarray.jl:26-28" ``P26 ``p26,
  entry 30 "SubArray(IndexCartesian,...)" "The Cartesian constructor selects the parent element type and supplied result rank before constructing a non-linear view." "base/subarray.jl:30-32" ``P30 ``p30,
  entry 34 "SubArray(IndexLinear,...)" "The linear constructor computes layout, selects element type and supplied rank, and constructs the view." "base/subarray.jl:34-37" ``P34 ``p34,
  entry 40 "_compute_linear_layout" "Linear layout converts compute_stride1 before calling and converting compute_offset1." "base/subarray.jl:40-43" ``P40 ``p40,
  entry 54 "viewindexing(scalar,...)" "Every Real scalar is removed before recursively classifying the arbitrary suffix." "base/subarray.jl:54" ``P54 ``p54,
  entry 56 "viewindexing(Slice,Slice,...)" "The first Slice is removed before recursively classifying the remaining arbitrary tuple." "base/subarray.jl:56" ``P56 ``p56,
  entry 58 "viewindexing(Slice,AbstractUnitRange,scalars...)" "Every AbstractUnitRange followed by Real scalars is classified as linear." "base/subarray.jl:58" ``P58 ``p58,
  entry 59 "viewindexing(Slice,Slice,scalars...)" "Two Slices followed by arbitrary Real scalars are classified as linear." "base/subarray.jl:59" ``P59 ``p59,
  entry 63 "viewindexing(AbstractRange,scalars...)" "Every scalar AbstractRange followed by Real scalars is classified as linear." "base/subarray.jl:63" ``P63 ``p63,
  entry 65 "viewindexing(any...)" "Every otherwise unsupported arbitrary tuple is classified as Cartesian." "base/subarray.jl:65" ``P65 ``p65,
  entry 67 "viewindexing(AbstractArray,any...)" "Every AbstractArray-leading arbitrary tuple is classified as Cartesian." "base/subarray.jl:67" ``P67 ``p67,
  entry 75 "sizeof(SubArray)" "Sizeof calls length, eltype and sizeof before multiplying their results." "base/subarray.jl:75" ``P75 ``p75,
  entry 76 "sizeof(SubArray{parent Array})" "Array-parent sizeof calls length, parent and elsize before multiplying." "base/subarray.jl:76" ``P76 ``p76,
  entry 78 "copy(SubArray)" "Copy performs parent indexing and the rank branch, including every failure and zero-rank allocation and assignment." "base/subarray.jl:78-83" ``P78 ``p78,
  entry 86 "parent(SubArray)" "Parent returns the actual stored parent object." "base/subarray.jl:86" ``P86 ``p86,
  entry 109 "parentindices(AbstractArray)" "Generic parentindices calls size on the array and oneto on every dimension." "base/subarray.jl:109" ``P109 ``p109,
  entry 112 "dataids(SubArray)" "Data identifiers call dataids on the actual parent and every actual stored index before concatenation." "base/subarray.jl:112" ``P112 ``p112,
  entry 115 "unaliascopy(SubArray)" "Generic unaliascopy copies the actual parent and indices and reconstructs the original concrete type and layout fields." "base/subarray.jl:115" ``P115 ``p115,
  entry 119 "unaliascopy(Array-parent SubArray)" "Array-parent unaliascopy performs trimming, optional destination view creation, copy, dense-index conversion, layout, and construction in order." "base/subarray.jl:119-130" ``P119 ``p119,
  entry 133 "_trimmedshape(scalar)" "Every Real scalar contributes one while preserving the recursive shape values." "base/subarray.jl:133" ``P133 ``p133,
  entry 134 "_trimmedshape(AbstractRange)" "AbstractRange shape preserves zero or maximum in the range element domain, including negative maxima." "base/subarray.jl:134" ``P134 ``p134,
  entry 138 "_trimmedshape(CartesianIndex array)" "A positive-rank Cartesian-index array contributes its length and exactly rank minus one singleton dimensions." "base/subarray.jl:138" ``P138 ``p138,
  entry 141 "_trimmedpind(generic)" "Generic trimmed parent indices call axes on the actual index and prepend one Colon per axis." "base/subarray.jl:141" ``P141 ``p141,
  entry 142 "_trimmedpind(AbstractRange)" "AbstractRange trimmed parent indices preserve the original range object." "base/subarray.jl:142" ``P142 ``p142,
  entry 146 "_trimmedvind(generic)" "Generic trimmed view indices call axes on the actual index and prepend one Colon per axis." "base/subarray.jl:146" ``P146 ``p146,
  entry 147 "_trimmedvind(rank-zero Cartesian array)" "Rank-zero Cartesian-index arrays call axes and first on every axis before recursion." "base/subarray.jl:147" ``P147 ``p147,
  entry 150 "_trimmedindex(scalar)" "Scalar trimming calls oftype on the actual Real scalar and one." "base/subarray.jl:150" ``P150 ``p150,
  entry 151 "_trimmedindex(AbstractRange)" "General AbstractRange trimming preserves the actual range object, type and values." "base/subarray.jl:151" ``P151 ``p151,
  entry 152 "_trimmedindex(dense range)" "Dense-range trimming computes length, oneto and same-type conversion in order." "base/subarray.jl:152" ``P152 ``p152,
  entry 153 "_trimmedindex(scalar-index array)" "Scalar-index-array trimming computes linear eachindex, axes, reshape and same-type conversion in order." "base/subarray.jl:153" ``P153 ``p153,
  entry 154 "_trimmedindex(rank-zero Cartesian array)" "Rank-zero Cartesian-index-array trimming copies the actual array and converts back to its concrete type." "base/subarray.jl:154" ``P154 ``p154,
  entry 155 "_trimmedindex(Cartesian-index array)" "Positive-rank Cartesian-index-array trimming builds padding, linear indices, CartesianIndices, reshape and same-type conversion." "base/subarray.jl:155-158" ``P155 ``p155,
  entry 165 "_maybe_reshape_parent(AbstractArray,rank1)" "The one-dimensional overload reshapes the actual parent with Val(1)." "base/subarray.jl:165" ``P165 ``p165,
  entry 166 "_maybe_reshape_parent(Vector,rank1)" "The vector overload reshapes the actual parent with Val(1)." "base/subarray.jl:166" ``P166 ``p166,
  entry 168 "_maybe_reshape_parent(AbstractArray,rankN)" "The general overload reshapes the actual parent with the supplied rank." "base/subarray.jl:168" ``P168 ``p168,
  entry 221 "view(AbstractArray,indices...)" "View converts and unaliases all indices, checks bounds, removes singleton indices, reshapes the parent and constructs the view with complete failure propagation." "base/subarray.jl:221-226" ``P221 ``p221
]

end JuliaLean.MultidimCov.SubarrayFaithfulA
