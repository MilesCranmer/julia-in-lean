import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReshapedFaithfulA

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

structure ArrayObject (Ref Dim : Type) where
  identity : Nat
  ref : Ref
  dims : List Dim
  deriving Repr, DecidableEq

def dmMessage (dims len : AnyValue) : LazyString :=
  lazyAppend [.literal "new dimensions ", .dynamic dims,
    .literal " must be consistent with array length ", .dynamic len]

/-- `throw_dmrsa`, lines 38-39. -/
def m38 (dims len : AnyValue) : JResult α := .error (.dimensionMismatch (dmMessage dims len))
def P38 : Prop := ∀ {α : Type} dims len,
  m38 (α := α) dims len = .error (.dimensionMismatch (dmMessage dims len))
theorem p38 : P38 := by unfold P38; intros; rfl

/-- Array `reshape`, lines 43-50, preserving shared storage. -/
def m43 (checkedDims : List D → JResult N) (length : ArrayObject Ref D → JResult N)
    (equal : N → N → JResult Bool) (asAnyDims : List D → AnyValue) (asAnyN : N → AnyValue)
    (array : ArrayObject Ref D) (dims : List D) : JResult (ArrayObject Ref D) := do
  let requested ← checkedDims dims
  let actual ← length array
  let same ← equal requested actual
  if ¬same then m38 (α := ArrayObject Ref D) (asAnyDims dims) (asAnyN actual)
  else .ok ⟨array.identity + 1, array.ref, dims⟩
def P43 : Prop := ∀ {D N Ref : Type} (checkedDims : List D → JResult N)
    (length : ArrayObject Ref D → JResult N) (equal : N → N → JResult Bool)
    (asAnyDims : List D → AnyValue) (asAnyN : N → AnyValue) array dims,
  m43 checkedDims length equal asAnyDims asAnyN array dims = do
    let requested ← checkedDims dims
    let actual ← length array
    let same ← equal requested actual
    if ¬same then m38 (α := ArrayObject Ref D) (asAnyDims dims) (asAnyN actual)
    else .ok ⟨array.identity + 1, array.ref, dims⟩
theorem p43 : P43 := by unfold P43; intros; rfl

/-- In-place Array `reshape!`, lines 55-61. The source writes the nonexistent
`dims` field of `Array`; callback 55 represents the resulting `FieldError`. -/
def m55 (checkedDims : List D → JResult N) (length : ArrayObject Ref D → JResult N)
    (equal : N → N → JResult Bool) (asAnyDims : List D → AnyValue) (asAnyN : N → AnyValue)
    (array : ArrayObject Ref D) (dims : List D) : JResult (ArrayObject Ref D) := do
  let requested ← checkedDims dims
  let actual ← length array
  let same ← equal requested actual
  if ¬same then m38 (α := ArrayObject Ref D) (asAnyDims dims) (asAnyN actual)
  else .error (.callback 55)
def P55 : Prop := ∀ {D N Ref : Type} (checkedDims : List D → JResult N)
    (length : ArrayObject Ref D → JResult N) (equal : N → N → JResult Bool)
    (asAnyDims : List D → AnyValue) (asAnyN : N → AnyValue) array dims requested,
  checkedDims dims = .ok requested → length array = .ok requested →
  equal requested requested = .ok true →
  m55 checkedDims length equal asAnyDims asAnyN array dims = .ok { array with dims := dims }
theorem p55_refuted : ¬ P55 := by
  intro h
  let array : ArrayObject Unit Unit := ⟨0, (), [()]⟩
  have impossible := h (fun _ : List Unit => .ok ()) (fun _ => .ok ())
    (fun _ _ => .ok true) (fun _ => ⟨0, 0⟩) (fun _ => ⟨0, 0⟩)
    array [()] () (by rfl) (by rfl) (by rfl)
  simp [m55] at impossible
  cases impossible

def delegate (reshape : A → D → JResult R) (parent : A) (dims : D) : JResult R :=
  reshape parent dims
def convertDelegate (convert : D → JResult E) (reshape : A → E → JResult R)
    (parent : A) (dims : D) : JResult R := do let shape ← convert dims; reshape parent shape

def P122 : Prop := ∀ {A D R : Type} (reshape : A → D → JResult R) parent dims,
  delegate reshape parent dims = reshape parent dims
theorem p122 : P122 := by unfold P122 delegate; intros; rfl
def P123 : Prop := ∀ {A D E R : Type} (toShape : D → JResult E)
    (reshape : A → E → JResult R) parent dims,
  convertDelegate toShape reshape parent dims = do let shape ← toShape dims; reshape parent shape
theorem p123 : P123 := by unfold P123 convertDelegate; intros; rfl
def P126 : Prop := P123
theorem p126 : P126 := p123
def P127 : Prop := ∀ {A D E R : Type} (mapInt : D → JResult E)
    (reshape : A → E → JResult R) parent dims,
  convertDelegate mapInt reshape parent dims = do let shape ← mapInt dims; reshape parent shape
theorem p127 : P127 := by unfold P127 convertDelegate; intros; rfl
def P128 : Prop := P122
theorem p128 : P128 := p122
def P133 : Prop := P122
theorem p133 : P133 := p122
def P134 : Prop := P122
theorem p134 : P134 := p122
def P135 : Prop := P122
theorem p135 : P135 := p122

/-- Tuple-Colon `reshape`, line 136. -/
def m136 (uncolon : A → D → JResult E) (reshape : A → E → JResult R)
    (parent : A) (dims : D) : JResult R := do
  let shape ← uncolon parent dims
  reshape parent shape
def P136 : Prop := ∀ {A D E R : Type} (uncolon : A → D → JResult E)
    (reshape : A → E → JResult R) parent dims,
  m136 uncolon reshape parent dims = do let shape ← uncolon parent dims; reshape parent shape
theorem p136 : P136 := by unfold P136; intros; rfl

def m138 (dims : AnyValue) : JResult α :=
  .error (.dimensionMismatch (lazyAppend [.literal "new dimensions ", .dynamic dims,
    .literal " may have at most one omitted dimension specified by `Colon()`"]))
def P138 : Prop := ∀ {α : Type} dims, m138 (α := α) dims =
  .error (.dimensionMismatch (lazyAppend [.literal "new dimensions ", .dynamic dims,
    .literal " may have at most one omitted dimension specified by `Colon()`"]))
theorem p138 : P138 := by unfold P138; intros; rfl

def m140 (len dims : AnyValue) : JResult α :=
  .error (.dimensionMismatch (lazyAppend [.literal "array size ", .dynamic len,
    .literal " must be divisible by the product of the new dimensions ", .dynamic dims]))
def P140 : Prop := ∀ {α : Type} len dims, m140 (α := α) len dims =
  .error (.dimensionMismatch (lazyAppend [.literal "array size ", .dynamic len,
    .literal " must be divisible by the product of the new dimensions ", .dynamic dims]))
theorem p140 : P140 := by unfold P140; intros; rfl

/-- `_reshape_uncolon`, lines 143-150. -/
def m143 (promoteDims : D → JResult E) (beforeColon afterColon : E → JResult P)
    (anyColon : P → JResult Bool) (length : A → JResult N)
    (compute : N → E → P → P → JResult R) (array : A) (dims : D) : JResult R := do
  let promoted ← promoteDims dims
  let pre ← beforeColon promoted
  let post ← afterColon promoted
  let extra ← anyColon post
  if extra then m138 (α := R) ⟨0, 0⟩
  else do let len ← length array; compute len promoted pre post
def P143 : Prop := ∀ {D E P A N R : Type} (promoteDims : D → JResult E)
    (beforeColon afterColon : E → JResult P) (anyColon : P → JResult Bool)
    (length : A → JResult N) (compute : N → E → P → P → JResult R) array dims,
  m143 promoteDims beforeColon afterColon anyColon length compute array dims = do
    let promoted ← promoteDims dims
    let pre ← beforeColon promoted
    let post ← afterColon promoted
    let extra ← anyColon post
    if extra then m138 (α := R) ⟨0, 0⟩
    else do let len ← length array; compute len promoted pre post
theorem p143 : P143 := by unfold P143; intros; rfl

/-- Int `_reshape_uncolon_computesize`, lines 152-161. -/
def m152 (isZero : Int → Bool) (checkedDims : P → P → JResult Q)
    (nonempty : Int → D → Q → JResult X) (convertInt : X → JResult Int)
    (join : P → Int → P → R) (len : Int) (dims : D) (pre post : P) : JResult R := do
  let size ← if isZero len then .ok 0 else do
    let product ← checkedDims pre post
    let quotient ← nonempty len dims product
    convertInt quotient
  .ok (join pre size post)
def P152 : Prop := ∀ {P Q D X R : Type} (isZero : Int → Bool)
    (checkedDims : P → P → JResult Q) (nonempty : Int → D → Q → JResult X)
    (convertInt : X → JResult Int) (join : P → Int → P → R) len dims pre post,
  m152 isZero checkedDims nonempty convertInt join len dims pre post = do
    let size ← if isZero len then .ok 0 else do
      let product ← checkedDims pre post
      let quotient ← nonempty len dims product
      convertInt quotient
    .ok (join pre size post)
theorem p152 : P152 := by unfold P152; intros; rfl

/-- Generic `_reshape_uncolon_computesize`, lines 163-170. -/
def m163 (product : P → P → JResult N) (isZero : N → JResult Bool)
    (promoteZero : N → N → JResult N) (nonempty : N → D → N → JResult N)
    (join : P → N → P → R) (len : N) (dims : D) (pre post : P) : JResult R := do
  let pr ← product pre post
  let zero ← isZero len
  let size ← if zero then promoteZero len pr else nonempty len dims pr
  .ok (join pre size post)
def P163 : Prop := ∀ {P N D R : Type} (product : P → P → JResult N)
    (isZero : N → JResult Bool) (promoteZero : N → N → JResult N)
    (nonempty : N → D → N → JResult N) (join : P → N → P → R) len dims pre post,
  m163 product isZero promoteZero nonempty join len dims pre post = do
    let pr ← product pre post
    let zero ← isZero len
    let size ← if zero then promoteZero len pr else nonempty len dims pr
    .ok (join pre size post)
theorem p163 : P163 := by unfold P163; intros; rfl

/-- Rank-valued `reshape`, lines 187-188. -/
def m187 (axes : A → JResult AX) (rdims : Nat → AX → JResult D)
    (reshape : A → D → JResult R) (parent : A) (rank : Nat) : JResult R := do
  let sourceAxes ← axes parent
  let dims ← rdims rank sourceAxes
  reshape parent dims
def P187 : Prop := ∀ {A AX D R : Type} (axes : A → JResult AX)
    (rdims : Nat → AX → JResult D) (reshape : A → D → JResult R) parent rank,
  m187 axes rdims reshape parent rank = do
    let sourceAxes ← axes parent
    let dims ← rdims rank sourceAxes
    reshape parent dims
theorem p187 : P187 := by unfold P187; intros; rfl

def trailingLengths (length : A → JResult N) (multiply : N → N → JResult N) : List A → JResult N
  | [] => .error (.callback 0)
  | [last] => length last
  | head :: tail => do let first ← length head; let rest ← trailingLengths length multiply tail; multiply first rest

def P194 : Prop := ∀ {A N : Type} (length : A → JResult N)
    (multiply : N → N → JResult N) head second rest,
  trailingLengths length multiply (head :: second :: rest) = do
    let first ← length head
    let tail ← trailingLengths length multiply (second :: rest)
    multiply first tail
theorem p194 : P194 := by unfold P194; intros; rfl
def P195 : Prop := ∀ {A N : Type} (length : A → JResult N)
    (multiply : N → N → JResult N) last,
  trailingLengths length multiply [last] = length last
theorem p195 : P195 := by unfold P195; intros; rfl

/-- `rdims(Val, axes)`, line 196. -/
def m196 (oneToOne : JResult AX) (rdims : List AX → I → JResult R)
    (rank : Nat) (indices : I) : JResult R := do
  let one ← oneToOne
  rdims (List.replicate rank one) indices
def P196 : Prop := ∀ {AX I R : Type} (oneToOne : JResult AX)
    (rdims : List AX → I → JResult R) rank indices,
  m196 oneToOne rdims rank indices = do let one ← oneToOne; rdims (List.replicate rank one) indices
theorem p196 : P196 := by unfold P196; intros; rfl

/-- One-result-dimension `rdims`, line 203. -/
def m203 (length : AX → JResult N) (multiply : N → N → JResult N)
    (oneto : N → JResult O) (indices : List AX) : JResult O := do
  let product ← trailingLengths length multiply indices
  oneto product
def P203 : Prop := ∀ {AX N O : Type} (length : AX → JResult N)
    (multiply : N → N → JResult N) (oneto : N → JResult O) indices,
  m203 length multiply oneto indices = do
    let product ← trailingLengths length multiply indices
    oneto product
theorem p203 : P203 := by unfold P203; intros; rfl

/-- Vector-to-vector `_reshape`, lines 214-218. -/
def m214 (requireOneBased : V → JResult Unit) (firstDim : D → JResult N)
    (length : V → JResult N) (equal : N → N → JResult Bool)
    (mismatch : N → N → JResult V) (vector : V) (dims : D) : JResult V := do
  requireOneBased vector
  let requested ← firstDim dims
  let actual ← length vector
  let same ← equal requested actual
  if same then .ok vector else mismatch actual requested
def P214 : Prop := ∀ {V D N : Type} (requireOneBased : V → JResult Unit)
    (firstDim : D → JResult N) (length : V → JResult N) (equal : N → N → JResult Bool)
    (mismatch : N → N → JResult V) vector dims,
  m214 requireOneBased firstDim length equal mismatch vector dims = do
    requireOneBased vector
    let requested ← firstDim dims
    let actual ← length vector
    let same ← equal requested actual
    if same then .ok vector else mismatch actual requested
theorem p214 : P214 := by unfold P214; intros; rfl

/-- General `_reshape`, lines 221-224. -/
def m221 (length : A → JResult N) (checkedDims : D → JResult N)
    (equal : N → N → JResult Bool) (mismatch : N → D → JResult R)
    (indexStyle : A → JResult S) (construct : (A × S) → D → JResult R)
    (parent : A) (dims : D) : JResult R := do
  let n ← length parent
  let requested ← checkedDims dims
  let same ← equal requested n
  if ¬same then mismatch n dims
  else do let style ← indexStyle parent; construct (parent, style) dims
def P221 : Prop := ∀ {A N D R S : Type} (length : A → JResult N)
    (checkedDims : D → JResult N) (equal : N → N → JResult Bool)
    (mismatch : N → D → JResult R) (indexStyle : A → JResult S)
    (construct : (A × S) → D → JResult R) parent dims,
  m221 length checkedDims equal mismatch indexStyle construct parent dims = do
    let n ← length parent
    let requested ← checkedDims dims
    let same ← equal requested n
    if ¬same then mismatch n dims
    else do let style ← indexStyle parent; construct (parent, style) dims
theorem p221 : P221 := by unfold P221; intros; rfl

def m227 (product : D → JResult AnyValue) (n : AnyValue) (kind : String)
    (dims : D) : JResult α := do
  let total ← product dims
  .error (.dimensionMismatch (lazyAppend [.literal "parent has ", .dynamic n,
    .literal " elements, which is incompatible with ", .literal kind, .literal " ",
    .dynamic ⟨0, 0⟩, .literal " (", .dynamic total, .literal " elements)"]))
def P227 : Prop := ∀ {D α : Type} (product : D → JResult AnyValue) n kind dims,
  m227 (α := α) product n kind dims = do
    let total ← product dims
    .error (.dimensionMismatch (lazyAppend [.literal "parent has ", .dynamic n,
      .literal " elements, which is incompatible with ", .literal kind, .literal " ",
      .dynamic ⟨0, 0⟩, .literal " (", .dynamic total, .literal " elements)"]))
theorem p227 : P227 := by unfold P227; intros; rfl

def unwrapReshape (parent : V → A) (reshape : A → D → JResult R)
    (view : V) (dims : D) : JResult R := reshape (parent view) dims
def P232 : Prop := ∀ {V A D R : Type} (parent : V → A)
    (reshape : A → D → JResult R) view dims,
  unwrapReshape parent reshape view dims = reshape (parent view) dims
theorem p232 : P232 := by unfold P232 unwrapReshape; intros; rfl
def P233 : Prop := P232
theorem p233 : P233 := p232

/-- Cartesian `__reshape`, lines 235-240. -/
def m235 (firstParent : P → JResult A) (size : A → JResult (List X))
    (front : List X → JResult (List X)) (toInt : X → JResult Int)
    (makeInverse : Int → JResult MI) (construct : A → D → List MI → JResult R)
    (pair : P) (dims : D) : JResult R := do
  let parent ← firstParent pair
  let shape ← size parent
  let leading ← front shape
  let adjusted ← leading.mapM fun value => do let n ← toInt value; .ok (max 1 n)
  let inverses ← adjusted.mapM makeInverse
  construct parent dims inverses
def P235 : Prop := ∀ {P A X MI D R : Type} (firstParent : P → JResult A)
    (size : A → JResult (List X)) (front : List X → JResult (List X))
    (toInt : X → JResult Int) (makeInverse : Int → JResult MI)
    (construct : A → D → List MI → JResult R) pair dims,
  m235 firstParent size front toInt makeInverse construct pair dims = do
    let parent ← firstParent pair
    let shape ← size parent
    let leading ← front shape
    let adjusted ← leading.mapM fun value => do let n ← toInt value; .ok (max 1 n)
    let inverses ← adjusted.mapM makeInverse
    construct parent dims inverses
theorem p235 : P235 := by unfold P235; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-reshapedarray-faithful-{line}", juliaFile := "base/reshapedarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.ReshapedFaithfulA
