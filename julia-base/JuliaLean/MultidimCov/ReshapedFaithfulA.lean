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

def entries : List Entry := [
  entry 38 "throw_dmrsa" "The helper constructs the complete LazyString DimensionMismatch and throws it." "base/reshapedarray.jl:38-39" ``P38 ``p38,
  entry 43 "reshape(Array,dims)" "Array reshape checks dimensions and length, returns a distinct Array object with the same storage reference and requested dimensions, and preserves all errors." "base/reshapedarray.jl:43-50" ``P43 ``p43,
  { id := "multidimcov-reshape-bang-field", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape!(Array,dims)"],
    statement := "In-place reshape should update the dimensions and return the same Array after the length check.",
    source := "base/reshapedarray.jl:53-61 and reshape documentation at lines 67-79",
    status := .refuted, prop := ``P55, thm := some ``p55_refuted,
    issue := "none found (queries: reshape! FieldError dims; reshape! Array no field dims; reshape! setfield size)",
    notes := "Counterexample: Base.reshape!([1,2,3,4], (4,)) throws FieldError(Vector{Int64}, :dims) on release and nightly." },
  entry 122 "reshape(parent,dims...)" "The vararg wrapper delegates with the actual parent and dimensions." "base/reshapedarray.jl:122" ``P122 ``p122,
  entry 123 "reshape(parent,shape)" "The shape wrapper converts the shape then reshapes the actual parent." "base/reshapedarray.jl:123" ``P123 ``p123,
  entry 126 "reshape(parent,OneTo shape)" "The legacy shape wrapper converts the shape then reshapes the actual parent." "base/reshapedarray.jl:126" ``P126 ``p126,
  entry 127 "reshape(parent,Integer tuple)" "The Integer-tuple wrapper maps Int conversion then reshapes the actual parent." "base/reshapedarray.jl:127" ``P127 ``p127,
  entry 128 "reshape(parent,Dims)" "The Dims wrapper delegates with the actual parent." "base/reshapedarray.jl:128" ``P128 ``p128,
  entry 133 "reshape(parent,Int...)" "The Int vararg wrapper retains the actual parent in its tuple delegation." "base/reshapedarray.jl:133" ``P133 ``p133,
  entry 134 "reshape(parent,Integer...)" "The Integer vararg wrapper retains the actual parent in its tuple delegation." "base/reshapedarray.jl:134" ``P134 ``p134,
  entry 135 "reshape(parent,Integer-or-Colon...)" "The mixed vararg wrapper retains the actual parent in its tuple delegation." "base/reshapedarray.jl:135" ``P135 ``p135,
  entry 136 "reshape(parent,Colon tuple)" "The Colon tuple wrapper passes the actual parent through both dimension inference and reshape." "base/reshapedarray.jl:136" ``P136 ``p136,
  entry 138 "throw1" "The helper constructs the complete LazyString DimensionMismatch for multiple omitted dimensions." "base/reshapedarray.jl:138-139" ``P138 ``p138,
  entry 140 "throw2" "The helper constructs and throws the complete divisibility DimensionMismatch." "base/reshapedarray.jl:140-141" ``P140 ``p140,
  entry 143 "_reshape_uncolon" "Dimension inference promotes the actual tuple, splits it around Colon, rejects another Colon, reads array length, and computes the shape in order." "base/reshapedarray.jl:143-150" ``P143 ``p143,
  entry 152 "_reshape_uncolon_computesize(Int)" "The Int specialization handles zero directly or calls checked_dims, the nonempty helper and convert(Int) before joining the shape." "base/reshapedarray.jl:152-161" ``P152 ``p152,
  entry 163 "_reshape_uncolon_computesize(generic)" "The generic method computes the product, promotes zero or calls the nonempty helper, and joins the inferred dimension." "base/reshapedarray.jl:163-170" ``P163 ``p163,
  entry 187 "reshape(parent,Val)" "Rank reshape obtains actual parent axes, computes rdims and reshapes the same parent." "base/reshapedarray.jl:187-188" ``P187 ``p187,
  entry 194 "rdims_trailing(many)" "Trailing dimension collapse calls length on every actual axis and multiplies recursively." "base/reshapedarray.jl:194" ``P194 ``p194,
  entry 195 "rdims_trailing(one)" "The terminal method calls length on the actual final axis." "base/reshapedarray.jl:195" ``P195 ``p195,
  entry 196 "rdims(Val,axes)" "The Val wrapper constructs exactly N OneTo(1) axes before rdims delegation." "base/reshapedarray.jl:196" ``P196 ``p196,
  entry 203 "rdims(one output,many inputs)" "The collapsing method calls length on every source axis, multiplies them, and constructs OneTo of the product." "base/reshapedarray.jl:203" ``P203 ``p203,
  entry 214 "_reshape(vector,Dims{1})" "Vector reshape requires one-based indexing, reads dims[1] and length, throws on mismatch, and returns the same vector." "base/reshapedarray.jl:214-218" ``P214 ``p214,
  entry 221 "_reshape(AbstractArray,Dims)" "General reshape reads parent length, checks dimensions, reads parent IndexStyle and constructs from the actual parent-style pair." "base/reshapedarray.jl:221-224" ``P221 ``p221,
  entry 227 "_throw_dmrs" "The mismatch helper evaluates prod(dims), constructs the full DimensionMismatch message and throws it." "base/reshapedarray.jl:227-228" ``P227 ``p227,
  entry 232 "_reshape(one-dimensional ReshapedArray)" "The specialization reads the actual stored parent before recursive reshape." "base/reshapedarray.jl:232" ``P232 ``p232,
  entry 233 "_reshape(ReshapedArray)" "The general specialization reads the actual stored parent before recursive reshape." "base/reshapedarray.jl:233" ``P233 ``p233,
  entry 235 "__reshape(Cartesian parent)" "Construction reads p[1], size and front, converts and clamps each leading size, constructs every multiplicative inverse, then builds the ReshapedArray." "base/reshapedarray.jl:235-240" ``P235 ``p235
]

end JuliaLean.MultidimCov.ReshapedFaithfulA
