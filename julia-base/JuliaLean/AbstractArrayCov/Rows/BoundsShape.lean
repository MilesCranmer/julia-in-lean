import JuliaLean.AbstractArrayCov.Rows.Iteration

/-! Method-specific models for `base/abstractarray.jl:682-896`. -/

namespace JuliaLean.AbstractArrayCov.Rows.BoundsShape

open JuliaLean
open JuliaLean.Registry
open JuliaLean.AbstractArrays
open JuliaLean.AbstractArrayCov.Rows.Basic

abbrev I64 := JInt .i64

def i64 (x : Int) : I64 := JInt.lit .i64 x

/-- `checkbounds(Bool,A,I...)`, lines 682-685. -/
def method682 (axes : α → β) (check : β → γ → Bool) (a : α) (indices : γ) : Bool :=
  check (axes a) indices
def Property682 : Prop := ∀ (α β γ : Type) (axes : α → β) (check : β → γ → Bool) a indices,
  method682 axes check a indices = check (axes a) indices
theorem property682 : Property682 := by unfold Property682; intros; rfl

/-- Single-index `checkbounds`, lines 690-693. -/
def method690 (eachindex : α → β) (checkindex : β → γ → Bool) (a : α) (index : γ) : Bool :=
  checkindex (eachindex a) index
def Property690 : Prop := ∀ (α β γ : Type) (eachindex : α → β)
    (checkindex : β → γ → Bool) a index,
  method690 eachindex checkindex a index = checkindex (eachindex a) index
theorem property690 : Property690 := by unfold Property690; intros; rfl

/-- Recursive nonempty `checkbounds_indices`, lines 722-726. -/
def method722 (default : α) (checkindex : α → β → Bool)
    (recurse : List α → List β → Bool) (inds : List α) (indices : β × List β) : Bool :=
  let firstOk := checkindex (inds.getD 0 default) indices.1
  firstOk && recurse inds.tail indices.2
def Property722 : Prop := ∀ (α β : Type) default (checkindex : α → β → Bool)
    (recurse : List α → List β → Bool) inds indices,
  method722 default checkindex recurse inds indices =
    let firstOk := checkindex (inds.getD 0 default) indices.1
    firstOk && recurse inds.tail indices.2
theorem property722 : Property722 := by unfold Property722; intros; rfl

/-- Empty-index `checkbounds_indices`, line 728. -/
def method728 (length : α → Nat) (inds : List α) : Bool := inds.all fun x => length x = 1
def Property728 : Prop := ∀ (α : Type) (length : α → Nat) inds,
  method728 length inds = inds.all fun x => length x = 1
theorem property728 : Property728 := by unfold Property728; intros; rfl

/-- Default `checkindex` error, line 750. -/
def method750 (typeofName : α → String) (index : α) : Jl Bool :=
  .error (.argumentError ("unable to check bounds for indices of type " ++ typeofName index))
def Property750 : Prop := ∀ (α : Type) (typeofName : α → String) index,
  method750 typeofName index =
    .error (.argumentError ("unable to check bounds for indices of type " ++ typeofName index))
theorem property750 : Property750 := by unfold Property750; intros; rfl

/-- Unit-range real `checkindex`, line 751. Both comparisons are evaluated. -/
def method751 (first last : α → β) (le : β → γ → Bool) (le' : γ → β → Bool)
    (inds : α) (index : γ) : Bool :=
  let lower := le (first inds) index
  let upper := le' index (last inds)
  lower && upper
def Property751 : Prop := ∀ (α β γ : Type) (first last : α → β)
    (le : β → γ → Bool) (le' : γ → β → Bool) inds index,
  method751 first last le le' inds index =
    let lower := le (first inds) index
    let upper := le' index (last inds)
    lower && upper
theorem property751 : Property751 := by unfold Property751; intros; rfl

/-- IdentityUnitRange `checkindex`, line 752. -/
def method752 (indices : α → β) (checkindex : β → γ → Bool) (inds : α) (index : γ) : Bool :=
  checkindex (indices inds) index
def Property752 : Prop := ∀ (α β γ : Type) (indices : α → β)
    (checkindex : β → γ → Bool) inds index,
  method752 indices checkindex inds index = checkindex (indices inds) index
theorem property752 : Property752 := by unfold Property752; intros; rfl

def unsignedValue (t : IntTy) (x : JInt t) : Int :=
  if t.signed ∧ x.val < 0 then x.val + 2 ^ t.bits else x.val

/-- OneTo same-BitInteger `checkindex`, line 753. -/
def method753 {t : IntTy} (last : α → JInt t) (inds : α) (index : JInt t) : Bool :=
  decide (unsignedValue t (index - JInt.lit t 1) < unsignedValue t (last inds))
def Property753 : Prop := ∀ (t : IntTy) (α : Type) (last : α → JInt t) inds index,
  method753 last inds index =
    decide (unsignedValue t (index - JInt.lit t 1) < unsignedValue t (last inds))
theorem property753 : Property753 := by unfold Property753; intros; rfl

/-- Colon `checkindex`, line 754. -/
def method754 : Bool := true
def Property754 : Prop := ∀ _axis : Unit, method754 = true
theorem property754 : Property754 := by unfold Property754; intros; rfl

/-- Slice `checkindex`, line 755. -/
def method755 : Bool := true
def Property755 : Prop := ∀ _axis : Unit, method755 = true
theorem property755 : Property755 := by unfold Property755; intros; rfl

/-- AbstractRange `checkindex`, lines 756-757. All bitwise operands are evaluated. -/
def method756 (isempty : α → Bool) (first last : α → β)
    (checkindex : γ → β → Bool) (inds : γ) (index : α) : Bool :=
  let empty := isempty index
  let firstOk := checkindex inds (first index)
  let lastOk := checkindex inds (last index)
  empty || (firstOk && lastOk)
def Property756 : Prop := ∀ (α β γ : Type) (isempty : α → Bool)
    (first last : α → β) (checkindex : γ → β → Bool) inds index,
  method756 isempty first last checkindex inds index =
    let empty := isempty index
    let firstOk := checkindex inds (first index)
    let lastOk := checkindex inds (last index)
    empty || (firstOk && lastOk)
theorem property756 : Property756 := by unfold Property756; intros; rfl

/-- LinearIndices `checkindex`, lines 759-760. -/
def method759 (isempty : α → Bool) (first last : α → β)
    (checkindex : γ → β → Bool) (inds : γ) (index : α) : Bool :=
  let empty := isempty index
  let firstOk := checkindex inds (first index)
  let lastOk := checkindex inds (last index)
  empty || (firstOk && lastOk)
def Property759 : Prop := ∀ (α β γ : Type) (isempty : α → Bool)
    (first last : α → β) (checkindex : γ → β → Bool) inds index,
  method759 isempty first last checkindex inds index =
    let empty := isempty index
    let firstOk := checkindex inds (first index)
    let lastOk := checkindex inds (last index)
    empty || (firstOk && lastOk)
theorem property759 : Property759 := by unfold Property759; intros; rfl

/-- Array-of-indices `checkindex`, lines 762-769. -/
def method762 (checkindex : α → β → Jl Bool) (inds : α) (indices : List β) : Jl Bool := do
  let mut b := true
  for i in indices do
    b := b && (← checkindex inds i)
  return b
def Property762 : Prop := ∀ (α β : Type) (checkindex : α → β → Jl Bool) inds indices,
  method762 checkindex inds indices = do
    let mut b := true
    for i in indices do b := b && (← checkindex inds i)
    return b
theorem property762 : Property762 := by unfold Property762; intros; rfl

/-- `similar(a::AbstractArray{T})`, line 819. -/
def method819 (similar : α → τ → β) (a : α) (elementType : τ) : β := similar a elementType
def Property819 : Prop := ∀ (α τ β : Type) (similar : α → τ → β) a t,
  method819 similar a t = similar a t
theorem property819 : Property819 := by unfold Property819; intros; rfl

/-- `similar(a, T)`, line 820. -/
def method820 (axes : α → γ) (similar : α → τ → γ → β) (a : α) (t : τ) : β :=
  similar a t (axes a)
def Property820 : Prop := ∀ (α γ τ β : Type) (axes : α → γ)
    (similar : α → τ → γ → β) a t,
  method820 axes similar a t = similar a t (axes a)
theorem property820 : Property820 := by unfold Property820; intros; rfl

/-- Tuple-dims `similar`, line 821. -/
def method821 (similar : α → τ → γ → β) (a : α) (t : τ) (dims : γ) : β :=
  similar a t dims
def Property821 : Prop := ∀ (α τ γ β : Type) (similar : α → τ → γ → β) a t dims,
  method821 similar a t dims = similar a t dims
theorem property821 : Property821 := by unfold Property821; intros; rfl

/-- Vararg-dims `similar(a,dims...)`, line 822. -/
def method822 (similar : α → τ → List γ → β) (a : α) (t : τ) (dims : List γ) : β :=
  similar a t dims
def Property822 : Prop := ∀ (α τ γ β : Type) (similar : α → τ → List γ → β) a t dims,
  method822 similar a t dims = similar a t dims
theorem property822 : Property822 := by unfold Property822; intros; rfl

/-- Vararg-dims `similar(a,T,dims...)`, line 823. -/
def method823 (similar : α → τ → List γ → β) (a : α) (t : τ) (dims : List γ) : β :=
  similar a t dims
def Property823 : Prop := ∀ (α τ γ β : Type) (similar : α → τ → List γ → β) a t dims,
  method823 similar a t dims = similar a t dims
theorem property823 : Property823 := by unfold Property823; intros; rfl

/-- Mixed Integer/AbstractOneTo dims `similar`, line 829. -/
def method829 (toShape : γ → δ) (similar : α → τ → δ → β)
    (a : α) (t : τ) (dims : γ) : β :=
  similar a t (toShape dims)
def Property829 : Prop := ∀ (α τ γ δ β : Type) (toShape : γ → δ)
    (similar : α → τ → δ → β) a t dims,
  method829 toShape similar a t dims = similar a t (toShape dims)
theorem property829 : Property829 := by unfold Property829; intros; rfl

/-- Legacy Integer/OneTo dims `similar`, line 832. -/
def method832 (toShape : γ → δ) (similar : α → τ → δ → β)
    (a : α) (t : τ) (dims : γ) : β :=
  similar a t (toShape dims)
def Property832 : Prop := ∀ (α τ γ δ β : Type) (toShape : γ → δ)
    (similar : α → τ → δ → β) a t dims,
  method832 toShape similar a t dims = similar a t (toShape dims)
theorem property832 : Property832 := by unfold Property832; intros; rfl

/-- Default Array allocation `similar`, line 834. -/
def method834 (array : τ → γ → β) (t : τ) (dims : γ) : β := array t dims
def Property834 : Prop := ∀ (τ γ β : Type) (array : τ → γ → β) t dims,
  method834 array t dims = array t dims
theorem property834 : Property834 := by unfold Property834; intros; rfl

/-- Empty tuple `to_shape`, line 836. -/
def method836 : List α := []
def Property836 : Prop := ∀ (α : Type), (method836 : List α) = []
theorem property836 : Property836 := by unfold Property836; intros; rfl

/-- Dims `to_shape`, line 837. -/
def method837 (dims : α) : α := dims
def Property837 : Prop := ∀ (α : Type) (dims : α), method837 dims = dims
theorem property837 : Property837 := by unfold Property837; intros; rfl

/-- DimsOrInds `to_shape`, line 838. -/
def method838 (toShape : α → β) (dims : List α) : List β := dims.map toShape
def Property838 : Prop := ∀ (α β : Type) (toShape : α → β) dims,
  method838 toShape dims = dims.map toShape
theorem property838 : Property838 := by unfold Property838; intros; rfl

/-- Int `to_shape`, line 840. -/
def method840 (i : I64) : I64 := i
def Property840 : Prop := ∀ i, method840 i = i
theorem property840 : Property840 := by unfold Property840; intros; rfl

/-- Integer `to_shape`, line 841. -/
def method841 (raw : Int) : Jl I64 := JInt.convert .i64 raw
def Property841 : Prop := ∀ raw, method841 raw = JInt.convert .i64 raw
theorem property841 : Property841 := by unfold Property841; intros; rfl

/-- AbstractOneTo `to_shape`, line 842. -/
def method842 (last : α → β) (toShapePrivate : β → γ) (range : α) : γ :=
  toShapePrivate (last range)
def Property842 : Prop := ∀ (α β γ : Type) (last : α → β)
    (toShapePrivate : β → γ) range,
  method842 last toShapePrivate range = toShapePrivate (last range)
theorem property842 : Property842 := by unfold Property842; intros; rfl

/-- Integer `_to_shape`, line 843. -/
def method843 (toShape : α → β) (x : α) : β := toShape x
def Property843 : Prop := ∀ (α β : Type) (toShape : α → β) x,
  method843 toShape x = toShape x
theorem property843 : Property843 := by unfold Property843; intros; rfl

/-- Fallback `_to_shape`, line 844. -/
def method844 (convertInt : α → Jl I64) (x : α) : Jl I64 := convertInt x
def Property844 : Prop := ∀ (α : Type) (convertInt : α → Jl I64) x,
  method844 convertInt x = convertInt x
theorem property844 : Property844 := by unfold Property844; intros; rfl

/-- AbstractUnitRange `to_shape`, line 845. -/
def method845 (range : α) : α := range
def Property845 : Prop := ∀ (α : Type) (range : α), method845 range = range
theorem property845 : Property845 := by unfold Property845; intros; rfl

/-- Storage-type vararg `similar`, line 869. -/
def method869 (similar : τ → List α → β) (t : τ) (dims : List α) : β := similar t dims
def Property869 : Prop := ∀ (τ α β : Type) (similar : τ → List α → β) t dims,
  method869 similar t dims = similar t dims
theorem property869 : Property869 := by unfold Property869; intros; rfl

/-- Storage-type mixed dims `similar`, line 870. -/
def method870 (toShape : α → β) (similar : τ → β → γ) (t : τ) (shape : α) : γ :=
  similar t (toShape shape)
def Property870 : Prop := ∀ (α β τ γ : Type) (toShape : α → β)
    (similar : τ → β → γ) t shape,
  method870 toShape similar t shape = similar t (toShape shape)
theorem property870 : Property870 := by unfold Property870; intros; rfl

/-- Storage-type legacy mixed dims `similar`, line 872. -/
def method872 (toShape : α → β) (similar : τ → β → γ) (t : τ) (shape : α) : γ :=
  similar t (toShape shape)
def Property872 : Prop := ∀ (α β τ γ : Type) (toShape : α → β)
    (similar : τ → β → γ) t shape,
  method872 toShape similar t shape = similar t (toShape shape)
theorem property872 : Property872 := by unfold Property872; intros; rfl

/-- Storage-type Dims allocation, line 873. -/
def method873 (construct : τ → α → β) (t : τ) (dims : α) : β := construct t dims
def Property873 : Prop := ∀ (τ α β : Type) (construct : τ → α → β) t dims,
  method873 construct t dims = construct t dims
theorem property873 : Property873 := by unfold Property873; intros; rfl

/-- `empty(v,U)`, line 892. -/
def method892 (similar : α → τ → Nat → β) (a : α) (t : τ) : β := similar a t 0
def Property892 : Prop := ∀ (α τ β : Type) (similar : α → τ → Nat → β) a t,
  method892 similar a t = similar a t 0
theorem property892 : Property892 := by unfold Property892; intros; rfl

/-- Vector `emptymutable`, line 895. -/
def method895 : List α := []
def Property895 : Prop := ∀ (α : Type), (method895 : List α) = []
theorem property895 : Property895 := by unfold Property895; intros; rfl

/-- Generic iterable `emptymutable`, line 896. -/
def method896 : List α := []
def Property896 : Prop := ∀ (α : Type), (method896 : List α) = []
theorem property896 : Property896 := by unfold Property896; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/abstractarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry "abstractarraycov-line682-checkbounds" "checkbounds(Bool,A,I...)" "The method calls axes before checkbounds_indices with the original index tuple." "base/abstractarray.jl:682-685" ``Property682 ``property682,
  entry "abstractarraycov-line690-checkbounds" "checkbounds(Bool,A,i)" "The single-index method constructs linear eachindex before calling checkindex." "base/abstractarray.jl:690-693" ``Property690 ``property690,
  entry "abstractarraycov-line722-checkbounds-indices" "checkbounds_indices(Bool,inds,I::nonempty)" "The recursion checks the first index against the first or singleton default axis and short-circuits before the tails." "base/abstractarray.jl:722-726" ``Property722 ``property722,
  entry "abstractarraycov-line728-checkbounds-indices" "checkbounds_indices(Bool,inds,())" "The empty requested-index case accepts exactly when every remaining axis has length one." "base/abstractarray.jl:728" ``Property728 ``property728,
  entry "abstractarraycov-line750-checkindex" "checkindex(Bool,inds,i)" "The fallback reports the runtime index type in ArgumentError." "base/abstractarray.jl:750" ``Property750 ``property750,
  entry "abstractarraycov-line751-checkindex" "checkindex(Bool,::AbstractUnitRange,::Real)" "The method evaluates both endpoint comparisons and combines them with bitwise and." "base/abstractarray.jl:751" ``Property751 ``property751,
  entry "abstractarraycov-line752-checkindex" "checkindex(Bool,::IdentityUnitRange,::Real)" "The method unwraps indices before delegating." "base/abstractarray.jl:752" ``Property752 ``property752,
  entry "abstractarraycov-line753-checkindex" "checkindex(Bool,::OneTo{T},::T)" "The optimized check wraps i-1 in T and compares the unsigned representations." "base/abstractarray.jl:753" ``Property753 ``property753,
  entry "abstractarraycov-line754-checkindex" "checkindex(Bool,::AbstractUnitRange,::Colon)" "Colon is always accepted." "base/abstractarray.jl:754" ``Property754 ``property754,
  entry "abstractarraycov-line755-checkindex" "checkindex(Bool,::AbstractUnitRange,::Slice)" "Slice is always accepted." "base/abstractarray.jl:755" ``Property755 ``property755,
  entry "abstractarraycov-line756-checkindex" "checkindex(Bool,::AbstractUnitRange,::AbstractRange)" "The method evaluates emptiness and both endpoint checks, then combines them with bitwise operators." "base/abstractarray.jl:756-757" ``Property756 ``property756,
  entry "abstractarraycov-line759-checkindex" "checkindex(Bool,::AbstractUnitRange,::LinearIndices)" "The method evaluates emptiness and both endpoint checks for LinearIndices." "base/abstractarray.jl:759-760" ``Property759 ``property759,
  entry "abstractarraycov-line762-checkindex" "checkindex(Bool,inds,::AbstractArray)" "The loop checks every supplied index in iteration order without short-circuiting false values." "base/abstractarray.jl:762-769" ``Property762 ``property762,
  entry "abstractarraycov-line819-similar" "similar(a::AbstractArray{T})" "The default forwards a and its element type." "base/abstractarray.jl:819" ``Property819 ``property819,
  entry "abstractarraycov-line820-similar" "similar(a::AbstractArray,::Type{T})" "The method obtains axes before forwarding a, T, and those axes." "base/abstractarray.jl:820" ``Property820 ``property820,
  entry "abstractarraycov-line821-similar" "similar(a::AbstractArray{T},dims::Tuple)" "The tuple overload forwards a, T, and dims." "base/abstractarray.jl:821" ``Property821 ``property821,
  entry "abstractarraycov-line822-similar" "similar(a::AbstractArray{T},dims...)" "The vararg overload packs and forwards dimensions with T." "base/abstractarray.jl:822" ``Property822 ``property822,
  entry "abstractarraycov-line823-similar" "similar(a::AbstractArray,::Type{T},dims...)" "The typed vararg overload packs and forwards dimensions." "base/abstractarray.jl:823" ``Property823 ``property823,
  entry "abstractarraycov-line829-similar" "similar(a,T,mixed-dims-tuple)" "The mixed-axis overload applies to_shape before forwarding." "base/abstractarray.jl:829" ``Property829 ``property829,
  entry "abstractarraycov-line832-similar" "similar(a,T,legacy-dims-tuple)" "The legacy mixed-axis overload applies to_shape before forwarding." "base/abstractarray.jl:832" ``Property832 ``property832,
  entry "abstractarraycov-line834-similar" "similar(a,T,dims::Dims{N})" "The fallback invokes the N-dimensional Array constructor with undef dimensions." "base/abstractarray.jl:834" ``Property834 ``property834,
  entry "abstractarraycov-line836-to-shape" "to_shape(())" "The empty shape remains empty." "base/abstractarray.jl:836" ``Property836 ``property836,
  entry "abstractarraycov-line837-to-shape" "to_shape(::Dims)" "A Dims tuple is returned unchanged." "base/abstractarray.jl:837" ``Property837 ``property837,
  entry "abstractarraycov-line838-to-shape" "to_shape(::DimsOrInds)" "The method maps scalar to_shape over dimensions in order." "base/abstractarray.jl:838" ``Property838 ``property838,
  entry "abstractarraycov-line840-to-shape" "to_shape(::Int)" "An Int dimension is returned unchanged." "base/abstractarray.jl:840" ``Property840 ``property840,
  entry "abstractarraycov-line841-to-shape" "to_shape(::Integer)" "A general Integer dimension is converted to Int." "base/abstractarray.jl:841" ``Property841 ``property841,
  entry "abstractarraycov-line842-to-shape" "to_shape(::AbstractOneTo)" "The method takes the range last value before private shape conversion." "base/abstractarray.jl:842" ``Property842 ``property842,
  entry "abstractarraycov-line843-private-to-shape" "_to_shape(::Integer)" "The integer private method delegates to public to_shape." "base/abstractarray.jl:843" ``Property843 ``property843,
  entry "abstractarraycov-line844-private-to-shape" "_to_shape(x)" "The fallback converts x to Int." "base/abstractarray.jl:844" ``Property844 ``property844,
  entry "abstractarraycov-line845-to-shape" "to_shape(::AbstractUnitRange)" "A general unit range is preserved as an axis." "base/abstractarray.jl:845" ``Property845 ``property845,
  entry "abstractarraycov-line869-similar" "similar(::Type{T},dims...)" "The storage-type vararg overload forwards the packed dimensions." "base/abstractarray.jl:869" ``Property869 ``property869,
  entry "abstractarraycov-line870-similar" "similar(::Type{T},mixed-shape)" "The storage-type mixed shape is converted before forwarding." "base/abstractarray.jl:870" ``Property870 ``property870,
  entry "abstractarraycov-line872-similar" "similar(::Type{T},legacy-shape)" "The storage-type legacy shape is converted before forwarding." "base/abstractarray.jl:872" ``Property872 ``property872,
  entry "abstractarraycov-line873-similar" "similar(::Type{T},dims::Dims)" "The Dims fallback invokes T(undef,dims)." "base/abstractarray.jl:873" ``Property873 ``property873,
  entry "abstractarraycov-line892-empty" "empty(::AbstractVector,U)" "empty calls similar with length zero." "base/abstractarray.jl:892" ``Property892 ``property892,
  entry "abstractarraycov-line895-emptymutable" "emptymutable(::AbstractVector,U)" "The vector method returns a new empty Vector{U}." "base/abstractarray.jl:895" ``Property895 ``property895,
  entry "abstractarraycov-line896-emptymutable" "emptymutable(itr,U)" "The generic iterable method returns a new empty Vector{U}." "base/abstractarray.jl:896" ``Property896 ``property896
]

end JuliaLean.AbstractArrayCov.Rows.BoundsShape
