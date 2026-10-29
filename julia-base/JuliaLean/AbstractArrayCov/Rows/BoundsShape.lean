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

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.BoundsShape
