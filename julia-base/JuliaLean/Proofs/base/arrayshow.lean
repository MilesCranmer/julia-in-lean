import JuliaLean.base.arrayshow
import JuliaLean.Registry.Types

namespace JuliaLean.ArrayDisplayState

@[simp] theorem runBind {E S A B : Type} (action : ExceptT E (StateM S) A)
    (next : A → ExceptT E (StateM S) B) (state : S) :
    ((action >>= next).run state) =
      match action.run state with
      | (.ok value, final) => (next value).run final
      | (.error error, final) => (.error error, final) := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runMap {E S A B : Type} (action : ExceptT E (StateM S) A)
    (f : A → B) (state : S) :
    ((f <$> action).run state) =
      match action.run state with
      | (.ok value, final) => (.ok (f value), final)
      | (.error error, final) => (.error error, final) := by
  simp only [Functor.map, ExceptT.map, Bind.bind, ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runCatch {E S A : Type} (action : ExceptT E (StateM S) A)
    (handler : E → ExceptT E (StateM S) A) (state : S) :
    (tryCatchThe E action handler).run state =
      match action.run state with
      | (.ok value, final) => (.ok value, final)
      | (.error error, final) => (handler error).run final := by
  simp only [tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind,
    ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runPure {E S A : Type} (value : A) (state : S) :
    ((pure value : ExceptT E (StateM S) A).run state) = (.ok value, state) := rfl

@[simp] theorem runThrow {E S A : Type} (error : E) (state : S) :
    ((throwThe E error : ExceptT E (StateM S) A).run state) = (.error error, state) := rfl

@[simp] theorem runGet {E S : Type} (state : S) :
    ((get : ExceptT E (StateM S) S).run state) = (.ok state, state) := rfl

@[simp] theorem byteToListLength (bytes : ByteArray) : bytes.toList.length = bytes.size := by
  have loop : ∀ (i : Nat) (r : List UInt8),
      (ByteArray.toList.loop bytes i r).length = bytes.size - i + r.length := by
    intro i r
    fun_induction ByteArray.toList.loop bytes i r with
    | case1 i r h ih => simp only [List.length_cons] at ih; omega
    | case2 i r h => simp only [List.length_reverse]; omega
  exact loop 0 []

end JuliaLean.ArrayDisplayState

namespace JuliaLean.Proofs.base.arrayshow
open JuliaLean.base.arrayshow JuliaLean.base.arrayshow.Model

def UnknownElementType : Prop :=
  ∀ (Ty : Type) (value : Ty),
    (typeinfoEltypeFallback value).isNone = true ∧
    (typeinfoEltypeBottom value).isNone = true

def ElementTypeDispatchErrors : Prop :=
  ∀ (World Ty Error : Type) (value : Ty)
    (eltype : Ty → ExceptT Error (StateM World) Ty)
    (initial final : World) (error : Error),
    (eltype value).run initial = (.error error, final) →
    (typeinfoEltypeArrayDispatch eltype value).run initial = (.error error, final) ∧
    (typeinfoEltypeDictDispatch eltype value).run initial = (.error error, final) ∧
    (typeinfoEltypeSetDispatch eltype value).run initial = (.error error, final)

def ElementTypeDispatchValues : Prop :=
  ∀ (World Ty Error : Type) (value result : Ty)
    (eltype : Ty → ExceptT Error (StateM World) Ty)
    (initial final : World),
    (eltype value).run initial = (.ok result, final) →
    (typeinfoEltypeArrayDispatch eltype value).run initial = (.ok (some result), final) ∧
    (typeinfoEltypeDictDispatch eltype value).run initial = (.ok (some result), final) ∧
    (typeinfoEltypeSetDispatch eltype value).run initial = (.ok (some result), final)

def NonemptyVectorRejected : Prop :=
  showNonemptyVector =
    .error (.errorException "_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented")

theorem unknownElementType : UnknownElementType := by
  intro Ty value
  exact ⟨rfl, rfl⟩

theorem elementTypeDispatchErrors : ElementTypeDispatchErrors := by
  intro World Ty Error value eltype initial final error h
  simp [typeinfoEltypeArrayDispatch, typeinfoEltypeDictDispatch, typeinfoEltypeSetDispatch, h]

theorem elementTypeDispatchValues : ElementTypeDispatchValues := by
  intro World Ty Error value result eltype initial final h
  simp [typeinfoEltypeArrayDispatch, typeinfoEltypeDictDispatch, typeinfoEltypeSetDispatch, h]

theorem nonemptyVectorRejected : NonemptyVectorRejected := rfl

end JuliaLean.Proofs.base.arrayshow

namespace JuliaLean.Proofs.base.arrayshow
open JuliaLean JuliaLean.base.arrayshow.Model JuliaLean.base.show

def EmptySummaryErrors : Prop :=
  ∀ (World Io V A R : Type) (summary : JIO Io V → A → ExceptT ShowError (StateM World) R)
    (io : JIO Io V) (array : A) (initial final : World) (error : ShowError),
    (summary io array).run initial = (.error error, final) →
    (showEmptyAbstractDispatch summary io array).run initial = (.error error, final)

def ZeroArrayAssignmentErrors : Prop :=
  ∀ (World Io V A X Ty R S : Type)
    (p : IOPrims (ExceptT ShowError (StateM World)) Io V)
    (isassigned : A → ExceptT ShowError (StateM World) Bool)
    (getindex : A → ExceptT ShowError (StateM World) X)
    (showElement : JIO Io V → X → ExceptT ShowError (StateM World) R)
    (printType : JIO Io V → Ty → ExceptT ShowError (StateM World) S)
    (io : JIO Io V) (array : A) (type : Ty) (initial final : World) (error : ShowError),
    (isassigned array).run initial = (.error error, final) →
    (printArrayZeroDispatch p isassigned getindex showElement io array).run initial =
      (.error error, final) ∧
    (showZeroArrayDispatch p isassigned getindex showElement printType io array type).run initial =
      (.error error, final)

def NonemptyMatrixAxesErrors : Prop :=
  ∀ (World Io V A Ax R : Type)
    (axes : A → ExceptT ShowError (StateM World) Ax)
    (impl : JIO Io V → A → String → Bool → Ax → ExceptT ShowError (StateM World) R)
    (io : JIO Io V) (array : A) (typePrefix : String) (initial final : World) (error : ShowError),
    (axes array).run initial = (.error error, final) →
    (showNonemptyMatrixDispatch axes impl io array typePrefix).run initial = (.error error, final)

def PrintArrayForwardingErrors : Prop :=
  ∀ (World Io V A R : Type) (render : JIO Io V → A → ExceptT ShowError (StateM World) R)
    (io : JIO Io V) (array : A) (initial final : World) (error : ShowError),
    (render io array).run initial = (.error error, final) →
    (printArrayVecOrMatDispatch render io array).run initial = (.error error, final) ∧
    (showNonemptyZeroDispatch render io array).run initial = (.error error, final)

def HigherArrayForwardingErrors : Prop :=
  ∀ (World Io V A Slice R S : Type)
    (showNd : JIO Io V → A →
      (JIO Io V → Slice → ExceptT ShowError (StateM World) S) → Bool →
      ExceptT ShowError (StateM World) R)
    (printMatrix : JIO Io V → Slice → ExceptT ShowError (StateM World) S)
    (io : JIO Io V) (array : A) (initial final : World) (error : ShowError),
    (showNd io array printMatrix true).run initial = (.error error, final) →
    (printArrayHigherDispatch showNd printMatrix io array).run initial = (.error error, final)

theorem emptySummaryErrors : EmptySummaryErrors := by
  intro World Io V A R summary io array initial final error h
  exact h

theorem zeroArrayAssignmentErrors : ZeroArrayAssignmentErrors := by
  intro World Io V A X Ty R S p isassigned getindex showElement printType io array type initial final error h
  simp [printArrayZeroDispatch, showZeroArrayDispatch, h]

theorem nonemptyMatrixAxesErrors : NonemptyMatrixAxesErrors := by
  intro World Io V A Ax R axes impl io array typePrefix initial final error h
  simp [showNonemptyMatrixDispatch, h]

theorem printArrayForwardingErrors : PrintArrayForwardingErrors := by
  intro World Io V A R render io array initial final error h
  exact ⟨h, h⟩

theorem higherArrayForwardingErrors : HigherArrayForwardingErrors := by
  intro World Io V A Slice R S showNd printMatrix io array initial final error h
  exact h

def PrintMatrixAxesErrors : Prop :=
  ∀ (World Io V A Ax Axis Text H W R : Type)
    (axes : A → JInt64 → ExceptT ShowError (StateM World) Ax)
    (unitrange : Ax → ExceptT ShowError (StateM World) Axis)
    (impl : JIO Io V → A → Text → Text → Text → Text → Text → Text →
      H → W → Axis → Axis → ExceptT ShowError (StateM World) R)
    (io : JIO Io V) (array : A) (pre sep post hdots vdots ddots : Text)
    (hmod : H) (vmod : W) (initial final : World) (error : ShowError),
    (axes array (i64 1)).run initial = (.error error, final) →
    (printMatrixDispatch axes unitrange impl io array pre sep post hdots vdots ddots hmod vmod).run initial =
      (.error error, final)

theorem printMatrixAxesErrors : PrintMatrixAxesErrors := by
  intro World Io V A Ax Axis Text H W R axes unitrange impl io array pre sep post hdots vdots ddots hmod vmod initial final error h
  simp [printMatrixDispatch, h]

end JuliaLean.Proofs.base.arrayshow

namespace JuliaLean.Proofs.base.arrayshow
open JuliaLean.Registry
def entries : List Entry := [
  { id := "arrayshow-unknown-element-type", juliaFile := "base/arrayshow.jl",
    juliaFns := ["typeinfo_eltype(typeinfo)", "typeinfo_eltype(::Type{Union{}})"],
    statement := "Unknown and bottom collection type information do not claim an element type.",
    source := "base/arrayshow.jl:570,571", status := .proven, prop := ``UnknownElementType, thm := some ``unknownElementType },
  { id := "arrayshow-element-type-dispatch-errors", juliaFile := "base/arrayshow.jl",
    juliaFns := ["typeinfo_eltype(::Type{<:AbstractArray})", "typeinfo_eltype(::Type{<:AbstractDict})", "typeinfo_eltype(::Type{<:AbstractSet})"],
    statement := "Element-type discovery preserves exceptions and all preceding effects of the selected eltype method.",
    source := "base/arrayshow.jl:573,574,575", status := .proven, prop := ``ElementTypeDispatchErrors, thm := some ``elementTypeDispatchErrors },
  { id := "arrayshow-element-type-dispatch-values", juliaFile := "base/arrayshow.jl",
    juliaFns := ["typeinfo_eltype(::Type{<:AbstractArray})", "typeinfo_eltype(::Type{<:AbstractDict})", "typeinfo_eltype(::Type{<:AbstractSet})"],
    statement := "Successful element-type discovery retains the exact returned type and preceding effects.",
    source := "base/arrayshow.jl:573,574,575", status := .proven, prop := ``ElementTypeDispatchValues, thm := some ``elementTypeDispatchValues },
  { id := "arrayshow-nonempty-vector-rejected", juliaFile := "base/arrayshow.jl",
    juliaFns := ["_show_nonempty(::IO, ::AbstractVector, ::String)"],
    statement := "The unsupported vector helper raises ErrorException with the complete documented diagnostic.",
    source := "base/arrayshow.jl:496", status := .proven, prop := ``NonemptyVectorRejected, thm := some ``nonemptyVectorRejected },
  { id := "arrayshow-empty-summary-errors", juliaFile := "base/arrayshow.jl",
    juliaFns := ["_show_empty(io, X::AbstractArray)"],
    statement := "Empty abstract-array rendering preserves exceptions and preceding effects of its summary method.",
    source := "base/arrayshow.jl:506", status := .proven, prop := ``EmptySummaryErrors, thm := some ``emptySummaryErrors },
  { id := "arrayshow-zero-array-assignment-errors", juliaFile := "base/arrayshow.jl",
    juliaFns := ["print_array(::IO, ::AbstractArray{<:Any,0})", "show_zero_dim(::IO, ::AbstractArray{T,0})"],
    statement := "Both zero-dimensional display paths preserve an exception and prior effects while checking whether their sole element is assigned.",
    source := "base/arrayshow.jl:366,526", status := .proven, prop := ``ZeroArrayAssignmentErrors, thm := some ``zeroArrayAssignmentErrors },
  { id := "arrayshow-nonempty-matrix-axes-errors", juliaFile := "base/arrayshow.jl",
    juliaFns := ["_show_nonempty(::IO, ::AbstractMatrix, ::String)"],
    statement := "Matrix rendering preserves exceptions and preceding effects while retrieving its axes.",
    source := "base/arrayshow.jl:438", status := .proven, prop := ``NonemptyMatrixAxesErrors, thm := some ``nonemptyMatrixAxesErrors },
  { id := "arrayshow-print-array-forwarding-errors", juliaFile := "base/arrayshow.jl",
    juliaFns := ["print_array(::IO, ::AbstractVecOrMat)", "_show_nonempty(::IO, ::AbstractArray{T,0}, ::String)"],
    statement := "Vector, matrix and zero-dimensional forwarding helpers preserve the selected renderer exception and preceding effects.",
    source := "base/arrayshow.jl:368,499", status := .proven, prop := ``PrintArrayForwardingErrors, thm := some ``printArrayForwardingErrors },
  { id := "arrayshow-higher-array-forwarding-errors", juliaFile := "base/arrayshow.jl",
    juliaFns := ["print_array(::IO, ::AbstractArray)"],
    statement := "Higher-dimensional rendering requests full display and preserves its renderer exception and preceding effects.",
    source := "base/arrayshow.jl:369", status := .proven, prop := ``HigherArrayForwardingErrors, thm := some ``higherArrayForwardingErrors },
  { id := "arrayshow-print-matrix-axes-errors", juliaFile := "base/arrayshow.jl",
    juliaFns := ["print_matrix(::IO, ::AbstractVecOrMat)"],
    statement := "A failure retrieving the row axis propagates with its preceding effects before column-axis lookup or rendering.",
    source := "base/arrayshow.jl:165", status := .proven, prop := ``PrintMatrixAxesErrors, thm := some ``printMatrixAxesErrors }
]
end JuliaLean.Proofs.base.arrayshow
