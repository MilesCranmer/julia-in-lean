import JuliaLean.base.refpointer
import JuliaLean.Registry.Types

/-!
# Properties of `base/refpointer.jl`

These propositions state the documented scalar, initialization, array-reference, and pointer
conversion contracts. Operations defined in other Julia files remain typed parameters with their
interface laws stated as hypotheses.
-/

namespace JuliaLean.Proofs.base.refpointer

open JuliaLean JuliaLean.base.refpointer JuliaLean.Registry

inductive UndefinedRefError where
  | undefRefError
  deriving DecidableEq

def RefScalarBehavior : Prop :=
  (∀ α : Type, refEltype (some α) = .element α) ∧
  refEltype none = .any ∧
  (∀ {R : Type} (r : R),
    refSize r = () ∧ refAxes r = () ∧ refLength r = int64 1 ∧
    refIsEmpty r = false ∧ refNdims r = int64 0 ∧ refNdimsType R = int64 0) ∧
  refIteratorSize = .hasShape0 ∧
  (∀ {R α E : Type} (get : R → Except E α) (r : R) (value : α),
    get r = .ok value → iterateRef get r = .ok (value, none)) ∧
  (∀ {R S α : Type} (r : R) (state : S), iterateRefState (α := α) r state = (none : Option (α × Option Unit)))

def RefValueConstructionBehavior : Prop :=
  (∀ {X R E : Type} (construct : X → Jl R) (get : R → Except E X),
    (∀ x reference, construct x = .ok reference → get reference = .ok x) →
    ∀ x reference, refAny construct x = .ok reference → get reference = .ok x) ∧
  (∀ {T X R Y E : Type} (construct : Type → X → Jl R)
      (convert : Type → X → Except E Y) (get : R → Except E Y),
    (∀ target x reference value, construct target x = .ok reference →
      convert target x = .ok value → get reference = .ok value) →
    ∀ x reference value, refTyped (T := T) construct x = .ok reference →
      convert T x = .ok value → get reference = .ok value) ∧
  (∀ {X R Y E : Type} (construct : X → Jl R) (convert : X → Except E Y)
      (get : R → Except E Y),
    (∀ x reference value, construct x = .ok reference →
      convert x = .ok value → get reference = .ok value) →
    ∀ x reference value, convertRefValue construct x = .ok reference →
      convert x = .ok value → get reference = .ok value) ∧
  (∀ {T R X : Type} (construct : Type → Jl R) (isBits : Type → Bool)
      (isAssigned : R → Bool) (get : R → Except UndefinedRefError X),
    (∀ target reference, construct target = .ok reference →
      isAssigned reference = isBits target) →
    (∀ target reference, construct target = .ok reference → isBits target = false →
      get reference = .error .undefRefError) →
    ∀ reference, refUndefined (T := T) construct = .ok reference →
      isAssigned reference = isBits T ∧
      (isBits T = false → get reference = .error .undefRefError)) ∧
  (∀ {R : Type} (reference : R), convertRefSame reference = reference)

def RefRefIndexBehavior : Prop :=
  ∀ {R I : Type} [DecidableEq I] (reference : R) (index one : I),
    (index = one → refRefIndex reference index one = .ok reference) ∧
    (index ≠ one →
      refRefIndex reference index one = .error (.errorException "Ref only has one element"))

def RefPointerIndexBehavior : Prop :=
  (∀ {T I S O : Type} (one : I) (subtract : I → I → I)
      (sizeOf : Type → S) (multiply : I → S → O)
      (toUInt : O → JuliaLean.base.pointer.U64)
      (indexValue : I → Int) (sizeValue : S → Int) (offsetValue : O → Int)
      (pointer : JuliaLean.base.pointer.Ptr T) (index : I),
    (∀ left right, indexValue (subtract left right) = indexValue left - indexValue right) →
    (∀ index size, offsetValue (multiply index size) = indexValue index * sizeValue size) →
    (∀ offset, (toUInt offset).val = wrapInt .u64 (offsetValue offset)) →
    (refPointerIndex one subtract sizeOf multiply toUInt pointer index).address.val =
      wrapInt .u64 (pointer.address.val +
        (indexValue index - indexValue one) * sizeValue (sizeOf T))) ∧
  RefRefIndexBehavior

def refArrayIndexValid {A : Type} (length : A → Nat) (array : A) (index : I64) : Prop :=
  1 ≤ index.val ∧ index.val ≤ (length array : Int)

def RefArrayIndexBehavior : Prop :=
  (∀ {T A R : Type} (length : A → Nat) (getindex : A → I64 → Jl T),
    (∀ array index, refArrayIndexValid length array index →
      ∃ value, getindex array index = .ok value) →
    (∀ array index, ¬ refArrayIndexValid length array index →
      getindex array index = .error .boundsError) →
    ∀ array index (roots : R),
      (¬ refArrayIndexValid length array index →
        getindexRefArray (R := R) getindex (makeRefArray (T := T) array index roots) = .error .boundsError) ∧
      (refArrayIndexValid length array index →
        ∃ value, getindexRefArray (R := R) getindex (makeRefArray (T := T) array index roots) = .ok value)) ∧
  (∀ {T A R : Type} (setindex : A → I64 → T → Jl A)
      (array : A) (index : I64) (roots : R) (value : T) (updated : A),
    setindex array index value = .ok updated →
    ∃ reference, setindexRefArray setindex (makeRefArray (T := T) array index roots) value =
      .ok reference ∧ reference.x = updated ∧ reference.index = index ∧ reference.roots = roots) ∧
  (∀ {T A : Type} (getindex : A → I64 → Jl T) (array : A),
    getindexRefArray (R := Unit) getindex (convertArrayToRef (T := T) array) = getindex array (int64 1)) ∧
  (∀ {T A I : Type} (toInt : I → Jl I64) (array : A) (index : I) (converted : I64),
    toInt index = .ok converted →
    refAbstractArray (T := T) toInt array index = .ok (makeRefArray (T := T) array converted ())) ∧
  (∀ {T A R : Type} (array : A) (index : I64) (roots : R),
    refArrayIntAnyRoots (T := T) array index roots = makeRefArray (T := T) array index roots) ∧
  (∀ {T A : Type} (array : A) (index : Option I64),
    refArrayIntNothingRoots array index =
      makeRefArray (T := T) array (index.getD (int64 1)) ()) ∧
  (∀ {T A R I : Type} (toInt : I → Jl I64) (array : A) (index : I) (roots : R)
      (converted : I64),
    toInt index = .ok converted →
    refArrayIntegerAnyRoots (T := T) toInt array index roots = .ok (makeRefArray (T := T) array converted roots)) ∧
  (∀ {T A I : Type} (toInt : I → Jl I64) (array : A) (index : I) (converted : I64),
    toInt index = .ok converted →
    refArrayIntegerNothingRoots (T := T) toInt array index = .ok (makeRefArray (T := T) array converted ()))

def RefDataPointerBehavior : Prop :=
  (∀ {R P : Type} (unsafeConvert : R → Jl P) (pointsToData : P → R → Prop),
    (∀ reference pointer, unsafeConvert reference = .ok pointer →
      pointsToData pointer reference) →
    ∀ reference pointer,
      unsafeConvertRefSame unsafeConvert reference = .ok pointer →
      pointsToData pointer reference) ∧
  (∀ {X P : Type} (unsafeConvert : X → Jl P) (pointsToData : P → X → Prop),
    (∀ value pointer, unsafeConvert value = .ok pointer → pointsToData pointer value) →
    ∀ value pointer,
      unsafeConvertRefAny unsafeConvert value = .ok pointer → pointsToData pointer value)

def RefArrayPointerRouteBehavior : Prop :=
  (∀ {T A R P Q V : Type} (allocatedinline isConcrete isMutable : Type → Bool)
      (pointer : A → I64 → Jl P) (getindex : A → I64 → Jl V)
      (pointerFromObjRef : V → P) (toPtrPtrCvoid : P → Q)
      (pointerref : Q → I64 → I64 → Jl P) (sizePtrCvoid : I64)
      (reference : RefArray T A R),
    (allocatedinline T = true →
      unsafeConvertRefArray allocatedinline isConcrete isMutable pointer getindex
        pointerFromObjRef toPtrPtrCvoid pointerref sizePtrCvoid reference =
        pointer reference.x reference.index) ∧
    (allocatedinline T = false → isConcrete T = true → isMutable T = true →
      unsafeConvertRefArray allocatedinline isConcrete isMutable pointer getindex
        pointerFromObjRef toPtrPtrCvoid pointerref sizePtrCvoid reference = do
          let value ← getindex reference.x reference.index
          pure (pointerFromObjRef value)) ∧
    (allocatedinline T = false → (isConcrete T && isMutable T) = false →
      unsafeConvertRefArray allocatedinline isConcrete isMutable pointer getindex
        pointerFromObjRef toPtrPtrCvoid pointerref sizePtrCvoid reference = do
          let pointerValue ← pointer reference.x reference.index
          pointerref (toPtrPtrCvoid pointerValue) (int64 1) sizePtrCvoid)) ∧
  (∀ {A R P : Type} (pointer : A → I64 → Jl P)
      (reference : RefArray AnyElement A R),
    unsafeConvertRefArrayAny pointer reference = pointer reference.x reference.index)

def PointerRootPairs {T P Root Q : Type}
    (cconvert : T → Jl Root) (unsafeConvert : Root → Jl Q)
    (assertPointer : Q → Jl P) : List T → List Root → List P → Prop
  | [], [], [] => True
  | value :: values, root :: roots, pointer :: pointers =>
      cconvert value = .ok root ∧
      (∃ converted, unsafeConvert root = .ok converted ∧
        assertPointer converted = .ok pointer) ∧
      PointerRootPairs cconvert unsafeConvert assertPointer values roots pointers
  | _, _, _ => False

def RefPointerArrayBehavior : Prop :=
  (∀ {T P Existing Root Q : Type} (tests : PointerArrayTypeTests)
      (arrayRef : List T → Existing) (cconvert : T → Jl Root)
      (unsafeConvert : Root → Jl Q) (assertPointer : Q → Jl P)
      (null : P) (array : List T),
    (tests.sameElementType = true →
      refPointerArray tests arrayRef cconvert unsafeConvert assertPointer null array =
        .ok (.existing (arrayRef array)) ∧
      cconvertPtrArray tests arrayRef cconvert unsafeConvert assertPointer null array =
        .ok (.existing (arrayRef array)) ∧
      cconvertRefPointerArray tests arrayRef cconvert unsafeConvert assertPointer null array =
        .ok (.existing (arrayRef array))) ∧
    (tests.sameElementType = false →
      (if tests.isBitsElement then tests.pointerOrCStringLayout else
        tests.elementSubtypeOfPointer) = true →
      ∃ reference1 reference2 reference3,
        refPointerArray tests arrayRef cconvert unsafeConvert assertPointer null array =
          .ok (.direct reference1) ∧
        cconvertPtrArray tests arrayRef cconvert unsafeConvert assertPointer null array =
          .ok (.direct reference2) ∧
        cconvertRefPointerArray tests arrayRef cconvert unsafeConvert assertPointer null array =
          .ok (.direct reference3) ∧
        reference1.x = array ∧ reference2.x = array ∧ reference3.x = array ∧
        reference1.index.val = 1 ∧ reference2.index.val = 1 ∧ reference3.index.val = 1 ∧
        reference1.roots = () ∧ reference2.roots = () ∧ reference3.roots = ()) ∧
    (tests.sameElementType = false →
      (if tests.isBitsElement then tests.pointerOrCStringLayout else
        tests.elementSubtypeOfPointer) = false →
      ∃ pointers roots reference1 reference2 reference3,
        PointerRootPairs cconvert unsafeConvert assertPointer array roots pointers ∧
        refPointerArray tests arrayRef cconvert unsafeConvert assertPointer null array =
          .ok (.converted reference1) ∧
        cconvertPtrArray tests arrayRef cconvert unsafeConvert assertPointer null array =
          .ok (.converted reference2) ∧
        cconvertRefPointerArray tests arrayRef cconvert unsafeConvert assertPointer null array =
          .ok (.converted reference3) ∧
        reference1.x = pointers ++ [null] ∧ reference2.x = pointers ++ [null] ∧
        reference3.x = pointers ++ [null] ∧
        reference1.roots = roots ∧ reference2.roots = roots ∧ reference3.roots = roots ∧
        reference1.index.val = 1 ∧ reference2.index.val = 1 ∧ reference3.index.val = 1 ∧
        roots.length = array.length)) ∧
  (∀ {A R : Type} (getArrayRef : A → R) (array : A),
    cconvertPtrArrayExisting getArrayRef array = getArrayRef array ∧
    cconvertRefArrayExisting getArrayRef array = getArrayRef array)

def RefTupleBehavior : Prop :=
  (∀ {T R E : Type} {N : Nat} (construct : Vector T N → Jl R)
      (get : R → Except E (Vector T N)) (tuple : Vector T N),
    (∀ values reference, construct values = .ok reference →
      get reference = .ok values) →
    ∀ reference, cconvertTupleRef construct tuple = .ok reference →
      get reference = .ok tuple) ∧
  (∀ {R : Type} (reference : R), cconvertTupleRefIdentity reference = reference) ∧
  (∀ {R TuplePointer RefPointer ElementPointer : Type}
      (unsafeConvert : R → Jl TuplePointer)
      (convertRef : TuplePointer → Jl RefPointer)
      (convertElement : TuplePointer → Jl ElementPointer)
      (tupleAddress : TuplePointer → Int) (refAddress : RefPointer → Int)
      (elementAddress : ElementPointer → Int) (reference : R)
      (tuplePointer : TuplePointer) (refPointer : RefPointer) (elementPointer : ElementPointer),
    (∀ pointer converted, convertRef pointer = .ok converted →
      refAddress converted = tupleAddress pointer) →
    (∀ pointer converted, convertElement pointer = .ok converted →
      elementAddress converted = tupleAddress pointer) →
    (unsafeConvert reference = .ok tuplePointer →
      convertRef tuplePointer = .ok refPointer →
      unsafeConvertRefTuple unsafeConvert convertRef reference = .ok refPointer ∧
      refAddress refPointer = tupleAddress tuplePointer) ∧
    (unsafeConvert reference = .ok tuplePointer →
      convertElement tuplePointer = .ok elementPointer →
      unsafeConvertPtrTupleRef unsafeConvert convertElement reference = .ok elementPointer ∧
      elementAddress elementPointer = tupleAddress tuplePointer)) ∧
  (∀ {TuplePointer ElementPointer : Type} (convert : TuplePointer → Jl ElementPointer)
      (pointer : TuplePointer) (elementPointer : ElementPointer)
      (tupleAddress : TuplePointer → Int) (elementAddress : ElementPointer → Int),
    (convert pointer = .ok elementPointer →
      elementAddress elementPointer = tupleAddress pointer) →
    unsafeConvertPtrTuple convert pointer = .ok elementPointer →
      elementAddress elementPointer = tupleAddress pointer)

def RefCoreBehavior : Prop :=
  RefScalarBehavior ∧ RefValueConstructionBehavior ∧ RefRefIndexBehavior ∧
  RefPointerIndexBehavior ∧ RefArrayIndexBehavior ∧ RefDataPointerBehavior ∧
  RefArrayPointerRouteBehavior ∧ RefTupleBehavior

def RefArrayInteropBehavior : Prop :=
  RefArrayIndexBehavior ∧ RefArrayPointerRouteBehavior ∧
  RefPointerArrayBehavior ∧ RefTupleBehavior

def entries : List Entry := [
  { id := "refpointer-core-behavior", juliaFile := "base/refpointer.jl"
    juliaFns := ["eltype(::Type{<:Ref{T}})", "convert(::Type{Ref{T}}, ::Ref{T})",
      "size(::Ref)", "axes(::Ref)", "length(::Ref)", "isempty(::Ref)", "ndims(::Ref)",
      "ndims(::Type{<:Ref})", "iterate(::Ref)", "iterate(::Ref, state)",
      "IteratorSize(::Type{<:Ref})", "unsafe_convert(::Type{Ref{T}}, ::Ref{T})",
      "unsafe_convert(::Type{Ref{T}}, x)", "convert(::Type{Ref{T}}, x)",
      "RefArray constructors", "convert(::Type{Ref{T}}, ::AbstractArray{T})",
      "unsafe_convert(::Ptr, ::RefArray)", "unsafe_convert(::Ptr{Any}, ::RefArray{Any})",
      "Ref(x::Any)", "Ref{T}()", "Ref{T}(x)", "Ref(::Ref, ::Integer)",
      "Ref(::Ptr{T}, ::Integer)", "Ref(::AbstractArray, ::Integer)",
      "getindex(::RefArray)", "setindex!(::RefArray)",
      "cconvert(::Type{Ref{T}}, ::NTuple{N,T})",
      "cconvert(::Type{Ref{T}}, ::Ref{NTuple{N,T}})",
      "unsafe_convert(::Type{Ref{T}}, ::Ref{NTuple{N,T}})",
      "unsafe_convert(::Type{Ptr{T}}, ::Ref{NTuple{N,T}})",
      "unsafe_convert(::Type{Ptr{T}}, ::Ptr{NTuple{N,T}})"]
    statement := "Ref has scalar shape and one-item iteration; initialized values, undefined-reference errors, array-backed access, pointer offsets, and tuple references preserve their documented behavior."
    source := "Ref docstring, base/refpointer.jl:97-150,182-194"
    status := .todo, prop := ``RefCoreBehavior, thm := none },
  { id := "refpointer-array-interoperability", juliaFile := "base/refpointer.jl"
    juliaFns := ["Ref{P}(::Array)", "Ref(::AbstractArray, ::Integer)",
      "cconvert(::Type{Ptr{P}}, ::Array{<:Union{Ptr,Cwstring,Cstring}})",
      "cconvert(::Type{Ref{P}}, ::Array{<:Union{Ptr,Cwstring,Cstring}})",
      "cconvert(::Type{Ptr{P}}, ::Array)", "cconvert(::Type{Ref{P}}, ::Array)",
      "cconvert(::Type{Ref{T}}, ::NTuple{N,T})",
      "cconvert(::Type{Ref{T}}, ::Ref{NTuple{N,T}})",
      "unsafe_convert(::Type{Ref{T}}, ::Ref{NTuple{N,T}})",
      "unsafe_convert(::Type{Ptr{T}}, ::Ref{NTuple{N,T}})",
      "unsafe_convert(::Type{Ptr{T}}, ::Ptr{NTuple{N,T}})",
      "getindex(::RefArray)", "setindex!(::RefArray)"]
    statement := "Pointer-array conversion reuses compatible storage or converts elements in order, retains each conversion root, appends C_NULL, and exposes tuple and array references through the expected element access and pointer view."
    source := "base/refpointer.jl:116-141,154-194"
    status := .todo, prop := ``RefArrayInteropBehavior, thm := none }
]

end JuliaLean.Proofs.base.refpointer