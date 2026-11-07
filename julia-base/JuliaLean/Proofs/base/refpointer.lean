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

end JuliaLean.Proofs.base.refpointer

namespace JuliaLean.ChatGPT.Batch4.Group15
open JuliaLean JuliaLean.base.refpointer JuliaLean.Proofs.base.refpointer

theorem ref_scalar_behavior : RefScalarBehavior := by
  refine ⟨?_, rfl, ?_, rfl, ?_, ?_⟩
  · intro α
    rfl
  · intro R r
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro R α E get r value h
    simp only [iterateRef, h, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro R S α r state
    rfl

theorem ref_value_construction_behavior : RefValueConstructionBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X R E construct get h x reference hx
    exact h x reference hx
  · intro T X R Y E construct convert get h x reference value hc hv
    exact h T x reference value hc hv
  · intro X R Y E construct convert get h x reference value hc hv
    exact h x reference value hc hv
  · intro T R X construct isBits isAssigned get hassigned hundef reference hc
    exact ⟨hassigned T reference hc, fun hb => hundef T reference hc hb⟩
  · intro R reference
    rfl

theorem ref_ref_index_behavior : RefRefIndexBehavior := by
  intro R I inst reference index one
  constructor
  · intro h
    simp [refRefIndex, h]
  · intro h
    simp [refRefIndex, h]

theorem ref_wrap_offset (address offset : Int) :
    wrapInt .u64 (address + wrapInt .u64 offset) = wrapInt .u64 (address + offset) := by
  change (address + offset % (2 ^ 64)) % (2 ^ 64) = (address + offset) % (2 ^ 64)
  simp only [Int.add_emod, Int.emod_emod]

theorem ref_pointer_index_behavior : RefPointerIndexBehavior := by
  constructor
  · intro T I S O one subtract sizeOf multiply toUInt indexValue sizeValue offsetValue
      pointer index hsubtract hmultiply hconvert
    change wrapInt .u64 (pointer.address.val +
      (toUInt (multiply (subtract index one) (sizeOf T))).val) = _
    rw [hconvert, hmultiply, hsubtract]
    exact ref_wrap_offset _ _
  · exact ref_ref_index_behavior

theorem ref_array_index_behavior : RefArrayIndexBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T A R length getindex hvalid hinvalid array index roots
    exact ⟨fun h => hinvalid array index h, fun h => hvalid array index h⟩
  · intro T A R setindex array index roots value updated h
    refine ⟨makeRefArray (T := T) updated index roots, ?_, rfl, rfl, rfl⟩
    simp only [setindexRefArray, makeRefArray, h, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  · intro T A getindex array
    rfl
  · intro T A I toInt array index converted h
    simp only [refAbstractArray, refArrayIntegerNothingRoots, refArrayIntNothingRoots, Option.getD_some, h, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
  · intro T A R array index roots
    rfl
  · intro T A array index
    rfl
  · intro T A R I toInt array index roots converted h
    simp only [refArrayIntegerAnyRoots, refArrayIntAnyRoots, h, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro T A I toInt array index converted h
    simp only [refArrayIntegerNothingRoots, refArrayIntNothingRoots, Option.getD_some, h, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem ref_data_pointer_behavior : RefDataPointerBehavior := by
  constructor
  · intro R P convert pointsToData h reference pointer hc
    exact h reference pointer hc
  · intro X P convert pointsToData h value pointer hc
    exact h value pointer hc

theorem ref_array_pointer_route_behavior : RefArrayPointerRouteBehavior := by
  constructor
  · intro T A R P Q V allocatedinline isConcrete isMutable pointer getindex
      pointerFromObjRef toPtrPtrCvoid pointerref sizePtrCvoid reference
    refine ⟨?_, ?_, ?_⟩
    · intro ha
      simp only [unsafeConvertRefArray, ha, ite_true]
    · intro ha hc hm
      simp only [unsafeConvertRefArray, ha, hc, hm, Bool.and_self,
        Bool.false_eq_true, ite_false, ite_true]
    · intro ha hcm
      simp only [unsafeConvertRefArray, ha, hcm, Bool.false_eq_true, ite_false]
  · intro A R P pointer reference
    rfl

theorem ref_tuple_behavior : RefTupleBehavior := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T R E N construct get tuple h reference hc
    exact h tuple reference hc
  · intro R reference
    rfl
  · intro R TuplePointer RefPointer ElementPointer convert convertRef convertElement
      tupleAddress refAddress elementAddress reference tuplePointer refPointer elementPointer
      href helement
    constructor
    · intro hc hr
      refine ⟨?_, href tuplePointer refPointer hr⟩
      simp only [unsafeConvertRefTuple, hc, Bind.bind, Except.bind, hr]
    · intro hc he
      refine ⟨?_, helement tuplePointer elementPointer he⟩
      simp only [unsafeConvertPtrTupleRef, hc, Bind.bind, Except.bind, he]
  · intro TuplePointer ElementPointer convert pointer elementPointer tupleAddress
      elementAddress h hc
    exact h hc

theorem RefpointerCoreBehavior_proven : JuliaLean.Proofs.base.refpointer.RefCoreBehavior := by
  exact ⟨ref_scalar_behavior, ref_value_construction_behavior, ref_ref_index_behavior,
    ref_pointer_index_behavior, ref_array_index_behavior, ref_data_pointer_behavior,
    ref_array_pointer_route_behavior, ref_tuple_behavior⟩

def ref_nul_error : JlError :=
  .argumentError "embedded NULs are not allowed in C strings: \"a\\0b\""

theorem ref_failed_pointer_has_no_pairing (roots pointers : List Unit) :
    ¬ PointerRootPairs (fun (_ : Unit) => .ok ())
      (fun (_ : Unit) => (Except.error ref_nul_error : Jl Unit))
      (fun (_ : Unit) => (Except.ok () : Jl Unit)) [()] roots pointers := by
  intro h
  cases roots with
  | nil => cases pointers <;> cases h
  | cons root roots =>
    cases pointers with
    | nil => cases h
    | cons pointer pointers =>
      obtain ⟨converted, herror, _⟩ := h.2.1
      cases herror

theorem ref_nul_conversion_failures :
    refPointerArray (T := Unit) (P := Unit) (Existing := Unit) (Root := Unit) (Q := Unit)
      ⟨false, false, false, false⟩ (fun _ => ()) (fun _ => .ok ())
      (fun _ => .error ref_nul_error) (fun _ => .ok ()) () [()] = .error ref_nul_error ∧
    cconvertPtrArray (T := Unit) (P := Unit) (Existing := Unit) (Root := Unit) (Q := Unit)
      ⟨false, false, false, false⟩ (fun _ => ()) (fun _ => .ok ())
      (fun _ => .error ref_nul_error) (fun _ => .ok ()) () [()] = .error ref_nul_error ∧
    cconvertRefPointerArray (T := Unit) (P := Unit) (Existing := Unit) (Root := Unit) (Q := Unit)
      ⟨false, false, false, false⟩ (fun _ => ()) (fun _ => .ok ())
      (fun _ => .error ref_nul_error) (fun _ => .ok ()) () [()] = .error ref_nul_error :=
  ⟨rfl, rfl, rfl⟩

end JuliaLean.ChatGPT.Batch4.Group15

namespace JuliaLean.Proofs.base.refpointer

open JuliaLean JuliaLean.base.refpointer JuliaLean.Registry

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
    status := .proven, prop := ``RefCoreBehavior, thm := some ``JuliaLean.ChatGPT.Batch4.Group15.RefpointerCoreBehavior_proven },
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
    status := .todo, prop := ``RefArrayInteropBehavior, thm := none, notes := "Frozen converting branch demands successful output without converter-success premises; registry prose promises ordered conversion and retained roots." }
]

end JuliaLean.Proofs.base.refpointer

namespace JuliaLean.ChatGPT.Batch8.Group4
open JuliaLean JuliaLean.base.refpointer JuliaLean.Proofs.base.refpointer

/-- A name-only reference to the existing private conversion loop. -/
local macro "g4RefOriginalLoop" : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.JuliaLean.base.refpointer 0).append
    `JuliaLean.base.refpointer.convertPointerArrayLoop)))

/-- Successful element conversion pairs retain one root and pointer per input. -/
theorem ref_pairs_lengths {T P Root Q : Type}
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (values : List T) (roots : List Root)
    (pointers : List P)
    (h : PointerRootPairs convertRoot convertPointer assertPointer values roots pointers) :
    roots.length = values.length ∧ pointers.length = values.length := by
  induction values generalizing roots pointers with
  | nil =>
    cases roots <;> cases pointers <;> simp only [PointerRootPairs] at h
    exact ⟨rfl, rfl⟩
  | cons value values ih =>
    cases roots with
    | nil => cases h
    | cons root roots =>
      cases pointers with
      | nil => cases h
      | cons pointer pointers =>
        obtain ⟨hr, hp⟩ := ih roots pointers h.2.2
        exact ⟨congrArg Nat.succ hr, congrArg Nat.succ hp⟩

/-- The branch that already has the requested element type never calls a converter. -/
theorem ref_existing_conversion {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (values : List T)
    (same : tests.sameElementType = true) :
    refPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.existing (arrayRef values)) ∧
    cconvertPtrArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.existing (arrayRef values)) ∧
    cconvertRefPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.existing (arrayRef values)) := by
  have h : refPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.existing (arrayRef values)) := by
    simp only [refPointerArray, same, ite_true, Pure.pure, Except.pure]
  exact ⟨h, h, h⟩

/-- A compatible storage layout keeps the array and uses the first element index. -/
theorem ref_direct_conversion {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (values : List T)
    (different : tests.sameElementType = false)
    (layout : (if tests.isBitsElement then tests.pointerOrCStringLayout else
      tests.elementSubtypeOfPointer) = true) :
    refPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.direct (makeRefArray values (int64 1) ())) ∧
    cconvertPtrArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.direct (makeRefArray values (int64 1) ())) ∧
    cconvertRefPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.direct (makeRefArray values (int64 1) ())) := by
  have h : refPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.direct (makeRefArray values (int64 1) ())) := by
    simp only [refPointerArray, different, Bool.false_eq_true, ite_false, layout,
      ite_true, Pure.pure, Except.pure]
  exact ⟨h, h, h⟩


/-- One source-loop iteration, stated as an equation usable by the simplifier. -/
theorem ref_loop_cons {T P Root Q : Type}
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (value : T) (values : List T) :
    g4RefOriginalLoop convertRoot convertPointer assertPointer (value :: values) =
      (do
        let root ← convertRoot value
        let converted ← convertPointer root
        let pointer ← assertPointer converted
        let (pointers, roots) ← g4RefOriginalLoop convertRoot convertPointer assertPointer values
        pure (pointer :: pointers, root :: roots)) := by
  rfl

/-- The frozen element loop realizes any successful, ordered conversion relation. -/
theorem ref_loop_of_pairs {T P Root Q : Type}
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (values : List T) (roots : List Root)
    (pointers : List P)
    (h : PointerRootPairs convertRoot convertPointer assertPointer values roots pointers) :
    g4RefOriginalLoop
      convertRoot convertPointer assertPointer values = .ok (pointers, roots) := by
  induction values generalizing roots pointers with
  | nil =>
    cases roots <;> cases pointers <;> simp only [PointerRootPairs] at h
    rfl
  | cons value values ih =>
    cases roots with
    | nil => cases h
    | cons root roots =>
      cases pointers with
      | nil => cases h
      | cons pointer pointers =>
        obtain ⟨hr, ⟨converted, hc, hp⟩, ht⟩ := h
        simp only [ref_loop_cons,
          hr, hc, hp, ih roots pointers ht, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Total element converters provide ordered roots and pointers for any finite list. -/
theorem ref_pairs_of_element_success {T P Root Q : Type}
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (values : List T)
    (success : ∀ value ∈ values, ∃ root converted pointer,
      convertRoot value = .ok root ∧ convertPointer root = .ok converted ∧
        assertPointer converted = .ok pointer) :
    ∃ roots pointers, PointerRootPairs convertRoot convertPointer assertPointer values roots pointers := by
  induction values with
  | nil => exact ⟨[], [], True.intro⟩
  | cons value values ih =>
    obtain ⟨root, converted, pointer, hr, hc, hp⟩ := success value (List.mem_cons_self)
    obtain ⟨roots, pointers, ht⟩ := ih (fun v hv => success v (List.mem_cons_of_mem value hv))
    exact ⟨root :: roots, pointer :: pointers, hr, ⟨converted, hc, hp⟩, ht⟩

/-- Under the exact missing success premise, all three routes append null and retain roots. -/
theorem ref_converted_array_of_pairs {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (values : List T)
    (roots : List Root) (pointers : List P)
    (different : tests.sameElementType = false)
    (layout : (if tests.isBitsElement then tests.pointerOrCStringLayout else
      tests.elementSubtypeOfPointer) = false)
    (pairs : PointerRootPairs convertRoot convertPointer assertPointer values roots pointers) :
    let reference := makeRefArray (T := P) (pointers ++ [null]) (int64 1) roots
    refPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.converted reference) ∧
    cconvertPtrArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.converted reference) ∧
    cconvertRefPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.converted reference) ∧ roots.length = values.length ∧
      pointers.length = values.length := by
  have loop := ref_loop_of_pairs convertRoot convertPointer assertPointer values roots pointers pairs
  have result : refPointerArray tests arrayRef convertRoot convertPointer assertPointer null values =
      .ok (.converted (makeRefArray (pointers ++ [null]) (int64 1) roots)) := by
    simp only [refPointerArray, different, layout, Bool.false_eq_true, ite_false,
      loop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨result, result, result, ref_pairs_lengths convertRoot convertPointer assertPointer
    values roots pointers pairs⟩

/-- A root-conversion error at the first input is propagated before later inputs. -/
theorem ref_head_root_error {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (value : T) (values : List T)
    (error : JlError) (different : tests.sameElementType = false)
    (layout : (if tests.isBitsElement then tests.pointerOrCStringLayout else
      tests.elementSubtypeOfPointer) = false)
    (failure : convertRoot value = .error error) :
    refPointerArray tests arrayRef convertRoot convertPointer assertPointer null (value :: values) =
      .error error := by
  simp only [refPointerArray, different, layout, Bool.false_eq_true, ite_false,
    ref_loop_cons,
    failure, Bind.bind, Except.bind]

/-- A pointer-conversion error is propagated after its root has been constructed. -/
theorem ref_head_pointer_error {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (value : T) (values : List T)
    (root : Root) (error : JlError) (different : tests.sameElementType = false)
    (layout : (if tests.isBitsElement then tests.pointerOrCStringLayout else
      tests.elementSubtypeOfPointer) = false)
    (rootSuccess : convertRoot value = .ok root)
    (failure : convertPointer root = .error error) :
    refPointerArray tests arrayRef convertRoot convertPointer assertPointer null (value :: values) =
      .error error := by
  simp only [refPointerArray, different, layout, Bool.false_eq_true, ite_false,
    ref_loop_cons,
    rootSuccess, failure, Bind.bind, Except.bind]

/-- A failed element type check propagates its error without accepting a converted array. -/
theorem ref_head_assert_error {T P Existing Root Q : Type}
    (tests : PointerArrayTypeTests) (arrayRef : List T → Existing)
    (convertRoot : T → Jl Root) (convertPointer : Root → Jl Q)
    (assertPointer : Q → Jl P) (null : P) (value : T) (values : List T)
    (root : Root) (pointer : Q) (error : JlError)
    (different : tests.sameElementType = false)
    (layout : (if tests.isBitsElement then tests.pointerOrCStringLayout else
      tests.elementSubtypeOfPointer) = false)
    (rootSuccess : convertRoot value = .ok root)
    (pointerSuccess : convertPointer root = .ok pointer)
    (failure : assertPointer pointer = .error error) :
    refPointerArray tests arrayRef convertRoot convertPointer assertPointer null (value :: values) =
      .error error := by
  simp only [refPointerArray, different, layout, Bool.false_eq_true, ite_false,
    ref_loop_cons,
    rootSuccess, pointerSuccess, failure, Bind.bind, Except.bind]

end JuliaLean.ChatGPT.Batch8.Group4