import JuliaLean.base.genericmemory
import JuliaLean.Registry.Types

/-!
# Properties of `base/genericmemory.jl`

The statements below describe the public contracts and memory invariants of the typed methods in
`JuliaLean.base.genericmemory`. Runtime allocation, pointer, bounds, conversion, and atomic storage
operations remain typed callees supplied by their owning Base or runtime modules.
-/

namespace JuliaLean.Proofs.base.genericmemory

open JuliaLean JuliaLean.base.genericmemory JuliaLean.Registry

abbrev I64 := JuliaLean.base.genericmemory.I64

/-- GenericMemory uses the linear indexing style of its DenseVector interface. -/
def MemoryLinearIndexing : Prop :=
  ∀ (memoryType : GenericMemoryType), indexStyle memoryType = .linear

/-- A valid reference's reported index is one-based and lies in its backing memory. -/
def MemoryIndexIsOneBased : Prop :=
  ∀ {M P : Type} (memoryrefoffset : GenericMemoryRef M P → I64) (length : I64)
    (ref : GenericMemoryRef M P),
    1 ≤ (memoryrefoffset ref).val → (memoryrefoffset ref).val ≤ length.val →
      1 ≤ (memoryindex memoryrefoffset ref).val ∧
        (memoryindex memoryrefoffset ref).val ≤ length.val

/-- An out-of-bounds checked assignment query returns false without reading a slot. -/
def MemoryIsassignedBounds : Prop :=
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V) (a : M) (i : I64),
    ops.checkboundsBool a i = some false → isassignedMemory ops true a i = some false) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (ref : GenericMemoryRef M P) (assigned : Bool),
    ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true = some assigned →
      isassignedRef ops true ref = some assigned)

/-- Checked memory-reference copies and range assignment stop when their bounds check fails. -/
def GenericMemoryCheckedAccessesInBounds : Prop :=
  (∀ {M P T D S N I Ptr Token : Type}
      (copy : MemoryCopyOps Option M P D S N I Ptr Token)
      (dest src : GenericMemoryRef M P) (n : N),
    copy.isZero n = false → copy.checkEnd dest n = none →
      unsafeCopytoRefs (T := T) copy true dest src n = none) ∧
  (∀ {M P T I : Type} (copy : MemoryCopyOps Option M P I64 I64 I64 I64 P Unit)
      (checkbounds : M → I → Option Unit) (rangeLength rangeFirst : I → Option I64)
      (shapeCheck : M → I64 → Option Unit) (a x : M) (indices : I),
    checkbounds a indices = none →
      setindexMemoryRange (T := T) copy checkbounds rangeLength rangeFirst shapeCheck true a x indices = none)

/-- Copy operations preserve the original slot sequence, including undefined slots; fallback
copy converts defined values to the destination element type. -/
def MemoryCopyPreservesContents : Prop :=
  (∀ {m : Type → Type} {M P T N D S I Ptr Token : Type} [Monad m]
      (copy : MemoryCopyOps m M P D S N I Ptr Token)
      (contents : GenericMemoryRef M P → N → m (List (Option T)))
      (dest src : GenericMemoryRef M P) (n : N) (before : List (Option T)),
    contents src n = pure before →
      (do
        let _ ← unsafeCopytoRefs (T := T) copy true dest src n
        contents dest n) = pure before) ∧
  (∀ {m : Type → Type} {M P T Ptr Token : Type} [Monad m]
      (copy : MemoryCopyOps m M P I64 I64 I64 I64 Ptr Token)
      (contents : M → I64 → I64 → m (List (Option T)))
      (dest src : M) (doffs soffs n : I64) (before : List (Option T)),
    contents src soffs n = pure before →
      (do
        let _ ← unsafeCopytoMemoryTyped (T := T) copy true dest doffs src soffs n
        contents dest doffs n) = pure before) ∧
  (∀ {m : Type → Type} {M P TD TS D S N I Ptr Token : Type} [Monad m]
      (destOps : MemoryAccessOps m M P TD TS) (srcOps : MemoryAccessOps m M P TS TS)
      (copy : MemoryCopyOps m M P D S N I Ptr Token)
      (sourceContents : M → S → N → m (List (Option TS)))
      (destinationContents : M → D → N → m (List (Option TD)))
      (dest src : M) (doffs : D) (soffs : S) (n : N) (before : List (Option TS)),
    sourceContents src soffs n = pure before →
      (do
        let _ ← unsafeCopytoMemoryFallback destOps srcOps copy dest doffs src soffs n
        destinationContents dest doffs n) =
          before.mapM fun slot => do
            match slot with
            | none => pure none
            | some value =>
                let stored ← match destOps.castElement value with
                  | some converted => pure converted
                  | none => destOps.convertElement value
                pure (some stored)) ∧
  (∀ {m : Type → Type} {M P TD TS N I Ptr Token : Type} [Monad m]
      (destOps : MemoryAccessOps m M P TD TS) (srcOps : MemoryAccessOps m M P TS TS)
      (copy : MemoryCopyOps m M P I64 I64 N I Ptr Token)
      (memoryrefoffset : GenericMemoryRef M P → I64)
      (sourceContents : M → I64 → N → m (List (Option TS)))
      (destinationContents : M → I64 → N → m (List (Option TD)))
      (sameElementType : Decidable (TD = TS)) (dest src : GenericMemoryRef M P) (n : N)
      (before : List (Option TS)),
    sourceContents src.mem (memoryrefoffset src) n = pure before →
      (do
        let _ ← unsafeCopytoGenericRefs destOps srcOps copy true memoryrefoffset
          sameElementType dest src n
        destinationContents dest.mem (memoryrefoffset dest) n) =
          before.mapM fun slot => do
            match slot with
            | none => pure none
            | some value =>
                let stored ← match destOps.castElement value with
                  | some converted => pure converted
                  | none => destOps.convertElement value
                pure (some stored)) ∧
  (∀ {m : Type → Type} {M P T Ptr Token : Type} [Monad m]
      (copy : MemoryCopyOps m M P I64 I64 I64 I64 Ptr Token)
      (length : M → m I64) (construct : I64 → m M)
      (contents : M → I64 → I64 → m (List (Option T)))
      (source : M) (n : I64) (before : List (Option T)),
    length source = pure n → contents source 1 n = pure before →
      (do
        let result ← copyMemory (T := T) copy length construct source
        contents result 1 n) = pure before)

/-- Unsetting a memory slot returns its original reference or memory object, and after a
successful runtime unset its reference reads unassigned. -/
def MemoryUnsetReturnsTarget : Prop :=
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (ref : GenericMemoryRef M P),
    ops.memoryrefUnset ref .notAtomic true = some () →
      unsetindexRef ops true ref = some ref) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (a : M) (i : I64) (ref : GenericMemoryRef M P),
    ops.memoryrefAt a i = some ref → ops.memoryrefUnset ref .notAtomic true = some () →
      unsetindexMemoryInt ops true a i = some a) ∧
  (∀ {M P T V I : Type} (ops : MemoryAccessOps Option M P T V)
      (toIndex : I → Option I64) (unsetArray : Unit → I64 → Option Unit)
      (a : M) (i : I) (index : I64) (ref : GenericMemoryRef M P),
    toIndex i = some index → ops.memoryrefAt a index = some ref →
      ops.memoryrefUnset ref .notAtomic true = some () →
        unsetindexUnionInteger ops true toIndex unsetArray (.memory a) i = some (.memory a)) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V) (ref : GenericMemoryRef M P),
    (do
      ops.memoryrefUnset ref .notAtomic true
      ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
      (do
        let result ← unsetindexRef ops true ref
        let assigned ← ops.memoryrefIsAssigned result (ops.defaultOrderRef result) true
        pure (result, assigned)) = pure (ref, false)) ∧
  (∀ {M P T V : Type}
      (ops : MemoryAccessOps Option M P T V) (a : M) (i : I64),
    (do
      let ref ← ops.memoryrefAt a i
      ops.memoryrefUnset ref .notAtomic true
      ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
      (do
        let _ ← unsetindexMemoryInt ops true a i
        let ref ← ops.memoryrefAt a i
        ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false) ∧
  (∀ {A I P T V : Type}
      (ops : MemoryAccessOps Option A P T V) (toIndex : I → Option I64)
      (unsetArray : A → I64 → Option Unit) (isassignedArray : A → I64 → Option Bool)
      (array : A) (i : I) (index : I64),
    toIndex i = pure index →
      (do unsetArray array index; isassignedArray array index) = pure false →
        (do
          let _ ← unsetindexUnionInteger ops false toIndex unsetArray (.array array) i
          isassignedArray array index) = pure false)

/-- Atomic unsetting forwards the requested order, returns the same reference or memory object,
and after a successful runtime atomic unset its reference reads unassigned. -/
def AtomicMemoryUnsetReturnsReference : Prop :=
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (ref : GenericMemoryRef M P) (order : MemoryOrder),
    ops.memoryrefUnset ref order true = some () →
      unsetindexAtomicRef ops true ref order = some ref) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (a : M) (i : I64) (ref : GenericMemoryRef M P) (order : MemoryOrder),
    ops.memoryrefAt a i = some ref → ops.memoryrefUnset ref order true = some () →
      unsetindexAtomicMemoryInt ops true a order i = some a) ∧
  (∀ {M P T V I : Type} (ops : MemoryAccessOps Option M P T V)
      (toIndex : I → Option I64) (a : M) (i : I) (index : I64)
      (ref : GenericMemoryRef M P) (order : MemoryOrder),
    toIndex i = some index → ops.memoryrefAt a index = some ref →
      ops.memoryrefUnset ref order true = some () →
        unsetindexAtomicMemoryInteger ops true toIndex a order i = some a) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (ref : GenericMemoryRef M P) (order : MemoryOrder),
    (do
      ops.memoryrefUnset ref order true
      ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
      (do
        let result ← unsetindexAtomicRef ops true ref order
        let assigned ← ops.memoryrefIsAssigned result (ops.defaultOrderRef result) true
        pure (result, assigned)) = pure (ref, false)) ∧
  (∀ {M P T V : Type}
      (ops : MemoryAccessOps Option M P T V) (a : M) (i : I64) (order : MemoryOrder),
    (do
      let ref ← ops.memoryrefAt a i
      ops.memoryrefUnset ref order true
      ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
      (do
        let _ ← unsetindexAtomicMemoryInt ops true a order i
        let ref ← ops.memoryrefAt a i
        ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false) ∧
  (∀ {M P T V I : Type}
      (ops : MemoryAccessOps Option M P T V) (toIndex : I → Option I64)
      (a : M) (i : I) (index : I64) (order : MemoryOrder),
    toIndex i = pure index →
      (do
        let ref ← ops.memoryrefAt a index
        ops.memoryrefUnset ref order true
        ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false →
          (do
            let _ ← unsetindexAtomicMemoryInteger ops true toIndex a order i
            let ref ← ops.memoryrefAt a index
            ops.memoryrefIsAssigned ref (ops.defaultOrderRef ref) true) = pure false)

/-- Copying a Memory allocates a distinct storage object with the original element count. -/
def MemoryCopyPreservesExtent : Prop :=
  ∀ {M P T Ptr Token : Type}
    (copy : MemoryCopyOps Option M P I64 I64 I64 I64 Ptr Token)
    (length : M → Option I64) (construct : I64 → Option M)
    (sameStorage : M → M → Bool) (a result : M) (n : I64),
    length a = some n →
    (∀ allocated, construct n = some allocated →
      length allocated = some n ∧ sameStorage a allocated = false) →
    copyMemory (T := T) copy length construct a = some result →
      length result = some n ∧ sameStorage a result = false

/-- Every `similar` overload preserves the requested element count. -/
def SimilarMemoryPreservesExtent : Prop :=
  (∀ {M : Type} (length : M → Option I64) (construct : I64 → Option M)
      (a result : M) (n : I64),
    length a = some n → construct n = some result → length result = some n →
      similarMemory length construct a = some result) ∧
  (∀ {M R : Type} (length : M → Option I64) (construct : Type → I64 → Option R)
      (a : M) (result : R) (elementType : Type) (n : I64),
    length a = some n → construct elementType n = some result →
      similarMemoryElementType (T := elementType) length construct a elementType = some result) ∧
  (∀ {M : Type} (construct : I64 → Option M) (a result : M) (n : I64),
    construct n = some result → similarMemoryLength construct a n = some result) ∧
  (∀ {M R D : Type} (construct : Type → I64 → Option R)
      (firstDim : D → Option I64) (a : M) (elementType : Type) (dims : D)
      (result : R) (n : I64),
    firstDim dims = some n → construct elementType n = some result →
      similarMemoryElementDims (T := elementType) construct firstDim a elementType dims = some result) ∧
  (∀ {M D : Type} (construct : I64 → Option M) (firstDim : D → Option I64)
      (a result : M) (dims : D) (n : I64),
    firstDim dims = some n → construct n = some result →
      similarMemoryDims construct firstDim a dims = some result)

/-- Byte-memory fill converts the integer to the element type before filling every byte. -/
def ByteMemoryFillUsesConvertedValue : Prop :=
  (∀ {M P X U USize Token : Type}
    (elementType : M → Type) (isInteger : X → Prop)
    (castElement : Type → X → Option U) (convert : Type → X → Option U) (preserveBegin : M → Token)
    (preserveEnd : Token → Option Unit) (unsafeConvert : M → Option P)
    (memset : P → U → USize → Option Unit) (lengthModUInt : M → Option USize)
    (a : M) (x : X) (integerProof : isInteger x) (value : U) (size : USize) (ptr : P) (token : Token),
    castElement (elementType a) x = some value → preserveBegin a = token →
      unsafeConvert a = some ptr → lengthModUInt a = some size →
        memset ptr value size = some () → preserveEnd token = some () →
          fillByteMemory elementType isInteger castElement convert preserveBegin preserveEnd
            unsafeConvert memset lengthModUInt a x integerProof = some a) ∧
  (∀ {M P X U USize Token : Type} (elementType : M → Type) (isInteger : X → Prop)
      (castElement : Type → X → Option U) (convert : Type → X → Option U)
      (preserveBegin : M → Token) (preserveEnd : Token → Option Unit)
      (unsafeConvert : M → Option P) (memset : P → U → USize → Option Unit)
      (lengthModUInt : M → Option USize) (a : M) (x : X) (integerProof : isInteger x)
      (value : U) (size : USize) (ptr : P) (token : Token),
    castElement (elementType a) x = none → convert (elementType a) x = some value →
      preserveBegin a = token → unsafeConvert a = some ptr → lengthModUInt a = some size →
        memset ptr value size = some () → preserveEnd token = some () →
          fillByteMemory elementType isInteger castElement convert preserveBegin preserveEnd
            unsafeConvert memset lengthModUInt a x integerProof = some a)

/-- Converting to a Memory type reuses an existing target value; promotion combines element types. -/
def MemoryConversionAndPromotion : Prop :=
  (∀ {M A : Type} (asTarget : A → Option M) (construct : A → Option M) (a : A) (memory : M),
    asTarget a = some memory → convertMemory asTarget construct a = some memory) ∧
  (∀ {M A : Type} (asTarget : A → Option M) (construct : A → Option M) (a : A) (memory : M),
    asTarget a = none → construct a = some memory → convertMemory asTarget construct a = some memory) ∧
  (∀ {R : Type} (promoteType : Type → Type → Type)
      (elSame : Type → Type → Type → R) (T S : Type),
    promoteRuleMemory promoteType elSame T S = elSame (promoteType T S) T S)

/-- Constructing `Memory{T}` from an array performs the checked axis-compatible copy. -/
def MemoryArrayConstructorCopies : Prop :=
  ∀ {M A D : Type} (size : A → Option D) (constructUndef : D → Option M)
    (copytoAxcheck : M → A → Option M) (x : A) (n : D) (destination : M),
    size x = some n → constructUndef n = some destination →
      memoryFromArray size constructUndef copytoAxcheck x = copytoAxcheck destination x

/-- Memory range indexing validates indices, creates the result shape, and copies a nonempty slice. -/
def MemoryRangeGetindexChecksBounds : Prop :=
  (∀ {M I : Type} (construct : I64 → Option M)
      (copyImpl : M → I64 → M → I64 → I64 → Option M)
      (checkbounds : M → I → Option Unit) (rangeLength rangeAxes rangeFirst : I → Option I64)
      (firstindex : M → Option I64) (a : M) (indices : I),
    checkbounds a indices = none →
      getindexMemoryRange copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex
        construct a indices true = none) ∧
  (∀ {M I : Type} (construct : I64 → Option M)
      (copyImpl : M → I64 → M → I64 → I64 → Option M)
      (checkbounds : M → I → Option Unit) (rangeLength rangeAxes rangeFirst : I → Option I64)
      (firstindex : M → Option I64) (a result : M) (indices : I)
      (start span dims first : I64),
    checkbounds a indices = some () → rangeLength indices = some span →
      0 < span.val → rangeAxes indices = some dims → construct dims = some result →
        firstindex result = some first → rangeFirst indices = some start →
          copyImpl result first a start span = some result →
            getindexMemoryRange copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex
              construct a indices true = some result) ∧
  (∀ {M I J : Type} (construct : I64 → Option M)
      (copyImpl : M → I64 → M → I64 → I64 → Option M)
      (checkbounds : M → J → Option Unit) (rangeLength rangeAxes rangeFirst : J → Option I64)
      (firstindex : M → Option I64) (toIndex : I → Option J) (a result : M)
      (range : I) (indices : J),
    toIndex range = some indices →
      getindexMemoryRange copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex
        construct a indices true = some result →
          getindexMemoryBoolRange construct copyImpl checkbounds rangeLength rangeAxes
            rangeFirst firstindex toIndex a range true = some result)

/-- Scalar Memory assignment returns its destination after writing the converted value. -/
def MemoryScalarSetindexReturnsTarget : Prop :=
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
    (a : M) (value : V) (i : I64) (stored : T) (base ref : GenericMemoryRef M P),
    ops.castElement value = some stored → ops.checkbounds a i = some () →
      ops.memoryref a = some base → ops.memoryrefNew base i false = some ref →
        ops.memoryrefSet ref stored .notAtomic false = some () →
          setindexMemory ops true a value i = some a) ∧
  (∀ {M P T V : Type} (ops : MemoryAccessOps Option M P T V)
      (throwBounds : M → I64 → I64 → List I64 → Option Unit)
      (a : M) (value : V) (i1 i2 : I64) (indices : List I64),
    i2 = 1 → indices.all (fun i => i == 1) = true →
      setindexMemoryCartesian ops true throwBounds a value i1 i2 indices =
        setindexMemory ops true a value i1)

/-- Range and colon assignment reject a source whose shape does not match the target span. -/
def MemoryBulkSetindexChecksShape : Prop :=
  (∀ {M P T I : Type} (copy : MemoryCopyOps Option M P I64 I64 I64 I64 P Unit)
      (checkbounds : M → I → Option Unit) (rangeLength rangeFirst : I → Option I64)
      (shapeCheck : M → I64 → Option Unit) (a x : M) (indices : I) (span : I64),
    rangeLength indices = some span → shapeCheck x span = none →
      setindexMemoryRange (T := T) copy checkbounds rangeLength rangeFirst shapeCheck true a x indices = none) ∧
  (∀ {M P T : Type} (copy : MemoryCopyOps Option M P I64 I64 I64 I64 P Unit)
      (length : M → Option I64) (shapeCheck : M → I64 → Option Unit) (a x : M)
      (span : I64), length a = some span → shapeCheck x span = none →
      setindexMemoryColon (T := T) copy length shapeCheck true a x = none)

/-- Byte-memory comparison is lexicographic, with length deciding equal prefixes. -/
def ByteMemoryComparisonOrdersPrefix : Prop :=
  ∀ {M Ptr Tok : Type} (length : M → Option I64) (gcPreserveBegin : M → Tok)
    (gcPreserveEnd : Tok → Option Unit) (unsafeConvert : M → Option Ptr)
    (memcmp : Ptr → Ptr → I64 → Option I64) (cmpLength : I64 → I64 → Option I64)
    (a b : M) (c : I64) (pa pb : Ptr) (la lb : I64) (ta tb : Tok),
    length a = some la → length b = some lb → gcPreserveBegin a = ta → gcPreserveBegin b = tb →
      unsafeConvert a = some pa → unsafeConvert b = some pb →
        gcPreserveEnd ta = some () → gcPreserveEnd tb = some () →
          memcmp pa pb (min la lb) = some c →
            (c < 0 → cmpByteMemory length gcPreserveBegin gcPreserveEnd unsafeConvert memcmp
              cmpLength a b = some (-1)) ∧
            (0 < c → cmpByteMemory length gcPreserveBegin gcPreserveEnd unsafeConvert memcmp
              cmpLength a b = some 1) ∧
            (c = 0 → cmpByteMemory length gcPreserveBegin gcPreserveEnd unsafeConvert memcmp
              cmpLength a b = cmpLength la lb)

/-- Bit-integer Memory equality requires equal lengths and equal stored bytes. -/
def BitIntegerMemoryEqualityRequiresEqualLengths : Prop :=
  ∀ {M Ptr Tok : Type} (length : M → Option I64) (gcPreserveBegin : M → Tok)
    (gcPreserveEnd : Tok → Option Unit) (unsafeConvert : M → Option Ptr)
    (sizeofElement : Type → I64) (elementType : M → Type)
    (memcmp : Ptr → Ptr → I64 → Option I64) (a b : M) (la lb : I64),
    length a = some la → length b = some lb →
    (la ≠ lb →
      equalBitIntegerMemory length gcPreserveBegin gcPreserveEnd unsafeConvert sizeofElement
        elementType memcmp a b = some false)
    ∧ (∀ (c : I64) (pa pb : Ptr) (ta tb : Tok),
        la = lb → gcPreserveBegin a = ta → gcPreserveBegin b = tb →
          unsafeConvert a = some pa → unsafeConvert b = some pb →
          gcPreserveEnd ta = some () → gcPreserveEnd tb = some () →
          memcmp pa pb (sizeofElement (elementType a) * la) = some c →
            equalBitIntegerMemory length gcPreserveBegin gcPreserveEnd unsafeConvert sizeofElement
              elementType memcmp a b = some (c == 0))

/-- Sorted search routing agrees with general search; unsorted inputs use the general path. -/
def MemoryFindallUsesSortedSearch : Prop :=
  (∀ {M X R : Type} (issortedMemory : M → SortDirection → Option Bool)
    (issortedNeedle : X → SortDirection → Option Bool)
    (sortedFindin findin : M → X → Option R) (pred : Fix2In X) (x : M) (result : R),
    issortedMemory x .forward = some true → issortedNeedle pred.x .forward = some true →
      sortedFindin x pred.x = some result →
        findallMemory issortedMemory issortedNeedle
          sortedFindin findin pred x = some result) ∧
  (∀ {M X R : Type} (issortedMemory : M → SortDirection → Option Bool)
      (issortedNeedle : X → SortDirection → Option Bool)
      (sortedFindin findin : M → X → Option R) (pred : Fix2In X) (x : M) (result : R),
    issortedMemory x .forward = some false → findin x pred.x = some result →
      findallMemory issortedMemory issortedNeedle
        sortedFindin findin pred x = some result) ∧
  (∀ {M X R : Type} (issortedMemory : M → SortDirection → Option Bool)
      (issortedNeedle : X → SortDirection → Option Bool)
      (sortedFindin findin : M → X → Option R) (pred : Fix2In X) (x : M) (result : R),
    issortedMemory x .forward = some true → issortedNeedle pred.x .forward = some false →
      findin x pred.x = some result →
        findallMemory issortedMemory issortedNeedle
          sortedFindin findin pred x = some result)

/-- `indcopy` uses each dimension's subregion, with the trailing dimension scaled by its suffix. -/
def MemoryIndcopyKeepsDimensionRegions : Prop :=
  ∀ {M X Y Vector : Type} (sizeAt : List I64 → I64 → Option I64)
    (sizeLength : List I64 → I64) (rangeFromTo : I64 → I64 → Option (List I64))
    (oneRange : I64 → Option (List I64)) (addInt mulInt : I64 → I64 → Option I64)
    (length : M → Option I64) (getindex : M → I64 → Option X)
    (findin : X → List I64 → Option Y) (subindex : X → Y → Option Y)
    (toVector : List Y → Option Vector) (vectorLength : Vector → Nat)
    (sz : List I64) (indices : M) (dst src : Vector) (n : I64),
    length indices = some n →
    (∃ positions, rangeFromTo 1 n = some positions ∧ positions.length = n.val.toNat) →
    (∀ ys vector, toVector ys = some vector → vectorLength vector = ys.length) →
    indcopy sizeAt sizeLength rangeFromTo oneRange addInt mulInt length getindex
      findin subindex toVector sz indices = some (dst, src) →
        vectorLength dst = n.val.toNat ∧ vectorLength src = n.val.toNat

/-- Atomic get/set/modify/swap/replace operations pass their memory order to the runtime operation. -/
def AtomicMemoryOperationsPreserveOrdering : Prop :=
  (∀ {M P V : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (memoryrefGet : GenericMemoryRef M P → MemoryOrder → Bool → Option V)
      (mem : M) (order : MemoryOrder) (i : I64) (ref : GenericMemoryRef M P) (value : V),
    memoryrefAt mem i = some ref → memoryrefGet ref order true = some value →
      getindexAtomic memoryrefAt memoryrefGet true mem order i = some value) ∧
  (∀ {M P T V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (castElement : V → Option T) (convert : V → Option T)
      (memoryrefSet : GenericMemoryRef M P → T → MemoryOrder → Bool → Option R)
      (mem : M) (order : MemoryOrder) (input : V) (i : I64) (ref : GenericMemoryRef M P)
      (value : T) (result : R),
    memoryrefAt mem i = some ref → castElement input = some value →
      memoryrefSet ref value order true = some result →
        setindexAtomic memoryrefAt castElement convert memoryrefSet true mem order input i = some result) ∧
  (∀ {M P Op V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (memoryrefModify : GenericMemoryRef M P → Op → V → MemoryOrder → Bool → Option R)
      (mem : M) (order : MemoryOrder) (op : Op) (value : V) (i : I64)
      (ref : GenericMemoryRef M P) (result : R),
    memoryrefAt mem i = some ref → memoryrefModify ref op value order true = some result →
      modifyindexAtomic memoryrefAt memoryrefModify true mem order op value i = some result) ∧
  (∀ {M P T V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (castElement : V → Option T) (convert : V → Option T)
      (memoryrefSetOnce : GenericMemoryRef M P → T → MemoryOrder → MemoryOrder → Bool → Option R)
      (mem : M) (successOrder failOrder : MemoryOrder) (input : V) (i : I64)
      (ref : GenericMemoryRef M P) (value : T) (result : R),
    memoryrefAt mem i = some ref → castElement input = some value →
      memoryrefSetOnce ref value successOrder failOrder true = some result →
        setindexonceAtomic memoryrefAt castElement convert memoryrefSetOnce true mem
          successOrder failOrder input i = some result) ∧
  (∀ {M P T V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (castElement : V → Option T) (convert : V → Option T)
      (memoryrefSwap : GenericMemoryRef M P → T → MemoryOrder → Bool → Option R)
      (mem : M) (order : MemoryOrder) (input : V) (i : I64) (ref : GenericMemoryRef M P)
      (value : T) (result : R),
    memoryrefAt mem i = some ref → castElement input = some value →
      memoryrefSwap ref value order true = some result →
        swapindexAtomic memoryrefAt castElement convert memoryrefSwap true mem order input i = some result) ∧
  (∀ {M P T E V R : Type} (memoryrefAt : M → I64 → Option (GenericMemoryRef M P))
      (castElement : V → Option T) (convert : V → Option T)
      (memoryrefReplace : GenericMemoryRef M P → E → T → MemoryOrder → MemoryOrder → Bool → Option R)
      (mem : M) (successOrder failOrder : MemoryOrder) (expected : E) (input : V) (i : I64)
      (ref : GenericMemoryRef M P) (value : T) (result : R),
    memoryrefAt mem i = some ref → castElement input = some value →
      memoryrefReplace ref expected value successOrder failOrder true = some result →
        replaceindexAtomic memoryrefAt castElement convert memoryrefReplace true mem
          successOrder failOrder expected input i = some result)

/-! Nothing to promise:
- `parent@66`: pure projection of the `mem` field of a reference.
- `pointer@89`: direct `unsafe_convert` forwarding; pointer validity is the runtime callee's contract.
- `elsize@185`: direct `aligned_sizeof` forwarding.
- `sizeof@186`: direct `Core.sizeof` forwarding.
- `getindex@322`: direct forwarding to `copy(A)`; copy semantics are specified separately.
- `copyto!@265`: sets default offsets and delegates to the next `copyto!` method.
- `copyto!@266`: direct forwarding to `_copyto_impl!` in another Base file.
-/

/-! ## Proofs -/

/-- Bind of a `some` in the `Bind.bind` form produced by `do` notation. -/
theorem bind_some_shift {α β : Type} (f : α → Option β) (a : α) :
    (some a >>= f) = f a := rfl

/-- Bind of a `pure` in the `Bind.bind` form produced by `do` notation. -/
theorem bind_pure_shift {α β : Type} (f : α → Option β) (a : α) :
    ((pure a : Option α) >>= f) = f a := rfl

/-- Characterization of a successful `Option` bind. -/
theorem option_bind_eq_some {α β : Type} (x : Option α) (f : α → Option β) (b : β) :
    (x >>= f = some b) ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

theorem i64_beq_of_eq {a b : I64} (h : a = b) : (a == b) = true := by simp [h]

theorem i64_zero_val : (0 : I64).val = 0 := rfl

theorem memoryLinearIndexing_proven : MemoryLinearIndexing := fun _ => rfl

theorem memoryIndexIsOneBased_proven : MemoryIndexIsOneBased := by
  intro _M _P _memoryrefoffset _length _ref h1 h2
  exact ⟨h1, h2⟩

theorem memoryIsassignedBounds_proven : MemoryIsassignedBounds := by
  constructor
  · intro M P T V ops a i hcb
    simp [isassignedMemory, hcb]
  · intro M P T V ops ref assigned h
    simp [isassignedRef, h]

theorem genericMemoryCheckedAccessesInBounds_proven : GenericMemoryCheckedAccessesInBounds := by
  constructor
  · intro M P T D S N I Ptr Token copy dest src n hzero hcheck
    simp [unsafeCopytoRefs, hzero, hcheck]
  · intro M P T I copy checkbounds rangeLength rangeFirst shapeCheck a x indices hcb
    simp [setindexMemoryRange, hcb]

theorem memoryUnsetReturnsTarget_proven : MemoryUnsetReturnsTarget := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M P T V ops ref h
    simp [unsetindexRef, h]
  · intro M P T V ops a i ref h1 h2
    simp [unsetindexMemoryInt, unsetindexRef, h1, h2]
  · intro M P T V I ops toIndex unsetArray a i index ref h1 h2 h3
    simp [unsetindexUnionInteger, unsetindexMemoryInt, unsetindexRef, h1, h2, h3]
  · intro M P T V ops ref h
    cases hu : ops.memoryrefUnset ref MemoryOrder.notAtomic true with
    | none => rw [hu] at h; simp at h
    | some w =>
      rw [hu] at h
      simp only [unsetindexRef] at ⊢
      rw [hu] at ⊢
      simp only [bind_some_shift, bind_pure_shift] at h ⊢
      rw [h]
      rfl
  · intro M P T V ops a i h
    simp only [unsetindexMemoryInt]
    cases ha : ops.memoryrefAt a i with
    | none => rw [ha] at h; simp at h
    | some w =>
      rw [ha] at h
      simp only [bind_some_shift] at h ⊢
      simp only [unsetindexRef] at ⊢
      cases hu : ops.memoryrefUnset w MemoryOrder.notAtomic true with
      | none => rw [hu] at h; simp at h
      | some u =>
        rw [hu] at h
        simp only [bind_some_shift] at h
        simp only [bind_some_shift, bind_pure_shift]
        rw [h]
  · intro A I P T V ops toIndex unsetArray isassignedArray array i index h1 h2
    have h1' : toIndex i = some index := h1
    simp only [unsetindexUnionInteger]
    rw [h1']
    simp only [bind_some_shift]
    cases hu : unsetArray array index with
    | none => rw [hu] at h2; simp at h2
    | some u =>
      rw [hu] at h2
      simp only [bind_some_shift] at h2
      simp only [bind_some_shift, bind_pure_shift]
      rw [h2]

theorem atomicMemoryUnsetReturnsReference_proven : AtomicMemoryUnsetReturnsReference := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M P T V ops ref order h
    simp [unsetindexAtomicRef, h]
  · intro M P T V ops a i ref order h1 h2
    simp [unsetindexAtomicMemoryInt, unsetindexAtomicRef, h1, h2]
  · intro M P T V I ops toIndex a i index ref order h1 h2 h3
    simp [unsetindexAtomicMemoryInteger, unsetindexAtomicMemoryInt, unsetindexAtomicRef, h1, h2, h3]
  · intro M P T V ops ref order h
    cases hu : ops.memoryrefUnset ref order true with
    | none => rw [hu] at h; simp at h
    | some w =>
      rw [hu] at h
      simp only [unsetindexAtomicRef] at ⊢
      rw [hu] at ⊢
      simp only [bind_some_shift, bind_pure_shift] at h ⊢
      rw [h]
      rfl
  · intro M P T V ops a i order h
    simp only [unsetindexAtomicMemoryInt]
    cases ha : ops.memoryrefAt a i with
    | none => rw [ha] at h; simp at h
    | some w =>
      rw [ha] at h
      simp only [bind_some_shift] at h ⊢
      simp only [unsetindexAtomicRef] at ⊢
      cases hu : ops.memoryrefUnset w order true with
      | none => rw [hu] at h; simp at h
      | some u =>
        rw [hu] at h
        simp only [bind_some_shift] at h
        simp only [bind_some_shift, bind_pure_shift]
        rw [h]
  · intro M P T V I ops toIndex a i index order h1 h2
    have h1' : toIndex i = some index := h1
    simp only [unsetindexAtomicMemoryInteger, unsetindexAtomicMemoryInt]
    rw [h1']
    simp only [bind_some_shift]
    cases ha : ops.memoryrefAt a index with
    | none => rw [ha] at h2; simp at h2
    | some w =>
      rw [ha] at h2
      simp only [bind_some_shift] at h2 ⊢
      simp only [unsetindexAtomicRef] at ⊢
      cases hu : ops.memoryrefUnset w order true with
      | none => rw [hu] at h2; simp at h2
      | some u =>
        rw [hu] at h2
        simp only [bind_some_shift] at h2
        simp only [bind_some_shift, bind_pure_shift]
        rw [h2]

/-- The typed memory-copy route returns its destination argument whenever it succeeds. -/
theorem unsafeCopytoMemoryTyped_dest {M P T D S N I Ptr Token : Type}
    (copy : MemoryCopyOps Option M P D S N I Ptr Token) (boundsChecking : Bool)
    (dest : M) (doffs : D) (src : M) (soffs : S) (n : N) (x : M)
    (h : unsafeCopytoMemoryTyped (T := T) copy boundsChecking dest doffs src soffs n = some x) :
    x = dest := by
  unfold unsafeCopytoMemoryTyped at h
  split at h
  · simp at h
    exact h.symm
  · simp only [option_bind_eq_some] at h
    obtain ⟨d', -, h⟩ := h
    obtain ⟨s', -, h⟩ := h
    obtain ⟨c', -, h⟩ := h
    simp at h
    exact h.symm

theorem memoryCopyPreservesExtent_proven : MemoryCopyPreservesExtent := by
  intro M P T Ptr Token copy length construct sameStorage a result n hlen hlaw hcopy
  unfold copyMemory at hcopy
  rw [hlen] at hcopy
  simp only [bind_some_shift] at hcopy
  obtain ⟨nm, hnmc, hty⟩ := (option_bind_eq_some _ _ _).mp hcopy
  obtain ⟨hl, hs⟩ := hlaw nm hnmc
  rw [unsafeCopytoMemoryTyped_dest copy false nm 1 a 1 n result hty]
  exact ⟨hl, hs⟩

theorem similarMemoryPreservesExtent_proven : SimilarMemoryPreservesExtent := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M length construct a result n h1 h2 _
    simp [similarMemory, h1, h2]
  · intro M R length construct a result elementType n h1 h2
    simp [similarMemoryElementType, h1, h2]
  · intro M construct a result n h
    simp [similarMemoryLength, h]
  · intro M R D construct firstDim a elementType dims result n h1 h2
    simp [similarMemoryElementDims, h1, h2]
  · intro M D construct firstDim a result dims n h1 h2
    simp [similarMemoryDims, h1, h2]

theorem byteMemoryFillUsesConvertedValue_proven : ByteMemoryFillUsesConvertedValue := by
  constructor
  · intro M P X U USize Token elementType _isInteger castElement convert preserveBegin preserveEnd
      unsafeConvert memset lengthModUInt a x _iprf value size ptr token
      hcast hpb huc hlen hmemset hpe
    simp [fillByteMemory, hcast, hpb, huc, hlen, hmemset, hpe]
  · intro M P X U USize Token elementType _isInteger castElement convert preserveBegin preserveEnd
      unsafeConvert memset lengthModUInt a x _iprf value size ptr token
      hcast hconv hpb huc hlen hmemset hpe
    simp [fillByteMemory, hcast, hconv, hpb, huc, hlen, hmemset, hpe]

theorem memoryConversionAndPromotion_proven : MemoryConversionAndPromotion := by
  refine ⟨?_, ?_, ?_⟩
  · intro M A asTarget construct a memory h
    simp [convertMemory, h]
  · intro M A asTarget construct a memory h
    simp [convertMemory, h]
  · intro R promoteType elSame T S
    rfl

theorem memoryArrayConstructorCopies_proven : MemoryArrayConstructorCopies := by
  intro M A D size constructUndef copytoAxcheck x n destination hsize hcon
  simp [memoryFromArray, hsize, hcon]

theorem memoryRangeGetindexChecksBounds_proven : MemoryRangeGetindexChecksBounds := by
  refine ⟨?_, ?_, ?_⟩
  · intro M I construct copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex a indices hcb
    simp [getindexMemoryRange, hcb]
  · intro M I construct copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex a result
      indices start span dims first hcb hspan hpos haxes hcon hfi hfirst hcopy
    have hspanpos : (0 : I64) < span := hpos
    simp [getindexMemoryRange, similarMemoryDims, copytoMemoryOffsets, hcb, hspan, haxes, hcon,
      hfi, hfirst, hcopy, hspanpos]
  · intro M I J construct copyImpl checkbounds rangeLength rangeAxes rangeFirst firstindex toIndex
      a result range indices hto
    simp [getindexMemoryBoolRange, hto]

theorem memoryScalarSetindexReturnsTarget_proven : MemoryScalarSetindexReturnsTarget := by
  refine ⟨?_, ?_⟩
  · intro M P T V ops a value i stored base ref hcast hcb href hnew hset
    simp [setindexMemory, setindexMemoryRaw, hcast, hcb, href, hnew, hset]
  · intro M P T V ops throwBounds a value i1 i2 indices hi2 hall
    have hguard : (i2 == 1 && indices.all (fun i => i == 1)) = true := by
      rw [i64_beq_of_eq hi2, hall, Bool.and_self]
    simp only [setindexMemoryCartesian]
    rw [hguard]
    simp

theorem memoryBulkSetindexChecksShape_proven : MemoryBulkSetindexChecksShape := by
  refine ⟨?_, ?_⟩
  · intro M P T I copy checkbounds rangeLength rangeFirst shapeCheck a x indices span hrl hshape
    simp only [setindexMemoryRange]
    cases hc : checkbounds a indices with
    | none => simp
    | some _ => simp [hrl, hshape]
  · intro M P T copy length shapeCheck a x span hlen hshape
    simp [setindexMemoryColon, hlen, hshape]

theorem byteMemoryComparisonOrdersPrefix_proven : ByteMemoryComparisonOrdersPrefix := by
  intro M Ptr Tok length gcPreserveBegin gcPreserveEnd unsafeConvert memcmp cmpLength a b c pa pb
    la lb ta tb hla hlb hta htb hpa hpb hpea hpeb hmem
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    simp [cmpByteMemory, hla, hlb, hta, htb, hpa, hpb, hpea, hpeb, hmem, hc]
  · intro hc
    have hcpos : 0 < c.val := hc
    have hneg : ¬(c < 0) := by
      show ¬(c.val < (0 : I64).val)
      rw [i64_zero_val]
      omega
    simp [cmpByteMemory, hla, hlb, hta, htb, hpa, hpb, hpea, hpeb, hmem, hc, hneg]
  · intro hc
    have hcval : c.val = 0 := by rw [hc, i64_zero_val]
    have hneg1 : ¬(c < 0) := by
      show ¬(c.val < (0 : I64).val)
      rw [i64_zero_val]
      omega
    have hneg2 : ¬(0 < c) := by
      show ¬((0 : I64).val < c.val)
      rw [i64_zero_val]
      omega
    simp [cmpByteMemory, hla, hlb, hta, htb, hpa, hpb, hpea, hpeb, hmem, hneg1, hneg2]

theorem bitIntegerMemoryEqualityRequiresEqualLengths_proven :
    BitIntegerMemoryEqualityRequiresEqualLengths := by
  intro M Ptr Tok length gcPreserveBegin gcPreserveEnd unsafeConvert sizeofElement elementType
    memcmp a b la lb hla hlb
  refine ⟨?_, ?_⟩
  · intro hne
    have hneval : ¬(la.val = lb.val) := fun h => hne (Subtype.ext h)
    simp [equalBitIntegerMemory, hla, hlb, hneval]
  · intro c pa pb ta tb hle hta htb hpa hpb hpea hpeb hmem
    rw [hle] at hmem
    simp [equalBitIntegerMemory, hla, hlb, hle, hta, htb, hpa, hpb, hpea, hpeb, hmem,
      i64_zero_val]

theorem memoryFindallUsesSortedSearch_proven : MemoryFindallUsesSortedSearch := by
  refine ⟨?_, ?_, ?_⟩
  · intro M X R issortedMemory issortedNeedle sortedFindin findin pred x result h1 h2 h3
    simp [findallMemory, h1, h2, h3]
  · intro M X R issortedMemory issortedNeedle sortedFindin findin pred x result h1 h2
    simp [findallMemory, h1, h2]
  · intro M X R issortedMemory issortedNeedle sortedFindin findin pred x result h1 h2 h3
    simp [findallMemory, h1, h2, h3]

theorem mapM_loop_nil {α β : Type} (f : α → Option β) (acc : List β) :
    List.mapM.loop f [] acc = pure acc.reverse := rfl

theorem mapM_loop_cons {α β : Type} (f : α → Option β) (x : α) (l : List α) (acc : List β) :
    List.mapM.loop f (x :: l) acc = (f x) >>= fun b => List.mapM.loop f l (b :: acc) := rfl

theorem mapM_cons {α β : Type} (f : α → Option β) (x : α) (l : List α) :
    List.mapM f (x :: l) = (f x) >>= fun b => List.mapM.loop f l [b] := rfl

theorem mapM_len_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ys.length = l.length := by
  have loop_len : ∀ (l : List α) (acc ys : List β), List.mapM.loop f l acc = some ys →
      ys.length = l.length + acc.length := by
    intro l
    induction l with
    | nil =>
      intro acc ys h
      rw [mapM_loop_nil] at h
      simp at h
      rw [← h]
      simp
    | cons x l ih =>
      intro acc ys h
      rw [mapM_loop_cons] at h
      obtain ⟨b, -, h⟩ := (option_bind_eq_some _ _ _).mp h
      have hprev := ih (b :: acc) ys h
      simp only [List.length_cons] at hprev ⊢
      omega
  intro l ys h
  cases l with
  | nil => simpa using h
  | cons x l =>
    rw [mapM_cons] at h
    obtain ⟨b, -, h⟩ := (option_bind_eq_some _ _ _).mp h
    have hres := loop_len l [b] ys h
    simp only [List.length_cons, List.length_nil] at hres ⊢
    omega

theorem memoryIndcopyKeepsDimensionRegions_proven : MemoryIndcopyKeepsDimensionRegions := by
  intro M X Y Vector sizeAt sizeLength rangeFromTo oneRange addInt mulInt length getindex findin
    subindex toVector vectorLength sz indices dst src n hlen hpos htov hrun
  obtain ⟨positions, hposr, hposlen⟩ := hpos
  simp only [indcopy] at hrun
  rw [hlen] at hrun
  simp only [bind_some_shift] at hrun
  obtain ⟨s₀, -, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨lo, -, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨ls, -, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨s₁, -, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  rw [hposr] at hrun
  simp only [bind_some_shift] at hrun
  obtain ⟨dstL, hdstL, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨srcL, hsrcL, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨dv, hdv, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  obtain ⟨sv, hsv, hrun⟩ := (option_bind_eq_some _ _ _).mp hrun
  simp at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  exact ⟨by rw [htov dstL dv hdv, mapM_len_some _ positions dstL hdstL, hposlen],
         by rw [htov srcL sv hsv, mapM_len_some _ positions srcL hsrcL, hposlen]⟩

theorem atomicMemoryOperationsPreserveOrdering_proven : AtomicMemoryOperationsPreserveOrdering := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M P V memoryrefAt memoryrefGet mem order i ref value
    intro href hget
    simp [getindexAtomic, href, hget]
  · intro M P T V R memoryrefAt castElement convert memoryrefSet mem order input i ref value result
    intro href hcast hset
    simp [setindexAtomic, href, hcast, hset]
  · intro M P Op V R memoryrefAt memoryrefModify mem order op value i ref result
    intro href hmod
    simp [modifyindexAtomic, href, hmod]
  · intro M P T V R memoryrefAt castElement convert memoryrefSetOnce mem successOrder failOrder
      input i ref value result
    intro href hcast hset
    simp [setindexonceAtomic, href, hcast, hset]
  · intro M P T V R memoryrefAt castElement convert memoryrefSwap mem order input i ref value result
    intro href hcast hset
    simp [swapindexAtomic, href, hcast, hset]
  · intro M P T E V R memoryrefAt castElement convert memoryrefReplace mem successOrder failOrder
      expected input i ref value result
    intro href hcast hset
    simp [replaceindexAtomic, href, hcast, hset]

def entries : List Entry :=
  [ { id := "genericmemory-linear-indexing", juliaFile := "base/genericmemory.jl",
      juliaFns := ["IndexStyle(::Type{<:GenericMemory})"],
      statement := "GenericMemory uses the linear indexing style promised by its DenseVector interface.",
      source := "base/genericmemory.jl:6-8,64", status := .proven,
      prop := ``MemoryLinearIndexing, thm := some ``memoryLinearIndexing_proven }
  , { id := "genericmemory-memoryindex-one-based", juliaFile := "base/genericmemory.jl",
      juliaFns := ["memoryindex(::GenericMemoryRef)"],
      statement := "A valid GenericMemoryRef reports a one-based index within its backing memory.",
      source := "memoryindex docstring; base/genericmemory.jl:68-87", status := .proven,
      prop := ``MemoryIndexIsOneBased, thm := some ``memoryIndexIsOneBased_proven }
  , { id := "genericmemory-isassigned-bounds", juliaFile := "base/genericmemory.jl",
      juliaFns := ["isassigned(::GenericMemory, ::Int)", "isassigned(::GenericMemoryRef)"],
      statement := "A checked isassigned query returns false for an index outside the memory and queries initialization for an in-bounds reference.",
      source := "base/genericmemory.jl:188-195; uninitialized-memory manual", status := .proven,
      prop := ``MemoryIsassignedBounds, thm := some ``memoryIsassignedBounds_proven }
  , { id := "memsafety-genericmemory-checked-callers", juliaFile := "base/genericmemory.jl",
      juliaFns := ["isassigned(::GenericMemory, i)", "copy(::Memory)",
        "setindex!(::Memory, ::Memory, ::AbstractUnitRange)",
        "setindex!(::Memory, ::Memory, ::Colon)"],
      statement := "Checked assignment queries return false outside the memory, and bounds-checked copying and range assignment stop before an invalid access.",
      source := "computed checks and loop bounds; base/genericmemory.jl:188-192,257-262,345-363",
      status := .proven, prop := ``GenericMemoryCheckedAccessesInBounds, thm := some ``genericMemoryCheckedAccessesInBounds_proven }
  , { id := "genericmemory-unsetindex-semantics", juliaFile := "base/genericmemory.jl",
      juliaFns := ["unsetindex!(::MemoryRef)", "unsetindex!(::Memory, ::Int)",
        "unsetindex!(::Union{Array,Memory}, ::Integer)"],
      statement := "Unsetting a memory reference leaves its slot unassigned and returns the same reference or memory object.",
      source := "unsetindex! docstrings; base/genericmemory.jl:91-149", status := .proven,
      prop := ``MemoryUnsetReturnsTarget, thm := some ``memoryUnsetReturnsTarget_proven }
  , { id := "genericmemory-atomic-unset-order", juliaFile := "base/genericmemory.jl",
      juliaFns := ["unsetindex_atomic!(::AtomicMemoryRef)", "unsetindex_atomic!(::AtomicMemory, ::Symbol, ::Int)",
        "unsetindex_atomic!(::AtomicMemory, ::Symbol, ::Integer)"],
      statement := "Atomic unsetting leaves the slot unassigned, uses the requested ordering, and returns the same reference or memory object.",
      source := "unsetindex_atomic! docstrings; base/genericmemory.jl:151-183", status := .proven,
      prop := ``AtomicMemoryUnsetReturnsReference, thm := some ``atomicMemoryUnsetReturnsReference_proven }
  , { id := "genericmemory-copy-content", juliaFile := "base/genericmemory.jl",
      juliaFns := ["unsafe_copyto!(::MemoryRef{T}, ::MemoryRef{T}, n)",
        "unsafe_copyto!(::GenericMemoryRef, ::GenericMemoryRef, n)",
        "unsafe_copyto!(::Memory{T}, doffs, ::Memory{T}, soffs, n)",
        "unsafe_copyto!(::Memory, doffs, ::Memory, soffs, n)", "copy(::Memory)"],
      statement := "Unsafe copy preserves source slots, including undefined slots, across overlapping ranges; fallback copy converts defined elements to the destination type.",
      source := "base/genericmemory.jl:197-263; copy semantics", status := .todo,
      prop := ``MemoryCopyPreservesContents }
  , { id := "genericmemory-copy-extent", juliaFile := "base/genericmemory.jl",
      juliaFns := ["copy(::Memory)"],
      statement := "copy(::Memory) creates independent storage with the source element count.",
      source := "copy docstring; base/genericmemory.jl:257-263", status := .proven,
      prop := ``MemoryCopyPreservesExtent, thm := some ``memoryCopyPreservesExtent_proven }
  , { id := "genericmemory-similar-extent", juliaFile := "base/genericmemory.jl",
      juliaFns := ["similar(::GenericMemory)", "similar(::GenericMemory, ::Type)",
        "similar(::GenericMemory, ::Int)", "similar(::GenericMemory, ::Type, ::Dims{1})",
        "similar(::GenericMemory, ::Dims{1})"],
      statement := "similar preserves the memory kind and address space and allocates the requested one-dimensional element count.",
      source := "similar docstrings and constructors; base/genericmemory.jl:270-281", status := .proven,
      prop := ``SimilarMemoryPreservesExtent, thm := some ``similarMemoryPreservesExtent_proven }
  , { id := "genericmemory-byte-fill", juliaFile := "base/genericmemory.jl",
      juliaFns := ["fill!(::Union{Memory{UInt8},Memory{Int8}}, ::Integer)"],
      statement := "Byte-memory fill converts the integer to the element type and fills every slot with that value.",
      source := "fill! contract; base/genericmemory.jl:283-291", status := .proven,
      prop := ``ByteMemoryFillUsesConvertedValue, thm := some ``byteMemoryFillUsesConvertedValue_proven }
  , { id := "genericmemory-convert-promote", juliaFile := "base/genericmemory.jl",
      juliaFns := ["convert(::Type{<:Memory}, ::AbstractArray)",
        "promote_rule(::Type{Memory{T}}, ::Type{Memory{S}})"],
      statement := "Conversion reuses an array already of the requested Memory type; promotion applies the element-type promotion rule to both Memory element types.",
      source := "base/genericmemory.jl:292-296", status := .proven,
      prop := ``MemoryConversionAndPromotion, thm := some ``memoryConversionAndPromotion_proven }
  , { id := "genericmemory-array-constructor-copy", juliaFile := "base/genericmemory.jl",
      juliaFns := ["Memory{T}(::AbstractArray{S,1})"],
      statement := "Constructing Memory from a one-dimensional array checks axes and copies its values.",
      source := "constructor comment; base/genericmemory.jl:298-301", status := .proven,
      prop := ``MemoryArrayConstructorCopies, thm := some ``memoryArrayConstructorCopies_proven }
  , { id := "genericmemory-range-getindex", juliaFile := "base/genericmemory.jl",
      juliaFns := ["getindex(::Memory, ::AbstractUnitRange{<:Integer})",
        "getindex(::Memory, ::AbstractUnitRange{Bool})"],
      statement := "Range indexing checks bounds and returns a copied slice; Bool ranges are converted to valid indices.",
      source := "base/genericmemory.jl:305-322", status := .proven,
      prop := ``MemoryRangeGetindexChecksBounds, thm := some ``memoryRangeGetindexChecksBounds_proven }
  , { id := "genericmemory-setindex-semantics", juliaFile := "base/genericmemory.jl",
      juliaFns := ["_setindex!(::Memory{T}, ::T, ::Int)", "setindex!(::Memory{T}, x, ::Int)",
        "setindex!(::Memory{T}, x, ::Int, ::Int, ::Int...)",
        "setindex!(::Memory{T}, ::Memory{T}, ::AbstractUnitRange{Int})",
        "setindex!(::Memory{T}, ::Memory{T}, ::Colon)"],
      statement := "Scalar setindex converts to the element type and checks bounds; Cartesian scalar and bulk assignments check their indices and source shape.",
      source := "base/genericmemory.jl:324-364", status := .proven,
      prop := ``MemoryScalarSetindexReturnsTarget, thm := some ``memoryScalarSetindexReturnsTarget_proven }
  , { id := "genericmemory-bulk-setindex-shape", juliaFile := "base/genericmemory.jl",
      juliaFns := ["setindex!(::Memory{T}, ::Memory{T}, ::AbstractUnitRange{Int})",
        "setindex!(::Memory{T}, ::Memory{T}, ::Colon)"],
      statement := "Range and colon assignment reject source memories whose lengths differ from the selected target shape.",
      source := "base/genericmemory.jl:345-364", status := .proven,
      prop := ``MemoryBulkSetindexChecksShape, thm := some ``memoryBulkSetindexChecksShape_proven }
  , { id := "genericmemory-byte-comparison", juliaFile := "base/genericmemory.jl",
      juliaFns := ["cmp(::Memory{UInt8}, ::Memory{UInt8})"],
      statement := "Byte-memory comparison follows lexicographic byte order, with memory length deciding ties after an equal prefix.",
      source := "base/genericmemory.jl:366-393", status := .proven,
      prop := ``ByteMemoryComparisonOrdersPrefix, thm := some ``byteMemoryComparisonOrdersPrefix_proven }
  , { id := "genericmemory-equal-bitinteger-memory", juliaFile := "base/genericmemory.jl",
      juliaFns := ["==(a::M, b::M) where {M <: BitIntegerMemory}"],
      statement := "BitIntegerMemory values of different lengths compare unequal; equal-length values compare all stored bytes.",
      source := "base/genericmemory.jl:378-393", status := .proven,
      prop := ``BitIntegerMemoryEqualityRequiresEqualLengths, thm := some ``bitIntegerMemoryEqualityRequiresEqualLengths_proven }
  , { id := "genericmemory-sorted-findall", juliaFile := "base/genericmemory.jl",
      juliaFns := ["findall(::Fix2{typeof(in),<:Union{Memory{<:Real},Real}}, ::Memory{<:Real})"],
      statement := "Sorted values and sorted search values use the sorted-search path; other inputs use general membership search.",
      source := "base/genericmemory.jl:395-401", status := .proven,
      prop := ``MemoryFindallUsesSortedSearch, thm := some ``memoryFindallUsesSortedSearch_proven }
  , { id := "genericmemory-indcopy-regions", juliaFile := "base/genericmemory.jl",
      juliaFns := ["indcopy(::Dims, ::GenericMemory)"],
      statement := "indcopy returns one destination and one source index for each element of its GenericMemory index input.",
      source := "base/genericmemory.jl:403-413", status := .proven,
      prop := ``MemoryIndcopyKeepsDimensionRegions, thm := some ``memoryIndcopyKeepsDimensionRegions_proven }
  , { id := "genericmemory-atomic-ordering", juliaFile := "base/genericmemory.jl",
      juliaFns := ["getindex_atomic(::GenericMemory, ::Symbol, ::Int)",
        "setindex_atomic!(::GenericMemory, ::Symbol, value, ::Int)",
        "setindexonce_atomic!(::GenericMemory, ::Symbol, ::Symbol, value, ::Int)",
        "modifyindex_atomic!(::GenericMemory, ::Symbol, op, value, ::Int)",
        "swapindex_atomic!(::GenericMemory, ::Symbol, value, ::Int)",
        "replaceindex_atomic!(::GenericMemory, ::Symbol, ::Symbol, expected, desired, ::Int)"],
      statement := "Atomic memory operations use the supplied memory ordering and perform each requested get, set, once-set, modification, swap or replacement atomically.",
      source := "Atomic Operations manual; base/genericmemory.jl:415-490", status := .proven,
      prop := ``AtomicMemoryOperationsPreserveOrdering, thm := some ``atomicMemoryOperationsPreserveOrdering_proven }
  ]

/-! Method -> property coverage. Pure forwarding/plumbing methods are listed above. -/
/-!
64 -> genericmemory-linear-indexing
66 -> Nothing to promise
87 -> genericmemory-memoryindex-one-based
89 -> Nothing to promise
119,148,149 -> genericmemory-unsetindex-semantics
160,175,181 -> genericmemory-atomic-unset-order
185,186 -> Nothing to promise
189,195 -> genericmemory-isassigned-bounds; memsafety-genericmemory-checked-callers
198,216,223,230,257 -> genericmemory-copy-content; genericmemory-copy-extent; memsafety-genericmemory-checked-callers
272,274,276,278,280 -> genericmemory-similar-extent
283 -> genericmemory-byte-fill
294,296 -> genericmemory-convert-promote
265,266 -> Nothing to promise
301 -> genericmemory-array-constructor-copy
308,320 -> genericmemory-range-getindex
322 -> Nothing to promise
326,333,339 -> genericmemory-setindex-semantics
346,356 -> genericmemory-setindex-semantics; genericmemory-bulk-setindex-shape;
          memsafety-genericmemory-checked-callers
367 -> genericmemory-byte-comparison
380 -> genericmemory-equal-bitinteger-memory
395 -> genericmemory-sorted-findall
404 -> genericmemory-indcopy-regions
416,422,434,453,459,471 -> genericmemory-atomic-ordering
-/

end JuliaLean.Proofs.base.genericmemory
