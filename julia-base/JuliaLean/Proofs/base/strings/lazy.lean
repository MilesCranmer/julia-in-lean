import JuliaLean.base.strings.lazy
import JuliaLean.Registry.Types

/-!
# Properties of `base/strings/lazy.jl`

Specifications for the lazy string model bound to the installed models. A lazy string is a heap
object (`LazyHeap`, `lazyFields`) holding the `@atomic str` cache, with its `parts` and `compact`
fields. Statements run the bound methods over the concrete heap `lazyFields`; the forwarding methods
are stated against the installed `String` models.
-/

namespace JuliaLean.Proofs.base.strings.lazy

open JuliaLean JuliaLean.base.strings.lazy JuliaLean.Registry

/-- The public constructor retains every part and the compact flag, and the new object's `str` cell
holds `nothing`. -/
def CtorProperty : Prop :=
  ∀ {E V : Type} (parts : List (LazyPart E V)) (compact : Bool) (heap : LazyHeap),
    ∃ (l : LazyString CellRef E V) (heap' : LazyHeap),
      lazyStringCtor lazyFields parts compact heap = some (.ok (l, heap')) ∧
      l.parts = parts ∧ l.compact = compact ∧
      lazyFields.getfield l.ref .acquire heap' = some (.ok (none, heap'))

/-- `_LazyString(parts, str)` stores the given cache and sets compact to false (arguments already of
the field types). -/
def PrivateCtorProperty : Prop :=
  ∀ {E V : Type} (parts : List (LazyPart E V)) (str : Option JString) (heap : LazyHeap),
    ∃ (l : LazyString CellRef E V) (heap' : LazyHeap),
      _LazyString lazyFields parts str heap = some (.ok (l, heap')) ∧
      l.parts = parts ∧ l.compact = false ∧
      lazyFields.getfield l.ref .acquire heap' = some (.ok (str, heap'))

/-- A successful conversion of a lazy string whose parts are Strings returns their bytes left to
right and stores that String in the cache. -/
def MaterializationContract : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (strs : List JString) (compact : Bool) (heap : LazyHeap)
    (l : LazyString CellRef E V) (heap₁ : LazyHeap) (result : JString) (heap₂ : LazyHeap),
    lazyStringCtor lazyFields
      (strs.map (fun s => (JuliaLean.base.strings.io.StrArg.string s : LazyPart E V))) compact heap =
        some (.ok (l, heap₁)) →
    toString lazyFields c displaySize a l heap₁ = some (.ok (result, heap₂)) →
      result.bytes = (strs.map (·.bytes)).flatten ∧
      lazyFields.getfield l.ref .acquire heap₂ = some (.ok (some result, heap₂))

/-- A successful conversion caches its String, so a later conversion returns the same String and
leaves the heap unchanged. -/
def ToStringProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V) (heap : LazyHeap)
    (str : JString) (heap₁ : LazyHeap),
    toString lazyFields c displaySize a l heap = some (.ok (str, heap₁)) →
      lazyFields.getfield l.ref .acquire heap₁ = some (.ok (some str, heap₁)) ∧
      toString lazyFields c displaySize a l heap₁ = some (.ok (str, heap₁))

/-- `m` is `String(l)` followed by `k` on the String: a failed conversion's error is returned with the
heap at the failure, otherwise `k` runs on the result (a `k` error keeps the converted heap). -/
def Forwards {E V Ty α : Type} (c : JuliaLean.base.intfuncs.DigitCallees)
    (displaySize : JInt64 × JInt64) (a : JuliaLean.base.show.AnyOps V Ty)
    (l : LazyString CellRef E V) (k : JString → Except (LazyError E) α)
    (m : M LazyHeap E α) : Prop :=
  ∀ heap : LazyHeap,
    (∀ (str : JString) (heap₁ : LazyHeap),
      toString lazyFields c displaySize a l heap = some (.ok (str, heap₁)) →
      m heap = some (match k str with
        | .ok x => .ok (x, heap₁)
        | .error e => .error (e, heap₁))) ∧
    (∀ (e : LazyError E) (heap₁ : LazyHeap),
      toString lazyFields c displaySize a l heap = some (.error (e, heap₁)) →
      m heap = some (.error (e, heap₁)))

/-- `hash(::LazyString, h)` is the String hash of its String with the same seed. -/
def HashProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (seed : JuliaLean.base.hashing.Word),
    Forwards c displaySize a l (fun str => .ok (JuliaLean.Bindings.base.hashing.hashStringBound str seed))
      (hash lazyFields c displaySize a l seed)

/-- A lazy string has the last index of its String. -/
def LastindexProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V),
    Forwards c displaySize a l
      (fun str => (JuliaLean.base.strings.string.lastindexString
        JuliaLean.base.strings.string.stringNcodeunits
        JuliaLean.base.strings.string.stringBetweenIndex
        JuliaLean.base.strings.string.stringBetweenByte
        JuliaLean.base.strings.string.stringCodeunitAt str).mapError LazyError.string)
      (lastindex lazyFields c displaySize a l)

/-- The first iteration result of a lazy string is the first result of its String. -/
def Iterate0Property : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V),
    Forwards c displaySize a l
      (fun str => .ok (JuliaLean.base.strings.string.stringIterate str
        (JuliaLean.base.strings.string.stringFirstindex str)))
      (iterate0 lazyFields c displaySize a l)

/-- Iteration at an index converts it with `Int(i)` after `String(l)` and iterates the String there, for
`BitInteger`, `Bool` and `BigInt` indices. -/
def IterateAtProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V),
    (∀ (t : IntTy) (i : JInt t),
      Forwards c displaySize a l
        (fun str => (bitIntegerIndex (E := E) t i).map
          (JuliaLean.base.strings.string.stringIterate str))
        (iterateAt lazyFields c displaySize a (bitIntegerIndex (E := E) t) l i)) ∧
    (∀ i : Bool,
      Forwards c displaySize a l
        (fun str => (boolIndex (E := E) i).map (JuliaLean.base.strings.string.stringIterate str))
        (iterateAt lazyFields c displaySize a (boolIndex (E := E)) l i)) ∧
    (∀ i : JuliaLean.base.gmp.BigInt,
      Forwards c displaySize a l
        (fun str => (bigIntIndex (E := E) i).map (JuliaLean.base.strings.string.stringIterate str))
        (iterateAt lazyFields c displaySize a (bigIntIndex (E := E)) l i))

/-- `isequal` converts left then right and applies String equality; an error stops at the first
failing conversion. -/
def IsequalProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (x y : LazyString CellRef E V) (heap : LazyHeap),
    (∀ (e : LazyError E) (heap₁ : LazyHeap),
      toString lazyFields c displaySize a x heap = some (.error (e, heap₁)) →
      isequal lazyFields c displaySize a x y heap = some (.error (e, heap₁))) ∧
    (∀ (s₁ : JString) (heap₁ : LazyHeap) (e : LazyError E) (heap₂ : LazyHeap),
      toString lazyFields c displaySize a x heap = some (.ok (s₁, heap₁)) →
      toString lazyFields c displaySize a y heap₁ = some (.error (e, heap₂)) →
      isequal lazyFields c displaySize a x y heap = some (.error (e, heap₂))) ∧
    (∀ (s₁ : JString) (heap₁ : LazyHeap) (s₂ : JString) (heap₂ : LazyHeap),
      toString lazyFields c displaySize a x heap = some (.ok (s₁, heap₁)) →
      toString lazyFields c displaySize a y heap₁ = some (.ok (s₂, heap₂)) →
      isequal lazyFields c displaySize a x y heap =
        some (.ok (JuliaLean.base.operators.isequalDefault
          (JuliaLean.base.strings.string.eqString identicalString) s₁ s₂, heap₂)))

/-- `==` converts left then right and applies String equality; an error stops at the first failing
conversion. -/
def EqProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (x y : LazyString CellRef E V) (heap : LazyHeap),
    (∀ (e : LazyError E) (heap₁ : LazyHeap),
      toString lazyFields c displaySize a x heap = some (.error (e, heap₁)) →
      eq lazyFields c displaySize a x y heap = some (.error (e, heap₁))) ∧
    (∀ (s₁ : JString) (heap₁ : LazyHeap) (e : LazyError E) (heap₂ : LazyHeap),
      toString lazyFields c displaySize a x heap = some (.ok (s₁, heap₁)) →
      toString lazyFields c displaySize a y heap₁ = some (.error (e, heap₂)) →
      eq lazyFields c displaySize a x y heap = some (.error (e, heap₂))) ∧
    (∀ (s₁ : JString) (heap₁ : LazyHeap) (s₂ : JString) (heap₂ : LazyHeap),
      toString lazyFields c displaySize a x heap = some (.ok (s₁, heap₁)) →
      toString lazyFields c displaySize a y heap₁ = some (.ok (s₂, heap₂)) →
      eq lazyFields c displaySize a x y heap =
        some (.ok (JuliaLean.base.strings.string.eqString identicalString s₁ s₂, heap₂)))

/-- A lazy string's code-unit count is that of its String. -/
def NcodeunitsProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V),
    Forwards c displaySize a l (fun str => .ok (JuliaLean.base.strings.string.stringNcodeunits str))
      (ncodeunits lazyFields c displaySize a l)

/-- `codeunit(::LazyString)` is the code-unit type of the empty String (`UInt8`), without forcing the
lazy string. -/
def CodeunitTypeProperty : Prop :=
  ∀ {Ref E V : Type} (l : LazyString Ref E V),
    codeunitType l = JuliaLean.base.strings.string.codeunitType ∧ codeunitType l = UInt8

/-- Indexed code-unit reads convert the index with `Int(i)` after `String(l)` and read the String
there with `@boundscheck`, for `BitInteger`, `Bool` and `BigInt` indices. -/
def CodeunitAtProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V),
    (∀ (t : IntTy) (i : JInt t),
      Forwards c displaySize a l
        (fun str => do
          let index ← bitIntegerIndex (E := E) t i
          (JuliaLean.base.strings.string.stringCodeunitAt true str index).mapError LazyError.string)
        (codeunitAt lazyFields c displaySize a (bitIntegerIndex (E := E) t) l i)) ∧
    (∀ i : Bool,
      Forwards c displaySize a l
        (fun str => do
          let index ← boolIndex (E := E) i
          (JuliaLean.base.strings.string.stringCodeunitAt true str index).mapError LazyError.string)
        (codeunitAt lazyFields c displaySize a (boolIndex (E := E)) l i)) ∧
    (∀ i : JuliaLean.base.gmp.BigInt,
      Forwards c displaySize a l
        (fun str => do
          let index ← bigIntIndex (E := E) i
          (JuliaLean.base.strings.string.stringCodeunitAt true str index).mapError LazyError.string)
        (codeunitAt lazyFields c displaySize a (bigIntIndex (E := E)) l i))

/-- `codeunits` is the `CodeUnits` view of the String. -/
def CodeunitsProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V),
    Forwards c displaySize a l
      (fun str => .ok (JuliaLean.base.strings.basic.codeunits
        (fun _ => JuliaLean.base.strings.string.codeunitType) str))
      (codeunits lazyFields c displaySize a l)

/-- Validity at an index converts it with `Int(i)` after `String(l)` and checks the String there, for
`BitInteger`, `Bool` and `BigInt` indices. -/
def IsvalidProperty : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V),
    (∀ (t : IntTy) (i : JInt t),
      Forwards c displaySize a l
        (fun str => (bitIntegerIndex (E := E) t i).map
          (JuliaLean.base.strings.string.stringIsvalidIndex str))
        (isvalid lazyFields c displaySize a (bitIntegerIndex (E := E) t) l i)) ∧
    (∀ i : Bool,
      Forwards c displaySize a l
        (fun str => (boolIndex (E := E) i).map (JuliaLean.base.strings.string.stringIsvalidIndex str))
        (isvalid lazyFields c displaySize a (boolIndex (E := E)) l i)) ∧
    (∀ i : JuliaLean.base.gmp.BigInt,
      Forwards c displaySize a l
        (fun str => (bigIntIndex (E := E) i).map (JuliaLean.base.strings.string.stringIsvalidIndex str))
        (isvalid lazyFields c displaySize a (bigIntIndex (E := E)) l i))

/-- Only the documented lazy-string flags are accepted; parsing preserves byte-indexed parts. -/
def LazyStrProperty : Prop :=
  ∀ {E : Type}
    (findnext : Char → EagerString → Index → Option Index)
    (prevind : EagerString → Index → Index)
    (lastindex : EagerString → Index)
    (slice : EagerString → Index → Index → EagerString)
    (parseatom : EagerString → Index → String → Except E ParsedAtom)
    (showFlags : List String → String) (argumentError : String → E)
    (sourceFile : String) (text : EagerString) (flags : List String),
    (flags ≠ [] → flags ≠ ["c"] →
      lazy_str findnext prevind lastindex slice parseatom showFlags argumentError
        sourceFile text flags = .error (argumentError ("unknown lazy-string flag: " ++ showFlags flags))) ∧
    ((flags = [] ∨ flags = ["c"]) →
      lazy_str findnext prevind lastindex slice parseatom showFlags argumentError
        sourceFile text flags =
        (lazyLoop findnext prevind lastindex slice parseatom sourceFile text
          firstIndex firstIndex []).map (fun parts => .lazyString parts (flags == ["c"])))


/-- The public constructor and the macro: the constructor retains its parts, the private constructor
stores its cache, and the macro preserves parsed expansion parts. -/
def ConstructionContract : Prop :=
  CtorProperty ∧ PrivateCtorProperty ∧ LazyStrProperty

/-- All documented AbstractString forwarding methods observe the materialized String. -/
def ForwardingContract : Prop :=
  HashProperty ∧ LastindexProperty ∧ Iterate0Property ∧ IterateAtProperty ∧
  IsequalProperty ∧ EqProperty ∧ NcodeunitsProperty ∧ CodeunitTypeProperty ∧
  CodeunitAtProperty ∧ CodeunitsProperty ∧ IsvalidProperty

end JuliaLean.Proofs.base.strings.lazy


namespace JuliaLean.ChatGPT.Batch4.Group21

set_option Elab.async false

open JuliaLean JuliaLean.base.strings.lazy JuliaLean.Proofs.base.strings.lazy

/-- Successful stateful bind preserves the state returned by its first action. -/
theorem lazyBindOk {World E A B : Type} (action : M World E A)
    (next : A → M World E B) (world world' : World) (value : A)
    (h : action world = some (.ok (value, world'))) :
    (action >>= next) world = next value world' := by
  change (match action world with
    | none => none
    | some (.error result) => some (Except.error result)
    | some (.ok (value, world)) => next value world) = _
  rw [h]

/-- Failed stateful bind preserves the error and its state. -/
theorem lazyBindError {World E A B : Type} (action : M World E A)
    (next : A → M World E B) (world world' : World) (error : LazyError E)
    (h : action world = some (.error (error, world'))) :
    (action >>= next) world = some (.error (error, world')) := by
  change (match action world with
    | none => none
    | some (.error result) => some (Except.error result)
    | some (.ok (value, world)) => next value world) = _
  rw [h]

/-- A pure continuation following materialization satisfies the forwarding contract. -/
theorem lazyForwardsBind {E V Ty A : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (k : JString → Except (LazyError E) A) (run : JString → M LazyHeap E A)
    (hrun : ∀ str heap, run str heap = some (match k str with
      | .ok x => .ok (x, heap)
      | .error e => .error (e, heap))) :
    Forwards c displaySize a l k (toString lazyFields c displaySize a l >>= run) := by
  intro heap
  constructor
  · intro str heap₁ h
    rw [lazyBindOk _ _ _ _ _ h]
    exact hrun str heap₁
  · intro e heap₁ h
    exact lazyBindError _ _ _ _ _ h

/-- Reading the cache uses the allocated slot and leaves the heap unchanged. -/
theorem lazyAcquireEquation (heap : LazyHeap) (ref : CellRef) :
    lazyFields.getfield ref .acquire heap =
      some (match heap.cells[ref]? with
        | some value => .ok (value, heap)
        | none => .error (.errorException "reference to an object that was not allocated by new", heap)) := by
  cases hc : heap.cells[ref]? <;>
    simp only [lazyFields, runCell, checkedOrder, requireAtomic, cellAt, hc] <;> rfl

/-- stringscova-lazy-ctor-faithful -/
theorem StringscovaLazyCtorFaithful_proven : JuliaLean.Proofs.base.strings.lazy.CtorProperty := by
  intro E V parts compact heap
  refine ⟨⟨heap.cells.length, parts, compact⟩, ⟨heap.cells ++ [none]⟩, rfl, rfl, rfl, ?_⟩
  rw [lazyAcquireEquation, List.getElem?_append_right (Nat.le_refl heap.cells.length)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

/-- Lifting a successful field access keeps both its result and state. -/
theorem lazyLiftFieldOk {World E A : Type} (action : JuliaLean.base.io.M World A)
    (world world' : World) (value : A)
    (h : action world = some (.ok (value, world'))) :
    (liftField action : M World E A) world = some (.ok (value, world')) := by
  unfold liftField
  rw [h]

/-- A populated cache is returned without running any printing operation. -/
theorem lazyToStringCached {E V Ty : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (heap : LazyHeap) (str : JString)
    (h : lazyFields.getfield l.ref .acquire heap = some (.ok (some str, heap))) :
    toString lazyFields c ds a l heap = some (.ok (str, heap)) := by
  unfold JuliaLean.base.strings.lazy.toString
  rw [lazyBindOk _ _ _ _ _ (lazyLiftFieldOk _ _ _ _ h)] <;> rfl

/-- Printing the parts is isolated from the heap containing the lazy-string cache. -/
def lazyPrinted {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees)
    (ds : JInt64 × JInt64) (a : JuliaLean.base.show.AnyOps V Ty)
    (l : LazyString CellRef E V) :
    Except (JuliaLean.base.strings.io.Error E) JuliaLean.base.strings.io.JuliaString :=
  JuliaLean.base.strings.io.sprintIOBuffer (Args := Unit)
    (JuliaLean.base.iobuffer.bitsConversions .i64) ds a
    JuliaLean.base.strings.io.SprintContext.none (JuliaLean.base.iobuffer.i 0)
    (printParts c ds a l) ()

/-- The compare-and-swap installs a String in an allocated empty cache. -/
theorem lazyReplaceEmpty (heap : LazyHeap) (ref : CellRef) (str : JString)
    (h : heap.cells[ref]? = some none) :
    lazyFields.replacefield ref none (some str) .acquire_release .acquire heap =
      some (.ok ((none, true), ⟨heap.cells.set ref (some str)⟩)) := by
  simp only [lazyFields, runCell, checkedOrder, requireAtomic, orderRank, cellAt,
    h, bind, Except.bind, pure, Except.pure] <;> rfl

/-- Successful reads identify the heap slot. -/
theorem lazyAcquireSuccess (heap heap' : LazyHeap) (ref : CellRef) (value : Option JString)
    (h : lazyFields.getfield ref .acquire heap = some (.ok (value, heap'))) :
    heap.cells[ref]? = some value ∧ heap' = heap := by
  rw [lazyAcquireEquation] at h
  cases hc : heap.cells[ref]? with
  | none => rw [hc] at h; cases h
  | some got =>
    rw [hc] at h
    have hh := Prod.mk.inj (Except.ok.inj (Option.some.inj h))
    exact ⟨congrArg some hh.1, hh.2.symm⟩

/-- A lifted successful pure computation leaves the state unchanged. -/
theorem lazyBindLiftOk {World E A B : Type} (next : A → M World E B)
    (world : World) (value : A) :
    (liftPure (.ok value) >>= next) world = next value world := by rfl

/-- Materialization from an empty cache either propagates printing's error or installs its output. -/
theorem lazyToStringEmpty {E V Ty : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (heap : LazyHeap) (h : heap.cells[l.ref]? = some none) :
    toString lazyFields c ds a l heap =
      match lazyPrinted c ds a l with
      | .error e => some (.error (.sprint e, heap))
      | .ok printed =>
        match stringFromPrinted (E := E) printed with
        | .error e => some (.error (e, heap))
        | .ok str => some (.ok (str, ⟨heap.cells.set l.ref (some str)⟩)) := by
  have hget : lazyFields.getfield l.ref .acquire heap = some (.ok (none, heap)) := by
    rw [lazyAcquireEquation, h]
  unfold JuliaLean.base.strings.lazy.toString
  rw [lazyBindOk _ _ _ _ _ (lazyLiftFieldOk _ _ _ _ hget)]
  change (liftPure ((lazyPrinted c ds a l).mapError LazyError.sprint) >>= _) heap = _
  cases hp : lazyPrinted c ds a l with
  | error e => rfl
  | ok printed =>
    simp only [Except.mapError]
    rw [lazyBindLiftOk]
    change (liftPure (stringFromPrinted (E := E) printed) >>= _) heap = _
    cases hs : stringFromPrinted (E := E) printed with
    | error e => rfl
    | ok str =>
      rw [lazyBindLiftOk]
      rw [lazyBindOk _ _ _ _ _ (lazyLiftFieldOk _ _ _ _ (lazyReplaceEmpty heap l.ref str h))] <;> rfl

/-- Updating an allocated cache slot makes subsequent acquire reads return its new contents. -/
theorem lazyAcquireSet (heap : LazyHeap) (ref : CellRef) (old value : Option JString)
    (h : heap.cells[ref]? = some old) :
    lazyFields.getfield ref .acquire ⟨heap.cells.set ref value⟩ =
      some (.ok (value, ⟨heap.cells.set ref value⟩)) := by
  rw [lazyAcquireEquation]
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
  simp only [List.getElem?_set_self hlt]

/-- A nonallocated reference cannot materialize successfully. -/
theorem lazyToStringInvalid {E V Ty : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (heap : LazyHeap) (h : heap.cells[l.ref]? = none) :
    toString lazyFields c ds a l heap =
      some (.error (.field (.errorException "reference to an object that was not allocated by new"), heap)) := by
  unfold JuliaLean.base.strings.lazy.toString
  apply lazyBindError
  unfold liftField
  rw [lazyAcquireEquation, h]

/-- stringscova-lazy-string-faithful -/
theorem StringscovaLazyStringFaithful_proven : JuliaLean.Proofs.base.strings.lazy.ToStringProperty := by
  intro E V Ty c ds a l heap str heap₁ h
  suffices hcache : lazyFields.getfield l.ref .acquire heap₁ = some (.ok (some str, heap₁)) from
    ⟨hcache, lazyToStringCached c ds a l heap₁ str hcache⟩
  cases hc : heap.cells[l.ref]? with
  | none => rw [lazyToStringInvalid c ds a l heap hc] at h; cases h
  | some old =>
    cases old with
    | some cached =>
      have hget : lazyFields.getfield l.ref .acquire heap = some (.ok (some cached, heap)) := by
        rw [lazyAcquireEquation, hc]
      rw [lazyToStringCached c ds a l heap cached hget] at h
      have hh := Prod.mk.inj (Except.ok.inj (Option.some.inj h))
      rcases hh with ⟨rfl, rfl⟩
      exact hget
    | none =>
      rw [lazyToStringEmpty c ds a l heap hc] at h
      cases hp : lazyPrinted c ds a l with
      | error e => rw [hp] at h; cases h
      | ok printed =>
        rw [hp] at h
        dsimp only at h
        cases hs : stringFromPrinted (E := E) printed with
        | error e => rw [hs] at h; cases h
        | ok value =>
          rw [hs] at h
          have hh := Prod.mk.inj (Except.ok.inj (Option.some.inj h))
          rcases hh with ⟨rfl, rfl⟩
          exact lazyAcquireSet heap l.ref none (some value) hc

/-- Wrapping a successfully printed byte sequence in a String does not change the bytes. -/
theorem lazyStringFromPrintedBytes {E : Type}
    (printed : JuliaLean.base.strings.io.JuliaString) (str : JString)
    (h : stringFromPrinted (E := E) printed = .ok str) : printed.bytes = str.bytes := by
  unfold stringFromPrinted at h
  split at h
  · exact congrArg JuliaLean.Strings.JStr.bytes (Except.ok.inj h)
  · cases h

/-- The remaining independent byte-content obligation for String-only parts. -/
def lazyStringPartsPrinted : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (strs : List JString) (compact : Bool)
    (ref : CellRef) (printed : JuliaLean.base.strings.io.JuliaString),
    lazyPrinted c ds a
      ⟨ref, strs.map (fun s => (JuliaLean.base.strings.io.StrArg.string s : LazyPart E V)), compact⟩ =
        .ok printed →
      printed.bytes.length < 2 ^ 62 →
      printed.bytes = (strs.map (·.bytes)).flatten

/-- The full materialization target follows from byte correctness of the installed printer. -/
theorem lazyMaterializationOfPrinting (hprint : lazyStringPartsPrinted) :
    JuliaLean.Proofs.base.strings.lazy.MaterializationContract := by
  intro E V Ty c ds a strs compact heap l heap₁ result heap₂ hctor hstring
  change some (Except.ok ((⟨heap.cells.length,
    strs.map (fun s => (JuliaLean.base.strings.io.StrArg.string s : LazyPart E V)), compact⟩ : LazyString CellRef E V),
    (⟨heap.cells ++ [none]⟩ : LazyHeap))) = some (Except.ok (l, heap₁)) at hctor
  have hh := Prod.mk.inj (Except.ok.inj (Option.some.inj hctor))
  rcases hh with ⟨rfl, rfl⟩
  have hslot : (heap.cells ++ [none])[heap.cells.length]? = some none := by
    rw [List.getElem?_append_right (Nat.le_refl heap.cells.length), Nat.sub_self] <;> rfl
  refine ⟨?_, (StringscovaLazyStringFaithful_proven c ds a _ _ result heap₂ hstring).1⟩
  rw [lazyToStringEmpty c ds a _ _ hslot] at hstring
  cases hp : lazyPrinted c ds a
      ⟨heap.cells.length,
        strs.map (fun s => (JuliaLean.base.strings.io.StrArg.string s : LazyPart E V)), compact⟩ with
  | error e => rw [hp] at hstring; cases hstring
  | ok printed =>
    rw [hp] at hstring
    dsimp only at hstring
    cases hs : stringFromPrinted (E := E) printed with
    | error e => rw [hs] at hstring; cases hstring
    | ok str =>
      rw [hs] at hstring
      have hresult := (Prod.mk.inj (Except.ok.inj (Option.some.inj hstring))).1
      calc
        result.bytes = printed.bytes := by
          rw [← hresult]
          exact (lazyStringFromPrintedBytes (E := E) printed str hs).symm
        _ = (strs.map (·.bytes)).flatten := hprint c ds a strs compact heap.cells.length printed hp (by
          rw [lazyStringFromPrintedBytes (E := E) printed str hs]
          exact str.small)

/-- stringscova-lazy-hash-faithful -/
theorem StringscovaLazyHashFaithful_proven : JuliaLean.Proofs.base.strings.lazy.HashProperty := by
  intro E V Ty c ds a l seed
  apply lazyForwardsBind
  intro str heap
  rfl

/-- Forwarding a String operation treats its result without reducing the operation. -/
theorem lazyForwardsStringResult {E V Ty A : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (result : JString → JuliaLean.base.strings.string.StringResult A) :
    Forwards c ds a l (fun str => (result str).mapError LazyError.string)
      (toString lazyFields c ds a l >>= fun str =>
        match result str with
        | .ok value => pure value
        | .error error => throw (LazyError.string error)) := by
  apply lazyForwardsBind
  intro str heap
  cases result str <;> rfl


/-- stringscova-lazy-iterate0-faithful -/
theorem StringscovaLazyIterate0Faithful_proven : JuliaLean.Proofs.base.strings.lazy.Iterate0Property := by
  intro E V Ty c ds a l
  apply lazyForwardsBind
  intro str heap
  rfl

theorem lazyIterateAtForwards {E V Ty I : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (toInt : I → Except (LazyError E) JInt64) (i : I) :
    Forwards c ds a l
      (fun str => (toInt i).map (JuliaLean.base.strings.string.stringIterate str))
      (iterateAt lazyFields c ds a toInt l i) := by
  apply lazyForwardsBind
  intro str heap
  cases toInt i <;> rfl

/-- stringscova-lazy-iterate-faithful -/
theorem StringscovaLazyIterateFaithful_proven : JuliaLean.Proofs.base.strings.lazy.IterateAtProperty := by
  intro E V Ty c ds a l
  exact ⟨fun t i => lazyIterateAtForwards c ds a l _ i,
    fun i => lazyIterateAtForwards c ds a l _ i,
    fun i => lazyIterateAtForwards c ds a l _ i⟩

/-- stringscova-lazy-isequal-faithful -/
theorem StringscovaLazyIsequalFaithful_proven : JuliaLean.Proofs.base.strings.lazy.IsequalProperty := by
  intro E V Ty c ds a x y heap
  constructor
  · intro e heap₁ h
    exact lazyBindError _ _ _ _ _ h
  constructor
  · intro s₁ heap₁ e heap₂ hx hy
    unfold JuliaLean.base.strings.lazy.isequal
    rw [lazyBindOk _ _ _ _ _ hx, lazyBindError _ _ _ _ _ hy]
  · intro s₁ heap₁ s₂ heap₂ hx hy
    unfold JuliaLean.base.strings.lazy.isequal
    rw [lazyBindOk _ _ _ _ _ hx, lazyBindOk _ _ _ _ _ hy] <;> rfl

/-- stringscova-lazy-eq-faithful -/
theorem StringscovaLazyEqFaithful_proven : JuliaLean.Proofs.base.strings.lazy.EqProperty := by
  intro E V Ty c ds a x y heap
  constructor
  · intro e heap₁ h
    exact lazyBindError _ _ _ _ _ h
  constructor
  · intro s₁ heap₁ e heap₂ hx hy
    unfold JuliaLean.base.strings.lazy.eq
    rw [lazyBindOk _ _ _ _ _ hx, lazyBindError _ _ _ _ _ hy]
  · intro s₁ heap₁ s₂ heap₂ hx hy
    unfold JuliaLean.base.strings.lazy.eq
    rw [lazyBindOk _ _ _ _ _ hx, lazyBindOk _ _ _ _ _ hy] <;> rfl

/-- stringscova-lazy-ncodeunits-faithful -/
theorem StringscovaLazyNcodeunitsFaithful_proven : JuliaLean.Proofs.base.strings.lazy.NcodeunitsProperty := by
  intro E V Ty c ds a l
  apply lazyForwardsBind
  intro str heap
  rfl

/-- stringscova-lazy-codeunit-type-faithful -/
theorem StringscovaLazyCodeunitTypeFaithful_proven : JuliaLean.Proofs.base.strings.lazy.CodeunitTypeProperty := by
  intro Ref E V l
  exact ⟨rfl, rfl⟩

theorem lazyCodeunitAtForwards {E V Ty I : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (toInt : I → Except (LazyError E) JInt64) (i : I) :
    Forwards c ds a l
      (fun str => do
        let index ← toInt i
        (JuliaLean.base.strings.string.stringCodeunitAt true str index).mapError LazyError.string)
      (codeunitAt lazyFields c ds a toInt l i) := by
  apply lazyForwardsBind
  intro str heap
  cases h : toInt i with
  | error e => rfl
  | ok index =>
    dsimp only [liftPure, bind, Except.bind]
    cases JuliaLean.base.strings.string.stringCodeunitAt true str index <;> rfl

/-- stringscova-lazy-codeunit-faithful -/
theorem StringscovaLazyCodeunitFaithful_proven : JuliaLean.Proofs.base.strings.lazy.CodeunitAtProperty := by
  intro E V Ty c ds a l
  exact ⟨fun t i => lazyCodeunitAtForwards c ds a l _ i,
    fun i => lazyCodeunitAtForwards c ds a l _ i,
    fun i => lazyCodeunitAtForwards c ds a l _ i⟩

/-- stringscova-lazy-codeunits-faithful -/
theorem StringscovaLazyCodeunitsFaithful_proven : JuliaLean.Proofs.base.strings.lazy.CodeunitsProperty := by
  intro E V Ty c ds a l
  apply lazyForwardsBind
  intro str heap
  rfl

theorem lazyIsvalidForwards {E V Ty I : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (toInt : I → Except (LazyError E) JInt64) (i : I) :
    Forwards c ds a l
      (fun str => (toInt i).map (JuliaLean.base.strings.string.stringIsvalidIndex str))
      (isvalid lazyFields c ds a toInt l i) := by
  apply lazyForwardsBind
  intro str heap
  cases toInt i <;> rfl

/-- stringscova-lazy-isvalid-faithful -/
theorem StringscovaLazyIsvalidFaithful_proven : JuliaLean.Proofs.base.strings.lazy.IsvalidProperty := by
  intro E V Ty c ds a l
  exact ⟨fun t i => lazyIsvalidForwards c ds a l _ i,
    fun i => lazyIsvalidForwards c ds a l _ i,
    fun i => lazyIsvalidForwards c ds a l _ i⟩

/-- stringscova-lazy-macro-faithful -/
theorem StringscovaLazyMacroFaithful_proven : JuliaLean.Proofs.base.strings.lazy.LazyStrProperty := by
  intro E findnext prevind lastindex slice parseatom showFlags argumentError sourceFile text flags
  constructor
  · intro hnil hc
    simp only [lazy_str, List.isEmpty_eq_false_iff.mpr hnil, beq_eq_false_iff_ne.mpr hc,
      Bool.or_false, Bool.false_eq_true, ite_false]
  · intro hflags
    rcases hflags with rfl | rfl <;>
      simp only [lazy_str, List.isEmpty_nil, Bool.true_or, beq_self_eq_true,
        Bool.or_true, ite_true]
    all_goals
      cases lazyLoop findnext prevind lastindex slice parseatom sourceFile text
        firstIndex firstIndex [] <;> rfl

theorem lazyPrivateCtor : JuliaLean.Proofs.base.strings.lazy.PrivateCtorProperty := by
  intro E V parts str heap
  refine ⟨⟨heap.cells.length, parts, false⟩, ⟨heap.cells ++ [str]⟩, rfl, rfl, rfl, ?_⟩
  rw [lazyAcquireEquation, List.getElem?_append_right (Nat.le_refl heap.cells.length)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

/-- stringscova-lazy-construction -/
theorem StringscovaLazyConstruction_proven : JuliaLean.Proofs.base.strings.lazy.ConstructionContract := by
  exact ⟨StringscovaLazyCtorFaithful_proven, lazyPrivateCtor, StringscovaLazyMacroFaithful_proven⟩


open JuliaLean JuliaLean.base.strings.lazy

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace LazyPrintOps
export JuliaLean.base.iobuffer (I U IOErr BufferState M i u imaxval imax imin uminU
  getOffset getCompacted getUsedSpan overallocation bitLength stringMemory similarData resize
  ensureroom ensureroomSlowpath ensureroomReallocate writeByte unsafeWrite
  takestring slice rangeLength writeAt setChecked toI lift copyto)
end LazyPrintOps

theorem lazyPrintWrapCongr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> omega

theorem lazyPrintWrapMod (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem lazyPrintWrapAddLeft (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a + b) = wrapInt t (a + b) :=
  lazyPrintWrapCongr t (by rw [Int.add_emod, lazyPrintWrapMod, ← Int.add_emod])

theorem lazyPrintWrapAddRight (t : IntTy) (a b : Int) :
    wrapInt t (a + wrapInt t b) = wrapInt t (a + b) :=
  lazyPrintWrapCongr t (by rw [Int.add_emod, lazyPrintWrapMod, ← Int.add_emod])

theorem lazyPrintWrapMulLeft (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a * b) = wrapInt t (a * b) :=
  lazyPrintWrapCongr t (by rw [Int.mul_emod, lazyPrintWrapMod, ← Int.mul_emod])

theorem lazyPrintWrapMulRight (t : IntTy) (a b : Int) :
    wrapInt t (a * wrapInt t b) = wrapInt t (a * b) :=
  lazyPrintWrapCongr t (by rw [Int.mul_emod, lazyPrintWrapMod, ← Int.mul_emod])

theorem lazyPrintWrapSubLeft (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a - b) = wrapInt t (a - b) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem lazyPrintWrapSubRight (t : IntTy) (a b : Int) :
    wrapInt t (a - wrapInt t b) = wrapInt t (a - b) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem lazyPrintIVal (n : Int) (hlo : -2 ^ 63 ≤ n) (hhi : n < 2 ^ 63) :
    (LazyPrintOps.i n).val = n := by
  exact wrapInt_of_inRange .i64 n (by
    change -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807
    omega)

theorem lazyPrintIAdd (a b : Int) : LazyPrintOps.i a + LazyPrintOps.i b = LazyPrintOps.i (a + b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a + wrapInt .i64 b) = wrapInt .i64 (a + b)
  rw [lazyPrintWrapAddLeft, lazyPrintWrapAddRight]

theorem lazyPrintISub (a b : Int) : LazyPrintOps.i a - LazyPrintOps.i b = LazyPrintOps.i (a - b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a - wrapInt .i64 b) = wrapInt .i64 (a - b)
  rw [lazyPrintWrapSubLeft, lazyPrintWrapSubRight]

theorem lazyPrintIMul (a b : Int) : LazyPrintOps.i a * LazyPrintOps.i b = LazyPrintOps.i (a * b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a * wrapInt .i64 b) = wrapInt .i64 (a * b)
  rw [lazyPrintWrapMulLeft, lazyPrintWrapMulRight]

theorem lazyPrintUVal (n : Nat) (hn : n < 2 ^ 64) : (LazyPrintOps.u n).val = (n : Int) := by
  change wrapInt .u64 n = (n : Int)
  apply wrapInt_of_inRange
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ 18446744073709551615
  omega

theorem lazyPrintRemUInt (n : Nat) (hn : n < 2 ^ 64) :
    JInt.rem .i64 (LazyPrintOps.u n) = LazyPrintOps.i n := by
  apply Subtype.ext
  change wrapInt .i64 (LazyPrintOps.u n).val = wrapInt .i64 n
  rw [lazyPrintUVal n hn]

theorem lazyPrintConvertNat (n : Nat) (hn : n < 2 ^ 63) : LazyPrintOps.toI n = .ok (LazyPrintOps.i n) := by
  have hr : IntTy.i64.min ≤ (n : Int) ∧ (n : Int) ≤ IntTy.i64.max := by
    change -9223372036854775808 ≤ (n : Int) ∧ (n : Int) ≤ 9223372036854775807
    omega
  unfold LazyPrintOps.toI JInt.convert
  rw [dif_pos hr]
  apply congrArg Except.ok
  apply Subtype.ext
  change (n : Int) = (LazyPrintOps.i n).val
  exact (lazyPrintIVal (n : Int) (by omega) (by omega)).symm

theorem lazyPrintBitLengthBound (fuel n : Nat) : LazyPrintOps.bitLength fuel n ≤ fuel := by
  induction fuel generalizing n with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
    simp only [LazyPrintOps.bitLength]
    split <;> (have := ih (n / 2); omega)

theorem lazyPrintOverallocationBound (n : LazyPrintOps.I) (hn : 0 ≤ n.val) :
    n.val ≤ (LazyPrintOps.overallocation n).val ∧ (LazyPrintOps.overallocation n).val ≤ 2 ^ 63 - 1 := by
  have nmax := n.property.2
  change n.val ≤ 9223372036854775807 at nmax
  unfold LazyPrintOps.overallocation
  have hneg : ¬ n.val < 0 := by omega
  simp only [hneg, ↓reduceIte]
  generalize hb : LazyPrintOps.bitLength 64 n.val.toNat = bits
  have hb64 : bits ≤ 64 := hb ▸ lazyPrintBitLengthBound 64 _
  have he : bits * 7 / 8 ≤ 56 := by omega
  have hp1 := Nat.pow_le_pow_right (by decide : 2 > 0) he
  have hp0 := Nat.pow_le_pow_right (by decide : 2 > 0) (Nat.zero_le (bits * 7 / 8))
  have hc : ((2 ^ (bits * 7 / 8) : Nat) : Int) = (2 : Int) ^ (bits * 7 / 8) :=
    Int.natCast_pow 2 _
  generalize (2 : Int) ^ (bits * 7 / 8) = x at *
  have hx1 : x ≤ 2 ^ 56 := by omega
  have hx0 : 1 ≤ x := by simp only [Nat.pow_zero] at hp0; omega
  have ht : n.val.tdiv 8 = n.val / 8 := Int.tdiv_eq_ediv_of_nonneg hn
  have hex : (LazyPrintOps.i x * LazyPrintOps.i 3 + LazyPrintOps.i (n.val.tdiv 8)).val = x * 3 + n.val / 8 := by
    rw [lazyPrintIMul, lazyPrintIAdd, ht, lazyPrintIVal _ (by omega) (by omega)]
  have him : LazyPrintOps.imaxval.val = 2 ^ 63 - 1 := by decide
  have hsub : (LazyPrintOps.imaxval - (LazyPrintOps.i x * LazyPrintOps.i 3 + LazyPrintOps.i (n.val.tdiv 8))).val =
      2 ^ 63 - 1 - (x * 3 + n.val / 8) := by
    change wrapInt .i64 (LazyPrintOps.imaxval.val - (LazyPrintOps.i x * LazyPrintOps.i 3 + LazyPrintOps.i (n.val.tdiv 8)).val) = _
    rw [him, hex]
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ 2 ^ 63 - 1 - (x * 3 + n.val / 8) ∧
      2 ^ 63 - 1 - (x * 3 + n.val / 8) ≤ 9223372036854775807
    omega
  rw [hsub]
  split
  · rw [him]; omega
  · rename_i hroom
    have hsum : (n + (LazyPrintOps.i x * LazyPrintOps.i 3 + LazyPrintOps.i (n.val.tdiv 8))).val =
        n.val + (x * 3 + n.val / 8) := by
      change wrapInt .i64 (n.val + (LazyPrintOps.i x * LazyPrintOps.i 3 + LazyPrintOps.i (n.val.tdiv 8)).val) = _
      rw [hex]
      apply wrapInt_of_inRange
      change -9223372036854775808 ≤ n.val + (x * 3 + n.val / 8) ∧
        n.val + (x * 3 + n.val / 8) ≤ 9223372036854775807
      omega
    rw [hsum]
    omega

abbrev lazyPrintBuffer (data : List UInt8) (len : Nat) : LazyPrintOps.BufferState where
  data := data
  isMemory := true
  reinit := false
  readable := true
  writable := true
  seekable := true
  append := false
  size := LazyPrintOps.i len
  maxsize := LazyPrintOps.imaxval
  ptr := LazyPrintOps.i ((len : Int) + 1)
  offset := LazyPrintOps.i 0
  mark := LazyPrintOps.i (-1)


theorem lazyPrintBufferOffset (data : List UInt8) (len : Nat) :
    LazyPrintOps.getOffset (lazyPrintBuffer data len) = LazyPrintOps.i 0 := by rfl

theorem lazyPrintBufferSpan (data : List UInt8) (len : Nat) :
    LazyPrintOps.getUsedSpan (lazyPrintBuffer data len) = .ok (LazyPrintOps.i 1, LazyPrintOps.i len) := by rfl

theorem lazyPrintEnsureForm (data : List UInt8) (len : Nat) (n : LazyPrintOps.U) :
    (LazyPrintOps.ensureroom n).run (lazyPrintBuffer data len) =
      (let existing := LazyPrintOps.imin (LazyPrintOps.i data.length - (LazyPrintOps.i ((len : Int) + 1) - LazyPrintOps.i 1))
        (LazyPrintOps.imaxval - ((LazyPrintOps.i ((len : Int) + 1) - LazyPrintOps.i 1) - LazyPrintOps.i 0))
       if existing.val < (JInt.rem .i64 n).val then
         (LazyPrintOps.ensureroomSlowpath n existing).run (lazyPrintBuffer data len)
       else .ok () (lazyPrintBuffer data len)) := by
  simp only [LazyPrintOps.ensureroom, EStateM.run, Bind.bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, Bool.not_true, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, lazyPrintBufferOffset, Pure.pure, EStateM.pure]
  split <;> simp_all only [EStateM.pure, ↓reduceIte]

/-- Normalize the slow path before specializing its state or integer arguments. -/
theorem lazyPrintSlowResizeGeneral (st : LazyPrintOps.BufferState) (n : LazyPrintOps.U) (avail count desired last : LazyPrintOps.I)
    (hspan : LazyPrintOps.getUsedSpan st = .ok (LazyPrintOps.i 1, last))
    (hconvert : LazyPrintOps.toI n.val = .ok count)
    (hdesired : LazyPrintOps.i st.data.length + count - avail = desired)
    (hnot : ¬ desired.val > st.maxsize.val) :
    (LazyPrintOps.ensureroomSlowpath n avail).run st = (LazyPrintOps.resize desired false).run st := by
  unfold LazyPrintOps.ensureroomSlowpath
  generalize LazyPrintOps.resize = resizeAction
  simp only [EStateM.run, Bind.bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, hspan, LazyPrintOps.lift, lazyPrintISub, Int.sub_self,
    show (LazyPrintOps.i 0).val = 0 from rfl, show ¬ (0 : Int) ≥ 32 by decide,
    false_and, ↓reduceIte, hconvert, hdesired, hnot, Pure.pure, EStateM.pure]

theorem lazyPrintSlowResize (data : List UInt8) (len : Nat) (n : LazyPrintOps.U) (avail count : LazyPrintOps.I)
    (hconvert : LazyPrintOps.toI n.val = .ok count)
    (hnot : ¬ (LazyPrintOps.i data.length + count - avail).val > LazyPrintOps.imaxval.val) :
    (LazyPrintOps.ensureroomSlowpath n avail).run (lazyPrintBuffer data len) =
      (LazyPrintOps.resize (LazyPrintOps.i data.length + count - avail) false).run (lazyPrintBuffer data len) := by
  exact lazyPrintSlowResizeGeneral (lazyPrintBuffer data len) n avail count _ (LazyPrintOps.i len)
    (lazyPrintBufferSpan data len) hconvert rfl hnot

theorem lazyPrintRangeLengthOne (len : Nat) (hlen : len < 2 ^ 63) :
    LazyPrintOps.rangeLength (LazyPrintOps.i 1) (LazyPrintOps.i len) = LazyPrintOps.i len := by
  unfold LazyPrintOps.rangeLength
  have hone : (LazyPrintOps.i 1).val = 1 := by decide
  rw [lazyPrintIVal _ (by omega) (by omega), hone]
  by_cases hz : len = 0
  · subst len
    rfl
  · rw [if_neg (by omega), lazyPrintISub, lazyPrintIAdd]
    apply congrArg LazyPrintOps.i
    omega

/-- The native resize result with all intermediate values kept abstract. -/
theorem lazyPrintResizeBufferGeneral (st : LazyPrintOps.BufferState) (desired cap a b used : LazyPrintOps.I)
    (fresh final : List UInt8)
    (hcap : LazyPrintOps.imin st.maxsize (LazyPrintOps.overallocation desired) = cap)
    (hspan : LazyPrintOps.getUsedSpan st = .ok (a, b))
    (halloc : LazyPrintOps.similarData st cap = .ok fresh)
    (hnz : cap.val ≠ 0) (hused : LazyPrintOps.rangeLength a b = used)
    (hcopy : (if used.val = 0 then Except.ok fresh
      else LazyPrintOps.copyto fresh (LazyPrintOps.i 1) st.data a used) = .ok final) :
    (LazyPrintOps.resize desired false).run st =
      .ok () { st with
        data := final
        offset := -LazyPrintOps.getCompacted st - ((a - LazyPrintOps.i 1) - LazyPrintOps.getOffset st)
        ptr := st.ptr - (a - LazyPrintOps.i 1)
        size := used } := by
  unfold LazyPrintOps.resize
  generalize LazyPrintOps.copyto = copyAction at hcopy ⊢
  generalize LazyPrintOps.similarData = allocateData at halloc ⊢
  simp only [EStateM.run, Bind.bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, Bool.false_eq_true, ↓reduceIte,
    hcap, hspan, LazyPrintOps.lift, Pure.pure, EStateM.pure, halloc, hnz,
    hused, set, MonadStateOf.set, EStateM.set]
  by_cases hz : used.val = 0
  · simp only [hz, ↓reduceIte] at hcopy ⊢
    cases hcopy
    rfl
  · simp only [hz, ↓reduceIte] at hcopy ⊢
    simp only [hcopy, LazyPrintOps.lift, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      set, MonadStateOf.set, EStateM.set]

theorem lazyPrintResizeBuffer (data : List UInt8) (len desired cap : Nat)
    (hlen : len < 2 ^ 63) (hdata : len ≤ data.length)
    (hcap : 0 < cap) (hcapsmall : cap < 2 ^ 63) (hfit : len ≤ cap)
    (hc : LazyPrintOps.imin LazyPrintOps.imaxval (LazyPrintOps.overallocation (LazyPrintOps.i desired)) = LazyPrintOps.i cap) :
    (LazyPrintOps.resize (LazyPrintOps.i desired) false).run (lazyPrintBuffer data len) =
      .ok () (lazyPrintBuffer (data.take len ++ List.replicate (cap - len) 0) len) := by
  have hv : (LazyPrintOps.i len).val = (len : Int) := lazyPrintIVal _ (by omega) (by omega)
  have hcv : (LazyPrintOps.i cap).val = (cap : Int) := lazyPrintIVal _ (by omega) (by omega)
  have hspan : LazyPrintOps.getUsedSpan (lazyPrintBuffer data len) = .ok (LazyPrintOps.i 1, LazyPrintOps.i len) := by rfl
  have hsm : LazyPrintOps.similarData (lazyPrintBuffer data len) (LazyPrintOps.i cap) = .ok (List.replicate cap 0) := by
    simp only [LazyPrintOps.similarData, lazyPrintBuffer, ↓reduceIte, LazyPrintOps.stringMemory, hcv,
      show ¬ (cap : Int) < 0 by omega, ↓reduceIte, Int.toNat_natCast]
  have hcopy : LazyPrintOps.copyto (List.replicate cap 0) (LazyPrintOps.i 1) data (LazyPrintOps.i 1) (LazyPrintOps.i len) =
      .ok (data.take len ++ List.replicate (cap - len) 0) := by
    by_cases hz : len = 0
    · subst len
      simp only [LazyPrintOps.copyto, hv, Int.natCast_zero, show (LazyPrintOps.i 0).val = 0 from rfl, ↓reduceIte,
        List.take_zero, Nat.sub_zero, List.nil_append]
    · have hone : (LazyPrintOps.i 1).val = 1 := by decide
      have hbounds : 1 ≤ (LazyPrintOps.i 1).val ∧ (LazyPrintOps.i 1).val + (LazyPrintOps.i len).val - 1 ≤
          (List.replicate cap (0 : UInt8)).length ∧ 1 ≤ (LazyPrintOps.i 1).val ∧
          (LazyPrintOps.i 1).val + (LazyPrintOps.i len).val - 1 ≤ data.length := by
        rw [hone, hv, List.length_replicate]
        omega
      simp only [LazyPrintOps.copyto, hv, show (len : Int) ≠ 0 by omega,
        show ¬ (len : Int) < 0 by omega, ↓reduceIte, hone,
        List.length_replicate, show 1 + (len : Int) - 1 = len by omega,
        show (len : Int) ≤ cap by omega, show (len : Int) ≤ data.length by omega,
        Int.reduceLE, and_self, ↓reduceIte, List.take_zero, List.nil_append,
        LazyPrintOps.slice, Int.reduceSub, Int.reduceToNat, List.drop_zero,
        Int.zero_add, Int.sub_add_cancel, Int.toNat_natCast, List.drop_replicate]
  have hcopyResult : (if (LazyPrintOps.i len).val = 0 then Except.ok (List.replicate cap 0)
      else LazyPrintOps.copyto (List.replicate cap 0) (LazyPrintOps.i 1) data (LazyPrintOps.i 1) (LazyPrintOps.i len)) =
      .ok (data.take len ++ List.replicate (cap - len) 0) := by
    by_cases hz : len = 0
    · subst len
      simp only [hv, Int.natCast_zero, show (LazyPrintOps.i 0).val = 0 from rfl, ↓reduceIte, List.take_zero,
        Nat.sub_zero, List.nil_append]
    · rw [if_neg (by rw [hv]; omega)]
      exact hcopy
  rw [lazyPrintResizeBufferGeneral (lazyPrintBuffer data len) (LazyPrintOps.i desired) (LazyPrintOps.i cap) (LazyPrintOps.i 1) (LazyPrintOps.i len)
    (LazyPrintOps.i len) (List.replicate cap 0) _ hc hspan hsm (by rw [hcv]; omega)
    (lazyPrintRangeLengthOne len hlen) hcopyResult]
  have hp : (lazyPrintBuffer data len).ptr - (LazyPrintOps.i 1 - LazyPrintOps.i 1) = (lazyPrintBuffer data len).ptr := by
    change LazyPrintOps.i ((len : Int) + 1) - (LazyPrintOps.i 1 - LazyPrintOps.i 1) = _
    rw [lazyPrintISub, lazyPrintISub]
    apply congrArg LazyPrintOps.i
    omega
  rw [hp]
  rfl

theorem lazyPrintExisting (data : List UInt8) (len : Nat)
    (hfits : len ≤ data.length) (hcap : data.length < 2 ^ 63) :
    LazyPrintOps.imin
      (LazyPrintOps.i data.length - (LazyPrintOps.i ((len : Int) + 1) - LazyPrintOps.i 1))
      (LazyPrintOps.imaxval - ((LazyPrintOps.i ((len : Int) + 1) - LazyPrintOps.i 1) - LazyPrintOps.i 0)) =
        LazyPrintOps.i ((data.length : Int) - len) := by
  simp only [lazyPrintISub, LazyPrintOps.imaxval]
  have hstart : (len : Int) + 1 - 1 = len := by omega
  rw [hstart]
  simp only [Int.sub_zero]
  have hl := lazyPrintIVal ((data.length : Int) - len) (by omega) (by omega)
  have hr := lazyPrintIVal ((2 : Int) ^ 63 - 1 - len) (by omega) (by omega)
  simp only [LazyPrintOps.imin, hl, hr, show ¬ (2 : Int) ^ 63 - 1 - len < (data.length : Int) - len by omega,
    ↓reduceIte]

theorem lazyPrintEnsureEquation (data : List UInt8) (len n : Nat)
    (hfits : len ≤ data.length) (hcap : data.length < 2 ^ 63) (hn : n < 2 ^ 63) :
    (LazyPrintOps.ensureroom (LazyPrintOps.u n)).run (lazyPrintBuffer data len) =
      if data.length - len < n then
        (LazyPrintOps.resize (LazyPrintOps.i ((len : Int) + n)) false).run (lazyPrintBuffer data len)
      else .ok () (lazyPrintBuffer data len) := by
  rw [lazyPrintEnsureForm, lazyPrintExisting data len hfits hcap, lazyPrintRemUInt n (by omega)]
  dsimp only
  simp only [lazyPrintIVal ((data.length : Int) - len) (by omega) (by omega),
    lazyPrintIVal (n : Int) (by omega) (by omega)]
  have hcond : (data.length : Int) - len < n ↔ data.length - len < n := by omega
  simp only [hcond]
  split
  · have hconvert : LazyPrintOps.toI (LazyPrintOps.u n).val = .ok (LazyPrintOps.i n) := by
      rw [lazyPrintUVal n (by omega)]
      exact lazyPrintConvertNat n hn
    have hd : LazyPrintOps.i data.length + LazyPrintOps.i n -
        LazyPrintOps.i ((data.length : Int) - len) = LazyPrintOps.i ((len : Int) + n) := by
      rw [lazyPrintIAdd, lazyPrintISub]
      apply congrArg LazyPrintOps.i
      omega
    rw [lazyPrintSlowResizeGeneral (lazyPrintBuffer data len) (LazyPrintOps.u n)
      (LazyPrintOps.i ((data.length : Int) - len)) (LazyPrintOps.i n)
      (LazyPrintOps.i ((len : Int) + n)) (LazyPrintOps.i len)
      (lazyPrintBufferSpan data len) hconvert hd (by
        have h := (LazyPrintOps.i ((len : Int) + n)).property.2
        change ¬ (LazyPrintOps.i ((len : Int) + n)).val > 9223372036854775807
        exact Int.not_lt.mpr h)]
  · rfl

/-- Wrapped cumulative sizes cannot produce the zero-sized reallocation early return. -/
theorem lazyPrintOverallocationFarNegative (n : LazyPrintOps.I)
    (hn : n.val ≤ -(2 ^ 62 : Int)) : (LazyPrintOps.overallocation n).val ≠ 0 := by
  have hnlo := n.property.1
  change -9223372036854775808 ≤ n.val at hnlo
  have ht : -(2 ^ 60 : Int) ≤ n.val.tdiv 8 ∧ n.val.tdiv 8 ≤ -(2 ^ 59 : Int) + 1 := by
    simp only [Int.tdiv_eq_ediv, show Int.sign 8 = 1 from rfl]
    split <;> omega
  have he : (LazyPrintOps.i (2 ^ (64 * 7 / 8)) * LazyPrintOps.i 3 +
      LazyPrintOps.i (n.val.tdiv 8)).val = (3 * 2 ^ 56 : Int) + n.val.tdiv 8 := by
    rw [lazyPrintIMul, lazyPrintIAdd, lazyPrintIVal _ (by omega) (by omega)]
    omega
  unfold LazyPrintOps.overallocation
  rw [ite_eq_left (show n.val < 0 by omega)]
  dsimp only
  split
  · decide
  · change wrapInt .i64 (n.val + (LazyPrintOps.i (2 ^ (64 * 7 / 8)) * LazyPrintOps.i 3 +
        LazyPrintOps.i (n.val.tdiv 8)).val) ≠ 0
    rw [he]
    change ((n.val + (3 * 2 ^ 56 + n.val.tdiv 8) + 2 ^ 63) % 2 ^ 64 - 2 ^ 63 : Int) ≠ 0
    omega

theorem lazyPrintCapSelf (cap : LazyPrintOps.I) :
    LazyPrintOps.imin LazyPrintOps.imaxval cap = cap := by
  unfold LazyPrintOps.imin
  split
  · rfl
  · rename_i hnot
    apply Subtype.ext
    have hupper := cap.property.2
    change 9223372036854775807 = cap.val
    change ¬ cap.val < 9223372036854775807 at hnot
    change cap.val ≤ 9223372036854775807 at hupper
    omega

theorem lazyPrintResizeAllocError (st : LazyPrintOps.BufferState)
    (desired cap a b : LazyPrintOps.I) (next : LazyPrintOps.BufferState) (err : LazyPrintOps.IOErr)
    (hcap : LazyPrintOps.imin st.maxsize (LazyPrintOps.overallocation desired) = cap)
    (hspan : LazyPrintOps.getUsedSpan st = .ok (a, b))
    (halloc : LazyPrintOps.similarData st cap = .error err)
    (hresult : (LazyPrintOps.resize desired false).run st = .ok () next) : False := by
  unfold LazyPrintOps.resize at hresult
  generalize LazyPrintOps.similarData = allocateData at halloc hresult
  simp only [EStateM.run, Bind.bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, Bool.false_eq_true, ↓reduceIte,
    hcap, hspan, LazyPrintOps.lift, Pure.pure, EStateM.pure, halloc,
    EStateM.throw] at hresult
  cases hresult

theorem lazyPrintResizeCopyError (st : LazyPrintOps.BufferState)
    (desired cap a b used : LazyPrintOps.I) (fresh : List UInt8)
    (next : LazyPrintOps.BufferState) (err : LazyPrintOps.IOErr)
    (hcap : LazyPrintOps.imin st.maxsize (LazyPrintOps.overallocation desired) = cap)
    (hspan : LazyPrintOps.getUsedSpan st = .ok (a, b))
    (halloc : LazyPrintOps.similarData st cap = .ok fresh)
    (hnz : cap.val ≠ 0) (hused : LazyPrintOps.rangeLength a b = used)
    (hcopy : (if used.val = 0 then Except.ok fresh
      else LazyPrintOps.copyto fresh (LazyPrintOps.i 1) st.data a used) = .error err)
    (hresult : (LazyPrintOps.resize desired false).run st = .ok () next) : False := by
  unfold LazyPrintOps.resize at hresult
  generalize LazyPrintOps.copyto = copyAction at hcopy hresult
  generalize LazyPrintOps.similarData = allocateData at halloc hresult
  simp only [EStateM.run, Bind.bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, Bool.false_eq_true, ↓reduceIte,
    hcap, hspan, LazyPrintOps.lift, Pure.pure, EStateM.pure, halloc, hnz,
    hused, set, MonadStateOf.set, EStateM.set] at hresult
  by_cases hz : used.val = 0
  · simp only [hz, ↓reduceIte] at hcopy
    cases hcopy
  · simp only [hz, ↓reduceIte] at hcopy hresult
    simp only [hcopy, LazyPrintOps.lift, EStateM.throw, Bind.bind, EStateM.bind] at hresult
    cases hresult

def lazyPrintRawUnsafeWrite (signed : Int → LazyPrintOps.I) (unsigned : Int → LazyPrintOps.U)
    (maximum minimum : LazyPrintOps.I → LazyPrintOps.I → LazyPrintOps.I) (minUnsigned : LazyPrintOps.U → LazyPrintOps.U → LazyPrintOps.U)
    (toSigned : LazyPrintOps.U → LazyPrintOps.I) (toUnsigned : LazyPrintOps.I → LazyPrintOps.U)
    (offset : LazyPrintOps.BufferState → LazyPrintOps.I)
    (store : Bool → List UInt8 → LazyPrintOps.I → List UInt8 → Except LazyPrintOps.IOErr (List UInt8))
    (ensure : LazyPrintOps.U → LazyPrintOps.M Unit) (src : List UInt8) : LazyPrintOps.M LazyPrintOps.I := do
  let nb : LazyPrintOps.U := unsigned src.length
  ensure nb
  let io ← get
  let size := io.size
  let append := io.append
  let ptr := if append then size + signed 1 else io.ptr
  let start := ptr - signed 1
  let inner := minimum (signed io.data.length - start) (io.maxsize - (start - offset io))
  let toWrite := maximum (signed 0) (toSigned (minUnsigned nb (toUnsigned inner)))
  let data ← LazyPrintOps.lift (store io.isMemory io.data ptr (src.take toWrite.val.toNat))
  set { io with data, size := maximum size (start + toWrite),
                ptr := if append then io.ptr else ptr + toWrite }
  return toWrite

theorem lazyPrintRawUnsafeWriteEq (src : List UInt8) :
    LazyPrintOps.unsafeWrite src = lazyPrintRawUnsafeWrite LazyPrintOps.i LazyPrintOps.u LazyPrintOps.imax LazyPrintOps.imin LazyPrintOps.uminU
      (JInt.rem .i64) (JInt.rem .u64) LazyPrintOps.getOffset LazyPrintOps.writeAt LazyPrintOps.ensureroom src := by
  rfl

theorem lazyPrintRawUnsafeWriteRun (signed : Int → LazyPrintOps.I) (unsigned : Int → LazyPrintOps.U)
    (maximum minimum : LazyPrintOps.I → LazyPrintOps.I → LazyPrintOps.I) (minUnsigned : LazyPrintOps.U → LazyPrintOps.U → LazyPrintOps.U)
    (toSigned : LazyPrintOps.U → LazyPrintOps.I) (toUnsigned : LazyPrintOps.I → LazyPrintOps.U)
    (offset : LazyPrintOps.BufferState → LazyPrintOps.I)
    (store : Bool → List UInt8 → LazyPrintOps.I → List UInt8 → Except LazyPrintOps.IOErr (List UInt8))
    (ensure : LazyPrintOps.U → LazyPrintOps.M Unit) (src : List UInt8)
    (io ready : LazyPrintOps.BufferState) (count : LazyPrintOps.I) (newData : List UInt8)
    (hens : (ensure (unsigned src.length)).run io = .ok () ready)
    (happend : ready.append = false)
    (hcount : maximum (signed 0) (toSigned (minUnsigned (unsigned src.length)
      (toUnsigned (minimum (signed ready.data.length - (ready.ptr - signed 1))
        (ready.maxsize - (ready.ptr - signed 1 - offset ready)))))) = count)
    (hwrite : store ready.isMemory ready.data ready.ptr
      (src.take count.val.toNat) = .ok newData) :
    (lazyPrintRawUnsafeWrite signed unsigned maximum minimum minUnsigned toSigned toUnsigned offset store ensure src).run io = .ok count
      { ready with
        data := newData
        size := maximum ready.size (ready.ptr - signed 1 + count)
        ptr := ready.ptr + count } := by
  simp only [lazyPrintRawUnsafeWrite, EStateM.run, Bind.bind, EStateM.bind] at hens ⊢
  rw [hens]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, happend,
    Bool.false_eq_true, ↓reduceIte]
  rw [hcount, hwrite]
  rfl

theorem lazyPrintUnsafeWriteResult (src : List UInt8) (io ready : LazyPrintOps.BufferState)
    (count : LazyPrintOps.I) (newData : List UInt8)
    (hens : (LazyPrintOps.ensureroom (LazyPrintOps.u src.length)).run io = .ok () ready)
    (happend : ready.append = false)
    (hcount : LazyPrintOps.imax (LazyPrintOps.i 0) (JInt.rem .i64 (LazyPrintOps.uminU (LazyPrintOps.u src.length)
      (JInt.rem .u64 (LazyPrintOps.imin (LazyPrintOps.i ready.data.length - (ready.ptr - LazyPrintOps.i 1))
        (ready.maxsize - (ready.ptr - LazyPrintOps.i 1 - LazyPrintOps.getOffset ready)))))) = count)
    (hwrite : LazyPrintOps.writeAt ready.isMemory ready.data ready.ptr
      (src.take count.val.toNat) = .ok newData) :
    (LazyPrintOps.unsafeWrite src).run io = .ok count
      { ready with
        data := newData
        size := LazyPrintOps.imax ready.size (ready.ptr - LazyPrintOps.i 1 + count)
        ptr := ready.ptr + count } := by
  rw [lazyPrintRawUnsafeWriteEq]
  exact lazyPrintRawUnsafeWriteRun LazyPrintOps.i LazyPrintOps.u LazyPrintOps.imax LazyPrintOps.imin LazyPrintOps.uminU
    (JInt.rem .i64) (JInt.rem .u64) LazyPrintOps.getOffset LazyPrintOps.writeAt LazyPrintOps.ensureroom src
    io ready count newData hens happend hcount hwrite



theorem lazyPrintWriteCount (data : List UInt8) (len n : Nat)
    (hfits : len ≤ data.length) (hcap : data.length < 2 ^ 63) (hn : n < 2 ^ 63) :
    LazyPrintOps.imax (LazyPrintOps.i 0)
      (JInt.rem .i64 (LazyPrintOps.uminU (LazyPrintOps.u n)
        (JInt.rem .u64 (LazyPrintOps.imin
          (LazyPrintOps.i data.length - (LazyPrintOps.i ((len : Int) + 1) - LazyPrintOps.i 1))
          (LazyPrintOps.imaxval - ((LazyPrintOps.i ((len : Int) + 1) - LazyPrintOps.i 1) - LazyPrintOps.i 0)))))) =
      LazyPrintOps.i ((min n (data.length - len) : Nat) : Int) := by
  rw [lazyPrintExisting data len hfits hcap]
  have hfree : (data.length : Int) - len = ((data.length - len : Nat) : Int) := by omega
  rw [hfree]
  have hr : JInt.rem .u64 (LazyPrintOps.i ((data.length - len : Nat) : Int)) =
      LazyPrintOps.u ((data.length - len : Nat) : Int) := by
    apply Subtype.ext
    change wrapInt .u64 (LazyPrintOps.i ((data.length - len : Nat) : Int)).val = _
    rw [lazyPrintIVal _ (by omega) (by omega)]
    rfl
  rw [hr]
  have hm : LazyPrintOps.uminU (LazyPrintOps.u n) (LazyPrintOps.u ((data.length - len : Nat) : Int)) =
      LazyPrintOps.u ((min n (data.length - len) : Nat) : Int) := by
    unfold LazyPrintOps.uminU
    rw [lazyPrintUVal n (by omega), lazyPrintUVal (data.length - len) (by omega)]
    split
    · rename_i hlt
      rw [Nat.min_eq_right (by omega)]
    · rename_i hlt
      rw [Nat.min_eq_left (by omega)]
  have hwsmall : min n (data.length - len) < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hn
  rw [hm, lazyPrintRemUInt _ (by omega)]
  have hwval : (LazyPrintOps.i ((min n (data.length - len) : Nat) : Int)).val =
      ((min n (data.length - len) : Nat) : Int) :=
    lazyPrintIVal _ (by omega) (by omega)
  simp only [LazyPrintOps.imax, show (LazyPrintOps.i 0).val = 0 from rfl,
    hwval, show ¬ ((min n (data.length - len) : Nat) : Int) < 0 by omega, ↓reduceIte]

theorem lazyPrintWriteAt (data src : List UInt8) (len w : Nat)
    (hfits : len ≤ data.length) (hcap : data.length < 2 ^ 63)
    (hw : w ≤ src.length) (hroom : len + w ≤ data.length) :
    LazyPrintOps.writeAt true data (LazyPrintOps.i ((len : Int) + 1)) (src.take w) =
      .ok (data.take len ++ src.take w ++ data.drop (len + w)) := by
  by_cases hz : w = 0
  · subst w
    simp only [List.take_zero, List.length_nil, LazyPrintOps.writeAt, ↓reduceIte,
      List.append_nil, List.nil_append, Nat.add_zero, List.take_append_drop]
  · have hp : (LazyPrintOps.i ((len : Int) + 1)).val = (len : Int) + 1 :=
      lazyPrintIVal _ (by omega) (by omega)
    have hl : (src.take w).length = w := by
      simp only [List.length_take, Nat.min_eq_left hw]
    unfold LazyPrintOps.writeAt
    rw [hl, ite_eq_right hz, hp, ite_eq_left (by omega)]
    have ha : ((len : Int) + 1 - 1).toNat = len := by omega
    have hb : ((len : Int) + 1 - 1 + w).toNat = len + w := by omega
    rw [ha, hb]

theorem lazyPrintWriteDataLength (data src : List UInt8) (len w : Nat)
    (hfits : len ≤ data.length) (hw : w ≤ src.length)
    (hroom : len + w ≤ data.length) :
    (data.take len ++ src.take w ++ data.drop (len + w)).length = data.length := by
  simp only [List.length_append, List.length_take, List.length_drop,
    Nat.min_eq_left hfits, Nat.min_eq_left hw]
  omega

theorem lazyPrintWriteDataPrefix (data src : List UInt8) (len w : Nat)
    (hfits : len ≤ data.length) (hw : w ≤ src.length) :
    (data.take len ++ src.take w ++ data.drop (len + w)).take (len + w) =
      data.take len ++ src.take w := by
  have hl : (data.take len ++ src.take w).length = len + w := by
    simp only [List.length_append, List.length_take, Nat.min_eq_left hfits, Nat.min_eq_left hw]
  simpa only [hl, List.append_assoc] using (List.take_append_length
    (l₁ := data.take len ++ src.take w) (l₂ := data.drop (len + w)))


theorem lazyPrintWritePost (data written : List UInt8) (len w : Nat)
    (hcap : data.length < 2 ^ 63) (hroom : len + w ≤ data.length) :
    { lazyPrintBuffer data len with
        data := written
        size := LazyPrintOps.imax (lazyPrintBuffer data len).size
          ((lazyPrintBuffer data len).ptr - LazyPrintOps.i 1 + LazyPrintOps.i w)
        ptr := (lazyPrintBuffer data len).ptr + LazyPrintOps.i w } =
      lazyPrintBuffer written (len + w) := by
  have hs : (lazyPrintBuffer data len).ptr - LazyPrintOps.i 1 + LazyPrintOps.i w =
      LazyPrintOps.i ((len + w : Nat) : Int) := by
    change LazyPrintOps.i ((len : Int) + 1) - LazyPrintOps.i 1 + LazyPrintOps.i w = _
    rw [lazyPrintISub, lazyPrintIAdd]
    apply congrArg LazyPrintOps.i
    omega
  have hp : (lazyPrintBuffer data len).ptr + LazyPrintOps.i w =
      LazyPrintOps.i (((len + w : Nat) : Int) + 1) := by
    change LazyPrintOps.i ((len : Int) + 1) + LazyPrintOps.i w = _
    rw [lazyPrintIAdd]
    apply congrArg LazyPrintOps.i
    omega
  have hm : LazyPrintOps.imax (lazyPrintBuffer data len).size (LazyPrintOps.i ((len + w : Nat) : Int)) =
      LazyPrintOps.i ((len + w : Nat) : Int) := by
    change LazyPrintOps.imax (LazyPrintOps.i len) (LazyPrintOps.i ((len + w : Nat) : Int)) = _
    have hlval : (LazyPrintOps.i len).val = (len : Int) :=
      lazyPrintIVal _ (by omega) (by omega)
    have hwval : (LazyPrintOps.i ((len + w : Nat) : Int)).val = ((len + w : Nat) : Int) :=
      lazyPrintIVal _ (by omega) (by omega)
    simp only [LazyPrintOps.imax, hlval, hwval,
      show ¬ (((len + w : Nat) : Int) < (len : Int)) by omega, ↓reduceIte]
  rw [hs, hp, hm] <;> rfl

theorem lazyPrintWriteAfterEnsure (src data : List UInt8) (len : Nat)
    (io : LazyPrintOps.BufferState) (hfits : len ≤ data.length)
    (hcap : data.length < 2 ^ 63) (hn : src.length < 2 ^ 63)
    (hens : (LazyPrintOps.ensureroom (LazyPrintOps.u src.length)).run io =
      .ok () (lazyPrintBuffer data len)) :
    (LazyPrintOps.unsafeWrite src).run io =
      .ok (LazyPrintOps.i ((min src.length (data.length - len) : Nat) : Int))
        (lazyPrintBuffer
          (data.take len ++ src.take (min src.length (data.length - len)) ++
            data.drop (len + min src.length (data.length - len)))
          (len + min src.length (data.length - len))) := by
  let w := min src.length (data.length - len)
  have hwsrc : w ≤ src.length := Nat.min_le_left _ _
  have hwroom : len + w ≤ data.length := by
    have hwfree : w ≤ data.length - len := Nat.min_le_right _ _
    omega
  have hc : LazyPrintOps.imax (LazyPrintOps.i 0)
      (JInt.rem .i64 (LazyPrintOps.uminU (LazyPrintOps.u src.length)
        (JInt.rem .u64 (LazyPrintOps.imin
          (LazyPrintOps.i (lazyPrintBuffer data len).data.length - ((lazyPrintBuffer data len).ptr - LazyPrintOps.i 1))
          ((lazyPrintBuffer data len).maxsize - ((lazyPrintBuffer data len).ptr - LazyPrintOps.i 1 -
            LazyPrintOps.getOffset (lazyPrintBuffer data len))))))) = LazyPrintOps.i w := by
    exact lazyPrintWriteCount data len src.length hfits hcap hn
  have hwrite : LazyPrintOps.writeAt (lazyPrintBuffer data len).isMemory
      (lazyPrintBuffer data len).data (lazyPrintBuffer data len).ptr
      (src.take (LazyPrintOps.i w).val.toNat) =
      .ok (data.take len ++ src.take w ++ data.drop (len + w)) := by
    rw [lazyPrintIVal _ (by omega) (by omega), Int.toNat_natCast]
    exact lazyPrintWriteAt data src len w hfits hcap hwsrc hwroom
  have h := lazyPrintUnsafeWriteResult src io (lazyPrintBuffer data len) (LazyPrintOps.i w)
    (data.take len ++ src.take w ++ data.drop (len + w)) hens rfl hc hwrite
  rw [lazyPrintWritePost data _ len w hcap hwroom] at h
  exact h

/-- A successful buffer bind resumes with the returned state. -/
theorem lazyPrintStateBindOk {A B : Type} (action : LazyPrintOps.M A)
    (next : A → LazyPrintOps.M B) (state state' : LazyPrintOps.BufferState) (value : A)
    (h : action.run state = .ok value state') :
    (action >>= next).run state = (next value).run state' := by
  simp only [EStateM.run, Bind.bind, EStateM.bind] at h ⊢
  rw [h]

/-- A failed buffer bind propagates its error and state. -/
theorem lazyPrintStateBindError {A B : Type} (action : LazyPrintOps.M A)
    (next : A → LazyPrintOps.M B) (state state' : LazyPrintOps.BufferState)
    (error : LazyPrintOps.IOErr) (h : action.run state = .error error state') :
    (action >>= next).run state = .error error state' := by
  simp only [EStateM.run, Bind.bind, EStateM.bind] at h ⊢
  rw [h]

open JuliaLean JuliaLean.base.strings.lazy

/-- The explicit zero size hint creates an empty backing buffer. -/
def lazyPrintInitialBuffer : JuliaLean.base.iobuffer.BufferState :=
  JuliaLean.base.iobuffer.newBuf [] true true true true false JuliaLean.base.iobuffer.imaxval

theorem lazyPrintInitial :
    JuliaLean.base.strings.io.newBufferState (JuliaLean.base.iobuffer.bitsConversions .i64) (some (JuliaLean.base.iobuffer.i 0)) =
      .ok lazyPrintInitialBuffer := by
  rfl

/-- The compact context changes properties, while preserving the buffer. -/
theorem lazyPrintCompactContext {E V Ty : Type} (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) :
    JuliaLean.base.show.IOContext_pairs (JuliaLean.base.strings.io.bufferPrims (E := E) (V := V) ds) a
      (JuliaLean.base.dict.fieldConv JuliaLean.base.show.Sym) (JuliaLean.base.show.boolConv a) (.plain ())
      ("compact", true) [("limit", true)] =
      (pure ⟨(), [("limit", a.ofBool true), ("compact", a.ofBool true)]⟩ :
        JuliaLean.base.strings.io.BufferShowM E (JuliaLean.base.show.IOContext Unit V)) := by
  rfl

/-- The signed byte-count representation is exact for a model String. -/
theorem lazyPrintSizeof (s : JString) :
    (JuliaLean.base.strings.io.sizeofJString s).val = (s.bytes.length : Int) := by
  change wrapInt .i64 (s.bytes.length : Int) = _
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (s.bytes.length : Int) ∧
    (s.bytes.length : Int) ≤ 9223372036854775807
  have hs := s.small
  change s.bytes.length < 4611686018427387904 at hs
  omega

/-- Reinterpreting the byte count as UInt preserves its natural value. -/
theorem lazyPrintUnsignedSize (s : JString) :
    (JInt.wrap .u64 (JuliaLean.base.strings.io.sizeofJString s).val).val.toNat = s.bytes.length := by
  have hu : (JInt.wrap .u64 (JuliaLean.base.strings.io.sizeofJString s).val).val = (s.bytes.length : Int) := by
    change wrapInt .u64 (JuliaLean.base.strings.io.sizeofJString s).val = _
    rw [lazyPrintSizeof]
    apply wrapInt_of_inRange
    change 0 ≤ (s.bytes.length : Int) ∧ (s.bytes.length : Int) ≤ 18446744073709551615
    have hs := s.small
    change s.bytes.length < 4611686018427387904 at hs
    omega
  rw [hu, Int.toNat_natCast]

/-- Lifting IOBuffer operations preserves pure results. -/
theorem lazyPrintLiftPure {E A : Type} (value : A) :
    JuliaLean.base.strings.io.liftBuffer (pure value : JuliaLean.base.iobuffer.M A) = (pure value : JuliaLean.base.strings.io.BufferShowM E A) := by
  rfl

/-- Lifting IOBuffer operations commutes with stateful composition. -/
theorem lazyPrintLiftBind {E A C : Type} (action : JuliaLean.base.iobuffer.M A) (next : A → JuliaLean.base.iobuffer.M C) :
    JuliaLean.base.strings.io.liftBuffer (action >>= next) =
      (JuliaLean.base.strings.io.liftBuffer action >>= fun value => JuliaLean.base.strings.io.liftBuffer (E := E) (next value)) := by
  funext state
  simp only [JuliaLean.base.strings.io.liftBuffer, bind, EStateM.bind]
  cases action state <;> rfl

/-- Printing a String writes exactly its byte sequence, including through an IOContext. -/
theorem lazyPrintStringAction {E V : Type} (io : JuliaLean.base.show.JIO Unit V) (s : JString) :
    (JuliaLean.base.strings.io.printStringBuffer io s : JuliaLean.base.strings.io.BufferShowM E Unit) =
      JuliaLean.base.strings.io.liftBuffer (do let _ ← JuliaLean.base.iobuffer.unsafeWrite s.bytes; pure ()) := by
  funext state
  cases io <;>
    simp only [JuliaLean.base.strings.io.printStringBuffer, JuliaLean.base.strings.io.printConcreteString, JuliaLean.base.strings.io.writeConcreteString,
      JuliaLean.base.strings.io.pointerStringPure, JuliaLean.base.strings.io.purePointerOps, JuliaLean.base.strings.io.bufferWriter, JuliaLean.base.strings.io.UnsafeWrite.forwardContext,
      JuliaLean.base.strings.io.iobufferUnsafeWrite, JuliaLean.base.show.pipe_writer, lazyPrintUnsignedSize, List.take_length,
      JuliaLean.base.strings.io.liftBuffer, bind, EStateM.bind, pure, EStateM.pure] <;>
    cases JuliaLean.base.iobuffer.unsafeWrite s.bytes state <;> rfl

/-- The String dispatch case uses the already reduced byte-writing action. -/
theorem lazyPrintArgString {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees)
    (ds : JInt64 × JInt64) (a : JuliaLean.base.show.AnyOps V Ty)
    (io : JuliaLean.base.show.JIO Unit V) (s : JString) :
    (JuliaLean.base.strings.io.printArg c ds a io (.string s) :
      JuliaLean.base.strings.io.BufferShowM E Unit) =
      JuliaLean.base.strings.io.liftBuffer
        (do let _ ← JuliaLean.base.iobuffer.unsafeWrite s.bytes; pure ()) := by
  exact lazyPrintStringAction io s

/-- Lifting a finite sequence of buffer actions preserves its order. -/
theorem lazyPrintLiftForM {E A : Type} (xs : List A) (action : A → JuliaLean.base.iobuffer.M PUnit) :
    JuliaLean.base.strings.io.liftBuffer (forM xs action) =
      forM xs (fun value => JuliaLean.base.strings.io.liftBuffer (E := E) (action value)) := by
  induction xs with
  | nil => exact lazyPrintLiftPure _
  | cons value rest ih =>
    simp only [List.forM_cons, lazyPrintLiftBind, ih]

/-- A list loop that always continues agrees with the corresponding monadic traversal. -/
theorem lazyPrintForIn {m : Type → Type} [Monad m] [LawfulMonad m] {A : Type}
    (xs : List A) (action : A → m PUnit) :
    forIn xs () (fun value state => do action value; pure (.yield state)) =
      forM xs action := by
  induction xs with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.forIn_cons, List.forM_cons, bind_assoc, pure_bind, ih]

theorem lazyPrintForInUnit {m : Type → Type} [Monad m] [LawfulMonad m] {A : Type}
    (xs : List A) (action : A → m PUnit) :
    forIn xs () (fun value _ => do action value; pure (.yield ())) =
      forM xs action := by
  induction xs with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.forIn_cons, List.forM_cons, bind_assoc, pure_bind, ih]

/-- The exact specialization of the installed part printer to String-valued parts. -/
def lazyPrintStringParts {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees)
    (ds : JInt64 × JInt64) (a : JuliaLean.base.show.AnyOps V Ty)
    (strs : List JString) (compact : Bool) (io : JuliaLean.base.show.JIO Unit V) (_ : Unit) :
    JuliaLean.base.strings.io.BufferShowM E Unit := do
  if compact then
    let context ← JuliaLean.base.show.IOContext_pairs
      (JuliaLean.base.strings.io.bufferPrims (E := E) (V := V) ds) a
      (JuliaLean.base.dict.fieldConv JuliaLean.base.show.Sym)
      (JuliaLean.base.show.boolConv a) io ("compact", true) [("limit", true)]
    for part in strs.map (fun s => (JuliaLean.base.strings.io.StrArg.string s : JuliaLean.base.strings.io.StrArg E V)) do
      JuliaLean.base.strings.io.printArg c ds a (.context context) part
  else
    for part in strs.map (fun s => (JuliaLean.base.strings.io.StrArg.string s : JuliaLean.base.strings.io.StrArg E V)) do
      JuliaLean.base.strings.io.printArg c ds a io part

/-- The String-only printing loop is the lifted sequence of byte writes. -/
theorem lazyPrintPartsStrings {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees)
    (ds : JInt64 × JInt64) (a : JuliaLean.base.show.AnyOps V Ty) (strs : List JString)
    (compact : Bool) :
    lazyPrintStringParts (E := E) c ds a strs compact (.plain ()) () =
    JuliaLean.base.strings.io.liftBuffer (forM strs (fun s => do let _ ← JuliaLean.base.iobuffer.unsafeWrite s.bytes; pure ())) := by
  cases compact <;>
    simp only [lazyPrintStringParts, Bool.false_eq_true, ite_false, ite_true,
      lazyPrintCompactContext, pure_bind, bind_pure_unit, lazyPrintForIn, lazyPrintForInUnit, List.forM_map, lazyPrintArgString,
      ← lazyPrintLiftForM]

/-- Byte writes followed by the installed takestring operation. -/
def lazyPrintBufferProgram (strs : List JString) : JuliaLean.base.iobuffer.M (List UInt8) := do
  forM strs (fun s => do let _ ← JuliaLean.base.iobuffer.unsafeWrite s.bytes; pure ())
  JuliaLean.base.iobuffer.takestring

/-- Successful String-only sprint is a successful run of the underlying byte program. -/
theorem lazyPrintSprintSuccess {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees)
    (ds : JInt64 × JInt64) (a : JuliaLean.base.show.AnyOps V Ty) (strs : List JString)
    (compact : Bool) (printed : JuliaLean.base.strings.io.JuliaString)
    (h : JuliaLean.base.strings.io.sprintIOBuffer (Args := Unit) (JuliaLean.base.iobuffer.bitsConversions .i64) ds a JuliaLean.base.strings.io.SprintContext.none
      (JuliaLean.base.iobuffer.i 0) (lazyPrintStringParts (E := E) c ds a strs compact) () = .ok printed) :
    ∃ finalState, (lazyPrintBufferProgram strs).run lazyPrintInitialBuffer =
      .ok printed.bytes finalState := by
  unfold JuliaLean.base.strings.io.sprintIOBuffer at h
  rw [lazyPrintInitial] at h
  change (match ((lazyPrintStringParts (E := E) c ds a strs compact (.plain ()) () >>=
      fun _ => JuliaLean.base.strings.io.liftBuffer JuliaLean.base.iobuffer.takestring)
        lazyPrintInitialBuffer) with
    | .ok bytes _ => Except.ok (⟨bytes⟩ : JuliaLean.base.strings.io.JuliaString)
    | .error error _ => Except.error error) = .ok printed at h
  rw [lazyPrintPartsStrings, ← lazyPrintLiftBind] at h
  change (match JuliaLean.base.strings.io.liftBuffer (E := E) (lazyPrintBufferProgram strs) lazyPrintInitialBuffer with
    | .ok bytes _ => Except.ok (⟨bytes⟩ : JuliaLean.base.strings.io.JuliaString)
    | .error error _ => Except.error error) = .ok printed at h
  cases hb : (lazyPrintBufferProgram strs).run lazyPrintInitialBuffer with
  | error error finalState =>
    simp only [EStateM.run] at hb
    simp only [JuliaLean.base.strings.io.liftBuffer, hb] at h
    cases h
  | ok bytes finalState =>
    simp only [EStateM.run] at hb
    simp only [JuliaLean.base.strings.io.liftBuffer, hb] at h
    have hp := congrArg JuliaLean.base.strings.io.JuliaString.bytes (Except.ok.inj h)
    change bytes = printed.bytes at hp
    exact ⟨finalState, by rw [hp]⟩

end JuliaLean.ChatGPT.Batch4.Group21
namespace JuliaLean.ChatGPT.Batch8.Group13
universe u

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

open JuliaLean JuliaLean.base.strings.lazy JuliaLean.Proofs.base.strings.lazy
open JuliaLean.ChatGPT.Batch4.Group21

/-- Keep the source wrapper's matcher abstract until its result is specialized. -/
theorem lazyLastindexForwards {E V Ty : Type}
    (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : JuliaLean.base.show.AnyOps V Ty) (l : LazyString CellRef E V)
    (result : JString → JuliaLean.base.strings.string.StringResult Index) :
    Forwards c ds a l (fun str => (result str).mapError LazyError.string)
      (toString lazyFields c ds a l >>= fun str =>
        @JuliaLean.base.strings.lazy.lastindex.match_1
          (fun _ => M LazyHeap E Index) (result str)
          (fun value => pure value) (fun error => throw (LazyError.string error))) := by
  apply lazyForwardsBind
  intro str heap
  delta JuliaLean.base.strings.lazy.lastindex.match_1
  cases result str <;> rfl

/-- lastindex follows the materialized String result and preserves its error. -/
theorem StringscovaLazyLastindexFaithful_proven : JuliaLean.Proofs.base.strings.lazy.LastindexProperty := by
  intro E V Ty c ds a l
  exact lazyLastindexForwards c ds a l
    (JuliaLean.base.strings.string.lastindexString
      JuliaLean.base.strings.string.stringNcodeunits
      JuliaLean.base.strings.string.stringBetweenIndex
      JuliaLean.base.strings.string.stringBetweenByte
      JuliaLean.base.strings.string.stringCodeunitAt)

/-- Combine lastindex with the ten installed forwarding contracts. -/
theorem StringscovaLazyForwarders_proven : JuliaLean.Proofs.base.strings.lazy.ForwardingContract := by
  exact ⟨StringscovaLazyHashFaithful_proven, StringscovaLazyLastindexFaithful_proven,
    StringscovaLazyIterate0Faithful_proven, StringscovaLazyIterateFaithful_proven,
    StringscovaLazyIsequalFaithful_proven, StringscovaLazyEqFaithful_proven,
    StringscovaLazyNcodeunitsFaithful_proven, StringscovaLazyCodeunitTypeFaithful_proven,
    StringscovaLazyCodeunitFaithful_proven, StringscovaLazyCodeunitsFaithful_proven,
    StringscovaLazyIsvalidFaithful_proven⟩

end JuliaLean.ChatGPT.Batch8.Group13

namespace JuliaLean.Proofs.base.strings.lazy

open JuliaLean.Registry

/-- Registry entries for the source-mirrored methods in `base/strings/lazy.jl`. -/
def entries : List Entry := [
  { id := "stringscova-lazy-construction", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["_LazyString(parts, str)", "LazyString(args...; compact::Bool=false)", "lazy_str(text, flags...)"]
    statement := "The public constructor preserves the captured parts and compact setting and starts uncached, `_LazyString` stores the given cache (for arguments already of the field types), and the macro parses interpolation parts while accepting only the empty or c flag tuple."
    source := "base/strings/lazy.jl:36-43,45-87"
    status := .proven, prop := ``ConstructionContract, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyConstruction_proven },
  { id := "stringscova-lazy-materialization", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["String(::LazyString)"]
    statement := "For a lazy string whose parts are Strings, a successful String conversion returns their bytes left to right and stores that String in the cache (restricted to parts that do not force the same lazy string and to String parts)."
    source := "base/strings/lazy.jl:1-35,89-101"
    status := .todo, prop := ``MaterializationContract, notes := "The complete buffer-growth, allocation and materialization contract remains unproved." },
  { id := "stringscova-lazy-forwarders", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["hash(::LazyString, ::UInt64)", "lastindex(::LazyString)", "iterate(::LazyString)", "iterate(::LazyString, ::Integer)", "isequal(::LazyString, ::LazyString)", "==(::LazyString, ::LazyString)", "ncodeunits(::LazyString)", "codeunit(::LazyString)", "codeunit(::LazyString, ::Integer)", "codeunits(::LazyString)", "isvalid(::LazyString, ::Integer)"]
    statement := "Hashing, iteration, indexing, equality and code-unit operations on a lazy string use the same results as those operations on its materialized String, with the same errors (index conversions for Base integer index types: BitInteger, Bool, BigInt)."
    source := "base/strings/lazy.jl:103-113"
    status := .proven, prop := ``ForwardingContract, thm := some ``JuliaLean.ChatGPT.Batch8.Group13.StringscovaLazyForwarders_proven },
  { id := "stringscova-lazy-ctor-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["LazyString(args...; compact::Bool=false)"]
    statement := "LazyString retains every supplied part and the compact flag and leaves the string cache empty."
    source := "base/strings/lazy.jl:42"
    status := .proven, prop := ``CtorProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyCtorFaithful_proven },
  { id := "stringscova-lazy-macro-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["lazy_str(text, flags...)"]
    statement := "The macro rejects every flag tuple except empty and c, parses interpolation at the following byte index using the source filename, escapes parsed expressions and records compact output."
    source := "base/strings/lazy.jl:45-87"
    status := .proven, prop := ``LazyStrProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyMacroFaithful_proven },
  { id := "stringscova-lazy-string-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["String(::LazyString)"]
    statement := "A successful String conversion caches its returned String, so every later conversion returns the same String and leaves the heap unchanged."
    source := "base/strings/lazy.jl:89-101"
    status := .proven, prop := ``ToStringProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyStringFaithful_proven },
  { id := "stringscova-lazy-hash-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["hash(::LazyString, ::UInt64)"]
    statement := "hash of a lazy string equals hash of its materialized String with the same UInt64 seed, and materialization errors propagate."
    source := "base/strings/lazy.jl:103"
    status := .proven, prop := ``HashProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyHashFaithful_proven },
  { id := "stringscova-lazy-lastindex-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["lastindex(::LazyString)"]
    statement := "lastindex of a lazy string is the last index of the eager String produced from it."
    source := "base/strings/lazy.jl:104"
    status := .proven, prop := ``LastindexProperty, thm := some ``JuliaLean.ChatGPT.Batch8.Group13.StringscovaLazyLastindexFaithful_proven },
  { id := "stringscova-lazy-iterate0-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["iterate(::LazyString)"]
    statement := "The first iteration result of a lazy string is the first iteration result of its materialized String, with materialization and iteration errors preserved."
    source := "base/strings/lazy.jl:105"
    status := .proven, prop := ``Iterate0Property, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyIterate0Faithful_proven },
  { id := "stringscova-lazy-iterate-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["iterate(::LazyString, ::Integer)"]
    statement := "Iteration at an Integer state uses that same state on the materialized String and preserves either error (for BitInteger, Bool and BigInt states)."
    source := "base/strings/lazy.jl:106"
    status := .proven, prop := ``IterateAtProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyIterateFaithful_proven },
  { id := "stringscova-lazy-isequal-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["isequal(::LazyString, ::LazyString)"]
    statement := "isequal compares the two materialized Strings in argument order and propagates the first materialization error."
    source := "base/strings/lazy.jl:107"
    status := .proven, prop := ``IsequalProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyIsequalFaithful_proven },
  { id := "stringscova-lazy-eq-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["==(::LazyString, ::LazyString)"]
    statement := "LazyString equality agrees with String equality after materializing left then right, and propagates the first materialization error."
    source := "base/strings/lazy.jl:108"
    status := .proven, prop := ``EqProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyEqFaithful_proven },
  { id := "stringscova-lazy-ncodeunits-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["ncodeunits(::LazyString)"]
    statement := "ncodeunits of a lazy string equals ncodeunits of its materialized String."
    source := "base/strings/lazy.jl:109"
    status := .proven, prop := ``NcodeunitsProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyNcodeunitsFaithful_proven },
  { id := "stringscova-lazy-codeunit-type-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunit(::LazyString)"]
    statement := "The code-unit type of a lazy string is UInt8, as for the empty String."
    source := "base/strings/lazy.jl:110"
    status := .proven, prop := ``CodeunitTypeProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyCodeunitTypeFaithful_proven },
  { id := "stringscova-lazy-codeunit-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunit(::LazyString, ::Integer)"]
    statement := "Indexed codeunit reads of a lazy string equal reads at the same Integer index from its materialized String (for BitInteger, Bool and BigInt indices)."
    source := "base/strings/lazy.jl:111"
    status := .proven, prop := ``CodeunitAtProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyCodeunitFaithful_proven },
  { id := "stringscova-lazy-codeunits-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunits(::LazyString)"]
    statement := "codeunits of a lazy string exposes the code-unit view of its materialized String."
    source := "base/strings/lazy.jl:112"
    status := .proven, prop := ``CodeunitsProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyCodeunitsFaithful_proven },
  { id := "stringscova-lazy-isvalid-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["isvalid(::LazyString, ::Integer)"]
    statement := "isvalid at an Integer index agrees with isvalid on the materialized String and preserves its errors (for BitInteger, Bool and BigInt indices)."
    source := "base/strings/lazy.jl:113"
    status := .proven, prop := ``IsvalidProperty, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.StringscovaLazyIsvalidFaithful_proven }
]

end JuliaLean.Proofs.base.strings.lazy
