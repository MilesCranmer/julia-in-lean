import JuliaLean.base.strings.lazy
import JuliaLean.Registry.Types

/-!
# Properties of `base/strings/lazy.jl`

Specifications for the source-mirrored lazy string model. A lazy string carries a heterogeneous
ordered sequence of typed values, a compact-printing flag and an optional cached eager byte string.
-/

namespace JuliaLean.Proofs.base.strings.lazy

open JuliaLean.base.strings.lazy JuliaLean.Registry

/-- `_LazyString` converts fields in order and stores successful values with compact disabled. -/
def PrivateCtorProperty : Prop :=
  ∀ {P S E : Type} (convertParts : P → Except E (List LazyPart))
    (convertCache : S → Except E (Option EagerString)) (parts : P) (str : S),
    (∀ convertedParts cached,
      convertParts parts = .ok convertedParts →
      convertCache str = .ok cached →
      _LazyString convertParts convertCache parts str =
        .ok ⟨convertedParts, false, cached⟩) ∧
    (∀ error,
      convertParts parts = .error error →
      _LazyString convertParts convertCache parts str = .error error) ∧
    (∀ convertedParts error,
      convertParts parts = .ok convertedParts →
      convertCache str = .error error →
      _LazyString convertParts convertCache parts str = .error error)

/-- Cache-free conversion agrees with eager printing and stores exactly the returned bytes. -/
def MaterializationContract : Prop :=
  ∀ {E : Type} (print : ValuePrinter E) (replace : AtomicReplace),
    (∀ lazy rendered, (replace lazy rendered).ok = false →
      (replace lazy rendered).old = rendered) →
    ∀ parts compact rendered state,
      eagerString print (if compact then compactContext else ordinaryContext) parts = .ok rendered →
      toString print replace (lazyStringCtor parts compact) = .ok (state, rendered) ∧
      state.str = some rendered

/-- A successful conversion publishes a cache; cached values bypass printing and print errors propagate. -/
def ToStringProperty : Prop :=
  ∀ {E : Type} (print : ValuePrinter E) (replace : AtomicReplace),
    (∀ lazy state rendered,
      toString print replace lazy = .ok (state, rendered) →
      state.str = some rendered ∧
      toString print replace state = .ok (state, rendered)) ∧
    (∀ (lazy : LazyString) cached,
      toString print replace {lazy with str := some cached} =
        .ok ({lazy with str := some cached}, cached)) ∧
    (∀ (lazy : LazyString) error,
      (if lazy.compact then printParts print compactContext lazy.parts
        else printParts print ordinaryContext lazy.parts) = .error error →
      toString print replace {lazy with str := none} = .error error)

/-- Hashing a lazy string uses its materialized String, unchanged seed and materialization errors. -/
def HashProperty : Prop :=
  ∀ {E : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringHash : EagerString → UInt64 → UInt64) (lazy seed),
    (∀ state rendered, toString print replace lazy = .ok (state, rendered) →
      hash print replace stringHash lazy seed = .ok (state, stringHash rendered seed)) ∧
    (∀ error, toString print replace lazy = .error error →
      hash print replace stringHash lazy seed = .error error)

/-- A lazy string has the last index of its eager String, and propagates materialization errors. -/
def LastindexProperty : Prop :=
  ∀ {E : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringLastindex : EagerString → Index) (lazy),
    (∀ state rendered, toString print replace lazy = .ok (state, rendered) →
      lastindex print replace stringLastindex lazy = .ok (state, stringLastindex rendered)) ∧
    (∀ error, toString print replace lazy = .error error →
      lastindex print replace stringLastindex lazy = .error error)

/-- The first lazy-string iteration result is the first result from the materialized String. -/
def Iterate0Property : Prop :=
  ∀ {E : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringIterate : EagerString → Except E (Option (UInt32 × Index))) (lazy state rendered),
    (∀ next, toString print replace lazy = .ok (state, rendered) →
      stringIterate rendered = .ok next →
      iterate0 print replace stringIterate lazy = .ok (state, next)) ∧
    (∀ error, toString print replace lazy = .error error →
      iterate0 print replace stringIterate lazy = .error error) ∧
    (∀ error, toString print replace lazy = .ok (state, rendered) →
      stringIterate rendered = .error error →
      iterate0 print replace stringIterate lazy = .error error)

/-- Stateful lazy-string iteration preserves the supplied Integer index and String result. -/
def IterateAtProperty : Prop :=
  ∀ {E I : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringIterate : EagerString → I → Except E (Option (UInt32 × Index)))
    (lazy state rendered index),
    (∀ next, toString print replace lazy = .ok (state, rendered) →
      stringIterate rendered index = .ok next →
      iterateAt print replace stringIterate lazy index = .ok (state, next)) ∧
    (∀ error, toString print replace lazy = .error error →
      iterateAt print replace stringIterate lazy index = .error error) ∧
    (∀ error, toString print replace lazy = .ok (state, rendered) →
      stringIterate rendered index = .error error →
      iterateAt print replace stringIterate lazy index = .error error)

/-- `isequal` materializes left then right and applies String's comparison to those results. -/
def IsequalProperty : Prop :=
  ∀ {E : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringIsequal : EagerString → EagerString → Bool) (a b : LazyString),
    (∀ error, toString print replace a = .error error →
      isequal print replace stringIsequal a b = .error error) ∧
    (∀ aState aString error, toString print replace a = .ok (aState, aString) →
      toString print replace b = .error error →
      isequal print replace stringIsequal a b = .error error) ∧
    (∀ aState bState aString bString,
      toString print replace a = .ok (aState, aString) →
      toString print replace b = .ok (bState, bString) →
      isequal print replace stringIsequal a b =
        .ok (aState, bState, stringIsequal aString bString))

/-- `==` materializes left then right and applies String equality to those results. -/
def EqProperty : Prop :=
  ∀ {E : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringEq : EagerString → EagerString → Bool) (a b : LazyString),
    (∀ error, toString print replace a = .error error →
      eq print replace stringEq a b = .error error) ∧
    (∀ aState aString error, toString print replace a = .ok (aState, aString) →
      toString print replace b = .error error →
      eq print replace stringEq a b = .error error) ∧
    (∀ aState bState aString bString,
      toString print replace a = .ok (aState, aString) →
      toString print replace b = .ok (bState, bString) →
      eq print replace stringEq a b = .ok (aState, bState, stringEq aString bString))

/-- A lazy string's code-unit count is that of its materialized String, with errors preserved. -/
def NcodeunitsProperty : Prop :=
  ∀ {E : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringNcodeunits : EagerString → Index) (lazy),
    (∀ state rendered, toString print replace lazy = .ok (state, rendered) →
      ncodeunits print replace stringNcodeunits lazy = .ok (state, stringNcodeunits rendered)) ∧
    (∀ error, toString print replace lazy = .error error →
      ncodeunits print replace stringNcodeunits lazy = .error error)

/-- `codeunit(::LazyString)` has the same code-unit type as the empty String. -/
def CodeunitTypeProperty : Prop :=
  ∀ (stringCodeunitType : EagerString → CodeUnitKind) (lazy : LazyString),
    stringCodeunitType [] = .uint8 → codeunitType stringCodeunitType lazy = .uint8

/-- Indexed code-unit reads use the materialized String and preserve the Integer index type. -/
def CodeunitAtProperty : Prop :=
  ∀ {E I : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringCodeunit : EagerString → I → Except E UInt8) (lazy state rendered index),
    (∀ byte, toString print replace lazy = .ok (state, rendered) →
      stringCodeunit rendered index = .ok byte →
      codeunitAt print replace stringCodeunit lazy index = .ok (state, byte)) ∧
    (∀ error, toString print replace lazy = .error error →
      codeunitAt print replace stringCodeunit lazy index = .error error) ∧
    (∀ error, toString print replace lazy = .ok (state, rendered) →
      stringCodeunit rendered index = .error error →
      codeunitAt print replace stringCodeunit lazy index = .error error)

/-- `codeunits` exposes the code-unit view of the materialized String and propagates print errors. -/
def CodeunitsProperty : Prop :=
  ∀ {E R : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringCodeunits : EagerString → R) (lazy),
    (∀ state rendered, toString print replace lazy = .ok (state, rendered) →
      codeunits print replace stringCodeunits lazy = .ok (state, stringCodeunits rendered)) ∧
    (∀ error, toString print replace lazy = .error error →
      codeunits print replace stringCodeunits lazy = .error error)

/-- Indexed validity checks use the materialized String and preserve String errors. -/
def IsvalidProperty : Prop :=
  ∀ {E I : Type} (print : ValuePrinter E) (replace : AtomicReplace)
    (stringIsvalid : EagerString → I → Except E Bool) (lazy state rendered index),
    (∀ valid, toString print replace lazy = .ok (state, rendered) →
      stringIsvalid rendered index = .ok valid →
      isvalid print replace stringIsvalid lazy index = .ok (state, valid)) ∧
    (∀ error, toString print replace lazy = .error error →
      isvalid print replace stringIsvalid lazy index = .error error) ∧
    (∀ error, toString print replace lazy = .ok (state, rendered) →
      stringIsvalid rendered index = .error error →
      isvalid print replace stringIsvalid lazy index = .error error)

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

/-- Constructors preserve parts and cache state, while the macro preserves parsed expansion parts. -/
def ConstructionContract : Prop :=
  (∀ parts compact,
    let lazy := lazyStringCtor parts compact
    lazy.parts = parts ∧ lazy.compact = compact ∧ lazy.str = none) ∧
  PrivateCtorProperty ∧ LazyStrProperty

/-- All documented AbstractString forwarding methods observe the cached eager String. -/
def ForwardingContract : Prop :=
  HashProperty ∧ LastindexProperty ∧ Iterate0Property ∧ IterateAtProperty ∧
  IsequalProperty ∧ EqProperty ∧ NcodeunitsProperty ∧ CodeunitTypeProperty ∧
  CodeunitAtProperty ∧ CodeunitsProperty ∧ IsvalidProperty

/-- Registry entries for the source-mirrored methods in `base/strings/lazy.jl`. -/
def entries : List Entry := [
  { id := "stringscova-lazy-construction", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["_LazyString(parts, str)", "LazyString(args...; compact::Bool=false)", "lazy_str(text, flags...)"]
    statement := "The constructor preserves the captured parts and compact setting, starts uncached, and the macro parses interpolation parts while accepting only the empty or c flag tuple."
    source := "base/strings/lazy.jl:36-43,45-87"
    status := .todo, prop := ``ConstructionContract },
  { id := "stringscova-lazy-materialization", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["String(::LazyString)"]
    statement := "For an uncached lazy string, String returns the eager left-to-right printed parts and stores those bytes in the cache."
    source := "base/strings/lazy.jl:1-35,89-101"
    status := .todo, prop := ``MaterializationContract },
  { id := "stringscova-lazy-forwarders", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["hash(::LazyString, ::UInt64)", "lastindex(::LazyString)", "iterate(::LazyString)", "iterate(::LazyString, ::Integer)", "isequal(::LazyString, ::LazyString)", "==(::LazyString, ::LazyString)", "ncodeunits(::LazyString)", "codeunit(::LazyString)", "codeunit(::LazyString, ::Integer)", "codeunits(::LazyString)", "isvalid(::LazyString, ::Integer)"]
    statement := "Hashing, iteration, indexing, equality and code-unit operations on a lazy string use the same results as those operations on its cached eager String."
    source := "base/strings/lazy.jl:103-113"
    status := .todo, prop := ``ForwardingContract },
  { id := "stringscova-lazy-ctor-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["LazyString(args...; compact::Bool=false)"]
    statement := "LazyString retains every supplied part and the compact flag and leaves the string cache empty."
    source := "base/strings/lazy.jl:42"
    status := .todo, prop := ``ConstructionContract },
  { id := "stringscova-lazy-private-ctor-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["_LazyString(parts, str)"]
    statement := "_LazyString converts parts before the cached String, propagates either conversion error and sets compact to false."
    source := "base/strings/lazy.jl:41"
    status := .todo, prop := ``PrivateCtorProperty },
  { id := "stringscova-lazy-macro-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["lazy_str(text, flags...)"]
    statement := "The macro rejects every flag tuple except empty and c, parses interpolation at the following byte index using the source filename, escapes parsed expressions and records compact output."
    source := "base/strings/lazy.jl:45-87"
    status := .todo, prop := ``LazyStrProperty },
  { id := "stringscova-lazy-string-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["String(::LazyString)"]
    statement := "A successful String conversion caches its returned bytes, so every later conversion returns the same String without printing again."
    source := "base/strings/lazy.jl:89-101"
    status := .todo, prop := ``ToStringProperty },
  { id := "stringscova-lazy-hash-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["hash(::LazyString, ::UInt64)"]
    statement := "hash of a lazy string equals hash of its materialized String with the same UInt64 seed, and materialization errors propagate."
    source := "base/strings/lazy.jl:103"
    status := .todo, prop := ``HashProperty },
  { id := "stringscova-lazy-lastindex-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["lastindex(::LazyString)"]
    statement := "lastindex of a lazy string is the last index of the eager String produced from it."
    source := "base/strings/lazy.jl:104"
    status := .todo, prop := ``LastindexProperty },
  { id := "stringscova-lazy-iterate0-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["iterate(::LazyString)"]
    statement := "The first iteration result of a lazy string is the first iteration result of its materialized String, with materialization and iteration errors preserved."
    source := "base/strings/lazy.jl:105"
    status := .todo, prop := ``Iterate0Property },
  { id := "stringscova-lazy-iterate-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["iterate(::LazyString, ::Integer)"]
    statement := "Iteration at an Integer state uses that same state on the materialized String and preserves either error."
    source := "base/strings/lazy.jl:106"
    status := .todo, prop := ``IterateAtProperty },
  { id := "stringscova-lazy-isequal-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["isequal(::LazyString, ::LazyString)"]
    statement := "isequal compares the two materialized Strings in argument order and propagates the first materialization error."
    source := "base/strings/lazy.jl:107"
    status := .todo, prop := ``IsequalProperty },
  { id := "stringscova-lazy-eq-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["==(::LazyString, ::LazyString)"]
    statement := "LazyString equality agrees with String equality after materializing left then right, and propagates the first materialization error."
    source := "base/strings/lazy.jl:108"
    status := .todo, prop := ``EqProperty },
  { id := "stringscova-lazy-ncodeunits-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["ncodeunits(::LazyString)"]
    statement := "ncodeunits of a lazy string equals ncodeunits of its materialized String."
    source := "base/strings/lazy.jl:109"
    status := .todo, prop := ``NcodeunitsProperty },
  { id := "stringscova-lazy-codeunit-type-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunit(::LazyString)"]
    statement := "The code-unit type of a lazy string is UInt8, as for the empty String."
    source := "base/strings/lazy.jl:110"
    status := .todo, prop := ``CodeunitTypeProperty },
  { id := "stringscova-lazy-codeunit-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunit(::LazyString, ::Integer)"]
    statement := "Indexed codeunit reads of a lazy string equal reads at the same Integer index from its materialized String."
    source := "base/strings/lazy.jl:111"
    status := .todo, prop := ``CodeunitAtProperty },
  { id := "stringscova-lazy-codeunits-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunits(::LazyString)"]
    statement := "codeunits of a lazy string exposes the code-unit view of its materialized String."
    source := "base/strings/lazy.jl:112"
    status := .todo, prop := ``CodeunitsProperty },
  { id := "stringscova-lazy-isvalid-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["isvalid(::LazyString, ::Integer)"]
    statement := "isvalid at an Integer index agrees with isvalid on the materialized String and preserves its errors."
    source := "base/strings/lazy.jl:113"
    status := .todo, prop := ``IsvalidProperty }
]

end JuliaLean.Proofs.base.strings.lazy
