import JuliaLean.StringsCovA.Basic

/-!
Faithful per-method models for rows rejected by the fixed review of
`base/strings/basic.jl` at Julia `bbfa0ce4150`.

An `IntegerInput` or `AbstractStringInput` records the observable dispatches
provided by an arbitrary Julia value.  This keeps conversion failures and
custom `AbstractString` behavior explicit instead of assuming `String`.
-/

namespace JuliaLean.StringsCovA.BasicRebuilt

open JuliaLean JuliaLean.Strings

@[simp] private theorem exceptOkBind (value : α) (next : α → Except ε β) :
    (Except.ok value : Except ε α).bind next = next value := rfl

@[simp] private theorem exceptErrorBind (error : ε) (next : α → Except ε β) :
    (Except.error error : Except ε α).bind next = .error error := rfl

structure IntegerInput (I : Type) where
  value : I
  isMachineInt : Bool
  toInt : SJl Int

/-! Integer fallbacks, lines 107-108, 143-144, and 156-157. -/

def codeunitInteger (s : S) (i : IntegerInput I)
    (codeunitInt : S → Int → SJl C) : SJl C :=
  if i.isMachineInt then .error (.jl (.methodError "codeunit(::AbstractString, ::Int) missing"))
  else do
    let converted ← i.toInt
    codeunitInt s converted

def isvalidInteger (s : S) (i : IntegerInput I)
    (isvalidInt : S → Int → SJl Bool) : SJl Bool :=
  if i.isMachineInt then .error (.jl (.methodError "isvalid(::AbstractString, ::Int) missing"))
  else do
    let converted ← i.toInt
    isvalidInt s converted

def iterateInteger (s : S) (i : IntegerInput I)
    (iterateInt : S → Int → SJl (Option (C × Int))) : SJl (Option (C × Int)) :=
  if i.isMachineInt then .error (.jl (.methodError "iterate(::AbstractString, ::Int) missing"))
  else do
    let converted ← i.toInt
    iterateInt s converted

def CodeunitIntegerProperty : Prop :=
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch,
    i.isMachineInt = true →
    codeunitInteger s i (dispatch : S → Int → SJl C) =
      .error (.jl (.methodError "codeunit(::AbstractString, ::Int) missing"))) ∧
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch error,
    i.isMachineInt = false → i.toInt = .error error →
    codeunitInteger s i (dispatch : S → Int → SJl C) = .error error) ∧
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch converted,
    i.isMachineInt = false → i.toInt = .ok converted →
    codeunitInteger s i (dispatch : S → Int → SJl C) = dispatch s converted)

theorem codeunitInteger_proven : CodeunitIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [codeunitInteger, bind, Except.bind, pure, Except.pure]

def IsvalidIntegerProperty : Prop :=
  (∀ (S I : Type) (s : S) (i : IntegerInput I) dispatch,
    i.isMachineInt = true →
    isvalidInteger s i (dispatch : S → Int → SJl Bool) =
      .error (.jl (.methodError "isvalid(::AbstractString, ::Int) missing"))) ∧
  (∀ (S I : Type) (s : S) (i : IntegerInput I) dispatch error,
    i.isMachineInt = false → i.toInt = .error error →
    isvalidInteger s i (dispatch : S → Int → SJl Bool) = .error error) ∧
  (∀ (S I : Type) (s : S) (i : IntegerInput I) dispatch converted,
    i.isMachineInt = false → i.toInt = .ok converted →
    isvalidInteger s i (dispatch : S → Int → SJl Bool) = dispatch s converted)

theorem isvalidInteger_proven : IsvalidIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [isvalidInteger, bind, Except.bind, pure, Except.pure]

def IterateIntegerProperty : Prop :=
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch,
    i.isMachineInt = true →
    iterateInteger s i (dispatch : S → Int → SJl (Option (C × Int))) =
      .error (.jl (.methodError "iterate(::AbstractString, ::Int) missing"))) ∧
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch error,
    i.isMachineInt = false → i.toInt = .error error →
    iterateInteger s i (dispatch : S → Int → SJl (Option (C × Int))) = .error error) ∧
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch converted,
    i.isMachineInt = false → i.toInt = .ok converted →
    iterateInteger s i (dispatch : S → Int → SJl (Option (C × Int))) = dispatch s converted)

theorem iterateInteger_proven : IterateIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [iterateInteger, bind, Except.bind, pure, Except.pure]

/-! Scalar calls and bounds checks, lines 178-213. -/

structure AbstractStringInput (S : Type) where
  value : S
  ncodeunits : SJl Int
  codeunitSize : SJl Int
  firstindex : SJl Int

def sizeofString (s : AbstractStringInput S) : SJl Int := do
  let count ← s.ncodeunits
  let unitSize ← s.codeunitSize
  return count * unitSize

def SizeofProperty : Prop :=
  (∀ (S : Type) (s : AbstractStringInput S) count unitSize,
    s.ncodeunits = .ok count → s.codeunitSize = .ok unitSize →
    sizeofString s = .ok (count * unitSize)) ∧
  (∀ (S : Type) (s : AbstractStringInput S) error,
    s.ncodeunits = .error error → sizeofString s = .error error) ∧
  (∀ (S : Type) (s : AbstractStringInput S) count error,
    s.ncodeunits = .ok count → s.codeunitSize = .error error →
    sizeofString s = .error error)

theorem sizeof_proven : SizeofProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [sizeofString, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

def lastindexString (s : AbstractStringInput S)
    (thisind : S → Int → SJl Int) : SJl Int := do
  let count ← s.ncodeunits
  thisind s.value count

def LastindexProperty : Prop :=
  (∀ (S : Type) (s : AbstractStringInput S) thisind count,
    s.ncodeunits = .ok count →
    lastindexString s thisind = thisind s.value count) ∧
  (∀ (S : Type) (s : AbstractStringInput S) thisind error,
    s.ncodeunits = .error error →
    lastindexString s thisind = .error error)

theorem lastindex_proven : LastindexProperty := by
  constructor <;> intros <;>
    simp_all [lastindexString, bind, Except.bind, pure, Except.pure]

def isemptyString (s : AbstractStringInput S) : SJl Bool := do
  let count ← s.ncodeunits
  return count == 0

def IsEmptyProperty : Prop :=
  (∀ (S : Type) (s : AbstractStringInput S) count,
    s.ncodeunits = .ok count → isemptyString s = .ok (count == 0)) ∧
  (∀ (S : Type) (s : AbstractStringInput S) error,
    s.ncodeunits = .error error → isemptyString s = .error error)

theorem isempty_proven : IsEmptyProperty := by
  constructor <;> intros <;>
    simp_all [isemptyString, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

def firstString (s : AbstractStringInput S)
    (getindex : S → Int → SJl C) : SJl C := do
  let index ← s.firstindex
  getindex s.value index

def FirstProperty : Prop :=
  (∀ (S C : Type) (s : AbstractStringInput S) getindex index,
    s.firstindex = .ok index →
    firstString s (getindex : S → Int → SJl C) = getindex s.value index) ∧
  (∀ (S C : Type) (s : AbstractStringInput S) getindex error,
    s.firstindex = .error error →
    firstString s (getindex : S → Int → SJl C) = .error error)

theorem first_proven : FirstProperty := by
  constructor <;> intros <;>
    simp_all [firstString, bind, Except.bind, pure, Except.pure]

structure ScalarIndexCalls (C : Type) where
  checkbounds : SJl Unit
  isvalid : SJl Bool
  iterate : SJl (C × Int)
  stringIndexError : SJl C

def getindexInteger (calls : ScalarIndexCalls C) : SJl C := do
  let _ ← calls.checkbounds
  let valid ← calls.isvalid
  if valid then
    let pair ← calls.iterate
    return pair.1
  else calls.stringIndexError

def GetindexIntegerProperty : Prop :=
  (∀ (C : Type) (calls : ScalarIndexCalls C) error,
    calls.checkbounds = .error error → getindexInteger calls = .error error) ∧
  (∀ (C : Type) (calls : ScalarIndexCalls C) error,
    calls.checkbounds = .ok () → calls.isvalid = .error error →
    getindexInteger calls = .error error) ∧
  (∀ (C : Type) (calls : ScalarIndexCalls C),
    calls.checkbounds = .ok () → calls.isvalid = .ok false →
    getindexInteger calls = calls.stringIndexError) ∧
  (∀ (C : Type) (calls : ScalarIndexCalls C) character next,
    calls.checkbounds = .ok () → calls.isvalid = .ok true →
    calls.iterate = .ok (character, next) → getindexInteger calls = .ok character)

theorem getindexInteger_proven : GetindexIntegerProperty := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [getindexInteger, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

structure IndexVectorInput (I : Type) where
  length : SJl Nat
  values : SJl (List I)

def collectIndices (getindex : I → SJl C) : List I → SJl (List C)
  | [] => .ok []
  | index :: rest => do
      let character ← getindex index
      let characters ← collectIndices getindex rest
      return character :: characters

def getindexVector (v : IndexVectorInput I)
    (getindex : I → SJl C) : SJl (List C) := do
  let _sizehint ← v.length
  let indices ← v.values
  collectIndices getindex indices

def GetindexVectorProperty : Prop :=
  (∀ (I C : Type) (v : IndexVectorInput I) getindex error,
    v.length = .error error →
    getindexVector v (getindex : I → SJl C) = .error error) ∧
  (∀ (I C : Type) (v : IndexVectorInput I) getindex size error,
    v.length = .ok size → v.values = .error error →
    getindexVector v (getindex : I → SJl C) = .error error) ∧
  (∀ (I C : Type) (v : IndexVectorInput I) getindex size indices,
    v.length = .ok size → v.values = .ok indices →
    getindexVector v (getindex : I → SJl C) = collectIndices getindex indices)

theorem getindexVector_proven : GetindexVectorProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [getindexVector, bind, Except.bind, pure, Except.pure]

structure GetCalls (A : Type) where
  checkbounds : SJl Bool
  getindex : SJl A

def getDefault (calls : GetCalls A) (default : A) : SJl A := do
  let inbounds ← calls.checkbounds
  if inbounds then calls.getindex else return default

def GetProperty : Prop :=
  (∀ (A : Type) (calls : GetCalls A) default error,
    calls.checkbounds = .error error → getDefault calls default = .error error) ∧
  (∀ (A : Type) (calls : GetCalls A) default,
    calls.checkbounds = .ok false → getDefault calls default = .ok default) ∧
  (∀ (A : Type) (calls : GetCalls A) default,
    calls.checkbounds = .ok true → getDefault calls default = calls.getindex)

theorem get_proven : GetProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [getDefault, bind, Except.bind, pure, Except.pure]

structure BoundsIndex (I : Type) where
  value : I
  oneLe : SJl Bool
  leCodeunits : Int → SJl Bool

def checkboundsIndex (s : AbstractStringInput S) (i : BoundsIndex I) : SJl Bool := do
  let lower ← i.oneLe
  if !lower then return false
  let count ← s.ncodeunits
  i.leCodeunits count

def CheckboundsIndexProperty : Prop :=
  (∀ (S I : Type) (s : AbstractStringInput S) (i : BoundsIndex I),
    i.oneLe = .ok false → checkboundsIndex s i = .ok false) ∧
  (∀ (S I : Type) (s : AbstractStringInput S) (i : BoundsIndex I) count,
    i.oneLe = .ok true → s.ncodeunits = .ok count →
    checkboundsIndex s i = i.leCodeunits count) ∧
  (∀ (S I : Type) (s : AbstractStringInput S) (i : BoundsIndex I) error,
    i.oneLe = .error error → checkboundsIndex s i = .error error)

theorem checkboundsIndex_proven : CheckboundsIndexProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [checkboundsIndex, bind, Except.bind, pure, Except.pure]

structure BoundsRange (I : Type) where
  isempty : SJl Bool
  minimum : SJl (BoundsIndex I)
  maximum : SJl (BoundsIndex I)

def checkboundsRange (s : AbstractStringInput S) (r : BoundsRange I) : SJl Bool := do
  let empty ← r.isempty
  if empty then return true
  let lo ← r.minimum
  let lower ← lo.oneLe
  if !lower then return false
  let hi ← r.maximum
  let count ← s.ncodeunits
  hi.leCodeunits count

def CheckboundsRangeProperty : Prop :=
  (∀ (S I : Type) (s : AbstractStringInput S) (r : BoundsRange I),
    r.isempty = .ok true → checkboundsRange s r = .ok true) ∧
  (∀ (S I : Type) (s : AbstractStringInput S) (r : BoundsRange I) lo,
    r.isempty = .ok false → r.minimum = .ok lo → lo.oneLe = .ok false →
    checkboundsRange s r = .ok false) ∧
  (∀ (S I : Type) (s : AbstractStringInput S) (r : BoundsRange I) lo hi count,
    r.isempty = .ok false → r.minimum = .ok lo → lo.oneLe = .ok true →
    r.maximum = .ok hi → s.ncodeunits = .ok count →
    checkboundsRange s r = hi.leCodeunits count)

theorem checkboundsRange_proven : CheckboundsRangeProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [checkboundsRange, bind, Except.bind, pure, Except.pure]

def checkboundsArrayLoop (check : I → SJl Bool) : List I → SJl Bool
  | [] => .ok true
  | index :: rest => do
      let inbounds ← check index
      if inbounds then checkboundsArrayLoop check rest else return false

def checkboundsArray (values : SJl (List I))
    (check : I → SJl Bool) : SJl Bool := do
  let indices ← values
  checkboundsArrayLoop check indices

def CheckboundsArrayProperty : Prop :=
  (∀ (I : Type) values check error,
    values = .error error →
    checkboundsArray values (check : I → SJl Bool) = .error error) ∧
  (∀ (I : Type) values check indices,
    values = .ok indices →
    checkboundsArray values (check : I → SJl Bool) = checkboundsArrayLoop check indices)

theorem checkboundsArray_proven : CheckboundsArrayProperty := by
  constructor <;> intros <;>
    simp_all [checkboundsArray, bind, Except.bind, pure, Except.pure]

def checkboundsThrow (s : S) (indices : I) (check : SJl Bool) : SJl Unit := do
  let inbounds ← check
  if inbounds then return () else .error (.jl .boundsError)

def CheckboundsThrowProperty : Prop :=
  (∀ (S I : Type) (s : S) (indices : I),
    checkboundsThrow s indices (.ok true) = .ok ()) ∧
  (∀ (S I : Type) (s : S) (indices : I),
    checkboundsThrow s indices (.ok false) = .error (.jl .boundsError)) ∧
  (∀ (S I : Type) (s : S) (indices : I) error,
    checkboundsThrow s indices (.error error) = .error error)

theorem checkboundsThrow_proven : CheckboundsThrowProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

/-! Construction, conversion, summary, and concatenation, lines 220-271. -/

structure ByteConversionInput (S : Type) where
  value : S
  string : SJl JStr

def vectorUInt8 (s : ByteConversionInput S)
    (unsafeWrap : JStr → SJl (List UInt8)) : SJl (List UInt8) := do
  let concrete ← s.string
  unsafeWrap concrete

def arrayUInt8 (s : ByteConversionInput S)
    (unsafeWrap : JStr → SJl (List UInt8)) : SJl (List UInt8) := do
  let concrete ← s.string
  unsafeWrap concrete

def VectorUInt8Property : Prop :=
  (∀ (S : Type) (s : ByteConversionInput S) unsafeWrap error,
    s.string = .error error →
    vectorUInt8 s unsafeWrap = .error error) ∧
  (∀ (S : Type) (s : ByteConversionInput S) unsafeWrap concrete,
    s.string = .ok concrete →
    vectorUInt8 s unsafeWrap = unsafeWrap concrete)

theorem vectorUInt8_proven : VectorUInt8Property := by
  constructor <;> intros <;>
    simp_all [vectorUInt8, bind, Except.bind, pure, Except.pure]

def ArrayUInt8Property : Prop :=
  (∀ (S : Type) (s : ByteConversionInput S) unsafeWrap error,
    s.string = .error error →
    arrayUInt8 s unsafeWrap = .error error) ∧
  (∀ (S : Type) (s : ByteConversionInput S) unsafeWrap concrete,
    s.string = .ok concrete →
    arrayUInt8 s unsafeWrap = unsafeWrap concrete)

theorem arrayUInt8_proven : ArrayUInt8Property := by
  constructor <;> intros <;>
    simp_all [arrayUInt8, bind, Except.bind, pure, Except.pure]

def vectorAbstractChar (s : S) (collect : S → SJl (List C)) : SJl (List C) :=
  collect s

def VectorAbstractCharProperty : Prop := ∀ (S C : Type) (s : S) collect,
  vectorAbstractChar s (collect : S → SJl (List C)) = collect s

theorem vectorAbstractChar_proven : VectorAbstractCharProperty := by
  unfold VectorAbstractCharProperty
  intros
  rfl

structure SymbolStringInput (S Sym : Type) where
  value : S
  string : SJl JStr
  intern : JStr → SJl Sym

def symbolAbstractString (s : SymbolStringInput S Sym) : SJl Sym := do
  let concrete ← s.string
  s.intern concrete

def SymbolAbstractStringProperty : Prop :=
  (∀ (S Sym : Type) (s : SymbolStringInput S Sym) error,
    s.string = .error error → symbolAbstractString s = .error error) ∧
  (∀ (S Sym : Type) (s : SymbolStringInput S Sym) concrete,
    s.string = .ok concrete → symbolAbstractString s = s.intern concrete)

theorem symbolAbstractString_proven : SymbolAbstractStringProperty := by
  constructor <;> intros <;>
    simp_all [symbolAbstractString, bind, Except.bind, pure, Except.pure]

structure SymbolArgsInput (Args Sym : Type) where
  values : Args
  render : Args → SJl JStr
  intern : JStr → SJl Sym

def symbolArgs (args : SymbolArgsInput Args Sym) : SJl Sym := do
  let rendered ← args.render args.values
  args.intern rendered

def SymbolArgsProperty : Prop :=
  (∀ (Args Sym : Type) (args : SymbolArgsInput Args Sym) error,
    args.render args.values = .error error → symbolArgs args = .error error) ∧
  (∀ (Args Sym : Type) (args : SymbolArgsInput Args Sym) rendered,
    args.render args.values = .ok rendered → symbolArgs args = args.intern rendered)

theorem symbolArgs_proven : SymbolArgsProperty := by
  constructor <;> intros <;>
    simp_all [symbolArgs, bind, Except.bind, pure, Except.pure]

structure ConvertInput (S T : Type) where
  value : S
  construct : S → SJl T
  typeAssert : T → SJl T

def convertAbstractString (input : ConvertInput S T) : SJl T := do
  let converted ← input.construct input.value
  input.typeAssert converted

def ConvertProperty : Prop :=
  (∀ (S T : Type) (input : ConvertInput S T) error,
    input.construct input.value = .error error →
    convertAbstractString input = .error error) ∧
  (∀ (S T : Type) (input : ConvertInput S T) converted,
    input.construct input.value = .ok converted →
    convertAbstractString input = input.typeAssert converted)

theorem convert_proven : ConvertProperty := by
  constructor <;> intros <;>
    simp_all [convertAbstractString, bind, Except.bind, pure, Except.pure]

structure SummaryInput (S : Type) where
  value : S
  isempty : SJl Bool
  ncodeunits : SJl Int
  typeName : String
  print : List String → SJl Unit

def summary (input : SummaryInput S) : SJl Unit := do
  let empty ← input.isempty
  let summaryPrefix ← (if empty then .ok "empty" else do
      let count ← input.ncodeunits
      return toString count ++ "-codeunit")
  input.print [summaryPrefix, " ", input.typeName]

def SummaryProperty : Prop :=
  (∀ (S : Type) (input : SummaryInput S),
    input.isempty = .ok true →
    summary input = input.print ["empty", " ", input.typeName]) ∧
  (∀ (S : Type) (input : SummaryInput S) count,
    input.isempty = .ok false → input.ncodeunits = .ok count →
    summary input = input.print [toString count ++ "-codeunit", " ", input.typeName]) ∧
  (∀ (S : Type) (input : SummaryInput S) error,
    input.isempty = .error error → summary input = .error error)

theorem summary_proven : SummaryProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [summary, bind, Except.bind, pure, Except.pure]

def anyAnnotated : List (SJl Bool) → SJl Bool
  | [] => .ok false
  | result :: rest => do
      let annotated ← result
      if annotated then return true else anyAnnotated rest

structure ConcatInput (A R : Type) where
  first : A
  rest : List A
  firstAnnotated : SJl Bool
  restAnnotated : List (SJl Bool)
  annotatedstring : A → List A → SJl R
  string : A → List A → SJl R

def concat (input : ConcatInput A R) : SJl R := do
  let firstAnnotated ← input.firstAnnotated
  let annotated ← if firstAnnotated then .ok true else anyAnnotated input.restAnnotated
  if annotated then input.annotatedstring input.first input.rest
  else input.string input.first input.rest

def ConcatProperty : Prop :=
  (∀ (A R : Type) (input : ConcatInput A R),
    input.firstAnnotated = .ok true →
    concat input = input.annotatedstring input.first input.rest) ∧
  (∀ (A R : Type) (input : ConcatInput A R),
    input.firstAnnotated = .ok false → anyAnnotated input.restAnnotated = .ok true →
    concat input = input.annotatedstring input.first input.rest) ∧
  (∀ (A R : Type) (input : ConcatInput A R),
    input.firstAnnotated = .ok false → anyAnnotated input.restAnnotated = .ok false →
    concat input = input.string input.first input.rest)

theorem concat_proven : ConcatProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [concat, bind, Except.bind, pure, Except.pure]

def oneString (convert : SJl T) : SJl T := convert

def OneProperty : Prop := ∀ (T : Type) (converted : SJl T), oneString converted = converted
theorem one_proven : OneProperty := by
  unfold OneProperty
  intros
  rfl

inductive StringTypeKind where
  | bottom
  | annotatedString
  | annotatedChar
  | other
  deriving DecidableEq

def isannotatedType : StringTypeKind → Bool
  | .bottom => false
  | .annotatedString => true
  | .annotatedChar => true
  | .other => false

def IsannotatedTypeProperty : Prop := ∀ kind,
  isannotatedType kind =
    match kind with
    | .bottom => false
    | .annotatedString => true
    | .annotatedChar => true
    | .other => false

theorem isannotatedType_proven : IsannotatedTypeProperty := by
  intro kind
  cases kind <;> rfl

structure ValueTypeInput (V : Type) where
  value : V
  typeOf : V → StringTypeKind

def isannotatedValue (input : ValueTypeInput V) : Bool :=
  isannotatedType (input.typeOf input.value)

def IsannotatedValueProperty : Prop := ∀ (V : Type) (input : ValueTypeInput V),
  isannotatedValue input = true ↔
    input.typeOf input.value = .annotatedString ∨
    input.typeOf input.value = .annotatedChar

theorem isannotatedValue_proven : IsannotatedValueProperty := by
  intro V input
  cases h : input.typeOf input.value <;> simp [isannotatedValue, isannotatedType, h]

/-! Generic string and Symbol comparison, lines 308-363. -/

structure AbstractStringSequence (A : Type) where
  identity : Nat
  characters : List A

def cmpCharacters [DecidableEq A] (lt : A → A → Bool) : List A → List A → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a = b then cmpCharacters lt as bs else if lt a b then -1 else 1

theorem cmpCharacters_eq_zero [DecidableEq A] (lt : A → A → Bool) : ∀ a b,
    cmpCharacters lt a b = 0 ↔ a = b := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [cmpCharacters]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [cmpCharacters]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simp [cmpCharacters, ih]
          · simp [cmpCharacters, h]
            split <;> omega

def cmpString [DecidableEq A] (lt : A → A → Bool)
    (a b : AbstractStringSequence A) : Int :=
  if a.identity == b.identity then 0 else cmpCharacters lt a.characters b.characters

def CmpStringProperty : Prop := ∀ (A : Type) (_ : DecidableEq A) lt
    (a b : AbstractStringSequence A),
  cmpString lt a b = 0 ↔
    a.identity = b.identity ∨ a.characters = b.characters

theorem cmpString_proven : CmpStringProperty := by
  intro A inst lt a b
  by_cases hid : a.identity = b.identity
  · simp [cmpString, hid]
  · simp [cmpString, hid, cmpCharacters_eq_zero]

def eqString [DecidableEq A] (lt : A → A → Bool)
    (a b : AbstractStringSequence A) : Bool := cmpString lt a b == 0

def EqStringProperty : Prop := ∀ (A : Type) (_ : DecidableEq A) lt
    (a b : AbstractStringSequence A),
  eqString lt a b = true ↔ a.identity = b.identity ∨ a.characters = b.characters

theorem eqString_proven : EqStringProperty := by
  intro A inst lt a b
  simpa only [eqString, beq_iff_eq] using cmpString_proven A inst lt a b

def islessString [DecidableEq A] (lt : A → A → Bool)
    (a b : AbstractStringSequence A) : Bool := decide (cmpString lt a b < 0)

def IslessStringProperty : Prop := ∀ (A : Type) (_ : DecidableEq A) lt
    (a b : AbstractStringSequence A),
  islessString lt a b =
    if a.identity = b.identity then false
    else decide (cmpCharacters lt a.characters b.characters < 0)

theorem islessString_proven : IslessStringProperty := by
  intro A inst lt a b
  by_cases hid : a.identity = b.identity
  · simp [islessString, cmpString, hid]
  · simp [islessString, cmpString, hid]

def lexBytes : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a = b then lexBytes as bs else if a < b then -1 else 1

def cmpSymbol (a b : List UInt8) : Int := Int.sign (lexBytes a b)

def CmpSymbolProperty : Prop := ∀ a b,
  cmpSymbol a b = 0 ↔ a = b

theorem cmpSymbol_proven : CmpSymbolProperty := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [cmpSymbol, lexBytes]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [cmpSymbol, lexBytes]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simpa [cmpSymbol, lexBytes] using ih ys
          · simp [cmpSymbol, lexBytes, h]
            split <;> omega

def islessSymbol (a b : List UInt8) : Bool := decide (cmpSymbol a b < 0)

def IslessSymbolProperty : Prop := ∀ a b,
  islessSymbol a b = decide (lexBytes a b < 0)

theorem islessSymbol_proven : IslessSymbolProperty := by
  intro a b
  unfold islessSymbol cmpSymbol
  cases h : lexBytes a b <;> simp

/-! Generic length and index arithmetic, lines 396-585. -/

structure IndexStringInput (S : Type) where
  value : S
  ncodeunits : SJl JInt64
  firstindex : SJl JInt64
  lastindex : SJl JInt64

structure MachineIntegerInput (I : Type) where
  value : I
  toInt : SJl JInt64

def lengthString (s : IndexStringInput S)
    (lengthBetween : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let last ← s.ncodeunits
  lengthBetween s.value (ix 1) last

def LengthStringProperty : Prop :=
  (∀ (S : Type) (s : IndexStringInput S) lengthBetween error,
    s.ncodeunits = .error error →
    lengthString s lengthBetween = .error error) ∧
  (∀ (S : Type) (s : IndexStringInput S) lengthBetween last,
    s.ncodeunits = .ok last →
    lengthString s lengthBetween = lengthBetween s.value (ix 1) last)

theorem lengthString_proven : LengthStringProperty := by
  constructor <;> intros <;>
    simp_all [lengthString, bind, Except.bind, pure, Except.pure]

def indexRange (first last : JInt64) : List JInt64 :=
  if last.val < first.val then []
  else (List.range (last.val - first.val + 1).toNat).map
    (fun (offset : Nat) => first + ix (Int.ofNat offset))

def countValid (isvalid : JInt64 → SJl Bool) : List JInt64 → SJl JInt64
  | [] => .ok (ix 0)
  | index :: rest => do
      let valid ← isvalid index
      let count ← countValid isvalid rest
      return count + bInt valid

structure LengthBetweenInput (S : Type) where
  string : S
  first : JInt64
  last : JInt64
  firstCodeunits : SJl JInt64
  lastCodeunits : SJl JInt64
  isvalid : S → JInt64 → SJl Bool

def lengthBetween (input : LengthBetweenInput S) : SJl JInt64 := do
  let firstCount ← input.firstCodeunits
  if !(ix 0 < input.first && input.first ≤ firstCount + ix 1) then
    .error (.jl .boundsError)
  else
    let lastCount ← input.lastCodeunits
    if !(ix 0 ≤ input.last && input.last < lastCount + ix 1) then
      .error (.jl .boundsError)
    else countValid (input.isvalid input.string) (indexRange input.first input.last)

def LengthBetweenProperty : Prop :=
  (∀ (S : Type) (input : LengthBetweenInput S) firstCount,
    input.firstCodeunits = .ok firstCount →
    ¬(ix 0 < input.first && input.first ≤ firstCount + ix 1) →
    lengthBetween input = .error (.jl .boundsError)) ∧
  (∀ (S : Type) (input : LengthBetweenInput S) firstCount lastCount,
    input.firstCodeunits = .ok firstCount →
    ix 0 < input.first && input.first ≤ firstCount + ix 1 →
    input.lastCodeunits = .ok lastCount →
    ix 0 ≤ input.last && input.last < lastCount + ix 1 →
    lengthBetween input =
      countValid (input.isvalid input.string) (indexRange input.first input.last))

theorem lengthBetween_proven : LengthBetweenProperty := by
  constructor <;> intros <;>
    simp_all [lengthBetween, bind, Except.bind, pure, Except.pure]

def lengthInteger (s : S) (first : MachineIntegerInput I) (last : MachineIntegerInput J)
    (lengthInt : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← first.toInt
  let j ← last.toInt
  lengthInt s i j

def LengthIntegerProperty : Prop :=
  (∀ (S I J : Type) (s : S) (first : MachineIntegerInput I)
      (last : MachineIntegerInput J) lengthInt error,
    first.toInt = .error error →
    lengthInteger s first last lengthInt = .error error) ∧
  (∀ (S I J : Type) (s : S) (first : MachineIntegerInput I)
      (last : MachineIntegerInput J) lengthInt i error,
    first.toInt = .ok i → last.toInt = .error error →
    lengthInteger s first last lengthInt = .error error) ∧
  (∀ (S I J : Type) (s : S) (first : MachineIntegerInput I)
      (last : MachineIntegerInput J) lengthInt i j,
    first.toInt = .ok i → last.toInt = .ok j →
    lengthInteger s first last lengthInt = lengthInt s i j)

theorem lengthInteger_proven : LengthIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [lengthInteger, bind, Except.bind, pure, Except.pure]

def thisindInteger (s : S) (index : MachineIntegerInput I)
    (thisindInt : S → JInt64 → SJl JInt64) : SJl JInt64 := do
  let converted ← index.toInt
  thisindInt s converted

def ThisindIntegerProperty : Prop :=
  (∀ (S I : Type) (s : S) (index : MachineIntegerInput I) thisindInt error,
    index.toInt = .error error →
    thisindInteger s index thisindInt = .error error) ∧
  (∀ (S I : Type) (s : S) (index : MachineIntegerInput I) thisindInt converted,
    index.toInt = .ok converted →
    thisindInteger s index thisindInt = thisindInt s converted)

theorem thisindInteger_proven : ThisindIntegerProperty := by
  constructor <;> intros <;>
    simp_all [thisindInteger, bind, Except.bind, pure, Except.pure]

def thisindRewind (isvalid : JInt64 → SJl Bool) : Nat → JInt64 → SJl JInt64
  | 0, index => .ok index
  | fuel + 1, index =>
      if ix 1 < index then do
        let valid ← isvalid index
        if valid then return index else thisindRewind isvalid fuel (index - ix 1)
      else return index

structure ThisindInput (S : Type) where
  string : S
  index : JInt64
  ncodeunits : SJl JInt64
  isvalid : S → JInt64 → SJl Bool

def thisindInt (input : ThisindInput S) : SJl JInt64 := do
  let count ← input.ncodeunits
  let after := count + ix 1
  if input.index == after then return input.index
  if !(ix 0 ≤ input.index && input.index ≤ after) then .error (.jl .boundsError)
  else thisindRewind (input.isvalid input.string) input.index.val.toNat input.index

def ThisindIntProperty : Prop :=
  (∀ (S : Type) (input : ThisindInput S) count,
    input.ncodeunits = .ok count → input.index.val = (count + ix 1).val →
    thisindInt input = .ok input.index) ∧
  (∀ (S : Type) (input : ThisindInput S) count,
    input.ncodeunits = .ok count → input.index.val ≠ (count + ix 1).val →
    ¬(ix 0 ≤ input.index ∧ input.index ≤ count + ix 1) →
    thisindInt input = .error (.jl .boundsError)) ∧
  (∀ (S : Type) (input : ThisindInput S) count,
    input.ncodeunits = .ok count → input.index.val ≠ (count + ix 1).val →
    ix 0 ≤ input.index ∧ input.index ≤ count + ix 1 →
    thisindInt input =
      thisindRewind (input.isvalid input.string) input.index.val.toNat input.index)

theorem thisindInt_proven : ThisindIntProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros
    simp_all [thisindInt, bind, Except.bind, pure, Except.pure]
  · intros
    simp_all [thisindInt, bind, Except.bind, pure, Except.pure]
  · intros
    simp_all [thisindInt, bind, Except.bind, pure, Except.pure]

def previndIntegerN (s : S) (index : MachineIntegerInput I) (count : MachineIntegerInput N)
    (previndInt : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← index.toInt
  let n ← count.toInt
  previndInt s i n

def previndIntegerOne (s : S) (index : MachineIntegerInput I)
    (previndInt : S → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← index.toInt
  previndInt s i

def previndOne (s : S) (index : JInt64)
    (previndIntN : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 :=
  previndIntN s index (ix 1)

def PrevindWrappersProperty : Prop :=
  (∀ (S I N : Type) (s : S) (index : MachineIntegerInput I)
      (count : MachineIntegerInput N) dispatch i n,
    index.toInt = .ok i → count.toInt = .ok n →
    previndIntegerN s index count dispatch = dispatch s i n) ∧
  (∀ (S I : Type) (s : S) (index : MachineIntegerInput I) dispatch i,
    index.toInt = .ok i →
    previndIntegerOne s index dispatch = dispatch s i) ∧
  (∀ (S : Type) (s : S) index dispatch,
    previndOne s index dispatch = dispatch s index (ix 1))

theorem previndWrappers_proven : PrevindWrappersProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [previndIntegerN, previndIntegerOne, previndOne, bind, Except.bind,
      pure, Except.pure]

def previndLoop (isvalid : JInt64 → SJl Bool) : Nat → JInt64 → JInt64 → SJl JInt64
  | 0, index, count => .ok (index - count)
  | fuel + 1, index, count =>
      if ix 0 < count && ix 1 < index then do
        let nextIndex := index - ix 1
        let valid ← isvalid nextIndex
        previndLoop isvalid fuel nextIndex (count - bInt valid)
      else return index - count

structure PrevindInput (S : Type) where
  string : S
  index : JInt64
  count : JInt64
  ncodeunits : SJl JInt64
  thisind : S → JInt64 → SJl JInt64
  isvalid : S → JInt64 → SJl Bool
  stringIndexError : SJl JInt64

def previndIntN (input : PrevindInput S) : SJl JInt64 :=
  if input.count < ix 0 then .error (.jl (.argumentError "n cannot be negative"))
  else do
    let codeunits ← input.ncodeunits
    let after := codeunits + ix 1
    if !(ix 0 < input.index && input.index ≤ after) then .error (.jl .boundsError)
    else if input.count == ix 0 then do
      let current ← input.thisind input.string input.index
      if current == input.index then return input.index else input.stringIndexError
    else previndLoop (input.isvalid input.string) input.index.val.toNat input.index input.count

def PrevindIntNProperty : Prop :=
  (∀ (S : Type) (input : PrevindInput S), input.count < ix 0 →
    previndIntN input = .error (.jl (.argumentError "n cannot be negative"))) ∧
  (∀ (S : Type) (input : PrevindInput S) codeunits,
    ¬(input.count < ix 0) → input.ncodeunits = .ok codeunits →
    ¬(ix 0 < input.index ∧ input.index ≤ codeunits + ix 1) →
    previndIntN input = .error (.jl .boundsError)) ∧
  (∀ (S : Type) (input : PrevindInput S) codeunits,
    ¬(input.count < ix 0) → input.ncodeunits = .ok codeunits →
    ix 0 < input.index ∧ input.index ≤ codeunits + ix 1 → input.count.val ≠ 0 →
    previndIntN input =
      previndLoop (input.isvalid input.string) input.index.val.toNat input.index input.count)

theorem previndIntN_proven : PrevindIntNProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros; simp_all [previndIntN]
  · intros
    simp_all [previndIntN, bind, Except.bind, pure, Except.pure]
  · intros
    simp_all [previndIntN, bind, Except.bind, pure, Except.pure]

def nextindIntegerN (s : S) (index : MachineIntegerInput I) (count : MachineIntegerInput N)
    (nextindInt : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← index.toInt
  let n ← count.toInt
  nextindInt s i n

def nextindIntegerOne (s : S) (index : MachineIntegerInput I)
    (nextindInt : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← index.toInt
  nextindInt s i (ix 1)

def nextindOne (s : S) (index : JInt64)
    (nextindIntN : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 :=
  nextindIntN s index (ix 1)

def NextindWrappersProperty : Prop :=
  (∀ (S I N : Type) (s : S) (index : MachineIntegerInput I)
      (count : MachineIntegerInput N) dispatch i n,
    index.toInt = .ok i → count.toInt = .ok n →
    nextindIntegerN s index count dispatch = dispatch s i n) ∧
  (∀ (S I : Type) (s : S) (index : MachineIntegerInput I) dispatch i,
    index.toInt = .ok i →
    nextindIntegerOne s index dispatch = dispatch s i (ix 1)) ∧
  (∀ (S : Type) (s : S) index dispatch,
    nextindOne s index dispatch = dispatch s index (ix 1))

theorem nextindWrappers_proven : NextindWrappersProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [nextindIntegerN, nextindIntegerOne, nextindOne, bind, Except.bind,
      pure, Except.pure]

def nextindLoop (isvalid : JInt64 → SJl Bool) (last : JInt64) :
    Nat → JInt64 → JInt64 → SJl JInt64
  | 0, index, count => .ok (index + count)
  | fuel + 1, index, count =>
      if ix 0 < count && index < last then do
        let nextIndex := index + ix 1
        let valid ← isvalid nextIndex
        nextindLoop isvalid last fuel nextIndex (count - bInt valid)
      else return index + count

structure NextindInput (S : Type) where
  string : S
  index : JInt64
  count : JInt64
  ncodeunits : SJl JInt64
  thisind : S → JInt64 → SJl JInt64
  isvalid : S → JInt64 → SJl Bool
  stringIndexError : SJl JInt64

def nextindIntN (input : NextindInput S) : SJl JInt64 :=
  if input.count < ix 0 then .error (.jl (.argumentError "n cannot be negative"))
  else do
    let last ← input.ncodeunits
    if !(ix 0 ≤ input.index && input.index ≤ last) then .error (.jl .boundsError)
    else
      if input.count == ix 0 then do
        let current ← input.thisind input.string input.index
        if current == input.index then return input.index else input.stringIndexError
      else
        nextindLoop (input.isvalid input.string) last
          (last.val - input.index.val).toNat input.index input.count

def NextindIntNProperty : Prop :=
  (∀ (S : Type) (input : NextindInput S), input.count < ix 0 →
    nextindIntN input = .error (.jl (.argumentError "n cannot be negative"))) ∧
  (∀ (S : Type) (input : NextindInput S) last,
    ¬(input.count < ix 0) → input.ncodeunits = .ok last →
    ¬(ix 0 ≤ input.index ∧ input.index ≤ last) →
    nextindIntN input = .error (.jl .boundsError)) ∧
  (∀ (S : Type) (input : NextindInput S) last,
    ¬(input.count < ix 0) → input.ncodeunits = .ok last →
    ix 0 ≤ input.index ∧ input.index ≤ last → input.count.val ≠ 0 →
    nextindIntN input = nextindLoop (input.isvalid input.string) last
      (last.val - input.index.val).toNat input.index input.count)

theorem nextindIntN_proven : NextindIntNProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros; simp_all [nextindIntN]
  · intros
    simp_all [nextindIntN, bind, Except.bind, pure, Except.pure]
  · intros
    simp_all [nextindIntN, bind, Except.bind, pure, Except.pure]

structure EachStringIndex (S : Type) where
  string : S

def keys (s : S) : EachStringIndex S := ⟨s⟩
def KeysProperty : Prop := ∀ (S : Type) (s : S), (keys s).string = s
theorem keys_proven : KeysProperty := by unfold KeysProperty; intros; rfl

def eachLength (index : EachStringIndex S) (length : S → SJl JInt64) : SJl JInt64 :=
  length index.string
def EachLengthProperty : Prop := ∀ (S : Type) (index : EachStringIndex S) length,
  eachLength index length = length index.string
theorem eachLength_proven : EachLengthProperty := by unfold EachLengthProperty; intros; rfl

def eachLast (index : EachStringIndex S) (lastindex : S → SJl JInt64) : SJl JInt64 :=
  lastindex index.string
def EachLastProperty : Prop := ∀ (S : Type) (index : EachStringIndex S) lastindex,
  eachLast index lastindex = lastindex index.string
theorem eachLast_proven : EachLastProperty := by unfold EachLastProperty; intros; rfl

structure EachIterateInput (S : Type) where
  index : EachStringIndex S
  state : Option JInt64
  firstindex : S → SJl JInt64
  ncodeunits : S → SJl JInt64
  nextind : S → JInt64 → SJl JInt64

def eachIterate (input : EachIterateInput S) : SJl (Option (JInt64 × JInt64)) := do
  let state ← match input.state with
    | some state => .ok state
    | none => input.firstindex input.index.string
  let last ← input.ncodeunits input.index.string
  if last < state then return none
  let next ← input.nextind input.index.string state
  return some (state, next)

def EachIterateProperty : Prop :=
  (∀ (S : Type) (input : EachIterateInput S) state last,
    input.state = some state → input.ncodeunits input.index.string = .ok last →
    last < state → eachIterate input = .ok none) ∧
  (∀ (S : Type) (input : EachIterateInput S) state last,
    input.state = some state → input.ncodeunits input.index.string = .ok last →
    ¬(last < state) → eachIterate input = do
      let next ← input.nextind input.index.string state
      return some (state, next))

theorem eachIterate_proven : EachIterateProperty := by
  constructor <;> intros <;>
    simp_all [eachIterate, bind, Except.bind, pure, Except.pure]

/-! ASCII classification, lines 619-653. -/

def allAscii (isascii : C → SJl Bool) : List C → SJl Bool
  | [] => .ok true
  | character :: rest => do
      let ascii ← isascii character
      if ascii then allAscii isascii rest else return false

structure AsciiStringInput (C : Type) where
  characters : SJl (List C)
  isascii : C → SJl Bool

def isasciiString (input : AsciiStringInput C) : SJl Bool := do
  let characters ← input.characters
  allAscii input.isascii characters

def IsasciiStringProperty : Prop :=
  (∀ (C : Type) (input : AsciiStringInput C) error,
    input.characters = .error error → isasciiString input = .error error) ∧
  (∀ (C : Type) (input : AsciiStringInput C) characters,
    input.characters = .ok characters →
    isasciiString input = allAscii input.isascii characters)

theorem isasciiString_proven : IsasciiStringProperty := by
  constructor <;> intros <;>
    simp_all [isasciiString, bind, Except.bind, pure, Except.pure]

def isasciiAbstractChar (toUInt32 : SJl UInt32) : SJl Bool := do
  let value ← toUInt32
  return value < 0x80

def IsasciiAbstractCharProperty : Prop :=
  (∀ value, isasciiAbstractChar (.ok value) = .ok (value < 0x80)) ∧
  (∀ error, isasciiAbstractChar (.error error) = .error error)

theorem isasciiAbstractChar_proven : IsasciiAbstractCharProperty := by
  constructor <;> intros <;> rfl

structure CodeUnitOps (CU V : Type) where
  vector : V
  zero : CU
  or : CU → CU → CU
  nonnegative : CU → Bool
  below80 : CU → Bool
  getindex : V → JInt64 → SJl CU

def isasciiRangeLoop (ops : CodeUnitOps CU V) (last : JInt64) :
    Nat → JInt64 → CU → SJl CU
  | 0, _, aggregate => .ok aggregate
  | fuel + 1, index, aggregate =>
      if last < index then .ok aggregate
      else do
        let value ← ops.getindex ops.vector index
        isasciiRangeLoop ops last fuel (index + ix 1) (ops.or aggregate value)

def isasciiRange (ops : CodeUnitOps CU V) (first last : JInt64) : SJl Bool := do
  let aggregate ← isasciiRangeLoop ops last
    (last.val - first.val + 1).toNat first ops.zero
  return ops.nonnegative aggregate && ops.below80 aggregate

def IsasciiRangeProperty : Prop := ∀ (CU V : Type) (ops : CodeUnitOps CU V) first last aggregate,
  isasciiRangeLoop ops last (last.val - first.val + 1).toNat first ops.zero = .ok aggregate →
  isasciiRange ops first last = .ok (ops.nonnegative aggregate && ops.below80 aggregate)

theorem isasciiRange_proven : IsasciiRangeProperty := by
  unfold IsasciiRangeProperty
  intros
  simp_all [isasciiRange, bind, Except.bind, pure, Except.pure]

def isasciiChunksLoop (range : JInt64 → JInt64 → SJl Bool)
    (chunkSize last : JInt64) : Nat → JInt64 → SJl Bool
  | 0, _ => range (last - chunkSize + ix 1) last
  | fuel + 1, index =>
      if index ≤ last - chunkSize then do
        let ascii ← range index (index + chunkSize - ix 1)
        if ascii then isasciiChunksLoop range chunkSize last fuel (index + chunkSize)
        else return false
      else range (last - chunkSize + ix 1) last

def isasciiChunks (range : JInt64 → JInt64 → SJl Bool)
    (chunkSize first last : JInt64) : SJl Bool :=
  isasciiChunksLoop range chunkSize last
    ((last.val - first.val + 1).toNat + 1) first

def IsasciiChunksProperty : Prop := ∀ range chunkSize first last,
  isasciiChunks range chunkSize first last =
    isasciiChunksLoop range chunkSize last
      ((last.val - first.val + 1).toNat + 1) first

theorem isasciiChunks_proven : IsasciiChunksProperty := by
  unfold IsasciiChunksProperty
  intros
  rfl

structure AsciiVectorInput where
  firstindex : SJl JInt64
  lastindex : SJl JInt64
  range : JInt64 → JInt64 → SJl Bool
  chunks : JInt64 → JInt64 → JInt64 → SJl Bool

def isasciiVector (input : AsciiVectorInput) : SJl Bool := do
  let first ← input.firstindex
  let last ← input.lastindex
  let length := last - first + ix 1
  let chunkSize := ix 1024
  let threshold := ix 1536
  if length < threshold then input.range first last
  else input.chunks chunkSize first last

def IsasciiVectorProperty : Prop :=
  (∀ input first last,
    input.firstindex = .ok first → input.lastindex = .ok last →
    last - first + ix 1 < ix 1536 →
    isasciiVector input = input.range first last) ∧
  (∀ input first last,
    input.firstindex = .ok first → input.lastindex = .ok last →
    ¬(last - first + ix 1 < ix 1536) →
    isasciiVector input = input.chunks (ix 1024) first last)

theorem isasciiVector_proven : IsasciiVectorProperty := by
  constructor <;> intros <;>
    simp_all [isasciiVector, bind, Except.bind, pure, Except.pure]

/-! Map, filter, slice, repeat, and reverse iteration, lines 657-776. -/

structure MapInput (S C M B : Type) where
  string : S
  sizeof : SJl JInt64
  codeunitSize : SJl JInt64
  characters : SJl (List C)
  apply : C → SJl M
  isAbstractChar : M → Bool
  convertChar : M → SJl UInt32
  allocate : JInt64 → SJl B
  length : B → SJl JInt64
  resize : B → JInt64 → SJl B
  writeChar : B → UInt32 → JInt64 → SJl (B × JInt64)
  sizehint : B → JInt64 → SJl B
  makeString : B → SJl JStr

def mapLoop (input : MapInput S C M B) : List C → B → JInt64 → SJl (B × JInt64)
  | [], buffer, index => .ok (buffer, index)
  | character :: rest, buffer, index => do
      let mapped ← input.apply character
      if !input.isAbstractChar mapped then
        .error (.jl (.argumentError "map requires AbstractChar results"))
      else
        let length ← input.length buffer
        let buffer ← if length < index + ix 3 then input.resize buffer (length * ix 2)
          else .ok buffer
        let converted ← input.convertChar mapped
        let written ← input.writeChar buffer converted index
        mapLoop input rest written.1 (index + written.2)

def divStringInt (left right : JInt64) : SJl JInt64 :=
  (JInt.div left right).mapError SErr.jl

def mapString (input : MapInput S C M B) : SJl JStr := do
  let bytes ← input.sizeof
  let unitSize ← input.codeunitSize
  let capacity ← divStringInt bytes unitSize
  let capacity := if capacity < ix 4 then ix 4 else capacity
  let buffer ← input.allocate capacity
  let characters ← input.characters
  let result ← mapLoop input characters buffer (ix 1)
  let resized ← input.resize result.1 (result.2 - ix 1)
  let hinted ← input.sizehint resized (result.2 - ix 1)
  input.makeString hinted

def MapProperty : Prop :=
  (∀ (S C M B : Type) (input : MapInput S C M B) error,
    input.sizeof = .error error → mapString input = .error error) ∧
  (∀ (S C M B : Type) (input : MapInput S C M B) bytes unitSize capacity buffer characters,
    input.sizeof = .ok bytes → input.codeunitSize = .ok unitSize →
    divStringInt bytes unitSize = .ok capacity →
    input.allocate (if capacity < ix 4 then ix 4 else capacity) = .ok buffer →
    input.characters = .ok characters →
    mapString input = do
      let result ← mapLoop input characters buffer (ix 1)
      let resized ← input.resize result.1 (result.2 - ix 1)
      let hinted ← input.sizehint resized (result.2 - ix 1)
      input.makeString hinted)

theorem map_proven : MapProperty := by
  constructor <;> intros <;>
    simp_all [mapString, bind, Except.bind, pure, Except.pure]

structure FilterInput (S C B : Type) where
  string : S
  sizeof : SJl JInt64
  makeBuffer : JInt64 → SJl B
  characters : SJl (List C)
  predicate : C → SJl Bool
  write : B → C → SJl B
  takestring : B → SJl JStr

def filterLoop (input : FilterInput S C B) : List C → B → SJl B
  | [], buffer => .ok buffer
  | character :: rest, buffer => do
      let keep ← input.predicate character
      let buffer ← if keep then input.write buffer character else .ok buffer
      filterLoop input rest buffer

def filterString (input : FilterInput S C B) : SJl JStr := do
  let size ← input.sizeof
  let buffer ← input.makeBuffer size
  let characters ← input.characters
  let result ← filterLoop input characters buffer
  input.takestring result

def FilterProperty : Prop :=
  (∀ (S C B : Type) (input : FilterInput S C B) error,
    input.sizeof = .error error → filterString input = .error error) ∧
  (∀ (S C B : Type) (input : FilterInput S C B) size buffer characters,
    input.sizeof = .ok size → input.makeBuffer size = .ok buffer →
    input.characters = .ok characters →
    filterString input = do
      let result ← filterLoop input characters buffer
      input.takestring result)

theorem filter_proven : FilterProperty := by
  constructor <;> intros <;>
    simp_all [filterString, bind, Except.bind, pure, Except.pure]

structure FirstNInput (S I R : Type) where
  string : S
  count : I
  nextind : S → JInt64 → I → SJl JInt64
  lastindex : S → SJl JInt64
  slice : S → JInt64 → JInt64 → SJl R

def firstN (input : FirstNInput S I R) : SJl R := do
  let advanced ← input.nextind input.string (ix 0) input.count
  let last ← input.lastindex input.string
  let stop := if advanced < last then advanced else last
  input.slice input.string (ix 1) stop

def FirstNProperty : Prop := ∀ (S I R : Type) (input : FirstNInput S I R) advanced last,
  input.nextind input.string (ix 0) input.count = .ok advanced →
  input.lastindex input.string = .ok last →
  firstN input = input.slice input.string (ix 1) (if advanced < last then advanced else last)

theorem firstN_proven : FirstNProperty := by
  unfold FirstNProperty
  intros
  simp_all [firstN, bind, Except.bind, pure, Except.pure]

structure LastNInput (S I R : Type) where
  string : S
  count : I
  ncodeunits : S → SJl JInt64
  prevind : S → JInt64 → I → SJl JInt64
  slice : S → JInt64 → SJl R

def lastN (input : LastNInput S I R) : SJl R := do
  let count ← input.ncodeunits input.string
  let first ← input.prevind input.string (count + ix 1) input.count
  input.slice input.string (if first < ix 1 then ix 1 else first)

def LastNProperty : Prop := ∀ (S I R : Type) (input : LastNInput S I R) count first,
  input.ncodeunits input.string = .ok count →
  input.prevind input.string (count + ix 1) input.count = .ok first →
  lastN input = input.slice input.string (if first < ix 1 then ix 1 else first)

theorem lastN_proven : LastNProperty := by
  unfold LastNProperty
  intros
  simp_all [lastN, bind, Except.bind, pure, Except.pure]

def reverseind (ncodeunits : SJl JInt64) (index : MachineIntegerInput I)
    (thisind : JInt64 → SJl JInt64) : SJl JInt64 := do
  let count ← ncodeunits
  let converted ← index.toInt
  thisind (count - converted + ix 1)

def ReverseindProperty : Prop := ∀ (I : Type) ncodeunits (index : MachineIntegerInput I)
    thisind count converted,
  ncodeunits = .ok count → index.toInt = .ok converted →
  reverseind ncodeunits index thisind = thisind (count - converted + ix 1)

theorem reverseind_proven : ReverseindProperty := by
  unfold ReverseindProperty
  intros
  simp_all [reverseind, bind, Except.bind, pure, Except.pure]

def repeatString (string : SJl JStr) (count : I)
    (repeatFn : JStr → I → SJl JStr) : SJl JStr := do
  let concrete ← string
  repeatFn concrete count

def RepeatProperty : Prop := ∀ (I : Type) string count repeatFn concrete,
  string = .ok concrete →
  repeatString string (count : I) repeatFn = repeatFn concrete count

theorem repeat_proven : RepeatProperty := by
  unfold RepeatProperty
  intros
  simp_all [repeatString, bind, Except.bind, pure, Except.pure]

def powerString (value : A) (count : I) (repeatFn : A → I → SJl R) : SJl R :=
  repeatFn value count

def PowerProperty : Prop := ∀ (A I R : Type) value count repeatFn,
  powerString value count (repeatFn : A → I → SJl R) = repeatFn value count

theorem power_proven : PowerProperty := by unfold PowerProperty; intros; rfl

structure ReverseIterateInput (S A : Type) where
  string : S
  state : Option JInt64
  lastindex : S → SJl JInt64
  firstindex : S → SJl JInt64
  getindex : S → JInt64 → SJl A
  prevind : S → JInt64 → SJl JInt64

def reverseIterate (input : ReverseIterateInput S A) : SJl (Option (A × JInt64)) := do
  let state ← match input.state with
    | some state => .ok state
    | none => input.lastindex input.string
  let first ← input.firstindex input.string
  if state < first then return none
  let value ← input.getindex input.string state
  let previous ← input.prevind input.string state
  return some (value, previous)

def ReverseIterateProperty : Prop :=
  (∀ (S A : Type) (input : ReverseIterateInput S A) state first,
    input.state = some state → input.firstindex input.string = .ok first →
    state < first → reverseIterate input = .ok none) ∧
  (∀ (S A : Type) (input : ReverseIterateInput S A) state first,
    input.state = some state → input.firstindex input.string = .ok first →
    ¬(state < first) → reverseIterate input = do
      let value ← input.getindex input.string state
      let previous ← input.prevind input.string state
      return some (value, previous))

theorem reverseIterate_proven : ReverseIterateProperty := by
  constructor <;> intros <;>
    simp_all [reverseIterate, bind, Except.bind, pure, Except.pure]

/-! CodeUnits and `_split_rest`, lines 788-840. -/

structure CodeUnits (S T : Type) where
  string : S

def codeUnitsCtor (s : S) : CodeUnits S T := ⟨s⟩
def CodeUnitsCtorProperty : Prop := ∀ (S T : Type) (s : S),
  (codeUnitsCtor (T := T) s).string = s
theorem codeUnitsCtor_proven : CodeUnitsCtorProperty := by
  unfold CodeUnitsCtorProperty
  intros
  rfl

def cuSizeof (s : CodeUnits S T) (ncodeunits : S → SJl JInt64)
    (sizeofType : SJl JInt64) : SJl JInt64 := do
  let count ← ncodeunits s.string
  let unitSize ← sizeofType
  return count * unitSize

def CuSizeofProperty : Prop := ∀ (S T : Type) (s : CodeUnits S T) ncodeunits sizeofType count unitSize,
  ncodeunits s.string = .ok count → sizeofType = .ok unitSize →
  cuSizeof s ncodeunits sizeofType = .ok (count * unitSize)
theorem cuSizeof_proven : CuSizeofProperty := by
  unfold CuSizeofProperty
  intros
  simp_all [cuSizeof, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

def cuSize (s : CodeUnits S T) (ncodeunits : S → SJl JInt64) : SJl (JInt64 × Unit) := do
  let count ← ncodeunits s.string
  return (count, ())
def CuSizeProperty : Prop := ∀ (S T : Type) (s : CodeUnits S T) ncodeunits count,
  ncodeunits s.string = .ok count → cuSize s ncodeunits = .ok (count, ())
theorem cuSize_proven : CuSizeProperty := by
  unfold CuSizeProperty
  intros
  simp_all [cuSize, bind, Except.bind, pure, Except.pure]

def cuElsize (sizeofType : SJl JInt64) : SJl JInt64 := sizeofType
def CuElsizeProperty : Prop := ∀ sizeofType : SJl JInt64, cuElsize sizeofType = sizeofType
theorem cuElsize_proven : CuElsizeProperty := by unfold CuElsizeProperty; intros; rfl

def cuGetindex (s : CodeUnits S T) (index : JInt64)
    (codeunit : S → JInt64 → SJl T) : SJl T := codeunit s.string index
def CuGetindexProperty : Prop := ∀ (S T : Type) (s : CodeUnits S T) index codeunit,
  cuGetindex s index codeunit = codeunit s.string index
theorem cuGetindex_proven : CuGetindexProperty := by unfold CuGetindexProperty; intros; rfl

def cuCheckbounds (s : CodeUnits S T) (index : I)
    (checkbounds : S → I → SJl Bool) : SJl Bool := checkbounds s.string index
def CuCheckboundsProperty : Prop := ∀ (S T I : Type) (s : CodeUnits S T)
    (index : I) (checkbounds : S → I → SJl Bool),
  cuCheckbounds s index checkbounds = checkbounds s.string index
theorem cuCheckbounds_proven : CuCheckboundsProperty := by unfold CuCheckboundsProperty; intros; rfl

def cuDataids (s : CodeUnits S T) (dataids : S → SJl R) : SJl R := dataids s.string
def CuDataidsProperty : Prop := ∀ (S T R : Type) (s : CodeUnits S T) dataids,
  cuDataids s (dataids : S → SJl R) = dataids s.string
theorem cuDataids_proven : CuDataidsProperty := by unfold CuDataidsProperty; intros; rfl

def cuWrite (io : IOType) (s : CodeUnits S T)
    (write : IOType → S → SJl R) : SJl R := write io s.string
def CuWriteProperty : Prop := ∀ (IOType S T R : Type) io (s : CodeUnits S T) write,
  cuWrite io s (write : IOType → S → SJl R) = write io s.string
theorem cuWrite_proven : CuWriteProperty := by unfold CuWriteProperty; intros; rfl

inductive PointerTarget (T : Type) where
  | typed
  | int8

def cuCconvert (target : PointerTarget T) (s : CodeUnits S T)
    (cconvert : PointerTarget T → S → SJl P) : SJl P := cconvert target s.string
def CuCconvertProperty : Prop := ∀ (S T P : Type) target (s : CodeUnits S T) cconvert,
  cuCconvert target s (cconvert : PointerTarget T → S → SJl P) = cconvert target s.string
theorem cuCconvert_proven : CuCconvertProperty := by unfold CuCconvertProperty; intros; rfl

def cuSimilar (dims : Dims) (similarArray : Dims → SJl A) : SJl A := similarArray dims
def CuSimilarProperty : Prop := ∀ (Dims A : Type) dims similarArray,
  cuSimilar dims (similarArray : Dims → SJl A) = similarArray dims
theorem cuSimilar_proven : CuSimilarProperty := by unfold CuSimilarProperty; intros; rfl

def codeunits (s : S) : CodeUnits S T := codeUnitsCtor s
def CodeunitsProperty : Prop := ∀ (S T : Type) (s : S),
  (codeunits (T := T) s).string = s
theorem codeunits_proven : CodeunitsProperty := by unfold CodeunitsProperty; intros; rfl

structure SplitRestInput (S R : Type) where
  string : S
  count : JInt64
  lastindex : S → SJl JInt64
  prevind : S → JInt64 → JInt64 → SJl JInt64
  length : S → SJl JInt64
  checkLength : JInt64 → JInt64 → SJl JInt64
  nextind : S → JInt64 → SJl JInt64
  substring : S → JInt64 → JInt64 → SJl R
  front : S → JInt64 → SJl R

def splitRest (input : SplitRestInput S R) : SJl (R × R) := do
  let last ← input.lastindex input.string
  let split ← match input.prevind input.string last input.count with
    | .ok index => .ok index
    | .error (.jl .boundsError) => do
        let length ← input.length input.string
        input.checkLength length input.count
    | .error error => .error error
  let suffixStart ← input.nextind input.string split
  let suffix ← input.substring input.string suffixStart last
  let frontResult ← input.front input.string split
  return (frontResult, suffix)

def SplitRestProperty : Prop :=
  (∀ (S R : Type) (input : SplitRestInput S R) last split,
    input.lastindex input.string = .ok last →
    input.prevind input.string last input.count = .ok split →
    splitRest input = do
      let suffixStart ← input.nextind input.string split
      let suffix ← input.substring input.string suffixStart last
      let frontResult ← input.front input.string split
      return (frontResult, suffix)) ∧
  (∀ (S R : Type) (input : SplitRestInput S R) last length,
    input.lastindex input.string = .ok last →
    input.prevind input.string last input.count = .error (.jl .boundsError) →
    input.length input.string = .ok length →
    splitRest input = do
      let split ← input.checkLength length input.count
      let suffixStart ← input.nextind input.string split
      let suffix ← input.substring input.string suffixStart last
      let frontResult ← input.front input.string split
      return (frontResult, suffix))

theorem splitRest_proven : SplitRestProperty := by
  constructor <;> intros <;>
    simp_all [splitRest, bind, Except.bind, pure, Except.pure]

end JuliaLean.StringsCovA.BasicRebuilt
